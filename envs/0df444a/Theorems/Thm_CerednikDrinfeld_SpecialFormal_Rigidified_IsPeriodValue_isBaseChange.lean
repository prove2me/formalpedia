-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_isBaseChange
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a7993995-910d-5346-a9c8-b6482b3861f0
-- title:
--   Period values are compatible with base change
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring map $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ over $W(k)/pW(k)$ (a two-dimensional commutative formal group law carrying an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$), together with the reduction $\bar\iota$ of $\iota$ modulo $p$. Assume: $\Phi$ is special for $\bar\iota$ (its zero and one Lie eigen-submodules are complementary and invertible), $\Phi$ has height $4$ (the kernel of $[p]$ has degree $p^4$), $\varpi$ annihilates the zero eigen-submodule of $\mathrm{Lie}\,\Phi$, the graded pieces of degree $0$ and $1$ of the Cartier module of $\Phi$ are complementary (`hcΦ`), and an additive map $r_\Phi\colon (\mathrm{Fin}\ 2\to\mathbb Z_p)\to N$ into the $N$-module of the graded Cartier module data of $\Phi$ is given which, for every canonical $L$-map $L$, maps bijectively onto the degree-$0$ $\eta$-piece of $L$. Let $B$, $B'$ be Noetherian $\mathbb Z_p$-algebras in which $p$ is nilpotent, with ring maps $\psi\colon W(k)\to B$, $\psi'\colon W(k)\to B'$, and let $f\colon B\to B'$ be a $\mathbb Z_p$-algebra map with $f\circ\psi=\psi'$. Let $t$ be a rigidified object over $B$ (a formal $\mathcal O_D$-module $X$ over $B$, an integer $n$, and a series $\rho$ over $B/pB$) which is admissible for $\iota,\psi$: $X$ is special, of height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$. Suppose $d$ is a Deligne datum over $B$ for $K=\mathbb Q_p$, $\pi=p$, which is a period value of $t$ (there is a Drinfeld datum $Q$ over $B$ forming a Cartier quadruple with $t$ and having $d$ as its associated Deligne datum), and $d'$ is a Deligne datum over $B'$ which is a period value of the base change $t$ along $f$ relative to $\psi'$. Then $d'$ is the base change of $d$ along $f$: for every full $\mathbb Z_p$-lattice $M\subset\mathbb Q_p^2$, the line of $d'$ at $M$ is the $B'$-span of the image of the line of $d$ at $M$ under $f\otimes\mathrm{id}_M$.
--
--   This is the naturality in the base of the Čerednik–Drinfeld period construction: a period value of a rigidified special formal module is determined by base change from the period value over the source ring. It is used in the construction of the period map on the moduli package, where the values over varying test algebras must be shown to assemble into a natural transformation of Deligne data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_IsPeriodValue_isBaseChange.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.IsPeriodValue.isBaseChange
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4)
    (h0 : ∀ m ∈ Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι), Φ.lieVarpi m = 0)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
  (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
  Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    {B' : Type} [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[p] B'] (ψ' : WittVector p k →+* B') (hB' : IsNilpotent (p : B'))
    (f : B →ₐ[ℤ_[p]] B') (hf : (f : B →+* B').comp ψ = ψ')
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    (d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B) (hd : t.IsPeriodValue ι hcΦ rΦ ψ d)
    (d' : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B') (hd' : (t.map (f : B →+* B')).IsPeriodValue ι hcΦ rΦ ψ' d') :
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f d d' := by sorry
