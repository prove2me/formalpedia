-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isPeriodValue_of_isAdmissible
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_isPeriodValue_of_isAdmissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/5c6677be-4227-5cbd-be96-a81068be15fe
-- title:
--   Existence of period values for admissible rigidified data
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, and let $\iota : \mathrm{Zp2}\,p \to W(k)$ be a ring homomorphism, where $\mathrm{Zp2}\,p = W(\mathbb{F}_{p^2})$; write $\bar\jmath$ for $\iota$ followed by the quotient map $W(k) \to W(k)/pW(k)$. Let $\Phi$ be a formal $\mathcal{O}_D$-module of dimension $2$ over $W(k)/pW(k)$ (a commutative formal group law in two variables together with an action of $\mathrm{Zp2}\,p$ and an endomorphism $\varpi$ with $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$) such that: $\Phi$ is special for $\bar\jmath$, i.e. the two eigenspaces $\mathrm{lieZero}$ and $\mathrm{lieOne}$ of the $\mathrm{Zp2}\,p$-action on $\mathrm{Lie}\,\Phi$ are complementary and invertible; the kernel of $[p]$ on $\Phi$ has degree $p^4$; the linear part $\mathrm{lieVarpi}$ of $\varpi$ kills $\mathrm{lieZero}$; and the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary, as witnessed by $h_{c\Phi}$, so that $\Phi$ determines graded Cartier module data $D_\Phi$. Let $r_\Phi : (\mathrm{Fin}\,2 \to \mathbb{Z}_p) \to D_\Phi.\mathrm{NMod}$ be an additive map which, for every canonical $L$-map $L$ on $D_\Phi$, maps the whole source bijectively onto the degree-$0$ $\eta$-piece $\mathrm{etaPiece}\,L\,0$. Let $B$ be a Noetherian commutative $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : W(k) \to B$ a ring homomorphism, and $t = (X, n, \rho)$ a rigidified object over $B$ which is admissible for $(\iota, \psi)$: $X$ is special for $\psi \circ \iota$, the kernel of $[p]$ on $X$ has degree $p^4$, and $\rho$ is an isogeny of height $4n$ from $\Phi$ base-changed along $\psi$ to $X$ reduced modulo $pB$. Then there exists a Deligne datum $d$ over $B$ for $(\mathbb{Z}_p \subset \mathbb{Q}_p, \pi = p)$ which is a period value of $t$: there is a Drinfeld datum $Q$ over $B$ forming a Cartier quadruple with $t$ (relative to $\iota$, $h_{c\Phi}$, $r_\Phi$, $\psi$) and such that $Q$ is the Drinfeld quadruple attached to $d$.
--
--   This is the existence half of the local period morphism in the Čerednik–Drinfeld uniformisation: an admissible rigidified formal $\mathcal{O}_D$-module over $B$ is matched with a point of Drinfeld's formal upper half-plane functor $\hat\Omega$. It feeds the construction of the period map on the moduli package, where it is cited to produce a period morphism under the vanishing condition on $\mathrm{lieVarpi}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_isPeriodValue_of_isAdmissible.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_isPeriodValue_of_isAdmissible
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
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∃ d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsPeriodValue ι hcΦ rΦ ψ d := by sorry
