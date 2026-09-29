-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/14578f86-8182-5afb-9fe8-16fc99b936c6
-- title:
--   Zariski-local realisation of Drinfeld data by admissible rigidified triples
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon W(\mathbb F_{p^2})\to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ over $W(k)/pW(k)$ (a two-dimensional commutative formal group law together with an action of $W(\mathbb F_{p^2})$ and an endomorphism $\varpi$ with $\varpi^2=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$), with $\bar\jmath$ the reduction of $\iota$ modulo $p$. Assume: $\Phi$ is special for $\bar\jmath$, i.e. the weight-$0$ and weight-$1$ parts of $\operatorname{Lie}\Phi$ are complementary and both invertible; $[p]$ on $\Phi$ has kernel of degree $p^4$; $\varpi$ annihilates the weight-$0$ part of $\operatorname{Lie}\Phi$; the degree-$0$ and degree-$1$ graded pieces `hcΦ` of the Cartier module of $\Phi$ are complementary; and there is an additive map $r_\Phi\colon \mathbb Z_p^2\to \mathcal N(\Phi)$ on the $N$-module of the associated graded Cartier module data which, for every canonical $L$-map $L$, maps all of $\mathbb Z_p^2$ bijectively onto the degree-$0$ $\eta$-piece of $L$. The conclusion asserts: for every Noetherian $\mathbb Z_p$-algebra $B$ in which $p$ is nilpotent, every $\psi\colon W(k)\to B$, every Drinfeld datum $Q$ over $B$ and every Deligne datum $d$ over $B$ for $\mathbb Q_p$ with uniformiser $p$, such that $Q$ is the quadruple of $d$ (at each prime $x$ of $B$ the pair $(L_0x,L_1x)$ is edge-nondegenerate for $d$ and the kernels of $u_0x$, $u_1x$ are the corresponding lines of $d$ over the local ring), there exist $n$ and $f\colon \mathrm{Fin}\,n\to B$ with $(f_i)=B$ such that for each $i$ and each Noetherian localisation $L$ of $B$ away from $f_i$ (as a $B$- and $\mathbb Z_p$-algebra, with $p$ nilpotent in $L$) there are a rigidified triple $t=(X,n_t,\rho)$ over $L$, a Deligne datum $d_L$ and a Drinfeld datum $Q_L$ over $L$ with: $t$ admissible for $\iota$ and $\psi$ followed by $B\to L$, meaning $X$ special of height $4$ and $\rho$ an isogeny of height $4n_t$ from the base change of $\Phi$ to the reduction of $X$; $t$ has Cartier quadruple $Q_L$ relative to $\iota$, `hcΦ` and $r_\Phi$; $Q_L$ the quadruple of $d_L$; and $d_L$ the base change of $d$ along $B\to L$, i.e. each line of $d_L$ is spanned by the image of the corresponding line of $d$.
--
--   This is the surjectivity-up-to-Zariski-refinement half of Drinfeld's classification of points of the formal upper half plane: every point of the moduli of Deligne–Drinfeld data over a Noetherian base with $p$ nilpotent comes, locally on the base, from a special formal $\mathcal O_D$-module with rigidification, under the standing assumption that the index $0$ is critical for $\Phi$. It feeds the comparison statement [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_drinfeldDatum_isIsomorphic_iff_and_exists_cover_and_isBaseChange_of_isAdmissible`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_drinfeldDatum_isIsomorphic_iff_and_exists_cover_and_isBaseChange_of_isAdmissible), which packages the equivalence of the two moduli problems used in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_cover_isAdmissible_isCartierQuadruple_isQuadrupleOf_of_isQuadrupleOf_of_lieVarpi_eq_zero
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
    :
    (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B), Q.IsQuadrupleOf d →
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] B L]
        [IsLocalization.Away (f i) L] (hL : IsNilpotent (p : L)),
        ∃ (t : Rigidified p Φ L) (dL : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) L)
          (QL : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) L),
          t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
          t.IsCartierQuadruple ι hcΦ rΦ ((algebraMap B L).comp ψ) QL ∧ QL.IsQuadrupleOf dL ∧
          DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) (IsScalarTower.toAlgHom ℤ_[p] B L) d dL) := by sorry
