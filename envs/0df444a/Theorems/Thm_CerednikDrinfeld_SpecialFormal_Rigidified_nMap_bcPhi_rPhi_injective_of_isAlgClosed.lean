-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_rPhi_injective_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.nMap_bcPhi_rPhi_injective_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/434f1de7-02ff-51f9-91b0-aa8accbfa7af
-- title:
--   Base change after rigidification is injective on ℤₚ²
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, and a ring homomorphism $\iota : \mathbb{W}(p,\mathbb{F}_{p^2}) \to W(k)$ from the Witt vectors of the quadratic extension of $\mathbb{F}_p$. Let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/pW(k)$ (a two-variable commutative formal group law with an action of $\mathbb{W}(p,\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ with $\varpi^2 = [p]$), and write $\bar\iota$ for $\iota$ followed by reduction mod $p$. Assume: $\Phi$ is special for $\bar\iota$, i.e. the weight-$0$ and weight-$1$ parts of its Lie module are complementary and invertible; $\Phi$ has height $4$, i.e. the kernel of $[p]$ is finite projective of degree $p^4$ at every point; the weight-$0$ Lie part is killed by the linear part of $\varpi$; and the two graded pieces of degree $0$ and $1$ of the Cartier module of $\Phi$ (where the Teichmüller action is homothety by $\bar\iota$ composed with the $p^n$-power) are complementary, giving graded Cartier module data $D_\Phi$. Let $r_\Phi : \mathbb{Z}_p^2 \to D_\Phi.\mathrm{NMod}$ be additive and assume that for every canonical $L$-map $L$ on $D_\Phi$ the map $r_\Phi$ is a bijection from all of $\mathbb{Z}_p^2$ onto the degree-$0$ part $\eta(L) \cap N_0$. Let further $K$ be an algebraically closed field of characteristic $p$ and a $\mathbb{Z}_p$-algebra, $\psi' : W(k) \to K$ a ring homomorphism, with $p$ nilpotent in $K$; let $t'$ be a rigidified object over $K$ (a formal $O_D$-module $X$, an integer $n$, and a law $\rho$ over $K/p$) which is admissible for $(\iota,\psi')$, i.e. $X$ is special of height $4$ and $\rho$ is an isogeny of height $4n$ from the base change of $\Phi$ to $\bar X$. Assume the gradedness hypotheses at the localisation $g =$ `awayHom (1 : K)`: the degree-$0$ and degree-$1$ graded pieces are complementary for $t'.XS\,g$, for $t'.XbarS\,g$ and for the base change $\bar\Phi_S$ of $\Phi$ along $\psi'$ and $g$; and let $L'$ be a canonical $L$-map on the graded Cartier module data of $t'.XS\,g$. Then the composite of $r_\Phi$ with the map $D_\Phi.\mathrm{NMod} \to D_{\bar\Phi_S}.\mathrm{NMod}$ induced by the base-change homomorphism `bcPhi` of Cartier modules (which commutes with Verschiebung and with $\varpi$) is injective as a function on $\mathbb{Z}_p^2$.
--
--   This is the injectivity half of the comparison, in the Čerednik–Drinfel'd uniformisation of the Cartier–Dieudonné theory of special formal $O_D$-modules, between the $\mathbb{Z}_p^2$-parametrisation of the degree-zero part of the period module of $\Phi$ and its base change to an algebraically closed extension $K$. It is used in establishing that period points over $K$ are, up to a power of $p$, images of $\mathbb{Z}_p^2$ under base change, and cites only the existence of a canonical $L$-map for the special module $\Phi$ over $W(k)/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_nMap_bcPhi_rPhi_injective_of_isAlgClosed.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.nMap_bcPhi_rPhi_injective_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ' : WittVector p k →+* K) (hK : IsNilpotent (p : K))
    (t' : Rigidified p Φ K) (ht' : t'.IsAdmissible ι ψ')
    (hc : t'.IsGradedS ι ψ' (Rigidified.awayHom (1 : K))) (hcb : t'.IsGradedSbar ι ψ' (Rigidified.awayHom (1 : K)))
    (hcΦ1 : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' (Rigidified.awayHom (1 : K)))
    (L' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).M →+
      ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod)
    (hL' : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).IsCanonicalLMap L') :
    Function.Injective (fun w : Fin 2 → ℤ_[p] => (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (rΦ w)) := by sorry
