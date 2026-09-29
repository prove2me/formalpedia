-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/277787bb-6cd4-5613-9edc-57d1e8d9988b
-- title:
--   Pointwise p-power divisibility of η₀ into the base-changed rigidification
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $O_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$ (a commutative two-dimensional formal group law with an action of $W(\mathbb{F}_{p^2})$ and an endomorphism $\varpi$ with $\varpi^2 = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$). Assume: $\Phi$ is special for the reduction $\bar\iota$ of $\iota$, i.e. its Lie algebra is the direct sum of the invertible submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$; $\Phi$ has height $4$, i.e. the kernel of $[p]$ has degree $p^4$; $\mathrm{lieZero}$ lies in the kernel of the linear part of $\varpi$; the Cartier module of $\Phi$ is the direct sum of its graded pieces of weights $0$ and $1$ for $\bar\iota$, so that the associated graded Cartier module data are defined; and an additive map $r_\Phi : \mathbb{Z}_p^2 \to N(M_\Phi)$ is given which, for every canonical $L$-map $L$ on $M_\Phi$, maps $\mathbb{Z}_p^2$ bijectively onto $\mathrm{etaPiece}\,L\,0$, the intersection of the subgroup $\mathrm{eta}$ attached to $L$ with the degree-$0$ part of $N(M_\Phi)$. Fix further an algebraically closed field $K$ of characteristic $p$ which is a $\mathbb{Z}_p$-algebra, a ring homomorphism $\psi' : W(k) \to K$, nilpotence of $p$ in $K$, and a rigidified object $t' = (X,n,\rho)$ over $K$ which is admissible for $(\iota,\psi')$: $X$ is special for $\psi'\circ\iota$, of height $4$, and $\rho$ is an isogeny of height $4n$ from $\Phi$ base-changed along $\psi'$ to the reduction $\bar X$. All objects are read over the localisation of $K$ at the powers of $1$, where the graded pieces of weights $0$ and $1$ are assumed complementary for $X_S$, for $\bar X_S$ and for $\bar\Phi_S$, and a canonical $L$-map $L'$ on the data of $X_S$ is given. The conclusion: for every canonical $L$-map $L_\Phi$ on the graded Cartier module data of $\bar\Phi_S$ and every $x$ in $\mathrm{etaPiece}\,L_\Phi\,0$ inside $N(M_{\bar\Phi_S})$, there exist $N \in \mathbb{N}$ and $w \in \mathbb{Z}_p^2$ with $p^N \cdot x$ equal to the image of $r_\Phi(w)$ under the map of $N$-modules induced by the base-change homomorphism `bcPhi` of Cartier modules (composition of base change along the residue map of $\psi'$ with base change along the reduction of the localisation map).
--
--   This is a cofinality statement in the Cartier-module side of the Čerednik–Drinfel'd uniformisation: on the degree-$0$ part of $\eta$, the $N$-module of $\Phi$ base-changed to $K$ is, up to $p$-power multiples, exhausted by the image of the rigidification $r_\Phi$ of the base point. It is used in the identification of the rigidification numerator, `exists_nsmul_etaRed_nVarpi_eq_rigidNum_of_mem_etaPiece_of_isAlgClosed`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_eq_nMap_bcPhi_apply_of_mem_etaPiece_of_isAlgClosed
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
    ∀ (LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod) (hLΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).IsCanonicalLMap LΦ)
      (x : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod), x ∈ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0 →
      ∃ (N : ℕ) (w : Fin 2 → ℤ_[p]), p ^ N • x = (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (rΦ w) := by sorry
