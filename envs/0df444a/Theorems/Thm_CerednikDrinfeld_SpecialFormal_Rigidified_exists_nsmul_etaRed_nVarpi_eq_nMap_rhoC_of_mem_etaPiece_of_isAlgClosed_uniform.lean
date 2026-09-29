-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/cd70964f-677f-5d25-9bad-58ac9b2413d1
-- title:
--   Uniform exponent for η-pieces under reduction and isogeny
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/p$ (a commutative two-variable formal group with a $W(\mathbb{F}_{p^2})$-action and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$). Assume: $\Phi$ is special for the reduction $\bar\iota$ of $\iota$, i.e. its Lie module is the direct sum of the $\bar\iota$-eigenspace and the Frobenius-twisted one, both invertible; multiplication by $p$ on $\Phi$ has kernel of degree $p^4$; the weight-zero Lie summand lies in the kernel of the linear part of $\varpi$; the degree-$0$ and degree-$1$ Teichmüller graded pieces of the Cartier module of $\Phi$ are complementary, giving graded Cartier data $D_\Phi$; and there is an additive map $r_\Phi : \mathbb{Z}_p^2 \to N(D_\Phi)$ which, for every canonical $L$-map $L$ on $D_\Phi$, maps $\mathbb{Z}_p^2$ bijectively onto $\eta(L)\cap N(D_\Phi)_0$. Fix further an algebraically closed field $K$ of characteristic $p$ that is a $\mathbb{Z}_p$-algebra with $p$ nilpotent, a ring homomorphism $\psi' : W(k) \to K$, and a rigidified object $t' = (X, n, \rho)$ over $K$ admissible for $(\iota,\psi')$: $X$ is special for $\psi'\circ\iota$, of height $4$, and $\rho$ is an isogeny of height $4n$ from the base change $\bar\Phi$ of $\Phi$ to $K/pK$ onto the reduction $\bar X$. All Cartier data are read over the localisation of $K$ at the powers of $1$; assume the degree-$0$ and degree-$1$ graded pieces are complementary for $X$, for $\bar X$ and for $\bar\Phi$ there, yielding data $D_X$, $D_{\bar X}$, $D_{\bar\Phi}$, and let $L'$ be a canonical $L$-map on $D_X$. The assertion is: for every canonical $L$-map $L_\Phi$ on $D_{\bar\Phi}$ there is a single $N \in \mathbb{N}$ such that for every $i \in \{0,1\}$ and every $z$ in $\eta(L')\cap N(D_X)_i$ there exists $x$ in $\eta(L_\Phi)\cap N(D_{\bar\Phi})_0$ with $p^N \cdot \mathrm{etaRed}(\varpi^i z) = N(\bar\rho_*)(x)$, where $\mathrm{etaRed}$ is the map $N(D_X) \to N(D_{\bar X})$ induced by reduction modulo $p$, $\varpi$ is the $\varpi$-operator `nVarpi` on $N(D_X)$, and $N(\bar\rho_*) : N(D_{\bar\Phi}) \to N(D_{\bar X})$ is induced by the Cartier-module map `Rigidified.rhoC` attached to $\rho$.
--
--   This is the uniform (exponent-independent-of-$z$) form of the cofinality statement saying that, up to a fixed power of $p$, the reduction of the graded $\eta$-pieces of the Cartier module of $X$ is captured by the isogeny $\bar\rho$ from the base point $\bar\Phi$; it is the input for constructing the rigidifying coordinates in the Čerednik–Drinfeld uniformisation. It is cited by [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_etaRed_nVarpi_eq_nMap_rhoC_of_mem_etaPiece_of_isAlgClosed_uniform
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
    ∀ (LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod) (hLΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).IsCanonicalLMap LΦ), ∃ N : ℕ,
      ∀ (i : Fin 2) (z : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod), z ∈ ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).etaPiece L' hL'.isCartierLMap.map_verschiebung i →
      ∃ x : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod, x ∈ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0 ∧
        p ^ N • t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z) = ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).nMap ((t'.XbarS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jSbar ι ψ' (Rigidified.awayHom (1 : K))) hcb) (Rigidified.rhoC ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_verschiebungInt ψ' t' ht'.2.2.1.1 (Rigidified.awayHom (1 : K))) (Rigidified.rhoC_endAct_varpiEnd ψ' t' ht'.2.2.1 (Rigidified.awayHom (1 : K))) x := by sorry
