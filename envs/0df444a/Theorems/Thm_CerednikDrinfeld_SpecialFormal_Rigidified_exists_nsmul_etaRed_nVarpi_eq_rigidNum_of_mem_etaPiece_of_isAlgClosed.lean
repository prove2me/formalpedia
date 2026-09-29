-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_rigidNum_of_mem_etaPiece_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_etaRed_nVarpi_eq_rigidNum_of_mem_etaPiece_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/dde60c6d-cc5d-5404-886c-3002750d7537
-- title:
--   p-power commensurability of η-pieces with `rigidNum`
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota$ a ring homomorphism from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ to $W(k)$; write $\bar\iota$ for $\iota$ followed by reduction modulo the ideal $(p)$ of $W(k)$. Let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/(p)$ which is special for $\bar\iota$ (its Lie algebra splits as the sum of the $\bar\iota$-eigenspace `lieZero` and the Frobenius-twisted eigenspace `lieOne`, both invertible modules), which has height $4$ (the kernel of multiplication by $p$ has degree $p^4$), and whose `lieZero` is annihilated by the linear part `lieVarpi` of $\varpi$. Assume the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ — the subgroups on which the Teichmüller lifts of $\mathbb{F}_{p^2}$ act through $\bar\iota$ by the scalars $\bar\iota(\tau(c))$, resp. $\bar\iota(\tau(c))^{p}$ — are complementary, giving graded Cartier module data for $\Phi$, and let $r_\Phi : \mathbb{Z}_p^2 \to N(\Phi)$ be an additive map which, for every canonical $L$-map $L$ on these data, is a bijection from $\mathbb{Z}_p^2$ onto the degree-$0$ $\eta$-piece $\eta(L) \cap N_0$. Let $K$ be a further algebraically closed field of characteristic $p$ which is a $\mathbb{Z}_p$-algebra and in which $p$ is nilpotent, let $\psi' : W(k) \to K$ be a ring homomorphism, and let $t'$ be a rigidified object over $K$ (a formal $O_D$-module $X$, an integer $n$, and a power series system $\rho$) which is admissible for $(\iota,\psi')$: $X$ is special and of height $4$, and $\rho$ is an isogeny of height $4n$ from the base change $\bar\Phi_{\psi'}$ to $\bar X$. Assume the graded pieces split for $X$, for $\bar X$ and for $\bar\Phi$ over the localisation of $K$ away from $1$, and let $L'$ be a canonical $L$-map on the graded Cartier module data of $X$ there. Then for every $i \in \{0,1\}$ and every $z$ in the $\eta$-piece of degree $i$ attached to $L'$ there are $N \in \mathbb{N}$ and $w \in \mathbb{Z}_p^2$ with $p^N \cdot \mathrm{etaRed}(\Pi^i z) = \mathrm{rigidNum}(w)$, where $\Pi$ is the operator `nVarpi` induced by $\varpi$ on the $N$-module, $\mathrm{etaRed}$ is the map induced on $N$-modules by reduction modulo $p$, and $\mathrm{rigidNum}$ is $r_\Phi$ followed by the $N$-module maps induced by the base change $\Phi \to \bar\Phi_{\psi'}$ and by $\rho$.
--
--   This is the commensurability step in the Čerednik–Drinfeld description of the fibres of the rigidifying moduli problem: every element of an $\eta$-piece of the $N$-module of $X$ becomes, after multiplication by a power of $p$ and reduction, a value of the rigidification map coming from the fixed special formal module $\Phi$. It feeds the coordinate description of $\eta$-sections in [`CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_etaRed_nVarpi_eq_rigidNum_of_mem_etaPiece_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_etaRed_nVarpi_eq_rigidNum_of_mem_etaPiece_of_isAlgClosed
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
    ∀ (i : Fin 2) (z : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod), z ∈ ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).etaPiece L' hL'.isCartierLMap.map_verschiebung i →
      ∃ (N : ℕ) (w : Fin 2 → ℤ_[p]), p ^ N • t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z) = t'.rigidNum ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hcb hcΦ1 w := by sorry
