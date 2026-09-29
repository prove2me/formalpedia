-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_mem_etaPiece_nsmul_rigidNum_eq_etaRed_nVarpi_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_mem_etaPiece_nsmul_rigidNum_eq_etaRed_nVarpi_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/ea807e31-67d5-50e7-8ae9-f995fbbbe95b
-- title:
--   Rigid numbering lies in reduced η up to a p-power
-- statement:
--   Let $p$ be a prime, $k$ an algebraically closed field of characteristic $p$, and $\iota : W(\mathbb F_{p^2}) \to W(k)$ a ring homomorphism. Let $\Phi$ be a formal $\mathcal O_D$-module over $W(k)/pW(k)$ which is special for the reduction $\bar\jmath$ of $\iota$ (its Lie algebra is the direct sum of the eigen-submodules `lieZero` and `lieOne`, both invertible), which has height $4$ (the kernel of multiplication by $p$ has degree $p^4$), and whose submodule `lieZero` is contained in the kernel of `lieVarpi`. Assume the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ are complementary, let $r_\Phi : \mathbb Z_p^2 \to N(\Phi)$ be an additive map into the $N$-module of the associated graded Cartier module data, and assume that for every canonical $L$-map $L$ on that data, $r_\Phi$ maps $\mathbb Z_p^2$ bijectively onto the degree-$0$ part $\eta_0(L)$ of $\eta(L)$. Let $K$ be an algebraically closed field of characteristic $p$ which is a $\mathbb Z_p$-algebra, $\psi' : W(k) \to K$ a ring homomorphism, and suppose $p$ is nilpotent in $K$. Let $t' = (X, n, \rho)$ be a rigidified object over $K$ which is admissible for $\iota, \psi'$ ($X$ special of height $4$ and $\rho$ an isogeny of height $4n$ from $\bar\Phi_{\psi'}$ to $\bar X$), and assume, over the localisation of $K$ at the powers of $1$, that the degree-$0$ and degree-$1$ graded pieces are complementary for the Cartier module of $X$, for that of $\bar X$, and for that of the reduced base change of $\Phi$. Let $L'$ be a canonical $L$-map on the graded Cartier module data of $X$ over that localisation. Then for every $i \in \{0,1\}$ and every $w \in \mathbb Z_p^2$ there are $N \in \mathbb N$ and an element $z$ of the degree-$i$ part $\eta_i(L')$ of $\eta(L')$ with $$p^N \cdot \mathrm{rigidNum}(w) = \mathrm{etaRed}\bigl(\mathrm{nVarpi}^i(z)\bigr),$$ where $\mathrm{rigidNum}$ is $r_\Phi$ followed by the $N$-maps induced by the base change $\Phi \to \bar\Phi_K$ and by $\bar\rho_*$, and $\mathrm{etaRed}$ is the $N$-map induced by reduction modulo $p$ from the Cartier module of $X$ to that of $\bar X$.
--
--   This is the surjectivity half of the comparison between the $\mathbb Z_p^2$-numbering of a special formal $\mathcal O_D$-module and the $\eta$-filtration of the Cartier module of a rigidified object, in the Čerednik–Drinfeld uniformisation of the formal upper half plane. It supplies one clause of [`CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed) and is used in the Cartier-quadruple bijectivity statement [`CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_map_nsmul_eq_of_isEtaSection_iff_of_bijective_XS_awayHom_of_lieZero_le_ker`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.IsCartierQuadruple.exists_bijective_cartierModule_map_nsmul_eq_of_isEtaSection_iff_of_bijective_XS_awayHom_of_lieZero_le_ker).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_mem_etaPiece_nsmul_rigidNum_eq_etaRed_nVarpi_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_mem_etaPiece_nsmul_rigidNum_eq_etaRed_nVarpi_of_isAlgClosed
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
    ∀ (i : Fin 2) (w : Fin 2 → ℤ_[p]), ∃ (N : ℕ) (z : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod), z ∈ ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).etaPiece L' hL'.isCartierLMap.map_verschiebung i ∧
      p ^ N • t'.rigidNum ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hcb hcΦ1 w = t'.etaRed ι ψ' (Rigidified.awayHom (1 : K)) hc hcb (((((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).nVarpi : ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod →ₗ[WittVector p (Rigidified.Baway (1 : K))] ((t'.XS (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jS ι ψ' (Rigidified.awayHom (1 : K))) hc).NMod) ^ (i : ℕ)) z) := by sorry
