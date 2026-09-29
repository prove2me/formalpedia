-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nMap_bcPhi_rPhi_eq_of_mem_etaPiece_zero_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_nMap_bcPhi_rPhi_eq_of_mem_etaPiece_zero_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/8da32de9-969d-5297-ab14-f399a5dc786c
-- title:
--   Base change is onto the degree-zero η-piece
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, and a ring homomorphism $\iota : W(\mathbf F_{p^2}) \to W(k)$; write $\bar\jmath$ for $\iota$ followed by reduction modulo $pW(k)$. Let $\Phi$ be a formal $O_D$-module of dimension $2$ over $W(k)/p$ (a commutative two-variable formal group with an action of $W(\mathbf F_{p^2})$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ a = a^{\sigma}\circ\varpi$) subject to: $\Phi$ is special for $\bar\jmath$, i.e. the submodules of the Lie algebra on which the Teichmüller action is by $\bar\jmath$ resp. $\bar\jmath\circ\sigma$ are complementary and invertible; $\Phi$ has height $4$, i.e. the kernel algebra of $[p]$ has degree $p^4$; the $\bar\jmath$-eigenspace of the Lie algebra is annihilated by the linear part of $\varpi$; and the weight-$0$ and weight-$1$ Teichmüller eigenpieces of the Cartier module $C_p(\Phi)$ (those $f$ with $\varpi$-free Teichmüller action by $\bar\jmath(\tau(c))^{p^n}$ for all $c \in \mathbf F_{p^2}$) are complementary, giving the graded Cartier datum $D_\Phi$. Let $r_\Phi : \mathbb Z_p^2 \to N(D_\Phi)$ be additive and such that, for every canonical $L$-map $L$ on $D_\Phi$, $r_\Phi$ is a bijection of $\mathbb Z_p^2$ onto the degree-$0$ $\eta$-piece `etaPiece L _ 0`, the intersection of `eta L` with the image of $(\mathrm{piece}\,0)\times(\mathrm{piece}\,0)$ in $N(D_\Phi)$. Let further $K$ be an algebraically closed field of characteristic $p$ which is a $\mathbb Z_p$-algebra, with $p$ nilpotent in $K$, let $\psi' : W(k) \to K$ be a ring homomorphism, and let $t' = (X, n, \rho)$ be a rigidified object over $K$ which is admissible for $(\iota,\psi')$: $X$ is special for $\psi'\circ\iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from $\Phi$ pushed to $K/pK$ to the reduction $\bar X$. Put $S = K[1^{-1}]$, the localisation of $K$ at the powers of $1$, with $g : K \to S$ the canonical map. Assume the weight-$0$ and weight-$1$ pieces are complementary for the Cartier modules of `t'.XS g` relative to `jS`, of `t'.XbarS g` relative to `jSbar`, and of $\bar\Phi_S = (\Phi \otimes K/pK)\otimes S/pS$ relative to `jPhiS`, and let $L'$ be a canonical $L$-map for the datum of `t'.XS g`. Then for every canonical $L$-map $L_\Phi$ on the graded Cartier datum $D'$ of $\bar\Phi_S$ and every $x$ in the degree-$0$ $\eta$-piece of $D'$ determined by $L_\Phi$, there is $w \in \mathbb Z_p^2$ such that the homomorphism $N(D_\Phi) \to N(D')$ induced by the base-change map `bcPhi` on Cartier modules (base change along the residue map of $\psi'$ followed by that of $g$, which commutes with Verschiebung and with $\varpi$) sends $r_\Phi(w)$ to $x$.
--
--   This is the surjectivity half of the comparison, at a geometric fibre, between the rigidification of the base point $\Phi$ and the degree-zero $\eta$-lattice of its base change: every element of the degree-zero $\eta$-piece over $S$ comes from $\mathbb Z_p^2$ through $r_\Phi$ and `bcPhi`. It is used, together with the corresponding inclusion and injectivity statements, in the determinant computations `exists_det_eq_mul_pow_two_mul_add_one_of_smul_rigidNum_eq_nMk_mulVec_of_lieOne_le_ker_of_isAlgClosed_wittVector` and `exists_det_eq_mul_pow_two_mul_of_rigidNum_eq_nMk_mulVec_of_lieZero_le_ker_of_isAlgClosed_wittVector`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nMap_bcPhi_rPhi_eq_of_mem_etaPiece_zero_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_nMap_bcPhi_rPhi_eq_of_mem_etaPiece_zero_of_isAlgClosed
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
    ∀ (LΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).M →+ ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).NMod) (hLΦ : ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).IsCanonicalLMap LΦ),
      ∀ x ∈ (((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1).etaPiece LΦ hLΦ.isCartierLMap.map_verschiebung 0),
        ∃ w : Fin 2 → ℤ_[p], (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))).toGradedCartierModuleData (Rigidified.jPhiS ι ψ' (Rigidified.awayHom (1 : K))) hcΦ1) (Rigidified.bcPhi (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ' (Rigidified.awayHom (1 : K))) (rΦ w) = x := by sorry
