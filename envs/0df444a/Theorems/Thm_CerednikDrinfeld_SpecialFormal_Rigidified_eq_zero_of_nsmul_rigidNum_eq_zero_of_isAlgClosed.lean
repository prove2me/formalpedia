-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_zero_of_nsmul_rigidNum_eq_zero_of_isAlgClosed
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.eq_zero_of_nsmul_rigidNum_eq_zero_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/9f2bab22-7213-51fe-8a88-1242af0a2a26
-- title:
--   Injectivity of the rigid numerator over an algebraically closed field
-- statement:
--   Fix a prime $p$ and an algebraically closed field $k$ of characteristic $p$, together with a ring homomorphism $\iota$ from $\mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2})$ to $W(k)$. Let $\Phi$ be a formal $O_D$-module over $W(k)/pW(k)$, that is, a two-dimensional commutative formal group law carrying a $\mathbb{Z}_{p^2}$-action and an endomorphism $\varpi$ with $\varpi\circ\varpi = [p]$ and $\varpi\circ[a] = [\sigma a]\circ\varpi$. Assume: $\Phi$ is special for the reduction $\bar\iota$ of $\iota$ (the weight-$0$ and weight-$1$ subspaces of its Lie algebra are complementary and invertible); $\Phi$ has height $4$, i.e. the kernel of $[p]$ has degree $p^4$; the weight-$0$ Lie subspace lies in the kernel of the linear part of $\varpi$; the graded pieces $0$ and $1$ of the Cartier module of $\Phi$ are complementary, giving graded Cartier module data $D_\Phi$; and an additive map $r_\Phi : \mathbb{Z}_p^2 \to N(D_\Phi)$ is given which, for every canonical $L$-map $L$ on $D_\Phi$, maps $\mathbb{Z}_p^2$ bijectively onto $\eta_0(L) = \eta(L)\cap N(D_\Phi)_0$. Let further $K$ be an algebraically closed field of characteristic $p$ and a $\mathbb{Z}_p$-algebra, $\psi' : W(k) \to K$ a ring homomorphism, with $p$ nilpotent in $K$; let $t'$ be a rigidified object over $K$ (a formal $O_D$-module $X$, an integer $n$, and a series $\rho$ over $K/pK$) which is admissible for $\iota,\psi'$: $X$ is special, of height $4$, and $\rho$ is an isogeny of height $4n$ from the base change of $\Phi$ to $\bar X$. Assume the gradedness conditions for $X$, for $\bar X$ and for the base change of $\Phi$ over the localisation of $K$ at the powers of $1$, and let $L'$ be a canonical $L$-map on the graded Cartier module data of $X$ over that localisation. Then for all $u \in \mathbb{Z}_p^2$ and all $N \in \mathbb{N}$, if $p^N \cdot r(u) = 0$, where $r$ is the composite of $r_\Phi$ with the $N$-functor maps induced by base change along $\psi'$ and by $\bar\rho$, then $u = 0$.
--
--   The assertion is that the rigid numerator $r$, the map $\mathbb{Z}_p^2 \to N(M_{\bar X})$ built from $r_\Phi$ by base change and by push-forward along the isogeny $\bar\rho$, is injective modulo $p$-power torsion; it expresses the torsion-freeness needed to read off coordinates on the $\eta$-part of the Cartier $N$-module over an algebraically closed base. It is used in the construction of $\eta$-sections and their coordinates in the Čerednik–Drinfeld uniformisation argument, being cited by [`CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.isEtaSection_coordinates_of_isAlgClosed) and by [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_pow_smul_eq_coe_of_isEtaSection_zero_of_isAdmissible_of_isAlgClosed_of_lieZero_le_ker_wittVector).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_eq_zero_of_nsmul_rigidNum_eq_zero_of_isAlgClosed.lean

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

theorem CerednikDrinfeld.SpecialFormal.Rigidified.eq_zero_of_nsmul_rigidNum_eq_zero_of_isAlgClosed
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
    ∀ (u : Fin 2 → ℤ_[p]) (N : ℕ), p ^ N • t'.rigidNum ι hcΦ rΦ ψ' ht'.2.2.1 (Rigidified.awayHom (1 : K)) hcb hcΦ1 u = 0 → u = 0 := by sorry
