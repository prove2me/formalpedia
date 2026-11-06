-- Prove2me | Theorems.Thm_BlockBochner_bochner_coercivity
-- name    : BlockBochner.bochner_coercivity
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:38:49.115421+00:00
-- url     : https://prove2.me/theorems/4687ed6f-fa07-483d-9281-30a848ecd0f9
-- title:
--   Sec. 3.3, p.23 — coercivity of the Bochner operator $B\succeq\lambda_{\min}(M)I$
-- statement:
--   Let $H$ be a real Hilbert space, $W_1,\dots,W_n$ closed subspaces with orthogonal projections $P_i$, $P_{ij}$ the projection onto $W_i\cap W_j$, and $S=(s_{ij})$ a real symmetric matrix with non-negative entries, zero diagonal and $\lambda_{\max}(S)<1$ such that $\|P_iP_j-P_{ij}\|\le s_{ij}$ for all $i\ne j$. Let $M=I-S$ and let $B$ be the Bochner operator on $H_1=\bigoplus_iW_i$.
--   Then
--   $$B\succeq\lambda_{\min}(M)\,I;$$
--   therefore $B$ is boundedly invertible and $B^{-1}\preceq\lambda_{\min}(M)^{-1}I$.
--
--   The positive lower bound comes from $B_{ii}\succeq I$, $\|B_{ij}\|\le s_{ij}$ and $\lambda_{\max}(S)<1$.
--
--   Differences from the source: none.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 3.3, p.23

import Mathlib
import Definitions.Def_BlockBochner_bochnerOp
import Definitions.Def_BlockBochner_IsAdmissible
import Definitions.Def_BlockBochner_lamMin

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Coercivity of the Bochner operator.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 3.3, p.23 ("Coercivity of the Bochner
operator"): `B ⪰ λ_min(M) I`; therefore `B` is boundedly invertible and `B⁻¹ ⪯ λ_min(M)⁻¹ I`.

Setting of Sec. 3.2 (p.21): `H` a real Hilbert space, `W₁, …, W_n` closed subspaces with orthogonal
projections `P_i`, `P_{ij}` the projection onto `W_i ∩ W_j`, and `S` a real symmetric matrix with
non-negative entries, zero diagonal and `λ_max(S) < 1` such that `‖P_i P_j − P_{ij}‖ ≤ s_{ij}` for all
`i ≠ j`; `M = I − S`.

**Formalization Note** `B = bochnerOp W` on `⊕_i W_i`; `B⁻¹` is `Ring.inverse`. -/
theorem bochner_coercivity {n : ℕ} (W : Fin n → ClosedSubmodule ℝ H) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : IsAdmissible S)
    (hang : ∀ i j, i ≠ j → ‖(W i : Submodule ℝ H).starProjection ∘L (W j : Submodule ℝ H).starProjection -
      ((W i ⊓ W j : ClosedSubmodule ℝ H) : Submodule ℝ H).starProjection‖ ≤ S i j) :
    (∀ g, lamMin (1 - S) * ‖g‖ ^ 2 ≤ inner ℝ g (bochnerOp W g)) ∧ IsUnit (bochnerOp W) ∧
      ∀ g, inner ℝ g (Ring.inverse (bochnerOp W) g) ≤ (lamMin (1 - S))⁻¹ * ‖g‖ ^ 2 := by sorry

end BlockBochner
