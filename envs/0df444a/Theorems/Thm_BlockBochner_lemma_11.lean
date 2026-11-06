-- Prove2me | Theorems.Thm_BlockBochner_lemma_11
-- name    : BlockBochner.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:28.941216+00:00
-- url     : https://prove2.me/theorems/15282a4b-2396-4fbb-bec9-d5e6f32defba
-- title:
--   Lemma 11 — angle-norm equivalence
-- statement:
--   Let $P_i,P_j,P_{ij}$ be the orthogonal projections onto closed subspaces $W_i$, $W_j$ and $W_i\cap W_j$ of a real Hilbert space. Then
--   $$\cos(W_i,W_j)=\|P_iP_j-P_{ij}\|_{\mathrm{op}} .$$
--
--   The norm condition $\|P_iP_j-P_{ij}\|\le s_{ij}$ of Theorem 21 is therefore a bound on the Friedrichs angle.
--
--   Differences from the source:
--   - encoding: cos(U, W) as a supremum over non-zero pairs, left undefined when there is none → friedrichsCos, with value 0 when no admissible pair exists; reason: the right-hand side is 0 exactly then, so the identity is the source's whenever the supremum is defined
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Lemma 11, p.15

import Mathlib
import Definitions.Def_BlockBochner_friedrichsCos

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Lemma 11 (angle-norm equivalence).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Lemma 11, p.15. For closed subspaces `W_i`, `W_j`
with orthogonal projections `P_i`, `P_j`, and `P_{ij}` the projection onto `W_i ∩ W_j`,
`cos(W_i, W_j) = ‖P_i P_j − P_{ij}‖_op`.

**Formalization Note** `cos` is `friedrichsCos` (value `0` when no admissible pair exists). -/
theorem lemma_11 (Wi Wj : ClosedSubmodule ℝ H) :
    friedrichsCos (Wi : Submodule ℝ H) Wj =
      ‖(Wi : Submodule ℝ H).starProjection ∘L (Wj : Submodule ℝ H).starProjection -
        ((Wi ⊓ Wj : ClosedSubmodule ℝ H) : Submodule ℝ H).starProjection‖ := by sorry

end BlockBochner
