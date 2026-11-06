-- Prove2me | Theorems.Thm_BlockBochner_lemma_12
-- name    : BlockBochner.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:36:27.409266+00:00
-- url     : https://prove2.me/theorems/74f0b8da-5bb2-4a13-825a-7f36be2c49a6
-- title:
--   Lemma 12 — orthogonal complements preserve angles
-- statement:
--   For closed subspaces $U,W$ of a real Hilbert space,
--   $$\cos(U,W)=\cos(U^\perp,W^\perp).$$
--
--   This is used in Lemma 13 to pass from conditional-expectation operators to Laplacians.
--
--   Differences from the source:
--   - encoding: cos(U, W) as a supremum over non-zero pairs, left undefined when there is none → friedrichsCos, with value 0 when no admissible pair exists; reason: no admissible pair for (U, W) iff none for (U⊥, W⊥) when U, W are closed; otherwise the values are the source's
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Lemma 12, p.15

import Mathlib
import Definitions.Def_BlockBochner_friedrichsCos

namespace BlockBochner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Lemma 12 (orthogonal complements preserve angles).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Lemma 12, p.15 (cited from
[Kas11]). For closed subspaces `U, W ⊆ H`, `cos(U, W) = cos(U^⊥, W^⊥)`. -/
theorem lemma_12 (U W : ClosedSubmodule ℝ H) :
    friedrichsCos (U : Submodule ℝ H) W =
      friedrichsCos (U : Submodule ℝ H)ᗮ (W : Submodule ℝ H)ᗮ := by sorry

end BlockBochner
