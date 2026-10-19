-- Prove2me | Theorems.Thm_EnsembleSpaceDraft_monodecomposable_iff_mixtures_preserve_separateness
-- name    : EnsembleSpaceDraft.monodecomposable_iff_mixtures_preserve_separateness
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T11:51:07.538272+00:00
-- url     : https://prove2.me/theorems/0950ee1a-bbfe-49d4-ae18-55a5216bded1
-- title:
--   Proposition 1.35 — monodecomposability and separateness
-- statement:
--   An ensemble space is monodecomposable if and only if mixtures preserve separateness in it.
--
--   The space is **monodecomposable** when every decomposable ensemble is monodecomposable: whenever $e=pa+\bar p b$ with $p\in(0,1)$ and $a\neq b$, there do not exist two decompositions
--   $$
--   e=p a_1+\bar p a_2=q b_1+\bar q b_2
--   $$
--   with coefficients in $(0,1)$, distinct summands, and $a_1$ separate from both $b_1$ and $b_2$ (Definitions 1.31 and 1.33).
--
--   **Mixtures preserve separateness** when $e$ separate from $a$ and from $b$ implies $e$ separate from $pa+\bar p b$ for every $p\in[0,1]$ (Definition 1.28).
--
--   This is Proposition 1.35, the convex characterization of that uniqueness of decomposition. No entropy, finite-dimensionality, or model hypothesis (classical or quantum) is used.
-- source:
--   G. Carcassi, C. A. Aidala, Ensemble spaces, draft of 12 October 2026, Chapter 1. Generated from https://github.com/assumptionsofphysics/book (art_pm_EnsembleSpaces). Proposition 1.35, pp. 26–27; Definitions 1.28, 1.31 and 1.33.

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval

namespace EnsembleSpaceDraft

universe u

/-- Proposition 1.35. An ensemble space is monodecomposable if and only if mixtures
preserve separateness. -/
theorem monodecomposable_iff_mixtures_preserve_separateness {E : Type u} [TopologicalSpace E]
    (X : EnsembleSpace E) :
    X.Monodecomposable ↔ X.MixturesPreserveSeparateness := by
  sorry

end EnsembleSpaceDraft
