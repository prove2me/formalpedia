-- Prove2me | Theorems.Thm_EnsembleSpaceDraft_extreme_iff_not_decomposable
-- name    : EnsembleSpaceDraft.extreme_iff_not_decomposable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-18T11:50:48.77041+00:00
-- url     : https://prove2.me/theorems/3f8592f6-0190-4393-aa58-b906c640dc90
-- title:
--   Corollary 1.32 — extreme points are the non-decomposable ensembles
-- statement:
--   An ensemble $e$ is extreme if and only if it is not decomposable.
--
--   Extreme means that $e$ has no component distinct from itself (Definition 1.20). Decomposable means that $e=pa+\bar p b$ for some $p\in(0,1)$ and some distinct ensembles $a,b$ (Definition 1.31). This is Corollary 1.32.
-- source:
--   G. Carcassi, C. A. Aidala, Ensemble spaces, draft of 12 October 2026, Chapter 1. Generated from https://github.com/assumptionsofphysics/book (art_pm_EnsembleSpaces). Corollary 1.32, pp. 25–26; Definitions 1.20 and 1.31.

import Definitions.Def_EnsembleSpaceDraft_axioms
import Mathlib

open scoped unitInterval

namespace EnsembleSpaceDraft

universe u

/-- Corollary 1.32. An ensemble is extreme if and only if it is not decomposable. -/
theorem extreme_iff_not_decomposable {E : Type u} [TopologicalSpace E] (X : EnsembleSpace E)
    (e : E) :
    X.IsExtreme e ↔ ¬ X.IsDecomposable e := by
  sorry

end EnsembleSpaceDraft
