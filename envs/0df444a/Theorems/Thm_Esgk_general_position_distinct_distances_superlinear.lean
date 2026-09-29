-- Prove2me | Theorems.Thm_Esgk_general_position_distinct_distances_superlinear
-- name    : Esgk.general_position_distinct_distances_superlinear
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-09-14T18:03:51.438175+00:00
-- url     : https://prove2.me/theorems/dfa50bdc-3d25-4f99-aa26-0cbbcbee7797
-- title:
--   Superlinear growth of distinct distances in general position
-- statement:
--   For every real constant $A>0$, there is a threshold N_A such that, for every natural number n ≥ N_A and every injective configuration p : Fin(n) → ℝ² whose image has no three collinear points and no four cocircular points, the number D(P) of distinct Euclidean distances determined by the image P satisfies
--
--   $$D(P)>A n.$$
--
--   The threshold may depend on A, while the conclusion must hold uniformly for every qualifying configuration of size n. Here D(P) counts each distance value once, even when multiple ordered pairs determine it. This is the superlinear-growth target of Erdős Problem 98 and remains an open problem in this Lean formalization.
-- source:
--   Erdős Problem 98, https://www.erdosproblems.com/98; project current mission description: prove2me/mission-superlinear-description.md (2026-09-14)

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_Esgk_Foundation

open EuclideanGeometry Filter

namespace Esgk

/-- Open problem target for Erdős Problem 98; no Lean proof is supplied. -/
theorem general_position_distinct_distances_superlinear :
    ∀ A : ℝ, 0 < A →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∀ p : Config n,
          Function.Injective p →
          InGeneralPosition (Config.toFinset p) →
          A * (n : ℝ) < (distinctDistances (Config.toFinset p) : ℝ) := by
  sorry

end Esgk
