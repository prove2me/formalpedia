-- Prove2me | Theorems.Thm_D1Bound5_card_bound_iff_three_ordered_cases
-- name    : D1Bound5.card_bound_iff_three_ordered_cases
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:28:10.328313+00:00
-- url     : https://prove2.me/theorems/2a2d5927-3a0d-49a6-b264-3a664ca9f228
-- title:
--   Three exhaustive ordered sextuple cases
-- statement:
--   Let R be a commutative ring, let W be a linearly ordered type, let w map R to W, and let c be a cutoff. Every finite Diophantine set in R has cardinality at most five if and only if all three following kinds of nondecreasing Diophantine sextuple are impossible:
--
--   1. The first weight is at least c.
--   2. The first weight is below c and the second weight is at least c.
--   3. The second weight is below c.
--
--   These cases are exhaustive and allow equal weights. This equivalence isolates the three exclusions needed for a cardinality bound.
-- source:
--   D1Bound5/MainCaseReduction.lean, D1Bound5.card_bound_iff_three_ordered_cases, lines 67-90; exact source SHA-256 94580cd4f5977bc9f503aba3da8004380cecfe272766c2d856a70706a14c5d2b. Original project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_MainStatement
import Mathlib.Analysis.Complex.Basic
import Lean.Elab.Tactic.Omega

open D1Bound5
open scoped NumberField
universe u

theorem D1Bound5.card_bound_iff_three_ordered_cases
    {R W : Type*} [CommRing R] [LinearOrder W]
    (weight : R → W) (cutoff : W) :
    (∀ A : Finset R, IsD1 A → A.card ≤ 5) ↔
      (∀ t : Fin 6 → R, IsD1Tuple t → Monotone (weight ∘ t) →
        cutoff ≤ weight (t 0) → False) ∧
      (∀ t : Fin 6 → R, IsD1Tuple t → Monotone (weight ∘ t) →
        weight (t 0) < cutoff → cutoff ≤ weight (t 1) → False) ∧
      (∀ t : Fin 6 → R, IsD1Tuple t → Monotone (weight ∘ t) →
        weight (t 1) < cutoff → False) := by sorry
