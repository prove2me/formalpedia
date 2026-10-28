-- Prove2me | Theorems.Thm_D1Bound5_card_bound_iff_no_ordered_sextuple
-- name    : D1Bound5.card_bound_iff_no_ordered_sextuple
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:26:58.493994+00:00
-- url     : https://prove2.me/theorems/d002bcf2-0ae5-4833-99f8-a616846d3e1d
-- title:
--   Cardinality bound and exclusion of ordered sextuples
-- statement:
--   Let R be a commutative ring, let W be a linearly ordered type, and let w map R to W. The following are equivalent:
--
--   1. Every finite Diophantine set in R has cardinality at most five.
--   2. There is no injective Diophantine sextuple whose weights are nondecreasing.
--
--   Equal weights are allowed. This converts a bound on arbitrary finite sets into the exclusion of ordered six-element tuples.
-- source:
--   https://github.com/tomislav-math/d1-bound5-lean/blob/a019c2a2b8e7a40dcf88c9d119d225cce84a61df/D1Bound5/Sextuple.lean#L49-L64

import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.EquivFin

open D1Bound5

theorem D1Bound5.card_bound_iff_no_ordered_sextuple {R W : Type*} [CommRing R] [LinearOrder W]
    (weight : R → W) :
    (∀ A : Finset R, IsD1 A → A.card ≤ 5) ↔
      ∀ f : Fin 6 → R, IsD1Tuple f → Monotone (weight ∘ f) → False := by sorry
