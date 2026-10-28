-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_not_one_small
-- name    : D1Bound5.IsD1Tuple.not_one_small
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:30:19.571612+00:00
-- url     : https://prove2.me/theorems/a5c45153-39ea-4693-96b9-bb1b407e4db3
-- title:
--   Exclusion of sextuples with exactly one small entry
-- statement:
--   Let K be an imaginary quadratic number field, let phi be a complex embedding, and let t be a Diophantine sextuple in its full ring of integers. Assume that the absolute values of the images of its entries are nondecreasing. Such a sextuple is impossible if the first absolute value is below 3 and the second absolute value is at least 3.
--
--   The sextuple consists of distinct nonzero algebraic integers, and the product of any two distinct entries plus one is a square in the full ring of integers. Equal absolute values are permitted. This is one of the exhaustive branches used to establish the cardinality bound.
-- source:
--   D1Bound5/OneSmallImpossible.lean, D1Bound5.IsD1Tuple.not_one_small, lines 13-18; exact source SHA-256 bc74e35dff73f3a31c3a0c7289fa9bc0b4bcfd974356cedbecf1e757ce31954a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_MainStatement
import Mathlib.Analysis.Complex.Basic

open scoped NumberField
open Module D1Bound5

theorem D1Bound5.IsD1Tuple.not_one_small
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hA : ‖phi (a 0 : K)‖ < 3) (hB : 3 ≤ ‖phi (a 1 : K)‖) : False := by sorry
