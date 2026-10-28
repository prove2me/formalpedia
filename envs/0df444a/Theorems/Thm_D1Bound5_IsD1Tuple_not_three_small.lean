-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_not_three_small
-- name    : D1Bound5.IsD1Tuple.not_three_small
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:30:23.749514+00:00
-- url     : https://prove2.me/theorems/9b9374e1-0421-4a79-acfd-c7ba1ab29be1
-- title:
--   Exclusion of sextuples with three small entries
-- statement:
--   Let K be an imaginary quadratic number field, let phi be a complex embedding, and let t be a Diophantine sextuple in its full ring of integers. Assume that the absolute values of the images of its entries are nondecreasing. Such a sextuple is impossible if the third absolute value is below 3.
--
--   The sextuple consists of distinct nonzero algebraic integers, and the product of any two distinct entries plus one is a square in the full ring of integers. Equal absolute values are permitted. This is one of the exhaustive branches used to establish the cardinality bound.
-- source:
--   D1Bound5/ThreeSmallExclusion.lean, D1Bound5.IsD1Tuple.not_three_small, lines 12-17; exact source SHA-256 0dc7dba5727b9d1694bbd794d4a0876ffc8c3e3b74991534d3bd30a3608db3bd. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_MainStatement
import Mathlib.Analysis.Complex.Basic

open scoped NumberField
open Module D1Bound5

theorem D1Bound5.IsD1Tuple.not_three_small
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 6 → 𝓞 K) (ha : IsD1Tuple a)
    (hmon : Monotone (fun i => ‖phi (a i : K)‖))
    (hsmall : ‖phi (a 2 : K)‖ < 3) : False := by sorry
