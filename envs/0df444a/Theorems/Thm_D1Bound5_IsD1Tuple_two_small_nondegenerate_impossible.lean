-- Prove2me | Theorems.Thm_D1Bound5_IsD1Tuple_two_small_nondegenerate_impossible
-- name    : D1Bound5.IsD1Tuple.two_small_nondegenerate_impossible
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:30:23.824347+00:00
-- url     : https://prove2.me/theorems/15f23883-5b61-4356-982f-dc5eb7923a9e
-- title:
--   Exclusion of nondegenerate sextuples with exactly two small entries
-- statement:
--   Let K be an imaginary quadratic number field, let phi be a complex embedding, and let t be a Diophantine sextuple in its full ring of integers. Assume that the absolute values of the images of its entries are nondecreasing. Such a sextuple is impossible if the second absolute value is below 3, the third is at least 3, and the product of the first two entries plus one is nonzero.
--
--   The sextuple consists of distinct nonzero algebraic integers, and the product of any two distinct entries plus one is a square in the full ring of integers. Equal absolute values are permitted. This is one of the exhaustive branches used to establish the cardinality bound.
-- source:
--   D1Bound5/TwoSmallNondegenerateImpossible.lean, D1Bound5.IsD1Tuple.two_small_nondegenerate_impossible, lines 12-19; exact source SHA-256 cd2e46669d5180d170708c2c6e146711677502487bd331463fa9c364e4d7b7bb. Project: https://github.com/tomislav-math/d1-bound5-lean

import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_MainStatement
import Mathlib.Analysis.Complex.Basic

open scoped NumberField
open Module D1Bound5

theorem D1Bound5.IsD1Tuple.two_small_nondegenerate_impossible
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 6 → 𝓞 K) (ht : IsD1Tuple t)
    (hmon : Monotone (fun i => ‖phi (t i : K)‖))
    (hsmall : ‖phi (t 1 : K)‖ < 3)
    (hlarge : 3 ≤ ‖phi (t 2 : K)‖)
    (hnondeg : t 0*t 1+1 ≠ 0) : False := by sorry
