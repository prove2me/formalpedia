-- Prove2me | Theorems.Thm_BitDFT_fixed_point_product_error
-- name    : BitDFT.fixed_point_product_error
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T01:23:23.206616+00:00
-- url     : https://prove2.me/theorems/00f651d0-8d29-4915-9f61-9a905a2f2041
-- title:
--   Fixed-point complex multiplication adds input error and fewer than two ulps
-- statement:
--   For fixed-point complex values U and V in the unit disc, multiplying their represented values and rounding each output coordinate toward zero incurs fewer than two additional ulps. If u and v are also in the unit disc, the total product error is strictly less than the sum of the two input ulp errors plus 2. The bound is independent of precision and coefficient magnitude within the unit disc.
-- source:
--   Numerical component of the BitDFT.fixed_point_multiplication obligation. The proof derives the scalar round-toward-zero error from floor/ceiling bounds, combines the two coordinate errors using the complex norm triangle inequality, and uses the product perturbation identity (a-u)b + u(b-v). This theorem proves only the numerical error bound; it does not construct the multitape multiplication machine required by the parent theorem.

import Definitions.Def_BitDFT_Numerics
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
open BitDFT

theorem BitDFT.fixed_point_product_error (p : ℕ) (U V : ℤ × ℤ)
    (hU : inDisc p U) (hV : inDisc p V) (u v : ℂ)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    ulpError p (roundPair p (value p U * value p V)) (u * v) <
      ulpError p U u + ulpError p V v + 2 := by sorry
