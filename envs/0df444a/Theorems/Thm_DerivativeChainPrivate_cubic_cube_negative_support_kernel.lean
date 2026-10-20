-- Prove2me | Theorems.Thm_DerivativeChainPrivate_cubic_cube_negative_support_kernel
-- name    : DerivativeChainPrivate.cubic_cube_negative_support_kernel
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-19T11:14:16.013983+00:00
-- url     : https://prove2.me/theorems/014c7cb5-4096-4c01-b0d2-37ebde136d50
-- title:
--   The cubic-cube negative-cut kernel is positive and bounded by four fifths
-- statement:
--   For all real X>=5/2, Y>=0 and 0<=a<=1/6, the denominator D=(X+a)^2+2(X-a)Y+Y^2 is positive and (2(X+Y)+a)/D<=4/5. This is the negative-support kernel estimate needed by the cubic-cube analytic comparison. No inverse-measure representation, root existence, or full chain theorem is asserted.
-- source:
--   Derivative-zero chains: public formalization reference, R57, DerivativeChainPrivate.cubic_cube_negative_support_kernel. https://gist.github.com/Amal-David/d6612109c98595b12561cd638c60edf5/3883c57ddc7bf9d4c0e898c3d6bfd2ca0d7f9c95#file-notes-md

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false

theorem DerivativeChainPrivate.cubic_cube_negative_support_kernel (X Y a : ℝ)
    (hX : 5 / 2 ≤ X) (hY : 0 ≤ Y) (ha : 0 ≤ a) (ha' : a ≤ 1 / 6) :
    0 < (X + a) ^ 2 + 2 * (X - a) * Y + Y ^ 2 ∧
      (2 * (X + Y) + a) / ((X + a) ^ 2 + 2 * (X - a) * Y + Y ^ 2) ≤ 4 / 5 := by sorry
