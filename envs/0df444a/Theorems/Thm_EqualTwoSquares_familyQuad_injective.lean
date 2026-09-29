-- Prove2me | Theorems.Thm_EqualTwoSquares_familyQuad_injective
-- name    : EqualTwoSquares.familyQuad_injective
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-26T11:24:56.246988+00:00
-- url     : https://prove2.me/theorems/3760d32c-b023-4061-bd40-08f6ca2583cf
-- title:
--   The family parametrisation is injective
-- statement:
--   The map sending an integer n to the quadruple (1, n^2 - n + 1, 2n - 1, n^2 - n - 1) of integers is injective on all of the integers.
-- source:
--   Mission target; machine-checked locally in examples/two-squares/Family.lean.

import Mathlib

namespace EqualTwoSquares

/-- Objective 3: the parametrisation n ↦ (1, n^2-n+1, 2n-1, n^2-n-1) is injective. -/
theorem familyQuad_injective :
    Function.Injective
      (fun n : ℤ => ((1 : ℤ), n^2 - n + 1, 2 * n - 1, n^2 - n - 1)) := by sorry

end EqualTwoSquares
