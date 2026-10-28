-- Prove2me | Theorems.Thm_D1Bound5_coherent_cpow_half_sq
-- name    : D1Bound5.coherent_cpow_half_sq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T21:42:48.561733+00:00
-- url     : https://prove2.me/theorems/25b8af4e-a608-4eb5-ae0f-a458d1d199b3
-- title:
--   Squaring the principal complex half power
-- statement:
--   For every complex number $z$, including zero, the principal complex power satisfies
--   $$\bigl(z^{1/2}\bigr)^2=z.$$
--   This identity fixes the square-root convention used in the interpolation estimates.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, D1Bound5.coherent_cpow_half_sq, lines 358-363; original file SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.SpecialFunctions.Pow.Complex

theorem D1Bound5.coherent_cpow_half_sq (z : ℂ) :
    (z ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = z := by sorry
