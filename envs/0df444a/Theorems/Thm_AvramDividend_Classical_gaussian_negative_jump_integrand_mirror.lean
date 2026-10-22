-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_integrand_mirror
-- name    : AvramDividend.Classical.gaussian_negative_jump_integrand_mirror
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:07:14.332698+00:00
-- url     : https://prove2.me/theorems/77cb59c6-bf69-4087-a8cd-935c9b6d374c
-- title:
--   Exact negative-jump compensator conversion with strict truncation
-- statement:
--   For every negative Lévy jump y, change variables to its positive magnitude z=-y. The canonical Lévy–Khintchine integrand with the open truncation interval (-1,1) equals the positive-magnitude exponential compensator with strict cutoff z<1. This records the boundary convention exactly and provides the pointwise bridge needed to transport the signed-jump integral in the mission's actual laplaceExponent definition to the Gaussian Esscher jump-magnitude machinery. The atom at z=1 requires a separate correction when using a non-strict cutoff.
-- source:
--   Mission declaration Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy, laplaceExponent; real-algebraic indicator identity.

import Mathlib
open Set

theorem AvramDividend.Classical.gaussian_negative_jump_integrand_mirror (θ y : ℝ) (hy : y < 0) :
    Real.exp (θ * y) - 1 -
      θ * y * (Ioo (-1 : ℝ) 1).indicator (1 : ℝ → ℝ) y =
    Real.exp (-θ * (-y)) - 1 +
      θ * (if -y < 1 then -y else 0) := by sorry
