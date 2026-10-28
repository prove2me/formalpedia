-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_residual_choose_abs_Gamma
-- name    : D1Bound5.bennett_two_residual_choose_abs_Gamma
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:39:13.738335+00:00
-- url     : https://prove2.me/theorems/6144e0e2-c147-421e-9f4f-e6e09d7d4fd4
-- title:
--   Bennett two residual choose abs Gamma
-- statement:
--   The exact coefficient at degree3k in the two-anchor residual is the beta/Gamma factor used by the manuscript.
-- source:
--   D1Bound5/BennettChooseGamma.lean, lines 144-157, SHA-256 ed364c7393e2791f97fcc92aa240c1e9f11c109de4d2306c76becc3f16ded4f0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

section
open Polynomial

namespace D1Bound5














theorem _root_.D1Bound5.bennett_two_residual_choose_abs_Gamma (k : ℕ) (hk : 1 ≤ k) :
    |Ring.choose ((k : ℝ) + 1 / 2) (3 * k)| =
      Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
        (Real.pi * Real.Gamma (3 * (k : ℝ) + 1)) := by sorry

end D1Bound5
end
