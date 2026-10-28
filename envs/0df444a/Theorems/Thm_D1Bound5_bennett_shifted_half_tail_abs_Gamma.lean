-- Prove2me | Theorems.Thm_D1Bound5_bennett_shifted_half_tail_abs_Gamma
-- name    : D1Bound5.bennett_shifted_half_tail_abs_Gamma
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:29.981587+00:00
-- url     : https://prove2.me/theorems/b4db1c9a-0717-442f-9d37-958668faff95
-- title:
--   Bennett shifted half tail abs Gamma
-- statement:
--   Exact absolute Gamma formula after the positive part of a shifted half-binomial coefficient. This is proved from finite choose identities, factorials, and Gamma at positive half-integers, without reflection or a contour representation.
-- source:
--   D1Bound5/BennettChooseGamma.lean, lines 76-142, SHA-256 ed364c7393e2791f97fcc92aa240c1e9f11c109de4d2306c76becc3f16ded4f0. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

section
open Polynomial

namespace D1Bound5












theorem _root_.D1Bound5.bennett_shifted_half_tail_abs_Gamma (k m : ℕ) :
    |Ring.choose ((k : ℝ) + 1 / 2) (k + 1 + m)| =
      Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma ((m : ℝ) + 1 / 2) /
        (Real.pi * Real.Gamma (((k + 1 + m : ℕ) : ℝ) + 1)) := by sorry



end D1Bound5
end
