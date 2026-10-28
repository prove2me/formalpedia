-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_true_drawdown_limsup_test_joint_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_true_drawdown_limsup_test_joint_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-28T20:12:43.247299+00:00
-- url     : https://prove2.me/theorems/fac2f5c9-eea7-4503-ad75-1eb291f4c32b
-- title:
--   Jointly measurable limsup of dyadic sampled drawdown exponential on unrestricted random-terminal path space
-- statement:
--   For every countable deterministic nonnegative sampling schedule and real β, the countable infimum of countable supremum tails of the dyadic-ceiling prefix drawdown exponential is jointly measurable on clock time times the full product-Pi space of real-valued paths. The measurable functional is the literal pointwise ENNReal limsup of the finite dyadic rewards proved measurable in the accepted 46658681 theorem. On actual Lévy and shifted post-record paths it identifies with the exponential of the true random-terminal drawdown, using pathwise convergence 5886c047 and its shifted analogue. This is required to instantiate genuine Qp first-record full-path regeneration 4cf7269f on the true terminal-drawdown reward without an unproved dominated-convergence interchange.
-- source:
--   Accepted measurable dyadic reward 46658681; actual pathwise Cantor dyadic convergence 5886c047; uncapped random-terminal Qp regeneration 4cf7269f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_true_drawdown_limsup_test_joint_measurable
    (samples : ℕ → ℝ≥0) (β : ℝ) :
    Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      ⨅ k : ℕ, ⨆ n : ℕ, if k ≤ n then
        let r : ℝ≥0 :=
          (Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n
        ENNReal.ofReal (Real.exp
          (-β * ((⨆ i : ℕ, if samples i ≤ r then
            ENNReal.ofReal (z.2 (samples i)) else 0).toReal - z.2 r)))
      else 0) := by sorry
