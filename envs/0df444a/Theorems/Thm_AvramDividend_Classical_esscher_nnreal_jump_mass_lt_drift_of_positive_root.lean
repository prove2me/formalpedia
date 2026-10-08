-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_nnreal_jump_mass_lt_drift_of_positive_root
-- name    : AvramDividend.Classical.esscher_nnreal_jump_mass_lt_drift_of_positive_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:18:59.703278+00:00
-- url     : https://prove2.me/theorems/e0fdb780-c855-42e0-ad6f-2e4bb45e4c17
-- title:
--   Strict subcriticality of Esscher discounted jump mass in nonnegative magnitudes
-- statement:
--   With positive φ and q satisfying δ φ−∫(1−exp(−φ z))dν=q>0, the discounted first moment ∫z exp(−φ z)dν is strictly below δ. Prove using φ z exp(−φ z) ≤ 1−exp(−φ z), a consequence of exp t≥1+t, integral monotonicity and φ>0. The ν measure lives on NNReal positive jump magnitudes as in the canonical Proved BV exponent identity, avoiding measure-pushforward normalization.
-- source:
--   BV Lévy–Khintchine Esscher root and Real.add_one_le_exp; pinned Mathlib integral_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_nnreal_jump_mass_lt_drift_of_positive_root
    (ν : Measure ℝ≥0) (δ φ q : ℝ)
    (hφ : 0 < φ) (hq : 0 < q)
    (hA : Integrable (fun z : ℝ≥0 =>
      (z : ℝ) * Real.exp (-(φ * (z : ℝ)))) ν)
    (hJ : Integrable (fun z : ℝ≥0 =>
      1 - Real.exp (-(φ * (z : ℝ)))) ν)
    (hroot : δ * φ -
      (∫ z : ℝ≥0, 1 - Real.exp (-(φ * (z : ℝ))) ∂ν) = q) :
    (∫ z : ℝ≥0, (z : ℝ) * Real.exp (-(φ * (z : ℝ))) ∂ν) < δ := by sorry
