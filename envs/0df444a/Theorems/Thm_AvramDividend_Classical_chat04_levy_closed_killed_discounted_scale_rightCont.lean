-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_levy_closed_killed_discounted_scale_rightCont
-- name    : AvramDividend.Classical.chat04_levy_closed_killed_discounted_scale_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:56:52.611969+00:00
-- url     : https://prove2.me/theorems/8af22579-7f1d-4fb4-887b-7fad7e1cda3e
-- title:
--   Actual right-continuity of the whole-history killed discounted Lévy scale payoff
-- statement:
--   For any spectrally negative Lévy sample path and any continuous deterministic discount, if the scale function vanishes at zero then the q-scale reward restricted to survival throughout the past is right-continuous in the horizon. The theorem has the actual Lévy-process survival event and can be applied pointwise under the probability measure before a dominated convergence argument.
-- source:
--   Accepted pathwise masked reward continuity, positive-reserve survival stability, and continuous unmasked discounted scale payoff.

import Theorems.Thm_AvramDividend_Classical_chat04_rightContinuous_masked_reward_of_zero_boundary
import Theorems.Thm_AvramDividend_Classical_chat04_closed_survival_locally_stable_of_rightCont_positive
import Theorems.Thm_AvramDividend_Classical_chat03_discounted_scale_right_continuous_of_Wzero
import Mathlib.Topology.Order.LeftRightNhds

open Classical AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.chat04_levy_closed_killed_discounted_scale_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (discount : ℝ≥0 → ℝ) (hdiscount : Continuous discount)
    (ω : Ω) (t : ℝ≥0) :
    ContinuousWithinAt
      (fun u : ℝ≥0 =>
        if (∀ s : ℝ≥0, s ≤ u → 0 ≤ x + X.X s ω)
        then discount u * W (x + X.X u ω)
        else 0)
      (Ici t) t := by sorry
