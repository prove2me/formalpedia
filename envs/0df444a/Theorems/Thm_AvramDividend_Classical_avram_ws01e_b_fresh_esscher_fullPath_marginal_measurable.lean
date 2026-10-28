-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_fresh_esscher_fullPath_marginal_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_fresh_esscher_fullPath_marginal_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:41:17.165899+00:00
-- url     : https://prove2.me/theorems/da8731ac-c935-458e-9c89-11bfa43bbd03
-- title:
--   Measurability of the complete Lévy future-path Esscher reward integrated over paths at a real clock
-- statement:
--   For a genuine spectrally negative Lévy process, any real Esscher parameter and jointly measurable nonnegative reward H of a nonnegative observation clock and entire Lévy path, the fresh-side marginal r↦∫P exp(θX_{r+}−r+ψθ) H(r+,X) is a measurable function of real observation time. Here r+=Real.toNNReal r; no random-terminal global tilted path law is assumed. This directly discharges the hRMeas side condition in the open capped genuine-Qp fullPath regeneration theorem, provided its reward H is jointly measurable rather than only sectionwise measurable.
-- source:
--   Proved levy_wholePath_measurable (840bbf85), chat04_levy_joint_time_state_measurable (d55462c3), and pinned Mathlib Measurable.lintegral_prod_left under [SFinite P].

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_fresh_esscher_fullPath_marginal_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ)
    (H : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hH : Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      H z.1 z.2)) :
    Measurable (fun r : ℝ =>
      (∫⁻ ω : Ω,
        ENNReal.ofReal (Real.exp
          (θ * X.X (Real.toNNReal r) ω -
            (Real.toNNReal r : ℝ) * X.ψ θ)) *
        H (Real.toNNReal r)
          (fun s : ℝ≥0 => X.X s ω) ∂P)) := by sorry
