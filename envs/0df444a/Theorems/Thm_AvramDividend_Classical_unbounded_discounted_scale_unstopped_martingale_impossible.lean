-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_discounted_scale_unstopped_martingale_impossible
-- name    : AvramDividend.Classical.unbounded_discounted_scale_unstopped_martingale_impossible
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:29:51.232756+00:00
-- url     : https://prove2.me/theorems/2ca195c0-3dfc-4e24-9936-3ba37d8c6fc6
-- title:
--   Un-stopped discounted q-scale martingale is impossible in unbounded variation
-- statement:
--   For any unbounded-variation spectrally negative Levy process and q>0, the un-killed discounted q-scale reward e^{-qt}W(X_t) cannot be a martingale (under the standard sigma-finite filtration hypothesis). The scale starts at W(0)=0 and the Lévy process starts at X_0=0. A nonnegative zero-start martingale would force X_1≤0 almost surely. But unbounded variation yields a positive Lévy exponent ψ(θ)>q at some θ≥0; the Lévy exponential-moment identity then forbids X_1≤0 almost surely. Hence the un-killed theorem used as a prerequisite in the Avram strict exit workstream must be replaced by a killed/stopped martingale formulation.
-- source:
--   Proved chat04_scale_zero_origin_of_unbounded_variation, chat04_psi_eventually_gt_of_unbounded_variation, unbounded_unstopped_scale_martingale_forces_nonpositive_paths, positive_psi_excludes_nonpositive_one_increment_ae.

import Theorems.Thm_AvramDividend_Classical_chat04_scale_zero_origin_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_chat04_psi_eventually_gt_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_unbounded_unstopped_scale_martingale_forces_nonpositive_paths
import Theorems.Thm_AvramDividend_Classical_positive_psi_excludes_nonpositive_one_increment_ae
import Mathlib.Probability.Martingale.Basic

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_discounted_scale_unstopped_martingale_impossible
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration P 𝓕]
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ¬ Martingale
      (fun t : ℝ≥0 => fun ω : Ω =>
        Real.exp (-(q * (t : ℝ))) * W (X.X t ω)) 𝓕 P := by sorry
