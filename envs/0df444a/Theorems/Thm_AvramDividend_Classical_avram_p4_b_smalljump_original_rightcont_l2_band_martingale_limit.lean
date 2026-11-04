-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightcont_l2_band_martingale_limit
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_rightcont_l2_band_martingale_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:38:00.250003+00:00
-- url     : https://prove2.me/theorems/0fc9c4fb-2505-4402-80dc-02405da8f273
-- title:
--   Original right-continuous filtration L2 finite-band martingale closure without sigma-finiteness assumption
-- statement:
--   On the original probability and right-continuous source filtration, an L2 limit of adapted finite-band martingales is adapted and a martingale, assuming actual L2 convergence, finite-band adaptation and conditional increment centring. Sigma-finiteness of the right-continuous trimmed probability is discharged by the separately Proved original-source helper. This does not assert existence or centring of any original compensated Lévy jump integral.
-- source:
--   Accepted original-filtration L2 martingale closure 2ac43d23, and accepted original right-continuous trimmed probability sigma-finiteness 159a9398.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02b_original_filtration_l2_band_martingale_limit
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_rightcont_l2_band_martingale_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (L : ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P)
    (hconv : ∀ t, Tendsto (fun n => M n t) atTop (𝓝 (L t)))
    (hAdapt : ∀ s n,
      ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (M n s) :
        Lp ℝ (2 : ℝ≥0∞) P) = M n s)
    (hCenter : ∀ s t, s ≤ t → ∀ n,
      (MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (M n t - M n s) = 0) :
    (∀ s, ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (L s) :
      Lp ℝ (2 : ℝ≥0∞) P) = L s) ∧
    (∀ s t, s ≤ t →
      ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le s)) (L t) :
        Lp ℝ (2 : ℝ≥0∞) P) = L s) := by sorry
