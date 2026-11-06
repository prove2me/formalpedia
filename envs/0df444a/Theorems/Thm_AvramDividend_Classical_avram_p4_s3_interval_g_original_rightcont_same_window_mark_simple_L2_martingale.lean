-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_g_original_rightcont_same_window_mark_simple_L2_martingale
-- name    : AvramDividend.Classical.avram_p4_s3_interval_g_original_rightcont_same_window_mark_simple_L2_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T14:47:43.645201+00:00
-- url     : https://prove2.me/theorems/1766fc2e-347e-471d-bdff-df0a3fb2b009
-- title:
--   Exact same-window original negative-mark simple predictable L2 centring on right-continuous filtration
-- statement:
--   For a finite collection of genuine original spectrally negative Levy negative-mark count rectangles on one deterministic time window, uniformly bounded H coefficients measurable in the ORIGINAL right-continuous filtration at s yield an L2 compensated finite sum with conditional mean zero at that same right-continuous filtration. The same-path right-continuous Levy lift preserves X.X and X.nu, so no synthetic Poisson law or altered sample space is used.
-- source:
--   Transports proved original same-window marked simple L2 martingale theorem 7726d7c7 through the true original right-continuous Levy lift e58a099d. The lifted process has identical sample paths and Levy measure.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_e_original_same_window_mark_simple_L2_martingale
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_g_original_rightcont_same_window_mark_simple_L2_martingale
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (cut : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : ∀ i, B i ⊆ Iic (-(1 / ((cut : ℝ) + 1))))
    (H : ι → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont s] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (L : ℝ) (hBound : ∀ i ω, |H i ω| ≤ L)
    (F : Finset ι) :
    let Z : ι → Ω → ℝ := fun i ω =>
      H i ω * (((((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)).toReal) -
          (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    MemLp (∑ i ∈ F, Z i) 2 P ∧
    P[(∑ i ∈ F, Z i) | 𝓕.rightCont s] =ᵐ[P] (0 : Ω → ℝ) := by sorry
