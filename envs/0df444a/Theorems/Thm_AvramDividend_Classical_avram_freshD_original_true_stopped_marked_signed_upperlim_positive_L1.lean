-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_freshD_original_true_stopped_marked_signed_upperlim_positive_L1
-- name    : AvramDividend.Classical.avram_freshD_original_true_stopped_marked_signed_upperlim_positive_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:28:53.836767+00:00
-- url     : https://prove2.me/theorems/bc53cc98-cd90-4753-854c-262afda7e73e
-- title:
--   Original true stopped finite-activity signed negative-mark mesh upper-limit errors have vanishing expected positive part
-- statement:
--   For the exact negative Lévy jump marked cells of a deterministic physical mesh clipped by an actual right-continuous stopping time σ≤n, if signed cell errors have a fixed uniformly bounded absolute magnitude, the positive part of their whole physical marked-cell sum is measurable and tends almost surely to zero from above, then its expected positive part tends to zero. Domination uses the actual finite-horizon original negative-mark count, which is integrable under finite mark activity. This one-sided signed upper-limit theorem is explicitly suitable when the value function has an upward discontinuity at ruin reserve zero, so full absolute mesh-error convergence may be false; it does not assume the signed errors themselves converge in absolute value.
-- source:
--   Genuine finite-activity signed negative-mark rootward source for 242ca5f1, combining Proved whole original negative count L1 e19df3d9, Proved true stopped marked-cell count domination 7ad3bc4d, and dominated-convergence with a one-sided signed positive-part hypothesis. Used with Proved 5864c4ee one-sided exact zero-landing fixed-mark upper limit after a real proof of hUpper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_fullnegative_physical_finite_horizon_count_L1
import Theorems.Thm_AvramDividend_Classical_avram_b244_original_true_stopping_clock_ruinclipped_marked_cell_L1_dom_20261114
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_freshD_original_true_stopped_marked_signed_upperlim_positive_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (marked : ℕ → Ω → Finset ℕ)
    (hmarked : ∀ m ω, marked m ω =
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let grid : ℕ → ℝ≥0 := fun i =>
        min ((i : ℝ≥0) * Δ) (σ ω)
      (by
        classical
        exact (Finset.range (m + 1)).filter (fun i =>
          ∃ u : ℝ≥0, grid i < u ∧ u ≤ grid (i + 1) ∧
            X.X u ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) u ≠ 0)))
    (W : ℕ → Ω → ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hW : ∀ m i ω, |W m ω i| ≤ L)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => max (∑ i ∈ marked m ω, W m ω i) 0) P)
    (hUpper : ∀ᵐ ω ∂P, Tendsto
      (fun m => max (∑ i ∈ marked m ω, W m ω i) 0)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun m => ∫ ω, max (∑ i ∈ marked m ω, W m ω i) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
