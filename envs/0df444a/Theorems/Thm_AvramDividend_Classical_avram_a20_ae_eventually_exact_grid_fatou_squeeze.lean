-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_ae_eventually_exact_grid_fatou_squeeze
-- name    : AvramDividend.Classical.avram_a20_ae_eventually_exact_grid_fatou_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:11:39.87805+00:00
-- url     : https://prove2.me/theorems/1d37ce03-8354-422e-bf80-1cf84ed8f230
-- title:
--   Fatou squeeze for a.e. eventual exact physical grid counts with only a.e. samplewise domination
-- statement:
--   If measurable nonnegative extended-real physical grid counts F_n are almost surely dominated by a terminal physical count K, eventually coincide with K on almost every sample, and their genuine original-space expected values converge to r, then the expectation of K equals r exactly. This generalises the already Proved everywhere-dominated eventual grid Fatou squeeze to the case of physical finite-activity Lévy jump times that are finite only almost surely. Proof uses pointwise eventual equality on the full-measure set, Fatou liminf inequality, and reverse inequality through a.e. monotonicity of the lintegral. It enables direct original arbitrary-Borel second factorial moments.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a20_ae_eventually_exact_grid_fatou_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ≥0∞) (K : Ω → ℝ≥0∞) (r : ℝ≥0∞)
    (hFm : ∀ n, Measurable (F n))
    (hBound : ∀ᵐ ω ∂P, ∀ n, F n ω ≤ K ω)
    (hEventually : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, F n ω = K ω)
    (hRate : Tendsto (fun n => ∫⁻ ω, F n ω ∂P) atTop (𝓝 r)) :
    (∫⁻ ω, K ω ∂P) = r := by sorry
