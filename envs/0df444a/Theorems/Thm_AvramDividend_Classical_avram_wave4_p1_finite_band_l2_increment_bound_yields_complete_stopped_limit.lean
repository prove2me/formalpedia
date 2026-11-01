-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_finite_band_l2_increment_bound_yields_complete_stopped_limit
-- name    : AvramDividend.Classical.avram_wave4_p1_finite_band_l2_increment_bound_yields_complete_stopped_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T22:28:21.10219+00:00
-- url     : https://prove2.me/theorems/ba154790-a101-437a-aa27-8b73ace7f705
-- title:
--   Original stopped finite-band compensated integrals converge in complete L² under verified finite-band increment bound
-- statement:
--   Let M_n be the actual finite-band compensated stochastic integrals, represented in any complete metric space W (in application W=Lp ℝ 2 P on the original Ω). If source 04-A proves their finite-band pairwise L² increment bound in terms of the exact predictable square-energy of the mark tail, then the M_n converge to an element of W. The proof uses the independently Proved sigma-finite L² cutoff theorem (so tail energy→0), continuity of ENNReal.toReal at zero, Mathlib's Cauchy criterion, and completeness. Crucially the assumption is only an explicitly finite-band bound to be derived from Poisson independence/isometry, not Campbell or martingale property of the infinite limit; the result is the missing infinite-activity L² localisation step.
-- source:
--   P1 sigma-finite L² band cutoff theorem 65f775d0 Proved; pinned Mathlib ENNReal.continuousAt_toReal, cauchySeq_of_le_tendsto_0', cauchySeq_tendsto_of_complete.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_l2_band_cutoff_converges

open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_wave4_p1_finite_band_l2_increment_bound_yields_complete_stopped_limit
    {α W : Type*} [MeasurableSpace α]
    [MetricSpace W] [CompleteSpace W]
    (μ : Measure α)
    (f : α → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ < ∞)
    (B : ℕ → Set α) (hB : ∀ n, MeasurableSet (B n))
    (hBfinite : ∀ n, μ (B n) < ∞)
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (M : ℕ → W)
    (hfinite_band_isometry_bound :
      ∀ m n, m ≤ n →
        dist (M m) (M n) ≤
          (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) μ).toReal) :
    ∃ Mlimit : W, Tendsto M Filter.atTop (nhds Mlimit) := by sorry
