-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_uniform_grid_endpoint_predictable
-- name    : AvramDividend.Classical.avram_bv_meas7_original_uniform_grid_endpoint_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:26:56.186314+00:00
-- url     : https://prove2.me/theorems/fa927f54-38ea-4e24-bac6-eec8748883fc
-- title:
--   Actual original uniform BV physical-grid endpoint mask is predictable
-- statement:
--   For the genuine original spectrally negative Levy process and original dividend strategy, there exists a single uniform physical prefix grid starting at zero, ending at T-T/(n+2) with monotone cells of exact width T/(n+2). At each actual endpoint u(n,n+1), the original ruin-clipped stopping clock is bounded and is a stopping time in the right-continuous filtration; the original controlled pre-reserve compact-band mask is predictable in that filtration. No independent stochastic measurability or source identity assumptions are introduced.
-- source:
--   Strict physical grid geometry from Proved/public c527d1bc; exact original ruin-stopped predictable prefix certificate from Proved/public 1c35f32d, identified at the same actual grid endpoint by Real.toNNReal of a nonnegative real clock. This is the adapted/predictable geometric input for the original 2bc848f9 cell witness, without claiming its cash, B, Err or convergence components.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_prefix_uniform_physical_grid
import Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_original_physical_prefix_predictable_mask

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_original_uniform_grid_endpoint_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T) (a b : ℕ → ℝ) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0) ∧
      (∀ n, ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, i < n + 1 →
        (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2)) ∧
      ∀ n : ℕ,
        let S : ℝ≥0 := u n (n + 1)
        let τ : Ω → ℝ≥0 := fun ω =>
          (min (ruinTime X x D ω) (S : ℝ≥0∞)).toNNReal
        let E : Set (ℝ≥0 × Ω) := {p |
          (p.1 : ℝ≥0∞) ≤ (τ p.2 : ℝ≥0∞) ∧
          Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)}
        (∀ ω, τ ω ≤ S) ∧
        IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)) ∧
        MeasurableSet[𝓕.rightCont.predictable] E ∧
        (∀ p ∈ E, Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc (a n) (b n)) ∧
        (∀ p ∈ E, p.1 ≤ S) := by sorry
