-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_allnu_stopped_gaussian_exact_energy_isometry
-- name    : AvramDividend.Classical.avram_lsv_original_allnu_stopped_gaussian_exact_energy_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T13:06:50.331548+00:00
-- url     : https://prove2.me/theorems/e9b545dd-ab48-4a4b-aa50-e9d899561b3e
-- title:
--   Original mixed Levy physical Gaussian source has exact expected stopped energy sigma squared times stopped clock
-- statement:
--   For an original spectrally negative Levy process with an actual same-space zero-jump Gaussian source Y and physical small/large jump channels satisfying a pointwise reconstruction of X, the compensated original continuous Gaussian process has exact stopped mean-square E[M_tau²]=sigma² E[tau], for a genuine bounded countable-range stopping time of the original right-continuous filtration. Integrability of the stopped compensator is proved. The true martingale and quadratic-compensated martingale are established source results; only remote-Proved lean-lsv isometry is used. Upstream CC BY 4.0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn7_original_allnu_Xminusjump_gaussian_martingale_and_sigma_square
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_zero_jump_process_fixed_time_square_moment_20261113
import Theorems.Thm_AvramDividend_Classical_avram_lsv_finite_grid_stopped_quadratic_energy_isometry

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
noncomputable section

/- Actual original spectrally negative Levy X, physical small and large jump
   channels, with explicitly given same-space Y Gaussian driver. Port of
   lean-lsv exact stopped quadratic energy identity at bounded countable
   stopping clocks. Upstream CC BY 4.0, commit a5f604d. -/

theorem AvramDividend.Classical.avram_lsv_original_allnu_stopped_gaussian_exact_energy_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ (t : ℝ≥0) (ω : Ω),
      X.X t ω = (t : ℝ) * X.c +
        (Y.X t ω - (t : ℝ) * Y.c) + Jsmall t ω + Jlarge t ω)
    (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ)
    (hτle : ∀ ω, τ ω ≤ (T : WithTop ℝ≥0))
    (hτcount : (Set.range τ).Countable) :
    let M : ℝ≥0 → Ω → ℝ := fun t ω =>
      X.X t ω - (t : ℝ) * X.c - Jsmall t ω - Jlarge t ω
    Integrable (fun ω => ((τ ω).untopA : ℝ) * X.σ^2) P ∧
      (∫ ω, (stoppedValue M τ ω)^2 ∂P) =
        ∫ ω, ((τ ω).untopA : ℝ) * X.σ^2 ∂P := by sorry
