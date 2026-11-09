-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_F0_zero_under_physical_L1_mesh
-- name    : AvramDividend.Classical.avram_ubv_gauss13_stop_original_F0_zero_under_physical_L1_mesh
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:01:58.629481+00:00
-- url     : https://prove2.me/theorems/7ee521a5-187d-4bc7-ab26-417aab978ba3
-- title:
--   Original Gaussian finite-mesh initial conditional centring survives physical L1 convergence
-- statement:
--   Necessary direct original-filtration continuity interface for existing Open a338c453-58c0-411c-aaca-5cec689ed807 via its Open strict witness d1caa4aa-f44e-406b-b756-f6521d6a544f, and for positive-clock top-cap Gaussian 249c532d-4ec0-498c-81f0-b380dd476344. If the exact same original Levy probability-space finite-grid Gaussian stochastic sums F_n are integrable and conditionally centred at the actual original initial right-continuous filtration, as furnished by public Proved 48b4b851, 3377772a, 49c99bb6, and if their original physical stopped mesh converges in L1 to an integrable Z, then Z remains conditionally centred given that same initial sigma algebra. Uses Mathlib L1 contraction of conditional expectation; does not assert the missing actual mesh convergence, no detached Gaussian model, no floor of an arbitrary stopping time.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_stop_original_F0_zero_under_physical_L1_mesh
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (F : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hFI : ∀ n, Integrable (F n) P)
    (hFzero : ∀ n,
      P[F n | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hZI : Integrable Z P)
    (hLim : Tendsto
      (fun n => eLpNorm (fun ω => F n ω - Z ω) 1 P)
      atTop (nhds 0)) :
    P[Z | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) := by
  sorry
