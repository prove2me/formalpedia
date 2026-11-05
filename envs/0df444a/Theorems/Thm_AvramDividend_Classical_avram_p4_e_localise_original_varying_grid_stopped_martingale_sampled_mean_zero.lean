-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_varying_grid_stopped_martingale_sampled_mean_zero
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_varying_grid_stopped_martingale_sampled_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:49:46.015368+00:00
-- url     : https://prove2.me/theorems/c433db10-e426-40f9-812a-95733670af10
-- title:
--   Original true martingale sampled on each distinct bounded grid has zero expected value
-- statement:
--   The accepted varying-filtration bounded optional-stopping theorem and the definitionally exact stoppedValue finite-clock evaluator imply centred sampled original process values at each grid. This is the per-mesh martingale hypothesis needed by the original-clock L1 or L2 passage; a centred deterministic initial cell is retained explicitly.
-- source:
--   Proved P4-E bounded optional stopping on each source sampled right-continuous filtration and Proved source stoppedValue evaluation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_every_grid_stopped_martingale_mean_from_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_finite_grid_stoppedValue_is_sampled_value

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true original process sampled at each own-grid bounded stopping time is centred when its initial cell is centred. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_varying_grid_stopped_martingale_sampled_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f : ℝ≥0 → Ω → ℝ)
    (hf : Martingale f 𝓕.rightCont P)
    (e : ℕ → ℕ → ℝ≥0) (he : ∀ k, Monotone (e k))
    (𝓖 : ℕ → Filtration ℕ mΩ)
    (h𝓖 : ∀ k, 𝓖 k =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e k i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he k hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e k i) } : Filtration ℕ mΩ))
    (hSF : ∀ k, SigmaFiniteFiltration P (𝓖 k))
    (K : ℕ → Ω → ℕ)
    (hK : ∀ k, IsStoppingTime (𝓖 k) (fun ω => (K k ω : WithTop ℕ)))
    (N : ℕ → ℕ) (hN : ∀ k ω, K k ω ≤ N k)
    (hInit : ∀ k, (∫ ω, stoppedValue (fun i : ℕ => f (e k i))
      (fun _ : Ω => (0 : WithTop ℕ)) ω ∂P) = 0) :
    ∀ k, (∫ ω, f (e k (K k ω)) ω ∂P) = 0 := by sorry
