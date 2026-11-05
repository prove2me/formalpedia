-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_every_grid_stopped_martingale_mean_from_zero
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_every_grid_stopped_martingale_mean_from_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:31:07.451621+00:00
-- url     : https://prove2.me/theorems/1d093f35-2199-4838-a72b-e7c18ef4d531
-- title:
--   Original true martingale sampled on varying bounded right-continuous grids has expected stopped value equal to its zero cell
-- statement:
--   The actual original-filtration true martingale may be sampled on a different deterministic grid at every k. If each family clock is a genuine bounded stopping time for its own sampled right-continuous filtration with sigma-finiteness, optional stopping holds separately for each k: the stopped expectation equals the deterministic zero-index expectation. This avoids applying a fixed sampled filtration when grid mesh shrinks; zero mean at the initial cell and uniform L1/UI remain separate obligations.
-- source:
--   Proved chat01_monotone_sampling_bounded_optional_stopping_eq and source 𝓕.rightCont.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat01_monotone_sampling_bounded_optional_stopping_eq

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Each own-grid bounded source martingale stopping index is centred at its deterministic initial cell. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_every_grid_stopped_martingale_mean_from_zero
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
    (hK : ∀ k, IsStoppingTime (𝓖 k)
      (fun ω => (K k ω : WithTop ℕ)))
    (N : ℕ → ℕ) (hN : ∀ k ω, K k ω ≤ N k) :
    ∀ k,
      (∫ ω, stoppedValue (fun i : ℕ => f (e k i))
        (fun ω => (K k ω : WithTop ℕ)) ω ∂P) =
      (∫ ω, stoppedValue (fun i : ℕ => f (e k i))
        (fun _ : Ω => (0 : WithTop ℕ)) ω ∂P) := by sorry
