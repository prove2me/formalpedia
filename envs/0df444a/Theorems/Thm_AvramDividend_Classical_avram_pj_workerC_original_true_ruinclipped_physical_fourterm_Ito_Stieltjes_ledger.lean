-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_ruinclipped_physical_fourterm_Ito_Stieltjes_ledger
-- name    : AvramDividend.Classical.avram_pj_workerC_original_true_ruinclipped_physical_fourterm_Ito_Stieltjes_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:27:53.171398+00:00
-- url     : https://prove2.me/theorems/0b8419e0-81e7-470a-9c2d-8cc765f6bcdf
-- title:
--   Actual ruin-clipped original postright dividend reserve satisfies exact stopped deterministic-horizon fourterm discounted physical Ito-Stieltjes mesh identity at every refinement
-- statement:
--   For a genuine original spectrally negative Lévy risk process and original admissible dividend strategy D, the deterministic-horizon clipped physical mesh min(i*n/(m+1), rho) at any true subordinate ruin-clipped stopping time rho finishes exactly at rho and telescopes the discounted original post-right-payment reserve into the sum of discount drift, prepayment risk increment, physical right dividend payment and terminal contact terms. No abstract hRhoBound is assumed: derive the precise horizon bound from the actual ruin-clipped natural stopping time. This identity is the exact pathwise chronological decomposition that must be combined with original compensated negative-jump estimates and uniform L1 to close Worker C true physical K/E source.
-- source:
--   Proved b9dccb4b original fourterm Stieltjes mesh, Proved edebe535 subordinate clock actual ruin and horizon bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_true_ruinclipped_physical_fourterm_Ito_Stieltjes_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (C : ℝ≥0∞) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (n m : ℕ) (hn : 0 < n)
    (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    u (m + 1) = ρ ω ∧
    E (u (m + 1)) * w (Y (u (m + 1))) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
          E (u (i + 1)) * (w (Z i) - w (Y (u i))) +
          E (u (i + 1)) *
            (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
          E (u (i + 1)) *
            (w (Y (u (i + 1))) -
              w (riskProcess X x D (u (i + 1)) ω))) := by sorry
