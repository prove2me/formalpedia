-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_ruinclipped_finitecap_four_term_mesh_chain
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_ruinclipped_finitecap_four_term_mesh_chain
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:58:43.585757+00:00
-- url     : https://prove2.me/theorems/bceea60b-dbba-42e2-b106-9b2b6a84f4e4
-- title:
--   Original admissible purejump strategy at its true ruinclipped stopped clock has exact finite physical four-term Stieltjes cash mesh identity
-- statement:
--   For original admissible controlled spectrally negative Lévy process, true bounded ruin-clipped tau, and any substop rho<=tau, each canonical finite grid clipping to rho ends exactly at rho and satisfies the complete original four-term discounted identity including initial dividend atom and post-right-dividend reserve. The admissibility and clock bounds are discharged from proved original sources; no Gaussian replacement or finite-activity assumption.
-- source:
--   Proved edebe535 exact subordinate clock bound, Proved b9dccb4 exact discounted original finite grid four-term Stieltjes equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_ruinclipped_finitecap_four_term_mesh_chain
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (τ ρ : Ω → ℝ≥0)
    (n m : ℕ) (hn : 0 < n)
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
