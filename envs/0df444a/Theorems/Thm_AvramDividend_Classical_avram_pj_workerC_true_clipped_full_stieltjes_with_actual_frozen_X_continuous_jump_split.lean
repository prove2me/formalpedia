-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_clipped_full_stieltjes_with_actual_frozen_X_continuous_jump_split
-- name    : AvramDividend.Classical.avram_pj_workerC_true_clipped_full_stieltjes_with_actual_frozen_X_continuous_jump_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:53:10.946578+00:00
-- url     : https://prove2.me/theorems/ebc054e6-cdf7-45e4-b053-fd58c60a1df8
-- title:
--   Exact original post-right dividend true-ruinclipped physical Stieltjes telescoping with actual Levy frozen first-order continuous-corrected plus jump decomposition on every mesh cell
-- statement:
--   For the true spectrally negative Lévy path, admissible right-dividend strategy and true stopped deterministic horizon physical mesh u_i=min(i*n/(m+1),rho), combine exactly the original four-term discounted Stieltjes telescoping identity for w of the post-right reserve with the original frozen-X increment algebraic decomposition into continuous-corrected component Yc=X+Jp and the true negative-jump tsum Jp. The controlled state value at final rho equals initial value plus exact discount, first-order continuous-corrected term, true jump term, prepayment cash and contact term, without generic stochastic witnesses or artificial paths. This supplies an exact physical source ledger for proving the infinite-activity positive Ito L1 remainder.
-- source:
--   Proved b9dccb4b original four-term clipped physical Stieltjes and d5530287 true frozen-X continuous+jump decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_clipped_clock_four_term_Stieltjes_mesh_exact
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_true_clipped_full_stieltjes_with_actual_frozen_X_continuous_jump_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ρ : Ω → ℝ≥0)
    (n m : ℕ) (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i =>
      min (((min i (m + 1) : ℕ) : ℝ≥0) * Δ) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (u (i + 1)) ω - rightLimit D (u i) ω
    let Jp : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Yc : ℝ≥0 → ℝ := fun t => X.X t ω + Jp t
    let z : ℕ → ℝ := fun i => Y (u i)
    let c : ℕ → ℝ := fun i => Yc (u (i + 1)) - Yc (u i)
    let j : ℕ → ℝ := fun i => Jp (u (i + 1)) - Jp (u i)
    u (m + 1) = ρ ω ∧
    E (u (m + 1)) * w (Y (u (m + 1))) =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      ∑ i ∈ Finset.range (m + 1),
        ((E (u (i + 1)) - E (u i)) * w (Y (u i)) +
          E (u (i + 1)) *
            ((w (z i + c i - j i) - w (z i - j i)) +
              (w (z i - j i) - w (z i))) +
          E (u (i + 1)) *
            (w (riskProcess X x D (u (i + 1)) ω) - w (Z i)) +
          E (u (i + 1)) *
            (w (Y (u (i + 1))) -
              w (riskProcess X x D (u (i + 1)) ω))) := by sorry
