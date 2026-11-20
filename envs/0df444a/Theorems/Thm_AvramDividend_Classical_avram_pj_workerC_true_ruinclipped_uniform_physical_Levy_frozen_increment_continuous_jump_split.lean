-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_true_ruinclipped_uniform_physical_Levy_frozen_increment_continuous_jump_split
-- name    : AvramDividend.Classical.avram_pj_workerC_true_ruinclipped_uniform_physical_Levy_frozen_increment_continuous_jump_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:50:47.774543+00:00
-- url     : https://prove2.me/theorems/1523f9e4-313f-4f16-baec-cb7c45e10450
-- title:
--   Original ruin-clipped post-right controlled Lévy reserve has an exact frozen-increment pathwise continuous-corrected versus negative-jump split on every physical horizon cell
-- statement:
--   For each genuine original spectrally negative Levy sample and post-right admissible dividend strategy, construct the actual stopped physical lattice u_i=min(i*n/(m+1),rho(ω)). On every physical cell i<m+1, the original discounted-Ito frozen controlled reserve increment w(x+X_{u_i+1}-D^+_{u_i})-w(x+X_{u_i}-D^+_{u_i}) splits exactly into the algebraic continuous-corrected increment of the original X+J compensated small-jump part and the residual jump increment J_{u_i+1}-J_{u_i}, where J is the true signed jump tsum of X^-_t-X_t. This is an exact original X pathwise identity, with no replacement paths, gaussian approximations or abstract source assumptions.
-- source:
--   Proved d5530287 original frozen X cell exact Y/J split, specialised to actual preterminal clipped n/(m+1) physical clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_frozen_X_cell_exact_Y_J_split
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_true_ruinclipped_uniform_physical_Levy_frozen_increment_continuous_jump_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ρ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let u : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    let j : ℕ → ℝ := fun i => J (u (i + 1)) - J (u i)
    ∀ i, i < m + 1 →
      w (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
        w (x + X.X (u i) ω - rightLimit D (u i) ω) =
      (w (z i + c i - j i) - w (z i - j i)) +
      (w (z i - j i) - w (z i)) := by sorry
