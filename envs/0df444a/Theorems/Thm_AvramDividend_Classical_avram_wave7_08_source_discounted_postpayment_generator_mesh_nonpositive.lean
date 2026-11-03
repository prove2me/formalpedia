-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_discounted_postpayment_generator_mesh_nonpositive
-- name    : AvramDividend.Classical.avram_wave7_08_source_discounted_postpayment_generator_mesh_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:33:45.370417+00:00
-- url     : https://prove2.me/theorems/220513b9-f200-41f6-ab0b-5540d68a8eb5
-- title:
--   Original source discounted postpayment finite mesh generator residual is nonpositive on the HJB interior
-- statement:
--   At every finite mesh cell of the exact original Lévy source and right-dividend-limit postpayment reserve, the HJB subsolution generator residual Γw-qw is nonpositive when the cell reserve is in (0,C). Multiplying by nonnegative cell lengths and positive original discount factors and summing preserves the sign. This is the deterministic generator-drift sign step required by the genuine controlled stopped Itô–Meyer limit; stochastic martingale and jump convergence remain separate.
-- source:
--   W7-08 source positive reserve generator mesh sign, for use beside W7-05 Gaussian and W7-07 compensated Taylor source limits in original Ω,P,X,D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_discounted_postpayment_generator_mesh_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (N : ℕ) (clock : Fin N → ℝ≥0) (δ : Fin N → ℝ) (ω : Ω)
    (hδ : ∀ i, 0 ≤ δ i)
    (hpos : ∀ i, 0 < x + X.X (clock i) ω - rightLimit D (clock i) ω)
    (hcap : ∀ i, ENNReal.ofReal (x + X.X (clock i) ω -
      rightLimit D (clock i) ω) < C) :
    (∑ i : Fin N,
      (δ i * Real.exp (-(q * (clock i : ℝ)))) *
        (X.generator w (x + X.X (clock i) ω - rightLimit D (clock i) ω) -
         q * w (x + X.X (clock i) ω - rightLimit D (clock i) ω))) ≤ 0 := by sorry
