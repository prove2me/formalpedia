-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b20_nostanding_finiteactivity_actual_jump_laplace
-- name    : AvramDividend.Classical.avram_b20_nostanding_finiteactivity_actual_jump_laplace
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:44:52.889673+00:00
-- url     : https://prove2.me/theorems/6d107011-bfef-498e-b952-55cbced2750a
-- title:
--   Non-Standing original finite-activity negative-jump Laplace law on every integer clock
-- statement:
--   For the original spectrally negative Lévy process, bounded variation and finite negative jump intensity alone give the Laplace transform of the actual accumulated negative jump magnitudes on every integer horizon. No Standing condition, finite first moment or change of sample path is imposed.
-- source:
--   Source-faithful missing probabilistic premise for 69dc5e14-c06b-469b-9733-ef28d56baaa4. With θ=1, Proved 45236e85 converts the jump Laplace law to the exact all-time original BV drift-minus-actual-jump source. Proved f0ec726b changes the ENNReal positive jump magnitude sum to the signed real tsum. Genuine stochastic Poisson/exponential law is the remaining challenge.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_b20_nostanding_finiteactivity_actual_jump_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ∀ n : ℕ,
      (∫ ω : Ω, Real.exp (-
        ((∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ (n : ℝ≥0) then
            ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal)) ∂P) =
        Real.exp (-((n : ℝ) *
          (∫ y in Iio (0 : ℝ), (1 - Real.exp y) ∂X.ν))) := by sorry
