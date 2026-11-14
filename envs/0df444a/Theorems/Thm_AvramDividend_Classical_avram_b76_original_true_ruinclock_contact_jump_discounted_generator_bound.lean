-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b76_original_true_ruinclock_contact_jump_discounted_generator_bound
-- name    : AvramDividend.Classical.avram_b76_original_true_ruinclock_contact_jump_discounted_generator_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:55:56.580065+00:00
-- url     : https://prove2.me/theorems/aed67fb8-04f9-404e-a112-d87564c5a3b3
-- title:
--   Actual original ruin-clipped mixed contact negative source jump and paid cash generator bound
-- statement:
--   At a positive original physical spatial localising clock kappa, any negative source jump with prepayment reserve inside the compact C2 band obeys the exact discounted physical jump-plus-dividend cash generator inequality. B69 proves kappa is at most the already ruin-clipped rho and at most the true original ruin clock; its horizon n bound gives time<=n. The Proved wave5_03 inclusive ruin-mark generator theorem then applies directly. It includes the jump causing ruin and excludes a positive-time right dividend atom at ruin; post-ruin continuation is never needed. The statement retains the exact original X, D and w, and all original Ito smoothness and gradient hypotheses. This provides the *terminal contact-cell* complement to strict-interior energy B73. It does not itself establish the stochastic martingale or final Ito ledger.
-- source:
--   Avram Palmowski Pistorius 2007 Proposition 4(i), equation 5.11-5.13, original Prove2Me wave5_03 and B69.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_b69_original_true_spatial_clock_ruin_clipped
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_inclusive_ruin_jump_chronological_discounted_generator_bound
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b76_original_true_ruinclock_contact_jump_discounted_generator_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (hρclip : ∀ ω, ρ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (κ : ℕ → Ω → ℝ≥0)
    (hκexact : ∀ k ω, κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (k : ℕ) (ω : Ω) (ht : 0 < κ k ω)
    (q : ℝ) (hq : 0 ≤ q)
    (u v ζ : ℝ) :
    let t : ℝ≥0 := κ k ω
    let Y : ℝ := Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let J : ℝ :=
      X.X t ω - Function.leftLim (fun s : ℝ≥0 => X.X s ω) t
    let W : ℝ :=
      if (t : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X t ω - rightLimit D t ω
      else riskProcess X x D t ω
    let cash : ℝ :=
      if (t : ℝ≥0∞) < ruinTime X x D ω then
        rightLimit D t ω - D t ω else 0
    ∀ (hJneg : J < 0) (hBand : Y ∈ Icc (u + ζ) v),
    Real.exp (-(q * (t : ℝ))) *
      ((w W -
          w (Function.leftLim (fun s : ℝ≥0 =>
            riskProcess X x D s ω) t)) + cash) ≤
    Real.exp (-(q * (t : ℝ))) *
      ((if -1 < J then J * deriv w Y else 0) +
        SpectrallyNegativeLevy.generatorIntegrand w Y J) := by sorry
