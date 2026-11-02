-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_C1_compact_deterministic_derivative_ceiling_envelope
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_stopped_C1_compact_deterministic_derivative_ceiling_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T20:12:35.180168+00:00
-- url     : https://prove2.me/theorems/633c3d3f-1903-470a-9d31-876b7cdc16fd
-- title:
--   Original BV stopped nonlinear source loss has a deterministic compact ceiling from C1 regularity
-- statement:
--   For the actual original bounded-variation spectrally negative Levy source with its intrinsic negative left-jump measure, any increasing verification function that is C1 on (0,cap) admits a deterministic finite derivative ceiling M on every compact [l,r] strictly contained in (0,cap). On one probability-one event, whenever each stopped prepayment reserve and its hypothetical downward source-residual update lies in [l,r], all bounded nonnegative-weight nonlinear residual losses are nonnegative and dominated by A*M times original residual variation up to the stopping horizon. This is an actual-source C1 stopped finite-variation chain-rule interface and does not assume complete controlled Ito-Meyer or a replacement Poisson process.
-- source:
--   Chat04-A original-source composition of Proved C1 compact derivative bound c57310fb-0385-4462-8abe-2b223bb5c380 and newly Proved intrinsic BV stopped cell-local nonlinear residual envelope 24173b36-cac5-406e-a08a-bd43c367bfa2. The deterministic C1 ceiling is chosen before source sample paths; stochastic integration and right dividend payments remain with Chat03/Chat04.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_deriv_bounded_on_compact_of_contDiff_one
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_intrinsic_BV_stopped_compact_C1_nonlinear_downward_residual_envelope

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Actual BV source stopped C1 residual loss with deterministic derivative bound on compact source cells. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_intrinsic_BV_stopped_C1_compact_deterministic_derivative_ceiling_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : Monotone w)
    (cap l r : ℝ) (hlr : l < r)
    (hsub : Icc l r ⊆ Ioo 0 cap)
    (hC1 : ContDiffOn ℝ 1 w (Ioo 0 cap)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      ∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hcell : ∀ i < n,
          riskProcess X x D (u i) ω ∈ Icc l r ∧
          riskProcess X x D (u i) ω -
            (R (u (i + 1)) - R (u i)) ∈ Icc l r)
        (a : ℕ → ℝ) (A : ℝ) (hA : 0 ≤ A)
        (ha : ∀ i, 0 ≤ a i ∧ a i ≤ A),
        0 ≤ (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ∧
        (Finset.range n).sum (fun i =>
          a i * (w (riskProcess X x D (u i) ω) -
            w (riskProcess X x D (u i) ω -
              (R (u (i + 1)) - R (u i))))) ≤
          (A * M) * (R (τ ω) - R (u 0)) := by sorry
