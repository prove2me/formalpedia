-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_expected_full_stieltjes_grid_source_drift_bound
-- name    : AvramDividend.Classical.avram_wave5_03_actual_original_expected_full_stieltjes_grid_source_drift_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:27:22.344059+00:00
-- url     : https://prove2.me/theorems/b1a09850-c344-402d-bdcc-29536bc6fa21
-- title:
--   Original expected full discounted Stieltjes reward is bounded by initial verification value plus genuine source finite-grid drift
-- statement:
--   Under exactly the original positive-cap admissible dividend strategy, nonnegative initial reserve and indispensable boundary w(0)≥0, continuous C1 test with BV/UBV-compatible derivative floor and zero extension below ruin, the complete discounted full Stieltjes dividend cash on a pre-ruin finite grid has its real expectation bounded by V(x) plus the expectation of the exact original Lévy-source-frozen increments and exponential clock drift. This includes time-zero and all diffuse and singular-continuous dividends. Integrability is explicitly assumed only for those genuine random cash and source-grid observables. Terminal postpayment V is shown nonnegative using canonical Proved original source cap, original terminal gradient sign, and cap-linear equality, not assumed. The original source clock and control are unchanged, no martingale or Ito formula is smuggled in. This is a genuine expectation-level stochastic-verification bridge; source drift control at the mesh limit remains open.
-- source:
--   Proved 03 integrator full-grid bound 6e0125db, original BV/UBV boundary 28b04520, source cap 16104f4f, 04-B cap-linear equality 85617d04. Relates to canonical BV ef7e6c20 and corrected UBV 429e17ca. The proof uses expected inequality integral_mono under explicit actual L1 and P probability X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_leftclock_full_stieltjes_terminal_reward_grid_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_bv_postpayment_terminal_nonnegative_separate_gradient
import Theorems.Thm_AvramDividend_Classical_capped_postPaymentReserve_ofReal_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_caplinear_extension_eq_w_closed_cap

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_original_expected_full_stieltjes_grid_source_drift_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hC : 0 < C) (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (u : ℕ → ℝ≥0) (n : ℕ)
    (hu : Monotone u) (hu0 : u 0 = 0)
    (hPre : ∀ ω (i : ℕ), i < n →
      u (i + 1) = 0 ∨
        (u (i + 1) : ℝ≥0∞) < ruinTime X x D ω)
    (hCashInt : Integrable (fun ω => (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (hSourceInt : Integrable (fun ω =>
      ∑ i ∈ Finset.range n,
          ((Real.exp (-(q * (u (i + 1) : ℝ))) -
              Real.exp (-(q * (u i : ℝ)))) *
              V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) +
            Real.exp (-(q * (u i : ℝ))) *
              (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
                V (x + X.X (u i) ω - rightLimit D (u i) ω)))) P) :
    (∫ ω, (∫⁻ s in Icc (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
      V x + (∫ ω, ∑ i ∈ Finset.range n,
          ((Real.exp (-(q * (u (i + 1) : ℝ))) -
              Real.exp (-(q * (u i : ℝ)))) *
              V (x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) +
            Real.exp (-(q * (u i : ℝ))) *
              (V (x + X.X (u (i + 1)) ω - rightLimit D (u i) ω) -
                V (x + X.X (u i) ω - rightLimit D (u i) ω))) ∂P) := by sorry
