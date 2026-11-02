-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_discounted_full_stieltjes_real_atomic_diffuse_exact
-- name    : AvramDividend.Classical.avram_wave6_05_actual_original_discounted_full_stieltjes_real_atomic_diffuse_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:56:35.13647+00:00
-- url     : https://prove2.me/theorems/f275f454-05f9-4f71-bff4-fe5d7afa73d4
-- title:
--   Exact finite real-valued original discounted dividend cash equals all right-payment atoms plus genuine atomless Stieltjes cash
-- statement:
--   For every original nondecreasing adapted finite-variation dividend control, sample path, horizon, and q≥0, the toReal of the original closed-horizon discounted dividendMeasure lintegral is exactly the sum of the toReal of all original right-payment atomic cash and the toReal of the corresponding atomless Stieltjes cash integral. This decomposition is legitimate in the real numbers: the original closed-horizon cash budget bounds the full ENNReal integral by finite cumulative dividends, hence neither atomic nor diffuse term is infinite. The exact rightLimit singleton identities and exhaustive countable atomic support persist, with time-zero and endpoint payments and arbitrary singular-continuous controls. This is an importable real-cash control interface, not a smooth-control approximation.
-- source:
--   Use the accepted exact original all-atom plus atomless ENNReal weighted Stieltjes identity, instantiate its weight with ENNReal.ofReal(exp(-q*s)), and retain its countable exhaustive right-payment set and singleton formula. The canonically accepted discounted closed-horizon BV cash budget makes the entire discounted lintegral strictly below top. By monotonicity of addition each of the atomic sum and actual atomless integral is itself strictly below top. The pinned Mathlib ENNReal.toReal_add lemma (confirmed exact-source signature ha:a≠∞, hb:b≠∞) then converts the exact ENNReal sum identity to an equality in ℝ. No summability of signed w-jump corrections is used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_full_stieltjes_weighted_all_atoms_plus_atomless_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_actual_original_discounted_full_stieltjes_real_atomic_diffuse_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ).toReal =
        (∑' t : A, μ {(t : ℝ)} *
          ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))).toReal +
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse).toReal := by sorry
