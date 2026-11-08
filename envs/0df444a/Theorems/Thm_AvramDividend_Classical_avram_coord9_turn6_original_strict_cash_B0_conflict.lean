-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_coord9_turn6_original_strict_cash_B0_conflict
-- name    : AvramDividend.Classical.avram_coord9_turn6_original_strict_cash_B0_conflict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T22:29:57.948208+00:00
-- url     : https://prove2.me/theorems/a25453a7-5687-4a31-b14a-a4d70d73cc33
-- title:
--   Standing BV singular first row excludes an integrable strict-cash certificate
-- statement:
--   The Proved source-exact Standing BV initial-row obstruction and the Proved strict nonnegative cash-budget integrability theorem cannot both hold when the full physical uniform-grid source and an integrable centred martingale and positive error exist. This records a conditional incompatibility with the purported no-B-L1 parent route, without claiming a constructed countermodel.
-- source:
--   COORD9 cash-route bridge from Proved 4175c1b5 and c52a3794.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Theorems.Thm_AvramDividend_Classical_avram_coord9_turn6_original_Standing_BV_uniform_B0_nonintegrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn8b_original_B_L1_from_true_strict_cash_budget
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original uniform-grid nonintegrable first row rules out any strictly
    stopped nonnegative cash certificate with integrable martingale and error. -/

theorem AvramDividend.Classical.avram_coord9_turn6_original_strict_cash_B0_conflict
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q T x : ℝ) (hT : 0 < T)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hruin : ∀ ω, (0 : ℝ≥0∞) < ruinTime X x D ω)
    (hpositive : ∀ ω, 0 < x - rightLimit D 0 ω)
    (hcap : ∀ ω, ENNReal.ofReal (x - rightLimit D 0 ω) < C)
    (hmeas : AEStronglyMeasurable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (hnonint : ¬ Integrable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (u : ℕ → ℕ → ℝ≥0) (B : ℕ → Ω → ℝ)
    (hgrid0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hB : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
        (∑ i ∈ Finset.range (n + 1),
          if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
              0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) *
              (X.generator w (Z i) - q * w (Z i)) *
              ((u n (i + 1) : ℝ) - (u n i : ℝ))
          else 0) +
        (let J : ℝ≥0 → ℝ := fun t =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
              Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
            else 0
         let R : ℝ≥0 → ℝ := fun t =>
           ((t : ℝ) * X.drift - X.X t ω) - J t
         ∑ i ∈ Finset.range (n + 1),
           (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
             Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
            else 0) * (R (u n i) - R (u n (i + 1)))))
    (S : ℝ≥0) (hS : S = ⟨T, le_of_lt hT⟩) (δ : ℕ → ℝ)
    (Pay M Err : ℕ → Ω → ℝ)
    (hPayExact : ∀ n ω, Pay n ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
         Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0))
    (hM : ∀ n, Integrable (M n) P)
    (hErr : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hBMeas : ∀ n, AEStronglyMeasurable (B n) P)
    (hBNeg : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPayPos : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Pay n ω)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      Pay n ω ≤ w x + (M n ω + B n ω) + max (Err n ω) 0) :
    False := by sorry
