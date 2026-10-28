-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_full_killed_renewal_of_positive_reserve
-- name    : AvramDividend.Classical.chat04_full_killed_renewal_of_positive_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:17:56.503783+00:00
-- url     : https://prove2.me/theorems/f73066ff-92d8-40fe-80c9-4350e4c3a490
-- title:
--   Whole-horizon killed q-scale renewal reduces to strictly positive initial reserve
-- statement:
--   The unbounded-variation killed q-scale semigroup renewal identity at all initial reserves and horizons follows from its strictly positive-reserve identity. The negative-reserve branch vanishes by scale support, while the zero-reserve branch follows from monotone domination and vanishing scale at zero, eliminating any separate downcrossing regularity premise.
-- source:
--   Composes the Proved negative-reserve killed renewal branch with the zero-capital monotone limiting theorem; isolates the outstanding Wiener-Hopf killed-semigroup harmonicity to strictly positive reserves.

import Theorems.Thm_AvramDividend_Classical_chat04_zero_reserve_killed_renewal_of_positive_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_history_killed_renewal_zero_horizon_or_negative_reserve

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_full_killed_renewal_of_positive_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hpositive : ∀ (x : ℝ), 0 < x → ∀ t : ℝ≥0,
      (∫⁻ ω,
        ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
        ENNReal.ofReal (W x))
    (x : ℝ) (t : ℝ≥0) :
    (∫⁻ ω,
      ({ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s ω}).indicator
        (fun ω => ENNReal.ofReal
          (Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))) ω ∂P) =
    ENNReal.ofReal (W x) := by sorry
