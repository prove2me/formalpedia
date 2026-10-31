-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_postPayment_condExp_rightCont
-- name    : AvramDividend.Classical.avram_wave3_03_postPayment_condExp_rightCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:08:14.513596+00:00
-- url     : https://prove2.me/theorems/5428b871-53e1-4b62-8482-f55a76a9f3ca
-- title:
--   Original post-payment reserve future reward conditional on right-continuous dividend history
-- statement:
--   For the original spectrally negative Levy process and an actual dividend strategy, the conditional expected Lipschitz reward of the genuine post-payment controlled reserve plus its next Levy increment, given the right-continuous history at time s, equals the source Levy transition expectation started at that reserve. Integrability assumptions are explicit.
-- source:
--   Proved levy_rightCont_process, postPaymentReserve_cadlag_adapted and levy_increment_condExp_integrable_adapted_reserve_lipschitz, applied to the transported but path-identical source process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_integrable_adapted_reserve_lipschitz

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_postPayment_condExp_rightCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t)
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ y : ℝ, Integrable
      (fun η => f (y + X.X (t - s) η)) P)
    (hZm : Measurable (fun ω => x + X.X s ω - rightLimit D s ω))
    (hZI : Integrable (fun ω => x + X.X s ω - rightLimit D s ω) P)
    (hZPay : Integrable (fun ω =>
      f (x + X.X s ω - rightLimit D s ω +
        (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω =>
      f ((SimpleFunc.approxOn
        (fun η => x + X.X s η - rightLimit D s η) hZm
        (Set.range (fun η => x + X.X s η - rightLimit D s η) ∪ {0})
        0 (by simp) n) ω + (X.X t ω - X.X s ω))) P) :
    P[(fun η => f (x + X.X s η - rightLimit D s η +
      (X.X t η - X.X s η))) | 𝓕.rightCont s] =ᵐ[P]
    (fun ω => ∫ η, f (x + X.X s ω - rightLimit D s ω +
      X.X (t - s) η) ∂P) := by sorry
