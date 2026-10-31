-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_postPayment_source_oneStep_budget
-- name    : AvramDividend.Classical.avram_wave3_03_postPayment_source_oneStep_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:13:16.920342+00:00
-- url     : https://prove2.me/theorems/d567bda2-6538-49c6-85a5-ad305fa541e8
-- title:
--   Genuine Lévy source one-step budget with actual post-payment dividend atom in right-continuous history
-- statement:
--   At deterministic times s≤t, for an actual dividend strategy, the current right dividend atom plus the discounted right-continuous-history conditional value of the next source Levy increment is bounded by the pre-payment candidate value, assuming the exact source semigroup and secant inequalities with explicit Lipschitz and integrability conditions.
-- source:
--   Previously Proved original Levy right-continuous transport, postPaymentReserve_cadlag_adapted, and levy_adapted_reserve_one_step_dividend_budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_levy_rightCont_process
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_levy_adapted_reserve_one_step_dividend_budget

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_postPayment_source_oneStep_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (s t : ℝ≥0) (hst : s ≤ t)
    (w : ℝ → ℝ) (hw : Measurable w) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (hInt : ∀ y : ℝ, Integrable (fun η => w (y + X.X (t - s) η)) P)
    (q : ℝ)
    (hZm : Measurable (fun ω =>
      (x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω)))
    (hZI : Integrable (fun ω =>
      (x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω)) P)
    (hZPay : Integrable (fun ω => w
      ((x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω) +
        (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω => w
      ((SimpleFunc.approxOn
        (fun η => (x + X.X s η - D s η) -
          (rightLimit D s η - D s η)) hZm
        (Set.range (fun η => (x + X.X s η - D s η) -
          (rightLimit D s η - D s η)) ∪ {0})
        0 (by simp) n) ω + (X.X t ω - X.X s ω))) P)
    (hsec : ∀ᵐ ω ∂P, rightLimit D s ω - D s ω ≤
      w (x + X.X s ω - D s ω) -
      w ((x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω)))
    (hsemi : ∀ᵐ ω ∂P,
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (∫ η, w ((x + X.X s ω - D s ω) -
          (rightLimit D s ω - D s ω) + X.X (t - s) η) ∂P) ≤
      w ((x + X.X s ω - D s ω) - (rightLimit D s ω - D s ω))) :
    ∀ᵐ ω ∂P, (rightLimit D s ω - D s ω) +
      Real.exp (-((t - s : ℝ≥0) : ℝ) * q) *
        (P[(fun η => w
          ((x + X.X s η - D s η) - (rightLimit D s η - D s η) +
            (X.X t η - X.X s η))) | 𝓕.rightCont s]) ω ≤
      w (x + X.X s ω - D s ω) := by sorry
