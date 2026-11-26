-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_bounded_stop_positive_time_ito_stieltjes_of_reserve_range
-- name    : AvramDividend.Classical.gaussian_bounded_stop_positive_time_ito_stieltjes_of_reserve_range
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T07:35:25.727272+00:00
-- url     : https://prove2.me/theorems/1ce880af-3572-4c05-a759-857e0d8bd92c
-- title:
--   Positive-time Gaussian Itô–Stieltjes formula at a bounded stop in a reserve interval
-- statement:
--   Let a Gaussian Lévy surplus be controlled by an adapted left-continuous nondecreasing process. At a bounded stopping time, take the prepayment terminal reserve for a positive clock and the postpayment reserve for a zero clock. Assume that the postpayment initial reserve, the active positive-time prepayment and postpayment reserves, and the terminal reserve stay in a compact spatial interval, and take a test function that is twice continuously differentiable on a neighborhood of that interval.
--
--   The discounted terminal test value plus the signed discounted Stieltjes variation on the open positive-time interval equals the postpayment initial test value plus an integrable centered Gaussian term and the discounted generator integral. The coefficient of the continuous dividend measure is the spatial derivative, and the coefficient of each positive-time dividend atom is the exact divided difference across the payment. The interval excludes both the initial atom and the right dividend jump at the stopping time.
--
--   The clock is arbitrary subject to boundedness and the reserve-range hypotheses. There is no HJB, ruin, or payment-strategy optimality assumption.
-- source:
--   Controlled specialization of the Itô–Stieltjes calculation in Avram, Palmowski and Pistorius (2007), Section 5.4, equation (5.11), https://arxiv.org/pdf/math/0702893#page=19.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_bounded_stop_positive_time_ito_stieltjes_of_reserve_range
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (v : ℝ → ℝ) (a b l u : ℝ) (hal : a < l) (hub : u < b)
    (hv : ContDiffOn ℝ 2 v (Ioo a b))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (T : ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hBound : ∀ ω, ρ ω ≤ T)
    (hInitial : ∀ ω, x - rightLimit D 0 ω ∈ Icc l u)
    (hActive : ∀ ω t, 0 < t → t < ρ ω →
      riskProcess X x D t ω ∈ Icc l u ∧
      (riskProcess X x D t ω - (rightLimit D t ω - D t ω)) ∈ Icc l u)
    (hTerminal : ∀ᵐ ω ∂P, 0 < ρ ω → riskProcess X x D (ρ ω) ω ∈ Icc l u) :
  let pre : ℝ≥0 → Ω → ℝ := riskProcess X x D
  let jump : ℝ≥0 → Ω → ℝ := fun t ω => rightLimit D t ω - D t ω
  let post : ℝ≥0 → Ω → ℝ := fun t ω => pre t ω - jump t ω
  let toll : Ω → ℝ → ℝ := fun ω s =>
    if jump s.toNNReal ω = 0 then deriv v (pre s.toNNReal ω)
    else (v (pre s.toNNReal ω) - v (post s.toNNReal ω)) / jump s.toNNReal ω
  let paid : Ω → ℝ → ℝ := fun ω s => Real.exp (-(q * s)) * toll ω s
  let finish : Ω → ℝ := fun ω =>
    if ρ ω = 0 then post (ρ ω) ω else pre (ρ ω) ω
  let driftTerm : Ω → ℝ → ℝ := fun ω s =>
    Real.exp (-(q * s)) * (X.generator v (pre s.toNNReal ω) - q * v (pre s.toNNReal ω))
  ∃ M : Ω → ℝ, Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
    ∀ᵐ ω ∂P, IntegrableOn (paid ω) (Ioo (0 : ℝ) (ρ ω : ℝ)) (dividendMeasure D ω) ∧
      Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) +
          (∫ s in Ioo (0 : ℝ) (ρ ω : ℝ), paid ω s ∂(dividendMeasure D ω)) =
        v (post 0 ω) + M ω + (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s) := by sorry
