-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_finitecap_stopped_ito_stieltjes_formula
-- name    : AvramDividend.Classical.gaussian_finitecap_stopped_ito_stieltjes_formula
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T07:12:04.850805+00:00
-- url     : https://prove2.me/theorems/7b07c3a5-0209-4019-9a9e-65366ec9f371
-- title:
--   Stopped Gaussian Itô–Stieltjes formula for a smooth test function on a finite reserve cap
-- statement:
--   For the original Gaussian-only surplus process, a finite positive reserve cap, and an admissible left-continuous dividend strategy, stop at the earlier of ruin and the positive integer horizon $n$. Let $v$ be twice continuously differentiable on a neighborhood of the closed reserve interval.
--
--   Prove the controlled Itô–Stieltjes identity on the original probability space. The discounted terminal test value plus the discounted dividend variation term equals the initial test value plus an integrable centered Gaussian martingale increment and the discounted generator integral. The dividend variation term weights continuous Stieltjes mass by the derivative at the reserve and each right jump by the exact divided difference between its prepayment and postpayment reserves. At a positive stop the terminal reserve is prepayment and the endpoint dividend is excluded. If the clock is zero the terminal reserve is postpayment and the original time-zero atom is included.
--
--   The identity is signed and imposes no HJB inequality or lower bound on the derivative of the test function.
-- source:
--   Avram, Palmowski and Pistorius (2007), Section 5.4, equation (5.11) and the stopped classical-control argument before (5.13), https://arxiv.org/pdf/math/0702893#page=19. Smooth Gaussian identity underlying d19a8155-6cf8-4ec3-a8ce-66e19602cbf2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.gaussian_finitecap_stopped_ito_stieltjes_formula
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q) (v : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (a b : ℝ) (ha : a < 0) (hb : C.toReal < b)
    (hvSmooth : ContDiffOn ℝ 2 v (Ioo a b))
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) :
  let ρ : Ω → ℝ≥0 := fun ω => (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
  let A : Ω → Set ℝ := fun ω =>
    paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ)
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
  ∃ M : Ω → ℝ,
    Integrable M P ∧ (∫ ω, M ω ∂P) = 0 ∧
      ∀ᵐ ω ∂P,
        IntegrableOn (paid ω) (A ω) (dividendMeasure D ω) ∧
        (Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) +
          (∫ s in A ω, paid ω s ∂(dividendMeasure D ω)) =
          v x + M ω + (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s)) := by sorry
