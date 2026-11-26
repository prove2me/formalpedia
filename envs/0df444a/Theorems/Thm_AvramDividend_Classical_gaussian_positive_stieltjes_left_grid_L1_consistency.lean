-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_positive_stieltjes_left_grid_L1_consistency
-- name    : AvramDividend.Classical.gaussian_positive_stieltjes_left_grid_L1_consistency
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T07:58:13.93294+00:00
-- url     : https://prove2.me/theorems/53fcfb3d-e5df-4238-a17c-f06eb0034790
-- title:
--   Left-grid consistency for the positive-time stopped Gaussian Itô–Stieltjes residual
-- statement:
--   Partition a deterministic bound $T$ for the stopping clock into $j+1$ equal cells. On each cell whose left endpoint precedes the clock, weight the centered Gaussian surplus increment by the discounted test derivative at the postpayment reserve there. The derivative is composed with the projection onto the closed reserve interval to give a globally defined coefficient.
--
--   Show that these real sums converge in $L^1$ to the signed residual obtained by subtracting the postpayment initial test value and the discounted generator integral from the terminal test value plus the positive-time Stieltjes variation. The variation uses divided differences for dividend jumps. The final dividend right jump is excluded, and the terminal reserve is prepayment at a positive stop. The statement only asks for consistency of explicit finite sums, with no stochastic integral object or zero-mean requirement.
-- source:
--   Brownian specialization of the controlled Itô calculation of Avram, Palmowski and Pistorius (2007), equation (5.11), https://arxiv.org/pdf/math/0702893#page=19.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
open Filter
open scoped Topology

theorem AvramDividend.Classical.gaussian_positive_stieltjes_left_grid_L1_consistency
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
  let clamp : ℝ → ℝ := fun y => max l (min u y)
  let R : ℝ≥0 → Ω → ℝ := fun t ω => X.X t ω - (t : ℝ) * X.c
  let step : ℕ → ℝ≥0 := fun j => T / ((j + 1 : ℕ) : ℝ≥0)
  let left : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) * step j
  let weight : ℕ → ℕ → Ω → ℝ := fun j i ω =>
    if ρ ω ≤ left j i then 0 else
      Real.exp (-(q * (left j i : ℝ))) * deriv v (clamp (post (left j i) ω))
  let S : ℕ → Ω → ℝ := fun j ω => ∑ i ∈ Finset.range (j + 1),
    weight j i ω * (R (left j i + step j) ω - R (left j i) ω)
  let residual : Ω → ℝ := fun ω =>
    (Real.exp (-(q * (ρ ω : ℝ))) * v (finish ω) +
      (∫ s in Ioo (0 : ℝ) (ρ ω : ℝ), paid ω s ∂(dividendMeasure D ω))) -
        v (post 0 ω) - (∫ s in Ico (0 : ℝ) (ρ ω : ℝ), driftTerm ω s)
  AEStronglyMeasurable residual P ∧
    Tendsto (fun j => ∫⁻ ω, ‖S j ω - residual ω‖ₑ ∂P) atTop (𝓝 0) := by sorry
