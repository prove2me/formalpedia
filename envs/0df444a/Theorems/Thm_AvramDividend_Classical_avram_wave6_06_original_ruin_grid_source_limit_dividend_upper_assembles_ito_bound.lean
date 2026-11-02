-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_grid_source_limit_dividend_upper_assembles_ito_bound
-- name    : AvramDividend.Classical.avram_wave6_06_original_ruin_grid_source_limit_dividend_upper_assembles_ito_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T22:21:55.366711+00:00
-- url     : https://prove2.me/theorems/de45bfb6-d0ac-4a93-b896-2423e9e785f0
-- title:
--   Actual ruin-stopped source grid limit and eventual complete Stieltjes dividend domination assemble one-sided Ito budget
-- statement:
--   For the original physical controlled Levy process and ruin, the exact discounted four-event clipped triangular grid is Proved. If its true original source/discount sum converges almost surely to the source martingale plus generator drift, and the complementary original dividend/drop grid plus full original Stieltjes cash is eventually bounded above by the finite-variation remainder, the one-sided stopped Ito-Meyer upper inequality holds almost surely. This weakens the full exact dividend mesh limit to a one-sided eventual domination and is compatible with BV C1 and UBV C2 approaches. It asserts neither the source martingale limit nor the dividend domination automatically; those remain explicit separate owner obligations.
-- source:
--   Avram Prop 4(i), (5.11)-(5.13), exact original stopped grid e92ede42; analytic order-closed limit of source terms and one-sided control-Stieltjes bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_ruin_grid_source_limit_dividend_upper_assembles_ito_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (τ : Ω → ℝ≥0)
    (hτruin : ∀ ω, (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hmono : ∀ n, Monotone (u n))
    (hzero : ∀ n, u n 0 = 0)
    (hcover : ∀ ω, ∀ᶠ n in atTop, τ ω ≤ u n (k n))
    (Term Cash M G H : Ω → ℝ)
    (Source Dividend : ℕ → Ω → ℝ)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) *
        w (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω))
    (hSource : ∀ n ω, Source n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      ∑ i ∈ Finset.range (k n),
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i)))))
    (hDividend : ∀ n ω, Dividend n ω =
      let v : ℕ → ℝ≥0 := fun i => min (u n i) (τ ω)
      let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
      let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
      let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let pre : Prop := τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (k n),
          ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
            E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
            E (v (i + 1)) *
              (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
            E (v (i + 1)) *
              (w (Y (v (i + 1))) -
                w (riskProcess X x D (v (i + 1)) ω)))) +
        (if pre then 0 else E (τ ω) *
          (w (riskProcess X x D (τ ω) ω) - w (Y (τ ω)))) -
        Source n ω)
    (hSourceLimit : ∀ᵐ ω ∂P,
      Tendsto (fun n => Source n ω) atTop (𝓝 (M ω + G ω)))
    (hDividendBound : ∀ᵐ ω ∂P,
      ∀ᶠ n in atTop, Dividend n ω + Cash ω ≤ H ω) :
    ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω := by sorry
