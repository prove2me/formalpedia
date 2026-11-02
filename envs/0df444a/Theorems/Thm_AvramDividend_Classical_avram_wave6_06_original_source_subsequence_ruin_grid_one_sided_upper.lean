-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_source_subsequence_ruin_grid_one_sided_upper
-- name    : AvramDividend.Classical.avram_wave6_06_original_source_subsequence_ruin_grid_one_sided_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T00:02:45.400943+00:00
-- url     : https://prove2.me/theorems/1f02a071-ed35-414a-aafe-9b0a4e5b4fa0
-- title:
--   Actual ruin-stopped source grid needs only an almost-sure convergent subsequence to assemble stopped one-sided Ito upper bound
-- statement:
--   For the genuine original Levy process X, admissible left-continuous dividend strategy D, ruin-localised finite stopped grid and complete dividend Stieltjes cash, the physical source-grid upper bound requires only convergence along one common deterministic subsequence φ tending to infinity, rather than almost sure convergence of the entire grid sequence. The full-grid eventual cover and dividend domination persist along φ. This weakens the stochastic convergence cutset and interfaces with L2 subsequence extraction, but still explicitly assumes that extraction and dividend estimate; it does not claim a stochastic Ito identity.
-- source:
--   Avram Proposition 4(i), stopped source-grid limit Eq (5.11), deterministic reindexing of Proved de45bfb6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_grid_source_limit_dividend_upper_assembles_ito_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_source_subsequence_ruin_grid_one_sided_upper
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
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
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
    (hSourceSubsequence : ∀ᵐ ω ∂P,
      Tendsto (fun n => Source (φ n) ω) atTop (𝓝 (M ω + G ω)))
    (hDividendBound : ∀ᵐ ω ∂P,
      ∀ᶠ n in atTop, Dividend n ω + Cash ω ≤ H ω) :
    ∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω := by sorry
