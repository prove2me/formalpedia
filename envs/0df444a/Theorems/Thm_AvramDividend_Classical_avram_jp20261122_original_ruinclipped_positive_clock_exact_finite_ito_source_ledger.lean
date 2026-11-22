-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jp20261122_original_ruinclipped_positive_clock_exact_finite_ito_source_ledger
-- name    : AvramDividend.Classical.avram_jp20261122_original_ruinclipped_positive_clock_exact_finite_ito_source_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:05:41.757271+00:00
-- url     : https://prove2.me/theorems/aad69e54-f093-4e68-aa2f-b8f1307cf98c
-- title:
--   Exact physical stopped Levy source-grid telescope with ruin terminal and initial right-dividend cash
-- statement:
--   For the exact original spectrally negative Levy surplus and arbitrary adapted dividend process D, express the ruin-clipped discounted full payoff F minus w(x) as a finite chronological source-increment sum plus post-source right-payment value increments, a genuine terminal correction for the last incomplete grid cell that retains the at-ruin book reserve, an initial right-paid dividend correction, and the original literal Iic paymentTimes discounted Stieltjes cash. This exact finite-grid identity is a substantive algebraic first stage of the positive-clock Ito-Stieltjes source; no sign or L1 limit is assumed, no simulator clock is substituted, and it must be proved by importing the already Proved original stopped source/postdividend telescope 036fe055.
-- source:
--   Original Avram controlled stopped surplus; Proved 036fe055-37c4-40d0-b260-a6c6558cf43f; root-connected positive-clock source cfb0fd02-4145-4c0f-b754-08ca9913e868

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_jp20261122_original_ruinclipped_positive_clock_exact_finite_ito_source_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0) (n : ℕ)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
      let Y : ℕ → ℝ := fun i =>
        x + X.X (v i) ω - rightLimit D (v i) ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let W : ℝ := if σ ω = 0 ∨
        (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω
      let Cash : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      F ω - w x =
        (∑ i ∈ Finset.range m,
          ((e (i + 1) * w (Z i) - e i * w (Y i)) +
            e (i + 1) * (w (Y (i + 1)) - w (Z i)))) +
        (Real.exp (-(q * (σ ω : ℝ))) * w W - e m * w (Y m)) +
        (e 0 * w (Y 0) - w x) + Cash := by sorry
