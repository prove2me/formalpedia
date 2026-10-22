-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_stopped_firstRecord_fin_grid_discount_bounds
-- name    : AvramDividend.Classical.runningSup_stopped_firstRecord_fin_grid_discount_bounds
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T09:51:43.538746+00:00
-- url     : https://prove2.me/theorems/f1a9dd57-83d0-4cda-8f17-6d6d35ec2769
-- title:
--   Finite first-record h-cell grid yields exact two-sided discounted Stieltjes payout sums
-- statement:
--   For the genuine spectrally negative Lévy running-supremum regulator, let t(i) be finite attained first upward passage times of the equally spaced record levels b+i h through level n, with nondecreasing passage times and the final time strictly before the original stopped-payment horizon. The complete original q-discounted Stieltjes payout between t(0) and t(n) is bounded below by the finite sum of h exp(-q t(i+1)) and above by the sum of h exp(-q t(i)). The proof applies the remotely accepted exact first-record h-cell bound to each adjacent level and combines the rewards using the exact stopped finite interval partition identity. It assumes no strong-Markov regeneration or two-sided q-scale exit identities.
-- source:
--   Accepted original first-record h-cell bounds target a87a10e8-a1d2-4485-a173-c0cf2d7e72d0 and dependency-gated stopped_lintegral_Ioc_partition_fin target 327485ca-2f02-40a7-ae17-175bddbe2b84, candidate 12757.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_Ioc_partition_fin
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_firstRecord_step_discount_bounds


open MeasureTheory Set
open scoped NNReal ENNReal BigOperators Classical
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_stopped_firstRecord_fin_grid_discount_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h)
    (n : ℕ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (hpass : ∀ i : ℕ, i ≤ n →
      (t i : ℝ≥0∞) =
      (⨅ (r : ℝ≥0) (_ : b + (i : ℝ) * h < X.X r ω),
        (r : ℝ≥0∞)))
    (hSurvive : ENNReal.ofReal (t n : ℝ) < τ) :
    (∑ i ∈ Finset.range n,
      ENNReal.ofReal (Real.exp (-(q * (t (i + 1) : ℝ)))) *
        ENNReal.ofReal h) ≤ (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (t 0 : ℝ) (t n : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ∧ (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (t 0 : ℝ) (t n : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤ (∑ i ∈ Finset.range n,
      ENNReal.ofReal (Real.exp (-(q * (t i : ℝ)))) *
        ENNReal.ofReal h) := by sorry
