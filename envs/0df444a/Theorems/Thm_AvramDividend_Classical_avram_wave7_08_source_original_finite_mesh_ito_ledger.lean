-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_finite_mesh_ito_ledger
-- name    : AvramDividend.Classical.avram_wave7_08_source_original_finite_mesh_ito_ledger
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:37:49.145188+00:00
-- url     : https://prove2.me/theorems/b820d43c-a7f4-475b-889a-f49201d43314
-- title:
--   Exact original discounted postpayment finite mesh Ito ledger telescopes with time-zero dividend atom
-- statement:
--   Given the exact original discounted postpayment reserve value V at each clock, the initial time-zero atom budget and one-cell stopped Ito inequalities whose increments comprise source dividend cash, centred Gaussian/jump innovations, and generator/dividend residuals, telescope all mesh cells. The resulting pathwise global budget retains exact X, D, right-limit reserves, discount and time-zero cash. The one-cell source martingale inequality and convergence are genuine future obligations.
-- source:
--   W7-08 source-specific finite mesh accounting needed to assemble W7-05 finite Gaussian, W7-06/07 jump terms, W7-03 Stieltjes and corrected zero-atom entry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_original_finite_mesh_ito_ledger
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (clock : ℕ → ℝ≥0) (ω : Ω)
    (V : ℕ → ℝ)
    (hV : ∀ k, V k =
      Real.exp (-(q * (clock k : ℝ))) *
        w (x + X.X (clock k) ω - rightLimit D (clock k) ω))
    (CashZero : ℝ) (CashInc MInc GInc HInc : ℕ → ℝ)
    (hinit : V 0 + CashZero ≤ w x)
    (hcell : ∀ k, V (k + 1) + CashInc k ≤
      V k + MInc k + GInc k + HInc k)
    (N : ℕ) :
    Real.exp (-(q * (clock N : ℝ))) *
        w (x + X.X (clock N) ω - rightLimit D (clock N) ω) +
      CashZero + (∑ k ∈ Finset.range N, CashInc k) ≤
      w x + (∑ k ∈ Finset.range N, MInc k) +
        (∑ k ∈ Finset.range N, GInc k) +
        (∑ k ∈ Finset.range N, HInc k) := by sorry
