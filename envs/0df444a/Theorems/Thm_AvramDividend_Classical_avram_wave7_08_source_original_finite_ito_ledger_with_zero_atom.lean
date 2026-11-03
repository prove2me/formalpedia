-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_finite_ito_ledger_with_zero_atom
-- name    : AvramDividend.Classical.avram_wave7_08_source_original_finite_ito_ledger_with_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:42:54.793565+00:00
-- url     : https://prove2.me/theorems/2f8def11-0821-46ee-a44a-8b0b7dfece78
-- title:
--   Finite original stopped Ito ledger from corrected zero-atom secant with no assumed initial budget
-- statement:
--   Derive the original-source finite discounted postpayment Itô–Meyer ledger with the initial right-dividend payment exactly D(0+) from corrected hjump and canonical X(0)=D(0)=0, without hypothesising an initial budget. Combine this source zero-atom entry with the finite-cell stochastic inequality by exact telescoping. The only remaining assumptions are genuine one-step stopped Itô innovations to be proved using the original source.
-- source:
--   Combines authored and separately Proved source zero-atom ledger entry with source finite mesh Ito ledger, for W7-05/06/07 and positive-reserve W7-08 residual construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_source_original_finite_ito_ledger_with_zero_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (clock : ℕ → ℝ≥0) (hclock0 : clock 0 = 0) (ω : Ω)
    (V : ℕ → ℝ)
    (hV : ∀ k, V k =
      Real.exp (-(q * (clock k : ℝ))) *
        w (x + X.X (clock k) ω - rightLimit D (clock k) ω))
    (CashInc MInc GInc HInc : ℕ → ℝ)
    (hcell : ∀ k, V (k + 1) + CashInc k ≤
      V k + MInc k + GInc k + HInc k)
    (N : ℕ) :
    Real.exp (-(q * (clock N : ℝ))) *
        w (x + X.X (clock N) ω - rightLimit D (clock N) ω) +
      rightLimit D 0 ω + (∑ k ∈ Finset.range N, CashInc k) ≤
      w x + (∑ k ∈ Finset.range N, MInc k) +
        (∑ k ∈ Finset.range N, GInc k) +
        (∑ k ∈ Finset.range N, HInc k) := by sorry
