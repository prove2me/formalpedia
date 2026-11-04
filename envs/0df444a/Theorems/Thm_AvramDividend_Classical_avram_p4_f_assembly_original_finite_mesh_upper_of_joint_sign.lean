-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_finite_mesh_upper_of_joint_sign
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_finite_mesh_upper_of_joint_sign
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T07:56:31.09395+00:00
-- url     : https://prove2.me/theorems/77ae02c4-482e-4a62-a92a-45f5694711e0
-- title:
--   Actual source finite stopped Itô mesh cash upper bound after jointly nonpositive generator and dividend residuals
-- statement:
--   For the original Lévy process X and admissible original dividend D, the already accepted exact zero-time-atom finite Itô mesh ledger bounds terminal postpayment value plus the true initial right-dividend amount and all mesh cash increments. If the generator and control residual meshes have jointly nonpositive sum, their contribution can be removed, leaving the exact upper bound by initial w(x) plus the source martingale mesh increments. This is an algebraic original-source finite-mesh integration, conditional on a genuine stochastic cell identity and signed source residuals; it is not the fixed stopped-clock Itô–Meyer theorem itself.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), Eq. (5.11)-(5.13); accepted original-source finite ledger theorem 2f8def11-0821-46ee-a44a-8b0b7dfece78.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_original_finite_ito_ledger_with_zero_atom
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_finite_mesh_upper_of_joint_sign
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
    (N : ℕ)
    (hsign : (∑ k ∈ Finset.range N, GInc k) +
      (∑ k ∈ Finset.range N, HInc k) ≤ 0) :
    Real.exp (-(q * (clock N : ℝ))) *
        w (x + X.X (clock N) ω - rightLimit D (clock N) ω) +
      rightLimit D 0 ω + (∑ k ∈ Finset.range N, CashInc k) ≤
      w x + (∑ k ∈ Finset.range N, MInc k) := by sorry
