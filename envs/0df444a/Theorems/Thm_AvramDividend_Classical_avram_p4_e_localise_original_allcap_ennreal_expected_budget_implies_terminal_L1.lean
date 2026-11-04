-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_allcap_ennreal_expected_budget_implies_terminal_L1
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_allcap_ennreal_expected_budget_implies_terminal_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:45:36.988887+00:00
-- url     : https://prove2.me/theorems/6bb60804-ca88-4c2a-8b38-5eaf3e23cb00
-- title:
--   All-cap expected nonnegative original stopped budget forces true terminal L1 and real inequality
-- statement:
--   The genuine stopped source terminal and complete Stieltjes cash are already a.e. measurable and nonnegative. A finite ENNReal expectation upper bound for their sum, with nonnegative initial verification value, forces terminal L1 despite infinite cap, and yields the real expected inequality needed by the separately Proved P4-F witness equivalence. This is conditional on the authentic stopped expected budget, not an assumed local martingale decomposition.
-- source:
--   P4-F signed witness iff real expected budget 9ff8bb39; P4-E original true stopped terminal nonnegative 32477187 and P4-F original cash nonnegative 4db282c6; pinned Mathlib hasFiniteIntegral_iff_ofReal, integral_eq_lintegral_of_nonneg_ae, ENNReal.toReal_le_of_le_ofReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- A finite ENNReal original stopped reward bound forces terminal L¹, even when the dividend cap is infinite and the payoff is unbounded. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_allcap_ennreal_expected_budget_implies_terminal_L1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (w : ℝ → ℝ) (x : ℝ) (hwx : 0 ≤ w x)
    (Term Cash : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hCashPos : ∀ᵐ ω ∂P, 0 ≤ Cash ω)
    (hBound : (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    Integrable Term P ∧
    (∫ ω, Term ω + Cash ω ∂P) ≤ w x := by sorry
