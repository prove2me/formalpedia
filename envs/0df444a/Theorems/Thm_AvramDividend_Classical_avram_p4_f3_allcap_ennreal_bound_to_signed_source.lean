-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_allcap_ennreal_bound_to_signed_source
-- name    : AvramDividend.Classical.avram_p4_f3_allcap_ennreal_bound_to_signed_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:35:00.277091+00:00
-- url     : https://prove2.me/theorems/b42989a9-47a1-4898-98a8-a61bbb140a97
-- title:
--   Source-exact all-cap nonnegative stopped ENNReal expected-budget to integrable signed Itô witnesses
-- statement:
--   For the original spectrally negative Levy process, if the stopped terminal-plus-cash reward has an independently established ENNReal expectation upper bound at every cap, the exact integrable mean-zero source martingale witness and integrable signed drift witnesses follow on the same original probability space. This is a conditional bridge: the stochastic stopped expected-budget hypothesis is explicit and remains to be established separately.
-- source:
--   Proved 6bb60804 all-cap ENNReal expected bound implies L1 terminal and real budget; Proved 9ff8bb39 original conditional L1 signed witness iff real expected budget. Neither source imports canonical Open 0dda/fdb.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_allcap_ennreal_expected_budget_implies_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_L1_signed_witness_iff_expected_budget
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f3_allcap_ennreal_bound_to_signed_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (x : ℝ) (hwx : 0 ≤ w x)
    (Term Cash : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hCashPos : ∀ᵐ ω ∂P, 0 ≤ Cash ω)
    (hExpected : (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x)) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
