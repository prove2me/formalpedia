-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_wordCount_exp_upper
-- name    : BalanceSpecification.GibbsBounds.wordCount_exp_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:00.725684+00:00
-- url     : https://prove2.me/theorems/90f8f69e-577b-48c0-85d5-9924a2bd3d4c
-- title:
--   Gibbs Bounds: word Count exp upper
-- statement:
--   Summing the lower Gibbs cylinder bound controls the total word count.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L22-L41
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L22-L41

module
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
public import Definitions.Def_BalanceSpecificaton_BlockEntropy
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsBalance
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory
variable {A : Type*} [Fintype A] [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [BorelSpace A] {X : ShiftSpace A}

theorem BalanceSpecification.GibbsBounds.wordCount_exp_upper {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hG : GibbsBounds hX μ K) (n : ℕ) :
    (wordCount (language X) n : ℝ) ≤ K * Real.exp ((n : ℝ) * entropy X hX) := by sorry
