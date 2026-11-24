-- Prove2me | Theorems.Thm_BalanceSpecification_GibbsBounds_extension_card_exp_lower
-- name    : BalanceSpecification.GibbsBounds.extension_card_exp_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:11:05.540307+00:00
-- url     : https://prove2.me/theorems/cf86fd59-fc46-4f70-97c7-be374bd6b558
-- title:
--   Gibbs Bounds: extension card exp lower
-- statement:
--   A finite refinement of an admissible cylinder must have enough elements
--   to carry its Gibbs lower mass, since every refined cylinder has a Gibbs upper bound.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L46-L75
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsBalance.lean#L46-L75

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
omit [DiscreteTopology A] [BorelSpace A]

theorem BalanceSpecification.GibbsBounds.extension_card_exp_lower {hX : X.carrier.Nonempty}
    {μ : ProbabilityMeasure X.carrier} {K : ℝ} (hG : GibbsBounds hX μ K)
    {u : Word A} (hu : u ∈ language X) (n : ℕ)
    (S : Finset (Word A)) (f : Word A → Word A)
    (hwords : ∀ w ∈ S, f w ∈ language X ∧ (f w).length = u.length + n)
    (hsum : (∑ w ∈ S, (μ : Measure X.carrier).real (cylinder X (f w) 0)) =
      (μ : Measure X.carrier).real (cylinder X u 0)) :
    Real.exp ((n : ℝ) * entropy X hX) ≤ K ^ 2 * S.card := by sorry
