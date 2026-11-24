-- Prove2me | Theorems.Thm_BalanceSpecification_tendsto_integral_comp_sub_finiteOrbitProbability
-- name    : BalanceSpecification.tendsto_integral_comp_sub_finiteOrbitProbability
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:07:30.572469+00:00
-- url     : https://prove2.me/theorems/5e7d24f9-4705-447d-9ec2-7188cabaab0d
-- title:
--   Balance Specification: tendsto integral comp sub finite Orbit Probability
-- statement:
--   Orbit averages remain asymptotically invariant even when both the finite
--   family and its points vary with the averaging length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L165-L173
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/GibbsExistence.lean#L165-L173

module
public import Definitions.Def_BalanceSpecificaton_Measures
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_GibbsExistence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open MeasureTheory Filter
open scoped Topology ENNReal Classical BoundedContinuousFunction
variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [T2Space Ω]
    [HasOuterApproxClosed Ω]
    {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
omit [HasOuterApproxClosed Ω]

theorem BalanceSpecification.tendsto_integral_comp_sub_finiteOrbitProbability
    (f : Ω → Ω) (x : ∀ n, I n → Ω) (g : Ω →ᵇ ℝ) :
    Tendsto (fun n =>
      (∫ y, (g ∘ f) y ∂(finiteOrbitProbability f (x n) n : Measure Ω)) -
        ∫ y, g y ∂(finiteOrbitProbability f (x n) n : Measure Ω))
      atTop (𝓝 0) := by sorry
