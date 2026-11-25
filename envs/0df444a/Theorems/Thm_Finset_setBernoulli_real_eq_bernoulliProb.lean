-- Prove2me | Theorems.Thm_Finset_setBernoulli_real_eq_bernoulliProb
-- name    : Finset.setBernoulli_real_eq_bernoulliProb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:25.180063+00:00
-- url     : https://prove2.me/theorems/fc1c4689-bf16-4f07-9ffc-aa434b780b1c
-- title:
--   Finset: set Bernoulli real eq bernoulli Prob
-- statement:
--   The product of `p`-Bernoulli distributions on a finite set `U` is the finite `p`-biased cube:
--   it gives a family `S` of sets the probability of any event `Q` that agrees with `S` on the
--   subsets of `U`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/MeasureBridge.lean#L42-L61
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/MeasureBridge.lean#L42-L61

module
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Definitions.Def_ProbabilisticMethod_MeasureBridge
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Finset
open Finset
variable {α : Type*} [DecidableEq α] [Countable α]

theorem Finset.setBernoulli_real_eq_bernoulliProb (U : Finset α) (p : I) {S : Set (Set α)}
    {Q : Finset α → Prop} [DecidablePred Q] (hQ : ∀ A ⊆ U, (A : Set α) ∈ S ↔ Q A) :
    setBer((U : Set α), p).real S = U.bernoulliProb p Q := by sorry
