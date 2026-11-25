-- Prove2me | Theorems.Thm_Finset_bernoulliProb_eq_add
-- name    : Finset.bernoulliProb_eq_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:58.243844+00:00
-- url     : https://prove2.me/theorems/ddd9f64d-561e-42a4-bfeb-5d23baca213d
-- title:
--   Finset: bernoulli Prob eq add
-- statement:
--   Splitting an event along another: `P(P) = P(P ∧ Q) + P(P ∧ ¬Q)`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L72-L76
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/LocalLemma.lean#L72-L76

module
public import Definitions.Def_ProbabilisticMethod_BernoulliWeights
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Definitions.Def_ProbabilisticMethod_LocalLemma
set_option autoImplicit true
@[expose] public section
public section
open Finset Real
open Finset
variable {α ι : Type*} [DecidableEq α] {U : Finset α} {p : ℝ}
variable (U p)

theorem Finset.bernoulliProb_eq_add (P Q : Finset α → Prop) [DecidablePred P] [DecidablePred Q] :
    U.bernoulliProb p P =
      U.bernoulliProb p (fun A => P A ∧ Q A) + U.bernoulliProb p (fun A => P A ∧ ¬Q A) := by sorry
