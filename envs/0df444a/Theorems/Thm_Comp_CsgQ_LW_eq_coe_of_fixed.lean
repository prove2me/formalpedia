-- Prove2me | Theorems.Thm_Comp_CsgQ_LW_eq_coe_of_fixed
-- name    : Comp.CsgQ.LW_eq_coe_of_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:01:39.360116+00:00
-- url     : https://prove2.me/theorems/4eb5da48-dd21-4360-8c2d-0bc86cff612d
-- title:
--   Csg Q: LW eq coe of fixed
-- statement:
--   **The payoff, one state at a time.** A `Finset A1` reached by iterating `lStepF` from `∅` and
--       left fixed by it *is* the row-action witness set of the real-valued game at `s`.
--
--       Both hypotheses are decidable statements about concrete `Finset`s, and `n` is a parameter rather
--       than a bound to be justified: the climb is run by `#eval`, the stabilisation observed, and the
--       two inequalities do the rest. `Lpre1`'s own bridge will take the `∀ s` version of `hfix` as its
--       hypothesis, which is how an inner exactness becomes an outer soundness.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L151-L162
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeLimitFinset.lean#L151-L162

import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_Reach
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Comp_QualitativeLimitFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.LW_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (x y : Finset S) (s : S)
    (c : Finset A1) (n : ℕ) (hiter : (G.lStepF x y s)^[n] ∅ = c)
    (hfix : G.lStepF x y s c = c) :
    (G.toCSG h).LW ↑x ↑y s = ↑c := by sorry
