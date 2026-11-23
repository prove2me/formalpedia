-- Prove2me | Theorems.Thm_Comp_CsgQ_G_eq_coe_of_fixed
-- name    : Comp.CsgQ.G_eq_coe_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:53:15.94602+00:00
-- url     : https://prove2.me/theorems/8b50107d-15ad-4551-b9e4-3941350981e1
-- title:
--   Csg Q: G eq coe of fixed
-- statement:
--   **The payoff.** A `Finset` that was reached by iterating `gStepF` from `Finset.univ` and that
--       `gStepF` leaves fixed *is* the sure-safety region of the real-valued game, on the nose.
--
--       Both hypotheses are decidable statements about concrete `Finset`s, and both are discovered by
--       `#eval` rather than proved about the search: iterate until the printed region repeats, take `n`
--       and `c` from what was printed, and the fixed-point check is then a `Finset` equality. Nothing
--       here assumes a bound on `n`, and nothing appeals to a theorem that the iteration terminates
--       within `|S|` steps -- stabilisation is *observed*, and the two inequalities do the rest.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L129-L138
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/QualitativeFinset.lean#L129-L138

import Definitions.Def_Comp_Qualitative
import Definitions.Def_Comp_QualitativeFinset
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.G_eq_coe_of_fixed (G : CsgQ S A1 A2) (h : G.WellFormed) (safe c : Finset S) (n : ℕ)
    (hiter : (G.gStepF safe)^[n] Finset.univ = c) (hfix : G.gStepF safe c = c) :
    (G.toCSG h).G (↑safe : Set S) = ↑c := by sorry
