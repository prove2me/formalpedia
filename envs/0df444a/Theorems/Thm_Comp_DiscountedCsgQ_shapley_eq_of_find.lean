-- Prove2me | Theorems.Thm_Comp_DiscountedCsgQ_shapley_eq_of_find
-- name    : Comp.DiscountedCsgQ.shapley_eq_of_find
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:46:10.228337+00:00
-- url     : https://prove2.me/theorems/7dedb5e2-cfda-4a5b-abc3-9890a6e54fec
-- title:
--   Discounted Csg Q: shapley eq of find
-- statement:
--   **The payoff.** When the search succeeds on the rational stage game at `s`, the value `t` it
--       returns is exactly the real Shapley operator's value there. Composition of
--       `shapleyGameQ_value` with `Comp/Search.lean`'s `value_eq_of_find`, so the solver is still never
--       trusted -- only its checked output is.
--
--       This is the statement an executable iteration rests on: run the search per state with `#eval`,
--       read off the numbers, and each one is pinned to the specification by this theorem.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Shapley.lean#L99-L106
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Shapley.lean#L99-L106

import Definitions.Def_Comp_Search
import Definitions.Def_Comp_Shapley
set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.DiscountedCsgQ.shapley_eq_of_find (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed)
    {As1 : List A1} {As2 : List A2} {v : S → ℚ} {s : S}
    {t : ℚ} {p : A1 → ℚ} {q : A2 → ℚ}
    (hf : (G.shapleyGameQ s v).findValueCert As1 As2 = some (t, p, q)) :
    (G.toDiscountedCSG h).shapley (fun s' => ((v s' : ℚ) : ℝ)) s = ((t : ℚ) : ℝ) := by sorry
