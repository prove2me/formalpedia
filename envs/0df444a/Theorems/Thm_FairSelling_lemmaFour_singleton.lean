-- Prove2me | Theorems.Thm_FairSelling_lemmaFour_singleton
-- name    : FairSelling.lemmaFour_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:20.776634+00:00
-- url     : https://prove2.me/theorems/f94570a6-08ae-4b63-9e8f-43970a2ba9b5
-- title:
--   Fair Selling: lemma Four singleton
-- statement:
--   **The singleton case of Lemma 4.**  A bundle made of at most one kept good `K` plus money `m`
--   coming from the sale of the single good `f` is handed out, the unused proceeds `p f - m` being
--   banked.  An agent that values the bundle at most `3/4 · MMS` can still split what is left into two
--   bundles worth `3/4 · MMS` each.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L65-L214
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaFourResidual.lean#L65-L214

import Mathlib
import Definitions.Def_RequestProject_ConfigSplit
import Definitions.Def_RequestProject_CanonicalStrict
import Definitions.Def_RequestProject_LemmaFourResidual
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.lemmaFour_singleton (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hnobig : ∀ g, vbar w p g < (3 / 4 : ℝ) * MMS 3 w p)
    (K : Finset G) (f : G) (m : ℝ) (hfK : f ∉ K) (hm0 : 0 ≤ m) (hmf : m ≤ p f)
    (hKcard : K.card ≤ 1) (hprice : (1 / 4 : ℝ) * MMS 3 w p ≤ p f)
    (hrej : vbarSum w p K + m ≤ (3 / 4 : ℝ) * MMS 3 w p) :
    (3 / 4 : ℝ) * MMS 3 w p ≤ MMS 2 (cashVal (Finset.univ \ (K ∪ {f})) w)
      (cashPrice (Finset.univ \ (K ∪ {f})) p (p f - m)) := by sorry
