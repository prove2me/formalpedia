-- Prove2me | Theorems.Thm_FairSelling_servable_of_inv
-- name    : FairSelling.servable_of_inv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:01.183662+00:00
-- url     : https://prove2.me/theorems/8665a2af-1c8a-4409-a608-e1187a266917
-- title:
--   Fair Selling: servable of inv
-- statement:
--   **The main loop of Algorithm 1.**  From a state satisfying the invariant, all the active
--   agents can be served.  The induction is on the number of active agents: the agent of highest
--   maximin share proposes a canonical partition (Lemma 9), the matching phase serves at least that
--   agent (`round_outcome`), and the invariant is restored on the smaller state (Proposition 5).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L55-L89
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L55-L89

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Definitions.Def_RequestProject_TwoThirds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.servable_of_inv (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) :
    ∀ (m : ℕ) (T : Finset (Fin n)) (R : Finset G) (D : ℝ), T.card = m → Inv v p T R D →
      Servable v p (thr v p) T R D := by sorry
