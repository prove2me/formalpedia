-- Prove2me | Theorems.Thm_FairSelling_realize2
-- name    : FairSelling.realize2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:52:10.908303+00:00
-- url     : https://prove2.me/theorems/37d62895-2e46-4561-8086-6bf2168c4838
-- title:
--   Fair Selling: realize2
-- statement:
--   Realize a two-agent unified assignment (agent `0` gets `B0`, agent `1` gets `B1`, force-sale
--   set `F` split as `r0, r1`) as a concrete valid outcome with the stated utilities.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L227-L241
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L227-L241

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.realize2 (v : Fin 2 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (B0 B1 F : Finset G) (r0 r1 : ℝ)
    (hd01 : Disjoint B0 B1) (hdF0 : Disjoint F B0) (hdF1 : Disjoint F B1)
    (hr0 : 0 ≤ r0) (hr1 : 0 ≤ r1) (hsum : r0 + r1 ≤ ∑ g ∈ F, p g) :
    ∃ o : Outcome G 2, o.Valid p ∧
      util (v 0) o 0 = vbarSum (v 0) p B0 + r0 ∧
      util (v 1) o 1 = vbarSum (v 1) p B1 + r1 := by sorry
