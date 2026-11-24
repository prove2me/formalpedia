-- Prove2me | Theorems.Thm_FairSelling_config_sum_bound
-- name    : FairSelling.config_sum_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:51:56.445685+00:00
-- url     : https://prove2.me/theorems/97e9e179-d439-4498-85ce-3d8bde6a58a8
-- title:
--   Fair Selling: config sum bound
-- statement:
--   From a two-part configuration in which both parts are worth at least `M`, twice `M` is
--   bounded by the total `v̄`-value of the kept goods plus the force-sale proceeds.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L178-L198
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoAgents.lean#L178-L198

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.config_sum_bound (w p : G → ℝ) (M : ℝ) (A : Fin 2 → Finset G) (s : Finset G) (q : Fin 2 → ℝ)
    (h : Config w p M A s q) : 2 * M ≤ vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g := by sorry
