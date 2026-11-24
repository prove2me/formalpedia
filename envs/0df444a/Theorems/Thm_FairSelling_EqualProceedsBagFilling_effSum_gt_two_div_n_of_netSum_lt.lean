-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_effSum_gt_two_div_n_of_netSum_lt
-- name    : FairSelling.EqualProceedsBagFilling.effSum_gt_two_div_n_of_netSum_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:36:47.413746+00:00
-- url     : https://prove2.me/theorems/4546017a-d649-4e95-903b-14867781e5ce
-- title:
--   Equal Proceeds Bag Filling: eff Sum gt two div n of net Sum lt
-- statement:
--   **The manuscript's intermediate bound `v'ₖ(B) ≤ (2/n)·TPSₖ` is false as stated.**  In the
--   instance above, the single-good bag `B = {g₀}` is one that a round can produce: the good is
--   cheaper than the agent's `TPS` (rule 1 does not fire), it is worth less to her than
--   `TPSₖ/n` (rule 2 does not fire), and its net value `ṽₖ(B)` is below `TPSₖ/n`, so she does not
--   claim the bag.  Nevertheless `v'ₖ(B) = 9/10` exceeds `(2/10)·TPSₖ = 99/500`.  The bound is
--   correct for the net value `ṽₖ(B)`, which is what the stopping rule controls.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L678-L691
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L678-L691

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_TPSCompute
import Definitions.Def_RequestProject_EqualProceedsBagFilling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open FairSelling.EqualProceedsBagFilling
variable {G : Type*} {n : ℕ}
variable {vi p : G → ℝ} {tk : ℝ}

theorem FairSelling.EqualProceedsBagFilling.effSum_gt_two_div_n_of_netSum_lt :
    ∃ (val pr : Fin 10 → ℝ) (e : Fin 10) (t : ℝ),
      (∀ g, 0 ≤ val g) ∧ (∀ g, 0 ≤ pr g) ∧ t = TPS 10 val pr ∧
      pr e < t ∧ val e < t / 10 ∧
      netSum 10 val pr t {e} < t / 10 ∧
      (2 / 10) * t < effSum val pr t {e} := by sorry
