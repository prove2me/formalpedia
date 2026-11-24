-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_exists_equalProceeds_TPS_approx_full
-- name    : FairSelling.EqualProceedsBagFilling.exists_equalProceeds_TPS_approx_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:36:14.982164+00:00
-- url     : https://prove2.me/theorems/6959b194-7649-4c42-b852-3388c55351ab
-- title:
--   Equal Proceeds Bag Filling: exists equal Proceeds TPS approx full
-- statement:
--   The same conclusion with a **full** allocation: every good is either sold or allocated, and
--   the distributed proceeds equal the proceeds of the sold goods (equation (3) of the model).
--   Leftover goods are simply handed to the first agent, which only increases her utility.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L542-L622
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L542-L622

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
variable [Fintype G] [DecidableEq G]

theorem FairSelling.EqualProceedsBagFilling.exists_equalProceeds_TPS_approx_full (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      o.sold ∪ Finset.univ.biUnion o.kept = Finset.univ ∧
      (∑ j, o.money j) = ∑ g ∈ o.sold, p g ∧
      ∀ i, TPS n (v i) p / n ≤ util (v i) o i := by sorry
