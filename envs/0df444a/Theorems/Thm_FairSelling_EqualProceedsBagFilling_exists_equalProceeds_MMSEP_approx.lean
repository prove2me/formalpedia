-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_exists_equalProceeds_MMSEP_approx
-- name    : FairSelling.EqualProceedsBagFilling.exists_equalProceeds_MMSEP_approx
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T03:36:18.139957+00:00
-- url     : https://prove2.me/theorems/fce1d5f1-0f72-4c22-a277-6b1378dcad1b
-- title:
--   Equal Proceeds Bag Filling: exists equal Proceeds MMSEP approx
-- statement:
--   A fortiori, every agent gets at least `(1/n)` of her *equal-proceeds* maximin share; by
--   Example 4 this factor `1/n` cannot be improved.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L529-L537
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L529-L537

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

theorem FairSelling.EqualProceedsBagFilling.exists_equalProceeds_MMSEP_approx (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      ∀ i, MMSEP n (v i) p / n ≤ util (v i) o i := by sorry
