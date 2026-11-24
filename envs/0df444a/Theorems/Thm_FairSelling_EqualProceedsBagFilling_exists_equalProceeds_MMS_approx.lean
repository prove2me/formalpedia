-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_exists_equalProceeds_MMS_approx
-- name    : FairSelling.EqualProceedsBagFilling.exists_equalProceeds_MMS_approx
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:26:45.048807+00:00
-- url     : https://prove2.me/theorems/663ae958-2e4e-42e1-804f-d8d59fe28c06
-- title:
--   Equal Proceeds Bag Filling: exists equal Proceeds MMS approx
-- statement:
--   Since `MMSᵢ ≤ TPSᵢ` (Lemma 1), the same outcome guarantees `(1/n)·MMSᵢ` — where `MMSᵢ` is
--   the *unconstrained* maximin share — to every agent.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L517-L525
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L517-L525

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

theorem FairSelling.EqualProceedsBagFilling.exists_equalProceeds_MMS_approx (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      ∀ i, MMS n (v i) p / n ≤ util (v i) o i := by sorry
