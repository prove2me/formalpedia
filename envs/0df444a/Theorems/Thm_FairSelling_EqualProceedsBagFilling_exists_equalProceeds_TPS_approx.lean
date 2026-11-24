-- Prove2me | Theorems.Thm_FairSelling_EqualProceedsBagFilling_exists_equalProceeds_TPS_approx
-- name    : FairSelling.EqualProceedsBagFilling.exists_equalProceeds_TPS_approx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:50:32.727959+00:00
-- url     : https://prove2.me/theorems/12878222-6c0c-46b3-9c92-d908ecb84eaf
-- title:
--   Equal Proceeds Bag Filling: exists equal Proceeds TPS approx
-- statement:
--   **Theorem 7 of Appendix H.**  Every instance admits a feasible outcome with *equal
--   proceeds* in which every agent `i` receives at least `(1/n) · TPSᵢ`, where `TPSᵢ` is the
--   truncated proportional share of Definition 3 (with unconstrained proceeds).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L476-L513
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsBagFilling.lean#L476-L513

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

theorem FairSelling.EqualProceedsBagFilling.exists_equalProceeds_TPS_approx (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ o.EqualProceeds p ∧
      ∀ i, TPS n (v i) p / n ≤ util (v i) o i := by sorry
