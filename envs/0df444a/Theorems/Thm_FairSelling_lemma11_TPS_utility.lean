-- Prove2me | Theorems.Thm_FairSelling_lemma11_TPS_utility
-- name    : FairSelling.lemma11_TPS_utility
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:36:14.239364+00:00
-- url     : https://prove2.me/theorems/b501e2f4-0b83-4812-a79d-cc96f7be91f7
-- title:
--   Fair Selling: lemma11 TPS utility
-- statement:
--   **Lemma 11 for the truncated proportional share** (utility form).  If for every `ε > 0` some
--   valid outcome is `(ρ − ε)`-`TPS` and `ε-SEFX`, then some valid outcome is `ρ`-`TPS` and `SEFXu`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L412-L417
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L412-L417

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.lemma11_TPS_utility (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFXu v p o := by sorry
