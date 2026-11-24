-- Prove2me | Theorems.Thm_FairSelling_lemma11_TPS_strict
-- name    : FairSelling.lemma11_TPS_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:36:19.638735+00:00
-- url     : https://prove2.me/theorems/ca2e3c89-0712-49d0-9dd2-6be708ea4acd
-- title:
--   Fair Selling: lemma11 TPS strict
-- statement:
--   **Lemma 11 for the truncated proportional share** (strict form).  If for every `ε > 0` some
--   valid outcome is `(ρ − ε)`-`TPS` and `ε-SEFXs`, then some valid outcome is `ρ`-`TPS` and
--   `SEFX`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L431-L437
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L431-L437

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.lemma11_TPS_strict (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFXs v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
