-- Prove2me | Theorems.Thm_FairSelling_lemma11_TPS_u
-- name    : FairSelling.lemma11_TPS_u
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:30:50.333132+00:00
-- url     : https://prove2.me/theorems/49e3dd6e-d226-45fb-9647-80750fdc7614
-- title:
--   Fair Selling: lemma11 TPS u
-- statement:
--   **Lemma 11 for the truncated proportional share**, with `ε-SEFXu` as input.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L440-L445
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L440-L445

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.lemma11_TPS_u (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFXu v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
