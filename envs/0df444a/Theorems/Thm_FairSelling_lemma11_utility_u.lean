-- Prove2me | Theorems.Thm_FairSelling_lemma11_utility_u
-- name    : FairSelling.lemma11_utility_u
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:53:47.970562+00:00
-- url     : https://prove2.me/theorems/278f4190-2210-4227-963f-5d3d90191853
-- title:
--   Fair Selling: lemma11 utility u
-- statement:
--   **Lemma 11 (utility form), with `ε-SEFXu` as input.**  If for every `ε > 0` there is a valid
--   outcome that guarantees every agent `i` at least `(ρ − ε)·sᵢ` and is `ε-SEFXu`, then there is a
--   valid outcome that guarantees every agent `i` at least `ρ·sᵢ` and is `SEFXu`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L220-L301
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L220-L301

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.lemma11_utility_u (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFXu v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFXu v p o := by sorry
