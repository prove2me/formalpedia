-- Prove2me | Theorems.Thm_FairSelling_lemma11_TPS
-- name    : FairSelling.lemma11_TPS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:36:23.496531+00:00
-- url     : https://prove2.me/theorems/33f0aede-c95b-4d35-9df6-14433433e694
-- title:
--   Fair Selling: lemma11 TPS
-- statement:
--   **Lemma 11 for the truncated proportional share.**  If for every `ε > 0` some valid outcome
--   is `(ρ − ε)`-`TPS` and `ε-SEFX`, then some valid outcome is `ρ`-`TPS` and `SEFX`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L421-L426
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L421-L426

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.lemma11_TPS (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * TPS n (v i) p ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, rho * TPS n (v i) p ≤ util (v i) o i) ∧ SEFX v p o := by sorry
