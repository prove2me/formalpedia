-- Prove2me | Theorems.Thm_FairSelling_lemma11_utility
-- name    : FairSelling.lemma11_utility
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:38:52.150815+00:00
-- url     : https://prove2.me/theorems/d959b5e6-3294-43e1-bce5-678ed8db838b
-- title:
--   Fair Selling: lemma11 utility
-- statement:
--   **Lemma 11 (corrected: utility form).**  If for every `ε > 0` there is a valid outcome that
--   guarantees every agent `i` at least `(ρ − ε)·sᵢ` and is `ε-SEFX` in the sense of Definition 8,
--   then there is a valid outcome that guarantees every agent `i` at least `ρ·sᵢ` and is `SEFXu`
--   (the utility form of `SEFX`, i.e. `EFXM`; for valid outcomes this is equivalent to the corrected
--   `SEFX`, see `SEFX_iff_SEFXu`).
--
--   For the literal reading of Definition 4.2/8.2 the statement is false; see
--   `RequestProject.LemmaElevenCounterexample`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L124-L209
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L124-L209

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.lemma11_utility (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFX v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFXu v p o := by sorry
