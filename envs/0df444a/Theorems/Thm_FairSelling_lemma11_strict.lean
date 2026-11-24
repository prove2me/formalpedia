-- Prove2me | Theorems.Thm_FairSelling_lemma11_strict
-- name    : FairSelling.lemma11_strict
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:54:04.23849+00:00
-- url     : https://prove2.me/theorems/69463447-80a2-4877-9f0c-f828092f26c2
-- title:
--   Fair Selling: lemma11 strict
-- statement:
--   **Lemma 11 (corrected: strict form).**  If for every `ε > 0` there is a valid outcome that
--   guarantees every agent `i` at least `(ρ − ε)·sᵢ` and is `ε-SEFXs`, then there is a valid outcome
--   that guarantees every agent `i` at least `ρ·sᵢ` and is `SEFXs`, hence in particular `SEFX` in the
--   sense of Definition 4.2 of the manuscript.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L335-L406
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L335-L406

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.lemma11_strict (v : Fin n → G → ℝ) (p : G → ℝ) (rho : ℝ) (s : Fin n → ℝ)
    (H : ∀ eps > (0 : ℝ), ∃ o : Outcome G n, o.Valid p ∧
      (∀ i, (rho - eps) * s i ≤ util (v i) o i) ∧ epsSEFXs v p eps o) :
    ∃ o : Outcome G n, o.Valid p ∧ (∀ i, rho * s i ≤ util (v i) o i) ∧ SEFXs v p o := by sorry
