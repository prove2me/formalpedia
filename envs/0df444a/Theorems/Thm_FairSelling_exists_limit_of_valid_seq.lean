-- Prove2me | Theorems.Thm_FairSelling_exists_limit_of_valid_seq
-- name    : FairSelling.exists_limit_of_valid_seq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:39.547804+00:00
-- url     : https://prove2.me/theorems/8dd494fb-1a1a-4dc5-ba0e-61651aa9ee6a
-- title:
--   Fair Selling: exists limit of valid seq
-- statement:
--   **The compactness step of Lemma 11.**  From any sequence of valid outcomes one can extract a
--   subsequence whose class is constant and whose money vectors converge.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L91-L112
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/LemmaEleven.lean#L91-L112

import Mathlib
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
set_option autoImplicit true
open scoped BigOperators
open Filter Topology
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [DecidableEq G]

theorem FairSelling.exists_limit_of_valid_seq {p : G → ℝ} (o : ℕ → Outcome G n)
    (hval : ∀ k, (o k).Valid p) :
    ∃ (S : Finset G) (A : Fin n → Finset G) (P : Fin n → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ (∀ k, (o (φ k)).sold = S) ∧ (∀ k, (o (φ k)).kept = A) ∧
      Tendsto (fun k => (o (φ k)).money) atTop (𝓝 P) := by sorry
