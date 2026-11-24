-- Prove2me | Theorems.Thm_FairSelling_exists_kept_subset
-- name    : FairSelling.exists_kept_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:48:56.388796+00:00
-- url     : https://prove2.me/theorems/d042c713-5186-49ee-906e-a7100eee9ca2
-- title:
--   Fair Selling: exists kept subset
-- statement:
--   Pigeonhole: if the kept bundles of an outcome are pairwise disjoint and, outside of `E`,
--   are contained in a set `R` of fewer goods than there are agents in `T`, then some agent of `T`
--   keeps nothing outside `E`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L36-L60
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceedsExamples.lean#L36-L60

import Mathlib
import Definitions.Def_RequestProject_EqualProceeds
import Definitions.Def_RequestProject_EqualProceedsExamples
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]

theorem FairSelling.exists_kept_subset (o : Outcome G n) (E R : Finset G) (T : Finset (Fin n))
    (hdisj : ∀ j k, j ≠ k → Disjoint (o.kept j) (o.kept k))
    (hsub : ∀ j, o.kept j \ E ⊆ R)
    (hcard : R.card < T.card) :
    ∃ j ∈ T, o.kept j ⊆ E := by sorry
