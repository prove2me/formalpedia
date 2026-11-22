-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_runs_of_cover
-- name    : DeciSigma1.Holes.Tail.exists_runs_of_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:03.425618+00:00
-- url     : https://prove2.me/theorems/e8db2362-24ae-416f-9f6a-1cbafdcc6a70
-- title:
--   Tail: exists runs of cover
-- statement:
--   Periodic factors to designated runs: a factor of length `≥ 2D` lies in a maximal piece of
--   period dividing its period; a shorter one is charged by its length.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L102-L147
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RunCovers.lean#L102-L147

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RunCovers
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Holes.Periodic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.exists_runs_of_cover (U : Fin k → List α) (i : Fin k) {D : ℕ} :
    ∀ fs : List PeriodicFactor, (∀ f ∈ fs, f.Valid (U i) D) →
    ∃ rs : Finset (RunSpec k), rs.card ≤ fs.length ∧
        (∀ r ∈ rs, r.coordinate = i ∧ IsBoundedRun U D r) ∧
      ∃ X : Finset ℕ, X.card ≤ fs.length * (2 * D) ∧
        ∀ p, Covers fs p → RunCovers rs i p ∨ p ∈ X
  := by sorry
