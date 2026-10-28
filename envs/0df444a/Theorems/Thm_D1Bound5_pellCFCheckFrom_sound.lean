-- Prove2me | Theorems.Thm_D1Bound5_pellCFCheckFrom_sound
-- name    : D1Bound5.pellCFCheckFrom_sound
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:34.967992+00:00
-- url     : https://prove2.me/theorems/3a78c996-6644-4839-9051-5b93b826d6f8
-- title:
--   Pell CFCheck From sound
-- statement:
--   Auxiliary result `pellCFCheckFrom_sound` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PellCFPrefixCheck.lean, lines 78-104, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions

section
namespace D1Bound5





























theorem _root_.D1Bound5.pellCFCheckFrom_sound (d a0 : ℤ) (s : PellCFState) (N : ℕ)
    (h : pellCFCheckFrom d a0 s N = true) :
    (∀ i ≤ N, PellCFStateGood a0 (pellCFAt d a0 s i)) ∧
    (∀ i < N, PellCFTransitionGood d a0 (pellCFAt d a0 s i)) := by sorry





















end D1Bound5
end
