-- Prove2me | Theorems.Thm_D1Bound5_pellCFPrefixCheck_pairs
-- name    : D1Bound5.pellCFPrefixCheck_pairs
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:32:15.773993+00:00
-- url     : https://prove2.me/theorems/0097017f-08b6-4933-b319-2b1cd46a989b
-- title:
--   Pell CFPrefix Check pairs
-- statement:
--   Auxiliary result `pellCFPrefixCheck_pairs` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/PellCFPrefixCheck.lean, lines 213-272, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellCFPrefixCheck_Definitions
import Definitions.Def_D1Bound5_PellConvergentCompleteness_Definitions

section
namespace D1Bound5













































theorem _root_.D1Bound5.pellCFPrefixCheck_pairs {d a0 : ℤ} {N : ℕ}
    (h : pellCFPrefixCheck d a0 N = true) :
    ∀ i ≤ N, pellConvergentPair (Real.sqrt (d : ℝ)) i =
      ((pellCFAt d a0 (pellCFInit a0) i).p,
       (pellCFAt d a0 (pellCFInit a0) i).q) := by sorry





end D1Bound5
end
