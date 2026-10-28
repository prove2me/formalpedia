-- Prove2me | Theorems.Thm_D1Bound5_pellConvergentPair_recurrence
-- name    : D1Bound5.pellConvergentPair_recurrence
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:45:56.510945+00:00
-- url     : https://prove2.me/theorems/f60197b6-aa4f-4f9d-af59-35b101cf3559
-- title:
--   Pell Convergent Pair recurrence
-- statement:
--   The forward recurrence that connects the short executable certificate to the independently proved real-convergent completeness theorem.
-- source:
--   D1Bound5/PellCFPrefixCheck.lean, lines 116-139, SHA-256 a5468d17d5b8fd8febaae9f486b606a6148827a88a3b76dca5782d036662adba. Project: https://github.com/tomislav-math/d1-bound5-lean

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




































theorem _root_.D1Bound5.pellConvergentPair_recurrence (x : ℝ) (n : ℕ) :
    pellConvergentPair x (n+2) =
      (⌊pellRealTail x (n+2)⌋ * (pellConvergentPair x (n+1)).1 +
          (pellConvergentPair x n).1,
       ⌊pellRealTail x (n+2)⌋ * (pellConvergentPair x (n+1)).2 +
          (pellConvergentPair x n).2) := by sorry















end D1Bound5
end
