-- Prove2me | Theorems.Thm_Csg_unif2_mem
-- name    : Csg.unif2_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T21:54:47.222361+00:00
-- url     : https://prove2.me/theorems/431a4d4d-254a-4f38-a602-c55050ed9b9e
-- title:
--   Csg: unif2 mem
-- statement:
--   The Csg construction uses the unif2 mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L46-L47
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatchingPennies.lean#L46-L47

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
set_option autoImplicit true
open Csg

theorem Csg.unif2_mem : unif2 ∈ stdSimplex ℝ (Fin 2) := by sorry
