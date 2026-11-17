-- Prove2me | Theorems.Thm_APFPaper5_K2_SplitWorld_defd_iff
-- name    : APFPaper5.K2.SplitWorld.defd_iff
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:55:27.618814+00:00
-- url     : https://prove2.me/theorems/1e125808-c240-4f25-bda1-14a82fac4277
-- title:
--   defd iff
-- statement:
--   Result: defd iff. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem defd_iff (g : Unit) (x : Raw g) (w : WordFrom Frag g) : Defd g x w ↔ runsAt w.2 x
--   ```
--
--   Module context and limits: The supplied one-context model has admission-only score and three pairwise distinct word classes with invisible combination A+B-C. No declared form is verified for this example, and its score is not asserted physical. The sure test is equivalent to the empty word only for trivial values.
--
--   Source scope parameters:
--
--   ```lean
--   universe uV
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_split_world:120; pullbacks v39; source SHA-256 ab8c5d883c4869eacb9234c07f3222c655df1746ff6238076e60f1ea564a8e57']

import Definitions.Def_APFPaper5_K2_split_world_Vocabulary
import Definitions.Def_APFPaper5_K2_ClosedBoundary
import Definitions.Def_APFPaper5_K2_closed_boundary_on_words_Vocabulary
import Theorems.Thm_APFPaper5_K2_readoutEq_append
import Theorems.Thm_APFPaper5_K2_mulClass_assoc
import Theorems.Thm_APFPaper5_K2_oneClass_mul
import Theorems.Thm_APFPaper5_K2_mul_oneClass
import Theorems.Thm_APFPaper5_K2_neverDefined_sandwich
import Theorems.Thm_APFPaper5_K2_readoutEq_of_neverDefined
import Theorems.Thm_APFPaper5_K2_never_class_mul
import Theorems.Thm_APFPaper5_K2_mul_never_class
import Theorems.Thm_APFPaper5_K2_toldApart_of_not_readoutEq
import Theorems.Thm_APFPaper5_K2_not_readoutEq_of_toldApart
import Theorems.Thm_APFPaper5_K2_not_readoutEq_iff_toldApart
import Theorems.Thm_APFPaper5_K2_toldApart_one_is_defined
import Theorems.Thm_APFPaper5_K2_told_apart_by_admitted_word
import Theorems.Thm_APFPaper5_K2_scoreNull_sandwich
import Theorems.Thm_APFPaper5_K2_score_eq_of_readoutEq
import Theorems.Thm_APFPaper5_K2_scoreNull_pair_of_readoutEq
import Theorems.Thm_APFPaper5_K2_admissionScore_of_defd
import Theorems.Thm_APFPaper5_K2_admissionScore_of_not_defd
import Theorems.Thm_APFPaper5_K2_admissionScore_zeroConvention
import Theorems.Thm_APFPaper5_K2_admissionScore_eq_one_iff
import Theorems.Thm_APFPaper5_K2_readoutEq_iff_admissionScore_eq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
open APFPaper1.Continuation

namespace APFPaper5.K2.SplitWorld
end APFPaper5.K2.SplitWorld
open APFPaper5
open APFPaper5.K2
open APFPaper5.K2.SplitWorld
universe uV

theorem APFPaper5.K2.SplitWorld.defd_iff (g : Unit) (x : Raw g) (w : WordFrom Frag g) : Defd g x w ↔ runsAt w.2 x := by sorry
