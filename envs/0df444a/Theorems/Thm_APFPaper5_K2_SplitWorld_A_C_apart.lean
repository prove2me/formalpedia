-- Prove2me | Theorems.Thm_APFPaper5_K2_SplitWorld_A_C_apart
-- name    : APFPaper5.K2.SplitWorld.A_C_apart
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:53:40.903885+00:00
-- url     : https://prove2.me/theorems/a8cdd2fe-7343-47f6-8d24-d78975f9222a
-- title:
--   A C apart
-- statement:
--   Result: A C apart. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem A_C_apart {Val : Type uV} (value : (g : Unit) → WordFrom Frag g → Raw g → Val) :
--       ¬ ReadoutEq Defd value (word Letter.A) (word Letter.Cc)
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
--   ['Theorems.Thm_APFPaper5_K2_split_world:159; pullbacks v39; source SHA-256 ab8c5d883c4869eacb9234c07f3222c655df1746ff6238076e60f1ea564a8e57']

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




































/-! ### The three words are told apart -/

theorem APFPaper5.K2.SplitWorld.A_C_apart {Val : Type uV} (value : (g : Unit) → WordFrom Frag g → Raw g → Val) :
    ¬ ReadoutEq Defd value (word Letter.A) (word Letter.Cc) := by sorry
