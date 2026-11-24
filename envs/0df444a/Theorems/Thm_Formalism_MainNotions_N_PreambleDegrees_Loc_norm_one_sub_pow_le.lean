-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_one_sub_pow_le
-- name    : Formalism.MainNotions.N.PreambleDegrees.Loc.norm_one_sub_pow_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:03:36.278185+00:00
-- url     : https://prove2.me/theorems/e600124f-c7cf-4520-a6bf-85976b5c759b
-- title:
--   Loc: norm one sub pow le
-- statement:
--   The Loc construction uses the norm one sub pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L128-L136

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.PreambleDegrees Formalism.MainNotions.N.PreambleDegrees.Loc
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.DiscreteGroups Polynomial
variable {l : ℕ} [Fact l.Prime]
variable (l)
variable {l}

theorem Formalism.MainNotions.N.PreambleDegrees.Loc.norm_one_sub_pow_le {z : Om l} (hz : ‖z‖ ≤ 1) (a : ℕ) : ‖1 - z ^ a‖ ≤ ‖1 - z‖ := by sorry
