-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_one_sub_eq
-- name    : Formalism.MainNotions.N.PreambleDegrees.Loc.norm_one_sub_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:48.2673+00:00
-- url     : https://prove2.me/theorems/7e9abd60-406b-47e4-8ffc-b1bc5450cc24
-- title:
--   Loc: norm one sub eq
-- statement:
--   The Loc construction uses the norm one sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L138-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L138-L149

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

theorem Formalism.MainNotions.N.PreambleDegrees.Loc.norm_one_sub_eq {k : ℕ} {z z' : Om l} (hz : IsPrimitiveRoot z (l ^ k))
    (hz' : IsPrimitiveRoot z' (l ^ k)) : ‖1 - z‖ = ‖1 - z'‖ := by sorry
