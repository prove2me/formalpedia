-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_Kur
-- name    : Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:03:37.657555+00:00
-- url     : https://prove2.me/theorems/39a905d2-6507-4c7c-a494-d7f04dd71a87
-- title:
--   Loc: norm Kur
-- statement:
--   The Loc construction uses the norm Kur property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L97-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L97-L102

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

theorem Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) : ∃ a : ℚ_[l], ‖x‖ = ‖a‖ := by sorry
