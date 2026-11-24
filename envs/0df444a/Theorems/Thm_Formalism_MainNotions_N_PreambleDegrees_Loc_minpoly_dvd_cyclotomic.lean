-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_minpoly_dvd_cyclotomic
-- name    : Formalism.MainNotions.N.PreambleDegrees.Loc.minpoly_dvd_cyclotomic
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:03:41.616308+00:00
-- url     : https://prove2.me/theorems/fa710a32-f308-4a76-8664-23ced3994325
-- title:
--   Loc: minpoly dvd cyclotomic
-- statement:
--   The Loc construction uses the minpoly dvd cyclotomic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L164-L168

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
variable {F : IntermediateField ℚ_[l] (Om l)}

theorem Formalism.MainNotions.N.PreambleDegrees.Loc.minpoly_dvd_cyclotomic {k : ℕ} {z : Om l} (hz : IsPrimitiveRoot z (l ^ k)) :
    minpoly F z ∣ cyclotomic (l ^ k) F := by sorry
