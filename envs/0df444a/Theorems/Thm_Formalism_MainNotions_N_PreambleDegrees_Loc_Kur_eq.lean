-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_Kur_eq
-- name    : Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:05:09.855671+00:00
-- url     : https://prove2.me/theorems/4e5d63f1-f421-49a4-9aa5-db343249cb02
-- title:
--   Loc: Kur eq
-- statement:
--   The Loc construction uses the Kur eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L87-L95

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_ProdOneSubPrimitiveRoots
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_Kur_eq

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

theorem Formalism.MainNotions.N.PreambleDegrees.Loc.Kur_eq : LocalClassField.MaximalUnramifiedExtension l (Q0 l) = MaximalUnramifiedExtension l := by sorry
