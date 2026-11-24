-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_prod_one_sub_primitiveRoots
-- name    : Formalism.MainNotions.N.PreambleDegrees.Loc.prod_one_sub_primitiveRoots
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:05:16.406018+00:00
-- url     : https://prove2.me/theorems/82e5444a-f79d-4e9c-a81c-06486104c8a1
-- title:
--   Loc: prod one sub primitive Roots
-- statement:
--   The Loc construction uses the prod one sub primitive Roots property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L121-L126

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

theorem Formalism.MainNotions.N.PreambleDegrees.Loc.prod_one_sub_primitiveRoots {k : ℕ} (hk : 0 < k) :
    ∏ x ∈ primitiveRoots (l ^ k) (Om l), (1 - x) = (l : Om l) := by sorry
