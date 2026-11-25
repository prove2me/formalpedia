-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_natDegree_minpoly_eq
-- name    : Formalism.MainNotions.N.PreambleDegrees.Loc.natDegree_minpoly_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:54:20.229391+00:00
-- url     : https://prove2.me/theorems/57719740-c4b4-48a3-9a6b-b7043f3deec7
-- title:
--   Loc: nat Degree minpoly eq
-- statement:
--   The Loc construction uses the nat Degree minpoly eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L170-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L170-L245

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

theorem Formalism.MainNotions.N.PreambleDegrees.Loc.natDegree_minpoly_eq (hF : F ≤ MaximalUnramifiedExtension l) {k : ℕ} (hk : 0 < k) {z : Om l}
    (hz : IsPrimitiveRoot z (l ^ k)) : (minpoly F z).natDegree = (l ^ k).totient := by sorry
