-- Prove2me | Theorems.Thm_Formalism_MainNotions_N_PreambleDegrees_Loc_norm_Kur_zpow
-- name    : Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:08:51.304393+00:00
-- url     : https://prove2.me/theorems/af832231-1bf7-4158-bb9d-12f4bfc23394
-- title:
--   Loc: norm Kur zpow
-- statement:
--   The Loc construction uses the norm Kur zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L104-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/ProdOneSubPrimitiveRoots.lean#L104-L114

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

theorem Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow {x : Om l} (hx : x ∈ MaximalUnramifiedExtension l) (h0 : x ≠ 0) : ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by sorry
