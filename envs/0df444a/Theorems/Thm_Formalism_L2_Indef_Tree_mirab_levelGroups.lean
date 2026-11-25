-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_mirab_levelGroups
-- name    : Formalism.L2.Indef.Tree.mirab_levelGroups
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:52:04.773885+00:00
-- url     : https://prove2.me/theorems/efd3a686-9647-4b3e-b93d-d01bdcc44c7a
-- title:
--   Tree: mirab level Groups
-- statement:
--   The Tree construction uses the mirab level Groups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONLeaves.lean#L372-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONLeaves.lean#L372-L374

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ExampleSatisfiesConditionsAtFive
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharIdem
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IndexUBound
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_MirabIndex
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IsMackeyPiUpperUnipotentProdCharacter
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnipVal
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_ONLeaves
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain CategoryTheory
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.Indef.Tree.mirab_levelGroups {ι : Type} (kf : ι → Type) [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] (n : ℕ) :
    IsLevelGroups kf n (fun v => mirabSub (kf v) n) (fun v => uniSub (kf v) n) := by sorry
