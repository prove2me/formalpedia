-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_vw_level
-- name    : Formalism.L2.Indef.Tree.vw_level
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T18:01:15.680602+00:00
-- url     : https://prove2.me/theorems/f2eee150-ed1a-4c43-960e-eec3810639a6
-- title:
--   Tree: vw level
-- statement:
--   The Tree construction uses the vw level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONLeaves.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONLeaves.lean#L18-L21

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

theorem Formalism.L2.Indef.Tree.vw_level (w : HeightOneSpectrum (𝓞 K)) {g1 g2 : ℕ} (h1 : g1.Prime) (h2 : g2.Prime) (h12 : g1 ≠ g2) (a : ℕ) :
    (vw w (((g1 ^ a * g2 ^ a : ℕ)) : K) : ℝ) =
      (ramw w : ℝ) * (if plc w = g1 ∨ plc w = g2 then (a : ℝ) else 0) := by sorry
