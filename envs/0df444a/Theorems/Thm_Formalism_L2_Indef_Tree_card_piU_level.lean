-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_card_piU_level
-- name    : Formalism.L2.Indef.Tree.card_piU_level
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T17:50:40.667654+00:00
-- url     : https://prove2.me/theorems/c1b4653a-b8e8-5bf9-89ff-2ca07f750234
-- title:
--   Tree: card pi U level
-- statement:
--   The Tree construction uses the card pi U level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONLeaves.lean#L186-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/ONLeaves.lean#L186-L207

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
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {c : OnConst}
variable {ι : Type} [Fintype ι] [DecidableEq ι] {kf : ι → Type} [∀ v, Field (kf v)] [∀ v, Fintype (kf v)] {n : ℕ}
variable {Pm : ∀ v, Subgroup (GL (Fin (n + 1)) (kf v))} {Uv : ∀ v, Subgroup (Pm v)}

theorem Formalism.L2.Indef.Tree.card_piU_level (hG : IsLevelGroups kf n Pm Uv) (g1 g2 fN : ℕ) (h12 : g1 ≠ g2)
    (hor : ∀ v, Fintype.card (kf v) = g1 ∨ Fintype.card (kf v) = g2)
    (hc1 : (Finset.univ.filter fun v => Fintype.card (kf v) = g1).card = fN)
    (hc2 : (Finset.univ.filter fun v => Fintype.card (kf v) = g2).card = fN) :
    Nat.card (Subgroup.pi Set.univ Uv) = g1 ^ ((n + 1) * n / 2 * fN) * g2 ^ ((n + 1) * n / 2 * fN) := by sorry
