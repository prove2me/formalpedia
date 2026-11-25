-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_valBlocks_fin
-- name    : Formalism.L2.FormalSeriesBounds.RF.valBlocks_fin
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:32:35.852492+00:00
-- url     : https://prove2.me/theorems/969cc0d1-379f-4390-a3d6-532551c5e0bb
-- title:
--   RF: val Blocks fin
-- statement:
--   The RF construction uses the val Blocks fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValBlocksChart.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/ValBlocksChart.lean#L20-L24

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ValBlocksChart
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  {X : ∀ o, RowData C V d (I o) (J o)} {n : ℕ}

theorem Formalism.L2.FormalSeriesBounds.RF.valBlocks_fin {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν)
    (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ) (hM : BlockMembership X n F FFimg Z ga)
    (hdich : ∀ o ∈ Z, (X o).Alt ∨ ∀ a, (X o).big 0 a) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (X o).rkF g a) : ValBlocks X F Z n ga ν := by sorry
