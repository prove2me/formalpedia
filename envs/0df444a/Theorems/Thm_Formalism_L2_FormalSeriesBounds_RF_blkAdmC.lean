-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_blkAdmC
-- name    : Formalism.L2.FormalSeriesBounds.RF.blkAdmC
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:40.562677+00:00
-- url     : https://prove2.me/theorems/471682e8-9113-40b9-8489-a96b748ed571
-- title:
--   RF: blk Adm C
-- statement:
--   The RF construction uses the blk Adm C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L190-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L190-L211

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
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
variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (I o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)

theorem Formalism.L2.FormalSeriesBounds.RF.blkAdmC (hA : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (X o).rkF 0 s) : BlockAdmissibleSelfConjugate X F gaC := by sorry
