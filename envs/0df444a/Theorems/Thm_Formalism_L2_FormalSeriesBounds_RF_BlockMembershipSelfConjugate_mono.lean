-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_BlockMembershipSelfConjugate_mono
-- name    : Formalism.L2.FormalSeriesBounds.RF.BlockMembershipSelfConjugate.mono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:23:08.539771+00:00
-- url     : https://prove2.me/theorems/7ff3be8e-a7e9-560a-a248-936f8861f339
-- title:
--   Block Membership Self Conjugate: mono
-- statement:
--   The Block Membership Self Conjugate construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjCharts.lean#L83-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjCharts.lean#L83-L87

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_GramMatrixMulRight
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjCharts
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_mono
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.RF.BlockMembershipSelfConjugate.mono {C : Type} [Field C] {V : VF C} {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type}
    [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)] {X : ∀ o, RowData C V 2 (I o) (J o)} {n : ℕ} {F : ∀ o, Flag (X o)}
    {FF FF' : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {gaC : Orb → ZMod 2 → ℕ → ℕ}
    (h : BlockMembershipSelfConjugate X n F FF gaC) (hs : FF ⊆ FF') : BlockMembershipSelfConjugate X n F FF' gaC := by sorry
