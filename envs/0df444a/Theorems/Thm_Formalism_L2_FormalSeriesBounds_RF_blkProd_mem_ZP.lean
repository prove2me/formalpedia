-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_blkProd_mem_ZP
-- name    : Formalism.L2.FormalSeriesBounds.RF.blkProd_mem_ZP
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:45:42.543395+00:00
-- url     : https://prove2.me/theorems/235ca3a1-35e8-4451-a76d-0e611c9822bb
-- title:
--   RF: blk Prod mem ZP
-- statement:
--   The RF construction uses the blk Prod mem ZP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L61-L66

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
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
open Formalism.IncomingBounds Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.RF.blkProd_mem_ZP {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (n : ℕ) (L : Orb → List (GlobalTheory d × ℝ))
    (pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n) : blkProd X F n L pl ∈ ZP C _ := by sorry
