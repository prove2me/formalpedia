-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_mem_vars_blkProdG
-- name    : Formalism.L2.FormalSeriesBounds.RF.mem_vars_blkProdG
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:45:02.642401+00:00
-- url     : https://prove2.me/theorems/44f69b60-1d58-58eb-b0b7-79db7caacd12
-- title:
--   RF: mem vars blk Prod G
-- statement:
--   The RF construction uses the mem vars blk Prod G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCHarm.lean#L86-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCHarm.lean#L86-L109

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCHarm
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
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem Formalism.L2.FormalSeriesBounds.RF.mem_vars_blkProdG {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {Orb : Type} [Fintype Orb]
    {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
    {X : ∀ o, RowData C V d (I o) (J o)} {F : ∀ o, Flag (X o)} {n : ℕ} {L : Orb → List (GlobalTheory d × ℝ)}
    {pl : (Σ o, Σ i : Fin (L o).length, Fin (rowsAt X L o i)) → Fin n} {b : Fin n} {o : Orb} {w : WV (I o)}
    (hx : ((b, ⟨o, w⟩) : Fin n × WVO I) ∈ (blkProd X F n L pl).vars) :
    (b, w) ∈ (prodAll (plAt n pl o) fun i => (blkAt L o i).poly (X o) (F o)).vars := by sorry
