-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_mem_smul_top_self_iff
-- name    : Formalism.L2.LamCM.mem_smul_top_self_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:58.504082+00:00
-- url     : https://prove2.me/theorems/da73a0ce-c805-4ab8-8646-beb5aff60fd3
-- title:
--   Lam CM: mem smul top self iff
-- statement:
--   The Lam CM construction uses the mem smul top self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ExistsMonicIrreducibleCardGt.lean#L59-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/ExistsMonicIrreducibleCardGt.lean#L59-L61

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsMonicIrreducibleCardGt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open Polynomial IsLocalRing

theorem Formalism.L2.LamCM.mem_smul_top_self_iff {R : Type} [CommRing R] (J : Ideal R) (y : R) :
    y ∈ J • (⊤ : Submodule R R) ↔ y ∈ J := by sorry
