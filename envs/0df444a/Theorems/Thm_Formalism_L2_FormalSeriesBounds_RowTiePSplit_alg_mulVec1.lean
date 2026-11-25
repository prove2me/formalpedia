-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_alg_mulVec1
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePSplit.alg_mulVec1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:06.43932+00:00
-- url     : https://prove2.me/theorems/5b33ffe1-55d7-4ffd-aa83-9f0e19590b0c
-- title:
--   Row Tie PSplit: alg mul Vec1
-- statement:
--   The Row Tie PSplit construction uses the alg mul Vec1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L62-L64

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
variable {K : Type} [Field K] {n : ℕ}

theorem Formalism.L2.FormalSeriesBounds.RowTiePSplit.alg_mulVec1 (a : K) (w : Fin n → K) :
    algebraMap K (Matrix (Fin n) (Fin n) K) a *ᵥ w = a • w := by sorry
