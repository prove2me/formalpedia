-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_alg_mulVec
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePSplit.alg_mulVec
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:20:19.006275+00:00
-- url     : https://prove2.me/theorems/65fc856a-2ef1-5b9f-964c-4c2b51ca8953
-- title:
--   Row Tie PSplit: alg mul Vec
-- statement:
--   The Row Tie PSplit construction uses the alg mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L58-L60

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

theorem Formalism.L2.FormalSeriesBounds.RowTiePSplit.alg_mulVec (a : K) (A : Matrix (Fin n) (Fin n) K) (w : Fin n → K) :
    (algebraMap K (Matrix (Fin n) (Fin n) K) a * A) *ᵥ w = a • (A *ᵥ w) := by sorry
