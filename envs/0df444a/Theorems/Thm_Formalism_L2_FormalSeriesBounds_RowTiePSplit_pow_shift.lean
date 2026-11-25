-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_pow_shift
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePSplit.pow_shift
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:10.576389+00:00
-- url     : https://prove2.me/theorems/1ca126e1-331b-4754-8de4-7c969897f008
-- title:
--   Row Tie PSplit: pow shift
-- statement:
--   The Row Tie PSplit construction uses the pow shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L78-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L78-L90

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

theorem Formalism.L2.FormalSeriesBounds.RowTiePSplit.pow_shift (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (k : ℕ) :
    (N + B) ^ k *ᵥ w = (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) ^ k *ᵥ w := by sorry
