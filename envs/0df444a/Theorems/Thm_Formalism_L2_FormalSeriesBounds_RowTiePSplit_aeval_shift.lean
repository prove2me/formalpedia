-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_aeval_shift
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePSplit.aeval_shift
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:30:10.651114+00:00
-- url     : https://prove2.me/theorems/36a24f81-79a7-4ebc-8a15-ea308c7ef46e
-- title:
--   Row Tie PSplit: aeval shift
-- statement:
--   The Row Tie PSplit construction uses the aeval shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L92-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L92-L100

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

theorem Formalism.L2.FormalSeriesBounds.RowTiePSplit.aeval_shift (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (f : K[X]) :
    aeval (N + B) f *ᵥ w = aeval (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) f *ᵥ w := by sorry
