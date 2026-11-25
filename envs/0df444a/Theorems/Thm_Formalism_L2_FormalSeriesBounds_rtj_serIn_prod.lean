-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_rtj_serIn_prod
-- name    : Formalism.L2.FormalSeriesBounds.rtj_serIn_prod
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:24:49.606867+00:00
-- url     : https://prove2.me/theorems/c53ae0f7-3be0-4997-be28-1556bea5a297
-- title:
--   Formal Series Bounds: rtj ser In prod
-- statement:
--   The Formal Series Bounds construction uses the rtj ser In prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L154-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieJet.lean#L154-L163

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieJet
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.IncomingBounds
variable {K : Type} [Field K] {σ : Type}

theorem Formalism.L2.FormalSeriesBounds.rtj_serIn_prod {ι : Type} (A : Set σ) (s : Finset ι) (F : ι → MvPowerSeries σ K)
    (hF : ∀ i ∈ s, rtjSerIn A (F i)) : rtjSerIn A (∏ i ∈ s, F i) := by sorry
