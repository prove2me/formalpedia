-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RowTiePSplit_exists_sep
-- name    : Formalism.L2.FormalSeriesBounds.RowTiePSplit.exists_sep
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:50.099808+00:00
-- url     : https://prove2.me/theorems/874af1aa-f554-5e81-a54a-35d5e77e94b6
-- title:
--   Row Tie PSplit: exists sep
-- statement:
--   The Row Tie PSplit construction uses the exists sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L23-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePSplitLA.lean#L23-L50

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
variable {K : Type} [Field K] [CharZero K]

theorem Formalism.L2.FormalSeriesBounds.RowTiePSplit.exists_sep {O : Type} [CommRing O] {ι : Type} [Fintype ι] (em : ι → (O →+* K))
    (hem : Function.Injective em) : ∃ x0 : O, ∀ c c', c ≠ c' → em c x0 ≠ em c' x0 := by sorry
