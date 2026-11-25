-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_snd_injective_fin_one
-- name    : Formalism.L2.FormalSeriesBounds.snd_injective_fin_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:37:28.029482+00:00
-- url     : https://prove2.me/theorems/e2f7861b-688c-41a5-b543-2effd9137347
-- title:
--   Formal Series Bounds: snd injective fin one
-- statement:
--   The Formal Series Bounds construction uses the snd injective fin one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L44-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieCartFB.lean#L44-L44

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffAlongCvCongr
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCartFB
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
open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {C : Type} [Field C]
variable {dd : ℕ}

theorem Formalism.L2.FormalSeriesBounds.snd_injective_fin_one : Function.Injective (fun p : Fin 1 × Fin dd => p.2) := by sorry
