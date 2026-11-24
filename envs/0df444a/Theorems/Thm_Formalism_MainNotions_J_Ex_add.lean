-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_Ex_add
-- name    : Formalism.MainNotions.J.Ex_add
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:40.656287+00:00
-- url     : https://prove2.me/theorems/93c9ef46-28bb-4d90-acd8-c1bb1ee63067
-- title:
--   J: Ex add
-- statement:
--   The J construction uses the Ex add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L313-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L313-L323

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_AdmissibleParameterJoins_GandSo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.J
open MvPowerSeries
variable {ι κ : Type} {K K' : Type} [Field K] [CharZero K] [Field K'] [CharZero K']

theorem Formalism.MainNotions.J.Ex_add {f g : MvPowerSeries ι K} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    Ex (f + g) = Ex f * Ex g := by sorry
