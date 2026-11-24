-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_map_Ex
-- name    : Formalism.MainNotions.J.map_Ex
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:09.812852+00:00
-- url     : https://prove2.me/theorems/d1c0e6b3-9660-4832-ab15-c63203eae0f1
-- title:
--   J: map Ex
-- statement:
--   The J construction uses the map Ex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L197-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L197-L205

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

theorem Formalism.MainNotions.J.map_Ex (h : K →+* K') {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) :
    map h (Ex f) = Ex (map h f) := by sorry
