-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_Ex_neg_mul
-- name    : Formalism.MainNotions.J.Ex_neg_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:47.600501+00:00
-- url     : https://prove2.me/theorems/b78676d9-d0d3-491b-a65f-a7a9320869d1
-- title:
--   J: Ex neg mul
-- statement:
--   The J construction uses the Ex neg mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L325-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L325-L328

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

theorem Formalism.MainNotions.J.Ex_neg_mul {f : MvPowerSeries ι K} (hf : constantCoeff f = 0) : Ex (-f) * Ex f = 1 := by sorry
