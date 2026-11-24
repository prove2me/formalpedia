-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_Ex_biv
-- name    : Formalism.MainNotions.J.Ex_biv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:56:43.421466+00:00
-- url     : https://prove2.me/theorems/1b2e2f77-d78d-4a6d-aafe-037ebf4c0dac
-- title:
--   J: Ex biv
-- statement:
--   The J construction uses the Ex biv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L262-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L262-L311

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

theorem Formalism.MainNotions.J.Ex_biv : Ex (X 0 + X 1 : MvPowerSeries (Fin 2) K) = Ex (X 0) * Ex (X 1) := by sorry
