-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_exists_plift
-- name    : Formalism.MainNotions.J.exists_plift
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:27.931334+00:00
-- url     : https://prove2.me/theorems/41b3a198-ffd3-5973-8b02-bd7b5539626c
-- title:
--   J: exists plift
-- statement:
--   The J construction uses the exists plift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L396-L401
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L396-L401

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
variable {ι κ : Type} {K : Type} [Field K]

theorem Formalism.MainNotions.J.exists_plift (O : Subring K) (a : PowerSeries K) (h : ∀ n, PowerSeries.coeff n a ∈ O) :
    ∃ a' : PowerSeries O, PowerSeries.map O.subtype a' = a := by sorry
