-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_dg_X
-- name    : Formalism.MainNotions.J.dg_X
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:55.279348+00:00
-- url     : https://prove2.me/theorems/1aa29483-cba1-492d-bc6c-8a47f9646f77
-- title:
--   J: dg X
-- statement:
--   The J construction uses the dg X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L107-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L107-L118

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
variable {ι κ : Type} {R S : Type} [CommRing R] [CommRing S]

theorem Formalism.MainNotions.J.dg_X (i : ι) : (diagS (PowerSeries.X : PowerSeries R) i : MvPowerSeries ι R) = X i := by sorry
