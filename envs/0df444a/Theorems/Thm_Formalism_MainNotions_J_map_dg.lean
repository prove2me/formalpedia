-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_map_dg
-- name    : Formalism.MainNotions.J.map_dg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:57:20.216826+00:00
-- url     : https://prove2.me/theorems/caa7961f-683e-4f42-b292-5b5003280fbc
-- title:
--   J: map dg
-- statement:
--   The J construction uses the map dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L98-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L98-L105

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

theorem Formalism.MainNotions.J.map_dg (h : R →+* S) (a : PowerSeries R) (i : ι) :
    map h (diagS a i : MvPowerSeries ι R) = diagS (PowerSeries.map h a) i := by sorry
