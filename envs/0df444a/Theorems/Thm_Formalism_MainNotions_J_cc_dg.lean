-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_cc_dg
-- name    : Formalism.MainNotions.J.cc_dg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:23.852591+00:00
-- url     : https://prove2.me/theorems/8fd1ad4b-065a-4b5f-998a-e0833dc5559f
-- title:
--   J: cc dg
-- statement:
--   The J construction uses the cc dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L47-L50

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

theorem Formalism.MainNotions.J.cc_dg {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) (i : ι) :
    constantCoeff (diagS a i : MvPowerSeries ι R) = 0 := by sorry
