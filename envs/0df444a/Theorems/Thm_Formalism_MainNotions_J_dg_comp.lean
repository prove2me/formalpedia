-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_dg_comp
-- name    : Formalism.MainNotions.J.dg_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T09:56:48.250852+00:00
-- url     : https://prove2.me/theorems/f67998e7-55e9-4de6-8fc7-b6d887acf79d
-- title:
--   J: dg comp
-- statement:
--   The J construction uses the dg comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L83-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L83-L96

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

theorem Formalism.MainNotions.J.dg_comp {a b : PowerSeries R} (hb : PowerSeries.constantCoeff b = 0) (i : ι) :
    subst (diagS b) (diagS a i : MvPowerSeries ι R) = diagS (PowerSeries.subst b a) i := by sorry
