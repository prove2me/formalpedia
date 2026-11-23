-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_subst_psubst
-- name    : Formalism.MainNotions.J.subst_psubst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:48.561918+00:00
-- url     : https://prove2.me/theorems/5b774f7a-2345-40f1-8a72-15bc9821372a
-- title:
--   J: subst psubst
-- statement:
--   The J construction uses the subst psubst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L75-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L75-L81

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

theorem Formalism.MainNotions.J.subst_psubst {c : ι → MvPowerSeries κ R} (hc : HasSubst c) {f : MvPowerSeries ι R}
    (hf : constantCoeff f = 0) (a : PowerSeries R) :
    subst c (PowerSeries.subst f a) = PowerSeries.subst (subst c f) a := by sorry
