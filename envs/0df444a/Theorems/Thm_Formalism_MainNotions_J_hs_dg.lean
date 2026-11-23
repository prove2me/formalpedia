-- Prove2me | Theorems.Thm_Formalism_MainNotions_J_hs_dg
-- name    : Formalism.MainNotions.J.hs_dg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:19.671185+00:00
-- url     : https://prove2.me/theorems/bef7c933-132d-42fe-9a55-8c745e1d7af8
-- title:
--   J: hs dg
-- statement:
--   The J construction uses the hs dg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L52-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/AdmissibleParameterJoins/GandSo.lean#L52-L67

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

theorem Formalism.MainNotions.J.hs_dg {a : PowerSeries R} (ha : PowerSeries.constantCoeff a = 0) :
    HasSubst (diagS a : ι → MvPowerSeries ι R) := by sorry
