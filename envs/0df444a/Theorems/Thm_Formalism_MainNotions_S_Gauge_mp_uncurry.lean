-- Prove2me | Theorems.Thm_Formalism_MainNotions_S_Gauge_mp_uncurry
-- name    : Formalism.MainNotions.S.Gauge.mp_uncurry
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:10:40.25997+00:00
-- url     : https://prove2.me/theorems/b72de710-5cda-4571-9a03-fd8b61a14b1b
-- title:
--   Gauge: mp uncurry
-- statement:
--   The Gauge construction uses the mp uncurry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/MpUncurry.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/MpUncurry.lean#L9-L19

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_MpUncurry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Gauge

theorem Formalism.MainNotions.S.Gauge.mp_uncurry (κ : Type*) [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry κ (Fin 2) ℝ).symm volume volume := by sorry
