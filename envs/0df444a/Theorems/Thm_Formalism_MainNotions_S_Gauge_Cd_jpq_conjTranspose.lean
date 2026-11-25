-- Prove2me | Theorems.Thm_Formalism_MainNotions_S_Gauge_Cd_jpq_conjTranspose
-- name    : Formalism.MainNotions.S.Gauge.Cd.jpq_conjTranspose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:11.73612+00:00
-- url     : https://prove2.me/theorems/85f18090-535b-4902-8808-d97ca45fc932
-- title:
--   Cd: jpq conj Transpose
-- statement:
--   The Cd construction uses the jpq conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/TraceMulConjTransposeReal.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/TraceMulConjTransposeReal.lean#L18-L21

import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_TraceMulConjTransposeReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Gauge Formalism.MainNotions.S.Gauge.Cd
variable {P Q : ℕ}
local notation "ι" => Fin P ⊕ Fin Q

theorem Formalism.MainNotions.S.Gauge.Cd.jpq_conjTranspose : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by sorry
