-- Prove2me | Theorems.Thm_Formalism_MainNotions_S_Gauge_Cd_hilbert_schmidt_eq_re_trace
-- name    : Formalism.MainNotions.S.Gauge.Cd.hilbert_schmidt_eq_re_trace
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:10:44.22546+00:00
-- url     : https://prove2.me/theorems/7902e3a5-9d70-4e25-9c65-281db63b2ff7
-- title:
--   Cd: hilbert schmidt eq re trace
-- statement:
--   The Cd construction uses the hilbert schmidt eq re trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/TraceMulConjTransposeReal.lean#L45-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/TraceMulConjTransposeReal.lean#L45-L49

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

theorem Formalism.MainNotions.S.Gauge.Cd.hilbert_schmidt_eq_re_trace (Z : Matrix ι ι ℂ) : hs2 Z = (Matrix.trace (Z * Zᴴ)).re := by sorry
