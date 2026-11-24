-- Prove2me | Theorems.Thm_Formalism_MainNotions_S_Gauge_Cd_trace_mul_conjTranspose_real
-- name    : Formalism.MainNotions.S.Gauge.Cd.trace_mul_conjTranspose_real
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:12:33.137091+00:00
-- url     : https://prove2.me/theorems/902ae2ec-2bf7-415a-8df2-996ec32ea567
-- title:
--   Cd: trace mul conj Transpose real
-- statement:
--   The Cd construction uses the trace mul conj Transpose real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/TraceMulConjTransposeReal.lean#L23-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/TraceMulConjTransposeReal.lean#L23-L41

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

theorem Formalism.MainNotions.S.Gauge.Cd.trace_mul_conjTranspose_real {a b : Matrix ι ι ℂ} (ha : a ∈ Formalism.BasicNotions.lieU P Q) (hb : b ∈ Formalism.BasicNotions.lieU P Q) :
    star (Matrix.trace (a * bᴴ)) = Matrix.trace (a * bᴴ) := by sorry
