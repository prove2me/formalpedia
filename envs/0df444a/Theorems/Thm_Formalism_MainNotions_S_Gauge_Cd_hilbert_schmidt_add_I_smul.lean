-- Prove2me | Theorems.Thm_Formalism_MainNotions_S_Gauge_Cd_hilbert_schmidt_add_I_smul
-- name    : Formalism.MainNotions.S.Gauge.Cd.hilbert_schmidt_add_I_smul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:51:21.00473+00:00
-- url     : https://prove2.me/theorems/94336763-9925-40b7-9d42-b96148866bc3
-- title:
--   Cd: hilbert schmidt add I smul
-- statement:
--   The Cd construction uses the hilbert schmidt add I smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/TraceMulConjTransposeReal.lean#L51-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/ClosedLocalOrbits/GaugeLatticeShifts/TraceMulConjTransposeReal.lean#L51-L67

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

theorem Formalism.MainNotions.S.Gauge.Cd.hilbert_schmidt_add_I_smul {a b : Matrix ι ι ℂ} (ha : a ∈ Formalism.BasicNotions.lieU P Q) (hb : b ∈ Formalism.BasicNotions.lieU P Q) :
    hs2 (a + Complex.I • b) = hs2 a + hs2 b := by sorry
