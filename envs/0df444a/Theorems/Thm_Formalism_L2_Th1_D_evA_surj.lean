-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_evA_surj
-- name    : Formalism.L2.Th1.D.evA_surj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:53:42.899799+00:00
-- url     : https://prove2.me/theorems/f9f4dbb2-df3f-4d6a-b765-f52e8dfa09f4
-- title:
--   D: ev A surj
-- statement:
--   The D construction uses the ev A surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusOnRingA.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusOnRingA.lean#L108-L116

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_RingAFacts
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_FrobeniusOnRingA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
variable (l : ℕ) [Fact l.Prime]

theorem Formalism.L2.Th1.D.evA_surj : Function.Surjective (evA l 1) := by sorry
