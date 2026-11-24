-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_int_fermat
-- name    : Formalism.L2.Th1.D.int_fermat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:53:07.899619+00:00
-- url     : https://prove2.me/theorems/873a349e-edef-455e-b708-eacda4cd0e3a
-- title:
--   D: int fermat
-- statement:
--   The D construction uses the int fermat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusOnRingA.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/FrobeniusOnRingA.lean#L125-L129

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

theorem Formalism.L2.Th1.D.int_fermat (a : ℤ) : ∃ c : ℤ, a - a ^ l = (l : ℤ) * c := by sorry
