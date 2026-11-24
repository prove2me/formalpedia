-- Prove2me | Theorems.Thm_Formalism_ZF_zetaPrimeSum_nonneg_and_le
-- name    : Formalism.ZF.zetaPrimeSum_nonneg_and_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:40:47.619181+00:00
-- url     : https://prove2.me/theorems/83d6ef99-707d-4102-b430-32c659d86655
-- title:
--   ZF: zeta Prime Sum nonneg and le
-- statement:
--   The ZF construction uses the zeta Prime Sum nonneg and le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/AbsZetaPrimeSumErrorLeOfOneLe.lean#L10-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/AbsZetaPrimeSumErrorLeOfOneLe.lean#L10-L36

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_AbsZetaPrimeSumErrorLeOfOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZF
open ArithmeticFunction

theorem Formalism.ZF.zetaPrimeSum_nonneg_and_le (y : ℝ) (hy : 1 ≤ y) :
    0 ≤ Formalism.Sz y ∧ Formalism.Sz y ≤ y * y * Real.log y := by sorry
