-- Prove2me | Theorems.Thm_Formalism_ZF_abs_zetaPrimeSumError_le_of_one_le
-- name    : Formalism.ZF.abs_zetaPrimeSumError_le_of_one_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:41:00.290973+00:00
-- url     : https://prove2.me/theorems/11025f7e-618a-4b0c-9d61-26aa778d1563
-- title:
--   ZF: abs zeta Prime Sum Error le of one le
-- statement:
--   The ZF construction uses the abs zeta Prime Sum Error le of one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/AbsZetaPrimeSumErrorLeOfOneLe.lean#L38-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/AbsZetaPrimeSumErrorLeOfOneLe.lean#L38-L51

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

theorem Formalism.ZF.abs_zetaPrimeSumError_le_of_one_le (y : ℝ) (hy : 1 ≤ y) :
    |Formalism.Gz y| ≤ y * (y * Real.log y + Real.log y + 2) := by sorry
