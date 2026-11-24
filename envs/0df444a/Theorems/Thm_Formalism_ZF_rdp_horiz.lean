-- Prove2me | Theorems.Thm_Formalism_ZF_rdp_horiz
-- name    : Formalism.ZF.rdp_horiz
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:40:58.990283+00:00
-- url     : https://prove2.me/theorems/96f7e4e7-3876-4646-9ce3-7fff13e7e611
-- title:
--   ZF: rdp horiz
-- statement:
--   The ZF construction uses the rdp horiz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L36-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L36-L55

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_LFunctionBounds_LFunctionBoundsProofs_RectResidue
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RectDoublePole
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

theorem Formalism.ZF.rdp_horiz (a p : ℂ) (y x0 x1 : ℝ) (hy : y ≠ p.im) :
    ∫ x in x0..x1, a / ((x : ℂ) + y * I - p) ^ 2 =
      (-a * ((x1 : ℂ) + y * I - p)⁻¹) - (-a * ((x0 : ℂ) + y * I - p)⁻¹) := by sorry
