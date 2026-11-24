-- Prove2me | Theorems.Thm_Formalism_ZF_rdp_rectInt_double
-- name    : Formalism.ZF.rdp_rectInt_double
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:03.927053+00:00
-- url     : https://prove2.me/theorems/66b50819-42e2-4879-8238-5a2b4d2cf951
-- title:
--   ZF: rdp rect Int double
-- statement:
--   The ZF construction uses the rdp rect Int double property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L80-L86

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

theorem Formalism.ZF.rdp_rectInt_double (a p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => a / (w - p) ^ 2) x0 x1 y0 y1 = 0 := by sorry
