-- Prove2me | Theorems.Thm_Formalism_ZF_rdp_rectInt_add
-- name    : Formalism.ZF.rdp_rectInt_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:41:01.356835+00:00
-- url     : https://prove2.me/theorems/68fa219c-205d-4ad7-af5c-dc3f35afb029
-- title:
--   ZF: rdp rect Int add
-- statement:
--   The ZF construction uses the rdp rect Int add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L13-L27

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

theorem Formalism.ZF.rdp_rectInt_add (f1 f2 : ℂ → ℂ) (x0 x1 y0 y1 : ℝ)
    (hB1 : IntervalIntegrable (fun x : ℝ => f1 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hB2 : IntervalIntegrable (fun x : ℝ => f2 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hT1 : IntervalIntegrable (fun x : ℝ => f1 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hT2 : IntervalIntegrable (fun x : ℝ => f2 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hR1 : IntervalIntegrable (fun y : ℝ => f1 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hR2 : IntervalIntegrable (fun y : ℝ => f2 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hL1 : IntervalIntegrable (fun y : ℝ => f1 (x0 + y * I)) MeasureTheory.volume y0 y1)
    (hL2 : IntervalIntegrable (fun y : ℝ => f2 (x0 + y * I)) MeasureTheory.volume y0 y1) :
    rectInt (fun w => f1 w + f2 w) x0 x1 y0 y1 =
      rectInt f1 x0 x1 y0 y1 + rectInt f2 x0 x1 y0 y1 := by sorry
