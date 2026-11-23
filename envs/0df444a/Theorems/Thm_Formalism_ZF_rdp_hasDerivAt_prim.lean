-- Prove2me | Theorems.Thm_Formalism_ZF_rdp_hasDerivAt_prim
-- name    : Formalism.ZF.rdp_hasDerivAt_prim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:10.569493+00:00
-- url     : https://prove2.me/theorems/fd084094-567d-4b4f-b1a2-0ce624717708
-- title:
--   ZF: rdp has Deriv At prim
-- statement:
--   The ZF construction uses the rdp has Deriv At prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RectDoublePole.lean#L29-L34

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

theorem Formalism.ZF.rdp_hasDerivAt_prim (a p w : ℂ) (hw : w ≠ p) :
    HasDerivAt (fun z => -a * (z - p)⁻¹) (a / (w - p) ^ 2) w := by sorry
