-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_map_mulLeft_den_span_image_eq_map_num
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.map_mulLeft_den_span_image_eq_map_num
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:36.76739+00:00
-- url     : https://prove2.me/theorems/16b05232-4006-4c89-997a-98185d86c084
-- title:
--   B5: map mul Left den span image eq map num
-- statement:
--   The B5 construction uses the map mul Left den span image eq map num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/MapMulLeftDenSpanImageEqMapNum.lean#L13-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/MapMulLeftDenSpanImageEqMapNum.lean#L13-L42

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_MapMulLeftDenSpanImageEqMapNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
open NumberField Classical
open scoped Pointwise

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.map_mulLeft_den_span_image_eq_map_num {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 F) ((algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E) : 𝓞 F) : F))
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) =
      Submodule.map (Algebra.linearMap (𝓞 F) F) (J.num.map (algebraMap (𝓞 E) (𝓞 F))) := by sorry
