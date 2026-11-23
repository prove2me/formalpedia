-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ThinSetIntegral_twist_is_primitive_character
-- name    : Formalism.HermitianLattices.ThinSetIntegral.twist_is_primitive_character
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:24.109472+00:00
-- url     : https://prove2.me/theorems/4dc30ee3-dcdb-49f3-9c34-44f253bb3026
-- title:
--   Thin Set Integral: twist is primitive character
-- statement:
--   The Thin Set Integral construction uses the twist is primitive character property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/TwistIsPrimitiveCharacter.lean#L87-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/TwistIsPrimitiveCharacter.lean#L87-L105

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TwistIsPrimitiveCharacter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirichletCharacter
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ThinSetIntegral

theorem Formalism.HermitianLattices.ThinSetIntegral.twist_is_primitive_character : Formalism.HermitianLattices.ZeroFreeRegionGL2.TwPrimitive := by sorry
