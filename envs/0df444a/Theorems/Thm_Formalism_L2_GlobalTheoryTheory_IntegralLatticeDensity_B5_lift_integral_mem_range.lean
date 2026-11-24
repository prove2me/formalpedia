-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_lift_integral_mem_range
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.lift_integral_mem_range
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:21.440183+00:00
-- url     : https://prove2.me/theorems/49c16f77-96d0-4be2-9350-eef223f51db8
-- title:
--   B5: lift integral mem range
-- statement:
--   The B5 construction uses the lift integral mem range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/FractionalIdealDualFamily.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/FractionalIdealDualFamily.lean#L15-L22

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_FractionalIdealDualFamily
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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.lift_integral_mem_range (M : IntermediateField ℚ ℂ) [NumberField M] {z : ℂ} (hz : z ∈ M)
    (hi : IsIntegral ℤ z) : liftM M z ∈ (algebraMap (𝓞 M) M).range := by sorry
