-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_fractional_ideal_dual_family
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.fractional_ideal_dual_family
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:11.994822+00:00
-- url     : https://prove2.me/theorems/790d9a90-3222-4337-b16f-c8c71732a806
-- title:
--   B5: fractional ideal dual family
-- statement:
--   The B5 construction uses the fractional ideal dual family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/FractionalIdealDualFamily.lean#L81-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/FractionalIdealDualFamily.lean#L81-L108

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.fractional_ideal_dual_family (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    ∃ (n : ℕ) (g : Fin n → E) (f : Fin n → ((I : Submodule (𝓞 E) E).restrictScalars (𝓞 K) →ₗ[𝓞 K] 𝓞 K)),
      (∀ j, g j ∈ (I : Submodule (𝓞 E) E)) ∧
      ∀ y : (I : Submodule (𝓞 E) E).restrictScalars (𝓞 K), (y : E) = ∑ j, f j y • g j := by sorry
