-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_fractional_ideal_span_top
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.fractional_ideal_span_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:00:14.936819+00:00
-- url     : https://prove2.me/theorems/03a6ba40-7f82-4cb4-884b-f8c2688b088b
-- title:
--   B5: fractional ideal span top
-- statement:
--   The B5 construction uses the fractional ideal span top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/FractionalIdealDualFamily.lean#L60-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/FractionalIdealDualFamily.lean#L60-L79

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.fractional_ideal_span_top (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) :
    Submodule.span K ((I : Submodule (𝓞 E) E) : Set E) = ⊤ := by sorry
