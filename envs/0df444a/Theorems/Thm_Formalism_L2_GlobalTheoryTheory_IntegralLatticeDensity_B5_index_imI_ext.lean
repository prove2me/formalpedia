-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_index_imI_ext
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_imI_ext
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:56.124155+00:00
-- url     : https://prove2.me/theorems/6350edfe-95ea-4820-8e09-8b48971f5d08
-- title:
--   B5: index im I ext
-- statement:
--   The B5 construction uses the index im I ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/MapMulLeftDenSpanImageEqMapNum.lean#L96-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/MapMulLeftDenSpanImageEqMapNum.lean#L96-L113

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_imI_ext {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (s : F)
    (hs : s ∈ Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) :
    ((((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))).toAddSubgroup).index : ℕ) : ℚ) ^
        Module.finrank ℚ E * (FractionalIdeal.absNorm J : ℚ) ^ Module.finrank ℚ F =
      |Algebra.norm ℚ s| ^ Module.finrank ℚ E := by sorry
