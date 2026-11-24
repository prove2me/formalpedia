-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_index_imI
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_imI
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:12.268801+00:00
-- url     : https://prove2.me/theorems/fd3ed9b2-5a6f-4476-849d-b9b0f0d1b1b2
-- title:
--   B5: index im I
-- statement:
--   The B5 construction uses the index im I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/MapMulLeftDenSpanImageEqMapNum.lean#L115-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/MapMulLeftDenSpanImageEqMapNum.lean#L115-L136

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_imI {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (s : M) (hs0 : s ≠ 0)
    (hs : s ∈ imI M σ J) :
    ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (imI M σ J).toAddSubgroup).index : ℕ) : ℝ) ^ Module.finrank ℚ E *
      ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ Module.finrank ℚ M =
      |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ Module.finrank ℚ E := by sorry
