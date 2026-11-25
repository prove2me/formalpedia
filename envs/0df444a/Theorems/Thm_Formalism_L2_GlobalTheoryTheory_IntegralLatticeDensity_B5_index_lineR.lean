-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_index_lineR
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_lineR
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:45:39.814376+00:00
-- url     : https://prove2.me/theorems/299b9e0e-1478-4cc8-9cbf-315a958e074d
-- title:
--   B5: index line R
-- statement:
--   The B5 construction uses the index line R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/CoeIdealDifferentNeZero.lean#L62-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/CoeIdealDifferentNeZero.lean#L62-L78

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_FractionalIdealDualFamily
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LiftMOneExt
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_MapMulLeftDenSpanImageEqMapNum
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_CoeIdealDifferentNeZero
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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.index_lineR (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (M : IntermediateField ℚ ℂ) [NumberField M] (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) (hM : ∀ i y, emb i y ∈ M) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hI : I ≠ 0) (i : ι) (s : M) (hs0 : s ≠ 0)
    (hs : s ∈ lineR M emb I i) :
    ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (lineR M emb I i).toAddSubgroup).index : ℕ) : ℝ) ^ Module.finrank ℚ E *
      ((FractionalIdeal.absNorm (I * ((differentIdeal (𝓞 K) (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) : ℚ) : ℝ) ^
        Module.finrank ℚ M =
      |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ Module.finrank ℚ E := by sorry
