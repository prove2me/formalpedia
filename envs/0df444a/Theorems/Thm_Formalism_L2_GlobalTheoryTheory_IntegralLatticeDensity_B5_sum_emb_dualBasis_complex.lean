-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_B5_sum_emb_dualBasis_complex
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.sum_emb_dualBasis_complex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:49:56.264059+00:00
-- url     : https://prove2.me/theorems/5cd74c21-0c3b-469a-b26f-09711ba8c3b7
-- title:
--   B5: sum emb dual Basis complex
-- statement:
--   The B5 construction uses the sum emb dual Basis complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/SumEmbDualBasisComplex.lean#L42-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/CubicFields/DifferentIdeal/SumEmbDualBasisComplex.lean#L42-L68

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_LineR
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_CubicFields_DifferentIdeal_SumEmbDualBasisComplex
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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.sum_emb_dualBasis_complex (K E : Type) [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
    (φ₀ : K →+* ℂ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (emb : ι → E →+* ℂ) (hinj : Function.Injective emb)
    (hres : ∀ i (y : K), emb i (algebraMap K E y) = φ₀ y)
    (hcard : Fintype.card ι = Module.finrank K E) {κ : Type} [Fintype κ] [DecidableEq κ] (e : Module.Basis κ K E)
    (i k : ι) :
    ∑ j, emb i (e j) * emb k ((Algebra.traceForm K E).dualBasis (traceForm_nondegenerate K E) e j) =
      if i = k then 1 else 0 := by sorry
