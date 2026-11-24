-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_sum_re_cmType
-- name    : Formalism.L2.Pj.FundamentalDomainD5.sum_re_cmType
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:29.125554+00:00
-- url     : https://prove2.me/theorems/ce6035f9-79d7-420a-b518-bfb741730c2f
-- title:
--   Fundamental Domain D5: sum re cm Type
-- statement:
--   The Fundamental Domain D5 construction uses the sum re cm Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinrankCmType.lean#L49-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinrankCmType.lean#L49-L64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_FinrankCmType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.FundamentalDomainD5
open NumberField Matrix
open scoped ComplexConjugate

theorem Formalism.L2.Pj.FundamentalDomainD5.sum_re_cmType {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) (z : K) :
    ∑ i, (σ i z).re = (1 / 2 : ℝ) * ((Algebra.trace ℚ K z : ℚ) : ℝ) := by sorry
