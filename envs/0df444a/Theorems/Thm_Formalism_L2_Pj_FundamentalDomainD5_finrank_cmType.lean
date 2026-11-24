-- Prove2me | Theorems.Thm_Formalism_L2_Pj_FundamentalDomainD5_finrank_cmType
-- name    : Formalism.L2.Pj.FundamentalDomainD5.finrank_cmType
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:40.476814+00:00
-- url     : https://prove2.me/theorems/46d13264-29c7-4b02-866c-f9bae6539888
-- title:
--   Fundamental Domain D5: finrank cm Type
-- statement:
--   The Fundamental Domain D5 construction uses the finrank cm Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinrankCmType.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/FinrankCmType.lean#L66-L71

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

theorem Formalism.L2.Pj.FundamentalDomainD5.finrank_cmType {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (σ : ι → K →+* ℂ)
    (hinj : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) :
    Module.finrank ℚ K = 2 * Fintype.card ι := by sorry
