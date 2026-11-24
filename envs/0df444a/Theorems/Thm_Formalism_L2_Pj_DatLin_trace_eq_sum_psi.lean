-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_trace_eq_sum_psi
-- name    : Formalism.L2.Pj.DatLin.trace_eq_sum_psi
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:24.924178+00:00
-- url     : https://prove2.me/theorems/382363b0-38b2-4ecf-b321-cf79f93a4707
-- title:
--   Dat Lin: trace eq sum psi
-- statement:
--   The Dat Lin construction uses the trace eq sum psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SumEmbeddingsEq.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SumEmbeddingsEq.lean#L16-L36

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SumEmbeddingsEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open NumberField ComplexConjugate Classical
variable {E : Type} [Field E] [NumberField E]

theorem Formalism.L2.Pj.DatLin.trace_eq_sum_psi (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) (z : E) :
    ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ ∈ Ψ, 2 * (τ z).re := by sorry
