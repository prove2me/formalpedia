-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_sum_embeddings_eq
-- name    : Formalism.L2.Pj.DatLin.sum_embeddings_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:32.636966+00:00
-- url     : https://prove2.me/theorems/c0bf08e1-eed2-48a6-b972-15ba938ae320
-- title:
--   Dat Lin: sum embeddings eq
-- statement:
--   The Dat Lin construction uses the sum embeddings eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SumEmbeddingsEq.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/SumEmbeddingsEq.lean#L11-L14

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

theorem Formalism.L2.Pj.DatLin.sum_embeddings_eq (z : E) :
    (((Algebra.trace ℚ E z : ℚ) : ℂ)) = ∑ σ : E →+* ℂ, σ z := by sorry
