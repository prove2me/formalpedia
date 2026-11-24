-- Prove2me | Theorems.Thm_Formalism_SLP_P_norm_det_gram_of_decomp
-- name    : Formalism.SLP.P.norm_det_gram_of_decomp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:00.33999+00:00
-- url     : https://prove2.me/theorems/654f9328-2e19-4496-9e4f-091f9968b94e
-- title:
--   P: norm det gram of decomp
-- statement:
--   The P construction uses the norm det gram of decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SesquilinearDeterminantHolds.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HyperbolicPlaceProducts/SubgroupIndexCounts/SesquilinearDeterminantHolds.lean#L74-L79

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset ComplexConjugate
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]

theorem Formalism.SLP.P.norm_det_gram_of_decomp {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m : ℕ}
    (e : Fin m → V) (he : Orthonormal ℂ e) (A : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → V)
    (hu : ∀ i, u i = ∑ k, A i k • e k) :
    ‖(Matrix.gram ℂ u).det‖ = ‖A.det‖ ^ 2 := by sorry
