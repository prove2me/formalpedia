-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_exists_fd
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.exists_fd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:32:59.256512+00:00
-- url     : https://prove2.me/theorems/a8a46d4b-ee27-5573-84df-4a1b50dd31c0
-- title:
--   Split Embedding: exists fd
-- statement:
--   The Split Embedding construction uses the exists fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L105-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L105-L185

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CosetFd
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MeasurablePhiInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.SplitEmbedding

theorem Formalism.L2.SG.NGCut.SplitEmbedding.exists_fd (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : AddSubgroup K)
    (hΛ : ∀ a ∈ Λ, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
    (hk0 : Λ.relIndex (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) ≠ 0)
    (s : ℂ) (hs : s ≠ 0) :
    ∃ F : Set (ι → ℂ), MeasurableSet F ∧ ∀ v, ∃! a : Λ, (fun i => s * φ i a) + v ∈ F := by sorry
