-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_idealCovolC
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.idealCovolC
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:32:53.166119+00:00
-- url     : https://prove2.me/theorems/a952d050-7f7c-5c0b-98d7-db06dbfa858a
-- title:
--   Split Embedding: ideal Covol C
-- statement:
--   The Split Embedding construction uses the ideal Covol C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L207-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/MeasurablePhiInv.lean#L207-L238

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

theorem Formalism.L2.SG.NGCut.SplitEmbedding.idealCovolC (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (I : (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : AddSubgroup K)
    (hΛ : ∀ a ∈ Λ, a ∈ (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : ℕ)
    (hk : Λ.relIndex (((I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k)
    (hk0 : k ≠ 0) (s : ℂ) (hs : s ≠ 0) (F : Set (ι → ℂ)) (hF : MeasurableSet F)
    (hFd : ∀ v, ∃! a : Λ, (fun i => s * φ i a) + v ∈ F) :
    volume F = ENNReal.ofReal ((k : ℝ) * (FractionalIdeal.absNorm (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
      2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s‖ ^ (2 * Fintype.card ι)) := by sorry
