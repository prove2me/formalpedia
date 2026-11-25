-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_covol_oneT
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.covol_oneT
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:24.062057+00:00
-- url     : https://prove2.me/theorems/df82002b-cc35-5e9a-a437-1a7657454f1b
-- title:
--   Split Embedding: covol one T
-- statement:
--   The Split Embedding construction uses the covol one T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/EmbSInjective.lean#L28-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/EmbSInjective.lean#L28-L85

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_BoxFundT
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_SwapMp
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_MeasurablePhiInv
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_EmbSInjective
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

theorem Formalism.L2.SG.NGCut.SplitEmbedding.covol_oneT (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ)
    (B : ∀ _ : P, (P → ι → ℂ) → (P → ι → ℂ) → (ι → ℂ))
    (hBm : ∀ p, Measurable (fun z : (P → ι → ℂ) × (P → ι → ℂ) => B p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ι → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y')
    (hB0 : ∀ p (x : P → ι → ℂ), B p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (τ : ∀ _ : P, (P → ι → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : P → ι → ℂ), (∀ q, h q < h p → x q = x' q) → τ p x = τ p x')
    (hinv : ∀ γ : P → ι → ℂ, (∀ p, γ p - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : P → ι → ℂ,
      (∀ p, γ' p - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧ ∀ g, mlaw B γ' (mlaw B γ g) = g ∧ mlaw B γ (mlaw B γ' g) = g)
    (Kset : Set (P → ι → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ g, ∃! γ : P → ι → ℂ, (∀ p, γ p - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧ mlaw B γ g ∈ Kset) :
    (Measure.pi fun _ : P => Measure.pi fun _ : ι => ENNReal.ofReal c • (volume : Measure ℂ)) Kset =
      ∏ p, ENNReal.ofReal (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) := by sorry
