-- Prove2me | Theorems.Thm_Formalism_L2_SG_NGCut_SplitEmbedding_pi_measure_eq_prod_absNorm_mul_sqrt_discr
-- name    : Formalism.L2.SG.NGCut.SplitEmbedding.pi_measure_eq_prod_absNorm_mul_sqrt_discr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:58:15.938155+00:00
-- url     : https://prove2.me/theorems/2ff48f35-4ff4-47d0-b85a-88a7039ad48a
-- title:
--   Split Embedding: pi measure eq prod abs Norm mul sqrt discr
-- statement:
--   The Split Embedding construction uses the pi measure eq prod abs Norm mul sqrt discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CovolOneEqOne.lean#L14-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CovolOneEqOne.lean#L14-L92

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_EmbSInjective
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CovolOneEqOne
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

theorem Formalism.L2.SG.NGCut.SplitEmbedding.pi_measure_eq_prod_absNorm_mul_sqrt_discr (K : Type) [Field K] [NumberField K] [IsEmpty {w : InfinitePlace K // w.IsReal}]
    (ι : Type) [Fintype ι] (φ : ι → (K →+* ℂ)) (σ : ι ≃ {w : InfinitePlace K // w.IsComplex})
    (hφ : ∀ i, φ i = (σ i).1.embedding ∨ φ i = ComplexEmbedding.conjugate (σ i).1.embedding)
    (P : Type) [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBm : ∀ p, Measurable (fun z : (P → ℂ) × (P → ℂ) => BX p z.1 z.2))
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (hB0 : ∀ p (x : P → ℂ), BX p x 0 = 0)
    (c : ℝ) (hc : 0 ≤ c) (I : P → (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ) (Λ : P → AddSubgroup K)
    (hΛ : ∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) (k : P → ℕ)
    (hk : ∀ p, (Λ p).relIndex
      (((I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K).toAddSubgroup) = k p)
    (hk0 : ∀ p, k p ≠ 0) (s : P → ℂ) (hs : ∀ p, s p ≠ 0)
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (hinv : ∀ γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) → ∃ γ' : ι → P → ℂ,
      (∀ p, (fun v => γ' v p) - τ p γ' ∈ (Λ p).map (embS φ (s p))) ∧
        ∀ x, lawX BX γ' (lawX BX γ x) = x ∧ lawX BX γ (lawX BX γ' x) = x)
    (Kset : Set (ι → P → ℂ)) (hK : MeasurableSet Kset)
    (hKd : ∀ x, ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ (Λ p).map (embS φ (s p))) ∧
      lawX BX γ x ∈ Kset) :
    (Measure.pi fun _ : ι => Measure.pi fun _ : P => ENNReal.ofReal c • (volume : Measure ℂ)) Kset =
      ∏ p, ENNReal.ofReal (c ^ Fintype.card ι * k p *
        (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : ℝ) *
        2⁻¹ ^ Fintype.card ι * √|(discr K : ℝ)| * ‖s p‖ ^ (2 * Fintype.card ι)) := by sorry
