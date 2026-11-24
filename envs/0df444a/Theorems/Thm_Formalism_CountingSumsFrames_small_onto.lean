-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_small_onto
-- name    : Formalism.CountingSumsFrames.small_onto
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:12.855859+00:00
-- url     : https://prove2.me/theorems/96233610-0175-4261-b94a-29e0558d56b9
-- title:
--   Counting Sums Frames: small onto
-- statement:
--   The Counting Sums Frames construction uses the small onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1535-L1573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1535-L1573

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.CountingSumsFrames.small_onto [NeZero r] (LK : Letters K) (ρ : Fin r) (hρ : (ρ : ℕ) = r - 1) (n : ℕ) (hS : LK.total ≤ n)
    {q : ℕ} (J : Fin q → ℕ) (Mt : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ K) (μ : Fin r → ℤ)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hFP : F ∈ Pol p r (LK.snoc n))
    (hFY : ∀ k, F ∈ YCond p (LK.snoc n) (J k) (Mt k))
    (hFw : IsWeightedHomogeneous (wv (LK.snoc n) (K + 1)) F μ)
    (hFr : ∀ a b, a < b → glAct p (LK.snoc n) (K + 1) a b F = 0) :
    ∃ f, f ∈ MMw p LK J Mt ρ (μ + ((n : ℕ) : ℤ) • Pi.single ρ 1) ∧ freeze p LK ρ n f = F := by sorry
