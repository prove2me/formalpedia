-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_freeze_surj
-- name    : Formalism.CountingSumsFrames.freeze_surj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:44.852815+00:00
-- url     : https://prove2.me/theorems/2e52a891-a960-450e-a37c-abd844bc60ff
-- title:
--   Counting Sums Frames: freeze surj
-- statement:
--   The Counting Sums Frames construction uses the freeze surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1488-L1522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1488-L1522

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

theorem Formalism.CountingSumsFrames.freeze_surj (LL : Letters K) (ρ : Fin r) (n : ℕ) (hS : LL.total ≤ n)
    (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hFpol' : F ∈ Pol p r (LL.snoc n))
    (hinv : IsFrozenInv p LL ρ n F) :
    ∃ f ∈ Pol p r LL, freeze p LL ρ n f = F ∧ ∀ m', coeff m' f = coeff (FB.ext n ρ m') F := by sorry
