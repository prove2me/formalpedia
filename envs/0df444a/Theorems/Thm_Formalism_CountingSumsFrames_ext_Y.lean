-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_ext_Y
-- name    : Formalism.CountingSumsFrames.ext_Y
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:36.916876+00:00
-- url     : https://prove2.me/theorems/b052bce8-6ab5-4412-9de0-2a18b106e118
-- title:
--   Counting Sums Frames: ext Y
-- statement:
--   The Counting Sums Frames construction uses the ext Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L912-L939
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L912-L939

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
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.ext_Y [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ1 : ∀ c d x, φ (glAct p L j0 c d x) = glAct p L j0 c d (φ x))
    (hφw : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν → φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν)
    (hφP : ∀ x, φ x ∈ Pol p r (Lz L j0)) (hφC : ∀ x ∈ Cset p L j0 J M, φ x ∈ Cset p L j0 J M) :
    ∀ x ∈ Y p L J M, ext (fsj N r j0) φ x ∈ Y p L J M := by sorry
