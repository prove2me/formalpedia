-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_count_HW
-- name    : Formalism.CountingSumsFrames.count_HW
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:22.37118+00:00
-- url     : https://prove2.me/theorems/d2246e28-2837-4118-8ce7-9a7591be9ba4
-- title:
--   Counting Sums Frames: count HW
-- statement:
--   The Counting Sums Frames construction uses the count HW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1390-L1478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1390-L1478

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

theorem Formalism.CountingSumsFrames.count_HW [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (S : Finset (Fin r → ℤ)) (hS : ∀ x ∈ Pol p r (Lz L j0), ∀ μ ∉ S, (GA p L j0).comp μ x = 0)
    (e : (Fin r → ℤ) → MvPolynomial (Fin N × Fin r) ℚ_[p])
    (he : ∀ μ, e μ ∈ GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M)
    (he0 : ∀ μ, GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M ≠ ⊥ → e μ ≠ 0) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) =
      ∑ μ ∈ S, Module.finrank ℚ_[p] (GlX.HWs (GA p L j0) μ ⊓ Cset p L j0 J M : Submodule ℚ_[p] _) *
        Module.finrank ℚ_[p] (YYs p L j0 J M (e μ)) := by sorry
