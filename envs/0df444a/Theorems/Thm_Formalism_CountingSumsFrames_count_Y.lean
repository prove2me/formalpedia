-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_count_Y
-- name    : Formalism.CountingSumsFrames.count_Y
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:26.876433+00:00
-- url     : https://prove2.me/theorems/589c927c-b5bc-4cfc-a58b-0dd918e1d9a4
-- title:
--   Counting Sums Frames: count Y
-- statement:
--   The Counting Sums Frames construction uses the count Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1228-L1317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1228-L1317

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

theorem Formalism.CountingSumsFrames.count_Y [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhP : ∀ i, h i ∈ Pol p r (Lz L j0))
    (hli : LinearIndependent ℚ_[p] h)
    (hsp : ∀ μ v, v ∈ Pol p r (Lz L j0) → (GA p L j0).IsHW μ v → v ∈ Submodule.span ℚ_[p] (Set.range h))
    (hspC : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (h '' {i | h i ∈ Cset p L j0 J M})) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) = ∑ i, Module.finrank ℚ_[p] (YYs p L j0 J M (h i)) ∧
    (∀ i, h i ∉ Cset p L j0 J M → YYs p L j0 J M (h i) = ⊥) ∧
    (∀ i j, h i ∈ Cset p L j0 J M → h j ∈ Cset p L j0 J M → la i = la j →
      Module.finrank ℚ_[p] (YYs p L j0 J M (h i)) ≤ Module.finrank ℚ_[p] (YYs p L j0 J M (h j))) := by sorry
