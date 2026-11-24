-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_exists_pi
-- name    : Formalism.CountingSumsFrames.exists_pi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:18.523597+00:00
-- url     : https://prove2.me/theorems/30669c93-bd41-44a5-a5cd-0f77f11f43d0
-- title:
--   Counting Sums Frames: exists pi
-- statement:
--   The Counting Sums Frames construction uses the exists pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1042-L1086
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/MonoCount.lean#L1042-L1086

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

theorem Formalism.CountingSumsFrames.exists_pi [NeZero r] (L : Letters N) (j0 : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
    (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhP : ∀ i, h i ∈ Pol p r (Lz L j0))
    (hli : LinearIndependent ℚ_[p] h)
    (hsp : ∀ μ v, v ∈ Pol p r (Lz L j0) → (GA p L j0).IsHW μ v → v ∈ Submodule.span ℚ_[p] (Set.range h))
    (hspC : ∀ μ v, v ∈ Cset p L j0 J M → (GA p L j0).IsHW μ v →
      v ∈ Submodule.span ℚ_[p] (h '' {i | h i ∈ Cset p L j0 J M})) :
    ∃ π : ι → MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      (∀ i x, π i x ∈ (GA p L j0).gS {h i}) ∧ (∀ i, ∀ x ∈ (GA p L j0).gS {h i}, π i x = x) ∧
      (∀ i j, j ≠ i → ∀ x ∈ (GA p L j0).gS {h j}, π i x = 0) ∧
      (∀ x ∈ Pol p r (Lz L j0), ∑ i, π i x = x) ∧
      (∀ i, ∀ x ∈ Cset p L j0 J M, π i x ∈ Cset p L j0 J M) ∧
      (∀ i, h i ∉ Cset p L j0 J M → ∀ x ∈ Cset p L j0 J M, π i x = 0) ∧
      (∀ i, ∀ x ∈ Pol p r (Lz L j0), ∀ c d, π i (glAct p L j0 c d x) = glAct p L j0 c d (π i x)) ∧
      (∀ i, ∀ x ∈ Pol p r (Lz L j0), ∀ ν, π i ((GA p L j0).comp ν x) = (GA p L j0).comp ν (π i x)) := by sorry
