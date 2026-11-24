-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_count_le
-- name    : Formalism.CountingSumsFrames.TO.count_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:16.264742+00:00
-- url     : https://prove2.me/theorems/7fcbe1a3-226b-4228-8176-330c9340f6b6
-- title:
--   TO: count le
-- statement:
--   The TO construction uses the count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2745-L2826
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2745-L2826

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi)
  {ι : Type} [Fintype ι] [DecidableEq ι] (h : ι → MvPolynomial (Fin N × Fin r) ℚ_[p]) (la : ι → Fin r → ℤ)
  (hh : ∀ i, (GA p L j0).IsHW (la i) (h i)) (hhC : ∀ i, h i ∈ Cset p L j0 J M)
  (hli : LinearIndependent ℚ_[p] h) (hsp : Cset p (r := r) L j0 J M ≤ ⨆ i, (GA p L j0).gS {h i})
include hPi hh hhC hli hsp

theorem Formalism.CountingSumsFrames.TO.count_le (bad : ι → Prop) [DecidablePred bad]
    (ϖ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hϖ : IsEqC L j0 J M ϖ) (hgood : ∀ i, ¬ bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = x)
    (hbad : ∀ i, bad i → ∀ x ∈ (GA p L j0).gS {h i}, ϖ x = 0) :
    Module.finrank ℚ_[p] (Y p (r := r) L J M) -
      Module.finrank ℚ_[p] ((Y p L J M ⊓ LinearMap.ker (bigOp L j0 Pi ϖ - LinearMap.id) :
        Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))) ≤
      ∑ i ∈ univ.filter bad, Module.finrank ℚ_[p] (YYs L j0 J M (h i)) := by sorry
