-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_smith_bases
-- name    : Formalism.CountingSumsFrames.TO.smith_bases
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:51.741795+00:00
-- url     : https://prove2.me/theorems/b36fe773-c200-4adb-b799-8f2d1d8a3876
-- title:
--   TO: smith bases
-- statement:
--   The TO construction uses the smith bases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2896-L2955
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2896-L2955

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
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.TO.smith_bases {σ : Type} (nb : ℕ) (f : Fin nb → MvPolynomial σ ℚ_[p])
    (Lat : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (hli : LinearIndependent ℤ_[p] f) (hsp : Submodule.span ℤ_[p] (Set.range f) = Lat)
    (B : MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial σ ℚ_[p] →ₗ[ℚ_[p]] ℚ_[p])
    (U V : Matrix (Fin nb) (Fin nb) ℚ_[p]) (dg : Fin nb → ℚ_[p])
    (hU : ∀ x y, ‖U x y‖ ≤ 1) (hV : ∀ x y, ‖V x y‖ ≤ 1) (hUd : ‖U.det‖ = 1) (hVd : ‖V.det‖ = 1)
    (hfac : (Matrix.of fun x y => B (f x) (f y)) = U * Matrix.diagonal dg * V) :
    ∃ f' f'' : Fin nb → MvPolynomial σ ℚ_[p], (∀ a, f' a ∈ Lat) ∧ (∀ a, f'' a ∈ Lat) ∧
      LinearIndependent ℚ_[p] f' ∧ Lat ≤ Submodule.span ℤ_[p] (Set.range f') ∧
      ∀ a b, B (f' a) (f'' b) = if a = b then dg a else 0 := by sorry
