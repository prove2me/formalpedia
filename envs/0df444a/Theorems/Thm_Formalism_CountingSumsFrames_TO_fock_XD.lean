-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_XD
-- name    : Formalism.CountingSumsFrames.TO.fock_XD
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:23.585805+00:00
-- url     : https://prove2.me/theorems/0eb9baf9-0b48-4705-abef-66b98b5950fa
-- title:
--   TO: fock XD
-- statement:
--   The TO construction uses the fock XD property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1249-L1251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1249-L1251

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

theorem Formalism.CountingSumsFrames.TO.fock_XD {σ : Type} [Fintype σ] [DecidableEq σ] (u v : σ) (x y : MvPolynomial σ ℚ_[p]) :
    fock p (X u * pderiv v x) y = fock p x (X v * pderiv u y) := by sorry
