-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_mul
-- name    : Formalism.CountingSumsFrames.TO.ext_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:09.813211+00:00
-- url     : https://prove2.me/theorems/2ee577a8-2b37-486f-97a1-68c6bb325fa4
-- title:
--   TO: ext mul
-- statement:
--   The TO construction uses the ext mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L566-L579
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L566-L579

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
open MvPolynomial Finset
variable {K : Type} [Field K] {σ : Type} [DecidableEq σ] (fs : σ → Prop) [DecidablePred fs]

theorem Formalism.CountingSumsFrames.TO.ext_mul (φ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K) {g q : MvPolynomial σ K} (hg : IsF fs g)
    (hq : IsL fs q) : ext fs φ (g * q) = φ g * q := by sorry
