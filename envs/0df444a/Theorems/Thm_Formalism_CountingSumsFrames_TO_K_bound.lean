-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_K_bound
-- name    : Formalism.CountingSumsFrames.TO.K_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:56.357348+00:00
-- url     : https://prove2.me/theorems/4ea26d55-29fc-4fc0-819d-3399b25f6559
-- title:
--   TO: K bound
-- statement:
--   The TO construction uses the K bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2984-L3017
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2984-L3017

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

theorem Formalism.CountingSumsFrames.TO.K_bound (N r a j0 : ℕ) (κ : ℝ) (hr : 2 ≤ r) (hj0 : j0 ≤ N)
    (hκ : ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ) :
    ((⌈κ / (N + 2)⌉₊ * j0 + 2 * ⌈κ / (N + 2)⌉₊ : ℕ) : ℝ) ≤ 3 * κ := by sorry
