-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_gamma_zero_exponent_le
-- name    : Formalism.CountingSumsFrames.TO.gamma_zero_exponent_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:43.429294+00:00
-- url     : https://prove2.me/theorems/d373d382-6d50-42a6-8d28-ef2884ae5d36
-- title:
--   TO: gamma zero exponent le
-- statement:
--   The TO construction uses the gamma zero exponent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1669-L1699
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1669-L1699

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
open Formalism.GM Formalism.GM.M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.CountingSumsFrames.TO.gamma_zero_exponent_le (K r a : ℕ) (hr : 1 ≤ r) (κ : ℝ) (hκ : ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ) :
    (K + 2) * (r * Nat.log p (2 * a)) ≤ ⌈κ⌉₊ := by sorry
