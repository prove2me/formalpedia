-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_add_eq_add_iff_disj
-- name    : Formalism.CountingSumsFrames.TO.add_eq_add_iff_disj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:05.38638+00:00
-- url     : https://prove2.me/theorems/dfaa5688-6a23-4463-a59c-997e9d5fac55
-- title:
--   TO: add eq add iff disj
-- statement:
--   The TO construction uses the add eq add iff disj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1280-L1291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1280-L1291

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

theorem Formalism.CountingSumsFrames.TO.add_eq_add_iff_disj (j0 : ℕ) (a b m m' : Fin N × Fin r →₀ ℕ) (ha : ∀ v, a v ≠ 0 → fsj N r j0 v)
    (hb : ∀ v, b v ≠ 0 → fsj N r j0 v) (hm : ∀ v, m v ≠ 0 → ¬ fsj N r j0 v)
    (hm' : ∀ v, m' v ≠ 0 → ¬ fsj N r j0 v) : a + m = b + m' ↔ a = b ∧ m = m' := by sorry
