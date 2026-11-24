-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_projC
-- name    : Formalism.CountingSumsFrames.TO.projC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:22.893634+00:00
-- url     : https://prove2.me/theorems/2ca1b3c0-c0c9-4d68-82d7-56aa45ef03f9
-- title:
--   TO: proj C
-- statement:
--   The TO construction uses the proj C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1862-L1945
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1862-L1945

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

theorem Formalism.CountingSumsFrames.TO.projC [NeZero r] (L : Letters N) (ρ : Fin r) (e1 j0 : ℕ) (hj0 : j0 ≤ N) (hHP : HypP p L ρ e1) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) :
    ∃ Pi : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p],
      IsProjC L j0 (e1 * j0) J M Pi := by sorry
