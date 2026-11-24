-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_wh
-- name    : Formalism.CountingSumsFrames.TO.ext_wh
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:09.908135+00:00
-- url     : https://prove2.me/theorems/81f846c9-003c-4217-a5e0-7c7cb1586866
-- title:
--   TO: ext wh
-- statement:
--   The TO construction uses the ext wh property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L907-L928
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L907-L928

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
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.ext_wh (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφw : ∀ ν x, x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν → φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L j0) ν)
    (hφF : ∀ x, IsF (fsj N r j0) (φ x)) (ν : Fin r → ℤ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν) :
    ext (fsj N r j0) φ x ∈ weightedHomogeneousSubmodule ℚ_[p] (wv L J) ν := by sorry
