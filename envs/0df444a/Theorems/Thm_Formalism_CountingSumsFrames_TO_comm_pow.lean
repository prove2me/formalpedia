-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_comm_pow
-- name    : Formalism.CountingSumsFrames.TO.comm_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:09.011292+00:00
-- url     : https://prove2.me/theorems/7b3d6f62-052a-4002-a4f4-44c43731b4fd
-- title:
--   TO: comm pow
-- statement:
--   The TO construction uses the comm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2054-L2062
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2054-L2062

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

theorem Formalism.CountingSumsFrames.TO.comm_pow (L : Letters N) (j0 : ℕ)
    (Tm : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hcomm : ∀ c d x, Tm (glAct p L j0 c d x) = glAct p L j0 c d (Tm x)) (c d : Fin r) (k : ℕ) :
    ∀ x, Tm (((glAct p L j0 c d) ^ k) x) = ((glAct p L j0 c d) ^ k) (Tm x) := by sorry
