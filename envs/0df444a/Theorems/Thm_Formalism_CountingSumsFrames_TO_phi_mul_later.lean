-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_phi_mul_later
-- name    : Formalism.CountingSumsFrames.TO.phi_mul_later
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:43.561809+00:00
-- url     : https://prove2.me/theorems/ded71ae7-41db-4541-8a9e-cb0205f5c581
-- title:
--   TO: phi mul later
-- statement:
--   The TO construction uses the phi mul later property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1515-L1522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1515-L1522

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
variable (L : Letters N) (T : TieData) (hadm : T.Admissible L) (i : Fin T.t)
include hadm

theorem Formalism.CountingSumsFrames.TO.phi_mul_later (g q : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hq : IsL (fsj N r (T.pos i + 1 + 1)) q) :
    T.phi p L i (g * q) = T.phi p L i g * q := by sorry
