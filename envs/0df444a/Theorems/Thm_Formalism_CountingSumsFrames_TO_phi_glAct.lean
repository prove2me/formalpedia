-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_phi_glAct
-- name    : Formalism.CountingSumsFrames.TO.phi_glAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:40.121003+00:00
-- url     : https://prove2.me/theorems/c8edb8e3-2b51-4c0f-91d6-f9c049a73d57
-- title:
--   TO: phi gl Act
-- statement:
--   The TO construction uses the phi gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1531-L1587
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1531-L1587

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

theorem Formalism.CountingSumsFrames.TO.phi_glAct (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    T.phi p L i (glAct p L (T.pos i + 1 + 1) c d x) = glAct p L (T.pos i + 1 + 1) c d (T.phi p L i x) := by sorry
