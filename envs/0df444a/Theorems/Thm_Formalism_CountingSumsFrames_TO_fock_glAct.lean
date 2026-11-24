-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_fock_glAct
-- name    : Formalism.CountingSumsFrames.TO.fock_glAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:58.81512+00:00
-- url     : https://prove2.me/theorems/5f614913-1223-4bcf-9a78-39757ddc1278
-- title:
--   TO: fock gl Act
-- statement:
--   The TO construction uses the fock gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1253-L1265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1253-L1265

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

theorem Formalism.CountingSumsFrames.TO.fock_glAct (L : Letters N) (j : ℕ) (c d : Fin r) (x y : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    fock p (glAct p L j c d x) y = fock p x (glAct p L j d c y) := by sorry
