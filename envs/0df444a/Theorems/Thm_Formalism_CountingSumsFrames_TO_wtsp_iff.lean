-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_wtsp_iff
-- name    : Formalism.CountingSumsFrames.TO.wtsp_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:32.678516+00:00
-- url     : https://prove2.me/theorems/e1b41a03-b2ca-44ce-a9a0-0123b45384a0
-- title:
--   TO: wtsp iff
-- statement:
--   The TO construction uses the wtsp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2170-L2179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L2170-L2179

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
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.CountingSumsFrames.TO.wtsp_iff {M : ℕ} (L : Letters M) (j : ℕ) (la : Fin r → ℤ) (x : MvPolynomial (Fin M × Fin r) ℚ_[p]) :
    x ∈ WtSpC p L j univ la ↔ IsWeightedHomogeneous (wv L j) x la := by sorry
