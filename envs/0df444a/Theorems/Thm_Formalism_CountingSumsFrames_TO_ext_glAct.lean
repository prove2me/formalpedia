-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_ext_glAct
-- name    : Formalism.CountingSumsFrames.TO.ext_glAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:35:15.498795+00:00
-- url     : https://prove2.me/theorems/abc55b6d-2d93-4587-a101-a22d8755c56c
-- title:
--   TO: ext gl Act
-- statement:
--   The TO construction uses the ext gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L877-L889
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L877-L889

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

theorem Formalism.CountingSumsFrames.TO.ext_glAct (L : Letters N) {j0 J : ℕ} (hJ : j0 ≤ J) (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ1 : ∀ c d x, φ (glAct p L j0 c d x) = glAct p L j0 c d (φ x)) (hφF : ∀ x, IsF (fsj N r j0) (φ x))
    (c d : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r j0) φ (glAct p L J c d x) = glAct p L J c d (ext (fsj N r j0) φ x) := by sorry
