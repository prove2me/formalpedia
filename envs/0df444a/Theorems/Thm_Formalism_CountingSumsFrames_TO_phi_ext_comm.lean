-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_phi_ext_comm
-- name    : Formalism.CountingSumsFrames.TO.phi_ext_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:57.803699+00:00
-- url     : https://prove2.me/theorems/1932eda3-478c-41df-8e94-79abcc04a918
-- title:
--   TO: phi ext comm
-- statement:
--   The TO construction uses the phi ext comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1589-L1604
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L1589-L1604

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

theorem Formalism.CountingSumsFrames.TO.phi_ext_comm (j : Fin T.t) (hij : i < j)
    (φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hφ : ∀ x, IsF (fsj N r (T.pos i + 1 + 1)) (φ x)) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    ext (fsj N r (T.pos i + 1 + 1)) φ (T.phi p L j x) = T.phi p L j (ext (fsj N r (T.pos i + 1 + 1)) φ x) := by sorry
