-- Prove2me | Theorems.Thm_Formalism_CountingSumsFrames_TO_psi_mem
-- name    : Formalism.CountingSumsFrames.TO.psi_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:40:05.504324+00:00
-- url     : https://prove2.me/theorems/1bb679b2-087f-42ac-932b-bd25eb77b939
-- title:
--   TO: psi mem
-- statement:
--   The TO construction uses the psi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L988-L989
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/MultinomialDepth/TieOps.lean#L988-L989

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

theorem Formalism.CountingSumsFrames.TO.psi_mem (L : Letters N) (j0 : ℕ) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : psi p L j0 x ∈ Pol p r (Lz L j0) := by sorry
