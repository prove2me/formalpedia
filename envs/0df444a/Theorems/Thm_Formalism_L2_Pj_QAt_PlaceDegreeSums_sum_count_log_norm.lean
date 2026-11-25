-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_PlaceDegreeSums_sum_count_log_norm
-- name    : Formalism.L2.Pj.QAt.PlaceDegreeSums.sum_count_log_norm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:54.179802+00:00
-- url     : https://prove2.me/theorems/783c321a-6325-4752-bb44-e4264a82260b
-- title:
--   Place Degree Sums: sum count log norm
-- statement:
--   The Place Degree Sums construction uses the sum count log norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DegreeInfimum/PlaceDegreeSums.lean#L22-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DegreeInfimum/PlaceDegreeSums.lean#L22-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobSt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_DegreeInfimum_PlaceDegreeSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.L2.Pj.QAt.PlaceDegreeSums
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.Pj.QAt.PlaceDegreeSums.sum_count_log_norm (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), (FractionalIdeal.count K w I : ℝ) * logN w =
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by sorry
