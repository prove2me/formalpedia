-- Prove2me | Theorems.Thm_Formalism_L2_Pj_QAt_PlaceDegreeSums_sum_infinite_places_mult
-- name    : Formalism.L2.Pj.QAt.PlaceDegreeSums.sum_infinite_places_mult
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:45:43.353332+00:00
-- url     : https://prove2.me/theorems/129fa5bc-a3f5-5809-8780-4d0c36d8a183
-- title:
--   Place Degree Sums: sum infinite places mult
-- statement:
--   The Place Degree Sums construction uses the sum infinite places mult property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DegreeInfimum/PlaceDegreeSums.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/ArchimedeanQuadraticData/DegreeInfimum/PlaceDegreeSums.lean#L13-L20

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

theorem Formalism.L2.Pj.QAt.PlaceDegreeSums.sum_infinite_places_mult (f : InfinitePlace K → ℝ) :
    ∑ σ : InfinitePlace K, (σ.mult : ℝ) * f σ = ∑ τ : K →+* ℂ, f (InfinitePlace.mk τ) := by sorry
