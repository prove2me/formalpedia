-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_dec
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.dec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:09.698208+00:00
-- url     : https://prove2.me/theorems/155e67bf-2d6f-4c44-af2d-b76da8bffb53
-- title:
--   Adapted: dec
-- statement:
--   The Adapted construction uses the dec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L186-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L186-L240

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaChol
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_IwaCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted CompanionTheory.D.gk.admitted.CholeskyDecomposition
open Matrix
open scoped ComplexOrder MatrixOrder
variable {n : ℕ}
variable {p : Fin n → Fin n} {b : Fin n → ℤ} {c : Fin n → ℂ}

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.dec (h : Adapted p b c) : Dec (dp p 0 c) := by sorry
