-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_conj_apply
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.conj_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:50:43.640811+00:00
-- url     : https://prove2.me/theorems/b04770c7-f0c4-4f4f-a80b-7a4743ca28d0
-- title:
--   Adapted: conj apply
-- statement:
--   The Adapted construction uses the conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L106-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L106-L110

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.conj_apply (h : Adapted p b c) (B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (dp p 0 c * Bᴴ * dp p 0 c) i j = c i * c j * star (B (p j) (p i)) := by sorry
