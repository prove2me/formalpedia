-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_Adapted_posSemidef
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.posSemidef
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:22.607207+00:00
-- url     : https://prove2.me/theorems/5472316f-871d-43d7-be9c-5849cc1198c4
-- title:
--   Adapted: pos Semidef
-- statement:
--   The Adapted construction uses the pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L121-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L121-L170

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.Adapted.posSemidef (h : Adapted p b c) {B : Matrix (Fin n) (Fin n) ℂ} (hB : B.BlockTriangular id)
    {a : Fin n → ℝ} (ha : ∀ i, 0 < a i) (hBa : ∀ i, B i i = a i)
    (hz : ∀ i j, b i ≠ b j → (B * (dp p 0 c * Bᴴ * dp p 0 c)) i j = 0) :
    (B * (dp p 0 c * Bᴴ * dp p 0 c)).PosSemidef := by sorry
