-- Prove2me | Theorems.Thm_CompanionTheory_D_gk_admitted_CholeskyDecomposition_eq_zero_of_unitary_blockTriangular
-- name    : CompanionTheory.D.gk.admitted.CholeskyDecomposition.eq_zero_of_unitary_blockTriangular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:54.468028+00:00
-- url     : https://prove2.me/theorems/85ba5c0e-cb40-4821-a02e-6ebcb2a0b2e4
-- title:
--   Cholesky Decomposition: eq zero of unitary block Triangular
-- statement:
--   The Cholesky Decomposition construction uses the eq zero of unitary block Triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/HarishChandraModules/KFiniteAnalyticVectors/AdmissibleSmoothVectors/IwaCore.lean#L67-L76

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

theorem CompanionTheory.D.gk.admitted.CholeskyDecomposition.eq_zero_of_unitary_blockTriangular {b : Fin n → ℤ} {w : Matrix (Fin n) (Fin n) ℂ}
    (h1 : wᴴ * w = 1) (hw : w.BlockTriangular b) {i j : Fin n} (hij : b i ≠ b j) : w i j = 0 := by sorry
