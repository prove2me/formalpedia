-- Prove2me | Theorems.Thm_ExactVacuumAtlas_eq_inv_smul_adjugate
-- name    : ExactVacuumAtlas.eq_inv_smul_adjugate
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:33.386156+00:00
-- url     : https://prove2.me/theorems/31b6cb61-e035-4b55-a0cf-de45a336ffc6
-- title:
--   Left inverse via the adjugate
-- statement:
--   Left inverse via the adjugate
--
--   If J · K = 1 then K = (det J)⁻¹ • adjugate J.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 由伴随矩阵表示逆。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/Transport/MatrixCalc.lean#L231-L242; SHA-256 994bf6c8664b9c7b2def61b44cb0205ed97883699045a73e41d873029c259310. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.eq_inv_smul_adjugate {J K : Matrix (Fin n) (Fin n) ℝ} (h : J * K = 1) :
    K = (J.det)⁻¹ • J.adjugate := by sorry
