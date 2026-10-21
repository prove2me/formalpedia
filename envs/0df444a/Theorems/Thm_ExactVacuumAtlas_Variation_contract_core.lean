-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_contract_core
-- name    : ExactVacuumAtlas.Variation.contract_core
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:57.699003+00:00
-- url     : https://prove2.me/theorems/d6aced43-e1b3-4f23-8f4b-4b4962604838
-- title:
--   Contraction identity for the J law
-- statement:
--   Contraction identity for the J law
--
--   Finite-sum identity Σ_a (Σ_e J_{ea} K X_e Kᵀ)_{ab} = Σ_q K_{bq} Σ_e (X_e)_{eq} when J · K = 1.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** J 变换律的缩并恒等式。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Covariance.lean#L86-L104; SHA-256 9354896334506569e5c4491ef3a59340742907640cf5d1c465ba5a6e2e9ad40b. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Certificate
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.Variation.contract_core {Jm Km : Matrix (Fin n) (Fin n) ℝ} {X : Fin n → Matrix (Fin n) (Fin n) ℝ}
    (hJK : Jm * Km = 1) (b : Fin n) :
    ∑ a, (∑ e, Jm e a • (Km * X e * Kmᵀ)) a b = ∑ q, Km b q * ∑ e, X e e q := by sorry
