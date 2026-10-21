-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_param_inv
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_param_inv
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:36.08023+00:00
-- url     : https://prove2.me/theorems/e83e6296-3e96-4a33-9808-e3c289c795e0
-- title:
--   Derivative of the true inverse family
-- statement:
--   Derivative of the true inverse family
--
--   For jointly C^∞ g on open W with true inverse ginv on W: HasDerivAt (ε ↦ ginv_ε,ij(y)) (invVar (ginv ε₀) h)_ij(y) at ε₀ when h is the derivative of g.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 真实逆族的导数 −G h G。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Joint.lean#L192-L237; SHA-256 4b63c47f27fd80bedab505cf38c5c13014839c88f3159852417904171ca49a55. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.Variation.hasDerivAt_param_inv {g ginv : ℝ → Metric n} {W : Set (ℝ × Pt n)} (hW : IsOpen W)
    (hg : ∀ i j, ContDiffOn ℝ ∞ (fun p : ℝ × Pt n => g p.1 i j p.2) W)
    (hinv : ∀ p ∈ W, metricMatrix (ginv p.1) p.2 * metricMatrix (g p.1) p.2 = 1)
    {ε₀ : ℝ} {y : Pt n} (hy : (ε₀, y) ∈ W) {h : Metric n}
    (hh : ∀ i j, HasDerivAt (fun ε => g ε i j y) (h i j y) ε₀) (a b : Fin n) :
    HasDerivAt (fun ε => ginv ε a b y)
      (-∑ c, ∑ d, ginv ε₀ a c y * h c d y * ginv ε₀ d b y) ε₀ := by sorry
