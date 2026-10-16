-- Prove2me | Theorems.Thm_ExactVacuumAtlas_ricci_eq_contr_curv
-- name    : ExactVacuumAtlas.ricci_eq_contr_curv
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:03:36.967147+00:00
-- url     : https://prove2.me/theorems/ecb23d54-d818-407e-bd0b-ffa25313e8ae
-- title:
--   Bridge: the registered ricci equals the contraction of the matrix curvature (symmetric connection)
-- statement:
--   Let U be open and Γ a connection (Fin n → Fin n → Fin n → Pt n → ℝ) that is symmetric in its two lower indices at every point of U (Γ a b c x = Γ a c b x). Then for every y ∈ U and all b, d: ricci Γ b d y = Σ_i curv (connMat Γ) i d y i b. For christoffel of a symmetric metric this symmetry holds (MetricData.christoffel_symm).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Connection.lean#L158-L170; SHA-256 d9d2c0c550804af1430499fc5d73ee7e2bc88101561ef9f58a7d0037f08372e9. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.ricci_eq_contr_curv {Γ : Fin n → Fin n → Fin n → Pt n → ℝ} {U : Set (Pt n)} (hU : IsOpen U)
    (hΓ : ∀ x ∈ U, ∀ a b c, Γ a b c x = Γ a c b x) {y : Pt n} (hy : y ∈ U) (b d : Fin n) :
    ricci Γ b d y = ∑ i, curv (connMat Γ) i d y i b := by sorry
