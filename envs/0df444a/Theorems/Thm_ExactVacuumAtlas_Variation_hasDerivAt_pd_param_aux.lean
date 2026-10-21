-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_pd_param_aux
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_pd_param_aux
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:24.198998+00:00
-- url     : https://prove2.me/theorems/5a813f8b-086d-45f3-8aaf-af8b3bbc2137
-- title:
--   Interchange of ∂_ε and ∂_i (auxiliary)
-- statement:
--   Interchange of ∂_ε and ∂_i (auxiliary)
--
--   For jointly C^∞ φ on open W: the ε-derivative of ∂_i φ(ε, ·) at x is ∂_i of the ε-derivative.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 参数导数与坐标导数交换（辅助）。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Joint.lean#L89-L137; SHA-256 4b63c47f27fd80bedab505cf38c5c13014839c88f3159852417904171ca49a55. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.Variation.hasDerivAt_pd_param_aux {φ : ℝ × Pt n → ℝ} {W : Set (ℝ × Pt n)} (hW : IsOpen W)
    (hφ : ContDiffOn ℝ ∞ φ W) {ε₀ : ℝ} {x : Pt n} (hx : (ε₀, x) ∈ W)
    {ψ : Pt n → ℝ} (hψ : ∀ y, (ε₀, y) ∈ W → HasDerivAt (fun ε => φ (ε, y)) (ψ y) ε₀) (i : Fin n) :
    HasDerivAt (fun ε => pd i (fun z => φ (ε, z)) x) (pd i ψ x) ε₀ := by sorry
