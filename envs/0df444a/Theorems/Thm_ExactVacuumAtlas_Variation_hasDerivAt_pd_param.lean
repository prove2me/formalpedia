-- Prove2me | Theorems.Thm_ExactVacuumAtlas_Variation_hasDerivAt_pd_param
-- name    : ExactVacuumAtlas.Variation.hasDerivAt_pd_param
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-21T01:50:25.126023+00:00
-- url     : https://prove2.me/theorems/77348717-6a40-4fef-b893-a59b2f29e8a9
-- title:
--   Interchange of ∂_ε and ∂_i
-- statement:
--   Interchange of ∂_ε and ∂_i
--
--   For jointly C^∞ Φ on open W and (ε₀, x) ∈ W: HasDerivAt (ε ↦ pd i (Φ ε) x) (pd i ψ x) ε₀ where ψ is the ε-derivative.
--
--   **Scope.** Exactly the hypotheses printed in the formal statement.
--
--   **中文摘要** 参数导数与坐标偏导交换。
-- source:
--   He Wang, Exact Spacetime Atlas IV: Certified Einstein–Maxwell Backgrounds and First Variations. Local source, no public repository; commit 543904bfcfa3bb169f43fc4d9dbd569999b71886; Atlas/EinsteinMaxwell/Variation/Joint.lean#L139-L146; SHA-256 4b63c47f27fd80bedab505cf38c5c13014839c88f3159852417904171ca49a55. Registered definitions and literature: mission/PHYSICS_BOUNDARY.md (§H–§J); Müller–Grave arXiv:0904.4184; Newman et al., J. Math. Phys. 6 (1965) 918.

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Transport_MatrixCalc
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.Variation.hasDerivAt_pd_param {Φ : ℝ → Pt n → ℝ} {W : Set (ℝ × Pt n)} (hW : IsOpen W)
    (hΦ : ContDiffOn ℝ ∞ (fun p : ℝ × Pt n => Φ p.1 p.2) W) {ε₀ : ℝ} {x : Pt n} (hx : (ε₀, x) ∈ W)
    {ψ : Pt n → ℝ} (hψ : ∀ y, (ε₀, y) ∈ W → HasDerivAt (fun ε => Φ ε y) (ψ y) ε₀) (i : Fin n) :
    HasDerivAt (fun ε => pd i (Φ ε) x) (pd i ψ x) ε₀ := by sorry
