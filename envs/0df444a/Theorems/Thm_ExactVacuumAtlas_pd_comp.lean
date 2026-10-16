-- Prove2me | Theorems.Thm_ExactVacuumAtlas_pd_comp
-- name    : ExactVacuumAtlas.pd_comp
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:50:58.564572+00:00
-- url     : https://prove2.me/theorems/1eff1220-b700-43d9-ae42-f2179b4a469b
-- title:
--   Chain rule for the slice derivative
-- statement:
--   Let V be open, f C^∞ on V, Φ a map with Φ y ∈ V whose slices have genuine derivatives J y k i at y. Then for every i: pd i (z ↦ f (Φ z)) y = Σ_e pd e f (Φ y) · J y e i.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Calculus.lean#L69-L87; SHA-256 0f59ac6cfdfd6b539a70914c2743635b3775f0848016a2490e7a5b20efd22759. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.pd_comp {V : Set (Pt n)} (hV : IsOpen V) {f : Pt n → ℝ} (hf : ContDiffOn ℝ ∞ f V)
    {Φ : Pt n → Pt n} {J : Pt n → Matrix (Fin n) (Fin n) ℝ} {y : Pt n} (hy : Φ y ∈ V)
    (hJ : ∀ k i : Fin n, HasDerivAt (fun u : ℝ => Φ (Function.update y i u) k) (J y k i) (y i))
    (i : Fin n) : pd i (fun z => f (Φ z)) y = ∑ e, pd e f (Φ y) * J y e i := by sorry
