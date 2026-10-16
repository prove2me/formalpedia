-- Prove2me | Theorems.Thm_ExactVacuumAtlas_pd_congr_of_eqOn
-- name    : ExactVacuumAtlas.pd_congr_of_eqOn
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T18:58:26.470691+00:00
-- url     : https://prove2.me/theorems/2477a8ad-1139-4386-9d17-e953c7d83302
-- title:
--   Locality of the slice derivative
-- statement:
--   For any n, functions f, h : ℝⁿ → ℝ, an open set V, a point x ∈ V and an index i: if f and h agree on V (Set.EqOn f h V) then pd i f x = pd i h x.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Core/Pd.lean#L35-L41; SHA-256 de5add9938c9a8be29fbeea73f501181f6cd5e596029c40b44e10ae21b047ab1. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
open Filter Topology
open scoped ContDiff
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.pd_congr_of_eqOn {f h : Pt n → ℝ} {V : Set (Pt n)} (hV : IsOpen V) {x : Pt n}
    (hx : x ∈ V) (hfh : Set.EqOn f h V) (i : Fin n) : pd i f x = pd i h x := by sorry
