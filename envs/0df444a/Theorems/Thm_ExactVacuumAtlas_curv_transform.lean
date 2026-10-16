-- Prove2me | Theorems.Thm_ExactVacuumAtlas_curv_transform
-- name    : ExactVacuumAtlas.curv_transform
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:01:33.393145+00:00
-- url     : https://prove2.me/theorems/60906357-4026-4db3-89eb-5dbf3b743f07
-- title:
--   Tensoriality of the matrix curvature of a transformed connection
-- statement:
--   Under CoordChange U V Φ J K, for connections Γ, Γ′ (families of matrix fields) with every Γ e C^∞ on V (SmoothOn) and Γ′ i y = Σ_e J(y)_{ei} • (K(y) Γ e (Φ y) J(y)) + K(y) ∂ᵢJ(y) for all y ∈ U (the explicit transformation hypothesis, which is exactly what christoffel_transform proves): for every y ∈ U and all c, d, curv Γ′ c d y = Σ_e Σ_f (J(y)_{ec} J(y)_{fd}) • (K(y) · curv Γ e f (Φ y) · J(y)), where curv Γ c d = ∂_c Γ_d − ∂_d Γ_c + Γ_c Γ_d − Γ_d Γ_c.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Curvature.lean#L67-L145; SHA-256 858c500b5613da0b7365f52bf082c6d59235ecb04152a0bc11669cac412050f2. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}

theorem ExactVacuumAtlas.curv_transform (hc : CoordChange U V Φ J K)
    {Γ Γ' : Fin n → Pt n → Matrix (Fin n) (Fin n) ℝ} (hΓ : ∀ e, SmoothOn (Γ e) V)
    (hΓ' : ∀ y ∈ U, ∀ i, Γ' i y = ∑ e, J y e i • (K y * Γ e (Φ y) * J y) + K y * pdM i J y)
    {y : Pt n} (hy : y ∈ U) (c d : Fin n) :
    curv Γ' c d y = ∑ e, ∑ f, (J y e c * J y f d) • (K y * curv Γ e f (Φ y) * J y) := by sorry
