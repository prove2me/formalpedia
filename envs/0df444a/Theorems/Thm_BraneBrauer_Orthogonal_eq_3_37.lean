-- Prove2me | Theorems.Thm_BraneBrauer_Orthogonal_eq_3_37
-- name    : BraneBrauer.Orthogonal.eq_3_37
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T09:28:41.170143+00:00
-- url     : https://prove2.me/theorems/d3bea32e-e95a-474a-9143-f7613e038771
-- title:
--   (3.37) — partial transpose preserves symmetric operators
-- statement:
--   Let $P_{\sigma,\tau}$ represent $(\sigma,\tau)\in S_m\times S_n$ on the mixed tensor space. For every operator $X$,
--   $$
--   P_{\sigma,\tau}XP_{\sigma^{-1},\tau^{-1}}=X
--   \quad\Longleftrightarrow\quad
--   P_{\sigma,\tau}\Sigma(X)P_{\sigma^{-1},\tau^{-1}}=\Sigma(X).
--   $$
--   Thus the partial transpose preserves the subgroup-conjugation invariance that defines a symmetric operator.
--
--   **Formalization Note** The matrix identity holds on the full operator space; the paper states it for Brauer elements.
-- source:
--   Kimura & Ramgoolam, Branes, Anti-Branes and Brauer Algebras in Gauge-Gravity duality, arXiv:0709.2158v2, p. 15, (3.37)

import Mathlib
import Definitions.Def_BraneBrauer_Orthogonal_Setting

noncomputable section

namespace BraneBrauer.Orthogonal

/-- (3.37), p. 15: partial transpose preserves invariance under
conjugation by the `Sₘ × Sₙ` tensor-factor permutation action. -/
theorem eq_3_37 {N m n : ℕ}
    (σ : Equiv.Perm (Fin m)) (τ : Equiv.Perm (Fin n))
    (X : Op N m n) :
    (permOp N m n σ τ * X * permOp N m n σ⁻¹ τ⁻¹ = X) ↔
    (permOp N m n σ τ * sigma X * permOp N m n σ⁻¹ τ⁻¹ = sigma X) := by sorry

end BraneBrauer.Orthogonal
