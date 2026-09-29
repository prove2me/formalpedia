-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_weak_duality
-- name    : ExactSDPDuality.ELSD.weak_duality
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:14:06.707961+00:00
-- url     : https://prove2.me/theorems/c16bd339-0be8-45fc-89fa-cb9daa903bb0
-- title:
--   Theorem 6(i) — weak duality: cᵀx ≤ (U + W) • Q₀ for W ∈ 𝒲ₖ, k ≤ m
-- statement:
--   Let $Q_0,\dots,Q_m$ be real symmetric $n\times n$ matrices, $c\in\mathbb R^m$, and $G = \{x\mid \sum_i x_iQ_i\preceq Q_0\}$. Let $k\le m$, let $x\in G$, and let $U, W$ be real $n\times n$ matrices with
--   $$Q^*(U+W) = c,\qquad W\in\mathcal W_k,\qquad U\succeq 0 .$$
--   Then
--   $$c^{\mathsf T}x \le (U+W)\bullet Q_0 .$$
--
--   With $k = m$ this is weak duality between (P) and (ELSD); with $k = m-1$ it is weak duality between (P) and (Weak-ELSD). This is the form in which the paper proves Theorem 6(i).
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 138, Theorem 6(i); proof on pp. 140–141

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Theorem 6(i), weak duality, in the form proved on pp. 140–141 (Ramana 1997): if `x` is
primal feasible, `k ≤ m`, and `(U, W)` satisfies `Q*(U + W) = c`, `W ∈ 𝒲ₖ`, `U ⪰ 0`, then
`cᵀx ≤ (U + W) • Q₀`. With `k = m` this is weak duality for (ELSD), with `k = m − 1` for
(Weak-ELSD). -/
theorem weak_duality {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm) (k : ℕ) (hk : k ≤ m)
    (x : Fin m → ℝ) (hx : x ∈ feasibleSet Q0 Q)
    (U W : Matrix (Fin n) (Fin n) ℝ) (hc : Qstar Q (U + W) = c)
    (hW : W ∈ Wset Q0 Q k) (hU : U.PosSemidef) :
    c ⬝ᵥ x ≤ frob (U + W) Q0 := by sorry

end ExactSDPDuality.ELSD
