-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_system14
-- name    : ExactSDPDuality.ELSD.system14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:20:17.739469+00:00
-- url     : https://prove2.me/theorems/1272289f-06e0-4f75-8357-a19276253b31
-- title:
--   §2.5, system (14) — if 0 ∈ G is primal optimal, (ELSD) has a feasible pair of value 0
-- statement:
--   Let $Q_0,\dots,Q_m$ be real symmetric $n\times n$ matrices, $c\in\mathbb R^m$, and suppose $0\in G = \{x\mid Q(x)\succeq 0\}$ and $c^{\mathsf T}x\le 0$ for every $x\in G$ (the origin is an optimal solution of (P)). Then the system
--   $$(U+W)\bullet Q_0 = 0,\qquad Q^*(U+W) = c,\qquad U\succeq 0,\qquad W\in\mathcal W_m \tag{14}$$
--   is feasible.
--
--   This is the case of optimal value $0$ in the proof of dual attainment (Theorem 6(iv)).
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 152, §2.5, proof of Theorem 6(iv), Case 2, system (14)

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- System (14) (Ramana 1997, §2.5, p. 152, proof of Theorem 6(iv), Case 2): if `0 ∈ G` and the
origin is an optimal solution of (P), i.e. `cᵀx ≤ 0` for every `x ∈ G`, then the system
`(U + W) • Q₀ = 0`, `Q*(U + W) = c`, `U ⪰ 0`, `W ∈ 𝒲ₘ` is feasible. -/
theorem system14 {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ) (c : Fin m → ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q)
    (hopt : ∀ x ∈ feasibleSet Q0 Q, c ⬝ᵥ x ≤ 0) :
    ∃ U W : Matrix (Fin n) (Fin n) ℝ,
      frob (U + W) Q0 = 0 ∧ Qstar Q (U + W) = c ∧ U.PosSemidef ∧ W ∈ Wset Q0 Q m := by sorry

end ExactSDPDuality.ELSD
