-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_theorem12
-- name    : ExactSDPDuality.ELSD.theorem12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:19:43.551835+00:00
-- url     : https://prove2.me/theorems/d49cf192-1301-4b64-9bd5-42295476fde9
-- title:
--   Theorem 12 — exact description of the polar G° via 𝒲ₖ, k ≥ m − 1
-- statement:
--   Let $Q_0,\dots,Q_m$ be real symmetric $n\times n$ matrices and $G = \{x\in\mathbb R^m\mid Q(x)\succeq 0\}$. If $G$ contains the origin, then for every $k\ge m-1$ its polar is
--   $$G^\circ = \{Q^*(U + W)\mid W\in\mathcal W_k,\ U\succeq 0,\ U\bullet Q_0\le 1\}.$$
--
--   The paper calls this its central result: an exact, polynomial-size semidefinite description of the polar of a spectrahedron, with no closure operation. The strong duality theorem follows from it by a support-function argument.
--
--   **Formalization Note** For $m = 0$ the bound $m-1$ is $0$ (natural-number subtraction), and $\mathcal W_0 = \{0\}$.
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 143, Theorem 12

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix

namespace ExactSDPDuality.ELSD

/-- Theorem 12 (Ramana 1997, p. 143): if `G` contains the origin, then for every `k ≥ m − 1`,
`G° = {Q*(U + W) | W ∈ 𝒲ₖ, U ⪰ 0, U • Q₀ ≤ 1}`. -/
theorem theorem12 {n m : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q) (k : ℕ) (hk : m - 1 ≤ k) :
    polar (feasibleSet Q0 Q) =
      {y | ∃ U W : Matrix (Fin n) (Fin n) ℝ,
        W ∈ Wset Q0 Q k ∧ U.PosSemidef ∧ frob U Q0 ≤ 1 ∧ Qstar Q (U + W) = y} := by sorry

end ExactSDPDuality.ELSD
