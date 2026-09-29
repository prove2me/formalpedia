-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_claim17
-- name    : ExactSDPDuality.ELSD.claim17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T00:18:10.633421+00:00
-- url     : https://prove2.me/theorems/28ca4baa-1ebf-4bc0-9c39-5957cb60e297
-- title:
--   Claim 17 — non-closedness of G* + T^⊥ yields U ⪰ 0 cutting down the subspace T
-- statement:
--   Let $A$ be a real $r\times m$ matrix of full row rank, $T = \{x\mid Ax = 0\}$, and let $G = \{x\mid Q(x)\succeq 0\}$ be a spectrahedron given by real symmetric $Q_0,\dots,Q_m$ and containing the origin. If $G^* + T^\perp$ is not closed, then there exist $U\succeq 0$ and $\lambda\in\mathbb R^r$ with
--   $$Q^*(U) + A^{\mathsf T}\lambda = 0,\qquad Q_0\bullet U = 0,$$
--   such that $\{x\mid Ax = 0,\ Q(x)U = 0\}$ is a linear subspace whose dimension is strictly smaller than that of $T$.
--
--   This is the step that extracts, from the failure of closedness, a new constraint on the affine hull of $G$; iterated, it builds the sets $\mathcal W_k$.
--
--   **Formalization Note** "Full row rank" is linear independence of the rows of $A$. The subspace claim is stated as: there are submodules whose carriers are $\{x\mid Ax = 0,\ Q(x)U = 0\}$ and $T$, and the finite rank of the first is strictly smaller than that of the second.
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 147, Claim 17

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix Pointwise

namespace ExactSDPDuality.ELSD

/-- Claim 17 (Ramana 1997, p. 147): let `T = {x | Ax = 0}` with `A` an `r × m` matrix of full
row rank, and let `G = {x | Q(x) ⪰ 0}` contain the origin. If `G* + T^⊥` is not closed, then
there exist `U ⪰ 0` and `λ ∈ ℝʳ` with `Q*(U) + Aᵀλ = 0`, `Q₀ • U = 0`, and
`{x | Ax = 0, Q(x)U = 0}` is a subspace of dimension strictly smaller than that of `T`. -/
theorem claim17 {n m r : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q)
    (A : Matrix (Fin r) (Fin m) ℝ) (hA : LinearIndependent ℝ (fun i : Fin r => A i))
    (hnc : ¬ IsClosed (algPolar Q0 Q + perp {x | A *ᵥ x = 0})) :
    ∃ (U : Matrix (Fin n) (Fin n) ℝ) (lam : Fin r → ℝ),
      U.PosSemidef ∧ Qstar Q U + Aᵀ *ᵥ lam = 0 ∧ frob Q0 U = 0 ∧
        ∃ S T : Submodule ℝ (Fin m → ℝ),
          (S : Set (Fin m → ℝ)) = {x | A *ᵥ x = 0 ∧ Qaff Q0 Q x * U = 0} ∧
          (T : Set (Fin m → ℝ)) = {x | A *ᵥ x = 0} ∧
          Module.finrank ℝ S < Module.finrank ℝ T := by sorry

end ExactSDPDuality.ELSD
