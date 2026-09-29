-- Prove2me | Theorems.Thm_ExactSDPDuality_ELSD_cor14
-- name    : ExactSDPDuality.ELSD.cor14
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T00:17:24.528593+00:00
-- url     : https://prove2.me/theorems/0844e655-9e89-44cf-a325-810d4138ce77
-- title:
--   Corollary 14 — (G ∩ T)° = Cl(G* + T^⊥) for T = {x | Ax = 0}
-- statement:
--   Let $Q_0,\dots,Q_m$ be real symmetric $n\times n$ matrices with $0\in G = \{x\mid Q(x)\succeq 0\}$, let $A$ be a real $r\times m$ matrix and $T = \{x\mid Ax = 0\}$. Then
--   $$(G\cap T)^\circ = \mathrm{Cl}\big(G^* + T^\perp\big),$$
--   where $G^*$ is the algebraic polar, $T^\perp$ the orthogonal complement of $T$, and $+$ the Minkowski sum.
--
--   It extends Lemma 13 to a spectrahedron intersected with a linear subspace, and is used in the proof of Claim 17.
-- source:
--   Ramana, An exact duality theory for semidefinite programming and its complexity implications, Math. Program. 77 (1997), p. 144, Corollary 14

import Mathlib
import Definitions.Def_ExactSDPDuality_ELSD_Model

open Matrix Pointwise

namespace ExactSDPDuality.ELSD

/-- Corollary 14 (Ramana 1997, p. 144): if `0 ∈ G` and `T = {x | Ax = 0}` for a real
`r × m` matrix `A`, then `(G ∩ T)° = Cl(G* + T^⊥)` (Minkowski sum). -/
theorem cor14 {n m r : ℕ} (Q0 : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hQ0 : Q0.IsSymm) (hQ : ∀ i, (Q i).IsSymm)
    (h0 : (0 : Fin m → ℝ) ∈ feasibleSet Q0 Q) (A : Matrix (Fin r) (Fin m) ℝ) :
    polar (feasibleSet Q0 Q ∩ {x | A *ᵥ x = 0}) =
      closure (algPolar Q0 Q + perp {x | A *ᵥ x = 0}) := by sorry

end ExactSDPDuality.ELSD
