-- Prove2me | Theorems.Thm_ConjGrad_Termination_cg_isCDRun
-- name    : ConjGrad.Termination.cg_isCDRun
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:52:33.201029+00:00
-- url     : https://prove2.me/theorems/25565eb8-0348-43cb-b77d-b967363c7852
-- title:
--   Theorem 5:2, first sentence — the cg-method is a cd-method
-- statement:
--   Let $A$ be a real symmetric positive definite $n \times n$ matrix and let $k, x_0 \in \mathbb{R}^n$. The estimates $x_i$, residuals $r_i$ and directions $p_i$ produced by the conjugate gradient method (3:1) started at $x_0$ form a run of the method of conjugate directions for $Ax = k$: for all $i \ge 0$,
--
--   1. $r_i = k - Ax_i$;
--   2. $x_{i+1} = x_i + a_i p_i$ with $a_i = \dfrac{(p_i, r_i)}{(p_i, Ap_i)}$;
--   3. $(p_{i+1}, Ap_j) = 0$ for $j = 0, 1, \dots, i$.
--
--   In the paper's words: the cg-method is a cd-method. Together with Theorem 4:2 this yields the finite termination of the cg-method.
--
--   **Formalization Note** Only the first sentence of Theorem 5:2 is formalized. The second sentence (the $p_i$ are obtained by $A$-orthogonalization of the residuals) and the converse ("a cd-method in which the residuals are mutually orthogonal is essentially a cg-method", which the paper qualifies by an informal continuity assumption) are not part of this statement.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 415, Theorem 5:2, first sentence

import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter
import Definitions.Def_ConjGrad_Termination_IsCDRun

open Matrix

namespace ConjGrad.Termination

/-- Theorem 5:2, first sentence (Hestenes–Stiefel 1952, p. 415): the cg-method is a
cd-method. For a symmetric positive definite `A`, the estimates, residuals and directions
produced by the cg-method (3:1) form a run of the cd-method (4:1)–(4:2): `rᵢ = k − Axᵢ`,
`xᵢ₊₁ = xᵢ + ((pᵢ,rᵢ)/(pᵢ,Apᵢ)) pᵢ`, and each `pᵢ₊₁` is conjugate to `p₀, …, pᵢ`. -/
theorem cg_isCDRun {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) :
    IsCDRun A k (fun i => (cgIter A k x₀ i).x) (fun i => (cgIter A k x₀ i).r)
      (fun i => (cgIter A k x₀ i).p) := by sorry

end ConjGrad.Termination
