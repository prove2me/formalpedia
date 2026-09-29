-- Prove2me | Theorems.Thm_ConjGrad_Termination_cg_stepLength_formulas
-- name    : ConjGrad.Termination.cg_stepLength_formulas
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:51:57.025547+00:00
-- url     : https://prove2.me/theorems/5772d0af-434c-4609-83d9-97b992f03611
-- title:
--   Theorem 5:5, eq. (5:10) — $a_i=|r_i|^2/(p_i,Ap_i)=(p_i,r_i)/(p_i,Ap_i)=(p_i,r_0)/(p_i,Ap_i)$
-- statement:
--   Let $A$ be a real symmetric positive definite $n \times n$ matrix, let $k, x_0 \in \mathbb{R}^n$, and let $x_i$, $r_i$, $p_i$ be produced by the conjugate gradient method (3:1) started at $x_0$, with step lengths $a_i = |r_i|^2/(p_i, Ap_i)$ as in (3:1b). Then for every $i$
--
--   $$a_i = \frac{|r_i|^2}{(p_i, Ap_i)} = \frac{(p_i, r_i)}{(p_i, Ap_i)} = \frac{(p_i, r_0)}{(p_i, Ap_i)}.$$
--
--   The middle expression is the step length (4:1a) of the method of conjugate directions, so this identity is one half of the statement that the cg-method is a cd-method; the last expression is (4:4).
--
--   **Formalization Note** The first equality is the definition of $a_i$ (`cgA`); the statement asserts the other two. It covers only formula (5:10) of Theorem 5:5; the formulas (5:11) for $b_i$ and the Rayleigh quotient bounds (5:12) are not part of it. After the method reaches the solution both sides are $0$.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), https://doi.org/10.6028/jres.049.044, p. 416, Theorem 5:5, eq. (5:10)

import Mathlib
import Definitions.Def_ConjGrad_Termination_cgIter

open Matrix

namespace ConjGrad.Termination

/-- Theorem 5:5, eq. (5:10) (Hestenes–Stiefel 1952, p. 416). For a symmetric positive
definite `A`, the step length `aᵢ = |rᵢ|²/(pᵢ, Apᵢ)` of the cg-method (3:1b) also equals
`(pᵢ, rᵢ)/(pᵢ, Apᵢ)` and `(pᵢ, r₀)/(pᵢ, Apᵢ)`. -/
theorem cg_stepLength_formulas {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (i : ℕ) :
    cgA A (cgIter A k x₀ i) =
        ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).r) /
          ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) ∧
      cgA A (cgIter A k x₀ i) =
        ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ 0).r) /
          ((cgIter A k x₀ i).p ⬝ᵥ (A *ᵥ (cgIter A k x₀ i).p)) := by sorry

end ConjGrad.Termination
