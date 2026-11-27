-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_4_3
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T01:53:47.090257+00:00
-- url     : https://prove2.me/theorems/6d6ccf50-8c47-4e36-a516-2fa2a0c433b1
-- title:
--   Theorem 4:3 — the cd-method minimizes $f$ on lines and on the planes $P_i$
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix, $h$ the solution of $Ah=k$, and $f(x)=(h-x,A(h-x))$ the error function (4:5). Let $x_0,x_1,\dots$, $r_i=k-Ax_i$ and $p_0,p_1,\dots$ be the estimates, residuals and directions of a run of the cd-method (4:1)–(4:2). Then for every step $i\ge1$:
--
--   1. $x_i$ minimizes $f$ on the line $x=x_{i-1}+\alpha p_{i-1}$, $\alpha\in\mathbb R$;
--   2. the error is relaxed by
--   $$f(x_{i-1})-f(x_i)=\frac{(p_{i-1},r_{i-1})^2}{(p_{i-1},Ap_{i-1})}; \tag{4:9}$$
--   3. $x_i$ minimizes $f$ on the plane $P_i$ of points $x=x_0+\alpha_0p_0+\cdots+\alpha_{i-1}p_{i-1}$ (4:10), which contains $x_0,x_1,\dots,x_i$;
--   4. $P_i$ is $i$-dimensional: when $p_0,\dots,p_{i-1}$ are nonzero they are linearly independent.
--
--   This is the variational characterization behind every cd-method: each step is an exact line search, and after $i$ steps the estimate is the minimizer of $f$ on the whole affine span of the directions used.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product. The run is any `x r p` satisfying the published predicate `ConjGrad.Termination.IsCDRun` (residuals $r_i=k-Ax_i$, step (4:1a)–(4:1b), conjugacy (4:2)); the plane is `cdPlane (x 0) p i`. Line minimization and (4:9) are stated at the Lean step $i+1$. The dimension of $P_i$ is stated as linear independence of the nonzero directions, the condition under which the paper's $P_i$ is $i$-dimensional.
--
--   Differences from the source:
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
--   - generalization: a cd-method, whose formula (4:1a) is defined for nonzero directions → every run satisfying `IsCDRun`, a zero direction giving step $a_i=0/0=0$; reason: for runs with nonzero directions it is exactly the source's statement
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 413, Theorem 4:3, eqs. (4:9), (4:10) (PDF p. 5)

import Mathlib
import Definitions.Def_ConjGrad_Termination_IsCDRun
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 4:3 (Hestenes–Stiefel 1952, p. 413), for every run of the cd-method; the paper's
step `i` is the Lean step `i + 1`. -/
theorem theorem_4_3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k h : Fin n → ℝ) (hh : A *ᵥ h = k) (x r p : ℕ → Fin n → ℝ)
    (hcd : Termination.IsCDRun A k x r p) :
    (∀ (i : ℕ) (α : ℝ), errorFun A h (x (i + 1)) ≤ errorFun A h (x i + α • p i)) ∧
    (∀ i : ℕ, errorFun A h (x i) - errorFun A h (x (i + 1)) =
        (p i ⬝ᵥ r i) ^ 2 / (p i ⬝ᵥ (A *ᵥ p i))) ∧
    (∀ i : ℕ, x i ∈ cdPlane (x 0) p i ∧
        ∀ y ∈ cdPlane (x 0) p i, errorFun A h (x i) ≤ errorFun A h y) ∧
    (∀ i : ℕ, ∀ j ≤ i, x j ∈ cdPlane (x 0) p i) ∧
    (∀ i : ℕ, (∀ j < i, p j ≠ 0) → LinearIndependent ℝ (fun j : Fin i => p j)) := by sorry

end ConjGrad.ErrorDecrease.Supplement
