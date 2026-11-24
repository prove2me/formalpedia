-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_7_2
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:00:59.526822+00:00
-- url     : https://prove2.me/theorems/bb32b4dd-ebad-4b1d-a608-80dfcddbcf60
-- title:
--   Theorem 7:2 — $\bar x_i\in S_i$ minimizes $|k-Ax|^2$ on $P_i$; (7:4) and the decrease (7:5)
-- statement:
--   With the cg-method for a real symmetric positive definite $A$ and the smoothed estimates $\bar x_i$ of (7:2), $\bar r_i=k-A\bar x_i$:
--
--   1. $\bar x_i$ lies in the convex closure $S_i$ of $x_0,\dots,x_i$;
--   2. $\bar x_i$ is the point of the plane $P_i$ through $x_0,\dots,x_i$ at which $|k-Ax|^2$ is minimal (every other point of $P_i$ has a strictly larger squared residual);
--   3. $$|\bar r_i|^2=\frac{|r_i|^2}{c_i}=\frac{|r_i|^4}{|p_i|^2}; \tag{7:4}$$
--   4. the squared residuals $|\bar r_0|^2,|\bar r_1|^2,\dots$ diminish monotonically, strictly up to the termination step $m$, and at the $i$-th step
--   $$|\bar r_{i-1}|^2-|\bar r_i|^2=\frac{|\bar r_{i-1}|^2}{c_i}. \tag{7:5}$$
--
--   The smoothed estimates are the minimal-residual points of the cg planes, so their residuals decrease even when those of the cg estimates do not (§18).
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 418, Theorem 7:2, eqs. (7:4), (7:5) (PDF p. 10)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cdPlane
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:2 (Hestenes–Stiefel 1952, p. 418): `x̄ᵢ` lies in the convex hull `Sᵢ` of
`x₀, …, xᵢ`, is the unique minimizer of `|k − Ax|²` on the plane `Pᵢ`, satisfies (7:4), and the
squared residuals `|r̄ᵢ|²` decrease, strictly through termination step `m`, by (7:5). -/
theorem theorem_7_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, smoothX A k x₀ i ∈
      convexHull ℝ (Set.range fun j : Fin (i + 1) => (cgIter A k x₀ j).x)) ∧
    (∀ i : ℕ, smoothX A k x₀ i ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i ∧
      ∀ y ∈ cdPlane x₀ (fun j => (cgIter A k x₀ j).p) i, y ≠ smoothX A k x₀ i →
        (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) <
          (k - A *ᵥ y) ⬝ᵥ (k - A *ᵥ y)) ∧
    (∀ i : ℕ,
      (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) =
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) / smoothC A k x₀ i ∧
        (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) =
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) ^ 2 /
            ((cgIter A k x₀ i).p ⬝ᵥ (cgIter A k x₀ i).p)) ∧
    (∀ i : ℕ, (k - A *ᵥ smoothX A k x₀ (i + 1)) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ (i + 1)) ≤
      (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i)) ∧
    (∀ i : ℕ, i + 1 ≤ m →
      (k - A *ᵥ smoothX A k x₀ (i + 1)) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ (i + 1)) <
        (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i)) ∧
    (∀ i : ℕ, (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) -
        (k - A *ᵥ smoothX A k x₀ (i + 1)) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ (i + 1)) =
      (k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i) /
        smoothC A k x₀ (i + 1)) := by sorry

end ConjGrad.ErrorDecrease.Supplement
