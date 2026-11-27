-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_7_4
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_7_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:02:09.370452+00:00
-- url     : https://prove2.me/theorems/4eb9c272-a534-403e-94fd-f073529d9c1b
-- title:
--   Theorem 7:4 — the error function at $\bar x_i$: (7:7), (7:8) and monotone decrease
-- statement:
--   With the cg-method for a real symmetric positive definite $A$, $Ah=k$, $f(x)=(h-x,A(h-x))$ and the smoothed estimates $\bar x_i$, $\bar r_i=k-A\bar x_i$ of (7:2):
--
--   $$f(\bar x_i)=f(x_i)+|\bar r_i|^4\sum_{j=0}^{i-1}\frac{f(x_j)-f(x_{j+1})}{|\bar r_j|^4} \tag{7:7}$$
--
--   for every $i$, and
--
--   $$f(x_i)<f(\bar x_i)<f(\bar x_{i-1})\quad(0<i<m). \tag{7:8}$$
--
--   The sequence $f(\bar x_0),f(\bar x_1),\dots$ decreases monotonically, strictly up to the termination step $m$. At the endpoints $\bar x_0=x_0$ and $\bar x_m=x_m=h$.
--
--   The smoothed estimates are worse than the cg estimates in the energy norm but still improve monotonically.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
--   - reading: (7:8) stated without range → $f(x_i)<f(\bar x_i)$ for $0<i<m$; $f(\bar x_{i})<f(\bar x_{i-1})$ for $1\le i\le m$; reason: at $i=0$ and $i=m$ the raw and smoothed estimates coincide, so the left inequality is an equality there
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 419, Theorem 7:4, eqs. (7:7), (7:8) (PDF p. 11)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_errorFun
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:4 (Hestenes–Stiefel 1952, p. 419): the identity (7:7) for every `i`, the
inequalities (7:8) `f(xᵢ) < f(x̄ᵢ) < f(x̄ᵢ₋₁)` for `0 < i < m`, strict decrease of `f(x̄ᵢ)` through
the termination step `m`, monotone decrease of the whole sequence, and the endpoint equalities
`x̄₀ = x₀`, `x̄ₘ = xₘ`. -/
theorem theorem_7_4 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ h : Fin n → ℝ) (hh : A *ᵥ h = k) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, errorFun A h (smoothX A k x₀ i) = errorFun A h (cgIter A k x₀ i).x +
      ((k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i)) ^ 2 *
        ∑ j ∈ Finset.range i,
          (errorFun A h (cgIter A k x₀ j).x - errorFun A h (cgIter A k x₀ (j + 1)).x) /
            ((k - A *ᵥ smoothX A k x₀ j) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ j)) ^ 2) ∧
    (∀ i : ℕ, 0 < i → i < m →
      errorFun A h (cgIter A k x₀ i).x < errorFun A h (smoothX A k x₀ i)) ∧
    (∀ i : ℕ, i + 1 ≤ m →
      errorFun A h (smoothX A k x₀ (i + 1)) < errorFun A h (smoothX A k x₀ i)) ∧
    (∀ i : ℕ, errorFun A h (smoothX A k x₀ (i + 1)) ≤ errorFun A h (smoothX A k x₀ i)) ∧
    smoothX A k x₀ 0 = x₀ ∧ smoothX A k x₀ m = (cgIter A k x₀ m).x := by sorry

end ConjGrad.ErrorDecrease.Supplement
