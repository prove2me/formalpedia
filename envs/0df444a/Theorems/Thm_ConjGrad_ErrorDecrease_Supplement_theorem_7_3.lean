-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_7_3
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:01:34.978988+00:00
-- url     : https://prove2.me/theorems/2c752743-c58d-4b17-bc48-31a50e0f74fa
-- title:
--   Theorem 7:3 — Rayleigh quotients of $r_i$ and $\bar r_i$: (7:6a), (7:6b), $\mu(\bar r_i)<\mu(r_i)$
-- statement:
--   With the cg-method for a real symmetric positive definite $A$, the smoothed residuals $\bar r_i=k-A\bar x_i$ of (7:2) and the Rayleigh quotient $\mu$:
--
--   $$\frac{\mu(r_i)}{|r_i|^2}=\frac{\mu(\bar r_i)}{|\bar r_i|^2}+\frac{\mu(\bar r_{i-1})}{|\bar r_{i-1}|^2}\quad(0<i<m), \tag{7:6a}$$
--
--   $$\frac{\mu(\bar r_i)}{|\bar r_i|^2}=\frac{\mu(r_i)}{|r_i|^2}-\frac{\mu(r_{i-1})}{|r_{i-1}|^2}+\cdots+(-1)^i\frac{\mu(r_0)}{|r_0|^2}\quad(i<m), \tag{7:6b}$$
--
--   and $\mu(\bar r_i)<\mu(r_i)$ for $0<i<m$.
--
--   Since $\mu(r)$ measures the smoothness of an estimate in difference-equation applications, $\bar x_i$ is smoother than $x_i$.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
--   - reading: (7:6a), (7:6b) stated without range → $0<i<m$ for (7:6a), $i<m$ for (7:6b); reason: after termination the residuals vanish and the quotients are undefined; the strict comparison is stated for $i>0$ in the source
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 419, Theorem 7:3, eqs. (7:6a), (7:6b) (PDF p. 11)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_rayleigh
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 7:3 (Hestenes–Stiefel 1952, p. 419): (7:6a) at the paper's index `i + 1` with
`0 < i + 1 < m`, (7:6b) for `i < m`, and `μ(r̄ᵢ) < μ(rᵢ)` for `0 < i < m`, where
`r̄ᵢ = k − Ax̄ᵢ` and `m` is the step at which the cg-method terminates. -/
theorem theorem_7_3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (m : ℕ) (hm : (cgIter A k x₀ m).r = 0)
    (hact : ∀ j < m, (cgIter A k x₀ j).r ≠ 0) :
    (∀ i : ℕ, i + 1 < m →
      rayleigh A (cgIter A k x₀ (i + 1)).r /
          ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) =
        rayleigh A (k - A *ᵥ smoothX A k x₀ (i + 1)) /
            ((k - A *ᵥ smoothX A k x₀ (i + 1)) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ (i + 1))) +
          rayleigh A (k - A *ᵥ smoothX A k x₀ i) /
            ((k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i))) ∧
    (∀ i : ℕ, i < m →
      rayleigh A (k - A *ᵥ smoothX A k x₀ i) /
          ((k - A *ᵥ smoothX A k x₀ i) ⬝ᵥ (k - A *ᵥ smoothX A k x₀ i)) =
        ∑ j ∈ Finset.range (i + 1), (-1 : ℝ) ^ (i + j) *
          (rayleigh A (cgIter A k x₀ j).r / ((cgIter A k x₀ j).r ⬝ᵥ (cgIter A k x₀ j).r))) ∧
    (∀ i : ℕ, 0 < i → i < m →
      rayleigh A (k - A *ᵥ smoothX A k x₀ i) < rayleigh A (cgIter A k x₀ i).r) := by sorry

end ConjGrad.ErrorDecrease.Supplement
