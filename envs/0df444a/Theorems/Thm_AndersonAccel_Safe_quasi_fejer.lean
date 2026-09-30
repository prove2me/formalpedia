-- Prove2me | Theorems.Thm_AndersonAccel_Safe_quasi_fejer
-- name    : AndersonAccel.Safe.quasi_fejer
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:11:45.997987+00:00
-- url     : https://prove2.me/theorems/b9b7587c-f87f-4020-b822-2d5dd892dbcf
-- title:
--   Eq. (4.7) — quasi-Fejér monotonicity $\|x^{k+1}-y\|_2^2\le\|x^k-y\|_2^2+\epsilon_k$ with $\sum_k\epsilon_k<\infty$
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R^n$ be nonexpansive and run Algorithm 3.1 with $\bar\theta,\tau,\alpha\in(0,1)$, $D,\epsilon>0$ and max-memory $m\ge1$, assuming no iterate is a solution. Let $y$ be a fixed point of $f$, $\bar U=\|g(x^0)\|_2$, $C$ the bound (3.8), and
--   $$E=\|x^0-y\|_2+CD\bar U\sum_{i=0}^\infty(i+1)^{-(1+\epsilon)}.$$
--   Define $\epsilon_k=0$ when step $k$ is an averaged step (and for $k=0$), and, when iteration $k\ge1$ accepts the accelerated step as the $i$-th one ($i=n_{AA}$ at the test),
--   $$\epsilon_k=(CD\bar U)^2(i+1)^{-(2+2\epsilon)}+2CDE\bar U(i+1)^{-(1+\epsilon)}.\qquad(4.4)$$
--   Then $\epsilon_k\ge0$, $\sum_{k=0}^\infty\epsilon_k<\infty$, and for every $k\ge0$
--   $$\|x^{k+1}-y\|_2^2\ \le\ \|x^k-y\|_2^2+\epsilon_k.\qquad(4.7)$$
--
--   This quasi-Fejér property is what turns the boundedness of the iterates into convergence of the distances to every fixed point.
--
--   **Formalization Note** The sequence $\epsilon_k$ is given explicitly (from (4.4)) rather than asserted to exist; the paper's identity $\sum_k\epsilon_k=\sum_i\epsilon_{k_i}$ is replaced by summability, which is its content. The safeguard exponent $\epsilon$ and the sequence $\epsilon_k$ are different objects (`ε` and `epsSeq` in Lean). The index $k=0$ is the averaged step $x^1=f_\alpha(x^0)$.
-- source:
--   Zhang, O'Donoghue, Boyd, SIAM J. Optim. 30 (2020), p. 3180, Eq. (4.4), and p. 3181, Eq. (4.7)

import Mathlib
import Definitions.Def_AndersonAccel_Safe_Basic
import Definitions.Def_AndersonAccel_Safe_IsAAISRun

namespace AndersonAccel.Safe

/-- Eq. (4.7) with (4.4) (pp. 3180–3181). For every fixed point `y`,
`‖x^{k+1} - y‖² ≤ ‖x^k - y‖² + ε_k` with `ε_k ≥ 0` summable, where `ε_k = 0` at KM steps and
`ε_k = (C D Ū)² (i + 1)^{-(2+2ε)} + 2 C D E Ū (i + 1)^{-(1+ε)}` at the `i`-th accepted AA step. -/
theorem quasi_fejer {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hf : LipschitzWith 1 f)
    (θbar τ α D ε : ℝ) (m : ℕ)
    (hθ0 : 0 < θbar) (hθ1 : θbar < 1) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hα0 : 0 < α) (hα1 : α < 1)
    (hD : 0 < D) (hε : 0 < ε) (hm : 0 < m)
    (x xt s y shat ytil : ℕ → EuclideanSpace ℝ (Fin n))
    (H : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) (mem nAA : ℕ → ℕ)
    (hrun : IsAAISRun f θbar τ α D ε m x xt s y shat ytil H mem nAA)
    (hnosol : ∀ k, f (x k) ≠ x k)
    (yf : EuclideanSpace ℝ (Fin n)) (hyf : f yf = yf) :
    let C := (3 * ((1 + θbar + τ) / τ) ^ m - 2) ^ (n - 1) / θbar ^ m
    let Ubar := ‖residual f (x 0)‖
    let Ebd := ‖x 0 - yf‖ + C * D * Ubar * ∑' i : ℕ, ((i : ℝ) + 1) ^ (-(1 + ε))
    let epsSeq : ℕ → ℝ := fun k =>
      if 1 ≤ k ∧ ‖residual f (x k)‖ ≤ D * Ubar * ((nAA k : ℝ) + 1) ^ (-(1 + ε)) then
        (C * D * Ubar) ^ 2 * ((nAA k : ℝ) + 1) ^ (-(2 + 2 * ε)) +
          2 * C * D * Ebd * Ubar * ((nAA k : ℝ) + 1) ^ (-(1 + ε))
      else 0
    (∀ k, 0 ≤ epsSeq k) ∧ Summable epsSeq ∧
      ∀ k, ‖x (k + 1) - yf‖ ^ 2 ≤ ‖x k - yf‖ ^ 2 + epsSeq k := by sorry

end AndersonAccel.Safe
