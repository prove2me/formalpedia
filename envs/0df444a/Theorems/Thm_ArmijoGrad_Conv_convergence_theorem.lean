-- Prove2me | Theorems.Thm_ArmijoGrad_Conv_convergence_theorem
-- name    : ArmijoGrad.Conv.convergence_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:02:56.792592+00:00
-- url     : https://prove2.me/theorems/3c0b25b4-4b56-4da0-9dfa-ba91d389bd08
-- title:
--   THEOREM (§2), pp. 1–2 — for 0 < δ ≤ 1/4K, S*(x, δ) ≠ ∅ and every sequence with x_{k+1} ∈ S*(x_k, δ) converges to x*
-- statement:
--   Let $f : E^n \to \mathbb{R}$ be continuous everywhere on $E^n$ and bounded below on $E^n$, and fix $x_0 \in E^n$ with level set $S(x_0) = \{x : f(x) \le f(x_0)\}$. Assume:
--
--   1. **Condition III at $x_0$:** $f \in C^1$ on $S(x_0)$ and $|\nabla f(y) - \nabla f(x)| \le K|y - x|$ for all $x, y \in S(x_0)$, with $K > 0$;
--   2. **Condition IV at $x_0$:** $f \in C^1$ on $S(x_0)$, $x^*$ satisfies $f(x^*) = \inf_{E^n} f$, and for every $r > 0$, $m(r) = \inf\{|\nabla f(x)| : x \in S(x_0),\ |x - x^*| \ge r\} > 0$ (with $m(r) = \infty$ if the set is empty).
--
--   Let $0 < \delta \le 1/(4K)$. Then for every $x \in S(x_0)$ the set
--   $$S^*(x,\delta) = \{x_\lambda : x_\lambda = x - \lambda\nabla f(x),\ \lambda > 0,\ f(x_\lambda) - f(x) \le -\delta|\nabla f(x)|^2\}$$
--   is a nonempty subset of $S(x_0)$, and every sequence $\{x_k\}_{k=0}^\infty$ with first term $x_0$ and $x_{k+1} \in S^*(x_k,\delta)$ for $k = 0, 1, 2, \dots$ converges to $x^*$.
--
--   This is Armijo's convergence theorem for the gradient method: any choice of step that achieves the sufficient decrease $\delta|\nabla f(x_k)|^2$ yields convergence to the minimizer. Both the fixed-step steepest descent method and Armijo's halving rule (Corollaries 1 and 2) are instances.
--
--   **Formalization Note** $E^n$ is `EuclideanSpace ℝ (Fin n)` and $\nabla f$ is Mathlib's `gradient`. The paper uses the same symbol $x_0$ for the base point of $S(x_0)$ and the first iterate; the formalization makes this explicit with the hypothesis $x_0 = $ first term. Conditions III and IV are assumed on $S(x_0)$ only, never on all of $E^n$. Condition IV carries the minimizer $x^*$; it forces $x^*$ to be the unique minimizer, so the limit is *the* minimizer of $f$.
-- source:
--   Armijo, Minimization of functions having Lipschitz continuous first partial derivatives, Pacific J. Math. 16 (1966), pp. 1–2, THEOREM (§2) and (1), under the standing assumptions of §2

import Mathlib
import Definitions.Def_ArmijoGrad_Conv_Setting

open Filter Topology

namespace ArmijoGrad.Conv

/-- THEOREM (§2), pp. 1–2. If `0 < δ ≤ 1/4K`, then for any `x ∈ S(x₀)` the set `S*(x, δ)` of (1)
is a nonempty subset of `S(x₀)`, and any sequence with `x₀` as first term and
`x_{k+1} ∈ S*(x_k, δ)` converges to the minimizer `x*`. -/
theorem convergence_theorem {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (hbdd : BddBelow (Set.range f)) (x0 : EuclideanSpace ℝ (Fin n)) (K : ℝ)
    (hIII : ConditionIII f x0 K) (xstar : EuclideanSpace ℝ (Fin n))
    (hIV : ConditionIV f x0 xstar) (δ : ℝ) (hδ : 0 < δ) (hδK : δ ≤ 1 / (4 * K)) :
    (∀ x ∈ levelSet f x0, (sdSet f x δ).Nonempty ∧ sdSet f x δ ⊆ levelSet f x0) ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x0 → (∀ k, x (k + 1) ∈ sdSet f (x k) δ) →
        Tendsto x atTop (𝓝 xstar) := by sorry

end ArmijoGrad.Conv
