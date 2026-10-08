-- Prove2me | Theorems.Thm_BellmanDP_Inventory_renewal_equation_exists_unique
-- name    : BellmanDP.Inventory.renewal_equation_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T16:42:26.308976+00:00
-- url     : https://prove2.me/theorems/81affc8b-3890-462d-a9c2-8a76c6b473f3
-- title:
--   Appendix to Chapter V, Theorem 9 — existence, uniqueness, approximation, derivative and positivity for the renewal equation
-- statement:
--   Let $f$ be measurable and bounded on every finite interval $[0,x_0]$, and let $\varphi$ be integrable on $(0,\infty)$ with
--   $$\int_0^\infty |\varphi(s)|\,ds < 1.$$
--   Consider the renewal equation
--   $$u(x) = f(x) + \int_0^x u(x-s)\varphi(s)\,ds, \qquad x \ge 0.$$
--
--   1. It has exactly one solution $u$ among measurable functions bounded on every finite interval (uniqueness on $[0,\infty)$).
--   2. $u$ is the pointwise limit on $[0,\infty)$ of $u_0 = f$, $u_{n+1}(x) = f(x) + \int_0^x u_n(x-s)\varphi(s)\,ds$.
--   3. If $f$ is continuously differentiable and $\varphi$ is continuous on $[0,\infty)$, then $u$ is differentiable at every $x > 0$ and
--   $$u'(x) = f'(x) + u(0)\varphi(x) + \int_0^x u'(x-s)\varphi(s)\,ds.$$
--   4. If $f \ge 0$ and $\varphi \ge 0$ on $[0,\infty)$, then $u \ge 0$ on $[0,\infty)$.
--
--   The positivity clause is what the proof of Chapter V, Theorem 1 uses to show that the marginal cost $F'(x) + k$ is positive beyond the critical level.
--
--   **Formalization Note** The book assumes only that $f$ is differentiable in clause 3; the statement assumes $f$ continuously differentiable (on $\mathbb R$; any $C^1$ function on $[0,\infty)$ extends), which keeps $\int_0^x u'(x-s)\varphi(s)\,ds$ meaningful. The derivative identity is asserted for $x > 0$. Solutions are required to be measurable.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Appendix to Chapter V, Theorem 9, p. 178 (equation (1), p. 177; approximations (4), p. 178)

import Mathlib
import Definitions.Def_BellmanDP_Inventory_Model

open MeasureTheory Filter Topology

namespace BellmanDP.Inventory

/-- Bellman, *Dynamic Programming*, Appendix to Ch. V, Theorem 9, p. 178. If `f` is measurable
and bounded on every finite interval `[0, x₀]` and `∫_0^∞ |φ(s)| ds < 1`, the renewal equation
`u(x) = f(x) + ∫_0^x u(x − s) φ(s) ds` has exactly one solution (among measurable functions)
bounded on every `[0, x₀]`; it is the pointwise limit of the approximations (4); if `f` is
continuously differentiable and `φ` continuous on `[0, ∞)`, then for `x > 0`
`u′(x) = f′(x) + u(0) φ(x) + ∫_0^x u′(x − s) φ(s) ds`; and if `f ≥ 0`, `φ ≥ 0` on `[0, ∞)`,
then `u ≥ 0` there. -/
theorem renewal_equation_exists_unique (f φ : ℝ → ℝ)
    (hf_meas : Measurable f)
    (hf_bdd : ∀ x₀ : ℝ, 0 ≤ x₀ → ∃ M : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) x₀, |f x| ≤ M)
    (hφ_int : IntegrableOn φ (Set.Ioi 0))
    (hφ_lt : ∫ s in Set.Ioi 0, |φ s| < 1) :
    ∃ u : ℝ → ℝ, LocallyBoundedClass u ∧ IsRenewalSolution f φ u ∧
      (∀ v : ℝ → ℝ, LocallyBoundedClass v → IsRenewalSolution f φ v →
        Set.EqOn v u (Set.Ici 0)) ∧
      (∀ x : ℝ, 0 ≤ x → Tendsto (fun n => renewalIter f φ n x) atTop (𝓝 (u x))) ∧
      (ContDiff ℝ 1 f → ContinuousOn φ (Set.Ici 0) →
        ∀ x : ℝ, 0 < x → HasDerivAt u
          (deriv f x + u 0 * φ x + ∫ s in (0 : ℝ)..x, deriv u (x - s) * φ s) x) ∧
      ((∀ x : ℝ, 0 ≤ x → 0 ≤ f x) → (∀ x : ℝ, 0 ≤ x → 0 ≤ φ x) →
        ∀ x : ℝ, 0 ≤ x → 0 ≤ u x) := by sorry

end BellmanDP.Inventory
