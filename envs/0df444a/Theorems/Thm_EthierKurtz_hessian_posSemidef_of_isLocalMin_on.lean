-- Prove2me | Theorems.Thm_EthierKurtz_hessian_posSemidef_of_isLocalMin_on
-- name    : EthierKurtz.hessian_posSemidef_of_isLocalMin_on
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T21:18:16.327095+00:00
-- url     : https://prove2.me/theorems/5d296c9f-20ca-49ea-badc-48948035b454
-- title:
--   Hessian PSD at a local minimizer, localized to a neighborhood
-- statement:
--   This is the Hessian positive-semidefiniteness criterion at a local minimizer, localized to a neighborhood.
--
--   Let $d$ be a natural number, let $f : \mathrm{EuclideanSpace}(\mathbb{R}, \mathrm{Fin}\,d) \to \mathbb{R}$, let $x_0$ be a point and $s$ a set with $s \in \mathcal{N}(x_0)$. Suppose $f$ is twice continuously differentiable on $s$ and attains a local minimum at $x_0$. Then for every direction $v$,
--
--   $$
--   \langle D^2 f(x_0) v, v \rangle \ge 0.
--   $$
--
--   Unlike the global version, this applies to functions that are only known to be regular near the minimizer, such as H\"older functions arising as resolvent-graph components on a domain. It is the form needed at interior minimum points in maximum-principle arguments.
--
--   **Formalization Note** The quadratic form is expressed as `(fderiv ℝ (fun y => fderiv ℝ f y v) x₀) v`, and twice continuous differentiability on $s$ as `ContDiffOn ℝ 2 f s`.
-- source:
--   Second partial derivative test, necessary direction, localized version. https://en.wikipedia.org/wiki/Second_partial_derivative_test

import Mathlib

open scoped Topology

namespace EthierKurtz

theorem hessian_posSemidef_of_isLocalMin_on {d : ℕ}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    {s : Set (EuclideanSpace ℝ (Fin d))}
    (hs : ContDiffOn ℝ 2 f s) (hmem : s ∈ 𝓝 x₀)
    (hmin : IsLocalMin f x₀) (v : EuclideanSpace ℝ (Fin d)) :
    0 ≤ (fderiv ℝ (fun y => fderiv ℝ f y v) x₀) v := by sorry

end EthierKurtz
