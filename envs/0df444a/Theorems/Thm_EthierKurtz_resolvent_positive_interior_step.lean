-- Prove2me | Theorems.Thm_EthierKurtz_resolvent_positive_interior_step
-- name    : EthierKurtz.resolvent_positive_interior_step
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T21:18:19.224617+00:00
-- url     : https://prove2.me/theorems/072be6fb-491b-4905-b693-14052607cdff
-- title:
--   Interior maximum-principle step for resolvent positivity
-- statement:
--   This is the interior step of the positive maximum principle for the resolvent problem.
--
--   Let $\Omega \subset \mathbb{R}^d$ be open and $x_0 \in \Omega$. Let $u$ be twice continuously differentiable on $\Omega$ with a local minimum at $x_0$, a negative value $u(x_0) < 0$, and a positive-semidefinite Hessian quadratic form at $x_0$. Let $a(x_0)$ be positive-semidefinite and suppose the elliptic expression
--
--   $$
--   g = \tfrac{1}{2}\mathrm{tr}(a(x_0) D^2 u(x_0)) + Du(x_0) b(x_0)
--   $$
--
--   satisfies the resolvent inequality $0 \le \lambda u(x_0) - g$ for some rate $\lambda > 0$. Then this situation is impossible.
--
--   Indeed, Fermat's theorem kills the first-order term, the Hessian sign together with $a(x_0) \succeq 0$ makes the second-order term nonnegative, so $g \ge 0$ while $\lambda u(x_0) < 0$. This is the contradiction that rules out a negative interior minimum of a resolvent supersolution.
--
--   **Formalization Note** The Hessian-sign hypothesis is exactly the conclusion of the proved lemma `EthierKurtz.hessian_posSemidef_of_isLocalMin_on`, so a future proof of this step imports it directly.
-- source:
--   Interior weak maximum principle step for a uniformly elliptic operator at a minimum point, cf. Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Theorem 3.5; as used for reflecting diffusions in Ethier-Kurtz, Markov Processes, Chapter 4.

import Mathlib

open scoped Topology

namespace EthierKurtz

theorem resolvent_positive_interior_step {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ}
    {b : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    {gval lam : ℝ}
    (hopen : IsOpen Ω) (hx : x₀ ∈ Ω)
    (hC : ContDiffOn ℝ 2 u Ω)
    (hmin : IsLocalMin u x₀)
    (hH : ∀ v, 0 ≤ (fderiv ℝ (fun y => fderiv ℝ u y v) x₀) v)
    (ha : (a x₀).PosSemidef)
    (hId : gval = (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d,
      a x₀ i j * fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x₀
        (EuclideanSpace.single i 1)) + fderiv ℝ u x₀ (b x₀))
    (hlam : 0 < lam) (hu0 : u x₀ < 0)
    (hineq : 0 ≤ lam * u x₀ - gval) :
    False := by sorry

end EthierKurtz
