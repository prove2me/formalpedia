-- Prove2me | Theorems.Thm_EthierKurtz_resolvent_positive_boundary_step
-- name    : EthierKurtz.resolvent_positive_boundary_step
-- status  : Disproved
-- author  : @caleb
-- created : 2026-09-27T21:18:34.044884+00:00
-- url     : https://prove2.me/theorems/e157d805-ed34-420d-8d02-fc8e6728351f
-- title:
--   Boundary maximum-principle step for resolvent positivity
-- statement:
--   This is the boundary step of the positive maximum principle for the resolvent problem with oblique boundary condition.
--
--   Let $\Omega \subset \mathbb{R}^{n+1}$ have twice-H\"older boundary, and let $x_0$ be a frontier point where a function $u$, twice continuously differentiable inside $\Omega$ and continuous up to the closure, attains its global minimum $u(x_0) < 0$. Suppose the oblique boundary data are satisfied at $x_0$: the boundary gradient $J_0$ annihilates the obliquefield $c(x_0)$, and $c(x_0)$ is uniformly transverse to the outward unit normal. Suppose further that the elliptic identity and the resolvent inequality hold as stated. Then this situation is impossible.
--
--   This is the Hopf-boundary-point step of the argument: at a boundary minimum, either the Hopf lemma forces a strictly positive outward normal derivative, contradicting the homogeneous oblique condition, or the degenerate case is ruled out through the operator identity. It isolates the entire boundary analysis of the resolvent-positivity proof in one reusable statement.
--
--   **Formalization Note** Boundary regularity and the outward normal are the mission predicates `BoundaryCTwiceHolder` and `IsOutwardUnitNormal`; the boundary gradient is the value at $x_0$ of the continuous extension supplied by `EthierKurtz.oblique_boundary_differentiability_step`.
-- source:
--   Hopf boundary-point step with oblique boundary condition, cf. Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Lemma 3.4 (Hopf) and Section 6.4 (oblique derivative problems); as used for reflecting diffusions in Ethier-Kurtz, Markov Processes, Chapter 4.

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

theorem resolvent_positive_boundary_step {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin (n + 1)))} {μ : ℝ}
    {a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    {b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    {u g : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} {x₀ : EuclideanSpace ℝ (Fin (n + 1))}
    {J0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ} {lam : ℝ}
    (hx : x₀ ∈ frontier Ω)
    (hboundary : BoundaryCTwiceHolder Ω μ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hC : ContDiffOn ℝ 2 u Ω)
    (hcont : ContinuousOn u (closure Ω))
    (hcontG : ContinuousOn g (closure Ω))
    (hD : HasFDerivAt u J0 x₀)
    (hJ0b : J0 (c x₀) = 0)
    (hnor : IsOutwardUnitNormal Ω x₀ (normal x₀))
    (hob : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ∑ i, c x₀ i * normal x₀ i)
    (hIdΩ : ∀ x ∈ Ω, g x = (1 / 2 : ℝ) * (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      a x i j * fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single j 1)) x
        (EuclideanSpace.single i 1)) + fderiv ℝ u x (b x))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (hell : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hminglob : ∀ y ∈ closure Ω, u x₀ ≤ u y)
    (hu0 : u x₀ < 0)
    (hlam : 0 < lam)
    (hop : 0 ≤ lam * u x₀ - g x₀) :
    False := by sorry

end EthierKurtz
