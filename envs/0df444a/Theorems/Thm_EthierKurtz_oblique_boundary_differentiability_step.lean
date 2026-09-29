-- Prove2me | Theorems.Thm_EthierKurtz_oblique_boundary_differentiability_step
-- name    : EthierKurtz.oblique_boundary_differentiability_step
-- status  : Disproved
-- author  : @caleb
-- created : 2026-09-27T21:18:23.922621+00:00
-- url     : https://prove2.me/theorems/fdd20755-ce26-40de-8305-66884e8e00c4
-- title:
--   Up-to-the-boundary differentiability of graph components
-- statement:
--   This is the up-to-the-boundary differentiability step for graph components.
--
--   Let $u$ be twice continuously differentiable inside an open set $\Omega$ and continuous on its closure. Suppose the interior gradients extend continuously to the closure, i.e. there is a continuous map $J$ with $J(x) = Du(x)$ at every interior point. Then at every frontier point $x_0$, $u$ is differentiable with derivative $J(x_0)$.
--
--   This packages the Schauder up-to-the-boundary gradient estimate used along reflecting boundaries: it turns the continuous boundary gradient supplied by the graph definition into a genuine derivative, which the Hopf-type boundary step then consumes.
--
--   **Formalization Note** The conclusion is `HasFDerivAt u (J x_0) x_0`; its proof is the $C^1$ Schauder estimate up to the boundary.
-- source:
--   Boundary gradient estimate: continuous extension of interior gradients is the derivative at frontier points (Schauder $C^1$ estimate up to the boundary), cf. Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Chapter 6; as used for reflecting diffusions in Ethier-Kurtz, Markov Processes, Chapter 4.

import Mathlib

open scoped Topology

namespace EthierKurtz

theorem oblique_boundary_differentiability_step {d : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {x₀ : EuclideanSpace ℝ (Fin d)}
    {J : (closure Ω) → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)}
    (hx : x₀ ∈ frontier Ω) (hxmem : x₀ ∈ closure Ω)
    (hC : ContDiffOn ℝ 2 u Ω)
    (hcont : ContinuousOn u (closure Ω))
    (hJc : Continuous J)
    (hJid : ∀ x : (closure Ω), (x : EuclideanSpace ℝ (Fin d)) ∈ Ω →
      J x = fderiv ℝ u x) :
    HasFDerivAt u (J ⟨x₀, hxmem⟩) x₀ := by sorry

end EthierKurtz
