-- Prove2me | Theorems.Thm_EthierKurtz_oblique_halfspace_model_solvability
-- name    : EthierKurtz.oblique_halfspace_model_solvability
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T20:04:15.142358+00:00
-- url     : https://prove2.me/theorems/502049df-baed-4fe3-a0cd-98e1e4250634
-- title:
--   Half-space model solvability for the oblique Laplacian resolvent
-- statement:
--   This is the frozen-coefficient model problem for the oblique Laplacian resolvent.\n\nOn the open half-space $\\{x : x_0 > 0\\}$ in $\\mathbb{R}^{n+1}$, with identity diffusion, no drift, and constant oblique direction $-e_0$ (uniformly transverse to the boundary, since the outward unit normal is $-e_0$), exact resolvent solvability holds: there is a rate $\\lambda_0 > 0$ such that every H\\\"older right-hand side $h$ is hit, $\\lambda_0 f - g = h$, by a classical pair $(f, g)$ in the reflected graph.\n\nLocally straightening the $C^{2,\\mu}$ boundary and freezing the oblique field reduces the base problem on a general region to this model, so it is the endpoint that the localization assembly consumes.\n\n**Formalization Note** The half-space is the Lean set-builder `{x | 0 < x 0}`; the constant field is `EuclideanSpace.single 0 (-1)`. The domain is unbounded, so no boundedness hypothesis appears; the proof is the explicit constant-coefficient theory (reflection and Poisson-kernel methods).
-- source:
--   Half-space model problem with constant oblique direction for the Laplacian: explicit solvability via reflection and Poisson-kernel methods; cf. Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Chapter 6 (constant-coefficient oblique theory); as used in Ethier-Kurtz, Markov Processes, Chapter 8, Section 1.

import Definitions.Def_EthierKurtz_obliqueDiffusionGraph

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Half-space model solvability for the oblique Laplacian resolvent:
on the open half-space with identity diffusion, no drift, and constant
oblique direction, every Hölder right-hand side is hit exactly. This is
the frozen-coefficient model problem that localization reduces to. -/
theorem oblique_halfspace_model_solvability (n : ℕ) (hd : 2 ≤ n + 1)
    (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧
      ∀ (h : (closure {x : EuclideanSpace ℝ (Fin (n + 1)) |
        (0 : ℝ) < x (0 : Fin (n + 1))}) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph
          {x : EuclideanSpace ℝ (Fin (n + 1)) |
            (0 : ℝ) < x (0 : Fin (n + 1))} μ (fun _ => 1) (fun _ => 0)
          (fun _ => EuclideanSpace.single (0 : Fin (n + 1)) (-1 : ℝ)),
          lam₀ • fg.1 - fg.2 = h := by sorry

end EthierKurtz
