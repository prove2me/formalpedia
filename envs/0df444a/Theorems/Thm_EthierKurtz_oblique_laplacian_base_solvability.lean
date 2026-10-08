-- Prove2me | Theorems.Thm_EthierKurtz_oblique_laplacian_base_solvability
-- name    : EthierKurtz.oblique_laplacian_base_solvability
-- status  : Open
-- author  : @caleb
-- created : 2026-10-07T18:37:14.10004+00:00
-- url     : https://prove2.me/theorems/f0119421-052f-4535-b23c-0be3501204a1
-- title:
--   Laplacian base-case solvability for the oblique resolvent problem
-- statement:
--   This is the starting point of the continuity homotopy for the oblique-derivative resolvent problem.\n\nOn a bounded connected $C^{2,\\mu}$ region with a $C^{1,\\mu}$ uniformly oblique field $c$, the constant-coefficient base problem --- identity diffusion, no drift, same oblique field --- is exactly solvable: there is a rate $\\lambda_0 > 0$ such that every H\\\"older right-hand side $h$ is hit, $\\lambda_0 f - g = h$, by a classical pair $(f, g)$ in the reflected graph.\n\nThe method of continuity deforms this base operator into the full variable-coefficient operator while keeping the oblique boundary condition fixed; this child supplies the solvable endpoint of that homotopy.\n\n**Formalization Note** The base graph is `obliqueDiffusionGraph` instantiated with `(fun _ => 1)` diffusion and `(fun _ => 0)` drift; no hypotheses on variable coefficients are needed.
-- source:
--   Constant-coefficient oblique base case (Laplacian with uniformly oblique boundary field): Gilbarg-Trudinger, Elliptic Partial Differential Equations of Second Order, Chapter 6 (constant-coefficient theory); as used in Ethier-Kurtz, Markov Processes, Chapter 8, Section 1.

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Laplacian base-case solvability for the oblique resolvent problem:
with identity diffusion, no drift, and the same uniformly oblique field,
every Hölder right-hand side is hit exactly. This is the starting point
of the continuity homotopy. -/
theorem oblique_laplacian_base_solvability (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ ∀ (h : (closure Ω) →ᵇ ℝ) (C : NNReal),
      HolderWith C ⟨μ, hμ.1.le⟩ ⇑h →
        ∃ fg ∈ obliqueDiffusionGraph Ω μ (fun _ => 1) (fun _ => 0) c,
          lam₀ • fg.1 - fg.2 = h := by sorry

end EthierKurtz
