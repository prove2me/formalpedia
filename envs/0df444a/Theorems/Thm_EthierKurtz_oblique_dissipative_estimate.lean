-- Prove2me | Theorems.Thm_EthierKurtz_oblique_dissipative_estimate
-- name    : EthierKurtz.oblique_dissipative_estimate
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T04:32:27.134179+00:00
-- url     : https://prove2.me/theorems/7f173dd7-697b-4c41-9723-22560b4722ab
-- title:
--   Dissipative estimate for the reflected graph
-- statement:
--   Dissipative estimate for the closed reflected diffusion graph.
--
--   Let $\Omega \subset \mathbb{R}^{n+1}$ be a bounded connected open set with
--   $C^{2,\mu}$ boundary, and let $L = \tfrac{1}{2}\sum a_{ij}\partial_{ij} +
--   \sum b_i\partial_i$ be uniformly elliptic with H\"older coefficients.
--   Let $c$ be a $C^{1,\mu}$ reflection field uniformly oblique to the outward
--   unit normal, and let $A$ be the closure of the operator graph defined by the
--   interior equation (1.15) with the oblique boundary condition (1.19)--(1.20).
--   Then every pair $(f, g) \in A$ satisfies the dissipative resolvent bound
--
--   $$
--   \lambda \lVert f\rVert \le \lVert \lambda f - g\rVert
--   \qquad \text{for all } \lambda > 0.
--   $$
--
--   This is the positive-maximum-principle half of the Hille--Yosida argument:
--   at an interior maximum the elliptic operator is nonpositive, and the oblique
--   boundary condition rules out a boundary maximum, so the estimate passes from
--   the graph to its closure by continuity of the norm.
--
--   **Formalization Note** Lean states the bound over bounded continuous functions
--   on $closure~\Omega$, with $A := closure~(obliqueDiffusionGraph~\Omega~\mu~a~b~c)$.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378); positive maximum principle for (1.15) with (1.19)--(1.20).

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Dissipative estimate for the closed reflected graph: on the closure of
the graph (1.20), every pair satisfies the resolvent bound of a dissipative
operator, by the positive maximum principle for the uniformly elliptic
interior operator and the oblique boundary condition. -/
theorem oblique_dissipative_estimate (n : ℕ) (hd : 2 ≤ n + 1)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) (hconnected : IsConnected Ω)
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (hboundary : BoundaryCTwiceHolder Ω μ)
    (a : EuclideanSpace ℝ (Fin (n + 1)) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (ha : ∀ x ∈ Ω, (a x).PosSemidef)
    (haHolder : ∀ i j, ComponentHolder Ω μ (fun x => a x i j))
    (hbHolder : ∀ i, ComponentHolder Ω μ (fun x => b x i))
    (helliptic : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ Ω,
      ∀ θ : EuclideanSpace ℝ (Fin (n + 1)), ‖θ‖ = 1 →
        ε ≤ ∑ i, ∑ j, θ i * a x i j * θ j)
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω,
      ε ≤ ∑ i, c x i * normal x i) :
    ∀ fg ∈ closure (obliqueDiffusionGraph Ω μ a b c),
      ∀ lam : ℝ, 0 < lam → lam * ‖fg.1‖ ≤ ‖lam • fg.1 - fg.2‖ := by sorry
