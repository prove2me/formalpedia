-- Prove2me | Theorems.Thm_EthierKurtz_oblique_closure_singlevalued
-- name    : EthierKurtz.oblique_closure_singlevalued
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T02:16:28.958157+00:00
-- url     : https://prove2.me/theorems/74866daf-8eee-42cf-8fea-78c2ab50360d
-- title:
--   Single-valuedness of the closed reflected graph
-- statement:
--   Single-valuedness of the closed reflected diffusion graph.
--
--   Let $\Omega \subset \mathbb{R}^{n+1}$ be a bounded connected open set with
--   $C^{2,\mu}$ boundary, and let $L = \tfrac{1}{2}\sum a_{ij}\partial_{ij} +
--   \sum b_i\partial_i$ be uniformly elliptic with H\"older coefficients.
--   Let $c$ be a $C^{1,\mu}$ reflection field uniformly oblique to the outward
--   unit normal on the boundary, and let $G$ be the operator graph defined by the
--   interior equation (1.15) together with the oblique boundary condition
--   $Jc = 0$ of (1.19)--(1.20). With $A$ the closure of $G$ in
--   $C(\bar\Omega) \times C(\bar\Omega)$, we have
--
--   $$
--   (f, g_1) \in A \text{ and } (f, g_2) \in A \implies g_1 = g_2.
--   $$
--
--   That is, closing the graph never pairs one function with two distinct images;
--   $A$ is the graph of a (single-valued) operator. This is the dissipativity /
--   positive-maximum-principle half of Theorem 1.5.
--
--   **Formalization Note** Lean states the conclusion with
--   $A := closure~(obliqueDiffusionGraph~\Omega~\mu~a~b~c)$ and quantifies over
--   bounded continuous functions on $closure~\Omega$.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378); graph (1.20) and boundary equations (1.19)--(1.20).

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Single-valuedness of the closed obliquely reflected diffusion graph:
under the hypotheses of Theorem 1.5, no continuous function on the closed
region is paired with two distinct images in the closure of the graph. -/
theorem oblique_closure_singlevalued (n : ℕ) (hd : 2 ≤ n + 1)
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
    let A := closure (obliqueDiffusionGraph Ω μ a b c)
    ∀ f g₁ g₂, (f, g₁) ∈ A → (f, g₂) ∈ A → g₁ = g₂ := by sorry
