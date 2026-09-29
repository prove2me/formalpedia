-- Prove2me | Theorems.Thm_EthierKurtz_oblique_resolvent_positive
-- name    : EthierKurtz.oblique_resolvent_positive
-- status  : Open
-- author  : @caleb
-- created : 2026-09-27T13:49:39.159908+00:00
-- url     : https://prove2.me/theorems/2a6a2cc1-d4ac-427e-8a4a-e3830352893a
-- title:
--   Resolvent positivity on the reflected graph
-- statement:
--   Resolvent positivity on the reflected graph.
--
--   Under the hypotheses of Theorem 1.5 (bounded connected $C^{2,\mu}$ region,
--   uniformly elliptic operator with H\"older coefficients, uniformly oblique
--   $C^{1,\mu}$ reflection field), the resolvent map of the reflected graph is
--   positive: for every graph pair and every positive rate, a nonnegative
--   resolvent image forces a nonnegative source,
--
--   $$
--   \lambda f - g \ge 0 \implies f \ge 0 \qquad (\lambda > 0).
--   $$
--
--   This is the positive maximum principle in resolvent form: at an interior
--   minimum the elliptic operator is nonnegative, and the oblique boundary
--   condition rules out a negative boundary minimum.
--
--   **Formalization Note** Lean quantifies over pairs in
--   $obliqueDiffusionGraph~\Omega~\mu~a~b~c$ and concludes pointwise
--   nonnegativity on $closure~\Omega$.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378); positive maximum principle with (1.19)--(1.20).

import Definitions.Def_EthierKurtz_BoundaryCTwiceHolder
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_obliqueDiffusionGraph
import Definitions.Def_EthierKurtz_IsStronglyContinuousContractionSemigroup

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Resolvent positivity on the reflected graph: if a graph pair satisfies
the resolvent inequality for a positive rate, its first component is
nonnegative, by the positive maximum principle for the uniformly elliptic
interior operator with the oblique boundary condition. -/
theorem oblique_resolvent_positive (n : ℕ) (hd : 2 ≤ n + 1)
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
    ∀ fg ∈ obliqueDiffusionGraph Ω μ a b c, ∀ lam : ℝ, 0 < lam →
      (∀ x, 0 ≤ (lam • fg.1 - fg.2) x) → ∀ x, 0 ≤ fg.1 x := by sorry
