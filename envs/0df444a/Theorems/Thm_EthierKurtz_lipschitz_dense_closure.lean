-- Prove2me | Theorems.Thm_EthierKurtz_lipschitz_dense_closure
-- name    : EthierKurtz.lipschitz_dense_closure
-- status  : Proved
-- author  : @caleb
-- created : 2026-09-27T04:50:29.129103+00:00
-- url     : https://prove2.me/theorems/cefb9ae8-6654-42d6-94c4-d287caf6b008
-- title:
--   Uniform density of Lipschitz maps on the closed region
-- statement:
--   Uniform density of Lipschitz maps on the closed region.
--
--   Let $\Omega \subset \mathbb{R}^{n+1}$ be bounded. Every bounded continuous
--   function on the closure $\bar\Omega$ is uniformly approximable by Lipschitz
--   bounded continuous functions:
--
--   $$
--   \forall h,\ \forall \delta > 0,\ \exists h' \text{ Lipschitz},\quad
--   \lVert h' - h\rVert < \delta.
--   $$
--
--   This is the approximation-theoretic half of the dense-range argument: the
--   closure is compact metric, so Lipschitz maps are uniformly dense in
--   continuous maps. It needs none of the elliptic hypotheses.
--
--   **Formalization Note** Lean states this over $(closure~\Omega) \to^b~\mathbb{R}$
--   with Lipschitz constant $K : NNReal$; only boundedness of $\Omega$ is assumed.
-- source:
--   Approximation-theoretic lemma for Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986. Chapter 8, Section 1, Theorem 1.5, printed p. 369 (PDF p. 378).

import Mathlib

open Filter
open scoped Topology BoundedContinuousFunction

namespace EthierKurtz

/-- Uniform density of Lipschitz maps on the closed region: every bounded
continuous function on the closure of a bounded set is uniformly
approximable by Lipschitz bounded continuous functions, since the closure
is compact metric. -/
theorem lipschitz_dense_closure (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hbounded : Bornology.IsBounded Ω) :
    ∀ h : (closure Ω) →ᵇ ℝ, ∀ delta : ℝ, 0 < delta →
      ∃ h' : (closure Ω) →ᵇ ℝ, (∃ K : NNReal, LipschitzWith K ⇑h') ∧
        ‖h' - h‖ < delta := by sorry
