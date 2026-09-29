-- Prove2me | Theorems.Thm_Erdos146_pairGraphOverFin_free_of_manuscript_exclusion
-- name    : Erdos146.pairGraphOverFin_free_of_manuscript_exclusion
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:53:17.040526+00:00
-- url     : https://prove2.me/theorems/79d79d01-abfa-478a-b5ec-cc0d9d7f7d47
-- title:
--   Freeness under the manuscript parameter choice (Proposition 8.1)
-- statement:
--   **Proposition 8.1 (Exclusion of the layered graph).** With probability $1 - o(1)$ the sampled graph contains no copy of $H$. Step in the exclusion argument of Sections 7 and 8. The exclusion argument runs on the conditional-entropy functional $E(u,z) = \frac{1}{m}\sum_{j=1}^{m} H(Z_j \mid X_j, Y_j)$ of Section 7, where a parent pair is drawn uniformly and oriented by an independent fair coin. The thresholds are $A(\tau) = \kappa + \tau\log_2 3$ and $C(\tau) = 2h(\tau) - 1$, and the construction needs a sampling exponent $\beta$ with $A(\tau) < \beta < C(\tau)$. Lemma 7.1 excludes, with probability at least $1 - 2s\,2^{-m}$, any parent array of length $L_{i-1}$ together with a pairwise distinct retained child array of length $L_i$ satisfying $E(u,z) \le \beta - \delta$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L17915-L17937

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Real.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairGraphOverFin_free_of_manuscript_exclusion
    {baseSize depth dimension : ℕ}
    (hbase : 4 ≤ baseSize)
    (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * (certifiedWindowWidth / 2))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion :
      ∀ (side : Bool) (layer : Fin depth),
        retained ∉
          badPairLayerRetentionEvent
            (Fintype.card (PairLayer baseSize layer.val))
            dimension side (midpointBeta - entropySlack))
    (herror :
      ∀ layer : Fin depth,
        empiricalEntropyError
          (Fintype.card (PairLayer baseSize layer.val)) < entropySlack) :
    (pairGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension
        (manuscriptHammingRadius dimension) retained) := by sorry
