-- Prove2me | Theorems.Thm_Erdos146_pairChildArrayEntropy_empirical_bound
-- name    : Erdos146.pairChildArrayEntropy_empirical_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:46:36.340803+00:00
-- url     : https://prove2.me/theorems/1148d9a8-9c3a-4440-8691-7a152b5282db
-- title:
--   Array-level empirical entropy bound
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. Summing the coordinatewise bound gives the bound on $E(u,z)$ for a whole child array — the quantity Lemma 7.1 thresholds at $\beta - \delta$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L14239-L14409

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairChildArrayEntropy_empirical_bound
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : PairLayer parentCount 1 → HammingWord dimension) :
    pairChildArrayEntropy parents children ≤
      kappa +
        logTwo 3 *
          pairChildArrayAverageDisagreement hparents parents children +
        (pairChildArrayEntropyPotential children -
          pairParentArrayEntropyPotential parents) / 2 +
        empiricalEntropyError parentCount := by sorry
