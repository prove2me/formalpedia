-- Prove2me | Theorems.Thm_Erdos146_empiricalConditionalEntropy_bound
-- name    : Erdos146.empiricalConditionalEntropy_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:43:41.593511+00:00
-- url     : https://prove2.me/theorems/201dd463-a000-44b8-9745-24ce577e4b62
-- title:
--   The empirical conditional entropy obeys the same bound
-- statement:
--   Step in the passage from the two-bit kernel of Section 5 to the array-level entropy functional $E(u,z)$ of Section 7, where the empirical distribution of a coordinate over a parent array replaces a fixed kernel. The empirical conditional entropy of a coordinate is bounded by the same constant $\kappa$ that bounds the idealised kernel, up to the empirical error term.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L11603-L11671

import Definitions.Def_erdos146_core2
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.empiricalConditionalEntropy_bound
    (parentCount oneCount : ℕ)
    (hparents : 4 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (kernel : BinaryPairKernel)
    (hparameter :
      kernel.parentProbability =
        (oneCount : ℝ) / (parentCount : ℝ)) :
    empiricalConditionalEntropy parentCount oneCount kernel ≤
      kappa + logTwo 3 *
          empiricalAverageDisagreement parentCount oneCount kernel +
        (binaryEntropy
            (empiricalChildMarginal parentCount oneCount kernel) -
          binaryEntropy kernel.parentProbability) / 2 +
        empiricalEntropyError parentCount := by sorry
