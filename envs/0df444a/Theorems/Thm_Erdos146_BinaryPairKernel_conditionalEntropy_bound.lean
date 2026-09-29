-- Prove2me | Theorems.Thm_Erdos146_BinaryPairKernel_conditionalEntropy_bound
-- name    : Erdos146.BinaryPairKernel.conditionalEntropy_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:41:23.081982+00:00
-- url     : https://prove2.me/theorems/5ac8eb12-f317-4ee0-8081-336b46bdef63
-- title:
--   The pair kernel obeys the entropy bound $\kappa$
-- statement:
--   The conditional entropy $H(Z \mid X, Y)$ of a child bit given its two parent bits, maximised over admissible two-bit kernels, is at most the constant $\kappa$ of Section 5. This is the bound behind the threshold $A(\tau) = \kappa + \tau\log_2 3$: it is what makes an embedding of the layered graph raise a bounded entropy potential by a fixed amount at each layer, which is impossible after enough layers.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L10321-L10440

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open Erdos146
open Erdos146.BinaryPairKernel
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.BinaryPairKernel.conditionalEntropy_bound (kernel : BinaryPairKernel) :
    kernel.conditionalEntropy ≤
      kappa + logTwo 3 * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by sorry
