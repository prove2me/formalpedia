-- Prove2me | solution 1 for t0_isEmbedding_into_sierpinski_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:09.466614+00:00
-- url     : https://prove2.me/submissions/69d520ef-d44d-4089-bceb-90a5ce01e7cf

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Theorems.Thm_proposition_1_5

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
theorem _root_.solution (X : Type u) [TopologicalSpace X] [T0Space X] :
    IsEmbedding (productOfMemOpens X) :=
  (proposition_1_5 X).2
