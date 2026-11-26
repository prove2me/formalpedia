-- Prove2me | solution 1 for proposition_1_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:33:28.077724+00:00
-- url     : https://prove2.me/submissions/da29816a-81ab-47d8-b448-8f680871bc89

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Theorems.Thm_isInjectiveSpace_sierpinski_power

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
theorem _root_.solution (X : Type u) [TopologicalSpace X] [T0Space X] :
    IsInjectiveSpace.{u,u} (Opens X → Prop) ∧
      IsEmbedding (productOfMemOpens X) := by
  refine ⟨?_, productOfMemOpens_isEmbedding X⟩
  exact isInjectiveSpace_sierpinski_power (Opens X)
