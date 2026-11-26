-- Prove2me | solution 1 for proposition_1_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:15.113648+00:00
-- url     : https://prove2.me/submissions/a1a0fc25-75ed-44e8-ad2f-3d3dbae30399

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Theorems.Thm_IsInjectiveSpace_pi

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
theorem _root_.solution {ι : Type w} (D : ι → Type v) [∀ i, TopologicalSpace (D i)]
    (h : ∀ i, IsInjectiveSpace.{u} (D i)) : IsInjectiveSpace.{u} (∀ i, D i) :=
  IsInjectiveSpace.pi D h
