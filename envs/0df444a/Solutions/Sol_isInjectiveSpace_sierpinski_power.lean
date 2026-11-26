-- Prove2me | solution 1 for isInjectiveSpace_sierpinski_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:45.383098+00:00
-- url     : https://prove2.me/submissions/f7db2059-a7a6-41a1-897a-e85de6260df8

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Theorems.Thm_proposition_1_2
import Theorems.Thm_proposition_1_3

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
theorem _root_.solution (ι : Type w) :
    IsInjectiveSpace.{u} (ι → Prop) :=
  proposition_1_3 (fun (_ : ι) => Prop) (fun _ => proposition_1_2)
