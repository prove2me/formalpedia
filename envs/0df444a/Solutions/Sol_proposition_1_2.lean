-- Prove2me | solution 1 for proposition_1_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:32:09.015066+00:00
-- url     : https://prove2.me/submissions/9161e66d-bd23-44a0-b846-d4098cd0b049

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Theorems.Thm_isInjectiveSpace_sierpinski

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
theorem _root_.solution : IsInjectiveSpace.{u} Sierpinski :=
  isInjectiveSpace_sierpinski
