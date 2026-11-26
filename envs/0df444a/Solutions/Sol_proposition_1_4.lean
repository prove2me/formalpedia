-- Prove2me | solution 1 for proposition_1_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:05.733349+00:00
-- url     : https://prove2.me/submissions/c8ad1809-c5c6-48b1-a534-cca17eaf3c3e

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Theorems.Thm_IsInjectiveSpace_of_retract

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
theorem _root_.solution {D : Type v} {D' : Type v} [TopologicalSpace D] [TopologicalSpace D']
    (hD : IsInjectiveSpace.{u} D) (s : C(D', D)) (r : C(D, D')) (hrs : ∀ d, r (s d) = d) :
    IsInjectiveSpace.{u} D' :=
  IsInjectiveSpace.of_retract hD s r hrs
