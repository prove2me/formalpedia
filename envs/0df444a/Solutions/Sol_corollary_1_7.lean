-- Prove2me | solution 1 for corollary_1_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:43:22.829896+00:00
-- url     : https://prove2.me/submissions/cc262cd6-038d-466d-9528-7f5ddd50596c

import Mathlib.Topology.ContinuousMap.T0Sierpinski
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Sets.Opens
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Theorems.Thm_IsInjectiveSpace_of_retract
import Theorems.Thm_isInjectiveSpace_sierpinski_power
import Theorems.Thm_proposition_1_5

set_option autoImplicit true
open Topology TopologicalSpace
universe u v w
theorem _root_.solution (D : Type u) [TopologicalSpace D] [T0Space D] :
    IsInjectiveSpace.{u,u} D ↔
      ∀ {Y : Type u} [TopologicalSpace Y] (e : D → Y), IsEmbedding e →
        ∃ r : C(Y, D), ∀ d, r (e d) = d := by
  constructor
  · intro hD Y _ e he
    obtain ⟨r, hr⟩ := hD e he (ContinuousMap.id D)
    exact ⟨r, hr⟩
  · intro hD
    obtain ⟨r, hr⟩ := hD (productOfMemOpens D) (proposition_1_5 D).2
    exact IsInjectiveSpace.of_retract (isInjectiveSpace_sierpinski_power (Opens D))
      (productOfMemOpens D) r hr
