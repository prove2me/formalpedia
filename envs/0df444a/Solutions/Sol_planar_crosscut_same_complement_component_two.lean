-- Prove2me | solution 1 for planar_crosscut_same_complement_component_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:28:56.433718+00:00
-- url     : https://prove2.me/submissions/163ae9d2-a610-42e1-b2bf-eab20c7c05bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Set.Card
import Mathlib.Topology.ContinuousOn
import Theorems.Thm_planar_crosscut_same_complement_component_two_upper__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4
import Theorems.Thm_planar_crosscut_same_complement_component_two_lower__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4

open Set

theorem solution
    (U : Set (ℝ × ℝ)) (a : ℝ → ℝ × ℝ)
    (hUopen : IsOpen U) (hUconn : IsConnected U)
    (ha : ContinuousOn a (Icc (0 : ℝ) 1)) (hinj : InjOn a (Icc (0 : ℝ) 1))
    (hinside : a '' Ioo (0 : ℝ) 1 ⊆ U)
    (hzero : a 0 ∈ frontier U) (hone : a 1 ∈ frontier U)
    (hsame : a 1 ∈ connectedComponentIn Uᶜ (a 0)) :
    Finite (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ))) ∧
      Nat.card (ConnectedComponents ((U \ (a '' Icc (0 : ℝ) 1)) : Set (ℝ × ℝ))) = 2 := by
  have hu := planar_crosscut_same_complement_component_two_upper__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4
    (U := U) (a := a) hUopen hUconn ha hinj hinside hzero hone hsame
  have hl := planar_crosscut_same_complement_component_two_lower__p2m_701f7db2_54c5_46ad_a4c7_3073537171ce_a4
    (U := U) (a := a) hUopen hUconn ha hinj hinside hzero hone hsame hu.1
  exact ⟨hu.1, le_antisymm hu.2 hl⟩