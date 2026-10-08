-- Prove2me | solution 1 for d9_eventual_left_max_of_all_seat_dominance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:07:58.04999+00:00
-- url     : https://prove2.me/submissions/d5778dca-e5aa-4fcb-a869-023518ba8716

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open NestedSeatAlloc.IntPolicy
open scoped Topology
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (j n : ℕ) (s : ℝ) (hpj : 0 < p j) (hs : 0 ≤ s)
    (hprev : ∀ t, 0 ≤ t → ∀ q, IsProtectionPolicy q →
      expRevenue P X f q n t ≤ expRevenue P X f p n t)
    (hupdate : ∀ u, 0 ≤ u → IsProtectionPolicy (Function.update p j u)) :
    ∀ᶠ u in 𝓝[Set.Iic (p j) \ {p j}] (p j),
      expRevenue P X f (Function.update p j u) n s ≤
        expRevenue P X f p n s := by
  let l : Filter ℝ := 𝓝[Set.Iic (p j) \ {p j}] (p j)
  have hpos : ∀ᶠ u in l, 0 < u :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds hpj)
  filter_upwards [hpos] with u hupos
  exact hprev s hs (Function.update p j u)
    (hupdate u (le_of_lt hupos))
