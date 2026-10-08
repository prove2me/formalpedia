-- Prove2me | solution 1 for d9_eventual_right_max_of_all_seat_dominance
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:06:51.541727+00:00
-- url     : https://prove2.me/submissions/f012ad15-924f-4716-9e2c-810403cb908a

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
    (j n : ℕ) (s : ℝ) (hpj : 0 ≤ p j) (hs : 0 ≤ s)
    (hprev : ∀ t, 0 ≤ t → ∀ q, IsProtectionPolicy q →
      expRevenue P X f q n t ≤ expRevenue P X f p n t)
    (hupdate : ∀ u, 0 ≤ u → IsProtectionPolicy (Function.update p j u)) :
    ∀ᶠ u in 𝓝[Set.Ici (p j) \ {p j}] (p j),
      expRevenue P X f (Function.update p j u) n s ≤
        expRevenue P X f p n s := by
  filter_upwards [self_mem_nhdsWithin] with u hu
  change u ∈ Set.Ici (p j) ∧ u ∉ ({p j} : Set ℝ) at hu
  have huge : p j ≤ u := Set.mem_Ici.mp hu.1
  have hu0 : 0 ≤ u := le_trans hpj huge
  have hdom := hprev s hs (Function.update p j u) (hupdate u hu0)
  simpa using hdom
