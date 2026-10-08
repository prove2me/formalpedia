-- Prove2me | solution 1 for d9_left_derivative_nonneg_of_eventual_max
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:27:26.629975+00:00
-- url     : https://prove2.me/submissions/8cac249c-96fe-4771-85ca-7da85411cf9c

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open NestedSeatAlloc.IntPolicy
open scoped Topology
theorem solution
    (g : ℝ → ℝ) (p lval : ℝ)
    (hderiv : HasDerivWithinAt g lval (Set.Iic p) p)
    (hmax : ∀ᶠ u in 𝓝[Set.Iic p \ {p}] p, g u ≤ g p) :
    0 ≤ lval := by
  have hpunctured : Set.Iic p \ {p} = Set.Iio p := by
    ext u
    change (u ≤ p ∧ u ≠ p) ↔ u < p
    constructor
    · rintro ⟨hup, hne⟩
      exact lt_of_le_of_ne hup hne
    · intro h
      exact ⟨le_of_lt h, ne_of_lt h⟩
  let l : Filter ℝ := 𝓝[Set.Iic p \ {p}] p
  have hl : Filter.NeBot l := by
    dsimp [l]
    rw [hpunctured]
    exact nhdsWithin_Iio_neBot (a := p) (b := p) le_rfl
  letI : Filter.NeBot l := hl
  have hlim : Filter.Tendsto (fun u => slope g p u) l (𝓝 lval) :=
    hasDerivWithinAt_iff_tendsto_slope.mp hderiv
  have hnonpos : ∀ᶠ u in l, -slope g p u ≤ 0 := by
    filter_upwards [hmax, self_mem_nhdsWithin] with u huMax hu
    have hmem : u ∈ Set.Iic p ∧ u ∉ ({p} : Set ℝ) := by
      change u ∈ Set.Iic p ∧ u ∉ ({p} : Set ℝ) at hu
      exact hu
    have hup : u ≤ p := Set.mem_Iic.mp hmem.1
    have hne : u ≠ p := by simpa using hmem.2
    have hlt : u < p := lt_of_le_of_ne hup hne
    have hnum : g u - g p ≤ 0 := sub_nonpos.mpr huMax
    have hden : u - p ≤ 0 := sub_nonpos.mpr (le_of_lt hlt)
    have hquot : 0 ≤ (g u - g p) / (u - p) :=
      div_nonneg_iff.mpr (Or.inr ⟨hnum, hden⟩)
    have hslope : 0 ≤ slope g p u := by
      simpa [slope, div_eq_mul_inv, mul_comm] using hquot
    linarith
  have hlim' : Filter.Tendsto (fun u => -slope g p u) l (𝓝 (-lval)) := hlim.neg
  have hneg : -lval ≤ 0 := le_of_tendsto hlim' hnonpos
  linarith
