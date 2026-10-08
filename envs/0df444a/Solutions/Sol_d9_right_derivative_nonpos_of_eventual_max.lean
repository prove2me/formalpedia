-- Prove2me | solution 1 for d9_right_derivative_nonpos_of_eventual_max
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T13:26:11.925977+00:00
-- url     : https://prove2.me/submissions/0db0cb5c-3bd2-4158-9752-dde3f65225ad

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open NestedSeatAlloc.IntPolicy
open scoped Topology
theorem solution
    (g : ℝ → ℝ) (p r : ℝ)
    (hderiv : HasDerivWithinAt g r (Set.Ici p) p)
    (hmax : ∀ᶠ u in 𝓝[Set.Ici p \ {p}] p, g u ≤ g p) :
    r ≤ 0 := by
  have hpunctured : Set.Ici p \ {p} = Set.Ioi p := by
    ext u
    change (p ≤ u ∧ u ≠ p) ↔ p < u
    constructor
    · rintro ⟨hpu, hne⟩
      exact lt_of_le_of_ne hpu (Ne.symm hne)
    · intro h
      exact ⟨le_of_lt h, ne_of_gt h⟩
  let l : Filter ℝ := 𝓝[Set.Ici p \ {p}] p
  have hl : Filter.NeBot l := by
    dsimp [l]
    rw [hpunctured]
    exact nhdsWithin_Ioi_neBot (a := p) (b := p) le_rfl
  letI : Filter.NeBot l := hl
  have hlim : Filter.Tendsto (fun u => slope g p u) l (𝓝 r) :=
    hasDerivWithinAt_iff_tendsto_slope.mp hderiv
  have hnonpos : ∀ᶠ u in l, slope g p u ≤ 0 := by
    filter_upwards [hmax, self_mem_nhdsWithin] with u huMax hu
    have hmem : u ∈ Set.Ici p ∧ u ∉ ({p} : Set ℝ) := by
      change u ∈ Set.Ici p ∧ u ∉ ({p} : Set ℝ) at hu
      exact hu
    have hpu : p ≤ u := Set.mem_Ici.mp hmem.1
    have hne : u ≠ p := by simpa using hmem.2
    have hlt : p < u := lt_of_le_of_ne hpu (Ne.symm hne)
    have hnum : g u - g p ≤ 0 := sub_nonpos.mpr huMax
    have hden : 0 ≤ u - p := sub_nonneg.mpr (le_of_lt hlt)
    have hquot : (g u - g p) / (u - p) ≤ 0 :=
      div_nonpos_iff.mpr (Or.inr ⟨hnum, hden⟩)
    simpa [slope, div_eq_mul_inv, mul_comm] using hquot
  exact le_of_tendsto hlim hnonpos
