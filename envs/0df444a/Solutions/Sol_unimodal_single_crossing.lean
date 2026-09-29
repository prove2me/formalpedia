-- Prove2me | solution 1 for unimodal_single_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T18:21:06.193327+00:00
-- url     : https://prove2.me/submissions/58ec7737-88f9-4261-9962-964686cb888b

import Mathlib.Order.Monotone.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false

open Set

/-- **Siegel 2001, Theorem 2.1, p.5 — the single-crossing / intermediate-value step.**
If `g` is continuous on `[0,µ]`, strictly increasing on `[0,a]` and strictly decreasing on
`[a,µ]` (single interior maximum, `0 < a < µ`) with `g 0 < 0` and `g µ = 0`, then there is a
single crossing point `c ∈ (0,a)` with `g ≤ 0` on `[0,c]` and `g ≥ 0` on `[c,µ]`. -/
theorem solution
    (g : ℝ → ℝ) (μ a : ℝ)
    (ha0 : 0 < a) (haμ : a < μ)
    (hcont : ContinuousOn g (Icc 0 μ))
    (hinc : StrictMonoOn g (Icc 0 a))
    (hdec : StrictAntiOn g (Icc a μ))
    (hg0 : g 0 < 0)
    (hgμ : g μ = 0) :
    ∃ c, 0 < c ∧ c < a ∧
      (∀ x ∈ Icc (0:ℝ) c, g x ≤ 0) ∧ (∀ x ∈ Icc c μ, 0 ≤ g x) := by
  have haμ' : a ≤ μ := le_of_lt haμ
  have hga_pos : 0 < g a := by
    have hμmem : μ ∈ Icc a μ := ⟨haμ', le_refl μ⟩
    have hamem : a ∈ Icc a μ := ⟨le_refl a, haμ'⟩
    have := hdec hamem hμmem haμ
    rw [hgμ] at this
    exact this
  have hcont_0a : ContinuousOn g (Icc 0 a) :=
    hcont.mono (Icc_subset_Icc (le_refl 0) haμ')
  have h0a : (0:ℝ) ≤ a := ha0.le
  have hivt : (0:ℝ) ∈ g '' Icc 0 a := by
    apply intermediate_value_Icc h0a hcont_0a
    exact ⟨hg0.le, hga_pos.le⟩
  obtain ⟨c, hcmem, hgc⟩ := hivt
  obtain ⟨hc0, hca⟩ := hcmem
  have hcne0 : c ≠ 0 := by
    intro h; rw [h] at hgc; rw [hgc] at hg0; exact lt_irrefl 0 hg0
  have hcnea : c ≠ a := by
    intro h; rw [h] at hgc; rw [hgc] at hga_pos; exact lt_irrefl 0 hga_pos
  have hc0' : 0 < c := lt_of_le_of_ne hc0 (Ne.symm hcne0)
  have hca' : c < a := lt_of_le_of_ne hca hcnea
  refine ⟨c, hc0', hca', ?_, ?_⟩
  · intro x hx
    obtain ⟨hx0, hxc⟩ := hx
    rcases eq_or_lt_of_le hxc with h | h
    · rw [h, hgc]
    · have hxmem : x ∈ Icc (0:ℝ) a := ⟨hx0, hxc.trans hca⟩
      have hcmem' : c ∈ Icc (0:ℝ) a := ⟨hc0, hca⟩
      have := hinc hxmem hcmem' h
      rw [hgc] at this; exact this.le
  · intro x hx
    obtain ⟨hcx, hxμ⟩ := hx
    rcases le_or_gt x a with hxa | hax
    · rcases eq_or_lt_of_le hcx with h | h
      · rw [← h, hgc]
      · have hxmem : x ∈ Icc (0:ℝ) a := ⟨hc0.trans hcx, hxa⟩
        have hcmem' : c ∈ Icc (0:ℝ) a := ⟨hc0, hca⟩
        have := hinc hcmem' hxmem h
        rw [hgc] at this; exact this.le
    · rcases eq_or_lt_of_le hxμ with h | h
      · rw [h, hgμ]
      · have hxmem : x ∈ Icc a μ := ⟨hax.le, hxμ⟩
        have hμmem : μ ∈ Icc a μ := ⟨haμ', le_refl μ⟩
        have := hdec hxmem hμmem h
        rw [hgμ] at this; exact this.le
