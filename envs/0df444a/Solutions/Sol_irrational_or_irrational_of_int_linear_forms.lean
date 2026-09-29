-- Prove2me | solution 1 for irrational_or_irrational_of_int_linear_forms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-10T23:37:27.384036+00:00
-- url     : https://prove2.me/submissions/dc28afa4-9dc2-4bc4-89ae-6fb47233c71d

import Mathlib
open Filter Topology

/-- Two-variable irrationality criterion: non-vanishing integer linear forms in `x`, `y`
tending to zero force at least one of `x`, `y` to be irrational. -/
theorem solution (x y : ℝ) (A B C : ℕ → ℤ)
    (hne : ∀ n, (A n : ℝ) * x + (B n : ℝ) * y + (C n : ℝ) ≠ 0)
    (hlim : Filter.Tendsto (fun n => (A n : ℝ) * x + (B n : ℝ) * y + (C n : ℝ))
      Filter.atTop (nhds 0)) :
    Irrational x ∨ Irrational y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hx, hy⟩ := hcon
  rw [Irrational, not_not] at hx hy
  obtain ⟨r, hr⟩ := hx
  obtain ⟨s, hs⟩ := hy
  have hdr : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hds : (0 : ℝ) < (s.den : ℝ) := by exact_mod_cast s.pos
  have hxr : x = (r.num : ℝ) / (r.den : ℝ) := by rw [← hr]; exact_mod_cast (Rat.num_div_den r).symm
  have hys : y = (s.num : ℝ) / (s.den : ℝ) := by rw [← hs]; exact_mod_cast (Rat.num_div_den s).symm
  -- every form is an integer over the fixed denominator `r.den * s.den`
  set D : ℤ := (r.den : ℤ) * (s.den : ℤ) with hD
  have hDpos : (0 : ℝ) < (D : ℝ) := by rw [hD]; push_cast; positivity
  have hform : ∀ n, (A n : ℝ) * x + (B n : ℝ) * y + (C n : ℝ)
      = ((A n * r.num * (s.den : ℤ) + B n * s.num * (r.den : ℤ) + C n * D : ℤ) : ℝ) / (D : ℝ) := by
    intro n
    rw [hxr, hys, hD]
    push_cast
    field_simp
  have hkey : ∀ n, 1 / (D : ℝ) ≤ |(A n : ℝ) * x + (B n : ℝ) * y + (C n : ℝ)| := by
    intro n
    have h0 : A n * r.num * (s.den : ℤ) + B n * s.num * (r.den : ℤ) + C n * D ≠ 0 := by
      intro h
      exact hne n (by rw [hform n, h]; simp)
    have h1 : (1 : ℝ) ≤ |((A n * r.num * (s.den : ℤ) + B n * s.num * (r.den : ℤ) + C n * D : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs h0
    rw [hform n, abs_div, abs_of_pos hDpos]
    gcongr
  have habs : Filter.Tendsto (fun n => |(A n : ℝ) * x + (B n : ℝ) * y + (C n : ℝ)|)
      Filter.atTop (nhds 0) := by simpa using hlim.abs
  obtain ⟨n, hn⟩ := (habs.eventually (gt_mem_nhds (show (0:ℝ) < 1 / (D:ℝ) by positivity))).exists
  exact absurd hn (not_lt.mpr (hkey n))
