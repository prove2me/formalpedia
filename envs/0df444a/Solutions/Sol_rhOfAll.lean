-- Prove2me | solution 1 for rhOfAll
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @GeorgeCoote
-- created : 2026-11-21T18:50:19.844826+00:00
-- url     : https://prove2.me/submissions/2cff919a-4e75-46d3-b22f-aac238818b32
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_rh_zeta_zero_free_right_half
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution :
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
      s ≠ 1 → s.re = 1 / 2 := by
  intro s hz htrivial hpole
  have hRight (w : ℂ) (hw : 1 / 2 < w.re) : riemannZeta w ≠ 0 := by
    rcases lt_or_ge w.re 1 with hstrip | houtside
    · exact rh_zeta_zero_free_right_half w hw hstrip
    · exact riemannZeta_ne_zero_of_one_le_re houtside
  rcases lt_trichotomy s.re (1 / 2) with hleft | hcritical | hright
  · exfalso
    -- The Gamma factor is nonzero after excluding zero and the trivial zeros.
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [riemannZeta_zero] at hz
      norm_num at hz
    have hgamma : Complex.Gammaℝ s ≠ 0 := by
      intro h
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h
      cases n with
      | zero => exact hs0 (by simpa using hn)
      | succ n => exact htrivial ⟨n, by simpa only [Nat.cast_succ, neg_mul] using hn⟩
    have hcompleted : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0] at hz
      exact (div_eq_zero_iff.mp hz).resolve_right hgamma
    have hreflect : 1 / 2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    apply hRight (1 - s) hreflect
    rw [riemannZeta_def_of_ne_zero (sub_ne_zero.mpr hpole.symm),
      completedRiemannZeta_one_sub, hcompleted, zero_div]
  · exact hcritical
  · exact (hRight s hright hz).elim
