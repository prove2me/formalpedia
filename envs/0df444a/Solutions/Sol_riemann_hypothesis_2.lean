-- Prove2me | solution 2 for riemann_hypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-20T22:41:14.959983+00:00
-- url     : https://prove2.me/submissions/4820ba35-6262-4987-8812-f555f052aeca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AlpoGeChallenge_LFunction_eq_zero_re_of_isPrimitive

open Complex Real

namespace HubRHfull

/-- Left of the critical strip, the only zeros of `ζ` are the trivial ones. -/
lemma zeta_ne_zero_of_re_nonpos {s : ℂ} (hre : s.re ≤ 0)
    (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) : riemannZeta s ≠ 0 := by
  intro hz
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [riemannZeta_zero] at hz; norm_num at hz
  set u := 1 - s with hu_def
  have hure : 1 ≤ u.re := by simp [hu_def]; linarith
  have hun : ∀ n : ℕ, u ≠ -n := by
    intro n h; have := congrArg Complex.re h; simp at this; linarith [n.cast_nonneg (α := ℝ)]
  have hu1 : u ≠ 1 := by intro h; apply hs0; linear_combination -h
  have hfe := riemannZeta_one_sub hun hu1
  rw [show 1 - u = s by simp [hu_def], hz] at hfe
  have h2pi : (2 * (π : ℂ)) ≠ 0 := by
    have := Real.pi_pos; exact mul_ne_zero two_ne_zero (by exact_mod_cast this.ne')
  have hpow : (2 * (π : ℂ)) ^ (-u) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  have hgam : Complex.Gamma u ≠ 0 := Complex.Gamma_ne_zero hun
  have hcos : Complex.cos (π * u / 2) ≠ 0 := by
    rw [Ne, Complex.cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have huk : u = 2 * k + 1 := by
      have := hk; field_simp at this; linear_combination this
    have hsk : s = -2 * (k : ℂ) := by linear_combination -huk + hu_def
    have hk0 : 0 ≤ k := by
      have := congrArg Complex.re hsk; simp at this
      have : (0 : ℝ) ≤ k := by linarith
      exact_mod_cast this
    rcases (show k = 0 ∨ 1 ≤ k by omega) with rfl | hk1
    · apply hs0; simpa using hsk
    · apply htriv
      refine ⟨(k - 1).toNat, ?_⟩
      rw [hsk]
      have : ((k - 1).toNat : ℤ) = k - 1 := Int.toNat_of_nonneg (by omega)
      have hc : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
        rw [show (((k - 1).toNat : ℕ) : ℂ) = (((k - 1).toNat : ℤ) : ℂ) from rfl, this]; push_cast; ring
      rw [hc]; ring
  have hzu : riemannZeta u = 0 := by
    rcases mul_eq_zero.mp hfe.symm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · exact absurd h hpow
        · exact absurd h hgam
      · exact absurd h hcos
    · exact h
  exact riemannZeta_ne_zero_of_one_le_re hure hzu

end HubRHfull

theorem solution :
    ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2 := by
  intro s hz htriv hs1
  rcases le_or_gt s.re 0 with h0 | h0
  · exact absurd hz (HubRHfull.zeta_ne_zero_of_re_nonpos h0 htriv)
  rcases lt_or_ge s.re 1 with h1 | h1
  · exact AlpoGeChallenge.LFunction_eq_zero_re_of_isPrimitive 1 1
      DirichletCharacter.isPrimitive_one_level_one s h0 h1
      (by rw [DirichletCharacter.LFunction_modOne_eq]; exact hz)
  · exact absurd hz (riemannZeta_ne_zero_of_one_le_re h1)
