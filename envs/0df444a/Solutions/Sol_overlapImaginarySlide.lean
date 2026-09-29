-- Prove2me | solution 1 for overlapImaginarySlide
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-26T23:30:44.523973+00:00
-- url     : https://prove2.me/submissions/728b8c6c-0f88-4ed3-87e4-9b72711c5488

import Mathlib

open Set

theorem solution (n : ℕ) :
    ∀ (z : ℂ), (n : ℝ) + 1 - 3 / 4 < z.re →
      (z.re < (n : ℝ) + 1 ∨ 0 < z.im ∨ dist z ((n + 2 : ℕ) : ℂ) < 1 / 2) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        (n : ℝ) + 1 - 3 / 4 < (⟨z.re, (1 - s) * z.im + s⟩ : ℂ).re ∧
        ((⟨z.re, (1 - s) * z.im + s⟩ : ℂ).re < (n : ℝ) + 1 ∨
          0 < (⟨z.re, (1 - s) * z.im + s⟩ : ℂ).im ∨
          dist (⟨z.re, (1 - s) * z.im + s⟩ : ℂ) ((n + 2 : ℕ) : ℂ) < 1 / 2) := by
  intro z hlo hmem s hs0 hs1
  have hre : (⟨z.re, (1 - s) * z.im + s⟩ : ℂ).re = z.re := rfl
  have him : (⟨z.re, (1 - s) * z.im + s⟩ : ℂ).im = (1 - s) * z.im + s := rfl
  refine ⟨hlo, ?_⟩
  rcases hmem with hlt | him0 | hdz
  · -- The real part is untouched and still below the bound.
    exact Or.inl (hre ▸ hlt)
  · -- `0 < z.im` and `0 ≤ s ≤ 1`: the running value `(1-s)*z.im + s` is positive,
    -- because either `s < 1`, when `z.im`'s share is positive, or `s = 1`, when the
    -- value is `1`.  So the image is in the upper cap.
    by_cases hs : 0 < (1 - s) * z.im + s
    · exact Or.inr (Or.inl hs)
    · exfalso
      have h1m : (0 : ℝ) ≤ 1 - s := by linarith
      rcases lt_or_eq_of_le h1m with hlt1 | heq1
      · have hmul : (0 : ℝ) < (1 - s) * z.im := mul_pos hlt1 him0
        nlinarith [hmul]
      · have : s = 1 := by linarith
        subst this
        have hpos : (0 : ℝ) < (1 - 1) * z.im + 1 := by norm_num
        exact absurd hpos hs
  · -- `dist z (n+2) < 1/2`: if the image is above the axis it is in the upper cap;
    -- otherwise its imaginary part is at least `z.im`'s, and because `c = n+2` lies
    -- ON the real axis the distance to `c` is monotone in `|im|` at fixed real part,
    -- so the image is still within `1/2` of `c`.
    by_cases hs : 0 < (1 - s) * z.im + s
    · exact Or.inr (Or.inl hs)
    · refine Or.inr (Or.inr ?_)
      have hrun : (1 - s) * z.im + s ≤ 0 := le_of_not_gt hs
      -- `s = 1` would make the running value `1`, contradicting `hrun`, so `s < 1`;
      -- then `1 - s > 0` and `(1-s)*z.im <= -s <= 0` force `z.im <= 0`.
      have hslt : s < 1 := by
        have hne : s ≠ 1 := by
          intro hcon
          rw [hcon] at hrun
          norm_num at hrun
        exact lt_of_le_of_ne hs1 hne
      have hzim : z.im ≤ 0 := by
        have h1m : (0 : ℝ) < 1 - s := by linarith
        have hmul : (1 - s) * z.im ≤ -s := by linarith
        nlinarith
      have hlow : z.im ≤ (1 - s) * z.im + s := by
        have hid : (1 - s) * z.im + s - z.im = s * (1 - z.im) := by ring
        have hpos : 0 ≤ s * (1 - z.im) := mul_nonneg hs0 (by linarith)
        linarith
      have hsq : ‖(⟨z.re, (1 - s) * z.im + s⟩ : ℂ) - ((n + 2 : ℕ) : ℂ)‖ ^ 2
          ≤ ‖(⟨z.re, z.im⟩ : ℂ) - ((n + 2 : ℕ) : ℂ)‖ ^ 2 := by
        -- `simp only` rather than `rw`: `rw` rewrites only the first occurrence of a
        -- pattern at each step, and the real and imaginary projections occur under
        -- anonymous constructors, so a `rw` list leaves some of them unreduced.  `simp
        -- only` applies the rules repeatedly and under constructors.
        simp only [RCLike.norm_sq_eq_def, RCLike.re_eq_complex_re, RCLike.im_eq_complex_im,
          Complex.sub_re, Complex.sub_im, Complex.natCast_re, Complex.natCast_im]
        -- Both `z.im` and the running value are non-positive with `z.im` the smaller, so
        -- negating reverses the order and squaring is monotone on `ℝ≥0`.  No `abs` lemma
        -- is needed: `mul_self_le_mul_self` applies directly to the two negatives.
        have hb0 : (0 : ℝ) ≤ -((1 - s) * z.im + s) := by linarith
        have hnb : -((1 - s) * z.im + s) ≤ -z.im := by linarith
        have h1 : ((1 - s) * z.im + s) ^ 2 ≤ z.im ^ 2 := by
          have hmul := mul_self_le_mul_self hb0 hnb
          nlinarith
        -- The real-part summands are identical on both sides, so the goal reduces to
        -- `h1`.  `nlinarith` is used rather than `linarith` because the goal's real-part
        -- summands are products of the form `A * A`, which only the square-aware
        -- preprocessing can cancel against the identical term on the other side.
        nlinarith
      have hnorm : ‖(⟨z.re, (1 - s) * z.im + s⟩ : ℂ) - ((n + 2 : ℕ) : ℂ)‖
          ≤ ‖(⟨z.re, z.im⟩ : ℂ) - ((n + 2 : ℕ) : ℂ)‖ := by
        -- `Real.sqrt_le_sqrt` turns the SQUARED bound into the same bound under `√`.
        -- Reading it back simplifies `√(‖·‖ ^ 2)` DOWN to `‖·‖`, which is the FORWARD
        -- `[simp]` rule `Real.sqrt_sq (h : 0 ≤ x) : √(x ^ 2) = x` with `x := ‖·‖`.
        -- Its side condition is `0 ≤ ‖·‖`, supplied by `norm_nonneg` (not `sq_nonneg`,
        -- which would only give `0 ≤ ‖·‖ ^ 2`).
        have hroot := Real.sqrt_le_sqrt hsq
        simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] using hroot
      have hdist : dist (⟨z.re, (1 - s) * z.im + s⟩ : ℂ) ((n + 2 : ℕ) : ℂ)
          ≤ dist (⟨z.re, z.im⟩ : ℂ) ((n + 2 : ℕ) : ℂ) := by
        rw [dist_eq_norm, dist_eq_norm]
        exact hnorm
      exact lt_of_le_of_lt hdist hdz
