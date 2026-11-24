-- Prove2me | solution 1 for gw_constant
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:50:28.303426+00:00
-- url     : https://prove2.me/submissions/3647612e-0ce4-4728-a17e-d79ace1a49a4

import Mathlib
set_option autoImplicit false
open Real

private lemma gw_cmp {f g f' g' : ℝ → ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hg : ∀ t, HasDerivAt g (g' t) t) (h0 : f 0 ≤ g 0)
    (hd : ∀ t, 0 ≤ t → f' t ≤ g' t) {x : ℝ} (hx : 0 ≤ x) : f x ≤ g x := by
  have hmono : MonotoneOn (fun t => g t - f t) (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => g' t - f' t)
    · exact fun t _ => ((hg t).sub (hf t)).continuousAt.continuousWithinAt
    · exact fun t _ => ((hg t).sub (hf t)).hasDerivWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have := hd t (le_of_lt ht)
      linarith
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
  simp only at this; linarith

private lemma dpoly (t : ℝ) (n : ℕ) (k : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ (n + 1) / k) ((n + 1) * t ^ n / k) t := by
  have := (hasDerivAt_pow (n + 1) t).div_const k
  simpa using this

private lemma s1 {x : ℝ} (hx : 0 ≤ x) : sin x ≤ x :=
  gw_cmp (f' := cos) (g' := fun _ => 1) (hasDerivAt_sin) (fun t => hasDerivAt_id t)
    (by simp) (fun t _ => cos_le_one t) hx

private lemma c2 {x : ℝ} (hx : 0 ≤ x) : 1 - x ^ 2 / 2 ≤ cos x := by
  have := gw_cmp (f := fun x => 1 - x ^ 2 / 2) (g := cos) (f' := fun t => -t) (g' := fun t => -sin t)
    (fun t => by
      have := (dpoly t 1 2).const_sub 1
      exact this.congr_deriv (by push_cast; ring))
    hasDerivAt_cos (by simp) (fun t ht => by have := s1 ht; linarith) hx
  simpa using this

private lemma s3 {x : ℝ} (hx : 0 ≤ x) : x - x ^ 3 / 6 ≤ sin x := by
  have := gw_cmp (f := fun x => x - x ^ 3 / 6) (g := sin) (f' := fun t => 1 - t ^ 2 / 2) (g' := cos)
    (fun t => by
      have := (hasDerivAt_id t).sub (dpoly t 2 6)
      exact this.congr_deriv (by push_cast; ring))
    hasDerivAt_sin (by simp) (fun t ht => c2 ht) hx
  simpa using this

private lemma c4 {x : ℝ} (hx : 0 ≤ x) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have := gw_cmp (g := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24) (f := cos)
    (g' := fun t => -t + t ^ 3 / 6) (f' := fun t => -sin t)
    hasDerivAt_cos
    (fun t => by
      have := ((dpoly t 1 2).const_sub 1).add (dpoly t 3 24)
      exact this.congr_deriv (by push_cast; ring))
    (by simp) (fun t ht => by have := s3 ht; linarith) hx
  simpa using this

private lemma s5 {x : ℝ} (hx : 0 ≤ x) : sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have := gw_cmp (g := fun x => x - x ^ 3 / 6 + x ^ 5 / 120) (f := sin)
    (g' := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24) (f' := cos)
    hasDerivAt_sin
    (fun t => by
      have := ((hasDerivAt_id t).sub (dpoly t 2 6)).add (dpoly t 4 120)
      exact this.congr_deriv (by push_cast; ring))
    (by simp) (fun t ht => c4 ht) hx
  simpa using this

private lemma c6 {x : ℝ} (hx : 0 ≤ x) :
    1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 ≤ cos x := by
  have := gw_cmp (f := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720) (g := cos)
    (f' := fun t => -t + t ^ 3 / 6 - t ^ 5 / 120) (g' := fun t => -sin t)
    (fun t => by
      have := (((dpoly t 1 2).const_sub 1).add (dpoly t 3 24)).sub (dpoly t 5 720)
      exact this.congr_deriv (by push_cast; ring))
    hasDerivAt_cos (by simp) (fun t ht => by have := s5 ht; linarith) hx
  simpa using this

private lemma s7 {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ sin x := by
  have := gw_cmp (f := fun x => x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040) (g := sin)
    (f' := fun t => 1 - t ^ 2 / 2 + t ^ 4 / 24 - t ^ 6 / 720) (g' := cos)
    (fun t => by
      have := (((hasDerivAt_id t).sub (dpoly t 2 6)).add (dpoly t 4 120)).sub (dpoly t 6 5040)
      exact this.congr_deriv (by push_cast; ring))
    hasDerivAt_sin (by simp) (fun t ht => c6 ht) hx
  simpa using this

private lemma c8 {x : ℝ} (hx : 0 ≤ x) :
    cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 := by
  have := gw_cmp (g := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320) (f := cos)
    (g' := fun t => -t + t ^ 3 / 6 - t ^ 5 / 120 + t ^ 7 / 5040) (f' := fun t => -sin t)
    hasDerivAt_cos
    (fun t => by
      have := ((((dpoly t 1 2).const_sub 1).add (dpoly t 3 24)).sub (dpoly t 5 720)).add
        (dpoly t 7 40320)
      exact this.congr_deriv (by push_cast; ring))
    (by simp) (fun t ht => by have := s7 ht; linarith) hx
  simpa using this

/-- tangent bound for cos on [a, π/2] -/
private lemma tangent {a x : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hx : x ≤ π / 2) :
    cos x ≤ cos a - sin a * (x - a) := by
  rcases eq_or_lt_of_le hax with h | h
  · subst h; simp
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope cos (fun t => -sin t) h
    continuous_cos.continuousOn (fun t _ => hasDerivAt_cos t)
  have hs : sin a ≤ sin ξ :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) (by linarith [hξ.2]) hξ.1.le
  have hpos : 0 < x - a := by linarith
  rw [eq_div_iff hpos.ne'] at hξeq
  nlinarith [mul_le_mul_of_nonneg_right hs hpos.le]

/-- On `[a, b] ⊆ [0, π/2]`, the tangent bound plus Taylor values at `a` give the claim,
provided three rational inequalities hold. -/
private lemma piece (a b x : ℝ) (ha : 0 ≤ a) (hax : a ≤ x) (hxb : x ≤ b) (hx : x ≤ π / 2)
    (h0 : 0 ≤ 2 - 8785 / 10000 * (1 + (1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320)))
    (hl : 0 ≤ a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040)
    (h1 : 2 * a ≤ 3.141592 *
      (2 - 8785 / 10000 * (1 + (1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320))))
    (h2 : 2 * b ≤ 3.141592 *
      (2 - 8785 / 10000 * (1 + (1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320)
        - (a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040) * (b - a)))) :
    8785 / 10000 * π * (1 + cos x) ≤ 2 * π - 2 * x := by
  have hc := tangent ha hax hx
  have hu := c8 ha
  have hs := s7 ha
  generalize 1 - a ^ 2 / 2 + a ^ 4 / 24 - a ^ 6 / 720 + a ^ 8 / 40320 = u at *
  generalize a - a ^ 3 / 6 + a ^ 5 / 120 - a ^ 7 / 5040 = l at *
  have hxa : 0 ≤ x - a := by linarith
  have hR : cos x ≤ u - l * (x - a) := by nlinarith [mul_le_mul_of_nonneg_right hs hxa]
  have hE : 2 * x ≤ 3.141592 * (2 - 8785 / 10000 * (1 + u - l * (x - a))) := by
    rcases le_total 0 (3.141592 * (8785 / 10000) * l - 2) with hsl | hsl
    · nlinarith [mul_nonneg hsl hxa]
    · nlinarith [mul_nonneg (neg_nonneg.2 hsl) (sub_nonneg.2 hxb)]
  have hq : 0 ≤ 2 - 8785 / 10000 * (1 + u - l * (x - a)) := by nlinarith [mul_nonneg hl hxa]
  nlinarith [mul_le_mul_of_nonneg_right pi_gt_d6.le hq, mul_le_mul_of_nonneg_left hR pi_pos.le]

private lemma main_x (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ π / 2) :
    8785 / 10000 * π * (1 + cos x) ≤ 2 * π - 2 * x := by
  rcases le_total x (3817 / 10000 : ℝ) with u0 | l1
  · exact piece (0 : ℝ) (3817 / 10000 : ℝ) x (by norm_num) hx0 u0 hx
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_total x (293 / 500 : ℝ) with u1 | l2
  · exact piece (3817 / 10000 : ℝ) (293 / 500 : ℝ) x (by norm_num) l1 u1 hx
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_total x (3477 / 5000 : ℝ) with u2 | l3
  · exact piece (293 / 500 : ℝ) (3477 / 5000 : ℝ) x (by norm_num) l2 u2 hx
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_total x (3767 / 5000 : ℝ) with u3 | l4
  · exact piece (3477 / 5000 : ℝ) (3767 / 5000 : ℝ) x (by norm_num) l3 u3 hx
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_total x (981 / 1250 : ℝ) with u4 | l5
  · exact piece (3767 / 5000 : ℝ) (981 / 1250 : ℝ) x (by norm_num) l4 u4 hx
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_total x (8047 / 10000 : ℝ) with u5 | l6
  · exact piece (981 / 1250 : ℝ) (8047 / 10000 : ℝ) x (by norm_num) l5 u5 hx
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rcases le_total x (1679 / 2000 : ℝ) with u6 | l7
  · exact piece (8047 / 10000 : ℝ) (1679 / 2000 : ℝ) x (by norm_num) l6 u6 hx
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact piece (1679 / 2000 : ℝ) (3927 / 2500 : ℝ) x (by norm_num) l7 (by linarith [pi_lt_d6]) hx
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

theorem solution (t : ℝ) (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    (8785 / 10000 : ℝ) * Real.pi * (1 - t) ≤ 2 * Real.arccos t := by
  have hcos : cos (arccos t) = t := cos_arccos h1 h2
  have h0 : 0 ≤ arccos t := arccos_nonneg t
  have hle : arccos t ≤ π := arccos_le_pi t
  generalize arccos t = θ at *
  subst hcos
  have hpu := pi_lt_d6
  rcases le_or_gt θ (144 / 100) with hA | hA
  · have hq := one_sub_sq_div_two_le_cos (x := θ)
    nlinarith [mul_le_mul_of_nonneg_left (show 1 - cos θ ≤ θ ^ 2 / 2 by linarith) pi_pos.le,
      mul_le_mul_of_nonneg_right hpu.le (sq_nonneg θ), mul_le_mul_of_nonneg_left hA h0,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA h0) pi_pos.le]
  rcases le_or_gt θ (π / 2) with hB | hB
  · have hc0 : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hB⟩
    nlinarith [mul_nonneg pi_pos.le hc0]
  have key := main_x (π - θ) (by linarith) (by linarith)
  rw [cos_pi_sub] at key
  linarith
