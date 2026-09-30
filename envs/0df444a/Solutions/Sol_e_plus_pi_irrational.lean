-- Prove2me | solution 1 for e_plus_pi_irrational
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:02:54.062291+00:00
-- url     : https://prove2.me/submissions/a467a5f0-71eb-4cf5-9298-d86f30654009

import Mathlib

set_option autoImplicit false

/- Adapted from ryanshin, Prove2me accepted submission
   f18f80bf-4cbc-4f4b-8a8d-02bf01ee969e (legacy counterpart 223a668d). -/

open Filter Polynomial
open scoped Topology

namespace ExpQuadratic

theorem approximation_tendsto (C : ℝ) :
    Tendsto (fun n : ℕ => C ^ n / ((n - 1).factorial : ℝ)) atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa [pow_succ, mul_div_assoc, mul_comm] using
    (FloorSemiring.tendsto_pow_div_factorial_atTop C).const_mul C

theorem real_approximation (g : ℤ[X]) (n : ℤ) (p : ℕ) (k : ℤ) (B : ℝ)
    (h : ‖n • Complex.exp (k : ℂ) - p • aeval (k : ℂ) g‖ ≤ B) :
    |(n : ℝ) * Real.exp k - (p : ℝ) * (↑(g.eval k) : ℝ)| ≤ B := by
  have heval : aeval (k : ℂ) g = (↑(g.eval k) : ℂ) :=
    aeval_algebraMap_apply_eq_algebraMap_eval k g
  rw [zsmul_eq_mul, nsmul_eq_mul, heval] at h
  simpa only [← Complex.ofReal_intCast,
    ← Complex.ofReal_natCast, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h

theorem quadratic_approximations :
    ∃ C : ℝ, ∀ p : ℕ, 2 < p → p.Prime →
      ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ ∃ u v : ℤ,
        |(n : ℝ) * Real.exp 1 - (p : ℝ) * u| ≤ C ^ p / ((p - 1).factorial : ℝ) ∧
        |(n : ℝ) * Real.exp 2 - (p : ℝ) * v| ≤ C ^ p / ((p - 1).factorial : ℝ) := by
  let f : ℤ[X] := (X - 1) * (X - 2)
  have hf : f.eval 0 ≠ 0 := by norm_num [f]
  obtain ⟨C, hC⟩ := LindemannWeierstrass.exp_polynomial_approx f hf
  refine ⟨C, fun p hp hprime => ?_⟩
  obtain ⟨n, hn, g, _, hg⟩ := hC p (by simpa [f] using hp) hprime
  have hf0 : f ≠ 0 := by
    intro h
    apply hf
    simp [h]
  have hroot1 : (1 : ℂ) ∈ f.aroots ℂ := by
    apply mem_aroots.mpr
    refine ⟨hf0, ?_⟩
    simp only [f, map_mul, map_sub, map_one, map_ofNat, aeval_X]
    norm_num
  have hroot2 : (2 : ℂ) ∈ f.aroots ℂ := by
    apply mem_aroots.mpr
    refine ⟨hf0, ?_⟩
    simp only [f, map_mul, map_sub, map_one, map_ofNat, aeval_X]
    norm_num
  refine ⟨n, hn, g.eval 1, g.eval 2, ?_, ?_⟩
  · simpa using real_approximation g n p 1 _ (by simpa using hg hroot1)
  · simpa using real_approximation g n p 2 _ (by simpa using hg hroot2)

theorem no_integer_quadratic (a b c : ℤ) (hc : c ≠ 0) :
    (a : ℝ) * Real.exp 2 + (b : ℝ) * Real.exp 1 + c ≠ 0 := by
  intro hrel
  obtain ⟨C, hC⟩ := quadratic_approximations
  have hlim : Tendsto
      (fun p : ℕ => (|(b : ℝ)| + |(a : ℝ)|) *
        (C ^ p / ((p - 1).factorial : ℝ))) atTop (𝓝 0) := by
    simpa using (approximation_tendsto C).const_mul (|(b : ℝ)| + |(a : ℝ)|)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max N (max (c.natAbs + 1) 3))
  have hpN : N ≤ p := (le_max_left _ _).trans hp
  have hpc : c.natAbs < p := by omega
  have hp2 : 2 < p := by omega
  obtain ⟨n, hn, u, v, h1, h2⟩ := hC p hp2 hprime
  let k : ℤ := n * c + p * (b * u + a * v)
  have hk : k ≠ 0 := by
    intro hk
    have hd : (p : ℤ) ∣ n * c := by
      refine ⟨-(b * u + a * v), ?_⟩
      dsimp [k] at hk
      linarith
    rcases Int.Prime.dvd_mul hprime hd with hd | hd
    · exact hn (Int.natCast_dvd.mpr hd)
    · exact (Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr hc) hpc) hd
  have hkreal : (k : ℝ) =
      -((b : ℝ) * ((n : ℝ) * Real.exp 1 - (p : ℝ) * u) +
        (a : ℝ) * ((n : ℝ) * Real.exp 2 - (p : ℝ) * v)) := by
    dsimp [k]
    push_cast
    linear_combination (n : ℝ) * hrel
  have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
  have hbound : |(k : ℝ)| ≤ (|(b : ℝ)| + |(a : ℝ)|) *
      (C ^ p / ((p - 1).factorial : ℝ)) := by
    rw [hkreal, abs_neg]
    calc
      _ ≤ |(b : ℝ) * ((n : ℝ) * Real.exp 1 - (p : ℝ) * u)| +
          |(a : ℝ) * ((n : ℝ) * Real.exp 2 - (p : ℝ) * v)| := abs_add_le _ _
      _ = |(b : ℝ)| * |(n : ℝ) * Real.exp 1 - (p : ℝ) * u| +
          |(a : ℝ)| * |(n : ℝ) * Real.exp 2 - (p : ℝ) * v| := by rw [abs_mul, abs_mul]
      _ ≤ |(b : ℝ)| * (C ^ p / ((p - 1).factorial : ℝ)) +
          |(a : ℝ)| * (C ^ p / ((p - 1).factorial : ℝ)) := by gcongr
      _ = _ := by ring
  exact (not_lt_of_ge (hk1.trans hbound)) (hN p hpN)

theorem no_rational_quadratic (s t : ℚ) (ht : t ≠ 0) :
    Real.exp 1 ^ 2 - (s : ℝ) * Real.exp 1 + t ≠ 0 := by
  intro hrel
  have hsden : (s.den : ℝ) ≠ 0 := by exact_mod_cast s.den_ne_zero
  have htden : (t.den : ℝ) ≠ 0 := by exact_mod_cast t.den_ne_zero
  apply no_integer_quadratic ((s.den : ℤ) * t.den) (-s.num * t.den)
    (t.num * s.den) (mul_ne_zero (Rat.num_ne_zero.mpr ht) (by exact_mod_cast s.den_ne_zero))
  have hexp : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    norm_num
  rw [hexp]
  push_cast
  rw [Rat.cast_def, Rat.cast_def] at hrel
  field_simp at hrel
  nlinarith only [hrel]

end ExpQuadratic

theorem solution :
    Irrational (Real.exp 1 + Real.pi) ∨ Irrational (Real.exp 1 * Real.pi) := by
  by_contra h
  push_neg at h
  obtain ⟨s, hs⟩ := exists_rat_of_not_irrational h.1
  obtain ⟨t, ht⟩ := exists_rat_of_not_irrational h.2
  have ht0 : t ≠ 0 := by
    intro hzero
    have hpos := mul_pos (Real.exp_pos 1) Real.pi_pos
    rw [ht, hzero, Rat.cast_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  apply ExpQuadratic.no_rational_quadratic s t ht0
  rw [← hs, ← ht]
  ring

#print axioms ExpQuadratic.approximation_tendsto
#print axioms ExpQuadratic.quadratic_approximations
#print axioms ExpQuadratic.no_integer_quadratic
#print axioms ExpQuadratic.no_rational_quadratic
#print axioms solution
