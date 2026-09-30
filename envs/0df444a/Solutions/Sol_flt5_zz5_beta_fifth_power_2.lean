-- Prove2me | solution 2 for flt5_zz5_beta_fifth_power
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T07:41:41.098365+00:00
-- url     : https://prove2.me/submissions/1b243344-cd8a-4d84-9d98-b3959acf0008

import Mathlib

set_option autoImplicit false

open scoped NumberField

namespace KummerNormCounterexample

abbrev K := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ K :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField K := IsCyclotomicExtension.numberField {5} ℚ K

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

lemma norm_add_two {z : K} (hz : IsPrimitiveRoot z 5) :
    Algebra.norm ℚ (z + 2) = 11 := by
  classical
  let pb := hz.powerBasis ℚ
  have hgen : pb.gen = z := hz.powerBasis_gen ℚ
  have hdim : pb.dim = 4 := by
    rw [← pb.finrank, IsCyclotomicExtension.finrank K
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 5))]
    decide
  let M := Algebra.leftMulMatrix pb.basis z
  have hchar : M.charpoly = Polynomial.cyclotomic 5 ℚ := by
    change (Algebra.leftMulMatrix pb.basis z).charpoly = _
    rw [← hgen, charpoly_leftMulMatrix, hgen,
      hz.minpoly_eq_cyclotomic_of_irreducible
        (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 5))]
  have heval := Matrix.eval_charpoly M (-2)
  rw [hchar, Polynomial.cyclotomic_prime] at heval
  norm_num [Finset.sum_range_succ] at heval
  have hmat : Matrix.diagonal (fun _ : Fin pb.dim => (-2 : ℚ)) - M =
      -(Algebra.leftMulMatrix pb.basis (z + 2)) := by
    simp only [map_add, map_ofNat]
    change Matrix.diagonal (fun _ : Fin pb.dim => (-2 : ℚ)) - M = -(M + 2)
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, Matrix.ofNat_apply, h, sub_eq_add_neg]
  rw [hmat, Matrix.det_neg, Fintype.card_fin] at heval
  have hsign : (-1 : ℚ) ^ pb.dim = 1 := by rw [hdim]; norm_num
  rw [hsign, one_mul] at heval
  rw [Algebra.norm_eq_matrix_det pb.basis]
  exact heval.symm

lemma norm_integer_add_two {z : K} (hz : IsPrimitiveRoot z 5) :
    Algebra.norm ℤ (hz.toInteger + 2) = 11 := by
  have h := norm_add_two hz
  have heq := Algebra.coe_norm_int (hz.toInteger + 2)
  have hc : ((hz.toInteger + 2 : 𝓞 K) : K) = z + 2 := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_add, map_ofNat]
    rfl
  rw [hc, h] at heq
  exact_mod_cast heq

lemma prime_of_norm_eleven {a : 𝓞 K} (ha : Algebra.norm ℤ a = 11) : Prime a := by
  have ha0 : a ≠ 0 := by
    intro h
    simp [h, Algebra.norm_zero] at ha
  apply Ideal.prime_of_irreducible_absNorm_span ha0
  rw [Ideal.absNorm_span_singleton, ha]
  rw [Nat.irreducible_iff_prime, ← Nat.prime_iff]
  norm_num

lemma norm_six : Algebra.norm ℤ (6 : 𝓞 K) = 1296 := by
  have heq := Algebra.coe_norm_int (6 : 𝓞 K)
  have hdim : Module.finrank ℚ K = 4 := by
    rw [IsCyclotomicExtension.finrank K
      (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 5))]
    decide
  simp only [map_ofNat] at heq
  have hn := Algebra.norm_natCast ℚ (S := K) 6
  rw [hdim] at hn
  norm_num at hn
  rw [hn] at heq
  exact_mod_cast heq

lemma not_fifth {R : Type*} [CommRing R] [IsDomain R] {a b : R}
    (ha : Prime a) (hab : ¬a ∣ b) :
    ¬∃ (u : Rˣ) (d : R), a * b ^ 4 = (u : R) * d ^ 5 := by
  rintro ⟨u, d, h⟩
  have hpow : a ∣ d ^ 5 := by
    have hdiv : a ∣ (u : R) * d ^ 5 := h ▸ dvd_mul_right a (b ^ 4)
    rcases ha.dvd_or_dvd hdiv with hu | hd
    · exact False.elim (ha.not_isUnit (isUnit_of_dvd_unit hu u.isUnit))
    · exact hd
  obtain ⟨c, rfl⟩ := ha.dvd_of_dvd_pow hpow
  have heq : b ^ 4 = a * ((u : R) * a ^ 3 * c ^ 5) := by
    apply mul_left_cancel₀ ha.ne_zero
    calc
      a * b ^ 4 = (u : R) * (a * c) ^ 5 := h
      _ = a * (a * ((u : R) * a ^ 3 * c ^ 5)) := by ring
  exact hab (ha.dvd_of_dvd_pow ⟨_, heq⟩)

lemma counterexample :
    ∃ β : 𝓞 K, Algebra.norm ℤ β = (11 : ℤ) ^ 5 ∧
      ¬∃ (u : (𝓞 K)ˣ) (d : 𝓞 K), β = (u : 𝓞 K) * d ^ 5 := by
  let z := IsCyclotomicExtension.zeta 5 ℚ K
  have hz : IsPrimitiveRoot z 5 := IsCyclotomicExtension.zeta_spec 5 ℚ K
  let zi : 𝓞 K := hz.toInteger
  let a : 𝓞 K := zi + 2
  let b : 𝓞 K := zi ^ 2 + 2
  have ha : Algebra.norm ℤ a = 11 := norm_integer_add_two hz
  have hb : Algebra.norm ℤ b = 11 := by
    have hpow := norm_integer_add_two (hz.pow_of_coprime 2 (by decide))
    convert hpow using 1
    congr 1
  have hab : ¬a ∣ b := by
    intro hab
    have hid : b - (zi - 2) * a = 6 := by dsimp [a, b]; ring
    have ha6 : a ∣ (6 : 𝓞 K) := by
      rw [← hid]
      exact dvd_sub hab (dvd_mul_left a (zi - 2))
    have hdiv := map_dvd (Algebra.norm ℤ) ha6
    rw [ha, norm_six] at hdiv
    norm_num at hdiv
  refine ⟨a * b ^ 4, ?_, not_fifth (prime_of_norm_eleven ha) hab⟩
  rw [map_mul, map_pow, ha, hb]
  norm_num

end KummerNormCounterexample

theorem solution :
    ¬∀ (a b s : ℤ), Int.gcd a b = 1 →
      ∀ β : NumberField.RingOfIntegers (CyclotomicField 5 ℚ),
        Algebra.norm ℤ β = s ^ 5 →
        IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) →
        ∃ (u : (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))ˣ)
          (d : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)),
          β = (u : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) * d ^ 5 := by
  intro h
  obtain ⟨β, hnorm, hnot⟩ := KummerNormCounterexample.counterexample
  exact hnot (h 1 0 11 (by norm_num) β hnorm
    (IsCyclotomicExtension.Rat.five_pid KummerNormCounterexample.K))

#print axioms solution
