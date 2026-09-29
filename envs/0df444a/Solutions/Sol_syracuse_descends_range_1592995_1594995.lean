-- Prove2me | solution 1 for syracuse_descends_range_1592995_1594995
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:09:04.956527+00:00
-- url     : https://prove2.me/submissions/0e74c9b8-3c57-425f-b578-992c8cfe612b

import Mathlib
import Definitions.Def_syracuseStep

set_option maxHeartbeats 1000000

open Nat

/-- Half of all odd numbers descend in a single Syracuse step, uniformly. -/
theorem step_lt_of_one_mod_four (m : ℕ) (h1 : 1 < m) (h4 : m % 4 = 1) : syracuseStep m < m := by
  have hne : 3 * m + 1 ≠ 0 := by omega
  have hdvd : (2:ℕ) ^ 2 ∣ 3 * m + 1 := by
    have : (4:ℕ) ∣ 3 * m + 1 := by omega
    simpa using this
  have hle : 2 ≤ (3 * m + 1).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).mp hdvd
  have hpow : (2:ℕ) ^ 2 ≤ 2 ^ ((3 * m + 1).factorization 2) :=
    Nat.pow_le_pow_right (by norm_num) hle
  have h1' : syracuseStep m ≤ (3 * m + 1) / 2 ^ 2 := by
    show ordCompl[2] (3 * m + 1) ≤ _
    exact Nat.div_le_div_left hpow (by positivity)
  have h2' : (3 * m + 1) / 2 ^ 2 < m := by
    apply Nat.div_lt_of_lt_mul
    omega
  omega

/-- `Blo L x` : some Syracuse iterate of `x` drops below `L`. -/
abbrev Blo (L x : ℕ) : Prop := ∃ t : ℕ, syracuseStep^[t] x < L

theorem bbase {L x y : ℕ} (h : syracuseStep x = y) (hy : y < L) : Blo L x :=
  ⟨1, by rw [Function.iterate_one, h]; exact hy⟩

theorem bstep {L x y : ℕ} (h : syracuseStep x = y) (hy : Blo L y) : Blo L x := by
  obtain ⟨t, ht⟩ := hy
  exact ⟨t + 1, by rw [Function.iterate_add_apply, Function.iterate_one, h]; exact ht⟩

theorem se (a : ℕ) {y z : ℕ} (h : 3 * y + 1 = 2 ^ a * z) (hz : Odd z) :
    syracuseStep y = z := by
  have hz0 : z ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hz
  have hfac : (3 * y + 1).factorization 2 = a := by
    rw [h, Nat.factorization_mul (by positivity) hz0]
    simp [Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by rwa [Nat.two_dvd_ne_zero, ← Nat.odd_iff])]
  show ordCompl[2] (3 * y + 1) = z
  rw [hfac, h, Nat.mul_div_cancel_left _ (by positivity)]


theorem B3588101 : Blo 1592995 3588101 := bbase (se 4 (by rfl) ⟨336384, by rfl⟩ : syracuseStep 3588101 = 672769) (by norm_num)
theorem B2392085 : Blo 1592995 2392085 := bbase (se 6 (by rfl) ⟨56064, by rfl⟩ : syracuseStep 2392085 = 112129) (by norm_num)
theorem B1794073 : Blo 1592995 1794073 := bbase (se 2 (by rfl) ⟨672777, by rfl⟩ : syracuseStep 1794073 = 1345555) (by norm_num)
theorem B2392109 : Blo 1592995 2392109 := bbase (se 3 (by rfl) ⟨448520, by rfl⟩ : syracuseStep 2392109 = 897041) (by norm_num)
theorem B1794109 : Blo 1592995 1794109 := bbase (se 3 (by rfl) ⟨336395, by rfl⟩ : syracuseStep 1794109 = 672791) (by norm_num)
theorem B2392133 : Blo 1592995 2392133 := bbase (se 4 (by rfl) ⟨224262, by rfl⟩ : syracuseStep 2392133 = 448525) (by norm_num)
theorem B3588173 : Blo 1592995 3588173 := bbase (se 3 (by rfl) ⟨672782, by rfl⟩ : syracuseStep 3588173 = 1345565) (by norm_num)
theorem B18153557 : Blo 1592995 18153557 := bbase (se 8 (by rfl) ⟨106368, by rfl⟩ : syracuseStep 18153557 = 212737) (by norm_num)
theorem B4145245 : Blo 1592995 4145245 := bbase (se 3 (by rfl) ⟨777233, by rfl⟩ : syracuseStep 4145245 = 1554467) (by norm_num)
theorem B2392157 : Blo 1592995 2392157 := bbase (se 3 (by rfl) ⟨448529, by rfl⟩ : syracuseStep 2392157 = 897059) (by norm_num)
theorem B1794145 : Blo 1592995 1794145 := bbase (se 2 (by rfl) ⟨672804, by rfl⟩ : syracuseStep 1794145 = 1345609) (by norm_num)
theorem B2392181 : Blo 1592995 2392181 := bbase (se 5 (by rfl) ⟨112133, by rfl⟩ : syracuseStep 2392181 = 224267) (by norm_num)
theorem B2269309 : Blo 1592995 2269309 := bbase (se 3 (by rfl) ⟨425495, by rfl⟩ : syracuseStep 2269309 = 850991) (by norm_num)
theorem B1794181 : Blo 1592995 1794181 := bbase (se 4 (by rfl) ⟨168204, by rfl⟩ : syracuseStep 1794181 = 336409) (by norm_num)
theorem B2392205 : Blo 1592995 2392205 := bbase (se 3 (by rfl) ⟨448538, by rfl⟩ : syracuseStep 2392205 = 897077) (by norm_num)
theorem B3588245 : Blo 1592995 3588245 := bbase (se 6 (by rfl) ⟨84099, by rfl⟩ : syracuseStep 3588245 = 168199) (by norm_num)
theorem B2392229 : Blo 1592995 2392229 := bbase (se 4 (by rfl) ⟨224271, by rfl⟩ : syracuseStep 2392229 = 448543) (by norm_num)
theorem B1794217 : Blo 1592995 1794217 := bbase (se 2 (by rfl) ⟨672831, by rfl⟩ : syracuseStep 1794217 = 1345663) (by norm_num)
theorem B2392253 : Blo 1592995 2392253 := bbase (se 3 (by rfl) ⟨448547, by rfl⟩ : syracuseStep 2392253 = 897095) (by norm_num)
theorem B5382341 : Blo 1592995 5382341 := bbase (se 4 (by rfl) ⟨504594, by rfl⟩ : syracuseStep 5382341 = 1009189) (by norm_num)
theorem B1794253 : Blo 1592995 1794253 := bbase (se 3 (by rfl) ⟨336422, by rfl⟩ : syracuseStep 1794253 = 672845) (by norm_num)
theorem B2392277 : Blo 1592995 2392277 := bbase (se 7 (by rfl) ⟨28034, by rfl⟩ : syracuseStep 2392277 = 56069) (by norm_num)
theorem B3588317 : Blo 1592995 3588317 := bbase (se 3 (by rfl) ⟨672809, by rfl⟩ : syracuseStep 3588317 = 1345619) (by norm_num)
theorem B2392301 : Blo 1592995 2392301 := bbase (se 3 (by rfl) ⟨448556, by rfl⟩ : syracuseStep 2392301 = 897113) (by norm_num)
theorem B1794289 : Blo 1592995 1794289 := bbase (se 2 (by rfl) ⟨672858, by rfl⟩ : syracuseStep 1794289 = 1345717) (by norm_num)
theorem B8069381 : Blo 1592995 8069381 := bbase (se 4 (by rfl) ⟨756504, by rfl⟩ : syracuseStep 8069381 = 1513009) (by norm_num)
theorem B2392325 : Blo 1592995 2392325 := bbase (se 4 (by rfl) ⟨224280, by rfl⟩ : syracuseStep 2392325 = 448561) (by norm_num)
theorem B1794325 : Blo 1592995 1794325 := bbase (se 6 (by rfl) ⟨42054, by rfl⟩ : syracuseStep 1794325 = 84109) (by norm_num)
theorem B2392349 : Blo 1592995 2392349 := bbase (se 3 (by rfl) ⟨448565, by rfl⟩ : syracuseStep 2392349 = 897131) (by norm_num)
theorem B3588389 : Blo 1592995 3588389 := bbase (se 4 (by rfl) ⟨336411, by rfl⟩ : syracuseStep 3588389 = 672823) (by norm_num)
theorem B2392373 : Blo 1592995 2392373 := bbase (se 5 (by rfl) ⟨112142, by rfl⟩ : syracuseStep 2392373 = 224285) (by norm_num)
theorem B1794361 : Blo 1592995 1794361 := bbase (se 2 (by rfl) ⟨672885, by rfl⟩ : syracuseStep 1794361 = 1345771) (by norm_num)
theorem B2392397 : Blo 1592995 2392397 := bbase (se 3 (by rfl) ⟨448574, by rfl⟩ : syracuseStep 2392397 = 897149) (by norm_num)
theorem B2392421 : Blo 1592995 2392421 := bbase (se 4 (by rfl) ⟨224289, by rfl⟩ : syracuseStep 2392421 = 448579) (by norm_num)
theorem B3588461 : Blo 1592995 3588461 := bbase (se 3 (by rfl) ⟨672836, by rfl⟩ : syracuseStep 3588461 = 1345673) (by norm_num)
theorem B2392445 : Blo 1592995 2392445 := bbase (se 3 (by rfl) ⟨448583, by rfl⟩ : syracuseStep 2392445 = 897167) (by norm_num)
theorem B2392469 : Blo 1592995 2392469 := bbase (se 6 (by rfl) ⟨56073, by rfl⟩ : syracuseStep 2392469 = 112147) (by norm_num)
theorem B2392493 : Blo 1592995 2392493 := bbase (se 3 (by rfl) ⟨448592, by rfl⟩ : syracuseStep 2392493 = 897185) (by norm_num)
theorem B3588533 : Blo 1592995 3588533 := bbase (se 5 (by rfl) ⟨168212, by rfl⟩ : syracuseStep 3588533 = 336425) (by norm_num)
theorem B3588605 : Blo 1592995 3588605 := bbase (se 3 (by rfl) ⟨672863, by rfl⟩ : syracuseStep 3588605 = 1345727) (by norm_num)
theorem B3588677 : Blo 1592995 3588677 := bbase (se 4 (by rfl) ⟨336438, by rfl⟩ : syracuseStep 3588677 = 672877) (by norm_num)
theorem B5382773 : Blo 1592995 5382773 := bbase (se 5 (by rfl) ⟨252317, by rfl⟩ : syracuseStep 5382773 = 504635) (by norm_num)
theorem B4203197 : Blo 1592995 4203197 := bbase (se 3 (by rfl) ⟨788099, by rfl⟩ : syracuseStep 4203197 = 1576199) (by norm_num)
theorem B2269901 : Blo 1592995 2269901 := bbase (se 3 (by rfl) ⟨425606, by rfl⟩ : syracuseStep 2269901 = 851213) (by norm_num)
theorem B2589389 : Blo 1592995 2589389 := bbase (se 3 (by rfl) ⟨485510, by rfl⟩ : syracuseStep 2589389 = 971021) (by norm_num)
theorem B5743381 : Blo 1592995 5743381 := bbase (se 6 (by rfl) ⟨134610, by rfl⟩ : syracuseStep 5743381 = 269221) (by norm_num)
theorem B3498773 : Blo 1592995 3498773 := bbase (se 6 (by rfl) ⟨82002, by rfl⟩ : syracuseStep 3498773 = 164005) (by norm_num)
theorem B2269981 : Blo 1592995 2269981 := bbase (se 3 (by rfl) ⟨425621, by rfl⟩ : syracuseStep 2269981 = 851243) (by norm_num)
theorem B2073373 : Blo 1592995 2073373 := bbase (se 3 (by rfl) ⟨388757, by rfl⟩ : syracuseStep 2073373 = 777515) (by norm_num)
theorem B6054709 : Blo 1592995 6054709 := bbase (se 5 (by rfl) ⟨283814, by rfl⟩ : syracuseStep 6054709 = 567629) (by norm_num)
theorem B2491229 : Blo 1592995 2491229 := bbase (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) (by norm_num)
theorem B20423573 : Blo 1592995 20423573 := bbase (se 6 (by rfl) ⟨478677, by rfl⟩ : syracuseStep 20423573 = 957355) (by norm_num)
theorem B2270101 : Blo 1592995 2270101 := bbase (se 6 (by rfl) ⟨53205, by rfl⟩ : syracuseStep 2270101 = 106411) (by norm_num)
theorem B5104549 : Blo 1592995 5104549 := bbase (se 4 (by rfl) ⟨478551, by rfl⟩ : syracuseStep 5104549 = 957103) (by norm_num)
theorem B2016181 : Blo 1592995 2016181 := bbase (se 5 (by rfl) ⟨94508, by rfl⟩ : syracuseStep 2016181 = 189017) (by norm_num)
theorem B5743541 : Blo 1592995 5743541 := bbase (se 5 (by rfl) ⟨269228, by rfl⟩ : syracuseStep 5743541 = 538457) (by norm_num)
theorem B2155477 : Blo 1592995 2155477 := bbase (se 7 (by rfl) ⟨25259, by rfl⟩ : syracuseStep 2155477 = 50519) (by norm_num)
theorem B5104613 : Blo 1592995 5104613 := bbase (se 4 (by rfl) ⟨478557, by rfl⟩ : syracuseStep 5104613 = 957115) (by norm_num)
theorem B2270197 : Blo 1592995 2270197 := bbase (se 5 (by rfl) ⟨106415, by rfl⟩ : syracuseStep 2270197 = 212831) (by norm_num)
theorem B2950141 : Blo 1592995 2950141 := bbase (se 3 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 2950141 = 1106303) (by norm_num)
theorem B2016353 : Blo 1592995 2016353 := bbase (se 2 (by rfl) ⟨756132, by rfl⟩ : syracuseStep 2016353 = 1512265) (by norm_num)
theorem B6055013 : Blo 1592995 6055013 := bbase (se 4 (by rfl) ⟨567657, by rfl⟩ : syracuseStep 6055013 = 1135315) (by norm_num)
theorem B2016409 : Blo 1592995 2016409 := bbase (se 2 (by rfl) ⟨756153, by rfl⟩ : syracuseStep 2016409 = 1512307) (by norm_num)
theorem B3933365 : Blo 1592995 3933365 := bbase (se 5 (by rfl) ⟨184376, by rfl⟩ : syracuseStep 3933365 = 368753) (by norm_num)
theorem B2688221 : Blo 1592995 2688221 := bbase (se 3 (by rfl) ⟨504041, by rfl⟩ : syracuseStep 2688221 = 1008083) (by norm_num)
theorem B2016505 : Blo 1592995 2016505 := bbase (se 2 (by rfl) ⟨756189, by rfl⟩ : syracuseStep 2016505 = 1512379) (by norm_num)
theorem B8733973 : Blo 1592995 8733973 := bbase (se 6 (by rfl) ⟨204702, by rfl⟩ : syracuseStep 8733973 = 409405) (by norm_num)
theorem B1615177 : Blo 1592995 1615177 := bbase (se 2 (by rfl) ⟨605691, by rfl⟩ : syracuseStep 1615177 = 1211383) (by norm_num)
theorem B9078101 : Blo 1592995 9078101 := bbase (se 12 (by rfl) ⟨3324, by rfl⟩ : syracuseStep 9078101 = 6649) (by norm_num)
theorem B2688349 : Blo 1592995 2688349 := bbase (se 3 (by rfl) ⟨504065, by rfl⟩ : syracuseStep 2688349 = 1008131) (by norm_num)
theorem B2016677 : Blo 1592995 2016677 := bbase (se 4 (by rfl) ⟨189063, by rfl⟩ : syracuseStep 2016677 = 378127) (by norm_num)
theorem B2688437 : Blo 1592995 2688437 := bbase (se 5 (by rfl) ⟨126020, by rfl⟩ : syracuseStep 2688437 = 252041) (by norm_num)
theorem B3024317 : Blo 1592995 3024317 := bbase (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) (by norm_num)
theorem B2016733 : Blo 1592995 2016733 := bbase (se 3 (by rfl) ⟨378137, by rfl⟩ : syracuseStep 2016733 = 756275) (by norm_num)
theorem B2270693 : Blo 1592995 2270693 := bbase (se 4 (by rfl) ⟨212877, by rfl⟩ : syracuseStep 2270693 = 425755) (by norm_num)
theorem B8070677 : Blo 1592995 8070677 := bbase (se 6 (by rfl) ⟨189156, by rfl⟩ : syracuseStep 8070677 = 378313) (by norm_num)
theorem B2688565 : Blo 1592995 2688565 := bbase (se 5 (by rfl) ⟨126026, by rfl⟩ : syracuseStep 2688565 = 252053) (by norm_num)
theorem B2016829 : Blo 1592995 2016829 := bbase (se 3 (by rfl) ⟨378155, by rfl⟩ : syracuseStep 2016829 = 756311) (by norm_num)
theorem B3024469 : Blo 1592995 3024469 := bbase (se 8 (by rfl) ⟨17721, by rfl⟩ : syracuseStep 3024469 = 35443) (by norm_num)
theorem B2688653 : Blo 1592995 2688653 := bbase (se 3 (by rfl) ⟨504122, by rfl⟩ : syracuseStep 2688653 = 1008245) (by norm_num)
theorem B2017001 : Blo 1592995 2017001 := bbase (se 2 (by rfl) ⟨756375, by rfl⟩ : syracuseStep 2017001 = 1512751) (by norm_num)
theorem B2688781 : Blo 1592995 2688781 := bbase (se 3 (by rfl) ⟨504146, by rfl⟩ : syracuseStep 2688781 = 1008293) (by norm_num)
theorem B2017057 : Blo 1592995 2017057 := bbase (se 2 (by rfl) ⟨756396, by rfl⟩ : syracuseStep 2017057 = 1512793) (by norm_num)
theorem B4032301 : Blo 1592995 4032301 := bbase (se 3 (by rfl) ⟨756056, by rfl⟩ : syracuseStep 4032301 = 1512113) (by norm_num)
theorem B3229517 : Blo 1592995 3229517 := bbase (se 3 (by rfl) ⟨605534, by rfl⟩ : syracuseStep 3229517 = 1211069) (by norm_num)
theorem B2688869 : Blo 1592995 2688869 := bbase (se 4 (by rfl) ⟨252081, by rfl⟩ : syracuseStep 2688869 = 504163) (by norm_num)
theorem B2017153 : Blo 1592995 2017153 := bbase (se 2 (by rfl) ⟨756432, by rfl⟩ : syracuseStep 2017153 = 1512865) (by norm_num)
theorem B3024773 : Blo 1592995 3024773 := bbase (se 4 (by rfl) ⟨283572, by rfl⟩ : syracuseStep 3024773 = 567145) (by norm_num)
theorem B4032413 : Blo 1592995 4032413 := bbase (se 3 (by rfl) ⟨756077, by rfl⟩ : syracuseStep 4032413 = 1512155) (by norm_num)
theorem B2688997 : Blo 1592995 2688997 := bbase (se 4 (by rfl) ⟨252093, by rfl⟩ : syracuseStep 2688997 = 504187) (by norm_num)
theorem B1615861 : Blo 1592995 1615861 := bbase (se 5 (by rfl) ⟨75743, by rfl⟩ : syracuseStep 1615861 = 151487) (by norm_num)
theorem B13273109 : Blo 1592995 13273109 := bbase (se 6 (by rfl) ⟨311088, by rfl⟩ : syracuseStep 13273109 = 622177) (by norm_num)
theorem B2017325 : Blo 1592995 2017325 := bbase (se 3 (by rfl) ⟨378248, by rfl⟩ : syracuseStep 2017325 = 756497) (by norm_num)
theorem B2689085 : Blo 1592995 2689085 := bbase (se 3 (by rfl) ⟨504203, by rfl⟩ : syracuseStep 2689085 = 1008407) (by norm_num)
theorem B4032605 : Blo 1592995 4032605 := bbase (se 3 (by rfl) ⟨756113, by rfl⟩ : syracuseStep 4032605 = 1512227) (by norm_num)
theorem B2017381 : Blo 1592995 2017381 := bbase (se 4 (by rfl) ⟨189129, by rfl⟩ : syracuseStep 2017381 = 378259) (by norm_num)
theorem B2689213 : Blo 1592995 2689213 := bbase (se 3 (by rfl) ⟨504227, by rfl⟩ : syracuseStep 2689213 = 1008455) (by norm_num)
theorem B7760069 : Blo 1592995 7760069 := bbase (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) (by norm_num)
theorem B2017477 : Blo 1592995 2017477 := bbase (se 4 (by rfl) ⟨189138, by rfl⟩ : syracuseStep 2017477 = 378277) (by norm_num)
theorem B2689301 : Blo 1592995 2689301 := bbase (se 6 (by rfl) ⟨63030, by rfl⟩ : syracuseStep 2689301 = 126061) (by norm_num)
theorem B2017649 : Blo 1592995 2017649 := bbase (se 2 (by rfl) ⟨756618, by rfl⟩ : syracuseStep 2017649 = 1513237) (by norm_num)
theorem B4540805 : Blo 1592995 4540805 := bbase (se 4 (by rfl) ⟨425700, by rfl⟩ : syracuseStep 4540805 = 851401) (by norm_num)
theorem B2689429 : Blo 1592995 2689429 := bbase (se 6 (by rfl) ⟨63033, by rfl⟩ : syracuseStep 2689429 = 126067) (by norm_num)
theorem B2017705 : Blo 1592995 2017705 := bbase (se 2 (by rfl) ⟨756639, by rfl⟩ : syracuseStep 2017705 = 1513279) (by norm_num)
theorem B4032949 : Blo 1592995 4032949 := bbase (se 5 (by rfl) ⟨189044, by rfl⟩ : syracuseStep 4032949 = 378089) (by norm_num)
theorem B7662053 : Blo 1592995 7662053 := bbase (se 4 (by rfl) ⟨718317, by rfl⟩ : syracuseStep 7662053 = 1436635) (by norm_num)
theorem B2689517 : Blo 1592995 2689517 := bbase (se 3 (by rfl) ⟨504284, by rfl⟩ : syracuseStep 2689517 = 1008569) (by norm_num)
theorem B2017801 : Blo 1592995 2017801 := bbase (se 2 (by rfl) ⟨756675, by rfl⟩ : syracuseStep 2017801 = 1513351) (by norm_num)
theorem B4033061 : Blo 1592995 4033061 := bbase (se 4 (by rfl) ⟨378099, by rfl⟩ : syracuseStep 4033061 = 756199) (by norm_num)
theorem B9202261 : Blo 1592995 9202261 := bbase (se 8 (by rfl) ⟨53919, by rfl⟩ : syracuseStep 9202261 = 107839) (by norm_num)
theorem B2689645 : Blo 1592995 2689645 := bbase (se 3 (by rfl) ⟨504308, by rfl⟩ : syracuseStep 2689645 = 1008617) (by norm_num)
theorem B3025525 : Blo 1592995 3025525 := bbase (se 5 (by rfl) ⟨141821, by rfl⟩ : syracuseStep 3025525 = 283643) (by norm_num)
theorem B2017973 : Blo 1592995 2017973 := bbase (se 5 (by rfl) ⟨94592, by rfl⟩ : syracuseStep 2017973 = 189185) (by norm_num)
theorem B3828421 : Blo 1592995 3828421 := bbase (se 4 (by rfl) ⟨358914, by rfl⟩ : syracuseStep 3828421 = 717829) (by norm_num)
theorem B2689733 : Blo 1592995 2689733 := bbase (se 4 (by rfl) ⟨252162, by rfl⟩ : syracuseStep 2689733 = 504325) (by norm_num)
theorem B5376725 : Blo 1592995 5376725 := bbase (se 7 (by rfl) ⟨63008, by rfl⟩ : syracuseStep 5376725 = 126017) (by norm_num)
theorem B4033253 : Blo 1592995 4033253 := bbase (se 4 (by rfl) ⟨378117, by rfl⟩ : syracuseStep 4033253 = 756235) (by norm_num)
theorem B2018029 : Blo 1592995 2018029 := bbase (se 3 (by rfl) ⟨378380, by rfl⟩ : syracuseStep 2018029 = 756761) (by norm_num)
theorem B3025669 : Blo 1592995 3025669 := bbase (se 4 (by rfl) ⟨283656, by rfl⟩ : syracuseStep 3025669 = 567313) (by norm_num)
theorem B8071973 : Blo 1592995 8071973 := bbase (se 4 (by rfl) ⟨756747, by rfl⟩ : syracuseStep 8071973 = 1513495) (by norm_num)
theorem B2689861 : Blo 1592995 2689861 := bbase (se 4 (by rfl) ⟨252174, by rfl⟩ : syracuseStep 2689861 = 504349) (by norm_num)
theorem B2018125 : Blo 1592995 2018125 := bbase (se 3 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 2018125 = 756797) (by norm_num)
theorem B3230621 : Blo 1592995 3230621 := bbase (se 3 (by rfl) ⟨605741, by rfl⟩ : syracuseStep 3230621 = 1211483) (by norm_num)
theorem B2689949 : Blo 1592995 2689949 := bbase (se 3 (by rfl) ⟨504365, by rfl⟩ : syracuseStep 2689949 = 1008731) (by norm_num)
theorem B3025829 : Blo 1592995 3025829 := bbase (se 4 (by rfl) ⟨283671, by rfl⟩ : syracuseStep 3025829 = 567343) (by norm_num)
theorem B2018297 : Blo 1592995 2018297 := bbase (se 2 (by rfl) ⟨756861, by rfl⟩ : syracuseStep 2018297 = 1513723) (by norm_num)
theorem B2690077 : Blo 1592995 2690077 := bbase (se 3 (by rfl) ⟨504389, by rfl⟩ : syracuseStep 2690077 = 1008779) (by norm_num)
theorem B2018353 : Blo 1592995 2018353 := bbase (se 2 (by rfl) ⟨756882, by rfl⟩ : syracuseStep 2018353 = 1513765) (by norm_num)
theorem B3025973 : Blo 1592995 3025973 := bbase (se 5 (by rfl) ⟨141842, by rfl⟩ : syracuseStep 3025973 = 283685) (by norm_num)
theorem B4033597 : Blo 1592995 4033597 := bbase (se 3 (by rfl) ⟨756299, by rfl⟩ : syracuseStep 4033597 = 1512599) (by norm_num)
theorem B3828845 : Blo 1592995 3828845 := bbase (se 3 (by rfl) ⟨717908, by rfl⟩ : syracuseStep 3828845 = 1435817) (by norm_num)
theorem B2690165 : Blo 1592995 2690165 := bbase (se 5 (by rfl) ⟨126101, by rfl⟩ : syracuseStep 2690165 = 252203) (by norm_num)
theorem B5377157 : Blo 1592995 5377157 := bbase (se 4 (by rfl) ⟨504108, by rfl⟩ : syracuseStep 5377157 = 1008217) (by norm_num)
theorem B7662725 : Blo 1592995 7662725 := bbase (se 4 (by rfl) ⟨718380, by rfl⟩ : syracuseStep 7662725 = 1436761) (by norm_num)
theorem B2018449 : Blo 1592995 2018449 := bbase (se 2 (by rfl) ⟨756918, by rfl⟩ : syracuseStep 2018449 = 1513837) (by norm_num)
theorem B2763941 : Blo 1592995 2763941 := bbase (se 4 (by rfl) ⟨259119, by rfl⟩ : syracuseStep 2763941 = 518239) (by norm_num)
theorem B4033709 : Blo 1592995 4033709 := bbase (se 3 (by rfl) ⟨756320, by rfl⟩ : syracuseStep 4033709 = 1512641) (by norm_num)
theorem B3402965 : Blo 1592995 3402965 := bbase (se 7 (by rfl) ⟨39878, by rfl⟩ : syracuseStep 3402965 = 79757) (by norm_num)
theorem B2690293 : Blo 1592995 2690293 := bbase (se 5 (by rfl) ⟨126107, by rfl⟩ : syracuseStep 2690293 = 252215) (by norm_num)
theorem B2624797 : Blo 1592995 2624797 := bbase (se 3 (by rfl) ⟨492149, by rfl⟩ : syracuseStep 2624797 = 984299) (by norm_num)
theorem B2018621 : Blo 1592995 2018621 := bbase (se 3 (by rfl) ⟨378491, by rfl⟩ : syracuseStep 2018621 = 756983) (by norm_num)
theorem B2690381 : Blo 1592995 2690381 := bbase (se 3 (by rfl) ⟨504446, by rfl⟩ : syracuseStep 2690381 = 1008893) (by norm_num)
theorem B113397077 : Blo 1592995 113397077 := bbase (se 11 (by rfl) ⟨83054, by rfl⟩ : syracuseStep 113397077 = 166109) (by norm_num)
theorem B3026261 : Blo 1592995 3026261 := bbase (se 11 (by rfl) ⟨2216, by rfl⟩ : syracuseStep 3026261 = 4433) (by norm_num)
theorem B3403109 : Blo 1592995 3403109 := bbase (se 4 (by rfl) ⟨319041, by rfl⟩ : syracuseStep 3403109 = 638083) (by norm_num)
theorem B4033901 : Blo 1592995 4033901 := bbase (se 3 (by rfl) ⟨756356, by rfl⟩ : syracuseStep 4033901 = 1512713) (by norm_num)
theorem B3829133 : Blo 1592995 3829133 := bbase (se 3 (by rfl) ⟨717962, by rfl⟩ : syracuseStep 3829133 = 1435925) (by norm_num)
theorem B2690509 : Blo 1592995 2690509 := bbase (se 3 (by rfl) ⟨504470, by rfl⟩ : syracuseStep 2690509 = 1008941) (by norm_num)
theorem B3026413 : Blo 1592995 3026413 := bbase (se 3 (by rfl) ⟨567452, by rfl⟩ : syracuseStep 3026413 = 1134905) (by norm_num)
theorem B2764301 : Blo 1592995 2764301 := bbase (se 3 (by rfl) ⟨518306, by rfl⟩ : syracuseStep 2764301 = 1036613) (by norm_num)
theorem B15314453 : Blo 1592995 15314453 := bbase (se 6 (by rfl) ⟨358932, by rfl⟩ : syracuseStep 15314453 = 717865) (by norm_num)
theorem B2690597 : Blo 1592995 2690597 := bbase (se 4 (by rfl) ⟨252243, by rfl⟩ : syracuseStep 2690597 = 504487) (by norm_num)
theorem B4541989 : Blo 1592995 4541989 := bbase (se 4 (by rfl) ⟨425811, by rfl⟩ : syracuseStep 4541989 = 851623) (by norm_num)
theorem B5377589 : Blo 1592995 5377589 := bbase (se 5 (by rfl) ⟨252074, by rfl⟩ : syracuseStep 5377589 = 504149) (by norm_num)
theorem B3067445 : Blo 1592995 3067445 := bbase (se 5 (by rfl) ⟨143786, by rfl⟩ : syracuseStep 3067445 = 287573) (by norm_num)
theorem B6049349 : Blo 1592995 6049349 := bbase (se 4 (by rfl) ⟨567126, by rfl⟩ : syracuseStep 6049349 = 1134253) (by norm_num)
theorem B6131285 : Blo 1592995 6131285 := bbase (se 8 (by rfl) ⟨35925, by rfl⟩ : syracuseStep 6131285 = 71851) (by norm_num)
theorem B2690725 : Blo 1592995 2690725 := bbase (se 4 (by rfl) ⟨252255, by rfl⟩ : syracuseStep 2690725 = 504511) (by norm_num)
theorem B4034245 : Blo 1592995 4034245 := bbase (se 4 (by rfl) ⟨378210, by rfl⟩ : syracuseStep 4034245 = 756421) (by norm_num)
theorem B12111605 : Blo 1592995 12111605 := bbase (se 5 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 12111605 = 1135463) (by norm_num)
theorem B2690813 : Blo 1592995 2690813 := bbase (se 3 (by rfl) ⟨504527, by rfl⟩ : syracuseStep 2690813 = 1009055) (by norm_num)
theorem B2043649 : Blo 1592995 2043649 := bbase (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) (by norm_num)
theorem B6811397 : Blo 1592995 6811397 := bbase (se 4 (by rfl) ⟨638568, by rfl⟩ : syracuseStep 6811397 = 1277137) (by norm_num)
theorem B3026717 : Blo 1592995 3026717 := bbase (se 3 (by rfl) ⟨567509, by rfl⟩ : syracuseStep 3026717 = 1135019) (by norm_num)
theorem B4034357 : Blo 1592995 4034357 := bbase (se 5 (by rfl) ⟨189110, by rfl⟩ : syracuseStep 4034357 = 378221) (by norm_num)
theorem B2871101 : Blo 1592995 2871101 := bbase (se 3 (by rfl) ⟨538331, by rfl⟩ : syracuseStep 2871101 = 1076663) (by norm_num)
theorem B6049637 : Blo 1592995 6049637 := bbase (se 4 (by rfl) ⟨567153, by rfl⟩ : syracuseStep 6049637 = 1134307) (by norm_num)
theorem B2690941 : Blo 1592995 2690941 := bbase (se 3 (by rfl) ⟨504551, by rfl⟩ : syracuseStep 2690941 = 1009103) (by norm_num)
theorem B5107637 : Blo 1592995 5107637 := bbase (se 5 (by rfl) ⟨239420, by rfl⟩ : syracuseStep 5107637 = 478841) (by norm_num)
theorem B7655381 : Blo 1592995 7655381 := bbase (se 7 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 7655381 = 179423) (by norm_num)
theorem B2691029 : Blo 1592995 2691029 := bbase (se 7 (by rfl) ⟨31535, by rfl⟩ : syracuseStep 2691029 = 63071) (by norm_num)
theorem B2551781 : Blo 1592995 2551781 := bbase (se 4 (by rfl) ⟨239229, by rfl⟩ : syracuseStep 2551781 = 478459) (by norm_num)
theorem B5378021 : Blo 1592995 5378021 := bbase (se 4 (by rfl) ⟨504189, by rfl⟩ : syracuseStep 5378021 = 1008379) (by norm_num)
theorem B4034549 : Blo 1592995 4034549 := bbase (se 5 (by rfl) ⟨189119, by rfl⟩ : syracuseStep 4034549 = 378239) (by norm_num)
theorem B6131717 : Blo 1592995 6131717 := bbase (se 4 (by rfl) ⟨574848, by rfl⟩ : syracuseStep 6131717 = 1149697) (by norm_num)
theorem B5451781 : Blo 1592995 5451781 := bbase (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) (by norm_num)
theorem B6811685 : Blo 1592995 6811685 := bbase (se 4 (by rfl) ⟨638595, by rfl⟩ : syracuseStep 6811685 = 1277191) (by norm_num)
theorem B8073269 : Blo 1592995 8073269 := bbase (se 5 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 8073269 = 756869) (by norm_num)
theorem B3403853 : Blo 1592995 3403853 := bbase (se 3 (by rfl) ⟨638222, by rfl⟩ : syracuseStep 3403853 = 1276445) (by norm_num)
theorem B2691157 : Blo 1592995 2691157 := bbase (se 8 (by rfl) ⟨15768, by rfl⟩ : syracuseStep 2691157 = 31537) (by norm_num)
theorem B2871389 : Blo 1592995 2871389 := bbase (se 3 (by rfl) ⟨538385, by rfl⟩ : syracuseStep 2871389 = 1076771) (by norm_num)
theorem B1724537 : Blo 1592995 1724537 := bbase (se 2 (by rfl) ⟨646701, by rfl⟩ : syracuseStep 1724537 = 1293403) (by norm_num)
theorem B12103829 : Blo 1592995 12103829 := bbase (se 6 (by rfl) ⟨283683, by rfl⟩ : syracuseStep 12103829 = 567367) (by norm_num)
theorem B2691245 : Blo 1592995 2691245 := bbase (se 3 (by rfl) ⟨504608, by rfl⟩ : syracuseStep 2691245 = 1009217) (by norm_num)
theorem B22974677 : Blo 1592995 22974677 := bbase (se 7 (by rfl) ⟨269234, by rfl⟩ : syracuseStep 22974677 = 538469) (by norm_num)
theorem B8179973 : Blo 1592995 8179973 := bbase (se 4 (by rfl) ⟨766872, by rfl⟩ : syracuseStep 8179973 = 1533745) (by norm_num)
theorem B3584285 : Blo 1592995 3584285 := bbase (se 3 (by rfl) ⟨672053, by rfl⟩ : syracuseStep 3584285 = 1344107) (by norm_num)
theorem B2691373 : Blo 1592995 2691373 := bbase (se 3 (by rfl) ⟨504632, by rfl⟩ : syracuseStep 2691373 = 1009265) (by norm_num)
theorem B2871605 : Blo 1592995 2871605 := bbase (se 5 (by rfl) ⟨134606, by rfl⟩ : syracuseStep 2871605 = 269213) (by norm_num)
theorem B4034893 : Blo 1592995 4034893 := bbase (se 3 (by rfl) ⟨756542, by rfl⟩ : syracuseStep 4034893 = 1513085) (by norm_num)
theorem B4092245 : Blo 1592995 4092245 := bbase (se 10 (by rfl) ⟨5994, by rfl⟩ : syracuseStep 4092245 = 11989) (by norm_num)
theorem B3584357 : Blo 1592995 3584357 := bbase (se 4 (by rfl) ⟨336033, by rfl⟩ : syracuseStep 3584357 = 672067) (by norm_num)
theorem B2691461 : Blo 1592995 2691461 := bbase (se 4 (by rfl) ⟨252324, by rfl⟩ : syracuseStep 2691461 = 504649) (by norm_num)
theorem B5378453 : Blo 1592995 5378453 := bbase (se 6 (by rfl) ⟨126057, by rfl⟩ : syracuseStep 5378453 = 252115) (by norm_num)
theorem B3584429 : Blo 1592995 3584429 := bbase (se 3 (by rfl) ⟨672080, by rfl⟩ : syracuseStep 3584429 = 1344161) (by norm_num)
theorem B4035005 : Blo 1592995 4035005 := bbase (se 3 (by rfl) ⟨756563, by rfl⟩ : syracuseStep 4035005 = 1513127) (by norm_num)
theorem B8065493 : Blo 1592995 8065493 := bbase (se 7 (by rfl) ⟨94517, by rfl⟩ : syracuseStep 8065493 = 189035) (by norm_num)
theorem B2183653 : Blo 1592995 2183653 := bbase (se 4 (by rfl) ⟨204717, by rfl⟩ : syracuseStep 2183653 = 409435) (by norm_num)
theorem B5247461 : Blo 1592995 5247461 := bbase (se 4 (by rfl) ⟨491949, by rfl⟩ : syracuseStep 5247461 = 983899) (by norm_num)
theorem B2912741 : Blo 1592995 2912741 := bbase (se 4 (by rfl) ⟨273069, by rfl⟩ : syracuseStep 2912741 = 546139) (by norm_num)
theorem B3584501 : Blo 1592995 3584501 := bbase (se 5 (by rfl) ⟨168023, by rfl⟩ : syracuseStep 3584501 = 336047) (by norm_num)
theorem B3027469 : Blo 1592995 3027469 := bbase (se 3 (by rfl) ⟨567650, by rfl⟩ : syracuseStep 3027469 = 1135301) (by norm_num)
theorem B3584573 : Blo 1592995 3584573 := bbase (se 3 (by rfl) ⟨672107, by rfl⟩ : syracuseStep 3584573 = 1344215) (by norm_num)
theorem B4035197 : Blo 1592995 4035197 := bbase (se 3 (by rfl) ⟨756599, by rfl⟩ : syracuseStep 4035197 = 1513199) (by norm_num)
theorem B3584645 : Blo 1592995 3584645 := bbase (se 4 (by rfl) ⟨336060, by rfl⟩ : syracuseStep 3584645 = 672121) (by norm_num)
theorem B5526149 : Blo 1592995 5526149 := bbase (se 4 (by rfl) ⟨518076, by rfl⟩ : syracuseStep 5526149 = 1036153) (by norm_num)
theorem B3027613 : Blo 1592995 3027613 := bbase (se 3 (by rfl) ⟨567677, by rfl⟩ : syracuseStep 3027613 = 1135355) (by norm_num)
theorem B3232453 : Blo 1592995 3232453 := bbase (se 4 (by rfl) ⟨303042, by rfl⟩ : syracuseStep 3232453 = 606085) (by norm_num)
theorem B3584717 : Blo 1592995 3584717 := bbase (se 3 (by rfl) ⟨672134, by rfl⟩ : syracuseStep 3584717 = 1344269) (by norm_num)
theorem B3584789 : Blo 1592995 3584789 := bbase (se 6 (by rfl) ⟨84018, by rfl⟩ : syracuseStep 3584789 = 168037) (by norm_num)
theorem B6812437 : Blo 1592995 6812437 := bbase (se 6 (by rfl) ⟨159666, by rfl⟩ : syracuseStep 6812437 = 319333) (by norm_num)
theorem B3404605 : Blo 1592995 3404605 := bbase (se 3 (by rfl) ⟨638363, by rfl⟩ : syracuseStep 3404605 = 1276727) (by norm_num)
theorem B3027773 : Blo 1592995 3027773 := bbase (se 3 (by rfl) ⟨567707, by rfl⟩ : syracuseStep 3027773 = 1135415) (by norm_num)
theorem B5378885 : Blo 1592995 5378885 := bbase (se 4 (by rfl) ⟨504270, by rfl⟩ : syracuseStep 5378885 = 1008541) (by norm_num)
theorem B3584861 : Blo 1592995 3584861 := bbase (se 3 (by rfl) ⟨672161, by rfl⟩ : syracuseStep 3584861 = 1344323) (by norm_num)
theorem B2552717 : Blo 1592995 2552717 := bbase (se 3 (by rfl) ⟨478634, by rfl⟩ : syracuseStep 2552717 = 957269) (by norm_num)
theorem B3584933 : Blo 1592995 3584933 := bbase (se 4 (by rfl) ⟨336087, by rfl⟩ : syracuseStep 3584933 = 672175) (by norm_num)
theorem B3404749 : Blo 1592995 3404749 := bbase (se 3 (by rfl) ⟨638390, by rfl⟩ : syracuseStep 3404749 = 1276781) (by norm_num)
theorem B3027917 : Blo 1592995 3027917 := bbase (se 3 (by rfl) ⟨567734, by rfl⟩ : syracuseStep 3027917 = 1135469) (by norm_num)
theorem B5452757 : Blo 1592995 5452757 := bbase (se 7 (by rfl) ⟨63899, by rfl⟩ : syracuseStep 5452757 = 127799) (by norm_num)
theorem B4035541 : Blo 1592995 4035541 := bbase (se 7 (by rfl) ⟨47291, by rfl⟩ : syracuseStep 4035541 = 94583) (by norm_num)
theorem B3585005 : Blo 1592995 3585005 := bbase (se 3 (by rfl) ⟨672188, by rfl⟩ : syracuseStep 3585005 = 1344377) (by norm_num)
theorem B6050821 : Blo 1592995 6050821 := bbase (se 4 (by rfl) ⟨567264, by rfl⟩ : syracuseStep 6050821 = 1134529) (by norm_num)
theorem B3585077 : Blo 1592995 3585077 := bbase (se 5 (by rfl) ⟨168050, by rfl⟩ : syracuseStep 3585077 = 336101) (by norm_num)
theorem B4035653 : Blo 1592995 4035653 := bbase (se 4 (by rfl) ⟨378342, by rfl⟩ : syracuseStep 4035653 = 756685) (by norm_num)
theorem B7271525 : Blo 1592995 7271525 := bbase (se 4 (by rfl) ⟨681705, by rfl⟩ : syracuseStep 7271525 = 1363411) (by norm_num)
theorem B4846709 : Blo 1592995 4846709 := bbase (se 5 (by rfl) ⟨227189, by rfl⟩ : syracuseStep 4846709 = 454379) (by norm_num)
theorem B3585149 : Blo 1592995 3585149 := bbase (se 3 (by rfl) ⟨672215, by rfl⟩ : syracuseStep 3585149 = 1344431) (by norm_num)
theorem B3634301 : Blo 1592995 3634301 := bbase (se 3 (by rfl) ⟨681431, by rfl⟩ : syracuseStep 3634301 = 1362863) (by norm_num)
theorem B2872469 : Blo 1592995 2872469 := bbase (se 6 (by rfl) ⟨67323, by rfl⟩ : syracuseStep 2872469 = 134647) (by norm_num)
theorem B3585221 : Blo 1592995 3585221 := bbase (se 4 (by rfl) ⟨336114, by rfl⟩ : syracuseStep 3585221 = 672229) (by norm_num)
theorem B4846805 : Blo 1592995 4846805 := bbase (se 7 (by rfl) ⟨56798, by rfl⟩ : syracuseStep 4846805 = 113597) (by norm_num)
theorem B5379317 : Blo 1592995 5379317 := bbase (se 5 (by rfl) ⟨252155, by rfl⟩ : syracuseStep 5379317 = 504311) (by norm_num)
theorem B4035845 : Blo 1592995 4035845 := bbase (se 4 (by rfl) ⟨378360, by rfl⟩ : syracuseStep 4035845 = 756721) (by norm_num)
theorem B3585293 : Blo 1592995 3585293 := bbase (se 3 (by rfl) ⟨672242, by rfl⟩ : syracuseStep 3585293 = 1344485) (by norm_num)
theorem B2553101 : Blo 1592995 2553101 := bbase (se 3 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 2553101 = 957413) (by norm_num)
theorem B6051125 : Blo 1592995 6051125 := bbase (se 5 (by rfl) ⟨283646, by rfl⟩ : syracuseStep 6051125 = 567293) (by norm_num)
theorem B3405125 : Blo 1592995 3405125 := bbase (se 4 (by rfl) ⟨319230, by rfl⟩ : syracuseStep 3405125 = 638461) (by norm_num)
theorem B8074565 : Blo 1592995 8074565 := bbase (se 4 (by rfl) ⟨756990, by rfl⟩ : syracuseStep 8074565 = 1513981) (by norm_num)
theorem B3585365 : Blo 1592995 3585365 := bbase (se 13 (by rfl) ⟨656, by rfl⟩ : syracuseStep 3585365 = 1313) (by norm_num)
theorem B1701209 : Blo 1592995 1701209 := bbase (se 2 (by rfl) ⟨637953, by rfl⟩ : syracuseStep 1701209 = 1275907) (by norm_num)
theorem B2872693 : Blo 1592995 2872693 := bbase (se 5 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 2872693 = 269315) (by norm_num)
theorem B2553229 : Blo 1592995 2553229 := bbase (se 3 (by rfl) ⟨478730, by rfl⟩ : syracuseStep 2553229 = 957461) (by norm_num)
theorem B3585437 : Blo 1592995 3585437 := bbase (se 3 (by rfl) ⟨672269, by rfl⟩ : syracuseStep 3585437 = 1344539) (by norm_num)
theorem B1701281 : Blo 1592995 1701281 := bbase (se 2 (by rfl) ⟨637980, by rfl⟩ : syracuseStep 1701281 = 1275961) (by norm_num)
theorem B3585509 : Blo 1592995 3585509 := bbase (se 4 (by rfl) ⟨336141, by rfl⟩ : syracuseStep 3585509 = 672283) (by norm_num)
theorem B2389493 : Blo 1592995 2389493 := bbase (se 5 (by rfl) ⟨112007, by rfl⟩ : syracuseStep 2389493 = 224015) (by norm_num)
theorem B12932597 : Blo 1592995 12932597 := bbase (se 5 (by rfl) ⟨606215, by rfl⟩ : syracuseStep 12932597 = 1212431) (by norm_num)
theorem B2389517 : Blo 1592995 2389517 := bbase (se 3 (by rfl) ⟨448034, by rfl⟩ : syracuseStep 2389517 = 896069) (by norm_num)
theorem B12441109 : Blo 1592995 12441109 := bbase (se 6 (by rfl) ⟨291588, by rfl⟩ : syracuseStep 12441109 = 583177) (by norm_num)
theorem B2389541 : Blo 1592995 2389541 := bbase (se 4 (by rfl) ⟨224019, by rfl⟩ : syracuseStep 2389541 = 448039) (by norm_num)
theorem B3585581 : Blo 1592995 3585581 := bbase (se 3 (by rfl) ⟨672296, by rfl⟩ : syracuseStep 3585581 = 1344593) (by norm_num)
theorem B2389565 : Blo 1592995 2389565 := bbase (se 3 (by rfl) ⟨448043, by rfl⟩ : syracuseStep 2389565 = 896087) (by norm_num)
theorem B2389589 : Blo 1592995 2389589 := bbase (se 8 (by rfl) ⟨14001, by rfl⟩ : syracuseStep 2389589 = 28003) (by norm_num)
theorem B1701469 : Blo 1592995 1701469 := bbase (se 3 (by rfl) ⟨319025, by rfl⟩ : syracuseStep 1701469 = 638051) (by norm_num)
theorem B4036189 : Blo 1592995 4036189 := bbase (se 3 (by rfl) ⟨756785, by rfl⟩ : syracuseStep 4036189 = 1513571) (by norm_num)
theorem B2389613 : Blo 1592995 2389613 := bbase (se 3 (by rfl) ⟨448052, by rfl⟩ : syracuseStep 2389613 = 896105) (by norm_num)
theorem B3585653 : Blo 1592995 3585653 := bbase (se 5 (by rfl) ⟨168077, by rfl⟩ : syracuseStep 3585653 = 336155) (by norm_num)
theorem B2389637 : Blo 1592995 2389637 := bbase (se 4 (by rfl) ⟨224028, by rfl⟩ : syracuseStep 2389637 = 448057) (by norm_num)
theorem B2389661 : Blo 1592995 2389661 := bbase (se 3 (by rfl) ⟨448061, by rfl⟩ : syracuseStep 2389661 = 896123) (by norm_num)
theorem B5379749 : Blo 1592995 5379749 := bbase (se 4 (by rfl) ⟨504351, by rfl⟩ : syracuseStep 5379749 = 1008703) (by norm_num)
theorem B2389685 : Blo 1592995 2389685 := bbase (se 5 (by rfl) ⟨112016, by rfl⟩ : syracuseStep 2389685 = 224033) (by norm_num)
theorem B3405493 : Blo 1592995 3405493 := bbase (se 5 (by rfl) ⟨159632, by rfl⟩ : syracuseStep 3405493 = 319265) (by norm_num)
theorem B3585725 : Blo 1592995 3585725 := bbase (se 3 (by rfl) ⟨672323, by rfl⟩ : syracuseStep 3585725 = 1344647) (by norm_num)
theorem B2389709 : Blo 1592995 2389709 := bbase (se 3 (by rfl) ⟨448070, by rfl⟩ : syracuseStep 2389709 = 896141) (by norm_num)
theorem B4036301 : Blo 1592995 4036301 := bbase (se 3 (by rfl) ⟨756806, by rfl⟩ : syracuseStep 4036301 = 1513613) (by norm_num)
theorem B2389733 : Blo 1592995 2389733 := bbase (se 4 (by rfl) ⟨224037, by rfl⟩ : syracuseStep 2389733 = 448075) (by norm_num)
theorem B8066789 : Blo 1592995 8066789 := bbase (se 4 (by rfl) ⟨756261, by rfl⟩ : syracuseStep 8066789 = 1512523) (by norm_num)
theorem B13801205 : Blo 1592995 13801205 := bbase (se 5 (by rfl) ⟨646931, by rfl⟩ : syracuseStep 13801205 = 1293863) (by norm_num)
theorem B2389757 : Blo 1592995 2389757 := bbase (se 3 (by rfl) ⟨448079, by rfl⟩ : syracuseStep 2389757 = 896159) (by norm_num)
theorem B3585797 : Blo 1592995 3585797 := bbase (se 4 (by rfl) ⟨336168, by rfl⟩ : syracuseStep 3585797 = 672337) (by norm_num)
theorem B2389781 : Blo 1592995 2389781 := bbase (se 6 (by rfl) ⟨56010, by rfl⟩ : syracuseStep 2389781 = 112021) (by norm_num)
theorem B1701653 : Blo 1592995 1701653 := bbase (se 6 (by rfl) ⟨39882, by rfl⟩ : syracuseStep 1701653 = 79765) (by norm_num)
theorem B2389805 : Blo 1592995 2389805 := bbase (se 3 (by rfl) ⟨448088, by rfl⟩ : syracuseStep 2389805 = 896177) (by norm_num)
theorem B2389829 : Blo 1592995 2389829 := bbase (se 4 (by rfl) ⟨224046, by rfl⟩ : syracuseStep 2389829 = 448093) (by norm_num)
theorem B3585869 : Blo 1592995 3585869 := bbase (se 3 (by rfl) ⟨672350, by rfl⟩ : syracuseStep 3585869 = 1344701) (by norm_num)
theorem B2389853 : Blo 1592995 2389853 := bbase (se 3 (by rfl) ⟨448097, by rfl⟩ : syracuseStep 2389853 = 896195) (by norm_num)
theorem B2725741 : Blo 1592995 2725741 := bbase (se 3 (by rfl) ⟨511076, by rfl⟩ : syracuseStep 2725741 = 1022153) (by norm_num)
theorem B2389877 : Blo 1592995 2389877 := bbase (se 5 (by rfl) ⟨112025, by rfl⟩ : syracuseStep 2389877 = 224051) (by norm_num)
theorem B2389901 : Blo 1592995 2389901 := bbase (se 3 (by rfl) ⟨448106, by rfl⟩ : syracuseStep 2389901 = 896213) (by norm_num)
theorem B4036493 : Blo 1592995 4036493 := bbase (se 3 (by rfl) ⟨756842, by rfl⟩ : syracuseStep 4036493 = 1513685) (by norm_num)
theorem B6805397 : Blo 1592995 6805397 := bbase (se 6 (by rfl) ⟨159501, by rfl⟩ : syracuseStep 6805397 = 319003) (by norm_num)
theorem B3585941 : Blo 1592995 3585941 := bbase (se 6 (by rfl) ⟨84045, by rfl⟩ : syracuseStep 3585941 = 168091) (by norm_num)
theorem B2389925 : Blo 1592995 2389925 := bbase (se 4 (by rfl) ⟨224055, by rfl⟩ : syracuseStep 2389925 = 448111) (by norm_num)
theorem B13612981 : Blo 1592995 13612981 := bbase (se 5 (by rfl) ⟨638108, by rfl⟩ : syracuseStep 13612981 = 1276217) (by norm_num)
theorem B2389949 : Blo 1592995 2389949 := bbase (se 3 (by rfl) ⟨448115, by rfl⟩ : syracuseStep 2389949 = 896231) (by norm_num)
theorem B2389973 : Blo 1592995 2389973 := bbase (se 7 (by rfl) ⟨28007, by rfl⟩ : syracuseStep 2389973 = 56015) (by norm_num)
theorem B3586013 : Blo 1592995 3586013 := bbase (se 3 (by rfl) ⟨672377, by rfl⟩ : syracuseStep 3586013 = 1344755) (by norm_num)
theorem B1914845 : Blo 1592995 1914845 := bbase (se 3 (by rfl) ⟨359033, by rfl⟩ : syracuseStep 1914845 = 718067) (by norm_num)
theorem B2389997 : Blo 1592995 2389997 := bbase (se 3 (by rfl) ⟨448124, by rfl⟩ : syracuseStep 2389997 = 896249) (by norm_num)
theorem B2390021 : Blo 1592995 2390021 := bbase (se 4 (by rfl) ⟨224064, by rfl⟩ : syracuseStep 2390021 = 448129) (by norm_num)
theorem B2390045 : Blo 1592995 2390045 := bbase (se 3 (by rfl) ⟨448133, by rfl⟩ : syracuseStep 2390045 = 896267) (by norm_num)
theorem B3586085 : Blo 1592995 3586085 := bbase (se 4 (by rfl) ⟨336195, by rfl⟩ : syracuseStep 3586085 = 672391) (by norm_num)
theorem B2390069 : Blo 1592995 2390069 := bbase (se 5 (by rfl) ⟨112034, by rfl⟩ : syracuseStep 2390069 = 224069) (by norm_num)
theorem B2390093 : Blo 1592995 2390093 := bbase (se 3 (by rfl) ⟨448142, by rfl⟩ : syracuseStep 2390093 = 896285) (by norm_num)
theorem B5380181 : Blo 1592995 5380181 := bbase (se 8 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 5380181 = 63049) (by norm_num)
theorem B2390117 : Blo 1592995 2390117 := bbase (se 4 (by rfl) ⟨224073, by rfl⟩ : syracuseStep 2390117 = 448147) (by norm_num)
theorem B3586157 : Blo 1592995 3586157 := bbase (se 3 (by rfl) ⟨672404, by rfl⟩ : syracuseStep 3586157 = 1344809) (by norm_num)
theorem B2390141 : Blo 1592995 2390141 := bbase (se 3 (by rfl) ⟨448151, by rfl⟩ : syracuseStep 2390141 = 896303) (by norm_num)
theorem B1792129 : Blo 1592995 1792129 := bbase (se 2 (by rfl) ⟨672048, by rfl⟩ : syracuseStep 1792129 = 1344097) (by norm_num)
theorem B2046097 : Blo 1592995 2046097 := bbase (se 2 (by rfl) ⟨767286, by rfl⟩ : syracuseStep 2046097 = 1534573) (by norm_num)
theorem B2390165 : Blo 1592995 2390165 := bbase (se 6 (by rfl) ⟨56019, by rfl⟩ : syracuseStep 2390165 = 112039) (by norm_num)
theorem B1792165 : Blo 1592995 1792165 := bbase (se 4 (by rfl) ⟨168015, by rfl⟩ : syracuseStep 1792165 = 336031) (by norm_num)
theorem B2390189 : Blo 1592995 2390189 := bbase (se 3 (by rfl) ⟨448160, by rfl⟩ : syracuseStep 2390189 = 896321) (by norm_num)
theorem B3586229 : Blo 1592995 3586229 := bbase (se 5 (by rfl) ⟨168104, by rfl⟩ : syracuseStep 3586229 = 336209) (by norm_num)
theorem B2390213 : Blo 1592995 2390213 := bbase (se 4 (by rfl) ⟨224082, by rfl⟩ : syracuseStep 2390213 = 448165) (by norm_num)
theorem B1792201 : Blo 1592995 1792201 := bbase (se 2 (by rfl) ⟨672075, by rfl⟩ : syracuseStep 1792201 = 1344151) (by norm_num)
theorem B2390237 : Blo 1592995 2390237 := bbase (se 3 (by rfl) ⟨448169, by rfl⟩ : syracuseStep 2390237 = 896339) (by norm_num)
theorem B4036837 : Blo 1592995 4036837 := bbase (se 4 (by rfl) ⟨378453, by rfl⟩ : syracuseStep 4036837 = 756907) (by norm_num)
theorem B1792237 : Blo 1592995 1792237 := bbase (se 3 (by rfl) ⟨336044, by rfl⟩ : syracuseStep 1792237 = 672089) (by norm_num)
theorem B2390261 : Blo 1592995 2390261 := bbase (se 5 (by rfl) ⟨112043, by rfl⟩ : syracuseStep 2390261 = 224087) (by norm_num)
theorem B3586301 : Blo 1592995 3586301 := bbase (se 3 (by rfl) ⟨672431, by rfl⟩ : syracuseStep 3586301 = 1344863) (by norm_num)
theorem B2390285 : Blo 1592995 2390285 := bbase (se 3 (by rfl) ⟨448178, by rfl⟩ : syracuseStep 2390285 = 896357) (by norm_num)
theorem B1792273 : Blo 1592995 1792273 := bbase (se 2 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 1792273 = 1344205) (by norm_num)
theorem B2390309 : Blo 1592995 2390309 := bbase (se 4 (by rfl) ⟨224091, by rfl⟩ : syracuseStep 2390309 = 448183) (by norm_num)
theorem B1792309 : Blo 1592995 1792309 := bbase (se 5 (by rfl) ⟨84014, by rfl⟩ : syracuseStep 1792309 = 168029) (by norm_num)
theorem B10213685 : Blo 1592995 10213685 := bbase (se 5 (by rfl) ⟨478766, by rfl⟩ : syracuseStep 10213685 = 957533) (by norm_num)
theorem B2390333 : Blo 1592995 2390333 := bbase (se 3 (by rfl) ⟨448187, by rfl⟩ : syracuseStep 2390333 = 896375) (by norm_num)
theorem B3586373 : Blo 1592995 3586373 := bbase (se 4 (by rfl) ⟨336222, by rfl⟩ : syracuseStep 3586373 = 672445) (by norm_num)
theorem B2390357 : Blo 1592995 2390357 := bbase (se 10 (by rfl) ⟨3501, by rfl⟩ : syracuseStep 2390357 = 7003) (by norm_num)
theorem B4036949 : Blo 1592995 4036949 := bbase (se 10 (by rfl) ⟨5913, by rfl⟩ : syracuseStep 4036949 = 11827) (by norm_num)
theorem B1792345 : Blo 1592995 1792345 := bbase (se 2 (by rfl) ⟨672129, by rfl⟩ : syracuseStep 1792345 = 1344259) (by norm_num)
theorem B2390381 : Blo 1592995 2390381 := bbase (se 3 (by rfl) ⟨448196, by rfl⟩ : syracuseStep 2390381 = 896393) (by norm_num)
theorem B2554229 : Blo 1592995 2554229 := bbase (se 5 (by rfl) ⟨119729, by rfl⟩ : syracuseStep 2554229 = 239459) (by norm_num)
theorem B1792381 : Blo 1592995 1792381 := bbase (se 3 (by rfl) ⟨336071, by rfl⟩ : syracuseStep 1792381 = 672143) (by norm_num)
theorem B2390405 : Blo 1592995 2390405 := bbase (se 4 (by rfl) ⟨224100, by rfl⟩ : syracuseStep 2390405 = 448201) (by norm_num)
theorem B3586445 : Blo 1592995 3586445 := bbase (se 3 (by rfl) ⟨672458, by rfl⟩ : syracuseStep 3586445 = 1344917) (by norm_num)
theorem B2390429 : Blo 1592995 2390429 := bbase (se 3 (by rfl) ⟨448205, by rfl⟩ : syracuseStep 2390429 = 896411) (by norm_num)
theorem B1792417 : Blo 1592995 1792417 := bbase (se 2 (by rfl) ⟨672156, by rfl⟩ : syracuseStep 1792417 = 1344313) (by norm_num)
theorem B2390453 : Blo 1592995 2390453 := bbase (se 5 (by rfl) ⟨112052, by rfl⟩ : syracuseStep 2390453 = 224105) (by norm_num)
theorem B4536773 : Blo 1592995 4536773 := bbase (se 4 (by rfl) ⟨425322, by rfl⟩ : syracuseStep 4536773 = 850645) (by norm_num)
theorem B1792453 : Blo 1592995 1792453 := bbase (se 4 (by rfl) ⟨168042, by rfl⟩ : syracuseStep 1792453 = 336085) (by norm_num)
theorem B2390477 : Blo 1592995 2390477 := bbase (se 3 (by rfl) ⟨448214, by rfl⟩ : syracuseStep 2390477 = 896429) (by norm_num)
theorem B3586517 : Blo 1592995 3586517 := bbase (se 7 (by rfl) ⟨42029, by rfl⟩ : syracuseStep 3586517 = 84059) (by norm_num)
theorem B3832285 : Blo 1592995 3832285 := bbase (se 3 (by rfl) ⟨718553, by rfl⟩ : syracuseStep 3832285 = 1437107) (by norm_num)
theorem B2390501 : Blo 1592995 2390501 := bbase (se 4 (by rfl) ⟨224109, by rfl⟩ : syracuseStep 2390501 = 448219) (by norm_num)
theorem B1792489 : Blo 1592995 1792489 := bbase (se 2 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 1792489 = 1344367) (by norm_num)
theorem B2554357 : Blo 1592995 2554357 := bbase (se 5 (by rfl) ⟨119735, by rfl⟩ : syracuseStep 2554357 = 239471) (by norm_num)
theorem B2390525 : Blo 1592995 2390525 := bbase (se 3 (by rfl) ⟨448223, by rfl⟩ : syracuseStep 2390525 = 896447) (by norm_num)
theorem B1702405 : Blo 1592995 1702405 := bbase (se 4 (by rfl) ⟨159600, by rfl⟩ : syracuseStep 1702405 = 319201) (by norm_num)
theorem B5380613 : Blo 1592995 5380613 := bbase (se 4 (by rfl) ⟨504432, by rfl⟩ : syracuseStep 5380613 = 1008865) (by norm_num)
theorem B1792525 : Blo 1592995 1792525 := bbase (se 3 (by rfl) ⟨336098, by rfl⟩ : syracuseStep 1792525 = 672197) (by norm_num)
theorem B2390549 : Blo 1592995 2390549 := bbase (se 6 (by rfl) ⟨56028, by rfl⟩ : syracuseStep 2390549 = 112057) (by norm_num)
theorem B4037141 : Blo 1592995 4037141 := bbase (se 6 (by rfl) ⟨94620, by rfl⟩ : syracuseStep 4037141 = 189241) (by norm_num)
theorem B3586589 : Blo 1592995 3586589 := bbase (se 3 (by rfl) ⟨672485, by rfl⟩ : syracuseStep 3586589 = 1344971) (by norm_num)
theorem B2390573 : Blo 1592995 2390573 := bbase (se 3 (by rfl) ⟨448232, by rfl⟩ : syracuseStep 2390573 = 896465) (by norm_num)
theorem B1792561 : Blo 1592995 1792561 := bbase (se 2 (by rfl) ⟨672210, by rfl⟩ : syracuseStep 1792561 = 1344421) (by norm_num)
theorem B2390597 : Blo 1592995 2390597 := bbase (se 4 (by rfl) ⟨224118, by rfl⟩ : syracuseStep 2390597 = 448237) (by norm_num)
theorem B1702477 : Blo 1592995 1702477 := bbase (se 3 (by rfl) ⟨319214, by rfl⟩ : syracuseStep 1702477 = 638429) (by norm_num)
theorem B1792597 : Blo 1592995 1792597 := bbase (se 8 (by rfl) ⟨10503, by rfl⟩ : syracuseStep 1792597 = 21007) (by norm_num)
theorem B2390621 : Blo 1592995 2390621 := bbase (se 3 (by rfl) ⟨448241, by rfl⟩ : syracuseStep 2390621 = 896483) (by norm_num)
theorem B3586661 : Blo 1592995 3586661 := bbase (se 4 (by rfl) ⟨336249, by rfl⟩ : syracuseStep 3586661 = 672499) (by norm_num)
theorem B2390645 : Blo 1592995 2390645 := bbase (se 5 (by rfl) ⟨112061, by rfl⟩ : syracuseStep 2390645 = 224123) (by norm_num)
theorem B1940089 : Blo 1592995 1940089 := bbase (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) (by norm_num)
theorem B1792633 : Blo 1592995 1792633 := bbase (se 2 (by rfl) ⟨672237, by rfl⟩ : syracuseStep 1792633 = 1344475) (by norm_num)
theorem B2390669 : Blo 1592995 2390669 := bbase (se 3 (by rfl) ⟨448250, by rfl⟩ : syracuseStep 2390669 = 896501) (by norm_num)
theorem B1915537 : Blo 1592995 1915537 := bbase (se 2 (by rfl) ⟨718326, by rfl⟩ : syracuseStep 1915537 = 1436653) (by norm_num)
theorem B1792669 : Blo 1592995 1792669 := bbase (se 3 (by rfl) ⟨336125, by rfl⟩ : syracuseStep 1792669 = 672251) (by norm_num)
theorem B2390693 : Blo 1592995 2390693 := bbase (se 4 (by rfl) ⟨224127, by rfl⟩ : syracuseStep 2390693 = 448255) (by norm_num)
theorem B3586733 : Blo 1592995 3586733 := bbase (se 3 (by rfl) ⟨672512, by rfl⟩ : syracuseStep 3586733 = 1345025) (by norm_num)
theorem B2390717 : Blo 1592995 2390717 := bbase (se 3 (by rfl) ⟨448259, by rfl⟩ : syracuseStep 2390717 = 896519) (by norm_num)
theorem B1792705 : Blo 1592995 1792705 := bbase (se 2 (by rfl) ⟨672264, by rfl⟩ : syracuseStep 1792705 = 1344529) (by norm_num)
theorem B2390741 : Blo 1592995 2390741 := bbase (se 7 (by rfl) ⟨28016, by rfl⟩ : syracuseStep 2390741 = 56033) (by norm_num)
theorem B1792741 : Blo 1592995 1792741 := bbase (se 4 (by rfl) ⟨168069, by rfl⟩ : syracuseStep 1792741 = 336139) (by norm_num)
theorem B2390765 : Blo 1592995 2390765 := bbase (se 3 (by rfl) ⟨448268, by rfl⟩ : syracuseStep 2390765 = 896537) (by norm_num)
theorem B1915633 : Blo 1592995 1915633 := bbase (se 2 (by rfl) ⟨718362, by rfl⟩ : syracuseStep 1915633 = 1436725) (by norm_num)
theorem B3586805 : Blo 1592995 3586805 := bbase (se 5 (by rfl) ⟨168131, by rfl⟩ : syracuseStep 3586805 = 336263) (by norm_num)
theorem B1702657 : Blo 1592995 1702657 := bbase (se 2 (by rfl) ⟨638496, by rfl⟩ : syracuseStep 1702657 = 1276993) (by norm_num)
theorem B2390789 : Blo 1592995 2390789 := bbase (se 4 (by rfl) ⟨224136, by rfl⟩ : syracuseStep 2390789 = 448273) (by norm_num)
theorem B1792777 : Blo 1592995 1792777 := bbase (se 2 (by rfl) ⟨672291, by rfl⟩ : syracuseStep 1792777 = 1344583) (by norm_num)
theorem B3635981 : Blo 1592995 3635981 := bbase (se 3 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 3635981 = 1363493) (by norm_num)
theorem B2390813 : Blo 1592995 2390813 := bbase (se 3 (by rfl) ⟨448277, by rfl⟩ : syracuseStep 2390813 = 896555) (by norm_num)
theorem B1792813 : Blo 1592995 1792813 := bbase (se 3 (by rfl) ⟨336152, by rfl⟩ : syracuseStep 1792813 = 672305) (by norm_num)
theorem B2390837 : Blo 1592995 2390837 := bbase (se 5 (by rfl) ⟨112070, by rfl⟩ : syracuseStep 2390837 = 224141) (by norm_num)
theorem B3586877 : Blo 1592995 3586877 := bbase (se 3 (by rfl) ⟨672539, by rfl⟩ : syracuseStep 3586877 = 1345079) (by norm_num)
theorem B2390861 : Blo 1592995 2390861 := bbase (se 3 (by rfl) ⟨448286, by rfl⟩ : syracuseStep 2390861 = 896573) (by norm_num)
theorem B1792849 : Blo 1592995 1792849 := bbase (se 2 (by rfl) ⟨672318, by rfl⟩ : syracuseStep 1792849 = 1344637) (by norm_num)
theorem B2390885 : Blo 1592995 2390885 := bbase (se 4 (by rfl) ⟨224145, by rfl⟩ : syracuseStep 2390885 = 448291) (by norm_num)
theorem B4537205 : Blo 1592995 4537205 := bbase (se 5 (by rfl) ⟨212681, by rfl⟩ : syracuseStep 4537205 = 425363) (by norm_num)
theorem B6806389 : Blo 1592995 6806389 := bbase (se 5 (by rfl) ⟨319049, by rfl⟩ : syracuseStep 6806389 = 638099) (by norm_num)
theorem B1792885 : Blo 1592995 1792885 := bbase (se 5 (by rfl) ⟨84041, by rfl⟩ : syracuseStep 1792885 = 168083) (by norm_num)
theorem B5176181 : Blo 1592995 5176181 := bbase (se 5 (by rfl) ⟨242633, by rfl⟩ : syracuseStep 5176181 = 485267) (by norm_num)
theorem B2554741 : Blo 1592995 2554741 := bbase (se 5 (by rfl) ⟨119753, by rfl⟩ : syracuseStep 2554741 = 239507) (by norm_num)
theorem B2390909 : Blo 1592995 2390909 := bbase (se 3 (by rfl) ⟨448295, by rfl⟩ : syracuseStep 2390909 = 896591) (by norm_num)
theorem B3586949 : Blo 1592995 3586949 := bbase (se 4 (by rfl) ⟨336276, by rfl⟩ : syracuseStep 3586949 = 672553) (by norm_num)
theorem B2390933 : Blo 1592995 2390933 := bbase (se 6 (by rfl) ⟨56037, by rfl⟩ : syracuseStep 2390933 = 112075) (by norm_num)
theorem B1792921 : Blo 1592995 1792921 := bbase (se 2 (by rfl) ⟨672345, by rfl⟩ : syracuseStep 1792921 = 1344691) (by norm_num)
theorem B2390957 : Blo 1592995 2390957 := bbase (se 3 (by rfl) ⟨448304, by rfl⟩ : syracuseStep 2390957 = 896609) (by norm_num)
theorem B5381045 : Blo 1592995 5381045 := bbase (se 5 (by rfl) ⟨252236, by rfl⟩ : syracuseStep 5381045 = 504473) (by norm_num)
theorem B1792957 : Blo 1592995 1792957 := bbase (se 3 (by rfl) ⟨336179, by rfl⟩ : syracuseStep 1792957 = 672359) (by norm_num)
theorem B2390981 : Blo 1592995 2390981 := bbase (se 4 (by rfl) ⟨224154, by rfl⟩ : syracuseStep 2390981 = 448309) (by norm_num)
theorem B3587021 : Blo 1592995 3587021 := bbase (se 3 (by rfl) ⟨672566, by rfl⟩ : syracuseStep 3587021 = 1345133) (by norm_num)
theorem B2391005 : Blo 1592995 2391005 := bbase (se 3 (by rfl) ⟨448313, by rfl⟩ : syracuseStep 2391005 = 896627) (by norm_num)
theorem B1792993 : Blo 1592995 1792993 := bbase (se 2 (by rfl) ⟨672372, by rfl⟩ : syracuseStep 1792993 = 1344745) (by norm_num)
theorem B8068085 : Blo 1592995 8068085 := bbase (se 5 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 8068085 = 756383) (by norm_num)
theorem B2391029 : Blo 1592995 2391029 := bbase (se 5 (by rfl) ⟨112079, by rfl⟩ : syracuseStep 2391029 = 224159) (by norm_num)
theorem B1793029 : Blo 1592995 1793029 := bbase (se 4 (by rfl) ⟨168096, by rfl⟩ : syracuseStep 1793029 = 336193) (by norm_num)
theorem B2391053 : Blo 1592995 2391053 := bbase (se 3 (by rfl) ⟨448322, by rfl⟩ : syracuseStep 2391053 = 896645) (by norm_num)
theorem B3587093 : Blo 1592995 3587093 := bbase (se 6 (by rfl) ⟨84072, by rfl⟩ : syracuseStep 3587093 = 168145) (by norm_num)
theorem B2391077 : Blo 1592995 2391077 := bbase (se 4 (by rfl) ⟨224163, by rfl⟩ : syracuseStep 2391077 = 448327) (by norm_num)
theorem B1793065 : Blo 1592995 1793065 := bbase (se 2 (by rfl) ⟨672399, by rfl⟩ : syracuseStep 1793065 = 1344799) (by norm_num)
theorem B2391101 : Blo 1592995 2391101 := bbase (se 3 (by rfl) ⟨448331, by rfl⟩ : syracuseStep 2391101 = 896663) (by norm_num)
theorem B1793101 : Blo 1592995 1793101 := bbase (se 3 (by rfl) ⟨336206, by rfl⟩ : syracuseStep 1793101 = 672413) (by norm_num)
theorem B2391125 : Blo 1592995 2391125 := bbase (se 8 (by rfl) ⟨14010, by rfl⟩ : syracuseStep 2391125 = 28021) (by norm_num)
theorem B3587165 : Blo 1592995 3587165 := bbase (se 3 (by rfl) ⟨672593, by rfl⟩ : syracuseStep 3587165 = 1345187) (by norm_num)
theorem B2391149 : Blo 1592995 2391149 := bbase (se 3 (by rfl) ⟨448340, by rfl⟩ : syracuseStep 2391149 = 896681) (by norm_num)
theorem B1793137 : Blo 1592995 1793137 := bbase (se 2 (by rfl) ⟨672426, by rfl⟩ : syracuseStep 1793137 = 1344853) (by norm_num)
theorem B1916017 : Blo 1592995 1916017 := bbase (se 2 (by rfl) ⟨718506, by rfl⟩ : syracuseStep 1916017 = 1437013) (by norm_num)
theorem B14548085 : Blo 1592995 14548085 := bbase (se 5 (by rfl) ⟨681941, by rfl⟩ : syracuseStep 14548085 = 1363883) (by norm_num)
theorem B2391173 : Blo 1592995 2391173 := bbase (se 4 (by rfl) ⟨224172, by rfl⟩ : syracuseStep 2391173 = 448345) (by norm_num)
theorem B1793173 : Blo 1592995 1793173 := bbase (se 6 (by rfl) ⟨42027, by rfl⟩ : syracuseStep 1793173 = 84055) (by norm_num)
theorem B2391197 : Blo 1592995 2391197 := bbase (se 3 (by rfl) ⟨448349, by rfl⟩ : syracuseStep 2391197 = 896699) (by norm_num)
theorem B3587237 : Blo 1592995 3587237 := bbase (se 4 (by rfl) ⟨336303, by rfl⟩ : syracuseStep 3587237 = 672607) (by norm_num)
theorem B11484341 : Blo 1592995 11484341 := bbase (se 5 (by rfl) ⟨538328, by rfl⟩ : syracuseStep 11484341 = 1076657) (by norm_num)
theorem B2391221 : Blo 1592995 2391221 := bbase (se 5 (by rfl) ⟨112088, by rfl⟩ : syracuseStep 2391221 = 224177) (by norm_num)
theorem B1793209 : Blo 1592995 1793209 := bbase (se 2 (by rfl) ⟨672453, by rfl⟩ : syracuseStep 1793209 = 1344907) (by norm_num)
theorem B1703101 : Blo 1592995 1703101 := bbase (se 3 (by rfl) ⟨319331, by rfl⟩ : syracuseStep 1703101 = 638663) (by norm_num)
theorem B2391245 : Blo 1592995 2391245 := bbase (se 3 (by rfl) ⟨448358, by rfl⟩ : syracuseStep 2391245 = 896717) (by norm_num)
theorem B1793245 : Blo 1592995 1793245 := bbase (se 3 (by rfl) ⟨336233, by rfl⟩ : syracuseStep 1793245 = 672467) (by norm_num)
theorem B2391269 : Blo 1592995 2391269 := bbase (se 4 (by rfl) ⟨224181, by rfl⟩ : syracuseStep 2391269 = 448363) (by norm_num)
theorem B3587309 : Blo 1592995 3587309 := bbase (se 3 (by rfl) ⟨672620, by rfl⟩ : syracuseStep 3587309 = 1345241) (by norm_num)
theorem B2391293 : Blo 1592995 2391293 := bbase (se 3 (by rfl) ⟨448367, by rfl⟩ : syracuseStep 2391293 = 896735) (by norm_num)
theorem B1793281 : Blo 1592995 1793281 := bbase (se 2 (by rfl) ⟨672480, by rfl⟩ : syracuseStep 1793281 = 1344961) (by norm_num)
theorem B2391317 : Blo 1592995 2391317 := bbase (se 6 (by rfl) ⟨56046, by rfl⟩ : syracuseStep 2391317 = 112093) (by norm_num)
theorem B1793317 : Blo 1592995 1793317 := bbase (se 4 (by rfl) ⟨168123, by rfl⟩ : syracuseStep 1793317 = 336247) (by norm_num)
theorem B2391341 : Blo 1592995 2391341 := bbase (se 3 (by rfl) ⟨448376, by rfl⟩ : syracuseStep 2391341 = 896753) (by norm_num)
theorem B3587381 : Blo 1592995 3587381 := bbase (se 5 (by rfl) ⟨168158, by rfl⟩ : syracuseStep 3587381 = 336317) (by norm_num)
theorem B1703225 : Blo 1592995 1703225 := bbase (se 2 (by rfl) ⟨638709, by rfl⟩ : syracuseStep 1703225 = 1277419) (by norm_num)
theorem B2391365 : Blo 1592995 2391365 := bbase (se 4 (by rfl) ⟨224190, by rfl⟩ : syracuseStep 2391365 = 448381) (by norm_num)
theorem B1793353 : Blo 1592995 1793353 := bbase (se 2 (by rfl) ⟨672507, by rfl⟩ : syracuseStep 1793353 = 1345015) (by norm_num)
theorem B2391389 : Blo 1592995 2391389 := bbase (se 3 (by rfl) ⟨448385, by rfl⟩ : syracuseStep 2391389 = 896771) (by norm_num)
theorem B5381477 : Blo 1592995 5381477 := bbase (se 4 (by rfl) ⟨504513, by rfl⟩ : syracuseStep 5381477 = 1009027) (by norm_num)
theorem B1793389 : Blo 1592995 1793389 := bbase (se 3 (by rfl) ⟨336260, by rfl⟩ : syracuseStep 1793389 = 672521) (by norm_num)
theorem B6053237 : Blo 1592995 6053237 := bbase (se 5 (by rfl) ⟨283745, by rfl⟩ : syracuseStep 6053237 = 567491) (by norm_num)
theorem B2391413 : Blo 1592995 2391413 := bbase (se 5 (by rfl) ⟨112097, by rfl⟩ : syracuseStep 2391413 = 224195) (by norm_num)
theorem B3587453 : Blo 1592995 3587453 := bbase (se 3 (by rfl) ⟨672647, by rfl⟩ : syracuseStep 3587453 = 1345295) (by norm_num)
theorem B2391437 : Blo 1592995 2391437 := bbase (se 3 (by rfl) ⟨448394, by rfl⟩ : syracuseStep 2391437 = 896789) (by norm_num)
theorem B1793425 : Blo 1592995 1793425 := bbase (se 2 (by rfl) ⟨672534, by rfl⟩ : syracuseStep 1793425 = 1345069) (by norm_num)
theorem B14548373 : Blo 1592995 14548373 := bbase (se 6 (by rfl) ⟨340977, by rfl⟩ : syracuseStep 14548373 = 681955) (by norm_num)
theorem B2391461 : Blo 1592995 2391461 := bbase (se 4 (by rfl) ⟨224199, by rfl⟩ : syracuseStep 2391461 = 448399) (by norm_num)
theorem B1793461 : Blo 1592995 1793461 := bbase (se 5 (by rfl) ⟨84068, by rfl⟩ : syracuseStep 1793461 = 168137) (by norm_num)
theorem B2391485 : Blo 1592995 2391485 := bbase (se 3 (by rfl) ⟨448403, by rfl⟩ : syracuseStep 2391485 = 896807) (by norm_num)
theorem B3587525 : Blo 1592995 3587525 := bbase (se 4 (by rfl) ⟨336330, by rfl⟩ : syracuseStep 3587525 = 672661) (by norm_num)
theorem B2391509 : Blo 1592995 2391509 := bbase (se 7 (by rfl) ⟨28025, by rfl⟩ : syracuseStep 2391509 = 56051) (by norm_num)
theorem B1793497 : Blo 1592995 1793497 := bbase (se 2 (by rfl) ⟨672561, by rfl⟩ : syracuseStep 1793497 = 1345123) (by norm_num)
theorem B2391533 : Blo 1592995 2391533 := bbase (se 3 (by rfl) ⟨448412, by rfl⟩ : syracuseStep 2391533 = 896825) (by norm_num)
theorem B4849141 : Blo 1592995 4849141 := bbase (se 5 (by rfl) ⟨227303, by rfl⟩ : syracuseStep 4849141 = 454607) (by norm_num)
theorem B1793533 : Blo 1592995 1793533 := bbase (se 3 (by rfl) ⟨336287, by rfl⟩ : syracuseStep 1793533 = 672575) (by norm_num)
theorem B2391557 : Blo 1592995 2391557 := bbase (se 4 (by rfl) ⟨224208, by rfl⟩ : syracuseStep 2391557 = 448417) (by norm_num)
theorem B3587597 : Blo 1592995 3587597 := bbase (se 3 (by rfl) ⟨672674, by rfl⟩ : syracuseStep 3587597 = 1345349) (by norm_num)
theorem B2391581 : Blo 1592995 2391581 := bbase (se 3 (by rfl) ⟨448421, by rfl⟩ : syracuseStep 2391581 = 896843) (by norm_num)
theorem B1793569 : Blo 1592995 1793569 := bbase (se 2 (by rfl) ⟨672588, by rfl⟩ : syracuseStep 1793569 = 1345177) (by norm_num)
theorem B2391605 : Blo 1592995 2391605 := bbase (se 5 (by rfl) ⟨112106, by rfl⟩ : syracuseStep 2391605 = 224213) (by norm_num)
theorem B1818173 : Blo 1592995 1818173 := bbase (se 3 (by rfl) ⟨340907, by rfl⟩ : syracuseStep 1818173 = 681815) (by norm_num)
theorem B1793605 : Blo 1592995 1793605 := bbase (se 4 (by rfl) ⟨168150, by rfl⟩ : syracuseStep 1793605 = 336301) (by norm_num)
theorem B2391629 : Blo 1592995 2391629 := bbase (se 3 (by rfl) ⟨448430, by rfl⟩ : syracuseStep 2391629 = 896861) (by norm_num)
theorem B3587669 : Blo 1592995 3587669 := bbase (se 8 (by rfl) ⟨21021, by rfl⟩ : syracuseStep 3587669 = 42043) (by norm_num)
theorem B4537957 : Blo 1592995 4537957 := bbase (se 4 (by rfl) ⟨425433, by rfl⟩ : syracuseStep 4537957 = 850867) (by norm_num)
theorem B2391653 : Blo 1592995 2391653 := bbase (se 4 (by rfl) ⟨224217, by rfl⟩ : syracuseStep 2391653 = 448435) (by norm_num)
theorem B1793641 : Blo 1592995 1793641 := bbase (se 2 (by rfl) ⟨672615, by rfl⟩ : syracuseStep 1793641 = 1345231) (by norm_num)
theorem B2391677 : Blo 1592995 2391677 := bbase (se 3 (by rfl) ⟨448439, by rfl⟩ : syracuseStep 2391677 = 896879) (by norm_num)
theorem B1793677 : Blo 1592995 1793677 := bbase (se 3 (by rfl) ⟨336314, by rfl⟩ : syracuseStep 1793677 = 672629) (by norm_num)
theorem B6053525 : Blo 1592995 6053525 := bbase (se 6 (by rfl) ⟨141879, by rfl⟩ : syracuseStep 6053525 = 283759) (by norm_num)
theorem B2391701 : Blo 1592995 2391701 := bbase (se 6 (by rfl) ⟨56055, by rfl⟩ : syracuseStep 2391701 = 112111) (by norm_num)
theorem B3587741 : Blo 1592995 3587741 := bbase (se 3 (by rfl) ⟨672701, by rfl⟩ : syracuseStep 3587741 = 1345403) (by norm_num)
theorem B2391725 : Blo 1592995 2391725 := bbase (se 3 (by rfl) ⟨448448, by rfl⟩ : syracuseStep 2391725 = 896897) (by norm_num)
theorem B1793713 : Blo 1592995 1793713 := bbase (se 2 (by rfl) ⟨672642, by rfl⟩ : syracuseStep 1793713 = 1345285) (by norm_num)
theorem B5529269 : Blo 1592995 5529269 := bbase (se 5 (by rfl) ⟨259184, by rfl⟩ : syracuseStep 5529269 = 518369) (by norm_num)
theorem B2391749 : Blo 1592995 2391749 := bbase (se 4 (by rfl) ⟨224226, by rfl⟩ : syracuseStep 2391749 = 448453) (by norm_num)
theorem B3546821 : Blo 1592995 3546821 := bbase (se 4 (by rfl) ⟨332514, by rfl⟩ : syracuseStep 3546821 = 665029) (by norm_num)
theorem B3882701 : Blo 1592995 3882701 := bbase (se 3 (by rfl) ⟨728006, by rfl⟩ : syracuseStep 3882701 = 1456013) (by norm_num)
theorem B1793749 : Blo 1592995 1793749 := bbase (se 7 (by rfl) ⟨21020, by rfl⟩ : syracuseStep 1793749 = 42041) (by norm_num)
theorem B2391773 : Blo 1592995 2391773 := bbase (se 3 (by rfl) ⟨448457, by rfl⟩ : syracuseStep 2391773 = 896915) (by norm_num)
theorem B3587813 : Blo 1592995 3587813 := bbase (se 4 (by rfl) ⟨336357, by rfl⟩ : syracuseStep 3587813 = 672715) (by norm_num)
theorem B2391797 : Blo 1592995 2391797 := bbase (se 5 (by rfl) ⟨112115, by rfl⟩ : syracuseStep 2391797 = 224231) (by norm_num)
theorem B9699061 : Blo 1592995 9699061 := bbase (se 5 (by rfl) ⟨454643, by rfl⟩ : syracuseStep 9699061 = 909287) (by norm_num)
theorem B1793785 : Blo 1592995 1793785 := bbase (se 2 (by rfl) ⟨672669, by rfl⟩ : syracuseStep 1793785 = 1345339) (by norm_num)
theorem B2391821 : Blo 1592995 2391821 := bbase (se 3 (by rfl) ⟨448466, by rfl⟩ : syracuseStep 2391821 = 896933) (by norm_num)
theorem B6463253 : Blo 1592995 6463253 := bbase (se 6 (by rfl) ⟨151482, by rfl⟩ : syracuseStep 6463253 = 302965) (by norm_num)
theorem B5381909 : Blo 1592995 5381909 := bbase (se 6 (by rfl) ⟨126138, by rfl⟩ : syracuseStep 5381909 = 252277) (by norm_num)
theorem B1793821 : Blo 1592995 1793821 := bbase (se 3 (by rfl) ⟨336341, by rfl⟩ : syracuseStep 1793821 = 672683) (by norm_num)
theorem B2391845 : Blo 1592995 2391845 := bbase (se 4 (by rfl) ⟨224235, by rfl⟩ : syracuseStep 2391845 = 448471) (by norm_num)
theorem B3587885 : Blo 1592995 3587885 := bbase (se 3 (by rfl) ⟨672728, by rfl⟩ : syracuseStep 3587885 = 1345457) (by norm_num)
theorem B2391869 : Blo 1592995 2391869 := bbase (se 3 (by rfl) ⟨448475, by rfl⟩ : syracuseStep 2391869 = 896951) (by norm_num)
theorem B1793857 : Blo 1592995 1793857 := bbase (se 2 (by rfl) ⟨672696, by rfl⟩ : syracuseStep 1793857 = 1345393) (by norm_num)
theorem B2391893 : Blo 1592995 2391893 := bbase (se 9 (by rfl) ⟨7007, by rfl⟩ : syracuseStep 2391893 = 14015) (by norm_num)
theorem B1793893 : Blo 1592995 1793893 := bbase (se 4 (by rfl) ⟨168177, by rfl⟩ : syracuseStep 1793893 = 336355) (by norm_num)
theorem B2391917 : Blo 1592995 2391917 := bbase (se 3 (by rfl) ⟨448484, by rfl⟩ : syracuseStep 2391917 = 896969) (by norm_num)
theorem B13614965 : Blo 1592995 13614965 := bbase (se 5 (by rfl) ⟨638201, by rfl⟩ : syracuseStep 13614965 = 1276403) (by norm_num)
theorem B3587957 : Blo 1592995 3587957 := bbase (se 5 (by rfl) ⟨168185, by rfl⟩ : syracuseStep 3587957 = 336371) (by norm_num)
theorem B2391941 : Blo 1592995 2391941 := bbase (se 4 (by rfl) ⟨224244, by rfl⟩ : syracuseStep 2391941 = 448489) (by norm_num)
theorem B1793929 : Blo 1592995 1793929 := bbase (se 2 (by rfl) ⟨672723, by rfl⟩ : syracuseStep 1793929 = 1345447) (by norm_num)
theorem B2391965 : Blo 1592995 2391965 := bbase (se 3 (by rfl) ⟨448493, by rfl⟩ : syracuseStep 2391965 = 896987) (by norm_num)
theorem B1793965 : Blo 1592995 1793965 := bbase (se 3 (by rfl) ⟨336368, by rfl⟩ : syracuseStep 1793965 = 672737) (by norm_num)
theorem B2391989 : Blo 1592995 2391989 := bbase (se 5 (by rfl) ⟨112124, by rfl⟩ : syracuseStep 2391989 = 224249) (by norm_num)
theorem B3588029 : Blo 1592995 3588029 := bbase (se 3 (by rfl) ⟨672755, by rfl⟩ : syracuseStep 3588029 = 1345511) (by norm_num)
theorem B2392013 : Blo 1592995 2392013 := bbase (se 3 (by rfl) ⟨448502, by rfl⟩ : syracuseStep 2392013 = 897005) (by norm_num)
theorem B1794001 : Blo 1592995 1794001 := bbase (se 2 (by rfl) ⟨672750, by rfl⟩ : syracuseStep 1794001 = 1345501) (by norm_num)
theorem B2392037 : Blo 1592995 2392037 := bbase (se 4 (by rfl) ⟨224253, by rfl⟩ : syracuseStep 2392037 = 448507) (by norm_num)
theorem B1794037 : Blo 1592995 1794037 := bbase (se 5 (by rfl) ⟨84095, by rfl⟩ : syracuseStep 1794037 = 168191) (by norm_num)
theorem B2392061 : Blo 1592995 2392061 := bbase (se 3 (by rfl) ⟨448511, by rfl⟩ : syracuseStep 2392061 = 897023) (by norm_num)
theorem B4087811 : Blo 1592995 4087811 := bstep (se 1 (by rfl) ⟨3065858, by rfl⟩ : syracuseStep 4087811 = 6131717) B6131717
theorem B2392067 : Blo 1592995 2392067 := bstep (se 1 (by rfl) ⟨1794050, by rfl⟩ : syracuseStep 2392067 = 3588101) B3588101
theorem B2392097 : Blo 1592995 2392097 := bstep (se 2 (by rfl) ⟨897036, by rfl⟩ : syracuseStep 2392097 = 1794073) B1794073
theorem B5382179 : Blo 1592995 5382179 := bstep (se 1 (by rfl) ⟨4036634, by rfl⟩ : syracuseStep 5382179 = 8073269) B8073269
theorem B2269235 : Blo 1592995 2269235 := bstep (se 1 (by rfl) ⟨1701926, by rfl⟩ : syracuseStep 2269235 = 3403853) B3403853
theorem B2392115 : Blo 1592995 2392115 := bstep (se 1 (by rfl) ⟨1794086, by rfl⟩ : syracuseStep 2392115 = 3588173) B3588173
theorem B2392145 : Blo 1592995 2392145 := bstep (se 2 (by rfl) ⟨897054, by rfl⟩ : syracuseStep 2392145 = 1794109) B1794109
theorem B8069219 : Blo 1592995 8069219 := bstep (se 1 (by rfl) ⟨6051914, by rfl⟩ : syracuseStep 8069219 = 12103829) B12103829
theorem B2392163 : Blo 1592995 2392163 := bstep (se 1 (by rfl) ⟨1794122, by rfl⟩ : syracuseStep 2392163 = 3588245) B3588245
theorem B3588209 : Blo 1592995 3588209 := bstep (se 2 (by rfl) ⟨1345578, by rfl⟩ : syracuseStep 3588209 = 2691157) B2691157
theorem B1794163 : Blo 1592995 1794163 := bstep (se 1 (by rfl) ⟨1345622, by rfl⟩ : syracuseStep 1794163 = 2691245) B2691245
theorem B2392193 : Blo 1592995 2392193 := bstep (se 2 (by rfl) ⟨897072, by rfl⟩ : syracuseStep 2392193 = 1794145) B1794145
theorem B3588227 : Blo 1592995 3588227 := bstep (se 1 (by rfl) ⟨2691170, by rfl⟩ : syracuseStep 3588227 = 5382341) B5382341
theorem B2392211 : Blo 1592995 2392211 := bstep (se 1 (by rfl) ⟨1794158, by rfl⟩ : syracuseStep 2392211 = 3588317) B3588317
theorem B2392241 : Blo 1592995 2392241 := bstep (se 2 (by rfl) ⟨897090, by rfl⟩ : syracuseStep 2392241 = 1794181) B1794181
theorem B2728129 : Blo 1592995 2728129 := bstep (se 2 (by rfl) ⟨1023048, by rfl⟩ : syracuseStep 2728129 = 2046097) B2046097
theorem B2392259 : Blo 1592995 2392259 := bstep (se 1 (by rfl) ⟨1794194, by rfl⟩ : syracuseStep 2392259 = 3588389) B3588389
theorem B2392289 : Blo 1592995 2392289 := bstep (se 2 (by rfl) ⟨897108, by rfl⟩ : syracuseStep 2392289 = 1794217) B1794217
theorem B2728163 : Blo 1592995 2728163 := bstep (se 1 (by rfl) ⟨2046122, by rfl⟩ : syracuseStep 2728163 = 4092245) B4092245
theorem B2392307 : Blo 1592995 2392307 := bstep (se 1 (by rfl) ⟨1794230, by rfl⟩ : syracuseStep 2392307 = 3588461) B3588461
theorem B1794307 : Blo 1592995 1794307 := bstep (se 1 (by rfl) ⟨1345730, by rfl⟩ : syracuseStep 1794307 = 2691461) B2691461
theorem B2392337 : Blo 1592995 2392337 := bstep (se 2 (by rfl) ⟨897126, by rfl⟩ : syracuseStep 2392337 = 1794253) B1794253
theorem B2392355 : Blo 1592995 2392355 := bstep (se 1 (by rfl) ⟨1794266, by rfl⟩ : syracuseStep 2392355 = 3588533) B3588533
theorem B5382449 : Blo 1592995 5382449 := bstep (se 2 (by rfl) ⟨2018418, by rfl⟩ : syracuseStep 5382449 = 4036837) B4036837
theorem B2392385 : Blo 1592995 2392385 := bstep (se 2 (by rfl) ⟨897144, by rfl⟩ : syracuseStep 2392385 = 1794289) B1794289
theorem B1941827 : Blo 1592995 1941827 := bstep (se 1 (by rfl) ⟨1456370, by rfl⟩ : syracuseStep 1941827 = 2912741) B2912741
theorem B9691469 : Blo 1592995 9691469 := bstep (se 3 (by rfl) ⟨1817150, by rfl⟩ : syracuseStep 9691469 = 3634301) B3634301
theorem B2392403 : Blo 1592995 2392403 := bstep (se 1 (by rfl) ⟨1794302, by rfl⟩ : syracuseStep 2392403 = 3588605) B3588605
theorem B2392433 : Blo 1592995 2392433 := bstep (se 2 (by rfl) ⟨897162, by rfl⟩ : syracuseStep 2392433 = 1794325) B1794325
theorem B2392451 : Blo 1592995 2392451 := bstep (se 1 (by rfl) ⟨1794338, by rfl⟩ : syracuseStep 2392451 = 3588677) B3588677
theorem B7659917 : Blo 1592995 7659917 := bstep (se 3 (by rfl) ⟨1436234, by rfl⟩ : syracuseStep 7659917 = 2872469) B2872469
theorem B3588497 : Blo 1592995 3588497 := bstep (se 2 (by rfl) ⟨1345686, by rfl⟩ : syracuseStep 3588497 = 2691373) B2691373
theorem B2392481 : Blo 1592995 2392481 := bstep (se 2 (by rfl) ⟨897180, by rfl⟩ : syracuseStep 2392481 = 1794361) B1794361
theorem B3588515 : Blo 1592995 3588515 := bstep (se 1 (by rfl) ⟨2691386, by rfl⟩ : syracuseStep 3588515 = 5382773) B5382773
theorem B2802131 : Blo 1592995 2802131 := bstep (se 1 (by rfl) ⟨2101598, by rfl⟩ : syracuseStep 2802131 = 4203197) B4203197
theorem B13615715 : Blo 1592995 13615715 := bstep (se 1 (by rfl) ⟨10211786, by rfl⟩ : syracuseStep 13615715 = 20423573) B20423573
theorem B2269873 : Blo 1592995 2269873 := bstep (se 2 (by rfl) ⟨851202, by rfl⟩ : syracuseStep 2269873 = 1702405) B1702405
theorem B5382989 : Blo 1592995 5382989 := bstep (se 3 (by rfl) ⟨1009310, by rfl⟩ : syracuseStep 5382989 = 2018621) B2018621
theorem B5383043 : Blo 1592995 5383043 := bstep (se 1 (by rfl) ⟨4037282, by rfl⟩ : syracuseStep 5383043 = 8074565) B8074565
theorem B8070029 : Blo 1592995 8070029 := bstep (se 3 (by rfl) ⟨1513130, by rfl⟩ : syracuseStep 8070029 = 3026261) B3026261
theorem B5104561 : Blo 1592995 5104561 := bstep (se 2 (by rfl) ⟨1914210, by rfl⟩ : syracuseStep 5104561 = 3828421) B3828421
theorem B4309937 : Blo 1592995 4309937 := bstep (se 2 (by rfl) ⟨1616226, by rfl⟩ : syracuseStep 4309937 = 3232453) B3232453
theorem B2270209 : Blo 1592995 2270209 := bstep (se 2 (by rfl) ⟨851328, by rfl⟩ : syracuseStep 2270209 = 1702657) B1702657
theorem B4539473 : Blo 1592995 4539473 := bstep (se 2 (by rfl) ⟨1702302, by rfl⟩ : syracuseStep 4539473 = 3404605) B3404605
theorem B2688241 : Blo 1592995 2688241 := bstep (se 2 (by rfl) ⟨1008090, by rfl⟩ : syracuseStep 2688241 = 2016181) B2016181
theorem B2016515 : Blo 1592995 2016515 := bstep (se 1 (by rfl) ⟨1512386, by rfl⟩ : syracuseStep 2016515 = 3024773) B3024773
theorem B13993229 : Blo 1592995 13993229 := bstep (se 3 (by rfl) ⟨2623730, by rfl⟩ : syracuseStep 13993229 = 5247461) B5247461
theorem B6055181 : Blo 1592995 6055181 := bstep (se 3 (by rfl) ⟨1135346, by rfl⟩ : syracuseStep 6055181 = 2270693) B2270693
theorem B4539665 : Blo 1592995 4539665 := bstep (se 2 (by rfl) ⟨1702374, by rfl⟩ : syracuseStep 4539665 = 3404749) B3404749
theorem B2688275 : Blo 1592995 2688275 := bstep (se 1 (by rfl) ⟨2016206, by rfl⟩ : syracuseStep 2688275 = 4032413) B4032413
theorem B3933521 : Blo 1592995 3933521 := bstep (se 2 (by rfl) ⟨1475070, by rfl⟩ : syracuseStep 3933521 = 2950141) B2950141
theorem B8848739 : Blo 1592995 8848739 := bstep (se 1 (by rfl) ⟨6636554, by rfl⟩ : syracuseStep 8848739 = 13273109) B13273109
theorem B2688403 : Blo 1592995 2688403 := bstep (se 1 (by rfl) ⟨2016302, by rfl⟩ : syracuseStep 2688403 = 4032605) B4032605
theorem B2688545 : Blo 1592995 2688545 := bstep (se 2 (by rfl) ⟨1008204, by rfl⟩ : syracuseStep 2688545 = 2016409) B2016409
theorem B6809123 : Blo 1592995 6809123 := bstep (se 1 (by rfl) ⟨5106842, by rfl⟩ : syracuseStep 6809123 = 10213685) B10213685
theorem B2270801 : Blo 1592995 2270801 := bstep (se 2 (by rfl) ⟨851550, by rfl⟩ : syracuseStep 2270801 = 1703101) B1703101
theorem B3024515 : Blo 1592995 3024515 := bstep (se 1 (by rfl) ⟨2268386, by rfl⟩ : syracuseStep 3024515 = 4536773) B4536773
theorem B2688673 : Blo 1592995 2688673 := bstep (se 2 (by rfl) ⟨1008252, by rfl⟩ : syracuseStep 2688673 = 2016505) B2016505
theorem B2688707 : Blo 1592995 2688707 := bstep (se 1 (by rfl) ⟨2016530, by rfl⟩ : syracuseStep 2688707 = 4033061) B4033061
theorem B2688835 : Blo 1592995 2688835 := bstep (se 1 (by rfl) ⟨2016626, by rfl⟩ : syracuseStep 2688835 = 4033253) B4033253
theorem B3024803 : Blo 1592995 3024803 := bstep (se 1 (by rfl) ⟨2268602, by rfl⟩ : syracuseStep 3024803 = 4537205) B4537205
theorem B2017219 : Blo 1592995 2017219 := bstep (se 1 (by rfl) ⟨1512914, by rfl⟩ : syracuseStep 2017219 = 3025829) B3025829
theorem B2688977 : Blo 1592995 2688977 := bstep (se 2 (by rfl) ⟨1008366, by rfl⟩ : syracuseStep 2688977 = 2016733) B2016733
theorem B6465521 : Blo 1592995 6465521 := bstep (se 2 (by rfl) ⟨2424570, by rfl⟩ : syracuseStep 6465521 = 4849141) B4849141
theorem B2017315 : Blo 1592995 2017315 := bstep (se 1 (by rfl) ⟨1512986, by rfl⟩ : syracuseStep 2017315 = 3025973) B3025973
theorem B6055985 : Blo 1592995 6055985 := bstep (se 2 (by rfl) ⟨2270994, by rfl⟩ : syracuseStep 6055985 = 4541989) B4541989
theorem B2689105 : Blo 1592995 2689105 := bstep (se 2 (by rfl) ⟨1008414, by rfl⟩ : syracuseStep 2689105 = 2016829) B2016829
theorem B4032625 : Blo 1592995 4032625 := bstep (se 2 (by rfl) ⟨1512234, by rfl⟩ : syracuseStep 4032625 = 3024469) B3024469
theorem B2689139 : Blo 1592995 2689139 := bstep (se 1 (by rfl) ⟨2016854, by rfl⟩ : syracuseStep 2689139 = 4033709) B4033709
theorem B8612045 : Blo 1592995 8612045 := bstep (se 3 (by rfl) ⟨1614758, by rfl⟩ : syracuseStep 8612045 = 3229517) B3229517
theorem B75598051 : Blo 1592995 75598051 := bstep (se 1 (by rfl) ⟨56698538, by rfl⟩ : syracuseStep 75598051 = 113397077) B113397077
theorem B4540657 : Blo 1592995 4540657 := bstep (se 2 (by rfl) ⟨1702746, by rfl⟩ : syracuseStep 4540657 = 3405493) B3405493
theorem B2689267 : Blo 1592995 2689267 := bstep (se 1 (by rfl) ⟨2016950, by rfl⟩ : syracuseStep 2689267 = 4033901) B4033901
theorem B10209635 : Blo 1592995 10209635 := bstep (se 1 (by rfl) ⟨7657226, by rfl⟩ : syracuseStep 10209635 = 15314453) B15314453
theorem B2689409 : Blo 1592995 2689409 := bstep (se 2 (by rfl) ⟨1008528, by rfl⟩ : syracuseStep 2689409 = 2017057) B2017057
theorem B4032899 : Blo 1592995 4032899 := bstep (se 1 (by rfl) ⟨3024674, by rfl⟩ : syracuseStep 4032899 = 6049349) B6049349
theorem B18147725 : Blo 1592995 18147725 := bstep (se 3 (by rfl) ⟨3402698, by rfl⟩ : syracuseStep 18147725 = 6805397) B6805397
theorem B5376401 : Blo 1592995 5376401 := bstep (se 2 (by rfl) ⟨2016150, by rfl⟩ : syracuseStep 5376401 = 4032301) B4032301
theorem B2689537 : Blo 1592995 2689537 := bstep (se 2 (by rfl) ⟨1008576, by rfl⟩ : syracuseStep 2689537 = 2017153) B2017153
theorem B4540931 : Blo 1592995 4540931 := bstep (se 1 (by rfl) ⟨3405698, by rfl⟩ : syracuseStep 4540931 = 6811397) B6811397
theorem B2017811 : Blo 1592995 2017811 := bstep (se 1 (by rfl) ⟨1513358, by rfl⟩ : syracuseStep 2017811 = 3026717) B3026717
theorem B41388565 : Blo 1592995 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B2689571 : Blo 1592995 2689571 := bstep (se 1 (by rfl) ⟨2017178, by rfl⟩ : syracuseStep 2689571 = 4034357) B4034357
theorem B4033091 : Blo 1592995 4033091 := bstep (se 1 (by rfl) ⟨3024818, by rfl⟩ : syracuseStep 4033091 = 6049637) B6049637
theorem B5106253 : Blo 1592995 5106253 := bstep (se 3 (by rfl) ⟨957422, by rfl⟩ : syracuseStep 5106253 = 1914845) B1914845
theorem B2689699 : Blo 1592995 2689699 := bstep (se 1 (by rfl) ⟨2017274, by rfl⟩ : syracuseStep 2689699 = 4034549) B4034549
theorem B7269041 : Blo 1592995 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B4541123 : Blo 1592995 4541123 := bstep (se 1 (by rfl) ⟨3405842, by rfl⟩ : syracuseStep 4541123 = 6811685) B6811685
theorem B12102371 : Blo 1592995 12102371 := bstep (se 1 (by rfl) ⟨9076778, by rfl⟩ : syracuseStep 12102371 = 18153557) B18153557
theorem B2689841 : Blo 1592995 2689841 := bstep (se 2 (by rfl) ⟨1008690, by rfl⟩ : syracuseStep 2689841 = 2017381) B2017381
theorem B3025745 : Blo 1592995 3025745 := bstep (se 2 (by rfl) ⟨1134654, by rfl⟩ : syracuseStep 3025745 = 2269309) B2269309
theorem B5376941 : Blo 1592995 5376941 := bstep (se 3 (by rfl) ⟨1008176, by rfl⟩ : syracuseStep 5376941 = 2016353) B2016353
theorem B2689969 : Blo 1592995 2689969 := bstep (se 2 (by rfl) ⟨1008738, by rfl⟩ : syracuseStep 2689969 = 2017477) B2017477
theorem B2690003 : Blo 1592995 2690003 := bstep (se 1 (by rfl) ⟨2017502, by rfl⟩ : syracuseStep 2690003 = 4035005) B4035005
theorem B5376995 : Blo 1592995 5376995 := bstep (se 1 (by rfl) ⟨4032746, by rfl⟩ : syracuseStep 5376995 = 8065493) B8065493
theorem B4598765 : Blo 1592995 4598765 := bstep (se 3 (by rfl) ⟨862268, by rfl⟩ : syracuseStep 4598765 = 1724537) B1724537
theorem B9079877 : Blo 1592995 9079877 := bstep (se 4 (by rfl) ⟨851238, by rfl⟩ : syracuseStep 9079877 = 1702477) B1702477
theorem B2690131 : Blo 1592995 2690131 := bstep (se 1 (by rfl) ⟨2017598, by rfl⟩ : syracuseStep 2690131 = 4035197) B4035197
theorem B10488973 : Blo 1592995 10488973 := bstep (se 3 (by rfl) ⟨1966682, by rfl⟩ : syracuseStep 10488973 = 3933365) B3933365
theorem B2018515 : Blo 1592995 2018515 := bstep (se 1 (by rfl) ⟨1513886, by rfl⟩ : syracuseStep 2018515 = 3027773) B3027773
theorem B2690273 : Blo 1592995 2690273 := bstep (se 2 (by rfl) ⟨1008852, by rfl⟩ : syracuseStep 2690273 = 2017705) B2017705
theorem B5377265 : Blo 1592995 5377265 := bstep (se 2 (by rfl) ⟨2016474, by rfl⟩ : syracuseStep 5377265 = 4032949) B4032949
theorem B44231957 : Blo 1592995 44231957 := bstep (se 6 (by rfl) ⟨1036686, by rfl⟩ : syracuseStep 44231957 = 2073373) B2073373
theorem B3829027 : Blo 1592995 3829027 := bstep (se 1 (by rfl) ⟨2871770, by rfl⟩ : syracuseStep 3829027 = 5743541) B5743541
theorem B2911537 : Blo 1592995 2911537 := bstep (se 2 (by rfl) ⟨1091826, by rfl⟩ : syracuseStep 2911537 = 2183653) B2183653
theorem B2018611 : Blo 1592995 2018611 := bstep (se 1 (by rfl) ⟨1513958, by rfl⟩ : syracuseStep 2018611 = 3027917) B3027917
theorem B3403075 : Blo 1592995 3403075 := bstep (se 1 (by rfl) ⟨2552306, by rfl⟩ : syracuseStep 3403075 = 5104613) B5104613
theorem B2690401 : Blo 1592995 2690401 := bstep (se 2 (by rfl) ⟨1008900, by rfl⟩ : syracuseStep 2690401 = 2017801) B2017801
theorem B2690435 : Blo 1592995 2690435 := bstep (se 1 (by rfl) ⟨2017826, by rfl⟩ : syracuseStep 2690435 = 4035653) B4035653
theorem B3231139 : Blo 1592995 3231139 := bstep (se 1 (by rfl) ⟨2423354, by rfl⟩ : syracuseStep 3231139 = 4846709) B4846709
theorem B3231203 : Blo 1592995 3231203 := bstep (se 1 (by rfl) ⟨2423402, by rfl⟩ : syracuseStep 3231203 = 4846805) B4846805
theorem B4541933 : Blo 1592995 4541933 := bstep (se 3 (by rfl) ⟨851612, by rfl⟩ : syracuseStep 4541933 = 1703225) B1703225
theorem B4034033 : Blo 1592995 4034033 := bstep (se 2 (by rfl) ⟨1512762, by rfl⟩ : syracuseStep 4034033 = 3025525) B3025525
theorem B2690563 : Blo 1592995 2690563 := bstep (se 1 (by rfl) ⟨2017922, by rfl⟩ : syracuseStep 2690563 = 4035845) B4035845
theorem B9080333 : Blo 1592995 9080333 := bstep (se 3 (by rfl) ⟨1702562, by rfl⟩ : syracuseStep 9080333 = 3405125) B3405125
theorem B4034083 : Blo 1592995 4034083 := bstep (se 1 (by rfl) ⟨3025562, by rfl⟩ : syracuseStep 4034083 = 6051125) B6051125
theorem B2690705 : Blo 1592995 2690705 := bstep (se 2 (by rfl) ⟨1009014, by rfl⟩ : syracuseStep 2690705 = 2018029) B2018029
theorem B1592995 : Blo 1592995 1592995 := bstep (se 1 (by rfl) ⟨1194746, by rfl⟩ : syracuseStep 1592995 = 2389493) B2389493
theorem B8621731 : Blo 1592995 8621731 := bstep (se 1 (by rfl) ⟨6466298, by rfl⟩ : syracuseStep 8621731 = 12932597) B12932597
theorem B4034225 : Blo 1592995 4034225 := bstep (se 2 (by rfl) ⟨1512834, by rfl⟩ : syracuseStep 4034225 = 3025669) B3025669
theorem B1593011 : Blo 1592995 1593011 := bstep (se 1 (by rfl) ⟨1194758, by rfl⟩ : syracuseStep 1593011 = 2389517) B2389517
theorem B1593027 : Blo 1592995 1593027 := bstep (se 1 (by rfl) ⟨1194770, by rfl⟩ : syracuseStep 1593027 = 2389541) B2389541
theorem B10211021 : Blo 1592995 10211021 := bstep (se 3 (by rfl) ⟨1914566, by rfl⟩ : syracuseStep 10211021 = 3829133) B3829133
theorem B3026641 : Blo 1592995 3026641 := bstep (se 2 (by rfl) ⟨1134990, by rfl⟩ : syracuseStep 3026641 = 2269981) B2269981
theorem B1593043 : Blo 1592995 1593043 := bstep (se 1 (by rfl) ⟨1194782, by rfl⟩ : syracuseStep 1593043 = 2389565) B2389565
theorem B1593059 : Blo 1592995 1593059 := bstep (se 1 (by rfl) ⟨1194794, by rfl⟩ : syracuseStep 1593059 = 2389589) B2389589
theorem B8072945 : Blo 1592995 8072945 := bstep (se 2 (by rfl) ⟨3027354, by rfl⟩ : syracuseStep 8072945 = 6054709) B6054709
theorem B1593075 : Blo 1592995 1593075 := bstep (se 1 (by rfl) ⟨1194806, by rfl⟩ : syracuseStep 1593075 = 2389613) B2389613
theorem B1593091 : Blo 1592995 1593091 := bstep (se 1 (by rfl) ⟨1194818, by rfl⟩ : syracuseStep 1593091 = 2389637) B2389637
theorem B5377805 : Blo 1592995 5377805 := bstep (se 3 (by rfl) ⟨1008338, by rfl⟩ : syracuseStep 5377805 = 2016677) B2016677
theorem B2690833 : Blo 1592995 2690833 := bstep (se 2 (by rfl) ⟨1009062, by rfl⟩ : syracuseStep 2690833 = 2018125) B2018125
theorem B1593107 : Blo 1592995 1593107 := bstep (se 1 (by rfl) ⟨1194830, by rfl⟩ : syracuseStep 1593107 = 2389661) B2389661
theorem B1593123 : Blo 1592995 1593123 := bstep (se 1 (by rfl) ⟨1194842, by rfl⟩ : syracuseStep 1593123 = 2389685) B2389685
theorem B1593139 : Blo 1592995 1593139 := bstep (se 1 (by rfl) ⟨1194854, by rfl⟩ : syracuseStep 1593139 = 2389709) B2389709
theorem B2690867 : Blo 1592995 2690867 := bstep (se 1 (by rfl) ⟨2018150, by rfl⟩ : syracuseStep 2690867 = 4036301) B4036301
theorem B1593155 : Blo 1592995 1593155 := bstep (se 1 (by rfl) ⟨1194866, by rfl⟩ : syracuseStep 1593155 = 2389733) B2389733
theorem B5377859 : Blo 1592995 5377859 := bstep (se 1 (by rfl) ⟨4033394, by rfl⟩ : syracuseStep 5377859 = 8066789) B8066789
theorem B8064845 : Blo 1592995 8064845 := bstep (se 3 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 8064845 = 3024317) B3024317
theorem B1593171 : Blo 1592995 1593171 := bstep (se 1 (by rfl) ⟨1194878, by rfl⟩ : syracuseStep 1593171 = 2389757) B2389757
theorem B1593187 : Blo 1592995 1593187 := bstep (se 1 (by rfl) ⟨1194890, by rfl⟩ : syracuseStep 1593187 = 2389781) B2389781
theorem B3026801 : Blo 1592995 3026801 := bstep (se 2 (by rfl) ⟨1135050, by rfl⟩ : syracuseStep 3026801 = 2270101) B2270101
theorem B1593203 : Blo 1592995 1593203 := bstep (se 1 (by rfl) ⟨1194902, by rfl⟩ : syracuseStep 1593203 = 2389805) B2389805
theorem B1593219 : Blo 1592995 1593219 := bstep (se 1 (by rfl) ⟨1194914, by rfl⟩ : syracuseStep 1593219 = 2389829) B2389829
theorem B1593235 : Blo 1592995 1593235 := bstep (se 1 (by rfl) ⟨1194926, by rfl⟩ : syracuseStep 1593235 = 2389853) B2389853
theorem B1593251 : Blo 1592995 1593251 := bstep (se 1 (by rfl) ⟨1194938, by rfl⟩ : syracuseStep 1593251 = 2389877) B2389877
theorem B1593267 : Blo 1592995 1593267 := bstep (se 1 (by rfl) ⟨1194950, by rfl⟩ : syracuseStep 1593267 = 2389901) B2389901
theorem B2690995 : Blo 1592995 2690995 := bstep (se 1 (by rfl) ⟨2018246, by rfl⟩ : syracuseStep 2690995 = 4036493) B4036493
theorem B1593283 : Blo 1592995 1593283 := bstep (se 1 (by rfl) ⟨1194962, by rfl⟩ : syracuseStep 1593283 = 2389925) B2389925
theorem B1593299 : Blo 1592995 1593299 := bstep (se 1 (by rfl) ⟨1194974, by rfl⟩ : syracuseStep 1593299 = 2389949) B2389949
theorem B1593315 : Blo 1592995 1593315 := bstep (se 1 (by rfl) ⟨1194986, by rfl⟩ : syracuseStep 1593315 = 2389973) B2389973
theorem B1593331 : Blo 1592995 1593331 := bstep (se 1 (by rfl) ⟨1194998, by rfl⟩ : syracuseStep 1593331 = 2389997) B2389997
theorem B1593347 : Blo 1592995 1593347 := bstep (se 1 (by rfl) ⟨1195010, by rfl⟩ : syracuseStep 1593347 = 2390021) B2390021
theorem B10899461 : Blo 1592995 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B1593363 : Blo 1592995 1593363 := bstep (se 1 (by rfl) ⟨1195022, by rfl⟩ : syracuseStep 1593363 = 2390045) B2390045
theorem B1593379 : Blo 1592995 1593379 := bstep (se 1 (by rfl) ⟨1195034, by rfl⟩ : syracuseStep 1593379 = 2390069) B2390069
theorem B1593395 : Blo 1592995 1593395 := bstep (se 1 (by rfl) ⟨1195046, by rfl⟩ : syracuseStep 1593395 = 2390093) B2390093
theorem B58945589 : Blo 1592995 58945589 := bstep (se 5 (by rfl) ⟨2763074, by rfl⟩ : syracuseStep 58945589 = 5526149) B5526149
theorem B2691137 : Blo 1592995 2691137 := bstep (se 2 (by rfl) ⟨1009176, by rfl⟩ : syracuseStep 2691137 = 2018353) B2018353
theorem B1593411 : Blo 1592995 1593411 := bstep (se 1 (by rfl) ⟨1195058, by rfl⟩ : syracuseStep 1593411 = 2390117) B2390117
theorem B5378129 : Blo 1592995 5378129 := bstep (se 2 (by rfl) ⟨2016798, by rfl⟩ : syracuseStep 5378129 = 4033597) B4033597
theorem B1593427 : Blo 1592995 1593427 := bstep (se 1 (by rfl) ⟨1195070, by rfl⟩ : syracuseStep 1593427 = 2390141) B2390141
theorem B1593443 : Blo 1592995 1593443 := bstep (se 1 (by rfl) ⟨1195082, by rfl⟩ : syracuseStep 1593443 = 2390165) B2390165
theorem B1593459 : Blo 1592995 1593459 := bstep (se 1 (by rfl) ⟨1195094, by rfl⟩ : syracuseStep 1593459 = 2390189) B2390189
theorem B5173379 : Blo 1592995 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B1593475 : Blo 1592995 1593475 := bstep (se 1 (by rfl) ⟨1195106, by rfl⟩ : syracuseStep 1593475 = 2390213) B2390213
theorem B1593491 : Blo 1592995 1593491 := bstep (se 1 (by rfl) ⟨1195118, by rfl⟩ : syracuseStep 1593491 = 2390237) B2390237
theorem B1593507 : Blo 1592995 1593507 := bstep (se 1 (by rfl) ⟨1195130, by rfl⟩ : syracuseStep 1593507 = 2390261) B2390261
theorem B1593523 : Blo 1592995 1593523 := bstep (se 1 (by rfl) ⟨1195142, by rfl⟩ : syracuseStep 1593523 = 2390285) B2390285
theorem B2691265 : Blo 1592995 2691265 := bstep (se 2 (by rfl) ⟨1009224, by rfl⟩ : syracuseStep 2691265 = 2018449) B2018449
theorem B1593539 : Blo 1592995 1593539 := bstep (se 1 (by rfl) ⟨1195154, by rfl⟩ : syracuseStep 1593539 = 2390309) B2390309
theorem B1593555 : Blo 1592995 1593555 := bstep (se 1 (by rfl) ⟨1195166, by rfl⟩ : syracuseStep 1593555 = 2390333) B2390333
theorem B1593571 : Blo 1592995 1593571 := bstep (se 1 (by rfl) ⟨1195178, by rfl⟩ : syracuseStep 1593571 = 2390357) B2390357
theorem B2691299 : Blo 1592995 2691299 := bstep (se 1 (by rfl) ⟨2018474, by rfl⟩ : syracuseStep 2691299 = 4036949) B4036949
theorem B1593587 : Blo 1592995 1593587 := bstep (se 1 (by rfl) ⟨1195190, by rfl⟩ : syracuseStep 1593587 = 2390381) B2390381
theorem B1593603 : Blo 1592995 1593603 := bstep (se 1 (by rfl) ⟨1195202, by rfl⟩ : syracuseStep 1593603 = 2390405) B2390405
theorem B3027203 : Blo 1592995 3027203 := bstep (se 1 (by rfl) ⟨2270402, by rfl⟩ : syracuseStep 3027203 = 4540805) B4540805
theorem B1593619 : Blo 1592995 1593619 := bstep (se 1 (by rfl) ⟨1195214, by rfl⟩ : syracuseStep 1593619 = 2390429) B2390429
theorem B1593635 : Blo 1592995 1593635 := bstep (se 1 (by rfl) ⟨1195226, by rfl⟩ : syracuseStep 1593635 = 2390453) B2390453
theorem B1593651 : Blo 1592995 1593651 := bstep (se 1 (by rfl) ⟨1195238, by rfl⟩ : syracuseStep 1593651 = 2390477) B2390477
theorem B1593667 : Blo 1592995 1593667 := bstep (se 1 (by rfl) ⟨1195250, by rfl⟩ : syracuseStep 1593667 = 2390501) B2390501
theorem B5108035 : Blo 1592995 5108035 := bstep (se 1 (by rfl) ⟨3831026, by rfl⟩ : syracuseStep 5108035 = 7662053) B7662053
theorem B1593683 : Blo 1592995 1593683 := bstep (se 1 (by rfl) ⟨1195262, by rfl⟩ : syracuseStep 1593683 = 2390525) B2390525
theorem B1593699 : Blo 1592995 1593699 := bstep (se 1 (by rfl) ⟨1195274, by rfl⟩ : syracuseStep 1593699 = 2390549) B2390549
theorem B2691427 : Blo 1592995 2691427 := bstep (se 1 (by rfl) ⟨2018570, by rfl⟩ : syracuseStep 2691427 = 4037141) B4037141
theorem B11645297 : Blo 1592995 11645297 := bstep (se 2 (by rfl) ⟨4366986, by rfl⟩ : syracuseStep 11645297 = 8733973) B8733973
theorem B1593715 : Blo 1592995 1593715 := bstep (se 1 (by rfl) ⟨1195286, by rfl⟩ : syracuseStep 1593715 = 2390573) B2390573
theorem B1593731 : Blo 1592995 1593731 := bstep (se 1 (by rfl) ⟨1195298, by rfl⟩ : syracuseStep 1593731 = 2390597) B2390597
theorem B1593747 : Blo 1592995 1593747 := bstep (se 1 (by rfl) ⟨1195310, by rfl⟩ : syracuseStep 1593747 = 2390621) B2390621
theorem B1593763 : Blo 1592995 1593763 := bstep (se 1 (by rfl) ⟨1195322, by rfl⟩ : syracuseStep 1593763 = 2390645) B2390645
theorem B1593779 : Blo 1592995 1593779 := bstep (se 1 (by rfl) ⟨1195334, by rfl⟩ : syracuseStep 1593779 = 2390669) B2390669
theorem B1593795 : Blo 1592995 1593795 := bstep (se 1 (by rfl) ⟨1195346, by rfl⟩ : syracuseStep 1593795 = 2390693) B2390693
theorem B3584465 : Blo 1592995 3584465 := bstep (se 2 (by rfl) ⟨1344174, by rfl⟩ : syracuseStep 3584465 = 2688349) B2688349
theorem B1593811 : Blo 1592995 1593811 := bstep (se 1 (by rfl) ⟨1195358, by rfl⟩ : syracuseStep 1593811 = 2390717) B2390717
theorem B3584483 : Blo 1592995 3584483 := bstep (se 1 (by rfl) ⟨2688362, by rfl⟩ : syracuseStep 3584483 = 5376725) B5376725
theorem B1593827 : Blo 1592995 1593827 := bstep (se 1 (by rfl) ⟨1195370, by rfl⟩ : syracuseStep 1593827 = 2390741) B2390741
theorem B3830257 : Blo 1592995 3830257 := bstep (se 2 (by rfl) ⟨1436346, by rfl⟩ : syracuseStep 3830257 = 2872693) B2872693
theorem B1593843 : Blo 1592995 1593843 := bstep (se 1 (by rfl) ⟨1195382, by rfl⟩ : syracuseStep 1593843 = 2390765) B2390765
theorem B1593859 : Blo 1592995 1593859 := bstep (se 1 (by rfl) ⟨1195394, by rfl⟩ : syracuseStep 1593859 = 2390789) B2390789
theorem B3404305 : Blo 1592995 3404305 := bstep (se 2 (by rfl) ⟨1276614, by rfl⟩ : syracuseStep 3404305 = 2553229) B2553229
theorem B1593875 : Blo 1592995 1593875 := bstep (se 1 (by rfl) ⟨1195406, by rfl⟩ : syracuseStep 1593875 = 2390813) B2390813
theorem B1593891 : Blo 1592995 1593891 := bstep (se 1 (by rfl) ⟨1195418, by rfl⟩ : syracuseStep 1593891 = 2390837) B2390837
theorem B1593907 : Blo 1592995 1593907 := bstep (se 1 (by rfl) ⟨1195430, by rfl⟩ : syracuseStep 1593907 = 2390861) B2390861
theorem B1593923 : Blo 1592995 1593923 := bstep (se 1 (by rfl) ⟨1195442, by rfl⟩ : syracuseStep 1593923 = 2390885) B2390885
theorem B1593939 : Blo 1592995 1593939 := bstep (se 1 (by rfl) ⟨1195454, by rfl⟩ : syracuseStep 1593939 = 2390909) B2390909
theorem B1593955 : Blo 1592995 1593955 := bstep (se 1 (by rfl) ⟨1195466, by rfl⟩ : syracuseStep 1593955 = 2390933) B2390933
theorem B5378669 : Blo 1592995 5378669 := bstep (se 3 (by rfl) ⟨1008500, by rfl⟩ : syracuseStep 5378669 = 2017001) B2017001
theorem B1593971 : Blo 1592995 1593971 := bstep (se 1 (by rfl) ⟨1195478, by rfl⟩ : syracuseStep 1593971 = 2390957) B2390957
theorem B1593987 : Blo 1592995 1593987 := bstep (se 1 (by rfl) ⟨1195490, by rfl⟩ : syracuseStep 1593987 = 2390981) B2390981
theorem B36803213 : Blo 1592995 36803213 := bstep (se 3 (by rfl) ⟨6900602, by rfl⟩ : syracuseStep 36803213 = 13801205) B13801205
theorem B4035217 : Blo 1592995 4035217 := bstep (se 2 (by rfl) ⟨1513206, by rfl⟩ : syracuseStep 4035217 = 3026413) B3026413
theorem B1594003 : Blo 1592995 1594003 := bstep (se 1 (by rfl) ⟨1195502, by rfl⟩ : syracuseStep 1594003 = 2391005) B2391005
theorem B5378723 : Blo 1592995 5378723 := bstep (se 1 (by rfl) ⟨4034042, by rfl⟩ : syracuseStep 5378723 = 8068085) B8068085
theorem B1594019 : Blo 1592995 1594019 := bstep (se 1 (by rfl) ⟨1195514, by rfl⟩ : syracuseStep 1594019 = 2391029) B2391029
theorem B1594035 : Blo 1592995 1594035 := bstep (se 1 (by rfl) ⟨1195526, by rfl⟩ : syracuseStep 1594035 = 2391053) B2391053
theorem B1594051 : Blo 1592995 1594051 := bstep (se 1 (by rfl) ⟨1195538, by rfl⟩ : syracuseStep 1594051 = 2391077) B2391077
theorem B1594067 : Blo 1592995 1594067 := bstep (se 1 (by rfl) ⟨1195550, by rfl⟩ : syracuseStep 1594067 = 2391101) B2391101
theorem B1594083 : Blo 1592995 1594083 := bstep (se 1 (by rfl) ⟨1195562, by rfl⟩ : syracuseStep 1594083 = 2391125) B2391125
theorem B3584753 : Blo 1592995 3584753 := bstep (se 2 (by rfl) ⟨1344282, by rfl⟩ : syracuseStep 3584753 = 2688565) B2688565
theorem B2552563 : Blo 1592995 2552563 := bstep (se 1 (by rfl) ⟨1914422, by rfl⟩ : syracuseStep 2552563 = 3828845) B3828845
theorem B1594099 : Blo 1592995 1594099 := bstep (se 1 (by rfl) ⟨1195574, by rfl⟩ : syracuseStep 1594099 = 2391149) B2391149
theorem B3584771 : Blo 1592995 3584771 := bstep (se 1 (by rfl) ⟨2688578, by rfl⟩ : syracuseStep 3584771 = 5377157) B5377157
theorem B1594115 : Blo 1592995 1594115 := bstep (se 1 (by rfl) ⟨1195586, by rfl⟩ : syracuseStep 1594115 = 2391173) B2391173
theorem B5108483 : Blo 1592995 5108483 := bstep (se 1 (by rfl) ⟨3831362, by rfl⟩ : syracuseStep 5108483 = 7662725) B7662725
theorem B1594131 : Blo 1592995 1594131 := bstep (se 1 (by rfl) ⟨1195598, by rfl⟩ : syracuseStep 1594131 = 2391197) B2391197
theorem B7656227 : Blo 1592995 7656227 := bstep (se 1 (by rfl) ⟨5742170, by rfl⟩ : syracuseStep 7656227 = 11484341) B11484341
theorem B1594147 : Blo 1592995 1594147 := bstep (se 1 (by rfl) ⟨1195610, by rfl⟩ : syracuseStep 1594147 = 2391221) B2391221
theorem B6050609 : Blo 1592995 6050609 := bstep (se 2 (by rfl) ⟨2268978, by rfl⟩ : syracuseStep 6050609 = 4537957) B4537957
theorem B1594163 : Blo 1592995 1594163 := bstep (se 1 (by rfl) ⟨1195622, by rfl⟩ : syracuseStep 1594163 = 2391245) B2391245
theorem B1594179 : Blo 1592995 1594179 := bstep (se 1 (by rfl) ⟨1195634, by rfl⟩ : syracuseStep 1594179 = 2391269) B2391269
theorem B1594195 : Blo 1592995 1594195 := bstep (se 1 (by rfl) ⟨1195646, by rfl⟩ : syracuseStep 1594195 = 2391293) B2391293
theorem B1594211 : Blo 1592995 1594211 := bstep (se 1 (by rfl) ⟨1195658, by rfl⟩ : syracuseStep 1594211 = 2391317) B2391317
theorem B1594227 : Blo 1592995 1594227 := bstep (se 1 (by rfl) ⟨1195670, by rfl⟩ : syracuseStep 1594227 = 2391341) B2391341
theorem B1594243 : Blo 1592995 1594243 := bstep (se 1 (by rfl) ⟨1195682, by rfl⟩ : syracuseStep 1594243 = 2391365) B2391365
theorem B1594259 : Blo 1592995 1594259 := bstep (se 1 (by rfl) ⟨1195694, by rfl⟩ : syracuseStep 1594259 = 2391389) B2391389
theorem B4035491 : Blo 1592995 4035491 := bstep (se 1 (by rfl) ⟨3026618, by rfl⟩ : syracuseStep 4035491 = 6053237) B6053237
theorem B1594275 : Blo 1592995 1594275 := bstep (se 1 (by rfl) ⟨1195706, by rfl⟩ : syracuseStep 1594275 = 2391413) B2391413
theorem B5378993 : Blo 1592995 5378993 := bstep (se 2 (by rfl) ⟨2017122, by rfl⟩ : syracuseStep 5378993 = 4034245) B4034245
theorem B1594291 : Blo 1592995 1594291 := bstep (se 1 (by rfl) ⟨1195718, by rfl⟩ : syracuseStep 1594291 = 2391437) B2391437
theorem B1594307 : Blo 1592995 1594307 := bstep (se 1 (by rfl) ⟨1195730, by rfl⟩ : syracuseStep 1594307 = 2391461) B2391461
theorem B1594323 : Blo 1592995 1594323 := bstep (se 1 (by rfl) ⟨1195742, by rfl⟩ : syracuseStep 1594323 = 2391485) B2391485
theorem B1594339 : Blo 1592995 1594339 := bstep (se 1 (by rfl) ⟨1195754, by rfl⟩ : syracuseStep 1594339 = 2391509) B2391509
theorem B12932081 : Blo 1592995 12932081 := bstep (se 2 (by rfl) ⟨4849530, by rfl⟩ : syracuseStep 12932081 = 9699061) B9699061
theorem B1594355 : Blo 1592995 1594355 := bstep (se 1 (by rfl) ⟨1195766, by rfl⟩ : syracuseStep 1594355 = 2391533) B2391533
theorem B1594371 : Blo 1592995 1594371 := bstep (se 1 (by rfl) ⟨1195778, by rfl⟩ : syracuseStep 1594371 = 2391557) B2391557
theorem B3585041 : Blo 1592995 3585041 := bstep (se 2 (by rfl) ⟨1344390, by rfl⟩ : syracuseStep 3585041 = 2688781) B2688781
theorem B1594387 : Blo 1592995 1594387 := bstep (se 1 (by rfl) ⟨1195790, by rfl⟩ : syracuseStep 1594387 = 2391581) B2391581
theorem B40875029 : Blo 1592995 40875029 := bstep (se 6 (by rfl) ⟨958008, by rfl⟩ : syracuseStep 40875029 = 1916017) B1916017
theorem B3585059 : Blo 1592995 3585059 := bstep (se 1 (by rfl) ⟨2688794, by rfl⟩ : syracuseStep 3585059 = 5377589) B5377589
theorem B2044963 : Blo 1592995 2044963 := bstep (se 1 (by rfl) ⟨1533722, by rfl⟩ : syracuseStep 2044963 = 3067445) B3067445
theorem B1594403 : Blo 1592995 1594403 := bstep (se 1 (by rfl) ⟨1195802, by rfl⟩ : syracuseStep 1594403 = 2391605) B2391605
theorem B1594419 : Blo 1592995 1594419 := bstep (se 1 (by rfl) ⟨1195814, by rfl⟩ : syracuseStep 1594419 = 2391629) B2391629
theorem B1594435 : Blo 1592995 1594435 := bstep (se 1 (by rfl) ⟨1195826, by rfl⟩ : syracuseStep 1594435 = 2391653) B2391653
theorem B1594451 : Blo 1592995 1594451 := bstep (se 1 (by rfl) ⟨1195838, by rfl⟩ : syracuseStep 1594451 = 2391677) B2391677
theorem B4035683 : Blo 1592995 4035683 := bstep (se 1 (by rfl) ⟨3026762, by rfl⟩ : syracuseStep 4035683 = 6053525) B6053525
theorem B1594467 : Blo 1592995 1594467 := bstep (se 1 (by rfl) ⟨1195850, by rfl⟩ : syracuseStep 1594467 = 2391701) B2391701
theorem B1594483 : Blo 1592995 1594483 := bstep (se 1 (by rfl) ⟨1195862, by rfl⟩ : syracuseStep 1594483 = 2391725) B2391725
theorem B1594499 : Blo 1592995 1594499 := bstep (se 1 (by rfl) ⟨1195874, by rfl⟩ : syracuseStep 1594499 = 2391749) B2391749
theorem B2364547 : Blo 1592995 2364547 := bstep (se 1 (by rfl) ⟨1773410, by rfl⟩ : syracuseStep 2364547 = 3546821) B3546821
theorem B3634321 : Blo 1592995 3634321 := bstep (se 2 (by rfl) ⟨1362870, by rfl⟩ : syracuseStep 3634321 = 2725741) B2725741
theorem B1594515 : Blo 1592995 1594515 := bstep (se 1 (by rfl) ⟨1195886, by rfl⟩ : syracuseStep 1594515 = 2391773) B2391773
theorem B1594531 : Blo 1592995 1594531 := bstep (se 1 (by rfl) ⟨1195898, by rfl⟩ : syracuseStep 1594531 = 2391797) B2391797
theorem B8074403 : Blo 1592995 8074403 := bstep (se 1 (by rfl) ⟨6055802, by rfl⟩ : syracuseStep 8074403 = 12111605) B12111605
theorem B1594547 : Blo 1592995 1594547 := bstep (se 1 (by rfl) ⟨1195910, by rfl⟩ : syracuseStep 1594547 = 2391821) B2391821
theorem B1594563 : Blo 1592995 1594563 := bstep (se 1 (by rfl) ⟨1195922, by rfl⟩ : syracuseStep 1594563 = 2391845) B2391845
theorem B1914067 : Blo 1592995 1914067 := bstep (se 1 (by rfl) ⟨1435550, by rfl⟩ : syracuseStep 1914067 = 2871101) B2871101
theorem B1594579 : Blo 1592995 1594579 := bstep (se 1 (by rfl) ⟨1195934, by rfl⟩ : syracuseStep 1594579 = 2391869) B2391869
theorem B1594595 : Blo 1592995 1594595 := bstep (se 1 (by rfl) ⟨1195946, by rfl⟩ : syracuseStep 1594595 = 2391893) B2391893
theorem B18150641 : Blo 1592995 18150641 := bstep (se 2 (by rfl) ⟨6806490, by rfl⟩ : syracuseStep 18150641 = 13612981) B13612981
theorem B1594611 : Blo 1592995 1594611 := bstep (se 1 (by rfl) ⟨1195958, by rfl⟩ : syracuseStep 1594611 = 2391917) B2391917
theorem B1594627 : Blo 1592995 1594627 := bstep (se 1 (by rfl) ⟨1195970, by rfl⟩ : syracuseStep 1594627 = 2391941) B2391941
theorem B6804749 : Blo 1592995 6804749 := bstep (se 3 (by rfl) ⟨1275890, by rfl⟩ : syracuseStep 6804749 = 2551781) B2551781
theorem B1594643 : Blo 1592995 1594643 := bstep (se 1 (by rfl) ⟨1195982, by rfl⟩ : syracuseStep 1594643 = 2391965) B2391965
theorem B3405091 : Blo 1592995 3405091 := bstep (se 1 (by rfl) ⟨2553818, by rfl⟩ : syracuseStep 3405091 = 5107637) B5107637
theorem B1594659 : Blo 1592995 1594659 := bstep (se 1 (by rfl) ⟨1195994, by rfl⟩ : syracuseStep 1594659 = 2391989) B2391989
theorem B3585329 : Blo 1592995 3585329 := bstep (se 2 (by rfl) ⟨1344498, by rfl⟩ : syracuseStep 3585329 = 2688997) B2688997
theorem B1594675 : Blo 1592995 1594675 := bstep (se 1 (by rfl) ⟨1196006, by rfl⟩ : syracuseStep 1594675 = 2392013) B2392013
theorem B3585347 : Blo 1592995 3585347 := bstep (se 1 (by rfl) ⟨2689010, by rfl⟩ : syracuseStep 3585347 = 5378021) B5378021
theorem B1594691 : Blo 1592995 1594691 := bstep (se 1 (by rfl) ⟨1196018, by rfl⟩ : syracuseStep 1594691 = 2392037) B2392037
theorem B1594707 : Blo 1592995 1594707 := bstep (se 1 (by rfl) ⟨1196030, by rfl⟩ : syracuseStep 1594707 = 2392061) B2392061
theorem B1594723 : Blo 1592995 1594723 := bstep (se 1 (by rfl) ⟨1196042, by rfl⟩ : syracuseStep 1594723 = 2392085) B2392085
theorem B1594739 : Blo 1592995 1594739 := bstep (se 1 (by rfl) ⟨1196054, by rfl⟩ : syracuseStep 1594739 = 2392109) B2392109
theorem B1594755 : Blo 1592995 1594755 := bstep (se 1 (by rfl) ⟨1196066, by rfl⟩ : syracuseStep 1594755 = 2392133) B2392133
theorem B1594771 : Blo 1592995 1594771 := bstep (se 1 (by rfl) ⟨1196078, by rfl⟩ : syracuseStep 1594771 = 2392157) B2392157
theorem B1594787 : Blo 1592995 1594787 := bstep (se 1 (by rfl) ⟨1196090, by rfl⟩ : syracuseStep 1594787 = 2392181) B2392181
theorem B1594803 : Blo 1592995 1594803 := bstep (se 1 (by rfl) ⟨1196102, by rfl⟩ : syracuseStep 1594803 = 2392205) B2392205
theorem B1594819 : Blo 1592995 1594819 := bstep (se 1 (by rfl) ⟨1196114, by rfl⟩ : syracuseStep 1594819 = 2392229) B2392229
theorem B5379533 : Blo 1592995 5379533 := bstep (se 3 (by rfl) ⟨1008662, by rfl⟩ : syracuseStep 5379533 = 2017325) B2017325
theorem B1594835 : Blo 1592995 1594835 := bstep (se 1 (by rfl) ⟨1196126, by rfl⟩ : syracuseStep 1594835 = 2392253) B2392253
theorem B15316451 : Blo 1592995 15316451 := bstep (se 1 (by rfl) ⟨11487338, by rfl⟩ : syracuseStep 15316451 = 22974677) B22974677
theorem B1594851 : Blo 1592995 1594851 := bstep (se 1 (by rfl) ⟨1196138, by rfl⟩ : syracuseStep 1594851 = 2392277) B2392277
theorem B1594867 : Blo 1592995 1594867 := bstep (se 1 (by rfl) ⟨1196150, by rfl⟩ : syracuseStep 1594867 = 2392301) B2392301
theorem B2389505 : Blo 1592995 2389505 := bstep (se 2 (by rfl) ⟨896064, by rfl⟩ : syracuseStep 2389505 = 1792129) B1792129
theorem B5379587 : Blo 1592995 5379587 := bstep (se 1 (by rfl) ⟨4034690, by rfl⟩ : syracuseStep 5379587 = 8069381) B8069381
theorem B5453315 : Blo 1592995 5453315 := bstep (se 1 (by rfl) ⟨4089986, by rfl⟩ : syracuseStep 5453315 = 8179973) B8179973
theorem B1594883 : Blo 1592995 1594883 := bstep (se 1 (by rfl) ⟨1196162, by rfl⟩ : syracuseStep 1594883 = 2392325) B2392325
theorem B2389523 : Blo 1592995 2389523 := bstep (se 1 (by rfl) ⟨1792142, by rfl⟩ : syracuseStep 2389523 = 3584285) B3584285
theorem B1594899 : Blo 1592995 1594899 := bstep (se 1 (by rfl) ⟨1196174, by rfl⟩ : syracuseStep 1594899 = 2392349) B2392349
theorem B1914403 : Blo 1592995 1914403 := bstep (se 1 (by rfl) ⟨1435802, by rfl⟩ : syracuseStep 1914403 = 2871605) B2871605
theorem B1594915 : Blo 1592995 1594915 := bstep (se 1 (by rfl) ⟨1196186, by rfl⟩ : syracuseStep 1594915 = 2392373) B2392373
theorem B2389553 : Blo 1592995 2389553 := bstep (se 2 (by rfl) ⟨896082, by rfl⟩ : syracuseStep 2389553 = 1792165) B1792165
theorem B1594931 : Blo 1592995 1594931 := bstep (se 1 (by rfl) ⟨1196198, by rfl⟩ : syracuseStep 1594931 = 2392397) B2392397
theorem B2389571 : Blo 1592995 2389571 := bstep (se 1 (by rfl) ⟨1792178, by rfl⟩ : syracuseStep 2389571 = 3584357) B3584357
theorem B1594947 : Blo 1592995 1594947 := bstep (se 1 (by rfl) ⟨1196210, by rfl⟩ : syracuseStep 1594947 = 2392421) B2392421
theorem B7657037 : Blo 1592995 7657037 := bstep (se 3 (by rfl) ⟨1435694, by rfl⟩ : syracuseStep 7657037 = 2871389) B2871389
theorem B3585617 : Blo 1592995 3585617 := bstep (se 2 (by rfl) ⟨1344606, by rfl⟩ : syracuseStep 3585617 = 2689213) B2689213
theorem B1594963 : Blo 1592995 1594963 := bstep (se 1 (by rfl) ⟨1196222, by rfl⟩ : syracuseStep 1594963 = 2392445) B2392445
theorem B2389601 : Blo 1592995 2389601 := bstep (se 2 (by rfl) ⟨896100, by rfl⟩ : syracuseStep 2389601 = 1792201) B1792201
theorem B3585635 : Blo 1592995 3585635 := bstep (se 1 (by rfl) ⟨2689226, by rfl⟩ : syracuseStep 3585635 = 5378453) B5378453
theorem B1594979 : Blo 1592995 1594979 := bstep (se 1 (by rfl) ⟨1196234, by rfl⟩ : syracuseStep 1594979 = 2392469) B2392469
theorem B2389619 : Blo 1592995 2389619 := bstep (se 1 (by rfl) ⟨1792214, by rfl⟩ : syracuseStep 2389619 = 3584429) B3584429
theorem B1594995 : Blo 1592995 1594995 := bstep (se 1 (by rfl) ⟨1196246, by rfl⟩ : syracuseStep 1594995 = 2392493) B2392493
theorem B2389649 : Blo 1592995 2389649 := bstep (se 2 (by rfl) ⟨896118, by rfl⟩ : syracuseStep 2389649 = 1792237) B1792237
theorem B2389667 : Blo 1592995 2389667 := bstep (se 1 (by rfl) ⟨1792250, by rfl⟩ : syracuseStep 2389667 = 3584501) B3584501
theorem B2389697 : Blo 1592995 2389697 := bstep (se 2 (by rfl) ⟨896136, by rfl⟩ : syracuseStep 2389697 = 1792273) B1792273
theorem B2389715 : Blo 1592995 2389715 := bstep (se 1 (by rfl) ⟨1792286, by rfl⟩ : syracuseStep 2389715 = 3584573) B3584573
theorem B2389745 : Blo 1592995 2389745 := bstep (se 2 (by rfl) ⟨896154, by rfl⟩ : syracuseStep 2389745 = 1792309) B1792309
theorem B2389763 : Blo 1592995 2389763 := bstep (se 1 (by rfl) ⟨1792322, by rfl⟩ : syracuseStep 2389763 = 3584645) B3584645
theorem B7370509 : Blo 1592995 7370509 := bstep (se 3 (by rfl) ⟨1381970, by rfl⟩ : syracuseStep 7370509 = 2763941) B2763941
theorem B5379857 : Blo 1592995 5379857 := bstep (se 2 (by rfl) ⟨2017446, by rfl⟩ : syracuseStep 5379857 = 4034893) B4034893
theorem B2389793 : Blo 1592995 2389793 := bstep (se 2 (by rfl) ⟨896172, by rfl⟩ : syracuseStep 2389793 = 1792345) B1792345
theorem B2389811 : Blo 1592995 2389811 := bstep (se 1 (by rfl) ⟨1792358, by rfl⟩ : syracuseStep 2389811 = 3584717) B3584717
theorem B1726259 : Blo 1592995 1726259 := bstep (se 1 (by rfl) ⟨1294694, by rfl⟩ : syracuseStep 1726259 = 2589389) B2589389
theorem B9074501 : Blo 1592995 9074501 := bstep (se 4 (by rfl) ⟨850734, by rfl⟩ : syracuseStep 9074501 = 1701469) B1701469
theorem B22107973 : Blo 1592995 22107973 := bstep (se 4 (by rfl) ⟨2072622, by rfl⟩ : syracuseStep 22107973 = 4145245) B4145245
theorem B2389841 : Blo 1592995 2389841 := bstep (se 2 (by rfl) ⟨896190, by rfl⟩ : syracuseStep 2389841 = 1792381) B1792381
theorem B2389859 : Blo 1592995 2389859 := bstep (se 1 (by rfl) ⟨1792394, by rfl⟩ : syracuseStep 2389859 = 3584789) B3584789
theorem B3585905 : Blo 1592995 3585905 := bstep (se 2 (by rfl) ⟨1344714, by rfl⟩ : syracuseStep 3585905 = 2689429) B2689429
theorem B2389889 : Blo 1592995 2389889 := bstep (se 2 (by rfl) ⟨896208, by rfl⟩ : syracuseStep 2389889 = 1792417) B1792417
theorem B3585923 : Blo 1592995 3585923 := bstep (se 1 (by rfl) ⟨2689442, by rfl⟩ : syracuseStep 3585923 = 5378885) B5378885
theorem B2389907 : Blo 1592995 2389907 := bstep (se 1 (by rfl) ⟨1792430, by rfl⟩ : syracuseStep 2389907 = 3584861) B3584861
theorem B1660819 : Blo 1592995 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B2389937 : Blo 1592995 2389937 := bstep (se 2 (by rfl) ⟨896226, by rfl⟩ : syracuseStep 2389937 = 1792453) B1792453
theorem B1701811 : Blo 1592995 1701811 := bstep (se 1 (by rfl) ⟨1276358, by rfl⟩ : syracuseStep 1701811 = 2552717) B2552717
theorem B2389955 : Blo 1592995 2389955 := bstep (se 1 (by rfl) ⟨1792466, by rfl⟩ : syracuseStep 2389955 = 3584933) B3584933
theorem B5109713 : Blo 1592995 5109713 := bstep (se 2 (by rfl) ⟨1916142, by rfl⟩ : syracuseStep 5109713 = 3832285) B3832285
theorem B2389985 : Blo 1592995 2389985 := bstep (se 2 (by rfl) ⟨896244, by rfl⟩ : syracuseStep 2389985 = 1792489) B1792489
theorem B3635171 : Blo 1592995 3635171 := bstep (se 1 (by rfl) ⟨2726378, by rfl⟩ : syracuseStep 3635171 = 5452757) B5452757
theorem B3405809 : Blo 1592995 3405809 := bstep (se 2 (by rfl) ⟨1277178, by rfl⟩ : syracuseStep 3405809 = 2554357) B2554357
theorem B2390003 : Blo 1592995 2390003 := bstep (se 1 (by rfl) ⟨1792502, by rfl⟩ : syracuseStep 2390003 = 3585005) B3585005
theorem B2390033 : Blo 1592995 2390033 := bstep (se 2 (by rfl) ⟨896262, by rfl⟩ : syracuseStep 2390033 = 1792525) B1792525
theorem B4036625 : Blo 1592995 4036625 := bstep (se 2 (by rfl) ⟨1513734, by rfl⟩ : syracuseStep 4036625 = 3027469) B3027469
theorem B2390051 : Blo 1592995 2390051 := bstep (se 1 (by rfl) ⟨1792538, by rfl⟩ : syracuseStep 2390051 = 3585077) B3585077
theorem B2390081 : Blo 1592995 2390081 := bstep (se 2 (by rfl) ⟨896280, by rfl⟩ : syracuseStep 2390081 = 1792561) B1792561
theorem B4847683 : Blo 1592995 4847683 := bstep (se 1 (by rfl) ⟨3635762, by rfl⟩ : syracuseStep 4847683 = 7271525) B7271525
theorem B4036675 : Blo 1592995 4036675 := bstep (se 1 (by rfl) ⟨3027506, by rfl⟩ : syracuseStep 4036675 = 6055013) B6055013
theorem B2390099 : Blo 1592995 2390099 := bstep (se 1 (by rfl) ⟨1792574, by rfl⟩ : syracuseStep 2390099 = 3585149) B3585149
theorem B2390129 : Blo 1592995 2390129 := bstep (se 2 (by rfl) ⟨896298, by rfl⟩ : syracuseStep 2390129 = 1792597) B1792597
theorem B12269681 : Blo 1592995 12269681 := bstep (se 2 (by rfl) ⟨4601130, by rfl⟩ : syracuseStep 12269681 = 9202261) B9202261
theorem B2390147 : Blo 1592995 2390147 := bstep (se 1 (by rfl) ⟨1792610, by rfl⟩ : syracuseStep 2390147 = 3585221) B3585221
theorem B3586193 : Blo 1592995 3586193 := bstep (se 2 (by rfl) ⟨1344822, by rfl⟩ : syracuseStep 3586193 = 2689645) B2689645
theorem B1792147 : Blo 1592995 1792147 := bstep (se 1 (by rfl) ⟨1344110, by rfl⟩ : syracuseStep 1792147 = 2688221) B2688221
theorem B2390177 : Blo 1592995 2390177 := bstep (se 2 (by rfl) ⟨896316, by rfl⟩ : syracuseStep 2390177 = 1792633) B1792633
theorem B3586211 : Blo 1592995 3586211 := bstep (se 1 (by rfl) ⟨2689658, by rfl⟩ : syracuseStep 3586211 = 5379317) B5379317
theorem B2390195 : Blo 1592995 2390195 := bstep (se 1 (by rfl) ⟨1792646, by rfl⟩ : syracuseStep 2390195 = 3585293) B3585293
theorem B1702067 : Blo 1592995 1702067 := bstep (se 1 (by rfl) ⟨1276550, by rfl⟩ : syracuseStep 1702067 = 2553101) B2553101
theorem B2554049 : Blo 1592995 2554049 := bstep (se 2 (by rfl) ⟨957768, by rfl⟩ : syracuseStep 2554049 = 1915537) B1915537
theorem B2390225 : Blo 1592995 2390225 := bstep (se 2 (by rfl) ⟨896334, by rfl⟩ : syracuseStep 2390225 = 1792669) B1792669
theorem B4036817 : Blo 1592995 4036817 := bstep (se 2 (by rfl) ⟨1513806, by rfl⟩ : syracuseStep 4036817 = 3027613) B3027613
theorem B2390243 : Blo 1592995 2390243 := bstep (se 1 (by rfl) ⟨1792682, by rfl⟩ : syracuseStep 2390243 = 3585365) B3585365
theorem B6052067 : Blo 1592995 6052067 := bstep (se 1 (by rfl) ⟨4539050, by rfl⟩ : syracuseStep 6052067 = 9078101) B9078101
theorem B4536557 : Blo 1592995 4536557 := bstep (se 3 (by rfl) ⟨850604, by rfl⟩ : syracuseStep 4536557 = 1701209) B1701209
theorem B2390273 : Blo 1592995 2390273 := bstep (se 2 (by rfl) ⟨896352, by rfl⟩ : syracuseStep 2390273 = 1792705) B1792705
theorem B2390291 : Blo 1592995 2390291 := bstep (se 1 (by rfl) ⟨1792718, by rfl⟩ : syracuseStep 2390291 = 3585437) B3585437
theorem B1792291 : Blo 1592995 1792291 := bstep (se 1 (by rfl) ⟨1344218, by rfl⟩ : syracuseStep 1792291 = 2688437) B2688437
theorem B5380397 : Blo 1592995 5380397 := bstep (se 3 (by rfl) ⟨1008824, by rfl⟩ : syracuseStep 5380397 = 2017649) B2017649
theorem B2390321 : Blo 1592995 2390321 := bstep (se 2 (by rfl) ⟨896370, by rfl⟩ : syracuseStep 2390321 = 1792741) B1792741
theorem B2554177 : Blo 1592995 2554177 := bstep (se 2 (by rfl) ⟨957816, by rfl⟩ : syracuseStep 2554177 = 1915633) B1915633
theorem B2390339 : Blo 1592995 2390339 := bstep (se 1 (by rfl) ⟨1792754, by rfl⟩ : syracuseStep 2390339 = 3585509) B3585509
theorem B2390369 : Blo 1592995 2390369 := bstep (se 2 (by rfl) ⟨896388, by rfl⟩ : syracuseStep 2390369 = 1792777) B1792777
theorem B5380451 : Blo 1592995 5380451 := bstep (se 1 (by rfl) ⟨4035338, by rfl⟩ : syracuseStep 5380451 = 8070677) B8070677
theorem B7657841 : Blo 1592995 7657841 := bstep (se 2 (by rfl) ⟨2871690, by rfl⟩ : syracuseStep 7657841 = 5743381) B5743381
theorem B9083249 : Blo 1592995 9083249 := bstep (se 2 (by rfl) ⟨3406218, by rfl⟩ : syracuseStep 9083249 = 6812437) B6812437
theorem B2390387 : Blo 1592995 2390387 := bstep (se 1 (by rfl) ⟨1792790, by rfl⟩ : syracuseStep 2390387 = 3585581) B3585581
theorem B2390417 : Blo 1592995 2390417 := bstep (se 2 (by rfl) ⟨896406, by rfl⟩ : syracuseStep 2390417 = 1792813) B1792813
theorem B2390435 : Blo 1592995 2390435 := bstep (se 1 (by rfl) ⟨1792826, by rfl⟩ : syracuseStep 2390435 = 3585653) B3585653
theorem B4536749 : Blo 1592995 4536749 := bstep (se 3 (by rfl) ⟨850640, by rfl⟩ : syracuseStep 4536749 = 1701281) B1701281
theorem B3586481 : Blo 1592995 3586481 := bstep (se 2 (by rfl) ⟨1344930, by rfl⟩ : syracuseStep 3586481 = 2689861) B2689861
theorem B1792435 : Blo 1592995 1792435 := bstep (se 1 (by rfl) ⟨1344326, by rfl⟩ : syracuseStep 1792435 = 2688653) B2688653
theorem B2390465 : Blo 1592995 2390465 := bstep (se 2 (by rfl) ⟨896424, by rfl⟩ : syracuseStep 2390465 = 1792849) B1792849
theorem B3586499 : Blo 1592995 3586499 := bstep (se 1 (by rfl) ⟨2689874, by rfl⟩ : syracuseStep 3586499 = 5379749) B5379749
theorem B2390483 : Blo 1592995 2390483 := bstep (se 1 (by rfl) ⟨1792862, by rfl⟩ : syracuseStep 2390483 = 3585725) B3585725
theorem B9075185 : Blo 1592995 9075185 := bstep (se 2 (by rfl) ⟨3403194, by rfl⟩ : syracuseStep 9075185 = 6806389) B6806389
theorem B2390513 : Blo 1592995 2390513 := bstep (se 2 (by rfl) ⟨896442, by rfl⟩ : syracuseStep 2390513 = 1792885) B1792885
theorem B3406321 : Blo 1592995 3406321 := bstep (se 2 (by rfl) ⟨1277370, by rfl⟩ : syracuseStep 3406321 = 2554741) B2554741
theorem B2390531 : Blo 1592995 2390531 := bstep (se 1 (by rfl) ⟨1792898, by rfl⟩ : syracuseStep 2390531 = 3585797) B3585797
theorem B2390561 : Blo 1592995 2390561 := bstep (se 2 (by rfl) ⟨896460, by rfl⟩ : syracuseStep 2390561 = 1792921) B1792921
theorem B6806065 : Blo 1592995 6806065 := bstep (se 2 (by rfl) ⟨2552274, by rfl⟩ : syracuseStep 6806065 = 5104549) B5104549
theorem B2390579 : Blo 1592995 2390579 := bstep (se 1 (by rfl) ⟨1792934, by rfl⟩ : syracuseStep 2390579 = 3585869) B3585869
theorem B1792579 : Blo 1592995 1792579 := bstep (se 1 (by rfl) ⟨1344434, by rfl⟩ : syracuseStep 1792579 = 2688869) B2688869
theorem B2390609 : Blo 1592995 2390609 := bstep (se 2 (by rfl) ⟨896478, by rfl⟩ : syracuseStep 2390609 = 1792957) B1792957
theorem B2390627 : Blo 1592995 2390627 := bstep (se 1 (by rfl) ⟨1792970, by rfl⟩ : syracuseStep 2390627 = 3585941) B3585941
theorem B5380721 : Blo 1592995 5380721 := bstep (se 2 (by rfl) ⟨2017770, by rfl⟩ : syracuseStep 5380721 = 4035541) B4035541
theorem B2873969 : Blo 1592995 2873969 := bstep (se 2 (by rfl) ⟨1077738, by rfl⟩ : syracuseStep 2873969 = 2155477) B2155477
theorem B2390657 : Blo 1592995 2390657 := bstep (se 2 (by rfl) ⟨896496, by rfl⟩ : syracuseStep 2390657 = 1792993) B1792993
theorem B2390675 : Blo 1592995 2390675 := bstep (se 1 (by rfl) ⟨1793006, by rfl⟩ : syracuseStep 2390675 = 3586013) B3586013
theorem B8067761 : Blo 1592995 8067761 := bstep (se 2 (by rfl) ⟨3025410, by rfl⟩ : syracuseStep 8067761 = 6050821) B6050821
theorem B2390705 : Blo 1592995 2390705 := bstep (se 2 (by rfl) ⟨896514, by rfl⟩ : syracuseStep 2390705 = 1793029) B1793029
theorem B2390723 : Blo 1592995 2390723 := bstep (se 1 (by rfl) ⟨1793042, by rfl⟩ : syracuseStep 2390723 = 3586085) B3586085
theorem B7371469 : Blo 1592995 7371469 := bstep (se 3 (by rfl) ⟨1382150, by rfl⟩ : syracuseStep 7371469 = 2764301) B2764301
theorem B3586769 : Blo 1592995 3586769 := bstep (se 2 (by rfl) ⟨1345038, by rfl⟩ : syracuseStep 3586769 = 2690077) B2690077
theorem B1792723 : Blo 1592995 1792723 := bstep (se 1 (by rfl) ⟨1344542, by rfl⟩ : syracuseStep 1792723 = 2689085) B2689085
theorem B2390753 : Blo 1592995 2390753 := bstep (se 2 (by rfl) ⟨896532, by rfl⟩ : syracuseStep 2390753 = 1793065) B1793065
theorem B3586787 : Blo 1592995 3586787 := bstep (se 1 (by rfl) ⟨2690090, by rfl⟩ : syracuseStep 3586787 = 5380181) B5380181
theorem B2390771 : Blo 1592995 2390771 := bstep (se 1 (by rfl) ⟨1793078, by rfl⟩ : syracuseStep 2390771 = 3586157) B3586157
theorem B2390801 : Blo 1592995 2390801 := bstep (se 2 (by rfl) ⟨896550, by rfl⟩ : syracuseStep 2390801 = 1793101) B1793101
theorem B2390819 : Blo 1592995 2390819 := bstep (se 1 (by rfl) ⟨1793114, by rfl⟩ : syracuseStep 2390819 = 3586229) B3586229
theorem B2390849 : Blo 1592995 2390849 := bstep (se 2 (by rfl) ⟨896568, by rfl⟩ : syracuseStep 2390849 = 1793137) B1793137
theorem B13998917 : Blo 1592995 13998917 := bstep (se 4 (by rfl) ⟨1312398, by rfl⟩ : syracuseStep 13998917 = 2624797) B2624797
theorem B4848461 : Blo 1592995 4848461 := bstep (se 3 (by rfl) ⟨909086, by rfl⟩ : syracuseStep 4848461 = 1818173) B1818173
theorem B2390867 : Blo 1592995 2390867 := bstep (se 1 (by rfl) ⟨1793150, by rfl⟩ : syracuseStep 2390867 = 3586301) B3586301
theorem B1792867 : Blo 1592995 1792867 := bstep (se 1 (by rfl) ⟨1344650, by rfl⟩ : syracuseStep 1792867 = 2689301) B2689301
theorem B2390897 : Blo 1592995 2390897 := bstep (se 2 (by rfl) ⟨896586, by rfl⟩ : syracuseStep 2390897 = 1793173) B1793173
theorem B2390915 : Blo 1592995 2390915 := bstep (se 1 (by rfl) ⟨1793186, by rfl⟩ : syracuseStep 2390915 = 3586373) B3586373
theorem B2390945 : Blo 1592995 2390945 := bstep (se 2 (by rfl) ⟨896604, by rfl⟩ : syracuseStep 2390945 = 1793209) B1793209
theorem B1702819 : Blo 1592995 1702819 := bstep (se 1 (by rfl) ⟨1277114, by rfl⟩ : syracuseStep 1702819 = 2554229) B2554229
theorem B2390963 : Blo 1592995 2390963 := bstep (se 1 (by rfl) ⟨1793222, by rfl⟩ : syracuseStep 2390963 = 3586445) B3586445
theorem B2390993 : Blo 1592995 2390993 := bstep (se 2 (by rfl) ⟨896622, by rfl⟩ : syracuseStep 2390993 = 1793245) B1793245
theorem B2391011 : Blo 1592995 2391011 := bstep (se 1 (by rfl) ⟨1793258, by rfl⟩ : syracuseStep 2391011 = 3586517) B3586517
theorem B3587057 : Blo 1592995 3587057 := bstep (se 2 (by rfl) ⟨1345146, by rfl⟩ : syracuseStep 3587057 = 2690293) B2690293
theorem B1793011 : Blo 1592995 1793011 := bstep (se 1 (by rfl) ⟨1344758, by rfl⟩ : syracuseStep 1793011 = 2689517) B2689517
theorem B2391041 : Blo 1592995 2391041 := bstep (se 2 (by rfl) ⟨896640, by rfl⟩ : syracuseStep 2391041 = 1793281) B1793281
theorem B3587075 : Blo 1592995 3587075 := bstep (se 1 (by rfl) ⟨2690306, by rfl⟩ : syracuseStep 3587075 = 5380613) B5380613
theorem B2391059 : Blo 1592995 2391059 := bstep (se 1 (by rfl) ⟨1793294, by rfl⟩ : syracuseStep 2391059 = 3586589) B3586589
theorem B2391089 : Blo 1592995 2391089 := bstep (se 2 (by rfl) ⟨896658, by rfl⟩ : syracuseStep 2391089 = 1793317) B1793317
theorem B2391107 : Blo 1592995 2391107 := bstep (se 1 (by rfl) ⟨1793330, by rfl⟩ : syracuseStep 2391107 = 3586661) B3586661
theorem B2153569 : Blo 1592995 2153569 := bstep (se 2 (by rfl) ⟨807588, by rfl⟩ : syracuseStep 2153569 = 1615177) B1615177
theorem B2391137 : Blo 1592995 2391137 := bstep (se 2 (by rfl) ⟨896676, by rfl⟩ : syracuseStep 2391137 = 1793353) B1793353
theorem B2391155 : Blo 1592995 2391155 := bstep (se 1 (by rfl) ⟨1793366, by rfl⟩ : syracuseStep 2391155 = 3586733) B3586733
theorem B1793155 : Blo 1592995 1793155 := bstep (se 1 (by rfl) ⟨1344866, by rfl⟩ : syracuseStep 1793155 = 2689733) B2689733
theorem B5381261 : Blo 1592995 5381261 := bstep (se 3 (by rfl) ⟨1008986, by rfl⟩ : syracuseStep 5381261 = 2017973) B2017973
theorem B14744717 : Blo 1592995 14744717 := bstep (se 3 (by rfl) ⟨2764634, by rfl⟩ : syracuseStep 14744717 = 5529269) B5529269
theorem B2391185 : Blo 1592995 2391185 := bstep (se 2 (by rfl) ⟨896694, by rfl⟩ : syracuseStep 2391185 = 1793389) B1793389
theorem B2391203 : Blo 1592995 2391203 := bstep (se 1 (by rfl) ⟨1793402, by rfl⟩ : syracuseStep 2391203 = 3586805) B3586805
theorem B2423987 : Blo 1592995 2423987 := bstep (se 1 (by rfl) ⟨1817990, by rfl⟩ : syracuseStep 2423987 = 3635981) B3635981
theorem B2391233 : Blo 1592995 2391233 := bstep (se 2 (by rfl) ⟨896712, by rfl⟩ : syracuseStep 2391233 = 1793425) B1793425
theorem B5381315 : Blo 1592995 5381315 := bstep (se 1 (by rfl) ⟨4035986, by rfl⟩ : syracuseStep 5381315 = 8071973) B8071973
theorem B10353869 : Blo 1592995 10353869 := bstep (se 3 (by rfl) ⟨1941350, by rfl⟩ : syracuseStep 10353869 = 3882701) B3882701
theorem B6053069 : Blo 1592995 6053069 := bstep (se 3 (by rfl) ⟨1134950, by rfl⟩ : syracuseStep 6053069 = 2269901) B2269901
theorem B2391251 : Blo 1592995 2391251 := bstep (se 1 (by rfl) ⟨1793438, by rfl⟩ : syracuseStep 2391251 = 3586877) B3586877
theorem B2391281 : Blo 1592995 2391281 := bstep (se 2 (by rfl) ⟨896730, by rfl⟩ : syracuseStep 2391281 = 1793461) B1793461
theorem B2391299 : Blo 1592995 2391299 := bstep (se 1 (by rfl) ⟨1793474, by rfl⟩ : syracuseStep 2391299 = 3586949) B3586949
theorem B3587345 : Blo 1592995 3587345 := bstep (se 2 (by rfl) ⟨1345254, by rfl⟩ : syracuseStep 3587345 = 2690509) B2690509
theorem B2153747 : Blo 1592995 2153747 := bstep (se 1 (by rfl) ⟨1615310, by rfl⟩ : syracuseStep 2153747 = 3230621) B3230621
theorem B1793299 : Blo 1592995 1793299 := bstep (se 1 (by rfl) ⟨1344974, by rfl⟩ : syracuseStep 1793299 = 2689949) B2689949
theorem B2391329 : Blo 1592995 2391329 := bstep (se 2 (by rfl) ⟨896748, by rfl⟩ : syracuseStep 2391329 = 1793497) B1793497
theorem B3587363 : Blo 1592995 3587363 := bstep (se 1 (by rfl) ⟨2690522, by rfl⟩ : syracuseStep 3587363 = 5381045) B5381045
theorem B2391347 : Blo 1592995 2391347 := bstep (se 1 (by rfl) ⟨1793510, by rfl⟩ : syracuseStep 2391347 = 3587021) B3587021
theorem B2391377 : Blo 1592995 2391377 := bstep (se 2 (by rfl) ⟨896766, by rfl⟩ : syracuseStep 2391377 = 1793533) B1793533
theorem B2391395 : Blo 1592995 2391395 := bstep (se 1 (by rfl) ⟨1793546, by rfl⟩ : syracuseStep 2391395 = 3587093) B3587093
theorem B16588145 : Blo 1592995 16588145 := bstep (se 2 (by rfl) ⟨6220554, by rfl⟩ : syracuseStep 16588145 = 12441109) B12441109
theorem B2391425 : Blo 1592995 2391425 := bstep (se 2 (by rfl) ⟨896784, by rfl⟩ : syracuseStep 2391425 = 1793569) B1793569
theorem B4537741 : Blo 1592995 4537741 := bstep (se 3 (by rfl) ⟨850826, by rfl⟩ : syracuseStep 4537741 = 1701653) B1701653
theorem B9330061 : Blo 1592995 9330061 := bstep (se 3 (by rfl) ⟨1749386, by rfl⟩ : syracuseStep 9330061 = 3498773) B3498773
theorem B2391443 : Blo 1592995 2391443 := bstep (se 1 (by rfl) ⟨1793582, by rfl⟩ : syracuseStep 2391443 = 3587165) B3587165
theorem B1793443 : Blo 1592995 1793443 := bstep (se 1 (by rfl) ⟨1345082, by rfl⟩ : syracuseStep 1793443 = 2690165) B2690165
theorem B9698723 : Blo 1592995 9698723 := bstep (se 1 (by rfl) ⟨7274042, by rfl⟩ : syracuseStep 9698723 = 14548085) B14548085
theorem B2391473 : Blo 1592995 2391473 := bstep (se 2 (by rfl) ⟨896802, by rfl⟩ : syracuseStep 2391473 = 1793605) B1793605
theorem B2391491 : Blo 1592995 2391491 := bstep (se 1 (by rfl) ⟨1793618, by rfl⟩ : syracuseStep 2391491 = 3587237) B3587237
theorem B5381585 : Blo 1592995 5381585 := bstep (se 2 (by rfl) ⟨2018094, by rfl⟩ : syracuseStep 5381585 = 4036189) B4036189
theorem B2391521 : Blo 1592995 2391521 := bstep (se 2 (by rfl) ⟨896820, by rfl⟩ : syracuseStep 2391521 = 1793641) B1793641
theorem B2268643 : Blo 1592995 2268643 := bstep (se 1 (by rfl) ⟨1701482, by rfl⟩ : syracuseStep 2268643 = 3402965) B3402965
theorem B2391539 : Blo 1592995 2391539 := bstep (se 1 (by rfl) ⟨1793654, by rfl⟩ : syracuseStep 2391539 = 3587309) B3587309
theorem B2391569 : Blo 1592995 2391569 := bstep (se 2 (by rfl) ⟨896838, by rfl⟩ : syracuseStep 2391569 = 1793677) B1793677
theorem B2391587 : Blo 1592995 2391587 := bstep (se 1 (by rfl) ⟨1793690, by rfl⟩ : syracuseStep 2391587 = 3587381) B3587381
theorem B3587633 : Blo 1592995 3587633 := bstep (se 2 (by rfl) ⟨1345362, by rfl⟩ : syracuseStep 3587633 = 2690725) B2690725
theorem B1793587 : Blo 1592995 1793587 := bstep (se 1 (by rfl) ⟨1345190, by rfl⟩ : syracuseStep 1793587 = 2690381) B2690381
theorem B2391617 : Blo 1592995 2391617 := bstep (se 2 (by rfl) ⟨896856, by rfl⟩ : syracuseStep 2391617 = 1793713) B1793713
theorem B2268739 : Blo 1592995 2268739 := bstep (se 1 (by rfl) ⟨1701554, by rfl⟩ : syracuseStep 2268739 = 3403109) B3403109
theorem B3587651 : Blo 1592995 3587651 := bstep (se 1 (by rfl) ⟨2690738, by rfl⟩ : syracuseStep 3587651 = 5381477) B5381477
theorem B2391635 : Blo 1592995 2391635 := bstep (se 1 (by rfl) ⟨1793726, by rfl⟩ : syracuseStep 2391635 = 3587453) B3587453
theorem B9698915 : Blo 1592995 9698915 := bstep (se 1 (by rfl) ⟨7274186, by rfl⟩ : syracuseStep 9698915 = 14548373) B14548373
theorem B2391665 : Blo 1592995 2391665 := bstep (se 2 (by rfl) ⟨896874, by rfl⟩ : syracuseStep 2391665 = 1793749) B1793749
theorem B2391683 : Blo 1592995 2391683 := bstep (se 1 (by rfl) ⟨1793762, by rfl⟩ : syracuseStep 2391683 = 3587525) B3587525
theorem B13803149 : Blo 1592995 13803149 := bstep (se 3 (by rfl) ⟨2588090, by rfl⟩ : syracuseStep 13803149 = 5176181) B5176181
theorem B2391713 : Blo 1592995 2391713 := bstep (se 2 (by rfl) ⟨896892, by rfl⟩ : syracuseStep 2391713 = 1793785) B1793785
theorem B2391731 : Blo 1592995 2391731 := bstep (se 1 (by rfl) ⟨1793798, by rfl⟩ : syracuseStep 2391731 = 3587597) B3587597
theorem B1793731 : Blo 1592995 1793731 := bstep (se 1 (by rfl) ⟨1345298, by rfl⟩ : syracuseStep 1793731 = 2690597) B2690597
theorem B2391761 : Blo 1592995 2391761 := bstep (se 2 (by rfl) ⟨896910, by rfl⟩ : syracuseStep 2391761 = 1793821) B1793821
theorem B4087523 : Blo 1592995 4087523 := bstep (se 1 (by rfl) ⟨3065642, by rfl⟩ : syracuseStep 4087523 = 6131285) B6131285
theorem B2391779 : Blo 1592995 2391779 := bstep (se 1 (by rfl) ⟨1793834, by rfl⟩ : syracuseStep 2391779 = 3587669) B3587669
theorem B2391809 : Blo 1592995 2391809 := bstep (se 2 (by rfl) ⟨896928, by rfl⟩ : syracuseStep 2391809 = 1793857) B1793857
theorem B2391827 : Blo 1592995 2391827 := bstep (se 1 (by rfl) ⟨1793870, by rfl⟩ : syracuseStep 2391827 = 3587741) B3587741
theorem B2391857 : Blo 1592995 2391857 := bstep (se 2 (by rfl) ⟨896946, by rfl⟩ : syracuseStep 2391857 = 1793893) B1793893
theorem B2391875 : Blo 1592995 2391875 := bstep (se 1 (by rfl) ⟨1793906, by rfl⟩ : syracuseStep 2391875 = 3587813) B3587813
theorem B3587921 : Blo 1592995 3587921 := bstep (se 2 (by rfl) ⟨1345470, by rfl⟩ : syracuseStep 3587921 = 2690941) B2690941
theorem B1793875 : Blo 1592995 1793875 := bstep (se 1 (by rfl) ⟨1345406, by rfl⟩ : syracuseStep 1793875 = 2690813) B2690813
theorem B2391905 : Blo 1592995 2391905 := bstep (se 2 (by rfl) ⟨896964, by rfl⟩ : syracuseStep 2391905 = 1793929) B1793929
theorem B4308835 : Blo 1592995 4308835 := bstep (se 1 (by rfl) ⟨3231626, by rfl⟩ : syracuseStep 4308835 = 6463253) B6463253
theorem B3587939 : Blo 1592995 3587939 := bstep (se 1 (by rfl) ⟨2690954, by rfl⟩ : syracuseStep 3587939 = 5381909) B5381909
theorem B2391923 : Blo 1592995 2391923 := bstep (se 1 (by rfl) ⟨1793942, by rfl⟩ : syracuseStep 2391923 = 3587885) B3587885
theorem B2391953 : Blo 1592995 2391953 := bstep (se 2 (by rfl) ⟨896982, by rfl⟩ : syracuseStep 2391953 = 1793965) B1793965
theorem B9076643 : Blo 1592995 9076643 := bstep (se 1 (by rfl) ⟨6807482, by rfl⟩ : syracuseStep 9076643 = 13614965) B13614965
theorem B2391971 : Blo 1592995 2391971 := bstep (se 1 (by rfl) ⟨1793978, by rfl⟩ : syracuseStep 2391971 = 3587957) B3587957
theorem B2392001 : Blo 1592995 2392001 := bstep (se 2 (by rfl) ⟨897000, by rfl⟩ : syracuseStep 2392001 = 1794001) B1794001
theorem B8617925 : Blo 1592995 8617925 := bstep (se 4 (by rfl) ⟨807930, by rfl⟩ : syracuseStep 8617925 = 1615861) B1615861
theorem B12107717 : Blo 1592995 12107717 := bstep (se 4 (by rfl) ⟨1135098, by rfl⟩ : syracuseStep 12107717 = 2270197) B2270197
theorem B2392019 : Blo 1592995 2392019 := bstep (se 1 (by rfl) ⟨1794014, by rfl⟩ : syracuseStep 2392019 = 3588029) B3588029
theorem B5103587 : Blo 1592995 5103587 := bstep (se 1 (by rfl) ⟨3827690, by rfl⟩ : syracuseStep 5103587 = 7655381) B7655381
theorem B1794019 : Blo 1592995 1794019 := bstep (se 1 (by rfl) ⟨1345514, by rfl⟩ : syracuseStep 1794019 = 2691029) B2691029
theorem B5382125 : Blo 1592995 5382125 := bstep (se 3 (by rfl) ⟨1009148, by rfl⟩ : syracuseStep 5382125 = 2018297) B2018297
theorem B2392049 : Blo 1592995 2392049 := bstep (se 2 (by rfl) ⟨897018, by rfl⟩ : syracuseStep 2392049 = 1794037) B1794037
theorem B29065229 : Blo 1592995 29065229 := bstep (se 3 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 29065229 = 10899461) B10899461
theorem B3588119 : Blo 1592995 3588119 := bstep (se 1 (by rfl) ⟨2691089, by rfl⟩ : syracuseStep 3588119 = 5382179) B5382179
theorem B39297059 : Blo 1592995 39297059 := bstep (se 1 (by rfl) ⟨29472794, by rfl⟩ : syracuseStep 39297059 = 58945589) B58945589
theorem B1794091 : Blo 1592995 1794091 := bstep (se 1 (by rfl) ⟨1345568, by rfl⟩ : syracuseStep 1794091 = 2691137) B2691137
theorem B2392139 : Blo 1592995 2392139 := bstep (se 1 (by rfl) ⟨1794104, by rfl⟩ : syracuseStep 2392139 = 3588209) B3588209
theorem B3448919 : Blo 1592995 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B6463577 : Blo 1592995 6463577 := bstep (se 2 (by rfl) ⟨2423841, by rfl⟩ : syracuseStep 6463577 = 4847683) B4847683
theorem B5382233 : Blo 1592995 5382233 := bstep (se 2 (by rfl) ⟨2018337, by rfl⟩ : syracuseStep 5382233 = 4036675) B4036675
theorem B2392151 : Blo 1592995 2392151 := bstep (se 1 (by rfl) ⟨1794113, by rfl⟩ : syracuseStep 2392151 = 3588227) B3588227
theorem B1794199 : Blo 1592995 1794199 := bstep (se 1 (by rfl) ⟨1345649, by rfl⟩ : syracuseStep 1794199 = 2691299) B2691299
theorem B1818775 : Blo 1592995 1818775 := bstep (se 1 (by rfl) ⟨1364081, by rfl⟩ : syracuseStep 1818775 = 2728163) B2728163
theorem B2392217 : Blo 1592995 2392217 := bstep (se 2 (by rfl) ⟨897081, by rfl⟩ : syracuseStep 2392217 = 1794163) B1794163
theorem B3588299 : Blo 1592995 3588299 := bstep (se 1 (by rfl) ⟨2691224, by rfl⟩ : syracuseStep 3588299 = 5382449) B5382449
theorem B3588353 : Blo 1592995 3588353 := bstep (se 2 (by rfl) ⟨1345632, by rfl⟩ : syracuseStep 3588353 = 2691265) B2691265
theorem B3637505 : Blo 1592995 3637505 := bstep (se 2 (by rfl) ⟨1364064, by rfl⟩ : syracuseStep 3637505 = 2728129) B2728129
theorem B2392331 : Blo 1592995 2392331 := bstep (se 1 (by rfl) ⟨1794248, by rfl⟩ : syracuseStep 2392331 = 3588497) B3588497
theorem B2392343 : Blo 1592995 2392343 := bstep (se 1 (by rfl) ⟨1794257, by rfl⟩ : syracuseStep 2392343 = 3588515) B3588515
theorem B1868087 : Blo 1592995 1868087 := bstep (se 1 (by rfl) ⟨1401065, by rfl⟩ : syracuseStep 1868087 = 2802131) B2802131
theorem B6054209 : Blo 1592995 6054209 := bstep (se 2 (by rfl) ⟨2270328, by rfl⟩ : syracuseStep 6054209 = 4540657) B4540657
theorem B2392409 : Blo 1592995 2392409 := bstep (se 2 (by rfl) ⟨897153, by rfl⟩ : syracuseStep 2392409 = 1794307) B1794307
theorem B12099941 : Blo 1592995 12099941 := bstep (se 4 (by rfl) ⟨1134369, by rfl⟩ : syracuseStep 12099941 = 2268739) B2268739
theorem B9077143 : Blo 1592995 9077143 := bstep (se 1 (by rfl) ⟨6807857, by rfl⟩ : syracuseStep 9077143 = 13615715) B13615715
theorem B24535475 : Blo 1592995 24535475 := bstep (se 1 (by rfl) ⟨18401606, by rfl⟩ : syracuseStep 24535475 = 36803213) B36803213
theorem B3588569 : Blo 1592995 3588569 := bstep (se 2 (by rfl) ⟨1345713, by rfl⟩ : syracuseStep 3588569 = 2691427) B2691427
theorem B4538845 : Blo 1592995 4538845 := bstep (se 3 (by rfl) ⟨851033, by rfl⟩ : syracuseStep 4538845 = 1702067) B1702067
theorem B5104151 : Blo 1592995 5104151 := bstep (se 1 (by rfl) ⟨3828113, by rfl⟩ : syracuseStep 5104151 = 7656227) B7656227
theorem B3588659 : Blo 1592995 3588659 := bstep (se 1 (by rfl) ⟨2691494, by rfl⟩ : syracuseStep 3588659 = 5382989) B5382989
theorem B3588695 : Blo 1592995 3588695 := bstep (se 1 (by rfl) ⟨2691521, by rfl⟩ : syracuseStep 3588695 = 5383043) B5383043
theorem B4539073 : Blo 1592995 4539073 := bstep (se 2 (by rfl) ⟨1702152, by rfl⟩ : syracuseStep 4539073 = 3404305) B3404305
theorem B5743325 : Blo 1592995 5743325 := bstep (se 3 (by rfl) ⟨1076873, by rfl⟩ : syracuseStep 5743325 = 2153747) B2153747
theorem B6808337 : Blo 1592995 6808337 := bstep (se 2 (by rfl) ⟨2553126, by rfl⟩ : syracuseStep 6808337 = 5106253) B5106253
theorem B5382935 : Blo 1592995 5382935 := bstep (se 1 (by rfl) ⟨4037201, by rfl⟩ : syracuseStep 5382935 = 8074403) B8074403
theorem B12100427 : Blo 1592995 12100427 := bstep (se 1 (by rfl) ⟨9075320, by rfl⟩ : syracuseStep 12100427 = 18150641) B18150641
theorem B5178205 : Blo 1592995 5178205 := bstep (se 3 (by rfl) ⟨970913, by rfl⟩ : syracuseStep 5178205 = 1941827) B1941827
theorem B45982565 : Blo 1592995 45982565 := bstep (se 4 (by rfl) ⟨4310865, by rfl⟩ : syracuseStep 45982565 = 8621731) B8621731
theorem B2622347 : Blo 1592995 2622347 := bstep (se 1 (by rfl) ⟨1966760, by rfl⟩ : syracuseStep 2622347 = 3933521) B3933521
theorem B5899159 : Blo 1592995 5899159 := bstep (se 1 (by rfl) ⟨4424369, by rfl⟩ : syracuseStep 5899159 = 8848739) B8848739
theorem B4539415 : Blo 1592995 4539415 := bstep (se 1 (by rfl) ⟨3404561, by rfl⟩ : syracuseStep 4539415 = 6809123) B6809123
theorem B5104691 : Blo 1592995 5104691 := bstep (se 1 (by rfl) ⟨3828518, by rfl⟩ : syracuseStep 5104691 = 7657037) B7657037
theorem B2016343 : Blo 1592995 2016343 := bstep (se 1 (by rfl) ⟨1512257, by rfl⟩ : syracuseStep 2016343 = 3024515) B3024515
theorem B2270425 : Blo 1592995 2270425 := bstep (se 2 (by rfl) ⟨851409, by rfl⟩ : syracuseStep 2270425 = 1702819) B1702819
theorem B4310347 : Blo 1592995 4310347 := bstep (se 1 (by rfl) ⟨3232760, by rfl⟩ : syracuseStep 4310347 = 6465521) B6465521
theorem B2270539 : Blo 1592995 2270539 := bstep (se 1 (by rfl) ⟨1702904, by rfl⟩ : syracuseStep 2270539 = 3405809) B3405809
theorem B3024371 : Blo 1592995 3024371 := bstep (se 1 (by rfl) ⟨2268278, by rfl⟩ : syracuseStep 3024371 = 4536557) B4536557
theorem B13985297 : Blo 1592995 13985297 := bstep (se 2 (by rfl) ⟨5244486, by rfl⟩ : syracuseStep 13985297 = 10488973) B10488973
theorem B6055469 : Blo 1592995 6055469 := bstep (se 3 (by rfl) ⟨1135400, by rfl⟩ : syracuseStep 6055469 = 2270801) B2270801
theorem B6055499 : Blo 1592995 6055499 := bstep (se 1 (by rfl) ⟨4541624, by rfl⟩ : syracuseStep 6055499 = 9083249) B9083249
theorem B2688599 : Blo 1592995 2688599 := bstep (se 1 (by rfl) ⟨2016449, by rfl⟩ : syracuseStep 2688599 = 4032899) B4032899
theorem B2688727 : Blo 1592995 2688727 := bstep (se 1 (by rfl) ⟨2016545, by rfl⟩ : syracuseStep 2688727 = 4033091) B4033091
theorem B5105369 : Blo 1592995 5105369 := bstep (se 2 (by rfl) ⟨1914513, by rfl⟩ : syracuseStep 5105369 = 3829027) B3829027
theorem B4540121 : Blo 1592995 4540121 := bstep (se 2 (by rfl) ⟨1702545, by rfl⟩ : syracuseStep 4540121 = 3405091) B3405091
theorem B19384109 : Blo 1592995 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B12109661 : Blo 1592995 12109661 := bstep (se 3 (by rfl) ⟨2270561, by rfl⟩ : syracuseStep 12109661 = 4541123) B4541123
theorem B2017163 : Blo 1592995 2017163 := bstep (se 1 (by rfl) ⟨1512872, by rfl⟩ : syracuseStep 2017163 = 3025745) B3025745
theorem B3024857 : Blo 1592995 3024857 := bstep (se 2 (by rfl) ⟨1134321, by rfl⟩ : syracuseStep 3024857 = 2268643) B2268643
theorem B3065843 : Blo 1592995 3065843 := bstep (se 1 (by rfl) ⟨2299382, by rfl⟩ : syracuseStep 3065843 = 4598765) B4598765
theorem B1615991 : Blo 1592995 1615991 := bstep (se 1 (by rfl) ⟨1211993, by rfl⟩ : syracuseStep 1615991 = 2423987) B2423987
theorem B6465815 : Blo 1592995 6465815 := bstep (se 1 (by rfl) ⟨4849361, by rfl⟩ : syracuseStep 6465815 = 9698723) B9698723
theorem B2689355 : Blo 1592995 2689355 := bstep (se 1 (by rfl) ⟨2017016, by rfl⟩ : syracuseStep 2689355 = 4034033) B4034033
theorem B6465943 : Blo 1592995 6465943 := bstep (se 1 (by rfl) ⟨4849457, by rfl⟩ : syracuseStep 6465943 = 9698915) B9698915
theorem B29477297 : Blo 1592995 29477297 := bstep (se 2 (by rfl) ⟨11053986, by rfl⟩ : syracuseStep 29477297 = 22107973) B22107973
theorem B9202099 : Blo 1592995 9202099 := bstep (se 1 (by rfl) ⟨6901574, by rfl⟩ : syracuseStep 9202099 = 13803149) B13803149
theorem B2689483 : Blo 1592995 2689483 := bstep (se 1 (by rfl) ⟨2017112, by rfl⟩ : syracuseStep 2689483 = 4034225) B4034225
theorem B5745113 : Blo 1592995 5745113 := bstep (se 2 (by rfl) ⟨2154417, by rfl⟩ : syracuseStep 5745113 = 4308835) B4308835
theorem B22981133 : Blo 1592995 22981133 := bstep (se 3 (by rfl) ⟨4308962, by rfl⟩ : syracuseStep 22981133 = 8617925) B8617925
theorem B2214425 : Blo 1592995 2214425 := bstep (se 2 (by rfl) ⟨830409, by rfl⟩ : syracuseStep 2214425 = 1660819) B1660819
theorem B5376563 : Blo 1592995 5376563 := bstep (se 1 (by rfl) ⟨4032422, by rfl⟩ : syracuseStep 5376563 = 8064845) B8064845
theorem B2017867 : Blo 1592995 2017867 := bstep (se 1 (by rfl) ⟨1513400, by rfl⟩ : syracuseStep 2017867 = 3026801) B3026801
theorem B2689625 : Blo 1592995 2689625 := bstep (se 2 (by rfl) ⟨1008609, by rfl⟩ : syracuseStep 2689625 = 2017219) B2017219
theorem B13609565 : Blo 1592995 13609565 := bstep (se 3 (by rfl) ⟨2551793, by rfl⟩ : syracuseStep 13609565 = 5103587) B5103587
theorem B8071811 : Blo 1592995 8071811 := bstep (se 1 (by rfl) ⟨6053858, by rfl⟩ : syracuseStep 8071811 = 12107717) B12107717
theorem B2689753 : Blo 1592995 2689753 := bstep (se 2 (by rfl) ⟨1008657, by rfl⟩ : syracuseStep 2689753 = 2017315) B2017315
theorem B5376833 : Blo 1592995 5376833 := bstep (se 2 (by rfl) ⟨2016312, by rfl⟩ : syracuseStep 5376833 = 4032625) B4032625
theorem B2018135 : Blo 1592995 2018135 := bstep (se 1 (by rfl) ⟨1513601, by rfl⟩ : syracuseStep 2018135 = 3027203) B3027203
theorem B5106611 : Blo 1592995 5106611 := bstep (se 1 (by rfl) ⟨3829958, by rfl⟩ : syracuseStep 5106611 = 7659917) B7659917
theorem B100797401 : Blo 1592995 100797401 := bstep (se 2 (by rfl) ⟨37799025, by rfl⟩ : syracuseStep 100797401 = 75598051) B75598051
theorem B6810713 : Blo 1592995 6810713 := bstep (se 2 (by rfl) ⟨2554017, by rfl⟩ : syracuseStep 6810713 = 5108035) B5108035
theorem B6810797 : Blo 1592995 6810797 := bstep (se 3 (by rfl) ⟨1277024, by rfl⟩ : syracuseStep 6810797 = 2554049) B2554049
theorem B4033739 : Blo 1592995 4033739 := bstep (se 1 (by rfl) ⟨3025304, by rfl⟩ : syracuseStep 4033739 = 6050609) B6050609
theorem B2690327 : Blo 1592995 2690327 := bstep (se 1 (by rfl) ⟨2017745, by rfl⟩ : syracuseStep 2690327 = 4035491) B4035491
theorem B4541761 : Blo 1592995 4541761 := bstep (se 2 (by rfl) ⟨1703160, by rfl⟩ : syracuseStep 4541761 = 3406321) B3406321
theorem B8621387 : Blo 1592995 8621387 := bstep (se 1 (by rfl) ⟨6466040, by rfl⟩ : syracuseStep 8621387 = 12932081) B12932081
theorem B5377373 : Blo 1592995 5377373 := bstep (se 3 (by rfl) ⟨1008257, by rfl⟩ : syracuseStep 5377373 = 2016515) B2016515
theorem B27250019 : Blo 1592995 27250019 := bstep (se 1 (by rfl) ⟨20437514, by rfl⟩ : syracuseStep 27250019 = 40875029) B40875029
theorem B55184753 : Blo 1592995 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B3026315 : Blo 1592995 3026315 := bstep (se 1 (by rfl) ⟨2269736, by rfl⟩ : syracuseStep 3026315 = 4539473) B4539473
theorem B2690455 : Blo 1592995 2690455 := bstep (se 1 (by rfl) ⟨2017841, by rfl⟩ : syracuseStep 2690455 = 4035683) B4035683
theorem B3026497 : Blo 1592995 3026497 := bstep (se 2 (by rfl) ⟨1134936, by rfl⟩ : syracuseStep 3026497 = 2269873) B2269873
theorem B10210967 : Blo 1592995 10210967 := bstep (se 1 (by rfl) ⟨7658225, by rfl⟩ : syracuseStep 10210967 = 15316451) B15316451
theorem B3403417 : Blo 1592995 3403417 := bstep (se 2 (by rfl) ⟨1276281, by rfl⟩ : syracuseStep 3403417 = 2552563) B2552563
theorem B1593003 : Blo 1592995 1593003 := bstep (se 1 (by rfl) ⟨1194752, by rfl⟩ : syracuseStep 1593003 = 2389505) B2389505
theorem B1593015 : Blo 1592995 1593015 := bstep (se 1 (by rfl) ⟨1194761, by rfl⟩ : syracuseStep 1593015 = 2389523) B2389523
theorem B1593035 : Blo 1592995 1593035 := bstep (se 1 (by rfl) ⟨1194776, by rfl⟩ : syracuseStep 1593035 = 2389553) B2389553
theorem B1593047 : Blo 1592995 1593047 := bstep (se 1 (by rfl) ⟨1194785, by rfl⟩ : syracuseStep 1593047 = 2389571) B2389571
theorem B1593067 : Blo 1592995 1593067 := bstep (se 1 (by rfl) ⟨1194800, by rfl⟩ : syracuseStep 1593067 = 2389601) B2389601
theorem B1593079 : Blo 1592995 1593079 := bstep (se 1 (by rfl) ⟨1194809, by rfl⟩ : syracuseStep 1593079 = 2389619) B2389619
theorem B1593099 : Blo 1592995 1593099 := bstep (se 1 (by rfl) ⟨1194824, by rfl⟩ : syracuseStep 1593099 = 2389649) B2389649
theorem B1593111 : Blo 1592995 1593111 := bstep (se 1 (by rfl) ⟨1194833, by rfl⟩ : syracuseStep 1593111 = 2389667) B2389667
theorem B1593131 : Blo 1592995 1593131 := bstep (se 1 (by rfl) ⟨1194848, by rfl⟩ : syracuseStep 1593131 = 2389697) B2389697
theorem B1593143 : Blo 1592995 1593143 := bstep (se 1 (by rfl) ⟨1194857, by rfl⟩ : syracuseStep 1593143 = 2389715) B2389715
theorem B1593163 : Blo 1592995 1593163 := bstep (se 1 (by rfl) ⟨1194872, by rfl⟩ : syracuseStep 1593163 = 2389745) B2389745
theorem B1593175 : Blo 1592995 1593175 := bstep (se 1 (by rfl) ⟨1194881, by rfl⟩ : syracuseStep 1593175 = 2389763) B2389763
theorem B1593195 : Blo 1592995 1593195 := bstep (se 1 (by rfl) ⟨1194896, by rfl⟩ : syracuseStep 1593195 = 2389793) B2389793
theorem B1593207 : Blo 1592995 1593207 := bstep (se 1 (by rfl) ⟨1194905, by rfl⟩ : syracuseStep 1593207 = 2389811) B2389811
theorem B6049667 : Blo 1592995 6049667 := bstep (se 1 (by rfl) ⟨4537250, by rfl⟩ : syracuseStep 6049667 = 9074501) B9074501
theorem B1593227 : Blo 1592995 1593227 := bstep (se 1 (by rfl) ⟨1194920, by rfl⟩ : syracuseStep 1593227 = 2389841) B2389841
theorem B1593239 : Blo 1592995 1593239 := bstep (se 1 (by rfl) ⟨1194929, by rfl⟩ : syracuseStep 1593239 = 2389859) B2389859
theorem B1593259 : Blo 1592995 1593259 := bstep (se 1 (by rfl) ⟨1194944, by rfl⟩ : syracuseStep 1593259 = 2389889) B2389889
theorem B1593271 : Blo 1592995 1593271 := bstep (se 1 (by rfl) ⟨1194953, by rfl⟩ : syracuseStep 1593271 = 2389907) B2389907
theorem B1593291 : Blo 1592995 1593291 := bstep (se 1 (by rfl) ⟨1194968, by rfl⟩ : syracuseStep 1593291 = 2389937) B2389937
theorem B1593303 : Blo 1592995 1593303 := bstep (se 1 (by rfl) ⟨1194977, by rfl⟩ : syracuseStep 1593303 = 2389955) B2389955
theorem B1593323 : Blo 1592995 1593323 := bstep (se 1 (by rfl) ⟨1194992, by rfl⟩ : syracuseStep 1593323 = 2389985) B2389985
theorem B1593335 : Blo 1592995 1593335 := bstep (se 1 (by rfl) ⟨1195001, by rfl⟩ : syracuseStep 1593335 = 2390003) B2390003
theorem B3026945 : Blo 1592995 3026945 := bstep (se 2 (by rfl) ⟨1135104, by rfl⟩ : syracuseStep 3026945 = 2270209) B2270209
theorem B1593355 : Blo 1592995 1593355 := bstep (se 1 (by rfl) ⟨1195016, by rfl⟩ : syracuseStep 1593355 = 2390033) B2390033
theorem B2691083 : Blo 1592995 2691083 := bstep (se 1 (by rfl) ⟨2018312, by rfl⟩ : syracuseStep 2691083 = 4036625) B4036625
theorem B1593367 : Blo 1592995 1593367 := bstep (se 1 (by rfl) ⟨1195025, by rfl⟩ : syracuseStep 1593367 = 2390051) B2390051
theorem B1593387 : Blo 1592995 1593387 := bstep (se 1 (by rfl) ⟨1195040, by rfl⟩ : syracuseStep 1593387 = 2390081) B2390081
theorem B1593399 : Blo 1592995 1593399 := bstep (se 1 (by rfl) ⟨1195049, by rfl⟩ : syracuseStep 1593399 = 2390099) B2390099
theorem B1593419 : Blo 1592995 1593419 := bstep (se 1 (by rfl) ⟨1195064, by rfl⟩ : syracuseStep 1593419 = 2390129) B2390129
theorem B8179787 : Blo 1592995 8179787 := bstep (se 1 (by rfl) ⟨6134840, by rfl⟩ : syracuseStep 8179787 = 12269681) B12269681
theorem B1593431 : Blo 1592995 1593431 := bstep (se 1 (by rfl) ⟨1195073, by rfl⟩ : syracuseStep 1593431 = 2390147) B2390147
theorem B1593451 : Blo 1592995 1593451 := bstep (se 1 (by rfl) ⟨1195088, by rfl⟩ : syracuseStep 1593451 = 2390177) B2390177
theorem B1593463 : Blo 1592995 1593463 := bstep (se 1 (by rfl) ⟨1195097, by rfl⟩ : syracuseStep 1593463 = 2390195) B2390195
theorem B2871425 : Blo 1592995 2871425 := bstep (se 2 (by rfl) ⟨1076784, by rfl⟩ : syracuseStep 2871425 = 2153569) B2153569
theorem B1593483 : Blo 1592995 1593483 := bstep (se 1 (by rfl) ⟨1195112, by rfl⟩ : syracuseStep 1593483 = 2390225) B2390225
theorem B2691211 : Blo 1592995 2691211 := bstep (se 1 (by rfl) ⟨2018408, by rfl⟩ : syracuseStep 2691211 = 4036817) B4036817
theorem B1593495 : Blo 1592995 1593495 := bstep (se 1 (by rfl) ⟨1195121, by rfl⟩ : syracuseStep 1593495 = 2390243) B2390243
theorem B4034711 : Blo 1592995 4034711 := bstep (se 1 (by rfl) ⟨3026033, by rfl⟩ : syracuseStep 4034711 = 6052067) B6052067
theorem B1593515 : Blo 1592995 1593515 := bstep (se 1 (by rfl) ⟨1195136, by rfl⟩ : syracuseStep 1593515 = 2390273) B2390273
theorem B1593527 : Blo 1592995 1593527 := bstep (se 1 (by rfl) ⟨1195145, by rfl⟩ : syracuseStep 1593527 = 2390291) B2390291
theorem B4845761 : Blo 1592995 4845761 := bstep (se 2 (by rfl) ⟨1817160, by rfl⟩ : syracuseStep 4845761 = 3634321) B3634321
theorem B1593547 : Blo 1592995 1593547 := bstep (se 1 (by rfl) ⟨1195160, by rfl⟩ : syracuseStep 1593547 = 2390321) B2390321
theorem B1593559 : Blo 1592995 1593559 := bstep (se 1 (by rfl) ⟨1195169, by rfl⟩ : syracuseStep 1593559 = 2390339) B2390339
theorem B1593579 : Blo 1592995 1593579 := bstep (se 1 (by rfl) ⟨1195184, by rfl⟩ : syracuseStep 1593579 = 2390369) B2390369
theorem B1593591 : Blo 1592995 1593591 := bstep (se 1 (by rfl) ⟨1195193, by rfl⟩ : syracuseStep 1593591 = 2390387) B2390387
theorem B3584267 : Blo 1592995 3584267 := bstep (se 1 (by rfl) ⟨2688200, by rfl⟩ : syracuseStep 3584267 = 5376401) B5376401
theorem B1593611 : Blo 1592995 1593611 := bstep (se 1 (by rfl) ⟨1195208, by rfl⟩ : syracuseStep 1593611 = 2390417) B2390417
theorem B1593623 : Blo 1592995 1593623 := bstep (se 1 (by rfl) ⟨1195217, by rfl⟩ : syracuseStep 1593623 = 2390435) B2390435
theorem B2552089 : Blo 1592995 2552089 := bstep (se 2 (by rfl) ⟨957033, by rfl⟩ : syracuseStep 2552089 = 1914067) B1914067
theorem B2691353 : Blo 1592995 2691353 := bstep (se 2 (by rfl) ⟨1009257, by rfl⟩ : syracuseStep 2691353 = 2018515) B2018515
theorem B1593643 : Blo 1592995 1593643 := bstep (se 1 (by rfl) ⟨1195232, by rfl⟩ : syracuseStep 1593643 = 2390465) B2390465
theorem B1593655 : Blo 1592995 1593655 := bstep (se 1 (by rfl) ⟨1195241, by rfl⟩ : syracuseStep 1593655 = 2390483) B2390483
theorem B3584321 : Blo 1592995 3584321 := bstep (se 2 (by rfl) ⟨1344120, by rfl⟩ : syracuseStep 3584321 = 2688241) B2688241
theorem B6050123 : Blo 1592995 6050123 := bstep (se 1 (by rfl) ⟨4537592, by rfl⟩ : syracuseStep 6050123 = 9075185) B9075185
theorem B1593675 : Blo 1592995 1593675 := bstep (se 1 (by rfl) ⟨1195256, by rfl⟩ : syracuseStep 1593675 = 2390513) B2390513
theorem B1593687 : Blo 1592995 1593687 := bstep (se 1 (by rfl) ⟨1195265, by rfl⟩ : syracuseStep 1593687 = 2390531) B2390531
theorem B3027287 : Blo 1592995 3027287 := bstep (se 1 (by rfl) ⟨2270465, by rfl⟩ : syracuseStep 3027287 = 4540931) B4540931
theorem B1593707 : Blo 1592995 1593707 := bstep (se 1 (by rfl) ⟨1195280, by rfl⟩ : syracuseStep 1593707 = 2390561) B2390561
theorem B1593719 : Blo 1592995 1593719 := bstep (se 1 (by rfl) ⟨1195289, by rfl⟩ : syracuseStep 1593719 = 2390579) B2390579
theorem B1593739 : Blo 1592995 1593739 := bstep (se 1 (by rfl) ⟨1195304, by rfl⟩ : syracuseStep 1593739 = 2390609) B2390609
theorem B1593751 : Blo 1592995 1593751 := bstep (se 1 (by rfl) ⟨1195313, by rfl⟩ : syracuseStep 1593751 = 2390627) B2390627
theorem B2691481 : Blo 1592995 2691481 := bstep (se 2 (by rfl) ⟨1009305, by rfl⟩ : syracuseStep 2691481 = 2018611) B2018611
theorem B1593771 : Blo 1592995 1593771 := bstep (se 1 (by rfl) ⟨1195328, by rfl⟩ : syracuseStep 1593771 = 2390657) B2390657
theorem B1593783 : Blo 1592995 1593783 := bstep (se 1 (by rfl) ⟨1195337, by rfl⟩ : syracuseStep 1593783 = 2390675) B2390675
theorem B5378507 : Blo 1592995 5378507 := bstep (se 1 (by rfl) ⟨4033880, by rfl⟩ : syracuseStep 5378507 = 8067761) B8067761
theorem B1593803 : Blo 1592995 1593803 := bstep (se 1 (by rfl) ⟨1195352, by rfl⟩ : syracuseStep 1593803 = 2390705) B2390705
theorem B1593815 : Blo 1592995 1593815 := bstep (se 1 (by rfl) ⟨1195361, by rfl⟩ : syracuseStep 1593815 = 2390723) B2390723
theorem B1593835 : Blo 1592995 1593835 := bstep (se 1 (by rfl) ⟨1195376, by rfl⟩ : syracuseStep 1593835 = 2390753) B2390753
theorem B1593847 : Blo 1592995 1593847 := bstep (se 1 (by rfl) ⟨1195385, by rfl⟩ : syracuseStep 1593847 = 2390771) B2390771
theorem B1593867 : Blo 1592995 1593867 := bstep (se 1 (by rfl) ⟨1195400, by rfl⟩ : syracuseStep 1593867 = 2390801) B2390801
theorem B6050321 : Blo 1592995 6050321 := bstep (se 2 (by rfl) ⟨2268870, by rfl⟩ : syracuseStep 6050321 = 4537741) B4537741
theorem B12440081 : Blo 1592995 12440081 := bstep (se 2 (by rfl) ⟨4665030, by rfl⟩ : syracuseStep 12440081 = 9330061) B9330061
theorem B1593879 : Blo 1592995 1593879 := bstep (se 1 (by rfl) ⟨1195409, by rfl⟩ : syracuseStep 1593879 = 2390819) B2390819
theorem B3584537 : Blo 1592995 3584537 := bstep (se 2 (by rfl) ⟨1344201, by rfl⟩ : syracuseStep 3584537 = 2688403) B2688403
theorem B1593899 : Blo 1592995 1593899 := bstep (se 1 (by rfl) ⟨1195424, by rfl⟩ : syracuseStep 1593899 = 2390849) B2390849
theorem B3232307 : Blo 1592995 3232307 := bstep (se 1 (by rfl) ⟨2424230, by rfl⟩ : syracuseStep 3232307 = 4848461) B4848461
theorem B1593911 : Blo 1592995 1593911 := bstep (se 1 (by rfl) ⟨1195433, by rfl⟩ : syracuseStep 1593911 = 2390867) B2390867
theorem B1593931 : Blo 1592995 1593931 := bstep (se 1 (by rfl) ⟨1195448, by rfl⟩ : syracuseStep 1593931 = 2390897) B2390897
theorem B1593943 : Blo 1592995 1593943 := bstep (se 1 (by rfl) ⟨1195457, by rfl⟩ : syracuseStep 1593943 = 2390915) B2390915
theorem B1593963 : Blo 1592995 1593963 := bstep (se 1 (by rfl) ⟨1195472, by rfl⟩ : syracuseStep 1593963 = 2390945) B2390945
theorem B3584627 : Blo 1592995 3584627 := bstep (se 1 (by rfl) ⟨2688470, by rfl⟩ : syracuseStep 3584627 = 5376941) B5376941
theorem B1593975 : Blo 1592995 1593975 := bstep (se 1 (by rfl) ⟨1195481, by rfl⟩ : syracuseStep 1593975 = 2390963) B2390963
theorem B1593995 : Blo 1592995 1593995 := bstep (se 1 (by rfl) ⟨1195496, by rfl⟩ : syracuseStep 1593995 = 2390993) B2390993
theorem B3584663 : Blo 1592995 3584663 := bstep (se 1 (by rfl) ⟨2688497, by rfl⟩ : syracuseStep 3584663 = 5376995) B5376995
theorem B1594007 : Blo 1592995 1594007 := bstep (se 1 (by rfl) ⟨1195505, by rfl⟩ : syracuseStep 1594007 = 2391011) B2391011
theorem B1594027 : Blo 1592995 1594027 := bstep (se 1 (by rfl) ⟨1195520, by rfl⟩ : syracuseStep 1594027 = 2391041) B2391041
theorem B1594039 : Blo 1592995 1594039 := bstep (se 1 (by rfl) ⟨1195529, by rfl⟩ : syracuseStep 1594039 = 2391059) B2391059
theorem B1594059 : Blo 1592995 1594059 := bstep (se 1 (by rfl) ⟨1195544, by rfl⟩ : syracuseStep 1594059 = 2391089) B2391089
theorem B1594071 : Blo 1592995 1594071 := bstep (se 1 (by rfl) ⟨1195553, by rfl⟩ : syracuseStep 1594071 = 2391107) B2391107
theorem B2552537 : Blo 1592995 2552537 := bstep (se 2 (by rfl) ⟨957201, by rfl⟩ : syracuseStep 2552537 = 1914403) B1914403
theorem B5378777 : Blo 1592995 5378777 := bstep (se 2 (by rfl) ⟨2017041, by rfl⟩ : syracuseStep 5378777 = 4034083) B4034083
theorem B1594091 : Blo 1592995 1594091 := bstep (se 1 (by rfl) ⟨1195568, by rfl⟩ : syracuseStep 1594091 = 2391137) B2391137
theorem B1594103 : Blo 1592995 1594103 := bstep (se 1 (by rfl) ⟨1195577, by rfl⟩ : syracuseStep 1594103 = 2391155) B2391155
theorem B1594123 : Blo 1592995 1594123 := bstep (se 1 (by rfl) ⟨1195592, by rfl⟩ : syracuseStep 1594123 = 2391185) B2391185
theorem B1594135 : Blo 1592995 1594135 := bstep (se 1 (by rfl) ⟨1195601, by rfl⟩ : syracuseStep 1594135 = 2391203) B2391203
theorem B1594155 : Blo 1592995 1594155 := bstep (se 1 (by rfl) ⟨1195616, by rfl⟩ : syracuseStep 1594155 = 2391233) B2391233
theorem B6902579 : Blo 1592995 6902579 := bstep (se 1 (by rfl) ⟨5176934, by rfl⟩ : syracuseStep 6902579 = 10353869) B10353869
theorem B4035379 : Blo 1592995 4035379 := bstep (se 1 (by rfl) ⟨3026534, by rfl⟩ : syracuseStep 4035379 = 6053069) B6053069
theorem B1594167 : Blo 1592995 1594167 := bstep (se 1 (by rfl) ⟨1195625, by rfl⟩ : syracuseStep 1594167 = 2391251) B2391251
theorem B3584843 : Blo 1592995 3584843 := bstep (se 1 (by rfl) ⟨2688632, by rfl⟩ : syracuseStep 3584843 = 5377265) B5377265
theorem B1594187 : Blo 1592995 1594187 := bstep (se 1 (by rfl) ⟨1195640, by rfl⟩ : syracuseStep 1594187 = 2391281) B2391281
theorem B1594199 : Blo 1592995 1594199 := bstep (se 1 (by rfl) ⟨1195649, by rfl⟩ : syracuseStep 1594199 = 2391299) B2391299
theorem B29487971 : Blo 1592995 29487971 := bstep (se 1 (by rfl) ⟨22115978, by rfl⟩ : syracuseStep 29487971 = 44231957) B44231957
theorem B1594219 : Blo 1592995 1594219 := bstep (se 1 (by rfl) ⟨1195664, by rfl⟩ : syracuseStep 1594219 = 2391329) B2391329
theorem B1594231 : Blo 1592995 1594231 := bstep (se 1 (by rfl) ⟨1195673, by rfl⟩ : syracuseStep 1594231 = 2391347) B2391347
theorem B3584897 : Blo 1592995 3584897 := bstep (se 2 (by rfl) ⟨1344336, by rfl⟩ : syracuseStep 3584897 = 2688673) B2688673
theorem B1594251 : Blo 1592995 1594251 := bstep (se 1 (by rfl) ⟨1195688, by rfl⟩ : syracuseStep 1594251 = 2391377) B2391377
theorem B1594263 : Blo 1592995 1594263 := bstep (se 1 (by rfl) ⟨1195697, by rfl⟩ : syracuseStep 1594263 = 2391395) B2391395
theorem B1594283 : Blo 1592995 1594283 := bstep (se 1 (by rfl) ⟨1195712, by rfl⟩ : syracuseStep 1594283 = 2391425) B2391425
theorem B1594295 : Blo 1592995 1594295 := bstep (se 1 (by rfl) ⟨1195721, by rfl⟩ : syracuseStep 1594295 = 2391443) B2391443
theorem B4035521 : Blo 1592995 4035521 := bstep (se 2 (by rfl) ⟨1513320, by rfl⟩ : syracuseStep 4035521 = 3026641) B3026641
theorem B1594315 : Blo 1592995 1594315 := bstep (se 1 (by rfl) ⟨1195736, by rfl⟩ : syracuseStep 1594315 = 2391473) B2391473
theorem B1594327 : Blo 1592995 1594327 := bstep (se 1 (by rfl) ⟨1195745, by rfl⟩ : syracuseStep 1594327 = 2391491) B2391491
theorem B1594347 : Blo 1592995 1594347 := bstep (se 1 (by rfl) ⟨1195760, by rfl⟩ : syracuseStep 1594347 = 2391521) B2391521
theorem B3027955 : Blo 1592995 3027955 := bstep (se 1 (by rfl) ⟨2270966, by rfl⟩ : syracuseStep 3027955 = 4541933) B4541933
theorem B1594359 : Blo 1592995 1594359 := bstep (se 1 (by rfl) ⟨1195769, by rfl⟩ : syracuseStep 1594359 = 2391539) B2391539
theorem B1594379 : Blo 1592995 1594379 := bstep (se 1 (by rfl) ⟨1195784, by rfl⟩ : syracuseStep 1594379 = 2391569) B2391569
theorem B9827345 : Blo 1592995 9827345 := bstep (se 2 (by rfl) ⟨3685254, by rfl⟩ : syracuseStep 9827345 = 7370509) B7370509
theorem B1594391 : Blo 1592995 1594391 := bstep (se 1 (by rfl) ⟨1195793, by rfl⟩ : syracuseStep 1594391 = 2391587) B2391587
theorem B1594411 : Blo 1592995 1594411 := bstep (se 1 (by rfl) ⟨1195808, by rfl⟩ : syracuseStep 1594411 = 2391617) B2391617
theorem B1594423 : Blo 1592995 1594423 := bstep (se 1 (by rfl) ⟨1195817, by rfl⟩ : syracuseStep 1594423 = 2391635) B2391635
theorem B1594443 : Blo 1592995 1594443 := bstep (se 1 (by rfl) ⟨1195832, by rfl⟩ : syracuseStep 1594443 = 2391665) B2391665
theorem B1594455 : Blo 1592995 1594455 := bstep (se 1 (by rfl) ⟨1195841, by rfl⟩ : syracuseStep 1594455 = 2391683) B2391683
theorem B3585113 : Blo 1592995 3585113 := bstep (se 2 (by rfl) ⟨1344417, by rfl⟩ : syracuseStep 3585113 = 2688835) B2688835
theorem B8066141 : Blo 1592995 8066141 := bstep (se 3 (by rfl) ⟨1512401, by rfl⟩ : syracuseStep 8066141 = 3024803) B3024803
theorem B1594475 : Blo 1592995 1594475 := bstep (se 1 (by rfl) ⟨1195856, by rfl⟩ : syracuseStep 1594475 = 2391713) B2391713
theorem B1594487 : Blo 1592995 1594487 := bstep (se 1 (by rfl) ⟨1195865, by rfl⟩ : syracuseStep 1594487 = 2391731) B2391731
theorem B1594507 : Blo 1592995 1594507 := bstep (se 1 (by rfl) ⟨1195880, by rfl⟩ : syracuseStep 1594507 = 2391761) B2391761
theorem B2725015 : Blo 1592995 2725015 := bstep (se 1 (by rfl) ⟨2043761, by rfl⟩ : syracuseStep 2725015 = 4087523) B4087523
theorem B1594519 : Blo 1592995 1594519 := bstep (se 1 (by rfl) ⟨1195889, by rfl⟩ : syracuseStep 1594519 = 2391779) B2391779
theorem B1594539 : Blo 1592995 1594539 := bstep (se 1 (by rfl) ⟨1195904, by rfl⟩ : syracuseStep 1594539 = 2391809) B2391809
theorem B3585203 : Blo 1592995 3585203 := bstep (se 1 (by rfl) ⟨2688902, by rfl⟩ : syracuseStep 3585203 = 5377805) B5377805
theorem B1594551 : Blo 1592995 1594551 := bstep (se 1 (by rfl) ⟨1195913, by rfl⟩ : syracuseStep 1594551 = 2391827) B2391827
theorem B1594571 : Blo 1592995 1594571 := bstep (se 1 (by rfl) ⟨1195928, by rfl⟩ : syracuseStep 1594571 = 2391857) B2391857
theorem B3585239 : Blo 1592995 3585239 := bstep (se 1 (by rfl) ⟨2688929, by rfl⟩ : syracuseStep 3585239 = 5377859) B5377859
theorem B1594583 : Blo 1592995 1594583 := bstep (se 1 (by rfl) ⟨1195937, by rfl⟩ : syracuseStep 1594583 = 2391875) B2391875
theorem B1594603 : Blo 1592995 1594603 := bstep (se 1 (by rfl) ⟨1195952, by rfl⟩ : syracuseStep 1594603 = 2391905) B2391905
theorem B1594615 : Blo 1592995 1594615 := bstep (se 1 (by rfl) ⟨1195961, by rfl⟩ : syracuseStep 1594615 = 2391923) B2391923
theorem B20428037 : Blo 1592995 20428037 := bstep (se 4 (by rfl) ⟨1915128, by rfl⟩ : syracuseStep 20428037 = 3830257) B3830257
theorem B1594635 : Blo 1592995 1594635 := bstep (se 1 (by rfl) ⟨1195976, by rfl⟩ : syracuseStep 1594635 = 2391953) B2391953
theorem B6051095 : Blo 1592995 6051095 := bstep (se 1 (by rfl) ⟨4538321, by rfl⟩ : syracuseStep 6051095 = 9076643) B9076643
theorem B1594647 : Blo 1592995 1594647 := bstep (se 1 (by rfl) ⟨1195985, by rfl⟩ : syracuseStep 1594647 = 2391971) B2391971
theorem B1594667 : Blo 1592995 1594667 := bstep (se 1 (by rfl) ⟨1196000, by rfl⟩ : syracuseStep 1594667 = 2392001) B2392001
theorem B1594679 : Blo 1592995 1594679 := bstep (se 1 (by rfl) ⟨1196009, by rfl⟩ : syracuseStep 1594679 = 2392019) B2392019
theorem B1594699 : Blo 1592995 1594699 := bstep (se 1 (by rfl) ⟨1196024, by rfl⟩ : syracuseStep 1594699 = 2392049) B2392049
theorem B2725207 : Blo 1592995 2725207 := bstep (se 1 (by rfl) ⟨2043905, by rfl⟩ : syracuseStep 2725207 = 4087811) B4087811
theorem B1594711 : Blo 1592995 1594711 := bstep (se 1 (by rfl) ⟨1196033, by rfl⟩ : syracuseStep 1594711 = 2392067) B2392067
theorem B1594731 : Blo 1592995 1594731 := bstep (se 1 (by rfl) ⟨1196048, by rfl⟩ : syracuseStep 1594731 = 2392097) B2392097
theorem B1594743 : Blo 1592995 1594743 := bstep (se 1 (by rfl) ⟨1196057, by rfl⟩ : syracuseStep 1594743 = 2392115) B2392115
theorem B3585419 : Blo 1592995 3585419 := bstep (se 1 (by rfl) ⟨2689064, by rfl⟩ : syracuseStep 3585419 = 5378129) B5378129
theorem B1594763 : Blo 1592995 1594763 := bstep (se 1 (by rfl) ⟨1196072, by rfl⟩ : syracuseStep 1594763 = 2392145) B2392145
theorem B5379479 : Blo 1592995 5379479 := bstep (se 1 (by rfl) ⟨4034609, by rfl⟩ : syracuseStep 5379479 = 8069219) B8069219
theorem B1594775 : Blo 1592995 1594775 := bstep (se 1 (by rfl) ⟨1196081, by rfl⟩ : syracuseStep 1594775 = 2392163) B2392163
theorem B1594795 : Blo 1592995 1594795 := bstep (se 1 (by rfl) ⟨1196096, by rfl⟩ : syracuseStep 1594795 = 2392193) B2392193
theorem B1594807 : Blo 1592995 1594807 := bstep (se 1 (by rfl) ⟨1196105, by rfl⟩ : syracuseStep 1594807 = 2392211) B2392211
theorem B3585473 : Blo 1592995 3585473 := bstep (se 2 (by rfl) ⟨1344552, by rfl⟩ : syracuseStep 3585473 = 2689105) B2689105
theorem B1594827 : Blo 1592995 1594827 := bstep (se 1 (by rfl) ⟨1196120, by rfl⟩ : syracuseStep 1594827 = 2392241) B2392241
theorem B1594839 : Blo 1592995 1594839 := bstep (se 1 (by rfl) ⟨1196129, by rfl⟩ : syracuseStep 1594839 = 2392259) B2392259
theorem B6051293 : Blo 1592995 6051293 := bstep (se 3 (by rfl) ⟨1134617, by rfl⟩ : syracuseStep 6051293 = 2269235) B2269235
theorem B1594859 : Blo 1592995 1594859 := bstep (se 1 (by rfl) ⟨1196144, by rfl⟩ : syracuseStep 1594859 = 2392289) B2392289
theorem B1594871 : Blo 1592995 1594871 := bstep (se 1 (by rfl) ⟨1196153, by rfl⟩ : syracuseStep 1594871 = 2392307) B2392307
theorem B1594891 : Blo 1592995 1594891 := bstep (se 1 (by rfl) ⟨1196168, by rfl⟩ : syracuseStep 1594891 = 2392337) B2392337
theorem B1594903 : Blo 1592995 1594903 := bstep (se 1 (by rfl) ⟨1196177, by rfl⟩ : syracuseStep 1594903 = 2392355) B2392355
theorem B2389529 : Blo 1592995 2389529 := bstep (se 2 (by rfl) ⟨896073, by rfl⟩ : syracuseStep 2389529 = 1792147) B1792147
theorem B1594923 : Blo 1592995 1594923 := bstep (se 1 (by rfl) ⟨1196192, by rfl⟩ : syracuseStep 1594923 = 2392385) B2392385
theorem B6460979 : Blo 1592995 6460979 := bstep (se 1 (by rfl) ⟨4845734, by rfl⟩ : syracuseStep 6460979 = 9691469) B9691469
theorem B1594935 : Blo 1592995 1594935 := bstep (se 1 (by rfl) ⟨1196201, by rfl⟩ : syracuseStep 1594935 = 2392403) B2392403
theorem B7763531 : Blo 1592995 7763531 := bstep (se 1 (by rfl) ⟨5822648, by rfl⟩ : syracuseStep 7763531 = 11645297) B11645297
theorem B1594955 : Blo 1592995 1594955 := bstep (se 1 (by rfl) ⟨1196216, by rfl⟩ : syracuseStep 1594955 = 2392433) B2392433
theorem B1594967 : Blo 1592995 1594967 := bstep (se 1 (by rfl) ⟨1196225, by rfl⟩ : syracuseStep 1594967 = 2392451) B2392451
theorem B1594987 : Blo 1592995 1594987 := bstep (se 1 (by rfl) ⟨1196240, by rfl⟩ : syracuseStep 1594987 = 2392481) B2392481
theorem B2389643 : Blo 1592995 2389643 := bstep (se 1 (by rfl) ⟨1792232, by rfl⟩ : syracuseStep 2389643 = 3584465) B3584465
theorem B2389655 : Blo 1592995 2389655 := bstep (se 1 (by rfl) ⟨1792241, by rfl⟩ : syracuseStep 2389655 = 3584483) B3584483
theorem B3585689 : Blo 1592995 3585689 := bstep (se 2 (by rfl) ⟨1344633, by rfl⟩ : syracuseStep 3585689 = 2689267) B2689267
theorem B2389721 : Blo 1592995 2389721 := bstep (se 2 (by rfl) ⟨896145, by rfl⟩ : syracuseStep 2389721 = 1792291) B1792291
theorem B3585779 : Blo 1592995 3585779 := bstep (se 1 (by rfl) ⟨2689334, by rfl⟩ : syracuseStep 3585779 = 5378669) B5378669
theorem B3405569 : Blo 1592995 3405569 := bstep (se 2 (by rfl) ⟨1277088, by rfl⟩ : syracuseStep 3405569 = 2554177) B2554177
theorem B3585815 : Blo 1592995 3585815 := bstep (se 1 (by rfl) ⟨2689361, by rfl⟩ : syracuseStep 3585815 = 5378723) B5378723
theorem B2389835 : Blo 1592995 2389835 := bstep (se 1 (by rfl) ⟨1792376, by rfl⟩ : syracuseStep 2389835 = 3584753) B3584753
theorem B2389847 : Blo 1592995 2389847 := bstep (se 1 (by rfl) ⟨1792385, by rfl⟩ : syracuseStep 2389847 = 3584771) B3584771
theorem B3405655 : Blo 1592995 3405655 := bstep (se 1 (by rfl) ⟨2554241, by rfl⟩ : syracuseStep 3405655 = 5108483) B5108483
theorem B2389913 : Blo 1592995 2389913 := bstep (se 2 (by rfl) ⟨896217, by rfl⟩ : syracuseStep 2389913 = 1792435) B1792435
theorem B5380019 : Blo 1592995 5380019 := bstep (se 1 (by rfl) ⟨4035014, by rfl⟩ : syracuseStep 5380019 = 8070029) B8070029
theorem B3585995 : Blo 1592995 3585995 := bstep (se 1 (by rfl) ⟨2689496, by rfl⟩ : syracuseStep 3585995 = 5378993) B5378993
theorem B2873291 : Blo 1592995 2873291 := bstep (se 1 (by rfl) ⟨2154968, by rfl⟩ : syracuseStep 2873291 = 4309937) B4309937
theorem B3586049 : Blo 1592995 3586049 := bstep (se 2 (by rfl) ⟨1344768, by rfl⟩ : syracuseStep 3586049 = 2689537) B2689537
theorem B2390027 : Blo 1592995 2390027 := bstep (se 1 (by rfl) ⟨1792520, by rfl⟩ : syracuseStep 2390027 = 3585041) B3585041
theorem B2390039 : Blo 1592995 2390039 := bstep (se 1 (by rfl) ⟨1792529, by rfl⟩ : syracuseStep 2390039 = 3585059) B3585059
theorem B12105773 : Blo 1592995 12105773 := bstep (se 3 (by rfl) ⟨2269832, by rfl⟩ : syracuseStep 12105773 = 4539665) B4539665
theorem B9074753 : Blo 1592995 9074753 := bstep (se 2 (by rfl) ⟨3403032, by rfl⟩ : syracuseStep 9074753 = 6806065) B6806065
theorem B2390105 : Blo 1592995 2390105 := bstep (se 2 (by rfl) ⟨896289, by rfl⟩ : syracuseStep 2390105 = 1792579) B1792579
theorem B4536499 : Blo 1592995 4536499 := bstep (se 1 (by rfl) ⟨3402374, by rfl⟩ : syracuseStep 4536499 = 6804749) B6804749
theorem B1792183 : Blo 1592995 1792183 := bstep (se 1 (by rfl) ⟨1344137, by rfl⟩ : syracuseStep 1792183 = 2688275) B2688275
theorem B9328819 : Blo 1592995 9328819 := bstep (se 1 (by rfl) ⟨6996614, by rfl⟩ : syracuseStep 9328819 = 13993229) B13993229
theorem B4036787 : Blo 1592995 4036787 := bstep (se 1 (by rfl) ⟨3027590, by rfl⟩ : syracuseStep 4036787 = 6055181) B6055181
theorem B5380289 : Blo 1592995 5380289 := bstep (se 2 (by rfl) ⟨2017608, by rfl⟩ : syracuseStep 5380289 = 4035217) B4035217
theorem B2390219 : Blo 1592995 2390219 := bstep (se 1 (by rfl) ⟨1792664, by rfl⟩ : syracuseStep 2390219 = 3585329) B3585329
theorem B2390231 : Blo 1592995 2390231 := bstep (se 1 (by rfl) ⟨1792673, by rfl⟩ : syracuseStep 2390231 = 3585347) B3585347
theorem B3586265 : Blo 1592995 3586265 := bstep (se 2 (by rfl) ⟨1344849, by rfl⟩ : syracuseStep 3586265 = 2689699) B2689699
theorem B9828625 : Blo 1592995 9828625 := bstep (se 2 (by rfl) ⟨3685734, by rfl⟩ : syracuseStep 9828625 = 7371469) B7371469
theorem B2390297 : Blo 1592995 2390297 := bstep (se 2 (by rfl) ⟨896361, by rfl⟩ : syracuseStep 2390297 = 1792723) B1792723
theorem B20420909 : Blo 1592995 20420909 := bstep (se 3 (by rfl) ⟨3828920, by rfl⟩ : syracuseStep 20420909 = 7657841) B7657841
theorem B3586355 : Blo 1592995 3586355 := bstep (se 1 (by rfl) ⟨2689766, by rfl⟩ : syracuseStep 3586355 = 5379533) B5379533
theorem B3586391 : Blo 1592995 3586391 := bstep (se 1 (by rfl) ⟨2689793, by rfl⟩ : syracuseStep 3586391 = 5379587) B5379587
theorem B3635543 : Blo 1592995 3635543 := bstep (se 1 (by rfl) ⟨2726657, by rfl⟩ : syracuseStep 3635543 = 5453315) B5453315
theorem B1792363 : Blo 1592995 1792363 := bstep (se 1 (by rfl) ⟨1344272, by rfl⟩ : syracuseStep 1792363 = 2688545) B2688545
theorem B2390411 : Blo 1592995 2390411 := bstep (se 1 (by rfl) ⟨1792808, by rfl⟩ : syracuseStep 2390411 = 3585617) B3585617
theorem B2390423 : Blo 1592995 2390423 := bstep (se 1 (by rfl) ⟨1792817, by rfl⟩ : syracuseStep 2390423 = 3585635) B3585635
theorem B12097997 : Blo 1592995 12097997 := bstep (se 3 (by rfl) ⟨2268374, by rfl⟩ : syracuseStep 12097997 = 4536749) B4536749
theorem B1792471 : Blo 1592995 1792471 := bstep (se 1 (by rfl) ⟨1344353, by rfl⟩ : syracuseStep 1792471 = 2688707) B2688707
theorem B2390489 : Blo 1592995 2390489 := bstep (se 2 (by rfl) ⟨896433, by rfl⟩ : syracuseStep 2390489 = 1792867) B1792867
theorem B3586571 : Blo 1592995 3586571 := bstep (se 1 (by rfl) ⟨2689928, by rfl⟩ : syracuseStep 3586571 = 5379857) B5379857
theorem B6806081 : Blo 1592995 6806081 := bstep (se 2 (by rfl) ⟨2552280, by rfl⟩ : syracuseStep 6806081 = 5104561) B5104561
theorem B3586625 : Blo 1592995 3586625 := bstep (se 2 (by rfl) ⟨1344984, by rfl⟩ : syracuseStep 3586625 = 2689969) B2689969
theorem B2390603 : Blo 1592995 2390603 := bstep (se 1 (by rfl) ⟨1792952, by rfl⟩ : syracuseStep 2390603 = 3585905) B3585905
theorem B2390615 : Blo 1592995 2390615 := bstep (se 1 (by rfl) ⟨1792961, by rfl⟩ : syracuseStep 2390615 = 3585923) B3585923
theorem B8616541 : Blo 1592995 8616541 := bstep (se 3 (by rfl) ⟨1615601, by rfl⟩ : syracuseStep 8616541 = 3231203) B3231203
theorem B1792651 : Blo 1592995 1792651 := bstep (se 1 (by rfl) ⟨1344488, by rfl⟩ : syracuseStep 1792651 = 2688977) B2688977
theorem B3406475 : Blo 1592995 3406475 := bstep (se 1 (by rfl) ⟨2554856, by rfl⟩ : syracuseStep 3406475 = 5109713) B5109713
theorem B2423447 : Blo 1592995 2423447 := bstep (se 1 (by rfl) ⟨1817585, by rfl⟩ : syracuseStep 2423447 = 3635171) B3635171
theorem B2390681 : Blo 1592995 2390681 := bstep (se 2 (by rfl) ⟨896505, by rfl⟩ : syracuseStep 2390681 = 1793011) B1793011
theorem B4037323 : Blo 1592995 4037323 := bstep (se 1 (by rfl) ⟨3027992, by rfl⟩ : syracuseStep 4037323 = 6055985) B6055985
theorem B2726617 : Blo 1592995 2726617 := bstep (se 2 (by rfl) ⟨1022481, by rfl⟩ : syracuseStep 2726617 = 2044963) B2044963
theorem B5380829 : Blo 1592995 5380829 := bstep (se 3 (by rfl) ⟨1008905, by rfl⟩ : syracuseStep 5380829 = 2017811) B2017811
theorem B1792759 : Blo 1592995 1792759 := bstep (se 1 (by rfl) ⟨1344569, by rfl⟩ : syracuseStep 1792759 = 2689139) B2689139
theorem B2390795 : Blo 1592995 2390795 := bstep (se 1 (by rfl) ⟨1793096, by rfl⟩ : syracuseStep 2390795 = 3586193) B3586193
theorem B2390807 : Blo 1592995 2390807 := bstep (se 1 (by rfl) ⟨1793105, by rfl⟩ : syracuseStep 2390807 = 3586211) B3586211
theorem B3586841 : Blo 1592995 3586841 := bstep (se 2 (by rfl) ⟨1345065, by rfl⟩ : syracuseStep 3586841 = 2690131) B2690131
theorem B5741363 : Blo 1592995 5741363 := bstep (se 1 (by rfl) ⟨4306022, by rfl⟩ : syracuseStep 5741363 = 8612045) B8612045
theorem B2390873 : Blo 1592995 2390873 := bstep (se 2 (by rfl) ⟨896577, by rfl⟩ : syracuseStep 2390873 = 1793155) B1793155
theorem B3152729 : Blo 1592995 3152729 := bstep (se 2 (by rfl) ⟨1182273, by rfl⟩ : syracuseStep 3152729 = 2364547) B2364547
theorem B3586931 : Blo 1592995 3586931 := bstep (se 1 (by rfl) ⟨2690198, by rfl⟩ : syracuseStep 3586931 = 5380397) B5380397
theorem B6806423 : Blo 1592995 6806423 := bstep (se 1 (by rfl) ⟨5104817, by rfl⟩ : syracuseStep 6806423 = 10209635) B10209635
theorem B3586967 : Blo 1592995 3586967 := bstep (se 1 (by rfl) ⟨2690225, by rfl⟩ : syracuseStep 3586967 = 5380451) B5380451
theorem B1792939 : Blo 1592995 1792939 := bstep (se 1 (by rfl) ⟨1344704, by rfl⟩ : syracuseStep 1792939 = 2689409) B2689409
theorem B12098483 : Blo 1592995 12098483 := bstep (se 1 (by rfl) ⟨9073862, by rfl⟩ : syracuseStep 12098483 = 18147725) B18147725
theorem B2390987 : Blo 1592995 2390987 := bstep (se 1 (by rfl) ⟨1793240, by rfl⟩ : syracuseStep 2390987 = 3586481) B3586481
theorem B2390999 : Blo 1592995 2390999 := bstep (se 1 (by rfl) ⟨1793249, by rfl⟩ : syracuseStep 2390999 = 3586499) B3586499
theorem B1793047 : Blo 1592995 1793047 := bstep (se 1 (by rfl) ⟨1344785, by rfl⟩ : syracuseStep 1793047 = 2689571) B2689571
theorem B2391065 : Blo 1592995 2391065 := bstep (se 2 (by rfl) ⟨896649, by rfl⟩ : syracuseStep 2391065 = 1793299) B1793299
theorem B3882049 : Blo 1592995 3882049 := bstep (se 2 (by rfl) ⟨1455768, by rfl⟩ : syracuseStep 3882049 = 2911537) B2911537
theorem B3587147 : Blo 1592995 3587147 := bstep (se 1 (by rfl) ⟨2690360, by rfl⟩ : syracuseStep 3587147 = 5380721) B5380721
theorem B1915979 : Blo 1592995 1915979 := bstep (se 1 (by rfl) ⟨1436984, by rfl⟩ : syracuseStep 1915979 = 2873969) B2873969
theorem B4537433 : Blo 1592995 4537433 := bstep (se 2 (by rfl) ⟨1701537, by rfl⟩ : syracuseStep 4537433 = 3403075) B3403075
theorem B3587201 : Blo 1592995 3587201 := bstep (se 2 (by rfl) ⟨1345200, by rfl⟩ : syracuseStep 3587201 = 2690401) B2690401
theorem B2391179 : Blo 1592995 2391179 := bstep (se 1 (by rfl) ⟨1793384, by rfl⟩ : syracuseStep 2391179 = 3586769) B3586769
theorem B8068247 : Blo 1592995 8068247 := bstep (se 1 (by rfl) ⟨6051185, by rfl⟩ : syracuseStep 8068247 = 12102371) B12102371
theorem B2391191 : Blo 1592995 2391191 := bstep (se 1 (by rfl) ⟨1793393, by rfl⟩ : syracuseStep 2391191 = 3586787) B3586787
theorem B1793227 : Blo 1592995 1793227 := bstep (se 1 (by rfl) ⟨1344920, by rfl⟩ : syracuseStep 1793227 = 2689841) B2689841
theorem B4308185 : Blo 1592995 4308185 := bstep (se 2 (by rfl) ⟨1615569, by rfl⟩ : syracuseStep 4308185 = 3231139) B3231139
theorem B2391257 : Blo 1592995 2391257 := bstep (se 2 (by rfl) ⟨896721, by rfl⟩ : syracuseStep 2391257 = 1793443) B1793443
theorem B1793335 : Blo 1592995 1793335 := bstep (se 1 (by rfl) ⟨1345001, by rfl⟩ : syracuseStep 1793335 = 2690003) B2690003
theorem B2391371 : Blo 1592995 2391371 := bstep (se 1 (by rfl) ⟨1793528, by rfl⟩ : syracuseStep 2391371 = 3587057) B3587057
theorem B2391383 : Blo 1592995 2391383 := bstep (se 1 (by rfl) ⟨1793537, by rfl⟩ : syracuseStep 2391383 = 3587075) B3587075
theorem B3587417 : Blo 1592995 3587417 := bstep (se 2 (by rfl) ⟨1345281, by rfl⟩ : syracuseStep 3587417 = 2690563) B2690563
theorem B6053251 : Blo 1592995 6053251 := bstep (se 1 (by rfl) ⟨4539938, by rfl⟩ : syracuseStep 6053251 = 9079877) B9079877
theorem B2391449 : Blo 1592995 2391449 := bstep (se 2 (by rfl) ⟨896793, by rfl⟩ : syracuseStep 2391449 = 1793587) B1793587
theorem B3587507 : Blo 1592995 3587507 := bstep (se 1 (by rfl) ⟨2690630, by rfl⟩ : syracuseStep 3587507 = 5381261) B5381261
theorem B9829811 : Blo 1592995 9829811 := bstep (se 1 (by rfl) ⟨7372358, by rfl⟩ : syracuseStep 9829811 = 14744717) B14744717
theorem B3587543 : Blo 1592995 3587543 := bstep (se 1 (by rfl) ⟨2690657, by rfl⟩ : syracuseStep 3587543 = 5381315) B5381315
theorem B4603357 : Blo 1592995 4603357 := bstep (se 3 (by rfl) ⟨863129, by rfl⟩ : syracuseStep 4603357 = 1726259) B1726259
theorem B1793515 : Blo 1592995 1793515 := bstep (se 1 (by rfl) ⟨1345136, by rfl⟩ : syracuseStep 1793515 = 2690273) B2690273
theorem B2391563 : Blo 1592995 2391563 := bstep (se 1 (by rfl) ⟨1793672, by rfl⟩ : syracuseStep 2391563 = 3587345) B3587345
theorem B37330445 : Blo 1592995 37330445 := bstep (se 3 (by rfl) ⟨6999458, by rfl⟩ : syracuseStep 37330445 = 13998917) B13998917
theorem B2391575 : Blo 1592995 2391575 := bstep (se 1 (by rfl) ⟨1793681, by rfl⟩ : syracuseStep 2391575 = 3587363) B3587363
theorem B11058763 : Blo 1592995 11058763 := bstep (se 1 (by rfl) ⟨8294072, by rfl⟩ : syracuseStep 11058763 = 16588145) B16588145
theorem B1793623 : Blo 1592995 1793623 := bstep (se 1 (by rfl) ⟨1345217, by rfl⟩ : syracuseStep 1793623 = 2690435) B2690435
theorem B2391641 : Blo 1592995 2391641 := bstep (se 2 (by rfl) ⟨896865, by rfl⟩ : syracuseStep 2391641 = 1793731) B1793731
theorem B3587723 : Blo 1592995 3587723 := bstep (se 1 (by rfl) ⟨2690792, by rfl⟩ : syracuseStep 3587723 = 5381585) B5381585
theorem B6053555 : Blo 1592995 6053555 := bstep (se 1 (by rfl) ⟨4540166, by rfl⟩ : syracuseStep 6053555 = 9080333) B9080333
theorem B3587777 : Blo 1592995 3587777 := bstep (se 2 (by rfl) ⟨1345416, by rfl⟩ : syracuseStep 3587777 = 2690833) B2690833
theorem B2391755 : Blo 1592995 2391755 := bstep (se 1 (by rfl) ⟨1793816, by rfl⟩ : syracuseStep 2391755 = 3587633) B3587633
theorem B2391767 : Blo 1592995 2391767 := bstep (se 1 (by rfl) ⟨1793825, by rfl⟩ : syracuseStep 2391767 = 3587651) B3587651
theorem B1793803 : Blo 1592995 1793803 := bstep (se 1 (by rfl) ⟨1345352, by rfl⟩ : syracuseStep 1793803 = 2690705) B2690705
theorem B2391833 : Blo 1592995 2391833 := bstep (se 2 (by rfl) ⟨896937, by rfl⟩ : syracuseStep 2391833 = 1793875) B1793875
theorem B6807347 : Blo 1592995 6807347 := bstep (se 1 (by rfl) ⟨5105510, by rfl⟩ : syracuseStep 6807347 = 10211021) B10211021
theorem B5381963 : Blo 1592995 5381963 := bstep (se 1 (by rfl) ⟨4036472, by rfl⟩ : syracuseStep 5381963 = 8072945) B8072945
theorem B1793911 : Blo 1592995 1793911 := bstep (se 1 (by rfl) ⟨1345433, by rfl⟩ : syracuseStep 1793911 = 2690867) B2690867
theorem B2391947 : Blo 1592995 2391947 := bstep (se 1 (by rfl) ⟨1793960, by rfl⟩ : syracuseStep 2391947 = 3587921) B3587921
theorem B2391959 : Blo 1592995 2391959 := bstep (se 1 (by rfl) ⟨1793969, by rfl⟩ : syracuseStep 2391959 = 3587939) B3587939
theorem B2269081 : Blo 1592995 2269081 := bstep (se 2 (by rfl) ⟨850905, by rfl⟩ : syracuseStep 2269081 = 1701811) B1701811
theorem B3587993 : Blo 1592995 3587993 := bstep (se 2 (by rfl) ⟨1345497, by rfl⟩ : syracuseStep 3587993 = 2690995) B2690995
theorem B2392025 : Blo 1592995 2392025 := bstep (se 2 (by rfl) ⟨897009, by rfl⟩ : syracuseStep 2392025 = 1794019) B1794019
theorem B3588083 : Blo 1592995 3588083 := bstep (se 1 (by rfl) ⟨2691062, by rfl⟩ : syracuseStep 3588083 = 5382125) B5382125
theorem B1794055 : Blo 1592995 1794055 := bstep (se 1 (by rfl) ⟨1345541, by rfl⟩ : syracuseStep 1794055 = 2691083) B2691083
theorem B2392079 : Blo 1592995 2392079 := bstep (se 1 (by rfl) ⟨1794059, by rfl⟩ : syracuseStep 2392079 = 3588119) B3588119
theorem B26198039 : Blo 1592995 26198039 := bstep (se 1 (by rfl) ⟨19648529, by rfl⟩ : syracuseStep 26198039 = 39297059) B39297059
theorem B26206253 : Blo 1592995 26206253 := bstep (se 3 (by rfl) ⟨4913672, by rfl⟩ : syracuseStep 26206253 = 9827345) B9827345
theorem B2392121 : Blo 1592995 2392121 := bstep (se 2 (by rfl) ⟨897045, by rfl⟩ : syracuseStep 2392121 = 1794091) B1794091
theorem B4309051 : Blo 1592995 4309051 := bstep (se 1 (by rfl) ⟨3231788, by rfl⟩ : syracuseStep 4309051 = 6463577) B6463577
theorem B3588155 : Blo 1592995 3588155 := bstep (se 1 (by rfl) ⟨2691116, by rfl⟩ : syracuseStep 3588155 = 5382233) B5382233
theorem B2392199 : Blo 1592995 2392199 := bstep (se 1 (by rfl) ⟨1794149, by rfl⟩ : syracuseStep 2392199 = 3588299) B3588299
theorem B2392235 : Blo 1592995 2392235 := bstep (se 1 (by rfl) ⟨1794176, by rfl⟩ : syracuseStep 2392235 = 3588353) B3588353
theorem B3588281 : Blo 1592995 3588281 := bstep (se 2 (by rfl) ⟨1345605, by rfl⟩ : syracuseStep 3588281 = 2691211) B2691211
theorem B1794235 : Blo 1592995 1794235 := bstep (se 1 (by rfl) ⟨1345676, by rfl⟩ : syracuseStep 1794235 = 2691353) B2691353
theorem B2392265 : Blo 1592995 2392265 := bstep (se 2 (by rfl) ⟨897099, by rfl⟩ : syracuseStep 2392265 = 1794199) B1794199
theorem B2425033 : Blo 1592995 2425033 := bstep (se 2 (by rfl) ⟨909387, by rfl⟩ : syracuseStep 2425033 = 1818775) B1818775
theorem B2392379 : Blo 1592995 2392379 := bstep (se 1 (by rfl) ⟨1794284, by rfl⟩ : syracuseStep 2392379 = 3588569) B3588569
theorem B4309309 : Blo 1592995 4309309 := bstep (se 3 (by rfl) ⟨807995, by rfl⟩ : syracuseStep 4309309 = 1615991) B1615991
theorem B2154871 : Blo 1592995 2154871 := bstep (se 1 (by rfl) ⟨1616153, by rfl⟩ : syracuseStep 2154871 = 3232307) B3232307
theorem B2392439 : Blo 1592995 2392439 := bstep (se 1 (by rfl) ⟨1794329, by rfl⟩ : syracuseStep 2392439 = 3588659) B3588659
theorem B2392463 : Blo 1592995 2392463 := bstep (se 1 (by rfl) ⟨1794347, by rfl⟩ : syracuseStep 2392463 = 3588695) B3588695
theorem B4538891 : Blo 1592995 4538891 := bstep (se 1 (by rfl) ⟨3404168, by rfl⟩ : syracuseStep 4538891 = 6808337) B6808337
theorem B3588623 : Blo 1592995 3588623 := bstep (se 1 (by rfl) ⟨2691467, by rfl⟩ : syracuseStep 3588623 = 5382935) B5382935
theorem B3588641 : Blo 1592995 3588641 := bstep (se 2 (by rfl) ⟨1345740, by rfl⟩ : syracuseStep 3588641 = 2691481) B2691481
theorem B30655043 : Blo 1592995 30655043 := bstep (se 1 (by rfl) ⟨22991282, by rfl⟩ : syracuseStep 30655043 = 45982565) B45982565
theorem B9700013 : Blo 1592995 9700013 := bstep (se 3 (by rfl) ⟨1818752, by rfl⟩ : syracuseStep 9700013 = 3637505) B3637505
theorem B4981565 : Blo 1592995 4981565 := bstep (se 3 (by rfl) ⟨934043, by rfl⟩ : syracuseStep 4981565 = 1868087) B1868087
theorem B5383097 : Blo 1592995 5383097 := bstep (se 2 (by rfl) ⟨2018661, by rfl⟩ : syracuseStep 5383097 = 4037323) B4037323
theorem B2016247 : Blo 1592995 2016247 := bstep (se 1 (by rfl) ⟨1512185, by rfl⟩ : syracuseStep 2016247 = 3024371) B3024371
theorem B9323531 : Blo 1592995 9323531 := bstep (se 1 (by rfl) ⟨6992648, by rfl⟩ : syracuseStep 9323531 = 13985297) B13985297
theorem B2016571 : Blo 1592995 2016571 := bstep (se 1 (by rfl) ⟨1512428, by rfl⟩ : syracuseStep 2016571 = 3024857) B3024857
theorem B8070515 : Blo 1592995 8070515 := bstep (se 1 (by rfl) ⟨6052886, by rfl⟩ : syracuseStep 8070515 = 12105773) B12105773
theorem B2688457 : Blo 1592995 2688457 := bstep (se 2 (by rfl) ⟨1008171, by rfl⟩ : syracuseStep 2688457 = 2016343) B2016343
theorem B17229277 : Blo 1592995 17229277 := bstep (se 3 (by rfl) ⟨3230489, by rfl⟩ : syracuseStep 17229277 = 6460979) B6460979
theorem B4310543 : Blo 1592995 4310543 := bstep (se 1 (by rfl) ⟨3232907, by rfl⟩ : syracuseStep 4310543 = 6465815) B6465815
theorem B15320755 : Blo 1592995 15320755 := bstep (se 1 (by rfl) ⟨11490566, by rfl⟩ : syracuseStep 15320755 = 22981133) B22981133
theorem B6055681 : Blo 1592995 6055681 := bstep (se 2 (by rfl) ⟨2270880, by rfl⟩ : syracuseStep 6055681 = 4541761) B4541761
theorem B1615631 : Blo 1592995 1615631 := bstep (se 1 (by rfl) ⟨1211723, by rfl⟩ : syracuseStep 1615631 = 2423447) B2423447
theorem B14534437 : Blo 1592995 14534437 := bstep (se 4 (by rfl) ⟨1362603, by rfl⟩ : syracuseStep 14534437 = 2725207) B2725207
theorem B27617093 : Blo 1592995 27617093 := bstep (se 4 (by rfl) ⟨2589102, by rfl⟩ : syracuseStep 27617093 = 5178205) B5178205
theorem B8071001 : Blo 1592995 8071001 := bstep (se 2 (by rfl) ⟨3026625, by rfl⟩ : syracuseStep 8071001 = 6053251) B6053251
theorem B3827575 : Blo 1592995 3827575 := bstep (se 1 (by rfl) ⟨2870681, by rfl⟩ : syracuseStep 3827575 = 5741363) B5741363
theorem B3024955 : Blo 1592995 3024955 := bstep (se 1 (by rfl) ⟨2268716, by rfl⟩ : syracuseStep 3024955 = 4537433) B4537433
theorem B4540475 : Blo 1592995 4540475 := bstep (se 1 (by rfl) ⟨3405356, by rfl⟩ : syracuseStep 4540475 = 6810713) B6810713
theorem B4540531 : Blo 1592995 4540531 := bstep (se 1 (by rfl) ⟨3405398, by rfl⟩ : syracuseStep 4540531 = 6810797) B6810797
theorem B2689159 : Blo 1592995 2689159 := bstep (se 1 (by rfl) ⟨2016869, by rfl⟩ : syracuseStep 2689159 = 4033739) B4033739
theorem B8407277 : Blo 1592995 8407277 := bstep (se 3 (by rfl) ⟨1576364, by rfl⟩ : syracuseStep 8407277 = 3152729) B3152729
theorem B2017543 : Blo 1592995 2017543 := bstep (se 1 (by rfl) ⟨1513157, by rfl⟩ : syracuseStep 2017543 = 3026315) B3026315
theorem B4540873 : Blo 1592995 4540873 := bstep (se 2 (by rfl) ⟨1702827, by rfl⟩ : syracuseStep 4540873 = 3405655) B3405655
theorem B13617629 : Blo 1592995 13617629 := bstep (se 3 (by rfl) ⟨2553305, by rfl⟩ : syracuseStep 13617629 = 5106611) B5106611
theorem B7662109 : Blo 1592995 7662109 := bstep (se 3 (by rfl) ⟨1436645, by rfl⟩ : syracuseStep 7662109 = 2873291) B2873291
theorem B3025441 : Blo 1592995 3025441 := bstep (se 2 (by rfl) ⟨1134540, by rfl⟩ : syracuseStep 3025441 = 2269081) B2269081
theorem B4033111 : Blo 1592995 4033111 := bstep (se 1 (by rfl) ⟨3024833, by rfl⟩ : syracuseStep 4033111 = 6049667) B6049667
theorem B2017963 : Blo 1592995 2017963 := bstep (se 1 (by rfl) ⟨1513472, by rfl⟩ : syracuseStep 2017963 = 3026945) B3026945
theorem B19376819 : Blo 1592995 19376819 := bstep (se 1 (by rfl) ⟨14532614, by rfl⟩ : syracuseStep 19376819 = 29065229) B29065229
theorem B2689807 : Blo 1592995 2689807 := bstep (se 1 (by rfl) ⟨2017355, by rfl⟩ : syracuseStep 2689807 = 4034711) B4034711
theorem B3230507 : Blo 1592995 3230507 := bstep (se 1 (by rfl) ⟨2422880, by rfl⟩ : syracuseStep 3230507 = 4845761) B4845761
theorem B4033415 : Blo 1592995 4033415 := bstep (se 1 (by rfl) ⟨3025061, by rfl⟩ : syracuseStep 4033415 = 6050123) B6050123
theorem B2018191 : Blo 1592995 2018191 := bstep (se 1 (by rfl) ⟨1513643, by rfl⟩ : syracuseStep 2018191 = 3027287) B3027287
theorem B6048665 : Blo 1592995 6048665 := bstep (se 2 (by rfl) ⟨2268249, by rfl⟩ : syracuseStep 6048665 = 4536499) B4536499
theorem B12438425 : Blo 1592995 12438425 := bstep (se 2 (by rfl) ⟨4664409, by rfl⟩ : syracuseStep 12438425 = 9328819) B9328819
theorem B20704261 : Blo 1592995 20704261 := bstep (se 4 (by rfl) ⟨1941024, by rfl⟩ : syracuseStep 20704261 = 3882049) B3882049
theorem B4033547 : Blo 1592995 4033547 := bstep (se 1 (by rfl) ⟨3025160, by rfl⟩ : syracuseStep 4033547 = 6050321) B6050321
theorem B8293387 : Blo 1592995 8293387 := bstep (se 1 (by rfl) ⟨6220040, by rfl⟩ : syracuseStep 8293387 = 12440081) B12440081
theorem B3402767 : Blo 1592995 3402767 := bstep (se 1 (by rfl) ⟨2552075, by rfl⟩ : syracuseStep 3402767 = 5104151) B5104151
theorem B3402785 : Blo 1592995 3402785 := bstep (se 2 (by rfl) ⟨1276044, by rfl⟩ : syracuseStep 3402785 = 2552089) B2552089
theorem B3828883 : Blo 1592995 3828883 := bstep (se 1 (by rfl) ⟨2871662, by rfl⟩ : syracuseStep 3828883 = 5743325) B5743325
theorem B12102857 : Blo 1592995 12102857 := bstep (se 2 (by rfl) ⟨4538571, by rfl⟩ : syracuseStep 12102857 = 9077143) B9077143
theorem B8621257 : Blo 1592995 8621257 := bstep (se 2 (by rfl) ⟨3232971, by rfl⟩ : syracuseStep 8621257 = 6465943) B6465943
theorem B11488493 : Blo 1592995 11488493 := bstep (se 3 (by rfl) ⟨2154092, by rfl⟩ : syracuseStep 11488493 = 4308185) B4308185
theorem B1748231 : Blo 1592995 1748231 := bstep (se 1 (by rfl) ⟨1311173, by rfl⟩ : syracuseStep 1748231 = 2622347) B2622347
theorem B2690347 : Blo 1592995 2690347 := bstep (se 1 (by rfl) ⟨2017760, by rfl⟩ : syracuseStep 2690347 = 4035521) B4035521
theorem B3403127 : Blo 1592995 3403127 := bstep (se 1 (by rfl) ⟨2552345, by rfl⟩ : syracuseStep 3403127 = 5104691) B5104691
theorem B5377427 : Blo 1592995 5377427 := bstep (se 1 (by rfl) ⟨4033070, by rfl⟩ : syracuseStep 5377427 = 8066141) B8066141
theorem B2690489 : Blo 1592995 2690489 := bstep (se 2 (by rfl) ⟨1008933, by rfl⟩ : syracuseStep 2690489 = 2017867) B2017867
theorem B11488721 : Blo 1592995 11488721 := bstep (se 2 (by rfl) ⟨4308270, by rfl⟩ : syracuseStep 11488721 = 8616541) B8616541
theorem B13618691 : Blo 1592995 13618691 := bstep (se 1 (by rfl) ⟨10214018, by rfl⟩ : syracuseStep 13618691 = 20428037) B20428037
theorem B4034063 : Blo 1592995 4034063 := bstep (se 1 (by rfl) ⟨3025547, by rfl⟩ : syracuseStep 4034063 = 6051095) B6051095
theorem B4034195 : Blo 1592995 4034195 := bstep (se 1 (by rfl) ⟨3025646, by rfl⟩ : syracuseStep 4034195 = 6051293) B6051293
theorem B1593019 : Blo 1592995 1593019 := bstep (se 1 (by rfl) ⟨1194764, by rfl⟩ : syracuseStep 1593019 = 2389529) B2389529
theorem B1593095 : Blo 1592995 1593095 := bstep (se 1 (by rfl) ⟨1194821, by rfl⟩ : syracuseStep 1593095 = 2389643) B2389643
theorem B1593103 : Blo 1592995 1593103 := bstep (se 1 (by rfl) ⟨1194827, by rfl⟩ : syracuseStep 1593103 = 2389655) B2389655
theorem B1593147 : Blo 1592995 1593147 := bstep (se 1 (by rfl) ⟨1194860, by rfl⟩ : syracuseStep 1593147 = 2389721) B2389721
theorem B3026747 : Blo 1592995 3026747 := bstep (se 1 (by rfl) ⟨2270060, by rfl⟩ : syracuseStep 3026747 = 4540121) B4540121
theorem B12922739 : Blo 1592995 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B1593223 : Blo 1592995 1593223 := bstep (se 1 (by rfl) ⟨1194917, by rfl⟩ : syracuseStep 1593223 = 2389835) B2389835
theorem B1593231 : Blo 1592995 1593231 := bstep (se 1 (by rfl) ⟨1194923, by rfl⟩ : syracuseStep 1593231 = 2389847) B2389847
theorem B8073107 : Blo 1592995 8073107 := bstep (se 1 (by rfl) ⟨6054830, by rfl⟩ : syracuseStep 8073107 = 12109661) B12109661
theorem B1593275 : Blo 1592995 1593275 := bstep (se 1 (by rfl) ⟨1194956, by rfl⟩ : syracuseStep 1593275 = 2389913) B2389913
theorem B2043895 : Blo 1592995 2043895 := bstep (se 1 (by rfl) ⟨1532921, by rfl⟩ : syracuseStep 2043895 = 3065843) B3065843
theorem B1593351 : Blo 1592995 1593351 := bstep (se 1 (by rfl) ⟨1195013, by rfl⟩ : syracuseStep 1593351 = 2390027) B2390027
theorem B1593359 : Blo 1592995 1593359 := bstep (se 1 (by rfl) ⟨1195019, by rfl⟩ : syracuseStep 1593359 = 2390039) B2390039
theorem B6049835 : Blo 1592995 6049835 := bstep (se 1 (by rfl) ⟨4537376, by rfl⟩ : syracuseStep 6049835 = 9074753) B9074753
theorem B1593403 : Blo 1592995 1593403 := bstep (se 1 (by rfl) ⟨1195052, by rfl⟩ : syracuseStep 1593403 = 2390105) B2390105
theorem B2691191 : Blo 1592995 2691191 := bstep (se 1 (by rfl) ⟨2018393, by rfl⟩ : syracuseStep 2691191 = 4036787) B4036787
theorem B1593479 : Blo 1592995 1593479 := bstep (se 1 (by rfl) ⟨1195109, by rfl⟩ : syracuseStep 1593479 = 2390219) B2390219
theorem B1593487 : Blo 1592995 1593487 := bstep (se 1 (by rfl) ⟨1195115, by rfl⟩ : syracuseStep 1593487 = 2390231) B2390231
theorem B1593531 : Blo 1592995 1593531 := bstep (se 1 (by rfl) ⟨1195148, by rfl⟩ : syracuseStep 1593531 = 2390297) B2390297
theorem B3633353 : Blo 1592995 3633353 := bstep (se 2 (by rfl) ⟨1362507, by rfl⟩ : syracuseStep 3633353 = 2725015) B2725015
theorem B1593607 : Blo 1592995 1593607 := bstep (se 1 (by rfl) ⟨1195205, by rfl⟩ : syracuseStep 1593607 = 2390411) B2390411
theorem B1593615 : Blo 1592995 1593615 := bstep (se 1 (by rfl) ⟨1195211, by rfl⟩ : syracuseStep 1593615 = 2390423) B2390423
theorem B3027233 : Blo 1592995 3027233 := bstep (se 2 (by rfl) ⟨1135212, by rfl⟩ : syracuseStep 3027233 = 2270425) B2270425
theorem B8065331 : Blo 1592995 8065331 := bstep (se 1 (by rfl) ⟨6048998, by rfl⟩ : syracuseStep 8065331 = 12097997) B12097997
theorem B1593659 : Blo 1592995 1593659 := bstep (se 1 (by rfl) ⟨1195244, by rfl⟩ : syracuseStep 1593659 = 2390489) B2390489
theorem B3830075 : Blo 1592995 3830075 := bstep (se 1 (by rfl) ⟨2872556, by rfl⟩ : syracuseStep 3830075 = 5745113) B5745113
theorem B3584375 : Blo 1592995 3584375 := bstep (se 1 (by rfl) ⟨2688281, by rfl⟩ : syracuseStep 3584375 = 5376563) B5376563
theorem B1593735 : Blo 1592995 1593735 := bstep (se 1 (by rfl) ⟨1195301, by rfl⟩ : syracuseStep 1593735 = 2390603) B2390603
theorem B1593743 : Blo 1592995 1593743 := bstep (se 1 (by rfl) ⟨1195307, by rfl⟩ : syracuseStep 1593743 = 2390615) B2390615
theorem B9073043 : Blo 1592995 9073043 := bstep (se 1 (by rfl) ⟨6804782, by rfl⟩ : syracuseStep 9073043 = 13609565) B13609565
theorem B5747129 : Blo 1592995 5747129 := bstep (se 2 (by rfl) ⟨2155173, by rfl⟩ : syracuseStep 5747129 = 4310347) B4310347
theorem B3027385 : Blo 1592995 3027385 := bstep (se 2 (by rfl) ⟨1135269, by rfl⟩ : syracuseStep 3027385 = 2270539) B2270539
theorem B1593787 : Blo 1592995 1593787 := bstep (se 1 (by rfl) ⟨1195340, by rfl⟩ : syracuseStep 1593787 = 2390681) B2390681
theorem B1593863 : Blo 1592995 1593863 := bstep (se 1 (by rfl) ⟨1195397, by rfl⟩ : syracuseStep 1593863 = 2390795) B2390795
theorem B1593871 : Blo 1592995 1593871 := bstep (se 1 (by rfl) ⟨1195403, by rfl⟩ : syracuseStep 1593871 = 2390807) B2390807
theorem B3584555 : Blo 1592995 3584555 := bstep (se 1 (by rfl) ⟨2688416, by rfl⟩ : syracuseStep 3584555 = 5376833) B5376833
theorem B1593915 : Blo 1592995 1593915 := bstep (se 1 (by rfl) ⟨1195436, by rfl⟩ : syracuseStep 1593915 = 2390873) B2390873
theorem B8065655 : Blo 1592995 8065655 := bstep (se 1 (by rfl) ⟨6049241, by rfl⟩ : syracuseStep 8065655 = 12098483) B12098483
theorem B1593991 : Blo 1592995 1593991 := bstep (se 1 (by rfl) ⟨1195493, by rfl⟩ : syracuseStep 1593991 = 2390987) B2390987
theorem B1593999 : Blo 1592995 1593999 := bstep (se 1 (by rfl) ⟨1195499, by rfl⟩ : syracuseStep 1593999 = 2390999) B2390999
theorem B9081517 : Blo 1592995 9081517 := bstep (se 3 (by rfl) ⟨1702784, by rfl⟩ : syracuseStep 9081517 = 3405569) B3405569
theorem B1594043 : Blo 1592995 1594043 := bstep (se 1 (by rfl) ⟨1195532, by rfl⟩ : syracuseStep 1594043 = 2391065) B2391065
theorem B4035329 : Blo 1592995 4035329 := bstep (se 2 (by rfl) ⟨1513248, by rfl⟩ : syracuseStep 4035329 = 3026497) B3026497
theorem B1594119 : Blo 1592995 1594119 := bstep (se 1 (by rfl) ⟨1195589, by rfl⟩ : syracuseStep 1594119 = 2391179) B2391179
theorem B5378831 : Blo 1592995 5378831 := bstep (se 1 (by rfl) ⟨4034123, by rfl⟩ : syracuseStep 5378831 = 8068247) B8068247
theorem B1594127 : Blo 1592995 1594127 := bstep (se 1 (by rfl) ⟨1195595, by rfl⟩ : syracuseStep 1594127 = 2391191) B2391191
theorem B31462181 : Blo 1592995 31462181 := bstep (se 4 (by rfl) ⟨2949579, by rfl⟩ : syracuseStep 31462181 = 5899159) B5899159
theorem B1594171 : Blo 1592995 1594171 := bstep (se 1 (by rfl) ⟨1195628, by rfl⟩ : syracuseStep 1594171 = 2391257) B2391257
theorem B1594247 : Blo 1592995 1594247 := bstep (se 1 (by rfl) ⟨1195685, by rfl⟩ : syracuseStep 1594247 = 2391371) B2391371
theorem B5747591 : Blo 1592995 5747591 := bstep (se 1 (by rfl) ⟨4310693, by rfl⟩ : syracuseStep 5747591 = 8621387) B8621387
theorem B1594255 : Blo 1592995 1594255 := bstep (se 1 (by rfl) ⟨1195691, by rfl⟩ : syracuseStep 1594255 = 2391383) B2391383
theorem B3584915 : Blo 1592995 3584915 := bstep (se 1 (by rfl) ⟨2688686, by rfl⟩ : syracuseStep 3584915 = 5377373) B5377373
theorem B18166679 : Blo 1592995 18166679 := bstep (se 1 (by rfl) ⟨13625009, by rfl⟩ : syracuseStep 18166679 = 27250019) B27250019
theorem B1594299 : Blo 1592995 1594299 := bstep (se 1 (by rfl) ⟨1195724, by rfl⟩ : syracuseStep 1594299 = 2391449) B2391449
theorem B3584969 : Blo 1592995 3584969 := bstep (se 2 (by rfl) ⟨1344363, by rfl⟩ : syracuseStep 3584969 = 2688727) B2688727
theorem B1594375 : Blo 1592995 1594375 := bstep (se 1 (by rfl) ⟨1195781, by rfl⟩ : syracuseStep 1594375 = 2391563) B2391563
theorem B1594383 : Blo 1592995 1594383 := bstep (se 1 (by rfl) ⟨1195787, by rfl⟩ : syracuseStep 1594383 = 2391575) B2391575
theorem B5379101 : Blo 1592995 5379101 := bstep (se 3 (by rfl) ⟨1008581, by rfl⟩ : syracuseStep 5379101 = 2017163) B2017163
theorem B1594427 : Blo 1592995 1594427 := bstep (se 1 (by rfl) ⟨1195820, by rfl⟩ : syracuseStep 1594427 = 2391641) B2391641
theorem B4035703 : Blo 1592995 4035703 := bstep (se 1 (by rfl) ⟨3026777, by rfl⟩ : syracuseStep 4035703 = 6053555) B6053555
theorem B1594503 : Blo 1592995 1594503 := bstep (se 1 (by rfl) ⟨1195877, by rfl⟩ : syracuseStep 1594503 = 2391755) B2391755
theorem B1594511 : Blo 1592995 1594511 := bstep (se 1 (by rfl) ⟨1195883, by rfl⟩ : syracuseStep 1594511 = 2391767) B2391767
theorem B1594555 : Blo 1592995 1594555 := bstep (se 1 (by rfl) ⟨1195916, by rfl⟩ : syracuseStep 1594555 = 2391833) B2391833
theorem B1594631 : Blo 1592995 1594631 := bstep (se 1 (by rfl) ⟨1195973, by rfl⟩ : syracuseStep 1594631 = 2391947) B2391947
theorem B1594639 : Blo 1592995 1594639 := bstep (se 1 (by rfl) ⟨1195979, by rfl⟩ : syracuseStep 1594639 = 2391959) B2391959
theorem B1594683 : Blo 1592995 1594683 := bstep (se 1 (by rfl) ⟨1196012, by rfl⟩ : syracuseStep 1594683 = 2392025) B2392025
theorem B5453191 : Blo 1592995 5453191 := bstep (se 1 (by rfl) ⟨4089893, by rfl⟩ : syracuseStep 5453191 = 8179787) B8179787
theorem B1594759 : Blo 1592995 1594759 := bstep (se 1 (by rfl) ⟨1196069, by rfl⟩ : syracuseStep 1594759 = 2392139) B2392139
theorem B2299279 : Blo 1592995 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B1594767 : Blo 1592995 1594767 := bstep (se 1 (by rfl) ⟨1196075, by rfl⟩ : syracuseStep 1594767 = 2392151) B2392151
theorem B1914283 : Blo 1592995 1914283 := bstep (se 1 (by rfl) ⟨1435712, by rfl⟩ : syracuseStep 1914283 = 2871425) B2871425
theorem B1594811 : Blo 1592995 1594811 := bstep (se 1 (by rfl) ⟨1196108, by rfl⟩ : syracuseStep 1594811 = 2392217) B2392217
theorem B2389511 : Blo 1592995 2389511 := bstep (se 1 (by rfl) ⟨1792133, by rfl⟩ : syracuseStep 2389511 = 3584267) B3584267
theorem B1594887 : Blo 1592995 1594887 := bstep (se 1 (by rfl) ⟨1196165, by rfl⟩ : syracuseStep 1594887 = 2392331) B2392331
theorem B1594895 : Blo 1592995 1594895 := bstep (se 1 (by rfl) ⟨1196171, by rfl⟩ : syracuseStep 1594895 = 2392343) B2392343
theorem B5109277 : Blo 1592995 5109277 := bstep (se 3 (by rfl) ⟨957989, by rfl⟩ : syracuseStep 5109277 = 1915979) B1915979
theorem B2389547 : Blo 1592995 2389547 := bstep (se 1 (by rfl) ⟨1792160, by rfl⟩ : syracuseStep 2389547 = 3584321) B3584321
theorem B4036139 : Blo 1592995 4036139 := bstep (se 1 (by rfl) ⟨3027104, by rfl⟩ : syracuseStep 4036139 = 6054209) B6054209
theorem B1594939 : Blo 1592995 1594939 := bstep (se 1 (by rfl) ⟨1196204, by rfl⟩ : syracuseStep 1594939 = 2392409) B2392409
theorem B8066627 : Blo 1592995 8066627 := bstep (se 1 (by rfl) ⟨6049970, by rfl⟩ : syracuseStep 8066627 = 12099941) B12099941
theorem B2389577 : Blo 1592995 2389577 := bstep (se 2 (by rfl) ⟨896091, by rfl⟩ : syracuseStep 2389577 = 1792183) B1792183
theorem B16356983 : Blo 1592995 16356983 := bstep (se 1 (by rfl) ⟨12267737, by rfl⟩ : syracuseStep 16356983 = 24535475) B24535475
theorem B3585671 : Blo 1592995 3585671 := bstep (se 1 (by rfl) ⟨2689253, by rfl⟩ : syracuseStep 3585671 = 5378507) B5378507
theorem B2389691 : Blo 1592995 2389691 := bstep (se 1 (by rfl) ⟨1792268, by rfl⟩ : syracuseStep 2389691 = 3584537) B3584537
theorem B13104833 : Blo 1592995 13104833 := bstep (se 2 (by rfl) ⟨4914312, by rfl⟩ : syracuseStep 13104833 = 9828625) B9828625
theorem B2389751 : Blo 1592995 2389751 := bstep (se 1 (by rfl) ⟨1792313, by rfl⟩ : syracuseStep 2389751 = 3584627) B3584627
theorem B2389775 : Blo 1592995 2389775 := bstep (se 1 (by rfl) ⟨1792331, by rfl⟩ : syracuseStep 2389775 = 3584663) B3584663
theorem B2389817 : Blo 1592995 2389817 := bstep (se 2 (by rfl) ⟨896181, by rfl⟩ : syracuseStep 2389817 = 1792363) B1792363
theorem B1701691 : Blo 1592995 1701691 := bstep (se 1 (by rfl) ⟨1276268, by rfl⟩ : syracuseStep 1701691 = 2552537) B2552537
theorem B3585851 : Blo 1592995 3585851 := bstep (se 1 (by rfl) ⟨2689388, by rfl⟩ : syracuseStep 3585851 = 5378777) B5378777
theorem B4601719 : Blo 1592995 4601719 := bstep (se 1 (by rfl) ⟨3451289, by rfl⟩ : syracuseStep 4601719 = 6902579) B6902579
theorem B2389895 : Blo 1592995 2389895 := bstep (se 1 (by rfl) ⟨1792421, by rfl⟩ : syracuseStep 2389895 = 3584843) B3584843
theorem B8066951 : Blo 1592995 8066951 := bstep (se 1 (by rfl) ⟨6050213, by rfl⟩ : syracuseStep 8066951 = 12100427) B12100427
theorem B19658647 : Blo 1592995 19658647 := bstep (se 1 (by rfl) ⟨14743985, by rfl⟩ : syracuseStep 19658647 = 29487971) B29487971
theorem B12269465 : Blo 1592995 12269465 := bstep (se 2 (by rfl) ⟨4601049, by rfl⟩ : syracuseStep 12269465 = 9202099) B9202099
theorem B2389931 : Blo 1592995 2389931 := bstep (se 1 (by rfl) ⟨1792448, by rfl⟩ : syracuseStep 2389931 = 3584897) B3584897
theorem B3585977 : Blo 1592995 3585977 := bstep (se 2 (by rfl) ⟨1344741, by rfl⟩ : syracuseStep 3585977 = 2689483) B2689483
theorem B2389961 : Blo 1592995 2389961 := bstep (se 2 (by rfl) ⟨896235, by rfl⟩ : syracuseStep 2389961 = 1792471) B1792471
theorem B6051793 : Blo 1592995 6051793 := bstep (se 2 (by rfl) ⟨2269422, by rfl⟩ : syracuseStep 6051793 = 4538845) B4538845
theorem B2390075 : Blo 1592995 2390075 := bstep (se 1 (by rfl) ⟨1792556, by rfl⟩ : syracuseStep 2390075 = 3585113) B3585113
theorem B82810997 : Blo 1592995 82810997 := bstep (se 5 (by rfl) ⟨3881765, by rfl⟩ : syracuseStep 82810997 = 7763531) B7763531
theorem B2390135 : Blo 1592995 2390135 := bstep (se 1 (by rfl) ⟨1792601, by rfl⟩ : syracuseStep 2390135 = 3585203) B3585203
theorem B2390159 : Blo 1592995 2390159 := bstep (se 1 (by rfl) ⟨1792619, by rfl⟩ : syracuseStep 2390159 = 3585239) B3585239
theorem B2390201 : Blo 1592995 2390201 := bstep (se 2 (by rfl) ⟨896325, by rfl⟩ : syracuseStep 2390201 = 1792651) B1792651
theorem B6052097 : Blo 1592995 6052097 := bstep (se 2 (by rfl) ⟨2269536, by rfl⟩ : syracuseStep 6052097 = 4539073) B4539073
theorem B2390279 : Blo 1592995 2390279 := bstep (se 1 (by rfl) ⟨1792709, by rfl⟩ : syracuseStep 2390279 = 3585419) B3585419
theorem B3586319 : Blo 1592995 3586319 := bstep (se 1 (by rfl) ⟨2689739, by rfl⟩ : syracuseStep 3586319 = 5379479) B5379479
theorem B3586337 : Blo 1592995 3586337 := bstep (se 2 (by rfl) ⟨1344876, by rfl⟩ : syracuseStep 3586337 = 2689753) B2689753
theorem B3635489 : Blo 1592995 3635489 := bstep (se 2 (by rfl) ⟨1363308, by rfl⟩ : syracuseStep 3635489 = 2726617) B2726617
theorem B2390315 : Blo 1592995 2390315 := bstep (se 1 (by rfl) ⟨1792736, by rfl⟩ : syracuseStep 2390315 = 3585473) B3585473
theorem B2390345 : Blo 1592995 2390345 := bstep (se 2 (by rfl) ⟨896379, by rfl⟩ : syracuseStep 2390345 = 1792759) B1792759
theorem B4036979 : Blo 1592995 4036979 := bstep (se 1 (by rfl) ⟨3027734, by rfl⟩ : syracuseStep 4036979 = 6055469) B6055469
theorem B4036999 : Blo 1592995 4036999 := bstep (se 1 (by rfl) ⟨3027749, by rfl⟩ : syracuseStep 4036999 = 6055499) B6055499
theorem B1792399 : Blo 1592995 1792399 := bstep (se 1 (by rfl) ⟨1344299, by rfl⟩ : syracuseStep 1792399 = 2688599) B2688599
theorem B5380505 : Blo 1592995 5380505 := bstep (se 2 (by rfl) ⟨2017689, by rfl⟩ : syracuseStep 5380505 = 4035379) B4035379
theorem B2390459 : Blo 1592995 2390459 := bstep (se 1 (by rfl) ⟨1792844, by rfl⟩ : syracuseStep 2390459 = 3585689) B3585689
theorem B2390519 : Blo 1592995 2390519 := bstep (se 1 (by rfl) ⟨1792889, by rfl⟩ : syracuseStep 2390519 = 3585779) B3585779
theorem B2390543 : Blo 1592995 2390543 := bstep (se 1 (by rfl) ⟨1792907, by rfl⟩ : syracuseStep 2390543 = 3585815) B3585815
theorem B2390585 : Blo 1592995 2390585 := bstep (se 2 (by rfl) ⟨896469, by rfl⟩ : syracuseStep 2390585 = 1792939) B1792939
theorem B3586679 : Blo 1592995 3586679 := bstep (se 1 (by rfl) ⟨2690009, by rfl⟩ : syracuseStep 3586679 = 5380019) B5380019
theorem B2390663 : Blo 1592995 2390663 := bstep (se 1 (by rfl) ⟨1792997, by rfl⟩ : syracuseStep 2390663 = 3585995) B3585995
theorem B4037273 : Blo 1592995 4037273 := bstep (se 2 (by rfl) ⟨1513977, by rfl⟩ : syracuseStep 4037273 = 3027955) B3027955
theorem B2390699 : Blo 1592995 2390699 := bstep (se 1 (by rfl) ⟨1793024, by rfl⟩ : syracuseStep 2390699 = 3586049) B3586049
theorem B2390729 : Blo 1592995 2390729 := bstep (se 2 (by rfl) ⟨896523, by rfl⟩ : syracuseStep 2390729 = 1793047) B1793047
theorem B6052553 : Blo 1592995 6052553 := bstep (se 2 (by rfl) ⟨2269707, by rfl⟩ : syracuseStep 6052553 = 4539415) B4539415
theorem B5905133 : Blo 1592995 5905133 := bstep (se 3 (by rfl) ⟨1107212, by rfl⟩ : syracuseStep 5905133 = 2214425) B2214425
theorem B3586859 : Blo 1592995 3586859 := bstep (se 1 (by rfl) ⟨2690144, by rfl⟩ : syracuseStep 3586859 = 5380289) B5380289
theorem B2390843 : Blo 1592995 2390843 := bstep (se 1 (by rfl) ⟨1793132, by rfl⟩ : syracuseStep 2390843 = 3586265) B3586265
theorem B13613939 : Blo 1592995 13613939 := bstep (se 1 (by rfl) ⟨10210454, by rfl⟩ : syracuseStep 13613939 = 20420909) B20420909
theorem B2390903 : Blo 1592995 2390903 := bstep (se 1 (by rfl) ⟨1793177, by rfl⟩ : syracuseStep 2390903 = 3586355) B3586355
theorem B1792903 : Blo 1592995 1792903 := bstep (se 1 (by rfl) ⟨1344677, by rfl⟩ : syracuseStep 1792903 = 2689355) B2689355
theorem B2390927 : Blo 1592995 2390927 := bstep (se 1 (by rfl) ⟨1793195, by rfl⟩ : syracuseStep 2390927 = 3586391) B3586391
theorem B2423695 : Blo 1592995 2423695 := bstep (se 1 (by rfl) ⟨1817771, by rfl⟩ : syracuseStep 2423695 = 3635543) B3635543
theorem B2390969 : Blo 1592995 2390969 := bstep (se 2 (by rfl) ⟨896613, by rfl⟩ : syracuseStep 2390969 = 1793227) B1793227
theorem B19651531 : Blo 1592995 19651531 := bstep (se 1 (by rfl) ⟨14738648, by rfl⟩ : syracuseStep 19651531 = 29477297) B29477297
theorem B2391047 : Blo 1592995 2391047 := bstep (se 1 (by rfl) ⟨1793285, by rfl⟩ : syracuseStep 2391047 = 3586571) B3586571
theorem B9083933 : Blo 1592995 9083933 := bstep (se 3 (by rfl) ⟨1703237, by rfl⟩ : syracuseStep 9083933 = 3406475) B3406475
theorem B4537387 : Blo 1592995 4537387 := bstep (se 1 (by rfl) ⟨3403040, by rfl⟩ : syracuseStep 4537387 = 6806081) B6806081
theorem B2391083 : Blo 1592995 2391083 := bstep (se 1 (by rfl) ⟨1793312, by rfl⟩ : syracuseStep 2391083 = 3586625) B3586625
theorem B1793083 : Blo 1592995 1793083 := bstep (se 1 (by rfl) ⟨1344812, by rfl⟩ : syracuseStep 1793083 = 2689625) B2689625
theorem B2391113 : Blo 1592995 2391113 := bstep (se 2 (by rfl) ⟨896667, by rfl⟩ : syracuseStep 2391113 = 1793335) B1793335
theorem B5381207 : Blo 1592995 5381207 := bstep (se 1 (by rfl) ⟨4035905, by rfl⟩ : syracuseStep 5381207 = 8071811) B8071811
theorem B3587219 : Blo 1592995 3587219 := bstep (se 1 (by rfl) ⟨2690414, by rfl⟩ : syracuseStep 3587219 = 5380829) B5380829
theorem B2391227 : Blo 1592995 2391227 := bstep (se 1 (by rfl) ⟨1793420, by rfl⟩ : syracuseStep 2391227 = 3586841) B3586841
theorem B3587273 : Blo 1592995 3587273 := bstep (se 2 (by rfl) ⟨1345227, by rfl⟩ : syracuseStep 3587273 = 2690455) B2690455
theorem B13614317 : Blo 1592995 13614317 := bstep (se 3 (by rfl) ⟨2552684, by rfl⟩ : syracuseStep 13614317 = 5105369) B5105369
theorem B2391287 : Blo 1592995 2391287 := bstep (se 1 (by rfl) ⟨1793465, by rfl⟩ : syracuseStep 2391287 = 3586931) B3586931
theorem B4537615 : Blo 1592995 4537615 := bstep (se 1 (by rfl) ⟨3403211, by rfl⟩ : syracuseStep 4537615 = 6806423) B6806423
theorem B2391311 : Blo 1592995 2391311 := bstep (se 1 (by rfl) ⟨1793483, by rfl⟩ : syracuseStep 2391311 = 3586967) B3586967
theorem B2391353 : Blo 1592995 2391353 := bstep (se 2 (by rfl) ⟨896757, by rfl⟩ : syracuseStep 2391353 = 1793515) B1793515
theorem B67198267 : Blo 1592995 67198267 := bstep (se 1 (by rfl) ⟨50398700, by rfl⟩ : syracuseStep 67198267 = 100797401) B100797401
theorem B2391431 : Blo 1592995 2391431 := bstep (se 1 (by rfl) ⟨1793573, by rfl⟩ : syracuseStep 2391431 = 3587147) B3587147
theorem B2391467 : Blo 1592995 2391467 := bstep (se 1 (by rfl) ⟨1793600, by rfl⟩ : syracuseStep 2391467 = 3587201) B3587201
theorem B14745017 : Blo 1592995 14745017 := bstep (se 2 (by rfl) ⟨5529381, by rfl⟩ : syracuseStep 14745017 = 11058763) B11058763
theorem B2391497 : Blo 1592995 2391497 := bstep (se 2 (by rfl) ⟨896811, by rfl⟩ : syracuseStep 2391497 = 1793623) B1793623
theorem B1793551 : Blo 1592995 1793551 := bstep (se 1 (by rfl) ⟨1345163, by rfl⟩ : syracuseStep 1793551 = 2690327) B2690327
theorem B4537889 : Blo 1592995 4537889 := bstep (se 2 (by rfl) ⟨1701708, by rfl⟩ : syracuseStep 4537889 = 3403417) B3403417
theorem B2391611 : Blo 1592995 2391611 := bstep (se 1 (by rfl) ⟨1793708, by rfl⟩ : syracuseStep 2391611 = 3587417) B3587417
theorem B5381693 : Blo 1592995 5381693 := bstep (se 3 (by rfl) ⟨1009067, by rfl⟩ : syracuseStep 5381693 = 2018135) B2018135
theorem B36789835 : Blo 1592995 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B2391671 : Blo 1592995 2391671 := bstep (se 1 (by rfl) ⟨1793753, by rfl⟩ : syracuseStep 2391671 = 3587507) B3587507
theorem B6553207 : Blo 1592995 6553207 := bstep (se 1 (by rfl) ⟨4914905, by rfl⟩ : syracuseStep 6553207 = 9829811) B9829811
theorem B2391695 : Blo 1592995 2391695 := bstep (se 1 (by rfl) ⟨1793771, by rfl⟩ : syracuseStep 2391695 = 3587543) B3587543
theorem B24886963 : Blo 1592995 24886963 := bstep (se 1 (by rfl) ⟨18665222, by rfl⟩ : syracuseStep 24886963 = 37330445) B37330445
theorem B2391737 : Blo 1592995 2391737 := bstep (se 2 (by rfl) ⟨896901, by rfl⟩ : syracuseStep 2391737 = 1793803) B1793803
theorem B2391815 : Blo 1592995 2391815 := bstep (se 1 (by rfl) ⟨1793861, by rfl⟩ : syracuseStep 2391815 = 3587723) B3587723
theorem B6807311 : Blo 1592995 6807311 := bstep (se 1 (by rfl) ⟨5105483, by rfl⟩ : syracuseStep 6807311 = 10210967) B10210967
theorem B2391851 : Blo 1592995 2391851 := bstep (se 1 (by rfl) ⟨1793888, by rfl⟩ : syracuseStep 2391851 = 3587777) B3587777
theorem B24551237 : Blo 1592995 24551237 := bstep (se 4 (by rfl) ⟨2301678, by rfl⟩ : syracuseStep 24551237 = 4603357) B4603357
theorem B2391881 : Blo 1592995 2391881 := bstep (se 2 (by rfl) ⟨896955, by rfl⟩ : syracuseStep 2391881 = 1793911) B1793911
theorem B4538231 : Blo 1592995 4538231 := bstep (se 1 (by rfl) ⟨3403673, by rfl⟩ : syracuseStep 4538231 = 6807347) B6807347
theorem B3587975 : Blo 1592995 3587975 := bstep (se 1 (by rfl) ⟨2690981, by rfl⟩ : syracuseStep 3587975 = 5381963) B5381963
theorem B2391995 : Blo 1592995 2391995 := bstep (se 1 (by rfl) ⟨1793996, by rfl⟩ : syracuseStep 2391995 = 3587993) B3587993
theorem B2392055 : Blo 1592995 2392055 := bstep (se 1 (by rfl) ⟨1794041, by rfl⟩ : syracuseStep 2392055 = 3588083) B3588083
theorem B2392073 : Blo 1592995 2392073 := bstep (se 2 (by rfl) ⟨897027, by rfl⟩ : syracuseStep 2392073 = 1794055) B1794055
theorem B2392103 : Blo 1592995 2392103 := bstep (se 1 (by rfl) ⟨1794077, by rfl⟩ : syracuseStep 2392103 = 3588155) B3588155
theorem B69861437 : Blo 1592995 69861437 := bstep (se 3 (by rfl) ⟨13099019, by rfl⟩ : syracuseStep 69861437 = 26198039) B26198039
theorem B1794127 : Blo 1592995 1794127 := bstep (se 1 (by rfl) ⟨1345595, by rfl⟩ : syracuseStep 1794127 = 2691191) B2691191
theorem B2392187 : Blo 1592995 2392187 := bstep (se 1 (by rfl) ⟨1794140, by rfl⟩ : syracuseStep 2392187 = 3588281) B3588281
theorem B6054041 : Blo 1592995 6054041 := bstep (se 2 (by rfl) ⟨2270265, by rfl⟩ : syracuseStep 6054041 = 4540531) B4540531
theorem B2392313 : Blo 1592995 2392313 := bstep (se 2 (by rfl) ⟨897117, by rfl⟩ : syracuseStep 2392313 = 1794235) B1794235
theorem B2392415 : Blo 1592995 2392415 := bstep (se 1 (by rfl) ⟨1794311, by rfl⟩ : syracuseStep 2392415 = 3588623) B3588623
theorem B2392427 : Blo 1592995 2392427 := bstep (se 1 (by rfl) ⟨1794320, by rfl⟩ : syracuseStep 2392427 = 3588641) B3588641
theorem B5382665 : Blo 1592995 5382665 := bstep (se 2 (by rfl) ⟨2018499, by rfl⟩ : syracuseStep 5382665 = 4036999) B4036999
theorem B6054497 : Blo 1592995 6054497 := bstep (se 2 (by rfl) ⟨2270436, by rfl⟩ : syracuseStep 6054497 = 4540873) B4540873
theorem B3588731 : Blo 1592995 3588731 := bstep (se 1 (by rfl) ⟨2691548, by rfl⟩ : syracuseStep 3588731 = 5383097) B5383097
theorem B10216145 : Blo 1592995 10216145 := bstep (se 2 (by rfl) ⟨3831054, by rfl⟩ : syracuseStep 10216145 = 7662109) B7662109
theorem B12108689 : Blo 1592995 12108689 := bstep (se 2 (by rfl) ⟨4540758, by rfl⟩ : syracuseStep 12108689 = 9081517) B9081517
theorem B2688329 : Blo 1592995 2688329 := bstep (se 2 (by rfl) ⟨1008123, by rfl⟩ : syracuseStep 2688329 = 2016247) B2016247
theorem B11494781 : Blo 1592995 11494781 := bstep (se 3 (by rfl) ⟨2155271, by rfl⟩ : syracuseStep 11494781 = 4310543) B4310543
theorem B55207331 : Blo 1592995 55207331 := bstep (se 1 (by rfl) ⟨41405498, by rfl⟩ : syracuseStep 55207331 = 82810997) B82810997
theorem B5604851 : Blo 1592995 5604851 := bstep (se 1 (by rfl) ⟨4203638, by rfl⟩ : syracuseStep 5604851 = 8407277) B8407277
theorem B5105177 : Blo 1592995 5105177 := bstep (se 2 (by rfl) ⟨1914441, by rfl⟩ : syracuseStep 5105177 = 3828883) B3828883
theorem B11495009 : Blo 1592995 11495009 := bstep (se 2 (by rfl) ⟨4310628, by rfl⟩ : syracuseStep 11495009 = 8621257) B8621257
theorem B9078419 : Blo 1592995 9078419 := bstep (se 1 (by rfl) ⟨6808814, by rfl⟩ : syracuseStep 9078419 = 13617629) B13617629
theorem B2688761 : Blo 1592995 2688761 := bstep (se 2 (by rfl) ⟨1008285, by rfl⟩ : syracuseStep 2688761 = 2016571) B2016571
theorem B3065705 : Blo 1592995 3065705 := bstep (se 2 (by rfl) ⟨1149639, by rfl⟩ : syracuseStep 3065705 = 2299279) B2299279
theorem B2688943 : Blo 1592995 2688943 := bstep (se 1 (by rfl) ⟨2016707, by rfl⟩ : syracuseStep 2688943 = 4033415) B4033415
theorem B4032443 : Blo 1592995 4032443 := bstep (se 1 (by rfl) ⟨3024332, by rfl⟩ : syracuseStep 4032443 = 6048665) B6048665
theorem B22972369 : Blo 1592995 22972369 := bstep (se 2 (by rfl) ⟨8614638, by rfl⟩ : syracuseStep 22972369 = 17229277) B17229277
theorem B2689031 : Blo 1592995 2689031 := bstep (se 1 (by rfl) ⟨2016773, by rfl⟩ : syracuseStep 2689031 = 4033547) B4033547
theorem B6055955 : Blo 1592995 6055955 := bstep (se 1 (by rfl) ⟨4541966, by rfl⟩ : syracuseStep 6055955 = 9083933) B9083933
theorem B8071325 : Blo 1592995 8071325 := bstep (se 3 (by rfl) ⟨1513373, by rfl⟩ : syracuseStep 8071325 = 3026747) B3026747
theorem B10209509 : Blo 1592995 10209509 := bstep (se 4 (by rfl) ⟨957141, by rfl⟩ : syracuseStep 10209509 = 1914283) B1914283
theorem B9079127 : Blo 1592995 9079127 := bstep (se 1 (by rfl) ⟨6809345, by rfl⟩ : syracuseStep 9079127 = 13618691) B13618691
theorem B2689375 : Blo 1592995 2689375 := bstep (se 1 (by rfl) ⟨2017031, by rfl⟩ : syracuseStep 2689375 = 4034063) B4034063
theorem B3025259 : Blo 1592995 3025259 := bstep (se 1 (by rfl) ⟨2268944, by rfl⟩ : syracuseStep 3025259 = 4537889) B4537889
theorem B2689463 : Blo 1592995 2689463 := bstep (se 1 (by rfl) ⟨2017097, by rfl⟩ : syracuseStep 2689463 = 4034195) B4034195
theorem B3025487 : Blo 1592995 3025487 := bstep (se 1 (by rfl) ⟨2269115, by rfl⟩ : syracuseStep 3025487 = 4538231) B4538231
theorem B4033223 : Blo 1592995 4033223 := bstep (se 1 (by rfl) ⟨3024917, by rfl⟩ : syracuseStep 4033223 = 6049835) B6049835
theorem B4033273 : Blo 1592995 4033273 := bstep (se 2 (by rfl) ⟨1512477, by rfl⟩ : syracuseStep 4033273 = 3024955) B3024955
theorem B5745401 : Blo 1592995 5745401 := bstep (se 2 (by rfl) ⟨2154525, by rfl⟩ : syracuseStep 5745401 = 4309051) B4309051
theorem B5376887 : Blo 1592995 5376887 := bstep (se 1 (by rfl) ⟨4032665, by rfl⟩ : syracuseStep 5376887 = 8065331) B8065331
theorem B6048695 : Blo 1592995 6048695 := bstep (se 1 (by rfl) ⟨4536521, by rfl⟩ : syracuseStep 6048695 = 9073043) B9073043
theorem B74591189 : Blo 1592995 74591189 := bstep (se 7 (by rfl) ⟨874115, by rfl⟩ : syracuseStep 74591189 = 1748231) B1748231
theorem B3025927 : Blo 1592995 3025927 := bstep (se 1 (by rfl) ⟨2269445, by rfl⟩ : syracuseStep 3025927 = 4538891) B4538891
theorem B2690057 : Blo 1592995 2690057 := bstep (se 2 (by rfl) ⟨1008771, by rfl⟩ : syracuseStep 2690057 = 2017543) B2017543
theorem B5377103 : Blo 1592995 5377103 := bstep (se 1 (by rfl) ⟨4032827, by rfl⟩ : syracuseStep 5377103 = 8065655) B8065655
theorem B5745745 : Blo 1592995 5745745 := bstep (se 2 (by rfl) ⟨2154654, by rfl⟩ : syracuseStep 5745745 = 4309309) B4309309
theorem B6466675 : Blo 1592995 6466675 := bstep (se 1 (by rfl) ⟨4850006, by rfl⟩ : syracuseStep 6466675 = 9700013) B9700013
theorem B2690219 : Blo 1592995 2690219 := bstep (se 1 (by rfl) ⟨2017664, by rfl⟩ : syracuseStep 2690219 = 4035329) B4035329
theorem B20974787 : Blo 1592995 20974787 := bstep (se 1 (by rfl) ⟨15731090, by rfl⟩ : syracuseStep 20974787 = 31462181) B31462181
theorem B3321043 : Blo 1592995 3321043 := bstep (se 1 (by rfl) ⟨2490782, by rfl⟩ : syracuseStep 3321043 = 4981565) B4981565
theorem B12111119 : Blo 1592995 12111119 := bstep (se 1 (by rfl) ⟨9083339, by rfl⟩ : syracuseStep 12111119 = 18166679) B18166679
theorem B34950437 : Blo 1592995 34950437 := bstep (se 4 (by rfl) ⟨3276603, by rfl⟩ : syracuseStep 34950437 = 6553207) B6553207
theorem B4033921 : Blo 1592995 4033921 := bstep (se 2 (by rfl) ⟨1512720, by rfl⟩ : syracuseStep 4033921 = 3025441) B3025441
theorem B9694637 : Blo 1592995 9694637 := bstep (se 3 (by rfl) ⟨1817744, by rfl⟩ : syracuseStep 9694637 = 3635489) B3635489
theorem B8072621 : Blo 1592995 8072621 := bstep (se 3 (by rfl) ⟨1513616, by rfl⟩ : syracuseStep 8072621 = 3027233) B3027233
theorem B5377481 : Blo 1592995 5377481 := bstep (se 2 (by rfl) ⟨2016555, by rfl⟩ : syracuseStep 5377481 = 4033111) B4033111
theorem B2690617 : Blo 1592995 2690617 := bstep (se 2 (by rfl) ⟨1008981, by rfl⟩ : syracuseStep 2690617 = 2017963) B2017963
theorem B1593007 : Blo 1592995 1593007 := bstep (se 1 (by rfl) ⟨1194755, by rfl⟩ : syracuseStep 1593007 = 2389511) B2389511
theorem B1593031 : Blo 1592995 1593031 := bstep (se 1 (by rfl) ⟨1194773, by rfl⟩ : syracuseStep 1593031 = 2389547) B2389547
theorem B2690759 : Blo 1592995 2690759 := bstep (se 1 (by rfl) ⟨2018069, by rfl⟩ : syracuseStep 2690759 = 4036139) B4036139
theorem B5377751 : Blo 1592995 5377751 := bstep (se 1 (by rfl) ⟨4033313, by rfl⟩ : syracuseStep 5377751 = 8066627) B8066627
theorem B1593051 : Blo 1592995 1593051 := bstep (se 1 (by rfl) ⟨1194788, by rfl⟩ : syracuseStep 1593051 = 2389577) B2389577
theorem B1593127 : Blo 1592995 1593127 := bstep (se 1 (by rfl) ⟨1194845, by rfl⟩ : syracuseStep 1593127 = 2389691) B2389691
theorem B1593167 : Blo 1592995 1593167 := bstep (se 1 (by rfl) ⟨1194875, by rfl⟩ : syracuseStep 1593167 = 2389751) B2389751
theorem B1593183 : Blo 1592995 1593183 := bstep (se 1 (by rfl) ⟨1194887, by rfl⟩ : syracuseStep 1593183 = 2389775) B2389775
theorem B3231593 : Blo 1592995 3231593 := bstep (se 2 (by rfl) ⟨1211847, by rfl⟩ : syracuseStep 3231593 = 2423695) B2423695
theorem B2690921 : Blo 1592995 2690921 := bstep (se 2 (by rfl) ⟨1009095, by rfl⟩ : syracuseStep 2690921 = 2018191) B2018191
theorem B1593211 : Blo 1592995 1593211 := bstep (se 1 (by rfl) ⟨1194908, by rfl⟩ : syracuseStep 1593211 = 2389817) B2389817
theorem B18411395 : Blo 1592995 18411395 := bstep (se 1 (by rfl) ⟨13808546, by rfl⟩ : syracuseStep 18411395 = 27617093) B27617093
theorem B1593263 : Blo 1592995 1593263 := bstep (se 1 (by rfl) ⟨1194947, by rfl⟩ : syracuseStep 1593263 = 2389895) B2389895
theorem B5377967 : Blo 1592995 5377967 := bstep (se 1 (by rfl) ⟨4033475, by rfl⟩ : syracuseStep 5377967 = 8066951) B8066951
theorem B26202041 : Blo 1592995 26202041 := bstep (se 2 (by rfl) ⟨9825765, by rfl⟩ : syracuseStep 26202041 = 19651531) B19651531
theorem B8179643 : Blo 1592995 8179643 := bstep (se 1 (by rfl) ⟨6134732, by rfl⟩ : syracuseStep 8179643 = 12269465) B12269465
theorem B1593287 : Blo 1592995 1593287 := bstep (se 1 (by rfl) ⟨1194965, by rfl⟩ : syracuseStep 1593287 = 2389931) B2389931
theorem B1593307 : Blo 1592995 1593307 := bstep (se 1 (by rfl) ⟨1194980, by rfl⟩ : syracuseStep 1593307 = 2389961) B2389961
theorem B1593383 : Blo 1592995 1593383 := bstep (se 1 (by rfl) ⟨1195037, by rfl⟩ : syracuseStep 1593383 = 2390075) B2390075
theorem B3026983 : Blo 1592995 3026983 := bstep (se 1 (by rfl) ⟨2270237, by rfl⟩ : syracuseStep 3026983 = 4540475) B4540475
theorem B6049849 : Blo 1592995 6049849 := bstep (se 2 (by rfl) ⟨2268693, by rfl⟩ : syracuseStep 6049849 = 4537387) B4537387
theorem B1593423 : Blo 1592995 1593423 := bstep (se 1 (by rfl) ⟨1195067, by rfl⟩ : syracuseStep 1593423 = 2390135) B2390135
theorem B1593439 : Blo 1592995 1593439 := bstep (se 1 (by rfl) ⟨1195079, by rfl⟩ : syracuseStep 1593439 = 2390159) B2390159
theorem B1593467 : Blo 1592995 1593467 := bstep (se 1 (by rfl) ⟨1195100, by rfl⟩ : syracuseStep 1593467 = 2390201) B2390201
theorem B4034731 : Blo 1592995 4034731 := bstep (se 1 (by rfl) ⟨3026048, by rfl⟩ : syracuseStep 4034731 = 6052097) B6052097
theorem B1593519 : Blo 1592995 1593519 := bstep (se 1 (by rfl) ⟨1195139, by rfl⟩ : syracuseStep 1593519 = 2390279) B2390279
theorem B1593543 : Blo 1592995 1593543 := bstep (se 1 (by rfl) ⟨1195157, by rfl⟩ : syracuseStep 1593543 = 2390315) B2390315
theorem B1593563 : Blo 1592995 1593563 := bstep (se 1 (by rfl) ⟨1195172, by rfl⟩ : syracuseStep 1593563 = 2390345) B2390345
theorem B2691319 : Blo 1592995 2691319 := bstep (se 1 (by rfl) ⟨2018489, by rfl⟩ : syracuseStep 2691319 = 4036979) B4036979
theorem B1593639 : Blo 1592995 1593639 := bstep (se 1 (by rfl) ⟨1195229, by rfl⟩ : syracuseStep 1593639 = 2390459) B2390459
theorem B43618621 : Blo 1592995 43618621 := bstep (se 3 (by rfl) ⟨8178491, by rfl⟩ : syracuseStep 43618621 = 16356983) B16356983
theorem B1593679 : Blo 1592995 1593679 := bstep (se 1 (by rfl) ⟨1195259, by rfl⟩ : syracuseStep 1593679 = 2390519) B2390519
theorem B1593695 : Blo 1592995 1593695 := bstep (se 1 (by rfl) ⟨1195271, by rfl⟩ : syracuseStep 1593695 = 2390543) B2390543
theorem B6050153 : Blo 1592995 6050153 := bstep (se 2 (by rfl) ⟨2268807, by rfl⟩ : syracuseStep 6050153 = 4537615) B4537615
theorem B1593723 : Blo 1592995 1593723 := bstep (se 1 (by rfl) ⟨1195292, by rfl⟩ : syracuseStep 1593723 = 2390585) B2390585
theorem B1593775 : Blo 1592995 1593775 := bstep (se 1 (by rfl) ⟨1195331, by rfl⟩ : syracuseStep 1593775 = 2390663) B2390663
theorem B2691515 : Blo 1592995 2691515 := bstep (se 1 (by rfl) ⟨2018636, by rfl⟩ : syracuseStep 2691515 = 4037273) B4037273
theorem B1593799 : Blo 1592995 1593799 := bstep (se 1 (by rfl) ⟨1195349, by rfl⟩ : syracuseStep 1593799 = 2390699) B2390699
theorem B1593819 : Blo 1592995 1593819 := bstep (se 1 (by rfl) ⟨1195364, by rfl⟩ : syracuseStep 1593819 = 2390729) B2390729
theorem B4035035 : Blo 1592995 4035035 := bstep (se 1 (by rfl) ⟨3026276, by rfl⟩ : syracuseStep 4035035 = 6052553) B6052553
theorem B3936755 : Blo 1592995 3936755 := bstep (se 1 (by rfl) ⟨2952566, by rfl⟩ : syracuseStep 3936755 = 5905133) B5905133
theorem B7270921 : Blo 1592995 7270921 := bstep (se 2 (by rfl) ⟨2726595, by rfl⟩ : syracuseStep 7270921 = 5453191) B5453191
theorem B1593895 : Blo 1592995 1593895 := bstep (se 1 (by rfl) ⟨1195421, by rfl⟩ : syracuseStep 1593895 = 2390843) B2390843
theorem B1593935 : Blo 1592995 1593935 := bstep (se 1 (by rfl) ⟨1195451, by rfl⟩ : syracuseStep 1593935 = 2390903) B2390903
theorem B1593951 : Blo 1592995 1593951 := bstep (se 1 (by rfl) ⟨1195463, by rfl⟩ : syracuseStep 1593951 = 2390927) B2390927
theorem B3584609 : Blo 1592995 3584609 := bstep (se 2 (by rfl) ⟨1344228, by rfl⟩ : syracuseStep 3584609 = 2688457) B2688457
theorem B1593979 : Blo 1592995 1593979 := bstep (se 1 (by rfl) ⟨1195484, by rfl⟩ : syracuseStep 1593979 = 2390969) B2390969
theorem B1594031 : Blo 1592995 1594031 := bstep (se 1 (by rfl) ⟨1195523, by rfl⟩ : syracuseStep 1594031 = 2391047) B2391047
theorem B139784885 : Blo 1592995 139784885 := bstep (se 5 (by rfl) ⟨6552416, by rfl⟩ : syracuseStep 139784885 = 13104833) B13104833
theorem B1594055 : Blo 1592995 1594055 := bstep (se 1 (by rfl) ⟨1195541, by rfl⟩ : syracuseStep 1594055 = 2391083) B2391083
theorem B6812369 : Blo 1592995 6812369 := bstep (se 2 (by rfl) ⟨2554638, by rfl⟩ : syracuseStep 6812369 = 5109277) B5109277
theorem B1594075 : Blo 1592995 1594075 := bstep (se 1 (by rfl) ⟨1195556, by rfl⟩ : syracuseStep 1594075 = 2391113) B2391113
theorem B1594151 : Blo 1592995 1594151 := bstep (se 1 (by rfl) ⟨1195613, by rfl⟩ : syracuseStep 1594151 = 2391227) B2391227
theorem B1594191 : Blo 1592995 1594191 := bstep (se 1 (by rfl) ⟨1195643, by rfl⟩ : syracuseStep 1594191 = 2391287) B2391287
theorem B1594207 : Blo 1592995 1594207 := bstep (se 1 (by rfl) ⟨1195655, by rfl⟩ : syracuseStep 1594207 = 2391311) B2391311
theorem B1594235 : Blo 1592995 1594235 := bstep (se 1 (by rfl) ⟨1195676, by rfl⟩ : syracuseStep 1594235 = 2391353) B2391353
theorem B20427673 : Blo 1592995 20427673 := bstep (se 2 (by rfl) ⟨7660377, by rfl⟩ : syracuseStep 20427673 = 15320755) B15320755
theorem B33182617 : Blo 1592995 33182617 := bstep (se 2 (by rfl) ⟨12443481, by rfl⟩ : syracuseStep 33182617 = 24886963) B24886963
theorem B1594287 : Blo 1592995 1594287 := bstep (se 1 (by rfl) ⟨1195715, by rfl⟩ : syracuseStep 1594287 = 2391431) B2391431
theorem B3584951 : Blo 1592995 3584951 := bstep (se 1 (by rfl) ⟨2688713, by rfl⟩ : syracuseStep 3584951 = 5377427) B5377427
theorem B1594311 : Blo 1592995 1594311 := bstep (se 1 (by rfl) ⟨1195733, by rfl⟩ : syracuseStep 1594311 = 2391467) B2391467
theorem B1594331 : Blo 1592995 1594331 := bstep (se 1 (by rfl) ⟨1195748, by rfl⟩ : syracuseStep 1594331 = 2391497) B2391497
theorem B8074241 : Blo 1592995 8074241 := bstep (se 2 (by rfl) ⟨3027840, by rfl⟩ : syracuseStep 8074241 = 6055681) B6055681
theorem B1594407 : Blo 1592995 1594407 := bstep (se 1 (by rfl) ⟨1195805, by rfl⟩ : syracuseStep 1594407 = 2391611) B2391611
theorem B19379249 : Blo 1592995 19379249 := bstep (se 2 (by rfl) ⟨7267218, by rfl⟩ : syracuseStep 19379249 = 14534437) B14534437
theorem B1594447 : Blo 1592995 1594447 := bstep (se 1 (by rfl) ⟨1195835, by rfl⟩ : syracuseStep 1594447 = 2391671) B2391671
theorem B1594463 : Blo 1592995 1594463 := bstep (se 1 (by rfl) ⟨1195847, by rfl⟩ : syracuseStep 1594463 = 2391695) B2391695
theorem B1594491 : Blo 1592995 1594491 := bstep (se 1 (by rfl) ⟨1195868, by rfl⟩ : syracuseStep 1594491 = 2391737) B2391737
theorem B1594543 : Blo 1592995 1594543 := bstep (se 1 (by rfl) ⟨1195907, by rfl⟩ : syracuseStep 1594543 = 2391815) B2391815
theorem B1594567 : Blo 1592995 1594567 := bstep (se 1 (by rfl) ⟨1195925, by rfl⟩ : syracuseStep 1594567 = 2391851) B2391851
theorem B26211529 : Blo 1592995 26211529 := bstep (se 2 (by rfl) ⟨9829323, by rfl⟩ : syracuseStep 26211529 = 19658647) B19658647
theorem B1594587 : Blo 1592995 1594587 := bstep (se 1 (by rfl) ⟨1195940, by rfl⟩ : syracuseStep 1594587 = 2391881) B2391881
theorem B8615159 : Blo 1592995 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B1594663 : Blo 1592995 1594663 := bstep (se 1 (by rfl) ⟨1195997, by rfl⟩ : syracuseStep 1594663 = 2391995) B2391995
theorem B2725193 : Blo 1592995 2725193 := bstep (se 2 (by rfl) ⟨1021947, by rfl⟩ : syracuseStep 2725193 = 2043895) B2043895
theorem B1594703 : Blo 1592995 1594703 := bstep (se 1 (by rfl) ⟨1196027, by rfl⟩ : syracuseStep 1594703 = 2392055) B2392055
theorem B1594719 : Blo 1592995 1594719 := bstep (se 1 (by rfl) ⟨1196039, by rfl⟩ : syracuseStep 1594719 = 2392079) B2392079
theorem B17470835 : Blo 1592995 17470835 := bstep (se 1 (by rfl) ⟨13103126, by rfl⟩ : syracuseStep 17470835 = 26206253) B26206253
theorem B1594747 : Blo 1592995 1594747 := bstep (se 1 (by rfl) ⟨1196060, by rfl⟩ : syracuseStep 1594747 = 2392121) B2392121
theorem B9074045 : Blo 1592995 9074045 := bstep (se 3 (by rfl) ⟨1701383, by rfl⟩ : syracuseStep 9074045 = 3402767) B3402767
theorem B1594799 : Blo 1592995 1594799 := bstep (se 1 (by rfl) ⟨1196099, by rfl⟩ : syracuseStep 1594799 = 2392199) B2392199
theorem B1594823 : Blo 1592995 1594823 := bstep (se 1 (by rfl) ⟨1196117, by rfl⟩ : syracuseStep 1594823 = 2392235) B2392235
theorem B2422235 : Blo 1592995 2422235 := bstep (se 1 (by rfl) ⟨1816676, by rfl⟩ : syracuseStep 2422235 = 3633353) B3633353
theorem B1594843 : Blo 1592995 1594843 := bstep (se 1 (by rfl) ⟨1196132, by rfl⟩ : syracuseStep 1594843 = 2392265) B2392265
theorem B3585545 : Blo 1592995 3585545 := bstep (se 2 (by rfl) ⟨1344579, by rfl⟩ : syracuseStep 3585545 = 2689159) B2689159
theorem B2553383 : Blo 1592995 2553383 := bstep (se 1 (by rfl) ⟨1915037, by rfl⟩ : syracuseStep 2553383 = 3830075) B3830075
theorem B1594919 : Blo 1592995 1594919 := bstep (se 1 (by rfl) ⟨1196189, by rfl⟩ : syracuseStep 1594919 = 2392379) B2392379
theorem B2389583 : Blo 1592995 2389583 := bstep (se 1 (by rfl) ⟨1792187, by rfl⟩ : syracuseStep 2389583 = 3584375) B3584375
theorem B1594959 : Blo 1592995 1594959 := bstep (se 1 (by rfl) ⟨1196219, by rfl⟩ : syracuseStep 1594959 = 2392439) B2392439
theorem B1594975 : Blo 1592995 1594975 := bstep (se 1 (by rfl) ⟨1196231, by rfl⟩ : syracuseStep 1594975 = 2392463) B2392463
theorem B3233377 : Blo 1592995 3233377 := bstep (se 2 (by rfl) ⟨1212516, by rfl⟩ : syracuseStep 3233377 = 2425033) B2425033
theorem B3831419 : Blo 1592995 3831419 := bstep (se 1 (by rfl) ⟨2873564, by rfl⟩ : syracuseStep 3831419 = 5747129) B5747129
theorem B2389703 : Blo 1592995 2389703 := bstep (se 1 (by rfl) ⟨1792277, by rfl⟩ : syracuseStep 2389703 = 3584555) B3584555
theorem B20436695 : Blo 1592995 20436695 := bstep (se 1 (by rfl) ⟨15327521, by rfl⟩ : syracuseStep 20436695 = 30655043) B30655043
theorem B2873161 : Blo 1592995 2873161 := bstep (se 2 (by rfl) ⟨1077435, by rfl⟩ : syracuseStep 2873161 = 2154871) B2154871
theorem B3585887 : Blo 1592995 3585887 := bstep (se 1 (by rfl) ⟨2689415, by rfl⟩ : syracuseStep 3585887 = 5378831) B5378831
theorem B2389865 : Blo 1592995 2389865 := bstep (se 2 (by rfl) ⟨896199, by rfl⟩ : syracuseStep 2389865 = 1792399) B1792399
theorem B4036513 : Blo 1592995 4036513 := bstep (se 2 (by rfl) ⟨1513692, by rfl⟩ : syracuseStep 4036513 = 3027385) B3027385
theorem B3831727 : Blo 1592995 3831727 := bstep (se 1 (by rfl) ⟨2873795, by rfl⟩ : syracuseStep 3831727 = 5747591) B5747591
theorem B2389943 : Blo 1592995 2389943 := bstep (se 1 (by rfl) ⟨1792457, by rfl⟩ : syracuseStep 2389943 = 3584915) B3584915
theorem B2389979 : Blo 1592995 2389979 := bstep (se 1 (by rfl) ⟨1792484, by rfl⟩ : syracuseStep 2389979 = 3584969) B3584969
theorem B6215687 : Blo 1592995 6215687 := bstep (se 1 (by rfl) ⟨4661765, by rfl⟩ : syracuseStep 6215687 = 9323531) B9323531
theorem B3586067 : Blo 1592995 3586067 := bstep (se 1 (by rfl) ⟨2689550, by rfl⟩ : syracuseStep 3586067 = 5379101) B5379101
theorem B5380343 : Blo 1592995 5380343 := bstep (se 1 (by rfl) ⟨4035257, by rfl⟩ : syracuseStep 5380343 = 8070515) B8070515
theorem B3586409 : Blo 1592995 3586409 := bstep (se 2 (by rfl) ⟨1344903, by rfl⟩ : syracuseStep 3586409 = 2689807) B2689807
theorem B2390447 : Blo 1592995 2390447 := bstep (se 1 (by rfl) ⟨1792835, by rfl⟩ : syracuseStep 2390447 = 3585671) B3585671
theorem B2390537 : Blo 1592995 2390537 := bstep (se 2 (by rfl) ⟨896451, by rfl⟩ : syracuseStep 2390537 = 1792903) B1792903
theorem B2390567 : Blo 1592995 2390567 := bstep (se 1 (by rfl) ⟨1792925, by rfl⟩ : syracuseStep 2390567 = 3585851) B3585851
theorem B30636589 : Blo 1592995 30636589 := bstep (se 3 (by rfl) ⟨5744360, by rfl⟩ : syracuseStep 30636589 = 11488721) B11488721
theorem B5380667 : Blo 1592995 5380667 := bstep (se 1 (by rfl) ⟨4035500, by rfl⟩ : syracuseStep 5380667 = 8071001) B8071001
theorem B2390651 : Blo 1592995 2390651 := bstep (se 1 (by rfl) ⟨1792988, by rfl⟩ : syracuseStep 2390651 = 3585977) B3585977
theorem B27605681 : Blo 1592995 27605681 := bstep (se 2 (by rfl) ⟨10352130, by rfl⟩ : syracuseStep 27605681 = 20704261) B20704261
theorem B11057849 : Blo 1592995 11057849 := bstep (se 2 (by rfl) ⟨4146693, by rfl⟩ : syracuseStep 11057849 = 8293387) B8293387
theorem B2390777 : Blo 1592995 2390777 := bstep (se 2 (by rfl) ⟨896541, by rfl⟩ : syracuseStep 2390777 = 1793083) B1793083
theorem B5380937 : Blo 1592995 5380937 := bstep (se 2 (by rfl) ⟨2017851, by rfl⟩ : syracuseStep 5380937 = 4035703) B4035703
theorem B2390879 : Blo 1592995 2390879 := bstep (se 1 (by rfl) ⟨1793159, by rfl⟩ : syracuseStep 2390879 = 3586319) B3586319
theorem B2390891 : Blo 1592995 2390891 := bstep (se 1 (by rfl) ⟨1793168, by rfl⟩ : syracuseStep 2390891 = 3586337) B3586337
theorem B3587003 : Blo 1592995 3587003 := bstep (se 1 (by rfl) ⟨2690252, by rfl⟩ : syracuseStep 3587003 = 5380505) B5380505
theorem B358390757 : Blo 1592995 358390757 := bstep (se 4 (by rfl) ⟨33599133, by rfl⟩ : syracuseStep 358390757 = 67198267) B67198267
theorem B9075685 : Blo 1592995 9075685 := bstep (se 4 (by rfl) ⟨850845, by rfl⟩ : syracuseStep 9075685 = 1701691) B1701691
theorem B3587129 : Blo 1592995 3587129 := bstep (se 2 (by rfl) ⟨1345173, by rfl⟩ : syracuseStep 3587129 = 2690347) B2690347
theorem B2391119 : Blo 1592995 2391119 := bstep (se 1 (by rfl) ⟨1793339, by rfl⟩ : syracuseStep 2391119 = 3586679) B3586679
theorem B12917879 : Blo 1592995 12917879 := bstep (se 1 (by rfl) ⟨9688409, by rfl⟩ : syracuseStep 12917879 = 19376819) B19376819
theorem B2153671 : Blo 1592995 2153671 := bstep (se 1 (by rfl) ⟨1615253, by rfl⟩ : syracuseStep 2153671 = 3230507) B3230507
theorem B2391239 : Blo 1592995 2391239 := bstep (se 1 (by rfl) ⟨1793429, by rfl⟩ : syracuseStep 2391239 = 3586859) B3586859
theorem B9075959 : Blo 1592995 9075959 := bstep (se 1 (by rfl) ⟨6806969, by rfl⟩ : syracuseStep 9075959 = 13613939) B13613939
theorem B2391401 : Blo 1592995 2391401 := bstep (se 2 (by rfl) ⟨896775, by rfl⟩ : syracuseStep 2391401 = 1793551) B1793551
theorem B2268523 : Blo 1592995 2268523 := bstep (se 1 (by rfl) ⟨1701392, by rfl⟩ : syracuseStep 2268523 = 3402785) B3402785
theorem B4308349 : Blo 1592995 4308349 := bstep (se 3 (by rfl) ⟨807815, by rfl⟩ : syracuseStep 4308349 = 1615631) B1615631
theorem B3587471 : Blo 1592995 3587471 := bstep (se 1 (by rfl) ⟨2690603, by rfl⟩ : syracuseStep 3587471 = 5381207) B5381207
theorem B2391479 : Blo 1592995 2391479 := bstep (se 1 (by rfl) ⟨1793609, by rfl⟩ : syracuseStep 2391479 = 3587219) B3587219
theorem B49053113 : Blo 1592995 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B8068571 : Blo 1592995 8068571 := bstep (se 1 (by rfl) ⟨6051428, by rfl⟩ : syracuseStep 8068571 = 12102857) B12102857
theorem B2391515 : Blo 1592995 2391515 := bstep (se 1 (by rfl) ⟨1793636, by rfl⟩ : syracuseStep 2391515 = 3587273) B3587273
theorem B9076211 : Blo 1592995 9076211 := bstep (se 1 (by rfl) ⟨6807158, by rfl⟩ : syracuseStep 9076211 = 13614317) B13614317
theorem B7658995 : Blo 1592995 7658995 := bstep (se 1 (by rfl) ⟨5744246, by rfl⟩ : syracuseStep 7658995 = 11488493) B11488493
theorem B2268751 : Blo 1592995 2268751 := bstep (se 1 (by rfl) ⟨1701563, by rfl⟩ : syracuseStep 2268751 = 3403127) B3403127
theorem B1793659 : Blo 1592995 1793659 := bstep (se 1 (by rfl) ⟨1345244, by rfl⟩ : syracuseStep 1793659 = 2690489) B2690489
theorem B9830011 : Blo 1592995 9830011 := bstep (se 1 (by rfl) ⟨7372508, by rfl⟩ : syracuseStep 9830011 = 14745017) B14745017
theorem B3587795 : Blo 1592995 3587795 := bstep (se 1 (by rfl) ⟨2690846, by rfl⟩ : syracuseStep 3587795 = 5381693) B5381693
theorem B33169133 : Blo 1592995 33169133 := bstep (se 3 (by rfl) ⟨6219212, by rfl⟩ : syracuseStep 33169133 = 12438425) B12438425
theorem B5103433 : Blo 1592995 5103433 := bstep (se 2 (by rfl) ⟨1913787, by rfl⟩ : syracuseStep 5103433 = 3827575) B3827575
theorem B6135625 : Blo 1592995 6135625 := bstep (se 2 (by rfl) ⟨2300859, by rfl⟩ : syracuseStep 6135625 = 4601719) B4601719
theorem B4538207 : Blo 1592995 4538207 := bstep (se 1 (by rfl) ⟨3403655, by rfl⟩ : syracuseStep 4538207 = 6807311) B6807311
theorem B16367491 : Blo 1592995 16367491 := bstep (se 1 (by rfl) ⟨12275618, by rfl⟩ : syracuseStep 16367491 = 24551237) B24551237
theorem B2391983 : Blo 1592995 2391983 := bstep (se 1 (by rfl) ⟨1793987, by rfl⟩ : syracuseStep 2391983 = 3587975) B3587975
theorem B5382071 : Blo 1592995 5382071 := bstep (se 1 (by rfl) ⟨4036553, by rfl⟩ : syracuseStep 5382071 = 8073107) B8073107
theorem B8069057 : Blo 1592995 8069057 := bstep (se 2 (by rfl) ⟨3025896, by rfl⟩ : syracuseStep 8069057 = 6051793) B6051793
theorem B2392169 : Blo 1592995 2392169 := bstep (se 2 (by rfl) ⟨897063, by rfl⟩ : syracuseStep 2392169 = 1794127) B1794127
theorem B1794343 : Blo 1592995 1794343 := bstep (se 1 (by rfl) ⟨1345757, by rfl⟩ : syracuseStep 1794343 = 2691515) B2691515
theorem B3588425 : Blo 1592995 3588425 := bstep (se 2 (by rfl) ⟨1345659, by rfl⟩ : syracuseStep 3588425 = 2691319) B2691319
theorem B3588443 : Blo 1592995 3588443 := bstep (se 1 (by rfl) ⟨2691332, by rfl⟩ : syracuseStep 3588443 = 5382665) B5382665
theorem B2392487 : Blo 1592995 2392487 := bstep (se 1 (by rfl) ⟨1794365, by rfl⟩ : syracuseStep 2392487 = 3588731) B3588731
theorem B17244677 : Blo 1592995 17244677 := bstep (se 4 (by rfl) ⟨1616688, by rfl⟩ : syracuseStep 17244677 = 3233377) B3233377
theorem B5382827 : Blo 1592995 5382827 := bstep (se 1 (by rfl) ⟨4037120, by rfl⟩ : syracuseStep 5382827 = 8074241) B8074241
theorem B12919499 : Blo 1592995 12919499 := bstep (se 1 (by rfl) ⟨9689624, by rfl⟩ : syracuseStep 12919499 = 19379249) B19379249
theorem B5743439 : Blo 1592995 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B1614823 : Blo 1592995 1614823 := bstep (se 1 (by rfl) ⟨1211117, by rfl⟩ : syracuseStep 1614823 = 2422235) B2422235
theorem B3736567 : Blo 1592995 3736567 := bstep (se 1 (by rfl) ⟨2802425, by rfl⟩ : syracuseStep 3736567 = 5604851) B5604851
theorem B11486245 : Blo 1592995 11486245 := bstep (se 4 (by rfl) ⟨1076835, by rfl⟩ : syracuseStep 11486245 = 2153671) B2153671
theorem B17712229 : Blo 1592995 17712229 := bstep (se 4 (by rfl) ⟨1660521, by rfl⟩ : syracuseStep 17712229 = 3321043) B3321043
theorem B13624463 : Blo 1592995 13624463 := bstep (se 1 (by rfl) ⟨10218347, by rfl⟩ : syracuseStep 13624463 = 20436695) B20436695
theorem B2688295 : Blo 1592995 2688295 := bstep (se 1 (by rfl) ⟨2016221, by rfl⟩ : syracuseStep 2688295 = 4032443) B4032443
theorem B12100913 : Blo 1592995 12100913 := bstep (se 2 (by rfl) ⟨4537842, by rfl⟩ : syracuseStep 12100913 = 9075685) B9075685
theorem B6809021 : Blo 1592995 6809021 := bstep (se 3 (by rfl) ⟨1276691, by rfl⟩ : syracuseStep 6809021 = 2553383) B2553383
theorem B7660993 : Blo 1592995 7660993 := bstep (se 2 (by rfl) ⟨2872872, by rfl⟩ : syracuseStep 7660993 = 5745745) B5745745
theorem B2016839 : Blo 1592995 2016839 := bstep (se 1 (by rfl) ⟨1512629, by rfl⟩ : syracuseStep 2016839 = 3025259) B3025259
theorem B34948705 : Blo 1592995 34948705 := bstep (se 2 (by rfl) ⟨13105764, by rfl⟩ : syracuseStep 34948705 = 26211529) B26211529
theorem B10217117 : Blo 1592995 10217117 := bstep (se 3 (by rfl) ⟨1915709, by rfl⟩ : syracuseStep 10217117 = 3831419) B3831419
theorem B2016991 : Blo 1592995 2016991 := bstep (se 1 (by rfl) ⟨1512743, by rfl⟩ : syracuseStep 2016991 = 3025487) B3025487
theorem B2688815 : Blo 1592995 2688815 := bstep (se 1 (by rfl) ⟨2016611, by rfl⟩ : syracuseStep 2688815 = 4033223) B4033223
theorem B3024697 : Blo 1592995 3024697 := bstep (se 2 (by rfl) ⟨1134261, by rfl⟩ : syracuseStep 3024697 = 2268523) B2268523
theorem B5744465 : Blo 1592995 5744465 := bstep (se 2 (by rfl) ⟨2154174, by rfl⟩ : syracuseStep 5744465 = 4308349) B4308349
theorem B88451021 : Blo 1592995 88451021 := bstep (se 3 (by rfl) ⟨16584566, by rfl⟩ : syracuseStep 88451021 = 33169133) B33169133
theorem B4032463 : Blo 1592995 4032463 := bstep (se 1 (by rfl) ⟨3024347, by rfl⟩ : syracuseStep 4032463 = 6048695) B6048695
theorem B49727459 : Blo 1592995 49727459 := bstep (se 1 (by rfl) ⟨37295594, by rfl⟩ : syracuseStep 49727459 = 74591189) B74591189
theorem B8611919 : Blo 1592995 8611919 := bstep (se 1 (by rfl) ⟨6458939, by rfl⟩ : syracuseStep 8611919 = 12917879) B12917879
theorem B3025001 : Blo 1592995 3025001 := bstep (se 2 (by rfl) ⟨1134375, by rfl⟩ : syracuseStep 3025001 = 2268751) B2268751
theorem B23300291 : Blo 1592995 23300291 := bstep (se 1 (by rfl) ⟨17475218, by rfl⟩ : syracuseStep 23300291 = 34950437) B34950437
theorem B12101885 : Blo 1592995 12101885 := bstep (se 3 (by rfl) ⟨2269103, by rfl⟩ : syracuseStep 12101885 = 4538207) B4538207
theorem B49097053 : Blo 1592995 49097053 := bstep (se 3 (by rfl) ⟨9205697, by rfl⟩ : syracuseStep 49097053 = 18411395) B18411395
theorem B17468027 : Blo 1592995 17468027 := bstep (se 1 (by rfl) ⟨13101020, by rfl⟩ : syracuseStep 17468027 = 26202041) B26202041
theorem B46574291 : Blo 1592995 46574291 := bstep (se 1 (by rfl) ⟨34930718, by rfl⟩ : syracuseStep 46574291 = 69861437) B69861437
theorem B4033435 : Blo 1592995 4033435 := bstep (se 1 (by rfl) ⟨3025076, by rfl⟩ : syracuseStep 4033435 = 6050153) B6050153
theorem B2690023 : Blo 1592995 2690023 := bstep (se 1 (by rfl) ⟨2017517, by rfl⟩ : syracuseStep 2690023 = 4035035) B4035035
theorem B2624503 : Blo 1592995 2624503 := bstep (se 1 (by rfl) ⟨1968377, by rfl⟩ : syracuseStep 2624503 = 3936755) B3936755
theorem B58158161 : Blo 1592995 58158161 := bstep (se 2 (by rfl) ⟨21809310, by rfl⟩ : syracuseStep 58158161 = 43618621) B43618621
theorem B6810763 : Blo 1592995 6810763 := bstep (se 1 (by rfl) ⟨5108072, by rfl⟩ : syracuseStep 6810763 = 10216145) B10216145
theorem B4541579 : Blo 1592995 4541579 := bstep (se 1 (by rfl) ⟨3406184, by rfl⟩ : syracuseStep 4541579 = 6812369) B6812369
theorem B8072459 : Blo 1592995 8072459 := bstep (se 1 (by rfl) ⟨6054344, by rfl⟩ : syracuseStep 8072459 = 12108689) B12108689
theorem B9694561 : Blo 1592995 9694561 := bstep (se 2 (by rfl) ⟨3635460, by rfl⟩ : syracuseStep 9694561 = 7270921) B7270921
theorem B40848785 : Blo 1592995 40848785 := bstep (se 2 (by rfl) ⟨15318294, by rfl⟩ : syracuseStep 40848785 = 30636589) B30636589
theorem B6049363 : Blo 1592995 6049363 := bstep (se 1 (by rfl) ⟨4537022, by rfl⟩ : syracuseStep 6049363 = 9074045) B9074045
theorem B7663187 : Blo 1592995 7663187 := bstep (se 1 (by rfl) ⟨5747390, by rfl⟩ : syracuseStep 7663187 = 11494781) B11494781
theorem B5377697 : Blo 1592995 5377697 := bstep (se 2 (by rfl) ⟨2016636, by rfl⟩ : syracuseStep 5377697 = 4033273) B4033273
theorem B3403451 : Blo 1592995 3403451 := bstep (se 1 (by rfl) ⟨2552588, by rfl⟩ : syracuseStep 3403451 = 5105177) B5105177
theorem B1593055 : Blo 1592995 1593055 := bstep (se 1 (by rfl) ⟨1194791, by rfl⟩ : syracuseStep 1593055 = 2389583) B2389583
theorem B7663339 : Blo 1592995 7663339 := bstep (se 1 (by rfl) ⟨5747504, by rfl⟩ : syracuseStep 7663339 = 11495009) B11495009
theorem B1593135 : Blo 1592995 1593135 := bstep (se 1 (by rfl) ⟨1194851, by rfl⟩ : syracuseStep 1593135 = 2389703) B2389703
theorem B2043803 : Blo 1592995 2043803 := bstep (se 1 (by rfl) ⟨1532852, by rfl⟩ : syracuseStep 2043803 = 3065705) B3065705
theorem B1593243 : Blo 1592995 1593243 := bstep (se 1 (by rfl) ⟨1194932, by rfl⟩ : syracuseStep 1593243 = 2389865) B2389865
theorem B1593295 : Blo 1592995 1593295 := bstep (se 1 (by rfl) ⟨1194971, by rfl⟩ : syracuseStep 1593295 = 2389943) B2389943
theorem B1593319 : Blo 1592995 1593319 := bstep (se 1 (by rfl) ⟨1194989, by rfl⟩ : syracuseStep 1593319 = 2389979) B2389979
theorem B4034569 : Blo 1592995 4034569 := bstep (se 2 (by rfl) ⟨1512963, by rfl⟩ : syracuseStep 4034569 = 3025927) B3025927
theorem B8622233 : Blo 1592995 8622233 := bstep (se 2 (by rfl) ⟨3233337, by rfl⟩ : syracuseStep 8622233 = 6466675) B6466675
theorem B1593631 : Blo 1592995 1593631 := bstep (se 1 (by rfl) ⟨1195223, by rfl⟩ : syracuseStep 1593631 = 2390447) B2390447
theorem B1593691 : Blo 1592995 1593691 := bstep (se 1 (by rfl) ⟨1195268, by rfl⟩ : syracuseStep 1593691 = 2390537) B2390537
theorem B1593711 : Blo 1592995 1593711 := bstep (se 1 (by rfl) ⟨1195283, by rfl⟩ : syracuseStep 1593711 = 2390567) B2390567
theorem B15323525 : Blo 1592995 15323525 := bstep (se 4 (by rfl) ⟨1436580, by rfl⟩ : syracuseStep 15323525 = 2873161) B2873161
theorem B1593767 : Blo 1592995 1593767 := bstep (se 1 (by rfl) ⟨1195325, by rfl⟩ : syracuseStep 1593767 = 2390651) B2390651
theorem B18403787 : Blo 1592995 18403787 := bstep (se 1 (by rfl) ⟨13802840, by rfl⟩ : syracuseStep 18403787 = 27605681) B27605681
theorem B1593851 : Blo 1592995 1593851 := bstep (se 1 (by rfl) ⟨1195388, by rfl⟩ : syracuseStep 1593851 = 2390777) B2390777
theorem B3830267 : Blo 1592995 3830267 := bstep (se 1 (by rfl) ⟨2872700, by rfl⟩ : syracuseStep 3830267 = 5745401) B5745401
theorem B5378561 : Blo 1592995 5378561 := bstep (se 2 (by rfl) ⟨2016960, by rfl⟩ : syracuseStep 5378561 = 4033921) B4033921
theorem B1593919 : Blo 1592995 1593919 := bstep (se 1 (by rfl) ⟨1195439, by rfl⟩ : syracuseStep 1593919 = 2390879) B2390879
theorem B1593927 : Blo 1592995 1593927 := bstep (se 1 (by rfl) ⟨1195445, by rfl⟩ : syracuseStep 1593927 = 2390891) B2390891
theorem B3584591 : Blo 1592995 3584591 := bstep (se 1 (by rfl) ⟨2688443, by rfl⟩ : syracuseStep 3584591 = 5376887) B5376887
theorem B10211993 : Blo 1592995 10211993 := bstep (se 2 (by rfl) ⟨3829497, by rfl⟩ : syracuseStep 10211993 = 7658995) B7658995
theorem B3584735 : Blo 1592995 3584735 := bstep (se 1 (by rfl) ⟨2688551, by rfl⟩ : syracuseStep 3584735 = 5377103) B5377103
theorem B1594079 : Blo 1592995 1594079 := bstep (se 1 (by rfl) ⟨1195559, by rfl⟩ : syracuseStep 1594079 = 2391119) B2391119
theorem B1594159 : Blo 1592995 1594159 := bstep (se 1 (by rfl) ⟨1195619, by rfl⟩ : syracuseStep 1594159 = 2391239) B2391239
theorem B6050639 : Blo 1592995 6050639 := bstep (se 1 (by rfl) ⟨4537979, by rfl⟩ : syracuseStep 6050639 = 9075959) B9075959
theorem B8074079 : Blo 1592995 8074079 := bstep (se 1 (by rfl) ⟨6055559, by rfl⟩ : syracuseStep 8074079 = 12111119) B12111119
theorem B1594267 : Blo 1592995 1594267 := bstep (se 1 (by rfl) ⟨1195700, by rfl⟩ : syracuseStep 1594267 = 2391401) B2391401
theorem B1594319 : Blo 1592995 1594319 := bstep (se 1 (by rfl) ⟨1195739, by rfl⟩ : syracuseStep 1594319 = 2391479) B2391479
theorem B3584987 : Blo 1592995 3584987 := bstep (se 1 (by rfl) ⟨2688740, by rfl⟩ : syracuseStep 3584987 = 5377481) B5377481
theorem B5379047 : Blo 1592995 5379047 := bstep (se 1 (by rfl) ⟨4034285, by rfl⟩ : syracuseStep 5379047 = 8068571) B8068571
theorem B1594343 : Blo 1592995 1594343 := bstep (se 1 (by rfl) ⟨1195757, by rfl⟩ : syracuseStep 1594343 = 2391515) B2391515
theorem B6050807 : Blo 1592995 6050807 := bstep (se 1 (by rfl) ⟨4538105, by rfl⟩ : syracuseStep 6050807 = 9076211) B9076211
theorem B6804577 : Blo 1592995 6804577 := bstep (se 2 (by rfl) ⟨2551716, by rfl⟩ : syracuseStep 6804577 = 5103433) B5103433
theorem B8180833 : Blo 1592995 8180833 := bstep (se 2 (by rfl) ⟨3067812, by rfl⟩ : syracuseStep 8180833 = 6135625) B6135625
theorem B3585167 : Blo 1592995 3585167 := bstep (se 1 (by rfl) ⟨2688875, by rfl⟩ : syracuseStep 3585167 = 5377751) B5377751
theorem B3585257 : Blo 1592995 3585257 := bstep (se 2 (by rfl) ⟨1344471, by rfl⟩ : syracuseStep 3585257 = 2688943) B2688943
theorem B5108969 : Blo 1592995 5108969 := bstep (se 2 (by rfl) ⟨1915863, by rfl⟩ : syracuseStep 5108969 = 3831727) B3831727
theorem B3585311 : Blo 1592995 3585311 := bstep (se 1 (by rfl) ⟨2688983, by rfl⟩ : syracuseStep 3585311 = 5377967) B5377967
theorem B1594655 : Blo 1592995 1594655 := bstep (se 1 (by rfl) ⟨1195991, by rfl⟩ : syracuseStep 1594655 = 2391983) B2391983
theorem B5453095 : Blo 1592995 5453095 := bstep (se 1 (by rfl) ⟨4089821, by rfl⟩ : syracuseStep 5453095 = 8179643) B8179643
theorem B5379371 : Blo 1592995 5379371 := bstep (se 1 (by rfl) ⟨4034528, by rfl⟩ : syracuseStep 5379371 = 8069057) B8069057
theorem B1594715 : Blo 1592995 1594715 := bstep (se 1 (by rfl) ⟨1196036, by rfl⟩ : syracuseStep 1594715 = 2392073) B2392073
theorem B1594735 : Blo 1592995 1594735 := bstep (se 1 (by rfl) ⟨1196051, by rfl⟩ : syracuseStep 1594735 = 2392103) B2392103
theorem B4035977 : Blo 1592995 4035977 := bstep (se 2 (by rfl) ⟨1513491, by rfl⟩ : syracuseStep 4035977 = 3026983) B3026983
theorem B8066465 : Blo 1592995 8066465 := bstep (se 2 (by rfl) ⟨3024924, by rfl⟩ : syracuseStep 8066465 = 6049849) B6049849
theorem B1594791 : Blo 1592995 1594791 := bstep (se 1 (by rfl) ⟨1196093, by rfl⟩ : syracuseStep 1594791 = 2392187) B2392187
theorem B4036027 : Blo 1592995 4036027 := bstep (se 1 (by rfl) ⟨3027020, by rfl⟩ : syracuseStep 4036027 = 6054041) B6054041
theorem B1594875 : Blo 1592995 1594875 := bstep (se 1 (by rfl) ⟨1196156, by rfl⟩ : syracuseStep 1594875 = 2392313) B2392313
theorem B5379641 : Blo 1592995 5379641 := bstep (se 2 (by rfl) ⟨2017365, by rfl⟩ : syracuseStep 5379641 = 4034731) B4034731
theorem B1594943 : Blo 1592995 1594943 := bstep (se 1 (by rfl) ⟨1196207, by rfl⟩ : syracuseStep 1594943 = 2392415) B2392415
theorem B1594951 : Blo 1592995 1594951 := bstep (se 1 (by rfl) ⟨1196213, by rfl⟩ : syracuseStep 1594951 = 2392427) B2392427
theorem B2389739 : Blo 1592995 2389739 := bstep (se 1 (by rfl) ⟨1792304, by rfl⟩ : syracuseStep 2389739 = 3584609) B3584609
theorem B4036331 : Blo 1592995 4036331 := bstep (se 1 (by rfl) ⟨3027248, by rfl⟩ : syracuseStep 4036331 = 6054497) B6054497
theorem B93189923 : Blo 1592995 93189923 := bstep (se 1 (by rfl) ⟨69892442, by rfl⟩ : syracuseStep 93189923 = 139784885) B139784885
theorem B3585833 : Blo 1592995 3585833 := bstep (se 2 (by rfl) ⟨1344687, by rfl⟩ : syracuseStep 3585833 = 2689375) B2689375
theorem B2389967 : Blo 1592995 2389967 := bstep (se 1 (by rfl) ⟨1792475, by rfl⟩ : syracuseStep 2389967 = 3584951) B3584951
theorem B1792219 : Blo 1592995 1792219 := bstep (se 1 (by rfl) ⟨1344164, by rfl⟩ : syracuseStep 1792219 = 2688329) B2688329
theorem B1816795 : Blo 1592995 1816795 := bstep (se 1 (by rfl) ⟨1362596, by rfl⟩ : syracuseStep 1816795 = 2725193) B2725193
theorem B11647223 : Blo 1592995 11647223 := bstep (se 1 (by rfl) ⟨8735417, by rfl⟩ : syracuseStep 11647223 = 17470835) B17470835
theorem B36804887 : Blo 1592995 36804887 := bstep (se 1 (by rfl) ⟨27603665, by rfl⟩ : syracuseStep 36804887 = 55207331) B55207331
theorem B2390363 : Blo 1592995 2390363 := bstep (se 1 (by rfl) ⟨1792772, by rfl⟩ : syracuseStep 2390363 = 3585545) B3585545
theorem B6052279 : Blo 1592995 6052279 := bstep (se 1 (by rfl) ⟨4539209, by rfl⟩ : syracuseStep 6052279 = 9078419) B9078419
theorem B1792507 : Blo 1592995 1792507 := bstep (se 1 (by rfl) ⟨1344380, by rfl⟩ : syracuseStep 1792507 = 2688761) B2688761
theorem B27236897 : Blo 1592995 27236897 := bstep (se 2 (by rfl) ⟨10213836, by rfl⟩ : syracuseStep 27236897 = 20427673) B20427673
theorem B44243489 : Blo 1592995 44243489 := bstep (se 2 (by rfl) ⟨16591308, by rfl⟩ : syracuseStep 44243489 = 33182617) B33182617
theorem B2390591 : Blo 1592995 2390591 := bstep (se 1 (by rfl) ⟨1792943, by rfl⟩ : syracuseStep 2390591 = 3585887) B3585887
theorem B4143791 : Blo 1592995 4143791 := bstep (se 1 (by rfl) ⟨3107843, by rfl⟩ : syracuseStep 4143791 = 6215687) B6215687
theorem B1792687 : Blo 1592995 1792687 := bstep (se 1 (by rfl) ⟨1344515, by rfl⟩ : syracuseStep 1792687 = 2689031) B2689031
theorem B2390711 : Blo 1592995 2390711 := bstep (se 1 (by rfl) ⟨1793033, by rfl⟩ : syracuseStep 2390711 = 3586067) B3586067
theorem B4037303 : Blo 1592995 4037303 := bstep (se 1 (by rfl) ⟨3027977, by rfl⟩ : syracuseStep 4037303 = 6055955) B6055955
theorem B5380883 : Blo 1592995 5380883 := bstep (se 1 (by rfl) ⟨4035662, by rfl⟩ : syracuseStep 5380883 = 8071325) B8071325
theorem B6806339 : Blo 1592995 6806339 := bstep (se 1 (by rfl) ⟨5104754, by rfl⟩ : syracuseStep 6806339 = 10209509) B10209509
theorem B3586895 : Blo 1592995 3586895 := bstep (se 1 (by rfl) ⟨2690171, by rfl⟩ : syracuseStep 3586895 = 5380343) B5380343
theorem B6052751 : Blo 1592995 6052751 := bstep (se 1 (by rfl) ⟨4539563, by rfl⟩ : syracuseStep 6052751 = 9079127) B9079127
theorem B2390939 : Blo 1592995 2390939 := bstep (se 1 (by rfl) ⟨1793204, by rfl⟩ : syracuseStep 2390939 = 3586409) B3586409
theorem B1792975 : Blo 1592995 1792975 := bstep (se 1 (by rfl) ⟨1344731, by rfl⟩ : syracuseStep 1792975 = 2689463) B2689463
theorem B3587111 : Blo 1592995 3587111 := bstep (se 1 (by rfl) ⟨2690333, by rfl⟩ : syracuseStep 3587111 = 5380667) B5380667
theorem B7371899 : Blo 1592995 7371899 := bstep (se 1 (by rfl) ⟨5528924, by rfl⟩ : syracuseStep 7371899 = 11057849) B11057849
theorem B3587291 : Blo 1592995 3587291 := bstep (se 1 (by rfl) ⟨2690468, by rfl⟩ : syracuseStep 3587291 = 5380937) B5380937
theorem B2391335 : Blo 1592995 2391335 := bstep (se 1 (by rfl) ⟨1793501, by rfl⟩ : syracuseStep 2391335 = 3587003) B3587003
theorem B238927171 : Blo 1592995 238927171 := bstep (se 1 (by rfl) ⟨179195378, by rfl⟩ : syracuseStep 238927171 = 358390757) B358390757
theorem B1793371 : Blo 1592995 1793371 := bstep (se 1 (by rfl) ⟨1345028, by rfl⟩ : syracuseStep 1793371 = 2690057) B2690057
theorem B87293285 : Blo 1592995 87293285 := bstep (se 4 (by rfl) ⟨8183745, by rfl⟩ : syracuseStep 87293285 = 16367491) B16367491
theorem B2391419 : Blo 1592995 2391419 := bstep (se 1 (by rfl) ⟨1793564, by rfl⟩ : syracuseStep 2391419 = 3587129) B3587129
theorem B3587489 : Blo 1592995 3587489 := bstep (se 2 (by rfl) ⟨1345308, by rfl⟩ : syracuseStep 3587489 = 2690617) B2690617
theorem B1793479 : Blo 1592995 1793479 := bstep (se 1 (by rfl) ⟨1345109, by rfl⟩ : syracuseStep 1793479 = 2690219) B2690219
theorem B13983191 : Blo 1592995 13983191 := bstep (se 1 (by rfl) ⟨10487393, by rfl⟩ : syracuseStep 13983191 = 20974787) B20974787
theorem B2391545 : Blo 1592995 2391545 := bstep (se 2 (by rfl) ⟨896829, by rfl⟩ : syracuseStep 2391545 = 1793659) B1793659
theorem B13106681 : Blo 1592995 13106681 := bstep (se 2 (by rfl) ⟨4915005, by rfl⟩ : syracuseStep 13106681 = 9830011) B9830011
theorem B2391647 : Blo 1592995 2391647 := bstep (se 1 (by rfl) ⟨1793735, by rfl⟩ : syracuseStep 2391647 = 3587471) B3587471
theorem B6463091 : Blo 1592995 6463091 := bstep (se 1 (by rfl) ⟨4847318, by rfl⟩ : syracuseStep 6463091 = 9694637) B9694637
theorem B5381747 : Blo 1592995 5381747 := bstep (se 1 (by rfl) ⟨4036310, by rfl⟩ : syracuseStep 5381747 = 8072621) B8072621
theorem B32702075 : Blo 1592995 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B1793839 : Blo 1592995 1793839 := bstep (se 1 (by rfl) ⟨1345379, by rfl⟩ : syracuseStep 1793839 = 2690759) B2690759
theorem B2391863 : Blo 1592995 2391863 := bstep (se 1 (by rfl) ⟨1793897, by rfl⟩ : syracuseStep 2391863 = 3587795) B3587795
theorem B5382017 : Blo 1592995 5382017 := bstep (se 2 (by rfl) ⟨2018256, by rfl⟩ : syracuseStep 5382017 = 4036513) B4036513
theorem B2154395 : Blo 1592995 2154395 := bstep (se 1 (by rfl) ⟨1615796, by rfl⟩ : syracuseStep 2154395 = 3231593) B3231593
theorem B1793947 : Blo 1592995 1793947 := bstep (se 1 (by rfl) ⟨1345460, by rfl⟩ : syracuseStep 1793947 = 2690921) B2690921
theorem B30629825 : Blo 1592995 30629825 := bstep (se 2 (by rfl) ⟨11486184, by rfl⟩ : syracuseStep 30629825 = 22972369) B22972369
theorem B3588047 : Blo 1592995 3588047 := bstep (se 1 (by rfl) ⟨2691035, by rfl⟩ : syracuseStep 3588047 = 5382071) B5382071
theorem B2392283 : Blo 1592995 2392283 := bstep (se 1 (by rfl) ⟨1794212, by rfl⟩ : syracuseStep 2392283 = 3588425) B3588425
theorem B2392295 : Blo 1592995 2392295 := bstep (se 1 (by rfl) ⟨1794221, by rfl⟩ : syracuseStep 2392295 = 3588443) B3588443
theorem B10215683 : Blo 1592995 10215683 := bstep (se 1 (by rfl) ⟨7661762, by rfl⟩ : syracuseStep 10215683 = 15323525) B15323525
theorem B2392457 : Blo 1592995 2392457 := bstep (se 2 (by rfl) ⟨897171, by rfl⟩ : syracuseStep 2392457 = 1794343) B1794343
theorem B6807995 : Blo 1592995 6807995 := bstep (se 1 (by rfl) ⟨5105996, by rfl⟩ : syracuseStep 6807995 = 10211993) B10211993
theorem B3588551 : Blo 1592995 3588551 := bstep (se 1 (by rfl) ⟨2691413, by rfl⟩ : syracuseStep 3588551 = 5382827) B5382827
theorem B65462737 : Blo 1592995 65462737 := bstep (se 2 (by rfl) ⟨24548526, by rfl⟩ : syracuseStep 65462737 = 49097053) B49097053
theorem B5382719 : Blo 1592995 5382719 := bstep (se 1 (by rfl) ⟨4037039, by rfl⟩ : syracuseStep 5382719 = 8074079) B8074079
theorem B8069705 : Blo 1592995 8069705 := bstep (se 2 (by rfl) ⟨3026139, by rfl⟩ : syracuseStep 8069705 = 6052279) B6052279
theorem B4539347 : Blo 1592995 4539347 := bstep (se 1 (by rfl) ⟨3404510, by rfl⟩ : syracuseStep 4539347 = 6809021) B6809021
theorem B58967347 : Blo 1592995 58967347 := bstep (se 1 (by rfl) ⟨44225510, by rfl⟩ : syracuseStep 58967347 = 88451021) B88451021
theorem B3499337 : Blo 1592995 3499337 := bstep (se 2 (by rfl) ⟨1312251, by rfl⟩ : syracuseStep 3499337 = 2624503) B2624503
theorem B2016667 : Blo 1592995 2016667 := bstep (se 1 (by rfl) ⟨1512500, by rfl⟩ : syracuseStep 2016667 = 3025001) B3025001
theorem B15533527 : Blo 1592995 15533527 := bstep (se 1 (by rfl) ⟨11650145, by rfl⟩ : syracuseStep 15533527 = 23300291) B23300291
theorem B24536591 : Blo 1592995 24536591 := bstep (se 1 (by rfl) ⟨18402443, by rfl⟩ : syracuseStep 24536591 = 36804887) B36804887
theorem B2762527 : Blo 1592995 2762527 := bstep (se 1 (by rfl) ⟨2071895, by rfl⟩ : syracuseStep 2762527 = 4143791) B4143791
theorem B31049527 : Blo 1592995 31049527 := bstep (se 1 (by rfl) ⟨23287145, by rfl⟩ : syracuseStep 31049527 = 46574291) B46574291
theorem B46598273 : Blo 1592995 46598273 := bstep (se 2 (by rfl) ⟨17474352, by rfl⟩ : syracuseStep 46598273 = 34948705) B34948705
theorem B27232523 : Blo 1592995 27232523 := bstep (se 1 (by rfl) ⟨20424392, by rfl⟩ : syracuseStep 27232523 = 40848785) B40848785
theorem B2689321 : Blo 1592995 2689321 := bstep (se 2 (by rfl) ⟨1008495, by rfl⟩ : syracuseStep 2689321 = 2016991) B2016991
theorem B10217785 : Blo 1592995 10217785 := bstep (se 2 (by rfl) ⟨3831669, by rfl⟩ : syracuseStep 10217785 = 7663339) B7663339
theorem B5450141 : Blo 1592995 5450141 := bstep (se 3 (by rfl) ⟨1021901, by rfl⟩ : syracuseStep 5450141 = 2043803) B2043803
theorem B5745053 : Blo 1592995 5745053 := bstep (se 3 (by rfl) ⟨1077197, by rfl⟩ : syracuseStep 5745053 = 2154395) B2154395
theorem B4032929 : Blo 1592995 4032929 := bstep (se 2 (by rfl) ⟨1512348, by rfl⟩ : syracuseStep 4032929 = 3024697) B3024697
theorem B21801383 : Blo 1592995 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B8612389 : Blo 1592995 8612389 := bstep (se 4 (by rfl) ⟨807411, by rfl⟩ : syracuseStep 8612389 = 1614823) B1614823
theorem B5376617 : Blo 1592995 5376617 := bstep (se 2 (by rfl) ⟨2016231, by rfl⟩ : syracuseStep 5376617 = 4032463) B4032463
theorem B11496451 : Blo 1592995 11496451 := bstep (se 1 (by rfl) ⟨8622338, by rfl⟩ : syracuseStep 11496451 = 17244677) B17244677
theorem B8612999 : Blo 1592995 8612999 := bstep (se 1 (by rfl) ⟨6459749, by rfl⟩ : syracuseStep 8612999 = 12919499) B12919499
theorem B4033759 : Blo 1592995 4033759 := bstep (se 1 (by rfl) ⟨3025319, by rfl⟩ : syracuseStep 4033759 = 6050639) B6050639
theorem B3828959 : Blo 1592995 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B4033871 : Blo 1592995 4033871 := bstep (se 1 (by rfl) ⟨3025403, by rfl⟩ : syracuseStep 4033871 = 6050807) B6050807
theorem B2690651 : Blo 1592995 2690651 := bstep (se 1 (by rfl) ⟨2017988, by rfl⟩ : syracuseStep 2690651 = 4035977) B4035977
theorem B5377643 : Blo 1592995 5377643 := bstep (se 1 (by rfl) ⟨4033232, by rfl⟩ : syracuseStep 5377643 = 8066465) B8066465
theorem B1593159 : Blo 1592995 1593159 := bstep (se 1 (by rfl) ⟨1194869, by rfl⟩ : syracuseStep 1593159 = 2389739) B2389739
theorem B2690887 : Blo 1592995 2690887 := bstep (se 1 (by rfl) ⟨2018165, by rfl⟩ : syracuseStep 2690887 = 4036331) B4036331
theorem B5377913 : Blo 1592995 5377913 := bstep (se 2 (by rfl) ⟨2016717, by rfl⟩ : syracuseStep 5377913 = 4033435) B4033435
theorem B3829643 : Blo 1592995 3829643 := bstep (se 1 (by rfl) ⟨2872232, by rfl⟩ : syracuseStep 3829643 = 5744465) B5744465
theorem B1593311 : Blo 1592995 1593311 := bstep (se 1 (by rfl) ⟨1194983, by rfl⟩ : syracuseStep 1593311 = 2389967) B2389967
theorem B15314993 : Blo 1592995 15314993 := bstep (se 2 (by rfl) ⟨5743122, by rfl⟩ : syracuseStep 15314993 = 11486245) B11486245
theorem B9072769 : Blo 1592995 9072769 := bstep (se 2 (by rfl) ⟨3402288, by rfl⟩ : syracuseStep 9072769 = 6804577) B6804577
theorem B10907777 : Blo 1592995 10907777 := bstep (se 2 (by rfl) ⟨4090416, by rfl⟩ : syracuseStep 10907777 = 8180833) B8180833
theorem B9081017 : Blo 1592995 9081017 := bstep (se 2 (by rfl) ⟨3405381, by rfl⟩ : syracuseStep 9081017 = 6810763) B6810763
theorem B5378237 : Blo 1592995 5378237 := bstep (se 3 (by rfl) ⟨1008419, by rfl⟩ : syracuseStep 5378237 = 2016839) B2016839
theorem B1593575 : Blo 1592995 1593575 := bstep (se 1 (by rfl) ⟨1195181, by rfl⟩ : syracuseStep 1593575 = 2390363) B2390363
theorem B18157931 : Blo 1592995 18157931 := bstep (se 1 (by rfl) ⟨13618448, by rfl⟩ : syracuseStep 18157931 = 27236897) B27236897
theorem B29495659 : Blo 1592995 29495659 := bstep (se 1 (by rfl) ⟨22121744, by rfl⟩ : syracuseStep 29495659 = 44243489) B44243489
theorem B1593727 : Blo 1592995 1593727 := bstep (se 1 (by rfl) ⟨1195295, by rfl⟩ : syracuseStep 1593727 = 2390591) B2390591
theorem B3584393 : Blo 1592995 3584393 := bstep (se 2 (by rfl) ⟨1344147, by rfl⟩ : syracuseStep 3584393 = 2688295) B2688295
theorem B7270793 : Blo 1592995 7270793 := bstep (se 2 (by rfl) ⟨2726547, by rfl⟩ : syracuseStep 7270793 = 5453095) B5453095
theorem B11645351 : Blo 1592995 11645351 := bstep (se 1 (by rfl) ⟨8734013, by rfl⟩ : syracuseStep 11645351 = 17468027) B17468027
theorem B1593807 : Blo 1592995 1593807 := bstep (se 1 (by rfl) ⟨1195355, by rfl⟩ : syracuseStep 1593807 = 2390711) B2390711
theorem B2691535 : Blo 1592995 2691535 := bstep (se 1 (by rfl) ⟨2018651, by rfl⟩ : syracuseStep 2691535 = 4037303) B4037303
theorem B4035167 : Blo 1592995 4035167 := bstep (se 1 (by rfl) ⟨3026375, by rfl⟩ : syracuseStep 4035167 = 6052751) B6052751
theorem B1593959 : Blo 1592995 1593959 := bstep (se 1 (by rfl) ⟨1195469, by rfl⟩ : syracuseStep 1593959 = 2390939) B2390939
theorem B3027719 : Blo 1592995 3027719 := bstep (se 1 (by rfl) ⟨2270789, by rfl⟩ : syracuseStep 3027719 = 4541579) B4541579
theorem B8065817 : Blo 1592995 8065817 := bstep (se 2 (by rfl) ⟨3024681, by rfl⟩ : syracuseStep 8065817 = 6049363) B6049363
theorem B1594223 : Blo 1592995 1594223 := bstep (se 1 (by rfl) ⟨1195667, by rfl⟩ : syracuseStep 1594223 = 2391335) B2391335
theorem B1594279 : Blo 1592995 1594279 := bstep (se 1 (by rfl) ⟨1195709, by rfl⟩ : syracuseStep 1594279 = 2391419) B2391419
theorem B1594363 : Blo 1592995 1594363 := bstep (se 1 (by rfl) ⟨1195772, by rfl⟩ : syracuseStep 1594363 = 2391545) B2391545
theorem B8737787 : Blo 1592995 8737787 := bstep (se 1 (by rfl) ⟨6553340, by rfl⟩ : syracuseStep 8737787 = 13106681) B13106681
theorem B5108791 : Blo 1592995 5108791 := bstep (se 1 (by rfl) ⟨3831593, by rfl⟩ : syracuseStep 5108791 = 7663187) B7663187
theorem B1594431 : Blo 1592995 1594431 := bstep (se 1 (by rfl) ⟨1195823, by rfl⟩ : syracuseStep 1594431 = 2391647) B2391647
theorem B3585131 : Blo 1592995 3585131 := bstep (se 1 (by rfl) ⟨2688848, by rfl⟩ : syracuseStep 3585131 = 5377697) B5377697
theorem B1594575 : Blo 1592995 1594575 := bstep (se 1 (by rfl) ⟨1195931, by rfl⟩ : syracuseStep 1594575 = 2391863) B2391863
theorem B19928357 : Blo 1592995 19928357 := bstep (se 4 (by rfl) ⟨1868283, by rfl⟩ : syracuseStep 19928357 = 3736567) B3736567
theorem B20419883 : Blo 1592995 20419883 := bstep (se 1 (by rfl) ⟨15314912, by rfl⟩ : syracuseStep 20419883 = 30629825) B30629825
theorem B5379425 : Blo 1592995 5379425 := bstep (se 2 (by rfl) ⟨2017284, by rfl⟩ : syracuseStep 5379425 = 4034569) B4034569
theorem B1594779 : Blo 1592995 1594779 := bstep (se 1 (by rfl) ⟨1196084, by rfl⟩ : syracuseStep 1594779 = 2392169) B2392169
theorem B5748155 : Blo 1592995 5748155 := bstep (se 1 (by rfl) ⟨4311116, by rfl⟩ : syracuseStep 5748155 = 8622233) B8622233
theorem B1594991 : Blo 1592995 1594991 := bstep (se 1 (by rfl) ⟨1196243, by rfl⟩ : syracuseStep 1594991 = 2392487) B2392487
theorem B2389625 : Blo 1592995 2389625 := bstep (se 2 (by rfl) ⟨896109, by rfl⟩ : syracuseStep 2389625 = 1792219) B1792219
theorem B2422393 : Blo 1592995 2422393 := bstep (se 2 (by rfl) ⟨908397, by rfl⟩ : syracuseStep 2422393 = 1816795) B1816795
theorem B12269191 : Blo 1592995 12269191 := bstep (se 1 (by rfl) ⟨9201893, by rfl⟩ : syracuseStep 12269191 = 18403787) B18403787
theorem B2553511 : Blo 1592995 2553511 := bstep (se 1 (by rfl) ⟨1915133, by rfl⟩ : syracuseStep 2553511 = 3830267) B3830267
theorem B3585707 : Blo 1592995 3585707 := bstep (se 1 (by rfl) ⟨2689280, by rfl⟩ : syracuseStep 3585707 = 5378561) B5378561
theorem B2389727 : Blo 1592995 2389727 := bstep (se 1 (by rfl) ⟨1792295, by rfl⟩ : syracuseStep 2389727 = 3584591) B3584591
theorem B2389823 : Blo 1592995 2389823 := bstep (se 1 (by rfl) ⟨1792367, by rfl⟩ : syracuseStep 2389823 = 3584735) B3584735
theorem B2389991 : Blo 1592995 2389991 := bstep (se 1 (by rfl) ⟨1792493, by rfl⟩ : syracuseStep 2389991 = 3584987) B3584987
theorem B3586031 : Blo 1592995 3586031 := bstep (se 1 (by rfl) ⟨2689523, by rfl⟩ : syracuseStep 3586031 = 5379047) B5379047
theorem B2390009 : Blo 1592995 2390009 := bstep (se 2 (by rfl) ⟨896253, by rfl⟩ : syracuseStep 2390009 = 1792507) B1792507
theorem B2390111 : Blo 1592995 2390111 := bstep (se 1 (by rfl) ⟨1792583, by rfl⟩ : syracuseStep 2390111 = 3585167) B3585167
theorem B9082975 : Blo 1592995 9082975 := bstep (se 1 (by rfl) ⟨6812231, by rfl⟩ : syracuseStep 9082975 = 13624463) B13624463
theorem B2390171 : Blo 1592995 2390171 := bstep (se 1 (by rfl) ⟨1792628, by rfl⟩ : syracuseStep 2390171 = 3585257) B3585257
theorem B3405979 : Blo 1592995 3405979 := bstep (se 1 (by rfl) ⟨2554484, by rfl⟩ : syracuseStep 3405979 = 5108969) B5108969
theorem B2390207 : Blo 1592995 2390207 := bstep (se 1 (by rfl) ⟨1792655, by rfl⟩ : syracuseStep 2390207 = 3585311) B3585311
theorem B3586247 : Blo 1592995 3586247 := bstep (se 1 (by rfl) ⟨2689685, by rfl⟩ : syracuseStep 3586247 = 5379371) B5379371
theorem B8067275 : Blo 1592995 8067275 := bstep (se 1 (by rfl) ⟨6050456, by rfl⟩ : syracuseStep 8067275 = 12100913) B12100913
theorem B2390249 : Blo 1592995 2390249 := bstep (se 2 (by rfl) ⟨896343, by rfl⟩ : syracuseStep 2390249 = 1792687) B1792687
theorem B3586427 : Blo 1592995 3586427 := bstep (se 1 (by rfl) ⟨2689820, by rfl⟩ : syracuseStep 3586427 = 5379641) B5379641
theorem B62126615 : Blo 1592995 62126615 := bstep (se 1 (by rfl) ⟨46594961, by rfl⟩ : syracuseStep 62126615 = 93189923) B93189923
theorem B2390555 : Blo 1592995 2390555 := bstep (se 1 (by rfl) ⟨1792916, by rfl⟩ : syracuseStep 2390555 = 3585833) B3585833
theorem B1792543 : Blo 1592995 1792543 := bstep (se 1 (by rfl) ⟨1344407, by rfl⟩ : syracuseStep 1792543 = 2688815) B2688815
theorem B2390633 : Blo 1592995 2390633 := bstep (se 2 (by rfl) ⟨896487, by rfl⟩ : syracuseStep 2390633 = 1792975) B1792975
theorem B3586697 : Blo 1592995 3586697 := bstep (se 2 (by rfl) ⟨1345011, by rfl⟩ : syracuseStep 3586697 = 2690023) B2690023
theorem B33151639 : Blo 1592995 33151639 := bstep (se 1 (by rfl) ⟨24863729, by rfl⟩ : syracuseStep 33151639 = 49727459) B49727459
theorem B5741279 : Blo 1592995 5741279 := bstep (se 1 (by rfl) ⟨4305959, by rfl⟩ : syracuseStep 5741279 = 8611919) B8611919
theorem B23616305 : Blo 1592995 23616305 := bstep (se 2 (by rfl) ⟨8856114, by rfl⟩ : syracuseStep 23616305 = 17712229) B17712229
theorem B7764815 : Blo 1592995 7764815 := bstep (se 1 (by rfl) ⟨5823611, by rfl⟩ : syracuseStep 7764815 = 11647223) B11647223
theorem B8067923 : Blo 1592995 8067923 := bstep (se 1 (by rfl) ⟨6050942, by rfl⟩ : syracuseStep 8067923 = 12101885) B12101885
theorem B27245645 : Blo 1592995 27245645 := bstep (se 3 (by rfl) ⟨5108558, by rfl⟩ : syracuseStep 27245645 = 10217117) B10217117
theorem B318569561 : Blo 1592995 318569561 := bstep (se 2 (by rfl) ⟨119463585, by rfl⟩ : syracuseStep 318569561 = 238927171) B238927171
theorem B2391161 : Blo 1592995 2391161 := bstep (se 2 (by rfl) ⟨896685, by rfl⟩ : syracuseStep 2391161 = 1793371) B1793371
theorem B12926081 : Blo 1592995 12926081 := bstep (se 2 (by rfl) ⟨4847280, by rfl⟩ : syracuseStep 12926081 = 9694561) B9694561
theorem B3587255 : Blo 1592995 3587255 := bstep (se 1 (by rfl) ⟨2690441, by rfl⟩ : syracuseStep 3587255 = 5380883) B5380883
theorem B4537559 : Blo 1592995 4537559 := bstep (se 1 (by rfl) ⟨3403169, by rfl⟩ : syracuseStep 4537559 = 6806339) B6806339
theorem B2391263 : Blo 1592995 2391263 := bstep (se 1 (by rfl) ⟨1793447, by rfl⟩ : syracuseStep 2391263 = 3586895) B3586895
theorem B5381369 : Blo 1592995 5381369 := bstep (se 2 (by rfl) ⟨2018013, by rfl⟩ : syracuseStep 5381369 = 4036027) B4036027
theorem B10214657 : Blo 1592995 10214657 := bstep (se 2 (by rfl) ⟨3830496, by rfl⟩ : syracuseStep 10214657 = 7660993) B7660993
theorem B2391305 : Blo 1592995 2391305 := bstep (se 2 (by rfl) ⟨896739, by rfl⟩ : syracuseStep 2391305 = 1793479) B1793479
theorem B2391407 : Blo 1592995 2391407 := bstep (se 1 (by rfl) ⟨1793555, by rfl⟩ : syracuseStep 2391407 = 3587111) B3587111
theorem B38772107 : Blo 1592995 38772107 := bstep (se 1 (by rfl) ⟨29079080, by rfl⟩ : syracuseStep 38772107 = 58158161) B58158161
theorem B4914599 : Blo 1592995 4914599 := bstep (se 1 (by rfl) ⟨3685949, by rfl⟩ : syracuseStep 4914599 = 7371899) B7371899
theorem B2391527 : Blo 1592995 2391527 := bstep (se 1 (by rfl) ⟨1793645, by rfl⟩ : syracuseStep 2391527 = 3587291) B3587291
theorem B5381639 : Blo 1592995 5381639 := bstep (se 1 (by rfl) ⟨4036229, by rfl⟩ : syracuseStep 5381639 = 8072459) B8072459
theorem B58195523 : Blo 1592995 58195523 := bstep (se 1 (by rfl) ⟨43646642, by rfl⟩ : syracuseStep 58195523 = 87293285) B87293285
theorem B2391659 : Blo 1592995 2391659 := bstep (se 1 (by rfl) ⟨1793744, by rfl⟩ : syracuseStep 2391659 = 3587489) B3587489
theorem B9322127 : Blo 1592995 9322127 := bstep (se 1 (by rfl) ⟨6991595, by rfl⟩ : syracuseStep 9322127 = 13983191) B13983191
theorem B2391785 : Blo 1592995 2391785 := bstep (se 2 (by rfl) ⟨896919, by rfl⟩ : syracuseStep 2391785 = 1793839) B1793839
theorem B4308727 : Blo 1592995 4308727 := bstep (se 1 (by rfl) ⟨3231545, by rfl⟩ : syracuseStep 4308727 = 6463091) B6463091
theorem B3587831 : Blo 1592995 3587831 := bstep (se 1 (by rfl) ⟨2690873, by rfl⟩ : syracuseStep 3587831 = 5381747) B5381747
theorem B2268967 : Blo 1592995 2268967 := bstep (se 1 (by rfl) ⟨1701725, by rfl⟩ : syracuseStep 2268967 = 3403451) B3403451
theorem B2391929 : Blo 1592995 2391929 := bstep (se 2 (by rfl) ⟨896973, by rfl⟩ : syracuseStep 2391929 = 1793947) B1793947
theorem B3588011 : Blo 1592995 3588011 := bstep (se 1 (by rfl) ⟨2691008, by rfl⟩ : syracuseStep 3588011 = 5382017) B5382017
theorem B2392031 : Blo 1592995 2392031 := bstep (se 1 (by rfl) ⟨1794023, by rfl⟩ : syracuseStep 2392031 = 3588047) B3588047
theorem B6054011 : Blo 1592995 6054011 := bstep (se 1 (by rfl) ⟨4540508, by rfl⟩ : syracuseStep 6054011 = 9081017) B9081017
theorem B45932741 : Blo 1592995 45932741 := bstep (se 4 (by rfl) ⟨4306194, by rfl⟩ : syracuseStep 45932741 = 8612389) B8612389
theorem B4538663 : Blo 1592995 4538663 := bstep (se 1 (by rfl) ⟨3403997, by rfl⟩ : syracuseStep 4538663 = 6807995) B6807995
theorem B2392367 : Blo 1592995 2392367 := bstep (se 1 (by rfl) ⟨1794275, by rfl⟩ : syracuseStep 2392367 = 3588551) B3588551
theorem B3588479 : Blo 1592995 3588479 := bstep (se 1 (by rfl) ⟨2691359, by rfl⟩ : syracuseStep 3588479 = 5382719) B5382719
theorem B13623713 : Blo 1592995 13623713 := bstep (se 2 (by rfl) ⟨5108892, by rfl⟩ : syracuseStep 13623713 = 10217785) B10217785
theorem B3588713 : Blo 1592995 3588713 := bstep (se 2 (by rfl) ⟨1345767, by rfl⟩ : syracuseStep 3588713 = 2691535) B2691535
theorem B12919429 : Blo 1592995 12919429 := bstep (se 4 (by rfl) ⟨1211196, by rfl⟩ : syracuseStep 12919429 = 2422393) B2422393
theorem B5825191 : Blo 1592995 5825191 := bstep (se 1 (by rfl) ⟨4368893, by rfl⟩ : syracuseStep 5825191 = 8737787) B8737787
theorem B15320141 : Blo 1592995 15320141 := bstep (se 3 (by rfl) ⟨2872526, by rfl⟩ : syracuseStep 15320141 = 5745053) B5745053
theorem B15328601 : Blo 1592995 15328601 := bstep (se 2 (by rfl) ⟨5748225, by rfl⟩ : syracuseStep 15328601 = 11496451) B11496451
theorem B31065515 : Blo 1592995 31065515 := bstep (se 1 (by rfl) ⟨23299136, by rfl⟩ : syracuseStep 31065515 = 46598273) B46598273
theorem B18155015 : Blo 1592995 18155015 := bstep (se 1 (by rfl) ⟨13616261, by rfl⟩ : syracuseStep 18155015 = 27232523) B27232523
theorem B2688619 : Blo 1592995 2688619 := bstep (se 1 (by rfl) ⟨2016464, by rfl⟩ : syracuseStep 2688619 = 4032929) B4032929
theorem B14534255 : Blo 1592995 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B52422389 : Blo 1592995 52422389 := bstep (se 5 (by rfl) ⟨2457299, by rfl⟩ : syracuseStep 52422389 = 4914599) B4914599
theorem B3827519 : Blo 1592995 3827519 := bstep (se 1 (by rfl) ⟨2870639, by rfl⟩ : syracuseStep 3827519 = 5741279) B5741279
theorem B2688889 : Blo 1592995 2688889 := bstep (se 2 (by rfl) ⟨1008333, by rfl⟩ : syracuseStep 2688889 = 2016667) B2016667
theorem B20711369 : Blo 1592995 20711369 := bstep (se 2 (by rfl) ⟨7766763, by rfl⟩ : syracuseStep 20711369 = 15533527) B15533527
theorem B18163763 : Blo 1592995 18163763 := bstep (se 1 (by rfl) ⟨13622822, by rfl⟩ : syracuseStep 18163763 = 27245645) B27245645
theorem B212379707 : Blo 1592995 212379707 := bstep (se 1 (by rfl) ⟨159284780, by rfl⟩ : syracuseStep 212379707 = 318569561) B318569561
theorem B3025039 : Blo 1592995 3025039 := bstep (se 1 (by rfl) ⟨2268779, by rfl⟩ : syracuseStep 3025039 = 4537559) B4537559
theorem B6809771 : Blo 1592995 6809771 := bstep (se 1 (by rfl) ⟨5107328, by rfl⟩ : syracuseStep 6809771 = 10214657) B10214657
theorem B2689247 : Blo 1592995 2689247 := bstep (se 1 (by rfl) ⟨2016935, by rfl⟩ : syracuseStep 2689247 = 4033871) B4033871
theorem B25848071 : Blo 1592995 25848071 := bstep (se 1 (by rfl) ⟨19386053, by rfl⟩ : syracuseStep 25848071 = 38772107) B38772107
theorem B5744969 : Blo 1592995 5744969 := bstep (se 2 (by rfl) ⟨2154363, by rfl⟩ : syracuseStep 5744969 = 4308727) B4308727
theorem B3025289 : Blo 1592995 3025289 := bstep (se 2 (by rfl) ⟨1134483, by rfl⟩ : syracuseStep 3025289 = 2268967) B2268967
theorem B10209995 : Blo 1592995 10209995 := bstep (se 1 (by rfl) ⟨7657496, by rfl⟩ : syracuseStep 10209995 = 15314993) B15314993
theorem B12110633 : Blo 1592995 12110633 := bstep (se 2 (by rfl) ⟨4541487, by rfl⟩ : syracuseStep 12110633 = 9082975) B9082975
theorem B6810455 : Blo 1592995 6810455 := bstep (se 1 (by rfl) ⟨5107841, by rfl⟩ : syracuseStep 6810455 = 10215683) B10215683
theorem B2690111 : Blo 1592995 2690111 := bstep (se 1 (by rfl) ⟨2017583, by rfl⟩ : syracuseStep 2690111 = 4035167) B4035167
theorem B5377211 : Blo 1592995 5377211 := bstep (se 1 (by rfl) ⟨4032908, by rfl⟩ : syracuseStep 5377211 = 8065817) B8065817
theorem B3026231 : Blo 1592995 3026231 := bstep (se 1 (by rfl) ⟨2269673, by rfl⟩ : syracuseStep 3026231 = 4539347) B4539347
theorem B18165221 : Blo 1592995 18165221 := bstep (se 4 (by rfl) ⟨1702989, by rfl⟩ : syracuseStep 18165221 = 3405979) B3405979
theorem B1593083 : Blo 1592995 1593083 := bstep (se 1 (by rfl) ⟨1194812, by rfl⟩ : syracuseStep 1593083 = 2389625) B2389625
theorem B1593151 : Blo 1592995 1593151 := bstep (se 1 (by rfl) ⟨1194863, by rfl⟩ : syracuseStep 1593151 = 2389727) B2389727
theorem B1593215 : Blo 1592995 1593215 := bstep (se 1 (by rfl) ⟨1194911, by rfl⟩ : syracuseStep 1593215 = 2389823) B2389823
theorem B1593327 : Blo 1592995 1593327 := bstep (se 1 (by rfl) ⟨1194995, by rfl⟩ : syracuseStep 1593327 = 2389991) B2389991
theorem B1593339 : Blo 1592995 1593339 := bstep (se 1 (by rfl) ⟨1195004, by rfl⟩ : syracuseStep 1593339 = 2390009) B2390009
theorem B1593407 : Blo 1592995 1593407 := bstep (se 1 (by rfl) ⟨1195055, by rfl⟩ : syracuseStep 1593407 = 2390111) B2390111
theorem B6811721 : Blo 1592995 6811721 := bstep (se 2 (by rfl) ⟨2554395, by rfl⟩ : syracuseStep 6811721 = 5108791) B5108791
theorem B1593447 : Blo 1592995 1593447 := bstep (se 1 (by rfl) ⟨1195085, by rfl⟩ : syracuseStep 1593447 = 2390171) B2390171
theorem B1593471 : Blo 1592995 1593471 := bstep (se 1 (by rfl) ⟨1195103, by rfl⟩ : syracuseStep 1593471 = 2390207) B2390207
theorem B5378183 : Blo 1592995 5378183 := bstep (se 1 (by rfl) ⟨4033637, by rfl⟩ : syracuseStep 5378183 = 8067275) B8067275
theorem B1593499 : Blo 1592995 1593499 := bstep (se 1 (by rfl) ⟨1195124, by rfl⟩ : syracuseStep 1593499 = 2390249) B2390249
theorem B3633427 : Blo 1592995 3633427 := bstep (se 1 (by rfl) ⟨2725070, by rfl⟩ : syracuseStep 3633427 = 5450141) B5450141
theorem B5378345 : Blo 1592995 5378345 := bstep (se 2 (by rfl) ⟨2016879, by rfl⟩ : syracuseStep 5378345 = 4033759) B4033759
theorem B1593703 : Blo 1592995 1593703 := bstep (se 1 (by rfl) ⟨1195277, by rfl⟩ : syracuseStep 1593703 = 2390555) B2390555
theorem B78623129 : Blo 1592995 78623129 := bstep (se 2 (by rfl) ⟨29483673, by rfl⟩ : syracuseStep 78623129 = 58967347) B58967347
theorem B3584411 : Blo 1592995 3584411 := bstep (se 1 (by rfl) ⟨2688308, by rfl⟩ : syracuseStep 3584411 = 5376617) B5376617
theorem B1593755 : Blo 1592995 1593755 := bstep (se 1 (by rfl) ⟨1195316, by rfl⟩ : syracuseStep 1593755 = 2390633) B2390633
theorem B5378615 : Blo 1592995 5378615 := bstep (se 1 (by rfl) ⟨4033961, by rfl⟩ : syracuseStep 5378615 = 8067923) B8067923
theorem B8073917 : Blo 1592995 8073917 := bstep (se 3 (by rfl) ⟨1513859, by rfl⟩ : syracuseStep 8073917 = 3027719) B3027719
theorem B1594107 : Blo 1592995 1594107 := bstep (se 1 (by rfl) ⟨1195580, by rfl⟩ : syracuseStep 1594107 = 2391161) B2391161
theorem B2552639 : Blo 1592995 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B1594175 : Blo 1592995 1594175 := bstep (se 1 (by rfl) ⟨1195631, by rfl⟩ : syracuseStep 1594175 = 2391263) B2391263
theorem B1594203 : Blo 1592995 1594203 := bstep (se 1 (by rfl) ⟨1195652, by rfl⟩ : syracuseStep 1594203 = 2391305) B2391305
theorem B3404681 : Blo 1592995 3404681 := bstep (se 2 (by rfl) ⟨1276755, by rfl⟩ : syracuseStep 3404681 = 2553511) B2553511
theorem B1594271 : Blo 1592995 1594271 := bstep (se 1 (by rfl) ⟨1195703, by rfl⟩ : syracuseStep 1594271 = 2391407) B2391407
theorem B1594351 : Blo 1592995 1594351 := bstep (se 1 (by rfl) ⟨1195763, by rfl⟩ : syracuseStep 1594351 = 2391527) B2391527
theorem B3683369 : Blo 1592995 3683369 := bstep (se 2 (by rfl) ⟨1381263, by rfl⟩ : syracuseStep 3683369 = 2762527) B2762527
theorem B3585095 : Blo 1592995 3585095 := bstep (se 1 (by rfl) ⟨2688821, by rfl⟩ : syracuseStep 3585095 = 5377643) B5377643
theorem B1594439 : Blo 1592995 1594439 := bstep (se 1 (by rfl) ⟨1195829, by rfl⟩ : syracuseStep 1594439 = 2391659) B2391659
theorem B41399369 : Blo 1592995 41399369 := bstep (se 2 (by rfl) ⟨15524763, by rfl⟩ : syracuseStep 41399369 = 31049527) B31049527
theorem B6214751 : Blo 1592995 6214751 := bstep (se 1 (by rfl) ⟨4661063, by rfl⟩ : syracuseStep 6214751 = 9322127) B9322127
theorem B1594523 : Blo 1592995 1594523 := bstep (se 1 (by rfl) ⟨1195892, by rfl⟩ : syracuseStep 1594523 = 2391785) B2391785
theorem B3585275 : Blo 1592995 3585275 := bstep (se 1 (by rfl) ⟨2688956, by rfl⟩ : syracuseStep 3585275 = 5377913) B5377913
theorem B1594619 : Blo 1592995 1594619 := bstep (se 1 (by rfl) ⟨1195964, by rfl⟩ : syracuseStep 1594619 = 2391929) B2391929
theorem B2553095 : Blo 1592995 2553095 := bstep (se 1 (by rfl) ⟨1914821, by rfl⟩ : syracuseStep 2553095 = 3829643) B3829643
theorem B1594687 : Blo 1592995 1594687 := bstep (se 1 (by rfl) ⟨1196015, by rfl⟩ : syracuseStep 1594687 = 2392031) B2392031
theorem B7271851 : Blo 1592995 7271851 := bstep (se 1 (by rfl) ⟨5453888, by rfl⟩ : syracuseStep 7271851 = 10907777) B10907777
theorem B3585491 : Blo 1592995 3585491 := bstep (se 1 (by rfl) ⟨2689118, by rfl⟩ : syracuseStep 3585491 = 5378237) B5378237
theorem B1594855 : Blo 1592995 1594855 := bstep (se 1 (by rfl) ⟨1196141, by rfl⟩ : syracuseStep 1594855 = 2392283) B2392283
theorem B1594863 : Blo 1592995 1594863 := bstep (se 1 (by rfl) ⟨1196147, by rfl⟩ : syracuseStep 1594863 = 2392295) B2392295
theorem B12097025 : Blo 1592995 12097025 := bstep (se 2 (by rfl) ⟨4536384, by rfl⟩ : syracuseStep 12097025 = 9072769) B9072769
theorem B12105287 : Blo 1592995 12105287 := bstep (se 1 (by rfl) ⟨9078965, by rfl⟩ : syracuseStep 12105287 = 18157931) B18157931
theorem B2389595 : Blo 1592995 2389595 := bstep (se 1 (by rfl) ⟨1792196, by rfl⟩ : syracuseStep 2389595 = 3584393) B3584393
theorem B4847195 : Blo 1592995 4847195 := bstep (se 1 (by rfl) ⟨3635396, by rfl⟩ : syracuseStep 4847195 = 7270793) B7270793
theorem B1594971 : Blo 1592995 1594971 := bstep (se 1 (by rfl) ⟨1196228, by rfl⟩ : syracuseStep 1594971 = 2392457) B2392457
theorem B7763567 : Blo 1592995 7763567 := bstep (se 1 (by rfl) ⟨5822675, by rfl⟩ : syracuseStep 7763567 = 11645351) B11645351
theorem B34469549 : Blo 1592995 34469549 := bstep (se 3 (by rfl) ⟨6463040, by rfl⟩ : syracuseStep 34469549 = 12926081) B12926081
theorem B5379803 : Blo 1592995 5379803 := bstep (se 1 (by rfl) ⟨4034852, by rfl⟩ : syracuseStep 5379803 = 8069705) B8069705
theorem B3585761 : Blo 1592995 3585761 := bstep (se 2 (by rfl) ⟨1344660, by rfl⟩ : syracuseStep 3585761 = 2689321) B2689321
theorem B39327545 : Blo 1592995 39327545 := bstep (se 2 (by rfl) ⟨14747829, by rfl⟩ : syracuseStep 39327545 = 29495659) B29495659
theorem B87283649 : Blo 1592995 87283649 := bstep (se 2 (by rfl) ⟨32731368, by rfl⟩ : syracuseStep 87283649 = 65462737) B65462737
theorem B2390057 : Blo 1592995 2390057 := bstep (se 2 (by rfl) ⟨896271, by rfl⟩ : syracuseStep 2390057 = 1792543) B1792543
theorem B2390087 : Blo 1592995 2390087 := bstep (se 1 (by rfl) ⟨1792565, by rfl⟩ : syracuseStep 2390087 = 3585131) B3585131
theorem B13285571 : Blo 1592995 13285571 := bstep (se 1 (by rfl) ⟨9964178, by rfl⟩ : syracuseStep 13285571 = 19928357) B19928357
theorem B13613255 : Blo 1592995 13613255 := bstep (se 1 (by rfl) ⟨10209941, by rfl⟩ : syracuseStep 13613255 = 20419883) B20419883
theorem B44202185 : Blo 1592995 44202185 := bstep (se 2 (by rfl) ⟨16575819, by rfl⟩ : syracuseStep 44202185 = 33151639) B33151639
theorem B2332891 : Blo 1592995 2332891 := bstep (se 1 (by rfl) ⟨1749668, by rfl⟩ : syracuseStep 2332891 = 3499337) B3499337
theorem B3586283 : Blo 1592995 3586283 := bstep (se 1 (by rfl) ⟨2689712, by rfl⟩ : syracuseStep 3586283 = 5379425) B5379425
theorem B3832103 : Blo 1592995 3832103 := bstep (se 1 (by rfl) ⟨2874077, by rfl⟩ : syracuseStep 3832103 = 5748155) B5748155
theorem B16357727 : Blo 1592995 16357727 := bstep (se 1 (by rfl) ⟨12268295, by rfl⟩ : syracuseStep 16357727 = 24536591) B24536591
theorem B2390471 : Blo 1592995 2390471 := bstep (se 1 (by rfl) ⟨1792853, by rfl⟩ : syracuseStep 2390471 = 3585707) B3585707
theorem B2390687 : Blo 1592995 2390687 := bstep (se 1 (by rfl) ⟨1793015, by rfl⟩ : syracuseStep 2390687 = 3586031) B3586031
theorem B2390831 : Blo 1592995 2390831 := bstep (se 1 (by rfl) ⟨1793123, by rfl⟩ : syracuseStep 2390831 = 3586247) B3586247
theorem B2390951 : Blo 1592995 2390951 := bstep (se 1 (by rfl) ⟨1793213, by rfl⟩ : syracuseStep 2390951 = 3586427) B3586427
theorem B41417743 : Blo 1592995 41417743 := bstep (se 1 (by rfl) ⟨31063307, by rfl⟩ : syracuseStep 41417743 = 62126615) B62126615
theorem B2391131 : Blo 1592995 2391131 := bstep (se 1 (by rfl) ⟨1793348, by rfl⟩ : syracuseStep 2391131 = 3586697) B3586697
theorem B15744203 : Blo 1592995 15744203 := bstep (se 1 (by rfl) ⟨11808152, by rfl⟩ : syracuseStep 15744203 = 23616305) B23616305
theorem B5176543 : Blo 1592995 5176543 := bstep (se 1 (by rfl) ⟨3882407, by rfl⟩ : syracuseStep 5176543 = 7764815) B7764815
theorem B5741999 : Blo 1592995 5741999 := bstep (se 1 (by rfl) ⟨4306499, by rfl⟩ : syracuseStep 5741999 = 8612999) B8612999
theorem B2391503 : Blo 1592995 2391503 := bstep (se 1 (by rfl) ⟨1793627, by rfl⟩ : syracuseStep 2391503 = 3587255) B3587255
theorem B3587579 : Blo 1592995 3587579 := bstep (se 1 (by rfl) ⟨2690684, by rfl⟩ : syracuseStep 3587579 = 5381369) B5381369
theorem B16358921 : Blo 1592995 16358921 := bstep (se 2 (by rfl) ⟨6134595, by rfl⟩ : syracuseStep 16358921 = 12269191) B12269191
theorem B3587759 : Blo 1592995 3587759 := bstep (se 1 (by rfl) ⟨2690819, by rfl⟩ : syracuseStep 3587759 = 5381639) B5381639
theorem B38797015 : Blo 1592995 38797015 := bstep (se 1 (by rfl) ⟨29097761, by rfl⟩ : syracuseStep 38797015 = 58195523) B58195523
theorem B1793767 : Blo 1592995 1793767 := bstep (se 1 (by rfl) ⟨1345325, by rfl⟩ : syracuseStep 1793767 = 2690651) B2690651
theorem B3587849 : Blo 1592995 3587849 := bstep (se 2 (by rfl) ⟨1345443, by rfl⟩ : syracuseStep 3587849 = 2690887) B2690887
theorem B2391887 : Blo 1592995 2391887 := bstep (se 1 (by rfl) ⟨1793915, by rfl⟩ : syracuseStep 2391887 = 3587831) B3587831
theorem B2392007 : Blo 1592995 2392007 := bstep (se 1 (by rfl) ⟨1794005, by rfl⟩ : syracuseStep 2392007 = 3588011) B3588011
theorem B9822317 : Blo 1592995 9822317 := bstep (se 3 (by rfl) ⟨1841684, by rfl⟩ : syracuseStep 9822317 = 3683369) B3683369
theorem B30621827 : Blo 1592995 30621827 := bstep (se 1 (by rfl) ⟨22966370, by rfl⟩ : syracuseStep 30621827 = 45932741) B45932741
theorem B2392319 : Blo 1592995 2392319 := bstep (se 1 (by rfl) ⟨1794239, by rfl⟩ : syracuseStep 2392319 = 3588479) B3588479
theorem B2392475 : Blo 1592995 2392475 := bstep (se 1 (by rfl) ⟨1794356, by rfl⟩ : syracuseStep 2392475 = 3588713) B3588713
theorem B5382611 : Blo 1592995 5382611 := bstep (se 1 (by rfl) ⟨4036958, by rfl⟩ : syracuseStep 5382611 = 8073917) B8073917
theorem B2269787 : Blo 1592995 2269787 := bstep (se 1 (by rfl) ⟨1702340, by rfl⟩ : syracuseStep 2269787 = 3404681) B3404681
theorem B68903621 : Blo 1592995 68903621 := bstep (se 4 (by rfl) ⟨6459714, by rfl⟩ : syracuseStep 68903621 = 12919429) B12919429
theorem B27599579 : Blo 1592995 27599579 := bstep (se 1 (by rfl) ⟨20699684, by rfl⟩ : syracuseStep 27599579 = 41399369) B41399369
theorem B7766921 : Blo 1592995 7766921 := bstep (se 2 (by rfl) ⟨2912595, by rfl⟩ : syracuseStep 7766921 = 5825191) B5825191
theorem B20710343 : Blo 1592995 20710343 := bstep (se 1 (by rfl) ⟨15532757, by rfl⟩ : syracuseStep 20710343 = 31065515) B31065515
theorem B8070191 : Blo 1592995 8070191 := bstep (se 1 (by rfl) ⟨6052643, by rfl⟩ : syracuseStep 8070191 = 12105287) B12105287
theorem B22979699 : Blo 1592995 22979699 := bstep (se 1 (by rfl) ⟨17234774, by rfl⟩ : syracuseStep 22979699 = 34469549) B34469549
theorem B34948259 : Blo 1592995 34948259 := bstep (se 1 (by rfl) ⟨26211194, by rfl⟩ : syracuseStep 34948259 = 52422389) B52422389
theorem B58189099 : Blo 1592995 58189099 := bstep (se 1 (by rfl) ⟨43641824, by rfl⟩ : syracuseStep 58189099 = 87283649) B87283649
theorem B55223657 : Blo 1592995 55223657 := bstep (se 2 (by rfl) ⟨20708871, by rfl⟩ : syracuseStep 55223657 = 41417743) B41417743
theorem B12109175 : Blo 1592995 12109175 := bstep (se 1 (by rfl) ⟨9081881, by rfl⟩ : syracuseStep 12109175 = 18163763) B18163763
theorem B29468123 : Blo 1592995 29468123 := bstep (se 1 (by rfl) ⟨22101092, by rfl⟩ : syracuseStep 29468123 = 44202185) B44202185
theorem B38758013 : Blo 1592995 38758013 := bstep (se 3 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 38758013 = 14534255) B14534255
theorem B20702845 : Blo 1592995 20702845 := bstep (se 3 (by rfl) ⟨3881783, by rfl⟩ : syracuseStep 20702845 = 7763567) B7763567
theorem B4540303 : Blo 1592995 4540303 := bstep (se 1 (by rfl) ⟨3405227, by rfl⟩ : syracuseStep 4540303 = 6810455) B6810455
theorem B10496135 : Blo 1592995 10496135 := bstep (se 1 (by rfl) ⟨7872101, by rfl⟩ : syracuseStep 10496135 = 15744203) B15744203
theorem B2017487 : Blo 1592995 2017487 := bstep (se 1 (by rfl) ⟨1513115, by rfl⟩ : syracuseStep 2017487 = 3026231) B3026231
theorem B3827999 : Blo 1592995 3827999 := bstep (se 1 (by rfl) ⟨2870999, by rfl⟩ : syracuseStep 3827999 = 5741999) B5741999
theorem B12110147 : Blo 1592995 12110147 := bstep (se 1 (by rfl) ⟨9082610, by rfl⟩ : syracuseStep 12110147 = 18165221) B18165221
theorem B10905947 : Blo 1592995 10905947 := bstep (se 1 (by rfl) ⟨8179460, by rfl⟩ : syracuseStep 10905947 = 16358921) B16358921
theorem B4541147 : Blo 1592995 4541147 := bstep (se 1 (by rfl) ⟨3405860, by rfl⟩ : syracuseStep 4541147 = 6811721) B6811721
theorem B4033385 : Blo 1592995 4033385 := bstep (se 2 (by rfl) ⟨1512519, by rfl⟩ : syracuseStep 4033385 = 3025039) B3025039
theorem B3025775 : Blo 1592995 3025775 := bstep (se 1 (by rfl) ⟨2269331, by rfl⟩ : syracuseStep 3025775 = 4538663) B4538663
theorem B52415419 : Blo 1592995 52415419 := bstep (se 1 (by rfl) ⟨39311564, by rfl⟩ : syracuseStep 52415419 = 78623129) B78623129
theorem B10219067 : Blo 1592995 10219067 := bstep (se 1 (by rfl) ⟨7664300, by rfl⟩ : syracuseStep 10219067 = 15328601) B15328601
theorem B8064683 : Blo 1592995 8064683 := bstep (se 1 (by rfl) ⟨6048512, by rfl⟩ : syracuseStep 8064683 = 12097025) B12097025
theorem B12103343 : Blo 1592995 12103343 := bstep (se 1 (by rfl) ⟨9077507, by rfl⟩ : syracuseStep 12103343 = 18155015) B18155015
theorem B1593063 : Blo 1592995 1593063 := bstep (se 1 (by rfl) ⟨1194797, by rfl⟩ : syracuseStep 1593063 = 2389595) B2389595
theorem B3231463 : Blo 1592995 3231463 := bstep (se 1 (by rfl) ⟨2423597, by rfl⟩ : syracuseStep 3231463 = 4847195) B4847195
theorem B2551679 : Blo 1592995 2551679 := bstep (se 1 (by rfl) ⟨1913759, by rfl⟩ : syracuseStep 2551679 = 3827519) B3827519
theorem B13807579 : Blo 1592995 13807579 := bstep (se 1 (by rfl) ⟨10355684, by rfl⟩ : syracuseStep 13807579 = 20711369) B20711369
theorem B1593371 : Blo 1592995 1593371 := bstep (se 1 (by rfl) ⟨1195028, by rfl⟩ : syracuseStep 1593371 = 2390057) B2390057
theorem B141586471 : Blo 1592995 141586471 := bstep (se 1 (by rfl) ⟨106189853, by rfl⟩ : syracuseStep 141586471 = 212379707) B212379707
theorem B1593391 : Blo 1592995 1593391 := bstep (se 1 (by rfl) ⟨1195043, by rfl⟩ : syracuseStep 1593391 = 2390087) B2390087
theorem B19378277 : Blo 1592995 19378277 := bstep (se 4 (by rfl) ⟨1816713, by rfl⟩ : syracuseStep 19378277 = 3633427) B3633427
theorem B17232047 : Blo 1592995 17232047 := bstep (se 1 (by rfl) ⟨12924035, by rfl⟩ : syracuseStep 17232047 = 25848071) B25848071
theorem B3829979 : Blo 1592995 3829979 := bstep (se 1 (by rfl) ⟨2872484, by rfl⟩ : syracuseStep 3829979 = 5744969) B5744969
theorem B6902057 : Blo 1592995 6902057 := bstep (se 2 (by rfl) ⟨2588271, by rfl⟩ : syracuseStep 6902057 = 5176543) B5176543
theorem B1593647 : Blo 1592995 1593647 := bstep (se 1 (by rfl) ⟨1195235, by rfl⟩ : syracuseStep 1593647 = 2390471) B2390471
theorem B1593791 : Blo 1592995 1593791 := bstep (se 1 (by rfl) ⟨1195343, by rfl⟩ : syracuseStep 1593791 = 2390687) B2390687
theorem B8073755 : Blo 1592995 8073755 := bstep (se 1 (by rfl) ⟨6055316, by rfl⟩ : syracuseStep 8073755 = 12110633) B12110633
theorem B1593887 : Blo 1592995 1593887 := bstep (se 1 (by rfl) ⟨1195415, by rfl⟩ : syracuseStep 1593887 = 2390831) B2390831
theorem B9695801 : Blo 1592995 9695801 := bstep (se 2 (by rfl) ⟨3635925, by rfl⟩ : syracuseStep 9695801 = 7271851) B7271851
theorem B1593967 : Blo 1592995 1593967 := bstep (se 1 (by rfl) ⟨1195475, by rfl⟩ : syracuseStep 1593967 = 2390951) B2390951
theorem B1594087 : Blo 1592995 1594087 := bstep (se 1 (by rfl) ⟨1195565, by rfl⟩ : syracuseStep 1594087 = 2391131) B2391131
theorem B3584807 : Blo 1592995 3584807 := bstep (se 1 (by rfl) ⟨2688605, by rfl⟩ : syracuseStep 3584807 = 5377211) B5377211
theorem B3584825 : Blo 1592995 3584825 := bstep (se 2 (by rfl) ⟨1344309, by rfl⟩ : syracuseStep 3584825 = 2688619) B2688619
theorem B51729353 : Blo 1592995 51729353 := bstep (se 2 (by rfl) ⟨19398507, by rfl⟩ : syracuseStep 51729353 = 38797015) B38797015
theorem B1594335 : Blo 1592995 1594335 := bstep (se 1 (by rfl) ⟨1195751, by rfl⟩ : syracuseStep 1594335 = 2391503) B2391503
theorem B3585185 : Blo 1592995 3585185 := bstep (se 2 (by rfl) ⟨1344444, by rfl⟩ : syracuseStep 3585185 = 2688889) B2688889
theorem B1594591 : Blo 1592995 1594591 := bstep (se 1 (by rfl) ⟨1195943, by rfl⟩ : syracuseStep 1594591 = 2391887) B2391887
theorem B1594671 : Blo 1592995 1594671 := bstep (se 1 (by rfl) ⟨1196003, by rfl⟩ : syracuseStep 1594671 = 2392007) B2392007
theorem B4036007 : Blo 1592995 4036007 := bstep (se 1 (by rfl) ⟨3027005, by rfl⟩ : syracuseStep 4036007 = 6054011) B6054011
theorem B3585455 : Blo 1592995 3585455 := bstep (se 1 (by rfl) ⟨2689091, by rfl⟩ : syracuseStep 3585455 = 5378183) B5378183
theorem B3585563 : Blo 1592995 3585563 := bstep (se 1 (by rfl) ⟨2689172, by rfl⟩ : syracuseStep 3585563 = 5378345) B5378345
theorem B1594911 : Blo 1592995 1594911 := bstep (se 1 (by rfl) ⟨1196183, by rfl⟩ : syracuseStep 1594911 = 2392367) B2392367
theorem B2389607 : Blo 1592995 2389607 := bstep (se 1 (by rfl) ⟨1792205, by rfl⟩ : syracuseStep 2389607 = 3584411) B3584411
theorem B9082475 : Blo 1592995 9082475 := bstep (se 1 (by rfl) ⟨6811856, by rfl⟩ : syracuseStep 9082475 = 13623713) B13623713
theorem B3585743 : Blo 1592995 3585743 := bstep (se 1 (by rfl) ⟨2689307, by rfl⟩ : syracuseStep 3585743 = 5378615) B5378615
theorem B18159389 : Blo 1592995 18159389 := bstep (se 3 (by rfl) ⟨3404885, by rfl⟩ : syracuseStep 18159389 = 6809771) B6809771
theorem B27228149 : Blo 1592995 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B2390063 : Blo 1592995 2390063 := bstep (se 1 (by rfl) ⟨1792547, by rfl⟩ : syracuseStep 2390063 = 3585095) B3585095
theorem B10213427 : Blo 1592995 10213427 := bstep (se 1 (by rfl) ⟨7660070, by rfl⟩ : syracuseStep 10213427 = 15320141) B15320141
theorem B4143167 : Blo 1592995 4143167 := bstep (se 1 (by rfl) ⟨3107375, by rfl⟩ : syracuseStep 4143167 = 6214751) B6214751
theorem B2390183 : Blo 1592995 2390183 := bstep (se 1 (by rfl) ⟨1792637, by rfl⟩ : syracuseStep 2390183 = 3585275) B3585275
theorem B1702063 : Blo 1592995 1702063 := bstep (se 1 (by rfl) ⟨1276547, by rfl⟩ : syracuseStep 1702063 = 2553095) B2553095
theorem B43620605 : Blo 1592995 43620605 := bstep (se 3 (by rfl) ⟨8178863, by rfl⟩ : syracuseStep 43620605 = 16357727) B16357727
theorem B2390327 : Blo 1592995 2390327 := bstep (se 1 (by rfl) ⟨1792745, by rfl⟩ : syracuseStep 2390327 = 3585491) B3585491
theorem B8067437 : Blo 1592995 8067437 := bstep (se 3 (by rfl) ⟨1512644, by rfl⟩ : syracuseStep 8067437 = 3025289) B3025289
theorem B12442085 : Blo 1592995 12442085 := bstep (se 4 (by rfl) ⟨1166445, by rfl⟩ : syracuseStep 12442085 = 2332891) B2332891
theorem B3586535 : Blo 1592995 3586535 := bstep (se 1 (by rfl) ⟨2689901, by rfl⟩ : syracuseStep 3586535 = 5379803) B5379803
theorem B2390507 : Blo 1592995 2390507 := bstep (se 1 (by rfl) ⟨1792880, by rfl⟩ : syracuseStep 2390507 = 3585761) B3585761
theorem B9075503 : Blo 1592995 9075503 := bstep (se 1 (by rfl) ⟨6806627, by rfl⟩ : syracuseStep 9075503 = 13613255) B13613255
theorem B1792831 : Blo 1592995 1792831 := bstep (se 1 (by rfl) ⟨1344623, by rfl⟩ : syracuseStep 1792831 = 2689247) B2689247
theorem B2390855 : Blo 1592995 2390855 := bstep (se 1 (by rfl) ⟨1793141, by rfl⟩ : syracuseStep 2390855 = 3586283) B3586283
theorem B2554735 : Blo 1592995 2554735 := bstep (se 1 (by rfl) ⟨1916051, by rfl⟩ : syracuseStep 2554735 = 3832103) B3832103
theorem B6806663 : Blo 1592995 6806663 := bstep (se 1 (by rfl) ⟨5104997, by rfl⟩ : syracuseStep 6806663 = 10209995) B10209995
theorem B141712757 : Blo 1592995 141712757 := bstep (se 5 (by rfl) ⟨6642785, by rfl⟩ : syracuseStep 141712757 = 13285571) B13285571
theorem B1793407 : Blo 1592995 1793407 := bstep (se 1 (by rfl) ⟨1345055, by rfl⟩ : syracuseStep 1793407 = 2690111) B2690111
theorem B104873453 : Blo 1592995 104873453 := bstep (se 3 (by rfl) ⟨19663772, by rfl⟩ : syracuseStep 104873453 = 39327545) B39327545
theorem B2391689 : Blo 1592995 2391689 := bstep (se 2 (by rfl) ⟨896883, by rfl⟩ : syracuseStep 2391689 = 1793767) B1793767
theorem B2391719 : Blo 1592995 2391719 := bstep (se 1 (by rfl) ⟨1793789, by rfl⟩ : syracuseStep 2391719 = 3587579) B3587579
theorem B2391839 : Blo 1592995 2391839 := bstep (se 1 (by rfl) ⟨1793879, by rfl⟩ : syracuseStep 2391839 = 3587759) B3587759
theorem B2391899 : Blo 1592995 2391899 := bstep (se 1 (by rfl) ⟨1793924, by rfl⟩ : syracuseStep 2391899 = 3587849) B3587849
theorem B12918851 : Blo 1592995 12918851 := bstep (se 1 (by rfl) ⟨9689138, by rfl⟩ : syracuseStep 12918851 = 19378277) B19378277
theorem B20414551 : Blo 1592995 20414551 := bstep (se 1 (by rfl) ⟨15310913, by rfl⟩ : syracuseStep 20414551 = 30621827) B30621827
theorem B3588407 : Blo 1592995 3588407 := bstep (se 1 (by rfl) ⟨2691305, by rfl⟩ : syracuseStep 3588407 = 5382611) B5382611
theorem B5382503 : Blo 1592995 5382503 := bstep (se 1 (by rfl) ⟨4036877, by rfl⟩ : syracuseStep 5382503 = 8073755) B8073755
theorem B6463867 : Blo 1592995 6463867 := bstep (se 1 (by rfl) ⟨4847900, by rfl⟩ : syracuseStep 6463867 = 9695801) B9695801
theorem B18399719 : Blo 1592995 18399719 := bstep (se 1 (by rfl) ⟨13799789, by rfl⟩ : syracuseStep 18399719 = 27599579) B27599579
theorem B5177947 : Blo 1592995 5177947 := bstep (se 1 (by rfl) ⟨3883460, by rfl⟩ : syracuseStep 5177947 = 7766921) B7766921
theorem B15319799 : Blo 1592995 15319799 := bstep (se 1 (by rfl) ⟨11489849, by rfl⟩ : syracuseStep 15319799 = 22979699) B22979699
theorem B23298839 : Blo 1592995 23298839 := bstep (se 1 (by rfl) ⟨17474129, by rfl⟩ : syracuseStep 23298839 = 34948259) B34948259
theorem B36815771 : Blo 1592995 36815771 := bstep (se 1 (by rfl) ⟨27611828, by rfl⟩ : syracuseStep 36815771 = 55223657) B55223657
theorem B9077669 : Blo 1592995 9077669 := bstep (se 4 (by rfl) ⟨851031, by rfl⟩ : syracuseStep 9077669 = 1702063) B1702063
theorem B19645415 : Blo 1592995 19645415 := bstep (se 1 (by rfl) ⟨14734061, by rfl⟩ : syracuseStep 19645415 = 29468123) B29468123
theorem B6054983 : Blo 1592995 6054983 := bstep (se 1 (by rfl) ⟨4541237, by rfl⟩ : syracuseStep 6054983 = 9082475) B9082475
theorem B25838675 : Blo 1592995 25838675 := bstep (se 1 (by rfl) ⟨19379006, by rfl⟩ : syracuseStep 25838675 = 38758013) B38758013
theorem B69887225 : Blo 1592995 69887225 := bstep (se 2 (by rfl) ⟨26207709, by rfl⟩ : syracuseStep 69887225 = 52415419) B52415419
theorem B6808951 : Blo 1592995 6808951 := bstep (se 1 (by rfl) ⟨5106713, by rfl⟩ : syracuseStep 6808951 = 10213427) B10213427
theorem B2762111 : Blo 1592995 2762111 := bstep (se 1 (by rfl) ⟨2071583, by rfl⟩ : syracuseStep 2762111 = 4143167) B4143167
theorem B6997423 : Blo 1592995 6997423 := bstep (se 1 (by rfl) ⟨5248067, by rfl⟩ : syracuseStep 6997423 = 10496135) B10496135
theorem B2688923 : Blo 1592995 2688923 := bstep (se 1 (by rfl) ⟨2016692, by rfl⟩ : syracuseStep 2688923 = 4033385) B4033385
theorem B5376455 : Blo 1592995 5376455 := bstep (se 1 (by rfl) ⟨4032341, by rfl⟩ : syracuseStep 5376455 = 8064683) B8064683
theorem B18410105 : Blo 1592995 18410105 := bstep (se 2 (by rfl) ⟨6903789, by rfl⟩ : syracuseStep 18410105 = 13807579) B13807579
theorem B11488031 : Blo 1592995 11488031 := bstep (se 1 (by rfl) ⟨8616023, by rfl⟩ : syracuseStep 11488031 = 17232047) B17232047
theorem B26192845 : Blo 1592995 26192845 := bstep (se 3 (by rfl) ⟨4911158, by rfl⟩ : syracuseStep 26192845 = 9822317) B9822317
theorem B45935747 : Blo 1592995 45935747 := bstep (se 1 (by rfl) ⟨34451810, by rfl⟩ : syracuseStep 45935747 = 68903621) B68903621
theorem B8072783 : Blo 1592995 8072783 := bstep (se 1 (by rfl) ⟨6054587, by rfl⟩ : syracuseStep 8072783 = 12109175) B12109175
theorem B2690671 : Blo 1592995 2690671 := bstep (se 1 (by rfl) ⟨2018003, by rfl⟩ : syracuseStep 2690671 = 4036007) B4036007
theorem B1593071 : Blo 1592995 1593071 := bstep (se 1 (by rfl) ⟨1194803, by rfl⟩ : syracuseStep 1593071 = 2389607) B2389607
theorem B1593375 : Blo 1592995 1593375 := bstep (se 1 (by rfl) ⟨1195031, by rfl⟩ : syracuseStep 1593375 = 2390063) B2390063
theorem B1593455 : Blo 1592995 1593455 := bstep (se 1 (by rfl) ⟨1195091, by rfl⟩ : syracuseStep 1593455 = 2390183) B2390183
theorem B2551999 : Blo 1592995 2551999 := bstep (se 1 (by rfl) ⟨1913999, by rfl⟩ : syracuseStep 2551999 = 3827999) B3827999
theorem B1593551 : Blo 1592995 1593551 := bstep (se 1 (by rfl) ⟨1195163, by rfl⟩ : syracuseStep 1593551 = 2390327) B2390327
theorem B8073431 : Blo 1592995 8073431 := bstep (se 1 (by rfl) ⟨6055073, by rfl⟩ : syracuseStep 8073431 = 12110147) B12110147
theorem B7270631 : Blo 1592995 7270631 := bstep (se 1 (by rfl) ⟨5452973, by rfl⟩ : syracuseStep 7270631 = 10905947) B10905947
theorem B5378291 : Blo 1592995 5378291 := bstep (se 1 (by rfl) ⟨4033718, by rfl⟩ : syracuseStep 5378291 = 8067437) B8067437
theorem B8294723 : Blo 1592995 8294723 := bstep (se 1 (by rfl) ⟨6221042, by rfl⟩ : syracuseStep 8294723 = 12442085) B12442085
theorem B1593671 : Blo 1592995 1593671 := bstep (se 1 (by rfl) ⟨1195253, by rfl⟩ : syracuseStep 1593671 = 2390507) B2390507
theorem B3027431 : Blo 1592995 3027431 := bstep (se 1 (by rfl) ⟨2270573, by rfl⟩ : syracuseStep 3027431 = 4541147) B4541147
theorem B6050335 : Blo 1592995 6050335 := bstep (se 1 (by rfl) ⟨4537751, by rfl⟩ : syracuseStep 6050335 = 9075503) B9075503
theorem B1593903 : Blo 1592995 1593903 := bstep (se 1 (by rfl) ⟨1195427, by rfl⟩ : syracuseStep 1593903 = 2390855) B2390855
theorem B27603793 : Blo 1592995 27603793 := bstep (se 2 (by rfl) ⟨10351422, by rfl⟩ : syracuseStep 27603793 = 20702845) B20702845
theorem B94475171 : Blo 1592995 94475171 := bstep (se 1 (by rfl) ⟨70856378, by rfl⟩ : syracuseStep 94475171 = 141712757) B141712757
theorem B69915635 : Blo 1592995 69915635 := bstep (se 1 (by rfl) ⟨52436726, by rfl⟩ : syracuseStep 69915635 = 104873453) B104873453
theorem B6812711 : Blo 1592995 6812711 := bstep (se 1 (by rfl) ⟨5109533, by rfl⟩ : syracuseStep 6812711 = 10219067) B10219067
theorem B1594459 : Blo 1592995 1594459 := bstep (se 1 (by rfl) ⟨1195844, by rfl⟩ : syracuseStep 1594459 = 2391689) B2391689
theorem B1594479 : Blo 1592995 1594479 := bstep (se 1 (by rfl) ⟨1195859, by rfl⟩ : syracuseStep 1594479 = 2391719) B2391719
theorem B55227581 : Blo 1592995 55227581 := bstep (se 3 (by rfl) ⟨10355171, by rfl⟩ : syracuseStep 55227581 = 20710343) B20710343
theorem B1594559 : Blo 1592995 1594559 := bstep (se 1 (by rfl) ⟨1195919, by rfl⟩ : syracuseStep 1594559 = 2391839) B2391839
theorem B1594599 : Blo 1592995 1594599 := bstep (se 1 (by rfl) ⟨1195949, by rfl⟩ : syracuseStep 1594599 = 2391899) B2391899
theorem B1701119 : Blo 1592995 1701119 := bstep (se 1 (by rfl) ⟨1275839, by rfl⟩ : syracuseStep 1701119 = 2551679) B2551679
theorem B188781961 : Blo 1592995 188781961 := bstep (se 2 (by rfl) ⟨70793235, by rfl⟩ : syracuseStep 188781961 = 141586471) B141586471
theorem B2553319 : Blo 1592995 2553319 := bstep (se 1 (by rfl) ⟨1914989, by rfl⟩ : syracuseStep 2553319 = 3829979) B3829979
theorem B1594879 : Blo 1592995 1594879 := bstep (se 1 (by rfl) ⟨1196159, by rfl⟩ : syracuseStep 1594879 = 2392319) B2392319
theorem B1594983 : Blo 1592995 1594983 := bstep (se 1 (by rfl) ⟨1196237, by rfl⟩ : syracuseStep 1594983 = 2392475) B2392475
theorem B2389871 : Blo 1592995 2389871 := bstep (se 1 (by rfl) ⟨1792403, by rfl⟩ : syracuseStep 2389871 = 3584807) B3584807
theorem B2389883 : Blo 1592995 2389883 := bstep (se 1 (by rfl) ⟨1792412, by rfl⟩ : syracuseStep 2389883 = 3584825) B3584825
theorem B5379965 : Blo 1592995 5379965 := bstep (se 3 (by rfl) ⟨1008743, by rfl⟩ : syracuseStep 5379965 = 2017487) B2017487
theorem B34486235 : Blo 1592995 34486235 := bstep (se 1 (by rfl) ⟨25864676, by rfl⟩ : syracuseStep 34486235 = 51729353) B51729353
theorem B5380127 : Blo 1592995 5380127 := bstep (se 1 (by rfl) ⟨4035095, by rfl⟩ : syracuseStep 5380127 = 8070191) B8070191
theorem B2390123 : Blo 1592995 2390123 := bstep (se 1 (by rfl) ⟨1792592, by rfl⟩ : syracuseStep 2390123 = 3585185) B3585185
theorem B18405485 : Blo 1592995 18405485 := bstep (se 3 (by rfl) ⟨3451028, by rfl⟩ : syracuseStep 18405485 = 6902057) B6902057
theorem B2390303 : Blo 1592995 2390303 := bstep (se 1 (by rfl) ⟨1792727, by rfl⟩ : syracuseStep 2390303 = 3585455) B3585455
theorem B2390375 : Blo 1592995 2390375 := bstep (se 1 (by rfl) ⟨1792781, by rfl⟩ : syracuseStep 2390375 = 3585563) B3585563
theorem B2390441 : Blo 1592995 2390441 := bstep (se 2 (by rfl) ⟨896415, by rfl⟩ : syracuseStep 2390441 = 1792831) B1792831
theorem B2390495 : Blo 1592995 2390495 := bstep (se 1 (by rfl) ⟨1792871, by rfl⟩ : syracuseStep 2390495 = 3585743) B3585743
theorem B3406313 : Blo 1592995 3406313 := bstep (se 2 (by rfl) ⟨1277367, by rfl⟩ : syracuseStep 3406313 = 2554735) B2554735
theorem B12106259 : Blo 1592995 12106259 := bstep (se 1 (by rfl) ⟨9079694, by rfl⟩ : syracuseStep 12106259 = 18159389) B18159389
theorem B18152099 : Blo 1592995 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B29080403 : Blo 1592995 29080403 := bstep (se 1 (by rfl) ⟨21810302, by rfl⟩ : syracuseStep 29080403 = 43620605) B43620605
theorem B6052765 : Blo 1592995 6052765 := bstep (se 3 (by rfl) ⟨1134893, by rfl⟩ : syracuseStep 6052765 = 2269787) B2269787
theorem B2391023 : Blo 1592995 2391023 := bstep (se 1 (by rfl) ⟨1793267, by rfl⟩ : syracuseStep 2391023 = 3586535) B3586535
theorem B77585465 : Blo 1592995 77585465 := bstep (se 2 (by rfl) ⟨29094549, by rfl⟩ : syracuseStep 77585465 = 58189099) B58189099
theorem B2391209 : Blo 1592995 2391209 := bstep (se 2 (by rfl) ⟨896703, by rfl⟩ : syracuseStep 2391209 = 1793407) B1793407
theorem B4537775 : Blo 1592995 4537775 := bstep (se 1 (by rfl) ⟨3403331, by rfl⟩ : syracuseStep 4537775 = 6806663) B6806663
theorem B8068733 : Blo 1592995 8068733 := bstep (se 3 (by rfl) ⟨1512887, by rfl⟩ : syracuseStep 8068733 = 3025775) B3025775
theorem B4308617 : Blo 1592995 4308617 := bstep (se 2 (by rfl) ⟨1615731, by rfl⟩ : syracuseStep 4308617 = 3231463) B3231463
theorem B8068895 : Blo 1592995 8068895 := bstep (se 1 (by rfl) ⟨6051671, by rfl⟩ : syracuseStep 8068895 = 12103343) B12103343
theorem B6053737 : Blo 1592995 6053737 := bstep (se 2 (by rfl) ⟨2270151, by rfl⟩ : syracuseStep 6053737 = 4540303) B4540303
theorem B5382287 : Blo 1592995 5382287 := bstep (se 1 (by rfl) ⟨4036715, by rfl⟩ : syracuseStep 5382287 = 8073431) B8073431
theorem B2392271 : Blo 1592995 2392271 := bstep (se 1 (by rfl) ⟨1794203, by rfl⟩ : syracuseStep 2392271 = 3588407) B3588407
theorem B5529815 : Blo 1592995 5529815 := bstep (se 1 (by rfl) ⟨4147361, by rfl⟩ : syracuseStep 5529815 = 8294723) B8294723
theorem B3588335 : Blo 1592995 3588335 := bstep (se 1 (by rfl) ⟨2691251, by rfl⟩ : syracuseStep 3588335 = 5382503) B5382503
theorem B8618489 : Blo 1592995 8618489 := bstep (se 2 (by rfl) ⟨3231933, by rfl⟩ : syracuseStep 8618489 = 6463867) B6463867
theorem B15532559 : Blo 1592995 15532559 := bstep (se 1 (by rfl) ⟨11649419, by rfl⟩ : syracuseStep 15532559 = 23298839) B23298839
theorem B24543847 : Blo 1592995 24543847 := bstep (se 1 (by rfl) ⟨18407885, by rfl⟩ : syracuseStep 24543847 = 36815771) B36815771
theorem B7365629 : Blo 1592995 7365629 := bstep (se 3 (by rfl) ⟨1381055, by rfl⟩ : syracuseStep 7365629 = 2762111) B2762111
theorem B8070353 : Blo 1592995 8070353 := bstep (se 2 (by rfl) ⟨3026382, by rfl⟩ : syracuseStep 8070353 = 6052765) B6052765
theorem B34923793 : Blo 1592995 34923793 := bstep (se 2 (by rfl) ⟨13096422, by rfl⟩ : syracuseStep 34923793 = 26192845) B26192845
theorem B8070839 : Blo 1592995 8070839 := bstep (se 1 (by rfl) ⟨6053129, by rfl⟩ : syracuseStep 8070839 = 12106259) B12106259
theorem B12273403 : Blo 1592995 12273403 := bstep (se 1 (by rfl) ⟨9205052, by rfl⟩ : syracuseStep 12273403 = 18410105) B18410105
theorem B147220229 : Blo 1592995 147220229 := bstep (se 4 (by rfl) ⟨13801896, by rfl⟩ : syracuseStep 147220229 = 27603793) B27603793
theorem B12101399 : Blo 1592995 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B9078601 : Blo 1592995 9078601 := bstep (se 2 (by rfl) ⟨3404475, by rfl⟩ : syracuseStep 9078601 = 6808951) B6808951
theorem B251709281 : Blo 1592995 251709281 := bstep (se 2 (by rfl) ⟨94390980, by rfl⟩ : syracuseStep 251709281 = 188781961) B188781961
theorem B30623831 : Blo 1592995 30623831 := bstep (se 1 (by rfl) ⟨22967873, by rfl⟩ : syracuseStep 30623831 = 45935747) B45935747
theorem B3025183 : Blo 1592995 3025183 := bstep (se 1 (by rfl) ⟨2268887, by rfl⟩ : syracuseStep 3025183 = 4537775) B4537775
theorem B8071649 : Blo 1592995 8071649 := bstep (se 2 (by rfl) ⟨3026868, by rfl⟩ : syracuseStep 8071649 = 6053737) B6053737
theorem B8612567 : Blo 1592995 8612567 := bstep (se 1 (by rfl) ⟨6459425, by rfl⟩ : syracuseStep 8612567 = 12918851) B12918851
theorem B3402665 : Blo 1592995 3402665 := bstep (se 2 (by rfl) ⟨1275999, by rfl⟩ : syracuseStep 3402665 = 2551999) B2551999
theorem B12266479 : Blo 1592995 12266479 := bstep (se 1 (by rfl) ⟨9199859, by rfl⟩ : syracuseStep 12266479 = 18399719) B18399719
theorem B2018287 : Blo 1592995 2018287 := bstep (se 1 (by rfl) ⟨1513715, by rfl⟩ : syracuseStep 2018287 = 3027431) B3027431
theorem B4541807 : Blo 1592995 4541807 := bstep (se 1 (by rfl) ⟨3406355, by rfl⟩ : syracuseStep 4541807 = 6812711) B6812711
theorem B36818387 : Blo 1592995 36818387 := bstep (se 1 (by rfl) ⟨27613790, by rfl⟩ : syracuseStep 36818387 = 55227581) B55227581
theorem B46591483 : Blo 1592995 46591483 := bstep (se 1 (by rfl) ⟨34943612, by rfl⟩ : syracuseStep 46591483 = 69887225) B69887225
theorem B1593247 : Blo 1592995 1593247 := bstep (se 1 (by rfl) ⟨1194935, by rfl⟩ : syracuseStep 1593247 = 2389871) B2389871
theorem B1593255 : Blo 1592995 1593255 := bstep (se 1 (by rfl) ⟨1194941, by rfl⟩ : syracuseStep 1593255 = 2389883) B2389883
theorem B22990823 : Blo 1592995 22990823 := bstep (se 1 (by rfl) ⟨17243117, by rfl⟩ : syracuseStep 22990823 = 34486235) B34486235
theorem B1593415 : Blo 1592995 1593415 := bstep (se 1 (by rfl) ⟨1195061, by rfl⟩ : syracuseStep 1593415 = 2390123) B2390123
theorem B1593535 : Blo 1592995 1593535 := bstep (se 1 (by rfl) ⟨1195151, by rfl⟩ : syracuseStep 1593535 = 2390303) B2390303
theorem B1593583 : Blo 1592995 1593583 := bstep (se 1 (by rfl) ⟨1195187, by rfl⟩ : syracuseStep 1593583 = 2390375) B2390375
theorem B1593627 : Blo 1592995 1593627 := bstep (se 1 (by rfl) ⟨1195220, by rfl⟩ : syracuseStep 1593627 = 2390441) B2390441
theorem B3584303 : Blo 1592995 3584303 := bstep (se 1 (by rfl) ⟨2688227, by rfl⟩ : syracuseStep 3584303 = 5376455) B5376455
theorem B1593663 : Blo 1592995 1593663 := bstep (se 1 (by rfl) ⟨1195247, by rfl⟩ : syracuseStep 1593663 = 2390495) B2390495
theorem B19386935 : Blo 1592995 19386935 := bstep (se 1 (by rfl) ⟨14540201, by rfl⟩ : syracuseStep 19386935 = 29080403) B29080403
theorem B3404425 : Blo 1592995 3404425 := bstep (se 2 (by rfl) ⟨1276659, by rfl⟩ : syracuseStep 3404425 = 2553319) B2553319
theorem B1594015 : Blo 1592995 1594015 := bstep (se 1 (by rfl) ⟨1195511, by rfl⟩ : syracuseStep 1594015 = 2391023) B2391023
theorem B1594139 : Blo 1592995 1594139 := bstep (se 1 (by rfl) ⟨1195604, by rfl⟩ : syracuseStep 1594139 = 2391209) B2391209
theorem B5379155 : Blo 1592995 5379155 := bstep (se 1 (by rfl) ⟨4034366, by rfl⟩ : syracuseStep 5379155 = 8068733) B8068733
theorem B2872411 : Blo 1592995 2872411 := bstep (se 1 (by rfl) ⟨2154308, by rfl⟩ : syracuseStep 2872411 = 4308617) B4308617
theorem B251933789 : Blo 1592995 251933789 := bstep (se 3 (by rfl) ⟨47237585, by rfl⟩ : syracuseStep 251933789 = 94475171) B94475171
theorem B5379263 : Blo 1592995 5379263 := bstep (se 1 (by rfl) ⟨4034447, by rfl⟩ : syracuseStep 5379263 = 8068895) B8068895
theorem B27219401 : Blo 1592995 27219401 := bstep (se 2 (by rfl) ⟨10207275, by rfl⟩ : syracuseStep 27219401 = 20414551) B20414551
theorem B4847087 : Blo 1592995 4847087 := bstep (se 1 (by rfl) ⟨3635315, by rfl⟩ : syracuseStep 4847087 = 7270631) B7270631
theorem B3585527 : Blo 1592995 3585527 := bstep (se 1 (by rfl) ⟨2689145, by rfl⟩ : syracuseStep 3585527 = 5378291) B5378291
theorem B10213199 : Blo 1592995 10213199 := bstep (se 1 (by rfl) ⟨7659899, by rfl⟩ : syracuseStep 10213199 = 15319799) B15319799
theorem B6051779 : Blo 1592995 6051779 := bstep (se 1 (by rfl) ⟨4538834, by rfl⟩ : syracuseStep 6051779 = 9077669) B9077669
theorem B13096943 : Blo 1592995 13096943 := bstep (se 1 (by rfl) ⟨9822707, by rfl⟩ : syracuseStep 13096943 = 19645415) B19645415
theorem B46610423 : Blo 1592995 46610423 := bstep (se 1 (by rfl) ⟨34957817, by rfl⟩ : syracuseStep 46610423 = 69915635) B69915635
theorem B4536317 : Blo 1592995 4536317 := bstep (se 3 (by rfl) ⟨850559, by rfl⟩ : syracuseStep 4536317 = 1701119) B1701119
theorem B8067113 : Blo 1592995 8067113 := bstep (se 2 (by rfl) ⟨3025167, by rfl⟩ : syracuseStep 8067113 = 6050335) B6050335
theorem B4036655 : Blo 1592995 4036655 := bstep (se 1 (by rfl) ⟨3027491, by rfl⟩ : syracuseStep 4036655 = 6054983) B6054983
theorem B17225783 : Blo 1592995 17225783 := bstep (se 1 (by rfl) ⟨12919337, by rfl⟩ : syracuseStep 17225783 = 25838675) B25838675
theorem B6903929 : Blo 1592995 6903929 := bstep (se 2 (by rfl) ⟨2588973, by rfl⟩ : syracuseStep 6903929 = 5177947) B5177947
theorem B3586643 : Blo 1592995 3586643 := bstep (se 1 (by rfl) ⟨2689982, by rfl⟩ : syracuseStep 3586643 = 5379965) B5379965
theorem B1792615 : Blo 1592995 1792615 := bstep (se 1 (by rfl) ⟨1344461, by rfl⟩ : syracuseStep 1792615 = 2688923) B2688923
theorem B9083501 : Blo 1592995 9083501 := bstep (se 3 (by rfl) ⟨1703156, by rfl⟩ : syracuseStep 9083501 = 3406313) B3406313
theorem B3586751 : Blo 1592995 3586751 := bstep (se 1 (by rfl) ⟨2690063, by rfl⟩ : syracuseStep 3586751 = 5380127) B5380127
theorem B12270323 : Blo 1592995 12270323 := bstep (se 1 (by rfl) ⟨9202742, by rfl⟩ : syracuseStep 12270323 = 18405485) B18405485
theorem B7658687 : Blo 1592995 7658687 := bstep (se 1 (by rfl) ⟨5744015, by rfl⟩ : syracuseStep 7658687 = 11488031) B11488031
theorem B9329897 : Blo 1592995 9329897 := bstep (se 2 (by rfl) ⟨3498711, by rfl⟩ : syracuseStep 9329897 = 6997423) B6997423
theorem B51723643 : Blo 1592995 51723643 := bstep (se 1 (by rfl) ⟨38792732, by rfl⟩ : syracuseStep 51723643 = 77585465) B77585465
theorem B3587561 : Blo 1592995 3587561 := bstep (se 2 (by rfl) ⟨1345335, by rfl⟩ : syracuseStep 3587561 = 2690671) B2690671
theorem B5381855 : Blo 1592995 5381855 := bstep (se 1 (by rfl) ⟨4036391, by rfl⟩ : syracuseStep 5381855 = 8072783) B8072783
theorem B3588191 : Blo 1592995 3588191 := bstep (se 1 (by rfl) ⟨2691143, by rfl⟩ : syracuseStep 3588191 = 5382287) B5382287
theorem B3686543 : Blo 1592995 3686543 := bstep (se 1 (by rfl) ⟨2764907, by rfl⟩ : syracuseStep 3686543 = 5529815) B5529815
theorem B2392223 : Blo 1592995 2392223 := bstep (se 1 (by rfl) ⟨1794167, by rfl⟩ : syracuseStep 2392223 = 3588335) B3588335
theorem B10355039 : Blo 1592995 10355039 := bstep (se 1 (by rfl) ⟨7766279, by rfl⟩ : syracuseStep 10355039 = 15532559) B15532559
theorem B15319525 : Blo 1592995 15319525 := bstep (se 4 (by rfl) ⟨1436205, by rfl⟩ : syracuseStep 15319525 = 2872411) B2872411
theorem B4539233 : Blo 1592995 4539233 := bstep (se 2 (by rfl) ⟨1702212, by rfl⟩ : syracuseStep 4539233 = 3404425) B3404425
theorem B18146267 : Blo 1592995 18146267 := bstep (se 1 (by rfl) ⟨13609700, by rfl⟩ : syracuseStep 18146267 = 27219401) B27219401
theorem B6808799 : Blo 1592995 6808799 := bstep (se 1 (by rfl) ⟨5106599, by rfl⟩ : syracuseStep 6808799 = 10213199) B10213199
theorem B167806187 : Blo 1592995 167806187 := bstep (se 1 (by rfl) ⟨125854640, by rfl⟩ : syracuseStep 167806187 = 251709281) B251709281
theorem B31073615 : Blo 1592995 31073615 := bstep (se 1 (by rfl) ⟨23305211, by rfl⟩ : syracuseStep 31073615 = 46610423) B46610423
theorem B3024211 : Blo 1592995 3024211 := bstep (se 1 (by rfl) ⟨2268158, by rfl⟩ : syracuseStep 3024211 = 4536317) B4536317
theorem B20415887 : Blo 1592995 20415887 := bstep (se 1 (by rfl) ⟨15311915, by rfl⟩ : syracuseStep 20415887 = 30623831) B30623831
theorem B46565057 : Blo 1592995 46565057 := bstep (se 2 (by rfl) ⟨17461896, by rfl⟩ : syracuseStep 46565057 = 34923793) B34923793
theorem B6055667 : Blo 1592995 6055667 := bstep (se 1 (by rfl) ⟨4541750, by rfl⟩ : syracuseStep 6055667 = 9083501) B9083501
theorem B32720861 : Blo 1592995 32720861 := bstep (se 3 (by rfl) ⟨6135161, by rfl⟩ : syracuseStep 32720861 = 12270323) B12270323
theorem B62121977 : Blo 1592995 62121977 := bstep (se 2 (by rfl) ⟨23295741, by rfl⟩ : syracuseStep 62121977 = 46591483) B46591483
theorem B5105791 : Blo 1592995 5105791 := bstep (se 1 (by rfl) ⟨3829343, by rfl⟩ : syracuseStep 5105791 = 7658687) B7658687
theorem B6219931 : Blo 1592995 6219931 := bstep (se 1 (by rfl) ⟨4664948, by rfl⟩ : syracuseStep 6219931 = 9329897) B9329897
theorem B24545591 : Blo 1592995 24545591 := bstep (se 1 (by rfl) ⟨18409193, by rfl⟩ : syracuseStep 24545591 = 36818387) B36818387
theorem B5745659 : Blo 1592995 5745659 := bstep (se 1 (by rfl) ⟨4309244, by rfl⟩ : syracuseStep 5745659 = 8618489) B8618489
theorem B4033577 : Blo 1592995 4033577 := bstep (se 2 (by rfl) ⟨1512591, by rfl⟩ : syracuseStep 4033577 = 3025183) B3025183
theorem B4910419 : Blo 1592995 4910419 := bstep (se 1 (by rfl) ⟨3682814, by rfl⟩ : syracuseStep 4910419 = 7365629) B7365629
theorem B167955859 : Blo 1592995 167955859 := bstep (se 1 (by rfl) ⟨125966894, by rfl⟩ : syracuseStep 167955859 = 251933789) B251933789
theorem B4034519 : Blo 1592995 4034519 := bstep (se 1 (by rfl) ⟨3025889, by rfl⟩ : syracuseStep 4034519 = 6051779) B6051779
theorem B16355305 : Blo 1592995 16355305 := bstep (se 2 (by rfl) ⟨6133239, by rfl⟩ : syracuseStep 16355305 = 12266479) B12266479
theorem B2691049 : Blo 1592995 2691049 := bstep (se 2 (by rfl) ⟨1009143, by rfl⟩ : syracuseStep 2691049 = 2018287) B2018287
theorem B5378075 : Blo 1592995 5378075 := bstep (se 1 (by rfl) ⟨4033556, by rfl⟩ : syracuseStep 5378075 = 8067113) B8067113
theorem B2691103 : Blo 1592995 2691103 := bstep (se 1 (by rfl) ⟨2018327, by rfl⟩ : syracuseStep 2691103 = 4036655) B4036655
theorem B68964857 : Blo 1592995 68964857 := bstep (se 2 (by rfl) ⟨25861821, by rfl⟩ : syracuseStep 68964857 = 51723643) B51723643
theorem B3027871 : Blo 1592995 3027871 := bstep (se 1 (by rfl) ⟨2270903, by rfl⟩ : syracuseStep 3027871 = 4541807) B4541807
theorem B16364537 : Blo 1592995 16364537 := bstep (se 2 (by rfl) ⟨6136701, by rfl⟩ : syracuseStep 16364537 = 12273403) B12273403
theorem B12104801 : Blo 1592995 12104801 := bstep (se 2 (by rfl) ⟨4539300, by rfl⟩ : syracuseStep 12104801 = 9078601) B9078601
theorem B1594847 : Blo 1592995 1594847 := bstep (se 1 (by rfl) ⟨1196135, by rfl⟩ : syracuseStep 1594847 = 2392271) B2392271
theorem B2389535 : Blo 1592995 2389535 := bstep (se 1 (by rfl) ⟨1792151, by rfl⟩ : syracuseStep 2389535 = 3584303) B3584303
theorem B12924623 : Blo 1592995 12924623 := bstep (se 1 (by rfl) ⟨9693467, by rfl⟩ : syracuseStep 12924623 = 19386935) B19386935
theorem B3586103 : Blo 1592995 3586103 := bstep (se 1 (by rfl) ⟨2689577, by rfl⟩ : syracuseStep 3586103 = 5379155) B5379155
theorem B3586175 : Blo 1592995 3586175 := bstep (se 1 (by rfl) ⟨2689631, by rfl⟩ : syracuseStep 3586175 = 5379263) B5379263
theorem B2390153 : Blo 1592995 2390153 := bstep (se 2 (by rfl) ⟨896307, by rfl⟩ : syracuseStep 2390153 = 1792615) B1792615
theorem B32725129 : Blo 1592995 32725129 := bstep (se 2 (by rfl) ⟨12271923, by rfl⟩ : syracuseStep 32725129 = 24543847) B24543847
theorem B5380235 : Blo 1592995 5380235 := bstep (se 1 (by rfl) ⟨4035176, by rfl⟩ : syracuseStep 5380235 = 8070353) B8070353
theorem B2390351 : Blo 1592995 2390351 := bstep (se 1 (by rfl) ⟨1792763, by rfl⟩ : syracuseStep 2390351 = 3585527) B3585527
theorem B5380559 : Blo 1592995 5380559 := bstep (se 1 (by rfl) ⟨4035419, by rfl⟩ : syracuseStep 5380559 = 8070839) B8070839
theorem B98146819 : Blo 1592995 98146819 := bstep (se 1 (by rfl) ⟨73610114, by rfl⟩ : syracuseStep 98146819 = 147220229) B147220229
theorem B8067599 : Blo 1592995 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B12925565 : Blo 1592995 12925565 := bstep (se 3 (by rfl) ⟨2423543, by rfl⟩ : syracuseStep 12925565 = 4847087) B4847087
theorem B8731295 : Blo 1592995 8731295 := bstep (se 1 (by rfl) ⟨6548471, by rfl⟩ : syracuseStep 8731295 = 13096943) B13096943
theorem B11483855 : Blo 1592995 11483855 := bstep (se 1 (by rfl) ⟨8612891, by rfl⟩ : syracuseStep 11483855 = 17225783) B17225783
theorem B4602619 : Blo 1592995 4602619 := bstep (se 1 (by rfl) ⟨3451964, by rfl⟩ : syracuseStep 4602619 = 6903929) B6903929
theorem B5381099 : Blo 1592995 5381099 := bstep (se 1 (by rfl) ⟨4035824, by rfl⟩ : syracuseStep 5381099 = 8071649) B8071649
theorem B2391095 : Blo 1592995 2391095 := bstep (se 1 (by rfl) ⟨1793321, by rfl⟩ : syracuseStep 2391095 = 3586643) B3586643
theorem B2391167 : Blo 1592995 2391167 := bstep (se 1 (by rfl) ⟨1793375, by rfl⟩ : syracuseStep 2391167 = 3586751) B3586751
theorem B5741711 : Blo 1592995 5741711 := bstep (se 1 (by rfl) ⟨4306283, by rfl⟩ : syracuseStep 5741711 = 8612567) B8612567
theorem B2268443 : Blo 1592995 2268443 := bstep (se 1 (by rfl) ⟨1701332, by rfl⟩ : syracuseStep 2268443 = 3402665) B3402665
theorem B2391707 : Blo 1592995 2391707 := bstep (se 1 (by rfl) ⟨1793780, by rfl⟩ : syracuseStep 2391707 = 3587561) B3587561
theorem B3587903 : Blo 1592995 3587903 := bstep (se 1 (by rfl) ⟨2690927, by rfl⟩ : syracuseStep 3587903 = 5381855) B5381855
theorem B15327215 : Blo 1592995 15327215 := bstep (se 1 (by rfl) ⟨11495411, by rfl⟩ : syracuseStep 15327215 = 22990823) B22990823
theorem B3588137 : Blo 1592995 3588137 := bstep (se 2 (by rfl) ⟨1345551, by rfl⟩ : syracuseStep 3588137 = 2691103) B2691103
theorem B2392127 : Blo 1592995 2392127 := bstep (se 1 (by rfl) ⟨1794095, by rfl⟩ : syracuseStep 2392127 = 3588191) B3588191
theorem B2457695 : Blo 1592995 2457695 := bstep (se 1 (by rfl) ⟨1843271, by rfl⟩ : syracuseStep 2457695 = 3686543) B3686543
theorem B6807721 : Blo 1592995 6807721 := bstep (se 2 (by rfl) ⟨2552895, by rfl⟩ : syracuseStep 6807721 = 5105791) B5105791
theorem B8069867 : Blo 1592995 8069867 := bstep (se 1 (by rfl) ⟨6052400, by rfl⟩ : syracuseStep 8069867 = 12104801) B12104801
theorem B4539199 : Blo 1592995 4539199 := bstep (se 1 (by rfl) ⟨3404399, by rfl⟩ : syracuseStep 4539199 = 6808799) B6808799
theorem B111870791 : Blo 1592995 111870791 := bstep (se 1 (by rfl) ⟨83903093, by rfl⟩ : syracuseStep 111870791 = 167806187) B167806187
theorem B6136825 : Blo 1592995 6136825 := bstep (se 2 (by rfl) ⟨2301309, by rfl⟩ : syracuseStep 6136825 = 4602619) B4602619
theorem B4032281 : Blo 1592995 4032281 := bstep (se 2 (by rfl) ⟨1512105, by rfl⟩ : syracuseStep 4032281 = 3024211) B3024211
theorem B6547225 : Blo 1592995 6547225 := bstep (se 2 (by rfl) ⟨2455209, by rfl⟩ : syracuseStep 6547225 = 4910419) B4910419
theorem B2689051 : Blo 1592995 2689051 := bstep (se 1 (by rfl) ⟨2016788, by rfl⟩ : syracuseStep 2689051 = 4033577) B4033577
theorem B3827807 : Blo 1592995 3827807 := bstep (se 1 (by rfl) ⟨2870855, by rfl⟩ : syracuseStep 3827807 = 5741711) B5741711
theorem B87255629 : Blo 1592995 87255629 := bstep (se 3 (by rfl) ⟨16360430, by rfl⟩ : syracuseStep 87255629 = 32720861) B32720861
theorem B2689679 : Blo 1592995 2689679 := bstep (se 1 (by rfl) ⟨2017259, by rfl⟩ : syracuseStep 2689679 = 4034519) B4034519
theorem B15321757 : Blo 1592995 15321757 := bstep (se 3 (by rfl) ⟨2872829, by rfl⟩ : syracuseStep 15321757 = 5745659) B5745659
theorem B10218143 : Blo 1592995 10218143 := bstep (se 1 (by rfl) ⟨7663607, by rfl⟩ : syracuseStep 10218143 = 15327215) B15327215
theorem B43633505 : Blo 1592995 43633505 := bstep (se 2 (by rfl) ⟨16362564, by rfl⟩ : syracuseStep 43633505 = 32725129) B32725129
theorem B8293241 : Blo 1592995 8293241 := bstep (se 2 (by rfl) ⟨3109965, by rfl⟩ : syracuseStep 8293241 = 6219931) B6219931
theorem B45976571 : Blo 1592995 45976571 := bstep (se 1 (by rfl) ⟨34482428, by rfl⟩ : syracuseStep 45976571 = 68964857) B68964857
theorem B3026155 : Blo 1592995 3026155 := bstep (se 1 (by rfl) ⟨2269616, by rfl⟩ : syracuseStep 3026155 = 4539233) B4539233
theorem B20426033 : Blo 1592995 20426033 := bstep (se 2 (by rfl) ⟨7659762, by rfl⟩ : syracuseStep 20426033 = 15319525) B15319525
theorem B130862425 : Blo 1592995 130862425 := bstep (se 2 (by rfl) ⟨49073409, by rfl⟩ : syracuseStep 130862425 = 98146819) B98146819
theorem B6049181 : Blo 1592995 6049181 := bstep (se 3 (by rfl) ⟨1134221, by rfl⟩ : syracuseStep 6049181 = 2268443) B2268443
theorem B13610591 : Blo 1592995 13610591 := bstep (se 1 (by rfl) ⟨10207943, by rfl⟩ : syracuseStep 13610591 = 20415887) B20415887
theorem B1593023 : Blo 1592995 1593023 := bstep (se 1 (by rfl) ⟨1194767, by rfl⟩ : syracuseStep 1593023 = 2389535) B2389535
theorem B41414651 : Blo 1592995 41414651 := bstep (se 1 (by rfl) ⟨31060988, by rfl⟩ : syracuseStep 41414651 = 62121977) B62121977
theorem B1593435 : Blo 1592995 1593435 := bstep (se 1 (by rfl) ⟨1195076, by rfl⟩ : syracuseStep 1593435 = 2390153) B2390153
theorem B16363727 : Blo 1592995 16363727 := bstep (se 1 (by rfl) ⟨12272795, by rfl⟩ : syracuseStep 16363727 = 24545591) B24545591
theorem B1593567 : Blo 1592995 1593567 := bstep (se 1 (by rfl) ⟨1195175, by rfl⟩ : syracuseStep 1593567 = 2390351) B2390351
theorem B5378399 : Blo 1592995 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B5820863 : Blo 1592995 5820863 := bstep (se 1 (by rfl) ⟨4365647, by rfl⟩ : syracuseStep 5820863 = 8731295) B8731295
theorem B7655903 : Blo 1592995 7655903 := bstep (se 1 (by rfl) ⟨5741927, by rfl⟩ : syracuseStep 7655903 = 11483855) B11483855
theorem B223941145 : Blo 1592995 223941145 := bstep (se 2 (by rfl) ⟨83977929, by rfl⟩ : syracuseStep 223941145 = 167955859) B167955859
theorem B1594063 : Blo 1592995 1594063 := bstep (se 1 (by rfl) ⟨1195547, by rfl⟩ : syracuseStep 1594063 = 2391095) B2391095
theorem B1594111 : Blo 1592995 1594111 := bstep (se 1 (by rfl) ⟨1195583, by rfl⟩ : syracuseStep 1594111 = 2391167) B2391167
theorem B1594471 : Blo 1592995 1594471 := bstep (se 1 (by rfl) ⟨1195853, by rfl⟩ : syracuseStep 1594471 = 2391707) B2391707
theorem B3585383 : Blo 1592995 3585383 := bstep (se 1 (by rfl) ⟨2689037, by rfl⟩ : syracuseStep 3585383 = 5378075) B5378075
theorem B1594815 : Blo 1592995 1594815 := bstep (se 1 (by rfl) ⟨1196111, by rfl⟩ : syracuseStep 1594815 = 2392223) B2392223
theorem B6903359 : Blo 1592995 6903359 := bstep (se 1 (by rfl) ⟨5177519, by rfl⟩ : syracuseStep 6903359 = 10355039) B10355039
theorem B12097511 : Blo 1592995 12097511 := bstep (se 1 (by rfl) ⟨9073133, by rfl⟩ : syracuseStep 12097511 = 18146267) B18146267
theorem B10909691 : Blo 1592995 10909691 := bstep (se 1 (by rfl) ⟨8182268, by rfl⟩ : syracuseStep 10909691 = 16364537) B16364537
theorem B20715743 : Blo 1592995 20715743 := bstep (se 1 (by rfl) ⟨15536807, by rfl⟩ : syracuseStep 20715743 = 31073615) B31073615
theorem B8616415 : Blo 1592995 8616415 := bstep (se 1 (by rfl) ⟨6462311, by rfl⟩ : syracuseStep 8616415 = 12924623) B12924623
theorem B4037111 : Blo 1592995 4037111 := bstep (se 1 (by rfl) ⟨3027833, by rfl⟩ : syracuseStep 4037111 = 6055667) B6055667
theorem B4037161 : Blo 1592995 4037161 := bstep (se 2 (by rfl) ⟨1513935, by rfl⟩ : syracuseStep 4037161 = 3027871) B3027871
theorem B2390735 : Blo 1592995 2390735 := bstep (se 1 (by rfl) ⟨1793051, by rfl⟩ : syracuseStep 2390735 = 3586103) B3586103
theorem B2390783 : Blo 1592995 2390783 := bstep (se 1 (by rfl) ⟨1793087, by rfl⟩ : syracuseStep 2390783 = 3586175) B3586175
theorem B3586823 : Blo 1592995 3586823 := bstep (se 1 (by rfl) ⟨2690117, by rfl⟩ : syracuseStep 3586823 = 5380235) B5380235
theorem B3587039 : Blo 1592995 3587039 := bstep (se 1 (by rfl) ⟨2690279, by rfl⟩ : syracuseStep 3587039 = 5380559) B5380559
theorem B8617043 : Blo 1592995 8617043 := bstep (se 1 (by rfl) ⟨6462782, by rfl⟩ : syracuseStep 8617043 = 12925565) B12925565
theorem B124173485 : Blo 1592995 124173485 := bstep (se 3 (by rfl) ⟨23282528, by rfl⟩ : syracuseStep 124173485 = 46565057) B46565057
theorem B3587399 : Blo 1592995 3587399 := bstep (se 1 (by rfl) ⟨2690549, by rfl⟩ : syracuseStep 3587399 = 5381099) B5381099
theorem B2391935 : Blo 1592995 2391935 := bstep (se 1 (by rfl) ⟨1793951, by rfl⟩ : syracuseStep 2391935 = 3587903) B3587903
theorem B21807073 : Blo 1592995 21807073 := bstep (se 2 (by rfl) ⟨8177652, by rfl⟩ : syracuseStep 21807073 = 16355305) B16355305
theorem B3588065 : Blo 1592995 3588065 := bstep (se 2 (by rfl) ⟨1345524, by rfl⟩ : syracuseStep 3588065 = 2691049) B2691049
theorem B2392091 : Blo 1592995 2392091 := bstep (se 1 (by rfl) ⟨1794068, by rfl⟩ : syracuseStep 2392091 = 3588137) B3588137
theorem B1638463 : Blo 1592995 1638463 := bstep (se 1 (by rfl) ⟨1228847, by rfl⟩ : syracuseStep 1638463 = 2457695) B2457695
theorem B9076961 : Blo 1592995 9076961 := bstep (se 2 (by rfl) ⟨3403860, by rfl⟩ : syracuseStep 9076961 = 6807721) B6807721
theorem B5103935 : Blo 1592995 5103935 := bstep (se 1 (by rfl) ⟨3827951, by rfl⟩ : syracuseStep 5103935 = 7655903) B7655903
theorem B74580527 : Blo 1592995 74580527 := bstep (se 1 (by rfl) ⟨55935395, by rfl⟩ : syracuseStep 74580527 = 111870791) B111870791
theorem B5382881 : Blo 1592995 5382881 := bstep (se 2 (by rfl) ⟨2018580, by rfl⟩ : syracuseStep 5382881 = 4037161) B4037161
theorem B2688187 : Blo 1592995 2688187 := bstep (se 1 (by rfl) ⟨2016140, by rfl⟩ : syracuseStep 2688187 = 4032281) B4032281
theorem B174483233 : Blo 1592995 174483233 := bstep (se 2 (by rfl) ⟨65431212, by rfl⟩ : syracuseStep 174483233 = 130862425) B130862425
theorem B5744695 : Blo 1592995 5744695 := bstep (se 1 (by rfl) ⟨4308521, by rfl⟩ : syracuseStep 5744695 = 8617043) B8617043
theorem B82782323 : Blo 1592995 82782323 := bstep (se 1 (by rfl) ⟨62086742, by rfl⟩ : syracuseStep 82782323 = 124173485) B124173485
theorem B13617355 : Blo 1592995 13617355 := bstep (se 1 (by rfl) ⟨10213016, by rfl⟩ : syracuseStep 13617355 = 20426033) B20426033
theorem B4032787 : Blo 1592995 4032787 := bstep (se 1 (by rfl) ⟨3024590, by rfl⟩ : syracuseStep 4032787 = 6049181) B6049181
theorem B29076097 : Blo 1592995 29076097 := bstep (se 2 (by rfl) ⟨10903536, by rfl⟩ : syracuseStep 29076097 = 21807073) B21807073
theorem B27609767 : Blo 1592995 27609767 := bstep (se 1 (by rfl) ⟨20707325, by rfl⟩ : syracuseStep 27609767 = 41414651) B41414651
theorem B11488553 : Blo 1592995 11488553 := bstep (se 2 (by rfl) ⟨4308207, by rfl⟩ : syracuseStep 11488553 = 8616415) B8616415
theorem B8065007 : Blo 1592995 8065007 := bstep (se 1 (by rfl) ⟨6048755, by rfl⟩ : syracuseStep 8065007 = 12097511) B12097511
theorem B2551871 : Blo 1592995 2551871 := bstep (se 1 (by rfl) ⟨1913903, by rfl⟩ : syracuseStep 2551871 = 3827807) B3827807
theorem B4034873 : Blo 1592995 4034873 := bstep (se 2 (by rfl) ⟨1513077, by rfl⟩ : syracuseStep 4034873 = 3026155) B3026155
theorem B2691407 : Blo 1592995 2691407 := bstep (se 1 (by rfl) ⟨2018555, by rfl⟩ : syracuseStep 2691407 = 4037111) B4037111
theorem B6812095 : Blo 1592995 6812095 := bstep (se 1 (by rfl) ⟨5109071, by rfl⟩ : syracuseStep 6812095 = 10218143) B10218143
theorem B1593823 : Blo 1592995 1593823 := bstep (se 1 (by rfl) ⟨1195367, by rfl⟩ : syracuseStep 1593823 = 2390735) B2390735
theorem B1593855 : Blo 1592995 1593855 := bstep (se 1 (by rfl) ⟨1195391, by rfl⟩ : syracuseStep 1593855 = 2390783) B2390783
theorem B30651047 : Blo 1592995 30651047 := bstep (se 1 (by rfl) ⟨22988285, by rfl⟩ : syracuseStep 30651047 = 45976571) B45976571
theorem B8729633 : Blo 1592995 8729633 := bstep (se 2 (by rfl) ⟨3273612, by rfl⟩ : syracuseStep 8729633 = 6547225) B6547225
theorem B9073727 : Blo 1592995 9073727 := bstep (se 1 (by rfl) ⟨6805295, by rfl⟩ : syracuseStep 9073727 = 13610591) B13610591
theorem B1594623 : Blo 1592995 1594623 := bstep (se 1 (by rfl) ⟨1195967, by rfl⟩ : syracuseStep 1594623 = 2391935) B2391935
theorem B3585401 : Blo 1592995 3585401 := bstep (se 2 (by rfl) ⟨1344525, by rfl⟩ : syracuseStep 3585401 = 2689051) B2689051
theorem B1594751 : Blo 1592995 1594751 := bstep (se 1 (by rfl) ⟨1196063, by rfl⟩ : syracuseStep 1594751 = 2392127) B2392127
theorem B10909151 : Blo 1592995 10909151 := bstep (se 1 (by rfl) ⟨8181863, by rfl⟩ : syracuseStep 10909151 = 16363727) B16363727
theorem B3585599 : Blo 1592995 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B5379911 : Blo 1592995 5379911 := bstep (se 1 (by rfl) ⟨4034933, by rfl⟩ : syracuseStep 5379911 = 8069867) B8069867
theorem B298588193 : Blo 1592995 298588193 := bstep (se 2 (by rfl) ⟨111970572, by rfl⟩ : syracuseStep 298588193 = 223941145) B223941145
theorem B20429009 : Blo 1592995 20429009 := bstep (se 2 (by rfl) ⟨7660878, by rfl⟩ : syracuseStep 20429009 = 15321757) B15321757
theorem B2390255 : Blo 1592995 2390255 := bstep (se 1 (by rfl) ⟨1792691, by rfl⟩ : syracuseStep 2390255 = 3585383) B3585383
theorem B4602239 : Blo 1592995 4602239 := bstep (se 1 (by rfl) ⟨3451679, by rfl⟩ : syracuseStep 4602239 = 6903359) B6903359
theorem B6052265 : Blo 1592995 6052265 := bstep (se 2 (by rfl) ⟨2269599, by rfl⟩ : syracuseStep 6052265 = 4539199) B4539199
theorem B15522301 : Blo 1592995 15522301 := bstep (se 3 (by rfl) ⟨2910431, by rfl⟩ : syracuseStep 15522301 = 5820863) B5820863
theorem B8182433 : Blo 1592995 8182433 := bstep (se 2 (by rfl) ⟨3068412, by rfl⟩ : syracuseStep 8182433 = 6136825) B6136825
theorem B7273127 : Blo 1592995 7273127 := bstep (se 1 (by rfl) ⟨5454845, by rfl⟩ : syracuseStep 7273127 = 10909691) B10909691
theorem B13810495 : Blo 1592995 13810495 := bstep (se 1 (by rfl) ⟨10357871, by rfl⟩ : syracuseStep 13810495 = 20715743) B20715743
theorem B58170419 : Blo 1592995 58170419 := bstep (se 1 (by rfl) ⟨43627814, by rfl⟩ : syracuseStep 58170419 = 87255629) B87255629
theorem B1793119 : Blo 1592995 1793119 := bstep (se 1 (by rfl) ⟨1344839, by rfl⟩ : syracuseStep 1793119 = 2689679) B2689679
theorem B2391215 : Blo 1592995 2391215 := bstep (se 1 (by rfl) ⟨1793411, by rfl⟩ : syracuseStep 2391215 = 3586823) B3586823
theorem B29089003 : Blo 1592995 29089003 := bstep (se 1 (by rfl) ⟨21816752, by rfl⟩ : syracuseStep 29089003 = 43633505) B43633505
theorem B5528827 : Blo 1592995 5528827 := bstep (se 1 (by rfl) ⟨4146620, by rfl⟩ : syracuseStep 5528827 = 8293241) B8293241
theorem B2391359 : Blo 1592995 2391359 := bstep (se 1 (by rfl) ⟨1793519, by rfl⟩ : syracuseStep 2391359 = 3587039) B3587039
theorem B2391599 : Blo 1592995 2391599 := bstep (se 1 (by rfl) ⟨1793699, by rfl⟩ : syracuseStep 2391599 = 3587399) B3587399
theorem B2392043 : Blo 1592995 2392043 := bstep (se 1 (by rfl) ⟨1794032, by rfl⟩ : syracuseStep 2392043 = 3588065) B3588065
theorem B7659593 : Blo 1592995 7659593 := bstep (se 2 (by rfl) ⟨2872347, by rfl⟩ : syracuseStep 7659593 = 5744695) B5744695
theorem B1794271 : Blo 1592995 1794271 := bstep (se 1 (by rfl) ⟨1345703, by rfl⟩ : syracuseStep 1794271 = 2691407) B2691407
theorem B3588587 : Blo 1592995 3588587 := bstep (se 1 (by rfl) ⟨2691440, by rfl⟩ : syracuseStep 3588587 = 5382881) B5382881
theorem B199058795 : Blo 1592995 199058795 := bstep (se 1 (by rfl) ⟨149294096, by rfl⟩ : syracuseStep 199058795 = 298588193) B298588193
theorem B5376671 : Blo 1592995 5376671 := bstep (se 1 (by rfl) ⟨4032503, by rfl⟩ : syracuseStep 5376671 = 8065007) B8065007
theorem B2689915 : Blo 1592995 2689915 := bstep (se 1 (by rfl) ⟨2017436, by rfl⟩ : syracuseStep 2689915 = 4034873) B4034873
theorem B3402623 : Blo 1592995 3402623 := bstep (se 1 (by rfl) ⟨2551967, by rfl⟩ : syracuseStep 3402623 = 5103935) B5103935
theorem B18156473 : Blo 1592995 18156473 := bstep (se 2 (by rfl) ⟨6808677, by rfl⟩ : syracuseStep 18156473 = 13617355) B13617355
theorem B5377049 : Blo 1592995 5377049 := bstep (se 2 (by rfl) ⟨2016393, by rfl⟩ : syracuseStep 5377049 = 4032787) B4032787
theorem B20434031 : Blo 1592995 20434031 := bstep (se 1 (by rfl) ⟨15325523, by rfl⟩ : syracuseStep 20434031 = 30651047) B30651047
theorem B20696401 : Blo 1592995 20696401 := bstep (se 2 (by rfl) ⟨7761150, by rfl⟩ : syracuseStep 20696401 = 15522301) B15522301
theorem B6049151 : Blo 1592995 6049151 := bstep (se 1 (by rfl) ⟨4536863, by rfl⟩ : syracuseStep 6049151 = 9073727) B9073727
theorem B38768129 : Blo 1592995 38768129 := bstep (se 2 (by rfl) ⟨14538048, by rfl⟩ : syracuseStep 38768129 = 29076097) B29076097
theorem B116322155 : Blo 1592995 116322155 := bstep (se 1 (by rfl) ⟨87241616, by rfl⟩ : syracuseStep 116322155 = 174483233) B174483233
theorem B198881405 : Blo 1592995 198881405 := bstep (se 3 (by rfl) ⟨37290263, by rfl⟩ : syracuseStep 198881405 = 74580527) B74580527
theorem B13619339 : Blo 1592995 13619339 := bstep (se 1 (by rfl) ⟨10214504, by rfl⟩ : syracuseStep 13619339 = 20429009) B20429009
theorem B1593503 : Blo 1592995 1593503 := bstep (se 1 (by rfl) ⟨1195127, by rfl⟩ : syracuseStep 1593503 = 2390255) B2390255
theorem B3584249 : Blo 1592995 3584249 := bstep (se 2 (by rfl) ⟨1344093, by rfl⟩ : syracuseStep 3584249 = 2688187) B2688187
theorem B3068159 : Blo 1592995 3068159 := bstep (se 1 (by rfl) ⟨2301119, by rfl⟩ : syracuseStep 3068159 = 4602239) B4602239
theorem B4034843 : Blo 1592995 4034843 := bstep (se 1 (by rfl) ⟨3026132, by rfl⟩ : syracuseStep 4034843 = 6052265) B6052265
theorem B38785337 : Blo 1592995 38785337 := bstep (se 2 (by rfl) ⟨14544501, by rfl⟩ : syracuseStep 38785337 = 29089003) B29089003
theorem B1594143 : Blo 1592995 1594143 := bstep (se 1 (by rfl) ⟨1195607, by rfl⟩ : syracuseStep 1594143 = 2391215) B2391215
theorem B1594239 : Blo 1592995 1594239 := bstep (se 1 (by rfl) ⟨1195679, by rfl⟩ : syracuseStep 1594239 = 2391359) B2391359
theorem B1594399 : Blo 1592995 1594399 := bstep (se 1 (by rfl) ⟨1195799, by rfl⟩ : syracuseStep 1594399 = 2391599) B2391599
theorem B1594695 : Blo 1592995 1594695 := bstep (se 1 (by rfl) ⟨1196021, by rfl⟩ : syracuseStep 1594695 = 2392043) B2392043
theorem B1594727 : Blo 1592995 1594727 := bstep (se 1 (by rfl) ⟨1196045, by rfl⟩ : syracuseStep 1594727 = 2392091) B2392091
theorem B1701247 : Blo 1592995 1701247 := bstep (se 1 (by rfl) ⟨1275935, by rfl⟩ : syracuseStep 1701247 = 2551871) B2551871
theorem B2184617 : Blo 1592995 2184617 := bstep (se 2 (by rfl) ⟨819231, by rfl⟩ : syracuseStep 2184617 = 1638463) B1638463
theorem B23279021 : Blo 1592995 23279021 := bstep (se 3 (by rfl) ⟨4364816, by rfl⟩ : syracuseStep 23279021 = 8729633) B8729633
theorem B6051307 : Blo 1592995 6051307 := bstep (se 1 (by rfl) ⟨4538480, by rfl⟩ : syracuseStep 6051307 = 9076961) B9076961
theorem B9082793 : Blo 1592995 9082793 := bstep (se 2 (by rfl) ⟨3406047, by rfl⟩ : syracuseStep 9082793 = 6812095) B6812095
theorem B2390267 : Blo 1592995 2390267 := bstep (se 1 (by rfl) ⟨1792700, by rfl⟩ : syracuseStep 2390267 = 3585401) B3585401
theorem B7272767 : Blo 1592995 7272767 := bstep (se 1 (by rfl) ⟨5454575, by rfl⟩ : syracuseStep 7272767 = 10909151) B10909151
theorem B2390399 : Blo 1592995 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B18413993 : Blo 1592995 18413993 := bstep (se 2 (by rfl) ⟨6905247, by rfl⟩ : syracuseStep 18413993 = 13810495) B13810495
theorem B3586607 : Blo 1592995 3586607 := bstep (se 1 (by rfl) ⟨2689955, by rfl⟩ : syracuseStep 3586607 = 5379911) B5379911
theorem B55188215 : Blo 1592995 55188215 := bstep (se 1 (by rfl) ⟨41391161, by rfl⟩ : syracuseStep 55188215 = 82782323) B82782323
theorem B2390825 : Blo 1592995 2390825 := bstep (se 2 (by rfl) ⟨896559, by rfl⟩ : syracuseStep 2390825 = 1793119) B1793119
theorem B7371769 : Blo 1592995 7371769 := bstep (se 2 (by rfl) ⟨2764413, by rfl⟩ : syracuseStep 7371769 = 5528827) B5528827
theorem B5454955 : Blo 1592995 5454955 := bstep (se 1 (by rfl) ⟨4091216, by rfl⟩ : syracuseStep 5454955 = 8182433) B8182433
theorem B18406511 : Blo 1592995 18406511 := bstep (se 1 (by rfl) ⟨13804883, by rfl⟩ : syracuseStep 18406511 = 27609767) B27609767
theorem B4848751 : Blo 1592995 4848751 := bstep (se 1 (by rfl) ⟨3636563, by rfl⟩ : syracuseStep 4848751 = 7273127) B7273127
theorem B38780279 : Blo 1592995 38780279 := bstep (se 1 (by rfl) ⟨29085209, by rfl⟩ : syracuseStep 38780279 = 58170419) B58170419
theorem B7659035 : Blo 1592995 7659035 := bstep (se 1 (by rfl) ⟨5744276, by rfl⟩ : syracuseStep 7659035 = 11488553) B11488553
theorem B132587603 : Blo 1592995 132587603 := bstep (se 1 (by rfl) ⟨99440702, by rfl⟩ : syracuseStep 132587603 = 198881405) B198881405
theorem B2392361 : Blo 1592995 2392361 := bstep (se 2 (by rfl) ⟨897135, by rfl⟩ : syracuseStep 2392361 = 1794271) B1794271
theorem B2392391 : Blo 1592995 2392391 := bstep (se 1 (by rfl) ⟨1794293, by rfl⟩ : syracuseStep 2392391 = 3588587) B3588587
theorem B5825645 : Blo 1592995 5825645 := bstep (se 3 (by rfl) ⟨1092308, by rfl⟩ : syracuseStep 5825645 = 2184617) B2184617
theorem B49103981 : Blo 1592995 49103981 := bstep (se 3 (by rfl) ⟨9206996, by rfl⟩ : syracuseStep 49103981 = 18413993) B18413993
theorem B6055195 : Blo 1592995 6055195 := bstep (se 1 (by rfl) ⟨4541396, by rfl⟩ : syracuseStep 6055195 = 9082793) B9082793
theorem B36792143 : Blo 1592995 36792143 := bstep (se 1 (by rfl) ⟨27594107, by rfl⟩ : syracuseStep 36792143 = 55188215) B55188215
theorem B4032767 : Blo 1592995 4032767 := bstep (se 1 (by rfl) ⟨3024575, by rfl⟩ : syracuseStep 4032767 = 6049151) B6049151
theorem B5106023 : Blo 1592995 5106023 := bstep (se 1 (by rfl) ⟨3829517, by rfl⟩ : syracuseStep 5106023 = 7659035) B7659035
theorem B77548103 : Blo 1592995 77548103 := bstep (se 1 (by rfl) ⟨58161077, by rfl⟩ : syracuseStep 77548103 = 116322155) B116322155
theorem B5106395 : Blo 1592995 5106395 := bstep (se 1 (by rfl) ⟨3829796, by rfl⟩ : syracuseStep 5106395 = 7659593) B7659593
theorem B9079559 : Blo 1592995 9079559 := bstep (se 1 (by rfl) ⟨6809669, by rfl⟩ : syracuseStep 9079559 = 13619339) B13619339
theorem B2689895 : Blo 1592995 2689895 := bstep (se 1 (by rfl) ⟨2017421, by rfl⟩ : syracuseStep 2689895 = 4034843) B4034843
theorem B25856891 : Blo 1592995 25856891 := bstep (se 1 (by rfl) ⟨19392668, by rfl⟩ : syracuseStep 25856891 = 38785337) B38785337
theorem B29093093 : Blo 1592995 29093093 := bstep (se 4 (by rfl) ⟨2727477, by rfl⟩ : syracuseStep 29093093 = 5454955) B5454955
theorem B132705863 : Blo 1592995 132705863 := bstep (se 1 (by rfl) ⟨99529397, by rfl⟩ : syracuseStep 132705863 = 199058795) B199058795
theorem B15519347 : Blo 1592995 15519347 := bstep (se 1 (by rfl) ⟨11639510, by rfl⟩ : syracuseStep 15519347 = 23279021) B23279021
theorem B1593511 : Blo 1592995 1593511 := bstep (se 1 (by rfl) ⟨1195133, by rfl⟩ : syracuseStep 1593511 = 2390267) B2390267
theorem B1593599 : Blo 1592995 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B3584447 : Blo 1592995 3584447 := bstep (se 1 (by rfl) ⟨2688335, by rfl⟩ : syracuseStep 3584447 = 5376671) B5376671
theorem B27595201 : Blo 1592995 27595201 := bstep (se 2 (by rfl) ⟨10348200, by rfl⟩ : syracuseStep 27595201 = 20696401) B20696401
theorem B1593883 : Blo 1592995 1593883 := bstep (se 1 (by rfl) ⟨1195412, by rfl⟩ : syracuseStep 1593883 = 2390825) B2390825
theorem B12104315 : Blo 1592995 12104315 := bstep (se 1 (by rfl) ⟨9078236, by rfl⟩ : syracuseStep 12104315 = 18156473) B18156473
theorem B3584699 : Blo 1592995 3584699 := bstep (se 1 (by rfl) ⟨2688524, by rfl⟩ : syracuseStep 3584699 = 5377049) B5377049
theorem B2389499 : Blo 1592995 2389499 := bstep (se 1 (by rfl) ⟨1792124, by rfl⟩ : syracuseStep 2389499 = 3584249) B3584249
theorem B25860005 : Blo 1592995 25860005 := bstep (se 4 (by rfl) ⟨2424375, by rfl⟩ : syracuseStep 25860005 = 4848751) B4848751
theorem B8181757 : Blo 1592995 8181757 := bstep (se 3 (by rfl) ⟨1534079, by rfl⟩ : syracuseStep 8181757 = 3068159) B3068159
theorem B3586553 : Blo 1592995 3586553 := bstep (se 2 (by rfl) ⟨1344957, by rfl⟩ : syracuseStep 3586553 = 2689915) B2689915
theorem B9829025 : Blo 1592995 9829025 := bstep (se 2 (by rfl) ⟨3685884, by rfl⟩ : syracuseStep 9829025 = 7371769) B7371769
theorem B4848511 : Blo 1592995 4848511 := bstep (se 1 (by rfl) ⟨3636383, by rfl⟩ : syracuseStep 4848511 = 7272767) B7272767
theorem B2391071 : Blo 1592995 2391071 := bstep (se 1 (by rfl) ⟨1793303, by rfl⟩ : syracuseStep 2391071 = 3586607) B3586607
theorem B2268329 : Blo 1592995 2268329 := bstep (se 2 (by rfl) ⟨850623, by rfl⟩ : syracuseStep 2268329 = 1701247) B1701247
theorem B2268415 : Blo 1592995 2268415 := bstep (se 1 (by rfl) ⟨1701311, by rfl⟩ : syracuseStep 2268415 = 3402623) B3402623
theorem B8068409 : Blo 1592995 8068409 := bstep (se 2 (by rfl) ⟨3025653, by rfl⟩ : syracuseStep 8068409 = 6051307) B6051307
theorem B12271007 : Blo 1592995 12271007 := bstep (se 1 (by rfl) ⟨9203255, by rfl⟩ : syracuseStep 12271007 = 18406511) B18406511
theorem B13622687 : Blo 1592995 13622687 := bstep (se 1 (by rfl) ⟨10217015, by rfl⟩ : syracuseStep 13622687 = 20434031) B20434031
theorem B25853519 : Blo 1592995 25853519 := bstep (se 1 (by rfl) ⟨19390139, by rfl⟩ : syracuseStep 25853519 = 38780279) B38780279
theorem B25845419 : Blo 1592995 25845419 := bstep (se 1 (by rfl) ⟨19384064, by rfl⟩ : syracuseStep 25845419 = 38768129) B38768129
theorem B88391735 : Blo 1592995 88391735 := bstep (se 1 (by rfl) ⟨66293801, by rfl⟩ : syracuseStep 88391735 = 132587603) B132587603
theorem B8069543 : Blo 1592995 8069543 := bstep (se 1 (by rfl) ⟨6052157, by rfl⟩ : syracuseStep 8069543 = 12104315) B12104315
theorem B3883763 : Blo 1592995 3883763 := bstep (se 1 (by rfl) ⟨2912822, by rfl⟩ : syracuseStep 3883763 = 5825645) B5825645
theorem B32735987 : Blo 1592995 32735987 := bstep (se 1 (by rfl) ⟨24551990, by rfl⟩ : syracuseStep 32735987 = 49103981) B49103981
theorem B6464681 : Blo 1592995 6464681 := bstep (se 2 (by rfl) ⟨2424255, by rfl⟩ : syracuseStep 6464681 = 4848511) B4848511
theorem B24528095 : Blo 1592995 24528095 := bstep (se 1 (by rfl) ⟨18396071, by rfl⟩ : syracuseStep 24528095 = 36792143) B36792143
theorem B2688511 : Blo 1592995 2688511 := bstep (se 1 (by rfl) ⟨2016383, by rfl⟩ : syracuseStep 2688511 = 4032767) B4032767
theorem B3024553 : Blo 1592995 3024553 := bstep (se 2 (by rfl) ⟨1134207, by rfl⟩ : syracuseStep 3024553 = 2268415) B2268415
theorem B17237927 : Blo 1592995 17237927 := bstep (se 1 (by rfl) ⟨12928445, by rfl⟩ : syracuseStep 17237927 = 25856891) B25856891
theorem B17230279 : Blo 1592995 17230279 := bstep (se 1 (by rfl) ⟨12922709, by rfl⟩ : syracuseStep 17230279 = 25845419) B25845419
theorem B6048877 : Blo 1592995 6048877 := bstep (se 3 (by rfl) ⟨1134164, by rfl⟩ : syracuseStep 6048877 = 2268329) B2268329
theorem B36793601 : Blo 1592995 36793601 := bstep (se 2 (by rfl) ⟨13797600, by rfl⟩ : syracuseStep 36793601 = 27595201) B27595201
theorem B1592999 : Blo 1592995 1592999 := bstep (se 1 (by rfl) ⟨1194749, by rfl⟩ : syracuseStep 1592999 = 2389499) B2389499
theorem B17240003 : Blo 1592995 17240003 := bstep (se 1 (by rfl) ⟨12930002, by rfl⟩ : syracuseStep 17240003 = 25860005) B25860005
theorem B3404015 : Blo 1592995 3404015 := bstep (se 1 (by rfl) ⟨2553011, by rfl⟩ : syracuseStep 3404015 = 5106023) B5106023
theorem B8073593 : Blo 1592995 8073593 := bstep (se 2 (by rfl) ⟨3027597, by rfl⟩ : syracuseStep 8073593 = 6055195) B6055195
theorem B3404263 : Blo 1592995 3404263 := bstep (se 1 (by rfl) ⟨2553197, by rfl⟩ : syracuseStep 3404263 = 5106395) B5106395
theorem B1594047 : Blo 1592995 1594047 := bstep (se 1 (by rfl) ⟨1195535, by rfl⟩ : syracuseStep 1594047 = 2391071) B2391071
theorem B19395395 : Blo 1592995 19395395 := bstep (se 1 (by rfl) ⟨14546546, by rfl⟩ : syracuseStep 19395395 = 29093093) B29093093
theorem B5378939 : Blo 1592995 5378939 := bstep (se 1 (by rfl) ⟨4034204, by rfl⟩ : syracuseStep 5378939 = 8068409) B8068409
theorem B8180671 : Blo 1592995 8180671 := bstep (se 1 (by rfl) ⟨6135503, by rfl⟩ : syracuseStep 8180671 = 12271007) B12271007
theorem B9081791 : Blo 1592995 9081791 := bstep (se 1 (by rfl) ⟨6811343, by rfl⟩ : syracuseStep 9081791 = 13622687) B13622687
theorem B88470575 : Blo 1592995 88470575 := bstep (se 1 (by rfl) ⟨66352931, by rfl⟩ : syracuseStep 88470575 = 132705863) B132705863
theorem B10909009 : Blo 1592995 10909009 := bstep (se 2 (by rfl) ⟨4090878, by rfl⟩ : syracuseStep 10909009 = 8181757) B8181757
theorem B1594907 : Blo 1592995 1594907 := bstep (se 1 (by rfl) ⟨1196180, by rfl⟩ : syracuseStep 1594907 = 2392361) B2392361
theorem B1594927 : Blo 1592995 1594927 := bstep (se 1 (by rfl) ⟨1196195, by rfl⟩ : syracuseStep 1594927 = 2392391) B2392391
theorem B2389631 : Blo 1592995 2389631 := bstep (se 1 (by rfl) ⟨1792223, by rfl⟩ : syracuseStep 2389631 = 3584447) B3584447
theorem B2389799 : Blo 1592995 2389799 := bstep (se 1 (by rfl) ⟨1792349, by rfl⟩ : syracuseStep 2389799 = 3584699) B3584699
theorem B2391035 : Blo 1592995 2391035 := bstep (se 1 (by rfl) ⟨1793276, by rfl⟩ : syracuseStep 2391035 = 3586553) B3586553
theorem B51698735 : Blo 1592995 51698735 := bstep (se 1 (by rfl) ⟨38774051, by rfl⟩ : syracuseStep 51698735 = 77548103) B77548103
theorem B6552683 : Blo 1592995 6552683 := bstep (se 1 (by rfl) ⟨4914512, by rfl⟩ : syracuseStep 6552683 = 9829025) B9829025
theorem B6053039 : Blo 1592995 6053039 := bstep (se 1 (by rfl) ⟨4539779, by rfl⟩ : syracuseStep 6053039 = 9079559) B9079559
theorem B1793263 : Blo 1592995 1793263 := bstep (se 1 (by rfl) ⟨1344947, by rfl⟩ : syracuseStep 1793263 = 2689895) B2689895
theorem B17235679 : Blo 1592995 17235679 := bstep (se 1 (by rfl) ⟨12926759, by rfl⟩ : syracuseStep 17235679 = 25853519) B25853519
theorem B10346231 : Blo 1592995 10346231 := bstep (se 1 (by rfl) ⟨7759673, by rfl⟩ : syracuseStep 10346231 = 15519347) B15519347
theorem B2269343 : Blo 1592995 2269343 := bstep (se 1 (by rfl) ⟨1702007, by rfl⟩ : syracuseStep 2269343 = 3404015) B3404015
theorem B5382395 : Blo 1592995 5382395 := bstep (se 1 (by rfl) ⟨4036796, by rfl⟩ : syracuseStep 5382395 = 8073593) B8073593
theorem B2589175 : Blo 1592995 2589175 := bstep (se 1 (by rfl) ⟨1941881, by rfl⟩ : syracuseStep 2589175 = 3883763) B3883763
theorem B21823991 : Blo 1592995 21823991 := bstep (se 1 (by rfl) ⟨16367993, by rfl⟩ : syracuseStep 21823991 = 32735987) B32735987
theorem B6054527 : Blo 1592995 6054527 := bstep (se 1 (by rfl) ⟨4540895, by rfl⟩ : syracuseStep 6054527 = 9081791) B9081791
theorem B4539017 : Blo 1592995 4539017 := bstep (se 2 (by rfl) ⟨1702131, by rfl⟩ : syracuseStep 4539017 = 3404263) B3404263
theorem B4309787 : Blo 1592995 4309787 := bstep (se 1 (by rfl) ⟨3232340, by rfl⟩ : syracuseStep 4309787 = 6464681) B6464681
theorem B16352063 : Blo 1592995 16352063 := bstep (se 1 (by rfl) ⟨12264047, by rfl⟩ : syracuseStep 16352063 = 24528095) B24528095
theorem B34465823 : Blo 1592995 34465823 := bstep (se 1 (by rfl) ⟨25849367, by rfl⟩ : syracuseStep 34465823 = 51698735) B51698735
theorem B4368455 : Blo 1592995 4368455 := bstep (se 1 (by rfl) ⟨3276341, by rfl⟩ : syracuseStep 4368455 = 6552683) B6552683
theorem B24529067 : Blo 1592995 24529067 := bstep (se 1 (by rfl) ⟨18396800, by rfl⟩ : syracuseStep 24529067 = 36793601) B36793601
theorem B4032737 : Blo 1592995 4032737 := bstep (se 2 (by rfl) ⟨1512276, by rfl⟩ : syracuseStep 4032737 = 3024553) B3024553
theorem B22980905 : Blo 1592995 22980905 := bstep (se 2 (by rfl) ⟨8617839, by rfl⟩ : syracuseStep 22980905 = 17235679) B17235679
theorem B58927823 : Blo 1592995 58927823 := bstep (se 1 (by rfl) ⟨44195867, by rfl⟩ : syracuseStep 58927823 = 88391735) B88391735
theorem B12930263 : Blo 1592995 12930263 := bstep (se 1 (by rfl) ⟨9697697, by rfl⟩ : syracuseStep 12930263 = 19395395) B19395395
theorem B22973705 : Blo 1592995 22973705 := bstep (se 2 (by rfl) ⟨8615139, by rfl⟩ : syracuseStep 22973705 = 17230279) B17230279
theorem B1593087 : Blo 1592995 1593087 := bstep (se 1 (by rfl) ⟨1194815, by rfl⟩ : syracuseStep 1593087 = 2389631) B2389631
theorem B1593199 : Blo 1592995 1593199 := bstep (se 1 (by rfl) ⟨1194899, by rfl⟩ : syracuseStep 1593199 = 2389799) B2389799
theorem B10907561 : Blo 1592995 10907561 := bstep (se 2 (by rfl) ⟨4090335, by rfl⟩ : syracuseStep 10907561 = 8180671) B8180671
theorem B8065169 : Blo 1592995 8065169 := bstep (se 2 (by rfl) ⟨3024438, by rfl⟩ : syracuseStep 8065169 = 6048877) B6048877
theorem B14545345 : Blo 1592995 14545345 := bstep (se 2 (by rfl) ⟨5454504, by rfl⟩ : syracuseStep 14545345 = 10909009) B10909009
theorem B1594023 : Blo 1592995 1594023 := bstep (se 1 (by rfl) ⟨1195517, by rfl⟩ : syracuseStep 1594023 = 2391035) B2391035
theorem B3584681 : Blo 1592995 3584681 := bstep (se 2 (by rfl) ⟨1344255, by rfl⟩ : syracuseStep 3584681 = 2688511) B2688511
theorem B4035359 : Blo 1592995 4035359 := bstep (se 1 (by rfl) ⟨3026519, by rfl⟩ : syracuseStep 4035359 = 6053039) B6053039
theorem B5379695 : Blo 1592995 5379695 := bstep (se 1 (by rfl) ⟨4034771, by rfl⟩ : syracuseStep 5379695 = 8069543) B8069543
theorem B3585959 : Blo 1592995 3585959 := bstep (se 1 (by rfl) ⟨2689469, by rfl⟩ : syracuseStep 3585959 = 5378939) B5378939
theorem B58980383 : Blo 1592995 58980383 := bstep (se 1 (by rfl) ⟨44235287, by rfl⟩ : syracuseStep 58980383 = 88470575) B88470575
theorem B11491951 : Blo 1592995 11491951 := bstep (se 1 (by rfl) ⟨8618963, by rfl⟩ : syracuseStep 11491951 = 17237927) B17237927
theorem B2391017 : Blo 1592995 2391017 := bstep (se 2 (by rfl) ⟨896631, by rfl⟩ : syracuseStep 2391017 = 1793263) B1793263
theorem B6897487 : Blo 1592995 6897487 := bstep (se 1 (by rfl) ⟨5173115, by rfl⟩ : syracuseStep 6897487 = 10346231) B10346231
theorem B11493335 : Blo 1592995 11493335 := bstep (se 1 (by rfl) ⟨8620001, by rfl⟩ : syracuseStep 11493335 = 17240003) B17240003
theorem B3588263 : Blo 1592995 3588263 := bstep (se 1 (by rfl) ⟨2691197, by rfl⟩ : syracuseStep 3588263 = 5382395) B5382395
theorem B14549327 : Blo 1592995 14549327 := bstep (se 1 (by rfl) ⟨10911995, by rfl⟩ : syracuseStep 14549327 = 21823991) B21823991
theorem B16352711 : Blo 1592995 16352711 := bstep (se 1 (by rfl) ⟨12264533, by rfl⟩ : syracuseStep 16352711 = 24529067) B24529067
theorem B2688491 : Blo 1592995 2688491 := bstep (se 1 (by rfl) ⟨2016368, by rfl⟩ : syracuseStep 2688491 = 4032737) B4032737
theorem B15320603 : Blo 1592995 15320603 := bstep (se 1 (by rfl) ⟨11490452, by rfl⟩ : syracuseStep 15320603 = 22980905) B22980905
theorem B8620175 : Blo 1592995 8620175 := bstep (se 1 (by rfl) ⟨6465131, by rfl⟩ : syracuseStep 8620175 = 12930263) B12930263
theorem B7662223 : Blo 1592995 7662223 := bstep (se 1 (by rfl) ⟨5746667, by rfl⟩ : syracuseStep 7662223 = 11493335) B11493335
theorem B5376779 : Blo 1592995 5376779 := bstep (se 1 (by rfl) ⟨4032584, by rfl⟩ : syracuseStep 5376779 = 8065169) B8065169
theorem B3026011 : Blo 1592995 3026011 := bstep (se 1 (by rfl) ⟨2269508, by rfl⟩ : syracuseStep 3026011 = 4539017) B4539017
theorem B2690239 : Blo 1592995 2690239 := bstep (se 1 (by rfl) ⟨2017679, by rfl⟩ : syracuseStep 2690239 = 4035359) B4035359
theorem B19393793 : Blo 1592995 19393793 := bstep (se 2 (by rfl) ⟨7272672, by rfl⟩ : syracuseStep 19393793 = 14545345) B14545345
theorem B15322601 : Blo 1592995 15322601 := bstep (se 2 (by rfl) ⟨5745975, by rfl⟩ : syracuseStep 15322601 = 11491951) B11491951
theorem B2912303 : Blo 1592995 2912303 := bstep (se 1 (by rfl) ⟨2184227, by rfl⟩ : syracuseStep 2912303 = 4368455) B4368455
theorem B39285215 : Blo 1592995 39285215 := bstep (se 1 (by rfl) ⟨29463911, by rfl⟩ : syracuseStep 39285215 = 58927823) B58927823
theorem B1594011 : Blo 1592995 1594011 := bstep (se 1 (by rfl) ⟨1195508, by rfl⟩ : syracuseStep 1594011 = 2391017) B2391017
theorem B15315803 : Blo 1592995 15315803 := bstep (se 1 (by rfl) ⟨11486852, by rfl⟩ : syracuseStep 15315803 = 22973705) B22973705
theorem B9196649 : Blo 1592995 9196649 := bstep (se 2 (by rfl) ⟨3448743, by rfl⟩ : syracuseStep 9196649 = 6897487) B6897487
theorem B7271707 : Blo 1592995 7271707 := bstep (se 1 (by rfl) ⟨5453780, by rfl⟩ : syracuseStep 7271707 = 10907561) B10907561
theorem B13808933 : Blo 1592995 13808933 := bstep (se 4 (by rfl) ⟨1294587, by rfl⟩ : syracuseStep 13808933 = 2589175) B2589175
theorem B6051581 : Blo 1592995 6051581 := bstep (se 3 (by rfl) ⟨1134671, by rfl⟩ : syracuseStep 6051581 = 2269343) B2269343
theorem B4036351 : Blo 1592995 4036351 := bstep (se 1 (by rfl) ⟨3027263, by rfl⟩ : syracuseStep 4036351 = 6054527) B6054527
theorem B2389787 : Blo 1592995 2389787 := bstep (se 1 (by rfl) ⟨1792340, by rfl⟩ : syracuseStep 2389787 = 3584681) B3584681
theorem B2873191 : Blo 1592995 2873191 := bstep (se 1 (by rfl) ⟨2154893, by rfl⟩ : syracuseStep 2873191 = 4309787) B4309787
theorem B10901375 : Blo 1592995 10901375 := bstep (se 1 (by rfl) ⟨8176031, by rfl⟩ : syracuseStep 10901375 = 16352063) B16352063
theorem B3586463 : Blo 1592995 3586463 := bstep (se 1 (by rfl) ⟨2689847, by rfl⟩ : syracuseStep 3586463 = 5379695) B5379695
theorem B2390639 : Blo 1592995 2390639 := bstep (se 1 (by rfl) ⟨1792979, by rfl⟩ : syracuseStep 2390639 = 3585959) B3585959
theorem B22977215 : Blo 1592995 22977215 := bstep (se 1 (by rfl) ⟨17232911, by rfl⟩ : syracuseStep 22977215 = 34465823) B34465823
theorem B39320255 : Blo 1592995 39320255 := bstep (se 1 (by rfl) ⟨29490191, by rfl⟩ : syracuseStep 39320255 = 58980383) B58980383
theorem B1941535 : Blo 1592995 1941535 := bstep (se 1 (by rfl) ⟨1456151, by rfl⟩ : syracuseStep 1941535 = 2912303) B2912303
theorem B2392175 : Blo 1592995 2392175 := bstep (se 1 (by rfl) ⟨1794131, by rfl⟩ : syracuseStep 2392175 = 3588263) B3588263
theorem B9699551 : Blo 1592995 9699551 := bstep (se 1 (by rfl) ⟨7274663, by rfl⟩ : syracuseStep 9699551 = 14549327) B14549327
theorem B26190143 : Blo 1592995 26190143 := bstep (se 1 (by rfl) ⟨19642607, by rfl⟩ : syracuseStep 26190143 = 39285215) B39285215
theorem B10216297 : Blo 1592995 10216297 := bstep (se 2 (by rfl) ⟨3831111, by rfl⟩ : syracuseStep 10216297 = 7662223) B7662223
theorem B7267583 : Blo 1592995 7267583 := bstep (se 1 (by rfl) ⟨5450687, by rfl⟩ : syracuseStep 7267583 = 10901375) B10901375
theorem B12929195 : Blo 1592995 12929195 := bstep (se 1 (by rfl) ⟨9696896, by rfl⟩ : syracuseStep 12929195 = 19393793) B19393793
theorem B10210535 : Blo 1592995 10210535 := bstep (se 1 (by rfl) ⟨7657901, by rfl⟩ : syracuseStep 10210535 = 15315803) B15315803
theorem B6131099 : Blo 1592995 6131099 := bstep (se 1 (by rfl) ⟨4598324, by rfl⟩ : syracuseStep 6131099 = 9196649) B9196649
theorem B4034387 : Blo 1592995 4034387 := bstep (se 1 (by rfl) ⟨3025790, by rfl⟩ : syracuseStep 4034387 = 6051581) B6051581
theorem B1593191 : Blo 1592995 1593191 := bstep (se 1 (by rfl) ⟨1194893, by rfl⟩ : syracuseStep 1593191 = 2389787) B2389787
theorem B5746783 : Blo 1592995 5746783 := bstep (se 1 (by rfl) ⟨4310087, by rfl⟩ : syracuseStep 5746783 = 8620175) B8620175
theorem B4034681 : Blo 1592995 4034681 := bstep (se 2 (by rfl) ⟨1513005, by rfl⟩ : syracuseStep 4034681 = 3026011) B3026011
theorem B9695609 : Blo 1592995 9695609 := bstep (se 2 (by rfl) ⟨3635853, by rfl⟩ : syracuseStep 9695609 = 7271707) B7271707
theorem B1593759 : Blo 1592995 1593759 := bstep (se 1 (by rfl) ⟨1195319, by rfl⟩ : syracuseStep 1593759 = 2390639) B2390639
theorem B3584519 : Blo 1592995 3584519 := bstep (se 1 (by rfl) ⟨2688389, by rfl⟩ : syracuseStep 3584519 = 5376779) B5376779
theorem B3830921 : Blo 1592995 3830921 := bstep (se 2 (by rfl) ⟨1436595, by rfl⟩ : syracuseStep 3830921 = 2873191) B2873191
theorem B9205955 : Blo 1592995 9205955 := bstep (se 1 (by rfl) ⟨6904466, by rfl⟩ : syracuseStep 9205955 = 13808933) B13808933
theorem B10901807 : Blo 1592995 10901807 := bstep (se 1 (by rfl) ⟨8176355, by rfl⟩ : syracuseStep 10901807 = 16352711) B16352711
theorem B1792327 : Blo 1592995 1792327 := bstep (se 1 (by rfl) ⟨1344245, by rfl⟩ : syracuseStep 1792327 = 2688491) B2688491
theorem B10213735 : Blo 1592995 10213735 := bstep (se 1 (by rfl) ⟨7660301, by rfl⟩ : syracuseStep 10213735 = 15320603) B15320603
theorem B3586985 : Blo 1592995 3586985 := bstep (se 2 (by rfl) ⟨1345119, by rfl⟩ : syracuseStep 3586985 = 2690239) B2690239
theorem B2390975 : Blo 1592995 2390975 := bstep (se 1 (by rfl) ⟨1793231, by rfl⟩ : syracuseStep 2390975 = 3586463) B3586463
theorem B15318143 : Blo 1592995 15318143 := bstep (se 1 (by rfl) ⟨11488607, by rfl⟩ : syracuseStep 15318143 = 22977215) B22977215
theorem B26213503 : Blo 1592995 26213503 := bstep (se 1 (by rfl) ⟨19660127, by rfl⟩ : syracuseStep 26213503 = 39320255) B39320255
theorem B10215067 : Blo 1592995 10215067 := bstep (se 1 (by rfl) ⟨7661300, by rfl⟩ : syracuseStep 10215067 = 15322601) B15322601
theorem B5381801 : Blo 1592995 5381801 := bstep (se 2 (by rfl) ⟨2018175, by rfl⟩ : syracuseStep 5381801 = 4036351) B4036351
theorem B10354853 : Blo 1592995 10354853 := bstep (se 4 (by rfl) ⟨970767, by rfl⟩ : syracuseStep 10354853 = 1941535) B1941535
theorem B6463739 : Blo 1592995 6463739 := bstep (se 1 (by rfl) ⟨4847804, by rfl⟩ : syracuseStep 6463739 = 9695609) B9695609
theorem B8619463 : Blo 1592995 8619463 := bstep (se 1 (by rfl) ⟨6464597, by rfl⟩ : syracuseStep 8619463 = 12929195) B12929195
theorem B6137303 : Blo 1592995 6137303 := bstep (se 1 (by rfl) ⟨4602977, by rfl⟩ : syracuseStep 6137303 = 9205955) B9205955
theorem B7267871 : Blo 1592995 7267871 := bstep (se 1 (by rfl) ⟨5450903, by rfl⟩ : syracuseStep 7267871 = 10901807) B10901807
theorem B2689591 : Blo 1592995 2689591 := bstep (se 1 (by rfl) ⟨2017193, by rfl⟩ : syracuseStep 2689591 = 4034387) B4034387
theorem B2689787 : Blo 1592995 2689787 := bstep (se 1 (by rfl) ⟨2017340, by rfl⟩ : syracuseStep 2689787 = 4034681) B4034681
theorem B7662377 : Blo 1592995 7662377 := bstep (se 2 (by rfl) ⟨2873391, by rfl⟩ : syracuseStep 7662377 = 5746783) B5746783
theorem B6466367 : Blo 1592995 6466367 := bstep (se 1 (by rfl) ⟨4849775, by rfl⟩ : syracuseStep 6466367 = 9699551) B9699551
theorem B17460095 : Blo 1592995 17460095 := bstep (se 1 (by rfl) ⟨13095071, by rfl⟩ : syracuseStep 17460095 = 26190143) B26190143
theorem B13618313 : Blo 1592995 13618313 := bstep (se 2 (by rfl) ⟨5106867, by rfl⟩ : syracuseStep 13618313 = 10213735) B10213735
theorem B4845055 : Blo 1592995 4845055 := bstep (se 1 (by rfl) ⟨3633791, by rfl⟩ : syracuseStep 4845055 = 7267583) B7267583
theorem B34951337 : Blo 1592995 34951337 := bstep (se 2 (by rfl) ⟨13106751, by rfl⟩ : syracuseStep 34951337 = 26213503) B26213503
theorem B1593983 : Blo 1592995 1593983 := bstep (se 1 (by rfl) ⟨1195487, by rfl⟩ : syracuseStep 1593983 = 2390975) B2390975
theorem B10212095 : Blo 1592995 10212095 := bstep (se 1 (by rfl) ⟨7659071, by rfl⟩ : syracuseStep 10212095 = 15318143) B15318143
theorem B13620089 : Blo 1592995 13620089 := bstep (se 2 (by rfl) ⟨5107533, by rfl⟩ : syracuseStep 13620089 = 10215067) B10215067
theorem B1594783 : Blo 1592995 1594783 := bstep (se 1 (by rfl) ⟨1196087, by rfl⟩ : syracuseStep 1594783 = 2392175) B2392175
theorem B2389679 : Blo 1592995 2389679 := bstep (se 1 (by rfl) ⟨1792259, by rfl⟩ : syracuseStep 2389679 = 3584519) B3584519
theorem B2389769 : Blo 1592995 2389769 := bstep (se 2 (by rfl) ⟨896163, by rfl⟩ : syracuseStep 2389769 = 1792327) B1792327
theorem B2553947 : Blo 1592995 2553947 := bstep (se 1 (by rfl) ⟨1915460, by rfl⟩ : syracuseStep 2553947 = 3830921) B3830921
theorem B16349597 : Blo 1592995 16349597 := bstep (se 3 (by rfl) ⟨3065549, by rfl⟩ : syracuseStep 16349597 = 6131099) B6131099
theorem B13621729 : Blo 1592995 13621729 := bstep (se 2 (by rfl) ⟨5108148, by rfl⟩ : syracuseStep 13621729 = 10216297) B10216297
theorem B2391323 : Blo 1592995 2391323 := bstep (se 1 (by rfl) ⟨1793492, by rfl⟩ : syracuseStep 2391323 = 3586985) B3586985
theorem B6807023 : Blo 1592995 6807023 := bstep (se 1 (by rfl) ⟨5105267, by rfl⟩ : syracuseStep 6807023 = 10210535) B10210535
theorem B3587867 : Blo 1592995 3587867 := bstep (se 1 (by rfl) ⟨2690900, by rfl⟩ : syracuseStep 3587867 = 5381801) B5381801
theorem B6808063 : Blo 1592995 6808063 := bstep (se 1 (by rfl) ⟨5106047, by rfl⟩ : syracuseStep 6808063 = 10212095) B10212095
theorem B18162305 : Blo 1592995 18162305 := bstep (se 2 (by rfl) ⟨6810864, by rfl⟩ : syracuseStep 18162305 = 13621729) B13621729
theorem B17236637 : Blo 1592995 17236637 := bstep (se 3 (by rfl) ⟨3231869, by rfl⟩ : syracuseStep 17236637 = 6463739) B6463739
theorem B4310911 : Blo 1592995 4310911 := bstep (se 1 (by rfl) ⟨3233183, by rfl⟩ : syracuseStep 4310911 = 6466367) B6466367
theorem B9078875 : Blo 1592995 9078875 := bstep (se 1 (by rfl) ⟨6809156, by rfl⟩ : syracuseStep 9078875 = 13618313) B13618313
theorem B20433005 : Blo 1592995 20433005 := bstep (se 3 (by rfl) ⟨3831188, by rfl⟩ : syracuseStep 20433005 = 7662377) B7662377
theorem B23300891 : Blo 1592995 23300891 := bstep (se 1 (by rfl) ⟨17475668, by rfl⟩ : syracuseStep 23300891 = 34951337) B34951337
theorem B9080059 : Blo 1592995 9080059 := bstep (se 1 (by rfl) ⟨6810044, by rfl⟩ : syracuseStep 9080059 = 13620089) B13620089
theorem B1593119 : Blo 1592995 1593119 := bstep (se 1 (by rfl) ⟨1194839, by rfl⟩ : syracuseStep 1593119 = 2389679) B2389679
theorem B1593179 : Blo 1592995 1593179 := bstep (se 1 (by rfl) ⟨1194884, by rfl⟩ : syracuseStep 1593179 = 2389769) B2389769
theorem B10899731 : Blo 1592995 10899731 := bstep (se 1 (by rfl) ⟨8174798, by rfl⟩ : syracuseStep 10899731 = 16349597) B16349597
theorem B6460073 : Blo 1592995 6460073 := bstep (se 2 (by rfl) ⟨2422527, by rfl⟩ : syracuseStep 6460073 = 4845055) B4845055
theorem B1594215 : Blo 1592995 1594215 := bstep (se 1 (by rfl) ⟨1195661, by rfl⟩ : syracuseStep 1594215 = 2391323) B2391323
theorem B46560253 : Blo 1592995 46560253 := bstep (se 3 (by rfl) ⟨8730047, by rfl⟩ : syracuseStep 46560253 = 17460095) B17460095
theorem B6903235 : Blo 1592995 6903235 := bstep (se 1 (by rfl) ⟨5177426, by rfl⟩ : syracuseStep 6903235 = 10354853) B10354853
theorem B3586121 : Blo 1592995 3586121 := bstep (se 2 (by rfl) ⟨1344795, by rfl⟩ : syracuseStep 3586121 = 2689591) B2689591
theorem B16366141 : Blo 1592995 16366141 := bstep (se 3 (by rfl) ⟨3068651, by rfl⟩ : syracuseStep 16366141 = 6137303) B6137303
theorem B1702631 : Blo 1592995 1702631 := bstep (se 1 (by rfl) ⟨1276973, by rfl⟩ : syracuseStep 1702631 = 2553947) B2553947
theorem B19380989 : Blo 1592995 19380989 := bstep (se 3 (by rfl) ⟨3633935, by rfl⟩ : syracuseStep 19380989 = 7267871) B7267871
theorem B1793191 : Blo 1592995 1793191 := bstep (se 1 (by rfl) ⟨1344893, by rfl⟩ : syracuseStep 1793191 = 2689787) B2689787
theorem B11492617 : Blo 1592995 11492617 := bstep (se 2 (by rfl) ⟨4309731, by rfl⟩ : syracuseStep 11492617 = 8619463) B8619463
theorem B4538015 : Blo 1592995 4538015 := bstep (se 1 (by rfl) ⟨3403511, by rfl⟩ : syracuseStep 4538015 = 6807023) B6807023
theorem B2391911 : Blo 1592995 2391911 := bstep (se 1 (by rfl) ⟨1793933, by rfl⟩ : syracuseStep 2391911 = 3587867) B3587867
theorem B12108203 : Blo 1592995 12108203 := bstep (se 1 (by rfl) ⟨9081152, by rfl⟩ : syracuseStep 12108203 = 18162305) B18162305
theorem B9077417 : Blo 1592995 9077417 := bstep (se 2 (by rfl) ⟨3404031, by rfl⟩ : syracuseStep 9077417 = 6808063) B6808063
theorem B29065949 : Blo 1592995 29065949 := bstep (se 3 (by rfl) ⟨5449865, by rfl⟩ : syracuseStep 29065949 = 10899731) B10899731
theorem B62080337 : Blo 1592995 62080337 := bstep (se 2 (by rfl) ⟨23280126, by rfl⟩ : syracuseStep 62080337 = 46560253) B46560253
theorem B15533927 : Blo 1592995 15533927 := bstep (se 1 (by rfl) ⟨11650445, by rfl⟩ : syracuseStep 15533927 = 23300891) B23300891
theorem B4540349 : Blo 1592995 4540349 := bstep (se 3 (by rfl) ⟨851315, by rfl⟩ : syracuseStep 4540349 = 1702631) B1702631
theorem B3025343 : Blo 1592995 3025343 := bstep (se 1 (by rfl) ⟨2269007, by rfl⟩ : syracuseStep 3025343 = 4538015) B4538015
theorem B15323489 : Blo 1592995 15323489 := bstep (se 2 (by rfl) ⟨5746308, by rfl⟩ : syracuseStep 15323489 = 11492617) B11492617
theorem B9204313 : Blo 1592995 9204313 := bstep (se 2 (by rfl) ⟨3451617, by rfl⟩ : syracuseStep 9204313 = 6903235) B6903235
theorem B5747881 : Blo 1592995 5747881 := bstep (se 2 (by rfl) ⟨2155455, by rfl⟩ : syracuseStep 5747881 = 4310911) B4310911
theorem B1594607 : Blo 1592995 1594607 := bstep (se 1 (by rfl) ⟨1195955, by rfl⟩ : syracuseStep 1594607 = 2391911) B2391911
theorem B11491091 : Blo 1592995 11491091 := bstep (se 1 (by rfl) ⟨8618318, by rfl⟩ : syracuseStep 11491091 = 17236637) B17236637
theorem B4306715 : Blo 1592995 4306715 := bstep (se 1 (by rfl) ⟨3230036, by rfl⟩ : syracuseStep 4306715 = 6460073) B6460073
theorem B21821521 : Blo 1592995 21821521 := bstep (se 2 (by rfl) ⟨8183070, by rfl⟩ : syracuseStep 21821521 = 16366141) B16366141
theorem B2390747 : Blo 1592995 2390747 := bstep (se 1 (by rfl) ⟨1793060, by rfl⟩ : syracuseStep 2390747 = 3586121) B3586121
theorem B6052583 : Blo 1592995 6052583 := bstep (se 1 (by rfl) ⟨4539437, by rfl⟩ : syracuseStep 6052583 = 9078875) B9078875
theorem B13622003 : Blo 1592995 13622003 := bstep (se 1 (by rfl) ⟨10216502, by rfl⟩ : syracuseStep 13622003 = 20433005) B20433005
theorem B2390921 : Blo 1592995 2390921 := bstep (se 2 (by rfl) ⟨896595, by rfl⟩ : syracuseStep 2390921 = 1793191) B1793191
theorem B12106745 : Blo 1592995 12106745 := bstep (se 2 (by rfl) ⟨4540029, by rfl⟩ : syracuseStep 12106745 = 9080059) B9080059
theorem B51682637 : Blo 1592995 51682637 := bstep (se 3 (by rfl) ⟨9690494, by rfl⟩ : syracuseStep 51682637 = 19380989) B19380989
theorem B10215659 : Blo 1592995 10215659 := bstep (se 1 (by rfl) ⟨7661744, by rfl⟩ : syracuseStep 10215659 = 15323489) B15323489
theorem B12272417 : Blo 1592995 12272417 := bstep (se 2 (by rfl) ⟨4602156, by rfl⟩ : syracuseStep 12272417 = 9204313) B9204313
theorem B41386891 : Blo 1592995 41386891 := bstep (se 1 (by rfl) ⟨31040168, by rfl⟩ : syracuseStep 41386891 = 62080337) B62080337
theorem B7660727 : Blo 1592995 7660727 := bstep (se 1 (by rfl) ⟨5745545, by rfl⟩ : syracuseStep 7660727 = 11491091) B11491091
theorem B10355951 : Blo 1592995 10355951 := bstep (se 1 (by rfl) ⟨7766963, by rfl⟩ : syracuseStep 10355951 = 15533927) B15533927
theorem B2016895 : Blo 1592995 2016895 := bstep (se 1 (by rfl) ⟨1512671, by rfl⟩ : syracuseStep 2016895 = 3025343) B3025343
theorem B8071163 : Blo 1592995 8071163 := bstep (se 1 (by rfl) ⟨6053372, by rfl⟩ : syracuseStep 8071163 = 12106745) B12106745
theorem B8072135 : Blo 1592995 8072135 := bstep (se 1 (by rfl) ⟨6054101, by rfl⟩ : syracuseStep 8072135 = 12108203) B12108203
theorem B19377299 : Blo 1592995 19377299 := bstep (se 1 (by rfl) ⟨14532974, by rfl⟩ : syracuseStep 19377299 = 29065949) B29065949
theorem B2871143 : Blo 1592995 2871143 := bstep (se 1 (by rfl) ⟨2153357, by rfl⟩ : syracuseStep 2871143 = 4306715) B4306715
theorem B3026899 : Blo 1592995 3026899 := bstep (se 1 (by rfl) ⟨2270174, by rfl⟩ : syracuseStep 3026899 = 4540349) B4540349
theorem B7663841 : Blo 1592995 7663841 := bstep (se 2 (by rfl) ⟨2873940, by rfl⟩ : syracuseStep 7663841 = 5747881) B5747881
theorem B1593831 : Blo 1592995 1593831 := bstep (se 1 (by rfl) ⟨1195373, by rfl⟩ : syracuseStep 1593831 = 2390747) B2390747
theorem B4035055 : Blo 1592995 4035055 := bstep (se 1 (by rfl) ⟨3026291, by rfl⟩ : syracuseStep 4035055 = 6052583) B6052583
theorem B9081335 : Blo 1592995 9081335 := bstep (se 1 (by rfl) ⟨6811001, by rfl⟩ : syracuseStep 9081335 = 13622003) B13622003
theorem B1593947 : Blo 1592995 1593947 := bstep (se 1 (by rfl) ⟨1195460, by rfl⟩ : syracuseStep 1593947 = 2390921) B2390921
theorem B29095361 : Blo 1592995 29095361 := bstep (se 2 (by rfl) ⟨10910760, by rfl⟩ : syracuseStep 29095361 = 21821521) B21821521
theorem B6051611 : Blo 1592995 6051611 := bstep (se 1 (by rfl) ⟨4538708, by rfl⟩ : syracuseStep 6051611 = 9077417) B9077417
theorem B137820365 : Blo 1592995 137820365 := bstep (se 3 (by rfl) ⟨25841318, by rfl⟩ : syracuseStep 137820365 = 51682637) B51682637
theorem B6054223 : Blo 1592995 6054223 := bstep (se 1 (by rfl) ⟨4540667, by rfl⟩ : syracuseStep 6054223 = 9081335) B9081335
theorem B55182521 : Blo 1592995 55182521 := bstep (se 2 (by rfl) ⟨20693445, by rfl⟩ : syracuseStep 55182521 = 41386891) B41386891
theorem B2689193 : Blo 1592995 2689193 := bstep (se 2 (by rfl) ⟨1008447, by rfl⟩ : syracuseStep 2689193 = 2016895) B2016895
theorem B6810439 : Blo 1592995 6810439 := bstep (se 1 (by rfl) ⟨5107829, by rfl⟩ : syracuseStep 6810439 = 10215659) B10215659
theorem B5107151 : Blo 1592995 5107151 := bstep (se 1 (by rfl) ⟨3830363, by rfl⟩ : syracuseStep 5107151 = 7660727) B7660727
theorem B4034407 : Blo 1592995 4034407 := bstep (se 1 (by rfl) ⟨3025805, by rfl⟩ : syracuseStep 4034407 = 6051611) B6051611
theorem B1914095 : Blo 1592995 1914095 := bstep (se 1 (by rfl) ⟨1435571, by rfl⟩ : syracuseStep 1914095 = 2871143) B2871143
theorem B4035865 : Blo 1592995 4035865 := bstep (se 2 (by rfl) ⟨1513449, by rfl⟩ : syracuseStep 4035865 = 3026899) B3026899
theorem B5109227 : Blo 1592995 5109227 := bstep (se 1 (by rfl) ⟨3831920, by rfl⟩ : syracuseStep 5109227 = 7663841) B7663841
theorem B8181611 : Blo 1592995 8181611 := bstep (se 1 (by rfl) ⟨6136208, by rfl⟩ : syracuseStep 8181611 = 12272417) B12272417
theorem B5380073 : Blo 1592995 5380073 := bstep (se 2 (by rfl) ⟨2017527, by rfl⟩ : syracuseStep 5380073 = 4035055) B4035055
theorem B6903967 : Blo 1592995 6903967 := bstep (se 1 (by rfl) ⟨5177975, by rfl⟩ : syracuseStep 6903967 = 10355951) B10355951
theorem B19396907 : Blo 1592995 19396907 := bstep (se 1 (by rfl) ⟨14547680, by rfl⟩ : syracuseStep 19396907 = 29095361) B29095361
theorem B5380775 : Blo 1592995 5380775 := bstep (se 1 (by rfl) ⟨4035581, by rfl⟩ : syracuseStep 5380775 = 8071163) B8071163
theorem B91880243 : Blo 1592995 91880243 := bstep (se 1 (by rfl) ⟨68910182, by rfl⟩ : syracuseStep 91880243 = 137820365) B137820365
theorem B5381423 : Blo 1592995 5381423 := bstep (se 1 (by rfl) ⟨4036067, by rfl⟩ : syracuseStep 5381423 = 8072135) B8072135
theorem B12918199 : Blo 1592995 12918199 := bstep (se 1 (by rfl) ⟨9688649, by rfl⟩ : syracuseStep 12918199 = 19377299) B19377299
theorem B5104253 : Blo 1592995 5104253 := bstep (se 3 (by rfl) ⟨957047, by rfl⟩ : syracuseStep 5104253 = 1914095) B1914095
theorem B61253495 : Blo 1592995 61253495 := bstep (se 1 (by rfl) ⟨45940121, by rfl⟩ : syracuseStep 61253495 = 91880243) B91880243
theorem B8072297 : Blo 1592995 8072297 := bstep (se 2 (by rfl) ⟨3027111, by rfl⟩ : syracuseStep 8072297 = 6054223) B6054223
theorem B9080585 : Blo 1592995 9080585 := bstep (se 2 (by rfl) ⟨3405219, by rfl⟩ : syracuseStep 9080585 = 6810439) B6810439
theorem B12931271 : Blo 1592995 12931271 := bstep (se 1 (by rfl) ⟨9698453, by rfl⟩ : syracuseStep 12931271 = 19396907) B19396907
theorem B17224265 : Blo 1592995 17224265 := bstep (se 2 (by rfl) ⟨6459099, by rfl⟩ : syracuseStep 17224265 = 12918199) B12918199
theorem B3404767 : Blo 1592995 3404767 := bstep (se 1 (by rfl) ⟨2553575, by rfl⟩ : syracuseStep 3404767 = 5107151) B5107151
theorem B5379209 : Blo 1592995 5379209 := bstep (se 2 (by rfl) ⟨2017203, by rfl⟩ : syracuseStep 5379209 = 4034407) B4034407
theorem B9205289 : Blo 1592995 9205289 := bstep (se 2 (by rfl) ⟨3451983, by rfl⟩ : syracuseStep 9205289 = 6903967) B6903967
theorem B36788347 : Blo 1592995 36788347 := bstep (se 1 (by rfl) ⟨27591260, by rfl⟩ : syracuseStep 36788347 = 55182521) B55182521
theorem B3406151 : Blo 1592995 3406151 := bstep (se 1 (by rfl) ⟨2554613, by rfl⟩ : syracuseStep 3406151 = 5109227) B5109227
theorem B5454407 : Blo 1592995 5454407 := bstep (se 1 (by rfl) ⟨4090805, by rfl⟩ : syracuseStep 5454407 = 8181611) B8181611
theorem B3586715 : Blo 1592995 3586715 := bstep (se 1 (by rfl) ⟨2690036, by rfl⟩ : syracuseStep 3586715 = 5380073) B5380073
theorem B1792795 : Blo 1592995 1792795 := bstep (se 1 (by rfl) ⟨1344596, by rfl⟩ : syracuseStep 1792795 = 2689193) B2689193
theorem B5381153 : Blo 1592995 5381153 := bstep (se 2 (by rfl) ⟨2017932, by rfl⟩ : syracuseStep 5381153 = 4035865) B4035865
theorem B3587183 : Blo 1592995 3587183 := bstep (se 1 (by rfl) ⟨2690387, by rfl⟩ : syracuseStep 3587183 = 5380775) B5380775
theorem B3587615 : Blo 1592995 3587615 := bstep (se 1 (by rfl) ⟨2690711, by rfl⟩ : syracuseStep 3587615 = 5381423) B5381423
theorem B6136859 : Blo 1592995 6136859 := bstep (se 1 (by rfl) ⟨4602644, by rfl⟩ : syracuseStep 6136859 = 9205289) B9205289
theorem B4539689 : Blo 1592995 4539689 := bstep (se 2 (by rfl) ⟨1702383, by rfl⟩ : syracuseStep 4539689 = 3404767) B3404767
theorem B2270767 : Blo 1592995 2270767 := bstep (se 1 (by rfl) ⟨1703075, by rfl⟩ : syracuseStep 2270767 = 3406151) B3406151
theorem B8620847 : Blo 1592995 8620847 := bstep (se 1 (by rfl) ⟨6465635, by rfl⟩ : syracuseStep 8620847 = 12931271) B12931271
theorem B13611341 : Blo 1592995 13611341 := bstep (se 3 (by rfl) ⟨2552126, by rfl⟩ : syracuseStep 13611341 = 5104253) B5104253
theorem B49051129 : Blo 1592995 49051129 := bstep (se 2 (by rfl) ⟨18394173, by rfl⟩ : syracuseStep 49051129 = 36788347) B36788347
theorem B11482843 : Blo 1592995 11482843 := bstep (se 1 (by rfl) ⟨8612132, by rfl⟩ : syracuseStep 11482843 = 17224265) B17224265
theorem B3586139 : Blo 1592995 3586139 := bstep (se 1 (by rfl) ⟨2689604, by rfl⟩ : syracuseStep 3586139 = 5379209) B5379209
theorem B2390393 : Blo 1592995 2390393 := bstep (se 2 (by rfl) ⟨896397, by rfl⟩ : syracuseStep 2390393 = 1792795) B1792795
theorem B40835663 : Blo 1592995 40835663 := bstep (se 1 (by rfl) ⟨30626747, by rfl⟩ : syracuseStep 40835663 = 61253495) B61253495
theorem B3636271 : Blo 1592995 3636271 := bstep (se 1 (by rfl) ⟨2727203, by rfl⟩ : syracuseStep 3636271 = 5454407) B5454407
theorem B2391143 : Blo 1592995 2391143 := bstep (se 1 (by rfl) ⟨1793357, by rfl⟩ : syracuseStep 2391143 = 3586715) B3586715
theorem B3587435 : Blo 1592995 3587435 := bstep (se 1 (by rfl) ⟨2690576, by rfl⟩ : syracuseStep 3587435 = 5381153) B5381153
theorem B5381531 : Blo 1592995 5381531 := bstep (se 1 (by rfl) ⟨4036148, by rfl⟩ : syracuseStep 5381531 = 8072297) B8072297
theorem B2391455 : Blo 1592995 2391455 := bstep (se 1 (by rfl) ⟨1793591, by rfl⟩ : syracuseStep 2391455 = 3587183) B3587183
theorem B2391743 : Blo 1592995 2391743 := bstep (se 1 (by rfl) ⟨1793807, by rfl⟩ : syracuseStep 2391743 = 3587615) B3587615
theorem B6053723 : Blo 1592995 6053723 := bstep (se 1 (by rfl) ⟨4540292, by rfl⟩ : syracuseStep 6053723 = 9080585) B9080585
theorem B27223775 : Blo 1592995 27223775 := bstep (se 1 (by rfl) ⟨20417831, by rfl⟩ : syracuseStep 27223775 = 40835663) B40835663
theorem B19393445 : Blo 1592995 19393445 := bstep (se 4 (by rfl) ⟨1818135, by rfl⟩ : syracuseStep 19393445 = 3636271) B3636271
theorem B4091239 : Blo 1592995 4091239 := bstep (se 1 (by rfl) ⟨3068429, by rfl⟩ : syracuseStep 4091239 = 6136859) B6136859
theorem B3026459 : Blo 1592995 3026459 := bstep (se 1 (by rfl) ⟨2269844, by rfl⟩ : syracuseStep 3026459 = 4539689) B4539689
theorem B1593595 : Blo 1592995 1593595 := bstep (se 1 (by rfl) ⟨1195196, by rfl⟩ : syracuseStep 1593595 = 2390393) B2390393
theorem B5747231 : Blo 1592995 5747231 := bstep (se 1 (by rfl) ⟨4310423, by rfl⟩ : syracuseStep 5747231 = 8620847) B8620847
theorem B65401505 : Blo 1592995 65401505 := bstep (se 2 (by rfl) ⟨24525564, by rfl⟩ : syracuseStep 65401505 = 49051129) B49051129
theorem B3027689 : Blo 1592995 3027689 := bstep (se 2 (by rfl) ⟨1135383, by rfl⟩ : syracuseStep 3027689 = 2270767) B2270767
theorem B1594095 : Blo 1592995 1594095 := bstep (se 1 (by rfl) ⟨1195571, by rfl⟩ : syracuseStep 1594095 = 2391143) B2391143
theorem B1594303 : Blo 1592995 1594303 := bstep (se 1 (by rfl) ⟨1195727, by rfl⟩ : syracuseStep 1594303 = 2391455) B2391455
theorem B1594495 : Blo 1592995 1594495 := bstep (se 1 (by rfl) ⟨1195871, by rfl⟩ : syracuseStep 1594495 = 2391743) B2391743
theorem B4035815 : Blo 1592995 4035815 := bstep (se 1 (by rfl) ⟨3026861, by rfl⟩ : syracuseStep 4035815 = 6053723) B6053723
theorem B9074227 : Blo 1592995 9074227 := bstep (se 1 (by rfl) ⟨6805670, by rfl⟩ : syracuseStep 9074227 = 13611341) B13611341
theorem B2390759 : Blo 1592995 2390759 := bstep (se 1 (by rfl) ⟨1793069, by rfl⟩ : syracuseStep 2390759 = 3586139) B3586139
theorem B2391623 : Blo 1592995 2391623 := bstep (se 1 (by rfl) ⟨1793717, by rfl⟩ : syracuseStep 2391623 = 3587435) B3587435
theorem B3587687 : Blo 1592995 3587687 := bstep (se 1 (by rfl) ⟨2690765, by rfl⟩ : syracuseStep 3587687 = 5381531) B5381531
theorem B15310457 : Blo 1592995 15310457 := bstep (se 2 (by rfl) ⟨5741421, by rfl⟩ : syracuseStep 15310457 = 11482843) B11482843
theorem B2017639 : Blo 1592995 2017639 := bstep (se 1 (by rfl) ⟨1513229, by rfl⟩ : syracuseStep 2017639 = 3026459) B3026459
theorem B43601003 : Blo 1592995 43601003 := bstep (se 1 (by rfl) ⟨32700752, by rfl⟩ : syracuseStep 43601003 = 65401505) B65401505
theorem B2018459 : Blo 1592995 2018459 := bstep (se 1 (by rfl) ⟨1513844, by rfl⟩ : syracuseStep 2018459 = 3027689) B3027689
theorem B2690543 : Blo 1592995 2690543 := bstep (se 1 (by rfl) ⟨2017907, by rfl⟩ : syracuseStep 2690543 = 4035815) B4035815
theorem B18149183 : Blo 1592995 18149183 := bstep (se 1 (by rfl) ⟨13611887, by rfl⟩ : syracuseStep 18149183 = 27223775) B27223775
theorem B1593839 : Blo 1592995 1593839 := bstep (se 1 (by rfl) ⟨1195379, by rfl⟩ : syracuseStep 1593839 = 2390759) B2390759
theorem B21819941 : Blo 1592995 21819941 := bstep (se 4 (by rfl) ⟨2045619, by rfl⟩ : syracuseStep 21819941 = 4091239) B4091239
theorem B1594415 : Blo 1592995 1594415 := bstep (se 1 (by rfl) ⟨1195811, by rfl⟩ : syracuseStep 1594415 = 2391623) B2391623
theorem B15325949 : Blo 1592995 15325949 := bstep (se 3 (by rfl) ⟨2873615, by rfl⟩ : syracuseStep 15325949 = 5747231) B5747231
theorem B12098969 : Blo 1592995 12098969 := bstep (se 2 (by rfl) ⟨4537113, by rfl⟩ : syracuseStep 12098969 = 9074227) B9074227
theorem B2391791 : Blo 1592995 2391791 := bstep (se 1 (by rfl) ⟨1793843, by rfl⟩ : syracuseStep 2391791 = 3587687) B3587687
theorem B10206971 : Blo 1592995 10206971 := bstep (se 1 (by rfl) ⟨7655228, by rfl⟩ : syracuseStep 10206971 = 15310457) B15310457
theorem B51715853 : Blo 1592995 51715853 := bstep (se 3 (by rfl) ⟨9696722, by rfl⟩ : syracuseStep 51715853 = 19393445) B19393445
theorem B5382557 : Blo 1592995 5382557 := bstep (se 3 (by rfl) ⟨1009229, by rfl⟩ : syracuseStep 5382557 = 2018459) B2018459
theorem B10217299 : Blo 1592995 10217299 := bstep (se 1 (by rfl) ⟨7662974, by rfl⟩ : syracuseStep 10217299 = 15325949) B15325949
theorem B29067335 : Blo 1592995 29067335 := bstep (se 1 (by rfl) ⟨21800501, by rfl⟩ : syracuseStep 29067335 = 43601003) B43601003
theorem B2690185 : Blo 1592995 2690185 := bstep (se 2 (by rfl) ⟨1008819, by rfl⟩ : syracuseStep 2690185 = 2017639) B2017639
theorem B8065979 : Blo 1592995 8065979 := bstep (se 1 (by rfl) ⟨6049484, by rfl⟩ : syracuseStep 8065979 = 12098969) B12098969
theorem B1594527 : Blo 1592995 1594527 := bstep (se 1 (by rfl) ⟨1195895, by rfl⟩ : syracuseStep 1594527 = 2391791) B2391791
theorem B6804647 : Blo 1592995 6804647 := bstep (se 1 (by rfl) ⟨5103485, by rfl⟩ : syracuseStep 6804647 = 10206971) B10206971
theorem B34477235 : Blo 1592995 34477235 := bstep (se 1 (by rfl) ⟨25857926, by rfl⟩ : syracuseStep 34477235 = 51715853) B51715853
theorem B14546627 : Blo 1592995 14546627 := bstep (se 1 (by rfl) ⟨10909970, by rfl⟩ : syracuseStep 14546627 = 21819941) B21819941
theorem B1793695 : Blo 1592995 1793695 := bstep (se 1 (by rfl) ⟨1345271, by rfl⟩ : syracuseStep 1793695 = 2690543) B2690543
theorem B12099455 : Blo 1592995 12099455 := bstep (se 1 (by rfl) ⟨9074591, by rfl⟩ : syracuseStep 12099455 = 18149183) B18149183
theorem B3588371 : Blo 1592995 3588371 := bstep (se 1 (by rfl) ⟨2691278, by rfl⟩ : syracuseStep 3588371 = 5382557) B5382557
theorem B5377319 : Blo 1592995 5377319 := bstep (se 1 (by rfl) ⟨4032989, by rfl⟩ : syracuseStep 5377319 = 8065979) B8065979
theorem B19378223 : Blo 1592995 19378223 := bstep (se 1 (by rfl) ⟨14533667, by rfl⟩ : syracuseStep 19378223 = 29067335) B29067335
theorem B8066303 : Blo 1592995 8066303 := bstep (se 1 (by rfl) ⟨6049727, by rfl⟩ : syracuseStep 8066303 = 12099455) B12099455
theorem B4536431 : Blo 1592995 4536431 := bstep (se 1 (by rfl) ⟨3402323, by rfl⟩ : syracuseStep 4536431 = 6804647) B6804647
theorem B22984823 : Blo 1592995 22984823 := bstep (se 1 (by rfl) ⟨17238617, by rfl⟩ : syracuseStep 22984823 = 34477235) B34477235
theorem B9697751 : Blo 1592995 9697751 := bstep (se 1 (by rfl) ⟨7273313, by rfl⟩ : syracuseStep 9697751 = 14546627) B14546627
theorem B3586913 : Blo 1592995 3586913 := bstep (se 2 (by rfl) ⟨1345092, by rfl⟩ : syracuseStep 3586913 = 2690185) B2690185
theorem B2391593 : Blo 1592995 2391593 := bstep (se 2 (by rfl) ⟨896847, by rfl⟩ : syracuseStep 2391593 = 1793695) B1793695
theorem B13623065 : Blo 1592995 13623065 := bstep (se 2 (by rfl) ⟨5108649, by rfl⟩ : syracuseStep 13623065 = 10217299) B10217299
theorem B12918815 : Blo 1592995 12918815 := bstep (se 1 (by rfl) ⟨9689111, by rfl⟩ : syracuseStep 12918815 = 19378223) B19378223
theorem B2392247 : Blo 1592995 2392247 := bstep (se 1 (by rfl) ⟨1794185, by rfl⟩ : syracuseStep 2392247 = 3588371) B3588371
theorem B61292861 : Blo 1592995 61292861 := bstep (se 3 (by rfl) ⟨11492411, by rfl⟩ : syracuseStep 61292861 = 22984823) B22984823
theorem B3024287 : Blo 1592995 3024287 := bstep (se 1 (by rfl) ⟨2268215, by rfl⟩ : syracuseStep 3024287 = 4536431) B4536431
theorem B6465167 : Blo 1592995 6465167 := bstep (se 1 (by rfl) ⟨4848875, by rfl⟩ : syracuseStep 6465167 = 9697751) B9697751
theorem B5377535 : Blo 1592995 5377535 := bstep (se 1 (by rfl) ⟨4033151, by rfl⟩ : syracuseStep 5377535 = 8066303) B8066303
theorem B3584879 : Blo 1592995 3584879 := bstep (se 1 (by rfl) ⟨2688659, by rfl⟩ : syracuseStep 3584879 = 5377319) B5377319
theorem B1594395 : Blo 1592995 1594395 := bstep (se 1 (by rfl) ⟨1195796, by rfl⟩ : syracuseStep 1594395 = 2391593) B2391593
theorem B9082043 : Blo 1592995 9082043 := bstep (se 1 (by rfl) ⟨6811532, by rfl⟩ : syracuseStep 9082043 = 13623065) B13623065
theorem B2391275 : Blo 1592995 2391275 := bstep (se 1 (by rfl) ⟨1793456, by rfl⟩ : syracuseStep 2391275 = 3586913) B3586913
theorem B40861907 : Blo 1592995 40861907 := bstep (se 1 (by rfl) ⟨30646430, by rfl⟩ : syracuseStep 40861907 = 61292861) B61292861
theorem B6054695 : Blo 1592995 6054695 := bstep (se 1 (by rfl) ⟨4541021, by rfl⟩ : syracuseStep 6054695 = 9082043) B9082043
theorem B2016191 : Blo 1592995 2016191 := bstep (se 1 (by rfl) ⟨1512143, by rfl⟩ : syracuseStep 2016191 = 3024287) B3024287
theorem B4310111 : Blo 1592995 4310111 := bstep (se 1 (by rfl) ⟨3232583, by rfl⟩ : syracuseStep 4310111 = 6465167) B6465167
theorem B8612543 : Blo 1592995 8612543 := bstep (se 1 (by rfl) ⟨6459407, by rfl⟩ : syracuseStep 8612543 = 12918815) B12918815
theorem B1594183 : Blo 1592995 1594183 := bstep (se 1 (by rfl) ⟨1195637, by rfl⟩ : syracuseStep 1594183 = 2391275) B2391275
theorem B3585023 : Blo 1592995 3585023 := bstep (se 1 (by rfl) ⟨2688767, by rfl⟩ : syracuseStep 3585023 = 5377535) B5377535
theorem B1594831 : Blo 1592995 1594831 := bstep (se 1 (by rfl) ⟨1196123, by rfl⟩ : syracuseStep 1594831 = 2392247) B2392247
theorem B2389919 : Blo 1592995 2389919 := bstep (se 1 (by rfl) ⟨1792439, by rfl⟩ : syracuseStep 2389919 = 3584879) B3584879
theorem B5376509 : Blo 1592995 5376509 := bstep (se 3 (by rfl) ⟨1008095, by rfl⟩ : syracuseStep 5376509 = 2016191) B2016191
theorem B27241271 : Blo 1592995 27241271 := bstep (se 1 (by rfl) ⟨20430953, by rfl⟩ : syracuseStep 27241271 = 40861907) B40861907
theorem B1593279 : Blo 1592995 1593279 := bstep (se 1 (by rfl) ⟨1194959, by rfl⟩ : syracuseStep 1593279 = 2389919) B2389919
theorem B4036463 : Blo 1592995 4036463 := bstep (se 1 (by rfl) ⟨3027347, by rfl⟩ : syracuseStep 4036463 = 6054695) B6054695
theorem B2390015 : Blo 1592995 2390015 := bstep (se 1 (by rfl) ⟨1792511, by rfl⟩ : syracuseStep 2390015 = 3585023) B3585023
theorem B2873407 : Blo 1592995 2873407 := bstep (se 1 (by rfl) ⟨2155055, by rfl⟩ : syracuseStep 2873407 = 4310111) B4310111
theorem B5741695 : Blo 1592995 5741695 := bstep (se 1 (by rfl) ⟨4306271, by rfl⟩ : syracuseStep 5741695 = 8612543) B8612543
theorem B30622373 : Blo 1592995 30622373 := bstep (se 4 (by rfl) ⟨2870847, by rfl⟩ : syracuseStep 30622373 = 5741695) B5741695
theorem B2690975 : Blo 1592995 2690975 := bstep (se 1 (by rfl) ⟨2018231, by rfl⟩ : syracuseStep 2690975 = 4036463) B4036463
theorem B1593343 : Blo 1592995 1593343 := bstep (se 1 (by rfl) ⟨1195007, by rfl⟩ : syracuseStep 1593343 = 2390015) B2390015
theorem B3584339 : Blo 1592995 3584339 := bstep (se 1 (by rfl) ⟨2688254, by rfl⟩ : syracuseStep 3584339 = 5376509) B5376509
theorem B3831209 : Blo 1592995 3831209 := bstep (se 2 (by rfl) ⟨1436703, by rfl⟩ : syracuseStep 3831209 = 2873407) B2873407
theorem B18160847 : Blo 1592995 18160847 := bstep (se 1 (by rfl) ⟨13620635, by rfl⟩ : syracuseStep 18160847 = 27241271) B27241271
theorem B20414915 : Blo 1592995 20414915 := bstep (se 1 (by rfl) ⟨15311186, by rfl⟩ : syracuseStep 20414915 = 30622373) B30622373
theorem B2389559 : Blo 1592995 2389559 := bstep (se 1 (by rfl) ⟨1792169, by rfl⟩ : syracuseStep 2389559 = 3584339) B3584339
theorem B2554139 : Blo 1592995 2554139 := bstep (se 1 (by rfl) ⟨1915604, by rfl⟩ : syracuseStep 2554139 = 3831209) B3831209
theorem B12107231 : Blo 1592995 12107231 := bstep (se 1 (by rfl) ⟨9080423, by rfl⟩ : syracuseStep 12107231 = 18160847) B18160847
theorem B1793983 : Blo 1592995 1793983 := bstep (se 1 (by rfl) ⟨1345487, by rfl⟩ : syracuseStep 1793983 = 2690975) B2690975
theorem B8071487 : Blo 1592995 8071487 := bstep (se 1 (by rfl) ⟨6053615, by rfl⟩ : syracuseStep 8071487 = 12107231) B12107231
theorem B13609943 : Blo 1592995 13609943 := bstep (se 1 (by rfl) ⟨10207457, by rfl⟩ : syracuseStep 13609943 = 20414915) B20414915
theorem B6811037 : Blo 1592995 6811037 := bstep (se 3 (by rfl) ⟨1277069, by rfl⟩ : syracuseStep 6811037 = 2554139) B2554139
theorem B1593039 : Blo 1592995 1593039 := bstep (se 1 (by rfl) ⟨1194779, by rfl⟩ : syracuseStep 1593039 = 2389559) B2389559
theorem B2391977 : Blo 1592995 2391977 := bstep (se 2 (by rfl) ⟨896991, by rfl⟩ : syracuseStep 2391977 = 1793983) B1793983
theorem B4540691 : Blo 1592995 4540691 := bstep (se 1 (by rfl) ⟨3405518, by rfl⟩ : syracuseStep 4540691 = 6811037) B6811037
theorem B9073295 : Blo 1592995 9073295 := bstep (se 1 (by rfl) ⟨6804971, by rfl⟩ : syracuseStep 9073295 = 13609943) B13609943
theorem B1594651 : Blo 1592995 1594651 := bstep (se 1 (by rfl) ⟨1195988, by rfl⟩ : syracuseStep 1594651 = 2391977) B2391977
theorem B5380991 : Blo 1592995 5380991 := bstep (se 1 (by rfl) ⟨4035743, by rfl⟩ : syracuseStep 5380991 = 8071487) B8071487
theorem B6048863 : Blo 1592995 6048863 := bstep (se 1 (by rfl) ⟨4536647, by rfl⟩ : syracuseStep 6048863 = 9073295) B9073295
theorem B3027127 : Blo 1592995 3027127 := bstep (se 1 (by rfl) ⟨2270345, by rfl⟩ : syracuseStep 3027127 = 4540691) B4540691
theorem B3587327 : Blo 1592995 3587327 := bstep (se 1 (by rfl) ⟨2690495, by rfl⟩ : syracuseStep 3587327 = 5380991) B5380991
theorem B4032575 : Blo 1592995 4032575 := bstep (se 1 (by rfl) ⟨3024431, by rfl⟩ : syracuseStep 4032575 = 6048863) B6048863
theorem B4036169 : Blo 1592995 4036169 := bstep (se 2 (by rfl) ⟨1513563, by rfl⟩ : syracuseStep 4036169 = 3027127) B3027127
theorem B2391551 : Blo 1592995 2391551 := bstep (se 1 (by rfl) ⟨1793663, by rfl⟩ : syracuseStep 2391551 = 3587327) B3587327
theorem B2688383 : Blo 1592995 2688383 := bstep (se 1 (by rfl) ⟨2016287, by rfl⟩ : syracuseStep 2688383 = 4032575) B4032575
theorem B2690779 : Blo 1592995 2690779 := bstep (se 1 (by rfl) ⟨2018084, by rfl⟩ : syracuseStep 2690779 = 4036169) B4036169
theorem B1594367 : Blo 1592995 1594367 := bstep (se 1 (by rfl) ⟨1195775, by rfl⟩ : syracuseStep 1594367 = 2391551) B2391551
theorem B1792255 : Blo 1592995 1792255 := bstep (se 1 (by rfl) ⟨1344191, by rfl⟩ : syracuseStep 1792255 = 2688383) B2688383
theorem B3587705 : Blo 1592995 3587705 := bstep (se 2 (by rfl) ⟨1345389, by rfl⟩ : syracuseStep 3587705 = 2690779) B2690779
theorem B2389673 : Blo 1592995 2389673 := bstep (se 2 (by rfl) ⟨896127, by rfl⟩ : syracuseStep 2389673 = 1792255) B1792255
theorem B2391803 : Blo 1592995 2391803 := bstep (se 1 (by rfl) ⟨1793852, by rfl⟩ : syracuseStep 2391803 = 3587705) B3587705
theorem B1593115 : Blo 1592995 1593115 := bstep (se 1 (by rfl) ⟨1194836, by rfl⟩ : syracuseStep 1593115 = 2389673) B2389673
theorem B1594535 : Blo 1592995 1594535 := bstep (se 1 (by rfl) ⟨1195901, by rfl⟩ : syracuseStep 1594535 = 2391803) B2391803

theorem C0 (j : ℕ) (h1 : 398248 ≤ j) (h2 : j ≤ 398748) : Blo 1592995 (4 * j + 3) := by
  interval_cases j
  · exact B1592995
  · exact B1592999
  · exact B1593003
  · exact B1593007
  · exact B1593011
  · exact B1593015
  · exact B1593019
  · exact B1593023
  · exact B1593027
  · exact B1593031
  · exact B1593035
  · exact B1593039
  · exact B1593043
  · exact B1593047
  · exact B1593051
  · exact B1593055
  · exact B1593059
  · exact B1593063
  · exact B1593067
  · exact B1593071
  · exact B1593075
  · exact B1593079
  · exact B1593083
  · exact B1593087
  · exact B1593091
  · exact B1593095
  · exact B1593099
  · exact B1593103
  · exact B1593107
  · exact B1593111
  · exact B1593115
  · exact B1593119
  · exact B1593123
  · exact B1593127
  · exact B1593131
  · exact B1593135
  · exact B1593139
  · exact B1593143
  · exact B1593147
  · exact B1593151
  · exact B1593155
  · exact B1593159
  · exact B1593163
  · exact B1593167
  · exact B1593171
  · exact B1593175
  · exact B1593179
  · exact B1593183
  · exact B1593187
  · exact B1593191
  · exact B1593195
  · exact B1593199
  · exact B1593203
  · exact B1593207
  · exact B1593211
  · exact B1593215
  · exact B1593219
  · exact B1593223
  · exact B1593227
  · exact B1593231
  · exact B1593235
  · exact B1593239
  · exact B1593243
  · exact B1593247
  · exact B1593251
  · exact B1593255
  · exact B1593259
  · exact B1593263
  · exact B1593267
  · exact B1593271
  · exact B1593275
  · exact B1593279
  · exact B1593283
  · exact B1593287
  · exact B1593291
  · exact B1593295
  · exact B1593299
  · exact B1593303
  · exact B1593307
  · exact B1593311
  · exact B1593315
  · exact B1593319
  · exact B1593323
  · exact B1593327
  · exact B1593331
  · exact B1593335
  · exact B1593339
  · exact B1593343
  · exact B1593347
  · exact B1593351
  · exact B1593355
  · exact B1593359
  · exact B1593363
  · exact B1593367
  · exact B1593371
  · exact B1593375
  · exact B1593379
  · exact B1593383
  · exact B1593387
  · exact B1593391
  · exact B1593395
  · exact B1593399
  · exact B1593403
  · exact B1593407
  · exact B1593411
  · exact B1593415
  · exact B1593419
  · exact B1593423
  · exact B1593427
  · exact B1593431
  · exact B1593435
  · exact B1593439
  · exact B1593443
  · exact B1593447
  · exact B1593451
  · exact B1593455
  · exact B1593459
  · exact B1593463
  · exact B1593467
  · exact B1593471
  · exact B1593475
  · exact B1593479
  · exact B1593483
  · exact B1593487
  · exact B1593491
  · exact B1593495
  · exact B1593499
  · exact B1593503
  · exact B1593507
  · exact B1593511
  · exact B1593515
  · exact B1593519
  · exact B1593523
  · exact B1593527
  · exact B1593531
  · exact B1593535
  · exact B1593539
  · exact B1593543
  · exact B1593547
  · exact B1593551
  · exact B1593555
  · exact B1593559
  · exact B1593563
  · exact B1593567
  · exact B1593571
  · exact B1593575
  · exact B1593579
  · exact B1593583
  · exact B1593587
  · exact B1593591
  · exact B1593595
  · exact B1593599
  · exact B1593603
  · exact B1593607
  · exact B1593611
  · exact B1593615
  · exact B1593619
  · exact B1593623
  · exact B1593627
  · exact B1593631
  · exact B1593635
  · exact B1593639
  · exact B1593643
  · exact B1593647
  · exact B1593651
  · exact B1593655
  · exact B1593659
  · exact B1593663
  · exact B1593667
  · exact B1593671
  · exact B1593675
  · exact B1593679
  · exact B1593683
  · exact B1593687
  · exact B1593691
  · exact B1593695
  · exact B1593699
  · exact B1593703
  · exact B1593707
  · exact B1593711
  · exact B1593715
  · exact B1593719
  · exact B1593723
  · exact B1593727
  · exact B1593731
  · exact B1593735
  · exact B1593739
  · exact B1593743
  · exact B1593747
  · exact B1593751
  · exact B1593755
  · exact B1593759
  · exact B1593763
  · exact B1593767
  · exact B1593771
  · exact B1593775
  · exact B1593779
  · exact B1593783
  · exact B1593787
  · exact B1593791
  · exact B1593795
  · exact B1593799
  · exact B1593803
  · exact B1593807
  · exact B1593811
  · exact B1593815
  · exact B1593819
  · exact B1593823
  · exact B1593827
  · exact B1593831
  · exact B1593835
  · exact B1593839
  · exact B1593843
  · exact B1593847
  · exact B1593851
  · exact B1593855
  · exact B1593859
  · exact B1593863
  · exact B1593867
  · exact B1593871
  · exact B1593875
  · exact B1593879
  · exact B1593883
  · exact B1593887
  · exact B1593891
  · exact B1593895
  · exact B1593899
  · exact B1593903
  · exact B1593907
  · exact B1593911
  · exact B1593915
  · exact B1593919
  · exact B1593923
  · exact B1593927
  · exact B1593931
  · exact B1593935
  · exact B1593939
  · exact B1593943
  · exact B1593947
  · exact B1593951
  · exact B1593955
  · exact B1593959
  · exact B1593963
  · exact B1593967
  · exact B1593971
  · exact B1593975
  · exact B1593979
  · exact B1593983
  · exact B1593987
  · exact B1593991
  · exact B1593995
  · exact B1593999
  · exact B1594003
  · exact B1594007
  · exact B1594011
  · exact B1594015
  · exact B1594019
  · exact B1594023
  · exact B1594027
  · exact B1594031
  · exact B1594035
  · exact B1594039
  · exact B1594043
  · exact B1594047
  · exact B1594051
  · exact B1594055
  · exact B1594059
  · exact B1594063
  · exact B1594067
  · exact B1594071
  · exact B1594075
  · exact B1594079
  · exact B1594083
  · exact B1594087
  · exact B1594091
  · exact B1594095
  · exact B1594099
  · exact B1594103
  · exact B1594107
  · exact B1594111
  · exact B1594115
  · exact B1594119
  · exact B1594123
  · exact B1594127
  · exact B1594131
  · exact B1594135
  · exact B1594139
  · exact B1594143
  · exact B1594147
  · exact B1594151
  · exact B1594155
  · exact B1594159
  · exact B1594163
  · exact B1594167
  · exact B1594171
  · exact B1594175
  · exact B1594179
  · exact B1594183
  · exact B1594187
  · exact B1594191
  · exact B1594195
  · exact B1594199
  · exact B1594203
  · exact B1594207
  · exact B1594211
  · exact B1594215
  · exact B1594219
  · exact B1594223
  · exact B1594227
  · exact B1594231
  · exact B1594235
  · exact B1594239
  · exact B1594243
  · exact B1594247
  · exact B1594251
  · exact B1594255
  · exact B1594259
  · exact B1594263
  · exact B1594267
  · exact B1594271
  · exact B1594275
  · exact B1594279
  · exact B1594283
  · exact B1594287
  · exact B1594291
  · exact B1594295
  · exact B1594299
  · exact B1594303
  · exact B1594307
  · exact B1594311
  · exact B1594315
  · exact B1594319
  · exact B1594323
  · exact B1594327
  · exact B1594331
  · exact B1594335
  · exact B1594339
  · exact B1594343
  · exact B1594347
  · exact B1594351
  · exact B1594355
  · exact B1594359
  · exact B1594363
  · exact B1594367
  · exact B1594371
  · exact B1594375
  · exact B1594379
  · exact B1594383
  · exact B1594387
  · exact B1594391
  · exact B1594395
  · exact B1594399
  · exact B1594403
  · exact B1594407
  · exact B1594411
  · exact B1594415
  · exact B1594419
  · exact B1594423
  · exact B1594427
  · exact B1594431
  · exact B1594435
  · exact B1594439
  · exact B1594443
  · exact B1594447
  · exact B1594451
  · exact B1594455
  · exact B1594459
  · exact B1594463
  · exact B1594467
  · exact B1594471
  · exact B1594475
  · exact B1594479
  · exact B1594483
  · exact B1594487
  · exact B1594491
  · exact B1594495
  · exact B1594499
  · exact B1594503
  · exact B1594507
  · exact B1594511
  · exact B1594515
  · exact B1594519
  · exact B1594523
  · exact B1594527
  · exact B1594531
  · exact B1594535
  · exact B1594539
  · exact B1594543
  · exact B1594547
  · exact B1594551
  · exact B1594555
  · exact B1594559
  · exact B1594563
  · exact B1594567
  · exact B1594571
  · exact B1594575
  · exact B1594579
  · exact B1594583
  · exact B1594587
  · exact B1594591
  · exact B1594595
  · exact B1594599
  · exact B1594603
  · exact B1594607
  · exact B1594611
  · exact B1594615
  · exact B1594619
  · exact B1594623
  · exact B1594627
  · exact B1594631
  · exact B1594635
  · exact B1594639
  · exact B1594643
  · exact B1594647
  · exact B1594651
  · exact B1594655
  · exact B1594659
  · exact B1594663
  · exact B1594667
  · exact B1594671
  · exact B1594675
  · exact B1594679
  · exact B1594683
  · exact B1594687
  · exact B1594691
  · exact B1594695
  · exact B1594699
  · exact B1594703
  · exact B1594707
  · exact B1594711
  · exact B1594715
  · exact B1594719
  · exact B1594723
  · exact B1594727
  · exact B1594731
  · exact B1594735
  · exact B1594739
  · exact B1594743
  · exact B1594747
  · exact B1594751
  · exact B1594755
  · exact B1594759
  · exact B1594763
  · exact B1594767
  · exact B1594771
  · exact B1594775
  · exact B1594779
  · exact B1594783
  · exact B1594787
  · exact B1594791
  · exact B1594795
  · exact B1594799
  · exact B1594803
  · exact B1594807
  · exact B1594811
  · exact B1594815
  · exact B1594819
  · exact B1594823
  · exact B1594827
  · exact B1594831
  · exact B1594835
  · exact B1594839
  · exact B1594843
  · exact B1594847
  · exact B1594851
  · exact B1594855
  · exact B1594859
  · exact B1594863
  · exact B1594867
  · exact B1594871
  · exact B1594875
  · exact B1594879
  · exact B1594883
  · exact B1594887
  · exact B1594891
  · exact B1594895
  · exact B1594899
  · exact B1594903
  · exact B1594907
  · exact B1594911
  · exact B1594915
  · exact B1594919
  · exact B1594923
  · exact B1594927
  · exact B1594931
  · exact B1594935
  · exact B1594939
  · exact B1594943
  · exact B1594947
  · exact B1594951
  · exact B1594955
  · exact B1594959
  · exact B1594963
  · exact B1594967
  · exact B1594971
  · exact B1594975
  · exact B1594979
  · exact B1594983
  · exact B1594987
  · exact B1594991
  · exact B1594995

theorem solution (m : ℕ) (hlo : 1592995 ≤ m) (hhi : m ≤ 1594995) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 398248 ≤ j := by omega
    have hj2 : j ≤ 398748 := by omega
    have hb : Blo 1592995 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
