-- Prove2me | solution 1 for syracuse_descends_range_1659529_1661529
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:19:01.912595+00:00
-- url     : https://prove2.me/submissions/a84b8832-471a-4ba8-a10c-8784ed2eef91

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


theorem B3735557 : Blo 1659529 3735557 := bbase (se 4 (by rfl) ⟨350208, by rfl⟩ : syracuseStep 3735557 = 700417) (by norm_num)
theorem B2490389 : Blo 1659529 2490389 := bbase (se 6 (by rfl) ⟨58368, by rfl⟩ : syracuseStep 2490389 = 116737) (by norm_num)
theorem B1867801 : Blo 1659529 1867801 := bbase (se 2 (by rfl) ⟨700425, by rfl⟩ : syracuseStep 1867801 = 1400851) (by norm_num)
theorem B2490413 : Blo 1659529 2490413 := bbase (se 3 (by rfl) ⟨466952, by rfl⟩ : syracuseStep 2490413 = 933905) (by norm_num)
theorem B8405045 : Blo 1659529 8405045 := bbase (se 5 (by rfl) ⟨393986, by rfl⟩ : syracuseStep 8405045 = 787973) (by norm_num)
theorem B3153973 : Blo 1659529 3153973 := bbase (se 5 (by rfl) ⟨147842, by rfl⟩ : syracuseStep 3153973 = 295685) (by norm_num)
theorem B1867837 : Blo 1659529 1867837 := bbase (se 3 (by rfl) ⟨350219, by rfl⟩ : syracuseStep 1867837 = 700439) (by norm_num)
theorem B2490437 : Blo 1659529 2490437 := bbase (se 4 (by rfl) ⟨233478, by rfl⟩ : syracuseStep 2490437 = 466957) (by norm_num)
theorem B3735629 : Blo 1659529 3735629 := bbase (se 3 (by rfl) ⟨700430, by rfl⟩ : syracuseStep 3735629 = 1400861) (by norm_num)
theorem B2801749 : Blo 1659529 2801749 := bbase (se 8 (by rfl) ⟨16416, by rfl⟩ : syracuseStep 2801749 = 32833) (by norm_num)
theorem B2490461 : Blo 1659529 2490461 := bbase (se 3 (by rfl) ⟨466961, by rfl⟩ : syracuseStep 2490461 = 933923) (by norm_num)
theorem B1867873 : Blo 1659529 1867873 := bbase (se 2 (by rfl) ⟨700452, by rfl⟩ : syracuseStep 1867873 = 1400905) (by norm_num)
theorem B2490485 : Blo 1659529 2490485 := bbase (se 5 (by rfl) ⟨116741, by rfl⟩ : syracuseStep 2490485 = 233483) (by norm_num)
theorem B1867909 : Blo 1659529 1867909 := bbase (se 4 (by rfl) ⟨175116, by rfl⟩ : syracuseStep 1867909 = 350233) (by norm_num)
theorem B2490509 : Blo 1659529 2490509 := bbase (se 3 (by rfl) ⟨466970, by rfl⟩ : syracuseStep 2490509 = 933941) (by norm_num)
theorem B3735701 : Blo 1659529 3735701 := bbase (se 6 (by rfl) ⟨87555, by rfl⟩ : syracuseStep 3735701 = 175111) (by norm_num)
theorem B2490533 : Blo 1659529 2490533 := bbase (se 4 (by rfl) ⟨233487, by rfl⟩ : syracuseStep 2490533 = 466975) (by norm_num)
theorem B1867945 : Blo 1659529 1867945 := bbase (se 2 (by rfl) ⟨700479, by rfl⟩ : syracuseStep 1867945 = 1400959) (by norm_num)
theorem B2801837 : Blo 1659529 2801837 := bbase (se 3 (by rfl) ⟨525344, by rfl⟩ : syracuseStep 2801837 = 1050689) (by norm_num)
theorem B2244781 : Blo 1659529 2244781 := bbase (se 3 (by rfl) ⟨420896, by rfl⟩ : syracuseStep 2244781 = 841793) (by norm_num)
theorem B2490557 : Blo 1659529 2490557 := bbase (se 3 (by rfl) ⟨466979, by rfl⟩ : syracuseStep 2490557 = 933959) (by norm_num)
theorem B5603525 : Blo 1659529 5603525 := bbase (se 4 (by rfl) ⟨525330, by rfl⟩ : syracuseStep 5603525 = 1050661) (by norm_num)
theorem B1867981 : Blo 1659529 1867981 := bbase (se 3 (by rfl) ⟨350246, by rfl⟩ : syracuseStep 1867981 = 700493) (by norm_num)
theorem B2490581 : Blo 1659529 2490581 := bbase (se 7 (by rfl) ⟨29186, by rfl⟩ : syracuseStep 2490581 = 58373) (by norm_num)
theorem B3154133 : Blo 1659529 3154133 := bbase (se 7 (by rfl) ⟨36962, by rfl⟩ : syracuseStep 3154133 = 73925) (by norm_num)
theorem B3735773 : Blo 1659529 3735773 := bbase (se 3 (by rfl) ⟨700457, by rfl⟩ : syracuseStep 3735773 = 1400915) (by norm_num)
theorem B2244829 : Blo 1659529 2244829 := bbase (se 3 (by rfl) ⟨420905, by rfl⟩ : syracuseStep 2244829 = 841811) (by norm_num)
theorem B4202725 : Blo 1659529 4202725 := bbase (se 4 (by rfl) ⟨394005, by rfl⟩ : syracuseStep 4202725 = 788011) (by norm_num)
theorem B2490605 : Blo 1659529 2490605 := bbase (se 3 (by rfl) ⟨466988, by rfl⟩ : syracuseStep 2490605 = 933977) (by norm_num)
theorem B1868017 : Blo 1659529 1868017 := bbase (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) (by norm_num)
theorem B3989749 : Blo 1659529 3989749 := bbase (se 5 (by rfl) ⟨187019, by rfl⟩ : syracuseStep 3989749 = 374039) (by norm_num)
theorem B2490629 : Blo 1659529 2490629 := bbase (se 4 (by rfl) ⟨233496, by rfl⟩ : syracuseStep 2490629 = 466993) (by norm_num)
theorem B1868053 : Blo 1659529 1868053 := bbase (se 6 (by rfl) ⟨43782, by rfl⟩ : syracuseStep 1868053 = 87565) (by norm_num)
theorem B2490653 : Blo 1659529 2490653 := bbase (se 3 (by rfl) ⟨466997, by rfl⟩ : syracuseStep 2490653 = 933995) (by norm_num)
theorem B3735845 : Blo 1659529 3735845 := bbase (se 4 (by rfl) ⟨350235, by rfl⟩ : syracuseStep 3735845 = 700471) (by norm_num)
theorem B2801965 : Blo 1659529 2801965 := bbase (se 3 (by rfl) ⟨525368, by rfl⟩ : syracuseStep 2801965 = 1050737) (by norm_num)
theorem B2490677 : Blo 1659529 2490677 := bbase (se 5 (by rfl) ⟨116750, by rfl⟩ : syracuseStep 2490677 = 233501) (by norm_num)
theorem B1868089 : Blo 1659529 1868089 := bbase (se 2 (by rfl) ⟨700533, by rfl⟩ : syracuseStep 1868089 = 1401067) (by norm_num)
theorem B2490701 : Blo 1659529 2490701 := bbase (se 3 (by rfl) ⟨467006, by rfl⟩ : syracuseStep 2490701 = 934013) (by norm_num)
theorem B3547469 : Blo 1659529 3547469 := bbase (se 3 (by rfl) ⟨665150, by rfl⟩ : syracuseStep 3547469 = 1330301) (by norm_num)
theorem B4202837 : Blo 1659529 4202837 := bbase (se 10 (by rfl) ⟨6156, by rfl⟩ : syracuseStep 4202837 = 12313) (by norm_num)
theorem B1868125 : Blo 1659529 1868125 := bbase (se 3 (by rfl) ⟨350273, by rfl⟩ : syracuseStep 1868125 = 700547) (by norm_num)
theorem B2490725 : Blo 1659529 2490725 := bbase (se 4 (by rfl) ⟨233505, by rfl⟩ : syracuseStep 2490725 = 467011) (by norm_num)
theorem B3154277 : Blo 1659529 3154277 := bbase (se 4 (by rfl) ⟨295713, by rfl⟩ : syracuseStep 3154277 = 591427) (by norm_num)
theorem B3735917 : Blo 1659529 3735917 := bbase (se 3 (by rfl) ⟨700484, by rfl⟩ : syracuseStep 3735917 = 1400969) (by norm_num)
theorem B10633589 : Blo 1659529 10633589 := bbase (se 5 (by rfl) ⟨498449, by rfl⟩ : syracuseStep 10633589 = 996899) (by norm_num)
theorem B2490749 : Blo 1659529 2490749 := bbase (se 3 (by rfl) ⟨467015, by rfl⟩ : syracuseStep 2490749 = 934031) (by norm_num)
theorem B1868161 : Blo 1659529 1868161 := bbase (se 2 (by rfl) ⟨700560, by rfl⟩ : syracuseStep 1868161 = 1401121) (by norm_num)
theorem B2802053 : Blo 1659529 2802053 := bbase (se 4 (by rfl) ⟨262692, by rfl⟩ : syracuseStep 2802053 = 525385) (by norm_num)
theorem B2490773 : Blo 1659529 2490773 := bbase (se 6 (by rfl) ⟨58377, by rfl⟩ : syracuseStep 2490773 = 116755) (by norm_num)
theorem B1868197 : Blo 1659529 1868197 := bbase (se 4 (by rfl) ⟨175143, by rfl⟩ : syracuseStep 1868197 = 350287) (by norm_num)
theorem B2490797 : Blo 1659529 2490797 := bbase (se 3 (by rfl) ⟨467024, by rfl⟩ : syracuseStep 2490797 = 934049) (by norm_num)
theorem B3735989 : Blo 1659529 3735989 := bbase (se 5 (by rfl) ⟨175124, by rfl⟩ : syracuseStep 3735989 = 350249) (by norm_num)
theorem B2490821 : Blo 1659529 2490821 := bbase (se 4 (by rfl) ⟨233514, by rfl⟩ : syracuseStep 2490821 = 467029) (by norm_num)
theorem B1868233 : Blo 1659529 1868233 := bbase (se 2 (by rfl) ⟨700587, by rfl⟩ : syracuseStep 1868233 = 1401175) (by norm_num)
theorem B2490845 : Blo 1659529 2490845 := bbase (se 3 (by rfl) ⟨467033, by rfl⟩ : syracuseStep 2490845 = 934067) (by norm_num)
theorem B1868269 : Blo 1659529 1868269 := bbase (se 3 (by rfl) ⟨350300, by rfl⟩ : syracuseStep 1868269 = 700601) (by norm_num)
theorem B2490869 : Blo 1659529 2490869 := bbase (se 5 (by rfl) ⟨116759, by rfl⟩ : syracuseStep 2490869 = 233519) (by norm_num)
theorem B3736061 : Blo 1659529 3736061 := bbase (se 3 (by rfl) ⟨700511, by rfl⟩ : syracuseStep 3736061 = 1401023) (by norm_num)
theorem B5677573 : Blo 1659529 5677573 := bbase (se 4 (by rfl) ⟨532272, by rfl⟩ : syracuseStep 5677573 = 1064545) (by norm_num)
theorem B3785221 : Blo 1659529 3785221 := bbase (se 4 (by rfl) ⟨354864, by rfl⟩ : syracuseStep 3785221 = 709729) (by norm_num)
theorem B2802181 : Blo 1659529 2802181 := bbase (se 4 (by rfl) ⟨262704, by rfl⟩ : syracuseStep 2802181 = 525409) (by norm_num)
theorem B2490893 : Blo 1659529 2490893 := bbase (se 3 (by rfl) ⟨467042, by rfl⟩ : syracuseStep 2490893 = 934085) (by norm_num)
theorem B1868305 : Blo 1659529 1868305 := bbase (se 2 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 1868305 = 1401229) (by norm_num)
theorem B4203029 : Blo 1659529 4203029 := bbase (se 6 (by rfl) ⟨98508, by rfl⟩ : syracuseStep 4203029 = 197017) (by norm_num)
theorem B2490917 : Blo 1659529 2490917 := bbase (se 4 (by rfl) ⟨233523, by rfl⟩ : syracuseStep 2490917 = 467047) (by norm_num)
theorem B1868341 : Blo 1659529 1868341 := bbase (se 5 (by rfl) ⟨87578, by rfl⟩ : syracuseStep 1868341 = 175157) (by norm_num)
theorem B2490941 : Blo 1659529 2490941 := bbase (se 3 (by rfl) ⟨467051, by rfl⟩ : syracuseStep 2490941 = 934103) (by norm_num)
theorem B3736133 : Blo 1659529 3736133 := bbase (se 4 (by rfl) ⟨350262, by rfl⟩ : syracuseStep 3736133 = 700525) (by norm_num)
theorem B2490965 : Blo 1659529 2490965 := bbase (se 8 (by rfl) ⟨14595, by rfl⟩ : syracuseStep 2490965 = 29191) (by norm_num)
theorem B1868377 : Blo 1659529 1868377 := bbase (se 2 (by rfl) ⟨700641, by rfl⟩ : syracuseStep 1868377 = 1401283) (by norm_num)
theorem B2802269 : Blo 1659529 2802269 := bbase (se 3 (by rfl) ⟨525425, by rfl⟩ : syracuseStep 2802269 = 1050851) (by norm_num)
theorem B2490989 : Blo 1659529 2490989 := bbase (se 3 (by rfl) ⟨467060, by rfl⟩ : syracuseStep 2490989 = 934121) (by norm_num)
theorem B5603957 : Blo 1659529 5603957 := bbase (se 5 (by rfl) ⟨262685, by rfl⟩ : syracuseStep 5603957 = 525371) (by norm_num)
theorem B1868413 : Blo 1659529 1868413 := bbase (se 3 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 1868413 = 700655) (by norm_num)
theorem B4727429 : Blo 1659529 4727429 := bbase (se 4 (by rfl) ⟨443196, by rfl⟩ : syracuseStep 4727429 = 886393) (by norm_num)
theorem B2491013 : Blo 1659529 2491013 := bbase (se 4 (by rfl) ⟨233532, by rfl⟩ : syracuseStep 2491013 = 467065) (by norm_num)
theorem B3736205 : Blo 1659529 3736205 := bbase (se 3 (by rfl) ⟨700538, by rfl⟩ : syracuseStep 3736205 = 1401077) (by norm_num)
theorem B6062741 : Blo 1659529 6062741 := bbase (se 6 (by rfl) ⟨142095, by rfl⟩ : syracuseStep 6062741 = 284191) (by norm_num)
theorem B2491037 : Blo 1659529 2491037 := bbase (se 3 (by rfl) ⟨467069, by rfl⟩ : syracuseStep 2491037 = 934139) (by norm_num)
theorem B1868449 : Blo 1659529 1868449 := bbase (se 2 (by rfl) ⟨700668, by rfl⟩ : syracuseStep 1868449 = 1401337) (by norm_num)
theorem B5677733 : Blo 1659529 5677733 := bbase (se 4 (by rfl) ⟨532287, by rfl⟩ : syracuseStep 5677733 = 1064575) (by norm_num)
theorem B2491061 : Blo 1659529 2491061 := bbase (se 5 (by rfl) ⟨116768, by rfl⟩ : syracuseStep 2491061 = 233537) (by norm_num)
theorem B1868485 : Blo 1659529 1868485 := bbase (se 4 (by rfl) ⟨175170, by rfl⟩ : syracuseStep 1868485 = 350341) (by norm_num)
theorem B2491085 : Blo 1659529 2491085 := bbase (se 3 (by rfl) ⟨467078, by rfl⟩ : syracuseStep 2491085 = 934157) (by norm_num)
theorem B3736277 : Blo 1659529 3736277 := bbase (se 7 (by rfl) ⟨43784, by rfl⟩ : syracuseStep 3736277 = 87569) (by norm_num)
theorem B2802397 : Blo 1659529 2802397 := bbase (se 3 (by rfl) ⟨525449, by rfl⟩ : syracuseStep 2802397 = 1050899) (by norm_num)
theorem B2491109 : Blo 1659529 2491109 := bbase (se 4 (by rfl) ⟨233541, by rfl⟩ : syracuseStep 2491109 = 467083) (by norm_num)
theorem B1868521 : Blo 1659529 1868521 := bbase (se 2 (by rfl) ⟨700695, by rfl⟩ : syracuseStep 1868521 = 1401391) (by norm_num)
theorem B6390517 : Blo 1659529 6390517 := bbase (se 5 (by rfl) ⟨299555, by rfl⟩ : syracuseStep 6390517 = 599111) (by norm_num)
theorem B2523901 : Blo 1659529 2523901 := bbase (se 3 (by rfl) ⟨473231, by rfl⟩ : syracuseStep 2523901 = 946463) (by norm_num)
theorem B2491133 : Blo 1659529 2491133 := bbase (se 3 (by rfl) ⟨467087, by rfl⟩ : syracuseStep 2491133 = 934175) (by norm_num)
theorem B1868557 : Blo 1659529 1868557 := bbase (se 3 (by rfl) ⟨350354, by rfl⟩ : syracuseStep 1868557 = 700709) (by norm_num)
theorem B2491157 : Blo 1659529 2491157 := bbase (se 6 (by rfl) ⟨58386, by rfl⟩ : syracuseStep 2491157 = 116773) (by norm_num)
theorem B3736349 : Blo 1659529 3736349 := bbase (se 3 (by rfl) ⟨700565, by rfl⟩ : syracuseStep 3736349 = 1401131) (by norm_num)
theorem B2491181 : Blo 1659529 2491181 := bbase (se 3 (by rfl) ⟨467096, by rfl⟩ : syracuseStep 2491181 = 934193) (by norm_num)
theorem B1868593 : Blo 1659529 1868593 := bbase (se 2 (by rfl) ⟨700722, by rfl⟩ : syracuseStep 1868593 = 1401445) (by norm_num)
theorem B2802485 : Blo 1659529 2802485 := bbase (se 5 (by rfl) ⟨131366, by rfl⟩ : syracuseStep 2802485 = 262733) (by norm_num)
theorem B9462581 : Blo 1659529 9462581 := bbase (se 5 (by rfl) ⟨443558, by rfl⟩ : syracuseStep 9462581 = 887117) (by norm_num)
theorem B2491205 : Blo 1659529 2491205 := bbase (se 4 (by rfl) ⟨233550, by rfl⟩ : syracuseStep 2491205 = 467101) (by norm_num)
theorem B1868629 : Blo 1659529 1868629 := bbase (se 9 (by rfl) ⟨5474, by rfl⟩ : syracuseStep 1868629 = 10949) (by norm_num)
theorem B2491229 : Blo 1659529 2491229 := bbase (se 3 (by rfl) ⟨467105, by rfl⟩ : syracuseStep 2491229 = 934211) (by norm_num)
theorem B3736421 : Blo 1659529 3736421 := bbase (se 4 (by rfl) ⟨350289, by rfl⟩ : syracuseStep 3736421 = 700579) (by norm_num)
theorem B4203373 : Blo 1659529 4203373 := bbase (se 3 (by rfl) ⟨788132, by rfl⟩ : syracuseStep 4203373 = 1576265) (by norm_num)
theorem B2491253 : Blo 1659529 2491253 := bbase (se 5 (by rfl) ⟨116777, by rfl⟩ : syracuseStep 2491253 = 233555) (by norm_num)
theorem B7578485 : Blo 1659529 7578485 := bbase (se 5 (by rfl) ⟨355241, by rfl⟩ : syracuseStep 7578485 = 710483) (by norm_num)
theorem B1868665 : Blo 1659529 1868665 := bbase (se 2 (by rfl) ⟨700749, by rfl⟩ : syracuseStep 1868665 = 1401499) (by norm_num)
theorem B2491277 : Blo 1659529 2491277 := bbase (se 3 (by rfl) ⟨467114, by rfl⟩ : syracuseStep 2491277 = 934229) (by norm_num)
theorem B3990421 : Blo 1659529 3990421 := bbase (se 6 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 3990421 = 187051) (by norm_num)
theorem B1868701 : Blo 1659529 1868701 := bbase (se 3 (by rfl) ⟨350381, by rfl⟩ : syracuseStep 1868701 = 700763) (by norm_num)
theorem B2491301 : Blo 1659529 2491301 := bbase (se 4 (by rfl) ⟨233559, by rfl⟩ : syracuseStep 2491301 = 467119) (by norm_num)
theorem B3736493 : Blo 1659529 3736493 := bbase (se 3 (by rfl) ⟨700592, by rfl⟩ : syracuseStep 3736493 = 1401185) (by norm_num)
theorem B2802613 : Blo 1659529 2802613 := bbase (se 5 (by rfl) ⟨131372, by rfl⟩ : syracuseStep 2802613 = 262745) (by norm_num)
theorem B2491325 : Blo 1659529 2491325 := bbase (se 3 (by rfl) ⟨467123, by rfl⟩ : syracuseStep 2491325 = 934247) (by norm_num)
theorem B1868737 : Blo 1659529 1868737 := bbase (se 2 (by rfl) ⟨700776, by rfl⟩ : syracuseStep 1868737 = 1401553) (by norm_num)
theorem B5317589 : Blo 1659529 5317589 := bbase (se 7 (by rfl) ⟨62315, by rfl⟩ : syracuseStep 5317589 = 124631) (by norm_num)
theorem B2491349 : Blo 1659529 2491349 := bbase (se 7 (by rfl) ⟨29195, by rfl⟩ : syracuseStep 2491349 = 58391) (by norm_num)
theorem B4203485 : Blo 1659529 4203485 := bbase (se 3 (by rfl) ⟨788153, by rfl⟩ : syracuseStep 4203485 = 1576307) (by norm_num)
theorem B1868773 : Blo 1659529 1868773 := bbase (se 4 (by rfl) ⟨175197, by rfl⟩ : syracuseStep 1868773 = 350395) (by norm_num)
theorem B2491373 : Blo 1659529 2491373 := bbase (se 3 (by rfl) ⟨467132, by rfl⟩ : syracuseStep 2491373 = 934265) (by norm_num)
theorem B12633077 : Blo 1659529 12633077 := bbase (se 5 (by rfl) ⟨592175, by rfl⟩ : syracuseStep 12633077 = 1184351) (by norm_num)
theorem B3736565 : Blo 1659529 3736565 := bbase (se 5 (by rfl) ⟨175151, by rfl⟩ : syracuseStep 3736565 = 350303) (by norm_num)
theorem B4260869 : Blo 1659529 4260869 := bbase (se 4 (by rfl) ⟨399456, by rfl⟩ : syracuseStep 4260869 = 798913) (by norm_num)
theorem B2491397 : Blo 1659529 2491397 := bbase (se 4 (by rfl) ⟨233568, by rfl⟩ : syracuseStep 2491397 = 467137) (by norm_num)
theorem B1868809 : Blo 1659529 1868809 := bbase (se 2 (by rfl) ⟨700803, by rfl⟩ : syracuseStep 1868809 = 1401607) (by norm_num)
theorem B2802701 : Blo 1659529 2802701 := bbase (se 3 (by rfl) ⟨525506, by rfl⟩ : syracuseStep 2802701 = 1051013) (by norm_num)
theorem B2491421 : Blo 1659529 2491421 := bbase (se 3 (by rfl) ⟨467141, by rfl⟩ : syracuseStep 2491421 = 934283) (by norm_num)
theorem B5604389 : Blo 1659529 5604389 := bbase (se 4 (by rfl) ⟨525411, by rfl⟩ : syracuseStep 5604389 = 1050823) (by norm_num)
theorem B1868845 : Blo 1659529 1868845 := bbase (se 3 (by rfl) ⟨350408, by rfl⟩ : syracuseStep 1868845 = 700817) (by norm_num)
theorem B2491445 : Blo 1659529 2491445 := bbase (se 5 (by rfl) ⟨116786, by rfl⟩ : syracuseStep 2491445 = 233573) (by norm_num)
theorem B3736637 : Blo 1659529 3736637 := bbase (se 3 (by rfl) ⟨700619, by rfl⟩ : syracuseStep 3736637 = 1401239) (by norm_num)
theorem B2491469 : Blo 1659529 2491469 := bbase (se 3 (by rfl) ⟨467150, by rfl⟩ : syracuseStep 2491469 = 934301) (by norm_num)
theorem B1868881 : Blo 1659529 1868881 := bbase (se 2 (by rfl) ⟨700830, by rfl⟩ : syracuseStep 1868881 = 1401661) (by norm_num)
theorem B2491493 : Blo 1659529 2491493 := bbase (se 4 (by rfl) ⟨233577, by rfl⟩ : syracuseStep 2491493 = 467155) (by norm_num)
theorem B1868917 : Blo 1659529 1868917 := bbase (se 5 (by rfl) ⟨87605, by rfl⟩ : syracuseStep 1868917 = 175211) (by norm_num)
theorem B3990653 : Blo 1659529 3990653 := bbase (se 3 (by rfl) ⟨748247, by rfl⟩ : syracuseStep 3990653 = 1496495) (by norm_num)
theorem B2491517 : Blo 1659529 2491517 := bbase (se 3 (by rfl) ⟨467159, by rfl⟩ : syracuseStep 2491517 = 934319) (by norm_num)
theorem B3736709 : Blo 1659529 3736709 := bbase (se 4 (by rfl) ⟨350316, by rfl⟩ : syracuseStep 3736709 = 700633) (by norm_num)
theorem B5121157 : Blo 1659529 5121157 := bbase (se 4 (by rfl) ⟨480108, by rfl⟩ : syracuseStep 5121157 = 960217) (by norm_num)
theorem B2802829 : Blo 1659529 2802829 := bbase (se 3 (by rfl) ⟨525530, by rfl⟩ : syracuseStep 2802829 = 1051061) (by norm_num)
theorem B2491541 : Blo 1659529 2491541 := bbase (se 6 (by rfl) ⟨58395, by rfl⟩ : syracuseStep 2491541 = 116791) (by norm_num)
theorem B1868953 : Blo 1659529 1868953 := bbase (se 2 (by rfl) ⟨700857, by rfl⟩ : syracuseStep 1868953 = 1401715) (by norm_num)
theorem B4203677 : Blo 1659529 4203677 := bbase (se 3 (by rfl) ⟨788189, by rfl⟩ : syracuseStep 4203677 = 1576379) (by norm_num)
theorem B2491565 : Blo 1659529 2491565 := bbase (se 3 (by rfl) ⟨467168, by rfl⟩ : syracuseStep 2491565 = 934337) (by norm_num)
theorem B1868989 : Blo 1659529 1868989 := bbase (se 3 (by rfl) ⟨350435, by rfl⟩ : syracuseStep 1868989 = 700871) (by norm_num)
theorem B2491589 : Blo 1659529 2491589 := bbase (se 4 (by rfl) ⟨233586, by rfl⟩ : syracuseStep 2491589 = 467173) (by norm_num)
theorem B3548357 : Blo 1659529 3548357 := bbase (se 4 (by rfl) ⟨332658, by rfl⟩ : syracuseStep 3548357 = 665317) (by norm_num)
theorem B3736781 : Blo 1659529 3736781 := bbase (se 3 (by rfl) ⟨700646, by rfl⟩ : syracuseStep 3736781 = 1401293) (by norm_num)
theorem B2491613 : Blo 1659529 2491613 := bbase (se 3 (by rfl) ⟨467177, by rfl⟩ : syracuseStep 2491613 = 934355) (by norm_num)
theorem B1869025 : Blo 1659529 1869025 := bbase (se 2 (by rfl) ⟨700884, by rfl⟩ : syracuseStep 1869025 = 1401769) (by norm_num)
theorem B2802917 : Blo 1659529 2802917 := bbase (se 4 (by rfl) ⟨262773, by rfl⟩ : syracuseStep 2802917 = 525547) (by norm_num)
theorem B2491637 : Blo 1659529 2491637 := bbase (se 5 (by rfl) ⟨116795, by rfl⟩ : syracuseStep 2491637 = 233591) (by norm_num)
theorem B1869061 : Blo 1659529 1869061 := bbase (se 4 (by rfl) ⟨175224, by rfl⟩ : syracuseStep 1869061 = 350449) (by norm_num)
theorem B3990797 : Blo 1659529 3990797 := bbase (se 3 (by rfl) ⟨748274, by rfl⟩ : syracuseStep 3990797 = 1496549) (by norm_num)
theorem B2491661 : Blo 1659529 2491661 := bbase (se 3 (by rfl) ⟨467186, by rfl⟩ : syracuseStep 2491661 = 934373) (by norm_num)
theorem B3736853 : Blo 1659529 3736853 := bbase (se 6 (by rfl) ⟨87582, by rfl⟩ : syracuseStep 3736853 = 175165) (by norm_num)
theorem B2991389 : Blo 1659529 2991389 := bbase (se 3 (by rfl) ⟨560885, by rfl⟩ : syracuseStep 2991389 = 1121771) (by norm_num)
theorem B3196189 : Blo 1659529 3196189 := bbase (se 3 (by rfl) ⟨599285, by rfl⟩ : syracuseStep 3196189 = 1198571) (by norm_num)
theorem B2491685 : Blo 1659529 2491685 := bbase (se 4 (by rfl) ⟨233595, by rfl⟩ : syracuseStep 2491685 = 467191) (by norm_num)
theorem B1869097 : Blo 1659529 1869097 := bbase (se 2 (by rfl) ⟨700911, by rfl⟩ : syracuseStep 1869097 = 1401823) (by norm_num)
theorem B3990845 : Blo 1659529 3990845 := bbase (se 3 (by rfl) ⟨748283, by rfl⟩ : syracuseStep 3990845 = 1496567) (by norm_num)
theorem B2491709 : Blo 1659529 2491709 := bbase (se 3 (by rfl) ⟨467195, by rfl⟩ : syracuseStep 2491709 = 934391) (by norm_num)
theorem B8406341 : Blo 1659529 8406341 := bbase (se 4 (by rfl) ⟨788094, by rfl⟩ : syracuseStep 8406341 = 1576189) (by norm_num)
theorem B1869133 : Blo 1659529 1869133 := bbase (se 3 (by rfl) ⟨350462, by rfl⟩ : syracuseStep 1869133 = 700925) (by norm_num)
theorem B2491733 : Blo 1659529 2491733 := bbase (se 12 (by rfl) ⟨912, by rfl⟩ : syracuseStep 2491733 = 1825) (by norm_num)
theorem B12617045 : Blo 1659529 12617045 := bbase (se 12 (by rfl) ⟨4620, by rfl⟩ : syracuseStep 12617045 = 9241) (by norm_num)
theorem B3736925 : Blo 1659529 3736925 := bbase (se 3 (by rfl) ⟨700673, by rfl⟩ : syracuseStep 3736925 = 1401347) (by norm_num)
theorem B2803045 : Blo 1659529 2803045 := bbase (se 4 (by rfl) ⟨262785, by rfl⟩ : syracuseStep 2803045 = 525571) (by norm_num)
theorem B2491757 : Blo 1659529 2491757 := bbase (se 3 (by rfl) ⟨467204, by rfl⟩ : syracuseStep 2491757 = 934409) (by norm_num)
theorem B1869169 : Blo 1659529 1869169 := bbase (se 2 (by rfl) ⟨700938, by rfl⟩ : syracuseStep 1869169 = 1401877) (by norm_num)
theorem B2491781 : Blo 1659529 2491781 := bbase (se 4 (by rfl) ⟨233604, by rfl⟩ : syracuseStep 2491781 = 467209) (by norm_num)
theorem B1869205 : Blo 1659529 1869205 := bbase (se 6 (by rfl) ⟨43809, by rfl⟩ : syracuseStep 1869205 = 87619) (by norm_num)
theorem B2491805 : Blo 1659529 2491805 := bbase (se 3 (by rfl) ⟨467213, by rfl⟩ : syracuseStep 2491805 = 934427) (by norm_num)
theorem B3736997 : Blo 1659529 3736997 := bbase (se 4 (by rfl) ⟨350343, by rfl⟩ : syracuseStep 3736997 = 700687) (by norm_num)
theorem B2491829 : Blo 1659529 2491829 := bbase (se 5 (by rfl) ⟨116804, by rfl⟩ : syracuseStep 2491829 = 233609) (by norm_num)
theorem B2803133 : Blo 1659529 2803133 := bbase (se 3 (by rfl) ⟨525587, by rfl⟩ : syracuseStep 2803133 = 1051175) (by norm_num)
theorem B2491853 : Blo 1659529 2491853 := bbase (se 3 (by rfl) ⟨467222, by rfl⟩ : syracuseStep 2491853 = 934445) (by norm_num)
theorem B5604821 : Blo 1659529 5604821 := bbase (se 7 (by rfl) ⟨65681, by rfl⟩ : syracuseStep 5604821 = 131363) (by norm_num)
theorem B2491877 : Blo 1659529 2491877 := bbase (se 4 (by rfl) ⟨233613, by rfl⟩ : syracuseStep 2491877 = 467227) (by norm_num)
theorem B3737069 : Blo 1659529 3737069 := bbase (se 3 (by rfl) ⟨700700, by rfl⟩ : syracuseStep 3737069 = 1401401) (by norm_num)
theorem B4793845 : Blo 1659529 4793845 := bbase (se 5 (by rfl) ⟨224711, by rfl⟩ : syracuseStep 4793845 = 449423) (by norm_num)
theorem B4204021 : Blo 1659529 4204021 := bbase (se 5 (by rfl) ⟨197063, by rfl⟩ : syracuseStep 4204021 = 394127) (by norm_num)
theorem B2491901 : Blo 1659529 2491901 := bbase (se 3 (by rfl) ⟨467231, by rfl⟩ : syracuseStep 2491901 = 934463) (by norm_num)
theorem B2491925 : Blo 1659529 2491925 := bbase (se 6 (by rfl) ⟨58404, by rfl⟩ : syracuseStep 2491925 = 116809) (by norm_num)
theorem B4261421 : Blo 1659529 4261421 := bbase (se 3 (by rfl) ⟨799016, by rfl⟩ : syracuseStep 4261421 = 1598033) (by norm_num)
theorem B2491949 : Blo 1659529 2491949 := bbase (se 3 (by rfl) ⟨467240, by rfl⟩ : syracuseStep 2491949 = 934481) (by norm_num)
theorem B3737141 : Blo 1659529 3737141 := bbase (se 5 (by rfl) ⟨175178, by rfl⟩ : syracuseStep 3737141 = 350357) (by norm_num)
theorem B2803261 : Blo 1659529 2803261 := bbase (se 3 (by rfl) ⟨525611, by rfl⟩ : syracuseStep 2803261 = 1051223) (by norm_num)
theorem B1705541 : Blo 1659529 1705541 := bbase (se 4 (by rfl) ⟨159894, by rfl⟩ : syracuseStep 1705541 = 319789) (by norm_num)
theorem B2491973 : Blo 1659529 2491973 := bbase (se 4 (by rfl) ⟨233622, by rfl⟩ : syracuseStep 2491973 = 467245) (by norm_num)
theorem B3991133 : Blo 1659529 3991133 := bbase (se 3 (by rfl) ⟨748337, by rfl⟩ : syracuseStep 3991133 = 1496675) (by norm_num)
theorem B2491997 : Blo 1659529 2491997 := bbase (se 3 (by rfl) ⟨467249, by rfl⟩ : syracuseStep 2491997 = 934499) (by norm_num)
theorem B4204133 : Blo 1659529 4204133 := bbase (se 4 (by rfl) ⟨394137, by rfl⟩ : syracuseStep 4204133 = 788275) (by norm_num)
theorem B2492021 : Blo 1659529 2492021 := bbase (se 5 (by rfl) ⟨116813, by rfl⟩ : syracuseStep 2492021 = 233627) (by norm_num)
theorem B3737213 : Blo 1659529 3737213 := bbase (se 3 (by rfl) ⟨700727, by rfl⟩ : syracuseStep 3737213 = 1401455) (by norm_num)
theorem B2492045 : Blo 1659529 2492045 := bbase (se 3 (by rfl) ⟨467258, by rfl⟩ : syracuseStep 2492045 = 934517) (by norm_num)
theorem B3786389 : Blo 1659529 3786389 := bbase (se 6 (by rfl) ⟨88743, by rfl⟩ : syracuseStep 3786389 = 177487) (by norm_num)
theorem B2803349 : Blo 1659529 2803349 := bbase (se 6 (by rfl) ⟨65703, by rfl⟩ : syracuseStep 2803349 = 131407) (by norm_num)
theorem B2492069 : Blo 1659529 2492069 := bbase (se 4 (by rfl) ⟨233631, by rfl⟩ : syracuseStep 2492069 = 467263) (by norm_num)
theorem B2492093 : Blo 1659529 2492093 := bbase (se 3 (by rfl) ⟨467267, by rfl⟩ : syracuseStep 2492093 = 934535) (by norm_num)
theorem B3737285 : Blo 1659529 3737285 := bbase (se 4 (by rfl) ⟨350370, by rfl⟩ : syracuseStep 3737285 = 700741) (by norm_num)
theorem B2492117 : Blo 1659529 2492117 := bbase (se 7 (by rfl) ⟨29204, by rfl⟩ : syracuseStep 2492117 = 58409) (by norm_num)
theorem B2492141 : Blo 1659529 2492141 := bbase (se 3 (by rfl) ⟨467276, by rfl⟩ : syracuseStep 2492141 = 934553) (by norm_num)
theorem B5981941 : Blo 1659529 5981941 := bbase (se 5 (by rfl) ⟨280403, by rfl⟩ : syracuseStep 5981941 = 560807) (by norm_num)
theorem B12609269 : Blo 1659529 12609269 := bbase (se 5 (by rfl) ⟨591059, by rfl⟩ : syracuseStep 12609269 = 1182119) (by norm_num)
theorem B2492165 : Blo 1659529 2492165 := bbase (se 4 (by rfl) ⟨233640, by rfl⟩ : syracuseStep 2492165 = 467281) (by norm_num)
theorem B3737357 : Blo 1659529 3737357 := bbase (se 3 (by rfl) ⟨700754, by rfl⟩ : syracuseStep 3737357 = 1401509) (by norm_num)
theorem B2803477 : Blo 1659529 2803477 := bbase (se 6 (by rfl) ⟨65706, by rfl⟩ : syracuseStep 2803477 = 131413) (by norm_num)
theorem B2492189 : Blo 1659529 2492189 := bbase (se 3 (by rfl) ⟨467285, by rfl⟩ : syracuseStep 2492189 = 934571) (by norm_num)
theorem B4728613 : Blo 1659529 4728613 := bbase (se 4 (by rfl) ⟨443307, by rfl⟩ : syracuseStep 4728613 = 886615) (by norm_num)
theorem B4204325 : Blo 1659529 4204325 := bbase (se 4 (by rfl) ⟨394155, by rfl⟩ : syracuseStep 4204325 = 788311) (by norm_num)
theorem B6735653 : Blo 1659529 6735653 := bbase (se 4 (by rfl) ⟨631467, by rfl⟩ : syracuseStep 6735653 = 1262935) (by norm_num)
theorem B2492213 : Blo 1659529 2492213 := bbase (se 5 (by rfl) ⟨116822, by rfl⟩ : syracuseStep 2492213 = 233645) (by norm_num)
theorem B2492237 : Blo 1659529 2492237 := bbase (se 3 (by rfl) ⟨467294, by rfl⟩ : syracuseStep 2492237 = 934589) (by norm_num)
theorem B3737429 : Blo 1659529 3737429 := bbase (se 9 (by rfl) ⟨10949, by rfl⟩ : syracuseStep 3737429 = 21899) (by norm_num)
theorem B2492261 : Blo 1659529 2492261 := bbase (se 4 (by rfl) ⟨233649, by rfl⟩ : syracuseStep 2492261 = 467299) (by norm_num)
theorem B2803565 : Blo 1659529 2803565 := bbase (se 3 (by rfl) ⟨525668, by rfl⟩ : syracuseStep 2803565 = 1051337) (by norm_num)
theorem B2492285 : Blo 1659529 2492285 := bbase (se 3 (by rfl) ⟨467303, by rfl⟩ : syracuseStep 2492285 = 934607) (by norm_num)
theorem B5605253 : Blo 1659529 5605253 := bbase (se 4 (by rfl) ⟨525492, by rfl⟩ : syracuseStep 5605253 = 1050985) (by norm_num)
theorem B3737501 : Blo 1659529 3737501 := bbase (se 3 (by rfl) ⟨700781, by rfl⟩ : syracuseStep 3737501 = 1401563) (by norm_num)
theorem B4728773 : Blo 1659529 4728773 := bbase (se 4 (by rfl) ⟨443322, by rfl⟩ : syracuseStep 4728773 = 886645) (by norm_num)
theorem B3737573 : Blo 1659529 3737573 := bbase (se 4 (by rfl) ⟨350397, by rfl⟩ : syracuseStep 3737573 = 700795) (by norm_num)
theorem B2803693 : Blo 1659529 2803693 := bbase (se 3 (by rfl) ⟨525692, by rfl⟩ : syracuseStep 2803693 = 1051385) (by norm_num)
theorem B3737645 : Blo 1659529 3737645 := bbase (se 3 (by rfl) ⟨700808, by rfl⟩ : syracuseStep 3737645 = 1401617) (by norm_num)
theorem B2803781 : Blo 1659529 2803781 := bbase (se 4 (by rfl) ⟨262854, by rfl⟩ : syracuseStep 2803781 = 525709) (by norm_num)
theorem B7096405 : Blo 1659529 7096405 := bbase (se 8 (by rfl) ⟨41580, by rfl⟩ : syracuseStep 7096405 = 83161) (by norm_num)
theorem B3737717 : Blo 1659529 3737717 := bbase (se 5 (by rfl) ⟨175205, by rfl⟩ : syracuseStep 3737717 = 350411) (by norm_num)
theorem B4204669 : Blo 1659529 4204669 := bbase (se 3 (by rfl) ⟨788375, by rfl⟩ : syracuseStep 4204669 = 1576751) (by norm_num)
theorem B4614293 : Blo 1659529 4614293 := bbase (se 6 (by rfl) ⟨108147, by rfl⟩ : syracuseStep 4614293 = 216295) (by norm_num)
theorem B4729013 : Blo 1659529 4729013 := bbase (se 5 (by rfl) ⟨221672, by rfl⟩ : syracuseStep 4729013 = 443345) (by norm_num)
theorem B3737789 : Blo 1659529 3737789 := bbase (se 3 (by rfl) ⟨700835, by rfl⟩ : syracuseStep 3737789 = 1401671) (by norm_num)
theorem B4204781 : Blo 1659529 4204781 := bbase (se 3 (by rfl) ⟨788396, by rfl⟩ : syracuseStep 4204781 = 1576793) (by norm_num)
theorem B3737861 : Blo 1659529 3737861 := bbase (se 4 (by rfl) ⟨350424, by rfl⟩ : syracuseStep 3737861 = 700849) (by norm_num)
theorem B5605685 : Blo 1659529 5605685 := bbase (se 5 (by rfl) ⟨262766, by rfl⟩ : syracuseStep 5605685 = 525533) (by norm_num)
theorem B3737933 : Blo 1659529 3737933 := bbase (se 3 (by rfl) ⟨700862, by rfl⟩ : syracuseStep 3737933 = 1401725) (by norm_num)
theorem B20195669 : Blo 1659529 20195669 := bbase (se 10 (by rfl) ⟨29583, by rfl⟩ : syracuseStep 20195669 = 59167) (by norm_num)
theorem B6302069 : Blo 1659529 6302069 := bbase (se 5 (by rfl) ⟨295409, by rfl⟩ : syracuseStep 6302069 = 590819) (by norm_num)
theorem B4729205 : Blo 1659529 4729205 := bbase (se 5 (by rfl) ⟨221681, by rfl⟩ : syracuseStep 4729205 = 443363) (by norm_num)
theorem B2279821 : Blo 1659529 2279821 := bbase (se 3 (by rfl) ⟨427466, by rfl⟩ : syracuseStep 2279821 = 854933) (by norm_num)
theorem B12954005 : Blo 1659529 12954005 := bbase (se 6 (by rfl) ⟨303609, by rfl⟩ : syracuseStep 12954005 = 607219) (by norm_num)
theorem B3738005 : Blo 1659529 3738005 := bbase (se 6 (by rfl) ⟨87609, by rfl⟩ : syracuseStep 3738005 = 175219) (by norm_num)
theorem B4204973 : Blo 1659529 4204973 := bbase (se 3 (by rfl) ⟨788432, by rfl⟩ : syracuseStep 4204973 = 1576865) (by norm_num)
theorem B1796549 : Blo 1659529 1796549 := bbase (se 4 (by rfl) ⟨168426, by rfl⟩ : syracuseStep 1796549 = 336853) (by norm_num)
theorem B3738077 : Blo 1659529 3738077 := bbase (se 3 (by rfl) ⟨700889, by rfl⟩ : syracuseStep 3738077 = 1401779) (by norm_num)
theorem B5048821 : Blo 1659529 5048821 := bbase (se 5 (by rfl) ⟨236663, by rfl⟩ : syracuseStep 5048821 = 473327) (by norm_num)
theorem B3738149 : Blo 1659529 3738149 := bbase (se 4 (by rfl) ⟨350451, by rfl⟩ : syracuseStep 3738149 = 700903) (by norm_num)
theorem B8407637 : Blo 1659529 8407637 := bbase (se 8 (by rfl) ⟨49263, by rfl⟩ : syracuseStep 8407637 = 98527) (by norm_num)
theorem B3738221 : Blo 1659529 3738221 := bbase (se 3 (by rfl) ⟨700916, by rfl⟩ : syracuseStep 3738221 = 1401833) (by norm_num)
theorem B4795013 : Blo 1659529 4795013 := bbase (se 4 (by rfl) ⟨449532, by rfl⟩ : syracuseStep 4795013 = 899065) (by norm_num)
theorem B6302357 : Blo 1659529 6302357 := bbase (se 6 (by rfl) ⟨147711, by rfl⟩ : syracuseStep 6302357 = 295423) (by norm_num)
theorem B3738293 : Blo 1659529 3738293 := bbase (se 5 (by rfl) ⟨175232, by rfl⟩ : syracuseStep 3738293 = 350465) (by norm_num)
theorem B5606117 : Blo 1659529 5606117 := bbase (se 4 (by rfl) ⟨525573, by rfl⟩ : syracuseStep 5606117 = 1051147) (by norm_num)
theorem B3738365 : Blo 1659529 3738365 := bbase (se 3 (by rfl) ⟨700943, by rfl⟩ : syracuseStep 3738365 = 1401887) (by norm_num)
theorem B4205317 : Blo 1659529 4205317 := bbase (se 4 (by rfl) ⟨394248, by rfl⟩ : syracuseStep 4205317 = 788497) (by norm_num)
theorem B3738437 : Blo 1659529 3738437 := bbase (se 4 (by rfl) ⟨350478, by rfl⟩ : syracuseStep 3738437 = 700957) (by norm_num)
theorem B1772389 : Blo 1659529 1772389 := bbase (se 4 (by rfl) ⟨166161, by rfl⟩ : syracuseStep 1772389 = 332323) (by norm_num)
theorem B4205429 : Blo 1659529 4205429 := bbase (se 5 (by rfl) ⟨197129, by rfl⟩ : syracuseStep 4205429 = 394259) (by norm_num)
theorem B1772461 : Blo 1659529 1772461 := bbase (se 3 (by rfl) ⟨332336, by rfl⟩ : syracuseStep 1772461 = 664673) (by norm_num)
theorem B13642805 : Blo 1659529 13642805 := bbase (se 5 (by rfl) ⟨639506, by rfl⟩ : syracuseStep 13642805 = 1279013) (by norm_num)
theorem B4205621 : Blo 1659529 4205621 := bbase (se 5 (by rfl) ⟨197138, by rfl⟩ : syracuseStep 4205621 = 394277) (by norm_num)
theorem B1772641 : Blo 1659529 1772641 := bbase (se 2 (by rfl) ⟨664740, by rfl⟩ : syracuseStep 1772641 = 1329481) (by norm_num)
theorem B3787877 : Blo 1659529 3787877 := bbase (se 4 (by rfl) ⟨355113, by rfl⟩ : syracuseStep 3787877 = 710227) (by norm_num)
theorem B1797233 : Blo 1659529 1797233 := bbase (se 2 (by rfl) ⟨673962, by rfl⟩ : syracuseStep 1797233 = 1347925) (by norm_num)
theorem B5606549 : Blo 1659529 5606549 := bbase (se 6 (by rfl) ⟨131403, by rfl⟩ : syracuseStep 5606549 = 262807) (by norm_num)
theorem B2100421 : Blo 1659529 2100421 := bbase (se 4 (by rfl) ⟨196914, by rfl⟩ : syracuseStep 2100421 = 393829) (by norm_num)
theorem B1682713 : Blo 1659529 1682713 := bbase (se 2 (by rfl) ⟨631017, by rfl⟩ : syracuseStep 1682713 = 1262035) (by norm_num)
theorem B4730197 : Blo 1659529 4730197 := bbase (se 11 (by rfl) ⟨3464, by rfl⟩ : syracuseStep 4730197 = 6929) (by norm_num)
theorem B2100593 : Blo 1659529 2100593 := bbase (se 2 (by rfl) ⟨787722, by rfl⟩ : syracuseStep 2100593 = 1575445) (by norm_num)
theorem B2100649 : Blo 1659529 2100649 := bbase (se 2 (by rfl) ⟨787743, by rfl⟩ : syracuseStep 2100649 = 1575487) (by norm_num)
theorem B2100745 : Blo 1659529 2100745 := bbase (se 2 (by rfl) ⟨787779, by rfl⟩ : syracuseStep 2100745 = 1575559) (by norm_num)
theorem B1994269 : Blo 1659529 1994269 := bbase (se 3 (by rfl) ⟨373925, by rfl⟩ : syracuseStep 1994269 = 747851) (by norm_num)
theorem B1773085 : Blo 1659529 1773085 := bbase (se 3 (by rfl) ⟨332453, by rfl⟩ : syracuseStep 1773085 = 664907) (by norm_num)
theorem B3788333 : Blo 1659529 3788333 := bbase (se 3 (by rfl) ⟨710312, by rfl⟩ : syracuseStep 3788333 = 1420625) (by norm_num)
theorem B5606981 : Blo 1659529 5606981 := bbase (se 4 (by rfl) ⟨525654, by rfl⟩ : syracuseStep 5606981 = 1051309) (by norm_num)
theorem B6475349 : Blo 1659529 6475349 := bbase (se 8 (by rfl) ⟨37941, by rfl⟩ : syracuseStep 6475349 = 75883) (by norm_num)
theorem B1994365 : Blo 1659529 1994365 := bbase (se 3 (by rfl) ⟨373943, by rfl⟩ : syracuseStep 1994365 = 747887) (by norm_num)
theorem B1773209 : Blo 1659529 1773209 := bbase (se 2 (by rfl) ⟨664953, by rfl⟩ : syracuseStep 1773209 = 1329907) (by norm_num)
theorem B2100917 : Blo 1659529 2100917 := bbase (se 5 (by rfl) ⟨98480, by rfl⟩ : syracuseStep 2100917 = 196961) (by norm_num)
theorem B2100973 : Blo 1659529 2100973 := bbase (se 3 (by rfl) ⟨393932, by rfl⟩ : syracuseStep 2100973 = 787865) (by norm_num)
theorem B12775157 : Blo 1659529 12775157 := bbase (se 5 (by rfl) ⟨598835, by rfl⟩ : syracuseStep 12775157 = 1197671) (by norm_num)
theorem B6303541 : Blo 1659529 6303541 := bbase (se 5 (by rfl) ⟨295478, by rfl⟩ : syracuseStep 6303541 = 590957) (by norm_num)
theorem B2879293 : Blo 1659529 2879293 := bbase (se 3 (by rfl) ⟨539867, by rfl⟩ : syracuseStep 2879293 = 1079735) (by norm_num)
theorem B2363213 : Blo 1659529 2363213 := bbase (se 3 (by rfl) ⟨443102, by rfl⟩ : syracuseStep 2363213 = 886205) (by norm_num)
theorem B2101069 : Blo 1659529 2101069 := bbase (se 3 (by rfl) ⟨393950, by rfl⟩ : syracuseStep 2101069 = 787901) (by norm_num)
theorem B8408933 : Blo 1659529 8408933 := bbase (se 4 (by rfl) ⟨788337, by rfl⟩ : syracuseStep 8408933 = 1576675) (by norm_num)
theorem B1773461 : Blo 1659529 1773461 := bbase (se 6 (by rfl) ⟨41565, by rfl⟩ : syracuseStep 1773461 = 83131) (by norm_num)
theorem B2363293 : Blo 1659529 2363293 := bbase (se 3 (by rfl) ⟨443117, by rfl⟩ : syracuseStep 2363293 = 886235) (by norm_num)
theorem B5607413 : Blo 1659529 5607413 := bbase (se 5 (by rfl) ⟨262847, by rfl⟩ : syracuseStep 5607413 = 525695) (by norm_num)
theorem B2101241 : Blo 1659529 2101241 := bbase (se 2 (by rfl) ⟨787965, by rfl⟩ : syracuseStep 2101241 = 1575931) (by norm_num)
theorem B1994749 : Blo 1659529 1994749 := bbase (se 3 (by rfl) ⟨374015, by rfl⟩ : syracuseStep 1994749 = 748031) (by norm_num)
theorem B5754901 : Blo 1659529 5754901 := bbase (se 6 (by rfl) ⟨134880, by rfl⟩ : syracuseStep 5754901 = 269761) (by norm_num)
theorem B2363413 : Blo 1659529 2363413 := bbase (se 6 (by rfl) ⟨55392, by rfl⟩ : syracuseStep 2363413 = 110785) (by norm_num)
theorem B2101297 : Blo 1659529 2101297 := bbase (se 2 (by rfl) ⟨787986, by rfl⟩ : syracuseStep 2101297 = 1575973) (by norm_num)
theorem B6303845 : Blo 1659529 6303845 := bbase (se 4 (by rfl) ⟨590985, by rfl⟩ : syracuseStep 6303845 = 1181971) (by norm_num)
theorem B2363509 : Blo 1659529 2363509 := bbase (se 5 (by rfl) ⟨110789, by rfl⟩ : syracuseStep 2363509 = 221579) (by norm_num)
theorem B2101393 : Blo 1659529 2101393 := bbase (se 2 (by rfl) ⟨788022, by rfl⟩ : syracuseStep 2101393 = 1576045) (by norm_num)
theorem B5681333 : Blo 1659529 5681333 := bbase (se 5 (by rfl) ⟨266312, by rfl⟩ : syracuseStep 5681333 = 532625) (by norm_num)
theorem B8523989 : Blo 1659529 8523989 := bbase (se 7 (by rfl) ⟨99890, by rfl⟩ : syracuseStep 8523989 = 199781) (by norm_num)
theorem B2101565 : Blo 1659529 2101565 := bbase (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) (by norm_num)
theorem B1773905 : Blo 1659529 1773905 := bbase (se 2 (by rfl) ⟨665214, by rfl⟩ : syracuseStep 1773905 = 1330429) (by norm_num)
theorem B2101621 : Blo 1659529 2101621 := bbase (se 5 (by rfl) ⟨98513, by rfl⟩ : syracuseStep 2101621 = 197027) (by norm_num)
theorem B4731301 : Blo 1659529 4731301 := bbase (se 4 (by rfl) ⟨443559, by rfl⟩ : syracuseStep 4731301 = 887119) (by norm_num)
theorem B2101717 : Blo 1659529 2101717 := bbase (se 7 (by rfl) ⟨24629, by rfl⟩ : syracuseStep 2101717 = 49259) (by norm_num)
theorem B5681621 : Blo 1659529 5681621 := bbase (se 7 (by rfl) ⟨66581, by rfl⟩ : syracuseStep 5681621 = 133163) (by norm_num)
theorem B1774153 : Blo 1659529 1774153 := bbase (se 2 (by rfl) ⟨665307, by rfl⟩ : syracuseStep 1774153 = 1330615) (by norm_num)
theorem B2364005 : Blo 1659529 2364005 := bbase (se 4 (by rfl) ⟨221625, by rfl⟩ : syracuseStep 2364005 = 443251) (by norm_num)
theorem B2101889 : Blo 1659529 2101889 := bbase (se 2 (by rfl) ⟨788208, by rfl⟩ : syracuseStep 2101889 = 1576417) (by norm_num)
theorem B5321381 : Blo 1659529 5321381 := bbase (se 4 (by rfl) ⟨498879, by rfl⟩ : syracuseStep 5321381 = 997759) (by norm_num)
theorem B2101945 : Blo 1659529 2101945 := bbase (se 2 (by rfl) ⟨788229, by rfl⟩ : syracuseStep 2101945 = 1576459) (by norm_num)
theorem B1684157 : Blo 1659529 1684157 := bbase (se 3 (by rfl) ⟨315779, by rfl⟩ : syracuseStep 1684157 = 631559) (by norm_num)
theorem B2159365 : Blo 1659529 2159365 := bbase (se 4 (by rfl) ⟨202440, by rfl⟩ : syracuseStep 2159365 = 404881) (by norm_num)
theorem B2102041 : Blo 1659529 2102041 := bbase (se 2 (by rfl) ⟨788265, by rfl⟩ : syracuseStep 2102041 = 1576531) (by norm_num)
theorem B3150677 : Blo 1659529 3150677 := bbase (se 9 (by rfl) ⟨9230, by rfl⟩ : syracuseStep 3150677 = 18461) (by norm_num)
theorem B2659205 : Blo 1659529 2659205 := bbase (se 4 (by rfl) ⟨249300, by rfl⟩ : syracuseStep 2659205 = 498601) (by norm_num)
theorem B2102213 : Blo 1659529 2102213 := bbase (se 4 (by rfl) ⟨197082, by rfl⟩ : syracuseStep 2102213 = 394165) (by norm_num)
theorem B3150829 : Blo 1659529 3150829 := bbase (se 3 (by rfl) ⟨590780, by rfl⟩ : syracuseStep 3150829 = 1181561) (by norm_num)
theorem B2102269 : Blo 1659529 2102269 := bbase (se 3 (by rfl) ⟨394175, by rfl⟩ : syracuseStep 2102269 = 788351) (by norm_num)
theorem B2659333 : Blo 1659529 2659333 := bbase (se 4 (by rfl) ⟨249312, by rfl⟩ : syracuseStep 2659333 = 498625) (by norm_num)
theorem B1995797 : Blo 1659529 1995797 := bbase (se 6 (by rfl) ⟨46776, by rfl⟩ : syracuseStep 1995797 = 93553) (by norm_num)
theorem B2102365 : Blo 1659529 2102365 := bbase (se 3 (by rfl) ⟨394193, by rfl⟩ : syracuseStep 2102365 = 788387) (by norm_num)
theorem B8410229 : Blo 1659529 8410229 := bbase (se 5 (by rfl) ⟨394229, by rfl⟩ : syracuseStep 8410229 = 788459) (by norm_num)
theorem B7091333 : Blo 1659529 7091333 := bbase (se 4 (by rfl) ⟨664812, by rfl⟩ : syracuseStep 7091333 = 1329625) (by norm_num)
theorem B2364557 : Blo 1659529 2364557 := bbase (se 3 (by rfl) ⟨443354, by rfl⟩ : syracuseStep 2364557 = 886709) (by norm_num)
theorem B2102537 : Blo 1659529 2102537 := bbase (se 2 (by rfl) ⟨788451, by rfl⟩ : syracuseStep 2102537 = 1576903) (by norm_num)
theorem B3151133 : Blo 1659529 3151133 := bbase (se 3 (by rfl) ⟨590837, by rfl⟩ : syracuseStep 3151133 = 1181675) (by norm_num)
theorem B2102593 : Blo 1659529 2102593 := bbase (se 2 (by rfl) ⟨788472, by rfl⟩ : syracuseStep 2102593 = 1576945) (by norm_num)
theorem B13464949 : Blo 1659529 13464949 := bbase (se 5 (by rfl) ⟨631169, by rfl⟩ : syracuseStep 13464949 = 1262339) (by norm_num)
theorem B5051765 : Blo 1659529 5051765 := bbase (se 5 (by rfl) ⟨236801, by rfl⟩ : syracuseStep 5051765 = 473603) (by norm_num)
theorem B2659717 : Blo 1659529 2659717 := bbase (se 4 (by rfl) ⟨249348, by rfl⟩ : syracuseStep 2659717 = 498697) (by norm_num)
theorem B2102689 : Blo 1659529 2102689 := bbase (se 2 (by rfl) ⟨788508, by rfl⟩ : syracuseStep 2102689 = 1577017) (by norm_num)
theorem B7091621 : Blo 1659529 7091621 := bbase (se 4 (by rfl) ⟨664839, by rfl⟩ : syracuseStep 7091621 = 1329679) (by norm_num)
theorem B3544573 : Blo 1659529 3544573 := bbase (se 3 (by rfl) ⟨664607, by rfl⟩ : syracuseStep 3544573 = 1329215) (by norm_num)
theorem B8402453 : Blo 1659529 8402453 := bbase (se 6 (by rfl) ⟨196932, by rfl⟩ : syracuseStep 8402453 = 393865) (by norm_num)
theorem B5322293 : Blo 1659529 5322293 := bbase (se 5 (by rfl) ⟨249482, by rfl⟩ : syracuseStep 5322293 = 498965) (by norm_num)
theorem B2102861 : Blo 1659529 2102861 := bbase (se 3 (by rfl) ⟨394286, by rfl⟩ : syracuseStep 2102861 = 788573) (by norm_num)
theorem B3364453 : Blo 1659529 3364453 := bbase (se 4 (by rfl) ⟨315417, by rfl⟩ : syracuseStep 3364453 = 630835) (by norm_num)
theorem B2659973 : Blo 1659529 2659973 := bbase (se 4 (by rfl) ⟨249372, by rfl⟩ : syracuseStep 2659973 = 498745) (by norm_num)
theorem B3544717 : Blo 1659529 3544717 := bbase (se 3 (by rfl) ⟨664634, by rfl⟩ : syracuseStep 3544717 = 1329269) (by norm_num)
theorem B5600933 : Blo 1659529 5600933 := bbase (se 4 (by rfl) ⟨525087, by rfl⟩ : syracuseStep 5600933 = 1050175) (by norm_num)
theorem B7673525 : Blo 1659529 7673525 := bbase (se 5 (by rfl) ⟨359696, by rfl⟩ : syracuseStep 7673525 = 719393) (by norm_num)
theorem B9459413 : Blo 1659529 9459413 := bbase (se 7 (by rfl) ⟨110852, by rfl⟩ : syracuseStep 9459413 = 221705) (by norm_num)
theorem B2365309 : Blo 1659529 2365309 := bbase (se 3 (by rfl) ⟨443495, by rfl⟩ : syracuseStep 2365309 = 886991) (by norm_num)
theorem B2021377 : Blo 1659529 2021377 := bbase (se 2 (by rfl) ⟨758016, by rfl⟩ : syracuseStep 2021377 = 1516033) (by norm_num)
theorem B3545093 : Blo 1659529 3545093 := bbase (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) (by norm_num)
theorem B3151885 : Blo 1659529 3151885 := bbase (se 3 (by rfl) ⟨590978, by rfl⟩ : syracuseStep 3151885 = 1181957) (by norm_num)
theorem B7976981 : Blo 1659529 7976981 := bbase (se 6 (by rfl) ⟨186960, by rfl⟩ : syracuseStep 7976981 = 373921) (by norm_num)
theorem B5986325 : Blo 1659529 5986325 := bbase (se 6 (by rfl) ⟨140304, by rfl⟩ : syracuseStep 5986325 = 280609) (by norm_num)
theorem B5601365 : Blo 1659529 5601365 := bbase (se 8 (by rfl) ⟨32820, by rfl⟩ : syracuseStep 5601365 = 65641) (by norm_num)
theorem B7092373 : Blo 1659529 7092373 := bbase (se 6 (by rfl) ⟨166227, by rfl⟩ : syracuseStep 7092373 = 332455) (by norm_num)
theorem B3152029 : Blo 1659529 3152029 := bbase (se 3 (by rfl) ⟨591005, by rfl⟩ : syracuseStep 3152029 = 1182011) (by norm_num)
theorem B6305957 : Blo 1659529 6305957 := bbase (se 4 (by rfl) ⟨591183, by rfl⟩ : syracuseStep 6305957 = 1182367) (by norm_num)
theorem B5986469 : Blo 1659529 5986469 := bbase (se 4 (by rfl) ⟨561231, by rfl⟩ : syracuseStep 5986469 = 1122463) (by norm_num)
theorem B4258045 : Blo 1659529 4258045 := bbase (se 3 (by rfl) ⟨798383, by rfl⟩ : syracuseStep 4258045 = 1596767) (by norm_num)
theorem B3152189 : Blo 1659529 3152189 := bbase (se 3 (by rfl) ⟨591035, by rfl⟩ : syracuseStep 3152189 = 1182071) (by norm_num)
theorem B4200781 : Blo 1659529 4200781 := bbase (se 3 (by rfl) ⟨787646, by rfl⟩ : syracuseStep 4200781 = 1575293) (by norm_num)
theorem B3545461 : Blo 1659529 3545461 := bbase (se 5 (by rfl) ⟨166193, by rfl⟩ : syracuseStep 3545461 = 332387) (by norm_num)
theorem B6068645 : Blo 1659529 6068645 := bbase (se 4 (by rfl) ⟨568935, by rfl⟩ : syracuseStep 6068645 = 1137871) (by norm_num)
theorem B14186933 : Blo 1659529 14186933 := bbase (se 5 (by rfl) ⟨665012, by rfl⟩ : syracuseStep 14186933 = 1330025) (by norm_num)
theorem B4200893 : Blo 1659529 4200893 := bbase (se 3 (by rfl) ⟨787667, by rfl⟩ : syracuseStep 4200893 = 1575335) (by norm_num)
theorem B6306245 : Blo 1659529 6306245 := bbase (se 4 (by rfl) ⟨591210, by rfl⟩ : syracuseStep 6306245 = 1182421) (by norm_num)
theorem B3152333 : Blo 1659529 3152333 := bbase (se 3 (by rfl) ⟨591062, by rfl⟩ : syracuseStep 3152333 = 1182125) (by norm_num)
theorem B3733973 : Blo 1659529 3733973 := bbase (se 7 (by rfl) ⟨43757, by rfl⟩ : syracuseStep 3733973 = 87515) (by norm_num)
theorem B2660845 : Blo 1659529 2660845 := bbase (se 3 (by rfl) ⟨498908, by rfl⟩ : syracuseStep 2660845 = 997817) (by norm_num)
theorem B5601797 : Blo 1659529 5601797 := bbase (se 4 (by rfl) ⟨525168, by rfl⟩ : syracuseStep 5601797 = 1050337) (by norm_num)
theorem B3734045 : Blo 1659529 3734045 := bbase (se 3 (by rfl) ⟨700133, by rfl⟩ : syracuseStep 3734045 = 1400267) (by norm_num)
theorem B2660941 : Blo 1659529 2660941 := bbase (se 3 (by rfl) ⟨498926, by rfl⟩ : syracuseStep 2660941 = 997853) (by norm_num)
theorem B3643997 : Blo 1659529 3643997 := bbase (se 3 (by rfl) ⟨683249, by rfl⟩ : syracuseStep 3643997 = 1366499) (by norm_num)
theorem B3734117 : Blo 1659529 3734117 := bbase (se 4 (by rfl) ⟨350073, by rfl⟩ : syracuseStep 3734117 = 700147) (by norm_num)
theorem B4201085 : Blo 1659529 4201085 := bbase (se 3 (by rfl) ⟨787703, by rfl⟩ : syracuseStep 4201085 = 1575407) (by norm_num)
theorem B3734189 : Blo 1659529 3734189 := bbase (se 3 (by rfl) ⟨700160, by rfl⟩ : syracuseStep 3734189 = 1400321) (by norm_num)
theorem B7977653 : Blo 1659529 7977653 := bbase (se 5 (by rfl) ⟨373952, by rfl⟩ : syracuseStep 7977653 = 747905) (by norm_num)
theorem B3152621 : Blo 1659529 3152621 := bbase (se 3 (by rfl) ⟨591116, by rfl⟩ : syracuseStep 3152621 = 1182233) (by norm_num)
theorem B2661101 : Blo 1659529 2661101 := bbase (se 3 (by rfl) ⟨498956, by rfl⟩ : syracuseStep 2661101 = 997913) (by norm_num)
theorem B3734261 : Blo 1659529 3734261 := bbase (se 5 (by rfl) ⟨175043, by rfl⟩ : syracuseStep 3734261 = 350087) (by norm_num)
theorem B3365621 : Blo 1659529 3365621 := bbase (se 5 (by rfl) ⟨157763, by rfl⟩ : syracuseStep 3365621 = 315527) (by norm_num)
theorem B8403749 : Blo 1659529 8403749 := bbase (se 4 (by rfl) ⟨787851, by rfl⟩ : syracuseStep 8403749 = 1575703) (by norm_num)
theorem B3734333 : Blo 1659529 3734333 := bbase (se 3 (by rfl) ⟨700187, by rfl⟩ : syracuseStep 3734333 = 1400375) (by norm_num)
theorem B2841413 : Blo 1659529 2841413 := bbase (se 4 (by rfl) ⟨266382, by rfl⟩ : syracuseStep 2841413 = 532765) (by norm_num)
theorem B7093109 : Blo 1659529 7093109 := bbase (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) (by norm_num)
theorem B9460597 : Blo 1659529 9460597 := bbase (se 5 (by rfl) ⟨443465, by rfl⟩ : syracuseStep 9460597 = 886931) (by norm_num)
theorem B3734405 : Blo 1659529 3734405 := bbase (se 4 (by rfl) ⟨350100, by rfl⟩ : syracuseStep 3734405 = 700201) (by norm_num)
theorem B3152773 : Blo 1659529 3152773 := bbase (se 4 (by rfl) ⟨295572, by rfl⟩ : syracuseStep 3152773 = 591145) (by norm_num)
theorem B2800541 : Blo 1659529 2800541 := bbase (se 3 (by rfl) ⟨525101, by rfl⟩ : syracuseStep 2800541 = 1050203) (by norm_num)
theorem B4488101 : Blo 1659529 4488101 := bbase (se 4 (by rfl) ⟨420759, by rfl⟩ : syracuseStep 4488101 = 841519) (by norm_num)
theorem B5602229 : Blo 1659529 5602229 := bbase (se 5 (by rfl) ⟨262604, by rfl⟩ : syracuseStep 5602229 = 525209) (by norm_num)
theorem B3734477 : Blo 1659529 3734477 := bbase (se 3 (by rfl) ⟨700214, by rfl⟩ : syracuseStep 3734477 = 1400429) (by norm_num)
theorem B4201429 : Blo 1659529 4201429 := bbase (se 7 (by rfl) ⟨49235, by rfl⟩ : syracuseStep 4201429 = 98471) (by norm_num)
theorem B68189141 : Blo 1659529 68189141 := bbase (se 7 (by rfl) ⟨799091, by rfl⟩ : syracuseStep 68189141 = 1598183) (by norm_num)
theorem B2489309 : Blo 1659529 2489309 := bbase (se 3 (by rfl) ⟨466745, by rfl⟩ : syracuseStep 2489309 = 933491) (by norm_num)
theorem B2489333 : Blo 1659529 2489333 := bbase (se 5 (by rfl) ⟨116687, by rfl⟩ : syracuseStep 2489333 = 233375) (by norm_num)
theorem B2489357 : Blo 1659529 2489357 := bbase (se 3 (by rfl) ⟨466754, by rfl⟩ : syracuseStep 2489357 = 933509) (by norm_num)
theorem B3734549 : Blo 1659529 3734549 := bbase (se 6 (by rfl) ⟨87528, by rfl⟩ : syracuseStep 3734549 = 175057) (by norm_num)
theorem B2800669 : Blo 1659529 2800669 := bbase (se 3 (by rfl) ⟨525125, by rfl⟩ : syracuseStep 2800669 = 1050251) (by norm_num)
theorem B2489381 : Blo 1659529 2489381 := bbase (se 4 (by rfl) ⟨233379, by rfl⟩ : syracuseStep 2489381 = 466759) (by norm_num)
theorem B2243629 : Blo 1659529 2243629 := bbase (se 3 (by rfl) ⟨420680, by rfl⟩ : syracuseStep 2243629 = 841361) (by norm_num)
theorem B2489405 : Blo 1659529 2489405 := bbase (se 3 (by rfl) ⟨466763, by rfl⟩ : syracuseStep 2489405 = 933527) (by norm_num)
theorem B4201541 : Blo 1659529 4201541 := bbase (se 4 (by rfl) ⟨393894, by rfl⟩ : syracuseStep 4201541 = 787789) (by norm_num)
theorem B2489429 : Blo 1659529 2489429 := bbase (se 8 (by rfl) ⟨14586, by rfl⟩ : syracuseStep 2489429 = 29173) (by norm_num)
theorem B3734621 : Blo 1659529 3734621 := bbase (se 3 (by rfl) ⟨700241, by rfl⟩ : syracuseStep 3734621 = 1400483) (by norm_num)
theorem B2489453 : Blo 1659529 2489453 := bbase (se 3 (by rfl) ⟨466772, by rfl⟩ : syracuseStep 2489453 = 933545) (by norm_num)
theorem B2800757 : Blo 1659529 2800757 := bbase (se 5 (by rfl) ⟨131285, by rfl⟩ : syracuseStep 2800757 = 262571) (by norm_num)
theorem B2489477 : Blo 1659529 2489477 := bbase (se 4 (by rfl) ⟨233388, by rfl⟩ : syracuseStep 2489477 = 466777) (by norm_num)
theorem B2489501 : Blo 1659529 2489501 := bbase (se 3 (by rfl) ⟨466781, by rfl⟩ : syracuseStep 2489501 = 933563) (by norm_num)
theorem B3734693 : Blo 1659529 3734693 := bbase (se 4 (by rfl) ⟨350127, by rfl⟩ : syracuseStep 3734693 = 700255) (by norm_num)
theorem B2489525 : Blo 1659529 2489525 := bbase (se 5 (by rfl) ⟨116696, by rfl⟩ : syracuseStep 2489525 = 233393) (by norm_num)
theorem B3153077 : Blo 1659529 3153077 := bbase (se 5 (by rfl) ⟨147800, by rfl⟩ : syracuseStep 3153077 = 295601) (by norm_num)
theorem B2489549 : Blo 1659529 2489549 := bbase (se 3 (by rfl) ⟨466790, by rfl⟩ : syracuseStep 2489549 = 933581) (by norm_num)
theorem B1866973 : Blo 1659529 1866973 := bbase (se 3 (by rfl) ⟨350057, by rfl⟩ : syracuseStep 1866973 = 700115) (by norm_num)
theorem B2489573 : Blo 1659529 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B3734765 : Blo 1659529 3734765 := bbase (se 3 (by rfl) ⟨700268, by rfl⟩ : syracuseStep 3734765 = 1400537) (by norm_num)
theorem B2800885 : Blo 1659529 2800885 := bbase (se 5 (by rfl) ⟨131291, by rfl⟩ : syracuseStep 2800885 = 262583) (by norm_num)
theorem B2489597 : Blo 1659529 2489597 := bbase (se 3 (by rfl) ⟨466799, by rfl⟩ : syracuseStep 2489597 = 933599) (by norm_num)
theorem B1867009 : Blo 1659529 1867009 := bbase (se 2 (by rfl) ⟨700128, by rfl⟩ : syracuseStep 1867009 = 1400257) (by norm_num)
theorem B4201733 : Blo 1659529 4201733 := bbase (se 4 (by rfl) ⟨393912, by rfl⟩ : syracuseStep 4201733 = 787825) (by norm_num)
theorem B2243845 : Blo 1659529 2243845 := bbase (se 4 (by rfl) ⟨210360, by rfl⟩ : syracuseStep 2243845 = 420721) (by norm_num)
theorem B2489621 : Blo 1659529 2489621 := bbase (se 6 (by rfl) ⟨58350, by rfl⟩ : syracuseStep 2489621 = 116701) (by norm_num)
theorem B1867045 : Blo 1659529 1867045 := bbase (se 4 (by rfl) ⟨175035, by rfl⟩ : syracuseStep 1867045 = 350071) (by norm_num)
theorem B2489645 : Blo 1659529 2489645 := bbase (se 3 (by rfl) ⟨466808, by rfl⟩ : syracuseStep 2489645 = 933617) (by norm_num)
theorem B3734837 : Blo 1659529 3734837 := bbase (se 5 (by rfl) ⟨175070, by rfl⟩ : syracuseStep 3734837 = 350141) (by norm_num)
theorem B2489669 : Blo 1659529 2489669 := bbase (se 4 (by rfl) ⟨233406, by rfl⟩ : syracuseStep 2489669 = 466813) (by norm_num)
theorem B1867081 : Blo 1659529 1867081 := bbase (se 2 (by rfl) ⟨700155, by rfl⟩ : syracuseStep 1867081 = 1400311) (by norm_num)
theorem B2800973 : Blo 1659529 2800973 := bbase (se 3 (by rfl) ⟨525182, by rfl⟩ : syracuseStep 2800973 = 1050365) (by norm_num)
theorem B2489693 : Blo 1659529 2489693 := bbase (se 3 (by rfl) ⟨466817, by rfl⟩ : syracuseStep 2489693 = 933635) (by norm_num)
theorem B5602661 : Blo 1659529 5602661 := bbase (se 4 (by rfl) ⟨525249, by rfl⟩ : syracuseStep 5602661 = 1050499) (by norm_num)
theorem B1867117 : Blo 1659529 1867117 := bbase (se 3 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 1867117 = 700169) (by norm_num)
theorem B2489717 : Blo 1659529 2489717 := bbase (se 5 (by rfl) ⟨116705, by rfl⟩ : syracuseStep 2489717 = 233411) (by norm_num)
theorem B3734909 : Blo 1659529 3734909 := bbase (se 3 (by rfl) ⟨700295, by rfl⟩ : syracuseStep 3734909 = 1400591) (by norm_num)
theorem B2489741 : Blo 1659529 2489741 := bbase (se 3 (by rfl) ⟨466826, by rfl⟩ : syracuseStep 2489741 = 933653) (by norm_num)
theorem B1867153 : Blo 1659529 1867153 := bbase (se 2 (by rfl) ⟨700182, by rfl⟩ : syracuseStep 1867153 = 1400365) (by norm_num)
theorem B2489765 : Blo 1659529 2489765 := bbase (se 4 (by rfl) ⟨233415, by rfl⟩ : syracuseStep 2489765 = 466831) (by norm_num)
theorem B1867189 : Blo 1659529 1867189 := bbase (se 5 (by rfl) ⟨87524, by rfl⟩ : syracuseStep 1867189 = 175049) (by norm_num)
theorem B2489789 : Blo 1659529 2489789 := bbase (se 3 (by rfl) ⟨466835, by rfl⟩ : syracuseStep 2489789 = 933671) (by norm_num)
theorem B2244029 : Blo 1659529 2244029 := bbase (se 3 (by rfl) ⟨420755, by rfl⟩ : syracuseStep 2244029 = 841511) (by norm_num)
theorem B4046269 : Blo 1659529 4046269 := bbase (se 3 (by rfl) ⟨758675, by rfl⟩ : syracuseStep 4046269 = 1517351) (by norm_num)
theorem B3734981 : Blo 1659529 3734981 := bbase (se 4 (by rfl) ⟨350154, by rfl⟩ : syracuseStep 3734981 = 700309) (by norm_num)
theorem B2801101 : Blo 1659529 2801101 := bbase (se 3 (by rfl) ⟨525206, by rfl⟩ : syracuseStep 2801101 = 1050413) (by norm_num)
theorem B2489813 : Blo 1659529 2489813 := bbase (se 7 (by rfl) ⟨29177, by rfl⟩ : syracuseStep 2489813 = 58355) (by norm_num)
theorem B4259285 : Blo 1659529 4259285 := bbase (se 7 (by rfl) ⟨49913, by rfl⟩ : syracuseStep 4259285 = 99827) (by norm_num)
theorem B1867225 : Blo 1659529 1867225 := bbase (se 2 (by rfl) ⟨700209, by rfl⟩ : syracuseStep 1867225 = 1400419) (by norm_num)
theorem B2489837 : Blo 1659529 2489837 := bbase (se 3 (by rfl) ⟨466844, by rfl⟩ : syracuseStep 2489837 = 933689) (by norm_num)
theorem B1867261 : Blo 1659529 1867261 := bbase (se 3 (by rfl) ⟨350111, by rfl⟩ : syracuseStep 1867261 = 700223) (by norm_num)
theorem B2489861 : Blo 1659529 2489861 := bbase (se 4 (by rfl) ⟨233424, by rfl⟩ : syracuseStep 2489861 = 466849) (by norm_num)
theorem B3735053 : Blo 1659529 3735053 := bbase (se 3 (by rfl) ⟨700322, by rfl⟩ : syracuseStep 3735053 = 1400645) (by norm_num)
theorem B2489885 : Blo 1659529 2489885 := bbase (se 3 (by rfl) ⟨466853, by rfl⟩ : syracuseStep 2489885 = 933707) (by norm_num)
theorem B1867297 : Blo 1659529 1867297 := bbase (se 2 (by rfl) ⟨700236, by rfl⟩ : syracuseStep 1867297 = 1400473) (by norm_num)
theorem B2801189 : Blo 1659529 2801189 := bbase (se 4 (by rfl) ⟨262611, by rfl⟩ : syracuseStep 2801189 = 525223) (by norm_num)
theorem B2489909 : Blo 1659529 2489909 := bbase (se 5 (by rfl) ⟨116714, by rfl⟩ : syracuseStep 2489909 = 233429) (by norm_num)
theorem B1867333 : Blo 1659529 1867333 := bbase (se 4 (by rfl) ⟨175062, by rfl⟩ : syracuseStep 1867333 = 350125) (by norm_num)
theorem B2489933 : Blo 1659529 2489933 := bbase (se 3 (by rfl) ⟨466862, by rfl⟩ : syracuseStep 2489933 = 933725) (by norm_num)
theorem B3735125 : Blo 1659529 3735125 := bbase (se 8 (by rfl) ⟨21885, by rfl⟩ : syracuseStep 3735125 = 43771) (by norm_num)
theorem B4202077 : Blo 1659529 4202077 := bbase (se 3 (by rfl) ⟨787889, by rfl⟩ : syracuseStep 4202077 = 1575779) (by norm_num)
theorem B2489957 : Blo 1659529 2489957 := bbase (se 4 (by rfl) ⟨233433, by rfl⟩ : syracuseStep 2489957 = 466867) (by norm_num)
theorem B6307429 : Blo 1659529 6307429 := bbase (se 4 (by rfl) ⟨591321, by rfl⟩ : syracuseStep 6307429 = 1182643) (by norm_num)
theorem B1867369 : Blo 1659529 1867369 := bbase (se 2 (by rfl) ⟨700263, by rfl⟩ : syracuseStep 1867369 = 1400527) (by norm_num)
theorem B2489981 : Blo 1659529 2489981 := bbase (se 3 (by rfl) ⟨466871, by rfl⟩ : syracuseStep 2489981 = 933743) (by norm_num)
theorem B1867405 : Blo 1659529 1867405 := bbase (se 3 (by rfl) ⟨350138, by rfl⟩ : syracuseStep 1867405 = 700277) (by norm_num)
theorem B2490005 : Blo 1659529 2490005 := bbase (se 6 (by rfl) ⟨58359, by rfl⟩ : syracuseStep 2490005 = 116719) (by norm_num)
theorem B3735197 : Blo 1659529 3735197 := bbase (se 3 (by rfl) ⟨700349, by rfl⟩ : syracuseStep 3735197 = 1400699) (by norm_num)
theorem B2801317 : Blo 1659529 2801317 := bbase (se 4 (by rfl) ⟨262623, by rfl⟩ : syracuseStep 2801317 = 525247) (by norm_num)
theorem B2490029 : Blo 1659529 2490029 := bbase (se 3 (by rfl) ⟨466880, by rfl⟩ : syracuseStep 2490029 = 933761) (by norm_num)
theorem B1867441 : Blo 1659529 1867441 := bbase (se 2 (by rfl) ⟨700290, by rfl⟩ : syracuseStep 1867441 = 1400581) (by norm_num)
theorem B2490053 : Blo 1659529 2490053 := bbase (se 4 (by rfl) ⟨233442, by rfl⟩ : syracuseStep 2490053 = 466885) (by norm_num)
theorem B4202189 : Blo 1659529 4202189 := bbase (se 3 (by rfl) ⟨787910, by rfl⟩ : syracuseStep 4202189 = 1575821) (by norm_num)
theorem B1867477 : Blo 1659529 1867477 := bbase (se 7 (by rfl) ⟨21884, by rfl⟩ : syracuseStep 1867477 = 43769) (by norm_num)
theorem B2490077 : Blo 1659529 2490077 := bbase (se 3 (by rfl) ⟨466889, by rfl⟩ : syracuseStep 2490077 = 933779) (by norm_num)
theorem B3735269 : Blo 1659529 3735269 := bbase (se 4 (by rfl) ⟨350181, by rfl⟩ : syracuseStep 3735269 = 700363) (by norm_num)
theorem B7577317 : Blo 1659529 7577317 := bbase (se 4 (by rfl) ⟨710373, by rfl⟩ : syracuseStep 7577317 = 1420747) (by norm_num)
theorem B2490101 : Blo 1659529 2490101 := bbase (se 5 (by rfl) ⟨116723, by rfl⟩ : syracuseStep 2490101 = 233447) (by norm_num)
theorem B1867513 : Blo 1659529 1867513 := bbase (se 2 (by rfl) ⟨700317, by rfl⟩ : syracuseStep 1867513 = 1400635) (by norm_num)
theorem B2801405 : Blo 1659529 2801405 := bbase (se 3 (by rfl) ⟨525263, by rfl⟩ : syracuseStep 2801405 = 1050527) (by norm_num)
theorem B2490125 : Blo 1659529 2490125 := bbase (se 3 (by rfl) ⟨466898, by rfl⟩ : syracuseStep 2490125 = 933797) (by norm_num)
theorem B5603093 : Blo 1659529 5603093 := bbase (se 6 (by rfl) ⟨131322, by rfl⟩ : syracuseStep 5603093 = 262645) (by norm_num)
theorem B1867549 : Blo 1659529 1867549 := bbase (se 3 (by rfl) ⟨350165, by rfl⟩ : syracuseStep 1867549 = 700331) (by norm_num)
theorem B2490149 : Blo 1659529 2490149 := bbase (se 4 (by rfl) ⟨233451, by rfl⟩ : syracuseStep 2490149 = 466903) (by norm_num)
theorem B3735341 : Blo 1659529 3735341 := bbase (se 3 (by rfl) ⟨700376, by rfl⟩ : syracuseStep 3735341 = 1400753) (by norm_num)
theorem B2490173 : Blo 1659529 2490173 := bbase (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) (by norm_num)
theorem B1867585 : Blo 1659529 1867585 := bbase (se 2 (by rfl) ⟨700344, by rfl⟩ : syracuseStep 1867585 = 1400689) (by norm_num)
theorem B2490197 : Blo 1659529 2490197 := bbase (se 9 (by rfl) ⟨7295, by rfl⟩ : syracuseStep 2490197 = 14591) (by norm_num)
theorem B3546965 : Blo 1659529 3546965 := bbase (se 9 (by rfl) ⟨10391, by rfl⟩ : syracuseStep 3546965 = 20783) (by norm_num)
theorem B1867621 : Blo 1659529 1867621 := bbase (se 4 (by rfl) ⟨175089, by rfl⟩ : syracuseStep 1867621 = 350179) (by norm_num)
theorem B2490221 : Blo 1659529 2490221 := bbase (se 3 (by rfl) ⟨466916, by rfl⟩ : syracuseStep 2490221 = 933833) (by norm_num)
theorem B8085365 : Blo 1659529 8085365 := bbase (se 5 (by rfl) ⟨379001, by rfl⟩ : syracuseStep 8085365 = 758003) (by norm_num)
theorem B3735413 : Blo 1659529 3735413 := bbase (se 5 (by rfl) ⟨175097, by rfl⟩ : syracuseStep 3735413 = 350195) (by norm_num)
theorem B2801533 : Blo 1659529 2801533 := bbase (se 3 (by rfl) ⟨525287, by rfl⟩ : syracuseStep 2801533 = 1050575) (by norm_num)
theorem B2490245 : Blo 1659529 2490245 := bbase (se 4 (by rfl) ⟨233460, by rfl⟩ : syracuseStep 2490245 = 466921) (by norm_num)
theorem B1867657 : Blo 1659529 1867657 := bbase (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) (by norm_num)
theorem B4202381 : Blo 1659529 4202381 := bbase (se 3 (by rfl) ⟨787946, by rfl⟩ : syracuseStep 4202381 = 1575893) (by norm_num)
theorem B6307733 : Blo 1659529 6307733 := bbase (se 6 (by rfl) ⟨147837, by rfl⟩ : syracuseStep 6307733 = 295675) (by norm_num)
theorem B2490269 : Blo 1659529 2490269 := bbase (se 3 (by rfl) ⟨466925, by rfl⟩ : syracuseStep 2490269 = 933851) (by norm_num)
theorem B3153829 : Blo 1659529 3153829 := bbase (se 4 (by rfl) ⟨295671, by rfl⟩ : syracuseStep 3153829 = 591343) (by norm_num)
theorem B1867693 : Blo 1659529 1867693 := bbase (se 3 (by rfl) ⟨350192, by rfl⟩ : syracuseStep 1867693 = 700385) (by norm_num)
theorem B2490293 : Blo 1659529 2490293 := bbase (se 5 (by rfl) ⟨116732, by rfl⟩ : syracuseStep 2490293 = 233465) (by norm_num)
theorem B3735485 : Blo 1659529 3735485 := bbase (se 3 (by rfl) ⟨700403, by rfl⟩ : syracuseStep 3735485 = 1400807) (by norm_num)
theorem B2490317 : Blo 1659529 2490317 := bbase (se 3 (by rfl) ⟨466934, by rfl⟩ : syracuseStep 2490317 = 933869) (by norm_num)
theorem B1867729 : Blo 1659529 1867729 := bbase (se 2 (by rfl) ⟨700398, by rfl⟩ : syracuseStep 1867729 = 1400797) (by norm_num)
theorem B2801621 : Blo 1659529 2801621 := bbase (se 7 (by rfl) ⟨32831, by rfl⟩ : syracuseStep 2801621 = 65663) (by norm_num)
theorem B2490341 : Blo 1659529 2490341 := bbase (se 4 (by rfl) ⟨233469, by rfl⟩ : syracuseStep 2490341 = 466939) (by norm_num)
theorem B3547109 : Blo 1659529 3547109 := bbase (se 4 (by rfl) ⟨332541, by rfl⟩ : syracuseStep 3547109 = 665083) (by norm_num)
theorem B1867765 : Blo 1659529 1867765 := bbase (se 5 (by rfl) ⟨87551, by rfl⟩ : syracuseStep 1867765 = 175103) (by norm_num)
theorem B2490365 : Blo 1659529 2490365 := bbase (se 3 (by rfl) ⟨466943, by rfl⟩ : syracuseStep 2490365 = 933887) (by norm_num)
theorem B2695169 : Blo 1659529 2695169 := bstep (se 2 (by rfl) ⟨1010688, by rfl⟩ : syracuseStep 2695169 = 2021377) B2021377
theorem B2490371 : Blo 1659529 2490371 := bstep (se 1 (by rfl) ⟨1867778, by rfl⟩ : syracuseStep 2490371 = 3735557) B3735557
theorem B9453581 : Blo 1659529 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B4202513 : Blo 1659529 4202513 := bstep (se 2 (by rfl) ⟨1575942, by rfl⟩ : syracuseStep 4202513 = 3151885) B3151885
theorem B2490401 : Blo 1659529 2490401 := bstep (se 2 (by rfl) ⟨933900, by rfl⟩ : syracuseStep 2490401 = 1867801) B1867801
theorem B5603363 : Blo 1659529 5603363 := bstep (se 1 (by rfl) ⟨4202522, by rfl⟩ : syracuseStep 5603363 = 8405045) B8405045
theorem B2490419 : Blo 1659529 2490419 := bstep (se 1 (by rfl) ⟨1867814, by rfl⟩ : syracuseStep 2490419 = 3735629) B3735629
theorem B2801729 : Blo 1659529 2801729 := bstep (se 2 (by rfl) ⟨1050648, by rfl⟩ : syracuseStep 2801729 = 2101297) B2101297
theorem B4202563 : Blo 1659529 4202563 := bstep (se 1 (by rfl) ⟨3151922, by rfl⟩ : syracuseStep 4202563 = 6303845) B6303845
theorem B2490449 : Blo 1659529 2490449 := bstep (se 2 (by rfl) ⟨933918, by rfl⟩ : syracuseStep 2490449 = 1867837) B1867837
theorem B2490467 : Blo 1659529 2490467 := bstep (se 1 (by rfl) ⟨1867850, by rfl⟩ : syracuseStep 2490467 = 3735701) B3735701
theorem B3735665 : Blo 1659529 3735665 := bstep (se 2 (by rfl) ⟨1400874, by rfl⟩ : syracuseStep 3735665 = 2801749) B2801749
theorem B9461873 : Blo 1659529 9461873 := bstep (se 2 (by rfl) ⟨3548202, by rfl⟩ : syracuseStep 9461873 = 7096405) B7096405
theorem B1867891 : Blo 1659529 1867891 := bstep (se 1 (by rfl) ⟨1400918, by rfl⟩ : syracuseStep 1867891 = 2801837) B2801837
theorem B2490497 : Blo 1659529 2490497 := bstep (se 2 (by rfl) ⟨933936, by rfl⟩ : syracuseStep 2490497 = 1867873) B1867873
theorem B3735683 : Blo 1659529 3735683 := bstep (se 1 (by rfl) ⟨2801762, by rfl⟩ : syracuseStep 3735683 = 5603525) B5603525
theorem B2490515 : Blo 1659529 2490515 := bstep (se 1 (by rfl) ⟨1867886, by rfl⟩ : syracuseStep 2490515 = 3735773) B3735773
theorem B2490545 : Blo 1659529 2490545 := bstep (se 2 (by rfl) ⟨933954, by rfl⟩ : syracuseStep 2490545 = 1867909) B1867909
theorem B2801857 : Blo 1659529 2801857 := bstep (se 2 (by rfl) ⟨1050696, by rfl⟩ : syracuseStep 2801857 = 2101393) B2101393
theorem B2490563 : Blo 1659529 2490563 := bstep (se 1 (by rfl) ⟨1867922, by rfl⟩ : syracuseStep 2490563 = 3735845) B3735845
theorem B4202705 : Blo 1659529 4202705 := bstep (se 2 (by rfl) ⟨1576014, by rfl⟩ : syracuseStep 4202705 = 3152029) B3152029
theorem B2490593 : Blo 1659529 2490593 := bstep (se 2 (by rfl) ⟨933972, by rfl⟩ : syracuseStep 2490593 = 1867945) B1867945
theorem B2801891 : Blo 1659529 2801891 := bstep (se 1 (by rfl) ⟨2101418, by rfl⟩ : syracuseStep 2801891 = 4202837) B4202837
theorem B2490611 : Blo 1659529 2490611 := bstep (se 1 (by rfl) ⟨1867958, by rfl⟩ : syracuseStep 2490611 = 3735917) B3735917
theorem B1868035 : Blo 1659529 1868035 := bstep (se 1 (by rfl) ⟨1401026, by rfl⟩ : syracuseStep 1868035 = 2802053) B2802053
theorem B2490641 : Blo 1659529 2490641 := bstep (se 2 (by rfl) ⟨933990, by rfl⟩ : syracuseStep 2490641 = 1867981) B1867981
theorem B2490659 : Blo 1659529 2490659 := bstep (se 1 (by rfl) ⟨1867994, by rfl⟩ : syracuseStep 2490659 = 3735989) B3735989
theorem B4792621 : Blo 1659529 4792621 := bstep (se 3 (by rfl) ⟨898616, by rfl⟩ : syracuseStep 4792621 = 1797233) B1797233
theorem B5603633 : Blo 1659529 5603633 := bstep (se 2 (by rfl) ⟨2101362, by rfl⟩ : syracuseStep 5603633 = 4202725) B4202725
theorem B2490689 : Blo 1659529 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B5677393 : Blo 1659529 5677393 := bstep (se 2 (by rfl) ⟨2129022, by rfl⟩ : syracuseStep 5677393 = 4258045) B4258045
theorem B2490707 : Blo 1659529 2490707 := bstep (se 1 (by rfl) ⟨1868030, by rfl⟩ : syracuseStep 2490707 = 3736061) B3736061
theorem B2802019 : Blo 1659529 2802019 := bstep (se 1 (by rfl) ⟨2101514, by rfl⟩ : syracuseStep 2802019 = 4203029) B4203029
theorem B2490737 : Blo 1659529 2490737 := bstep (se 2 (by rfl) ⟨934026, by rfl⟩ : syracuseStep 2490737 = 1868053) B1868053
theorem B2490755 : Blo 1659529 2490755 := bstep (se 1 (by rfl) ⟨1868066, by rfl⟩ : syracuseStep 2490755 = 3736133) B3736133
theorem B12304781 : Blo 1659529 12304781 := bstep (se 3 (by rfl) ⟨2307146, by rfl⟩ : syracuseStep 12304781 = 4614293) B4614293
theorem B3735953 : Blo 1659529 3735953 := bstep (se 2 (by rfl) ⟨1400982, by rfl⟩ : syracuseStep 3735953 = 2801965) B2801965
theorem B1868179 : Blo 1659529 1868179 := bstep (se 1 (by rfl) ⟨1401134, by rfl⟩ : syracuseStep 1868179 = 2802269) B2802269
theorem B2490785 : Blo 1659529 2490785 := bstep (se 2 (by rfl) ⟨934044, by rfl⟩ : syracuseStep 2490785 = 1868089) B1868089
theorem B3735971 : Blo 1659529 3735971 := bstep (se 1 (by rfl) ⟨2801978, by rfl⟩ : syracuseStep 3735971 = 5603957) B5603957
theorem B2490803 : Blo 1659529 2490803 := bstep (se 1 (by rfl) ⟨1868102, by rfl⟩ : syracuseStep 2490803 = 3736205) B3736205
theorem B2490833 : Blo 1659529 2490833 := bstep (se 2 (by rfl) ⟨934062, by rfl⟩ : syracuseStep 2490833 = 1868125) B1868125
theorem B2490851 : Blo 1659529 2490851 := bstep (se 1 (by rfl) ⟨1868138, by rfl⟩ : syracuseStep 2490851 = 3736277) B3736277
theorem B4727281 : Blo 1659529 4727281 := bstep (se 2 (by rfl) ⟨1772730, by rfl⟩ : syracuseStep 4727281 = 3545461) B3545461
theorem B2802161 : Blo 1659529 2802161 := bstep (se 2 (by rfl) ⟨1050810, by rfl⟩ : syracuseStep 2802161 = 2101621) B2101621
theorem B2490881 : Blo 1659529 2490881 := bstep (se 2 (by rfl) ⟨934080, by rfl⟩ : syracuseStep 2490881 = 1868161) B1868161
theorem B3039761 : Blo 1659529 3039761 := bstep (se 2 (by rfl) ⟨1139910, by rfl⟩ : syracuseStep 3039761 = 2279821) B2279821
theorem B2490899 : Blo 1659529 2490899 := bstep (se 1 (by rfl) ⟨1868174, by rfl⟩ : syracuseStep 2490899 = 3736349) B3736349
theorem B1868323 : Blo 1659529 1868323 := bstep (se 1 (by rfl) ⟨1401242, by rfl⟩ : syracuseStep 1868323 = 2802485) B2802485
theorem B6308387 : Blo 1659529 6308387 := bstep (se 1 (by rfl) ⟨4731290, by rfl⟩ : syracuseStep 6308387 = 9462581) B9462581
theorem B2490929 : Blo 1659529 2490929 := bstep (se 2 (by rfl) ⟨934098, by rfl⟩ : syracuseStep 2490929 = 1868197) B1868197
theorem B6308401 : Blo 1659529 6308401 := bstep (se 2 (by rfl) ⟨2365650, by rfl⟩ : syracuseStep 6308401 = 4731301) B4731301
theorem B2490947 : Blo 1659529 2490947 := bstep (se 1 (by rfl) ⟨1868210, by rfl⟩ : syracuseStep 2490947 = 3736421) B3736421
theorem B2490977 : Blo 1659529 2490977 := bstep (se 2 (by rfl) ⟨934116, by rfl⟩ : syracuseStep 2490977 = 1868233) B1868233
theorem B2802289 : Blo 1659529 2802289 := bstep (se 2 (by rfl) ⟨1050858, by rfl⟩ : syracuseStep 2802289 = 2101717) B2101717
theorem B2490995 : Blo 1659529 2490995 := bstep (se 1 (by rfl) ⟨1868246, by rfl⟩ : syracuseStep 2490995 = 3736493) B3736493
theorem B2491025 : Blo 1659529 2491025 := bstep (se 2 (by rfl) ⟨934134, by rfl⟩ : syracuseStep 2491025 = 1868269) B1868269
theorem B2802323 : Blo 1659529 2802323 := bstep (se 1 (by rfl) ⟨2101742, by rfl⟩ : syracuseStep 2802323 = 4203485) B4203485
theorem B3547793 : Blo 1659529 3547793 := bstep (se 2 (by rfl) ⟨1330422, by rfl⟩ : syracuseStep 3547793 = 2660845) B2660845
theorem B8422051 : Blo 1659529 8422051 := bstep (se 1 (by rfl) ⟨6316538, by rfl⟩ : syracuseStep 8422051 = 12633077) B12633077
theorem B2491043 : Blo 1659529 2491043 := bstep (se 1 (by rfl) ⟨1868282, by rfl⟩ : syracuseStep 2491043 = 3736565) B3736565
theorem B7570097 : Blo 1659529 7570097 := bstep (se 2 (by rfl) ⟨2838786, by rfl⟩ : syracuseStep 7570097 = 5677573) B5677573
theorem B5046961 : Blo 1659529 5046961 := bstep (se 2 (by rfl) ⟨1892610, by rfl⟩ : syracuseStep 5046961 = 3785221) B3785221
theorem B3736241 : Blo 1659529 3736241 := bstep (se 2 (by rfl) ⟨1401090, by rfl⟩ : syracuseStep 3736241 = 2802181) B2802181
theorem B1868467 : Blo 1659529 1868467 := bstep (se 1 (by rfl) ⟨1401350, by rfl⟩ : syracuseStep 1868467 = 2802701) B2802701
theorem B2491073 : Blo 1659529 2491073 := bstep (se 2 (by rfl) ⟨934152, by rfl⟩ : syracuseStep 2491073 = 1868305) B1868305
theorem B3736259 : Blo 1659529 3736259 := bstep (se 1 (by rfl) ⟨2802194, by rfl⟩ : syracuseStep 3736259 = 5604389) B5604389
theorem B2491091 : Blo 1659529 2491091 := bstep (se 1 (by rfl) ⟨1868318, by rfl⟩ : syracuseStep 2491091 = 3736637) B3736637
theorem B2491121 : Blo 1659529 2491121 := bstep (se 2 (by rfl) ⟨934170, by rfl⟩ : syracuseStep 2491121 = 1868341) B1868341
theorem B4727555 : Blo 1659529 4727555 := bstep (se 1 (by rfl) ⟨3545666, by rfl⟩ : syracuseStep 4727555 = 7091333) B7091333
theorem B2491139 : Blo 1659529 2491139 := bstep (se 1 (by rfl) ⟨1868354, by rfl⟩ : syracuseStep 2491139 = 3736709) B3736709
theorem B2802451 : Blo 1659529 2802451 := bstep (se 1 (by rfl) ⟨2101838, by rfl⟩ : syracuseStep 2802451 = 4203677) B4203677
theorem B2491169 : Blo 1659529 2491169 := bstep (se 2 (by rfl) ⟨934188, by rfl⟩ : syracuseStep 2491169 = 1868377) B1868377
theorem B2491187 : Blo 1659529 2491187 := bstep (se 1 (by rfl) ⟨1868390, by rfl⟩ : syracuseStep 2491187 = 3736781) B3736781
theorem B1868611 : Blo 1659529 1868611 := bstep (se 1 (by rfl) ⟨1401458, by rfl⟩ : syracuseStep 1868611 = 2802917) B2802917
theorem B5604173 : Blo 1659529 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B2491217 : Blo 1659529 2491217 := bstep (se 2 (by rfl) ⟨934206, by rfl⟩ : syracuseStep 2491217 = 1868413) B1868413
theorem B2491235 : Blo 1659529 2491235 := bstep (se 1 (by rfl) ⟨1868426, by rfl⟩ : syracuseStep 2491235 = 3736853) B3736853
theorem B2491265 : Blo 1659529 2491265 := bstep (se 2 (by rfl) ⟨934224, by rfl⟩ : syracuseStep 2491265 = 1868449) B1868449
theorem B5604227 : Blo 1659529 5604227 := bstep (se 1 (by rfl) ⟨4203170, by rfl⟩ : syracuseStep 5604227 = 8406341) B8406341
theorem B53855117 : Blo 1659529 53855117 := bstep (se 3 (by rfl) ⟨10097834, by rfl⟩ : syracuseStep 53855117 = 20195669) B20195669
theorem B2491283 : Blo 1659529 2491283 := bstep (se 1 (by rfl) ⟨1868462, by rfl⟩ : syracuseStep 2491283 = 3736925) B3736925
theorem B2802593 : Blo 1659529 2802593 := bstep (se 2 (by rfl) ⟨1050972, by rfl⟩ : syracuseStep 2802593 = 2101945) B2101945
theorem B2491313 : Blo 1659529 2491313 := bstep (se 2 (by rfl) ⟨934242, by rfl⟩ : syracuseStep 2491313 = 1868485) B1868485
theorem B4727747 : Blo 1659529 4727747 := bstep (se 1 (by rfl) ⟨3545810, by rfl⟩ : syracuseStep 4727747 = 7091621) B7091621
theorem B2491331 : Blo 1659529 2491331 := bstep (se 1 (by rfl) ⟨1868498, by rfl⟩ : syracuseStep 2491331 = 3736997) B3736997
theorem B3736529 : Blo 1659529 3736529 := bstep (se 2 (by rfl) ⟨1401198, by rfl⟩ : syracuseStep 3736529 = 2802397) B2802397
theorem B1868755 : Blo 1659529 1868755 := bstep (se 1 (by rfl) ⟨1401566, by rfl⟩ : syracuseStep 1868755 = 2803133) B2803133
theorem B2491361 : Blo 1659529 2491361 := bstep (se 2 (by rfl) ⟨934260, by rfl⟩ : syracuseStep 2491361 = 1868521) B1868521
theorem B3736547 : Blo 1659529 3736547 := bstep (se 1 (by rfl) ⟨2802410, by rfl⟩ : syracuseStep 3736547 = 5604821) B5604821
theorem B8520689 : Blo 1659529 8520689 := bstep (se 2 (by rfl) ⟨3195258, by rfl⟩ : syracuseStep 8520689 = 6390517) B6390517
theorem B2491379 : Blo 1659529 2491379 := bstep (se 1 (by rfl) ⟨1868534, by rfl⟩ : syracuseStep 2491379 = 3737069) B3737069
theorem B2491409 : Blo 1659529 2491409 := bstep (se 2 (by rfl) ⟨934278, by rfl⟩ : syracuseStep 2491409 = 1868557) B1868557
theorem B2802721 : Blo 1659529 2802721 := bstep (se 2 (by rfl) ⟨1051020, by rfl⟩ : syracuseStep 2802721 = 2102041) B2102041
theorem B2491427 : Blo 1659529 2491427 := bstep (se 1 (by rfl) ⟨1868570, by rfl⟩ : syracuseStep 2491427 = 3737141) B3737141
theorem B3548195 : Blo 1659529 3548195 := bstep (se 1 (by rfl) ⟨2661146, by rfl⟩ : syracuseStep 3548195 = 5322293) B5322293
theorem B2802755 : Blo 1659529 2802755 := bstep (se 1 (by rfl) ⟨2102066, by rfl⟩ : syracuseStep 2802755 = 4204133) B4204133
theorem B2491457 : Blo 1659529 2491457 := bstep (se 2 (by rfl) ⟨934296, by rfl⟩ : syracuseStep 2491457 = 1868593) B1868593
theorem B2491475 : Blo 1659529 2491475 := bstep (se 1 (by rfl) ⟨1868606, by rfl⟩ : syracuseStep 2491475 = 3737213) B3737213
theorem B2524259 : Blo 1659529 2524259 := bstep (se 1 (by rfl) ⟨1893194, by rfl⟩ : syracuseStep 2524259 = 3786389) B3786389
theorem B1868899 : Blo 1659529 1868899 := bstep (se 1 (by rfl) ⟨1401674, by rfl⟩ : syracuseStep 1868899 = 2803349) B2803349
theorem B2491505 : Blo 1659529 2491505 := bstep (se 2 (by rfl) ⟨934314, by rfl⟩ : syracuseStep 2491505 = 1868629) B1868629
theorem B2491523 : Blo 1659529 2491523 := bstep (se 1 (by rfl) ⟨1868642, by rfl⟩ : syracuseStep 2491523 = 3737285) B3737285
theorem B5604497 : Blo 1659529 5604497 := bstep (se 2 (by rfl) ⟨2101686, by rfl⟩ : syracuseStep 5604497 = 4203373) B4203373
theorem B2491553 : Blo 1659529 2491553 := bstep (se 2 (by rfl) ⟨934332, by rfl⟩ : syracuseStep 2491553 = 1868665) B1868665
theorem B8406179 : Blo 1659529 8406179 := bstep (se 1 (by rfl) ⟨6304634, by rfl⟩ : syracuseStep 8406179 = 12609269) B12609269
theorem B4203697 : Blo 1659529 4203697 := bstep (se 2 (by rfl) ⟨1576386, by rfl⟩ : syracuseStep 4203697 = 3152773) B3152773
theorem B2491571 : Blo 1659529 2491571 := bstep (se 1 (by rfl) ⟨1868678, by rfl⟩ : syracuseStep 2491571 = 3737357) B3737357
theorem B2802883 : Blo 1659529 2802883 := bstep (se 1 (by rfl) ⟨2102162, by rfl⟩ : syracuseStep 2802883 = 4204325) B4204325
theorem B4490435 : Blo 1659529 4490435 := bstep (se 1 (by rfl) ⟨3367826, by rfl⟩ : syracuseStep 4490435 = 6735653) B6735653
theorem B40412357 : Blo 1659529 40412357 := bstep (se 4 (by rfl) ⟨3788658, by rfl⟩ : syracuseStep 40412357 = 7577317) B7577317
theorem B2491601 : Blo 1659529 2491601 := bstep (se 2 (by rfl) ⟨934350, by rfl⟩ : syracuseStep 2491601 = 1868701) B1868701
theorem B2491619 : Blo 1659529 2491619 := bstep (se 1 (by rfl) ⟨1868714, by rfl⟩ : syracuseStep 2491619 = 3737429) B3737429
theorem B3736817 : Blo 1659529 3736817 := bstep (se 2 (by rfl) ⟨1401306, by rfl⟩ : syracuseStep 3736817 = 2802613) B2802613
theorem B1869043 : Blo 1659529 1869043 := bstep (se 1 (by rfl) ⟨1401782, by rfl⟩ : syracuseStep 1869043 = 2803565) B2803565
theorem B2491649 : Blo 1659529 2491649 := bstep (se 2 (by rfl) ⟨934368, by rfl⟩ : syracuseStep 2491649 = 1868737) B1868737
theorem B3736835 : Blo 1659529 3736835 := bstep (se 1 (by rfl) ⟨2802626, by rfl⟩ : syracuseStep 3736835 = 5605253) B5605253
theorem B2491667 : Blo 1659529 2491667 := bstep (se 1 (by rfl) ⟨1868750, by rfl⟩ : syracuseStep 2491667 = 3737501) B3737501
theorem B2491697 : Blo 1659529 2491697 := bstep (se 2 (by rfl) ⟨934386, by rfl⟩ : syracuseStep 2491697 = 1868773) B1868773
theorem B2491715 : Blo 1659529 2491715 := bstep (se 1 (by rfl) ⟨1868786, by rfl⟩ : syracuseStep 2491715 = 3737573) B3737573
theorem B2803025 : Blo 1659529 2803025 := bstep (se 2 (by rfl) ⟨1051134, by rfl⟩ : syracuseStep 2803025 = 2102269) B2102269
theorem B2491745 : Blo 1659529 2491745 := bstep (se 2 (by rfl) ⟨934404, by rfl⟩ : syracuseStep 2491745 = 1868809) B1868809
theorem B5317987 : Blo 1659529 5317987 := bstep (se 1 (by rfl) ⟨3988490, by rfl⟩ : syracuseStep 5317987 = 7976981) B7976981
theorem B3990883 : Blo 1659529 3990883 := bstep (se 1 (by rfl) ⟨2993162, by rfl⟩ : syracuseStep 3990883 = 5986325) B5986325
theorem B2491763 : Blo 1659529 2491763 := bstep (se 1 (by rfl) ⟨1868822, by rfl⟩ : syracuseStep 2491763 = 3737645) B3737645
theorem B1869187 : Blo 1659529 1869187 := bstep (se 1 (by rfl) ⟨1401890, by rfl⟩ : syracuseStep 1869187 = 2803781) B2803781
theorem B2991505 : Blo 1659529 2991505 := bstep (se 2 (by rfl) ⟨1121814, by rfl⟩ : syracuseStep 2991505 = 2243629) B2243629
theorem B2491793 : Blo 1659529 2491793 := bstep (se 2 (by rfl) ⟨934422, by rfl⟩ : syracuseStep 2491793 = 1868845) B1868845
theorem B2491811 : Blo 1659529 2491811 := bstep (se 1 (by rfl) ⟨1868858, by rfl⟩ : syracuseStep 2491811 = 3737717) B3737717
theorem B2491841 : Blo 1659529 2491841 := bstep (se 2 (by rfl) ⟨934440, by rfl⟩ : syracuseStep 2491841 = 1868881) B1868881
theorem B4203971 : Blo 1659529 4203971 := bstep (se 1 (by rfl) ⟨3152978, by rfl⟩ : syracuseStep 4203971 = 6305957) B6305957
theorem B3990979 : Blo 1659529 3990979 := bstep (se 1 (by rfl) ⟨2993234, by rfl⟩ : syracuseStep 3990979 = 5986469) B5986469
theorem B11363789 : Blo 1659529 11363789 := bstep (se 3 (by rfl) ⟨2130710, by rfl⟩ : syracuseStep 11363789 = 4261421) B4261421
theorem B2803153 : Blo 1659529 2803153 := bstep (se 2 (by rfl) ⟨1051182, by rfl⟩ : syracuseStep 2803153 = 2102365) B2102365
theorem B2491859 : Blo 1659529 2491859 := bstep (se 1 (by rfl) ⟨1868894, by rfl⟩ : syracuseStep 2491859 = 3737789) B3737789
theorem B2491889 : Blo 1659529 2491889 := bstep (se 2 (by rfl) ⟨934458, by rfl⟩ : syracuseStep 2491889 = 1868917) B1868917
theorem B2803187 : Blo 1659529 2803187 := bstep (se 1 (by rfl) ⟨2102390, by rfl⟩ : syracuseStep 2803187 = 4204781) B4204781
theorem B2491907 : Blo 1659529 2491907 := bstep (se 1 (by rfl) ⟨1868930, by rfl⟩ : syracuseStep 2491907 = 3737861) B3737861
theorem B4548109 : Blo 1659529 4548109 := bstep (se 3 (by rfl) ⟨852770, by rfl⟩ : syracuseStep 4548109 = 1705541) B1705541
theorem B3737105 : Blo 1659529 3737105 := bstep (se 2 (by rfl) ⟨1401414, by rfl⟩ : syracuseStep 3737105 = 2802829) B2802829
theorem B2491937 : Blo 1659529 2491937 := bstep (se 2 (by rfl) ⟨934476, by rfl⟩ : syracuseStep 2491937 = 1868953) B1868953
theorem B3737123 : Blo 1659529 3737123 := bstep (se 1 (by rfl) ⟨2802842, by rfl⟩ : syracuseStep 3737123 = 5605685) B5605685
theorem B2491955 : Blo 1659529 2491955 := bstep (se 1 (by rfl) ⟨1868966, by rfl⟩ : syracuseStep 2491955 = 3737933) B3737933
theorem B10643021 : Blo 1659529 10643021 := bstep (se 3 (by rfl) ⟨1995566, by rfl⟩ : syracuseStep 10643021 = 3991133) B3991133
theorem B2491985 : Blo 1659529 2491985 := bstep (se 2 (by rfl) ⟨934494, by rfl⟩ : syracuseStep 2491985 = 1868989) B1868989
theorem B8636003 : Blo 1659529 8636003 := bstep (se 1 (by rfl) ⟨6477002, by rfl⟩ : syracuseStep 8636003 = 12954005) B12954005
theorem B2492003 : Blo 1659529 2492003 := bstep (se 1 (by rfl) ⟨1869002, by rfl⟩ : syracuseStep 2492003 = 3738005) B3738005
theorem B2803315 : Blo 1659529 2803315 := bstep (se 1 (by rfl) ⟨2102486, by rfl⟩ : syracuseStep 2803315 = 4204973) B4204973
theorem B2492033 : Blo 1659529 2492033 := bstep (se 2 (by rfl) ⟨934512, by rfl⟩ : syracuseStep 2492033 = 1869025) B1869025
theorem B4204163 : Blo 1659529 4204163 := bstep (se 1 (by rfl) ⟨3153122, by rfl⟩ : syracuseStep 4204163 = 6306245) B6306245
theorem B2492051 : Blo 1659529 2492051 := bstep (se 1 (by rfl) ⟨1869038, by rfl⟩ : syracuseStep 2492051 = 3738077) B3738077
theorem B5605037 : Blo 1659529 5605037 := bstep (se 3 (by rfl) ⟨1050944, by rfl⟩ : syracuseStep 5605037 = 2101889) B2101889
theorem B2492081 : Blo 1659529 2492081 := bstep (se 2 (by rfl) ⟨934530, by rfl⟩ : syracuseStep 2492081 = 1869061) B1869061
theorem B2492099 : Blo 1659529 2492099 := bstep (se 1 (by rfl) ⟨1869074, by rfl⟩ : syracuseStep 2492099 = 3738149) B3738149
theorem B4261585 : Blo 1659529 4261585 := bstep (se 2 (by rfl) ⟨1598094, by rfl⟩ : syracuseStep 4261585 = 3196189) B3196189
theorem B2492129 : Blo 1659529 2492129 := bstep (se 2 (by rfl) ⟨934548, by rfl⟩ : syracuseStep 2492129 = 1869097) B1869097
theorem B5605091 : Blo 1659529 5605091 := bstep (se 1 (by rfl) ⟨4203818, by rfl⟩ : syracuseStep 5605091 = 8407637) B8407637
theorem B4728557 : Blo 1659529 4728557 := bstep (se 3 (by rfl) ⟨886604, by rfl⟩ : syracuseStep 4728557 = 1773209) B1773209
theorem B2492147 : Blo 1659529 2492147 := bstep (se 1 (by rfl) ⟨1869110, by rfl⟩ : syracuseStep 2492147 = 3738221) B3738221
theorem B2803457 : Blo 1659529 2803457 := bstep (se 2 (by rfl) ⟨1051296, by rfl⟩ : syracuseStep 2803457 = 2102593) B2102593
theorem B3196675 : Blo 1659529 3196675 := bstep (se 1 (by rfl) ⟨2397506, by rfl⟩ : syracuseStep 3196675 = 4795013) B4795013
theorem B15140621 : Blo 1659529 15140621 := bstep (se 3 (by rfl) ⟨2838866, by rfl⟩ : syracuseStep 15140621 = 5677733) B5677733
theorem B14190349 : Blo 1659529 14190349 := bstep (se 3 (by rfl) ⟨2660690, by rfl⟩ : syracuseStep 14190349 = 5321381) B5321381
theorem B2492177 : Blo 1659529 2492177 := bstep (se 2 (by rfl) ⟨934566, by rfl⟩ : syracuseStep 2492177 = 1869133) B1869133
theorem B5318435 : Blo 1659529 5318435 := bstep (se 1 (by rfl) ⟨3988826, by rfl⟩ : syracuseStep 5318435 = 7977653) B7977653
theorem B2492195 : Blo 1659529 2492195 := bstep (se 1 (by rfl) ⟨1869146, by rfl⟩ : syracuseStep 2492195 = 3738293) B3738293
theorem B3737393 : Blo 1659529 3737393 := bstep (se 2 (by rfl) ⟨1401522, by rfl⟩ : syracuseStep 3737393 = 2803045) B2803045
theorem B2492225 : Blo 1659529 2492225 := bstep (se 2 (by rfl) ⟨934584, by rfl⟩ : syracuseStep 2492225 = 1869169) B1869169
theorem B3737411 : Blo 1659529 3737411 := bstep (se 1 (by rfl) ⟨2803058, by rfl⟩ : syracuseStep 3737411 = 5606117) B5606117
theorem B4491085 : Blo 1659529 4491085 := bstep (se 3 (by rfl) ⟨842078, by rfl⟩ : syracuseStep 4491085 = 1684157) B1684157
theorem B2492243 : Blo 1659529 2492243 := bstep (se 1 (by rfl) ⟨1869182, by rfl⟩ : syracuseStep 2492243 = 3738365) B3738365
theorem B2492273 : Blo 1659529 2492273 := bstep (se 2 (by rfl) ⟨934602, by rfl⟩ : syracuseStep 2492273 = 1869205) B1869205
theorem B2803585 : Blo 1659529 2803585 := bstep (se 2 (by rfl) ⟨1051344, by rfl⟩ : syracuseStep 2803585 = 2102689) B2102689
theorem B2492291 : Blo 1659529 2492291 := bstep (se 1 (by rfl) ⟨1869218, by rfl⟩ : syracuseStep 2492291 = 3738437) B3738437
theorem B4728739 : Blo 1659529 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B2803619 : Blo 1659529 2803619 := bstep (se 1 (by rfl) ⟨2102714, by rfl⟩ : syracuseStep 2803619 = 4205429) B4205429
theorem B2992067 : Blo 1659529 2992067 := bstep (se 1 (by rfl) ⟨2244050, by rfl⟩ : syracuseStep 2992067 = 4488101) B4488101
theorem B8406989 : Blo 1659529 8406989 := bstep (se 3 (by rfl) ⟨1576310, by rfl⟩ : syracuseStep 8406989 = 3152621) B3152621
theorem B45459427 : Blo 1659529 45459427 := bstep (se 1 (by rfl) ⟨34094570, by rfl⟩ : syracuseStep 45459427 = 68189141) B68189141
theorem B6391793 : Blo 1659529 6391793 := bstep (se 2 (by rfl) ⟨2396922, by rfl⟩ : syracuseStep 6391793 = 4793845) B4793845
theorem B5605361 : Blo 1659529 5605361 := bstep (se 2 (by rfl) ⟨2102010, by rfl⟩ : syracuseStep 5605361 = 4204021) B4204021
theorem B9095203 : Blo 1659529 9095203 := bstep (se 1 (by rfl) ⟨6821402, by rfl⟩ : syracuseStep 9095203 = 13642805) B13642805
theorem B2803747 : Blo 1659529 2803747 := bstep (se 1 (by rfl) ⟨2102810, by rfl⟩ : syracuseStep 2803747 = 4205621) B4205621
theorem B19163189 : Blo 1659529 19163189 := bstep (se 5 (by rfl) ⟨898274, by rfl⟩ : syracuseStep 19163189 = 1796549) B1796549
theorem B2525251 : Blo 1659529 2525251 := bstep (se 1 (by rfl) ⟨1893938, by rfl⟩ : syracuseStep 2525251 = 3787877) B3787877
theorem B3737681 : Blo 1659529 3737681 := bstep (se 2 (by rfl) ⟨1401630, by rfl⟩ : syracuseStep 3737681 = 2803261) B2803261
theorem B3737699 : Blo 1659529 3737699 := bstep (se 1 (by rfl) ⟨2803274, by rfl⟩ : syracuseStep 3737699 = 5606549) B5606549
theorem B6301901 : Blo 1659529 6301901 := bstep (se 3 (by rfl) ⟨1181606, by rfl⟩ : syracuseStep 6301901 = 2363213) B2363213
theorem B3737969 : Blo 1659529 3737969 := bstep (se 2 (by rfl) ⟨1401738, by rfl⟩ : syracuseStep 3737969 = 2803477) B2803477
theorem B2525555 : Blo 1659529 2525555 := bstep (se 1 (by rfl) ⟨1894166, by rfl⟩ : syracuseStep 2525555 = 3788333) B3788333
theorem B3737987 : Blo 1659529 3737987 := bstep (se 1 (by rfl) ⟨2803490, by rfl⟩ : syracuseStep 3737987 = 5606981) B5606981
theorem B4729229 : Blo 1659529 4729229 := bstep (se 3 (by rfl) ⟨886730, by rfl⟩ : syracuseStep 4729229 = 1773461) B1773461
theorem B5605901 : Blo 1659529 5605901 := bstep (se 3 (by rfl) ⟨1051106, by rfl⟩ : syracuseStep 5605901 = 2102213) B2102213
theorem B4205105 : Blo 1659529 4205105 := bstep (se 2 (by rfl) ⟨1576914, by rfl⟩ : syracuseStep 4205105 = 3153829) B3153829
theorem B5605955 : Blo 1659529 5605955 := bstep (se 1 (by rfl) ⟨4204466, by rfl⟩ : syracuseStep 5605955 = 8408933) B8408933
theorem B4205155 : Blo 1659529 4205155 := bstep (se 1 (by rfl) ⟨3153866, by rfl⟩ : syracuseStep 4205155 = 6307733) B6307733
theorem B3738257 : Blo 1659529 3738257 := bstep (se 2 (by rfl) ⟨1401846, by rfl⟩ : syracuseStep 3738257 = 2803693) B2803693
theorem B3738275 : Blo 1659529 3738275 := bstep (se 1 (by rfl) ⟨2803706, by rfl⟩ : syracuseStep 3738275 = 5607413) B5607413
theorem B4205297 : Blo 1659529 4205297 := bstep (se 2 (by rfl) ⟨1576986, by rfl⟩ : syracuseStep 4205297 = 3153973) B3153973
theorem B5606225 : Blo 1659529 5606225 := bstep (se 2 (by rfl) ⟨2102334, by rfl⟩ : syracuseStep 5606225 = 4204669) B4204669
theorem B9456497 : Blo 1659529 9456497 := bstep (se 2 (by rfl) ⟨3546186, by rfl⟩ : syracuseStep 9456497 = 7092373) B7092373
theorem B2993041 : Blo 1659529 2993041 := bstep (se 2 (by rfl) ⟨1122390, by rfl⟩ : syracuseStep 2993041 = 2244781) B2244781
theorem B7089059 : Blo 1659529 7089059 := bstep (se 1 (by rfl) ⟨5316794, by rfl⟩ : syracuseStep 7089059 = 10633589) B10633589
theorem B2993105 : Blo 1659529 2993105 := bstep (se 2 (by rfl) ⟨1122414, by rfl⟩ : syracuseStep 2993105 = 2244829) B2244829
theorem B5319665 : Blo 1659529 5319665 := bstep (se 2 (by rfl) ⟨1994874, by rfl⟩ : syracuseStep 5319665 = 3989749) B3989749
theorem B14191685 : Blo 1659529 14191685 := bstep (se 4 (by rfl) ⟨1330470, by rfl⟩ : syracuseStep 14191685 = 2660941) B2660941
theorem B4041827 : Blo 1659529 4041827 := bstep (se 1 (by rfl) ⟨3031370, by rfl⟩ : syracuseStep 4041827 = 6062741) B6062741
theorem B15150221 : Blo 1659529 15150221 := bstep (se 3 (by rfl) ⟨2840666, by rfl⟩ : syracuseStep 15150221 = 5681333) B5681333
theorem B1772803 : Blo 1659529 1772803 := bstep (se 1 (by rfl) ⟨1329602, by rfl⟩ : syracuseStep 1772803 = 2659205) B2659205
theorem B5606765 : Blo 1659529 5606765 := bstep (se 3 (by rfl) ⟨1051268, by rfl⟩ : syracuseStep 5606765 = 2102537) B2102537
theorem B5606819 : Blo 1659529 5606819 := bstep (se 1 (by rfl) ⟨4205114, by rfl⟩ : syracuseStep 5606819 = 8410229) B8410229
theorem B2100755 : Blo 1659529 2100755 := bstep (se 1 (by rfl) ⟨1575566, by rfl⟩ : syracuseStep 2100755 = 3151133) B3151133
theorem B4730413 : Blo 1659529 4730413 := bstep (se 3 (by rfl) ⟨886952, by rfl⟩ : syracuseStep 4730413 = 1773905) B1773905
theorem B12611213 : Blo 1659529 12611213 := bstep (se 3 (by rfl) ⟨2364602, by rfl⟩ : syracuseStep 12611213 = 4729205) B4729205
theorem B13471373 : Blo 1659529 13471373 := bstep (se 3 (by rfl) ⟨2525882, by rfl⟩ : syracuseStep 13471373 = 5051765) B5051765
theorem B2879153 : Blo 1659529 2879153 := bstep (se 2 (by rfl) ⟨1079682, by rfl⟩ : syracuseStep 2879153 = 2159365) B2159365
theorem B5607089 : Blo 1659529 5607089 := bstep (se 2 (by rfl) ⟨2102658, by rfl⟩ : syracuseStep 5607089 = 4205317) B4205317
theorem B5115683 : Blo 1659529 5115683 := bstep (se 1 (by rfl) ⟨3836762, by rfl⟩ : syracuseStep 5115683 = 7673525) B7673525
theorem B2363185 : Blo 1659529 2363185 := bstep (se 2 (by rfl) ⟨886194, by rfl⟩ : syracuseStep 2363185 = 1772389) B1772389
theorem B5984077 : Blo 1659529 5984077 := bstep (se 3 (by rfl) ⟨1122014, by rfl⟩ : syracuseStep 5984077 = 2244029) B2244029
theorem B5320561 : Blo 1659529 5320561 := bstep (se 2 (by rfl) ⟨1995210, by rfl⟩ : syracuseStep 5320561 = 3990421) B3990421
theorem B15150989 : Blo 1659529 15150989 := bstep (se 3 (by rfl) ⟨2840810, by rfl⟩ : syracuseStep 15150989 = 5681621) B5681621
theorem B2363521 : Blo 1659529 2363521 := bstep (se 2 (by rfl) ⟨886320, by rfl⟩ : syracuseStep 2363521 = 1772641) B1772641
theorem B8974469 : Blo 1659529 8974469 := bstep (se 4 (by rfl) ⟨841356, by rfl⟩ : syracuseStep 8974469 = 1682713) B1682713
theorem B6828209 : Blo 1659529 6828209 := bstep (se 2 (by rfl) ⟨2560578, by rfl⟩ : syracuseStep 6828209 = 5121157) B5121157
theorem B5607629 : Blo 1659529 5607629 := bstep (se 3 (by rfl) ⟨1051430, by rfl⟩ : syracuseStep 5607629 = 2102861) B2102861
theorem B2101459 : Blo 1659529 2101459 := bstep (se 1 (by rfl) ⟨1576094, by rfl⟩ : syracuseStep 2101459 = 3152189) B3152189
theorem B6304013 : Blo 1659529 6304013 := bstep (se 3 (by rfl) ⟨1182002, by rfl⟩ : syracuseStep 6304013 = 2364005) B2364005
theorem B9457955 : Blo 1659529 9457955 := bstep (se 1 (by rfl) ⟨7093466, by rfl⟩ : syracuseStep 9457955 = 14186933) B14186933
theorem B2101555 : Blo 1659529 2101555 := bstep (se 1 (by rfl) ⟨1576166, by rfl⟩ : syracuseStep 2101555 = 3152333) B3152333
theorem B17953265 : Blo 1659529 17953265 := bstep (se 2 (by rfl) ⟨6732474, by rfl⟩ : syracuseStep 17953265 = 13464949) B13464949
theorem B1774067 : Blo 1659529 1774067 := bstep (se 1 (by rfl) ⟨1330550, by rfl⟩ : syracuseStep 1774067 = 2661101) B2661101
theorem B5395025 : Blo 1659529 5395025 := bstep (se 2 (by rfl) ⟨2023134, by rfl⟩ : syracuseStep 5395025 = 4046269) B4046269
theorem B1659539 : Blo 1659529 1659539 := bstep (se 1 (by rfl) ⟨1244654, by rfl⟩ : syracuseStep 1659539 = 2489309) B2489309
theorem B1659555 : Blo 1659529 1659555 := bstep (se 1 (by rfl) ⟨1244666, by rfl⟩ : syracuseStep 1659555 = 2489333) B2489333
theorem B1659571 : Blo 1659529 1659571 := bstep (se 1 (by rfl) ⟨1244678, by rfl⟩ : syracuseStep 1659571 = 2489357) B2489357
theorem B1659587 : Blo 1659529 1659587 := bstep (se 1 (by rfl) ⟨1244690, by rfl⟩ : syracuseStep 1659587 = 2489381) B2489381
theorem B2659025 : Blo 1659529 2659025 := bstep (se 2 (by rfl) ⟨997134, by rfl⟩ : syracuseStep 2659025 = 1994269) B1994269
theorem B2364113 : Blo 1659529 2364113 := bstep (se 2 (by rfl) ⟨886542, by rfl⟩ : syracuseStep 2364113 = 1773085) B1773085
theorem B1659603 : Blo 1659529 1659603 := bstep (se 1 (by rfl) ⟨1244702, by rfl⟩ : syracuseStep 1659603 = 2489405) B2489405
theorem B1659619 : Blo 1659529 1659619 := bstep (se 1 (by rfl) ⟨1244714, by rfl⟩ : syracuseStep 1659619 = 2489429) B2489429
theorem B1659635 : Blo 1659529 1659635 := bstep (se 1 (by rfl) ⟨1244726, by rfl⟩ : syracuseStep 1659635 = 2489453) B2489453
theorem B1659651 : Blo 1659529 1659651 := bstep (se 1 (by rfl) ⟨1244738, by rfl⟩ : syracuseStep 1659651 = 2489477) B2489477
theorem B1659667 : Blo 1659529 1659667 := bstep (se 1 (by rfl) ⟨1244750, by rfl⟩ : syracuseStep 1659667 = 2489501) B2489501
theorem B1659683 : Blo 1659529 1659683 := bstep (se 1 (by rfl) ⟨1244762, by rfl⟩ : syracuseStep 1659683 = 2489525) B2489525
theorem B2102051 : Blo 1659529 2102051 := bstep (se 1 (by rfl) ⟨1576538, by rfl⟩ : syracuseStep 2102051 = 3153077) B3153077
theorem B4485937 : Blo 1659529 4485937 := bstep (se 2 (by rfl) ⟨1682226, by rfl⟩ : syracuseStep 4485937 = 3364453) B3364453
theorem B1659699 : Blo 1659529 1659699 := bstep (se 1 (by rfl) ⟨1244774, by rfl⟩ : syracuseStep 1659699 = 2489549) B2489549
theorem B8409905 : Blo 1659529 8409905 := bstep (se 2 (by rfl) ⟨3153714, by rfl⟩ : syracuseStep 8409905 = 6307429) B6307429
theorem B1659715 : Blo 1659529 1659715 := bstep (se 1 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 1659715 = 2489573) B2489573
theorem B2659153 : Blo 1659529 2659153 := bstep (se 2 (by rfl) ⟨997182, by rfl⟩ : syracuseStep 2659153 = 1994365) B1994365
theorem B1659731 : Blo 1659529 1659731 := bstep (se 1 (by rfl) ⟨1244798, by rfl⟩ : syracuseStep 1659731 = 2489597) B2489597
theorem B1659747 : Blo 1659529 1659747 := bstep (se 1 (by rfl) ⟨1244810, by rfl⟩ : syracuseStep 1659747 = 2489621) B2489621
theorem B1659763 : Blo 1659529 1659763 := bstep (se 1 (by rfl) ⟨1244822, by rfl⟩ : syracuseStep 1659763 = 2489645) B2489645
theorem B1659779 : Blo 1659529 1659779 := bstep (se 1 (by rfl) ⟨1244834, by rfl⟩ : syracuseStep 1659779 = 2489669) B2489669
theorem B8401805 : Blo 1659529 8401805 := bstep (se 3 (by rfl) ⟨1575338, by rfl⟩ : syracuseStep 8401805 = 3150677) B3150677
theorem B1659795 : Blo 1659529 1659795 := bstep (se 1 (by rfl) ⟨1244846, by rfl⟩ : syracuseStep 1659795 = 2489693) B2489693
theorem B1659811 : Blo 1659529 1659811 := bstep (se 1 (by rfl) ⟨1244858, by rfl⟩ : syracuseStep 1659811 = 2489717) B2489717
theorem B1659827 : Blo 1659529 1659827 := bstep (se 1 (by rfl) ⟨1244870, by rfl⟩ : syracuseStep 1659827 = 2489741) B2489741
theorem B1659843 : Blo 1659529 1659843 := bstep (se 1 (by rfl) ⟨1244882, by rfl⟩ : syracuseStep 1659843 = 2489765) B2489765
theorem B1659859 : Blo 1659529 1659859 := bstep (se 1 (by rfl) ⟨1244894, by rfl⟩ : syracuseStep 1659859 = 2489789) B2489789
theorem B1659875 : Blo 1659529 1659875 := bstep (se 1 (by rfl) ⟨1244906, by rfl⟩ : syracuseStep 1659875 = 2489813) B2489813
theorem B7975921 : Blo 1659529 7975921 := bstep (se 2 (by rfl) ⟨2990970, by rfl⟩ : syracuseStep 7975921 = 5981941) B5981941
theorem B1659891 : Blo 1659529 1659891 := bstep (se 1 (by rfl) ⟨1244918, by rfl⟩ : syracuseStep 1659891 = 2489837) B2489837
theorem B1659907 : Blo 1659529 1659907 := bstep (se 1 (by rfl) ⟨1244930, by rfl⟩ : syracuseStep 1659907 = 2489861) B2489861
theorem B1659923 : Blo 1659529 1659923 := bstep (se 1 (by rfl) ⟨1244942, by rfl⟩ : syracuseStep 1659923 = 2489885) B2489885
theorem B1659939 : Blo 1659529 1659939 := bstep (se 1 (by rfl) ⟨1244954, by rfl⟩ : syracuseStep 1659939 = 2489909) B2489909
theorem B6304817 : Blo 1659529 6304817 := bstep (se 2 (by rfl) ⟨2364306, by rfl⟩ : syracuseStep 6304817 = 4728613) B4728613
theorem B1659955 : Blo 1659529 1659955 := bstep (se 1 (by rfl) ⟨1244966, by rfl⟩ : syracuseStep 1659955 = 2489933) B2489933
theorem B1659971 : Blo 1659529 1659971 := bstep (se 1 (by rfl) ⟨1244978, by rfl⟩ : syracuseStep 1659971 = 2489957) B2489957
theorem B3839057 : Blo 1659529 3839057 := bstep (se 2 (by rfl) ⟨1439646, by rfl⟩ : syracuseStep 3839057 = 2879293) B2879293
theorem B1659987 : Blo 1659529 1659987 := bstep (se 1 (by rfl) ⟨1244990, by rfl⟩ : syracuseStep 1659987 = 2489981) B2489981
theorem B1660003 : Blo 1659529 1660003 := bstep (se 1 (by rfl) ⟨1245002, by rfl⟩ : syracuseStep 1660003 = 2490005) B2490005
theorem B1660019 : Blo 1659529 1660019 := bstep (se 1 (by rfl) ⟨1245014, by rfl⟩ : syracuseStep 1660019 = 2490029) B2490029
theorem B1660035 : Blo 1659529 1660035 := bstep (se 1 (by rfl) ⟨1245026, by rfl⟩ : syracuseStep 1660035 = 2490053) B2490053
theorem B1660051 : Blo 1659529 1660051 := bstep (se 1 (by rfl) ⟨1245038, by rfl⟩ : syracuseStep 1660051 = 2490077) B2490077
theorem B8516771 : Blo 1659529 8516771 := bstep (se 1 (by rfl) ⟨6387578, by rfl⟩ : syracuseStep 8516771 = 12775157) B12775157
theorem B1660067 : Blo 1659529 1660067 := bstep (se 1 (by rfl) ⟨1245050, by rfl⟩ : syracuseStep 1660067 = 2490101) B2490101
theorem B1660083 : Blo 1659529 1660083 := bstep (se 1 (by rfl) ⟨1245062, by rfl⟩ : syracuseStep 1660083 = 2490125) B2490125
theorem B1660099 : Blo 1659529 1660099 := bstep (se 1 (by rfl) ⟨1245074, by rfl⟩ : syracuseStep 1660099 = 2490149) B2490149
theorem B3151057 : Blo 1659529 3151057 := bstep (se 2 (by rfl) ⟨1181646, by rfl⟩ : syracuseStep 3151057 = 2363293) B2363293
theorem B1660115 : Blo 1659529 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B1660131 : Blo 1659529 1660131 := bstep (se 1 (by rfl) ⟨1245098, by rfl⟩ : syracuseStep 1660131 = 2490197) B2490197
theorem B2364643 : Blo 1659529 2364643 := bstep (se 1 (by rfl) ⟨1773482, by rfl⟩ : syracuseStep 2364643 = 3546965) B3546965
theorem B1660147 : Blo 1659529 1660147 := bstep (se 1 (by rfl) ⟨1245110, by rfl⟩ : syracuseStep 1660147 = 2490221) B2490221
theorem B1660163 : Blo 1659529 1660163 := bstep (se 1 (by rfl) ⟨1245122, by rfl⟩ : syracuseStep 1660163 = 2490245) B2490245
theorem B9458957 : Blo 1659529 9458957 := bstep (se 3 (by rfl) ⟨1773554, by rfl⟩ : syracuseStep 9458957 = 3547109) B3547109
theorem B1660179 : Blo 1659529 1660179 := bstep (se 1 (by rfl) ⟨1245134, by rfl⟩ : syracuseStep 1660179 = 2490269) B2490269
theorem B42554645 : Blo 1659529 42554645 := bstep (se 6 (by rfl) ⟨997374, by rfl⟩ : syracuseStep 42554645 = 1994749) B1994749
theorem B1660195 : Blo 1659529 1660195 := bstep (se 1 (by rfl) ⟨1245146, by rfl⟩ : syracuseStep 1660195 = 2490293) B2490293
theorem B1660211 : Blo 1659529 1660211 := bstep (se 1 (by rfl) ⟨1245158, by rfl⟩ : syracuseStep 1660211 = 2490317) B2490317
theorem B1660227 : Blo 1659529 1660227 := bstep (se 1 (by rfl) ⟨1245170, by rfl⟩ : syracuseStep 1660227 = 2490341) B2490341
theorem B1660243 : Blo 1659529 1660243 := bstep (se 1 (by rfl) ⟨1245182, by rfl⟩ : syracuseStep 1660243 = 2490365) B2490365
theorem B1660259 : Blo 1659529 1660259 := bstep (se 1 (by rfl) ⟨1245194, by rfl⟩ : syracuseStep 1660259 = 2490389) B2490389
theorem B7673201 : Blo 1659529 7673201 := bstep (se 2 (by rfl) ⟨2877450, by rfl⟩ : syracuseStep 7673201 = 5754901) B5754901
theorem B3151217 : Blo 1659529 3151217 := bstep (se 2 (by rfl) ⟨1181706, by rfl⟩ : syracuseStep 3151217 = 2363413) B2363413
theorem B1660275 : Blo 1659529 1660275 := bstep (se 1 (by rfl) ⟨1245206, by rfl⟩ : syracuseStep 1660275 = 2490413) B2490413
theorem B1660291 : Blo 1659529 1660291 := bstep (se 1 (by rfl) ⟨1245218, by rfl⟩ : syracuseStep 1660291 = 2490437) B2490437
theorem B5322125 : Blo 1659529 5322125 := bstep (se 3 (by rfl) ⟨997898, by rfl⟩ : syracuseStep 5322125 = 1995797) B1995797
theorem B1660307 : Blo 1659529 1660307 := bstep (se 1 (by rfl) ⟨1245230, by rfl⟩ : syracuseStep 1660307 = 2490461) B2490461
theorem B1660323 : Blo 1659529 1660323 := bstep (se 1 (by rfl) ⟨1245242, by rfl⟩ : syracuseStep 1660323 = 2490485) B2490485
theorem B1660339 : Blo 1659529 1660339 := bstep (se 1 (by rfl) ⟨1245254, by rfl⟩ : syracuseStep 1660339 = 2490509) B2490509
theorem B1660355 : Blo 1659529 1660355 := bstep (se 1 (by rfl) ⟨1245266, by rfl⟩ : syracuseStep 1660355 = 2490533) B2490533
theorem B1660371 : Blo 1659529 1660371 := bstep (se 1 (by rfl) ⟨1245278, by rfl⟩ : syracuseStep 1660371 = 2490557) B2490557
theorem B1660387 : Blo 1659529 1660387 := bstep (se 1 (by rfl) ⟨1245290, by rfl⟩ : syracuseStep 1660387 = 2490581) B2490581
theorem B5682659 : Blo 1659529 5682659 := bstep (se 1 (by rfl) ⟨4261994, by rfl⟩ : syracuseStep 5682659 = 8523989) B8523989
theorem B2102755 : Blo 1659529 2102755 := bstep (se 1 (by rfl) ⟨1577066, by rfl⟩ : syracuseStep 2102755 = 3154133) B3154133
theorem B1660403 : Blo 1659529 1660403 := bstep (se 1 (by rfl) ⟨1245302, by rfl⟩ : syracuseStep 1660403 = 2490605) B2490605
theorem B1660419 : Blo 1659529 1660419 := bstep (se 1 (by rfl) ⟨1245314, by rfl⟩ : syracuseStep 1660419 = 2490629) B2490629
theorem B1660435 : Blo 1659529 1660435 := bstep (se 1 (by rfl) ⟨1245326, by rfl⟩ : syracuseStep 1660435 = 2490653) B2490653
theorem B1660451 : Blo 1659529 1660451 := bstep (se 1 (by rfl) ⟨1245338, by rfl⟩ : syracuseStep 1660451 = 2490677) B2490677
theorem B1660467 : Blo 1659529 1660467 := bstep (se 1 (by rfl) ⟨1245350, by rfl⟩ : syracuseStep 1660467 = 2490701) B2490701
theorem B2364979 : Blo 1659529 2364979 := bstep (se 1 (by rfl) ⟨1773734, by rfl⟩ : syracuseStep 2364979 = 3547469) B3547469
theorem B1660483 : Blo 1659529 1660483 := bstep (se 1 (by rfl) ⟨1245362, by rfl⟩ : syracuseStep 1660483 = 2490725) B2490725
theorem B2102851 : Blo 1659529 2102851 := bstep (se 1 (by rfl) ⟨1577138, by rfl⟩ : syracuseStep 2102851 = 3154277) B3154277
theorem B1660499 : Blo 1659529 1660499 := bstep (se 1 (by rfl) ⟨1245374, by rfl⟩ : syracuseStep 1660499 = 2490749) B2490749
theorem B1660515 : Blo 1659529 1660515 := bstep (se 1 (by rfl) ⟨1245386, by rfl⟩ : syracuseStep 1660515 = 2490773) B2490773
theorem B1660531 : Blo 1659529 1660531 := bstep (se 1 (by rfl) ⟨1245398, by rfl⟩ : syracuseStep 1660531 = 2490797) B2490797
theorem B1660547 : Blo 1659529 1660547 := bstep (se 1 (by rfl) ⟨1245410, by rfl⟩ : syracuseStep 1660547 = 2490821) B2490821
theorem B1660563 : Blo 1659529 1660563 := bstep (se 1 (by rfl) ⟨1245422, by rfl⟩ : syracuseStep 1660563 = 2490845) B2490845
theorem B1660579 : Blo 1659529 1660579 := bstep (se 1 (by rfl) ⟨1245434, by rfl⟩ : syracuseStep 1660579 = 2490869) B2490869
theorem B1660595 : Blo 1659529 1660595 := bstep (se 1 (by rfl) ⟨1245446, by rfl⟩ : syracuseStep 1660595 = 2490893) B2490893
theorem B1660611 : Blo 1659529 1660611 := bstep (se 1 (by rfl) ⟨1245458, by rfl⟩ : syracuseStep 1660611 = 2490917) B2490917
theorem B6305485 : Blo 1659529 6305485 := bstep (se 3 (by rfl) ⟨1182278, by rfl⟩ : syracuseStep 6305485 = 2364557) B2364557
theorem B1660627 : Blo 1659529 1660627 := bstep (se 1 (by rfl) ⟨1245470, by rfl⟩ : syracuseStep 1660627 = 2490941) B2490941
theorem B1660643 : Blo 1659529 1660643 := bstep (se 1 (by rfl) ⟨1245482, by rfl⟩ : syracuseStep 1660643 = 2490965) B2490965
theorem B1660659 : Blo 1659529 1660659 := bstep (se 1 (by rfl) ⟨1245494, by rfl⟩ : syracuseStep 1660659 = 2490989) B2490989
theorem B3151619 : Blo 1659529 3151619 := bstep (se 1 (by rfl) ⟨2363714, by rfl⟩ : syracuseStep 3151619 = 4727429) B4727429
theorem B1660675 : Blo 1659529 1660675 := bstep (se 1 (by rfl) ⟨1245506, by rfl⟩ : syracuseStep 1660675 = 2491013) B2491013
theorem B5601041 : Blo 1659529 5601041 := bstep (se 2 (by rfl) ⟨2100390, by rfl⟩ : syracuseStep 5601041 = 4200781) B4200781
theorem B1660691 : Blo 1659529 1660691 := bstep (se 1 (by rfl) ⟨1245518, by rfl⟩ : syracuseStep 1660691 = 2491037) B2491037
theorem B1660707 : Blo 1659529 1660707 := bstep (se 1 (by rfl) ⟨1245530, by rfl⟩ : syracuseStep 1660707 = 2491061) B2491061
theorem B1660723 : Blo 1659529 1660723 := bstep (se 1 (by rfl) ⟨1245542, by rfl⟩ : syracuseStep 1660723 = 2491085) B2491085
theorem B1660739 : Blo 1659529 1660739 := bstep (se 1 (by rfl) ⟨1245554, by rfl⟩ : syracuseStep 1660739 = 2491109) B2491109
theorem B1660755 : Blo 1659529 1660755 := bstep (se 1 (by rfl) ⟨1245566, by rfl⟩ : syracuseStep 1660755 = 2491133) B2491133
theorem B1660771 : Blo 1659529 1660771 := bstep (se 1 (by rfl) ⟨1245578, by rfl⟩ : syracuseStep 1660771 = 2491157) B2491157
theorem B1660787 : Blo 1659529 1660787 := bstep (se 1 (by rfl) ⟨1245590, by rfl⟩ : syracuseStep 1660787 = 2491181) B2491181
theorem B1660803 : Blo 1659529 1660803 := bstep (se 1 (by rfl) ⟨1245602, by rfl⟩ : syracuseStep 1660803 = 2491205) B2491205
theorem B1660819 : Blo 1659529 1660819 := bstep (se 1 (by rfl) ⟨1245614, by rfl⟩ : syracuseStep 1660819 = 2491229) B2491229
theorem B1660835 : Blo 1659529 1660835 := bstep (se 1 (by rfl) ⟨1245626, by rfl⟩ : syracuseStep 1660835 = 2491253) B2491253
theorem B5052323 : Blo 1659529 5052323 := bstep (se 1 (by rfl) ⟨3789242, by rfl⟩ : syracuseStep 5052323 = 7578485) B7578485
theorem B1660851 : Blo 1659529 1660851 := bstep (se 1 (by rfl) ⟨1245638, by rfl⟩ : syracuseStep 1660851 = 2491277) B2491277
theorem B1660867 : Blo 1659529 1660867 := bstep (se 1 (by rfl) ⟨1245650, by rfl⟩ : syracuseStep 1660867 = 2491301) B2491301
theorem B12605381 : Blo 1659529 12605381 := bstep (se 4 (by rfl) ⟨1181754, by rfl⟩ : syracuseStep 12605381 = 2363509) B2363509
theorem B1660883 : Blo 1659529 1660883 := bstep (se 1 (by rfl) ⟨1245662, by rfl⟩ : syracuseStep 1660883 = 2491325) B2491325
theorem B3545059 : Blo 1659529 3545059 := bstep (se 1 (by rfl) ⟨2658794, by rfl⟩ : syracuseStep 3545059 = 5317589) B5317589
theorem B1660899 : Blo 1659529 1660899 := bstep (se 1 (by rfl) ⟨1245674, by rfl⟩ : syracuseStep 1660899 = 2491349) B2491349
theorem B6731761 : Blo 1659529 6731761 := bstep (se 2 (by rfl) ⟨2524410, by rfl⟩ : syracuseStep 6731761 = 5048821) B5048821
theorem B1660915 : Blo 1659529 1660915 := bstep (se 1 (by rfl) ⟨1245686, by rfl⟩ : syracuseStep 1660915 = 2491373) B2491373
theorem B2840579 : Blo 1659529 2840579 := bstep (se 1 (by rfl) ⟨2130434, by rfl⟩ : syracuseStep 2840579 = 4260869) B4260869
theorem B1660931 : Blo 1659529 1660931 := bstep (se 1 (by rfl) ⟨1245698, by rfl⟩ : syracuseStep 1660931 = 2491397) B2491397
theorem B1660947 : Blo 1659529 1660947 := bstep (se 1 (by rfl) ⟨1245710, by rfl⟩ : syracuseStep 1660947 = 2491421) B2491421
theorem B1660963 : Blo 1659529 1660963 := bstep (se 1 (by rfl) ⟨1245722, by rfl⟩ : syracuseStep 1660963 = 2491445) B2491445
theorem B1660979 : Blo 1659529 1660979 := bstep (se 1 (by rfl) ⟨1245734, by rfl⟩ : syracuseStep 1660979 = 2491469) B2491469
theorem B1660995 : Blo 1659529 1660995 := bstep (se 1 (by rfl) ⟨1245746, by rfl⟩ : syracuseStep 1660995 = 2491493) B2491493
theorem B7977037 : Blo 1659529 7977037 := bstep (se 3 (by rfl) ⟨1495694, by rfl⟩ : syracuseStep 7977037 = 2991389) B2991389
theorem B2660435 : Blo 1659529 2660435 := bstep (se 1 (by rfl) ⟨1995326, by rfl⟩ : syracuseStep 2660435 = 3990653) B3990653
theorem B1661011 : Blo 1659529 1661011 := bstep (se 1 (by rfl) ⟨1245758, by rfl⟩ : syracuseStep 1661011 = 2491517) B2491517
theorem B2365537 : Blo 1659529 2365537 := bstep (se 2 (by rfl) ⟨887076, by rfl⟩ : syracuseStep 2365537 = 1774153) B1774153
theorem B1661027 : Blo 1659529 1661027 := bstep (se 1 (by rfl) ⟨1245770, by rfl⟩ : syracuseStep 1661027 = 2491541) B2491541
theorem B1661043 : Blo 1659529 1661043 := bstep (se 1 (by rfl) ⟨1245782, by rfl⟩ : syracuseStep 1661043 = 2491565) B2491565
theorem B1661059 : Blo 1659529 1661059 := bstep (se 1 (by rfl) ⟨1245794, by rfl⟩ : syracuseStep 1661059 = 2491589) B2491589
theorem B2365571 : Blo 1659529 2365571 := bstep (se 1 (by rfl) ⟨1774178, by rfl⟩ : syracuseStep 2365571 = 3548357) B3548357
theorem B1661075 : Blo 1659529 1661075 := bstep (se 1 (by rfl) ⟨1245806, by rfl⟩ : syracuseStep 1661075 = 2491613) B2491613
theorem B1661091 : Blo 1659529 1661091 := bstep (se 1 (by rfl) ⟨1245818, by rfl⟩ : syracuseStep 1661091 = 2491637) B2491637
theorem B2660531 : Blo 1659529 2660531 := bstep (se 1 (by rfl) ⟨1995398, by rfl⟩ : syracuseStep 2660531 = 3990797) B3990797
theorem B1661107 : Blo 1659529 1661107 := bstep (se 1 (by rfl) ⟨1245830, by rfl⟩ : syracuseStep 1661107 = 2491661) B2491661
theorem B1661123 : Blo 1659529 1661123 := bstep (se 1 (by rfl) ⟨1245842, by rfl⟩ : syracuseStep 1661123 = 2491685) B2491685
theorem B2660563 : Blo 1659529 2660563 := bstep (se 1 (by rfl) ⟨1995422, by rfl⟩ : syracuseStep 2660563 = 3990845) B3990845
theorem B1661139 : Blo 1659529 1661139 := bstep (se 1 (by rfl) ⟨1245854, by rfl⟩ : syracuseStep 1661139 = 2491709) B2491709
theorem B1661155 : Blo 1659529 1661155 := bstep (se 1 (by rfl) ⟨1245866, by rfl⟩ : syracuseStep 1661155 = 2491733) B2491733
theorem B8411363 : Blo 1659529 8411363 := bstep (se 1 (by rfl) ⟨6308522, by rfl⟩ : syracuseStep 8411363 = 12617045) B12617045
theorem B1661171 : Blo 1659529 1661171 := bstep (se 1 (by rfl) ⟨1245878, by rfl⟩ : syracuseStep 1661171 = 2491757) B2491757
theorem B1661187 : Blo 1659529 1661187 := bstep (se 1 (by rfl) ⟨1245890, by rfl⟩ : syracuseStep 1661187 = 2491781) B2491781
theorem B1661203 : Blo 1659529 1661203 := bstep (se 1 (by rfl) ⟨1245902, by rfl⟩ : syracuseStep 1661203 = 2491805) B2491805
theorem B1661219 : Blo 1659529 1661219 := bstep (se 1 (by rfl) ⟨1245914, by rfl⟩ : syracuseStep 1661219 = 2491829) B2491829
theorem B5601581 : Blo 1659529 5601581 := bstep (se 3 (by rfl) ⟨1050296, by rfl⟩ : syracuseStep 5601581 = 2100593) B2100593
theorem B1661235 : Blo 1659529 1661235 := bstep (se 1 (by rfl) ⟨1245926, by rfl⟩ : syracuseStep 1661235 = 2491853) B2491853
theorem B38869301 : Blo 1659529 38869301 := bstep (se 5 (by rfl) ⟨1821998, by rfl⟩ : syracuseStep 38869301 = 3643997) B3643997
theorem B1661251 : Blo 1659529 1661251 := bstep (se 1 (by rfl) ⟨1245938, by rfl⟩ : syracuseStep 1661251 = 2491877) B2491877
theorem B3365201 : Blo 1659529 3365201 := bstep (se 2 (by rfl) ⟨1261950, by rfl⟩ : syracuseStep 3365201 = 2523901) B2523901
theorem B1661267 : Blo 1659529 1661267 := bstep (se 1 (by rfl) ⟨1245950, by rfl⟩ : syracuseStep 1661267 = 2491901) B2491901
theorem B5601635 : Blo 1659529 5601635 := bstep (se 1 (by rfl) ⟨4201226, by rfl⟩ : syracuseStep 5601635 = 8402453) B8402453
theorem B1661283 : Blo 1659529 1661283 := bstep (se 1 (by rfl) ⟨1245962, by rfl⟩ : syracuseStep 1661283 = 2491925) B2491925
theorem B1661299 : Blo 1659529 1661299 := bstep (se 1 (by rfl) ⟨1245974, by rfl⟩ : syracuseStep 1661299 = 2491949) B2491949
theorem B1661315 : Blo 1659529 1661315 := bstep (se 1 (by rfl) ⟨1245986, by rfl⟩ : syracuseStep 1661315 = 2491973) B2491973
theorem B1661331 : Blo 1659529 1661331 := bstep (se 1 (by rfl) ⟨1245998, by rfl⟩ : syracuseStep 1661331 = 2491997) B2491997
theorem B1661347 : Blo 1659529 1661347 := bstep (se 1 (by rfl) ⟨1246010, by rfl⟩ : syracuseStep 1661347 = 2492021) B2492021
theorem B1661363 : Blo 1659529 1661363 := bstep (se 1 (by rfl) ⟨1246022, by rfl⟩ : syracuseStep 1661363 = 2492045) B2492045
theorem B3733955 : Blo 1659529 3733955 := bstep (se 1 (by rfl) ⟨2800466, by rfl⟩ : syracuseStep 3733955 = 5600933) B5600933
theorem B1661379 : Blo 1659529 1661379 := bstep (se 1 (by rfl) ⟨1246034, by rfl⟩ : syracuseStep 1661379 = 2492069) B2492069
theorem B1661395 : Blo 1659529 1661395 := bstep (se 1 (by rfl) ⟨1246046, by rfl⟩ : syracuseStep 1661395 = 2492093) B2492093
theorem B6306275 : Blo 1659529 6306275 := bstep (se 1 (by rfl) ⟨4729706, by rfl⟩ : syracuseStep 6306275 = 9459413) B9459413
theorem B1661411 : Blo 1659529 1661411 := bstep (se 1 (by rfl) ⟨1246058, by rfl⟩ : syracuseStep 1661411 = 2492117) B2492117
theorem B12614129 : Blo 1659529 12614129 := bstep (se 2 (by rfl) ⟨4730298, by rfl⟩ : syracuseStep 12614129 = 9460597) B9460597
theorem B1661427 : Blo 1659529 1661427 := bstep (se 1 (by rfl) ⟨1246070, by rfl⟩ : syracuseStep 1661427 = 2492141) B2492141
theorem B1661443 : Blo 1659529 1661443 := bstep (se 1 (by rfl) ⟨1246082, by rfl⟩ : syracuseStep 1661443 = 2492165) B2492165
theorem B1661459 : Blo 1659529 1661459 := bstep (se 1 (by rfl) ⟨1246094, by rfl⟩ : syracuseStep 1661459 = 2492189) B2492189
theorem B1661475 : Blo 1659529 1661475 := bstep (se 1 (by rfl) ⟨1246106, by rfl⟩ : syracuseStep 1661475 = 2492213) B2492213
theorem B1661491 : Blo 1659529 1661491 := bstep (se 1 (by rfl) ⟨1246118, by rfl⟩ : syracuseStep 1661491 = 2492237) B2492237
theorem B1661507 : Blo 1659529 1661507 := bstep (se 1 (by rfl) ⟨1246130, by rfl⟩ : syracuseStep 1661507 = 2492261) B2492261
theorem B1661523 : Blo 1659529 1661523 := bstep (se 1 (by rfl) ⟨1246142, by rfl⟩ : syracuseStep 1661523 = 2492285) B2492285
theorem B5601905 : Blo 1659529 5601905 := bstep (se 2 (by rfl) ⟨2100714, by rfl⟩ : syracuseStep 5601905 = 4201429) B4201429
theorem B3152515 : Blo 1659529 3152515 := bstep (se 1 (by rfl) ⟨2364386, by rfl⟩ : syracuseStep 3152515 = 4728773) B4728773
theorem B4201105 : Blo 1659529 4201105 := bstep (se 2 (by rfl) ⟨1575414, by rfl⟩ : syracuseStep 4201105 = 3150829) B3150829
theorem B3545777 : Blo 1659529 3545777 := bstep (se 2 (by rfl) ⟨1329666, by rfl⟩ : syracuseStep 3545777 = 2659333) B2659333
theorem B11967173 : Blo 1659529 11967173 := bstep (se 4 (by rfl) ⟨1121922, by rfl⟩ : syracuseStep 11967173 = 2243845) B2243845
theorem B3734225 : Blo 1659529 3734225 := bstep (se 2 (by rfl) ⟨1400334, by rfl⟩ : syracuseStep 3734225 = 2800669) B2800669
theorem B3734243 : Blo 1659529 3734243 := bstep (se 1 (by rfl) ⟨2800682, by rfl⟩ : syracuseStep 3734243 = 5601365) B5601365
theorem B3152675 : Blo 1659529 3152675 := bstep (se 1 (by rfl) ⟨2364506, by rfl⟩ : syracuseStep 3152675 = 4729013) B4729013
theorem B4201379 : Blo 1659529 4201379 := bstep (se 1 (by rfl) ⟨3151034, by rfl⟩ : syracuseStep 4201379 = 6302069) B6302069
theorem B2800561 : Blo 1659529 2800561 := bstep (se 2 (by rfl) ⟨1050210, by rfl⟩ : syracuseStep 2800561 = 2100421) B2100421
theorem B4045763 : Blo 1659529 4045763 := bstep (se 1 (by rfl) ⟨3034322, by rfl⟩ : syracuseStep 4045763 = 6068645) B6068645
theorem B2489297 : Blo 1659529 2489297 := bstep (se 2 (by rfl) ⟨933486, by rfl⟩ : syracuseStep 2489297 = 1866973) B1866973
theorem B2800595 : Blo 1659529 2800595 := bstep (se 1 (by rfl) ⟨2100446, by rfl⟩ : syracuseStep 2800595 = 4200893) B4200893
theorem B2489315 : Blo 1659529 2489315 := bstep (se 1 (by rfl) ⟨1866986, by rfl⟩ : syracuseStep 2489315 = 3733973) B3733973
theorem B3734513 : Blo 1659529 3734513 := bstep (se 2 (by rfl) ⟨1400442, by rfl⟩ : syracuseStep 3734513 = 2800885) B2800885
theorem B2489345 : Blo 1659529 2489345 := bstep (se 2 (by rfl) ⟨933504, by rfl⟩ : syracuseStep 2489345 = 1867009) B1867009
theorem B3734531 : Blo 1659529 3734531 := bstep (se 1 (by rfl) ⟨2800898, by rfl⟩ : syracuseStep 3734531 = 5601797) B5601797
theorem B7093261 : Blo 1659529 7093261 := bstep (se 3 (by rfl) ⟨1329986, by rfl⟩ : syracuseStep 7093261 = 2659973) B2659973
theorem B2489363 : Blo 1659529 2489363 := bstep (se 1 (by rfl) ⟨1867022, by rfl⟩ : syracuseStep 2489363 = 3734045) B3734045
theorem B2489393 : Blo 1659529 2489393 := bstep (se 2 (by rfl) ⟨933522, by rfl⟩ : syracuseStep 2489393 = 1867045) B1867045
theorem B2489411 : Blo 1659529 2489411 := bstep (se 1 (by rfl) ⟨1867058, by rfl⟩ : syracuseStep 2489411 = 3734117) B3734117
theorem B2800723 : Blo 1659529 2800723 := bstep (se 1 (by rfl) ⟨2100542, by rfl⟩ : syracuseStep 2800723 = 4201085) B4201085
theorem B2489441 : Blo 1659529 2489441 := bstep (se 2 (by rfl) ⟨933540, by rfl⟩ : syracuseStep 2489441 = 1867081) B1867081
theorem B4201571 : Blo 1659529 4201571 := bstep (se 1 (by rfl) ⟨3151178, by rfl⟩ : syracuseStep 4201571 = 6302357) B6302357
theorem B6306929 : Blo 1659529 6306929 := bstep (se 2 (by rfl) ⟨2365098, by rfl⟩ : syracuseStep 6306929 = 4730197) B4730197
theorem B2489459 : Blo 1659529 2489459 := bstep (se 1 (by rfl) ⟨1867094, by rfl⟩ : syracuseStep 2489459 = 3734189) B3734189
theorem B5602445 : Blo 1659529 5602445 := bstep (se 3 (by rfl) ⟨1050458, by rfl⟩ : syracuseStep 5602445 = 2100917) B2100917
theorem B2489489 : Blo 1659529 2489489 := bstep (se 2 (by rfl) ⟨933558, by rfl⟩ : syracuseStep 2489489 = 1867117) B1867117
theorem B2489507 : Blo 1659529 2489507 := bstep (se 1 (by rfl) ⟨1867130, by rfl⟩ : syracuseStep 2489507 = 3734261) B3734261
theorem B2243747 : Blo 1659529 2243747 := bstep (se 1 (by rfl) ⟨1682810, by rfl⟩ : syracuseStep 2243747 = 3365621) B3365621
theorem B3546289 : Blo 1659529 3546289 := bstep (se 2 (by rfl) ⟨1329858, by rfl⟩ : syracuseStep 3546289 = 2659717) B2659717
theorem B2489537 : Blo 1659529 2489537 := bstep (se 2 (by rfl) ⟨933576, by rfl⟩ : syracuseStep 2489537 = 1867153) B1867153
theorem B5602499 : Blo 1659529 5602499 := bstep (se 1 (by rfl) ⟨4201874, by rfl⟩ : syracuseStep 5602499 = 8403749) B8403749
theorem B2489555 : Blo 1659529 2489555 := bstep (se 1 (by rfl) ⟨1867166, by rfl⟩ : syracuseStep 2489555 = 3734333) B3734333
theorem B2800865 : Blo 1659529 2800865 := bstep (se 2 (by rfl) ⟨1050324, by rfl⟩ : syracuseStep 2800865 = 2100649) B2100649
theorem B2489585 : Blo 1659529 2489585 := bstep (se 2 (by rfl) ⟨933594, by rfl⟩ : syracuseStep 2489585 = 1867189) B1867189
theorem B2489603 : Blo 1659529 2489603 := bstep (se 1 (by rfl) ⟨1867202, by rfl⟩ : syracuseStep 2489603 = 3734405) B3734405
theorem B3734801 : Blo 1659529 3734801 := bstep (se 2 (by rfl) ⟨1400550, by rfl⟩ : syracuseStep 3734801 = 2801101) B2801101
theorem B1867027 : Blo 1659529 1867027 := bstep (se 1 (by rfl) ⟨1400270, by rfl⟩ : syracuseStep 1867027 = 2800541) B2800541
theorem B2489633 : Blo 1659529 2489633 := bstep (se 2 (by rfl) ⟨933612, by rfl⟩ : syracuseStep 2489633 = 1867225) B1867225
theorem B3734819 : Blo 1659529 3734819 := bstep (se 1 (by rfl) ⟨2801114, by rfl⟩ : syracuseStep 3734819 = 5602229) B5602229
theorem B2489651 : Blo 1659529 2489651 := bstep (se 1 (by rfl) ⟨1867238, by rfl⟩ : syracuseStep 2489651 = 3734477) B3734477
theorem B4726097 : Blo 1659529 4726097 := bstep (se 2 (by rfl) ⟨1772286, by rfl⟩ : syracuseStep 4726097 = 3544573) B3544573
theorem B2489681 : Blo 1659529 2489681 := bstep (se 2 (by rfl) ⟨933630, by rfl⟩ : syracuseStep 2489681 = 1867261) B1867261
theorem B2800993 : Blo 1659529 2800993 := bstep (se 2 (by rfl) ⟨1050372, by rfl⟩ : syracuseStep 2800993 = 2100745) B2100745
theorem B2489699 : Blo 1659529 2489699 := bstep (se 1 (by rfl) ⟨1867274, by rfl⟩ : syracuseStep 2489699 = 3734549) B3734549
theorem B2489729 : Blo 1659529 2489729 := bstep (se 2 (by rfl) ⟨933648, by rfl⟩ : syracuseStep 2489729 = 1867297) B1867297
theorem B2801027 : Blo 1659529 2801027 := bstep (se 1 (by rfl) ⟨2100770, by rfl⟩ : syracuseStep 2801027 = 4201541) B4201541
theorem B2489747 : Blo 1659529 2489747 := bstep (se 1 (by rfl) ⟨1867310, by rfl⟩ : syracuseStep 2489747 = 3734621) B3734621
theorem B1867171 : Blo 1659529 1867171 := bstep (se 1 (by rfl) ⟨1400378, by rfl⟩ : syracuseStep 1867171 = 2800757) B2800757
theorem B2489777 : Blo 1659529 2489777 := bstep (se 2 (by rfl) ⟨933666, by rfl⟩ : syracuseStep 2489777 = 1867333) B1867333
theorem B2489795 : Blo 1659529 2489795 := bstep (se 1 (by rfl) ⟨1867346, by rfl⟩ : syracuseStep 2489795 = 3734693) B3734693
theorem B5602769 : Blo 1659529 5602769 := bstep (se 2 (by rfl) ⟨2101038, by rfl⟩ : syracuseStep 5602769 = 4202077) B4202077
theorem B2489825 : Blo 1659529 2489825 := bstep (se 2 (by rfl) ⟨933684, by rfl⟩ : syracuseStep 2489825 = 1867369) B1867369
theorem B2489843 : Blo 1659529 2489843 := bstep (se 1 (by rfl) ⟨1867382, by rfl⟩ : syracuseStep 2489843 = 3734765) B3734765
theorem B2801155 : Blo 1659529 2801155 := bstep (se 1 (by rfl) ⟨2100866, by rfl⟩ : syracuseStep 2801155 = 4201733) B4201733
theorem B7577101 : Blo 1659529 7577101 := bstep (se 3 (by rfl) ⟨1420706, by rfl⟩ : syracuseStep 7577101 = 2841413) B2841413
theorem B4726289 : Blo 1659529 4726289 := bstep (se 2 (by rfl) ⟨1772358, by rfl⟩ : syracuseStep 4726289 = 3544717) B3544717
theorem B2489873 : Blo 1659529 2489873 := bstep (se 2 (by rfl) ⟨933702, by rfl⟩ : syracuseStep 2489873 = 1867405) B1867405
theorem B2489891 : Blo 1659529 2489891 := bstep (se 1 (by rfl) ⟨1867418, by rfl⟩ : syracuseStep 2489891 = 3734837) B3734837
theorem B3735089 : Blo 1659529 3735089 := bstep (se 2 (by rfl) ⟨1400658, by rfl⟩ : syracuseStep 3735089 = 2801317) B2801317
theorem B1867315 : Blo 1659529 1867315 := bstep (se 1 (by rfl) ⟨1400486, by rfl⟩ : syracuseStep 1867315 = 2800973) B2800973
theorem B45432373 : Blo 1659529 45432373 := bstep (se 5 (by rfl) ⟨2129642, by rfl⟩ : syracuseStep 45432373 = 4259285) B4259285
theorem B2489921 : Blo 1659529 2489921 := bstep (se 2 (by rfl) ⟨933720, by rfl⟩ : syracuseStep 2489921 = 1867441) B1867441
theorem B3735107 : Blo 1659529 3735107 := bstep (se 1 (by rfl) ⟨2801330, by rfl⟩ : syracuseStep 3735107 = 5602661) B5602661
theorem B9453125 : Blo 1659529 9453125 := bstep (se 4 (by rfl) ⟨886230, by rfl⟩ : syracuseStep 9453125 = 1772461) B1772461
theorem B2489939 : Blo 1659529 2489939 := bstep (se 1 (by rfl) ⟨1867454, by rfl⟩ : syracuseStep 2489939 = 3734909) B3734909
theorem B2489969 : Blo 1659529 2489969 := bstep (se 2 (by rfl) ⟨933738, by rfl⟩ : syracuseStep 2489969 = 1867477) B1867477
theorem B2489987 : Blo 1659529 2489987 := bstep (se 1 (by rfl) ⟨1867490, by rfl⟩ : syracuseStep 2489987 = 3734981) B3734981
theorem B2801297 : Blo 1659529 2801297 := bstep (se 2 (by rfl) ⟨1050486, by rfl⟩ : syracuseStep 2801297 = 2100973) B2100973
theorem B2490017 : Blo 1659529 2490017 := bstep (se 2 (by rfl) ⟨933756, by rfl⟩ : syracuseStep 2490017 = 1867513) B1867513
theorem B2490035 : Blo 1659529 2490035 := bstep (se 1 (by rfl) ⟨1867526, by rfl⟩ : syracuseStep 2490035 = 3735053) B3735053
theorem B1867459 : Blo 1659529 1867459 := bstep (se 1 (by rfl) ⟨1400594, by rfl⟩ : syracuseStep 1867459 = 2801189) B2801189
theorem B2490065 : Blo 1659529 2490065 := bstep (se 2 (by rfl) ⟨933774, by rfl⟩ : syracuseStep 2490065 = 1867549) B1867549
theorem B4316899 : Blo 1659529 4316899 := bstep (se 1 (by rfl) ⟨3237674, by rfl⟩ : syracuseStep 4316899 = 6475349) B6475349
theorem B2490083 : Blo 1659529 2490083 := bstep (se 1 (by rfl) ⟨1867562, by rfl⟩ : syracuseStep 2490083 = 3735125) B3735125
theorem B8404721 : Blo 1659529 8404721 := bstep (se 2 (by rfl) ⟨3151770, by rfl⟩ : syracuseStep 8404721 = 6303541) B6303541
theorem B2490113 : Blo 1659529 2490113 := bstep (se 2 (by rfl) ⟨933792, by rfl⟩ : syracuseStep 2490113 = 1867585) B1867585
theorem B2801425 : Blo 1659529 2801425 := bstep (se 2 (by rfl) ⟨1050534, by rfl⟩ : syracuseStep 2801425 = 2101069) B2101069
theorem B2490131 : Blo 1659529 2490131 := bstep (se 1 (by rfl) ⟨1867598, by rfl⟩ : syracuseStep 2490131 = 3735197) B3735197
theorem B2490161 : Blo 1659529 2490161 := bstep (se 2 (by rfl) ⟨933810, by rfl⟩ : syracuseStep 2490161 = 1867621) B1867621
theorem B2801459 : Blo 1659529 2801459 := bstep (se 1 (by rfl) ⟨2101094, by rfl⟩ : syracuseStep 2801459 = 4202189) B4202189
theorem B2490179 : Blo 1659529 2490179 := bstep (se 1 (by rfl) ⟨1867634, by rfl⟩ : syracuseStep 2490179 = 3735269) B3735269
theorem B3735377 : Blo 1659529 3735377 := bstep (se 2 (by rfl) ⟨1400766, by rfl⟩ : syracuseStep 3735377 = 2801533) B2801533
theorem B3153745 : Blo 1659529 3153745 := bstep (se 2 (by rfl) ⟨1182654, by rfl⟩ : syracuseStep 3153745 = 2365309) B2365309
theorem B1867603 : Blo 1659529 1867603 := bstep (se 1 (by rfl) ⟨1400702, by rfl⟩ : syracuseStep 1867603 = 2801405) B2801405
theorem B2490209 : Blo 1659529 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B3735395 : Blo 1659529 3735395 := bstep (se 1 (by rfl) ⟨2801546, by rfl⟩ : syracuseStep 3735395 = 5603093) B5603093
theorem B2490227 : Blo 1659529 2490227 := bstep (se 1 (by rfl) ⟨1867670, by rfl⟩ : syracuseStep 2490227 = 3735341) B3735341
theorem B2490257 : Blo 1659529 2490257 := bstep (se 2 (by rfl) ⟨933846, by rfl⟩ : syracuseStep 2490257 = 1867693) B1867693
theorem B5390243 : Blo 1659529 5390243 := bstep (se 1 (by rfl) ⟨4042682, by rfl⟩ : syracuseStep 5390243 = 8085365) B8085365
theorem B2490275 : Blo 1659529 2490275 := bstep (se 1 (by rfl) ⟨1867706, by rfl⟩ : syracuseStep 2490275 = 3735413) B3735413
theorem B2801587 : Blo 1659529 2801587 := bstep (se 1 (by rfl) ⟨2101190, by rfl⟩ : syracuseStep 2801587 = 4202381) B4202381
theorem B2490305 : Blo 1659529 2490305 := bstep (se 2 (by rfl) ⟨933864, by rfl⟩ : syracuseStep 2490305 = 1867729) B1867729
theorem B2490323 : Blo 1659529 2490323 := bstep (se 1 (by rfl) ⟨1867742, by rfl⟩ : syracuseStep 2490323 = 3735485) B3735485
theorem B1867747 : Blo 1659529 1867747 := bstep (se 1 (by rfl) ⟨1400810, by rfl⟩ : syracuseStep 1867747 = 2801621) B2801621
theorem B5603309 : Blo 1659529 5603309 := bstep (se 3 (by rfl) ⟨1050620, by rfl⟩ : syracuseStep 5603309 = 2101241) B2101241
theorem B2490353 : Blo 1659529 2490353 := bstep (se 2 (by rfl) ⟨933882, by rfl⟩ : syracuseStep 2490353 = 1867765) B1867765
theorem B2801675 : Blo 1659529 2801675 := bstep (se 1 (by rfl) ⟨2101256, by rfl⟩ : syracuseStep 2801675 = 4202513) B4202513
theorem B3735575 : Blo 1659529 3735575 := bstep (se 1 (by rfl) ⟨2801681, by rfl⟩ : syracuseStep 3735575 = 5603363) B5603363
theorem B1867819 : Blo 1659529 1867819 := bstep (se 1 (by rfl) ⟨1400864, by rfl⟩ : syracuseStep 1867819 = 2801729) B2801729
theorem B2490443 : Blo 1659529 2490443 := bstep (se 1 (by rfl) ⟨1867832, by rfl⟩ : syracuseStep 2490443 = 3735665) B3735665
theorem B6307915 : Blo 1659529 6307915 := bstep (se 1 (by rfl) ⟨4730936, by rfl⟩ : syracuseStep 6307915 = 9461873) B9461873
theorem B2490455 : Blo 1659529 2490455 := bstep (se 1 (by rfl) ⟨1867841, by rfl⟩ : syracuseStep 2490455 = 3735683) B3735683
theorem B5603417 : Blo 1659529 5603417 := bstep (se 2 (by rfl) ⟨2101281, by rfl⟩ : syracuseStep 5603417 = 4202563) B4202563
theorem B3367001 : Blo 1659529 3367001 := bstep (se 2 (by rfl) ⟨1262625, by rfl⟩ : syracuseStep 3367001 = 2525251) B2525251
theorem B3154049 : Blo 1659529 3154049 := bstep (se 2 (by rfl) ⟨1182768, by rfl⟩ : syracuseStep 3154049 = 2365537) B2365537
theorem B2801803 : Blo 1659529 2801803 := bstep (se 1 (by rfl) ⟨2101352, by rfl⟩ : syracuseStep 2801803 = 4202705) B4202705
theorem B51101837 : Blo 1659529 51101837 := bstep (se 3 (by rfl) ⟨9581594, by rfl⟩ : syracuseStep 51101837 = 19163189) B19163189
theorem B1867927 : Blo 1659529 1867927 := bstep (se 1 (by rfl) ⟨1400945, by rfl⟩ : syracuseStep 1867927 = 2801891) B2801891
theorem B2490521 : Blo 1659529 2490521 := bstep (se 2 (by rfl) ⟨933945, by rfl⟩ : syracuseStep 2490521 = 1867891) B1867891
theorem B4202675 : Blo 1659529 4202675 := bstep (se 1 (by rfl) ⟨3152006, by rfl⟩ : syracuseStep 4202675 = 6304013) B6304013
theorem B3735755 : Blo 1659529 3735755 := bstep (se 1 (by rfl) ⟨2801816, by rfl⟩ : syracuseStep 3735755 = 5603633) B5603633
theorem B3735809 : Blo 1659529 3735809 := bstep (se 2 (by rfl) ⟨1400928, by rfl⟩ : syracuseStep 3735809 = 2801857) B2801857
theorem B2490635 : Blo 1659529 2490635 := bstep (se 1 (by rfl) ⟨1867976, by rfl⟩ : syracuseStep 2490635 = 3735953) B3735953
theorem B2490647 : Blo 1659529 2490647 := bstep (se 1 (by rfl) ⟨1867985, by rfl⟩ : syracuseStep 2490647 = 3735971) B3735971
theorem B2801945 : Blo 1659529 2801945 := bstep (se 2 (by rfl) ⟨1050729, by rfl⟩ : syracuseStep 2801945 = 2101459) B2101459
theorem B3547417 : Blo 1659529 3547417 := bstep (se 2 (by rfl) ⟨1330281, by rfl⟩ : syracuseStep 3547417 = 2660563) B2660563
theorem B11968843 : Blo 1659529 11968843 := bstep (se 1 (by rfl) ⟨8976632, by rfl⟩ : syracuseStep 11968843 = 17953265) B17953265
theorem B1868107 : Blo 1659529 1868107 := bstep (se 1 (by rfl) ⟨1401080, by rfl⟩ : syracuseStep 1868107 = 2802161) B2802161
theorem B2490713 : Blo 1659529 2490713 := bstep (se 2 (by rfl) ⟨934017, by rfl⟩ : syracuseStep 2490713 = 1868035) B1868035
theorem B6308189 : Blo 1659529 6308189 := bstep (se 3 (by rfl) ⟨1182785, by rfl⟩ : syracuseStep 6308189 = 2365571) B2365571
theorem B3596683 : Blo 1659529 3596683 := bstep (se 1 (by rfl) ⟨2697512, by rfl⟩ : syracuseStep 3596683 = 5395025) B5395025
theorem B6390161 : Blo 1659529 6390161 := bstep (se 2 (by rfl) ⟨2396310, by rfl⟩ : syracuseStep 6390161 = 4792621) B4792621
theorem B2802073 : Blo 1659529 2802073 := bstep (se 2 (by rfl) ⟨1050777, by rfl⟩ : syracuseStep 2802073 = 2101555) B2101555
theorem B1868215 : Blo 1659529 1868215 := bstep (se 1 (by rfl) ⟨1401161, by rfl⟩ : syracuseStep 1868215 = 2802323) B2802323
theorem B7569857 : Blo 1659529 7569857 := bstep (se 2 (by rfl) ⟨2838696, by rfl⟩ : syracuseStep 7569857 = 5677393) B5677393
theorem B5046731 : Blo 1659529 5046731 := bstep (se 1 (by rfl) ⟨3785048, by rfl⟩ : syracuseStep 5046731 = 7570097) B7570097
theorem B2490827 : Blo 1659529 2490827 := bstep (se 1 (by rfl) ⟨1868120, by rfl⟩ : syracuseStep 2490827 = 3736241) B3736241
theorem B2490839 : Blo 1659529 2490839 := bstep (se 1 (by rfl) ⟨1868129, by rfl⟩ : syracuseStep 2490839 = 3736259) B3736259
theorem B3736025 : Blo 1659529 3736025 := bstep (se 2 (by rfl) ⟨1401009, by rfl⟩ : syracuseStep 3736025 = 2802019) B2802019
theorem B7094749 : Blo 1659529 7094749 := bstep (se 3 (by rfl) ⟨1330265, by rfl⟩ : syracuseStep 7094749 = 2660531) B2660531
theorem B2490905 : Blo 1659529 2490905 := bstep (se 2 (by rfl) ⟨934089, by rfl⟩ : syracuseStep 2490905 = 1868179) B1868179
theorem B3736115 : Blo 1659529 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B3736151 : Blo 1659529 3736151 := bstep (se 1 (by rfl) ⟨2802113, by rfl⟩ : syracuseStep 3736151 = 5604227) B5604227
theorem B1868395 : Blo 1659529 1868395 := bstep (se 1 (by rfl) ⟨1401296, by rfl⟩ : syracuseStep 1868395 = 2802593) B2802593
theorem B2491019 : Blo 1659529 2491019 := bstep (se 1 (by rfl) ⟨1868264, by rfl⟩ : syracuseStep 2491019 = 3736529) B3736529
theorem B2491031 : Blo 1659529 2491031 := bstep (se 1 (by rfl) ⟨1868273, by rfl⟩ : syracuseStep 2491031 = 3736547) B3736547
theorem B4203211 : Blo 1659529 4203211 := bstep (se 1 (by rfl) ⟨3152408, by rfl⟩ : syracuseStep 4203211 = 6304817) B6304817
theorem B1868503 : Blo 1659529 1868503 := bstep (se 1 (by rfl) ⟨1401377, by rfl⟩ : syracuseStep 1868503 = 2802755) B2802755
theorem B2491097 : Blo 1659529 2491097 := bstep (se 2 (by rfl) ⟨934161, by rfl⟩ : syracuseStep 2491097 = 1868323) B1868323
theorem B3736331 : Blo 1659529 3736331 := bstep (se 1 (by rfl) ⟨2802248, by rfl⟩ : syracuseStep 3736331 = 5604497) B5604497
theorem B5677847 : Blo 1659529 5677847 := bstep (se 1 (by rfl) ⟨4258385, by rfl⟩ : syracuseStep 5677847 = 8516771) B8516771
theorem B5604119 : Blo 1659529 5604119 := bstep (se 1 (by rfl) ⟨4203089, by rfl⟩ : syracuseStep 5604119 = 8406179) B8406179
theorem B3736385 : Blo 1659529 3736385 := bstep (se 2 (by rfl) ⟨1401144, by rfl⟩ : syracuseStep 3736385 = 2802289) B2802289
theorem B2491211 : Blo 1659529 2491211 := bstep (se 1 (by rfl) ⟨1868408, by rfl⟩ : syracuseStep 2491211 = 3736817) B3736817
theorem B2491223 : Blo 1659529 2491223 := bstep (se 1 (by rfl) ⟨1868417, by rfl⟩ : syracuseStep 2491223 = 3736835) B3736835
theorem B4203353 : Blo 1659529 4203353 := bstep (se 2 (by rfl) ⟨1576257, by rfl⟩ : syracuseStep 4203353 = 3152515) B3152515
theorem B28369763 : Blo 1659529 28369763 := bstep (se 1 (by rfl) ⟨21277322, by rfl⟩ : syracuseStep 28369763 = 42554645) B42554645
theorem B1868683 : Blo 1659529 1868683 := bstep (se 1 (by rfl) ⟨1401512, by rfl⟩ : syracuseStep 1868683 = 2803025) B2803025
theorem B2491289 : Blo 1659529 2491289 := bstep (se 2 (by rfl) ⟨934233, by rfl⟩ : syracuseStep 2491289 = 1868467) B1868467
theorem B2802647 : Blo 1659529 2802647 := bstep (se 1 (by rfl) ⟨2101985, by rfl⟩ : syracuseStep 2802647 = 4203971) B4203971
theorem B1868791 : Blo 1659529 1868791 := bstep (se 1 (by rfl) ⟨1401593, by rfl⟩ : syracuseStep 1868791 = 2803187) B2803187
theorem B2491403 : Blo 1659529 2491403 := bstep (se 1 (by rfl) ⟨1868552, by rfl⟩ : syracuseStep 2491403 = 3737105) B3737105
theorem B2491415 : Blo 1659529 2491415 := bstep (se 1 (by rfl) ⟨1868561, by rfl⟩ : syracuseStep 2491415 = 3737123) B3737123
theorem B3736601 : Blo 1659529 3736601 := bstep (se 2 (by rfl) ⟨1401225, by rfl⟩ : syracuseStep 3736601 = 2802451) B2802451
theorem B7095347 : Blo 1659529 7095347 := bstep (se 1 (by rfl) ⟨5321510, by rfl⟩ : syracuseStep 7095347 = 10643021) B10643021
theorem B5981249 : Blo 1659529 5981249 := bstep (se 2 (by rfl) ⟨2242968, by rfl⟩ : syracuseStep 5981249 = 4485937) B4485937
theorem B2802775 : Blo 1659529 2802775 := bstep (se 1 (by rfl) ⟨2102081, by rfl⟩ : syracuseStep 2802775 = 4204163) B4204163
theorem B2491481 : Blo 1659529 2491481 := bstep (se 2 (by rfl) ⟨934305, by rfl⟩ : syracuseStep 2491481 = 1868611) B1868611
theorem B3736691 : Blo 1659529 3736691 := bstep (se 1 (by rfl) ⟨2802518, by rfl⟩ : syracuseStep 3736691 = 5605037) B5605037
theorem B3736727 : Blo 1659529 3736727 := bstep (se 1 (by rfl) ⟨2802545, by rfl⟩ : syracuseStep 3736727 = 5605091) B5605091
theorem B1868971 : Blo 1659529 1868971 := bstep (se 1 (by rfl) ⟨1401728, by rfl⟩ : syracuseStep 1868971 = 2803457) B2803457
theorem B10093747 : Blo 1659529 10093747 := bstep (se 1 (by rfl) ⟨7570310, by rfl⟩ : syracuseStep 10093747 = 15140621) B15140621
theorem B3990721 : Blo 1659529 3990721 := bstep (se 2 (by rfl) ⟨1496520, by rfl⟩ : syracuseStep 3990721 = 2993041) B2993041
theorem B2491595 : Blo 1659529 2491595 := bstep (se 1 (by rfl) ⟨1868696, by rfl⟩ : syracuseStep 2491595 = 3737393) B3737393
theorem B2491607 : Blo 1659529 2491607 := bstep (se 1 (by rfl) ⟨1868705, by rfl⟩ : syracuseStep 2491607 = 3737411) B3737411
theorem B1869079 : Blo 1659529 1869079 := bstep (se 1 (by rfl) ⟨1401809, by rfl⟩ : syracuseStep 1869079 = 2803619) B2803619
theorem B3368215 : Blo 1659529 3368215 := bstep (se 1 (by rfl) ⟨2526161, by rfl⟩ : syracuseStep 3368215 = 5052323) B5052323
theorem B2491673 : Blo 1659529 2491673 := bstep (se 2 (by rfl) ⟨934377, by rfl⟩ : syracuseStep 2491673 = 1868755) B1868755
theorem B5604659 : Blo 1659529 5604659 := bstep (se 1 (by rfl) ⟨4203494, by rfl⟩ : syracuseStep 5604659 = 8406989) B8406989
theorem B10634561 : Blo 1659529 10634561 := bstep (se 2 (by rfl) ⟨3987960, by rfl⟩ : syracuseStep 10634561 = 7975921) B7975921
theorem B4261195 : Blo 1659529 4261195 := bstep (se 1 (by rfl) ⟨3195896, by rfl⟩ : syracuseStep 4261195 = 6391793) B6391793
theorem B3736907 : Blo 1659529 3736907 := bstep (se 1 (by rfl) ⟨2802680, by rfl⟩ : syracuseStep 3736907 = 5605361) B5605361
theorem B1893719 : Blo 1659529 1893719 := bstep (se 1 (by rfl) ⟨1420289, by rfl⟩ : syracuseStep 1893719 = 2840579) B2840579
theorem B3736961 : Blo 1659529 3736961 := bstep (se 2 (by rfl) ⟨1401360, by rfl⟩ : syracuseStep 3736961 = 2802721) B2802721
theorem B2491787 : Blo 1659529 2491787 := bstep (se 1 (by rfl) ⟨1868840, by rfl⟩ : syracuseStep 2491787 = 3737681) B3737681
theorem B2491799 : Blo 1659529 2491799 := bstep (se 1 (by rfl) ⟨1868849, by rfl⟩ : syracuseStep 2491799 = 3737699) B3737699
theorem B2491865 : Blo 1659529 2491865 := bstep (se 2 (by rfl) ⟨934449, by rfl⟩ : syracuseStep 2491865 = 1868899) B1868899
theorem B25912867 : Blo 1659529 25912867 := bstep (se 1 (by rfl) ⟨19434650, by rfl⟩ : syracuseStep 25912867 = 38869301) B38869301
theorem B4728385 : Blo 1659529 4728385 := bstep (se 2 (by rfl) ⟨1773144, by rfl⟩ : syracuseStep 4728385 = 3546289) B3546289
theorem B5604929 : Blo 1659529 5604929 := bstep (se 2 (by rfl) ⟨2101848, by rfl⟩ : syracuseStep 5604929 = 4203697) B4203697
theorem B2491979 : Blo 1659529 2491979 := bstep (se 1 (by rfl) ⟨1868984, by rfl⟩ : syracuseStep 2491979 = 3737969) B3737969
theorem B2491991 : Blo 1659529 2491991 := bstep (se 1 (by rfl) ⟨1868993, by rfl⟩ : syracuseStep 2491991 = 3737987) B3737987
theorem B3737177 : Blo 1659529 3737177 := bstep (se 2 (by rfl) ⟨1401441, by rfl⟩ : syracuseStep 3737177 = 2802883) B2802883
theorem B4204183 : Blo 1659529 4204183 := bstep (se 1 (by rfl) ⟨3153137, by rfl⟩ : syracuseStep 4204183 = 6306275) B6306275
theorem B2492057 : Blo 1659529 2492057 := bstep (se 2 (by rfl) ⟨934521, by rfl⟩ : syracuseStep 2492057 = 1869043) B1869043
theorem B3737267 : Blo 1659529 3737267 := bstep (se 1 (by rfl) ⟨2802950, by rfl⟩ : syracuseStep 3737267 = 5605901) B5605901
theorem B2803403 : Blo 1659529 2803403 := bstep (se 1 (by rfl) ⟨2102552, by rfl⟩ : syracuseStep 2803403 = 4205105) B4205105
theorem B35923661 : Blo 1659529 35923661 := bstep (se 3 (by rfl) ⟨6735686, by rfl⟩ : syracuseStep 35923661 = 13471373) B13471373
theorem B3737303 : Blo 1659529 3737303 := bstep (se 1 (by rfl) ⟨2802977, by rfl⟩ : syracuseStep 3737303 = 5605955) B5605955
theorem B2492171 : Blo 1659529 2492171 := bstep (se 1 (by rfl) ⟨1869128, by rfl⟩ : syracuseStep 2492171 = 3738257) B3738257
theorem B2492183 : Blo 1659529 2492183 := bstep (se 1 (by rfl) ⟨1869137, by rfl⟩ : syracuseStep 2492183 = 3738275) B3738275
theorem B2803531 : Blo 1659529 2803531 := bstep (se 1 (by rfl) ⟨2102648, by rfl⟩ : syracuseStep 2803531 = 4205297) B4205297
theorem B2492249 : Blo 1659529 2492249 := bstep (se 2 (by rfl) ⟨934593, by rfl⟩ : syracuseStep 2492249 = 1869187) B1869187
theorem B3737483 : Blo 1659529 3737483 := bstep (se 1 (by rfl) ⟨2803112, by rfl⟩ : syracuseStep 3737483 = 5606225) B5606225
theorem B3737537 : Blo 1659529 3737537 := bstep (se 2 (by rfl) ⟨1401576, by rfl⟩ : syracuseStep 3737537 = 2803153) B2803153
theorem B2697175 : Blo 1659529 2697175 := bstep (se 1 (by rfl) ⟨2022881, by rfl⟩ : syracuseStep 2697175 = 4045763) B4045763
theorem B2803673 : Blo 1659529 2803673 := bstep (se 2 (by rfl) ⟨1051377, by rfl⟩ : syracuseStep 2803673 = 2102755) B2102755
theorem B6064145 : Blo 1659529 6064145 := bstep (se 2 (by rfl) ⟨2274054, by rfl⟩ : syracuseStep 6064145 = 4548109) B4548109
theorem B10102801 : Blo 1659529 10102801 := bstep (se 2 (by rfl) ⟨3788550, by rfl⟩ : syracuseStep 10102801 = 7577101) B7577101
theorem B4204619 : Blo 1659529 4204619 := bstep (se 1 (by rfl) ⟨3153464, by rfl⟩ : syracuseStep 4204619 = 6306929) B6306929
theorem B2803801 : Blo 1659529 2803801 := bstep (se 2 (by rfl) ⟨1051425, by rfl⟩ : syracuseStep 2803801 = 2102851) B2102851
theorem B5605469 : Blo 1659529 5605469 := bstep (se 3 (by rfl) ⟨1051025, by rfl⟩ : syracuseStep 5605469 = 2102051) B2102051
theorem B3737753 : Blo 1659529 3737753 := bstep (se 2 (by rfl) ⟨1401657, by rfl⟩ : syracuseStep 3737753 = 2803315) B2803315
theorem B3737843 : Blo 1659529 3737843 := bstep (se 1 (by rfl) ⟨2803382, by rfl⟩ : syracuseStep 3737843 = 5606765) B5606765
theorem B8407313 : Blo 1659529 8407313 := bstep (se 2 (by rfl) ⟨3152742, by rfl⟩ : syracuseStep 8407313 = 6305485) B6305485
theorem B3737879 : Blo 1659529 3737879 := bstep (se 1 (by rfl) ⟨2803409, by rfl⟩ : syracuseStep 3737879 = 5606819) B5606819
theorem B4262233 : Blo 1659529 4262233 := bstep (se 2 (by rfl) ⟨1598337, by rfl⟩ : syracuseStep 4262233 = 3196675) B3196675
theorem B60615029 : Blo 1659529 60615029 := bstep (se 5 (by rfl) ⟨2841329, by rfl⟩ : syracuseStep 60615029 = 5682659) B5682659
theorem B6302083 : Blo 1659529 6302083 := bstep (se 1 (by rfl) ⟨4726562, by rfl⟩ : syracuseStep 6302083 = 9453125) B9453125
theorem B8407475 : Blo 1659529 8407475 := bstep (se 1 (by rfl) ⟨6305606, by rfl⟩ : syracuseStep 8407475 = 12611213) B12611213
theorem B4204993 : Blo 1659529 4204993 := bstep (se 2 (by rfl) ⟨1576872, by rfl⟩ : syracuseStep 4204993 = 3153745) B3153745
theorem B1919435 : Blo 1659529 1919435 := bstep (se 1 (by rfl) ⟨1439576, by rfl⟩ : syracuseStep 1919435 = 2879153) B2879153
theorem B3738059 : Blo 1659529 3738059 := bstep (se 1 (by rfl) ⟨2803544, by rfl⟩ : syracuseStep 3738059 = 5607089) B5607089
theorem B3738113 : Blo 1659529 3738113 := bstep (se 2 (by rfl) ⟨1401792, by rfl⟩ : syracuseStep 3738113 = 2803585) B2803585
theorem B3410455 : Blo 1659529 3410455 := bstep (se 1 (by rfl) ⟨2557841, by rfl⟩ : syracuseStep 3410455 = 5115683) B5115683
theorem B1796779 : Blo 1659529 1796779 := bstep (se 1 (by rfl) ⟨1347584, by rfl⟩ : syracuseStep 1796779 = 2695169) B2695169
theorem B6302387 : Blo 1659529 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B12126937 : Blo 1659529 12126937 := bstep (se 2 (by rfl) ⟨4547601, by rfl⟩ : syracuseStep 12126937 = 9095203) B9095203
theorem B3738329 : Blo 1659529 3738329 := bstep (se 2 (by rfl) ⟨1401873, by rfl⟩ : syracuseStep 3738329 = 2803747) B2803747
theorem B5982979 : Blo 1659529 5982979 := bstep (se 1 (by rfl) ⟨4487234, by rfl⟩ : syracuseStep 5982979 = 8974469) B8974469
theorem B10636049 : Blo 1659529 10636049 := bstep (se 2 (by rfl) ⟨3988518, by rfl⟩ : syracuseStep 10636049 = 7977037) B7977037
theorem B3738419 : Blo 1659529 3738419 := bstep (se 1 (by rfl) ⟨2803814, by rfl⟩ : syracuseStep 3738419 = 5607629) B5607629
theorem B8203187 : Blo 1659529 8203187 := bstep (se 1 (by rfl) ⟨6152390, by rfl⟩ : syracuseStep 8203187 = 12304781) B12304781
theorem B2026507 : Blo 1659529 2026507 := bstep (se 1 (by rfl) ⟨1519880, by rfl⟩ : syracuseStep 2026507 = 3039761) B3039761
theorem B4205591 : Blo 1659529 4205591 := bstep (se 1 (by rfl) ⟨3154193, by rfl⟩ : syracuseStep 4205591 = 6308387) B6308387
theorem B5983325 : Blo 1659529 5983325 := bstep (se 3 (by rfl) ⟨1121873, by rfl⟩ : syracuseStep 5983325 = 2243747) B2243747
theorem B5606603 : Blo 1659529 5606603 := bstep (se 1 (by rfl) ⟨4204952, by rfl⟩ : syracuseStep 5606603 = 8409905) B8409905
theorem B6303041 : Blo 1659529 6303041 := bstep (se 2 (by rfl) ⟨2363640, by rfl⟩ : syracuseStep 6303041 = 4727281) B4727281
theorem B5680459 : Blo 1659529 5680459 := bstep (se 1 (by rfl) ⟨4260344, by rfl⟩ : syracuseStep 5680459 = 8520689) B8520689
theorem B2559371 : Blo 1659529 2559371 := bstep (se 1 (by rfl) ⟨1919528, by rfl⟩ : syracuseStep 2559371 = 3839057) B3839057
theorem B1682839 : Blo 1659529 1682839 := bstep (se 1 (by rfl) ⟨1262129, by rfl⟩ : syracuseStep 1682839 = 2524259) B2524259
theorem B5606873 : Blo 1659529 5606873 := bstep (se 2 (by rfl) ⟨2102577, by rfl⟩ : syracuseStep 5606873 = 4205155) B4205155
theorem B6729281 : Blo 1659529 6729281 := bstep (se 2 (by rfl) ⟨2523480, by rfl⟩ : syracuseStep 6729281 = 5046961) B5046961
theorem B5115467 : Blo 1659529 5115467 := bstep (se 1 (by rfl) ⟨3836600, by rfl⟩ : syracuseStep 5115467 = 7673201) B7673201
theorem B2100811 : Blo 1659529 2100811 := bstep (se 1 (by rfl) ⟨1575608, by rfl⟩ : syracuseStep 2100811 = 3151217) B3151217
theorem B14192333 : Blo 1659529 14192333 := bstep (se 3 (by rfl) ⟨2661062, by rfl⟩ : syracuseStep 14192333 = 5322125) B5322125
theorem B2101079 : Blo 1659529 2101079 := bstep (se 1 (by rfl) ⟨1575809, by rfl⟩ : syracuseStep 2101079 = 3151619) B3151619
theorem B1994711 : Blo 1659529 1994711 := bstep (se 1 (by rfl) ⟨1496033, by rfl⟩ : syracuseStep 1994711 = 2992067) B2992067
theorem B9457681 : Blo 1659529 9457681 := bstep (se 2 (by rfl) ⟨3546630, by rfl⟩ : syracuseStep 9457681 = 7093261) B7093261
theorem B12603437 : Blo 1659529 12603437 := bstep (se 3 (by rfl) ⟨2363144, by rfl⟩ : syracuseStep 12603437 = 4726289) B4726289
theorem B1773623 : Blo 1659529 1773623 := bstep (se 1 (by rfl) ⟨1330217, by rfl⟩ : syracuseStep 1773623 = 2660435) B2660435
theorem B5607575 : Blo 1659529 5607575 := bstep (se 1 (by rfl) ⟨4205681, by rfl⟩ : syracuseStep 5607575 = 8411363) B8411363
theorem B1683703 : Blo 1659529 1683703 := bstep (se 1 (by rfl) ⟨1262777, by rfl⟩ : syracuseStep 1683703 = 2525555) B2525555
theorem B8409419 : Blo 1659529 8409419 := bstep (se 1 (by rfl) ⟨6307064, by rfl⟩ : syracuseStep 8409419 = 12614129) B12614129
theorem B2363737 : Blo 1659529 2363737 := bstep (se 2 (by rfl) ⟨886401, by rfl⟩ : syracuseStep 2363737 = 1772803) B1772803
theorem B2363851 : Blo 1659529 2363851 := bstep (se 1 (by rfl) ⟨1772888, by rfl⟩ : syracuseStep 2363851 = 3545777) B3545777
theorem B7090649 : Blo 1659529 7090649 := bstep (se 2 (by rfl) ⟨2658993, by rfl⟩ : syracuseStep 7090649 = 5317987) B5317987
theorem B5321177 : Blo 1659529 5321177 := bstep (se 2 (by rfl) ⟨1995441, by rfl⟩ : syracuseStep 5321177 = 3990883) B3990883
theorem B2101783 : Blo 1659529 2101783 := bstep (se 1 (by rfl) ⟨1576337, by rfl⟩ : syracuseStep 2101783 = 3152675) B3152675
theorem B7090733 : Blo 1659529 7090733 := bstep (se 3 (by rfl) ⟨1329512, by rfl⟩ : syracuseStep 7090733 = 2659025) B2659025
theorem B6304301 : Blo 1659529 6304301 := bstep (se 3 (by rfl) ⟨1182056, by rfl⟩ : syracuseStep 6304301 = 2364113) B2364113
theorem B6304331 : Blo 1659529 6304331 := bstep (se 1 (by rfl) ⟨4728248, by rfl⟩ : syracuseStep 6304331 = 9456497) B9456497
theorem B5321305 : Blo 1659529 5321305 := bstep (se 2 (by rfl) ⟨1995489, by rfl⟩ : syracuseStep 5321305 = 3990979) B3990979
theorem B1659531 : Blo 1659529 1659531 := bstep (se 1 (by rfl) ⟨1244648, by rfl⟩ : syracuseStep 1659531 = 2489297) B2489297
theorem B1995403 : Blo 1659529 1995403 := bstep (se 1 (by rfl) ⟨1496552, by rfl⟩ : syracuseStep 1995403 = 2993105) B2993105
theorem B1659543 : Blo 1659529 1659543 := bstep (se 1 (by rfl) ⟨1244657, by rfl⟩ : syracuseStep 1659543 = 2489315) B2489315
theorem B1659563 : Blo 1659529 1659563 := bstep (se 1 (by rfl) ⟨1244672, by rfl⟩ : syracuseStep 1659563 = 2489345) B2489345
theorem B1659575 : Blo 1659529 1659575 := bstep (se 1 (by rfl) ⟨1244681, by rfl⟩ : syracuseStep 1659575 = 2489363) B2489363
theorem B1659595 : Blo 1659529 1659595 := bstep (se 1 (by rfl) ⟨1244696, by rfl⟩ : syracuseStep 1659595 = 2489393) B2489393
theorem B1659607 : Blo 1659529 1659607 := bstep (se 1 (by rfl) ⟨1244705, by rfl⟩ : syracuseStep 1659607 = 2489411) B2489411
theorem B1659627 : Blo 1659529 1659627 := bstep (se 1 (by rfl) ⟨1244720, by rfl⟩ : syracuseStep 1659627 = 2489441) B2489441
theorem B60576497 : Blo 1659529 60576497 := bstep (se 2 (by rfl) ⟨22716186, by rfl⟩ : syracuseStep 60576497 = 45432373) B45432373
theorem B1659639 : Blo 1659529 1659639 := bstep (se 1 (by rfl) ⟨1244729, by rfl⟩ : syracuseStep 1659639 = 2489459) B2489459
theorem B1659659 : Blo 1659529 1659659 := bstep (se 1 (by rfl) ⟨1244744, by rfl⟩ : syracuseStep 1659659 = 2489489) B2489489
theorem B1659671 : Blo 1659529 1659671 := bstep (se 1 (by rfl) ⟨1244753, by rfl⟩ : syracuseStep 1659671 = 2489507) B2489507
theorem B1659691 : Blo 1659529 1659691 := bstep (se 1 (by rfl) ⟨1244768, by rfl⟩ : syracuseStep 1659691 = 2489537) B2489537
theorem B1659703 : Blo 1659529 1659703 := bstep (se 1 (by rfl) ⟨1244777, by rfl⟩ : syracuseStep 1659703 = 2489555) B2489555
theorem B1659723 : Blo 1659529 1659723 := bstep (se 1 (by rfl) ⟨1244792, by rfl⟩ : syracuseStep 1659723 = 2489585) B2489585
theorem B1659735 : Blo 1659529 1659735 := bstep (se 1 (by rfl) ⟨1244801, by rfl⟩ : syracuseStep 1659735 = 2489603) B2489603
theorem B1659755 : Blo 1659529 1659755 := bstep (se 1 (by rfl) ⟨1244816, by rfl⟩ : syracuseStep 1659755 = 2489633) B2489633
theorem B1659767 : Blo 1659529 1659767 := bstep (se 1 (by rfl) ⟨1244825, by rfl⟩ : syracuseStep 1659767 = 2489651) B2489651
theorem B3150731 : Blo 1659529 3150731 := bstep (se 1 (by rfl) ⟨2363048, by rfl⟩ : syracuseStep 3150731 = 4726097) B4726097
theorem B1659787 : Blo 1659529 1659787 := bstep (se 1 (by rfl) ⟨1244840, by rfl⟩ : syracuseStep 1659787 = 2489681) B2489681
theorem B1659799 : Blo 1659529 1659799 := bstep (se 1 (by rfl) ⟨1244849, by rfl⟩ : syracuseStep 1659799 = 2489699) B2489699
theorem B1659819 : Blo 1659529 1659819 := bstep (se 1 (by rfl) ⟨1244864, by rfl⟩ : syracuseStep 1659819 = 2489729) B2489729
theorem B1659831 : Blo 1659529 1659831 := bstep (se 1 (by rfl) ⟨1244873, by rfl⟩ : syracuseStep 1659831 = 2489747) B2489747
theorem B5682113 : Blo 1659529 5682113 := bstep (se 2 (by rfl) ⟨2130792, by rfl⟩ : syracuseStep 5682113 = 4261585) B4261585
theorem B1659851 : Blo 1659529 1659851 := bstep (se 1 (by rfl) ⟨1244888, by rfl⟩ : syracuseStep 1659851 = 2489777) B2489777
theorem B1659863 : Blo 1659529 1659863 := bstep (se 1 (by rfl) ⟨1244897, by rfl⟩ : syracuseStep 1659863 = 2489795) B2489795
theorem B5755865 : Blo 1659529 5755865 := bstep (se 2 (by rfl) ⟨2158449, by rfl⟩ : syracuseStep 5755865 = 4316899) B4316899
theorem B1659883 : Blo 1659529 1659883 := bstep (se 1 (by rfl) ⟨1244912, by rfl⟩ : syracuseStep 1659883 = 2489825) B2489825
theorem B1659895 : Blo 1659529 1659895 := bstep (se 1 (by rfl) ⟨1244921, by rfl⟩ : syracuseStep 1659895 = 2489843) B2489843
theorem B1659915 : Blo 1659529 1659915 := bstep (se 1 (by rfl) ⟨1244936, by rfl⟩ : syracuseStep 1659915 = 2489873) B2489873
theorem B18920465 : Blo 1659529 18920465 := bstep (se 2 (by rfl) ⟨7095174, by rfl⟩ : syracuseStep 18920465 = 14190349) B14190349
theorem B1659927 : Blo 1659529 1659927 := bstep (se 1 (by rfl) ⟨1244945, by rfl⟩ : syracuseStep 1659927 = 2489891) B2489891
theorem B1659947 : Blo 1659529 1659947 := bstep (se 1 (by rfl) ⟨1244960, by rfl⟩ : syracuseStep 1659947 = 2489921) B2489921
theorem B1659959 : Blo 1659529 1659959 := bstep (se 1 (by rfl) ⟨1244969, by rfl⟩ : syracuseStep 1659959 = 2489939) B2489939
theorem B3150913 : Blo 1659529 3150913 := bstep (se 2 (by rfl) ⟨1181592, by rfl⟩ : syracuseStep 3150913 = 2363185) B2363185
theorem B1659979 : Blo 1659529 1659979 := bstep (se 1 (by rfl) ⟨1244984, by rfl⟩ : syracuseStep 1659979 = 2489969) B2489969
theorem B1659991 : Blo 1659529 1659991 := bstep (se 1 (by rfl) ⟨1244993, by rfl⟩ : syracuseStep 1659991 = 2489987) B2489987
theorem B1660011 : Blo 1659529 1660011 := bstep (se 1 (by rfl) ⟨1245008, by rfl⟩ : syracuseStep 1660011 = 2490017) B2490017
theorem B1660023 : Blo 1659529 1660023 := bstep (se 1 (by rfl) ⟨1245017, by rfl⟩ : syracuseStep 1660023 = 2490035) B2490035
theorem B1660043 : Blo 1659529 1660043 := bstep (se 1 (by rfl) ⟨1245032, by rfl⟩ : syracuseStep 1660043 = 2490065) B2490065
theorem B1660055 : Blo 1659529 1660055 := bstep (se 1 (by rfl) ⟨1245041, by rfl⟩ : syracuseStep 1660055 = 2490083) B2490083
theorem B1660075 : Blo 1659529 1660075 := bstep (se 1 (by rfl) ⟨1245056, by rfl⟩ : syracuseStep 1660075 = 2490113) B2490113
theorem B1660087 : Blo 1659529 1660087 := bstep (se 1 (by rfl) ⟨1245065, by rfl⟩ : syracuseStep 1660087 = 2490131) B2490131
theorem B1660107 : Blo 1659529 1660107 := bstep (se 1 (by rfl) ⟨1245080, by rfl⟩ : syracuseStep 1660107 = 2490161) B2490161
theorem B1660119 : Blo 1659529 1660119 := bstep (se 1 (by rfl) ⟨1245089, by rfl⟩ : syracuseStep 1660119 = 2490179) B2490179
theorem B6304985 : Blo 1659529 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B1660139 : Blo 1659529 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B1660151 : Blo 1659529 1660151 := bstep (se 1 (by rfl) ⟨1245113, by rfl⟩ : syracuseStep 1660151 = 2490227) B2490227
theorem B1660171 : Blo 1659529 1660171 := bstep (se 1 (by rfl) ⟨1245128, by rfl⟩ : syracuseStep 1660171 = 2490257) B2490257
theorem B3593495 : Blo 1659529 3593495 := bstep (se 1 (by rfl) ⟨2695121, by rfl⟩ : syracuseStep 3593495 = 5390243) B5390243
theorem B1660183 : Blo 1659529 1660183 := bstep (se 1 (by rfl) ⟨1245137, by rfl⟩ : syracuseStep 1660183 = 2490275) B2490275
theorem B1660203 : Blo 1659529 1660203 := bstep (se 1 (by rfl) ⟨1245152, by rfl⟩ : syracuseStep 1660203 = 2490305) B2490305
theorem B1660215 : Blo 1659529 1660215 := bstep (se 1 (by rfl) ⟨1245161, by rfl⟩ : syracuseStep 1660215 = 2490323) B2490323
theorem B8975681 : Blo 1659529 8975681 := bstep (se 2 (by rfl) ⟨3365880, by rfl⟩ : syracuseStep 8975681 = 6731761) B6731761
theorem B1660235 : Blo 1659529 1660235 := bstep (se 1 (by rfl) ⟨1245176, by rfl⟩ : syracuseStep 1660235 = 2490353) B2490353
theorem B1660247 : Blo 1659529 1660247 := bstep (se 1 (by rfl) ⟨1245185, by rfl⟩ : syracuseStep 1660247 = 2490371) B2490371
theorem B1660267 : Blo 1659529 1660267 := bstep (se 1 (by rfl) ⟨1245200, by rfl⟩ : syracuseStep 1660267 = 2490401) B2490401
theorem B1660279 : Blo 1659529 1660279 := bstep (se 1 (by rfl) ⟨1245209, by rfl⟩ : syracuseStep 1660279 = 2490419) B2490419
theorem B1660299 : Blo 1659529 1660299 := bstep (se 1 (by rfl) ⟨1245224, by rfl⟩ : syracuseStep 1660299 = 2490449) B2490449
theorem B1660311 : Blo 1659529 1660311 := bstep (se 1 (by rfl) ⟨1245233, by rfl⟩ : syracuseStep 1660311 = 2490467) B2490467
theorem B1660331 : Blo 1659529 1660331 := bstep (se 1 (by rfl) ⟨1245248, by rfl⟩ : syracuseStep 1660331 = 2490497) B2490497
theorem B1660343 : Blo 1659529 1660343 := bstep (se 1 (by rfl) ⟨1245257, by rfl⟩ : syracuseStep 1660343 = 2490515) B2490515
theorem B1660363 : Blo 1659529 1660363 := bstep (se 1 (by rfl) ⟨1245272, by rfl⟩ : syracuseStep 1660363 = 2490545) B2490545
theorem B4552139 : Blo 1659529 4552139 := bstep (se 1 (by rfl) ⟨3414104, by rfl⟩ : syracuseStep 4552139 = 6828209) B6828209
theorem B1660375 : Blo 1659529 1660375 := bstep (se 1 (by rfl) ⟨1245281, by rfl⟩ : syracuseStep 1660375 = 2490563) B2490563
theorem B1660395 : Blo 1659529 1660395 := bstep (se 1 (by rfl) ⟨1245296, by rfl⟩ : syracuseStep 1660395 = 2490593) B2490593
theorem B1660407 : Blo 1659529 1660407 := bstep (se 1 (by rfl) ⟨1245305, by rfl⟩ : syracuseStep 1660407 = 2490611) B2490611
theorem B3151361 : Blo 1659529 3151361 := bstep (se 2 (by rfl) ⟨1181760, by rfl⟩ : syracuseStep 3151361 = 2363521) B2363521
theorem B1660427 : Blo 1659529 1660427 := bstep (se 1 (by rfl) ⟨1245320, by rfl⟩ : syracuseStep 1660427 = 2490641) B2490641
theorem B1660439 : Blo 1659529 1660439 := bstep (se 1 (by rfl) ⟨1245329, by rfl⟩ : syracuseStep 1660439 = 2490659) B2490659
theorem B6305303 : Blo 1659529 6305303 := bstep (se 1 (by rfl) ⟨4728977, by rfl⟩ : syracuseStep 6305303 = 9457955) B9457955
theorem B1660459 : Blo 1659529 1660459 := bstep (se 1 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 1660459 = 2490689) B2490689
theorem B1660471 : Blo 1659529 1660471 := bstep (se 1 (by rfl) ⟨1245353, by rfl⟩ : syracuseStep 1660471 = 2490707) B2490707
theorem B1660491 : Blo 1659529 1660491 := bstep (se 1 (by rfl) ⟨1245368, by rfl⟩ : syracuseStep 1660491 = 2490737) B2490737
theorem B1660503 : Blo 1659529 1660503 := bstep (se 1 (by rfl) ⟨1245377, by rfl⟩ : syracuseStep 1660503 = 2490755) B2490755
theorem B1660523 : Blo 1659529 1660523 := bstep (se 1 (by rfl) ⟨1245392, by rfl⟩ : syracuseStep 1660523 = 2490785) B2490785
theorem B1660535 : Blo 1659529 1660535 := bstep (se 1 (by rfl) ⟨1245401, by rfl⟩ : syracuseStep 1660535 = 2490803) B2490803
theorem B1660555 : Blo 1659529 1660555 := bstep (se 1 (by rfl) ⟨1245416, by rfl⟩ : syracuseStep 1660555 = 2490833) B2490833
theorem B1660567 : Blo 1659529 1660567 := bstep (se 1 (by rfl) ⟨1245425, by rfl⟩ : syracuseStep 1660567 = 2490851) B2490851
theorem B1660587 : Blo 1659529 1660587 := bstep (se 1 (by rfl) ⟨1245440, by rfl⟩ : syracuseStep 1660587 = 2490881) B2490881
theorem B1660599 : Blo 1659529 1660599 := bstep (se 1 (by rfl) ⟨1245449, by rfl⟩ : syracuseStep 1660599 = 2490899) B2490899
theorem B1660619 : Blo 1659529 1660619 := bstep (se 1 (by rfl) ⟨1245464, by rfl⟩ : syracuseStep 1660619 = 2490929) B2490929
theorem B1660631 : Blo 1659529 1660631 := bstep (se 1 (by rfl) ⟨1245473, by rfl⟩ : syracuseStep 1660631 = 2490947) B2490947
theorem B1660651 : Blo 1659529 1660651 := bstep (se 1 (by rfl) ⟨1245488, by rfl⟩ : syracuseStep 1660651 = 2490977) B2490977
theorem B1660663 : Blo 1659529 1660663 := bstep (se 1 (by rfl) ⟨1245497, by rfl⟩ : syracuseStep 1660663 = 2490995) B2490995
theorem B1660683 : Blo 1659529 1660683 := bstep (se 1 (by rfl) ⟨1245512, by rfl⟩ : syracuseStep 1660683 = 2491025) B2491025
theorem B2365195 : Blo 1659529 2365195 := bstep (se 1 (by rfl) ⟨1773896, by rfl⟩ : syracuseStep 2365195 = 3547793) B3547793
theorem B1660695 : Blo 1659529 1660695 := bstep (se 1 (by rfl) ⟨1245521, by rfl⟩ : syracuseStep 1660695 = 2491043) B2491043
theorem B1660715 : Blo 1659529 1660715 := bstep (se 1 (by rfl) ⟨1245536, by rfl⟩ : syracuseStep 1660715 = 2491073) B2491073
theorem B1660727 : Blo 1659529 1660727 := bstep (se 1 (by rfl) ⟨1245545, by rfl⟩ : syracuseStep 1660727 = 2491091) B2491091
theorem B1660747 : Blo 1659529 1660747 := bstep (se 1 (by rfl) ⟨1245560, by rfl⟩ : syracuseStep 1660747 = 2491121) B2491121
theorem B3151703 : Blo 1659529 3151703 := bstep (se 1 (by rfl) ⟨2363777, by rfl⟩ : syracuseStep 3151703 = 4727555) B4727555
theorem B1660759 : Blo 1659529 1660759 := bstep (se 1 (by rfl) ⟨1245569, by rfl⟩ : syracuseStep 1660759 = 2491139) B2491139
theorem B11974493 : Blo 1659529 11974493 := bstep (se 3 (by rfl) ⟨2245217, by rfl⟩ : syracuseStep 11974493 = 4490435) B4490435
theorem B1660779 : Blo 1659529 1660779 := bstep (se 1 (by rfl) ⟨1245584, by rfl⟩ : syracuseStep 1660779 = 2491169) B2491169
theorem B1660791 : Blo 1659529 1660791 := bstep (se 1 (by rfl) ⟨1245593, by rfl⟩ : syracuseStep 1660791 = 2491187) B2491187
theorem B1660811 : Blo 1659529 1660811 := bstep (se 1 (by rfl) ⟨1245608, by rfl⟩ : syracuseStep 1660811 = 2491217) B2491217
theorem B1660823 : Blo 1659529 1660823 := bstep (se 1 (by rfl) ⟨1245617, by rfl⟩ : syracuseStep 1660823 = 2491235) B2491235
theorem B1660843 : Blo 1659529 1660843 := bstep (se 1 (by rfl) ⟨1245632, by rfl⟩ : syracuseStep 1660843 = 2491265) B2491265
theorem B5601203 : Blo 1659529 5601203 := bstep (se 1 (by rfl) ⟨4200902, by rfl⟩ : syracuseStep 5601203 = 8401805) B8401805
theorem B35903411 : Blo 1659529 35903411 := bstep (se 1 (by rfl) ⟨26927558, by rfl⟩ : syracuseStep 35903411 = 53855117) B53855117
theorem B1660855 : Blo 1659529 1660855 := bstep (se 1 (by rfl) ⟨1245641, by rfl⟩ : syracuseStep 1660855 = 2491283) B2491283
theorem B1660875 : Blo 1659529 1660875 := bstep (se 1 (by rfl) ⟨1245656, by rfl⟩ : syracuseStep 1660875 = 2491313) B2491313
theorem B1660887 : Blo 1659529 1660887 := bstep (se 1 (by rfl) ⟨1245665, by rfl⟩ : syracuseStep 1660887 = 2491331) B2491331
theorem B1660907 : Blo 1659529 1660907 := bstep (se 1 (by rfl) ⟨1245680, by rfl⟩ : syracuseStep 1660907 = 2491361) B2491361
theorem B1660919 : Blo 1659529 1660919 := bstep (se 1 (by rfl) ⟨1245689, by rfl⟩ : syracuseStep 1660919 = 2491379) B2491379
theorem B1660939 : Blo 1659529 1660939 := bstep (se 1 (by rfl) ⟨1245704, by rfl⟩ : syracuseStep 1660939 = 2491409) B2491409
theorem B1660951 : Blo 1659529 1660951 := bstep (se 1 (by rfl) ⟨1245713, by rfl⟩ : syracuseStep 1660951 = 2491427) B2491427
theorem B2365463 : Blo 1659529 2365463 := bstep (se 1 (by rfl) ⟨1774097, by rfl⟩ : syracuseStep 2365463 = 3548195) B3548195
theorem B1660971 : Blo 1659529 1660971 := bstep (se 1 (by rfl) ⟨1245728, by rfl⟩ : syracuseStep 1660971 = 2491457) B2491457
theorem B1660983 : Blo 1659529 1660983 := bstep (se 1 (by rfl) ⟨1245737, by rfl⟩ : syracuseStep 1660983 = 2491475) B2491475
theorem B8411201 : Blo 1659529 8411201 := bstep (se 2 (by rfl) ⟨3154200, by rfl⟩ : syracuseStep 8411201 = 6308401) B6308401
theorem B1661003 : Blo 1659529 1661003 := bstep (se 1 (by rfl) ⟨1245752, by rfl⟩ : syracuseStep 1661003 = 2491505) B2491505
theorem B1661015 : Blo 1659529 1661015 := bstep (se 1 (by rfl) ⟨1245761, by rfl⟩ : syracuseStep 1661015 = 2491523) B2491523
theorem B1661035 : Blo 1659529 1661035 := bstep (se 1 (by rfl) ⟨1245776, by rfl⟩ : syracuseStep 1661035 = 2491553) B2491553
theorem B1661047 : Blo 1659529 1661047 := bstep (se 1 (by rfl) ⟨1245785, by rfl⟩ : syracuseStep 1661047 = 2491571) B2491571
theorem B26941571 : Blo 1659529 26941571 := bstep (se 1 (by rfl) ⟨20206178, by rfl⟩ : syracuseStep 26941571 = 40412357) B40412357
theorem B1661067 : Blo 1659529 1661067 := bstep (se 1 (by rfl) ⟨1245800, by rfl⟩ : syracuseStep 1661067 = 2491601) B2491601
theorem B1661079 : Blo 1659529 1661079 := bstep (se 1 (by rfl) ⟨1245809, by rfl⟩ : syracuseStep 1661079 = 2491619) B2491619
theorem B1661099 : Blo 1659529 1661099 := bstep (se 1 (by rfl) ⟨1245824, by rfl⟩ : syracuseStep 1661099 = 2491649) B2491649
theorem B6305971 : Blo 1659529 6305971 := bstep (se 1 (by rfl) ⟨4729478, by rfl⟩ : syracuseStep 6305971 = 9458957) B9458957
theorem B1661111 : Blo 1659529 1661111 := bstep (se 1 (by rfl) ⟨1245833, by rfl⟩ : syracuseStep 1661111 = 2491667) B2491667
theorem B5601473 : Blo 1659529 5601473 := bstep (se 2 (by rfl) ⟨2100552, by rfl⟩ : syracuseStep 5601473 = 4201105) B4201105
theorem B1661131 : Blo 1659529 1661131 := bstep (se 1 (by rfl) ⟨1245848, by rfl⟩ : syracuseStep 1661131 = 2491697) B2491697
theorem B1661143 : Blo 1659529 1661143 := bstep (se 1 (by rfl) ⟨1245857, by rfl⟩ : syracuseStep 1661143 = 2491715) B2491715
theorem B11229401 : Blo 1659529 11229401 := bstep (se 2 (by rfl) ⟨4211025, by rfl⟩ : syracuseStep 11229401 = 8422051) B8422051
theorem B1661163 : Blo 1659529 1661163 := bstep (se 1 (by rfl) ⟨1245872, by rfl⟩ : syracuseStep 1661163 = 2491745) B2491745
theorem B1661175 : Blo 1659529 1661175 := bstep (se 1 (by rfl) ⟨1245881, by rfl⟩ : syracuseStep 1661175 = 2491763) B2491763
theorem B1661195 : Blo 1659529 1661195 := bstep (se 1 (by rfl) ⟨1245896, by rfl⟩ : syracuseStep 1661195 = 2491793) B2491793
theorem B1661207 : Blo 1659529 1661207 := bstep (se 1 (by rfl) ⟨1245905, by rfl⟩ : syracuseStep 1661207 = 2491811) B2491811
theorem B1661227 : Blo 1659529 1661227 := bstep (se 1 (by rfl) ⟨1245920, by rfl⟩ : syracuseStep 1661227 = 2491841) B2491841
theorem B7575859 : Blo 1659529 7575859 := bstep (se 1 (by rfl) ⟨5681894, by rfl⟩ : syracuseStep 7575859 = 11363789) B11363789
theorem B1661239 : Blo 1659529 1661239 := bstep (se 1 (by rfl) ⟨1245929, by rfl⟩ : syracuseStep 1661239 = 2491859) B2491859
theorem B1661259 : Blo 1659529 1661259 := bstep (se 1 (by rfl) ⟨1245944, by rfl⟩ : syracuseStep 1661259 = 2491889) B2491889
theorem B1661271 : Blo 1659529 1661271 := bstep (se 1 (by rfl) ⟨1245953, by rfl⟩ : syracuseStep 1661271 = 2491907) B2491907
theorem B1661291 : Blo 1659529 1661291 := bstep (se 1 (by rfl) ⟨1245968, by rfl⟩ : syracuseStep 1661291 = 2491937) B2491937
theorem B1661303 : Blo 1659529 1661303 := bstep (se 1 (by rfl) ⟨1245977, by rfl⟩ : syracuseStep 1661303 = 2491955) B2491955
theorem B1661323 : Blo 1659529 1661323 := bstep (se 1 (by rfl) ⟨1245992, by rfl⟩ : syracuseStep 1661323 = 2491985) B2491985
theorem B5757335 : Blo 1659529 5757335 := bstep (se 1 (by rfl) ⟨4318001, by rfl⟩ : syracuseStep 5757335 = 8636003) B8636003
theorem B1661335 : Blo 1659529 1661335 := bstep (se 1 (by rfl) ⟨1246001, by rfl⟩ : syracuseStep 1661335 = 2492003) B2492003
theorem B1661355 : Blo 1659529 1661355 := bstep (se 1 (by rfl) ⟨1246016, by rfl⟩ : syracuseStep 1661355 = 2492033) B2492033
theorem B1661367 : Blo 1659529 1661367 := bstep (se 1 (by rfl) ⟨1246025, by rfl⟩ : syracuseStep 1661367 = 2492051) B2492051
theorem B3545537 : Blo 1659529 3545537 := bstep (se 2 (by rfl) ⟨1329576, by rfl⟩ : syracuseStep 3545537 = 2659153) B2659153
theorem B1661387 : Blo 1659529 1661387 := bstep (se 1 (by rfl) ⟨1246040, by rfl⟩ : syracuseStep 1661387 = 2492081) B2492081
theorem B1661399 : Blo 1659529 1661399 := bstep (se 1 (by rfl) ⟨1246049, by rfl⟩ : syracuseStep 1661399 = 2492099) B2492099
theorem B1661419 : Blo 1659529 1661419 := bstep (se 1 (by rfl) ⟨1246064, by rfl⟩ : syracuseStep 1661419 = 2492129) B2492129
theorem B3152371 : Blo 1659529 3152371 := bstep (se 1 (by rfl) ⟨2364278, by rfl⟩ : syracuseStep 3152371 = 4728557) B4728557
theorem B1661431 : Blo 1659529 1661431 := bstep (se 1 (by rfl) ⟨1246073, by rfl⟩ : syracuseStep 1661431 = 2492147) B2492147
theorem B3734027 : Blo 1659529 3734027 := bstep (se 1 (by rfl) ⟨2800520, by rfl⟩ : syracuseStep 3734027 = 5601041) B5601041
theorem B1661451 : Blo 1659529 1661451 := bstep (se 1 (by rfl) ⟨1246088, by rfl⟩ : syracuseStep 1661451 = 2492177) B2492177
theorem B3545623 : Blo 1659529 3545623 := bstep (se 1 (by rfl) ⟨2659217, by rfl⟩ : syracuseStep 3545623 = 5318435) B5318435
theorem B1661463 : Blo 1659529 1661463 := bstep (se 1 (by rfl) ⟨1246097, by rfl⟩ : syracuseStep 1661463 = 2492195) B2492195
theorem B1661483 : Blo 1659529 1661483 := bstep (se 1 (by rfl) ⟨1246112, by rfl⟩ : syracuseStep 1661483 = 2492225) B2492225
theorem B1661495 : Blo 1659529 1661495 := bstep (se 1 (by rfl) ⟨1246121, by rfl⟩ : syracuseStep 1661495 = 2492243) B2492243
theorem B3734081 : Blo 1659529 3734081 := bstep (se 2 (by rfl) ⟨1400280, by rfl⟩ : syracuseStep 3734081 = 2800561) B2800561
theorem B1661515 : Blo 1659529 1661515 := bstep (se 1 (by rfl) ⟨1246136, by rfl⟩ : syracuseStep 1661515 = 2492273) B2492273
theorem B1661527 : Blo 1659529 1661527 := bstep (se 1 (by rfl) ⟨1246145, by rfl⟩ : syracuseStep 1661527 = 2492291) B2492291
theorem B8403587 : Blo 1659529 8403587 := bstep (se 1 (by rfl) ⟨6302690, by rfl⟩ : syracuseStep 8403587 = 12605381) B12605381
theorem B5602013 : Blo 1659529 5602013 := bstep (se 3 (by rfl) ⟨1050377, by rfl⟩ : syracuseStep 5602013 = 2100755) B2100755
theorem B3734297 : Blo 1659529 3734297 := bstep (se 2 (by rfl) ⟨1400361, by rfl⟩ : syracuseStep 3734297 = 2800723) B2800723
theorem B4201267 : Blo 1659529 4201267 := bstep (se 1 (by rfl) ⟨3150950, by rfl⟩ : syracuseStep 4201267 = 6301901) B6301901
theorem B3734387 : Blo 1659529 3734387 := bstep (se 1 (by rfl) ⟨2800790, by rfl⟩ : syracuseStep 3734387 = 5601581) B5601581
theorem B2243467 : Blo 1659529 2243467 := bstep (se 1 (by rfl) ⟨1682600, by rfl⟩ : syracuseStep 2243467 = 3365201) B3365201
theorem B3734423 : Blo 1659529 3734423 := bstep (se 1 (by rfl) ⟨2800817, by rfl⟩ : syracuseStep 3734423 = 5601635) B5601635
theorem B3152819 : Blo 1659529 3152819 := bstep (se 1 (by rfl) ⟨2364614, by rfl⟩ : syracuseStep 3152819 = 4729229) B4729229
theorem B4201409 : Blo 1659529 4201409 := bstep (se 2 (by rfl) ⟨1575528, by rfl⟩ : syracuseStep 4201409 = 3151057) B3151057
theorem B2489303 : Blo 1659529 2489303 := bstep (se 1 (by rfl) ⟨1866977, by rfl⟩ : syracuseStep 2489303 = 3733955) B3733955
theorem B3152857 : Blo 1659529 3152857 := bstep (se 2 (by rfl) ⟨1182321, by rfl⟩ : syracuseStep 3152857 = 2364643) B2364643
theorem B2489369 : Blo 1659529 2489369 := bstep (se 2 (by rfl) ⟨933513, by rfl⟩ : syracuseStep 2489369 = 1867027) B1867027
theorem B3734603 : Blo 1659529 3734603 := bstep (se 1 (by rfl) ⟨2800952, by rfl⟩ : syracuseStep 3734603 = 5601905) B5601905
theorem B3734657 : Blo 1659529 3734657 := bstep (se 2 (by rfl) ⟨1400496, by rfl⟩ : syracuseStep 3734657 = 2800993) B2800993
theorem B7978115 : Blo 1659529 7978115 := bstep (se 1 (by rfl) ⟨5983586, by rfl⟩ : syracuseStep 7978115 = 11967173) B11967173
theorem B2489483 : Blo 1659529 2489483 := bstep (se 1 (by rfl) ⟨1867112, by rfl⟩ : syracuseStep 2489483 = 3734225) B3734225
theorem B2489495 : Blo 1659529 2489495 := bstep (se 1 (by rfl) ⟨1867121, by rfl⟩ : syracuseStep 2489495 = 3734243) B3734243
theorem B3988673 : Blo 1659529 3988673 := bstep (se 2 (by rfl) ⟨1495752, by rfl⟩ : syracuseStep 3988673 = 2991505) B2991505
theorem B2489561 : Blo 1659529 2489561 := bstep (se 2 (by rfl) ⟨933585, by rfl⟩ : syracuseStep 2489561 = 1867171) B1867171
theorem B4726039 : Blo 1659529 4726039 := bstep (se 1 (by rfl) ⟨3544529, by rfl⟩ : syracuseStep 4726039 = 7089059) B7089059
theorem B2800919 : Blo 1659529 2800919 := bstep (se 1 (by rfl) ⟨2100689, by rfl⟩ : syracuseStep 2800919 = 4201379) B4201379
theorem B1867063 : Blo 1659529 1867063 := bstep (se 1 (by rfl) ⟨1400297, by rfl⟩ : syracuseStep 1867063 = 2800595) B2800595
theorem B2489675 : Blo 1659529 2489675 := bstep (se 1 (by rfl) ⟨1867256, by rfl⟩ : syracuseStep 2489675 = 3734513) B3734513
theorem B3546443 : Blo 1659529 3546443 := bstep (se 1 (by rfl) ⟨2659832, by rfl⟩ : syracuseStep 3546443 = 5319665) B5319665
theorem B2489687 : Blo 1659529 2489687 := bstep (se 1 (by rfl) ⟨1867265, by rfl⟩ : syracuseStep 2489687 = 3734531) B3734531
theorem B3734873 : Blo 1659529 3734873 := bstep (se 2 (by rfl) ⟨1400577, by rfl⟩ : syracuseStep 3734873 = 2801155) B2801155
theorem B9461123 : Blo 1659529 9461123 := bstep (se 1 (by rfl) ⟨7095842, by rfl⟩ : syracuseStep 9461123 = 14191685) B14191685
theorem B6307217 : Blo 1659529 6307217 := bstep (se 2 (by rfl) ⟨2365206, by rfl⟩ : syracuseStep 6307217 = 4730413) B4730413
theorem B2694551 : Blo 1659529 2694551 := bstep (se 1 (by rfl) ⟨2020913, by rfl⟩ : syracuseStep 2694551 = 4041827) B4041827
theorem B2801047 : Blo 1659529 2801047 := bstep (se 1 (by rfl) ⟨2100785, by rfl⟩ : syracuseStep 2801047 = 4201571) B4201571
theorem B2489753 : Blo 1659529 2489753 := bstep (se 2 (by rfl) ⟨933657, by rfl⟩ : syracuseStep 2489753 = 1867315) B1867315
theorem B3153305 : Blo 1659529 3153305 := bstep (se 2 (by rfl) ⟨1182489, by rfl⟩ : syracuseStep 3153305 = 2364979) B2364979
theorem B3734963 : Blo 1659529 3734963 := bstep (se 1 (by rfl) ⟨2801222, by rfl⟩ : syracuseStep 3734963 = 5602445) B5602445
theorem B10100147 : Blo 1659529 10100147 := bstep (se 1 (by rfl) ⟨7575110, by rfl⟩ : syracuseStep 10100147 = 15150221) B15150221
theorem B3734999 : Blo 1659529 3734999 := bstep (se 1 (by rfl) ⟨2801249, by rfl⟩ : syracuseStep 3734999 = 5602499) B5602499
theorem B1867243 : Blo 1659529 1867243 := bstep (se 1 (by rfl) ⟨1400432, by rfl⟩ : syracuseStep 1867243 = 2800865) B2800865
theorem B2489867 : Blo 1659529 2489867 := bstep (se 1 (by rfl) ⟨1867400, by rfl⟩ : syracuseStep 2489867 = 3734801) B3734801
theorem B2489879 : Blo 1659529 2489879 := bstep (se 1 (by rfl) ⟨1867409, by rfl⟩ : syracuseStep 2489879 = 3734819) B3734819
theorem B1867351 : Blo 1659529 1867351 := bstep (se 1 (by rfl) ⟨1400513, by rfl⟩ : syracuseStep 1867351 = 2801027) B2801027
theorem B2489945 : Blo 1659529 2489945 := bstep (se 2 (by rfl) ⟨933729, by rfl⟩ : syracuseStep 2489945 = 1867459) B1867459
theorem B3735179 : Blo 1659529 3735179 := bstep (se 1 (by rfl) ⟨2801384, by rfl⟩ : syracuseStep 3735179 = 5602769) B5602769
theorem B3735233 : Blo 1659529 3735233 := bstep (se 2 (by rfl) ⟨1400712, by rfl⟩ : syracuseStep 3735233 = 2801425) B2801425
theorem B2490059 : Blo 1659529 2490059 := bstep (se 1 (by rfl) ⟨1867544, by rfl⟩ : syracuseStep 2490059 = 3735089) B3735089
theorem B40402637 : Blo 1659529 40402637 := bstep (se 3 (by rfl) ⟨7575494, by rfl⟩ : syracuseStep 40402637 = 15150989) B15150989
theorem B2490071 : Blo 1659529 2490071 := bstep (se 1 (by rfl) ⟨1867553, by rfl⟩ : syracuseStep 2490071 = 3735107) B3735107
theorem B1867531 : Blo 1659529 1867531 := bstep (se 1 (by rfl) ⟨1400648, by rfl⟩ : syracuseStep 1867531 = 2801297) B2801297
theorem B7978769 : Blo 1659529 7978769 := bstep (se 2 (by rfl) ⟨2992038, by rfl⟩ : syracuseStep 7978769 = 5984077) B5984077
theorem B5988113 : Blo 1659529 5988113 := bstep (se 2 (by rfl) ⟨2245542, by rfl⟩ : syracuseStep 5988113 = 4491085) B4491085
theorem B2490137 : Blo 1659529 2490137 := bstep (se 2 (by rfl) ⟨933801, by rfl⟩ : syracuseStep 2490137 = 1867603) B1867603
theorem B7094081 : Blo 1659529 7094081 := bstep (se 2 (by rfl) ⟨2660280, by rfl⟩ : syracuseStep 7094081 = 5320561) B5320561
theorem B5603147 : Blo 1659529 5603147 := bstep (se 1 (by rfl) ⟨4202360, by rfl⟩ : syracuseStep 5603147 = 8404721) B8404721
theorem B12607325 : Blo 1659529 12607325 := bstep (se 3 (by rfl) ⟨2363873, by rfl⟩ : syracuseStep 12607325 = 4727747) B4727747
theorem B1867639 : Blo 1659529 1867639 := bstep (se 1 (by rfl) ⟨1400729, by rfl⟩ : syracuseStep 1867639 = 2801459) B2801459
theorem B18923381 : Blo 1659529 18923381 := bstep (se 5 (by rfl) ⟨887033, by rfl⟩ : syracuseStep 18923381 = 1774067) B1774067
theorem B2490251 : Blo 1659529 2490251 := bstep (se 1 (by rfl) ⟨1867688, by rfl⟩ : syracuseStep 2490251 = 3735377) B3735377
theorem B2490263 : Blo 1659529 2490263 := bstep (se 1 (by rfl) ⟨1867697, by rfl⟩ : syracuseStep 2490263 = 3735395) B3735395
theorem B3735449 : Blo 1659529 3735449 := bstep (se 2 (by rfl) ⟨1400793, by rfl⟩ : syracuseStep 3735449 = 2801587) B2801587
theorem B4726745 : Blo 1659529 4726745 := bstep (se 2 (by rfl) ⟨1772529, by rfl⟩ : syracuseStep 4726745 = 3545059) B3545059
theorem B2490329 : Blo 1659529 2490329 := bstep (se 2 (by rfl) ⟨933873, by rfl⟩ : syracuseStep 2490329 = 1867747) B1867747
theorem B60612569 : Blo 1659529 60612569 := bstep (se 2 (by rfl) ⟨22729713, by rfl⟩ : syracuseStep 60612569 = 45459427) B45459427
theorem B3735539 : Blo 1659529 3735539 := bstep (se 1 (by rfl) ⟨2801654, by rfl⟩ : syracuseStep 3735539 = 5603309) B5603309
theorem B1867783 : Blo 1659529 1867783 := bstep (se 1 (by rfl) ⟨1400837, by rfl⟩ : syracuseStep 1867783 = 2801675) B2801675
theorem B2490383 : Blo 1659529 2490383 := bstep (se 1 (by rfl) ⟨1867787, by rfl⟩ : syracuseStep 2490383 = 3735575) B3735575
theorem B2490425 : Blo 1659529 2490425 := bstep (se 2 (by rfl) ⟨933909, by rfl⟩ : syracuseStep 2490425 = 1867819) B1867819
theorem B3735611 : Blo 1659529 3735611 := bstep (se 1 (by rfl) ⟨2801708, by rfl⟩ : syracuseStep 3735611 = 5603417) B5603417
theorem B2244667 : Blo 1659529 2244667 := bstep (se 1 (by rfl) ⟨1683500, by rfl⟩ : syracuseStep 2244667 = 3367001) B3367001
theorem B6307901 : Blo 1659529 6307901 := bstep (se 3 (by rfl) ⟨1182731, by rfl⟩ : syracuseStep 6307901 = 2365463) B2365463
theorem B2801783 : Blo 1659529 2801783 := bstep (se 1 (by rfl) ⟨2101337, by rfl⟩ : syracuseStep 2801783 = 4202675) B4202675
theorem B2490503 : Blo 1659529 2490503 := bstep (se 1 (by rfl) ⟨1867877, by rfl⟩ : syracuseStep 2490503 = 3735755) B3735755
theorem B2490539 : Blo 1659529 2490539 := bstep (se 1 (by rfl) ⟨1867904, by rfl⟩ : syracuseStep 2490539 = 3735809) B3735809
theorem B15949997 : Blo 1659529 15949997 := bstep (se 3 (by rfl) ⟨2990624, by rfl⟩ : syracuseStep 15949997 = 5981249) B5981249
theorem B3735737 : Blo 1659529 3735737 := bstep (se 2 (by rfl) ⟨1400901, by rfl⟩ : syracuseStep 3735737 = 2801803) B2801803
theorem B1867963 : Blo 1659529 1867963 := bstep (se 1 (by rfl) ⟨1400972, by rfl⟩ : syracuseStep 1867963 = 2801945) B2801945
theorem B2490569 : Blo 1659529 2490569 := bstep (se 2 (by rfl) ⟨933963, by rfl⟩ : syracuseStep 2490569 = 1867927) B1867927
theorem B4260107 : Blo 1659529 4260107 := bstep (se 1 (by rfl) ⟨3195080, by rfl⟩ : syracuseStep 4260107 = 6390161) B6390161
theorem B5046571 : Blo 1659529 5046571 := bstep (se 1 (by rfl) ⟨3784928, by rfl⟩ : syracuseStep 5046571 = 7569857) B7569857
theorem B4727099 : Blo 1659529 4727099 := bstep (se 1 (by rfl) ⟨3545324, by rfl⟩ : syracuseStep 4727099 = 7090649) B7090649
theorem B2490683 : Blo 1659529 2490683 := bstep (se 1 (by rfl) ⟨1868012, by rfl⟩ : syracuseStep 2490683 = 3736025) B3736025
theorem B3547451 : Blo 1659529 3547451 := bstep (se 1 (by rfl) ⟨2660588, by rfl⟩ : syracuseStep 3547451 = 5321177) B5321177
theorem B2244937 : Blo 1659529 2244937 := bstep (se 2 (by rfl) ⟨841851, by rfl⟩ : syracuseStep 2244937 = 1683703) B1683703
theorem B4727155 : Blo 1659529 4727155 := bstep (se 1 (by rfl) ⟨3545366, by rfl⟩ : syracuseStep 4727155 = 7090733) B7090733
theorem B4202867 : Blo 1659529 4202867 := bstep (se 1 (by rfl) ⟨3152150, by rfl⟩ : syracuseStep 4202867 = 6304301) B6304301
theorem B2490743 : Blo 1659529 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B4202887 : Blo 1659529 4202887 := bstep (se 1 (by rfl) ⟨3152165, by rfl⟩ : syracuseStep 4202887 = 6304331) B6304331
theorem B2490767 : Blo 1659529 2490767 := bstep (se 1 (by rfl) ⟨1868075, by rfl⟩ : syracuseStep 2490767 = 3736151) B3736151
theorem B10101145 : Blo 1659529 10101145 := bstep (se 2 (by rfl) ⟨3787929, by rfl⟩ : syracuseStep 10101145 = 7575859) B7575859
theorem B15958457 : Blo 1659529 15958457 := bstep (se 2 (by rfl) ⟨5984421, by rfl⟩ : syracuseStep 15958457 = 11968843) B11968843
theorem B2490809 : Blo 1659529 2490809 := bstep (se 2 (by rfl) ⟨934053, by rfl⟩ : syracuseStep 2490809 = 1868107) B1868107
theorem B2490887 : Blo 1659529 2490887 := bstep (se 1 (by rfl) ⟨1868165, by rfl⟩ : syracuseStep 2490887 = 3736331) B3736331
theorem B3785231 : Blo 1659529 3785231 := bstep (se 1 (by rfl) ⟨2838923, by rfl⟩ : syracuseStep 3785231 = 5677847) B5677847
theorem B3736079 : Blo 1659529 3736079 := bstep (se 1 (by rfl) ⟨2802059, by rfl⟩ : syracuseStep 3736079 = 5604119) B5604119
theorem B3736097 : Blo 1659529 3736097 := bstep (se 2 (by rfl) ⟨1401036, by rfl⟩ : syracuseStep 3736097 = 2802073) B2802073
theorem B2490923 : Blo 1659529 2490923 := bstep (se 1 (by rfl) ⟨1868192, by rfl⟩ : syracuseStep 2490923 = 3736385) B3736385
theorem B2802235 : Blo 1659529 2802235 := bstep (se 1 (by rfl) ⟨2101676, by rfl⟩ : syracuseStep 2802235 = 4203353) B4203353
theorem B2490953 : Blo 1659529 2490953 := bstep (se 2 (by rfl) ⟨934107, by rfl⟩ : syracuseStep 2490953 = 1868215) B1868215
theorem B1868431 : Blo 1659529 1868431 := bstep (se 1 (by rfl) ⟨1401323, by rfl⟩ : syracuseStep 1868431 = 2802647) B2802647
theorem B4203161 : Blo 1659529 4203161 := bstep (se 2 (by rfl) ⟨1576185, by rfl⟩ : syracuseStep 4203161 = 3152371) B3152371
theorem B2491067 : Blo 1659529 2491067 := bstep (se 1 (by rfl) ⟨1868300, by rfl⟩ : syracuseStep 2491067 = 3736601) B3736601
theorem B4547273 : Blo 1659529 4547273 := bstep (se 2 (by rfl) ⟨1705227, by rfl⟩ : syracuseStep 4547273 = 3410455) B3410455
theorem B4727497 : Blo 1659529 4727497 := bstep (se 2 (by rfl) ⟨1772811, by rfl⟩ : syracuseStep 4727497 = 3545623) B3545623
theorem B2802377 : Blo 1659529 2802377 := bstep (se 2 (by rfl) ⟨1050891, by rfl⟩ : syracuseStep 2802377 = 2101783) B2101783
theorem B2491127 : Blo 1659529 2491127 := bstep (se 1 (by rfl) ⟨1868345, by rfl⟩ : syracuseStep 2491127 = 3736691) B3736691
theorem B2491151 : Blo 1659529 2491151 := bstep (se 1 (by rfl) ⟨1868363, by rfl⟩ : syracuseStep 2491151 = 3736727) B3736727
theorem B7095073 : Blo 1659529 7095073 := bstep (se 2 (by rfl) ⟨2660652, by rfl⟩ : syracuseStep 7095073 = 5321305) B5321305
theorem B2491193 : Blo 1659529 2491193 := bstep (se 2 (by rfl) ⟨934197, by rfl⟩ : syracuseStep 2491193 = 1868395) B1868395
theorem B4203323 : Blo 1659529 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B3736439 : Blo 1659529 3736439 := bstep (se 1 (by rfl) ⟨2802329, by rfl⟩ : syracuseStep 3736439 = 5604659) B5604659
theorem B2491271 : Blo 1659529 2491271 := bstep (se 1 (by rfl) ⟨1868453, by rfl⟩ : syracuseStep 2491271 = 3736907) B3736907
theorem B2491307 : Blo 1659529 2491307 := bstep (se 1 (by rfl) ⟨1868480, by rfl⟩ : syracuseStep 2491307 = 3736961) B3736961
theorem B5604281 : Blo 1659529 5604281 := bstep (se 2 (by rfl) ⟨2101605, by rfl⟩ : syracuseStep 5604281 = 4203211) B4203211
theorem B2491337 : Blo 1659529 2491337 := bstep (se 2 (by rfl) ⟨934251, by rfl⟩ : syracuseStep 2491337 = 1868503) B1868503
theorem B4203535 : Blo 1659529 4203535 := bstep (se 1 (by rfl) ⟨3152651, by rfl⟩ : syracuseStep 4203535 = 6305303) B6305303
theorem B6824989 : Blo 1659529 6824989 := bstep (se 3 (by rfl) ⟨1279685, by rfl⟩ : syracuseStep 6824989 = 2559371) B2559371
theorem B3736619 : Blo 1659529 3736619 := bstep (se 1 (by rfl) ⟨2802464, by rfl⟩ : syracuseStep 3736619 = 5604929) B5604929
theorem B2491451 : Blo 1659529 2491451 := bstep (se 1 (by rfl) ⟨1868588, by rfl⟩ : syracuseStep 2491451 = 3737177) B3737177
theorem B7185469 : Blo 1659529 7185469 := bstep (se 3 (by rfl) ⟨1347275, by rfl⟩ : syracuseStep 7185469 = 2694551) B2694551
theorem B2491511 : Blo 1659529 2491511 := bstep (se 1 (by rfl) ⟨1868633, by rfl⟩ : syracuseStep 2491511 = 3737267) B3737267
theorem B1868935 : Blo 1659529 1868935 := bstep (se 1 (by rfl) ⟨1401701, by rfl⟩ : syracuseStep 1868935 = 2803403) B2803403
theorem B2491535 : Blo 1659529 2491535 := bstep (se 1 (by rfl) ⟨1868651, by rfl⟩ : syracuseStep 2491535 = 3737303) B3737303
theorem B9454765 : Blo 1659529 9454765 := bstep (se 3 (by rfl) ⟨1772768, by rfl⟩ : syracuseStep 9454765 = 3545537) B3545537
theorem B2991289 : Blo 1659529 2991289 := bstep (se 2 (by rfl) ⟨1121733, by rfl⟩ : syracuseStep 2991289 = 2243467) B2243467
theorem B2491577 : Blo 1659529 2491577 := bstep (se 2 (by rfl) ⟨934341, by rfl⟩ : syracuseStep 2491577 = 1868683) B1868683
theorem B2491655 : Blo 1659529 2491655 := bstep (se 1 (by rfl) ⟨1868741, by rfl⟩ : syracuseStep 2491655 = 3737483) B3737483
theorem B4203809 : Blo 1659529 4203809 := bstep (se 2 (by rfl) ⟨1576428, by rfl⟩ : syracuseStep 4203809 = 3152857) B3152857
theorem B2491691 : Blo 1659529 2491691 := bstep (se 1 (by rfl) ⟨1868768, by rfl⟩ : syracuseStep 2491691 = 3737537) B3737537
theorem B1869115 : Blo 1659529 1869115 := bstep (se 1 (by rfl) ⟨1401836, by rfl⟩ : syracuseStep 1869115 = 2803673) B2803673
theorem B2491721 : Blo 1659529 2491721 := bstep (se 2 (by rfl) ⟨934395, by rfl⟩ : syracuseStep 2491721 = 1868791) B1868791
theorem B2803079 : Blo 1659529 2803079 := bstep (se 1 (by rfl) ⟨2102309, by rfl⟩ : syracuseStep 2803079 = 4204619) B4204619
theorem B3736979 : Blo 1659529 3736979 := bstep (se 1 (by rfl) ⟨2802734, by rfl⟩ : syracuseStep 3736979 = 5605469) B5605469
theorem B2491835 : Blo 1659529 2491835 := bstep (se 1 (by rfl) ⟨1868876, by rfl⟩ : syracuseStep 2491835 = 3737753) B3737753
theorem B3737033 : Blo 1659529 3737033 := bstep (se 2 (by rfl) ⟨1401387, by rfl⟩ : syracuseStep 3737033 = 2802775) B2802775
theorem B2491895 : Blo 1659529 2491895 := bstep (se 1 (by rfl) ⟨1868921, by rfl⟩ : syracuseStep 2491895 = 3737843) B3737843
theorem B5604875 : Blo 1659529 5604875 := bstep (se 1 (by rfl) ⟨4203656, by rfl⟩ : syracuseStep 5604875 = 8407313) B8407313
theorem B2491919 : Blo 1659529 2491919 := bstep (se 1 (by rfl) ⟨1868939, by rfl⟩ : syracuseStep 2491919 = 3737879) B3737879
theorem B2491961 : Blo 1659529 2491961 := bstep (se 2 (by rfl) ⟨934485, by rfl⟩ : syracuseStep 2491961 = 1868971) B1868971
theorem B5604983 : Blo 1659529 5604983 := bstep (se 1 (by rfl) ⟨4203737, by rfl⟩ : syracuseStep 5604983 = 8407475) B8407475
theorem B2492039 : Blo 1659529 2492039 := bstep (se 1 (by rfl) ⟨1869029, by rfl⟩ : syracuseStep 2492039 = 3738059) B3738059
theorem B2492075 : Blo 1659529 2492075 := bstep (se 1 (by rfl) ⟨1869056, by rfl⟩ : syracuseStep 2492075 = 3738113) B3738113
theorem B6301385 : Blo 1659529 6301385 := bstep (se 2 (by rfl) ⟨2363019, by rfl⟩ : syracuseStep 6301385 = 4726039) B4726039
theorem B2492105 : Blo 1659529 2492105 := bstep (se 2 (by rfl) ⟨934539, by rfl⟩ : syracuseStep 2492105 = 1869079) B1869079
theorem B30295781 : Blo 1659529 30295781 := bstep (se 4 (by rfl) ⟨2840229, by rfl⟩ : syracuseStep 30295781 = 5680459) B5680459
theorem B2492219 : Blo 1659529 2492219 := bstep (se 1 (by rfl) ⟨1869164, by rfl⟩ : syracuseStep 2492219 = 3738329) B3738329
theorem B2492279 : Blo 1659529 2492279 := bstep (se 1 (by rfl) ⟨1869209, by rfl⟩ : syracuseStep 2492279 = 3738419) B3738419
theorem B2803727 : Blo 1659529 2803727 := bstep (se 1 (by rfl) ⟨2102795, by rfl⟩ : syracuseStep 2803727 = 4205591) B4205591
theorem B5318743 : Blo 1659529 5318743 := bstep (se 1 (by rfl) ⟨3989057, by rfl⟩ : syracuseStep 5318743 = 7978115) B7978115
theorem B3737735 : Blo 1659529 3737735 := bstep (se 1 (by rfl) ⟨2803301, by rfl⟩ : syracuseStep 3737735 = 5606603) B5606603
theorem B18917549 : Blo 1659529 18917549 := bstep (se 3 (by rfl) ⟨3547040, by rfl⟩ : syracuseStep 18917549 = 7094081) B7094081
theorem B5605577 : Blo 1659529 5605577 := bstep (se 2 (by rfl) ⟨2102091, by rfl⟩ : syracuseStep 5605577 = 4204183) B4204183
theorem B4204811 : Blo 1659529 4204811 := bstep (se 1 (by rfl) ⟨3153608, by rfl⟩ : syracuseStep 4204811 = 6307217) B6307217
theorem B3737915 : Blo 1659529 3737915 := bstep (se 1 (by rfl) ⟨2803436, by rfl⟩ : syracuseStep 3737915 = 5606873) B5606873
theorem B3410311 : Blo 1659529 3410311 := bstep (se 1 (by rfl) ⟨2557733, by rfl⟩ : syracuseStep 3410311 = 5115467) B5115467
theorem B3738041 : Blo 1659529 3738041 := bstep (se 2 (by rfl) ⟨1401765, by rfl⟩ : syracuseStep 3738041 = 2803531) B2803531
theorem B5319179 : Blo 1659529 5319179 := bstep (se 1 (by rfl) ⟨3989384, by rfl⟩ : syracuseStep 5319179 = 7978769) B7978769
theorem B3992075 : Blo 1659529 3992075 := bstep (se 1 (by rfl) ⟨2994056, by rfl⟩ : syracuseStep 3992075 = 5988113) B5988113
theorem B5319229 : Blo 1659529 5319229 := bstep (se 3 (by rfl) ⟨997355, by rfl⟩ : syracuseStep 5319229 = 1994711) B1994711
theorem B12610241 : Blo 1659529 12610241 := bstep (se 2 (by rfl) ⟨4728840, by rfl⟩ : syracuseStep 12610241 = 9457681) B9457681
theorem B13470401 : Blo 1659529 13470401 := bstep (se 2 (by rfl) ⟨5051400, by rfl⟩ : syracuseStep 13470401 = 10102801) B10102801
theorem B3738383 : Blo 1659529 3738383 := bstep (se 1 (by rfl) ⟨2803787, by rfl⟩ : syracuseStep 3738383 = 5607575) B5607575
theorem B3738401 : Blo 1659529 3738401 := bstep (se 2 (by rfl) ⟨1401900, by rfl⟩ : syracuseStep 3738401 = 2803801) B2803801
theorem B4729661 : Blo 1659529 4729661 := bstep (se 3 (by rfl) ⟨886811, by rfl⟩ : syracuseStep 4729661 = 1773623) B1773623
theorem B5606279 : Blo 1659529 5606279 := bstep (se 1 (by rfl) ⟨4204709, by rfl⟩ : syracuseStep 5606279 = 8409419) B8409419
theorem B4205459 : Blo 1659529 4205459 := bstep (se 1 (by rfl) ⟨3154094, by rfl⟩ : syracuseStep 4205459 = 6308189) B6308189
theorem B8407961 : Blo 1659529 8407961 := bstep (se 2 (by rfl) ⟨3152985, by rfl⟩ : syracuseStep 8407961 = 6305971) B6305971
theorem B4729889 : Blo 1659529 4729889 := bstep (se 2 (by rfl) ⟨1773708, by rfl⟩ : syracuseStep 4729889 = 3547417) B3547417
theorem B4795577 : Blo 1659529 4795577 := bstep (se 2 (by rfl) ⟨1798341, by rfl⟩ : syracuseStep 4795577 = 3596683) B3596683
theorem B5606657 : Blo 1659529 5606657 := bstep (se 2 (by rfl) ⟨2102496, by rfl⟩ : syracuseStep 5606657 = 4204993) B4204993
theorem B2100487 : Blo 1659529 2100487 := bstep (se 1 (by rfl) ⟨1575365, by rfl⟩ : syracuseStep 2100487 = 3150731) B3150731
theorem B3788075 : Blo 1659529 3788075 := bstep (se 1 (by rfl) ⟨2841056, by rfl⟩ : syracuseStep 3788075 = 5682113) B5682113
theorem B4730231 : Blo 1659529 4730231 := bstep (se 1 (by rfl) ⟨3547673, by rfl⟩ : syracuseStep 4730231 = 7095347) B7095347
theorem B2395663 : Blo 1659529 2395663 := bstep (se 1 (by rfl) ⟨1796747, by rfl⟩ : syracuseStep 2395663 = 3593495) B3593495
theorem B9457181 : Blo 1659529 9457181 := bstep (se 3 (by rfl) ⟨1773221, by rfl⟩ : syracuseStep 9457181 = 3546443) B3546443
theorem B7089707 : Blo 1659529 7089707 := bstep (se 1 (by rfl) ⟨5317280, by rfl⟩ : syracuseStep 7089707 = 10634561) B10634561
theorem B5983787 : Blo 1659529 5983787 := bstep (se 1 (by rfl) ⟨4487840, by rfl⟩ : syracuseStep 5983787 = 8975681) B8975681
theorem B2395705 : Blo 1659529 2395705 := bstep (se 2 (by rfl) ⟨898389, by rfl⟩ : syracuseStep 2395705 = 1796779) B1796779
theorem B5049917 : Blo 1659529 5049917 := bstep (se 3 (by rfl) ⟨946859, by rfl⟩ : syracuseStep 5049917 = 1893719) B1893719
theorem B2100907 : Blo 1659529 2100907 := bstep (se 1 (by rfl) ⟨1575680, by rfl⟩ : syracuseStep 2100907 = 3151361) B3151361
theorem B23949107 : Blo 1659529 23949107 := bstep (se 1 (by rfl) ⟨17961830, by rfl⟩ : syracuseStep 23949107 = 35923661) B35923661
theorem B2101135 : Blo 1659529 2101135 := bstep (se 1 (by rfl) ⟨1575851, by rfl⟩ : syracuseStep 2101135 = 3151703) B3151703
theorem B7982995 : Blo 1659529 7982995 := bstep (se 1 (by rfl) ⟨5987246, by rfl⟩ : syracuseStep 7982995 = 11974493) B11974493
theorem B4042763 : Blo 1659529 4042763 := bstep (se 1 (by rfl) ⟨3032072, by rfl⟩ : syracuseStep 4042763 = 6064145) B6064145
theorem B5607467 : Blo 1659529 5607467 := bstep (se 1 (by rfl) ⟨4205600, by rfl⟩ : syracuseStep 5607467 = 8411201) B8411201
theorem B17961047 : Blo 1659529 17961047 := bstep (se 1 (by rfl) ⟨13470785, by rfl⟩ : syracuseStep 17961047 = 26941571) B26941571
theorem B5320961 : Blo 1659529 5320961 := bstep (se 2 (by rfl) ⟨1995360, by rfl⟩ : syracuseStep 5320961 = 3990721) B3990721
theorem B3838223 : Blo 1659529 3838223 := bstep (se 1 (by rfl) ⟨2878667, by rfl⟩ : syracuseStep 3838223 = 5757335) B5757335
theorem B5681593 : Blo 1659529 5681593 := bstep (se 2 (by rfl) ⟨2130597, by rfl⟩ : syracuseStep 5681593 = 4261195) B4261195
theorem B7090699 : Blo 1659529 7090699 := bstep (se 1 (by rfl) ⟨5318024, by rfl⟩ : syracuseStep 7090699 = 10636049) B10636049
theorem B2101879 : Blo 1659529 2101879 := bstep (se 1 (by rfl) ⟨1576409, by rfl⟩ : syracuseStep 2101879 = 3152819) B3152819
theorem B5468791 : Blo 1659529 5468791 := bstep (se 1 (by rfl) ⟨4101593, by rfl⟩ : syracuseStep 5468791 = 8203187) B8203187
theorem B1659535 : Blo 1659529 1659535 := bstep (se 1 (by rfl) ⟨1244651, by rfl⟩ : syracuseStep 1659535 = 2489303) B2489303
theorem B1659579 : Blo 1659529 1659579 := bstep (se 1 (by rfl) ⟨1244684, by rfl⟩ : syracuseStep 1659579 = 2489369) B2489369
theorem B34550489 : Blo 1659529 34550489 := bstep (se 2 (by rfl) ⟨12956433, by rfl⟩ : syracuseStep 34550489 = 25912867) B25912867
theorem B6304513 : Blo 1659529 6304513 := bstep (se 2 (by rfl) ⟨2364192, by rfl⟩ : syracuseStep 6304513 = 4728385) B4728385
theorem B1659655 : Blo 1659529 1659655 := bstep (se 1 (by rfl) ⟨1244741, by rfl⟩ : syracuseStep 1659655 = 2489483) B2489483
theorem B1659663 : Blo 1659529 1659663 := bstep (se 1 (by rfl) ⟨1244747, by rfl⟩ : syracuseStep 1659663 = 2489495) B2489495
theorem B8975141 : Blo 1659529 8975141 := bstep (se 4 (by rfl) ⟨841419, by rfl⟩ : syracuseStep 8975141 = 1682839) B1682839
theorem B2659115 : Blo 1659529 2659115 := bstep (se 1 (by rfl) ⟨1994336, by rfl⟩ : syracuseStep 2659115 = 3988673) B3988673
theorem B1659707 : Blo 1659529 1659707 := bstep (se 1 (by rfl) ⟨1244780, by rfl⟩ : syracuseStep 1659707 = 2489561) B2489561
theorem B1659783 : Blo 1659529 1659783 := bstep (se 1 (by rfl) ⟨1244837, by rfl⟩ : syracuseStep 1659783 = 2489675) B2489675
theorem B1659791 : Blo 1659529 1659791 := bstep (se 1 (by rfl) ⟨1244843, by rfl⟩ : syracuseStep 1659791 = 2489687) B2489687
theorem B61395893 : Blo 1659529 61395893 := bstep (se 5 (by rfl) ⟨2877932, by rfl⟩ : syracuseStep 61395893 = 5755865) B5755865
theorem B1659835 : Blo 1659529 1659835 := bstep (se 1 (by rfl) ⟨1244876, by rfl⟩ : syracuseStep 1659835 = 2489753) B2489753
theorem B2102203 : Blo 1659529 2102203 := bstep (se 1 (by rfl) ⟨1576652, by rfl⟩ : syracuseStep 2102203 = 3153305) B3153305
theorem B1659911 : Blo 1659529 1659911 := bstep (se 1 (by rfl) ⟨1244933, by rfl⟩ : syracuseStep 1659911 = 2489867) B2489867
theorem B1659919 : Blo 1659529 1659919 := bstep (se 1 (by rfl) ⟨1244939, by rfl⟩ : syracuseStep 1659919 = 2489879) B2489879
theorem B4486187 : Blo 1659529 4486187 := bstep (se 1 (by rfl) ⟨3364640, by rfl⟩ : syracuseStep 4486187 = 6729281) B6729281
theorem B1659963 : Blo 1659529 1659963 := bstep (se 1 (by rfl) ⟨1244972, by rfl⟩ : syracuseStep 1659963 = 2489945) B2489945
theorem B1660039 : Blo 1659529 1660039 := bstep (se 1 (by rfl) ⟨1245029, by rfl⟩ : syracuseStep 1660039 = 2490059) B2490059
theorem B1660047 : Blo 1659529 1660047 := bstep (se 1 (by rfl) ⟨1245035, by rfl⟩ : syracuseStep 1660047 = 2490071) B2490071
theorem B1660091 : Blo 1659529 1660091 := bstep (se 1 (by rfl) ⟨1245068, by rfl⟩ : syracuseStep 1660091 = 2490137) B2490137
theorem B1660167 : Blo 1659529 1660167 := bstep (se 1 (by rfl) ⟨1245125, by rfl⟩ : syracuseStep 1660167 = 2490251) B2490251
theorem B1660175 : Blo 1659529 1660175 := bstep (se 1 (by rfl) ⟨1245131, by rfl⟩ : syracuseStep 1660175 = 2490263) B2490263
theorem B3151163 : Blo 1659529 3151163 := bstep (se 1 (by rfl) ⟨2363372, by rfl⟩ : syracuseStep 3151163 = 4726745) B4726745
theorem B1660219 : Blo 1659529 1660219 := bstep (se 1 (by rfl) ⟨1245164, by rfl⟩ : syracuseStep 1660219 = 2490329) B2490329
theorem B40408379 : Blo 1659529 40408379 := bstep (se 1 (by rfl) ⟨30306284, by rfl⟩ : syracuseStep 40408379 = 60612569) B60612569
theorem B8402291 : Blo 1659529 8402291 := bstep (se 1 (by rfl) ⟨6301718, by rfl⟩ : syracuseStep 8402291 = 12603437) B12603437
theorem B1660295 : Blo 1659529 1660295 := bstep (se 1 (by rfl) ⟨1245221, by rfl⟩ : syracuseStep 1660295 = 2490443) B2490443
theorem B1660303 : Blo 1659529 1660303 := bstep (se 1 (by rfl) ⟨1245227, by rfl⟩ : syracuseStep 1660303 = 2490455) B2490455
theorem B2102699 : Blo 1659529 2102699 := bstep (se 1 (by rfl) ⟨1577024, by rfl⟩ : syracuseStep 2102699 = 3154049) B3154049
theorem B34067891 : Blo 1659529 34067891 := bstep (se 1 (by rfl) ⟨25550918, by rfl⟩ : syracuseStep 34067891 = 51101837) B51101837
theorem B8410553 : Blo 1659529 8410553 := bstep (se 2 (by rfl) ⟨3153957, by rfl⟩ : syracuseStep 8410553 = 6307915) B6307915
theorem B1660347 : Blo 1659529 1660347 := bstep (se 1 (by rfl) ⟨1245260, by rfl⟩ : syracuseStep 1660347 = 2490521) B2490521
theorem B1660423 : Blo 1659529 1660423 := bstep (se 1 (by rfl) ⟨1245317, by rfl⟩ : syracuseStep 1660423 = 2490635) B2490635
theorem B1660431 : Blo 1659529 1660431 := bstep (se 1 (by rfl) ⟨1245323, by rfl⟩ : syracuseStep 1660431 = 2490647) B2490647
theorem B1660475 : Blo 1659529 1660475 := bstep (se 1 (by rfl) ⟨1245356, by rfl⟩ : syracuseStep 1660475 = 2490713) B2490713
theorem B3364487 : Blo 1659529 3364487 := bstep (se 1 (by rfl) ⟨2523365, by rfl⟩ : syracuseStep 3364487 = 5046731) B5046731
theorem B1660551 : Blo 1659529 1660551 := bstep (se 1 (by rfl) ⟨1245413, by rfl⟩ : syracuseStep 1660551 = 2490827) B2490827
theorem B1660559 : Blo 1659529 1660559 := bstep (se 1 (by rfl) ⟨1245419, by rfl⟩ : syracuseStep 1660559 = 2490839) B2490839
theorem B1660603 : Blo 1659529 1660603 := bstep (se 1 (by rfl) ⟨1245452, by rfl⟩ : syracuseStep 1660603 = 2490905) B2490905
theorem B1660679 : Blo 1659529 1660679 := bstep (se 1 (by rfl) ⟨1245509, by rfl⟩ : syracuseStep 1660679 = 2491019) B2491019
theorem B1660687 : Blo 1659529 1660687 := bstep (se 1 (by rfl) ⟨1245515, by rfl⟩ : syracuseStep 1660687 = 2491031) B2491031
theorem B3151649 : Blo 1659529 3151649 := bstep (se 2 (by rfl) ⟨1181868, by rfl⟩ : syracuseStep 3151649 = 2363737) B2363737
theorem B5682977 : Blo 1659529 5682977 := bstep (se 2 (by rfl) ⟨2131116, by rfl⟩ : syracuseStep 5682977 = 4262233) B4262233
theorem B1660731 : Blo 1659529 1660731 := bstep (se 1 (by rfl) ⟨1245548, by rfl⟩ : syracuseStep 1660731 = 2491097) B2491097
theorem B40384331 : Blo 1659529 40384331 := bstep (se 1 (by rfl) ⟨30288248, by rfl⟩ : syracuseStep 40384331 = 60576497) B60576497
theorem B8402777 : Blo 1659529 8402777 := bstep (se 2 (by rfl) ⟨3151041, by rfl⟩ : syracuseStep 8402777 = 6302083) B6302083
theorem B1660807 : Blo 1659529 1660807 := bstep (se 1 (by rfl) ⟨1245605, by rfl⟩ : syracuseStep 1660807 = 2491211) B2491211
theorem B1660815 : Blo 1659529 1660815 := bstep (se 1 (by rfl) ⟨1245611, by rfl⟩ : syracuseStep 1660815 = 2491223) B2491223
theorem B18913175 : Blo 1659529 18913175 := bstep (se 1 (by rfl) ⟨14184881, by rfl⟩ : syracuseStep 18913175 = 28369763) B28369763
theorem B3151801 : Blo 1659529 3151801 := bstep (se 2 (by rfl) ⟨1181925, by rfl⟩ : syracuseStep 3151801 = 2363851) B2363851
theorem B1660859 : Blo 1659529 1660859 := bstep (se 1 (by rfl) ⟨1245644, by rfl⟩ : syracuseStep 1660859 = 2491289) B2491289
theorem B9459665 : Blo 1659529 9459665 := bstep (se 2 (by rfl) ⟨3547374, by rfl⟩ : syracuseStep 9459665 = 7094749) B7094749
theorem B1660935 : Blo 1659529 1660935 := bstep (se 1 (by rfl) ⟨1245701, by rfl⟩ : syracuseStep 1660935 = 2491403) B2491403
theorem B12613643 : Blo 1659529 12613643 := bstep (se 1 (by rfl) ⟨9460232, by rfl⟩ : syracuseStep 12613643 = 18920465) B18920465
theorem B1660943 : Blo 1659529 1660943 := bstep (se 1 (by rfl) ⟨1245707, by rfl⟩ : syracuseStep 1660943 = 2491415) B2491415
theorem B1660987 : Blo 1659529 1660987 := bstep (se 1 (by rfl) ⟨1245740, by rfl⟩ : syracuseStep 1660987 = 2491481) B2491481
theorem B1661063 : Blo 1659529 1661063 := bstep (se 1 (by rfl) ⟨1245797, by rfl⟩ : syracuseStep 1661063 = 2491595) B2491595
theorem B1661071 : Blo 1659529 1661071 := bstep (se 1 (by rfl) ⟨1245803, by rfl⟩ : syracuseStep 1661071 = 2491607) B2491607
theorem B2660537 : Blo 1659529 2660537 := bstep (se 2 (by rfl) ⟨997701, by rfl⟩ : syracuseStep 2660537 = 1995403) B1995403
theorem B1661115 : Blo 1659529 1661115 := bstep (se 1 (by rfl) ⟨1245836, by rfl⟩ : syracuseStep 1661115 = 2491673) B2491673
theorem B1661191 : Blo 1659529 1661191 := bstep (se 1 (by rfl) ⟨1245893, by rfl⟩ : syracuseStep 1661191 = 2491787) B2491787
theorem B1661199 : Blo 1659529 1661199 := bstep (se 1 (by rfl) ⟨1245899, by rfl⟩ : syracuseStep 1661199 = 2491799) B2491799
theorem B16169249 : Blo 1659529 16169249 := bstep (se 2 (by rfl) ⟨6063468, by rfl⟩ : syracuseStep 16169249 = 12126937) B12126937
theorem B1661243 : Blo 1659529 1661243 := bstep (se 1 (by rfl) ⟨1245932, by rfl⟩ : syracuseStep 1661243 = 2491865) B2491865
theorem B7977305 : Blo 1659529 7977305 := bstep (se 2 (by rfl) ⟨2991489, by rfl⟩ : syracuseStep 7977305 = 5982979) B5982979
theorem B1661319 : Blo 1659529 1661319 := bstep (se 1 (by rfl) ⟨1245989, by rfl⟩ : syracuseStep 1661319 = 2491979) B2491979
theorem B1661327 : Blo 1659529 1661327 := bstep (se 1 (by rfl) ⟨1245995, by rfl⟩ : syracuseStep 1661327 = 2491991) B2491991
theorem B5601689 : Blo 1659529 5601689 := bstep (se 2 (by rfl) ⟨2100633, by rfl⟩ : syracuseStep 5601689 = 4201267) B4201267
theorem B1661371 : Blo 1659529 1661371 := bstep (se 1 (by rfl) ⟨1246028, by rfl⟩ : syracuseStep 1661371 = 2492057) B2492057
theorem B26933725 : Blo 1659529 26933725 := bstep (se 3 (by rfl) ⟨5050073, by rfl⟩ : syracuseStep 26933725 = 10100147) B10100147
theorem B1661447 : Blo 1659529 1661447 := bstep (se 1 (by rfl) ⟨1246085, by rfl⟩ : syracuseStep 1661447 = 2492171) B2492171
theorem B1661455 : Blo 1659529 1661455 := bstep (se 1 (by rfl) ⟨1246091, by rfl⟩ : syracuseStep 1661455 = 2492183) B2492183
theorem B5118493 : Blo 1659529 5118493 := bstep (se 3 (by rfl) ⟨959717, by rfl⟩ : syracuseStep 5118493 = 1919435) B1919435
theorem B12139037 : Blo 1659529 12139037 := bstep (se 3 (by rfl) ⟨2276069, by rfl⟩ : syracuseStep 12139037 = 4552139) B4552139
theorem B1661499 : Blo 1659529 1661499 := bstep (se 1 (by rfl) ⟨1246124, by rfl⟩ : syracuseStep 1661499 = 2492249) B2492249
theorem B3734135 : Blo 1659529 3734135 := bstep (se 1 (by rfl) ⟨2800601, by rfl⟩ : syracuseStep 3734135 = 5601203) B5601203
theorem B23935607 : Blo 1659529 23935607 := bstep (se 1 (by rfl) ⟨17951705, by rfl⟩ : syracuseStep 23935607 = 35903411) B35903411
theorem B2702009 : Blo 1659529 2702009 := bstep (se 2 (by rfl) ⟨1013253, by rfl⟩ : syracuseStep 2702009 = 2026507) B2026507
theorem B4201217 : Blo 1659529 4201217 := bstep (se 2 (by rfl) ⟨1575456, by rfl⟩ : syracuseStep 4201217 = 3150913) B3150913
theorem B17963813 : Blo 1659529 17963813 := bstep (se 4 (by rfl) ⟨1684107, by rfl⟩ : syracuseStep 17963813 = 3368215) B3368215
theorem B3734315 : Blo 1659529 3734315 := bstep (se 1 (by rfl) ⟨2800736, by rfl⟩ : syracuseStep 3734315 = 5601473) B5601473
theorem B7486267 : Blo 1659529 7486267 := bstep (se 1 (by rfl) ⟨5614700, by rfl⟩ : syracuseStep 7486267 = 11229401) B11229401
theorem B13458329 : Blo 1659529 13458329 := bstep (se 2 (by rfl) ⟨5046873, by rfl⟩ : syracuseStep 13458329 = 10093747) B10093747
theorem B40410019 : Blo 1659529 40410019 := bstep (se 1 (by rfl) ⟨30307514, by rfl⟩ : syracuseStep 40410019 = 60615029) B60615029
theorem B2489351 : Blo 1659529 2489351 := bstep (se 1 (by rfl) ⟨1867013, by rfl⟩ : syracuseStep 2489351 = 3734027) B3734027
theorem B2489387 : Blo 1659529 2489387 := bstep (se 1 (by rfl) ⟨1867040, by rfl⟩ : syracuseStep 2489387 = 3734081) B3734081
theorem B2489417 : Blo 1659529 2489417 := bstep (se 2 (by rfl) ⟨933531, by rfl⟩ : syracuseStep 2489417 = 1867063) B1867063
theorem B5602391 : Blo 1659529 5602391 := bstep (se 1 (by rfl) ⟨4201793, by rfl⟩ : syracuseStep 5602391 = 8403587) B8403587
theorem B4201591 : Blo 1659529 4201591 := bstep (se 1 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 4201591 = 6302387) B6302387
theorem B3734675 : Blo 1659529 3734675 := bstep (se 1 (by rfl) ⟨2801006, by rfl⟩ : syracuseStep 3734675 = 5602013) B5602013
theorem B2489531 : Blo 1659529 2489531 := bstep (se 1 (by rfl) ⟨1867148, by rfl⟩ : syracuseStep 2489531 = 3734297) B3734297
theorem B3734729 : Blo 1659529 3734729 := bstep (se 2 (by rfl) ⟨1400523, by rfl⟩ : syracuseStep 3734729 = 2801047) B2801047
theorem B2489591 : Blo 1659529 2489591 := bstep (se 1 (by rfl) ⟨1867193, by rfl⟩ : syracuseStep 2489591 = 3734387) B3734387
theorem B2489615 : Blo 1659529 2489615 := bstep (se 1 (by rfl) ⟨1867211, by rfl⟩ : syracuseStep 2489615 = 3734423) B3734423
theorem B2800939 : Blo 1659529 2800939 := bstep (se 1 (by rfl) ⟨2100704, by rfl⟩ : syracuseStep 2800939 = 4201409) B4201409
theorem B2489657 : Blo 1659529 2489657 := bstep (se 2 (by rfl) ⟨933621, by rfl⟩ : syracuseStep 2489657 = 1867243) B1867243
theorem B2489735 : Blo 1659529 2489735 := bstep (se 1 (by rfl) ⟨1867301, by rfl⟩ : syracuseStep 2489735 = 3734603) B3734603
theorem B3988883 : Blo 1659529 3988883 := bstep (se 1 (by rfl) ⟨2991662, by rfl⟩ : syracuseStep 3988883 = 5983325) B5983325
theorem B2489771 : Blo 1659529 2489771 := bstep (se 1 (by rfl) ⟨1867328, by rfl⟩ : syracuseStep 2489771 = 3734657) B3734657
theorem B2801081 : Blo 1659529 2801081 := bstep (se 2 (by rfl) ⟨1050405, by rfl⟩ : syracuseStep 2801081 = 2100811) B2100811
theorem B2489801 : Blo 1659529 2489801 := bstep (se 2 (by rfl) ⟨933675, by rfl⟩ : syracuseStep 2489801 = 1867351) B1867351
theorem B1867279 : Blo 1659529 1867279 := bstep (se 1 (by rfl) ⟨1400459, by rfl⟩ : syracuseStep 1867279 = 2800919) B2800919
theorem B4202027 : Blo 1659529 4202027 := bstep (se 1 (by rfl) ⟨3151520, by rfl⟩ : syracuseStep 4202027 = 6303041) B6303041
theorem B2489915 : Blo 1659529 2489915 := bstep (se 1 (by rfl) ⟨1867436, by rfl⟩ : syracuseStep 2489915 = 3734873) B3734873
theorem B5602877 : Blo 1659529 5602877 := bstep (se 3 (by rfl) ⟨1050539, by rfl⟩ : syracuseStep 5602877 = 2101079) B2101079
theorem B6307415 : Blo 1659529 6307415 := bstep (se 1 (by rfl) ⟨4730561, by rfl⟩ : syracuseStep 6307415 = 9461123) B9461123
theorem B2489975 : Blo 1659529 2489975 := bstep (se 1 (by rfl) ⟨1867481, by rfl⟩ : syracuseStep 2489975 = 3734963) B3734963
theorem B2489999 : Blo 1659529 2489999 := bstep (se 1 (by rfl) ⟨1867499, by rfl⟩ : syracuseStep 2489999 = 3734999) B3734999
theorem B2490041 : Blo 1659529 2490041 := bstep (se 2 (by rfl) ⟨933765, by rfl⟩ : syracuseStep 2490041 = 1867531) B1867531
theorem B3153593 : Blo 1659529 3153593 := bstep (se 2 (by rfl) ⟨1182597, by rfl⟩ : syracuseStep 3153593 = 2365195) B2365195
theorem B2490119 : Blo 1659529 2490119 := bstep (se 1 (by rfl) ⟨1867589, by rfl⟩ : syracuseStep 2490119 = 3735179) B3735179
theorem B2490155 : Blo 1659529 2490155 := bstep (se 1 (by rfl) ⟨1867616, by rfl⟩ : syracuseStep 2490155 = 3735233) B3735233
theorem B26935091 : Blo 1659529 26935091 := bstep (se 1 (by rfl) ⟨20201318, by rfl⟩ : syracuseStep 26935091 = 40402637) B40402637
theorem B9461555 : Blo 1659529 9461555 := bstep (se 1 (by rfl) ⟨7096166, by rfl⟩ : syracuseStep 9461555 = 14192333) B14192333
theorem B2490185 : Blo 1659529 2490185 := bstep (se 2 (by rfl) ⟨933819, by rfl⟩ : syracuseStep 2490185 = 1867639) B1867639
theorem B3735431 : Blo 1659529 3735431 := bstep (se 1 (by rfl) ⟨2801573, by rfl⟩ : syracuseStep 3735431 = 5603147) B5603147
theorem B8404883 : Blo 1659529 8404883 := bstep (se 1 (by rfl) ⟨6303662, by rfl⟩ : syracuseStep 8404883 = 12607325) B12607325
theorem B12615587 : Blo 1659529 12615587 := bstep (se 1 (by rfl) ⟨9461690, by rfl⟩ : syracuseStep 12615587 = 18923381) B18923381
theorem B2490299 : Blo 1659529 2490299 := bstep (se 1 (by rfl) ⟨1867724, by rfl⟩ : syracuseStep 2490299 = 3735449) B3735449
theorem B3596233 : Blo 1659529 3596233 := bstep (se 2 (by rfl) ⟨1348587, by rfl⟩ : syracuseStep 3596233 = 2697175) B2697175
theorem B2490359 : Blo 1659529 2490359 := bstep (se 1 (by rfl) ⟨1867769, by rfl⟩ : syracuseStep 2490359 = 3735539) B3735539
theorem B2695175 : Blo 1659529 2695175 := bstep (se 1 (by rfl) ⟨2021381, by rfl⟩ : syracuseStep 2695175 = 4042763) B4042763
theorem B2490377 : Blo 1659529 2490377 := bstep (se 2 (by rfl) ⟨933891, by rfl⟩ : syracuseStep 2490377 = 1867783) B1867783
theorem B2490407 : Blo 1659529 2490407 := bstep (se 1 (by rfl) ⟨1867805, by rfl⟩ : syracuseStep 2490407 = 3735611) B3735611
theorem B1867855 : Blo 1659529 1867855 := bstep (se 1 (by rfl) ⟨1400891, by rfl⟩ : syracuseStep 1867855 = 2801783) B2801783
theorem B10633331 : Blo 1659529 10633331 := bstep (se 1 (by rfl) ⟨7974998, by rfl⟩ : syracuseStep 10633331 = 15949997) B15949997
theorem B2490491 : Blo 1659529 2490491 := bstep (se 1 (by rfl) ⟨1867868, by rfl⟩ : syracuseStep 2490491 = 3735737) B3735737
theorem B3547307 : Blo 1659529 3547307 := bstep (se 1 (by rfl) ⟨2660480, by rfl⟩ : syracuseStep 3547307 = 5320961) B5320961
theorem B2801911 : Blo 1659529 2801911 := bstep (se 1 (by rfl) ⟨2101433, by rfl⟩ : syracuseStep 2801911 = 4202867) B4202867
theorem B2490617 : Blo 1659529 2490617 := bstep (se 2 (by rfl) ⟨933981, by rfl⟩ : syracuseStep 2490617 = 1867963) B1867963
theorem B2523487 : Blo 1659529 2523487 := bstep (se 1 (by rfl) ⟨1892615, by rfl⟩ : syracuseStep 2523487 = 3785231) B3785231
theorem B2490719 : Blo 1659529 2490719 := bstep (se 1 (by rfl) ⟨1868039, by rfl⟩ : syracuseStep 2490719 = 3736079) B3736079
theorem B2490731 : Blo 1659529 2490731 := bstep (se 1 (by rfl) ⟨1868048, by rfl⟩ : syracuseStep 2490731 = 3736097) B3736097
theorem B2802107 : Blo 1659529 2802107 := bstep (se 1 (by rfl) ⟨2101580, by rfl⟩ : syracuseStep 2802107 = 4203161) B4203161
theorem B1868251 : Blo 1659529 1868251 := bstep (se 1 (by rfl) ⟨1401188, by rfl⟩ : syracuseStep 1868251 = 2802377) B2802377
theorem B7094765 : Blo 1659529 7094765 := bstep (se 3 (by rfl) ⟨1330268, by rfl⟩ : syracuseStep 7094765 = 2660537) B2660537
theorem B4547081 : Blo 1659529 4547081 := bstep (se 2 (by rfl) ⟨1705155, by rfl⟩ : syracuseStep 4547081 = 3410311) B3410311
theorem B5603849 : Blo 1659529 5603849 := bstep (se 2 (by rfl) ⟨2101443, by rfl⟩ : syracuseStep 5603849 = 4202887) B4202887
theorem B13468193 : Blo 1659529 13468193 := bstep (se 2 (by rfl) ⟨5050572, by rfl⟩ : syracuseStep 13468193 = 10101145) B10101145
theorem B2802215 : Blo 1659529 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B2490959 : Blo 1659529 2490959 := bstep (se 1 (by rfl) ⟨1868219, by rfl⟩ : syracuseStep 2490959 = 3736439) B3736439
theorem B3736187 : Blo 1659529 3736187 := bstep (se 1 (by rfl) ⟨2802140, by rfl⟩ : syracuseStep 3736187 = 5604281) B5604281
theorem B9454265 : Blo 1659529 9454265 := bstep (se 2 (by rfl) ⟨3545349, by rfl⟩ : syracuseStep 9454265 = 7090699) B7090699
theorem B2990791 : Blo 1659529 2990791 := bstep (se 1 (by rfl) ⟨2243093, by rfl⟩ : syracuseStep 2990791 = 4486187) B4486187
theorem B2491079 : Blo 1659529 2491079 := bstep (se 1 (by rfl) ⟨1868309, by rfl⟩ : syracuseStep 2491079 = 3736619) B3736619
theorem B6824657 : Blo 1659529 6824657 := bstep (se 2 (by rfl) ⟨2559246, by rfl⟩ : syracuseStep 6824657 = 5118493) B5118493
theorem B3736313 : Blo 1659529 3736313 := bstep (se 2 (by rfl) ⟨1401117, by rfl⟩ : syracuseStep 3736313 = 2802235) B2802235
theorem B2802505 : Blo 1659529 2802505 := bstep (se 2 (by rfl) ⟨1050939, by rfl⟩ : syracuseStep 2802505 = 2101879) B2101879
theorem B7291721 : Blo 1659529 7291721 := bstep (se 2 (by rfl) ⟨2734395, by rfl⟩ : syracuseStep 7291721 = 5468791) B5468791
theorem B2491241 : Blo 1659529 2491241 := bstep (se 2 (by rfl) ⟨934215, by rfl⟩ : syracuseStep 2491241 = 1868431) B1868431
theorem B2802539 : Blo 1659529 2802539 := bstep (se 1 (by rfl) ⟨2101904, by rfl⟩ : syracuseStep 2802539 = 4203809) B4203809
theorem B1868719 : Blo 1659529 1868719 := bstep (se 1 (by rfl) ⟨1401539, by rfl⟩ : syracuseStep 1868719 = 2803079) B2803079
theorem B2491319 : Blo 1659529 2491319 := bstep (se 1 (by rfl) ⟨1868489, by rfl⟩ : syracuseStep 2491319 = 3736979) B3736979
theorem B2491355 : Blo 1659529 2491355 := bstep (se 1 (by rfl) ⟨1868516, by rfl⟩ : syracuseStep 2491355 = 3737033) B3737033
theorem B8406017 : Blo 1659529 8406017 := bstep (se 2 (by rfl) ⟨3152256, by rfl⟩ : syracuseStep 8406017 = 6304513) B6304513
theorem B3736583 : Blo 1659529 3736583 := bstep (se 1 (by rfl) ⟨2802437, by rfl⟩ : syracuseStep 3736583 = 5604875) B5604875
theorem B3736655 : Blo 1659529 3736655 := bstep (se 1 (by rfl) ⟨2802491, by rfl⟩ : syracuseStep 3736655 = 5604983) B5604983
theorem B53880025 : Blo 1659529 53880025 := bstep (se 2 (by rfl) ⟨20205009, by rfl⟩ : syracuseStep 53880025 = 40410019) B40410019
theorem B2802937 : Blo 1659529 2802937 := bstep (se 2 (by rfl) ⟨1051101, by rfl⟩ : syracuseStep 2802937 = 2102203) B2102203
theorem B12608783 : Blo 1659529 12608783 := bstep (se 1 (by rfl) ⟨9456587, by rfl⟩ : syracuseStep 12608783 = 18913175) B18913175
theorem B1869151 : Blo 1659529 1869151 := bstep (se 1 (by rfl) ⟨1401863, by rfl⟩ : syracuseStep 1869151 = 2803727) B2803727
theorem B5604713 : Blo 1659529 5604713 := bstep (se 2 (by rfl) ⟨2101767, by rfl⟩ : syracuseStep 5604713 = 4203535) B4203535
theorem B2491823 : Blo 1659529 2491823 := bstep (se 1 (by rfl) ⟨1868867, by rfl⟩ : syracuseStep 2491823 = 3737735) B3737735
theorem B3737051 : Blo 1659529 3737051 := bstep (se 1 (by rfl) ⟨2802788, by rfl⟩ : syracuseStep 3737051 = 5605577) B5605577
theorem B2803207 : Blo 1659529 2803207 := bstep (se 1 (by rfl) ⟨2102405, by rfl⟩ : syracuseStep 2803207 = 4204811) B4204811
theorem B2491913 : Blo 1659529 2491913 := bstep (se 2 (by rfl) ⟨934467, by rfl⟩ : syracuseStep 2491913 = 1868935) B1868935
theorem B2491943 : Blo 1659529 2491943 := bstep (se 1 (by rfl) ⟨1868957, by rfl⟩ : syracuseStep 2491943 = 3737915) B3737915
theorem B2492027 : Blo 1659529 2492027 := bstep (se 1 (by rfl) ⟨1869020, by rfl⟩ : syracuseStep 2492027 = 3738041) B3738041
theorem B2492153 : Blo 1659529 2492153 := bstep (se 2 (by rfl) ⟨934557, by rfl⟩ : syracuseStep 2492153 = 1869115) B1869115
theorem B8406827 : Blo 1659529 8406827 := bstep (se 1 (by rfl) ⟨6305120, by rfl⟩ : syracuseStep 8406827 = 12610241) B12610241
theorem B8980267 : Blo 1659529 8980267 := bstep (se 1 (by rfl) ⟨6735200, by rfl⟩ : syracuseStep 8980267 = 13470401) B13470401
theorem B2492255 : Blo 1659529 2492255 := bstep (se 1 (by rfl) ⟨1869191, by rfl⟩ : syracuseStep 2492255 = 3738383) B3738383
theorem B2492267 : Blo 1659529 2492267 := bstep (se 1 (by rfl) ⟨1869200, by rfl⟩ : syracuseStep 2492267 = 3738401) B3738401
theorem B12126061 : Blo 1659529 12126061 := bstep (se 3 (by rfl) ⟨2273636, by rfl⟩ : syracuseStep 12126061 = 4547273) B4547273
theorem B3737519 : Blo 1659529 3737519 := bstep (se 1 (by rfl) ⟨2803139, by rfl⟩ : syracuseStep 3737519 = 5606279) B5606279
theorem B2803639 : Blo 1659529 2803639 := bstep (se 1 (by rfl) ⟨2102729, by rfl⟩ : syracuseStep 2803639 = 4205459) B4205459
theorem B8972219 : Blo 1659529 8972219 := bstep (se 1 (by rfl) ⟨6729164, by rfl⟩ : syracuseStep 8972219 = 13458329) B13458329
theorem B5605307 : Blo 1659529 5605307 := bstep (se 1 (by rfl) ⟨4203980, by rfl⟩ : syracuseStep 5605307 = 8407961) B8407961
theorem B3197051 : Blo 1659529 3197051 := bstep (se 1 (by rfl) ⟨2397788, by rfl⟩ : syracuseStep 3197051 = 4795577) B4795577
theorem B3737771 : Blo 1659529 3737771 := bstep (se 1 (by rfl) ⟨2803328, by rfl⟩ : syracuseStep 3737771 = 5606657) B5606657
theorem B2525383 : Blo 1659529 2525383 := bstep (se 1 (by rfl) ⟨1894037, by rfl⟩ : syracuseStep 2525383 = 3788075) B3788075
theorem B4204943 : Blo 1659529 4204943 := bstep (se 1 (by rfl) ⟨3153707, by rfl⟩ : syracuseStep 4204943 = 6307415) B6307415
theorem B10643993 : Blo 1659529 10643993 := bstep (se 2 (by rfl) ⟨3991497, by rfl⟩ : syracuseStep 10643993 = 7982995) B7982995
theorem B4794977 : Blo 1659529 4794977 := bstep (se 2 (by rfl) ⟨1798116, by rfl⟩ : syracuseStep 4794977 = 3596233) B3596233
theorem B3738311 : Blo 1659529 3738311 := bstep (se 1 (by rfl) ⟨2803733, by rfl⟩ : syracuseStep 3738311 = 5607467) B5607467
theorem B4205267 : Blo 1659529 4205267 := bstep (se 1 (by rfl) ⟨3153950, by rfl⟩ : syracuseStep 4205267 = 6307901) B6307901
theorem B2992889 : Blo 1659529 2992889 := bstep (se 2 (by rfl) ⟨1122333, by rfl⟩ : syracuseStep 2992889 = 2244667) B2244667
theorem B6728761 : Blo 1659529 6728761 := bstep (se 2 (by rfl) ⟨2523285, by rfl⟩ : syracuseStep 6728761 = 5046571) B5046571
theorem B2993249 : Blo 1659529 2993249 := bstep (se 2 (by rfl) ⟨1122468, by rfl⟩ : syracuseStep 2993249 = 2244937) B2244937
theorem B6302873 : Blo 1659529 6302873 := bstep (se 2 (by rfl) ⟨2363577, by rfl⟩ : syracuseStep 6302873 = 4727155) B4727155
theorem B5983427 : Blo 1659529 5983427 := bstep (se 1 (by rfl) ⟨4487570, by rfl⟩ : syracuseStep 5983427 = 8975141) B8975141
theorem B40930595 : Blo 1659529 40930595 := bstep (se 1 (by rfl) ⟨30697946, by rfl⟩ : syracuseStep 40930595 = 61395893) B61395893
theorem B10235261 : Blo 1659529 10235261 := bstep (se 3 (by rfl) ⟨1919111, by rfl⟩ : syracuseStep 10235261 = 3838223) B3838223
theorem B26938919 : Blo 1659529 26938919 := bstep (se 1 (by rfl) ⟨20204189, by rfl⟩ : syracuseStep 26938919 = 40408379) B40408379
theorem B6303329 : Blo 1659529 6303329 := bstep (se 2 (by rfl) ⟨2363748, by rfl⟩ : syracuseStep 6303329 = 4727497) B4727497
theorem B22711927 : Blo 1659529 22711927 := bstep (se 1 (by rfl) ⟨17033945, by rfl⟩ : syracuseStep 22711927 = 34067891) B34067891
theorem B5607035 : Blo 1659529 5607035 := bstep (se 1 (by rfl) ⟨4205276, by rfl⟩ : syracuseStep 5607035 = 8410553) B8410553
theorem B10637021 : Blo 1659529 10637021 := bstep (se 3 (by rfl) ⟨1994441, by rfl⟩ : syracuseStep 10637021 = 3988883) B3988883
theorem B9981689 : Blo 1659529 9981689 := bstep (se 2 (by rfl) ⟨3743133, by rfl⟩ : syracuseStep 9981689 = 7486267) B7486267
theorem B5607197 : Blo 1659529 5607197 := bstep (se 3 (by rfl) ⟨1051349, by rfl⟩ : syracuseStep 5607197 = 2102699) B2102699
theorem B20197187 : Blo 1659529 20197187 := bstep (se 1 (by rfl) ⟨15147890, by rfl⟩ : syracuseStep 20197187 = 30295781) B30295781
theorem B3788651 : Blo 1659529 3788651 := bstep (se 1 (by rfl) ⟨2841488, by rfl⟩ : syracuseStep 3788651 = 5682977) B5682977
theorem B26922887 : Blo 1659529 26922887 := bstep (se 1 (by rfl) ⟨20192165, by rfl⟩ : syracuseStep 26922887 = 40384331) B40384331
theorem B8409095 : Blo 1659529 8409095 := bstep (se 1 (by rfl) ⟨6306821, by rfl⟩ : syracuseStep 8409095 = 12613643) B12613643
theorem B9580625 : Blo 1659529 9580625 := bstep (se 2 (by rfl) ⟨3592734, by rfl⟩ : syracuseStep 9580625 = 7185469) B7185469
theorem B12611699 : Blo 1659529 12611699 := bstep (se 1 (by rfl) ⟨9458774, by rfl⟩ : syracuseStep 12611699 = 18917549) B18917549
theorem B7205357 : Blo 1659529 7205357 := bstep (se 3 (by rfl) ⟨1351004, by rfl⟩ : syracuseStep 7205357 = 2702009) B2702009
theorem B8409581 : Blo 1659529 8409581 := bstep (se 3 (by rfl) ⟨1576796, by rfl⟩ : syracuseStep 8409581 = 3153593) B3153593
theorem B1659567 : Blo 1659529 1659567 := bstep (se 1 (by rfl) ⟨1244675, by rfl⟩ : syracuseStep 1659567 = 2489351) B2489351
theorem B1659591 : Blo 1659529 1659591 := bstep (se 1 (by rfl) ⟨1244693, by rfl⟩ : syracuseStep 1659591 = 2489387) B2489387
theorem B1659611 : Blo 1659529 1659611 := bstep (se 1 (by rfl) ⟨1244708, by rfl⟩ : syracuseStep 1659611 = 2489417) B2489417
theorem B47903501 : Blo 1659529 47903501 := bstep (se 3 (by rfl) ⟨8981906, by rfl⟩ : syracuseStep 47903501 = 17963813) B17963813
theorem B7090973 : Blo 1659529 7090973 := bstep (se 3 (by rfl) ⟨1329557, by rfl⟩ : syracuseStep 7090973 = 2659115) B2659115
theorem B1659687 : Blo 1659529 1659687 := bstep (se 1 (by rfl) ⟨1244765, by rfl⟩ : syracuseStep 1659687 = 2489531) B2489531
theorem B1659727 : Blo 1659529 1659727 := bstep (se 1 (by rfl) ⟨1244795, by rfl⟩ : syracuseStep 1659727 = 2489591) B2489591
theorem B1659743 : Blo 1659529 1659743 := bstep (se 1 (by rfl) ⟨1244807, by rfl⟩ : syracuseStep 1659743 = 2489615) B2489615
theorem B1659771 : Blo 1659529 1659771 := bstep (se 1 (by rfl) ⟨1244828, by rfl⟩ : syracuseStep 1659771 = 2489657) B2489657
theorem B1659823 : Blo 1659529 1659823 := bstep (se 1 (by rfl) ⟨1244867, by rfl⟩ : syracuseStep 1659823 = 2489735) B2489735
theorem B1659847 : Blo 1659529 1659847 := bstep (se 1 (by rfl) ⟨1244885, by rfl⟩ : syracuseStep 1659847 = 2489771) B2489771
theorem B1659867 : Blo 1659529 1659867 := bstep (se 1 (by rfl) ⟨1244900, by rfl⟩ : syracuseStep 1659867 = 2489801) B2489801
theorem B6304787 : Blo 1659529 6304787 := bstep (se 1 (by rfl) ⟨4728590, by rfl⟩ : syracuseStep 6304787 = 9457181) B9457181
theorem B1659943 : Blo 1659529 1659943 := bstep (se 1 (by rfl) ⟨1244957, by rfl⟩ : syracuseStep 1659943 = 2489915) B2489915
theorem B1659983 : Blo 1659529 1659983 := bstep (se 1 (by rfl) ⟨1244987, by rfl⟩ : syracuseStep 1659983 = 2489975) B2489975
theorem B1659999 : Blo 1659529 1659999 := bstep (se 1 (by rfl) ⟨1244999, by rfl⟩ : syracuseStep 1659999 = 2489999) B2489999
theorem B1660027 : Blo 1659529 1660027 := bstep (se 1 (by rfl) ⟨1245020, by rfl⟩ : syracuseStep 1660027 = 2490041) B2490041
theorem B1660079 : Blo 1659529 1660079 := bstep (se 1 (by rfl) ⟨1245059, by rfl⟩ : syracuseStep 1660079 = 2490119) B2490119
theorem B1660103 : Blo 1659529 1660103 := bstep (se 1 (by rfl) ⟨1245077, by rfl⟩ : syracuseStep 1660103 = 2490155) B2490155
theorem B1660123 : Blo 1659529 1660123 := bstep (se 1 (by rfl) ⟨1245092, by rfl⟩ : syracuseStep 1660123 = 2490185) B2490185
theorem B8410391 : Blo 1659529 8410391 := bstep (se 1 (by rfl) ⟨6307793, by rfl⟩ : syracuseStep 8410391 = 12615587) B12615587
theorem B1660199 : Blo 1659529 1660199 := bstep (se 1 (by rfl) ⟨1245149, by rfl⟩ : syracuseStep 1660199 = 2490299) B2490299
theorem B1660239 : Blo 1659529 1660239 := bstep (se 1 (by rfl) ⟨1245179, by rfl⟩ : syracuseStep 1660239 = 2490359) B2490359
theorem B1660255 : Blo 1659529 1660255 := bstep (se 1 (by rfl) ⟨1245191, by rfl⟩ : syracuseStep 1660255 = 2490383) B2490383
theorem B1660283 : Blo 1659529 1660283 := bstep (se 1 (by rfl) ⟨1245212, by rfl⟩ : syracuseStep 1660283 = 2490425) B2490425
theorem B11974031 : Blo 1659529 11974031 := bstep (se 1 (by rfl) ⟨8980523, by rfl⟩ : syracuseStep 11974031 = 17961047) B17961047
theorem B12776869 : Blo 1659529 12776869 := bstep (se 4 (by rfl) ⟨1197831, by rfl⟩ : syracuseStep 12776869 = 2395663) B2395663
theorem B1660335 : Blo 1659529 1660335 := bstep (se 1 (by rfl) ⟨1245251, by rfl⟩ : syracuseStep 1660335 = 2490503) B2490503
theorem B1660359 : Blo 1659529 1660359 := bstep (se 1 (by rfl) ⟨1245269, by rfl⟩ : syracuseStep 1660359 = 2490539) B2490539
theorem B7091657 : Blo 1659529 7091657 := bstep (se 2 (by rfl) ⟨2659371, by rfl⟩ : syracuseStep 7091657 = 5318743) B5318743
theorem B1660379 : Blo 1659529 1660379 := bstep (se 1 (by rfl) ⟨1245284, by rfl⟩ : syracuseStep 1660379 = 2490569) B2490569
theorem B2840071 : Blo 1659529 2840071 := bstep (se 1 (by rfl) ⟨2130053, by rfl⟩ : syracuseStep 2840071 = 4260107) B4260107
theorem B3151399 : Blo 1659529 3151399 := bstep (se 1 (by rfl) ⟨2363549, by rfl⟩ : syracuseStep 3151399 = 4727099) B4727099
theorem B1660455 : Blo 1659529 1660455 := bstep (se 1 (by rfl) ⟨1245341, by rfl⟩ : syracuseStep 1660455 = 2490683) B2490683
theorem B2364967 : Blo 1659529 2364967 := bstep (se 1 (by rfl) ⟨1773725, by rfl⟩ : syracuseStep 2364967 = 3547451) B3547451
theorem B1660495 : Blo 1659529 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B1660511 : Blo 1659529 1660511 := bstep (se 1 (by rfl) ⟨1245383, by rfl⟩ : syracuseStep 1660511 = 2490767) B2490767
theorem B10638971 : Blo 1659529 10638971 := bstep (se 1 (by rfl) ⟨7979228, by rfl⟩ : syracuseStep 10638971 = 15958457) B15958457
theorem B1660539 : Blo 1659529 1660539 := bstep (se 1 (by rfl) ⟨1245404, by rfl⟩ : syracuseStep 1660539 = 2490809) B2490809
theorem B1660591 : Blo 1659529 1660591 := bstep (se 1 (by rfl) ⟨1245443, by rfl⟩ : syracuseStep 1660591 = 2490887) B2490887
theorem B1660615 : Blo 1659529 1660615 := bstep (se 1 (by rfl) ⟨1245461, by rfl⟩ : syracuseStep 1660615 = 2490923) B2490923
theorem B1660635 : Blo 1659529 1660635 := bstep (se 1 (by rfl) ⟨1245476, by rfl⟩ : syracuseStep 1660635 = 2490953) B2490953
theorem B1660711 : Blo 1659529 1660711 := bstep (se 1 (by rfl) ⟨1245533, by rfl⟩ : syracuseStep 1660711 = 2491067) B2491067
theorem B23033659 : Blo 1659529 23033659 := bstep (se 1 (by rfl) ⟨17275244, by rfl⟩ : syracuseStep 23033659 = 34550489) B34550489
theorem B1660751 : Blo 1659529 1660751 := bstep (se 1 (by rfl) ⟨1245563, by rfl⟩ : syracuseStep 1660751 = 2491127) B2491127
theorem B1660767 : Blo 1659529 1660767 := bstep (se 1 (by rfl) ⟨1245575, by rfl⟩ : syracuseStep 1660767 = 2491151) B2491151
theorem B1660795 : Blo 1659529 1660795 := bstep (se 1 (by rfl) ⟨1245596, by rfl⟩ : syracuseStep 1660795 = 2491193) B2491193
theorem B7575457 : Blo 1659529 7575457 := bstep (se 2 (by rfl) ⟨2840796, by rfl⟩ : syracuseStep 7575457 = 5681593) B5681593
theorem B1660847 : Blo 1659529 1660847 := bstep (se 1 (by rfl) ⟨1245635, by rfl⟩ : syracuseStep 1660847 = 2491271) B2491271
theorem B1660871 : Blo 1659529 1660871 := bstep (se 1 (by rfl) ⟨1245653, by rfl⟩ : syracuseStep 1660871 = 2491307) B2491307
theorem B35911633 : Blo 1659529 35911633 := bstep (se 2 (by rfl) ⟨13466862, by rfl⟩ : syracuseStep 35911633 = 26933725) B26933725
theorem B1660891 : Blo 1659529 1660891 := bstep (se 1 (by rfl) ⟨1245668, by rfl⟩ : syracuseStep 1660891 = 2491337) B2491337
theorem B1660967 : Blo 1659529 1660967 := bstep (se 1 (by rfl) ⟨1245725, by rfl⟩ : syracuseStep 1660967 = 2491451) B2491451
theorem B1661007 : Blo 1659529 1661007 := bstep (se 1 (by rfl) ⟨1245755, by rfl⟩ : syracuseStep 1661007 = 2491511) B2491511
theorem B7092305 : Blo 1659529 7092305 := bstep (se 2 (by rfl) ⟨2659614, by rfl⟩ : syracuseStep 7092305 = 5319229) B5319229
theorem B1661023 : Blo 1659529 1661023 := bstep (se 1 (by rfl) ⟨1245767, by rfl⟩ : syracuseStep 1661023 = 2491535) B2491535
theorem B1661051 : Blo 1659529 1661051 := bstep (se 1 (by rfl) ⟨1245788, by rfl⟩ : syracuseStep 1661051 = 2491577) B2491577
theorem B8403101 : Blo 1659529 8403101 := bstep (se 3 (by rfl) ⟨1575581, by rfl⟩ : syracuseStep 8403101 = 3151163) B3151163
theorem B1661103 : Blo 1659529 1661103 := bstep (se 1 (by rfl) ⟨1245827, by rfl⟩ : syracuseStep 1661103 = 2491655) B2491655
theorem B1661127 : Blo 1659529 1661127 := bstep (se 1 (by rfl) ⟨1245845, by rfl⟩ : syracuseStep 1661127 = 2491691) B2491691
theorem B1661147 : Blo 1659529 1661147 := bstep (se 1 (by rfl) ⟨1245860, by rfl⟩ : syracuseStep 1661147 = 2491721) B2491721
theorem B21272813 : Blo 1659529 21272813 := bstep (se 3 (by rfl) ⟨3988652, by rfl⟩ : syracuseStep 21272813 = 7977305) B7977305
theorem B5601527 : Blo 1659529 5601527 := bstep (se 1 (by rfl) ⟨4201145, by rfl⟩ : syracuseStep 5601527 = 8402291) B8402291
theorem B1661223 : Blo 1659529 1661223 := bstep (se 1 (by rfl) ⟨1245917, by rfl⟩ : syracuseStep 1661223 = 2491835) B2491835
theorem B1661263 : Blo 1659529 1661263 := bstep (se 1 (by rfl) ⟨1245947, by rfl⟩ : syracuseStep 1661263 = 2491895) B2491895
theorem B1661279 : Blo 1659529 1661279 := bstep (se 1 (by rfl) ⟨1245959, by rfl⟩ : syracuseStep 1661279 = 2491919) B2491919
theorem B1661307 : Blo 1659529 1661307 := bstep (se 1 (by rfl) ⟨1245980, by rfl⟩ : syracuseStep 1661307 = 2491961) B2491961
theorem B9460097 : Blo 1659529 9460097 := bstep (se 2 (by rfl) ⟨3547536, by rfl⟩ : syracuseStep 9460097 = 7095073) B7095073
theorem B2242991 : Blo 1659529 2242991 := bstep (se 1 (by rfl) ⟨1682243, by rfl⟩ : syracuseStep 2242991 = 3364487) B3364487
theorem B1661359 : Blo 1659529 1661359 := bstep (se 1 (by rfl) ⟨1246019, by rfl⟩ : syracuseStep 1661359 = 2492039) B2492039
theorem B1661383 : Blo 1659529 1661383 := bstep (se 1 (by rfl) ⟨1246037, by rfl⟩ : syracuseStep 1661383 = 2492075) B2492075
theorem B4200923 : Blo 1659529 4200923 := bstep (se 1 (by rfl) ⟨3150692, by rfl⟩ : syracuseStep 4200923 = 6301385) B6301385
theorem B1661403 : Blo 1659529 1661403 := bstep (se 1 (by rfl) ⟨1246052, by rfl⟩ : syracuseStep 1661403 = 2492105) B2492105
theorem B1661479 : Blo 1659529 1661479 := bstep (se 1 (by rfl) ⟨1246109, by rfl⟩ : syracuseStep 1661479 = 2492219) B2492219
theorem B5601851 : Blo 1659529 5601851 := bstep (se 1 (by rfl) ⟨4201388, by rfl⟩ : syracuseStep 5601851 = 8402777) B8402777
theorem B1661519 : Blo 1659529 1661519 := bstep (se 1 (by rfl) ⟨1246139, by rfl⟩ : syracuseStep 1661519 = 2492279) B2492279
theorem B6306443 : Blo 1659529 6306443 := bstep (se 1 (by rfl) ⟨4729832, by rfl⟩ : syracuseStep 6306443 = 9459665) B9459665
theorem B9099985 : Blo 1659529 9099985 := bstep (se 2 (by rfl) ⟨3412494, by rfl⟩ : syracuseStep 9099985 = 6824989) B6824989
theorem B18905885 : Blo 1659529 18905885 := bstep (se 3 (by rfl) ⟨3544853, by rfl⟩ : syracuseStep 18905885 = 7089707) B7089707
theorem B5602121 : Blo 1659529 5602121 := bstep (se 2 (by rfl) ⟨2100795, by rfl⟩ : syracuseStep 5602121 = 4201591) B4201591
theorem B10779499 : Blo 1659529 10779499 := bstep (se 1 (by rfl) ⟨8084624, by rfl⟩ : syracuseStep 10779499 = 16169249) B16169249
theorem B12606353 : Blo 1659529 12606353 := bstep (se 2 (by rfl) ⟨4727382, by rfl⟩ : syracuseStep 12606353 = 9454765) B9454765
theorem B3988385 : Blo 1659529 3988385 := bstep (se 2 (by rfl) ⟨1495644, by rfl⟩ : syracuseStep 3988385 = 2991289) B2991289
theorem B3734459 : Blo 1659529 3734459 := bstep (se 1 (by rfl) ⟨2800844, by rfl⟩ : syracuseStep 3734459 = 5601689) B5601689
theorem B3546119 : Blo 1659529 3546119 := bstep (se 1 (by rfl) ⟨2659589, by rfl⟩ : syracuseStep 3546119 = 5319179) B5319179
theorem B2800649 : Blo 1659529 2800649 := bstep (se 2 (by rfl) ⟨1050243, by rfl⟩ : syracuseStep 2800649 = 2100487) B2100487
theorem B2661383 : Blo 1659529 2661383 := bstep (se 1 (by rfl) ⟨1996037, by rfl⟩ : syracuseStep 2661383 = 3992075) B3992075
theorem B8092691 : Blo 1659529 8092691 := bstep (se 1 (by rfl) ⟨6069518, by rfl⟩ : syracuseStep 8092691 = 12139037) B12139037
theorem B3734585 : Blo 1659529 3734585 := bstep (se 2 (by rfl) ⟨1400469, by rfl⟩ : syracuseStep 3734585 = 2800939) B2800939
theorem B2489423 : Blo 1659529 2489423 := bstep (se 1 (by rfl) ⟨1867067, by rfl⟩ : syracuseStep 2489423 = 3734135) B3734135
theorem B15957071 : Blo 1659529 15957071 := bstep (se 1 (by rfl) ⟨11967803, by rfl⟩ : syracuseStep 15957071 = 23935607) B23935607
theorem B2800811 : Blo 1659529 2800811 := bstep (se 1 (by rfl) ⟨2100608, by rfl⟩ : syracuseStep 2800811 = 4201217) B4201217
theorem B2489543 : Blo 1659529 2489543 := bstep (se 1 (by rfl) ⟨1867157, by rfl⟩ : syracuseStep 2489543 = 3734315) B3734315
theorem B3153107 : Blo 1659529 3153107 := bstep (se 1 (by rfl) ⟨2364830, by rfl⟩ : syracuseStep 3153107 = 4729661) B4729661
theorem B2489705 : Blo 1659529 2489705 := bstep (se 2 (by rfl) ⟨933639, by rfl⟩ : syracuseStep 2489705 = 1867279) B1867279
theorem B3153259 : Blo 1659529 3153259 := bstep (se 1 (by rfl) ⟨2364944, by rfl⟩ : syracuseStep 3153259 = 4729889) B4729889
theorem B3734927 : Blo 1659529 3734927 := bstep (se 1 (by rfl) ⟨2801195, by rfl⟩ : syracuseStep 3734927 = 5602391) B5602391
theorem B3194273 : Blo 1659529 3194273 := bstep (se 2 (by rfl) ⟨1197852, by rfl⟩ : syracuseStep 3194273 = 2395705) B2395705
theorem B8404397 : Blo 1659529 8404397 := bstep (se 3 (by rfl) ⟨1575824, by rfl⟩ : syracuseStep 8404397 = 3151649) B3151649
theorem B2489783 : Blo 1659529 2489783 := bstep (se 1 (by rfl) ⟨1867337, by rfl⟩ : syracuseStep 2489783 = 3734675) B3734675
theorem B2489819 : Blo 1659529 2489819 := bstep (se 1 (by rfl) ⟨1867364, by rfl⟩ : syracuseStep 2489819 = 3734729) B3734729
theorem B2801209 : Blo 1659529 2801209 := bstep (se 2 (by rfl) ⟨1050453, by rfl⟩ : syracuseStep 2801209 = 2100907) B2100907
theorem B3153487 : Blo 1659529 3153487 := bstep (se 1 (by rfl) ⟨2365115, by rfl⟩ : syracuseStep 3153487 = 4730231) B4730231
theorem B1867387 : Blo 1659529 1867387 := bstep (se 1 (by rfl) ⟨1400540, by rfl⟩ : syracuseStep 1867387 = 2801081) B2801081
theorem B2801351 : Blo 1659529 2801351 := bstep (se 1 (by rfl) ⟨2101013, by rfl⟩ : syracuseStep 2801351 = 4202027) B4202027
theorem B3989191 : Blo 1659529 3989191 := bstep (se 1 (by rfl) ⟨2991893, by rfl⟩ : syracuseStep 3989191 = 5983787) B5983787
theorem B3735251 : Blo 1659529 3735251 := bstep (se 1 (by rfl) ⟨2801438, by rfl⟩ : syracuseStep 3735251 = 5602877) B5602877
theorem B3366611 : Blo 1659529 3366611 := bstep (se 1 (by rfl) ⟨2524958, by rfl⟩ : syracuseStep 3366611 = 5049917) B5049917
theorem B2801513 : Blo 1659529 2801513 := bstep (se 2 (by rfl) ⟨1050567, by rfl⟩ : syracuseStep 2801513 = 2101135) B2101135
theorem B17956727 : Blo 1659529 17956727 := bstep (se 1 (by rfl) ⟨13467545, by rfl⟩ : syracuseStep 17956727 = 26935091) B26935091
theorem B15966071 : Blo 1659529 15966071 := bstep (se 1 (by rfl) ⟨11974553, by rfl⟩ : syracuseStep 15966071 = 23949107) B23949107
theorem B6307703 : Blo 1659529 6307703 := bstep (se 1 (by rfl) ⟨4730777, by rfl⟩ : syracuseStep 6307703 = 9461555) B9461555
theorem B4202401 : Blo 1659529 4202401 := bstep (se 2 (by rfl) ⟨1575900, by rfl⟩ : syracuseStep 4202401 = 3151801) B3151801
theorem B2490287 : Blo 1659529 2490287 := bstep (se 1 (by rfl) ⟨1867715, by rfl⟩ : syracuseStep 2490287 = 3735431) B3735431
theorem B5603255 : Blo 1659529 5603255 := bstep (se 1 (by rfl) ⟨4202441, by rfl⟩ : syracuseStep 5603255 = 8404883) B8404883
theorem B2490473 : Blo 1659529 2490473 := bstep (se 2 (by rfl) ⟨933927, by rfl⟩ : syracuseStep 2490473 = 1867855) B1867855
theorem B3367177 : Blo 1659529 3367177 := bstep (se 2 (by rfl) ⟨1262691, by rfl⟩ : syracuseStep 3367177 = 2525383) B2525383
theorem B1868071 : Blo 1659529 1868071 := bstep (se 1 (by rfl) ⟨1401053, by rfl⟩ : syracuseStep 1868071 = 2802107) B2802107
theorem B3735881 : Blo 1659529 3735881 := bstep (se 2 (by rfl) ⟨1400955, by rfl⟩ : syracuseStep 3735881 = 2801911) B2801911
theorem B3031387 : Blo 1659529 3031387 := bstep (se 1 (by rfl) ⟨2273540, by rfl⟩ : syracuseStep 3031387 = 4547081) B4547081
theorem B3735899 : Blo 1659529 3735899 := bstep (se 1 (by rfl) ⟨2801924, by rfl⟩ : syracuseStep 3735899 = 5603849) B5603849
theorem B8978795 : Blo 1659529 8978795 := bstep (se 1 (by rfl) ⟨6734096, by rfl⟩ : syracuseStep 8978795 = 13468193) B13468193
theorem B1868143 : Blo 1659529 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B2490791 : Blo 1659529 2490791 := bstep (se 1 (by rfl) ⟨1868093, by rfl⟩ : syracuseStep 2490791 = 3736187) B3736187
theorem B2490875 : Blo 1659529 2490875 := bstep (se 1 (by rfl) ⟨1868156, by rfl⟩ : syracuseStep 2490875 = 3736313) B3736313
theorem B4727315 : Blo 1659529 4727315 := bstep (se 1 (by rfl) ⟨3545486, by rfl⟩ : syracuseStep 4727315 = 7090973) B7090973
theorem B1868359 : Blo 1659529 1868359 := bstep (se 1 (by rfl) ⟨1401269, by rfl⟩ : syracuseStep 1868359 = 2802539) B2802539
theorem B2491001 : Blo 1659529 2491001 := bstep (se 2 (by rfl) ⟨934125, by rfl⟩ : syracuseStep 2491001 = 1868251) B1868251
theorem B5604011 : Blo 1659529 5604011 := bstep (se 1 (by rfl) ⟨4203008, by rfl⟩ : syracuseStep 5604011 = 8406017) B8406017
theorem B2491055 : Blo 1659529 2491055 := bstep (se 1 (by rfl) ⟨1868291, by rfl⟩ : syracuseStep 2491055 = 3736583) B3736583
theorem B4203191 : Blo 1659529 4203191 := bstep (se 1 (by rfl) ⟨3152393, by rfl⟩ : syracuseStep 4203191 = 6304787) B6304787
theorem B2491103 : Blo 1659529 2491103 := bstep (se 1 (by rfl) ⟨1868327, by rfl⟩ : syracuseStep 2491103 = 3736655) B3736655
theorem B8405855 : Blo 1659529 8405855 := bstep (se 1 (by rfl) ⟨6304391, by rfl⟩ : syracuseStep 8405855 = 12608783) B12608783
theorem B3736475 : Blo 1659529 3736475 := bstep (se 1 (by rfl) ⟨2802356, by rfl⟩ : syracuseStep 3736475 = 5604713) B5604713
theorem B12133313 : Blo 1659529 12133313 := bstep (se 2 (by rfl) ⟨4549992, by rfl⟩ : syracuseStep 12133313 = 9099985) B9099985
theorem B4727771 : Blo 1659529 4727771 := bstep (se 1 (by rfl) ⟨3545828, by rfl⟩ : syracuseStep 4727771 = 7091657) B7091657
theorem B2491367 : Blo 1659529 2491367 := bstep (se 1 (by rfl) ⟨1868525, by rfl⟩ : syracuseStep 2491367 = 3737051) B3737051
theorem B3736673 : Blo 1659529 3736673 := bstep (se 2 (by rfl) ⟨1401252, by rfl⟩ : syracuseStep 3736673 = 2802505) B2802505
theorem B5981309 : Blo 1659529 5981309 := bstep (se 3 (by rfl) ⟨1121495, by rfl⟩ : syracuseStep 5981309 = 2242991) B2242991
theorem B5604551 : Blo 1659529 5604551 := bstep (se 1 (by rfl) ⟨4203413, by rfl⟩ : syracuseStep 5604551 = 8406827) B8406827
theorem B2491625 : Blo 1659529 2491625 := bstep (se 2 (by rfl) ⟨934359, by rfl⟩ : syracuseStep 2491625 = 1868719) B1868719
theorem B2491679 : Blo 1659529 2491679 := bstep (se 1 (by rfl) ⟨1868759, by rfl⟩ : syracuseStep 2491679 = 3737519) B3737519
theorem B3736871 : Blo 1659529 3736871 := bstep (se 1 (by rfl) ⟨2802653, by rfl⟩ : syracuseStep 3736871 = 5605307) B5605307
theorem B4728203 : Blo 1659529 4728203 := bstep (se 1 (by rfl) ⟨3546152, by rfl⟩ : syracuseStep 4728203 = 7092305) B7092305
theorem B2131367 : Blo 1659529 2131367 := bstep (se 1 (by rfl) ⟨1598525, by rfl⟩ : syracuseStep 2131367 = 3197051) B3197051
theorem B2491847 : Blo 1659529 2491847 := bstep (se 1 (by rfl) ⟨1868885, by rfl⟩ : syracuseStep 2491847 = 3737771) B3737771
theorem B14181875 : Blo 1659529 14181875 := bstep (se 1 (by rfl) ⟨10636406, by rfl⟩ : syracuseStep 14181875 = 21272813) B21272813
theorem B2803295 : Blo 1659529 2803295 := bstep (se 1 (by rfl) ⟨2102471, by rfl⟩ : syracuseStep 2803295 = 4204943) B4204943
theorem B3737249 : Blo 1659529 3737249 := bstep (se 2 (by rfl) ⟨1401468, by rfl⟩ : syracuseStep 3737249 = 2802937) B2802937
theorem B7095995 : Blo 1659529 7095995 := bstep (se 1 (by rfl) ⟨5321996, by rfl⟩ : syracuseStep 7095995 = 10643993) B10643993
theorem B4204295 : Blo 1659529 4204295 := bstep (se 1 (by rfl) ⟨3153221, by rfl⟩ : syracuseStep 4204295 = 6306443) B6306443
theorem B2492201 : Blo 1659529 2492201 := bstep (se 2 (by rfl) ⟨934575, by rfl⟩ : syracuseStep 2492201 = 1869151) B1869151
theorem B2492207 : Blo 1659529 2492207 := bstep (se 1 (by rfl) ⟨1869155, by rfl⟩ : syracuseStep 2492207 = 3738311) B3738311
theorem B2803511 : Blo 1659529 2803511 := bstep (se 1 (by rfl) ⟨2102633, by rfl⟩ : syracuseStep 2803511 = 4205267) B4205267
theorem B4204345 : Blo 1659529 4204345 := bstep (se 2 (by rfl) ⟨1576629, by rfl⟩ : syracuseStep 4204345 = 3153259) B3153259
theorem B26617837 : Blo 1659529 26617837 := bstep (se 3 (by rfl) ⟨4990844, by rfl⟩ : syracuseStep 26617837 = 9981689) B9981689
theorem B7981037 : Blo 1659529 7981037 := bstep (se 3 (by rfl) ⟨1496444, by rfl⟩ : syracuseStep 7981037 = 2992889) B2992889
theorem B3786761 : Blo 1659529 3786761 := bstep (se 2 (by rfl) ⟨1420035, by rfl⟩ : syracuseStep 3786761 = 2840071) B2840071
theorem B3737609 : Blo 1659529 3737609 := bstep (se 2 (by rfl) ⟨1401603, by rfl⟩ : syracuseStep 3737609 = 2803207) B2803207
theorem B4204649 : Blo 1659529 4204649 := bstep (se 2 (by rfl) ⟨1576743, by rfl⟩ : syracuseStep 4204649 = 3153487) B3153487
theorem B5318921 : Blo 1659529 5318921 := bstep (se 2 (by rfl) ⟨1994595, by rfl⟩ : syracuseStep 5318921 = 3989191) B3989191
theorem B10103069 : Blo 1659529 10103069 := bstep (se 3 (by rfl) ⟨1894325, by rfl⟩ : syracuseStep 10103069 = 3788651) B3788651
theorem B17959279 : Blo 1659529 17959279 := bstep (se 1 (by rfl) ⟨13469459, by rfl⟩ : syracuseStep 17959279 = 26938919) B26938919
theorem B3738023 : Blo 1659529 3738023 := bstep (se 1 (by rfl) ⟨2803517, by rfl⟩ : syracuseStep 3738023 = 5607035) B5607035
theorem B3738131 : Blo 1659529 3738131 := bstep (se 1 (by rfl) ⟨2803598, by rfl⟩ : syracuseStep 3738131 = 5607197) B5607197
theorem B3738185 : Blo 1659529 3738185 := bstep (se 2 (by rfl) ⟨1401819, by rfl⟩ : syracuseStep 3738185 = 2803639) B2803639
theorem B11971151 : Blo 1659529 11971151 := bstep (se 1 (by rfl) ⟨8978363, by rfl⟩ : syracuseStep 11971151 = 17956727) B17956727
theorem B10644047 : Blo 1659529 10644047 := bstep (se 1 (by rfl) ⟨7983035, by rfl⟩ : syracuseStep 10644047 = 15966071) B15966071
theorem B4205135 : Blo 1659529 4205135 := bstep (se 1 (by rfl) ⟨3153851, by rfl⟩ : syracuseStep 4205135 = 6307703) B6307703
theorem B1796783 : Blo 1659529 1796783 := bstep (se 1 (by rfl) ⟨1347587, by rfl⟩ : syracuseStep 1796783 = 2695175) B2695175
theorem B5606063 : Blo 1659529 5606063 := bstep (se 1 (by rfl) ⟨4204547, by rfl⟩ : syracuseStep 5606063 = 8409095) B8409095
theorem B7097021 : Blo 1659529 7097021 := bstep (se 3 (by rfl) ⟨1330691, by rfl⟩ : syracuseStep 7097021 = 2661383) B2661383
theorem B7088887 : Blo 1659529 7088887 := bstep (se 1 (by rfl) ⟨5316665, by rfl⟩ : syracuseStep 7088887 = 10633331) B10633331
theorem B8407799 : Blo 1659529 8407799 := bstep (se 1 (by rfl) ⟨6305849, by rfl⟩ : syracuseStep 8407799 = 12611699) B12611699
theorem B4803571 : Blo 1659529 4803571 := bstep (se 1 (by rfl) ⟨3602678, by rfl⟩ : syracuseStep 4803571 = 7205357) B7205357
theorem B4729843 : Blo 1659529 4729843 := bstep (se 1 (by rfl) ⟨3547382, by rfl⟩ : syracuseStep 4729843 = 7094765) B7094765
theorem B5606387 : Blo 1659529 5606387 := bstep (se 1 (by rfl) ⟨4204790, by rfl⟩ : syracuseStep 5606387 = 8409581) B8409581
theorem B6302843 : Blo 1659529 6302843 := bstep (se 1 (by rfl) ⟨4727132, by rfl⟩ : syracuseStep 6302843 = 9454265) B9454265
theorem B4549771 : Blo 1659529 4549771 := bstep (se 1 (by rfl) ⟨3412328, by rfl⟩ : syracuseStep 4549771 = 6824657) B6824657
theorem B31935667 : Blo 1659529 31935667 := bstep (se 1 (by rfl) ⟨23951750, by rfl⟩ : syracuseStep 31935667 = 47903501) B47903501
theorem B4861147 : Blo 1659529 4861147 := bstep (se 1 (by rfl) ⟨3645860, by rfl⟩ : syracuseStep 4861147 = 7291721) B7291721
theorem B8408285 : Blo 1659529 8408285 := bstep (se 3 (by rfl) ⟨1576553, by rfl⟩ : syracuseStep 8408285 = 3153107) B3153107
theorem B5606927 : Blo 1659529 5606927 := bstep (se 1 (by rfl) ⟨4205195, by rfl⟩ : syracuseStep 5606927 = 8410391) B8410391
theorem B7982687 : Blo 1659529 7982687 := bstep (se 1 (by rfl) ⟨5987015, by rfl⟩ : syracuseStep 7982687 = 11974031) B11974031
theorem B71840033 : Blo 1659529 71840033 := bstep (se 2 (by rfl) ⟨26940012, by rfl⟩ : syracuseStep 71840033 = 53880025) B53880025
theorem B12603923 : Blo 1659529 12603923 := bstep (se 1 (by rfl) ⟨9452942, by rfl⟩ : syracuseStep 12603923 = 18905885) B18905885
theorem B17035825 : Blo 1659529 17035825 := bstep (se 2 (by rfl) ⟨6388434, by rfl⟩ : syracuseStep 17035825 = 12776869) B12776869
theorem B28365389 : Blo 1659529 28365389 := bstep (se 3 (by rfl) ⟨5318510, by rfl⟩ : syracuseStep 28365389 = 10637021) B10637021
theorem B2658923 : Blo 1659529 2658923 := bstep (se 1 (by rfl) ⟨1994192, by rfl⟩ : syracuseStep 2658923 = 3988385) B3988385
theorem B2364079 : Blo 1659529 2364079 := bstep (se 1 (by rfl) ⟨1773059, by rfl⟩ : syracuseStep 2364079 = 3546119) B3546119
theorem B5395127 : Blo 1659529 5395127 := bstep (se 1 (by rfl) ⟨4046345, by rfl⟩ : syracuseStep 5395127 = 8092691) B8092691
theorem B1659615 : Blo 1659529 1659615 := bstep (se 1 (by rfl) ⟨1244711, by rfl⟩ : syracuseStep 1659615 = 2489423) B2489423
theorem B10638047 : Blo 1659529 10638047 := bstep (se 1 (by rfl) ⟨7978535, by rfl⟩ : syracuseStep 10638047 = 15957071) B15957071
theorem B1995499 : Blo 1659529 1995499 := bstep (se 1 (by rfl) ⟨1496624, by rfl⟩ : syracuseStep 1995499 = 2993249) B2993249
theorem B1659695 : Blo 1659529 1659695 := bstep (se 1 (by rfl) ⟨1244771, by rfl⟩ : syracuseStep 1659695 = 2489543) B2489543
theorem B30282569 : Blo 1659529 30282569 := bstep (se 2 (by rfl) ⟨11355963, by rfl⟩ : syracuseStep 30282569 = 22711927) B22711927
theorem B1659803 : Blo 1659529 1659803 := bstep (se 1 (by rfl) ⟨1244852, by rfl⟩ : syracuseStep 1659803 = 2489705) B2489705
theorem B1659855 : Blo 1659529 1659855 := bstep (se 1 (by rfl) ⟨1244891, by rfl⟩ : syracuseStep 1659855 = 2489783) B2489783
theorem B1659879 : Blo 1659529 1659879 := bstep (se 1 (by rfl) ⟨1244909, by rfl⟩ : syracuseStep 1659879 = 2489819) B2489819
theorem B11973689 : Blo 1659529 11973689 := bstep (se 2 (by rfl) ⟨4490133, by rfl⟩ : syracuseStep 11973689 = 8980267) B8980267
theorem B16168081 : Blo 1659529 16168081 := bstep (se 2 (by rfl) ⟨6063030, by rfl⟩ : syracuseStep 16168081 = 12126061) B12126061
theorem B23925917 : Blo 1659529 23925917 := bstep (se 3 (by rfl) ⟨4486109, by rfl⟩ : syracuseStep 23925917 = 8972219) B8972219
theorem B13464791 : Blo 1659529 13464791 := bstep (se 1 (by rfl) ⟨10098593, by rfl⟩ : syracuseStep 13464791 = 20197187) B20197187
theorem B1660191 : Blo 1659529 1660191 := bstep (se 1 (by rfl) ⟨1245143, by rfl⟩ : syracuseStep 1660191 = 2490287) B2490287
theorem B1660251 : Blo 1659529 1660251 := bstep (se 1 (by rfl) ⟨1245188, by rfl⟩ : syracuseStep 1660251 = 2490377) B2490377
theorem B1660271 : Blo 1659529 1660271 := bstep (se 1 (by rfl) ⟨1245203, by rfl⟩ : syracuseStep 1660271 = 2490407) B2490407
theorem B6387083 : Blo 1659529 6387083 := bstep (se 1 (by rfl) ⟨4790312, by rfl⟩ : syracuseStep 6387083 = 9580625) B9580625
theorem B1660327 : Blo 1659529 1660327 := bstep (se 1 (by rfl) ⟨1245245, by rfl⟩ : syracuseStep 1660327 = 2490491) B2490491
theorem B2364871 : Blo 1659529 2364871 := bstep (se 1 (by rfl) ⟨1773653, by rfl⟩ : syracuseStep 2364871 = 3547307) B3547307
theorem B1660411 : Blo 1659529 1660411 := bstep (se 1 (by rfl) ⟨1245308, by rfl⟩ : syracuseStep 1660411 = 2490617) B2490617
theorem B12613157 : Blo 1659529 12613157 := bstep (se 4 (by rfl) ⟨1182483, by rfl⟩ : syracuseStep 12613157 = 2364967) B2364967
theorem B1660479 : Blo 1659529 1660479 := bstep (se 1 (by rfl) ⟨1245359, by rfl⟩ : syracuseStep 1660479 = 2490719) B2490719
theorem B1660487 : Blo 1659529 1660487 := bstep (se 1 (by rfl) ⟨1245365, by rfl⟩ : syracuseStep 1660487 = 2490731) B2490731
theorem B35886725 : Blo 1659529 35886725 := bstep (se 4 (by rfl) ⟨3364380, by rfl⟩ : syracuseStep 35886725 = 6728761) B6728761
theorem B1660639 : Blo 1659529 1660639 := bstep (se 1 (by rfl) ⟨1245479, by rfl⟩ : syracuseStep 1660639 = 2490959) B2490959
theorem B3364649 : Blo 1659529 3364649 := bstep (se 2 (by rfl) ⟨1261743, by rfl⟩ : syracuseStep 3364649 = 2523487) B2523487
theorem B1660719 : Blo 1659529 1660719 := bstep (se 1 (by rfl) ⟨1245539, by rfl⟩ : syracuseStep 1660719 = 2491079) B2491079
theorem B15955805 : Blo 1659529 15955805 := bstep (se 3 (by rfl) ⟨2991713, by rfl⟩ : syracuseStep 15955805 = 5983427) B5983427
theorem B1660827 : Blo 1659529 1660827 := bstep (se 1 (by rfl) ⟨1245620, by rfl⟩ : syracuseStep 1660827 = 2491241) B2491241
theorem B1660879 : Blo 1659529 1660879 := bstep (se 1 (by rfl) ⟨1245659, by rfl⟩ : syracuseStep 1660879 = 2491319) B2491319
theorem B1660903 : Blo 1659529 1660903 := bstep (se 1 (by rfl) ⟨1245677, by rfl⟩ : syracuseStep 1660903 = 2491355) B2491355
theorem B3987721 : Blo 1659529 3987721 := bstep (se 2 (by rfl) ⟨1495395, by rfl⟩ : syracuseStep 3987721 = 2990791) B2990791
theorem B1661215 : Blo 1659529 1661215 := bstep (se 1 (by rfl) ⟨1245911, by rfl⟩ : syracuseStep 1661215 = 2491823) B2491823
theorem B1661275 : Blo 1659529 1661275 := bstep (se 1 (by rfl) ⟨1245956, by rfl⟩ : syracuseStep 1661275 = 2491913) B2491913
theorem B1661295 : Blo 1659529 1661295 := bstep (se 1 (by rfl) ⟨1245971, by rfl⟩ : syracuseStep 1661295 = 2491943) B2491943
theorem B7092647 : Blo 1659529 7092647 := bstep (se 1 (by rfl) ⟨5319485, by rfl⟩ : syracuseStep 7092647 = 10638971) B10638971
theorem B1661351 : Blo 1659529 1661351 := bstep (se 1 (by rfl) ⟨1246013, by rfl⟩ : syracuseStep 1661351 = 2492027) B2492027
theorem B8518061 : Blo 1659529 8518061 := bstep (se 3 (by rfl) ⟨1597136, by rfl⟩ : syracuseStep 8518061 = 3194273) B3194273
theorem B1661435 : Blo 1659529 1661435 := bstep (se 1 (by rfl) ⟨1246076, by rfl⟩ : syracuseStep 1661435 = 2492153) B2492153
theorem B1661503 : Blo 1659529 1661503 := bstep (se 1 (by rfl) ⟨1246127, by rfl⟩ : syracuseStep 1661503 = 2492255) B2492255
theorem B1661511 : Blo 1659529 1661511 := bstep (se 1 (by rfl) ⟨1246133, by rfl⟩ : syracuseStep 1661511 = 2492267) B2492267
theorem B5602067 : Blo 1659529 5602067 := bstep (se 1 (by rfl) ⟨4201550, by rfl⟩ : syracuseStep 5602067 = 8403101) B8403101
theorem B3734351 : Blo 1659529 3734351 := bstep (se 1 (by rfl) ⟨2800763, by rfl⟩ : syracuseStep 3734351 = 5601527) B5601527
theorem B6306731 : Blo 1659529 6306731 := bstep (se 1 (by rfl) ⟨4730048, by rfl⟩ : syracuseStep 6306731 = 9460097) B9460097
theorem B12786605 : Blo 1659529 12786605 := bstep (se 3 (by rfl) ⟨2397488, by rfl⟩ : syracuseStep 12786605 = 4794977) B4794977
theorem B2800615 : Blo 1659529 2800615 := bstep (se 1 (by rfl) ⟨2100461, by rfl⟩ : syracuseStep 2800615 = 4200923) B4200923
theorem B3734567 : Blo 1659529 3734567 := bstep (se 1 (by rfl) ⟨2800925, by rfl⟩ : syracuseStep 3734567 = 5601851) B5601851
theorem B3734747 : Blo 1659529 3734747 := bstep (se 1 (by rfl) ⟨2801060, by rfl⟩ : syracuseStep 3734747 = 5602121) B5602121
theorem B57490661 : Blo 1659529 57490661 := bstep (se 4 (by rfl) ⟨5389749, by rfl⟩ : syracuseStep 57490661 = 10779499) B10779499
theorem B8404235 : Blo 1659529 8404235 := bstep (se 1 (by rfl) ⟨6303176, by rfl⟩ : syracuseStep 8404235 = 12606353) B12606353
theorem B2489639 : Blo 1659529 2489639 := bstep (se 1 (by rfl) ⟨1867229, by rfl⟩ : syracuseStep 2489639 = 3734459) B3734459
theorem B1867099 : Blo 1659529 1867099 := bstep (se 1 (by rfl) ⟨1400324, by rfl⟩ : syracuseStep 1867099 = 2800649) B2800649
theorem B2489723 : Blo 1659529 2489723 := bstep (se 1 (by rfl) ⟨1867292, by rfl⟩ : syracuseStep 2489723 = 3734585) B3734585
theorem B4201865 : Blo 1659529 4201865 := bstep (se 2 (by rfl) ⟨1575699, by rfl⟩ : syracuseStep 4201865 = 3151399) B3151399
theorem B3734945 : Blo 1659529 3734945 := bstep (se 2 (by rfl) ⟨1400604, by rfl⟩ : syracuseStep 3734945 = 2801209) B2801209
theorem B4201915 : Blo 1659529 4201915 := bstep (se 1 (by rfl) ⟨3151436, by rfl⟩ : syracuseStep 4201915 = 6302873) B6302873
theorem B1867207 : Blo 1659529 1867207 := bstep (se 1 (by rfl) ⟨1400405, by rfl⟩ : syracuseStep 1867207 = 2800811) B2800811
theorem B2489849 : Blo 1659529 2489849 := bstep (se 2 (by rfl) ⟨933693, by rfl⟩ : syracuseStep 2489849 = 1867387) B1867387
theorem B27287063 : Blo 1659529 27287063 := bstep (se 1 (by rfl) ⟨20465297, by rfl⟩ : syracuseStep 27287063 = 40930595) B40930595
theorem B6823507 : Blo 1659529 6823507 := bstep (se 1 (by rfl) ⟨5117630, by rfl⟩ : syracuseStep 6823507 = 10235261) B10235261
theorem B2489951 : Blo 1659529 2489951 := bstep (se 1 (by rfl) ⟨1867463, by rfl⟩ : syracuseStep 2489951 = 3734927) B3734927
theorem B5602931 : Blo 1659529 5602931 := bstep (se 1 (by rfl) ⟨4202198, by rfl⟩ : syracuseStep 5602931 = 8404397) B8404397
theorem B4202219 : Blo 1659529 4202219 := bstep (se 1 (by rfl) ⟨3151664, by rfl⟩ : syracuseStep 4202219 = 6303329) B6303329
theorem B30711545 : Blo 1659529 30711545 := bstep (se 2 (by rfl) ⟨11516829, by rfl⟩ : syracuseStep 30711545 = 23033659) B23033659
theorem B1867567 : Blo 1659529 1867567 := bstep (se 1 (by rfl) ⟨1400675, by rfl⟩ : syracuseStep 1867567 = 2801351) B2801351
theorem B2490167 : Blo 1659529 2490167 := bstep (se 1 (by rfl) ⟨1867625, by rfl⟩ : syracuseStep 2490167 = 3735251) B3735251
theorem B2244407 : Blo 1659529 2244407 := bstep (se 1 (by rfl) ⟨1683305, by rfl⟩ : syracuseStep 2244407 = 3366611) B3366611
theorem B5603201 : Blo 1659529 5603201 := bstep (se 2 (by rfl) ⟨2101200, by rfl⟩ : syracuseStep 5603201 = 4202401) B4202401
theorem B10100609 : Blo 1659529 10100609 := bstep (se 2 (by rfl) ⟨3787728, by rfl⟩ : syracuseStep 10100609 = 7575457) B7575457
theorem B1867675 : Blo 1659529 1867675 := bstep (se 1 (by rfl) ⟨1400756, by rfl⟩ : syracuseStep 1867675 = 2801513) B2801513
theorem B17948591 : Blo 1659529 17948591 := bstep (se 1 (by rfl) ⟨13461443, by rfl⟩ : syracuseStep 17948591 = 26922887) B26922887
theorem B47882177 : Blo 1659529 47882177 := bstep (se 2 (by rfl) ⟨17955816, by rfl⟩ : syracuseStep 47882177 = 35911633) B35911633
theorem B3735503 : Blo 1659529 3735503 := bstep (se 1 (by rfl) ⟨2801627, by rfl⟩ : syracuseStep 3735503 = 5603255) B5603255
theorem B2490587 : Blo 1659529 2490587 := bstep (se 1 (by rfl) ⟨1867940, by rfl⟩ : syracuseStep 2490587 = 3735881) B3735881
theorem B2490599 : Blo 1659529 2490599 := bstep (se 1 (by rfl) ⟨1867949, by rfl⟩ : syracuseStep 2490599 = 3735899) B3735899
theorem B2490761 : Blo 1659529 2490761 := bstep (se 2 (by rfl) ⟨934035, by rfl⟩ : syracuseStep 2490761 = 1868071) B1868071
theorem B3736007 : Blo 1659529 3736007 := bstep (se 1 (by rfl) ⟨2802005, by rfl⟩ : syracuseStep 3736007 = 5604011) B5604011
theorem B2802127 : Blo 1659529 2802127 := bstep (se 1 (by rfl) ⟨2101595, by rfl⟩ : syracuseStep 2802127 = 4203191) B4203191
theorem B2490857 : Blo 1659529 2490857 := bstep (se 2 (by rfl) ⟨934071, by rfl⟩ : syracuseStep 2490857 = 1868143) B1868143
theorem B23945705 : Blo 1659529 23945705 := bstep (se 2 (by rfl) ⟨8979639, by rfl⟩ : syracuseStep 23945705 = 17959279) B17959279
theorem B5603903 : Blo 1659529 5603903 := bstep (se 1 (by rfl) ⟨4202927, by rfl⟩ : syracuseStep 5603903 = 8405855) B8405855
theorem B2490983 : Blo 1659529 2490983 := bstep (se 1 (by rfl) ⟨1868237, by rfl⟩ : syracuseStep 2490983 = 3736475) B3736475
theorem B2491115 : Blo 1659529 2491115 := bstep (se 1 (by rfl) ⟨1868336, by rfl⟩ : syracuseStep 2491115 = 3736673) B3736673
theorem B2491145 : Blo 1659529 2491145 := bstep (se 2 (by rfl) ⟨934179, by rfl⟩ : syracuseStep 2491145 = 1868359) B1868359
theorem B15950611 : Blo 1659529 15950611 := bstep (se 1 (by rfl) ⟨11962958, by rfl⟩ : syracuseStep 15950611 = 23925917) B23925917
theorem B3736367 : Blo 1659529 3736367 := bstep (se 1 (by rfl) ⟨2802275, by rfl⟩ : syracuseStep 3736367 = 5604551) B5604551
theorem B2491247 : Blo 1659529 2491247 := bstep (se 1 (by rfl) ⟨1868435, by rfl⟩ : syracuseStep 2491247 = 3736871) B3736871
theorem B9454583 : Blo 1659529 9454583 := bstep (se 1 (by rfl) ⟨7090937, by rfl⟩ : syracuseStep 9454583 = 14181875) B14181875
theorem B1868863 : Blo 1659529 1868863 := bstep (se 1 (by rfl) ⟨1401647, by rfl⟩ : syracuseStep 1868863 = 2803295) B2803295
theorem B2491499 : Blo 1659529 2491499 := bstep (se 1 (by rfl) ⟨1868624, by rfl⟩ : syracuseStep 2491499 = 3737249) B3737249
theorem B2802863 : Blo 1659529 2802863 := bstep (se 1 (by rfl) ⟨2102147, by rfl⟩ : syracuseStep 2802863 = 4204295) B4204295
theorem B1869007 : Blo 1659529 1869007 := bstep (se 1 (by rfl) ⟨1401755, by rfl⟩ : syracuseStep 1869007 = 2803511) B2803511
theorem B10642661 : Blo 1659529 10642661 := bstep (se 4 (by rfl) ⟨997749, by rfl⟩ : syracuseStep 10642661 = 1995499) B1995499
theorem B2491739 : Blo 1659529 2491739 := bstep (se 1 (by rfl) ⟨1868804, by rfl⟩ : syracuseStep 2491739 = 3737609) B3737609
theorem B21267845 : Blo 1659529 21267845 := bstep (se 4 (by rfl) ⟨1993860, by rfl⟩ : syracuseStep 21267845 = 3987721) B3987721
theorem B17958277 : Blo 1659529 17958277 := bstep (se 4 (by rfl) ⟨1683588, by rfl⟩ : syracuseStep 17958277 = 3367177) B3367177
theorem B2803099 : Blo 1659529 2803099 := bstep (se 1 (by rfl) ⟨2102324, by rfl⟩ : syracuseStep 2803099 = 4204649) B4204649
theorem B4728431 : Blo 1659529 4728431 := bstep (se 1 (by rfl) ⟨3546323, by rfl⟩ : syracuseStep 4728431 = 7092647) B7092647
theorem B2492015 : Blo 1659529 2492015 := bstep (se 1 (by rfl) ⟨1869011, by rfl⟩ : syracuseStep 2492015 = 3738023) B3738023
theorem B5678707 : Blo 1659529 5678707 := bstep (se 1 (by rfl) ⟨4259030, by rfl⟩ : syracuseStep 5678707 = 8518061) B8518061
theorem B6481529 : Blo 1659529 6481529 := bstep (se 2 (by rfl) ⟨2430573, by rfl⟩ : syracuseStep 6481529 = 4861147) B4861147
theorem B2492087 : Blo 1659529 2492087 := bstep (se 1 (by rfl) ⟨1869065, by rfl⟩ : syracuseStep 2492087 = 3738131) B3738131
theorem B2492123 : Blo 1659529 2492123 := bstep (se 1 (by rfl) ⟨1869092, by rfl⟩ : syracuseStep 2492123 = 3738185) B3738185
theorem B7980767 : Blo 1659529 7980767 := bstep (se 1 (by rfl) ⟨5985575, by rfl⟩ : syracuseStep 7980767 = 11971151) B11971151
theorem B7096031 : Blo 1659529 7096031 := bstep (se 1 (by rfl) ⟨5322023, by rfl⟩ : syracuseStep 7096031 = 10644047) B10644047
theorem B2803423 : Blo 1659529 2803423 := bstep (se 1 (by rfl) ⟨2102567, by rfl⟩ : syracuseStep 2803423 = 4205135) B4205135
theorem B3737375 : Blo 1659529 3737375 := bstep (se 1 (by rfl) ⟨2803031, by rfl⟩ : syracuseStep 3737375 = 5606063) B5606063
theorem B14387005 : Blo 1659529 14387005 := bstep (se 3 (by rfl) ⟨2697563, by rfl⟩ : syracuseStep 14387005 = 5395127) B5395127
theorem B5605199 : Blo 1659529 5605199 := bstep (se 1 (by rfl) ⟨4203899, by rfl⟩ : syracuseStep 5605199 = 8407799) B8407799
theorem B4204487 : Blo 1659529 4204487 := bstep (se 1 (by rfl) ⟨3153365, by rfl⟩ : syracuseStep 4204487 = 6306731) B6306731
theorem B3737591 : Blo 1659529 3737591 := bstep (se 1 (by rfl) ⟨2803193, by rfl⟩ : syracuseStep 3737591 = 5606387) B5606387
theorem B5605523 : Blo 1659529 5605523 := bstep (se 1 (by rfl) ⟨4204142, by rfl⟩ : syracuseStep 5605523 = 8408285) B8408285
theorem B3737951 : Blo 1659529 3737951 := bstep (se 1 (by rfl) ⟨2803463, by rfl⟩ : syracuseStep 3737951 = 5606927) B5606927
theorem B5605793 : Blo 1659529 5605793 := bstep (se 2 (by rfl) ⟨2102172, by rfl⟩ : syracuseStep 5605793 = 4204345) B4204345
theorem B20474363 : Blo 1659529 20474363 := bstep (se 1 (by rfl) ⟨15355772, by rfl⟩ : syracuseStep 20474363 = 30711545) B30711545
theorem B35490449 : Blo 1659529 35490449 := bstep (se 2 (by rfl) ⟨13308918, by rfl⟩ : syracuseStep 35490449 = 26617837) B26617837
theorem B47893355 : Blo 1659529 47893355 := bstep (se 1 (by rfl) ⟨35920016, by rfl⟩ : syracuseStep 47893355 = 71840033) B71840033
theorem B18910259 : Blo 1659529 18910259 := bstep (se 1 (by rfl) ⟨14182694, by rfl⟩ : syracuseStep 18910259 = 28365389) B28365389
theorem B1772615 : Blo 1659529 1772615 := bstep (se 1 (by rfl) ⟨1329461, by rfl⟩ : syracuseStep 1772615 = 2658923) B2658923
theorem B20188379 : Blo 1659529 20188379 := bstep (se 1 (by rfl) ⟨15141284, by rfl⟩ : syracuseStep 20188379 = 30282569) B30282569
theorem B8088875 : Blo 1659529 8088875 := bstep (se 1 (by rfl) ⟨6066656, by rfl⟩ : syracuseStep 8088875 = 12133313) B12133313
theorem B7982459 : Blo 1659529 7982459 := bstep (se 1 (by rfl) ⟨5986844, by rfl⟩ : syracuseStep 7982459 = 11973689) B11973689
theorem B8408771 : Blo 1659529 8408771 := bstep (se 1 (by rfl) ⟨6306578, by rfl⟩ : syracuseStep 8408771 = 12613157) B12613157
theorem B23924483 : Blo 1659529 23924483 := bstep (se 1 (by rfl) ⟨17943362, by rfl⟩ : syracuseStep 23924483 = 35886725) B35886725
theorem B4730663 : Blo 1659529 4730663 := bstep (se 1 (by rfl) ⟨3547997, by rfl⟩ : syracuseStep 4730663 = 7095995) B7095995
theorem B10637203 : Blo 1659529 10637203 := bstep (se 1 (by rfl) ⟨7977902, by rfl⟩ : syracuseStep 10637203 = 15955805) B15955805
theorem B5320691 : Blo 1659529 5320691 := bstep (se 1 (by rfl) ⟨3990518, by rfl⟩ : syracuseStep 5320691 = 7981037) B7981037
theorem B6066361 : Blo 1659529 6066361 := bstep (se 2 (by rfl) ⟨2274885, by rfl⟩ : syracuseStep 6066361 = 4549771) B4549771
theorem B21557441 : Blo 1659529 21557441 := bstep (se 2 (by rfl) ⟨8084040, by rfl⟩ : syracuseStep 21557441 = 16168081) B16168081
theorem B4731347 : Blo 1659529 4731347 := bstep (se 1 (by rfl) ⟨3548510, by rfl⟩ : syracuseStep 4731347 = 7097021) B7097021
theorem B16167397 : Blo 1659529 16167397 := bstep (se 4 (by rfl) ⟨1515693, by rfl⟩ : syracuseStep 16167397 = 3031387) B3031387
theorem B8524403 : Blo 1659529 8524403 := bstep (se 1 (by rfl) ⟨6393302, by rfl⟩ : syracuseStep 8524403 = 12786605) B12786605
theorem B9098009 : Blo 1659529 9098009 := bstep (se 2 (by rfl) ⟨3411753, by rfl⟩ : syracuseStep 9098009 = 6823507) B6823507
theorem B5985085 : Blo 1659529 5985085 := bstep (se 3 (by rfl) ⟨1122203, by rfl⟩ : syracuseStep 5985085 = 2244407) B2244407
theorem B38327107 : Blo 1659529 38327107 := bstep (se 1 (by rfl) ⟨28745330, by rfl⟩ : syracuseStep 38327107 = 57490661) B57490661
theorem B1659759 : Blo 1659529 1659759 := bstep (se 1 (by rfl) ⟨1244819, by rfl⟩ : syracuseStep 1659759 = 2489639) B2489639
theorem B1659815 : Blo 1659529 1659815 := bstep (se 1 (by rfl) ⟨1244861, by rfl⟩ : syracuseStep 1659815 = 2489723) B2489723
theorem B1659899 : Blo 1659529 1659899 := bstep (se 1 (by rfl) ⟨1244924, by rfl⟩ : syracuseStep 1659899 = 2489849) B2489849
theorem B18191375 : Blo 1659529 18191375 := bstep (se 1 (by rfl) ⟨13643531, by rfl⟩ : syracuseStep 18191375 = 27287063) B27287063
theorem B1659967 : Blo 1659529 1659967 := bstep (se 1 (by rfl) ⟨1244975, by rfl⟩ : syracuseStep 1659967 = 2489951) B2489951
theorem B5321791 : Blo 1659529 5321791 := bstep (se 1 (by rfl) ⟨3991343, by rfl⟩ : syracuseStep 5321791 = 7982687) B7982687
theorem B1660111 : Blo 1659529 1660111 := bstep (se 1 (by rfl) ⟨1245083, by rfl⟩ : syracuseStep 1660111 = 2490167) B2490167
theorem B11965727 : Blo 1659529 11965727 := bstep (se 1 (by rfl) ⟨8974295, by rfl⟩ : syracuseStep 11965727 = 17948591) B17948591
theorem B31921451 : Blo 1659529 31921451 := bstep (se 1 (by rfl) ⟨23941088, by rfl⟩ : syracuseStep 31921451 = 47882177) B47882177
theorem B10098029 : Blo 1659529 10098029 := bstep (se 3 (by rfl) ⟨1893380, by rfl⟩ : syracuseStep 10098029 = 3786761) B3786761
theorem B1660315 : Blo 1659529 1660315 := bstep (se 1 (by rfl) ⟨1245236, by rfl⟩ : syracuseStep 1660315 = 2490473) B2490473
theorem B5985863 : Blo 1659529 5985863 := bstep (se 1 (by rfl) ⟨4489397, by rfl⟩ : syracuseStep 5985863 = 8978795) B8978795
theorem B1660527 : Blo 1659529 1660527 := bstep (se 1 (by rfl) ⟨1245395, by rfl⟩ : syracuseStep 1660527 = 2490791) B2490791
theorem B1660583 : Blo 1659529 1660583 := bstep (se 1 (by rfl) ⟨1245437, by rfl⟩ : syracuseStep 1660583 = 2490875) B2490875
theorem B8402615 : Blo 1659529 8402615 := bstep (se 1 (by rfl) ⟨6301961, by rfl⟩ : syracuseStep 8402615 = 12603923) B12603923
theorem B3151543 : Blo 1659529 3151543 := bstep (se 1 (by rfl) ⟨2363657, by rfl⟩ : syracuseStep 3151543 = 4727315) B4727315
theorem B1660667 : Blo 1659529 1660667 := bstep (se 1 (by rfl) ⟨1245500, by rfl⟩ : syracuseStep 1660667 = 2491001) B2491001
theorem B1660703 : Blo 1659529 1660703 := bstep (se 1 (by rfl) ⟨1245527, by rfl⟩ : syracuseStep 1660703 = 2491055) B2491055
theorem B7092031 : Blo 1659529 7092031 := bstep (se 1 (by rfl) ⟨5319023, by rfl⟩ : syracuseStep 7092031 = 10638047) B10638047
theorem B1660735 : Blo 1659529 1660735 := bstep (se 1 (by rfl) ⟨1245551, by rfl⟩ : syracuseStep 1660735 = 2491103) B2491103
theorem B3151847 : Blo 1659529 3151847 := bstep (se 1 (by rfl) ⟨2363885, by rfl⟩ : syracuseStep 3151847 = 4727771) B4727771
theorem B1660911 : Blo 1659529 1660911 := bstep (se 1 (by rfl) ⟨1245683, by rfl⟩ : syracuseStep 1660911 = 2491367) B2491367
theorem B22714433 : Blo 1659529 22714433 := bstep (se 2 (by rfl) ⟨8517912, by rfl⟩ : syracuseStep 22714433 = 17035825) B17035825
theorem B26941517 : Blo 1659529 26941517 := bstep (se 3 (by rfl) ⟨5051534, by rfl⟩ : syracuseStep 26941517 = 10103069) B10103069
theorem B3987539 : Blo 1659529 3987539 := bstep (se 1 (by rfl) ⟨2990654, by rfl⟩ : syracuseStep 3987539 = 5981309) B5981309
theorem B8976527 : Blo 1659529 8976527 := bstep (se 1 (by rfl) ⟨6732395, by rfl⟩ : syracuseStep 8976527 = 13464791) B13464791
theorem B1661083 : Blo 1659529 1661083 := bstep (se 1 (by rfl) ⟨1245812, by rfl⟩ : syracuseStep 1661083 = 2491625) B2491625
theorem B1661119 : Blo 1659529 1661119 := bstep (se 1 (by rfl) ⟨1245839, by rfl⟩ : syracuseStep 1661119 = 2491679) B2491679
theorem B3152105 : Blo 1659529 3152105 := bstep (se 2 (by rfl) ⟨1182039, by rfl⟩ : syracuseStep 3152105 = 2364079) B2364079
theorem B4258055 : Blo 1659529 4258055 := bstep (se 1 (by rfl) ⟨3193541, by rfl⟩ : syracuseStep 4258055 = 6387083) B6387083
theorem B3152135 : Blo 1659529 3152135 := bstep (se 1 (by rfl) ⟨2364101, by rfl⟩ : syracuseStep 3152135 = 4728203) B4728203
theorem B1661231 : Blo 1659529 1661231 := bstep (se 1 (by rfl) ⟨1245923, by rfl⟩ : syracuseStep 1661231 = 2491847) B2491847
theorem B9451849 : Blo 1659529 9451849 := bstep (se 2 (by rfl) ⟨3544443, by rfl⟩ : syracuseStep 9451849 = 7088887) B7088887
theorem B5683645 : Blo 1659529 5683645 := bstep (se 3 (by rfl) ⟨1065683, by rfl⟩ : syracuseStep 5683645 = 2131367) B2131367
theorem B2243099 : Blo 1659529 2243099 := bstep (se 1 (by rfl) ⟨1682324, by rfl⟩ : syracuseStep 2243099 = 3364649) B3364649
theorem B1661467 : Blo 1659529 1661467 := bstep (se 1 (by rfl) ⟨1246100, by rfl⟩ : syracuseStep 1661467 = 2492201) B2492201
theorem B1661471 : Blo 1659529 1661471 := bstep (se 1 (by rfl) ⟨1246103, by rfl⟩ : syracuseStep 1661471 = 2492207) B2492207
theorem B3734153 : Blo 1659529 3734153 := bstep (se 2 (by rfl) ⟨1400307, by rfl⟩ : syracuseStep 3734153 = 2800615) B2800615
theorem B6404761 : Blo 1659529 6404761 := bstep (se 2 (by rfl) ⟨2401785, by rfl⟩ : syracuseStep 6404761 = 4803571) B4803571
theorem B6306457 : Blo 1659529 6306457 := bstep (se 2 (by rfl) ⟨2364921, by rfl⟩ : syracuseStep 6306457 = 4729843) B4729843
theorem B3545947 : Blo 1659529 3545947 := bstep (se 1 (by rfl) ⟨2659460, by rfl⟩ : syracuseStep 3545947 = 5318921) B5318921
theorem B42580889 : Blo 1659529 42580889 := bstep (se 2 (by rfl) ⟨15967833, by rfl⟩ : syracuseStep 42580889 = 31935667) B31935667
theorem B2489465 : Blo 1659529 2489465 := bstep (se 2 (by rfl) ⟨933549, by rfl⟩ : syracuseStep 2489465 = 1867099) B1867099
theorem B4791421 : Blo 1659529 4791421 := bstep (se 3 (by rfl) ⟨898391, by rfl⟩ : syracuseStep 4791421 = 1796783) B1796783
theorem B3734711 : Blo 1659529 3734711 := bstep (se 1 (by rfl) ⟨2801033, by rfl⟩ : syracuseStep 3734711 = 5602067) B5602067
theorem B2489567 : Blo 1659529 2489567 := bstep (se 1 (by rfl) ⟨1867175, by rfl⟩ : syracuseStep 2489567 = 3734351) B3734351
theorem B5602553 : Blo 1659529 5602553 := bstep (se 2 (by rfl) ⟨2100957, by rfl⟩ : syracuseStep 5602553 = 4201915) B4201915
theorem B2489609 : Blo 1659529 2489609 := bstep (se 2 (by rfl) ⟨933603, by rfl⟩ : syracuseStep 2489609 = 1867207) B1867207
theorem B3153161 : Blo 1659529 3153161 := bstep (se 2 (by rfl) ⟨1182435, by rfl⟩ : syracuseStep 3153161 = 2364871) B2364871
theorem B2489711 : Blo 1659529 2489711 := bstep (se 1 (by rfl) ⟨1867283, by rfl⟩ : syracuseStep 2489711 = 3734567) B3734567
theorem B4201895 : Blo 1659529 4201895 := bstep (se 1 (by rfl) ⟨3151421, by rfl⟩ : syracuseStep 4201895 = 6302843) B6302843
theorem B2489831 : Blo 1659529 2489831 := bstep (se 1 (by rfl) ⟨1867373, by rfl⟩ : syracuseStep 2489831 = 3734747) B3734747
theorem B5602823 : Blo 1659529 5602823 := bstep (se 1 (by rfl) ⟨4202117, by rfl⟩ : syracuseStep 5602823 = 8404235) B8404235
theorem B2801243 : Blo 1659529 2801243 := bstep (se 1 (by rfl) ⟨2100932, by rfl⟩ : syracuseStep 2801243 = 4201865) B4201865
theorem B2489963 : Blo 1659529 2489963 := bstep (se 1 (by rfl) ⟨1867472, by rfl⟩ : syracuseStep 2489963 = 3734945) B3734945
theorem B2490089 : Blo 1659529 2490089 := bstep (se 2 (by rfl) ⟨933783, by rfl⟩ : syracuseStep 2490089 = 1867567) B1867567
theorem B3735287 : Blo 1659529 3735287 := bstep (se 1 (by rfl) ⟨2801465, by rfl⟩ : syracuseStep 3735287 = 5602931) B5602931
theorem B2801479 : Blo 1659529 2801479 := bstep (se 1 (by rfl) ⟨2101109, by rfl⟩ : syracuseStep 2801479 = 4202219) B4202219
theorem B2490233 : Blo 1659529 2490233 := bstep (se 2 (by rfl) ⟨933837, by rfl⟩ : syracuseStep 2490233 = 1867675) B1867675
theorem B3735467 : Blo 1659529 3735467 := bstep (se 1 (by rfl) ⟨2801600, by rfl⟩ : syracuseStep 3735467 = 5603201) B5603201
theorem B6733739 : Blo 1659529 6733739 := bstep (se 1 (by rfl) ⟨5050304, by rfl⟩ : syracuseStep 6733739 = 10100609) B10100609
theorem B2490335 : Blo 1659529 2490335 := bstep (se 1 (by rfl) ⟨1867751, by rfl⟩ : syracuseStep 2490335 = 3735503) B3735503
theorem B4726973 : Blo 1659529 4726973 := bstep (se 3 (by rfl) ⟨886307, by rfl⟩ : syracuseStep 4726973 = 1772615) B1772615
theorem B2490671 : Blo 1659529 2490671 := bstep (se 1 (by rfl) ⟨1868003, by rfl⟩ : syracuseStep 2490671 = 3736007) B3736007
theorem B3154231 : Blo 1659529 3154231 := bstep (se 1 (by rfl) ⟨2365673, by rfl⟩ : syracuseStep 3154231 = 4731347) B4731347
theorem B3735935 : Blo 1659529 3735935 := bstep (se 1 (by rfl) ⟨2801951, by rfl⟩ : syracuseStep 3735935 = 5603903) B5603903
theorem B2490911 : Blo 1659529 2490911 := bstep (se 1 (by rfl) ⟨1868183, by rfl⟩ : syracuseStep 2490911 = 3736367) B3736367
theorem B7578193 : Blo 1659529 7578193 := bstep (se 2 (by rfl) ⟨2841822, by rfl⟩ : syracuseStep 7578193 = 5683645) B5683645
theorem B3736169 : Blo 1659529 3736169 := bstep (se 2 (by rfl) ⟨1401063, by rfl⟩ : syracuseStep 3736169 = 2802127) B2802127
theorem B11354813 : Blo 1659529 11354813 := bstep (se 3 (by rfl) ⟨2129027, by rfl⟩ : syracuseStep 11354813 = 4258055) B4258055
theorem B8405693 : Blo 1659529 8405693 := bstep (se 3 (by rfl) ⟨1576067, by rfl⟩ : syracuseStep 8405693 = 3152135) B3152135
theorem B1868575 : Blo 1659529 1868575 := bstep (se 1 (by rfl) ⟨1401431, by rfl⟩ : syracuseStep 1868575 = 2802863) B2802863
theorem B7095107 : Blo 1659529 7095107 := bstep (se 1 (by rfl) ⟨5321330, by rfl⟩ : syracuseStep 7095107 = 10642661) B10642661
theorem B21267481 : Blo 1659529 21267481 := bstep (se 2 (by rfl) ⟨7975305, by rfl⟩ : syracuseStep 21267481 = 15950611) B15950611
theorem B3990575 : Blo 1659529 3990575 := bstep (se 1 (by rfl) ⟨2992931, by rfl⟩ : syracuseStep 3990575 = 5985863) B5985863
theorem B7980113 : Blo 1659529 7980113 := bstep (se 2 (by rfl) ⟨2992542, by rfl⟩ : syracuseStep 7980113 = 5985085) B5985085
theorem B51102809 : Blo 1659529 51102809 := bstep (se 2 (by rfl) ⟨19163553, by rfl⟩ : syracuseStep 51102809 = 38327107) B38327107
theorem B2491583 : Blo 1659529 2491583 := bstep (se 1 (by rfl) ⟨1868687, by rfl⟩ : syracuseStep 2491583 = 3737375) B3737375
theorem B3736799 : Blo 1659529 3736799 := bstep (se 1 (by rfl) ⟨2802599, by rfl⟩ : syracuseStep 3736799 = 5605199) B5605199
theorem B2802991 : Blo 1659529 2802991 := bstep (se 1 (by rfl) ⟨2102243, by rfl⟩ : syracuseStep 2802991 = 4204487) B4204487
theorem B2491727 : Blo 1659529 2491727 := bstep (se 1 (by rfl) ⟨1868795, by rfl⟩ : syracuseStep 2491727 = 3737591) B3737591
theorem B5981597 : Blo 1659529 5981597 := bstep (se 3 (by rfl) ⟨1121549, by rfl⟩ : syracuseStep 5981597 = 2243099) B2243099
theorem B2491817 : Blo 1659529 2491817 := bstep (se 2 (by rfl) ⟨934431, by rfl⟩ : syracuseStep 2491817 = 1868863) B1868863
theorem B3737015 : Blo 1659529 3737015 := bstep (se 1 (by rfl) ⟨2802761, by rfl⟩ : syracuseStep 3737015 = 5605523) B5605523
theorem B2491967 : Blo 1659529 2491967 := bstep (se 1 (by rfl) ⟨1868975, by rfl⟩ : syracuseStep 2491967 = 3737951) B3737951
theorem B2492009 : Blo 1659529 2492009 := bstep (se 2 (by rfl) ⟨934503, by rfl⟩ : syracuseStep 2492009 = 1869007) B1869007
theorem B3737195 : Blo 1659529 3737195 := bstep (se 1 (by rfl) ⟨2802896, by rfl⟩ : syracuseStep 3737195 = 5605793) B5605793
theorem B13649575 : Blo 1659529 13649575 := bstep (se 1 (by rfl) ⟨10237181, by rfl⟩ : syracuseStep 13649575 = 20474363) B20474363
theorem B23660299 : Blo 1659529 23660299 := bstep (se 1 (by rfl) ⟨17745224, by rfl⟩ : syracuseStep 23660299 = 35490449) B35490449
theorem B3737465 : Blo 1659529 3737465 := bstep (se 2 (by rfl) ⟨1401549, by rfl⟩ : syracuseStep 3737465 = 2803099) B2803099
theorem B28387259 : Blo 1659529 28387259 := bstep (se 1 (by rfl) ⟨21290444, by rfl⟩ : syracuseStep 28387259 = 42580889) B42580889
theorem B7571609 : Blo 1659529 7571609 := bstep (se 2 (by rfl) ⟨2839353, by rfl⟩ : syracuseStep 7571609 = 5678707) B5678707
theorem B5392583 : Blo 1659529 5392583 := bstep (se 1 (by rfl) ⟨4044437, by rfl⟩ : syracuseStep 5392583 = 8088875) B8088875
theorem B3737897 : Blo 1659529 3737897 := bstep (se 2 (by rfl) ⟨1401711, by rfl⟩ : syracuseStep 3737897 = 2803423) B2803423
theorem B9456041 : Blo 1659529 9456041 := bstep (se 2 (by rfl) ⟨3546015, by rfl⟩ : syracuseStep 9456041 = 7092031) B7092031
theorem B5605847 : Blo 1659529 5605847 := bstep (se 1 (by rfl) ⟨4204385, by rfl⟩ : syracuseStep 5605847 = 8408771) B8408771
theorem B14182937 : Blo 1659529 14182937 := bstep (se 2 (by rfl) ⟨5318601, by rfl⟩ : syracuseStep 14182937 = 10637203) B10637203
theorem B14371627 : Blo 1659529 14371627 := bstep (se 1 (by rfl) ⟨10778720, by rfl⟩ : syracuseStep 14371627 = 21557441) B21557441
theorem B8088481 : Blo 1659529 8088481 := bstep (se 2 (by rfl) ⟨3033180, by rfl⟩ : syracuseStep 8088481 = 6066361) B6066361
theorem B12602465 : Blo 1659529 12602465 := bstep (se 2 (by rfl) ⟨4725924, by rfl⟩ : syracuseStep 12602465 = 9451849) B9451849
theorem B6065339 : Blo 1659529 6065339 := bstep (se 1 (by rfl) ⟨4549004, by rfl⟩ : syracuseStep 6065339 = 9098009) B9098009
theorem B21556529 : Blo 1659529 21556529 := bstep (se 2 (by rfl) ⟨8083698, by rfl⟩ : syracuseStep 21556529 = 16167397) B16167397
theorem B6303055 : Blo 1659529 6303055 := bstep (se 1 (by rfl) ⟨4727291, by rfl⟩ : syracuseStep 6303055 = 9454583) B9454583
theorem B12127583 : Blo 1659529 12127583 := bstep (se 1 (by rfl) ⟨9095687, by rfl⟩ : syracuseStep 12127583 = 18191375) B18191375
theorem B8539681 : Blo 1659529 8539681 := bstep (se 2 (by rfl) ⟨3202380, by rfl⟩ : syracuseStep 8539681 = 6404761) B6404761
theorem B8408609 : Blo 1659529 8408609 := bstep (se 2 (by rfl) ⟨3153228, by rfl⟩ : syracuseStep 8408609 = 6306457) B6306457
theorem B4321019 : Blo 1659529 4321019 := bstep (se 1 (by rfl) ⟨3240764, by rfl⟩ : syracuseStep 4321019 = 6481529) B6481529
theorem B5320511 : Blo 1659529 5320511 := bstep (se 1 (by rfl) ⟨3990383, by rfl⟩ : syracuseStep 5320511 = 7980767) B7980767
theorem B4730687 : Blo 1659529 4730687 := bstep (se 1 (by rfl) ⟨3548015, by rfl⟩ : syracuseStep 4730687 = 7096031) B7096031
theorem B2101231 : Blo 1659529 2101231 := bstep (se 1 (by rfl) ⟨1575923, by rfl⟩ : syracuseStep 2101231 = 3151847) B3151847
theorem B15142955 : Blo 1659529 15142955 := bstep (se 1 (by rfl) ⟨11357216, by rfl⟩ : syracuseStep 15142955 = 22714433) B22714433
theorem B17961011 : Blo 1659529 17961011 := bstep (se 1 (by rfl) ⟨13470758, by rfl⟩ : syracuseStep 17961011 = 26941517) B26941517
theorem B2658359 : Blo 1659529 2658359 := bstep (se 1 (by rfl) ⟨1993769, by rfl⟩ : syracuseStep 2658359 = 3987539) B3987539
theorem B5984351 : Blo 1659529 5984351 := bstep (se 1 (by rfl) ⟨4488263, by rfl⟩ : syracuseStep 5984351 = 8976527) B8976527
theorem B2101403 : Blo 1659529 2101403 := bstep (se 1 (by rfl) ⟨1576052, by rfl⟩ : syracuseStep 2101403 = 3152105) B3152105
theorem B3547127 : Blo 1659529 3547127 := bstep (se 1 (by rfl) ⟨2660345, by rfl⟩ : syracuseStep 3547127 = 5320691) B5320691
theorem B18911717 : Blo 1659529 18911717 := bstep (se 4 (by rfl) ⟨1772973, by rfl⟩ : syracuseStep 18911717 = 3545947) B3545947
theorem B31928903 : Blo 1659529 31928903 := bstep (se 1 (by rfl) ⟨23946677, by rfl⟩ : syracuseStep 31928903 = 47893355) B47893355
theorem B95777477 : Blo 1659529 95777477 := bstep (se 4 (by rfl) ⟨8979138, by rfl⟩ : syracuseStep 95777477 = 17958277) B17958277
theorem B1659643 : Blo 1659529 1659643 := bstep (se 1 (by rfl) ⟨1244732, by rfl⟩ : syracuseStep 1659643 = 2489465) B2489465
theorem B1659711 : Blo 1659529 1659711 := bstep (se 1 (by rfl) ⟨1244783, by rfl⟩ : syracuseStep 1659711 = 2489567) B2489567
theorem B1659739 : Blo 1659529 1659739 := bstep (se 1 (by rfl) ⟨1244804, by rfl⟩ : syracuseStep 1659739 = 2489609) B2489609
theorem B2102107 : Blo 1659529 2102107 := bstep (se 1 (by rfl) ⟨1576580, by rfl⟩ : syracuseStep 2102107 = 3153161) B3153161
theorem B1659807 : Blo 1659529 1659807 := bstep (se 1 (by rfl) ⟨1244855, by rfl⟩ : syracuseStep 1659807 = 2489711) B2489711
theorem B5321639 : Blo 1659529 5321639 := bstep (se 1 (by rfl) ⟨3991229, by rfl⟩ : syracuseStep 5321639 = 7982459) B7982459
theorem B1659887 : Blo 1659529 1659887 := bstep (se 1 (by rfl) ⟨1244915, by rfl⟩ : syracuseStep 1659887 = 2489831) B2489831
theorem B1659975 : Blo 1659529 1659975 := bstep (se 1 (by rfl) ⟨1244981, by rfl⟩ : syracuseStep 1659975 = 2489963) B2489963
theorem B19182673 : Blo 1659529 19182673 := bstep (se 2 (by rfl) ⟨7193502, by rfl⟩ : syracuseStep 19182673 = 14387005) B14387005
theorem B1660059 : Blo 1659529 1660059 := bstep (se 1 (by rfl) ⟨1245044, by rfl⟩ : syracuseStep 1660059 = 2490089) B2490089
theorem B1660155 : Blo 1659529 1660155 := bstep (se 1 (by rfl) ⟨1245116, by rfl⟩ : syracuseStep 1660155 = 2490233) B2490233
theorem B1660223 : Blo 1659529 1660223 := bstep (se 1 (by rfl) ⟨1245167, by rfl⟩ : syracuseStep 1660223 = 2490335) B2490335
theorem B1660391 : Blo 1659529 1660391 := bstep (se 1 (by rfl) ⟨1245293, by rfl⟩ : syracuseStep 1660391 = 2490587) B2490587
theorem B1660399 : Blo 1659529 1660399 := bstep (se 1 (by rfl) ⟨1245299, by rfl⟩ : syracuseStep 1660399 = 2490599) B2490599
theorem B1660507 : Blo 1659529 1660507 := bstep (se 1 (by rfl) ⟨1245380, by rfl⟩ : syracuseStep 1660507 = 2490761) B2490761
theorem B1660571 : Blo 1659529 1660571 := bstep (se 1 (by rfl) ⟨1245428, by rfl⟩ : syracuseStep 1660571 = 2490857) B2490857
theorem B15963803 : Blo 1659529 15963803 := bstep (se 1 (by rfl) ⟨11972852, by rfl⟩ : syracuseStep 15963803 = 23945705) B23945705
theorem B28382885 : Blo 1659529 28382885 := bstep (se 4 (by rfl) ⟨2660895, by rfl⟩ : syracuseStep 28382885 = 5321791) B5321791
theorem B1660655 : Blo 1659529 1660655 := bstep (se 1 (by rfl) ⟨1245491, by rfl⟩ : syracuseStep 1660655 = 2490983) B2490983
theorem B5682935 : Blo 1659529 5682935 := bstep (se 1 (by rfl) ⟨4262201, by rfl⟩ : syracuseStep 5682935 = 8524403) B8524403
theorem B1660743 : Blo 1659529 1660743 := bstep (se 1 (by rfl) ⟨1245557, by rfl⟩ : syracuseStep 1660743 = 2491115) B2491115
theorem B1660763 : Blo 1659529 1660763 := bstep (se 1 (by rfl) ⟨1245572, by rfl⟩ : syracuseStep 1660763 = 2491145) B2491145
theorem B1660831 : Blo 1659529 1660831 := bstep (se 1 (by rfl) ⟨1245623, by rfl⟩ : syracuseStep 1660831 = 2491247) B2491247
theorem B1660999 : Blo 1659529 1660999 := bstep (se 1 (by rfl) ⟨1245749, by rfl⟩ : syracuseStep 1660999 = 2491499) B2491499
theorem B7977151 : Blo 1659529 7977151 := bstep (se 1 (by rfl) ⟨5982863, by rfl⟩ : syracuseStep 7977151 = 11965727) B11965727
theorem B21280967 : Blo 1659529 21280967 := bstep (se 1 (by rfl) ⟨15960725, by rfl⟩ : syracuseStep 21280967 = 31921451) B31921451
theorem B1661159 : Blo 1659529 1661159 := bstep (se 1 (by rfl) ⟨1245869, by rfl⟩ : syracuseStep 1661159 = 2491739) B2491739
theorem B6732019 : Blo 1659529 6732019 := bstep (se 1 (by rfl) ⟨5049014, by rfl⟩ : syracuseStep 6732019 = 10098029) B10098029
theorem B14178563 : Blo 1659529 14178563 := bstep (se 1 (by rfl) ⟨10633922, by rfl⟩ : syracuseStep 14178563 = 21267845) B21267845
theorem B3152287 : Blo 1659529 3152287 := bstep (se 1 (by rfl) ⟨2364215, by rfl⟩ : syracuseStep 3152287 = 4728431) B4728431
theorem B1661343 : Blo 1659529 1661343 := bstep (se 1 (by rfl) ⟨1246007, by rfl⟩ : syracuseStep 1661343 = 2492015) B2492015
theorem B5601743 : Blo 1659529 5601743 := bstep (se 1 (by rfl) ⟨4201307, by rfl⟩ : syracuseStep 5601743 = 8402615) B8402615
theorem B1661391 : Blo 1659529 1661391 := bstep (se 1 (by rfl) ⟨1246043, by rfl⟩ : syracuseStep 1661391 = 2492087) B2492087
theorem B1661415 : Blo 1659529 1661415 := bstep (se 1 (by rfl) ⟨1246061, by rfl⟩ : syracuseStep 1661415 = 2492123) B2492123
theorem B6388561 : Blo 1659529 6388561 := bstep (se 2 (by rfl) ⟨2395710, by rfl⟩ : syracuseStep 6388561 = 4791421) B4791421
theorem B2489435 : Blo 1659529 2489435 := bstep (se 1 (by rfl) ⟨1867076, by rfl⟩ : syracuseStep 2489435 = 3734153) B3734153
theorem B12606839 : Blo 1659529 12606839 := bstep (se 1 (by rfl) ⟨9455129, by rfl⟩ : syracuseStep 12606839 = 18910259) B18910259
theorem B12615101 : Blo 1659529 12615101 := bstep (se 3 (by rfl) ⟨2365331, by rfl⟩ : syracuseStep 12615101 = 4730663) B4730663
theorem B2489807 : Blo 1659529 2489807 := bstep (se 1 (by rfl) ⟨1867355, by rfl⟩ : syracuseStep 2489807 = 3734711) B3734711
theorem B13458919 : Blo 1659529 13458919 := bstep (se 1 (by rfl) ⟨10094189, by rfl⟩ : syracuseStep 13458919 = 20188379) B20188379
theorem B3735035 : Blo 1659529 3735035 := bstep (se 1 (by rfl) ⟨2801276, by rfl⟩ : syracuseStep 3735035 = 5602553) B5602553
theorem B4202057 : Blo 1659529 4202057 := bstep (se 2 (by rfl) ⟨1575771, by rfl⟩ : syracuseStep 4202057 = 3151543) B3151543
theorem B2801263 : Blo 1659529 2801263 := bstep (se 1 (by rfl) ⟨2100947, by rfl⟩ : syracuseStep 2801263 = 4201895) B4201895
theorem B3735215 : Blo 1659529 3735215 := bstep (se 1 (by rfl) ⟨2801411, by rfl⟩ : syracuseStep 3735215 = 5602823) B5602823
theorem B1867495 : Blo 1659529 1867495 := bstep (se 1 (by rfl) ⟨1400621, by rfl⟩ : syracuseStep 1867495 = 2801243) B2801243
theorem B3735305 : Blo 1659529 3735305 := bstep (se 2 (by rfl) ⟨1400739, by rfl⟩ : syracuseStep 3735305 = 2801479) B2801479
theorem B17956637 : Blo 1659529 17956637 := bstep (se 3 (by rfl) ⟨3366869, by rfl⟩ : syracuseStep 17956637 = 6733739) B6733739
theorem B2490191 : Blo 1659529 2490191 := bstep (se 1 (by rfl) ⟨1867643, by rfl⟩ : syracuseStep 2490191 = 3735287) B3735287
theorem B15949655 : Blo 1659529 15949655 := bstep (se 1 (by rfl) ⟨11962241, by rfl⟩ : syracuseStep 15949655 = 23924483) B23924483
theorem B2490311 : Blo 1659529 2490311 := bstep (se 1 (by rfl) ⟨1867733, by rfl⟩ : syracuseStep 2490311 = 3735467) B3735467
theorem B3989567 : Blo 1659529 3989567 := bstep (se 1 (by rfl) ⟨2992175, by rfl⟩ : syracuseStep 3989567 = 5984351) B5984351
theorem B2490623 : Blo 1659529 2490623 := bstep (se 1 (by rfl) ⟨1867967, by rfl⟩ : syracuseStep 2490623 = 3735935) B3735935
theorem B12607811 : Blo 1659529 12607811 := bstep (se 1 (by rfl) ⟨9455858, by rfl⟩ : syracuseStep 12607811 = 18911717) B18911717
theorem B2490779 : Blo 1659529 2490779 := bstep (se 1 (by rfl) ⟨1868084, by rfl⟩ : syracuseStep 2490779 = 3736169) B3736169
theorem B5603741 : Blo 1659529 5603741 := bstep (se 3 (by rfl) ⟨1050701, by rfl⟩ : syracuseStep 5603741 = 2101403) B2101403
theorem B7569875 : Blo 1659529 7569875 := bstep (se 1 (by rfl) ⟨5677406, by rfl⟩ : syracuseStep 7569875 = 11354813) B11354813
theorem B5603795 : Blo 1659529 5603795 := bstep (se 1 (by rfl) ⟨4202846, by rfl⟩ : syracuseStep 5603795 = 8405693) B8405693
theorem B4203049 : Blo 1659529 4203049 := bstep (se 2 (by rfl) ⟨1576143, by rfl⟩ : syracuseStep 4203049 = 3152287) B3152287
theorem B3547759 : Blo 1659529 3547759 := bstep (se 1 (by rfl) ⟨2660819, by rfl⟩ : syracuseStep 3547759 = 5321639) B5321639
theorem B2491199 : Blo 1659529 2491199 := bstep (se 1 (by rfl) ⟨1868399, by rfl⟩ : syracuseStep 2491199 = 3736799) B3736799
theorem B2491343 : Blo 1659529 2491343 := bstep (se 1 (by rfl) ⟨1868507, by rfl⟩ : syracuseStep 2491343 = 3737015) B3737015
theorem B2491433 : Blo 1659529 2491433 := bstep (se 2 (by rfl) ⟨934287, by rfl⟩ : syracuseStep 2491433 = 1868575) B1868575
theorem B19162169 : Blo 1659529 19162169 := bstep (se 2 (by rfl) ⟨7185813, by rfl⟩ : syracuseStep 19162169 = 14371627) B14371627
theorem B2491463 : Blo 1659529 2491463 := bstep (se 1 (by rfl) ⟨1868597, by rfl⟩ : syracuseStep 2491463 = 3737195) B3737195
theorem B10642535 : Blo 1659529 10642535 := bstep (se 1 (by rfl) ⟨7981901, by rfl⟩ : syracuseStep 10642535 = 15963803) B15963803
theorem B2802809 : Blo 1659529 2802809 := bstep (se 2 (by rfl) ⟨1051053, by rfl⟩ : syracuseStep 2802809 = 2102107) B2102107
theorem B2491643 : Blo 1659529 2491643 := bstep (se 1 (by rfl) ⟨1868732, by rfl⟩ : syracuseStep 2491643 = 3737465) B3737465
theorem B18924839 : Blo 1659529 18924839 := bstep (se 1 (by rfl) ⟨14193629, by rfl⟩ : syracuseStep 18924839 = 28387259) B28387259
theorem B5047739 : Blo 1659529 5047739 := bstep (se 1 (by rfl) ⟨3785804, by rfl⟩ : syracuseStep 5047739 = 7571609) B7571609
theorem B25576897 : Blo 1659529 25576897 := bstep (se 2 (by rfl) ⟨9591336, by rfl⟩ : syracuseStep 25576897 = 19182673) B19182673
theorem B2491931 : Blo 1659529 2491931 := bstep (se 1 (by rfl) ⟨1868948, by rfl⟩ : syracuseStep 2491931 = 3737897) B3737897
theorem B3737231 : Blo 1659529 3737231 := bstep (se 1 (by rfl) ⟨2802923, by rfl⟩ : syracuseStep 3737231 = 5605847) B5605847
theorem B9455291 : Blo 1659529 9455291 := bstep (se 1 (by rfl) ⟨7091468, by rfl⟩ : syracuseStep 9455291 = 14182937) B14182937
theorem B3737321 : Blo 1659529 3737321 := bstep (se 2 (by rfl) ⟨1401495, by rfl⟩ : syracuseStep 3737321 = 2802991) B2802991
theorem B14371019 : Blo 1659529 14371019 := bstep (se 1 (by rfl) ⟨10778264, by rfl⟩ : syracuseStep 14371019 = 21556529) B21556529
theorem B5605739 : Blo 1659529 5605739 := bstep (se 1 (by rfl) ⟨4204304, by rfl⟩ : syracuseStep 5605739 = 8408609) B8408609
theorem B11971091 : Blo 1659529 11971091 := bstep (se 1 (by rfl) ⟨8978318, by rfl⟩ : syracuseStep 11971091 = 17956637) B17956637
theorem B40381213 : Blo 1659529 40381213 := bstep (se 3 (by rfl) ⟨7571477, by rfl⟩ : syracuseStep 40381213 = 15142955) B15142955
theorem B7088957 : Blo 1659529 7088957 := bstep (se 3 (by rfl) ⟨1329179, by rfl⟩ : syracuseStep 7088957 = 2658359) B2658359
theorem B10636201 : Blo 1659529 10636201 := bstep (se 2 (by rfl) ⟨3988575, by rfl⟩ : syracuseStep 10636201 = 7977151) B7977151
theorem B21285935 : Blo 1659529 21285935 := bstep (se 1 (by rfl) ⟨15964451, by rfl⟩ : syracuseStep 21285935 = 31928903) B31928903
theorem B4205641 : Blo 1659529 4205641 := bstep (se 2 (by rfl) ⟨1577115, by rfl⟩ : syracuseStep 4205641 = 3154231) B3154231
theorem B63851651 : Blo 1659529 63851651 := bstep (se 1 (by rfl) ⟨47888738, by rfl⟩ : syracuseStep 63851651 = 95777477) B95777477
theorem B16174237 : Blo 1659529 16174237 := bstep (se 3 (by rfl) ⟨3032669, by rfl⟩ : syracuseStep 16174237 = 6065339) B6065339
theorem B4730071 : Blo 1659529 4730071 := bstep (se 1 (by rfl) ⟨3547553, by rfl⟩ : syracuseStep 4730071 = 7095107) B7095107
theorem B5320075 : Blo 1659529 5320075 := bstep (se 1 (by rfl) ⟨3990056, by rfl⟩ : syracuseStep 5320075 = 7980113) B7980113
theorem B10104257 : Blo 1659529 10104257 := bstep (se 2 (by rfl) ⟨3789096, by rfl⟩ : syracuseStep 10104257 = 7578193) B7578193
theorem B3788623 : Blo 1659529 3788623 := bstep (se 1 (by rfl) ⟨2841467, by rfl⟩ : syracuseStep 3788623 = 5682935) B5682935
theorem B28356641 : Blo 1659529 28356641 := bstep (se 2 (by rfl) ⟨10633740, by rfl⟩ : syracuseStep 28356641 = 21267481) B21267481
theorem B6304027 : Blo 1659529 6304027 := bstep (se 1 (by rfl) ⟨4728020, by rfl⟩ : syracuseStep 6304027 = 9456041) B9456041
theorem B17945225 : Blo 1659529 17945225 := bstep (se 2 (by rfl) ⟨6729459, by rfl⟩ : syracuseStep 17945225 = 13458919) B13458919
theorem B1659623 : Blo 1659529 1659623 := bstep (se 1 (by rfl) ⟨1244717, by rfl⟩ : syracuseStep 1659623 = 2489435) B2489435
theorem B8401643 : Blo 1659529 8401643 := bstep (se 1 (by rfl) ⟨6301232, by rfl⟩ : syracuseStep 8401643 = 12602465) B12602465
theorem B18199433 : Blo 1659529 18199433 := bstep (se 2 (by rfl) ⟨6824787, by rfl⟩ : syracuseStep 18199433 = 13649575) B13649575
theorem B8410067 : Blo 1659529 8410067 := bstep (se 1 (by rfl) ⟨6307550, by rfl⟩ : syracuseStep 8410067 = 12615101) B12615101
theorem B1659871 : Blo 1659529 1659871 := bstep (se 1 (by rfl) ⟨1244903, by rfl⟩ : syracuseStep 1659871 = 2489807) B2489807
theorem B2880679 : Blo 1659529 2880679 := bstep (se 1 (by rfl) ⟨2160509, by rfl⟩ : syracuseStep 2880679 = 4321019) B4321019
theorem B1660127 : Blo 1659529 1660127 := bstep (se 1 (by rfl) ⟨1245095, by rfl⟩ : syracuseStep 1660127 = 2490191) B2490191
theorem B1660207 : Blo 1659529 1660207 := bstep (se 1 (by rfl) ⟨1245155, by rfl⟩ : syracuseStep 1660207 = 2490311) B2490311
theorem B2364751 : Blo 1659529 2364751 := bstep (se 1 (by rfl) ⟨1773563, by rfl⟩ : syracuseStep 2364751 = 3547127) B3547127
theorem B11974007 : Blo 1659529 11974007 := bstep (se 1 (by rfl) ⟨8980505, by rfl⟩ : syracuseStep 11974007 = 17961011) B17961011
theorem B3151315 : Blo 1659529 3151315 := bstep (se 1 (by rfl) ⟨2363486, by rfl⟩ : syracuseStep 3151315 = 4726973) B4726973
theorem B1660447 : Blo 1659529 1660447 := bstep (se 1 (by rfl) ⟨1245335, by rfl⟩ : syracuseStep 1660447 = 2490671) B2490671
theorem B8976025 : Blo 1659529 8976025 := bstep (se 2 (by rfl) ⟨3366009, by rfl⟩ : syracuseStep 8976025 = 6732019) B6732019
theorem B1660607 : Blo 1659529 1660607 := bstep (se 1 (by rfl) ⟨1245455, by rfl⟩ : syracuseStep 1660607 = 2490911) B2490911
theorem B2660383 : Blo 1659529 2660383 := bstep (se 1 (by rfl) ⟨1995287, by rfl⟩ : syracuseStep 2660383 = 3990575) B3990575
theorem B34068539 : Blo 1659529 34068539 := bstep (se 1 (by rfl) ⟨25551404, by rfl⟩ : syracuseStep 34068539 = 51102809) B51102809
theorem B1661055 : Blo 1659529 1661055 := bstep (se 1 (by rfl) ⟨1245791, by rfl⟩ : syracuseStep 1661055 = 2491583) B2491583
theorem B1661151 : Blo 1659529 1661151 := bstep (se 1 (by rfl) ⟨1245863, by rfl⟩ : syracuseStep 1661151 = 2491727) B2491727
theorem B3987731 : Blo 1659529 3987731 := bstep (se 1 (by rfl) ⟨2990798, by rfl⟩ : syracuseStep 3987731 = 5981597) B5981597
theorem B1661211 : Blo 1659529 1661211 := bstep (se 1 (by rfl) ⟨1245908, by rfl⟩ : syracuseStep 1661211 = 2491817) B2491817
theorem B1661311 : Blo 1659529 1661311 := bstep (se 1 (by rfl) ⟨1245983, by rfl⟩ : syracuseStep 1661311 = 2491967) B2491967
theorem B1661339 : Blo 1659529 1661339 := bstep (se 1 (by rfl) ⟨1246004, by rfl⟩ : syracuseStep 1661339 = 2492009) B2492009
theorem B8518081 : Blo 1659529 8518081 := bstep (se 2 (by rfl) ⟨3194280, by rfl⟩ : syracuseStep 8518081 = 6388561) B6388561
theorem B18921923 : Blo 1659529 18921923 := bstep (se 1 (by rfl) ⟨14191442, by rfl⟩ : syracuseStep 18921923 = 28382885) B28382885
theorem B3595055 : Blo 1659529 3595055 := bstep (se 1 (by rfl) ⟨2696291, by rfl⟩ : syracuseStep 3595055 = 5392583) B5392583
theorem B14187311 : Blo 1659529 14187311 := bstep (se 1 (by rfl) ⟨10640483, by rfl⟩ : syracuseStep 14187311 = 21280967) B21280967
theorem B9452375 : Blo 1659529 9452375 := bstep (se 1 (by rfl) ⟨7089281, by rfl⟩ : syracuseStep 9452375 = 14178563) B14178563
theorem B3734495 : Blo 1659529 3734495 := bstep (se 1 (by rfl) ⟨2800871, by rfl⟩ : syracuseStep 3734495 = 5601743) B5601743
theorem B8404073 : Blo 1659529 8404073 := bstep (se 2 (by rfl) ⟨3151527, by rfl⟩ : syracuseStep 8404073 = 6303055) B6303055
theorem B11386241 : Blo 1659529 11386241 := bstep (se 2 (by rfl) ⟨4269840, by rfl⟩ : syracuseStep 11386241 = 8539681) B8539681
theorem B3735017 : Blo 1659529 3735017 := bstep (se 2 (by rfl) ⟨1400631, by rfl⟩ : syracuseStep 3735017 = 2801263) B2801263
theorem B43138565 : Blo 1659529 43138565 := bstep (se 4 (by rfl) ⟨4044240, by rfl⟩ : syracuseStep 43138565 = 8088481) B8088481
theorem B8085055 : Blo 1659529 8085055 := bstep (se 1 (by rfl) ⟨6063791, by rfl⟩ : syracuseStep 8085055 = 12127583) B12127583
theorem B8404559 : Blo 1659529 8404559 := bstep (se 1 (by rfl) ⟨6303419, by rfl⟩ : syracuseStep 8404559 = 12606839) B12606839
theorem B2489993 : Blo 1659529 2489993 := bstep (se 2 (by rfl) ⟨933747, by rfl⟩ : syracuseStep 2489993 = 1867495) B1867495
theorem B2490023 : Blo 1659529 2490023 := bstep (se 1 (by rfl) ⟨1867517, by rfl⟩ : syracuseStep 2490023 = 3735035) B3735035
theorem B31547065 : Blo 1659529 31547065 := bstep (se 2 (by rfl) ⟨11830149, by rfl⟩ : syracuseStep 31547065 = 23660299) B23660299
theorem B2801371 : Blo 1659529 2801371 := bstep (se 1 (by rfl) ⟨2101028, by rfl⟩ : syracuseStep 2801371 = 4202057) B4202057
theorem B2490143 : Blo 1659529 2490143 := bstep (se 1 (by rfl) ⟨1867607, by rfl⟩ : syracuseStep 2490143 = 3735215) B3735215
theorem B2490203 : Blo 1659529 2490203 := bstep (se 1 (by rfl) ⟨1867652, by rfl⟩ : syracuseStep 2490203 = 3735305) B3735305
theorem B3547007 : Blo 1659529 3547007 := bstep (se 1 (by rfl) ⟨2660255, by rfl⟩ : syracuseStep 3547007 = 5320511) B5320511
theorem B3153791 : Blo 1659529 3153791 := bstep (se 1 (by rfl) ⟨2365343, by rfl⟩ : syracuseStep 3153791 = 4730687) B4730687
theorem B10633103 : Blo 1659529 10633103 := bstep (se 1 (by rfl) ⟨7974827, by rfl⟩ : syracuseStep 10633103 = 15949655) B15949655
theorem B2801641 : Blo 1659529 2801641 := bstep (se 2 (by rfl) ⟨1050615, by rfl⟩ : syracuseStep 2801641 = 2101231) B2101231
theorem B14188709 : Blo 1659529 14188709 := bstep (se 4 (by rfl) ⟨1330191, by rfl⟩ : syracuseStep 14188709 = 2660383) B2660383
theorem B8405207 : Blo 1659529 8405207 := bstep (se 1 (by rfl) ⟨6303905, by rfl⟩ : syracuseStep 8405207 = 12607811) B12607811
theorem B3735827 : Blo 1659529 3735827 := bstep (se 1 (by rfl) ⟨2801870, by rfl⟩ : syracuseStep 3735827 = 5603741) B5603741
theorem B5046583 : Blo 1659529 5046583 := bstep (se 1 (by rfl) ⟨3784937, by rfl⟩ : syracuseStep 5046583 = 7569875) B7569875
theorem B3735863 : Blo 1659529 3735863 := bstep (se 1 (by rfl) ⟨2801897, by rfl⟩ : syracuseStep 3735863 = 5603795) B5603795
theorem B8405369 : Blo 1659529 8405369 := bstep (se 2 (by rfl) ⟨3152013, by rfl⟩ : syracuseStep 8405369 = 6304027) B6304027
theorem B38347253 : Blo 1659529 38347253 := bstep (se 5 (by rfl) ⟨1797527, by rfl⟩ : syracuseStep 38347253 = 3595055) B3595055
theorem B12132955 : Blo 1659529 12132955 := bstep (se 1 (by rfl) ⟨9099716, by rfl⟩ : syracuseStep 12132955 = 18199433) B18199433
theorem B5604065 : Blo 1659529 5604065 := bstep (se 2 (by rfl) ⟨2101524, by rfl⟩ : syracuseStep 5604065 = 4203049) B4203049
theorem B7095023 : Blo 1659529 7095023 := bstep (se 1 (by rfl) ⟨5321267, by rfl⟩ : syracuseStep 7095023 = 10642535) B10642535
theorem B1868539 : Blo 1659529 1868539 := bstep (se 1 (by rfl) ⟨1401404, by rfl⟩ : syracuseStep 1868539 = 2802809) B2802809
theorem B12616559 : Blo 1659529 12616559 := bstep (se 1 (by rfl) ⟨9462419, by rfl⟩ : syracuseStep 12616559 = 18924839) B18924839
theorem B2491487 : Blo 1659529 2491487 := bstep (se 1 (by rfl) ⟨1868615, by rfl⟩ : syracuseStep 2491487 = 3737231) B3737231
theorem B2491547 : Blo 1659529 2491547 := bstep (se 1 (by rfl) ⟨1868660, by rfl⟩ : syracuseStep 2491547 = 3737321) B3737321
theorem B14181601 : Blo 1659529 14181601 := bstep (se 2 (by rfl) ⟨5318100, by rfl⟩ : syracuseStep 14181601 = 10636201) B10636201
theorem B3737159 : Blo 1659529 3737159 := bstep (se 1 (by rfl) ⟨2802869, by rfl⟩ : syracuseStep 3737159 = 5605739) B5605739
theorem B6301583 : Blo 1659529 6301583 := bstep (se 1 (by rfl) ⟨4726187, by rfl⟩ : syracuseStep 6301583 = 9452375) B9452375
theorem B14190623 : Blo 1659529 14190623 := bstep (se 1 (by rfl) ⟨10642967, by rfl⟩ : syracuseStep 14190623 = 21285935) B21285935
theorem B42567767 : Blo 1659529 42567767 := bstep (se 1 (by rfl) ⟨31925825, by rfl⟩ : syracuseStep 42567767 = 63851651) B63851651
theorem B6736171 : Blo 1659529 6736171 := bstep (se 1 (by rfl) ⟨5052128, by rfl⟩ : syracuseStep 6736171 = 10104257) B10104257
theorem B7088735 : Blo 1659529 7088735 := bstep (se 1 (by rfl) ⟨5316551, by rfl⟩ : syracuseStep 7088735 = 10633103) B10633103
theorem B11963483 : Blo 1659529 11963483 := bstep (se 1 (by rfl) ⟨8972612, by rfl⟩ : syracuseStep 11963483 = 17945225) B17945225
theorem B11357441 : Blo 1659529 11357441 := bstep (se 2 (by rfl) ⟨4259040, by rfl⟩ : syracuseStep 11357441 = 8518081) B8518081
theorem B5606711 : Blo 1659529 5606711 := bstep (se 1 (by rfl) ⟨4205033, by rfl⟩ : syracuseStep 5606711 = 8410067) B8410067
theorem B12774779 : Blo 1659529 12774779 := bstep (se 1 (by rfl) ⟨9581084, by rfl⟩ : syracuseStep 12774779 = 19162169) B19162169
theorem B4730345 : Blo 1659529 4730345 := bstep (se 2 (by rfl) ⟨1773879, by rfl⟩ : syracuseStep 4730345 = 3547759) B3547759
theorem B7982671 : Blo 1659529 7982671 := bstep (se 1 (by rfl) ⟨5987003, by rfl⟩ : syracuseStep 7982671 = 11974007) B11974007
theorem B53841617 : Blo 1659529 53841617 := bstep (se 2 (by rfl) ⟨20190606, by rfl⟩ : syracuseStep 53841617 = 40381213) B40381213
theorem B6303527 : Blo 1659529 6303527 := bstep (se 1 (by rfl) ⟨4727645, by rfl⟩ : syracuseStep 6303527 = 9455291) B9455291
theorem B22712359 : Blo 1659529 22712359 := bstep (se 1 (by rfl) ⟨17034269, by rfl⟩ : syracuseStep 22712359 = 34068539) B34068539
theorem B5607521 : Blo 1659529 5607521 := bstep (se 2 (by rfl) ⟨2102820, by rfl⟩ : syracuseStep 5607521 = 4205641) B4205641
theorem B9580679 : Blo 1659529 9580679 := bstep (se 1 (by rfl) ⟨7185509, by rfl⟩ : syracuseStep 9580679 = 14371019) B14371019
theorem B2658487 : Blo 1659529 2658487 := bstep (se 1 (by rfl) ⟨1993865, by rfl⟩ : syracuseStep 2658487 = 3987731) B3987731
theorem B21565649 : Blo 1659529 21565649 := bstep (se 2 (by rfl) ⟨8087118, by rfl⟩ : syracuseStep 21565649 = 16174237) B16174237
theorem B9458207 : Blo 1659529 9458207 := bstep (se 1 (by rfl) ⟨7093655, by rfl⟩ : syracuseStep 9458207 = 14187311) B14187311
theorem B42062753 : Blo 1659529 42062753 := bstep (se 2 (by rfl) ⟨15773532, by rfl⟩ : syracuseStep 42062753 = 31547065) B31547065
theorem B7590827 : Blo 1659529 7590827 := bstep (se 1 (by rfl) ⟨5693120, by rfl⟩ : syracuseStep 7590827 = 11386241) B11386241
theorem B28759043 : Blo 1659529 28759043 := bstep (se 1 (by rfl) ⟨21569282, by rfl⟩ : syracuseStep 28759043 = 43138565) B43138565
theorem B1659995 : Blo 1659529 1659995 := bstep (se 1 (by rfl) ⟨1244996, by rfl⟩ : syracuseStep 1659995 = 2489993) B2489993
theorem B5051497 : Blo 1659529 5051497 := bstep (se 2 (by rfl) ⟨1894311, by rfl⟩ : syracuseStep 5051497 = 3788623) B3788623
theorem B1660015 : Blo 1659529 1660015 := bstep (se 1 (by rfl) ⟨1245011, by rfl⟩ : syracuseStep 1660015 = 2490023) B2490023
theorem B1660095 : Blo 1659529 1660095 := bstep (se 1 (by rfl) ⟨1245071, by rfl⟩ : syracuseStep 1660095 = 2490143) B2490143
theorem B1660135 : Blo 1659529 1660135 := bstep (se 1 (by rfl) ⟨1245101, by rfl⟩ : syracuseStep 1660135 = 2490203) B2490203
theorem B2364671 : Blo 1659529 2364671 := bstep (se 1 (by rfl) ⟨1773503, by rfl⟩ : syracuseStep 2364671 = 3547007) B3547007
theorem B2102527 : Blo 1659529 2102527 := bstep (se 1 (by rfl) ⟨1576895, by rfl⟩ : syracuseStep 2102527 = 3153791) B3153791
theorem B18904427 : Blo 1659529 18904427 := bstep (se 1 (by rfl) ⟨14178320, by rfl⟩ : syracuseStep 18904427 = 28356641) B28356641
theorem B2659711 : Blo 1659529 2659711 := bstep (se 1 (by rfl) ⟨1994783, by rfl⟩ : syracuseStep 2659711 = 3989567) B3989567
theorem B1660415 : Blo 1659529 1660415 := bstep (se 1 (by rfl) ⟨1245311, by rfl⟩ : syracuseStep 1660415 = 2490623) B2490623
theorem B1660519 : Blo 1659529 1660519 := bstep (se 1 (by rfl) ⟨1245389, by rfl⟩ : syracuseStep 1660519 = 2490779) B2490779
theorem B5601095 : Blo 1659529 5601095 := bstep (se 1 (by rfl) ⟨4200821, by rfl⟩ : syracuseStep 5601095 = 8401643) B8401643
theorem B1660799 : Blo 1659529 1660799 := bstep (se 1 (by rfl) ⟨1245599, by rfl⟩ : syracuseStep 1660799 = 2491199) B2491199
theorem B1660895 : Blo 1659529 1660895 := bstep (se 1 (by rfl) ⟨1245671, by rfl⟩ : syracuseStep 1660895 = 2491343) B2491343
theorem B1660955 : Blo 1659529 1660955 := bstep (se 1 (by rfl) ⟨1245716, by rfl⟩ : syracuseStep 1660955 = 2491433) B2491433
theorem B1660975 : Blo 1659529 1660975 := bstep (se 1 (by rfl) ⟨1245731, by rfl⟩ : syracuseStep 1660975 = 2491463) B2491463
theorem B47872133 : Blo 1659529 47872133 := bstep (se 4 (by rfl) ⟨4488012, by rfl⟩ : syracuseStep 47872133 = 8976025) B8976025
theorem B1661095 : Blo 1659529 1661095 := bstep (se 1 (by rfl) ⟨1245821, by rfl⟩ : syracuseStep 1661095 = 2491643) B2491643
theorem B3365159 : Blo 1659529 3365159 := bstep (se 1 (by rfl) ⟨2523869, by rfl⟩ : syracuseStep 3365159 = 5047739) B5047739
theorem B1661287 : Blo 1659529 1661287 := bstep (se 1 (by rfl) ⟨1245965, by rfl⟩ : syracuseStep 1661287 = 2491931) B2491931
theorem B31922909 : Blo 1659529 31922909 := bstep (se 3 (by rfl) ⟨5985545, by rfl⟩ : syracuseStep 31922909 = 11971091) B11971091
theorem B3840905 : Blo 1659529 3840905 := bstep (se 2 (by rfl) ⟨1440339, by rfl⟩ : syracuseStep 3840905 = 2880679) B2880679
theorem B6306761 : Blo 1659529 6306761 := bstep (se 2 (by rfl) ⟨2365035, by rfl⟩ : syracuseStep 6306761 = 4730071) B4730071
theorem B12614615 : Blo 1659529 12614615 := bstep (se 1 (by rfl) ⟨9460961, by rfl⟩ : syracuseStep 12614615 = 18921923) B18921923
theorem B3153001 : Blo 1659529 3153001 := bstep (se 2 (by rfl) ⟨1182375, by rfl⟩ : syracuseStep 3153001 = 2364751) B2364751
theorem B7093433 : Blo 1659529 7093433 := bstep (se 2 (by rfl) ⟨2660037, by rfl⟩ : syracuseStep 7093433 = 5320075) B5320075
theorem B4725971 : Blo 1659529 4725971 := bstep (se 1 (by rfl) ⟨3544478, by rfl⟩ : syracuseStep 4725971 = 7088957) B7088957
theorem B34102529 : Blo 1659529 34102529 := bstep (se 2 (by rfl) ⟨12788448, by rfl⟩ : syracuseStep 34102529 = 25576897) B25576897
theorem B4201753 : Blo 1659529 4201753 := bstep (se 2 (by rfl) ⟨1575657, by rfl⟩ : syracuseStep 4201753 = 3151315) B3151315
theorem B2489663 : Blo 1659529 2489663 := bstep (se 1 (by rfl) ⟨1867247, by rfl⟩ : syracuseStep 2489663 = 3734495) B3734495
theorem B5602715 : Blo 1659529 5602715 := bstep (se 1 (by rfl) ⟨4202036, by rfl⟩ : syracuseStep 5602715 = 8404073) B8404073
theorem B10780073 : Blo 1659529 10780073 := bstep (se 2 (by rfl) ⟨4042527, by rfl⟩ : syracuseStep 10780073 = 8085055) B8085055
theorem B3735161 : Blo 1659529 3735161 := bstep (se 2 (by rfl) ⟨1400685, by rfl⟩ : syracuseStep 3735161 = 2801371) B2801371
theorem B2490011 : Blo 1659529 2490011 := bstep (se 1 (by rfl) ⟨1867508, by rfl⟩ : syracuseStep 2490011 = 3735017) B3735017
theorem B5603039 : Blo 1659529 5603039 := bstep (se 1 (by rfl) ⟨4202279, by rfl⟩ : syracuseStep 5603039 = 8404559) B8404559
theorem B3735521 : Blo 1659529 3735521 := bstep (se 2 (by rfl) ⟨1400820, by rfl⟩ : syracuseStep 3735521 = 2801641) B2801641
theorem B14377099 : Blo 1659529 14377099 := bstep (se 1 (by rfl) ⟨10782824, by rfl⟩ : syracuseStep 14377099 = 21565649) B21565649
theorem B5603471 : Blo 1659529 5603471 := bstep (se 1 (by rfl) ⟨4202603, by rfl⟩ : syracuseStep 5603471 = 8405207) B8405207
theorem B2490551 : Blo 1659529 2490551 := bstep (se 1 (by rfl) ⟨1867913, by rfl⟩ : syracuseStep 2490551 = 3735827) B3735827
theorem B2490575 : Blo 1659529 2490575 := bstep (se 1 (by rfl) ⟨1867931, by rfl⟩ : syracuseStep 2490575 = 3735863) B3735863
theorem B5603579 : Blo 1659529 5603579 := bstep (se 1 (by rfl) ⟨4202684, by rfl⟩ : syracuseStep 5603579 = 8405369) B8405369
theorem B64709093 : Blo 1659529 64709093 := bstep (se 4 (by rfl) ⟨6066477, by rfl⟩ : syracuseStep 64709093 = 12132955) B12132955
theorem B3736043 : Blo 1659529 3736043 := bstep (se 1 (by rfl) ⟨2802032, by rfl⟩ : syracuseStep 3736043 = 5604065) B5604065
theorem B28041835 : Blo 1659529 28041835 := bstep (se 1 (by rfl) ⟨21031376, by rfl⟩ : syracuseStep 28041835 = 42062753) B42062753
theorem B2491385 : Blo 1659529 2491385 := bstep (se 2 (by rfl) ⟨934269, by rfl⟩ : syracuseStep 2491385 = 1868539) B1868539
theorem B2491439 : Blo 1659529 2491439 := bstep (se 1 (by rfl) ⟨1868579, by rfl⟩ : syracuseStep 2491439 = 3737159) B3737159
theorem B28378511 : Blo 1659529 28378511 := bstep (se 1 (by rfl) ⟨21283883, by rfl⟩ : syracuseStep 28378511 = 42567767) B42567767
theorem B4204001 : Blo 1659529 4204001 := bstep (se 2 (by rfl) ⟨1576500, by rfl⟩ : syracuseStep 4204001 = 3153001) B3153001
theorem B6735329 : Blo 1659529 6735329 := bstep (se 2 (by rfl) ⟨2525748, by rfl⟩ : syracuseStep 6735329 = 5051497) B5051497
theorem B18908801 : Blo 1659529 18908801 := bstep (se 2 (by rfl) ⟨7090800, by rfl⟩ : syracuseStep 18908801 = 14181601) B14181601
theorem B2803369 : Blo 1659529 2803369 := bstep (se 2 (by rfl) ⟨1051263, by rfl⟩ : syracuseStep 2803369 = 2102527) B2102527
theorem B4204507 : Blo 1659529 4204507 := bstep (se 1 (by rfl) ⟨3153380, by rfl⟩ : syracuseStep 4204507 = 6306761) B6306761
theorem B10643561 : Blo 1659529 10643561 := bstep (se 2 (by rfl) ⟨3991335, by rfl⟩ : syracuseStep 10643561 = 7982671) B7982671
theorem B4728955 : Blo 1659529 4728955 := bstep (se 1 (by rfl) ⟨3546716, by rfl⟩ : syracuseStep 4728955 = 7093433) B7093433
theorem B7571627 : Blo 1659529 7571627 := bstep (se 1 (by rfl) ⟨5678720, by rfl⟩ : syracuseStep 7571627 = 11357441) B11357441
theorem B22735019 : Blo 1659529 22735019 := bstep (se 1 (by rfl) ⟨17051264, by rfl⟩ : syracuseStep 22735019 = 34102529) B34102529
theorem B3737807 : Blo 1659529 3737807 := bstep (se 1 (by rfl) ⟨2803355, by rfl⟩ : syracuseStep 3737807 = 5606711) B5606711
theorem B7186715 : Blo 1659529 7186715 := bstep (se 1 (by rfl) ⟨5390036, by rfl⟩ : syracuseStep 7186715 = 10780073) B10780073
theorem B10242413 : Blo 1659529 10242413 := bstep (se 3 (by rfl) ⟨1920452, by rfl⟩ : syracuseStep 10242413 = 3840905) B3840905
theorem B3738347 : Blo 1659529 3738347 := bstep (se 1 (by rfl) ⟨2803760, by rfl⟩ : syracuseStep 3738347 = 5607521) B5607521
theorem B8981561 : Blo 1659529 8981561 := bstep (se 2 (by rfl) ⟨3368085, by rfl⟩ : syracuseStep 8981561 = 6736171) B6736171
theorem B6728777 : Blo 1659529 6728777 := bstep (se 2 (by rfl) ⟨2523291, by rfl⟩ : syracuseStep 6728777 = 5046583) B5046583
theorem B4730015 : Blo 1659529 4730015 := bstep (se 1 (by rfl) ⟨3547511, by rfl⟩ : syracuseStep 4730015 = 7095023) B7095023
theorem B19172695 : Blo 1659529 19172695 := bstep (se 1 (by rfl) ⟨14379521, by rfl⟩ : syracuseStep 19172695 = 28759043) B28759043
theorem B8973757 : Blo 1659529 8973757 := bstep (se 3 (by rfl) ⟨1682579, by rfl⟩ : syracuseStep 8973757 = 3365159) B3365159
theorem B12602951 : Blo 1659529 12602951 := bstep (se 1 (by rfl) ⟨9452213, by rfl⟩ : syracuseStep 12602951 = 18904427) B18904427
theorem B8409743 : Blo 1659529 8409743 := bstep (se 1 (by rfl) ⟨6307307, by rfl⟩ : syracuseStep 8409743 = 12614615) B12614615
theorem B7975655 : Blo 1659529 7975655 := bstep (se 1 (by rfl) ⟨5981741, by rfl⟩ : syracuseStep 7975655 = 11963483) B11963483
theorem B3150647 : Blo 1659529 3150647 := bstep (se 1 (by rfl) ⟨2362985, by rfl⟩ : syracuseStep 3150647 = 4725971) B4725971
theorem B1659775 : Blo 1659529 1659775 := bstep (se 1 (by rfl) ⟨1244831, by rfl⟩ : syracuseStep 1659775 = 2489663) B2489663
theorem B8516519 : Blo 1659529 8516519 := bstep (se 1 (by rfl) ⟨6387389, by rfl⟩ : syracuseStep 8516519 = 12774779) B12774779
theorem B1660007 : Blo 1659529 1660007 := bstep (se 1 (by rfl) ⟨1245005, by rfl⟩ : syracuseStep 1660007 = 2490011) B2490011
theorem B35894411 : Blo 1659529 35894411 := bstep (se 1 (by rfl) ⟨26920808, by rfl⟩ : syracuseStep 35894411 = 53841617) B53841617
theorem B30283145 : Blo 1659529 30283145 := bstep (se 2 (by rfl) ⟨11356179, by rfl⟩ : syracuseStep 30283145 = 22712359) B22712359
theorem B6387119 : Blo 1659529 6387119 := bstep (se 1 (by rfl) ⟨4790339, by rfl⟩ : syracuseStep 6387119 = 9580679) B9580679
theorem B9459139 : Blo 1659529 9459139 := bstep (se 1 (by rfl) ⟨7094354, by rfl⟩ : syracuseStep 9459139 = 14188709) B14188709
theorem B3544649 : Blo 1659529 3544649 := bstep (se 2 (by rfl) ⟨1329243, by rfl⟩ : syracuseStep 3544649 = 2658487) B2658487
theorem B25564835 : Blo 1659529 25564835 := bstep (se 1 (by rfl) ⟨19173626, by rfl⟩ : syracuseStep 25564835 = 38347253) B38347253
theorem B6305471 : Blo 1659529 6305471 := bstep (se 1 (by rfl) ⟨4729103, by rfl⟩ : syracuseStep 6305471 = 9458207) B9458207
theorem B8411039 : Blo 1659529 8411039 := bstep (se 1 (by rfl) ⟨6308279, by rfl⟩ : syracuseStep 8411039 = 12616559) B12616559
theorem B5060551 : Blo 1659529 5060551 := bstep (se 1 (by rfl) ⟨3795413, by rfl⟩ : syracuseStep 5060551 = 7590827) B7590827
theorem B6305789 : Blo 1659529 6305789 := bstep (se 3 (by rfl) ⟨1182335, by rfl⟩ : syracuseStep 6305789 = 2364671) B2364671
theorem B1660991 : Blo 1659529 1660991 := bstep (se 1 (by rfl) ⟨1245743, by rfl⟩ : syracuseStep 1660991 = 2491487) B2491487
theorem B1661031 : Blo 1659529 1661031 := bstep (se 1 (by rfl) ⟨1245773, by rfl⟩ : syracuseStep 1661031 = 2491547) B2491547
theorem B3734063 : Blo 1659529 3734063 := bstep (se 1 (by rfl) ⟨2800547, by rfl⟩ : syracuseStep 3734063 = 5601095) B5601095
theorem B4201055 : Blo 1659529 4201055 := bstep (se 1 (by rfl) ⟨3150791, by rfl⟩ : syracuseStep 4201055 = 6301583) B6301583
theorem B9460415 : Blo 1659529 9460415 := bstep (se 1 (by rfl) ⟨7095311, by rfl⟩ : syracuseStep 9460415 = 14190623) B14190623
theorem B31914755 : Blo 1659529 31914755 := bstep (se 1 (by rfl) ⟨23936066, by rfl⟩ : syracuseStep 31914755 = 47872133) B47872133
theorem B5602337 : Blo 1659529 5602337 := bstep (se 2 (by rfl) ⟨2100876, by rfl⟩ : syracuseStep 5602337 = 4201753) B4201753
theorem B4725823 : Blo 1659529 4725823 := bstep (se 1 (by rfl) ⟨3544367, by rfl⟩ : syracuseStep 4725823 = 7088735) B7088735
theorem B21281939 : Blo 1659529 21281939 := bstep (se 1 (by rfl) ⟨15961454, by rfl⟩ : syracuseStep 21281939 = 31922909) B31922909
theorem B3546281 : Blo 1659529 3546281 := bstep (se 2 (by rfl) ⟨1329855, by rfl⟩ : syracuseStep 3546281 = 2659711) B2659711
theorem B3735143 : Blo 1659529 3735143 := bstep (se 1 (by rfl) ⟨2801357, by rfl⟩ : syracuseStep 3735143 = 5602715) B5602715
theorem B3153563 : Blo 1659529 3153563 := bstep (se 1 (by rfl) ⟨2365172, by rfl⟩ : syracuseStep 3153563 = 4730345) B4730345
theorem B2490107 : Blo 1659529 2490107 := bstep (se 1 (by rfl) ⟨1867580, by rfl⟩ : syracuseStep 2490107 = 3735161) B3735161
theorem B3735359 : Blo 1659529 3735359 := bstep (se 1 (by rfl) ⟨2801519, by rfl⟩ : syracuseStep 3735359 = 5603039) B5603039
theorem B4202351 : Blo 1659529 4202351 := bstep (se 1 (by rfl) ⟨3151763, by rfl⟩ : syracuseStep 4202351 = 6303527) B6303527
theorem B2490347 : Blo 1659529 2490347 := bstep (se 1 (by rfl) ⟨1867760, by rfl⟩ : syracuseStep 2490347 = 3735521) B3735521
theorem B3735647 : Blo 1659529 3735647 := bstep (se 1 (by rfl) ⟨2801735, by rfl⟩ : syracuseStep 3735647 = 5603471) B5603471
theorem B3735719 : Blo 1659529 3735719 := bstep (se 1 (by rfl) ⟨2801789, by rfl⟩ : syracuseStep 3735719 = 5603579) B5603579
theorem B19169465 : Blo 1659529 19169465 := bstep (se 2 (by rfl) ⟨7188549, by rfl⟩ : syracuseStep 19169465 = 14377099) B14377099
theorem B43139395 : Blo 1659529 43139395 := bstep (se 1 (by rfl) ⟨32354546, by rfl⟩ : syracuseStep 43139395 = 64709093) B64709093
theorem B2490695 : Blo 1659529 2490695 := bstep (se 1 (by rfl) ⟨1868021, by rfl⟩ : syracuseStep 2490695 = 3736043) B3736043
theorem B5317103 : Blo 1659529 5317103 := bstep (se 1 (by rfl) ⟨3987827, by rfl⟩ : syracuseStep 5317103 = 7975655) B7975655
theorem B5677679 : Blo 1659529 5677679 := bstep (se 1 (by rfl) ⟨4258259, by rfl⟩ : syracuseStep 5677679 = 8516519) B8516519
theorem B23929607 : Blo 1659529 23929607 := bstep (se 1 (by rfl) ⟨17947205, by rfl⟩ : syracuseStep 23929607 = 35894411) B35894411
theorem B37389113 : Blo 1659529 37389113 := bstep (se 2 (by rfl) ⟨14020917, by rfl⟩ : syracuseStep 37389113 = 28041835) B28041835
theorem B2802667 : Blo 1659529 2802667 := bstep (se 1 (by rfl) ⟨2102000, by rfl⟩ : syracuseStep 2802667 = 4204001) B4204001
theorem B4490219 : Blo 1659529 4490219 := bstep (se 1 (by rfl) ⟨3367664, by rfl⟩ : syracuseStep 4490219 = 6735329) B6735329
theorem B4203647 : Blo 1659529 4203647 := bstep (se 1 (by rfl) ⟨3152735, by rfl⟩ : syracuseStep 4203647 = 6305471) B6305471
theorem B4203859 : Blo 1659529 4203859 := bstep (se 1 (by rfl) ⟨3152894, by rfl⟩ : syracuseStep 4203859 = 6305789) B6305789
theorem B7095707 : Blo 1659529 7095707 := bstep (se 1 (by rfl) ⟨5321780, by rfl⟩ : syracuseStep 7095707 = 10643561) B10643561
theorem B6301097 : Blo 1659529 6301097 := bstep (se 2 (by rfl) ⟨2362911, by rfl⟩ : syracuseStep 6301097 = 4725823) B4725823
theorem B5047751 : Blo 1659529 5047751 := bstep (se 1 (by rfl) ⟨3785813, by rfl⟩ : syracuseStep 5047751 = 7571627) B7571627
theorem B2491871 : Blo 1659529 2491871 := bstep (se 1 (by rfl) ⟨1868903, by rfl⟩ : syracuseStep 2491871 = 3737807) B3737807
theorem B2492231 : Blo 1659529 2492231 := bstep (se 1 (by rfl) ⟨1869173, by rfl⟩ : syracuseStep 2492231 = 3738347) B3738347
theorem B21276503 : Blo 1659529 21276503 := bstep (se 1 (by rfl) ⟨15957377, by rfl⟩ : syracuseStep 21276503 = 31914755) B31914755
theorem B3737825 : Blo 1659529 3737825 := bstep (se 2 (by rfl) ⟨1401684, by rfl⟩ : syracuseStep 3737825 = 2803369) B2803369
theorem B5606009 : Blo 1659529 5606009 := bstep (se 2 (by rfl) ⟨2102253, by rfl⟩ : syracuseStep 5606009 = 4204507) B4204507
theorem B5606495 : Blo 1659529 5606495 := bstep (se 1 (by rfl) ⟨4204871, by rfl⟩ : syracuseStep 5606495 = 8409743) B8409743
theorem B9456749 : Blo 1659529 9456749 := bstep (se 3 (by rfl) ⟨1773140, by rfl⟩ : syracuseStep 9456749 = 3546281) B3546281
theorem B2100431 : Blo 1659529 2100431 := bstep (se 1 (by rfl) ⟨1575323, by rfl⟩ : syracuseStep 2100431 = 3150647) B3150647
theorem B20188763 : Blo 1659529 20188763 := bstep (se 1 (by rfl) ⟨15141572, by rfl⟩ : syracuseStep 20188763 = 30283145) B30283145
theorem B18919007 : Blo 1659529 18919007 := bstep (se 1 (by rfl) ⟨14189255, by rfl⟩ : syracuseStep 18919007 = 28378511) B28378511
theorem B2363099 : Blo 1659529 2363099 := bstep (se 1 (by rfl) ⟨1772324, by rfl⟩ : syracuseStep 2363099 = 3544649) B3544649
theorem B17043223 : Blo 1659529 17043223 := bstep (se 1 (by rfl) ⟨12782417, by rfl⟩ : syracuseStep 17043223 = 25564835) B25564835
theorem B5607359 : Blo 1659529 5607359 := bstep (se 1 (by rfl) ⟨4205519, by rfl⟩ : syracuseStep 5607359 = 8411039) B8411039
theorem B6828275 : Blo 1659529 6828275 := bstep (se 1 (by rfl) ⟨5121206, by rfl⟩ : syracuseStep 6828275 = 10242413) B10242413
theorem B25563593 : Blo 1659529 25563593 := bstep (se 2 (by rfl) ⟨9586347, by rfl⟩ : syracuseStep 25563593 = 19172695) B19172695
theorem B11965009 : Blo 1659529 11965009 := bstep (se 2 (by rfl) ⟨4486878, by rfl⟩ : syracuseStep 11965009 = 8973757) B8973757
theorem B12612185 : Blo 1659529 12612185 := bstep (se 2 (by rfl) ⟨4729569, by rfl⟩ : syracuseStep 12612185 = 9459139) B9459139
theorem B4485851 : Blo 1659529 4485851 := bstep (se 1 (by rfl) ⟨3364388, by rfl⟩ : syracuseStep 4485851 = 6728777) B6728777
theorem B8401967 : Blo 1659529 8401967 := bstep (se 1 (by rfl) ⟨6301475, by rfl⟩ : syracuseStep 8401967 = 12602951) B12602951
theorem B2102375 : Blo 1659529 2102375 := bstep (se 1 (by rfl) ⟨1576781, by rfl⟩ : syracuseStep 2102375 = 3153563) B3153563
theorem B1660071 : Blo 1659529 1660071 := bstep (se 1 (by rfl) ⟨1245053, by rfl⟩ : syracuseStep 1660071 = 2490107) B2490107
theorem B6747401 : Blo 1659529 6747401 := bstep (se 2 (by rfl) ⟨2530275, by rfl⟩ : syracuseStep 6747401 = 5060551) B5060551
theorem B1660231 : Blo 1659529 1660231 := bstep (se 1 (by rfl) ⟨1245173, by rfl⟩ : syracuseStep 1660231 = 2490347) B2490347
theorem B1660367 : Blo 1659529 1660367 := bstep (se 1 (by rfl) ⟨1245275, by rfl⟩ : syracuseStep 1660367 = 2490551) B2490551
theorem B1660383 : Blo 1659529 1660383 := bstep (se 1 (by rfl) ⟨1245287, by rfl⟩ : syracuseStep 1660383 = 2490575) B2490575
theorem B23950829 : Blo 1659529 23950829 := bstep (se 3 (by rfl) ⟨4490780, by rfl⟩ : syracuseStep 23950829 = 8981561) B8981561
theorem B6305273 : Blo 1659529 6305273 := bstep (se 2 (by rfl) ⟨2364477, by rfl⟩ : syracuseStep 6305273 = 4728955) B4728955
theorem B60626717 : Blo 1659529 60626717 := bstep (se 3 (by rfl) ⟨11367509, by rfl⟩ : syracuseStep 60626717 = 22735019) B22735019
theorem B1660923 : Blo 1659529 1660923 := bstep (se 1 (by rfl) ⟨1245692, by rfl⟩ : syracuseStep 1660923 = 2491385) B2491385
theorem B1660959 : Blo 1659529 1660959 := bstep (se 1 (by rfl) ⟨1245719, by rfl⟩ : syracuseStep 1660959 = 2491439) B2491439
theorem B4258079 : Blo 1659529 4258079 := bstep (se 1 (by rfl) ⟨3193559, by rfl⟩ : syracuseStep 4258079 = 6387119) B6387119
theorem B12605867 : Blo 1659529 12605867 := bstep (se 1 (by rfl) ⟨9454400, by rfl⟩ : syracuseStep 12605867 = 18908801) B18908801
theorem B4791143 : Blo 1659529 4791143 := bstep (se 1 (by rfl) ⟨3593357, by rfl⟩ : syracuseStep 4791143 = 7186715) B7186715
theorem B2489375 : Blo 1659529 2489375 := bstep (se 1 (by rfl) ⟨1867031, by rfl⟩ : syracuseStep 2489375 = 3734063) B3734063
theorem B2800703 : Blo 1659529 2800703 := bstep (se 1 (by rfl) ⟨2100527, by rfl⟩ : syracuseStep 2800703 = 4201055) B4201055
theorem B6306943 : Blo 1659529 6306943 := bstep (se 1 (by rfl) ⟨4730207, by rfl⟩ : syracuseStep 6306943 = 9460415) B9460415
theorem B3734891 : Blo 1659529 3734891 := bstep (se 1 (by rfl) ⟨2801168, by rfl⟩ : syracuseStep 3734891 = 5602337) B5602337
theorem B14187959 : Blo 1659529 14187959 := bstep (se 1 (by rfl) ⟨10640969, by rfl⟩ : syracuseStep 14187959 = 21281939) B21281939
theorem B3153343 : Blo 1659529 3153343 := bstep (se 1 (by rfl) ⟨2365007, by rfl⟩ : syracuseStep 3153343 = 4730015) B4730015
theorem B2490095 : Blo 1659529 2490095 := bstep (se 1 (by rfl) ⟨1867571, by rfl⟩ : syracuseStep 2490095 = 3735143) B3735143
theorem B2490239 : Blo 1659529 2490239 := bstep (se 1 (by rfl) ⟨1867679, by rfl⟩ : syracuseStep 2490239 = 3735359) B3735359
theorem B2801567 : Blo 1659529 2801567 := bstep (se 1 (by rfl) ⟨2101175, by rfl⟩ : syracuseStep 2801567 = 4202351) B4202351
theorem B2490431 : Blo 1659529 2490431 := bstep (se 1 (by rfl) ⟨1867823, by rfl⟩ : syracuseStep 2490431 = 3735647) B3735647
theorem B2490479 : Blo 1659529 2490479 := bstep (se 1 (by rfl) ⟨1867859, by rfl⟩ : syracuseStep 2490479 = 3735719) B3735719
theorem B3785119 : Blo 1659529 3785119 := bstep (se 1 (by rfl) ⟨2838839, by rfl⟩ : syracuseStep 3785119 = 5677679) B5677679
theorem B2990567 : Blo 1659529 2990567 := bstep (se 1 (by rfl) ⟨2242925, by rfl⟩ : syracuseStep 2990567 = 4485851) B4485851
theorem B51118573 : Blo 1659529 51118573 := bstep (se 3 (by rfl) ⟨9584732, by rfl⟩ : syracuseStep 51118573 = 19169465) B19169465
theorem B2802431 : Blo 1659529 2802431 := bstep (se 1 (by rfl) ⟨2101823, by rfl⟩ : syracuseStep 2802431 = 4203647) B4203647
theorem B4498267 : Blo 1659529 4498267 := bstep (se 1 (by rfl) ⟨3373700, by rfl⟩ : syracuseStep 4498267 = 6747401) B6747401
theorem B15967219 : Blo 1659529 15967219 := bstep (se 1 (by rfl) ⟨11975414, by rfl⟩ : syracuseStep 15967219 = 23950829) B23950829
theorem B4203515 : Blo 1659529 4203515 := bstep (se 1 (by rfl) ⟨3152636, by rfl⟩ : syracuseStep 4203515 = 6305273) B6305273
theorem B3736889 : Blo 1659529 3736889 := bstep (se 2 (by rfl) ⟨1401333, by rfl⟩ : syracuseStep 3736889 = 2802667) B2802667
theorem B2491883 : Blo 1659529 2491883 := bstep (se 1 (by rfl) ⟨1868912, by rfl⟩ : syracuseStep 2491883 = 3737825) B3737825
theorem B3737339 : Blo 1659529 3737339 := bstep (se 1 (by rfl) ⟨2803004, by rfl⟩ : syracuseStep 3737339 = 5606009) B5606009
theorem B5605145 : Blo 1659529 5605145 := bstep (se 2 (by rfl) ⟨2101929, by rfl⟩ : syracuseStep 5605145 = 4203859) B4203859
theorem B6301597 : Blo 1659529 6301597 := bstep (se 3 (by rfl) ⟨1181549, by rfl⟩ : syracuseStep 6301597 = 2363099) B2363099
theorem B4204457 : Blo 1659529 4204457 := bstep (se 2 (by rfl) ⟨1576671, by rfl⟩ : syracuseStep 4204457 = 3153343) B3153343
theorem B3737663 : Blo 1659529 3737663 := bstep (se 1 (by rfl) ⟨2803247, by rfl⟩ : syracuseStep 3737663 = 5606495) B5606495
theorem B3738239 : Blo 1659529 3738239 := bstep (se 1 (by rfl) ⟨2803679, by rfl⟩ : syracuseStep 3738239 = 5607359) B5607359
theorem B5606333 : Blo 1659529 5606333 := bstep (se 3 (by rfl) ⟨1051187, by rfl⟩ : syracuseStep 5606333 = 2102375) B2102375
theorem B17042395 : Blo 1659529 17042395 := bstep (se 1 (by rfl) ⟨12781796, by rfl⟩ : syracuseStep 17042395 = 25563593) B25563593
theorem B8408123 : Blo 1659529 8408123 := bstep (se 1 (by rfl) ⟨6306092, by rfl⟩ : syracuseStep 8408123 = 12612185) B12612185
theorem B2993479 : Blo 1659529 2993479 := bstep (se 1 (by rfl) ⟨2245109, by rfl⟩ : syracuseStep 2993479 = 4490219) B4490219
theorem B15953345 : Blo 1659529 15953345 := bstep (se 2 (by rfl) ⟨5982504, by rfl⟩ : syracuseStep 15953345 = 11965009) B11965009
theorem B4730471 : Blo 1659529 4730471 := bstep (se 1 (by rfl) ⟨3547853, by rfl⟩ : syracuseStep 4730471 = 7095707) B7095707
theorem B14184335 : Blo 1659529 14184335 := bstep (se 1 (by rfl) ⟨10638251, by rfl⟩ : syracuseStep 14184335 = 21276503) B21276503
theorem B8409257 : Blo 1659529 8409257 := bstep (se 2 (by rfl) ⟨3153471, by rfl⟩ : syracuseStep 8409257 = 6306943) B6306943
theorem B2838719 : Blo 1659529 2838719 := bstep (se 1 (by rfl) ⟨2129039, by rfl⟩ : syracuseStep 2838719 = 4258079) B4258079
theorem B230076773 : Blo 1659529 230076773 := bstep (se 4 (by rfl) ⟨21569697, by rfl⟩ : syracuseStep 230076773 = 43139395) B43139395
theorem B63812285 : Blo 1659529 63812285 := bstep (se 3 (by rfl) ⟨11964803, by rfl⟩ : syracuseStep 63812285 = 23929607) B23929607
theorem B1659583 : Blo 1659529 1659583 := bstep (se 1 (by rfl) ⟨1244687, by rfl⟩ : syracuseStep 1659583 = 2489375) B2489375
theorem B6304499 : Blo 1659529 6304499 := bstep (se 1 (by rfl) ⟨4728374, by rfl⟩ : syracuseStep 6304499 = 9456749) B9456749
theorem B9458639 : Blo 1659529 9458639 := bstep (se 1 (by rfl) ⟨7093979, by rfl⟩ : syracuseStep 9458639 = 14187959) B14187959
theorem B12612671 : Blo 1659529 12612671 := bstep (se 1 (by rfl) ⟨9459503, by rfl⟩ : syracuseStep 12612671 = 18919007) B18919007
theorem B1660063 : Blo 1659529 1660063 := bstep (se 1 (by rfl) ⟨1245047, by rfl⟩ : syracuseStep 1660063 = 2490095) B2490095
theorem B1660159 : Blo 1659529 1660159 := bstep (se 1 (by rfl) ⟨1245119, by rfl⟩ : syracuseStep 1660159 = 2490239) B2490239
theorem B4552183 : Blo 1659529 4552183 := bstep (se 1 (by rfl) ⟨3414137, by rfl⟩ : syracuseStep 4552183 = 6828275) B6828275
theorem B1660463 : Blo 1659529 1660463 := bstep (se 1 (by rfl) ⟨1245347, by rfl⟩ : syracuseStep 1660463 = 2490695) B2490695
theorem B3544735 : Blo 1659529 3544735 := bstep (se 1 (by rfl) ⟨2658551, by rfl⟩ : syracuseStep 3544735 = 5317103) B5317103
theorem B24926075 : Blo 1659529 24926075 := bstep (se 1 (by rfl) ⟨18694556, by rfl⟩ : syracuseStep 24926075 = 37389113) B37389113
theorem B5601149 : Blo 1659529 5601149 := bstep (se 3 (by rfl) ⟨1050215, by rfl⟩ : syracuseStep 5601149 = 2100431) B2100431
theorem B5601311 : Blo 1659529 5601311 := bstep (se 1 (by rfl) ⟨4200983, by rfl⟩ : syracuseStep 5601311 = 8401967) B8401967
theorem B4200731 : Blo 1659529 4200731 := bstep (se 1 (by rfl) ⟨3150548, by rfl⟩ : syracuseStep 4200731 = 6301097) B6301097
theorem B3365167 : Blo 1659529 3365167 := bstep (se 1 (by rfl) ⟨2523875, by rfl⟩ : syracuseStep 3365167 = 5047751) B5047751
theorem B1661247 : Blo 1659529 1661247 := bstep (se 1 (by rfl) ⟨1245935, by rfl⟩ : syracuseStep 1661247 = 2491871) B2491871
theorem B40417811 : Blo 1659529 40417811 := bstep (se 1 (by rfl) ⟨30313358, by rfl⟩ : syracuseStep 40417811 = 60626717) B60626717
theorem B1661487 : Blo 1659529 1661487 := bstep (se 1 (by rfl) ⟨1246115, by rfl⟩ : syracuseStep 1661487 = 2492231) B2492231
theorem B8403911 : Blo 1659529 8403911 := bstep (se 1 (by rfl) ⟨6302933, by rfl⟩ : syracuseStep 8403911 = 12605867) B12605867
theorem B3194095 : Blo 1659529 3194095 := bstep (se 1 (by rfl) ⟨2395571, by rfl⟩ : syracuseStep 3194095 = 4791143) B4791143
theorem B1867135 : Blo 1659529 1867135 := bstep (se 1 (by rfl) ⟨1400351, by rfl⟩ : syracuseStep 1867135 = 2800703) B2800703
theorem B2489927 : Blo 1659529 2489927 := bstep (se 1 (by rfl) ⟨1867445, by rfl⟩ : syracuseStep 2489927 = 3734891) B3734891
theorem B22724297 : Blo 1659529 22724297 := bstep (se 2 (by rfl) ⟨8521611, by rfl⟩ : syracuseStep 22724297 = 17043223) B17043223
theorem B13459175 : Blo 1659529 13459175 := bstep (se 1 (by rfl) ⟨10094381, by rfl⟩ : syracuseStep 13459175 = 20188763) B20188763
theorem B1867711 : Blo 1659529 1867711 := bstep (se 1 (by rfl) ⟨1400783, by rfl⟩ : syracuseStep 1867711 = 2801567) B2801567
theorem B1892479 : Blo 1659529 1892479 := bstep (se 1 (by rfl) ⟨1419359, by rfl⟩ : syracuseStep 1892479 = 2838719) B2838719
theorem B42541523 : Blo 1659529 42541523 := bstep (se 1 (by rfl) ⟨31906142, by rfl⟩ : syracuseStep 42541523 = 63812285) B63812285
theorem B4202999 : Blo 1659529 4202999 := bstep (se 1 (by rfl) ⟨3152249, by rfl⟩ : syracuseStep 4202999 = 6304499) B6304499
theorem B1868287 : Blo 1659529 1868287 := bstep (se 1 (by rfl) ⟨1401215, by rfl⟩ : syracuseStep 1868287 = 2802431) B2802431
theorem B68158097 : Blo 1659529 68158097 := bstep (se 2 (by rfl) ⟨25559286, by rfl⟩ : syracuseStep 68158097 = 51118573) B51118573
theorem B2802343 : Blo 1659529 2802343 := bstep (se 1 (by rfl) ⟨2101757, by rfl⟩ : syracuseStep 2802343 = 4203515) B4203515
theorem B2491259 : Blo 1659529 2491259 := bstep (se 1 (by rfl) ⟨1868444, by rfl⟩ : syracuseStep 2491259 = 3736889) B3736889
theorem B5997689 : Blo 1659529 5997689 := bstep (se 2 (by rfl) ⟨2249133, by rfl⟩ : syracuseStep 5997689 = 4498267) B4498267
theorem B2491559 : Blo 1659529 2491559 := bstep (se 1 (by rfl) ⟨1868669, by rfl⟩ : syracuseStep 2491559 = 3737339) B3737339
theorem B3736763 : Blo 1659529 3736763 := bstep (se 1 (by rfl) ⟨2802572, by rfl⟩ : syracuseStep 3736763 = 5605145) B5605145
theorem B2802971 : Blo 1659529 2802971 := bstep (se 1 (by rfl) ⟨2102228, by rfl⟩ : syracuseStep 2802971 = 4204457) B4204457
theorem B2491775 : Blo 1659529 2491775 := bstep (se 1 (by rfl) ⟨1868831, by rfl⟩ : syracuseStep 2491775 = 3737663) B3737663
theorem B26945207 : Blo 1659529 26945207 := bstep (se 1 (by rfl) ⟨20208905, by rfl⟩ : syracuseStep 26945207 = 40417811) B40417811
theorem B2492159 : Blo 1659529 2492159 := bstep (se 1 (by rfl) ⟨1869119, by rfl⟩ : syracuseStep 2492159 = 3738239) B3738239
theorem B3737555 : Blo 1659529 3737555 := bstep (se 1 (by rfl) ⟨2803166, by rfl⟩ : syracuseStep 3737555 = 5606333) B5606333
theorem B5605415 : Blo 1659529 5605415 := bstep (se 1 (by rfl) ⟨4204061, by rfl⟩ : syracuseStep 5605415 = 8408123) B8408123
theorem B20187301 : Blo 1659529 20187301 := bstep (se 4 (by rfl) ⟨1892559, by rfl⟩ : syracuseStep 20187301 = 3785119) B3785119
theorem B10635563 : Blo 1659529 10635563 := bstep (se 1 (by rfl) ⟨7976672, by rfl⟩ : syracuseStep 10635563 = 15953345) B15953345
theorem B15149531 : Blo 1659529 15149531 := bstep (se 1 (by rfl) ⟨11362148, by rfl⟩ : syracuseStep 15149531 = 22724297) B22724297
theorem B8972783 : Blo 1659529 8972783 := bstep (se 1 (by rfl) ⟨6729587, by rfl⟩ : syracuseStep 8972783 = 13459175) B13459175
theorem B9456223 : Blo 1659529 9456223 := bstep (se 1 (by rfl) ⟨7092167, by rfl⟩ : syracuseStep 9456223 = 14184335) B14184335
theorem B5606171 : Blo 1659529 5606171 := bstep (se 1 (by rfl) ⟨4204628, by rfl⟩ : syracuseStep 5606171 = 8409257) B8409257
theorem B8408447 : Blo 1659529 8408447 := bstep (se 1 (by rfl) ⟨6306335, by rfl⟩ : syracuseStep 8408447 = 12612671) B12612671
theorem B16617383 : Blo 1659529 16617383 := bstep (se 1 (by rfl) ⟨12463037, by rfl⟩ : syracuseStep 16617383 = 24926075) B24926075
theorem B7974845 : Blo 1659529 7974845 := bstep (se 3 (by rfl) ⟨1495283, by rfl⟩ : syracuseStep 7974845 = 2990567) B2990567
theorem B1659951 : Blo 1659529 1659951 := bstep (se 1 (by rfl) ⟨1244963, by rfl⟩ : syracuseStep 1659951 = 2489927) B2489927
theorem B8402129 : Blo 1659529 8402129 := bstep (se 2 (by rfl) ⟨3150798, by rfl⟩ : syracuseStep 8402129 = 6301597) B6301597
theorem B24278309 : Blo 1659529 24278309 := bstep (se 4 (by rfl) ⟨2276091, by rfl⟩ : syracuseStep 24278309 = 4552183) B4552183
theorem B1660287 : Blo 1659529 1660287 := bstep (se 1 (by rfl) ⟨1245215, by rfl⟩ : syracuseStep 1660287 = 2490431) B2490431
theorem B1660319 : Blo 1659529 1660319 := bstep (se 1 (by rfl) ⟨1245239, by rfl⟩ : syracuseStep 1660319 = 2490479) B2490479
theorem B153384515 : Blo 1659529 153384515 := bstep (se 1 (by rfl) ⟨115038386, by rfl⟩ : syracuseStep 153384515 = 230076773) B230076773
theorem B4486889 : Blo 1659529 4486889 := bstep (se 2 (by rfl) ⟨1682583, by rfl⟩ : syracuseStep 4486889 = 3365167) B3365167
theorem B6305759 : Blo 1659529 6305759 := bstep (se 1 (by rfl) ⟨4729319, by rfl⟩ : syracuseStep 6305759 = 9458639) B9458639
theorem B1661255 : Blo 1659529 1661255 := bstep (se 1 (by rfl) ⟨1245941, by rfl⟩ : syracuseStep 1661255 = 2491883) B2491883
theorem B3734099 : Blo 1659529 3734099 := bstep (se 1 (by rfl) ⟨2800574, by rfl⟩ : syracuseStep 3734099 = 5601149) B5601149
theorem B22723193 : Blo 1659529 22723193 := bstep (se 2 (by rfl) ⟨8521197, by rfl⟩ : syracuseStep 22723193 = 17042395) B17042395
theorem B21289625 : Blo 1659529 21289625 := bstep (se 2 (by rfl) ⟨7983609, by rfl⟩ : syracuseStep 21289625 = 15967219) B15967219
theorem B3734207 : Blo 1659529 3734207 := bstep (se 1 (by rfl) ⟨2800655, by rfl⟩ : syracuseStep 3734207 = 5601311) B5601311
theorem B2800487 : Blo 1659529 2800487 := bstep (se 1 (by rfl) ⟨2100365, by rfl⟩ : syracuseStep 2800487 = 4200731) B4200731
theorem B4258793 : Blo 1659529 4258793 := bstep (se 2 (by rfl) ⟨1597047, by rfl⟩ : syracuseStep 4258793 = 3194095) B3194095
theorem B15965221 : Blo 1659529 15965221 := bstep (se 4 (by rfl) ⟨1496739, by rfl⟩ : syracuseStep 15965221 = 2993479) B2993479
theorem B2489513 : Blo 1659529 2489513 := bstep (se 2 (by rfl) ⟨933567, by rfl⟩ : syracuseStep 2489513 = 1867135) B1867135
theorem B5602607 : Blo 1659529 5602607 := bstep (se 1 (by rfl) ⟨4201955, by rfl⟩ : syracuseStep 5602607 = 8403911) B8403911
theorem B4726313 : Blo 1659529 4726313 := bstep (se 2 (by rfl) ⟨1772367, by rfl⟩ : syracuseStep 4726313 = 3544735) B3544735
theorem B3153647 : Blo 1659529 3153647 := bstep (se 1 (by rfl) ⟨2365235, by rfl⟩ : syracuseStep 3153647 = 4730471) B4730471
theorem B2490281 : Blo 1659529 2490281 := bstep (se 2 (by rfl) ⟨933855, by rfl⟩ : syracuseStep 2490281 = 1867711) B1867711
theorem B2523305 : Blo 1659529 2523305 := bstep (se 2 (by rfl) ⟨946239, by rfl⟩ : syracuseStep 2523305 = 1892479) B1892479
theorem B28361015 : Blo 1659529 28361015 := bstep (se 1 (by rfl) ⟨21270761, by rfl⟩ : syracuseStep 28361015 = 42541523) B42541523
theorem B2801999 : Blo 1659529 2801999 := bstep (se 1 (by rfl) ⟨2101499, by rfl⟩ : syracuseStep 2801999 = 4202999) B4202999
theorem B2491049 : Blo 1659529 2491049 := bstep (se 2 (by rfl) ⟨934143, by rfl⟩ : syracuseStep 2491049 = 1868287) B1868287
theorem B3998459 : Blo 1659529 3998459 := bstep (se 1 (by rfl) ⟨2998844, by rfl⟩ : syracuseStep 3998459 = 5997689) B5997689
theorem B2491175 : Blo 1659529 2491175 := bstep (se 1 (by rfl) ⟨1868381, by rfl⟩ : syracuseStep 2491175 = 3736763) B3736763
theorem B12608297 : Blo 1659529 12608297 := bstep (se 2 (by rfl) ⟨4728111, by rfl⟩ : syracuseStep 12608297 = 9456223) B9456223
theorem B1868647 : Blo 1659529 1868647 := bstep (se 1 (by rfl) ⟨1401485, by rfl⟩ : syracuseStep 1868647 = 2802971) B2802971
theorem B3736457 : Blo 1659529 3736457 := bstep (se 2 (by rfl) ⟨1401171, by rfl⟩ : syracuseStep 3736457 = 2802343) B2802343
theorem B2991259 : Blo 1659529 2991259 := bstep (se 1 (by rfl) ⟨2243444, by rfl⟩ : syracuseStep 2991259 = 4486889) B4486889
theorem B2491703 : Blo 1659529 2491703 := bstep (se 1 (by rfl) ⟨1868777, by rfl⟩ : syracuseStep 2491703 = 3737555) B3737555
theorem B4203839 : Blo 1659529 4203839 := bstep (se 1 (by rfl) ⟨3152879, by rfl⟩ : syracuseStep 4203839 = 6305759) B6305759
theorem B3736943 : Blo 1659529 3736943 := bstep (se 1 (by rfl) ⟨2802707, by rfl⟩ : syracuseStep 3736943 = 5605415) B5605415
theorem B5981855 : Blo 1659529 5981855 := bstep (se 1 (by rfl) ⟨4486391, by rfl⟩ : syracuseStep 5981855 = 8972783) B8972783
theorem B15148795 : Blo 1659529 15148795 := bstep (se 1 (by rfl) ⟨11361596, by rfl⟩ : syracuseStep 15148795 = 22723193) B22723193
theorem B3737447 : Blo 1659529 3737447 := bstep (se 1 (by rfl) ⟨2803085, by rfl⟩ : syracuseStep 3737447 = 5606171) B5606171
theorem B5605631 : Blo 1659529 5605631 := bstep (se 1 (by rfl) ⟨4204223, by rfl⟩ : syracuseStep 5605631 = 8408447) B8408447
theorem B11078255 : Blo 1659529 11078255 := bstep (se 1 (by rfl) ⟨8308691, by rfl⟩ : syracuseStep 11078255 = 16617383) B16617383
theorem B102256343 : Blo 1659529 102256343 := bstep (se 1 (by rfl) ⟨76692257, by rfl⟩ : syracuseStep 102256343 = 153384515) B153384515
theorem B21286961 : Blo 1659529 21286961 := bstep (se 2 (by rfl) ⟨7982610, by rfl⟩ : syracuseStep 21286961 = 15965221) B15965221
theorem B7090375 : Blo 1659529 7090375 := bstep (se 1 (by rfl) ⟨5317781, by rfl⟩ : syracuseStep 7090375 = 10635563) B10635563
theorem B14193083 : Blo 1659529 14193083 := bstep (se 1 (by rfl) ⟨10644812, by rfl⟩ : syracuseStep 14193083 = 21289625) B21289625
theorem B2839195 : Blo 1659529 2839195 := bstep (se 1 (by rfl) ⟨2129396, by rfl⟩ : syracuseStep 2839195 = 4258793) B4258793
theorem B1659675 : Blo 1659529 1659675 := bstep (se 1 (by rfl) ⟨1244756, by rfl⟩ : syracuseStep 1659675 = 2489513) B2489513
theorem B3150875 : Blo 1659529 3150875 := bstep (se 1 (by rfl) ⟨2363156, by rfl⟩ : syracuseStep 3150875 = 4726313) B4726313
theorem B2102431 : Blo 1659529 2102431 := bstep (se 1 (by rfl) ⟨1576823, by rfl⟩ : syracuseStep 2102431 = 3153647) B3153647
theorem B1660187 : Blo 1659529 1660187 := bstep (se 1 (by rfl) ⟨1245140, by rfl⟩ : syracuseStep 1660187 = 2490281) B2490281
theorem B26916401 : Blo 1659529 26916401 := bstep (se 2 (by rfl) ⟨10093650, by rfl⟩ : syracuseStep 26916401 = 20187301) B20187301
theorem B45438731 : Blo 1659529 45438731 := bstep (se 1 (by rfl) ⟨34079048, by rfl⟩ : syracuseStep 45438731 = 68158097) B68158097
theorem B1660839 : Blo 1659529 1660839 := bstep (se 1 (by rfl) ⟨1245629, by rfl⟩ : syracuseStep 1660839 = 2491259) B2491259
theorem B1661039 : Blo 1659529 1661039 := bstep (se 1 (by rfl) ⟨1245779, by rfl⟩ : syracuseStep 1661039 = 2491559) B2491559
theorem B5601419 : Blo 1659529 5601419 := bstep (se 1 (by rfl) ⟨4201064, by rfl⟩ : syracuseStep 5601419 = 8402129) B8402129
theorem B16185539 : Blo 1659529 16185539 := bstep (se 1 (by rfl) ⟨12139154, by rfl⟩ : syracuseStep 16185539 = 24278309) B24278309
theorem B1661183 : Blo 1659529 1661183 := bstep (se 1 (by rfl) ⟨1245887, by rfl⟩ : syracuseStep 1661183 = 2491775) B2491775
theorem B17963471 : Blo 1659529 17963471 := bstep (se 1 (by rfl) ⟨13472603, by rfl⟩ : syracuseStep 17963471 = 26945207) B26945207
theorem B1661439 : Blo 1659529 1661439 := bstep (se 1 (by rfl) ⟨1246079, by rfl⟩ : syracuseStep 1661439 = 2492159) B2492159
theorem B10099687 : Blo 1659529 10099687 := bstep (se 1 (by rfl) ⟨7574765, by rfl⟩ : syracuseStep 10099687 = 15149531) B15149531
theorem B2489399 : Blo 1659529 2489399 := bstep (se 1 (by rfl) ⟨1867049, by rfl⟩ : syracuseStep 2489399 = 3734099) B3734099
theorem B2489471 : Blo 1659529 2489471 := bstep (se 1 (by rfl) ⟨1867103, by rfl⟩ : syracuseStep 2489471 = 3734207) B3734207
theorem B1866991 : Blo 1659529 1866991 := bstep (se 1 (by rfl) ⟨1400243, by rfl⟩ : syracuseStep 1866991 = 2800487) B2800487
theorem B3735071 : Blo 1659529 3735071 := bstep (se 1 (by rfl) ⟨2801303, by rfl⟩ : syracuseStep 3735071 = 5602607) B5602607
theorem B5316563 : Blo 1659529 5316563 := bstep (se 1 (by rfl) ⟨3987422, by rfl⟩ : syracuseStep 5316563 = 7974845) B7974845
theorem B18907343 : Blo 1659529 18907343 := bstep (se 1 (by rfl) ⟨14180507, by rfl⟩ : syracuseStep 18907343 = 28361015) B28361015
theorem B1867999 : Blo 1659529 1867999 := bstep (se 1 (by rfl) ⟨1400999, by rfl⟩ : syracuseStep 1867999 = 2801999) B2801999
theorem B9453833 : Blo 1659529 9453833 := bstep (se 2 (by rfl) ⟨3545187, by rfl⟩ : syracuseStep 9453833 = 7090375) B7090375
theorem B9462055 : Blo 1659529 9462055 := bstep (se 1 (by rfl) ⟨7096541, by rfl⟩ : syracuseStep 9462055 = 14193083) B14193083
theorem B8405531 : Blo 1659529 8405531 := bstep (se 1 (by rfl) ⟨6304148, by rfl⟩ : syracuseStep 8405531 = 12608297) B12608297
theorem B2490971 : Blo 1659529 2490971 := bstep (se 1 (by rfl) ⟨1868228, by rfl⟩ : syracuseStep 2490971 = 3736457) B3736457
theorem B2802559 : Blo 1659529 2802559 := bstep (se 1 (by rfl) ⟨2101919, by rfl⟩ : syracuseStep 2802559 = 4203839) B4203839
theorem B2491295 : Blo 1659529 2491295 := bstep (se 1 (by rfl) ⟨1868471, by rfl⟩ : syracuseStep 2491295 = 3736943) B3736943
theorem B2491529 : Blo 1659529 2491529 := bstep (se 2 (by rfl) ⟨934323, by rfl⟩ : syracuseStep 2491529 = 1868647) B1868647
theorem B2491631 : Blo 1659529 2491631 := bstep (se 1 (by rfl) ⟨1868723, by rfl⟩ : syracuseStep 2491631 = 3737447) B3737447
theorem B3737087 : Blo 1659529 3737087 := bstep (se 1 (by rfl) ⟨2802815, by rfl⟩ : syracuseStep 3737087 = 5605631) B5605631
theorem B2803241 : Blo 1659529 2803241 := bstep (se 2 (by rfl) ⟨1051215, by rfl⟩ : syracuseStep 2803241 = 2102431) B2102431
theorem B29542013 : Blo 1659529 29542013 := bstep (se 3 (by rfl) ⟨5539127, by rfl⟩ : syracuseStep 29542013 = 11078255) B11078255
theorem B15951613 : Blo 1659529 15951613 := bstep (se 3 (by rfl) ⟨2990927, by rfl⟩ : syracuseStep 15951613 = 5981855) B5981855
theorem B14191307 : Blo 1659529 14191307 := bstep (se 1 (by rfl) ⟨10643480, by rfl⟩ : syracuseStep 14191307 = 21286961) B21286961
theorem B1682203 : Blo 1659529 1682203 := bstep (se 1 (by rfl) ⟨1261652, by rfl⟩ : syracuseStep 1682203 = 2523305) B2523305
theorem B2665639 : Blo 1659529 2665639 := bstep (se 1 (by rfl) ⟨1999229, by rfl⟩ : syracuseStep 2665639 = 3998459) B3998459
theorem B2100583 : Blo 1659529 2100583 := bstep (se 1 (by rfl) ⟨1575437, by rfl⟩ : syracuseStep 2100583 = 3150875) B3150875
theorem B15142373 : Blo 1659529 15142373 := bstep (se 4 (by rfl) ⟨1419597, by rfl⟩ : syracuseStep 15142373 = 2839195) B2839195
theorem B15953381 : Blo 1659529 15953381 := bstep (se 4 (by rfl) ⟨1495629, by rfl⟩ : syracuseStep 15953381 = 2991259) B2991259
theorem B17944267 : Blo 1659529 17944267 := bstep (se 1 (by rfl) ⟨13458200, by rfl⟩ : syracuseStep 17944267 = 26916401) B26916401
theorem B1659599 : Blo 1659529 1659599 := bstep (se 1 (by rfl) ⟨1244699, by rfl⟩ : syracuseStep 1659599 = 2489399) B2489399
theorem B1659647 : Blo 1659529 1659647 := bstep (se 1 (by rfl) ⟨1244735, by rfl⟩ : syracuseStep 1659647 = 2489471) B2489471
theorem B20198393 : Blo 1659529 20198393 := bstep (se 2 (by rfl) ⟨7574397, by rfl⟩ : syracuseStep 20198393 = 15148795) B15148795
theorem B68170895 : Blo 1659529 68170895 := bstep (se 1 (by rfl) ⟨51128171, by rfl⟩ : syracuseStep 68170895 = 102256343) B102256343
theorem B14177501 : Blo 1659529 14177501 := bstep (se 3 (by rfl) ⟨2658281, by rfl⟩ : syracuseStep 14177501 = 5316563) B5316563
theorem B1660699 : Blo 1659529 1660699 := bstep (se 1 (by rfl) ⟨1245524, by rfl⟩ : syracuseStep 1660699 = 2491049) B2491049
theorem B43161437 : Blo 1659529 43161437 := bstep (se 3 (by rfl) ⟨8092769, by rfl⟩ : syracuseStep 43161437 = 16185539) B16185539
theorem B1660783 : Blo 1659529 1660783 := bstep (se 1 (by rfl) ⟨1245587, by rfl⟩ : syracuseStep 1660783 = 2491175) B2491175
theorem B1661135 : Blo 1659529 1661135 := bstep (se 1 (by rfl) ⟨1245851, by rfl⟩ : syracuseStep 1661135 = 2491703) B2491703
theorem B30292487 : Blo 1659529 30292487 := bstep (se 1 (by rfl) ⟨22719365, by rfl⟩ : syracuseStep 30292487 = 45438731) B45438731
theorem B13466249 : Blo 1659529 13466249 := bstep (se 2 (by rfl) ⟨5049843, by rfl⟩ : syracuseStep 13466249 = 10099687) B10099687
theorem B3734279 : Blo 1659529 3734279 := bstep (se 1 (by rfl) ⟨2800709, by rfl⟩ : syracuseStep 3734279 = 5601419) B5601419
theorem B11975647 : Blo 1659529 11975647 := bstep (se 1 (by rfl) ⟨8981735, by rfl⟩ : syracuseStep 11975647 = 17963471) B17963471
theorem B2489321 : Blo 1659529 2489321 := bstep (se 2 (by rfl) ⟨933495, by rfl⟩ : syracuseStep 2489321 = 1866991) B1866991
theorem B2490047 : Blo 1659529 2490047 := bstep (se 1 (by rfl) ⟨1867535, by rfl⟩ : syracuseStep 2490047 = 3735071) B3735071
theorem B2490665 : Blo 1659529 2490665 := bstep (se 2 (by rfl) ⟨933999, by rfl⟩ : syracuseStep 2490665 = 1867999) B1867999
theorem B5603687 : Blo 1659529 5603687 := bstep (se 1 (by rfl) ⟨4202765, by rfl⟩ : syracuseStep 5603687 = 8405531) B8405531
theorem B12616073 : Blo 1659529 12616073 := bstep (se 2 (by rfl) ⟨4731027, by rfl⟩ : syracuseStep 12616073 = 9462055) B9462055
theorem B2491391 : Blo 1659529 2491391 := bstep (se 1 (by rfl) ⟨1868543, by rfl⟩ : syracuseStep 2491391 = 3737087) B3737087
theorem B1868827 : Blo 1659529 1868827 := bstep (se 1 (by rfl) ⟨1401620, by rfl⟩ : syracuseStep 1868827 = 2803241) B2803241
theorem B19694675 : Blo 1659529 19694675 := bstep (se 1 (by rfl) ⟨14771006, by rfl⟩ : syracuseStep 19694675 = 29542013) B29542013
theorem B3736745 : Blo 1659529 3736745 := bstep (se 2 (by rfl) ⟨1401279, by rfl⟩ : syracuseStep 3736745 = 2802559) B2802559
theorem B15967529 : Blo 1659529 15967529 := bstep (se 2 (by rfl) ⟨5987823, by rfl⟩ : syracuseStep 15967529 = 11975647) B11975647
theorem B20194991 : Blo 1659529 20194991 := bstep (se 1 (by rfl) ⟨15146243, by rfl⟩ : syracuseStep 20194991 = 30292487) B30292487
theorem B10094915 : Blo 1659529 10094915 := bstep (se 1 (by rfl) ⟨7571186, by rfl⟩ : syracuseStep 10094915 = 15142373) B15142373
theorem B10635587 : Blo 1659529 10635587 := bstep (se 1 (by rfl) ⟨7976690, by rfl⟩ : syracuseStep 10635587 = 15953381) B15953381
theorem B21268817 : Blo 1659529 21268817 := bstep (se 2 (by rfl) ⟨7975806, by rfl⟩ : syracuseStep 21268817 = 15951613) B15951613
theorem B6302555 : Blo 1659529 6302555 := bstep (se 1 (by rfl) ⟨4726916, by rfl⟩ : syracuseStep 6302555 = 9453833) B9453833
theorem B14216741 : Blo 1659529 14216741 := bstep (se 4 (by rfl) ⟨1332819, by rfl⟩ : syracuseStep 14216741 = 2665639) B2665639
theorem B28774291 : Blo 1659529 28774291 := bstep (se 1 (by rfl) ⟨21580718, by rfl⟩ : syracuseStep 28774291 = 43161437) B43161437
theorem B1659547 : Blo 1659529 1659547 := bstep (se 1 (by rfl) ⟨1244660, by rfl⟩ : syracuseStep 1659547 = 2489321) B2489321
theorem B23925689 : Blo 1659529 23925689 := bstep (se 2 (by rfl) ⟨8972133, by rfl⟩ : syracuseStep 23925689 = 17944267) B17944267
theorem B1660031 : Blo 1659529 1660031 := bstep (se 1 (by rfl) ⟨1245023, by rfl⟩ : syracuseStep 1660031 = 2490047) B2490047
theorem B12604895 : Blo 1659529 12604895 := bstep (se 1 (by rfl) ⟨9453671, by rfl⟩ : syracuseStep 12604895 = 18907343) B18907343
theorem B1660647 : Blo 1659529 1660647 := bstep (se 1 (by rfl) ⟨1245485, by rfl⟩ : syracuseStep 1660647 = 2490971) B2490971
theorem B1660863 : Blo 1659529 1660863 := bstep (se 1 (by rfl) ⟨1245647, by rfl⟩ : syracuseStep 1660863 = 2491295) B2491295
theorem B13465595 : Blo 1659529 13465595 := bstep (se 1 (by rfl) ⟨10099196, by rfl⟩ : syracuseStep 13465595 = 20198393) B20198393
theorem B1661019 : Blo 1659529 1661019 := bstep (se 1 (by rfl) ⟨1245764, by rfl⟩ : syracuseStep 1661019 = 2491529) B2491529
theorem B45447263 : Blo 1659529 45447263 := bstep (se 1 (by rfl) ⟨34085447, by rfl⟩ : syracuseStep 45447263 = 68170895) B68170895
theorem B9451667 : Blo 1659529 9451667 := bstep (se 1 (by rfl) ⟨7088750, by rfl⟩ : syracuseStep 9451667 = 14177501) B14177501
theorem B1661087 : Blo 1659529 1661087 := bstep (se 1 (by rfl) ⟨1245815, by rfl⟩ : syracuseStep 1661087 = 2491631) B2491631
theorem B2242937 : Blo 1659529 2242937 := bstep (se 2 (by rfl) ⟨841101, by rfl⟩ : syracuseStep 2242937 = 1682203) B1682203
theorem B8977499 : Blo 1659529 8977499 := bstep (se 1 (by rfl) ⟨6733124, by rfl⟩ : syracuseStep 8977499 = 13466249) B13466249
theorem B9460871 : Blo 1659529 9460871 := bstep (se 1 (by rfl) ⟨7095653, by rfl⟩ : syracuseStep 9460871 = 14191307) B14191307
theorem B2800777 : Blo 1659529 2800777 := bstep (se 2 (by rfl) ⟨1050291, by rfl⟩ : syracuseStep 2800777 = 2100583) B2100583
theorem B2489519 : Blo 1659529 2489519 := bstep (se 1 (by rfl) ⟨1867139, by rfl⟩ : syracuseStep 2489519 = 3734279) B3734279
theorem B3735791 : Blo 1659529 3735791 := bstep (se 1 (by rfl) ⟨2801843, by rfl⟩ : syracuseStep 3735791 = 5603687) B5603687
theorem B15950459 : Blo 1659529 15950459 := bstep (se 1 (by rfl) ⟨11962844, by rfl⟩ : syracuseStep 15950459 = 23925689) B23925689
theorem B2491163 : Blo 1659529 2491163 := bstep (se 1 (by rfl) ⟨1868372, by rfl⟩ : syracuseStep 2491163 = 3736745) B3736745
theorem B26919773 : Blo 1659529 26919773 := bstep (se 3 (by rfl) ⟨5047457, by rfl⟩ : syracuseStep 26919773 = 10094915) B10094915
theorem B5981165 : Blo 1659529 5981165 := bstep (se 3 (by rfl) ⟨1121468, by rfl⟩ : syracuseStep 5981165 = 2242937) B2242937
theorem B2491769 : Blo 1659529 2491769 := bstep (se 2 (by rfl) ⟨934413, by rfl⟩ : syracuseStep 2491769 = 1868827) B1868827
theorem B6301111 : Blo 1659529 6301111 := bstep (se 1 (by rfl) ⟨4725833, by rfl⟩ : syracuseStep 6301111 = 9451667) B9451667
theorem B38365721 : Blo 1659529 38365721 := bstep (se 2 (by rfl) ⟨14387145, by rfl⟩ : syracuseStep 38365721 = 28774291) B28774291
theorem B10645019 : Blo 1659529 10645019 := bstep (se 1 (by rfl) ⟨7983764, by rfl⟩ : syracuseStep 10645019 = 15967529) B15967529
theorem B13463327 : Blo 1659529 13463327 := bstep (se 1 (by rfl) ⟨10097495, by rfl⟩ : syracuseStep 13463327 = 20194991) B20194991
theorem B30298175 : Blo 1659529 30298175 := bstep (se 1 (by rfl) ⟨22723631, by rfl⟩ : syracuseStep 30298175 = 45447263) B45447263
theorem B7090391 : Blo 1659529 7090391 := bstep (se 1 (by rfl) ⟨5317793, by rfl⟩ : syracuseStep 7090391 = 10635587) B10635587
theorem B5984999 : Blo 1659529 5984999 := bstep (se 1 (by rfl) ⟨4488749, by rfl⟩ : syracuseStep 5984999 = 8977499) B8977499
theorem B1659679 : Blo 1659529 1659679 := bstep (se 1 (by rfl) ⟨1244759, by rfl⟩ : syracuseStep 1659679 = 2489519) B2489519
theorem B1660443 : Blo 1659529 1660443 := bstep (se 1 (by rfl) ⟨1245332, by rfl⟩ : syracuseStep 1660443 = 2490665) B2490665
theorem B8410715 : Blo 1659529 8410715 := bstep (se 1 (by rfl) ⟨6308036, by rfl⟩ : syracuseStep 8410715 = 12616073) B12616073
theorem B1660927 : Blo 1659529 1660927 := bstep (se 1 (by rfl) ⟨1245695, by rfl⟩ : syracuseStep 1660927 = 2491391) B2491391
theorem B13129783 : Blo 1659529 13129783 := bstep (se 1 (by rfl) ⟨9847337, by rfl⟩ : syracuseStep 13129783 = 19694675) B19694675
theorem B8403263 : Blo 1659529 8403263 := bstep (se 1 (by rfl) ⟨6302447, by rfl⟩ : syracuseStep 8403263 = 12604895) B12604895
theorem B8977063 : Blo 1659529 8977063 := bstep (se 1 (by rfl) ⟨6732797, by rfl⟩ : syracuseStep 8977063 = 13465595) B13465595
theorem B3734369 : Blo 1659529 3734369 := bstep (se 2 (by rfl) ⟨1400388, by rfl⟩ : syracuseStep 3734369 = 2800777) B2800777
theorem B14179211 : Blo 1659529 14179211 := bstep (se 1 (by rfl) ⟨10634408, by rfl⟩ : syracuseStep 14179211 = 21268817) B21268817
theorem B4201703 : Blo 1659529 4201703 := bstep (se 1 (by rfl) ⟨3151277, by rfl⟩ : syracuseStep 4201703 = 6302555) B6302555
theorem B6307247 : Blo 1659529 6307247 := bstep (se 1 (by rfl) ⟨4730435, by rfl⟩ : syracuseStep 6307247 = 9460871) B9460871
theorem B9477827 : Blo 1659529 9477827 := bstep (se 1 (by rfl) ⟨7108370, by rfl⟩ : syracuseStep 9477827 = 14216741) B14216741
theorem B4726927 : Blo 1659529 4726927 := bstep (se 1 (by rfl) ⟨3545195, by rfl⟩ : syracuseStep 4726927 = 7090391) B7090391
theorem B2490527 : Blo 1659529 2490527 := bstep (se 1 (by rfl) ⟨1867895, by rfl⟩ : syracuseStep 2490527 = 3735791) B3735791
theorem B70025509 : Blo 1659529 70025509 := bstep (se 4 (by rfl) ⟨6564891, by rfl⟩ : syracuseStep 70025509 = 13129783) B13129783
theorem B10633639 : Blo 1659529 10633639 := bstep (se 1 (by rfl) ⟨7975229, by rfl⟩ : syracuseStep 10633639 = 15950459) B15950459
theorem B3989999 : Blo 1659529 3989999 := bstep (se 1 (by rfl) ⟨2992499, by rfl⟩ : syracuseStep 3989999 = 5984999) B5984999
theorem B11969417 : Blo 1659529 11969417 := bstep (se 2 (by rfl) ⟨4488531, by rfl⟩ : syracuseStep 11969417 = 8977063) B8977063
theorem B25577147 : Blo 1659529 25577147 := bstep (se 1 (by rfl) ⟨19182860, by rfl⟩ : syracuseStep 25577147 = 38365721) B38365721
theorem B4204831 : Blo 1659529 4204831 := bstep (se 1 (by rfl) ⟨3153623, by rfl⟩ : syracuseStep 4204831 = 6307247) B6307247
theorem B7096679 : Blo 1659529 7096679 := bstep (se 1 (by rfl) ⟨5322509, by rfl⟩ : syracuseStep 7096679 = 10645019) B10645019
theorem B6318551 : Blo 1659529 6318551 := bstep (se 1 (by rfl) ⟨4738913, by rfl⟩ : syracuseStep 6318551 = 9477827) B9477827
theorem B5607143 : Blo 1659529 5607143 := bstep (se 1 (by rfl) ⟨4205357, by rfl⟩ : syracuseStep 5607143 = 8410715) B8410715
theorem B8401481 : Blo 1659529 8401481 := bstep (se 2 (by rfl) ⟨3150555, by rfl⟩ : syracuseStep 8401481 = 6301111) B6301111
theorem B8975551 : Blo 1659529 8975551 := bstep (se 1 (by rfl) ⟨6731663, by rfl⟩ : syracuseStep 8975551 = 13463327) B13463327
theorem B20198783 : Blo 1659529 20198783 := bstep (se 1 (by rfl) ⟨15149087, by rfl⟩ : syracuseStep 20198783 = 30298175) B30298175
theorem B1660775 : Blo 1659529 1660775 := bstep (se 1 (by rfl) ⟨1245581, by rfl⟩ : syracuseStep 1660775 = 2491163) B2491163
theorem B17946515 : Blo 1659529 17946515 := bstep (se 1 (by rfl) ⟨13459886, by rfl⟩ : syracuseStep 17946515 = 26919773) B26919773
theorem B3987443 : Blo 1659529 3987443 := bstep (se 1 (by rfl) ⟨2990582, by rfl⟩ : syracuseStep 3987443 = 5981165) B5981165
theorem B1661179 : Blo 1659529 1661179 := bstep (se 1 (by rfl) ⟨1245884, by rfl⟩ : syracuseStep 1661179 = 2491769) B2491769
theorem B5602175 : Blo 1659529 5602175 := bstep (se 1 (by rfl) ⟨4201631, by rfl⟩ : syracuseStep 5602175 = 8403263) B8403263
theorem B2489579 : Blo 1659529 2489579 := bstep (se 1 (by rfl) ⟨1867184, by rfl⟩ : syracuseStep 2489579 = 3734369) B3734369
theorem B9452807 : Blo 1659529 9452807 := bstep (se 1 (by rfl) ⟨7089605, by rfl⟩ : syracuseStep 9452807 = 14179211) B14179211
theorem B2801135 : Blo 1659529 2801135 := bstep (se 1 (by rfl) ⟨2100851, by rfl⟩ : syracuseStep 2801135 = 4201703) B4201703
theorem B4212367 : Blo 1659529 4212367 := bstep (se 1 (by rfl) ⟨3159275, by rfl⟩ : syracuseStep 4212367 = 6318551) B6318551
theorem B6301871 : Blo 1659529 6301871 := bstep (se 1 (by rfl) ⟨4726403, by rfl⟩ : syracuseStep 6301871 = 9452807) B9452807
theorem B31918445 : Blo 1659529 31918445 := bstep (se 3 (by rfl) ⟨5984708, by rfl⟩ : syracuseStep 31918445 = 11969417) B11969417
theorem B3738095 : Blo 1659529 3738095 := bstep (se 1 (by rfl) ⟨2803571, by rfl⟩ : syracuseStep 3738095 = 5607143) B5607143
theorem B6302569 : Blo 1659529 6302569 := bstep (se 2 (by rfl) ⟨2363463, by rfl⟩ : syracuseStep 6302569 = 4726927) B4726927
theorem B5606441 : Blo 1659529 5606441 := bstep (se 2 (by rfl) ⟨2102415, by rfl⟩ : syracuseStep 5606441 = 4204831) B4204831
theorem B93367345 : Blo 1659529 93367345 := bstep (se 2 (by rfl) ⟨35012754, by rfl⟩ : syracuseStep 93367345 = 70025509) B70025509
theorem B17051431 : Blo 1659529 17051431 := bstep (se 1 (by rfl) ⟨12788573, by rfl⟩ : syracuseStep 17051431 = 25577147) B25577147
theorem B11964343 : Blo 1659529 11964343 := bstep (se 1 (by rfl) ⟨8973257, by rfl⟩ : syracuseStep 11964343 = 17946515) B17946515
theorem B2658295 : Blo 1659529 2658295 := bstep (se 1 (by rfl) ⟨1993721, by rfl⟩ : syracuseStep 2658295 = 3987443) B3987443
theorem B4731119 : Blo 1659529 4731119 := bstep (se 1 (by rfl) ⟨3548339, by rfl⟩ : syracuseStep 4731119 = 7096679) B7096679
theorem B1659719 : Blo 1659529 1659719 := bstep (se 1 (by rfl) ⟨1244789, by rfl⟩ : syracuseStep 1659719 = 2489579) B2489579
theorem B1660351 : Blo 1659529 1660351 := bstep (se 1 (by rfl) ⟨1245263, by rfl⟩ : syracuseStep 1660351 = 2490527) B2490527
theorem B5600987 : Blo 1659529 5600987 := bstep (se 1 (by rfl) ⟨4200740, by rfl⟩ : syracuseStep 5600987 = 8401481) B8401481
theorem B14178185 : Blo 1659529 14178185 := bstep (se 2 (by rfl) ⟨5316819, by rfl⟩ : syracuseStep 14178185 = 10633639) B10633639
theorem B13465855 : Blo 1659529 13465855 := bstep (se 1 (by rfl) ⟨10099391, by rfl⟩ : syracuseStep 13465855 = 20198783) B20198783
theorem B10639997 : Blo 1659529 10639997 := bstep (se 3 (by rfl) ⟨1994999, by rfl⟩ : syracuseStep 10639997 = 3989999) B3989999
theorem B11967401 : Blo 1659529 11967401 := bstep (se 2 (by rfl) ⟨4487775, by rfl⟩ : syracuseStep 11967401 = 8975551) B8975551
theorem B3734783 : Blo 1659529 3734783 := bstep (se 1 (by rfl) ⟨2801087, by rfl⟩ : syracuseStep 3734783 = 5602175) B5602175
theorem B1867423 : Blo 1659529 1867423 := bstep (se 1 (by rfl) ⟨1400567, by rfl⟩ : syracuseStep 1867423 = 2801135) B2801135
theorem B3154079 : Blo 1659529 3154079 := bstep (se 1 (by rfl) ⟨2365559, by rfl⟩ : syracuseStep 3154079 = 4731119) B4731119
theorem B2492063 : Blo 1659529 2492063 := bstep (se 1 (by rfl) ⟨1869047, by rfl⟩ : syracuseStep 2492063 = 3738095) B3738095
theorem B3737627 : Blo 1659529 3737627 := bstep (se 1 (by rfl) ⟨2803220, by rfl⟩ : syracuseStep 3737627 = 5606441) B5606441
theorem B22735241 : Blo 1659529 22735241 := bstep (se 2 (by rfl) ⟨8525715, by rfl⟩ : syracuseStep 22735241 = 17051431) B17051431
theorem B15952457 : Blo 1659529 15952457 := bstep (se 2 (by rfl) ⟨5982171, by rfl⟩ : syracuseStep 15952457 = 11964343) B11964343
theorem B22465957 : Blo 1659529 22465957 := bstep (se 4 (by rfl) ⟨2106183, by rfl⟩ : syracuseStep 22465957 = 4212367) B4212367
theorem B124489793 : Blo 1659529 124489793 := bstep (se 2 (by rfl) ⟨46683672, by rfl⟩ : syracuseStep 124489793 = 93367345) B93367345
theorem B21278963 : Blo 1659529 21278963 := bstep (se 1 (by rfl) ⟨15959222, by rfl⟩ : syracuseStep 21278963 = 31918445) B31918445
theorem B3544393 : Blo 1659529 3544393 := bstep (se 2 (by rfl) ⟨1329147, by rfl⟩ : syracuseStep 3544393 = 2658295) B2658295
theorem B17954473 : Blo 1659529 17954473 := bstep (se 2 (by rfl) ⟨6732927, by rfl⟩ : syracuseStep 17954473 = 13465855) B13465855
theorem B8403425 : Blo 1659529 8403425 := bstep (se 2 (by rfl) ⟨3151284, by rfl⟩ : syracuseStep 8403425 = 6302569) B6302569
theorem B3733991 : Blo 1659529 3733991 := bstep (se 1 (by rfl) ⟨2800493, by rfl⟩ : syracuseStep 3733991 = 5600987) B5600987
theorem B9452123 : Blo 1659529 9452123 := bstep (se 1 (by rfl) ⟨7089092, by rfl⟩ : syracuseStep 9452123 = 14178185) B14178185
theorem B4201247 : Blo 1659529 4201247 := bstep (se 1 (by rfl) ⟨3150935, by rfl⟩ : syracuseStep 4201247 = 6301871) B6301871
theorem B7093331 : Blo 1659529 7093331 := bstep (se 1 (by rfl) ⟨5319998, by rfl⟩ : syracuseStep 7093331 = 10639997) B10639997
theorem B7978267 : Blo 1659529 7978267 := bstep (se 1 (by rfl) ⟨5983700, by rfl⟩ : syracuseStep 7978267 = 11967401) B11967401
theorem B2489855 : Blo 1659529 2489855 := bstep (se 1 (by rfl) ⟨1867391, by rfl⟩ : syracuseStep 2489855 = 3734783) B3734783
theorem B2489897 : Blo 1659529 2489897 := bstep (se 2 (by rfl) ⟨933711, by rfl⟩ : syracuseStep 2489897 = 1867423) B1867423
theorem B82993195 : Blo 1659529 82993195 := bstep (se 1 (by rfl) ⟨62244896, by rfl⟩ : syracuseStep 82993195 = 124489793) B124489793
theorem B2491751 : Blo 1659529 2491751 := bstep (se 1 (by rfl) ⟨1868813, by rfl⟩ : syracuseStep 2491751 = 3737627) B3737627
theorem B15156827 : Blo 1659529 15156827 := bstep (se 1 (by rfl) ⟨11367620, by rfl⟩ : syracuseStep 15156827 = 22735241) B22735241
theorem B10634971 : Blo 1659529 10634971 := bstep (se 1 (by rfl) ⟨7976228, by rfl⟩ : syracuseStep 10634971 = 15952457) B15952457
theorem B6301415 : Blo 1659529 6301415 := bstep (se 1 (by rfl) ⟨4726061, by rfl⟩ : syracuseStep 6301415 = 9452123) B9452123
theorem B4728887 : Blo 1659529 4728887 := bstep (se 1 (by rfl) ⟨3546665, by rfl⟩ : syracuseStep 4728887 = 7093331) B7093331
theorem B23939297 : Blo 1659529 23939297 := bstep (se 2 (by rfl) ⟨8977236, by rfl⟩ : syracuseStep 23939297 = 17954473) B17954473
theorem B10637689 : Blo 1659529 10637689 := bstep (se 2 (by rfl) ⟨3989133, by rfl⟩ : syracuseStep 10637689 = 7978267) B7978267
theorem B29954609 : Blo 1659529 29954609 := bstep (se 2 (by rfl) ⟨11232978, by rfl⟩ : syracuseStep 29954609 = 22465957) B22465957
theorem B1659903 : Blo 1659529 1659903 := bstep (se 1 (by rfl) ⟨1244927, by rfl⟩ : syracuseStep 1659903 = 2489855) B2489855
theorem B1659931 : Blo 1659529 1659931 := bstep (se 1 (by rfl) ⟨1244948, by rfl⟩ : syracuseStep 1659931 = 2489897) B2489897
theorem B14185975 : Blo 1659529 14185975 := bstep (se 1 (by rfl) ⟨10639481, by rfl⟩ : syracuseStep 14185975 = 21278963) B21278963
theorem B8410877 : Blo 1659529 8410877 := bstep (se 3 (by rfl) ⟨1577039, by rfl⟩ : syracuseStep 8410877 = 3154079) B3154079
theorem B1661375 : Blo 1659529 1661375 := bstep (se 1 (by rfl) ⟨1246031, by rfl⟩ : syracuseStep 1661375 = 2492063) B2492063
theorem B5602283 : Blo 1659529 5602283 := bstep (se 1 (by rfl) ⟨4201712, by rfl⟩ : syracuseStep 5602283 = 8403425) B8403425
theorem B2489327 : Blo 1659529 2489327 := bstep (se 1 (by rfl) ⟨1866995, by rfl⟩ : syracuseStep 2489327 = 3733991) B3733991
theorem B4725857 : Blo 1659529 4725857 := bstep (se 2 (by rfl) ⟨1772196, by rfl⟩ : syracuseStep 4725857 = 3544393) B3544393
theorem B2800831 : Blo 1659529 2800831 := bstep (se 1 (by rfl) ⟨2100623, by rfl⟩ : syracuseStep 2800831 = 4201247) B4201247
theorem B110657593 : Blo 1659529 110657593 := bstep (se 2 (by rfl) ⟨41496597, by rfl⟩ : syracuseStep 110657593 = 82993195) B82993195
theorem B15959531 : Blo 1659529 15959531 := bstep (se 1 (by rfl) ⟨11969648, by rfl⟩ : syracuseStep 15959531 = 23939297) B23939297
theorem B14183585 : Blo 1659529 14183585 := bstep (se 2 (by rfl) ⟨5318844, by rfl⟩ : syracuseStep 14183585 = 10637689) B10637689
theorem B10104551 : Blo 1659529 10104551 := bstep (se 1 (by rfl) ⟨7578413, by rfl⟩ : syracuseStep 10104551 = 15156827) B15156827
theorem B5607251 : Blo 1659529 5607251 := bstep (se 1 (by rfl) ⟨4205438, by rfl⟩ : syracuseStep 5607251 = 8410877) B8410877
theorem B1659551 : Blo 1659529 1659551 := bstep (se 1 (by rfl) ⟨1244663, by rfl⟩ : syracuseStep 1659551 = 2489327) B2489327
theorem B3150571 : Blo 1659529 3150571 := bstep (se 1 (by rfl) ⟨2362928, by rfl⟩ : syracuseStep 3150571 = 4725857) B4725857
theorem B19969739 : Blo 1659529 19969739 := bstep (se 1 (by rfl) ⟨14977304, by rfl⟩ : syracuseStep 19969739 = 29954609) B29954609
theorem B1661167 : Blo 1659529 1661167 := bstep (se 1 (by rfl) ⟨1245875, by rfl⟩ : syracuseStep 1661167 = 2491751) B2491751
theorem B4200943 : Blo 1659529 4200943 := bstep (se 1 (by rfl) ⟨3150707, by rfl⟩ : syracuseStep 4200943 = 6301415) B6301415
theorem B3152591 : Blo 1659529 3152591 := bstep (se 1 (by rfl) ⟨2364443, by rfl⟩ : syracuseStep 3152591 = 4728887) B4728887
theorem B3734441 : Blo 1659529 3734441 := bstep (se 2 (by rfl) ⟨1400415, by rfl⟩ : syracuseStep 3734441 = 2800831) B2800831
theorem B3734855 : Blo 1659529 3734855 := bstep (se 1 (by rfl) ⟨2801141, by rfl⟩ : syracuseStep 3734855 = 5602283) B5602283
theorem B18914633 : Blo 1659529 18914633 := bstep (se 2 (by rfl) ⟨7092987, by rfl⟩ : syracuseStep 18914633 = 14185975) B14185975
theorem B14179961 : Blo 1659529 14179961 := bstep (se 2 (by rfl) ⟨5317485, by rfl⟩ : syracuseStep 14179961 = 10634971) B10634971
theorem B13313159 : Blo 1659529 13313159 := bstep (se 1 (by rfl) ⟨9984869, by rfl⟩ : syracuseStep 13313159 = 19969739) B19969739
theorem B9455723 : Blo 1659529 9455723 := bstep (se 1 (by rfl) ⟨7091792, by rfl⟩ : syracuseStep 9455723 = 14183585) B14183585
theorem B12609755 : Blo 1659529 12609755 := bstep (se 1 (by rfl) ⟨9457316, by rfl⟩ : syracuseStep 12609755 = 18914633) B18914633
theorem B6736367 : Blo 1659529 6736367 := bstep (se 1 (by rfl) ⟨5052275, by rfl⟩ : syracuseStep 6736367 = 10104551) B10104551
theorem B3738167 : Blo 1659529 3738167 := bstep (se 1 (by rfl) ⟨2803625, by rfl⟩ : syracuseStep 3738167 = 5607251) B5607251
theorem B2101727 : Blo 1659529 2101727 := bstep (se 1 (by rfl) ⟨1576295, by rfl⟩ : syracuseStep 2101727 = 3152591) B3152591
theorem B147543457 : Blo 1659529 147543457 := bstep (se 2 (by rfl) ⟨55328796, by rfl⟩ : syracuseStep 147543457 = 110657593) B110657593
theorem B5601257 : Blo 1659529 5601257 := bstep (se 2 (by rfl) ⟨2100471, by rfl⟩ : syracuseStep 5601257 = 4200943) B4200943
theorem B4200761 : Blo 1659529 4200761 := bstep (se 2 (by rfl) ⟨1575285, by rfl⟩ : syracuseStep 4200761 = 3150571) B3150571
theorem B10639687 : Blo 1659529 10639687 := bstep (se 1 (by rfl) ⟨7979765, by rfl⟩ : syracuseStep 10639687 = 15959531) B15959531
theorem B2489627 : Blo 1659529 2489627 := bstep (se 1 (by rfl) ⟨1867220, by rfl⟩ : syracuseStep 2489627 = 3734441) B3734441
theorem B2489903 : Blo 1659529 2489903 := bstep (se 1 (by rfl) ⟨1867427, by rfl⟩ : syracuseStep 2489903 = 3734855) B3734855
theorem B9453307 : Blo 1659529 9453307 := bstep (se 1 (by rfl) ⟨7089980, by rfl⟩ : syracuseStep 9453307 = 14179961) B14179961
theorem B5604605 : Blo 1659529 5604605 := bstep (se 3 (by rfl) ⟨1050863, by rfl⟩ : syracuseStep 5604605 = 2101727) B2101727
theorem B8406503 : Blo 1659529 8406503 := bstep (se 1 (by rfl) ⟨6304877, by rfl⟩ : syracuseStep 8406503 = 12609755) B12609755
theorem B4490911 : Blo 1659529 4490911 := bstep (se 1 (by rfl) ⟨3368183, by rfl⟩ : syracuseStep 4490911 = 6736367) B6736367
theorem B2492111 : Blo 1659529 2492111 := bstep (se 1 (by rfl) ⟨1869083, by rfl⟩ : syracuseStep 2492111 = 3738167) B3738167
theorem B196724609 : Blo 1659529 196724609 := bstep (se 2 (by rfl) ⟨73771728, by rfl⟩ : syracuseStep 196724609 = 147543457) B147543457
theorem B8875439 : Blo 1659529 8875439 := bstep (se 1 (by rfl) ⟨6656579, by rfl⟩ : syracuseStep 8875439 = 13313159) B13313159
theorem B6303815 : Blo 1659529 6303815 := bstep (se 1 (by rfl) ⟨4727861, by rfl⟩ : syracuseStep 6303815 = 9455723) B9455723
theorem B1659751 : Blo 1659529 1659751 := bstep (se 1 (by rfl) ⟨1244813, by rfl⟩ : syracuseStep 1659751 = 2489627) B2489627
theorem B12604409 : Blo 1659529 12604409 := bstep (se 2 (by rfl) ⟨4726653, by rfl⟩ : syracuseStep 12604409 = 9453307) B9453307
theorem B1659935 : Blo 1659529 1659935 := bstep (se 1 (by rfl) ⟨1244951, by rfl⟩ : syracuseStep 1659935 = 2489903) B2489903
theorem B14186249 : Blo 1659529 14186249 := bstep (se 2 (by rfl) ⟨5319843, by rfl⟩ : syracuseStep 14186249 = 10639687) B10639687
theorem B3734171 : Blo 1659529 3734171 := bstep (se 1 (by rfl) ⟨2800628, by rfl⟩ : syracuseStep 3734171 = 5601257) B5601257
theorem B2800507 : Blo 1659529 2800507 := bstep (se 1 (by rfl) ⟨2100380, by rfl⟩ : syracuseStep 2800507 = 4200761) B4200761
theorem B4202543 : Blo 1659529 4202543 := bstep (se 1 (by rfl) ⟨3151907, by rfl⟩ : syracuseStep 4202543 = 6303815) B6303815
theorem B3736403 : Blo 1659529 3736403 := bstep (se 1 (by rfl) ⟨2802302, by rfl⟩ : syracuseStep 3736403 = 5604605) B5604605
theorem B5604335 : Blo 1659529 5604335 := bstep (se 1 (by rfl) ⟨4203251, by rfl⟩ : syracuseStep 5604335 = 8406503) B8406503
theorem B5916959 : Blo 1659529 5916959 := bstep (se 1 (by rfl) ⟨4437719, by rfl⟩ : syracuseStep 5916959 = 8875439) B8875439
theorem B9457499 : Blo 1659529 9457499 := bstep (se 1 (by rfl) ⟨7093124, by rfl⟩ : syracuseStep 9457499 = 14186249) B14186249
theorem B131149739 : Blo 1659529 131149739 := bstep (se 1 (by rfl) ⟨98362304, by rfl⟩ : syracuseStep 131149739 = 196724609) B196724609
theorem B8402939 : Blo 1659529 8402939 := bstep (se 1 (by rfl) ⟨6302204, by rfl⟩ : syracuseStep 8402939 = 12604409) B12604409
theorem B1661407 : Blo 1659529 1661407 := bstep (se 1 (by rfl) ⟨1246055, by rfl⟩ : syracuseStep 1661407 = 2492111) B2492111
theorem B3734009 : Blo 1659529 3734009 := bstep (se 2 (by rfl) ⟨1400253, by rfl⟩ : syracuseStep 3734009 = 2800507) B2800507
theorem B2489447 : Blo 1659529 2489447 := bstep (se 1 (by rfl) ⟨1867085, by rfl⟩ : syracuseStep 2489447 = 3734171) B3734171
theorem B5987881 : Blo 1659529 5987881 := bstep (se 2 (by rfl) ⟨2245455, by rfl⟩ : syracuseStep 5987881 = 4490911) B4490911
theorem B2801695 : Blo 1659529 2801695 := bstep (se 1 (by rfl) ⟨2101271, by rfl⟩ : syracuseStep 2801695 = 4202543) B4202543
theorem B2490935 : Blo 1659529 2490935 := bstep (se 1 (by rfl) ⟨1868201, by rfl⟩ : syracuseStep 2490935 = 3736403) B3736403
theorem B3736223 : Blo 1659529 3736223 := bstep (se 1 (by rfl) ⟨2802167, by rfl⟩ : syracuseStep 3736223 = 5604335) B5604335
theorem B3944639 : Blo 1659529 3944639 := bstep (se 1 (by rfl) ⟨2958479, by rfl⟩ : syracuseStep 3944639 = 5916959) B5916959
theorem B7983841 : Blo 1659529 7983841 := bstep (se 2 (by rfl) ⟨2993940, by rfl⟩ : syracuseStep 7983841 = 5987881) B5987881
theorem B1659631 : Blo 1659529 1659631 := bstep (se 1 (by rfl) ⟨1244723, by rfl⟩ : syracuseStep 1659631 = 2489447) B2489447
theorem B6304999 : Blo 1659529 6304999 := bstep (se 1 (by rfl) ⟨4728749, by rfl⟩ : syracuseStep 6304999 = 9457499) B9457499
theorem B5601959 : Blo 1659529 5601959 := bstep (se 1 (by rfl) ⟨4201469, by rfl⟩ : syracuseStep 5601959 = 8402939) B8402939
theorem B2489339 : Blo 1659529 2489339 := bstep (se 1 (by rfl) ⟨1867004, by rfl⟩ : syracuseStep 2489339 = 3734009) B3734009
theorem B349732637 : Blo 1659529 349732637 := bstep (se 3 (by rfl) ⟨65574869, by rfl⟩ : syracuseStep 349732637 = 131149739) B131149739
theorem B3735593 : Blo 1659529 3735593 := bstep (se 2 (by rfl) ⟨1400847, by rfl⟩ : syracuseStep 3735593 = 2801695) B2801695
theorem B2629759 : Blo 1659529 2629759 := bstep (se 1 (by rfl) ⟨1972319, by rfl⟩ : syracuseStep 2629759 = 3944639) B3944639
theorem B2490815 : Blo 1659529 2490815 := bstep (se 1 (by rfl) ⟨1868111, by rfl⟩ : syracuseStep 2490815 = 3736223) B3736223
theorem B8406665 : Blo 1659529 8406665 := bstep (se 2 (by rfl) ⟨3152499, by rfl⟩ : syracuseStep 8406665 = 6304999) B6304999
theorem B233155091 : Blo 1659529 233155091 := bstep (se 1 (by rfl) ⟨174866318, by rfl⟩ : syracuseStep 233155091 = 349732637) B349732637
theorem B10645121 : Blo 1659529 10645121 := bstep (se 2 (by rfl) ⟨3991920, by rfl⟩ : syracuseStep 10645121 = 7983841) B7983841
theorem B1659559 : Blo 1659529 1659559 := bstep (se 1 (by rfl) ⟨1244669, by rfl⟩ : syracuseStep 1659559 = 2489339) B2489339
theorem B1660623 : Blo 1659529 1660623 := bstep (se 1 (by rfl) ⟨1245467, by rfl⟩ : syracuseStep 1660623 = 2490935) B2490935
theorem B3734639 : Blo 1659529 3734639 := bstep (se 1 (by rfl) ⟨2800979, by rfl⟩ : syracuseStep 3734639 = 5601959) B5601959
theorem B2490395 : Blo 1659529 2490395 := bstep (se 1 (by rfl) ⟨1867796, by rfl⟩ : syracuseStep 2490395 = 3735593) B3735593
theorem B3506345 : Blo 1659529 3506345 := bstep (se 2 (by rfl) ⟨1314879, by rfl⟩ : syracuseStep 3506345 = 2629759) B2629759
theorem B5604443 : Blo 1659529 5604443 := bstep (se 1 (by rfl) ⟨4203332, by rfl⟩ : syracuseStep 5604443 = 8406665) B8406665
theorem B155436727 : Blo 1659529 155436727 := bstep (se 1 (by rfl) ⟨116577545, by rfl⟩ : syracuseStep 155436727 = 233155091) B233155091
theorem B7096747 : Blo 1659529 7096747 := bstep (se 1 (by rfl) ⟨5322560, by rfl⟩ : syracuseStep 7096747 = 10645121) B10645121
theorem B1660543 : Blo 1659529 1660543 := bstep (se 1 (by rfl) ⟨1245407, by rfl⟩ : syracuseStep 1660543 = 2490815) B2490815
theorem B2489759 : Blo 1659529 2489759 := bstep (se 1 (by rfl) ⟨1867319, by rfl⟩ : syracuseStep 2489759 = 3734639) B3734639
theorem B9462329 : Blo 1659529 9462329 := bstep (se 2 (by rfl) ⟨3548373, by rfl⟩ : syracuseStep 9462329 = 7096747) B7096747
theorem B3736295 : Blo 1659529 3736295 := bstep (se 1 (by rfl) ⟨2802221, by rfl⟩ : syracuseStep 3736295 = 5604443) B5604443
theorem B2337563 : Blo 1659529 2337563 := bstep (se 1 (by rfl) ⟨1753172, by rfl⟩ : syracuseStep 2337563 = 3506345) B3506345
theorem B1659839 : Blo 1659529 1659839 := bstep (se 1 (by rfl) ⟨1244879, by rfl⟩ : syracuseStep 1659839 = 2489759) B2489759
theorem B1660263 : Blo 1659529 1660263 := bstep (se 1 (by rfl) ⟨1245197, by rfl⟩ : syracuseStep 1660263 = 2490395) B2490395
theorem B207248969 : Blo 1659529 207248969 := bstep (se 2 (by rfl) ⟨77718363, by rfl⟩ : syracuseStep 207248969 = 155436727) B155436727
theorem B6308219 : Blo 1659529 6308219 := bstep (se 1 (by rfl) ⟨4731164, by rfl⟩ : syracuseStep 6308219 = 9462329) B9462329
theorem B2490863 : Blo 1659529 2490863 := bstep (se 1 (by rfl) ⟨1868147, by rfl⟩ : syracuseStep 2490863 = 3736295) B3736295
theorem B6233501 : Blo 1659529 6233501 := bstep (se 3 (by rfl) ⟨1168781, by rfl⟩ : syracuseStep 6233501 = 2337563) B2337563
theorem B138165979 : Blo 1659529 138165979 := bstep (se 1 (by rfl) ⟨103624484, by rfl⟩ : syracuseStep 138165979 = 207248969) B207248969
theorem B16622669 : Blo 1659529 16622669 := bstep (se 3 (by rfl) ⟨3116750, by rfl⟩ : syracuseStep 16622669 = 6233501) B6233501
theorem B4205479 : Blo 1659529 4205479 := bstep (se 1 (by rfl) ⟨3154109, by rfl⟩ : syracuseStep 4205479 = 6308219) B6308219
theorem B1660575 : Blo 1659529 1660575 := bstep (se 1 (by rfl) ⟨1245431, by rfl⟩ : syracuseStep 1660575 = 2490863) B2490863
theorem B184221305 : Blo 1659529 184221305 := bstep (se 2 (by rfl) ⟨69082989, by rfl⟩ : syracuseStep 184221305 = 138165979) B138165979
theorem B5607305 : Blo 1659529 5607305 := bstep (se 2 (by rfl) ⟨2102739, by rfl⟩ : syracuseStep 5607305 = 4205479) B4205479
theorem B11081779 : Blo 1659529 11081779 := bstep (se 1 (by rfl) ⟨8311334, by rfl⟩ : syracuseStep 11081779 = 16622669) B16622669
theorem B122814203 : Blo 1659529 122814203 := bstep (se 1 (by rfl) ⟨92110652, by rfl⟩ : syracuseStep 122814203 = 184221305) B184221305
theorem B3738203 : Blo 1659529 3738203 := bstep (se 1 (by rfl) ⟨2803652, by rfl⟩ : syracuseStep 3738203 = 5607305) B5607305
theorem B327504541 : Blo 1659529 327504541 := bstep (se 3 (by rfl) ⟨61407101, by rfl⟩ : syracuseStep 327504541 = 122814203) B122814203
theorem B59102821 : Blo 1659529 59102821 := bstep (se 4 (by rfl) ⟨5540889, by rfl⟩ : syracuseStep 59102821 = 11081779) B11081779
theorem B2492135 : Blo 1659529 2492135 := bstep (se 1 (by rfl) ⟨1869101, by rfl⟩ : syracuseStep 2492135 = 3738203) B3738203
theorem B78803761 : Blo 1659529 78803761 := bstep (se 2 (by rfl) ⟨29551410, by rfl⟩ : syracuseStep 78803761 = 59102821) B59102821
theorem B436672721 : Blo 1659529 436672721 := bstep (se 2 (by rfl) ⟨163752270, by rfl⟩ : syracuseStep 436672721 = 327504541) B327504541
theorem B105071681 : Blo 1659529 105071681 := bstep (se 2 (by rfl) ⟨39401880, by rfl⟩ : syracuseStep 105071681 = 78803761) B78803761
theorem B291115147 : Blo 1659529 291115147 := bstep (se 1 (by rfl) ⟨218336360, by rfl⟩ : syracuseStep 291115147 = 436672721) B436672721
theorem B1661423 : Blo 1659529 1661423 := bstep (se 1 (by rfl) ⟨1246067, by rfl⟩ : syracuseStep 1661423 = 2492135) B2492135
theorem B280191149 : Blo 1659529 280191149 := bstep (se 3 (by rfl) ⟨52535840, by rfl⟩ : syracuseStep 280191149 = 105071681) B105071681
theorem B388153529 : Blo 1659529 388153529 := bstep (se 2 (by rfl) ⟨145557573, by rfl⟩ : syracuseStep 388153529 = 291115147) B291115147
theorem B186794099 : Blo 1659529 186794099 := bstep (se 1 (by rfl) ⟨140095574, by rfl⟩ : syracuseStep 186794099 = 280191149) B280191149
theorem B258769019 : Blo 1659529 258769019 := bstep (se 1 (by rfl) ⟨194076764, by rfl⟩ : syracuseStep 258769019 = 388153529) B388153529
theorem B124529399 : Blo 1659529 124529399 := bstep (se 1 (by rfl) ⟨93397049, by rfl⟩ : syracuseStep 124529399 = 186794099) B186794099
theorem B172512679 : Blo 1659529 172512679 := bstep (se 1 (by rfl) ⟨129384509, by rfl⟩ : syracuseStep 172512679 = 258769019) B258769019
theorem B83019599 : Blo 1659529 83019599 := bstep (se 1 (by rfl) ⟨62264699, by rfl⟩ : syracuseStep 83019599 = 124529399) B124529399
theorem B230016905 : Blo 1659529 230016905 := bstep (se 2 (by rfl) ⟨86256339, by rfl⟩ : syracuseStep 230016905 = 172512679) B172512679
theorem B55346399 : Blo 1659529 55346399 := bstep (se 1 (by rfl) ⟨41509799, by rfl⟩ : syracuseStep 55346399 = 83019599) B83019599
theorem B153344603 : Blo 1659529 153344603 := bstep (se 1 (by rfl) ⟨115008452, by rfl⟩ : syracuseStep 153344603 = 230016905) B230016905
theorem B36897599 : Blo 1659529 36897599 := bstep (se 1 (by rfl) ⟨27673199, by rfl⟩ : syracuseStep 36897599 = 55346399) B55346399
theorem B408918941 : Blo 1659529 408918941 := bstep (se 3 (by rfl) ⟨76672301, by rfl⟩ : syracuseStep 408918941 = 153344603) B153344603
theorem B24598399 : Blo 1659529 24598399 := bstep (se 1 (by rfl) ⟨18448799, by rfl⟩ : syracuseStep 24598399 = 36897599) B36897599
theorem B272612627 : Blo 1659529 272612627 := bstep (se 1 (by rfl) ⟨204459470, by rfl⟩ : syracuseStep 272612627 = 408918941) B408918941
theorem B181741751 : Blo 1659529 181741751 := bstep (se 1 (by rfl) ⟨136306313, by rfl⟩ : syracuseStep 181741751 = 272612627) B272612627
theorem B32797865 : Blo 1659529 32797865 := bstep (se 2 (by rfl) ⟨12299199, by rfl⟩ : syracuseStep 32797865 = 24598399) B24598399
theorem B21865243 : Blo 1659529 21865243 := bstep (se 1 (by rfl) ⟨16398932, by rfl⟩ : syracuseStep 21865243 = 32797865) B32797865
theorem B121161167 : Blo 1659529 121161167 := bstep (se 1 (by rfl) ⟨90870875, by rfl⟩ : syracuseStep 121161167 = 181741751) B181741751
theorem B80774111 : Blo 1659529 80774111 := bstep (se 1 (by rfl) ⟨60580583, by rfl⟩ : syracuseStep 80774111 = 121161167) B121161167
theorem B29153657 : Blo 1659529 29153657 := bstep (se 2 (by rfl) ⟨10932621, by rfl⟩ : syracuseStep 29153657 = 21865243) B21865243
theorem B53849407 : Blo 1659529 53849407 := bstep (se 1 (by rfl) ⟨40387055, by rfl⟩ : syracuseStep 53849407 = 80774111) B80774111
theorem B19435771 : Blo 1659529 19435771 := bstep (se 1 (by rfl) ⟨14576828, by rfl⟩ : syracuseStep 19435771 = 29153657) B29153657
theorem B103657445 : Blo 1659529 103657445 := bstep (se 4 (by rfl) ⟨9717885, by rfl⟩ : syracuseStep 103657445 = 19435771) B19435771
theorem B71799209 : Blo 1659529 71799209 := bstep (se 2 (by rfl) ⟨26924703, by rfl⟩ : syracuseStep 71799209 = 53849407) B53849407
theorem B47866139 : Blo 1659529 47866139 := bstep (se 1 (by rfl) ⟨35899604, by rfl⟩ : syracuseStep 47866139 = 71799209) B71799209
theorem B69104963 : Blo 1659529 69104963 := bstep (se 1 (by rfl) ⟨51828722, by rfl⟩ : syracuseStep 69104963 = 103657445) B103657445
theorem B31910759 : Blo 1659529 31910759 := bstep (se 1 (by rfl) ⟨23933069, by rfl⟩ : syracuseStep 31910759 = 47866139) B47866139
theorem B46069975 : Blo 1659529 46069975 := bstep (se 1 (by rfl) ⟨34552481, by rfl⟩ : syracuseStep 46069975 = 69104963) B69104963
theorem B245706533 : Blo 1659529 245706533 := bstep (se 4 (by rfl) ⟨23034987, by rfl⟩ : syracuseStep 245706533 = 46069975) B46069975
theorem B21273839 : Blo 1659529 21273839 := bstep (se 1 (by rfl) ⟨15955379, by rfl⟩ : syracuseStep 21273839 = 31910759) B31910759
theorem B14182559 : Blo 1659529 14182559 := bstep (se 1 (by rfl) ⟨10636919, by rfl⟩ : syracuseStep 14182559 = 21273839) B21273839
theorem B163804355 : Blo 1659529 163804355 := bstep (se 1 (by rfl) ⟨122853266, by rfl⟩ : syracuseStep 163804355 = 245706533) B245706533
theorem B9455039 : Blo 1659529 9455039 := bstep (se 1 (by rfl) ⟨7091279, by rfl⟩ : syracuseStep 9455039 = 14182559) B14182559
theorem B109202903 : Blo 1659529 109202903 := bstep (se 1 (by rfl) ⟨81902177, by rfl⟩ : syracuseStep 109202903 = 163804355) B163804355
theorem B6303359 : Blo 1659529 6303359 := bstep (se 1 (by rfl) ⟨4727519, by rfl⟩ : syracuseStep 6303359 = 9455039) B9455039
theorem B72801935 : Blo 1659529 72801935 := bstep (se 1 (by rfl) ⟨54601451, by rfl⟩ : syracuseStep 72801935 = 109202903) B109202903
theorem B48534623 : Blo 1659529 48534623 := bstep (se 1 (by rfl) ⟨36400967, by rfl⟩ : syracuseStep 48534623 = 72801935) B72801935
theorem B4202239 : Blo 1659529 4202239 := bstep (se 1 (by rfl) ⟨3151679, by rfl⟩ : syracuseStep 4202239 = 6303359) B6303359
theorem B32356415 : Blo 1659529 32356415 := bstep (se 1 (by rfl) ⟨24267311, by rfl⟩ : syracuseStep 32356415 = 48534623) B48534623
theorem B5602985 : Blo 1659529 5602985 := bstep (se 2 (by rfl) ⟨2101119, by rfl⟩ : syracuseStep 5602985 = 4202239) B4202239
theorem B21570943 : Blo 1659529 21570943 := bstep (se 1 (by rfl) ⟨16178207, by rfl⟩ : syracuseStep 21570943 = 32356415) B32356415
theorem B3735323 : Blo 1659529 3735323 := bstep (se 1 (by rfl) ⟨2801492, by rfl⟩ : syracuseStep 3735323 = 5602985) B5602985
theorem B28761257 : Blo 1659529 28761257 := bstep (se 2 (by rfl) ⟨10785471, by rfl⟩ : syracuseStep 28761257 = 21570943) B21570943
theorem B2490215 : Blo 1659529 2490215 := bstep (se 1 (by rfl) ⟨1867661, by rfl⟩ : syracuseStep 2490215 = 3735323) B3735323
theorem B19174171 : Blo 1659529 19174171 := bstep (se 1 (by rfl) ⟨14380628, by rfl⟩ : syracuseStep 19174171 = 28761257) B28761257
theorem B1660143 : Blo 1659529 1660143 := bstep (se 1 (by rfl) ⟨1245107, by rfl⟩ : syracuseStep 1660143 = 2490215) B2490215
theorem B25565561 : Blo 1659529 25565561 := bstep (se 2 (by rfl) ⟨9587085, by rfl⟩ : syracuseStep 25565561 = 19174171) B19174171
theorem B17043707 : Blo 1659529 17043707 := bstep (se 1 (by rfl) ⟨12782780, by rfl⟩ : syracuseStep 17043707 = 25565561) B25565561
theorem B45449885 : Blo 1659529 45449885 := bstep (se 3 (by rfl) ⟨8521853, by rfl⟩ : syracuseStep 45449885 = 17043707) B17043707
theorem B30299923 : Blo 1659529 30299923 := bstep (se 1 (by rfl) ⟨22724942, by rfl⟩ : syracuseStep 30299923 = 45449885) B45449885
theorem B40399897 : Blo 1659529 40399897 := bstep (se 2 (by rfl) ⟨15149961, by rfl⟩ : syracuseStep 40399897 = 30299923) B30299923
theorem B53866529 : Blo 1659529 53866529 := bstep (se 2 (by rfl) ⟨20199948, by rfl⟩ : syracuseStep 53866529 = 40399897) B40399897
theorem B35911019 : Blo 1659529 35911019 := bstep (se 1 (by rfl) ⟨26933264, by rfl⟩ : syracuseStep 35911019 = 53866529) B53866529
theorem B23940679 : Blo 1659529 23940679 := bstep (se 1 (by rfl) ⟨17955509, by rfl⟩ : syracuseStep 23940679 = 35911019) B35911019
theorem B31920905 : Blo 1659529 31920905 := bstep (se 2 (by rfl) ⟨11970339, by rfl⟩ : syracuseStep 31920905 = 23940679) B23940679
theorem B21280603 : Blo 1659529 21280603 := bstep (se 1 (by rfl) ⟨15960452, by rfl⟩ : syracuseStep 21280603 = 31920905) B31920905
theorem B28374137 : Blo 1659529 28374137 := bstep (se 2 (by rfl) ⟨10640301, by rfl⟩ : syracuseStep 28374137 = 21280603) B21280603
theorem B18916091 : Blo 1659529 18916091 := bstep (se 1 (by rfl) ⟨14187068, by rfl⟩ : syracuseStep 18916091 = 28374137) B28374137
theorem B12610727 : Blo 1659529 12610727 := bstep (se 1 (by rfl) ⟨9458045, by rfl⟩ : syracuseStep 12610727 = 18916091) B18916091
theorem B8407151 : Blo 1659529 8407151 := bstep (se 1 (by rfl) ⟨6305363, by rfl⟩ : syracuseStep 8407151 = 12610727) B12610727
theorem B5604767 : Blo 1659529 5604767 := bstep (se 1 (by rfl) ⟨4203575, by rfl⟩ : syracuseStep 5604767 = 8407151) B8407151
theorem B3736511 : Blo 1659529 3736511 := bstep (se 1 (by rfl) ⟨2802383, by rfl⟩ : syracuseStep 3736511 = 5604767) B5604767
theorem B2491007 : Blo 1659529 2491007 := bstep (se 1 (by rfl) ⟨1868255, by rfl⟩ : syracuseStep 2491007 = 3736511) B3736511
theorem B1660671 : Blo 1659529 1660671 := bstep (se 1 (by rfl) ⟨1245503, by rfl⟩ : syracuseStep 1660671 = 2491007) B2491007

theorem C0 (j : ℕ) (h1 : 414882 ≤ j) (h2 : j ≤ 415381) : Blo 1659529 (4 * j + 3) := by
  interval_cases j
  · exact B1659531
  · exact B1659535
  · exact B1659539
  · exact B1659543
  · exact B1659547
  · exact B1659551
  · exact B1659555
  · exact B1659559
  · exact B1659563
  · exact B1659567
  · exact B1659571
  · exact B1659575
  · exact B1659579
  · exact B1659583
  · exact B1659587
  · exact B1659591
  · exact B1659595
  · exact B1659599
  · exact B1659603
  · exact B1659607
  · exact B1659611
  · exact B1659615
  · exact B1659619
  · exact B1659623
  · exact B1659627
  · exact B1659631
  · exact B1659635
  · exact B1659639
  · exact B1659643
  · exact B1659647
  · exact B1659651
  · exact B1659655
  · exact B1659659
  · exact B1659663
  · exact B1659667
  · exact B1659671
  · exact B1659675
  · exact B1659679
  · exact B1659683
  · exact B1659687
  · exact B1659691
  · exact B1659695
  · exact B1659699
  · exact B1659703
  · exact B1659707
  · exact B1659711
  · exact B1659715
  · exact B1659719
  · exact B1659723
  · exact B1659727
  · exact B1659731
  · exact B1659735
  · exact B1659739
  · exact B1659743
  · exact B1659747
  · exact B1659751
  · exact B1659755
  · exact B1659759
  · exact B1659763
  · exact B1659767
  · exact B1659771
  · exact B1659775
  · exact B1659779
  · exact B1659783
  · exact B1659787
  · exact B1659791
  · exact B1659795
  · exact B1659799
  · exact B1659803
  · exact B1659807
  · exact B1659811
  · exact B1659815
  · exact B1659819
  · exact B1659823
  · exact B1659827
  · exact B1659831
  · exact B1659835
  · exact B1659839
  · exact B1659843
  · exact B1659847
  · exact B1659851
  · exact B1659855
  · exact B1659859
  · exact B1659863
  · exact B1659867
  · exact B1659871
  · exact B1659875
  · exact B1659879
  · exact B1659883
  · exact B1659887
  · exact B1659891
  · exact B1659895
  · exact B1659899
  · exact B1659903
  · exact B1659907
  · exact B1659911
  · exact B1659915
  · exact B1659919
  · exact B1659923
  · exact B1659927
  · exact B1659931
  · exact B1659935
  · exact B1659939
  · exact B1659943
  · exact B1659947
  · exact B1659951
  · exact B1659955
  · exact B1659959
  · exact B1659963
  · exact B1659967
  · exact B1659971
  · exact B1659975
  · exact B1659979
  · exact B1659983
  · exact B1659987
  · exact B1659991
  · exact B1659995
  · exact B1659999
  · exact B1660003
  · exact B1660007
  · exact B1660011
  · exact B1660015
  · exact B1660019
  · exact B1660023
  · exact B1660027
  · exact B1660031
  · exact B1660035
  · exact B1660039
  · exact B1660043
  · exact B1660047
  · exact B1660051
  · exact B1660055
  · exact B1660059
  · exact B1660063
  · exact B1660067
  · exact B1660071
  · exact B1660075
  · exact B1660079
  · exact B1660083
  · exact B1660087
  · exact B1660091
  · exact B1660095
  · exact B1660099
  · exact B1660103
  · exact B1660107
  · exact B1660111
  · exact B1660115
  · exact B1660119
  · exact B1660123
  · exact B1660127
  · exact B1660131
  · exact B1660135
  · exact B1660139
  · exact B1660143
  · exact B1660147
  · exact B1660151
  · exact B1660155
  · exact B1660159
  · exact B1660163
  · exact B1660167
  · exact B1660171
  · exact B1660175
  · exact B1660179
  · exact B1660183
  · exact B1660187
  · exact B1660191
  · exact B1660195
  · exact B1660199
  · exact B1660203
  · exact B1660207
  · exact B1660211
  · exact B1660215
  · exact B1660219
  · exact B1660223
  · exact B1660227
  · exact B1660231
  · exact B1660235
  · exact B1660239
  · exact B1660243
  · exact B1660247
  · exact B1660251
  · exact B1660255
  · exact B1660259
  · exact B1660263
  · exact B1660267
  · exact B1660271
  · exact B1660275
  · exact B1660279
  · exact B1660283
  · exact B1660287
  · exact B1660291
  · exact B1660295
  · exact B1660299
  · exact B1660303
  · exact B1660307
  · exact B1660311
  · exact B1660315
  · exact B1660319
  · exact B1660323
  · exact B1660327
  · exact B1660331
  · exact B1660335
  · exact B1660339
  · exact B1660343
  · exact B1660347
  · exact B1660351
  · exact B1660355
  · exact B1660359
  · exact B1660363
  · exact B1660367
  · exact B1660371
  · exact B1660375
  · exact B1660379
  · exact B1660383
  · exact B1660387
  · exact B1660391
  · exact B1660395
  · exact B1660399
  · exact B1660403
  · exact B1660407
  · exact B1660411
  · exact B1660415
  · exact B1660419
  · exact B1660423
  · exact B1660427
  · exact B1660431
  · exact B1660435
  · exact B1660439
  · exact B1660443
  · exact B1660447
  · exact B1660451
  · exact B1660455
  · exact B1660459
  · exact B1660463
  · exact B1660467
  · exact B1660471
  · exact B1660475
  · exact B1660479
  · exact B1660483
  · exact B1660487
  · exact B1660491
  · exact B1660495
  · exact B1660499
  · exact B1660503
  · exact B1660507
  · exact B1660511
  · exact B1660515
  · exact B1660519
  · exact B1660523
  · exact B1660527
  · exact B1660531
  · exact B1660535
  · exact B1660539
  · exact B1660543
  · exact B1660547
  · exact B1660551
  · exact B1660555
  · exact B1660559
  · exact B1660563
  · exact B1660567
  · exact B1660571
  · exact B1660575
  · exact B1660579
  · exact B1660583
  · exact B1660587
  · exact B1660591
  · exact B1660595
  · exact B1660599
  · exact B1660603
  · exact B1660607
  · exact B1660611
  · exact B1660615
  · exact B1660619
  · exact B1660623
  · exact B1660627
  · exact B1660631
  · exact B1660635
  · exact B1660639
  · exact B1660643
  · exact B1660647
  · exact B1660651
  · exact B1660655
  · exact B1660659
  · exact B1660663
  · exact B1660667
  · exact B1660671
  · exact B1660675
  · exact B1660679
  · exact B1660683
  · exact B1660687
  · exact B1660691
  · exact B1660695
  · exact B1660699
  · exact B1660703
  · exact B1660707
  · exact B1660711
  · exact B1660715
  · exact B1660719
  · exact B1660723
  · exact B1660727
  · exact B1660731
  · exact B1660735
  · exact B1660739
  · exact B1660743
  · exact B1660747
  · exact B1660751
  · exact B1660755
  · exact B1660759
  · exact B1660763
  · exact B1660767
  · exact B1660771
  · exact B1660775
  · exact B1660779
  · exact B1660783
  · exact B1660787
  · exact B1660791
  · exact B1660795
  · exact B1660799
  · exact B1660803
  · exact B1660807
  · exact B1660811
  · exact B1660815
  · exact B1660819
  · exact B1660823
  · exact B1660827
  · exact B1660831
  · exact B1660835
  · exact B1660839
  · exact B1660843
  · exact B1660847
  · exact B1660851
  · exact B1660855
  · exact B1660859
  · exact B1660863
  · exact B1660867
  · exact B1660871
  · exact B1660875
  · exact B1660879
  · exact B1660883
  · exact B1660887
  · exact B1660891
  · exact B1660895
  · exact B1660899
  · exact B1660903
  · exact B1660907
  · exact B1660911
  · exact B1660915
  · exact B1660919
  · exact B1660923
  · exact B1660927
  · exact B1660931
  · exact B1660935
  · exact B1660939
  · exact B1660943
  · exact B1660947
  · exact B1660951
  · exact B1660955
  · exact B1660959
  · exact B1660963
  · exact B1660967
  · exact B1660971
  · exact B1660975
  · exact B1660979
  · exact B1660983
  · exact B1660987
  · exact B1660991
  · exact B1660995
  · exact B1660999
  · exact B1661003
  · exact B1661007
  · exact B1661011
  · exact B1661015
  · exact B1661019
  · exact B1661023
  · exact B1661027
  · exact B1661031
  · exact B1661035
  · exact B1661039
  · exact B1661043
  · exact B1661047
  · exact B1661051
  · exact B1661055
  · exact B1661059
  · exact B1661063
  · exact B1661067
  · exact B1661071
  · exact B1661075
  · exact B1661079
  · exact B1661083
  · exact B1661087
  · exact B1661091
  · exact B1661095
  · exact B1661099
  · exact B1661103
  · exact B1661107
  · exact B1661111
  · exact B1661115
  · exact B1661119
  · exact B1661123
  · exact B1661127
  · exact B1661131
  · exact B1661135
  · exact B1661139
  · exact B1661143
  · exact B1661147
  · exact B1661151
  · exact B1661155
  · exact B1661159
  · exact B1661163
  · exact B1661167
  · exact B1661171
  · exact B1661175
  · exact B1661179
  · exact B1661183
  · exact B1661187
  · exact B1661191
  · exact B1661195
  · exact B1661199
  · exact B1661203
  · exact B1661207
  · exact B1661211
  · exact B1661215
  · exact B1661219
  · exact B1661223
  · exact B1661227
  · exact B1661231
  · exact B1661235
  · exact B1661239
  · exact B1661243
  · exact B1661247
  · exact B1661251
  · exact B1661255
  · exact B1661259
  · exact B1661263
  · exact B1661267
  · exact B1661271
  · exact B1661275
  · exact B1661279
  · exact B1661283
  · exact B1661287
  · exact B1661291
  · exact B1661295
  · exact B1661299
  · exact B1661303
  · exact B1661307
  · exact B1661311
  · exact B1661315
  · exact B1661319
  · exact B1661323
  · exact B1661327
  · exact B1661331
  · exact B1661335
  · exact B1661339
  · exact B1661343
  · exact B1661347
  · exact B1661351
  · exact B1661355
  · exact B1661359
  · exact B1661363
  · exact B1661367
  · exact B1661371
  · exact B1661375
  · exact B1661379
  · exact B1661383
  · exact B1661387
  · exact B1661391
  · exact B1661395
  · exact B1661399
  · exact B1661403
  · exact B1661407
  · exact B1661411
  · exact B1661415
  · exact B1661419
  · exact B1661423
  · exact B1661427
  · exact B1661431
  · exact B1661435
  · exact B1661439
  · exact B1661443
  · exact B1661447
  · exact B1661451
  · exact B1661455
  · exact B1661459
  · exact B1661463
  · exact B1661467
  · exact B1661471
  · exact B1661475
  · exact B1661479
  · exact B1661483
  · exact B1661487
  · exact B1661491
  · exact B1661495
  · exact B1661499
  · exact B1661503
  · exact B1661507
  · exact B1661511
  · exact B1661515
  · exact B1661519
  · exact B1661523
  · exact B1661527

theorem solution (m : ℕ) (hlo : 1659529 ≤ m) (hhi : m ≤ 1661529) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 414882 ≤ j := by omega
    have hj2 : j ≤ 415381 := by omega
    have hb : Blo 1659529 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
