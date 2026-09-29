-- Prove2me | solution 1 for syracuse_descends_range_1580488_1582488
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:07:47.57693+00:00
-- url     : https://prove2.me/submissions/ce4d53b2-2d86-485f-b192-e807afa7195d

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


theorem B1900621 : Blo 1580488 1900621 := bbase (se 3 (by rfl) ⟨356366, by rfl⟩ : syracuseStep 1900621 = 712733) (by norm_num)
theorem B6758549 : Blo 1580488 6758549 := bbase (se 6 (by rfl) ⟨158403, by rfl⟩ : syracuseStep 6758549 = 316807) (by norm_num)
theorem B4505813 : Blo 1580488 4505813 := bbase (se 7 (by rfl) ⟨52802, by rfl⟩ : syracuseStep 4505813 = 105605) (by norm_num)
theorem B1900765 : Blo 1580488 1900765 := bbase (se 3 (by rfl) ⟨356393, by rfl⟩ : syracuseStep 1900765 = 712787) (by norm_num)
theorem B34210133 : Blo 1580488 34210133 := bbase (se 10 (by rfl) ⟨50112, by rfl⟩ : syracuseStep 34210133 = 100225) (by norm_num)
theorem B20275541 : Blo 1580488 20275541 := bbase (se 10 (by rfl) ⟨29700, by rfl⟩ : syracuseStep 20275541 = 59401) (by norm_num)
theorem B1687937 : Blo 1580488 1687937 := bbase (se 2 (by rfl) ⟨632976, by rfl⟩ : syracuseStep 1687937 = 1265953) (by norm_num)
theorem B1778053 : Blo 1580488 1778053 := bbase (se 4 (by rfl) ⟨166692, by rfl⟩ : syracuseStep 1778053 = 333385) (by norm_num)
theorem B1778089 : Blo 1580488 1778089 := bbase (se 2 (by rfl) ⟨666783, by rfl⟩ : syracuseStep 1778089 = 1333567) (by norm_num)
theorem B3375533 : Blo 1580488 3375533 := bbase (se 3 (by rfl) ⟨632912, by rfl⟩ : syracuseStep 3375533 = 1265825) (by norm_num)
theorem B1687997 : Blo 1580488 1687997 := bbase (se 3 (by rfl) ⟨316499, by rfl⟩ : syracuseStep 1687997 = 632999) (by norm_num)
theorem B1778125 : Blo 1580488 1778125 := bbase (se 3 (by rfl) ⟨333398, by rfl⟩ : syracuseStep 1778125 = 666797) (by norm_num)
theorem B1778161 : Blo 1580488 1778161 := bbase (se 2 (by rfl) ⟨666810, by rfl⟩ : syracuseStep 1778161 = 1333621) (by norm_num)
theorem B1778197 : Blo 1580488 1778197 := bbase (se 6 (by rfl) ⟨41676, by rfl⟩ : syracuseStep 1778197 = 83353) (by norm_num)
theorem B2138653 : Blo 1580488 2138653 := bbase (se 3 (by rfl) ⟨400997, by rfl⟩ : syracuseStep 2138653 = 801995) (by norm_num)
theorem B2531893 : Blo 1580488 2531893 := bbase (se 5 (by rfl) ⟨118682, by rfl⟩ : syracuseStep 2531893 = 237365) (by norm_num)
theorem B1778233 : Blo 1580488 1778233 := bbase (se 2 (by rfl) ⟨666837, by rfl⟩ : syracuseStep 1778233 = 1333675) (by norm_num)
theorem B1688125 : Blo 1580488 1688125 := bbase (se 3 (by rfl) ⟨316523, by rfl⟩ : syracuseStep 1688125 = 633047) (by norm_num)
theorem B1778269 : Blo 1580488 1778269 := bbase (se 3 (by rfl) ⟨333425, by rfl⟩ : syracuseStep 1778269 = 666851) (by norm_num)
theorem B2851421 : Blo 1580488 2851421 := bbase (se 3 (by rfl) ⟨534641, by rfl⟩ : syracuseStep 2851421 = 1069283) (by norm_num)
theorem B1778305 : Blo 1580488 1778305 := bbase (se 2 (by rfl) ⟨666864, by rfl⟩ : syracuseStep 1778305 = 1333729) (by norm_num)
theorem B1778341 : Blo 1580488 1778341 := bbase (se 4 (by rfl) ⟨166719, by rfl⟩ : syracuseStep 1778341 = 333439) (by norm_num)
theorem B1778377 : Blo 1580488 1778377 := bbase (se 2 (by rfl) ⟨666891, by rfl⟩ : syracuseStep 1778377 = 1333783) (by norm_num)
theorem B1778413 : Blo 1580488 1778413 := bbase (se 3 (by rfl) ⟨333452, by rfl⟩ : syracuseStep 1778413 = 666905) (by norm_num)
theorem B1778449 : Blo 1580488 1778449 := bbase (se 2 (by rfl) ⟨666918, by rfl⟩ : syracuseStep 1778449 = 1333837) (by norm_num)
theorem B3556133 : Blo 1580488 3556133 := bbase (se 4 (by rfl) ⟨333387, by rfl⟩ : syracuseStep 3556133 = 666775) (by norm_num)
theorem B1778485 : Blo 1580488 1778485 := bbase (se 5 (by rfl) ⟨83366, by rfl⟩ : syracuseStep 1778485 = 166733) (by norm_num)
theorem B1778521 : Blo 1580488 1778521 := bbase (se 2 (by rfl) ⟨666945, by rfl⟩ : syracuseStep 1778521 = 1333891) (by norm_num)
theorem B3556205 : Blo 1580488 3556205 := bbase (se 3 (by rfl) ⟨666788, by rfl⟩ : syracuseStep 3556205 = 1333577) (by norm_num)
theorem B1778557 : Blo 1580488 1778557 := bbase (se 3 (by rfl) ⟨333479, by rfl⟩ : syracuseStep 1778557 = 666959) (by norm_num)
theorem B1778593 : Blo 1580488 1778593 := bbase (se 2 (by rfl) ⟨666972, by rfl⟩ : syracuseStep 1778593 = 1333945) (by norm_num)
theorem B3556277 : Blo 1580488 3556277 := bbase (se 5 (by rfl) ⟨166700, by rfl⟩ : syracuseStep 3556277 = 333401) (by norm_num)
theorem B1778629 : Blo 1580488 1778629 := bbase (se 4 (by rfl) ⟨166746, by rfl⟩ : syracuseStep 1778629 = 333493) (by norm_num)
theorem B27018197 : Blo 1580488 27018197 := bbase (se 7 (by rfl) ⟨316619, by rfl⟩ : syracuseStep 27018197 = 633239) (by norm_num)
theorem B3802069 : Blo 1580488 3802069 := bbase (se 7 (by rfl) ⟨44555, by rfl⟩ : syracuseStep 3802069 = 89111) (by norm_num)
theorem B8004581 : Blo 1580488 8004581 := bbase (se 4 (by rfl) ⟨750429, by rfl⟩ : syracuseStep 8004581 = 1500859) (by norm_num)
theorem B1778665 : Blo 1580488 1778665 := bbase (se 2 (by rfl) ⟨666999, by rfl⟩ : syracuseStep 1778665 = 1333999) (by norm_num)
theorem B2532341 : Blo 1580488 2532341 := bbase (se 5 (by rfl) ⟨118703, by rfl⟩ : syracuseStep 2532341 = 237407) (by norm_num)
theorem B1688569 : Blo 1580488 1688569 := bbase (se 2 (by rfl) ⟨633213, by rfl⟩ : syracuseStep 1688569 = 1266427) (by norm_num)
theorem B3556349 : Blo 1580488 3556349 := bbase (se 3 (by rfl) ⟨666815, by rfl⟩ : syracuseStep 3556349 = 1333631) (by norm_num)
theorem B1778701 : Blo 1580488 1778701 := bbase (se 3 (by rfl) ⟨333506, by rfl⟩ : syracuseStep 1778701 = 667013) (by norm_num)
theorem B12010517 : Blo 1580488 12010517 := bbase (se 6 (by rfl) ⟨281496, by rfl⟩ : syracuseStep 12010517 = 562993) (by norm_num)
theorem B1778737 : Blo 1580488 1778737 := bbase (se 2 (by rfl) ⟨667026, by rfl⟩ : syracuseStep 1778737 = 1334053) (by norm_num)
theorem B6939701 : Blo 1580488 6939701 := bbase (se 5 (by rfl) ⟨325298, by rfl⟩ : syracuseStep 6939701 = 650597) (by norm_num)
theorem B3556421 : Blo 1580488 3556421 := bbase (se 4 (by rfl) ⟨333414, by rfl⟩ : syracuseStep 3556421 = 666829) (by norm_num)
theorem B1778773 : Blo 1580488 1778773 := bbase (se 8 (by rfl) ⟨10422, by rfl⟩ : syracuseStep 1778773 = 20845) (by norm_num)
theorem B1688689 : Blo 1580488 1688689 := bbase (se 2 (by rfl) ⟨633258, by rfl⟩ : syracuseStep 1688689 = 1266517) (by norm_num)
theorem B1778809 : Blo 1580488 1778809 := bbase (se 2 (by rfl) ⟨667053, by rfl⟩ : syracuseStep 1778809 = 1334107) (by norm_num)
theorem B3556493 : Blo 1580488 3556493 := bbase (se 3 (by rfl) ⟨666842, by rfl⟩ : syracuseStep 3556493 = 1333685) (by norm_num)
theorem B1778845 : Blo 1580488 1778845 := bbase (se 3 (by rfl) ⟨333533, by rfl⟩ : syracuseStep 1778845 = 667067) (by norm_num)
theorem B2532541 : Blo 1580488 2532541 := bbase (se 3 (by rfl) ⟨474851, by rfl⟩ : syracuseStep 2532541 = 949703) (by norm_num)
theorem B1778881 : Blo 1580488 1778881 := bbase (se 2 (by rfl) ⟨667080, by rfl⟩ : syracuseStep 1778881 = 1334161) (by norm_num)
theorem B3556565 : Blo 1580488 3556565 := bbase (se 7 (by rfl) ⟨41678, by rfl⟩ : syracuseStep 3556565 = 83357) (by norm_num)
theorem B1778917 : Blo 1580488 1778917 := bbase (se 4 (by rfl) ⟨166773, by rfl⟩ : syracuseStep 1778917 = 333547) (by norm_num)
theorem B1778953 : Blo 1580488 1778953 := bbase (se 2 (by rfl) ⟨667107, by rfl⟩ : syracuseStep 1778953 = 1334215) (by norm_num)
theorem B3556637 : Blo 1580488 3556637 := bbase (se 3 (by rfl) ⟨666869, by rfl⟩ : syracuseStep 3556637 = 1333739) (by norm_num)
theorem B3376421 : Blo 1580488 3376421 := bbase (se 4 (by rfl) ⟨316539, by rfl⟩ : syracuseStep 3376421 = 633079) (by norm_num)
theorem B1778989 : Blo 1580488 1778989 := bbase (se 3 (by rfl) ⟨333560, by rfl⟩ : syracuseStep 1778989 = 667121) (by norm_num)
theorem B7595333 : Blo 1580488 7595333 := bbase (se 4 (by rfl) ⟨712062, by rfl⟩ : syracuseStep 7595333 = 1424125) (by norm_num)
theorem B1779025 : Blo 1580488 1779025 := bbase (se 2 (by rfl) ⟨667134, by rfl⟩ : syracuseStep 1779025 = 1334269) (by norm_num)
theorem B3556709 : Blo 1580488 3556709 := bbase (se 4 (by rfl) ⟨333441, by rfl⟩ : syracuseStep 3556709 = 666883) (by norm_num)
theorem B1688941 : Blo 1580488 1688941 := bbase (se 3 (by rfl) ⟨316676, by rfl⟩ : syracuseStep 1688941 = 633353) (by norm_num)
theorem B1688945 : Blo 1580488 1688945 := bbase (se 2 (by rfl) ⟨633354, by rfl⟩ : syracuseStep 1688945 = 1266709) (by norm_num)
theorem B5334389 : Blo 1580488 5334389 := bbase (se 5 (by rfl) ⟨250049, by rfl⟩ : syracuseStep 5334389 = 500099) (by norm_num)
theorem B1779061 : Blo 1580488 1779061 := bbase (se 5 (by rfl) ⟨83393, by rfl⟩ : syracuseStep 1779061 = 166787) (by norm_num)
theorem B1779097 : Blo 1580488 1779097 := bbase (se 2 (by rfl) ⟨667161, by rfl⟩ : syracuseStep 1779097 = 1334323) (by norm_num)
theorem B3376541 : Blo 1580488 3376541 := bbase (se 3 (by rfl) ⟨633101, by rfl⟩ : syracuseStep 3376541 = 1266203) (by norm_num)
theorem B3556781 : Blo 1580488 3556781 := bbase (se 3 (by rfl) ⟨666896, by rfl⟩ : syracuseStep 3556781 = 1333793) (by norm_num)
theorem B12002741 : Blo 1580488 12002741 := bbase (se 5 (by rfl) ⟨562628, by rfl⟩ : syracuseStep 12002741 = 1125257) (by norm_num)
theorem B2532797 : Blo 1580488 2532797 := bbase (se 3 (by rfl) ⟨474899, by rfl⟩ : syracuseStep 2532797 = 949799) (by norm_num)
theorem B1779133 : Blo 1580488 1779133 := bbase (se 3 (by rfl) ⟨333587, by rfl⟩ : syracuseStep 1779133 = 667175) (by norm_num)
theorem B1779169 : Blo 1580488 1779169 := bbase (se 2 (by rfl) ⟨667188, by rfl⟩ : syracuseStep 1779169 = 1334377) (by norm_num)
theorem B3556853 : Blo 1580488 3556853 := bbase (se 5 (by rfl) ⟨166727, by rfl⟩ : syracuseStep 3556853 = 333455) (by norm_num)
theorem B1779205 : Blo 1580488 1779205 := bbase (se 4 (by rfl) ⟨166800, by rfl⟩ : syracuseStep 1779205 = 333601) (by norm_num)
theorem B1779241 : Blo 1580488 1779241 := bbase (se 2 (by rfl) ⟨667215, by rfl⟩ : syracuseStep 1779241 = 1334431) (by norm_num)
theorem B5408309 : Blo 1580488 5408309 := bbase (se 5 (by rfl) ⟨253514, by rfl⟩ : syracuseStep 5408309 = 507029) (by norm_num)
theorem B3556925 : Blo 1580488 3556925 := bbase (se 3 (by rfl) ⟨666923, by rfl⟩ : syracuseStep 3556925 = 1333847) (by norm_num)
theorem B1779277 : Blo 1580488 1779277 := bbase (se 3 (by rfl) ⟨333614, by rfl⟩ : syracuseStep 1779277 = 667229) (by norm_num)
theorem B2000477 : Blo 1580488 2000477 := bbase (se 3 (by rfl) ⟨375089, by rfl⟩ : syracuseStep 2000477 = 750179) (by norm_num)
theorem B1779313 : Blo 1580488 1779313 := bbase (se 2 (by rfl) ⟨667242, by rfl⟩ : syracuseStep 1779313 = 1334485) (by norm_num)
theorem B6497909 : Blo 1580488 6497909 := bbase (se 5 (by rfl) ⟨304589, by rfl⟩ : syracuseStep 6497909 = 609179) (by norm_num)
theorem B3556997 : Blo 1580488 3556997 := bbase (se 4 (by rfl) ⟨333468, by rfl⟩ : syracuseStep 3556997 = 666937) (by norm_num)
theorem B2000533 : Blo 1580488 2000533 := bbase (se 6 (by rfl) ⟨46887, by rfl⟩ : syracuseStep 2000533 = 93775) (by norm_num)
theorem B1779349 : Blo 1580488 1779349 := bbase (se 6 (by rfl) ⟨41703, by rfl⟩ : syracuseStep 1779349 = 83407) (by norm_num)
theorem B4056733 : Blo 1580488 4056733 := bbase (se 3 (by rfl) ⟨760637, by rfl⟩ : syracuseStep 4056733 = 1521275) (by norm_num)
theorem B1779385 : Blo 1580488 1779385 := bbase (se 2 (by rfl) ⟨667269, by rfl⟩ : syracuseStep 1779385 = 1334539) (by norm_num)
theorem B3557069 : Blo 1580488 3557069 := bbase (se 3 (by rfl) ⟨666950, by rfl⟩ : syracuseStep 3557069 = 1333901) (by norm_num)
theorem B1779421 : Blo 1580488 1779421 := bbase (se 3 (by rfl) ⟨333641, by rfl⟩ : syracuseStep 1779421 = 667283) (by norm_num)
theorem B2000629 : Blo 1580488 2000629 := bbase (se 5 (by rfl) ⟨93779, by rfl⟩ : syracuseStep 2000629 = 187559) (by norm_num)
theorem B1779457 : Blo 1580488 1779457 := bbase (se 2 (by rfl) ⟨667296, by rfl⟩ : syracuseStep 1779457 = 1334593) (by norm_num)
theorem B3557141 : Blo 1580488 3557141 := bbase (se 6 (by rfl) ⟨83370, by rfl⟩ : syracuseStep 3557141 = 166741) (by norm_num)
theorem B5334821 : Blo 1580488 5334821 := bbase (se 4 (by rfl) ⟨500139, by rfl⟩ : syracuseStep 5334821 = 1000279) (by norm_num)
theorem B1779493 : Blo 1580488 1779493 := bbase (se 4 (by rfl) ⟨166827, by rfl⟩ : syracuseStep 1779493 = 333655) (by norm_num)
theorem B6006581 : Blo 1580488 6006581 := bbase (se 5 (by rfl) ⟨281558, by rfl⟩ : syracuseStep 6006581 = 563117) (by norm_num)
theorem B1779529 : Blo 1580488 1779529 := bbase (se 2 (by rfl) ⟨667323, by rfl⟩ : syracuseStep 1779529 = 1334647) (by norm_num)
theorem B3557213 : Blo 1580488 3557213 := bbase (se 3 (by rfl) ⟨666977, by rfl⟩ : syracuseStep 3557213 = 1333955) (by norm_num)
theorem B1779565 : Blo 1580488 1779565 := bbase (se 3 (by rfl) ⟨333668, by rfl⟩ : syracuseStep 1779565 = 667337) (by norm_num)
theorem B1779601 : Blo 1580488 1779601 := bbase (se 2 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 1779601 = 1334701) (by norm_num)
theorem B2000801 : Blo 1580488 2000801 := bbase (se 2 (by rfl) ⟨750300, by rfl⟩ : syracuseStep 2000801 = 1500601) (by norm_num)
theorem B3557285 : Blo 1580488 3557285 := bbase (se 4 (by rfl) ⟨333495, by rfl⟩ : syracuseStep 3557285 = 666991) (by norm_num)
theorem B1689509 : Blo 1580488 1689509 := bbase (se 4 (by rfl) ⟨158391, by rfl⟩ : syracuseStep 1689509 = 316783) (by norm_num)
theorem B1779637 : Blo 1580488 1779637 := bbase (se 5 (by rfl) ⟨83420, by rfl⟩ : syracuseStep 1779637 = 166841) (by norm_num)
theorem B2000857 : Blo 1580488 2000857 := bbase (se 2 (by rfl) ⟨750321, by rfl⟩ : syracuseStep 2000857 = 1500643) (by norm_num)
theorem B1779673 : Blo 1580488 1779673 := bbase (se 2 (by rfl) ⟨667377, by rfl⟩ : syracuseStep 1779673 = 1334755) (by norm_num)
theorem B3557357 : Blo 1580488 3557357 := bbase (se 3 (by rfl) ⟨667004, by rfl⟩ : syracuseStep 3557357 = 1334009) (by norm_num)
theorem B1779709 : Blo 1580488 1779709 := bbase (se 3 (by rfl) ⟨333695, by rfl⟩ : syracuseStep 1779709 = 667391) (by norm_num)
theorem B6752261 : Blo 1580488 6752261 := bbase (se 4 (by rfl) ⟨633024, by rfl⟩ : syracuseStep 6752261 = 1266049) (by norm_num)
theorem B3377173 : Blo 1580488 3377173 := bbase (se 6 (by rfl) ⟨79152, by rfl⟩ : syracuseStep 3377173 = 158305) (by norm_num)
theorem B1779745 : Blo 1580488 1779745 := bbase (se 2 (by rfl) ⟨667404, by rfl⟩ : syracuseStep 1779745 = 1334809) (by norm_num)
theorem B3557429 : Blo 1580488 3557429 := bbase (se 5 (by rfl) ⟨166754, by rfl⟩ : syracuseStep 3557429 = 333509) (by norm_num)
theorem B2000953 : Blo 1580488 2000953 := bbase (se 2 (by rfl) ⟨750357, by rfl⟩ : syracuseStep 2000953 = 1500715) (by norm_num)
theorem B7596101 : Blo 1580488 7596101 := bbase (se 4 (by rfl) ⟨712134, by rfl⟩ : syracuseStep 7596101 = 1424269) (by norm_num)
theorem B1779781 : Blo 1580488 1779781 := bbase (se 4 (by rfl) ⟨166854, by rfl⟩ : syracuseStep 1779781 = 333709) (by norm_num)
theorem B6006869 : Blo 1580488 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B1689697 : Blo 1580488 1689697 := bbase (se 2 (by rfl) ⟨633636, by rfl⟩ : syracuseStep 1689697 = 1267273) (by norm_num)
theorem B1779817 : Blo 1580488 1779817 := bbase (se 2 (by rfl) ⟨667431, by rfl⟩ : syracuseStep 1779817 = 1334863) (by norm_num)
theorem B1804397 : Blo 1580488 1804397 := bbase (se 3 (by rfl) ⟨338324, by rfl⟩ : syracuseStep 1804397 = 676649) (by norm_num)
theorem B3557501 : Blo 1580488 3557501 := bbase (se 3 (by rfl) ⟨667031, by rfl⟩ : syracuseStep 3557501 = 1334063) (by norm_num)
theorem B1779853 : Blo 1580488 1779853 := bbase (se 3 (by rfl) ⟨333722, by rfl⟩ : syracuseStep 1779853 = 667445) (by norm_num)
theorem B5482661 : Blo 1580488 5482661 := bbase (se 4 (by rfl) ⟨513999, by rfl⟩ : syracuseStep 5482661 = 1027999) (by norm_num)
theorem B1779889 : Blo 1580488 1779889 := bbase (se 2 (by rfl) ⟨667458, by rfl⟩ : syracuseStep 1779889 = 1334917) (by norm_num)
theorem B7604405 : Blo 1580488 7604405 := bbase (se 5 (by rfl) ⟨356456, by rfl⟩ : syracuseStep 7604405 = 712913) (by norm_num)
theorem B3557573 : Blo 1580488 3557573 := bbase (se 4 (by rfl) ⟨333522, by rfl⟩ : syracuseStep 3557573 = 667045) (by norm_num)
theorem B5335253 : Blo 1580488 5335253 := bbase (se 7 (by rfl) ⟨62522, by rfl⟩ : syracuseStep 5335253 = 125045) (by norm_num)
theorem B1779925 : Blo 1580488 1779925 := bbase (se 7 (by rfl) ⟨20858, by rfl⟩ : syracuseStep 1779925 = 41717) (by norm_num)
theorem B2001125 : Blo 1580488 2001125 := bbase (se 4 (by rfl) ⟨187605, by rfl⟩ : syracuseStep 2001125 = 375211) (by norm_num)
theorem B3000557 : Blo 1580488 3000557 := bbase (se 3 (by rfl) ⟨562604, by rfl⟩ : syracuseStep 3000557 = 1125209) (by norm_num)
theorem B8005877 : Blo 1580488 8005877 := bbase (se 5 (by rfl) ⟨375275, by rfl⟩ : syracuseStep 8005877 = 750551) (by norm_num)
theorem B1779961 : Blo 1580488 1779961 := bbase (se 2 (by rfl) ⟨667485, by rfl⟩ : syracuseStep 1779961 = 1334971) (by norm_num)
theorem B3557645 : Blo 1580488 3557645 := bbase (se 3 (by rfl) ⟨667058, by rfl⟩ : syracuseStep 3557645 = 1334117) (by norm_num)
theorem B2001181 : Blo 1580488 2001181 := bbase (se 3 (by rfl) ⟨375221, by rfl⟩ : syracuseStep 2001181 = 750443) (by norm_num)
theorem B1779997 : Blo 1580488 1779997 := bbase (se 3 (by rfl) ⟨333749, by rfl⟩ : syracuseStep 1779997 = 667499) (by norm_num)
theorem B4057381 : Blo 1580488 4057381 := bbase (se 4 (by rfl) ⟨380379, by rfl⟩ : syracuseStep 4057381 = 760759) (by norm_num)
theorem B3852589 : Blo 1580488 3852589 := bbase (se 3 (by rfl) ⟨722360, by rfl⟩ : syracuseStep 3852589 = 1444721) (by norm_num)
theorem B1780033 : Blo 1580488 1780033 := bbase (se 2 (by rfl) ⟨667512, by rfl⟩ : syracuseStep 1780033 = 1335025) (by norm_num)
theorem B3557717 : Blo 1580488 3557717 := bbase (se 10 (by rfl) ⟨5211, by rfl⟩ : syracuseStep 3557717 = 10423) (by norm_num)
theorem B4811093 : Blo 1580488 4811093 := bbase (se 10 (by rfl) ⟨7047, by rfl⟩ : syracuseStep 4811093 = 14095) (by norm_num)
theorem B1780069 : Blo 1580488 1780069 := bbase (se 4 (by rfl) ⟨166881, by rfl⟩ : syracuseStep 1780069 = 333763) (by norm_num)
theorem B9619829 : Blo 1580488 9619829 := bbase (se 5 (by rfl) ⟨450929, by rfl⟩ : syracuseStep 9619829 = 901859) (by norm_num)
theorem B10135925 : Blo 1580488 10135925 := bbase (se 5 (by rfl) ⟨475121, by rfl⟩ : syracuseStep 10135925 = 950243) (by norm_num)
theorem B3000701 : Blo 1580488 3000701 := bbase (se 3 (by rfl) ⟨562631, by rfl⟩ : syracuseStep 3000701 = 1125263) (by norm_num)
theorem B2001277 : Blo 1580488 2001277 := bbase (se 3 (by rfl) ⟨375239, by rfl⟩ : syracuseStep 2001277 = 750479) (by norm_num)
theorem B1780105 : Blo 1580488 1780105 := bbase (se 2 (by rfl) ⟨667539, by rfl⟩ : syracuseStep 1780105 = 1335079) (by norm_num)
theorem B3557789 : Blo 1580488 3557789 := bbase (se 3 (by rfl) ⟨667085, by rfl⟩ : syracuseStep 3557789 = 1334171) (by norm_num)
theorem B1780141 : Blo 1580488 1780141 := bbase (se 3 (by rfl) ⟨333776, by rfl⟩ : syracuseStep 1780141 = 667553) (by norm_num)
theorem B6408629 : Blo 1580488 6408629 := bbase (se 5 (by rfl) ⟨300404, by rfl⟩ : syracuseStep 6408629 = 600809) (by norm_num)
theorem B1780177 : Blo 1580488 1780177 := bbase (se 2 (by rfl) ⟨667566, by rfl⟩ : syracuseStep 1780177 = 1335133) (by norm_num)
theorem B3041749 : Blo 1580488 3041749 := bbase (se 7 (by rfl) ⟨35645, by rfl⟩ : syracuseStep 3041749 = 71291) (by norm_num)
theorem B3557861 : Blo 1580488 3557861 := bbase (se 4 (by rfl) ⟨333549, by rfl⟩ : syracuseStep 3557861 = 667099) (by norm_num)
theorem B12175861 : Blo 1580488 12175861 := bbase (se 5 (by rfl) ⟨570743, by rfl⟩ : syracuseStep 12175861 = 1141487) (by norm_num)
theorem B1780213 : Blo 1580488 1780213 := bbase (se 5 (by rfl) ⟨83447, by rfl⟩ : syracuseStep 1780213 = 166895) (by norm_num)
theorem B1780249 : Blo 1580488 1780249 := bbase (se 2 (by rfl) ⟨667593, by rfl⟩ : syracuseStep 1780249 = 1335187) (by norm_num)
theorem B2533925 : Blo 1580488 2533925 := bbase (se 4 (by rfl) ⟨237555, by rfl⟩ : syracuseStep 2533925 = 475111) (by norm_num)
theorem B2001449 : Blo 1580488 2001449 := bbase (se 2 (by rfl) ⟨750543, by rfl⟩ : syracuseStep 2001449 = 1501087) (by norm_num)
theorem B3557933 : Blo 1580488 3557933 := bbase (se 3 (by rfl) ⟨667112, by rfl⟩ : syracuseStep 3557933 = 1334225) (by norm_num)
theorem B1780285 : Blo 1580488 1780285 := bbase (se 3 (by rfl) ⟨333803, by rfl⟩ : syracuseStep 1780285 = 667607) (by norm_num)
theorem B2001505 : Blo 1580488 2001505 := bbase (se 2 (by rfl) ⟨750564, by rfl⟩ : syracuseStep 2001505 = 1501129) (by norm_num)
theorem B3558005 : Blo 1580488 3558005 := bbase (se 5 (by rfl) ⟨166781, by rfl⟩ : syracuseStep 3558005 = 333563) (by norm_num)
theorem B5335685 : Blo 1580488 5335685 := bbase (se 4 (by rfl) ⟨500220, by rfl⟩ : syracuseStep 5335685 = 1000441) (by norm_num)
theorem B3000989 : Blo 1580488 3000989 := bbase (se 3 (by rfl) ⟨562685, by rfl⟩ : syracuseStep 3000989 = 1125371) (by norm_num)
theorem B3558077 : Blo 1580488 3558077 := bbase (se 3 (by rfl) ⟨667139, by rfl⟩ : syracuseStep 3558077 = 1334279) (by norm_num)
theorem B2001601 : Blo 1580488 2001601 := bbase (se 2 (by rfl) ⟨750600, by rfl⟩ : syracuseStep 2001601 = 1501201) (by norm_num)
theorem B3558149 : Blo 1580488 3558149 := bbase (se 4 (by rfl) ⟨333576, by rfl⟩ : syracuseStep 3558149 = 667153) (by norm_num)
theorem B3001141 : Blo 1580488 3001141 := bbase (se 5 (by rfl) ⟨140678, by rfl⟩ : syracuseStep 3001141 = 281357) (by norm_num)
theorem B3558221 : Blo 1580488 3558221 := bbase (se 3 (by rfl) ⟨667166, by rfl⟩ : syracuseStep 3558221 = 1334333) (by norm_num)
theorem B2001773 : Blo 1580488 2001773 := bbase (se 3 (by rfl) ⟨375332, by rfl⟩ : syracuseStep 2001773 = 750665) (by norm_num)
theorem B3378061 : Blo 1580488 3378061 := bbase (se 3 (by rfl) ⟨633386, by rfl⟩ : syracuseStep 3378061 = 1266773) (by norm_num)
theorem B4000661 : Blo 1580488 4000661 := bbase (se 6 (by rfl) ⟨93765, by rfl⟩ : syracuseStep 4000661 = 187531) (by norm_num)
theorem B3558293 : Blo 1580488 3558293 := bbase (se 6 (by rfl) ⟨83397, by rfl⟩ : syracuseStep 3558293 = 166795) (by norm_num)
theorem B2001829 : Blo 1580488 2001829 := bbase (se 4 (by rfl) ⟨187671, by rfl⟩ : syracuseStep 2001829 = 375343) (by norm_num)
theorem B3558365 : Blo 1580488 3558365 := bbase (se 3 (by rfl) ⟨667193, by rfl⟩ : syracuseStep 3558365 = 1334387) (by norm_num)
theorem B3378181 : Blo 1580488 3378181 := bbase (se 4 (by rfl) ⟨316704, by rfl⟩ : syracuseStep 3378181 = 633409) (by norm_num)
theorem B2001925 : Blo 1580488 2001925 := bbase (se 4 (by rfl) ⟨187680, by rfl⟩ : syracuseStep 2001925 = 375361) (by norm_num)
theorem B3558437 : Blo 1580488 3558437 := bbase (se 4 (by rfl) ⟨333603, by rfl⟩ : syracuseStep 3558437 = 667207) (by norm_num)
theorem B2534437 : Blo 1580488 2534437 := bbase (se 4 (by rfl) ⟨237603, by rfl⟩ : syracuseStep 2534437 = 475207) (by norm_num)
theorem B5336117 : Blo 1580488 5336117 := bbase (se 5 (by rfl) ⟨250130, by rfl⟩ : syracuseStep 5336117 = 500261) (by norm_num)
theorem B3042365 : Blo 1580488 3042365 := bbase (se 3 (by rfl) ⟨570443, by rfl⟩ : syracuseStep 3042365 = 1140887) (by norm_num)
theorem B4000853 : Blo 1580488 4000853 := bbase (se 8 (by rfl) ⟨23442, by rfl⟩ : syracuseStep 4000853 = 46885) (by norm_num)
theorem B3001445 : Blo 1580488 3001445 := bbase (se 4 (by rfl) ⟨281385, by rfl⟩ : syracuseStep 3001445 = 562771) (by norm_num)
theorem B3206245 : Blo 1580488 3206245 := bbase (se 4 (by rfl) ⟨300585, by rfl⟩ : syracuseStep 3206245 = 601171) (by norm_num)
theorem B3558509 : Blo 1580488 3558509 := bbase (se 3 (by rfl) ⟨667220, by rfl⟩ : syracuseStep 3558509 = 1334441) (by norm_num)
theorem B3083405 : Blo 1580488 3083405 := bbase (se 3 (by rfl) ⟨578138, by rfl⟩ : syracuseStep 3083405 = 1156277) (by norm_num)
theorem B2002097 : Blo 1580488 2002097 := bbase (se 2 (by rfl) ⟨750786, by rfl⟩ : syracuseStep 2002097 = 1501573) (by norm_num)
theorem B3558581 : Blo 1580488 3558581 := bbase (se 5 (by rfl) ⟨166808, by rfl⟩ : syracuseStep 3558581 = 333617) (by norm_num)
theorem B2370749 : Blo 1580488 2370749 := bbase (se 3 (by rfl) ⟨444515, by rfl⟩ : syracuseStep 2370749 = 889031) (by norm_num)
theorem B2370773 : Blo 1580488 2370773 := bbase (se 7 (by rfl) ⟨27782, by rfl⟩ : syracuseStep 2370773 = 55565) (by norm_num)
theorem B2002153 : Blo 1580488 2002153 := bbase (se 2 (by rfl) ⟨750807, by rfl⟩ : syracuseStep 2002153 = 1501615) (by norm_num)
theorem B2370797 : Blo 1580488 2370797 := bbase (se 3 (by rfl) ⟨444524, by rfl⟩ : syracuseStep 2370797 = 889049) (by norm_num)
theorem B6008053 : Blo 1580488 6008053 := bbase (se 5 (by rfl) ⟨281627, by rfl⟩ : syracuseStep 6008053 = 563255) (by norm_num)
theorem B3558653 : Blo 1580488 3558653 := bbase (se 3 (by rfl) ⟨667247, by rfl⟩ : syracuseStep 3558653 = 1334495) (by norm_num)
theorem B2370821 : Blo 1580488 2370821 := bbase (se 4 (by rfl) ⟨222264, by rfl⟩ : syracuseStep 2370821 = 444529) (by norm_num)
theorem B3378437 : Blo 1580488 3378437 := bbase (se 4 (by rfl) ⟨316728, by rfl⟩ : syracuseStep 3378437 = 633457) (by norm_num)
theorem B3607829 : Blo 1580488 3607829 := bbase (se 6 (by rfl) ⟨84558, by rfl⟩ : syracuseStep 3607829 = 169117) (by norm_num)
theorem B2370845 : Blo 1580488 2370845 := bbase (se 3 (by rfl) ⟨444533, by rfl⟩ : syracuseStep 2370845 = 889067) (by norm_num)
theorem B2436389 : Blo 1580488 2436389 := bbase (se 4 (by rfl) ⟨228411, by rfl⟩ : syracuseStep 2436389 = 456823) (by norm_num)
theorem B2370869 : Blo 1580488 2370869 := bbase (se 5 (by rfl) ⟨111134, by rfl⟩ : syracuseStep 2370869 = 222269) (by norm_num)
theorem B3042613 : Blo 1580488 3042613 := bbase (se 5 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 3042613 = 285245) (by norm_num)
theorem B3558725 : Blo 1580488 3558725 := bbase (se 4 (by rfl) ⟨333630, by rfl⟩ : syracuseStep 3558725 = 667261) (by norm_num)
theorem B2002249 : Blo 1580488 2002249 := bbase (se 2 (by rfl) ⟨750843, by rfl⟩ : syracuseStep 2002249 = 1501687) (by norm_num)
theorem B2370893 : Blo 1580488 2370893 := bbase (se 3 (by rfl) ⟨444542, by rfl⟩ : syracuseStep 2370893 = 889085) (by norm_num)
theorem B3607901 : Blo 1580488 3607901 := bbase (se 3 (by rfl) ⟨676481, by rfl⟩ : syracuseStep 3607901 = 1352963) (by norm_num)
theorem B2370917 : Blo 1580488 2370917 := bbase (se 4 (by rfl) ⟨222273, by rfl⟩ : syracuseStep 2370917 = 444547) (by norm_num)
theorem B2370941 : Blo 1580488 2370941 := bbase (se 3 (by rfl) ⟨444551, by rfl⟩ : syracuseStep 2370941 = 889103) (by norm_num)
theorem B3558797 : Blo 1580488 3558797 := bbase (se 3 (by rfl) ⟨667274, by rfl⟩ : syracuseStep 3558797 = 1334549) (by norm_num)
theorem B2370965 : Blo 1580488 2370965 := bbase (se 6 (by rfl) ⟨55569, by rfl⟩ : syracuseStep 2370965 = 111139) (by norm_num)
theorem B2370989 : Blo 1580488 2370989 := bbase (se 3 (by rfl) ⟨444560, by rfl⟩ : syracuseStep 2370989 = 889121) (by norm_num)
theorem B4001197 : Blo 1580488 4001197 := bbase (se 3 (by rfl) ⟨750224, by rfl⟩ : syracuseStep 4001197 = 1500449) (by norm_num)
theorem B2371013 : Blo 1580488 2371013 := bbase (se 4 (by rfl) ⟨222282, by rfl⟩ : syracuseStep 2371013 = 444565) (by norm_num)
theorem B3558869 : Blo 1580488 3558869 := bbase (se 7 (by rfl) ⟨41705, by rfl⟩ : syracuseStep 3558869 = 83411) (by norm_num)
theorem B2371037 : Blo 1580488 2371037 := bbase (se 3 (by rfl) ⟨444569, by rfl⟩ : syracuseStep 2371037 = 889139) (by norm_num)
theorem B5336549 : Blo 1580488 5336549 := bbase (se 4 (by rfl) ⟨500301, by rfl⟩ : syracuseStep 5336549 = 1000603) (by norm_num)
theorem B2371061 : Blo 1580488 2371061 := bbase (se 5 (by rfl) ⟨111143, by rfl⟩ : syracuseStep 2371061 = 222287) (by norm_num)
theorem B2002421 : Blo 1580488 2002421 := bbase (se 5 (by rfl) ⟨93863, by rfl⟩ : syracuseStep 2002421 = 187727) (by norm_num)
theorem B8007173 : Blo 1580488 8007173 := bbase (se 4 (by rfl) ⟨750672, by rfl⟩ : syracuseStep 8007173 = 1501345) (by norm_num)
theorem B2371085 : Blo 1580488 2371085 := bbase (se 3 (by rfl) ⟨444578, by rfl⟩ : syracuseStep 2371085 = 889157) (by norm_num)
theorem B4001309 : Blo 1580488 4001309 := bbase (se 3 (by rfl) ⟨750245, by rfl⟩ : syracuseStep 4001309 = 1500491) (by norm_num)
theorem B3558941 : Blo 1580488 3558941 := bbase (se 3 (by rfl) ⟨667301, by rfl⟩ : syracuseStep 3558941 = 1334603) (by norm_num)
theorem B2371109 : Blo 1580488 2371109 := bbase (se 4 (by rfl) ⟨222291, by rfl⟩ : syracuseStep 2371109 = 444583) (by norm_num)
theorem B6008357 : Blo 1580488 6008357 := bbase (se 4 (by rfl) ⟨563283, by rfl⟩ : syracuseStep 6008357 = 1126567) (by norm_num)
theorem B2002477 : Blo 1580488 2002477 := bbase (se 3 (by rfl) ⟨375464, by rfl⟩ : syracuseStep 2002477 = 750929) (by norm_num)
theorem B2371133 : Blo 1580488 2371133 := bbase (se 3 (by rfl) ⟨444587, by rfl⟩ : syracuseStep 2371133 = 889175) (by norm_num)
theorem B2371157 : Blo 1580488 2371157 := bbase (se 8 (by rfl) ⟨13893, by rfl⟩ : syracuseStep 2371157 = 27787) (by norm_num)
theorem B43290197 : Blo 1580488 43290197 := bbase (se 8 (by rfl) ⟨253653, by rfl⟩ : syracuseStep 43290197 = 507307) (by norm_num)
theorem B3559013 : Blo 1580488 3559013 := bbase (se 4 (by rfl) ⟨333657, by rfl⟩ : syracuseStep 3559013 = 667315) (by norm_num)
theorem B2371181 : Blo 1580488 2371181 := bbase (se 3 (by rfl) ⟨444596, by rfl⟩ : syracuseStep 2371181 = 889193) (by norm_num)
theorem B4501109 : Blo 1580488 4501109 := bbase (se 5 (by rfl) ⟨210989, by rfl⟩ : syracuseStep 4501109 = 421979) (by norm_num)
theorem B2371205 : Blo 1580488 2371205 := bbase (se 4 (by rfl) ⟨222300, by rfl⟩ : syracuseStep 2371205 = 444601) (by norm_num)
theorem B2002573 : Blo 1580488 2002573 := bbase (se 3 (by rfl) ⟨375482, by rfl⟩ : syracuseStep 2002573 = 750965) (by norm_num)
theorem B2371229 : Blo 1580488 2371229 := bbase (se 3 (by rfl) ⟨444605, by rfl⟩ : syracuseStep 2371229 = 889211) (by norm_num)
theorem B3559085 : Blo 1580488 3559085 := bbase (se 3 (by rfl) ⟨667328, by rfl⟩ : syracuseStep 3559085 = 1334657) (by norm_num)
theorem B2371253 : Blo 1580488 2371253 := bbase (se 5 (by rfl) ⟨111152, by rfl⟩ : syracuseStep 2371253 = 222305) (by norm_num)
theorem B2371277 : Blo 1580488 2371277 := bbase (se 3 (by rfl) ⟨444614, by rfl⟩ : syracuseStep 2371277 = 889229) (by norm_num)
theorem B8113877 : Blo 1580488 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B4001501 : Blo 1580488 4001501 := bbase (se 3 (by rfl) ⟨750281, by rfl⟩ : syracuseStep 4001501 = 1500563) (by norm_num)
theorem B2371301 : Blo 1580488 2371301 := bbase (se 4 (by rfl) ⟨222309, by rfl⟩ : syracuseStep 2371301 = 444619) (by norm_num)
theorem B3559157 : Blo 1580488 3559157 := bbase (se 5 (by rfl) ⟨166835, by rfl⟩ : syracuseStep 3559157 = 333671) (by norm_num)
theorem B2371325 : Blo 1580488 2371325 := bbase (se 3 (by rfl) ⟨444623, by rfl⟩ : syracuseStep 2371325 = 889247) (by norm_num)
theorem B2371349 : Blo 1580488 2371349 := bbase (se 6 (by rfl) ⟨55578, by rfl⟩ : syracuseStep 2371349 = 111157) (by norm_num)
theorem B2371373 : Blo 1580488 2371373 := bbase (se 3 (by rfl) ⟨444632, by rfl⟩ : syracuseStep 2371373 = 889265) (by norm_num)
theorem B2002745 : Blo 1580488 2002745 := bbase (se 2 (by rfl) ⟨751029, by rfl⟩ : syracuseStep 2002745 = 1502059) (by norm_num)
theorem B3559229 : Blo 1580488 3559229 := bbase (se 3 (by rfl) ⟨667355, by rfl⟩ : syracuseStep 3559229 = 1334711) (by norm_num)
theorem B2371397 : Blo 1580488 2371397 := bbase (se 4 (by rfl) ⟨222318, by rfl⟩ : syracuseStep 2371397 = 444637) (by norm_num)
theorem B3002197 : Blo 1580488 3002197 := bbase (se 9 (by rfl) ⟨8795, by rfl⟩ : syracuseStep 3002197 = 17591) (by norm_num)
theorem B2371421 : Blo 1580488 2371421 := bbase (se 3 (by rfl) ⟨444641, by rfl⟩ : syracuseStep 2371421 = 889283) (by norm_num)
theorem B2002801 : Blo 1580488 2002801 := bbase (se 2 (by rfl) ⟨751050, by rfl⟩ : syracuseStep 2002801 = 1502101) (by norm_num)
theorem B2371445 : Blo 1580488 2371445 := bbase (se 5 (by rfl) ⟨111161, by rfl⟩ : syracuseStep 2371445 = 222323) (by norm_num)
theorem B3559301 : Blo 1580488 3559301 := bbase (se 4 (by rfl) ⟨333684, by rfl⟩ : syracuseStep 3559301 = 667369) (by norm_num)
theorem B2371469 : Blo 1580488 2371469 := bbase (se 3 (by rfl) ⟨444650, by rfl⟩ : syracuseStep 2371469 = 889301) (by norm_num)
theorem B5336981 : Blo 1580488 5336981 := bbase (se 6 (by rfl) ⟨125085, by rfl⟩ : syracuseStep 5336981 = 250171) (by norm_num)
theorem B5484437 : Blo 1580488 5484437 := bbase (se 6 (by rfl) ⟨128541, by rfl⟩ : syracuseStep 5484437 = 257083) (by norm_num)
theorem B2371493 : Blo 1580488 2371493 := bbase (se 4 (by rfl) ⟨222327, by rfl⟩ : syracuseStep 2371493 = 444655) (by norm_num)
theorem B2371517 : Blo 1580488 2371517 := bbase (se 3 (by rfl) ⟨444659, by rfl⟩ : syracuseStep 2371517 = 889319) (by norm_num)
theorem B3559373 : Blo 1580488 3559373 := bbase (se 3 (by rfl) ⟨667382, by rfl⟩ : syracuseStep 3559373 = 1334765) (by norm_num)
theorem B2371541 : Blo 1580488 2371541 := bbase (se 7 (by rfl) ⟨27791, by rfl⟩ : syracuseStep 2371541 = 55583) (by norm_num)
theorem B3002341 : Blo 1580488 3002341 := bbase (se 4 (by rfl) ⟨281469, by rfl⟩ : syracuseStep 3002341 = 562939) (by norm_num)
theorem B2371565 : Blo 1580488 2371565 := bbase (se 3 (by rfl) ⟨444668, by rfl⟩ : syracuseStep 2371565 = 889337) (by norm_num)
theorem B2371589 : Blo 1580488 2371589 := bbase (se 4 (by rfl) ⟨222336, by rfl⟩ : syracuseStep 2371589 = 444673) (by norm_num)
theorem B3559445 : Blo 1580488 3559445 := bbase (se 6 (by rfl) ⟨83424, by rfl⟩ : syracuseStep 3559445 = 166849) (by norm_num)
theorem B2371613 : Blo 1580488 2371613 := bbase (se 3 (by rfl) ⟨444677, by rfl⟩ : syracuseStep 2371613 = 889355) (by norm_num)
theorem B4001845 : Blo 1580488 4001845 := bbase (se 5 (by rfl) ⟨187586, by rfl⟩ : syracuseStep 4001845 = 375173) (by norm_num)
theorem B2371637 : Blo 1580488 2371637 := bbase (se 5 (by rfl) ⟨111170, by rfl⟩ : syracuseStep 2371637 = 222341) (by norm_num)
theorem B2371661 : Blo 1580488 2371661 := bbase (se 3 (by rfl) ⟨444686, by rfl⟩ : syracuseStep 2371661 = 889373) (by norm_num)
theorem B3559517 : Blo 1580488 3559517 := bbase (se 3 (by rfl) ⟨667409, by rfl⟩ : syracuseStep 3559517 = 1334819) (by norm_num)
theorem B2371685 : Blo 1580488 2371685 := bbase (se 4 (by rfl) ⟨222345, by rfl⟩ : syracuseStep 2371685 = 444691) (by norm_num)
theorem B2371709 : Blo 1580488 2371709 := bbase (se 3 (by rfl) ⟨444695, by rfl⟩ : syracuseStep 2371709 = 889391) (by norm_num)
theorem B3379325 : Blo 1580488 3379325 := bbase (se 3 (by rfl) ⟨633623, by rfl⟩ : syracuseStep 3379325 = 1267247) (by norm_num)
theorem B3002501 : Blo 1580488 3002501 := bbase (se 4 (by rfl) ⟨281484, by rfl⟩ : syracuseStep 3002501 = 562969) (by norm_num)
theorem B4059277 : Blo 1580488 4059277 := bbase (se 3 (by rfl) ⟨761114, by rfl⟩ : syracuseStep 4059277 = 1522229) (by norm_num)
theorem B2371733 : Blo 1580488 2371733 := bbase (se 6 (by rfl) ⟨55587, by rfl⟩ : syracuseStep 2371733 = 111175) (by norm_num)
theorem B4001957 : Blo 1580488 4001957 := bbase (se 4 (by rfl) ⟨375183, by rfl⟩ : syracuseStep 4001957 = 750367) (by norm_num)
theorem B3559589 : Blo 1580488 3559589 := bbase (se 4 (by rfl) ⟨333711, by rfl⟩ : syracuseStep 3559589 = 667423) (by norm_num)
theorem B2371757 : Blo 1580488 2371757 := bbase (se 3 (by rfl) ⟨444704, by rfl⟩ : syracuseStep 2371757 = 889409) (by norm_num)
theorem B5132485 : Blo 1580488 5132485 := bbase (se 4 (by rfl) ⟨481170, by rfl⟩ : syracuseStep 5132485 = 962341) (by norm_num)
theorem B2371781 : Blo 1580488 2371781 := bbase (se 4 (by rfl) ⟨222354, by rfl⟩ : syracuseStep 2371781 = 444709) (by norm_num)
theorem B13693141 : Blo 1580488 13693141 := bbase (se 7 (by rfl) ⟨160466, by rfl⟩ : syracuseStep 13693141 = 320933) (by norm_num)
theorem B2371805 : Blo 1580488 2371805 := bbase (se 3 (by rfl) ⟨444713, by rfl⟩ : syracuseStep 2371805 = 889427) (by norm_num)
theorem B3559661 : Blo 1580488 3559661 := bbase (se 3 (by rfl) ⟨667436, by rfl⟩ : syracuseStep 3559661 = 1334873) (by norm_num)
theorem B2371829 : Blo 1580488 2371829 := bbase (se 5 (by rfl) ⟨111179, by rfl⟩ : syracuseStep 2371829 = 222359) (by norm_num)
theorem B2371853 : Blo 1580488 2371853 := bbase (se 3 (by rfl) ⟨444722, by rfl⟩ : syracuseStep 2371853 = 889445) (by norm_num)
theorem B4501781 : Blo 1580488 4501781 := bbase (se 6 (by rfl) ⟨105510, by rfl⟩ : syracuseStep 4501781 = 211021) (by norm_num)
theorem B3002645 : Blo 1580488 3002645 := bbase (se 6 (by rfl) ⟨70374, by rfl⟩ : syracuseStep 3002645 = 140749) (by norm_num)
theorem B5067029 : Blo 1580488 5067029 := bbase (se 6 (by rfl) ⟨118758, by rfl⟩ : syracuseStep 5067029 = 237517) (by norm_num)
theorem B2371877 : Blo 1580488 2371877 := bbase (se 4 (by rfl) ⟨222363, by rfl⟩ : syracuseStep 2371877 = 444727) (by norm_num)
theorem B2314541 : Blo 1580488 2314541 := bbase (se 3 (by rfl) ⟨433976, by rfl⟩ : syracuseStep 2314541 = 867953) (by norm_num)
theorem B3559733 : Blo 1580488 3559733 := bbase (se 5 (by rfl) ⟨166862, by rfl⟩ : syracuseStep 3559733 = 333725) (by norm_num)
theorem B2371901 : Blo 1580488 2371901 := bbase (se 3 (by rfl) ⟨444731, by rfl⟩ : syracuseStep 2371901 = 889463) (by norm_num)
theorem B5337413 : Blo 1580488 5337413 := bbase (se 4 (by rfl) ⟨500382, by rfl⟩ : syracuseStep 5337413 = 1000765) (by norm_num)
theorem B13873493 : Blo 1580488 13873493 := bbase (se 10 (by rfl) ⟨20322, by rfl⟩ : syracuseStep 13873493 = 40645) (by norm_num)
theorem B2371925 : Blo 1580488 2371925 := bbase (se 10 (by rfl) ⟨3474, by rfl⟩ : syracuseStep 2371925 = 6949) (by norm_num)
theorem B4002149 : Blo 1580488 4002149 := bbase (se 4 (by rfl) ⟨375201, by rfl⟩ : syracuseStep 4002149 = 750403) (by norm_num)
theorem B2371949 : Blo 1580488 2371949 := bbase (se 3 (by rfl) ⟨444740, by rfl⟩ : syracuseStep 2371949 = 889481) (by norm_num)
theorem B3379565 : Blo 1580488 3379565 := bbase (se 3 (by rfl) ⟨633668, by rfl⟩ : syracuseStep 3379565 = 1267337) (by norm_num)
theorem B3559805 : Blo 1580488 3559805 := bbase (se 3 (by rfl) ⟨667463, by rfl⟩ : syracuseStep 3559805 = 1334927) (by norm_num)
theorem B4059517 : Blo 1580488 4059517 := bbase (se 3 (by rfl) ⟨761159, by rfl⟩ : syracuseStep 4059517 = 1522319) (by norm_num)
theorem B2371973 : Blo 1580488 2371973 := bbase (se 4 (by rfl) ⟨222372, by rfl⟩ : syracuseStep 2371973 = 444745) (by norm_num)
theorem B3658133 : Blo 1580488 3658133 := bbase (se 6 (by rfl) ⟨85737, by rfl⟩ : syracuseStep 3658133 = 171475) (by norm_num)
theorem B2371997 : Blo 1580488 2371997 := bbase (se 3 (by rfl) ⟨444749, by rfl⟩ : syracuseStep 2371997 = 889499) (by norm_num)
theorem B8114597 : Blo 1580488 8114597 := bbase (se 4 (by rfl) ⟨760743, by rfl⟩ : syracuseStep 8114597 = 1521487) (by norm_num)
theorem B2372021 : Blo 1580488 2372021 := bbase (se 5 (by rfl) ⟨111188, by rfl⟩ : syracuseStep 2372021 = 222377) (by norm_num)
theorem B3559877 : Blo 1580488 3559877 := bbase (se 4 (by rfl) ⟨333738, by rfl⟩ : syracuseStep 3559877 = 667477) (by norm_num)
theorem B2372045 : Blo 1580488 2372045 := bbase (se 3 (by rfl) ⟨444758, by rfl⟩ : syracuseStep 2372045 = 889517) (by norm_num)
theorem B2372069 : Blo 1580488 2372069 := bbase (se 4 (by rfl) ⟨222381, by rfl⟩ : syracuseStep 2372069 = 444763) (by norm_num)
theorem B2372093 : Blo 1580488 2372093 := bbase (se 3 (by rfl) ⟨444767, by rfl⟩ : syracuseStep 2372093 = 889535) (by norm_num)
theorem B3559949 : Blo 1580488 3559949 := bbase (se 3 (by rfl) ⟨667490, by rfl⟩ : syracuseStep 3559949 = 1334981) (by norm_num)
theorem B20263445 : Blo 1580488 20263445 := bbase (se 6 (by rfl) ⟨474924, by rfl⟩ : syracuseStep 20263445 = 949849) (by norm_num)
theorem B2372117 : Blo 1580488 2372117 := bbase (se 6 (by rfl) ⟨55596, by rfl⟩ : syracuseStep 2372117 = 111193) (by norm_num)
theorem B2372141 : Blo 1580488 2372141 := bbase (se 3 (by rfl) ⟨444776, by rfl⟩ : syracuseStep 2372141 = 889553) (by norm_num)
theorem B3002933 : Blo 1580488 3002933 := bbase (se 5 (by rfl) ⟨140762, by rfl⟩ : syracuseStep 3002933 = 281525) (by norm_num)
theorem B2372165 : Blo 1580488 2372165 := bbase (se 4 (by rfl) ⟨222390, by rfl⟩ : syracuseStep 2372165 = 444781) (by norm_num)
theorem B3560021 : Blo 1580488 3560021 := bbase (se 8 (by rfl) ⟨20859, by rfl⟩ : syracuseStep 3560021 = 41719) (by norm_num)
theorem B1602137 : Blo 1580488 1602137 := bbase (se 2 (by rfl) ⟨600801, by rfl⟩ : syracuseStep 1602137 = 1201603) (by norm_num)
theorem B2372189 : Blo 1580488 2372189 := bbase (se 3 (by rfl) ⟨444785, by rfl⟩ : syracuseStep 2372189 = 889571) (by norm_num)
theorem B2372213 : Blo 1580488 2372213 := bbase (se 5 (by rfl) ⟨111197, by rfl⟩ : syracuseStep 2372213 = 222395) (by norm_num)
theorem B2372237 : Blo 1580488 2372237 := bbase (se 3 (by rfl) ⟨444794, by rfl⟩ : syracuseStep 2372237 = 889589) (by norm_num)
theorem B3560093 : Blo 1580488 3560093 := bbase (se 3 (by rfl) ⟨667517, by rfl⟩ : syracuseStep 3560093 = 1335035) (by norm_num)
theorem B2372261 : Blo 1580488 2372261 := bbase (se 4 (by rfl) ⟨222399, by rfl⟩ : syracuseStep 2372261 = 444799) (by norm_num)
theorem B2667181 : Blo 1580488 2667181 := bbase (se 3 (by rfl) ⟨500096, by rfl⟩ : syracuseStep 2667181 = 1000193) (by norm_num)
theorem B6410933 : Blo 1580488 6410933 := bbase (se 5 (by rfl) ⟨300512, by rfl⟩ : syracuseStep 6410933 = 601025) (by norm_num)
theorem B4002493 : Blo 1580488 4002493 := bbase (se 3 (by rfl) ⟨750467, by rfl⟩ : syracuseStep 4002493 = 1500935) (by norm_num)
theorem B2372285 : Blo 1580488 2372285 := bbase (se 3 (by rfl) ⟨444803, by rfl⟩ : syracuseStep 2372285 = 889607) (by norm_num)
theorem B4502213 : Blo 1580488 4502213 := bbase (se 4 (by rfl) ⟨422082, by rfl⟩ : syracuseStep 4502213 = 844165) (by norm_num)
theorem B3003085 : Blo 1580488 3003085 := bbase (se 3 (by rfl) ⟨563078, by rfl⟩ : syracuseStep 3003085 = 1126157) (by norm_num)
theorem B2372309 : Blo 1580488 2372309 := bbase (se 7 (by rfl) ⟨27800, by rfl⟩ : syracuseStep 2372309 = 55601) (by norm_num)
theorem B3560165 : Blo 1580488 3560165 := bbase (se 4 (by rfl) ⟨333765, by rfl⟩ : syracuseStep 3560165 = 667531) (by norm_num)
theorem B2372333 : Blo 1580488 2372333 := bbase (se 3 (by rfl) ⟨444812, by rfl⟩ : syracuseStep 2372333 = 889625) (by norm_num)
theorem B5337845 : Blo 1580488 5337845 := bbase (se 5 (by rfl) ⟨250211, by rfl⟩ : syracuseStep 5337845 = 500423) (by norm_num)
theorem B2667269 : Blo 1580488 2667269 := bbase (se 4 (by rfl) ⟨250056, by rfl⟩ : syracuseStep 2667269 = 500113) (by norm_num)
theorem B2372357 : Blo 1580488 2372357 := bbase (se 4 (by rfl) ⟨222408, by rfl⟩ : syracuseStep 2372357 = 444817) (by norm_num)
theorem B8008469 : Blo 1580488 8008469 := bbase (se 6 (by rfl) ⟨187698, by rfl⟩ : syracuseStep 8008469 = 375397) (by norm_num)
theorem B2372381 : Blo 1580488 2372381 := bbase (se 3 (by rfl) ⟨444821, by rfl⟩ : syracuseStep 2372381 = 889643) (by norm_num)
theorem B4002605 : Blo 1580488 4002605 := bbase (se 3 (by rfl) ⟨750488, by rfl⟩ : syracuseStep 4002605 = 1500977) (by norm_num)
theorem B3560237 : Blo 1580488 3560237 := bbase (se 3 (by rfl) ⟨667544, by rfl⟩ : syracuseStep 3560237 = 1335089) (by norm_num)
theorem B2372405 : Blo 1580488 2372405 := bbase (se 5 (by rfl) ⟨111206, by rfl⟩ : syracuseStep 2372405 = 222413) (by norm_num)
theorem B2372429 : Blo 1580488 2372429 := bbase (se 3 (by rfl) ⟨444830, by rfl⟩ : syracuseStep 2372429 = 889661) (by norm_num)
theorem B2372453 : Blo 1580488 2372453 := bbase (se 4 (by rfl) ⟨222417, by rfl⟩ : syracuseStep 2372453 = 444835) (by norm_num)
theorem B3560309 : Blo 1580488 3560309 := bbase (se 5 (by rfl) ⟨166889, by rfl⟩ : syracuseStep 3560309 = 333779) (by norm_num)
theorem B2372477 : Blo 1580488 2372477 := bbase (se 3 (by rfl) ⟨444839, by rfl⟩ : syracuseStep 2372477 = 889679) (by norm_num)
theorem B3208061 : Blo 1580488 3208061 := bbase (se 3 (by rfl) ⟨601511, by rfl⟩ : syracuseStep 3208061 = 1203023) (by norm_num)
theorem B1602433 : Blo 1580488 1602433 := bbase (se 2 (by rfl) ⟨600912, by rfl⟩ : syracuseStep 1602433 = 1201825) (by norm_num)
theorem B2667397 : Blo 1580488 2667397 := bbase (se 4 (by rfl) ⟨250068, by rfl⟩ : syracuseStep 2667397 = 500137) (by norm_num)
theorem B5411717 : Blo 1580488 5411717 := bbase (se 4 (by rfl) ⟨507348, by rfl⟩ : syracuseStep 5411717 = 1014697) (by norm_num)
theorem B2372501 : Blo 1580488 2372501 := bbase (se 6 (by rfl) ⟨55605, by rfl⟩ : syracuseStep 2372501 = 111211) (by norm_num)
theorem B1602473 : Blo 1580488 1602473 := bbase (se 2 (by rfl) ⟨600927, by rfl⟩ : syracuseStep 1602473 = 1201855) (by norm_num)
theorem B2372525 : Blo 1580488 2372525 := bbase (se 3 (by rfl) ⟨444848, by rfl⟩ : syracuseStep 2372525 = 889697) (by norm_num)
theorem B3560381 : Blo 1580488 3560381 := bbase (se 3 (by rfl) ⟨667571, by rfl⟩ : syracuseStep 3560381 = 1335143) (by norm_num)
theorem B2372549 : Blo 1580488 2372549 := bbase (se 4 (by rfl) ⟨222426, by rfl⟩ : syracuseStep 2372549 = 444853) (by norm_num)
theorem B3797965 : Blo 1580488 3797965 := bbase (se 3 (by rfl) ⟨712118, by rfl⟩ : syracuseStep 3797965 = 1424237) (by norm_num)
theorem B25654229 : Blo 1580488 25654229 := bbase (se 7 (by rfl) ⟨300635, by rfl⟩ : syracuseStep 25654229 = 601271) (by norm_num)
theorem B2667485 : Blo 1580488 2667485 := bbase (se 3 (by rfl) ⟨500153, by rfl⟩ : syracuseStep 2667485 = 1000307) (by norm_num)
theorem B2372573 : Blo 1580488 2372573 := bbase (se 3 (by rfl) ⟨444857, by rfl⟩ : syracuseStep 2372573 = 889715) (by norm_num)
theorem B4002797 : Blo 1580488 4002797 := bbase (se 3 (by rfl) ⟨750524, by rfl⟩ : syracuseStep 4002797 = 1501049) (by norm_num)
theorem B9008117 : Blo 1580488 9008117 := bbase (se 5 (by rfl) ⟨422255, by rfl⟩ : syracuseStep 9008117 = 844511) (by norm_num)
theorem B2372597 : Blo 1580488 2372597 := bbase (se 5 (by rfl) ⟨111215, by rfl⟩ : syracuseStep 2372597 = 222431) (by norm_num)
theorem B2028541 : Blo 1580488 2028541 := bbase (se 3 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 2028541 = 760703) (by norm_num)
theorem B3003389 : Blo 1580488 3003389 := bbase (se 3 (by rfl) ⟨563135, by rfl⟩ : syracuseStep 3003389 = 1126271) (by norm_num)
theorem B3560453 : Blo 1580488 3560453 := bbase (se 4 (by rfl) ⟨333792, by rfl⟩ : syracuseStep 3560453 = 667585) (by norm_num)
theorem B2372621 : Blo 1580488 2372621 := bbase (se 3 (by rfl) ⟨444866, by rfl⟩ : syracuseStep 2372621 = 889733) (by norm_num)
theorem B2372645 : Blo 1580488 2372645 := bbase (se 4 (by rfl) ⟨222435, by rfl⟩ : syracuseStep 2372645 = 444871) (by norm_num)
theorem B2372669 : Blo 1580488 2372669 := bbase (se 3 (by rfl) ⟨444875, by rfl⟩ : syracuseStep 2372669 = 889751) (by norm_num)
theorem B3560525 : Blo 1580488 3560525 := bbase (se 3 (by rfl) ⟨667598, by rfl⟩ : syracuseStep 3560525 = 1335197) (by norm_num)
theorem B2372693 : Blo 1580488 2372693 := bbase (se 8 (by rfl) ⟨13902, by rfl⟩ : syracuseStep 2372693 = 27805) (by norm_num)
theorem B2667613 : Blo 1580488 2667613 := bbase (se 3 (by rfl) ⟨500177, by rfl⟩ : syracuseStep 2667613 = 1000355) (by norm_num)
theorem B2372717 : Blo 1580488 2372717 := bbase (se 3 (by rfl) ⟨444884, by rfl⟩ : syracuseStep 2372717 = 889769) (by norm_num)
theorem B2372741 : Blo 1580488 2372741 := bbase (se 4 (by rfl) ⟨222444, by rfl⟩ : syracuseStep 2372741 = 444889) (by norm_num)
theorem B3560597 : Blo 1580488 3560597 := bbase (se 6 (by rfl) ⟨83451, by rfl⟩ : syracuseStep 3560597 = 166903) (by norm_num)
theorem B2372765 : Blo 1580488 2372765 := bbase (se 3 (by rfl) ⟨444893, by rfl⟩ : syracuseStep 2372765 = 889787) (by norm_num)
theorem B1602721 : Blo 1580488 1602721 := bbase (se 2 (by rfl) ⟨601020, by rfl⟩ : syracuseStep 1602721 = 1202041) (by norm_num)
theorem B5338277 : Blo 1580488 5338277 := bbase (se 4 (by rfl) ⟨500463, by rfl⟩ : syracuseStep 5338277 = 1000927) (by norm_num)
theorem B3798197 : Blo 1580488 3798197 := bbase (se 5 (by rfl) ⟨178040, by rfl⟩ : syracuseStep 3798197 = 356081) (by norm_num)
theorem B2667701 : Blo 1580488 2667701 := bbase (se 5 (by rfl) ⟨125048, by rfl⟩ : syracuseStep 2667701 = 250097) (by norm_num)
theorem B2372789 : Blo 1580488 2372789 := bbase (se 5 (by rfl) ⟨111224, by rfl⟩ : syracuseStep 2372789 = 222449) (by norm_num)
theorem B1602757 : Blo 1580488 1602757 := bbase (se 4 (by rfl) ⟨150258, by rfl⟩ : syracuseStep 1602757 = 300517) (by norm_num)
theorem B2372813 : Blo 1580488 2372813 := bbase (se 3 (by rfl) ⟨444902, by rfl⟩ : syracuseStep 2372813 = 889805) (by norm_num)
theorem B2372837 : Blo 1580488 2372837 := bbase (se 4 (by rfl) ⟨222453, by rfl⟩ : syracuseStep 2372837 = 444907) (by norm_num)
theorem B2372861 : Blo 1580488 2372861 := bbase (se 3 (by rfl) ⟨444911, by rfl⟩ : syracuseStep 2372861 = 889823) (by norm_num)
theorem B2372885 : Blo 1580488 2372885 := bbase (se 6 (by rfl) ⟨55614, by rfl⟩ : syracuseStep 2372885 = 111229) (by norm_num)
theorem B2372909 : Blo 1580488 2372909 := bbase (se 3 (by rfl) ⟨444920, by rfl⟩ : syracuseStep 2372909 = 889841) (by norm_num)
theorem B2667829 : Blo 1580488 2667829 := bbase (se 5 (by rfl) ⟨125054, by rfl⟩ : syracuseStep 2667829 = 250109) (by norm_num)
theorem B2405693 : Blo 1580488 2405693 := bbase (se 3 (by rfl) ⟨451067, by rfl⟩ : syracuseStep 2405693 = 902135) (by norm_num)
theorem B4003141 : Blo 1580488 4003141 := bbase (se 4 (by rfl) ⟨375294, by rfl⟩ : syracuseStep 4003141 = 750589) (by norm_num)
theorem B2372933 : Blo 1580488 2372933 := bbase (se 4 (by rfl) ⟨222462, by rfl⟩ : syracuseStep 2372933 = 444925) (by norm_num)
theorem B2372957 : Blo 1580488 2372957 := bbase (se 3 (by rfl) ⟨444929, by rfl⟩ : syracuseStep 2372957 = 889859) (by norm_num)
theorem B2372981 : Blo 1580488 2372981 := bbase (se 5 (by rfl) ⟨111233, by rfl⟩ : syracuseStep 2372981 = 222467) (by norm_num)
theorem B2667917 : Blo 1580488 2667917 := bbase (se 3 (by rfl) ⟨500234, by rfl⟩ : syracuseStep 2667917 = 1000469) (by norm_num)
theorem B2373005 : Blo 1580488 2373005 := bbase (se 3 (by rfl) ⟨444938, by rfl⟩ : syracuseStep 2373005 = 889877) (by norm_num)
theorem B2373029 : Blo 1580488 2373029 := bbase (se 4 (by rfl) ⟨222471, by rfl⟩ : syracuseStep 2373029 = 444943) (by norm_num)
theorem B4502965 : Blo 1580488 4502965 := bbase (se 5 (by rfl) ⟨211076, by rfl⟩ : syracuseStep 4502965 = 422153) (by norm_num)
theorem B4003253 : Blo 1580488 4003253 := bbase (se 5 (by rfl) ⟨187652, by rfl⟩ : syracuseStep 4003253 = 375305) (by norm_num)
theorem B2373053 : Blo 1580488 2373053 := bbase (se 3 (by rfl) ⟨444947, by rfl⟩ : syracuseStep 2373053 = 889895) (by norm_num)
theorem B2373077 : Blo 1580488 2373077 := bbase (se 7 (by rfl) ⟨27809, by rfl⟩ : syracuseStep 2373077 = 55619) (by norm_num)
theorem B1603049 : Blo 1580488 1603049 := bbase (se 2 (by rfl) ⟨601143, by rfl⟩ : syracuseStep 1603049 = 1202287) (by norm_num)
theorem B2373101 : Blo 1580488 2373101 := bbase (se 3 (by rfl) ⟨444956, by rfl⟩ : syracuseStep 2373101 = 889913) (by norm_num)
theorem B2029045 : Blo 1580488 2029045 := bbase (se 5 (by rfl) ⟨95111, by rfl⟩ : syracuseStep 2029045 = 190223) (by norm_num)
theorem B2373125 : Blo 1580488 2373125 := bbase (se 4 (by rfl) ⟨222480, by rfl⟩ : syracuseStep 2373125 = 444961) (by norm_num)
theorem B2668045 : Blo 1580488 2668045 := bbase (se 3 (by rfl) ⟨500258, by rfl⟩ : syracuseStep 2668045 = 1000517) (by norm_num)
theorem B2373149 : Blo 1580488 2373149 := bbase (se 3 (by rfl) ⟨444965, by rfl⟩ : syracuseStep 2373149 = 889931) (by norm_num)
theorem B2373173 : Blo 1580488 2373173 := bbase (se 5 (by rfl) ⟨111242, by rfl⟩ : syracuseStep 2373173 = 222485) (by norm_num)
theorem B3798589 : Blo 1580488 3798589 := bbase (se 3 (by rfl) ⟨712235, by rfl⟩ : syracuseStep 3798589 = 1424471) (by norm_num)
theorem B2373197 : Blo 1580488 2373197 := bbase (se 3 (by rfl) ⟨444974, by rfl⟩ : syracuseStep 2373197 = 889949) (by norm_num)
theorem B4806229 : Blo 1580488 4806229 := bbase (se 8 (by rfl) ⟨28161, by rfl⟩ : syracuseStep 4806229 = 56323) (by norm_num)
theorem B73021013 : Blo 1580488 73021013 := bbase (se 8 (by rfl) ⟨427857, by rfl⟩ : syracuseStep 73021013 = 855715) (by norm_num)
theorem B5338709 : Blo 1580488 5338709 := bbase (se 8 (by rfl) ⟨31281, by rfl⟩ : syracuseStep 5338709 = 62563) (by norm_num)
theorem B2668133 : Blo 1580488 2668133 := bbase (se 4 (by rfl) ⟨250137, by rfl⟩ : syracuseStep 2668133 = 500275) (by norm_num)
theorem B2373221 : Blo 1580488 2373221 := bbase (se 4 (by rfl) ⟨222489, by rfl⟩ : syracuseStep 2373221 = 444979) (by norm_num)
theorem B4003445 : Blo 1580488 4003445 := bbase (se 5 (by rfl) ⟨187661, by rfl⟩ : syracuseStep 4003445 = 375323) (by norm_num)
theorem B2373245 : Blo 1580488 2373245 := bbase (se 3 (by rfl) ⟨444983, by rfl⟩ : syracuseStep 2373245 = 889967) (by norm_num)
theorem B2250389 : Blo 1580488 2250389 := bbase (se 6 (by rfl) ⟨52743, by rfl⟩ : syracuseStep 2250389 = 105487) (by norm_num)
theorem B7214741 : Blo 1580488 7214741 := bbase (se 6 (by rfl) ⟨169095, by rfl⟩ : syracuseStep 7214741 = 338191) (by norm_num)
theorem B21649045 : Blo 1580488 21649045 := bbase (se 6 (by rfl) ⟨507399, by rfl⟩ : syracuseStep 21649045 = 1014799) (by norm_num)
theorem B2373269 : Blo 1580488 2373269 := bbase (se 6 (by rfl) ⟨55623, by rfl⟩ : syracuseStep 2373269 = 111247) (by norm_num)
theorem B2373293 : Blo 1580488 2373293 := bbase (se 3 (by rfl) ⟨444992, by rfl⟩ : syracuseStep 2373293 = 889985) (by norm_num)
theorem B2373317 : Blo 1580488 2373317 := bbase (se 4 (by rfl) ⟨222498, by rfl⟩ : syracuseStep 2373317 = 444997) (by norm_num)
theorem B2373341 : Blo 1580488 2373341 := bbase (se 3 (by rfl) ⟨445001, by rfl⟩ : syracuseStep 2373341 = 890003) (by norm_num)
theorem B2668261 : Blo 1580488 2668261 := bbase (se 4 (by rfl) ⟨250149, by rfl⟩ : syracuseStep 2668261 = 500299) (by norm_num)
theorem B3004141 : Blo 1580488 3004141 := bbase (se 3 (by rfl) ⟨563276, by rfl⟩ : syracuseStep 3004141 = 1126553) (by norm_num)
theorem B2373365 : Blo 1580488 2373365 := bbase (se 5 (by rfl) ⟨111251, by rfl⟩ : syracuseStep 2373365 = 222503) (by norm_num)
theorem B2373389 : Blo 1580488 2373389 := bbase (se 3 (by rfl) ⟨445010, by rfl⟩ : syracuseStep 2373389 = 890021) (by norm_num)
theorem B2373413 : Blo 1580488 2373413 := bbase (se 4 (by rfl) ⟨222507, by rfl⟩ : syracuseStep 2373413 = 445015) (by norm_num)
theorem B2668349 : Blo 1580488 2668349 := bbase (se 3 (by rfl) ⟨500315, by rfl⟩ : syracuseStep 2668349 = 1000631) (by norm_num)
theorem B2373437 : Blo 1580488 2373437 := bbase (se 3 (by rfl) ⟨445019, by rfl⟩ : syracuseStep 2373437 = 890039) (by norm_num)
theorem B5699413 : Blo 1580488 5699413 := bbase (se 9 (by rfl) ⟨16697, by rfl⟩ : syracuseStep 5699413 = 33395) (by norm_num)
theorem B2373461 : Blo 1580488 2373461 := bbase (se 9 (by rfl) ⟨6953, by rfl⟩ : syracuseStep 2373461 = 13907) (by norm_num)
theorem B2373485 : Blo 1580488 2373485 := bbase (se 3 (by rfl) ⟨445028, by rfl⟩ : syracuseStep 2373485 = 890057) (by norm_num)
theorem B2373509 : Blo 1580488 2373509 := bbase (se 4 (by rfl) ⟨222516, by rfl⟩ : syracuseStep 2373509 = 445033) (by norm_num)
theorem B2373533 : Blo 1580488 2373533 := bbase (se 3 (by rfl) ⟨445037, by rfl⟩ : syracuseStep 2373533 = 890075) (by norm_num)
theorem B2373557 : Blo 1580488 2373557 := bbase (se 5 (by rfl) ⟨111260, by rfl⟩ : syracuseStep 2373557 = 222521) (by norm_num)
theorem B2668477 : Blo 1580488 2668477 := bbase (se 3 (by rfl) ⟨500339, by rfl⟩ : syracuseStep 2668477 = 1000679) (by norm_num)
theorem B4003789 : Blo 1580488 4003789 := bbase (se 3 (by rfl) ⟨750710, by rfl⟩ : syracuseStep 4003789 = 1501421) (by norm_num)
theorem B2373581 : Blo 1580488 2373581 := bbase (se 3 (by rfl) ⟨445046, by rfl⟩ : syracuseStep 2373581 = 890093) (by norm_num)
theorem B2373605 : Blo 1580488 2373605 := bbase (se 4 (by rfl) ⟨222525, by rfl⟩ : syracuseStep 2373605 = 445051) (by norm_num)
theorem B2373629 : Blo 1580488 2373629 := bbase (se 3 (by rfl) ⟨445055, by rfl⟩ : syracuseStep 2373629 = 890111) (by norm_num)
theorem B6002693 : Blo 1580488 6002693 := bbase (se 4 (by rfl) ⟨562752, by rfl⟩ : syracuseStep 6002693 = 1125505) (by norm_num)
theorem B5339141 : Blo 1580488 5339141 := bbase (se 4 (by rfl) ⟨500544, by rfl⟩ : syracuseStep 5339141 = 1001089) (by norm_num)
theorem B14424085 : Blo 1580488 14424085 := bbase (se 6 (by rfl) ⟨338064, by rfl⟩ : syracuseStep 14424085 = 676129) (by norm_num)
theorem B2668565 : Blo 1580488 2668565 := bbase (se 6 (by rfl) ⟨62544, by rfl⟩ : syracuseStep 2668565 = 125089) (by norm_num)
theorem B2373653 : Blo 1580488 2373653 := bbase (se 6 (by rfl) ⟨55632, by rfl⟩ : syracuseStep 2373653 = 111265) (by norm_num)
theorem B8009765 : Blo 1580488 8009765 := bbase (se 4 (by rfl) ⟨750915, by rfl⟩ : syracuseStep 8009765 = 1501831) (by norm_num)
theorem B2373677 : Blo 1580488 2373677 := bbase (se 3 (by rfl) ⟨445064, by rfl⟩ : syracuseStep 2373677 = 890129) (by norm_num)
theorem B4003901 : Blo 1580488 4003901 := bbase (se 3 (by rfl) ⟨750731, by rfl⟩ : syracuseStep 4003901 = 1501463) (by norm_num)
theorem B2373701 : Blo 1580488 2373701 := bbase (se 4 (by rfl) ⟨222534, by rfl⟩ : syracuseStep 2373701 = 445069) (by norm_num)
theorem B2373725 : Blo 1580488 2373725 := bbase (se 3 (by rfl) ⟨445073, by rfl⟩ : syracuseStep 2373725 = 890147) (by norm_num)
theorem B5699717 : Blo 1580488 5699717 := bbase (se 4 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 5699717 = 1068697) (by norm_num)
theorem B2668693 : Blo 1580488 2668693 := bbase (se 6 (by rfl) ⟨62547, by rfl⟩ : syracuseStep 2668693 = 125095) (by norm_num)
theorem B6756533 : Blo 1580488 6756533 := bbase (se 5 (by rfl) ⟨316712, by rfl⟩ : syracuseStep 6756533 = 633425) (by norm_num)
theorem B2283709 : Blo 1580488 2283709 := bbase (se 3 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 2283709 = 856391) (by norm_num)
theorem B2668781 : Blo 1580488 2668781 := bbase (se 3 (by rfl) ⟨500396, by rfl⟩ : syracuseStep 2668781 = 1000793) (by norm_num)
theorem B4004093 : Blo 1580488 4004093 := bbase (se 3 (by rfl) ⟨750767, by rfl⟩ : syracuseStep 4004093 = 1501535) (by norm_num)
theorem B6002981 : Blo 1580488 6002981 := bbase (se 4 (by rfl) ⟨562779, by rfl⟩ : syracuseStep 6002981 = 1125559) (by norm_num)
theorem B1603901 : Blo 1580488 1603901 := bbase (se 3 (by rfl) ⟨300731, by rfl⟩ : syracuseStep 1603901 = 601463) (by norm_num)
theorem B10819925 : Blo 1580488 10819925 := bbase (se 10 (by rfl) ⟨15849, by rfl⟩ : syracuseStep 10819925 = 31699) (by norm_num)
theorem B2668909 : Blo 1580488 2668909 := bbase (se 3 (by rfl) ⟨500420, by rfl⟩ : syracuseStep 2668909 = 1000841) (by norm_num)
theorem B2136469 : Blo 1580488 2136469 := bbase (se 6 (by rfl) ⟨50073, by rfl⟩ : syracuseStep 2136469 = 100147) (by norm_num)
theorem B5339573 : Blo 1580488 5339573 := bbase (se 5 (by rfl) ⟨250292, by rfl⟩ : syracuseStep 5339573 = 500585) (by norm_num)
theorem B8001989 : Blo 1580488 8001989 := bbase (se 4 (by rfl) ⟨750186, by rfl⟩ : syracuseStep 8001989 = 1500373) (by norm_num)
theorem B2668997 : Blo 1580488 2668997 := bbase (se 4 (by rfl) ⟨250218, by rfl⟩ : syracuseStep 2668997 = 500437) (by norm_num)
theorem B2669125 : Blo 1580488 2669125 := bbase (se 4 (by rfl) ⟨250230, by rfl⟩ : syracuseStep 2669125 = 500461) (by norm_num)
theorem B4004437 : Blo 1580488 4004437 := bbase (se 8 (by rfl) ⟨23463, by rfl⟩ : syracuseStep 4004437 = 46927) (by norm_num)
theorem B3799685 : Blo 1580488 3799685 := bbase (se 4 (by rfl) ⟨356220, by rfl⟩ : syracuseStep 3799685 = 712441) (by norm_num)
theorem B2669213 : Blo 1580488 2669213 := bbase (se 3 (by rfl) ⟨500477, by rfl⟩ : syracuseStep 2669213 = 1000955) (by norm_num)
theorem B4004549 : Blo 1580488 4004549 := bbase (se 4 (by rfl) ⟨375426, by rfl⟩ : syracuseStep 4004549 = 750853) (by norm_num)
theorem B2669341 : Blo 1580488 2669341 := bbase (se 3 (by rfl) ⟨500501, by rfl⟩ : syracuseStep 2669341 = 1001003) (by norm_num)
theorem B4275013 : Blo 1580488 4275013 := bbase (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) (by norm_num)
theorem B5340005 : Blo 1580488 5340005 := bbase (se 4 (by rfl) ⟨500625, by rfl⟩ : syracuseStep 5340005 = 1001251) (by norm_num)
theorem B2669429 : Blo 1580488 2669429 := bbase (se 5 (by rfl) ⟨125129, by rfl⟩ : syracuseStep 2669429 = 250259) (by norm_num)
theorem B4004741 : Blo 1580488 4004741 := bbase (se 4 (by rfl) ⟨375444, by rfl⟩ : syracuseStep 4004741 = 750889) (by norm_num)
theorem B3799973 : Blo 1580488 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B1899497 : Blo 1580488 1899497 := bbase (se 2 (by rfl) ⟨712311, by rfl⟩ : syracuseStep 1899497 = 1424623) (by norm_num)
theorem B2669557 : Blo 1580488 2669557 := bbase (se 5 (by rfl) ⟨125135, by rfl⟩ : syracuseStep 2669557 = 250271) (by norm_num)
theorem B2251813 : Blo 1580488 2251813 := bbase (se 4 (by rfl) ⟨211107, by rfl⟩ : syracuseStep 2251813 = 422215) (by norm_num)
theorem B2669645 : Blo 1580488 2669645 := bbase (se 3 (by rfl) ⟨500558, by rfl⟩ : syracuseStep 2669645 = 1001117) (by norm_num)
theorem B2669773 : Blo 1580488 2669773 := bbase (se 3 (by rfl) ⟨500582, by rfl⟩ : syracuseStep 2669773 = 1001165) (by norm_num)
theorem B4005085 : Blo 1580488 4005085 := bbase (se 3 (by rfl) ⟨750953, by rfl⟩ : syracuseStep 4005085 = 1501907) (by norm_num)
theorem B5340437 : Blo 1580488 5340437 := bbase (se 6 (by rfl) ⟨125166, by rfl⟩ : syracuseStep 5340437 = 250333) (by norm_num)
theorem B5135653 : Blo 1580488 5135653 := bbase (se 4 (by rfl) ⟨481467, by rfl⟩ : syracuseStep 5135653 = 962935) (by norm_num)
theorem B2669861 : Blo 1580488 2669861 := bbase (se 4 (by rfl) ⟨250299, by rfl⟩ : syracuseStep 2669861 = 500599) (by norm_num)
theorem B8011061 : Blo 1580488 8011061 := bbase (se 5 (by rfl) ⟨375518, by rfl⟩ : syracuseStep 8011061 = 751037) (by norm_num)
theorem B4005197 : Blo 1580488 4005197 := bbase (se 3 (by rfl) ⟨750974, by rfl⟩ : syracuseStep 4005197 = 1501949) (by norm_num)
theorem B13688149 : Blo 1580488 13688149 := bbase (se 11 (by rfl) ⟨10025, by rfl⟩ : syracuseStep 13688149 = 20051) (by norm_num)
theorem B14433653 : Blo 1580488 14433653 := bbase (se 5 (by rfl) ⟨676577, by rfl⟩ : syracuseStep 14433653 = 1353155) (by norm_num)
theorem B18013589 : Blo 1580488 18013589 := bbase (se 6 (by rfl) ⟨422193, by rfl⟩ : syracuseStep 18013589 = 844387) (by norm_num)
theorem B5709221 : Blo 1580488 5709221 := bbase (se 4 (by rfl) ⟨535239, by rfl⟩ : syracuseStep 5709221 = 1070479) (by norm_num)
theorem B2669989 : Blo 1580488 2669989 := bbase (se 4 (by rfl) ⟨250311, by rfl⟩ : syracuseStep 2669989 = 500623) (by norm_num)
theorem B6004165 : Blo 1580488 6004165 := bbase (se 4 (by rfl) ⟨562890, by rfl⟩ : syracuseStep 6004165 = 1125781) (by norm_num)
theorem B2670077 : Blo 1580488 2670077 := bbase (se 3 (by rfl) ⟨500639, by rfl⟩ : syracuseStep 2670077 = 1001279) (by norm_num)
theorem B4005389 : Blo 1580488 4005389 := bbase (se 3 (by rfl) ⟨751010, by rfl⟩ : syracuseStep 4005389 = 1502021) (by norm_num)
theorem B2252405 : Blo 1580488 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B2670205 : Blo 1580488 2670205 := bbase (se 3 (by rfl) ⟨500663, by rfl⟩ : syracuseStep 2670205 = 1001327) (by norm_num)
theorem B1900217 : Blo 1580488 1900217 := bbase (se 2 (by rfl) ⟨712581, by rfl⟩ : syracuseStep 1900217 = 1425163) (by norm_num)
theorem B2850493 : Blo 1580488 2850493 := bbase (se 3 (by rfl) ⟨534467, by rfl⟩ : syracuseStep 2850493 = 1068935) (by norm_num)
theorem B2252485 : Blo 1580488 2252485 := bbase (se 4 (by rfl) ⟨211170, by rfl⟩ : syracuseStep 2252485 = 422341) (by norm_num)
theorem B5340869 : Blo 1580488 5340869 := bbase (se 4 (by rfl) ⟨500706, by rfl⟩ : syracuseStep 5340869 = 1001413) (by norm_num)
theorem B8003285 : Blo 1580488 8003285 := bbase (se 7 (by rfl) ⟨93788, by rfl⟩ : syracuseStep 8003285 = 187577) (by norm_num)
theorem B2670293 : Blo 1580488 2670293 := bbase (se 7 (by rfl) ⟨31292, by rfl⟩ : syracuseStep 2670293 = 62585) (by norm_num)
theorem B6004469 : Blo 1580488 6004469 := bbase (se 5 (by rfl) ⟨281459, by rfl⟩ : syracuseStep 6004469 = 562919) (by norm_num)
theorem B2252605 : Blo 1580488 2252605 := bbase (se 3 (by rfl) ⟨422363, by rfl⟩ : syracuseStep 2252605 = 844727) (by norm_num)
theorem B100081493 : Blo 1580488 100081493 := bbase (se 9 (by rfl) ⟨293207, by rfl⟩ : syracuseStep 100081493 = 586415) (by norm_num)
theorem B2670421 : Blo 1580488 2670421 := bbase (se 9 (by rfl) ⟨7823, by rfl⟩ : syracuseStep 2670421 = 15647) (by norm_num)
theorem B2252701 : Blo 1580488 2252701 := bbase (se 3 (by rfl) ⟨422381, by rfl⟩ : syracuseStep 2252701 = 844763) (by norm_num)
theorem B6758309 : Blo 1580488 6758309 := bbase (se 4 (by rfl) ⟨633591, by rfl⟩ : syracuseStep 6758309 = 1267183) (by norm_num)
theorem B1900525 : Blo 1580488 1900525 := bbase (se 3 (by rfl) ⟨356348, by rfl⟩ : syracuseStep 1900525 = 712697) (by norm_num)
theorem B1581059 : Blo 1580488 1581059 := bstep (se 1 (by rfl) ⟨1185794, by rfl⟩ : syracuseStep 1581059 = 2371589) B2371589
theorem B1581075 : Blo 1580488 1581075 := bstep (se 1 (by rfl) ⟨1185806, by rfl⟩ : syracuseStep 1581075 = 2371613) B2371613
theorem B1581091 : Blo 1580488 1581091 := bstep (se 1 (by rfl) ⟨1185818, by rfl⟩ : syracuseStep 1581091 = 2371637) B2371637
theorem B1581107 : Blo 1580488 1581107 := bstep (se 1 (by rfl) ⟨1185830, by rfl⟩ : syracuseStep 1581107 = 2371661) B2371661
theorem B1581123 : Blo 1580488 1581123 := bstep (se 1 (by rfl) ⟨1185842, by rfl⟩ : syracuseStep 1581123 = 2371685) B2371685
theorem B1581139 : Blo 1580488 1581139 := bstep (se 1 (by rfl) ⟨1185854, by rfl⟩ : syracuseStep 1581139 = 2371709) B2371709
theorem B1581155 : Blo 1580488 1581155 := bstep (se 1 (by rfl) ⟨1185866, by rfl⟩ : syracuseStep 1581155 = 2371733) B2371733
theorem B4505699 : Blo 1580488 4505699 := bstep (se 1 (by rfl) ⟨3379274, by rfl⟩ : syracuseStep 4505699 = 6758549) B6758549
theorem B1581171 : Blo 1580488 1581171 := bstep (se 1 (by rfl) ⟨1185878, by rfl⟩ : syracuseStep 1581171 = 2371757) B2371757
theorem B2252929 : Blo 1580488 2252929 := bstep (se 2 (by rfl) ⟨844848, by rfl⟩ : syracuseStep 2252929 = 1689697) B1689697
theorem B1581187 : Blo 1580488 1581187 := bstep (se 1 (by rfl) ⟨1185890, by rfl⟩ : syracuseStep 1581187 = 2371781) B2371781
theorem B1581203 : Blo 1580488 1581203 := bstep (se 1 (by rfl) ⟨1185902, by rfl⟩ : syracuseStep 1581203 = 2371805) B2371805
theorem B1581219 : Blo 1580488 1581219 := bstep (se 1 (by rfl) ⟨1185914, by rfl⟩ : syracuseStep 1581219 = 2371829) B2371829
theorem B1581235 : Blo 1580488 1581235 := bstep (se 1 (by rfl) ⟨1185926, by rfl⟩ : syracuseStep 1581235 = 2371853) B2371853
theorem B1581251 : Blo 1580488 1581251 := bstep (se 1 (by rfl) ⟨1185938, by rfl⟩ : syracuseStep 1581251 = 2371877) B2371877
theorem B1581267 : Blo 1580488 1581267 := bstep (se 1 (by rfl) ⟨1185950, by rfl⟩ : syracuseStep 1581267 = 2371901) B2371901
theorem B9248995 : Blo 1580488 9248995 := bstep (se 1 (by rfl) ⟨6936746, by rfl⟩ : syracuseStep 9248995 = 13873493) B13873493
theorem B1581283 : Blo 1580488 1581283 := bstep (se 1 (by rfl) ⟨1185962, by rfl⟩ : syracuseStep 1581283 = 2371925) B2371925
theorem B22806755 : Blo 1580488 22806755 := bstep (se 1 (by rfl) ⟨17105066, by rfl⟩ : syracuseStep 22806755 = 34210133) B34210133
theorem B13517027 : Blo 1580488 13517027 := bstep (se 1 (by rfl) ⟨10137770, by rfl⟩ : syracuseStep 13517027 = 20275541) B20275541
theorem B1581299 : Blo 1580488 1581299 := bstep (se 1 (by rfl) ⟨1185974, by rfl⟩ : syracuseStep 1581299 = 2371949) B2371949
theorem B2253043 : Blo 1580488 2253043 := bstep (se 1 (by rfl) ⟨1689782, by rfl⟩ : syracuseStep 2253043 = 3379565) B3379565
theorem B1581315 : Blo 1580488 1581315 := bstep (se 1 (by rfl) ⟨1185986, by rfl⟩ : syracuseStep 1581315 = 2371973) B2371973
theorem B1581331 : Blo 1580488 1581331 := bstep (se 1 (by rfl) ⟨1185998, by rfl⟩ : syracuseStep 1581331 = 2371997) B2371997
theorem B1581347 : Blo 1580488 1581347 := bstep (se 1 (by rfl) ⟨1186010, by rfl⟩ : syracuseStep 1581347 = 2372021) B2372021
theorem B1581363 : Blo 1580488 1581363 := bstep (se 1 (by rfl) ⟨1186022, by rfl⟩ : syracuseStep 1581363 = 2372045) B2372045
theorem B1581379 : Blo 1580488 1581379 := bstep (se 1 (by rfl) ⟨1186034, by rfl⟩ : syracuseStep 1581379 = 2372069) B2372069
theorem B9011533 : Blo 1580488 9011533 := bstep (se 3 (by rfl) ⟨1689662, by rfl⟩ : syracuseStep 9011533 = 3379325) B3379325
theorem B1581395 : Blo 1580488 1581395 := bstep (se 1 (by rfl) ⟨1186046, by rfl⟩ : syracuseStep 1581395 = 2372093) B2372093
theorem B13508963 : Blo 1580488 13508963 := bstep (se 1 (by rfl) ⟨10131722, by rfl⟩ : syracuseStep 13508963 = 20263445) B20263445
theorem B1581411 : Blo 1580488 1581411 := bstep (se 1 (by rfl) ⟨1186058, by rfl⟩ : syracuseStep 1581411 = 2372117) B2372117
theorem B1581427 : Blo 1580488 1581427 := bstep (se 1 (by rfl) ⟨1186070, by rfl⟩ : syracuseStep 1581427 = 2372141) B2372141
theorem B1581443 : Blo 1580488 1581443 := bstep (se 1 (by rfl) ⟨1186082, by rfl⟩ : syracuseStep 1581443 = 2372165) B2372165
theorem B5136785 : Blo 1580488 5136785 := bstep (se 2 (by rfl) ⟨1926294, by rfl⟩ : syracuseStep 5136785 = 3852589) B3852589
theorem B1581459 : Blo 1580488 1581459 := bstep (se 1 (by rfl) ⟨1186094, by rfl⟩ : syracuseStep 1581459 = 2372189) B2372189
theorem B1581475 : Blo 1580488 1581475 := bstep (se 1 (by rfl) ⟨1186106, by rfl⟩ : syracuseStep 1581475 = 2372213) B2372213
theorem B1581491 : Blo 1580488 1581491 := bstep (se 1 (by rfl) ⟨1186118, by rfl⟩ : syracuseStep 1581491 = 2372237) B2372237
theorem B1581507 : Blo 1580488 1581507 := bstep (se 1 (by rfl) ⟨1186130, by rfl⟩ : syracuseStep 1581507 = 2372261) B2372261
theorem B1581523 : Blo 1580488 1581523 := bstep (se 1 (by rfl) ⟨1186142, by rfl⟩ : syracuseStep 1581523 = 2372285) B2372285
theorem B1581539 : Blo 1580488 1581539 := bstep (se 1 (by rfl) ⟨1186154, by rfl⟩ : syracuseStep 1581539 = 2372309) B2372309
theorem B1581555 : Blo 1580488 1581555 := bstep (se 1 (by rfl) ⟨1186166, by rfl⟩ : syracuseStep 1581555 = 2372333) B2372333
theorem B1778179 : Blo 1580488 1778179 := bstep (se 1 (by rfl) ⟨1333634, by rfl⟩ : syracuseStep 1778179 = 2667269) B2667269
theorem B1581571 : Blo 1580488 1581571 := bstep (se 1 (by rfl) ⟨1186178, by rfl⟩ : syracuseStep 1581571 = 2372357) B2372357
theorem B1581587 : Blo 1580488 1581587 := bstep (se 1 (by rfl) ⟨1186190, by rfl⟩ : syracuseStep 1581587 = 2372381) B2372381
theorem B1581603 : Blo 1580488 1581603 := bstep (se 1 (by rfl) ⟨1186202, by rfl⟩ : syracuseStep 1581603 = 2372405) B2372405
theorem B1581619 : Blo 1580488 1581619 := bstep (se 1 (by rfl) ⟨1186214, by rfl⟩ : syracuseStep 1581619 = 2372429) B2372429
theorem B1581635 : Blo 1580488 1581635 := bstep (se 1 (by rfl) ⟨1186226, by rfl⟩ : syracuseStep 1581635 = 2372453) B2372453
theorem B1581651 : Blo 1580488 1581651 := bstep (se 1 (by rfl) ⟨1186238, by rfl⟩ : syracuseStep 1581651 = 2372477) B2372477
theorem B2138707 : Blo 1580488 2138707 := bstep (se 1 (by rfl) ⟨1604030, by rfl⟩ : syracuseStep 2138707 = 3208061) B3208061
theorem B1581667 : Blo 1580488 1581667 := bstep (se 1 (by rfl) ⟨1186250, by rfl⟩ : syracuseStep 1581667 = 2372501) B2372501
theorem B4055665 : Blo 1580488 4055665 := bstep (se 2 (by rfl) ⟨1520874, by rfl⟩ : syracuseStep 4055665 = 3041749) B3041749
theorem B1581683 : Blo 1580488 1581683 := bstep (se 1 (by rfl) ⟨1186262, by rfl⟩ : syracuseStep 1581683 = 2372525) B2372525
theorem B1581699 : Blo 1580488 1581699 := bstep (se 1 (by rfl) ⟨1186274, by rfl⟩ : syracuseStep 1581699 = 2372549) B2372549
theorem B1778323 : Blo 1580488 1778323 := bstep (se 1 (by rfl) ⟨1333742, by rfl⟩ : syracuseStep 1778323 = 2667485) B2667485
theorem B1581715 : Blo 1580488 1581715 := bstep (se 1 (by rfl) ⟨1186286, by rfl⟩ : syracuseStep 1581715 = 2372573) B2372573
theorem B6005411 : Blo 1580488 6005411 := bstep (se 1 (by rfl) ⟨4504058, by rfl⟩ : syracuseStep 6005411 = 9008117) B9008117
theorem B1581731 : Blo 1580488 1581731 := bstep (se 1 (by rfl) ⟨1186298, by rfl⟩ : syracuseStep 1581731 = 2372597) B2372597
theorem B1581747 : Blo 1580488 1581747 := bstep (se 1 (by rfl) ⟨1186310, by rfl⟩ : syracuseStep 1581747 = 2372621) B2372621
theorem B1581763 : Blo 1580488 1581763 := bstep (se 1 (by rfl) ⟨1186322, by rfl⟩ : syracuseStep 1581763 = 2372645) B2372645
theorem B2851537 : Blo 1580488 2851537 := bstep (se 2 (by rfl) ⟨1069326, by rfl⟩ : syracuseStep 2851537 = 2138653) B2138653
theorem B1581779 : Blo 1580488 1581779 := bstep (se 1 (by rfl) ⟨1186334, by rfl⟩ : syracuseStep 1581779 = 2372669) B2372669
theorem B1581795 : Blo 1580488 1581795 := bstep (se 1 (by rfl) ⟨1186346, by rfl⟩ : syracuseStep 1581795 = 2372693) B2372693
theorem B3375857 : Blo 1580488 3375857 := bstep (se 2 (by rfl) ⟨1265946, by rfl⟩ : syracuseStep 3375857 = 2531893) B2531893
theorem B1581811 : Blo 1580488 1581811 := bstep (se 1 (by rfl) ⟨1186358, by rfl⟩ : syracuseStep 1581811 = 2372717) B2372717
theorem B1581827 : Blo 1580488 1581827 := bstep (se 1 (by rfl) ⟨1186370, by rfl⟩ : syracuseStep 1581827 = 2372741) B2372741
theorem B1581843 : Blo 1580488 1581843 := bstep (se 1 (by rfl) ⟨1186382, by rfl⟩ : syracuseStep 1581843 = 2372765) B2372765
theorem B2532131 : Blo 1580488 2532131 := bstep (se 1 (by rfl) ⟨1899098, by rfl⟩ : syracuseStep 2532131 = 3798197) B3798197
theorem B1778467 : Blo 1580488 1778467 := bstep (se 1 (by rfl) ⟨1333850, by rfl⟩ : syracuseStep 1778467 = 2667701) B2667701
theorem B1581859 : Blo 1580488 1581859 := bstep (se 1 (by rfl) ⟨1186394, by rfl⟩ : syracuseStep 1581859 = 2372789) B2372789
theorem B1581875 : Blo 1580488 1581875 := bstep (se 1 (by rfl) ⟨1186406, by rfl⟩ : syracuseStep 1581875 = 2372813) B2372813
theorem B1581891 : Blo 1580488 1581891 := bstep (se 1 (by rfl) ⟨1186418, by rfl⟩ : syracuseStep 1581891 = 2372837) B2372837
theorem B21635909 : Blo 1580488 21635909 := bstep (se 4 (by rfl) ⟨2028366, by rfl⟩ : syracuseStep 21635909 = 4056733) B4056733
theorem B4277069 : Blo 1580488 4277069 := bstep (se 3 (by rfl) ⟨801950, by rfl⟩ : syracuseStep 4277069 = 1603901) B1603901
theorem B1581907 : Blo 1580488 1581907 := bstep (se 1 (by rfl) ⟨1186430, by rfl⟩ : syracuseStep 1581907 = 2372861) B2372861
theorem B1581923 : Blo 1580488 1581923 := bstep (se 1 (by rfl) ⟨1186442, by rfl⟩ : syracuseStep 1581923 = 2372885) B2372885
theorem B1581939 : Blo 1580488 1581939 := bstep (se 1 (by rfl) ⟨1186454, by rfl⟩ : syracuseStep 1581939 = 2372909) B2372909
theorem B5063555 : Blo 1580488 5063555 := bstep (se 1 (by rfl) ⟨3797666, by rfl⟩ : syracuseStep 5063555 = 7595333) B7595333
theorem B1581955 : Blo 1580488 1581955 := bstep (se 1 (by rfl) ⟨1186466, by rfl⟩ : syracuseStep 1581955 = 2372933) B2372933
theorem B3556241 : Blo 1580488 3556241 := bstep (se 2 (by rfl) ⟨1333590, by rfl⟩ : syracuseStep 3556241 = 2667181) B2667181
theorem B1581971 : Blo 1580488 1581971 := bstep (se 1 (by rfl) ⟨1186478, by rfl⟩ : syracuseStep 1581971 = 2372957) B2372957
theorem B3556259 : Blo 1580488 3556259 := bstep (se 1 (by rfl) ⟨2667194, by rfl⟩ : syracuseStep 3556259 = 5334389) B5334389
theorem B1581987 : Blo 1580488 1581987 := bstep (se 1 (by rfl) ⟨1186490, by rfl⟩ : syracuseStep 1581987 = 2372981) B2372981
theorem B1778611 : Blo 1580488 1778611 := bstep (se 1 (by rfl) ⟨1333958, by rfl⟩ : syracuseStep 1778611 = 2667917) B2667917
theorem B1582003 : Blo 1580488 1582003 := bstep (se 1 (by rfl) ⟨1186502, by rfl⟩ : syracuseStep 1582003 = 2373005) B2373005
theorem B1582019 : Blo 1580488 1582019 := bstep (se 1 (by rfl) ⟨1186514, by rfl⟩ : syracuseStep 1582019 = 2373029) B2373029
theorem B1688531 : Blo 1580488 1688531 := bstep (se 1 (by rfl) ⟨1266398, by rfl⟩ : syracuseStep 1688531 = 2532797) B2532797
theorem B1582035 : Blo 1580488 1582035 := bstep (se 1 (by rfl) ⟨1186526, by rfl⟩ : syracuseStep 1582035 = 2373053) B2373053
theorem B1582051 : Blo 1580488 1582051 := bstep (se 1 (by rfl) ⟨1186538, by rfl⟩ : syracuseStep 1582051 = 2373077) B2373077
theorem B1582067 : Blo 1580488 1582067 := bstep (se 1 (by rfl) ⟨1186550, by rfl⟩ : syracuseStep 1582067 = 2373101) B2373101
theorem B1582083 : Blo 1580488 1582083 := bstep (se 1 (by rfl) ⟨1186562, by rfl⟩ : syracuseStep 1582083 = 2373125) B2373125
theorem B1582099 : Blo 1580488 1582099 := bstep (se 1 (by rfl) ⟨1186574, by rfl⟩ : syracuseStep 1582099 = 2373149) B2373149
theorem B1582115 : Blo 1580488 1582115 := bstep (se 1 (by rfl) ⟨1186586, by rfl⟩ : syracuseStep 1582115 = 2373173) B2373173
theorem B1582131 : Blo 1580488 1582131 := bstep (se 1 (by rfl) ⟨1186598, by rfl⟩ : syracuseStep 1582131 = 2373197) B2373197
theorem B1778755 : Blo 1580488 1778755 := bstep (se 1 (by rfl) ⟨1334066, by rfl⟩ : syracuseStep 1778755 = 2668133) B2668133
theorem B1582147 : Blo 1580488 1582147 := bstep (se 1 (by rfl) ⟨1186610, by rfl⟩ : syracuseStep 1582147 = 2373221) B2373221
theorem B1582163 : Blo 1580488 1582163 := bstep (se 1 (by rfl) ⟨1186622, by rfl⟩ : syracuseStep 1582163 = 2373245) B2373245
theorem B4809827 : Blo 1580488 4809827 := bstep (se 1 (by rfl) ⟨3607370, by rfl⟩ : syracuseStep 4809827 = 7214741) B7214741
theorem B1582179 : Blo 1580488 1582179 := bstep (se 1 (by rfl) ⟨1186634, by rfl⟩ : syracuseStep 1582179 = 2373269) B2373269
theorem B1582195 : Blo 1580488 1582195 := bstep (se 1 (by rfl) ⟨1186646, by rfl⟩ : syracuseStep 1582195 = 2373293) B2373293
theorem B1582211 : Blo 1580488 1582211 := bstep (se 1 (by rfl) ⟨1186658, by rfl⟩ : syracuseStep 1582211 = 2373317) B2373317
theorem B1582227 : Blo 1580488 1582227 := bstep (se 1 (by rfl) ⟨1186670, by rfl⟩ : syracuseStep 1582227 = 2373341) B2373341
theorem B1582243 : Blo 1580488 1582243 := bstep (se 1 (by rfl) ⟨1186682, by rfl⟩ : syracuseStep 1582243 = 2373365) B2373365
theorem B3556529 : Blo 1580488 3556529 := bstep (se 2 (by rfl) ⟨1333698, by rfl⟩ : syracuseStep 3556529 = 2667397) B2667397
theorem B1582259 : Blo 1580488 1582259 := bstep (se 1 (by rfl) ⟨1186694, by rfl⟩ : syracuseStep 1582259 = 2373389) B2373389
theorem B3556547 : Blo 1580488 3556547 := bstep (se 1 (by rfl) ⟨2667410, by rfl⟩ : syracuseStep 3556547 = 5334821) B5334821
theorem B1582275 : Blo 1580488 1582275 := bstep (se 1 (by rfl) ⟨1186706, by rfl⟩ : syracuseStep 1582275 = 2373413) B2373413
theorem B1778899 : Blo 1580488 1778899 := bstep (se 1 (by rfl) ⟨1334174, by rfl⟩ : syracuseStep 1778899 = 2668349) B2668349
theorem B1582291 : Blo 1580488 1582291 := bstep (se 1 (by rfl) ⟨1186718, by rfl⟩ : syracuseStep 1582291 = 2373437) B2373437
theorem B1582307 : Blo 1580488 1582307 := bstep (se 1 (by rfl) ⟨1186730, by rfl⟩ : syracuseStep 1582307 = 2373461) B2373461
theorem B1582323 : Blo 1580488 1582323 := bstep (se 1 (by rfl) ⟨1186742, by rfl⟩ : syracuseStep 1582323 = 2373485) B2373485
theorem B1582339 : Blo 1580488 1582339 := bstep (se 1 (by rfl) ⟨1186754, by rfl⟩ : syracuseStep 1582339 = 2373509) B2373509
theorem B5063953 : Blo 1580488 5063953 := bstep (se 2 (by rfl) ⟨1898982, by rfl⟩ : syracuseStep 5063953 = 3797965) B3797965
theorem B1582355 : Blo 1580488 1582355 := bstep (se 1 (by rfl) ⟨1186766, by rfl⟩ : syracuseStep 1582355 = 2373533) B2373533
theorem B1582371 : Blo 1580488 1582371 := bstep (se 1 (by rfl) ⟨1186778, by rfl⟩ : syracuseStep 1582371 = 2373557) B2373557
theorem B1582387 : Blo 1580488 1582387 := bstep (se 1 (by rfl) ⟨1186790, by rfl⟩ : syracuseStep 1582387 = 2373581) B2373581
theorem B1582403 : Blo 1580488 1582403 := bstep (se 1 (by rfl) ⟨1186802, by rfl⟩ : syracuseStep 1582403 = 2373605) B2373605
theorem B2704721 : Blo 1580488 2704721 := bstep (se 2 (by rfl) ⟨1014270, by rfl⟩ : syracuseStep 2704721 = 2028541) B2028541
theorem B1582419 : Blo 1580488 1582419 := bstep (se 1 (by rfl) ⟨1186814, by rfl⟩ : syracuseStep 1582419 = 2373629) B2373629
theorem B1779043 : Blo 1580488 1779043 := bstep (se 1 (by rfl) ⟨1334282, by rfl⟩ : syracuseStep 1779043 = 2668565) B2668565
theorem B1582435 : Blo 1580488 1582435 := bstep (se 1 (by rfl) ⟨1186826, by rfl⟩ : syracuseStep 1582435 = 2373653) B2373653
theorem B1582451 : Blo 1580488 1582451 := bstep (se 1 (by rfl) ⟨1186838, by rfl⟩ : syracuseStep 1582451 = 2373677) B2373677
theorem B5064067 : Blo 1580488 5064067 := bstep (se 1 (by rfl) ⟨3798050, by rfl⟩ : syracuseStep 5064067 = 7596101) B7596101
theorem B1582467 : Blo 1580488 1582467 := bstep (se 1 (by rfl) ⟨1186850, by rfl⟩ : syracuseStep 1582467 = 2373701) B2373701
theorem B1582483 : Blo 1580488 1582483 := bstep (se 1 (by rfl) ⟨1186862, by rfl⟩ : syracuseStep 1582483 = 2373725) B2373725
theorem B3556817 : Blo 1580488 3556817 := bstep (se 2 (by rfl) ⟨1333806, by rfl⟩ : syracuseStep 3556817 = 2667613) B2667613
theorem B3556835 : Blo 1580488 3556835 := bstep (se 1 (by rfl) ⟨2667626, by rfl⟩ : syracuseStep 3556835 = 5335253) B5335253
theorem B2000371 : Blo 1580488 2000371 := bstep (se 1 (by rfl) ⟨1500278, by rfl⟩ : syracuseStep 2000371 = 3000557) B3000557
theorem B1779187 : Blo 1580488 1779187 := bstep (se 1 (by rfl) ⟨1334390, by rfl⟩ : syracuseStep 1779187 = 2668781) B2668781
theorem B5334605 : Blo 1580488 5334605 := bstep (se 3 (by rfl) ⟨1000238, by rfl⟩ : syracuseStep 5334605 = 2000477) B2000477
theorem B3376721 : Blo 1580488 3376721 := bstep (se 2 (by rfl) ⟨1266270, by rfl⟩ : syracuseStep 3376721 = 2532541) B2532541
theorem B7603789 : Blo 1580488 7603789 := bstep (se 3 (by rfl) ⟨1425710, by rfl⟩ : syracuseStep 7603789 = 2851421) B2851421
theorem B2000467 : Blo 1580488 2000467 := bstep (se 1 (by rfl) ⟨1500350, by rfl⟩ : syracuseStep 2000467 = 3000701) B3000701
theorem B5334659 : Blo 1580488 5334659 := bstep (se 1 (by rfl) ⟨4000994, by rfl⟩ : syracuseStep 5334659 = 8001989) B8001989
theorem B1779331 : Blo 1580488 1779331 := bstep (se 1 (by rfl) ⟨1334498, by rfl⟩ : syracuseStep 1779331 = 2668997) B2668997
theorem B6006413 : Blo 1580488 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B1689283 : Blo 1580488 1689283 := bstep (se 1 (by rfl) ⟨1266962, by rfl⟩ : syracuseStep 1689283 = 2533925) B2533925
theorem B3557105 : Blo 1580488 3557105 := bstep (se 2 (by rfl) ⟨1333914, by rfl⟩ : syracuseStep 3557105 = 2667829) B2667829
theorem B4056817 : Blo 1580488 4056817 := bstep (se 2 (by rfl) ⟨1521306, by rfl⟩ : syracuseStep 4056817 = 3042613) B3042613
theorem B3557123 : Blo 1580488 3557123 := bstep (se 1 (by rfl) ⟨2667842, by rfl⟩ : syracuseStep 3557123 = 5335685) B5335685
theorem B2533123 : Blo 1580488 2533123 := bstep (se 1 (by rfl) ⟨1899842, by rfl⟩ : syracuseStep 2533123 = 3799685) B3799685
theorem B1779475 : Blo 1580488 1779475 := bstep (se 1 (by rfl) ⟨1334606, by rfl⟩ : syracuseStep 1779475 = 2669213) B2669213
theorem B5334929 : Blo 1580488 5334929 := bstep (se 2 (by rfl) ⟨2000598, by rfl⟩ : syracuseStep 5334929 = 4001197) B4001197
theorem B1779619 : Blo 1580488 1779619 := bstep (se 1 (by rfl) ⟨1334714, by rfl⟩ : syracuseStep 1779619 = 2669429) B2669429
theorem B8005553 : Blo 1580488 8005553 := bstep (se 2 (by rfl) ⟨3002082, by rfl⟩ : syracuseStep 8005553 = 6004165) B6004165
theorem B2705393 : Blo 1580488 2705393 := bstep (se 2 (by rfl) ⟨1014522, by rfl⟩ : syracuseStep 2705393 = 2029045) B2029045
theorem B8546309 : Blo 1580488 8546309 := bstep (se 4 (by rfl) ⟨801216, by rfl⟩ : syracuseStep 8546309 = 1602433) B1602433
theorem B3557393 : Blo 1580488 3557393 := bstep (se 2 (by rfl) ⟨1334022, by rfl⟩ : syracuseStep 3557393 = 2668045) B2668045
theorem B3557411 : Blo 1580488 3557411 := bstep (se 1 (by rfl) ⟨2668058, by rfl⟩ : syracuseStep 3557411 = 5336117) B5336117
theorem B1779763 : Blo 1580488 1779763 := bstep (se 1 (by rfl) ⟨1334822, by rfl⟩ : syracuseStep 1779763 = 2669645) B2669645
theorem B2000963 : Blo 1580488 2000963 := bstep (se 1 (by rfl) ⟨1500722, by rfl⟩ : syracuseStep 2000963 = 3001445) B3001445
theorem B5064785 : Blo 1580488 5064785 := bstep (se 2 (by rfl) ⟨1899294, by rfl⟩ : syracuseStep 5064785 = 3798589) B3798589
theorem B6408305 : Blo 1580488 6408305 := bstep (se 2 (by rfl) ⟨2403114, by rfl⟩ : syracuseStep 6408305 = 4806229) B4806229
theorem B1624259 : Blo 1580488 1624259 := bstep (se 1 (by rfl) ⟨1218194, by rfl⟩ : syracuseStep 1624259 = 2436389) B2436389
theorem B1779907 : Blo 1580488 1779907 := bstep (se 1 (by rfl) ⟨1334930, by rfl⟩ : syracuseStep 1779907 = 2669861) B2669861
theorem B3557681 : Blo 1580488 3557681 := bstep (se 2 (by rfl) ⟨1334130, by rfl⟩ : syracuseStep 3557681 = 2668261) B2668261
theorem B3557699 : Blo 1580488 3557699 := bstep (se 1 (by rfl) ⟨2668274, by rfl⟩ : syracuseStep 3557699 = 5336549) B5336549
theorem B1780051 : Blo 1580488 1780051 := bstep (se 1 (by rfl) ⟨1335038, by rfl⟩ : syracuseStep 1780051 = 2670077) B2670077
theorem B3000739 : Blo 1580488 3000739 := bstep (se 1 (by rfl) ⟨2250554, by rfl⟩ : syracuseStep 3000739 = 4501109) B4501109
theorem B5335469 : Blo 1580488 5335469 := bstep (se 3 (by rfl) ⟨1000400, by rfl⟩ : syracuseStep 5335469 = 2000801) B2000801
theorem B5335523 : Blo 1580488 5335523 := bstep (se 1 (by rfl) ⟨4001642, by rfl⟩ : syracuseStep 5335523 = 8003285) B8003285
theorem B5409251 : Blo 1580488 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B1780195 : Blo 1580488 1780195 := bstep (se 1 (by rfl) ⟨1335146, by rfl⟩ : syracuseStep 1780195 = 2670293) B2670293
theorem B3557969 : Blo 1580488 3557969 := bstep (se 2 (by rfl) ⟨1334238, by rfl⟩ : syracuseStep 3557969 = 2668477) B2668477
theorem B3557987 : Blo 1580488 3557987 := bstep (se 1 (by rfl) ⟨2668490, by rfl⟩ : syracuseStep 3557987 = 5336981) B5336981
theorem B3656291 : Blo 1580488 3656291 := bstep (se 1 (by rfl) ⟨2742218, by rfl⟩ : syracuseStep 3656291 = 5484437) B5484437
theorem B5065325 : Blo 1580488 5065325 := bstep (se 3 (by rfl) ⟨949748, by rfl⟩ : syracuseStep 5065325 = 1899497) B1899497
theorem B9005701 : Blo 1580488 9005701 := bstep (se 4 (by rfl) ⟨844284, by rfl⟩ : syracuseStep 9005701 = 1688569) B1688569
theorem B6752909 : Blo 1580488 6752909 := bstep (se 3 (by rfl) ⟨1266170, by rfl⟩ : syracuseStep 6752909 = 2532341) B2532341
theorem B2534033 : Blo 1580488 2534033 := bstep (se 2 (by rfl) ⟨950262, by rfl⟩ : syracuseStep 2534033 = 1900525) B1900525
theorem B5335793 : Blo 1580488 5335793 := bstep (se 2 (by rfl) ⟨2000922, by rfl⟩ : syracuseStep 5335793 = 4001845) B4001845
theorem B2001667 : Blo 1580488 2001667 := bstep (se 1 (by rfl) ⟨1501250, by rfl⟩ : syracuseStep 2001667 = 3002501) B3002501
theorem B2534161 : Blo 1580488 2534161 := bstep (se 2 (by rfl) ⟨950310, by rfl⟩ : syracuseStep 2534161 = 1900621) B1900621
theorem B8112973 : Blo 1580488 8112973 := bstep (se 3 (by rfl) ⟨1521182, by rfl⟩ : syracuseStep 8112973 = 3042365) B3042365
theorem B3001187 : Blo 1580488 3001187 := bstep (se 1 (by rfl) ⟨2250890, by rfl⟩ : syracuseStep 3001187 = 4501781) B4501781
theorem B2001763 : Blo 1580488 2001763 := bstep (se 1 (by rfl) ⟨1501322, by rfl⟩ : syracuseStep 2001763 = 3002645) B3002645
theorem B3378019 : Blo 1580488 3378019 := bstep (se 1 (by rfl) ⟨2533514, by rfl⟩ : syracuseStep 3378019 = 5067029) B5067029
theorem B3558257 : Blo 1580488 3558257 := bstep (se 2 (by rfl) ⟨1334346, by rfl⟩ : syracuseStep 3558257 = 2668693) B2668693
theorem B3558275 : Blo 1580488 3558275 := bstep (se 1 (by rfl) ⟨2668706, by rfl⟩ : syracuseStep 3558275 = 5337413) B5337413
theorem B6843313 : Blo 1580488 6843313 := bstep (se 2 (by rfl) ⟨2566242, by rfl⟩ : syracuseStep 6843313 = 5132485) B5132485
theorem B5409731 : Blo 1580488 5409731 := bstep (se 1 (by rfl) ⟨4057298, by rfl⟩ : syracuseStep 5409731 = 8114597) B8114597
theorem B4811725 : Blo 1580488 4811725 := bstep (se 3 (by rfl) ⟨902198, by rfl⟩ : syracuseStep 4811725 = 1804397) B1804397
theorem B5409841 : Blo 1580488 5409841 := bstep (se 2 (by rfl) ⟨2028690, by rfl⟩ : syracuseStep 5409841 = 4057381) B4057381
theorem B3001475 : Blo 1580488 3001475 := bstep (se 1 (by rfl) ⟨2251106, by rfl⟩ : syracuseStep 3001475 = 4502213) B4502213
theorem B3558545 : Blo 1580488 3558545 := bstep (se 2 (by rfl) ⟨1334454, by rfl⟩ : syracuseStep 3558545 = 2668909) B2668909
theorem B3558563 : Blo 1580488 3558563 := bstep (se 1 (by rfl) ⟨2668922, by rfl⟩ : syracuseStep 3558563 = 5337845) B5337845
theorem B2370737 : Blo 1580488 2370737 := bstep (se 2 (by rfl) ⟨889026, by rfl⟩ : syracuseStep 2370737 = 1778053) B1778053
theorem B2370755 : Blo 1580488 2370755 := bstep (se 1 (by rfl) ⟨1778066, by rfl⟩ : syracuseStep 2370755 = 3556133) B3556133
theorem B2370785 : Blo 1580488 2370785 := bstep (se 2 (by rfl) ⟨889044, by rfl⟩ : syracuseStep 2370785 = 1778089) B1778089
theorem B2370803 : Blo 1580488 2370803 := bstep (se 1 (by rfl) ⟨1778102, by rfl⟩ : syracuseStep 2370803 = 3556205) B3556205
theorem B3607811 : Blo 1580488 3607811 := bstep (se 1 (by rfl) ⟨2705858, by rfl⟩ : syracuseStep 3607811 = 5411717) B5411717
theorem B5336333 : Blo 1580488 5336333 := bstep (se 3 (by rfl) ⟨1000562, by rfl⟩ : syracuseStep 5336333 = 2001125) B2001125
theorem B2370833 : Blo 1580488 2370833 := bstep (se 2 (by rfl) ⟨889062, by rfl⟩ : syracuseStep 2370833 = 1778125) B1778125
theorem B2370851 : Blo 1580488 2370851 := bstep (se 1 (by rfl) ⟨1778138, by rfl⟩ : syracuseStep 2370851 = 3556277) B3556277
theorem B2370881 : Blo 1580488 2370881 := bstep (se 2 (by rfl) ⟨889080, by rfl⟩ : syracuseStep 2370881 = 1778161) B1778161
theorem B5336387 : Blo 1580488 5336387 := bstep (se 1 (by rfl) ⟨4002290, by rfl⟩ : syracuseStep 5336387 = 8004581) B8004581
theorem B2370899 : Blo 1580488 2370899 := bstep (se 1 (by rfl) ⟨1778174, by rfl⟩ : syracuseStep 2370899 = 3556349) B3556349
theorem B2002259 : Blo 1580488 2002259 := bstep (se 1 (by rfl) ⟨1501694, by rfl⟩ : syracuseStep 2002259 = 3003389) B3003389
theorem B8007011 : Blo 1580488 8007011 := bstep (se 1 (by rfl) ⟨6005258, by rfl⟩ : syracuseStep 8007011 = 12010517) B12010517
theorem B2370929 : Blo 1580488 2370929 := bstep (se 2 (by rfl) ⟨889098, by rfl⟩ : syracuseStep 2370929 = 1778197) B1778197
theorem B2370947 : Blo 1580488 2370947 := bstep (se 1 (by rfl) ⟨1778210, by rfl⟩ : syracuseStep 2370947 = 3556421) B3556421
theorem B2370977 : Blo 1580488 2370977 := bstep (se 2 (by rfl) ⟨889116, by rfl⟩ : syracuseStep 2370977 = 1778233) B1778233
theorem B3558833 : Blo 1580488 3558833 := bstep (se 2 (by rfl) ⟨1334562, by rfl⟩ : syracuseStep 3558833 = 2669125) B2669125
theorem B2370995 : Blo 1580488 2370995 := bstep (se 1 (by rfl) ⟨1778246, by rfl⟩ : syracuseStep 2370995 = 3556493) B3556493
theorem B3558851 : Blo 1580488 3558851 := bstep (se 1 (by rfl) ⟨2669138, by rfl⟩ : syracuseStep 3558851 = 5338277) B5338277
theorem B6172109 : Blo 1580488 6172109 := bstep (se 3 (by rfl) ⟨1157270, by rfl⟩ : syracuseStep 6172109 = 2314541) B2314541
theorem B2371025 : Blo 1580488 2371025 := bstep (se 2 (by rfl) ⟨889134, by rfl⟩ : syracuseStep 2371025 = 1778269) B1778269
theorem B2371043 : Blo 1580488 2371043 := bstep (se 1 (by rfl) ⟨1778282, by rfl⟩ : syracuseStep 2371043 = 3556565) B3556565
theorem B2371073 : Blo 1580488 2371073 := bstep (se 2 (by rfl) ⟨889152, by rfl⟩ : syracuseStep 2371073 = 1778305) B1778305
theorem B2371091 : Blo 1580488 2371091 := bstep (se 1 (by rfl) ⟨1778318, by rfl⟩ : syracuseStep 2371091 = 3556637) B3556637
theorem B2371121 : Blo 1580488 2371121 := bstep (se 2 (by rfl) ⟨889170, by rfl⟩ : syracuseStep 2371121 = 1778341) B1778341
theorem B2371139 : Blo 1580488 2371139 := bstep (se 1 (by rfl) ⟨1778354, by rfl⟩ : syracuseStep 2371139 = 3556709) B3556709
theorem B5336657 : Blo 1580488 5336657 := bstep (se 2 (by rfl) ⟨2001246, by rfl⟩ : syracuseStep 5336657 = 4002493) B4002493
theorem B2371169 : Blo 1580488 2371169 := bstep (se 2 (by rfl) ⟨889188, by rfl⟩ : syracuseStep 2371169 = 1778377) B1778377
theorem B2371187 : Blo 1580488 2371187 := bstep (se 1 (by rfl) ⟨1778390, by rfl⟩ : syracuseStep 2371187 = 3556781) B3556781
theorem B2371217 : Blo 1580488 2371217 := bstep (se 2 (by rfl) ⟨889206, by rfl⟩ : syracuseStep 2371217 = 1778413) B1778413
theorem B2371235 : Blo 1580488 2371235 := bstep (se 1 (by rfl) ⟨1778426, by rfl⟩ : syracuseStep 2371235 = 3556853) B3556853
theorem B4501165 : Blo 1580488 4501165 := bstep (se 3 (by rfl) ⟨843968, by rfl⟩ : syracuseStep 4501165 = 1687937) B1687937
theorem B2371265 : Blo 1580488 2371265 := bstep (se 2 (by rfl) ⟨889224, by rfl⟩ : syracuseStep 2371265 = 1778449) B1778449
theorem B8548037 : Blo 1580488 8548037 := bstep (se 4 (by rfl) ⟨801378, by rfl⟩ : syracuseStep 8548037 = 1602757) B1602757
theorem B3559121 : Blo 1580488 3559121 := bstep (se 2 (by rfl) ⟨1334670, by rfl⟩ : syracuseStep 3559121 = 2669341) B2669341
theorem B2371283 : Blo 1580488 2371283 := bstep (se 1 (by rfl) ⟨1778462, by rfl⟩ : syracuseStep 2371283 = 3556925) B3556925
theorem B48680675 : Blo 1580488 48680675 := bstep (se 1 (by rfl) ⟨36510506, by rfl⟩ : syracuseStep 48680675 = 73021013) B73021013
theorem B3559139 : Blo 1580488 3559139 := bstep (se 1 (by rfl) ⟨2669354, by rfl⟩ : syracuseStep 3559139 = 5338709) B5338709
theorem B4001521 : Blo 1580488 4001521 := bstep (se 2 (by rfl) ⟨1500570, by rfl⟩ : syracuseStep 4001521 = 3001141) B3001141
theorem B2371313 : Blo 1580488 2371313 := bstep (se 2 (by rfl) ⟨889242, by rfl⟩ : syracuseStep 2371313 = 1778485) B1778485
theorem B2371331 : Blo 1580488 2371331 := bstep (se 1 (by rfl) ⟨1778498, by rfl⟩ : syracuseStep 2371331 = 3556997) B3556997
theorem B2371361 : Blo 1580488 2371361 := bstep (se 2 (by rfl) ⟨889260, by rfl⟩ : syracuseStep 2371361 = 1778521) B1778521
theorem B2371379 : Blo 1580488 2371379 := bstep (se 1 (by rfl) ⟨1778534, by rfl⟩ : syracuseStep 2371379 = 3557069) B3557069
theorem B10137413 : Blo 1580488 10137413 := bstep (se 4 (by rfl) ⟨950382, by rfl⟩ : syracuseStep 10137413 = 1900765) B1900765
theorem B4501325 : Blo 1580488 4501325 := bstep (se 3 (by rfl) ⟨843998, by rfl⟩ : syracuseStep 4501325 = 1687997) B1687997
theorem B2371409 : Blo 1580488 2371409 := bstep (se 2 (by rfl) ⟨889278, by rfl⟩ : syracuseStep 2371409 = 1778557) B1778557
theorem B2371427 : Blo 1580488 2371427 := bstep (se 1 (by rfl) ⟨1778570, by rfl⟩ : syracuseStep 2371427 = 3557141) B3557141
theorem B2371457 : Blo 1580488 2371457 := bstep (se 2 (by rfl) ⟨889296, by rfl⟩ : syracuseStep 2371457 = 1778593) B1778593
theorem B2371475 : Blo 1580488 2371475 := bstep (se 1 (by rfl) ⟨1778606, by rfl⟩ : syracuseStep 2371475 = 3557213) B3557213
theorem B2371505 : Blo 1580488 2371505 := bstep (se 2 (by rfl) ⟨889314, by rfl⟩ : syracuseStep 2371505 = 1778629) B1778629
theorem B2371523 : Blo 1580488 2371523 := bstep (se 1 (by rfl) ⟨1778642, by rfl⟩ : syracuseStep 2371523 = 3557285) B3557285
theorem B2371553 : Blo 1580488 2371553 := bstep (se 2 (by rfl) ⟨889332, by rfl⟩ : syracuseStep 2371553 = 1778665) B1778665
theorem B3559409 : Blo 1580488 3559409 := bstep (se 2 (by rfl) ⟨1334778, by rfl⟩ : syracuseStep 3559409 = 2669557) B2669557
theorem B2371571 : Blo 1580488 2371571 := bstep (se 1 (by rfl) ⟨1778678, by rfl⟩ : syracuseStep 2371571 = 3557357) B3557357
theorem B4501507 : Blo 1580488 4501507 := bstep (se 1 (by rfl) ⟨3376130, by rfl⟩ : syracuseStep 4501507 = 6752261) B6752261
theorem B4001795 : Blo 1580488 4001795 := bstep (se 1 (by rfl) ⟨3001346, by rfl⟩ : syracuseStep 4001795 = 6002693) B6002693
theorem B3559427 : Blo 1580488 3559427 := bstep (se 1 (by rfl) ⟨2669570, by rfl⟩ : syracuseStep 3559427 = 5339141) B5339141
theorem B2371601 : Blo 1580488 2371601 := bstep (se 2 (by rfl) ⟨889350, by rfl⟩ : syracuseStep 2371601 = 1778701) B1778701
theorem B2371619 : Blo 1580488 2371619 := bstep (se 1 (by rfl) ⟨1778714, by rfl⟩ : syracuseStep 2371619 = 3557429) B3557429
theorem B3002417 : Blo 1580488 3002417 := bstep (se 2 (by rfl) ⟨1125906, by rfl⟩ : syracuseStep 3002417 = 2251813) B2251813
theorem B3379249 : Blo 1580488 3379249 := bstep (se 2 (by rfl) ⟨1267218, by rfl⟩ : syracuseStep 3379249 = 2534437) B2534437
theorem B2371649 : Blo 1580488 2371649 := bstep (se 2 (by rfl) ⟨889368, by rfl⟩ : syracuseStep 2371649 = 1778737) B1778737
theorem B2371667 : Blo 1580488 2371667 := bstep (se 1 (by rfl) ⟨1778750, by rfl⟩ : syracuseStep 2371667 = 3557501) B3557501
theorem B5337197 : Blo 1580488 5337197 := bstep (se 3 (by rfl) ⟨1000724, by rfl⟩ : syracuseStep 5337197 = 2001449) B2001449
theorem B2371697 : Blo 1580488 2371697 := bstep (se 2 (by rfl) ⟨889386, by rfl⟩ : syracuseStep 2371697 = 1778773) B1778773
theorem B2371715 : Blo 1580488 2371715 := bstep (se 1 (by rfl) ⟨1778786, by rfl⟩ : syracuseStep 2371715 = 3557573) B3557573
theorem B14422157 : Blo 1580488 14422157 := bstep (se 3 (by rfl) ⟨2704154, by rfl⟩ : syracuseStep 14422157 = 5408309) B5408309
theorem B8007821 : Blo 1580488 8007821 := bstep (se 3 (by rfl) ⟨1501466, by rfl⟩ : syracuseStep 8007821 = 3002933) B3002933
theorem B2371745 : Blo 1580488 2371745 := bstep (se 2 (by rfl) ⟨889404, by rfl⟩ : syracuseStep 2371745 = 1778809) B1778809
theorem B5337251 : Blo 1580488 5337251 := bstep (se 1 (by rfl) ⟨4002938, by rfl⟩ : syracuseStep 5337251 = 8005877) B8005877
theorem B2371763 : Blo 1580488 2371763 := bstep (se 1 (by rfl) ⟨1778822, by rfl⟩ : syracuseStep 2371763 = 3557645) B3557645
theorem B4001987 : Blo 1580488 4001987 := bstep (se 1 (by rfl) ⟨3001490, by rfl⟩ : syracuseStep 4001987 = 6002981) B6002981
theorem B27390149 : Blo 1580488 27390149 := bstep (se 4 (by rfl) ⟨2567826, by rfl⟩ : syracuseStep 27390149 = 5135653) B5135653
theorem B2371793 : Blo 1580488 2371793 := bstep (se 2 (by rfl) ⟨889422, by rfl⟩ : syracuseStep 2371793 = 1778845) B1778845
theorem B2371811 : Blo 1580488 2371811 := bstep (se 1 (by rfl) ⟨1778858, by rfl⟩ : syracuseStep 2371811 = 3557717) B3557717
theorem B7213283 : Blo 1580488 7213283 := bstep (se 1 (by rfl) ⟨5409962, by rfl⟩ : syracuseStep 7213283 = 10819925) B10819925
theorem B3207395 : Blo 1580488 3207395 := bstep (se 1 (by rfl) ⟨2405546, by rfl⟩ : syracuseStep 3207395 = 4811093) B4811093
theorem B4272365 : Blo 1580488 4272365 := bstep (se 3 (by rfl) ⟨801068, by rfl⟩ : syracuseStep 4272365 = 1602137) B1602137
theorem B2371841 : Blo 1580488 2371841 := bstep (se 2 (by rfl) ⟨889440, by rfl⟩ : syracuseStep 2371841 = 1778881) B1778881
theorem B3559697 : Blo 1580488 3559697 := bstep (se 2 (by rfl) ⟨1334886, by rfl⟩ : syracuseStep 3559697 = 2669773) B2669773
theorem B2371859 : Blo 1580488 2371859 := bstep (se 1 (by rfl) ⟨1778894, by rfl⟩ : syracuseStep 2371859 = 3557789) B3557789
theorem B4272419 : Blo 1580488 4272419 := bstep (se 1 (by rfl) ⟨3204314, by rfl⟩ : syracuseStep 4272419 = 6408629) B6408629
theorem B3559715 : Blo 1580488 3559715 := bstep (se 1 (by rfl) ⟨2669786, by rfl⟩ : syracuseStep 3559715 = 5339573) B5339573
theorem B2371889 : Blo 1580488 2371889 := bstep (se 2 (by rfl) ⟨889458, by rfl⟩ : syracuseStep 2371889 = 1778917) B1778917
theorem B2371907 : Blo 1580488 2371907 := bstep (se 1 (by rfl) ⟨1778930, by rfl⟩ : syracuseStep 2371907 = 3557861) B3557861
theorem B2371937 : Blo 1580488 2371937 := bstep (se 2 (by rfl) ⟨889476, by rfl⟩ : syracuseStep 2371937 = 1778953) B1778953
theorem B2371955 : Blo 1580488 2371955 := bstep (se 1 (by rfl) ⟨1778966, by rfl⟩ : syracuseStep 2371955 = 3557933) B3557933
theorem B6001037 : Blo 1580488 6001037 := bstep (se 3 (by rfl) ⟨1125194, by rfl⟩ : syracuseStep 6001037 = 2250389) B2250389
theorem B2371985 : Blo 1580488 2371985 := bstep (se 2 (by rfl) ⟨889494, by rfl⟩ : syracuseStep 2371985 = 1778989) B1778989
theorem B2372003 : Blo 1580488 2372003 := bstep (se 1 (by rfl) ⟨1779002, by rfl⟩ : syracuseStep 2372003 = 3558005) B3558005
theorem B5337521 : Blo 1580488 5337521 := bstep (se 2 (by rfl) ⟨2001570, by rfl⟩ : syracuseStep 5337521 = 4003141) B4003141
theorem B17093045 : Blo 1580488 17093045 := bstep (se 5 (by rfl) ⟨801236, by rfl⟩ : syracuseStep 17093045 = 1602473) B1602473
theorem B2372033 : Blo 1580488 2372033 := bstep (se 2 (by rfl) ⟨889512, by rfl⟩ : syracuseStep 2372033 = 1779025) B1779025
theorem B2372051 : Blo 1580488 2372051 := bstep (se 1 (by rfl) ⟨1779038, by rfl⟩ : syracuseStep 2372051 = 3558077) B3558077
theorem B5067245 : Blo 1580488 5067245 := bstep (se 3 (by rfl) ⟨950108, by rfl⟩ : syracuseStep 5067245 = 1900217) B1900217
theorem B2372081 : Blo 1580488 2372081 := bstep (se 2 (by rfl) ⟨889530, by rfl⟩ : syracuseStep 2372081 = 1779061) B1779061
theorem B2372099 : Blo 1580488 2372099 := bstep (se 1 (by rfl) ⟨1779074, by rfl⟩ : syracuseStep 2372099 = 3558149) B3558149
theorem B2372129 : Blo 1580488 2372129 := bstep (se 2 (by rfl) ⟨889548, by rfl⟩ : syracuseStep 2372129 = 1779097) B1779097
theorem B3559985 : Blo 1580488 3559985 := bstep (se 2 (by rfl) ⟨1334994, by rfl⟩ : syracuseStep 3559985 = 2669989) B2669989
theorem B2372147 : Blo 1580488 2372147 := bstep (se 1 (by rfl) ⟨1779110, by rfl⟩ : syracuseStep 2372147 = 3558221) B3558221
theorem B3560003 : Blo 1580488 3560003 := bstep (se 1 (by rfl) ⟨2670002, by rfl⟩ : syracuseStep 3560003 = 5340005) B5340005
theorem B9007685 : Blo 1580488 9007685 := bstep (se 4 (by rfl) ⟨844470, by rfl⟩ : syracuseStep 9007685 = 1688941) B1688941
theorem B2372177 : Blo 1580488 2372177 := bstep (se 2 (by rfl) ⟨889566, by rfl⟩ : syracuseStep 2372177 = 1779133) B1779133
theorem B2667107 : Blo 1580488 2667107 := bstep (se 1 (by rfl) ⟨2000330, by rfl⟩ : syracuseStep 2667107 = 4000661) B4000661
theorem B2372195 : Blo 1580488 2372195 := bstep (se 1 (by rfl) ⟨1779146, by rfl⟩ : syracuseStep 2372195 = 3558293) B3558293
theorem B2372225 : Blo 1580488 2372225 := bstep (se 2 (by rfl) ⟨889584, by rfl⟩ : syracuseStep 2372225 = 1779169) B1779169
theorem B2372243 : Blo 1580488 2372243 := bstep (se 1 (by rfl) ⟨1779182, by rfl⟩ : syracuseStep 2372243 = 3558365) B3558365
theorem B2372273 : Blo 1580488 2372273 := bstep (se 2 (by rfl) ⟨889602, by rfl⟩ : syracuseStep 2372273 = 1779205) B1779205
theorem B2372291 : Blo 1580488 2372291 := bstep (se 1 (by rfl) ⟨1779218, by rfl⟩ : syracuseStep 2372291 = 3558437) B3558437
theorem B2372321 : Blo 1580488 2372321 := bstep (se 2 (by rfl) ⟨889620, by rfl⟩ : syracuseStep 2372321 = 1779241) B1779241
theorem B2667235 : Blo 1580488 2667235 := bstep (se 1 (by rfl) ⟨2000426, by rfl⟩ : syracuseStep 2667235 = 4000853) B4000853
theorem B2372339 : Blo 1580488 2372339 := bstep (se 1 (by rfl) ⟨1779254, by rfl⟩ : syracuseStep 2372339 = 3558509) B3558509
theorem B2372369 : Blo 1580488 2372369 := bstep (se 2 (by rfl) ⟨889638, by rfl⟩ : syracuseStep 2372369 = 1779277) B1779277
theorem B2372387 : Blo 1580488 2372387 := bstep (se 1 (by rfl) ⟨1779290, by rfl⟩ : syracuseStep 2372387 = 3558581) B3558581
theorem B2372417 : Blo 1580488 2372417 := bstep (se 2 (by rfl) ⟨889656, by rfl⟩ : syracuseStep 2372417 = 1779313) B1779313
theorem B12014405 : Blo 1580488 12014405 := bstep (se 4 (by rfl) ⟨1126350, by rfl⟩ : syracuseStep 12014405 = 2252701) B2252701
theorem B3560273 : Blo 1580488 3560273 := bstep (se 2 (by rfl) ⟨1335102, by rfl⟩ : syracuseStep 3560273 = 2670205) B2670205
theorem B2372435 : Blo 1580488 2372435 := bstep (se 1 (by rfl) ⟨1779326, by rfl⟩ : syracuseStep 2372435 = 3558653) B3558653
theorem B2405219 : Blo 1580488 2405219 := bstep (se 1 (by rfl) ⟨1803914, by rfl⟩ : syracuseStep 2405219 = 3607829) B3607829
theorem B3560291 : Blo 1580488 3560291 := bstep (se 1 (by rfl) ⟨2670218, by rfl⟩ : syracuseStep 3560291 = 5340437) B5340437
theorem B2667377 : Blo 1580488 2667377 := bstep (se 2 (by rfl) ⟨1000266, by rfl⟩ : syracuseStep 2667377 = 2000533) B2000533
theorem B2372465 : Blo 1580488 2372465 := bstep (se 2 (by rfl) ⟨889674, by rfl⟩ : syracuseStep 2372465 = 1779349) B1779349
theorem B28865393 : Blo 1580488 28865393 := bstep (se 2 (by rfl) ⟨10824522, by rfl⟩ : syracuseStep 28865393 = 21649045) B21649045
theorem B2372483 : Blo 1580488 2372483 := bstep (se 1 (by rfl) ⟨1779362, by rfl⟩ : syracuseStep 2372483 = 3558725) B3558725
theorem B2405267 : Blo 1580488 2405267 := bstep (se 1 (by rfl) ⟨1803950, by rfl⟩ : syracuseStep 2405267 = 3607901) B3607901
theorem B2372513 : Blo 1580488 2372513 := bstep (se 2 (by rfl) ⟨889692, by rfl⟩ : syracuseStep 2372513 = 1779385) B1779385
theorem B9622435 : Blo 1580488 9622435 := bstep (se 1 (by rfl) ⟨7216826, by rfl⟩ : syracuseStep 9622435 = 14433653) B14433653
theorem B3003313 : Blo 1580488 3003313 := bstep (se 2 (by rfl) ⟨1126242, by rfl⟩ : syracuseStep 3003313 = 2252485) B2252485
theorem B2372531 : Blo 1580488 2372531 := bstep (se 1 (by rfl) ⟨1779398, by rfl⟩ : syracuseStep 2372531 = 3558797) B3558797
theorem B3806147 : Blo 1580488 3806147 := bstep (se 1 (by rfl) ⟨2854610, by rfl⟩ : syracuseStep 3806147 = 5709221) B5709221
theorem B5338061 : Blo 1580488 5338061 := bstep (se 3 (by rfl) ⟨1000886, by rfl⟩ : syracuseStep 5338061 = 2001773) B2001773
theorem B2372561 : Blo 1580488 2372561 := bstep (se 2 (by rfl) ⟨889710, by rfl⟩ : syracuseStep 2372561 = 1779421) B1779421
theorem B2372579 : Blo 1580488 2372579 := bstep (se 1 (by rfl) ⟨1779434, by rfl⟩ : syracuseStep 2372579 = 3558869) B3558869
theorem B2667505 : Blo 1580488 2667505 := bstep (se 2 (by rfl) ⟨1000314, by rfl⟩ : syracuseStep 2667505 = 2000629) B2000629
theorem B2372609 : Blo 1580488 2372609 := bstep (se 2 (by rfl) ⟨889728, by rfl⟩ : syracuseStep 2372609 = 1779457) B1779457
theorem B5338115 : Blo 1580488 5338115 := bstep (se 1 (by rfl) ⟨4003586, by rfl⟩ : syracuseStep 5338115 = 8007173) B8007173
theorem B2667539 : Blo 1580488 2667539 := bstep (se 1 (by rfl) ⟨2000654, by rfl⟩ : syracuseStep 2667539 = 4001309) B4001309
theorem B2372627 : Blo 1580488 2372627 := bstep (se 1 (by rfl) ⟨1779470, by rfl⟩ : syracuseStep 2372627 = 3558941) B3558941
theorem B2372657 : Blo 1580488 2372657 := bstep (se 2 (by rfl) ⟨889746, by rfl⟩ : syracuseStep 2372657 = 1779493) B1779493
theorem B2372675 : Blo 1580488 2372675 := bstep (se 1 (by rfl) ⟨1779506, by rfl⟩ : syracuseStep 2372675 = 3559013) B3559013
theorem B3003473 : Blo 1580488 3003473 := bstep (se 2 (by rfl) ⟨1126302, by rfl⟩ : syracuseStep 3003473 = 2252605) B2252605
theorem B2372705 : Blo 1580488 2372705 := bstep (se 2 (by rfl) ⟨889764, by rfl⟩ : syracuseStep 2372705 = 1779529) B1779529
theorem B7599217 : Blo 1580488 7599217 := bstep (se 2 (by rfl) ⟨2849706, by rfl⟩ : syracuseStep 7599217 = 5699413) B5699413
theorem B4002929 : Blo 1580488 4002929 := bstep (se 2 (by rfl) ⟨1501098, by rfl⟩ : syracuseStep 4002929 = 3002197) B3002197
theorem B2372723 : Blo 1580488 2372723 := bstep (se 1 (by rfl) ⟨1779542, by rfl⟩ : syracuseStep 2372723 = 3559085) B3559085
theorem B3560561 : Blo 1580488 3560561 := bstep (se 2 (by rfl) ⟨1335210, by rfl⟩ : syracuseStep 3560561 = 2670421) B2670421
theorem B3560579 : Blo 1580488 3560579 := bstep (se 1 (by rfl) ⟨2670434, by rfl⟩ : syracuseStep 3560579 = 5340869) B5340869
theorem B2372753 : Blo 1580488 2372753 := bstep (se 2 (by rfl) ⟨889782, by rfl⟩ : syracuseStep 2372753 = 1779565) B1779565
theorem B2667667 : Blo 1580488 2667667 := bstep (se 1 (by rfl) ⟨2000750, by rfl⟩ : syracuseStep 2667667 = 4001501) B4001501
theorem B4002979 : Blo 1580488 4002979 := bstep (se 1 (by rfl) ⟨3002234, by rfl⟩ : syracuseStep 4002979 = 6004469) B6004469
theorem B2372771 : Blo 1580488 2372771 := bstep (se 1 (by rfl) ⟨1779578, by rfl⟩ : syracuseStep 2372771 = 3559157) B3559157
theorem B2372801 : Blo 1580488 2372801 := bstep (se 2 (by rfl) ⟨889800, by rfl⟩ : syracuseStep 2372801 = 1779601) B1779601
theorem B2372819 : Blo 1580488 2372819 := bstep (se 1 (by rfl) ⟨1779614, by rfl⟩ : syracuseStep 2372819 = 3559229) B3559229
theorem B66720995 : Blo 1580488 66720995 := bstep (se 1 (by rfl) ⟨50040746, by rfl⟩ : syracuseStep 66720995 = 100081493) B100081493
theorem B2372849 : Blo 1580488 2372849 := bstep (se 2 (by rfl) ⟨889818, by rfl⟩ : syracuseStep 2372849 = 1779637) B1779637
theorem B2372867 : Blo 1580488 2372867 := bstep (se 1 (by rfl) ⟨1779650, by rfl⟩ : syracuseStep 2372867 = 3559301) B3559301
theorem B5338385 : Blo 1580488 5338385 := bstep (se 2 (by rfl) ⟨2001894, by rfl⟩ : syracuseStep 5338385 = 4003789) B4003789
theorem B2667809 : Blo 1580488 2667809 := bstep (se 2 (by rfl) ⟨1000428, by rfl⟩ : syracuseStep 2667809 = 2000857) B2000857
theorem B2372897 : Blo 1580488 2372897 := bstep (se 2 (by rfl) ⟨889836, by rfl⟩ : syracuseStep 2372897 = 1779673) B1779673
theorem B4003121 : Blo 1580488 4003121 := bstep (se 2 (by rfl) ⟨1501170, by rfl⟩ : syracuseStep 4003121 = 3002341) B3002341
theorem B2372915 : Blo 1580488 2372915 := bstep (se 1 (by rfl) ⟨1779686, by rfl⟩ : syracuseStep 2372915 = 3559373) B3559373
theorem B2372945 : Blo 1580488 2372945 := bstep (se 2 (by rfl) ⟨889854, by rfl⟩ : syracuseStep 2372945 = 1779709) B1779709
theorem B2372963 : Blo 1580488 2372963 := bstep (se 1 (by rfl) ⟨1779722, by rfl⟩ : syracuseStep 2372963 = 3559445) B3559445
theorem B19232113 : Blo 1580488 19232113 := bstep (se 2 (by rfl) ⟨7212042, by rfl⟩ : syracuseStep 19232113 = 14424085) B14424085
theorem B4502897 : Blo 1580488 4502897 := bstep (se 2 (by rfl) ⟨1688586, by rfl⟩ : syracuseStep 4502897 = 3377173) B3377173
theorem B2372993 : Blo 1580488 2372993 := bstep (se 2 (by rfl) ⟨889872, by rfl⟩ : syracuseStep 2372993 = 1779745) B1779745
theorem B2373011 : Blo 1580488 2373011 := bstep (se 1 (by rfl) ⟨1779758, by rfl⟩ : syracuseStep 2373011 = 3559517) B3559517
theorem B2667937 : Blo 1580488 2667937 := bstep (se 2 (by rfl) ⟨1000476, by rfl⟩ : syracuseStep 2667937 = 2000953) B2000953
theorem B2373041 : Blo 1580488 2373041 := bstep (se 2 (by rfl) ⟨889890, by rfl⟩ : syracuseStep 2373041 = 1779781) B1779781
theorem B2667971 : Blo 1580488 2667971 := bstep (se 1 (by rfl) ⟨2000978, by rfl⟩ : syracuseStep 2667971 = 4001957) B4001957
theorem B2373059 : Blo 1580488 2373059 := bstep (se 1 (by rfl) ⟨1779794, by rfl⟩ : syracuseStep 2373059 = 3559589) B3559589
theorem B2373089 : Blo 1580488 2373089 := bstep (se 2 (by rfl) ⟨889908, by rfl⟩ : syracuseStep 2373089 = 1779817) B1779817
theorem B3003875 : Blo 1580488 3003875 := bstep (se 1 (by rfl) ⟨2252906, by rfl⟩ : syracuseStep 3003875 = 4505813) B4505813
theorem B2373107 : Blo 1580488 2373107 := bstep (se 1 (by rfl) ⟨1779830, by rfl⟩ : syracuseStep 2373107 = 3559661) B3559661
theorem B2373137 : Blo 1580488 2373137 := bstep (se 2 (by rfl) ⟨889926, by rfl⟩ : syracuseStep 2373137 = 1779853) B1779853
theorem B2373155 : Blo 1580488 2373155 := bstep (se 1 (by rfl) ⟨1779866, by rfl⟩ : syracuseStep 2373155 = 3559733) B3559733
theorem B2373185 : Blo 1580488 2373185 := bstep (se 2 (by rfl) ⟨889944, by rfl⟩ : syracuseStep 2373185 = 1779889) B1779889
theorem B2668099 : Blo 1580488 2668099 := bstep (se 1 (by rfl) ⟨2001074, by rfl⟩ : syracuseStep 2668099 = 4002149) B4002149
theorem B3044945 : Blo 1580488 3044945 := bstep (se 2 (by rfl) ⟨1141854, by rfl⟩ : syracuseStep 3044945 = 2283709) B2283709
theorem B2373203 : Blo 1580488 2373203 := bstep (se 1 (by rfl) ⟨1779902, by rfl⟩ : syracuseStep 2373203 = 3559805) B3559805
theorem B2438755 : Blo 1580488 2438755 := bstep (se 1 (by rfl) ⟨1829066, by rfl⟩ : syracuseStep 2438755 = 3658133) B3658133
theorem B18257521 : Blo 1580488 18257521 := bstep (se 2 (by rfl) ⟨6846570, by rfl⟩ : syracuseStep 18257521 = 13693141) B13693141
theorem B2373233 : Blo 1580488 2373233 := bstep (se 2 (by rfl) ⟨889962, by rfl⟩ : syracuseStep 2373233 = 1779925) B1779925
theorem B2250355 : Blo 1580488 2250355 := bstep (se 1 (by rfl) ⟨1687766, by rfl⟩ : syracuseStep 2250355 = 3375533) B3375533
theorem B2373251 : Blo 1580488 2373251 := bstep (se 1 (by rfl) ⟨1779938, by rfl⟩ : syracuseStep 2373251 = 3559877) B3559877
theorem B2373281 : Blo 1580488 2373281 := bstep (se 2 (by rfl) ⟨889980, by rfl⟩ : syracuseStep 2373281 = 1779961) B1779961
theorem B2373299 : Blo 1580488 2373299 := bstep (se 1 (by rfl) ⟨1779974, by rfl⟩ : syracuseStep 2373299 = 3559949) B3559949
theorem B2668241 : Blo 1580488 2668241 := bstep (se 2 (by rfl) ⟨1000590, by rfl⟩ : syracuseStep 2668241 = 2001181) B2001181
theorem B2373329 : Blo 1580488 2373329 := bstep (se 2 (by rfl) ⟨889998, by rfl⟩ : syracuseStep 2373329 = 1779997) B1779997
theorem B2373347 : Blo 1580488 2373347 := bstep (se 1 (by rfl) ⟨1780010, by rfl⟩ : syracuseStep 2373347 = 3560021) B3560021
theorem B2373377 : Blo 1580488 2373377 := bstep (se 2 (by rfl) ⟨890016, by rfl⟩ : syracuseStep 2373377 = 1780033) B1780033
theorem B14620429 : Blo 1580488 14620429 := bstep (se 3 (by rfl) ⟨2741330, by rfl⟩ : syracuseStep 14620429 = 5482661) B5482661
theorem B2373395 : Blo 1580488 2373395 := bstep (se 1 (by rfl) ⟨1780046, by rfl⟩ : syracuseStep 2373395 = 3560093) B3560093
theorem B4273955 : Blo 1580488 4273955 := bstep (se 1 (by rfl) ⟨3205466, by rfl⟩ : syracuseStep 4273955 = 6410933) B6410933
theorem B5338925 : Blo 1580488 5338925 := bstep (se 3 (by rfl) ⟨1001048, by rfl⟩ : syracuseStep 5338925 = 2002097) B2002097
theorem B2373425 : Blo 1580488 2373425 := bstep (se 2 (by rfl) ⟨890034, by rfl⟩ : syracuseStep 2373425 = 1780069) B1780069
theorem B2373443 : Blo 1580488 2373443 := bstep (se 1 (by rfl) ⟨1780082, by rfl⟩ : syracuseStep 2373443 = 3560165) B3560165
theorem B2668369 : Blo 1580488 2668369 := bstep (se 2 (by rfl) ⟨1000638, by rfl⟩ : syracuseStep 2668369 = 2001277) B2001277
theorem B5412689 : Blo 1580488 5412689 := bstep (se 2 (by rfl) ⟨2029758, by rfl⟩ : syracuseStep 5412689 = 4059517) B4059517
theorem B2373473 : Blo 1580488 2373473 := bstep (se 2 (by rfl) ⟨890052, by rfl⟩ : syracuseStep 2373473 = 1780105) B1780105
theorem B5338979 : Blo 1580488 5338979 := bstep (se 1 (by rfl) ⟨4004234, by rfl⟩ : syracuseStep 5338979 = 8008469) B8008469
theorem B2848625 : Blo 1580488 2848625 := bstep (se 2 (by rfl) ⟨1068234, by rfl⟩ : syracuseStep 2848625 = 2136469) B2136469
theorem B2668403 : Blo 1580488 2668403 := bstep (se 1 (by rfl) ⟨2001302, by rfl⟩ : syracuseStep 2668403 = 4002605) B4002605
theorem B2373491 : Blo 1580488 2373491 := bstep (se 1 (by rfl) ⟨1780118, by rfl⟩ : syracuseStep 2373491 = 3560237) B3560237
theorem B2373521 : Blo 1580488 2373521 := bstep (se 2 (by rfl) ⟨890070, by rfl⟩ : syracuseStep 2373521 = 1780141) B1780141
theorem B2373539 : Blo 1580488 2373539 := bstep (se 1 (by rfl) ⟨1780154, by rfl⟩ : syracuseStep 2373539 = 3560309) B3560309
theorem B2373569 : Blo 1580488 2373569 := bstep (se 2 (by rfl) ⟨890088, by rfl⟩ : syracuseStep 2373569 = 1780177) B1780177
theorem B2373587 : Blo 1580488 2373587 := bstep (se 1 (by rfl) ⟨1780190, by rfl⟩ : syracuseStep 2373587 = 3560381) B3560381
theorem B18012131 : Blo 1580488 18012131 := bstep (se 1 (by rfl) ⟨13509098, by rfl⟩ : syracuseStep 18012131 = 27018197) B27018197
theorem B17102819 : Blo 1580488 17102819 := bstep (se 1 (by rfl) ⟨12827114, by rfl⟩ : syracuseStep 17102819 = 25654229) B25654229
theorem B16234481 : Blo 1580488 16234481 := bstep (se 2 (by rfl) ⟨6087930, by rfl⟩ : syracuseStep 16234481 = 12175861) B12175861
theorem B2373617 : Blo 1580488 2373617 := bstep (se 2 (by rfl) ⟨890106, by rfl⟩ : syracuseStep 2373617 = 1780213) B1780213
theorem B2668531 : Blo 1580488 2668531 := bstep (se 1 (by rfl) ⟨2001398, by rfl⟩ : syracuseStep 2668531 = 4002797) B4002797
theorem B2373635 : Blo 1580488 2373635 := bstep (se 1 (by rfl) ⟨1780226, by rfl⟩ : syracuseStep 2373635 = 3560453) B3560453
theorem B2373665 : Blo 1580488 2373665 := bstep (se 2 (by rfl) ⟨890124, by rfl⟩ : syracuseStep 2373665 = 1780249) B1780249
theorem B4626467 : Blo 1580488 4626467 := bstep (se 1 (by rfl) ⟨3469850, by rfl⟩ : syracuseStep 4626467 = 6939701) B6939701
theorem B2373683 : Blo 1580488 2373683 := bstep (se 1 (by rfl) ⟨1780262, by rfl⟩ : syracuseStep 2373683 = 3560525) B3560525
theorem B21649477 : Blo 1580488 21649477 := bstep (se 4 (by rfl) ⟨2029638, by rfl⟩ : syracuseStep 21649477 = 4059277) B4059277
theorem B2250833 : Blo 1580488 2250833 := bstep (se 2 (by rfl) ⟨844062, by rfl⟩ : syracuseStep 2250833 = 1688125) B1688125
theorem B2373713 : Blo 1580488 2373713 := bstep (se 2 (by rfl) ⟨890142, by rfl⟩ : syracuseStep 2373713 = 1780285) B1780285
theorem B2373731 : Blo 1580488 2373731 := bstep (se 1 (by rfl) ⟨1780298, by rfl⟩ : syracuseStep 2373731 = 3560597) B3560597
theorem B5339249 : Blo 1580488 5339249 := bstep (se 2 (by rfl) ⟨2002218, by rfl⟩ : syracuseStep 5339249 = 4004437) B4004437
theorem B2668673 : Blo 1580488 2668673 := bstep (se 2 (by rfl) ⟨1000752, by rfl⟩ : syracuseStep 2668673 = 2001505) B2001505
theorem B2250947 : Blo 1580488 2250947 := bstep (se 1 (by rfl) ⟨1688210, by rfl⟩ : syracuseStep 2250947 = 3376421) B3376421
theorem B1603795 : Blo 1580488 1603795 := bstep (se 1 (by rfl) ⟨1202846, by rfl⟩ : syracuseStep 1603795 = 2405693) B2405693
theorem B2668801 : Blo 1580488 2668801 := bstep (se 2 (by rfl) ⟨1000800, by rfl⟩ : syracuseStep 2668801 = 2001601) B2001601
theorem B4004113 : Blo 1580488 4004113 := bstep (se 2 (by rfl) ⟨1501542, by rfl⟩ : syracuseStep 4004113 = 3003085) B3003085
theorem B2251027 : Blo 1580488 2251027 := bstep (se 1 (by rfl) ⟨1688270, by rfl⟩ : syracuseStep 2251027 = 3376541) B3376541
theorem B8001827 : Blo 1580488 8001827 := bstep (se 1 (by rfl) ⟨6001370, by rfl⟩ : syracuseStep 8001827 = 12002741) B12002741
theorem B2668835 : Blo 1580488 2668835 := bstep (se 1 (by rfl) ⟨2001626, by rfl⟩ : syracuseStep 2668835 = 4003253) B4003253
theorem B4503853 : Blo 1580488 4503853 := bstep (se 3 (by rfl) ⟨844472, by rfl⟩ : syracuseStep 4503853 = 1688945) B1688945
theorem B4331939 : Blo 1580488 4331939 := bstep (se 1 (by rfl) ⟨3248954, by rfl⟩ : syracuseStep 4331939 = 6497909) B6497909
theorem B2668963 : Blo 1580488 2668963 := bstep (se 1 (by rfl) ⟨2001722, by rfl⟩ : syracuseStep 2668963 = 4003445) B4003445
theorem B5700017 : Blo 1580488 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B4504081 : Blo 1580488 4504081 := bstep (se 2 (by rfl) ⟨1689030, by rfl⟩ : syracuseStep 4504081 = 3378061) B3378061
theorem B4004387 : Blo 1580488 4004387 := bstep (se 1 (by rfl) ⟨3003290, by rfl⟩ : syracuseStep 4004387 = 6006581) B6006581
theorem B2669105 : Blo 1580488 2669105 := bstep (se 2 (by rfl) ⟨1000914, by rfl⟩ : syracuseStep 2669105 = 2001829) B2001829
theorem B4274797 : Blo 1580488 4274797 := bstep (se 3 (by rfl) ⟨801524, by rfl⟩ : syracuseStep 4274797 = 1603049) B1603049
theorem B5069425 : Blo 1580488 5069425 := bstep (se 2 (by rfl) ⟨1901034, by rfl⟩ : syracuseStep 5069425 = 3802069) B3802069
theorem B5339789 : Blo 1580488 5339789 := bstep (se 3 (by rfl) ⟨1001210, by rfl⟩ : syracuseStep 5339789 = 2002421) B2002421
theorem B4504241 : Blo 1580488 4504241 := bstep (se 2 (by rfl) ⟨1689090, by rfl⟩ : syracuseStep 4504241 = 3378181) B3378181
theorem B2669233 : Blo 1580488 2669233 := bstep (se 2 (by rfl) ⟨1000962, by rfl⟩ : syracuseStep 2669233 = 2001925) B2001925
theorem B5339843 : Blo 1580488 5339843 := bstep (se 1 (by rfl) ⟨4004882, by rfl⟩ : syracuseStep 5339843 = 8009765) B8009765
theorem B2669267 : Blo 1580488 2669267 := bstep (se 1 (by rfl) ⟨2001950, by rfl⟩ : syracuseStep 2669267 = 4003901) B4003901
theorem B4004579 : Blo 1580488 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B3799811 : Blo 1580488 3799811 := bstep (se 1 (by rfl) ⟨2849858, by rfl⟩ : syracuseStep 3799811 = 5699717) B5699717
theorem B4504355 : Blo 1580488 4504355 := bstep (se 1 (by rfl) ⟨3378266, by rfl⟩ : syracuseStep 4504355 = 6756533) B6756533
theorem B5069603 : Blo 1580488 5069603 := bstep (se 1 (by rfl) ⟨3802202, by rfl⟩ : syracuseStep 5069603 = 7604405) B7604405
theorem B4274993 : Blo 1580488 4274993 := bstep (se 2 (by rfl) ⟨1603122, by rfl⟩ : syracuseStep 4274993 = 3206245) B3206245
theorem B32889653 : Blo 1580488 32889653 := bstep (se 5 (by rfl) ⟨1541702, by rfl⟩ : syracuseStep 32889653 = 3083405) B3083405
theorem B2251585 : Blo 1580488 2251585 := bstep (se 2 (by rfl) ⟨844344, by rfl⟩ : syracuseStep 2251585 = 1688689) B1688689
theorem B2669395 : Blo 1580488 2669395 := bstep (se 1 (by rfl) ⟨2002046, by rfl⟩ : syracuseStep 2669395 = 4004093) B4004093
theorem B2136961 : Blo 1580488 2136961 := bstep (se 2 (by rfl) ⟨801360, by rfl⟩ : syracuseStep 2136961 = 1602721) B1602721
theorem B6413219 : Blo 1580488 6413219 := bstep (se 1 (by rfl) ⟨4809914, by rfl⟩ : syracuseStep 6413219 = 9619829) B9619829
theorem B6757283 : Blo 1580488 6757283 := bstep (se 1 (by rfl) ⟨5067962, by rfl⟩ : syracuseStep 6757283 = 10135925) B10135925
theorem B5340113 : Blo 1580488 5340113 := bstep (se 2 (by rfl) ⟨2002542, by rfl⟩ : syracuseStep 5340113 = 4005085) B4005085
theorem B2669537 : Blo 1580488 2669537 := bstep (se 2 (by rfl) ⟨1001076, by rfl⟩ : syracuseStep 2669537 = 2002153) B2002153
theorem B8010737 : Blo 1580488 8010737 := bstep (se 2 (by rfl) ⟨3004026, by rfl⟩ : syracuseStep 8010737 = 6008053) B6008053
theorem B8002637 : Blo 1580488 8002637 := bstep (se 3 (by rfl) ⟨1500494, by rfl⟩ : syracuseStep 8002637 = 3000989) B3000989
theorem B2669665 : Blo 1580488 2669665 := bstep (se 2 (by rfl) ⟨1001124, by rfl⟩ : syracuseStep 2669665 = 2002249) B2002249
theorem B18250865 : Blo 1580488 18250865 := bstep (se 2 (by rfl) ⟨6844074, by rfl⟩ : syracuseStep 18250865 = 13688149) B13688149
theorem B2669699 : Blo 1580488 2669699 := bstep (se 1 (by rfl) ⟨2002274, by rfl⟩ : syracuseStep 2669699 = 4004549) B4004549
theorem B6003953 : Blo 1580488 6003953 := bstep (se 2 (by rfl) ⟨2251482, by rfl⟩ : syracuseStep 6003953 = 4502965) B4502965
theorem B2669827 : Blo 1580488 2669827 := bstep (se 1 (by rfl) ⟨2002370, by rfl⟩ : syracuseStep 2669827 = 4004741) B4004741
theorem B2669969 : Blo 1580488 2669969 := bstep (se 2 (by rfl) ⟨1001238, by rfl⟩ : syracuseStep 2669969 = 2002477) B2002477
theorem B1580499 : Blo 1580488 1580499 := bstep (se 1 (by rfl) ⟨1185374, by rfl⟩ : syracuseStep 1580499 = 2370749) B2370749
theorem B1580515 : Blo 1580488 1580515 := bstep (se 1 (by rfl) ⟨1185386, by rfl⟩ : syracuseStep 1580515 = 2370773) B2370773
theorem B5340653 : Blo 1580488 5340653 := bstep (se 3 (by rfl) ⟨1001372, by rfl⟩ : syracuseStep 5340653 = 2002745) B2002745
theorem B1580531 : Blo 1580488 1580531 := bstep (se 1 (by rfl) ⟨1185398, by rfl⟩ : syracuseStep 1580531 = 2370797) B2370797
theorem B1580547 : Blo 1580488 1580547 := bstep (se 1 (by rfl) ⟨1185410, by rfl⟩ : syracuseStep 1580547 = 2370821) B2370821
theorem B2252291 : Blo 1580488 2252291 := bstep (se 1 (by rfl) ⟨1689218, by rfl⟩ : syracuseStep 2252291 = 3378437) B3378437
theorem B2670097 : Blo 1580488 2670097 := bstep (se 2 (by rfl) ⟨1001286, by rfl⟩ : syracuseStep 2670097 = 2002573) B2002573
theorem B1580563 : Blo 1580488 1580563 := bstep (se 1 (by rfl) ⟨1185422, by rfl⟩ : syracuseStep 1580563 = 2370845) B2370845
theorem B1580579 : Blo 1580488 1580579 := bstep (se 1 (by rfl) ⟨1185434, by rfl⟩ : syracuseStep 1580579 = 2370869) B2370869
theorem B5340707 : Blo 1580488 5340707 := bstep (se 1 (by rfl) ⟨4005530, by rfl⟩ : syracuseStep 5340707 = 8011061) B8011061
theorem B1580595 : Blo 1580488 1580595 := bstep (se 1 (by rfl) ⟨1185446, by rfl⟩ : syracuseStep 1580595 = 2370893) B2370893
theorem B2670131 : Blo 1580488 2670131 := bstep (se 1 (by rfl) ⟨2002598, by rfl⟩ : syracuseStep 2670131 = 4005197) B4005197
theorem B1580611 : Blo 1580488 1580611 := bstep (se 1 (by rfl) ⟨1185458, by rfl⟩ : syracuseStep 1580611 = 2370917) B2370917
theorem B3800657 : Blo 1580488 3800657 := bstep (se 2 (by rfl) ⟨1425246, by rfl⟩ : syracuseStep 3800657 = 2850493) B2850493
theorem B1580627 : Blo 1580488 1580627 := bstep (se 1 (by rfl) ⟨1185470, by rfl⟩ : syracuseStep 1580627 = 2370941) B2370941
theorem B1580643 : Blo 1580488 1580643 := bstep (se 1 (by rfl) ⟨1185482, by rfl⟩ : syracuseStep 1580643 = 2370965) B2370965
theorem B12009059 : Blo 1580488 12009059 := bstep (se 1 (by rfl) ⟨9006794, by rfl⟩ : syracuseStep 12009059 = 18013589) B18013589
theorem B1580659 : Blo 1580488 1580659 := bstep (se 1 (by rfl) ⟨1185494, by rfl⟩ : syracuseStep 1580659 = 2370989) B2370989
theorem B1580675 : Blo 1580488 1580675 := bstep (se 1 (by rfl) ⟨1185506, by rfl⟩ : syracuseStep 1580675 = 2371013) B2371013
theorem B4005521 : Blo 1580488 4005521 := bstep (se 2 (by rfl) ⟨1502070, by rfl⟩ : syracuseStep 4005521 = 3004141) B3004141
theorem B1580691 : Blo 1580488 1580691 := bstep (se 1 (by rfl) ⟨1185518, by rfl⟩ : syracuseStep 1580691 = 2371037) B2371037
theorem B1580707 : Blo 1580488 1580707 := bstep (se 1 (by rfl) ⟨1185530, by rfl⟩ : syracuseStep 1580707 = 2371061) B2371061
theorem B1580723 : Blo 1580488 1580723 := bstep (se 1 (by rfl) ⟨1185542, by rfl⟩ : syracuseStep 1580723 = 2371085) B2371085
theorem B2670259 : Blo 1580488 2670259 := bstep (se 1 (by rfl) ⟨2002694, by rfl⟩ : syracuseStep 2670259 = 4005389) B4005389
theorem B1580739 : Blo 1580488 1580739 := bstep (se 1 (by rfl) ⟨1185554, by rfl⟩ : syracuseStep 1580739 = 2371109) B2371109
theorem B4005571 : Blo 1580488 4005571 := bstep (se 1 (by rfl) ⟨3004178, by rfl⟩ : syracuseStep 4005571 = 6008357) B6008357
theorem B1580755 : Blo 1580488 1580755 := bstep (se 1 (by rfl) ⟨1185566, by rfl⟩ : syracuseStep 1580755 = 2371133) B2371133
theorem B1580771 : Blo 1580488 1580771 := bstep (se 1 (by rfl) ⟨1185578, by rfl⟩ : syracuseStep 1580771 = 2371157) B2371157
theorem B28860131 : Blo 1580488 28860131 := bstep (se 1 (by rfl) ⟨21645098, by rfl⟩ : syracuseStep 28860131 = 43290197) B43290197
theorem B1580787 : Blo 1580488 1580787 := bstep (se 1 (by rfl) ⟨1185590, by rfl⟩ : syracuseStep 1580787 = 2371181) B2371181
theorem B1580803 : Blo 1580488 1580803 := bstep (se 1 (by rfl) ⟨1185602, by rfl⟩ : syracuseStep 1580803 = 2371205) B2371205
theorem B10133261 : Blo 1580488 10133261 := bstep (se 3 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 10133261 = 3799973) B3799973
theorem B4505357 : Blo 1580488 4505357 := bstep (se 3 (by rfl) ⟨844754, by rfl⟩ : syracuseStep 4505357 = 1689509) B1689509
theorem B1580819 : Blo 1580488 1580819 := bstep (se 1 (by rfl) ⟨1185614, by rfl⟩ : syracuseStep 1580819 = 2371229) B2371229
theorem B1580835 : Blo 1580488 1580835 := bstep (se 1 (by rfl) ⟨1185626, by rfl⟩ : syracuseStep 1580835 = 2371253) B2371253
theorem B1580851 : Blo 1580488 1580851 := bstep (se 1 (by rfl) ⟨1185638, by rfl⟩ : syracuseStep 1580851 = 2371277) B2371277
theorem B2670401 : Blo 1580488 2670401 := bstep (se 2 (by rfl) ⟨1001400, by rfl⟩ : syracuseStep 2670401 = 2002801) B2002801
theorem B1580867 : Blo 1580488 1580867 := bstep (se 1 (by rfl) ⟨1185650, by rfl⟩ : syracuseStep 1580867 = 2371301) B2371301
theorem B1580883 : Blo 1580488 1580883 := bstep (se 1 (by rfl) ⟨1185662, by rfl⟩ : syracuseStep 1580883 = 2371325) B2371325
theorem B1580899 : Blo 1580488 1580899 := bstep (se 1 (by rfl) ⟨1185674, by rfl⟩ : syracuseStep 1580899 = 2371349) B2371349
theorem B1580915 : Blo 1580488 1580915 := bstep (se 1 (by rfl) ⟨1185686, by rfl⟩ : syracuseStep 1580915 = 2371373) B2371373
theorem B1580931 : Blo 1580488 1580931 := bstep (se 1 (by rfl) ⟨1185698, by rfl⟩ : syracuseStep 1580931 = 2371397) B2371397
theorem B1580947 : Blo 1580488 1580947 := bstep (se 1 (by rfl) ⟨1185710, by rfl⟩ : syracuseStep 1580947 = 2371421) B2371421
theorem B1580963 : Blo 1580488 1580963 := bstep (se 1 (by rfl) ⟨1185722, by rfl⟩ : syracuseStep 1580963 = 2371445) B2371445
theorem B1580979 : Blo 1580488 1580979 := bstep (se 1 (by rfl) ⟨1185734, by rfl⟩ : syracuseStep 1580979 = 2371469) B2371469
theorem B1580995 : Blo 1580488 1580995 := bstep (se 1 (by rfl) ⟨1185746, by rfl⟩ : syracuseStep 1580995 = 2371493) B2371493
theorem B4505539 : Blo 1580488 4505539 := bstep (se 1 (by rfl) ⟨3379154, by rfl⟩ : syracuseStep 4505539 = 6758309) B6758309
theorem B1581011 : Blo 1580488 1581011 := bstep (se 1 (by rfl) ⟨1185758, by rfl⟩ : syracuseStep 1581011 = 2371517) B2371517
theorem B1581027 : Blo 1580488 1581027 := bstep (se 1 (by rfl) ⟨1185770, by rfl⟩ : syracuseStep 1581027 = 2371541) B2371541
theorem B1581043 : Blo 1580488 1581043 := bstep (se 1 (by rfl) ⟨1185782, by rfl⟩ : syracuseStep 1581043 = 2371565) B2371565
theorem B1581067 : Blo 1580488 1581067 := bstep (se 1 (by rfl) ⟨1185800, by rfl⟩ : syracuseStep 1581067 = 2371601) B2371601
theorem B1581079 : Blo 1580488 1581079 := bstep (se 1 (by rfl) ⟨1185809, by rfl⟩ : syracuseStep 1581079 = 2371619) B2371619
theorem B1581099 : Blo 1580488 1581099 := bstep (se 1 (by rfl) ⟨1185824, by rfl⟩ : syracuseStep 1581099 = 2371649) B2371649
theorem B1581111 : Blo 1580488 1581111 := bstep (se 1 (by rfl) ⟨1185833, by rfl⟩ : syracuseStep 1581111 = 2371667) B2371667
theorem B4505665 : Blo 1580488 4505665 := bstep (se 2 (by rfl) ⟨1689624, by rfl⟩ : syracuseStep 4505665 = 3379249) B3379249
theorem B1581131 : Blo 1580488 1581131 := bstep (se 1 (by rfl) ⟨1185848, by rfl⟩ : syracuseStep 1581131 = 2371697) B2371697
theorem B1581143 : Blo 1580488 1581143 := bstep (se 1 (by rfl) ⟨1185857, by rfl⟩ : syracuseStep 1581143 = 2371715) B2371715
theorem B1581163 : Blo 1580488 1581163 := bstep (se 1 (by rfl) ⟨1185872, by rfl⟩ : syracuseStep 1581163 = 2371745) B2371745
theorem B1581175 : Blo 1580488 1581175 := bstep (se 1 (by rfl) ⟨1185881, by rfl⟩ : syracuseStep 1581175 = 2371763) B2371763
theorem B18260099 : Blo 1580488 18260099 := bstep (se 1 (by rfl) ⟨13695074, by rfl⟩ : syracuseStep 18260099 = 27390149) B27390149
theorem B1581195 : Blo 1580488 1581195 := bstep (se 1 (by rfl) ⟨1185896, by rfl⟩ : syracuseStep 1581195 = 2371793) B2371793
theorem B1581207 : Blo 1580488 1581207 := bstep (se 1 (by rfl) ⟨1185905, by rfl⟩ : syracuseStep 1581207 = 2371811) B2371811
theorem B4808855 : Blo 1580488 4808855 := bstep (se 1 (by rfl) ⟨3606641, by rfl⟩ : syracuseStep 4808855 = 7213283) B7213283
theorem B15204503 : Blo 1580488 15204503 := bstep (se 1 (by rfl) ⟨11403377, by rfl⟩ : syracuseStep 15204503 = 22806755) B22806755
theorem B9011351 : Blo 1580488 9011351 := bstep (se 1 (by rfl) ⟨6758513, by rfl⟩ : syracuseStep 9011351 = 13517027) B13517027
theorem B1581227 : Blo 1580488 1581227 := bstep (se 1 (by rfl) ⟨1185920, by rfl⟩ : syracuseStep 1581227 = 2371841) B2371841
theorem B1581239 : Blo 1580488 1581239 := bstep (se 1 (by rfl) ⟨1185929, by rfl⟩ : syracuseStep 1581239 = 2371859) B2371859
theorem B1581259 : Blo 1580488 1581259 := bstep (se 1 (by rfl) ⟨1185944, by rfl⟩ : syracuseStep 1581259 = 2371889) B2371889
theorem B1581271 : Blo 1580488 1581271 := bstep (se 1 (by rfl) ⟨1185953, by rfl⟩ : syracuseStep 1581271 = 2371907) B2371907
theorem B1581291 : Blo 1580488 1581291 := bstep (se 1 (by rfl) ⟨1185968, by rfl⟩ : syracuseStep 1581291 = 2371937) B2371937
theorem B1581303 : Blo 1580488 1581303 := bstep (se 1 (by rfl) ⟨1185977, by rfl⟩ : syracuseStep 1581303 = 2371955) B2371955
theorem B1581323 : Blo 1580488 1581323 := bstep (se 1 (by rfl) ⟨1185992, by rfl⟩ : syracuseStep 1581323 = 2371985) B2371985
theorem B3424523 : Blo 1580488 3424523 := bstep (se 1 (by rfl) ⟨2568392, by rfl⟩ : syracuseStep 3424523 = 5136785) B5136785
theorem B1581335 : Blo 1580488 1581335 := bstep (se 1 (by rfl) ⟨1186001, by rfl⟩ : syracuseStep 1581335 = 2372003) B2372003
theorem B2138393 : Blo 1580488 2138393 := bstep (se 2 (by rfl) ⟨801897, by rfl⟩ : syracuseStep 2138393 = 1603795) B1603795
theorem B1581355 : Blo 1580488 1581355 := bstep (se 1 (by rfl) ⟨1186016, by rfl⟩ : syracuseStep 1581355 = 2372033) B2372033
theorem B1581367 : Blo 1580488 1581367 := bstep (se 1 (by rfl) ⟨1186025, by rfl⟩ : syracuseStep 1581367 = 2372051) B2372051
theorem B1581387 : Blo 1580488 1581387 := bstep (se 1 (by rfl) ⟨1186040, by rfl⟩ : syracuseStep 1581387 = 2372081) B2372081
theorem B1581399 : Blo 1580488 1581399 := bstep (se 1 (by rfl) ⟨1186049, by rfl⟩ : syracuseStep 1581399 = 2372099) B2372099
theorem B8003933 : Blo 1580488 8003933 := bstep (se 3 (by rfl) ⟨1500737, by rfl⟩ : syracuseStep 8003933 = 3001475) B3001475
theorem B1581419 : Blo 1580488 1581419 := bstep (se 1 (by rfl) ⟨1186064, by rfl⟩ : syracuseStep 1581419 = 2372129) B2372129
theorem B1581431 : Blo 1580488 1581431 := bstep (se 1 (by rfl) ⟨1186073, by rfl⟩ : syracuseStep 1581431 = 2372147) B2372147
theorem B6005123 : Blo 1580488 6005123 := bstep (se 1 (by rfl) ⟨4503842, by rfl⟩ : syracuseStep 6005123 = 9007685) B9007685
theorem B1581451 : Blo 1580488 1581451 := bstep (se 1 (by rfl) ⟨1186088, by rfl⟩ : syracuseStep 1581451 = 2372177) B2372177
theorem B6005137 : Blo 1580488 6005137 := bstep (se 2 (by rfl) ⟨2251926, by rfl⟩ : syracuseStep 6005137 = 4503853) B4503853
theorem B1778071 : Blo 1580488 1778071 := bstep (se 1 (by rfl) ⟨1333553, by rfl⟩ : syracuseStep 1778071 = 2667107) B2667107
theorem B1581463 : Blo 1580488 1581463 := bstep (se 1 (by rfl) ⟨1186097, by rfl⟩ : syracuseStep 1581463 = 2372195) B2372195
theorem B1581483 : Blo 1580488 1581483 := bstep (se 1 (by rfl) ⟨1186112, by rfl⟩ : syracuseStep 1581483 = 2372225) B2372225
theorem B1581495 : Blo 1580488 1581495 := bstep (se 1 (by rfl) ⟨1186121, by rfl⟩ : syracuseStep 1581495 = 2372243) B2372243
theorem B1581515 : Blo 1580488 1581515 := bstep (se 1 (by rfl) ⟨1186136, by rfl⟩ : syracuseStep 1581515 = 2372273) B2372273
theorem B1581527 : Blo 1580488 1581527 := bstep (se 1 (by rfl) ⟨1186145, by rfl⟩ : syracuseStep 1581527 = 2372291) B2372291
theorem B1581547 : Blo 1580488 1581547 := bstep (se 1 (by rfl) ⟨1186160, by rfl⟩ : syracuseStep 1581547 = 2372321) B2372321
theorem B1581559 : Blo 1580488 1581559 := bstep (se 1 (by rfl) ⟨1186169, by rfl⟩ : syracuseStep 1581559 = 2372339) B2372339
theorem B1581579 : Blo 1580488 1581579 := bstep (se 1 (by rfl) ⟨1186184, by rfl⟩ : syracuseStep 1581579 = 2372369) B2372369
theorem B1688087 : Blo 1580488 1688087 := bstep (se 1 (by rfl) ⟨1266065, by rfl⟩ : syracuseStep 1688087 = 2532131) B2532131
theorem B1581591 : Blo 1580488 1581591 := bstep (se 1 (by rfl) ⟨1186193, by rfl⟩ : syracuseStep 1581591 = 2372387) B2372387
theorem B1581611 : Blo 1580488 1581611 := bstep (se 1 (by rfl) ⟨1186208, by rfl⟩ : syracuseStep 1581611 = 2372417) B2372417
theorem B2851379 : Blo 1580488 2851379 := bstep (se 1 (by rfl) ⟨2138534, by rfl⟩ : syracuseStep 2851379 = 4277069) B4277069
theorem B1581623 : Blo 1580488 1581623 := bstep (se 1 (by rfl) ⟨1186217, by rfl⟩ : syracuseStep 1581623 = 2372435) B2372435
theorem B1778251 : Blo 1580488 1778251 := bstep (se 1 (by rfl) ⟨1333688, by rfl⟩ : syracuseStep 1778251 = 2667377) B2667377
theorem B1581643 : Blo 1580488 1581643 := bstep (se 1 (by rfl) ⟨1186232, by rfl⟩ : syracuseStep 1581643 = 2372465) B2372465
theorem B19243595 : Blo 1580488 19243595 := bstep (se 1 (by rfl) ⟨14432696, by rfl⟩ : syracuseStep 19243595 = 28865393) B28865393
theorem B3375703 : Blo 1580488 3375703 := bstep (se 1 (by rfl) ⟨2531777, by rfl⟩ : syracuseStep 3375703 = 5063555) B5063555
theorem B1581655 : Blo 1580488 1581655 := bstep (se 1 (by rfl) ⟨1186241, by rfl⟩ : syracuseStep 1581655 = 2372483) B2372483
theorem B8553053 : Blo 1580488 8553053 := bstep (se 3 (by rfl) ⟨1603697, by rfl⟩ : syracuseStep 8553053 = 3207395) B3207395
theorem B1581675 : Blo 1580488 1581675 := bstep (se 1 (by rfl) ⟨1186256, by rfl⟩ : syracuseStep 1581675 = 2372513) B2372513
theorem B1581687 : Blo 1580488 1581687 := bstep (se 1 (by rfl) ⟨1186265, by rfl⟩ : syracuseStep 1581687 = 2372531) B2372531
theorem B1581707 : Blo 1580488 1581707 := bstep (se 1 (by rfl) ⟨1186280, by rfl⟩ : syracuseStep 1581707 = 2372561) B2372561
theorem B1581719 : Blo 1580488 1581719 := bstep (se 1 (by rfl) ⟨1186289, by rfl⟩ : syracuseStep 1581719 = 2372579) B2372579
theorem B1581739 : Blo 1580488 1581739 := bstep (se 1 (by rfl) ⟨1186304, by rfl⟩ : syracuseStep 1581739 = 2372609) B2372609
theorem B1778359 : Blo 1580488 1778359 := bstep (se 1 (by rfl) ⟨1333769, by rfl⟩ : syracuseStep 1778359 = 2667539) B2667539
theorem B1581751 : Blo 1580488 1581751 := bstep (se 1 (by rfl) ⟨1186313, by rfl⟩ : syracuseStep 1581751 = 2372627) B2372627
theorem B6005441 : Blo 1580488 6005441 := bstep (se 2 (by rfl) ⟨2252040, by rfl⟩ : syracuseStep 6005441 = 4504081) B4504081
theorem B1581771 : Blo 1580488 1581771 := bstep (se 1 (by rfl) ⟨1186328, by rfl⟩ : syracuseStep 1581771 = 2372657) B2372657
theorem B1581783 : Blo 1580488 1581783 := bstep (se 1 (by rfl) ⟨1186337, by rfl⟩ : syracuseStep 1581783 = 2372675) B2372675
theorem B1581803 : Blo 1580488 1581803 := bstep (se 1 (by rfl) ⟨1186352, by rfl⟩ : syracuseStep 1581803 = 2372705) B2372705
theorem B1581815 : Blo 1580488 1581815 := bstep (se 1 (by rfl) ⟨1186361, by rfl⟩ : syracuseStep 1581815 = 2372723) B2372723
theorem B1581835 : Blo 1580488 1581835 := bstep (se 1 (by rfl) ⟨1186376, by rfl⟩ : syracuseStep 1581835 = 2372753) B2372753
theorem B1581847 : Blo 1580488 1581847 := bstep (se 1 (by rfl) ⟨1186385, by rfl⟩ : syracuseStep 1581847 = 2372771) B2372771
theorem B2851609 : Blo 1580488 2851609 := bstep (se 2 (by rfl) ⟨1069353, by rfl⟩ : syracuseStep 2851609 = 2138707) B2138707
theorem B1581867 : Blo 1580488 1581867 := bstep (se 1 (by rfl) ⟨1186400, by rfl⟩ : syracuseStep 1581867 = 2372801) B2372801
theorem B1581879 : Blo 1580488 1581879 := bstep (se 1 (by rfl) ⟨1186409, by rfl⟩ : syracuseStep 1581879 = 2372819) B2372819
theorem B5407553 : Blo 1580488 5407553 := bstep (se 2 (by rfl) ⟨2027832, by rfl⟩ : syracuseStep 5407553 = 4055665) B4055665
theorem B6759233 : Blo 1580488 6759233 := bstep (se 2 (by rfl) ⟨2534712, by rfl⟩ : syracuseStep 6759233 = 5069425) B5069425
theorem B1581899 : Blo 1580488 1581899 := bstep (se 1 (by rfl) ⟨1186424, by rfl⟩ : syracuseStep 1581899 = 2372849) B2372849
theorem B1581911 : Blo 1580488 1581911 := bstep (se 1 (by rfl) ⟨1186433, by rfl⟩ : syracuseStep 1581911 = 2372867) B2372867
theorem B1778539 : Blo 1580488 1778539 := bstep (se 1 (by rfl) ⟨1333904, by rfl⟩ : syracuseStep 1778539 = 2667809) B2667809
theorem B1581931 : Blo 1580488 1581931 := bstep (se 1 (by rfl) ⟨1186448, by rfl⟩ : syracuseStep 1581931 = 2372897) B2372897
theorem B1581943 : Blo 1580488 1581943 := bstep (se 1 (by rfl) ⟨1186457, by rfl⟩ : syracuseStep 1581943 = 2372915) B2372915
theorem B1581963 : Blo 1580488 1581963 := bstep (se 1 (by rfl) ⟨1186472, by rfl⟩ : syracuseStep 1581963 = 2372945) B2372945
theorem B1581975 : Blo 1580488 1581975 := bstep (se 1 (by rfl) ⟨1186481, by rfl⟩ : syracuseStep 1581975 = 2372963) B2372963
theorem B1581995 : Blo 1580488 1581995 := bstep (se 1 (by rfl) ⟨1186496, by rfl⟩ : syracuseStep 1581995 = 2372993) B2372993
theorem B1582007 : Blo 1580488 1582007 := bstep (se 1 (by rfl) ⟨1186505, by rfl⟩ : syracuseStep 1582007 = 2373011) B2373011
theorem B3802049 : Blo 1580488 3802049 := bstep (se 2 (by rfl) ⟨1425768, by rfl⟩ : syracuseStep 3802049 = 2851537) B2851537
theorem B1582027 : Blo 1580488 1582027 := bstep (se 1 (by rfl) ⟨1186520, by rfl⟩ : syracuseStep 1582027 = 2373041) B2373041
theorem B1778647 : Blo 1580488 1778647 := bstep (se 1 (by rfl) ⟨1333985, by rfl⟩ : syracuseStep 1778647 = 2667971) B2667971
theorem B1582039 : Blo 1580488 1582039 := bstep (se 1 (by rfl) ⟨1186529, by rfl⟩ : syracuseStep 1582039 = 2373059) B2373059
theorem B3556313 : Blo 1580488 3556313 := bstep (se 2 (by rfl) ⟨1333617, by rfl⟩ : syracuseStep 3556313 = 2667235) B2667235
theorem B1582059 : Blo 1580488 1582059 := bstep (se 1 (by rfl) ⟨1186544, by rfl⟩ : syracuseStep 1582059 = 2373089) B2373089
theorem B1582071 : Blo 1580488 1582071 := bstep (se 1 (by rfl) ⟨1186553, by rfl⟩ : syracuseStep 1582071 = 2373107) B2373107
theorem B1582091 : Blo 1580488 1582091 := bstep (se 1 (by rfl) ⟨1186568, by rfl⟩ : syracuseStep 1582091 = 2373137) B2373137
theorem B1582103 : Blo 1580488 1582103 := bstep (se 1 (by rfl) ⟨1186577, by rfl⟩ : syracuseStep 1582103 = 2373155) B2373155
theorem B1582123 : Blo 1580488 1582123 := bstep (se 1 (by rfl) ⟨1186592, by rfl⟩ : syracuseStep 1582123 = 2373185) B2373185
theorem B3556403 : Blo 1580488 3556403 := bstep (se 1 (by rfl) ⟨2667302, by rfl⟩ : syracuseStep 3556403 = 5334605) B5334605
theorem B1582135 : Blo 1580488 1582135 := bstep (se 1 (by rfl) ⟨1186601, by rfl⟩ : syracuseStep 1582135 = 2373203) B2373203
theorem B1582155 : Blo 1580488 1582155 := bstep (se 1 (by rfl) ⟨1186616, by rfl⟩ : syracuseStep 1582155 = 2373233) B2373233
theorem B3556439 : Blo 1580488 3556439 := bstep (se 1 (by rfl) ⟨2667329, by rfl⟩ : syracuseStep 3556439 = 5334659) B5334659
theorem B1582167 : Blo 1580488 1582167 := bstep (se 1 (by rfl) ⟨1186625, by rfl⟩ : syracuseStep 1582167 = 2373251) B2373251
theorem B11551837 : Blo 1580488 11551837 := bstep (se 3 (by rfl) ⟨2165969, by rfl⟩ : syracuseStep 11551837 = 4331939) B4331939
theorem B1582187 : Blo 1580488 1582187 := bstep (se 1 (by rfl) ⟨1186640, by rfl⟩ : syracuseStep 1582187 = 2373281) B2373281
theorem B1582199 : Blo 1580488 1582199 := bstep (se 1 (by rfl) ⟨1186649, by rfl⟩ : syracuseStep 1582199 = 2373299) B2373299
theorem B1778827 : Blo 1580488 1778827 := bstep (se 1 (by rfl) ⟨1334120, by rfl⟩ : syracuseStep 1778827 = 2668241) B2668241
theorem B1582219 : Blo 1580488 1582219 := bstep (se 1 (by rfl) ⟨1186664, by rfl⟩ : syracuseStep 1582219 = 2373329) B2373329
theorem B45581453 : Blo 1580488 45581453 := bstep (se 3 (by rfl) ⟨8546522, by rfl⟩ : syracuseStep 45581453 = 17093045) B17093045
theorem B1582231 : Blo 1580488 1582231 := bstep (se 1 (by rfl) ⟨1186673, by rfl⟩ : syracuseStep 1582231 = 2373347) B2373347
theorem B1582251 : Blo 1580488 1582251 := bstep (se 1 (by rfl) ⟨1186688, by rfl⟩ : syracuseStep 1582251 = 2373377) B2373377
theorem B1582263 : Blo 1580488 1582263 := bstep (se 1 (by rfl) ⟨1186697, by rfl⟩ : syracuseStep 1582263 = 2373395) B2373395
theorem B1582283 : Blo 1580488 1582283 := bstep (se 1 (by rfl) ⟨1186712, by rfl⟩ : syracuseStep 1582283 = 2373425) B2373425
theorem B1582295 : Blo 1580488 1582295 := bstep (se 1 (by rfl) ⟨1186721, by rfl⟩ : syracuseStep 1582295 = 2373443) B2373443
theorem B12829913 : Blo 1580488 12829913 := bstep (se 2 (by rfl) ⟨4811217, by rfl⟩ : syracuseStep 12829913 = 9622435) B9622435
theorem B1582315 : Blo 1580488 1582315 := bstep (se 1 (by rfl) ⟨1186736, by rfl⟩ : syracuseStep 1582315 = 2373473) B2373473
theorem B1778935 : Blo 1580488 1778935 := bstep (se 1 (by rfl) ⟨1334201, by rfl⟩ : syracuseStep 1778935 = 2668403) B2668403
theorem B1582327 : Blo 1580488 1582327 := bstep (se 1 (by rfl) ⟨1186745, by rfl⟩ : syracuseStep 1582327 = 2373491) B2373491
theorem B3556619 : Blo 1580488 3556619 := bstep (se 1 (by rfl) ⟨2667464, by rfl⟩ : syracuseStep 3556619 = 5334929) B5334929
theorem B1582347 : Blo 1580488 1582347 := bstep (se 1 (by rfl) ⟨1186760, by rfl⟩ : syracuseStep 1582347 = 2373521) B2373521
theorem B6415633 : Blo 1580488 6415633 := bstep (se 2 (by rfl) ⟨2405862, by rfl⟩ : syracuseStep 6415633 = 4811725) B4811725
theorem B1582359 : Blo 1580488 1582359 := bstep (se 1 (by rfl) ⟨1186769, by rfl⟩ : syracuseStep 1582359 = 2373539) B2373539
theorem B1582379 : Blo 1580488 1582379 := bstep (se 1 (by rfl) ⟨1186784, by rfl⟩ : syracuseStep 1582379 = 2373569) B2373569
theorem B1582391 : Blo 1580488 1582391 := bstep (se 1 (by rfl) ⟨1186793, by rfl⟩ : syracuseStep 1582391 = 2373587) B2373587
theorem B3556673 : Blo 1580488 3556673 := bstep (se 2 (by rfl) ⟨1333752, by rfl⟩ : syracuseStep 3556673 = 2667505) B2667505
theorem B1803595 : Blo 1580488 1803595 := bstep (se 1 (by rfl) ⟨1352696, by rfl⟩ : syracuseStep 1803595 = 2705393) B2705393
theorem B10822987 : Blo 1580488 10822987 := bstep (se 1 (by rfl) ⟨8117240, by rfl⟩ : syracuseStep 10822987 = 16234481) B16234481
theorem B1582411 : Blo 1580488 1582411 := bstep (se 1 (by rfl) ⟨1186808, by rfl⟩ : syracuseStep 1582411 = 2373617) B2373617
theorem B1582423 : Blo 1580488 1582423 := bstep (se 1 (by rfl) ⟨1186817, by rfl⟩ : syracuseStep 1582423 = 2373635) B2373635
theorem B6006109 : Blo 1580488 6006109 := bstep (se 3 (by rfl) ⟨1126145, by rfl⟩ : syracuseStep 6006109 = 2252291) B2252291
theorem B13509989 : Blo 1580488 13509989 := bstep (se 4 (by rfl) ⟨1266561, by rfl⟩ : syracuseStep 13509989 = 2533123) B2533123
theorem B1582443 : Blo 1580488 1582443 := bstep (se 1 (by rfl) ⟨1186832, by rfl⟩ : syracuseStep 1582443 = 2373665) B2373665
theorem B1582455 : Blo 1580488 1582455 := bstep (se 1 (by rfl) ⟨1186841, by rfl⟩ : syracuseStep 1582455 = 2373683) B2373683
theorem B3376523 : Blo 1580488 3376523 := bstep (se 1 (by rfl) ⟨2532392, by rfl⟩ : syracuseStep 3376523 = 5064785) B5064785
theorem B1582475 : Blo 1580488 1582475 := bstep (se 1 (by rfl) ⟨1186856, by rfl⟩ : syracuseStep 1582475 = 2373713) B2373713
theorem B1582487 : Blo 1580488 1582487 := bstep (se 1 (by rfl) ⟨1186865, by rfl⟩ : syracuseStep 1582487 = 2373731) B2373731
theorem B1779115 : Blo 1580488 1779115 := bstep (se 1 (by rfl) ⟨1334336, by rfl⟩ : syracuseStep 1779115 = 2668673) B2668673
theorem B5334551 : Blo 1580488 5334551 := bstep (se 1 (by rfl) ⟨4000913, by rfl⟩ : syracuseStep 5334551 = 8001827) B8001827
theorem B1779223 : Blo 1580488 1779223 := bstep (se 1 (by rfl) ⟨1334417, by rfl⟩ : syracuseStep 1779223 = 2668835) B2668835
theorem B3556889 : Blo 1580488 3556889 := bstep (se 2 (by rfl) ⟨1333833, by rfl⟩ : syracuseStep 3556889 = 2667667) B2667667
theorem B8119853 : Blo 1580488 8119853 := bstep (se 3 (by rfl) ⟨1522472, by rfl⟩ : syracuseStep 8119853 = 3044945) B3044945
theorem B3556979 : Blo 1580488 3556979 := bstep (se 1 (by rfl) ⟨2667734, by rfl⟩ : syracuseStep 3556979 = 5335469) B5335469
theorem B3606167 : Blo 1580488 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B3557015 : Blo 1580488 3557015 := bstep (se 1 (by rfl) ⟨2667761, by rfl⟩ : syracuseStep 3557015 = 5335523) B5335523
theorem B6751937 : Blo 1580488 6751937 := bstep (se 2 (by rfl) ⟨2531976, by rfl⟩ : syracuseStep 6751937 = 5063953) B5063953
theorem B1779403 : Blo 1580488 1779403 := bstep (se 1 (by rfl) ⟨1334552, by rfl⟩ : syracuseStep 1779403 = 2669105) B2669105
theorem B18007757 : Blo 1580488 18007757 := bstep (se 3 (by rfl) ⟨3376454, by rfl⟩ : syracuseStep 18007757 = 6752909) B6752909
theorem B3376883 : Blo 1580488 3376883 := bstep (se 1 (by rfl) ⟨2532662, by rfl⟩ : syracuseStep 3376883 = 5065325) B5065325
theorem B1689355 : Blo 1580488 1689355 := bstep (se 1 (by rfl) ⟨1267016, by rfl⟩ : syracuseStep 1689355 = 2534033) B2534033
theorem B1779511 : Blo 1580488 1779511 := bstep (se 1 (by rfl) ⟨1334633, by rfl⟩ : syracuseStep 1779511 = 2669267) B2669267
theorem B25642817 : Blo 1580488 25642817 := bstep (se 2 (by rfl) ⟨9616056, by rfl⟩ : syracuseStep 25642817 = 19232113) B19232113
theorem B3557195 : Blo 1580488 3557195 := bstep (se 1 (by rfl) ⟨2667896, by rfl⟩ : syracuseStep 3557195 = 5335793) B5335793
theorem B2533207 : Blo 1580488 2533207 := bstep (se 1 (by rfl) ⟨1899905, by rfl⟩ : syracuseStep 2533207 = 3799811) B3799811
theorem B6752089 : Blo 1580488 6752089 := bstep (se 2 (by rfl) ⟨2532033, by rfl⟩ : syracuseStep 6752089 = 5064067) B5064067
theorem B3557249 : Blo 1580488 3557249 := bstep (se 2 (by rfl) ⟨1333968, by rfl⟩ : syracuseStep 3557249 = 2667937) B2667937
theorem B2000791 : Blo 1580488 2000791 := bstep (se 1 (by rfl) ⟨1500593, by rfl⟩ : syracuseStep 2000791 = 3001187) B3001187
theorem B3606487 : Blo 1580488 3606487 := bstep (se 1 (by rfl) ⟨2704865, by rfl⟩ : syracuseStep 3606487 = 5409731) B5409731
theorem B1779691 : Blo 1580488 1779691 := bstep (se 1 (by rfl) ⟨1334768, by rfl⟩ : syracuseStep 1779691 = 2669537) B2669537
theorem B11397125 : Blo 1580488 11397125 := bstep (se 4 (by rfl) ⟨1068480, by rfl⟩ : syracuseStep 11397125 = 2136961) B2136961
theorem B5335091 : Blo 1580488 5335091 := bstep (se 1 (by rfl) ⟨4001318, by rfl⟩ : syracuseStep 5335091 = 8002637) B8002637
theorem B12167243 : Blo 1580488 12167243 := bstep (se 1 (by rfl) ⟨9125432, by rfl⟩ : syracuseStep 12167243 = 18250865) B18250865
theorem B1779799 : Blo 1580488 1779799 := bstep (se 1 (by rfl) ⟨1334849, by rfl⟩ : syracuseStep 1779799 = 2669699) B2669699
theorem B3557465 : Blo 1580488 3557465 := bstep (se 2 (by rfl) ⟨1334049, by rfl⟩ : syracuseStep 3557465 = 2668099) B2668099
theorem B3000473 : Blo 1580488 3000473 := bstep (se 2 (by rfl) ⟨1125177, by rfl⟩ : syracuseStep 3000473 = 2250355) B2250355
theorem B3557555 : Blo 1580488 3557555 := bstep (se 1 (by rfl) ⟨2668166, by rfl⟩ : syracuseStep 3557555 = 5336333) B5336333
theorem B3557591 : Blo 1580488 3557591 := bstep (se 1 (by rfl) ⟨2668193, by rfl⟩ : syracuseStep 3557591 = 5336387) B5336387
theorem B1779979 : Blo 1580488 1779979 := bstep (se 1 (by rfl) ⟨1334984, by rfl⟩ : syracuseStep 1779979 = 2669969) B2669969
theorem B4114739 : Blo 1580488 4114739 := bstep (se 1 (by rfl) ⟨3086054, by rfl⟩ : syracuseStep 4114739 = 6172109) B6172109
theorem B5335361 : Blo 1580488 5335361 := bstep (se 2 (by rfl) ⟨2000760, by rfl⟩ : syracuseStep 5335361 = 4001521) B4001521
theorem B5409089 : Blo 1580488 5409089 := bstep (se 2 (by rfl) ⟨2028408, by rfl⟩ : syracuseStep 5409089 = 4056817) B4056817
theorem B1780087 : Blo 1580488 1780087 := bstep (se 1 (by rfl) ⟨1335065, by rfl⟩ : syracuseStep 1780087 = 2670131) B2670131
theorem B3557771 : Blo 1580488 3557771 := bstep (se 1 (by rfl) ⟨2668328, by rfl⟩ : syracuseStep 3557771 = 5336657) B5336657
theorem B2533771 : Blo 1580488 2533771 := bstep (se 1 (by rfl) ⟨1900328, by rfl⟩ : syracuseStep 2533771 = 3800657) B3800657
theorem B8006039 : Blo 1580488 8006039 := bstep (se 1 (by rfl) ⟨6004529, by rfl⟩ : syracuseStep 8006039 = 12009059) B12009059
theorem B3557825 : Blo 1580488 3557825 := bstep (se 2 (by rfl) ⟨1334184, by rfl⟩ : syracuseStep 3557825 = 2668369) B2668369
theorem B1780267 : Blo 1580488 1780267 := bstep (se 1 (by rfl) ⟨1335200, by rfl⟩ : syracuseStep 1780267 = 2670401) B2670401
theorem B3000883 : Blo 1580488 3000883 := bstep (se 1 (by rfl) ⟨2250662, by rfl⟩ : syracuseStep 3000883 = 4501325) B4501325
theorem B6007385 : Blo 1580488 6007385 := bstep (se 2 (by rfl) ⟨2252769, by rfl⟩ : syracuseStep 6007385 = 4505539) B4505539
theorem B3558041 : Blo 1580488 3558041 := bstep (se 2 (by rfl) ⟨1334265, by rfl⟩ : syracuseStep 3558041 = 2668531) B2668531
theorem B2001611 : Blo 1580488 2001611 := bstep (se 1 (by rfl) ⟨1501208, by rfl⟩ : syracuseStep 2001611 = 3002417) B3002417
theorem B3558131 : Blo 1580488 3558131 := bstep (se 1 (by rfl) ⟨2668598, by rfl⟩ : syracuseStep 3558131 = 5337197) B5337197
theorem B3558167 : Blo 1580488 3558167 := bstep (se 1 (by rfl) ⟨2668625, by rfl⟩ : syracuseStep 3558167 = 5337251) B5337251
theorem B5335901 : Blo 1580488 5335901 := bstep (se 3 (by rfl) ⟨1000481, by rfl⟩ : syracuseStep 5335901 = 2000963) B2000963
theorem B9005975 : Blo 1580488 9005975 := bstep (se 1 (by rfl) ⟨6754481, by rfl⟩ : syracuseStep 9005975 = 13508963) B13508963
theorem B4000691 : Blo 1580488 4000691 := bstep (se 1 (by rfl) ⟨3000518, by rfl⟩ : syracuseStep 4000691 = 6001037) B6001037
theorem B3558347 : Blo 1580488 3558347 := bstep (se 1 (by rfl) ⟨2668760, by rfl⟩ : syracuseStep 3558347 = 5337521) B5337521
theorem B12331993 : Blo 1580488 12331993 := bstep (se 2 (by rfl) ⟨4624497, by rfl⟩ : syracuseStep 12331993 = 9248995) B9248995
theorem B3558401 : Blo 1580488 3558401 := bstep (se 2 (by rfl) ⟨1334400, by rfl⟩ : syracuseStep 3558401 = 2668801) B2668801
theorem B3001369 : Blo 1580488 3001369 := bstep (se 2 (by rfl) ⟨1125513, by rfl⟩ : syracuseStep 3001369 = 2251027) B2251027
theorem B4000985 : Blo 1580488 4000985 := bstep (se 2 (by rfl) ⟨1500369, by rfl⟩ : syracuseStep 4000985 = 3000739) B3000739
theorem B3558617 : Blo 1580488 3558617 := bstep (se 2 (by rfl) ⟨1334481, by rfl⟩ : syracuseStep 3558617 = 2668963) B2668963
theorem B2370827 : Blo 1580488 2370827 := bstep (se 1 (by rfl) ⟨1778120, by rfl⟩ : syracuseStep 2370827 = 3556241) B3556241
theorem B2370839 : Blo 1580488 2370839 := bstep (se 1 (by rfl) ⟨1778129, by rfl⟩ : syracuseStep 2370839 = 3556259) B3556259
theorem B3558707 : Blo 1580488 3558707 := bstep (se 1 (by rfl) ⟨2669030, by rfl⟩ : syracuseStep 3558707 = 5338061) B5338061
theorem B3558743 : Blo 1580488 3558743 := bstep (se 1 (by rfl) ⟨2669057, by rfl⟩ : syracuseStep 3558743 = 5338115) B5338115
theorem B2370905 : Blo 1580488 2370905 := bstep (se 2 (by rfl) ⟨889089, by rfl⟩ : syracuseStep 2370905 = 1778179) B1778179
theorem B2002315 : Blo 1580488 2002315 := bstep (se 1 (by rfl) ⟨1501736, by rfl⟩ : syracuseStep 2002315 = 3003473) B3003473
theorem B2371019 : Blo 1580488 2371019 := bstep (se 1 (by rfl) ⟨1778264, by rfl⟩ : syracuseStep 2371019 = 3556529) B3556529
theorem B2371031 : Blo 1580488 2371031 := bstep (se 1 (by rfl) ⟨1778273, by rfl⟩ : syracuseStep 2371031 = 3556547) B3556547
theorem B3558923 : Blo 1580488 3558923 := bstep (se 1 (by rfl) ⟨2669192, by rfl⟩ : syracuseStep 3558923 = 5338385) B5338385
theorem B2371097 : Blo 1580488 2371097 := bstep (se 2 (by rfl) ⟨889161, by rfl⟩ : syracuseStep 2371097 = 1778323) B1778323
theorem B3558977 : Blo 1580488 3558977 := bstep (se 2 (by rfl) ⟨1334616, by rfl⟩ : syracuseStep 3558977 = 2669233) B2669233
theorem B3001931 : Blo 1580488 3001931 := bstep (se 1 (by rfl) ⟨2251448, by rfl⟩ : syracuseStep 3001931 = 4502897) B4502897
theorem B2371211 : Blo 1580488 2371211 := bstep (se 1 (by rfl) ⟨1778408, by rfl⟩ : syracuseStep 2371211 = 3556817) B3556817
theorem B2371223 : Blo 1580488 2371223 := bstep (se 1 (by rfl) ⟨1778417, by rfl⟩ : syracuseStep 2371223 = 3556835) B3556835
theorem B2002583 : Blo 1580488 2002583 := bstep (se 1 (by rfl) ⟨1501937, by rfl⟩ : syracuseStep 2002583 = 3003875) B3003875
theorem B3378881 : Blo 1580488 3378881 := bstep (se 2 (by rfl) ⟨1267080, by rfl⟩ : syracuseStep 3378881 = 2534161) B2534161
theorem B2371289 : Blo 1580488 2371289 := bstep (se 2 (by rfl) ⟨889233, by rfl⟩ : syracuseStep 2371289 = 1778467) B1778467
theorem B3002113 : Blo 1580488 3002113 := bstep (se 2 (by rfl) ⟨1125792, by rfl⟩ : syracuseStep 3002113 = 2251585) B2251585
theorem B10817297 : Blo 1580488 10817297 := bstep (se 2 (by rfl) ⟨4056486, by rfl⟩ : syracuseStep 10817297 = 8112973) B8112973
theorem B3559193 : Blo 1580488 3559193 := bstep (se 2 (by rfl) ⟨1334697, by rfl⟩ : syracuseStep 3559193 = 2669395) B2669395
theorem B15200045 : Blo 1580488 15200045 := bstep (se 3 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 15200045 = 5700017) B5700017
theorem B2371403 : Blo 1580488 2371403 := bstep (se 1 (by rfl) ⟨1778552, by rfl⟩ : syracuseStep 2371403 = 3557105) B3557105
theorem B2371415 : Blo 1580488 2371415 := bstep (se 1 (by rfl) ⟨1778561, by rfl⟩ : syracuseStep 2371415 = 3557123) B3557123
theorem B3559283 : Blo 1580488 3559283 := bstep (se 1 (by rfl) ⟨2669462, by rfl⟩ : syracuseStep 3559283 = 5338925) B5338925
theorem B3608459 : Blo 1580488 3608459 := bstep (se 1 (by rfl) ⟨2706344, by rfl⟩ : syracuseStep 3608459 = 5412689) B5412689
theorem B3559319 : Blo 1580488 3559319 := bstep (se 1 (by rfl) ⟨2669489, by rfl⟩ : syracuseStep 3559319 = 5338979) B5338979
theorem B2371481 : Blo 1580488 2371481 := bstep (se 2 (by rfl) ⟨889305, by rfl⟩ : syracuseStep 2371481 = 1778611) B1778611
theorem B5337035 : Blo 1580488 5337035 := bstep (se 1 (by rfl) ⟨4002776, by rfl⟩ : syracuseStep 5337035 = 8005553) B8005553
theorem B13512653 : Blo 1580488 13512653 := bstep (se 3 (by rfl) ⟨2533622, by rfl⟩ : syracuseStep 13512653 = 5067245) B5067245
theorem B5697539 : Blo 1580488 5697539 := bstep (se 1 (by rfl) ⟨4273154, by rfl⟩ : syracuseStep 5697539 = 8546309) B8546309
theorem B2371595 : Blo 1580488 2371595 := bstep (se 1 (by rfl) ⟨1778696, by rfl⟩ : syracuseStep 2371595 = 3557393) B3557393
theorem B2371607 : Blo 1580488 2371607 := bstep (se 1 (by rfl) ⟨1778705, by rfl⟩ : syracuseStep 2371607 = 3557411) B3557411
theorem B3084311 : Blo 1580488 3084311 := bstep (se 1 (by rfl) ⟨2313233, by rfl⟩ : syracuseStep 3084311 = 4626467) B4626467
theorem B7213121 : Blo 1580488 7213121 := bstep (se 2 (by rfl) ⟨2704920, by rfl⟩ : syracuseStep 7213121 = 5409841) B5409841
theorem B4272203 : Blo 1580488 4272203 := bstep (se 1 (by rfl) ⟨3204152, by rfl⟩ : syracuseStep 4272203 = 6408305) B6408305
theorem B3559499 : Blo 1580488 3559499 := bstep (se 1 (by rfl) ⟨2669624, by rfl⟩ : syracuseStep 3559499 = 5339249) B5339249
theorem B2371673 : Blo 1580488 2371673 := bstep (se 2 (by rfl) ⟨889377, by rfl⟩ : syracuseStep 2371673 = 1778755) B1778755
theorem B3559553 : Blo 1580488 3559553 := bstep (se 2 (by rfl) ⟨1334832, by rfl⟩ : syracuseStep 3559553 = 2669665) B2669665
theorem B2371787 : Blo 1580488 2371787 := bstep (se 1 (by rfl) ⟨1778840, by rfl⟩ : syracuseStep 2371787 = 3557681) B3557681
theorem B2371799 : Blo 1580488 2371799 := bstep (se 1 (by rfl) ⟨1778849, by rfl⟩ : syracuseStep 2371799 = 3557699) B3557699
theorem B5337305 : Blo 1580488 5337305 := bstep (se 2 (by rfl) ⟨2001489, by rfl⟩ : syracuseStep 5337305 = 4002979) B4002979
theorem B2371865 : Blo 1580488 2371865 := bstep (se 2 (by rfl) ⟨889449, by rfl⟩ : syracuseStep 2371865 = 1778899) B1778899
theorem B3559769 : Blo 1580488 3559769 := bstep (se 2 (by rfl) ⟨1334913, by rfl⟩ : syracuseStep 3559769 = 2669827) B2669827
theorem B2371979 : Blo 1580488 2371979 := bstep (se 1 (by rfl) ⟨1778984, by rfl⟩ : syracuseStep 2371979 = 3557969) B3557969
theorem B2371991 : Blo 1580488 2371991 := bstep (se 1 (by rfl) ⟨1778993, by rfl⟩ : syracuseStep 2371991 = 3557987) B3557987
theorem B3559859 : Blo 1580488 3559859 := bstep (se 1 (by rfl) ⟨2669894, by rfl⟩ : syracuseStep 3559859 = 5339789) B5339789
theorem B3002827 : Blo 1580488 3002827 := bstep (se 1 (by rfl) ⟨2252120, by rfl⟩ : syracuseStep 3002827 = 4504241) B4504241
theorem B3559895 : Blo 1580488 3559895 := bstep (se 1 (by rfl) ⟨2669921, by rfl⟩ : syracuseStep 3559895 = 5339843) B5339843
theorem B2372057 : Blo 1580488 2372057 := bstep (se 2 (by rfl) ⟨889521, by rfl⟩ : syracuseStep 2372057 = 1779043) B1779043
theorem B3002903 : Blo 1580488 3002903 := bstep (se 1 (by rfl) ⟨2252177, by rfl⟩ : syracuseStep 3002903 = 4504355) B4504355
theorem B3379735 : Blo 1580488 3379735 := bstep (se 1 (by rfl) ⟨2534801, by rfl⟩ : syracuseStep 3379735 = 5069603) B5069603
theorem B21926435 : Blo 1580488 21926435 := bstep (se 1 (by rfl) ⟨16444826, by rfl⟩ : syracuseStep 21926435 = 32889653) B32889653
theorem B2372171 : Blo 1580488 2372171 := bstep (se 1 (by rfl) ⟨1779128, by rfl⟩ : syracuseStep 2372171 = 3558257) B3558257
theorem B2372183 : Blo 1580488 2372183 := bstep (se 1 (by rfl) ⟨1779137, by rfl⟩ : syracuseStep 2372183 = 3558275) B3558275
theorem B3560075 : Blo 1580488 3560075 := bstep (se 1 (by rfl) ⟨2670056, by rfl⟩ : syracuseStep 3560075 = 5340113) B5340113
theorem B2667161 : Blo 1580488 2667161 := bstep (se 2 (by rfl) ⟨1000185, by rfl⟩ : syracuseStep 2667161 = 2000371) B2000371
theorem B2372249 : Blo 1580488 2372249 := bstep (se 2 (by rfl) ⟨889593, by rfl⟩ : syracuseStep 2372249 = 1779187) B1779187
theorem B3560129 : Blo 1580488 3560129 := bstep (se 2 (by rfl) ⟨1335048, by rfl⟩ : syracuseStep 3560129 = 2670097) B2670097
theorem B2372363 : Blo 1580488 2372363 := bstep (se 1 (by rfl) ⟨1779272, by rfl⟩ : syracuseStep 2372363 = 3558545) B3558545
theorem B10138385 : Blo 1580488 10138385 := bstep (se 2 (by rfl) ⟨3801894, by rfl⟩ : syracuseStep 10138385 = 7603789) B7603789
theorem B2372375 : Blo 1580488 2372375 := bstep (se 1 (by rfl) ⟨1779281, by rfl⟩ : syracuseStep 2372375 = 3558563) B3558563
theorem B2667289 : Blo 1580488 2667289 := bstep (se 2 (by rfl) ⟨1000233, by rfl⟩ : syracuseStep 2667289 = 2000467) B2000467
theorem B24343361 : Blo 1580488 24343361 := bstep (se 2 (by rfl) ⟨9128760, by rfl⟩ : syracuseStep 24343361 = 18257521) B18257521
theorem B4002635 : Blo 1580488 4002635 := bstep (se 1 (by rfl) ⟨3001976, by rfl⟩ : syracuseStep 4002635 = 6003953) B6003953
theorem B2405207 : Blo 1580488 2405207 := bstep (se 1 (by rfl) ⟨1803905, by rfl⟩ : syracuseStep 2405207 = 3607811) B3607811
theorem B2372441 : Blo 1580488 2372441 := bstep (se 2 (by rfl) ⟨889665, by rfl⟩ : syracuseStep 2372441 = 1779331) B1779331
theorem B6001553 : Blo 1580488 6001553 := bstep (se 2 (by rfl) ⟨2250582, by rfl⟩ : syracuseStep 6001553 = 4501165) B4501165
theorem B5338007 : Blo 1580488 5338007 := bstep (se 1 (by rfl) ⟨4003505, by rfl⟩ : syracuseStep 5338007 = 8007011) B8007011
theorem B3560345 : Blo 1580488 3560345 := bstep (se 2 (by rfl) ⟨1335129, by rfl⟩ : syracuseStep 3560345 = 2670259) B2670259
theorem B2372555 : Blo 1580488 2372555 := bstep (se 1 (by rfl) ⟨1779416, by rfl⟩ : syracuseStep 2372555 = 3558833) B3558833
theorem B2372567 : Blo 1580488 2372567 := bstep (se 1 (by rfl) ⟨1779425, by rfl⟩ : syracuseStep 2372567 = 3558851) B3558851
theorem B3560435 : Blo 1580488 3560435 := bstep (se 1 (by rfl) ⟨2670326, by rfl⟩ : syracuseStep 3560435 = 5340653) B5340653
theorem B19493905 : Blo 1580488 19493905 := bstep (se 2 (by rfl) ⟨7310214, by rfl⟩ : syracuseStep 19493905 = 14620429) B14620429
theorem B3560471 : Blo 1580488 3560471 := bstep (se 1 (by rfl) ⟨2670353, by rfl⟩ : syracuseStep 3560471 = 5340707) B5340707
theorem B2372633 : Blo 1580488 2372633 := bstep (se 2 (by rfl) ⟨889737, by rfl⟩ : syracuseStep 2372633 = 1779475) B1779475
theorem B18019421 : Blo 1580488 18019421 := bstep (se 3 (by rfl) ⟨3378641, by rfl⟩ : syracuseStep 18019421 = 6757283) B6757283
theorem B5698691 : Blo 1580488 5698691 := bstep (se 1 (by rfl) ⟨4274018, by rfl⟩ : syracuseStep 5698691 = 8548037) B8548037
theorem B2372747 : Blo 1580488 2372747 := bstep (se 1 (by rfl) ⟨1779560, by rfl⟩ : syracuseStep 2372747 = 3559121) B3559121
theorem B32453783 : Blo 1580488 32453783 := bstep (se 1 (by rfl) ⟨24340337, by rfl⟩ : syracuseStep 32453783 = 48680675) B48680675
theorem B19240087 : Blo 1580488 19240087 := bstep (se 1 (by rfl) ⟨14430065, by rfl⟩ : syracuseStep 19240087 = 28860131) B28860131
theorem B2372759 : Blo 1580488 2372759 := bstep (se 1 (by rfl) ⟨1779569, by rfl⟩ : syracuseStep 2372759 = 3559139) B3559139
theorem B6755507 : Blo 1580488 6755507 := bstep (se 1 (by rfl) ⟨5066630, by rfl⟩ : syracuseStep 6755507 = 10133261) B10133261
theorem B3003571 : Blo 1580488 3003571 := bstep (se 1 (by rfl) ⟨2252678, by rfl⟩ : syracuseStep 3003571 = 4505357) B4505357
theorem B2372825 : Blo 1580488 2372825 := bstep (se 2 (by rfl) ⟨889809, by rfl⟩ : syracuseStep 2372825 = 1779619) B1779619
theorem B4502749 : Blo 1580488 4502749 := bstep (se 3 (by rfl) ⟨844265, by rfl⟩ : syracuseStep 4502749 = 1688531) B1688531
theorem B2372939 : Blo 1580488 2372939 := bstep (se 1 (by rfl) ⟨1779704, by rfl⟩ : syracuseStep 2372939 = 3559409) B3559409
theorem B2667863 : Blo 1580488 2667863 := bstep (se 1 (by rfl) ⟨2000897, by rfl⟩ : syracuseStep 2667863 = 4001795) B4001795
theorem B6002009 : Blo 1580488 6002009 := bstep (se 2 (by rfl) ⟨2250753, by rfl⟩ : syracuseStep 6002009 = 4501507) B4501507
theorem B2372951 : Blo 1580488 2372951 := bstep (se 1 (by rfl) ⟨1779713, by rfl⟩ : syracuseStep 2372951 = 3559427) B3559427
theorem B3003799 : Blo 1580488 3003799 := bstep (se 1 (by rfl) ⟨2252849, by rfl⟩ : syracuseStep 3003799 = 4505699) B4505699
theorem B2373017 : Blo 1580488 2373017 := bstep (se 2 (by rfl) ⟨889881, by rfl⟩ : syracuseStep 2373017 = 1779763) B1779763
theorem B28865969 : Blo 1580488 28865969 := bstep (se 2 (by rfl) ⟨10824738, by rfl⟩ : syracuseStep 28865969 = 21649477) B21649477
theorem B9614771 : Blo 1580488 9614771 := bstep (se 1 (by rfl) ⟨7211078, by rfl⟩ : syracuseStep 9614771 = 14422157) B14422157
theorem B5338547 : Blo 1580488 5338547 := bstep (se 1 (by rfl) ⟨4003910, by rfl⟩ : syracuseStep 5338547 = 8007821) B8007821
theorem B2667991 : Blo 1580488 2667991 := bstep (se 1 (by rfl) ⟨2000993, by rfl⟩ : syracuseStep 2667991 = 4001987) B4001987
theorem B3003905 : Blo 1580488 3003905 := bstep (se 2 (by rfl) ⟨1126464, by rfl⟩ : syracuseStep 3003905 = 2252929) B2252929
theorem B2373131 : Blo 1580488 2373131 := bstep (se 1 (by rfl) ⟨1779848, by rfl⟩ : syracuseStep 2373131 = 3559697) B3559697
theorem B2848279 : Blo 1580488 2848279 := bstep (se 1 (by rfl) ⟨2136209, by rfl⟩ : syracuseStep 2848279 = 4272419) B4272419
theorem B2373143 : Blo 1580488 2373143 := bstep (se 1 (by rfl) ⟨1779857, by rfl⟩ : syracuseStep 2373143 = 3559715) B3559715
theorem B6002221 : Blo 1580488 6002221 := bstep (se 3 (by rfl) ⟨1125416, by rfl⟩ : syracuseStep 6002221 = 2250833) B2250833
theorem B2373209 : Blo 1580488 2373209 := bstep (se 2 (by rfl) ⟨889953, by rfl⟩ : syracuseStep 2373209 = 1779907) B1779907
theorem B12826205 : Blo 1580488 12826205 := bstep (se 3 (by rfl) ⟨2404913, by rfl⟩ : syracuseStep 12826205 = 4809827) B4809827
theorem B3004057 : Blo 1580488 3004057 := bstep (se 2 (by rfl) ⟨1126521, by rfl⟩ : syracuseStep 3004057 = 2253043) B2253043
theorem B5338817 : Blo 1580488 5338817 := bstep (se 2 (by rfl) ⟨2002056, by rfl⟩ : syracuseStep 5338817 = 4004113) B4004113
theorem B2373323 : Blo 1580488 2373323 := bstep (se 1 (by rfl) ⟨1779992, by rfl⟩ : syracuseStep 2373323 = 3559985) B3559985
theorem B2373335 : Blo 1580488 2373335 := bstep (se 1 (by rfl) ⟨1780001, by rfl⟩ : syracuseStep 2373335 = 3560003) B3560003
theorem B12015377 : Blo 1580488 12015377 := bstep (se 2 (by rfl) ⟨4505766, by rfl⟩ : syracuseStep 12015377 = 9011533) B9011533
theorem B4003607 : Blo 1580488 4003607 := bstep (se 1 (by rfl) ⟨3002705, by rfl⟩ : syracuseStep 4003607 = 6005411) B6005411
theorem B2373401 : Blo 1580488 2373401 := bstep (se 2 (by rfl) ⟨890025, by rfl⟩ : syracuseStep 2373401 = 1780051) B1780051
theorem B4331357 : Blo 1580488 4331357 := bstep (se 3 (by rfl) ⟨812129, by rfl⟩ : syracuseStep 4331357 = 1624259) B1624259
theorem B6002525 : Blo 1580488 6002525 := bstep (se 3 (by rfl) ⟨1125473, by rfl⟩ : syracuseStep 6002525 = 2250947) B2250947
theorem B13006693 : Blo 1580488 13006693 := bstep (se 4 (by rfl) ⟨1219377, by rfl⟩ : syracuseStep 13006693 = 2438755) B2438755
theorem B14423939 : Blo 1580488 14423939 := bstep (se 1 (by rfl) ⟨10817954, by rfl⟩ : syracuseStep 14423939 = 21635909) B21635909
theorem B8009603 : Blo 1580488 8009603 := bstep (se 1 (by rfl) ⟨6007202, by rfl⟩ : syracuseStep 8009603 = 12014405) B12014405
theorem B2373515 : Blo 1580488 2373515 := bstep (se 1 (by rfl) ⟨1780136, by rfl⟩ : syracuseStep 2373515 = 3560273) B3560273
theorem B2373527 : Blo 1580488 2373527 := bstep (se 1 (by rfl) ⟨1780145, by rfl⟩ : syracuseStep 2373527 = 3560291) B3560291
theorem B1603511 : Blo 1580488 1603511 := bstep (se 1 (by rfl) ⟨1202633, by rfl⟩ : syracuseStep 1603511 = 2405267) B2405267
theorem B11392973 : Blo 1580488 11392973 := bstep (se 3 (by rfl) ⟨2136182, by rfl⟩ : syracuseStep 11392973 = 4272365) B4272365
theorem B2373593 : Blo 1580488 2373593 := bstep (se 2 (by rfl) ⟨890097, by rfl⟩ : syracuseStep 2373593 = 1780195) B1780195
theorem B2668619 : Blo 1580488 2668619 := bstep (se 1 (by rfl) ⟨2001464, by rfl⟩ : syracuseStep 2668619 = 4002929) B4002929
theorem B2373707 : Blo 1580488 2373707 := bstep (se 1 (by rfl) ⟨1780280, by rfl⟩ : syracuseStep 2373707 = 3560561) B3560561
theorem B2373719 : Blo 1580488 2373719 := bstep (se 1 (by rfl) ⟨1780289, by rfl⟩ : syracuseStep 2373719 = 3560579) B3560579
theorem B5699729 : Blo 1580488 5699729 := bstep (se 2 (by rfl) ⟨2137398, by rfl⟩ : syracuseStep 5699729 = 4274797) B4274797
theorem B44480663 : Blo 1580488 44480663 := bstep (se 1 (by rfl) ⟨33360497, by rfl⟩ : syracuseStep 44480663 = 66720995) B66720995
theorem B12007601 : Blo 1580488 12007601 := bstep (se 2 (by rfl) ⟨4502850, by rfl⟩ : syracuseStep 12007601 = 9005701) B9005701
theorem B28850357 : Blo 1580488 28850357 := bstep (se 5 (by rfl) ⟨1352360, by rfl⟩ : syracuseStep 28850357 = 2704721) B2704721
theorem B2668747 : Blo 1580488 2668747 := bstep (se 1 (by rfl) ⟨2001560, by rfl⟩ : syracuseStep 2668747 = 4003121) B4003121
theorem B5339357 : Blo 1580488 5339357 := bstep (se 3 (by rfl) ⟨1001129, by rfl⟩ : syracuseStep 5339357 = 2002259) B2002259
theorem B2668889 : Blo 1580488 2668889 := bstep (se 2 (by rfl) ⟨1000833, by rfl⟩ : syracuseStep 2668889 = 2001667) B2001667
theorem B39000437 : Blo 1580488 39000437 := bstep (se 5 (by rfl) ⟨1828145, by rfl⟩ : syracuseStep 39000437 = 3656291) B3656291
theorem B2251147 : Blo 1580488 2251147 := bstep (se 1 (by rfl) ⟨1688360, by rfl⟩ : syracuseStep 2251147 = 3376721) B3376721
theorem B4004275 : Blo 1580488 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B2669017 : Blo 1580488 2669017 := bstep (se 2 (by rfl) ⟨1000881, by rfl⟩ : syracuseStep 2669017 = 2001763) B2001763
theorem B4504025 : Blo 1580488 4504025 := bstep (se 2 (by rfl) ⟨1689009, by rfl⟩ : syracuseStep 4504025 = 3378019) B3378019
theorem B2849303 : Blo 1580488 2849303 := bstep (se 1 (by rfl) ⟨2136977, by rfl⟩ : syracuseStep 2849303 = 4273955) B4273955
theorem B9124417 : Blo 1580488 9124417 := bstep (se 2 (by rfl) ⟨3421656, by rfl⟩ : syracuseStep 9124417 = 6843313) B6843313
theorem B4004417 : Blo 1580488 4004417 := bstep (se 2 (by rfl) ⟨1501656, by rfl⟩ : syracuseStep 4004417 = 3003313) B3003313
theorem B1899083 : Blo 1580488 1899083 := bstep (se 1 (by rfl) ⟨1424312, by rfl⟩ : syracuseStep 1899083 = 2848625) B2848625
theorem B12008087 : Blo 1580488 12008087 := bstep (se 1 (by rfl) ⟨9006065, by rfl⟩ : syracuseStep 12008087 = 18012131) B18012131
theorem B11401879 : Blo 1580488 11401879 := bstep (se 1 (by rfl) ⟨8551409, by rfl⟩ : syracuseStep 11401879 = 17102819) B17102819
theorem B10132289 : Blo 1580488 10132289 := bstep (se 2 (by rfl) ⟨3799608, by rfl⟩ : syracuseStep 10132289 = 7599217) B7599217
theorem B2669591 : Blo 1580488 2669591 := bstep (se 1 (by rfl) ⟨2002193, by rfl⟩ : syracuseStep 2669591 = 4004387) B4004387
theorem B2669719 : Blo 1580488 2669719 := bstep (se 1 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 2669719 = 4004579) B4004579
theorem B2849995 : Blo 1580488 2849995 := bstep (se 1 (by rfl) ⟨2137496, by rfl⟩ : syracuseStep 2849995 = 4274993) B4274993
theorem B4275479 : Blo 1580488 4275479 := bstep (se 1 (by rfl) ⟨3206609, by rfl⟩ : syracuseStep 4275479 = 6413219) B6413219
theorem B9002285 : Blo 1580488 9002285 := bstep (se 3 (by rfl) ⟨1687928, by rfl⟩ : syracuseStep 9002285 = 3375857) B3375857
theorem B5340491 : Blo 1580488 5340491 := bstep (se 1 (by rfl) ⟨4005368, by rfl⟩ : syracuseStep 5340491 = 8010737) B8010737
theorem B1580491 : Blo 1580488 1580491 := bstep (se 1 (by rfl) ⟨1185368, by rfl⟩ : syracuseStep 1580491 = 2370737) B2370737
theorem B1580503 : Blo 1580488 1580503 := bstep (se 1 (by rfl) ⟨1185377, by rfl⟩ : syracuseStep 1580503 = 2370755) B2370755
theorem B1580523 : Blo 1580488 1580523 := bstep (se 1 (by rfl) ⟨1185392, by rfl⟩ : syracuseStep 1580523 = 2370785) B2370785
theorem B1580535 : Blo 1580488 1580535 := bstep (se 1 (by rfl) ⟨1185401, by rfl⟩ : syracuseStep 1580535 = 2370803) B2370803
theorem B1580555 : Blo 1580488 1580555 := bstep (se 1 (by rfl) ⟨1185416, by rfl⟩ : syracuseStep 1580555 = 2370833) B2370833
theorem B1580567 : Blo 1580488 1580567 := bstep (se 1 (by rfl) ⟨1185425, by rfl⟩ : syracuseStep 1580567 = 2370851) B2370851
theorem B1580587 : Blo 1580488 1580587 := bstep (se 1 (by rfl) ⟨1185440, by rfl⟩ : syracuseStep 1580587 = 2370881) B2370881
theorem B1580599 : Blo 1580488 1580599 := bstep (se 1 (by rfl) ⟨1185449, by rfl⟩ : syracuseStep 1580599 = 2370899) B2370899
theorem B1580619 : Blo 1580488 1580619 := bstep (se 1 (by rfl) ⟨1185464, by rfl⟩ : syracuseStep 1580619 = 2370929) B2370929
theorem B1580631 : Blo 1580488 1580631 := bstep (se 1 (by rfl) ⟨1185473, by rfl⟩ : syracuseStep 1580631 = 2370947) B2370947
theorem B2252377 : Blo 1580488 2252377 := bstep (se 2 (by rfl) ⟨844641, by rfl⟩ : syracuseStep 2252377 = 1689283) B1689283
theorem B5340761 : Blo 1580488 5340761 := bstep (se 2 (by rfl) ⟨2002785, by rfl⟩ : syracuseStep 5340761 = 4005571) B4005571
theorem B6413917 : Blo 1580488 6413917 := bstep (se 3 (by rfl) ⟨1202609, by rfl⟩ : syracuseStep 6413917 = 2405219) B2405219
theorem B1580651 : Blo 1580488 1580651 := bstep (se 1 (by rfl) ⟨1185488, by rfl⟩ : syracuseStep 1580651 = 2370977) B2370977
theorem B1580663 : Blo 1580488 1580663 := bstep (se 1 (by rfl) ⟨1185497, by rfl⟩ : syracuseStep 1580663 = 2370995) B2370995
theorem B1580683 : Blo 1580488 1580683 := bstep (se 1 (by rfl) ⟨1185512, by rfl⟩ : syracuseStep 1580683 = 2371025) B2371025
theorem B1580695 : Blo 1580488 1580695 := bstep (se 1 (by rfl) ⟨1185521, by rfl⟩ : syracuseStep 1580695 = 2371043) B2371043
theorem B1580715 : Blo 1580488 1580715 := bstep (se 1 (by rfl) ⟨1185536, by rfl⟩ : syracuseStep 1580715 = 2371073) B2371073
theorem B1580727 : Blo 1580488 1580727 := bstep (se 1 (by rfl) ⟨1185545, by rfl⟩ : syracuseStep 1580727 = 2371091) B2371091
theorem B1580747 : Blo 1580488 1580747 := bstep (se 1 (by rfl) ⟨1185560, by rfl⟩ : syracuseStep 1580747 = 2371121) B2371121
theorem B1580759 : Blo 1580488 1580759 := bstep (se 1 (by rfl) ⟨1185569, by rfl⟩ : syracuseStep 1580759 = 2371139) B2371139
theorem B1580779 : Blo 1580488 1580779 := bstep (se 1 (by rfl) ⟨1185584, by rfl⟩ : syracuseStep 1580779 = 2371169) B2371169
theorem B1580791 : Blo 1580488 1580791 := bstep (se 1 (by rfl) ⟨1185593, by rfl⟩ : syracuseStep 1580791 = 2371187) B2371187
theorem B1580811 : Blo 1580488 1580811 := bstep (se 1 (by rfl) ⟨1185608, by rfl⟩ : syracuseStep 1580811 = 2371217) B2371217
theorem B2670347 : Blo 1580488 2670347 := bstep (se 1 (by rfl) ⟨2002760, by rfl⟩ : syracuseStep 2670347 = 4005521) B4005521
theorem B1580823 : Blo 1580488 1580823 := bstep (se 1 (by rfl) ⟨1185617, by rfl⟩ : syracuseStep 1580823 = 2371235) B2371235
theorem B1580843 : Blo 1580488 1580843 := bstep (se 1 (by rfl) ⟨1185632, by rfl⟩ : syracuseStep 1580843 = 2371265) B2371265
theorem B1580855 : Blo 1580488 1580855 := bstep (se 1 (by rfl) ⟨1185641, by rfl⟩ : syracuseStep 1580855 = 2371283) B2371283
theorem B1580875 : Blo 1580488 1580875 := bstep (se 1 (by rfl) ⟨1185656, by rfl⟩ : syracuseStep 1580875 = 2371313) B2371313
theorem B1580887 : Blo 1580488 1580887 := bstep (se 1 (by rfl) ⟨1185665, by rfl⟩ : syracuseStep 1580887 = 2371331) B2371331
theorem B10149725 : Blo 1580488 10149725 := bstep (se 3 (by rfl) ⟨1903073, by rfl⟩ : syracuseStep 10149725 = 3806147) B3806147
theorem B1580907 : Blo 1580488 1580907 := bstep (se 1 (by rfl) ⟨1185680, by rfl⟩ : syracuseStep 1580907 = 2371361) B2371361
theorem B1580919 : Blo 1580488 1580919 := bstep (se 1 (by rfl) ⟨1185689, by rfl⟩ : syracuseStep 1580919 = 2371379) B2371379
theorem B6758275 : Blo 1580488 6758275 := bstep (se 1 (by rfl) ⟨5068706, by rfl⟩ : syracuseStep 6758275 = 10137413) B10137413
theorem B1580939 : Blo 1580488 1580939 := bstep (se 1 (by rfl) ⟨1185704, by rfl⟩ : syracuseStep 1580939 = 2371409) B2371409
theorem B1580951 : Blo 1580488 1580951 := bstep (se 1 (by rfl) ⟨1185713, by rfl⟩ : syracuseStep 1580951 = 2371427) B2371427
theorem B1580971 : Blo 1580488 1580971 := bstep (se 1 (by rfl) ⟨1185728, by rfl⟩ : syracuseStep 1580971 = 2371457) B2371457
theorem B1580983 : Blo 1580488 1580983 := bstep (se 1 (by rfl) ⟨1185737, by rfl⟩ : syracuseStep 1580983 = 2371475) B2371475
theorem B1581003 : Blo 1580488 1581003 := bstep (se 1 (by rfl) ⟨1185752, by rfl⟩ : syracuseStep 1581003 = 2371505) B2371505
theorem B1581015 : Blo 1580488 1581015 := bstep (se 1 (by rfl) ⟨1185761, by rfl⟩ : syracuseStep 1581015 = 2371523) B2371523
theorem B1581035 : Blo 1580488 1581035 := bstep (se 1 (by rfl) ⟨1185776, by rfl⟩ : syracuseStep 1581035 = 2371553) B2371553
theorem B1581047 : Blo 1580488 1581047 := bstep (se 1 (by rfl) ⟨1185785, by rfl⟩ : syracuseStep 1581047 = 2371571) B2371571
theorem B1581063 : Blo 1580488 1581063 := bstep (se 1 (by rfl) ⟨1185797, by rfl⟩ : syracuseStep 1581063 = 2371595) B2371595
theorem B1581071 : Blo 1580488 1581071 := bstep (se 1 (by rfl) ⟨1185803, by rfl⟩ : syracuseStep 1581071 = 2371607) B2371607
theorem B4808747 : Blo 1580488 4808747 := bstep (se 1 (by rfl) ⟨3606560, by rfl⟩ : syracuseStep 4808747 = 7213121) B7213121
theorem B1581115 : Blo 1580488 1581115 := bstep (se 1 (by rfl) ⟨1185836, by rfl⟩ : syracuseStep 1581115 = 2371673) B2371673
theorem B8224829 : Blo 1580488 8224829 := bstep (se 3 (by rfl) ⟨1542155, by rfl⟩ : syracuseStep 8224829 = 3084311) B3084311
theorem B12173399 : Blo 1580488 12173399 := bstep (se 1 (by rfl) ⟨9130049, by rfl⟩ : syracuseStep 12173399 = 18260099) B18260099
theorem B36528245 : Blo 1580488 36528245 := bstep (se 5 (by rfl) ⟨1712261, by rfl⟩ : syracuseStep 36528245 = 3424523) B3424523
theorem B1581191 : Blo 1580488 1581191 := bstep (se 1 (by rfl) ⟨1185893, by rfl⟩ : syracuseStep 1581191 = 2371787) B2371787
theorem B1581199 : Blo 1580488 1581199 := bstep (se 1 (by rfl) ⟨1185899, by rfl⟩ : syracuseStep 1581199 = 2371799) B2371799
theorem B1581243 : Blo 1580488 1581243 := bstep (se 1 (by rfl) ⟨1185932, by rfl⟩ : syracuseStep 1581243 = 2371865) B2371865
theorem B1581319 : Blo 1580488 1581319 := bstep (se 1 (by rfl) ⟨1185989, by rfl⟩ : syracuseStep 1581319 = 2371979) B2371979
theorem B1581327 : Blo 1580488 1581327 := bstep (se 1 (by rfl) ⟨1185995, by rfl⟩ : syracuseStep 1581327 = 2371991) B2371991
theorem B1581371 : Blo 1580488 1581371 := bstep (se 1 (by rfl) ⟨1186028, by rfl⟩ : syracuseStep 1581371 = 2372057) B2372057
theorem B1900919 : Blo 1580488 1900919 := bstep (se 1 (by rfl) ⟨1425689, by rfl⟩ : syracuseStep 1900919 = 2851379) B2851379
theorem B1581447 : Blo 1580488 1581447 := bstep (se 1 (by rfl) ⟨1186085, by rfl⟩ : syracuseStep 1581447 = 2372171) B2372171
theorem B12829063 : Blo 1580488 12829063 := bstep (se 1 (by rfl) ⟨9621797, by rfl⟩ : syracuseStep 12829063 = 19243595) B19243595
theorem B1581455 : Blo 1580488 1581455 := bstep (se 1 (by rfl) ⟨1186091, by rfl⟩ : syracuseStep 1581455 = 2372183) B2372183
theorem B1778107 : Blo 1580488 1778107 := bstep (se 1 (by rfl) ⟨1333580, by rfl⟩ : syracuseStep 1778107 = 2667161) B2667161
theorem B1581499 : Blo 1580488 1581499 := bstep (se 1 (by rfl) ⟨1186124, by rfl⟩ : syracuseStep 1581499 = 2372249) B2372249
theorem B1581575 : Blo 1580488 1581575 := bstep (se 1 (by rfl) ⟨1186181, by rfl⟩ : syracuseStep 1581575 = 2372363) B2372363
theorem B1581583 : Blo 1580488 1581583 := bstep (se 1 (by rfl) ⟨1186187, by rfl⟩ : syracuseStep 1581583 = 2372375) B2372375
theorem B3605035 : Blo 1580488 3605035 := bstep (se 1 (by rfl) ⟨2703776, by rfl⟩ : syracuseStep 3605035 = 5407553) B5407553
theorem B16228907 : Blo 1580488 16228907 := bstep (se 1 (by rfl) ⟨12171680, by rfl⟩ : syracuseStep 16228907 = 24343361) B24343361
theorem B4506155 : Blo 1580488 4506155 := bstep (se 1 (by rfl) ⟨3379616, by rfl⟩ : syracuseStep 4506155 = 6759233) B6759233
theorem B1581627 : Blo 1580488 1581627 := bstep (se 1 (by rfl) ⟨1186220, by rfl⟩ : syracuseStep 1581627 = 2372441) B2372441
theorem B1581703 : Blo 1580488 1581703 := bstep (se 1 (by rfl) ⟨1186277, by rfl⟩ : syracuseStep 1581703 = 2372555) B2372555
theorem B1581711 : Blo 1580488 1581711 := bstep (se 1 (by rfl) ⟨1186283, by rfl⟩ : syracuseStep 1581711 = 2372567) B2372567
theorem B1581755 : Blo 1580488 1581755 := bstep (se 1 (by rfl) ⟨1186316, by rfl⟩ : syracuseStep 1581755 = 2372633) B2372633
theorem B5702381 : Blo 1580488 5702381 := bstep (se 3 (by rfl) ⟨1069196, by rfl⟩ : syracuseStep 5702381 = 2138393) B2138393
theorem B12165889 : Blo 1580488 12165889 := bstep (se 2 (by rfl) ⟨4562208, by rfl⟩ : syracuseStep 12165889 = 9124417) B9124417
theorem B1581831 : Blo 1580488 1581831 := bstep (se 1 (by rfl) ⟨1186373, by rfl⟩ : syracuseStep 1581831 = 2372747) B2372747
theorem B21635855 : Blo 1580488 21635855 := bstep (se 1 (by rfl) ⟨16226891, by rfl⟩ : syracuseStep 21635855 = 32453783) B32453783
theorem B1581839 : Blo 1580488 1581839 := bstep (se 1 (by rfl) ⟨1186379, by rfl⟩ : syracuseStep 1581839 = 2372759) B2372759
theorem B1581883 : Blo 1580488 1581883 := bstep (se 1 (by rfl) ⟨1186412, by rfl⟩ : syracuseStep 1581883 = 2372825) B2372825
theorem B8553275 : Blo 1580488 8553275 := bstep (se 1 (by rfl) ⟨6414956, by rfl⟩ : syracuseStep 8553275 = 12829913) B12829913
theorem B1581959 : Blo 1580488 1581959 := bstep (se 1 (by rfl) ⟨1186469, by rfl⟩ : syracuseStep 1581959 = 2372939) B2372939
theorem B1778575 : Blo 1580488 1778575 := bstep (se 1 (by rfl) ⟨1333931, by rfl⟩ : syracuseStep 1778575 = 2667863) B2667863
theorem B1581967 : Blo 1580488 1581967 := bstep (se 1 (by rfl) ⟨1186475, by rfl⟩ : syracuseStep 1581967 = 2372951) B2372951
theorem B1582011 : Blo 1580488 1582011 := bstep (se 1 (by rfl) ⟨1186508, by rfl⟩ : syracuseStep 1582011 = 2373017) B2373017
theorem B19243979 : Blo 1580488 19243979 := bstep (se 1 (by rfl) ⟨14432984, by rfl⟩ : syracuseStep 19243979 = 28865969) B28865969
theorem B1582087 : Blo 1580488 1582087 := bstep (se 1 (by rfl) ⟨1186565, by rfl⟩ : syracuseStep 1582087 = 2373131) B2373131
theorem B3556367 : Blo 1580488 3556367 := bstep (se 1 (by rfl) ⟨2667275, by rfl⟩ : syracuseStep 3556367 = 5334551) B5334551
theorem B1582095 : Blo 1580488 1582095 := bstep (se 1 (by rfl) ⟨1186571, by rfl⟩ : syracuseStep 1582095 = 2373143) B2373143
theorem B9004061 : Blo 1580488 9004061 := bstep (se 3 (by rfl) ⟨1688261, by rfl⟩ : syracuseStep 9004061 = 3376523) B3376523
theorem B3556385 : Blo 1580488 3556385 := bstep (se 2 (by rfl) ⟨1333644, by rfl⟩ : syracuseStep 3556385 = 2667289) B2667289
theorem B3802145 : Blo 1580488 3802145 := bstep (se 2 (by rfl) ⟨1425804, by rfl⟩ : syracuseStep 3802145 = 2851609) B2851609
theorem B1582139 : Blo 1580488 1582139 := bstep (se 1 (by rfl) ⟨1186604, by rfl⟩ : syracuseStep 1582139 = 2373209) B2373209
theorem B1582215 : Blo 1580488 1582215 := bstep (se 1 (by rfl) ⟨1186661, by rfl⟩ : syracuseStep 1582215 = 2373323) B2373323
theorem B1582223 : Blo 1580488 1582223 := bstep (se 1 (by rfl) ⟨1186667, by rfl⟩ : syracuseStep 1582223 = 2373335) B2373335
theorem B1582267 : Blo 1580488 1582267 := bstep (se 1 (by rfl) ⟨1186700, by rfl⟩ : syracuseStep 1582267 = 2373401) B2373401
theorem B1582343 : Blo 1580488 1582343 := bstep (se 1 (by rfl) ⟨1186757, by rfl⟩ : syracuseStep 1582343 = 2373515) B2373515
theorem B1582351 : Blo 1580488 1582351 := bstep (se 1 (by rfl) ⟨1186763, by rfl⟩ : syracuseStep 1582351 = 2373527) B2373527
theorem B16442657 : Blo 1580488 16442657 := bstep (se 2 (by rfl) ⟨6165996, by rfl⟩ : syracuseStep 16442657 = 12331993) B12331993
theorem B7595315 : Blo 1580488 7595315 := bstep (se 1 (by rfl) ⟨5696486, by rfl⟩ : syracuseStep 7595315 = 11392973) B11392973
theorem B1582395 : Blo 1580488 1582395 := bstep (se 1 (by rfl) ⟨1186796, by rfl⟩ : syracuseStep 1582395 = 2373593) B2373593
theorem B3556727 : Blo 1580488 3556727 := bstep (se 1 (by rfl) ⟨2667545, by rfl⟩ : syracuseStep 3556727 = 5335091) B5335091
theorem B8111495 : Blo 1580488 8111495 := bstep (se 1 (by rfl) ⟨6083621, by rfl⟩ : syracuseStep 8111495 = 12167243) B12167243
theorem B1779079 : Blo 1580488 1779079 := bstep (se 1 (by rfl) ⟨1334309, by rfl⟩ : syracuseStep 1779079 = 2668619) B2668619
theorem B1582471 : Blo 1580488 1582471 := bstep (se 1 (by rfl) ⟨1186853, by rfl⟩ : syracuseStep 1582471 = 2373707) B2373707
theorem B1582479 : Blo 1580488 1582479 := bstep (se 1 (by rfl) ⟨1186859, by rfl⟩ : syracuseStep 1582479 = 2373719) B2373719
theorem B2000315 : Blo 1580488 2000315 := bstep (se 1 (by rfl) ⟨1500236, by rfl⟩ : syracuseStep 2000315 = 3000473) B3000473
theorem B8005067 : Blo 1580488 8005067 := bstep (se 1 (by rfl) ⟨6003800, by rfl⟩ : syracuseStep 8005067 = 12007601) B12007601
theorem B15402449 : Blo 1580488 15402449 := bstep (se 2 (by rfl) ⟨5775918, by rfl⟩ : syracuseStep 15402449 = 11551837) B11551837
theorem B5064221 : Blo 1580488 5064221 := bstep (se 3 (by rfl) ⟨949541, by rfl⟩ : syracuseStep 5064221 = 1899083) B1899083
theorem B3556907 : Blo 1580488 3556907 := bstep (se 1 (by rfl) ⟨2667680, by rfl⟩ : syracuseStep 3556907 = 5335361) B5335361
theorem B3606059 : Blo 1580488 3606059 := bstep (se 1 (by rfl) ⟨2704544, by rfl⟩ : syracuseStep 3606059 = 5409089) B5409089
theorem B1779259 : Blo 1580488 1779259 := bstep (se 1 (by rfl) ⟨1334444, by rfl⟩ : syracuseStep 1779259 = 2668889) B2668889
theorem B22808141 : Blo 1580488 22808141 := bstep (se 3 (by rfl) ⟨4276526, by rfl⟩ : syracuseStep 22808141 = 8553053) B8553053
theorem B8554177 : Blo 1580488 8554177 := bstep (se 2 (by rfl) ⟨3207816, by rfl⟩ : syracuseStep 8554177 = 6415633) B6415633
theorem B8005391 : Blo 1580488 8005391 := bstep (se 1 (by rfl) ⟨6004043, by rfl⟩ : syracuseStep 8005391 = 12008087) B12008087
theorem B3557267 : Blo 1580488 3557267 := bstep (se 1 (by rfl) ⟨2667950, by rfl⟩ : syracuseStep 3557267 = 5335901) B5335901
theorem B3557321 : Blo 1580488 3557321 := bstep (se 2 (by rfl) ⟨1333995, by rfl⟩ : syracuseStep 3557321 = 2667991) B2667991
theorem B1779727 : Blo 1580488 1779727 := bstep (se 1 (by rfl) ⟨1334795, by rfl⟩ : syracuseStep 1779727 = 2669591) B2669591
theorem B27035693 : Blo 1580488 27035693 := bstep (se 3 (by rfl) ⟨5069192, by rfl⟩ : syracuseStep 27035693 = 10138385) B10138385
theorem B2001287 : Blo 1580488 2001287 := bstep (se 1 (by rfl) ⟨1500965, by rfl⟩ : syracuseStep 2001287 = 3001931) B3001931
theorem B3377609 : Blo 1580488 3377609 := bstep (se 2 (by rfl) ⟨1266603, by rfl⟩ : syracuseStep 3377609 = 2533207) B2533207
theorem B1780231 : Blo 1580488 1780231 := bstep (se 1 (by rfl) ⟨1335173, by rfl⟩ : syracuseStep 1780231 = 2670347) B2670347
theorem B7211531 : Blo 1580488 7211531 := bstep (se 1 (by rfl) ⟨5408648, by rfl⟩ : syracuseStep 7211531 = 10817297) B10817297
theorem B3558023 : Blo 1580488 3558023 := bstep (se 1 (by rfl) ⟨2668517, by rfl⟩ : syracuseStep 3558023 = 5337035) B5337035
theorem B6007553 : Blo 1580488 6007553 := bstep (se 2 (by rfl) ⟨2252832, by rfl⟩ : syracuseStep 6007553 = 4505665) B4505665
theorem B3205903 : Blo 1580488 3205903 := bstep (se 1 (by rfl) ⟨2404427, by rfl⟩ : syracuseStep 3205903 = 4808855) B4808855
theorem B10136335 : Blo 1580488 10136335 := bstep (se 1 (by rfl) ⟨7602251, by rfl⟩ : syracuseStep 10136335 = 15204503) B15204503
theorem B6007567 : Blo 1580488 6007567 := bstep (se 1 (by rfl) ⟨4505675, by rfl⟩ : syracuseStep 6007567 = 9011351) B9011351
theorem B18025253 : Blo 1580488 18025253 := bstep (se 4 (by rfl) ⟨1689867, by rfl⟩ : syracuseStep 18025253 = 3379735) B3379735
theorem B3558203 : Blo 1580488 3558203 := bstep (se 1 (by rfl) ⟨2668652, by rfl⟩ : syracuseStep 3558203 = 5337305) B5337305
theorem B5335955 : Blo 1580488 5335955 := bstep (se 1 (by rfl) ⟨4001966, by rfl⟩ : syracuseStep 5335955 = 8003933) B8003933
theorem B3558329 : Blo 1580488 3558329 := bstep (se 2 (by rfl) ⟨1334373, by rfl⟩ : syracuseStep 3558329 = 2668747) B2668747
theorem B2001935 : Blo 1580488 2001935 := bstep (se 1 (by rfl) ⟨1501451, by rfl⟩ : syracuseStep 2001935 = 3002903) B3002903
theorem B76934285 : Blo 1580488 76934285 := bstep (se 3 (by rfl) ⟨14425178, by rfl⟩ : syracuseStep 76934285 = 28850357) B28850357
theorem B3001529 : Blo 1580488 3001529 := bstep (se 2 (by rfl) ⟨1125573, by rfl⟩ : syracuseStep 3001529 = 2251147) B2251147
theorem B3378361 : Blo 1580488 3378361 := bstep (se 2 (by rfl) ⟨1266885, by rfl⟩ : syracuseStep 3378361 = 2533771) B2533771
theorem B8006849 : Blo 1580488 8006849 := bstep (se 2 (by rfl) ⟨3002568, by rfl⟩ : syracuseStep 8006849 = 6005137) B6005137
theorem B2370761 : Blo 1580488 2370761 := bstep (se 2 (by rfl) ⟨889035, by rfl⟩ : syracuseStep 2370761 = 1778071) B1778071
theorem B4001035 : Blo 1580488 4001035 := bstep (se 1 (by rfl) ⟨3000776, by rfl⟩ : syracuseStep 4001035 = 6001553) B6001553
theorem B3558671 : Blo 1580488 3558671 := bstep (se 1 (by rfl) ⟨2669003, by rfl⟩ : syracuseStep 3558671 = 5338007) B5338007
theorem B3558689 : Blo 1580488 3558689 := bstep (se 2 (by rfl) ⟨1334508, by rfl⟩ : syracuseStep 3558689 = 2669017) B2669017
theorem B2534699 : Blo 1580488 2534699 := bstep (se 1 (by rfl) ⟨1901024, by rfl⟩ : syracuseStep 2534699 = 3802049) B3802049
theorem B2370875 : Blo 1580488 2370875 := bstep (se 1 (by rfl) ⟨1778156, by rfl⟩ : syracuseStep 2370875 = 3556313) B3556313
theorem B2370935 : Blo 1580488 2370935 := bstep (se 1 (by rfl) ⟨1778201, by rfl⟩ : syracuseStep 2370935 = 3556403) B3556403
theorem B2370959 : Blo 1580488 2370959 := bstep (se 1 (by rfl) ⟨1778219, by rfl⟩ : syracuseStep 2370959 = 3556439) B3556439
theorem B12012947 : Blo 1580488 12012947 := bstep (se 1 (by rfl) ⟨9009710, by rfl⟩ : syracuseStep 12012947 = 18019421) B18019421
theorem B4001177 : Blo 1580488 4001177 := bstep (se 2 (by rfl) ⟨1500441, by rfl⟩ : syracuseStep 4001177 = 3000883) B3000883
theorem B30387635 : Blo 1580488 30387635 := bstep (se 1 (by rfl) ⟨22790726, by rfl⟩ : syracuseStep 30387635 = 45581453) B45581453
theorem B2371001 : Blo 1580488 2371001 := bstep (se 2 (by rfl) ⟨889125, by rfl⟩ : syracuseStep 2371001 = 1778251) B1778251
theorem B4500937 : Blo 1580488 4500937 := bstep (se 2 (by rfl) ⟨1687851, by rfl⟩ : syracuseStep 4500937 = 3375703) B3375703
theorem B2371079 : Blo 1580488 2371079 := bstep (se 1 (by rfl) ⟨1778309, by rfl⟩ : syracuseStep 2371079 = 3556619) B3556619
theorem B2371115 : Blo 1580488 2371115 := bstep (se 1 (by rfl) ⟨1778336, by rfl⟩ : syracuseStep 2371115 = 3556673) B3556673
theorem B4001339 : Blo 1580488 4001339 := bstep (se 1 (by rfl) ⟨3001004, by rfl⟩ : syracuseStep 4001339 = 6002009) B6002009
theorem B9006659 : Blo 1580488 9006659 := bstep (se 1 (by rfl) ⟨6754994, by rfl⟩ : syracuseStep 9006659 = 13509989) B13509989
theorem B2371145 : Blo 1580488 2371145 := bstep (se 2 (by rfl) ⟨889179, by rfl⟩ : syracuseStep 2371145 = 1778359) B1778359
theorem B6409847 : Blo 1580488 6409847 := bstep (se 1 (by rfl) ⟨4807385, by rfl⟩ : syracuseStep 6409847 = 9614771) B9614771
theorem B3559031 : Blo 1580488 3559031 := bstep (se 1 (by rfl) ⟨2669273, by rfl⟩ : syracuseStep 3559031 = 5338547) B5338547
theorem B2371259 : Blo 1580488 2371259 := bstep (se 1 (by rfl) ⟨1778444, by rfl⟩ : syracuseStep 2371259 = 3556889) B3556889
theorem B2371319 : Blo 1580488 2371319 := bstep (se 1 (by rfl) ⟨1778489, by rfl⟩ : syracuseStep 2371319 = 3556979) B3556979
theorem B2371343 : Blo 1580488 2371343 := bstep (se 1 (by rfl) ⟨1778507, by rfl⟩ : syracuseStep 2371343 = 3557015) B3557015
theorem B4501291 : Blo 1580488 4501291 := bstep (se 1 (by rfl) ⟨3375968, by rfl⟩ : syracuseStep 4501291 = 6751937) B6751937
theorem B3559211 : Blo 1580488 3559211 := bstep (se 1 (by rfl) ⟨2669408, by rfl⟩ : syracuseStep 3559211 = 5338817) B5338817
theorem B12005171 : Blo 1580488 12005171 := bstep (se 1 (by rfl) ⟨9003878, by rfl⟩ : syracuseStep 12005171 = 18007757) B18007757
theorem B2371385 : Blo 1580488 2371385 := bstep (se 2 (by rfl) ⟨889269, by rfl⟩ : syracuseStep 2371385 = 1778539) B1778539
theorem B2371463 : Blo 1580488 2371463 := bstep (se 1 (by rfl) ⟨1778597, by rfl⟩ : syracuseStep 2371463 = 3557195) B3557195
theorem B2887571 : Blo 1580488 2887571 := bstep (se 1 (by rfl) ⟨2165678, by rfl⟩ : syracuseStep 2887571 = 4331357) B4331357
theorem B4001683 : Blo 1580488 4001683 := bstep (se 1 (by rfl) ⟨3001262, by rfl⟩ : syracuseStep 4001683 = 6002525) B6002525
theorem B2371499 : Blo 1580488 2371499 := bstep (se 1 (by rfl) ⟨1778624, by rfl⟩ : syracuseStep 2371499 = 3557249) B3557249
theorem B2371529 : Blo 1580488 2371529 := bstep (se 2 (by rfl) ⟨889323, by rfl⟩ : syracuseStep 2371529 = 1778647) B1778647
theorem B7598083 : Blo 1580488 7598083 := bstep (se 1 (by rfl) ⟨5698562, by rfl⟩ : syracuseStep 7598083 = 11397125) B11397125
theorem B4001825 : Blo 1580488 4001825 := bstep (se 2 (by rfl) ⟨1500684, by rfl⟩ : syracuseStep 4001825 = 3001369) B3001369
theorem B2371643 : Blo 1580488 2371643 := bstep (se 1 (by rfl) ⟨1778732, by rfl⟩ : syracuseStep 2371643 = 3557465) B3557465
theorem B4501565 : Blo 1580488 4501565 := bstep (se 3 (by rfl) ⟨844043, by rfl⟩ : syracuseStep 4501565 = 1688087) B1688087
theorem B58470493 : Blo 1580488 58470493 := bstep (se 3 (by rfl) ⟨10963217, by rfl⟩ : syracuseStep 58470493 = 21926435) B21926435
theorem B2371703 : Blo 1580488 2371703 := bstep (se 1 (by rfl) ⟨1778777, by rfl⟩ : syracuseStep 2371703 = 3557555) B3557555
theorem B2371727 : Blo 1580488 2371727 := bstep (se 1 (by rfl) ⟨1778795, by rfl⟩ : syracuseStep 2371727 = 3557591) B3557591
theorem B3559571 : Blo 1580488 3559571 := bstep (se 1 (by rfl) ⟨2669678, by rfl⟩ : syracuseStep 3559571 = 5339357) B5339357
theorem B2371769 : Blo 1580488 2371769 := bstep (se 2 (by rfl) ⟨889413, by rfl⟩ : syracuseStep 2371769 = 1778827) B1778827
theorem B25653449 : Blo 1580488 25653449 := bstep (se 2 (by rfl) ⟨9620043, by rfl⟩ : syracuseStep 25653449 = 19240087) B19240087
theorem B3559625 : Blo 1580488 3559625 := bstep (se 2 (by rfl) ⟨1334859, by rfl⟩ : syracuseStep 3559625 = 2669719) B2669719
theorem B2371847 : Blo 1580488 2371847 := bstep (se 1 (by rfl) ⟨1778885, by rfl⟩ : syracuseStep 2371847 = 3557771) B3557771
theorem B5337359 : Blo 1580488 5337359 := bstep (se 1 (by rfl) ⟨4003019, by rfl⟩ : syracuseStep 5337359 = 8006039) B8006039
theorem B2371883 : Blo 1580488 2371883 := bstep (se 1 (by rfl) ⟨1778912, by rfl⟩ : syracuseStep 2371883 = 3557825) B3557825
theorem B3002683 : Blo 1580488 3002683 := bstep (se 1 (by rfl) ⟨2252012, by rfl⟩ : syracuseStep 3002683 = 4504025) B4504025
theorem B2371913 : Blo 1580488 2371913 := bstep (se 2 (by rfl) ⟨889467, by rfl⟩ : syracuseStep 2371913 = 1778935) B1778935
theorem B2404793 : Blo 1580488 2404793 := bstep (se 2 (by rfl) ⟨901797, by rfl⟩ : syracuseStep 2404793 = 1803595) B1803595
theorem B14430649 : Blo 1580488 14430649 := bstep (se 2 (by rfl) ⟨5411493, by rfl⟩ : syracuseStep 14430649 = 10822987) B10822987
theorem B2372027 : Blo 1580488 2372027 := bstep (se 1 (by rfl) ⟨1779020, by rfl⟩ : syracuseStep 2372027 = 3558041) B3558041
theorem B8008145 : Blo 1580488 8008145 := bstep (se 2 (by rfl) ⟨3003054, by rfl⟩ : syracuseStep 8008145 = 6006109) B6006109
theorem B2372087 : Blo 1580488 2372087 := bstep (se 1 (by rfl) ⟨1779065, by rfl⟩ : syracuseStep 2372087 = 3558131) B3558131
theorem B2372111 : Blo 1580488 2372111 := bstep (se 1 (by rfl) ⟨1779083, by rfl⟩ : syracuseStep 2372111 = 3558167) B3558167
theorem B5337629 : Blo 1580488 5337629 := bstep (se 3 (by rfl) ⟨1000805, by rfl⟩ : syracuseStep 5337629 = 2001611) B2001611
theorem B6754859 : Blo 1580488 6754859 := bstep (se 1 (by rfl) ⟨5066144, by rfl⟩ : syracuseStep 6754859 = 10132289) B10132289
theorem B2372153 : Blo 1580488 2372153 := bstep (se 2 (by rfl) ⟨889557, by rfl⟩ : syracuseStep 2372153 = 1779115) B1779115
theorem B2667127 : Blo 1580488 2667127 := bstep (se 1 (by rfl) ⟨2000345, by rfl⟩ : syracuseStep 2667127 = 4000691) B4000691
theorem B2372231 : Blo 1580488 2372231 := bstep (se 1 (by rfl) ⟨1779173, by rfl⟩ : syracuseStep 2372231 = 3558347) B3558347
theorem B2372267 : Blo 1580488 2372267 := bstep (se 1 (by rfl) ⟨1779200, by rfl⟩ : syracuseStep 2372267 = 3558401) B3558401
theorem B3797705 : Blo 1580488 3797705 := bstep (se 2 (by rfl) ⟨1424139, by rfl⟩ : syracuseStep 3797705 = 2848279) B2848279
theorem B2372297 : Blo 1580488 2372297 := bstep (se 2 (by rfl) ⟨889611, by rfl⟩ : syracuseStep 2372297 = 1779223) B1779223
theorem B3003169 : Blo 1580488 3003169 := bstep (se 2 (by rfl) ⟨1126188, by rfl⟩ : syracuseStep 3003169 = 2252377) B2252377
theorem B2667323 : Blo 1580488 2667323 := bstep (se 1 (by rfl) ⟨2000492, by rfl⟩ : syracuseStep 2667323 = 4000985) B4000985
theorem B2372411 : Blo 1580488 2372411 := bstep (se 1 (by rfl) ⟨1779308, by rfl⟩ : syracuseStep 2372411 = 3558617) B3558617
theorem B6001523 : Blo 1580488 6001523 := bstep (se 1 (by rfl) ⟨4501142, by rfl⟩ : syracuseStep 6001523 = 9002285) B9002285
theorem B2372471 : Blo 1580488 2372471 := bstep (se 1 (by rfl) ⟨1779353, by rfl⟩ : syracuseStep 2372471 = 3558707) B3558707
theorem B3560327 : Blo 1580488 3560327 := bstep (se 1 (by rfl) ⟨2670245, by rfl⟩ : syracuseStep 3560327 = 5340491) B5340491
theorem B2372495 : Blo 1580488 2372495 := bstep (se 1 (by rfl) ⟨1779371, by rfl⟩ : syracuseStep 2372495 = 3558743) B3558743
theorem B2372537 : Blo 1580488 2372537 := bstep (se 2 (by rfl) ⟨889701, by rfl⟩ : syracuseStep 2372537 = 1779403) B1779403
theorem B4002817 : Blo 1580488 4002817 := bstep (se 2 (by rfl) ⟨1501056, by rfl⟩ : syracuseStep 4002817 = 3002113) B3002113
theorem B2372615 : Blo 1580488 2372615 := bstep (se 1 (by rfl) ⟨1779461, by rfl⟩ : syracuseStep 2372615 = 3558923) B3558923
theorem B2372651 : Blo 1580488 2372651 := bstep (se 1 (by rfl) ⟨1779488, by rfl⟩ : syracuseStep 2372651 = 3558977) B3558977
theorem B3560507 : Blo 1580488 3560507 := bstep (se 1 (by rfl) ⟨2670380, by rfl⟩ : syracuseStep 3560507 = 5340761) B5340761
theorem B2372681 : Blo 1580488 2372681 := bstep (se 2 (by rfl) ⟨889755, by rfl⟩ : syracuseStep 2372681 = 1779511) B1779511
theorem B2372795 : Blo 1580488 2372795 := bstep (se 1 (by rfl) ⟨1779596, by rfl⟩ : syracuseStep 2372795 = 3559193) B3559193
theorem B2667721 : Blo 1580488 2667721 := bstep (se 2 (by rfl) ⟨1000395, by rfl⟩ : syracuseStep 2667721 = 2000791) B2000791
theorem B2372855 : Blo 1580488 2372855 := bstep (se 1 (by rfl) ⟨1779641, by rfl⟩ : syracuseStep 2372855 = 3559283) B3559283
theorem B2405639 : Blo 1580488 2405639 := bstep (se 1 (by rfl) ⟨1804229, by rfl⟩ : syracuseStep 2405639 = 3608459) B3608459
theorem B2372879 : Blo 1580488 2372879 := bstep (se 1 (by rfl) ⟨1779659, by rfl⟩ : syracuseStep 2372879 = 3559319) B3559319
theorem B9008435 : Blo 1580488 9008435 := bstep (se 1 (by rfl) ⟨6756326, by rfl⟩ : syracuseStep 9008435 = 13512653) B13512653
theorem B2372921 : Blo 1580488 2372921 := bstep (se 2 (by rfl) ⟨889845, by rfl⟩ : syracuseStep 2372921 = 1779691) B1779691
theorem B3798359 : Blo 1580488 3798359 := bstep (se 1 (by rfl) ⟨2848769, by rfl⟩ : syracuseStep 3798359 = 5697539) B5697539
theorem B2848135 : Blo 1580488 2848135 := bstep (se 1 (by rfl) ⟨2136101, by rfl⟩ : syracuseStep 2848135 = 4272203) B4272203
theorem B2372999 : Blo 1580488 2372999 := bstep (se 1 (by rfl) ⟨1779749, by rfl⟩ : syracuseStep 2372999 = 3559499) B3559499
theorem B2373035 : Blo 1580488 2373035 := bstep (se 1 (by rfl) ⟨1779776, by rfl⟩ : syracuseStep 2373035 = 3559553) B3559553
theorem B2373065 : Blo 1580488 2373065 := bstep (se 2 (by rfl) ⟨889899, by rfl⟩ : syracuseStep 2373065 = 1779799) B1779799
theorem B2373179 : Blo 1580488 2373179 := bstep (se 1 (by rfl) ⟨1779884, by rfl⟩ : syracuseStep 2373179 = 3559769) B3559769
theorem B4003415 : Blo 1580488 4003415 := bstep (se 1 (by rfl) ⟨3002561, by rfl⟩ : syracuseStep 4003415 = 6005123) B6005123
theorem B2373239 : Blo 1580488 2373239 := bstep (se 1 (by rfl) ⟨1779929, by rfl⟩ : syracuseStep 2373239 = 3559859) B3559859
theorem B2373263 : Blo 1580488 2373263 := bstep (se 1 (by rfl) ⟨1779947, by rfl⟩ : syracuseStep 2373263 = 3559895) B3559895
theorem B2373305 : Blo 1580488 2373305 := bstep (se 2 (by rfl) ⟨889989, by rfl⟩ : syracuseStep 2373305 = 1779979) B1779979
theorem B2373383 : Blo 1580488 2373383 := bstep (se 1 (by rfl) ⟨1780037, by rfl⟩ : syracuseStep 2373383 = 3560075) B3560075
theorem B4003627 : Blo 1580488 4003627 := bstep (se 1 (by rfl) ⟨3002720, by rfl⟩ : syracuseStep 4003627 = 6005441) B6005441
theorem B2373419 : Blo 1580488 2373419 := bstep (se 1 (by rfl) ⟨1780064, by rfl⟩ : syracuseStep 2373419 = 3560129) B3560129
theorem B2373449 : Blo 1580488 2373449 := bstep (se 2 (by rfl) ⟨890043, by rfl⟩ : syracuseStep 2373449 = 1780087) B1780087
theorem B2668423 : Blo 1580488 2668423 := bstep (se 1 (by rfl) ⟨2001317, by rfl⟩ : syracuseStep 2668423 = 4002635) B4002635
theorem B1603471 : Blo 1580488 1603471 := bstep (se 1 (by rfl) ⟨1202603, by rfl⟩ : syracuseStep 1603471 = 2405207) B2405207
theorem B5339033 : Blo 1580488 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B4003769 : Blo 1580488 4003769 := bstep (se 2 (by rfl) ⟨1501413, by rfl⟩ : syracuseStep 4003769 = 3002827) B3002827
theorem B2373563 : Blo 1580488 2373563 := bstep (se 1 (by rfl) ⟨1780172, by rfl⟩ : syracuseStep 2373563 = 3560345) B3560345
theorem B2373623 : Blo 1580488 2373623 := bstep (se 1 (by rfl) ⟨1780217, by rfl⟩ : syracuseStep 2373623 = 3560435) B3560435
theorem B2373647 : Blo 1580488 2373647 := bstep (se 1 (by rfl) ⟨1780235, by rfl⟩ : syracuseStep 2373647 = 3560471) B3560471
theorem B2373689 : Blo 1580488 2373689 := bstep (se 2 (by rfl) ⟨890133, by rfl⟩ : syracuseStep 2373689 = 1780267) B1780267
theorem B3799127 : Blo 1580488 3799127 := bstep (se 1 (by rfl) ⟨2849345, by rfl⟩ : syracuseStep 3799127 = 5698691) B5698691
theorem B4503671 : Blo 1580488 4503671 := bstep (se 1 (by rfl) ⟨3377753, by rfl⟩ : syracuseStep 4503671 = 6755507) B6755507
theorem B15202505 : Blo 1580488 15202505 := bstep (se 2 (by rfl) ⟨5700939, by rfl⟩ : syracuseStep 15202505 = 11401879) B11401879
theorem B5413235 : Blo 1580488 5413235 := bstep (se 1 (by rfl) ⟨4059926, by rfl⟩ : syracuseStep 5413235 = 8119853) B8119853
theorem B8550803 : Blo 1580488 8550803 := bstep (se 1 (by rfl) ⟨6413102, by rfl⟩ : syracuseStep 8550803 = 12826205) B12826205
theorem B2251255 : Blo 1580488 2251255 := bstep (se 1 (by rfl) ⟨1688441, by rfl⟩ : syracuseStep 2251255 = 3376883) B3376883
theorem B8010251 : Blo 1580488 8010251 := bstep (se 1 (by rfl) ⟨6007688, by rfl⟩ : syracuseStep 8010251 = 12015377) B12015377
theorem B2669071 : Blo 1580488 2669071 := bstep (se 1 (by rfl) ⟨2001803, by rfl⟩ : syracuseStep 2669071 = 4003607) B4003607
theorem B17095211 : Blo 1580488 17095211 := bstep (se 1 (by rfl) ⟨12821408, by rfl⟩ : syracuseStep 17095211 = 25642817) B25642817
theorem B9615959 : Blo 1580488 9615959 := bstep (se 1 (by rfl) ⟨7211969, by rfl⟩ : syracuseStep 9615959 = 14423939) B14423939
theorem B5339735 : Blo 1580488 5339735 := bstep (se 1 (by rfl) ⟨4004801, by rfl⟩ : syracuseStep 5339735 = 8009603) B8009603
theorem B8010413 : Blo 1580488 8010413 := bstep (se 3 (by rfl) ⟨1501952, by rfl⟩ : syracuseStep 8010413 = 3003905) B3003905
theorem B25991873 : Blo 1580488 25991873 := bstep (se 2 (by rfl) ⟨9746952, by rfl⟩ : syracuseStep 25991873 = 19493905) B19493905
theorem B9009893 : Blo 1580488 9009893 := bstep (se 4 (by rfl) ⟨844677, by rfl⟩ : syracuseStep 9009893 = 1689355) B1689355
theorem B3799819 : Blo 1580488 3799819 := bstep (se 1 (by rfl) ⟨2849864, by rfl⟩ : syracuseStep 3799819 = 5699729) B5699729
theorem B29653775 : Blo 1580488 29653775 := bstep (se 1 (by rfl) ⟨22240331, by rfl⟩ : syracuseStep 29653775 = 44480663) B44480663
theorem B2743159 : Blo 1580488 2743159 := bstep (se 1 (by rfl) ⟨2057369, by rfl⟩ : syracuseStep 2743159 = 4114739) B4114739
theorem B4004761 : Blo 1580488 4004761 := bstep (se 2 (by rfl) ⟨1501785, by rfl⟩ : syracuseStep 4004761 = 3003571) B3003571
theorem B26000291 : Blo 1580488 26000291 := bstep (se 1 (by rfl) ⟨19500218, by rfl⟩ : syracuseStep 26000291 = 39000437) B39000437
theorem B3799993 : Blo 1580488 3799993 := bstep (se 2 (by rfl) ⟨1424997, by rfl⟩ : syracuseStep 3799993 = 2849995) B2849995
theorem B6003665 : Blo 1580488 6003665 := bstep (se 2 (by rfl) ⟨2251374, by rfl⟩ : syracuseStep 6003665 = 4502749) B4502749
theorem B1899535 : Blo 1580488 1899535 := bstep (se 1 (by rfl) ⟨1424651, by rfl⟩ : syracuseStep 1899535 = 2849303) B2849303
theorem B2669611 : Blo 1580488 2669611 := bstep (se 1 (by rfl) ⟨2002208, by rfl⟩ : syracuseStep 2669611 = 4004417) B4004417
theorem B4004923 : Blo 1580488 4004923 := bstep (se 1 (by rfl) ⟨3003692, by rfl⟩ : syracuseStep 4004923 = 6007385) B6007385
theorem B9616445 : Blo 1580488 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B5340221 : Blo 1580488 5340221 := bstep (se 3 (by rfl) ⟨1001291, by rfl⟩ : syracuseStep 5340221 = 2002583) B2002583
theorem B9010349 : Blo 1580488 9010349 := bstep (se 3 (by rfl) ⟨1689440, by rfl⟩ : syracuseStep 9010349 = 3378881) B3378881
theorem B2669753 : Blo 1580488 2669753 := bstep (se 2 (by rfl) ⟨1001157, by rfl⟩ : syracuseStep 2669753 = 2002315) B2002315
theorem B4005065 : Blo 1580488 4005065 := bstep (se 2 (by rfl) ⟨1501899, by rfl⟩ : syracuseStep 4005065 = 3003799) B3003799
theorem B17104117 : Blo 1580488 17104117 := bstep (se 5 (by rfl) ⟨801755, by rfl⟩ : syracuseStep 17104117 = 1603511) B1603511
theorem B6003983 : Blo 1580488 6003983 := bstep (se 1 (by rfl) ⟨4502987, by rfl⟩ : syracuseStep 6003983 = 9005975) B9005975
theorem B8002961 : Blo 1580488 8002961 := bstep (se 2 (by rfl) ⟨3001110, by rfl⟩ : syracuseStep 8002961 = 6002221) B6002221
theorem B8551889 : Blo 1580488 8551889 := bstep (se 2 (by rfl) ⟨3206958, by rfl⟩ : syracuseStep 8551889 = 6413917) B6413917
theorem B1580551 : Blo 1580488 1580551 := bstep (se 1 (by rfl) ⟨1185413, by rfl⟩ : syracuseStep 1580551 = 2370827) B2370827
theorem B1580559 : Blo 1580488 1580559 := bstep (se 1 (by rfl) ⟨1185419, by rfl⟩ : syracuseStep 1580559 = 2370839) B2370839
theorem B2850319 : Blo 1580488 2850319 := bstep (se 1 (by rfl) ⟨2137739, by rfl⟩ : syracuseStep 2850319 = 4275479) B4275479
theorem B4005409 : Blo 1580488 4005409 := bstep (se 2 (by rfl) ⟨1502028, by rfl⟩ : syracuseStep 4005409 = 3004057) B3004057
theorem B1580603 : Blo 1580488 1580603 := bstep (se 1 (by rfl) ⟨1185452, by rfl⟩ : syracuseStep 1580603 = 2370905) B2370905
theorem B27065933 : Blo 1580488 27065933 := bstep (se 3 (by rfl) ⟨5074862, by rfl⟩ : syracuseStep 27065933 = 10149725) B10149725
theorem B1580679 : Blo 1580488 1580679 := bstep (se 1 (by rfl) ⟨1185509, by rfl⟩ : syracuseStep 1580679 = 2371019) B2371019
theorem B1580687 : Blo 1580488 1580687 := bstep (se 1 (by rfl) ⟨1185515, by rfl⟩ : syracuseStep 1580687 = 2371031) B2371031
theorem B1580731 : Blo 1580488 1580731 := bstep (se 1 (by rfl) ⟨1185548, by rfl⟩ : syracuseStep 1580731 = 2371097) B2371097
theorem B1580807 : Blo 1580488 1580807 := bstep (se 1 (by rfl) ⟨1185605, by rfl⟩ : syracuseStep 1580807 = 2371211) B2371211
theorem B1580815 : Blo 1580488 1580815 := bstep (se 1 (by rfl) ⟨1185611, by rfl⟩ : syracuseStep 1580815 = 2371223) B2371223
theorem B9002785 : Blo 1580488 9002785 := bstep (se 2 (by rfl) ⟨3376044, by rfl⟩ : syracuseStep 9002785 = 6752089) B6752089
theorem B19234597 : Blo 1580488 19234597 := bstep (se 4 (by rfl) ⟨1803243, by rfl⟩ : syracuseStep 19234597 = 3606487) B3606487
theorem B17342257 : Blo 1580488 17342257 := bstep (se 2 (by rfl) ⟨6503346, by rfl⟩ : syracuseStep 17342257 = 13006693) B13006693
theorem B1580859 : Blo 1580488 1580859 := bstep (se 1 (by rfl) ⟨1185644, by rfl⟩ : syracuseStep 1580859 = 2371289) B2371289
theorem B9011033 : Blo 1580488 9011033 := bstep (se 2 (by rfl) ⟨3379137, by rfl⟩ : syracuseStep 9011033 = 6758275) B6758275
theorem B10133363 : Blo 1580488 10133363 := bstep (se 1 (by rfl) ⟨7600022, by rfl⟩ : syracuseStep 10133363 = 15200045) B15200045
theorem B1580935 : Blo 1580488 1580935 := bstep (se 1 (by rfl) ⟨1185701, by rfl⟩ : syracuseStep 1580935 = 2371403) B2371403
theorem B1580943 : Blo 1580488 1580943 := bstep (se 1 (by rfl) ⟨1185707, by rfl⟩ : syracuseStep 1580943 = 2371415) B2371415
theorem B1580987 : Blo 1580488 1580987 := bstep (se 1 (by rfl) ⟨1185740, by rfl⟩ : syracuseStep 1580987 = 2371481) B2371481
theorem B1581095 : Blo 1580488 1581095 := bstep (se 1 (by rfl) ⟨1185821, by rfl⟩ : syracuseStep 1581095 = 2371643) B2371643
theorem B1581135 : Blo 1580488 1581135 := bstep (se 1 (by rfl) ⟨1185851, by rfl⟩ : syracuseStep 1581135 = 2371703) B2371703
theorem B1581151 : Blo 1580488 1581151 := bstep (se 1 (by rfl) ⟨1185863, by rfl⟩ : syracuseStep 1581151 = 2371727) B2371727
theorem B1581179 : Blo 1580488 1581179 := bstep (se 1 (by rfl) ⟨1185884, by rfl⟩ : syracuseStep 1581179 = 2371769) B2371769
theorem B1581231 : Blo 1580488 1581231 := bstep (se 1 (by rfl) ⟨1185923, by rfl⟩ : syracuseStep 1581231 = 2371847) B2371847
theorem B1581255 : Blo 1580488 1581255 := bstep (se 1 (by rfl) ⟨1185941, by rfl⟩ : syracuseStep 1581255 = 2371883) B2371883
theorem B1581275 : Blo 1580488 1581275 := bstep (se 1 (by rfl) ⟨1185956, by rfl⟩ : syracuseStep 1581275 = 2371913) B2371913
theorem B1581351 : Blo 1580488 1581351 := bstep (se 1 (by rfl) ⟨1186013, by rfl⟩ : syracuseStep 1581351 = 2372027) B2372027
theorem B1581391 : Blo 1580488 1581391 := bstep (se 1 (by rfl) ⟨1186043, by rfl⟩ : syracuseStep 1581391 = 2372087) B2372087
theorem B1581407 : Blo 1580488 1581407 := bstep (se 1 (by rfl) ⟨1186055, by rfl⟩ : syracuseStep 1581407 = 2372111) B2372111
theorem B1581435 : Blo 1580488 1581435 := bstep (se 1 (by rfl) ⟨1186076, by rfl⟩ : syracuseStep 1581435 = 2372153) B2372153
theorem B1581487 : Blo 1580488 1581487 := bstep (se 1 (by rfl) ⟨1186115, by rfl⟩ : syracuseStep 1581487 = 2372231) B2372231
theorem B1581511 : Blo 1580488 1581511 := bstep (se 1 (by rfl) ⟨1186133, by rfl⟩ : syracuseStep 1581511 = 2372267) B2372267
theorem B1581531 : Blo 1580488 1581531 := bstep (se 1 (by rfl) ⟨1186148, by rfl⟩ : syracuseStep 1581531 = 2372297) B2372297
theorem B3801587 : Blo 1580488 3801587 := bstep (se 1 (by rfl) ⟨2851190, by rfl⟩ : syracuseStep 3801587 = 5702381) B5702381
theorem B17105417 : Blo 1580488 17105417 := bstep (se 2 (by rfl) ⟨6414531, by rfl⟩ : syracuseStep 17105417 = 12829063) B12829063
theorem B1778215 : Blo 1580488 1778215 := bstep (se 1 (by rfl) ⟨1333661, by rfl⟩ : syracuseStep 1778215 = 2667323) B2667323
theorem B1581607 : Blo 1580488 1581607 := bstep (se 1 (by rfl) ⟨1186205, by rfl⟩ : syracuseStep 1581607 = 2372411) B2372411
theorem B5702183 : Blo 1580488 5702183 := bstep (se 1 (by rfl) ⟨4276637, by rfl⟩ : syracuseStep 5702183 = 8553275) B8553275
theorem B1581647 : Blo 1580488 1581647 := bstep (se 1 (by rfl) ⟨1186235, by rfl⟩ : syracuseStep 1581647 = 2372471) B2372471
theorem B1581663 : Blo 1580488 1581663 := bstep (se 1 (by rfl) ⟨1186247, by rfl⟩ : syracuseStep 1581663 = 2372495) B2372495
theorem B1581691 : Blo 1580488 1581691 := bstep (se 1 (by rfl) ⟨1186268, by rfl⟩ : syracuseStep 1581691 = 2372537) B2372537
theorem B12829319 : Blo 1580488 12829319 := bstep (se 1 (by rfl) ⟨9621989, by rfl⟩ : syracuseStep 12829319 = 19243979) B19243979
theorem B1581743 : Blo 1580488 1581743 := bstep (se 1 (by rfl) ⟨1186307, by rfl⟩ : syracuseStep 1581743 = 2372615) B2372615
theorem B6415037 : Blo 1580488 6415037 := bstep (se 3 (by rfl) ⟨1202819, by rfl⟩ : syracuseStep 6415037 = 2405639) B2405639
theorem B1581767 : Blo 1580488 1581767 := bstep (se 1 (by rfl) ⟨1186325, by rfl⟩ : syracuseStep 1581767 = 2372651) B2372651
theorem B1581787 : Blo 1580488 1581787 := bstep (se 1 (by rfl) ⟨1186340, by rfl⟩ : syracuseStep 1581787 = 2372681) B2372681
theorem B6759197 : Blo 1580488 6759197 := bstep (se 3 (by rfl) ⟨1267349, by rfl⟩ : syracuseStep 6759197 = 2534699) B2534699
theorem B1581863 : Blo 1580488 1581863 := bstep (se 1 (by rfl) ⟨1186397, by rfl⟩ : syracuseStep 1581863 = 2372795) B2372795
theorem B3556169 : Blo 1580488 3556169 := bstep (se 2 (by rfl) ⟨1333563, by rfl⟩ : syracuseStep 3556169 = 2667127) B2667127
theorem B1581903 : Blo 1580488 1581903 := bstep (se 1 (by rfl) ⟨1186427, by rfl⟩ : syracuseStep 1581903 = 2372855) B2372855
theorem B1581919 : Blo 1580488 1581919 := bstep (se 1 (by rfl) ⟨1186439, by rfl⟩ : syracuseStep 1581919 = 2372879) B2372879
theorem B10961771 : Blo 1580488 10961771 := bstep (se 1 (by rfl) ⟨8221328, by rfl⟩ : syracuseStep 10961771 = 16442657) B16442657
theorem B5063543 : Blo 1580488 5063543 := bstep (se 1 (by rfl) ⟨3797657, by rfl⟩ : syracuseStep 5063543 = 7595315) B7595315
theorem B6005623 : Blo 1580488 6005623 := bstep (se 1 (by rfl) ⟨4504217, by rfl⟩ : syracuseStep 6005623 = 9008435) B9008435
theorem B1581947 : Blo 1580488 1581947 := bstep (se 1 (by rfl) ⟨1186460, by rfl⟩ : syracuseStep 1581947 = 2372921) B2372921
theorem B2532239 : Blo 1580488 2532239 := bstep (se 1 (by rfl) ⟨1899179, by rfl⟩ : syracuseStep 2532239 = 3798359) B3798359
theorem B5407663 : Blo 1580488 5407663 := bstep (se 1 (by rfl) ⟨4055747, by rfl⟩ : syracuseStep 5407663 = 8111495) B8111495
theorem B1581999 : Blo 1580488 1581999 := bstep (se 1 (by rfl) ⟨1186499, by rfl⟩ : syracuseStep 1581999 = 2372999) B2372999
theorem B1582023 : Blo 1580488 1582023 := bstep (se 1 (by rfl) ⟨1186517, by rfl⟩ : syracuseStep 1582023 = 2373035) B2373035
theorem B1582043 : Blo 1580488 1582043 := bstep (se 1 (by rfl) ⟨1186532, by rfl⟩ : syracuseStep 1582043 = 2373065) B2373065
theorem B14435293 : Blo 1580488 14435293 := bstep (se 3 (by rfl) ⟨2706617, by rfl⟩ : syracuseStep 14435293 = 5413235) B5413235
theorem B16221185 : Blo 1580488 16221185 := bstep (se 2 (by rfl) ⟨6082944, by rfl⟩ : syracuseStep 16221185 = 12165889) B12165889
theorem B45622277 : Blo 1580488 45622277 := bstep (se 4 (by rfl) ⟨4277088, by rfl⟩ : syracuseStep 45622277 = 8554177) B8554177
theorem B1582119 : Blo 1580488 1582119 := bstep (se 1 (by rfl) ⟨1186589, by rfl⟩ : syracuseStep 1582119 = 2373179) B2373179
theorem B15205427 : Blo 1580488 15205427 := bstep (se 1 (by rfl) ⟨11404070, by rfl⟩ : syracuseStep 15205427 = 22808141) B22808141
theorem B1582159 : Blo 1580488 1582159 := bstep (se 1 (by rfl) ⟨1186619, by rfl⟩ : syracuseStep 1582159 = 2373239) B2373239
theorem B1582175 : Blo 1580488 1582175 := bstep (se 1 (by rfl) ⟨1186631, by rfl⟩ : syracuseStep 1582175 = 2373263) B2373263
theorem B1582203 : Blo 1580488 1582203 := bstep (se 1 (by rfl) ⟨1186652, by rfl⟩ : syracuseStep 1582203 = 2373305) B2373305
theorem B5334173 : Blo 1580488 5334173 := bstep (se 3 (by rfl) ⟨1000157, by rfl⟩ : syracuseStep 5334173 = 2000315) B2000315
theorem B1582255 : Blo 1580488 1582255 := bstep (se 1 (by rfl) ⟨1186691, by rfl⟩ : syracuseStep 1582255 = 2373383) B2373383
theorem B1582279 : Blo 1580488 1582279 := bstep (se 1 (by rfl) ⟨1186709, by rfl⟩ : syracuseStep 1582279 = 2373419) B2373419
theorem B1582299 : Blo 1580488 1582299 := bstep (se 1 (by rfl) ⟨1186724, by rfl⟩ : syracuseStep 1582299 = 2373449) B2373449
theorem B1582375 : Blo 1580488 1582375 := bstep (se 1 (by rfl) ⟨1186781, by rfl⟩ : syracuseStep 1582375 = 2373563) B2373563
theorem B1582415 : Blo 1580488 1582415 := bstep (se 1 (by rfl) ⟨1186811, by rfl⟩ : syracuseStep 1582415 = 2373623) B2373623
theorem B1582431 : Blo 1580488 1582431 := bstep (se 1 (by rfl) ⟨1186823, by rfl⟩ : syracuseStep 1582431 = 2373647) B2373647
theorem B2532713 : Blo 1580488 2532713 := bstep (se 2 (by rfl) ⟨949767, by rfl⟩ : syracuseStep 2532713 = 1899535) B1899535
theorem B18023795 : Blo 1580488 18023795 := bstep (se 1 (by rfl) ⟨13517846, by rfl⟩ : syracuseStep 18023795 = 27035693) B27035693
theorem B1582459 : Blo 1580488 1582459 := bstep (se 1 (by rfl) ⟨1186844, by rfl⟩ : syracuseStep 1582459 = 2373689) B2373689
theorem B2532751 : Blo 1580488 2532751 := bstep (se 1 (by rfl) ⟨1899563, by rfl⟩ : syracuseStep 2532751 = 3799127) B3799127
theorem B10135003 : Blo 1580488 10135003 := bstep (se 1 (by rfl) ⟨7601252, by rfl⟩ : syracuseStep 10135003 = 15202505) B15202505
theorem B3556961 : Blo 1580488 3556961 := bstep (se 2 (by rfl) ⟨1333860, by rfl⟩ : syracuseStep 3556961 = 2667721) B2667721
theorem B5334713 : Blo 1580488 5334713 := bstep (se 2 (by rfl) ⟨2000517, by rfl⟩ : syracuseStep 5334713 = 4001035) B4001035
theorem B11396807 : Blo 1580488 11396807 := bstep (se 1 (by rfl) ⟨8547605, by rfl⟩ : syracuseStep 11396807 = 17095211) B17095211
theorem B17327915 : Blo 1580488 17327915 := bstep (se 1 (by rfl) ⟨12995936, by rfl⟩ : syracuseStep 17327915 = 25991873) B25991873
theorem B6006595 : Blo 1580488 6006595 := bstep (se 1 (by rfl) ⟨4504946, by rfl⟩ : syracuseStep 6006595 = 9009893) B9009893
theorem B19769183 : Blo 1580488 19769183 := bstep (se 1 (by rfl) ⟨14826887, by rfl⟩ : syracuseStep 19769183 = 29653775) B29653775
theorem B10127213 : Blo 1580488 10127213 := bstep (se 3 (by rfl) ⟨1898852, by rfl⟩ : syracuseStep 10127213 = 3797705) B3797705
theorem B3557303 : Blo 1580488 3557303 := bstep (se 1 (by rfl) ⟨2667977, by rfl⟩ : syracuseStep 3557303 = 5335955) B5335955
theorem B6006899 : Blo 1580488 6006899 := bstep (se 1 (by rfl) ⟨4505174, by rfl⟩ : syracuseStep 6006899 = 9010349) B9010349
theorem B2001019 : Blo 1580488 2001019 := bstep (se 1 (by rfl) ⟨1500764, by rfl⟩ : syracuseStep 2001019 = 3001529) B3001529
theorem B1779835 : Blo 1580488 1779835 := bstep (se 1 (by rfl) ⟨1334876, by rfl⟩ : syracuseStep 1779835 = 2669753) B2669753
theorem B5335307 : Blo 1580488 5335307 := bstep (se 1 (by rfl) ⟨4001480, by rfl⟩ : syracuseStep 5335307 = 8002961) B8002961
theorem B12003713 : Blo 1580488 12003713 := bstep (se 2 (by rfl) ⟨4501392, by rfl⟩ : syracuseStep 12003713 = 9002785) B9002785
theorem B3557897 : Blo 1580488 3557897 := bstep (se 2 (by rfl) ⟨1334211, by rfl⟩ : syracuseStep 3557897 = 2668423) B2668423
theorem B5335577 : Blo 1580488 5335577 := bstep (se 2 (by rfl) ⟨2000841, by rfl⟩ : syracuseStep 5335577 = 4001683) B4001683
theorem B6007355 : Blo 1580488 6007355 := bstep (se 1 (by rfl) ⟨4505516, by rfl⟩ : syracuseStep 6007355 = 9011033) B9011033
theorem B3205831 : Blo 1580488 3205831 := bstep (se 1 (by rfl) ⟨2404373, by rfl⟩ : syracuseStep 3205831 = 4808747) B4808747
theorem B3001043 : Blo 1580488 3001043 := bstep (se 1 (by rfl) ⟨2250782, by rfl⟩ : syracuseStep 3001043 = 4501565) B4501565
theorem B5483219 : Blo 1580488 5483219 := bstep (se 1 (by rfl) ⟨4112414, by rfl⟩ : syracuseStep 5483219 = 8224829) B8224829
theorem B3558239 : Blo 1580488 3558239 := bstep (se 1 (by rfl) ⟨2668679, by rfl⟩ : syracuseStep 3558239 = 5337359) B5337359
theorem B3558419 : Blo 1580488 3558419 := bstep (se 1 (by rfl) ⟨2668814, by rfl⟩ : syracuseStep 3558419 = 5337629) B5337629
theorem B4001015 : Blo 1580488 4001015 := bstep (se 1 (by rfl) ⟨3000761, by rfl⟩ : syracuseStep 4001015 = 6001523) B6001523
theorem B2370809 : Blo 1580488 2370809 := bstep (se 2 (by rfl) ⟨889053, by rfl⟩ : syracuseStep 2370809 = 1778107) B1778107
theorem B3001673 : Blo 1580488 3001673 := bstep (se 2 (by rfl) ⟨1125627, by rfl⟩ : syracuseStep 3001673 = 2251255) B2251255
theorem B2370911 : Blo 1580488 2370911 := bstep (se 1 (by rfl) ⟨1778183, by rfl⟩ : syracuseStep 2370911 = 3556367) B3556367
theorem B3558761 : Blo 1580488 3558761 := bstep (se 2 (by rfl) ⟨1334535, by rfl⟩ : syracuseStep 3558761 = 2669071) B2669071
theorem B2370923 : Blo 1580488 2370923 := bstep (se 1 (by rfl) ⟨1778192, by rfl⟩ : syracuseStep 2370923 = 3556385) B3556385
theorem B2371151 : Blo 1580488 2371151 := bstep (se 1 (by rfl) ⟨1778363, by rfl⟩ : syracuseStep 2371151 = 3556727) B3556727
theorem B5336711 : Blo 1580488 5336711 := bstep (se 1 (by rfl) ⟨4002533, by rfl⟩ : syracuseStep 5336711 = 8005067) B8005067
theorem B10268299 : Blo 1580488 10268299 := bstep (se 1 (by rfl) ⟨7701224, by rfl⟩ : syracuseStep 10268299 = 15402449) B15402449
theorem B5066425 : Blo 1580488 5066425 := bstep (se 2 (by rfl) ⟨1899909, by rfl⟩ : syracuseStep 5066425 = 3799819) B3799819
theorem B5336765 : Blo 1580488 5336765 := bstep (se 3 (by rfl) ⟨1000643, by rfl⟩ : syracuseStep 5336765 = 2001287) B2001287
theorem B2371271 : Blo 1580488 2371271 := bstep (se 1 (by rfl) ⟨1778453, by rfl⟩ : syracuseStep 2371271 = 3556907) B3556907
theorem B22802141 : Blo 1580488 22802141 := bstep (se 3 (by rfl) ⟨4275401, by rfl⟩ : syracuseStep 22802141 = 8550803) B8550803
theorem B3657545 : Blo 1580488 3657545 := bstep (se 2 (by rfl) ⟨1371579, by rfl⟩ : syracuseStep 3657545 = 2743159) B2743159
theorem B5336927 : Blo 1580488 5336927 := bstep (se 1 (by rfl) ⟨4002695, by rfl⟩ : syracuseStep 5336927 = 8005391) B8005391
theorem B2371433 : Blo 1580488 2371433 := bstep (se 2 (by rfl) ⟨889287, by rfl⟩ : syracuseStep 2371433 = 1778575) B1778575
theorem B5066657 : Blo 1580488 5066657 := bstep (se 2 (by rfl) ⟨1899996, by rfl⟩ : syracuseStep 5066657 = 3799993) B3799993
theorem B2371511 : Blo 1580488 2371511 := bstep (se 1 (by rfl) ⟨1778633, by rfl⟩ : syracuseStep 2371511 = 3557267) B3557267
theorem B3559355 : Blo 1580488 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B2371547 : Blo 1580488 2371547 := bstep (se 1 (by rfl) ⟨1778660, by rfl⟩ : syracuseStep 2371547 = 3557321) B3557321
theorem B5337089 : Blo 1580488 5337089 := bstep (se 2 (by rfl) ⟨2001408, by rfl⟩ : syracuseStep 5337089 = 4002817) B4002817
theorem B3559481 : Blo 1580488 3559481 := bstep (se 2 (by rfl) ⟨1334805, by rfl⟩ : syracuseStep 3559481 = 2669611) B2669611
theorem B13504589 : Blo 1580488 13504589 := bstep (se 3 (by rfl) ⟨2532110, by rfl⟩ : syracuseStep 13504589 = 5064221) B5064221
theorem B3002447 : Blo 1580488 3002447 := bstep (se 1 (by rfl) ⟨2251835, by rfl⟩ : syracuseStep 3002447 = 4503671) B4503671
theorem B6410639 : Blo 1580488 6410639 := bstep (se 1 (by rfl) ⟨4807979, by rfl⟩ : syracuseStep 6410639 = 9615959) B9615959
theorem B3559823 : Blo 1580488 3559823 := bstep (se 1 (by rfl) ⟨2669867, by rfl⟩ : syracuseStep 3559823 = 5339735) B5339735
theorem B2372015 : Blo 1580488 2372015 := bstep (se 1 (by rfl) ⟨1779011, by rfl⟩ : syracuseStep 2372015 = 3558023) B3558023
theorem B3797513 : Blo 1580488 3797513 := bstep (se 2 (by rfl) ⟨1424067, by rfl⟩ : syracuseStep 3797513 = 2848135) B2848135
theorem B2372105 : Blo 1580488 2372105 := bstep (se 2 (by rfl) ⟨889539, by rfl⟩ : syracuseStep 2372105 = 1779079) B1779079
theorem B2372135 : Blo 1580488 2372135 := bstep (se 1 (by rfl) ⟨1779101, by rfl⟩ : syracuseStep 2372135 = 3558203) B3558203
theorem B6001249 : Blo 1580488 6001249 := bstep (se 2 (by rfl) ⟨2250468, by rfl⟩ : syracuseStep 6001249 = 4500937) B4500937
theorem B2372219 : Blo 1580488 2372219 := bstep (se 1 (by rfl) ⟨1779164, by rfl⟩ : syracuseStep 2372219 = 3558329) B3558329
theorem B4002443 : Blo 1580488 4002443 := bstep (se 1 (by rfl) ⟨3001832, by rfl⟩ : syracuseStep 4002443 = 6003665) B6003665
theorem B6410963 : Blo 1580488 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B3560147 : Blo 1580488 3560147 := bstep (se 1 (by rfl) ⟨2670110, by rfl⟩ : syracuseStep 3560147 = 5340221) B5340221
theorem B2372345 : Blo 1580488 2372345 := bstep (se 2 (by rfl) ⟨889629, by rfl⟩ : syracuseStep 2372345 = 1779259) B1779259
theorem B5337899 : Blo 1580488 5337899 := bstep (se 1 (by rfl) ⟨4003424, by rfl⟩ : syracuseStep 5337899 = 8006849) B8006849
theorem B4002655 : Blo 1580488 4002655 := bstep (se 1 (by rfl) ⟨3001991, by rfl⟩ : syracuseStep 4002655 = 6003983) B6003983
theorem B2372447 : Blo 1580488 2372447 := bstep (se 1 (by rfl) ⟨1779335, by rfl⟩ : syracuseStep 2372447 = 3558671) B3558671
theorem B2372459 : Blo 1580488 2372459 := bstep (se 1 (by rfl) ⟨1779344, by rfl⟩ : syracuseStep 2372459 = 3558689) B3558689
theorem B8008631 : Blo 1580488 8008631 := bstep (se 1 (by rfl) ⟨6006473, by rfl⟩ : syracuseStep 8008631 = 12012947) B12012947
theorem B2667451 : Blo 1580488 2667451 := bstep (se 1 (by rfl) ⟨2000588, by rfl⟩ : syracuseStep 2667451 = 4001177) B4001177
theorem B2667559 : Blo 1580488 2667559 := bstep (se 1 (by rfl) ⟨2000669, by rfl⟩ : syracuseStep 2667559 = 4001339) B4001339
theorem B25646129 : Blo 1580488 25646129 := bstep (se 2 (by rfl) ⟨9617298, by rfl⟩ : syracuseStep 25646129 = 19234597) B19234597
theorem B18043955 : Blo 1580488 18043955 := bstep (se 1 (by rfl) ⟨13532966, by rfl⟩ : syracuseStep 18043955 = 27065933) B27065933
theorem B6001721 : Blo 1580488 6001721 := bstep (se 2 (by rfl) ⟨2250645, by rfl⟩ : syracuseStep 6001721 = 4501291) B4501291
theorem B5338169 : Blo 1580488 5338169 := bstep (se 2 (by rfl) ⟨2001813, by rfl⟩ : syracuseStep 5338169 = 4003627) B4003627
theorem B23123009 : Blo 1580488 23123009 := bstep (se 2 (by rfl) ⟨8671128, by rfl⟩ : syracuseStep 23123009 = 17342257) B17342257
theorem B4273231 : Blo 1580488 4273231 := bstep (se 1 (by rfl) ⟨3204923, by rfl⟩ : syracuseStep 4273231 = 6409847) B6409847
theorem B2372687 : Blo 1580488 2372687 := bstep (se 1 (by rfl) ⟨1779515, by rfl⟩ : syracuseStep 2372687 = 3559031) B3559031
theorem B2372807 : Blo 1580488 2372807 := bstep (se 1 (by rfl) ⟨1779605, by rfl⟩ : syracuseStep 2372807 = 3559211) B3559211
theorem B6755575 : Blo 1580488 6755575 := bstep (se 1 (by rfl) ⟨5066681, by rfl⟩ : syracuseStep 6755575 = 10133363) B10133363
theorem B10130777 : Blo 1580488 10130777 := bstep (se 2 (by rfl) ⟨3799041, by rfl⟩ : syracuseStep 10130777 = 7598083) B7598083
theorem B2372969 : Blo 1580488 2372969 := bstep (se 2 (by rfl) ⟨889863, by rfl⟩ : syracuseStep 2372969 = 1779727) B1779727
theorem B2667883 : Blo 1580488 2667883 := bstep (se 1 (by rfl) ⟨2000912, by rfl⟩ : syracuseStep 2667883 = 4001825) B4001825
theorem B5338493 : Blo 1580488 5338493 := bstep (se 3 (by rfl) ⟨1000967, by rfl⟩ : syracuseStep 5338493 = 2001935) B2001935
theorem B8115599 : Blo 1580488 8115599 := bstep (se 1 (by rfl) ⟨6086699, by rfl⟩ : syracuseStep 8115599 = 12173399) B12173399
theorem B24352163 : Blo 1580488 24352163 := bstep (se 1 (by rfl) ⟨18264122, by rfl⟩ : syracuseStep 24352163 = 36528245) B36528245
theorem B15201701 : Blo 1580488 15201701 := bstep (se 4 (by rfl) ⟨1425159, by rfl⟩ : syracuseStep 15201701 = 2850319) B2850319
theorem B10139053 : Blo 1580488 10139053 := bstep (se 3 (by rfl) ⟨1901072, by rfl⟩ : syracuseStep 10139053 = 3802145) B3802145
theorem B2373047 : Blo 1580488 2373047 := bstep (se 1 (by rfl) ⟨1779785, by rfl⟩ : syracuseStep 2373047 = 3559571) B3559571
theorem B77960657 : Blo 1580488 77960657 := bstep (se 2 (by rfl) ⟨29235246, by rfl⟩ : syracuseStep 77960657 = 58470493) B58470493
theorem B17102299 : Blo 1580488 17102299 := bstep (se 1 (by rfl) ⟨12826724, by rfl⟩ : syracuseStep 17102299 = 25653449) B25653449
theorem B2373083 : Blo 1580488 2373083 := bstep (se 1 (by rfl) ⟨1779812, by rfl⟩ : syracuseStep 2373083 = 3559625) B3559625
theorem B1603195 : Blo 1580488 1603195 := bstep (se 1 (by rfl) ⟨1202396, by rfl⟩ : syracuseStep 1603195 = 2404793) B2404793
theorem B5338763 : Blo 1580488 5338763 := bstep (se 1 (by rfl) ⟨4004072, by rfl⟩ : syracuseStep 5338763 = 8008145) B8008145
theorem B10819271 : Blo 1580488 10819271 := bstep (se 1 (by rfl) ⟨8114453, by rfl⟩ : syracuseStep 10819271 = 16228907) B16228907
theorem B4503239 : Blo 1580488 4503239 := bstep (se 1 (by rfl) ⟨3377429, by rfl⟩ : syracuseStep 4503239 = 6754859) B6754859
theorem B3004103 : Blo 1580488 3004103 := bstep (se 1 (by rfl) ⟨2253077, by rfl⟩ : syracuseStep 3004103 = 4506155) B4506155
theorem B4003577 : Blo 1580488 4003577 := bstep (se 2 (by rfl) ⟨1501341, by rfl⟩ : syracuseStep 4003577 = 3002683) B3002683
theorem B14423903 : Blo 1580488 14423903 := bstep (se 1 (by rfl) ⟨10817927, by rfl⟩ : syracuseStep 14423903 = 21635855) B21635855
theorem B19240865 : Blo 1580488 19240865 := bstep (se 2 (by rfl) ⟨7215324, by rfl⟩ : syracuseStep 19240865 = 14430649) B14430649
theorem B2373551 : Blo 1580488 2373551 := bstep (se 1 (by rfl) ⟨1780163, by rfl⟩ : syracuseStep 2373551 = 3560327) B3560327
theorem B2373641 : Blo 1580488 2373641 := bstep (se 2 (by rfl) ⟨890115, by rfl⟩ : syracuseStep 2373641 = 1780231) B1780231
theorem B6002707 : Blo 1580488 6002707 := bstep (se 1 (by rfl) ⟨4502030, by rfl⟩ : syracuseStep 6002707 = 9004061) B9004061
theorem B2373671 : Blo 1580488 2373671 := bstep (se 1 (by rfl) ⟨1780253, by rfl⟩ : syracuseStep 2373671 = 3560507) B3560507
theorem B4806713 : Blo 1580488 4806713 := bstep (se 2 (by rfl) ⟨1802517, by rfl⟩ : syracuseStep 4806713 = 3605035) B3605035
theorem B5069117 : Blo 1580488 5069117 := bstep (se 3 (by rfl) ⟨950459, by rfl⟩ : syracuseStep 5069117 = 1900919) B1900919
theorem B4274537 : Blo 1580488 4274537 := bstep (se 2 (by rfl) ⟨1602951, by rfl⟩ : syracuseStep 4274537 = 3205903) B3205903
theorem B13515113 : Blo 1580488 13515113 := bstep (se 2 (by rfl) ⟨5068167, by rfl⟩ : syracuseStep 13515113 = 10136335) B10136335
theorem B8010089 : Blo 1580488 8010089 := bstep (se 2 (by rfl) ⟨3003783, by rfl⟩ : syracuseStep 8010089 = 6007567) B6007567
theorem B4004225 : Blo 1580488 4004225 := bstep (se 2 (by rfl) ⟨1501584, by rfl⟩ : syracuseStep 4004225 = 3003169) B3003169
theorem B2668943 : Blo 1580488 2668943 := bstep (se 1 (by rfl) ⟨2001707, by rfl⟩ : syracuseStep 2668943 = 4003415) B4003415
theorem B5339681 : Blo 1580488 5339681 := bstep (se 2 (by rfl) ⟨2002380, by rfl⟩ : syracuseStep 5339681 = 4004761) B4004761
theorem B2669179 : Blo 1580488 2669179 := bstep (se 1 (by rfl) ⟨2001884, by rfl⟩ : syracuseStep 2669179 = 4003769) B4003769
theorem B5339897 : Blo 1580488 5339897 := bstep (se 2 (by rfl) ⟨2002461, by rfl⟩ : syracuseStep 5339897 = 4004923) B4004923
theorem B9616157 : Blo 1580488 9616157 := bstep (se 3 (by rfl) ⟨1803029, by rfl⟩ : syracuseStep 9616157 = 3606059) B3606059
theorem B4504481 : Blo 1580488 4504481 := bstep (se 2 (by rfl) ⟨1689180, by rfl⟩ : syracuseStep 4504481 = 3378361) B3378361
theorem B2251739 : Blo 1580488 2251739 := bstep (se 1 (by rfl) ⟨1688804, by rfl⟩ : syracuseStep 2251739 = 3377609) B3377609
theorem B22805489 : Blo 1580488 22805489 := bstep (se 2 (by rfl) ⟨8552058, by rfl⟩ : syracuseStep 22805489 = 17104117) B17104117
theorem B4807687 : Blo 1580488 4807687 := bstep (se 1 (by rfl) ⟨3605765, by rfl⟩ : syracuseStep 4807687 = 7211531) B7211531
theorem B5340167 : Blo 1580488 5340167 := bstep (se 1 (by rfl) ⟨4005125, by rfl⟩ : syracuseStep 5340167 = 8010251) B8010251
theorem B5340275 : Blo 1580488 5340275 := bstep (se 1 (by rfl) ⟨4005206, by rfl⟩ : syracuseStep 5340275 = 8010413) B8010413
theorem B4005035 : Blo 1580488 4005035 := bstep (se 1 (by rfl) ⟨3003776, by rfl⟩ : syracuseStep 4005035 = 6007553) B6007553
theorem B12016835 : Blo 1580488 12016835 := bstep (se 1 (by rfl) ⟨9012626, by rfl⟩ : syracuseStep 12016835 = 18025253) B18025253
theorem B17333527 : Blo 1580488 17333527 := bstep (se 1 (by rfl) ⟨13000145, by rfl⟩ : syracuseStep 17333527 = 26000291) B26000291
theorem B5340545 : Blo 1580488 5340545 := bstep (se 2 (by rfl) ⟨2002704, by rfl⟩ : syracuseStep 5340545 = 4005409) B4005409
theorem B51289523 : Blo 1580488 51289523 := bstep (se 1 (by rfl) ⟨38467142, by rfl⟩ : syracuseStep 51289523 = 76934285) B76934285
theorem B1580507 : Blo 1580488 1580507 := bstep (se 1 (by rfl) ⟨1185380, by rfl⟩ : syracuseStep 1580507 = 2370761) B2370761
theorem B2670043 : Blo 1580488 2670043 := bstep (se 1 (by rfl) ⟨2002532, by rfl⟩ : syracuseStep 2670043 = 4005065) B4005065
theorem B1580583 : Blo 1580488 1580583 := bstep (se 1 (by rfl) ⟨1185437, by rfl⟩ : syracuseStep 1580583 = 2370875) B2370875
theorem B1580623 : Blo 1580488 1580623 := bstep (se 1 (by rfl) ⟨1185467, by rfl⟩ : syracuseStep 1580623 = 2370935) B2370935
theorem B1580639 : Blo 1580488 1580639 := bstep (se 1 (by rfl) ⟨1185479, by rfl⟩ : syracuseStep 1580639 = 2370959) B2370959
theorem B20258423 : Blo 1580488 20258423 := bstep (se 1 (by rfl) ⟨15193817, by rfl⟩ : syracuseStep 20258423 = 30387635) B30387635
theorem B1580667 : Blo 1580488 1580667 := bstep (se 1 (by rfl) ⟨1185500, by rfl⟩ : syracuseStep 1580667 = 2371001) B2371001
theorem B5701259 : Blo 1580488 5701259 := bstep (se 1 (by rfl) ⟨4275944, by rfl⟩ : syracuseStep 5701259 = 8551889) B8551889
theorem B1580719 : Blo 1580488 1580719 := bstep (se 1 (by rfl) ⟨1185539, by rfl⟩ : syracuseStep 1580719 = 2371079) B2371079
theorem B1580743 : Blo 1580488 1580743 := bstep (se 1 (by rfl) ⟨1185557, by rfl⟩ : syracuseStep 1580743 = 2371115) B2371115
theorem B6004439 : Blo 1580488 6004439 := bstep (se 1 (by rfl) ⟨4503329, by rfl⟩ : syracuseStep 6004439 = 9006659) B9006659
theorem B1580763 : Blo 1580488 1580763 := bstep (se 1 (by rfl) ⟨1185572, by rfl⟩ : syracuseStep 1580763 = 2371145) B2371145
theorem B1580839 : Blo 1580488 1580839 := bstep (se 1 (by rfl) ⟨1185629, by rfl⟩ : syracuseStep 1580839 = 2371259) B2371259
theorem B1580879 : Blo 1580488 1580879 := bstep (se 1 (by rfl) ⟨1185659, by rfl⟩ : syracuseStep 1580879 = 2371319) B2371319
theorem B1580895 : Blo 1580488 1580895 := bstep (se 1 (by rfl) ⟨1185671, by rfl⟩ : syracuseStep 1580895 = 2371343) B2371343
theorem B2137961 : Blo 1580488 2137961 := bstep (se 2 (by rfl) ⟨801735, by rfl⟩ : syracuseStep 2137961 = 1603471) B1603471
theorem B8003447 : Blo 1580488 8003447 := bstep (se 1 (by rfl) ⟨6002585, by rfl⟩ : syracuseStep 8003447 = 12005171) B12005171
theorem B1580923 : Blo 1580488 1580923 := bstep (se 1 (by rfl) ⟨1185692, by rfl⟩ : syracuseStep 1580923 = 2371385) B2371385
theorem B1580975 : Blo 1580488 1580975 := bstep (se 1 (by rfl) ⟨1185731, by rfl⟩ : syracuseStep 1580975 = 2371463) B2371463
theorem B1925047 : Blo 1580488 1925047 := bstep (se 1 (by rfl) ⟨1443785, by rfl⟩ : syracuseStep 1925047 = 2887571) B2887571
theorem B1580999 : Blo 1580488 1580999 := bstep (se 1 (by rfl) ⟨1185749, by rfl⟩ : syracuseStep 1580999 = 2371499) B2371499
theorem B1581019 : Blo 1580488 1581019 := bstep (se 1 (by rfl) ⟨1185764, by rfl⟩ : syracuseStep 1581019 = 2371529) B2371529
theorem B8003609 : Blo 1580488 8003609 := bstep (se 2 (by rfl) ⟨3001353, by rfl⟩ : syracuseStep 8003609 = 6002707) B6002707
theorem B9003059 : Blo 1580488 9003059 := bstep (se 1 (by rfl) ⟨6752294, by rfl⟩ : syracuseStep 9003059 = 13504589) B13504589
theorem B61661357 : Blo 1580488 61661357 := bstep (se 3 (by rfl) ⟨11561504, by rfl⟩ : syracuseStep 61661357 = 23123009) B23123009
theorem B1581343 : Blo 1580488 1581343 := bstep (se 1 (by rfl) ⟨1186007, by rfl⟩ : syracuseStep 1581343 = 2372015) B2372015
theorem B2531675 : Blo 1580488 2531675 := bstep (se 1 (by rfl) ⟨1898756, by rfl⟩ : syracuseStep 2531675 = 3797513) B3797513
theorem B1581403 : Blo 1580488 1581403 := bstep (se 1 (by rfl) ⟨1186052, by rfl⟩ : syracuseStep 1581403 = 2372105) B2372105
theorem B11403611 : Blo 1580488 11403611 := bstep (se 1 (by rfl) ⟨8552708, by rfl⟩ : syracuseStep 11403611 = 17105417) B17105417
theorem B1581423 : Blo 1580488 1581423 := bstep (se 1 (by rfl) ⟨1186067, by rfl⟩ : syracuseStep 1581423 = 2372135) B2372135
theorem B3801455 : Blo 1580488 3801455 := bstep (se 1 (by rfl) ⟨2851091, by rfl⟩ : syracuseStep 3801455 = 5702183) B5702183
theorem B1581479 : Blo 1580488 1581479 := bstep (se 1 (by rfl) ⟨1186109, by rfl⟩ : syracuseStep 1581479 = 2372219) B2372219
theorem B8552879 : Blo 1580488 8552879 := bstep (se 1 (by rfl) ⟨6414659, by rfl⟩ : syracuseStep 8552879 = 12829319) B12829319
theorem B4276691 : Blo 1580488 4276691 := bstep (se 1 (by rfl) ⟨3207518, by rfl⟩ : syracuseStep 4276691 = 6415037) B6415037
theorem B1581563 : Blo 1580488 1581563 := bstep (se 1 (by rfl) ⟨1186172, by rfl⟩ : syracuseStep 1581563 = 2372345) B2372345
theorem B4506131 : Blo 1580488 4506131 := bstep (se 1 (by rfl) ⟨3379598, by rfl⟩ : syracuseStep 4506131 = 6759197) B6759197
theorem B1581631 : Blo 1580488 1581631 := bstep (se 1 (by rfl) ⟨1186223, by rfl⟩ : syracuseStep 1581631 = 2372447) B2372447
theorem B1581639 : Blo 1580488 1581639 := bstep (se 1 (by rfl) ⟨1186229, by rfl⟩ : syracuseStep 1581639 = 2372459) B2372459
theorem B3375695 : Blo 1580488 3375695 := bstep (se 1 (by rfl) ⟨2531771, by rfl⟩ : syracuseStep 3375695 = 5063543) B5063543
theorem B1688159 : Blo 1580488 1688159 := bstep (se 1 (by rfl) ⟨1266119, by rfl⟩ : syracuseStep 1688159 = 2532239) B2532239
theorem B10814123 : Blo 1580488 10814123 := bstep (se 1 (by rfl) ⟨8110592, by rfl⟩ : syracuseStep 10814123 = 16221185) B16221185
theorem B17097419 : Blo 1580488 17097419 := bstep (se 1 (by rfl) ⟨12823064, by rfl⟩ : syracuseStep 17097419 = 25646129) B25646129
theorem B1581791 : Blo 1580488 1581791 := bstep (se 1 (by rfl) ⟨1186343, by rfl⟩ : syracuseStep 1581791 = 2372687) B2372687
theorem B3556115 : Blo 1580488 3556115 := bstep (se 1 (by rfl) ⟨2667086, by rfl⟩ : syracuseStep 3556115 = 5334173) B5334173
theorem B1581871 : Blo 1580488 1581871 := bstep (se 1 (by rfl) ⟨1186403, by rfl⟩ : syracuseStep 1581871 = 2372807) B2372807
theorem B1581979 : Blo 1580488 1581979 := bstep (se 1 (by rfl) ⟨1186484, by rfl⟩ : syracuseStep 1581979 = 2372969) B2372969
theorem B10134467 : Blo 1580488 10134467 := bstep (se 1 (by rfl) ⟨7600850, by rfl⟩ : syracuseStep 10134467 = 15201701) B15201701
theorem B1582031 : Blo 1580488 1582031 := bstep (se 1 (by rfl) ⟨1186523, by rfl⟩ : syracuseStep 1582031 = 2373047) B2373047
theorem B1582055 : Blo 1580488 1582055 := bstep (se 1 (by rfl) ⟨1186541, by rfl⟩ : syracuseStep 1582055 = 2373083) B2373083
theorem B3556475 : Blo 1580488 3556475 := bstep (se 1 (by rfl) ⟨2667356, by rfl⟩ : syracuseStep 3556475 = 5334713) B5334713
theorem B11551943 : Blo 1580488 11551943 := bstep (se 1 (by rfl) ⟨8663957, by rfl⟩ : syracuseStep 11551943 = 17327915) B17327915
theorem B7210217 : Blo 1580488 7210217 := bstep (se 2 (by rfl) ⟨2703831, by rfl⟩ : syracuseStep 7210217 = 5407663) B5407663
theorem B6751475 : Blo 1580488 6751475 := bstep (se 1 (by rfl) ⟨5063606, by rfl⟩ : syracuseStep 6751475 = 10127213) B10127213
theorem B3556601 : Blo 1580488 3556601 := bstep (se 2 (by rfl) ⟨1333725, by rfl⟩ : syracuseStep 3556601 = 2667451) B2667451
theorem B1582367 : Blo 1580488 1582367 := bstep (se 1 (by rfl) ⟨1186775, by rfl⟩ : syracuseStep 1582367 = 2373551) B2373551
theorem B1582427 : Blo 1580488 1582427 := bstep (se 1 (by rfl) ⟨1186820, by rfl⟩ : syracuseStep 1582427 = 2373641) B2373641
theorem B1582447 : Blo 1580488 1582447 := bstep (se 1 (by rfl) ⟨1186835, by rfl⟩ : syracuseStep 1582447 = 2373671) B2373671
theorem B3556745 : Blo 1580488 3556745 := bstep (se 2 (by rfl) ⟨1333779, by rfl⟩ : syracuseStep 3556745 = 2667559) B2667559
theorem B3556871 : Blo 1580488 3556871 := bstep (se 1 (by rfl) ⟨2667653, by rfl⟩ : syracuseStep 3556871 = 5335307) B5335307
theorem B1779295 : Blo 1580488 1779295 := bstep (se 1 (by rfl) ⟨1334471, by rfl⟩ : syracuseStep 1779295 = 2668943) B2668943
theorem B3557051 : Blo 1580488 3557051 := bstep (se 1 (by rfl) ⟨2667788, by rfl⟩ : syracuseStep 3557051 = 5335577) B5335577
theorem B23111369 : Blo 1580488 23111369 := bstep (se 2 (by rfl) ⟨8666763, by rfl⟩ : syracuseStep 23111369 = 17333527) B17333527
theorem B2000695 : Blo 1580488 2000695 := bstep (se 1 (by rfl) ⟨1500521, by rfl⟩ : syracuseStep 2000695 = 3001043) B3001043
theorem B3557177 : Blo 1580488 3557177 := bstep (se 2 (by rfl) ⟨1333941, by rfl⟩ : syracuseStep 3557177 = 2667883) B2667883
theorem B13518737 : Blo 1580488 13518737 := bstep (se 2 (by rfl) ⟨5069526, by rfl⟩ : syracuseStep 13518737 = 10139053) B10139053
theorem B13691065 : Blo 1580488 13691065 := bstep (se 2 (by rfl) ⟨5134149, by rfl⟩ : syracuseStep 13691065 = 10268299) B10268299
theorem B2001115 : Blo 1580488 2001115 := bstep (se 1 (by rfl) ⟨1500836, by rfl⟩ : syracuseStep 2001115 = 3001673) B3001673
theorem B29231389 : Blo 1580488 29231389 := bstep (se 3 (by rfl) ⟨5480885, by rfl⟩ : syracuseStep 29231389 = 10961771) B10961771
theorem B10266917 : Blo 1580488 10266917 := bstep (se 4 (by rfl) ⟨962523, by rfl⟩ : syracuseStep 10266917 = 1925047) B1925047
theorem B3557807 : Blo 1580488 3557807 := bstep (se 1 (by rfl) ⟨2668355, by rfl⟩ : syracuseStep 3557807 = 5336711) B5336711
theorem B3557843 : Blo 1580488 3557843 := bstep (se 1 (by rfl) ⟨2668382, by rfl⟩ : syracuseStep 3557843 = 5336765) B5336765
theorem B3557951 : Blo 1580488 3557951 := bstep (se 1 (by rfl) ⟨2668463, by rfl⟩ : syracuseStep 3557951 = 5336927) B5336927
theorem B5335631 : Blo 1580488 5335631 := bstep (se 1 (by rfl) ⟨4001723, by rfl⟩ : syracuseStep 5335631 = 8003447) B8003447
theorem B3377771 : Blo 1580488 3377771 := bstep (se 1 (by rfl) ⟨2533328, by rfl⟩ : syracuseStep 3377771 = 5066657) B5066657
theorem B3558059 : Blo 1580488 3558059 := bstep (se 1 (by rfl) ⟨2668544, by rfl⟩ : syracuseStep 3558059 = 5337089) B5337089
theorem B8006525 : Blo 1580488 8006525 := bstep (se 3 (by rfl) ⟨1501223, by rfl⟩ : syracuseStep 8006525 = 3002447) B3002447
theorem B3558599 : Blo 1580488 3558599 := bstep (se 1 (by rfl) ⟨2668949, by rfl⟩ : syracuseStep 3558599 = 5337899) B5337899
theorem B2370779 : Blo 1580488 2370779 := bstep (se 1 (by rfl) ⟨1778084, by rfl⟩ : syracuseStep 2370779 = 3556169) B3556169
theorem B12029303 : Blo 1580488 12029303 := bstep (se 1 (by rfl) ⟨9021977, by rfl⟩ : syracuseStep 12029303 = 18043955) B18043955
theorem B10136951 : Blo 1580488 10136951 := bstep (se 1 (by rfl) ⟨7602713, by rfl⟩ : syracuseStep 10136951 = 15205427) B15205427
theorem B4001147 : Blo 1580488 4001147 := bstep (se 1 (by rfl) ⟨3000860, by rfl⟩ : syracuseStep 4001147 = 6001721) B6001721
theorem B3558779 : Blo 1580488 3558779 := bstep (se 1 (by rfl) ⟨2669084, by rfl⟩ : syracuseStep 3558779 = 5338169) B5338169
theorem B2370953 : Blo 1580488 2370953 := bstep (se 2 (by rfl) ⟨889107, by rfl⟩ : syracuseStep 2370953 = 1778215) B1778215
theorem B3558905 : Blo 1580488 3558905 := bstep (se 2 (by rfl) ⟨1334589, by rfl⟩ : syracuseStep 3558905 = 2669179) B2669179
theorem B6753851 : Blo 1580488 6753851 := bstep (se 1 (by rfl) ⟨5065388, by rfl⟩ : syracuseStep 6753851 = 10130777) B10130777
theorem B3558995 : Blo 1580488 3558995 := bstep (se 1 (by rfl) ⟨2669246, by rfl⟩ : syracuseStep 3558995 = 5338493) B5338493
theorem B5410399 : Blo 1580488 5410399 := bstep (se 1 (by rfl) ⟨4057799, by rfl⟩ : syracuseStep 5410399 = 8115599) B8115599
theorem B6753901 : Blo 1580488 6753901 := bstep (se 3 (by rfl) ⟨1266356, by rfl⟩ : syracuseStep 6753901 = 2532713) B2532713
theorem B11398765 : Blo 1580488 11398765 := bstep (se 3 (by rfl) ⟨2137268, by rfl⟩ : syracuseStep 11398765 = 4274537) B4274537
theorem B51973771 : Blo 1580488 51973771 := bstep (se 1 (by rfl) ⟨38980328, by rfl⟩ : syracuseStep 51973771 = 77960657) B77960657
theorem B2371307 : Blo 1580488 2371307 := bstep (se 1 (by rfl) ⟨1778480, by rfl⟩ : syracuseStep 2371307 = 3556961) B3556961
theorem B3559175 : Blo 1580488 3559175 := bstep (se 1 (by rfl) ⟨2669381, by rfl⟩ : syracuseStep 3559175 = 5338763) B5338763
theorem B5336873 : Blo 1580488 5336873 := bstep (se 2 (by rfl) ⟨2001327, by rfl⟩ : syracuseStep 5336873 = 4002655) B4002655
theorem B7597871 : Blo 1580488 7597871 := bstep (se 1 (by rfl) ⟨5698403, by rfl⟩ : syracuseStep 7597871 = 11396807) B11396807
theorem B7212847 : Blo 1580488 7212847 := bstep (se 1 (by rfl) ⟨5409635, by rfl⟩ : syracuseStep 7212847 = 10819271) B10819271
theorem B3002159 : Blo 1580488 3002159 := bstep (se 1 (by rfl) ⟨2251619, by rfl⟩ : syracuseStep 3002159 = 4503239) B4503239
theorem B2002735 : Blo 1580488 2002735 := bstep (se 1 (by rfl) ⟨1502051, by rfl⟩ : syracuseStep 2002735 = 3004103) B3004103
theorem B8007497 : Blo 1580488 8007497 := bstep (se 2 (by rfl) ⟨3002811, by rfl⟩ : syracuseStep 8007497 = 6005623) B6005623
theorem B2371535 : Blo 1580488 2371535 := bstep (se 1 (by rfl) ⟨1778651, by rfl⟩ : syracuseStep 2371535 = 3557303) B3557303
theorem B19247057 : Blo 1580488 19247057 := bstep (se 2 (by rfl) ⟨7217646, by rfl⟩ : syracuseStep 19247057 = 14435293) B14435293
theorem B10137565 : Blo 1580488 10137565 := bstep (se 3 (by rfl) ⟨1900793, by rfl⟩ : syracuseStep 10137565 = 3801587) B3801587
theorem B6410249 : Blo 1580488 6410249 := bstep (se 2 (by rfl) ⟨2403843, by rfl⟩ : syracuseStep 6410249 = 4807687) B4807687
theorem B5697641 : Blo 1580488 5697641 := bstep (se 2 (by rfl) ⟨2136615, by rfl⟩ : syracuseStep 5697641 = 4273231) B4273231
theorem B3379411 : Blo 1580488 3379411 := bstep (se 1 (by rfl) ⟨2534558, by rfl⟩ : syracuseStep 3379411 = 5069117) B5069117
theorem B9007433 : Blo 1580488 9007433 := bstep (se 2 (by rfl) ⟨3377787, by rfl⟩ : syracuseStep 9007433 = 6755575) B6755575
theorem B2371931 : Blo 1580488 2371931 := bstep (se 1 (by rfl) ⟨1778948, by rfl⟩ : syracuseStep 2371931 = 3557897) B3557897
theorem B3559787 : Blo 1580488 3559787 := bstep (se 1 (by rfl) ⟨2669840, by rfl⟩ : syracuseStep 3559787 = 5339681) B5339681
theorem B3559931 : Blo 1580488 3559931 := bstep (se 1 (by rfl) ⟨2669948, by rfl⟩ : syracuseStep 3559931 = 5339897) B5339897
theorem B6410771 : Blo 1580488 6410771 := bstep (se 1 (by rfl) ⟨4808078, by rfl⟩ : syracuseStep 6410771 = 9616157) B9616157
theorem B2372159 : Blo 1580488 2372159 := bstep (se 1 (by rfl) ⟨1779119, by rfl⟩ : syracuseStep 2372159 = 3558239) B3558239
theorem B3002987 : Blo 1580488 3002987 := bstep (se 1 (by rfl) ⟨2252240, by rfl⟩ : syracuseStep 3002987 = 4504481) B4504481
theorem B22803065 : Blo 1580488 22803065 := bstep (se 2 (by rfl) ⟨8551149, by rfl⟩ : syracuseStep 22803065 = 17102299) B17102299
theorem B13513337 : Blo 1580488 13513337 := bstep (se 2 (by rfl) ⟨5067501, by rfl⟩ : syracuseStep 13513337 = 10135003) B10135003
theorem B3560057 : Blo 1580488 3560057 := bstep (se 2 (by rfl) ⟨1335021, by rfl⟩ : syracuseStep 3560057 = 2670043) B2670043
theorem B3560111 : Blo 1580488 3560111 := bstep (se 1 (by rfl) ⟨2670083, by rfl⟩ : syracuseStep 3560111 = 5340167) B5340167
theorem B2372279 : Blo 1580488 2372279 := bstep (se 1 (by rfl) ⟨1779209, by rfl⟩ : syracuseStep 2372279 = 3558419) B3558419
theorem B3560183 : Blo 1580488 3560183 := bstep (se 1 (by rfl) ⟨2670137, by rfl⟩ : syracuseStep 3560183 = 5340275) B5340275
theorem B2667343 : Blo 1580488 2667343 := bstep (se 1 (by rfl) ⟨2000507, by rfl⟩ : syracuseStep 2667343 = 4001015) B4001015
theorem B2372507 : Blo 1580488 2372507 := bstep (se 1 (by rfl) ⟨1779380, by rfl⟩ : syracuseStep 2372507 = 3558761) B3558761
theorem B6755233 : Blo 1580488 6755233 := bstep (se 2 (by rfl) ⟨2533212, by rfl⟩ : syracuseStep 6755233 = 5066425) B5066425
theorem B3560363 : Blo 1580488 3560363 := bstep (se 1 (by rfl) ⟨2670272, by rfl⟩ : syracuseStep 3560363 = 5340545) B5340545
theorem B13505615 : Blo 1580488 13505615 := bstep (se 1 (by rfl) ⟨10129211, by rfl⟩ : syracuseStep 13505615 = 20258423) B20258423
theorem B8008793 : Blo 1580488 8008793 := bstep (se 2 (by rfl) ⟨3003297, by rfl⟩ : syracuseStep 8008793 = 6006595) B6006595
theorem B4002959 : Blo 1580488 4002959 := bstep (se 1 (by rfl) ⟨3002219, by rfl⟩ : syracuseStep 4002959 = 6004439) B6004439
theorem B15201427 : Blo 1580488 15201427 := bstep (se 1 (by rfl) ⟨11401070, by rfl⟩ : syracuseStep 15201427 = 22802141) B22802141
theorem B2438363 : Blo 1580488 2438363 := bstep (se 1 (by rfl) ⟨1828772, by rfl⟩ : syracuseStep 2438363 = 3657545) B3657545
theorem B2372903 : Blo 1580488 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B2372987 : Blo 1580488 2372987 := bstep (se 1 (by rfl) ⟨1779740, by rfl⟩ : syracuseStep 2372987 = 3559481) B3559481
theorem B12817901 : Blo 1580488 12817901 := bstep (se 3 (by rfl) ⟨2403356, by rfl⟩ : syracuseStep 12817901 = 4806713) B4806713
theorem B2668025 : Blo 1580488 2668025 := bstep (se 2 (by rfl) ⟨1000509, by rfl⟩ : syracuseStep 2668025 = 2001019) B2001019
theorem B2373113 : Blo 1580488 2373113 := bstep (se 2 (by rfl) ⟨889917, by rfl⟩ : syracuseStep 2373113 = 1779835) B1779835
theorem B4273759 : Blo 1580488 4273759 := bstep (se 1 (by rfl) ⟨3205319, by rfl⟩ : syracuseStep 4273759 = 6410639) B6410639
theorem B2373215 : Blo 1580488 2373215 := bstep (se 1 (by rfl) ⟨1779911, by rfl⟩ : syracuseStep 2373215 = 3559823) B3559823
theorem B2668295 : Blo 1580488 2668295 := bstep (se 1 (by rfl) ⟨2001221, by rfl⟩ : syracuseStep 2668295 = 4002443) B4002443
theorem B4273975 : Blo 1580488 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B2373431 : Blo 1580488 2373431 := bstep (se 1 (by rfl) ⟨1780073, by rfl⟩ : syracuseStep 2373431 = 3560147) B3560147
theorem B5339087 : Blo 1580488 5339087 := bstep (se 1 (by rfl) ⟨4004315, by rfl⟩ : syracuseStep 5339087 = 8008631) B8008631
theorem B8550373 : Blo 1580488 8550373 := bstep (se 4 (by rfl) ⟨801597, by rfl⟩ : syracuseStep 8550373 = 1603195) B1603195
theorem B30414851 : Blo 1580488 30414851 := bstep (se 1 (by rfl) ⟨22811138, by rfl⟩ : syracuseStep 30414851 = 45622277) B45622277
theorem B8001665 : Blo 1580488 8001665 := bstep (se 2 (by rfl) ⟨3000624, by rfl⟩ : syracuseStep 8001665 = 6001249) B6001249
theorem B12015863 : Blo 1580488 12015863 := bstep (se 1 (by rfl) ⟨9011897, by rfl⟩ : syracuseStep 12015863 = 18023795) B18023795
theorem B4274441 : Blo 1580488 4274441 := bstep (se 2 (by rfl) ⟨1602915, by rfl⟩ : syracuseStep 4274441 = 3205831) B3205831
theorem B16234775 : Blo 1580488 16234775 := bstep (se 1 (by rfl) ⟨12176081, by rfl⟩ : syracuseStep 16234775 = 24352163) B24352163
theorem B2669051 : Blo 1580488 2669051 := bstep (se 1 (by rfl) ⟨2001788, by rfl⟩ : syracuseStep 2669051 = 4003577) B4003577
theorem B9615935 : Blo 1580488 9615935 := bstep (se 1 (by rfl) ⟨7211951, by rfl⟩ : syracuseStep 9615935 = 14423903) B14423903
theorem B13179455 : Blo 1580488 13179455 := bstep (se 1 (by rfl) ⟨9884591, by rfl⟩ : syracuseStep 13179455 = 19769183) B19769183
theorem B12827243 : Blo 1580488 12827243 := bstep (se 1 (by rfl) ⟨9620432, by rfl⟩ : syracuseStep 12827243 = 19240865) B19240865
theorem B4004599 : Blo 1580488 4004599 := bstep (se 1 (by rfl) ⟨3003449, by rfl⟩ : syracuseStep 4004599 = 6006899) B6006899
theorem B9010075 : Blo 1580488 9010075 := bstep (se 1 (by rfl) ⟨6757556, by rfl⟩ : syracuseStep 9010075 = 13515113) B13515113
theorem B5340059 : Blo 1580488 5340059 := bstep (se 1 (by rfl) ⟨4005044, by rfl⟩ : syracuseStep 5340059 = 8010089) B8010089
theorem B8002475 : Blo 1580488 8002475 := bstep (se 1 (by rfl) ⟨6001856, by rfl⟩ : syracuseStep 8002475 = 12003713) B12003713
theorem B2669483 : Blo 1580488 2669483 := bstep (se 1 (by rfl) ⟨2002112, by rfl⟩ : syracuseStep 2669483 = 4004225) B4004225
theorem B4004903 : Blo 1580488 4004903 := bstep (se 1 (by rfl) ⟨3003677, by rfl⟩ : syracuseStep 4004903 = 6007355) B6007355
theorem B14621917 : Blo 1580488 14621917 := bstep (se 3 (by rfl) ⟨2741609, by rfl⟩ : syracuseStep 14621917 = 5483219) B5483219
theorem B15203659 : Blo 1580488 15203659 := bstep (se 1 (by rfl) ⟨11402744, by rfl⟩ : syracuseStep 15203659 = 22805489) B22805489
theorem B13508005 : Blo 1580488 13508005 := bstep (se 4 (by rfl) ⟨1266375, by rfl⟩ : syracuseStep 13508005 = 2532751) B2532751
theorem B2670023 : Blo 1580488 2670023 := bstep (se 1 (by rfl) ⟨2002517, by rfl⟩ : syracuseStep 2670023 = 4005035) B4005035
theorem B8011223 : Blo 1580488 8011223 := bstep (se 1 (by rfl) ⟨6008417, by rfl⟩ : syracuseStep 8011223 = 12016835) B12016835
theorem B1580539 : Blo 1580488 1580539 := bstep (se 1 (by rfl) ⟨1185404, by rfl⟩ : syracuseStep 1580539 = 2370809) B2370809
theorem B1580607 : Blo 1580488 1580607 := bstep (se 1 (by rfl) ⟨1185455, by rfl⟩ : syracuseStep 1580607 = 2370911) B2370911
theorem B1580615 : Blo 1580488 1580615 := bstep (se 1 (by rfl) ⟨1185461, by rfl⟩ : syracuseStep 1580615 = 2370923) B2370923
theorem B5701229 : Blo 1580488 5701229 := bstep (se 3 (by rfl) ⟨1068980, by rfl⟩ : syracuseStep 5701229 = 2137961) B2137961
theorem B34193015 : Blo 1580488 34193015 := bstep (se 1 (by rfl) ⟨25644761, by rfl⟩ : syracuseStep 34193015 = 51289523) B51289523
theorem B1580767 : Blo 1580488 1580767 := bstep (se 1 (by rfl) ⟨1185575, by rfl⟩ : syracuseStep 1580767 = 2371151) B2371151
theorem B3800839 : Blo 1580488 3800839 := bstep (se 1 (by rfl) ⟨2850629, by rfl⟩ : syracuseStep 3800839 = 5701259) B5701259
theorem B1580847 : Blo 1580488 1580847 := bstep (se 1 (by rfl) ⟨1185635, by rfl⟩ : syracuseStep 1580847 = 2371271) B2371271
theorem B1580955 : Blo 1580488 1580955 := bstep (se 1 (by rfl) ⟨1185716, by rfl⟩ : syracuseStep 1580955 = 2371433) B2371433
theorem B6004637 : Blo 1580488 6004637 := bstep (se 3 (by rfl) ⟨1125869, by rfl⟩ : syracuseStep 6004637 = 2251739) B2251739
theorem B1581007 : Blo 1580488 1581007 := bstep (se 1 (by rfl) ⟨1185755, by rfl⟩ : syracuseStep 1581007 = 2371511) B2371511
theorem B1581031 : Blo 1580488 1581031 := bstep (se 1 (by rfl) ⟨1185773, by rfl⟩ : syracuseStep 1581031 = 2371547) B2371547
theorem B41107571 : Blo 1580488 41107571 := bstep (se 1 (by rfl) ⟨30830678, by rfl⟩ : syracuseStep 41107571 = 61661357) B61661357
theorem B6004955 : Blo 1580488 6004955 := bstep (se 1 (by rfl) ⟨4503716, by rfl⟩ : syracuseStep 6004955 = 9007433) B9007433
theorem B1581287 : Blo 1580488 1581287 := bstep (se 1 (by rfl) ⟨1185965, by rfl⟩ : syracuseStep 1581287 = 2371931) B2371931
theorem B7602407 : Blo 1580488 7602407 := bstep (se 1 (by rfl) ⟨5701805, by rfl⟩ : syracuseStep 7602407 = 11403611) B11403611
theorem B4505881 : Blo 1580488 4505881 := bstep (se 2 (by rfl) ⟨1689705, by rfl⟩ : syracuseStep 4505881 = 3379411) B3379411
theorem B5701919 : Blo 1580488 5701919 := bstep (se 1 (by rfl) ⟨4276439, by rfl⟩ : syracuseStep 5701919 = 8552879) B8552879
theorem B2851127 : Blo 1580488 2851127 := bstep (se 1 (by rfl) ⟨2138345, by rfl⟩ : syracuseStep 2851127 = 4276691) B4276691
theorem B1581439 : Blo 1580488 1581439 := bstep (se 1 (by rfl) ⟨1186079, by rfl⟩ : syracuseStep 1581439 = 2372159) B2372159
theorem B7209415 : Blo 1580488 7209415 := bstep (se 1 (by rfl) ⟨5407061, by rfl⟩ : syracuseStep 7209415 = 10814123) B10814123
theorem B1581519 : Blo 1580488 1581519 := bstep (se 1 (by rfl) ⟨1186139, by rfl⟩ : syracuseStep 1581519 = 2372279) B2372279
theorem B1581671 : Blo 1580488 1581671 := bstep (se 1 (by rfl) ⟨1186253, by rfl⟩ : syracuseStep 1581671 = 2372507) B2372507
theorem B9003743 : Blo 1580488 9003743 := bstep (se 1 (by rfl) ⟨6752807, by rfl⟩ : syracuseStep 9003743 = 13505615) B13505615
theorem B27378445 : Blo 1580488 27378445 := bstep (se 3 (by rfl) ⟨5133458, by rfl⟩ : syracuseStep 27378445 = 10266917) B10266917
theorem B7701295 : Blo 1580488 7701295 := bstep (se 1 (by rfl) ⟨5775971, by rfl⟩ : syracuseStep 7701295 = 11551943) B11551943
theorem B1581935 : Blo 1580488 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B6751133 : Blo 1580488 6751133 := bstep (se 3 (by rfl) ⟨1265837, by rfl⟩ : syracuseStep 6751133 = 2531675) B2531675
theorem B1581991 : Blo 1580488 1581991 := bstep (se 1 (by rfl) ⟨1186493, by rfl⟩ : syracuseStep 1581991 = 2372987) B2372987
theorem B8545267 : Blo 1580488 8545267 := bstep (se 1 (by rfl) ⟨6408950, by rfl⟩ : syracuseStep 8545267 = 12817901) B12817901
theorem B1778683 : Blo 1580488 1778683 := bstep (se 1 (by rfl) ⟨1334012, by rfl⟩ : syracuseStep 1778683 = 2668025) B2668025
theorem B1582075 : Blo 1580488 1582075 := bstep (se 1 (by rfl) ⟨1186556, by rfl⟩ : syracuseStep 1582075 = 2373113) B2373113
theorem B1582143 : Blo 1580488 1582143 := bstep (se 1 (by rfl) ⟨1186607, by rfl⟩ : syracuseStep 1582143 = 2373215) B2373215
theorem B3556457 : Blo 1580488 3556457 := bstep (se 2 (by rfl) ⟨1333671, by rfl⟩ : syracuseStep 3556457 = 2667343) B2667343
theorem B1778863 : Blo 1580488 1778863 := bstep (se 1 (by rfl) ⟨1334147, by rfl⟩ : syracuseStep 1778863 = 2668295) B2668295
theorem B1582287 : Blo 1580488 1582287 := bstep (se 1 (by rfl) ⟨1186715, by rfl⟩ : syracuseStep 1582287 = 2373431) B2373431
theorem B9012491 : Blo 1580488 9012491 := bstep (se 1 (by rfl) ⟨6759368, by rfl⟩ : syracuseStep 9012491 = 13518737) B13518737
theorem B20276567 : Blo 1580488 20276567 := bstep (se 1 (by rfl) ⟨15207425, by rfl⟩ : syracuseStep 20276567 = 30414851) B30414851
theorem B5334443 : Blo 1580488 5334443 := bstep (se 1 (by rfl) ⟨4000832, by rfl⟩ : syracuseStep 5334443 = 8001665) B8001665
theorem B25642493 : Blo 1580488 25642493 := bstep (se 3 (by rfl) ⟨4807967, by rfl⟩ : syracuseStep 25642493 = 9615935) B9615935
theorem B10823183 : Blo 1580488 10823183 := bstep (se 1 (by rfl) ⟨8117387, by rfl⟩ : syracuseStep 10823183 = 16234775) B16234775
theorem B20268569 : Blo 1580488 20268569 := bstep (se 2 (by rfl) ⟨7600713, by rfl⟩ : syracuseStep 20268569 = 15201427) B15201427
theorem B1779367 : Blo 1580488 1779367 := bstep (se 1 (by rfl) ⟨1334525, by rfl⟩ : syracuseStep 1779367 = 2669051) B2669051
theorem B3557087 : Blo 1580488 3557087 := bstep (se 1 (by rfl) ⟨2667815, by rfl⟩ : syracuseStep 3557087 = 5335631) B5335631
theorem B5334983 : Blo 1580488 5334983 := bstep (se 1 (by rfl) ⟨4001237, by rfl⟩ : syracuseStep 5334983 = 8002475) B8002475
theorem B1779655 : Blo 1580488 1779655 := bstep (se 1 (by rfl) ⟨1334741, by rfl⟩ : syracuseStep 1779655 = 2669483) B2669483
theorem B9005201 : Blo 1580488 9005201 := bstep (se 2 (by rfl) ⟨3376950, by rfl⟩ : syracuseStep 9005201 = 6753901) B6753901
theorem B15198353 : Blo 1580488 15198353 := bstep (se 2 (by rfl) ⟨5699382, by rfl⟩ : syracuseStep 15198353 = 11398765) B11398765
theorem B69298361 : Blo 1580488 69298361 := bstep (se 2 (by rfl) ⟨25986885, by rfl⟩ : syracuseStep 69298361 = 51973771) B51973771
theorem B1780015 : Blo 1580488 1780015 := bstep (se 1 (by rfl) ⟨1335011, by rfl⟩ : syracuseStep 1780015 = 2670023) B2670023
theorem B3557915 : Blo 1580488 3557915 := bstep (se 1 (by rfl) ⟨2668436, by rfl⟩ : syracuseStep 3557915 = 5336873) B5336873
theorem B5065247 : Blo 1580488 5065247 := bstep (se 1 (by rfl) ⟨3798935, by rfl⟩ : syracuseStep 5065247 = 7597871) B7597871
theorem B2001439 : Blo 1580488 2001439 := bstep (se 1 (by rfl) ⟨1501079, by rfl⟩ : syracuseStep 2001439 = 3002159) B3002159
theorem B12831371 : Blo 1580488 12831371 := bstep (se 1 (by rfl) ⟨9623528, by rfl⟩ : syracuseStep 12831371 = 19247057) B19247057
theorem B5335739 : Blo 1580488 5335739 := bstep (se 1 (by rfl) ⟨4001804, by rfl⟩ : syracuseStep 5335739 = 8003609) B8003609
theorem B2534303 : Blo 1580488 2534303 := bstep (se 1 (by rfl) ⟨1900727, by rfl⟩ : syracuseStep 2534303 = 3801455) B3801455
theorem B18254753 : Blo 1580488 18254753 := bstep (se 2 (by rfl) ⟨6845532, by rfl⟩ : syracuseStep 18254753 = 13691065) B13691065
theorem B2001991 : Blo 1580488 2001991 := bstep (se 1 (by rfl) ⟨1501493, by rfl⟩ : syracuseStep 2001991 = 3002987) B3002987
theorem B11398279 : Blo 1580488 11398279 := bstep (se 1 (by rfl) ⟨8548709, by rfl⟩ : syracuseStep 11398279 = 17097419) B17097419
theorem B2370743 : Blo 1580488 2370743 := bstep (se 1 (by rfl) ⟨1778057, by rfl⟩ : syracuseStep 2370743 = 3556115) B3556115
theorem B2370983 : Blo 1580488 2370983 := bstep (se 1 (by rfl) ⟨1778237, by rfl⟩ : syracuseStep 2370983 = 3556475) B3556475
theorem B4500983 : Blo 1580488 4500983 := bstep (se 1 (by rfl) ⟨3375737, by rfl⟩ : syracuseStep 4500983 = 6751475) B6751475
theorem B2371067 : Blo 1580488 2371067 := bstep (se 1 (by rfl) ⟨1778300, by rfl⟩ : syracuseStep 2371067 = 3556601) B3556601
theorem B2371163 : Blo 1580488 2371163 := bstep (se 1 (by rfl) ⟨1778372, by rfl⟩ : syracuseStep 2371163 = 3556745) B3556745
theorem B2371247 : Blo 1580488 2371247 := bstep (se 1 (by rfl) ⟨1778435, by rfl⟩ : syracuseStep 2371247 = 3556871) B3556871
theorem B2371367 : Blo 1580488 2371367 := bstep (se 1 (by rfl) ⟨1778525, by rfl⟩ : syracuseStep 2371367 = 3557051) B3557051
theorem B12013433 : Blo 1580488 12013433 := bstep (se 2 (by rfl) ⟨4505037, by rfl⟩ : syracuseStep 12013433 = 9010075) B9010075
theorem B2371451 : Blo 1580488 2371451 := bstep (se 1 (by rfl) ⟨1778588, by rfl⟩ : syracuseStep 2371451 = 3557177) B3557177
theorem B9006977 : Blo 1580488 9006977 := bstep (se 2 (by rfl) ⟨3377616, by rfl⟩ : syracuseStep 9006977 = 6755233) B6755233
theorem B3559391 : Blo 1580488 3559391 := bstep (se 1 (by rfl) ⟨2669543, by rfl⟩ : syracuseStep 3559391 = 5339087) B5339087
theorem B4501757 : Blo 1580488 4501757 := bstep (se 3 (by rfl) ⟨844079, by rfl⟩ : syracuseStep 4501757 = 1688159) B1688159
theorem B2371871 : Blo 1580488 2371871 := bstep (se 1 (by rfl) ⟨1778903, by rfl⟩ : syracuseStep 2371871 = 3557807) B3557807
theorem B22794533 : Blo 1580488 22794533 := bstep (se 4 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 22794533 = 4273975) B4273975
theorem B2371895 : Blo 1580488 2371895 := bstep (se 1 (by rfl) ⟨1778921, by rfl⟩ : syracuseStep 2371895 = 3557843) B3557843
theorem B2371967 : Blo 1580488 2371967 := bstep (se 1 (by rfl) ⟨1778975, by rfl⟩ : syracuseStep 2371967 = 3557951) B3557951
theorem B8786303 : Blo 1580488 8786303 := bstep (se 1 (by rfl) ⟨6589727, by rfl⟩ : syracuseStep 8786303 = 13179455) B13179455
theorem B20271545 : Blo 1580488 20271545 := bstep (se 2 (by rfl) ⟨7601829, by rfl⟩ : syracuseStep 20271545 = 15203659) B15203659
theorem B2372039 : Blo 1580488 2372039 := bstep (se 1 (by rfl) ⟨1779029, by rfl⟩ : syracuseStep 2372039 = 3558059) B3558059
theorem B18010673 : Blo 1580488 18010673 := bstep (se 2 (by rfl) ⟨6754002, by rfl⟩ : syracuseStep 18010673 = 13508005) B13508005
theorem B5337683 : Blo 1580488 5337683 := bstep (se 1 (by rfl) ⟨4003262, by rfl⟩ : syracuseStep 5337683 = 8006525) B8006525
theorem B3560039 : Blo 1580488 3560039 := bstep (se 1 (by rfl) ⟨2670029, by rfl⟩ : syracuseStep 3560039 = 5340059) B5340059
theorem B5698345 : Blo 1580488 5698345 := bstep (se 2 (by rfl) ⟨2136879, by rfl⟩ : syracuseStep 5698345 = 4273759) B4273759
theorem B7213865 : Blo 1580488 7213865 := bstep (se 2 (by rfl) ⟨2705199, by rfl⟩ : syracuseStep 7213865 = 5410399) B5410399
theorem B2372393 : Blo 1580488 2372393 := bstep (se 2 (by rfl) ⟨889647, by rfl⟩ : syracuseStep 2372393 = 1779295) B1779295
theorem B2372399 : Blo 1580488 2372399 := bstep (se 1 (by rfl) ⟨1779299, by rfl⟩ : syracuseStep 2372399 = 3558599) B3558599
theorem B2667431 : Blo 1580488 2667431 := bstep (se 1 (by rfl) ⟨2000573, by rfl⟩ : syracuseStep 2667431 = 4001147) B4001147
theorem B2372519 : Blo 1580488 2372519 := bstep (se 1 (by rfl) ⟨1779389, by rfl⟩ : syracuseStep 2372519 = 3558779) B3558779
theorem B2372603 : Blo 1580488 2372603 := bstep (se 1 (by rfl) ⟨1779452, by rfl⟩ : syracuseStep 2372603 = 3558905) B3558905
theorem B5067785 : Blo 1580488 5067785 := bstep (se 2 (by rfl) ⟨1900419, by rfl⟩ : syracuseStep 5067785 = 3800839) B3800839
theorem B4502567 : Blo 1580488 4502567 := bstep (se 1 (by rfl) ⟨3376925, by rfl⟩ : syracuseStep 4502567 = 6753851) B6753851
theorem B2372663 : Blo 1580488 2372663 := bstep (se 1 (by rfl) ⟨1779497, by rfl⟩ : syracuseStep 2372663 = 3558995) B3558995
theorem B2667593 : Blo 1580488 2667593 := bstep (se 2 (by rfl) ⟨1000347, by rfl⟩ : syracuseStep 2667593 = 2000695) B2000695
theorem B22795343 : Blo 1580488 22795343 := bstep (se 1 (by rfl) ⟨17096507, by rfl⟩ : syracuseStep 22795343 = 34193015) B34193015
theorem B2372783 : Blo 1580488 2372783 := bstep (se 1 (by rfl) ⟨1779587, by rfl⟩ : syracuseStep 2372783 = 3559175) B3559175
theorem B5338331 : Blo 1580488 5338331 := bstep (se 1 (by rfl) ⟨4003748, by rfl⟩ : syracuseStep 5338331 = 8007497) B8007497
theorem B4003091 : Blo 1580488 4003091 := bstep (se 1 (by rfl) ⟨3002318, by rfl⟩ : syracuseStep 4003091 = 6004637) B6004637
theorem B11400497 : Blo 1580488 11400497 := bstep (se 2 (by rfl) ⟨4275186, by rfl⟩ : syracuseStep 11400497 = 8550373) B8550373
theorem B4273499 : Blo 1580488 4273499 := bstep (se 1 (by rfl) ⟨3205124, by rfl⟩ : syracuseStep 4273499 = 6410249) B6410249
theorem B6002039 : Blo 1580488 6002039 := bstep (se 1 (by rfl) ⟨4501529, by rfl⟩ : syracuseStep 6002039 = 9003059) B9003059
theorem B3798427 : Blo 1580488 3798427 := bstep (se 1 (by rfl) ⟨2848820, by rfl⟩ : syracuseStep 3798427 = 5697641) B5697641
theorem B2373191 : Blo 1580488 2373191 := bstep (se 1 (by rfl) ⟨1779893, by rfl⟩ : syracuseStep 2373191 = 3559787) B3559787
theorem B2668153 : Blo 1580488 2668153 := bstep (se 2 (by rfl) ⟨1000557, by rfl⟩ : syracuseStep 2668153 = 2001115) B2001115
theorem B2373287 : Blo 1580488 2373287 := bstep (se 1 (by rfl) ⟨1779965, by rfl⟩ : syracuseStep 2373287 = 3559931) B3559931
theorem B4273847 : Blo 1580488 4273847 := bstep (se 1 (by rfl) ⟨3205385, by rfl⟩ : syracuseStep 4273847 = 6410771) B6410771
theorem B38975185 : Blo 1580488 38975185 := bstep (se 2 (by rfl) ⟨14615694, by rfl⟩ : syracuseStep 38975185 = 29231389) B29231389
theorem B15202043 : Blo 1580488 15202043 := bstep (se 1 (by rfl) ⟨11401532, by rfl⟩ : syracuseStep 15202043 = 22803065) B22803065
theorem B9008891 : Blo 1580488 9008891 := bstep (se 1 (by rfl) ⟨6756668, by rfl⟩ : syracuseStep 9008891 = 13513337) B13513337
theorem B2373371 : Blo 1580488 2373371 := bstep (se 1 (by rfl) ⟨1780028, by rfl⟩ : syracuseStep 2373371 = 3560057) B3560057
theorem B2373407 : Blo 1580488 2373407 := bstep (se 1 (by rfl) ⟨1780055, by rfl⟩ : syracuseStep 2373407 = 3560111) B3560111
theorem B2373455 : Blo 1580488 2373455 := bstep (se 1 (by rfl) ⟨1780091, by rfl⟩ : syracuseStep 2373455 = 3560183) B3560183
theorem B6502301 : Blo 1580488 6502301 := bstep (se 3 (by rfl) ⟨1219181, by rfl⟩ : syracuseStep 6502301 = 2438363) B2438363
theorem B2373575 : Blo 1580488 2373575 := bstep (se 1 (by rfl) ⟨1780181, by rfl⟩ : syracuseStep 2373575 = 3560363) B3560363
theorem B6756311 : Blo 1580488 6756311 := bstep (se 1 (by rfl) ⟨5067233, by rfl⟩ : syracuseStep 6756311 = 10134467) B10134467
theorem B5339195 : Blo 1580488 5339195 := bstep (se 1 (by rfl) ⟨4004396, by rfl⟩ : syracuseStep 5339195 = 8008793) B8008793
theorem B2668639 : Blo 1580488 2668639 := bstep (se 1 (by rfl) ⟨2001479, by rfl⟩ : syracuseStep 2668639 = 4002959) B4002959
theorem B4806811 : Blo 1580488 4806811 := bstep (se 1 (by rfl) ⟨3605108, by rfl⟩ : syracuseStep 4806811 = 7210217) B7210217
theorem B5339465 : Blo 1580488 5339465 := bstep (se 2 (by rfl) ⟨2002299, by rfl⟩ : syracuseStep 5339465 = 4004599) B4004599
theorem B15407579 : Blo 1580488 15407579 := bstep (se 1 (by rfl) ⟨11555684, by rfl⟩ : syracuseStep 15407579 = 23111369) B23111369
theorem B12016349 : Blo 1580488 12016349 := bstep (se 3 (by rfl) ⟨2253065, by rfl⟩ : syracuseStep 12016349 = 4506131) B4506131
theorem B8010575 : Blo 1580488 8010575 := bstep (se 1 (by rfl) ⟨6007931, by rfl⟩ : syracuseStep 8010575 = 12015863) B12015863
theorem B2849627 : Blo 1580488 2849627 := bstep (se 1 (by rfl) ⟨2137220, by rfl⟩ : syracuseStep 2849627 = 4274441) B4274441
theorem B9001853 : Blo 1580488 9001853 := bstep (se 3 (by rfl) ⟨1687847, by rfl⟩ : syracuseStep 9001853 = 3375695) B3375695
theorem B19495889 : Blo 1580488 19495889 := bstep (se 2 (by rfl) ⟨7310958, by rfl⟩ : syracuseStep 19495889 = 14621917) B14621917
theorem B2251847 : Blo 1580488 2251847 := bstep (se 1 (by rfl) ⟨1688885, by rfl⟩ : syracuseStep 2251847 = 3377771) B3377771
theorem B8551495 : Blo 1580488 8551495 := bstep (se 1 (by rfl) ⟨6413621, by rfl⟩ : syracuseStep 8551495 = 12827243) B12827243
theorem B2669935 : Blo 1580488 2669935 := bstep (se 1 (by rfl) ⟨2002451, by rfl⟩ : syracuseStep 2669935 = 4004903) B4004903
theorem B1580519 : Blo 1580488 1580519 := bstep (se 1 (by rfl) ⟨1185389, by rfl⟩ : syracuseStep 1580519 = 2370779) B2370779
theorem B8019535 : Blo 1580488 8019535 := bstep (se 1 (by rfl) ⟨6014651, by rfl⟩ : syracuseStep 8019535 = 12029303) B12029303
theorem B6757967 : Blo 1580488 6757967 := bstep (se 1 (by rfl) ⟨5068475, by rfl⟩ : syracuseStep 6757967 = 10136951) B10136951
theorem B1580635 : Blo 1580488 1580635 := bstep (se 1 (by rfl) ⟨1185476, by rfl⟩ : syracuseStep 1580635 = 2370953) B2370953
theorem B5340815 : Blo 1580488 5340815 := bstep (se 1 (by rfl) ⟨4005611, by rfl⟩ : syracuseStep 5340815 = 8011223) B8011223
theorem B9617129 : Blo 1580488 9617129 := bstep (se 2 (by rfl) ⟨3606423, by rfl⟩ : syracuseStep 9617129 = 7212847) B7212847
theorem B2670313 : Blo 1580488 2670313 := bstep (se 2 (by rfl) ⟨1001367, by rfl⟩ : syracuseStep 2670313 = 2002735) B2002735
theorem B3800819 : Blo 1580488 3800819 := bstep (se 1 (by rfl) ⟨2850614, by rfl⟩ : syracuseStep 3800819 = 5701229) B5701229
theorem B1580871 : Blo 1580488 1580871 := bstep (se 1 (by rfl) ⟨1185653, by rfl⟩ : syracuseStep 1580871 = 2371307) B2371307
theorem B13516753 : Blo 1580488 13516753 := bstep (se 2 (by rfl) ⟨5068782, by rfl⟩ : syracuseStep 13516753 = 10137565) B10137565
theorem B1581023 : Blo 1580488 1581023 := bstep (se 1 (by rfl) ⟨1185767, by rfl⟩ : syracuseStep 1581023 = 2371535) B2371535
theorem B6004925 : Blo 1580488 6004925 := bstep (se 3 (by rfl) ⟨1125923, by rfl⟩ : syracuseStep 6004925 = 2251847) B2251847
theorem B1581247 : Blo 1580488 1581247 := bstep (se 1 (by rfl) ⟨1185935, by rfl⟩ : syracuseStep 1581247 = 2371871) B2371871
theorem B15196355 : Blo 1580488 15196355 := bstep (se 1 (by rfl) ⟨11397266, by rfl⟩ : syracuseStep 15196355 = 22794533) B22794533
theorem B1581263 : Blo 1580488 1581263 := bstep (se 1 (by rfl) ⟨1185947, by rfl⟩ : syracuseStep 1581263 = 2371895) B2371895
theorem B1900751 : Blo 1580488 1900751 := bstep (se 1 (by rfl) ⟨1425563, by rfl⟩ : syracuseStep 1900751 = 2851127) B2851127
theorem B1581311 : Blo 1580488 1581311 := bstep (se 1 (by rfl) ⟨1185983, by rfl⟩ : syracuseStep 1581311 = 2371967) B2371967
theorem B5857535 : Blo 1580488 5857535 := bstep (se 1 (by rfl) ⟨4393151, by rfl⟩ : syracuseStep 5857535 = 8786303) B8786303
theorem B1581359 : Blo 1580488 1581359 := bstep (se 1 (by rfl) ⟨1186019, by rfl⟩ : syracuseStep 1581359 = 2372039) B2372039
theorem B1581595 : Blo 1580488 1581595 := bstep (se 1 (by rfl) ⟨1186196, by rfl⟩ : syracuseStep 1581595 = 2372393) B2372393
theorem B1581599 : Blo 1580488 1581599 := bstep (se 1 (by rfl) ⟨1186199, by rfl⟩ : syracuseStep 1581599 = 2372399) B2372399
theorem B1778287 : Blo 1580488 1778287 := bstep (se 1 (by rfl) ⟨1333715, by rfl⟩ : syracuseStep 1778287 = 2667431) B2667431
theorem B1581679 : Blo 1580488 1581679 := bstep (se 1 (by rfl) ⟨1186259, by rfl⟩ : syracuseStep 1581679 = 2372519) B2372519
theorem B1581735 : Blo 1580488 1581735 := bstep (se 1 (by rfl) ⟨1186301, by rfl⟩ : syracuseStep 1581735 = 2372603) B2372603
theorem B1581775 : Blo 1580488 1581775 := bstep (se 1 (by rfl) ⟨1186331, by rfl⟩ : syracuseStep 1581775 = 2372663) B2372663
theorem B1778395 : Blo 1580488 1778395 := bstep (se 1 (by rfl) ⟨1333796, by rfl⟩ : syracuseStep 1778395 = 2667593) B2667593
theorem B15196895 : Blo 1580488 15196895 := bstep (se 1 (by rfl) ⟨11397671, by rfl⟩ : syracuseStep 15196895 = 22795343) B22795343
theorem B1581855 : Blo 1580488 1581855 := bstep (se 1 (by rfl) ⟨1186391, by rfl⟩ : syracuseStep 1581855 = 2372783) B2372783
theorem B13517711 : Blo 1580488 13517711 := bstep (se 1 (by rfl) ⟨10138283, by rfl⟩ : syracuseStep 13517711 = 20276567) B20276567
theorem B11395997 : Blo 1580488 11395997 := bstep (se 3 (by rfl) ⟨2136749, by rfl⟩ : syracuseStep 11395997 = 4273499) B4273499
theorem B3556295 : Blo 1580488 3556295 := bstep (se 1 (by rfl) ⟨2667221, by rfl⟩ : syracuseStep 3556295 = 5334443) B5334443
theorem B36504593 : Blo 1580488 36504593 := bstep (se 2 (by rfl) ⟨13689222, by rfl⟩ : syracuseStep 36504593 = 27378445) B27378445
theorem B1582127 : Blo 1580488 1582127 := bstep (se 1 (by rfl) ⟨1186595, by rfl⟩ : syracuseStep 1582127 = 2373191) B2373191
theorem B1582191 : Blo 1580488 1582191 := bstep (se 1 (by rfl) ⟨1186643, by rfl⟩ : syracuseStep 1582191 = 2373287) B2373287
theorem B10134695 : Blo 1580488 10134695 := bstep (se 1 (by rfl) ⟨7601021, by rfl⟩ : syracuseStep 10134695 = 15202043) B15202043
theorem B6005927 : Blo 1580488 6005927 := bstep (se 1 (by rfl) ⟨4504445, by rfl⟩ : syracuseStep 6005927 = 9008891) B9008891
theorem B1582247 : Blo 1580488 1582247 := bstep (se 1 (by rfl) ⟨1186685, by rfl⟩ : syracuseStep 1582247 = 2373371) B2373371
theorem B1582271 : Blo 1580488 1582271 := bstep (se 1 (by rfl) ⟨1186703, by rfl⟩ : syracuseStep 1582271 = 2373407) B2373407
theorem B1582303 : Blo 1580488 1582303 := bstep (se 1 (by rfl) ⟨1186727, by rfl⟩ : syracuseStep 1582303 = 2373455) B2373455
theorem B4334867 : Blo 1580488 4334867 := bstep (se 1 (by rfl) ⟨3251150, by rfl⟩ : syracuseStep 4334867 = 6502301) B6502301
theorem B3556655 : Blo 1580488 3556655 := bstep (se 1 (by rfl) ⟨2667491, by rfl⟩ : syracuseStep 3556655 = 5334983) B5334983
theorem B1582383 : Blo 1580488 1582383 := bstep (se 1 (by rfl) ⟨1186787, by rfl⟩ : syracuseStep 1582383 = 2373575) B2373575
theorem B15197705 : Blo 1580488 15197705 := bstep (se 2 (by rfl) ⟨5699139, by rfl⟩ : syracuseStep 15197705 = 11398279) B11398279
theorem B3376831 : Blo 1580488 3376831 := bstep (se 1 (by rfl) ⟨2532623, by rfl⟩ : syracuseStep 3376831 = 5065247) B5065247
theorem B8554247 : Blo 1580488 8554247 := bstep (se 1 (by rfl) ⟨6415685, by rfl⟩ : syracuseStep 8554247 = 12831371) B12831371
theorem B3557159 : Blo 1580488 3557159 := bstep (se 1 (by rfl) ⟨2667869, by rfl⟩ : syracuseStep 3557159 = 5335739) B5335739
theorem B5064569 : Blo 1580488 5064569 := bstep (se 2 (by rfl) ⟨1899213, by rfl⟩ : syracuseStep 5064569 = 3798427) B3798427
theorem B1689535 : Blo 1580488 1689535 := bstep (se 1 (by rfl) ⟨1267151, by rfl⟩ : syracuseStep 1689535 = 2534303) B2534303
theorem B10692713 : Blo 1580488 10692713 := bstep (se 2 (by rfl) ⟨4009767, by rfl⟩ : syracuseStep 10692713 = 8019535) B8019535
theorem B19236973 : Blo 1580488 19236973 := bstep (se 3 (by rfl) ⟨3606932, by rfl⟩ : syracuseStep 19236973 = 7213865) B7213865
theorem B3557537 : Blo 1580488 3557537 := bstep (se 2 (by rfl) ⟨1334076, by rfl⟩ : syracuseStep 3557537 = 2668153) B2668153
theorem B3000655 : Blo 1580488 3000655 := bstep (se 1 (by rfl) ⟨2250491, by rfl⟩ : syracuseStep 3000655 = 4500983) B4500983
theorem B2533879 : Blo 1580488 2533879 := bstep (se 1 (by rfl) ⟨1900409, by rfl⟩ : syracuseStep 2533879 = 3800819) B3800819
theorem B45574757 : Blo 1580488 45574757 := bstep (se 4 (by rfl) ⟨4272633, by rfl⟩ : syracuseStep 45574757 = 8545267) B8545267
theorem B27405047 : Blo 1580488 27405047 := bstep (se 1 (by rfl) ⟨20553785, by rfl⟩ : syracuseStep 27405047 = 41107571) B41107571
theorem B3558185 : Blo 1580488 3558185 := bstep (se 2 (by rfl) ⟨1334319, by rfl⟩ : syracuseStep 3558185 = 2668639) B2668639
theorem B6409081 : Blo 1580488 6409081 := bstep (se 2 (by rfl) ⟨2403405, by rfl⟩ : syracuseStep 6409081 = 4806811) B4806811
theorem B60820469 : Blo 1580488 60820469 := bstep (se 5 (by rfl) ⟨2850959, by rfl⟩ : syracuseStep 60820469 = 5701919) B5701919
theorem B6007841 : Blo 1580488 6007841 := bstep (se 2 (by rfl) ⟨2252940, by rfl⟩ : syracuseStep 6007841 = 4505881) B4505881
theorem B3558455 : Blo 1580488 3558455 := bstep (se 1 (by rfl) ⟨2668841, by rfl⟩ : syracuseStep 3558455 = 5337683) B5337683
theorem B9612553 : Blo 1580488 9612553 := bstep (se 2 (by rfl) ⟨3604707, by rfl⟩ : syracuseStep 9612553 = 7209415) B7209415
theorem B4500755 : Blo 1580488 4500755 := bstep (se 1 (by rfl) ⟨3375566, by rfl⟩ : syracuseStep 4500755 = 6751133) B6751133
theorem B12004685 : Blo 1580488 12004685 := bstep (se 3 (by rfl) ⟨2250878, by rfl⟩ : syracuseStep 12004685 = 4501757) B4501757
theorem B3378523 : Blo 1580488 3378523 := bstep (se 1 (by rfl) ⟨2533892, by rfl⟩ : syracuseStep 3378523 = 5067785) B5067785
theorem B3001711 : Blo 1580488 3001711 := bstep (se 1 (by rfl) ⟨2251283, by rfl⟩ : syracuseStep 3001711 = 4502567) B4502567
theorem B2370971 : Blo 1580488 2370971 := bstep (se 1 (by rfl) ⟨1778228, by rfl⟩ : syracuseStep 2370971 = 3556457) B3556457
theorem B3558887 : Blo 1580488 3558887 := bstep (se 1 (by rfl) ⟨2669165, by rfl⟩ : syracuseStep 3558887 = 5338331) B5338331
theorem B6008327 : Blo 1580488 6008327 := bstep (se 1 (by rfl) ⟨4506245, by rfl⟩ : syracuseStep 6008327 = 9012491) B9012491
theorem B4001359 : Blo 1580488 4001359 := bstep (se 1 (by rfl) ⟨3001019, by rfl⟩ : syracuseStep 4001359 = 6002039) B6002039
theorem B13512379 : Blo 1580488 13512379 := bstep (se 1 (by rfl) ⟨10134284, by rfl⟩ : syracuseStep 13512379 = 20268569) B20268569
theorem B7597793 : Blo 1580488 7597793 := bstep (se 2 (by rfl) ⟨2849172, by rfl⟩ : syracuseStep 7597793 = 5698345) B5698345
theorem B10268393 : Blo 1580488 10268393 := bstep (se 2 (by rfl) ⟨3850647, by rfl⟩ : syracuseStep 10268393 = 7701295) B7701295
theorem B207867653 : Blo 1580488 207867653 := bstep (se 4 (by rfl) ⟨19487592, by rfl⟩ : syracuseStep 207867653 = 38975185) B38975185
theorem B2371391 : Blo 1580488 2371391 := bstep (se 1 (by rfl) ⟨1778543, by rfl⟩ : syracuseStep 2371391 = 3557087) B3557087
theorem B2371577 : Blo 1580488 2371577 := bstep (se 2 (by rfl) ⟨889341, by rfl⟩ : syracuseStep 2371577 = 1778683) B1778683
theorem B3559463 : Blo 1580488 3559463 := bstep (se 1 (by rfl) ⟨2669597, by rfl⟩ : syracuseStep 3559463 = 5339195) B5339195
theorem B46198907 : Blo 1580488 46198907 := bstep (se 1 (by rfl) ⟨34649180, by rfl⟩ : syracuseStep 46198907 = 69298361) B69298361
theorem B3559643 : Blo 1580488 3559643 := bstep (se 1 (by rfl) ⟨2669732, by rfl⟩ : syracuseStep 3559643 = 5339465) B5339465
theorem B2371817 : Blo 1580488 2371817 := bstep (se 2 (by rfl) ⟨889431, by rfl⟩ : syracuseStep 2371817 = 1778863) B1778863
theorem B2371943 : Blo 1580488 2371943 := bstep (se 1 (by rfl) ⟨1778957, by rfl⟩ : syracuseStep 2371943 = 3557915) B3557915
theorem B3559913 : Blo 1580488 3559913 := bstep (se 2 (by rfl) ⟨1334967, by rfl⟩ : syracuseStep 3559913 = 2669935) B2669935
theorem B6001235 : Blo 1580488 6001235 := bstep (se 1 (by rfl) ⟨4500926, by rfl⟩ : syracuseStep 6001235 = 9001853) B9001853
theorem B12169835 : Blo 1580488 12169835 := bstep (se 1 (by rfl) ⟨9127376, by rfl⟩ : syracuseStep 12169835 = 18254753) B18254753
theorem B12997259 : Blo 1580488 12997259 := bstep (se 1 (by rfl) ⟨9747944, by rfl⟩ : syracuseStep 12997259 = 19495889) B19495889
theorem B2372489 : Blo 1580488 2372489 := bstep (se 2 (by rfl) ⟨889683, by rfl⟩ : syracuseStep 2372489 = 1779367) B1779367
theorem B7599005 : Blo 1580488 7599005 := bstep (se 3 (by rfl) ⟨1424813, by rfl⟩ : syracuseStep 7599005 = 2849627) B2849627
theorem B3560417 : Blo 1580488 3560417 := bstep (se 2 (by rfl) ⟨1335156, by rfl⟩ : syracuseStep 3560417 = 2670313) B2670313
theorem B3560543 : Blo 1580488 3560543 := bstep (se 1 (by rfl) ⟨2670407, by rfl⟩ : syracuseStep 3560543 = 5340815) B5340815
theorem B6411419 : Blo 1580488 6411419 := bstep (se 1 (by rfl) ⟨4808564, by rfl⟩ : syracuseStep 6411419 = 9617129) B9617129
theorem B8008955 : Blo 1580488 8008955 := bstep (se 1 (by rfl) ⟨6006716, by rfl⟩ : syracuseStep 8008955 = 12013433) B12013433
theorem B2372873 : Blo 1580488 2372873 := bstep (se 2 (by rfl) ⟨889827, by rfl⟩ : syracuseStep 2372873 = 1779655) B1779655
theorem B2372927 : Blo 1580488 2372927 := bstep (se 1 (by rfl) ⟨1779695, by rfl⟩ : syracuseStep 2372927 = 3559391) B3559391
theorem B4003303 : Blo 1580488 4003303 := bstep (se 1 (by rfl) ⟨3002477, by rfl⟩ : syracuseStep 4003303 = 6004955) B6004955
theorem B5068271 : Blo 1580488 5068271 := bstep (se 1 (by rfl) ⟨3801203, by rfl⟩ : syracuseStep 5068271 = 7602407) B7602407
theorem B13514363 : Blo 1580488 13514363 := bstep (se 1 (by rfl) ⟨10135772, by rfl⟩ : syracuseStep 13514363 = 20271545) B20271545
theorem B12007115 : Blo 1580488 12007115 := bstep (se 1 (by rfl) ⟨9005336, by rfl⟩ : syracuseStep 12007115 = 18010673) B18010673
theorem B2373353 : Blo 1580488 2373353 := bstep (se 2 (by rfl) ⟨890007, by rfl⟩ : syracuseStep 2373353 = 1780015) B1780015
theorem B2373359 : Blo 1580488 2373359 := bstep (se 1 (by rfl) ⟨1780019, by rfl⟩ : syracuseStep 2373359 = 3560039) B3560039
theorem B6002495 : Blo 1580488 6002495 := bstep (se 1 (by rfl) ⟨4501871, by rfl⟩ : syracuseStep 6002495 = 9003743) B9003743
theorem B2668585 : Blo 1580488 2668585 := bstep (se 2 (by rfl) ⟨1000719, by rfl⟩ : syracuseStep 2668585 = 2001439) B2001439
theorem B2668727 : Blo 1580488 2668727 := bstep (se 1 (by rfl) ⟨2001545, by rfl⟩ : syracuseStep 2668727 = 4003091) B4003091
theorem B7600331 : Blo 1580488 7600331 := bstep (se 1 (by rfl) ⟨5700248, by rfl⟩ : syracuseStep 7600331 = 11400497) B11400497
theorem B17094995 : Blo 1580488 17094995 := bstep (se 1 (by rfl) ⟨12821246, by rfl⟩ : syracuseStep 17094995 = 25642493) B25642493
theorem B7215455 : Blo 1580488 7215455 := bstep (se 1 (by rfl) ⟨5411591, by rfl⟩ : syracuseStep 7215455 = 10823183) B10823183
theorem B2849231 : Blo 1580488 2849231 := bstep (se 1 (by rfl) ⟨2136923, by rfl⟩ : syracuseStep 2849231 = 4273847) B4273847
theorem B4504207 : Blo 1580488 4504207 := bstep (se 1 (by rfl) ⟨3378155, by rfl⟩ : syracuseStep 4504207 = 6756311) B6756311
theorem B2669321 : Blo 1580488 2669321 := bstep (se 2 (by rfl) ⟨1000995, by rfl⟩ : syracuseStep 2669321 = 2001991) B2001991
theorem B6003467 : Blo 1580488 6003467 := bstep (se 1 (by rfl) ⟨4502600, by rfl⟩ : syracuseStep 6003467 = 9005201) B9005201
theorem B10132235 : Blo 1580488 10132235 := bstep (se 1 (by rfl) ⟨7599176, by rfl⟩ : syracuseStep 10132235 = 15198353) B15198353
theorem B11401993 : Blo 1580488 11401993 := bstep (se 2 (by rfl) ⟨4275747, by rfl⟩ : syracuseStep 11401993 = 8551495) B8551495
theorem B10271719 : Blo 1580488 10271719 := bstep (se 1 (by rfl) ⟨7703789, by rfl⟩ : syracuseStep 10271719 = 15407579) B15407579
theorem B8010899 : Blo 1580488 8010899 := bstep (se 1 (by rfl) ⟨6008174, by rfl⟩ : syracuseStep 8010899 = 12016349) B12016349
theorem B5340383 : Blo 1580488 5340383 := bstep (se 1 (by rfl) ⟨4005287, by rfl⟩ : syracuseStep 5340383 = 8010575) B8010575
theorem B1580495 : Blo 1580488 1580495 := bstep (se 1 (by rfl) ⟨1185371, by rfl⟩ : syracuseStep 1580495 = 2370743) B2370743
theorem B1580655 : Blo 1580488 1580655 := bstep (se 1 (by rfl) ⟨1185491, by rfl⟩ : syracuseStep 1580655 = 2370983) B2370983
theorem B1580711 : Blo 1580488 1580711 := bstep (se 1 (by rfl) ⟨1185533, by rfl⟩ : syracuseStep 1580711 = 2371067) B2371067
theorem B4505311 : Blo 1580488 4505311 := bstep (se 1 (by rfl) ⟨3378983, by rfl⟩ : syracuseStep 4505311 = 6757967) B6757967
theorem B1580775 : Blo 1580488 1580775 := bstep (se 1 (by rfl) ⟨1185581, by rfl⟩ : syracuseStep 1580775 = 2371163) B2371163
theorem B1580831 : Blo 1580488 1580831 := bstep (se 1 (by rfl) ⟨1185623, by rfl⟩ : syracuseStep 1580831 = 2371247) B2371247
theorem B1580911 : Blo 1580488 1580911 := bstep (se 1 (by rfl) ⟨1185683, by rfl⟩ : syracuseStep 1580911 = 2371367) B2371367
theorem B1580967 : Blo 1580488 1580967 := bstep (se 1 (by rfl) ⟨1185725, by rfl⟩ : syracuseStep 1580967 = 2371451) B2371451
theorem B6004651 : Blo 1580488 6004651 := bstep (se 1 (by rfl) ⟨4503488, by rfl⟩ : syracuseStep 6004651 = 9006977) B9006977
theorem B18022337 : Blo 1580488 18022337 := bstep (se 2 (by rfl) ⟨6758376, by rfl⟩ : syracuseStep 18022337 = 13516753) B13516753
theorem B25649297 : Blo 1580488 25649297 := bstep (se 2 (by rfl) ⟨9618486, by rfl⟩ : syracuseStep 25649297 = 19236973) B19236973
theorem B1581211 : Blo 1580488 1581211 := bstep (se 1 (by rfl) ⟨1185908, by rfl⟩ : syracuseStep 1581211 = 2371817) B2371817
theorem B1581295 : Blo 1580488 1581295 := bstep (se 1 (by rfl) ⟨1185971, by rfl⟩ : syracuseStep 1581295 = 2371943) B2371943
theorem B1581659 : Blo 1580488 1581659 := bstep (se 1 (by rfl) ⟨1186244, by rfl⟩ : syracuseStep 1581659 = 2372489) B2372489
theorem B9011807 : Blo 1580488 9011807 := bstep (se 1 (by rfl) ⟨6758855, by rfl⟩ : syracuseStep 9011807 = 13517711) B13517711
theorem B1581915 : Blo 1580488 1581915 := bstep (se 1 (by rfl) ⟨1186436, by rfl⟩ : syracuseStep 1581915 = 2372873) B2372873
theorem B6005609 : Blo 1580488 6005609 := bstep (se 2 (by rfl) ⟨2252103, by rfl⟩ : syracuseStep 6005609 = 4504207) B4504207
theorem B1581951 : Blo 1580488 1581951 := bstep (se 1 (by rfl) ⟨1186463, by rfl⟩ : syracuseStep 1581951 = 2372927) B2372927
theorem B8004743 : Blo 1580488 8004743 := bstep (se 1 (by rfl) ⟨6003557, by rfl⟩ : syracuseStep 8004743 = 12007115) B12007115
theorem B1582235 : Blo 1580488 1582235 := bstep (se 1 (by rfl) ⟨1186676, by rfl⟩ : syracuseStep 1582235 = 2373353) B2373353
theorem B1582239 : Blo 1580488 1582239 := bstep (se 1 (by rfl) ⟨1186679, by rfl⟩ : syracuseStep 1582239 = 2373359) B2373359
theorem B8545441 : Blo 1580488 8545441 := bstep (se 2 (by rfl) ⟨3204540, by rfl⟩ : syracuseStep 8545441 = 6409081) B6409081
theorem B5702831 : Blo 1580488 5702831 := bstep (se 1 (by rfl) ⟨4277123, by rfl⟩ : syracuseStep 5702831 = 8554247) B8554247
theorem B3376379 : Blo 1580488 3376379 := bstep (se 1 (by rfl) ⟨2532284, by rfl⟩ : syracuseStep 3376379 = 5064569) B5064569
theorem B1779151 : Blo 1580488 1779151 := bstep (se 1 (by rfl) ⟨1334363, by rfl⟩ : syracuseStep 1779151 = 2668727) B2668727
theorem B11396663 : Blo 1580488 11396663 := bstep (se 1 (by rfl) ⟨8547497, by rfl⟩ : syracuseStep 11396663 = 17094995) B17094995
theorem B4810303 : Blo 1580488 4810303 := bstep (se 1 (by rfl) ⟨3607727, by rfl⟩ : syracuseStep 4810303 = 7215455) B7215455
theorem B18270031 : Blo 1580488 18270031 := bstep (se 1 (by rfl) ⟨13702523, by rfl⟩ : syracuseStep 18270031 = 27405047) B27405047
theorem B1779547 : Blo 1580488 1779547 := bstep (se 1 (by rfl) ⟨1334660, by rfl⟩ : syracuseStep 1779547 = 2669321) B2669321
theorem B5335145 : Blo 1580488 5335145 := bstep (se 2 (by rfl) ⟨2000679, by rfl⟩ : syracuseStep 5335145 = 4001359) B4001359
theorem B3000503 : Blo 1580488 3000503 := bstep (se 1 (by rfl) ⟨2250377, by rfl⟩ : syracuseStep 3000503 = 4500755) B4500755
theorem B18016505 : Blo 1580488 18016505 := bstep (se 2 (by rfl) ⟨6756189, by rfl⟩ : syracuseStep 18016505 = 13512379) B13512379
theorem B6007081 : Blo 1580488 6007081 := bstep (se 2 (by rfl) ⟨2252655, by rfl⟩ : syracuseStep 6007081 = 4505311) B4505311
theorem B5065195 : Blo 1580488 5065195 := bstep (se 1 (by rfl) ⟨3798896, by rfl⟩ : syracuseStep 5065195 = 7597793) B7597793
theorem B138578435 : Blo 1580488 138578435 := bstep (se 1 (by rfl) ⟨103933826, by rfl⟩ : syracuseStep 138578435 = 207867653) B207867653
theorem B8006201 : Blo 1580488 8006201 := bstep (se 2 (by rfl) ⟨3002325, by rfl⟩ : syracuseStep 8006201 = 6004651) B6004651
theorem B3558113 : Blo 1580488 3558113 := bstep (se 2 (by rfl) ⟨1334292, by rfl⟩ : syracuseStep 3558113 = 2668585) B2668585
theorem B4000823 : Blo 1580488 4000823 := bstep (se 1 (by rfl) ⟨3000617, by rfl⟩ : syracuseStep 4000823 = 6001235) B6001235
theorem B8113223 : Blo 1580488 8113223 := bstep (se 1 (by rfl) ⟨6084917, by rfl⟩ : syracuseStep 8113223 = 12169835) B12169835
theorem B4000873 : Blo 1580488 4000873 := bstep (se 2 (by rfl) ⟨1500327, by rfl⟩ : syracuseStep 4000873 = 3000655) B3000655
theorem B7597331 : Blo 1580488 7597331 := bstep (se 1 (by rfl) ⟨5697998, by rfl⟩ : syracuseStep 7597331 = 11395997) B11395997
theorem B5066003 : Blo 1580488 5066003 := bstep (se 1 (by rfl) ⟨3799502, by rfl⟩ : syracuseStep 5066003 = 7599005) B7599005
theorem B2370863 : Blo 1580488 2370863 := bstep (se 1 (by rfl) ⟨1778147, by rfl⟩ : syracuseStep 2370863 = 3556295) B3556295
theorem B3378505 : Blo 1580488 3378505 := bstep (se 2 (by rfl) ⟨1266939, by rfl⟩ : syracuseStep 3378505 = 2533879) B2533879
theorem B2371049 : Blo 1580488 2371049 := bstep (se 2 (by rfl) ⟨889143, by rfl⟩ : syracuseStep 2371049 = 1778287) B1778287
theorem B2371103 : Blo 1580488 2371103 := bstep (se 1 (by rfl) ⟨1778327, by rfl⟩ : syracuseStep 2371103 = 3556655) B3556655
theorem B2371193 : Blo 1580488 2371193 := bstep (se 2 (by rfl) ⟨889197, by rfl⟩ : syracuseStep 2371193 = 1778395) B1778395
theorem B3378847 : Blo 1580488 3378847 := bstep (se 1 (by rfl) ⟨2534135, by rfl⟩ : syracuseStep 3378847 = 5068271) B5068271
theorem B2371439 : Blo 1580488 2371439 := bstep (se 1 (by rfl) ⟨1778579, by rfl⟩ : syracuseStep 2371439 = 3557159) B3557159
theorem B4001663 : Blo 1580488 4001663 := bstep (se 1 (by rfl) ⟨3001247, by rfl⟩ : syracuseStep 4001663 = 6002495) B6002495
theorem B2371691 : Blo 1580488 2371691 := bstep (se 1 (by rfl) ⟨1778768, by rfl⟩ : syracuseStep 2371691 = 3557537) B3557537
theorem B5066887 : Blo 1580488 5066887 := bstep (se 1 (by rfl) ⟨3800165, by rfl⟩ : syracuseStep 5066887 = 7600331) B7600331
theorem B12816737 : Blo 1580488 12816737 := bstep (se 2 (by rfl) ⟨4806276, by rfl⟩ : syracuseStep 12816737 = 9612553) B9612553
theorem B4002281 : Blo 1580488 4002281 := bstep (se 2 (by rfl) ⟨1500855, by rfl⟩ : syracuseStep 4002281 = 3001711) B3001711
theorem B4002311 : Blo 1580488 4002311 := bstep (se 1 (by rfl) ⟨3001733, by rfl⟩ : syracuseStep 4002311 = 6003467) B6003467
theorem B6754823 : Blo 1580488 6754823 := bstep (se 1 (by rfl) ⟨5066117, by rfl⟩ : syracuseStep 6754823 = 10132235) B10132235
theorem B2372123 : Blo 1580488 2372123 := bstep (se 1 (by rfl) ⟨1779092, by rfl⟩ : syracuseStep 2372123 = 3558185) B3558185
theorem B27382381 : Blo 1580488 27382381 := bstep (se 3 (by rfl) ⟨5134196, by rfl⟩ : syracuseStep 27382381 = 10268393) B10268393
theorem B5337737 : Blo 1580488 5337737 := bstep (se 2 (by rfl) ⟨2001651, by rfl⟩ : syracuseStep 5337737 = 4003303) B4003303
theorem B40546979 : Blo 1580488 40546979 := bstep (se 1 (by rfl) ⟨30410234, by rfl⟩ : syracuseStep 40546979 = 60820469) B60820469
theorem B2372303 : Blo 1580488 2372303 := bstep (se 1 (by rfl) ⟨1779227, by rfl⟩ : syracuseStep 2372303 = 3558455) B3558455
theorem B3560255 : Blo 1580488 3560255 := bstep (se 1 (by rfl) ⟨2670191, by rfl⟩ : syracuseStep 3560255 = 5340383) B5340383
theorem B4502441 : Blo 1580488 4502441 := bstep (se 2 (by rfl) ⟨1688415, by rfl⟩ : syracuseStep 4502441 = 3376831) B3376831
theorem B2372591 : Blo 1580488 2372591 := bstep (se 1 (by rfl) ⟨1779443, by rfl⟩ : syracuseStep 2372591 = 3558887) B3558887
theorem B12014891 : Blo 1580488 12014891 := bstep (se 1 (by rfl) ⟨9011168, by rfl⟩ : syracuseStep 12014891 = 18022337) B18022337
theorem B2372975 : Blo 1580488 2372975 := bstep (se 1 (by rfl) ⟨1779731, by rfl⟩ : syracuseStep 2372975 = 3559463) B3559463
theorem B30799271 : Blo 1580488 30799271 := bstep (se 1 (by rfl) ⟨23099453, by rfl⟩ : syracuseStep 30799271 = 46198907) B46198907
theorem B4003283 : Blo 1580488 4003283 := bstep (se 1 (by rfl) ⟨3002462, by rfl⟩ : syracuseStep 4003283 = 6004925) B6004925
theorem B10130903 : Blo 1580488 10130903 := bstep (se 1 (by rfl) ⟨7598177, by rfl⟩ : syracuseStep 10130903 = 15196355) B15196355
theorem B2373095 : Blo 1580488 2373095 := bstep (se 1 (by rfl) ⟨1779821, by rfl⟩ : syracuseStep 2373095 = 3559643) B3559643
theorem B3905023 : Blo 1580488 3905023 := bstep (se 1 (by rfl) ⟨2928767, by rfl⟩ : syracuseStep 3905023 = 5857535) B5857535
theorem B28513901 : Blo 1580488 28513901 := bstep (se 3 (by rfl) ⟨5346356, by rfl⟩ : syracuseStep 28513901 = 10692713) B10692713
theorem B2373275 : Blo 1580488 2373275 := bstep (se 1 (by rfl) ⟨1779956, by rfl⟩ : syracuseStep 2373275 = 3559913) B3559913
theorem B8664839 : Blo 1580488 8664839 := bstep (se 1 (by rfl) ⟨6498629, by rfl⟩ : syracuseStep 8664839 = 12997259) B12997259
theorem B10131263 : Blo 1580488 10131263 := bstep (se 1 (by rfl) ⟨7598447, by rfl⟩ : syracuseStep 10131263 = 15196895) B15196895
theorem B5068669 : Blo 1580488 5068669 := bstep (se 3 (by rfl) ⟨950375, by rfl⟩ : syracuseStep 5068669 = 1900751) B1900751
theorem B2373611 : Blo 1580488 2373611 := bstep (se 1 (by rfl) ⟨1780208, by rfl⟩ : syracuseStep 2373611 = 3560417) B3560417
theorem B24336395 : Blo 1580488 24336395 := bstep (se 1 (by rfl) ⟨18252296, by rfl⟩ : syracuseStep 24336395 = 36504593) B36504593
theorem B2373695 : Blo 1580488 2373695 := bstep (se 1 (by rfl) ⟨1780271, by rfl⟩ : syracuseStep 2373695 = 3560543) B3560543
theorem B4274279 : Blo 1580488 4274279 := bstep (se 1 (by rfl) ⟨3205709, by rfl⟩ : syracuseStep 4274279 = 6411419) B6411419
theorem B6756463 : Blo 1580488 6756463 := bstep (se 1 (by rfl) ⟨5067347, by rfl⟩ : syracuseStep 6756463 = 10134695) B10134695
theorem B4003951 : Blo 1580488 4003951 := bstep (se 1 (by rfl) ⟨3002963, by rfl⟩ : syracuseStep 4003951 = 6005927) B6005927
theorem B5339303 : Blo 1580488 5339303 := bstep (se 1 (by rfl) ⟨4004477, by rfl⟩ : syracuseStep 5339303 = 8008955) B8008955
theorem B2889911 : Blo 1580488 2889911 := bstep (se 1 (by rfl) ⟨2167433, by rfl⟩ : syracuseStep 2889911 = 4334867) B4334867
theorem B10131803 : Blo 1580488 10131803 := bstep (se 1 (by rfl) ⟨7598852, by rfl⟩ : syracuseStep 10131803 = 15197705) B15197705
theorem B15202657 : Blo 1580488 15202657 := bstep (se 2 (by rfl) ⟨5700996, by rfl⟩ : syracuseStep 15202657 = 11401993) B11401993
theorem B9009575 : Blo 1580488 9009575 := bstep (se 1 (by rfl) ⟨6757181, by rfl⟩ : syracuseStep 9009575 = 13514363) B13514363
theorem B13695625 : Blo 1580488 13695625 := bstep (se 2 (by rfl) ⟨5135859, by rfl⟩ : syracuseStep 13695625 = 10271719) B10271719
theorem B1899487 : Blo 1580488 1899487 := bstep (se 1 (by rfl) ⟨1424615, by rfl⟩ : syracuseStep 1899487 = 2849231) B2849231
theorem B30383171 : Blo 1580488 30383171 := bstep (se 1 (by rfl) ⟨22787378, by rfl⟩ : syracuseStep 30383171 = 45574757) B45574757
theorem B4504697 : Blo 1580488 4504697 := bstep (se 2 (by rfl) ⟨1689261, by rfl⟩ : syracuseStep 4504697 = 3378523) B3378523
theorem B4005227 : Blo 1580488 4005227 := bstep (se 1 (by rfl) ⟨3003920, by rfl⟩ : syracuseStep 4005227 = 6007841) B6007841
theorem B5340599 : Blo 1580488 5340599 := bstep (se 1 (by rfl) ⟨4005449, by rfl⟩ : syracuseStep 5340599 = 8010899) B8010899
theorem B8003123 : Blo 1580488 8003123 := bstep (se 1 (by rfl) ⟨6002342, by rfl⟩ : syracuseStep 8003123 = 12004685) B12004685
theorem B1580647 : Blo 1580488 1580647 := bstep (se 1 (by rfl) ⟨1185485, by rfl⟩ : syracuseStep 1580647 = 2370971) B2370971
theorem B4005551 : Blo 1580488 4005551 := bstep (se 1 (by rfl) ⟨3004163, by rfl⟩ : syracuseStep 4005551 = 6008327) B6008327
theorem B1580927 : Blo 1580488 1580927 := bstep (se 1 (by rfl) ⟨1185695, by rfl⟩ : syracuseStep 1580927 = 2371391) B2371391
theorem B2252713 : Blo 1580488 2252713 := bstep (se 2 (by rfl) ⟨844767, by rfl⟩ : syracuseStep 2252713 = 1689535) B1689535
theorem B1581051 : Blo 1580488 1581051 := bstep (se 1 (by rfl) ⟨1185788, by rfl⟩ : syracuseStep 1581051 = 2371577) B2371577
theorem B1581127 : Blo 1580488 1581127 := bstep (se 1 (by rfl) ⟨1185845, by rfl⟩ : syracuseStep 1581127 = 2371691) B2371691
theorem B21635261 : Blo 1580488 21635261 := bstep (se 3 (by rfl) ⟨4056611, by rfl⟩ : syracuseStep 21635261 = 8113223) B8113223
theorem B8544491 : Blo 1580488 8544491 := bstep (se 1 (by rfl) ⟨6408368, by rfl⟩ : syracuseStep 8544491 = 12816737) B12816737
theorem B1581415 : Blo 1580488 1581415 := bstep (se 1 (by rfl) ⟨1186061, by rfl⟩ : syracuseStep 1581415 = 2372123) B2372123
theorem B1581535 : Blo 1580488 1581535 := bstep (se 1 (by rfl) ⟨1186151, by rfl⟩ : syracuseStep 1581535 = 2372303) B2372303
theorem B146039365 : Blo 1580488 146039365 := bstep (se 4 (by rfl) ⟨13691190, by rfl⟩ : syracuseStep 146039365 = 27382381) B27382381
theorem B1581727 : Blo 1580488 1581727 := bstep (se 1 (by rfl) ⟨1186295, by rfl⟩ : syracuseStep 1581727 = 2372591) B2372591
theorem B13509341 : Blo 1580488 13509341 := bstep (se 3 (by rfl) ⟨2533001, by rfl⟩ : syracuseStep 13509341 = 5066003) B5066003
theorem B3801887 : Blo 1580488 3801887 := bstep (se 1 (by rfl) ⟨2851415, by rfl⟩ : syracuseStep 3801887 = 5702831) B5702831
theorem B1581983 : Blo 1580488 1581983 := bstep (se 1 (by rfl) ⟨1186487, by rfl⟩ : syracuseStep 1581983 = 2372975) B2372975
theorem B1582063 : Blo 1580488 1582063 := bstep (se 1 (by rfl) ⟨1186547, by rfl⟩ : syracuseStep 1582063 = 2373095) B2373095
theorem B1582183 : Blo 1580488 1582183 := bstep (se 1 (by rfl) ⟨1186637, by rfl⟩ : syracuseStep 1582183 = 2373275) B2373275
theorem B5776559 : Blo 1580488 5776559 := bstep (se 1 (by rfl) ⟨4332419, by rfl⟩ : syracuseStep 5776559 = 8664839) B8664839
theorem B2532649 : Blo 1580488 2532649 := bstep (se 2 (by rfl) ⟨949743, by rfl⟩ : syracuseStep 2532649 = 1899487) B1899487
theorem B1582407 : Blo 1580488 1582407 := bstep (se 1 (by rfl) ⟨1186805, by rfl⟩ : syracuseStep 1582407 = 2373611) B2373611
theorem B1582463 : Blo 1580488 1582463 := bstep (se 1 (by rfl) ⟨1186847, by rfl⟩ : syracuseStep 1582463 = 2373695) B2373695
theorem B3556763 : Blo 1580488 3556763 := bstep (se 1 (by rfl) ⟨2667572, by rfl⟩ : syracuseStep 3556763 = 5335145) B5335145
theorem B1926607 : Blo 1580488 1926607 := bstep (se 1 (by rfl) ⟨1444955, by rfl⟩ : syracuseStep 1926607 = 2889911) B2889911
theorem B5334497 : Blo 1580488 5334497 := bstep (se 2 (by rfl) ⟨2000436, by rfl⟩ : syracuseStep 5334497 = 4000873) B4000873
theorem B12011003 : Blo 1580488 12011003 := bstep (se 1 (by rfl) ⟨9008252, by rfl⟩ : syracuseStep 12011003 = 18016505) B18016505
theorem B6006383 : Blo 1580488 6006383 := bstep (se 1 (by rfl) ⟨4504787, by rfl⟩ : syracuseStep 6006383 = 9009575) B9009575
theorem B5064887 : Blo 1580488 5064887 := bstep (se 1 (by rfl) ⟨3798665, by rfl⟩ : syracuseStep 5064887 = 7597331) B7597331
theorem B5335415 : Blo 1580488 5335415 := bstep (se 1 (by rfl) ⟨4001561, by rfl⟩ : syracuseStep 5335415 = 8003123) B8003123
theorem B17099531 : Blo 1580488 17099531 := bstep (se 1 (by rfl) ⟨12824648, by rfl⟩ : syracuseStep 17099531 = 25649297) B25649297
theorem B6007871 : Blo 1580488 6007871 := bstep (se 1 (by rfl) ⟨4505903, by rfl⟩ : syracuseStep 6007871 = 9011807) B9011807
theorem B3558491 : Blo 1580488 3558491 := bstep (se 1 (by rfl) ⟨2668868, by rfl⟩ : syracuseStep 3558491 = 5337737) B5337737
theorem B20270209 : Blo 1580488 20270209 := bstep (se 2 (by rfl) ⟨7601328, by rfl⟩ : syracuseStep 20270209 = 15202657) B15202657
theorem B3001627 : Blo 1580488 3001627 := bstep (se 1 (by rfl) ⟨2251220, by rfl⟩ : syracuseStep 3001627 = 4502441) B4502441
theorem B6753593 : Blo 1580488 6753593 := bstep (se 2 (by rfl) ⟨2532597, by rfl⟩ : syracuseStep 6753593 = 5065195) B5065195
theorem B73043333 : Blo 1580488 73043333 := bstep (se 4 (by rfl) ⟨6847812, by rfl⟩ : syracuseStep 73043333 = 13695625) B13695625
theorem B5336495 : Blo 1580488 5336495 := bstep (se 1 (by rfl) ⟨4002371, by rfl⟩ : syracuseStep 5336495 = 8004743) B8004743
theorem B20532847 : Blo 1580488 20532847 := bstep (se 1 (by rfl) ⟨15399635, by rfl⟩ : syracuseStep 20532847 = 30799271) B30799271
theorem B6753935 : Blo 1580488 6753935 := bstep (se 1 (by rfl) ⟨5065451, by rfl⟩ : syracuseStep 6753935 = 10130903) B10130903
theorem B7597775 : Blo 1580488 7597775 := bstep (se 1 (by rfl) ⟨5698331, by rfl⟩ : syracuseStep 7597775 = 11396663) B11396663
theorem B6754175 : Blo 1580488 6754175 := bstep (se 1 (by rfl) ⟨5065631, by rfl⟩ : syracuseStep 6754175 = 10131263) B10131263
theorem B16224263 : Blo 1580488 16224263 := bstep (se 1 (by rfl) ⟨12168197, by rfl⟩ : syracuseStep 16224263 = 24336395) B24336395
theorem B3559535 : Blo 1580488 3559535 := bstep (se 1 (by rfl) ⟨2669651, by rfl⟩ : syracuseStep 3559535 = 5339303) B5339303
theorem B6754535 : Blo 1580488 6754535 := bstep (se 1 (by rfl) ⟨5065901, by rfl⟩ : syracuseStep 6754535 = 10131803) B10131803
theorem B92385623 : Blo 1580488 92385623 := bstep (se 1 (by rfl) ⟨69289217, by rfl⟩ : syracuseStep 92385623 = 138578435) B138578435
theorem B5337467 : Blo 1580488 5337467 := bstep (se 1 (by rfl) ⟨4003100, by rfl⟩ : syracuseStep 5337467 = 8006201) B8006201
theorem B2372075 : Blo 1580488 2372075 := bstep (se 1 (by rfl) ⟨1779056, by rfl⟩ : syracuseStep 2372075 = 3558113) B3558113
theorem B2372201 : Blo 1580488 2372201 := bstep (se 2 (by rfl) ⟨889575, by rfl⟩ : syracuseStep 2372201 = 1779151) B1779151
theorem B5206697 : Blo 1580488 5206697 := bstep (se 2 (by rfl) ⟨1952511, by rfl⟩ : syracuseStep 5206697 = 3905023) B3905023
theorem B2667215 : Blo 1580488 2667215 := bstep (se 1 (by rfl) ⟨2000411, by rfl⟩ : syracuseStep 2667215 = 4000823) B4000823
theorem B20255447 : Blo 1580488 20255447 := bstep (se 1 (by rfl) ⟨15191585, by rfl⟩ : syracuseStep 20255447 = 30383171) B30383171
theorem B3003131 : Blo 1580488 3003131 := bstep (se 1 (by rfl) ⟨2252348, by rfl⟩ : syracuseStep 3003131 = 4504697) B4504697
theorem B3560399 : Blo 1580488 3560399 := bstep (se 1 (by rfl) ⟨2670299, by rfl⟩ : syracuseStep 3560399 = 5340599) B5340599
theorem B24360041 : Blo 1580488 24360041 := bstep (se 2 (by rfl) ⟨9135015, by rfl⟩ : syracuseStep 24360041 = 18270031) B18270031
theorem B2372729 : Blo 1580488 2372729 := bstep (se 2 (by rfl) ⟨889773, by rfl⟩ : syracuseStep 2372729 = 1779547) B1779547
theorem B3003617 : Blo 1580488 3003617 := bstep (se 2 (by rfl) ⟨1126356, by rfl⟩ : syracuseStep 3003617 = 2252713) B2252713
theorem B2667775 : Blo 1580488 2667775 := bstep (se 1 (by rfl) ⟨2000831, by rfl⟩ : syracuseStep 2667775 = 4001663) B4001663
theorem B9008617 : Blo 1580488 9008617 := bstep (se 2 (by rfl) ⟨3378231, by rfl⟩ : syracuseStep 9008617 = 6756463) B6756463
theorem B5338601 : Blo 1580488 5338601 := bstep (se 2 (by rfl) ⟨2001975, by rfl⟩ : syracuseStep 5338601 = 4003951) B4003951
theorem B6755849 : Blo 1580488 6755849 := bstep (se 2 (by rfl) ⟨2533443, by rfl⟩ : syracuseStep 6755849 = 5066887) B5066887
theorem B2668187 : Blo 1580488 2668187 := bstep (se 1 (by rfl) ⟨2001140, by rfl⟩ : syracuseStep 2668187 = 4002281) B4002281
theorem B2668207 : Blo 1580488 2668207 := bstep (se 1 (by rfl) ⟨2001155, by rfl⟩ : syracuseStep 2668207 = 4002311) B4002311
theorem B4503215 : Blo 1580488 4503215 := bstep (se 1 (by rfl) ⟨3377411, by rfl⟩ : syracuseStep 4503215 = 6754823) B6754823
theorem B8009441 : Blo 1580488 8009441 := bstep (se 2 (by rfl) ⟨3003540, by rfl⟩ : syracuseStep 8009441 = 6007081) B6007081
theorem B27031319 : Blo 1580488 27031319 := bstep (se 1 (by rfl) ⟨20273489, by rfl⟩ : syracuseStep 27031319 = 40546979) B40546979
theorem B8001341 : Blo 1580488 8001341 := bstep (se 3 (by rfl) ⟨1500251, by rfl⟩ : syracuseStep 8001341 = 3000503) B3000503
theorem B2373503 : Blo 1580488 2373503 := bstep (se 1 (by rfl) ⟨1780127, by rfl⟩ : syracuseStep 2373503 = 3560255) B3560255
theorem B4003739 : Blo 1580488 4003739 := bstep (se 1 (by rfl) ⟨3002804, by rfl⟩ : syracuseStep 4003739 = 6005609) B6005609
theorem B2250919 : Blo 1580488 2250919 := bstep (se 1 (by rfl) ⟨1688189, by rfl⟩ : syracuseStep 2250919 = 3376379) B3376379
theorem B8009927 : Blo 1580488 8009927 := bstep (se 1 (by rfl) ⟨6007445, by rfl⟩ : syracuseStep 8009927 = 12014891) B12014891
theorem B2668855 : Blo 1580488 2668855 := bstep (se 1 (by rfl) ⟨2001641, by rfl⟩ : syracuseStep 2668855 = 4003283) B4003283
theorem B2849519 : Blo 1580488 2849519 := bstep (se 1 (by rfl) ⟨2137139, by rfl⟩ : syracuseStep 2849519 = 4274279) B4274279
theorem B11393921 : Blo 1580488 11393921 := bstep (se 2 (by rfl) ⟨4272720, by rfl⟩ : syracuseStep 11393921 = 8545441) B8545441
theorem B76037069 : Blo 1580488 76037069 := bstep (se 3 (by rfl) ⟨14256950, by rfl⟩ : syracuseStep 76037069 = 28513901) B28513901
theorem B4504673 : Blo 1580488 4504673 := bstep (se 2 (by rfl) ⟨1689252, by rfl⟩ : syracuseStep 4504673 = 3378505) B3378505
theorem B6413737 : Blo 1580488 6413737 := bstep (se 2 (by rfl) ⟨2405151, by rfl⟩ : syracuseStep 6413737 = 4810303) B4810303
theorem B1580575 : Blo 1580488 1580575 := bstep (se 1 (by rfl) ⟨1185431, by rfl⟩ : syracuseStep 1580575 = 2370863) B2370863
theorem B4505129 : Blo 1580488 4505129 := bstep (se 2 (by rfl) ⟨1689423, by rfl⟩ : syracuseStep 4505129 = 3378847) B3378847
theorem B2670151 : Blo 1580488 2670151 := bstep (se 1 (by rfl) ⟨2002613, by rfl⟩ : syracuseStep 2670151 = 4005227) B4005227
theorem B1580699 : Blo 1580488 1580699 := bstep (se 1 (by rfl) ⟨1185524, by rfl⟩ : syracuseStep 1580699 = 2371049) B2371049
theorem B1580735 : Blo 1580488 1580735 := bstep (se 1 (by rfl) ⟨1185551, by rfl⟩ : syracuseStep 1580735 = 2371103) B2371103
theorem B1580795 : Blo 1580488 1580795 := bstep (se 1 (by rfl) ⟨1185596, by rfl⟩ : syracuseStep 1580795 = 2371193) B2371193
theorem B2670367 : Blo 1580488 2670367 := bstep (se 1 (by rfl) ⟨2002775, by rfl⟩ : syracuseStep 2670367 = 4005551) B4005551
theorem B6758225 : Blo 1580488 6758225 := bstep (se 2 (by rfl) ⟨2534334, by rfl⟩ : syracuseStep 6758225 = 5068669) B5068669
theorem B1580959 : Blo 1580488 1580959 := bstep (se 1 (by rfl) ⟨1185719, by rfl⟩ : syracuseStep 1580959 = 2371439) B2371439
theorem B1581383 : Blo 1580488 1581383 := bstep (se 1 (by rfl) ⟨1186037, by rfl⟩ : syracuseStep 1581383 = 2372075) B2372075
theorem B1581467 : Blo 1580488 1581467 := bstep (se 1 (by rfl) ⟨1186100, by rfl⟩ : syracuseStep 1581467 = 2372201) B2372201
theorem B1778143 : Blo 1580488 1778143 := bstep (se 1 (by rfl) ⟨1333607, by rfl⟩ : syracuseStep 1778143 = 2667215) B2667215
theorem B1581819 : Blo 1580488 1581819 := bstep (se 1 (by rfl) ⟨1186364, by rfl⟩ : syracuseStep 1581819 = 2372729) B2372729
theorem B3851039 : Blo 1580488 3851039 := bstep (se 1 (by rfl) ⟨2888279, by rfl⟩ : syracuseStep 3851039 = 5776559) B5776559
theorem B3556331 : Blo 1580488 3556331 := bstep (se 1 (by rfl) ⟨2667248, by rfl⟩ : syracuseStep 3556331 = 5334497) B5334497
theorem B1778791 : Blo 1580488 1778791 := bstep (se 1 (by rfl) ⟨1334093, by rfl⟩ : syracuseStep 1778791 = 2668187) B2668187
theorem B5334227 : Blo 1580488 5334227 := bstep (se 1 (by rfl) ⟨4000670, by rfl⟩ : syracuseStep 5334227 = 8001341) B8001341
theorem B1582335 : Blo 1580488 1582335 := bstep (se 1 (by rfl) ⟨1186751, by rfl⟩ : syracuseStep 1582335 = 2373503) B2373503
theorem B27026945 : Blo 1580488 27026945 := bstep (se 2 (by rfl) ⟨10135104, by rfl⟩ : syracuseStep 27026945 = 20270209) B20270209
theorem B3556943 : Blo 1580488 3556943 := bstep (se 1 (by rfl) ⟨2667707, by rfl⟩ : syracuseStep 3556943 = 5335415) B5335415
theorem B3557033 : Blo 1580488 3557033 := bstep (se 2 (by rfl) ⟨1333887, by rfl⟩ : syracuseStep 3557033 = 2667775) B2667775
theorem B3376865 : Blo 1580488 3376865 := bstep (se 2 (by rfl) ⟨1266324, by rfl⟩ : syracuseStep 3376865 = 2532649) B2532649
theorem B7595947 : Blo 1580488 7595947 := bstep (se 1 (by rfl) ⟨5696960, by rfl⟩ : syracuseStep 7595947 = 11393921) B11393921
theorem B12011489 : Blo 1580488 12011489 := bstep (se 2 (by rfl) ⟨4504308, by rfl⟩ : syracuseStep 12011489 = 9008617) B9008617
theorem B3557609 : Blo 1580488 3557609 := bstep (se 2 (by rfl) ⟨1334103, by rfl⟩ : syracuseStep 3557609 = 2668207) B2668207
theorem B48695555 : Blo 1580488 48695555 := bstep (se 1 (by rfl) ⟨36521666, by rfl⟩ : syracuseStep 48695555 = 73043333) B73043333
theorem B3557663 : Blo 1580488 3557663 := bstep (se 1 (by rfl) ⟨2668247, by rfl⟩ : syracuseStep 3557663 = 5336495) B5336495
theorem B5065183 : Blo 1580488 5065183 := bstep (se 1 (by rfl) ⟨3798887, by rfl⟩ : syracuseStep 5065183 = 7597775) B7597775
theorem B10816175 : Blo 1580488 10816175 := bstep (se 1 (by rfl) ⟨8112131, by rfl⟩ : syracuseStep 10816175 = 16224263) B16224263
theorem B5696327 : Blo 1580488 5696327 := bstep (se 1 (by rfl) ⟨4272245, by rfl⟩ : syracuseStep 5696327 = 8544491) B8544491
theorem B3001225 : Blo 1580488 3001225 := bstep (se 2 (by rfl) ⟨1125459, by rfl⟩ : syracuseStep 3001225 = 2250919) B2250919
theorem B61590415 : Blo 1580488 61590415 := bstep (se 1 (by rfl) ⟨46192811, by rfl⟩ : syracuseStep 61590415 = 92385623) B92385623
theorem B3558311 : Blo 1580488 3558311 := bstep (se 1 (by rfl) ⟨2668733, by rfl⟩ : syracuseStep 3558311 = 5337467) B5337467
theorem B12012461 : Blo 1580488 12012461 := bstep (se 3 (by rfl) ⟨2252336, by rfl⟩ : syracuseStep 12012461 = 4504673) B4504673
theorem B3558473 : Blo 1580488 3558473 := bstep (se 2 (by rfl) ⟨1334427, by rfl⟩ : syracuseStep 3558473 = 2668855) B2668855
theorem B13503631 : Blo 1580488 13503631 := bstep (se 1 (by rfl) ⟨10127723, by rfl⟩ : syracuseStep 13503631 = 20255447) B20255447
theorem B9006227 : Blo 1580488 9006227 := bstep (se 1 (by rfl) ⟨6754670, by rfl⟩ : syracuseStep 9006227 = 13509341) B13509341
theorem B2002087 : Blo 1580488 2002087 := bstep (se 1 (by rfl) ⟨1501565, by rfl⟩ : syracuseStep 2002087 = 3003131) B3003131
theorem B2534591 : Blo 1580488 2534591 := bstep (se 1 (by rfl) ⟨1900943, by rfl⟩ : syracuseStep 2534591 = 3801887) B3801887
theorem B16240027 : Blo 1580488 16240027 := bstep (se 1 (by rfl) ⟨12180020, by rfl⟩ : syracuseStep 16240027 = 24360041) B24360041
theorem B194719153 : Blo 1580488 194719153 := bstep (se 2 (by rfl) ⟨73019682, by rfl⟩ : syracuseStep 194719153 = 146039365) B146039365
theorem B2002411 : Blo 1580488 2002411 := bstep (se 1 (by rfl) ⟨1501808, by rfl⟩ : syracuseStep 2002411 = 3003617) B3003617
theorem B2371175 : Blo 1580488 2371175 := bstep (se 1 (by rfl) ⟨1778381, by rfl⟩ : syracuseStep 2371175 = 3556763) B3556763
theorem B3559067 : Blo 1580488 3559067 := bstep (se 1 (by rfl) ⟨2669300, by rfl⟩ : syracuseStep 3559067 = 5338601) B5338601
theorem B8007335 : Blo 1580488 8007335 := bstep (se 1 (by rfl) ⟨6005501, by rfl⟩ : syracuseStep 8007335 = 12011003) B12011003
theorem B4002169 : Blo 1580488 4002169 := bstep (se 2 (by rfl) ⟨1500813, by rfl⟩ : syracuseStep 4002169 = 3001627) B3001627
theorem B11399687 : Blo 1580488 11399687 := bstep (se 1 (by rfl) ⟨8549765, by rfl⟩ : syracuseStep 11399687 = 17099531) B17099531
theorem B2568809 : Blo 1580488 2568809 := bstep (se 2 (by rfl) ⟨963303, by rfl⟩ : syracuseStep 2568809 = 1926607) B1926607
theorem B7598717 : Blo 1580488 7598717 := bstep (se 3 (by rfl) ⟨1424759, by rfl⟩ : syracuseStep 7598717 = 2849519) B2849519
theorem B2372327 : Blo 1580488 2372327 := bstep (se 1 (by rfl) ⟨1779245, by rfl⟩ : syracuseStep 2372327 = 3558491) B3558491
theorem B3560201 : Blo 1580488 3560201 := bstep (se 2 (by rfl) ⟨1335075, by rfl⟩ : syracuseStep 3560201 = 2670151) B2670151
theorem B4502395 : Blo 1580488 4502395 := bstep (se 1 (by rfl) ⟨3376796, by rfl⟩ : syracuseStep 4502395 = 6753593) B6753593
theorem B3003419 : Blo 1580488 3003419 := bstep (se 1 (by rfl) ⟨2252564, by rfl⟩ : syracuseStep 3003419 = 4505129) B4505129
theorem B3560489 : Blo 1580488 3560489 := bstep (se 2 (by rfl) ⟨1335183, by rfl⟩ : syracuseStep 3560489 = 2670367) B2670367
theorem B4502623 : Blo 1580488 4502623 := bstep (se 1 (by rfl) ⟨3376967, by rfl⟩ : syracuseStep 4502623 = 6753935) B6753935
theorem B4502783 : Blo 1580488 4502783 := bstep (se 1 (by rfl) ⟨3377087, by rfl⟩ : syracuseStep 4502783 = 6754175) B6754175
theorem B2373023 : Blo 1580488 2373023 := bstep (se 1 (by rfl) ⟨1779767, by rfl⟩ : syracuseStep 2373023 = 3559535) B3559535
theorem B14423507 : Blo 1580488 14423507 := bstep (se 1 (by rfl) ⟨10817630, by rfl⟩ : syracuseStep 14423507 = 21635261) B21635261
theorem B4503023 : Blo 1580488 4503023 := bstep (se 1 (by rfl) ⟨3377267, by rfl⟩ : syracuseStep 4503023 = 6754535) B6754535
theorem B3471131 : Blo 1580488 3471131 := bstep (se 1 (by rfl) ⟨2603348, by rfl⟩ : syracuseStep 3471131 = 5206697) B5206697
theorem B13506365 : Blo 1580488 13506365 := bstep (se 3 (by rfl) ⟨2532443, by rfl⟩ : syracuseStep 13506365 = 5064887) B5064887
theorem B2373599 : Blo 1580488 2373599 := bstep (se 1 (by rfl) ⟨1780199, by rfl⟩ : syracuseStep 2373599 = 3560399) B3560399
theorem B4503899 : Blo 1580488 4503899 := bstep (se 1 (by rfl) ⟨3377924, by rfl⟩ : syracuseStep 4503899 = 6755849) B6755849
theorem B4004255 : Blo 1580488 4004255 := bstep (se 1 (by rfl) ⟨3003191, by rfl⟩ : syracuseStep 4004255 = 6006383) B6006383
theorem B5339627 : Blo 1580488 5339627 := bstep (se 1 (by rfl) ⟨4004720, by rfl⟩ : syracuseStep 5339627 = 8009441) B8009441
theorem B18020879 : Blo 1580488 18020879 := bstep (se 1 (by rfl) ⟨13515659, by rfl⟩ : syracuseStep 18020879 = 27031319) B27031319
theorem B2669159 : Blo 1580488 2669159 := bstep (se 1 (by rfl) ⟨2001869, by rfl⟩ : syracuseStep 2669159 = 4003739) B4003739
theorem B5339951 : Blo 1580488 5339951 := bstep (se 1 (by rfl) ⟨4004963, by rfl⟩ : syracuseStep 5339951 = 8009927) B8009927
theorem B12008573 : Blo 1580488 12008573 := bstep (se 3 (by rfl) ⟨2251607, by rfl⟩ : syracuseStep 12008573 = 4503215) B4503215
theorem B8551649 : Blo 1580488 8551649 := bstep (se 2 (by rfl) ⟨3206868, by rfl⟩ : syracuseStep 8551649 = 6413737) B6413737
theorem B50691379 : Blo 1580488 50691379 := bstep (se 1 (by rfl) ⟨38018534, by rfl⟩ : syracuseStep 50691379 = 76037069) B76037069
theorem B4005247 : Blo 1580488 4005247 := bstep (se 1 (by rfl) ⟨3003935, by rfl⟩ : syracuseStep 4005247 = 6007871) B6007871
theorem B27377129 : Blo 1580488 27377129 := bstep (se 2 (by rfl) ⟨10266423, by rfl⟩ : syracuseStep 27377129 = 20532847) B20532847
theorem B4505483 : Blo 1580488 4505483 := bstep (se 1 (by rfl) ⟨3379112, by rfl⟩ : syracuseStep 4505483 = 6758225) B6758225
theorem B1712539 : Blo 1580488 1712539 := bstep (se 1 (by rfl) ⟨1284404, by rfl⟩ : syracuseStep 1712539 = 2568809) B2568809
theorem B1581551 : Blo 1580488 1581551 := bstep (se 1 (by rfl) ⟨1186163, by rfl⟩ : syracuseStep 1581551 = 2372327) B2372327
theorem B6758909 : Blo 1580488 6758909 := bstep (se 3 (by rfl) ⟨1267295, by rfl⟩ : syracuseStep 6758909 = 2534591) B2534591
theorem B3556151 : Blo 1580488 3556151 := bstep (se 1 (by rfl) ⟨2667113, by rfl⟩ : syracuseStep 3556151 = 5334227) B5334227
theorem B1582015 : Blo 1580488 1582015 := bstep (se 1 (by rfl) ⟨1186511, by rfl⟩ : syracuseStep 1582015 = 2373023) B2373023
theorem B9004243 : Blo 1580488 9004243 := bstep (se 1 (by rfl) ⟨6753182, by rfl⟩ : syracuseStep 9004243 = 13506365) B13506365
theorem B1582399 : Blo 1580488 1582399 := bstep (se 1 (by rfl) ⟨1186799, by rfl⟩ : syracuseStep 1582399 = 2373599) B2373599
theorem B1779439 : Blo 1580488 1779439 := bstep (se 1 (by rfl) ⟨1334579, by rfl⟩ : syracuseStep 1779439 = 2669159) B2669159
theorem B7210783 : Blo 1580488 7210783 := bstep (se 1 (by rfl) ⟨5408087, by rfl⟩ : syracuseStep 7210783 = 10816175) B10816175
theorem B21653369 : Blo 1580488 21653369 := bstep (se 2 (by rfl) ⟨8120013, by rfl⟩ : syracuseStep 21653369 = 16240027) B16240027
theorem B8005715 : Blo 1580488 8005715 := bstep (se 1 (by rfl) ⟨6004286, by rfl⟩ : syracuseStep 8005715 = 12008573) B12008573
theorem B10127929 : Blo 1580488 10127929 := bstep (se 2 (by rfl) ⟨3797973, by rfl⟩ : syracuseStep 10127929 = 7595947) B7595947
theorem B5065811 : Blo 1580488 5065811 := bstep (se 1 (by rfl) ⟨3799358, by rfl⟩ : syracuseStep 5065811 = 7598717) B7598717
theorem B5336225 : Blo 1580488 5336225 := bstep (se 2 (by rfl) ⟨2001084, by rfl⟩ : syracuseStep 5336225 = 4002169) B4002169
theorem B2567359 : Blo 1580488 2567359 := bstep (se 1 (by rfl) ⟨1925519, by rfl⟩ : syracuseStep 2567359 = 3851039) B3851039
theorem B2370857 : Blo 1580488 2370857 := bstep (se 2 (by rfl) ⟨889071, by rfl⟩ : syracuseStep 2370857 = 1778143) B1778143
theorem B6753577 : Blo 1580488 6753577 := bstep (se 2 (by rfl) ⟨2532591, by rfl⟩ : syracuseStep 6753577 = 5065183) B5065183
theorem B2370887 : Blo 1580488 2370887 := bstep (se 1 (by rfl) ⟨1778165, by rfl⟩ : syracuseStep 2370887 = 3556331) B3556331
theorem B3001855 : Blo 1580488 3001855 := bstep (se 1 (by rfl) ⟨2251391, by rfl⟩ : syracuseStep 3001855 = 4502783) B4502783
theorem B3002015 : Blo 1580488 3002015 := bstep (se 1 (by rfl) ⟨2251511, by rfl⟩ : syracuseStep 3002015 = 4503023) B4503023
theorem B18017963 : Blo 1580488 18017963 := bstep (se 1 (by rfl) ⟨13513472, by rfl⟩ : syracuseStep 18017963 = 27026945) B27026945
theorem B2371295 : Blo 1580488 2371295 := bstep (se 1 (by rfl) ⟨1778471, by rfl⟩ : syracuseStep 2371295 = 3556943) B3556943
theorem B2371355 : Blo 1580488 2371355 := bstep (se 1 (by rfl) ⟨1778516, by rfl⟩ : syracuseStep 2371355 = 3557033) B3557033
theorem B4001633 : Blo 1580488 4001633 := bstep (se 2 (by rfl) ⟨1500612, by rfl⟩ : syracuseStep 4001633 = 3001225) B3001225
theorem B82120553 : Blo 1580488 82120553 := bstep (se 2 (by rfl) ⟨30795207, by rfl⟩ : syracuseStep 82120553 = 61590415) B61590415
theorem B8007659 : Blo 1580488 8007659 := bstep (se 1 (by rfl) ⟨6005744, by rfl⟩ : syracuseStep 8007659 = 12011489) B12011489
theorem B2371721 : Blo 1580488 2371721 := bstep (se 2 (by rfl) ⟨889395, by rfl⟩ : syracuseStep 2371721 = 1778791) B1778791
theorem B2371739 : Blo 1580488 2371739 := bstep (se 1 (by rfl) ⟨1778804, by rfl⟩ : syracuseStep 2371739 = 3557609) B3557609
theorem B2371775 : Blo 1580488 2371775 := bstep (se 1 (by rfl) ⟨1778831, by rfl⟩ : syracuseStep 2371775 = 3557663) B3557663
theorem B3002599 : Blo 1580488 3002599 := bstep (se 1 (by rfl) ⟨2251949, by rfl⟩ : syracuseStep 3002599 = 4503899) B4503899
theorem B3559751 : Blo 1580488 3559751 := bstep (se 1 (by rfl) ⟨2669813, by rfl⟩ : syracuseStep 3559751 = 5339627) B5339627
theorem B12013919 : Blo 1580488 12013919 := bstep (se 1 (by rfl) ⟨9010439, by rfl⟩ : syracuseStep 12013919 = 18020879) B18020879
theorem B67588505 : Blo 1580488 67588505 := bstep (se 2 (by rfl) ⟨25345689, by rfl⟩ : syracuseStep 67588505 = 50691379) B50691379
theorem B3559967 : Blo 1580488 3559967 := bstep (se 1 (by rfl) ⟨2669975, by rfl⟩ : syracuseStep 3559967 = 5339951) B5339951
theorem B3797551 : Blo 1580488 3797551 := bstep (se 1 (by rfl) ⟨2848163, by rfl⟩ : syracuseStep 3797551 = 5696327) B5696327
theorem B259625537 : Blo 1580488 259625537 := bstep (se 2 (by rfl) ⟨97359576, by rfl⟩ : syracuseStep 259625537 = 194719153) B194719153
theorem B2372207 : Blo 1580488 2372207 := bstep (se 1 (by rfl) ⟨1779155, by rfl⟩ : syracuseStep 2372207 = 3558311) B3558311
theorem B8008307 : Blo 1580488 8008307 := bstep (se 1 (by rfl) ⟨6006230, by rfl⟩ : syracuseStep 8008307 = 12012461) B12012461
theorem B2372315 : Blo 1580488 2372315 := bstep (se 1 (by rfl) ⟨1779236, by rfl⟩ : syracuseStep 2372315 = 3558473) B3558473
theorem B2372711 : Blo 1580488 2372711 := bstep (se 1 (by rfl) ⟨1779533, by rfl⟩ : syracuseStep 2372711 = 3559067) B3559067
theorem B5338223 : Blo 1580488 5338223 := bstep (se 1 (by rfl) ⟨4003667, by rfl⟩ : syracuseStep 5338223 = 8007335) B8007335
theorem B3003655 : Blo 1580488 3003655 := bstep (se 1 (by rfl) ⟨2252741, by rfl⟩ : syracuseStep 3003655 = 4505483) B4505483
theorem B8009117 : Blo 1580488 8009117 := bstep (se 3 (by rfl) ⟨1501709, by rfl⟩ : syracuseStep 8009117 = 3003419) B3003419
theorem B7599791 : Blo 1580488 7599791 := bstep (se 1 (by rfl) ⟨5699843, by rfl⟩ : syracuseStep 7599791 = 11399687) B11399687
theorem B2373467 : Blo 1580488 2373467 := bstep (se 1 (by rfl) ⟨1780100, by rfl⟩ : syracuseStep 2373467 = 3560201) B3560201
theorem B2373659 : Blo 1580488 2373659 := bstep (se 1 (by rfl) ⟨1780244, by rfl⟩ : syracuseStep 2373659 = 3560489) B3560489
theorem B9615671 : Blo 1580488 9615671 := bstep (se 1 (by rfl) ⟨7211753, by rfl⟩ : syracuseStep 9615671 = 14423507) B14423507
theorem B2251243 : Blo 1580488 2251243 := bstep (se 1 (by rfl) ⟨1688432, by rfl⟩ : syracuseStep 2251243 = 3376865) B3376865
theorem B6003193 : Blo 1580488 6003193 := bstep (se 2 (by rfl) ⟨2251197, by rfl⟩ : syracuseStep 6003193 = 4502395) B4502395
theorem B6003497 : Blo 1580488 6003497 := bstep (se 2 (by rfl) ⟨2251311, by rfl⟩ : syracuseStep 6003497 = 4502623) B4502623
theorem B32463703 : Blo 1580488 32463703 := bstep (se 1 (by rfl) ⟨24347777, by rfl⟩ : syracuseStep 32463703 = 48695555) B48695555
theorem B18004841 : Blo 1580488 18004841 := bstep (se 2 (by rfl) ⟨6751815, by rfl⟩ : syracuseStep 18004841 = 13503631) B13503631
theorem B2669449 : Blo 1580488 2669449 := bstep (se 2 (by rfl) ⟨1001043, by rfl⟩ : syracuseStep 2669449 = 2002087) B2002087
theorem B2669503 : Blo 1580488 2669503 := bstep (se 1 (by rfl) ⟨2002127, by rfl⟩ : syracuseStep 2669503 = 4004255) B4004255
theorem B5340329 : Blo 1580488 5340329 := bstep (se 2 (by rfl) ⟨2002623, by rfl⟩ : syracuseStep 5340329 = 4005247) B4005247
theorem B2669881 : Blo 1580488 2669881 := bstep (se 2 (by rfl) ⟨1001205, by rfl⟩ : syracuseStep 2669881 = 2002411) B2002411
theorem B9256349 : Blo 1580488 9256349 := bstep (se 3 (by rfl) ⟨1735565, by rfl⟩ : syracuseStep 9256349 = 3471131) B3471131
theorem B6004151 : Blo 1580488 6004151 := bstep (se 1 (by rfl) ⟨4503113, by rfl⟩ : syracuseStep 6004151 = 9006227) B9006227
theorem B5701099 : Blo 1580488 5701099 := bstep (se 1 (by rfl) ⟨4275824, by rfl⟩ : syracuseStep 5701099 = 8551649) B8551649
theorem B18251419 : Blo 1580488 18251419 := bstep (se 1 (by rfl) ⟨13688564, by rfl⟩ : syracuseStep 18251419 = 27377129) B27377129
theorem B1580783 : Blo 1580488 1580783 := bstep (se 1 (by rfl) ⟨1185587, by rfl⟩ : syracuseStep 1580783 = 2371175) B2371175
theorem B1581147 : Blo 1580488 1581147 := bstep (se 1 (by rfl) ⟨1185860, by rfl⟩ : syracuseStep 1581147 = 2371721) B2371721
theorem B1581159 : Blo 1580488 1581159 := bstep (se 1 (by rfl) ⟨1185869, by rfl⟩ : syracuseStep 1581159 = 2371739) B2371739
theorem B1581183 : Blo 1580488 1581183 := bstep (se 1 (by rfl) ⟨1185887, by rfl⟩ : syracuseStep 1581183 = 2371775) B2371775
theorem B4505939 : Blo 1580488 4505939 := bstep (se 1 (by rfl) ⟨3379454, by rfl⟩ : syracuseStep 4505939 = 6758909) B6758909
theorem B1581471 : Blo 1580488 1581471 := bstep (se 1 (by rfl) ⟨1186103, by rfl⟩ : syracuseStep 1581471 = 2372207) B2372207
theorem B1581543 : Blo 1580488 1581543 := bstep (se 1 (by rfl) ⟨1186157, by rfl⟩ : syracuseStep 1581543 = 2372315) B2372315
theorem B8004257 : Blo 1580488 8004257 := bstep (se 2 (by rfl) ⟨3001596, by rfl⟩ : syracuseStep 8004257 = 6003193) B6003193
theorem B5063401 : Blo 1580488 5063401 := bstep (se 2 (by rfl) ⟨1898775, by rfl⟩ : syracuseStep 5063401 = 3797551) B3797551
theorem B1581807 : Blo 1580488 1581807 := bstep (se 1 (by rfl) ⟨1186355, by rfl⟩ : syracuseStep 1581807 = 2372711) B2372711
theorem B1582311 : Blo 1580488 1582311 := bstep (se 1 (by rfl) ⟨1186733, by rfl⟩ : syracuseStep 1582311 = 2373467) B2373467
theorem B14435579 : Blo 1580488 14435579 := bstep (se 1 (by rfl) ⟨10826684, by rfl⟩ : syracuseStep 14435579 = 21653369) B21653369
theorem B1582439 : Blo 1580488 1582439 := bstep (se 1 (by rfl) ⟨1186829, by rfl⟩ : syracuseStep 1582439 = 2373659) B2373659
theorem B9004769 : Blo 1580488 9004769 := bstep (se 2 (by rfl) ⟨3376788, by rfl⟩ : syracuseStep 9004769 = 6753577) B6753577
theorem B12003227 : Blo 1580488 12003227 := bstep (se 1 (by rfl) ⟨9002420, by rfl⟩ : syracuseStep 12003227 = 18004841) B18004841
theorem B3377207 : Blo 1580488 3377207 := bstep (se 1 (by rfl) ⟨2532905, by rfl⟩ : syracuseStep 3377207 = 5065811) B5065811
theorem B3557483 : Blo 1580488 3557483 := bstep (se 1 (by rfl) ⟨2668112, by rfl⟩ : syracuseStep 3557483 = 5336225) B5336225
theorem B6170899 : Blo 1580488 6170899 := bstep (se 1 (by rfl) ⟨4628174, by rfl⟩ : syracuseStep 6170899 = 9256349) B9256349
theorem B2001343 : Blo 1580488 2001343 := bstep (se 1 (by rfl) ⟨1501007, by rfl⟩ : syracuseStep 2001343 = 3002015) B3002015
theorem B12011975 : Blo 1580488 12011975 := bstep (se 1 (by rfl) ⟨9008981, by rfl⟩ : syracuseStep 12011975 = 18017963) B18017963
theorem B45059003 : Blo 1580488 45059003 := bstep (se 1 (by rfl) ⟨33794252, by rfl⟩ : syracuseStep 45059003 = 67588505) B67588505
theorem B173083691 : Blo 1580488 173083691 := bstep (se 1 (by rfl) ⟨129812768, by rfl⟩ : syracuseStep 173083691 = 259625537) B259625537
theorem B2370767 : Blo 1580488 2370767 := bstep (se 1 (by rfl) ⟨1778075, by rfl⟩ : syracuseStep 2370767 = 3556151) B3556151
theorem B3558815 : Blo 1580488 3558815 := bstep (se 1 (by rfl) ⟨2669111, by rfl⟩ : syracuseStep 3558815 = 5338223) B5338223
theorem B13503905 : Blo 1580488 13503905 := bstep (se 2 (by rfl) ⟨5063964, by rfl⟩ : syracuseStep 13503905 = 10127929) B10127929
theorem B3559265 : Blo 1580488 3559265 := bstep (se 2 (by rfl) ⟨1334724, by rfl⟩ : syracuseStep 3559265 = 2669449) B2669449
theorem B3559337 : Blo 1580488 3559337 := bstep (se 2 (by rfl) ⟨1334751, by rfl⟩ : syracuseStep 3559337 = 2669503) B2669503
theorem B5337143 : Blo 1580488 5337143 := bstep (se 1 (by rfl) ⟨4002857, by rfl⟩ : syracuseStep 5337143 = 8005715) B8005715
theorem B6410447 : Blo 1580488 6410447 := bstep (se 1 (by rfl) ⟨4807835, by rfl⟩ : syracuseStep 6410447 = 9615671) B9615671
theorem B12005657 : Blo 1580488 12005657 := bstep (se 2 (by rfl) ⟨4502121, by rfl⟩ : syracuseStep 12005657 = 9004243) B9004243
theorem B3559841 : Blo 1580488 3559841 := bstep (se 2 (by rfl) ⟨1334940, by rfl⟩ : syracuseStep 3559841 = 2669881) B2669881
theorem B4002331 : Blo 1580488 4002331 := bstep (se 1 (by rfl) ⟨3001748, by rfl⟩ : syracuseStep 4002331 = 6003497) B6003497
theorem B4002473 : Blo 1580488 4002473 := bstep (se 2 (by rfl) ⟨1500927, by rfl⟩ : syracuseStep 4002473 = 3001855) B3001855
theorem B3560219 : Blo 1580488 3560219 := bstep (se 1 (by rfl) ⟨2670164, by rfl⟩ : syracuseStep 3560219 = 5340329) B5340329
theorem B24335225 : Blo 1580488 24335225 := bstep (se 2 (by rfl) ⟨9125709, by rfl⟩ : syracuseStep 24335225 = 18251419) B18251419
theorem B4002767 : Blo 1580488 4002767 := bstep (se 1 (by rfl) ⟨3002075, by rfl⟩ : syracuseStep 4002767 = 6004151) B6004151
theorem B2372585 : Blo 1580488 2372585 := bstep (se 2 (by rfl) ⟨889719, by rfl⟩ : syracuseStep 2372585 = 1779439) B1779439
theorem B9614377 : Blo 1580488 9614377 := bstep (se 2 (by rfl) ⟨3605391, by rfl⟩ : syracuseStep 9614377 = 7210783) B7210783
theorem B12006629 : Blo 1580488 12006629 := bstep (se 4 (by rfl) ⟨1125621, by rfl⟩ : syracuseStep 12006629 = 2251243) B2251243
theorem B2667755 : Blo 1580488 2667755 := bstep (se 1 (by rfl) ⟨2000816, by rfl⟩ : syracuseStep 2667755 = 4001633) B4001633
theorem B5338439 : Blo 1580488 5338439 := bstep (se 1 (by rfl) ⟨4003829, by rfl⟩ : syracuseStep 5338439 = 8007659) B8007659
theorem B2373167 : Blo 1580488 2373167 := bstep (se 1 (by rfl) ⟨1779875, by rfl⟩ : syracuseStep 2373167 = 3559751) B3559751
theorem B8009279 : Blo 1580488 8009279 := bstep (se 1 (by rfl) ⟨6006959, by rfl⟩ : syracuseStep 8009279 = 12013919) B12013919
theorem B4003465 : Blo 1580488 4003465 := bstep (se 2 (by rfl) ⟨1501299, by rfl⟩ : syracuseStep 4003465 = 3002599) B3002599
theorem B2373311 : Blo 1580488 2373311 := bstep (se 1 (by rfl) ⟨1779983, by rfl⟩ : syracuseStep 2373311 = 3559967) B3559967
theorem B5338871 : Blo 1580488 5338871 := bstep (se 1 (by rfl) ⟨4004153, by rfl⟩ : syracuseStep 5338871 = 8008307) B8008307
theorem B2283385 : Blo 1580488 2283385 := bstep (se 2 (by rfl) ⟨856269, by rfl⟩ : syracuseStep 2283385 = 1712539) B1712539
theorem B5339411 : Blo 1580488 5339411 := bstep (se 1 (by rfl) ⟨4004558, by rfl⟩ : syracuseStep 5339411 = 8009117) B8009117
theorem B43284937 : Blo 1580488 43284937 := bstep (se 2 (by rfl) ⟨16231851, by rfl⟩ : syracuseStep 43284937 = 32463703) B32463703
theorem B3423145 : Blo 1580488 3423145 := bstep (se 2 (by rfl) ⟨1283679, by rfl⟩ : syracuseStep 3423145 = 2567359) B2567359
theorem B4004873 : Blo 1580488 4004873 := bstep (se 2 (by rfl) ⟨1501827, by rfl⟩ : syracuseStep 4004873 = 3003655) B3003655
theorem B20266109 : Blo 1580488 20266109 := bstep (se 3 (by rfl) ⟨3799895, by rfl⟩ : syracuseStep 20266109 = 7599791) B7599791
theorem B7601465 : Blo 1580488 7601465 := bstep (se 2 (by rfl) ⟨2850549, by rfl⟩ : syracuseStep 7601465 = 5701099) B5701099
theorem B1580571 : Blo 1580488 1580571 := bstep (se 1 (by rfl) ⟨1185428, by rfl⟩ : syracuseStep 1580571 = 2370857) B2370857
theorem B1580591 : Blo 1580488 1580591 := bstep (se 1 (by rfl) ⟨1185443, by rfl⟩ : syracuseStep 1580591 = 2370887) B2370887
theorem B1580863 : Blo 1580488 1580863 := bstep (se 1 (by rfl) ⟨1185647, by rfl⟩ : syracuseStep 1580863 = 2371295) B2371295
theorem B1580903 : Blo 1580488 1580903 := bstep (se 1 (by rfl) ⟨1185677, by rfl⟩ : syracuseStep 1580903 = 2371355) B2371355
theorem B54747035 : Blo 1580488 54747035 := bstep (se 1 (by rfl) ⟨41060276, by rfl⟩ : syracuseStep 54747035 = 82120553) B82120553
theorem B8003771 : Blo 1580488 8003771 := bstep (se 1 (by rfl) ⟨6002828, by rfl⟩ : syracuseStep 8003771 = 12005657) B12005657
theorem B57713249 : Blo 1580488 57713249 := bstep (se 2 (by rfl) ⟨21642468, by rfl⟩ : syracuseStep 57713249 = 43284937) B43284937
theorem B1581723 : Blo 1580488 1581723 := bstep (se 1 (by rfl) ⟨1186292, by rfl⟩ : syracuseStep 1581723 = 2372585) B2372585
theorem B8004419 : Blo 1580488 8004419 := bstep (se 1 (by rfl) ⟨6003314, by rfl⟩ : syracuseStep 8004419 = 12006629) B12006629
theorem B1778503 : Blo 1580488 1778503 := bstep (se 1 (by rfl) ⟨1333877, by rfl⟩ : syracuseStep 1778503 = 2667755) B2667755
theorem B6751201 : Blo 1580488 6751201 := bstep (se 2 (by rfl) ⟨2531700, by rfl⟩ : syracuseStep 6751201 = 5063401) B5063401
theorem B1582111 : Blo 1580488 1582111 := bstep (se 1 (by rfl) ⟨1186583, by rfl⟩ : syracuseStep 1582111 = 2373167) B2373167
theorem B1582207 : Blo 1580488 1582207 := bstep (se 1 (by rfl) ⟨1186655, by rfl⟩ : syracuseStep 1582207 = 2373311) B2373311
theorem B4564193 : Blo 1580488 4564193 := bstep (se 2 (by rfl) ⟨1711572, by rfl⟩ : syracuseStep 4564193 = 3423145) B3423145
theorem B13510739 : Blo 1580488 13510739 := bstep (se 1 (by rfl) ⟨10133054, by rfl⟩ : syracuseStep 13510739 = 20266109) B20266109
theorem B36498023 : Blo 1580488 36498023 := bstep (se 1 (by rfl) ⟨27373517, by rfl⟩ : syracuseStep 36498023 = 54747035) B54747035
theorem B3558095 : Blo 1580488 3558095 := bstep (se 1 (by rfl) ⟨2668571, by rfl⟩ : syracuseStep 3558095 = 5337143) B5337143
theorem B8227865 : Blo 1580488 8227865 := bstep (se 2 (by rfl) ⟨3085449, by rfl⟩ : syracuseStep 8227865 = 6170899) B6170899
theorem B5336171 : Blo 1580488 5336171 := bstep (se 1 (by rfl) ⟨4002128, by rfl⟩ : syracuseStep 5336171 = 8004257) B8004257
theorem B16223483 : Blo 1580488 16223483 := bstep (se 1 (by rfl) ⟨12167612, by rfl⟩ : syracuseStep 16223483 = 24335225) B24335225
theorem B5336441 : Blo 1580488 5336441 := bstep (se 2 (by rfl) ⟨2001165, by rfl⟩ : syracuseStep 5336441 = 4002331) B4002331
theorem B20270573 : Blo 1580488 20270573 := bstep (se 3 (by rfl) ⟨3800732, by rfl⟩ : syracuseStep 20270573 = 7601465) B7601465
theorem B3558959 : Blo 1580488 3558959 := bstep (se 1 (by rfl) ⟨2669219, by rfl⟩ : syracuseStep 3558959 = 5338439) B5338439
theorem B3559247 : Blo 1580488 3559247 := bstep (se 1 (by rfl) ⟨2669435, by rfl⟩ : syracuseStep 3559247 = 5338871) B5338871
theorem B2371655 : Blo 1580488 2371655 := bstep (se 1 (by rfl) ⟨1778741, by rfl⟩ : syracuseStep 2371655 = 3557483) B3557483
theorem B3559607 : Blo 1580488 3559607 := bstep (se 1 (by rfl) ⟨2669705, by rfl⟩ : syracuseStep 3559607 = 5339411) B5339411
theorem B8007983 : Blo 1580488 8007983 := bstep (se 1 (by rfl) ⟨6005987, by rfl⟩ : syracuseStep 8007983 = 12011975) B12011975
theorem B115389127 : Blo 1580488 115389127 := bstep (se 1 (by rfl) ⟨86541845, by rfl⟩ : syracuseStep 115389127 = 173083691) B173083691
theorem B5337953 : Blo 1580488 5337953 := bstep (se 2 (by rfl) ⟨2001732, by rfl⟩ : syracuseStep 5337953 = 4003465) B4003465
theorem B2372543 : Blo 1580488 2372543 := bstep (se 1 (by rfl) ⟨1779407, by rfl⟩ : syracuseStep 2372543 = 3558815) B3558815
theorem B3044513 : Blo 1580488 3044513 := bstep (se 2 (by rfl) ⟨1141692, by rfl⟩ : syracuseStep 3044513 = 2283385) B2283385
theorem B2372843 : Blo 1580488 2372843 := bstep (se 1 (by rfl) ⟨1779632, by rfl⟩ : syracuseStep 2372843 = 3559265) B3559265
theorem B2372891 : Blo 1580488 2372891 := bstep (se 1 (by rfl) ⟨1779668, by rfl⟩ : syracuseStep 2372891 = 3559337) B3559337
theorem B4273631 : Blo 1580488 4273631 := bstep (se 1 (by rfl) ⟨3205223, by rfl⟩ : syracuseStep 4273631 = 6410447) B6410447
theorem B3003959 : Blo 1580488 3003959 := bstep (se 1 (by rfl) ⟨2252969, by rfl⟩ : syracuseStep 3003959 = 4505939) B4505939
theorem B2373227 : Blo 1580488 2373227 := bstep (se 1 (by rfl) ⟨1779920, by rfl⟩ : syracuseStep 2373227 = 3559841) B3559841
theorem B2668315 : Blo 1580488 2668315 := bstep (se 1 (by rfl) ⟨2001236, by rfl⟩ : syracuseStep 2668315 = 4002473) B4002473
theorem B2373479 : Blo 1580488 2373479 := bstep (se 1 (by rfl) ⟨1780109, by rfl⟩ : syracuseStep 2373479 = 3560219) B3560219
theorem B2668457 : Blo 1580488 2668457 := bstep (se 2 (by rfl) ⟨1000671, by rfl⟩ : syracuseStep 2668457 = 2001343) B2001343
theorem B2668511 : Blo 1580488 2668511 := bstep (se 1 (by rfl) ⟨2001383, by rfl⟩ : syracuseStep 2668511 = 4002767) B4002767
theorem B9623719 : Blo 1580488 9623719 := bstep (se 1 (by rfl) ⟨7217789, by rfl⟩ : syracuseStep 9623719 = 14435579) B14435579
theorem B5339519 : Blo 1580488 5339519 := bstep (se 1 (by rfl) ⟨4004639, by rfl⟩ : syracuseStep 5339519 = 8009279) B8009279
theorem B6003179 : Blo 1580488 6003179 := bstep (se 1 (by rfl) ⟨4502384, by rfl⟩ : syracuseStep 6003179 = 9004769) B9004769
theorem B8002151 : Blo 1580488 8002151 := bstep (se 1 (by rfl) ⟨6001613, by rfl⟩ : syracuseStep 8002151 = 12003227) B12003227
theorem B2251471 : Blo 1580488 2251471 := bstep (se 1 (by rfl) ⟨1688603, by rfl⟩ : syracuseStep 2251471 = 3377207) B3377207
theorem B12819169 : Blo 1580488 12819169 := bstep (se 2 (by rfl) ⟨4807188, by rfl⟩ : syracuseStep 12819169 = 9614377) B9614377
theorem B30039335 : Blo 1580488 30039335 := bstep (se 1 (by rfl) ⟨22529501, by rfl⟩ : syracuseStep 30039335 = 45059003) B45059003
theorem B2669915 : Blo 1580488 2669915 := bstep (se 1 (by rfl) ⟨2002436, by rfl⟩ : syracuseStep 2669915 = 4004873) B4004873
theorem B1580511 : Blo 1580488 1580511 := bstep (se 1 (by rfl) ⟨1185383, by rfl⟩ : syracuseStep 1580511 = 2370767) B2370767
theorem B9002603 : Blo 1580488 9002603 := bstep (se 1 (by rfl) ⟨6751952, by rfl⟩ : syracuseStep 9002603 = 13503905) B13503905
theorem B1581103 : Blo 1580488 1581103 := bstep (se 1 (by rfl) ⟨1185827, by rfl⟩ : syracuseStep 1581103 = 2371655) B2371655
theorem B8118701 : Blo 1580488 8118701 := bstep (se 3 (by rfl) ⟨1522256, by rfl⟩ : syracuseStep 8118701 = 3044513) B3044513
theorem B1581695 : Blo 1580488 1581695 := bstep (se 1 (by rfl) ⟨1186271, by rfl⟩ : syracuseStep 1581695 = 2372543) B2372543
theorem B1581895 : Blo 1580488 1581895 := bstep (se 1 (by rfl) ⟨1186421, by rfl⟩ : syracuseStep 1581895 = 2372843) B2372843
theorem B1581927 : Blo 1580488 1581927 := bstep (se 1 (by rfl) ⟨1186445, by rfl⟩ : syracuseStep 1581927 = 2372891) B2372891
theorem B1582151 : Blo 1580488 1582151 := bstep (se 1 (by rfl) ⟨1186613, by rfl⟩ : syracuseStep 1582151 = 2373227) B2373227
theorem B1582319 : Blo 1580488 1582319 := bstep (se 1 (by rfl) ⟨1186739, by rfl⟩ : syracuseStep 1582319 = 2373479) B2373479
theorem B1778971 : Blo 1580488 1778971 := bstep (se 1 (by rfl) ⟨1334228, by rfl⟩ : syracuseStep 1778971 = 2668457) B2668457
theorem B1779007 : Blo 1580488 1779007 := bstep (se 1 (by rfl) ⟨1334255, by rfl⟩ : syracuseStep 1779007 = 2668511) B2668511
theorem B24332015 : Blo 1580488 24332015 := bstep (se 1 (by rfl) ⟨18249011, by rfl⟩ : syracuseStep 24332015 = 36498023) B36498023
theorem B5334767 : Blo 1580488 5334767 := bstep (se 1 (by rfl) ⟨4001075, by rfl⟩ : syracuseStep 5334767 = 8002151) B8002151
theorem B3557447 : Blo 1580488 3557447 := bstep (se 1 (by rfl) ⟨2668085, by rfl⟩ : syracuseStep 3557447 = 5336171) B5336171
theorem B10815655 : Blo 1580488 10815655 := bstep (se 1 (by rfl) ⟨8111741, by rfl⟩ : syracuseStep 10815655 = 16223483) B16223483
theorem B1779943 : Blo 1580488 1779943 := bstep (se 1 (by rfl) ⟨1334957, by rfl⟩ : syracuseStep 1779943 = 2669915) B2669915
theorem B3557627 : Blo 1580488 3557627 := bstep (se 1 (by rfl) ⟨2668220, by rfl⟩ : syracuseStep 3557627 = 5336441) B5336441
theorem B3557753 : Blo 1580488 3557753 := bstep (se 2 (by rfl) ⟨1334157, by rfl⟩ : syracuseStep 3557753 = 2668315) B2668315
theorem B5335847 : Blo 1580488 5335847 := bstep (se 1 (by rfl) ⟨4001885, by rfl⟩ : syracuseStep 5335847 = 8003771) B8003771
theorem B12831625 : Blo 1580488 12831625 := bstep (se 2 (by rfl) ⟨4811859, by rfl⟩ : syracuseStep 12831625 = 9623719) B9623719
theorem B5336279 : Blo 1580488 5336279 := bstep (se 1 (by rfl) ⟨4002209, by rfl⟩ : syracuseStep 5336279 = 8004419) B8004419
theorem B3558635 : Blo 1580488 3558635 := bstep (se 1 (by rfl) ⟨2668976, by rfl⟩ : syracuseStep 3558635 = 5337953) B5337953
theorem B3001961 : Blo 1580488 3001961 := bstep (se 2 (by rfl) ⟨1125735, by rfl⟩ : syracuseStep 3001961 = 2251471) B2251471
theorem B17092225 : Blo 1580488 17092225 := bstep (se 2 (by rfl) ⟨6409584, by rfl⟩ : syracuseStep 17092225 = 12819169) B12819169
theorem B2002639 : Blo 1580488 2002639 := bstep (se 1 (by rfl) ⟨1501979, by rfl⟩ : syracuseStep 2002639 = 3003959) B3003959
theorem B2371337 : Blo 1580488 2371337 := bstep (se 2 (by rfl) ⟨889251, by rfl⟩ : syracuseStep 2371337 = 1778503) B1778503
theorem B9007159 : Blo 1580488 9007159 := bstep (se 1 (by rfl) ⟨6755369, by rfl⟩ : syracuseStep 9007159 = 13510739) B13510739
theorem B3559679 : Blo 1580488 3559679 := bstep (se 1 (by rfl) ⟨2669759, by rfl⟩ : syracuseStep 3559679 = 5339519) B5339519
theorem B4002119 : Blo 1580488 4002119 := bstep (se 1 (by rfl) ⟨3001589, by rfl⟩ : syracuseStep 4002119 = 6003179) B6003179
theorem B2372063 : Blo 1580488 2372063 := bstep (se 1 (by rfl) ⟨1779047, by rfl⟩ : syracuseStep 2372063 = 3558095) B3558095
theorem B5485243 : Blo 1580488 5485243 := bstep (se 1 (by rfl) ⟨4113932, by rfl⟩ : syracuseStep 5485243 = 8227865) B8227865
theorem B20026223 : Blo 1580488 20026223 := bstep (se 1 (by rfl) ⟨15019667, by rfl⟩ : syracuseStep 20026223 = 30039335) B30039335
theorem B13513715 : Blo 1580488 13513715 := bstep (se 1 (by rfl) ⟨10135286, by rfl⟩ : syracuseStep 13513715 = 20270573) B20270573
theorem B2372639 : Blo 1580488 2372639 := bstep (se 1 (by rfl) ⟨1779479, by rfl⟩ : syracuseStep 2372639 = 3558959) B3558959
theorem B6001735 : Blo 1580488 6001735 := bstep (se 1 (by rfl) ⟨4501301, by rfl⟩ : syracuseStep 6001735 = 9002603) B9002603
theorem B2372831 : Blo 1580488 2372831 := bstep (se 1 (by rfl) ⟨1779623, by rfl⟩ : syracuseStep 2372831 = 3559247) B3559247
theorem B2373071 : Blo 1580488 2373071 := bstep (se 1 (by rfl) ⟨1779803, by rfl⟩ : syracuseStep 2373071 = 3559607) B3559607
theorem B5338655 : Blo 1580488 5338655 := bstep (se 1 (by rfl) ⟨4003991, by rfl⟩ : syracuseStep 5338655 = 8007983) B8007983
theorem B38475499 : Blo 1580488 38475499 := bstep (se 1 (by rfl) ⟨28856624, by rfl⟩ : syracuseStep 38475499 = 57713249) B57713249
theorem B153852169 : Blo 1580488 153852169 := bstep (se 2 (by rfl) ⟨57694563, by rfl⟩ : syracuseStep 153852169 = 115389127) B115389127
theorem B2849087 : Blo 1580488 2849087 := bstep (se 1 (by rfl) ⟨2136815, by rfl⟩ : syracuseStep 2849087 = 4273631) B4273631
theorem B9001601 : Blo 1580488 9001601 := bstep (se 2 (by rfl) ⟨3375600, by rfl⟩ : syracuseStep 9001601 = 6751201) B6751201
theorem B48684725 : Blo 1580488 48684725 := bstep (se 5 (by rfl) ⟨2282096, by rfl⟩ : syracuseStep 48684725 = 4564193) B4564193
theorem B12009545 : Blo 1580488 12009545 := bstep (se 2 (by rfl) ⟨4503579, by rfl⟩ : syracuseStep 12009545 = 9007159) B9007159
theorem B1581375 : Blo 1580488 1581375 := bstep (se 1 (by rfl) ⟨1186031, by rfl⟩ : syracuseStep 1581375 = 2372063) B2372063
theorem B205136225 : Blo 1580488 205136225 := bstep (se 2 (by rfl) ⟨76926084, by rfl⟩ : syracuseStep 205136225 = 153852169) B153852169
theorem B1581759 : Blo 1580488 1581759 := bstep (se 1 (by rfl) ⟨1186319, by rfl⟩ : syracuseStep 1581759 = 2372639) B2372639
theorem B1581887 : Blo 1580488 1581887 := bstep (se 1 (by rfl) ⟨1186415, by rfl⟩ : syracuseStep 1581887 = 2372831) B2372831
theorem B1582047 : Blo 1580488 1582047 := bstep (se 1 (by rfl) ⟨1186535, by rfl⟩ : syracuseStep 1582047 = 2373071) B2373071
theorem B3556511 : Blo 1580488 3556511 := bstep (se 1 (by rfl) ⟨2667383, by rfl⟩ : syracuseStep 3556511 = 5334767) B5334767
theorem B8005229 : Blo 1580488 8005229 := bstep (se 3 (by rfl) ⟨1500980, by rfl⟩ : syracuseStep 8005229 = 3001961) B3001961
theorem B3557231 : Blo 1580488 3557231 := bstep (se 1 (by rfl) ⟨2667923, by rfl⟩ : syracuseStep 3557231 = 5335847) B5335847
theorem B3557519 : Blo 1580488 3557519 := bstep (se 1 (by rfl) ⟨2668139, by rfl⟩ : syracuseStep 3557519 = 5336279) B5336279
theorem B51300665 : Blo 1580488 51300665 := bstep (se 2 (by rfl) ⟨19237749, by rfl⟩ : syracuseStep 51300665 = 38475499) B38475499
theorem B14420873 : Blo 1580488 14420873 := bstep (se 2 (by rfl) ⟨5407827, by rfl⟩ : syracuseStep 14420873 = 10815655) B10815655
theorem B3559103 : Blo 1580488 3559103 := bstep (se 1 (by rfl) ⟨2669327, by rfl⟩ : syracuseStep 3559103 = 5338655) B5338655
theorem B17108833 : Blo 1580488 17108833 := bstep (se 2 (by rfl) ⟨6415812, by rfl⟩ : syracuseStep 17108833 = 12831625) B12831625
theorem B2371631 : Blo 1580488 2371631 := bstep (se 1 (by rfl) ⟨1778723, by rfl⟩ : syracuseStep 2371631 = 3557447) B3557447
theorem B2371751 : Blo 1580488 2371751 := bstep (se 1 (by rfl) ⟨1778813, by rfl⟩ : syracuseStep 2371751 = 3557627) B3557627
theorem B2371835 : Blo 1580488 2371835 := bstep (se 1 (by rfl) ⟨1778876, by rfl⟩ : syracuseStep 2371835 = 3557753) B3557753
theorem B2371961 : Blo 1580488 2371961 := bstep (se 2 (by rfl) ⟨889485, by rfl⟩ : syracuseStep 2371961 = 1778971) B1778971
theorem B2372009 : Blo 1580488 2372009 := bstep (se 2 (by rfl) ⟨889503, by rfl⟩ : syracuseStep 2372009 = 1779007) B1779007
theorem B6001067 : Blo 1580488 6001067 := bstep (se 1 (by rfl) ⟨4500800, by rfl⟩ : syracuseStep 6001067 = 9001601) B9001601
theorem B64885373 : Blo 1580488 64885373 := bstep (se 3 (by rfl) ⟨12166007, by rfl⟩ : syracuseStep 64885373 = 24332015) B24332015
theorem B2372423 : Blo 1580488 2372423 := bstep (se 1 (by rfl) ⟨1779317, by rfl⟩ : syracuseStep 2372423 = 3558635) B3558635
theorem B2373119 : Blo 1580488 2373119 := bstep (se 1 (by rfl) ⟨1779839, by rfl⟩ : syracuseStep 2373119 = 3559679) B3559679
theorem B2668079 : Blo 1580488 2668079 := bstep (se 1 (by rfl) ⟨2001059, by rfl⟩ : syracuseStep 2668079 = 4002119) B4002119
theorem B5412467 : Blo 1580488 5412467 := bstep (se 1 (by rfl) ⟨4059350, by rfl⟩ : syracuseStep 5412467 = 8118701) B8118701
theorem B2373257 : Blo 1580488 2373257 := bstep (se 2 (by rfl) ⟨889971, by rfl⟩ : syracuseStep 2373257 = 1779943) B1779943
theorem B13350815 : Blo 1580488 13350815 := bstep (se 1 (by rfl) ⟨10013111, by rfl⟩ : syracuseStep 13350815 = 20026223) B20026223
theorem B9009143 : Blo 1580488 9009143 := bstep (se 1 (by rfl) ⟨6756857, by rfl⟩ : syracuseStep 9009143 = 13513715) B13513715
theorem B7313657 : Blo 1580488 7313657 := bstep (se 2 (by rfl) ⟨2742621, by rfl⟩ : syracuseStep 7313657 = 5485243) B5485243
theorem B8002313 : Blo 1580488 8002313 := bstep (se 2 (by rfl) ⟨3000867, by rfl⟩ : syracuseStep 8002313 = 6001735) B6001735
theorem B1899391 : Blo 1580488 1899391 := bstep (se 1 (by rfl) ⟨1424543, by rfl⟩ : syracuseStep 1899391 = 2849087) B2849087
theorem B22789633 : Blo 1580488 22789633 := bstep (se 2 (by rfl) ⟨8546112, by rfl⟩ : syracuseStep 22789633 = 17092225) B17092225
theorem B2670185 : Blo 1580488 2670185 := bstep (se 2 (by rfl) ⟨1001319, by rfl⟩ : syracuseStep 2670185 = 2002639) B2002639
theorem B32456483 : Blo 1580488 32456483 := bstep (se 1 (by rfl) ⟨24342362, by rfl⟩ : syracuseStep 32456483 = 48684725) B48684725
theorem B1580891 : Blo 1580488 1580891 := bstep (se 1 (by rfl) ⟨1185668, by rfl⟩ : syracuseStep 1580891 = 2371337) B2371337
theorem B1581087 : Blo 1580488 1581087 := bstep (se 1 (by rfl) ⟨1185815, by rfl⟩ : syracuseStep 1581087 = 2371631) B2371631
theorem B1581167 : Blo 1580488 1581167 := bstep (se 1 (by rfl) ⟨1185875, by rfl⟩ : syracuseStep 1581167 = 2371751) B2371751
theorem B1581223 : Blo 1580488 1581223 := bstep (se 1 (by rfl) ⟨1185917, by rfl⟩ : syracuseStep 1581223 = 2371835) B2371835
theorem B136757483 : Blo 1580488 136757483 := bstep (se 1 (by rfl) ⟨102568112, by rfl⟩ : syracuseStep 136757483 = 205136225) B205136225
theorem B1581307 : Blo 1580488 1581307 := bstep (se 1 (by rfl) ⟨1185980, by rfl⟩ : syracuseStep 1581307 = 2371961) B2371961
theorem B1581339 : Blo 1580488 1581339 := bstep (se 1 (by rfl) ⟨1186004, by rfl⟩ : syracuseStep 1581339 = 2372009) B2372009
theorem B1581615 : Blo 1580488 1581615 := bstep (se 1 (by rfl) ⟨1186211, by rfl⟩ : syracuseStep 1581615 = 2372423) B2372423
theorem B1582079 : Blo 1580488 1582079 := bstep (se 1 (by rfl) ⟨1186559, by rfl⟩ : syracuseStep 1582079 = 2373119) B2373119
theorem B1778719 : Blo 1580488 1778719 := bstep (se 1 (by rfl) ⟨1334039, by rfl⟩ : syracuseStep 1778719 = 2668079) B2668079
theorem B1582171 : Blo 1580488 1582171 := bstep (se 1 (by rfl) ⟨1186628, by rfl⟩ : syracuseStep 1582171 = 2373257) B2373257
theorem B2532521 : Blo 1580488 2532521 := bstep (se 2 (by rfl) ⟨949695, by rfl⟩ : syracuseStep 2532521 = 1899391) B1899391
theorem B6006095 : Blo 1580488 6006095 := bstep (se 1 (by rfl) ⟨4504571, by rfl⟩ : syracuseStep 6006095 = 9009143) B9009143
theorem B5334875 : Blo 1580488 5334875 := bstep (se 1 (by rfl) ⟨4001156, by rfl⟩ : syracuseStep 5334875 = 8002313) B8002313
theorem B30386177 : Blo 1580488 30386177 := bstep (se 2 (by rfl) ⟨11394816, by rfl⟩ : syracuseStep 30386177 = 22789633) B22789633
theorem B38455661 : Blo 1580488 38455661 := bstep (se 3 (by rfl) ⟨7210436, by rfl⟩ : syracuseStep 38455661 = 14420873) B14420873
theorem B1780123 : Blo 1580488 1780123 := bstep (se 1 (by rfl) ⟨1335092, by rfl⟩ : syracuseStep 1780123 = 2670185) B2670185
theorem B21637655 : Blo 1580488 21637655 := bstep (se 1 (by rfl) ⟨16228241, by rfl⟩ : syracuseStep 21637655 = 32456483) B32456483
theorem B8006363 : Blo 1580488 8006363 := bstep (se 1 (by rfl) ⟨6004772, by rfl⟩ : syracuseStep 8006363 = 12009545) B12009545
theorem B4000711 : Blo 1580488 4000711 := bstep (se 1 (by rfl) ⟨3000533, by rfl⟩ : syracuseStep 4000711 = 6001067) B6001067
theorem B43256915 : Blo 1580488 43256915 := bstep (se 1 (by rfl) ⟨32442686, by rfl⟩ : syracuseStep 43256915 = 64885373) B64885373
theorem B2371007 : Blo 1580488 2371007 := bstep (se 1 (by rfl) ⟨1778255, by rfl⟩ : syracuseStep 2371007 = 3556511) B3556511
theorem B5336819 : Blo 1580488 5336819 := bstep (se 1 (by rfl) ⟨4002614, by rfl⟩ : syracuseStep 5336819 = 8005229) B8005229
theorem B3608311 : Blo 1580488 3608311 := bstep (se 1 (by rfl) ⟨2706233, by rfl⟩ : syracuseStep 3608311 = 5412467) B5412467
theorem B2371487 : Blo 1580488 2371487 := bstep (se 1 (by rfl) ⟨1778615, by rfl⟩ : syracuseStep 2371487 = 3557231) B3557231
theorem B8900543 : Blo 1580488 8900543 := bstep (se 1 (by rfl) ⟨6675407, by rfl⟩ : syracuseStep 8900543 = 13350815) B13350815
theorem B2371679 : Blo 1580488 2371679 := bstep (se 1 (by rfl) ⟨1778759, by rfl⟩ : syracuseStep 2371679 = 3557519) B3557519
theorem B2372735 : Blo 1580488 2372735 := bstep (se 1 (by rfl) ⟨1779551, by rfl⟩ : syracuseStep 2372735 = 3559103) B3559103
theorem B22811777 : Blo 1580488 22811777 := bstep (se 2 (by rfl) ⟨8554416, by rfl⟩ : syracuseStep 22811777 = 17108833) B17108833
theorem B34200443 : Blo 1580488 34200443 := bstep (se 1 (by rfl) ⟨25650332, by rfl⟩ : syracuseStep 34200443 = 51300665) B51300665
theorem B78012341 : Blo 1580488 78012341 := bstep (se 5 (by rfl) ⟨3656828, by rfl⟩ : syracuseStep 78012341 = 7313657) B7313657
theorem B1581119 : Blo 1580488 1581119 := bstep (se 1 (by rfl) ⟨1185839, by rfl⟩ : syracuseStep 1581119 = 2371679) B2371679
theorem B1581823 : Blo 1580488 1581823 := bstep (se 1 (by rfl) ⟨1186367, by rfl⟩ : syracuseStep 1581823 = 2372735) B2372735
theorem B1688347 : Blo 1580488 1688347 := bstep (se 1 (by rfl) ⟨1266260, by rfl⟩ : syracuseStep 1688347 = 2532521) B2532521
theorem B3556583 : Blo 1580488 3556583 := bstep (se 1 (by rfl) ⟨2667437, by rfl⟩ : syracuseStep 3556583 = 5334875) B5334875
theorem B5334281 : Blo 1580488 5334281 := bstep (se 2 (by rfl) ⟨2000355, by rfl⟩ : syracuseStep 5334281 = 4000711) B4000711
theorem B22800295 : Blo 1580488 22800295 := bstep (se 1 (by rfl) ⟨17100221, by rfl⟩ : syracuseStep 22800295 = 34200443) B34200443
theorem B28837943 : Blo 1580488 28837943 := bstep (se 1 (by rfl) ⟨21628457, by rfl⟩ : syracuseStep 28837943 = 43256915) B43256915
theorem B4811081 : Blo 1580488 4811081 := bstep (se 2 (by rfl) ⟨1804155, by rfl⟩ : syracuseStep 4811081 = 3608311) B3608311
theorem B3557879 : Blo 1580488 3557879 := bstep (se 1 (by rfl) ⟨2668409, by rfl⟩ : syracuseStep 3557879 = 5336819) B5336819
theorem B23734781 : Blo 1580488 23734781 := bstep (se 3 (by rfl) ⟨4450271, by rfl⟩ : syracuseStep 23734781 = 8900543) B8900543
theorem B91171655 : Blo 1580488 91171655 := bstep (se 1 (by rfl) ⟨68378741, by rfl⟩ : syracuseStep 91171655 = 136757483) B136757483
theorem B15207851 : Blo 1580488 15207851 := bstep (se 1 (by rfl) ⟨11405888, by rfl⟩ : syracuseStep 15207851 = 22811777) B22811777
theorem B2371625 : Blo 1580488 2371625 := bstep (se 2 (by rfl) ⟨889359, by rfl⟩ : syracuseStep 2371625 = 1778719) B1778719
theorem B25637107 : Blo 1580488 25637107 := bstep (se 1 (by rfl) ⟨19227830, by rfl⟩ : syracuseStep 25637107 = 38455661) B38455661
theorem B5337575 : Blo 1580488 5337575 := bstep (se 1 (by rfl) ⟨4003181, by rfl⟩ : syracuseStep 5337575 = 8006363) B8006363
theorem B52008227 : Blo 1580488 52008227 := bstep (se 1 (by rfl) ⟨39006170, by rfl⟩ : syracuseStep 52008227 = 78012341) B78012341
theorem B2373497 : Blo 1580488 2373497 := bstep (se 2 (by rfl) ⟨890061, by rfl⟩ : syracuseStep 2373497 = 1780123) B1780123
theorem B4004063 : Blo 1580488 4004063 := bstep (se 1 (by rfl) ⟨3003047, by rfl⟩ : syracuseStep 4004063 = 6006095) B6006095
theorem B20257451 : Blo 1580488 20257451 := bstep (se 1 (by rfl) ⟨15193088, by rfl⟩ : syracuseStep 20257451 = 30386177) B30386177
theorem B14425103 : Blo 1580488 14425103 := bstep (se 1 (by rfl) ⟨10818827, by rfl⟩ : syracuseStep 14425103 = 21637655) B21637655
theorem B1580671 : Blo 1580488 1580671 := bstep (se 1 (by rfl) ⟨1185503, by rfl⟩ : syracuseStep 1580671 = 2371007) B2371007
theorem B1580991 : Blo 1580488 1580991 := bstep (se 1 (by rfl) ⟨1185743, by rfl⟩ : syracuseStep 1580991 = 2371487) B2371487
theorem B1581083 : Blo 1580488 1581083 := bstep (se 1 (by rfl) ⟨1185812, by rfl⟩ : syracuseStep 1581083 = 2371625) B2371625
theorem B3556187 : Blo 1580488 3556187 := bstep (se 1 (by rfl) ⟨2667140, by rfl⟩ : syracuseStep 3556187 = 5334281) B5334281
theorem B1582331 : Blo 1580488 1582331 := bstep (se 1 (by rfl) ⟨1186748, by rfl⟩ : syracuseStep 1582331 = 2373497) B2373497
theorem B9004517 : Blo 1580488 9004517 := bstep (se 4 (by rfl) ⟨844173, by rfl⟩ : syracuseStep 9004517 = 1688347) B1688347
theorem B3558383 : Blo 1580488 3558383 := bstep (se 1 (by rfl) ⟨2668787, by rfl⟩ : syracuseStep 3558383 = 5337575) B5337575
theorem B51318197 : Blo 1580488 51318197 := bstep (se 5 (by rfl) ⟨2405540, by rfl⟩ : syracuseStep 51318197 = 4811081) B4811081
theorem B2371055 : Blo 1580488 2371055 := bstep (se 1 (by rfl) ⟨1778291, by rfl⟩ : syracuseStep 2371055 = 3556583) B3556583
theorem B34672151 : Blo 1580488 34672151 := bstep (se 1 (by rfl) ⟨26004113, by rfl⟩ : syracuseStep 34672151 = 52008227) B52008227
theorem B2371919 : Blo 1580488 2371919 := bstep (se 1 (by rfl) ⟨1778939, by rfl⟩ : syracuseStep 2371919 = 3557879) B3557879
theorem B15823187 : Blo 1580488 15823187 := bstep (se 1 (by rfl) ⟨11867390, by rfl⟩ : syracuseStep 15823187 = 23734781) B23734781
theorem B13504967 : Blo 1580488 13504967 := bstep (se 1 (by rfl) ⟨10128725, by rfl⟩ : syracuseStep 13504967 = 20257451) B20257451
theorem B60781103 : Blo 1580488 60781103 := bstep (se 1 (by rfl) ⟨45585827, by rfl⟩ : syracuseStep 60781103 = 91171655) B91171655
theorem B10138567 : Blo 1580488 10138567 := bstep (se 1 (by rfl) ⟨7603925, by rfl⟩ : syracuseStep 10138567 = 15207851) B15207851
theorem B34182809 : Blo 1580488 34182809 := bstep (se 2 (by rfl) ⟨12818553, by rfl⟩ : syracuseStep 34182809 = 25637107) B25637107
theorem B19225295 : Blo 1580488 19225295 := bstep (se 1 (by rfl) ⟨14418971, by rfl⟩ : syracuseStep 19225295 = 28837943) B28837943
theorem B2669375 : Blo 1580488 2669375 := bstep (se 1 (by rfl) ⟨2002031, by rfl⟩ : syracuseStep 2669375 = 4004063) B4004063
theorem B9616735 : Blo 1580488 9616735 := bstep (se 1 (by rfl) ⟨7212551, by rfl⟩ : syracuseStep 9616735 = 14425103) B14425103
theorem B30400393 : Blo 1580488 30400393 := bstep (se 2 (by rfl) ⟨11400147, by rfl⟩ : syracuseStep 30400393 = 22800295) B22800295
theorem B1581279 : Blo 1580488 1581279 := bstep (se 1 (by rfl) ⟨1185959, by rfl⟩ : syracuseStep 1581279 = 2371919) B2371919
theorem B9003311 : Blo 1580488 9003311 := bstep (se 1 (by rfl) ⟨6752483, by rfl⟩ : syracuseStep 9003311 = 13504967) B13504967
theorem B13518089 : Blo 1580488 13518089 := bstep (se 2 (by rfl) ⟨5069283, by rfl⟩ : syracuseStep 13518089 = 10138567) B10138567
theorem B12822313 : Blo 1580488 12822313 := bstep (se 2 (by rfl) ⟨4808367, by rfl⟩ : syracuseStep 12822313 = 9616735) B9616735
theorem B1779583 : Blo 1580488 1779583 := bstep (se 1 (by rfl) ⟨1334687, by rfl⟩ : syracuseStep 1779583 = 2669375) B2669375
theorem B34212131 : Blo 1580488 34212131 := bstep (se 1 (by rfl) ⟨25659098, by rfl⟩ : syracuseStep 34212131 = 51318197) B51318197
theorem B40520735 : Blo 1580488 40520735 := bstep (se 1 (by rfl) ⟨30390551, by rfl⟩ : syracuseStep 40520735 = 60781103) B60781103
theorem B2370791 : Blo 1580488 2370791 := bstep (se 1 (by rfl) ⟨1778093, by rfl⟩ : syracuseStep 2370791 = 3556187) B3556187
theorem B92459069 : Blo 1580488 92459069 := bstep (se 3 (by rfl) ⟨17336075, by rfl⟩ : syracuseStep 92459069 = 34672151) B34672151
theorem B12816863 : Blo 1580488 12816863 := bstep (se 1 (by rfl) ⟨9612647, by rfl⟩ : syracuseStep 12816863 = 19225295) B19225295
theorem B2372255 : Blo 1580488 2372255 := bstep (se 1 (by rfl) ⟨1779191, by rfl⟩ : syracuseStep 2372255 = 3558383) B3558383
theorem B10548791 : Blo 1580488 10548791 := bstep (se 1 (by rfl) ⟨7911593, by rfl⟩ : syracuseStep 10548791 = 15823187) B15823187
theorem B6003011 : Blo 1580488 6003011 := bstep (se 1 (by rfl) ⟨4502258, by rfl⟩ : syracuseStep 6003011 = 9004517) B9004517
theorem B22788539 : Blo 1580488 22788539 := bstep (se 1 (by rfl) ⟨17091404, by rfl⟩ : syracuseStep 22788539 = 34182809) B34182809
theorem B1580703 : Blo 1580488 1580703 := bstep (se 1 (by rfl) ⟨1185527, by rfl⟩ : syracuseStep 1580703 = 2371055) B2371055
theorem B40533857 : Blo 1580488 40533857 := bstep (se 2 (by rfl) ⟨15200196, by rfl⟩ : syracuseStep 40533857 = 30400393) B30400393
theorem B8544575 : Blo 1580488 8544575 := bstep (se 1 (by rfl) ⟨6408431, by rfl⟩ : syracuseStep 8544575 = 12816863) B12816863
theorem B1581503 : Blo 1580488 1581503 := bstep (se 1 (by rfl) ⟨1186127, by rfl⟩ : syracuseStep 1581503 = 2372255) B2372255
theorem B9012059 : Blo 1580488 9012059 := bstep (se 1 (by rfl) ⟨6759044, by rfl⟩ : syracuseStep 9012059 = 13518089) B13518089
theorem B22808087 : Blo 1580488 22808087 := bstep (se 1 (by rfl) ⟨17106065, by rfl⟩ : syracuseStep 22808087 = 34212131) B34212131
theorem B61639379 : Blo 1580488 61639379 := bstep (se 1 (by rfl) ⟨46229534, by rfl⟩ : syracuseStep 61639379 = 92459069) B92459069
theorem B7032527 : Blo 1580488 7032527 := bstep (se 1 (by rfl) ⟨5274395, by rfl⟩ : syracuseStep 7032527 = 10548791) B10548791
theorem B4002007 : Blo 1580488 4002007 := bstep (se 1 (by rfl) ⟨3001505, by rfl⟩ : syracuseStep 4002007 = 6003011) B6003011
theorem B15192359 : Blo 1580488 15192359 := bstep (se 1 (by rfl) ⟨11394269, by rfl⟩ : syracuseStep 15192359 = 22788539) B22788539
theorem B27013823 : Blo 1580488 27013823 := bstep (se 1 (by rfl) ⟨20260367, by rfl⟩ : syracuseStep 27013823 = 40520735) B40520735
theorem B2372777 : Blo 1580488 2372777 := bstep (se 2 (by rfl) ⟨889791, by rfl⟩ : syracuseStep 2372777 = 1779583) B1779583
theorem B27022571 : Blo 1580488 27022571 := bstep (se 1 (by rfl) ⟨20266928, by rfl⟩ : syracuseStep 27022571 = 40533857) B40533857
theorem B6002207 : Blo 1580488 6002207 := bstep (se 1 (by rfl) ⟨4501655, by rfl⟩ : syracuseStep 6002207 = 9003311) B9003311
theorem B1580527 : Blo 1580488 1580527 := bstep (se 1 (by rfl) ⟨1185395, by rfl⟩ : syracuseStep 1580527 = 2370791) B2370791
theorem B17096417 : Blo 1580488 17096417 := bstep (se 2 (by rfl) ⟨6411156, by rfl⟩ : syracuseStep 17096417 = 12822313) B12822313
theorem B1581851 : Blo 1580488 1581851 := bstep (se 1 (by rfl) ⟨1186388, by rfl⟩ : syracuseStep 1581851 = 2372777) B2372777
theorem B18015047 : Blo 1580488 18015047 := bstep (se 1 (by rfl) ⟨13511285, by rfl⟩ : syracuseStep 18015047 = 27022571) B27022571
theorem B15205391 : Blo 1580488 15205391 := bstep (se 1 (by rfl) ⟨11404043, by rfl⟩ : syracuseStep 15205391 = 22808087) B22808087
theorem B41092919 : Blo 1580488 41092919 := bstep (se 1 (by rfl) ⟨30819689, by rfl⟩ : syracuseStep 41092919 = 61639379) B61639379
theorem B4688351 : Blo 1580488 4688351 := bstep (se 1 (by rfl) ⟨3516263, by rfl⟩ : syracuseStep 4688351 = 7032527) B7032527
theorem B11397611 : Blo 1580488 11397611 := bstep (se 1 (by rfl) ⟨8548208, by rfl⟩ : syracuseStep 11397611 = 17096417) B17096417
theorem B10128239 : Blo 1580488 10128239 := bstep (se 1 (by rfl) ⟨7596179, by rfl⟩ : syracuseStep 10128239 = 15192359) B15192359
theorem B5336009 : Blo 1580488 5336009 := bstep (se 2 (by rfl) ⟨2001003, by rfl⟩ : syracuseStep 5336009 = 4002007) B4002007
theorem B18009215 : Blo 1580488 18009215 := bstep (se 1 (by rfl) ⟨13506911, by rfl⟩ : syracuseStep 18009215 = 27013823) B27013823
theorem B6008039 : Blo 1580488 6008039 := bstep (se 1 (by rfl) ⟨4506029, by rfl⟩ : syracuseStep 6008039 = 9012059) B9012059
theorem B22785533 : Blo 1580488 22785533 := bstep (se 3 (by rfl) ⟨4272287, by rfl⟩ : syracuseStep 22785533 = 8544575) B8544575
theorem B4001471 : Blo 1580488 4001471 := bstep (se 1 (by rfl) ⟨3001103, by rfl⟩ : syracuseStep 4001471 = 6002207) B6002207
theorem B12010031 : Blo 1580488 12010031 := bstep (se 1 (by rfl) ⟨9007523, by rfl⟩ : syracuseStep 12010031 = 18015047) B18015047
theorem B27395279 : Blo 1580488 27395279 := bstep (se 1 (by rfl) ⟨20546459, by rfl⟩ : syracuseStep 27395279 = 41092919) B41092919
theorem B30393629 : Blo 1580488 30393629 := bstep (se 3 (by rfl) ⟨5698805, by rfl⟩ : syracuseStep 30393629 = 11397611) B11397611
theorem B6752159 : Blo 1580488 6752159 := bstep (se 1 (by rfl) ⟨5064119, by rfl⟩ : syracuseStep 6752159 = 10128239) B10128239
theorem B3557339 : Blo 1580488 3557339 := bstep (se 1 (by rfl) ⟨2668004, by rfl⟩ : syracuseStep 3557339 = 5336009) B5336009
theorem B15190355 : Blo 1580488 15190355 := bstep (se 1 (by rfl) ⟨11392766, by rfl⟩ : syracuseStep 15190355 = 22785533) B22785533
theorem B10136927 : Blo 1580488 10136927 := bstep (se 1 (by rfl) ⟨7602695, by rfl⟩ : syracuseStep 10136927 = 15205391) B15205391
theorem B3125567 : Blo 1580488 3125567 := bstep (se 1 (by rfl) ⟨2344175, by rfl⟩ : syracuseStep 3125567 = 4688351) B4688351
theorem B12006143 : Blo 1580488 12006143 := bstep (se 1 (by rfl) ⟨9004607, by rfl⟩ : syracuseStep 12006143 = 18009215) B18009215
theorem B2667647 : Blo 1580488 2667647 := bstep (se 1 (by rfl) ⟨2000735, by rfl⟩ : syracuseStep 2667647 = 4001471) B4001471
theorem B4005359 : Blo 1580488 4005359 := bstep (se 1 (by rfl) ⟨3004019, by rfl⟩ : syracuseStep 4005359 = 6008039) B6008039
theorem B8004095 : Blo 1580488 8004095 := bstep (se 1 (by rfl) ⟨6003071, by rfl⟩ : syracuseStep 8004095 = 12006143) B12006143
theorem B1778431 : Blo 1580488 1778431 := bstep (se 1 (by rfl) ⟨1333823, by rfl⟩ : syracuseStep 1778431 = 2667647) B2667647
theorem B2083711 : Blo 1580488 2083711 := bstep (se 1 (by rfl) ⟨1562783, by rfl⟩ : syracuseStep 2083711 = 3125567) B3125567
theorem B8006687 : Blo 1580488 8006687 := bstep (se 1 (by rfl) ⟨6005015, by rfl⟩ : syracuseStep 8006687 = 12010031) B12010031
theorem B18263519 : Blo 1580488 18263519 := bstep (se 1 (by rfl) ⟨13697639, by rfl⟩ : syracuseStep 18263519 = 27395279) B27395279
theorem B20262419 : Blo 1580488 20262419 := bstep (se 1 (by rfl) ⟨15196814, by rfl⟩ : syracuseStep 20262419 = 30393629) B30393629
theorem B4501439 : Blo 1580488 4501439 := bstep (se 1 (by rfl) ⟨3376079, by rfl⟩ : syracuseStep 4501439 = 6752159) B6752159
theorem B2371559 : Blo 1580488 2371559 := bstep (se 1 (by rfl) ⟨1778669, by rfl⟩ : syracuseStep 2371559 = 3557339) B3557339
theorem B40507613 : Blo 1580488 40507613 := bstep (se 3 (by rfl) ⟨7595177, by rfl⟩ : syracuseStep 40507613 = 15190355) B15190355
theorem B6757951 : Blo 1580488 6757951 := bstep (se 1 (by rfl) ⟨5068463, by rfl⟩ : syracuseStep 6757951 = 10136927) B10136927
theorem B2670239 : Blo 1580488 2670239 := bstep (se 1 (by rfl) ⟨2002679, by rfl⟩ : syracuseStep 2670239 = 4005359) B4005359
theorem B2778281 : Blo 1580488 2778281 := bstep (se 2 (by rfl) ⟨1041855, by rfl⟩ : syracuseStep 2778281 = 2083711) B2083711
theorem B12175679 : Blo 1580488 12175679 := bstep (se 1 (by rfl) ⟨9131759, by rfl⟩ : syracuseStep 12175679 = 18263519) B18263519
theorem B1780159 : Blo 1580488 1780159 := bstep (se 1 (by rfl) ⟨1335119, by rfl⟩ : syracuseStep 1780159 = 2670239) B2670239
theorem B3000959 : Blo 1580488 3000959 := bstep (se 1 (by rfl) ⟨2250719, by rfl⟩ : syracuseStep 3000959 = 4501439) B4501439
theorem B5336063 : Blo 1580488 5336063 := bstep (se 1 (by rfl) ⟨4002047, by rfl⟩ : syracuseStep 5336063 = 8004095) B8004095
theorem B2371241 : Blo 1580488 2371241 := bstep (se 2 (by rfl) ⟨889215, by rfl⟩ : syracuseStep 2371241 = 1778431) B1778431
theorem B27005075 : Blo 1580488 27005075 := bstep (se 1 (by rfl) ⟨20253806, by rfl⟩ : syracuseStep 27005075 = 40507613) B40507613
theorem B5337791 : Blo 1580488 5337791 := bstep (se 1 (by rfl) ⟨4003343, by rfl⟩ : syracuseStep 5337791 = 8006687) B8006687
theorem B9010601 : Blo 1580488 9010601 := bstep (se 2 (by rfl) ⟨3378975, by rfl⟩ : syracuseStep 9010601 = 6757951) B6757951
theorem B13508279 : Blo 1580488 13508279 := bstep (se 1 (by rfl) ⟨10131209, by rfl⟩ : syracuseStep 13508279 = 20262419) B20262419
theorem B1581039 : Blo 1580488 1581039 := bstep (se 1 (by rfl) ⟨1185779, by rfl⟩ : syracuseStep 1581039 = 2371559) B2371559
theorem B2000639 : Blo 1580488 2000639 := bstep (se 1 (by rfl) ⟨1500479, by rfl⟩ : syracuseStep 2000639 = 3000959) B3000959
theorem B3557375 : Blo 1580488 3557375 := bstep (se 1 (by rfl) ⟨2668031, by rfl⟩ : syracuseStep 3557375 = 5336063) B5336063
theorem B6007067 : Blo 1580488 6007067 := bstep (se 1 (by rfl) ⟨4505300, by rfl⟩ : syracuseStep 6007067 = 9010601) B9010601
theorem B9005519 : Blo 1580488 9005519 := bstep (se 1 (by rfl) ⟨6754139, by rfl⟩ : syracuseStep 9005519 = 13508279) B13508279
theorem B3558527 : Blo 1580488 3558527 := bstep (se 1 (by rfl) ⟨2668895, by rfl⟩ : syracuseStep 3558527 = 5337791) B5337791
theorem B29634997 : Blo 1580488 29634997 := bstep (se 5 (by rfl) ⟨1389140, by rfl⟩ : syracuseStep 29634997 = 2778281) B2778281
theorem B18003383 : Blo 1580488 18003383 := bstep (se 1 (by rfl) ⟨13502537, by rfl⟩ : syracuseStep 18003383 = 27005075) B27005075
theorem B2373545 : Blo 1580488 2373545 := bstep (se 2 (by rfl) ⟨890079, by rfl⟩ : syracuseStep 2373545 = 1780159) B1780159
theorem B8117119 : Blo 1580488 8117119 := bstep (se 1 (by rfl) ⟨6087839, by rfl⟩ : syracuseStep 8117119 = 12175679) B12175679
theorem B1580827 : Blo 1580488 1580827 := bstep (se 1 (by rfl) ⟨1185620, by rfl⟩ : syracuseStep 1580827 = 2371241) B2371241
theorem B12002255 : Blo 1580488 12002255 := bstep (se 1 (by rfl) ⟨9001691, by rfl⟩ : syracuseStep 12002255 = 18003383) B18003383
theorem B10822825 : Blo 1580488 10822825 := bstep (se 2 (by rfl) ⟨4058559, by rfl⟩ : syracuseStep 10822825 = 8117119) B8117119
theorem B1582363 : Blo 1580488 1582363 := bstep (se 1 (by rfl) ⟨1186772, by rfl⟩ : syracuseStep 1582363 = 2373545) B2373545
theorem B5335037 : Blo 1580488 5335037 := bstep (se 3 (by rfl) ⟨1000319, by rfl⟩ : syracuseStep 5335037 = 2000639) B2000639
theorem B39513329 : Blo 1580488 39513329 := bstep (se 2 (by rfl) ⟨14817498, by rfl⟩ : syracuseStep 39513329 = 29634997) B29634997
theorem B2371583 : Blo 1580488 2371583 := bstep (se 1 (by rfl) ⟨1778687, by rfl⟩ : syracuseStep 2371583 = 3557375) B3557375
theorem B2372351 : Blo 1580488 2372351 := bstep (se 1 (by rfl) ⟨1779263, by rfl⟩ : syracuseStep 2372351 = 3558527) B3558527
theorem B4004711 : Blo 1580488 4004711 := bstep (se 1 (by rfl) ⟨3003533, by rfl⟩ : syracuseStep 4004711 = 6007067) B6007067
theorem B6003679 : Blo 1580488 6003679 := bstep (se 1 (by rfl) ⟨4502759, by rfl⟩ : syracuseStep 6003679 = 9005519) B9005519
theorem B1581567 : Blo 1580488 1581567 := bstep (se 1 (by rfl) ⟨1186175, by rfl⟩ : syracuseStep 1581567 = 2372351) B2372351
theorem B57721733 : Blo 1580488 57721733 := bstep (se 4 (by rfl) ⟨5411412, by rfl⟩ : syracuseStep 57721733 = 10822825) B10822825
theorem B8004905 : Blo 1580488 8004905 := bstep (se 2 (by rfl) ⟨3001839, by rfl⟩ : syracuseStep 8004905 = 6003679) B6003679
theorem B3556691 : Blo 1580488 3556691 := bstep (se 1 (by rfl) ⟨2667518, by rfl⟩ : syracuseStep 3556691 = 5335037) B5335037
theorem B26342219 : Blo 1580488 26342219 := bstep (se 1 (by rfl) ⟨19756664, by rfl⟩ : syracuseStep 26342219 = 39513329) B39513329
theorem B8001503 : Blo 1580488 8001503 := bstep (se 1 (by rfl) ⟨6001127, by rfl⟩ : syracuseStep 8001503 = 12002255) B12002255
theorem B2669807 : Blo 1580488 2669807 := bstep (se 1 (by rfl) ⟨2002355, by rfl⟩ : syracuseStep 2669807 = 4004711) B4004711
theorem B1581055 : Blo 1580488 1581055 := bstep (se 1 (by rfl) ⟨1185791, by rfl⟩ : syracuseStep 1581055 = 2371583) B2371583
theorem B5334335 : Blo 1580488 5334335 := bstep (se 1 (by rfl) ⟨4000751, by rfl⟩ : syracuseStep 5334335 = 8001503) B8001503
theorem B1779871 : Blo 1580488 1779871 := bstep (se 1 (by rfl) ⟨1334903, by rfl⟩ : syracuseStep 1779871 = 2669807) B2669807
theorem B38481155 : Blo 1580488 38481155 := bstep (se 1 (by rfl) ⟨28860866, by rfl⟩ : syracuseStep 38481155 = 57721733) B57721733
theorem B5336603 : Blo 1580488 5336603 := bstep (se 1 (by rfl) ⟨4002452, by rfl⟩ : syracuseStep 5336603 = 8004905) B8004905
theorem B2371127 : Blo 1580488 2371127 := bstep (se 1 (by rfl) ⟨1778345, by rfl⟩ : syracuseStep 2371127 = 3556691) B3556691
theorem B70245917 : Blo 1580488 70245917 := bstep (se 3 (by rfl) ⟨13171109, by rfl⟩ : syracuseStep 70245917 = 26342219) B26342219
theorem B3556223 : Blo 1580488 3556223 := bstep (se 1 (by rfl) ⟨2667167, by rfl⟩ : syracuseStep 3556223 = 5334335) B5334335
theorem B3557735 : Blo 1580488 3557735 := bstep (se 1 (by rfl) ⟨2668301, by rfl⟩ : syracuseStep 3557735 = 5336603) B5336603
theorem B25654103 : Blo 1580488 25654103 := bstep (se 1 (by rfl) ⟨19240577, by rfl⟩ : syracuseStep 25654103 = 38481155) B38481155
theorem B46830611 : Blo 1580488 46830611 := bstep (se 1 (by rfl) ⟨35122958, by rfl⟩ : syracuseStep 46830611 = 70245917) B70245917
theorem B2373161 : Blo 1580488 2373161 := bstep (se 2 (by rfl) ⟨889935, by rfl⟩ : syracuseStep 2373161 = 1779871) B1779871
theorem B1580751 : Blo 1580488 1580751 := bstep (se 1 (by rfl) ⟨1185563, by rfl⟩ : syracuseStep 1580751 = 2371127) B2371127
theorem B1582107 : Blo 1580488 1582107 := bstep (se 1 (by rfl) ⟨1186580, by rfl⟩ : syracuseStep 1582107 = 2373161) B2373161
theorem B124881629 : Blo 1580488 124881629 := bstep (se 3 (by rfl) ⟨23415305, by rfl⟩ : syracuseStep 124881629 = 46830611) B46830611
theorem B2370815 : Blo 1580488 2370815 := bstep (se 1 (by rfl) ⟨1778111, by rfl⟩ : syracuseStep 2370815 = 3556223) B3556223
theorem B2371823 : Blo 1580488 2371823 := bstep (se 1 (by rfl) ⟨1778867, by rfl⟩ : syracuseStep 2371823 = 3557735) B3557735
theorem B17102735 : Blo 1580488 17102735 := bstep (se 1 (by rfl) ⟨12827051, by rfl⟩ : syracuseStep 17102735 = 25654103) B25654103
theorem B1581215 : Blo 1580488 1581215 := bstep (se 1 (by rfl) ⟨1185911, by rfl⟩ : syracuseStep 1581215 = 2371823) B2371823
theorem B333017677 : Blo 1580488 333017677 := bstep (se 3 (by rfl) ⟨62440814, by rfl⟩ : syracuseStep 333017677 = 124881629) B124881629
theorem B11401823 : Blo 1580488 11401823 := bstep (se 1 (by rfl) ⟨8551367, by rfl⟩ : syracuseStep 11401823 = 17102735) B17102735
theorem B1580543 : Blo 1580488 1580543 := bstep (se 1 (by rfl) ⟨1185407, by rfl⟩ : syracuseStep 1580543 = 2370815) B2370815
theorem B444023569 : Blo 1580488 444023569 := bstep (se 2 (by rfl) ⟨166508838, by rfl⟩ : syracuseStep 444023569 = 333017677) B333017677
theorem B7601215 : Blo 1580488 7601215 := bstep (se 1 (by rfl) ⟨5700911, by rfl⟩ : syracuseStep 7601215 = 11401823) B11401823
theorem B10134953 : Blo 1580488 10134953 := bstep (se 2 (by rfl) ⟨3800607, by rfl⟩ : syracuseStep 10134953 = 7601215) B7601215
theorem B592031425 : Blo 1580488 592031425 := bstep (se 2 (by rfl) ⟨222011784, by rfl⟩ : syracuseStep 592031425 = 444023569) B444023569
theorem B789375233 : Blo 1580488 789375233 := bstep (se 2 (by rfl) ⟨296015712, by rfl⟩ : syracuseStep 789375233 = 592031425) B592031425
theorem B6756635 : Blo 1580488 6756635 := bstep (se 1 (by rfl) ⟨5067476, by rfl⟩ : syracuseStep 6756635 = 10134953) B10134953
theorem B2105000621 : Blo 1580488 2105000621 := bstep (se 3 (by rfl) ⟨394687616, by rfl⟩ : syracuseStep 2105000621 = 789375233) B789375233
theorem B4504423 : Blo 1580488 4504423 := bstep (se 1 (by rfl) ⟨3378317, by rfl⟩ : syracuseStep 4504423 = 6756635) B6756635
theorem B6005897 : Blo 1580488 6005897 := bstep (se 2 (by rfl) ⟨2252211, by rfl⟩ : syracuseStep 6005897 = 4504423) B4504423
theorem B1403333747 : Blo 1580488 1403333747 := bstep (se 1 (by rfl) ⟨1052500310, by rfl⟩ : syracuseStep 1403333747 = 2105000621) B2105000621
theorem B935555831 : Blo 1580488 935555831 := bstep (se 1 (by rfl) ⟨701666873, by rfl⟩ : syracuseStep 935555831 = 1403333747) B1403333747
theorem B4003931 : Blo 1580488 4003931 := bstep (se 1 (by rfl) ⟨3002948, by rfl⟩ : syracuseStep 4003931 = 6005897) B6005897
theorem B623703887 : Blo 1580488 623703887 := bstep (se 1 (by rfl) ⟨467777915, by rfl⟩ : syracuseStep 623703887 = 935555831) B935555831
theorem B2669287 : Blo 1580488 2669287 := bstep (se 1 (by rfl) ⟨2001965, by rfl⟩ : syracuseStep 2669287 = 4003931) B4003931
theorem B415802591 : Blo 1580488 415802591 := bstep (se 1 (by rfl) ⟨311851943, by rfl⟩ : syracuseStep 415802591 = 623703887) B623703887
theorem B3559049 : Blo 1580488 3559049 := bstep (se 2 (by rfl) ⟨1334643, by rfl⟩ : syracuseStep 3559049 = 2669287) B2669287
theorem B277201727 : Blo 1580488 277201727 := bstep (se 1 (by rfl) ⟨207901295, by rfl⟩ : syracuseStep 277201727 = 415802591) B415802591
theorem B2372699 : Blo 1580488 2372699 := bstep (se 1 (by rfl) ⟨1779524, by rfl⟩ : syracuseStep 2372699 = 3559049) B3559049
theorem B1581799 : Blo 1580488 1581799 := bstep (se 1 (by rfl) ⟨1186349, by rfl⟩ : syracuseStep 1581799 = 2372699) B2372699
theorem B184801151 : Blo 1580488 184801151 := bstep (se 1 (by rfl) ⟨138600863, by rfl⟩ : syracuseStep 184801151 = 277201727) B277201727
theorem B123200767 : Blo 1580488 123200767 := bstep (se 1 (by rfl) ⟨92400575, by rfl⟩ : syracuseStep 123200767 = 184801151) B184801151
theorem B164267689 : Blo 1580488 164267689 := bstep (se 2 (by rfl) ⟨61600383, by rfl⟩ : syracuseStep 164267689 = 123200767) B123200767
theorem B219023585 : Blo 1580488 219023585 := bstep (se 2 (by rfl) ⟨82133844, by rfl⟩ : syracuseStep 219023585 = 164267689) B164267689
theorem B146015723 : Blo 1580488 146015723 := bstep (se 1 (by rfl) ⟨109511792, by rfl⟩ : syracuseStep 146015723 = 219023585) B219023585
theorem B97343815 : Blo 1580488 97343815 := bstep (se 1 (by rfl) ⟨73007861, by rfl⟩ : syracuseStep 97343815 = 146015723) B146015723
theorem B129791753 : Blo 1580488 129791753 := bstep (se 2 (by rfl) ⟨48671907, by rfl⟩ : syracuseStep 129791753 = 97343815) B97343815
theorem B86527835 : Blo 1580488 86527835 := bstep (se 1 (by rfl) ⟨64895876, by rfl⟩ : syracuseStep 86527835 = 129791753) B129791753
theorem B57685223 : Blo 1580488 57685223 := bstep (se 1 (by rfl) ⟨43263917, by rfl⟩ : syracuseStep 57685223 = 86527835) B86527835
theorem B153827261 : Blo 1580488 153827261 := bstep (se 3 (by rfl) ⟨28842611, by rfl⟩ : syracuseStep 153827261 = 57685223) B57685223
theorem B102551507 : Blo 1580488 102551507 := bstep (se 1 (by rfl) ⟨76913630, by rfl⟩ : syracuseStep 102551507 = 153827261) B153827261
theorem B68367671 : Blo 1580488 68367671 := bstep (se 1 (by rfl) ⟨51275753, by rfl⟩ : syracuseStep 68367671 = 102551507) B102551507
theorem B45578447 : Blo 1580488 45578447 := bstep (se 1 (by rfl) ⟨34183835, by rfl⟩ : syracuseStep 45578447 = 68367671) B68367671
theorem B30385631 : Blo 1580488 30385631 := bstep (se 1 (by rfl) ⟨22789223, by rfl⟩ : syracuseStep 30385631 = 45578447) B45578447
theorem B20257087 : Blo 1580488 20257087 := bstep (se 1 (by rfl) ⟨15192815, by rfl⟩ : syracuseStep 20257087 = 30385631) B30385631
theorem B27009449 : Blo 1580488 27009449 := bstep (se 2 (by rfl) ⟨10128543, by rfl⟩ : syracuseStep 27009449 = 20257087) B20257087
theorem B18006299 : Blo 1580488 18006299 := bstep (se 1 (by rfl) ⟨13504724, by rfl⟩ : syracuseStep 18006299 = 27009449) B27009449
theorem B12004199 : Blo 1580488 12004199 := bstep (se 1 (by rfl) ⟨9003149, by rfl⟩ : syracuseStep 12004199 = 18006299) B18006299
theorem B8002799 : Blo 1580488 8002799 := bstep (se 1 (by rfl) ⟨6002099, by rfl⟩ : syracuseStep 8002799 = 12004199) B12004199
theorem B5335199 : Blo 1580488 5335199 := bstep (se 1 (by rfl) ⟨4001399, by rfl⟩ : syracuseStep 5335199 = 8002799) B8002799
theorem B3556799 : Blo 1580488 3556799 := bstep (se 1 (by rfl) ⟨2667599, by rfl⟩ : syracuseStep 3556799 = 5335199) B5335199
theorem B2371199 : Blo 1580488 2371199 := bstep (se 1 (by rfl) ⟨1778399, by rfl⟩ : syracuseStep 2371199 = 3556799) B3556799
theorem B1580799 : Blo 1580488 1580799 := bstep (se 1 (by rfl) ⟨1185599, by rfl⟩ : syracuseStep 1580799 = 2371199) B2371199

theorem C0 (j : ℕ) (h1 : 395122 ≤ j) (h2 : j ≤ 395621) : Blo 1580488 (4 * j + 3) := by
  interval_cases j
  · exact B1580491
  · exact B1580495
  · exact B1580499
  · exact B1580503
  · exact B1580507
  · exact B1580511
  · exact B1580515
  · exact B1580519
  · exact B1580523
  · exact B1580527
  · exact B1580531
  · exact B1580535
  · exact B1580539
  · exact B1580543
  · exact B1580547
  · exact B1580551
  · exact B1580555
  · exact B1580559
  · exact B1580563
  · exact B1580567
  · exact B1580571
  · exact B1580575
  · exact B1580579
  · exact B1580583
  · exact B1580587
  · exact B1580591
  · exact B1580595
  · exact B1580599
  · exact B1580603
  · exact B1580607
  · exact B1580611
  · exact B1580615
  · exact B1580619
  · exact B1580623
  · exact B1580627
  · exact B1580631
  · exact B1580635
  · exact B1580639
  · exact B1580643
  · exact B1580647
  · exact B1580651
  · exact B1580655
  · exact B1580659
  · exact B1580663
  · exact B1580667
  · exact B1580671
  · exact B1580675
  · exact B1580679
  · exact B1580683
  · exact B1580687
  · exact B1580691
  · exact B1580695
  · exact B1580699
  · exact B1580703
  · exact B1580707
  · exact B1580711
  · exact B1580715
  · exact B1580719
  · exact B1580723
  · exact B1580727
  · exact B1580731
  · exact B1580735
  · exact B1580739
  · exact B1580743
  · exact B1580747
  · exact B1580751
  · exact B1580755
  · exact B1580759
  · exact B1580763
  · exact B1580767
  · exact B1580771
  · exact B1580775
  · exact B1580779
  · exact B1580783
  · exact B1580787
  · exact B1580791
  · exact B1580795
  · exact B1580799
  · exact B1580803
  · exact B1580807
  · exact B1580811
  · exact B1580815
  · exact B1580819
  · exact B1580823
  · exact B1580827
  · exact B1580831
  · exact B1580835
  · exact B1580839
  · exact B1580843
  · exact B1580847
  · exact B1580851
  · exact B1580855
  · exact B1580859
  · exact B1580863
  · exact B1580867
  · exact B1580871
  · exact B1580875
  · exact B1580879
  · exact B1580883
  · exact B1580887
  · exact B1580891
  · exact B1580895
  · exact B1580899
  · exact B1580903
  · exact B1580907
  · exact B1580911
  · exact B1580915
  · exact B1580919
  · exact B1580923
  · exact B1580927
  · exact B1580931
  · exact B1580935
  · exact B1580939
  · exact B1580943
  · exact B1580947
  · exact B1580951
  · exact B1580955
  · exact B1580959
  · exact B1580963
  · exact B1580967
  · exact B1580971
  · exact B1580975
  · exact B1580979
  · exact B1580983
  · exact B1580987
  · exact B1580991
  · exact B1580995
  · exact B1580999
  · exact B1581003
  · exact B1581007
  · exact B1581011
  · exact B1581015
  · exact B1581019
  · exact B1581023
  · exact B1581027
  · exact B1581031
  · exact B1581035
  · exact B1581039
  · exact B1581043
  · exact B1581047
  · exact B1581051
  · exact B1581055
  · exact B1581059
  · exact B1581063
  · exact B1581067
  · exact B1581071
  · exact B1581075
  · exact B1581079
  · exact B1581083
  · exact B1581087
  · exact B1581091
  · exact B1581095
  · exact B1581099
  · exact B1581103
  · exact B1581107
  · exact B1581111
  · exact B1581115
  · exact B1581119
  · exact B1581123
  · exact B1581127
  · exact B1581131
  · exact B1581135
  · exact B1581139
  · exact B1581143
  · exact B1581147
  · exact B1581151
  · exact B1581155
  · exact B1581159
  · exact B1581163
  · exact B1581167
  · exact B1581171
  · exact B1581175
  · exact B1581179
  · exact B1581183
  · exact B1581187
  · exact B1581191
  · exact B1581195
  · exact B1581199
  · exact B1581203
  · exact B1581207
  · exact B1581211
  · exact B1581215
  · exact B1581219
  · exact B1581223
  · exact B1581227
  · exact B1581231
  · exact B1581235
  · exact B1581239
  · exact B1581243
  · exact B1581247
  · exact B1581251
  · exact B1581255
  · exact B1581259
  · exact B1581263
  · exact B1581267
  · exact B1581271
  · exact B1581275
  · exact B1581279
  · exact B1581283
  · exact B1581287
  · exact B1581291
  · exact B1581295
  · exact B1581299
  · exact B1581303
  · exact B1581307
  · exact B1581311
  · exact B1581315
  · exact B1581319
  · exact B1581323
  · exact B1581327
  · exact B1581331
  · exact B1581335
  · exact B1581339
  · exact B1581343
  · exact B1581347
  · exact B1581351
  · exact B1581355
  · exact B1581359
  · exact B1581363
  · exact B1581367
  · exact B1581371
  · exact B1581375
  · exact B1581379
  · exact B1581383
  · exact B1581387
  · exact B1581391
  · exact B1581395
  · exact B1581399
  · exact B1581403
  · exact B1581407
  · exact B1581411
  · exact B1581415
  · exact B1581419
  · exact B1581423
  · exact B1581427
  · exact B1581431
  · exact B1581435
  · exact B1581439
  · exact B1581443
  · exact B1581447
  · exact B1581451
  · exact B1581455
  · exact B1581459
  · exact B1581463
  · exact B1581467
  · exact B1581471
  · exact B1581475
  · exact B1581479
  · exact B1581483
  · exact B1581487
  · exact B1581491
  · exact B1581495
  · exact B1581499
  · exact B1581503
  · exact B1581507
  · exact B1581511
  · exact B1581515
  · exact B1581519
  · exact B1581523
  · exact B1581527
  · exact B1581531
  · exact B1581535
  · exact B1581539
  · exact B1581543
  · exact B1581547
  · exact B1581551
  · exact B1581555
  · exact B1581559
  · exact B1581563
  · exact B1581567
  · exact B1581571
  · exact B1581575
  · exact B1581579
  · exact B1581583
  · exact B1581587
  · exact B1581591
  · exact B1581595
  · exact B1581599
  · exact B1581603
  · exact B1581607
  · exact B1581611
  · exact B1581615
  · exact B1581619
  · exact B1581623
  · exact B1581627
  · exact B1581631
  · exact B1581635
  · exact B1581639
  · exact B1581643
  · exact B1581647
  · exact B1581651
  · exact B1581655
  · exact B1581659
  · exact B1581663
  · exact B1581667
  · exact B1581671
  · exact B1581675
  · exact B1581679
  · exact B1581683
  · exact B1581687
  · exact B1581691
  · exact B1581695
  · exact B1581699
  · exact B1581703
  · exact B1581707
  · exact B1581711
  · exact B1581715
  · exact B1581719
  · exact B1581723
  · exact B1581727
  · exact B1581731
  · exact B1581735
  · exact B1581739
  · exact B1581743
  · exact B1581747
  · exact B1581751
  · exact B1581755
  · exact B1581759
  · exact B1581763
  · exact B1581767
  · exact B1581771
  · exact B1581775
  · exact B1581779
  · exact B1581783
  · exact B1581787
  · exact B1581791
  · exact B1581795
  · exact B1581799
  · exact B1581803
  · exact B1581807
  · exact B1581811
  · exact B1581815
  · exact B1581819
  · exact B1581823
  · exact B1581827
  · exact B1581831
  · exact B1581835
  · exact B1581839
  · exact B1581843
  · exact B1581847
  · exact B1581851
  · exact B1581855
  · exact B1581859
  · exact B1581863
  · exact B1581867
  · exact B1581871
  · exact B1581875
  · exact B1581879
  · exact B1581883
  · exact B1581887
  · exact B1581891
  · exact B1581895
  · exact B1581899
  · exact B1581903
  · exact B1581907
  · exact B1581911
  · exact B1581915
  · exact B1581919
  · exact B1581923
  · exact B1581927
  · exact B1581931
  · exact B1581935
  · exact B1581939
  · exact B1581943
  · exact B1581947
  · exact B1581951
  · exact B1581955
  · exact B1581959
  · exact B1581963
  · exact B1581967
  · exact B1581971
  · exact B1581975
  · exact B1581979
  · exact B1581983
  · exact B1581987
  · exact B1581991
  · exact B1581995
  · exact B1581999
  · exact B1582003
  · exact B1582007
  · exact B1582011
  · exact B1582015
  · exact B1582019
  · exact B1582023
  · exact B1582027
  · exact B1582031
  · exact B1582035
  · exact B1582039
  · exact B1582043
  · exact B1582047
  · exact B1582051
  · exact B1582055
  · exact B1582059
  · exact B1582063
  · exact B1582067
  · exact B1582071
  · exact B1582075
  · exact B1582079
  · exact B1582083
  · exact B1582087
  · exact B1582091
  · exact B1582095
  · exact B1582099
  · exact B1582103
  · exact B1582107
  · exact B1582111
  · exact B1582115
  · exact B1582119
  · exact B1582123
  · exact B1582127
  · exact B1582131
  · exact B1582135
  · exact B1582139
  · exact B1582143
  · exact B1582147
  · exact B1582151
  · exact B1582155
  · exact B1582159
  · exact B1582163
  · exact B1582167
  · exact B1582171
  · exact B1582175
  · exact B1582179
  · exact B1582183
  · exact B1582187
  · exact B1582191
  · exact B1582195
  · exact B1582199
  · exact B1582203
  · exact B1582207
  · exact B1582211
  · exact B1582215
  · exact B1582219
  · exact B1582223
  · exact B1582227
  · exact B1582231
  · exact B1582235
  · exact B1582239
  · exact B1582243
  · exact B1582247
  · exact B1582251
  · exact B1582255
  · exact B1582259
  · exact B1582263
  · exact B1582267
  · exact B1582271
  · exact B1582275
  · exact B1582279
  · exact B1582283
  · exact B1582287
  · exact B1582291
  · exact B1582295
  · exact B1582299
  · exact B1582303
  · exact B1582307
  · exact B1582311
  · exact B1582315
  · exact B1582319
  · exact B1582323
  · exact B1582327
  · exact B1582331
  · exact B1582335
  · exact B1582339
  · exact B1582343
  · exact B1582347
  · exact B1582351
  · exact B1582355
  · exact B1582359
  · exact B1582363
  · exact B1582367
  · exact B1582371
  · exact B1582375
  · exact B1582379
  · exact B1582383
  · exact B1582387
  · exact B1582391
  · exact B1582395
  · exact B1582399
  · exact B1582403
  · exact B1582407
  · exact B1582411
  · exact B1582415
  · exact B1582419
  · exact B1582423
  · exact B1582427
  · exact B1582431
  · exact B1582435
  · exact B1582439
  · exact B1582443
  · exact B1582447
  · exact B1582451
  · exact B1582455
  · exact B1582459
  · exact B1582463
  · exact B1582467
  · exact B1582471
  · exact B1582475
  · exact B1582479
  · exact B1582483
  · exact B1582487

theorem solution (m : ℕ) (hlo : 1580488 ≤ m) (hhi : m ≤ 1582488) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 395122 ≤ j := by omega
    have hj2 : j ≤ 395621 := by omega
    have hb : Blo 1580488 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
