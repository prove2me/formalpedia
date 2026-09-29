-- Prove2me | solution 1 for syracuse_descends_range_1640019_1642019
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:16:06.713132+00:00
-- url     : https://prove2.me/submissions/81a33e3d-6145-4c6f-b3b4-49c841dd5304

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


theorem B2768917 : Blo 1640019 2768917 := bbase (se 6 (by rfl) ⟨64896, by rfl⟩ : syracuseStep 2768917 = 129793) (by norm_num)
theorem B2629693 : Blo 1640019 2629693 := bbase (se 3 (by rfl) ⟨493067, by rfl⟩ : syracuseStep 2629693 = 986135) (by norm_num)
theorem B5537861 : Blo 1640019 5537861 := bbase (se 4 (by rfl) ⟨519174, by rfl⟩ : syracuseStep 5537861 = 1038349) (by norm_num)
theorem B2769005 : Blo 1640019 2769005 := bbase (se 3 (by rfl) ⟨519188, by rfl⟩ : syracuseStep 2769005 = 1038377) (by norm_num)
theorem B4153477 : Blo 1640019 4153477 := bbase (se 4 (by rfl) ⟨389388, by rfl⟩ : syracuseStep 4153477 = 778777) (by norm_num)
theorem B14016725 : Blo 1640019 14016725 := bbase (se 7 (by rfl) ⟨164258, by rfl⟩ : syracuseStep 14016725 = 328517) (by norm_num)
theorem B2957525 : Blo 1640019 2957525 := bbase (se 7 (by rfl) ⟨34658, by rfl⟩ : syracuseStep 2957525 = 69317) (by norm_num)
theorem B1753321 : Blo 1640019 1753321 := bbase (se 2 (by rfl) ⟨657495, by rfl⟩ : syracuseStep 1753321 = 1314991) (by norm_num)
theorem B2769133 : Blo 1640019 2769133 := bbase (se 3 (by rfl) ⟨519212, by rfl⟩ : syracuseStep 2769133 = 1038425) (by norm_num)
theorem B4153589 : Blo 1640019 4153589 := bbase (se 5 (by rfl) ⟨194699, by rfl⟩ : syracuseStep 4153589 = 389399) (by norm_num)
theorem B1663301 : Blo 1640019 1663301 := bbase (se 4 (by rfl) ⟨155934, by rfl⟩ : syracuseStep 1663301 = 311869) (by norm_num)
theorem B2769221 : Blo 1640019 2769221 := bbase (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) (by norm_num)
theorem B9732469 : Blo 1640019 9732469 := bbase (se 5 (by rfl) ⟨456209, by rfl⟩ : syracuseStep 9732469 = 912419) (by norm_num)
theorem B3506581 : Blo 1640019 3506581 := bbase (se 6 (by rfl) ⟨82185, by rfl⟩ : syracuseStep 3506581 = 164371) (by norm_num)
theorem B4153781 : Blo 1640019 4153781 := bbase (se 5 (by rfl) ⟨194708, by rfl⟩ : syracuseStep 4153781 = 389417) (by norm_num)
theorem B2769349 : Blo 1640019 2769349 := bbase (se 4 (by rfl) ⟨259626, by rfl⟩ : syracuseStep 2769349 = 519253) (by norm_num)
theorem B6316501 : Blo 1640019 6316501 := bbase (se 7 (by rfl) ⟨74021, by rfl⟩ : syracuseStep 6316501 = 148043) (by norm_num)
theorem B5538293 : Blo 1640019 5538293 := bbase (se 5 (by rfl) ⟨259607, by rfl⟩ : syracuseStep 5538293 = 519215) (by norm_num)
theorem B4735493 : Blo 1640019 4735493 := bbase (se 4 (by rfl) ⟨443952, by rfl⟩ : syracuseStep 4735493 = 887905) (by norm_num)
theorem B2769437 : Blo 1640019 2769437 := bbase (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) (by norm_num)
theorem B3998261 : Blo 1640019 3998261 := bbase (se 5 (by rfl) ⟨187418, by rfl⟩ : syracuseStep 3998261 = 374837) (by norm_num)
theorem B3744397 : Blo 1640019 3744397 := bbase (se 3 (by rfl) ⟨702074, by rfl⟩ : syracuseStep 3744397 = 1404149) (by norm_num)
theorem B23667349 : Blo 1640019 23667349 := bbase (se 6 (by rfl) ⟨554703, by rfl⟩ : syracuseStep 23667349 = 1109407) (by norm_num)
theorem B2769565 : Blo 1640019 2769565 := bbase (se 3 (by rfl) ⟨519293, by rfl⟩ : syracuseStep 2769565 = 1038587) (by norm_num)
theorem B2335397 : Blo 1640019 2335397 := bbase (se 4 (by rfl) ⟨218943, by rfl⟩ : syracuseStep 2335397 = 437887) (by norm_num)
theorem B1663673 : Blo 1640019 1663673 := bbase (se 2 (by rfl) ⟨623877, by rfl⟩ : syracuseStep 1663673 = 1247755) (by norm_num)
theorem B2769653 : Blo 1640019 2769653 := bbase (se 5 (by rfl) ⟨129827, by rfl⟩ : syracuseStep 2769653 = 259655) (by norm_num)
theorem B3113741 : Blo 1640019 3113741 := bbase (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) (by norm_num)
theorem B4154125 : Blo 1640019 4154125 := bbase (se 3 (by rfl) ⟨778898, by rfl⟩ : syracuseStep 4154125 = 1557797) (by norm_num)
theorem B15770389 : Blo 1640019 15770389 := bbase (se 6 (by rfl) ⟨369618, by rfl⟩ : syracuseStep 15770389 = 739237) (by norm_num)
theorem B2106157 : Blo 1640019 2106157 := bbase (se 3 (by rfl) ⟨394904, by rfl⟩ : syracuseStep 2106157 = 789809) (by norm_num)
theorem B4670293 : Blo 1640019 4670293 := bbase (se 9 (by rfl) ⟨13682, by rfl⟩ : syracuseStep 4670293 = 27365) (by norm_num)
theorem B2769781 : Blo 1640019 2769781 := bbase (se 5 (by rfl) ⟨129833, by rfl⟩ : syracuseStep 2769781 = 259667) (by norm_num)
theorem B4154237 : Blo 1640019 4154237 := bbase (se 3 (by rfl) ⟨778919, by rfl⟩ : syracuseStep 4154237 = 1557839) (by norm_num)
theorem B3113893 : Blo 1640019 3113893 := bbase (se 4 (by rfl) ⟨291927, by rfl⟩ : syracuseStep 3113893 = 583855) (by norm_num)
theorem B5538725 : Blo 1640019 5538725 := bbase (se 4 (by rfl) ⟨519255, by rfl⟩ : syracuseStep 5538725 = 1038511) (by norm_num)
theorem B2769869 : Blo 1640019 2769869 := bbase (se 3 (by rfl) ⟨519350, by rfl⟩ : syracuseStep 2769869 = 1038701) (by norm_num)
theorem B4670453 : Blo 1640019 4670453 := bbase (se 5 (by rfl) ⟨218927, by rfl⟩ : syracuseStep 4670453 = 437855) (by norm_num)
theorem B1663997 : Blo 1640019 1663997 := bbase (se 3 (by rfl) ⟨311999, by rfl⟩ : syracuseStep 1663997 = 623999) (by norm_num)
theorem B11994133 : Blo 1640019 11994133 := bbase (se 6 (by rfl) ⟨281112, by rfl⟩ : syracuseStep 11994133 = 562225) (by norm_num)
theorem B9348149 : Blo 1640019 9348149 := bbase (se 5 (by rfl) ⟨438194, by rfl⟩ : syracuseStep 9348149 = 876389) (by norm_num)
theorem B4154429 : Blo 1640019 4154429 := bbase (se 3 (by rfl) ⟨778955, by rfl⟩ : syracuseStep 4154429 = 1557911) (by norm_num)
theorem B2769997 : Blo 1640019 2769997 := bbase (se 3 (by rfl) ⟨519374, by rfl⟩ : syracuseStep 2769997 = 1038749) (by norm_num)
theorem B5260373 : Blo 1640019 5260373 := bbase (se 8 (by rfl) ⟨30822, by rfl⟩ : syracuseStep 5260373 = 61645) (by norm_num)
theorem B2106469 : Blo 1640019 2106469 := bbase (se 4 (by rfl) ⟨197481, by rfl⟩ : syracuseStep 2106469 = 394963) (by norm_num)
theorem B8307845 : Blo 1640019 8307845 := bbase (se 4 (by rfl) ⟨778860, by rfl⟩ : syracuseStep 8307845 = 1557721) (by norm_num)
theorem B2770085 : Blo 1640019 2770085 := bbase (se 4 (by rfl) ⟨259695, by rfl⟩ : syracuseStep 2770085 = 519391) (by norm_num)
theorem B7013573 : Blo 1640019 7013573 := bbase (se 4 (by rfl) ⟨657522, by rfl⟩ : syracuseStep 7013573 = 1315045) (by norm_num)
theorem B3114197 : Blo 1640019 3114197 := bbase (se 7 (by rfl) ⟨36494, by rfl⟩ : syracuseStep 3114197 = 72989) (by norm_num)
theorem B4670693 : Blo 1640019 4670693 := bbase (se 4 (by rfl) ⟨437877, by rfl⟩ : syracuseStep 4670693 = 875755) (by norm_num)
theorem B12625141 : Blo 1640019 12625141 := bbase (se 5 (by rfl) ⟨591803, by rfl⟩ : syracuseStep 12625141 = 1183607) (by norm_num)
theorem B4433173 : Blo 1640019 4433173 := bbase (se 6 (by rfl) ⟨103902, by rfl⟩ : syracuseStep 4433173 = 207805) (by norm_num)
theorem B2770213 : Blo 1640019 2770213 := bbase (se 4 (by rfl) ⟨259707, by rfl⟩ : syracuseStep 2770213 = 519415) (by norm_num)
theorem B5539157 : Blo 1640019 5539157 := bbase (se 12 (by rfl) ⟨2028, by rfl⟩ : syracuseStep 5539157 = 4057) (by norm_num)
theorem B2770301 : Blo 1640019 2770301 := bbase (se 3 (by rfl) ⟨519431, by rfl⟩ : syracuseStep 2770301 = 1038863) (by norm_num)
theorem B2336149 : Blo 1640019 2336149 := bbase (se 6 (by rfl) ⟨54753, by rfl⟩ : syracuseStep 2336149 = 109507) (by norm_num)
theorem B4154773 : Blo 1640019 4154773 := bbase (se 6 (by rfl) ⟨97377, by rfl⟩ : syracuseStep 4154773 = 194755) (by norm_num)
theorem B4670885 : Blo 1640019 4670885 := bbase (se 4 (by rfl) ⟨437895, by rfl⟩ : syracuseStep 4670885 = 875791) (by norm_num)
theorem B12461525 : Blo 1640019 12461525 := bbase (se 7 (by rfl) ⟨146033, by rfl⟩ : syracuseStep 12461525 = 292067) (by norm_num)
theorem B2770429 : Blo 1640019 2770429 := bbase (se 3 (by rfl) ⟨519455, by rfl⟩ : syracuseStep 2770429 = 1038911) (by norm_num)
theorem B4154885 : Blo 1640019 4154885 := bbase (se 4 (by rfl) ⟨389520, by rfl⟩ : syracuseStep 4154885 = 779041) (by norm_num)
theorem B7005781 : Blo 1640019 7005781 := bbase (se 8 (by rfl) ⟨41049, by rfl⟩ : syracuseStep 7005781 = 82099) (by norm_num)
theorem B2770517 : Blo 1640019 2770517 := bbase (se 8 (by rfl) ⟨16233, by rfl⟩ : syracuseStep 2770517 = 32467) (by norm_num)
theorem B4155077 : Blo 1640019 4155077 := bbase (se 4 (by rfl) ⟨389538, by rfl⟩ : syracuseStep 4155077 = 779077) (by norm_num)
theorem B2770645 : Blo 1640019 2770645 := bbase (se 7 (by rfl) ⟨32468, by rfl⟩ : syracuseStep 2770645 = 64937) (by norm_num)
theorem B5539589 : Blo 1640019 5539589 := bbase (se 4 (by rfl) ⟨519336, by rfl⟩ : syracuseStep 5539589 = 1038673) (by norm_num)
theorem B2770733 : Blo 1640019 2770733 := bbase (se 3 (by rfl) ⟨519512, by rfl⟩ : syracuseStep 2770733 = 1039025) (by norm_num)
theorem B4433717 : Blo 1640019 4433717 := bbase (se 5 (by rfl) ⟨207830, by rfl⟩ : syracuseStep 4433717 = 415661) (by norm_num)
theorem B1845049 : Blo 1640019 1845049 := bbase (se 2 (by rfl) ⟨691893, by rfl⟩ : syracuseStep 1845049 = 1383787) (by norm_num)
theorem B1845085 : Blo 1640019 1845085 := bbase (se 3 (by rfl) ⟨345953, by rfl⟩ : syracuseStep 1845085 = 691907) (by norm_num)
theorem B4212589 : Blo 1640019 4212589 := bbase (se 3 (by rfl) ⟨789860, by rfl⟩ : syracuseStep 4212589 = 1579721) (by norm_num)
theorem B1845121 : Blo 1640019 1845121 := bbase (se 2 (by rfl) ⟨691920, by rfl⟩ : syracuseStep 1845121 = 1383841) (by norm_num)
theorem B1845157 : Blo 1640019 1845157 := bbase (se 4 (by rfl) ⟨172983, by rfl⟩ : syracuseStep 1845157 = 345967) (by norm_num)
theorem B2770861 : Blo 1640019 2770861 := bbase (se 3 (by rfl) ⟨519536, by rfl⟩ : syracuseStep 2770861 = 1039073) (by norm_num)
theorem B3114949 : Blo 1640019 3114949 := bbase (se 4 (by rfl) ⟨292026, by rfl⟩ : syracuseStep 3114949 = 584053) (by norm_num)
theorem B1845193 : Blo 1640019 1845193 := bbase (se 2 (by rfl) ⟨691947, by rfl⟩ : syracuseStep 1845193 = 1383895) (by norm_num)
theorem B5400533 : Blo 1640019 5400533 := bbase (se 7 (by rfl) ⟨63287, by rfl⟩ : syracuseStep 5400533 = 126575) (by norm_num)
theorem B10512341 : Blo 1640019 10512341 := bbase (se 7 (by rfl) ⟨123191, by rfl⟩ : syracuseStep 10512341 = 246383) (by norm_num)
theorem B1845229 : Blo 1640019 1845229 := bbase (se 3 (by rfl) ⟨345980, by rfl⟩ : syracuseStep 1845229 = 691961) (by norm_num)
theorem B1845265 : Blo 1640019 1845265 := bbase (se 2 (by rfl) ⟨691974, by rfl⟩ : syracuseStep 1845265 = 1383949) (by norm_num)
theorem B4155421 : Blo 1640019 4155421 := bbase (se 3 (by rfl) ⟨779141, by rfl⟩ : syracuseStep 4155421 = 1558283) (by norm_num)
theorem B1845301 : Blo 1640019 1845301 := bbase (se 5 (by rfl) ⟨86498, by rfl⟩ : syracuseStep 1845301 = 172997) (by norm_num)
theorem B5916725 : Blo 1640019 5916725 := bbase (se 5 (by rfl) ⟨277346, by rfl⟩ : syracuseStep 5916725 = 554693) (by norm_num)
theorem B3115093 : Blo 1640019 3115093 := bbase (se 8 (by rfl) ⟨18252, by rfl⟩ : syracuseStep 3115093 = 36505) (by norm_num)
theorem B1845337 : Blo 1640019 1845337 := bbase (se 2 (by rfl) ⟨692001, by rfl⟩ : syracuseStep 1845337 = 1384003) (by norm_num)
theorem B1845373 : Blo 1640019 1845373 := bbase (se 3 (by rfl) ⟨346007, by rfl⟩ : syracuseStep 1845373 = 692015) (by norm_num)
theorem B4155533 : Blo 1640019 4155533 := bbase (se 3 (by rfl) ⟨779162, by rfl⟩ : syracuseStep 4155533 = 1558325) (by norm_num)
theorem B1845409 : Blo 1640019 1845409 := bbase (se 2 (by rfl) ⟨692028, by rfl⟩ : syracuseStep 1845409 = 1384057) (by norm_num)
theorem B4991141 : Blo 1640019 4991141 := bbase (se 4 (by rfl) ⟨467919, by rfl⟩ : syracuseStep 4991141 = 935839) (by norm_num)
theorem B2336941 : Blo 1640019 2336941 := bbase (se 3 (by rfl) ⟨438176, by rfl⟩ : syracuseStep 2336941 = 876353) (by norm_num)
theorem B5613749 : Blo 1640019 5613749 := bbase (se 5 (by rfl) ⟨263144, by rfl⟩ : syracuseStep 5613749 = 526289) (by norm_num)
theorem B5540021 : Blo 1640019 5540021 := bbase (se 5 (by rfl) ⟨259688, by rfl⟩ : syracuseStep 5540021 = 519377) (by norm_num)
theorem B1845445 : Blo 1640019 1845445 := bbase (se 4 (by rfl) ⟨173010, by rfl⟩ : syracuseStep 1845445 = 346021) (by norm_num)
theorem B3795149 : Blo 1640019 3795149 := bbase (se 3 (by rfl) ⟨711590, by rfl⟩ : syracuseStep 3795149 = 1423181) (by norm_num)
theorem B6228197 : Blo 1640019 6228197 := bbase (se 4 (by rfl) ⟨583893, by rfl⟩ : syracuseStep 6228197 = 1167787) (by norm_num)
theorem B1845481 : Blo 1640019 1845481 := bbase (se 2 (by rfl) ⟨692055, by rfl⟩ : syracuseStep 1845481 = 1384111) (by norm_num)
theorem B3115253 : Blo 1640019 3115253 := bbase (se 5 (by rfl) ⟨146027, by rfl⟩ : syracuseStep 3115253 = 292055) (by norm_num)
theorem B1845517 : Blo 1640019 1845517 := bbase (se 3 (by rfl) ⟨346034, by rfl⟩ : syracuseStep 1845517 = 692069) (by norm_num)
theorem B1845553 : Blo 1640019 1845553 := bbase (se 2 (by rfl) ⟨692082, by rfl⟩ : syracuseStep 1845553 = 1384165) (by norm_num)
theorem B5916997 : Blo 1640019 5916997 := bbase (se 4 (by rfl) ⟨554718, by rfl⟩ : syracuseStep 5916997 = 1109437) (by norm_num)
theorem B4155725 : Blo 1640019 4155725 := bbase (se 3 (by rfl) ⟨779198, by rfl⟩ : syracuseStep 4155725 = 1558397) (by norm_num)
theorem B1845589 : Blo 1640019 1845589 := bbase (se 10 (by rfl) ⟨2703, by rfl⟩ : syracuseStep 1845589 = 5407) (by norm_num)
theorem B1845625 : Blo 1640019 1845625 := bbase (se 2 (by rfl) ⟨692109, by rfl⟩ : syracuseStep 1845625 = 1384219) (by norm_num)
theorem B2460029 : Blo 1640019 2460029 := bbase (se 3 (by rfl) ⟨461255, by rfl⟩ : syracuseStep 2460029 = 922511) (by norm_num)
theorem B4671877 : Blo 1640019 4671877 := bbase (se 4 (by rfl) ⟨437988, by rfl⟩ : syracuseStep 4671877 = 875977) (by norm_num)
theorem B3115397 : Blo 1640019 3115397 := bbase (se 4 (by rfl) ⟨292068, by rfl⟩ : syracuseStep 3115397 = 584137) (by norm_num)
theorem B2460053 : Blo 1640019 2460053 := bbase (se 6 (by rfl) ⟨57657, by rfl⟩ : syracuseStep 2460053 = 115315) (by norm_num)
theorem B8309141 : Blo 1640019 8309141 := bbase (se 6 (by rfl) ⟨194745, by rfl⟩ : syracuseStep 8309141 = 389491) (by norm_num)
theorem B1845661 : Blo 1640019 1845661 := bbase (se 3 (by rfl) ⟨346061, by rfl⟩ : syracuseStep 1845661 = 692123) (by norm_num)
theorem B2460077 : Blo 1640019 2460077 := bbase (se 3 (by rfl) ⟨461264, by rfl⟩ : syracuseStep 2460077 = 922529) (by norm_num)
theorem B15165877 : Blo 1640019 15165877 := bbase (se 5 (by rfl) ⟨710900, by rfl⟩ : syracuseStep 15165877 = 1421801) (by norm_num)
theorem B1845697 : Blo 1640019 1845697 := bbase (se 2 (by rfl) ⟨692136, by rfl⟩ : syracuseStep 1845697 = 1384273) (by norm_num)
theorem B2460101 : Blo 1640019 2460101 := bbase (se 4 (by rfl) ⟨230634, by rfl⟩ : syracuseStep 2460101 = 461269) (by norm_num)
theorem B2460125 : Blo 1640019 2460125 := bbase (se 3 (by rfl) ⟨461273, by rfl⟩ : syracuseStep 2460125 = 922547) (by norm_num)
theorem B1845733 : Blo 1640019 1845733 := bbase (se 4 (by rfl) ⟨173037, by rfl⟩ : syracuseStep 1845733 = 346075) (by norm_num)
theorem B5917157 : Blo 1640019 5917157 := bbase (se 4 (by rfl) ⟨554733, by rfl⟩ : syracuseStep 5917157 = 1109467) (by norm_num)
theorem B2460149 : Blo 1640019 2460149 := bbase (se 5 (by rfl) ⟨115319, by rfl⟩ : syracuseStep 2460149 = 230639) (by norm_num)
theorem B2337277 : Blo 1640019 2337277 := bbase (se 3 (by rfl) ⟨438239, by rfl⟩ : syracuseStep 2337277 = 876479) (by norm_num)
theorem B6228485 : Blo 1640019 6228485 := bbase (se 4 (by rfl) ⟨583920, by rfl⟩ : syracuseStep 6228485 = 1167841) (by norm_num)
theorem B5327365 : Blo 1640019 5327365 := bbase (se 4 (by rfl) ⟨499440, by rfl⟩ : syracuseStep 5327365 = 998881) (by norm_num)
theorem B1845769 : Blo 1640019 1845769 := bbase (se 2 (by rfl) ⟨692163, by rfl⟩ : syracuseStep 1845769 = 1384327) (by norm_num)
theorem B2460173 : Blo 1640019 2460173 := bbase (se 3 (by rfl) ⟨461282, by rfl⟩ : syracuseStep 2460173 = 922565) (by norm_num)
theorem B2460197 : Blo 1640019 2460197 := bbase (se 4 (by rfl) ⟨230643, by rfl⟩ : syracuseStep 2460197 = 461287) (by norm_num)
theorem B6834725 : Blo 1640019 6834725 := bbase (se 4 (by rfl) ⟨640755, by rfl⟩ : syracuseStep 6834725 = 1281511) (by norm_num)
theorem B1845805 : Blo 1640019 1845805 := bbase (se 3 (by rfl) ⟨346088, by rfl⟩ : syracuseStep 1845805 = 692177) (by norm_num)
theorem B2460221 : Blo 1640019 2460221 := bbase (se 3 (by rfl) ⟨461291, by rfl⟩ : syracuseStep 2460221 = 922583) (by norm_num)
theorem B1845841 : Blo 1640019 1845841 := bbase (se 2 (by rfl) ⟨692190, by rfl⟩ : syracuseStep 1845841 = 1384381) (by norm_num)
theorem B2460245 : Blo 1640019 2460245 := bbase (se 8 (by rfl) ⟨14415, by rfl⟩ : syracuseStep 2460245 = 28831) (by norm_num)
theorem B5540453 : Blo 1640019 5540453 := bbase (se 4 (by rfl) ⟨519417, by rfl⟩ : syracuseStep 5540453 = 1038835) (by norm_num)
theorem B2460269 : Blo 1640019 2460269 := bbase (se 3 (by rfl) ⟨461300, by rfl⟩ : syracuseStep 2460269 = 922601) (by norm_num)
theorem B3943021 : Blo 1640019 3943021 := bbase (se 3 (by rfl) ⟨739316, by rfl⟩ : syracuseStep 3943021 = 1478633) (by norm_num)
theorem B1845877 : Blo 1640019 1845877 := bbase (se 5 (by rfl) ⟨86525, by rfl⟩ : syracuseStep 1845877 = 173051) (by norm_num)
theorem B2460293 : Blo 1640019 2460293 := bbase (se 4 (by rfl) ⟨230652, by rfl⟩ : syracuseStep 2460293 = 461305) (by norm_num)
theorem B1845913 : Blo 1640019 1845913 := bbase (se 2 (by rfl) ⟨692217, by rfl⟩ : syracuseStep 1845913 = 1384435) (by norm_num)
theorem B2460317 : Blo 1640019 2460317 := bbase (se 3 (by rfl) ⟨461309, by rfl⟩ : syracuseStep 2460317 = 922619) (by norm_num)
theorem B3115685 : Blo 1640019 3115685 := bbase (se 4 (by rfl) ⟨292095, by rfl⟩ : syracuseStep 3115685 = 584191) (by norm_num)
theorem B4156069 : Blo 1640019 4156069 := bbase (se 4 (by rfl) ⟨389631, by rfl⟩ : syracuseStep 4156069 = 779263) (by norm_num)
theorem B2460341 : Blo 1640019 2460341 := bbase (se 5 (by rfl) ⟨115328, by rfl⟩ : syracuseStep 2460341 = 230657) (by norm_num)
theorem B1845949 : Blo 1640019 1845949 := bbase (se 3 (by rfl) ⟨346115, by rfl⟩ : syracuseStep 1845949 = 692231) (by norm_num)
theorem B2460365 : Blo 1640019 2460365 := bbase (se 3 (by rfl) ⟨461318, by rfl⟩ : syracuseStep 2460365 = 922637) (by norm_num)
theorem B2337493 : Blo 1640019 2337493 := bbase (se 7 (by rfl) ⟨27392, by rfl⟩ : syracuseStep 2337493 = 54785) (by norm_num)
theorem B1845985 : Blo 1640019 1845985 := bbase (se 2 (by rfl) ⟨692244, by rfl⟩ : syracuseStep 1845985 = 1384489) (by norm_num)
theorem B2460389 : Blo 1640019 2460389 := bbase (se 4 (by rfl) ⟨230661, by rfl⟩ : syracuseStep 2460389 = 461323) (by norm_num)
theorem B2460413 : Blo 1640019 2460413 := bbase (se 3 (by rfl) ⟨461327, by rfl⟩ : syracuseStep 2460413 = 922655) (by norm_num)
theorem B1846021 : Blo 1640019 1846021 := bbase (se 4 (by rfl) ⟨173064, by rfl⟩ : syracuseStep 1846021 = 346129) (by norm_num)
theorem B2460437 : Blo 1640019 2460437 := bbase (se 6 (by rfl) ⟨57666, by rfl⟩ : syracuseStep 2460437 = 115333) (by norm_num)
theorem B4156181 : Blo 1640019 4156181 := bbase (se 6 (by rfl) ⟨97410, by rfl⟩ : syracuseStep 4156181 = 194821) (by norm_num)
theorem B7482149 : Blo 1640019 7482149 := bbase (se 4 (by rfl) ⟨701451, by rfl⟩ : syracuseStep 7482149 = 1402903) (by norm_num)
theorem B1846057 : Blo 1640019 1846057 := bbase (se 2 (by rfl) ⟨692271, by rfl⟩ : syracuseStep 1846057 = 1384543) (by norm_num)
theorem B2460461 : Blo 1640019 2460461 := bbase (se 3 (by rfl) ⟨461336, by rfl⟩ : syracuseStep 2460461 = 922673) (by norm_num)
theorem B8874805 : Blo 1640019 8874805 := bbase (se 5 (by rfl) ⟨416006, by rfl⟩ : syracuseStep 8874805 = 832013) (by norm_num)
theorem B3115837 : Blo 1640019 3115837 := bbase (se 3 (by rfl) ⟨584219, by rfl⟩ : syracuseStep 3115837 = 1168439) (by norm_num)
theorem B2460485 : Blo 1640019 2460485 := bbase (se 4 (by rfl) ⟨230670, by rfl⟩ : syracuseStep 2460485 = 461341) (by norm_num)
theorem B1846093 : Blo 1640019 1846093 := bbase (se 3 (by rfl) ⟨346142, by rfl⟩ : syracuseStep 1846093 = 692285) (by norm_num)
theorem B11832149 : Blo 1640019 11832149 := bbase (se 9 (by rfl) ⟨34664, by rfl⟩ : syracuseStep 11832149 = 69329) (by norm_num)
theorem B2460509 : Blo 1640019 2460509 := bbase (se 3 (by rfl) ⟨461345, by rfl⟩ : syracuseStep 2460509 = 922691) (by norm_num)
theorem B1846129 : Blo 1640019 1846129 := bbase (se 2 (by rfl) ⟨692298, by rfl⟩ : syracuseStep 1846129 = 1384597) (by norm_num)
theorem B2460533 : Blo 1640019 2460533 := bbase (se 5 (by rfl) ⟨115337, by rfl⟩ : syracuseStep 2460533 = 230675) (by norm_num)
theorem B2460557 : Blo 1640019 2460557 := bbase (se 3 (by rfl) ⟨461354, by rfl⟩ : syracuseStep 2460557 = 922709) (by norm_num)
theorem B1846165 : Blo 1640019 1846165 := bbase (se 6 (by rfl) ⟨43269, by rfl⟩ : syracuseStep 1846165 = 86539) (by norm_num)
theorem B2460581 : Blo 1640019 2460581 := bbase (se 4 (by rfl) ⟨230679, by rfl⟩ : syracuseStep 2460581 = 461359) (by norm_num)
theorem B1846201 : Blo 1640019 1846201 := bbase (se 2 (by rfl) ⟨692325, by rfl⟩ : syracuseStep 1846201 = 1384651) (by norm_num)
theorem B2460605 : Blo 1640019 2460605 := bbase (se 3 (by rfl) ⟨461363, by rfl⟩ : syracuseStep 2460605 = 922727) (by norm_num)
theorem B2460629 : Blo 1640019 2460629 := bbase (se 7 (by rfl) ⟨28835, by rfl⟩ : syracuseStep 2460629 = 57671) (by norm_num)
theorem B1846237 : Blo 1640019 1846237 := bbase (se 3 (by rfl) ⟨346169, by rfl⟩ : syracuseStep 1846237 = 692339) (by norm_num)
theorem B2460653 : Blo 1640019 2460653 := bbase (se 3 (by rfl) ⟨461372, by rfl⟩ : syracuseStep 2460653 = 922745) (by norm_num)
theorem B1846273 : Blo 1640019 1846273 := bbase (se 2 (by rfl) ⟨692352, by rfl⟩ : syracuseStep 1846273 = 1384705) (by norm_num)
theorem B2460677 : Blo 1640019 2460677 := bbase (se 4 (by rfl) ⟨230688, by rfl⟩ : syracuseStep 2460677 = 461377) (by norm_num)
theorem B5540885 : Blo 1640019 5540885 := bbase (se 6 (by rfl) ⟨129864, by rfl⟩ : syracuseStep 5540885 = 259729) (by norm_num)
theorem B2460701 : Blo 1640019 2460701 := bbase (se 3 (by rfl) ⟨461381, by rfl⟩ : syracuseStep 2460701 = 922763) (by norm_num)
theorem B7007269 : Blo 1640019 7007269 := bbase (se 4 (by rfl) ⟨656931, by rfl⟩ : syracuseStep 7007269 = 1313863) (by norm_num)
theorem B1846309 : Blo 1640019 1846309 := bbase (se 4 (by rfl) ⟨173091, by rfl⟩ : syracuseStep 1846309 = 346183) (by norm_num)
theorem B2075701 : Blo 1640019 2075701 := bbase (se 5 (by rfl) ⟨97298, by rfl⟩ : syracuseStep 2075701 = 194597) (by norm_num)
theorem B7007285 : Blo 1640019 7007285 := bbase (se 5 (by rfl) ⟨328466, by rfl⟩ : syracuseStep 7007285 = 656933) (by norm_num)
theorem B2460725 : Blo 1640019 2460725 := bbase (se 5 (by rfl) ⟨115346, by rfl⟩ : syracuseStep 2460725 = 230693) (by norm_num)
theorem B1846345 : Blo 1640019 1846345 := bbase (se 2 (by rfl) ⟨692379, by rfl⟩ : syracuseStep 1846345 = 1384759) (by norm_num)
theorem B2460749 : Blo 1640019 2460749 := bbase (se 3 (by rfl) ⟨461390, by rfl⟩ : syracuseStep 2460749 = 922781) (by norm_num)
theorem B2337869 : Blo 1640019 2337869 := bbase (se 3 (by rfl) ⟨438350, by rfl⟩ : syracuseStep 2337869 = 876701) (by norm_num)
theorem B2460773 : Blo 1640019 2460773 := bbase (se 4 (by rfl) ⟨230697, by rfl⟩ : syracuseStep 2460773 = 461395) (by norm_num)
theorem B1846381 : Blo 1640019 1846381 := bbase (se 3 (by rfl) ⟨346196, by rfl⟩ : syracuseStep 1846381 = 692393) (by norm_num)
theorem B3116141 : Blo 1640019 3116141 := bbase (se 3 (by rfl) ⟨584276, by rfl⟩ : syracuseStep 3116141 = 1168553) (by norm_num)
theorem B3943541 : Blo 1640019 3943541 := bbase (se 5 (by rfl) ⟨184853, by rfl⟩ : syracuseStep 3943541 = 369707) (by norm_num)
theorem B2460797 : Blo 1640019 2460797 := bbase (se 3 (by rfl) ⟨461399, by rfl⟩ : syracuseStep 2460797 = 922799) (by norm_num)
theorem B1846417 : Blo 1640019 1846417 := bbase (se 2 (by rfl) ⟨692406, by rfl⟩ : syracuseStep 1846417 = 1384813) (by norm_num)
theorem B2075797 : Blo 1640019 2075797 := bbase (se 6 (by rfl) ⟨48651, by rfl⟩ : syracuseStep 2075797 = 97303) (by norm_num)
theorem B2460821 : Blo 1640019 2460821 := bbase (se 6 (by rfl) ⟨57675, by rfl⟩ : syracuseStep 2460821 = 115351) (by norm_num)
theorem B2460845 : Blo 1640019 2460845 := bbase (se 3 (by rfl) ⟨461408, by rfl⟩ : syracuseStep 2460845 = 922817) (by norm_num)
theorem B1846453 : Blo 1640019 1846453 := bbase (se 5 (by rfl) ⟨86552, by rfl⟩ : syracuseStep 1846453 = 173105) (by norm_num)
theorem B2460869 : Blo 1640019 2460869 := bbase (se 4 (by rfl) ⟨230706, by rfl⟩ : syracuseStep 2460869 = 461413) (by norm_num)
theorem B3943637 : Blo 1640019 3943637 := bbase (se 7 (by rfl) ⟨46214, by rfl⟩ : syracuseStep 3943637 = 92429) (by norm_num)
theorem B1846489 : Blo 1640019 1846489 := bbase (se 2 (by rfl) ⟨692433, by rfl⟩ : syracuseStep 1846489 = 1384867) (by norm_num)
theorem B2460893 : Blo 1640019 2460893 := bbase (se 3 (by rfl) ⟨461417, by rfl⟩ : syracuseStep 2460893 = 922835) (by norm_num)
theorem B2460917 : Blo 1640019 2460917 := bbase (se 5 (by rfl) ⟨115355, by rfl⟩ : syracuseStep 2460917 = 230711) (by norm_num)
theorem B1846525 : Blo 1640019 1846525 := bbase (se 3 (by rfl) ⟨346223, by rfl⟩ : syracuseStep 1846525 = 692447) (by norm_num)
theorem B2460941 : Blo 1640019 2460941 := bbase (se 3 (by rfl) ⟨461426, by rfl⟩ : syracuseStep 2460941 = 922853) (by norm_num)
theorem B14970133 : Blo 1640019 14970133 := bbase (se 6 (by rfl) ⟨350862, by rfl⟩ : syracuseStep 14970133 = 701725) (by norm_num)
theorem B1846561 : Blo 1640019 1846561 := bbase (se 2 (by rfl) ⟨692460, by rfl⟩ : syracuseStep 1846561 = 1384921) (by norm_num)
theorem B2460965 : Blo 1640019 2460965 := bbase (se 4 (by rfl) ⟨230715, by rfl⟩ : syracuseStep 2460965 = 461431) (by norm_num)
theorem B2460989 : Blo 1640019 2460989 := bbase (se 3 (by rfl) ⟨461435, by rfl⟩ : syracuseStep 2460989 = 922871) (by norm_num)
theorem B2075969 : Blo 1640019 2075969 := bbase (se 2 (by rfl) ⟨778488, by rfl⟩ : syracuseStep 2075969 = 1556977) (by norm_num)
theorem B1846597 : Blo 1640019 1846597 := bbase (se 4 (by rfl) ⟨173118, by rfl⟩ : syracuseStep 1846597 = 346237) (by norm_num)
theorem B2461013 : Blo 1640019 2461013 := bbase (se 11 (by rfl) ⟨1802, by rfl⟩ : syracuseStep 2461013 = 3605) (by norm_num)
theorem B1846633 : Blo 1640019 1846633 := bbase (se 2 (by rfl) ⟨692487, by rfl⟩ : syracuseStep 1846633 = 1384975) (by norm_num)
theorem B2461037 : Blo 1640019 2461037 := bbase (se 3 (by rfl) ⟨461444, by rfl⟩ : syracuseStep 2461037 = 922889) (by norm_num)
theorem B2076025 : Blo 1640019 2076025 := bbase (se 2 (by rfl) ⟨778509, by rfl⟩ : syracuseStep 2076025 = 1557019) (by norm_num)
theorem B2461061 : Blo 1640019 2461061 := bbase (se 4 (by rfl) ⟨230724, by rfl⟩ : syracuseStep 2461061 = 461449) (by norm_num)
theorem B1846669 : Blo 1640019 1846669 := bbase (se 3 (by rfl) ⟨346250, by rfl⟩ : syracuseStep 1846669 = 692501) (by norm_num)
theorem B2461085 : Blo 1640019 2461085 := bbase (se 3 (by rfl) ⟨461453, by rfl⟩ : syracuseStep 2461085 = 922907) (by norm_num)
theorem B1846705 : Blo 1640019 1846705 := bbase (se 2 (by rfl) ⟨692514, by rfl⟩ : syracuseStep 1846705 = 1385029) (by norm_num)
theorem B2461109 : Blo 1640019 2461109 := bbase (se 5 (by rfl) ⟨115364, by rfl⟩ : syracuseStep 2461109 = 230729) (by norm_num)
theorem B5541317 : Blo 1640019 5541317 := bbase (se 4 (by rfl) ⟨519498, by rfl⟩ : syracuseStep 5541317 = 1038997) (by norm_num)
theorem B2461133 : Blo 1640019 2461133 := bbase (se 3 (by rfl) ⟨461462, by rfl⟩ : syracuseStep 2461133 = 922925) (by norm_num)
theorem B4672981 : Blo 1640019 4672981 := bbase (se 7 (by rfl) ⟨54761, by rfl⟩ : syracuseStep 4672981 = 109523) (by norm_num)
theorem B1846741 : Blo 1640019 1846741 := bbase (se 7 (by rfl) ⟨21641, by rfl⟩ : syracuseStep 1846741 = 43283) (by norm_num)
theorem B2076121 : Blo 1640019 2076121 := bbase (se 2 (by rfl) ⟨778545, by rfl⟩ : syracuseStep 2076121 = 1557091) (by norm_num)
theorem B2461157 : Blo 1640019 2461157 := bbase (se 4 (by rfl) ⟨230733, by rfl⟩ : syracuseStep 2461157 = 461467) (by norm_num)
theorem B1846777 : Blo 1640019 1846777 := bbase (se 2 (by rfl) ⟨692541, by rfl⟩ : syracuseStep 1846777 = 1385083) (by norm_num)
theorem B2461181 : Blo 1640019 2461181 := bbase (se 3 (by rfl) ⟨461471, by rfl⟩ : syracuseStep 2461181 = 922943) (by norm_num)
theorem B2461205 : Blo 1640019 2461205 := bbase (se 6 (by rfl) ⟨57684, by rfl⟩ : syracuseStep 2461205 = 115369) (by norm_num)
theorem B1846813 : Blo 1640019 1846813 := bbase (se 3 (by rfl) ⟨346277, by rfl⟩ : syracuseStep 1846813 = 692555) (by norm_num)
theorem B2461229 : Blo 1640019 2461229 := bbase (se 3 (by rfl) ⟨461480, by rfl⟩ : syracuseStep 2461229 = 922961) (by norm_num)
theorem B15773237 : Blo 1640019 15773237 := bbase (se 5 (by rfl) ⟨739370, by rfl⟩ : syracuseStep 15773237 = 1478741) (by norm_num)
theorem B2494013 : Blo 1640019 2494013 := bbase (se 3 (by rfl) ⟨467627, by rfl⟩ : syracuseStep 2494013 = 935255) (by norm_num)
theorem B1846849 : Blo 1640019 1846849 := bbase (se 2 (by rfl) ⟨692568, by rfl⟩ : syracuseStep 1846849 = 1385137) (by norm_num)
theorem B3690053 : Blo 1640019 3690053 := bbase (se 4 (by rfl) ⟨345942, by rfl⟩ : syracuseStep 3690053 = 691885) (by norm_num)
theorem B2461253 : Blo 1640019 2461253 := bbase (se 4 (by rfl) ⟨230742, by rfl⟩ : syracuseStep 2461253 = 461485) (by norm_num)
theorem B2461277 : Blo 1640019 2461277 := bbase (se 3 (by rfl) ⟨461489, by rfl⟩ : syracuseStep 2461277 = 922979) (by norm_num)
theorem B1846885 : Blo 1640019 1846885 := bbase (se 4 (by rfl) ⟨173145, by rfl⟩ : syracuseStep 1846885 = 346291) (by norm_num)
theorem B2461301 : Blo 1640019 2461301 := bbase (se 5 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 2461301 = 230747) (by norm_num)
theorem B2076293 : Blo 1640019 2076293 := bbase (se 4 (by rfl) ⟨194652, by rfl⟩ : syracuseStep 2076293 = 389305) (by norm_num)
theorem B1846921 : Blo 1640019 1846921 := bbase (se 2 (by rfl) ⟨692595, by rfl⟩ : syracuseStep 1846921 = 1385191) (by norm_num)
theorem B3690125 : Blo 1640019 3690125 := bbase (se 3 (by rfl) ⟨691898, by rfl⟩ : syracuseStep 3690125 = 1383797) (by norm_num)
theorem B2461325 : Blo 1640019 2461325 := bbase (se 3 (by rfl) ⟨461498, by rfl⟩ : syracuseStep 2461325 = 922997) (by norm_num)
theorem B6229669 : Blo 1640019 6229669 := bbase (se 4 (by rfl) ⟨584031, by rfl⟩ : syracuseStep 6229669 = 1168063) (by norm_num)
theorem B2461349 : Blo 1640019 2461349 := bbase (se 4 (by rfl) ⟨230751, by rfl⟩ : syracuseStep 2461349 = 461503) (by norm_num)
theorem B8310437 : Blo 1640019 8310437 := bbase (se 4 (by rfl) ⟨779103, by rfl⟩ : syracuseStep 8310437 = 1558207) (by norm_num)
theorem B1846957 : Blo 1640019 1846957 := bbase (se 3 (by rfl) ⟨346304, by rfl⟩ : syracuseStep 1846957 = 692609) (by norm_num)
theorem B2076349 : Blo 1640019 2076349 := bbase (se 3 (by rfl) ⟨389315, by rfl⟩ : syracuseStep 2076349 = 778631) (by norm_num)
theorem B2461373 : Blo 1640019 2461373 := bbase (se 3 (by rfl) ⟨461507, by rfl⟩ : syracuseStep 2461373 = 923015) (by norm_num)
theorem B1846993 : Blo 1640019 1846993 := bbase (se 2 (by rfl) ⟨692622, by rfl⟩ : syracuseStep 1846993 = 1385245) (by norm_num)
theorem B3690197 : Blo 1640019 3690197 := bbase (se 7 (by rfl) ⟨43244, by rfl⟩ : syracuseStep 3690197 = 86489) (by norm_num)
theorem B2461397 : Blo 1640019 2461397 := bbase (se 7 (by rfl) ⟨28844, by rfl⟩ : syracuseStep 2461397 = 57689) (by norm_num)
theorem B2461421 : Blo 1640019 2461421 := bbase (se 3 (by rfl) ⟨461516, by rfl⟩ : syracuseStep 2461421 = 923033) (by norm_num)
theorem B5254901 : Blo 1640019 5254901 := bbase (se 5 (by rfl) ⟨246323, by rfl⟩ : syracuseStep 5254901 = 492647) (by norm_num)
theorem B1847029 : Blo 1640019 1847029 := bbase (se 5 (by rfl) ⟨86579, by rfl⟩ : syracuseStep 1847029 = 173159) (by norm_num)
theorem B2461445 : Blo 1640019 2461445 := bbase (se 4 (by rfl) ⟨230760, by rfl⟩ : syracuseStep 2461445 = 461521) (by norm_num)
theorem B1847065 : Blo 1640019 1847065 := bbase (se 2 (by rfl) ⟨692649, by rfl⟩ : syracuseStep 1847065 = 1385299) (by norm_num)
theorem B3690269 : Blo 1640019 3690269 := bbase (se 3 (by rfl) ⟨691925, by rfl⟩ : syracuseStep 3690269 = 1383851) (by norm_num)
theorem B2076445 : Blo 1640019 2076445 := bbase (se 3 (by rfl) ⟨389333, by rfl⟩ : syracuseStep 2076445 = 778667) (by norm_num)
theorem B2461469 : Blo 1640019 2461469 := bbase (se 3 (by rfl) ⟨461525, by rfl⟩ : syracuseStep 2461469 = 923051) (by norm_num)
theorem B9342773 : Blo 1640019 9342773 := bbase (se 5 (by rfl) ⟨437942, by rfl⟩ : syracuseStep 9342773 = 875885) (by norm_num)
theorem B2461493 : Blo 1640019 2461493 := bbase (se 5 (by rfl) ⟨115382, by rfl⟩ : syracuseStep 2461493 = 230765) (by norm_num)
theorem B1847101 : Blo 1640019 1847101 := bbase (se 3 (by rfl) ⟨346331, by rfl⟩ : syracuseStep 1847101 = 692663) (by norm_num)
theorem B2461517 : Blo 1640019 2461517 := bbase (se 3 (by rfl) ⟨461534, by rfl⟩ : syracuseStep 2461517 = 923069) (by norm_num)
theorem B3116893 : Blo 1640019 3116893 := bbase (se 3 (by rfl) ⟨584417, by rfl⟩ : syracuseStep 3116893 = 1168835) (by norm_num)
theorem B1847137 : Blo 1640019 1847137 := bbase (se 2 (by rfl) ⟨692676, by rfl⟩ : syracuseStep 1847137 = 1385353) (by norm_num)
theorem B3690341 : Blo 1640019 3690341 := bbase (se 4 (by rfl) ⟨345969, by rfl⟩ : syracuseStep 3690341 = 691939) (by norm_num)
theorem B3370853 : Blo 1640019 3370853 := bbase (se 4 (by rfl) ⟨316017, by rfl⟩ : syracuseStep 3370853 = 632035) (by norm_num)
theorem B2461541 : Blo 1640019 2461541 := bbase (se 4 (by rfl) ⟨230769, by rfl⟩ : syracuseStep 2461541 = 461539) (by norm_num)
theorem B5541749 : Blo 1640019 5541749 := bbase (se 5 (by rfl) ⟨259769, by rfl⟩ : syracuseStep 5541749 = 519539) (by norm_num)
theorem B2461565 : Blo 1640019 2461565 := bbase (se 3 (by rfl) ⟨461543, by rfl⟩ : syracuseStep 2461565 = 923087) (by norm_num)
theorem B1847173 : Blo 1640019 1847173 := bbase (se 4 (by rfl) ⟨173172, by rfl⟩ : syracuseStep 1847173 = 346345) (by norm_num)
theorem B2461589 : Blo 1640019 2461589 := bbase (se 6 (by rfl) ⟨57693, by rfl⟩ : syracuseStep 2461589 = 115387) (by norm_num)
theorem B1847209 : Blo 1640019 1847209 := bbase (se 2 (by rfl) ⟨692703, by rfl⟩ : syracuseStep 1847209 = 1385407) (by norm_num)
theorem B3690413 : Blo 1640019 3690413 := bbase (se 3 (by rfl) ⟨691952, by rfl⟩ : syracuseStep 3690413 = 1383905) (by norm_num)
theorem B2461613 : Blo 1640019 2461613 := bbase (se 3 (by rfl) ⟨461552, by rfl⟩ : syracuseStep 2461613 = 923105) (by norm_num)
theorem B6655925 : Blo 1640019 6655925 := bbase (se 5 (by rfl) ⟨311996, by rfl⟩ : syracuseStep 6655925 = 623993) (by norm_num)
theorem B2461637 : Blo 1640019 2461637 := bbase (se 4 (by rfl) ⟨230778, by rfl⟩ : syracuseStep 2461637 = 461557) (by norm_num)
theorem B4992965 : Blo 1640019 4992965 := bbase (se 4 (by rfl) ⟨468090, by rfl⟩ : syracuseStep 4992965 = 936181) (by norm_num)
theorem B2076617 : Blo 1640019 2076617 := bbase (se 2 (by rfl) ⟨778731, by rfl⟩ : syracuseStep 2076617 = 1557463) (by norm_num)
theorem B1847245 : Blo 1640019 1847245 := bbase (se 3 (by rfl) ⟨346358, by rfl⟩ : syracuseStep 1847245 = 692717) (by norm_num)
theorem B6229973 : Blo 1640019 6229973 := bbase (se 7 (by rfl) ⟨73007, by rfl⟩ : syracuseStep 6229973 = 146015) (by norm_num)
theorem B35975125 : Blo 1640019 35975125 := bbase (se 7 (by rfl) ⟨421583, by rfl⟩ : syracuseStep 35975125 = 843167) (by norm_num)
theorem B1871833 : Blo 1640019 1871833 := bbase (se 2 (by rfl) ⟨701937, by rfl⟩ : syracuseStep 1871833 = 1403875) (by norm_num)
theorem B2461661 : Blo 1640019 2461661 := bbase (se 3 (by rfl) ⟨461561, by rfl⟩ : syracuseStep 2461661 = 923123) (by norm_num)
theorem B7884773 : Blo 1640019 7884773 := bbase (se 4 (by rfl) ⟨739197, by rfl⟩ : syracuseStep 7884773 = 1478395) (by norm_num)
theorem B3117037 : Blo 1640019 3117037 := bbase (se 3 (by rfl) ⟨584444, by rfl⟩ : syracuseStep 3117037 = 1168889) (by norm_num)
theorem B3690485 : Blo 1640019 3690485 := bbase (se 5 (by rfl) ⟨172991, by rfl⟩ : syracuseStep 3690485 = 345983) (by norm_num)
theorem B2461685 : Blo 1640019 2461685 := bbase (se 5 (by rfl) ⟨115391, by rfl⟩ : syracuseStep 2461685 = 230783) (by norm_num)
theorem B2076673 : Blo 1640019 2076673 := bbase (se 2 (by rfl) ⟨778752, by rfl⟩ : syracuseStep 2076673 = 1557505) (by norm_num)
theorem B2461709 : Blo 1640019 2461709 := bbase (se 3 (by rfl) ⟨461570, by rfl⟩ : syracuseStep 2461709 = 923141) (by norm_num)
theorem B2461733 : Blo 1640019 2461733 := bbase (se 4 (by rfl) ⟨230787, by rfl⟩ : syracuseStep 2461733 = 461575) (by norm_num)
theorem B3690557 : Blo 1640019 3690557 := bbase (se 3 (by rfl) ⟨691979, by rfl⟩ : syracuseStep 3690557 = 1383959) (by norm_num)
theorem B2461757 : Blo 1640019 2461757 := bbase (se 3 (by rfl) ⟨461579, by rfl⟩ : syracuseStep 2461757 = 923159) (by norm_num)
theorem B8302661 : Blo 1640019 8302661 := bbase (se 4 (by rfl) ⟨778374, by rfl⟩ : syracuseStep 8302661 = 1556749) (by norm_num)
theorem B1970257 : Blo 1640019 1970257 := bbase (se 2 (by rfl) ⟨738846, by rfl⟩ : syracuseStep 1970257 = 1477693) (by norm_num)
theorem B2461781 : Blo 1640019 2461781 := bbase (se 8 (by rfl) ⟨14424, by rfl⟩ : syracuseStep 2461781 = 28849) (by norm_num)
theorem B2076769 : Blo 1640019 2076769 := bbase (se 2 (by rfl) ⟨778788, by rfl⟩ : syracuseStep 2076769 = 1557577) (by norm_num)
theorem B2461805 : Blo 1640019 2461805 := bbase (se 3 (by rfl) ⟨461588, by rfl⟩ : syracuseStep 2461805 = 923177) (by norm_num)
theorem B3690629 : Blo 1640019 3690629 := bbase (se 4 (by rfl) ⟨345996, by rfl⟩ : syracuseStep 3690629 = 691993) (by norm_num)
theorem B2461829 : Blo 1640019 2461829 := bbase (se 4 (by rfl) ⟨230796, by rfl⟩ : syracuseStep 2461829 = 461593) (by norm_num)
theorem B3117197 : Blo 1640019 3117197 := bbase (se 3 (by rfl) ⟨584474, by rfl⟩ : syracuseStep 3117197 = 1168949) (by norm_num)
theorem B2461853 : Blo 1640019 2461853 := bbase (se 3 (by rfl) ⟨461597, by rfl⟩ : syracuseStep 2461853 = 923195) (by norm_num)
theorem B2461877 : Blo 1640019 2461877 := bbase (se 5 (by rfl) ⟨115400, by rfl⟩ : syracuseStep 2461877 = 230801) (by norm_num)
theorem B3690701 : Blo 1640019 3690701 := bbase (se 3 (by rfl) ⟨692006, by rfl⟩ : syracuseStep 3690701 = 1384013) (by norm_num)
theorem B2461901 : Blo 1640019 2461901 := bbase (se 3 (by rfl) ⟨461606, by rfl⟩ : syracuseStep 2461901 = 923213) (by norm_num)
theorem B2461925 : Blo 1640019 2461925 := bbase (se 4 (by rfl) ⟨230805, by rfl⟩ : syracuseStep 2461925 = 461611) (by norm_num)
theorem B2461949 : Blo 1640019 2461949 := bbase (se 3 (by rfl) ⟨461615, by rfl⟩ : syracuseStep 2461949 = 923231) (by norm_num)
theorem B2076941 : Blo 1640019 2076941 := bbase (se 3 (by rfl) ⟨389426, by rfl⟩ : syracuseStep 2076941 = 778853) (by norm_num)
theorem B3690773 : Blo 1640019 3690773 := bbase (se 6 (by rfl) ⟨86502, by rfl⟩ : syracuseStep 3690773 = 173005) (by norm_num)
theorem B2461973 : Blo 1640019 2461973 := bbase (se 6 (by rfl) ⟨57702, by rfl⟩ : syracuseStep 2461973 = 115405) (by norm_num)
theorem B2461997 : Blo 1640019 2461997 := bbase (se 3 (by rfl) ⟨461624, by rfl⟩ : syracuseStep 2461997 = 923249) (by norm_num)
theorem B2076997 : Blo 1640019 2076997 := bbase (se 4 (by rfl) ⟨194718, by rfl⟩ : syracuseStep 2076997 = 389437) (by norm_num)
theorem B2462021 : Blo 1640019 2462021 := bbase (se 4 (by rfl) ⟨230814, by rfl⟩ : syracuseStep 2462021 = 461629) (by norm_num)
theorem B3690845 : Blo 1640019 3690845 := bbase (se 3 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 3690845 = 1384067) (by norm_num)
theorem B2462045 : Blo 1640019 2462045 := bbase (se 3 (by rfl) ⟨461633, by rfl⟩ : syracuseStep 2462045 = 923267) (by norm_num)
theorem B2462069 : Blo 1640019 2462069 := bbase (se 5 (by rfl) ⟨115409, by rfl⟩ : syracuseStep 2462069 = 230819) (by norm_num)
theorem B2462093 : Blo 1640019 2462093 := bbase (se 3 (by rfl) ⟨461642, by rfl⟩ : syracuseStep 2462093 = 923285) (by norm_num)
theorem B3690917 : Blo 1640019 3690917 := bbase (se 4 (by rfl) ⟨346023, by rfl⟩ : syracuseStep 3690917 = 692047) (by norm_num)
theorem B2077093 : Blo 1640019 2077093 := bbase (se 4 (by rfl) ⟨194727, by rfl⟩ : syracuseStep 2077093 = 389455) (by norm_num)
theorem B2462117 : Blo 1640019 2462117 := bbase (se 4 (by rfl) ⟨230823, by rfl⟩ : syracuseStep 2462117 = 461647) (by norm_num)
theorem B2462141 : Blo 1640019 2462141 := bbase (se 3 (by rfl) ⟨461651, by rfl⟩ : syracuseStep 2462141 = 923303) (by norm_num)
theorem B2462165 : Blo 1640019 2462165 := bbase (se 7 (by rfl) ⟨28853, by rfl⟩ : syracuseStep 2462165 = 57707) (by norm_num)
theorem B5911013 : Blo 1640019 5911013 := bbase (se 4 (by rfl) ⟨554157, by rfl⟩ : syracuseStep 5911013 = 1108315) (by norm_num)
theorem B8425957 : Blo 1640019 8425957 := bbase (se 4 (by rfl) ⟨789933, by rfl⟩ : syracuseStep 8425957 = 1579867) (by norm_num)
theorem B3690989 : Blo 1640019 3690989 := bbase (se 3 (by rfl) ⟨692060, by rfl⟩ : syracuseStep 3690989 = 1384121) (by norm_num)
theorem B2462189 : Blo 1640019 2462189 := bbase (se 3 (by rfl) ⟨461660, by rfl⟩ : syracuseStep 2462189 = 923321) (by norm_num)
theorem B2462213 : Blo 1640019 2462213 := bbase (se 4 (by rfl) ⟨230832, by rfl⟩ : syracuseStep 2462213 = 461665) (by norm_num)
theorem B3944981 : Blo 1640019 3944981 := bbase (se 6 (by rfl) ⟨92460, by rfl⟩ : syracuseStep 3944981 = 184921) (by norm_num)
theorem B2462237 : Blo 1640019 2462237 := bbase (se 3 (by rfl) ⟨461669, by rfl⟩ : syracuseStep 2462237 = 923339) (by norm_num)
theorem B3691061 : Blo 1640019 3691061 := bbase (se 5 (by rfl) ⟨173018, by rfl⟩ : syracuseStep 3691061 = 346037) (by norm_num)
theorem B2462261 : Blo 1640019 2462261 := bbase (se 5 (by rfl) ⟨115418, by rfl⟩ : syracuseStep 2462261 = 230837) (by norm_num)
theorem B2462285 : Blo 1640019 2462285 := bbase (se 3 (by rfl) ⟨461678, by rfl⟩ : syracuseStep 2462285 = 923357) (by norm_num)
theorem B2077265 : Blo 1640019 2077265 := bbase (se 2 (by rfl) ⟨778974, by rfl⟩ : syracuseStep 2077265 = 1557949) (by norm_num)
theorem B2462309 : Blo 1640019 2462309 := bbase (se 4 (by rfl) ⟨230841, by rfl⟩ : syracuseStep 2462309 = 461683) (by norm_num)
theorem B3691133 : Blo 1640019 3691133 := bbase (se 3 (by rfl) ⟨692087, by rfl⟩ : syracuseStep 3691133 = 1384175) (by norm_num)
theorem B2462333 : Blo 1640019 2462333 := bbase (se 3 (by rfl) ⟨461687, by rfl⟩ : syracuseStep 2462333 = 923375) (by norm_num)
theorem B2077321 : Blo 1640019 2077321 := bbase (se 2 (by rfl) ⟨778995, by rfl⟩ : syracuseStep 2077321 = 1557991) (by norm_num)
theorem B2462357 : Blo 1640019 2462357 := bbase (se 6 (by rfl) ⟨57711, by rfl⟩ : syracuseStep 2462357 = 115423) (by norm_num)
theorem B2462381 : Blo 1640019 2462381 := bbase (se 3 (by rfl) ⟨461696, by rfl⟩ : syracuseStep 2462381 = 923393) (by norm_num)
theorem B3691205 : Blo 1640019 3691205 := bbase (se 4 (by rfl) ⟨346050, by rfl⟩ : syracuseStep 3691205 = 692101) (by norm_num)
theorem B2462405 : Blo 1640019 2462405 := bbase (se 4 (by rfl) ⟨230850, by rfl⟩ : syracuseStep 2462405 = 461701) (by norm_num)
theorem B2462429 : Blo 1640019 2462429 := bbase (se 3 (by rfl) ⟨461705, by rfl⟩ : syracuseStep 2462429 = 923411) (by norm_num)
theorem B2077417 : Blo 1640019 2077417 := bbase (se 2 (by rfl) ⟨779031, by rfl⟩ : syracuseStep 2077417 = 1558063) (by norm_num)
theorem B2462453 : Blo 1640019 2462453 := bbase (se 5 (by rfl) ⟨115427, by rfl⟩ : syracuseStep 2462453 = 230855) (by norm_num)
theorem B3691277 : Blo 1640019 3691277 := bbase (se 3 (by rfl) ⟨692114, by rfl⟩ : syracuseStep 3691277 = 1384229) (by norm_num)
theorem B2462477 : Blo 1640019 2462477 := bbase (se 3 (by rfl) ⟨461714, by rfl⟩ : syracuseStep 2462477 = 923429) (by norm_num)
theorem B2495261 : Blo 1640019 2495261 := bbase (se 3 (by rfl) ⟨467861, by rfl⟩ : syracuseStep 2495261 = 935723) (by norm_num)
theorem B2462501 : Blo 1640019 2462501 := bbase (se 4 (by rfl) ⟨230859, by rfl⟩ : syracuseStep 2462501 = 461719) (by norm_num)
theorem B2462525 : Blo 1640019 2462525 := bbase (se 3 (by rfl) ⟨461723, by rfl⟩ : syracuseStep 2462525 = 923447) (by norm_num)
theorem B3691349 : Blo 1640019 3691349 := bbase (se 9 (by rfl) ⟨10814, by rfl⟩ : syracuseStep 3691349 = 21629) (by norm_num)
theorem B2462549 : Blo 1640019 2462549 := bbase (se 9 (by rfl) ⟨7214, by rfl⟩ : syracuseStep 2462549 = 14429) (by norm_num)
theorem B2462573 : Blo 1640019 2462573 := bbase (se 3 (by rfl) ⟨461732, by rfl⟩ : syracuseStep 2462573 = 923465) (by norm_num)
theorem B2462597 : Blo 1640019 2462597 := bbase (se 4 (by rfl) ⟨230868, by rfl⟩ : syracuseStep 2462597 = 461737) (by norm_num)
theorem B2077589 : Blo 1640019 2077589 := bbase (se 6 (by rfl) ⟨48693, by rfl⟩ : syracuseStep 2077589 = 97387) (by norm_num)
theorem B3691421 : Blo 1640019 3691421 := bbase (se 3 (by rfl) ⟨692141, by rfl⟩ : syracuseStep 3691421 = 1384283) (by norm_num)
theorem B2462621 : Blo 1640019 2462621 := bbase (se 3 (by rfl) ⟨461741, by rfl⟩ : syracuseStep 2462621 = 923483) (by norm_num)
theorem B4674485 : Blo 1640019 4674485 := bbase (se 5 (by rfl) ⟨219116, by rfl⟩ : syracuseStep 4674485 = 438233) (by norm_num)
theorem B2462645 : Blo 1640019 2462645 := bbase (se 5 (by rfl) ⟨115436, by rfl⟩ : syracuseStep 2462645 = 230873) (by norm_num)
theorem B8311733 : Blo 1640019 8311733 := bbase (se 5 (by rfl) ⟨389612, by rfl⟩ : syracuseStep 8311733 = 779225) (by norm_num)
theorem B1971145 : Blo 1640019 1971145 := bbase (se 2 (by rfl) ⟨739179, by rfl⟩ : syracuseStep 1971145 = 1478359) (by norm_num)
theorem B2077645 : Blo 1640019 2077645 := bbase (se 3 (by rfl) ⟨389558, by rfl⟩ : syracuseStep 2077645 = 779117) (by norm_num)
theorem B2462669 : Blo 1640019 2462669 := bbase (se 3 (by rfl) ⟨461750, by rfl⟩ : syracuseStep 2462669 = 923501) (by norm_num)
theorem B9343957 : Blo 1640019 9343957 := bbase (se 7 (by rfl) ⟨109499, by rfl⟩ : syracuseStep 9343957 = 218999) (by norm_num)
theorem B3691493 : Blo 1640019 3691493 := bbase (se 4 (by rfl) ⟨346077, by rfl⟩ : syracuseStep 3691493 = 692155) (by norm_num)
theorem B2462693 : Blo 1640019 2462693 := bbase (se 4 (by rfl) ⟨230877, by rfl⟩ : syracuseStep 2462693 = 461755) (by norm_num)
theorem B5256181 : Blo 1640019 5256181 := bbase (se 5 (by rfl) ⟨246383, by rfl⟩ : syracuseStep 5256181 = 492767) (by norm_num)
theorem B2462717 : Blo 1640019 2462717 := bbase (se 3 (by rfl) ⟨461759, by rfl⟩ : syracuseStep 2462717 = 923519) (by norm_num)
theorem B3552269 : Blo 1640019 3552269 := bbase (se 3 (by rfl) ⟨666050, by rfl⟩ : syracuseStep 3552269 = 1332101) (by norm_num)
theorem B2462741 : Blo 1640019 2462741 := bbase (se 6 (by rfl) ⟨57720, by rfl⟩ : syracuseStep 2462741 = 115441) (by norm_num)
theorem B3691565 : Blo 1640019 3691565 := bbase (se 3 (by rfl) ⟨692168, by rfl⟩ : syracuseStep 3691565 = 1384337) (by norm_num)
theorem B2077741 : Blo 1640019 2077741 := bbase (se 3 (by rfl) ⟨389576, by rfl⟩ : syracuseStep 2077741 = 779153) (by norm_num)
theorem B2462765 : Blo 1640019 2462765 := bbase (se 3 (by rfl) ⟨461768, by rfl⟩ : syracuseStep 2462765 = 923537) (by norm_num)
theorem B2462789 : Blo 1640019 2462789 := bbase (se 4 (by rfl) ⟨230886, by rfl⟩ : syracuseStep 2462789 = 461773) (by norm_num)
theorem B2806861 : Blo 1640019 2806861 := bbase (se 3 (by rfl) ⟨526286, by rfl⟩ : syracuseStep 2806861 = 1052573) (by norm_num)
theorem B10515541 : Blo 1640019 10515541 := bbase (se 8 (by rfl) ⟨61614, by rfl⟩ : syracuseStep 10515541 = 123229) (by norm_num)
theorem B2462813 : Blo 1640019 2462813 := bbase (se 3 (by rfl) ⟨461777, by rfl⟩ : syracuseStep 2462813 = 923555) (by norm_num)
theorem B3691637 : Blo 1640019 3691637 := bbase (se 5 (by rfl) ⟨173045, by rfl⟩ : syracuseStep 3691637 = 346091) (by norm_num)
theorem B2462837 : Blo 1640019 2462837 := bbase (se 5 (by rfl) ⟨115445, by rfl⟩ : syracuseStep 2462837 = 230891) (by norm_num)
theorem B2462861 : Blo 1640019 2462861 := bbase (se 3 (by rfl) ⟨461786, by rfl⟩ : syracuseStep 2462861 = 923573) (by norm_num)
theorem B2462885 : Blo 1640019 2462885 := bbase (se 4 (by rfl) ⟨230895, by rfl⟩ : syracuseStep 2462885 = 461791) (by norm_num)
theorem B3691709 : Blo 1640019 3691709 := bbase (se 3 (by rfl) ⟨692195, by rfl⟩ : syracuseStep 3691709 = 1384391) (by norm_num)
theorem B2462909 : Blo 1640019 2462909 := bbase (se 3 (by rfl) ⟨461795, by rfl⟩ : syracuseStep 2462909 = 923591) (by norm_num)
theorem B2462933 : Blo 1640019 2462933 := bbase (se 7 (by rfl) ⟨28862, by rfl⟩ : syracuseStep 2462933 = 57725) (by norm_num)
theorem B2077913 : Blo 1640019 2077913 := bbase (se 2 (by rfl) ⟨779217, by rfl⟩ : syracuseStep 2077913 = 1558435) (by norm_num)
theorem B2462957 : Blo 1640019 2462957 := bbase (se 3 (by rfl) ⟨461804, by rfl⟩ : syracuseStep 2462957 = 923609) (by norm_num)
theorem B3691781 : Blo 1640019 3691781 := bbase (se 4 (by rfl) ⟨346104, by rfl⟩ : syracuseStep 3691781 = 692209) (by norm_num)
theorem B7009541 : Blo 1640019 7009541 := bbase (se 4 (by rfl) ⟨657144, by rfl⟩ : syracuseStep 7009541 = 1314289) (by norm_num)
theorem B2462981 : Blo 1640019 2462981 := bbase (se 4 (by rfl) ⟨230904, by rfl⟩ : syracuseStep 2462981 = 461809) (by norm_num)
theorem B2077969 : Blo 1640019 2077969 := bbase (se 2 (by rfl) ⟨779238, by rfl⟩ : syracuseStep 2077969 = 1558477) (by norm_num)
theorem B2463005 : Blo 1640019 2463005 := bbase (se 3 (by rfl) ⟨461813, by rfl⟩ : syracuseStep 2463005 = 923627) (by norm_num)
theorem B7886117 : Blo 1640019 7886117 := bbase (se 4 (by rfl) ⟨739323, by rfl⟩ : syracuseStep 7886117 = 1478647) (by norm_num)
theorem B14013749 : Blo 1640019 14013749 := bbase (se 5 (by rfl) ⟨656894, by rfl⟩ : syracuseStep 14013749 = 1313789) (by norm_num)
theorem B2463029 : Blo 1640019 2463029 := bbase (se 5 (by rfl) ⟨115454, by rfl⟩ : syracuseStep 2463029 = 230909) (by norm_num)
theorem B3691853 : Blo 1640019 3691853 := bbase (se 3 (by rfl) ⟨692222, by rfl⟩ : syracuseStep 3691853 = 1384445) (by norm_num)
theorem B8303957 : Blo 1640019 8303957 := bbase (se 13 (by rfl) ⟨1520, by rfl⟩ : syracuseStep 8303957 = 3041) (by norm_num)
theorem B2078065 : Blo 1640019 2078065 := bbase (se 2 (by rfl) ⟨779274, by rfl⟩ : syracuseStep 2078065 = 1558549) (by norm_num)
theorem B3691925 : Blo 1640019 3691925 := bbase (se 6 (by rfl) ⟨86529, by rfl⟩ : syracuseStep 3691925 = 173059) (by norm_num)
theorem B8869333 : Blo 1640019 8869333 := bbase (se 7 (by rfl) ⟨103937, by rfl⟩ : syracuseStep 8869333 = 207875) (by norm_num)
theorem B3741149 : Blo 1640019 3741149 := bbase (se 3 (by rfl) ⟨701465, by rfl⟩ : syracuseStep 3741149 = 1402931) (by norm_num)
theorem B3691997 : Blo 1640019 3691997 := bbase (se 3 (by rfl) ⟨692249, by rfl⟩ : syracuseStep 3691997 = 1384499) (by norm_num)
theorem B5535269 : Blo 1640019 5535269 := bbase (se 4 (by rfl) ⟨518931, by rfl⟩ : syracuseStep 5535269 = 1037863) (by norm_num)
theorem B3692069 : Blo 1640019 3692069 := bbase (se 4 (by rfl) ⟨346131, by rfl⟩ : syracuseStep 3692069 = 692263) (by norm_num)
theorem B3503677 : Blo 1640019 3503677 := bbase (se 3 (by rfl) ⟨656939, by rfl⟩ : syracuseStep 3503677 = 1313879) (by norm_num)
theorem B3692141 : Blo 1640019 3692141 := bbase (se 3 (by rfl) ⟨692276, by rfl⟩ : syracuseStep 3692141 = 1384553) (by norm_num)
theorem B2627245 : Blo 1640019 2627245 := bbase (se 3 (by rfl) ⟨492608, by rfl⟩ : syracuseStep 2627245 = 985217) (by norm_num)
theorem B3692213 : Blo 1640019 3692213 := bbase (se 5 (by rfl) ⟨173072, by rfl⟩ : syracuseStep 3692213 = 346145) (by norm_num)
theorem B4495061 : Blo 1640019 4495061 := bbase (se 7 (by rfl) ⟨52676, by rfl⟩ : syracuseStep 4495061 = 105353) (by norm_num)
theorem B3692285 : Blo 1640019 3692285 := bbase (se 3 (by rfl) ⟨692303, by rfl⟩ : syracuseStep 3692285 = 1384607) (by norm_num)
theorem B2807557 : Blo 1640019 2807557 := bbase (se 4 (by rfl) ⟨263208, by rfl⟩ : syracuseStep 2807557 = 526417) (by norm_num)
theorem B3692357 : Blo 1640019 3692357 := bbase (se 4 (by rfl) ⟨346158, by rfl⟩ : syracuseStep 3692357 = 692317) (by norm_num)
theorem B1775441 : Blo 1640019 1775441 := bbase (se 2 (by rfl) ⟨665790, by rfl⟩ : syracuseStep 1775441 = 1331581) (by norm_num)
theorem B4437845 : Blo 1640019 4437845 := bbase (se 9 (by rfl) ⟨13001, by rfl⟩ : syracuseStep 4437845 = 26003) (by norm_num)
theorem B3692429 : Blo 1640019 3692429 := bbase (se 3 (by rfl) ⟨692330, by rfl⟩ : syracuseStep 3692429 = 1384661) (by norm_num)
theorem B3741605 : Blo 1640019 3741605 := bbase (se 4 (by rfl) ⟨350775, by rfl⟩ : syracuseStep 3741605 = 701551) (by norm_num)
theorem B3504053 : Blo 1640019 3504053 := bbase (se 5 (by rfl) ⟨164252, by rfl⟩ : syracuseStep 3504053 = 328505) (by norm_num)
theorem B5535701 : Blo 1640019 5535701 := bbase (se 7 (by rfl) ⟨64871, by rfl⟩ : syracuseStep 5535701 = 129743) (by norm_num)
theorem B3692501 : Blo 1640019 3692501 := bbase (se 7 (by rfl) ⟨43271, by rfl⟩ : syracuseStep 3692501 = 86543) (by norm_num)
theorem B1972193 : Blo 1640019 1972193 := bbase (se 2 (by rfl) ⟨739572, by rfl⟩ : syracuseStep 1972193 = 1479145) (by norm_num)
theorem B6649877 : Blo 1640019 6649877 := bbase (se 6 (by rfl) ⟨155856, by rfl⟩ : syracuseStep 6649877 = 311713) (by norm_num)
theorem B6232085 : Blo 1640019 6232085 := bbase (se 6 (by rfl) ⟨146064, by rfl⟩ : syracuseStep 6232085 = 292129) (by norm_num)
theorem B3692573 : Blo 1640019 3692573 := bbase (se 3 (by rfl) ⟨692357, by rfl⟩ : syracuseStep 3692573 = 1384715) (by norm_num)
theorem B7485493 : Blo 1640019 7485493 := bbase (se 5 (by rfl) ⟨350882, by rfl⟩ : syracuseStep 7485493 = 701765) (by norm_num)
theorem B3692645 : Blo 1640019 3692645 := bbase (se 4 (by rfl) ⟨346185, by rfl⟩ : syracuseStep 3692645 = 692371) (by norm_num)
theorem B2496629 : Blo 1640019 2496629 := bbase (se 5 (by rfl) ⟨117029, by rfl⟩ : syracuseStep 2496629 = 234059) (by norm_num)
theorem B3692717 : Blo 1640019 3692717 := bbase (se 3 (by rfl) ⟨692384, by rfl⟩ : syracuseStep 3692717 = 1384769) (by norm_num)
theorem B2627797 : Blo 1640019 2627797 := bbase (se 7 (by rfl) ⟨30794, by rfl⟩ : syracuseStep 2627797 = 61589) (by norm_num)
theorem B17742037 : Blo 1640019 17742037 := bbase (se 7 (by rfl) ⟨207914, by rfl⟩ : syracuseStep 17742037 = 415829) (by norm_num)
theorem B4151533 : Blo 1640019 4151533 := bbase (se 3 (by rfl) ⟨778412, by rfl⟩ : syracuseStep 4151533 = 1556825) (by norm_num)
theorem B3692789 : Blo 1640019 3692789 := bbase (se 5 (by rfl) ⟨173099, by rfl⟩ : syracuseStep 3692789 = 346199) (by norm_num)
theorem B5331221 : Blo 1640019 5331221 := bbase (se 6 (by rfl) ⟨124950, by rfl⟩ : syracuseStep 5331221 = 249901) (by norm_num)
theorem B6232373 : Blo 1640019 6232373 := bbase (se 5 (by rfl) ⟨292142, by rfl⟩ : syracuseStep 6232373 = 584285) (by norm_num)
theorem B3692861 : Blo 1640019 3692861 := bbase (se 3 (by rfl) ⟨692411, by rfl⟩ : syracuseStep 3692861 = 1384823) (by norm_num)
theorem B5257541 : Blo 1640019 5257541 := bbase (se 4 (by rfl) ⟨492894, by rfl⟩ : syracuseStep 5257541 = 985789) (by norm_num)
theorem B1972549 : Blo 1640019 1972549 := bbase (se 4 (by rfl) ⟨184926, by rfl⟩ : syracuseStep 1972549 = 369853) (by norm_num)
theorem B4151645 : Blo 1640019 4151645 := bbase (se 3 (by rfl) ⟨778433, by rfl⟩ : syracuseStep 4151645 = 1556867) (by norm_num)
theorem B2955637 : Blo 1640019 2955637 := bbase (se 5 (by rfl) ⟨138545, by rfl⟩ : syracuseStep 2955637 = 277091) (by norm_num)
theorem B5536133 : Blo 1640019 5536133 := bbase (se 4 (by rfl) ⟨519012, by rfl⟩ : syracuseStep 5536133 = 1038025) (by norm_num)
theorem B3692933 : Blo 1640019 3692933 := bbase (se 4 (by rfl) ⟨346212, by rfl⟩ : syracuseStep 3692933 = 692425) (by norm_num)
theorem B5257669 : Blo 1640019 5257669 := bbase (se 4 (by rfl) ⟨492906, by rfl⟩ : syracuseStep 5257669 = 985813) (by norm_num)
theorem B3693005 : Blo 1640019 3693005 := bbase (se 3 (by rfl) ⟨692438, by rfl⟩ : syracuseStep 3693005 = 1384877) (by norm_num)
theorem B2628053 : Blo 1640019 2628053 := bbase (se 7 (by rfl) ⟨30797, by rfl⟩ : syracuseStep 2628053 = 61595) (by norm_num)
theorem B3693077 : Blo 1640019 3693077 := bbase (se 6 (by rfl) ⟨86556, by rfl⟩ : syracuseStep 3693077 = 173113) (by norm_num)
theorem B4151837 : Blo 1640019 4151837 := bbase (se 3 (by rfl) ⟨778469, by rfl⟩ : syracuseStep 4151837 = 1556939) (by norm_num)
theorem B3693149 : Blo 1640019 3693149 := bbase (se 3 (by rfl) ⟨692465, by rfl⟩ : syracuseStep 3693149 = 1384931) (by norm_num)
theorem B8305253 : Blo 1640019 8305253 := bbase (se 4 (by rfl) ⟨778617, by rfl⟩ : syracuseStep 8305253 = 1557235) (by norm_num)
theorem B3693221 : Blo 1640019 3693221 := bbase (se 4 (by rfl) ⟨346239, by rfl⟩ : syracuseStep 3693221 = 692479) (by norm_num)
theorem B5257925 : Blo 1640019 5257925 := bbase (se 4 (by rfl) ⟨492930, by rfl⟩ : syracuseStep 5257925 = 985861) (by norm_num)
theorem B1751753 : Blo 1640019 1751753 := bbase (se 2 (by rfl) ⟨656907, by rfl⟩ : syracuseStep 1751753 = 1313815) (by norm_num)
theorem B3693293 : Blo 1640019 3693293 := bbase (se 3 (by rfl) ⟨692492, by rfl⟩ : syracuseStep 3693293 = 1384985) (by norm_num)
theorem B2767621 : Blo 1640019 2767621 := bbase (se 4 (by rfl) ⟨259464, by rfl⟩ : syracuseStep 2767621 = 518929) (by norm_num)
theorem B5536565 : Blo 1640019 5536565 := bbase (se 5 (by rfl) ⟨259526, by rfl⟩ : syracuseStep 5536565 = 519053) (by norm_num)
theorem B3693365 : Blo 1640019 3693365 := bbase (se 5 (by rfl) ⟨173126, by rfl⟩ : syracuseStep 3693365 = 346253) (by norm_num)
theorem B2104129 : Blo 1640019 2104129 := bbase (se 2 (by rfl) ⟨789048, by rfl⟩ : syracuseStep 2104129 = 1578097) (by norm_num)
theorem B2767709 : Blo 1640019 2767709 := bbase (se 3 (by rfl) ⟨518945, by rfl⟩ : syracuseStep 2767709 = 1037891) (by norm_num)
theorem B4152181 : Blo 1640019 4152181 := bbase (se 5 (by rfl) ⟨194633, by rfl⟩ : syracuseStep 4152181 = 389267) (by norm_num)
theorem B8420213 : Blo 1640019 8420213 := bbase (se 5 (by rfl) ⟨394697, by rfl⟩ : syracuseStep 8420213 = 789395) (by norm_num)
theorem B3693437 : Blo 1640019 3693437 := bbase (se 3 (by rfl) ⟨692519, by rfl⟩ : syracuseStep 3693437 = 1385039) (by norm_num)
theorem B9345941 : Blo 1640019 9345941 := bbase (se 6 (by rfl) ⟨219045, by rfl⟩ : syracuseStep 9345941 = 438091) (by norm_num)
theorem B3693509 : Blo 1640019 3693509 := bbase (se 4 (by rfl) ⟨346266, by rfl⟩ : syracuseStep 3693509 = 692533) (by norm_num)
theorem B2767837 : Blo 1640019 2767837 := bbase (se 3 (by rfl) ⟨518969, by rfl⟩ : syracuseStep 2767837 = 1037939) (by norm_num)
theorem B4152293 : Blo 1640019 4152293 := bbase (se 4 (by rfl) ⟨389277, by rfl⟩ : syracuseStep 4152293 = 778555) (by norm_num)
theorem B3693581 : Blo 1640019 3693581 := bbase (se 3 (by rfl) ⟨692546, by rfl⟩ : syracuseStep 3693581 = 1385093) (by norm_num)
theorem B2767925 : Blo 1640019 2767925 := bbase (se 5 (by rfl) ⟨129746, by rfl⟩ : syracuseStep 2767925 = 259493) (by norm_num)
theorem B3693653 : Blo 1640019 3693653 := bbase (se 8 (by rfl) ⟨21642, by rfl⟩ : syracuseStep 3693653 = 43285) (by norm_num)
theorem B1752197 : Blo 1640019 1752197 := bbase (se 4 (by rfl) ⟨164268, by rfl⟩ : syracuseStep 1752197 = 328537) (by norm_num)
theorem B2628757 : Blo 1640019 2628757 := bbase (se 6 (by rfl) ⟨61611, by rfl⟩ : syracuseStep 2628757 = 123223) (by norm_num)
theorem B3693725 : Blo 1640019 3693725 := bbase (se 3 (by rfl) ⟨692573, by rfl⟩ : syracuseStep 3693725 = 1385147) (by norm_num)
theorem B4152485 : Blo 1640019 4152485 := bbase (se 4 (by rfl) ⟨389295, by rfl⟩ : syracuseStep 4152485 = 778591) (by norm_num)
theorem B2768053 : Blo 1640019 2768053 := bbase (se 5 (by rfl) ⟨129752, by rfl⟩ : syracuseStep 2768053 = 259505) (by norm_num)
theorem B5536997 : Blo 1640019 5536997 := bbase (se 4 (by rfl) ⟨519093, by rfl⟩ : syracuseStep 5536997 = 1038187) (by norm_num)
theorem B2956517 : Blo 1640019 2956517 := bbase (se 4 (by rfl) ⟨277173, by rfl⟩ : syracuseStep 2956517 = 554347) (by norm_num)
theorem B3693797 : Blo 1640019 3693797 := bbase (se 4 (by rfl) ⟨346293, by rfl⟩ : syracuseStep 3693797 = 692587) (by norm_num)
theorem B7888117 : Blo 1640019 7888117 := bbase (se 5 (by rfl) ⟨369755, by rfl⟩ : syracuseStep 7888117 = 739511) (by norm_num)
theorem B3742973 : Blo 1640019 3742973 := bbase (se 3 (by rfl) ⟨701807, by rfl⟩ : syracuseStep 3742973 = 1403615) (by norm_num)
theorem B2768141 : Blo 1640019 2768141 := bbase (se 3 (by rfl) ⟨519026, by rfl⟩ : syracuseStep 2768141 = 1038053) (by norm_num)
theorem B4799765 : Blo 1640019 4799765 := bbase (se 6 (by rfl) ⟨112494, by rfl⟩ : syracuseStep 4799765 = 224989) (by norm_num)
theorem B3693869 : Blo 1640019 3693869 := bbase (se 3 (by rfl) ⟨692600, by rfl⟩ : syracuseStep 3693869 = 1385201) (by norm_num)
theorem B3693941 : Blo 1640019 3693941 := bbase (se 5 (by rfl) ⟨173153, by rfl⟩ : syracuseStep 3693941 = 346307) (by norm_num)
theorem B1752445 : Blo 1640019 1752445 := bbase (se 3 (by rfl) ⟨328583, by rfl⟩ : syracuseStep 1752445 = 657167) (by norm_num)
theorem B2768269 : Blo 1640019 2768269 := bbase (se 3 (by rfl) ⟨519050, by rfl⟩ : syracuseStep 2768269 = 1038101) (by norm_num)
theorem B3694013 : Blo 1640019 3694013 := bbase (se 3 (by rfl) ⟨692627, by rfl⟩ : syracuseStep 3694013 = 1385255) (by norm_num)
theorem B6233557 : Blo 1640019 6233557 := bbase (se 7 (by rfl) ⟨73049, by rfl⟩ : syracuseStep 6233557 = 146099) (by norm_num)
theorem B2768357 : Blo 1640019 2768357 := bbase (se 4 (by rfl) ⟨259533, by rfl⟩ : syracuseStep 2768357 = 519067) (by norm_num)
theorem B4152829 : Blo 1640019 4152829 := bbase (se 3 (by rfl) ⟨778655, by rfl⟩ : syracuseStep 4152829 = 1557311) (by norm_num)
theorem B3694085 : Blo 1640019 3694085 := bbase (se 4 (by rfl) ⟨346320, by rfl⟩ : syracuseStep 3694085 = 692641) (by norm_num)
theorem B3792413 : Blo 1640019 3792413 := bbase (se 3 (by rfl) ⟨711077, by rfl⟩ : syracuseStep 3792413 = 1422155) (by norm_num)
theorem B3505693 : Blo 1640019 3505693 := bbase (se 3 (by rfl) ⟨657317, by rfl⟩ : syracuseStep 3505693 = 1314635) (by norm_num)
theorem B2629181 : Blo 1640019 2629181 := bbase (se 3 (by rfl) ⟨492971, by rfl⟩ : syracuseStep 2629181 = 985943) (by norm_num)
theorem B3694157 : Blo 1640019 3694157 := bbase (se 3 (by rfl) ⟨692654, by rfl⟩ : syracuseStep 3694157 = 1385309) (by norm_num)
theorem B2768485 : Blo 1640019 2768485 := bbase (se 4 (by rfl) ⟨259545, by rfl⟩ : syracuseStep 2768485 = 519091) (by norm_num)
theorem B4152941 : Blo 1640019 4152941 := bbase (se 3 (by rfl) ⟨778676, by rfl⟩ : syracuseStep 4152941 = 1557353) (by norm_num)
theorem B5537429 : Blo 1640019 5537429 := bbase (se 6 (by rfl) ⟨129783, by rfl⟩ : syracuseStep 5537429 = 259567) (by norm_num)
theorem B3694229 : Blo 1640019 3694229 := bbase (se 6 (by rfl) ⟨86583, by rfl⟩ : syracuseStep 3694229 = 173167) (by norm_num)
theorem B2768573 : Blo 1640019 2768573 := bbase (se 3 (by rfl) ⟨519107, by rfl⟩ : syracuseStep 2768573 = 1038215) (by norm_num)
theorem B3694301 : Blo 1640019 3694301 := bbase (se 3 (by rfl) ⟨692681, by rfl⟩ : syracuseStep 3694301 = 1385363) (by norm_num)
theorem B6233861 : Blo 1640019 6233861 := bbase (se 4 (by rfl) ⟨584424, by rfl⟩ : syracuseStep 6233861 = 1168849) (by norm_num)
theorem B3694373 : Blo 1640019 3694373 := bbase (se 4 (by rfl) ⟨346347, by rfl⟩ : syracuseStep 3694373 = 692695) (by norm_num)
theorem B4153133 : Blo 1640019 4153133 := bbase (se 3 (by rfl) ⟨778712, by rfl⟩ : syracuseStep 4153133 = 1557425) (by norm_num)
theorem B1752877 : Blo 1640019 1752877 := bbase (se 3 (by rfl) ⟨328664, by rfl⟩ : syracuseStep 1752877 = 657329) (by norm_num)
theorem B2768701 : Blo 1640019 2768701 := bbase (se 3 (by rfl) ⟨519131, by rfl⟩ : syracuseStep 2768701 = 1038263) (by norm_num)
theorem B3325789 : Blo 1640019 3325789 := bbase (se 3 (by rfl) ⟨623585, by rfl⟩ : syracuseStep 3325789 = 1247171) (by norm_num)
theorem B2629469 : Blo 1640019 2629469 := bbase (se 3 (by rfl) ⟨493025, by rfl⟩ : syracuseStep 2629469 = 986051) (by norm_num)
theorem B3694445 : Blo 1640019 3694445 := bbase (se 3 (by rfl) ⟨692708, by rfl⟩ : syracuseStep 3694445 = 1385417) (by norm_num)
theorem B8306549 : Blo 1640019 8306549 := bbase (se 5 (by rfl) ⟨389369, by rfl⟩ : syracuseStep 8306549 = 778739) (by norm_num)
theorem B1752949 : Blo 1640019 1752949 := bbase (se 5 (by rfl) ⟨82169, by rfl⟩ : syracuseStep 1752949 = 164339) (by norm_num)
theorem B2768789 : Blo 1640019 2768789 := bbase (se 6 (by rfl) ⟨64893, by rfl⟩ : syracuseStep 2768789 = 129787) (by norm_num)
theorem B3694517 : Blo 1640019 3694517 := bbase (se 5 (by rfl) ⟨173180, by rfl⟩ : syracuseStep 3694517 = 346361) (by norm_num)
theorem B3997637 : Blo 1640019 3997637 := bbase (se 4 (by rfl) ⟨374778, by rfl⟩ : syracuseStep 3997637 = 749557) (by norm_num)
theorem B3743701 : Blo 1640019 3743701 := bbase (se 7 (by rfl) ⟨43871, by rfl⟩ : syracuseStep 3743701 = 87743) (by norm_num)
theorem B5611493 : Blo 1640019 5611493 := bbase (se 4 (by rfl) ⟨526077, by rfl⟩ : syracuseStep 5611493 = 1052155) (by norm_num)
theorem B2768897 : Blo 1640019 2768897 := bstep (se 2 (by rfl) ⟨1038336, by rfl⟩ : syracuseStep 2768897 = 2076673) B2076673
theorem B3506257 : Blo 1640019 3506257 := bstep (se 2 (by rfl) ⟨1314846, by rfl⟩ : syracuseStep 3506257 = 2629693) B2629693
theorem B4153457 : Blo 1640019 4153457 := bstep (se 2 (by rfl) ⟨1557546, by rfl⟩ : syracuseStep 4153457 = 3115093) B3115093
theorem B2769025 : Blo 1640019 2769025 := bstep (se 2 (by rfl) ⟨1038384, by rfl⟩ : syracuseStep 2769025 = 2076769) B2076769
theorem B2769059 : Blo 1640019 2769059 := bstep (se 1 (by rfl) ⟨2076794, by rfl⟩ : syracuseStep 2769059 = 4153589) B4153589
theorem B5537969 : Blo 1640019 5537969 := bstep (se 2 (by rfl) ⟨2076738, by rfl⟩ : syracuseStep 5537969 = 4153477) B4153477
theorem B6234317 : Blo 1640019 6234317 := bstep (se 3 (by rfl) ⟨1168934, by rfl⟩ : syracuseStep 6234317 = 2337869) B2337869
theorem B2769187 : Blo 1640019 2769187 := bstep (se 1 (by rfl) ⟨2076890, by rfl⟩ : syracuseStep 2769187 = 4153781) B4153781
theorem B2769329 : Blo 1640019 2769329 := bstep (se 2 (by rfl) ⟨1038498, by rfl⟩ : syracuseStep 2769329 = 2076997) B2076997
theorem B7889329 : Blo 1640019 7889329 := bstep (se 2 (by rfl) ⟨2958498, by rfl⟩ : syracuseStep 7889329 = 5916997) B5916997
theorem B2630065 : Blo 1640019 2630065 := bstep (se 2 (by rfl) ⟨986274, by rfl⟩ : syracuseStep 2630065 = 1972549) B1972549
theorem B3940849 : Blo 1640019 3940849 := bstep (se 2 (by rfl) ⟨1477818, by rfl⟩ : syracuseStep 3940849 = 2955637) B2955637
theorem B12976625 : Blo 1640019 12976625 := bstep (se 2 (by rfl) ⟨4866234, by rfl⟩ : syracuseStep 12976625 = 9732469) B9732469
theorem B1663507 : Blo 1640019 1663507 := bstep (se 1 (by rfl) ⟨1247630, by rfl⟩ : syracuseStep 1663507 = 2495261) B2495261
theorem B2769457 : Blo 1640019 2769457 := bstep (se 2 (by rfl) ⟨1038546, by rfl⟩ : syracuseStep 2769457 = 2077093) B2077093
theorem B2769491 : Blo 1640019 2769491 := bstep (se 1 (by rfl) ⟨2077118, by rfl⟩ : syracuseStep 2769491 = 4154237) B4154237
theorem B8422001 : Blo 1640019 8422001 := bstep (se 2 (by rfl) ⟨3158250, by rfl⟩ : syracuseStep 8422001 = 6316501) B6316501
theorem B3113635 : Blo 1640019 3113635 := bstep (se 1 (by rfl) ⟨2335226, by rfl⟩ : syracuseStep 3113635 = 4670453) B4670453
theorem B7103153 : Blo 1640019 7103153 := bstep (se 2 (by rfl) ⟨2663682, by rfl⟩ : syracuseStep 7103153 = 5327365) B5327365
theorem B5538509 : Blo 1640019 5538509 := bstep (se 3 (by rfl) ⟨1038470, by rfl⟩ : syracuseStep 5538509 = 2076941) B2076941
theorem B2769619 : Blo 1640019 2769619 := bstep (se 1 (by rfl) ⟨2077214, by rfl⟩ : syracuseStep 2769619 = 4154429) B4154429
theorem B3506915 : Blo 1640019 3506915 := bstep (se 1 (by rfl) ⟨2630186, by rfl⟩ : syracuseStep 3506915 = 5260373) B5260373
theorem B5538563 : Blo 1640019 5538563 := bstep (se 1 (by rfl) ⟨4153922, by rfl⟩ : syracuseStep 5538563 = 8307845) B8307845
theorem B21029645 : Blo 1640019 21029645 := bstep (se 3 (by rfl) ⟨3943058, by rfl⟩ : syracuseStep 21029645 = 7886117) B7886117
theorem B3113795 : Blo 1640019 3113795 := bstep (se 1 (by rfl) ⟨2335346, by rfl⟩ : syracuseStep 3113795 = 4670693) B4670693
theorem B2769761 : Blo 1640019 2769761 := bstep (se 2 (by rfl) ⟨1038660, by rfl⟩ : syracuseStep 2769761 = 2077321) B2077321
theorem B31556465 : Blo 1640019 31556465 := bstep (se 2 (by rfl) ⟨11833674, by rfl⟩ : syracuseStep 31556465 = 23667349) B23667349
theorem B2769889 : Blo 1640019 2769889 := bstep (se 2 (by rfl) ⟨1038708, by rfl⟩ : syracuseStep 2769889 = 2077417) B2077417
theorem B8307683 : Blo 1640019 8307683 := bstep (se 1 (by rfl) ⟨6230762, by rfl⟩ : syracuseStep 8307683 = 12461525) B12461525
theorem B2769923 : Blo 1640019 2769923 := bstep (se 1 (by rfl) ⟨2077442, by rfl⟩ : syracuseStep 2769923 = 4154885) B4154885
theorem B5538833 : Blo 1640019 5538833 := bstep (se 2 (by rfl) ⟨2077062, by rfl⟩ : syracuseStep 5538833 = 4154125) B4154125
theorem B4154449 : Blo 1640019 4154449 := bstep (se 2 (by rfl) ⟨1557918, by rfl⟩ : syracuseStep 4154449 = 3115837) B3115837
theorem B6227057 : Blo 1640019 6227057 := bstep (se 2 (by rfl) ⟨2335146, by rfl⟩ : syracuseStep 6227057 = 4670293) B4670293
theorem B2770051 : Blo 1640019 2770051 := bstep (se 1 (by rfl) ⟨2077538, by rfl⟩ : syracuseStep 2770051 = 4155077) B4155077
theorem B2958563 : Blo 1640019 2958563 := bstep (se 1 (by rfl) ⟨2218922, by rfl⟩ : syracuseStep 2958563 = 4437845) B4437845
theorem B15762701 : Blo 1640019 15762701 := bstep (se 3 (by rfl) ⟨2955506, by rfl⟩ : syracuseStep 15762701 = 5911013) B5911013
theorem B2770193 : Blo 1640019 2770193 := bstep (se 2 (by rfl) ⟨1038822, by rfl⟩ : syracuseStep 2770193 = 2077645) B2077645
theorem B2336035 : Blo 1640019 2336035 := bstep (se 1 (by rfl) ⟨1752026, by rfl⟩ : syracuseStep 2336035 = 3504053) B3504053
theorem B4433251 : Blo 1640019 4433251 := bstep (se 1 (by rfl) ⟨3324938, by rfl⟩ : syracuseStep 4433251 = 6649877) B6649877
theorem B4154723 : Blo 1640019 4154723 := bstep (se 1 (by rfl) ⟨3116042, by rfl⟩ : syracuseStep 4154723 = 6232085) B6232085
theorem B15992177 : Blo 1640019 15992177 := bstep (se 2 (by rfl) ⟨5997066, by rfl⟩ : syracuseStep 15992177 = 11994133) B11994133
theorem B10519949 : Blo 1640019 10519949 := bstep (se 3 (by rfl) ⟨1972490, by rfl⟩ : syracuseStep 10519949 = 3944981) B3944981
theorem B2770321 : Blo 1640019 2770321 := bstep (se 2 (by rfl) ⟨1038870, by rfl⟩ : syracuseStep 2770321 = 2077741) B2077741
theorem B2770355 : Blo 1640019 2770355 := bstep (se 1 (by rfl) ⟨2077766, by rfl⟩ : syracuseStep 2770355 = 4155533) B4155533
theorem B3327427 : Blo 1640019 3327427 := bstep (se 1 (by rfl) ⟨2495570, by rfl⟩ : syracuseStep 3327427 = 4991141) B4991141
theorem B23643589 : Blo 1640019 23643589 := bstep (se 4 (by rfl) ⟨2216586, by rfl⟩ : syracuseStep 23643589 = 4433173) B4433173
theorem B4154915 : Blo 1640019 4154915 := bstep (se 1 (by rfl) ⟨3116186, by rfl⟩ : syracuseStep 4154915 = 6232373) B6232373
theorem B5539373 : Blo 1640019 5539373 := bstep (se 3 (by rfl) ⟨1038632, by rfl⟩ : syracuseStep 5539373 = 2077265) B2077265
theorem B2770483 : Blo 1640019 2770483 := bstep (se 1 (by rfl) ⟨2077862, by rfl⟩ : syracuseStep 2770483 = 4155725) B4155725
theorem B1640019 : Blo 1640019 1640019 := bstep (se 1 (by rfl) ⟨1230014, by rfl⟩ : syracuseStep 1640019 = 2460029) B2460029
theorem B1640035 : Blo 1640019 1640035 := bstep (se 1 (by rfl) ⟨1230026, by rfl⟩ : syracuseStep 1640035 = 2460053) B2460053
theorem B5539427 : Blo 1640019 5539427 := bstep (se 1 (by rfl) ⟨4154570, by rfl⟩ : syracuseStep 5539427 = 8309141) B8309141
theorem B1640051 : Blo 1640019 1640051 := bstep (se 1 (by rfl) ⟨1230038, by rfl⟩ : syracuseStep 1640051 = 2460077) B2460077
theorem B1640067 : Blo 1640019 1640067 := bstep (se 1 (by rfl) ⟨1230050, by rfl⟩ : syracuseStep 1640067 = 2460101) B2460101
theorem B1640083 : Blo 1640019 1640083 := bstep (se 1 (by rfl) ⟨1230062, by rfl⟩ : syracuseStep 1640083 = 2460125) B2460125
theorem B1640099 : Blo 1640019 1640099 := bstep (se 1 (by rfl) ⟨1230074, by rfl⟩ : syracuseStep 1640099 = 2460149) B2460149
theorem B1640115 : Blo 1640019 1640115 := bstep (se 1 (by rfl) ⟨1230086, by rfl⟩ : syracuseStep 1640115 = 2460173) B2460173
theorem B2770625 : Blo 1640019 2770625 := bstep (se 2 (by rfl) ⟨1038984, by rfl⟩ : syracuseStep 2770625 = 2077969) B2077969
theorem B1640131 : Blo 1640019 1640131 := bstep (se 1 (by rfl) ⟨1230098, by rfl⟩ : syracuseStep 1640131 = 2460197) B2460197
theorem B4556483 : Blo 1640019 4556483 := bstep (se 1 (by rfl) ⟨3417362, by rfl⟩ : syracuseStep 4556483 = 6834725) B6834725
theorem B1640147 : Blo 1640019 1640147 := bstep (se 1 (by rfl) ⟨1230110, by rfl⟩ : syracuseStep 1640147 = 2460221) B2460221
theorem B1640163 : Blo 1640019 1640163 := bstep (se 1 (by rfl) ⟨1230122, by rfl⟩ : syracuseStep 1640163 = 2460245) B2460245
theorem B1640179 : Blo 1640019 1640179 := bstep (se 1 (by rfl) ⟨1230134, by rfl⟩ : syracuseStep 1640179 = 2460269) B2460269
theorem B1640195 : Blo 1640019 1640195 := bstep (se 1 (by rfl) ⟨1230146, by rfl⟩ : syracuseStep 1640195 = 2460293) B2460293
theorem B6227725 : Blo 1640019 6227725 := bstep (se 3 (by rfl) ⟨1167698, by rfl⟩ : syracuseStep 6227725 = 2335397) B2335397
theorem B8308493 : Blo 1640019 8308493 := bstep (se 3 (by rfl) ⟨1557842, by rfl⟩ : syracuseStep 8308493 = 3115685) B3115685
theorem B1640211 : Blo 1640019 1640211 := bstep (se 1 (by rfl) ⟨1230158, by rfl⟩ : syracuseStep 1640211 = 2460317) B2460317
theorem B1640227 : Blo 1640019 1640227 := bstep (se 1 (by rfl) ⟨1230170, by rfl⟩ : syracuseStep 1640227 = 2460341) B2460341
theorem B1640243 : Blo 1640019 1640243 := bstep (se 1 (by rfl) ⟨1230182, by rfl⟩ : syracuseStep 1640243 = 2460365) B2460365
theorem B2770753 : Blo 1640019 2770753 := bstep (se 2 (by rfl) ⟨1039032, by rfl⟩ : syracuseStep 2770753 = 2078065) B2078065
theorem B1640259 : Blo 1640019 1640259 := bstep (se 1 (by rfl) ⟨1230194, by rfl⟩ : syracuseStep 1640259 = 2460389) B2460389
theorem B17737541 : Blo 1640019 17737541 := bstep (se 4 (by rfl) ⟨1662894, by rfl⟩ : syracuseStep 17737541 = 3325789) B3325789
theorem B1640275 : Blo 1640019 1640275 := bstep (se 1 (by rfl) ⟨1230206, by rfl⟩ : syracuseStep 1640275 = 2460413) B2460413
theorem B1640291 : Blo 1640019 1640291 := bstep (se 1 (by rfl) ⟨1230218, by rfl⟩ : syracuseStep 1640291 = 2460437) B2460437
theorem B2770787 : Blo 1640019 2770787 := bstep (se 1 (by rfl) ⟨2078090, by rfl⟩ : syracuseStep 2770787 = 4156181) B4156181
theorem B4671341 : Blo 1640019 4671341 := bstep (se 3 (by rfl) ⟨875876, by rfl⟩ : syracuseStep 4671341 = 1751753) B1751753
theorem B3114865 : Blo 1640019 3114865 := bstep (se 2 (by rfl) ⟨1168074, by rfl⟩ : syracuseStep 3114865 = 2336149) B2336149
theorem B5539697 : Blo 1640019 5539697 := bstep (se 2 (by rfl) ⟨2077386, by rfl⟩ : syracuseStep 5539697 = 4154773) B4154773
theorem B1640307 : Blo 1640019 1640307 := bstep (se 1 (by rfl) ⟨1230230, by rfl⟩ : syracuseStep 1640307 = 2460461) B2460461
theorem B1640323 : Blo 1640019 1640323 := bstep (se 1 (by rfl) ⟨1230242, by rfl⟩ : syracuseStep 1640323 = 2460485) B2460485
theorem B11986829 : Blo 1640019 11986829 := bstep (se 3 (by rfl) ⟨2247530, by rfl⟩ : syracuseStep 11986829 = 4495061) B4495061
theorem B1845139 : Blo 1640019 1845139 := bstep (se 1 (by rfl) ⟨1383854, by rfl⟩ : syracuseStep 1845139 = 2767709) B2767709
theorem B1640339 : Blo 1640019 1640339 := bstep (se 1 (by rfl) ⟨1230254, by rfl⟩ : syracuseStep 1640339 = 2460509) B2460509
theorem B1640355 : Blo 1640019 1640355 := bstep (se 1 (by rfl) ⟨1230266, by rfl⟩ : syracuseStep 1640355 = 2460533) B2460533
theorem B5613475 : Blo 1640019 5613475 := bstep (se 1 (by rfl) ⟨4210106, by rfl⟩ : syracuseStep 5613475 = 8420213) B8420213
theorem B1640371 : Blo 1640019 1640371 := bstep (se 1 (by rfl) ⟨1230278, by rfl⟩ : syracuseStep 1640371 = 2460557) B2460557
theorem B1640387 : Blo 1640019 1640387 := bstep (se 1 (by rfl) ⟨1230290, by rfl⟩ : syracuseStep 1640387 = 2460581) B2460581
theorem B1640403 : Blo 1640019 1640403 := bstep (se 1 (by rfl) ⟨1230302, by rfl⟩ : syracuseStep 1640403 = 2460605) B2460605
theorem B1640419 : Blo 1640019 1640419 := bstep (se 1 (by rfl) ⟨1230314, by rfl⟩ : syracuseStep 1640419 = 2460629) B2460629
theorem B1640435 : Blo 1640019 1640435 := bstep (se 1 (by rfl) ⟨1230326, by rfl⟩ : syracuseStep 1640435 = 2460653) B2460653
theorem B1640451 : Blo 1640019 1640451 := bstep (se 1 (by rfl) ⟨1230338, by rfl⟩ : syracuseStep 1640451 = 2460677) B2460677
theorem B1640467 : Blo 1640019 1640467 := bstep (se 1 (by rfl) ⟨1230350, by rfl⟩ : syracuseStep 1640467 = 2460701) B2460701
theorem B1845283 : Blo 1640019 1845283 := bstep (se 1 (by rfl) ⟨1383962, by rfl⟩ : syracuseStep 1845283 = 2767925) B2767925
theorem B4671523 : Blo 1640019 4671523 := bstep (se 1 (by rfl) ⟨3503642, by rfl⟩ : syracuseStep 4671523 = 7007285) B7007285
theorem B1640483 : Blo 1640019 1640483 := bstep (se 1 (by rfl) ⟨1230362, by rfl⟩ : syracuseStep 1640483 = 2460725) B2460725
theorem B1640499 : Blo 1640019 1640499 := bstep (se 1 (by rfl) ⟨1230374, by rfl⟩ : syracuseStep 1640499 = 2460749) B2460749
theorem B1640515 : Blo 1640019 1640515 := bstep (se 1 (by rfl) ⟨1230386, by rfl⟩ : syracuseStep 1640515 = 2460773) B2460773
theorem B4671569 : Blo 1640019 4671569 := bstep (se 2 (by rfl) ⟨1751838, by rfl⟩ : syracuseStep 4671569 = 3503677) B3503677
theorem B1640531 : Blo 1640019 1640531 := bstep (se 1 (by rfl) ⟨1230398, by rfl⟩ : syracuseStep 1640531 = 2460797) B2460797
theorem B1640547 : Blo 1640019 1640547 := bstep (se 1 (by rfl) ⟨1230410, by rfl⟩ : syracuseStep 1640547 = 2460821) B2460821
theorem B9341041 : Blo 1640019 9341041 := bstep (se 2 (by rfl) ⟨3502890, by rfl⟩ : syracuseStep 9341041 = 7005781) B7005781
theorem B1640563 : Blo 1640019 1640563 := bstep (se 1 (by rfl) ⟨1230422, by rfl⟩ : syracuseStep 1640563 = 2460845) B2460845
theorem B1640579 : Blo 1640019 1640579 := bstep (se 1 (by rfl) ⟨1230434, by rfl⟩ : syracuseStep 1640579 = 2460869) B2460869
theorem B1640595 : Blo 1640019 1640595 := bstep (se 1 (by rfl) ⟨1230446, by rfl⟩ : syracuseStep 1640595 = 2460893) B2460893
theorem B1640611 : Blo 1640019 1640611 := bstep (se 1 (by rfl) ⟨1230458, by rfl⟩ : syracuseStep 1640611 = 2460917) B2460917
theorem B1845427 : Blo 1640019 1845427 := bstep (se 1 (by rfl) ⟨1384070, by rfl⟩ : syracuseStep 1845427 = 2768141) B2768141
theorem B1640627 : Blo 1640019 1640627 := bstep (se 1 (by rfl) ⟨1230470, by rfl⟩ : syracuseStep 1640627 = 2460941) B2460941
theorem B1640643 : Blo 1640019 1640643 := bstep (se 1 (by rfl) ⟨1230482, by rfl⟩ : syracuseStep 1640643 = 2460965) B2460965
theorem B1640659 : Blo 1640019 1640659 := bstep (se 1 (by rfl) ⟨1230494, by rfl⟩ : syracuseStep 1640659 = 2460989) B2460989
theorem B1640675 : Blo 1640019 1640675 := bstep (se 1 (by rfl) ⟨1230506, by rfl⟩ : syracuseStep 1640675 = 2461013) B2461013
theorem B1640691 : Blo 1640019 1640691 := bstep (se 1 (by rfl) ⟨1230518, by rfl⟩ : syracuseStep 1640691 = 2461037) B2461037
theorem B1640707 : Blo 1640019 1640707 := bstep (se 1 (by rfl) ⟨1230530, by rfl⟩ : syracuseStep 1640707 = 2461061) B2461061
theorem B8988941 : Blo 1640019 8988941 := bstep (se 3 (by rfl) ⟨1685426, by rfl⟩ : syracuseStep 8988941 = 3370853) B3370853
theorem B1640723 : Blo 1640019 1640723 := bstep (se 1 (by rfl) ⟨1230542, by rfl⟩ : syracuseStep 1640723 = 2461085) B2461085
theorem B1640739 : Blo 1640019 1640739 := bstep (se 1 (by rfl) ⟨1230554, by rfl⟩ : syracuseStep 1640739 = 2461109) B2461109
theorem B1640755 : Blo 1640019 1640755 := bstep (se 1 (by rfl) ⟨1230566, by rfl⟩ : syracuseStep 1640755 = 2461133) B2461133
theorem B1845571 : Blo 1640019 1845571 := bstep (se 1 (by rfl) ⟨1384178, by rfl⟩ : syracuseStep 1845571 = 2768357) B2768357
theorem B1640771 : Blo 1640019 1640771 := bstep (se 1 (by rfl) ⟨1230578, by rfl⟩ : syracuseStep 1640771 = 2461157) B2461157
theorem B1640787 : Blo 1640019 1640787 := bstep (se 1 (by rfl) ⟨1230590, by rfl⟩ : syracuseStep 1640787 = 2461181) B2461181
theorem B1640803 : Blo 1640019 1640803 := bstep (se 1 (by rfl) ⟨1230602, by rfl⟩ : syracuseStep 1640803 = 2461205) B2461205
theorem B1640819 : Blo 1640019 1640819 := bstep (se 1 (by rfl) ⟨1230614, by rfl⟩ : syracuseStep 1640819 = 2461229) B2461229
theorem B2460035 : Blo 1640019 2460035 := bstep (se 1 (by rfl) ⟨1845026, by rfl⟩ : syracuseStep 2460035 = 3690053) B3690053
theorem B10512773 : Blo 1640019 10512773 := bstep (se 4 (by rfl) ⟨985572, by rfl⟩ : syracuseStep 10512773 = 1971145) B1971145
theorem B1640835 : Blo 1640019 1640835 := bstep (se 1 (by rfl) ⟨1230626, by rfl⟩ : syracuseStep 1640835 = 2461253) B2461253
theorem B2337169 : Blo 1640019 2337169 := bstep (se 2 (by rfl) ⟨876438, by rfl⟩ : syracuseStep 2337169 = 1752877) B1752877
theorem B1640851 : Blo 1640019 1640851 := bstep (se 1 (by rfl) ⟨1230638, by rfl⟩ : syracuseStep 1640851 = 2461277) B2461277
theorem B5540237 : Blo 1640019 5540237 := bstep (se 3 (by rfl) ⟨1038794, by rfl⟩ : syracuseStep 5540237 = 2077589) B2077589
theorem B2460065 : Blo 1640019 2460065 := bstep (se 2 (by rfl) ⟨922524, by rfl⟩ : syracuseStep 2460065 = 1845049) B1845049
theorem B1640867 : Blo 1640019 1640867 := bstep (se 1 (by rfl) ⟨1230650, by rfl⟩ : syracuseStep 1640867 = 2461301) B2461301
theorem B2460083 : Blo 1640019 2460083 := bstep (se 1 (by rfl) ⟨1845062, by rfl⟩ : syracuseStep 2460083 = 3690125) B3690125
theorem B1640883 : Blo 1640019 1640883 := bstep (se 1 (by rfl) ⟨1230662, by rfl⟩ : syracuseStep 1640883 = 2461325) B2461325
theorem B1640899 : Blo 1640019 1640899 := bstep (se 1 (by rfl) ⟨1230674, by rfl⟩ : syracuseStep 1640899 = 2461349) B2461349
theorem B5540291 : Blo 1640019 5540291 := bstep (se 1 (by rfl) ⟨4155218, by rfl⟩ : syracuseStep 5540291 = 8310437) B8310437
theorem B19966405 : Blo 1640019 19966405 := bstep (se 4 (by rfl) ⟨1871850, by rfl⟩ : syracuseStep 19966405 = 3743701) B3743701
theorem B2460113 : Blo 1640019 2460113 := bstep (se 2 (by rfl) ⟨922542, by rfl⟩ : syracuseStep 2460113 = 1845085) B1845085
theorem B4155857 : Blo 1640019 4155857 := bstep (se 2 (by rfl) ⟨1558446, by rfl⟩ : syracuseStep 4155857 = 3116893) B3116893
theorem B1845715 : Blo 1640019 1845715 := bstep (se 1 (by rfl) ⟨1384286, by rfl⟩ : syracuseStep 1845715 = 2768573) B2768573
theorem B1640915 : Blo 1640019 1640915 := bstep (se 1 (by rfl) ⟨1230686, by rfl⟩ : syracuseStep 1640915 = 2461373) B2461373
theorem B2460131 : Blo 1640019 2460131 := bstep (se 1 (by rfl) ⟨1845098, by rfl⟩ : syracuseStep 2460131 = 3690197) B3690197
theorem B1640931 : Blo 1640019 1640931 := bstep (se 1 (by rfl) ⟨1230698, by rfl⟩ : syracuseStep 1640931 = 2461397) B2461397
theorem B2337265 : Blo 1640019 2337265 := bstep (se 2 (by rfl) ⟨876474, by rfl⟩ : syracuseStep 2337265 = 1752949) B1752949
theorem B1640947 : Blo 1640019 1640947 := bstep (se 1 (by rfl) ⟨1230710, by rfl⟩ : syracuseStep 1640947 = 2461421) B2461421
theorem B2460161 : Blo 1640019 2460161 := bstep (se 2 (by rfl) ⟨922560, by rfl⟩ : syracuseStep 2460161 = 1845121) B1845121
theorem B1640963 : Blo 1640019 1640963 := bstep (se 1 (by rfl) ⟨1230722, by rfl⟩ : syracuseStep 1640963 = 2461445) B2461445
theorem B4155907 : Blo 1640019 4155907 := bstep (se 1 (by rfl) ⟨3116930, by rfl⟩ : syracuseStep 4155907 = 6233861) B6233861
theorem B2460179 : Blo 1640019 2460179 := bstep (se 1 (by rfl) ⟨1845134, by rfl⟩ : syracuseStep 2460179 = 3690269) B3690269
theorem B1640979 : Blo 1640019 1640979 := bstep (se 1 (by rfl) ⟨1230734, by rfl⟩ : syracuseStep 1640979 = 2461469) B2461469
theorem B6228515 : Blo 1640019 6228515 := bstep (se 1 (by rfl) ⟨4671386, by rfl⟩ : syracuseStep 6228515 = 9342773) B9342773
theorem B1640995 : Blo 1640019 1640995 := bstep (se 1 (by rfl) ⟨1230746, by rfl⟩ : syracuseStep 1640995 = 2461493) B2461493
theorem B2460209 : Blo 1640019 2460209 := bstep (se 2 (by rfl) ⟨922578, by rfl⟩ : syracuseStep 2460209 = 1845157) B1845157
theorem B1641011 : Blo 1640019 1641011 := bstep (se 1 (by rfl) ⟨1230758, by rfl⟩ : syracuseStep 1641011 = 2461517) B2461517
theorem B2460227 : Blo 1640019 2460227 := bstep (se 1 (by rfl) ⟨1845170, by rfl⟩ : syracuseStep 2460227 = 3690341) B3690341
theorem B1641027 : Blo 1640019 1641027 := bstep (se 1 (by rfl) ⟨1230770, by rfl⟩ : syracuseStep 1641027 = 2461541) B2461541
theorem B1641043 : Blo 1640019 1641043 := bstep (se 1 (by rfl) ⟨1230782, by rfl⟩ : syracuseStep 1641043 = 2461565) B2461565
theorem B2460257 : Blo 1640019 2460257 := bstep (se 2 (by rfl) ⟨922596, by rfl⟩ : syracuseStep 2460257 = 1845193) B1845193
theorem B1845859 : Blo 1640019 1845859 := bstep (se 1 (by rfl) ⟨1384394, by rfl⟩ : syracuseStep 1845859 = 2768789) B2768789
theorem B1641059 : Blo 1640019 1641059 := bstep (se 1 (by rfl) ⟨1230794, by rfl⟩ : syracuseStep 1641059 = 2461589) B2461589
theorem B47966833 : Blo 1640019 47966833 := bstep (se 2 (by rfl) ⟨17987562, by rfl⟩ : syracuseStep 47966833 = 35975125) B35975125
theorem B2460275 : Blo 1640019 2460275 := bstep (se 1 (by rfl) ⟨1845206, by rfl⟩ : syracuseStep 2460275 = 3690413) B3690413
theorem B1641075 : Blo 1640019 1641075 := bstep (se 1 (by rfl) ⟨1230806, by rfl⟩ : syracuseStep 1641075 = 2461613) B2461613
theorem B1641091 : Blo 1640019 1641091 := bstep (se 1 (by rfl) ⟨1230818, by rfl⟩ : syracuseStep 1641091 = 2461637) B2461637
theorem B2665091 : Blo 1640019 2665091 := bstep (se 1 (by rfl) ⟨1998818, by rfl⟩ : syracuseStep 2665091 = 3997637) B3997637
theorem B2460305 : Blo 1640019 2460305 := bstep (se 2 (by rfl) ⟨922614, by rfl⟩ : syracuseStep 2460305 = 1845229) B1845229
theorem B4156049 : Blo 1640019 4156049 := bstep (se 2 (by rfl) ⟨1558518, by rfl⟩ : syracuseStep 4156049 = 3117037) B3117037
theorem B1641107 : Blo 1640019 1641107 := bstep (se 1 (by rfl) ⟨1230830, by rfl⟩ : syracuseStep 1641107 = 2461661) B2461661
theorem B2460323 : Blo 1640019 2460323 := bstep (se 1 (by rfl) ⟨1845242, by rfl⟩ : syracuseStep 2460323 = 3690485) B3690485
theorem B1641123 : Blo 1640019 1641123 := bstep (se 1 (by rfl) ⟨1230842, by rfl⟩ : syracuseStep 1641123 = 2461685) B2461685
theorem B1641139 : Blo 1640019 1641139 := bstep (se 1 (by rfl) ⟨1230854, by rfl⟩ : syracuseStep 1641139 = 2461709) B2461709
theorem B2460353 : Blo 1640019 2460353 := bstep (se 2 (by rfl) ⟨922632, by rfl⟩ : syracuseStep 2460353 = 1845265) B1845265
theorem B1641155 : Blo 1640019 1641155 := bstep (se 1 (by rfl) ⟨1230866, by rfl⟩ : syracuseStep 1641155 = 2461733) B2461733
theorem B9472717 : Blo 1640019 9472717 := bstep (se 3 (by rfl) ⟨1776134, by rfl⟩ : syracuseStep 9472717 = 3552269) B3552269
theorem B5540561 : Blo 1640019 5540561 := bstep (se 2 (by rfl) ⟨2077710, by rfl⟩ : syracuseStep 5540561 = 4155421) B4155421
theorem B2460371 : Blo 1640019 2460371 := bstep (se 1 (by rfl) ⟨1845278, by rfl⟩ : syracuseStep 2460371 = 3690557) B3690557
theorem B1641171 : Blo 1640019 1641171 := bstep (se 1 (by rfl) ⟨1230878, by rfl⟩ : syracuseStep 1641171 = 2461757) B2461757
theorem B1641187 : Blo 1640019 1641187 := bstep (se 1 (by rfl) ⟨1230890, by rfl⟩ : syracuseStep 1641187 = 2461781) B2461781
theorem B3328643 : Blo 1640019 3328643 := bstep (se 1 (by rfl) ⟨2496482, by rfl⟩ : syracuseStep 3328643 = 4992965) B4992965
theorem B2460401 : Blo 1640019 2460401 := bstep (se 2 (by rfl) ⟨922650, by rfl⟩ : syracuseStep 2460401 = 1845301) B1845301
theorem B9980657 : Blo 1640019 9980657 := bstep (se 2 (by rfl) ⟨3742746, by rfl⟩ : syracuseStep 9980657 = 7485493) B7485493
theorem B1846003 : Blo 1640019 1846003 := bstep (se 1 (by rfl) ⟨1384502, by rfl⟩ : syracuseStep 1846003 = 2769005) B2769005
theorem B1641203 : Blo 1640019 1641203 := bstep (se 1 (by rfl) ⟨1230902, by rfl⟩ : syracuseStep 1641203 = 2461805) B2461805
theorem B2460419 : Blo 1640019 2460419 := bstep (se 1 (by rfl) ⟨1845314, by rfl⟩ : syracuseStep 2460419 = 3690629) B3690629
theorem B1641219 : Blo 1640019 1641219 := bstep (se 1 (by rfl) ⟨1230914, by rfl⟩ : syracuseStep 1641219 = 2461829) B2461829
theorem B1641235 : Blo 1640019 1641235 := bstep (se 1 (by rfl) ⟨1230926, by rfl⟩ : syracuseStep 1641235 = 2461853) B2461853
theorem B59894549 : Blo 1640019 59894549 := bstep (se 6 (by rfl) ⟨1403778, by rfl⟩ : syracuseStep 59894549 = 2807557) B2807557
theorem B2460449 : Blo 1640019 2460449 := bstep (se 2 (by rfl) ⟨922668, by rfl⟩ : syracuseStep 2460449 = 1845337) B1845337
theorem B1641251 : Blo 1640019 1641251 := bstep (se 1 (by rfl) ⟨1230938, by rfl⟩ : syracuseStep 1641251 = 2461877) B2461877
theorem B2460467 : Blo 1640019 2460467 := bstep (se 1 (by rfl) ⟨1845350, by rfl⟩ : syracuseStep 2460467 = 3690701) B3690701
theorem B1641267 : Blo 1640019 1641267 := bstep (se 1 (by rfl) ⟨1230950, by rfl⟩ : syracuseStep 1641267 = 2461901) B2461901
theorem B1641283 : Blo 1640019 1641283 := bstep (se 1 (by rfl) ⟨1230962, by rfl⟩ : syracuseStep 1641283 = 2461925) B2461925
theorem B2460497 : Blo 1640019 2460497 := bstep (se 2 (by rfl) ⟨922686, by rfl⟩ : syracuseStep 2460497 = 1845373) B1845373
theorem B1641299 : Blo 1640019 1641299 := bstep (se 1 (by rfl) ⟨1230974, by rfl⟩ : syracuseStep 1641299 = 2461949) B2461949
theorem B2460515 : Blo 1640019 2460515 := bstep (se 1 (by rfl) ⟨1845386, by rfl⟩ : syracuseStep 2460515 = 3690773) B3690773
theorem B1641315 : Blo 1640019 1641315 := bstep (se 1 (by rfl) ⟨1230986, by rfl⟩ : syracuseStep 1641315 = 2461973) B2461973
theorem B1641331 : Blo 1640019 1641331 := bstep (se 1 (by rfl) ⟨1230998, by rfl⟩ : syracuseStep 1641331 = 2461997) B2461997
theorem B2460545 : Blo 1640019 2460545 := bstep (se 2 (by rfl) ⟨922704, by rfl⟩ : syracuseStep 2460545 = 1845409) B1845409
theorem B1846147 : Blo 1640019 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B1641347 : Blo 1640019 1641347 := bstep (se 1 (by rfl) ⟨1231010, by rfl⟩ : syracuseStep 1641347 = 2462021) B2462021
theorem B3115921 : Blo 1640019 3115921 := bstep (se 2 (by rfl) ⟨1168470, by rfl⟩ : syracuseStep 3115921 = 2336941) B2336941
theorem B2460563 : Blo 1640019 2460563 := bstep (se 1 (by rfl) ⟨1845422, by rfl⟩ : syracuseStep 2460563 = 3690845) B3690845
theorem B1641363 : Blo 1640019 1641363 := bstep (se 1 (by rfl) ⟨1231022, by rfl⟩ : syracuseStep 1641363 = 2462045) B2462045
theorem B1641379 : Blo 1640019 1641379 := bstep (se 1 (by rfl) ⟨1231034, by rfl⟩ : syracuseStep 1641379 = 2462069) B2462069
theorem B2460593 : Blo 1640019 2460593 := bstep (se 2 (by rfl) ⟨922722, by rfl⟩ : syracuseStep 2460593 = 1845445) B1845445
theorem B1641395 : Blo 1640019 1641395 := bstep (se 1 (by rfl) ⟨1231046, by rfl⟩ : syracuseStep 1641395 = 2462093) B2462093
theorem B2460611 : Blo 1640019 2460611 := bstep (se 1 (by rfl) ⟨1845458, by rfl⟩ : syracuseStep 2460611 = 3690917) B3690917
theorem B1641411 : Blo 1640019 1641411 := bstep (se 1 (by rfl) ⟨1231058, by rfl⟩ : syracuseStep 1641411 = 2462117) B2462117
theorem B1641427 : Blo 1640019 1641427 := bstep (se 1 (by rfl) ⟨1231070, by rfl⟩ : syracuseStep 1641427 = 2462141) B2462141
theorem B2460641 : Blo 1640019 2460641 := bstep (se 2 (by rfl) ⟨922740, by rfl⟩ : syracuseStep 2460641 = 1845481) B1845481
theorem B2337761 : Blo 1640019 2337761 := bstep (se 2 (by rfl) ⟨876660, by rfl⟩ : syracuseStep 2337761 = 1753321) B1753321
theorem B1641443 : Blo 1640019 1641443 := bstep (se 1 (by rfl) ⟨1231082, by rfl⟩ : syracuseStep 1641443 = 2462165) B2462165
theorem B2460659 : Blo 1640019 2460659 := bstep (se 1 (by rfl) ⟨1845494, by rfl⟩ : syracuseStep 2460659 = 3690989) B3690989
theorem B1641459 : Blo 1640019 1641459 := bstep (se 1 (by rfl) ⟨1231094, by rfl⟩ : syracuseStep 1641459 = 2462189) B2462189
theorem B3156995 : Blo 1640019 3156995 := bstep (se 1 (by rfl) ⟨2367746, by rfl⟩ : syracuseStep 3156995 = 4735493) B4735493
theorem B1641475 : Blo 1640019 1641475 := bstep (se 1 (by rfl) ⟨1231106, by rfl⟩ : syracuseStep 1641475 = 2462213) B2462213
theorem B2460689 : Blo 1640019 2460689 := bstep (se 2 (by rfl) ⟨922758, by rfl⟩ : syracuseStep 2460689 = 1845517) B1845517
theorem B1846291 : Blo 1640019 1846291 := bstep (se 1 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 1846291 = 2769437) B2769437
theorem B1641491 : Blo 1640019 1641491 := bstep (se 1 (by rfl) ⟨1231118, by rfl⟩ : syracuseStep 1641491 = 2462237) B2462237
theorem B2460707 : Blo 1640019 2460707 := bstep (se 1 (by rfl) ⟨1845530, by rfl⟩ : syracuseStep 2460707 = 3691061) B3691061
theorem B1641507 : Blo 1640019 1641507 := bstep (se 1 (by rfl) ⟨1231130, by rfl⟩ : syracuseStep 1641507 = 2462261) B2462261
theorem B1641523 : Blo 1640019 1641523 := bstep (se 1 (by rfl) ⟨1231142, by rfl⟩ : syracuseStep 1641523 = 2462285) B2462285
theorem B2460737 : Blo 1640019 2460737 := bstep (se 2 (by rfl) ⟨922776, by rfl⟩ : syracuseStep 2460737 = 1845553) B1845553
theorem B1641539 : Blo 1640019 1641539 := bstep (se 1 (by rfl) ⟨1231154, by rfl⟩ : syracuseStep 1641539 = 2462309) B2462309
theorem B2460755 : Blo 1640019 2460755 := bstep (se 1 (by rfl) ⟨1845566, by rfl⟩ : syracuseStep 2460755 = 3691133) B3691133
theorem B1641555 : Blo 1640019 1641555 := bstep (se 1 (by rfl) ⟨1231166, by rfl⟩ : syracuseStep 1641555 = 2462333) B2462333
theorem B1641571 : Blo 1640019 1641571 := bstep (se 1 (by rfl) ⟨1231178, by rfl⟩ : syracuseStep 1641571 = 2462357) B2462357
theorem B2460785 : Blo 1640019 2460785 := bstep (se 2 (by rfl) ⟨922794, by rfl⟩ : syracuseStep 2460785 = 1845589) B1845589
theorem B1641587 : Blo 1640019 1641587 := bstep (se 1 (by rfl) ⟨1231190, by rfl⟩ : syracuseStep 1641587 = 2462381) B2462381
theorem B2460803 : Blo 1640019 2460803 := bstep (se 1 (by rfl) ⟨1845602, by rfl⟩ : syracuseStep 2460803 = 3691205) B3691205
theorem B1641603 : Blo 1640019 1641603 := bstep (se 1 (by rfl) ⟨1231202, by rfl⟩ : syracuseStep 1641603 = 2462405) B2462405
theorem B1641619 : Blo 1640019 1641619 := bstep (se 1 (by rfl) ⟨1231214, by rfl⟩ : syracuseStep 1641619 = 2462429) B2462429
theorem B2460833 : Blo 1640019 2460833 := bstep (se 2 (by rfl) ⟨922812, by rfl⟩ : syracuseStep 2460833 = 1845625) B1845625
theorem B1846435 : Blo 1640019 1846435 := bstep (se 1 (by rfl) ⟨1384826, by rfl⟩ : syracuseStep 1846435 = 2769653) B2769653
theorem B1641635 : Blo 1640019 1641635 := bstep (se 1 (by rfl) ⟨1231226, by rfl⟩ : syracuseStep 1641635 = 2462453) B2462453
theorem B6229169 : Blo 1640019 6229169 := bstep (se 2 (by rfl) ⟨2335938, by rfl⟩ : syracuseStep 6229169 = 4671877) B4671877
theorem B2460851 : Blo 1640019 2460851 := bstep (se 1 (by rfl) ⟨1845638, by rfl⟩ : syracuseStep 2460851 = 3691277) B3691277
theorem B1641651 : Blo 1640019 1641651 := bstep (se 1 (by rfl) ⟨1231238, by rfl⟩ : syracuseStep 1641651 = 2462477) B2462477
theorem B1641667 : Blo 1640019 1641667 := bstep (se 1 (by rfl) ⟨1231250, by rfl⟩ : syracuseStep 1641667 = 2462501) B2462501
theorem B11234501 : Blo 1640019 11234501 := bstep (se 4 (by rfl) ⟨1053234, by rfl⟩ : syracuseStep 11234501 = 2106469) B2106469
theorem B2460881 : Blo 1640019 2460881 := bstep (se 2 (by rfl) ⟨922830, by rfl⟩ : syracuseStep 2460881 = 1845661) B1845661
theorem B1641683 : Blo 1640019 1641683 := bstep (se 1 (by rfl) ⟨1231262, by rfl⟩ : syracuseStep 1641683 = 2462525) B2462525
theorem B2460899 : Blo 1640019 2460899 := bstep (se 1 (by rfl) ⟨1845674, by rfl⟩ : syracuseStep 2460899 = 3691349) B3691349
theorem B1641699 : Blo 1640019 1641699 := bstep (se 1 (by rfl) ⟨1231274, by rfl⟩ : syracuseStep 1641699 = 2462549) B2462549
theorem B5541101 : Blo 1640019 5541101 := bstep (se 3 (by rfl) ⟨1038956, by rfl⟩ : syracuseStep 5541101 = 2077913) B2077913
theorem B20221169 : Blo 1640019 20221169 := bstep (se 2 (by rfl) ⟨7582938, by rfl⟩ : syracuseStep 20221169 = 15165877) B15165877
theorem B1641715 : Blo 1640019 1641715 := bstep (se 1 (by rfl) ⟨1231286, by rfl⟩ : syracuseStep 1641715 = 2462573) B2462573
theorem B2460929 : Blo 1640019 2460929 := bstep (se 2 (by rfl) ⟨922848, by rfl⟩ : syracuseStep 2460929 = 1845697) B1845697
theorem B1641731 : Blo 1640019 1641731 := bstep (se 1 (by rfl) ⟨1231298, by rfl⟩ : syracuseStep 1641731 = 2462597) B2462597
theorem B2460947 : Blo 1640019 2460947 := bstep (se 1 (by rfl) ⟨1845710, by rfl⟩ : syracuseStep 2460947 = 3691421) B3691421
theorem B1641747 : Blo 1640019 1641747 := bstep (se 1 (by rfl) ⟨1231310, by rfl⟩ : syracuseStep 1641747 = 2462621) B2462621
theorem B3116323 : Blo 1640019 3116323 := bstep (se 1 (by rfl) ⟨2337242, by rfl⟩ : syracuseStep 3116323 = 4674485) B4674485
theorem B1641763 : Blo 1640019 1641763 := bstep (se 1 (by rfl) ⟨1231322, by rfl⟩ : syracuseStep 1641763 = 2462645) B2462645
theorem B5541155 : Blo 1640019 5541155 := bstep (se 1 (by rfl) ⟨4155866, by rfl⟩ : syracuseStep 5541155 = 8311733) B8311733
theorem B2460977 : Blo 1640019 2460977 := bstep (se 2 (by rfl) ⟨922866, by rfl⟩ : syracuseStep 2460977 = 1845733) B1845733
theorem B11234609 : Blo 1640019 11234609 := bstep (se 2 (by rfl) ⟨4212978, by rfl⟩ : syracuseStep 11234609 = 8425957) B8425957
theorem B1846579 : Blo 1640019 1846579 := bstep (se 1 (by rfl) ⟨1384934, by rfl⟩ : syracuseStep 1846579 = 2769869) B2769869
theorem B1641779 : Blo 1640019 1641779 := bstep (se 1 (by rfl) ⟨1231334, by rfl⟩ : syracuseStep 1641779 = 2462669) B2462669
theorem B26602805 : Blo 1640019 26602805 := bstep (se 5 (by rfl) ⟨1247006, by rfl⟩ : syracuseStep 26602805 = 2494013) B2494013
theorem B2460995 : Blo 1640019 2460995 := bstep (se 1 (by rfl) ⟨1845746, by rfl⟩ : syracuseStep 2460995 = 3691493) B3691493
theorem B1641795 : Blo 1640019 1641795 := bstep (se 1 (by rfl) ⟨1231346, by rfl⟩ : syracuseStep 1641795 = 2462693) B2462693
theorem B3116369 : Blo 1640019 3116369 := bstep (se 2 (by rfl) ⟨1168638, by rfl⟩ : syracuseStep 3116369 = 2337277) B2337277
theorem B1641811 : Blo 1640019 1641811 := bstep (se 1 (by rfl) ⟨1231358, by rfl⟩ : syracuseStep 1641811 = 2462717) B2462717
theorem B2461025 : Blo 1640019 2461025 := bstep (se 2 (by rfl) ⟨922884, by rfl⟩ : syracuseStep 2461025 = 1845769) B1845769
theorem B1641827 : Blo 1640019 1641827 := bstep (se 1 (by rfl) ⟨1231370, by rfl⟩ : syracuseStep 1641827 = 2462741) B2462741
theorem B2461043 : Blo 1640019 2461043 := bstep (se 1 (by rfl) ⟨1845782, by rfl⟩ : syracuseStep 2461043 = 3691565) B3691565
theorem B1641843 : Blo 1640019 1641843 := bstep (se 1 (by rfl) ⟨1231382, by rfl⟩ : syracuseStep 1641843 = 2462765) B2462765
theorem B1641859 : Blo 1640019 1641859 := bstep (se 1 (by rfl) ⟨1231394, by rfl⟩ : syracuseStep 1641859 = 2462789) B2462789
theorem B2461073 : Blo 1640019 2461073 := bstep (se 2 (by rfl) ⟨922902, by rfl⟩ : syracuseStep 2461073 = 1845805) B1845805
theorem B1641875 : Blo 1640019 1641875 := bstep (se 1 (by rfl) ⟨1231406, by rfl⟩ : syracuseStep 1641875 = 2462813) B2462813
theorem B2461091 : Blo 1640019 2461091 := bstep (se 1 (by rfl) ⟨1845818, by rfl⟩ : syracuseStep 2461091 = 3691637) B3691637
theorem B1641891 : Blo 1640019 1641891 := bstep (se 1 (by rfl) ⟨1231418, by rfl⟩ : syracuseStep 1641891 = 2462837) B2462837
theorem B1641907 : Blo 1640019 1641907 := bstep (se 1 (by rfl) ⟨1231430, by rfl⟩ : syracuseStep 1641907 = 2462861) B2462861
theorem B2461121 : Blo 1640019 2461121 := bstep (se 2 (by rfl) ⟨922920, by rfl⟩ : syracuseStep 2461121 = 1845841) B1845841
theorem B1846723 : Blo 1640019 1846723 := bstep (se 1 (by rfl) ⟨1385042, by rfl⟩ : syracuseStep 1846723 = 2770085) B2770085
theorem B1641923 : Blo 1640019 1641923 := bstep (se 1 (by rfl) ⟨1231442, by rfl⟩ : syracuseStep 1641923 = 2462885) B2462885
theorem B14020037 : Blo 1640019 14020037 := bstep (se 4 (by rfl) ⟨1314378, by rfl⟩ : syracuseStep 14020037 = 2628757) B2628757
theorem B2461139 : Blo 1640019 2461139 := bstep (se 1 (by rfl) ⟨1845854, by rfl⟩ : syracuseStep 2461139 = 3691709) B3691709
theorem B1641939 : Blo 1640019 1641939 := bstep (se 1 (by rfl) ⟨1231454, by rfl⟩ : syracuseStep 1641939 = 2462909) B2462909
theorem B2076131 : Blo 1640019 2076131 := bstep (se 1 (by rfl) ⟨1557098, by rfl⟩ : syracuseStep 2076131 = 3114197) B3114197
theorem B1641955 : Blo 1640019 1641955 := bstep (se 1 (by rfl) ⟨1231466, by rfl⟩ : syracuseStep 1641955 = 2462933) B2462933
theorem B2461169 : Blo 1640019 2461169 := bstep (se 2 (by rfl) ⟨922938, by rfl⟩ : syracuseStep 2461169 = 1845877) B1845877
theorem B1641971 : Blo 1640019 1641971 := bstep (se 1 (by rfl) ⟨1231478, by rfl⟩ : syracuseStep 1641971 = 2462957) B2462957
theorem B2461187 : Blo 1640019 2461187 := bstep (se 1 (by rfl) ⟨1845890, by rfl⟩ : syracuseStep 2461187 = 3691781) B3691781
theorem B4673027 : Blo 1640019 4673027 := bstep (se 1 (by rfl) ⟨3504770, by rfl⟩ : syracuseStep 4673027 = 7009541) B7009541
theorem B1641987 : Blo 1640019 1641987 := bstep (se 1 (by rfl) ⟨1231490, by rfl⟩ : syracuseStep 1641987 = 2462981) B2462981
theorem B4435469 : Blo 1640019 4435469 := bstep (se 3 (by rfl) ⟨831650, by rfl⟩ : syracuseStep 4435469 = 1663301) B1663301
theorem B4992529 : Blo 1640019 4992529 := bstep (se 2 (by rfl) ⟨1872198, by rfl⟩ : syracuseStep 4992529 = 3744397) B3744397
theorem B1642003 : Blo 1640019 1642003 := bstep (se 1 (by rfl) ⟨1231502, by rfl⟩ : syracuseStep 1642003 = 2463005) B2463005
theorem B2461217 : Blo 1640019 2461217 := bstep (se 2 (by rfl) ⟨922956, by rfl⟩ : syracuseStep 2461217 = 1845913) B1845913
theorem B9342499 : Blo 1640019 9342499 := bstep (se 1 (by rfl) ⟨7006874, by rfl⟩ : syracuseStep 9342499 = 14013749) B14013749
theorem B1642019 : Blo 1640019 1642019 := bstep (se 1 (by rfl) ⟨1231514, by rfl⟩ : syracuseStep 1642019 = 2463029) B2463029
theorem B5541425 : Blo 1640019 5541425 := bstep (se 2 (by rfl) ⟨2078034, by rfl⟩ : syracuseStep 5541425 = 4156069) B4156069
theorem B2461235 : Blo 1640019 2461235 := bstep (se 1 (by rfl) ⟨1845926, by rfl⟩ : syracuseStep 2461235 = 3691853) B3691853
theorem B14011973 : Blo 1640019 14011973 := bstep (se 4 (by rfl) ⟨1313622, by rfl⟩ : syracuseStep 14011973 = 2627245) B2627245
theorem B2461265 : Blo 1640019 2461265 := bstep (se 2 (by rfl) ⟨922974, by rfl⟩ : syracuseStep 2461265 = 1845949) B1845949
theorem B1846867 : Blo 1640019 1846867 := bstep (se 1 (by rfl) ⟨1385150, by rfl⟩ : syracuseStep 1846867 = 2770301) B2770301
theorem B2461283 : Blo 1640019 2461283 := bstep (se 1 (by rfl) ⟨1845962, by rfl⟩ : syracuseStep 2461283 = 3691925) B3691925
theorem B3116657 : Blo 1640019 3116657 := bstep (se 2 (by rfl) ⟨1168746, by rfl⟩ : syracuseStep 3116657 = 2337493) B2337493
theorem B2461313 : Blo 1640019 2461313 := bstep (se 2 (by rfl) ⟨922992, by rfl⟩ : syracuseStep 2461313 = 1845985) B1845985
theorem B2494099 : Blo 1640019 2494099 := bstep (se 1 (by rfl) ⟨1870574, by rfl⟩ : syracuseStep 2494099 = 3741149) B3741149
theorem B2461331 : Blo 1640019 2461331 := bstep (se 1 (by rfl) ⟨1845998, by rfl⟩ : syracuseStep 2461331 = 3691997) B3691997
theorem B3690161 : Blo 1640019 3690161 := bstep (se 2 (by rfl) ⟨1383810, by rfl⟩ : syracuseStep 3690161 = 2767621) B2767621
theorem B2461361 : Blo 1640019 2461361 := bstep (se 2 (by rfl) ⟨923010, by rfl⟩ : syracuseStep 2461361 = 1846021) B1846021
theorem B3690179 : Blo 1640019 3690179 := bstep (se 1 (by rfl) ⟨2767634, by rfl⟩ : syracuseStep 3690179 = 5535269) B5535269
theorem B2461379 : Blo 1640019 2461379 := bstep (se 1 (by rfl) ⟨1846034, by rfl⟩ : syracuseStep 2461379 = 3692069) B3692069
theorem B2461409 : Blo 1640019 2461409 := bstep (se 2 (by rfl) ⟨923028, by rfl⟩ : syracuseStep 2461409 = 1846057) B1846057
theorem B1847011 : Blo 1640019 1847011 := bstep (se 1 (by rfl) ⟨1385258, by rfl⟩ : syracuseStep 1847011 = 2770517) B2770517
theorem B11833073 : Blo 1640019 11833073 := bstep (se 2 (by rfl) ⟨4437402, by rfl⟩ : syracuseStep 11833073 = 8874805) B8874805
theorem B2461427 : Blo 1640019 2461427 := bstep (se 1 (by rfl) ⟨1846070, by rfl⟩ : syracuseStep 2461427 = 3692141) B3692141
theorem B12455693 : Blo 1640019 12455693 := bstep (se 3 (by rfl) ⟨2335442, by rfl⟩ : syracuseStep 12455693 = 4670885) B4670885
theorem B2461457 : Blo 1640019 2461457 := bstep (se 2 (by rfl) ⟨923046, by rfl⟩ : syracuseStep 2461457 = 1846093) B1846093
theorem B2461475 : Blo 1640019 2461475 := bstep (se 1 (by rfl) ⟨1846106, by rfl⟩ : syracuseStep 2461475 = 3692213) B3692213
theorem B2461505 : Blo 1640019 2461505 := bstep (se 2 (by rfl) ⟨923064, by rfl⟩ : syracuseStep 2461505 = 1846129) B1846129
theorem B2461523 : Blo 1640019 2461523 := bstep (se 1 (by rfl) ⟨1846142, by rfl⟩ : syracuseStep 2461523 = 3692285) B3692285
theorem B2461553 : Blo 1640019 2461553 := bstep (se 2 (by rfl) ⟨923082, by rfl⟩ : syracuseStep 2461553 = 1846165) B1846165
theorem B1847155 : Blo 1640019 1847155 := bstep (se 1 (by rfl) ⟨1385366, by rfl⟩ : syracuseStep 1847155 = 2770733) B2770733
theorem B2461571 : Blo 1640019 2461571 := bstep (se 1 (by rfl) ⟨1846178, by rfl⟩ : syracuseStep 2461571 = 3692357) B3692357
theorem B2461601 : Blo 1640019 2461601 := bstep (se 2 (by rfl) ⟨923100, by rfl⟩ : syracuseStep 2461601 = 1846201) B1846201
theorem B2461619 : Blo 1640019 2461619 := bstep (se 1 (by rfl) ⟨1846214, by rfl⟩ : syracuseStep 2461619 = 3692429) B3692429
theorem B2494403 : Blo 1640019 2494403 := bstep (se 1 (by rfl) ⟨1870802, by rfl⟩ : syracuseStep 2494403 = 3741605) B3741605
theorem B3690449 : Blo 1640019 3690449 := bstep (se 2 (by rfl) ⟨1383918, by rfl⟩ : syracuseStep 3690449 = 2767837) B2767837
theorem B2461649 : Blo 1640019 2461649 := bstep (se 2 (by rfl) ⟨923118, by rfl⟩ : syracuseStep 2461649 = 1846237) B1846237
theorem B3690467 : Blo 1640019 3690467 := bstep (se 1 (by rfl) ⟨2767850, by rfl⟩ : syracuseStep 3690467 = 5535701) B5535701
theorem B7008227 : Blo 1640019 7008227 := bstep (se 1 (by rfl) ⟨5256170, by rfl⟩ : syracuseStep 7008227 = 10512341) B10512341
theorem B2461667 : Blo 1640019 2461667 := bstep (se 1 (by rfl) ⟨1846250, by rfl⟩ : syracuseStep 2461667 = 3692501) B3692501
theorem B2461697 : Blo 1640019 2461697 := bstep (se 2 (by rfl) ⟨923136, by rfl⟩ : syracuseStep 2461697 = 1846273) B1846273
theorem B2461715 : Blo 1640019 2461715 := bstep (se 1 (by rfl) ⟨1846286, by rfl⟩ : syracuseStep 2461715 = 3692573) B3692573
theorem B3944483 : Blo 1640019 3944483 := bstep (se 1 (by rfl) ⟨2958362, by rfl⟩ : syracuseStep 3944483 = 5916725) B5916725
theorem B9343025 : Blo 1640019 9343025 := bstep (se 2 (by rfl) ⟨3503634, by rfl⟩ : syracuseStep 9343025 = 7007269) B7007269
theorem B2461745 : Blo 1640019 2461745 := bstep (se 2 (by rfl) ⟨923154, by rfl⟩ : syracuseStep 2461745 = 1846309) B1846309
theorem B18690101 : Blo 1640019 18690101 := bstep (se 5 (by rfl) ⟨876098, by rfl⟩ : syracuseStep 18690101 = 1752197) B1752197
theorem B2461763 : Blo 1640019 2461763 := bstep (se 1 (by rfl) ⟨1846322, by rfl⟩ : syracuseStep 2461763 = 3692645) B3692645
theorem B2461793 : Blo 1640019 2461793 := bstep (se 2 (by rfl) ⟨923172, by rfl⟩ : syracuseStep 2461793 = 1846345) B1846345
theorem B14020721 : Blo 1640019 14020721 := bstep (se 2 (by rfl) ⟨5257770, by rfl⟩ : syracuseStep 14020721 = 10515541) B10515541
theorem B2461811 : Blo 1640019 2461811 := bstep (se 1 (by rfl) ⟨1846358, by rfl⟩ : syracuseStep 2461811 = 3692717) B3692717
theorem B10662029 : Blo 1640019 10662029 := bstep (se 3 (by rfl) ⟨1999130, by rfl⟩ : syracuseStep 10662029 = 3998261) B3998261
theorem B2461841 : Blo 1640019 2461841 := bstep (se 2 (by rfl) ⟨923190, by rfl⟩ : syracuseStep 2461841 = 1846381) B1846381
theorem B2076835 : Blo 1640019 2076835 := bstep (se 1 (by rfl) ⟨1557626, by rfl⟩ : syracuseStep 2076835 = 3115253) B3115253
theorem B2461859 : Blo 1640019 2461859 := bstep (se 1 (by rfl) ⟨1846394, by rfl⟩ : syracuseStep 2461859 = 3692789) B3692789
theorem B2461889 : Blo 1640019 2461889 := bstep (se 2 (by rfl) ⟨923208, by rfl⟩ : syracuseStep 2461889 = 1846417) B1846417
theorem B2461907 : Blo 1640019 2461907 := bstep (se 1 (by rfl) ⟨1846430, by rfl⟩ : syracuseStep 2461907 = 3692861) B3692861
theorem B3690737 : Blo 1640019 3690737 := bstep (se 2 (by rfl) ⟨1384026, by rfl⟩ : syracuseStep 3690737 = 2768053) B2768053
theorem B2461937 : Blo 1640019 2461937 := bstep (se 2 (by rfl) ⟨923226, by rfl⟩ : syracuseStep 2461937 = 1846453) B1846453
theorem B3690755 : Blo 1640019 3690755 := bstep (se 1 (by rfl) ⟨2768066, by rfl⟩ : syracuseStep 3690755 = 5536133) B5536133
theorem B2076931 : Blo 1640019 2076931 := bstep (se 1 (by rfl) ⟨1557698, by rfl⟩ : syracuseStep 2076931 = 3115397) B3115397
theorem B2461955 : Blo 1640019 2461955 := bstep (se 1 (by rfl) ⟨1846466, by rfl⟩ : syracuseStep 2461955 = 3692933) B3692933
theorem B2461985 : Blo 1640019 2461985 := bstep (se 2 (by rfl) ⟨923244, by rfl⟩ : syracuseStep 2461985 = 1846489) B1846489
theorem B2462003 : Blo 1640019 2462003 := bstep (se 1 (by rfl) ⟨1846502, by rfl⟩ : syracuseStep 2462003 = 3693005) B3693005
theorem B3944771 : Blo 1640019 3944771 := bstep (se 1 (by rfl) ⟨2958578, by rfl⟩ : syracuseStep 3944771 = 5917157) B5917157
theorem B2462033 : Blo 1640019 2462033 := bstep (se 2 (by rfl) ⟨923262, by rfl⟩ : syracuseStep 2462033 = 1846525) B1846525
theorem B2462051 : Blo 1640019 2462051 := bstep (se 1 (by rfl) ⟨1846538, by rfl⟩ : syracuseStep 2462051 = 3693077) B3693077
theorem B19960177 : Blo 1640019 19960177 := bstep (se 2 (by rfl) ⟨7485066, by rfl⟩ : syracuseStep 19960177 = 14970133) B14970133
theorem B2462081 : Blo 1640019 2462081 := bstep (se 2 (by rfl) ⟨923280, by rfl⟩ : syracuseStep 2462081 = 1846561) B1846561
theorem B2462099 : Blo 1640019 2462099 := bstep (se 1 (by rfl) ⟨1846574, by rfl⟩ : syracuseStep 2462099 = 3693149) B3693149
theorem B2462129 : Blo 1640019 2462129 := bstep (se 2 (by rfl) ⟨923298, by rfl⟩ : syracuseStep 2462129 = 1846597) B1846597
theorem B2462147 : Blo 1640019 2462147 := bstep (se 1 (by rfl) ⟨1846610, by rfl⟩ : syracuseStep 2462147 = 3693221) B3693221
theorem B2462177 : Blo 1640019 2462177 := bstep (se 2 (by rfl) ⟨923316, by rfl⟩ : syracuseStep 2462177 = 1846633) B1846633
theorem B4436461 : Blo 1640019 4436461 := bstep (se 3 (by rfl) ⟨831836, by rfl⟩ : syracuseStep 4436461 = 1663673) B1663673
theorem B2462195 : Blo 1640019 2462195 := bstep (se 1 (by rfl) ⟨1846646, by rfl⟩ : syracuseStep 2462195 = 3693293) B3693293
theorem B3691025 : Blo 1640019 3691025 := bstep (se 2 (by rfl) ⟨1384134, by rfl⟩ : syracuseStep 3691025 = 2768269) B2768269
theorem B2462225 : Blo 1640019 2462225 := bstep (se 2 (by rfl) ⟨923334, by rfl⟩ : syracuseStep 2462225 = 1846669) B1846669
theorem B3691043 : Blo 1640019 3691043 := bstep (se 1 (by rfl) ⟨2768282, by rfl⟩ : syracuseStep 3691043 = 5536565) B5536565
theorem B2462243 : Blo 1640019 2462243 := bstep (se 1 (by rfl) ⟨1846682, by rfl⟩ : syracuseStep 2462243 = 3693365) B3693365
theorem B2462273 : Blo 1640019 2462273 := bstep (se 2 (by rfl) ⟨923352, by rfl⟩ : syracuseStep 2462273 = 1846705) B1846705
theorem B2462291 : Blo 1640019 2462291 := bstep (se 1 (by rfl) ⟨1846718, by rfl⟩ : syracuseStep 2462291 = 3693437) B3693437
theorem B6230627 : Blo 1640019 6230627 := bstep (se 1 (by rfl) ⟨4672970, by rfl⟩ : syracuseStep 6230627 = 9345941) B9345941
theorem B11825777 : Blo 1640019 11825777 := bstep (se 2 (by rfl) ⟨4434666, by rfl⟩ : syracuseStep 11825777 = 8869333) B8869333
theorem B6230641 : Blo 1640019 6230641 := bstep (se 2 (by rfl) ⟨2336490, by rfl⟩ : syracuseStep 6230641 = 4672981) B4672981
theorem B2462321 : Blo 1640019 2462321 := bstep (se 2 (by rfl) ⟨923370, by rfl⟩ : syracuseStep 2462321 = 1846741) B1846741
theorem B8311409 : Blo 1640019 8311409 := bstep (se 2 (by rfl) ⟨3116778, by rfl⟩ : syracuseStep 8311409 = 6233557) B6233557
theorem B2462339 : Blo 1640019 2462339 := bstep (se 1 (by rfl) ⟨1846754, by rfl⟩ : syracuseStep 2462339 = 3693509) B3693509
theorem B2462369 : Blo 1640019 2462369 := bstep (se 2 (by rfl) ⟨923388, by rfl⟩ : syracuseStep 2462369 = 1846777) B1846777
theorem B2462387 : Blo 1640019 2462387 := bstep (se 1 (by rfl) ⟨1846790, by rfl⟩ : syracuseStep 2462387 = 3693581) B3693581
theorem B8303309 : Blo 1640019 8303309 := bstep (se 3 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 8303309 = 3113741) B3113741
theorem B4674257 : Blo 1640019 4674257 := bstep (se 2 (by rfl) ⟨1752846, by rfl⟩ : syracuseStep 4674257 = 3505693) B3505693
theorem B2462417 : Blo 1640019 2462417 := bstep (se 2 (by rfl) ⟨923406, by rfl⟩ : syracuseStep 2462417 = 1846813) B1846813
theorem B2462435 : Blo 1640019 2462435 := bstep (se 1 (by rfl) ⟨1846826, by rfl⟩ : syracuseStep 2462435 = 3693653) B3693653
theorem B2077427 : Blo 1640019 2077427 := bstep (se 1 (by rfl) ⟨1558070, by rfl⟩ : syracuseStep 2077427 = 3116141) B3116141
theorem B2462465 : Blo 1640019 2462465 := bstep (se 2 (by rfl) ⟨923424, by rfl⟩ : syracuseStep 2462465 = 1846849) B1846849
theorem B2462483 : Blo 1640019 2462483 := bstep (se 1 (by rfl) ⟨1846862, by rfl⟩ : syracuseStep 2462483 = 3693725) B3693725
theorem B3691313 : Blo 1640019 3691313 := bstep (se 2 (by rfl) ⟨1384242, by rfl⟩ : syracuseStep 3691313 = 2768485) B2768485
theorem B2462513 : Blo 1640019 2462513 := bstep (se 2 (by rfl) ⟨923442, by rfl⟩ : syracuseStep 2462513 = 1846885) B1846885
theorem B3691331 : Blo 1640019 3691331 := bstep (se 1 (by rfl) ⟨2768498, by rfl⟩ : syracuseStep 3691331 = 5536997) B5536997
theorem B1971011 : Blo 1640019 1971011 := bstep (se 1 (by rfl) ⟨1478258, by rfl⟩ : syracuseStep 1971011 = 2956517) B2956517
theorem B2462531 : Blo 1640019 2462531 := bstep (se 1 (by rfl) ⟨1846898, by rfl⟩ : syracuseStep 2462531 = 3693797) B3693797
theorem B2495315 : Blo 1640019 2495315 := bstep (se 1 (by rfl) ⟨1871486, by rfl⟩ : syracuseStep 2495315 = 3742973) B3742973
theorem B2462561 : Blo 1640019 2462561 := bstep (se 2 (by rfl) ⟨923460, by rfl⟩ : syracuseStep 2462561 = 1846921) B1846921
theorem B3199843 : Blo 1640019 3199843 := bstep (se 1 (by rfl) ⟨2399882, by rfl⟩ : syracuseStep 3199843 = 4799765) B4799765
theorem B2462579 : Blo 1640019 2462579 := bstep (se 1 (by rfl) ⟨1846934, by rfl⟩ : syracuseStep 2462579 = 3693869) B3693869
theorem B2462609 : Blo 1640019 2462609 := bstep (se 2 (by rfl) ⟨923478, by rfl⟩ : syracuseStep 2462609 = 1846957) B1846957
theorem B2462627 : Blo 1640019 2462627 := bstep (se 1 (by rfl) ⟨1846970, by rfl⟩ : syracuseStep 2462627 = 3693941) B3693941
theorem B2462657 : Blo 1640019 2462657 := bstep (se 2 (by rfl) ⟨923496, by rfl⟩ : syracuseStep 2462657 = 1846993) B1846993
theorem B2462675 : Blo 1640019 2462675 := bstep (se 1 (by rfl) ⟨1847006, by rfl⟩ : syracuseStep 2462675 = 3694013) B3694013
theorem B2462705 : Blo 1640019 2462705 := bstep (se 2 (by rfl) ⟨923514, by rfl⟩ : syracuseStep 2462705 = 1847029) B1847029
theorem B2462723 : Blo 1640019 2462723 := bstep (se 1 (by rfl) ⟨1847042, by rfl⟩ : syracuseStep 2462723 = 3694085) B3694085
theorem B2528275 : Blo 1640019 2528275 := bstep (se 1 (by rfl) ⟨1896206, by rfl⟩ : syracuseStep 2528275 = 3792413) B3792413
theorem B2462753 : Blo 1640019 2462753 := bstep (se 2 (by rfl) ⟨923532, by rfl⟩ : syracuseStep 2462753 = 1847065) B1847065
theorem B10515491 : Blo 1640019 10515491 := bstep (se 1 (by rfl) ⟨7886618, by rfl⟩ : syracuseStep 10515491 = 15773237) B15773237
theorem B2462771 : Blo 1640019 2462771 := bstep (se 1 (by rfl) ⟨1847078, by rfl⟩ : syracuseStep 2462771 = 3694157) B3694157
theorem B3691601 : Blo 1640019 3691601 := bstep (se 2 (by rfl) ⟨1384350, by rfl⟩ : syracuseStep 3691601 = 2768701) B2768701
theorem B2462801 : Blo 1640019 2462801 := bstep (se 2 (by rfl) ⟨923550, by rfl⟩ : syracuseStep 2462801 = 1847101) B1847101
theorem B3691619 : Blo 1640019 3691619 := bstep (se 1 (by rfl) ⟨2768714, by rfl⟩ : syracuseStep 3691619 = 5537429) B5537429
theorem B2462819 : Blo 1640019 2462819 := bstep (se 1 (by rfl) ⟨1847114, by rfl⟩ : syracuseStep 2462819 = 3694229) B3694229
theorem B2462849 : Blo 1640019 2462849 := bstep (se 2 (by rfl) ⟨923568, by rfl⟩ : syracuseStep 2462849 = 1847137) B1847137
theorem B5616785 : Blo 1640019 5616785 := bstep (se 2 (by rfl) ⟨2106294, by rfl⟩ : syracuseStep 5616785 = 4212589) B4212589
theorem B2462867 : Blo 1640019 2462867 := bstep (se 1 (by rfl) ⟨1847150, by rfl⟩ : syracuseStep 2462867 = 3694301) B3694301
theorem B3503267 : Blo 1640019 3503267 := bstep (se 1 (by rfl) ⟨2627450, by rfl⟩ : syracuseStep 3503267 = 5254901) B5254901
theorem B2462897 : Blo 1640019 2462897 := bstep (se 2 (by rfl) ⟨923586, by rfl⟩ : syracuseStep 2462897 = 1847173) B1847173
theorem B2462915 : Blo 1640019 2462915 := bstep (se 1 (by rfl) ⟨1847186, by rfl⟩ : syracuseStep 2462915 = 3694373) B3694373
theorem B2462945 : Blo 1640019 2462945 := bstep (se 2 (by rfl) ⟨923604, by rfl⟩ : syracuseStep 2462945 = 1847209) B1847209
theorem B2462963 : Blo 1640019 2462963 := bstep (se 1 (by rfl) ⟨1847222, by rfl⟩ : syracuseStep 2462963 = 3694445) B3694445
theorem B2462993 : Blo 1640019 2462993 := bstep (se 2 (by rfl) ⟨923622, by rfl⟩ : syracuseStep 2462993 = 1847245) B1847245
theorem B2495777 : Blo 1640019 2495777 := bstep (se 2 (by rfl) ⟨935916, by rfl⟩ : syracuseStep 2495777 = 1871833) B1871833
theorem B4437283 : Blo 1640019 4437283 := bstep (se 1 (by rfl) ⟨3327962, by rfl⟩ : syracuseStep 4437283 = 6655925) B6655925
theorem B2463011 : Blo 1640019 2463011 := bstep (se 1 (by rfl) ⟨1847258, by rfl⟩ : syracuseStep 2463011 = 3694517) B3694517
theorem B3740995 : Blo 1640019 3740995 := bstep (se 1 (by rfl) ⟨2805746, by rfl⟩ : syracuseStep 3740995 = 5611493) B5611493
theorem B5256515 : Blo 1640019 5256515 := bstep (se 1 (by rfl) ⟨3942386, by rfl⟩ : syracuseStep 5256515 = 7884773) B7884773
theorem B4437325 : Blo 1640019 4437325 := bstep (se 3 (by rfl) ⟨831998, by rfl⟩ : syracuseStep 4437325 = 1663997) B1663997
theorem B3691889 : Blo 1640019 3691889 := bstep (se 2 (by rfl) ⟨1384458, by rfl⟩ : syracuseStep 3691889 = 2768917) B2768917
theorem B5535107 : Blo 1640019 5535107 := bstep (se 1 (by rfl) ⟨4151330, by rfl⟩ : syracuseStep 5535107 = 8302661) B8302661
theorem B3691907 : Blo 1640019 3691907 := bstep (se 1 (by rfl) ⟨2768930, by rfl⟩ : syracuseStep 3691907 = 5537861) B5537861
theorem B2078131 : Blo 1640019 2078131 := bstep (se 1 (by rfl) ⟨1558598, by rfl⟩ : syracuseStep 2078131 = 3117197) B3117197
theorem B2627009 : Blo 1640019 2627009 := bstep (se 2 (by rfl) ⟨985128, by rfl⟩ : syracuseStep 2627009 = 1970257) B1970257
theorem B9344483 : Blo 1640019 9344483 := bstep (se 1 (by rfl) ⟨7008362, by rfl⟩ : syracuseStep 9344483 = 14016725) B14016725
theorem B1971683 : Blo 1640019 1971683 := bstep (se 1 (by rfl) ⟨1478762, by rfl⟩ : syracuseStep 1971683 = 2957525) B2957525
theorem B3503729 : Blo 1640019 3503729 := bstep (se 2 (by rfl) ⟨1313898, by rfl⟩ : syracuseStep 3503729 = 2627797) B2627797
theorem B23656049 : Blo 1640019 23656049 := bstep (se 2 (by rfl) ⟨8871018, by rfl⟩ : syracuseStep 23656049 = 17742037) B17742037
theorem B6657677 : Blo 1640019 6657677 := bstep (se 3 (by rfl) ⟨1248314, by rfl⟩ : syracuseStep 6657677 = 2496629) B2496629
theorem B5535377 : Blo 1640019 5535377 := bstep (se 2 (by rfl) ⟨2075766, by rfl⟩ : syracuseStep 5535377 = 4151533) B4151533
theorem B3692177 : Blo 1640019 3692177 := bstep (se 2 (by rfl) ⟨1384566, by rfl⟩ : syracuseStep 3692177 = 2769133) B2769133
theorem B3692195 : Blo 1640019 3692195 := bstep (se 1 (by rfl) ⟨2769146, by rfl⟩ : syracuseStep 3692195 = 5538293) B5538293
theorem B3692465 : Blo 1640019 3692465 := bstep (se 2 (by rfl) ⟨1384674, by rfl⟩ : syracuseStep 3692465 = 2769349) B2769349
theorem B7010225 : Blo 1640019 7010225 := bstep (se 2 (by rfl) ⟨2628834, by rfl⟩ : syracuseStep 7010225 = 5257669) B5257669
theorem B3692483 : Blo 1640019 3692483 := bstep (se 1 (by rfl) ⟨2769362, by rfl⟩ : syracuseStep 3692483 = 5538725) B5538725
theorem B6232099 : Blo 1640019 6232099 := bstep (se 1 (by rfl) ⟨4674074, by rfl⟩ : syracuseStep 6232099 = 9348149) B9348149
theorem B4675715 : Blo 1640019 4675715 := bstep (se 1 (by rfl) ⟨3506786, by rfl⟩ : syracuseStep 4675715 = 7013573) B7013573
theorem B5257361 : Blo 1640019 5257361 := bstep (se 2 (by rfl) ⟨1971510, by rfl⟩ : syracuseStep 5257361 = 3943021) B3943021
theorem B5535917 : Blo 1640019 5535917 := bstep (se 3 (by rfl) ⟨1037984, by rfl⟩ : syracuseStep 5535917 = 2075969) B2075969
theorem B3692753 : Blo 1640019 3692753 := bstep (se 2 (by rfl) ⟨1384782, by rfl⟩ : syracuseStep 3692753 = 2769565) B2769565
theorem B5535971 : Blo 1640019 5535971 := bstep (se 1 (by rfl) ⟨4151978, by rfl⟩ : syracuseStep 5535971 = 8303957) B8303957
theorem B3692771 : Blo 1640019 3692771 := bstep (se 1 (by rfl) ⟨2769578, by rfl⟩ : syracuseStep 3692771 = 5539157) B5539157
theorem B21027185 : Blo 1640019 21027185 := bstep (se 2 (by rfl) ⟨7885194, by rfl⟩ : syracuseStep 21027185 = 15770389) B15770389
theorem B2808209 : Blo 1640019 2808209 := bstep (se 2 (by rfl) ⟨1053078, by rfl⟩ : syracuseStep 2808209 = 2106157) B2106157
theorem B5536241 : Blo 1640019 5536241 := bstep (se 2 (by rfl) ⟨2076090, by rfl⟩ : syracuseStep 5536241 = 4152181) B4152181
theorem B3693041 : Blo 1640019 3693041 := bstep (se 2 (by rfl) ⟨1384890, by rfl⟩ : syracuseStep 3693041 = 2769781) B2769781
theorem B3693059 : Blo 1640019 3693059 := bstep (se 1 (by rfl) ⟨2769794, by rfl⟩ : syracuseStep 3693059 = 5539589) B5539589
theorem B2955811 : Blo 1640019 2955811 := bstep (se 1 (by rfl) ⟨2216858, by rfl⟩ : syracuseStep 2955811 = 4433717) B4433717
theorem B4151857 : Blo 1640019 4151857 := bstep (se 2 (by rfl) ⟨1556946, by rfl⟩ : syracuseStep 4151857 = 3113893) B3113893
theorem B12458609 : Blo 1640019 12458609 := bstep (se 2 (by rfl) ⟨4671978, by rfl⟩ : syracuseStep 12458609 = 9343957) B9343957
theorem B2767601 : Blo 1640019 2767601 := bstep (se 2 (by rfl) ⟨1037850, by rfl⟩ : syracuseStep 2767601 = 2075701) B2075701
theorem B3742481 : Blo 1640019 3742481 := bstep (se 2 (by rfl) ⟨1403430, by rfl⟩ : syracuseStep 3742481 = 2806861) B2806861
theorem B3693329 : Blo 1640019 3693329 := bstep (se 2 (by rfl) ⟨1384998, by rfl⟩ : syracuseStep 3693329 = 2769997) B2769997
theorem B3742499 : Blo 1640019 3742499 := bstep (se 1 (by rfl) ⟨2806874, by rfl⟩ : syracuseStep 3742499 = 5613749) B5613749
theorem B3693347 : Blo 1640019 3693347 := bstep (se 1 (by rfl) ⟨2770010, by rfl⟩ : syracuseStep 3693347 = 5540021) B5540021
theorem B2530099 : Blo 1640019 2530099 := bstep (se 1 (by rfl) ⟨1897574, by rfl⟩ : syracuseStep 2530099 = 3795149) B3795149
theorem B4152131 : Blo 1640019 4152131 := bstep (se 1 (by rfl) ⟨3114098, by rfl⟩ : syracuseStep 4152131 = 6228197) B6228197
theorem B3554147 : Blo 1640019 3554147 := bstep (se 1 (by rfl) ⟨2665610, by rfl⟩ : syracuseStep 3554147 = 5331221) B5331221
theorem B2767729 : Blo 1640019 2767729 := bstep (se 2 (by rfl) ⟨1037898, by rfl⟩ : syracuseStep 2767729 = 2075797) B2075797
theorem B3505027 : Blo 1640019 3505027 := bstep (se 1 (by rfl) ⟨2628770, by rfl⟩ : syracuseStep 3505027 = 5257541) B5257541
theorem B2767763 : Blo 1640019 2767763 := bstep (se 1 (by rfl) ⟨2075822, by rfl⟩ : syracuseStep 2767763 = 4151645) B4151645
theorem B1752035 : Blo 1640019 1752035 := bstep (se 1 (by rfl) ⟨1314026, by rfl⟩ : syracuseStep 1752035 = 2628053) B2628053
theorem B16833521 : Blo 1640019 16833521 := bstep (se 2 (by rfl) ⟨6312570, by rfl⟩ : syracuseStep 16833521 = 12625141) B12625141
theorem B10517489 : Blo 1640019 10517489 := bstep (se 2 (by rfl) ⟨3944058, by rfl⟩ : syracuseStep 10517489 = 7888117) B7888117
theorem B4152323 : Blo 1640019 4152323 := bstep (se 1 (by rfl) ⟨3114242, by rfl⟩ : syracuseStep 4152323 = 6228485) B6228485
theorem B11222021 : Blo 1640019 11222021 := bstep (se 4 (by rfl) ⟨1052064, by rfl⟩ : syracuseStep 11222021 = 2104129) B2104129
theorem B5536781 : Blo 1640019 5536781 := bstep (se 3 (by rfl) ⟨1038146, by rfl⟩ : syracuseStep 5536781 = 2076293) B2076293
theorem B2767891 : Blo 1640019 2767891 := bstep (se 1 (by rfl) ⟨2075918, by rfl⟩ : syracuseStep 2767891 = 4151837) B4151837
theorem B3693617 : Blo 1640019 3693617 := bstep (se 2 (by rfl) ⟨1385106, by rfl⟩ : syracuseStep 3693617 = 2770213) B2770213
theorem B5536835 : Blo 1640019 5536835 := bstep (se 1 (by rfl) ⟨4152626, by rfl⟩ : syracuseStep 5536835 = 8305253) B8305253
theorem B3693635 : Blo 1640019 3693635 := bstep (se 1 (by rfl) ⟨2770226, by rfl⟩ : syracuseStep 3693635 = 5540453) B5540453
theorem B3505283 : Blo 1640019 3505283 := bstep (se 1 (by rfl) ⟨2628962, by rfl⟩ : syracuseStep 3505283 = 5257925) B5257925
theorem B2768033 : Blo 1640019 2768033 := bstep (se 2 (by rfl) ⟨1038012, by rfl⟩ : syracuseStep 2768033 = 2076025) B2076025
theorem B4988099 : Blo 1640019 4988099 := bstep (se 1 (by rfl) ⟨3741074, by rfl⟩ : syracuseStep 4988099 = 7482149) B7482149
theorem B7888099 : Blo 1640019 7888099 := bstep (se 1 (by rfl) ⟨5916074, by rfl⟩ : syracuseStep 7888099 = 11832149) B11832149
theorem B2768161 : Blo 1640019 2768161 := bstep (se 2 (by rfl) ⟨1038060, by rfl⟩ : syracuseStep 2768161 = 2076121) B2076121
theorem B2768195 : Blo 1640019 2768195 := bstep (se 1 (by rfl) ⟨2076146, by rfl⟩ : syracuseStep 2768195 = 4152293) B4152293
theorem B9346373 : Blo 1640019 9346373 := bstep (se 4 (by rfl) ⟨876222, by rfl⟩ : syracuseStep 9346373 = 1752445) B1752445
theorem B5537105 : Blo 1640019 5537105 := bstep (se 2 (by rfl) ⟨2076414, by rfl⟩ : syracuseStep 5537105 = 4152829) B4152829
theorem B3693905 : Blo 1640019 3693905 := bstep (se 2 (by rfl) ⟨1385214, by rfl⟩ : syracuseStep 3693905 = 2770429) B2770429
theorem B3693923 : Blo 1640019 3693923 := bstep (se 1 (by rfl) ⟨2770442, by rfl⟩ : syracuseStep 3693923 = 5540885) B5540885
theorem B2629027 : Blo 1640019 2629027 := bstep (se 1 (by rfl) ⟨1971770, by rfl⟩ : syracuseStep 2629027 = 3943541) B3943541
theorem B2768323 : Blo 1640019 2768323 := bstep (se 1 (by rfl) ⟨2076242, by rfl⟩ : syracuseStep 2768323 = 4152485) B4152485
theorem B18701765 : Blo 1640019 18701765 := bstep (se 4 (by rfl) ⟨1753290, by rfl⟩ : syracuseStep 18701765 = 3506581) B3506581
theorem B2629091 : Blo 1640019 2629091 := bstep (se 1 (by rfl) ⟨1971818, by rfl⟩ : syracuseStep 2629091 = 3943637) B3943637
theorem B4734509 : Blo 1640019 4734509 := bstep (se 3 (by rfl) ⟨887720, by rfl⟩ : syracuseStep 4734509 = 1775441) B1775441
theorem B8306225 : Blo 1640019 8306225 := bstep (se 2 (by rfl) ⟨3114834, by rfl⟩ : syracuseStep 8306225 = 6229669) B6229669
theorem B7011917 : Blo 1640019 7011917 := bstep (se 3 (by rfl) ⟨1314734, by rfl⟩ : syracuseStep 7011917 = 2629469) B2629469
theorem B2768465 : Blo 1640019 2768465 := bstep (se 2 (by rfl) ⟨1038174, by rfl⟩ : syracuseStep 2768465 = 2076349) B2076349
theorem B3694193 : Blo 1640019 3694193 := bstep (se 2 (by rfl) ⟨1385322, by rfl⟩ : syracuseStep 3694193 = 2770645) B2770645
theorem B3694211 : Blo 1640019 3694211 := bstep (se 1 (by rfl) ⟨2770658, by rfl⟩ : syracuseStep 3694211 = 5541317) B5541317
theorem B2768593 : Blo 1640019 2768593 := bstep (se 2 (by rfl) ⟨1038222, by rfl⟩ : syracuseStep 2768593 = 2076445) B2076445
theorem B1752787 : Blo 1640019 1752787 := bstep (se 1 (by rfl) ⟨1314590, by rfl⟩ : syracuseStep 1752787 = 2629181) B2629181
theorem B2768627 : Blo 1640019 2768627 := bstep (se 1 (by rfl) ⟨2076470, by rfl⟩ : syracuseStep 2768627 = 4152941) B4152941
theorem B5537645 : Blo 1640019 5537645 := bstep (se 3 (by rfl) ⟨1038308, by rfl⟩ : syracuseStep 5537645 = 2076617) B2076617
theorem B2768755 : Blo 1640019 2768755 := bstep (se 1 (by rfl) ⟨2076566, by rfl⟩ : syracuseStep 2768755 = 4153133) B4153133
theorem B14401421 : Blo 1640019 14401421 := bstep (se 3 (by rfl) ⟨2700266, by rfl⟩ : syracuseStep 14401421 = 5400533) B5400533
theorem B3694481 : Blo 1640019 3694481 := bstep (se 2 (by rfl) ⟨1385430, by rfl⟩ : syracuseStep 3694481 = 2770861) B2770861
theorem B5537699 : Blo 1640019 5537699 := bstep (se 1 (by rfl) ⟨4153274, by rfl⟩ : syracuseStep 5537699 = 8306549) B8306549
theorem B3694499 : Blo 1640019 3694499 := bstep (se 1 (by rfl) ⟨2770874, by rfl⟩ : syracuseStep 3694499 = 5541749) B5541749
theorem B5259181 : Blo 1640019 5259181 := bstep (se 3 (by rfl) ⟨986096, by rfl⟩ : syracuseStep 5259181 = 1972193) B1972193
theorem B4153265 : Blo 1640019 4153265 := bstep (se 2 (by rfl) ⟨1557474, by rfl⟩ : syracuseStep 4153265 = 3114949) B3114949
theorem B28032965 : Blo 1640019 28032965 := bstep (se 4 (by rfl) ⟨2628090, by rfl⟩ : syracuseStep 28032965 = 5256181) B5256181
theorem B4153315 : Blo 1640019 4153315 := bstep (se 1 (by rfl) ⟨3114986, by rfl⟩ : syracuseStep 4153315 = 6229973) B6229973
theorem B29925389 : Blo 1640019 29925389 := bstep (se 3 (by rfl) ⟨5611010, by rfl⟩ : syracuseStep 29925389 = 11222021) B11222021
theorem B2629655 : Blo 1640019 2629655 := bstep (se 1 (by rfl) ⟨1972241, by rfl⟩ : syracuseStep 2629655 = 3944483) B3944483
theorem B12460067 : Blo 1640019 12460067 := bstep (se 1 (by rfl) ⟨9345050, by rfl⟩ : syracuseStep 12460067 = 18690101) B18690101
theorem B2768971 : Blo 1640019 2768971 := bstep (se 1 (by rfl) ⟨2076728, by rfl⟩ : syracuseStep 2768971 = 4153457) B4153457
theorem B9347147 : Blo 1640019 9347147 := bstep (se 1 (by rfl) ⟨7010360, by rfl⟩ : syracuseStep 9347147 = 14020721) B14020721
theorem B8872037 : Blo 1640019 8872037 := bstep (se 4 (by rfl) ⟨831753, by rfl⟩ : syracuseStep 8872037 = 1663507) B1663507
theorem B2629847 : Blo 1640019 2629847 := bstep (se 1 (by rfl) ⟨1972385, by rfl⟩ : syracuseStep 2629847 = 3944771) B3944771
theorem B2769113 : Blo 1640019 2769113 := bstep (se 2 (by rfl) ⟨1038417, by rfl⟩ : syracuseStep 2769113 = 2076835) B2076835
theorem B2769241 : Blo 1640019 2769241 := bstep (se 2 (by rfl) ⟨1038465, by rfl⟩ : syracuseStep 2769241 = 2076931) B2076931
theorem B4153751 : Blo 1640019 4153751 := bstep (se 1 (by rfl) ⟨3115313, by rfl⟩ : syracuseStep 4153751 = 6230627) B6230627
theorem B4735435 : Blo 1640019 4735435 := bstep (se 1 (by rfl) ⟨3551576, by rfl⟩ : syracuseStep 4735435 = 7103153) B7103153
theorem B1663543 : Blo 1640019 1663543 := bstep (se 1 (by rfl) ⟨1247657, by rfl⟩ : syracuseStep 1663543 = 2495315) B2495315
theorem B10519105 : Blo 1640019 10519105 := bstep (se 2 (by rfl) ⟨3944664, by rfl⟩ : syracuseStep 10519105 = 7889329) B7889329
theorem B3506753 : Blo 1640019 3506753 := bstep (se 2 (by rfl) ⟨1315032, by rfl⟩ : syracuseStep 3506753 = 2630065) B2630065
theorem B21037643 : Blo 1640019 21037643 := bstep (se 1 (by rfl) ⟨15778232, by rfl⟩ : syracuseStep 21037643 = 31556465) B31556465
theorem B7889501 : Blo 1640019 7889501 := bstep (se 3 (by rfl) ⟨1479281, by rfl⟩ : syracuseStep 7889501 = 2958563) B2958563
theorem B5915281 : Blo 1640019 5915281 := bstep (se 2 (by rfl) ⟨2218230, by rfl⟩ : syracuseStep 5915281 = 4436461) B4436461
theorem B5538455 : Blo 1640019 5538455 := bstep (se 1 (by rfl) ⟨4153841, by rfl⟩ : syracuseStep 5538455 = 8307683) B8307683
theorem B3941081 : Blo 1640019 3941081 := bstep (se 2 (by rfl) ⟨1477905, by rfl⟩ : syracuseStep 3941081 = 2955811) B2955811
theorem B3744523 : Blo 1640019 3744523 := bstep (se 1 (by rfl) ⟨2808392, by rfl⟩ : syracuseStep 3744523 = 5616785) B5616785
theorem B2335511 : Blo 1640019 2335511 := bstep (se 1 (by rfl) ⟨1751633, by rfl⟩ : syracuseStep 2335511 = 3503267) B3503267
theorem B8307521 : Blo 1640019 8307521 := bstep (se 2 (by rfl) ⟨3115320, by rfl⟩ : syracuseStep 8307521 = 6230641) B6230641
theorem B14017373 : Blo 1640019 14017373 := bstep (se 3 (by rfl) ⟨2628257, by rfl⟩ : syracuseStep 14017373 = 5256515) B5256515
theorem B2769815 : Blo 1640019 2769815 := bstep (se 1 (by rfl) ⟨2077361, by rfl⟩ : syracuseStep 2769815 = 4154723) B4154723
theorem B7013299 : Blo 1640019 7013299 := bstep (se 1 (by rfl) ⟨5259974, by rfl⟩ : syracuseStep 7013299 = 10519949) B10519949
theorem B2769943 : Blo 1640019 2769943 := bstep (se 1 (by rfl) ⟨2077457, by rfl⟩ : syracuseStep 2769943 = 4154915) B4154915
theorem B7488557 : Blo 1640019 7488557 := bstep (se 3 (by rfl) ⟨1404104, by rfl⟩ : syracuseStep 7488557 = 2808209) B2808209
theorem B50521157 : Blo 1640019 50521157 := bstep (se 4 (by rfl) ⟨4736358, by rfl⟩ : syracuseStep 50521157 = 9472717) B9472717
theorem B2335819 : Blo 1640019 2335819 := bstep (se 1 (by rfl) ⟨1751864, by rfl⟩ : syracuseStep 2335819 = 3503729) B3503729
theorem B15770699 : Blo 1640019 15770699 := bstep (se 1 (by rfl) ⟨11828024, by rfl⟩ : syracuseStep 15770699 = 23656049) B23656049
theorem B5538995 : Blo 1640019 5538995 := bstep (se 1 (by rfl) ⟨4154246, by rfl⟩ : syracuseStep 5538995 = 8308493) B8308493
theorem B170583221 : Blo 1640019 170583221 := bstep (se 5 (by rfl) ⟨7996088, by rfl⟩ : syracuseStep 170583221 = 15992177) B15992177
theorem B4154561 : Blo 1640019 4154561 := bstep (se 2 (by rfl) ⟨1557960, by rfl⟩ : syracuseStep 4154561 = 3115921) B3115921
theorem B3114227 : Blo 1640019 3114227 := bstep (se 1 (by rfl) ⟨2335670, by rfl⟩ : syracuseStep 3114227 = 4671341) B4671341
theorem B34604333 : Blo 1640019 34604333 := bstep (se 3 (by rfl) ⟨6488312, by rfl⟩ : syracuseStep 34604333 = 12976625) B12976625
theorem B3114379 : Blo 1640019 3114379 := bstep (se 1 (by rfl) ⟨2335784, by rfl⟩ : syracuseStep 3114379 = 4671569) B4671569
theorem B5539265 : Blo 1640019 5539265 := bstep (se 2 (by rfl) ⟨2077224, by rfl⟩ : syracuseStep 5539265 = 4154449) B4154449
theorem B12625357 : Blo 1640019 12625357 := bstep (se 3 (by rfl) ⟨2367254, by rfl⟩ : syracuseStep 12625357 = 4734509) B4734509
theorem B14018123 : Blo 1640019 14018123 := bstep (se 1 (by rfl) ⟨10513592, by rfl⟩ : syracuseStep 14018123 = 21027185) B21027185
theorem B1640023 : Blo 1640019 1640023 := bstep (se 1 (by rfl) ⟨1230017, by rfl⟩ : syracuseStep 1640023 = 2460035) B2460035
theorem B13493861 : Blo 1640019 13493861 := bstep (se 4 (by rfl) ⟨1265049, by rfl⟩ : syracuseStep 13493861 = 2530099) B2530099
theorem B1640043 : Blo 1640019 1640043 := bstep (se 1 (by rfl) ⟨1230032, by rfl⟩ : syracuseStep 1640043 = 2460065) B2460065
theorem B1640055 : Blo 1640019 1640055 := bstep (se 1 (by rfl) ⟨1230041, by rfl⟩ : syracuseStep 1640055 = 2460083) B2460083
theorem B1640075 : Blo 1640019 1640075 := bstep (se 1 (by rfl) ⟨1230056, by rfl⟩ : syracuseStep 1640075 = 2460113) B2460113
theorem B2770571 : Blo 1640019 2770571 := bstep (se 1 (by rfl) ⟨2077928, by rfl⟩ : syracuseStep 2770571 = 4155857) B4155857
theorem B1640087 : Blo 1640019 1640087 := bstep (se 1 (by rfl) ⟨1230065, by rfl⟩ : syracuseStep 1640087 = 2460131) B2460131
theorem B1640107 : Blo 1640019 1640107 := bstep (se 1 (by rfl) ⟨1230080, by rfl⟩ : syracuseStep 1640107 = 2460161) B2460161
theorem B1640119 : Blo 1640019 1640119 := bstep (se 1 (by rfl) ⟨1230089, by rfl⟩ : syracuseStep 1640119 = 2460179) B2460179
theorem B1640139 : Blo 1640019 1640139 := bstep (se 1 (by rfl) ⟨1230104, by rfl⟩ : syracuseStep 1640139 = 2460209) B2460209
theorem B1640151 : Blo 1640019 1640151 := bstep (se 1 (by rfl) ⟨1230113, by rfl⟩ : syracuseStep 1640151 = 2460227) B2460227
theorem B3114713 : Blo 1640019 3114713 := bstep (se 2 (by rfl) ⟨1168017, by rfl⟩ : syracuseStep 3114713 = 2336035) B2336035
theorem B4155097 : Blo 1640019 4155097 := bstep (se 2 (by rfl) ⟨1558161, by rfl⟩ : syracuseStep 4155097 = 3116323) B3116323
theorem B5916377 : Blo 1640019 5916377 := bstep (se 2 (by rfl) ⟨2218641, by rfl⟩ : syracuseStep 5916377 = 4437283) B4437283
theorem B1640171 : Blo 1640019 1640171 := bstep (se 1 (by rfl) ⟨1230128, by rfl⟩ : syracuseStep 1640171 = 2460257) B2460257
theorem B1640183 : Blo 1640019 1640183 := bstep (se 1 (by rfl) ⟨1230137, by rfl⟩ : syracuseStep 1640183 = 2460275) B2460275
theorem B1640203 : Blo 1640019 1640203 := bstep (se 1 (by rfl) ⟨1230152, by rfl⟩ : syracuseStep 1640203 = 2460305) B2460305
theorem B2770699 : Blo 1640019 2770699 := bstep (se 1 (by rfl) ⟨2078024, by rfl⟩ : syracuseStep 2770699 = 4156049) B4156049
theorem B1640215 : Blo 1640019 1640215 := bstep (se 1 (by rfl) ⟨1230161, by rfl⟩ : syracuseStep 1640215 = 2460323) B2460323
theorem B1640235 : Blo 1640019 1640235 := bstep (se 1 (by rfl) ⟨1230176, by rfl⟩ : syracuseStep 1640235 = 2460353) B2460353
theorem B1640247 : Blo 1640019 1640247 := bstep (se 1 (by rfl) ⟨1230185, by rfl⟩ : syracuseStep 1640247 = 2460371) B2460371
theorem B1845067 : Blo 1640019 1845067 := bstep (se 1 (by rfl) ⟨1383800, by rfl⟩ : syracuseStep 1845067 = 2767601) B2767601
theorem B1640267 : Blo 1640019 1640267 := bstep (se 1 (by rfl) ⟨1230200, by rfl⟩ : syracuseStep 1640267 = 2460401) B2460401
theorem B6653771 : Blo 1640019 6653771 := bstep (se 1 (by rfl) ⟨4990328, by rfl⟩ : syracuseStep 6653771 = 9980657) B9980657
theorem B1640279 : Blo 1640019 1640279 := bstep (se 1 (by rfl) ⟨1230209, by rfl⟩ : syracuseStep 1640279 = 2460419) B2460419
theorem B39929699 : Blo 1640019 39929699 := bstep (se 1 (by rfl) ⟨29947274, by rfl⟩ : syracuseStep 39929699 = 59894549) B59894549
theorem B17065829 : Blo 1640019 17065829 := bstep (se 4 (by rfl) ⟨1599921, by rfl⟩ : syracuseStep 17065829 = 3199843) B3199843
theorem B1640299 : Blo 1640019 1640299 := bstep (se 1 (by rfl) ⟨1230224, by rfl⟩ : syracuseStep 1640299 = 2460449) B2460449
theorem B1640311 : Blo 1640019 1640311 := bstep (se 1 (by rfl) ⟨1230233, by rfl⟩ : syracuseStep 1640311 = 2460467) B2460467
theorem B1640331 : Blo 1640019 1640331 := bstep (se 1 (by rfl) ⟨1230248, by rfl⟩ : syracuseStep 1640331 = 2460497) B2460497
theorem B1640343 : Blo 1640019 1640343 := bstep (se 1 (by rfl) ⟨1230257, by rfl⟩ : syracuseStep 1640343 = 2460515) B2460515
theorem B2369431 : Blo 1640019 2369431 := bstep (se 1 (by rfl) ⟨1777073, by rfl⟩ : syracuseStep 2369431 = 3554147) B3554147
theorem B2770841 : Blo 1640019 2770841 := bstep (se 2 (by rfl) ⟨1039065, by rfl⟩ : syracuseStep 2770841 = 2078131) B2078131
theorem B1640363 : Blo 1640019 1640363 := bstep (se 1 (by rfl) ⟨1230272, by rfl⟩ : syracuseStep 1640363 = 2460545) B2460545
theorem B31524785 : Blo 1640019 31524785 := bstep (se 2 (by rfl) ⟨11821794, by rfl⟩ : syracuseStep 31524785 = 23643589) B23643589
theorem B1845175 : Blo 1640019 1845175 := bstep (se 1 (by rfl) ⟨1383881, by rfl⟩ : syracuseStep 1845175 = 2767763) B2767763
theorem B1640375 : Blo 1640019 1640375 := bstep (se 1 (by rfl) ⟨1230281, by rfl⟩ : syracuseStep 1640375 = 2460563) B2460563
theorem B1640395 : Blo 1640019 1640395 := bstep (se 1 (by rfl) ⟨1230296, by rfl⟩ : syracuseStep 1640395 = 2460593) B2460593
theorem B1640407 : Blo 1640019 1640407 := bstep (se 1 (by rfl) ⟨1230305, by rfl⟩ : syracuseStep 1640407 = 2460611) B2460611
theorem B5539805 : Blo 1640019 5539805 := bstep (se 3 (by rfl) ⟨1038713, by rfl⟩ : syracuseStep 5539805 = 2077427) B2077427
theorem B1640427 : Blo 1640019 1640427 := bstep (se 1 (by rfl) ⟨1230320, by rfl⟩ : syracuseStep 1640427 = 2460641) B2460641
theorem B1640439 : Blo 1640019 1640439 := bstep (se 1 (by rfl) ⟨1230329, by rfl⟩ : syracuseStep 1640439 = 2460659) B2460659
theorem B1640459 : Blo 1640019 1640459 := bstep (se 1 (by rfl) ⟨1230344, by rfl⟩ : syracuseStep 1640459 = 2460689) B2460689
theorem B1640471 : Blo 1640019 1640471 := bstep (se 1 (by rfl) ⟨1230353, by rfl⟩ : syracuseStep 1640471 = 2460707) B2460707
theorem B1640491 : Blo 1640019 1640491 := bstep (se 1 (by rfl) ⟨1230368, by rfl⟩ : syracuseStep 1640491 = 2460737) B2460737
theorem B9979949 : Blo 1640019 9979949 := bstep (se 3 (by rfl) ⟨1871240, by rfl⟩ : syracuseStep 9979949 = 3742481) B3742481
theorem B1640503 : Blo 1640019 1640503 := bstep (se 1 (by rfl) ⟨1230377, by rfl⟩ : syracuseStep 1640503 = 2460755) B2460755
theorem B1640523 : Blo 1640019 1640523 := bstep (se 1 (by rfl) ⟨1230392, by rfl⟩ : syracuseStep 1640523 = 2460785) B2460785
theorem B1640535 : Blo 1640019 1640535 := bstep (se 1 (by rfl) ⟨1230401, by rfl⟩ : syracuseStep 1640535 = 2460803) B2460803
theorem B2336855 : Blo 1640019 2336855 := bstep (se 1 (by rfl) ⟨1752641, by rfl⟩ : syracuseStep 2336855 = 3505283) B3505283
theorem B1845355 : Blo 1640019 1845355 := bstep (se 1 (by rfl) ⟨1384016, by rfl⟩ : syracuseStep 1845355 = 2768033) B2768033
theorem B1640555 : Blo 1640019 1640555 := bstep (se 1 (by rfl) ⟨1230416, by rfl⟩ : syracuseStep 1640555 = 2460833) B2460833
theorem B1640567 : Blo 1640019 1640567 := bstep (se 1 (by rfl) ⟨1230425, by rfl⟩ : syracuseStep 1640567 = 2460851) B2460851
theorem B7489667 : Blo 1640019 7489667 := bstep (se 1 (by rfl) ⟨5617250, by rfl⟩ : syracuseStep 7489667 = 11234501) B11234501
theorem B1640587 : Blo 1640019 1640587 := bstep (se 1 (by rfl) ⟨1230440, by rfl⟩ : syracuseStep 1640587 = 2460881) B2460881
theorem B1640599 : Blo 1640019 1640599 := bstep (se 1 (by rfl) ⟨1230449, by rfl⟩ : syracuseStep 1640599 = 2460899) B2460899
theorem B1640619 : Blo 1640019 1640619 := bstep (se 1 (by rfl) ⟨1230464, by rfl⟩ : syracuseStep 1640619 = 2460929) B2460929
theorem B1640631 : Blo 1640019 1640631 := bstep (se 1 (by rfl) ⟨1230473, by rfl⟩ : syracuseStep 1640631 = 2460947) B2460947
theorem B1640651 : Blo 1640019 1640651 := bstep (se 1 (by rfl) ⟨1230488, by rfl⟩ : syracuseStep 1640651 = 2460977) B2460977
theorem B7489739 : Blo 1640019 7489739 := bstep (se 1 (by rfl) ⟨5617304, by rfl⟩ : syracuseStep 7489739 = 11234609) B11234609
theorem B1845463 : Blo 1640019 1845463 := bstep (se 1 (by rfl) ⟨1384097, by rfl⟩ : syracuseStep 1845463 = 2768195) B2768195
theorem B1640663 : Blo 1640019 1640663 := bstep (se 1 (by rfl) ⟨1230497, by rfl⟩ : syracuseStep 1640663 = 2460995) B2460995
theorem B1640683 : Blo 1640019 1640683 := bstep (se 1 (by rfl) ⟨1230512, by rfl⟩ : syracuseStep 1640683 = 2461025) B2461025
theorem B1640695 : Blo 1640019 1640695 := bstep (se 1 (by rfl) ⟨1230521, by rfl⟩ : syracuseStep 1640695 = 2461043) B2461043
theorem B1640715 : Blo 1640019 1640715 := bstep (se 1 (by rfl) ⟨1230536, by rfl⟩ : syracuseStep 1640715 = 2461073) B2461073
theorem B1640727 : Blo 1640019 1640727 := bstep (se 1 (by rfl) ⟨1230545, by rfl⟩ : syracuseStep 1640727 = 2461091) B2461091
theorem B2337049 : Blo 1640019 2337049 := bstep (se 2 (by rfl) ⟨876393, by rfl⟩ : syracuseStep 2337049 = 1752787) B1752787
theorem B1640747 : Blo 1640019 1640747 := bstep (se 1 (by rfl) ⟨1230560, by rfl⟩ : syracuseStep 1640747 = 2461121) B2461121
theorem B1640759 : Blo 1640019 1640759 := bstep (se 1 (by rfl) ⟨1230569, by rfl⟩ : syracuseStep 1640759 = 2461139) B2461139
theorem B1640779 : Blo 1640019 1640779 := bstep (se 1 (by rfl) ⟨1230584, by rfl⟩ : syracuseStep 1640779 = 2461169) B2461169
theorem B1640791 : Blo 1640019 1640791 := bstep (se 1 (by rfl) ⟨1230593, by rfl⟩ : syracuseStep 1640791 = 2461187) B2461187
theorem B3115351 : Blo 1640019 3115351 := bstep (se 1 (by rfl) ⟨2336513, by rfl⟩ : syracuseStep 3115351 = 4673027) B4673027
theorem B1640811 : Blo 1640019 1640811 := bstep (se 1 (by rfl) ⟨1230608, by rfl⟩ : syracuseStep 1640811 = 2461217) B2461217
theorem B21031285 : Blo 1640019 21031285 := bstep (se 5 (by rfl) ⟨985841, by rfl⟩ : syracuseStep 21031285 = 1971683) B1971683
theorem B1640823 : Blo 1640019 1640823 := bstep (se 1 (by rfl) ⟨1230617, by rfl⟩ : syracuseStep 1640823 = 2461235) B2461235
theorem B9341315 : Blo 1640019 9341315 := bstep (se 1 (by rfl) ⟨7005986, by rfl⟩ : syracuseStep 9341315 = 14011973) B14011973
theorem B1845643 : Blo 1640019 1845643 := bstep (se 1 (by rfl) ⟨1384232, by rfl⟩ : syracuseStep 1845643 = 2768465) B2768465
theorem B1640843 : Blo 1640019 1640843 := bstep (se 1 (by rfl) ⟨1230632, by rfl⟩ : syracuseStep 1640843 = 2461265) B2461265
theorem B1640855 : Blo 1640019 1640855 := bstep (se 1 (by rfl) ⟨1230641, by rfl⟩ : syracuseStep 1640855 = 2461283) B2461283
theorem B1640875 : Blo 1640019 1640875 := bstep (se 1 (by rfl) ⟨1230656, by rfl⟩ : syracuseStep 1640875 = 2461313) B2461313
theorem B1640887 : Blo 1640019 1640887 := bstep (se 1 (by rfl) ⟨1230665, by rfl⟩ : syracuseStep 1640887 = 2461331) B2461331
theorem B2460107 : Blo 1640019 2460107 := bstep (se 1 (by rfl) ⟨1845080, by rfl⟩ : syracuseStep 2460107 = 3690161) B3690161
theorem B1640907 : Blo 1640019 1640907 := bstep (se 1 (by rfl) ⟨1230680, by rfl⟩ : syracuseStep 1640907 = 2461361) B2461361
theorem B2460119 : Blo 1640019 2460119 := bstep (se 1 (by rfl) ⟨1845089, by rfl⟩ : syracuseStep 2460119 = 3690179) B3690179
theorem B1640919 : Blo 1640019 1640919 := bstep (se 1 (by rfl) ⟨1230689, by rfl⟩ : syracuseStep 1640919 = 2461379) B2461379
theorem B1640939 : Blo 1640019 1640939 := bstep (se 1 (by rfl) ⟨1230704, by rfl⟩ : syracuseStep 1640939 = 2461409) B2461409
theorem B1845751 : Blo 1640019 1845751 := bstep (se 1 (by rfl) ⟨1384313, by rfl⟩ : syracuseStep 1845751 = 2768627) B2768627
theorem B1640951 : Blo 1640019 1640951 := bstep (se 1 (by rfl) ⟨1230713, by rfl⟩ : syracuseStep 1640951 = 2461427) B2461427
theorem B1640971 : Blo 1640019 1640971 := bstep (se 1 (by rfl) ⟨1230728, by rfl⟩ : syracuseStep 1640971 = 2461457) B2461457
theorem B1640983 : Blo 1640019 1640983 := bstep (se 1 (by rfl) ⟨1230737, by rfl⟩ : syracuseStep 1640983 = 2461475) B2461475
theorem B2460185 : Blo 1640019 2460185 := bstep (se 2 (by rfl) ⟨922569, by rfl⟩ : syracuseStep 2460185 = 1845139) B1845139
theorem B1641003 : Blo 1640019 1641003 := bstep (se 1 (by rfl) ⟨1230752, by rfl⟩ : syracuseStep 1641003 = 2461505) B2461505
theorem B1641015 : Blo 1640019 1641015 := bstep (se 1 (by rfl) ⟨1230761, by rfl⟩ : syracuseStep 1641015 = 2461523) B2461523
theorem B1641035 : Blo 1640019 1641035 := bstep (se 1 (by rfl) ⟨1230776, by rfl⟩ : syracuseStep 1641035 = 2461553) B2461553
theorem B1641047 : Blo 1640019 1641047 := bstep (se 1 (by rfl) ⟨1230785, by rfl⟩ : syracuseStep 1641047 = 2461571) B2461571
theorem B4672093 : Blo 1640019 4672093 := bstep (se 3 (by rfl) ⟨876017, by rfl⟩ : syracuseStep 4672093 = 1752035) B1752035
theorem B1641067 : Blo 1640019 1641067 := bstep (se 1 (by rfl) ⟨1230800, by rfl⟩ : syracuseStep 1641067 = 2461601) B2461601
theorem B1641079 : Blo 1640019 1641079 := bstep (se 1 (by rfl) ⟨1230809, by rfl⟩ : syracuseStep 1641079 = 2461619) B2461619
theorem B18688643 : Blo 1640019 18688643 := bstep (se 1 (by rfl) ⟨14016482, by rfl⟩ : syracuseStep 18688643 = 28032965) B28032965
theorem B2460299 : Blo 1640019 2460299 := bstep (se 1 (by rfl) ⟨1845224, by rfl⟩ : syracuseStep 2460299 = 3690449) B3690449
theorem B1641099 : Blo 1640019 1641099 := bstep (se 1 (by rfl) ⟨1230824, by rfl⟩ : syracuseStep 1641099 = 2461649) B2461649
theorem B2460311 : Blo 1640019 2460311 := bstep (se 1 (by rfl) ⟨1845233, by rfl⟩ : syracuseStep 2460311 = 3690467) B3690467
theorem B4672151 : Blo 1640019 4672151 := bstep (se 1 (by rfl) ⟨3504113, by rfl⟩ : syracuseStep 4672151 = 7008227) B7008227
theorem B1641111 : Blo 1640019 1641111 := bstep (se 1 (by rfl) ⟨1230833, by rfl⟩ : syracuseStep 1641111 = 2461667) B2461667
theorem B1845931 : Blo 1640019 1845931 := bstep (se 1 (by rfl) ⟨1384448, by rfl⟩ : syracuseStep 1845931 = 2768897) B2768897
theorem B1641131 : Blo 1640019 1641131 := bstep (se 1 (by rfl) ⟨1230848, by rfl⟩ : syracuseStep 1641131 = 2461697) B2461697
theorem B1641143 : Blo 1640019 1641143 := bstep (se 1 (by rfl) ⟨1230857, by rfl⟩ : syracuseStep 1641143 = 2461715) B2461715
theorem B6228683 : Blo 1640019 6228683 := bstep (se 1 (by rfl) ⟨4671512, by rfl⟩ : syracuseStep 6228683 = 9343025) B9343025
theorem B1641163 : Blo 1640019 1641163 := bstep (se 1 (by rfl) ⟨1230872, by rfl⟩ : syracuseStep 1641163 = 2461745) B2461745
theorem B1641175 : Blo 1640019 1641175 := bstep (se 1 (by rfl) ⟨1230881, by rfl⟩ : syracuseStep 1641175 = 2461763) B2461763
theorem B2460377 : Blo 1640019 2460377 := bstep (se 2 (by rfl) ⟨922641, by rfl⟩ : syracuseStep 2460377 = 1845283) B1845283
theorem B6228697 : Blo 1640019 6228697 := bstep (se 2 (by rfl) ⟨2335761, by rfl⟩ : syracuseStep 6228697 = 4671523) B4671523
theorem B8309465 : Blo 1640019 8309465 := bstep (se 2 (by rfl) ⟨3116049, by rfl⟩ : syracuseStep 8309465 = 6232099) B6232099
theorem B1641195 : Blo 1640019 1641195 := bstep (se 1 (by rfl) ⟨1230896, by rfl⟩ : syracuseStep 1641195 = 2461793) B2461793
theorem B1641207 : Blo 1640019 1641207 := bstep (se 1 (by rfl) ⟨1230905, by rfl⟩ : syracuseStep 1641207 = 2461811) B2461811
theorem B1641227 : Blo 1640019 1641227 := bstep (se 1 (by rfl) ⟨1230920, by rfl⟩ : syracuseStep 1641227 = 2461841) B2461841
theorem B1846039 : Blo 1640019 1846039 := bstep (se 1 (by rfl) ⟨1384529, by rfl⟩ : syracuseStep 1846039 = 2769059) B2769059
theorem B1641239 : Blo 1640019 1641239 := bstep (se 1 (by rfl) ⟨1230929, by rfl⟩ : syracuseStep 1641239 = 2461859) B2461859
theorem B1641259 : Blo 1640019 1641259 := bstep (se 1 (by rfl) ⟨1230944, by rfl⟩ : syracuseStep 1641259 = 2461889) B2461889
theorem B4156211 : Blo 1640019 4156211 := bstep (se 1 (by rfl) ⟨3117158, by rfl⟩ : syracuseStep 4156211 = 6234317) B6234317
theorem B1641271 : Blo 1640019 1641271 := bstep (se 1 (by rfl) ⟨1230953, by rfl⟩ : syracuseStep 1641271 = 2461907) B2461907
theorem B12454721 : Blo 1640019 12454721 := bstep (se 2 (by rfl) ⟨4670520, by rfl⟩ : syracuseStep 12454721 = 9341041) B9341041
theorem B2460491 : Blo 1640019 2460491 := bstep (se 1 (by rfl) ⟨1845368, by rfl⟩ : syracuseStep 2460491 = 3690737) B3690737
theorem B1641291 : Blo 1640019 1641291 := bstep (se 1 (by rfl) ⟨1230968, by rfl⟩ : syracuseStep 1641291 = 2461937) B2461937
theorem B2460503 : Blo 1640019 2460503 := bstep (se 1 (by rfl) ⟨1845377, by rfl⟩ : syracuseStep 2460503 = 3690755) B3690755
theorem B1641303 : Blo 1640019 1641303 := bstep (se 1 (by rfl) ⟨1230977, by rfl⟩ : syracuseStep 1641303 = 2461955) B2461955
theorem B1641323 : Blo 1640019 1641323 := bstep (se 1 (by rfl) ⟨1230992, by rfl⟩ : syracuseStep 1641323 = 2461985) B2461985
theorem B1641335 : Blo 1640019 1641335 := bstep (se 1 (by rfl) ⟨1231001, by rfl⟩ : syracuseStep 1641335 = 2462003) B2462003
theorem B1641355 : Blo 1640019 1641355 := bstep (se 1 (by rfl) ⟨1231016, by rfl⟩ : syracuseStep 1641355 = 2462033) B2462033
theorem B1641367 : Blo 1640019 1641367 := bstep (se 1 (by rfl) ⟨1231025, by rfl⟩ : syracuseStep 1641367 = 2462051) B2462051
theorem B2460569 : Blo 1640019 2460569 := bstep (se 2 (by rfl) ⟨922713, by rfl⟩ : syracuseStep 2460569 = 1845427) B1845427
theorem B1641387 : Blo 1640019 1641387 := bstep (se 1 (by rfl) ⟨1231040, by rfl⟩ : syracuseStep 1641387 = 2462081) B2462081
theorem B1641399 : Blo 1640019 1641399 := bstep (se 1 (by rfl) ⟨1231049, by rfl⟩ : syracuseStep 1641399 = 2462099) B2462099
theorem B1846219 : Blo 1640019 1846219 := bstep (se 1 (by rfl) ⟨1384664, by rfl⟩ : syracuseStep 1846219 = 2769329) B2769329
theorem B1641419 : Blo 1640019 1641419 := bstep (se 1 (by rfl) ⟨1231064, by rfl⟩ : syracuseStep 1641419 = 2462129) B2462129
theorem B1641431 : Blo 1640019 1641431 := bstep (se 1 (by rfl) ⟨1231073, by rfl⟩ : syracuseStep 1641431 = 2462147) B2462147
theorem B1641451 : Blo 1640019 1641451 := bstep (se 1 (by rfl) ⟨1231088, by rfl⟩ : syracuseStep 1641451 = 2462177) B2462177
theorem B1641463 : Blo 1640019 1641463 := bstep (se 1 (by rfl) ⟨1231097, by rfl⟩ : syracuseStep 1641463 = 2462195) B2462195
theorem B2460683 : Blo 1640019 2460683 := bstep (se 1 (by rfl) ⟨1845512, by rfl⟩ : syracuseStep 2460683 = 3691025) B3691025
theorem B1641483 : Blo 1640019 1641483 := bstep (se 1 (by rfl) ⟨1231112, by rfl⟩ : syracuseStep 1641483 = 2462225) B2462225
theorem B2460695 : Blo 1640019 2460695 := bstep (se 1 (by rfl) ⟨1845521, by rfl⟩ : syracuseStep 2460695 = 3691043) B3691043
theorem B1641495 : Blo 1640019 1641495 := bstep (se 1 (by rfl) ⟨1231121, by rfl⟩ : syracuseStep 1641495 = 2462243) B2462243
theorem B1641515 : Blo 1640019 1641515 := bstep (se 1 (by rfl) ⟨1231136, by rfl⟩ : syracuseStep 1641515 = 2462273) B2462273
theorem B1846327 : Blo 1640019 1846327 := bstep (se 1 (by rfl) ⟨1384745, by rfl⟩ : syracuseStep 1846327 = 2769491) B2769491
theorem B1641527 : Blo 1640019 1641527 := bstep (se 1 (by rfl) ⟨1231145, by rfl⟩ : syracuseStep 1641527 = 2462291) B2462291
theorem B7883851 : Blo 1640019 7883851 := bstep (se 1 (by rfl) ⟨5912888, by rfl⟩ : syracuseStep 7883851 = 11825777) B11825777
theorem B5614667 : Blo 1640019 5614667 := bstep (se 1 (by rfl) ⟨4211000, by rfl⟩ : syracuseStep 5614667 = 8422001) B8422001
theorem B1641547 : Blo 1640019 1641547 := bstep (se 1 (by rfl) ⟨1231160, by rfl⟩ : syracuseStep 1641547 = 2462321) B2462321
theorem B5540939 : Blo 1640019 5540939 := bstep (se 1 (by rfl) ⟨4155704, by rfl⟩ : syracuseStep 5540939 = 8311409) B8311409
theorem B1641559 : Blo 1640019 1641559 := bstep (se 1 (by rfl) ⟨1231169, by rfl⟩ : syracuseStep 1641559 = 2462339) B2462339
theorem B2460761 : Blo 1640019 2460761 := bstep (se 2 (by rfl) ⟨922785, by rfl⟩ : syracuseStep 2460761 = 1845571) B1845571
theorem B1641579 : Blo 1640019 1641579 := bstep (se 1 (by rfl) ⟨1231184, by rfl⟩ : syracuseStep 1641579 = 2462369) B2462369
theorem B1641591 : Blo 1640019 1641591 := bstep (se 1 (by rfl) ⟨1231193, by rfl⟩ : syracuseStep 1641591 = 2462387) B2462387
theorem B3116171 : Blo 1640019 3116171 := bstep (se 1 (by rfl) ⟨2337128, by rfl⟩ : syracuseStep 3116171 = 4674257) B4674257
theorem B1641611 : Blo 1640019 1641611 := bstep (se 1 (by rfl) ⟨1231208, by rfl⟩ : syracuseStep 1641611 = 2462417) B2462417
theorem B1641623 : Blo 1640019 1641623 := bstep (se 1 (by rfl) ⟨1231217, by rfl⟩ : syracuseStep 1641623 = 2462435) B2462435
theorem B1641643 : Blo 1640019 1641643 := bstep (se 1 (by rfl) ⟨1231232, by rfl⟩ : syracuseStep 1641643 = 2462465) B2462465
theorem B14019763 : Blo 1640019 14019763 := bstep (se 1 (by rfl) ⟨10514822, by rfl⟩ : syracuseStep 14019763 = 21029645) B21029645
theorem B1641655 : Blo 1640019 1641655 := bstep (se 1 (by rfl) ⟨1231241, by rfl⟩ : syracuseStep 1641655 = 2462483) B2462483
theorem B3116225 : Blo 1640019 3116225 := bstep (se 2 (by rfl) ⟨1168584, by rfl⟩ : syracuseStep 3116225 = 2337169) B2337169
theorem B2460875 : Blo 1640019 2460875 := bstep (se 1 (by rfl) ⟨1845656, by rfl⟩ : syracuseStep 2460875 = 3691313) B3691313
theorem B1641675 : Blo 1640019 1641675 := bstep (se 1 (by rfl) ⟨1231256, by rfl⟩ : syracuseStep 1641675 = 2462513) B2462513
theorem B2075863 : Blo 1640019 2075863 := bstep (se 1 (by rfl) ⟨1556897, by rfl⟩ : syracuseStep 2075863 = 3113795) B3113795
theorem B2460887 : Blo 1640019 2460887 := bstep (se 1 (by rfl) ⟨1845665, by rfl⟩ : syracuseStep 2460887 = 3691331) B3691331
theorem B1641687 : Blo 1640019 1641687 := bstep (se 1 (by rfl) ⟨1231265, by rfl⟩ : syracuseStep 1641687 = 2462531) B2462531
theorem B1846507 : Blo 1640019 1846507 := bstep (se 1 (by rfl) ⟨1384880, by rfl⟩ : syracuseStep 1846507 = 2769761) B2769761
theorem B1641707 : Blo 1640019 1641707 := bstep (se 1 (by rfl) ⟨1231280, by rfl⟩ : syracuseStep 1641707 = 2462561) B2462561
theorem B1641719 : Blo 1640019 1641719 := bstep (se 1 (by rfl) ⟨1231289, by rfl⟩ : syracuseStep 1641719 = 2462579) B2462579
theorem B255823109 : Blo 1640019 255823109 := bstep (se 4 (by rfl) ⟨23983416, by rfl⟩ : syracuseStep 255823109 = 47966833) B47966833
theorem B1641739 : Blo 1640019 1641739 := bstep (se 1 (by rfl) ⟨1231304, by rfl⟩ : syracuseStep 1641739 = 2462609) B2462609
theorem B1641751 : Blo 1640019 1641751 := bstep (se 1 (by rfl) ⟨1231313, by rfl⟩ : syracuseStep 1641751 = 2462627) B2462627
theorem B2460953 : Blo 1640019 2460953 := bstep (se 2 (by rfl) ⟨922857, by rfl⟩ : syracuseStep 2460953 = 1845715) B1845715
theorem B1641771 : Blo 1640019 1641771 := bstep (se 1 (by rfl) ⟨1231328, by rfl⟩ : syracuseStep 1641771 = 2462657) B2462657
theorem B53923117 : Blo 1640019 53923117 := bstep (se 3 (by rfl) ⟨10110584, by rfl⟩ : syracuseStep 53923117 = 20221169) B20221169
theorem B1641783 : Blo 1640019 1641783 := bstep (se 1 (by rfl) ⟨1231337, by rfl⟩ : syracuseStep 1641783 = 2462675) B2462675
theorem B5254465 : Blo 1640019 5254465 := bstep (se 2 (by rfl) ⟨1970424, by rfl⟩ : syracuseStep 5254465 = 3940849) B3940849
theorem B1641803 : Blo 1640019 1641803 := bstep (se 1 (by rfl) ⟨1231352, by rfl⟩ : syracuseStep 1641803 = 2462705) B2462705
theorem B1846615 : Blo 1640019 1846615 := bstep (se 1 (by rfl) ⟨1384961, by rfl⟩ : syracuseStep 1846615 = 2769923) B2769923
theorem B1641815 : Blo 1640019 1641815 := bstep (se 1 (by rfl) ⟨1231361, by rfl⟩ : syracuseStep 1641815 = 2462723) B2462723
theorem B5541209 : Blo 1640019 5541209 := bstep (se 2 (by rfl) ⟨2077953, by rfl⟩ : syracuseStep 5541209 = 4155907) B4155907
theorem B1641835 : Blo 1640019 1641835 := bstep (se 1 (by rfl) ⟨1231376, by rfl⟩ : syracuseStep 1641835 = 2462753) B2462753
theorem B1641847 : Blo 1640019 1641847 := bstep (se 1 (by rfl) ⟨1231385, by rfl⟩ : syracuseStep 1641847 = 2462771) B2462771
theorem B2461067 : Blo 1640019 2461067 := bstep (se 1 (by rfl) ⟨1845800, by rfl⟩ : syracuseStep 2461067 = 3691601) B3691601
theorem B1641867 : Blo 1640019 1641867 := bstep (se 1 (by rfl) ⟨1231400, by rfl⟩ : syracuseStep 1641867 = 2462801) B2462801
theorem B2461079 : Blo 1640019 2461079 := bstep (se 1 (by rfl) ⟨1845809, by rfl⟩ : syracuseStep 2461079 = 3691619) B3691619
theorem B1641879 : Blo 1640019 1641879 := bstep (se 1 (by rfl) ⟨1231409, by rfl⟩ : syracuseStep 1641879 = 2462819) B2462819
theorem B1641899 : Blo 1640019 1641899 := bstep (se 1 (by rfl) ⟨1231424, by rfl⟩ : syracuseStep 1641899 = 2462849) B2462849
theorem B1641911 : Blo 1640019 1641911 := bstep (se 1 (by rfl) ⟨1231433, by rfl⟩ : syracuseStep 1641911 = 2462867) B2462867
theorem B1641931 : Blo 1640019 1641931 := bstep (se 1 (by rfl) ⟨1231448, by rfl⟩ : syracuseStep 1641931 = 2462897) B2462897
theorem B1641943 : Blo 1640019 1641943 := bstep (se 1 (by rfl) ⟨1231457, by rfl⟩ : syracuseStep 1641943 = 2462915) B2462915
theorem B2461145 : Blo 1640019 2461145 := bstep (se 2 (by rfl) ⟨922929, by rfl⟩ : syracuseStep 2461145 = 1845859) B1845859
theorem B1641963 : Blo 1640019 1641963 := bstep (se 1 (by rfl) ⟨1231472, by rfl⟩ : syracuseStep 1641963 = 2462945) B2462945
theorem B1641975 : Blo 1640019 1641975 := bstep (se 1 (by rfl) ⟨1231481, by rfl⟩ : syracuseStep 1641975 = 2462963) B2462963
theorem B1846795 : Blo 1640019 1846795 := bstep (se 1 (by rfl) ⟨1385096, by rfl⟩ : syracuseStep 1846795 = 2770193) B2770193
theorem B1641995 : Blo 1640019 1641995 := bstep (se 1 (by rfl) ⟨1231496, by rfl⟩ : syracuseStep 1641995 = 2462993) B2462993
theorem B1642007 : Blo 1640019 1642007 := bstep (se 1 (by rfl) ⟨1231505, by rfl⟩ : syracuseStep 1642007 = 2463011) B2463011
theorem B2461259 : Blo 1640019 2461259 := bstep (se 1 (by rfl) ⟨1845944, by rfl⟩ : syracuseStep 2461259 = 3691889) B3691889
theorem B3690071 : Blo 1640019 3690071 := bstep (se 1 (by rfl) ⟨2767553, by rfl⟩ : syracuseStep 3690071 = 5535107) B5535107
theorem B2461271 : Blo 1640019 2461271 := bstep (se 1 (by rfl) ⟨1845953, by rfl⟩ : syracuseStep 2461271 = 3691907) B3691907
theorem B1846903 : Blo 1640019 1846903 := bstep (se 1 (by rfl) ⟨1385177, by rfl⟩ : syracuseStep 1846903 = 2770355) B2770355
theorem B6229655 : Blo 1640019 6229655 := bstep (se 1 (by rfl) ⟨4672241, by rfl⟩ : syracuseStep 6229655 = 9344483) B9344483
theorem B2461337 : Blo 1640019 2461337 := bstep (se 2 (by rfl) ⟨923001, by rfl⟩ : syracuseStep 2461337 = 1846003) B1846003
theorem B3690251 : Blo 1640019 3690251 := bstep (se 1 (by rfl) ⟨2767688, by rfl⟩ : syracuseStep 3690251 = 5535377) B5535377
theorem B2461451 : Blo 1640019 2461451 := bstep (se 1 (by rfl) ⟨1846088, by rfl⟩ : syracuseStep 2461451 = 3692177) B3692177
theorem B2461463 : Blo 1640019 2461463 := bstep (se 1 (by rfl) ⟨1846097, by rfl⟩ : syracuseStep 2461463 = 3692195) B3692195
theorem B1847083 : Blo 1640019 1847083 := bstep (se 1 (by rfl) ⟨1385312, by rfl⟩ : syracuseStep 1847083 = 2770625) B2770625
theorem B3690305 : Blo 1640019 3690305 := bstep (se 2 (by rfl) ⟨1383864, by rfl⟩ : syracuseStep 3690305 = 2767729) B2767729
theorem B2461529 : Blo 1640019 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B4673369 : Blo 1640019 4673369 := bstep (se 2 (by rfl) ⟨1752513, by rfl⟩ : syracuseStep 4673369 = 3505027) B3505027
theorem B11825027 : Blo 1640019 11825027 := bstep (se 1 (by rfl) ⟨8868770, by rfl⟩ : syracuseStep 11825027 = 17737541) B17737541
theorem B1847191 : Blo 1640019 1847191 := bstep (se 1 (by rfl) ⟨1385393, by rfl⟩ : syracuseStep 1847191 = 2770787) B2770787
theorem B7991219 : Blo 1640019 7991219 := bstep (se 1 (by rfl) ⟨5993414, by rfl⟩ : syracuseStep 7991219 = 11986829) B11986829
theorem B2461643 : Blo 1640019 2461643 := bstep (se 1 (by rfl) ⟨1846232, by rfl⟩ : syracuseStep 2461643 = 3692465) B3692465
theorem B4673483 : Blo 1640019 4673483 := bstep (se 1 (by rfl) ⟨3505112, by rfl⟩ : syracuseStep 4673483 = 7010225) B7010225
theorem B2461655 : Blo 1640019 2461655 := bstep (se 1 (by rfl) ⟨1846241, by rfl⟩ : syracuseStep 2461655 = 3692483) B3692483
theorem B3690521 : Blo 1640019 3690521 := bstep (se 2 (by rfl) ⟨1383945, by rfl⟩ : syracuseStep 3690521 = 2767891) B2767891
theorem B3371033 : Blo 1640019 3371033 := bstep (se 2 (by rfl) ⟨1264137, by rfl⟩ : syracuseStep 3371033 = 2528275) B2528275
theorem B2461721 : Blo 1640019 2461721 := bstep (se 2 (by rfl) ⟨923145, by rfl⟩ : syracuseStep 2461721 = 1846291) B1846291
theorem B3117143 : Blo 1640019 3117143 := bstep (se 1 (by rfl) ⟨2337857, by rfl⟩ : syracuseStep 3117143 = 4675715) B4675715
theorem B3690611 : Blo 1640019 3690611 := bstep (se 1 (by rfl) ⟨2767958, by rfl⟩ : syracuseStep 3690611 = 5535917) B5535917
theorem B2461835 : Blo 1640019 2461835 := bstep (se 1 (by rfl) ⟨1846376, by rfl⟩ : syracuseStep 2461835 = 3692753) B3692753
theorem B3690647 : Blo 1640019 3690647 := bstep (se 1 (by rfl) ⟨2767985, by rfl⟩ : syracuseStep 3690647 = 5535971) B5535971
theorem B2461847 : Blo 1640019 2461847 := bstep (se 1 (by rfl) ⟨1846385, by rfl⟩ : syracuseStep 2461847 = 3692771) B3692771
theorem B5992627 : Blo 1640019 5992627 := bstep (se 1 (by rfl) ⟨4494470, by rfl⟩ : syracuseStep 5992627 = 8988941) B8988941
theorem B2461913 : Blo 1640019 2461913 := bstep (se 2 (by rfl) ⟨923217, by rfl⟩ : syracuseStep 2461913 = 1846435) B1846435
theorem B7008515 : Blo 1640019 7008515 := bstep (se 1 (by rfl) ⟨5256386, by rfl⟩ : syracuseStep 7008515 = 10512773) B10512773
theorem B8311085 : Blo 1640019 8311085 := bstep (se 3 (by rfl) ⟨1558328, by rfl⟩ : syracuseStep 8311085 = 3116657) B3116657
theorem B3690827 : Blo 1640019 3690827 := bstep (se 1 (by rfl) ⟨2768120, by rfl⟩ : syracuseStep 3690827 = 5536241) B5536241
theorem B2462027 : Blo 1640019 2462027 := bstep (se 1 (by rfl) ⟨1846520, by rfl⟩ : syracuseStep 2462027 = 3693041) B3693041
theorem B2462039 : Blo 1640019 2462039 := bstep (se 1 (by rfl) ⟨1846529, by rfl⟩ : syracuseStep 2462039 = 3693059) B3693059
theorem B3690881 : Blo 1640019 3690881 := bstep (se 2 (by rfl) ⟨1384080, by rfl⟩ : syracuseStep 3690881 = 2768161) B2768161
theorem B2462105 : Blo 1640019 2462105 := bstep (se 2 (by rfl) ⟨923289, by rfl⟩ : syracuseStep 2462105 = 1846579) B1846579
theorem B5911001 : Blo 1640019 5911001 := bstep (se 2 (by rfl) ⟨2216625, by rfl⟩ : syracuseStep 5911001 = 4433251) B4433251
theorem B2462219 : Blo 1640019 2462219 := bstep (se 1 (by rfl) ⟨1846664, by rfl⟩ : syracuseStep 2462219 = 3693329) B3693329
theorem B2494999 : Blo 1640019 2494999 := bstep (se 1 (by rfl) ⟨1871249, by rfl⟩ : syracuseStep 2494999 = 3742499) B3742499
theorem B2462231 : Blo 1640019 2462231 := bstep (se 1 (by rfl) ⟨1846673, by rfl⟩ : syracuseStep 2462231 = 3693347) B3693347
theorem B3691097 : Blo 1640019 3691097 := bstep (se 2 (by rfl) ⟨1384161, by rfl⟩ : syracuseStep 3691097 = 2768323) B2768323
theorem B4436569 : Blo 1640019 4436569 := bstep (se 2 (by rfl) ⟨1663713, by rfl⟩ : syracuseStep 4436569 = 3327427) B3327427
theorem B2462297 : Blo 1640019 2462297 := bstep (se 2 (by rfl) ⟨923361, by rfl⟩ : syracuseStep 2462297 = 1846723) B1846723
theorem B9351773 : Blo 1640019 9351773 := bstep (se 3 (by rfl) ⟨1753457, by rfl⟩ : syracuseStep 9351773 = 3506915) B3506915
theorem B3691187 : Blo 1640019 3691187 := bstep (se 1 (by rfl) ⟨2768390, by rfl⟩ : syracuseStep 3691187 = 5536781) B5536781
theorem B6656705 : Blo 1640019 6656705 := bstep (se 2 (by rfl) ⟨2496264, by rfl⟩ : syracuseStep 6656705 = 4992529) B4992529
theorem B2462411 : Blo 1640019 2462411 := bstep (se 1 (by rfl) ⟨1846808, by rfl⟩ : syracuseStep 2462411 = 3693617) B3693617
theorem B3691223 : Blo 1640019 3691223 := bstep (se 1 (by rfl) ⟨2768417, by rfl⟩ : syracuseStep 3691223 = 5536835) B5536835
theorem B2462423 : Blo 1640019 2462423 := bstep (se 1 (by rfl) ⟨1846817, by rfl⟩ : syracuseStep 2462423 = 3693635) B3693635
theorem B12456665 : Blo 1640019 12456665 := bstep (se 2 (by rfl) ⟨4671249, by rfl⟩ : syracuseStep 12456665 = 9342499) B9342499
theorem B2462489 : Blo 1640019 2462489 := bstep (se 2 (by rfl) ⟨923433, by rfl⟩ : syracuseStep 2462489 = 1846867) B1846867
theorem B5256029 : Blo 1640019 5256029 := bstep (se 3 (by rfl) ⟨985505, by rfl⟩ : syracuseStep 5256029 = 1971011) B1971011
theorem B6230915 : Blo 1640019 6230915 := bstep (se 1 (by rfl) ⟨4673186, by rfl⟩ : syracuseStep 6230915 = 9346373) B9346373
theorem B3691403 : Blo 1640019 3691403 := bstep (se 1 (by rfl) ⟨2768552, by rfl⟩ : syracuseStep 3691403 = 5537105) B5537105
theorem B2077579 : Blo 1640019 2077579 := bstep (se 1 (by rfl) ⟨1558184, by rfl⟩ : syracuseStep 2077579 = 3116369) B3116369
theorem B2462603 : Blo 1640019 2462603 := bstep (se 1 (by rfl) ⟨1846952, by rfl⟩ : syracuseStep 2462603 = 3693905) B3693905
theorem B2462615 : Blo 1640019 2462615 := bstep (se 1 (by rfl) ⟨1846961, by rfl⟩ : syracuseStep 2462615 = 3693923) B3693923
theorem B3691457 : Blo 1640019 3691457 := bstep (se 2 (by rfl) ⟨1384296, by rfl⟩ : syracuseStep 3691457 = 2768593) B2768593
theorem B2462681 : Blo 1640019 2462681 := bstep (se 2 (by rfl) ⟨923505, by rfl⟩ : syracuseStep 2462681 = 1847011) B1847011
theorem B8303633 : Blo 1640019 8303633 := bstep (se 2 (by rfl) ⟨3113862, by rfl⟩ : syracuseStep 8303633 = 6227725) B6227725
theorem B4674611 : Blo 1640019 4674611 := bstep (se 1 (by rfl) ⟨3505958, by rfl⟩ : syracuseStep 4674611 = 7011917) B7011917
theorem B2462795 : Blo 1640019 2462795 := bstep (se 1 (by rfl) ⟨1847096, by rfl⟩ : syracuseStep 2462795 = 3694193) B3694193
theorem B2462807 : Blo 1640019 2462807 := bstep (se 1 (by rfl) ⟨1847105, by rfl⟩ : syracuseStep 2462807 = 3694211) B3694211
theorem B3691673 : Blo 1640019 3691673 := bstep (se 2 (by rfl) ⟨1384377, by rfl⟩ : syracuseStep 3691673 = 2768755) B2768755
theorem B2462873 : Blo 1640019 2462873 := bstep (se 2 (by rfl) ⟨923577, by rfl⟩ : syracuseStep 2462873 = 1847155) B1847155
theorem B8303795 : Blo 1640019 8303795 := bstep (se 1 (by rfl) ⟨6227846, by rfl⟩ : syracuseStep 8303795 = 12455693) B12455693
theorem B7484633 : Blo 1640019 7484633 := bstep (se 2 (by rfl) ⟨2806737, by rfl⟩ : syracuseStep 7484633 = 5613475) B5613475
theorem B3691763 : Blo 1640019 3691763 := bstep (se 1 (by rfl) ⟨2768822, by rfl⟩ : syracuseStep 3691763 = 5537645) B5537645
theorem B12465413 : Blo 1640019 12465413 := bstep (se 4 (by rfl) ⟨1168632, by rfl⟩ : syracuseStep 12465413 = 2337265) B2337265
theorem B2462987 : Blo 1640019 2462987 := bstep (se 1 (by rfl) ⟨1847240, by rfl⟩ : syracuseStep 2462987 = 3694481) B3694481
theorem B3691799 : Blo 1640019 3691799 := bstep (se 1 (by rfl) ⟨2768849, by rfl⟩ : syracuseStep 3691799 = 5537699) B5537699
theorem B2462999 : Blo 1640019 2462999 := bstep (se 1 (by rfl) ⟨1847249, by rfl⟩ : syracuseStep 2462999 = 3694499) B3694499
theorem B8418653 : Blo 1640019 8418653 := bstep (se 3 (by rfl) ⟨1578497, by rfl⟩ : syracuseStep 8418653 = 3156995) B3156995
theorem B7108019 : Blo 1640019 7108019 := bstep (se 1 (by rfl) ⟨5331014, by rfl⟩ : syracuseStep 7108019 = 10662029) B10662029
theorem B4675009 : Blo 1640019 4675009 := bstep (se 2 (by rfl) ⟨1753128, by rfl⟩ : syracuseStep 4675009 = 3506257) B3506257
theorem B3691979 : Blo 1640019 3691979 := bstep (se 1 (by rfl) ⟨2768984, by rfl⟩ : syracuseStep 3691979 = 5537969) B5537969
theorem B3692033 : Blo 1640019 3692033 := bstep (se 2 (by rfl) ⟨1384512, by rfl⟩ : syracuseStep 3692033 = 2769025) B2769025
theorem B26621621 : Blo 1640019 26621621 := bstep (se 5 (by rfl) ⟨1247888, by rfl⟩ : syracuseStep 26621621 = 2495777) B2495777
theorem B3692249 : Blo 1640019 3692249 := bstep (se 2 (by rfl) ⟨1384593, by rfl⟩ : syracuseStep 3692249 = 2769187) B2769187
theorem B5535539 : Blo 1640019 5535539 := bstep (se 1 (by rfl) ⟨4151654, by rfl⟩ : syracuseStep 5535539 = 8303309) B8303309
theorem B3692339 : Blo 1640019 3692339 := bstep (se 1 (by rfl) ⟨2769254, by rfl⟩ : syracuseStep 3692339 = 5538509) B5538509
theorem B26613569 : Blo 1640019 26613569 := bstep (se 2 (by rfl) ⟨9980088, by rfl⟩ : syracuseStep 26613569 = 19960177) B19960177
theorem B3692375 : Blo 1640019 3692375 := bstep (se 1 (by rfl) ⟨2769281, by rfl⟩ : syracuseStep 3692375 = 5538563) B5538563
theorem B13301597 : Blo 1640019 13301597 := bstep (se 3 (by rfl) ⟨2494049, by rfl⟩ : syracuseStep 13301597 = 4988099) B4988099
theorem B26621873 : Blo 1640019 26621873 := bstep (se 2 (by rfl) ⟨9983202, by rfl⟩ : syracuseStep 26621873 = 19966405) B19966405
theorem B3692555 : Blo 1640019 3692555 := bstep (se 1 (by rfl) ⟨2769416, by rfl⟩ : syracuseStep 3692555 = 5538833) B5538833
theorem B7010327 : Blo 1640019 7010327 := bstep (se 1 (by rfl) ⟨5257745, by rfl⟩ : syracuseStep 7010327 = 10515491) B10515491
theorem B5535809 : Blo 1640019 5535809 := bstep (se 2 (by rfl) ⟨2075928, by rfl⟩ : syracuseStep 5535809 = 4151857) B4151857
theorem B3692609 : Blo 1640019 3692609 := bstep (se 2 (by rfl) ⟨1384728, by rfl⟩ : syracuseStep 3692609 = 2769457) B2769457
theorem B4151371 : Blo 1640019 4151371 := bstep (se 1 (by rfl) ⟨3113528, by rfl⟩ : syracuseStep 4151371 = 6227057) B6227057
theorem B10508467 : Blo 1640019 10508467 := bstep (se 1 (by rfl) ⟨7881350, by rfl⟩ : syracuseStep 10508467 = 15762701) B15762701
theorem B4151513 : Blo 1640019 4151513 := bstep (se 2 (by rfl) ⟨1556817, by rfl⟩ : syracuseStep 4151513 = 3113635) B3113635
theorem B3692825 : Blo 1640019 3692825 := bstep (se 2 (by rfl) ⟨1384809, by rfl⟩ : syracuseStep 3692825 = 2769619) B2769619
theorem B1751339 : Blo 1640019 1751339 := bstep (se 1 (by rfl) ⟨1313504, by rfl⟩ : syracuseStep 1751339 = 2627009) B2627009
theorem B3692915 : Blo 1640019 3692915 := bstep (se 1 (by rfl) ⟨2769686, by rfl⟩ : syracuseStep 3692915 = 5539373) B5539373
theorem B3692951 : Blo 1640019 3692951 := bstep (se 1 (by rfl) ⟨2769713, by rfl⟩ : syracuseStep 3692951 = 5539427) B5539427
theorem B4438451 : Blo 1640019 4438451 := bstep (se 1 (by rfl) ⟨3328838, by rfl⟩ : syracuseStep 4438451 = 6657677) B6657677
theorem B3037655 : Blo 1640019 3037655 := bstep (se 1 (by rfl) ⟨2278241, by rfl⟩ : syracuseStep 3037655 = 4556483) B4556483
theorem B3693131 : Blo 1640019 3693131 := bstep (se 1 (by rfl) ⟨2769848, by rfl⟩ : syracuseStep 3693131 = 5539697) B5539697
theorem B5536349 : Blo 1640019 5536349 := bstep (se 3 (by rfl) ⟨1038065, by rfl⟩ : syracuseStep 5536349 = 2076131) B2076131
theorem B3693185 : Blo 1640019 3693185 := bstep (se 2 (by rfl) ⟨1384944, by rfl⟩ : syracuseStep 3693185 = 2769889) B2769889
theorem B3504907 : Blo 1640019 3504907 := bstep (se 1 (by rfl) ⟨2628680, by rfl⟩ : syracuseStep 3504907 = 5257361) B5257361
theorem B3693401 : Blo 1640019 3693401 := bstep (se 2 (by rfl) ⟨1385025, by rfl⟩ : syracuseStep 3693401 = 2770051) B2770051
theorem B3693491 : Blo 1640019 3693491 := bstep (se 1 (by rfl) ⟨2770118, by rfl⟩ : syracuseStep 3693491 = 5540237) B5540237
theorem B3693527 : Blo 1640019 3693527 := bstep (se 1 (by rfl) ⟨2770145, by rfl⟩ : syracuseStep 3693527 = 5540291) B5540291
theorem B10517465 : Blo 1640019 10517465 := bstep (se 2 (by rfl) ⟨3944049, by rfl⟩ : syracuseStep 10517465 = 7888099) B7888099
theorem B4152343 : Blo 1640019 4152343 := bstep (se 1 (by rfl) ⟨3114257, by rfl⟩ : syracuseStep 4152343 = 6228515) B6228515
theorem B23665733 : Blo 1640019 23665733 := bstep (se 4 (by rfl) ⟨2218662, by rfl⟩ : syracuseStep 23665733 = 4437325) B4437325
theorem B8305739 : Blo 1640019 8305739 := bstep (se 1 (by rfl) ⟨6229304, by rfl⟩ : syracuseStep 8305739 = 12458609) B12458609
theorem B1776727 : Blo 1640019 1776727 := bstep (se 1 (by rfl) ⟨1332545, by rfl⟩ : syracuseStep 1776727 = 2665091) B2665091
theorem B4987993 : Blo 1640019 4987993 := bstep (se 2 (by rfl) ⟨1870497, by rfl⟩ : syracuseStep 4987993 = 3740995) B3740995
theorem B2219095 : Blo 1640019 2219095 := bstep (se 1 (by rfl) ⟨1664321, by rfl⟩ : syracuseStep 2219095 = 3328643) B3328643
theorem B3693707 : Blo 1640019 3693707 := bstep (se 1 (by rfl) ⟨2770280, by rfl⟩ : syracuseStep 3693707 = 5540561) B5540561
theorem B3693761 : Blo 1640019 3693761 := bstep (se 2 (by rfl) ⟨1385160, by rfl⟩ : syracuseStep 3693761 = 2770321) B2770321
theorem B2768087 : Blo 1640019 2768087 := bstep (se 1 (by rfl) ⟨2076065, by rfl⟩ : syracuseStep 2768087 = 4152131) B4152131
theorem B3505369 : Blo 1640019 3505369 := bstep (se 2 (by rfl) ⟨1314513, by rfl⟩ : syracuseStep 3505369 = 2629027) B2629027
theorem B11222347 : Blo 1640019 11222347 := bstep (se 1 (by rfl) ⟨8416760, by rfl⟩ : syracuseStep 11222347 = 16833521) B16833521
theorem B7011659 : Blo 1640019 7011659 := bstep (se 1 (by rfl) ⟨5258744, by rfl⟩ : syracuseStep 7011659 = 10517489) B10517489
theorem B2768215 : Blo 1640019 2768215 := bstep (se 1 (by rfl) ⟨2076161, by rfl⟩ : syracuseStep 2768215 = 4152323) B4152323
theorem B3693977 : Blo 1640019 3693977 := bstep (se 2 (by rfl) ⟨1385241, by rfl⟩ : syracuseStep 3693977 = 2770483) B2770483
theorem B4152779 : Blo 1640019 4152779 := bstep (se 1 (by rfl) ⟨3114584, by rfl⟩ : syracuseStep 4152779 = 6229169) B6229169
theorem B3694067 : Blo 1640019 3694067 := bstep (se 1 (by rfl) ⟨2770550, by rfl⟩ : syracuseStep 3694067 = 5541101) B5541101
theorem B3694103 : Blo 1640019 3694103 := bstep (se 1 (by rfl) ⟨2770577, by rfl⟩ : syracuseStep 3694103 = 5541155) B5541155
theorem B3325465 : Blo 1640019 3325465 := bstep (se 2 (by rfl) ⟨1247049, by rfl⟩ : syracuseStep 3325465 = 2494099) B2494099
theorem B17735203 : Blo 1640019 17735203 := bstep (se 1 (by rfl) ⟨13301402, by rfl⟩ : syracuseStep 17735203 = 26602805) B26602805
theorem B9346691 : Blo 1640019 9346691 := bstep (se 1 (by rfl) ⟨7010018, by rfl⟩ : syracuseStep 9346691 = 14020037) B14020037
theorem B12467843 : Blo 1640019 12467843 := bstep (se 1 (by rfl) ⟨9350882, by rfl⟩ : syracuseStep 12467843 = 18701765) B18701765
theorem B1752727 : Blo 1640019 1752727 := bstep (se 1 (by rfl) ⟨1314545, by rfl⟩ : syracuseStep 1752727 = 2629091) B2629091
theorem B2956979 : Blo 1640019 2956979 := bstep (se 1 (by rfl) ⟨2217734, by rfl⟩ : syracuseStep 2956979 = 4435469) B4435469
theorem B5537483 : Blo 1640019 5537483 := bstep (se 1 (by rfl) ⟨4153112, by rfl⟩ : syracuseStep 5537483 = 8306225) B8306225
theorem B3694283 : Blo 1640019 3694283 := bstep (se 1 (by rfl) ⟨2770712, by rfl⟩ : syracuseStep 3694283 = 5541425) B5541425
theorem B3694337 : Blo 1640019 3694337 := bstep (se 2 (by rfl) ⟨1385376, by rfl⟩ : syracuseStep 3694337 = 2770753) B2770753
theorem B4153153 : Blo 1640019 4153153 := bstep (se 2 (by rfl) ⟨1557432, by rfl⟩ : syracuseStep 4153153 = 3114865) B3114865
theorem B7888715 : Blo 1640019 7888715 := bstep (se 1 (by rfl) ⟨5916536, by rfl⟩ : syracuseStep 7888715 = 11833073) B11833073
theorem B7012241 : Blo 1640019 7012241 := bstep (se 2 (by rfl) ⟨2629590, by rfl⟩ : syracuseStep 7012241 = 5259181) B5259181
theorem B6234029 : Blo 1640019 6234029 := bstep (se 3 (by rfl) ⟨1168880, by rfl⟩ : syracuseStep 6234029 = 2337761) B2337761
theorem B9600947 : Blo 1640019 9600947 := bstep (se 1 (by rfl) ⟨7200710, by rfl⟩ : syracuseStep 9600947 = 14401421) B14401421
theorem B2768843 : Blo 1640019 2768843 := bstep (se 1 (by rfl) ⟨2076632, by rfl⟩ : syracuseStep 2768843 = 4153265) B4153265
theorem B1662935 : Blo 1640019 1662935 := bstep (se 1 (by rfl) ⟨1247201, by rfl⟩ : syracuseStep 1662935 = 2494403) B2494403
theorem B5537753 : Blo 1640019 5537753 := bstep (se 2 (by rfl) ⟨2076657, by rfl⟩ : syracuseStep 5537753 = 4153315) B4153315
theorem B1753103 : Blo 1640019 1753103 := bstep (se 1 (by rfl) ⟨1314827, by rfl⟩ : syracuseStep 1753103 = 2629655) B2629655
theorem B8306711 : Blo 1640019 8306711 := bstep (se 1 (by rfl) ⟨6230033, by rfl⟩ : syracuseStep 8306711 = 12460067) B12460067
theorem B5914691 : Blo 1640019 5914691 := bstep (se 1 (by rfl) ⟨4436018, by rfl⟩ : syracuseStep 5914691 = 8872037) B8872037
theorem B2769167 : Blo 1640019 2769167 := bstep (se 1 (by rfl) ⟨2076875, by rfl⟩ : syracuseStep 2769167 = 4153751) B4153751
theorem B8872229 : Blo 1640019 8872229 := bstep (se 4 (by rfl) ⟨831771, by rfl⟩ : syracuseStep 8872229 = 1663543) B1663543
theorem B3940667 : Blo 1640019 3940667 := bstep (se 1 (by rfl) ⟨2955500, by rfl⟩ : syracuseStep 3940667 = 5911001) B5911001
theorem B14025095 : Blo 1640019 14025095 := bstep (se 1 (by rfl) ⟨10518821, by rfl⟩ : syracuseStep 14025095 = 21037643) B21037643
theorem B5259667 : Blo 1640019 5259667 := bstep (se 1 (by rfl) ⟨3944750, by rfl⟩ : syracuseStep 5259667 = 7889501) B7889501
theorem B6234515 : Blo 1640019 6234515 := bstep (se 1 (by rfl) ⟨4675886, by rfl⟩ : syracuseStep 6234515 = 9351773) B9351773
theorem B4153801 : Blo 1640019 4153801 := bstep (se 2 (by rfl) ⟨1557675, by rfl⟩ : syracuseStep 4153801 = 3115351) B3115351
theorem B28041713 : Blo 1640019 28041713 := bstep (se 2 (by rfl) ⟨10515642, by rfl⟩ : syracuseStep 28041713 = 21031285) B21031285
theorem B5538347 : Blo 1640019 5538347 := bstep (se 1 (by rfl) ⟨4153760, by rfl⟩ : syracuseStep 5538347 = 8307521) B8307521
theorem B7012925 : Blo 1640019 7012925 := bstep (se 3 (by rfl) ⟨1314923, by rfl⟩ : syracuseStep 7012925 = 2629847) B2629847
theorem B4153943 : Blo 1640019 4153943 := bstep (se 1 (by rfl) ⟨3115457, by rfl⟩ : syracuseStep 4153943 = 6230915) B6230915
theorem B3326665 : Blo 1640019 3326665 := bstep (se 2 (by rfl) ⟨1247499, by rfl⟩ : syracuseStep 3326665 = 2494999) B2494999
theorem B14025473 : Blo 1640019 14025473 := bstep (se 2 (by rfl) ⟨5259552, by rfl⟩ : syracuseStep 14025473 = 10519105) B10519105
theorem B4670237 : Blo 1640019 4670237 := bstep (se 3 (by rfl) ⟨875669, by rfl⟩ : syracuseStep 4670237 = 1751339) B1751339
theorem B5915425 : Blo 1640019 5915425 := bstep (se 2 (by rfl) ⟨2218284, by rfl⟩ : syracuseStep 5915425 = 4436569) B4436569
theorem B113722147 : Blo 1640019 113722147 := bstep (se 1 (by rfl) ⟨85291610, by rfl⟩ : syracuseStep 113722147 = 170583221) B170583221
theorem B2769707 : Blo 1640019 2769707 := bstep (se 1 (by rfl) ⟨2077280, by rfl⟩ : syracuseStep 2769707 = 4154561) B4154561
theorem B4989755 : Blo 1640019 4989755 := bstep (se 1 (by rfl) ⟨3742316, by rfl⟩ : syracuseStep 4989755 = 7484633) B7484633
theorem B23069555 : Blo 1640019 23069555 := bstep (se 1 (by rfl) ⟨17302166, by rfl⟩ : syracuseStep 23069555 = 34604333) B34604333
theorem B5612435 : Blo 1640019 5612435 := bstep (se 1 (by rfl) ⟨4209326, by rfl⟩ : syracuseStep 5612435 = 8418653) B8418653
theorem B8995907 : Blo 1640019 8995907 := bstep (se 1 (by rfl) ⟨6746930, by rfl⟩ : syracuseStep 8995907 = 13493861) B13493861
theorem B2770105 : Blo 1640019 2770105 := bstep (se 2 (by rfl) ⟨1038789, by rfl⟩ : syracuseStep 2770105 = 2077579) B2077579
theorem B6653299 : Blo 1640019 6653299 := bstep (se 1 (by rfl) ⟨4989974, by rfl⟩ : syracuseStep 6653299 = 9979949) B9979949
theorem B3114425 : Blo 1640019 3114425 := bstep (se 2 (by rfl) ⟨1167909, by rfl⟩ : syracuseStep 3114425 = 2335819) B2335819
theorem B10511801 : Blo 1640019 10511801 := bstep (se 2 (by rfl) ⟨3941925, by rfl⟩ : syracuseStep 10511801 = 7883851) B7883851
theorem B2368969 : Blo 1640019 2368969 := bstep (se 2 (by rfl) ⟨888363, by rfl⟩ : syracuseStep 2368969 = 1776727) B1776727
theorem B6227543 : Blo 1640019 6227543 := bstep (se 1 (by rfl) ⟨4670657, by rfl⟩ : syracuseStep 6227543 = 9341315) B9341315
theorem B2958967 : Blo 1640019 2958967 := bstep (se 1 (by rfl) ⟨2219225, by rfl⟩ : syracuseStep 2958967 = 4438451) B4438451
theorem B1640071 : Blo 1640019 1640071 := bstep (se 1 (by rfl) ⟨1230053, by rfl⟩ : syracuseStep 1640071 = 2460107) B2460107
theorem B1640079 : Blo 1640019 1640079 := bstep (se 1 (by rfl) ⟨1230059, by rfl⟩ : syracuseStep 1640079 = 2460119) B2460119
theorem B2025103 : Blo 1640019 2025103 := bstep (se 1 (by rfl) ⟨1518827, by rfl⟩ : syracuseStep 2025103 = 3037655) B3037655
theorem B1640123 : Blo 1640019 1640123 := bstep (se 1 (by rfl) ⟨1230092, by rfl⟩ : syracuseStep 1640123 = 2460185) B2460185
theorem B7005953 : Blo 1640019 7005953 := bstep (se 2 (by rfl) ⟨2627232, by rfl⟩ : syracuseStep 7005953 = 5254465) B5254465
theorem B1640199 : Blo 1640019 1640199 := bstep (se 1 (by rfl) ⟨1230149, by rfl⟩ : syracuseStep 1640199 = 2460299) B2460299
theorem B1640207 : Blo 1640019 1640207 := bstep (se 1 (by rfl) ⟨1230155, by rfl⟩ : syracuseStep 1640207 = 2460311) B2460311
theorem B3114767 : Blo 1640019 3114767 := bstep (se 1 (by rfl) ⟨2336075, by rfl⟩ : syracuseStep 3114767 = 4672151) B4672151
theorem B1640251 : Blo 1640019 1640251 := bstep (se 1 (by rfl) ⟨1230188, by rfl⟩ : syracuseStep 1640251 = 2460377) B2460377
theorem B5539643 : Blo 1640019 5539643 := bstep (se 1 (by rfl) ⟨4154732, by rfl⟩ : syracuseStep 5539643 = 8309465) B8309465
theorem B2770807 : Blo 1640019 2770807 := bstep (se 1 (by rfl) ⟨2078105, by rfl⟩ : syracuseStep 2770807 = 4156211) B4156211
theorem B1640327 : Blo 1640019 1640327 := bstep (se 1 (by rfl) ⟨1230245, by rfl⟩ : syracuseStep 1640327 = 2460491) B2460491
theorem B1640335 : Blo 1640019 1640335 := bstep (se 1 (by rfl) ⟨1230251, by rfl⟩ : syracuseStep 1640335 = 2460503) B2460503
theorem B1640379 : Blo 1640019 1640379 := bstep (se 1 (by rfl) ⟨1230284, by rfl⟩ : syracuseStep 1640379 = 2460569) B2460569
theorem B1640455 : Blo 1640019 1640455 := bstep (se 1 (by rfl) ⟨1230341, by rfl⟩ : syracuseStep 1640455 = 2460683) B2460683
theorem B1640463 : Blo 1640019 1640463 := bstep (se 1 (by rfl) ⟨1230347, by rfl⟩ : syracuseStep 1640463 = 2460695) B2460695
theorem B4433953 : Blo 1640019 4433953 := bstep (se 2 (by rfl) ⟨1662732, by rfl⟩ : syracuseStep 4433953 = 3325465) B3325465
theorem B1640507 : Blo 1640019 1640507 := bstep (se 1 (by rfl) ⟨1230380, by rfl⟩ : syracuseStep 1640507 = 2460761) B2460761
theorem B6228029 : Blo 1640019 6228029 := bstep (se 3 (by rfl) ⟨1167755, by rfl⟩ : syracuseStep 6228029 = 2335511) B2335511
theorem B1640583 : Blo 1640019 1640583 := bstep (se 1 (by rfl) ⟨1230437, by rfl⟩ : syracuseStep 1640583 = 2460875) B2460875
theorem B1845391 : Blo 1640019 1845391 := bstep (se 1 (by rfl) ⟨1384043, by rfl⟩ : syracuseStep 1845391 = 2768087) B2768087
theorem B1640591 : Blo 1640019 1640591 := bstep (se 1 (by rfl) ⟨1230443, by rfl⟩ : syracuseStep 1640591 = 2460887) B2460887
theorem B70969517 : Blo 1640019 70969517 := bstep (se 3 (by rfl) ⟨13306784, by rfl⟩ : syracuseStep 70969517 = 26613569) B26613569
theorem B1640635 : Blo 1640019 1640635 := bstep (se 1 (by rfl) ⟨1230476, by rfl⟩ : syracuseStep 1640635 = 2460953) B2460953
theorem B2336969 : Blo 1640019 2336969 := bstep (se 2 (by rfl) ⟨876363, by rfl⟩ : syracuseStep 2336969 = 1752727) B1752727
theorem B17737973 : Blo 1640019 17737973 := bstep (se 5 (by rfl) ⟨831467, by rfl⟩ : syracuseStep 17737973 = 1662935) B1662935
theorem B1640711 : Blo 1640019 1640711 := bstep (se 1 (by rfl) ⟨1230533, by rfl⟩ : syracuseStep 1640711 = 2461067) B2461067
theorem B1640719 : Blo 1640019 1640719 := bstep (se 1 (by rfl) ⟨1230539, by rfl⟩ : syracuseStep 1640719 = 2461079) B2461079
theorem B5540129 : Blo 1640019 5540129 := bstep (se 2 (by rfl) ⟨2077548, by rfl⟩ : syracuseStep 5540129 = 4155097) B4155097
theorem B1640763 : Blo 1640019 1640763 := bstep (se 1 (by rfl) ⟨1230572, by rfl⟩ : syracuseStep 1640763 = 2461145) B2461145
theorem B1640839 : Blo 1640019 1640839 := bstep (se 1 (by rfl) ⟨1230629, by rfl⟩ : syracuseStep 1640839 = 2461259) B2461259
theorem B2460047 : Blo 1640019 2460047 := bstep (se 1 (by rfl) ⟨1845035, by rfl⟩ : syracuseStep 2460047 = 3690071) B3690071
theorem B1640847 : Blo 1640019 1640847 := bstep (se 1 (by rfl) ⟨1230635, by rfl⟩ : syracuseStep 1640847 = 2461271) B2461271
theorem B2460089 : Blo 1640019 2460089 := bstep (se 2 (by rfl) ⟨922533, by rfl⟩ : syracuseStep 2460089 = 1845067) B1845067
theorem B1640891 : Blo 1640019 1640891 := bstep (se 1 (by rfl) ⟨1230668, by rfl⟩ : syracuseStep 1640891 = 2461337) B2461337
theorem B2460167 : Blo 1640019 2460167 := bstep (se 1 (by rfl) ⟨1845125, by rfl⟩ : syracuseStep 2460167 = 3690251) B3690251
theorem B1640967 : Blo 1640019 1640967 := bstep (se 1 (by rfl) ⟨1230725, by rfl⟩ : syracuseStep 1640967 = 2461451) B2461451
theorem B1640975 : Blo 1640019 1640975 := bstep (se 1 (by rfl) ⟨1230731, by rfl⟩ : syracuseStep 1640975 = 2461463) B2461463
theorem B2460203 : Blo 1640019 2460203 := bstep (se 1 (by rfl) ⟨1845152, by rfl⟩ : syracuseStep 2460203 = 3690305) B3690305
theorem B1641019 : Blo 1640019 1641019 := bstep (se 1 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 1641019 = 2461529) B2461529
theorem B3115579 : Blo 1640019 3115579 := bstep (se 1 (by rfl) ⟨2336684, by rfl⟩ : syracuseStep 3115579 = 4673369) B4673369
theorem B2460233 : Blo 1640019 2460233 := bstep (se 2 (by rfl) ⟨922587, by rfl⟩ : syracuseStep 2460233 = 1845175) B1845175
theorem B7883351 : Blo 1640019 7883351 := bstep (se 1 (by rfl) ⟨5912513, by rfl⟩ : syracuseStep 7883351 = 11825027) B11825027
theorem B4156019 : Blo 1640019 4156019 := bstep (se 1 (by rfl) ⟨3117014, by rfl⟩ : syracuseStep 4156019 = 6234029) B6234029
theorem B5327479 : Blo 1640019 5327479 := bstep (se 1 (by rfl) ⟨3995609, by rfl⟩ : syracuseStep 5327479 = 7991219) B7991219
theorem B6400631 : Blo 1640019 6400631 := bstep (se 1 (by rfl) ⟨4800473, by rfl⟩ : syracuseStep 6400631 = 9600947) B9600947
theorem B1845895 : Blo 1640019 1845895 := bstep (se 1 (by rfl) ⟨1384421, by rfl⟩ : syracuseStep 1845895 = 2768843) B2768843
theorem B1641095 : Blo 1640019 1641095 := bstep (se 1 (by rfl) ⟨1230821, by rfl⟩ : syracuseStep 1641095 = 2461643) B2461643
theorem B3115655 : Blo 1640019 3115655 := bstep (se 1 (by rfl) ⟨2336741, by rfl⟩ : syracuseStep 3115655 = 4673483) B4673483
theorem B1641103 : Blo 1640019 1641103 := bstep (se 1 (by rfl) ⟨1230827, by rfl⟩ : syracuseStep 1641103 = 2461655) B2461655
theorem B19950259 : Blo 1640019 19950259 := bstep (se 1 (by rfl) ⟨14962694, by rfl⟩ : syracuseStep 19950259 = 29925389) B29925389
theorem B2460347 : Blo 1640019 2460347 := bstep (se 1 (by rfl) ⟨1845260, by rfl⟩ : syracuseStep 2460347 = 3690521) B3690521
theorem B2247355 : Blo 1640019 2247355 := bstep (se 1 (by rfl) ⟨1685516, by rfl⟩ : syracuseStep 2247355 = 3371033) B3371033
theorem B1641147 : Blo 1640019 1641147 := bstep (se 1 (by rfl) ⟨1230860, by rfl⟩ : syracuseStep 1641147 = 2461721) B2461721
theorem B2460407 : Blo 1640019 2460407 := bstep (se 1 (by rfl) ⟨1845305, by rfl⟩ : syracuseStep 2460407 = 3690611) B3690611
theorem B1641223 : Blo 1640019 1641223 := bstep (se 1 (by rfl) ⟨1230917, by rfl⟩ : syracuseStep 1641223 = 2461835) B2461835
theorem B2460431 : Blo 1640019 2460431 := bstep (se 1 (by rfl) ⟨1845323, by rfl⟩ : syracuseStep 2460431 = 3690647) B3690647
theorem B1641231 : Blo 1640019 1641231 := bstep (se 1 (by rfl) ⟨1230923, by rfl⟩ : syracuseStep 1641231 = 2461847) B2461847
theorem B2460473 : Blo 1640019 2460473 := bstep (se 2 (by rfl) ⟨922677, by rfl⟩ : syracuseStep 2460473 = 1845355) B1845355
theorem B1846075 : Blo 1640019 1846075 := bstep (se 1 (by rfl) ⟨1384556, by rfl⟩ : syracuseStep 1846075 = 2769113) B2769113
theorem B1641275 : Blo 1640019 1641275 := bstep (se 1 (by rfl) ⟨1230956, by rfl⟩ : syracuseStep 1641275 = 2461913) B2461913
theorem B4672343 : Blo 1640019 4672343 := bstep (se 1 (by rfl) ⟨3504257, by rfl⟩ : syracuseStep 4672343 = 7008515) B7008515
theorem B5540723 : Blo 1640019 5540723 := bstep (se 1 (by rfl) ⟨4155542, by rfl⟩ : syracuseStep 5540723 = 8311085) B8311085
theorem B2460551 : Blo 1640019 2460551 := bstep (se 1 (by rfl) ⟨1845413, by rfl⟩ : syracuseStep 2460551 = 3690827) B3690827
theorem B1641351 : Blo 1640019 1641351 := bstep (se 1 (by rfl) ⟨1231013, by rfl⟩ : syracuseStep 1641351 = 2462027) B2462027
theorem B1641359 : Blo 1640019 1641359 := bstep (se 1 (by rfl) ⟨1231019, by rfl⟩ : syracuseStep 1641359 = 2462039) B2462039
theorem B14011289 : Blo 1640019 14011289 := bstep (se 2 (by rfl) ⟨5254233, by rfl⟩ : syracuseStep 14011289 = 10508467) B10508467
theorem B7990169 : Blo 1640019 7990169 := bstep (se 2 (by rfl) ⟨2996313, by rfl⟩ : syracuseStep 7990169 = 5992627) B5992627
theorem B2460587 : Blo 1640019 2460587 := bstep (se 1 (by rfl) ⟨1845440, by rfl⟩ : syracuseStep 2460587 = 3690881) B3690881
theorem B1641403 : Blo 1640019 1641403 := bstep (se 1 (by rfl) ⟨1231052, by rfl⟩ : syracuseStep 1641403 = 2462105) B2462105
theorem B2460617 : Blo 1640019 2460617 := bstep (se 2 (by rfl) ⟨922731, by rfl⟩ : syracuseStep 2460617 = 1845463) B1845463
theorem B1641479 : Blo 1640019 1641479 := bstep (se 1 (by rfl) ⟨1231109, by rfl⟩ : syracuseStep 1641479 = 2462219) B2462219
theorem B1641487 : Blo 1640019 1641487 := bstep (se 1 (by rfl) ⟨1231115, by rfl⟩ : syracuseStep 1641487 = 2462231) B2462231
theorem B8309789 : Blo 1640019 8309789 := bstep (se 3 (by rfl) ⟨1558085, by rfl⟩ : syracuseStep 8309789 = 3116171) B3116171
theorem B3116065 : Blo 1640019 3116065 := bstep (se 2 (by rfl) ⟨1168524, by rfl⟩ : syracuseStep 3116065 = 2337049) B2337049
theorem B2337835 : Blo 1640019 2337835 := bstep (se 1 (by rfl) ⟨1753376, by rfl⟩ : syracuseStep 2337835 = 3506753) B3506753
theorem B2460731 : Blo 1640019 2460731 := bstep (se 1 (by rfl) ⟨1845548, by rfl⟩ : syracuseStep 2460731 = 3691097) B3691097
theorem B1641531 : Blo 1640019 1641531 := bstep (se 1 (by rfl) ⟨1231148, by rfl⟩ : syracuseStep 1641531 = 2462297) B2462297
theorem B2460791 : Blo 1640019 2460791 := bstep (se 1 (by rfl) ⟨1845593, by rfl⟩ : syracuseStep 2460791 = 3691187) B3691187
theorem B1641607 : Blo 1640019 1641607 := bstep (se 1 (by rfl) ⟨1231205, by rfl⟩ : syracuseStep 1641607 = 2462411) B2462411
theorem B2460815 : Blo 1640019 2460815 := bstep (se 1 (by rfl) ⟨1845611, by rfl⟩ : syracuseStep 2460815 = 3691223) B3691223
theorem B1641615 : Blo 1640019 1641615 := bstep (se 1 (by rfl) ⟨1231211, by rfl⟩ : syracuseStep 1641615 = 2462423) B2462423
theorem B2460857 : Blo 1640019 2460857 := bstep (se 2 (by rfl) ⟨922821, by rfl⟩ : syracuseStep 2460857 = 1845643) B1845643
theorem B1641659 : Blo 1640019 1641659 := bstep (se 1 (by rfl) ⟨1231244, by rfl⟩ : syracuseStep 1641659 = 2462489) B2462489
theorem B2460935 : Blo 1640019 2460935 := bstep (se 1 (by rfl) ⟨1845701, by rfl⟩ : syracuseStep 2460935 = 3691403) B3691403
theorem B1641735 : Blo 1640019 1641735 := bstep (se 1 (by rfl) ⟨1231301, by rfl⟩ : syracuseStep 1641735 = 2462603) B2462603
theorem B1846543 : Blo 1640019 1846543 := bstep (se 1 (by rfl) ⟨1384907, by rfl⟩ : syracuseStep 1846543 = 2769815) B2769815
theorem B1641743 : Blo 1640019 1641743 := bstep (se 1 (by rfl) ⟨1231307, by rfl⟩ : syracuseStep 1641743 = 2462615) B2462615
theorem B2460971 : Blo 1640019 2460971 := bstep (se 1 (by rfl) ⟨1845728, by rfl⟩ : syracuseStep 2460971 = 3691457) B3691457
theorem B1641787 : Blo 1640019 1641787 := bstep (se 1 (by rfl) ⟨1231340, by rfl⟩ : syracuseStep 1641787 = 2462681) B2462681
theorem B2461001 : Blo 1640019 2461001 := bstep (se 2 (by rfl) ⟨922875, by rfl⟩ : syracuseStep 2461001 = 1845751) B1845751
theorem B4992371 : Blo 1640019 4992371 := bstep (se 1 (by rfl) ⟨3744278, by rfl⟩ : syracuseStep 4992371 = 7488557) B7488557
theorem B3116407 : Blo 1640019 3116407 := bstep (se 1 (by rfl) ⟨2337305, by rfl⟩ : syracuseStep 3116407 = 4674611) B4674611
theorem B33680771 : Blo 1640019 33680771 := bstep (se 1 (by rfl) ⟨25260578, by rfl⟩ : syracuseStep 33680771 = 50521157) B50521157
theorem B10513799 : Blo 1640019 10513799 := bstep (se 1 (by rfl) ⟨7885349, by rfl⟩ : syracuseStep 10513799 = 15770699) B15770699
theorem B1641863 : Blo 1640019 1641863 := bstep (se 1 (by rfl) ⟨1231397, by rfl⟩ : syracuseStep 1641863 = 2462795) B2462795
theorem B1641871 : Blo 1640019 1641871 := bstep (se 1 (by rfl) ⟨1231403, by rfl⟩ : syracuseStep 1641871 = 2462807) B2462807
theorem B2461115 : Blo 1640019 2461115 := bstep (se 1 (by rfl) ⟨1845836, by rfl⟩ : syracuseStep 2461115 = 3691673) B3691673
theorem B1641915 : Blo 1640019 1641915 := bstep (se 1 (by rfl) ⟨1231436, by rfl⟩ : syracuseStep 1641915 = 2462873) B2462873
theorem B6229457 : Blo 1640019 6229457 := bstep (se 2 (by rfl) ⟨2336046, by rfl⟩ : syracuseStep 6229457 = 4672093) B4672093
theorem B2461175 : Blo 1640019 2461175 := bstep (se 1 (by rfl) ⟨1845881, by rfl⟩ : syracuseStep 2461175 = 3691763) B3691763
theorem B8310275 : Blo 1640019 8310275 := bstep (se 1 (by rfl) ⟨6232706, by rfl⟩ : syracuseStep 8310275 = 12465413) B12465413
theorem B1641991 : Blo 1640019 1641991 := bstep (se 1 (by rfl) ⟨1231493, by rfl⟩ : syracuseStep 1641991 = 2462987) B2462987
theorem B2461199 : Blo 1640019 2461199 := bstep (se 1 (by rfl) ⟨1845899, by rfl⟩ : syracuseStep 2461199 = 3691799) B3691799
theorem B1641999 : Blo 1640019 1641999 := bstep (se 1 (by rfl) ⟨1231499, by rfl⟩ : syracuseStep 1641999 = 2462999) B2462999
theorem B2461241 : Blo 1640019 2461241 := bstep (se 2 (by rfl) ⟨922965, by rfl⟩ : syracuseStep 2461241 = 1845931) B1845931
theorem B4738679 : Blo 1640019 4738679 := bstep (se 1 (by rfl) ⟨3554009, by rfl⟩ : syracuseStep 4738679 = 7108019) B7108019
theorem B2461319 : Blo 1640019 2461319 := bstep (se 1 (by rfl) ⟨1845989, by rfl⟩ : syracuseStep 2461319 = 3691979) B3691979
theorem B2461355 : Blo 1640019 2461355 := bstep (se 1 (by rfl) ⟨1846016, by rfl⟩ : syracuseStep 2461355 = 3692033) B3692033
theorem B4673209 : Blo 1640019 4673209 := bstep (se 2 (by rfl) ⟨1752453, by rfl⟩ : syracuseStep 4673209 = 3504907) B3504907
theorem B4992697 : Blo 1640019 4992697 := bstep (se 2 (by rfl) ⟨1872261, by rfl⟩ : syracuseStep 4992697 = 3744523) B3744523
theorem B2461385 : Blo 1640019 2461385 := bstep (se 2 (by rfl) ⟨923019, by rfl⟩ : syracuseStep 2461385 = 1846039) B1846039
theorem B1847047 : Blo 1640019 1847047 := bstep (se 1 (by rfl) ⟨1385285, by rfl⟩ : syracuseStep 1847047 = 2770571) B2770571
theorem B17747747 : Blo 1640019 17747747 := bstep (se 1 (by rfl) ⟨13310810, by rfl⟩ : syracuseStep 17747747 = 26621621) B26621621
theorem B2461499 : Blo 1640019 2461499 := bstep (se 1 (by rfl) ⟨1846124, by rfl⟩ : syracuseStep 2461499 = 3692249) B3692249
theorem B3944251 : Blo 1640019 3944251 := bstep (se 1 (by rfl) ⟨2958188, by rfl⟩ : syracuseStep 3944251 = 5916377) B5916377
theorem B3690359 : Blo 1640019 3690359 := bstep (se 1 (by rfl) ⟨2767769, by rfl⟩ : syracuseStep 3690359 = 5535539) B5535539
theorem B2461559 : Blo 1640019 2461559 := bstep (se 1 (by rfl) ⟨1846169, by rfl⟩ : syracuseStep 2461559 = 3692339) B3692339
theorem B4435847 : Blo 1640019 4435847 := bstep (se 1 (by rfl) ⟨3326885, by rfl⟩ : syracuseStep 4435847 = 6653771) B6653771
theorem B2461583 : Blo 1640019 2461583 := bstep (se 1 (by rfl) ⟨1846187, by rfl⟩ : syracuseStep 2461583 = 3692375) B3692375
theorem B8867731 : Blo 1640019 8867731 := bstep (se 1 (by rfl) ⟨6650798, by rfl⟩ : syracuseStep 8867731 = 13301597) B13301597
theorem B26619799 : Blo 1640019 26619799 := bstep (se 1 (by rfl) ⟨19964849, by rfl⟩ : syracuseStep 26619799 = 39929699) B39929699
theorem B9351065 : Blo 1640019 9351065 := bstep (se 2 (by rfl) ⟨3506649, by rfl⟩ : syracuseStep 9351065 = 7013299) B7013299
theorem B2461625 : Blo 1640019 2461625 := bstep (se 2 (by rfl) ⟨923109, by rfl⟩ : syracuseStep 2461625 = 1846219) B1846219
theorem B1847227 : Blo 1640019 1847227 := bstep (se 1 (by rfl) ⟨1385420, by rfl⟩ : syracuseStep 1847227 = 2770841) B2770841
theorem B21016523 : Blo 1640019 21016523 := bstep (se 1 (by rfl) ⟨15762392, by rfl⟩ : syracuseStep 21016523 = 31524785) B31524785
theorem B17747915 : Blo 1640019 17747915 := bstep (se 1 (by rfl) ⟨13310936, by rfl⟩ : syracuseStep 17747915 = 26621873) B26621873
theorem B2461703 : Blo 1640019 2461703 := bstep (se 1 (by rfl) ⟨1846277, by rfl⟩ : syracuseStep 2461703 = 3692555) B3692555
theorem B4673551 : Blo 1640019 4673551 := bstep (se 1 (by rfl) ⟨3505163, by rfl⟩ : syracuseStep 4673551 = 7010327) B7010327
theorem B3690539 : Blo 1640019 3690539 := bstep (se 1 (by rfl) ⟨2767904, by rfl⟩ : syracuseStep 3690539 = 5535809) B5535809
theorem B2461739 : Blo 1640019 2461739 := bstep (se 1 (by rfl) ⟨1846304, by rfl⟩ : syracuseStep 2461739 = 3692609) B3692609
theorem B2461769 : Blo 1640019 2461769 := bstep (se 2 (by rfl) ⟨923163, by rfl⟩ : syracuseStep 2461769 = 1846327) B1846327
theorem B4993111 : Blo 1640019 4993111 := bstep (se 1 (by rfl) ⟨3744833, by rfl⟩ : syracuseStep 4993111 = 7489667) B7489667
theorem B4993159 : Blo 1640019 4993159 := bstep (se 1 (by rfl) ⟨3744869, by rfl⟩ : syracuseStep 4993159 = 7489739) B7489739
theorem B2461883 : Blo 1640019 2461883 := bstep (se 1 (by rfl) ⟨1846412, by rfl⟩ : syracuseStep 2461883 = 3692825) B3692825
theorem B2461943 : Blo 1640019 2461943 := bstep (se 1 (by rfl) ⟨1846457, by rfl⟩ : syracuseStep 2461943 = 3692915) B3692915
theorem B2461967 : Blo 1640019 2461967 := bstep (se 1 (by rfl) ⟨1846475, by rfl⟩ : syracuseStep 2461967 = 3692951) B3692951
theorem B4673825 : Blo 1640019 4673825 := bstep (se 2 (by rfl) ⟨1752684, by rfl⟩ : syracuseStep 4673825 = 3505369) B3505369
theorem B2462009 : Blo 1640019 2462009 := bstep (se 2 (by rfl) ⟨923253, by rfl⟩ : syracuseStep 2462009 = 1846507) B1846507
theorem B2462087 : Blo 1640019 2462087 := bstep (se 1 (by rfl) ⟨1846565, by rfl⟩ : syracuseStep 2462087 = 3693131) B3693131
theorem B71897489 : Blo 1640019 71897489 := bstep (se 2 (by rfl) ⟨26961558, by rfl⟩ : syracuseStep 71897489 = 53923117) B53923117
theorem B3690899 : Blo 1640019 3690899 := bstep (se 1 (by rfl) ⟨2768174, by rfl⟩ : syracuseStep 3690899 = 5536349) B5536349
theorem B2462123 : Blo 1640019 2462123 := bstep (se 1 (by rfl) ⟨1846592, by rfl⟩ : syracuseStep 2462123 = 3693185) B3693185
theorem B14963129 : Blo 1640019 14963129 := bstep (se 2 (by rfl) ⟨5611173, by rfl⟩ : syracuseStep 14963129 = 11222347) B11222347
theorem B3690953 : Blo 1640019 3690953 := bstep (se 2 (by rfl) ⟨1384107, by rfl⟩ : syracuseStep 3690953 = 2768215) B2768215
theorem B2462153 : Blo 1640019 2462153 := bstep (se 2 (by rfl) ⟨923307, by rfl⟩ : syracuseStep 2462153 = 1846615) B1846615
theorem B8303147 : Blo 1640019 8303147 := bstep (se 1 (by rfl) ⟨6227360, by rfl⟩ : syracuseStep 8303147 = 12454721) B12454721
theorem B2462267 : Blo 1640019 2462267 := bstep (se 1 (by rfl) ⟨1846700, by rfl⟩ : syracuseStep 2462267 = 3693401) B3693401
theorem B2462327 : Blo 1640019 2462327 := bstep (se 1 (by rfl) ⟨1846745, by rfl⟩ : syracuseStep 2462327 = 3693491) B3693491
theorem B2462351 : Blo 1640019 2462351 := bstep (se 1 (by rfl) ⟨1846763, by rfl⟩ : syracuseStep 2462351 = 3693527) B3693527
theorem B2462393 : Blo 1640019 2462393 := bstep (se 2 (by rfl) ⟨923397, by rfl⟩ : syracuseStep 2462393 = 1846795) B1846795
theorem B23646937 : Blo 1640019 23646937 := bstep (se 2 (by rfl) ⟨8867601, by rfl⟩ : syracuseStep 23646937 = 17735203) B17735203
theorem B2462471 : Blo 1640019 2462471 := bstep (se 1 (by rfl) ⟨1846853, by rfl⟩ : syracuseStep 2462471 = 3693707) B3693707
theorem B12636965 : Blo 1640019 12636965 := bstep (se 4 (by rfl) ⟨1184715, by rfl⟩ : syracuseStep 12636965 = 2369431) B2369431
theorem B2077483 : Blo 1640019 2077483 := bstep (se 1 (by rfl) ⟨1558112, by rfl⟩ : syracuseStep 2077483 = 3116225) B3116225
theorem B2462507 : Blo 1640019 2462507 := bstep (se 1 (by rfl) ⟨1846880, by rfl⟩ : syracuseStep 2462507 = 3693761) B3693761
theorem B2462537 : Blo 1640019 2462537 := bstep (se 2 (by rfl) ⟨923451, by rfl⟩ : syracuseStep 2462537 = 1846903) B1846903
theorem B4674439 : Blo 1640019 4674439 := bstep (se 1 (by rfl) ⟨3505829, by rfl⟩ : syracuseStep 4674439 = 7011659) B7011659
theorem B2462651 : Blo 1640019 2462651 := bstep (se 1 (by rfl) ⟨1846988, by rfl⟩ : syracuseStep 2462651 = 3693977) B3693977
theorem B2462711 : Blo 1640019 2462711 := bstep (se 1 (by rfl) ⟨1847033, by rfl⟩ : syracuseStep 2462711 = 3694067) B3694067
theorem B2462735 : Blo 1640019 2462735 := bstep (se 1 (by rfl) ⟨1847051, by rfl⟩ : syracuseStep 2462735 = 3694103) B3694103
theorem B2462777 : Blo 1640019 2462777 := bstep (se 2 (by rfl) ⟨923541, by rfl⟩ : syracuseStep 2462777 = 1847083) B1847083
theorem B6231127 : Blo 1640019 6231127 := bstep (se 1 (by rfl) ⟨4673345, by rfl⟩ : syracuseStep 6231127 = 9346691) B9346691
theorem B8311895 : Blo 1640019 8311895 := bstep (se 1 (by rfl) ⟨6233921, by rfl⟩ : syracuseStep 8311895 = 12467843) B12467843
theorem B1971319 : Blo 1640019 1971319 := bstep (se 1 (by rfl) ⟨1478489, by rfl⟩ : syracuseStep 1971319 = 2956979) B2956979
theorem B3691655 : Blo 1640019 3691655 := bstep (se 1 (by rfl) ⟨2768741, by rfl⟩ : syracuseStep 3691655 = 5537483) B5537483
theorem B2462855 : Blo 1640019 2462855 := bstep (se 1 (by rfl) ⟨1847141, by rfl⟩ : syracuseStep 2462855 = 3694283) B3694283
theorem B2462891 : Blo 1640019 2462891 := bstep (se 1 (by rfl) ⟨1847168, by rfl⟩ : syracuseStep 2462891 = 3694337) B3694337
theorem B2462921 : Blo 1640019 2462921 := bstep (se 2 (by rfl) ⟨923595, by rfl⟩ : syracuseStep 2462921 = 1847191) B1847191
theorem B4674827 : Blo 1640019 4674827 := bstep (se 1 (by rfl) ⟨3506120, by rfl⟩ : syracuseStep 4674827 = 7012241) B7012241
theorem B3691835 : Blo 1640019 3691835 := bstep (se 1 (by rfl) ⟨2768876, by rfl⟩ : syracuseStep 3691835 = 5537753) B5537753
theorem B6231431 : Blo 1640019 6231431 := bstep (se 1 (by rfl) ⟨4673573, by rfl⟩ : syracuseStep 6231431 = 9347147) B9347147
theorem B5535161 : Blo 1640019 5535161 := bstep (se 2 (by rfl) ⟨2075685, by rfl⟩ : syracuseStep 5535161 = 4151371) B4151371
theorem B3691961 : Blo 1640019 3691961 := bstep (se 2 (by rfl) ⟨1384485, by rfl⟩ : syracuseStep 3691961 = 2768971) B2768971
theorem B6231613 : Blo 1640019 6231613 := bstep (se 3 (by rfl) ⟨1168427, by rfl⟩ : syracuseStep 6231613 = 2336855) B2336855
theorem B8312381 : Blo 1640019 8312381 := bstep (se 3 (by rfl) ⟨1558571, by rfl⟩ : syracuseStep 8312381 = 3117143) B3117143
theorem B3692303 : Blo 1640019 3692303 := bstep (se 1 (by rfl) ⟨2769227, by rfl⟩ : syracuseStep 3692303 = 5538455) B5538455
theorem B3692321 : Blo 1640019 3692321 := bstep (se 2 (by rfl) ⟨1384620, by rfl⟩ : syracuseStep 3692321 = 2769241) B2769241
theorem B11835173 : Blo 1640019 11835173 := bstep (se 4 (by rfl) ⟨1109547, by rfl⟩ : syracuseStep 11835173 = 2219095) B2219095
theorem B4437803 : Blo 1640019 4437803 := bstep (se 1 (by rfl) ⟨3328352, by rfl⟩ : syracuseStep 4437803 = 6656705) B6656705
theorem B2627387 : Blo 1640019 2627387 := bstep (se 1 (by rfl) ⟨1970540, by rfl⟩ : syracuseStep 2627387 = 3941081) B3941081
theorem B8304443 : Blo 1640019 8304443 := bstep (se 1 (by rfl) ⟨6228332, by rfl⟩ : syracuseStep 8304443 = 12456665) B12456665
theorem B3504019 : Blo 1640019 3504019 := bstep (se 1 (by rfl) ⟨2628014, by rfl⟩ : syracuseStep 3504019 = 5256029) B5256029
theorem B9344915 : Blo 1640019 9344915 := bstep (se 1 (by rfl) ⟨7008686, by rfl⟩ : syracuseStep 9344915 = 14017373) B14017373
theorem B6313913 : Blo 1640019 6313913 := bstep (se 2 (by rfl) ⟨2367717, by rfl⟩ : syracuseStep 6313913 = 4735435) B4735435
theorem B8304605 : Blo 1640019 8304605 := bstep (se 3 (by rfl) ⟨1557113, by rfl⟩ : syracuseStep 8304605 = 3114227) B3114227
theorem B5535755 : Blo 1640019 5535755 := bstep (se 1 (by rfl) ⟨4151816, by rfl⟩ : syracuseStep 5535755 = 8303633) B8303633
theorem B5535863 : Blo 1640019 5535863 := bstep (se 1 (by rfl) ⟨4151897, by rfl⟩ : syracuseStep 5535863 = 8303795) B8303795
theorem B3692663 : Blo 1640019 3692663 := bstep (se 1 (by rfl) ⟨2769497, by rfl⟩ : syracuseStep 3692663 = 5538995) B5538995
theorem B7887041 : Blo 1640019 7887041 := bstep (se 2 (by rfl) ⟨2957640, by rfl⟩ : syracuseStep 7887041 = 5915281) B5915281
theorem B8304929 : Blo 1640019 8304929 := bstep (se 2 (by rfl) ⟨3114348, by rfl⟩ : syracuseStep 8304929 = 6228697) B6228697
theorem B3692843 : Blo 1640019 3692843 := bstep (se 1 (by rfl) ⟨2769632, by rfl⟩ : syracuseStep 3692843 = 5539265) B5539265
theorem B9345415 : Blo 1640019 9345415 := bstep (se 1 (by rfl) ⟨7009061, by rfl⟩ : syracuseStep 9345415 = 14018123) B14018123
theorem B11377219 : Blo 1640019 11377219 := bstep (se 1 (by rfl) ⟨8532914, by rfl⟩ : syracuseStep 11377219 = 17065829) B17065829
theorem B3693203 : Blo 1640019 3693203 := bstep (se 1 (by rfl) ⟨2769902, by rfl⟩ : syracuseStep 3693203 = 5539805) B5539805
theorem B5536457 : Blo 1640019 5536457 := bstep (se 2 (by rfl) ⟨2076171, by rfl⟩ : syracuseStep 5536457 = 4152343) B4152343
theorem B3693257 : Blo 1640019 3693257 := bstep (se 2 (by rfl) ⟨1384971, by rfl⟩ : syracuseStep 3693257 = 2769943) B2769943
theorem B6650657 : Blo 1640019 6650657 := bstep (se 2 (by rfl) ⟨2493996, by rfl⟩ : syracuseStep 6650657 = 4987993) B4987993
theorem B2767675 : Blo 1640019 2767675 := bstep (se 1 (by rfl) ⟨2075756, by rfl⟩ : syracuseStep 2767675 = 4151513) B4151513
theorem B18693017 : Blo 1640019 18693017 := bstep (se 2 (by rfl) ⟨7009881, by rfl⟩ : syracuseStep 18693017 = 14019763) B14019763
theorem B2767817 : Blo 1640019 2767817 := bstep (se 2 (by rfl) ⟨1037931, by rfl⟩ : syracuseStep 2767817 = 2075863) B2075863
theorem B12459095 : Blo 1640019 12459095 := bstep (se 1 (by rfl) ⟨9344321, by rfl⟩ : syracuseStep 12459095 = 18688643) B18688643
theorem B4152455 : Blo 1640019 4152455 := bstep (se 1 (by rfl) ⟨3114341, by rfl⟩ : syracuseStep 4152455 = 6228683) B6228683
theorem B4152505 : Blo 1640019 4152505 := bstep (se 2 (by rfl) ⟨1557189, by rfl⟩ : syracuseStep 4152505 = 3114379) B3114379
theorem B8305901 : Blo 1640019 8305901 := bstep (se 3 (by rfl) ⟨1557356, by rfl⟩ : syracuseStep 8305901 = 3114713) B3114713
theorem B6233345 : Blo 1640019 6233345 := bstep (se 2 (by rfl) ⟨2337504, by rfl⟩ : syracuseStep 6233345 = 4675009) B4675009
theorem B16833809 : Blo 1640019 16833809 := bstep (se 2 (by rfl) ⟨6312678, by rfl⟩ : syracuseStep 16833809 = 12625357) B12625357
theorem B7011643 : Blo 1640019 7011643 := bstep (se 1 (by rfl) ⟨5258732, by rfl⟩ : syracuseStep 7011643 = 10517465) B10517465
theorem B15777155 : Blo 1640019 15777155 := bstep (se 1 (by rfl) ⟨11832866, by rfl⟩ : syracuseStep 15777155 = 23665733) B23665733
theorem B5537159 : Blo 1640019 5537159 := bstep (se 1 (by rfl) ⟨4152869, by rfl⟩ : syracuseStep 5537159 = 8305739) B8305739
theorem B3743111 : Blo 1640019 3743111 := bstep (se 1 (by rfl) ⟨2807333, by rfl⟩ : syracuseStep 3743111 = 5614667) B5614667
theorem B3693959 : Blo 1640019 3693959 := bstep (se 1 (by rfl) ⟨2770469, by rfl⟩ : syracuseStep 3693959 = 5540939) B5540939
theorem B170548739 : Blo 1640019 170548739 := bstep (se 1 (by rfl) ⟨127911554, by rfl⟩ : syracuseStep 170548739 = 255823109) B255823109
theorem B3694139 : Blo 1640019 3694139 := bstep (se 1 (by rfl) ⟨2770604, by rfl⟩ : syracuseStep 3694139 = 5541209) B5541209
theorem B2768519 : Blo 1640019 2768519 := bstep (se 1 (by rfl) ⟨2076389, by rfl⟩ : syracuseStep 2768519 = 4152779) B4152779
theorem B3694265 : Blo 1640019 3694265 := bstep (se 2 (by rfl) ⟨1385349, by rfl⟩ : syracuseStep 3694265 = 2770699) B2770699
theorem B5537537 : Blo 1640019 5537537 := bstep (se 2 (by rfl) ⟨2076576, by rfl⟩ : syracuseStep 5537537 = 4153153) B4153153
theorem B4153103 : Blo 1640019 4153103 := bstep (se 1 (by rfl) ⟨3114827, by rfl⟩ : syracuseStep 4153103 = 6229655) B6229655
theorem B5259143 : Blo 1640019 5259143 := bstep (se 1 (by rfl) ⟨3944357, by rfl⟩ : syracuseStep 5259143 = 7888715) B7888715
theorem B5537807 : Blo 1640019 5537807 := bstep (se 1 (by rfl) ⟨4153355, by rfl⟩ : syracuseStep 5537807 = 8306711) B8306711
theorem B5914819 : Blo 1640019 5914819 := bstep (se 1 (by rfl) ⟨4436114, by rfl⟩ : syracuseStep 5914819 = 8872229) B8872229
theorem B47931659 : Blo 1640019 47931659 := bstep (se 1 (by rfl) ⟨35948744, by rfl⟩ : syracuseStep 47931659 = 71897489) B71897489
theorem B18694475 : Blo 1640019 18694475 := bstep (se 1 (by rfl) ⟨14020856, by rfl⟩ : syracuseStep 18694475 = 28041713) B28041713
theorem B2769295 : Blo 1640019 2769295 := bstep (se 1 (by rfl) ⟨2076971, by rfl⟩ : syracuseStep 2769295 = 4153943) B4153943
theorem B12460553 : Blo 1640019 12460553 := bstep (se 2 (by rfl) ⟨4672707, by rfl⟩ : syracuseStep 12460553 = 9345415) B9345415
theorem B3113491 : Blo 1640019 3113491 := bstep (se 1 (by rfl) ⟨2335118, by rfl⟩ : syracuseStep 3113491 = 4670237) B4670237
theorem B7012889 : Blo 1640019 7012889 := bstep (se 2 (by rfl) ⟨2629833, by rfl⟩ : syracuseStep 7012889 = 5259667) B5259667
theorem B3326503 : Blo 1640019 3326503 := bstep (se 1 (by rfl) ⟨2494877, by rfl⟩ : syracuseStep 3326503 = 4989755) B4989755
theorem B5538401 : Blo 1640019 5538401 := bstep (se 2 (by rfl) ⟨2076900, by rfl⟩ : syracuseStep 5538401 = 4153801) B4153801
theorem B4154105 : Blo 1640019 4154105 := bstep (se 2 (by rfl) ⟨1557789, by rfl⟩ : syracuseStep 4154105 = 3115579) B3115579
theorem B7103305 : Blo 1640019 7103305 := bstep (se 2 (by rfl) ⟨2663739, by rfl⟩ : syracuseStep 7103305 = 5327479) B5327479
theorem B26600345 : Blo 1640019 26600345 := bstep (se 2 (by rfl) ⟨9975129, by rfl⟩ : syracuseStep 26600345 = 19950259) B19950259
theorem B4154287 : Blo 1640019 4154287 := bstep (se 1 (by rfl) ⟨3115715, by rfl⟩ : syracuseStep 4154287 = 6231431) B6231431
theorem B11985893 : Blo 1640019 11985893 := bstep (se 4 (by rfl) ⟨1123677, by rfl⟩ : syracuseStep 11985893 = 2247355) B2247355
theorem B2769977 : Blo 1640019 2769977 := bstep (se 2 (by rfl) ⟨1038741, by rfl⟩ : syracuseStep 2769977 = 2077483) B2077483
theorem B4670635 : Blo 1640019 4670635 := bstep (se 1 (by rfl) ⟨3502976, by rfl⟩ : syracuseStep 4670635 = 7005953) B7005953
theorem B2958535 : Blo 1640019 2958535 := bstep (se 1 (by rfl) ⟨2218901, by rfl⟩ : syracuseStep 2958535 = 4437803) B4437803
theorem B4154753 : Blo 1640019 4154753 := bstep (se 2 (by rfl) ⟨1558032, by rfl⟩ : syracuseStep 4154753 = 3116065) B3116065
theorem B8308169 : Blo 1640019 8308169 := bstep (se 2 (by rfl) ⟨3115563, by rfl⟩ : syracuseStep 8308169 = 6231127) B6231127
theorem B1640031 : Blo 1640019 1640031 := bstep (se 1 (by rfl) ⟨1230023, by rfl⟩ : syracuseStep 1640031 = 2460047) B2460047
theorem B1640059 : Blo 1640019 1640059 := bstep (se 1 (by rfl) ⟨1230044, by rfl⟩ : syracuseStep 1640059 = 2460089) B2460089
theorem B1640111 : Blo 1640019 1640111 := bstep (se 1 (by rfl) ⟨1230083, by rfl⟩ : syracuseStep 1640111 = 2460167) B2460167
theorem B1640135 : Blo 1640019 1640135 := bstep (se 1 (by rfl) ⟨1230101, by rfl⟩ : syracuseStep 1640135 = 2460203) B2460203
theorem B1640155 : Blo 1640019 1640155 := bstep (se 1 (by rfl) ⟨1230116, by rfl⟩ : syracuseStep 1640155 = 2460233) B2460233
theorem B2770679 : Blo 1640019 2770679 := bstep (se 1 (by rfl) ⟨2078009, by rfl⟩ : syracuseStep 2770679 = 4156019) B4156019
theorem B9348857 : Blo 1640019 9348857 := bstep (se 2 (by rfl) ⟨3505821, by rfl⟩ : syracuseStep 9348857 = 7011643) B7011643
theorem B1640231 : Blo 1640019 1640231 := bstep (se 1 (by rfl) ⟨1230173, by rfl⟩ : syracuseStep 1640231 = 2460347) B2460347
theorem B4155209 : Blo 1640019 4155209 := bstep (se 2 (by rfl) ⟨1558203, by rfl⟩ : syracuseStep 4155209 = 3116407) B3116407
theorem B1640271 : Blo 1640019 1640271 := bstep (se 1 (by rfl) ⟨1230203, by rfl⟩ : syracuseStep 1640271 = 2460407) B2460407
theorem B1640287 : Blo 1640019 1640287 := bstep (se 1 (by rfl) ⟨1230215, by rfl⟩ : syracuseStep 1640287 = 2460431) B2460431
theorem B4433771 : Blo 1640019 4433771 := bstep (se 1 (by rfl) ⟨3325328, by rfl⟩ : syracuseStep 4433771 = 6650657) B6650657
theorem B1640315 : Blo 1640019 1640315 := bstep (se 1 (by rfl) ⟨1230236, by rfl⟩ : syracuseStep 1640315 = 2460473) B2460473
theorem B1640367 : Blo 1640019 1640367 := bstep (se 1 (by rfl) ⟨1230275, by rfl⟩ : syracuseStep 1640367 = 2460551) B2460551
theorem B9340859 : Blo 1640019 9340859 := bstep (se 1 (by rfl) ⟨7005644, by rfl⟩ : syracuseStep 9340859 = 14011289) B14011289
theorem B12462011 : Blo 1640019 12462011 := bstep (se 1 (by rfl) ⟨9346508, by rfl⟩ : syracuseStep 12462011 = 18693017) B18693017
theorem B1640391 : Blo 1640019 1640391 := bstep (se 1 (by rfl) ⟨1230293, by rfl⟩ : syracuseStep 1640391 = 2460587) B2460587
theorem B1845211 : Blo 1640019 1845211 := bstep (se 1 (by rfl) ⟨1383908, by rfl⟩ : syracuseStep 1845211 = 2767817) B2767817
theorem B1640411 : Blo 1640019 1640411 := bstep (se 1 (by rfl) ⟨1230308, by rfl⟩ : syracuseStep 1640411 = 2460617) B2460617
theorem B5539859 : Blo 1640019 5539859 := bstep (se 1 (by rfl) ⟨4154894, by rfl⟩ : syracuseStep 5539859 = 8309789) B8309789
theorem B1640487 : Blo 1640019 1640487 := bstep (se 1 (by rfl) ⟨1230365, by rfl⟩ : syracuseStep 1640487 = 2460731) B2460731
theorem B1640527 : Blo 1640019 1640527 := bstep (se 1 (by rfl) ⟨1230395, by rfl⟩ : syracuseStep 1640527 = 2460791) B2460791
theorem B8308817 : Blo 1640019 8308817 := bstep (se 2 (by rfl) ⟨3115806, by rfl⟩ : syracuseStep 8308817 = 6231613) B6231613
theorem B1640543 : Blo 1640019 1640543 := bstep (se 1 (by rfl) ⟨1230407, by rfl⟩ : syracuseStep 1640543 = 2460815) B2460815
theorem B1640571 : Blo 1640019 1640571 := bstep (se 1 (by rfl) ⟨1230428, by rfl⟩ : syracuseStep 1640571 = 2460857) B2460857
theorem B4155563 : Blo 1640019 4155563 := bstep (se 1 (by rfl) ⟨3116672, by rfl⟩ : syracuseStep 4155563 = 6233345) B6233345
theorem B1640623 : Blo 1640019 1640623 := bstep (se 1 (by rfl) ⟨1230467, by rfl⟩ : syracuseStep 1640623 = 2460935) B2460935
theorem B1640647 : Blo 1640019 1640647 := bstep (se 1 (by rfl) ⟨1230485, by rfl⟩ : syracuseStep 1640647 = 2460971) B2460971
theorem B1640667 : Blo 1640019 1640667 := bstep (se 1 (by rfl) ⟨1230500, by rfl⟩ : syracuseStep 1640667 = 2461001) B2461001
theorem B3328247 : Blo 1640019 3328247 := bstep (se 1 (by rfl) ⟨2496185, by rfl⟩ : syracuseStep 3328247 = 4992371) B4992371
theorem B1640743 : Blo 1640019 1640743 := bstep (se 1 (by rfl) ⟨1230557, by rfl⟩ : syracuseStep 1640743 = 2461115) B2461115
theorem B1640783 : Blo 1640019 1640783 := bstep (se 1 (by rfl) ⟨1230587, by rfl⟩ : syracuseStep 1640783 = 2461175) B2461175
theorem B113699159 : Blo 1640019 113699159 := bstep (se 1 (by rfl) ⟨85274369, by rfl⟩ : syracuseStep 113699159 = 170548739) B170548739
theorem B5540183 : Blo 1640019 5540183 := bstep (se 1 (by rfl) ⟨4155137, by rfl⟩ : syracuseStep 5540183 = 8310275) B8310275
theorem B1640799 : Blo 1640019 1640799 := bstep (se 1 (by rfl) ⟨1230599, by rfl⟩ : syracuseStep 1640799 = 2461199) B2461199
theorem B1640827 : Blo 1640019 1640827 := bstep (se 1 (by rfl) ⟨1230620, by rfl⟩ : syracuseStep 1640827 = 2461241) B2461241
theorem B12634501 : Blo 1640019 12634501 := bstep (se 4 (by rfl) ⟨1184484, by rfl⟩ : syracuseStep 12634501 = 2368969) B2368969
theorem B1845679 : Blo 1640019 1845679 := bstep (se 1 (by rfl) ⟨1384259, by rfl⟩ : syracuseStep 1845679 = 2768519) B2768519
theorem B1640879 : Blo 1640019 1640879 := bstep (se 1 (by rfl) ⟨1230659, by rfl⟩ : syracuseStep 1640879 = 2461319) B2461319
theorem B1640903 : Blo 1640019 1640903 := bstep (se 1 (by rfl) ⟨1230677, by rfl⟩ : syracuseStep 1640903 = 2461355) B2461355
theorem B1640923 : Blo 1640019 1640923 := bstep (se 1 (by rfl) ⟨1230692, by rfl⟩ : syracuseStep 1640923 = 2461385) B2461385
theorem B11831831 : Blo 1640019 11831831 := bstep (se 1 (by rfl) ⟨8873873, by rfl⟩ : syracuseStep 11831831 = 17747747) B17747747
theorem B11823641 : Blo 1640019 11823641 := bstep (se 2 (by rfl) ⟨4433865, by rfl⟩ : syracuseStep 11823641 = 8867731) B8867731
theorem B4672025 : Blo 1640019 4672025 := bstep (se 2 (by rfl) ⟨1752009, by rfl⟩ : syracuseStep 4672025 = 3504019) B3504019
theorem B47327773 : Blo 1640019 47327773 := bstep (se 3 (by rfl) ⟨8873957, by rfl⟩ : syracuseStep 47327773 = 17747915) B17747915
theorem B1640999 : Blo 1640019 1640999 := bstep (se 1 (by rfl) ⟨1230749, by rfl⟩ : syracuseStep 1640999 = 2461499) B2461499
theorem B2460239 : Blo 1640019 2460239 := bstep (se 1 (by rfl) ⟨1845179, by rfl⟩ : syracuseStep 2460239 = 3690359) B3690359
theorem B1641039 : Blo 1640019 1641039 := bstep (se 1 (by rfl) ⟨1230779, by rfl⟩ : syracuseStep 1641039 = 2461559) B2461559
theorem B1641055 : Blo 1640019 1641055 := bstep (se 1 (by rfl) ⟨1230791, by rfl⟩ : syracuseStep 1641055 = 2461583) B2461583
theorem B1641083 : Blo 1640019 1641083 := bstep (se 1 (by rfl) ⟨1230812, by rfl⟩ : syracuseStep 1641083 = 2461625) B2461625
theorem B14011015 : Blo 1640019 14011015 := bstep (se 1 (by rfl) ⟨10508261, by rfl⟩ : syracuseStep 14011015 = 21016523) B21016523
theorem B1641135 : Blo 1640019 1641135 := bstep (se 1 (by rfl) ⟨1230851, by rfl⟩ : syracuseStep 1641135 = 2461703) B2461703
theorem B2460359 : Blo 1640019 2460359 := bstep (se 1 (by rfl) ⟨1845269, by rfl⟩ : syracuseStep 2460359 = 3690539) B3690539
theorem B1641159 : Blo 1640019 1641159 := bstep (se 1 (by rfl) ⟨1230869, by rfl⟩ : syracuseStep 1641159 = 2461739) B2461739
theorem B3943127 : Blo 1640019 3943127 := bstep (se 1 (by rfl) ⟨2957345, by rfl⟩ : syracuseStep 3943127 = 5914691) B5914691
theorem B1641179 : Blo 1640019 1641179 := bstep (se 1 (by rfl) ⟨1230884, by rfl⟩ : syracuseStep 1641179 = 2461769) B2461769
theorem B1641255 : Blo 1640019 1641255 := bstep (se 1 (by rfl) ⟨1230941, by rfl⟩ : syracuseStep 1641255 = 2461883) B2461883
theorem B1641295 : Blo 1640019 1641295 := bstep (se 1 (by rfl) ⟨1230971, by rfl⟩ : syracuseStep 1641295 = 2461943) B2461943
theorem B23989085 : Blo 1640019 23989085 := bstep (se 3 (by rfl) ⟨4497953, by rfl⟩ : syracuseStep 23989085 = 8995907) B8995907
theorem B1846111 : Blo 1640019 1846111 := bstep (se 1 (by rfl) ⟨1384583, by rfl⟩ : syracuseStep 1846111 = 2769167) B2769167
theorem B1641311 : Blo 1640019 1641311 := bstep (se 1 (by rfl) ⟨1230983, by rfl⟩ : syracuseStep 1641311 = 2461967) B2461967
theorem B2460521 : Blo 1640019 2460521 := bstep (se 2 (by rfl) ⟨922695, by rfl⟩ : syracuseStep 2460521 = 1845391) B1845391
theorem B3115883 : Blo 1640019 3115883 := bstep (se 1 (by rfl) ⟨2336912, by rfl⟩ : syracuseStep 3115883 = 4673825) B4673825
theorem B1641339 : Blo 1640019 1641339 := bstep (se 1 (by rfl) ⟨1231004, by rfl⟩ : syracuseStep 1641339 = 2462009) B2462009
theorem B1641391 : Blo 1640019 1641391 := bstep (se 1 (by rfl) ⟨1231043, by rfl⟩ : syracuseStep 1641391 = 2462087) B2462087
theorem B9350063 : Blo 1640019 9350063 := bstep (se 1 (by rfl) ⟨7012547, by rfl⟩ : syracuseStep 9350063 = 14025095) B14025095
theorem B2460599 : Blo 1640019 2460599 := bstep (se 1 (by rfl) ⟨1845449, by rfl⟩ : syracuseStep 2460599 = 3690899) B3690899
theorem B4156343 : Blo 1640019 4156343 := bstep (se 1 (by rfl) ⟨3117257, by rfl⟩ : syracuseStep 4156343 = 6234515) B6234515
theorem B1641415 : Blo 1640019 1641415 := bstep (se 1 (by rfl) ⟨1231061, by rfl⟩ : syracuseStep 1641415 = 2462123) B2462123
theorem B2460635 : Blo 1640019 2460635 := bstep (se 1 (by rfl) ⟨1845476, by rfl⟩ : syracuseStep 2460635 = 3690953) B3690953
theorem B1641435 : Blo 1640019 1641435 := bstep (se 1 (by rfl) ⟨1231076, by rfl⟩ : syracuseStep 1641435 = 2462153) B2462153
theorem B1641511 : Blo 1640019 1641511 := bstep (se 1 (by rfl) ⟨1231133, by rfl⟩ : syracuseStep 1641511 = 2462267) B2462267
theorem B1641551 : Blo 1640019 1641551 := bstep (se 1 (by rfl) ⟨1231163, by rfl⟩ : syracuseStep 1641551 = 2462327) B2462327
theorem B1641567 : Blo 1640019 1641567 := bstep (se 1 (by rfl) ⟨1231175, by rfl⟩ : syracuseStep 1641567 = 2462351) B2462351
theorem B1641595 : Blo 1640019 1641595 := bstep (se 1 (by rfl) ⟨1231196, by rfl⟩ : syracuseStep 1641595 = 2462393) B2462393
theorem B9350315 : Blo 1640019 9350315 := bstep (se 1 (by rfl) ⟨7012736, by rfl⟩ : syracuseStep 9350315 = 14025473) B14025473
theorem B1641647 : Blo 1640019 1641647 := bstep (se 1 (by rfl) ⟨1231235, by rfl⟩ : syracuseStep 1641647 = 2462471) B2462471
theorem B8424643 : Blo 1640019 8424643 := bstep (se 1 (by rfl) ⟨6318482, by rfl⟩ : syracuseStep 8424643 = 12636965) B12636965
theorem B1846471 : Blo 1640019 1846471 := bstep (se 1 (by rfl) ⟨1384853, by rfl⟩ : syracuseStep 1846471 = 2769707) B2769707
theorem B1641671 : Blo 1640019 1641671 := bstep (se 1 (by rfl) ⟨1231253, by rfl⟩ : syracuseStep 1641671 = 2462507) B2462507
theorem B1641691 : Blo 1640019 1641691 := bstep (se 1 (by rfl) ⟨1231268, by rfl⟩ : syracuseStep 1641691 = 2462537) B2462537
theorem B15379703 : Blo 1640019 15379703 := bstep (se 1 (by rfl) ⟨11534777, by rfl⟩ : syracuseStep 15379703 = 23069555) B23069555
theorem B1641767 : Blo 1640019 1641767 := bstep (se 1 (by rfl) ⟨1231325, by rfl⟩ : syracuseStep 1641767 = 2462651) B2462651
theorem B1641807 : Blo 1640019 1641807 := bstep (se 1 (by rfl) ⟨1231355, by rfl⟩ : syracuseStep 1641807 = 2462711) B2462711
theorem B1641823 : Blo 1640019 1641823 := bstep (se 1 (by rfl) ⟨1231367, by rfl⟩ : syracuseStep 1641823 = 2462735) B2462735
theorem B1641851 : Blo 1640019 1641851 := bstep (se 1 (by rfl) ⟨1231388, by rfl⟩ : syracuseStep 1641851 = 2462777) B2462777
theorem B5541263 : Blo 1640019 5541263 := bstep (se 1 (by rfl) ⟨4155947, by rfl⟩ : syracuseStep 5541263 = 8311895) B8311895
theorem B2461103 : Blo 1640019 2461103 := bstep (se 1 (by rfl) ⟨1845827, by rfl⟩ : syracuseStep 2461103 = 3691655) B3691655
theorem B1641903 : Blo 1640019 1641903 := bstep (se 1 (by rfl) ⟨1231427, by rfl⟩ : syracuseStep 1641903 = 2462855) B2462855
theorem B1641927 : Blo 1640019 1641927 := bstep (se 1 (by rfl) ⟨1231445, by rfl⟩ : syracuseStep 1641927 = 2462891) B2462891
theorem B1641947 : Blo 1640019 1641947 := bstep (se 1 (by rfl) ⟨1231460, by rfl⟩ : syracuseStep 1641947 = 2462921) B2462921
theorem B3116551 : Blo 1640019 3116551 := bstep (se 1 (by rfl) ⟨2337413, by rfl⟩ : syracuseStep 3116551 = 4674827) B4674827
theorem B2461193 : Blo 1640019 2461193 := bstep (se 2 (by rfl) ⟨922947, by rfl⟩ : syracuseStep 2461193 = 1845895) B1845895
theorem B2461223 : Blo 1640019 2461223 := bstep (se 1 (by rfl) ⟨1845917, by rfl⟩ : syracuseStep 2461223 = 3691835) B3691835
theorem B4435553 : Blo 1640019 4435553 := bstep (se 2 (by rfl) ⟨1663332, by rfl⟩ : syracuseStep 4435553 = 3326665) B3326665
theorem B3690107 : Blo 1640019 3690107 := bstep (se 1 (by rfl) ⟨2767580, by rfl⟩ : syracuseStep 3690107 = 5535161) B5535161
theorem B2076283 : Blo 1640019 2076283 := bstep (se 1 (by rfl) ⟨1557212, by rfl⟩ : syracuseStep 2076283 = 3114425) B3114425
theorem B7007867 : Blo 1640019 7007867 := bstep (se 1 (by rfl) ⟨5255900, by rfl⟩ : syracuseStep 7007867 = 10511801) B10511801
theorem B2461307 : Blo 1640019 2461307 := bstep (se 1 (by rfl) ⟨1845980, by rfl⟩ : syracuseStep 2461307 = 3691961) B3691961
theorem B26627717 : Blo 1640019 26627717 := bstep (se 4 (by rfl) ⟨2496348, by rfl⟩ : syracuseStep 26627717 = 4992697) B4992697
theorem B9981629 : Blo 1640019 9981629 := bstep (se 3 (by rfl) ⟨1871555, by rfl⟩ : syracuseStep 9981629 = 3743111) B3743111
theorem B5541587 : Blo 1640019 5541587 := bstep (se 1 (by rfl) ⟨4156190, by rfl⟩ : syracuseStep 5541587 = 8312381) B8312381
theorem B151629529 : Blo 1640019 151629529 := bstep (se 2 (by rfl) ⟨56861073, by rfl⟩ : syracuseStep 151629529 = 113722147) B113722147
theorem B3690233 : Blo 1640019 3690233 := bstep (se 2 (by rfl) ⟨1383837, by rfl⟩ : syracuseStep 3690233 = 2767675) B2767675
theorem B2461433 : Blo 1640019 2461433 := bstep (se 2 (by rfl) ⟨923037, by rfl⟩ : syracuseStep 2461433 = 1846075) B1846075
theorem B2076511 : Blo 1640019 2076511 := bstep (se 1 (by rfl) ⟨1557383, by rfl⟩ : syracuseStep 2076511 = 3114767) B3114767
theorem B2461535 : Blo 1640019 2461535 := bstep (se 1 (by rfl) ⟨1846151, by rfl⟩ : syracuseStep 2461535 = 3692303) B3692303
theorem B2461547 : Blo 1640019 2461547 := bstep (se 1 (by rfl) ⟨1846160, by rfl⟩ : syracuseStep 2461547 = 3692321) B3692321
theorem B6229943 : Blo 1640019 6229943 := bstep (se 1 (by rfl) ⟨4672457, by rfl⟩ : syracuseStep 6229943 = 9344915) B9344915
theorem B3690503 : Blo 1640019 3690503 := bstep (se 1 (by rfl) ⟨2767877, by rfl⟩ : syracuseStep 3690503 = 5535755) B5535755
theorem B3117113 : Blo 1640019 3117113 := bstep (se 2 (by rfl) ⟨1168917, by rfl⟩ : syracuseStep 3117113 = 2337835) B2337835
theorem B3690575 : Blo 1640019 3690575 := bstep (se 1 (by rfl) ⟨2767931, by rfl⟩ : syracuseStep 3690575 = 5535863) B5535863
theorem B2461775 : Blo 1640019 2461775 := bstep (se 1 (by rfl) ⟨1846331, by rfl⟩ : syracuseStep 2461775 = 3692663) B3692663
theorem B47313011 : Blo 1640019 47313011 := bstep (se 1 (by rfl) ⟨35484758, by rfl⟩ : syracuseStep 47313011 = 70969517) B70969517
theorem B11825315 : Blo 1640019 11825315 := bstep (se 1 (by rfl) ⟨8868986, by rfl⟩ : syracuseStep 11825315 = 17737973) B17737973
theorem B2461895 : Blo 1640019 2461895 := bstep (se 1 (by rfl) ⟨1846421, by rfl⟩ : syracuseStep 2461895 = 3692843) B3692843
theorem B2462057 : Blo 1640019 2462057 := bstep (se 2 (by rfl) ⟨923271, by rfl⟩ : syracuseStep 2462057 = 1846543) B1846543
theorem B5255567 : Blo 1640019 5255567 := bstep (se 1 (by rfl) ⟨3941675, by rfl⟩ : syracuseStep 5255567 = 7883351) B7883351
theorem B2077103 : Blo 1640019 2077103 := bstep (se 1 (by rfl) ⟨1557827, by rfl⟩ : syracuseStep 2077103 = 3115655) B3115655
theorem B2462135 : Blo 1640019 2462135 := bstep (se 1 (by rfl) ⟨1846601, by rfl⟩ : syracuseStep 2462135 = 3693203) B3693203
theorem B3690971 : Blo 1640019 3690971 := bstep (se 1 (by rfl) ⟨2768228, by rfl⟩ : syracuseStep 3690971 = 5536457) B5536457
theorem B2462171 : Blo 1640019 2462171 := bstep (se 1 (by rfl) ⟨1846628, by rfl⟩ : syracuseStep 2462171 = 3693257) B3693257
theorem B31560461 : Blo 1640019 31560461 := bstep (se 3 (by rfl) ⟨5917586, by rfl⟩ : syracuseStep 31560461 = 11835173) B11835173
theorem B3945289 : Blo 1640019 3945289 := bstep (se 2 (by rfl) ⟨1479483, by rfl⟩ : syracuseStep 3945289 = 2958967) B2958967
theorem B2700137 : Blo 1640019 2700137 := bstep (se 2 (by rfl) ⟨1012551, by rfl⟩ : syracuseStep 2700137 = 2025103) B2025103
theorem B6230945 : Blo 1640019 6230945 := bstep (se 2 (by rfl) ⟨2336604, by rfl⟩ : syracuseStep 6230945 = 4673209) B4673209
theorem B3691439 : Blo 1640019 3691439 := bstep (se 1 (by rfl) ⟨2768579, by rfl⟩ : syracuseStep 3691439 = 5537159) B5537159
theorem B7009199 : Blo 1640019 7009199 := bstep (se 1 (by rfl) ⟨5256899, by rfl⟩ : syracuseStep 7009199 = 10513799) B10513799
theorem B2462639 : Blo 1640019 2462639 := bstep (se 1 (by rfl) ⟨1846979, by rfl⟩ : syracuseStep 2462639 = 3693959) B3693959
theorem B2462729 : Blo 1640019 2462729 := bstep (se 2 (by rfl) ⟨923523, by rfl⟩ : syracuseStep 2462729 = 1847047) B1847047
theorem B2462759 : Blo 1640019 2462759 := bstep (se 1 (by rfl) ⟨1847069, by rfl⟩ : syracuseStep 2462759 = 3694139) B3694139
theorem B3159119 : Blo 1640019 3159119 := bstep (se 1 (by rfl) ⟨2369339, by rfl⟩ : syracuseStep 3159119 = 4738679) B4738679
theorem B2462843 : Blo 1640019 2462843 := bstep (se 1 (by rfl) ⟨1847132, by rfl⟩ : syracuseStep 2462843 = 3694265) B3694265
theorem B3691691 : Blo 1640019 3691691 := bstep (se 1 (by rfl) ⟨2768768, by rfl⟩ : syracuseStep 3691691 = 5537537) B5537537
theorem B35493065 : Blo 1640019 35493065 := bstep (se 2 (by rfl) ⟨13309899, by rfl⟩ : syracuseStep 35493065 = 26619799) B26619799
theorem B2462969 : Blo 1640019 2462969 := bstep (se 2 (by rfl) ⟨923613, by rfl⟩ : syracuseStep 2462969 = 1847227) B1847227
theorem B6231401 : Blo 1640019 6231401 := bstep (se 2 (by rfl) ⟨2336775, by rfl⟩ : syracuseStep 6231401 = 4673551) B4673551
theorem B4674941 : Blo 1640019 4674941 := bstep (se 3 (by rfl) ⟨876551, by rfl⟩ : syracuseStep 4674941 = 1753103) B1753103
theorem B5911937 : Blo 1640019 5911937 := bstep (se 2 (by rfl) ⟨2216976, by rfl⟩ : syracuseStep 5911937 = 4433953) B4433953
theorem B6657481 : Blo 1640019 6657481 := bstep (se 2 (by rfl) ⟨2496555, by rfl⟩ : syracuseStep 6657481 = 4993111) B4993111
theorem B6657545 : Blo 1640019 6657545 := bstep (se 2 (by rfl) ⟨2496579, by rfl⟩ : syracuseStep 6657545 = 4993159) B4993159
theorem B2627111 : Blo 1640019 2627111 := bstep (se 1 (by rfl) ⟨1970333, by rfl⟩ : syracuseStep 2627111 = 3940667) B3940667
theorem B9975419 : Blo 1640019 9975419 := bstep (se 1 (by rfl) ⟨7481564, by rfl⟩ : syracuseStep 9975419 = 14963129) B14963129
theorem B5535431 : Blo 1640019 5535431 := bstep (se 1 (by rfl) ⟨4151573, by rfl⟩ : syracuseStep 5535431 = 8303147) B8303147
theorem B3692231 : Blo 1640019 3692231 := bstep (se 1 (by rfl) ⟨2769173, by rfl⟩ : syracuseStep 3692231 = 5538347) B5538347
theorem B4675283 : Blo 1640019 4675283 := bstep (se 1 (by rfl) ⟨3506462, by rfl⟩ : syracuseStep 4675283 = 7012925) B7012925
theorem B6231917 : Blo 1640019 6231917 := bstep (se 3 (by rfl) ⟨1168484, by rfl⟩ : syracuseStep 6231917 = 2336969) B2336969
theorem B3741623 : Blo 1640019 3741623 := bstep (se 1 (by rfl) ⟨2806217, by rfl⟩ : syracuseStep 3741623 = 5612435) B5612435
theorem B44890157 : Blo 1640019 44890157 := bstep (se 3 (by rfl) ⟨8416904, by rfl⟩ : syracuseStep 44890157 = 16833809) B16833809
theorem B15169625 : Blo 1640019 15169625 := bstep (se 2 (by rfl) ⟨5688609, by rfl⟩ : syracuseStep 15169625 = 11377219) B11377219
theorem B31529249 : Blo 1640019 31529249 := bstep (se 2 (by rfl) ⟨11823468, by rfl⟩ : syracuseStep 31529249 = 23646937) B23646937
theorem B7887233 : Blo 1640019 7887233 := bstep (se 2 (by rfl) ⟨2957712, by rfl⟩ : syracuseStep 7887233 = 5915425) B5915425
theorem B4151695 : Blo 1640019 4151695 := bstep (se 1 (by rfl) ⟨3113771, by rfl⟩ : syracuseStep 4151695 = 6227543) B6227543
theorem B6232585 : Blo 1640019 6232585 := bstep (se 2 (by rfl) ⟨2337219, by rfl⟩ : syracuseStep 6232585 = 4674439) B4674439
theorem B1751591 : Blo 1640019 1751591 := bstep (se 1 (by rfl) ⟨1313693, by rfl⟩ : syracuseStep 1751591 = 2627387) B2627387
theorem B5536295 : Blo 1640019 5536295 := bstep (se 1 (by rfl) ⟨4152221, by rfl⟩ : syracuseStep 5536295 = 8304443) B8304443
theorem B3693095 : Blo 1640019 3693095 := bstep (se 1 (by rfl) ⟨2769821, by rfl⟩ : syracuseStep 3693095 = 5539643) B5539643
theorem B4209275 : Blo 1640019 4209275 := bstep (se 1 (by rfl) ⟨3156956, by rfl⟩ : syracuseStep 4209275 = 6313913) B6313913
theorem B5536403 : Blo 1640019 5536403 := bstep (se 1 (by rfl) ⟨4152302, by rfl⟩ : syracuseStep 5536403 = 8304605) B8304605
theorem B4152019 : Blo 1640019 4152019 := bstep (se 1 (by rfl) ⟨3114014, by rfl⟩ : syracuseStep 4152019 = 6228029) B6228029
theorem B5258027 : Blo 1640019 5258027 := bstep (se 1 (by rfl) ⟨3943520, by rfl⟩ : syracuseStep 5258027 = 7887041) B7887041
theorem B2628425 : Blo 1640019 2628425 := bstep (se 2 (by rfl) ⟨985659, by rfl⟩ : syracuseStep 2628425 = 1971319) B1971319
theorem B5536619 : Blo 1640019 5536619 := bstep (se 1 (by rfl) ⟨4152464, by rfl⟩ : syracuseStep 5536619 = 8304929) B8304929
theorem B3693419 : Blo 1640019 3693419 := bstep (se 1 (by rfl) ⟨2770064, by rfl⟩ : syracuseStep 3693419 = 5540129) B5540129
theorem B5536673 : Blo 1640019 5536673 := bstep (se 2 (by rfl) ⟨2076252, by rfl⟩ : syracuseStep 5536673 = 4152505) B4152505
theorem B3693473 : Blo 1640019 3693473 := bstep (se 2 (by rfl) ⟨1385052, by rfl⟩ : syracuseStep 3693473 = 2770105) B2770105
theorem B85228469 : Blo 1640019 85228469 := bstep (se 5 (by rfl) ⟨3995084, by rfl⟩ : syracuseStep 85228469 = 7990169) B7990169
theorem B4267087 : Blo 1640019 4267087 := bstep (se 1 (by rfl) ⟨3200315, by rfl⟩ : syracuseStep 4267087 = 6400631) B6400631
theorem B8871065 : Blo 1640019 8871065 := bstep (se 2 (by rfl) ⟨3326649, by rfl⟩ : syracuseStep 8871065 = 6653299) B6653299
theorem B3693815 : Blo 1640019 3693815 := bstep (se 1 (by rfl) ⟨2770361, by rfl⟩ : syracuseStep 3693815 = 5540723) B5540723
theorem B8306063 : Blo 1640019 8306063 := bstep (se 1 (by rfl) ⟨6229547, by rfl⟩ : syracuseStep 8306063 = 12459095) B12459095
theorem B2768303 : Blo 1640019 2768303 := bstep (se 1 (by rfl) ⟨2076227, by rfl⟩ : syracuseStep 2768303 = 4152455) B4152455
theorem B5537267 : Blo 1640019 5537267 := bstep (se 1 (by rfl) ⟨4152950, by rfl⟩ : syracuseStep 5537267 = 8305901) B8305901
theorem B12459581 : Blo 1640019 12459581 := bstep (se 3 (by rfl) ⟨2336171, by rfl⟩ : syracuseStep 12459581 = 4672343) B4672343
theorem B22453847 : Blo 1640019 22453847 := bstep (se 1 (by rfl) ⟨16840385, by rfl⟩ : syracuseStep 22453847 = 33680771) B33680771
theorem B10518103 : Blo 1640019 10518103 := bstep (se 1 (by rfl) ⟨7888577, by rfl⟩ : syracuseStep 10518103 = 15777155) B15777155
theorem B4152971 : Blo 1640019 4152971 := bstep (se 1 (by rfl) ⟨3114728, by rfl⟩ : syracuseStep 4152971 = 6229457) B6229457
theorem B5259001 : Blo 1640019 5259001 := bstep (se 2 (by rfl) ⟨1972125, by rfl⟩ : syracuseStep 5259001 = 3944251) B3944251
theorem B3694409 : Blo 1640019 3694409 := bstep (se 2 (by rfl) ⟨1385403, by rfl⟩ : syracuseStep 3694409 = 2770807) B2770807
theorem B2768735 : Blo 1640019 2768735 := bstep (se 1 (by rfl) ⟨2076551, by rfl⟩ : syracuseStep 2768735 = 4153103) B4153103
theorem B2957231 : Blo 1640019 2957231 := bstep (se 1 (by rfl) ⟨2217923, by rfl⟩ : syracuseStep 2957231 = 4435847) B4435847
theorem B3506095 : Blo 1640019 3506095 := bstep (se 1 (by rfl) ⟨2629571, by rfl⟩ : syracuseStep 3506095 = 5259143) B5259143
theorem B6234043 : Blo 1640019 6234043 := bstep (se 1 (by rfl) ⟨4675532, by rfl⟩ : syracuseStep 6234043 = 9351065) B9351065
theorem B8307035 : Blo 1640019 8307035 := bstep (se 1 (by rfl) ⟨6230276, by rfl⟩ : syracuseStep 8307035 = 12460553) B12460553
theorem B22757797 : Blo 1640019 22757797 := bstep (se 4 (by rfl) ⟨2133543, by rfl⟩ : syracuseStep 22757797 = 4267087) B4267087
theorem B2769403 : Blo 1640019 2769403 := bstep (se 1 (by rfl) ⟨2077052, by rfl⟩ : syracuseStep 2769403 = 4154105) B4154105
theorem B4153963 : Blo 1640019 4153963 := bstep (se 1 (by rfl) ⟨3115472, by rfl⟩ : syracuseStep 4153963 = 6230945) B6230945
theorem B63103697 : Blo 1640019 63103697 := bstep (se 2 (by rfl) ⟨23663886, by rfl⟩ : syracuseStep 63103697 = 47327773) B47327773
theorem B4154267 : Blo 1640019 4154267 := bstep (se 1 (by rfl) ⟨3115700, by rfl⟩ : syracuseStep 4154267 = 6231401) B6231401
theorem B3941291 : Blo 1640019 3941291 := bstep (se 1 (by rfl) ⟨2955968, by rfl⟩ : syracuseStep 3941291 = 5911937) B5911937
theorem B2769835 : Blo 1640019 2769835 := bstep (se 1 (by rfl) ⟨2077376, by rfl⟩ : syracuseStep 2769835 = 4154753) B4154753
theorem B5538779 : Blo 1640019 5538779 := bstep (se 1 (by rfl) ⟨4154084, by rfl⟩ : syracuseStep 5538779 = 8308169) B8308169
theorem B5260385 : Blo 1640019 5260385 := bstep (se 2 (by rfl) ⟨1972644, by rfl⟩ : syracuseStep 5260385 = 3945289) B3945289
theorem B5538941 : Blo 1640019 5538941 := bstep (se 3 (by rfl) ⟨1038551, by rfl⟩ : syracuseStep 5538941 = 2077103) B2077103
theorem B2770139 : Blo 1640019 2770139 := bstep (se 1 (by rfl) ⟨2077604, by rfl⟩ : syracuseStep 2770139 = 4155209) B4155209
theorem B5539049 : Blo 1640019 5539049 := bstep (se 2 (by rfl) ⟨2077143, by rfl⟩ : syracuseStep 5539049 = 4154287) B4154287
theorem B4154611 : Blo 1640019 4154611 := bstep (se 1 (by rfl) ⟨3115958, by rfl⟩ : syracuseStep 4154611 = 6231917) B6231917
theorem B6227239 : Blo 1640019 6227239 := bstep (se 1 (by rfl) ⟨4670429, by rfl⟩ : syracuseStep 6227239 = 9340859) B9340859
theorem B8308007 : Blo 1640019 8308007 := bstep (se 1 (by rfl) ⟨6231005, by rfl⟩ : syracuseStep 8308007 = 12462011) B12462011
theorem B5539211 : Blo 1640019 5539211 := bstep (se 1 (by rfl) ⟨4154408, by rfl⟩ : syracuseStep 5539211 = 8308817) B8308817
theorem B7005629 : Blo 1640019 7005629 := bstep (se 3 (by rfl) ⟨1313555, by rfl⟩ : syracuseStep 7005629 = 2627111) B2627111
theorem B4670909 : Blo 1640019 4670909 := bstep (se 3 (by rfl) ⟨875795, by rfl⟩ : syracuseStep 4670909 = 1751591) B1751591
theorem B2770375 : Blo 1640019 2770375 := bstep (se 1 (by rfl) ⟨2077781, by rfl⟩ : syracuseStep 2770375 = 4155563) B4155563
theorem B6227513 : Blo 1640019 6227513 := bstep (se 2 (by rfl) ⟨2335317, by rfl⟩ : syracuseStep 6227513 = 4670635) B4670635
theorem B11232857 : Blo 1640019 11232857 := bstep (se 2 (by rfl) ⟨4212321, by rfl⟩ : syracuseStep 11232857 = 8424643) B8424643
theorem B7882427 : Blo 1640019 7882427 := bstep (se 1 (by rfl) ⟨5911820, by rfl⟩ : syracuseStep 7882427 = 11823641) B11823641
theorem B3114683 : Blo 1640019 3114683 := bstep (se 1 (by rfl) ⟨2336012, by rfl⟩ : syracuseStep 3114683 = 4672025) B4672025
theorem B1640159 : Blo 1640019 1640159 := bstep (se 1 (by rfl) ⟨1230119, by rfl⟩ : syracuseStep 1640159 = 2460239) B2460239
theorem B1640239 : Blo 1640019 1640239 := bstep (se 1 (by rfl) ⟨1230179, by rfl⟩ : syracuseStep 1640239 = 2460359) B2460359
theorem B15992723 : Blo 1640019 15992723 := bstep (se 1 (by rfl) ⟨11994542, by rfl⟩ : syracuseStep 15992723 = 23989085) B23989085
theorem B1640347 : Blo 1640019 1640347 := bstep (se 1 (by rfl) ⟨1230260, by rfl⟩ : syracuseStep 1640347 = 2460521) B2460521
theorem B1640399 : Blo 1640019 1640399 := bstep (se 1 (by rfl) ⟨1230299, by rfl⟩ : syracuseStep 1640399 = 2460599) B2460599
theorem B2770895 : Blo 1640019 2770895 := bstep (se 1 (by rfl) ⟨2078171, by rfl⟩ : syracuseStep 2770895 = 4156343) B4156343
theorem B1640423 : Blo 1640019 1640423 := bstep (se 1 (by rfl) ⟨1230317, by rfl⟩ : syracuseStep 1640423 = 2460635) B2460635
theorem B4155401 : Blo 1640019 4155401 := bstep (se 2 (by rfl) ⟨1558275, by rfl⟩ : syracuseStep 4155401 = 3116551) B3116551
theorem B1845535 : Blo 1640019 1845535 := bstep (se 1 (by rfl) ⟨1384151, by rfl⟩ : syracuseStep 1845535 = 2768303) B2768303
theorem B1640735 : Blo 1640019 1640735 := bstep (se 1 (by rfl) ⟨1230551, by rfl⟩ : syracuseStep 1640735 = 2461103) B2461103
theorem B202172705 : Blo 1640019 202172705 := bstep (se 2 (by rfl) ⟨75814764, by rfl⟩ : syracuseStep 202172705 = 151629529) B151629529
theorem B1640795 : Blo 1640019 1640795 := bstep (se 1 (by rfl) ⟨1230596, by rfl⟩ : syracuseStep 1640795 = 2461193) B2461193
theorem B1640815 : Blo 1640019 1640815 := bstep (se 1 (by rfl) ⟨1230611, by rfl⟩ : syracuseStep 1640815 = 2461223) B2461223
theorem B14969231 : Blo 1640019 14969231 := bstep (se 1 (by rfl) ⟨11226923, by rfl⟩ : syracuseStep 14969231 = 22453847) B22453847
theorem B2460071 : Blo 1640019 2460071 := bstep (se 1 (by rfl) ⟨1845053, by rfl⟩ : syracuseStep 2460071 = 3690107) B3690107
theorem B4671911 : Blo 1640019 4671911 := bstep (se 1 (by rfl) ⟨3503933, by rfl⟩ : syracuseStep 4671911 = 7007867) B7007867
theorem B1640871 : Blo 1640019 1640871 := bstep (se 1 (by rfl) ⟨1230653, by rfl⟩ : syracuseStep 1640871 = 2461307) B2461307
theorem B6654419 : Blo 1640019 6654419 := bstep (se 1 (by rfl) ⟨4990814, by rfl⟩ : syracuseStep 6654419 = 9981629) B9981629
theorem B2460155 : Blo 1640019 2460155 := bstep (se 1 (by rfl) ⟨1845116, by rfl⟩ : syracuseStep 2460155 = 3690233) B3690233
theorem B1640955 : Blo 1640019 1640955 := bstep (se 1 (by rfl) ⟨1230716, by rfl⟩ : syracuseStep 1640955 = 2461433) B2461433
theorem B1845823 : Blo 1640019 1845823 := bstep (se 1 (by rfl) ⟨1384367, by rfl⟩ : syracuseStep 1845823 = 2768735) B2768735
theorem B1641023 : Blo 1640019 1641023 := bstep (se 1 (by rfl) ⟨1230767, by rfl⟩ : syracuseStep 1641023 = 2461535) B2461535
theorem B1641031 : Blo 1640019 1641031 := bstep (se 1 (by rfl) ⟨1230773, by rfl⟩ : syracuseStep 1641031 = 2461547) B2461547
theorem B2460281 : Blo 1640019 2460281 := bstep (se 2 (by rfl) ⟨922605, by rfl⟩ : syracuseStep 2460281 = 1845211) B1845211
theorem B2460335 : Blo 1640019 2460335 := bstep (se 1 (by rfl) ⟨1845251, by rfl⟩ : syracuseStep 2460335 = 3690503) B3690503
theorem B2460383 : Blo 1640019 2460383 := bstep (se 1 (by rfl) ⟨1845287, by rfl⟩ : syracuseStep 2460383 = 3690575) B3690575
theorem B1641183 : Blo 1640019 1641183 := bstep (se 1 (by rfl) ⟨1230887, by rfl⟩ : syracuseStep 1641183 = 2461775) B2461775
theorem B31542007 : Blo 1640019 31542007 := bstep (se 1 (by rfl) ⟨23656505, by rfl⟩ : syracuseStep 31542007 = 47313011) B47313011
theorem B7883543 : Blo 1640019 7883543 := bstep (se 1 (by rfl) ⟨5912657, by rfl⟩ : syracuseStep 7883543 = 11825315) B11825315
theorem B1641263 : Blo 1640019 1641263 := bstep (se 1 (by rfl) ⟨1230947, by rfl⟩ : syracuseStep 1641263 = 2461895) B2461895
theorem B8424317 : Blo 1640019 8424317 := bstep (se 3 (by rfl) ⟨1579559, by rfl⟩ : syracuseStep 8424317 = 3159119) B3159119
theorem B12462983 : Blo 1640019 12462983 := bstep (se 1 (by rfl) ⟨9347237, by rfl⟩ : syracuseStep 12462983 = 18694475) B18694475
theorem B1641371 : Blo 1640019 1641371 := bstep (se 1 (by rfl) ⟨1231028, by rfl⟩ : syracuseStep 1641371 = 2462057) B2462057
theorem B1641423 : Blo 1640019 1641423 := bstep (se 1 (by rfl) ⟨1231067, by rfl⟩ : syracuseStep 1641423 = 2462135) B2462135
theorem B2460647 : Blo 1640019 2460647 := bstep (se 1 (by rfl) ⟨1845485, by rfl⟩ : syracuseStep 2460647 = 3690971) B3690971
theorem B1641447 : Blo 1640019 1641447 := bstep (se 1 (by rfl) ⟨1231085, by rfl⟩ : syracuseStep 1641447 = 2462171) B2462171
theorem B16846001 : Blo 1640019 16846001 := bstep (se 2 (by rfl) ⟨6317250, by rfl⟩ : syracuseStep 16846001 = 12634501) B12634501
theorem B21040307 : Blo 1640019 21040307 := bstep (se 1 (by rfl) ⟨15780230, by rfl⟩ : syracuseStep 21040307 = 31560461) B31560461
theorem B2460905 : Blo 1640019 2460905 := bstep (se 2 (by rfl) ⟨922839, by rfl⟩ : syracuseStep 2460905 = 1845679) B1845679
theorem B2460959 : Blo 1640019 2460959 := bstep (se 1 (by rfl) ⟨1845719, by rfl⟩ : syracuseStep 2460959 = 3691439) B3691439
theorem B4672799 : Blo 1640019 4672799 := bstep (se 1 (by rfl) ⟨3504599, by rfl⟩ : syracuseStep 4672799 = 7009199) B7009199
theorem B1641759 : Blo 1640019 1641759 := bstep (se 1 (by rfl) ⟨1231319, by rfl⟩ : syracuseStep 1641759 = 2462639) B2462639
theorem B8875325 : Blo 1640019 8875325 := bstep (se 3 (by rfl) ⟨1664123, by rfl⟩ : syracuseStep 8875325 = 3328247) B3328247
theorem B7990595 : Blo 1640019 7990595 := bstep (se 1 (by rfl) ⟨5992946, by rfl⟩ : syracuseStep 7990595 = 11985893) B11985893
theorem B1641819 : Blo 1640019 1641819 := bstep (se 1 (by rfl) ⟨1231364, by rfl⟩ : syracuseStep 1641819 = 2462729) B2462729
theorem B8310113 : Blo 1640019 8310113 := bstep (se 2 (by rfl) ⟨3116292, by rfl⟩ : syracuseStep 8310113 = 6232585) B6232585
theorem B1641839 : Blo 1640019 1641839 := bstep (se 1 (by rfl) ⟨1231379, by rfl⟩ : syracuseStep 1641839 = 2462759) B2462759
theorem B1846651 : Blo 1640019 1846651 := bstep (se 1 (by rfl) ⟨1384988, by rfl⟩ : syracuseStep 1846651 = 2769977) B2769977
theorem B4435337 : Blo 1640019 4435337 := bstep (se 2 (by rfl) ⟨1663251, by rfl⟩ : syracuseStep 4435337 = 3326503) B3326503
theorem B1641895 : Blo 1640019 1641895 := bstep (se 1 (by rfl) ⟨1231421, by rfl⟩ : syracuseStep 1641895 = 2462843) B2462843
theorem B2461127 : Blo 1640019 2461127 := bstep (se 1 (by rfl) ⟨1845845, by rfl⟩ : syracuseStep 2461127 = 3691691) B3691691
theorem B23662043 : Blo 1640019 23662043 := bstep (se 1 (by rfl) ⟨17746532, by rfl⟩ : syracuseStep 23662043 = 35493065) B35493065
theorem B1641979 : Blo 1640019 1641979 := bstep (se 1 (by rfl) ⟨1231484, by rfl⟩ : syracuseStep 1641979 = 2462969) B2462969
theorem B18681353 : Blo 1640019 18681353 := bstep (se 2 (by rfl) ⟨7005507, by rfl⟩ : syracuseStep 18681353 = 14011015) B14011015
theorem B3116627 : Blo 1640019 3116627 := bstep (se 1 (by rfl) ⟨2337470, by rfl⟩ : syracuseStep 3116627 = 4674941) B4674941
theorem B21032621 : Blo 1640019 21032621 := bstep (se 3 (by rfl) ⟨3943616, by rfl⟩ : syracuseStep 21032621 = 7887233) B7887233
theorem B2461481 : Blo 1640019 2461481 := bstep (se 2 (by rfl) ⟨923055, by rfl⟩ : syracuseStep 2461481 = 1846111) B1846111
theorem B3690287 : Blo 1640019 3690287 := bstep (se 1 (by rfl) ⟨2767715, by rfl⟩ : syracuseStep 3690287 = 5535431) B5535431
theorem B2461487 : Blo 1640019 2461487 := bstep (se 1 (by rfl) ⟨1846115, by rfl⟩ : syracuseStep 2461487 = 3692231) B3692231
theorem B3116855 : Blo 1640019 3116855 := bstep (se 1 (by rfl) ⟨2337641, by rfl⟩ : syracuseStep 3116855 = 4675283) B4675283
theorem B1847119 : Blo 1640019 1847119 := bstep (se 1 (by rfl) ⟨1385339, by rfl⟩ : syracuseStep 1847119 = 2770679) B2770679
theorem B2494415 : Blo 1640019 2494415 := bstep (se 1 (by rfl) ⟨1870811, by rfl⟩ : syracuseStep 2494415 = 3741623) B3741623
theorem B10113083 : Blo 1640019 10113083 := bstep (se 1 (by rfl) ⟨7584812, by rfl⟩ : syracuseStep 10113083 = 15169625) B15169625
theorem B2461961 : Blo 1640019 2461961 := bstep (se 2 (by rfl) ⟨923235, by rfl⟩ : syracuseStep 2461961 = 1846471) B1846471
theorem B3944713 : Blo 1640019 3944713 := bstep (se 2 (by rfl) ⟨1479267, by rfl⟩ : syracuseStep 3944713 = 2958535) B2958535
theorem B3690863 : Blo 1640019 3690863 := bstep (se 1 (by rfl) ⟨2768147, by rfl⟩ : syracuseStep 3690863 = 5536295) B5536295
theorem B2462063 : Blo 1640019 2462063 := bstep (se 1 (by rfl) ⟨1846547, by rfl⟩ : syracuseStep 2462063 = 3693095) B3693095
theorem B37884293 : Blo 1640019 37884293 := bstep (se 4 (by rfl) ⟨3551652, by rfl⟩ : syracuseStep 37884293 = 7103305) B7103305
theorem B2806183 : Blo 1640019 2806183 := bstep (se 1 (by rfl) ⟨2104637, by rfl⟩ : syracuseStep 2806183 = 4209275) B4209275
theorem B3690935 : Blo 1640019 3690935 := bstep (se 1 (by rfl) ⟨2768201, by rfl⟩ : syracuseStep 3690935 = 5536403) B5536403
theorem B10515005 : Blo 1640019 10515005 := bstep (se 3 (by rfl) ⟨1971563, by rfl⟩ : syracuseStep 10515005 = 3943127) B3943127
theorem B3691079 : Blo 1640019 3691079 := bstep (se 1 (by rfl) ⟨2768309, by rfl⟩ : syracuseStep 3691079 = 5536619) B5536619
theorem B2077255 : Blo 1640019 2077255 := bstep (se 1 (by rfl) ⟨1557941, by rfl⟩ : syracuseStep 2077255 = 3115883) B3115883
theorem B2462279 : Blo 1640019 2462279 := bstep (se 1 (by rfl) ⟨1846709, by rfl⟩ : syracuseStep 2462279 = 3693419) B3693419
theorem B8876641 : Blo 1640019 8876641 := bstep (se 2 (by rfl) ⟨3328740, by rfl⟩ : syracuseStep 8876641 = 6657481) B6657481
theorem B3691115 : Blo 1640019 3691115 := bstep (se 1 (by rfl) ⟨2768336, by rfl⟩ : syracuseStep 3691115 = 5536673) B5536673
theorem B2462315 : Blo 1640019 2462315 := bstep (se 1 (by rfl) ⟨1846736, by rfl⟩ : syracuseStep 2462315 = 3693473) B3693473
theorem B10253135 : Blo 1640019 10253135 := bstep (se 1 (by rfl) ⟨7689851, by rfl⟩ : syracuseStep 10253135 = 15379703) B15379703
theorem B2462543 : Blo 1640019 2462543 := bstep (se 1 (by rfl) ⟨1846907, by rfl⟩ : syracuseStep 2462543 = 3693815) B3693815
theorem B3691511 : Blo 1640019 3691511 := bstep (se 1 (by rfl) ⟨2768633, by rfl⟩ : syracuseStep 3691511 = 5537267) B5537267
theorem B2462939 : Blo 1640019 2462939 := bstep (se 1 (by rfl) ⟨1847204, by rfl⟩ : syracuseStep 2462939 = 3694409) B3694409
theorem B4674793 : Blo 1640019 4674793 := bstep (se 2 (by rfl) ⟨1753047, by rfl⟩ : syracuseStep 4674793 = 3506095) B3506095
theorem B8312057 : Blo 1640019 8312057 := bstep (se 2 (by rfl) ⟨3117021, by rfl⟩ : syracuseStep 8312057 = 6234043) B6234043
theorem B1971487 : Blo 1640019 1971487 := bstep (se 1 (by rfl) ⟨1478615, by rfl⟩ : syracuseStep 1971487 = 2957231) B2957231
theorem B3691871 : Blo 1640019 3691871 := bstep (se 1 (by rfl) ⟨2768903, by rfl⟩ : syracuseStep 3691871 = 5537807) B5537807
theorem B2078075 : Blo 1640019 2078075 := bstep (se 1 (by rfl) ⟨1558556, by rfl⟩ : syracuseStep 2078075 = 3117113) B3117113
theorem B119707085 : Blo 1640019 119707085 := bstep (se 3 (by rfl) ⟨22445078, by rfl⟩ : syracuseStep 119707085 = 44890157) B44890157
theorem B31954439 : Blo 1640019 31954439 := bstep (se 1 (by rfl) ⟨23965829, by rfl⟩ : syracuseStep 31954439 = 47931659) B47931659
theorem B7886425 : Blo 1640019 7886425 := bstep (se 2 (by rfl) ⟨2957409, by rfl⟩ : syracuseStep 7886425 = 5914819) B5914819
theorem B3503711 : Blo 1640019 3503711 := bstep (se 1 (by rfl) ⟨2627783, by rfl⟩ : syracuseStep 3503711 = 5255567) B5255567
theorem B4675259 : Blo 1640019 4675259 := bstep (se 1 (by rfl) ⟨3506444, by rfl⟩ : syracuseStep 4675259 = 7012889) B7012889
theorem B3692267 : Blo 1640019 3692267 := bstep (se 1 (by rfl) ⟨2769200, by rfl⟩ : syracuseStep 3692267 = 5538401) B5538401
theorem B5535593 : Blo 1640019 5535593 := bstep (se 2 (by rfl) ⟨2075847, by rfl⟩ : syracuseStep 5535593 = 4151695) B4151695
theorem B3692393 : Blo 1640019 3692393 := bstep (se 2 (by rfl) ⟨1384647, by rfl⟩ : syracuseStep 3692393 = 2769295) B2769295
theorem B1800091 : Blo 1640019 1800091 := bstep (se 1 (by rfl) ⟨1350068, by rfl⟩ : syracuseStep 1800091 = 2700137) B2700137
theorem B17733563 : Blo 1640019 17733563 := bstep (se 1 (by rfl) ⟨13300172, by rfl⟩ : syracuseStep 17733563 = 26600345) B26600345
theorem B4151321 : Blo 1640019 4151321 := bstep (se 2 (by rfl) ⟨1556745, by rfl⟩ : syracuseStep 4151321 = 3113491) B3113491
theorem B5536025 : Blo 1640019 5536025 := bstep (se 2 (by rfl) ⟨2076009, by rfl⟩ : syracuseStep 5536025 = 4152019) B4152019
theorem B4438363 : Blo 1640019 4438363 := bstep (se 1 (by rfl) ⟨3328772, by rfl⟩ : syracuseStep 4438363 = 6657545) B6657545
theorem B6650279 : Blo 1640019 6650279 := bstep (se 1 (by rfl) ⟨4987709, by rfl⟩ : syracuseStep 6650279 = 9975419) B9975419
theorem B6232571 : Blo 1640019 6232571 := bstep (se 1 (by rfl) ⟨4674428, by rfl⟩ : syracuseStep 6232571 = 9348857) B9348857
theorem B2955847 : Blo 1640019 2955847 := bstep (se 1 (by rfl) ⟨2216885, by rfl⟩ : syracuseStep 2955847 = 4433771) B4433771
theorem B3693239 : Blo 1640019 3693239 := bstep (se 1 (by rfl) ⟨2769929, by rfl⟩ : syracuseStep 3693239 = 5539859) B5539859
theorem B21019499 : Blo 1640019 21019499 := bstep (se 1 (by rfl) ⟨15764624, by rfl⟩ : syracuseStep 21019499 = 31529249) B31529249
theorem B75799439 : Blo 1640019 75799439 := bstep (se 1 (by rfl) ⟨56849579, by rfl⟩ : syracuseStep 75799439 = 113699159) B113699159
theorem B3693455 : Blo 1640019 3693455 := bstep (se 1 (by rfl) ⟨2770091, by rfl⟩ : syracuseStep 3693455 = 5540183) B5540183
theorem B7887887 : Blo 1640019 7887887 := bstep (se 1 (by rfl) ⟨5915915, by rfl⟩ : syracuseStep 7887887 = 11831831) B11831831
theorem B3505351 : Blo 1640019 3505351 := bstep (se 1 (by rfl) ⟨2629013, by rfl⟩ : syracuseStep 3505351 = 5258027) B5258027
theorem B1752283 : Blo 1640019 1752283 := bstep (se 1 (by rfl) ⟨1314212, by rfl⟩ : syracuseStep 1752283 = 2628425) B2628425
theorem B6233375 : Blo 1640019 6233375 := bstep (se 1 (by rfl) ⟨4675031, by rfl⟩ : syracuseStep 6233375 = 9350063) B9350063
theorem B56818979 : Blo 1640019 56818979 := bstep (se 1 (by rfl) ⟨42614234, by rfl⟩ : syracuseStep 56818979 = 85228469) B85228469
theorem B5914043 : Blo 1640019 5914043 := bstep (se 1 (by rfl) ⟨4435532, by rfl⟩ : syracuseStep 5914043 = 8871065) B8871065
theorem B6233543 : Blo 1640019 6233543 := bstep (se 1 (by rfl) ⟨4675157, by rfl⟩ : syracuseStep 6233543 = 9350315) B9350315
theorem B14024137 : Blo 1640019 14024137 := bstep (se 2 (by rfl) ⟨5259051, by rfl⟩ : syracuseStep 14024137 = 10518103) B10518103
theorem B2768377 : Blo 1640019 2768377 := bstep (se 2 (by rfl) ⟨1038141, by rfl⟩ : syracuseStep 2768377 = 2076283) B2076283
theorem B5537375 : Blo 1640019 5537375 := bstep (se 1 (by rfl) ⟨4153031, by rfl⟩ : syracuseStep 5537375 = 8306063) B8306063
theorem B3694175 : Blo 1640019 3694175 := bstep (se 1 (by rfl) ⟨2770631, by rfl⟩ : syracuseStep 3694175 = 5541263) B5541263
theorem B7012001 : Blo 1640019 7012001 := bstep (se 2 (by rfl) ⟨2629500, by rfl⟩ : syracuseStep 7012001 = 5259001) B5259001
theorem B8306387 : Blo 1640019 8306387 := bstep (se 1 (by rfl) ⟨6229790, by rfl⟩ : syracuseStep 8306387 = 12459581) B12459581
theorem B2957035 : Blo 1640019 2957035 := bstep (se 1 (by rfl) ⟨2217776, by rfl⟩ : syracuseStep 2957035 = 4435553) B4435553
theorem B17751811 : Blo 1640019 17751811 := bstep (se 1 (by rfl) ⟨13313858, by rfl⟩ : syracuseStep 17751811 = 26627717) B26627717
theorem B2768647 : Blo 1640019 2768647 := bstep (se 1 (by rfl) ⟨2076485, by rfl⟩ : syracuseStep 2768647 = 4152971) B4152971
theorem B2768681 : Blo 1640019 2768681 := bstep (se 2 (by rfl) ⟨1038255, by rfl⟩ : syracuseStep 2768681 = 2076511) B2076511
theorem B3694391 : Blo 1640019 3694391 := bstep (se 1 (by rfl) ⟨2770793, by rfl⟩ : syracuseStep 3694391 = 5541587) B5541587
theorem B4153295 : Blo 1640019 4153295 := bstep (se 1 (by rfl) ⟨3114971, by rfl⟩ : syracuseStep 4153295 = 6229943) B6229943
theorem B6742055 : Blo 1640019 6742055 := bstep (se 1 (by rfl) ⟨5056541, by rfl⟩ : syracuseStep 6742055 = 10113083) B10113083
theorem B5538023 : Blo 1640019 5538023 := bstep (se 1 (by rfl) ⟨4153517, by rfl⟩ : syracuseStep 5538023 = 8307035) B8307035
theorem B25256195 : Blo 1640019 25256195 := bstep (se 1 (by rfl) ⟨18942146, by rfl⟩ : syracuseStep 25256195 = 37884293) B37884293
theorem B5259617 : Blo 1640019 5259617 := bstep (se 2 (by rfl) ⟨1972356, by rfl⟩ : syracuseStep 5259617 = 3944713) B3944713
theorem B30343729 : Blo 1640019 30343729 := bstep (se 2 (by rfl) ⟨11378898, by rfl⟩ : syracuseStep 30343729 = 22757797) B22757797
theorem B2769511 : Blo 1640019 2769511 := bstep (se 1 (by rfl) ⟨2077133, by rfl⟩ : syracuseStep 2769511 = 4154267) B4154267
theorem B3506923 : Blo 1640019 3506923 := bstep (se 1 (by rfl) ⟨2630192, by rfl⟩ : syracuseStep 3506923 = 5260385) B5260385
theorem B3941129 : Blo 1640019 3941129 := bstep (se 2 (by rfl) ⟨1477923, by rfl⟩ : syracuseStep 3941129 = 2955847) B2955847
theorem B2769673 : Blo 1640019 2769673 := bstep (se 2 (by rfl) ⟨1038627, by rfl⟩ : syracuseStep 2769673 = 2077255) B2077255
theorem B5538617 : Blo 1640019 5538617 := bstep (se 2 (by rfl) ⟨2076981, by rfl⟩ : syracuseStep 5538617 = 4153963) B4153963
theorem B5538671 : Blo 1640019 5538671 := bstep (se 1 (by rfl) ⟨4154003, by rfl⟩ : syracuseStep 5538671 = 8308007) B8308007
theorem B4670419 : Blo 1640019 4670419 := bstep (se 1 (by rfl) ⟨3502814, by rfl⟩ : syracuseStep 4670419 = 7005629) B7005629
theorem B3113939 : Blo 1640019 3113939 := bstep (se 1 (by rfl) ⟨2335454, by rfl⟩ : syracuseStep 3113939 = 4670909) B4670909
theorem B7488571 : Blo 1640019 7488571 := bstep (se 1 (by rfl) ⟨5616428, by rfl⟩ : syracuseStep 7488571 = 11232857) B11232857
theorem B2335807 : Blo 1640019 2335807 := bstep (se 1 (by rfl) ⟨1751855, by rfl⟩ : syracuseStep 2335807 = 3503711) B3503711
theorem B11822375 : Blo 1640019 11822375 := bstep (se 1 (by rfl) ⟨8866781, by rfl⟩ : syracuseStep 11822375 = 17733563) B17733563
theorem B2770267 : Blo 1640019 2770267 := bstep (se 1 (by rfl) ⟨2077700, by rfl⟩ : syracuseStep 2770267 = 4155401) B4155401
theorem B9979487 : Blo 1640019 9979487 := bstep (se 1 (by rfl) ⟨7484615, by rfl⟩ : syracuseStep 9979487 = 14969231) B14969231
theorem B1640047 : Blo 1640019 1640047 := bstep (se 1 (by rfl) ⟨1230035, by rfl⟩ : syracuseStep 1640047 = 2460071) B2460071
theorem B4433519 : Blo 1640019 4433519 := bstep (se 1 (by rfl) ⟨3325139, by rfl⟩ : syracuseStep 4433519 = 6650279) B6650279
theorem B3114607 : Blo 1640019 3114607 := bstep (se 1 (by rfl) ⟨2335955, by rfl⟩ : syracuseStep 3114607 = 4671911) B4671911
theorem B2336377 : Blo 1640019 2336377 := bstep (se 2 (by rfl) ⟨876141, by rfl⟩ : syracuseStep 2336377 = 1752283) B1752283
theorem B5539481 : Blo 1640019 5539481 := bstep (se 2 (by rfl) ⟨2077305, by rfl⟩ : syracuseStep 5539481 = 4154611) B4154611
theorem B1640103 : Blo 1640019 1640103 := bstep (se 1 (by rfl) ⟨1230077, by rfl⟩ : syracuseStep 1640103 = 2460155) B2460155
theorem B4155047 : Blo 1640019 4155047 := bstep (se 1 (by rfl) ⟨3116285, by rfl⟩ : syracuseStep 4155047 = 6232571) B6232571
theorem B1640187 : Blo 1640019 1640187 := bstep (se 1 (by rfl) ⟨1230140, by rfl⟩ : syracuseStep 1640187 = 2460281) B2460281
theorem B1640223 : Blo 1640019 1640223 := bstep (se 1 (by rfl) ⟨1230167, by rfl⟩ : syracuseStep 1640223 = 2460335) B2460335
theorem B1640255 : Blo 1640019 1640255 := bstep (se 1 (by rfl) ⟨1230191, by rfl⟩ : syracuseStep 1640255 = 2460383) B2460383
theorem B8308655 : Blo 1640019 8308655 := bstep (se 1 (by rfl) ⟨6231491, by rfl⟩ : syracuseStep 8308655 = 12462983) B12462983
theorem B1640431 : Blo 1640019 1640431 := bstep (se 1 (by rfl) ⟨1230323, by rfl⟩ : syracuseStep 1640431 = 2460647) B2460647
theorem B14026871 : Blo 1640019 14026871 := bstep (se 1 (by rfl) ⟨10520153, by rfl⟩ : syracuseStep 14026871 = 21040307) B21040307
theorem B1640603 : Blo 1640019 1640603 := bstep (se 1 (by rfl) ⟨1230452, by rfl⟩ : syracuseStep 1640603 = 2460905) B2460905
theorem B1640639 : Blo 1640019 1640639 := bstep (se 1 (by rfl) ⟨1230479, by rfl⟩ : syracuseStep 1640639 = 2460959) B2460959
theorem B3115199 : Blo 1640019 3115199 := bstep (se 1 (by rfl) ⟨2336399, by rfl⟩ : syracuseStep 3115199 = 4672799) B4672799
theorem B4155583 : Blo 1640019 4155583 := bstep (se 1 (by rfl) ⟨3116687, by rfl⟩ : syracuseStep 4155583 = 6233375) B6233375
theorem B5916883 : Blo 1640019 5916883 := bstep (se 1 (by rfl) ⟨4437662, by rfl⟩ : syracuseStep 5916883 = 8875325) B8875325
theorem B5327063 : Blo 1640019 5327063 := bstep (se 1 (by rfl) ⟨3995297, by rfl⟩ : syracuseStep 5327063 = 7990595) B7990595
theorem B5540075 : Blo 1640019 5540075 := bstep (se 1 (by rfl) ⟨4155056, by rfl⟩ : syracuseStep 5540075 = 8310113) B8310113
theorem B3942695 : Blo 1640019 3942695 := bstep (se 1 (by rfl) ⟨2957021, by rfl⟩ : syracuseStep 3942695 = 5914043) B5914043
theorem B1640751 : Blo 1640019 1640751 := bstep (se 1 (by rfl) ⟨1230563, by rfl⟩ : syracuseStep 1640751 = 2461127) B2461127
theorem B4155695 : Blo 1640019 4155695 := bstep (se 1 (by rfl) ⟨3116771, by rfl⟩ : syracuseStep 4155695 = 6233543) B6233543
theorem B3942713 : Blo 1640019 3942713 := bstep (se 2 (by rfl) ⟨1478517, by rfl⟩ : syracuseStep 3942713 = 2957035) B2957035
theorem B12454235 : Blo 1640019 12454235 := bstep (se 1 (by rfl) ⟨9340676, by rfl⟩ : syracuseStep 12454235 = 18681353) B18681353
theorem B23669081 : Blo 1640019 23669081 := bstep (se 2 (by rfl) ⟨8875905, by rfl⟩ : syracuseStep 23669081 = 17751811) B17751811
theorem B1845787 : Blo 1640019 1845787 := bstep (se 1 (by rfl) ⟨1384340, by rfl⟩ : syracuseStep 1845787 = 2768681) B2768681
theorem B1640987 : Blo 1640019 1640987 := bstep (se 1 (by rfl) ⟨1230740, by rfl⟩ : syracuseStep 1640987 = 2461481) B2461481
theorem B2460191 : Blo 1640019 2460191 := bstep (se 1 (by rfl) ⟨1845143, by rfl⟩ : syracuseStep 2460191 = 3690287) B3690287
theorem B1640991 : Blo 1640019 1640991 := bstep (se 1 (by rfl) ⟨1230743, by rfl⟩ : syracuseStep 1640991 = 2461487) B2461487
theorem B1641307 : Blo 1640019 1641307 := bstep (se 1 (by rfl) ⟨1230980, by rfl⟩ : syracuseStep 1641307 = 2461961) B2461961
theorem B2460575 : Blo 1640019 2460575 := bstep (se 1 (by rfl) ⟨1845431, by rfl⟩ : syracuseStep 2460575 = 3690863) B3690863
theorem B1641375 : Blo 1640019 1641375 := bstep (se 1 (by rfl) ⟨1231031, by rfl⟩ : syracuseStep 1641375 = 2462063) B2462063
theorem B2460623 : Blo 1640019 2460623 := bstep (se 1 (by rfl) ⟨1845467, by rfl⟩ : syracuseStep 2460623 = 3690935) B3690935
theorem B2460713 : Blo 1640019 2460713 := bstep (se 2 (by rfl) ⟨922767, by rfl⟩ : syracuseStep 2460713 = 1845535) B1845535
theorem B2460719 : Blo 1640019 2460719 := bstep (se 1 (by rfl) ⟨1845539, by rfl⟩ : syracuseStep 2460719 = 3691079) B3691079
theorem B1641519 : Blo 1640019 1641519 := bstep (se 1 (by rfl) ⟨1231139, by rfl⟩ : syracuseStep 1641519 = 2462279) B2462279
theorem B2460743 : Blo 1640019 2460743 := bstep (se 1 (by rfl) ⟨1845557, by rfl⟩ : syracuseStep 2460743 = 3691115) B3691115
theorem B1641543 : Blo 1640019 1641543 := bstep (se 1 (by rfl) ⟨1231157, by rfl⟩ : syracuseStep 1641543 = 2462315) B2462315
theorem B5917817 : Blo 1640019 5917817 := bstep (se 2 (by rfl) ⟨2219181, by rfl⟩ : syracuseStep 5917817 = 4438363) B4438363
theorem B42069131 : Blo 1640019 42069131 := bstep (se 1 (by rfl) ⟨31551848, by rfl⟩ : syracuseStep 42069131 = 63103697) B63103697
theorem B6835423 : Blo 1640019 6835423 := bstep (se 1 (by rfl) ⟨5126567, by rfl⟩ : syracuseStep 6835423 = 10253135) B10253135
theorem B1641695 : Blo 1640019 1641695 := bstep (se 1 (by rfl) ⟨1231271, by rfl⟩ : syracuseStep 1641695 = 2462543) B2462543
theorem B2461007 : Blo 1640019 2461007 := bstep (se 1 (by rfl) ⟨1845755, by rfl⟩ : syracuseStep 2461007 = 3691511) B3691511
theorem B2461097 : Blo 1640019 2461097 := bstep (se 2 (by rfl) ⟨922911, by rfl⟩ : syracuseStep 2461097 = 1845823) B1845823
theorem B1846759 : Blo 1640019 1846759 := bstep (se 1 (by rfl) ⟨1385069, by rfl⟩ : syracuseStep 1846759 = 2770139) B2770139
theorem B1641959 : Blo 1640019 1641959 := bstep (se 1 (by rfl) ⟨1231469, by rfl⟩ : syracuseStep 1641959 = 2462939) B2462939
theorem B5541371 : Blo 1640019 5541371 := bstep (se 1 (by rfl) ⟨4156028, by rfl⟩ : syracuseStep 5541371 = 8312057) B8312057
theorem B2461247 : Blo 1640019 2461247 := bstep (se 1 (by rfl) ⟨1845935, by rfl⟩ : syracuseStep 2461247 = 3691871) B3691871
theorem B5541533 : Blo 1640019 5541533 := bstep (se 3 (by rfl) ⟨1039037, by rfl⟩ : syracuseStep 5541533 = 2078075) B2078075
theorem B21302959 : Blo 1640019 21302959 := bstep (se 1 (by rfl) ⟨15977219, by rfl⟩ : syracuseStep 21302959 = 31954439) B31954439
theorem B5254951 : Blo 1640019 5254951 := bstep (se 1 (by rfl) ⟨3941213, by rfl⟩ : syracuseStep 5254951 = 7882427) B7882427
theorem B2076455 : Blo 1640019 2076455 := bstep (se 1 (by rfl) ⟨1557341, by rfl⟩ : syracuseStep 2076455 = 3114683) B3114683
theorem B2461511 : Blo 1640019 2461511 := bstep (se 1 (by rfl) ⟨1846133, by rfl⟩ : syracuseStep 2461511 = 3692267) B3692267
theorem B3690395 : Blo 1640019 3690395 := bstep (se 1 (by rfl) ⟨2767796, by rfl⟩ : syracuseStep 3690395 = 5535593) B5535593
theorem B2461595 : Blo 1640019 2461595 := bstep (se 1 (by rfl) ⟨1846196, by rfl⟩ : syracuseStep 2461595 = 3692393) B3692393
theorem B10661815 : Blo 1640019 10661815 := bstep (se 1 (by rfl) ⟨7996361, by rfl⟩ : syracuseStep 10661815 = 15992723) B15992723
theorem B1847263 : Blo 1640019 1847263 := bstep (se 1 (by rfl) ⟨1385447, by rfl⟩ : syracuseStep 1847263 = 2770895) B2770895
theorem B3690683 : Blo 1640019 3690683 := bstep (se 1 (by rfl) ⟨2768012, by rfl⟩ : syracuseStep 3690683 = 5536025) B5536025
theorem B4673801 : Blo 1640019 4673801 := bstep (se 2 (by rfl) ⟨1752675, by rfl⟩ : syracuseStep 4673801 = 3505351) B3505351
theorem B4436279 : Blo 1640019 4436279 := bstep (se 1 (by rfl) ⟨3327209, by rfl⟩ : syracuseStep 4436279 = 6654419) B6654419
theorem B8302985 : Blo 1640019 8302985 := bstep (se 2 (by rfl) ⟨3113619, by rfl⟩ : syracuseStep 8302985 = 6227239) B6227239
theorem B2462159 : Blo 1640019 2462159 := bstep (se 1 (by rfl) ⟨1846619, by rfl⟩ : syracuseStep 2462159 = 3693239) B3693239
theorem B2462201 : Blo 1640019 2462201 := bstep (se 2 (by rfl) ⟨923325, by rfl⟩ : syracuseStep 2462201 = 1846651) B1846651
theorem B5255695 : Blo 1640019 5255695 := bstep (se 1 (by rfl) ⟨3941771, by rfl⟩ : syracuseStep 5255695 = 7883543) B7883543
theorem B14012999 : Blo 1640019 14012999 := bstep (se 1 (by rfl) ⟨10509749, by rfl⟩ : syracuseStep 14012999 = 21019499) B21019499
theorem B5616211 : Blo 1640019 5616211 := bstep (se 1 (by rfl) ⟨4212158, by rfl⟩ : syracuseStep 5616211 = 8424317) B8424317
theorem B50532959 : Blo 1640019 50532959 := bstep (se 1 (by rfl) ⟨37899719, by rfl⟩ : syracuseStep 50532959 = 75799439) B75799439
theorem B2462303 : Blo 1640019 2462303 := bstep (se 1 (by rfl) ⟨1846727, by rfl⟩ : syracuseStep 2462303 = 3693455) B3693455
theorem B18698849 : Blo 1640019 18698849 := bstep (se 2 (by rfl) ⟨7012068, by rfl⟩ : syracuseStep 18698849 = 14024137) B14024137
theorem B3691169 : Blo 1640019 3691169 := bstep (se 2 (by rfl) ⟨1384188, by rfl⟩ : syracuseStep 3691169 = 2768377) B2768377
theorem B10515233 : Blo 1640019 10515233 := bstep (se 2 (by rfl) ⟨3943212, by rfl⟩ : syracuseStep 10515233 = 7886425) B7886425
theorem B15774695 : Blo 1640019 15774695 := bstep (se 1 (by rfl) ⟨11831021, by rfl⟩ : syracuseStep 15774695 = 23662043) B23662043
theorem B3691529 : Blo 1640019 3691529 := bstep (se 2 (by rfl) ⟨1384323, by rfl⟩ : syracuseStep 3691529 = 2768647) B2768647
theorem B2077751 : Blo 1640019 2077751 := bstep (se 1 (by rfl) ⟨1558313, by rfl⟩ : syracuseStep 2077751 = 3116627) B3116627
theorem B3691583 : Blo 1640019 3691583 := bstep (se 1 (by rfl) ⟨2768687, by rfl⟩ : syracuseStep 3691583 = 5537375) B5537375
theorem B2462783 : Blo 1640019 2462783 := bstep (se 1 (by rfl) ⟨1847087, by rfl⟩ : syracuseStep 2462783 = 3694175) B3694175
theorem B2462825 : Blo 1640019 2462825 := bstep (se 2 (by rfl) ⟨923559, by rfl⟩ : syracuseStep 2462825 = 1847119) B1847119
theorem B4674667 : Blo 1640019 4674667 := bstep (se 1 (by rfl) ⟨3506000, by rfl⟩ : syracuseStep 4674667 = 7012001) B7012001
theorem B14021747 : Blo 1640019 14021747 := bstep (se 1 (by rfl) ⟨10516310, by rfl⟩ : syracuseStep 14021747 = 21032621) B21032621
theorem B2077903 : Blo 1640019 2077903 := bstep (se 1 (by rfl) ⟨1558427, by rfl⟩ : syracuseStep 2077903 = 3116855) B3116855
theorem B2462927 : Blo 1640019 2462927 := bstep (se 1 (by rfl) ⟨1847195, by rfl⟩ : syracuseStep 2462927 = 3694391) B3694391
theorem B7010003 : Blo 1640019 7010003 := bstep (se 1 (by rfl) ⟨5257502, by rfl⟩ : syracuseStep 7010003 = 10515005) B10515005
theorem B2627527 : Blo 1640019 2627527 := bstep (se 1 (by rfl) ⟨1970645, by rfl⟩ : syracuseStep 2627527 = 3941291) B3941291
theorem B3692519 : Blo 1640019 3692519 := bstep (se 1 (by rfl) ⟨2769389, by rfl⟩ : syracuseStep 3692519 = 5538779) B5538779
theorem B3692537 : Blo 1640019 3692537 := bstep (se 2 (by rfl) ⟨1384701, by rfl⟩ : syracuseStep 3692537 = 2769403) B2769403
theorem B3692627 : Blo 1640019 3692627 := bstep (se 1 (by rfl) ⟨2769470, by rfl⟩ : syracuseStep 3692627 = 5538941) B5538941
theorem B11835521 : Blo 1640019 11835521 := bstep (se 2 (by rfl) ⟨4438320, by rfl⟩ : syracuseStep 11835521 = 8876641) B8876641
theorem B3692699 : Blo 1640019 3692699 := bstep (se 1 (by rfl) ⟨2769524, by rfl⟩ : syracuseStep 3692699 = 5539049) B5539049
theorem B3692807 : Blo 1640019 3692807 := bstep (se 1 (by rfl) ⟨2769605, by rfl⟩ : syracuseStep 3692807 = 5539211) B5539211
theorem B79804723 : Blo 1640019 79804723 := bstep (se 1 (by rfl) ⟨59853542, by rfl⟩ : syracuseStep 79804723 = 119707085) B119707085
theorem B42056009 : Blo 1640019 42056009 := bstep (se 2 (by rfl) ⟨15771003, by rfl⟩ : syracuseStep 42056009 = 31542007) B31542007
theorem B4151675 : Blo 1640019 4151675 := bstep (se 1 (by rfl) ⟨3113756, by rfl⟩ : syracuseStep 4151675 = 6227513) B6227513
theorem B3693113 : Blo 1640019 3693113 := bstep (se 2 (by rfl) ⟨1384917, by rfl⟩ : syracuseStep 3693113 = 2769835) B2769835
theorem B2767547 : Blo 1640019 2767547 := bstep (se 1 (by rfl) ⟨2075660, by rfl⟩ : syracuseStep 2767547 = 4151321) B4151321
theorem B134781803 : Blo 1640019 134781803 := bstep (se 1 (by rfl) ⟨101086352, by rfl⟩ : syracuseStep 134781803 = 202172705) B202172705
theorem B6233057 : Blo 1640019 6233057 := bstep (se 2 (by rfl) ⟨2337396, by rfl⟩ : syracuseStep 6233057 = 4674793) B4674793
theorem B2628649 : Blo 1640019 2628649 := bstep (se 2 (by rfl) ⟨985743, by rfl⟩ : syracuseStep 2628649 = 1971487) B1971487
theorem B12467357 : Blo 1640019 12467357 := bstep (se 3 (by rfl) ⟨2337629, by rfl⟩ : syracuseStep 12467357 = 4675259) B4675259
theorem B3693833 : Blo 1640019 3693833 := bstep (se 2 (by rfl) ⟨1385187, by rfl⟩ : syracuseStep 3693833 = 2770375) B2770375
theorem B5258591 : Blo 1640019 5258591 := bstep (se 1 (by rfl) ⟨3943943, by rfl⟩ : syracuseStep 5258591 = 7887887) B7887887
theorem B11230667 : Blo 1640019 11230667 := bstep (se 1 (by rfl) ⟨8423000, by rfl⟩ : syracuseStep 11230667 = 16846001) B16846001
theorem B37879319 : Blo 1640019 37879319 := bstep (se 1 (by rfl) ⟨28409489, by rfl⟩ : syracuseStep 37879319 = 56818979) B56818979
theorem B14966309 : Blo 1640019 14966309 := bstep (se 4 (by rfl) ⟨1403091, by rfl⟩ : syracuseStep 14966309 = 2806183) B2806183
theorem B2956891 : Blo 1640019 2956891 := bstep (se 1 (by rfl) ⟨2217668, by rfl⟩ : syracuseStep 2956891 = 4435337) B4435337
theorem B5537591 : Blo 1640019 5537591 := bstep (se 1 (by rfl) ⟨4153193, by rfl⟩ : syracuseStep 5537591 = 8306387) B8306387
theorem B2400121 : Blo 1640019 2400121 := bstep (se 2 (by rfl) ⟨900045, by rfl⟩ : syracuseStep 2400121 = 1800091) B1800091
theorem B6651773 : Blo 1640019 6651773 := bstep (se 3 (by rfl) ⟨1247207, by rfl⟩ : syracuseStep 6651773 = 2494415) B2494415
theorem B2768863 : Blo 1640019 2768863 := bstep (se 1 (by rfl) ⟨2076647, by rfl⟩ : syracuseStep 2768863 = 4153295) B4153295
theorem B2957519 : Blo 1640019 2957519 := bstep (se 1 (by rfl) ⟨2218139, by rfl⟩ : syracuseStep 2957519 = 4436279) B4436279
theorem B3506411 : Blo 1640019 3506411 := bstep (se 1 (by rfl) ⟨2629808, by rfl⟩ : syracuseStep 3506411 = 5259617) B5259617
theorem B7889177 : Blo 1640019 7889177 := bstep (se 2 (by rfl) ⟨2958441, by rfl⟩ : syracuseStep 7889177 = 5916883) B5916883
theorem B106406297 : Blo 1640019 106406297 := bstep (se 2 (by rfl) ⟨39902361, by rfl⟩ : syracuseStep 106406297 = 79804723) B79804723
theorem B8307197 : Blo 1640019 8307197 := bstep (se 3 (by rfl) ⟨1557599, by rfl⟩ : syracuseStep 8307197 = 3115199) B3115199
theorem B9347831 : Blo 1640019 9347831 := bstep (se 1 (by rfl) ⟨7010873, by rfl⟩ : syracuseStep 9347831 = 14021747) B14021747
theorem B7488281 : Blo 1640019 7488281 := bstep (se 2 (by rfl) ⟨2808105, by rfl⟩ : syracuseStep 7488281 = 5616211) B5616211
theorem B7881583 : Blo 1640019 7881583 := bstep (se 1 (by rfl) ⟨5911187, by rfl⟩ : syracuseStep 7881583 = 11822375) B11822375
theorem B6652991 : Blo 1640019 6652991 := bstep (se 1 (by rfl) ⟨4989743, by rfl⟩ : syracuseStep 6652991 = 9979487) B9979487
theorem B2770031 : Blo 1640019 2770031 := bstep (se 1 (by rfl) ⟨2077523, by rfl⟩ : syracuseStep 2770031 = 4155047) B4155047
theorem B6227225 : Blo 1640019 6227225 := bstep (se 2 (by rfl) ⟨2335209, by rfl⟩ : syracuseStep 6227225 = 4670419) B4670419
theorem B5539103 : Blo 1640019 5539103 := bstep (se 1 (by rfl) ⟨4154327, by rfl⟩ : syracuseStep 5539103 = 8308655) B8308655
theorem B7890347 : Blo 1640019 7890347 := bstep (se 1 (by rfl) ⟨5917760, by rfl⟩ : syracuseStep 7890347 = 11835521) B11835521
theorem B2770463 : Blo 1640019 2770463 := bstep (se 1 (by rfl) ⟨2077847, by rfl⟩ : syracuseStep 2770463 = 4155695) B4155695
theorem B15779387 : Blo 1640019 15779387 := bstep (se 1 (by rfl) ⟨11834540, by rfl⟩ : syracuseStep 15779387 = 23669081) B23669081
theorem B2770537 : Blo 1640019 2770537 := bstep (se 2 (by rfl) ⟨1038951, by rfl⟩ : syracuseStep 2770537 = 2077903) B2077903
theorem B11822717 : Blo 1640019 11822717 := bstep (se 3 (by rfl) ⟨2216759, by rfl⟩ : syracuseStep 11822717 = 4433519) B4433519
theorem B1640127 : Blo 1640019 1640127 := bstep (se 1 (by rfl) ⟨1230095, by rfl⟩ : syracuseStep 1640127 = 2460191) B2460191
theorem B1845031 : Blo 1640019 1845031 := bstep (se 1 (by rfl) ⟨1383773, by rfl⟩ : syracuseStep 1845031 = 2767547) B2767547
theorem B1640383 : Blo 1640019 1640383 := bstep (se 1 (by rfl) ⟨1230287, by rfl⟩ : syracuseStep 1640383 = 2460575) B2460575
theorem B1640415 : Blo 1640019 1640415 := bstep (se 1 (by rfl) ⟨1230311, by rfl⟩ : syracuseStep 1640415 = 2460623) B2460623
theorem B4155371 : Blo 1640019 4155371 := bstep (se 1 (by rfl) ⟨3116528, by rfl⟩ : syracuseStep 4155371 = 6233057) B6233057
theorem B1640475 : Blo 1640019 1640475 := bstep (se 1 (by rfl) ⟨1230356, by rfl⟩ : syracuseStep 1640475 = 2460713) B2460713
theorem B1640479 : Blo 1640019 1640479 := bstep (se 1 (by rfl) ⟨1230359, by rfl⟩ : syracuseStep 1640479 = 2460719) B2460719
theorem B1640495 : Blo 1640019 1640495 := bstep (se 1 (by rfl) ⟨1230371, by rfl⟩ : syracuseStep 1640495 = 2460743) B2460743
theorem B3942521 : Blo 1640019 3942521 := bstep (se 2 (by rfl) ⟨1478445, by rfl⟩ : syracuseStep 3942521 = 2956891) B2956891
theorem B3115169 : Blo 1640019 3115169 := bstep (se 2 (by rfl) ⟨1168188, by rfl⟩ : syracuseStep 3115169 = 2336377) B2336377
theorem B1640671 : Blo 1640019 1640671 := bstep (se 1 (by rfl) ⟨1230503, by rfl⟩ : syracuseStep 1640671 = 2461007) B2461007
theorem B28403945 : Blo 1640019 28403945 := bstep (se 2 (by rfl) ⟨10651479, by rfl⟩ : syracuseStep 28403945 = 21302959) B21302959
theorem B1640731 : Blo 1640019 1640731 := bstep (se 1 (by rfl) ⟨1230548, by rfl⟩ : syracuseStep 1640731 = 2461097) B2461097
theorem B1640831 : Blo 1640019 1640831 := bstep (se 1 (by rfl) ⟨1230623, by rfl⟩ : syracuseStep 1640831 = 2461247) B2461247
theorem B7006601 : Blo 1640019 7006601 := bstep (se 2 (by rfl) ⟨2627475, by rfl⟩ : syracuseStep 7006601 = 5254951) B5254951
theorem B1641007 : Blo 1640019 1641007 := bstep (se 1 (by rfl) ⟨1230755, by rfl⟩ : syracuseStep 1641007 = 2461511) B2461511
theorem B14215753 : Blo 1640019 14215753 := bstep (se 2 (by rfl) ⟨5330907, by rfl⟩ : syracuseStep 14215753 = 10661815) B10661815
theorem B4434515 : Blo 1640019 4434515 := bstep (se 1 (by rfl) ⟨3325886, by rfl⟩ : syracuseStep 4434515 = 6651773) B6651773
theorem B2460263 : Blo 1640019 2460263 := bstep (se 1 (by rfl) ⟨1845197, by rfl⟩ : syracuseStep 2460263 = 3690395) B3690395
theorem B1641063 : Blo 1640019 1641063 := bstep (se 1 (by rfl) ⟨1230797, by rfl⟩ : syracuseStep 1641063 = 2461595) B2461595
theorem B2460455 : Blo 1640019 2460455 := bstep (se 1 (by rfl) ⟨1845341, by rfl⟩ : syracuseStep 2460455 = 3690683) B3690683
theorem B5540669 : Blo 1640019 5540669 := bstep (se 3 (by rfl) ⟨1038875, by rfl⟩ : syracuseStep 5540669 = 2077751) B2077751
theorem B16837463 : Blo 1640019 16837463 := bstep (se 1 (by rfl) ⟨12628097, by rfl⟩ : syracuseStep 16837463 = 25256195) B25256195
theorem B5540777 : Blo 1640019 5540777 := bstep (se 2 (by rfl) ⟨2077791, by rfl⟩ : syracuseStep 5540777 = 4155583) B4155583
theorem B1641439 : Blo 1640019 1641439 := bstep (se 1 (by rfl) ⟨1231079, by rfl⟩ : syracuseStep 1641439 = 2462159) B2462159
theorem B15780845 : Blo 1640019 15780845 := bstep (se 3 (by rfl) ⟨2958908, by rfl⟩ : syracuseStep 15780845 = 5917817) B5917817
theorem B1641467 : Blo 1640019 1641467 := bstep (se 1 (by rfl) ⟨1231100, by rfl⟩ : syracuseStep 1641467 = 2462201) B2462201
theorem B9341999 : Blo 1640019 9341999 := bstep (se 1 (by rfl) ⟨7006499, by rfl⟩ : syracuseStep 9341999 = 14012999) B14012999
theorem B33688639 : Blo 1640019 33688639 := bstep (se 1 (by rfl) ⟨25266479, by rfl⟩ : syracuseStep 33688639 = 50532959) B50532959
theorem B1641535 : Blo 1640019 1641535 := bstep (se 1 (by rfl) ⟨1231151, by rfl⟩ : syracuseStep 1641535 = 2462303) B2462303
theorem B2460779 : Blo 1640019 2460779 := bstep (se 1 (by rfl) ⟨1845584, by rfl⟩ : syracuseStep 2460779 = 3691169) B3691169
theorem B2075959 : Blo 1640019 2075959 := bstep (se 1 (by rfl) ⟨1556969, by rfl⟩ : syracuseStep 2075959 = 3113939) B3113939
theorem B2461019 : Blo 1640019 2461019 := bstep (se 1 (by rfl) ⟨1845764, by rfl⟩ : syracuseStep 2461019 = 3691529) B3691529
theorem B7007593 : Blo 1640019 7007593 := bstep (se 2 (by rfl) ⟨2627847, by rfl⟩ : syracuseStep 7007593 = 5255695) B5255695
theorem B12463469 : Blo 1640019 12463469 := bstep (se 3 (by rfl) ⟨2336900, by rfl⟩ : syracuseStep 12463469 = 4673801) B4673801
theorem B2461049 : Blo 1640019 2461049 := bstep (se 2 (by rfl) ⟨922893, by rfl⟩ : syracuseStep 2461049 = 1845787) B1845787
theorem B2461055 : Blo 1640019 2461055 := bstep (se 1 (by rfl) ⟨1845791, by rfl⟩ : syracuseStep 2461055 = 3691583) B3691583
theorem B1641855 : Blo 1640019 1641855 := bstep (se 1 (by rfl) ⟨1231391, by rfl⟩ : syracuseStep 1641855 = 2462783) B2462783
theorem B1641883 : Blo 1640019 1641883 := bstep (se 1 (by rfl) ⟨1231412, by rfl⟩ : syracuseStep 1641883 = 2462825) B2462825
theorem B1641951 : Blo 1640019 1641951 := bstep (se 1 (by rfl) ⟨1231463, by rfl⟩ : syracuseStep 1641951 = 2462927) B2462927
theorem B10513901 : Blo 1640019 10513901 := bstep (se 3 (by rfl) ⟨1971356, by rfl⟩ : syracuseStep 10513901 = 3942713) B3942713
theorem B4673335 : Blo 1640019 4673335 := bstep (se 1 (by rfl) ⟨3505001, by rfl⟩ : syracuseStep 4673335 = 7010003) B7010003
theorem B2461679 : Blo 1640019 2461679 := bstep (se 1 (by rfl) ⟨1846259, by rfl⟩ : syracuseStep 2461679 = 3692519) B3692519
theorem B2461691 : Blo 1640019 2461691 := bstep (se 1 (by rfl) ⟨1846268, by rfl⟩ : syracuseStep 2461691 = 3692537) B3692537
theorem B2461751 : Blo 1640019 2461751 := bstep (se 1 (by rfl) ⟨1846313, by rfl⟩ : syracuseStep 2461751 = 3692627) B3692627
theorem B9351247 : Blo 1640019 9351247 := bstep (se 1 (by rfl) ⟨7013435, by rfl⟩ : syracuseStep 9351247 = 14026871) B14026871
theorem B2461799 : Blo 1640019 2461799 := bstep (se 1 (by rfl) ⟨1846349, by rfl⟩ : syracuseStep 2461799 = 3692699) B3692699
theorem B3551375 : Blo 1640019 3551375 := bstep (se 1 (by rfl) ⟨2663531, by rfl⟩ : syracuseStep 3551375 = 5327063) B5327063
theorem B2461871 : Blo 1640019 2461871 := bstep (se 1 (by rfl) ⟨1846403, by rfl⟩ : syracuseStep 2461871 = 3692807) B3692807
theorem B28037339 : Blo 1640019 28037339 := bstep (se 1 (by rfl) ⟨21028004, by rfl⟩ : syracuseStep 28037339 = 42056009) B42056009
theorem B8302823 : Blo 1640019 8302823 := bstep (se 1 (by rfl) ⟨6227117, by rfl⟩ : syracuseStep 8302823 = 12454235) B12454235
theorem B9113897 : Blo 1640019 9113897 := bstep (se 2 (by rfl) ⟨3417711, by rfl⟩ : syracuseStep 9113897 = 6835423) B6835423
theorem B2462075 : Blo 1640019 2462075 := bstep (se 1 (by rfl) ⟨1846556, by rfl⟩ : syracuseStep 2462075 = 3693113) B3693113
theorem B89854535 : Blo 1640019 89854535 := bstep (se 1 (by rfl) ⟨67390901, by rfl⟩ : syracuseStep 89854535 = 134781803) B134781803
theorem B2462345 : Blo 1640019 2462345 := bstep (se 2 (by rfl) ⟨923379, by rfl⟩ : syracuseStep 2462345 = 1846759) B1846759
theorem B28046087 : Blo 1640019 28046087 := bstep (se 1 (by rfl) ⟨21034565, by rfl⟩ : syracuseStep 28046087 = 42069131) B42069131
theorem B8311571 : Blo 1640019 8311571 := bstep (se 1 (by rfl) ⟨6233678, by rfl⟩ : syracuseStep 8311571 = 12467357) B12467357
theorem B2462555 : Blo 1640019 2462555 := bstep (se 1 (by rfl) ⟨1846916, by rfl⟩ : syracuseStep 2462555 = 3693833) B3693833
theorem B25252879 : Blo 1640019 25252879 := bstep (se 1 (by rfl) ⟨18939659, by rfl⟩ : syracuseStep 25252879 = 37879319) B37879319
theorem B3200161 : Blo 1640019 3200161 := bstep (se 2 (by rfl) ⟨1200060, by rfl⟩ : syracuseStep 3200161 = 2400121) B2400121
theorem B3691727 : Blo 1640019 3691727 := bstep (se 1 (by rfl) ⟨2768795, by rfl⟩ : syracuseStep 3691727 = 5537591) B5537591
theorem B3503369 : Blo 1640019 3503369 := bstep (se 2 (by rfl) ⟨1313763, by rfl⟩ : syracuseStep 3503369 = 2627527) B2627527
theorem B3691817 : Blo 1640019 3691817 := bstep (se 2 (by rfl) ⟨1384431, by rfl⟩ : syracuseStep 3691817 = 2768863) B2768863
theorem B2463017 : Blo 1640019 2463017 := bstep (se 2 (by rfl) ⟨923631, by rfl⟩ : syracuseStep 2463017 = 1847263) B1847263
theorem B4494703 : Blo 1640019 4494703 := bstep (se 1 (by rfl) ⟨3371027, by rfl⟩ : syracuseStep 4494703 = 6742055) B6742055
theorem B3692015 : Blo 1640019 3692015 := bstep (se 1 (by rfl) ⟨2769011, by rfl⟩ : syracuseStep 3692015 = 5538023) B5538023
theorem B5535323 : Blo 1640019 5535323 := bstep (se 1 (by rfl) ⟨4151492, by rfl⟩ : syracuseStep 5535323 = 8302985) B8302985
theorem B12457637 : Blo 1640019 12457637 := bstep (se 4 (by rfl) ⟨1167903, by rfl⟩ : syracuseStep 12457637 = 2335807) B2335807
theorem B12465899 : Blo 1640019 12465899 := bstep (se 1 (by rfl) ⟨9349424, by rfl⟩ : syracuseStep 12465899 = 18698849) B18698849
theorem B2627419 : Blo 1640019 2627419 := bstep (se 1 (by rfl) ⟨1970564, by rfl⟩ : syracuseStep 2627419 = 3941129) B3941129
theorem B7010155 : Blo 1640019 7010155 := bstep (se 1 (by rfl) ⟨5257616, by rfl⟩ : syracuseStep 7010155 = 10515233) B10515233
theorem B3692411 : Blo 1640019 3692411 := bstep (se 1 (by rfl) ⟨2769308, by rfl⟩ : syracuseStep 3692411 = 5538617) B5538617
theorem B3692447 : Blo 1640019 3692447 := bstep (se 1 (by rfl) ⟨2769335, by rfl⟩ : syracuseStep 3692447 = 5538671) B5538671
theorem B10516463 : Blo 1640019 10516463 := bstep (se 1 (by rfl) ⟨7887347, by rfl⟩ : syracuseStep 10516463 = 15774695) B15774695
theorem B40458305 : Blo 1640019 40458305 := bstep (se 2 (by rfl) ⟨15171864, by rfl⟩ : syracuseStep 40458305 = 30343729) B30343729
theorem B3692681 : Blo 1640019 3692681 := bstep (se 2 (by rfl) ⟨1384755, by rfl⟩ : syracuseStep 3692681 = 2769511) B2769511
theorem B4675897 : Blo 1640019 4675897 := bstep (se 2 (by rfl) ⟨1753461, by rfl⟩ : syracuseStep 4675897 = 3506923) B3506923
theorem B3692897 : Blo 1640019 3692897 := bstep (se 2 (by rfl) ⟨1384836, by rfl⟩ : syracuseStep 3692897 = 2769673) B2769673
theorem B3692987 : Blo 1640019 3692987 := bstep (se 1 (by rfl) ⟨2769740, by rfl⟩ : syracuseStep 3692987 = 5539481) B5539481
theorem B3504865 : Blo 1640019 3504865 := bstep (se 2 (by rfl) ⟨1314324, by rfl⟩ : syracuseStep 3504865 = 2628649) B2628649
theorem B9984761 : Blo 1640019 9984761 := bstep (se 2 (by rfl) ⟨3744285, by rfl⟩ : syracuseStep 9984761 = 7488571) B7488571
theorem B6232889 : Blo 1640019 6232889 := bstep (se 2 (by rfl) ⟨2337333, by rfl⟩ : syracuseStep 6232889 = 4674667) B4674667
theorem B3693383 : Blo 1640019 3693383 := bstep (se 1 (by rfl) ⟨2770037, by rfl⟩ : syracuseStep 3693383 = 5540075) B5540075
theorem B2628463 : Blo 1640019 2628463 := bstep (se 1 (by rfl) ⟨1971347, by rfl⟩ : syracuseStep 2628463 = 3942695) B3942695
theorem B2767783 : Blo 1640019 2767783 := bstep (se 1 (by rfl) ⟨2075837, by rfl⟩ : syracuseStep 2767783 = 4151675) B4151675
theorem B3693689 : Blo 1640019 3693689 := bstep (se 2 (by rfl) ⟨1385133, by rfl⟩ : syracuseStep 3693689 = 2770267) B2770267
theorem B5537213 : Blo 1640019 5537213 := bstep (se 3 (by rfl) ⟨1038227, by rfl⟩ : syracuseStep 5537213 = 2076455) B2076455
theorem B4152809 : Blo 1640019 4152809 := bstep (se 2 (by rfl) ⟨1557303, by rfl⟩ : syracuseStep 4152809 = 3114607) B3114607
theorem B3505727 : Blo 1640019 3505727 := bstep (se 1 (by rfl) ⟨2629295, by rfl⟩ : syracuseStep 3505727 = 5258591) B5258591
theorem B7487111 : Blo 1640019 7487111 := bstep (se 1 (by rfl) ⟨5615333, by rfl⟩ : syracuseStep 7487111 = 11230667) B11230667
theorem B3694247 : Blo 1640019 3694247 := bstep (se 1 (by rfl) ⟨2770685, by rfl⟩ : syracuseStep 3694247 = 5541371) B5541371
theorem B9977539 : Blo 1640019 9977539 := bstep (se 1 (by rfl) ⟨7483154, by rfl⟩ : syracuseStep 9977539 = 14966309) B14966309
theorem B3694355 : Blo 1640019 3694355 := bstep (se 1 (by rfl) ⟨2770766, by rfl⟩ : syracuseStep 3694355 = 5541533) B5541533
theorem B12468329 : Blo 1640019 12468329 := bstep (se 2 (by rfl) ⟨4675623, by rfl⟩ : syracuseStep 12468329 = 9351247) B9351247
theorem B5259451 : Blo 1640019 5259451 := bstep (se 1 (by rfl) ⟨3944588, by rfl⟩ : syracuseStep 5259451 = 7889177) B7889177
theorem B5538131 : Blo 1640019 5538131 := bstep (se 1 (by rfl) ⟨4153598, by rfl⟩ : syracuseStep 5538131 = 8307197) B8307197
theorem B9470333 : Blo 1640019 9470333 := bstep (se 3 (by rfl) ⟨1775687, by rfl⟩ : syracuseStep 9470333 = 3551375) B3551375
theorem B6234529 : Blo 1640019 6234529 := bstep (se 2 (by rfl) ⟨2337948, by rfl⟩ : syracuseStep 6234529 = 4675897) B4675897
theorem B5260231 : Blo 1640019 5260231 := bstep (se 1 (by rfl) ⟨3945173, by rfl⟩ : syracuseStep 5260231 = 7890347) B7890347
theorem B10519591 : Blo 1640019 10519591 := bstep (se 1 (by rfl) ⟨7889693, by rfl⟩ : syracuseStep 10519591 = 15779387) B15779387
theorem B2770247 : Blo 1640019 2770247 := bstep (se 1 (by rfl) ⟨2077685, by rfl⟩ : syracuseStep 2770247 = 4155371) B4155371
theorem B33670505 : Blo 1640019 33670505 := bstep (se 2 (by rfl) ⟨12626439, by rfl⟩ : syracuseStep 33670505 = 25252879) B25252879
theorem B44918185 : Blo 1640019 44918185 := bstep (se 2 (by rfl) ⟨16844319, by rfl⟩ : syracuseStep 44918185 = 33688639) B33688639
theorem B9348605 : Blo 1640019 9348605 := bstep (se 3 (by rfl) ⟨1752863, by rfl⟩ : syracuseStep 9348605 = 3505727) B3505727
theorem B19965629 : Blo 1640019 19965629 := bstep (se 3 (by rfl) ⟨3743555, by rfl⟩ : syracuseStep 19965629 = 7487111) B7487111
theorem B1640175 : Blo 1640019 1640175 := bstep (se 1 (by rfl) ⟨1230131, by rfl⟩ : syracuseStep 1640175 = 2460263) B2460263
theorem B1640303 : Blo 1640019 1640303 := bstep (se 1 (by rfl) ⟨1230227, by rfl⟩ : syracuseStep 1640303 = 2460455) B2460455
theorem B4155259 : Blo 1640019 4155259 := bstep (se 1 (by rfl) ⟨3116444, by rfl⟩ : syracuseStep 4155259 = 6232889) B6232889
theorem B11224975 : Blo 1640019 11224975 := bstep (se 1 (by rfl) ⟨8418731, by rfl⟩ : syracuseStep 11224975 = 16837463) B16837463
theorem B6227999 : Blo 1640019 6227999 := bstep (se 1 (by rfl) ⟨4670999, by rfl⟩ : syracuseStep 6227999 = 9341999) B9341999
theorem B1640519 : Blo 1640019 1640519 := bstep (se 1 (by rfl) ⟨1230389, by rfl⟩ : syracuseStep 1640519 = 2460779) B2460779
theorem B1640679 : Blo 1640019 1640679 := bstep (se 1 (by rfl) ⟨1230509, by rfl⟩ : syracuseStep 1640679 = 2461019) B2461019
theorem B8308979 : Blo 1640019 8308979 := bstep (se 1 (by rfl) ⟨6231734, by rfl⟩ : syracuseStep 8308979 = 12463469) B12463469
theorem B1640699 : Blo 1640019 1640699 := bstep (se 1 (by rfl) ⟨1230524, by rfl⟩ : syracuseStep 1640699 = 2461049) B2461049
theorem B1640703 : Blo 1640019 1640703 := bstep (se 1 (by rfl) ⟨1230527, by rfl⟩ : syracuseStep 1640703 = 2461055) B2461055
theorem B2460041 : Blo 1640019 2460041 := bstep (se 2 (by rfl) ⟨922515, by rfl⟩ : syracuseStep 2460041 = 1845031) B1845031
theorem B1641119 : Blo 1640019 1641119 := bstep (se 1 (by rfl) ⟨1230839, by rfl⟩ : syracuseStep 1641119 = 2461679) B2461679
theorem B1641127 : Blo 1640019 1641127 := bstep (se 1 (by rfl) ⟨1230845, by rfl⟩ : syracuseStep 1641127 = 2461691) B2461691
theorem B1641167 : Blo 1640019 1641167 := bstep (se 1 (by rfl) ⟨1230875, by rfl⟩ : syracuseStep 1641167 = 2461751) B2461751
theorem B1641199 : Blo 1640019 1641199 := bstep (se 1 (by rfl) ⟨1230899, by rfl⟩ : syracuseStep 1641199 = 2461799) B2461799
theorem B1641247 : Blo 1640019 1641247 := bstep (se 1 (by rfl) ⟨1230935, by rfl⟩ : syracuseStep 1641247 = 2461871) B2461871
theorem B2337607 : Blo 1640019 2337607 := bstep (se 1 (by rfl) ⟨1753205, by rfl⟩ : syracuseStep 2337607 = 3506411) B3506411
theorem B1641383 : Blo 1640019 1641383 := bstep (se 1 (by rfl) ⟨1231037, by rfl⟩ : syracuseStep 1641383 = 2462075) B2462075
theorem B70937531 : Blo 1640019 70937531 := bstep (se 1 (by rfl) ⟨53203148, by rfl⟩ : syracuseStep 70937531 = 106406297) B106406297
theorem B59903023 : Blo 1640019 59903023 := bstep (se 1 (by rfl) ⟨44927267, by rfl⟩ : syracuseStep 59903023 = 89854535) B89854535
theorem B1641563 : Blo 1640019 1641563 := bstep (se 1 (by rfl) ⟨1231172, by rfl⟩ : syracuseStep 1641563 = 2462345) B2462345
theorem B18697391 : Blo 1640019 18697391 := bstep (se 1 (by rfl) ⟨14023043, by rfl⟩ : syracuseStep 18697391 = 28046087) B28046087
theorem B5541047 : Blo 1640019 5541047 := bstep (se 1 (by rfl) ⟨4155785, by rfl⟩ : syracuseStep 5541047 = 8311571) B8311571
theorem B4992187 : Blo 1640019 4992187 := bstep (se 1 (by rfl) ⟨3744140, by rfl⟩ : syracuseStep 4992187 = 7488281) B7488281
theorem B1641703 : Blo 1640019 1641703 := bstep (se 1 (by rfl) ⟨1231277, by rfl⟩ : syracuseStep 1641703 = 2462555) B2462555
theorem B9342317 : Blo 1640019 9342317 := bstep (se 3 (by rfl) ⟨1751684, by rfl⟩ : syracuseStep 9342317 = 3503369) B3503369
theorem B4435327 : Blo 1640019 4435327 := bstep (se 1 (by rfl) ⟨3326495, by rfl⟩ : syracuseStep 4435327 = 6652991) B6652991
theorem B1846687 : Blo 1640019 1846687 := bstep (se 1 (by rfl) ⟨1385015, by rfl⟩ : syracuseStep 1846687 = 2770031) B2770031
theorem B2461151 : Blo 1640019 2461151 := bstep (se 1 (by rfl) ⟨1845863, by rfl⟩ : syracuseStep 2461151 = 3691727) B3691727
theorem B2461211 : Blo 1640019 2461211 := bstep (se 1 (by rfl) ⟨1845908, by rfl⟩ : syracuseStep 2461211 = 3691817) B3691817
theorem B1642011 : Blo 1640019 1642011 := bstep (se 1 (by rfl) ⟨1231508, by rfl⟩ : syracuseStep 1642011 = 2463017) B2463017
theorem B4673153 : Blo 1640019 4673153 := bstep (se 2 (by rfl) ⟨1752432, by rfl⟩ : syracuseStep 4673153 = 3504865) B3504865
theorem B2461343 : Blo 1640019 2461343 := bstep (se 1 (by rfl) ⟨1846007, by rfl⟩ : syracuseStep 2461343 = 3692015) B3692015
theorem B1846975 : Blo 1640019 1846975 := bstep (se 1 (by rfl) ⟨1385231, by rfl⟩ : syracuseStep 1846975 = 2770463) B2770463
theorem B3690215 : Blo 1640019 3690215 := bstep (se 1 (by rfl) ⟨2767661, by rfl⟩ : syracuseStep 3690215 = 5535323) B5535323
theorem B8310599 : Blo 1640019 8310599 := bstep (se 1 (by rfl) ⟨6232949, by rfl⟩ : syracuseStep 8310599 = 12465899) B12465899
theorem B3690377 : Blo 1640019 3690377 := bstep (se 2 (by rfl) ⟨1383891, by rfl⟩ : syracuseStep 3690377 = 2767783) B2767783
theorem B2461607 : Blo 1640019 2461607 := bstep (se 1 (by rfl) ⟨1846205, by rfl⟩ : syracuseStep 2461607 = 3692411) B3692411
theorem B2461631 : Blo 1640019 2461631 := bstep (se 1 (by rfl) ⟨1846223, by rfl⟩ : syracuseStep 2461631 = 3692447) B3692447
theorem B26972203 : Blo 1640019 26972203 := bstep (se 1 (by rfl) ⟨20229152, by rfl⟩ : syracuseStep 26972203 = 40458305) B40458305
theorem B2461787 : Blo 1640019 2461787 := bstep (se 1 (by rfl) ⟨1846340, by rfl⟩ : syracuseStep 2461787 = 3692681) B3692681
theorem B2076779 : Blo 1640019 2076779 := bstep (se 1 (by rfl) ⟨1557584, by rfl⟩ : syracuseStep 2076779 = 3115169) B3115169
theorem B18935963 : Blo 1640019 18935963 := bstep (se 1 (by rfl) ⟨14201972, by rfl⟩ : syracuseStep 18935963 = 28403945) B28403945
theorem B2461931 : Blo 1640019 2461931 := bstep (se 1 (by rfl) ⟨1846448, by rfl⟩ : syracuseStep 2461931 = 3692897) B3692897
theorem B2461991 : Blo 1640019 2461991 := bstep (se 1 (by rfl) ⟨1846493, by rfl⟩ : syracuseStep 2461991 = 3692987) B3692987
theorem B31527245 : Blo 1640019 31527245 := bstep (se 3 (by rfl) ⟨5911358, by rfl⟩ : syracuseStep 31527245 = 11822717) B11822717
theorem B9343457 : Blo 1640019 9343457 := bstep (se 2 (by rfl) ⟨3503796, by rfl⟩ : syracuseStep 9343457 = 7007593) B7007593
theorem B5992937 : Blo 1640019 5992937 := bstep (se 2 (by rfl) ⟨2247351, by rfl⟩ : syracuseStep 5992937 = 4494703) B4494703
theorem B6656507 : Blo 1640019 6656507 := bstep (se 1 (by rfl) ⟨4992380, by rfl⟩ : syracuseStep 6656507 = 9984761) B9984761
theorem B2462255 : Blo 1640019 2462255 := bstep (se 1 (by rfl) ⟨1846691, by rfl⟩ : syracuseStep 2462255 = 3693383) B3693383
theorem B2462459 : Blo 1640019 2462459 := bstep (se 1 (by rfl) ⟨1846844, by rfl⟩ : syracuseStep 2462459 = 3693689) B3693689
theorem B3691475 : Blo 1640019 3691475 := bstep (se 1 (by rfl) ⟨2768606, by rfl⟩ : syracuseStep 3691475 = 5537213) B5537213
theorem B7009267 : Blo 1640019 7009267 := bstep (se 1 (by rfl) ⟨5256950, by rfl⟩ : syracuseStep 7009267 = 10513901) B10513901
theorem B6231113 : Blo 1640019 6231113 := bstep (se 2 (by rfl) ⟨2336667, by rfl⟩ : syracuseStep 6231113 = 4673335) B4673335
theorem B2462831 : Blo 1640019 2462831 := bstep (se 1 (by rfl) ⟨1847123, by rfl⟩ : syracuseStep 2462831 = 3694247) B3694247
theorem B3503225 : Blo 1640019 3503225 := bstep (se 2 (by rfl) ⟨1313709, by rfl⟩ : syracuseStep 3503225 = 2627419) B2627419
theorem B2462903 : Blo 1640019 2462903 := bstep (se 1 (by rfl) ⟨1847177, by rfl⟩ : syracuseStep 2462903 = 3694355) B3694355
theorem B18691559 : Blo 1640019 18691559 := bstep (se 1 (by rfl) ⟨14018669, by rfl⟩ : syracuseStep 18691559 = 28037339) B28037339
theorem B5535215 : Blo 1640019 5535215 := bstep (se 1 (by rfl) ⟨4151411, by rfl⟩ : syracuseStep 5535215 = 8302823) B8302823
theorem B6075931 : Blo 1640019 6075931 := bstep (se 1 (by rfl) ⟨4556948, by rfl⟩ : syracuseStep 6075931 = 9113897) B9113897
theorem B6231887 : Blo 1640019 6231887 := bstep (se 1 (by rfl) ⟨4673915, by rfl⟩ : syracuseStep 6231887 = 9347831) B9347831
theorem B7886717 : Blo 1640019 7886717 := bstep (se 3 (by rfl) ⟨1478759, by rfl⟩ : syracuseStep 7886717 = 2957519) B2957519
theorem B18954337 : Blo 1640019 18954337 := bstep (se 2 (by rfl) ⟨7107876, by rfl⟩ : syracuseStep 18954337 = 14215753) B14215753
theorem B4151483 : Blo 1640019 4151483 := bstep (se 1 (by rfl) ⟨3113612, by rfl⟩ : syracuseStep 4151483 = 6227225) B6227225
theorem B3692735 : Blo 1640019 3692735 := bstep (se 1 (by rfl) ⟨2769551, by rfl⟩ : syracuseStep 3692735 = 5539103) B5539103
theorem B18684269 : Blo 1640019 18684269 := bstep (se 3 (by rfl) ⟨3503300, by rfl⟩ : syracuseStep 18684269 = 7006601) B7006601
theorem B8305091 : Blo 1640019 8305091 := bstep (se 1 (by rfl) ⟨6228818, by rfl⟩ : syracuseStep 8305091 = 12457637) B12457637
theorem B10508777 : Blo 1640019 10508777 := bstep (se 2 (by rfl) ⟨3940791, by rfl⟩ : syracuseStep 10508777 = 7881583) B7881583
theorem B3504617 : Blo 1640019 3504617 := bstep (se 2 (by rfl) ⟨1314231, by rfl⟩ : syracuseStep 3504617 = 2628463) B2628463
theorem B7010975 : Blo 1640019 7010975 := bstep (se 1 (by rfl) ⟨5258231, by rfl⟩ : syracuseStep 7010975 = 10516463) B10516463
theorem B2628347 : Blo 1640019 2628347 := bstep (se 1 (by rfl) ⟨1971260, by rfl⟩ : syracuseStep 2628347 = 3942521) B3942521
theorem B4266881 : Blo 1640019 4266881 := bstep (se 2 (by rfl) ⟨1600080, by rfl⟩ : syracuseStep 4266881 = 3200161) B3200161
theorem B2956343 : Blo 1640019 2956343 := bstep (se 1 (by rfl) ⟨2217257, by rfl⟩ : syracuseStep 2956343 = 4434515) B4434515
theorem B2767945 : Blo 1640019 2767945 := bstep (se 2 (by rfl) ⟨1037979, by rfl⟩ : syracuseStep 2767945 = 2075959) B2075959
theorem B3693779 : Blo 1640019 3693779 := bstep (se 1 (by rfl) ⟨2770334, by rfl⟩ : syracuseStep 3693779 = 5540669) B5540669
theorem B3693851 : Blo 1640019 3693851 := bstep (se 1 (by rfl) ⟨2770388, by rfl⟩ : syracuseStep 3693851 = 5540777) B5540777
theorem B3694049 : Blo 1640019 3694049 := bstep (se 2 (by rfl) ⟨1385268, by rfl⟩ : syracuseStep 3694049 = 2770537) B2770537
theorem B13303385 : Blo 1640019 13303385 := bstep (se 2 (by rfl) ⟨4988769, by rfl⟩ : syracuseStep 13303385 = 9977539) B9977539
theorem B2768539 : Blo 1640019 2768539 := bstep (se 1 (by rfl) ⟨2076404, by rfl⟩ : syracuseStep 2768539 = 4152809) B4152809
theorem B9346873 : Blo 1640019 9346873 := bstep (se 2 (by rfl) ⟨3505077, by rfl⟩ : syracuseStep 9346873 = 7010155) B7010155
theorem B42082253 : Blo 1640019 42082253 := bstep (se 3 (by rfl) ⟨7890422, by rfl⟩ : syracuseStep 42082253 = 15780845) B15780845
theorem B35962937 : Blo 1640019 35962937 := bstep (se 2 (by rfl) ⟨13486101, by rfl⟩ : syracuseStep 35962937 = 26972203) B26972203
theorem B12623975 : Blo 1640019 12623975 := bstep (se 1 (by rfl) ⟨9467981, by rfl⟩ : syracuseStep 12623975 = 18935963) B18935963
theorem B25272449 : Blo 1640019 25272449 := bstep (se 2 (by rfl) ⟨9477168, by rfl⟩ : syracuseStep 25272449 = 18954337) B18954337
theorem B7012601 : Blo 1640019 7012601 := bstep (se 2 (by rfl) ⟨2629725, by rfl⟩ : syracuseStep 7012601 = 5259451) B5259451
theorem B5538077 : Blo 1640019 5538077 := bstep (se 3 (by rfl) ⟨1038389, by rfl⟩ : syracuseStep 5538077 = 2076779) B2076779
theorem B4154075 : Blo 1640019 4154075 := bstep (se 1 (by rfl) ⟨3115556, by rfl⟩ : syracuseStep 4154075 = 6231113) B6231113
theorem B2335483 : Blo 1640019 2335483 := bstep (se 1 (by rfl) ⟨1751612, by rfl⟩ : syracuseStep 2335483 = 3503225) B3503225
theorem B22447003 : Blo 1640019 22447003 := bstep (se 1 (by rfl) ⟨16835252, by rfl⟩ : syracuseStep 22447003 = 33670505) B33670505
theorem B12461039 : Blo 1640019 12461039 := bstep (se 1 (by rfl) ⟨9345779, by rfl⟩ : syracuseStep 12461039 = 18691559) B18691559
theorem B4154591 : Blo 1640019 4154591 := bstep (se 1 (by rfl) ⟨3115943, by rfl⟩ : syracuseStep 4154591 = 6231887) B6231887
theorem B7013641 : Blo 1640019 7013641 := bstep (se 2 (by rfl) ⟨2630115, by rfl⟩ : syracuseStep 7013641 = 5260231) B5260231
theorem B14026121 : Blo 1640019 14026121 := bstep (se 2 (by rfl) ⟨5259795, by rfl⟩ : syracuseStep 14026121 = 10519591) B10519591
theorem B5539319 : Blo 1640019 5539319 := bstep (se 1 (by rfl) ⟨4154489, by rfl⟩ : syracuseStep 5539319 = 8308979) B8308979
theorem B1640027 : Blo 1640019 1640027 := bstep (se 1 (by rfl) ⟨1230020, by rfl⟩ : syracuseStep 1640027 = 2460041) B2460041
theorem B7005851 : Blo 1640019 7005851 := bstep (se 1 (by rfl) ⟨5254388, by rfl⟩ : syracuseStep 7005851 = 10508777) B10508777
theorem B2336411 : Blo 1640019 2336411 := bstep (se 1 (by rfl) ⟨1752308, by rfl⟩ : syracuseStep 2336411 = 3504617) B3504617
theorem B18695933 : Blo 1640019 18695933 := bstep (se 3 (by rfl) ⟨3505487, by rfl⟩ : syracuseStep 18695933 = 7010975) B7010975
theorem B2844587 : Blo 1640019 2844587 := bstep (se 1 (by rfl) ⟨2133440, by rfl⟩ : syracuseStep 2844587 = 4266881) B4266881
theorem B6228211 : Blo 1640019 6228211 := bstep (se 1 (by rfl) ⟨4671158, by rfl⟩ : syracuseStep 6228211 = 9342317) B9342317
theorem B1640767 : Blo 1640019 1640767 := bstep (se 1 (by rfl) ⟨1230575, by rfl⟩ : syracuseStep 1640767 = 2461151) B2461151
theorem B1640807 : Blo 1640019 1640807 := bstep (se 1 (by rfl) ⟨1230605, by rfl⟩ : syracuseStep 1640807 = 2461211) B2461211
theorem B12462497 : Blo 1640019 12462497 := bstep (se 2 (by rfl) ⟨4673436, by rfl⟩ : syracuseStep 12462497 = 9346873) B9346873
theorem B3115435 : Blo 1640019 3115435 := bstep (se 1 (by rfl) ⟨2336576, by rfl⟩ : syracuseStep 3115435 = 4673153) B4673153
theorem B1640895 : Blo 1640019 1640895 := bstep (se 1 (by rfl) ⟨1230671, by rfl⟩ : syracuseStep 1640895 = 2461343) B2461343
theorem B2460143 : Blo 1640019 2460143 := bstep (se 1 (by rfl) ⟨1845107, by rfl⟩ : syracuseStep 2460143 = 3690215) B3690215
theorem B5540345 : Blo 1640019 5540345 := bstep (se 2 (by rfl) ⟨2077629, by rfl⟩ : syracuseStep 5540345 = 4155259) B4155259
theorem B5540399 : Blo 1640019 5540399 := bstep (se 1 (by rfl) ⟨4155299, by rfl⟩ : syracuseStep 5540399 = 8310599) B8310599
theorem B2460251 : Blo 1640019 2460251 := bstep (se 1 (by rfl) ⟨1845188, by rfl⟩ : syracuseStep 2460251 = 3690377) B3690377
theorem B1641071 : Blo 1640019 1641071 := bstep (se 1 (by rfl) ⟨1230803, by rfl⟩ : syracuseStep 1641071 = 2461607) B2461607
theorem B1641087 : Blo 1640019 1641087 := bstep (se 1 (by rfl) ⟨1230815, by rfl⟩ : syracuseStep 1641087 = 2461631) B2461631
theorem B1641191 : Blo 1640019 1641191 := bstep (se 1 (by rfl) ⟨1230893, by rfl⟩ : syracuseStep 1641191 = 2461787) B2461787
theorem B7883581 : Blo 1640019 7883581 := bstep (se 3 (by rfl) ⟨1478171, by rfl⟩ : syracuseStep 7883581 = 2956343) B2956343
theorem B1641287 : Blo 1640019 1641287 := bstep (se 1 (by rfl) ⟨1230965, by rfl⟩ : syracuseStep 1641287 = 2461931) B2461931
theorem B1641327 : Blo 1640019 1641327 := bstep (se 1 (by rfl) ⟨1230995, by rfl⟩ : syracuseStep 1641327 = 2461991) B2461991
theorem B6228971 : Blo 1640019 6228971 := bstep (se 1 (by rfl) ⟨4671728, by rfl⟩ : syracuseStep 6228971 = 9343457) B9343457
theorem B1641503 : Blo 1640019 1641503 := bstep (se 1 (by rfl) ⟨1231127, by rfl⟩ : syracuseStep 1641503 = 2462255) B2462255
theorem B1641639 : Blo 1640019 1641639 := bstep (se 1 (by rfl) ⟨1231229, by rfl⟩ : syracuseStep 1641639 = 2462459) B2462459
theorem B2460983 : Blo 1640019 2460983 := bstep (se 1 (by rfl) ⟨1845737, by rfl⟩ : syracuseStep 2460983 = 3691475) B3691475
theorem B1641887 : Blo 1640019 1641887 := bstep (se 1 (by rfl) ⟨1231415, by rfl⟩ : syracuseStep 1641887 = 2462831) B2462831
theorem B1641935 : Blo 1640019 1641935 := bstep (se 1 (by rfl) ⟨1231451, by rfl⟩ : syracuseStep 1641935 = 2462903) B2462903
theorem B1846831 : Blo 1640019 1846831 := bstep (se 1 (by rfl) ⟨1385123, by rfl⟩ : syracuseStep 1846831 = 2770247) B2770247
theorem B3690143 : Blo 1640019 3690143 := bstep (se 1 (by rfl) ⟨2767607, by rfl⟩ : syracuseStep 3690143 = 5535215) B5535215
theorem B3116809 : Blo 1640019 3116809 := bstep (se 2 (by rfl) ⟨1168803, by rfl⟩ : syracuseStep 3116809 = 2337607) B2337607
theorem B3690593 : Blo 1640019 3690593 := bstep (se 2 (by rfl) ⟨1383972, by rfl⟩ : syracuseStep 3690593 = 2767945) B2767945
theorem B2461823 : Blo 1640019 2461823 := bstep (se 1 (by rfl) ⟨1846367, by rfl⟩ : syracuseStep 2461823 = 3692735) B3692735
theorem B12456179 : Blo 1640019 12456179 := bstep (se 1 (by rfl) ⟨9342134, by rfl⟩ : syracuseStep 12456179 = 18684269) B18684269
theorem B6656249 : Blo 1640019 6656249 := bstep (se 2 (by rfl) ⟨2496093, by rfl⟩ : syracuseStep 6656249 = 4992187) B4992187
theorem B2462249 : Blo 1640019 2462249 := bstep (se 2 (by rfl) ⟨923343, by rfl⟩ : syracuseStep 2462249 = 1846687) B1846687
theorem B7008925 : Blo 1640019 7008925 := bstep (se 3 (by rfl) ⟨1314173, by rfl⟩ : syracuseStep 7008925 = 2628347) B2628347
theorem B12464927 : Blo 1640019 12464927 := bstep (se 1 (by rfl) ⟨9348695, by rfl⟩ : syracuseStep 12464927 = 18697391) B18697391
theorem B2462519 : Blo 1640019 2462519 := bstep (se 1 (by rfl) ⟨1846889, by rfl⟩ : syracuseStep 2462519 = 3693779) B3693779
theorem B2462567 : Blo 1640019 2462567 := bstep (se 1 (by rfl) ⟨1846925, by rfl⟩ : syracuseStep 2462567 = 3693851) B3693851
theorem B3691385 : Blo 1640019 3691385 := bstep (se 2 (by rfl) ⟨1384269, by rfl⟩ : syracuseStep 3691385 = 2768539) B2768539
theorem B2462633 : Blo 1640019 2462633 := bstep (se 2 (by rfl) ⟨923487, by rfl⟩ : syracuseStep 2462633 = 1846975) B1846975
theorem B2462699 : Blo 1640019 2462699 := bstep (se 1 (by rfl) ⟨1847024, by rfl⟩ : syracuseStep 2462699 = 3694049) B3694049
theorem B8868923 : Blo 1640019 8868923 := bstep (se 1 (by rfl) ⟨6651692, by rfl⟩ : syracuseStep 8868923 = 13303385) B13303385
theorem B28054835 : Blo 1640019 28054835 := bstep (se 1 (by rfl) ⟨21041126, by rfl⟩ : syracuseStep 28054835 = 42082253) B42082253
theorem B8312219 : Blo 1640019 8312219 := bstep (se 1 (by rfl) ⟨6234164, by rfl⟩ : syracuseStep 8312219 = 12468329) B12468329
theorem B21018163 : Blo 1640019 21018163 := bstep (se 1 (by rfl) ⟨15763622, by rfl⟩ : syracuseStep 21018163 = 31527245) B31527245
theorem B3692087 : Blo 1640019 3692087 := bstep (se 1 (by rfl) ⟨2769065, by rfl⟩ : syracuseStep 3692087 = 5538131) B5538131
theorem B6313555 : Blo 1640019 6313555 := bstep (se 1 (by rfl) ⟨4735166, by rfl⟩ : syracuseStep 6313555 = 9470333) B9470333
theorem B3995291 : Blo 1640019 3995291 := bstep (se 1 (by rfl) ⟨2996468, by rfl⟩ : syracuseStep 3995291 = 5992937) B5992937
theorem B4437671 : Blo 1640019 4437671 := bstep (se 1 (by rfl) ⟨3328253, by rfl⟩ : syracuseStep 4437671 = 6656507) B6656507
theorem B8312705 : Blo 1640019 8312705 := bstep (se 2 (by rfl) ⟨3117264, by rfl⟩ : syracuseStep 8312705 = 6234529) B6234529
theorem B6232403 : Blo 1640019 6232403 := bstep (se 1 (by rfl) ⟨4674302, by rfl⟩ : syracuseStep 6232403 = 9348605) B9348605
theorem B13310419 : Blo 1640019 13310419 := bstep (se 1 (by rfl) ⟨9982814, by rfl⟩ : syracuseStep 13310419 = 19965629) B19965629
theorem B5257811 : Blo 1640019 5257811 := bstep (se 1 (by rfl) ⟨3943358, by rfl⟩ : syracuseStep 5257811 = 7886717) B7886717
theorem B9345689 : Blo 1640019 9345689 := bstep (se 2 (by rfl) ⟨3504633, by rfl⟩ : syracuseStep 9345689 = 7009267) B7009267
theorem B4151999 : Blo 1640019 4151999 := bstep (se 1 (by rfl) ⟨3113999, by rfl⟩ : syracuseStep 4151999 = 6227999) B6227999
theorem B79870697 : Blo 1640019 79870697 := bstep (se 2 (by rfl) ⟨29951511, by rfl⟩ : syracuseStep 79870697 = 59903023) B59903023
theorem B2767655 : Blo 1640019 2767655 := bstep (se 1 (by rfl) ⟨2075741, by rfl⟩ : syracuseStep 2767655 = 4151483) B4151483
theorem B5536727 : Blo 1640019 5536727 := bstep (se 1 (by rfl) ⟨4152545, by rfl⟩ : syracuseStep 5536727 = 8305091) B8305091
theorem B5913769 : Blo 1640019 5913769 := bstep (se 2 (by rfl) ⟨2217663, by rfl⟩ : syracuseStep 5913769 = 4435327) B4435327
theorem B59890913 : Blo 1640019 59890913 := bstep (se 2 (by rfl) ⟨22459092, by rfl⟩ : syracuseStep 59890913 = 44918185) B44918185
theorem B47291687 : Blo 1640019 47291687 := bstep (se 1 (by rfl) ⟨35468765, by rfl⟩ : syracuseStep 47291687 = 70937531) B70937531
theorem B8101241 : Blo 1640019 8101241 := bstep (se 2 (by rfl) ⟨3037965, by rfl⟩ : syracuseStep 8101241 = 6075931) B6075931
theorem B3694031 : Blo 1640019 3694031 := bstep (se 1 (by rfl) ⟨2770523, by rfl⟩ : syracuseStep 3694031 = 5541047) B5541047
theorem B14966633 : Blo 1640019 14966633 := bstep (se 2 (by rfl) ⟨5612487, by rfl⟩ : syracuseStep 14966633 = 11224975) B11224975
theorem B2769383 : Blo 1640019 2769383 := bstep (se 1 (by rfl) ⟨2077037, by rfl⟩ : syracuseStep 2769383 = 4154075) B4154075
theorem B4153913 : Blo 1640019 4153913 := bstep (se 2 (by rfl) ⟨1557717, by rfl⟩ : syracuseStep 4153913 = 3115435) B3115435
theorem B8307359 : Blo 1640019 8307359 := bstep (se 1 (by rfl) ⟨6230519, by rfl⟩ : syracuseStep 8307359 = 12461039) B12461039
theorem B2769727 : Blo 1640019 2769727 := bstep (se 1 (by rfl) ⟨2077295, by rfl⟩ : syracuseStep 2769727 = 4154591) B4154591
theorem B18703223 : Blo 1640019 18703223 := bstep (se 1 (by rfl) ⟨14027417, by rfl⟩ : syracuseStep 18703223 = 28054835) B28054835
theorem B3113977 : Blo 1640019 3113977 := bstep (se 2 (by rfl) ⟨1167741, by rfl⟩ : syracuseStep 3113977 = 2335483) B2335483
theorem B10511441 : Blo 1640019 10511441 := bstep (se 2 (by rfl) ⟨3941790, by rfl⟩ : syracuseStep 10511441 = 7883581) B7883581
theorem B4670567 : Blo 1640019 4670567 := bstep (se 1 (by rfl) ⟨3502925, by rfl⟩ : syracuseStep 4670567 = 7005851) B7005851
theorem B2663527 : Blo 1640019 2663527 := bstep (se 1 (by rfl) ⟨1997645, by rfl⟩ : syracuseStep 2663527 = 3995291) B3995291
theorem B4154935 : Blo 1640019 4154935 := bstep (se 1 (by rfl) ⟨3116201, by rfl⟩ : syracuseStep 4154935 = 6232403) B6232403
theorem B8308331 : Blo 1640019 8308331 := bstep (se 1 (by rfl) ⟨6231248, by rfl⟩ : syracuseStep 8308331 = 12462497) B12462497
theorem B1640095 : Blo 1640019 1640095 := bstep (se 1 (by rfl) ⟨1230071, by rfl⟩ : syracuseStep 1640095 = 2460143) B2460143
theorem B1640167 : Blo 1640019 1640167 := bstep (se 1 (by rfl) ⟨1230125, by rfl⟩ : syracuseStep 1640167 = 2460251) B2460251
theorem B1845103 : Blo 1640019 1845103 := bstep (se 1 (by rfl) ⟨1383827, by rfl⟩ : syracuseStep 1845103 = 2767655) B2767655
theorem B1640655 : Blo 1640019 1640655 := bstep (se 1 (by rfl) ⟨1230491, by rfl⟩ : syracuseStep 1640655 = 2460983) B2460983
theorem B5400827 : Blo 1640019 5400827 := bstep (se 1 (by rfl) ⟨4050620, by rfl⟩ : syracuseStep 5400827 = 8101241) B8101241
theorem B4155745 : Blo 1640019 4155745 := bstep (se 2 (by rfl) ⟨1558404, by rfl⟩ : syracuseStep 4155745 = 3116809) B3116809
theorem B2460095 : Blo 1640019 2460095 := bstep (se 1 (by rfl) ⟨1845071, by rfl⟩ : syracuseStep 2460095 = 3690143) B3690143
theorem B2460395 : Blo 1640019 2460395 := bstep (se 1 (by rfl) ⟨1845296, by rfl⟩ : syracuseStep 2460395 = 3690593) B3690593
theorem B8415983 : Blo 1640019 8415983 := bstep (se 1 (by rfl) ⟨6311987, by rfl⟩ : syracuseStep 8415983 = 12623975) B12623975
theorem B1641215 : Blo 1640019 1641215 := bstep (se 1 (by rfl) ⟨1230911, by rfl⟩ : syracuseStep 1641215 = 2461823) B2461823
theorem B1641499 : Blo 1640019 1641499 := bstep (se 1 (by rfl) ⟨1231124, by rfl⟩ : syracuseStep 1641499 = 2462249) B2462249
theorem B8309951 : Blo 1640019 8309951 := bstep (se 1 (by rfl) ⟨6232463, by rfl⟩ : syracuseStep 8309951 = 12464927) B12464927
theorem B1641679 : Blo 1640019 1641679 := bstep (se 1 (by rfl) ⟨1231259, by rfl⟩ : syracuseStep 1641679 = 2462519) B2462519
theorem B1641711 : Blo 1640019 1641711 := bstep (se 1 (by rfl) ⟨1231283, by rfl⟩ : syracuseStep 1641711 = 2462567) B2462567
theorem B2460923 : Blo 1640019 2460923 := bstep (se 1 (by rfl) ⟨1845692, by rfl⟩ : syracuseStep 2460923 = 3691385) B3691385
theorem B17747225 : Blo 1640019 17747225 := bstep (se 2 (by rfl) ⟨6655209, by rfl⟩ : syracuseStep 17747225 = 13310419) B13310419
theorem B1641755 : Blo 1640019 1641755 := bstep (se 1 (by rfl) ⟨1231316, by rfl⟩ : syracuseStep 1641755 = 2462633) B2462633
theorem B1641799 : Blo 1640019 1641799 := bstep (se 1 (by rfl) ⟨1231349, by rfl⟩ : syracuseStep 1641799 = 2462699) B2462699
theorem B9350747 : Blo 1640019 9350747 := bstep (se 1 (by rfl) ⟨7013060, by rfl⟩ : syracuseStep 9350747 = 14026121) B14026121
theorem B5541479 : Blo 1640019 5541479 := bstep (se 1 (by rfl) ⟨4156109, by rfl⟩ : syracuseStep 5541479 = 8312219) B8312219
theorem B2461391 : Blo 1640019 2461391 := bstep (se 1 (by rfl) ⟨1846043, by rfl⟩ : syracuseStep 2461391 = 3692087) B3692087
theorem B12463955 : Blo 1640019 12463955 := bstep (se 1 (by rfl) ⟨9347966, by rfl⟩ : syracuseStep 12463955 = 18695933) B18695933
theorem B29929337 : Blo 1640019 29929337 := bstep (se 2 (by rfl) ⟨11223501, by rfl⟩ : syracuseStep 29929337 = 22447003) B22447003
theorem B5541803 : Blo 1640019 5541803 := bstep (se 1 (by rfl) ⟨4156352, by rfl⟩ : syracuseStep 5541803 = 8312705) B8312705
theorem B1896391 : Blo 1640019 1896391 := bstep (se 1 (by rfl) ⟨1422293, by rfl⟩ : syracuseStep 1896391 = 2844587) B2844587
theorem B7885025 : Blo 1640019 7885025 := bstep (se 2 (by rfl) ⟨2956884, by rfl⟩ : syracuseStep 7885025 = 5913769) B5913769
theorem B9351521 : Blo 1640019 9351521 := bstep (se 2 (by rfl) ⟨3506820, by rfl⟩ : syracuseStep 9351521 = 7013641) B7013641
theorem B6230429 : Blo 1640019 6230429 := bstep (se 3 (by rfl) ⟨1168205, by rfl⟩ : syracuseStep 6230429 = 2336411) B2336411
theorem B6230459 : Blo 1640019 6230459 := bstep (se 1 (by rfl) ⟨4672844, by rfl⟩ : syracuseStep 6230459 = 9345689) B9345689
theorem B11833789 : Blo 1640019 11833789 := bstep (se 3 (by rfl) ⟨2218835, by rfl⟩ : syracuseStep 11833789 = 4437671) B4437671
theorem B3691151 : Blo 1640019 3691151 := bstep (se 1 (by rfl) ⟨2768363, by rfl⟩ : syracuseStep 3691151 = 5536727) B5536727
theorem B2462441 : Blo 1640019 2462441 := bstep (se 2 (by rfl) ⟨923415, by rfl⟩ : syracuseStep 2462441 = 1846831) B1846831
theorem B8418073 : Blo 1640019 8418073 := bstep (se 2 (by rfl) ⟨3156777, by rfl⟩ : syracuseStep 8418073 = 6313555) B6313555
theorem B31527791 : Blo 1640019 31527791 := bstep (se 1 (by rfl) ⟨23645843, by rfl⟩ : syracuseStep 31527791 = 47291687) B47291687
theorem B2462687 : Blo 1640019 2462687 := bstep (se 1 (by rfl) ⟨1847015, by rfl⟩ : syracuseStep 2462687 = 3694031) B3694031
theorem B23975291 : Blo 1640019 23975291 := bstep (se 1 (by rfl) ⟨17981468, by rfl⟩ : syracuseStep 23975291 = 35962937) B35962937
theorem B16848299 : Blo 1640019 16848299 := bstep (se 1 (by rfl) ⟨12636224, by rfl⟩ : syracuseStep 16848299 = 25272449) B25272449
theorem B8304119 : Blo 1640019 8304119 := bstep (se 1 (by rfl) ⟨6228089, by rfl⟩ : syracuseStep 8304119 = 12456179) B12456179
theorem B4437499 : Blo 1640019 4437499 := bstep (se 1 (by rfl) ⟨3328124, by rfl⟩ : syracuseStep 4437499 = 6656249) B6656249
theorem B4675067 : Blo 1640019 4675067 := bstep (se 1 (by rfl) ⟨3506300, by rfl⟩ : syracuseStep 4675067 = 7012601) B7012601
theorem B3692051 : Blo 1640019 3692051 := bstep (se 1 (by rfl) ⟨2769038, by rfl⟩ : syracuseStep 3692051 = 5538077) B5538077
theorem B8304281 : Blo 1640019 8304281 := bstep (se 2 (by rfl) ⟨3114105, by rfl⟩ : syracuseStep 8304281 = 6228211) B6228211
theorem B5912615 : Blo 1640019 5912615 := bstep (se 1 (by rfl) ⟨4434461, by rfl⟩ : syracuseStep 5912615 = 8868923) B8868923
theorem B9345233 : Blo 1640019 9345233 := bstep (se 2 (by rfl) ⟨3504462, by rfl⟩ : syracuseStep 9345233 = 7008925) B7008925
theorem B3692879 : Blo 1640019 3692879 := bstep (se 1 (by rfl) ⟨2769659, by rfl⟩ : syracuseStep 3692879 = 5539319) B5539319
theorem B3693563 : Blo 1640019 3693563 := bstep (se 1 (by rfl) ⟨2770172, by rfl⟩ : syracuseStep 3693563 = 5540345) B5540345
theorem B3693599 : Blo 1640019 3693599 := bstep (se 1 (by rfl) ⟨2770199, by rfl⟩ : syracuseStep 3693599 = 5540399) B5540399
theorem B3505207 : Blo 1640019 3505207 := bstep (se 1 (by rfl) ⟨2628905, by rfl⟩ : syracuseStep 3505207 = 5257811) B5257811
theorem B2767999 : Blo 1640019 2767999 := bstep (se 1 (by rfl) ⟨2075999, by rfl⟩ : syracuseStep 2767999 = 4151999) B4151999
theorem B53247131 : Blo 1640019 53247131 := bstep (se 1 (by rfl) ⟨39935348, by rfl⟩ : syracuseStep 53247131 = 79870697) B79870697
theorem B4152647 : Blo 1640019 4152647 := bstep (se 1 (by rfl) ⟨3114485, by rfl⟩ : syracuseStep 4152647 = 6228971) B6228971
theorem B28024217 : Blo 1640019 28024217 := bstep (se 2 (by rfl) ⟨10509081, by rfl⟩ : syracuseStep 28024217 = 21018163) B21018163
theorem B39927275 : Blo 1640019 39927275 := bstep (se 1 (by rfl) ⟨29945456, by rfl⟩ : syracuseStep 39927275 = 59890913) B59890913
theorem B9977755 : Blo 1640019 9977755 := bstep (se 1 (by rfl) ⟨7483316, by rfl⟩ : syracuseStep 9977755 = 14966633) B14966633
theorem B6234347 : Blo 1640019 6234347 := bstep (se 1 (by rfl) ⟨4675760, by rfl⟩ : syracuseStep 6234347 = 9351521) B9351521
theorem B4153619 : Blo 1640019 4153619 := bstep (se 1 (by rfl) ⟨3115214, by rfl⟩ : syracuseStep 4153619 = 6230429) B6230429
theorem B4153639 : Blo 1640019 4153639 := bstep (se 1 (by rfl) ⟨3115229, by rfl⟩ : syracuseStep 4153639 = 6230459) B6230459
theorem B2769275 : Blo 1640019 2769275 := bstep (se 1 (by rfl) ⟨2076956, by rfl⟩ : syracuseStep 2769275 = 4153913) B4153913
theorem B5538239 : Blo 1640019 5538239 := bstep (se 1 (by rfl) ⟨4153679, by rfl⟩ : syracuseStep 5538239 = 8307359) B8307359
theorem B12468815 : Blo 1640019 12468815 := bstep (se 1 (by rfl) ⟨9351611, by rfl⟩ : syracuseStep 12468815 = 18703223) B18703223
theorem B15778385 : Blo 1640019 15778385 := bstep (se 2 (by rfl) ⟨5916894, by rfl⟩ : syracuseStep 15778385 = 11833789) B11833789
theorem B3113711 : Blo 1640019 3113711 := bstep (se 1 (by rfl) ⟨2335283, by rfl⟩ : syracuseStep 3113711 = 4670567) B4670567
theorem B15983527 : Blo 1640019 15983527 := bstep (se 1 (by rfl) ⟨11987645, by rfl⟩ : syracuseStep 15983527 = 23975291) B23975291
theorem B11232199 : Blo 1640019 11232199 := bstep (se 1 (by rfl) ⟨8424149, by rfl⟩ : syracuseStep 11232199 = 16848299) B16848299
theorem B11224097 : Blo 1640019 11224097 := bstep (se 2 (by rfl) ⟨4209036, by rfl⟩ : syracuseStep 11224097 = 8418073) B8418073
theorem B5538887 : Blo 1640019 5538887 := bstep (se 1 (by rfl) ⟨4154165, by rfl⟩ : syracuseStep 5538887 = 8308331) B8308331
theorem B1640063 : Blo 1640019 1640063 := bstep (se 1 (by rfl) ⟨1230047, by rfl⟩ : syracuseStep 1640063 = 2460095) B2460095
theorem B1640263 : Blo 1640019 1640263 := bstep (se 1 (by rfl) ⟨1230197, by rfl⟩ : syracuseStep 1640263 = 2460395) B2460395
theorem B5916665 : Blo 1640019 5916665 := bstep (se 2 (by rfl) ⟨2218749, by rfl⟩ : syracuseStep 5916665 = 4437499) B4437499
theorem B5539913 : Blo 1640019 5539913 := bstep (se 2 (by rfl) ⟨2077467, by rfl⟩ : syracuseStep 5539913 = 4154935) B4154935
theorem B35498087 : Blo 1640019 35498087 := bstep (se 1 (by rfl) ⟨26623565, by rfl⟩ : syracuseStep 35498087 = 53247131) B53247131
theorem B5539967 : Blo 1640019 5539967 := bstep (se 1 (by rfl) ⟨4154975, by rfl⟩ : syracuseStep 5539967 = 8309951) B8309951
theorem B1640615 : Blo 1640019 1640615 := bstep (se 1 (by rfl) ⟨1230461, by rfl⟩ : syracuseStep 1640615 = 2460923) B2460923
theorem B11831483 : Blo 1640019 11831483 := bstep (se 1 (by rfl) ⟨8873612, by rfl⟩ : syracuseStep 11831483 = 17747225) B17747225
theorem B26618183 : Blo 1640019 26618183 := bstep (se 1 (by rfl) ⟨19963637, by rfl⟩ : syracuseStep 26618183 = 39927275) B39927275
theorem B1640927 : Blo 1640019 1640927 := bstep (se 1 (by rfl) ⟨1230695, by rfl⟩ : syracuseStep 1640927 = 2461391) B2461391
theorem B2460137 : Blo 1640019 2460137 := bstep (se 2 (by rfl) ⟨922551, by rfl⟩ : syracuseStep 2460137 = 1845103) B1845103
theorem B8309303 : Blo 1640019 8309303 := bstep (se 1 (by rfl) ⟨6231977, by rfl⟩ : syracuseStep 8309303 = 12463955) B12463955
theorem B1846255 : Blo 1640019 1846255 := bstep (se 1 (by rfl) ⟨1384691, by rfl⟩ : syracuseStep 1846255 = 2769383) B2769383
theorem B2460767 : Blo 1640019 2460767 := bstep (se 1 (by rfl) ⟨1845575, by rfl⟩ : syracuseStep 2460767 = 3691151) B3691151
theorem B5540993 : Blo 1640019 5540993 := bstep (se 2 (by rfl) ⟨2077872, by rfl⟩ : syracuseStep 5540993 = 4155745) B4155745
theorem B1641627 : Blo 1640019 1641627 := bstep (se 1 (by rfl) ⟨1231220, by rfl⟩ : syracuseStep 1641627 = 2462441) B2462441
theorem B1641791 : Blo 1640019 1641791 := bstep (se 1 (by rfl) ⟨1231343, by rfl⟩ : syracuseStep 1641791 = 2462687) B2462687
theorem B7007627 : Blo 1640019 7007627 := bstep (se 1 (by rfl) ⟨5255720, by rfl⟩ : syracuseStep 7007627 = 10511441) B10511441
theorem B3116711 : Blo 1640019 3116711 := bstep (se 1 (by rfl) ⟨2337533, by rfl⟩ : syracuseStep 3116711 = 4675067) B4675067
theorem B2461367 : Blo 1640019 2461367 := bstep (se 1 (by rfl) ⟨1846025, by rfl⟩ : syracuseStep 2461367 = 3692051) B3692051
theorem B4673609 : Blo 1640019 4673609 := bstep (se 2 (by rfl) ⟨1752603, by rfl⟩ : syracuseStep 4673609 = 3505207) B3505207
theorem B3551369 : Blo 1640019 3551369 := bstep (se 2 (by rfl) ⟨1331763, by rfl⟩ : syracuseStep 3551369 = 2663527) B2663527
theorem B6230155 : Blo 1640019 6230155 := bstep (se 1 (by rfl) ⟨4672616, by rfl⟩ : syracuseStep 6230155 = 9345233) B9345233
theorem B3600551 : Blo 1640019 3600551 := bstep (se 1 (by rfl) ⟨2700413, by rfl⟩ : syracuseStep 3600551 = 5400827) B5400827
theorem B3690665 : Blo 1640019 3690665 := bstep (se 2 (by rfl) ⟨1383999, by rfl⟩ : syracuseStep 3690665 = 2767999) B2767999
theorem B2461919 : Blo 1640019 2461919 := bstep (se 1 (by rfl) ⟨1846439, by rfl⟩ : syracuseStep 2461919 = 3692879) B3692879
theorem B2462375 : Blo 1640019 2462375 := bstep (se 1 (by rfl) ⟨1846781, by rfl⟩ : syracuseStep 2462375 = 3693563) B3693563
theorem B2462399 : Blo 1640019 2462399 := bstep (se 1 (by rfl) ⟨1846799, by rfl⟩ : syracuseStep 2462399 = 3693599) B3693599
theorem B18682811 : Blo 1640019 18682811 := bstep (se 1 (by rfl) ⟨14012108, by rfl⟩ : syracuseStep 18682811 = 28024217) B28024217
theorem B10114085 : Blo 1640019 10114085 := bstep (se 4 (by rfl) ⟨948195, by rfl⟩ : syracuseStep 10114085 = 1896391) B1896391
theorem B19952891 : Blo 1640019 19952891 := bstep (se 1 (by rfl) ⟨14964668, by rfl⟩ : syracuseStep 19952891 = 29929337) B29929337
theorem B15766973 : Blo 1640019 15766973 := bstep (se 3 (by rfl) ⟨2956307, by rfl⟩ : syracuseStep 15766973 = 5912615) B5912615
theorem B5256683 : Blo 1640019 5256683 := bstep (se 1 (by rfl) ⟨3942512, by rfl⟩ : syracuseStep 5256683 = 7885025) B7885025
theorem B21018527 : Blo 1640019 21018527 := bstep (se 1 (by rfl) ⟨15763895, by rfl⟩ : syracuseStep 21018527 = 31527791) B31527791
theorem B5536079 : Blo 1640019 5536079 := bstep (se 1 (by rfl) ⟨4152059, by rfl⟩ : syracuseStep 5536079 = 8304119) B8304119
theorem B3692969 : Blo 1640019 3692969 := bstep (se 2 (by rfl) ⟨1384863, by rfl⟩ : syracuseStep 3692969 = 2769727) B2769727
theorem B5536187 : Blo 1640019 5536187 := bstep (se 1 (by rfl) ⟨4152140, by rfl⟩ : syracuseStep 5536187 = 8304281) B8304281
theorem B4151969 : Blo 1640019 4151969 := bstep (se 2 (by rfl) ⟨1556988, by rfl⟩ : syracuseStep 4151969 = 3113977) B3113977
theorem B5610655 : Blo 1640019 5610655 := bstep (se 1 (by rfl) ⟨4207991, by rfl⟩ : syracuseStep 5610655 = 8415983) B8415983
theorem B2768431 : Blo 1640019 2768431 := bstep (se 1 (by rfl) ⟨2076323, by rfl⟩ : syracuseStep 2768431 = 4152647) B4152647
theorem B6233831 : Blo 1640019 6233831 := bstep (se 1 (by rfl) ⟨4675373, by rfl⟩ : syracuseStep 6233831 = 9350747) B9350747
theorem B3694319 : Blo 1640019 3694319 := bstep (se 1 (by rfl) ⟨2770739, by rfl⟩ : syracuseStep 3694319 = 5541479) B5541479
theorem B13303673 : Blo 1640019 13303673 := bstep (se 2 (by rfl) ⟨4988877, by rfl⟩ : syracuseStep 13303673 = 9977755) B9977755
theorem B3694535 : Blo 1640019 3694535 := bstep (se 1 (by rfl) ⟨2770901, by rfl⟩ : syracuseStep 3694535 = 5541803) B5541803
theorem B2400367 : Blo 1640019 2400367 := bstep (se 1 (by rfl) ⟨1800275, by rfl⟩ : syracuseStep 2400367 = 3600551) B3600551
theorem B2769079 : Blo 1640019 2769079 := bstep (se 1 (by rfl) ⟨2076809, by rfl⟩ : syracuseStep 2769079 = 4153619) B4153619
theorem B8306873 : Blo 1640019 8306873 := bstep (se 2 (by rfl) ⟨3115077, by rfl⟩ : syracuseStep 8306873 = 6230155) B6230155
theorem B5538185 : Blo 1640019 5538185 := bstep (se 2 (by rfl) ⟨2076819, by rfl⟩ : syracuseStep 5538185 = 4153639) B4153639
theorem B10518923 : Blo 1640019 10518923 := bstep (se 1 (by rfl) ⟨7889192, by rfl⟩ : syracuseStep 10518923 = 15778385) B15778385
theorem B6742723 : Blo 1640019 6742723 := bstep (se 1 (by rfl) ⟨5057042, by rfl⟩ : syracuseStep 6742723 = 10114085) B10114085
theorem B10511315 : Blo 1640019 10511315 := bstep (se 1 (by rfl) ⟨7883486, by rfl⟩ : syracuseStep 10511315 = 15766973) B15766973
theorem B14976265 : Blo 1640019 14976265 := bstep (se 2 (by rfl) ⟨5616099, by rfl⟩ : syracuseStep 14976265 = 11232199) B11232199
theorem B37881269 : Blo 1640019 37881269 := bstep (se 5 (by rfl) ⟨1775684, by rfl⟩ : syracuseStep 37881269 = 3551369) B3551369
theorem B7480873 : Blo 1640019 7480873 := bstep (se 2 (by rfl) ⟨2805327, by rfl⟩ : syracuseStep 7480873 = 5610655) B5610655
theorem B17745455 : Blo 1640019 17745455 := bstep (se 1 (by rfl) ⟨13309091, by rfl⟩ : syracuseStep 17745455 = 26618183) B26618183
theorem B1640091 : Blo 1640019 1640091 := bstep (se 1 (by rfl) ⟨1230068, by rfl⟩ : syracuseStep 1640091 = 2460137) B2460137
theorem B5539535 : Blo 1640019 5539535 := bstep (se 1 (by rfl) ⟨4154651, by rfl⟩ : syracuseStep 5539535 = 8309303) B8309303
theorem B1640511 : Blo 1640019 1640511 := bstep (se 1 (by rfl) ⟨1230383, by rfl⟩ : syracuseStep 1640511 = 2460767) B2460767
theorem B4671751 : Blo 1640019 4671751 := bstep (se 1 (by rfl) ⟨3503813, by rfl⟩ : syracuseStep 4671751 = 7007627) B7007627
theorem B1640911 : Blo 1640019 1640911 := bstep (se 1 (by rfl) ⟨1230683, by rfl⟩ : syracuseStep 1640911 = 2461367) B2461367
theorem B4155887 : Blo 1640019 4155887 := bstep (se 1 (by rfl) ⟨3116915, by rfl⟩ : syracuseStep 4155887 = 6233831) B6233831
theorem B3115739 : Blo 1640019 3115739 := bstep (se 1 (by rfl) ⟨2336804, by rfl⟩ : syracuseStep 3115739 = 4673609) B4673609
theorem B2460443 : Blo 1640019 2460443 := bstep (se 1 (by rfl) ⟨1845332, by rfl⟩ : syracuseStep 2460443 = 3690665) B3690665
theorem B1641279 : Blo 1640019 1641279 := bstep (se 1 (by rfl) ⟨1230959, by rfl⟩ : syracuseStep 1641279 = 2461919) B2461919
theorem B4156231 : Blo 1640019 4156231 := bstep (se 1 (by rfl) ⟨3117173, by rfl⟩ : syracuseStep 4156231 = 6234347) B6234347
theorem B1846183 : Blo 1640019 1846183 := bstep (se 1 (by rfl) ⟨1384637, by rfl⟩ : syracuseStep 1846183 = 2769275) B2769275
theorem B1641583 : Blo 1640019 1641583 := bstep (se 1 (by rfl) ⟨1231187, by rfl⟩ : syracuseStep 1641583 = 2462375) B2462375
theorem B1641599 : Blo 1640019 1641599 := bstep (se 1 (by rfl) ⟨1231199, by rfl⟩ : syracuseStep 1641599 = 2462399) B2462399
theorem B2075807 : Blo 1640019 2075807 := bstep (se 1 (by rfl) ⟨1556855, by rfl⟩ : syracuseStep 2075807 = 3113711) B3113711
theorem B12455207 : Blo 1640019 12455207 := bstep (se 1 (by rfl) ⟨9341405, by rfl⟩ : syracuseStep 12455207 = 18682811) B18682811
theorem B7482731 : Blo 1640019 7482731 := bstep (se 1 (by rfl) ⟨5612048, by rfl⟩ : syracuseStep 7482731 = 11224097) B11224097
theorem B21311369 : Blo 1640019 21311369 := bstep (se 2 (by rfl) ⟨7991763, by rfl⟩ : syracuseStep 21311369 = 15983527) B15983527
theorem B14012351 : Blo 1640019 14012351 := bstep (se 1 (by rfl) ⟨10509263, by rfl⟩ : syracuseStep 14012351 = 21018527) B21018527
theorem B2461673 : Blo 1640019 2461673 := bstep (se 2 (by rfl) ⟨923127, by rfl⟩ : syracuseStep 2461673 = 1846255) B1846255
theorem B3944443 : Blo 1640019 3944443 := bstep (se 1 (by rfl) ⟨2958332, by rfl⟩ : syracuseStep 3944443 = 5916665) B5916665
theorem B3690719 : Blo 1640019 3690719 := bstep (se 1 (by rfl) ⟨2768039, by rfl⟩ : syracuseStep 3690719 = 5536079) B5536079
theorem B2461979 : Blo 1640019 2461979 := bstep (se 1 (by rfl) ⟨1846484, by rfl⟩ : syracuseStep 2461979 = 3692969) B3692969
theorem B3690791 : Blo 1640019 3690791 := bstep (se 1 (by rfl) ⟨2768093, by rfl⟩ : syracuseStep 3690791 = 5536187) B5536187
theorem B3691241 : Blo 1640019 3691241 := bstep (se 2 (by rfl) ⟨1384215, by rfl⟩ : syracuseStep 3691241 = 2768431) B2768431
theorem B2077807 : Blo 1640019 2077807 := bstep (se 1 (by rfl) ⟨1558355, by rfl⟩ : syracuseStep 2077807 = 3116711) B3116711
theorem B2462879 : Blo 1640019 2462879 := bstep (se 1 (by rfl) ⟨1847159, by rfl⟩ : syracuseStep 2462879 = 3694319) B3694319
theorem B8869115 : Blo 1640019 8869115 := bstep (se 1 (by rfl) ⟨6651836, by rfl⟩ : syracuseStep 8869115 = 13303673) B13303673
theorem B2463023 : Blo 1640019 2463023 := bstep (se 1 (by rfl) ⟨1847267, by rfl⟩ : syracuseStep 2463023 = 3694535) B3694535
theorem B3692159 : Blo 1640019 3692159 := bstep (se 1 (by rfl) ⟨2769119, by rfl⟩ : syracuseStep 3692159 = 5538239) B5538239
theorem B8312543 : Blo 1640019 8312543 := bstep (se 1 (by rfl) ⟨6234407, by rfl⟩ : syracuseStep 8312543 = 12468815) B12468815
theorem B3692591 : Blo 1640019 3692591 := bstep (se 1 (by rfl) ⟨2769443, by rfl⟩ : syracuseStep 3692591 = 5538887) B5538887
theorem B13301927 : Blo 1640019 13301927 := bstep (se 1 (by rfl) ⟨9976445, by rfl⟩ : syracuseStep 13301927 = 19952891) B19952891
theorem B3504455 : Blo 1640019 3504455 := bstep (se 1 (by rfl) ⟨2628341, by rfl⟩ : syracuseStep 3504455 = 5256683) B5256683
theorem B3693275 : Blo 1640019 3693275 := bstep (se 1 (by rfl) ⟨2769956, by rfl⟩ : syracuseStep 3693275 = 5539913) B5539913
theorem B23665391 : Blo 1640019 23665391 := bstep (se 1 (by rfl) ⟨17749043, by rfl⟩ : syracuseStep 23665391 = 35498087) B35498087
theorem B3693311 : Blo 1640019 3693311 := bstep (se 1 (by rfl) ⟨2769983, by rfl⟩ : syracuseStep 3693311 = 5539967) B5539967
theorem B7887655 : Blo 1640019 7887655 := bstep (se 1 (by rfl) ⟨5915741, by rfl⟩ : syracuseStep 7887655 = 11831483) B11831483
theorem B2767979 : Blo 1640019 2767979 := bstep (se 1 (by rfl) ⟨2075984, by rfl⟩ : syracuseStep 2767979 = 4151969) B4151969
theorem B3693995 : Blo 1640019 3693995 := bstep (se 1 (by rfl) ⟨2770496, by rfl⟩ : syracuseStep 3693995 = 5540993) B5540993
theorem B5537915 : Blo 1640019 5537915 := bstep (se 1 (by rfl) ⟨4153436, by rfl⟩ : syracuseStep 5537915 = 8306873) B8306873
theorem B28050461 : Blo 1640019 28050461 := bstep (se 3 (by rfl) ⟨5259461, by rfl⟩ : syracuseStep 28050461 = 10518923) B10518923
theorem B11830303 : Blo 1640019 11830303 := bstep (se 1 (by rfl) ⟨8872727, by rfl⟩ : syracuseStep 11830303 = 17745455) B17745455
theorem B2770409 : Blo 1640019 2770409 := bstep (se 2 (by rfl) ⟨1038903, by rfl⟩ : syracuseStep 2770409 = 2077807) B2077807
theorem B2336303 : Blo 1640019 2336303 := bstep (se 1 (by rfl) ⟨1752227, by rfl⟩ : syracuseStep 2336303 = 3504455) B3504455
theorem B2770591 : Blo 1640019 2770591 := bstep (se 1 (by rfl) ⟨2077943, by rfl⟩ : syracuseStep 2770591 = 4155887) B4155887
theorem B1640295 : Blo 1640019 1640295 := bstep (se 1 (by rfl) ⟨1230221, by rfl⟩ : syracuseStep 1640295 = 2460443) B2460443
theorem B1845319 : Blo 1640019 1845319 := bstep (se 1 (by rfl) ⟨1383989, by rfl⟩ : syracuseStep 1845319 = 2767979) B2767979
theorem B14207579 : Blo 1640019 14207579 := bstep (se 1 (by rfl) ⟨10655684, by rfl⟩ : syracuseStep 14207579 = 21311369) B21311369
theorem B9341567 : Blo 1640019 9341567 := bstep (se 1 (by rfl) ⟨7006175, by rfl⟩ : syracuseStep 9341567 = 14012351) B14012351
theorem B1641115 : Blo 1640019 1641115 := bstep (se 1 (by rfl) ⟨1230836, by rfl⟩ : syracuseStep 1641115 = 2461673) B2461673
theorem B2460479 : Blo 1640019 2460479 := bstep (se 1 (by rfl) ⟨1845359, by rfl⟩ : syracuseStep 2460479 = 3690719) B3690719
theorem B1641319 : Blo 1640019 1641319 := bstep (se 1 (by rfl) ⟨1230989, by rfl⟩ : syracuseStep 1641319 = 2461979) B2461979
theorem B2460527 : Blo 1640019 2460527 := bstep (se 1 (by rfl) ⟨1845395, by rfl⟩ : syracuseStep 2460527 = 3690791) B3690791
theorem B6229001 : Blo 1640019 6229001 := bstep (se 2 (by rfl) ⟨2335875, by rfl⟩ : syracuseStep 6229001 = 4671751) B4671751
theorem B2460827 : Blo 1640019 2460827 := bstep (se 1 (by rfl) ⟨1845620, by rfl⟩ : syracuseStep 2460827 = 3691241) B3691241
theorem B7007543 : Blo 1640019 7007543 := bstep (se 1 (by rfl) ⟨5255657, by rfl⟩ : syracuseStep 7007543 = 10511315) B10511315
theorem B1641919 : Blo 1640019 1641919 := bstep (se 1 (by rfl) ⟨1231439, by rfl⟩ : syracuseStep 1641919 = 2462879) B2462879
theorem B1642015 : Blo 1640019 1642015 := bstep (se 1 (by rfl) ⟨1231511, by rfl⟩ : syracuseStep 1642015 = 2463023) B2463023
theorem B8990297 : Blo 1640019 8990297 := bstep (se 2 (by rfl) ⟨3371361, by rfl⟩ : syracuseStep 8990297 = 6742723) B6742723
theorem B2461439 : Blo 1640019 2461439 := bstep (se 1 (by rfl) ⟨1846079, by rfl⟩ : syracuseStep 2461439 = 3692159) B3692159
theorem B5541641 : Blo 1640019 5541641 := bstep (se 2 (by rfl) ⟨2078115, by rfl⟩ : syracuseStep 5541641 = 4156231) B4156231
theorem B5541695 : Blo 1640019 5541695 := bstep (se 1 (by rfl) ⟨4156271, by rfl⟩ : syracuseStep 5541695 = 8312543) B8312543
theorem B2461577 : Blo 1640019 2461577 := bstep (se 2 (by rfl) ⟨923091, by rfl⟩ : syracuseStep 2461577 = 1846183) B1846183
theorem B2461727 : Blo 1640019 2461727 := bstep (se 1 (by rfl) ⟨1846295, by rfl⟩ : syracuseStep 2461727 = 3692591) B3692591
theorem B8867951 : Blo 1640019 8867951 := bstep (se 1 (by rfl) ⟨6650963, by rfl⟩ : syracuseStep 8867951 = 13301927) B13301927
theorem B19968353 : Blo 1640019 19968353 := bstep (se 2 (by rfl) ⟨7488132, by rfl⟩ : syracuseStep 19968353 = 14976265) B14976265
theorem B2077159 : Blo 1640019 2077159 := bstep (se 1 (by rfl) ⟨1557869, by rfl⟩ : syracuseStep 2077159 = 3115739) B3115739
theorem B2462183 : Blo 1640019 2462183 := bstep (se 1 (by rfl) ⟨1846637, by rfl⟩ : syracuseStep 2462183 = 3693275) B3693275
theorem B2462207 : Blo 1640019 2462207 := bstep (se 1 (by rfl) ⟨1846655, by rfl⟩ : syracuseStep 2462207 = 3693311) B3693311
theorem B9974497 : Blo 1640019 9974497 := bstep (se 2 (by rfl) ⟨3740436, by rfl⟩ : syracuseStep 9974497 = 7480873) B7480873
theorem B8303471 : Blo 1640019 8303471 := bstep (se 1 (by rfl) ⟨6227603, by rfl⟩ : syracuseStep 8303471 = 12455207) B12455207
theorem B2462663 : Blo 1640019 2462663 := bstep (se 1 (by rfl) ⟨1846997, by rfl⟩ : syracuseStep 2462663 = 3693995) B3693995
theorem B3200489 : Blo 1640019 3200489 := bstep (se 2 (by rfl) ⟨1200183, by rfl⟩ : syracuseStep 3200489 = 2400367) B2400367
theorem B3692105 : Blo 1640019 3692105 := bstep (se 2 (by rfl) ⟨1384539, by rfl⟩ : syracuseStep 3692105 = 2769079) B2769079
theorem B3692123 : Blo 1640019 3692123 := bstep (se 1 (by rfl) ⟨2769092, by rfl⟩ : syracuseStep 3692123 = 5538185) B5538185
theorem B5535485 : Blo 1640019 5535485 := bstep (se 3 (by rfl) ⟨1037903, by rfl⟩ : syracuseStep 5535485 = 2075807) B2075807
theorem B5912743 : Blo 1640019 5912743 := bstep (se 1 (by rfl) ⟨4434557, by rfl⟩ : syracuseStep 5912743 = 8869115) B8869115
theorem B19953949 : Blo 1640019 19953949 := bstep (se 3 (by rfl) ⟨3741365, by rfl⟩ : syracuseStep 19953949 = 7482731) B7482731
theorem B25254179 : Blo 1640019 25254179 := bstep (se 1 (by rfl) ⟨18940634, by rfl⟩ : syracuseStep 25254179 = 37881269) B37881269
theorem B10516873 : Blo 1640019 10516873 := bstep (se 2 (by rfl) ⟨3943827, by rfl⟩ : syracuseStep 10516873 = 7887655) B7887655
theorem B3693023 : Blo 1640019 3693023 := bstep (se 1 (by rfl) ⟨2769767, by rfl⟩ : syracuseStep 3693023 = 5539535) B5539535
theorem B15776927 : Blo 1640019 15776927 := bstep (se 1 (by rfl) ⟨11832695, by rfl⟩ : syracuseStep 15776927 = 23665391) B23665391
theorem B5259257 : Blo 1640019 5259257 := bstep (se 2 (by rfl) ⟨1972221, by rfl⟩ : syracuseStep 5259257 = 3944443) B3944443
theorem B13312235 : Blo 1640019 13312235 := bstep (se 1 (by rfl) ⟨9984176, by rfl⟩ : syracuseStep 13312235 = 19968353) B19968353
theorem B2769545 : Blo 1640019 2769545 := bstep (se 2 (by rfl) ⟨1038579, by rfl⟩ : syracuseStep 2769545 = 2077159) B2077159
theorem B16836119 : Blo 1640019 16836119 := bstep (se 1 (by rfl) ⟨12627089, by rfl⟩ : syracuseStep 16836119 = 25254179) B25254179
theorem B9471719 : Blo 1640019 9471719 := bstep (se 1 (by rfl) ⟨7103789, by rfl⟩ : syracuseStep 9471719 = 14207579) B14207579
theorem B6227711 : Blo 1640019 6227711 := bstep (se 1 (by rfl) ⟨4670783, by rfl⟩ : syracuseStep 6227711 = 9341567) B9341567
theorem B1640319 : Blo 1640019 1640319 := bstep (se 1 (by rfl) ⟨1230239, by rfl⟩ : syracuseStep 1640319 = 2460479) B2460479
theorem B1640351 : Blo 1640019 1640351 := bstep (se 1 (by rfl) ⟨1230263, by rfl⟩ : syracuseStep 1640351 = 2460527) B2460527
theorem B1640551 : Blo 1640019 1640551 := bstep (se 1 (by rfl) ⟨1230413, by rfl⟩ : syracuseStep 1640551 = 2460827) B2460827
theorem B4671695 : Blo 1640019 4671695 := bstep (se 1 (by rfl) ⟨3503771, by rfl⟩ : syracuseStep 4671695 = 7007543) B7007543
theorem B1640959 : Blo 1640019 1640959 := bstep (se 1 (by rfl) ⟨1230719, by rfl⟩ : syracuseStep 1640959 = 2461439) B2461439
theorem B1641051 : Blo 1640019 1641051 := bstep (se 1 (by rfl) ⟨1230788, by rfl⟩ : syracuseStep 1641051 = 2461577) B2461577
theorem B1641151 : Blo 1640019 1641151 := bstep (se 1 (by rfl) ⟨1230863, by rfl⟩ : syracuseStep 1641151 = 2461727) B2461727
theorem B2460425 : Blo 1640019 2460425 := bstep (se 2 (by rfl) ⟨922659, by rfl⟩ : syracuseStep 2460425 = 1845319) B1845319
theorem B7883657 : Blo 1640019 7883657 := bstep (se 2 (by rfl) ⟨2956371, by rfl⟩ : syracuseStep 7883657 = 5912743) B5912743
theorem B1641455 : Blo 1640019 1641455 := bstep (se 1 (by rfl) ⟨1231091, by rfl⟩ : syracuseStep 1641455 = 2462183) B2462183
theorem B1641471 : Blo 1640019 1641471 := bstep (se 1 (by rfl) ⟨1231103, by rfl⟩ : syracuseStep 1641471 = 2462207) B2462207
theorem B1641775 : Blo 1640019 1641775 := bstep (se 1 (by rfl) ⟨1231331, by rfl⟩ : syracuseStep 1641775 = 2462663) B2462663
theorem B13299329 : Blo 1640019 13299329 := bstep (se 2 (by rfl) ⟨4987248, by rfl⟩ : syracuseStep 13299329 = 9974497) B9974497
theorem B2133659 : Blo 1640019 2133659 := bstep (se 1 (by rfl) ⟨1600244, by rfl⟩ : syracuseStep 2133659 = 3200489) B3200489
theorem B1846939 : Blo 1640019 1846939 := bstep (se 1 (by rfl) ⟨1385204, by rfl⟩ : syracuseStep 1846939 = 2770409) B2770409
theorem B2461403 : Blo 1640019 2461403 := bstep (se 1 (by rfl) ⟨1846052, by rfl⟩ : syracuseStep 2461403 = 3692105) B3692105
theorem B2461415 : Blo 1640019 2461415 := bstep (se 1 (by rfl) ⟨1846061, by rfl⟩ : syracuseStep 2461415 = 3692123) B3692123
theorem B3690323 : Blo 1640019 3690323 := bstep (se 1 (by rfl) ⟨2767742, by rfl⟩ : syracuseStep 3690323 = 5535485) B5535485
theorem B15773737 : Blo 1640019 15773737 := bstep (se 2 (by rfl) ⟨5915151, by rfl⟩ : syracuseStep 15773737 = 11830303) B11830303
theorem B6230141 : Blo 1640019 6230141 := bstep (se 3 (by rfl) ⟨1168151, by rfl⟩ : syracuseStep 6230141 = 2336303) B2336303
theorem B2462015 : Blo 1640019 2462015 := bstep (se 1 (by rfl) ⟨1846511, by rfl⟩ : syracuseStep 2462015 = 3693023) B3693023
theorem B5993531 : Blo 1640019 5993531 := bstep (se 1 (by rfl) ⟨4495148, by rfl⟩ : syracuseStep 5993531 = 8990297) B8990297
theorem B5911967 : Blo 1640019 5911967 := bstep (se 1 (by rfl) ⟨4433975, by rfl⟩ : syracuseStep 5911967 = 8867951) B8867951
theorem B3691943 : Blo 1640019 3691943 := bstep (se 1 (by rfl) ⟨2768957, by rfl⟩ : syracuseStep 3691943 = 5537915) B5537915
theorem B26605265 : Blo 1640019 26605265 := bstep (se 2 (by rfl) ⟨9976974, by rfl⟩ : syracuseStep 26605265 = 19953949) B19953949
theorem B14022497 : Blo 1640019 14022497 := bstep (se 2 (by rfl) ⟨5258436, by rfl⟩ : syracuseStep 14022497 = 10516873) B10516873
theorem B5535647 : Blo 1640019 5535647 := bstep (se 1 (by rfl) ⟨4151735, by rfl⟩ : syracuseStep 5535647 = 8303471) B8303471
theorem B18700307 : Blo 1640019 18700307 := bstep (se 1 (by rfl) ⟨14025230, by rfl⟩ : syracuseStep 18700307 = 28050461) B28050461
theorem B4152667 : Blo 1640019 4152667 := bstep (se 1 (by rfl) ⟨3114500, by rfl⟩ : syracuseStep 4152667 = 6229001) B6229001
theorem B10517951 : Blo 1640019 10517951 := bstep (se 1 (by rfl) ⟨7888463, by rfl⟩ : syracuseStep 10517951 = 15776927) B15776927
theorem B3694121 : Blo 1640019 3694121 := bstep (se 2 (by rfl) ⟨1385295, by rfl⟩ : syracuseStep 3694121 = 2770591) B2770591
theorem B3694427 : Blo 1640019 3694427 := bstep (se 1 (by rfl) ⟨2770820, by rfl⟩ : syracuseStep 3694427 = 5541641) B5541641
theorem B3694463 : Blo 1640019 3694463 := bstep (se 1 (by rfl) ⟨2770847, by rfl⟩ : syracuseStep 3694463 = 5541695) B5541695
theorem B3506171 : Blo 1640019 3506171 := bstep (se 1 (by rfl) ⟨2629628, by rfl⟩ : syracuseStep 3506171 = 5259257) B5259257
theorem B4153427 : Blo 1640019 4153427 := bstep (se 1 (by rfl) ⟨3115070, by rfl⟩ : syracuseStep 4153427 = 6230141) B6230141
theorem B3941311 : Blo 1640019 3941311 := bstep (se 1 (by rfl) ⟨2955983, by rfl⟩ : syracuseStep 3941311 = 5911967) B5911967
theorem B11224079 : Blo 1640019 11224079 := bstep (se 1 (by rfl) ⟨8418059, by rfl⟩ : syracuseStep 11224079 = 16836119) B16836119
theorem B9348331 : Blo 1640019 9348331 := bstep (se 1 (by rfl) ⟨7011248, by rfl⟩ : syracuseStep 9348331 = 14022497) B14022497
theorem B3114463 : Blo 1640019 3114463 := bstep (se 1 (by rfl) ⟨2335847, by rfl⟩ : syracuseStep 3114463 = 4671695) B4671695
theorem B1640283 : Blo 1640019 1640283 := bstep (se 1 (by rfl) ⟨1230212, by rfl⟩ : syracuseStep 1640283 = 2460425) B2460425
theorem B8866219 : Blo 1640019 8866219 := bstep (se 1 (by rfl) ⟨6649664, by rfl⟩ : syracuseStep 8866219 = 13299329) B13299329
theorem B1640935 : Blo 1640019 1640935 := bstep (se 1 (by rfl) ⟨1230701, by rfl⟩ : syracuseStep 1640935 = 2461403) B2461403
theorem B1640943 : Blo 1640019 1640943 := bstep (se 1 (by rfl) ⟨1230707, by rfl⟩ : syracuseStep 1640943 = 2461415) B2461415
theorem B2460215 : Blo 1640019 2460215 := bstep (se 1 (by rfl) ⟨1845161, by rfl⟩ : syracuseStep 2460215 = 3690323) B3690323
theorem B9349789 : Blo 1640019 9349789 := bstep (se 3 (by rfl) ⟨1753085, by rfl⟩ : syracuseStep 9349789 = 3506171) B3506171
theorem B21031649 : Blo 1640019 21031649 := bstep (se 2 (by rfl) ⟨7886868, by rfl⟩ : syracuseStep 21031649 = 15773737) B15773737
theorem B1641343 : Blo 1640019 1641343 := bstep (se 1 (by rfl) ⟨1231007, by rfl⟩ : syracuseStep 1641343 = 2462015) B2462015
theorem B1846363 : Blo 1640019 1846363 := bstep (se 1 (by rfl) ⟨1384772, by rfl⟩ : syracuseStep 1846363 = 2769545) B2769545
theorem B35499293 : Blo 1640019 35499293 := bstep (se 3 (by rfl) ⟨6656117, by rfl⟩ : syracuseStep 35499293 = 13312235) B13312235
theorem B2461295 : Blo 1640019 2461295 := bstep (se 1 (by rfl) ⟨1845971, by rfl⟩ : syracuseStep 2461295 = 3691943) B3691943
theorem B3690431 : Blo 1640019 3690431 := bstep (se 1 (by rfl) ⟨2767823, by rfl⟩ : syracuseStep 3690431 = 5535647) B5535647
theorem B5689757 : Blo 1640019 5689757 := bstep (se 3 (by rfl) ⟨1066829, by rfl⟩ : syracuseStep 5689757 = 2133659) B2133659
theorem B70947373 : Blo 1640019 70947373 := bstep (se 3 (by rfl) ⟨13302632, by rfl⟩ : syracuseStep 70947373 = 26605265) B26605265
theorem B5255771 : Blo 1640019 5255771 := bstep (se 1 (by rfl) ⟨3941828, by rfl⟩ : syracuseStep 5255771 = 7883657) B7883657
theorem B2462585 : Blo 1640019 2462585 := bstep (se 2 (by rfl) ⟨923469, by rfl⟩ : syracuseStep 2462585 = 1846939) B1846939
theorem B2462747 : Blo 1640019 2462747 := bstep (se 1 (by rfl) ⟨1847060, by rfl⟩ : syracuseStep 2462747 = 3694121) B3694121
theorem B2462951 : Blo 1640019 2462951 := bstep (se 1 (by rfl) ⟨1847213, by rfl⟩ : syracuseStep 2462951 = 3694427) B3694427
theorem B2462975 : Blo 1640019 2462975 := bstep (se 1 (by rfl) ⟨1847231, by rfl⟩ : syracuseStep 2462975 = 3694463) B3694463
theorem B3995687 : Blo 1640019 3995687 := bstep (se 1 (by rfl) ⟨2996765, by rfl⟩ : syracuseStep 3995687 = 5993531) B5993531
theorem B6314479 : Blo 1640019 6314479 := bstep (se 1 (by rfl) ⟨4735859, by rfl⟩ : syracuseStep 6314479 = 9471719) B9471719
theorem B4151807 : Blo 1640019 4151807 := bstep (se 1 (by rfl) ⟨3113855, by rfl⟩ : syracuseStep 4151807 = 6227711) B6227711
theorem B12466871 : Blo 1640019 12466871 := bstep (se 1 (by rfl) ⟨9350153, by rfl⟩ : syracuseStep 12466871 = 18700307) B18700307
theorem B5536889 : Blo 1640019 5536889 := bstep (se 2 (by rfl) ⟨2076333, by rfl⟩ : syracuseStep 5536889 = 4152667) B4152667
theorem B7011967 : Blo 1640019 7011967 := bstep (se 1 (by rfl) ⟨5258975, by rfl⟩ : syracuseStep 7011967 = 10517951) B10517951
theorem B2768951 : Blo 1640019 2768951 := bstep (se 1 (by rfl) ⟨2076713, by rfl⟩ : syracuseStep 2768951 = 4153427) B4153427
theorem B11821625 : Blo 1640019 11821625 := bstep (se 2 (by rfl) ⟨4433109, by rfl⟩ : syracuseStep 11821625 = 8866219) B8866219
theorem B15172685 : Blo 1640019 15172685 := bstep (se 3 (by rfl) ⟨2844878, by rfl⟩ : syracuseStep 15172685 = 5689757) B5689757
theorem B1640143 : Blo 1640019 1640143 := bstep (se 1 (by rfl) ⟨1230107, by rfl⟩ : syracuseStep 1640143 = 2460215) B2460215
theorem B9349289 : Blo 1640019 9349289 := bstep (se 2 (by rfl) ⟨3505983, by rfl⟩ : syracuseStep 9349289 = 7011967) B7011967
theorem B1640863 : Blo 1640019 1640863 := bstep (se 1 (by rfl) ⟨1230647, by rfl⟩ : syracuseStep 1640863 = 2461295) B2461295
theorem B2460287 : Blo 1640019 2460287 := bstep (se 1 (by rfl) ⟨1845215, by rfl⟩ : syracuseStep 2460287 = 3690431) B3690431
theorem B1641723 : Blo 1640019 1641723 := bstep (se 1 (by rfl) ⟨1231292, by rfl⟩ : syracuseStep 1641723 = 2462585) B2462585
theorem B7482719 : Blo 1640019 7482719 := bstep (se 1 (by rfl) ⟨5612039, by rfl⟩ : syracuseStep 7482719 = 11224079) B11224079
theorem B1641831 : Blo 1640019 1641831 := bstep (se 1 (by rfl) ⟨1231373, by rfl⟩ : syracuseStep 1641831 = 2462747) B2462747
theorem B94596497 : Blo 1640019 94596497 := bstep (se 2 (by rfl) ⟨35473686, by rfl⟩ : syracuseStep 94596497 = 70947373) B70947373
theorem B1641967 : Blo 1640019 1641967 := bstep (se 1 (by rfl) ⟨1231475, by rfl⟩ : syracuseStep 1641967 = 2462951) B2462951
theorem B1641983 : Blo 1640019 1641983 := bstep (se 1 (by rfl) ⟨1231487, by rfl⟩ : syracuseStep 1641983 = 2462975) B2462975
theorem B5255081 : Blo 1640019 5255081 := bstep (se 2 (by rfl) ⟨1970655, by rfl⟩ : syracuseStep 5255081 = 3941311) B3941311
theorem B2461817 : Blo 1640019 2461817 := bstep (se 2 (by rfl) ⟨923181, by rfl⟩ : syracuseStep 2461817 = 1846363) B1846363
theorem B12464441 : Blo 1640019 12464441 := bstep (se 2 (by rfl) ⟨4674165, by rfl⟩ : syracuseStep 12464441 = 9348331) B9348331
theorem B8311247 : Blo 1640019 8311247 := bstep (se 1 (by rfl) ⟨6233435, by rfl⟩ : syracuseStep 8311247 = 12466871) B12466871
theorem B14021099 : Blo 1640019 14021099 := bstep (se 1 (by rfl) ⟨10515824, by rfl⟩ : syracuseStep 14021099 = 21031649) B21031649
theorem B3691259 : Blo 1640019 3691259 := bstep (se 1 (by rfl) ⟨2768444, by rfl⟩ : syracuseStep 3691259 = 5536889) B5536889
theorem B10655165 : Blo 1640019 10655165 := bstep (se 3 (by rfl) ⟨1997843, by rfl⟩ : syracuseStep 10655165 = 3995687) B3995687
theorem B12466385 : Blo 1640019 12466385 := bstep (se 2 (by rfl) ⟨4674894, by rfl⟩ : syracuseStep 12466385 = 9349789) B9349789
theorem B14015389 : Blo 1640019 14015389 := bstep (se 3 (by rfl) ⟨2627885, by rfl⟩ : syracuseStep 14015389 = 5255771) B5255771
theorem B2767871 : Blo 1640019 2767871 := bstep (se 1 (by rfl) ⟨2075903, by rfl⟩ : syracuseStep 2767871 = 4151807) B4151807
theorem B4152617 : Blo 1640019 4152617 := bstep (se 2 (by rfl) ⟨1557231, by rfl⟩ : syracuseStep 4152617 = 3114463) B3114463
theorem B23666195 : Blo 1640019 23666195 := bstep (se 1 (by rfl) ⟨17749646, by rfl⟩ : syracuseStep 23666195 = 35499293) B35499293
theorem B33677221 : Blo 1640019 33677221 := bstep (se 4 (by rfl) ⟨3157239, by rfl⟩ : syracuseStep 33677221 = 6314479) B6314479
theorem B9347399 : Blo 1640019 9347399 := bstep (se 1 (by rfl) ⟨7010549, by rfl⟩ : syracuseStep 9347399 = 14021099) B14021099
theorem B7881083 : Blo 1640019 7881083 := bstep (se 1 (by rfl) ⟨5910812, by rfl⟩ : syracuseStep 7881083 = 11821625) B11821625
theorem B7103443 : Blo 1640019 7103443 := bstep (se 1 (by rfl) ⟨5327582, by rfl⟩ : syracuseStep 7103443 = 10655165) B10655165
theorem B18687185 : Blo 1640019 18687185 := bstep (se 2 (by rfl) ⟨7007694, by rfl⟩ : syracuseStep 18687185 = 14015389) B14015389
theorem B1640191 : Blo 1640019 1640191 := bstep (se 1 (by rfl) ⟨1230143, by rfl⟩ : syracuseStep 1640191 = 2460287) B2460287
theorem B1845247 : Blo 1640019 1845247 := bstep (se 1 (by rfl) ⟨1383935, by rfl⟩ : syracuseStep 1845247 = 2767871) B2767871
theorem B63064331 : Blo 1640019 63064331 := bstep (se 1 (by rfl) ⟨47298248, by rfl⟩ : syracuseStep 63064331 = 94596497) B94596497
theorem B44902961 : Blo 1640019 44902961 := bstep (se 2 (by rfl) ⟨16838610, by rfl⟩ : syracuseStep 44902961 = 33677221) B33677221
theorem B1845967 : Blo 1640019 1845967 := bstep (se 1 (by rfl) ⟨1384475, by rfl⟩ : syracuseStep 1845967 = 2768951) B2768951
theorem B1641211 : Blo 1640019 1641211 := bstep (se 1 (by rfl) ⟨1230908, by rfl⟩ : syracuseStep 1641211 = 2461817) B2461817
theorem B8309627 : Blo 1640019 8309627 := bstep (se 1 (by rfl) ⟨6232220, by rfl⟩ : syracuseStep 8309627 = 12464441) B12464441
theorem B5540831 : Blo 1640019 5540831 := bstep (se 1 (by rfl) ⟨4155623, by rfl⟩ : syracuseStep 5540831 = 8311247) B8311247
theorem B2460839 : Blo 1640019 2460839 := bstep (se 1 (by rfl) ⟨1845629, by rfl⟩ : syracuseStep 2460839 = 3691259) B3691259
theorem B8310923 : Blo 1640019 8310923 := bstep (se 1 (by rfl) ⟨6233192, by rfl⟩ : syracuseStep 8310923 = 12466385) B12466385
theorem B3503387 : Blo 1640019 3503387 := bstep (se 1 (by rfl) ⟨2627540, by rfl⟩ : syracuseStep 3503387 = 5255081) B5255081
theorem B10115123 : Blo 1640019 10115123 := bstep (se 1 (by rfl) ⟨7586342, by rfl⟩ : syracuseStep 10115123 = 15172685) B15172685
theorem B6232859 : Blo 1640019 6232859 := bstep (se 1 (by rfl) ⟨4674644, by rfl⟩ : syracuseStep 6232859 = 9349289) B9349289
theorem B2768411 : Blo 1640019 2768411 := bstep (se 1 (by rfl) ⟨2076308, by rfl⟩ : syracuseStep 2768411 = 4152617) B4152617
theorem B4988479 : Blo 1640019 4988479 := bstep (se 1 (by rfl) ⟨3741359, by rfl⟩ : syracuseStep 4988479 = 7482719) B7482719
theorem B15777463 : Blo 1640019 15777463 := bstep (se 1 (by rfl) ⟨11833097, by rfl⟩ : syracuseStep 15777463 = 23666195) B23666195
theorem B2335591 : Blo 1640019 2335591 := bstep (se 1 (by rfl) ⟨1751693, by rfl⟩ : syracuseStep 2335591 = 3503387) B3503387
theorem B9471257 : Blo 1640019 9471257 := bstep (se 2 (by rfl) ⟨3551721, by rfl⟩ : syracuseStep 9471257 = 7103443) B7103443
theorem B42042887 : Blo 1640019 42042887 := bstep (se 1 (by rfl) ⟨31532165, by rfl⟩ : syracuseStep 42042887 = 63064331) B63064331
theorem B29935307 : Blo 1640019 29935307 := bstep (se 1 (by rfl) ⟨22451480, by rfl⟩ : syracuseStep 29935307 = 44902961) B44902961
theorem B4155239 : Blo 1640019 4155239 := bstep (se 1 (by rfl) ⟨3116429, by rfl⟩ : syracuseStep 4155239 = 6232859) B6232859
theorem B5539751 : Blo 1640019 5539751 := bstep (se 1 (by rfl) ⟨4154813, by rfl⟩ : syracuseStep 5539751 = 8309627) B8309627
theorem B1640559 : Blo 1640019 1640559 := bstep (se 1 (by rfl) ⟨1230419, by rfl⟩ : syracuseStep 1640559 = 2460839) B2460839
theorem B1845607 : Blo 1640019 1845607 := bstep (se 1 (by rfl) ⟨1384205, by rfl⟩ : syracuseStep 1845607 = 2768411) B2768411
theorem B2460329 : Blo 1640019 2460329 := bstep (se 2 (by rfl) ⟨922623, by rfl⟩ : syracuseStep 2460329 = 1845247) B1845247
theorem B5540615 : Blo 1640019 5540615 := bstep (se 1 (by rfl) ⟨4155461, by rfl⟩ : syracuseStep 5540615 = 8310923) B8310923
theorem B5254055 : Blo 1640019 5254055 := bstep (se 1 (by rfl) ⟨3940541, by rfl⟩ : syracuseStep 5254055 = 7881083) B7881083
theorem B2461289 : Blo 1640019 2461289 := bstep (se 2 (by rfl) ⟨922983, by rfl⟩ : syracuseStep 2461289 = 1845967) B1845967
theorem B26973661 : Blo 1640019 26973661 := bstep (se 3 (by rfl) ⟨5057561, by rfl⟩ : syracuseStep 26973661 = 10115123) B10115123
theorem B6231599 : Blo 1640019 6231599 := bstep (se 1 (by rfl) ⟨4673699, by rfl⟩ : syracuseStep 6231599 = 9347399) B9347399
theorem B12458123 : Blo 1640019 12458123 := bstep (se 1 (by rfl) ⟨9343592, by rfl⟩ : syracuseStep 12458123 = 18687185) B18687185
theorem B3693887 : Blo 1640019 3693887 := bstep (se 1 (by rfl) ⟨2770415, by rfl⟩ : syracuseStep 3693887 = 5540831) B5540831
theorem B6651305 : Blo 1640019 6651305 := bstep (se 2 (by rfl) ⟨2494239, by rfl⟩ : syracuseStep 6651305 = 4988479) B4988479
theorem B21036617 : Blo 1640019 21036617 := bstep (se 2 (by rfl) ⟨7888731, by rfl⟩ : syracuseStep 21036617 = 15777463) B15777463
theorem B4154399 : Blo 1640019 4154399 := bstep (se 1 (by rfl) ⟨3115799, by rfl⟩ : syracuseStep 4154399 = 6231599) B6231599
theorem B19956871 : Blo 1640019 19956871 := bstep (se 1 (by rfl) ⟨14967653, by rfl⟩ : syracuseStep 19956871 = 29935307) B29935307
theorem B3114121 : Blo 1640019 3114121 := bstep (se 2 (by rfl) ⟨1167795, by rfl⟩ : syracuseStep 3114121 = 2335591) B2335591
theorem B2770159 : Blo 1640019 2770159 := bstep (se 1 (by rfl) ⟨2077619, by rfl⟩ : syracuseStep 2770159 = 4155239) B4155239
theorem B1640219 : Blo 1640019 1640219 := bstep (se 1 (by rfl) ⟨1230164, by rfl⟩ : syracuseStep 1640219 = 2460329) B2460329
theorem B35964881 : Blo 1640019 35964881 := bstep (se 2 (by rfl) ⟨13486830, by rfl⟩ : syracuseStep 35964881 = 26973661) B26973661
theorem B4434203 : Blo 1640019 4434203 := bstep (se 1 (by rfl) ⟨3325652, by rfl⟩ : syracuseStep 4434203 = 6651305) B6651305
theorem B1640859 : Blo 1640019 1640859 := bstep (se 1 (by rfl) ⟨1230644, by rfl⟩ : syracuseStep 1640859 = 2461289) B2461289
theorem B2460809 : Blo 1640019 2460809 := bstep (se 2 (by rfl) ⟨922803, by rfl⟩ : syracuseStep 2460809 = 1845607) B1845607
theorem B28028591 : Blo 1640019 28028591 := bstep (se 1 (by rfl) ⟨21021443, by rfl⟩ : syracuseStep 28028591 = 42042887) B42042887
theorem B3502703 : Blo 1640019 3502703 := bstep (se 1 (by rfl) ⟨2627027, by rfl⟩ : syracuseStep 3502703 = 5254055) B5254055
theorem B2462591 : Blo 1640019 2462591 := bstep (se 1 (by rfl) ⟨1846943, by rfl⟩ : syracuseStep 2462591 = 3693887) B3693887
theorem B6314171 : Blo 1640019 6314171 := bstep (se 1 (by rfl) ⟨4735628, by rfl⟩ : syracuseStep 6314171 = 9471257) B9471257
theorem B3693167 : Blo 1640019 3693167 := bstep (se 1 (by rfl) ⟨2769875, by rfl⟩ : syracuseStep 3693167 = 5539751) B5539751
theorem B8305415 : Blo 1640019 8305415 := bstep (se 1 (by rfl) ⟨6229061, by rfl⟩ : syracuseStep 8305415 = 12458123) B12458123
theorem B3693743 : Blo 1640019 3693743 := bstep (se 1 (by rfl) ⟨2770307, by rfl⟩ : syracuseStep 3693743 = 5540615) B5540615
theorem B14024411 : Blo 1640019 14024411 := bstep (se 1 (by rfl) ⟨10518308, by rfl⟩ : syracuseStep 14024411 = 21036617) B21036617
theorem B2769599 : Blo 1640019 2769599 := bstep (se 1 (by rfl) ⟨2077199, by rfl⟩ : syracuseStep 2769599 = 4154399) B4154399
theorem B26609161 : Blo 1640019 26609161 := bstep (se 2 (by rfl) ⟨9978435, by rfl⟩ : syracuseStep 26609161 = 19956871) B19956871
theorem B9340541 : Blo 1640019 9340541 := bstep (se 3 (by rfl) ⟨1751351, by rfl⟩ : syracuseStep 9340541 = 3502703) B3502703
theorem B1640539 : Blo 1640019 1640539 := bstep (se 1 (by rfl) ⟨1230404, by rfl⟩ : syracuseStep 1640539 = 2460809) B2460809
theorem B9349607 : Blo 1640019 9349607 := bstep (se 1 (by rfl) ⟨7012205, by rfl⟩ : syracuseStep 9349607 = 14024411) B14024411
theorem B16837789 : Blo 1640019 16837789 := bstep (se 3 (by rfl) ⟨3157085, by rfl⟩ : syracuseStep 16837789 = 6314171) B6314171
theorem B1641727 : Blo 1640019 1641727 := bstep (se 1 (by rfl) ⟨1231295, by rfl⟩ : syracuseStep 1641727 = 2462591) B2462591
theorem B11824541 : Blo 1640019 11824541 := bstep (se 3 (by rfl) ⟨2217101, by rfl⟩ : syracuseStep 11824541 = 4434203) B4434203
theorem B2462111 : Blo 1640019 2462111 := bstep (se 1 (by rfl) ⟨1846583, by rfl⟩ : syracuseStep 2462111 = 3693167) B3693167
theorem B2462495 : Blo 1640019 2462495 := bstep (se 1 (by rfl) ⟨1846871, by rfl⟩ : syracuseStep 2462495 = 3693743) B3693743
theorem B23976587 : Blo 1640019 23976587 := bstep (se 1 (by rfl) ⟨17982440, by rfl⟩ : syracuseStep 23976587 = 35964881) B35964881
theorem B4152161 : Blo 1640019 4152161 := bstep (se 2 (by rfl) ⟨1557060, by rfl⟩ : syracuseStep 4152161 = 3114121) B3114121
theorem B3693545 : Blo 1640019 3693545 := bstep (se 2 (by rfl) ⟨1385079, by rfl⟩ : syracuseStep 3693545 = 2770159) B2770159
theorem B5536943 : Blo 1640019 5536943 := bstep (se 1 (by rfl) ⟨4152707, by rfl⟩ : syracuseStep 5536943 = 8305415) B8305415
theorem B18685727 : Blo 1640019 18685727 := bstep (se 1 (by rfl) ⟨14014295, by rfl⟩ : syracuseStep 18685727 = 28028591) B28028591
theorem B6227027 : Blo 1640019 6227027 := bstep (se 1 (by rfl) ⟨4670270, by rfl⟩ : syracuseStep 6227027 = 9340541) B9340541
theorem B15984391 : Blo 1640019 15984391 := bstep (se 1 (by rfl) ⟨11988293, by rfl⟩ : syracuseStep 15984391 = 23976587) B23976587
theorem B7883027 : Blo 1640019 7883027 := bstep (se 1 (by rfl) ⟨5912270, by rfl⟩ : syracuseStep 7883027 = 11824541) B11824541
theorem B1641407 : Blo 1640019 1641407 := bstep (se 1 (by rfl) ⟨1231055, by rfl⟩ : syracuseStep 1641407 = 2462111) B2462111
theorem B1846399 : Blo 1640019 1846399 := bstep (se 1 (by rfl) ⟨1384799, by rfl⟩ : syracuseStep 1846399 = 2769599) B2769599
theorem B1641663 : Blo 1640019 1641663 := bstep (se 1 (by rfl) ⟨1231247, by rfl⟩ : syracuseStep 1641663 = 2462495) B2462495
theorem B22450385 : Blo 1640019 22450385 := bstep (se 2 (by rfl) ⟨8418894, by rfl⟩ : syracuseStep 22450385 = 16837789) B16837789
theorem B2462363 : Blo 1640019 2462363 := bstep (se 1 (by rfl) ⟨1846772, by rfl⟩ : syracuseStep 2462363 = 3693545) B3693545
theorem B3691295 : Blo 1640019 3691295 := bstep (se 1 (by rfl) ⟨2768471, by rfl⟩ : syracuseStep 3691295 = 5536943) B5536943
theorem B12457151 : Blo 1640019 12457151 := bstep (se 1 (by rfl) ⟨9342863, by rfl⟩ : syracuseStep 12457151 = 18685727) B18685727
theorem B6233071 : Blo 1640019 6233071 := bstep (se 1 (by rfl) ⟨4674803, by rfl⟩ : syracuseStep 6233071 = 9349607) B9349607
theorem B2768107 : Blo 1640019 2768107 := bstep (se 1 (by rfl) ⟨2076080, by rfl⟩ : syracuseStep 2768107 = 4152161) B4152161
theorem B35478881 : Blo 1640019 35478881 := bstep (se 2 (by rfl) ⟨13304580, by rfl⟩ : syracuseStep 35478881 = 26609161) B26609161
theorem B14966923 : Blo 1640019 14966923 := bstep (se 1 (by rfl) ⟨11225192, by rfl⟩ : syracuseStep 14966923 = 22450385) B22450385
theorem B23652587 : Blo 1640019 23652587 := bstep (se 1 (by rfl) ⟨17739440, by rfl⟩ : syracuseStep 23652587 = 35478881) B35478881
theorem B1641575 : Blo 1640019 1641575 := bstep (se 1 (by rfl) ⟨1231181, by rfl⟩ : syracuseStep 1641575 = 2462363) B2462363
theorem B2460863 : Blo 1640019 2460863 := bstep (se 1 (by rfl) ⟨1845647, by rfl⟩ : syracuseStep 2460863 = 3691295) B3691295
theorem B8310761 : Blo 1640019 8310761 := bstep (se 2 (by rfl) ⟨3116535, by rfl⟩ : syracuseStep 8310761 = 6233071) B6233071
theorem B2461865 : Blo 1640019 2461865 := bstep (se 2 (by rfl) ⟨923199, by rfl⟩ : syracuseStep 2461865 = 1846399) B1846399
theorem B5255351 : Blo 1640019 5255351 := bstep (se 1 (by rfl) ⟨3941513, by rfl⟩ : syracuseStep 5255351 = 7883027) B7883027
theorem B3690809 : Blo 1640019 3690809 := bstep (se 2 (by rfl) ⟨1384053, by rfl⟩ : syracuseStep 3690809 = 2768107) B2768107
theorem B21312521 : Blo 1640019 21312521 := bstep (se 2 (by rfl) ⟨7992195, by rfl⟩ : syracuseStep 21312521 = 15984391) B15984391
theorem B4151351 : Blo 1640019 4151351 := bstep (se 1 (by rfl) ⟨3113513, by rfl⟩ : syracuseStep 4151351 = 6227027) B6227027
theorem B8304767 : Blo 1640019 8304767 := bstep (se 1 (by rfl) ⟨6228575, by rfl⟩ : syracuseStep 8304767 = 12457151) B12457151
theorem B19955897 : Blo 1640019 19955897 := bstep (se 2 (by rfl) ⟨7483461, by rfl⟩ : syracuseStep 19955897 = 14966923) B14966923
theorem B1640575 : Blo 1640019 1640575 := bstep (se 1 (by rfl) ⟨1230431, by rfl⟩ : syracuseStep 1640575 = 2460863) B2460863
theorem B5540507 : Blo 1640019 5540507 := bstep (se 1 (by rfl) ⟨4155380, by rfl⟩ : syracuseStep 5540507 = 8310761) B8310761
theorem B1641243 : Blo 1640019 1641243 := bstep (se 1 (by rfl) ⟨1230932, by rfl⟩ : syracuseStep 1641243 = 2461865) B2461865
theorem B2460539 : Blo 1640019 2460539 := bstep (se 1 (by rfl) ⟨1845404, by rfl⟩ : syracuseStep 2460539 = 3690809) B3690809
theorem B14208347 : Blo 1640019 14208347 := bstep (se 1 (by rfl) ⟨10656260, by rfl⟩ : syracuseStep 14208347 = 21312521) B21312521
theorem B3503567 : Blo 1640019 3503567 := bstep (se 1 (by rfl) ⟨2627675, by rfl⟩ : syracuseStep 3503567 = 5255351) B5255351
theorem B2767567 : Blo 1640019 2767567 := bstep (se 1 (by rfl) ⟨2075675, by rfl⟩ : syracuseStep 2767567 = 4151351) B4151351
theorem B5536511 : Blo 1640019 5536511 := bstep (se 1 (by rfl) ⟨4152383, by rfl⟩ : syracuseStep 5536511 = 8304767) B8304767
theorem B15768391 : Blo 1640019 15768391 := bstep (se 1 (by rfl) ⟨11826293, by rfl⟩ : syracuseStep 15768391 = 23652587) B23652587
theorem B13303931 : Blo 1640019 13303931 := bstep (se 1 (by rfl) ⟨9977948, by rfl⟩ : syracuseStep 13303931 = 19955897) B19955897
theorem B2335711 : Blo 1640019 2335711 := bstep (se 1 (by rfl) ⟨1751783, by rfl⟩ : syracuseStep 2335711 = 3503567) B3503567
theorem B1640359 : Blo 1640019 1640359 := bstep (se 1 (by rfl) ⟨1230269, by rfl⟩ : syracuseStep 1640359 = 2460539) B2460539
theorem B9472231 : Blo 1640019 9472231 := bstep (se 1 (by rfl) ⟨7104173, by rfl⟩ : syracuseStep 9472231 = 14208347) B14208347
theorem B3690089 : Blo 1640019 3690089 := bstep (se 2 (by rfl) ⟨1383783, by rfl⟩ : syracuseStep 3690089 = 2767567) B2767567
theorem B21024521 : Blo 1640019 21024521 := bstep (se 2 (by rfl) ⟨7884195, by rfl⟩ : syracuseStep 21024521 = 15768391) B15768391
theorem B3691007 : Blo 1640019 3691007 := bstep (se 1 (by rfl) ⟨2768255, by rfl⟩ : syracuseStep 3691007 = 5536511) B5536511
theorem B3693671 : Blo 1640019 3693671 := bstep (se 1 (by rfl) ⟨2770253, by rfl⟩ : syracuseStep 3693671 = 5540507) B5540507
theorem B3114281 : Blo 1640019 3114281 := bstep (se 2 (by rfl) ⟨1167855, by rfl⟩ : syracuseStep 3114281 = 2335711) B2335711
theorem B2460059 : Blo 1640019 2460059 := bstep (se 1 (by rfl) ⟨1845044, by rfl⟩ : syracuseStep 2460059 = 3690089) B3690089
theorem B2460671 : Blo 1640019 2460671 := bstep (se 1 (by rfl) ⟨1845503, by rfl⟩ : syracuseStep 2460671 = 3691007) B3691007
theorem B2462447 : Blo 1640019 2462447 := bstep (se 1 (by rfl) ⟨1846835, by rfl⟩ : syracuseStep 2462447 = 3693671) B3693671
theorem B12629641 : Blo 1640019 12629641 := bstep (se 2 (by rfl) ⟨4736115, by rfl⟩ : syracuseStep 12629641 = 9472231) B9472231
theorem B35477149 : Blo 1640019 35477149 := bstep (se 3 (by rfl) ⟨6651965, by rfl⟩ : syracuseStep 35477149 = 13303931) B13303931
theorem B14016347 : Blo 1640019 14016347 := bstep (se 1 (by rfl) ⟨10512260, by rfl⟩ : syracuseStep 14016347 = 21024521) B21024521
theorem B1640039 : Blo 1640019 1640039 := bstep (se 1 (by rfl) ⟨1230029, by rfl⟩ : syracuseStep 1640039 = 2460059) B2460059
theorem B1640447 : Blo 1640019 1640447 := bstep (se 1 (by rfl) ⟨1230335, by rfl⟩ : syracuseStep 1640447 = 2460671) B2460671
theorem B47302865 : Blo 1640019 47302865 := bstep (se 2 (by rfl) ⟨17738574, by rfl⟩ : syracuseStep 47302865 = 35477149) B35477149
theorem B1641631 : Blo 1640019 1641631 := bstep (se 1 (by rfl) ⟨1231223, by rfl⟩ : syracuseStep 1641631 = 2462447) B2462447
theorem B2076187 : Blo 1640019 2076187 := bstep (se 1 (by rfl) ⟨1557140, by rfl⟩ : syracuseStep 2076187 = 3114281) B3114281
theorem B16839521 : Blo 1640019 16839521 := bstep (se 2 (by rfl) ⟨6314820, by rfl⟩ : syracuseStep 16839521 = 12629641) B12629641
theorem B9344231 : Blo 1640019 9344231 := bstep (se 1 (by rfl) ⟨7008173, by rfl⟩ : syracuseStep 9344231 = 14016347) B14016347
theorem B11226347 : Blo 1640019 11226347 := bstep (se 1 (by rfl) ⟨8419760, by rfl⟩ : syracuseStep 11226347 = 16839521) B16839521
theorem B6229487 : Blo 1640019 6229487 := bstep (se 1 (by rfl) ⟨4672115, by rfl⟩ : syracuseStep 6229487 = 9344231) B9344231
theorem B31535243 : Blo 1640019 31535243 := bstep (se 1 (by rfl) ⟨23651432, by rfl⟩ : syracuseStep 31535243 = 47302865) B47302865
theorem B2768249 : Blo 1640019 2768249 := bstep (se 2 (by rfl) ⟨1038093, by rfl⟩ : syracuseStep 2768249 = 2076187) B2076187
theorem B1845499 : Blo 1640019 1845499 := bstep (se 1 (by rfl) ⟨1384124, by rfl⟩ : syracuseStep 1845499 = 2768249) B2768249
theorem B21023495 : Blo 1640019 21023495 := bstep (se 1 (by rfl) ⟨15767621, by rfl⟩ : syracuseStep 21023495 = 31535243) B31535243
theorem B7484231 : Blo 1640019 7484231 := bstep (se 1 (by rfl) ⟨5613173, by rfl⟩ : syracuseStep 7484231 = 11226347) B11226347
theorem B4152991 : Blo 1640019 4152991 := bstep (se 1 (by rfl) ⟨3114743, by rfl⟩ : syracuseStep 4152991 = 6229487) B6229487
theorem B4989487 : Blo 1640019 4989487 := bstep (se 1 (by rfl) ⟨3742115, by rfl⟩ : syracuseStep 4989487 = 7484231) B7484231
theorem B2460665 : Blo 1640019 2460665 := bstep (se 2 (by rfl) ⟨922749, by rfl⟩ : syracuseStep 2460665 = 1845499) B1845499
theorem B14015663 : Blo 1640019 14015663 := bstep (se 1 (by rfl) ⟨10511747, by rfl⟩ : syracuseStep 14015663 = 21023495) B21023495
theorem B5537321 : Blo 1640019 5537321 := bstep (se 2 (by rfl) ⟨2076495, by rfl⟩ : syracuseStep 5537321 = 4152991) B4152991
theorem B6652649 : Blo 1640019 6652649 := bstep (se 2 (by rfl) ⟨2494743, by rfl⟩ : syracuseStep 6652649 = 4989487) B4989487
theorem B1640443 : Blo 1640019 1640443 := bstep (se 1 (by rfl) ⟨1230332, by rfl⟩ : syracuseStep 1640443 = 2460665) B2460665
theorem B9343775 : Blo 1640019 9343775 := bstep (se 1 (by rfl) ⟨7007831, by rfl⟩ : syracuseStep 9343775 = 14015663) B14015663
theorem B3691547 : Blo 1640019 3691547 := bstep (se 1 (by rfl) ⟨2768660, by rfl⟩ : syracuseStep 3691547 = 5537321) B5537321
theorem B6229183 : Blo 1640019 6229183 := bstep (se 1 (by rfl) ⟨4671887, by rfl⟩ : syracuseStep 6229183 = 9343775) B9343775
theorem B2461031 : Blo 1640019 2461031 := bstep (se 1 (by rfl) ⟨1845773, by rfl⟩ : syracuseStep 2461031 = 3691547) B3691547
theorem B17740397 : Blo 1640019 17740397 := bstep (se 3 (by rfl) ⟨3326324, by rfl⟩ : syracuseStep 17740397 = 6652649) B6652649
theorem B1640687 : Blo 1640019 1640687 := bstep (se 1 (by rfl) ⟨1230515, by rfl⟩ : syracuseStep 1640687 = 2461031) B2461031
theorem B11826931 : Blo 1640019 11826931 := bstep (se 1 (by rfl) ⟨8870198, by rfl⟩ : syracuseStep 11826931 = 17740397) B17740397
theorem B8305577 : Blo 1640019 8305577 := bstep (se 2 (by rfl) ⟨3114591, by rfl⟩ : syracuseStep 8305577 = 6229183) B6229183
theorem B5537051 : Blo 1640019 5537051 := bstep (se 1 (by rfl) ⟨4152788, by rfl⟩ : syracuseStep 5537051 = 8305577) B8305577
theorem B15769241 : Blo 1640019 15769241 := bstep (se 2 (by rfl) ⟨5913465, by rfl⟩ : syracuseStep 15769241 = 11826931) B11826931
theorem B10512827 : Blo 1640019 10512827 := bstep (se 1 (by rfl) ⟨7884620, by rfl⟩ : syracuseStep 10512827 = 15769241) B15769241
theorem B3691367 : Blo 1640019 3691367 := bstep (se 1 (by rfl) ⟨2768525, by rfl⟩ : syracuseStep 3691367 = 5537051) B5537051
theorem B2460911 : Blo 1640019 2460911 := bstep (se 1 (by rfl) ⟨1845683, by rfl⟩ : syracuseStep 2460911 = 3691367) B3691367
theorem B7008551 : Blo 1640019 7008551 := bstep (se 1 (by rfl) ⟨5256413, by rfl⟩ : syracuseStep 7008551 = 10512827) B10512827
theorem B1640607 : Blo 1640019 1640607 := bstep (se 1 (by rfl) ⟨1230455, by rfl⟩ : syracuseStep 1640607 = 2460911) B2460911
theorem B4672367 : Blo 1640019 4672367 := bstep (se 1 (by rfl) ⟨3504275, by rfl⟩ : syracuseStep 4672367 = 7008551) B7008551
theorem B3114911 : Blo 1640019 3114911 := bstep (se 1 (by rfl) ⟨2336183, by rfl⟩ : syracuseStep 3114911 = 4672367) B4672367
theorem B2076607 : Blo 1640019 2076607 := bstep (se 1 (by rfl) ⟨1557455, by rfl⟩ : syracuseStep 2076607 = 3114911) B3114911
theorem B2768809 : Blo 1640019 2768809 := bstep (se 2 (by rfl) ⟨1038303, by rfl⟩ : syracuseStep 2768809 = 2076607) B2076607
theorem B3691745 : Blo 1640019 3691745 := bstep (se 2 (by rfl) ⟨1384404, by rfl⟩ : syracuseStep 3691745 = 2768809) B2768809
theorem B2461163 : Blo 1640019 2461163 := bstep (se 1 (by rfl) ⟨1845872, by rfl⟩ : syracuseStep 2461163 = 3691745) B3691745
theorem B1640775 : Blo 1640019 1640775 := bstep (se 1 (by rfl) ⟨1230581, by rfl⟩ : syracuseStep 1640775 = 2461163) B2461163

theorem C0 (j : ℕ) (h1 : 410004 ≤ j) (h2 : j ≤ 410504) : Blo 1640019 (4 * j + 3) := by
  interval_cases j
  · exact B1640019
  · exact B1640023
  · exact B1640027
  · exact B1640031
  · exact B1640035
  · exact B1640039
  · exact B1640043
  · exact B1640047
  · exact B1640051
  · exact B1640055
  · exact B1640059
  · exact B1640063
  · exact B1640067
  · exact B1640071
  · exact B1640075
  · exact B1640079
  · exact B1640083
  · exact B1640087
  · exact B1640091
  · exact B1640095
  · exact B1640099
  · exact B1640103
  · exact B1640107
  · exact B1640111
  · exact B1640115
  · exact B1640119
  · exact B1640123
  · exact B1640127
  · exact B1640131
  · exact B1640135
  · exact B1640139
  · exact B1640143
  · exact B1640147
  · exact B1640151
  · exact B1640155
  · exact B1640159
  · exact B1640163
  · exact B1640167
  · exact B1640171
  · exact B1640175
  · exact B1640179
  · exact B1640183
  · exact B1640187
  · exact B1640191
  · exact B1640195
  · exact B1640199
  · exact B1640203
  · exact B1640207
  · exact B1640211
  · exact B1640215
  · exact B1640219
  · exact B1640223
  · exact B1640227
  · exact B1640231
  · exact B1640235
  · exact B1640239
  · exact B1640243
  · exact B1640247
  · exact B1640251
  · exact B1640255
  · exact B1640259
  · exact B1640263
  · exact B1640267
  · exact B1640271
  · exact B1640275
  · exact B1640279
  · exact B1640283
  · exact B1640287
  · exact B1640291
  · exact B1640295
  · exact B1640299
  · exact B1640303
  · exact B1640307
  · exact B1640311
  · exact B1640315
  · exact B1640319
  · exact B1640323
  · exact B1640327
  · exact B1640331
  · exact B1640335
  · exact B1640339
  · exact B1640343
  · exact B1640347
  · exact B1640351
  · exact B1640355
  · exact B1640359
  · exact B1640363
  · exact B1640367
  · exact B1640371
  · exact B1640375
  · exact B1640379
  · exact B1640383
  · exact B1640387
  · exact B1640391
  · exact B1640395
  · exact B1640399
  · exact B1640403
  · exact B1640407
  · exact B1640411
  · exact B1640415
  · exact B1640419
  · exact B1640423
  · exact B1640427
  · exact B1640431
  · exact B1640435
  · exact B1640439
  · exact B1640443
  · exact B1640447
  · exact B1640451
  · exact B1640455
  · exact B1640459
  · exact B1640463
  · exact B1640467
  · exact B1640471
  · exact B1640475
  · exact B1640479
  · exact B1640483
  · exact B1640487
  · exact B1640491
  · exact B1640495
  · exact B1640499
  · exact B1640503
  · exact B1640507
  · exact B1640511
  · exact B1640515
  · exact B1640519
  · exact B1640523
  · exact B1640527
  · exact B1640531
  · exact B1640535
  · exact B1640539
  · exact B1640543
  · exact B1640547
  · exact B1640551
  · exact B1640555
  · exact B1640559
  · exact B1640563
  · exact B1640567
  · exact B1640571
  · exact B1640575
  · exact B1640579
  · exact B1640583
  · exact B1640587
  · exact B1640591
  · exact B1640595
  · exact B1640599
  · exact B1640603
  · exact B1640607
  · exact B1640611
  · exact B1640615
  · exact B1640619
  · exact B1640623
  · exact B1640627
  · exact B1640631
  · exact B1640635
  · exact B1640639
  · exact B1640643
  · exact B1640647
  · exact B1640651
  · exact B1640655
  · exact B1640659
  · exact B1640663
  · exact B1640667
  · exact B1640671
  · exact B1640675
  · exact B1640679
  · exact B1640683
  · exact B1640687
  · exact B1640691
  · exact B1640695
  · exact B1640699
  · exact B1640703
  · exact B1640707
  · exact B1640711
  · exact B1640715
  · exact B1640719
  · exact B1640723
  · exact B1640727
  · exact B1640731
  · exact B1640735
  · exact B1640739
  · exact B1640743
  · exact B1640747
  · exact B1640751
  · exact B1640755
  · exact B1640759
  · exact B1640763
  · exact B1640767
  · exact B1640771
  · exact B1640775
  · exact B1640779
  · exact B1640783
  · exact B1640787
  · exact B1640791
  · exact B1640795
  · exact B1640799
  · exact B1640803
  · exact B1640807
  · exact B1640811
  · exact B1640815
  · exact B1640819
  · exact B1640823
  · exact B1640827
  · exact B1640831
  · exact B1640835
  · exact B1640839
  · exact B1640843
  · exact B1640847
  · exact B1640851
  · exact B1640855
  · exact B1640859
  · exact B1640863
  · exact B1640867
  · exact B1640871
  · exact B1640875
  · exact B1640879
  · exact B1640883
  · exact B1640887
  · exact B1640891
  · exact B1640895
  · exact B1640899
  · exact B1640903
  · exact B1640907
  · exact B1640911
  · exact B1640915
  · exact B1640919
  · exact B1640923
  · exact B1640927
  · exact B1640931
  · exact B1640935
  · exact B1640939
  · exact B1640943
  · exact B1640947
  · exact B1640951
  · exact B1640955
  · exact B1640959
  · exact B1640963
  · exact B1640967
  · exact B1640971
  · exact B1640975
  · exact B1640979
  · exact B1640983
  · exact B1640987
  · exact B1640991
  · exact B1640995
  · exact B1640999
  · exact B1641003
  · exact B1641007
  · exact B1641011
  · exact B1641015
  · exact B1641019
  · exact B1641023
  · exact B1641027
  · exact B1641031
  · exact B1641035
  · exact B1641039
  · exact B1641043
  · exact B1641047
  · exact B1641051
  · exact B1641055
  · exact B1641059
  · exact B1641063
  · exact B1641067
  · exact B1641071
  · exact B1641075
  · exact B1641079
  · exact B1641083
  · exact B1641087
  · exact B1641091
  · exact B1641095
  · exact B1641099
  · exact B1641103
  · exact B1641107
  · exact B1641111
  · exact B1641115
  · exact B1641119
  · exact B1641123
  · exact B1641127
  · exact B1641131
  · exact B1641135
  · exact B1641139
  · exact B1641143
  · exact B1641147
  · exact B1641151
  · exact B1641155
  · exact B1641159
  · exact B1641163
  · exact B1641167
  · exact B1641171
  · exact B1641175
  · exact B1641179
  · exact B1641183
  · exact B1641187
  · exact B1641191
  · exact B1641195
  · exact B1641199
  · exact B1641203
  · exact B1641207
  · exact B1641211
  · exact B1641215
  · exact B1641219
  · exact B1641223
  · exact B1641227
  · exact B1641231
  · exact B1641235
  · exact B1641239
  · exact B1641243
  · exact B1641247
  · exact B1641251
  · exact B1641255
  · exact B1641259
  · exact B1641263
  · exact B1641267
  · exact B1641271
  · exact B1641275
  · exact B1641279
  · exact B1641283
  · exact B1641287
  · exact B1641291
  · exact B1641295
  · exact B1641299
  · exact B1641303
  · exact B1641307
  · exact B1641311
  · exact B1641315
  · exact B1641319
  · exact B1641323
  · exact B1641327
  · exact B1641331
  · exact B1641335
  · exact B1641339
  · exact B1641343
  · exact B1641347
  · exact B1641351
  · exact B1641355
  · exact B1641359
  · exact B1641363
  · exact B1641367
  · exact B1641371
  · exact B1641375
  · exact B1641379
  · exact B1641383
  · exact B1641387
  · exact B1641391
  · exact B1641395
  · exact B1641399
  · exact B1641403
  · exact B1641407
  · exact B1641411
  · exact B1641415
  · exact B1641419
  · exact B1641423
  · exact B1641427
  · exact B1641431
  · exact B1641435
  · exact B1641439
  · exact B1641443
  · exact B1641447
  · exact B1641451
  · exact B1641455
  · exact B1641459
  · exact B1641463
  · exact B1641467
  · exact B1641471
  · exact B1641475
  · exact B1641479
  · exact B1641483
  · exact B1641487
  · exact B1641491
  · exact B1641495
  · exact B1641499
  · exact B1641503
  · exact B1641507
  · exact B1641511
  · exact B1641515
  · exact B1641519
  · exact B1641523
  · exact B1641527
  · exact B1641531
  · exact B1641535
  · exact B1641539
  · exact B1641543
  · exact B1641547
  · exact B1641551
  · exact B1641555
  · exact B1641559
  · exact B1641563
  · exact B1641567
  · exact B1641571
  · exact B1641575
  · exact B1641579
  · exact B1641583
  · exact B1641587
  · exact B1641591
  · exact B1641595
  · exact B1641599
  · exact B1641603
  · exact B1641607
  · exact B1641611
  · exact B1641615
  · exact B1641619
  · exact B1641623
  · exact B1641627
  · exact B1641631
  · exact B1641635
  · exact B1641639
  · exact B1641643
  · exact B1641647
  · exact B1641651
  · exact B1641655
  · exact B1641659
  · exact B1641663
  · exact B1641667
  · exact B1641671
  · exact B1641675
  · exact B1641679
  · exact B1641683
  · exact B1641687
  · exact B1641691
  · exact B1641695
  · exact B1641699
  · exact B1641703
  · exact B1641707
  · exact B1641711
  · exact B1641715
  · exact B1641719
  · exact B1641723
  · exact B1641727
  · exact B1641731
  · exact B1641735
  · exact B1641739
  · exact B1641743
  · exact B1641747
  · exact B1641751
  · exact B1641755
  · exact B1641759
  · exact B1641763
  · exact B1641767
  · exact B1641771
  · exact B1641775
  · exact B1641779
  · exact B1641783
  · exact B1641787
  · exact B1641791
  · exact B1641795
  · exact B1641799
  · exact B1641803
  · exact B1641807
  · exact B1641811
  · exact B1641815
  · exact B1641819
  · exact B1641823
  · exact B1641827
  · exact B1641831
  · exact B1641835
  · exact B1641839
  · exact B1641843
  · exact B1641847
  · exact B1641851
  · exact B1641855
  · exact B1641859
  · exact B1641863
  · exact B1641867
  · exact B1641871
  · exact B1641875
  · exact B1641879
  · exact B1641883
  · exact B1641887
  · exact B1641891
  · exact B1641895
  · exact B1641899
  · exact B1641903
  · exact B1641907
  · exact B1641911
  · exact B1641915
  · exact B1641919
  · exact B1641923
  · exact B1641927
  · exact B1641931
  · exact B1641935
  · exact B1641939
  · exact B1641943
  · exact B1641947
  · exact B1641951
  · exact B1641955
  · exact B1641959
  · exact B1641963
  · exact B1641967
  · exact B1641971
  · exact B1641975
  · exact B1641979
  · exact B1641983
  · exact B1641987
  · exact B1641991
  · exact B1641995
  · exact B1641999
  · exact B1642003
  · exact B1642007
  · exact B1642011
  · exact B1642015
  · exact B1642019

theorem solution (m : ℕ) (hlo : 1640019 ≤ m) (hhi : m ≤ 1642019) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 410004 ≤ j := by omega
    have hj2 : j ≤ 410504 := by omega
    have hb : Blo 1640019 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
