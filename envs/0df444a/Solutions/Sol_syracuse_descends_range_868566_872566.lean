-- Prove2me | solution 1 for syracuse_descends_range_868566_872566
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:21:41.941721+00:00
-- url     : https://prove2.me/submissions/7e2c6d82-5ad2-47c8-ad4d-3c587e4a38af

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


theorem B3309781 : Blo 868566 3309781 := bbase (se 7 (by rfl) ⟨38786, by rfl⟩ : syracuseStep 3309781 = 77573) (by norm_num)
theorem B1671637 : Blo 868566 1671637 := bbase (se 7 (by rfl) ⟨19589, by rfl⟩ : syracuseStep 1671637 = 39179) (by norm_num)
theorem B3310085 : Blo 868566 3310085 := bbase (se 4 (by rfl) ⟨310320, by rfl⟩ : syracuseStep 3310085 = 620641) (by norm_num)
theorem B9044597 : Blo 868566 9044597 := bbase (se 5 (by rfl) ⟨423965, by rfl⟩ : syracuseStep 9044597 = 847931) (by norm_num)
theorem B6357685 : Blo 868566 6357685 := bbase (se 5 (by rfl) ⟨298016, by rfl⟩ : syracuseStep 6357685 = 596033) (by norm_num)
theorem B7144213 : Blo 868566 7144213 := bbase (se 6 (by rfl) ⟨167442, by rfl⟩ : syracuseStep 7144213 = 334885) (by norm_num)
theorem B2786197 : Blo 868566 2786197 := bbase (se 6 (by rfl) ⟨65301, by rfl⟩ : syracuseStep 2786197 = 130603) (by norm_num)
theorem B4949045 : Blo 868566 4949045 := bbase (se 5 (by rfl) ⟨231986, by rfl⟩ : syracuseStep 4949045 = 463973) (by norm_num)
theorem B1673029 : Blo 868566 1673029 := bbase (se 4 (by rfl) ⟨156846, by rfl⟩ : syracuseStep 1673029 = 313693) (by norm_num)
theorem B21137237 : Blo 868566 21137237 := bbase (se 9 (by rfl) ⟨61925, by rfl⟩ : syracuseStep 21137237 = 123851) (by norm_num)
theorem B5572597 : Blo 868566 5572597 := bbase (se 5 (by rfl) ⟨261215, by rfl⟩ : syracuseStep 5572597 = 522431) (by norm_num)
theorem B6621749 : Blo 868566 6621749 := bbase (se 5 (by rfl) ⟨310394, by rfl⟩ : syracuseStep 6621749 = 620789) (by norm_num)
theorem B3312197 : Blo 868566 3312197 := bbase (se 4 (by rfl) ⟨310518, by rfl⟩ : syracuseStep 3312197 = 621037) (by norm_num)
theorem B1608317 : Blo 868566 1608317 := bbase (se 3 (by rfl) ⟨301559, by rfl⟩ : syracuseStep 1608317 = 603119) (by norm_num)
theorem B3312485 : Blo 868566 3312485 := bbase (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) (by norm_num)
theorem B2198573 : Blo 868566 2198573 := bbase (se 3 (by rfl) ⟨412232, by rfl⟩ : syracuseStep 2198573 = 824465) (by norm_num)
theorem B2198765 : Blo 868566 2198765 := bbase (se 3 (by rfl) ⟨412268, by rfl⟩ : syracuseStep 2198765 = 824537) (by norm_num)
theorem B2199109 : Blo 868566 2199109 := bbase (se 4 (by rfl) ⟨206166, by rfl⟩ : syracuseStep 2199109 = 412333) (by norm_num)
theorem B2199221 : Blo 868566 2199221 := bbase (se 5 (by rfl) ⟨103088, by rfl⟩ : syracuseStep 2199221 = 206177) (by norm_num)
theorem B2789093 : Blo 868566 2789093 := bbase (se 4 (by rfl) ⟨261477, by rfl⟩ : syracuseStep 2789093 = 522955) (by norm_num)
theorem B2199413 : Blo 868566 2199413 := bbase (se 5 (by rfl) ⟨103097, by rfl⟩ : syracuseStep 2199413 = 206195) (by norm_num)
theorem B2723701 : Blo 868566 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B1675253 : Blo 868566 1675253 := bbase (se 5 (by rfl) ⟨78527, by rfl⟩ : syracuseStep 1675253 = 157055) (by norm_num)
theorem B2199757 : Blo 868566 2199757 := bbase (se 3 (by rfl) ⟨412454, by rfl⟩ : syracuseStep 2199757 = 824909) (by norm_num)
theorem B2199869 : Blo 868566 2199869 := bbase (se 3 (by rfl) ⟨412475, by rfl⟩ : syracuseStep 2199869 = 824951) (by norm_num)
theorem B954761 : Blo 868566 954761 := bbase (se 2 (by rfl) ⟨358035, by rfl⟩ : syracuseStep 954761 = 716071) (by norm_num)
theorem B2200061 : Blo 868566 2200061 := bbase (se 3 (by rfl) ⟨412511, by rfl⟩ : syracuseStep 2200061 = 825023) (by norm_num)
theorem B11932181 : Blo 868566 11932181 := bbase (se 6 (by rfl) ⟨279660, by rfl⟩ : syracuseStep 11932181 = 559321) (by norm_num)
theorem B2232893 : Blo 868566 2232893 := bbase (se 3 (by rfl) ⟨418667, by rfl⟩ : syracuseStep 2232893 = 837335) (by norm_num)
theorem B12554837 : Blo 868566 12554837 := bbase (se 8 (by rfl) ⟨73563, by rfl⟩ : syracuseStep 12554837 = 147127) (by norm_num)
theorem B3347045 : Blo 868566 3347045 := bbase (se 4 (by rfl) ⟨313785, by rfl⟩ : syracuseStep 3347045 = 627571) (by norm_num)
theorem B5083829 : Blo 868566 5083829 := bbase (se 5 (by rfl) ⟨238304, by rfl⟩ : syracuseStep 5083829 = 476609) (by norm_num)
theorem B1118929 : Blo 868566 1118929 := bbase (se 2 (by rfl) ⟨419598, by rfl⟩ : syracuseStep 1118929 = 839197) (by norm_num)
theorem B2200405 : Blo 868566 2200405 := bbase (se 9 (by rfl) ⟨6446, by rfl⟩ : syracuseStep 2200405 = 12893) (by norm_num)
theorem B2200517 : Blo 868566 2200517 := bbase (se 4 (by rfl) ⟨206298, by rfl⟩ : syracuseStep 2200517 = 412597) (by norm_num)
theorem B2200709 : Blo 868566 2200709 := bbase (se 4 (by rfl) ⟨206316, by rfl⟩ : syracuseStep 2200709 = 412633) (by norm_num)
theorem B1119377 : Blo 868566 1119377 := bbase (se 2 (by rfl) ⟨419766, by rfl⟩ : syracuseStep 1119377 = 839533) (by norm_num)
theorem B4461925 : Blo 868566 4461925 := bbase (se 4 (by rfl) ⟨418305, by rfl⟩ : syracuseStep 4461925 = 836611) (by norm_num)
theorem B2201053 : Blo 868566 2201053 := bbase (se 3 (by rfl) ⟨412697, by rfl⟩ : syracuseStep 2201053 = 825395) (by norm_num)
theorem B2201165 : Blo 868566 2201165 := bbase (se 3 (by rfl) ⟨412718, by rfl⟩ : syracuseStep 2201165 = 825437) (by norm_num)
theorem B2201357 : Blo 868566 2201357 := bbase (se 3 (by rfl) ⟨412754, by rfl⟩ : syracuseStep 2201357 = 825509) (by norm_num)
theorem B1677133 : Blo 868566 1677133 := bbase (se 3 (by rfl) ⟨314462, by rfl⟩ : syracuseStep 1677133 = 628925) (by norm_num)
theorem B3774293 : Blo 868566 3774293 := bbase (se 9 (by rfl) ⟨11057, by rfl⟩ : syracuseStep 3774293 = 22115) (by norm_num)
theorem B3774485 : Blo 868566 3774485 := bbase (se 6 (by rfl) ⟨88464, by rfl⟩ : syracuseStep 3774485 = 176929) (by norm_num)
theorem B2201701 : Blo 868566 2201701 := bbase (se 4 (by rfl) ⟨206409, by rfl⟩ : syracuseStep 2201701 = 412819) (by norm_num)
theorem B2201813 : Blo 868566 2201813 := bbase (se 7 (by rfl) ⟨25802, by rfl⟩ : syracuseStep 2201813 = 51605) (by norm_num)
theorem B2202005 : Blo 868566 2202005 := bbase (se 6 (by rfl) ⟨51609, by rfl⟩ : syracuseStep 2202005 = 103219) (by norm_num)
theorem B3578309 : Blo 868566 3578309 := bbase (se 4 (by rfl) ⟨335466, by rfl⟩ : syracuseStep 3578309 = 670933) (by norm_num)
theorem B4463237 : Blo 868566 4463237 := bbase (se 4 (by rfl) ⟨418428, by rfl⟩ : syracuseStep 4463237 = 836857) (by norm_num)
theorem B2202349 : Blo 868566 2202349 := bbase (se 3 (by rfl) ⟨412940, by rfl⟩ : syracuseStep 2202349 = 825881) (by norm_num)
theorem B4397813 : Blo 868566 4397813 := bbase (se 5 (by rfl) ⟨206147, by rfl⟩ : syracuseStep 4397813 = 412295) (by norm_num)
theorem B2792245 : Blo 868566 2792245 := bbase (se 5 (by rfl) ⟨130886, by rfl⟩ : syracuseStep 2792245 = 261773) (by norm_num)
theorem B2202461 : Blo 868566 2202461 := bbase (se 3 (by rfl) ⟨412961, by rfl⟩ : syracuseStep 2202461 = 825923) (by norm_num)
theorem B20126677 : Blo 868566 20126677 := bbase (se 7 (by rfl) ⟨235859, by rfl⟩ : syracuseStep 20126677 = 471719) (by norm_num)
theorem B2202653 : Blo 868566 2202653 := bbase (se 3 (by rfl) ⟨412997, by rfl⟩ : syracuseStep 2202653 = 825995) (by norm_num)
theorem B990481 : Blo 868566 990481 := bbase (se 2 (by rfl) ⟨371430, by rfl⟩ : syracuseStep 990481 = 742861) (by norm_num)
theorem B2235725 : Blo 868566 2235725 := bbase (se 3 (by rfl) ⟨419198, by rfl⟩ : syracuseStep 2235725 = 838397) (by norm_num)
theorem B2202997 : Blo 868566 2202997 := bbase (se 5 (by rfl) ⟨103265, by rfl⟩ : syracuseStep 2202997 = 206531) (by norm_num)
theorem B2203109 : Blo 868566 2203109 := bbase (se 4 (by rfl) ⟨206541, by rfl⟩ : syracuseStep 2203109 = 413083) (by norm_num)
theorem B2203301 : Blo 868566 2203301 := bbase (se 4 (by rfl) ⟨206559, by rfl⟩ : syracuseStep 2203301 = 413119) (by norm_num)
theorem B2203645 : Blo 868566 2203645 := bbase (se 3 (by rfl) ⟨413183, by rfl⟩ : syracuseStep 2203645 = 826367) (by norm_num)
theorem B4399109 : Blo 868566 4399109 := bbase (se 4 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 4399109 = 824833) (by norm_num)
theorem B1450037 : Blo 868566 1450037 := bbase (se 5 (by rfl) ⟨67970, by rfl⟩ : syracuseStep 1450037 = 135941) (by norm_num)
theorem B2203757 : Blo 868566 2203757 := bbase (se 3 (by rfl) ⟨413204, by rfl⟩ : syracuseStep 2203757 = 826409) (by norm_num)
theorem B9412757 : Blo 868566 9412757 := bbase (se 6 (by rfl) ⟨220611, by rfl⟩ : syracuseStep 9412757 = 441223) (by norm_num)
theorem B5578901 : Blo 868566 5578901 := bbase (se 6 (by rfl) ⟨130755, by rfl⟩ : syracuseStep 5578901 = 261511) (by norm_num)
theorem B2203949 : Blo 868566 2203949 := bbase (se 3 (by rfl) ⟨413240, by rfl⟩ : syracuseStep 2203949 = 826481) (by norm_num)
theorem B1810765 : Blo 868566 1810765 := bbase (se 3 (by rfl) ⟨339518, by rfl⟩ : syracuseStep 1810765 = 679037) (by norm_num)
theorem B2204293 : Blo 868566 2204293 := bbase (se 4 (by rfl) ⟨206652, by rfl⟩ : syracuseStep 2204293 = 413305) (by norm_num)
theorem B2204405 : Blo 868566 2204405 := bbase (se 5 (by rfl) ⟨103331, by rfl⟩ : syracuseStep 2204405 = 206663) (by norm_num)
theorem B5022485 : Blo 868566 5022485 := bbase (se 6 (by rfl) ⟨117714, by rfl⟩ : syracuseStep 5022485 = 235429) (by norm_num)
theorem B1254269 : Blo 868566 1254269 := bbase (se 3 (by rfl) ⟨235175, by rfl⟩ : syracuseStep 1254269 = 470351) (by norm_num)
theorem B4957109 : Blo 868566 4957109 := bbase (se 5 (by rfl) ⟨232364, by rfl⟩ : syracuseStep 4957109 = 464729) (by norm_num)
theorem B2204597 : Blo 868566 2204597 := bbase (se 5 (by rfl) ⟨103340, by rfl⟩ : syracuseStep 2204597 = 206681) (by norm_num)
theorem B7939093 : Blo 868566 7939093 := bbase (se 6 (by rfl) ⟨186072, by rfl⟩ : syracuseStep 7939093 = 372145) (by norm_num)
theorem B5022805 : Blo 868566 5022805 := bbase (se 8 (by rfl) ⟨29430, by rfl⟩ : syracuseStep 5022805 = 58861) (by norm_num)
theorem B3712229 : Blo 868566 3712229 := bbase (se 4 (by rfl) ⟨348021, by rfl⟩ : syracuseStep 3712229 = 696043) (by norm_num)
theorem B2204941 : Blo 868566 2204941 := bbase (se 3 (by rfl) ⟨413426, by rfl⟩ : syracuseStep 2204941 = 826853) (by norm_num)
theorem B4400405 : Blo 868566 4400405 := bbase (se 6 (by rfl) ⟨103134, by rfl⟩ : syracuseStep 4400405 = 206269) (by norm_num)
theorem B2827541 : Blo 868566 2827541 := bbase (se 6 (by rfl) ⟨66270, by rfl⟩ : syracuseStep 2827541 = 132541) (by norm_num)
theorem B2205053 : Blo 868566 2205053 := bbase (se 3 (by rfl) ⟨413447, by rfl⟩ : syracuseStep 2205053 = 826895) (by norm_num)
theorem B16983445 : Blo 868566 16983445 := bbase (se 6 (by rfl) ⟨398049, by rfl⟩ : syracuseStep 16983445 = 796099) (by norm_num)
theorem B2205245 : Blo 868566 2205245 := bbase (se 3 (by rfl) ⟨413483, by rfl⟩ : syracuseStep 2205245 = 826967) (by norm_num)
theorem B2795077 : Blo 868566 2795077 := bbase (se 4 (by rfl) ⟨262038, by rfl⟩ : syracuseStep 2795077 = 524077) (by norm_num)
theorem B2795141 : Blo 868566 2795141 := bbase (se 4 (by rfl) ⟨262044, by rfl⟩ : syracuseStep 2795141 = 524089) (by norm_num)
theorem B2238293 : Blo 868566 2238293 := bbase (se 9 (by rfl) ⟨6557, by rfl⟩ : syracuseStep 2238293 = 13115) (by norm_num)
theorem B927613 : Blo 868566 927613 := bbase (se 3 (by rfl) ⟨173927, by rfl⟩ : syracuseStep 927613 = 347855) (by norm_num)
theorem B2205589 : Blo 868566 2205589 := bbase (se 6 (by rfl) ⟨51693, by rfl⟩ : syracuseStep 2205589 = 103387) (by norm_num)
theorem B2205701 : Blo 868566 2205701 := bbase (se 4 (by rfl) ⟨206784, by rfl⟩ : syracuseStep 2205701 = 413569) (by norm_num)
theorem B8366165 : Blo 868566 8366165 := bbase (se 8 (by rfl) ⟨49020, by rfl⟩ : syracuseStep 8366165 = 98041) (by norm_num)
theorem B4958293 : Blo 868566 4958293 := bbase (se 8 (by rfl) ⟨29052, by rfl⟩ : syracuseStep 4958293 = 58105) (by norm_num)
theorem B927865 : Blo 868566 927865 := bbase (se 2 (by rfl) ⟨347949, by rfl⟩ : syracuseStep 927865 = 695899) (by norm_num)
theorem B927869 : Blo 868566 927869 := bbase (se 3 (by rfl) ⟨173975, by rfl⟩ : syracuseStep 927869 = 347951) (by norm_num)
theorem B2205893 : Blo 868566 2205893 := bbase (se 4 (by rfl) ⟨206802, by rfl⟩ : syracuseStep 2205893 = 413605) (by norm_num)
theorem B1649173 : Blo 868566 1649173 := bbase (se 6 (by rfl) ⟨38652, by rfl⟩ : syracuseStep 1649173 = 77305) (by norm_num)
theorem B2206237 : Blo 868566 2206237 := bbase (se 3 (by rfl) ⟨413669, by rfl⟩ : syracuseStep 2206237 = 827339) (by norm_num)
theorem B4401701 : Blo 868566 4401701 := bbase (se 4 (by rfl) ⟨412659, by rfl⟩ : syracuseStep 4401701 = 825319) (by norm_num)
theorem B2206349 : Blo 868566 2206349 := bbase (se 3 (by rfl) ⟨413690, by rfl⟩ : syracuseStep 2206349 = 827381) (by norm_num)
theorem B1649317 : Blo 868566 1649317 := bbase (se 4 (by rfl) ⟨154623, by rfl⟩ : syracuseStep 1649317 = 309247) (by norm_num)
theorem B928433 : Blo 868566 928433 := bbase (se 2 (by rfl) ⟨348162, by rfl⟩ : syracuseStep 928433 = 696325) (by norm_num)
theorem B1649477 : Blo 868566 1649477 := bbase (se 4 (by rfl) ⟨154638, by rfl⟩ : syracuseStep 1649477 = 309277) (by norm_num)
theorem B2206541 : Blo 868566 2206541 := bbase (se 3 (by rfl) ⟨413726, by rfl⟩ : syracuseStep 2206541 = 827453) (by norm_num)
theorem B928621 : Blo 868566 928621 := bbase (se 3 (by rfl) ⟨174116, by rfl⟩ : syracuseStep 928621 = 348233) (by norm_num)
theorem B1649621 : Blo 868566 1649621 := bbase (se 7 (by rfl) ⟨19331, by rfl⟩ : syracuseStep 1649621 = 38663) (by norm_num)
theorem B3714005 : Blo 868566 3714005 := bbase (se 7 (by rfl) ⟨43523, by rfl⟩ : syracuseStep 3714005 = 87047) (by norm_num)
theorem B2206885 : Blo 868566 2206885 := bbase (se 4 (by rfl) ⟨206895, by rfl⟩ : syracuseStep 2206885 = 413791) (by norm_num)
theorem B3714245 : Blo 868566 3714245 := bbase (se 4 (by rfl) ⟨348210, by rfl⟩ : syracuseStep 3714245 = 696421) (by norm_num)
theorem B1649909 : Blo 868566 1649909 := bbase (se 5 (by rfl) ⟨77339, by rfl⟩ : syracuseStep 1649909 = 154679) (by norm_num)
theorem B2206997 : Blo 868566 2206997 := bbase (se 6 (by rfl) ⟨51726, by rfl⟩ : syracuseStep 2206997 = 103453) (by norm_num)
theorem B1650061 : Blo 868566 1650061 := bbase (se 3 (by rfl) ⟨309386, by rfl⟩ : syracuseStep 1650061 = 618773) (by norm_num)
theorem B2207189 : Blo 868566 2207189 := bbase (se 7 (by rfl) ⟨25865, by rfl⟩ : syracuseStep 2207189 = 51731) (by norm_num)
theorem B929441 : Blo 868566 929441 := bbase (se 2 (by rfl) ⟨348540, by rfl⟩ : syracuseStep 929441 = 697081) (by norm_num)
theorem B1650365 : Blo 868566 1650365 := bbase (se 3 (by rfl) ⟨309443, by rfl⟩ : syracuseStep 1650365 = 618887) (by norm_num)
theorem B1191629 : Blo 868566 1191629 := bbase (se 3 (by rfl) ⟨223430, by rfl⟩ : syracuseStep 1191629 = 446861) (by norm_num)
theorem B6598421 : Blo 868566 6598421 := bbase (se 6 (by rfl) ⟨154650, by rfl⟩ : syracuseStep 6598421 = 309301) (by norm_num)
theorem B2207533 : Blo 868566 2207533 := bbase (se 3 (by rfl) ⟨413912, by rfl⟩ : syracuseStep 2207533 = 827825) (by norm_num)
theorem B4402997 : Blo 868566 4402997 := bbase (se 5 (by rfl) ⟨206390, by rfl⟩ : syracuseStep 4402997 = 412781) (by norm_num)
theorem B2207645 : Blo 868566 2207645 := bbase (se 3 (by rfl) ⟨413933, by rfl⟩ : syracuseStep 2207645 = 827867) (by norm_num)
theorem B4960277 : Blo 868566 4960277 := bbase (se 6 (by rfl) ⟨116256, by rfl⟩ : syracuseStep 4960277 = 232513) (by norm_num)
theorem B929885 : Blo 868566 929885 := bbase (se 3 (by rfl) ⟨174353, by rfl⟩ : syracuseStep 929885 = 348707) (by norm_num)
theorem B2207837 : Blo 868566 2207837 := bbase (se 3 (by rfl) ⟨413969, by rfl⟩ : syracuseStep 2207837 = 827939) (by norm_num)
theorem B1061173 : Blo 868566 1061173 := bbase (se 5 (by rfl) ⟨49742, by rfl⟩ : syracuseStep 1061173 = 99485) (by norm_num)
theorem B930133 : Blo 868566 930133 := bbase (se 10 (by rfl) ⟨1362, by rfl⟩ : syracuseStep 930133 = 2725) (by norm_num)
theorem B1651117 : Blo 868566 1651117 := bbase (se 3 (by rfl) ⟨309584, by rfl⟩ : syracuseStep 1651117 = 619169) (by norm_num)
theorem B2208181 : Blo 868566 2208181 := bbase (se 5 (by rfl) ⟨103508, by rfl⟩ : syracuseStep 2208181 = 207017) (by norm_num)
theorem B2208293 : Blo 868566 2208293 := bbase (se 4 (by rfl) ⟨207027, by rfl⟩ : syracuseStep 2208293 = 414055) (by norm_num)
theorem B1651261 : Blo 868566 1651261 := bbase (se 3 (by rfl) ⟨309611, by rfl⟩ : syracuseStep 1651261 = 619223) (by norm_num)
theorem B1651421 : Blo 868566 1651421 := bbase (se 3 (by rfl) ⟨309641, by rfl⟩ : syracuseStep 1651421 = 619283) (by norm_num)
theorem B2208485 : Blo 868566 2208485 := bbase (se 4 (by rfl) ⟨207045, by rfl⟩ : syracuseStep 2208485 = 414091) (by norm_num)
theorem B930565 : Blo 868566 930565 := bbase (se 4 (by rfl) ⟨87240, by rfl⟩ : syracuseStep 930565 = 174481) (by norm_num)
theorem B930637 : Blo 868566 930637 := bbase (se 3 (by rfl) ⟨174494, by rfl⟩ : syracuseStep 930637 = 348989) (by norm_num)
theorem B1651565 : Blo 868566 1651565 := bbase (se 3 (by rfl) ⟨309668, by rfl⟩ : syracuseStep 1651565 = 619337) (by norm_num)
theorem B3978197 : Blo 868566 3978197 := bbase (se 7 (by rfl) ⟨46619, by rfl⟩ : syracuseStep 3978197 = 93239) (by norm_num)
theorem B4404293 : Blo 868566 4404293 := bbase (se 4 (by rfl) ⟨412902, by rfl⟩ : syracuseStep 4404293 = 825805) (by norm_num)
theorem B1487965 : Blo 868566 1487965 := bbase (se 3 (by rfl) ⟨278993, by rfl⟩ : syracuseStep 1487965 = 557987) (by norm_num)
theorem B4174949 : Blo 868566 4174949 := bbase (se 4 (by rfl) ⟨391401, by rfl⟩ : syracuseStep 4174949 = 782803) (by norm_num)
theorem B1651853 : Blo 868566 1651853 := bbase (se 3 (by rfl) ⟨309722, by rfl⟩ : syracuseStep 1651853 = 619445) (by norm_num)
theorem B931009 : Blo 868566 931009 := bbase (se 2 (by rfl) ⟨349128, by rfl⟩ : syracuseStep 931009 = 698257) (by norm_num)
theorem B1652005 : Blo 868566 1652005 := bbase (se 4 (by rfl) ⟨154875, by rfl⟩ : syracuseStep 1652005 = 309751) (by norm_num)
theorem B3716533 : Blo 868566 3716533 := bbase (se 5 (by rfl) ⟨174212, by rfl⟩ : syracuseStep 3716533 = 348425) (by norm_num)
theorem B931385 : Blo 868566 931385 := bbase (se 2 (by rfl) ⟨349269, by rfl⟩ : syracuseStep 931385 = 698539) (by norm_num)
theorem B1652309 : Blo 868566 1652309 := bbase (se 8 (by rfl) ⟨9681, by rfl⟩ : syracuseStep 1652309 = 19363) (by norm_num)
theorem B931457 : Blo 868566 931457 := bbase (se 2 (by rfl) ⟨349296, by rfl⟩ : syracuseStep 931457 = 698593) (by norm_num)
theorem B3356293 : Blo 868566 3356293 := bbase (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) (by norm_num)
theorem B3356453 : Blo 868566 3356453 := bbase (se 4 (by rfl) ⟨314667, by rfl⟩ : syracuseStep 3356453 = 629335) (by norm_num)
theorem B931645 : Blo 868566 931645 := bbase (se 3 (by rfl) ⟨174683, by rfl⟩ : syracuseStep 931645 = 349367) (by norm_num)
theorem B7944277 : Blo 868566 7944277 := bbase (se 8 (by rfl) ⟨46548, by rfl⟩ : syracuseStep 7944277 = 93097) (by norm_num)
theorem B1194085 : Blo 868566 1194085 := bbase (se 4 (by rfl) ⟨111945, by rfl⟩ : syracuseStep 1194085 = 223891) (by norm_num)
theorem B4962485 : Blo 868566 4962485 := bbase (se 5 (by rfl) ⟨232616, by rfl⟩ : syracuseStep 4962485 = 465233) (by norm_num)
theorem B1653061 : Blo 868566 1653061 := bbase (se 4 (by rfl) ⟨154974, by rfl⟩ : syracuseStep 1653061 = 309949) (by norm_num)
theorem B4405589 : Blo 868566 4405589 := bbase (se 10 (by rfl) ⟨6453, by rfl⟩ : syracuseStep 4405589 = 12907) (by norm_num)
theorem B188627285 : Blo 868566 188627285 := bbase (se 10 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 188627285 = 552619) (by norm_num)
theorem B1653205 : Blo 868566 1653205 := bbase (se 7 (by rfl) ⟨19373, by rfl⟩ : syracuseStep 1653205 = 38747) (by norm_num)
theorem B4176373 : Blo 868566 4176373 := bbase (se 5 (by rfl) ⟨195767, by rfl⟩ : syracuseStep 4176373 = 391535) (by norm_num)
theorem B1653365 : Blo 868566 1653365 := bbase (se 5 (by rfl) ⟨77501, by rfl⟩ : syracuseStep 1653365 = 155003) (by norm_num)
theorem B1325749 : Blo 868566 1325749 := bbase (se 5 (by rfl) ⟨62144, by rfl⟩ : syracuseStep 1325749 = 124289) (by norm_num)
theorem B1653509 : Blo 868566 1653509 := bbase (se 4 (by rfl) ⟨155016, by rfl⟩ : syracuseStep 1653509 = 310033) (by norm_num)
theorem B3718021 : Blo 868566 3718021 := bbase (se 4 (by rfl) ⟨348564, by rfl⟩ : syracuseStep 3718021 = 697129) (by norm_num)
theorem B2931605 : Blo 868566 2931605 := bbase (se 6 (by rfl) ⟨68709, by rfl⟩ : syracuseStep 2931605 = 137419) (by norm_num)
theorem B1391509 : Blo 868566 1391509 := bbase (se 6 (by rfl) ⟨32613, by rfl⟩ : syracuseStep 1391509 = 65227) (by norm_num)
theorem B3718037 : Blo 868566 3718037 := bbase (se 6 (by rfl) ⟨87141, by rfl⟩ : syracuseStep 3718037 = 174283) (by norm_num)
theorem B1489909 : Blo 868566 1489909 := bbase (se 5 (by rfl) ⟨69839, by rfl⟩ : syracuseStep 1489909 = 139679) (by norm_num)
theorem B1653797 : Blo 868566 1653797 := bbase (se 4 (by rfl) ⟨155043, by rfl⟩ : syracuseStep 1653797 = 310087) (by norm_num)
theorem B1326181 : Blo 868566 1326181 := bbase (se 4 (by rfl) ⟨124329, by rfl⟩ : syracuseStep 1326181 = 248659) (by norm_num)
theorem B1653949 : Blo 868566 1653949 := bbase (se 3 (by rfl) ⟨310115, by rfl⟩ : syracuseStep 1653949 = 620231) (by norm_num)
theorem B2932037 : Blo 868566 2932037 := bbase (se 4 (by rfl) ⟨274878, by rfl⟩ : syracuseStep 2932037 = 549757) (by norm_num)
theorem B6274421 : Blo 868566 6274421 := bbase (se 5 (by rfl) ⟨294113, by rfl⟩ : syracuseStep 6274421 = 588227) (by norm_num)
theorem B1981829 : Blo 868566 1981829 := bbase (se 4 (by rfl) ⟨185796, by rfl⟩ : syracuseStep 1981829 = 371593) (by norm_num)
theorem B2473429 : Blo 868566 2473429 := bbase (se 7 (by rfl) ⟨28985, by rfl⟩ : syracuseStep 2473429 = 57971) (by norm_num)
theorem B1654253 : Blo 868566 1654253 := bbase (se 3 (by rfl) ⟨310172, by rfl⟩ : syracuseStep 1654253 = 620345) (by norm_num)
theorem B4472309 : Blo 868566 4472309 := bbase (se 5 (by rfl) ⟨209639, by rfl⟩ : syracuseStep 4472309 = 419279) (by norm_num)
theorem B1392157 : Blo 868566 1392157 := bbase (se 3 (by rfl) ⟨261029, by rfl⟩ : syracuseStep 1392157 = 522059) (by norm_num)
theorem B4406885 : Blo 868566 4406885 := bbase (se 4 (by rfl) ⟨413145, by rfl⟩ : syracuseStep 4406885 = 826291) (by norm_num)
theorem B6274709 : Blo 868566 6274709 := bbase (se 6 (by rfl) ⟨147063, by rfl⟩ : syracuseStep 6274709 = 294127) (by norm_num)
theorem B2932469 : Blo 868566 2932469 := bbase (se 5 (by rfl) ⟨137459, by rfl⟩ : syracuseStep 2932469 = 274919) (by norm_num)
theorem B1883917 : Blo 868566 1883917 := bbase (se 3 (by rfl) ⟨353234, by rfl⟩ : syracuseStep 1883917 = 706469) (by norm_num)
theorem B17841941 : Blo 868566 17841941 := bbase (se 6 (by rfl) ⟨418170, by rfl⟩ : syracuseStep 17841941 = 836341) (by norm_num)
theorem B30097493 : Blo 868566 30097493 := bbase (se 8 (by rfl) ⟨176352, by rfl⟩ : syracuseStep 30097493 = 352705) (by norm_num)
theorem B1491029 : Blo 868566 1491029 := bbase (se 8 (by rfl) ⟨8736, by rfl⟩ : syracuseStep 1491029 = 17473) (by norm_num)
theorem B2932901 : Blo 868566 2932901 := bbase (se 4 (by rfl) ⟨274959, by rfl⟩ : syracuseStep 2932901 = 549919) (by norm_num)
theorem B1655005 : Blo 868566 1655005 := bbase (se 3 (by rfl) ⟨310313, by rfl⟩ : syracuseStep 1655005 = 620627) (by norm_num)
theorem B1655149 : Blo 868566 1655149 := bbase (se 3 (by rfl) ⟨310340, by rfl⟩ : syracuseStep 1655149 = 620681) (by norm_num)
theorem B1393085 : Blo 868566 1393085 := bbase (se 3 (by rfl) ⟨261203, by rfl⟩ : syracuseStep 1393085 = 522407) (by norm_num)
theorem B1655309 : Blo 868566 1655309 := bbase (se 3 (by rfl) ⟨310370, by rfl⟩ : syracuseStep 1655309 = 620741) (by norm_num)
theorem B2933333 : Blo 868566 2933333 := bbase (se 8 (by rfl) ⟨17187, by rfl⟩ : syracuseStep 2933333 = 34375) (by norm_num)
theorem B5292661 : Blo 868566 5292661 := bbase (se 5 (by rfl) ⟨248093, by rfl⟩ : syracuseStep 5292661 = 496187) (by norm_num)
theorem B1655453 : Blo 868566 1655453 := bbase (se 3 (by rfl) ⟨310397, by rfl⟩ : syracuseStep 1655453 = 620795) (by norm_num)
theorem B4408181 : Blo 868566 4408181 := bbase (se 5 (by rfl) ⟨206633, by rfl⟩ : syracuseStep 4408181 = 413267) (by norm_num)
theorem B1393541 : Blo 868566 1393541 := bbase (se 4 (by rfl) ⟨130644, by rfl⟩ : syracuseStep 1393541 = 261289) (by norm_num)
theorem B1655741 : Blo 868566 1655741 := bbase (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) (by norm_num)
theorem B2933765 : Blo 868566 2933765 := bbase (se 4 (by rfl) ⟨275040, by rfl⟩ : syracuseStep 2933765 = 550081) (by norm_num)
theorem B1655893 : Blo 868566 1655893 := bbase (se 8 (by rfl) ⟨9702, by rfl⟩ : syracuseStep 1655893 = 19405) (by norm_num)
theorem B1885285 : Blo 868566 1885285 := bbase (se 4 (by rfl) ⟨176745, by rfl⟩ : syracuseStep 1885285 = 353491) (by norm_num)
theorem B3720293 : Blo 868566 3720293 := bbase (se 4 (by rfl) ⟨348777, by rfl⟩ : syracuseStep 3720293 = 697555) (by norm_num)
theorem B1885421 : Blo 868566 1885421 := bbase (se 3 (by rfl) ⟨353516, by rfl⟩ : syracuseStep 1885421 = 707033) (by norm_num)
theorem B1983733 : Blo 868566 1983733 := bbase (se 5 (by rfl) ⟨92987, by rfl⟩ : syracuseStep 1983733 = 185975) (by norm_num)
theorem B1983845 : Blo 868566 1983845 := bbase (se 4 (by rfl) ⟨185985, by rfl⟩ : syracuseStep 1983845 = 371971) (by norm_num)
theorem B1656197 : Blo 868566 1656197 := bbase (se 4 (by rfl) ⟨155268, by rfl⟩ : syracuseStep 1656197 = 310537) (by norm_num)
theorem B2934197 : Blo 868566 2934197 := bbase (se 5 (by rfl) ⟨137540, by rfl⟩ : syracuseStep 2934197 = 275081) (by norm_num)
theorem B1099433 : Blo 868566 1099433 := bbase (se 2 (by rfl) ⟨412287, by rfl⟩ : syracuseStep 1099433 = 824575) (by norm_num)
theorem B4703957 : Blo 868566 4703957 := bbase (se 7 (by rfl) ⟨55124, by rfl⟩ : syracuseStep 4703957 = 110249) (by norm_num)
theorem B1099489 : Blo 868566 1099489 := bbase (se 2 (by rfl) ⟨412308, by rfl⟩ : syracuseStep 1099489 = 824617) (by norm_num)
theorem B1099585 : Blo 868566 1099585 := bbase (se 2 (by rfl) ⟨412344, by rfl⟩ : syracuseStep 1099585 = 824689) (by norm_num)
theorem B4245317 : Blo 868566 4245317 := bbase (se 4 (by rfl) ⟨397998, by rfl⟩ : syracuseStep 4245317 = 795997) (by norm_num)
theorem B2934629 : Blo 868566 2934629 := bbase (se 4 (by rfl) ⟨275121, by rfl⟩ : syracuseStep 2934629 = 550243) (by norm_num)
theorem B1099757 : Blo 868566 1099757 := bbase (se 3 (by rfl) ⟨206204, by rfl⟩ : syracuseStep 1099757 = 412409) (by norm_num)
theorem B1099813 : Blo 868566 1099813 := bbase (se 4 (by rfl) ⟨103107, by rfl⟩ : syracuseStep 1099813 = 206215) (by norm_num)
theorem B1099909 : Blo 868566 1099909 := bbase (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) (by norm_num)
theorem B4409477 : Blo 868566 4409477 := bbase (se 4 (by rfl) ⟨413388, by rfl⟩ : syracuseStep 4409477 = 826777) (by norm_num)
theorem B1591501 : Blo 868566 1591501 := bbase (se 3 (by rfl) ⟨298406, by rfl⟩ : syracuseStep 1591501 = 596813) (by norm_num)
theorem B2476277 : Blo 868566 2476277 := bbase (se 5 (by rfl) ⟨116075, by rfl⟩ : syracuseStep 2476277 = 232151) (by norm_num)
theorem B1394957 : Blo 868566 1394957 := bbase (se 3 (by rfl) ⟨261554, by rfl⟩ : syracuseStep 1394957 = 523109) (by norm_num)
theorem B2935061 : Blo 868566 2935061 := bbase (se 6 (by rfl) ⟨68790, by rfl⟩ : syracuseStep 2935061 = 137581) (by norm_num)
theorem B2509093 : Blo 868566 2509093 := bbase (se 4 (by rfl) ⟨235227, by rfl⟩ : syracuseStep 2509093 = 470455) (by norm_num)
theorem B1100081 : Blo 868566 1100081 := bbase (se 2 (by rfl) ⟨412530, by rfl⟩ : syracuseStep 1100081 = 825061) (by norm_num)
theorem B1100137 : Blo 868566 1100137 := bbase (se 2 (by rfl) ⟨412551, by rfl⟩ : syracuseStep 1100137 = 825103) (by norm_num)
theorem B1100233 : Blo 868566 1100233 := bbase (se 2 (by rfl) ⟨412587, by rfl⟩ : syracuseStep 1100233 = 825175) (by norm_num)
theorem B1395181 : Blo 868566 1395181 := bbase (se 3 (by rfl) ⟨261596, by rfl⟩ : syracuseStep 1395181 = 523193) (by norm_num)
theorem B1100405 : Blo 868566 1100405 := bbase (se 5 (by rfl) ⟨51581, by rfl⟩ : syracuseStep 1100405 = 103163) (by norm_num)
theorem B1100461 : Blo 868566 1100461 := bbase (se 3 (by rfl) ⟨206336, by rfl⟩ : syracuseStep 1100461 = 412673) (by norm_num)
theorem B2935493 : Blo 868566 2935493 := bbase (se 4 (by rfl) ⟨275202, by rfl⟩ : syracuseStep 2935493 = 550405) (by norm_num)
theorem B1100557 : Blo 868566 1100557 := bbase (se 3 (by rfl) ⟨206354, by rfl⟩ : syracuseStep 1100557 = 412709) (by norm_num)
theorem B7064405 : Blo 868566 7064405 := bbase (se 9 (by rfl) ⟨20696, by rfl⟩ : syracuseStep 7064405 = 41393) (by norm_num)
theorem B9423701 : Blo 868566 9423701 := bbase (se 9 (by rfl) ⟨27608, by rfl⟩ : syracuseStep 9423701 = 55217) (by norm_num)
theorem B1100729 : Blo 868566 1100729 := bbase (se 2 (by rfl) ⟨412773, by rfl⟩ : syracuseStep 1100729 = 825547) (by norm_num)
theorem B1100785 : Blo 868566 1100785 := bbase (se 2 (by rfl) ⟨412794, by rfl⟩ : syracuseStep 1100785 = 825589) (by norm_num)
theorem B1100881 : Blo 868566 1100881 := bbase (se 2 (by rfl) ⟨412830, by rfl⟩ : syracuseStep 1100881 = 825661) (by norm_num)
theorem B2935925 : Blo 868566 2935925 := bbase (se 5 (by rfl) ⟨137621, by rfl⟩ : syracuseStep 2935925 = 275243) (by norm_num)
theorem B1101053 : Blo 868566 1101053 := bbase (se 3 (by rfl) ⟨206447, by rfl⟩ : syracuseStep 1101053 = 412895) (by norm_num)
theorem B3525893 : Blo 868566 3525893 := bbase (se 4 (by rfl) ⟨330552, by rfl⟩ : syracuseStep 3525893 = 661105) (by norm_num)
theorem B1101109 : Blo 868566 1101109 := bbase (se 5 (by rfl) ⟨51614, by rfl⟩ : syracuseStep 1101109 = 103229) (by norm_num)
theorem B6606197 : Blo 868566 6606197 := bbase (se 5 (by rfl) ⟨309665, by rfl⟩ : syracuseStep 6606197 = 619331) (by norm_num)
theorem B2477461 : Blo 868566 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B1101205 : Blo 868566 1101205 := bbase (se 6 (by rfl) ⟨25809, by rfl⟩ : syracuseStep 1101205 = 51619) (by norm_num)
theorem B4410773 : Blo 868566 4410773 := bbase (se 6 (by rfl) ⟨103377, by rfl⟩ : syracuseStep 4410773 = 206755) (by norm_num)
theorem B2936357 : Blo 868566 2936357 := bbase (se 4 (by rfl) ⟨275283, by rfl⟩ : syracuseStep 2936357 = 550567) (by norm_num)
theorem B2477621 : Blo 868566 2477621 := bbase (se 5 (by rfl) ⟨116138, by rfl⟩ : syracuseStep 2477621 = 232277) (by norm_num)
theorem B1101377 : Blo 868566 1101377 := bbase (se 2 (by rfl) ⟨413016, by rfl⟩ : syracuseStep 1101377 = 826033) (by norm_num)
theorem B1101433 : Blo 868566 1101433 := bbase (se 2 (by rfl) ⟨413037, by rfl⟩ : syracuseStep 1101433 = 826075) (by norm_num)
theorem B2117285 : Blo 868566 2117285 := bbase (se 4 (by rfl) ⟨198495, by rfl⟩ : syracuseStep 2117285 = 396991) (by norm_num)
theorem B1101529 : Blo 868566 1101529 := bbase (se 2 (by rfl) ⟨413073, by rfl⟩ : syracuseStep 1101529 = 826147) (by norm_num)
theorem B2477861 : Blo 868566 2477861 := bbase (se 4 (by rfl) ⟨232299, by rfl⟩ : syracuseStep 2477861 = 464599) (by norm_num)
theorem B1396597 : Blo 868566 1396597 := bbase (se 5 (by rfl) ⟨65465, by rfl⟩ : syracuseStep 1396597 = 130931) (by norm_num)
theorem B1101701 : Blo 868566 1101701 := bbase (se 4 (by rfl) ⟨103284, by rfl⟩ : syracuseStep 1101701 = 206569) (by norm_num)
theorem B1101757 : Blo 868566 1101757 := bbase (se 3 (by rfl) ⟨206579, by rfl⟩ : syracuseStep 1101757 = 413159) (by norm_num)
theorem B2936789 : Blo 868566 2936789 := bbase (se 7 (by rfl) ⟨34415, by rfl⟩ : syracuseStep 2936789 = 68831) (by norm_num)
theorem B2478053 : Blo 868566 2478053 := bbase (se 4 (by rfl) ⟨232317, by rfl⟩ : syracuseStep 2478053 = 464635) (by norm_num)
theorem B1101853 : Blo 868566 1101853 := bbase (se 3 (by rfl) ⟨206597, by rfl⟩ : syracuseStep 1101853 = 413195) (by norm_num)
theorem B2117749 : Blo 868566 2117749 := bbase (se 5 (by rfl) ⟨99269, by rfl⟩ : syracuseStep 2117749 = 198539) (by norm_num)
theorem B1396853 : Blo 868566 1396853 := bbase (se 5 (by rfl) ⟨65477, by rfl⟩ : syracuseStep 1396853 = 130955) (by norm_num)
theorem B1102025 : Blo 868566 1102025 := bbase (se 2 (by rfl) ⟨413259, by rfl⟩ : syracuseStep 1102025 = 826519) (by norm_num)
theorem B1102081 : Blo 868566 1102081 := bbase (se 2 (by rfl) ⟨413280, by rfl⟩ : syracuseStep 1102081 = 826561) (by norm_num)
theorem B1397045 : Blo 868566 1397045 := bbase (se 5 (by rfl) ⟨65486, by rfl⟩ : syracuseStep 1397045 = 130973) (by norm_num)
theorem B1102177 : Blo 868566 1102177 := bbase (se 2 (by rfl) ⟨413316, by rfl⟩ : syracuseStep 1102177 = 826633) (by norm_num)
theorem B2937221 : Blo 868566 2937221 := bbase (se 4 (by rfl) ⟨275364, by rfl⟩ : syracuseStep 2937221 = 550729) (by norm_num)
theorem B1855909 : Blo 868566 1855909 := bbase (se 4 (by rfl) ⟨173991, by rfl⟩ : syracuseStep 1855909 = 347983) (by norm_num)
theorem B1954277 : Blo 868566 1954277 := bbase (se 4 (by rfl) ⟨183213, by rfl⟩ : syracuseStep 1954277 = 366427) (by norm_num)
theorem B1102349 : Blo 868566 1102349 := bbase (se 3 (by rfl) ⟨206690, by rfl⟩ : syracuseStep 1102349 = 413381) (by norm_num)
theorem B1856029 : Blo 868566 1856029 := bbase (se 3 (by rfl) ⟨348005, by rfl⟩ : syracuseStep 1856029 = 696011) (by norm_num)
theorem B1954349 : Blo 868566 1954349 := bbase (se 3 (by rfl) ⟨366440, by rfl⟩ : syracuseStep 1954349 = 732881) (by norm_num)
theorem B3527221 : Blo 868566 3527221 := bbase (se 5 (by rfl) ⟨165338, by rfl⟩ : syracuseStep 3527221 = 330677) (by norm_num)
theorem B1102405 : Blo 868566 1102405 := bbase (se 4 (by rfl) ⟨103350, by rfl⟩ : syracuseStep 1102405 = 206701) (by norm_num)
theorem B1954421 : Blo 868566 1954421 := bbase (se 5 (by rfl) ⟨91613, by rfl⟩ : syracuseStep 1954421 = 183227) (by norm_num)
theorem B1102501 : Blo 868566 1102501 := bbase (se 4 (by rfl) ⟨103359, by rfl⟩ : syracuseStep 1102501 = 206719) (by norm_num)
theorem B4412069 : Blo 868566 4412069 := bbase (se 4 (by rfl) ⟨413631, by rfl⟩ : syracuseStep 4412069 = 827263) (by norm_num)
theorem B1954493 : Blo 868566 1954493 := bbase (se 3 (by rfl) ⟨366467, by rfl⟩ : syracuseStep 1954493 = 732935) (by norm_num)
theorem B1954565 : Blo 868566 1954565 := bbase (se 4 (by rfl) ⟨183240, by rfl⟩ : syracuseStep 1954565 = 366481) (by norm_num)
theorem B1856285 : Blo 868566 1856285 := bbase (se 3 (by rfl) ⟨348053, by rfl⟩ : syracuseStep 1856285 = 696107) (by norm_num)
theorem B2937653 : Blo 868566 2937653 := bbase (se 5 (by rfl) ⟨137702, by rfl⟩ : syracuseStep 2937653 = 275405) (by norm_num)
theorem B3298117 : Blo 868566 3298117 := bbase (se 4 (by rfl) ⟨309198, by rfl⟩ : syracuseStep 3298117 = 618397) (by norm_num)
theorem B1954637 : Blo 868566 1954637 := bbase (se 3 (by rfl) ⟨366494, by rfl⟩ : syracuseStep 1954637 = 732989) (by norm_num)
theorem B1102673 : Blo 868566 1102673 := bbase (se 2 (by rfl) ⟨413502, by rfl⟩ : syracuseStep 1102673 = 827005) (by norm_num)
theorem B67982165 : Blo 868566 67982165 := bbase (se 9 (by rfl) ⟨199166, by rfl⟩ : syracuseStep 67982165 = 398333) (by norm_num)
theorem B1102729 : Blo 868566 1102729 := bbase (se 2 (by rfl) ⟨413523, by rfl⟩ : syracuseStep 1102729 = 827047) (by norm_num)
theorem B1954709 : Blo 868566 1954709 := bbase (se 6 (by rfl) ⟨45813, by rfl⟩ : syracuseStep 1954709 = 91627) (by norm_num)
theorem B2479045 : Blo 868566 2479045 := bbase (se 4 (by rfl) ⟨232410, by rfl⟩ : syracuseStep 2479045 = 464821) (by norm_num)
theorem B1954781 : Blo 868566 1954781 := bbase (se 3 (by rfl) ⟨366521, by rfl⟩ : syracuseStep 1954781 = 733043) (by norm_num)
theorem B1102825 : Blo 868566 1102825 := bbase (se 2 (by rfl) ⟨413559, by rfl⟩ : syracuseStep 1102825 = 827119) (by norm_num)
theorem B1954853 : Blo 868566 1954853 := bbase (se 4 (by rfl) ⟨183267, by rfl⟩ : syracuseStep 1954853 = 366535) (by norm_num)
theorem B3724325 : Blo 868566 3724325 := bbase (se 4 (by rfl) ⟨349155, by rfl⟩ : syracuseStep 3724325 = 698311) (by norm_num)
theorem B1954925 : Blo 868566 1954925 := bbase (se 3 (by rfl) ⟨366548, by rfl⟩ : syracuseStep 1954925 = 733097) (by norm_num)
theorem B3298421 : Blo 868566 3298421 := bbase (se 5 (by rfl) ⟨154613, by rfl⟩ : syracuseStep 3298421 = 309227) (by norm_num)
theorem B1102997 : Blo 868566 1102997 := bbase (se 6 (by rfl) ⟨25851, by rfl⟩ : syracuseStep 1102997 = 51703) (by norm_num)
theorem B1954997 : Blo 868566 1954997 := bbase (se 5 (by rfl) ⟨91640, by rfl⟩ : syracuseStep 1954997 = 183281) (by norm_num)
theorem B1103053 : Blo 868566 1103053 := bbase (se 3 (by rfl) ⟨206822, by rfl⟩ : syracuseStep 1103053 = 413645) (by norm_num)
theorem B4183253 : Blo 868566 4183253 := bbase (se 7 (by rfl) ⟨49022, by rfl⟩ : syracuseStep 4183253 = 98045) (by norm_num)
theorem B2938085 : Blo 868566 2938085 := bbase (se 4 (by rfl) ⟨275445, by rfl⟩ : syracuseStep 2938085 = 550891) (by norm_num)
theorem B1955069 : Blo 868566 1955069 := bbase (se 3 (by rfl) ⟨366575, by rfl⟩ : syracuseStep 1955069 = 733151) (by norm_num)
theorem B1103149 : Blo 868566 1103149 := bbase (se 3 (by rfl) ⟨206840, by rfl⟩ : syracuseStep 1103149 = 413681) (by norm_num)
theorem B1955141 : Blo 868566 1955141 := bbase (se 4 (by rfl) ⟨183294, by rfl⟩ : syracuseStep 1955141 = 366589) (by norm_num)
theorem B1955213 : Blo 868566 1955213 := bbase (se 3 (by rfl) ⟨366602, by rfl⟩ : syracuseStep 1955213 = 733205) (by norm_num)
theorem B1791389 : Blo 868566 1791389 := bbase (se 3 (by rfl) ⟨335885, by rfl⟩ : syracuseStep 1791389 = 671771) (by norm_num)
theorem B1955285 : Blo 868566 1955285 := bbase (se 7 (by rfl) ⟨22913, by rfl⟩ : syracuseStep 1955285 = 45827) (by norm_num)
theorem B1103321 : Blo 868566 1103321 := bbase (se 2 (by rfl) ⟨413745, by rfl⟩ : syracuseStep 1103321 = 827491) (by norm_num)
theorem B1103377 : Blo 868566 1103377 := bbase (se 2 (by rfl) ⟨413766, by rfl⟩ : syracuseStep 1103377 = 827533) (by norm_num)
theorem B1955357 : Blo 868566 1955357 := bbase (se 3 (by rfl) ⟨366629, by rfl⟩ : syracuseStep 1955357 = 733259) (by norm_num)
theorem B1955429 : Blo 868566 1955429 := bbase (se 4 (by rfl) ⟨183321, by rfl⟩ : syracuseStep 1955429 = 366643) (by norm_num)
theorem B3135077 : Blo 868566 3135077 := bbase (se 4 (by rfl) ⟨293913, by rfl⟩ : syracuseStep 3135077 = 587827) (by norm_num)
theorem B1103473 : Blo 868566 1103473 := bbase (se 2 (by rfl) ⟨413802, by rfl⟩ : syracuseStep 1103473 = 827605) (by norm_num)
theorem B1857173 : Blo 868566 1857173 := bbase (se 6 (by rfl) ⟨43527, by rfl⟩ : syracuseStep 1857173 = 87055) (by norm_num)
theorem B2938517 : Blo 868566 2938517 := bbase (se 6 (by rfl) ⟨68871, by rfl⟩ : syracuseStep 2938517 = 137743) (by norm_num)
theorem B1955501 : Blo 868566 1955501 := bbase (se 3 (by rfl) ⟨366656, by rfl⟩ : syracuseStep 1955501 = 733313) (by norm_num)
theorem B1955573 : Blo 868566 1955573 := bbase (se 5 (by rfl) ⟨91667, by rfl⟩ : syracuseStep 1955573 = 183335) (by norm_num)
theorem B12048149 : Blo 868566 12048149 := bbase (se 6 (by rfl) ⟨282378, by rfl⟩ : syracuseStep 12048149 = 564757) (by norm_num)
theorem B1103645 : Blo 868566 1103645 := bbase (se 3 (by rfl) ⟨206933, by rfl⟩ : syracuseStep 1103645 = 413867) (by norm_num)
theorem B1988405 : Blo 868566 1988405 := bbase (se 5 (by rfl) ⟨93206, by rfl⟩ : syracuseStep 1988405 = 186413) (by norm_num)
theorem B1955645 : Blo 868566 1955645 := bbase (se 3 (by rfl) ⟨366683, by rfl⟩ : syracuseStep 1955645 = 733367) (by norm_num)
theorem B1103701 : Blo 868566 1103701 := bbase (se 9 (by rfl) ⟨3233, by rfl⟩ : syracuseStep 1103701 = 6467) (by norm_num)
theorem B1988477 : Blo 868566 1988477 := bbase (se 3 (by rfl) ⟨372839, by rfl⟩ : syracuseStep 1988477 = 745679) (by norm_num)
theorem B1955717 : Blo 868566 1955717 := bbase (se 4 (by rfl) ⟨183348, by rfl⟩ : syracuseStep 1955717 = 366697) (by norm_num)
theorem B1857413 : Blo 868566 1857413 := bbase (se 4 (by rfl) ⟨174132, by rfl⟩ : syracuseStep 1857413 = 348265) (by norm_num)
theorem B11163541 : Blo 868566 11163541 := bbase (se 6 (by rfl) ⟨261645, by rfl⟩ : syracuseStep 11163541 = 523291) (by norm_num)
theorem B4413365 : Blo 868566 4413365 := bbase (se 5 (by rfl) ⟨206876, by rfl⟩ : syracuseStep 4413365 = 413753) (by norm_num)
theorem B1103797 : Blo 868566 1103797 := bbase (se 5 (by rfl) ⟨51740, by rfl⟩ : syracuseStep 1103797 = 103481) (by norm_num)
theorem B1955789 : Blo 868566 1955789 := bbase (se 3 (by rfl) ⟨366710, by rfl⟩ : syracuseStep 1955789 = 733421) (by norm_num)
theorem B22566869 : Blo 868566 22566869 := bbase (se 7 (by rfl) ⟨264455, by rfl⟩ : syracuseStep 22566869 = 528911) (by norm_num)
theorem B2578405 : Blo 868566 2578405 := bbase (se 4 (by rfl) ⟨241725, by rfl⟩ : syracuseStep 2578405 = 483451) (by norm_num)
theorem B1955861 : Blo 868566 1955861 := bbase (se 6 (by rfl) ⟨45840, by rfl⟩ : syracuseStep 1955861 = 91681) (by norm_num)
theorem B2480149 : Blo 868566 2480149 := bbase (se 6 (by rfl) ⟨58128, by rfl⟩ : syracuseStep 2480149 = 116257) (by norm_num)
theorem B2938949 : Blo 868566 2938949 := bbase (se 4 (by rfl) ⟨275526, by rfl⟩ : syracuseStep 2938949 = 551053) (by norm_num)
theorem B1955933 : Blo 868566 1955933 := bbase (se 3 (by rfl) ⟨366737, by rfl⟩ : syracuseStep 1955933 = 733475) (by norm_num)
theorem B1103969 : Blo 868566 1103969 := bbase (se 2 (by rfl) ⟨413988, by rfl⟩ : syracuseStep 1103969 = 827977) (by norm_num)
theorem B1104025 : Blo 868566 1104025 := bbase (se 2 (by rfl) ⟨414009, by rfl⟩ : syracuseStep 1104025 = 828019) (by norm_num)
theorem B1956005 : Blo 868566 1956005 := bbase (se 4 (by rfl) ⟨183375, by rfl⟩ : syracuseStep 1956005 = 366751) (by norm_num)
theorem B2119853 : Blo 868566 2119853 := bbase (se 3 (by rfl) ⟨397472, by rfl⟩ : syracuseStep 2119853 = 794945) (by norm_num)
theorem B1956077 : Blo 868566 1956077 := bbase (se 3 (by rfl) ⟨366764, by rfl⟩ : syracuseStep 1956077 = 733529) (by norm_num)
theorem B1104121 : Blo 868566 1104121 := bbase (se 2 (by rfl) ⟨414045, by rfl⟩ : syracuseStep 1104121 = 828091) (by norm_num)
theorem B1956149 : Blo 868566 1956149 := bbase (se 5 (by rfl) ⟨91694, by rfl⟩ : syracuseStep 1956149 = 183389) (by norm_num)
theorem B1988981 : Blo 868566 1988981 := bbase (se 5 (by rfl) ⟨93233, by rfl⟩ : syracuseStep 1988981 = 186467) (by norm_num)
theorem B1956221 : Blo 868566 1956221 := bbase (se 3 (by rfl) ⟨366791, by rfl⟩ : syracuseStep 1956221 = 733583) (by norm_num)
theorem B1857917 : Blo 868566 1857917 := bbase (se 3 (by rfl) ⟨348359, by rfl⟩ : syracuseStep 1857917 = 696719) (by norm_num)
theorem B1857925 : Blo 868566 1857925 := bbase (se 4 (by rfl) ⟨174180, by rfl⟩ : syracuseStep 1857925 = 348361) (by norm_num)
theorem B1104293 : Blo 868566 1104293 := bbase (se 4 (by rfl) ⟨103527, by rfl⟩ : syracuseStep 1104293 = 207055) (by norm_num)
theorem B1956293 : Blo 868566 1956293 := bbase (se 4 (by rfl) ⟨183402, by rfl⟩ : syracuseStep 1956293 = 366805) (by norm_num)
theorem B2939381 : Blo 868566 2939381 := bbase (se 5 (by rfl) ⟨137783, by rfl⟩ : syracuseStep 2939381 = 275567) (by norm_num)
theorem B1956365 : Blo 868566 1956365 := bbase (se 3 (by rfl) ⟨366818, by rfl⟩ : syracuseStep 1956365 = 733637) (by norm_num)
theorem B1956437 : Blo 868566 1956437 := bbase (se 8 (by rfl) ⟨11463, by rfl⟩ : syracuseStep 1956437 = 22927) (by norm_num)
theorem B1956509 : Blo 868566 1956509 := bbase (se 3 (by rfl) ⟨366845, by rfl⟩ : syracuseStep 1956509 = 733691) (by norm_num)
theorem B1956581 : Blo 868566 1956581 := bbase (se 4 (by rfl) ⟨183429, by rfl⟩ : syracuseStep 1956581 = 366859) (by norm_num)
theorem B3726101 : Blo 868566 3726101 := bbase (se 6 (by rfl) ⟨87330, by rfl⟩ : syracuseStep 3726101 = 174661) (by norm_num)
theorem B1956653 : Blo 868566 1956653 := bbase (se 3 (by rfl) ⟨366872, by rfl⟩ : syracuseStep 1956653 = 733745) (by norm_num)
theorem B1006381 : Blo 868566 1006381 := bbase (se 3 (by rfl) ⟨188696, by rfl⟩ : syracuseStep 1006381 = 377393) (by norm_num)
theorem B1956725 : Blo 868566 1956725 := bbase (se 5 (by rfl) ⟨91721, by rfl⟩ : syracuseStep 1956725 = 183443) (by norm_num)
theorem B2939813 : Blo 868566 2939813 := bbase (se 4 (by rfl) ⟨275607, by rfl⟩ : syracuseStep 2939813 = 551215) (by norm_num)
theorem B1956797 : Blo 868566 1956797 := bbase (se 3 (by rfl) ⟨366899, by rfl⟩ : syracuseStep 1956797 = 733799) (by norm_num)
theorem B1956869 : Blo 868566 1956869 := bbase (se 4 (by rfl) ⟨183456, by rfl⟩ : syracuseStep 1956869 = 366913) (by norm_num)
theorem B2088013 : Blo 868566 2088013 := bbase (se 3 (by rfl) ⟨391502, by rfl⟩ : syracuseStep 2088013 = 783005) (by norm_num)
theorem B1956941 : Blo 868566 1956941 := bbase (se 3 (by rfl) ⟨366926, by rfl⟩ : syracuseStep 1956941 = 733853) (by norm_num)
theorem B1957013 : Blo 868566 1957013 := bbase (se 6 (by rfl) ⟨45867, by rfl⟩ : syracuseStep 1957013 = 91735) (by norm_num)
theorem B3300533 : Blo 868566 3300533 := bbase (se 5 (by rfl) ⟨154712, by rfl⟩ : syracuseStep 3300533 = 309425) (by norm_num)
theorem B2645173 : Blo 868566 2645173 := bbase (se 5 (by rfl) ⟨123992, by rfl⟩ : syracuseStep 2645173 = 247985) (by norm_num)
theorem B4414661 : Blo 868566 4414661 := bbase (se 4 (by rfl) ⟨413874, by rfl⟩ : syracuseStep 4414661 = 827749) (by norm_num)
theorem B1957085 : Blo 868566 1957085 := bbase (se 3 (by rfl) ⟨366953, by rfl⟩ : syracuseStep 1957085 = 733907) (by norm_num)
theorem B1957157 : Blo 868566 1957157 := bbase (se 4 (by rfl) ⟨183483, by rfl⟩ : syracuseStep 1957157 = 366967) (by norm_num)
theorem B2940245 : Blo 868566 2940245 := bbase (se 11 (by rfl) ⟨2153, by rfl⟩ : syracuseStep 2940245 = 4307) (by norm_num)
theorem B1957229 : Blo 868566 1957229 := bbase (se 3 (by rfl) ⟨366980, by rfl⟩ : syracuseStep 1957229 = 733961) (by norm_num)
theorem B1957301 : Blo 868566 1957301 := bbase (se 5 (by rfl) ⟨91748, by rfl⟩ : syracuseStep 1957301 = 183497) (by norm_num)
theorem B1465789 : Blo 868566 1465789 := bbase (se 3 (by rfl) ⟨274835, by rfl⟩ : syracuseStep 1465789 = 549671) (by norm_num)
theorem B3300821 : Blo 868566 3300821 := bbase (se 7 (by rfl) ⟨38681, by rfl⟩ : syracuseStep 3300821 = 77363) (by norm_num)
theorem B1859053 : Blo 868566 1859053 := bbase (se 3 (by rfl) ⟨348572, by rfl⟩ : syracuseStep 1859053 = 697145) (by norm_num)
theorem B2481653 : Blo 868566 2481653 := bbase (se 5 (by rfl) ⟨116327, by rfl⟩ : syracuseStep 2481653 = 232655) (by norm_num)
theorem B1957373 : Blo 868566 1957373 := bbase (se 3 (by rfl) ⟨367007, by rfl⟩ : syracuseStep 1957373 = 734015) (by norm_num)
theorem B1072649 : Blo 868566 1072649 := bbase (se 2 (by rfl) ⟨402243, by rfl⟩ : syracuseStep 1072649 = 804487) (by norm_num)
theorem B1465877 : Blo 868566 1465877 := bbase (se 6 (by rfl) ⟨34356, by rfl⟩ : syracuseStep 1465877 = 68713) (by norm_num)
theorem B1957445 : Blo 868566 1957445 := bbase (se 4 (by rfl) ⟨183510, by rfl⟩ : syracuseStep 1957445 = 367021) (by norm_num)
theorem B1957517 : Blo 868566 1957517 := bbase (se 3 (by rfl) ⟨367034, by rfl⟩ : syracuseStep 1957517 = 734069) (by norm_num)
theorem B1466005 : Blo 868566 1466005 := bbase (se 6 (by rfl) ⟨34359, by rfl⟩ : syracuseStep 1466005 = 68719) (by norm_num)
theorem B2088629 : Blo 868566 2088629 := bbase (se 5 (by rfl) ⟨97904, by rfl⟩ : syracuseStep 2088629 = 195809) (by norm_num)
theorem B1957589 : Blo 868566 1957589 := bbase (se 7 (by rfl) ⟨22940, by rfl⟩ : syracuseStep 1957589 = 45881) (by norm_num)
theorem B1466093 : Blo 868566 1466093 := bbase (se 3 (by rfl) ⟨274892, by rfl⟩ : syracuseStep 1466093 = 549785) (by norm_num)
theorem B3727093 : Blo 868566 3727093 := bbase (se 5 (by rfl) ⟨174707, by rfl⟩ : syracuseStep 3727093 = 349415) (by norm_num)
theorem B2940677 : Blo 868566 2940677 := bbase (se 4 (by rfl) ⟨275688, by rfl⟩ : syracuseStep 2940677 = 551377) (by norm_num)
theorem B1957661 : Blo 868566 1957661 := bbase (se 3 (by rfl) ⟨367061, by rfl⟩ : syracuseStep 1957661 = 734123) (by norm_num)
theorem B1957733 : Blo 868566 1957733 := bbase (se 4 (by rfl) ⟨183537, by rfl⟩ : syracuseStep 1957733 = 367075) (by norm_num)
theorem B1859429 : Blo 868566 1859429 := bbase (se 4 (by rfl) ⟨174321, by rfl⟩ : syracuseStep 1859429 = 348643) (by norm_num)
theorem B1466221 : Blo 868566 1466221 := bbase (se 3 (by rfl) ⟨274916, by rfl⟩ : syracuseStep 1466221 = 549833) (by norm_num)
theorem B2088821 : Blo 868566 2088821 := bbase (se 5 (by rfl) ⟨97913, by rfl⟩ : syracuseStep 2088821 = 195827) (by norm_num)
theorem B2383781 : Blo 868566 2383781 := bbase (se 4 (by rfl) ⟨223479, by rfl⟩ : syracuseStep 2383781 = 446959) (by norm_num)
theorem B4186021 : Blo 868566 4186021 := bbase (se 4 (by rfl) ⟨392439, by rfl⟩ : syracuseStep 4186021 = 784879) (by norm_num)
theorem B1957805 : Blo 868566 1957805 := bbase (se 3 (by rfl) ⟨367088, by rfl⟩ : syracuseStep 1957805 = 734177) (by norm_num)
theorem B1466309 : Blo 868566 1466309 := bbase (se 4 (by rfl) ⟨137466, by rfl⟩ : syracuseStep 1466309 = 274933) (by norm_num)
theorem B1957877 : Blo 868566 1957877 := bbase (se 5 (by rfl) ⟨91775, by rfl⟩ : syracuseStep 1957877 = 183551) (by norm_num)
theorem B1237045 : Blo 868566 1237045 := bbase (se 5 (by rfl) ⟨57986, by rfl⟩ : syracuseStep 1237045 = 115973) (by norm_num)
theorem B1957949 : Blo 868566 1957949 := bbase (se 3 (by rfl) ⟨367115, by rfl⟩ : syracuseStep 1957949 = 734231) (by norm_num)
theorem B1466437 : Blo 868566 1466437 := bbase (se 4 (by rfl) ⟨137478, by rfl⟩ : syracuseStep 1466437 = 274957) (by norm_num)
theorem B2384005 : Blo 868566 2384005 := bbase (se 4 (by rfl) ⟨223500, by rfl⟩ : syracuseStep 2384005 = 447001) (by norm_num)
theorem B1958021 : Blo 868566 1958021 := bbase (se 4 (by rfl) ⟨183564, by rfl⟩ : syracuseStep 1958021 = 367129) (by norm_num)
theorem B2089109 : Blo 868566 2089109 := bbase (se 6 (by rfl) ⟨48963, by rfl⟩ : syracuseStep 2089109 = 97927) (by norm_num)
theorem B1466525 : Blo 868566 1466525 := bbase (se 3 (by rfl) ⟨274973, by rfl⟩ : syracuseStep 1466525 = 549947) (by norm_num)
theorem B2941109 : Blo 868566 2941109 := bbase (se 5 (by rfl) ⟨137864, by rfl⟩ : syracuseStep 2941109 = 275729) (by norm_num)
theorem B1958093 : Blo 868566 1958093 := bbase (se 3 (by rfl) ⟨367142, by rfl⟩ : syracuseStep 1958093 = 734285) (by norm_num)
theorem B1958165 : Blo 868566 1958165 := bbase (se 6 (by rfl) ⟨45894, by rfl⟩ : syracuseStep 1958165 = 91789) (by norm_num)
theorem B1466653 : Blo 868566 1466653 := bbase (se 3 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 1466653 = 549995) (by norm_num)
theorem B1302869 : Blo 868566 1302869 := bbase (se 10 (by rfl) ⟨1908, by rfl⟩ : syracuseStep 1302869 = 3817) (by norm_num)
theorem B1958237 : Blo 868566 1958237 := bbase (se 3 (by rfl) ⟨367169, by rfl⟩ : syracuseStep 1958237 = 734339) (by norm_num)
theorem B1302893 : Blo 868566 1302893 := bbase (se 3 (by rfl) ⟨244292, by rfl⟩ : syracuseStep 1302893 = 488585) (by norm_num)
theorem B8348021 : Blo 868566 8348021 := bbase (se 5 (by rfl) ⟨391313, by rfl⟩ : syracuseStep 8348021 = 782627) (by norm_num)
theorem B1466741 : Blo 868566 1466741 := bbase (se 5 (by rfl) ⟨68753, by rfl⟩ : syracuseStep 1466741 = 137507) (by norm_num)
theorem B1302917 : Blo 868566 1302917 := bbase (se 4 (by rfl) ⟨122148, by rfl⟩ : syracuseStep 1302917 = 244297) (by norm_num)
theorem B1302941 : Blo 868566 1302941 := bbase (se 3 (by rfl) ⟨244301, by rfl⟩ : syracuseStep 1302941 = 488603) (by norm_num)
theorem B2646437 : Blo 868566 2646437 := bbase (se 4 (by rfl) ⟨248103, by rfl⟩ : syracuseStep 2646437 = 496207) (by norm_num)
theorem B1958309 : Blo 868566 1958309 := bbase (se 4 (by rfl) ⟨183591, by rfl⟩ : syracuseStep 1958309 = 367183) (by norm_num)
theorem B1302965 : Blo 868566 1302965 := bbase (se 5 (by rfl) ⟨61076, by rfl⟩ : syracuseStep 1302965 = 122153) (by norm_num)
theorem B1302989 : Blo 868566 1302989 := bbase (se 3 (by rfl) ⟨244310, by rfl⟩ : syracuseStep 1302989 = 488621) (by norm_num)
theorem B4415957 : Blo 868566 4415957 := bbase (se 7 (by rfl) ⟨51749, by rfl⟩ : syracuseStep 4415957 = 103499) (by norm_num)
theorem B1303013 : Blo 868566 1303013 := bbase (se 4 (by rfl) ⟨122157, by rfl⟩ : syracuseStep 1303013 = 244315) (by norm_num)
theorem B1958381 : Blo 868566 1958381 := bbase (se 3 (by rfl) ⟨367196, by rfl⟩ : syracuseStep 1958381 = 734393) (by norm_num)
theorem B1466869 : Blo 868566 1466869 := bbase (se 5 (by rfl) ⟨68759, by rfl⟩ : syracuseStep 1466869 = 137519) (by norm_num)
theorem B1303037 : Blo 868566 1303037 := bbase (se 3 (by rfl) ⟨244319, by rfl⟩ : syracuseStep 1303037 = 488639) (by norm_num)
theorem B1303061 : Blo 868566 1303061 := bbase (se 6 (by rfl) ⟨30540, by rfl⟩ : syracuseStep 1303061 = 61081) (by norm_num)
theorem B1303085 : Blo 868566 1303085 := bbase (se 3 (by rfl) ⟨244328, by rfl⟩ : syracuseStep 1303085 = 488657) (by norm_num)
theorem B1958453 : Blo 868566 1958453 := bbase (se 5 (by rfl) ⟨91802, by rfl⟩ : syracuseStep 1958453 = 183605) (by norm_num)
theorem B1303109 : Blo 868566 1303109 := bbase (se 4 (by rfl) ⟨122166, by rfl⟩ : syracuseStep 1303109 = 244333) (by norm_num)
theorem B2122309 : Blo 868566 2122309 := bbase (se 4 (by rfl) ⟨198966, by rfl⟩ : syracuseStep 2122309 = 397933) (by norm_num)
theorem B1466957 : Blo 868566 1466957 := bbase (se 3 (by rfl) ⟨275054, by rfl⟩ : syracuseStep 1466957 = 550109) (by norm_num)
theorem B1303133 : Blo 868566 1303133 := bbase (se 3 (by rfl) ⟨244337, by rfl⟩ : syracuseStep 1303133 = 488675) (by norm_num)
theorem B2941541 : Blo 868566 2941541 := bbase (se 4 (by rfl) ⟨275769, by rfl⟩ : syracuseStep 2941541 = 551539) (by norm_num)
theorem B1303157 : Blo 868566 1303157 := bbase (se 5 (by rfl) ⟨61085, by rfl⟩ : syracuseStep 1303157 = 122171) (by norm_num)
theorem B3302005 : Blo 868566 3302005 := bbase (se 5 (by rfl) ⟨154781, by rfl⟩ : syracuseStep 3302005 = 309563) (by norm_num)
theorem B1958525 : Blo 868566 1958525 := bbase (se 3 (by rfl) ⟨367223, by rfl⟩ : syracuseStep 1958525 = 734447) (by norm_num)
theorem B1237637 : Blo 868566 1237637 := bbase (se 4 (by rfl) ⟨116028, by rfl⟩ : syracuseStep 1237637 = 232057) (by norm_num)
theorem B1303181 : Blo 868566 1303181 := bbase (se 3 (by rfl) ⟨244346, by rfl⟩ : syracuseStep 1303181 = 488693) (by norm_num)
theorem B8938133 : Blo 868566 8938133 := bbase (se 6 (by rfl) ⟨209487, by rfl⟩ : syracuseStep 8938133 = 418975) (by norm_num)
theorem B1303205 : Blo 868566 1303205 := bbase (se 4 (by rfl) ⟨122175, by rfl⟩ : syracuseStep 1303205 = 244351) (by norm_num)
theorem B1303229 : Blo 868566 1303229 := bbase (se 3 (by rfl) ⟨244355, by rfl⟩ : syracuseStep 1303229 = 488711) (by norm_num)
theorem B1958597 : Blo 868566 1958597 := bbase (se 4 (by rfl) ⟨183618, by rfl⟩ : syracuseStep 1958597 = 367237) (by norm_num)
theorem B1467085 : Blo 868566 1467085 := bbase (se 3 (by rfl) ⟨275078, by rfl⟩ : syracuseStep 1467085 = 550157) (by norm_num)
theorem B1303253 : Blo 868566 1303253 := bbase (se 7 (by rfl) ⟨15272, by rfl⟩ : syracuseStep 1303253 = 30545) (by norm_num)
theorem B1237717 : Blo 868566 1237717 := bbase (se 7 (by rfl) ⟨14504, by rfl⟩ : syracuseStep 1237717 = 29009) (by norm_num)
theorem B3138277 : Blo 868566 3138277 := bbase (se 4 (by rfl) ⟨294213, by rfl⟩ : syracuseStep 3138277 = 588427) (by norm_num)
theorem B1303277 : Blo 868566 1303277 := bbase (se 3 (by rfl) ⟨244364, by rfl⟩ : syracuseStep 1303277 = 488729) (by norm_num)
theorem B1303301 : Blo 868566 1303301 := bbase (se 4 (by rfl) ⟨122184, by rfl⟩ : syracuseStep 1303301 = 244369) (by norm_num)
theorem B1958669 : Blo 868566 1958669 := bbase (se 3 (by rfl) ⟨367250, by rfl⟩ : syracuseStep 1958669 = 734501) (by norm_num)
theorem B1303325 : Blo 868566 1303325 := bbase (se 3 (by rfl) ⟨244373, by rfl⟩ : syracuseStep 1303325 = 488747) (by norm_num)
theorem B1467173 : Blo 868566 1467173 := bbase (se 4 (by rfl) ⟨137547, by rfl⟩ : syracuseStep 1467173 = 275095) (by norm_num)
theorem B1303349 : Blo 868566 1303349 := bbase (se 5 (by rfl) ⟨61094, by rfl⟩ : syracuseStep 1303349 = 122189) (by norm_num)
theorem B1303373 : Blo 868566 1303373 := bbase (se 3 (by rfl) ⟨244382, by rfl⟩ : syracuseStep 1303373 = 488765) (by norm_num)
theorem B1237837 : Blo 868566 1237837 := bbase (se 3 (by rfl) ⟨232094, by rfl⟩ : syracuseStep 1237837 = 464189) (by norm_num)
theorem B1958741 : Blo 868566 1958741 := bbase (se 9 (by rfl) ⟨5738, by rfl⟩ : syracuseStep 1958741 = 11477) (by norm_num)
theorem B1303397 : Blo 868566 1303397 := bbase (se 4 (by rfl) ⟨122193, by rfl⟩ : syracuseStep 1303397 = 244387) (by norm_num)
theorem B1565549 : Blo 868566 1565549 := bbase (se 3 (by rfl) ⟨293540, by rfl⟩ : syracuseStep 1565549 = 587081) (by norm_num)
theorem B1303421 : Blo 868566 1303421 := bbase (se 3 (by rfl) ⟨244391, by rfl⟩ : syracuseStep 1303421 = 488783) (by norm_num)
theorem B1303445 : Blo 868566 1303445 := bbase (se 6 (by rfl) ⟨30549, by rfl⟩ : syracuseStep 1303445 = 61099) (by norm_num)
theorem B1958813 : Blo 868566 1958813 := bbase (se 3 (by rfl) ⟨367277, by rfl⟩ : syracuseStep 1958813 = 734555) (by norm_num)
theorem B1467301 : Blo 868566 1467301 := bbase (se 4 (by rfl) ⟨137559, by rfl⟩ : syracuseStep 1467301 = 275119) (by norm_num)
theorem B3302309 : Blo 868566 3302309 := bbase (se 4 (by rfl) ⟨309591, by rfl⟩ : syracuseStep 3302309 = 619183) (by norm_num)
theorem B1303469 : Blo 868566 1303469 := bbase (se 3 (by rfl) ⟨244400, by rfl⟩ : syracuseStep 1303469 = 488801) (by norm_num)
theorem B1237933 : Blo 868566 1237933 := bbase (se 3 (by rfl) ⟨232112, by rfl⟩ : syracuseStep 1237933 = 464225) (by norm_num)
theorem B1303493 : Blo 868566 1303493 := bbase (se 4 (by rfl) ⟨122202, by rfl⟩ : syracuseStep 1303493 = 244405) (by norm_num)
theorem B1303517 : Blo 868566 1303517 := bbase (se 3 (by rfl) ⟨244409, by rfl⟩ : syracuseStep 1303517 = 488819) (by norm_num)
theorem B1958885 : Blo 868566 1958885 := bbase (se 4 (by rfl) ⟨183645, by rfl⟩ : syracuseStep 1958885 = 367291) (by norm_num)
theorem B1303541 : Blo 868566 1303541 := bbase (se 5 (by rfl) ⟨61103, by rfl⟩ : syracuseStep 1303541 = 122207) (by norm_num)
theorem B1467389 : Blo 868566 1467389 := bbase (se 3 (by rfl) ⟨275135, by rfl⟩ : syracuseStep 1467389 = 550271) (by norm_num)
theorem B1303565 : Blo 868566 1303565 := bbase (se 3 (by rfl) ⟨244418, by rfl⟩ : syracuseStep 1303565 = 488837) (by norm_num)
theorem B2941973 : Blo 868566 2941973 := bbase (se 6 (by rfl) ⟨68952, by rfl⟩ : syracuseStep 2941973 = 137905) (by norm_num)
theorem B1303589 : Blo 868566 1303589 := bbase (se 4 (by rfl) ⟨122211, by rfl⟩ : syracuseStep 1303589 = 244423) (by norm_num)
theorem B2483237 : Blo 868566 2483237 := bbase (se 4 (by rfl) ⟨232803, by rfl⟩ : syracuseStep 2483237 = 465607) (by norm_num)
theorem B1958957 : Blo 868566 1958957 := bbase (se 3 (by rfl) ⟨367304, by rfl⟩ : syracuseStep 1958957 = 734609) (by norm_num)
theorem B1303613 : Blo 868566 1303613 := bbase (se 3 (by rfl) ⟨244427, by rfl⟩ : syracuseStep 1303613 = 488855) (by norm_num)
theorem B1303637 : Blo 868566 1303637 := bbase (se 8 (by rfl) ⟨7638, by rfl⟩ : syracuseStep 1303637 = 15277) (by norm_num)
theorem B1303661 : Blo 868566 1303661 := bbase (se 3 (by rfl) ⟨244436, by rfl⟩ : syracuseStep 1303661 = 488873) (by norm_num)
theorem B1959029 : Blo 868566 1959029 := bbase (se 5 (by rfl) ⟨91829, by rfl⟩ : syracuseStep 1959029 = 183659) (by norm_num)
theorem B1467517 : Blo 868566 1467517 := bbase (se 3 (by rfl) ⟨275159, by rfl⟩ : syracuseStep 1467517 = 550319) (by norm_num)
theorem B1303685 : Blo 868566 1303685 := bbase (se 4 (by rfl) ⟨122220, by rfl⟩ : syracuseStep 1303685 = 244441) (by norm_num)
theorem B1303709 : Blo 868566 1303709 := bbase (se 3 (by rfl) ⟨244445, by rfl⟩ : syracuseStep 1303709 = 488891) (by norm_num)
theorem B1303733 : Blo 868566 1303733 := bbase (se 5 (by rfl) ⟨61112, by rfl⟩ : syracuseStep 1303733 = 122225) (by norm_num)
theorem B1959101 : Blo 868566 1959101 := bbase (se 3 (by rfl) ⟨367331, by rfl⟩ : syracuseStep 1959101 = 734663) (by norm_num)
theorem B1303757 : Blo 868566 1303757 := bbase (se 3 (by rfl) ⟨244454, by rfl⟩ : syracuseStep 1303757 = 488909) (by norm_num)
theorem B1467605 : Blo 868566 1467605 := bbase (se 7 (by rfl) ⟨17198, by rfl⟩ : syracuseStep 1467605 = 34397) (by norm_num)
theorem B1303781 : Blo 868566 1303781 := bbase (se 4 (by rfl) ⟨122229, by rfl⟩ : syracuseStep 1303781 = 244459) (by norm_num)
theorem B1303805 : Blo 868566 1303805 := bbase (se 3 (by rfl) ⟨244463, by rfl⟩ : syracuseStep 1303805 = 488927) (by norm_num)
theorem B1959173 : Blo 868566 1959173 := bbase (se 4 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 1959173 = 367345) (by norm_num)
theorem B1303829 : Blo 868566 1303829 := bbase (se 6 (by rfl) ⟨30558, by rfl⟩ : syracuseStep 1303829 = 61117) (by norm_num)
theorem B1303853 : Blo 868566 1303853 := bbase (se 3 (by rfl) ⟨244472, by rfl⟩ : syracuseStep 1303853 = 488945) (by norm_num)
theorem B1303877 : Blo 868566 1303877 := bbase (se 4 (by rfl) ⟨122238, by rfl⟩ : syracuseStep 1303877 = 244477) (by norm_num)
theorem B1959245 : Blo 868566 1959245 := bbase (se 3 (by rfl) ⟨367358, by rfl⟩ : syracuseStep 1959245 = 734717) (by norm_num)
theorem B1467733 : Blo 868566 1467733 := bbase (se 12 (by rfl) ⟨537, by rfl⟩ : syracuseStep 1467733 = 1075) (by norm_num)
theorem B1303901 : Blo 868566 1303901 := bbase (se 3 (by rfl) ⟨244481, by rfl⟩ : syracuseStep 1303901 = 488963) (by norm_num)
theorem B1303925 : Blo 868566 1303925 := bbase (se 5 (by rfl) ⟨61121, by rfl⟩ : syracuseStep 1303925 = 122243) (by norm_num)
theorem B1860989 : Blo 868566 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B1303949 : Blo 868566 1303949 := bbase (se 3 (by rfl) ⟨244490, by rfl⟩ : syracuseStep 1303949 = 488981) (by norm_num)
theorem B1959317 : Blo 868566 1959317 := bbase (se 6 (by rfl) ⟨45921, by rfl⟩ : syracuseStep 1959317 = 91843) (by norm_num)
theorem B1238429 : Blo 868566 1238429 := bbase (se 3 (by rfl) ⟨232205, by rfl⟩ : syracuseStep 1238429 = 464411) (by norm_num)
theorem B1303973 : Blo 868566 1303973 := bbase (se 4 (by rfl) ⟨122247, by rfl⟩ : syracuseStep 1303973 = 244495) (by norm_num)
theorem B1467821 : Blo 868566 1467821 := bbase (se 3 (by rfl) ⟨275216, by rfl⟩ : syracuseStep 1467821 = 550433) (by norm_num)
theorem B1303997 : Blo 868566 1303997 := bbase (se 3 (by rfl) ⟨244499, by rfl⟩ : syracuseStep 1303997 = 488999) (by norm_num)
theorem B2942405 : Blo 868566 2942405 := bbase (se 4 (by rfl) ⟨275850, by rfl⟩ : syracuseStep 2942405 = 551701) (by norm_num)
theorem B1861069 : Blo 868566 1861069 := bbase (se 3 (by rfl) ⟨348950, by rfl⟩ : syracuseStep 1861069 = 697901) (by norm_num)
theorem B1304021 : Blo 868566 1304021 := bbase (se 7 (by rfl) ⟨15281, by rfl⟩ : syracuseStep 1304021 = 30563) (by norm_num)
theorem B1959389 : Blo 868566 1959389 := bbase (se 3 (by rfl) ⟨367385, by rfl⟩ : syracuseStep 1959389 = 734771) (by norm_num)
theorem B1304045 : Blo 868566 1304045 := bbase (se 3 (by rfl) ⟨244508, by rfl⟩ : syracuseStep 1304045 = 489017) (by norm_num)
theorem B1304069 : Blo 868566 1304069 := bbase (se 4 (by rfl) ⟨122256, by rfl⟩ : syracuseStep 1304069 = 244513) (by norm_num)
theorem B1304093 : Blo 868566 1304093 := bbase (se 3 (by rfl) ⟨244517, by rfl⟩ : syracuseStep 1304093 = 489035) (by norm_num)
theorem B1959461 : Blo 868566 1959461 := bbase (se 4 (by rfl) ⟨183699, by rfl⟩ : syracuseStep 1959461 = 367399) (by norm_num)
theorem B1467949 : Blo 868566 1467949 := bbase (se 3 (by rfl) ⟨275240, by rfl⟩ : syracuseStep 1467949 = 550481) (by norm_num)
theorem B1304117 : Blo 868566 1304117 := bbase (se 5 (by rfl) ⟨61130, by rfl⟩ : syracuseStep 1304117 = 122261) (by norm_num)
theorem B1304141 : Blo 868566 1304141 := bbase (se 3 (by rfl) ⟨244526, by rfl⟩ : syracuseStep 1304141 = 489053) (by norm_num)
theorem B1304165 : Blo 868566 1304165 := bbase (se 4 (by rfl) ⟨122265, by rfl⟩ : syracuseStep 1304165 = 244531) (by norm_num)
theorem B1959533 : Blo 868566 1959533 := bbase (se 3 (by rfl) ⟨367412, by rfl⟩ : syracuseStep 1959533 = 734825) (by norm_num)
theorem B1304189 : Blo 868566 1304189 := bbase (se 3 (by rfl) ⟨244535, by rfl⟩ : syracuseStep 1304189 = 489071) (by norm_num)
theorem B1468037 : Blo 868566 1468037 := bbase (se 4 (by rfl) ⟨137628, by rfl⟩ : syracuseStep 1468037 = 275257) (by norm_num)
theorem B1304213 : Blo 868566 1304213 := bbase (se 6 (by rfl) ⟨30567, by rfl⟩ : syracuseStep 1304213 = 61135) (by norm_num)
theorem B1304237 : Blo 868566 1304237 := bbase (se 3 (by rfl) ⟨244544, by rfl⟩ : syracuseStep 1304237 = 489089) (by norm_num)
theorem B1959605 : Blo 868566 1959605 := bbase (se 5 (by rfl) ⟨91856, by rfl⟩ : syracuseStep 1959605 = 183713) (by norm_num)
theorem B1304261 : Blo 868566 1304261 := bbase (se 4 (by rfl) ⟨122274, by rfl⟩ : syracuseStep 1304261 = 244549) (by norm_num)
theorem B2483909 : Blo 868566 2483909 := bbase (se 4 (by rfl) ⟨232866, by rfl⟩ : syracuseStep 2483909 = 465733) (by norm_num)
theorem B3139285 : Blo 868566 3139285 := bbase (se 7 (by rfl) ⟨36788, by rfl⟩ : syracuseStep 3139285 = 73577) (by norm_num)
theorem B1304285 : Blo 868566 1304285 := bbase (se 3 (by rfl) ⟨244553, by rfl⟩ : syracuseStep 1304285 = 489107) (by norm_num)
theorem B4417253 : Blo 868566 4417253 := bbase (se 4 (by rfl) ⟨414117, by rfl⟩ : syracuseStep 4417253 = 828235) (by norm_num)
theorem B3761909 : Blo 868566 3761909 := bbase (se 5 (by rfl) ⟨176339, by rfl⟩ : syracuseStep 3761909 = 352679) (by norm_num)
theorem B1304309 : Blo 868566 1304309 := bbase (se 5 (by rfl) ⟨61139, by rfl⟩ : syracuseStep 1304309 = 122279) (by norm_num)
theorem B1959677 : Blo 868566 1959677 := bbase (se 3 (by rfl) ⟨367439, by rfl⟩ : syracuseStep 1959677 = 734879) (by norm_num)
theorem B1468165 : Blo 868566 1468165 := bbase (se 4 (by rfl) ⟨137640, by rfl⟩ : syracuseStep 1468165 = 275281) (by norm_num)
theorem B1304333 : Blo 868566 1304333 := bbase (se 3 (by rfl) ⟨244562, by rfl⟩ : syracuseStep 1304333 = 489125) (by norm_num)
theorem B7956245 : Blo 868566 7956245 := bbase (se 6 (by rfl) ⟨186474, by rfl⟩ : syracuseStep 7956245 = 372949) (by norm_num)
theorem B1304357 : Blo 868566 1304357 := bbase (se 4 (by rfl) ⟨122283, by rfl⟩ : syracuseStep 1304357 = 244567) (by norm_num)
theorem B1304381 : Blo 868566 1304381 := bbase (se 3 (by rfl) ⟨244571, by rfl⟩ : syracuseStep 1304381 = 489143) (by norm_num)
theorem B1959749 : Blo 868566 1959749 := bbase (se 4 (by rfl) ⟨183726, by rfl⟩ : syracuseStep 1959749 = 367453) (by norm_num)
theorem B1304405 : Blo 868566 1304405 := bbase (se 9 (by rfl) ⟨3821, by rfl⟩ : syracuseStep 1304405 = 7643) (by norm_num)
theorem B1468253 : Blo 868566 1468253 := bbase (se 3 (by rfl) ⟨275297, by rfl⟩ : syracuseStep 1468253 = 550595) (by norm_num)
theorem B1304429 : Blo 868566 1304429 := bbase (se 3 (by rfl) ⟨244580, by rfl⟩ : syracuseStep 1304429 = 489161) (by norm_num)
theorem B2942837 : Blo 868566 2942837 := bbase (se 5 (by rfl) ⟨137945, by rfl⟩ : syracuseStep 2942837 = 275891) (by norm_num)
theorem B1304453 : Blo 868566 1304453 := bbase (se 4 (by rfl) ⟨122292, by rfl⟩ : syracuseStep 1304453 = 244585) (by norm_num)
theorem B1959821 : Blo 868566 1959821 := bbase (se 3 (by rfl) ⟨367466, by rfl⟩ : syracuseStep 1959821 = 734933) (by norm_num)
theorem B1304477 : Blo 868566 1304477 := bbase (se 3 (by rfl) ⟨244589, by rfl⟩ : syracuseStep 1304477 = 489179) (by norm_num)
theorem B1304501 : Blo 868566 1304501 := bbase (se 5 (by rfl) ⟨61148, by rfl⟩ : syracuseStep 1304501 = 122297) (by norm_num)
theorem B1238981 : Blo 868566 1238981 := bbase (se 4 (by rfl) ⟨116154, by rfl⟩ : syracuseStep 1238981 = 232309) (by norm_num)
theorem B1304525 : Blo 868566 1304525 := bbase (se 3 (by rfl) ⟨244598, by rfl⟩ : syracuseStep 1304525 = 489197) (by norm_num)
theorem B1959893 : Blo 868566 1959893 := bbase (se 7 (by rfl) ⟨22967, by rfl⟩ : syracuseStep 1959893 = 45935) (by norm_num)
theorem B1468381 : Blo 868566 1468381 := bbase (se 3 (by rfl) ⟨275321, by rfl⟩ : syracuseStep 1468381 = 550643) (by norm_num)
theorem B1304549 : Blo 868566 1304549 := bbase (se 4 (by rfl) ⟨122301, by rfl⟩ : syracuseStep 1304549 = 244603) (by norm_num)
theorem B1304573 : Blo 868566 1304573 := bbase (se 3 (by rfl) ⟨244607, by rfl⟩ : syracuseStep 1304573 = 489215) (by norm_num)
theorem B1304597 : Blo 868566 1304597 := bbase (se 6 (by rfl) ⟨30576, by rfl⟩ : syracuseStep 1304597 = 61153) (by norm_num)
theorem B1959965 : Blo 868566 1959965 := bbase (se 3 (by rfl) ⟨367493, by rfl⟩ : syracuseStep 1959965 = 734987) (by norm_num)
theorem B1304621 : Blo 868566 1304621 := bbase (se 3 (by rfl) ⟨244616, by rfl⟩ : syracuseStep 1304621 = 489233) (by norm_num)
theorem B1468469 : Blo 868566 1468469 := bbase (se 5 (by rfl) ⟨68834, by rfl⟩ : syracuseStep 1468469 = 137669) (by norm_num)
theorem B1304645 : Blo 868566 1304645 := bbase (se 4 (by rfl) ⟨122310, by rfl⟩ : syracuseStep 1304645 = 244621) (by norm_num)
theorem B1304669 : Blo 868566 1304669 := bbase (se 3 (by rfl) ⟨244625, by rfl⟩ : syracuseStep 1304669 = 489251) (by norm_num)
theorem B2091109 : Blo 868566 2091109 := bbase (se 4 (by rfl) ⟨196041, by rfl⟩ : syracuseStep 2091109 = 392083) (by norm_num)
theorem B1960037 : Blo 868566 1960037 := bbase (se 4 (by rfl) ⟨183753, by rfl⟩ : syracuseStep 1960037 = 367507) (by norm_num)
theorem B1304693 : Blo 868566 1304693 := bbase (se 5 (by rfl) ⟨61157, by rfl⟩ : syracuseStep 1304693 = 122315) (by norm_num)
theorem B2484341 : Blo 868566 2484341 := bbase (se 5 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 2484341 = 232907) (by norm_num)
theorem B1304717 : Blo 868566 1304717 := bbase (se 3 (by rfl) ⟨244634, by rfl⟩ : syracuseStep 1304717 = 489269) (by norm_num)
theorem B1304741 : Blo 868566 1304741 := bbase (se 4 (by rfl) ⟨122319, by rfl⟩ : syracuseStep 1304741 = 244639) (by norm_num)
theorem B1960109 : Blo 868566 1960109 := bbase (se 3 (by rfl) ⟨367520, by rfl⟩ : syracuseStep 1960109 = 735041) (by norm_num)
theorem B1468597 : Blo 868566 1468597 := bbase (se 5 (by rfl) ⟨68840, by rfl⟩ : syracuseStep 1468597 = 137681) (by norm_num)
theorem B1304765 : Blo 868566 1304765 := bbase (se 3 (by rfl) ⟨244643, by rfl⟩ : syracuseStep 1304765 = 489287) (by norm_num)
theorem B1304789 : Blo 868566 1304789 := bbase (se 7 (by rfl) ⟨15290, by rfl⟩ : syracuseStep 1304789 = 30581) (by norm_num)
theorem B1304813 : Blo 868566 1304813 := bbase (se 3 (by rfl) ⟨244652, by rfl⟩ : syracuseStep 1304813 = 489305) (by norm_num)
theorem B1960181 : Blo 868566 1960181 := bbase (se 5 (by rfl) ⟨91883, by rfl⟩ : syracuseStep 1960181 = 183767) (by norm_num)
theorem B1304837 : Blo 868566 1304837 := bbase (se 4 (by rfl) ⟨122328, by rfl⟩ : syracuseStep 1304837 = 244657) (by norm_num)
theorem B977161 : Blo 868566 977161 := bbase (se 2 (by rfl) ⟨366435, by rfl⟩ : syracuseStep 977161 = 732871) (by norm_num)
theorem B1468685 : Blo 868566 1468685 := bbase (se 3 (by rfl) ⟨275378, by rfl⟩ : syracuseStep 1468685 = 550757) (by norm_num)
theorem B1304861 : Blo 868566 1304861 := bbase (se 3 (by rfl) ⟨244661, by rfl⟩ : syracuseStep 1304861 = 489323) (by norm_num)
theorem B2943269 : Blo 868566 2943269 := bbase (se 4 (by rfl) ⟨275931, by rfl⟩ : syracuseStep 2943269 = 551863) (by norm_num)
theorem B977197 : Blo 868566 977197 := bbase (se 3 (by rfl) ⟨183224, by rfl⟩ : syracuseStep 977197 = 366449) (by norm_num)
theorem B1304885 : Blo 868566 1304885 := bbase (se 5 (by rfl) ⟨61166, by rfl⟩ : syracuseStep 1304885 = 122333) (by norm_num)
theorem B1960253 : Blo 868566 1960253 := bbase (se 3 (by rfl) ⟨367547, by rfl⟩ : syracuseStep 1960253 = 735095) (by norm_num)
theorem B1861957 : Blo 868566 1861957 := bbase (se 4 (by rfl) ⟨174558, by rfl⟩ : syracuseStep 1861957 = 349117) (by norm_num)
theorem B1304909 : Blo 868566 1304909 := bbase (se 3 (by rfl) ⟨244670, by rfl⟩ : syracuseStep 1304909 = 489341) (by norm_num)
theorem B977233 : Blo 868566 977233 := bbase (se 2 (by rfl) ⟨366462, by rfl⟩ : syracuseStep 977233 = 732925) (by norm_num)
theorem B1304933 : Blo 868566 1304933 := bbase (se 4 (by rfl) ⟨122337, by rfl⟩ : syracuseStep 1304933 = 244675) (by norm_num)
theorem B977269 : Blo 868566 977269 := bbase (se 5 (by rfl) ⟨45809, by rfl⟩ : syracuseStep 977269 = 91619) (by norm_num)
theorem B1304957 : Blo 868566 1304957 := bbase (se 3 (by rfl) ⟨244679, by rfl⟩ : syracuseStep 1304957 = 489359) (by norm_num)
theorem B1960325 : Blo 868566 1960325 := bbase (se 4 (by rfl) ⟨183780, by rfl⟩ : syracuseStep 1960325 = 367561) (by norm_num)
theorem B1468813 : Blo 868566 1468813 := bbase (se 3 (by rfl) ⟨275402, by rfl⟩ : syracuseStep 1468813 = 550805) (by norm_num)
theorem B1304981 : Blo 868566 1304981 := bbase (se 6 (by rfl) ⟨30585, by rfl⟩ : syracuseStep 1304981 = 61171) (by norm_num)
theorem B977305 : Blo 868566 977305 := bbase (se 2 (by rfl) ⟨366489, by rfl⟩ : syracuseStep 977305 = 732979) (by norm_num)
theorem B1305005 : Blo 868566 1305005 := bbase (se 3 (by rfl) ⟨244688, by rfl⟩ : syracuseStep 1305005 = 489377) (by norm_num)
theorem B977341 : Blo 868566 977341 := bbase (se 3 (by rfl) ⟨183251, by rfl⟩ : syracuseStep 977341 = 366503) (by norm_num)
theorem B1305029 : Blo 868566 1305029 := bbase (se 4 (by rfl) ⟨122346, by rfl⟩ : syracuseStep 1305029 = 244693) (by norm_num)
theorem B1960397 : Blo 868566 1960397 := bbase (se 3 (by rfl) ⟨367574, by rfl⟩ : syracuseStep 1960397 = 735149) (by norm_num)
theorem B1305053 : Blo 868566 1305053 := bbase (se 3 (by rfl) ⟨244697, by rfl⟩ : syracuseStep 1305053 = 489395) (by norm_num)
theorem B977377 : Blo 868566 977377 := bbase (se 2 (by rfl) ⟨366516, by rfl⟩ : syracuseStep 977377 = 733033) (by norm_num)
theorem B1468901 : Blo 868566 1468901 := bbase (se 4 (by rfl) ⟨137709, by rfl⟩ : syracuseStep 1468901 = 275419) (by norm_num)
theorem B1305077 : Blo 868566 1305077 := bbase (se 5 (by rfl) ⟨61175, by rfl⟩ : syracuseStep 1305077 = 122351) (by norm_num)
theorem B977413 : Blo 868566 977413 := bbase (se 4 (by rfl) ⟨91632, by rfl⟩ : syracuseStep 977413 = 183265) (by norm_num)
theorem B1305101 : Blo 868566 1305101 := bbase (se 3 (by rfl) ⟨244706, by rfl⟩ : syracuseStep 1305101 = 489413) (by norm_num)
theorem B1960469 : Blo 868566 1960469 := bbase (se 6 (by rfl) ⟨45948, by rfl⟩ : syracuseStep 1960469 = 91897) (by norm_num)
theorem B1305125 : Blo 868566 1305125 := bbase (se 4 (by rfl) ⟨122355, by rfl⟩ : syracuseStep 1305125 = 244711) (by norm_num)
theorem B977449 : Blo 868566 977449 := bbase (se 2 (by rfl) ⟨366543, by rfl⟩ : syracuseStep 977449 = 733087) (by norm_num)
theorem B1305149 : Blo 868566 1305149 := bbase (se 3 (by rfl) ⟨244715, by rfl⟩ : syracuseStep 1305149 = 489431) (by norm_num)
theorem B977485 : Blo 868566 977485 := bbase (se 3 (by rfl) ⟨183278, by rfl⟩ : syracuseStep 977485 = 366557) (by norm_num)
theorem B1305173 : Blo 868566 1305173 := bbase (se 8 (by rfl) ⟨7647, by rfl⟩ : syracuseStep 1305173 = 15295) (by norm_num)
theorem B1960541 : Blo 868566 1960541 := bbase (se 3 (by rfl) ⟨367601, by rfl⟩ : syracuseStep 1960541 = 735203) (by norm_num)
theorem B1469029 : Blo 868566 1469029 := bbase (se 4 (by rfl) ⟨137721, by rfl⟩ : syracuseStep 1469029 = 275443) (by norm_num)
theorem B4188773 : Blo 868566 4188773 := bbase (se 4 (by rfl) ⟨392697, by rfl⟩ : syracuseStep 4188773 = 785395) (by norm_num)
theorem B1305197 : Blo 868566 1305197 := bbase (se 3 (by rfl) ⟨244724, by rfl⟩ : syracuseStep 1305197 = 489449) (by norm_num)
theorem B977521 : Blo 868566 977521 := bbase (se 2 (by rfl) ⟨366570, by rfl⟩ : syracuseStep 977521 = 733141) (by norm_num)
theorem B1305221 : Blo 868566 1305221 := bbase (se 4 (by rfl) ⟨122364, by rfl⟩ : syracuseStep 1305221 = 244729) (by norm_num)
theorem B977557 : Blo 868566 977557 := bbase (se 6 (by rfl) ⟨22911, by rfl⟩ : syracuseStep 977557 = 45823) (by norm_num)
theorem B1305245 : Blo 868566 1305245 := bbase (se 3 (by rfl) ⟨244733, by rfl⟩ : syracuseStep 1305245 = 489467) (by norm_num)
theorem B1960613 : Blo 868566 1960613 := bbase (se 4 (by rfl) ⟨183807, by rfl⟩ : syracuseStep 1960613 = 367615) (by norm_num)
theorem B1305269 : Blo 868566 1305269 := bbase (se 5 (by rfl) ⟨61184, by rfl⟩ : syracuseStep 1305269 = 122369) (by norm_num)
theorem B1239733 : Blo 868566 1239733 := bbase (se 5 (by rfl) ⟨58112, by rfl⟩ : syracuseStep 1239733 = 116225) (by norm_num)
theorem B977593 : Blo 868566 977593 := bbase (se 2 (by rfl) ⟨366597, by rfl⟩ : syracuseStep 977593 = 733195) (by norm_num)
theorem B1469117 : Blo 868566 1469117 := bbase (se 3 (by rfl) ⟨275459, by rfl⟩ : syracuseStep 1469117 = 550919) (by norm_num)
theorem B1305293 : Blo 868566 1305293 := bbase (se 3 (by rfl) ⟨244742, by rfl⟩ : syracuseStep 1305293 = 489485) (by norm_num)
theorem B2943701 : Blo 868566 2943701 := bbase (se 7 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 2943701 = 68993) (by norm_num)
theorem B977629 : Blo 868566 977629 := bbase (se 3 (by rfl) ⟨183305, by rfl⟩ : syracuseStep 977629 = 366611) (by norm_num)
theorem B1305317 : Blo 868566 1305317 := bbase (se 4 (by rfl) ⟨122373, by rfl⟩ : syracuseStep 1305317 = 244747) (by norm_num)
theorem B1960685 : Blo 868566 1960685 := bbase (se 3 (by rfl) ⟨367628, by rfl⟩ : syracuseStep 1960685 = 735257) (by norm_num)
theorem B1305341 : Blo 868566 1305341 := bbase (se 3 (by rfl) ⟨244751, by rfl⟩ : syracuseStep 1305341 = 489503) (by norm_num)
theorem B977665 : Blo 868566 977665 := bbase (se 2 (by rfl) ⟨366624, by rfl⟩ : syracuseStep 977665 = 733249) (by norm_num)
theorem B1305365 : Blo 868566 1305365 := bbase (se 6 (by rfl) ⟨30594, by rfl⟩ : syracuseStep 1305365 = 61189) (by norm_num)
theorem B977701 : Blo 868566 977701 := bbase (se 4 (by rfl) ⟨91659, by rfl⟩ : syracuseStep 977701 = 183319) (by norm_num)
theorem B1567525 : Blo 868566 1567525 := bbase (se 4 (by rfl) ⟨146955, by rfl⟩ : syracuseStep 1567525 = 293911) (by norm_num)
theorem B1305389 : Blo 868566 1305389 := bbase (se 3 (by rfl) ⟨244760, by rfl⟩ : syracuseStep 1305389 = 489521) (by norm_num)
theorem B1960757 : Blo 868566 1960757 := bbase (se 5 (by rfl) ⟨91910, by rfl⟩ : syracuseStep 1960757 = 183821) (by norm_num)
theorem B1862453 : Blo 868566 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B7269173 : Blo 868566 7269173 := bbase (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) (by norm_num)
theorem B1469245 : Blo 868566 1469245 := bbase (se 3 (by rfl) ⟨275483, by rfl⟩ : syracuseStep 1469245 = 550967) (by norm_num)
theorem B1305413 : Blo 868566 1305413 := bbase (se 4 (by rfl) ⟨122382, by rfl⟩ : syracuseStep 1305413 = 244765) (by norm_num)
theorem B977737 : Blo 868566 977737 := bbase (se 2 (by rfl) ⟨366651, by rfl⟩ : syracuseStep 977737 = 733303) (by norm_num)
theorem B1305437 : Blo 868566 1305437 := bbase (se 3 (by rfl) ⟨244769, by rfl⟩ : syracuseStep 1305437 = 489539) (by norm_num)
theorem B977773 : Blo 868566 977773 := bbase (se 3 (by rfl) ⟨183332, by rfl⟩ : syracuseStep 977773 = 366665) (by norm_num)
theorem B1305461 : Blo 868566 1305461 := bbase (se 5 (by rfl) ⟨61193, by rfl⟩ : syracuseStep 1305461 = 122387) (by norm_num)
theorem B1960829 : Blo 868566 1960829 := bbase (se 3 (by rfl) ⟨367655, by rfl⟩ : syracuseStep 1960829 = 735311) (by norm_num)
theorem B1305485 : Blo 868566 1305485 := bbase (se 3 (by rfl) ⟨244778, by rfl⟩ : syracuseStep 1305485 = 489557) (by norm_num)
theorem B977809 : Blo 868566 977809 := bbase (se 2 (by rfl) ⟨366678, by rfl⟩ : syracuseStep 977809 = 733357) (by norm_num)
theorem B1469333 : Blo 868566 1469333 := bbase (se 6 (by rfl) ⟨34437, by rfl⟩ : syracuseStep 1469333 = 68875) (by norm_num)
theorem B1305509 : Blo 868566 1305509 := bbase (se 4 (by rfl) ⟨122391, by rfl⟩ : syracuseStep 1305509 = 244783) (by norm_num)
theorem B977845 : Blo 868566 977845 := bbase (se 5 (by rfl) ⟨45836, by rfl⟩ : syracuseStep 977845 = 91673) (by norm_num)
theorem B1305533 : Blo 868566 1305533 := bbase (se 3 (by rfl) ⟨244787, by rfl⟩ : syracuseStep 1305533 = 489575) (by norm_num)
theorem B1960901 : Blo 868566 1960901 := bbase (se 4 (by rfl) ⟨183834, by rfl⟩ : syracuseStep 1960901 = 367669) (by norm_num)
theorem B1305557 : Blo 868566 1305557 := bbase (se 7 (by rfl) ⟨15299, by rfl⟩ : syracuseStep 1305557 = 30599) (by norm_num)
theorem B6613973 : Blo 868566 6613973 := bbase (se 7 (by rfl) ⟨77507, by rfl⟩ : syracuseStep 6613973 = 155015) (by norm_num)
theorem B977881 : Blo 868566 977881 := bbase (se 2 (by rfl) ⟨366705, by rfl⟩ : syracuseStep 977881 = 733411) (by norm_num)
theorem B3304421 : Blo 868566 3304421 := bbase (se 4 (by rfl) ⟨309789, by rfl⟩ : syracuseStep 3304421 = 619579) (by norm_num)
theorem B1305581 : Blo 868566 1305581 := bbase (se 3 (by rfl) ⟨244796, by rfl⟩ : syracuseStep 1305581 = 489593) (by norm_num)
theorem B977917 : Blo 868566 977917 := bbase (se 3 (by rfl) ⟨183359, by rfl⟩ : syracuseStep 977917 = 366719) (by norm_num)
theorem B1305605 : Blo 868566 1305605 := bbase (se 4 (by rfl) ⟨122400, by rfl⟩ : syracuseStep 1305605 = 244801) (by norm_num)
theorem B1960973 : Blo 868566 1960973 := bbase (se 3 (by rfl) ⟨367682, by rfl⟩ : syracuseStep 1960973 = 735365) (by norm_num)
theorem B1469461 : Blo 868566 1469461 := bbase (se 6 (by rfl) ⟨34440, by rfl⟩ : syracuseStep 1469461 = 68881) (by norm_num)
theorem B1305629 : Blo 868566 1305629 := bbase (se 3 (by rfl) ⟨244805, by rfl⟩ : syracuseStep 1305629 = 489611) (by norm_num)
theorem B977953 : Blo 868566 977953 := bbase (se 2 (by rfl) ⟨366732, by rfl⟩ : syracuseStep 977953 = 733465) (by norm_num)
theorem B1305653 : Blo 868566 1305653 := bbase (se 5 (by rfl) ⟨61202, by rfl⟩ : syracuseStep 1305653 = 122405) (by norm_num)
theorem B977989 : Blo 868566 977989 := bbase (se 4 (by rfl) ⟨91686, by rfl⟩ : syracuseStep 977989 = 183373) (by norm_num)
theorem B1305677 : Blo 868566 1305677 := bbase (se 3 (by rfl) ⟨244814, by rfl⟩ : syracuseStep 1305677 = 489629) (by norm_num)
theorem B1961045 : Blo 868566 1961045 := bbase (se 8 (by rfl) ⟨11490, by rfl⟩ : syracuseStep 1961045 = 22981) (by norm_num)
theorem B1305701 : Blo 868566 1305701 := bbase (se 4 (by rfl) ⟨122409, by rfl⟩ : syracuseStep 1305701 = 244819) (by norm_num)
theorem B978025 : Blo 868566 978025 := bbase (se 2 (by rfl) ⟨366759, by rfl⟩ : syracuseStep 978025 = 733519) (by norm_num)
theorem B1174637 : Blo 868566 1174637 := bbase (se 3 (by rfl) ⟨220244, by rfl⟩ : syracuseStep 1174637 = 440489) (by norm_num)
theorem B1469549 : Blo 868566 1469549 := bbase (se 3 (by rfl) ⟨275540, by rfl⟩ : syracuseStep 1469549 = 551081) (by norm_num)
theorem B1305725 : Blo 868566 1305725 := bbase (se 3 (by rfl) ⟨244823, by rfl⟩ : syracuseStep 1305725 = 489647) (by norm_num)
theorem B2944133 : Blo 868566 2944133 := bbase (se 4 (by rfl) ⟨276012, by rfl⟩ : syracuseStep 2944133 = 552025) (by norm_num)
theorem B978061 : Blo 868566 978061 := bbase (se 3 (by rfl) ⟨183386, by rfl⟩ : syracuseStep 978061 = 366773) (by norm_num)
theorem B1305749 : Blo 868566 1305749 := bbase (se 6 (by rfl) ⟨30603, by rfl⟩ : syracuseStep 1305749 = 61207) (by norm_num)
theorem B1961117 : Blo 868566 1961117 := bbase (se 3 (by rfl) ⟨367709, by rfl⟩ : syracuseStep 1961117 = 735419) (by norm_num)
theorem B1305773 : Blo 868566 1305773 := bbase (se 3 (by rfl) ⟨244832, by rfl⟩ : syracuseStep 1305773 = 489665) (by norm_num)
theorem B978097 : Blo 868566 978097 := bbase (se 2 (by rfl) ⟨366786, by rfl⟩ : syracuseStep 978097 = 733573) (by norm_num)
theorem B1305797 : Blo 868566 1305797 := bbase (se 4 (by rfl) ⟨122418, by rfl⟩ : syracuseStep 1305797 = 244837) (by norm_num)
theorem B2387141 : Blo 868566 2387141 := bbase (se 4 (by rfl) ⟨223794, by rfl⟩ : syracuseStep 2387141 = 447589) (by norm_num)
theorem B978133 : Blo 868566 978133 := bbase (se 7 (by rfl) ⟨11462, by rfl⟩ : syracuseStep 978133 = 22925) (by norm_num)
theorem B1305821 : Blo 868566 1305821 := bbase (se 3 (by rfl) ⟨244841, by rfl⟩ : syracuseStep 1305821 = 489683) (by norm_num)
theorem B1961189 : Blo 868566 1961189 := bbase (se 4 (by rfl) ⟨183861, by rfl⟩ : syracuseStep 1961189 = 367723) (by norm_num)
theorem B1469677 : Blo 868566 1469677 := bbase (se 3 (by rfl) ⟨275564, by rfl⟩ : syracuseStep 1469677 = 551129) (by norm_num)
theorem B1305845 : Blo 868566 1305845 := bbase (se 5 (by rfl) ⟨61211, by rfl⟩ : syracuseStep 1305845 = 122423) (by norm_num)
theorem B978169 : Blo 868566 978169 := bbase (se 2 (by rfl) ⟨366813, by rfl⟩ : syracuseStep 978169 = 733627) (by norm_num)
theorem B3304709 : Blo 868566 3304709 := bbase (se 4 (by rfl) ⟨309816, by rfl⟩ : syracuseStep 3304709 = 619633) (by norm_num)
theorem B1305869 : Blo 868566 1305869 := bbase (se 3 (by rfl) ⟨244850, by rfl⟩ : syracuseStep 1305869 = 489701) (by norm_num)
theorem B3534101 : Blo 868566 3534101 := bbase (se 6 (by rfl) ⟨82830, by rfl⟩ : syracuseStep 3534101 = 165661) (by norm_num)
theorem B978205 : Blo 868566 978205 := bbase (se 3 (by rfl) ⟨183413, by rfl⟩ : syracuseStep 978205 = 366827) (by norm_num)
theorem B3763493 : Blo 868566 3763493 := bbase (se 4 (by rfl) ⟨352827, by rfl⟩ : syracuseStep 3763493 = 705655) (by norm_num)
theorem B1305893 : Blo 868566 1305893 := bbase (se 4 (by rfl) ⟨122427, by rfl⟩ : syracuseStep 1305893 = 244855) (by norm_num)
theorem B1961261 : Blo 868566 1961261 := bbase (se 3 (by rfl) ⟨367736, by rfl⟩ : syracuseStep 1961261 = 735473) (by norm_num)
theorem B1305917 : Blo 868566 1305917 := bbase (se 3 (by rfl) ⟨244859, by rfl⟩ : syracuseStep 1305917 = 489719) (by norm_num)
theorem B978241 : Blo 868566 978241 := bbase (se 2 (by rfl) ⟨366840, by rfl⟩ : syracuseStep 978241 = 733681) (by norm_num)
theorem B1469765 : Blo 868566 1469765 := bbase (se 4 (by rfl) ⟨137790, by rfl⟩ : syracuseStep 1469765 = 275581) (by norm_num)
theorem B1305941 : Blo 868566 1305941 := bbase (se 11 (by rfl) ⟨956, by rfl⟩ : syracuseStep 1305941 = 1913) (by norm_num)
theorem B978277 : Blo 868566 978277 := bbase (se 4 (by rfl) ⟨91713, by rfl⟩ : syracuseStep 978277 = 183427) (by norm_num)
theorem B1305965 : Blo 868566 1305965 := bbase (se 3 (by rfl) ⟨244868, by rfl⟩ : syracuseStep 1305965 = 489737) (by norm_num)
theorem B1961333 : Blo 868566 1961333 := bbase (se 5 (by rfl) ⟨91937, by rfl⟩ : syracuseStep 1961333 = 183875) (by norm_num)
theorem B1305989 : Blo 868566 1305989 := bbase (se 4 (by rfl) ⟨122436, by rfl⟩ : syracuseStep 1305989 = 244873) (by norm_num)
theorem B978313 : Blo 868566 978313 := bbase (se 2 (by rfl) ⟨366867, by rfl⟩ : syracuseStep 978313 = 733735) (by norm_num)
theorem B1306013 : Blo 868566 1306013 := bbase (se 3 (by rfl) ⟨244877, by rfl⟩ : syracuseStep 1306013 = 489755) (by norm_num)
theorem B978349 : Blo 868566 978349 := bbase (se 3 (by rfl) ⟨183440, by rfl⟩ : syracuseStep 978349 = 366881) (by norm_num)
theorem B1306037 : Blo 868566 1306037 := bbase (se 5 (by rfl) ⟨61220, by rfl⟩ : syracuseStep 1306037 = 122441) (by norm_num)
theorem B1961405 : Blo 868566 1961405 := bbase (se 3 (by rfl) ⟨367763, by rfl⟩ : syracuseStep 1961405 = 735527) (by norm_num)
theorem B1469893 : Blo 868566 1469893 := bbase (se 4 (by rfl) ⟨137802, by rfl⟩ : syracuseStep 1469893 = 275605) (by norm_num)
theorem B1306061 : Blo 868566 1306061 := bbase (se 3 (by rfl) ⟨244886, by rfl⟩ : syracuseStep 1306061 = 489773) (by norm_num)
theorem B2092493 : Blo 868566 2092493 := bbase (se 3 (by rfl) ⟨392342, by rfl⟩ : syracuseStep 2092493 = 784685) (by norm_num)
theorem B1240525 : Blo 868566 1240525 := bbase (se 3 (by rfl) ⟨232598, by rfl⟩ : syracuseStep 1240525 = 465197) (by norm_num)
theorem B978385 : Blo 868566 978385 := bbase (se 2 (by rfl) ⟨366894, by rfl⟩ : syracuseStep 978385 = 733789) (by norm_num)
theorem B1306085 : Blo 868566 1306085 := bbase (se 4 (by rfl) ⟨122445, by rfl⟩ : syracuseStep 1306085 = 244891) (by norm_num)
theorem B978421 : Blo 868566 978421 := bbase (se 5 (by rfl) ⟨45863, by rfl⟩ : syracuseStep 978421 = 91727) (by norm_num)
theorem B1633781 : Blo 868566 1633781 := bbase (se 5 (by rfl) ⟨76583, by rfl⟩ : syracuseStep 1633781 = 153167) (by norm_num)
theorem B1306109 : Blo 868566 1306109 := bbase (se 3 (by rfl) ⟨244895, by rfl⟩ : syracuseStep 1306109 = 489791) (by norm_num)
theorem B1961477 : Blo 868566 1961477 := bbase (se 4 (by rfl) ⟨183888, by rfl⟩ : syracuseStep 1961477 = 367777) (by norm_num)
theorem B1306133 : Blo 868566 1306133 := bbase (se 6 (by rfl) ⟨30612, by rfl⟩ : syracuseStep 1306133 = 61225) (by norm_num)
theorem B978457 : Blo 868566 978457 := bbase (se 2 (by rfl) ⟨366921, by rfl⟩ : syracuseStep 978457 = 733843) (by norm_num)
theorem B1469981 : Blo 868566 1469981 := bbase (se 3 (by rfl) ⟨275621, by rfl⟩ : syracuseStep 1469981 = 551243) (by norm_num)
theorem B1306157 : Blo 868566 1306157 := bbase (se 3 (by rfl) ⟨244904, by rfl⟩ : syracuseStep 1306157 = 489809) (by norm_num)
theorem B2944565 : Blo 868566 2944565 := bbase (se 5 (by rfl) ⟨138026, by rfl⟩ : syracuseStep 2944565 = 276053) (by norm_num)
theorem B978493 : Blo 868566 978493 := bbase (se 3 (by rfl) ⟨183467, by rfl⟩ : syracuseStep 978493 = 366935) (by norm_num)
theorem B1568317 : Blo 868566 1568317 := bbase (se 3 (by rfl) ⟨294059, by rfl⟩ : syracuseStep 1568317 = 588119) (by norm_num)
theorem B1306181 : Blo 868566 1306181 := bbase (se 4 (by rfl) ⟨122454, by rfl⟩ : syracuseStep 1306181 = 244909) (by norm_num)
theorem B1961549 : Blo 868566 1961549 := bbase (se 3 (by rfl) ⟨367790, by rfl⟩ : syracuseStep 1961549 = 735581) (by norm_num)
theorem B1306205 : Blo 868566 1306205 := bbase (se 3 (by rfl) ⟨244913, by rfl⟩ : syracuseStep 1306205 = 489827) (by norm_num)
theorem B978529 : Blo 868566 978529 := bbase (se 2 (by rfl) ⟨366948, by rfl⟩ : syracuseStep 978529 = 733897) (by norm_num)
theorem B1306229 : Blo 868566 1306229 := bbase (se 5 (by rfl) ⟨61229, by rfl⟩ : syracuseStep 1306229 = 122459) (by norm_num)
theorem B978565 : Blo 868566 978565 := bbase (se 4 (by rfl) ⟨91740, by rfl⟩ : syracuseStep 978565 = 183481) (by norm_num)
theorem B1306253 : Blo 868566 1306253 := bbase (se 3 (by rfl) ⟨244922, by rfl⟩ : syracuseStep 1306253 = 489845) (by norm_num)
theorem B1961621 : Blo 868566 1961621 := bbase (se 6 (by rfl) ⟨45975, by rfl⟩ : syracuseStep 1961621 = 91951) (by norm_num)
theorem B1863317 : Blo 868566 1863317 := bbase (se 6 (by rfl) ⟨43671, by rfl⟩ : syracuseStep 1863317 = 87343) (by norm_num)
theorem B1470109 : Blo 868566 1470109 := bbase (se 3 (by rfl) ⟨275645, by rfl⟩ : syracuseStep 1470109 = 551291) (by norm_num)
theorem B1306277 : Blo 868566 1306277 := bbase (se 4 (by rfl) ⟨122463, by rfl⟩ : syracuseStep 1306277 = 244927) (by norm_num)
theorem B978601 : Blo 868566 978601 := bbase (se 2 (by rfl) ⟨366975, by rfl⟩ : syracuseStep 978601 = 733951) (by norm_num)
theorem B1306301 : Blo 868566 1306301 := bbase (se 3 (by rfl) ⟨244931, by rfl⟩ : syracuseStep 1306301 = 489863) (by norm_num)
theorem B978637 : Blo 868566 978637 := bbase (se 3 (by rfl) ⟨183494, by rfl⟩ : syracuseStep 978637 = 366989) (by norm_num)
theorem B1306325 : Blo 868566 1306325 := bbase (se 7 (by rfl) ⟨15308, by rfl⟩ : syracuseStep 1306325 = 30617) (by norm_num)
theorem B1961693 : Blo 868566 1961693 := bbase (se 3 (by rfl) ⟨367817, by rfl⟩ : syracuseStep 1961693 = 735635) (by norm_num)
theorem B1306349 : Blo 868566 1306349 := bbase (se 3 (by rfl) ⟨244940, by rfl⟩ : syracuseStep 1306349 = 489881) (by norm_num)
theorem B1044209 : Blo 868566 1044209 := bbase (se 2 (by rfl) ⟨391578, by rfl⟩ : syracuseStep 1044209 = 783157) (by norm_num)
theorem B978673 : Blo 868566 978673 := bbase (se 2 (by rfl) ⟨367002, by rfl⟩ : syracuseStep 978673 = 734005) (by norm_num)
theorem B1470197 : Blo 868566 1470197 := bbase (se 5 (by rfl) ⟨68915, by rfl⟩ : syracuseStep 1470197 = 137831) (by norm_num)
theorem B1306373 : Blo 868566 1306373 := bbase (se 4 (by rfl) ⟨122472, by rfl⟩ : syracuseStep 1306373 = 244945) (by norm_num)
theorem B978709 : Blo 868566 978709 := bbase (se 6 (by rfl) ⟨22938, by rfl⟩ : syracuseStep 978709 = 45877) (by norm_num)
theorem B1306397 : Blo 868566 1306397 := bbase (se 3 (by rfl) ⟨244949, by rfl⟩ : syracuseStep 1306397 = 489899) (by norm_num)
theorem B1240861 : Blo 868566 1240861 := bbase (se 3 (by rfl) ⟨232661, by rfl⟩ : syracuseStep 1240861 = 465323) (by norm_num)
theorem B1961765 : Blo 868566 1961765 := bbase (se 4 (by rfl) ⟨183915, by rfl⟩ : syracuseStep 1961765 = 367831) (by norm_num)
theorem B1863461 : Blo 868566 1863461 := bbase (se 4 (by rfl) ⟨174699, by rfl⟩ : syracuseStep 1863461 = 349399) (by norm_num)
theorem B1306421 : Blo 868566 1306421 := bbase (se 5 (by rfl) ⟨61238, by rfl⟩ : syracuseStep 1306421 = 122477) (by norm_num)
theorem B978745 : Blo 868566 978745 := bbase (se 2 (by rfl) ⟨367029, by rfl⟩ : syracuseStep 978745 = 734059) (by norm_num)
theorem B1306445 : Blo 868566 1306445 := bbase (se 3 (by rfl) ⟨244958, by rfl⟩ : syracuseStep 1306445 = 489917) (by norm_num)
theorem B978781 : Blo 868566 978781 := bbase (se 3 (by rfl) ⟨183521, by rfl⟩ : syracuseStep 978781 = 367043) (by norm_num)
theorem B1306469 : Blo 868566 1306469 := bbase (se 4 (by rfl) ⟨122481, by rfl⟩ : syracuseStep 1306469 = 244963) (by norm_num)
theorem B1568621 : Blo 868566 1568621 := bbase (se 3 (by rfl) ⟨294116, by rfl⟩ : syracuseStep 1568621 = 588233) (by norm_num)
theorem B1961837 : Blo 868566 1961837 := bbase (se 3 (by rfl) ⟨367844, by rfl⟩ : syracuseStep 1961837 = 735689) (by norm_num)
theorem B6352757 : Blo 868566 6352757 := bbase (se 5 (by rfl) ⟨297785, by rfl⟩ : syracuseStep 6352757 = 595571) (by norm_num)
theorem B1470325 : Blo 868566 1470325 := bbase (se 5 (by rfl) ⟨68921, by rfl⟩ : syracuseStep 1470325 = 137843) (by norm_num)
theorem B1306493 : Blo 868566 1306493 := bbase (se 3 (by rfl) ⟨244967, by rfl⟩ : syracuseStep 1306493 = 489935) (by norm_num)
theorem B2092925 : Blo 868566 2092925 := bbase (se 3 (by rfl) ⟨392423, by rfl⟩ : syracuseStep 2092925 = 784847) (by norm_num)
theorem B978817 : Blo 868566 978817 := bbase (se 2 (by rfl) ⟨367056, by rfl⟩ : syracuseStep 978817 = 734113) (by norm_num)
theorem B2977669 : Blo 868566 2977669 := bbase (se 4 (by rfl) ⟨279156, by rfl⟩ : syracuseStep 2977669 = 558313) (by norm_num)
theorem B1306517 : Blo 868566 1306517 := bbase (se 6 (by rfl) ⟨30621, by rfl⟩ : syracuseStep 1306517 = 61243) (by norm_num)
theorem B978853 : Blo 868566 978853 := bbase (se 4 (by rfl) ⟨91767, by rfl⟩ : syracuseStep 978853 = 183535) (by norm_num)
theorem B1306541 : Blo 868566 1306541 := bbase (se 3 (by rfl) ⟨244976, by rfl⟩ : syracuseStep 1306541 = 489953) (by norm_num)
theorem B1961909 : Blo 868566 1961909 := bbase (se 5 (by rfl) ⟨91964, by rfl⟩ : syracuseStep 1961909 = 183929) (by norm_num)
theorem B1306565 : Blo 868566 1306565 := bbase (se 4 (by rfl) ⟨122490, by rfl⟩ : syracuseStep 1306565 = 244981) (by norm_num)
theorem B978889 : Blo 868566 978889 := bbase (se 2 (by rfl) ⟨367083, by rfl⟩ : syracuseStep 978889 = 734167) (by norm_num)
theorem B1470413 : Blo 868566 1470413 := bbase (se 3 (by rfl) ⟨275702, by rfl⟩ : syracuseStep 1470413 = 551405) (by norm_num)
theorem B1306589 : Blo 868566 1306589 := bbase (se 3 (by rfl) ⟨244985, by rfl⟩ : syracuseStep 1306589 = 489971) (by norm_num)
theorem B978925 : Blo 868566 978925 := bbase (se 3 (by rfl) ⟨183548, by rfl⟩ : syracuseStep 978925 = 367097) (by norm_num)
theorem B1306613 : Blo 868566 1306613 := bbase (se 5 (by rfl) ⟨61247, by rfl⟩ : syracuseStep 1306613 = 122495) (by norm_num)
theorem B1241077 : Blo 868566 1241077 := bbase (se 5 (by rfl) ⟨58175, by rfl⟩ : syracuseStep 1241077 = 116351) (by norm_num)
theorem B1961981 : Blo 868566 1961981 := bbase (se 3 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 1961981 = 735743) (by norm_num)
theorem B1306637 : Blo 868566 1306637 := bbase (se 3 (by rfl) ⟨244994, by rfl⟩ : syracuseStep 1306637 = 489989) (by norm_num)
theorem B978961 : Blo 868566 978961 := bbase (se 2 (by rfl) ⟨367110, by rfl⟩ : syracuseStep 978961 = 734221) (by norm_num)
theorem B1044517 : Blo 868566 1044517 := bbase (se 4 (by rfl) ⟨97923, by rfl⟩ : syracuseStep 1044517 = 195847) (by norm_num)
theorem B1306661 : Blo 868566 1306661 := bbase (se 4 (by rfl) ⟨122499, by rfl⟩ : syracuseStep 1306661 = 244999) (by norm_num)
theorem B978997 : Blo 868566 978997 := bbase (se 5 (by rfl) ⟨45890, by rfl⟩ : syracuseStep 978997 = 91781) (by norm_num)
theorem B1306685 : Blo 868566 1306685 := bbase (se 3 (by rfl) ⟨245003, by rfl⟩ : syracuseStep 1306685 = 490007) (by norm_num)
theorem B1962053 : Blo 868566 1962053 := bbase (se 4 (by rfl) ⟨183942, by rfl⟩ : syracuseStep 1962053 = 367885) (by norm_num)
theorem B1470541 : Blo 868566 1470541 := bbase (se 3 (by rfl) ⟨275726, by rfl⟩ : syracuseStep 1470541 = 551453) (by norm_num)
theorem B1306709 : Blo 868566 1306709 := bbase (se 8 (by rfl) ⟨7656, by rfl⟩ : syracuseStep 1306709 = 15313) (by norm_num)
theorem B979033 : Blo 868566 979033 := bbase (se 2 (by rfl) ⟨367137, by rfl⟩ : syracuseStep 979033 = 734275) (by norm_num)
theorem B1306733 : Blo 868566 1306733 := bbase (se 3 (by rfl) ⟨245012, by rfl⟩ : syracuseStep 1306733 = 490025) (by norm_num)
theorem B979069 : Blo 868566 979069 := bbase (se 3 (by rfl) ⟨183575, by rfl⟩ : syracuseStep 979069 = 367151) (by norm_num)
theorem B1306757 : Blo 868566 1306757 := bbase (se 4 (by rfl) ⟨122508, by rfl⟩ : syracuseStep 1306757 = 245017) (by norm_num)
theorem B1568909 : Blo 868566 1568909 := bbase (se 3 (by rfl) ⟨294170, by rfl⟩ : syracuseStep 1568909 = 588341) (by norm_num)
theorem B1962125 : Blo 868566 1962125 := bbase (se 3 (by rfl) ⟨367898, by rfl⟩ : syracuseStep 1962125 = 735797) (by norm_num)
theorem B1306781 : Blo 868566 1306781 := bbase (se 3 (by rfl) ⟨245021, by rfl⟩ : syracuseStep 1306781 = 490043) (by norm_num)
theorem B979105 : Blo 868566 979105 := bbase (se 2 (by rfl) ⟨367164, by rfl⟩ : syracuseStep 979105 = 734329) (by norm_num)
theorem B1470629 : Blo 868566 1470629 := bbase (se 4 (by rfl) ⟨137871, by rfl⟩ : syracuseStep 1470629 = 275743) (by norm_num)
theorem B1306805 : Blo 868566 1306805 := bbase (se 5 (by rfl) ⟨61256, by rfl⟩ : syracuseStep 1306805 = 122513) (by norm_num)
theorem B979141 : Blo 868566 979141 := bbase (se 4 (by rfl) ⟨91794, by rfl⟩ : syracuseStep 979141 = 183589) (by norm_num)
theorem B1306829 : Blo 868566 1306829 := bbase (se 3 (by rfl) ⟨245030, by rfl⟩ : syracuseStep 1306829 = 490061) (by norm_num)
theorem B1962197 : Blo 868566 1962197 := bbase (se 7 (by rfl) ⟨22994, by rfl⟩ : syracuseStep 1962197 = 45989) (by norm_num)
theorem B1306853 : Blo 868566 1306853 := bbase (se 4 (by rfl) ⟨122517, by rfl⟩ : syracuseStep 1306853 = 245035) (by norm_num)
theorem B979177 : Blo 868566 979177 := bbase (se 2 (by rfl) ⟨367191, by rfl⟩ : syracuseStep 979177 = 734383) (by norm_num)
theorem B880877 : Blo 868566 880877 := bbase (se 3 (by rfl) ⟨165164, by rfl⟩ : syracuseStep 880877 = 330329) (by norm_num)
theorem B1044733 : Blo 868566 1044733 := bbase (se 3 (by rfl) ⟨195887, by rfl⟩ : syracuseStep 1044733 = 391775) (by norm_num)
theorem B1306877 : Blo 868566 1306877 := bbase (se 3 (by rfl) ⟨245039, by rfl⟩ : syracuseStep 1306877 = 490079) (by norm_num)
theorem B979213 : Blo 868566 979213 := bbase (se 3 (by rfl) ⟨183602, by rfl⟩ : syracuseStep 979213 = 367205) (by norm_num)
theorem B1306901 : Blo 868566 1306901 := bbase (se 6 (by rfl) ⟨30630, by rfl⟩ : syracuseStep 1306901 = 61261) (by norm_num)
theorem B1962269 : Blo 868566 1962269 := bbase (se 3 (by rfl) ⟨367925, by rfl⟩ : syracuseStep 1962269 = 735851) (by norm_num)
theorem B1470757 : Blo 868566 1470757 := bbase (se 4 (by rfl) ⟨137883, by rfl⟩ : syracuseStep 1470757 = 275767) (by norm_num)
theorem B1306925 : Blo 868566 1306925 := bbase (se 3 (by rfl) ⟨245048, by rfl⟩ : syracuseStep 1306925 = 490097) (by norm_num)
theorem B979249 : Blo 868566 979249 := bbase (se 2 (by rfl) ⟨367218, by rfl⟩ : syracuseStep 979249 = 734437) (by norm_num)
theorem B1306949 : Blo 868566 1306949 := bbase (se 4 (by rfl) ⟨122526, by rfl⟩ : syracuseStep 1306949 = 245053) (by norm_num)
theorem B5566805 : Blo 868566 5566805 := bbase (se 10 (by rfl) ⟨8154, by rfl⟩ : syracuseStep 5566805 = 16309) (by norm_num)
theorem B979285 : Blo 868566 979285 := bbase (se 10 (by rfl) ⟨1434, by rfl⟩ : syracuseStep 979285 = 2869) (by norm_num)
theorem B1306973 : Blo 868566 1306973 := bbase (se 3 (by rfl) ⟨245057, by rfl⟩ : syracuseStep 1306973 = 490115) (by norm_num)
theorem B1962341 : Blo 868566 1962341 := bbase (se 4 (by rfl) ⟨183969, by rfl⟩ : syracuseStep 1962341 = 367939) (by norm_num)
theorem B1241453 : Blo 868566 1241453 := bbase (se 3 (by rfl) ⟨232772, by rfl⟩ : syracuseStep 1241453 = 465545) (by norm_num)
theorem B1306997 : Blo 868566 1306997 := bbase (se 5 (by rfl) ⟨61265, by rfl⟩ : syracuseStep 1306997 = 122531) (by norm_num)
theorem B979321 : Blo 868566 979321 := bbase (se 2 (by rfl) ⟨367245, by rfl⟩ : syracuseStep 979321 = 734491) (by norm_num)
theorem B1470845 : Blo 868566 1470845 := bbase (se 3 (by rfl) ⟨275783, by rfl⟩ : syracuseStep 1470845 = 551567) (by norm_num)
theorem B2355589 : Blo 868566 2355589 := bbase (se 4 (by rfl) ⟨220836, by rfl⟩ : syracuseStep 2355589 = 441673) (by norm_num)
theorem B1307021 : Blo 868566 1307021 := bbase (se 3 (by rfl) ⟨245066, by rfl⟩ : syracuseStep 1307021 = 490133) (by norm_num)
theorem B979357 : Blo 868566 979357 := bbase (se 3 (by rfl) ⟨183629, by rfl⟩ : syracuseStep 979357 = 367259) (by norm_num)
theorem B3305893 : Blo 868566 3305893 := bbase (se 4 (by rfl) ⟨309927, by rfl⟩ : syracuseStep 3305893 = 619855) (by norm_num)
theorem B1307045 : Blo 868566 1307045 := bbase (se 4 (by rfl) ⟨122535, by rfl⟩ : syracuseStep 1307045 = 245071) (by norm_num)
theorem B1962413 : Blo 868566 1962413 := bbase (se 3 (by rfl) ⟨367952, by rfl⟩ : syracuseStep 1962413 = 735905) (by norm_num)
theorem B1307069 : Blo 868566 1307069 := bbase (se 3 (by rfl) ⟨245075, by rfl⟩ : syracuseStep 1307069 = 490151) (by norm_num)
theorem B979393 : Blo 868566 979393 := bbase (se 2 (by rfl) ⟨367272, by rfl⟩ : syracuseStep 979393 = 734545) (by norm_num)
theorem B1307093 : Blo 868566 1307093 := bbase (se 7 (by rfl) ⟨15317, by rfl⟩ : syracuseStep 1307093 = 30635) (by norm_num)
theorem B979429 : Blo 868566 979429 := bbase (se 4 (by rfl) ⟨91821, by rfl⟩ : syracuseStep 979429 = 183643) (by norm_num)
theorem B1307117 : Blo 868566 1307117 := bbase (se 3 (by rfl) ⟨245084, by rfl⟩ : syracuseStep 1307117 = 490169) (by norm_num)
theorem B1962485 : Blo 868566 1962485 := bbase (se 5 (by rfl) ⟨91991, by rfl⟩ : syracuseStep 1962485 = 183983) (by norm_num)
theorem B1470973 : Blo 868566 1470973 := bbase (se 3 (by rfl) ⟨275807, by rfl⟩ : syracuseStep 1470973 = 551615) (by norm_num)
theorem B1307141 : Blo 868566 1307141 := bbase (se 4 (by rfl) ⟨122544, by rfl⟩ : syracuseStep 1307141 = 245089) (by norm_num)
theorem B979465 : Blo 868566 979465 := bbase (se 2 (by rfl) ⟨367299, by rfl⟩ : syracuseStep 979465 = 734599) (by norm_num)
theorem B1307165 : Blo 868566 1307165 := bbase (se 3 (by rfl) ⟨245093, by rfl⟩ : syracuseStep 1307165 = 490187) (by norm_num)
theorem B979501 : Blo 868566 979501 := bbase (se 3 (by rfl) ⟨183656, by rfl⟩ : syracuseStep 979501 = 367313) (by norm_num)
theorem B1307189 : Blo 868566 1307189 := bbase (se 5 (by rfl) ⟨61274, by rfl⟩ : syracuseStep 1307189 = 122549) (by norm_num)
theorem B1962557 : Blo 868566 1962557 := bbase (se 3 (by rfl) ⟨367979, by rfl⟩ : syracuseStep 1962557 = 735959) (by norm_num)
theorem B1307213 : Blo 868566 1307213 := bbase (se 3 (by rfl) ⟨245102, by rfl⟩ : syracuseStep 1307213 = 490205) (by norm_num)
theorem B979537 : Blo 868566 979537 := bbase (se 2 (by rfl) ⟨367326, by rfl⟩ : syracuseStep 979537 = 734653) (by norm_num)
theorem B1471061 : Blo 868566 1471061 := bbase (se 8 (by rfl) ⟨8619, by rfl⟩ : syracuseStep 1471061 = 17239) (by norm_num)
theorem B1307237 : Blo 868566 1307237 := bbase (se 4 (by rfl) ⟨122553, by rfl⟩ : syracuseStep 1307237 = 245107) (by norm_num)
theorem B979573 : Blo 868566 979573 := bbase (se 5 (by rfl) ⟨45917, by rfl⟩ : syracuseStep 979573 = 91835) (by norm_num)
theorem B1307261 : Blo 868566 1307261 := bbase (se 3 (by rfl) ⟨245111, by rfl⟩ : syracuseStep 1307261 = 490223) (by norm_num)
theorem B1962629 : Blo 868566 1962629 := bbase (se 4 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 1962629 = 367993) (by norm_num)
theorem B1307285 : Blo 868566 1307285 := bbase (se 6 (by rfl) ⟨30639, by rfl⟩ : syracuseStep 1307285 = 61279) (by norm_num)
theorem B2388629 : Blo 868566 2388629 := bbase (se 6 (by rfl) ⟨55983, by rfl⟩ : syracuseStep 2388629 = 111967) (by norm_num)
theorem B979609 : Blo 868566 979609 := bbase (se 2 (by rfl) ⟨367353, by rfl⟩ : syracuseStep 979609 = 734707) (by norm_num)
theorem B3535525 : Blo 868566 3535525 := bbase (se 4 (by rfl) ⟨331455, by rfl⟩ : syracuseStep 3535525 = 662911) (by norm_num)
theorem B1307309 : Blo 868566 1307309 := bbase (se 3 (by rfl) ⟨245120, by rfl⟩ : syracuseStep 1307309 = 490241) (by norm_num)
theorem B979645 : Blo 868566 979645 := bbase (se 3 (by rfl) ⟨183683, by rfl⟩ : syracuseStep 979645 = 367367) (by norm_num)
theorem B1307333 : Blo 868566 1307333 := bbase (se 4 (by rfl) ⟨122562, by rfl⟩ : syracuseStep 1307333 = 245125) (by norm_num)
theorem B1962701 : Blo 868566 1962701 := bbase (se 3 (by rfl) ⟨368006, by rfl⟩ : syracuseStep 1962701 = 736013) (by norm_num)
theorem B3306197 : Blo 868566 3306197 := bbase (se 7 (by rfl) ⟨38744, by rfl⟩ : syracuseStep 3306197 = 77489) (by norm_num)
theorem B1471189 : Blo 868566 1471189 := bbase (se 7 (by rfl) ⟨17240, by rfl⟩ : syracuseStep 1471189 = 34481) (by norm_num)
theorem B1307357 : Blo 868566 1307357 := bbase (se 3 (by rfl) ⟨245129, by rfl⟩ : syracuseStep 1307357 = 490259) (by norm_num)
theorem B979681 : Blo 868566 979681 := bbase (se 2 (by rfl) ⟨367380, by rfl⟩ : syracuseStep 979681 = 734761) (by norm_num)
theorem B1307381 : Blo 868566 1307381 := bbase (se 5 (by rfl) ⟨61283, by rfl⟩ : syracuseStep 1307381 = 122567) (by norm_num)
theorem B979717 : Blo 868566 979717 := bbase (se 4 (by rfl) ⟨91848, by rfl⟩ : syracuseStep 979717 = 183697) (by norm_num)
theorem B1307405 : Blo 868566 1307405 := bbase (se 3 (by rfl) ⟨245138, by rfl⟩ : syracuseStep 1307405 = 490277) (by norm_num)
theorem B1766165 : Blo 868566 1766165 := bbase (se 6 (by rfl) ⟨41394, by rfl⟩ : syracuseStep 1766165 = 82789) (by norm_num)
theorem B1962773 : Blo 868566 1962773 := bbase (se 6 (by rfl) ⟨46002, by rfl⟩ : syracuseStep 1962773 = 92005) (by norm_num)
theorem B1307429 : Blo 868566 1307429 := bbase (se 4 (by rfl) ⟨122571, by rfl⟩ : syracuseStep 1307429 = 245143) (by norm_num)
theorem B979753 : Blo 868566 979753 := bbase (se 2 (by rfl) ⟨367407, by rfl⟩ : syracuseStep 979753 = 734815) (by norm_num)
theorem B1471277 : Blo 868566 1471277 := bbase (se 3 (by rfl) ⟨275864, by rfl⟩ : syracuseStep 1471277 = 551729) (by norm_num)
theorem B1307453 : Blo 868566 1307453 := bbase (se 3 (by rfl) ⟨245147, by rfl⟩ : syracuseStep 1307453 = 490295) (by norm_num)
theorem B979789 : Blo 868566 979789 := bbase (se 3 (by rfl) ⟨183710, by rfl⟩ : syracuseStep 979789 = 367421) (by norm_num)
theorem B1045333 : Blo 868566 1045333 := bbase (se 9 (by rfl) ⟨3062, by rfl⟩ : syracuseStep 1045333 = 6125) (by norm_num)
theorem B1307477 : Blo 868566 1307477 := bbase (se 9 (by rfl) ⟨3830, by rfl⟩ : syracuseStep 1307477 = 7661) (by norm_num)
theorem B5665621 : Blo 868566 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B881497 : Blo 868566 881497 := bbase (se 2 (by rfl) ⟨330561, by rfl⟩ : syracuseStep 881497 = 661123) (by norm_num)
theorem B1962845 : Blo 868566 1962845 := bbase (se 3 (by rfl) ⟨368033, by rfl⟩ : syracuseStep 1962845 = 736067) (by norm_num)
theorem B1307501 : Blo 868566 1307501 := bbase (se 3 (by rfl) ⟨245156, by rfl⟩ : syracuseStep 1307501 = 490313) (by norm_num)
theorem B979825 : Blo 868566 979825 := bbase (se 2 (by rfl) ⟨367434, by rfl⟩ : syracuseStep 979825 = 734869) (by norm_num)
theorem B1307525 : Blo 868566 1307525 := bbase (se 4 (by rfl) ⟨122580, by rfl⟩ : syracuseStep 1307525 = 245161) (by norm_num)
theorem B979861 : Blo 868566 979861 := bbase (se 6 (by rfl) ⟨22965, by rfl⟩ : syracuseStep 979861 = 45931) (by norm_num)
theorem B1307549 : Blo 868566 1307549 := bbase (se 3 (by rfl) ⟨245165, by rfl⟩ : syracuseStep 1307549 = 490331) (by norm_num)
theorem B1700765 : Blo 868566 1700765 := bbase (se 3 (by rfl) ⟨318893, by rfl⟩ : syracuseStep 1700765 = 637787) (by norm_num)
theorem B1569701 : Blo 868566 1569701 := bbase (se 4 (by rfl) ⟨147159, by rfl⟩ : syracuseStep 1569701 = 294319) (by norm_num)
theorem B1962917 : Blo 868566 1962917 := bbase (se 4 (by rfl) ⟨184023, by rfl⟩ : syracuseStep 1962917 = 368047) (by norm_num)
theorem B1471405 : Blo 868566 1471405 := bbase (se 3 (by rfl) ⟨275888, by rfl⟩ : syracuseStep 1471405 = 551777) (by norm_num)
theorem B1307573 : Blo 868566 1307573 := bbase (se 5 (by rfl) ⟨61292, by rfl⟩ : syracuseStep 1307573 = 122585) (by norm_num)
theorem B979897 : Blo 868566 979897 := bbase (se 2 (by rfl) ⟨367461, by rfl⟩ : syracuseStep 979897 = 734923) (by norm_num)
theorem B4191173 : Blo 868566 4191173 := bbase (se 4 (by rfl) ⟨392922, by rfl⟩ : syracuseStep 4191173 = 785845) (by norm_num)
theorem B1307597 : Blo 868566 1307597 := bbase (se 3 (by rfl) ⟨245174, by rfl⟩ : syracuseStep 1307597 = 490349) (by norm_num)
theorem B979933 : Blo 868566 979933 := bbase (se 3 (by rfl) ⟨183737, by rfl⟩ : syracuseStep 979933 = 367475) (by norm_num)
theorem B1307621 : Blo 868566 1307621 := bbase (se 4 (by rfl) ⟨122589, by rfl⟩ : syracuseStep 1307621 = 245179) (by norm_num)
theorem B1962989 : Blo 868566 1962989 := bbase (se 3 (by rfl) ⟨368060, by rfl⟩ : syracuseStep 1962989 = 736121) (by norm_num)
theorem B7435253 : Blo 868566 7435253 := bbase (se 5 (by rfl) ⟨348527, by rfl⟩ : syracuseStep 7435253 = 697055) (by norm_num)
theorem B1307645 : Blo 868566 1307645 := bbase (se 3 (by rfl) ⟨245183, by rfl⟩ : syracuseStep 1307645 = 490367) (by norm_num)
theorem B979969 : Blo 868566 979969 := bbase (se 2 (by rfl) ⟨367488, by rfl⟩ : syracuseStep 979969 = 734977) (by norm_num)
theorem B1471493 : Blo 868566 1471493 := bbase (se 4 (by rfl) ⟨137952, by rfl⟩ : syracuseStep 1471493 = 275905) (by norm_num)
theorem B1307669 : Blo 868566 1307669 := bbase (se 6 (by rfl) ⟨30648, by rfl⟩ : syracuseStep 1307669 = 61297) (by norm_num)
theorem B980005 : Blo 868566 980005 := bbase (se 4 (by rfl) ⟨91875, by rfl⟩ : syracuseStep 980005 = 183751) (by norm_num)
theorem B1307693 : Blo 868566 1307693 := bbase (se 3 (by rfl) ⟨245192, by rfl⟩ : syracuseStep 1307693 = 490385) (by norm_num)
theorem B8352821 : Blo 868566 8352821 := bbase (se 5 (by rfl) ⟨391538, by rfl⟩ : syracuseStep 8352821 = 783077) (by norm_num)
theorem B1569845 : Blo 868566 1569845 := bbase (se 5 (by rfl) ⟨73586, by rfl⟩ : syracuseStep 1569845 = 147173) (by norm_num)
theorem B1963061 : Blo 868566 1963061 := bbase (se 5 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 1963061 = 184037) (by norm_num)
theorem B1307717 : Blo 868566 1307717 := bbase (se 4 (by rfl) ⟨122598, by rfl⟩ : syracuseStep 1307717 = 245197) (by norm_num)
theorem B980041 : Blo 868566 980041 := bbase (se 2 (by rfl) ⟨367515, by rfl⟩ : syracuseStep 980041 = 735031) (by norm_num)
theorem B1307741 : Blo 868566 1307741 := bbase (se 3 (by rfl) ⟨245201, by rfl⟩ : syracuseStep 1307741 = 490403) (by norm_num)
theorem B980077 : Blo 868566 980077 := bbase (se 3 (by rfl) ⟨183764, by rfl⟩ : syracuseStep 980077 = 367529) (by norm_num)
theorem B1307765 : Blo 868566 1307765 := bbase (se 5 (by rfl) ⟨61301, by rfl⟩ : syracuseStep 1307765 = 122603) (by norm_num)
theorem B1963133 : Blo 868566 1963133 := bbase (se 3 (by rfl) ⟨368087, by rfl⟩ : syracuseStep 1963133 = 736175) (by norm_num)
theorem B1176709 : Blo 868566 1176709 := bbase (se 4 (by rfl) ⟨110316, by rfl⟩ : syracuseStep 1176709 = 220633) (by norm_num)
theorem B1471621 : Blo 868566 1471621 := bbase (se 4 (by rfl) ⟨137964, by rfl⟩ : syracuseStep 1471621 = 275929) (by norm_num)
theorem B1307789 : Blo 868566 1307789 := bbase (se 3 (by rfl) ⟨245210, by rfl⟩ : syracuseStep 1307789 = 490421) (by norm_num)
theorem B980113 : Blo 868566 980113 := bbase (se 2 (by rfl) ⟨367542, by rfl⟩ : syracuseStep 980113 = 735085) (by norm_num)
theorem B14840981 : Blo 868566 14840981 := bbase (se 6 (by rfl) ⟨347835, by rfl⟩ : syracuseStep 14840981 = 695671) (by norm_num)
theorem B1307813 : Blo 868566 1307813 := bbase (se 4 (by rfl) ⟨122607, by rfl⟩ : syracuseStep 1307813 = 245215) (by norm_num)
theorem B980149 : Blo 868566 980149 := bbase (se 5 (by rfl) ⟨45944, by rfl⟩ : syracuseStep 980149 = 91889) (by norm_num)
theorem B1307837 : Blo 868566 1307837 := bbase (se 3 (by rfl) ⟨245219, by rfl⟩ : syracuseStep 1307837 = 490439) (by norm_num)
theorem B1569989 : Blo 868566 1569989 := bbase (se 4 (by rfl) ⟨147186, by rfl⟩ : syracuseStep 1569989 = 294373) (by norm_num)
theorem B1963205 : Blo 868566 1963205 := bbase (se 4 (by rfl) ⟨184050, by rfl⟩ : syracuseStep 1963205 = 368101) (by norm_num)
theorem B1307861 : Blo 868566 1307861 := bbase (se 7 (by rfl) ⟨15326, by rfl⟩ : syracuseStep 1307861 = 30653) (by norm_num)
theorem B980185 : Blo 868566 980185 := bbase (se 2 (by rfl) ⟨367569, by rfl⟩ : syracuseStep 980185 = 735139) (by norm_num)
theorem B1471709 : Blo 868566 1471709 := bbase (se 3 (by rfl) ⟨275945, by rfl⟩ : syracuseStep 1471709 = 551891) (by norm_num)
theorem B1307885 : Blo 868566 1307885 := bbase (se 3 (by rfl) ⟨245228, by rfl⟩ : syracuseStep 1307885 = 490457) (by norm_num)
theorem B4715765 : Blo 868566 4715765 := bbase (se 5 (by rfl) ⟨221051, by rfl⟩ : syracuseStep 4715765 = 442103) (by norm_num)
theorem B980221 : Blo 868566 980221 := bbase (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) (by norm_num)
theorem B1307909 : Blo 868566 1307909 := bbase (se 4 (by rfl) ⟨122616, by rfl⟩ : syracuseStep 1307909 = 245233) (by norm_num)
theorem B1570061 : Blo 868566 1570061 := bbase (se 3 (by rfl) ⟨294386, by rfl⟩ : syracuseStep 1570061 = 588773) (by norm_num)
theorem B1307933 : Blo 868566 1307933 := bbase (se 3 (by rfl) ⟨245237, by rfl⟩ : syracuseStep 1307933 = 490475) (by norm_num)
theorem B980257 : Blo 868566 980257 := bbase (se 2 (by rfl) ⟨367596, by rfl⟩ : syracuseStep 980257 = 735193) (by norm_num)
theorem B1307957 : Blo 868566 1307957 := bbase (se 5 (by rfl) ⟨61310, by rfl⟩ : syracuseStep 1307957 = 122621) (by norm_num)
theorem B980293 : Blo 868566 980293 := bbase (se 4 (by rfl) ⟨91902, by rfl⟩ : syracuseStep 980293 = 183805) (by norm_num)
theorem B1307981 : Blo 868566 1307981 := bbase (se 3 (by rfl) ⟨245246, by rfl⟩ : syracuseStep 1307981 = 490493) (by norm_num)
theorem B1176925 : Blo 868566 1176925 := bbase (se 3 (by rfl) ⟨220673, by rfl⟩ : syracuseStep 1176925 = 441347) (by norm_num)
theorem B1471837 : Blo 868566 1471837 := bbase (se 3 (by rfl) ⟨275969, by rfl⟩ : syracuseStep 1471837 = 551939) (by norm_num)
theorem B1308005 : Blo 868566 1308005 := bbase (se 4 (by rfl) ⟨122625, by rfl⟩ : syracuseStep 1308005 = 245251) (by norm_num)
theorem B980329 : Blo 868566 980329 := bbase (se 2 (by rfl) ⟨367623, by rfl⟩ : syracuseStep 980329 = 735247) (by norm_num)
theorem B1308029 : Blo 868566 1308029 := bbase (se 3 (by rfl) ⟨245255, by rfl⟩ : syracuseStep 1308029 = 490511) (by norm_num)
theorem B980365 : Blo 868566 980365 := bbase (se 3 (by rfl) ⟨183818, by rfl⟩ : syracuseStep 980365 = 367637) (by norm_num)
theorem B1308053 : Blo 868566 1308053 := bbase (se 6 (by rfl) ⟨30657, by rfl⟩ : syracuseStep 1308053 = 61315) (by norm_num)
theorem B2717093 : Blo 868566 2717093 := bbase (se 4 (by rfl) ⟨254727, by rfl⟩ : syracuseStep 2717093 = 509455) (by norm_num)
theorem B1308077 : Blo 868566 1308077 := bbase (se 3 (by rfl) ⟨245264, by rfl⟩ : syracuseStep 1308077 = 490529) (by norm_num)
theorem B980401 : Blo 868566 980401 := bbase (se 2 (by rfl) ⟨367650, by rfl⟩ : syracuseStep 980401 = 735301) (by norm_num)
theorem B1471925 : Blo 868566 1471925 := bbase (se 5 (by rfl) ⟨68996, by rfl⟩ : syracuseStep 1471925 = 137993) (by norm_num)
theorem B1308101 : Blo 868566 1308101 := bbase (se 4 (by rfl) ⟨122634, by rfl⟩ : syracuseStep 1308101 = 245269) (by norm_num)
theorem B980437 : Blo 868566 980437 := bbase (se 7 (by rfl) ⟨11489, by rfl⟩ : syracuseStep 980437 = 22979) (by norm_num)
theorem B1308125 : Blo 868566 1308125 := bbase (se 3 (by rfl) ⟨245273, by rfl⟩ : syracuseStep 1308125 = 490547) (by norm_num)
theorem B1308149 : Blo 868566 1308149 := bbase (se 5 (by rfl) ⟨61319, by rfl⟩ : syracuseStep 1308149 = 122639) (by norm_num)
theorem B8386037 : Blo 868566 8386037 := bbase (se 5 (by rfl) ⟨393095, by rfl⟩ : syracuseStep 8386037 = 786191) (by norm_num)
theorem B980473 : Blo 868566 980473 := bbase (se 2 (by rfl) ⟨367677, by rfl⟩ : syracuseStep 980473 = 735355) (by norm_num)
theorem B1308173 : Blo 868566 1308173 := bbase (se 3 (by rfl) ⟨245282, by rfl⟩ : syracuseStep 1308173 = 490565) (by norm_num)
theorem B980509 : Blo 868566 980509 := bbase (se 3 (by rfl) ⟨183845, by rfl⟩ : syracuseStep 980509 = 367691) (by norm_num)
theorem B1308197 : Blo 868566 1308197 := bbase (se 4 (by rfl) ⟨122643, by rfl⟩ : syracuseStep 1308197 = 245287) (by norm_num)
theorem B1472053 : Blo 868566 1472053 := bbase (se 5 (by rfl) ⟨69002, by rfl⟩ : syracuseStep 1472053 = 138005) (by norm_num)
theorem B1308221 : Blo 868566 1308221 := bbase (se 3 (by rfl) ⟨245291, by rfl⟩ : syracuseStep 1308221 = 490583) (by norm_num)
theorem B980545 : Blo 868566 980545 := bbase (se 2 (by rfl) ⟨367704, by rfl⟩ : syracuseStep 980545 = 735409) (by norm_num)
theorem B1308245 : Blo 868566 1308245 := bbase (se 8 (by rfl) ⟨7665, by rfl⟩ : syracuseStep 1308245 = 15331) (by norm_num)
theorem B980581 : Blo 868566 980581 := bbase (se 4 (by rfl) ⟨91929, by rfl⟩ : syracuseStep 980581 = 183859) (by norm_num)
theorem B1308269 : Blo 868566 1308269 := bbase (se 3 (by rfl) ⟨245300, by rfl⟩ : syracuseStep 1308269 = 490601) (by norm_num)
theorem B1308293 : Blo 868566 1308293 := bbase (se 4 (by rfl) ⟨122652, by rfl⟩ : syracuseStep 1308293 = 245305) (by norm_num)
theorem B980617 : Blo 868566 980617 := bbase (se 2 (by rfl) ⟨367731, by rfl⟩ : syracuseStep 980617 = 735463) (by norm_num)
theorem B1472141 : Blo 868566 1472141 := bbase (se 3 (by rfl) ⟨276026, by rfl⟩ : syracuseStep 1472141 = 552053) (by norm_num)
theorem B1308317 : Blo 868566 1308317 := bbase (se 3 (by rfl) ⟨245309, by rfl⟩ : syracuseStep 1308317 = 490619) (by norm_num)
theorem B980653 : Blo 868566 980653 := bbase (se 3 (by rfl) ⟨183872, by rfl⟩ : syracuseStep 980653 = 367745) (by norm_num)
theorem B1308341 : Blo 868566 1308341 := bbase (se 5 (by rfl) ⟨61328, by rfl⟩ : syracuseStep 1308341 = 122657) (by norm_num)
theorem B6715061 : Blo 868566 6715061 := bbase (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) (by norm_num)
theorem B1308365 : Blo 868566 1308365 := bbase (se 3 (by rfl) ⟨245318, by rfl⟩ : syracuseStep 1308365 = 490637) (by norm_num)
theorem B980689 : Blo 868566 980689 := bbase (se 2 (by rfl) ⟨367758, by rfl⟩ : syracuseStep 980689 = 735517) (by norm_num)
theorem B1308389 : Blo 868566 1308389 := bbase (se 4 (by rfl) ⟨122661, by rfl⟩ : syracuseStep 1308389 = 245323) (by norm_num)
theorem B980725 : Blo 868566 980725 := bbase (se 5 (by rfl) ⟨45971, by rfl⟩ : syracuseStep 980725 = 91943) (by norm_num)
theorem B1308413 : Blo 868566 1308413 := bbase (se 3 (by rfl) ⟨245327, by rfl⟩ : syracuseStep 1308413 = 490655) (by norm_num)
theorem B1472269 : Blo 868566 1472269 := bbase (se 3 (by rfl) ⟨276050, by rfl⟩ : syracuseStep 1472269 = 552101) (by norm_num)
theorem B1308437 : Blo 868566 1308437 := bbase (se 6 (by rfl) ⟨30666, by rfl⟩ : syracuseStep 1308437 = 61333) (by norm_num)
theorem B980761 : Blo 868566 980761 := bbase (se 2 (by rfl) ⟨367785, by rfl⟩ : syracuseStep 980761 = 735571) (by norm_num)
theorem B1177373 : Blo 868566 1177373 := bbase (se 3 (by rfl) ⟨220757, by rfl⟩ : syracuseStep 1177373 = 441515) (by norm_num)
theorem B1308461 : Blo 868566 1308461 := bbase (se 3 (by rfl) ⟨245336, by rfl⟩ : syracuseStep 1308461 = 490673) (by norm_num)
theorem B980797 : Blo 868566 980797 := bbase (se 3 (by rfl) ⟨183899, by rfl⟩ : syracuseStep 980797 = 367799) (by norm_num)
theorem B1308485 : Blo 868566 1308485 := bbase (se 4 (by rfl) ⟨122670, by rfl⟩ : syracuseStep 1308485 = 245341) (by norm_num)
theorem B1308509 : Blo 868566 1308509 := bbase (se 3 (by rfl) ⟨245345, by rfl⟩ : syracuseStep 1308509 = 490691) (by norm_num)
theorem B980833 : Blo 868566 980833 := bbase (se 2 (by rfl) ⟨367812, by rfl⟩ : syracuseStep 980833 = 735625) (by norm_num)
theorem B1472357 : Blo 868566 1472357 := bbase (se 4 (by rfl) ⟨138033, by rfl⟩ : syracuseStep 1472357 = 276067) (by norm_num)
theorem B1308533 : Blo 868566 1308533 := bbase (se 5 (by rfl) ⟨61337, by rfl⟩ : syracuseStep 1308533 = 122675) (by norm_num)
theorem B980869 : Blo 868566 980869 := bbase (se 4 (by rfl) ⟨91956, by rfl⟩ : syracuseStep 980869 = 183913) (by norm_num)
theorem B1308557 : Blo 868566 1308557 := bbase (se 3 (by rfl) ⟨245354, by rfl⟩ : syracuseStep 1308557 = 490709) (by norm_num)
theorem B3536789 : Blo 868566 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B1308581 : Blo 868566 1308581 := bbase (se 4 (by rfl) ⟨122679, by rfl⟩ : syracuseStep 1308581 = 245359) (by norm_num)
theorem B980905 : Blo 868566 980905 := bbase (se 2 (by rfl) ⟨367839, by rfl⟩ : syracuseStep 980905 = 735679) (by norm_num)
theorem B1308605 : Blo 868566 1308605 := bbase (se 3 (by rfl) ⟨245363, by rfl⟩ : syracuseStep 1308605 = 490727) (by norm_num)
theorem B1046477 : Blo 868566 1046477 := bbase (se 3 (by rfl) ⟨196214, by rfl⟩ : syracuseStep 1046477 = 392429) (by norm_num)
theorem B980941 : Blo 868566 980941 := bbase (se 3 (by rfl) ⟨183926, by rfl⟩ : syracuseStep 980941 = 367853) (by norm_num)
theorem B1308629 : Blo 868566 1308629 := bbase (se 7 (by rfl) ⟨15335, by rfl⟩ : syracuseStep 1308629 = 30671) (by norm_num)
theorem B1308653 : Blo 868566 1308653 := bbase (se 3 (by rfl) ⟨245372, by rfl⟩ : syracuseStep 1308653 = 490745) (by norm_num)
theorem B980977 : Blo 868566 980977 := bbase (se 2 (by rfl) ⟨367866, by rfl⟩ : syracuseStep 980977 = 735733) (by norm_num)
theorem B1046525 : Blo 868566 1046525 := bbase (se 3 (by rfl) ⟨196223, by rfl⟩ : syracuseStep 1046525 = 392447) (by norm_num)
theorem B1308677 : Blo 868566 1308677 := bbase (se 4 (by rfl) ⟨122688, by rfl⟩ : syracuseStep 1308677 = 245377) (by norm_num)
theorem B981013 : Blo 868566 981013 := bbase (se 6 (by rfl) ⟨22992, by rfl⟩ : syracuseStep 981013 = 45985) (by norm_num)
theorem B1308701 : Blo 868566 1308701 := bbase (se 3 (by rfl) ⟨245381, by rfl⟩ : syracuseStep 1308701 = 490763) (by norm_num)
theorem B1308725 : Blo 868566 1308725 := bbase (se 5 (by rfl) ⟨61346, by rfl⟩ : syracuseStep 1308725 = 122693) (by norm_num)
theorem B981049 : Blo 868566 981049 := bbase (se 2 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 981049 = 735787) (by norm_num)
theorem B1308749 : Blo 868566 1308749 := bbase (se 3 (by rfl) ⟨245390, by rfl⟩ : syracuseStep 1308749 = 490781) (by norm_num)
theorem B1046621 : Blo 868566 1046621 := bbase (se 3 (by rfl) ⟨196241, by rfl⟩ : syracuseStep 1046621 = 392483) (by norm_num)
theorem B981085 : Blo 868566 981085 := bbase (se 3 (by rfl) ⟨183953, by rfl⟩ : syracuseStep 981085 = 367907) (by norm_num)
theorem B1308773 : Blo 868566 1308773 := bbase (se 4 (by rfl) ⟨122697, by rfl⟩ : syracuseStep 1308773 = 245395) (by norm_num)
theorem B1308797 : Blo 868566 1308797 := bbase (se 3 (by rfl) ⟨245399, by rfl⟩ : syracuseStep 1308797 = 490799) (by norm_num)
theorem B981121 : Blo 868566 981121 := bbase (se 2 (by rfl) ⟨367920, by rfl⟩ : syracuseStep 981121 = 735841) (by norm_num)
theorem B4028549 : Blo 868566 4028549 := bbase (se 4 (by rfl) ⟨377676, by rfl⟩ : syracuseStep 4028549 = 755353) (by norm_num)
theorem B1308821 : Blo 868566 1308821 := bbase (se 6 (by rfl) ⟨30675, by rfl⟩ : syracuseStep 1308821 = 61351) (by norm_num)
theorem B981157 : Blo 868566 981157 := bbase (se 4 (by rfl) ⟨91983, by rfl⟩ : syracuseStep 981157 = 183967) (by norm_num)
theorem B1308845 : Blo 868566 1308845 := bbase (se 3 (by rfl) ⟨245408, by rfl⟩ : syracuseStep 1308845 = 490817) (by norm_num)
theorem B2783429 : Blo 868566 2783429 := bbase (se 4 (by rfl) ⟨260946, by rfl⟩ : syracuseStep 2783429 = 521893) (by norm_num)
theorem B981193 : Blo 868566 981193 := bbase (se 2 (by rfl) ⟨367947, by rfl⟩ : syracuseStep 981193 = 735895) (by norm_num)
theorem B981229 : Blo 868566 981229 := bbase (se 3 (by rfl) ⟨183980, by rfl⟩ : syracuseStep 981229 = 367961) (by norm_num)
theorem B1046785 : Blo 868566 1046785 := bbase (se 2 (by rfl) ⟨392544, by rfl⟩ : syracuseStep 1046785 = 785089) (by norm_num)
theorem B981265 : Blo 868566 981265 := bbase (se 2 (by rfl) ⟨367974, by rfl⟩ : syracuseStep 981265 = 735949) (by norm_num)
theorem B981301 : Blo 868566 981301 := bbase (se 5 (by rfl) ⟨45998, by rfl⟩ : syracuseStep 981301 = 91997) (by norm_num)
theorem B981337 : Blo 868566 981337 := bbase (se 2 (by rfl) ⟨368001, by rfl⟩ : syracuseStep 981337 = 736003) (by norm_num)
theorem B981373 : Blo 868566 981373 := bbase (se 3 (by rfl) ⟨184007, by rfl⟩ : syracuseStep 981373 = 368015) (by norm_num)
theorem B981409 : Blo 868566 981409 := bbase (se 2 (by rfl) ⟨368028, by rfl⟩ : syracuseStep 981409 = 736057) (by norm_num)
theorem B981445 : Blo 868566 981445 := bbase (se 4 (by rfl) ⟨92010, by rfl⟩ : syracuseStep 981445 = 184021) (by norm_num)
theorem B1047001 : Blo 868566 1047001 := bbase (se 2 (by rfl) ⟨392625, by rfl⟩ : syracuseStep 1047001 = 785251) (by norm_num)
theorem B981481 : Blo 868566 981481 := bbase (se 2 (by rfl) ⟨368055, by rfl⟩ : syracuseStep 981481 = 736111) (by norm_num)
theorem B1571309 : Blo 868566 1571309 := bbase (se 3 (by rfl) ⟨294620, by rfl⟩ : syracuseStep 1571309 = 589241) (by norm_num)
theorem B981517 : Blo 868566 981517 := bbase (se 3 (by rfl) ⟨184034, by rfl⟩ : syracuseStep 981517 = 368069) (by norm_num)
theorem B981553 : Blo 868566 981553 := bbase (se 2 (by rfl) ⟨368082, by rfl⟩ : syracuseStep 981553 = 736165) (by norm_num)
theorem B981589 : Blo 868566 981589 := bbase (se 8 (by rfl) ⟨5751, by rfl⟩ : syracuseStep 981589 = 11503) (by norm_num)
theorem B981625 : Blo 868566 981625 := bbase (se 2 (by rfl) ⟨368109, by rfl⟩ : syracuseStep 981625 = 736219) (by norm_num)
theorem B1047169 : Blo 868566 1047169 := bbase (se 2 (by rfl) ⟨392688, by rfl⟩ : syracuseStep 1047169 = 785377) (by norm_num)
theorem B3308309 : Blo 868566 3308309 := bbase (se 6 (by rfl) ⟨77538, by rfl⟩ : syracuseStep 3308309 = 155077) (by norm_num)
theorem B3537701 : Blo 868566 3537701 := bbase (se 4 (by rfl) ⟨331659, by rfl⟩ : syracuseStep 3537701 = 663319) (by norm_num)
theorem B3767093 : Blo 868566 3767093 := bbase (se 5 (by rfl) ⟨176582, by rfl⟩ : syracuseStep 3767093 = 353165) (by norm_num)
theorem B3308597 : Blo 868566 3308597 := bbase (se 5 (by rfl) ⟨155090, by rfl⟩ : syracuseStep 3308597 = 310181) (by norm_num)
theorem B1047697 : Blo 868566 1047697 := bbase (se 2 (by rfl) ⟨392886, by rfl⟩ : syracuseStep 1047697 = 785773) (by norm_num)
theorem B2096317 : Blo 868566 2096317 := bbase (se 3 (by rfl) ⟨393059, by rfl⟩ : syracuseStep 2096317 = 786119) (by norm_num)
theorem B884125 : Blo 868566 884125 := bbase (se 3 (by rfl) ⟨165773, by rfl⟩ : syracuseStep 884125 = 331547) (by norm_num)
theorem B9895445 : Blo 868566 9895445 := bbase (se 6 (by rfl) ⟨231924, by rfl⟩ : syracuseStep 9895445 = 463849) (by norm_num)
theorem B7438229 : Blo 868566 7438229 := bbase (se 6 (by rfl) ⟨174333, by rfl⟩ : syracuseStep 7438229 = 348667) (by norm_num)
theorem B3178673 : Blo 868566 3178673 := bstep (se 2 (by rfl) ⟨1192002, by rfl⟩ : syracuseStep 3178673 = 2384005) B2384005
theorem B5570957 : Blo 868566 5570957 := bstep (se 3 (by rfl) ⟨1044554, by rfl⟩ : syracuseStep 5570957 = 2089109) B2089109
theorem B6029731 : Blo 868566 6029731 := bstep (se 1 (by rfl) ⟨4522298, by rfl⟩ : syracuseStep 6029731 = 9044597) B9044597
theorem B2228849 : Blo 868566 2228849 := bstep (se 2 (by rfl) ⟨835818, by rfl⟩ : syracuseStep 2228849 = 1671637) B1671637
theorem B4948613 : Blo 868566 4948613 := bstep (se 4 (by rfl) ⟨463932, by rfl⟩ : syracuseStep 4948613 = 927865) B927865
theorem B3310541 : Blo 868566 3310541 := bstep (se 3 (by rfl) ⟨620726, by rfl⟩ : syracuseStep 3310541 = 1241453) B1241453
theorem B14091491 : Blo 868566 14091491 := bstep (se 1 (by rfl) ⟨10568618, by rfl⟩ : syracuseStep 14091491 = 21137237) B21137237
theorem B10585457 : Blo 868566 10585457 := bstep (se 2 (by rfl) ⟨3969546, by rfl⟩ : syracuseStep 10585457 = 7939093) B7939093
theorem B9930437 : Blo 868566 9930437 := bstep (se 4 (by rfl) ⟨930978, by rfl⟩ : syracuseStep 9930437 = 1861957) B1861957
theorem B22644593 : Blo 868566 22644593 := bstep (se 2 (by rfl) ⟨8491722, by rfl⟩ : syracuseStep 22644593 = 16983445) B16983445
theorem B3344717 : Blo 868566 3344717 := bstep (se 3 (by rfl) ⟨627134, by rfl⟩ : syracuseStep 3344717 = 1254269) B1254269
theorem B2230705 : Blo 868566 2230705 := bstep (se 2 (by rfl) ⟨836514, by rfl⟩ : syracuseStep 2230705 = 1673029) B1673029
theorem B1411523 : Blo 868566 1411523 := bstep (se 1 (by rfl) ⟨1058642, by rfl⟩ : syracuseStep 1411523 = 2117285) B2117285
theorem B1116835 : Blo 868566 1116835 := bstep (se 1 (by rfl) ⟨837626, by rfl⟩ : syracuseStep 1116835 = 1675253) B1675253
theorem B2788145 : Blo 868566 2788145 := bstep (se 2 (by rfl) ⟨1045554, by rfl⟩ : syracuseStep 2788145 = 2091109) B2091109
theorem B2985005 : Blo 868566 2985005 := bstep (se 3 (by rfl) ⟨559688, by rfl⟩ : syracuseStep 2985005 = 1119377) B1119377
theorem B3345457 : Blo 868566 3345457 := bstep (se 2 (by rfl) ⟨1254546, by rfl⟩ : syracuseStep 3345457 = 2509093) B2509093
theorem B2231363 : Blo 868566 2231363 := bstep (se 1 (by rfl) ⟨1673522, by rfl⟩ : syracuseStep 2231363 = 3347045) B3347045
theorem B45321443 : Blo 868566 45321443 := bstep (se 1 (by rfl) ⟨33991082, by rfl⟩ : syracuseStep 45321443 = 67982165) B67982165
theorem B2198897 : Blo 868566 2198897 := bstep (se 2 (by rfl) ⟨824586, by rfl⟩ : syracuseStep 2198897 = 1649173) B1649173
theorem B2198947 : Blo 868566 2198947 := bstep (se 1 (by rfl) ⟨1649210, by rfl⟩ : syracuseStep 2198947 = 3298421) B3298421
theorem B2788835 : Blo 868566 2788835 := bstep (se 1 (by rfl) ⟨2091626, by rfl⟩ : syracuseStep 2788835 = 4183253) B4183253
theorem B2199089 : Blo 868566 2199089 := bstep (se 2 (by rfl) ⟨824658, by rfl⟩ : syracuseStep 2199089 = 1649317) B1649317
theorem B15044579 : Blo 868566 15044579 := bstep (se 1 (by rfl) ⟨11283434, by rfl⟩ : syracuseStep 15044579 = 22566869) B22566869
theorem B1413235 : Blo 868566 1413235 := bstep (se 1 (by rfl) ⟨1059926, by rfl⟩ : syracuseStep 1413235 = 2119853) B2119853
theorem B4952461 : Blo 868566 4952461 := bstep (se 3 (by rfl) ⟨928586, by rfl⟩ : syracuseStep 4952461 = 1857173) B1857173
theorem B2200081 : Blo 868566 2200081 := bstep (se 2 (by rfl) ⟨825030, by rfl⟩ : syracuseStep 2200081 = 1650061) B1650061
theorem B2200355 : Blo 868566 2200355 := bstep (se 1 (by rfl) ⟨1650266, by rfl⟩ : syracuseStep 2200355 = 3300533) B3300533
theorem B2200547 : Blo 868566 2200547 := bstep (se 1 (by rfl) ⟨1650410, by rfl⟩ : syracuseStep 2200547 = 3300821) B3300821
theorem B3970225 : Blo 868566 3970225 := bstep (se 2 (by rfl) ⟨1488834, by rfl⟩ : syracuseStep 3970225 = 2977669) B2977669
theorem B2790605 : Blo 868566 2790605 := bstep (se 3 (by rfl) ⟨523238, by rfl⟩ : syracuseStep 2790605 = 1046477) B1046477
theorem B2790733 : Blo 868566 2790733 := bstep (se 3 (by rfl) ⟨523262, by rfl⟩ : syracuseStep 2790733 = 1046525) B1046525
theorem B10065293 : Blo 868566 10065293 := bstep (se 3 (by rfl) ⟨1887242, by rfl⟩ : syracuseStep 10065293 = 3774485) B3774485
theorem B2823665 : Blo 868566 2823665 := bstep (se 2 (by rfl) ⟨1058874, by rfl⟩ : syracuseStep 2823665 = 2117749) B2117749
theorem B2790989 : Blo 868566 2790989 := bstep (se 3 (by rfl) ⟨523310, by rfl⟩ : syracuseStep 2790989 = 1046621) B1046621
theorem B3348323 : Blo 868566 3348323 := bstep (se 1 (by rfl) ⟨2511242, by rfl⟩ : syracuseStep 3348323 = 5022485) B5022485
theorem B2201489 : Blo 868566 2201489 := bstep (se 2 (by rfl) ⟨825558, by rfl⟩ : syracuseStep 2201489 = 1651117) B1651117
theorem B2201539 : Blo 868566 2201539 := bstep (se 1 (by rfl) ⟨1651154, by rfl⟩ : syracuseStep 2201539 = 3302309) B3302309
theorem B2201681 : Blo 868566 2201681 := bstep (se 2 (by rfl) ⟨825630, by rfl⟩ : syracuseStep 2201681 = 1651261) B1651261
theorem B4954445 : Blo 868566 4954445 := bstep (se 3 (by rfl) ⟨928958, by rfl⟩ : syracuseStep 4954445 = 1857917) B1857917
theorem B4397489 : Blo 868566 4397489 := bstep (se 2 (by rfl) ⟨1649058, by rfl⟩ : syracuseStep 4397489 = 3298117) B3298117
theorem B5577443 : Blo 868566 5577443 := bstep (se 1 (by rfl) ⟨4183082, by rfl⟩ : syracuseStep 5577443 = 8366165) B8366165
theorem B2202673 : Blo 868566 2202673 := bstep (se 2 (by rfl) ⟨826002, by rfl⟩ : syracuseStep 2202673 = 1652005) B1652005
theorem B2792515 : Blo 868566 2792515 := bstep (se 1 (by rfl) ⟨2094386, by rfl⟩ : syracuseStep 2792515 = 4188773) B4188773
theorem B4955377 : Blo 868566 4955377 := bstep (se 2 (by rfl) ⟨1858266, by rfl⟩ : syracuseStep 4955377 = 3716533) B3716533
theorem B2202947 : Blo 868566 2202947 := bstep (se 1 (by rfl) ⟨1652210, by rfl⟩ : syracuseStep 2202947 = 3304421) B3304421
theorem B9936269 : Blo 868566 9936269 := bstep (se 3 (by rfl) ⟨1863050, by rfl⟩ : syracuseStep 9936269 = 3726101) B3726101
theorem B2203139 : Blo 868566 2203139 := bstep (se 1 (by rfl) ⟨1652354, by rfl⟩ : syracuseStep 2203139 = 3304709) B3304709
theorem B1089187 : Blo 868566 1089187 := bstep (se 1 (by rfl) ⟨816890, by rfl⟩ : syracuseStep 1089187 = 1633781) B1633781
theorem B2236177 : Blo 868566 2236177 := bstep (se 2 (by rfl) ⟨838566, by rfl⟩ : syracuseStep 2236177 = 1677133) B1677133
theorem B4398947 : Blo 868566 4398947 := bstep (se 1 (by rfl) ⟨3299210, by rfl⟩ : syracuseStep 4398947 = 6598421) B6598421
theorem B14884721 : Blo 868566 14884721 := bstep (se 2 (by rfl) ⟨5581770, by rfl⟩ : syracuseStep 14884721 = 11163541) B11163541
theorem B4235171 : Blo 868566 4235171 := bstep (se 1 (by rfl) ⟨3176378, by rfl⟩ : syracuseStep 4235171 = 6352757) B6352757
theorem B10592369 : Blo 868566 10592369 := bstep (se 2 (by rfl) ⟨3972138, by rfl⟩ : syracuseStep 10592369 = 7944277) B7944277
theorem B3711203 : Blo 868566 3711203 := bstep (se 1 (by rfl) ⟨2783402, by rfl⟩ : syracuseStep 3711203 = 5566805) B5566805
theorem B2204081 : Blo 868566 2204081 := bstep (se 2 (by rfl) ⟨826530, by rfl⟩ : syracuseStep 2204081 = 1653061) B1653061
theorem B2204131 : Blo 868566 2204131 := bstep (se 1 (by rfl) ⟨1653098, by rfl⟩ : syracuseStep 2204131 = 3306197) B3306197
theorem B77537845 : Blo 868566 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B2204273 : Blo 868566 2204273 := bstep (se 2 (by rfl) ⟨826602, by rfl⟩ : syracuseStep 2204273 = 1653205) B1653205
theorem B2794115 : Blo 868566 2794115 := bstep (se 1 (by rfl) ⟨2095586, by rfl⟩ : syracuseStep 2794115 = 4191173) B4191173
theorem B4399757 : Blo 868566 4399757 := bstep (se 3 (by rfl) ⟨824954, by rfl⟩ : syracuseStep 4399757 = 1649909) B1649909
theorem B4956835 : Blo 868566 4956835 := bstep (se 1 (by rfl) ⟨3717626, by rfl⟩ : syracuseStep 4956835 = 7435253) B7435253
theorem B1811395 : Blo 868566 1811395 := bstep (se 1 (by rfl) ⟨1358546, by rfl⟩ : syracuseStep 1811395 = 2717093) B2717093
theorem B4957361 : Blo 868566 4957361 := bstep (se 2 (by rfl) ⟨1859010, by rfl⟩ : syracuseStep 4957361 = 3718021) B3718021
theorem B2237635 : Blo 868566 2237635 := bstep (se 1 (by rfl) ⟨1678226, by rfl⟩ : syracuseStep 2237635 = 3356453) B3356453
theorem B2860397 : Blo 868566 2860397 := bstep (se 3 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 2860397 = 1072649) B1072649
theorem B37725749 : Blo 868566 37725749 := bstep (se 5 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 37725749 = 3536789) B3536789
theorem B2205265 : Blo 868566 2205265 := bstep (se 2 (by rfl) ⟨826974, by rfl⟩ : syracuseStep 2205265 = 1653949) B1653949
theorem B2795089 : Blo 868566 2795089 := bstep (se 2 (by rfl) ⟨1048158, by rfl⟩ : syracuseStep 2795089 = 2096317) B2096317
theorem B1320641 : Blo 868566 1320641 := bstep (se 2 (by rfl) ⟨495240, by rfl⟩ : syracuseStep 1320641 = 990481) B990481
theorem B2205539 : Blo 868566 2205539 := bstep (se 1 (by rfl) ⟨1654154, by rfl⟩ : syracuseStep 2205539 = 3308309) B3308309
theorem B2205731 : Blo 868566 2205731 := bstep (se 1 (by rfl) ⟨1654298, by rfl⟩ : syracuseStep 2205731 = 3308597) B3308597
theorem B1321219 : Blo 868566 1321219 := bstep (se 1 (by rfl) ⟨990914, by rfl⟩ : syracuseStep 1321219 = 1981829) B1981829
theorem B5581133 : Blo 868566 5581133 := bstep (se 3 (by rfl) ⟨1046462, by rfl⟩ : syracuseStep 5581133 = 2092925) B2092925
theorem B6596963 : Blo 868566 6596963 := bstep (se 1 (by rfl) ⟨4947722, by rfl⟩ : syracuseStep 6596963 = 9895445) B9895445
theorem B5581361 : Blo 868566 5581361 := bstep (se 2 (by rfl) ⟨2093010, by rfl⟩ : syracuseStep 5581361 = 4186021) B4186021
theorem B4958819 : Blo 868566 4958819 := bstep (se 1 (by rfl) ⟨3719114, by rfl⟩ : syracuseStep 4958819 = 7438229) B7438229
theorem B20064995 : Blo 868566 20064995 := bstep (se 1 (by rfl) ⟨15048746, by rfl⟩ : syracuseStep 20064995 = 30097493) B30097493
theorem B1649393 : Blo 868566 1649393 := bstep (se 2 (by rfl) ⟨618522, by rfl⟩ : syracuseStep 1649393 = 1237045) B1237045
theorem B2206673 : Blo 868566 2206673 := bstep (se 2 (by rfl) ⟨827502, by rfl⟩ : syracuseStep 2206673 = 1655005) B1655005
theorem B2206723 : Blo 868566 2206723 := bstep (se 1 (by rfl) ⟨1655042, by rfl⟩ : syracuseStep 2206723 = 3310085) B3310085
theorem B2206865 : Blo 868566 2206865 := bstep (se 2 (by rfl) ⟨827574, by rfl⟩ : syracuseStep 2206865 = 1655149) B1655149
theorem B6368453 : Blo 868566 6368453 := bstep (se 4 (by rfl) ⟨597042, by rfl⟩ : syracuseStep 6368453 = 1194085) B1194085
theorem B929027 : Blo 868566 929027 := bstep (se 1 (by rfl) ⟨696770, by rfl⟩ : syracuseStep 929027 = 1393541) B1393541
theorem B2829745 : Blo 868566 2829745 := bstep (se 2 (by rfl) ⟨1061154, by rfl⟩ : syracuseStep 2829745 = 2122309) B2122309
theorem B4402673 : Blo 868566 4402673 := bstep (se 2 (by rfl) ⟨1651002, by rfl⟩ : syracuseStep 4402673 = 3302005) B3302005
theorem B7056881 : Blo 868566 7056881 := bstep (se 2 (by rfl) ⟨2646330, by rfl⟩ : syracuseStep 7056881 = 5292661) B5292661
theorem B15904309 : Blo 868566 15904309 := bstep (se 5 (by rfl) ⟨745514, by rfl⟩ : syracuseStep 15904309 = 1491029) B1491029
theorem B1322563 : Blo 868566 1322563 := bstep (se 1 (by rfl) ⟨991922, by rfl⟩ : syracuseStep 1322563 = 1983845) B1983845
theorem B1650289 : Blo 868566 1650289 := bstep (se 2 (by rfl) ⟨618858, by rfl⟩ : syracuseStep 1650289 = 1237717) B1237717
theorem B7057165 : Blo 868566 7057165 := bstep (se 3 (by rfl) ⟨1323218, by rfl⟩ : syracuseStep 7057165 = 2646437) B2646437
theorem B1650449 : Blo 868566 1650449 := bstep (se 2 (by rfl) ⟨618918, by rfl⟩ : syracuseStep 1650449 = 1237837) B1237837
theorem B3714893 : Blo 868566 3714893 := bstep (se 3 (by rfl) ⟨696542, by rfl⟩ : syracuseStep 3714893 = 1393085) B1393085
theorem B3714929 : Blo 868566 3714929 := bstep (se 2 (by rfl) ⟨1393098, by rfl⟩ : syracuseStep 3714929 = 2786197) B2786197
theorem B2830211 : Blo 868566 2830211 := bstep (se 1 (by rfl) ⟨2122658, by rfl⟩ : syracuseStep 2830211 = 4245317) B4245317
theorem B6697073 : Blo 868566 6697073 := bstep (se 2 (by rfl) ⟨2511402, by rfl⟩ : syracuseStep 6697073 = 5022805) B5022805
theorem B2207857 : Blo 868566 2207857 := bstep (se 2 (by rfl) ⟨827946, by rfl⟩ : syracuseStep 2207857 = 1655893) B1655893
theorem B1650851 : Blo 868566 1650851 := bstep (se 1 (by rfl) ⟨1238138, by rfl⟩ : syracuseStep 1650851 = 2476277) B2476277
theorem B929971 : Blo 868566 929971 := bstep (se 1 (by rfl) ⟨697478, by rfl⟩ : syracuseStep 929971 = 1394957) B1394957
theorem B2208131 : Blo 868566 2208131 := bstep (se 1 (by rfl) ⟨1656098, by rfl⟩ : syracuseStep 2208131 = 3312197) B3312197
theorem B4960709 : Blo 868566 4960709 := bstep (se 4 (by rfl) ⟨465066, by rfl⟩ : syracuseStep 4960709 = 930133) B930133
theorem B2208323 : Blo 868566 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B4404131 : Blo 868566 4404131 := bstep (se 1 (by rfl) ⟨3303098, by rfl⟩ : syracuseStep 4404131 = 6606197) B6606197
theorem B1651747 : Blo 868566 1651747 := bstep (se 1 (by rfl) ⟨1238810, by rfl⟩ : syracuseStep 1651747 = 2477621) B2477621
theorem B1651907 : Blo 868566 1651907 := bstep (se 1 (by rfl) ⟨1238930, by rfl⟩ : syracuseStep 1651907 = 2477861) B2477861
theorem B931235 : Blo 868566 931235 := bstep (se 1 (by rfl) ⟨698426, by rfl⟩ : syracuseStep 931235 = 1396853) B1396853
theorem B4404941 : Blo 868566 4404941 := bstep (se 3 (by rfl) ⟨825926, by rfl⟩ : syracuseStep 4404941 = 1651853) B1651853
theorem B8369891 : Blo 868566 8369891 := bstep (se 1 (by rfl) ⟨6277418, by rfl⟩ : syracuseStep 8369891 = 12554837) B12554837
theorem B3389219 : Blo 868566 3389219 := bstep (se 1 (by rfl) ⟨2541914, by rfl⟩ : syracuseStep 3389219 = 5083829) B5083829
theorem B5027789 : Blo 868566 5027789 := bstep (se 3 (by rfl) ⟨942710, by rfl⟩ : syracuseStep 5027789 = 1885421) B1885421
theorem B1652977 : Blo 868566 1652977 := bstep (se 2 (by rfl) ⟨619866, by rfl⟩ : syracuseStep 1652977 = 1239733) B1239733
theorem B1194259 : Blo 868566 1194259 := bstep (se 1 (by rfl) ⟨895694, by rfl⟩ : syracuseStep 1194259 = 1791389) B1791389
theorem B4962637 : Blo 868566 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B1325603 : Blo 868566 1325603 := bstep (se 1 (by rfl) ⟨994202, by rfl⟩ : syracuseStep 1325603 = 1988405) B1988405
theorem B1325651 : Blo 868566 1325651 := bstep (se 1 (by rfl) ⟨994238, by rfl⟩ : syracuseStep 1325651 = 1988477) B1988477
theorem B1325987 : Blo 868566 1325987 := bstep (se 1 (by rfl) ⟨994490, by rfl⟩ : syracuseStep 1325987 = 1988981) B1988981
theorem B2931821 : Blo 868566 2931821 := bstep (se 3 (by rfl) ⟨549716, by rfl⟩ : syracuseStep 2931821 = 1099433) B1099433
theorem B2931875 : Blo 868566 2931875 := bstep (se 1 (by rfl) ⟨2198906, by rfl⟩ : syracuseStep 2931875 = 4397813) B4397813
theorem B1654033 : Blo 868566 1654033 := bstep (se 2 (by rfl) ⟨620262, by rfl⟩ : syracuseStep 1654033 = 1240525) B1240525
theorem B32128397 : Blo 868566 32128397 := bstep (se 3 (by rfl) ⟨6024074, by rfl⟩ : syracuseStep 32128397 = 12048149) B12048149
theorem B2932145 : Blo 868566 2932145 := bstep (se 2 (by rfl) ⟨1099554, by rfl⟩ : syracuseStep 2932145 = 2199109) B2199109
theorem B7421381 : Blo 868566 7421381 := bstep (se 4 (by rfl) ⟨695754, by rfl⟩ : syracuseStep 7421381 = 1391509) B1391509
theorem B1490483 : Blo 868566 1490483 := bstep (se 1 (by rfl) ⟨1117862, by rfl⟩ : syracuseStep 1490483 = 2235725) B2235725
theorem B6602309 : Blo 868566 6602309 := bstep (se 4 (by rfl) ⟨618966, by rfl⟩ : syracuseStep 6602309 = 1237933) B1237933
theorem B1654435 : Blo 868566 1654435 := bstep (se 1 (by rfl) ⟨1240826, by rfl⟩ : syracuseStep 1654435 = 2481653) B2481653
theorem B1654481 : Blo 868566 1654481 := bstep (se 2 (by rfl) ⟨620430, by rfl⟩ : syracuseStep 1654481 = 1240861) B1240861
theorem B1392419 : Blo 868566 1392419 := bstep (se 1 (by rfl) ⟨1044314, by rfl⟩ : syracuseStep 1392419 = 2088629) B2088629
theorem B1392547 : Blo 868566 1392547 := bstep (se 1 (by rfl) ⟨1044410, by rfl⟩ : syracuseStep 1392547 = 2088821) B2088821
theorem B2932685 : Blo 868566 2932685 := bstep (se 3 (by rfl) ⟨549878, by rfl⟩ : syracuseStep 2932685 = 1099757) B1099757
theorem B1654769 : Blo 868566 1654769 := bstep (se 2 (by rfl) ⟨620538, by rfl⟩ : syracuseStep 1654769 = 1241077) B1241077
theorem B2932739 : Blo 868566 2932739 := bstep (se 1 (by rfl) ⟨2199554, by rfl⟩ : syracuseStep 2932739 = 4399109) B4399109
theorem B966691 : Blo 868566 966691 := bstep (se 1 (by rfl) ⟨725018, by rfl⟩ : syracuseStep 966691 = 1450037) B1450037
theorem B1392689 : Blo 868566 1392689 := bstep (se 2 (by rfl) ⟨522258, by rfl⟩ : syracuseStep 1392689 = 1044517) B1044517
theorem B6275171 : Blo 868566 6275171 := bstep (se 1 (by rfl) ⟨4706378, by rfl⟩ : syracuseStep 6275171 = 9412757) B9412757
theorem B3719267 : Blo 868566 3719267 := bstep (se 1 (by rfl) ⟨2789450, by rfl⟩ : syracuseStep 3719267 = 5578901) B5578901
theorem B868579 : Blo 868566 868579 := bstep (se 1 (by rfl) ⟨651434, by rfl⟩ : syracuseStep 868579 = 1302869) B1302869
theorem B868595 : Blo 868566 868595 := bstep (se 1 (by rfl) ⟨651446, by rfl⟩ : syracuseStep 868595 = 1302893) B1302893
theorem B868611 : Blo 868566 868611 := bstep (se 1 (by rfl) ⟨651458, by rfl⟩ : syracuseStep 868611 = 1302917) B1302917
theorem B2933009 : Blo 868566 2933009 := bstep (se 2 (by rfl) ⟨1099878, by rfl⟩ : syracuseStep 2933009 = 2199757) B2199757
theorem B868627 : Blo 868566 868627 := bstep (se 1 (by rfl) ⟨651470, by rfl⟩ : syracuseStep 868627 = 1302941) B1302941
theorem B868643 : Blo 868566 868643 := bstep (se 1 (by rfl) ⟨651482, by rfl⟩ : syracuseStep 868643 = 1302965) B1302965
theorem B868659 : Blo 868566 868659 := bstep (se 1 (by rfl) ⟨651494, by rfl⟩ : syracuseStep 868659 = 1302989) B1302989
theorem B868675 : Blo 868566 868675 := bstep (se 1 (by rfl) ⟨651506, by rfl⟩ : syracuseStep 868675 = 1303013) B1303013
theorem B2474317 : Blo 868566 2474317 := bstep (se 3 (by rfl) ⟨463934, by rfl⟩ : syracuseStep 2474317 = 927869) B927869
theorem B1392977 : Blo 868566 1392977 := bstep (se 2 (by rfl) ⟨522366, by rfl⟩ : syracuseStep 1392977 = 1044733) B1044733
theorem B868691 : Blo 868566 868691 := bstep (se 1 (by rfl) ⟨651518, by rfl⟩ : syracuseStep 868691 = 1303037) B1303037
theorem B868707 : Blo 868566 868707 := bstep (se 1 (by rfl) ⟨651530, by rfl⟩ : syracuseStep 868707 = 1303061) B1303061
theorem B868723 : Blo 868566 868723 := bstep (se 1 (by rfl) ⟨651542, by rfl⟩ : syracuseStep 868723 = 1303085) B1303085
theorem B868739 : Blo 868566 868739 := bstep (se 1 (by rfl) ⟨651554, by rfl⟩ : syracuseStep 868739 = 1303109) B1303109
theorem B868755 : Blo 868566 868755 := bstep (se 1 (by rfl) ⟨651566, by rfl⟩ : syracuseStep 868755 = 1303133) B1303133
theorem B868771 : Blo 868566 868771 := bstep (se 1 (by rfl) ⟨651578, by rfl⟩ : syracuseStep 868771 = 1303157) B1303157
theorem B868787 : Blo 868566 868787 := bstep (se 1 (by rfl) ⟨651590, by rfl⟩ : syracuseStep 868787 = 1303181) B1303181
theorem B868803 : Blo 868566 868803 := bstep (se 1 (by rfl) ⟨651602, by rfl⟩ : syracuseStep 868803 = 1303205) B1303205
theorem B868819 : Blo 868566 868819 := bstep (se 1 (by rfl) ⟨651614, by rfl⟩ : syracuseStep 868819 = 1303229) B1303229
theorem B868835 : Blo 868566 868835 := bstep (se 1 (by rfl) ⟨651626, by rfl⟩ : syracuseStep 868835 = 1303253) B1303253
theorem B868851 : Blo 868566 868851 := bstep (se 1 (by rfl) ⟨651638, by rfl⟩ : syracuseStep 868851 = 1303277) B1303277
theorem B868867 : Blo 868566 868867 := bstep (se 1 (by rfl) ⟨651650, by rfl⟩ : syracuseStep 868867 = 1303301) B1303301
theorem B868883 : Blo 868566 868883 := bstep (se 1 (by rfl) ⟨651662, by rfl⟩ : syracuseStep 868883 = 1303325) B1303325
theorem B868899 : Blo 868566 868899 := bstep (se 1 (by rfl) ⟨651674, by rfl⟩ : syracuseStep 868899 = 1303349) B1303349
theorem B2474545 : Blo 868566 2474545 := bstep (se 2 (by rfl) ⟨927954, by rfl⟩ : syracuseStep 2474545 = 1855909) B1855909
theorem B4407857 : Blo 868566 4407857 := bstep (se 2 (by rfl) ⟨1652946, by rfl⟩ : syracuseStep 4407857 = 3305893) B3305893
theorem B868915 : Blo 868566 868915 := bstep (se 1 (by rfl) ⟨651686, by rfl⟩ : syracuseStep 868915 = 1303373) B1303373
theorem B868931 : Blo 868566 868931 := bstep (se 1 (by rfl) ⟨651698, by rfl⟩ : syracuseStep 868931 = 1303397) B1303397
theorem B868947 : Blo 868566 868947 := bstep (se 1 (by rfl) ⟨651710, by rfl⟩ : syracuseStep 868947 = 1303421) B1303421
theorem B868963 : Blo 868566 868963 := bstep (se 1 (by rfl) ⟨651722, by rfl⟩ : syracuseStep 868963 = 1303445) B1303445
theorem B868979 : Blo 868566 868979 := bstep (se 1 (by rfl) ⟨651734, by rfl⟩ : syracuseStep 868979 = 1303469) B1303469
theorem B868995 : Blo 868566 868995 := bstep (se 1 (by rfl) ⟨651746, by rfl⟩ : syracuseStep 868995 = 1303493) B1303493
theorem B869011 : Blo 868566 869011 := bstep (se 1 (by rfl) ⟨651758, by rfl⟩ : syracuseStep 869011 = 1303517) B1303517
theorem B869027 : Blo 868566 869027 := bstep (se 1 (by rfl) ⟨651770, by rfl⟩ : syracuseStep 869027 = 1303541) B1303541
theorem B869043 : Blo 868566 869043 := bstep (se 1 (by rfl) ⟨651782, by rfl⟩ : syracuseStep 869043 = 1303565) B1303565
theorem B869059 : Blo 868566 869059 := bstep (se 1 (by rfl) ⟨651794, by rfl⟩ : syracuseStep 869059 = 1303589) B1303589
theorem B1655491 : Blo 868566 1655491 := bstep (se 1 (by rfl) ⟨1241618, by rfl⟩ : syracuseStep 1655491 = 2483237) B2483237
theorem B2474705 : Blo 868566 2474705 := bstep (se 2 (by rfl) ⟨928014, by rfl⟩ : syracuseStep 2474705 = 1856029) B1856029
theorem B869075 : Blo 868566 869075 := bstep (se 1 (by rfl) ⟨651806, by rfl⟩ : syracuseStep 869075 = 1303613) B1303613
theorem B869091 : Blo 868566 869091 := bstep (se 1 (by rfl) ⟨651818, by rfl⟩ : syracuseStep 869091 = 1303637) B1303637
theorem B4702961 : Blo 868566 4702961 := bstep (se 2 (by rfl) ⟨1763610, by rfl⟩ : syracuseStep 4702961 = 3527221) B3527221
theorem B869107 : Blo 868566 869107 := bstep (se 1 (by rfl) ⟨651830, by rfl⟩ : syracuseStep 869107 = 1303661) B1303661
theorem B869123 : Blo 868566 869123 := bstep (se 1 (by rfl) ⟨651842, by rfl⟩ : syracuseStep 869123 = 1303685) B1303685
theorem B5587717 : Blo 868566 5587717 := bstep (se 4 (by rfl) ⟨523848, by rfl⟩ : syracuseStep 5587717 = 1047697) B1047697
theorem B869139 : Blo 868566 869139 := bstep (se 1 (by rfl) ⟨651854, by rfl⟩ : syracuseStep 869139 = 1303709) B1303709
theorem B869155 : Blo 868566 869155 := bstep (se 1 (by rfl) ⟨651866, by rfl⟩ : syracuseStep 869155 = 1303733) B1303733
theorem B2933549 : Blo 868566 2933549 := bstep (se 3 (by rfl) ⟨550040, by rfl⟩ : syracuseStep 2933549 = 1100081) B1100081
theorem B869171 : Blo 868566 869171 := bstep (se 1 (by rfl) ⟨651878, by rfl⟩ : syracuseStep 869171 = 1303757) B1303757
theorem B2474819 : Blo 868566 2474819 := bstep (se 1 (by rfl) ⟨1856114, by rfl⟩ : syracuseStep 2474819 = 3712229) B3712229
theorem B869187 : Blo 868566 869187 := bstep (se 1 (by rfl) ⟨651890, by rfl⟩ : syracuseStep 869187 = 1303781) B1303781
theorem B869203 : Blo 868566 869203 := bstep (se 1 (by rfl) ⟨651902, by rfl⟩ : syracuseStep 869203 = 1303805) B1303805
theorem B2933603 : Blo 868566 2933603 := bstep (se 1 (by rfl) ⟨2200202, by rfl⟩ : syracuseStep 2933603 = 4400405) B4400405
theorem B869219 : Blo 868566 869219 := bstep (se 1 (by rfl) ⟨651914, by rfl⟩ : syracuseStep 869219 = 1303829) B1303829
theorem B1885027 : Blo 868566 1885027 := bstep (se 1 (by rfl) ⟨1413770, by rfl⟩ : syracuseStep 1885027 = 2827541) B2827541
theorem B869235 : Blo 868566 869235 := bstep (se 1 (by rfl) ⟨651926, by rfl⟩ : syracuseStep 869235 = 1303853) B1303853
theorem B869251 : Blo 868566 869251 := bstep (se 1 (by rfl) ⟨651938, by rfl⟩ : syracuseStep 869251 = 1303877) B1303877
theorem B869267 : Blo 868566 869267 := bstep (se 1 (by rfl) ⟨651950, by rfl⟩ : syracuseStep 869267 = 1303901) B1303901
theorem B869283 : Blo 868566 869283 := bstep (se 1 (by rfl) ⟨651962, by rfl⟩ : syracuseStep 869283 = 1303925) B1303925
theorem B869299 : Blo 868566 869299 := bstep (se 1 (by rfl) ⟨651974, by rfl⟩ : syracuseStep 869299 = 1303949) B1303949
theorem B1491905 : Blo 868566 1491905 := bstep (se 2 (by rfl) ⟨559464, by rfl⟩ : syracuseStep 1491905 = 1118929) B1118929
theorem B869315 : Blo 868566 869315 := bstep (se 1 (by rfl) ⟨651986, by rfl⟩ : syracuseStep 869315 = 1303973) B1303973
theorem B869331 : Blo 868566 869331 := bstep (se 1 (by rfl) ⟨651998, by rfl⟩ : syracuseStep 869331 = 1303997) B1303997
theorem B869347 : Blo 868566 869347 := bstep (se 1 (by rfl) ⟨652010, by rfl⟩ : syracuseStep 869347 = 1304021) B1304021
theorem B869363 : Blo 868566 869363 := bstep (se 1 (by rfl) ⟨652022, by rfl⟩ : syracuseStep 869363 = 1304045) B1304045
theorem B869379 : Blo 868566 869379 := bstep (se 1 (by rfl) ⟨652034, by rfl⟩ : syracuseStep 869379 = 1304069) B1304069
theorem B869395 : Blo 868566 869395 := bstep (se 1 (by rfl) ⟨652046, by rfl⟩ : syracuseStep 869395 = 1304093) B1304093
theorem B869411 : Blo 868566 869411 := bstep (se 1 (by rfl) ⟨652058, by rfl⟩ : syracuseStep 869411 = 1304117) B1304117
theorem B869427 : Blo 868566 869427 := bstep (se 1 (by rfl) ⟨652070, by rfl⟩ : syracuseStep 869427 = 1304141) B1304141
theorem B869443 : Blo 868566 869443 := bstep (se 1 (by rfl) ⟨652082, by rfl⟩ : syracuseStep 869443 = 1304165) B1304165
theorem B869459 : Blo 868566 869459 := bstep (se 1 (by rfl) ⟨652094, by rfl⟩ : syracuseStep 869459 = 1304189) B1304189
theorem B869475 : Blo 868566 869475 := bstep (se 1 (by rfl) ⟨652106, by rfl⟩ : syracuseStep 869475 = 1304213) B1304213
theorem B2933873 : Blo 868566 2933873 := bstep (se 2 (by rfl) ⟨1100202, by rfl⟩ : syracuseStep 2933873 = 2200405) B2200405
theorem B1393777 : Blo 868566 1393777 := bstep (se 2 (by rfl) ⟨522666, by rfl⟩ : syracuseStep 1393777 = 1045333) B1045333
theorem B869491 : Blo 868566 869491 := bstep (se 1 (by rfl) ⟨652118, by rfl⟩ : syracuseStep 869491 = 1304237) B1304237
theorem B7554161 : Blo 868566 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B869507 : Blo 868566 869507 := bstep (se 1 (by rfl) ⟨652130, by rfl⟩ : syracuseStep 869507 = 1304261) B1304261
theorem B1655939 : Blo 868566 1655939 := bstep (se 1 (by rfl) ⟨1241954, by rfl⟩ : syracuseStep 1655939 = 2483909) B2483909
theorem B869523 : Blo 868566 869523 := bstep (se 1 (by rfl) ⟨652142, by rfl⟩ : syracuseStep 869523 = 1304285) B1304285
theorem B2507939 : Blo 868566 2507939 := bstep (se 1 (by rfl) ⟨1880954, by rfl⟩ : syracuseStep 2507939 = 3761909) B3761909
theorem B869539 : Blo 868566 869539 := bstep (se 1 (by rfl) ⟨652154, by rfl⟩ : syracuseStep 869539 = 1304309) B1304309
theorem B869555 : Blo 868566 869555 := bstep (se 1 (by rfl) ⟨652166, by rfl⟩ : syracuseStep 869555 = 1304333) B1304333
theorem B869571 : Blo 868566 869571 := bstep (se 1 (by rfl) ⟨652178, by rfl⟩ : syracuseStep 869571 = 1304357) B1304357
theorem B869587 : Blo 868566 869587 := bstep (se 1 (by rfl) ⟨652190, by rfl⟩ : syracuseStep 869587 = 1304381) B1304381
theorem B869603 : Blo 868566 869603 := bstep (se 1 (by rfl) ⟨652202, by rfl⟩ : syracuseStep 869603 = 1304405) B1304405
theorem B1492195 : Blo 868566 1492195 := bstep (se 1 (by rfl) ⟨1119146, by rfl⟩ : syracuseStep 1492195 = 2238293) B2238293
theorem B869619 : Blo 868566 869619 := bstep (se 1 (by rfl) ⟨652214, by rfl⟩ : syracuseStep 869619 = 1304429) B1304429
theorem B869635 : Blo 868566 869635 := bstep (se 1 (by rfl) ⟨652226, by rfl⟩ : syracuseStep 869635 = 1304453) B1304453
theorem B869651 : Blo 868566 869651 := bstep (se 1 (by rfl) ⟨652238, by rfl⟩ : syracuseStep 869651 = 1304477) B1304477
theorem B869667 : Blo 868566 869667 := bstep (se 1 (by rfl) ⟨652250, by rfl⟩ : syracuseStep 869667 = 1304501) B1304501
theorem B869683 : Blo 868566 869683 := bstep (se 1 (by rfl) ⟨652262, by rfl⟩ : syracuseStep 869683 = 1304525) B1304525
theorem B869699 : Blo 868566 869699 := bstep (se 1 (by rfl) ⟨652274, by rfl⟩ : syracuseStep 869699 = 1304549) B1304549
theorem B869715 : Blo 868566 869715 := bstep (se 1 (by rfl) ⟨652286, by rfl⟩ : syracuseStep 869715 = 1304573) B1304573
theorem B869731 : Blo 868566 869731 := bstep (se 1 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 869731 = 1304597) B1304597
theorem B869747 : Blo 868566 869747 := bstep (se 1 (by rfl) ⟨652310, by rfl⟩ : syracuseStep 869747 = 1304621) B1304621
theorem B869763 : Blo 868566 869763 := bstep (se 1 (by rfl) ⟨652322, by rfl⟩ : syracuseStep 869763 = 1304645) B1304645
theorem B869779 : Blo 868566 869779 := bstep (se 1 (by rfl) ⟨652334, by rfl⟩ : syracuseStep 869779 = 1304669) B1304669
theorem B869795 : Blo 868566 869795 := bstep (se 1 (by rfl) ⟨652346, by rfl⟩ : syracuseStep 869795 = 1304693) B1304693
theorem B1656227 : Blo 868566 1656227 := bstep (se 1 (by rfl) ⟨1242170, by rfl⟩ : syracuseStep 1656227 = 2484341) B2484341
theorem B869811 : Blo 868566 869811 := bstep (se 1 (by rfl) ⟨652358, by rfl⟩ : syracuseStep 869811 = 1304717) B1304717
theorem B869827 : Blo 868566 869827 := bstep (se 1 (by rfl) ⟨652370, by rfl⟩ : syracuseStep 869827 = 1304741) B1304741
theorem B1983953 : Blo 868566 1983953 := bstep (se 2 (by rfl) ⟨743982, by rfl⟩ : syracuseStep 1983953 = 1487965) B1487965
theorem B869843 : Blo 868566 869843 := bstep (se 1 (by rfl) ⟨652382, by rfl⟩ : syracuseStep 869843 = 1304765) B1304765
theorem B869859 : Blo 868566 869859 := bstep (se 1 (by rfl) ⟨652394, by rfl⟩ : syracuseStep 869859 = 1304789) B1304789
theorem B869875 : Blo 868566 869875 := bstep (se 1 (by rfl) ⟨652406, by rfl⟩ : syracuseStep 869875 = 1304813) B1304813
theorem B869891 : Blo 868566 869891 := bstep (se 1 (by rfl) ⟨652418, by rfl⟩ : syracuseStep 869891 = 1304837) B1304837
theorem B869907 : Blo 868566 869907 := bstep (se 1 (by rfl) ⟨652430, by rfl⟩ : syracuseStep 869907 = 1304861) B1304861
theorem B869923 : Blo 868566 869923 := bstep (se 1 (by rfl) ⟨652442, by rfl⟩ : syracuseStep 869923 = 1304885) B1304885
theorem B869939 : Blo 868566 869939 := bstep (se 1 (by rfl) ⟨652454, by rfl⟩ : syracuseStep 869939 = 1304909) B1304909
theorem B869955 : Blo 868566 869955 := bstep (se 1 (by rfl) ⟨652466, by rfl⟩ : syracuseStep 869955 = 1304933) B1304933
theorem B869971 : Blo 868566 869971 := bstep (se 1 (by rfl) ⟨652478, by rfl⟩ : syracuseStep 869971 = 1304957) B1304957
theorem B869987 : Blo 868566 869987 := bstep (se 1 (by rfl) ⟨652490, by rfl⟩ : syracuseStep 869987 = 1304981) B1304981
theorem B870003 : Blo 868566 870003 := bstep (se 1 (by rfl) ⟨652502, by rfl⟩ : syracuseStep 870003 = 1305005) B1305005
theorem B870019 : Blo 868566 870019 := bstep (se 1 (by rfl) ⟨652514, by rfl⟩ : syracuseStep 870019 = 1305029) B1305029
theorem B2934413 : Blo 868566 2934413 := bstep (se 3 (by rfl) ⟨550202, by rfl⟩ : syracuseStep 2934413 = 1100405) B1100405
theorem B870035 : Blo 868566 870035 := bstep (se 1 (by rfl) ⟨652526, by rfl⟩ : syracuseStep 870035 = 1305053) B1305053
theorem B870051 : Blo 868566 870051 := bstep (se 1 (by rfl) ⟨652538, by rfl⟩ : syracuseStep 870051 = 1305077) B1305077
theorem B870067 : Blo 868566 870067 := bstep (se 1 (by rfl) ⟨652550, by rfl⟩ : syracuseStep 870067 = 1305101) B1305101
theorem B2934467 : Blo 868566 2934467 := bstep (se 1 (by rfl) ⟨2200850, by rfl⟩ : syracuseStep 2934467 = 4401701) B4401701
theorem B870083 : Blo 868566 870083 := bstep (se 1 (by rfl) ⟨652562, by rfl⟩ : syracuseStep 870083 = 1305125) B1305125
theorem B870099 : Blo 868566 870099 := bstep (se 1 (by rfl) ⟨652574, by rfl⟩ : syracuseStep 870099 = 1305149) B1305149
theorem B870115 : Blo 868566 870115 := bstep (se 1 (by rfl) ⟨652586, by rfl⟩ : syracuseStep 870115 = 1305173) B1305173
theorem B870131 : Blo 868566 870131 := bstep (se 1 (by rfl) ⟨652598, by rfl⟩ : syracuseStep 870131 = 1305197) B1305197
theorem B870147 : Blo 868566 870147 := bstep (se 1 (by rfl) ⟨652610, by rfl⟩ : syracuseStep 870147 = 1305221) B1305221
theorem B870163 : Blo 868566 870163 := bstep (se 1 (by rfl) ⟨652622, by rfl⟩ : syracuseStep 870163 = 1305245) B1305245
theorem B870179 : Blo 868566 870179 := bstep (se 1 (by rfl) ⟨652634, by rfl⟩ : syracuseStep 870179 = 1305269) B1305269
theorem B2475821 : Blo 868566 2475821 := bstep (se 3 (by rfl) ⟨464216, by rfl⟩ : syracuseStep 2475821 = 928433) B928433
theorem B5949233 : Blo 868566 5949233 := bstep (se 2 (by rfl) ⟨2230962, by rfl⟩ : syracuseStep 5949233 = 4461925) B4461925
theorem B870195 : Blo 868566 870195 := bstep (se 1 (by rfl) ⟨652646, by rfl⟩ : syracuseStep 870195 = 1305293) B1305293
theorem B870211 : Blo 868566 870211 := bstep (se 1 (by rfl) ⟨652658, by rfl⟩ : syracuseStep 870211 = 1305317) B1305317
theorem B870227 : Blo 868566 870227 := bstep (se 1 (by rfl) ⟨652670, by rfl⟩ : syracuseStep 870227 = 1305341) B1305341
theorem B870243 : Blo 868566 870243 := bstep (se 1 (by rfl) ⟨652682, by rfl⟩ : syracuseStep 870243 = 1305365) B1305365
theorem B870259 : Blo 868566 870259 := bstep (se 1 (by rfl) ⟨652694, by rfl⟩ : syracuseStep 870259 = 1305389) B1305389
theorem B1099651 : Blo 868566 1099651 := bstep (se 1 (by rfl) ⟨824738, by rfl⟩ : syracuseStep 1099651 = 1649477) B1649477
theorem B870275 : Blo 868566 870275 := bstep (se 1 (by rfl) ⟨652706, by rfl⟩ : syracuseStep 870275 = 1305413) B1305413
theorem B870291 : Blo 868566 870291 := bstep (se 1 (by rfl) ⟨652718, by rfl⟩ : syracuseStep 870291 = 1305437) B1305437
theorem B870307 : Blo 868566 870307 := bstep (se 1 (by rfl) ⟨652730, by rfl⟩ : syracuseStep 870307 = 1305461) B1305461
theorem B870323 : Blo 868566 870323 := bstep (se 1 (by rfl) ⟨652742, by rfl⟩ : syracuseStep 870323 = 1305485) B1305485
theorem B870339 : Blo 868566 870339 := bstep (se 1 (by rfl) ⟨652754, by rfl⟩ : syracuseStep 870339 = 1305509) B1305509
theorem B2934737 : Blo 868566 2934737 := bstep (se 2 (by rfl) ⟨1100526, by rfl⟩ : syracuseStep 2934737 = 2201053) B2201053
theorem B870355 : Blo 868566 870355 := bstep (se 1 (by rfl) ⟨652766, by rfl⟩ : syracuseStep 870355 = 1305533) B1305533
theorem B1099747 : Blo 868566 1099747 := bstep (se 1 (by rfl) ⟨824810, by rfl⟩ : syracuseStep 1099747 = 1649621) B1649621
theorem B2476003 : Blo 868566 2476003 := bstep (se 1 (by rfl) ⟨1857002, by rfl⟩ : syracuseStep 2476003 = 3714005) B3714005
theorem B870371 : Blo 868566 870371 := bstep (se 1 (by rfl) ⟨652778, by rfl⟩ : syracuseStep 870371 = 1305557) B1305557
theorem B4409315 : Blo 868566 4409315 := bstep (se 1 (by rfl) ⟨3306986, by rfl⟩ : syracuseStep 4409315 = 6613973) B6613973
theorem B870387 : Blo 868566 870387 := bstep (se 1 (by rfl) ⟨652790, by rfl⟩ : syracuseStep 870387 = 1305581) B1305581
theorem B870403 : Blo 868566 870403 := bstep (se 1 (by rfl) ⟨652802, by rfl⟩ : syracuseStep 870403 = 1305605) B1305605
theorem B870419 : Blo 868566 870419 := bstep (se 1 (by rfl) ⟨652814, by rfl⟩ : syracuseStep 870419 = 1305629) B1305629
theorem B870435 : Blo 868566 870435 := bstep (se 1 (by rfl) ⟨652826, by rfl⟩ : syracuseStep 870435 = 1305653) B1305653
theorem B870451 : Blo 868566 870451 := bstep (se 1 (by rfl) ⟨652838, by rfl⟩ : syracuseStep 870451 = 1305677) B1305677
theorem B870467 : Blo 868566 870467 := bstep (se 1 (by rfl) ⟨652850, by rfl⟩ : syracuseStep 870467 = 1305701) B1305701
theorem B870483 : Blo 868566 870483 := bstep (se 1 (by rfl) ⟨652862, by rfl⟩ : syracuseStep 870483 = 1305725) B1305725
theorem B870499 : Blo 868566 870499 := bstep (se 1 (by rfl) ⟨652874, by rfl⟩ : syracuseStep 870499 = 1305749) B1305749
theorem B870515 : Blo 868566 870515 := bstep (se 1 (by rfl) ⟨652886, by rfl⟩ : syracuseStep 870515 = 1305773) B1305773
theorem B2476163 : Blo 868566 2476163 := bstep (se 1 (by rfl) ⟨1857122, by rfl⟩ : syracuseStep 2476163 = 3714245) B3714245
theorem B870531 : Blo 868566 870531 := bstep (se 1 (by rfl) ⟨652898, by rfl⟩ : syracuseStep 870531 = 1305797) B1305797
theorem B1591427 : Blo 868566 1591427 := bstep (se 1 (by rfl) ⟨1193570, by rfl⟩ : syracuseStep 1591427 = 2387141) B2387141
theorem B4966541 : Blo 868566 4966541 := bstep (se 3 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 4966541 = 1862453) B1862453
theorem B870547 : Blo 868566 870547 := bstep (se 1 (by rfl) ⟨652910, by rfl⟩ : syracuseStep 870547 = 1305821) B1305821
theorem B870563 : Blo 868566 870563 := bstep (se 1 (by rfl) ⟨652922, by rfl⟩ : syracuseStep 870563 = 1305845) B1305845
theorem B4475057 : Blo 868566 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B870579 : Blo 868566 870579 := bstep (se 1 (by rfl) ⟨652934, by rfl⟩ : syracuseStep 870579 = 1305869) B1305869
theorem B2508995 : Blo 868566 2508995 := bstep (se 1 (by rfl) ⟨1881746, by rfl⟩ : syracuseStep 2508995 = 3763493) B3763493
theorem B870595 : Blo 868566 870595 := bstep (se 1 (by rfl) ⟨652946, by rfl⟩ : syracuseStep 870595 = 1305893) B1305893
theorem B870611 : Blo 868566 870611 := bstep (se 1 (by rfl) ⟨652958, by rfl⟩ : syracuseStep 870611 = 1305917) B1305917
theorem B870627 : Blo 868566 870627 := bstep (se 1 (by rfl) ⟨652970, by rfl⟩ : syracuseStep 870627 = 1305941) B1305941
theorem B870643 : Blo 868566 870643 := bstep (se 1 (by rfl) ⟨652982, by rfl⟩ : syracuseStep 870643 = 1305965) B1305965
theorem B870659 : Blo 868566 870659 := bstep (se 1 (by rfl) ⟨652994, by rfl⟩ : syracuseStep 870659 = 1305989) B1305989
theorem B870675 : Blo 868566 870675 := bstep (se 1 (by rfl) ⟨653006, by rfl⟩ : syracuseStep 870675 = 1306013) B1306013
theorem B870691 : Blo 868566 870691 := bstep (se 1 (by rfl) ⟨653018, by rfl⟩ : syracuseStep 870691 = 1306037) B1306037
theorem B870707 : Blo 868566 870707 := bstep (se 1 (by rfl) ⟨653030, by rfl⟩ : syracuseStep 870707 = 1306061) B1306061
theorem B1394995 : Blo 868566 1394995 := bstep (se 1 (by rfl) ⟨1046246, by rfl⟩ : syracuseStep 1394995 = 2092493) B2092493
theorem B870723 : Blo 868566 870723 := bstep (se 1 (by rfl) ⟨653042, by rfl⟩ : syracuseStep 870723 = 1306085) B1306085
theorem B870739 : Blo 868566 870739 := bstep (se 1 (by rfl) ⟨653054, by rfl⟩ : syracuseStep 870739 = 1306109) B1306109
theorem B870755 : Blo 868566 870755 := bstep (se 1 (by rfl) ⟨653066, by rfl⟩ : syracuseStep 870755 = 1306133) B1306133
theorem B870771 : Blo 868566 870771 := bstep (se 1 (by rfl) ⟨653078, by rfl⟩ : syracuseStep 870771 = 1306157) B1306157
theorem B870787 : Blo 868566 870787 := bstep (se 1 (by rfl) ⟨653090, by rfl⟩ : syracuseStep 870787 = 1306181) B1306181
theorem B870803 : Blo 868566 870803 := bstep (se 1 (by rfl) ⟨653102, by rfl⟩ : syracuseStep 870803 = 1306205) B1306205
theorem B870819 : Blo 868566 870819 := bstep (se 1 (by rfl) ⟨653114, by rfl⟩ : syracuseStep 870819 = 1306229) B1306229
theorem B870835 : Blo 868566 870835 := bstep (se 1 (by rfl) ⟨653126, by rfl⟩ : syracuseStep 870835 = 1306253) B1306253
theorem B870851 : Blo 868566 870851 := bstep (se 1 (by rfl) ⟨653138, by rfl⟩ : syracuseStep 870851 = 1306277) B1306277
theorem B1100243 : Blo 868566 1100243 := bstep (se 1 (by rfl) ⟨825182, by rfl⟩ : syracuseStep 1100243 = 1650365) B1650365
theorem B870867 : Blo 868566 870867 := bstep (se 1 (by rfl) ⟨653150, by rfl⟩ : syracuseStep 870867 = 1306301) B1306301
theorem B870883 : Blo 868566 870883 := bstep (se 1 (by rfl) ⟨653162, by rfl⟩ : syracuseStep 870883 = 1306325) B1306325
theorem B2935277 : Blo 868566 2935277 := bstep (se 3 (by rfl) ⟨550364, by rfl⟩ : syracuseStep 2935277 = 1100729) B1100729
theorem B870899 : Blo 868566 870899 := bstep (se 1 (by rfl) ⟨653174, by rfl⟩ : syracuseStep 870899 = 1306349) B1306349
theorem B870915 : Blo 868566 870915 := bstep (se 1 (by rfl) ⟨653186, by rfl⟩ : syracuseStep 870915 = 1306373) B1306373
theorem B870931 : Blo 868566 870931 := bstep (se 1 (by rfl) ⟨653198, by rfl⟩ : syracuseStep 870931 = 1306397) B1306397
theorem B2935331 : Blo 868566 2935331 := bstep (se 1 (by rfl) ⟨2201498, by rfl⟩ : syracuseStep 2935331 = 4402997) B4402997
theorem B870947 : Blo 868566 870947 := bstep (se 1 (by rfl) ⟨653210, by rfl⟩ : syracuseStep 870947 = 1306421) B1306421
theorem B870963 : Blo 868566 870963 := bstep (se 1 (by rfl) ⟨653222, by rfl⟩ : syracuseStep 870963 = 1306445) B1306445
theorem B870979 : Blo 868566 870979 := bstep (se 1 (by rfl) ⟨653234, by rfl⟩ : syracuseStep 870979 = 1306469) B1306469
theorem B870995 : Blo 868566 870995 := bstep (se 1 (by rfl) ⟨653246, by rfl⟩ : syracuseStep 870995 = 1306493) B1306493
theorem B871011 : Blo 868566 871011 := bstep (se 1 (by rfl) ⟨653258, by rfl⟩ : syracuseStep 871011 = 1306517) B1306517
theorem B871027 : Blo 868566 871027 := bstep (se 1 (by rfl) ⟨653270, by rfl⟩ : syracuseStep 871027 = 1306541) B1306541
theorem B871043 : Blo 868566 871043 := bstep (se 1 (by rfl) ⟨653282, by rfl⟩ : syracuseStep 871043 = 1306565) B1306565
theorem B871059 : Blo 868566 871059 := bstep (se 1 (by rfl) ⟨653294, by rfl⟩ : syracuseStep 871059 = 1306589) B1306589
theorem B871075 : Blo 868566 871075 := bstep (se 1 (by rfl) ⟨653306, by rfl⟩ : syracuseStep 871075 = 1306613) B1306613
theorem B871091 : Blo 868566 871091 := bstep (se 1 (by rfl) ⟨653318, by rfl⟩ : syracuseStep 871091 = 1306637) B1306637
theorem B871107 : Blo 868566 871107 := bstep (se 1 (by rfl) ⟨653330, by rfl⟩ : syracuseStep 871107 = 1306661) B1306661
theorem B871123 : Blo 868566 871123 := bstep (se 1 (by rfl) ⟨653342, by rfl⟩ : syracuseStep 871123 = 1306685) B1306685
theorem B871139 : Blo 868566 871139 := bstep (se 1 (by rfl) ⟨653354, by rfl⟩ : syracuseStep 871139 = 1306709) B1306709
theorem B871155 : Blo 868566 871155 := bstep (se 1 (by rfl) ⟨653366, by rfl⟩ : syracuseStep 871155 = 1306733) B1306733
theorem B871171 : Blo 868566 871171 := bstep (se 1 (by rfl) ⟨653378, by rfl⟩ : syracuseStep 871171 = 1306757) B1306757
theorem B4410125 : Blo 868566 4410125 := bstep (se 3 (by rfl) ⟨826898, by rfl⟩ : syracuseStep 4410125 = 1653797) B1653797
theorem B871187 : Blo 868566 871187 := bstep (se 1 (by rfl) ⟨653390, by rfl⟩ : syracuseStep 871187 = 1306781) B1306781
theorem B871203 : Blo 868566 871203 := bstep (se 1 (by rfl) ⟨653402, by rfl⟩ : syracuseStep 871203 = 1306805) B1306805
theorem B2935601 : Blo 868566 2935601 := bstep (se 2 (by rfl) ⟨1100850, by rfl⟩ : syracuseStep 2935601 = 2201701) B2201701
theorem B871219 : Blo 868566 871219 := bstep (se 1 (by rfl) ⟨653414, by rfl⟩ : syracuseStep 871219 = 1306829) B1306829
theorem B871235 : Blo 868566 871235 := bstep (se 1 (by rfl) ⟨653426, by rfl⟩ : syracuseStep 871235 = 1306853) B1306853
theorem B871251 : Blo 868566 871251 := bstep (se 1 (by rfl) ⟨653438, by rfl⟩ : syracuseStep 871251 = 1306877) B1306877
theorem B871267 : Blo 868566 871267 := bstep (se 1 (by rfl) ⟨653450, by rfl⟩ : syracuseStep 871267 = 1306901) B1306901
theorem B871283 : Blo 868566 871283 := bstep (se 1 (by rfl) ⟨653462, by rfl⟩ : syracuseStep 871283 = 1306925) B1306925
theorem B871299 : Blo 868566 871299 := bstep (se 1 (by rfl) ⟨653474, by rfl⟩ : syracuseStep 871299 = 1306949) B1306949
theorem B871315 : Blo 868566 871315 := bstep (se 1 (by rfl) ⟨653486, by rfl⟩ : syracuseStep 871315 = 1306973) B1306973
theorem B871331 : Blo 868566 871331 := bstep (se 1 (by rfl) ⟨653498, by rfl⟩ : syracuseStep 871331 = 1306997) B1306997
theorem B871347 : Blo 868566 871347 := bstep (se 1 (by rfl) ⟨653510, by rfl⟩ : syracuseStep 871347 = 1307021) B1307021
theorem B871363 : Blo 868566 871363 := bstep (se 1 (by rfl) ⟨653522, by rfl⟩ : syracuseStep 871363 = 1307045) B1307045
theorem B3132365 : Blo 868566 3132365 := bstep (se 3 (by rfl) ⟨587318, by rfl⟩ : syracuseStep 3132365 = 1174637) B1174637
theorem B871379 : Blo 868566 871379 := bstep (se 1 (by rfl) ⟨653534, by rfl⟩ : syracuseStep 871379 = 1307069) B1307069
theorem B871395 : Blo 868566 871395 := bstep (se 1 (by rfl) ⟨653546, by rfl⟩ : syracuseStep 871395 = 1307093) B1307093
theorem B871411 : Blo 868566 871411 := bstep (se 1 (by rfl) ⟨653558, by rfl⟩ : syracuseStep 871411 = 1307117) B1307117
theorem B1395713 : Blo 868566 1395713 := bstep (se 2 (by rfl) ⟨523392, by rfl⟩ : syracuseStep 1395713 = 1046785) B1046785
theorem B871427 : Blo 868566 871427 := bstep (se 1 (by rfl) ⟨653570, by rfl⟩ : syracuseStep 871427 = 1307141) B1307141
theorem B871443 : Blo 868566 871443 := bstep (se 1 (by rfl) ⟨653582, by rfl⟩ : syracuseStep 871443 = 1307165) B1307165
theorem B871459 : Blo 868566 871459 := bstep (se 1 (by rfl) ⟨653594, by rfl⟩ : syracuseStep 871459 = 1307189) B1307189
theorem B871475 : Blo 868566 871475 := bstep (se 1 (by rfl) ⟨653606, by rfl⟩ : syracuseStep 871475 = 1307213) B1307213
theorem B871491 : Blo 868566 871491 := bstep (se 1 (by rfl) ⟨653618, by rfl⟩ : syracuseStep 871491 = 1307237) B1307237
theorem B871507 : Blo 868566 871507 := bstep (se 1 (by rfl) ⟨653630, by rfl⟩ : syracuseStep 871507 = 1307261) B1307261
theorem B1592419 : Blo 868566 1592419 := bstep (se 1 (by rfl) ⟨1194314, by rfl⟩ : syracuseStep 1592419 = 2388629) B2388629
theorem B871523 : Blo 868566 871523 := bstep (se 1 (by rfl) ⟨653642, by rfl⟩ : syracuseStep 871523 = 1307285) B1307285
theorem B871539 : Blo 868566 871539 := bstep (se 1 (by rfl) ⟨653654, by rfl⟩ : syracuseStep 871539 = 1307309) B1307309
theorem B871555 : Blo 868566 871555 := bstep (se 1 (by rfl) ⟨653666, by rfl⟩ : syracuseStep 871555 = 1307333) B1307333
theorem B1100947 : Blo 868566 1100947 := bstep (se 1 (by rfl) ⟨825710, by rfl⟩ : syracuseStep 1100947 = 1651421) B1651421
theorem B871571 : Blo 868566 871571 := bstep (se 1 (by rfl) ⟨653678, by rfl⟩ : syracuseStep 871571 = 1307357) B1307357
theorem B871587 : Blo 868566 871587 := bstep (se 1 (by rfl) ⟨653690, by rfl⟩ : syracuseStep 871587 = 1307381) B1307381
theorem B2477233 : Blo 868566 2477233 := bstep (se 2 (by rfl) ⟨928962, by rfl⟩ : syracuseStep 2477233 = 1857925) B1857925
theorem B871603 : Blo 868566 871603 := bstep (se 1 (by rfl) ⟨653702, by rfl⟩ : syracuseStep 871603 = 1307405) B1307405
theorem B871619 : Blo 868566 871619 := bstep (se 1 (by rfl) ⟨653714, by rfl⟩ : syracuseStep 871619 = 1307429) B1307429
theorem B871635 : Blo 868566 871635 := bstep (se 1 (by rfl) ⟨653726, by rfl⟩ : syracuseStep 871635 = 1307453) B1307453
theorem B871651 : Blo 868566 871651 := bstep (se 1 (by rfl) ⟨653738, by rfl⟩ : syracuseStep 871651 = 1307477) B1307477
theorem B871667 : Blo 868566 871667 := bstep (se 1 (by rfl) ⟨653750, by rfl⟩ : syracuseStep 871667 = 1307501) B1307501
theorem B1101043 : Blo 868566 1101043 := bstep (se 1 (by rfl) ⟨825782, by rfl⟩ : syracuseStep 1101043 = 1651565) B1651565
theorem B871683 : Blo 868566 871683 := bstep (se 1 (by rfl) ⟨653762, by rfl⟩ : syracuseStep 871683 = 1307525) B1307525
theorem B871699 : Blo 868566 871699 := bstep (se 1 (by rfl) ⟨653774, by rfl⟩ : syracuseStep 871699 = 1307549) B1307549
theorem B1133843 : Blo 868566 1133843 := bstep (se 1 (by rfl) ⟨850382, by rfl⟩ : syracuseStep 1133843 = 1700765) B1700765
theorem B1396001 : Blo 868566 1396001 := bstep (se 2 (by rfl) ⟨523500, by rfl⟩ : syracuseStep 1396001 = 1047001) B1047001
theorem B871715 : Blo 868566 871715 := bstep (se 1 (by rfl) ⟨653786, by rfl⟩ : syracuseStep 871715 = 1307573) B1307573
theorem B871731 : Blo 868566 871731 := bstep (se 1 (by rfl) ⟨653798, by rfl⟩ : syracuseStep 871731 = 1307597) B1307597
theorem B871747 : Blo 868566 871747 := bstep (se 1 (by rfl) ⟨653810, by rfl⟩ : syracuseStep 871747 = 1307621) B1307621
theorem B2936141 : Blo 868566 2936141 := bstep (se 3 (by rfl) ⟨550526, by rfl⟩ : syracuseStep 2936141 = 1101053) B1101053
theorem B871763 : Blo 868566 871763 := bstep (se 1 (by rfl) ⟨653822, by rfl⟩ : syracuseStep 871763 = 1307645) B1307645
theorem B871779 : Blo 868566 871779 := bstep (se 1 (by rfl) ⟨653834, by rfl⟩ : syracuseStep 871779 = 1307669) B1307669
theorem B871795 : Blo 868566 871795 := bstep (se 1 (by rfl) ⟨653846, by rfl⟩ : syracuseStep 871795 = 1307693) B1307693
theorem B2936195 : Blo 868566 2936195 := bstep (se 1 (by rfl) ⟨2202146, by rfl⟩ : syracuseStep 2936195 = 4404293) B4404293
theorem B871811 : Blo 868566 871811 := bstep (se 1 (by rfl) ⟨653858, by rfl⟩ : syracuseStep 871811 = 1307717) B1307717
theorem B871827 : Blo 868566 871827 := bstep (se 1 (by rfl) ⟨653870, by rfl⟩ : syracuseStep 871827 = 1307741) B1307741
theorem B871843 : Blo 868566 871843 := bstep (se 1 (by rfl) ⟨653882, by rfl⟩ : syracuseStep 871843 = 1307765) B1307765
theorem B871859 : Blo 868566 871859 := bstep (se 1 (by rfl) ⟨653894, by rfl⟩ : syracuseStep 871859 = 1307789) B1307789
theorem B871875 : Blo 868566 871875 := bstep (se 1 (by rfl) ⟨653906, by rfl⟩ : syracuseStep 871875 = 1307813) B1307813
theorem B871891 : Blo 868566 871891 := bstep (se 1 (by rfl) ⟨653918, by rfl⟩ : syracuseStep 871891 = 1307837) B1307837
theorem B871907 : Blo 868566 871907 := bstep (se 1 (by rfl) ⟨653930, by rfl⟩ : syracuseStep 871907 = 1307861) B1307861
theorem B871923 : Blo 868566 871923 := bstep (se 1 (by rfl) ⟨653942, by rfl⟩ : syracuseStep 871923 = 1307885) B1307885
theorem B1396225 : Blo 868566 1396225 := bstep (se 2 (by rfl) ⟨523584, by rfl⟩ : syracuseStep 1396225 = 1047169) B1047169
theorem B871939 : Blo 868566 871939 := bstep (se 1 (by rfl) ⟨653954, by rfl⟩ : syracuseStep 871939 = 1307909) B1307909
theorem B871955 : Blo 868566 871955 := bstep (se 1 (by rfl) ⟨653966, by rfl⟩ : syracuseStep 871955 = 1307933) B1307933
theorem B871971 : Blo 868566 871971 := bstep (se 1 (by rfl) ⟨653978, by rfl⟩ : syracuseStep 871971 = 1307957) B1307957
theorem B871987 : Blo 868566 871987 := bstep (se 1 (by rfl) ⟨653990, by rfl⟩ : syracuseStep 871987 = 1307981) B1307981
theorem B872003 : Blo 868566 872003 := bstep (se 1 (by rfl) ⟨654002, by rfl⟩ : syracuseStep 872003 = 1308005) B1308005
theorem B872019 : Blo 868566 872019 := bstep (se 1 (by rfl) ⟨654014, by rfl⟩ : syracuseStep 872019 = 1308029) B1308029
theorem B872035 : Blo 868566 872035 := bstep (se 1 (by rfl) ⟨654026, by rfl⟩ : syracuseStep 872035 = 1308053) B1308053
theorem B872051 : Blo 868566 872051 := bstep (se 1 (by rfl) ⟨654038, by rfl⟩ : syracuseStep 872051 = 1308077) B1308077
theorem B872067 : Blo 868566 872067 := bstep (se 1 (by rfl) ⟨654050, by rfl⟩ : syracuseStep 872067 = 1308101) B1308101
theorem B2936465 : Blo 868566 2936465 := bstep (se 2 (by rfl) ⟨1101174, by rfl⟩ : syracuseStep 2936465 = 2202349) B2202349
theorem B872083 : Blo 868566 872083 := bstep (se 1 (by rfl) ⟨654062, by rfl⟩ : syracuseStep 872083 = 1308125) B1308125
theorem B872099 : Blo 868566 872099 := bstep (se 1 (by rfl) ⟨654074, by rfl⟩ : syracuseStep 872099 = 1308149) B1308149
theorem B5590691 : Blo 868566 5590691 := bstep (se 1 (by rfl) ⟨4193018, by rfl⟩ : syracuseStep 5590691 = 8386037) B8386037
theorem B872115 : Blo 868566 872115 := bstep (se 1 (by rfl) ⟨654086, by rfl⟩ : syracuseStep 872115 = 1308173) B1308173
theorem B872131 : Blo 868566 872131 := bstep (se 1 (by rfl) ⟨654098, by rfl⟩ : syracuseStep 872131 = 1308197) B1308197
theorem B872147 : Blo 868566 872147 := bstep (se 1 (by rfl) ⟨654110, by rfl⟩ : syracuseStep 872147 = 1308221) B1308221
theorem B1101539 : Blo 868566 1101539 := bstep (se 1 (by rfl) ⟨826154, by rfl⟩ : syracuseStep 1101539 = 1652309) B1652309
theorem B872163 : Blo 868566 872163 := bstep (se 1 (by rfl) ⟨654122, by rfl⟩ : syracuseStep 872163 = 1308245) B1308245
theorem B3722993 : Blo 868566 3722993 := bstep (se 2 (by rfl) ⟨1396122, by rfl⟩ : syracuseStep 3722993 = 2792245) B2792245
theorem B872179 : Blo 868566 872179 := bstep (se 1 (by rfl) ⟨654134, by rfl⟩ : syracuseStep 872179 = 1308269) B1308269
theorem B872195 : Blo 868566 872195 := bstep (se 1 (by rfl) ⟨654146, by rfl⟩ : syracuseStep 872195 = 1308293) B1308293
theorem B872211 : Blo 868566 872211 := bstep (se 1 (by rfl) ⟨654158, by rfl⟩ : syracuseStep 872211 = 1308317) B1308317
theorem B872227 : Blo 868566 872227 := bstep (se 1 (by rfl) ⟨654170, by rfl⟩ : syracuseStep 872227 = 1308341) B1308341
theorem B4476707 : Blo 868566 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B872243 : Blo 868566 872243 := bstep (se 1 (by rfl) ⟨654182, by rfl⟩ : syracuseStep 872243 = 1308365) B1308365
theorem B872259 : Blo 868566 872259 := bstep (se 1 (by rfl) ⟨654194, by rfl⟩ : syracuseStep 872259 = 1308389) B1308389
theorem B872275 : Blo 868566 872275 := bstep (se 1 (by rfl) ⟨654206, by rfl⟩ : syracuseStep 872275 = 1308413) B1308413
theorem B872291 : Blo 868566 872291 := bstep (se 1 (by rfl) ⟨654218, by rfl⟩ : syracuseStep 872291 = 1308437) B1308437
theorem B872307 : Blo 868566 872307 := bstep (se 1 (by rfl) ⟨654230, by rfl⟩ : syracuseStep 872307 = 1308461) B1308461
theorem B872323 : Blo 868566 872323 := bstep (se 1 (by rfl) ⟨654242, by rfl⟩ : syracuseStep 872323 = 1308485) B1308485
theorem B872339 : Blo 868566 872339 := bstep (se 1 (by rfl) ⟨654254, by rfl⟩ : syracuseStep 872339 = 1308509) B1308509
theorem B872355 : Blo 868566 872355 := bstep (se 1 (by rfl) ⟨654266, by rfl⟩ : syracuseStep 872355 = 1308533) B1308533
theorem B872371 : Blo 868566 872371 := bstep (se 1 (by rfl) ⟨654278, by rfl⟩ : syracuseStep 872371 = 1308557) B1308557
theorem B872387 : Blo 868566 872387 := bstep (se 1 (by rfl) ⟨654290, by rfl⟩ : syracuseStep 872387 = 1308581) B1308581
theorem B872403 : Blo 868566 872403 := bstep (se 1 (by rfl) ⟨654302, by rfl⟩ : syracuseStep 872403 = 1308605) B1308605
theorem B872419 : Blo 868566 872419 := bstep (se 1 (by rfl) ⟨654314, by rfl⟩ : syracuseStep 872419 = 1308629) B1308629
theorem B1986545 : Blo 868566 1986545 := bstep (se 2 (by rfl) ⟨744954, by rfl⟩ : syracuseStep 1986545 = 1489909) B1489909
theorem B872435 : Blo 868566 872435 := bstep (se 1 (by rfl) ⟨654326, by rfl⟩ : syracuseStep 872435 = 1308653) B1308653
theorem B872451 : Blo 868566 872451 := bstep (se 1 (by rfl) ⟨654338, by rfl⟩ : syracuseStep 872451 = 1308677) B1308677
theorem B872467 : Blo 868566 872467 := bstep (se 1 (by rfl) ⟨654350, by rfl⟩ : syracuseStep 872467 = 1308701) B1308701
theorem B872483 : Blo 868566 872483 := bstep (se 1 (by rfl) ⟨654362, by rfl⟩ : syracuseStep 872483 = 1308725) B1308725
theorem B872499 : Blo 868566 872499 := bstep (se 1 (by rfl) ⟨654374, by rfl⟩ : syracuseStep 872499 = 1308749) B1308749
theorem B872515 : Blo 868566 872515 := bstep (se 1 (by rfl) ⟨654386, by rfl⟩ : syracuseStep 872515 = 1308773) B1308773
theorem B10047557 : Blo 868566 10047557 := bstep (se 4 (by rfl) ⟨941958, by rfl⟩ : syracuseStep 10047557 = 1883917) B1883917
theorem B872531 : Blo 868566 872531 := bstep (se 1 (by rfl) ⟨654398, by rfl⟩ : syracuseStep 872531 = 1308797) B1308797
theorem B872547 : Blo 868566 872547 := bstep (se 1 (by rfl) ⟨654410, by rfl⟩ : syracuseStep 872547 = 1308821) B1308821
theorem B872563 : Blo 868566 872563 := bstep (se 1 (by rfl) ⟨654422, by rfl⟩ : syracuseStep 872563 = 1308845) B1308845
theorem B1855619 : Blo 868566 1855619 := bstep (se 1 (by rfl) ⟨1391714, by rfl⟩ : syracuseStep 1855619 = 2783429) B2783429
theorem B2937005 : Blo 868566 2937005 := bstep (se 3 (by rfl) ⟨550688, by rfl⟩ : syracuseStep 2937005 = 1101377) B1101377
theorem B2937059 : Blo 868566 2937059 := bstep (se 1 (by rfl) ⟨2202794, by rfl⟩ : syracuseStep 2937059 = 4405589) B4405589
theorem B125751523 : Blo 868566 125751523 := bstep (se 1 (by rfl) ⟨94313642, by rfl⟩ : syracuseStep 125751523 = 188627285) B188627285
theorem B3526897 : Blo 868566 3526897 := bstep (se 2 (by rfl) ⟨1322586, by rfl⟩ : syracuseStep 3526897 = 2645173) B2645173
theorem B4968773 : Blo 868566 4968773 := bstep (se 4 (by rfl) ⟨465822, by rfl⟩ : syracuseStep 4968773 = 931645) B931645
theorem B1102243 : Blo 868566 1102243 := bstep (se 1 (by rfl) ⟨826682, by rfl⟩ : syracuseStep 1102243 = 1653365) B1653365
theorem B2478509 : Blo 868566 2478509 := bstep (se 3 (by rfl) ⟨464720, by rfl⟩ : syracuseStep 2478509 = 929441) B929441
theorem B2937329 : Blo 868566 2937329 := bstep (se 2 (by rfl) ⟨1101498, by rfl⟩ : syracuseStep 2937329 = 2202997) B2202997
theorem B1102339 : Blo 868566 1102339 := bstep (se 1 (by rfl) ⟨826754, by rfl⟩ : syracuseStep 1102339 = 1653509) B1653509
theorem B2511395 : Blo 868566 2511395 := bstep (se 1 (by rfl) ⟨1883546, by rfl⟩ : syracuseStep 2511395 = 3767093) B3767093
theorem B1954385 : Blo 868566 1954385 := bstep (se 2 (by rfl) ⟨732894, by rfl⟩ : syracuseStep 1954385 = 1465789) B1465789
theorem B1954403 : Blo 868566 1954403 := bstep (se 1 (by rfl) ⟨1465802, by rfl⟩ : syracuseStep 1954403 = 2931605) B2931605
theorem B2478691 : Blo 868566 2478691 := bstep (se 1 (by rfl) ⟨1859018, by rfl⟩ : syracuseStep 2478691 = 3718037) B3718037
theorem B3297905 : Blo 868566 3297905 := bstep (se 2 (by rfl) ⟨1236714, by rfl⟩ : syracuseStep 3297905 = 2473429) B2473429
theorem B2478737 : Blo 868566 2478737 := bstep (se 2 (by rfl) ⟨929526, by rfl⟩ : syracuseStep 2478737 = 1859053) B1859053
theorem B1856209 : Blo 868566 1856209 := bstep (se 2 (by rfl) ⟨696078, by rfl⟩ : syracuseStep 1856209 = 1392157) B1392157
theorem B1954673 : Blo 868566 1954673 := bstep (se 2 (by rfl) ⟨733002, by rfl⟩ : syracuseStep 1954673 = 1466005) B1466005
theorem B1954691 : Blo 868566 1954691 := bstep (se 1 (by rfl) ⟨1466018, by rfl⟩ : syracuseStep 1954691 = 2932037) B2932037
theorem B4182947 : Blo 868566 4182947 := bstep (se 1 (by rfl) ⟨3137210, by rfl⟩ : syracuseStep 4182947 = 6274421) B6274421
theorem B4969457 : Blo 868566 4969457 := bstep (se 2 (by rfl) ⟨1863546, by rfl⟩ : syracuseStep 4969457 = 3727093) B3727093
theorem B1102835 : Blo 868566 1102835 := bstep (se 1 (by rfl) ⟨827126, by rfl⟩ : syracuseStep 1102835 = 1654253) B1654253
theorem B2937869 : Blo 868566 2937869 := bstep (se 3 (by rfl) ⟨550850, by rfl⟩ : syracuseStep 2937869 = 1101701) B1101701
theorem B2937923 : Blo 868566 2937923 := bstep (se 1 (by rfl) ⟨2203442, by rfl⟩ : syracuseStep 2937923 = 4406885) B4406885
theorem B4183139 : Blo 868566 4183139 := bstep (se 1 (by rfl) ⟨3137354, by rfl⟩ : syracuseStep 4183139 = 6274709) B6274709
theorem B1954961 : Blo 868566 1954961 := bstep (se 2 (by rfl) ⟨733110, by rfl⟩ : syracuseStep 1954961 = 1466221) B1466221
theorem B1954979 : Blo 868566 1954979 := bstep (se 1 (by rfl) ⟨1466234, by rfl⟩ : syracuseStep 1954979 = 2932469) B2932469
theorem B6608141 : Blo 868566 6608141 := bstep (se 3 (by rfl) ⟨1239026, by rfl⟩ : syracuseStep 6608141 = 2478053) B2478053
theorem B2938193 : Blo 868566 2938193 := bstep (se 2 (by rfl) ⟨1101822, by rfl⟩ : syracuseStep 2938193 = 2203645) B2203645
theorem B1955249 : Blo 868566 1955249 := bstep (se 2 (by rfl) ⟨733218, by rfl⟩ : syracuseStep 1955249 = 1466437) B1466437
theorem B1955267 : Blo 868566 1955267 := bstep (se 1 (by rfl) ⟨1466450, by rfl⟩ : syracuseStep 1955267 = 2932901) B2932901
theorem B4413041 : Blo 868566 4413041 := bstep (se 2 (by rfl) ⟨1654890, by rfl⟩ : syracuseStep 4413041 = 3309781) B3309781
theorem B1103539 : Blo 868566 1103539 := bstep (se 1 (by rfl) ⟨827654, by rfl⟩ : syracuseStep 1103539 = 1655309) B1655309
theorem B1955537 : Blo 868566 1955537 := bstep (se 2 (by rfl) ⟨733326, by rfl⟩ : syracuseStep 1955537 = 1466653) B1466653
theorem B1955555 : Blo 868566 1955555 := bstep (se 1 (by rfl) ⟨1466666, by rfl⟩ : syracuseStep 1955555 = 2933333) B2933333
theorem B1103635 : Blo 868566 1103635 := bstep (se 1 (by rfl) ⟨827726, by rfl⟩ : syracuseStep 1103635 = 1655453) B1655453
theorem B2938733 : Blo 868566 2938733 := bstep (se 3 (by rfl) ⟨551012, by rfl⟩ : syracuseStep 2938733 = 1102025) B1102025
theorem B2938787 : Blo 868566 2938787 := bstep (se 1 (by rfl) ⟨2204090, by rfl⟩ : syracuseStep 2938787 = 4408181) B4408181
theorem B2349005 : Blo 868566 2349005 := bstep (se 3 (by rfl) ⟨440438, by rfl⟩ : syracuseStep 2349005 = 880877) B880877
theorem B1955825 : Blo 868566 1955825 := bstep (se 2 (by rfl) ⟨733434, by rfl⟩ : syracuseStep 1955825 = 1466869) B1466869
theorem B1955843 : Blo 868566 1955843 := bstep (se 1 (by rfl) ⟨1466882, by rfl⟩ : syracuseStep 1955843 = 2933765) B2933765
theorem B3299363 : Blo 868566 3299363 := bstep (se 1 (by rfl) ⟨2474522, by rfl⟩ : syracuseStep 3299363 = 4949045) B4949045
theorem B2480195 : Blo 868566 2480195 := bstep (se 1 (by rfl) ⟨1860146, by rfl⟩ : syracuseStep 2480195 = 3720293) B3720293
theorem B3725453 : Blo 868566 3725453 := bstep (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) B1397045
theorem B2939057 : Blo 868566 2939057 := bstep (se 2 (by rfl) ⟨1102146, by rfl⟩ : syracuseStep 2939057 = 2204293) B2204293
theorem B8476913 : Blo 868566 8476913 := bstep (se 2 (by rfl) ⟨3178842, by rfl⟩ : syracuseStep 8476913 = 6357685) B6357685
theorem B1104131 : Blo 868566 1104131 := bstep (se 1 (by rfl) ⟨828098, by rfl⟩ : syracuseStep 1104131 = 1656197) B1656197
theorem B1956113 : Blo 868566 1956113 := bstep (se 2 (by rfl) ⟨733542, by rfl⟩ : syracuseStep 1956113 = 1467085) B1467085
theorem B1956131 : Blo 868566 1956131 := bstep (se 1 (by rfl) ⟨1467098, by rfl⟩ : syracuseStep 1956131 = 2934197) B2934197
theorem B4184369 : Blo 868566 4184369 := bstep (se 2 (by rfl) ⟨1569138, by rfl⟩ : syracuseStep 4184369 = 3138277) B3138277
theorem B9918773 : Blo 868566 9918773 := bstep (se 5 (by rfl) ⟨464942, by rfl⟩ : syracuseStep 9918773 = 929885) B929885
theorem B2546029 : Blo 868566 2546029 := bstep (se 3 (by rfl) ⟨477380, by rfl⟩ : syracuseStep 2546029 = 954761) B954761
theorem B9525617 : Blo 868566 9525617 := bstep (se 2 (by rfl) ⟨3572106, by rfl⟩ : syracuseStep 9525617 = 7144213) B7144213
theorem B3135971 : Blo 868566 3135971 := bstep (se 1 (by rfl) ⟨2351978, by rfl⟩ : syracuseStep 3135971 = 4703957) B4703957
theorem B1956401 : Blo 868566 1956401 := bstep (se 2 (by rfl) ⟨733650, by rfl⟩ : syracuseStep 1956401 = 1467301) B1467301
theorem B1956419 : Blo 868566 1956419 := bstep (se 1 (by rfl) ⟨1467314, by rfl⟩ : syracuseStep 1956419 = 2934629) B2934629
theorem B2939597 : Blo 868566 2939597 := bstep (se 3 (by rfl) ⟨551174, by rfl⟩ : syracuseStep 2939597 = 1102349) B1102349
theorem B2939651 : Blo 868566 2939651 := bstep (se 1 (by rfl) ⟨2204738, by rfl⟩ : syracuseStep 2939651 = 4409477) B4409477
theorem B2513713 : Blo 868566 2513713 := bstep (se 2 (by rfl) ⟨942642, by rfl⟩ : syracuseStep 2513713 = 1885285) B1885285
theorem B5954381 : Blo 868566 5954381 := bstep (se 3 (by rfl) ⟨1116446, by rfl⟩ : syracuseStep 5954381 = 2232893) B2232893
theorem B1956689 : Blo 868566 1956689 := bstep (se 2 (by rfl) ⟨733758, by rfl⟩ : syracuseStep 1956689 = 1467517) B1467517
theorem B1956707 : Blo 868566 1956707 := bstep (se 1 (by rfl) ⟨1467530, by rfl⟩ : syracuseStep 1956707 = 2935061) B2935061
theorem B5659589 : Blo 868566 5659589 := bstep (se 4 (by rfl) ⟨530586, by rfl⟩ : syracuseStep 5659589 = 1061173) B1061173
theorem B3300365 : Blo 868566 3300365 := bstep (se 3 (by rfl) ⟨618818, by rfl⟩ : syracuseStep 3300365 = 1237637) B1237637
theorem B2939921 : Blo 868566 2939921 := bstep (se 2 (by rfl) ⟨1102470, by rfl⟩ : syracuseStep 2939921 = 2204941) B2204941
theorem B4414499 : Blo 868566 4414499 := bstep (se 1 (by rfl) ⟨3310874, by rfl⟩ : syracuseStep 4414499 = 6621749) B6621749
theorem B9657413 : Blo 868566 9657413 := bstep (se 4 (by rfl) ⟨905382, by rfl⟩ : syracuseStep 9657413 = 1810765) B1810765
theorem B1072211 : Blo 868566 1072211 := bstep (se 1 (by rfl) ⟨804158, by rfl⟩ : syracuseStep 1072211 = 1608317) B1608317
theorem B1956977 : Blo 868566 1956977 := bstep (se 2 (by rfl) ⟨733866, by rfl⟩ : syracuseStep 1956977 = 1467733) B1467733
theorem B1956995 : Blo 868566 1956995 := bstep (se 1 (by rfl) ⟨1467746, by rfl⟩ : syracuseStep 1956995 = 2935493) B2935493
theorem B4709603 : Blo 868566 4709603 := bstep (se 1 (by rfl) ⟨3532202, by rfl⟩ : syracuseStep 4709603 = 7064405) B7064405
theorem B6282467 : Blo 868566 6282467 := bstep (se 1 (by rfl) ⟨4711850, by rfl⟩ : syracuseStep 6282467 = 9423701) B9423701
theorem B2481425 : Blo 868566 2481425 := bstep (se 2 (by rfl) ⟨930534, by rfl⟩ : syracuseStep 2481425 = 1861069) B1861069
theorem B1465715 : Blo 868566 1465715 := bstep (se 1 (by rfl) ⟨1099286, by rfl⟩ : syracuseStep 1465715 = 2198573) B2198573
theorem B4709773 : Blo 868566 4709773 := bstep (se 3 (by rfl) ⟨883082, by rfl⟩ : syracuseStep 4709773 = 1766165) B1766165
theorem B1957265 : Blo 868566 1957265 := bstep (se 2 (by rfl) ⟨733974, by rfl⟩ : syracuseStep 1957265 = 1467949) B1467949
theorem B1957283 : Blo 868566 1957283 := bstep (se 1 (by rfl) ⟨1467962, by rfl⟩ : syracuseStep 1957283 = 2935925) B2935925
theorem B3726769 : Blo 868566 3726769 := bstep (se 2 (by rfl) ⟨1397538, by rfl⟩ : syracuseStep 3726769 = 2795077) B2795077
theorem B1465843 : Blo 868566 1465843 := bstep (se 1 (by rfl) ⟨1099382, by rfl⟩ : syracuseStep 1465843 = 2198765) B2198765
theorem B2350595 : Blo 868566 2350595 := bstep (se 1 (by rfl) ⟨1762946, by rfl⟩ : syracuseStep 2350595 = 3525893) B3525893
theorem B2940461 : Blo 868566 2940461 := bstep (se 3 (by rfl) ⟨551336, by rfl⟩ : syracuseStep 2940461 = 1102673) B1102673
theorem B2940515 : Blo 868566 2940515 := bstep (se 1 (by rfl) ⟨2205386, by rfl⟩ : syracuseStep 2940515 = 4410773) B4410773
theorem B4185713 : Blo 868566 4185713 := bstep (se 2 (by rfl) ⟨1569642, by rfl⟩ : syracuseStep 4185713 = 3139285) B3139285
theorem B1465985 : Blo 868566 1465985 := bstep (se 2 (by rfl) ⟨549744, by rfl⟩ : syracuseStep 1465985 = 1099489) B1099489
theorem B1957553 : Blo 868566 1957553 := bstep (se 2 (by rfl) ⟨734082, by rfl⟩ : syracuseStep 1957553 = 1468165) B1468165
theorem B1957571 : Blo 868566 1957571 := bstep (se 1 (by rfl) ⟨1468178, by rfl⟩ : syracuseStep 1957571 = 2936357) B2936357
theorem B1466113 : Blo 868566 1466113 := bstep (se 2 (by rfl) ⟨549792, by rfl⟩ : syracuseStep 1466113 = 1099585) B1099585
theorem B1466147 : Blo 868566 1466147 := bstep (se 1 (by rfl) ⟨1099610, by rfl⟩ : syracuseStep 1466147 = 2199221) B2199221
theorem B1859395 : Blo 868566 1859395 := bstep (se 1 (by rfl) ⟨1394546, by rfl⟩ : syracuseStep 1859395 = 2789093) B2789093
theorem B4415309 : Blo 868566 4415309 := bstep (se 3 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 4415309 = 1655741) B1655741
theorem B1236817 : Blo 868566 1236817 := bstep (se 2 (by rfl) ⟨463806, by rfl⟩ : syracuseStep 1236817 = 927613) B927613
theorem B2940785 : Blo 868566 2940785 := bstep (se 2 (by rfl) ⟨1102794, by rfl⟩ : syracuseStep 2940785 = 2205589) B2205589
theorem B1466275 : Blo 868566 1466275 := bstep (se 1 (by rfl) ⟨1099706, by rfl⟩ : syracuseStep 1466275 = 2199413) B2199413
theorem B1957841 : Blo 868566 1957841 := bstep (se 2 (by rfl) ⟨734190, by rfl⟩ : syracuseStep 1957841 = 1468381) B1468381
theorem B1957859 : Blo 868566 1957859 := bstep (se 1 (by rfl) ⟨1468394, by rfl⟩ : syracuseStep 1957859 = 2936789) B2936789
theorem B7430129 : Blo 868566 7430129 := bstep (se 2 (by rfl) ⟨2786298, by rfl⟩ : syracuseStep 7430129 = 5572597) B5572597
theorem B1466417 : Blo 868566 1466417 := bstep (se 2 (by rfl) ⟨549906, by rfl⟩ : syracuseStep 1466417 = 1099813) B1099813
theorem B6611057 : Blo 868566 6611057 := bstep (se 2 (by rfl) ⟨2479146, by rfl⟩ : syracuseStep 6611057 = 4958293) B4958293
theorem B1466545 : Blo 868566 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B1466579 : Blo 868566 1466579 := bstep (se 1 (by rfl) ⟨1099934, by rfl⟩ : syracuseStep 1466579 = 2199869) B2199869
theorem B1958129 : Blo 868566 1958129 := bstep (se 2 (by rfl) ⟨734298, by rfl⟩ : syracuseStep 1958129 = 1468597) B1468597
theorem B1958147 : Blo 868566 1958147 := bstep (se 1 (by rfl) ⟨1468610, by rfl⟩ : syracuseStep 1958147 = 2937221) B2937221
theorem B11133197 : Blo 868566 11133197 := bstep (se 3 (by rfl) ⟨2087474, by rfl⟩ : syracuseStep 11133197 = 4174949) B4174949
theorem B2122001 : Blo 868566 2122001 := bstep (se 2 (by rfl) ⟨795750, by rfl⟩ : syracuseStep 2122001 = 1591501) B1591501
theorem B1302851 : Blo 868566 1302851 := bstep (se 1 (by rfl) ⟨977138, by rfl⟩ : syracuseStep 1302851 = 1954277) B1954277
theorem B1466707 : Blo 868566 1466707 := bstep (se 1 (by rfl) ⟨1100030, by rfl⟩ : syracuseStep 1466707 = 2200061) B2200061
theorem B1302881 : Blo 868566 1302881 := bstep (se 2 (by rfl) ⟨488580, by rfl⟩ : syracuseStep 1302881 = 977161) B977161
theorem B7954787 : Blo 868566 7954787 := bstep (se 1 (by rfl) ⟨5966090, by rfl⟩ : syracuseStep 7954787 = 11932181) B11932181
theorem B1302899 : Blo 868566 1302899 := bstep (se 1 (by rfl) ⟨977174, by rfl⟩ : syracuseStep 1302899 = 1954349) B1954349
theorem B2941325 : Blo 868566 2941325 := bstep (se 3 (by rfl) ⟨551498, by rfl⟩ : syracuseStep 2941325 = 1102997) B1102997
theorem B1302929 : Blo 868566 1302929 := bstep (se 2 (by rfl) ⟨488598, by rfl⟩ : syracuseStep 1302929 = 977197) B977197
theorem B1302947 : Blo 868566 1302947 := bstep (se 1 (by rfl) ⟨977210, by rfl⟩ : syracuseStep 1302947 = 1954421) B1954421
theorem B1302977 : Blo 868566 1302977 := bstep (se 2 (by rfl) ⟨488616, by rfl⟩ : syracuseStep 1302977 = 977233) B977233
theorem B2941379 : Blo 868566 2941379 := bstep (se 1 (by rfl) ⟨2206034, by rfl⟩ : syracuseStep 2941379 = 4412069) B4412069
theorem B1302995 : Blo 868566 1302995 := bstep (se 1 (by rfl) ⟨977246, by rfl⟩ : syracuseStep 1302995 = 1954493) B1954493
theorem B1466849 : Blo 868566 1466849 := bstep (se 2 (by rfl) ⟨550068, by rfl⟩ : syracuseStep 1466849 = 1100137) B1100137
theorem B1303025 : Blo 868566 1303025 := bstep (se 2 (by rfl) ⟨488634, by rfl⟩ : syracuseStep 1303025 = 977269) B977269
theorem B1303043 : Blo 868566 1303043 := bstep (se 1 (by rfl) ⟨977282, by rfl⟩ : syracuseStep 1303043 = 1954565) B1954565
theorem B4186637 : Blo 868566 4186637 := bstep (se 3 (by rfl) ⟨784994, by rfl⟩ : syracuseStep 4186637 = 1569989) B1569989
theorem B1958417 : Blo 868566 1958417 := bstep (se 2 (by rfl) ⟨734406, by rfl⟩ : syracuseStep 1958417 = 1468813) B1468813
theorem B1237523 : Blo 868566 1237523 := bstep (se 1 (by rfl) ⟨928142, by rfl⟩ : syracuseStep 1237523 = 1856285) B1856285
theorem B1303073 : Blo 868566 1303073 := bstep (se 2 (by rfl) ⟨488652, by rfl⟩ : syracuseStep 1303073 = 977305) B977305
theorem B1958435 : Blo 868566 1958435 := bstep (se 1 (by rfl) ⟨1468826, by rfl⟩ : syracuseStep 1958435 = 2937653) B2937653
theorem B1303091 : Blo 868566 1303091 := bstep (se 1 (by rfl) ⟨977318, by rfl⟩ : syracuseStep 1303091 = 1954637) B1954637
theorem B1303121 : Blo 868566 1303121 := bstep (se 2 (by rfl) ⟨488670, by rfl⟩ : syracuseStep 1303121 = 977341) B977341
theorem B1466977 : Blo 868566 1466977 := bstep (se 2 (by rfl) ⟨550116, by rfl⟩ : syracuseStep 1466977 = 1100233) B1100233
theorem B1303139 : Blo 868566 1303139 := bstep (se 1 (by rfl) ⟨977354, by rfl⟩ : syracuseStep 1303139 = 1954709) B1954709
theorem B1303169 : Blo 868566 1303169 := bstep (se 2 (by rfl) ⟨488688, by rfl⟩ : syracuseStep 1303169 = 977377) B977377
theorem B1467011 : Blo 868566 1467011 := bstep (se 1 (by rfl) ⟨1100258, by rfl⟩ : syracuseStep 1467011 = 2200517) B2200517
theorem B1860241 : Blo 868566 1860241 := bstep (se 2 (by rfl) ⟨697590, by rfl⟩ : syracuseStep 1860241 = 1395181) B1395181
theorem B1303187 : Blo 868566 1303187 := bstep (se 1 (by rfl) ⟨977390, by rfl⟩ : syracuseStep 1303187 = 1954781) B1954781
theorem B1303217 : Blo 868566 1303217 := bstep (se 2 (by rfl) ⟨488706, by rfl⟩ : syracuseStep 1303217 = 977413) B977413
theorem B1303235 : Blo 868566 1303235 := bstep (se 1 (by rfl) ⟨977426, by rfl⟩ : syracuseStep 1303235 = 1954853) B1954853
theorem B2482883 : Blo 868566 2482883 := bstep (se 1 (by rfl) ⟨1862162, by rfl⟩ : syracuseStep 2482883 = 3724325) B3724325
theorem B4186829 : Blo 868566 4186829 := bstep (se 3 (by rfl) ⟨785030, by rfl⟩ : syracuseStep 4186829 = 1570061) B1570061
theorem B2941649 : Blo 868566 2941649 := bstep (se 2 (by rfl) ⟨1103118, by rfl⟩ : syracuseStep 2941649 = 2206237) B2206237
theorem B1303265 : Blo 868566 1303265 := bstep (se 2 (by rfl) ⟨488724, by rfl⟩ : syracuseStep 1303265 = 977449) B977449
theorem B1303283 : Blo 868566 1303283 := bstep (se 1 (by rfl) ⟨977462, by rfl⟩ : syracuseStep 1303283 = 1954925) B1954925
theorem B1467139 : Blo 868566 1467139 := bstep (se 1 (by rfl) ⟨1100354, by rfl⟩ : syracuseStep 1467139 = 2200709) B2200709
theorem B1303313 : Blo 868566 1303313 := bstep (se 2 (by rfl) ⟨488742, by rfl⟩ : syracuseStep 1303313 = 977485) B977485
theorem B1303331 : Blo 868566 1303331 := bstep (se 1 (by rfl) ⟨977498, by rfl⟩ : syracuseStep 1303331 = 1954997) B1954997
theorem B1958705 : Blo 868566 1958705 := bstep (se 2 (by rfl) ⟨734514, by rfl⟩ : syracuseStep 1958705 = 1469029) B1469029
theorem B1303361 : Blo 868566 1303361 := bstep (se 2 (by rfl) ⟨488760, by rfl⟩ : syracuseStep 1303361 = 977521) B977521
theorem B1958723 : Blo 868566 1958723 := bstep (se 1 (by rfl) ⟨1469042, by rfl⟩ : syracuseStep 1958723 = 2938085) B2938085
theorem B1303379 : Blo 868566 1303379 := bstep (se 1 (by rfl) ⟨977534, by rfl⟩ : syracuseStep 1303379 = 1955069) B1955069
theorem B1303409 : Blo 868566 1303409 := bstep (se 2 (by rfl) ⟨488778, by rfl⟩ : syracuseStep 1303409 = 977557) B977557
theorem B1303427 : Blo 868566 1303427 := bstep (se 1 (by rfl) ⟨977570, by rfl⟩ : syracuseStep 1303427 = 1955141) B1955141
theorem B1467281 : Blo 868566 1467281 := bstep (se 2 (by rfl) ⟨550230, by rfl⟩ : syracuseStep 1467281 = 1100461) B1100461
theorem B1303457 : Blo 868566 1303457 := bstep (se 2 (by rfl) ⟨488796, by rfl⟩ : syracuseStep 1303457 = 977593) B977593
theorem B1303475 : Blo 868566 1303475 := bstep (se 1 (by rfl) ⟨977606, by rfl⟩ : syracuseStep 1303475 = 1955213) B1955213
theorem B1303505 : Blo 868566 1303505 := bstep (se 2 (by rfl) ⟨488814, by rfl⟩ : syracuseStep 1303505 = 977629) B977629
theorem B1303523 : Blo 868566 1303523 := bstep (se 1 (by rfl) ⟨977642, by rfl⟩ : syracuseStep 1303523 = 1955285) B1955285
theorem B1303553 : Blo 868566 1303553 := bstep (se 2 (by rfl) ⟨488832, by rfl⟩ : syracuseStep 1303553 = 977665) B977665
theorem B1467409 : Blo 868566 1467409 := bstep (se 2 (by rfl) ⟨550278, by rfl⟩ : syracuseStep 1467409 = 1100557) B1100557
theorem B1303571 : Blo 868566 1303571 := bstep (se 1 (by rfl) ⟨977678, by rfl⟩ : syracuseStep 1303571 = 1955357) B1955357
theorem B1303601 : Blo 868566 1303601 := bstep (se 2 (by rfl) ⟨488850, by rfl⟩ : syracuseStep 1303601 = 977701) B977701
theorem B2090033 : Blo 868566 2090033 := bstep (se 2 (by rfl) ⟨783762, by rfl⟩ : syracuseStep 2090033 = 1567525) B1567525
theorem B1467443 : Blo 868566 1467443 := bstep (se 1 (by rfl) ⟨1100582, by rfl⟩ : syracuseStep 1467443 = 2201165) B2201165
theorem B1303619 : Blo 868566 1303619 := bstep (se 1 (by rfl) ⟨977714, by rfl⟩ : syracuseStep 1303619 = 1955429) B1955429
theorem B2090051 : Blo 868566 2090051 := bstep (se 1 (by rfl) ⟨1567538, by rfl⟩ : syracuseStep 2090051 = 3135077) B3135077
theorem B3302477 : Blo 868566 3302477 := bstep (se 3 (by rfl) ⟨619214, by rfl⟩ : syracuseStep 3302477 = 1238429) B1238429
theorem B1958993 : Blo 868566 1958993 := bstep (se 2 (by rfl) ⟨734622, by rfl⟩ : syracuseStep 1958993 = 1469245) B1469245
theorem B1303649 : Blo 868566 1303649 := bstep (se 2 (by rfl) ⟨488868, by rfl⟩ : syracuseStep 1303649 = 977737) B977737
theorem B1959011 : Blo 868566 1959011 := bstep (se 1 (by rfl) ⟨1469258, by rfl⟩ : syracuseStep 1959011 = 2938517) B2938517
theorem B1303667 : Blo 868566 1303667 := bstep (se 1 (by rfl) ⟨977750, by rfl⟩ : syracuseStep 1303667 = 1955501) B1955501
theorem B1303697 : Blo 868566 1303697 := bstep (se 2 (by rfl) ⟨488886, by rfl⟩ : syracuseStep 1303697 = 977773) B977773
theorem B1238161 : Blo 868566 1238161 := bstep (se 2 (by rfl) ⟨464310, by rfl⟩ : syracuseStep 1238161 = 928621) B928621
theorem B1303715 : Blo 868566 1303715 := bstep (se 1 (by rfl) ⟨977786, by rfl⟩ : syracuseStep 1303715 = 1955573) B1955573
theorem B1467571 : Blo 868566 1467571 := bstep (se 1 (by rfl) ⟨1100678, by rfl⟩ : syracuseStep 1467571 = 2201357) B2201357
theorem B1303745 : Blo 868566 1303745 := bstep (se 2 (by rfl) ⟨488904, by rfl⟩ : syracuseStep 1303745 = 977809) B977809
theorem B1303763 : Blo 868566 1303763 := bstep (se 1 (by rfl) ⟨977822, by rfl⟩ : syracuseStep 1303763 = 1955645) B1955645
theorem B2516195 : Blo 868566 2516195 := bstep (se 1 (by rfl) ⟨1887146, by rfl⟩ : syracuseStep 2516195 = 3774293) B3774293
theorem B2942189 : Blo 868566 2942189 := bstep (se 3 (by rfl) ⟨551660, by rfl⟩ : syracuseStep 2942189 = 1103321) B1103321
theorem B1303793 : Blo 868566 1303793 := bstep (se 2 (by rfl) ⟨488922, by rfl⟩ : syracuseStep 1303793 = 977845) B977845
theorem B1303811 : Blo 868566 1303811 := bstep (se 1 (by rfl) ⟨977858, by rfl⟩ : syracuseStep 1303811 = 1955717) B1955717
theorem B1238275 : Blo 868566 1238275 := bstep (se 1 (by rfl) ⟨928706, by rfl⟩ : syracuseStep 1238275 = 1857413) B1857413
theorem B1303841 : Blo 868566 1303841 := bstep (se 2 (by rfl) ⟨488940, by rfl⟩ : syracuseStep 1303841 = 977881) B977881
theorem B2942243 : Blo 868566 2942243 := bstep (se 1 (by rfl) ⟨2206682, by rfl⟩ : syracuseStep 2942243 = 4413365) B4413365
theorem B1303859 : Blo 868566 1303859 := bstep (se 1 (by rfl) ⟨977894, by rfl⟩ : syracuseStep 1303859 = 1955789) B1955789
theorem B1467713 : Blo 868566 1467713 := bstep (se 2 (by rfl) ⟨550392, by rfl⟩ : syracuseStep 1467713 = 1100785) B1100785
theorem B1303889 : Blo 868566 1303889 := bstep (se 2 (by rfl) ⟨488958, by rfl⟩ : syracuseStep 1303889 = 977917) B977917
theorem B1303907 : Blo 868566 1303907 := bstep (se 1 (by rfl) ⟨977930, by rfl⟩ : syracuseStep 1303907 = 1955861) B1955861
theorem B1959281 : Blo 868566 1959281 := bstep (se 2 (by rfl) ⟨734730, by rfl⟩ : syracuseStep 1959281 = 1469461) B1469461
theorem B1303937 : Blo 868566 1303937 := bstep (se 2 (by rfl) ⟨488976, by rfl⟩ : syracuseStep 1303937 = 977953) B977953
theorem B1959299 : Blo 868566 1959299 := bstep (se 1 (by rfl) ⟨1469474, by rfl⟩ : syracuseStep 1959299 = 2938949) B2938949
theorem B1303955 : Blo 868566 1303955 := bstep (se 1 (by rfl) ⟨977966, by rfl⟩ : syracuseStep 1303955 = 1955933) B1955933
theorem B1303985 : Blo 868566 1303985 := bstep (se 2 (by rfl) ⟨488994, by rfl⟩ : syracuseStep 1303985 = 977989) B977989
theorem B1467841 : Blo 868566 1467841 := bstep (se 2 (by rfl) ⟨550440, by rfl⟩ : syracuseStep 1467841 = 1100881) B1100881
theorem B1304003 : Blo 868566 1304003 := bstep (se 1 (by rfl) ⟨978002, by rfl⟩ : syracuseStep 1304003 = 1956005) B1956005
theorem B1304033 : Blo 868566 1304033 := bstep (se 2 (by rfl) ⟨489012, by rfl⟩ : syracuseStep 1304033 = 978025) B978025
theorem B1467875 : Blo 868566 1467875 := bstep (se 1 (by rfl) ⟨1100906, by rfl⟩ : syracuseStep 1467875 = 2201813) B2201813
theorem B2483693 : Blo 868566 2483693 := bstep (se 3 (by rfl) ⟨465692, by rfl⟩ : syracuseStep 2483693 = 931385) B931385
theorem B1304051 : Blo 868566 1304051 := bstep (se 1 (by rfl) ⟨978038, by rfl⟩ : syracuseStep 1304051 = 1956077) B1956077
theorem B1304081 : Blo 868566 1304081 := bstep (se 2 (by rfl) ⟨489030, by rfl⟩ : syracuseStep 1304081 = 978061) B978061
theorem B1304099 : Blo 868566 1304099 := bstep (se 1 (by rfl) ⟨978074, by rfl⟩ : syracuseStep 1304099 = 1956149) B1956149
theorem B2942513 : Blo 868566 2942513 := bstep (se 2 (by rfl) ⟨1103442, by rfl⟩ : syracuseStep 2942513 = 2206885) B2206885
theorem B1304129 : Blo 868566 1304129 := bstep (se 2 (by rfl) ⟨489048, by rfl⟩ : syracuseStep 1304129 = 978097) B978097
theorem B1304147 : Blo 868566 1304147 := bstep (se 1 (by rfl) ⟨978110, by rfl⟩ : syracuseStep 1304147 = 1956221) B1956221
theorem B1468003 : Blo 868566 1468003 := bstep (se 1 (by rfl) ⟨1101002, by rfl⟩ : syracuseStep 1468003 = 2202005) B2202005
theorem B1304177 : Blo 868566 1304177 := bstep (se 2 (by rfl) ⟨489066, by rfl⟩ : syracuseStep 1304177 = 978133) B978133
theorem B1304195 : Blo 868566 1304195 := bstep (se 1 (by rfl) ⟨978146, by rfl⟩ : syracuseStep 1304195 = 1956293) B1956293
theorem B2385539 : Blo 868566 2385539 := bstep (se 1 (by rfl) ⟨1789154, by rfl⟩ : syracuseStep 2385539 = 3578309) B3578309
theorem B1959569 : Blo 868566 1959569 := bstep (se 2 (by rfl) ⟨734838, by rfl⟩ : syracuseStep 1959569 = 1469677) B1469677
theorem B1304225 : Blo 868566 1304225 := bstep (se 2 (by rfl) ⟨489084, by rfl⟩ : syracuseStep 1304225 = 978169) B978169
theorem B1959587 : Blo 868566 1959587 := bstep (se 1 (by rfl) ⟨1469690, by rfl⟩ : syracuseStep 1959587 = 2939381) B2939381
theorem B2483885 : Blo 868566 2483885 := bstep (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) B931457
theorem B1304243 : Blo 868566 1304243 := bstep (se 1 (by rfl) ⟨978182, by rfl⟩ : syracuseStep 1304243 = 1956365) B1956365
theorem B1304273 : Blo 868566 1304273 := bstep (se 2 (by rfl) ⟨489102, by rfl⟩ : syracuseStep 1304273 = 978205) B978205
theorem B1304291 : Blo 868566 1304291 := bstep (se 1 (by rfl) ⟨978218, by rfl⟩ : syracuseStep 1304291 = 1956437) B1956437
theorem B1468145 : Blo 868566 1468145 := bstep (se 2 (by rfl) ⟨550554, by rfl⟩ : syracuseStep 1468145 = 1101109) B1101109
theorem B1304321 : Blo 868566 1304321 := bstep (se 2 (by rfl) ⟨489120, by rfl⟩ : syracuseStep 1304321 = 978241) B978241
theorem B2975491 : Blo 868566 2975491 := bstep (se 1 (by rfl) ⟨2231618, by rfl⟩ : syracuseStep 2975491 = 4463237) B4463237
theorem B1304339 : Blo 868566 1304339 := bstep (se 1 (by rfl) ⟨978254, by rfl⟩ : syracuseStep 1304339 = 1956509) B1956509
theorem B1304369 : Blo 868566 1304369 := bstep (se 2 (by rfl) ⟨489138, by rfl⟩ : syracuseStep 1304369 = 978277) B978277
theorem B1304387 : Blo 868566 1304387 := bstep (se 1 (by rfl) ⟨978290, by rfl⟩ : syracuseStep 1304387 = 1956581) B1956581
theorem B1304417 : Blo 868566 1304417 := bstep (se 2 (by rfl) ⟨489156, by rfl⟩ : syracuseStep 1304417 = 978313) B978313
theorem B3303281 : Blo 868566 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B1468273 : Blo 868566 1468273 := bstep (se 2 (by rfl) ⟨550602, by rfl⟩ : syracuseStep 1468273 = 1101205) B1101205
theorem B1304435 : Blo 868566 1304435 := bstep (se 1 (by rfl) ⟨978326, by rfl⟩ : syracuseStep 1304435 = 1956653) B1956653
theorem B1304465 : Blo 868566 1304465 := bstep (se 2 (by rfl) ⟨489174, by rfl⟩ : syracuseStep 1304465 = 978349) B978349
theorem B1468307 : Blo 868566 1468307 := bstep (se 1 (by rfl) ⟨1101230, by rfl⟩ : syracuseStep 1468307 = 2202461) B2202461
theorem B1304483 : Blo 868566 1304483 := bstep (se 1 (by rfl) ⟨978362, by rfl⟩ : syracuseStep 1304483 = 1956725) B1956725
theorem B1959857 : Blo 868566 1959857 := bstep (se 2 (by rfl) ⟨734946, by rfl⟩ : syracuseStep 1959857 = 1469893) B1469893
theorem B1304513 : Blo 868566 1304513 := bstep (se 2 (by rfl) ⟨489192, by rfl⟩ : syracuseStep 1304513 = 978385) B978385
theorem B1959875 : Blo 868566 1959875 := bstep (se 1 (by rfl) ⟨1469906, by rfl⟩ : syracuseStep 1959875 = 2939813) B2939813
theorem B1304531 : Blo 868566 1304531 := bstep (se 1 (by rfl) ⟨978398, by rfl⟩ : syracuseStep 1304531 = 1956797) B1956797
theorem B1304561 : Blo 868566 1304561 := bstep (se 2 (by rfl) ⟨489210, by rfl⟩ : syracuseStep 1304561 = 978421) B978421
theorem B1304579 : Blo 868566 1304579 := bstep (se 1 (by rfl) ⟨978434, by rfl⟩ : syracuseStep 1304579 = 1956869) B1956869
theorem B1468435 : Blo 868566 1468435 := bstep (se 1 (by rfl) ⟨1101326, by rfl⟩ : syracuseStep 1468435 = 2202653) B2202653
theorem B1304609 : Blo 868566 1304609 := bstep (se 2 (by rfl) ⟨489228, by rfl⟩ : syracuseStep 1304609 = 978457) B978457
theorem B1304627 : Blo 868566 1304627 := bstep (se 1 (by rfl) ⟨978470, by rfl⟩ : syracuseStep 1304627 = 1956941) B1956941
theorem B3139661 : Blo 868566 3139661 := bstep (se 3 (by rfl) ⟨588686, by rfl⟩ : syracuseStep 3139661 = 1177373) B1177373
theorem B2943053 : Blo 868566 2943053 := bstep (se 3 (by rfl) ⟨551822, by rfl⟩ : syracuseStep 2943053 = 1103645) B1103645
theorem B1304657 : Blo 868566 1304657 := bstep (se 2 (by rfl) ⟨489246, by rfl⟩ : syracuseStep 1304657 = 978493) B978493
theorem B2091089 : Blo 868566 2091089 := bstep (se 2 (by rfl) ⟨784158, by rfl⟩ : syracuseStep 2091089 = 1568317) B1568317
theorem B1304675 : Blo 868566 1304675 := bstep (se 1 (by rfl) ⟨978506, by rfl⟩ : syracuseStep 1304675 = 1957013) B1957013
theorem B1304705 : Blo 868566 1304705 := bstep (se 2 (by rfl) ⟨489264, by rfl⟩ : syracuseStep 1304705 = 978529) B978529
theorem B2943107 : Blo 868566 2943107 := bstep (se 1 (by rfl) ⟨2207330, by rfl⟩ : syracuseStep 2943107 = 4414661) B4414661
theorem B1304723 : Blo 868566 1304723 := bstep (se 1 (by rfl) ⟨978542, by rfl⟩ : syracuseStep 1304723 = 1957085) B1957085
theorem B1468577 : Blo 868566 1468577 := bstep (se 2 (by rfl) ⟨550716, by rfl⟩ : syracuseStep 1468577 = 1101433) B1101433
theorem B1304753 : Blo 868566 1304753 := bstep (se 2 (by rfl) ⟨489282, by rfl⟩ : syracuseStep 1304753 = 978565) B978565
theorem B1304771 : Blo 868566 1304771 := bstep (se 1 (by rfl) ⟨978578, by rfl⟩ : syracuseStep 1304771 = 1957157) B1957157
theorem B1960145 : Blo 868566 1960145 := bstep (se 2 (by rfl) ⟨735054, by rfl⟩ : syracuseStep 1960145 = 1470109) B1470109
theorem B1304801 : Blo 868566 1304801 := bstep (se 2 (by rfl) ⟨489300, by rfl⟩ : syracuseStep 1304801 = 978601) B978601
theorem B1960163 : Blo 868566 1960163 := bstep (se 1 (by rfl) ⟨1470122, by rfl⟩ : syracuseStep 1960163 = 2940245) B2940245
theorem B1304819 : Blo 868566 1304819 := bstep (se 1 (by rfl) ⟨978614, by rfl⟩ : syracuseStep 1304819 = 1957229) B1957229
theorem B1304849 : Blo 868566 1304849 := bstep (se 2 (by rfl) ⟨489318, by rfl⟩ : syracuseStep 1304849 = 978637) B978637
theorem B1468705 : Blo 868566 1468705 := bstep (se 2 (by rfl) ⟨550764, by rfl⟩ : syracuseStep 1468705 = 1101529) B1101529
theorem B1304867 : Blo 868566 1304867 := bstep (se 1 (by rfl) ⟨978650, by rfl⟩ : syracuseStep 1304867 = 1957301) B1957301
theorem B1304897 : Blo 868566 1304897 := bstep (se 2 (by rfl) ⟨489336, by rfl⟩ : syracuseStep 1304897 = 978673) B978673
theorem B1468739 : Blo 868566 1468739 := bstep (se 1 (by rfl) ⟨1101554, by rfl⟩ : syracuseStep 1468739 = 2203109) B2203109
theorem B1304915 : Blo 868566 1304915 := bstep (se 1 (by rfl) ⟨978686, by rfl⟩ : syracuseStep 1304915 = 1957373) B1957373
theorem B977251 : Blo 868566 977251 := bstep (se 1 (by rfl) ⟨732938, by rfl⟩ : syracuseStep 977251 = 1465877) B1465877
theorem B1304945 : Blo 868566 1304945 := bstep (se 2 (by rfl) ⟨489354, by rfl⟩ : syracuseStep 1304945 = 978709) B978709
theorem B1304963 : Blo 868566 1304963 := bstep (se 1 (by rfl) ⟨978722, by rfl⟩ : syracuseStep 1304963 = 1957445) B1957445
theorem B2943377 : Blo 868566 2943377 := bstep (se 2 (by rfl) ⟨1103766, by rfl⟩ : syracuseStep 2943377 = 2207533) B2207533
theorem B1304993 : Blo 868566 1304993 := bstep (se 2 (by rfl) ⟨489372, by rfl⟩ : syracuseStep 1304993 = 978745) B978745
theorem B1305011 : Blo 868566 1305011 := bstep (se 1 (by rfl) ⟨978758, by rfl⟩ : syracuseStep 1305011 = 1957517) B1957517
theorem B1468867 : Blo 868566 1468867 := bstep (se 1 (by rfl) ⟨1101650, by rfl⟩ : syracuseStep 1468867 = 2203301) B2203301
theorem B1305041 : Blo 868566 1305041 := bstep (se 2 (by rfl) ⟨489390, by rfl⟩ : syracuseStep 1305041 = 978781) B978781
theorem B1305059 : Blo 868566 1305059 := bstep (se 1 (by rfl) ⟨978794, by rfl⟩ : syracuseStep 1305059 = 1957589) B1957589
theorem B1960433 : Blo 868566 1960433 := bstep (se 2 (by rfl) ⟨735162, by rfl⟩ : syracuseStep 1960433 = 1470325) B1470325
theorem B3631601 : Blo 868566 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B977395 : Blo 868566 977395 := bstep (se 1 (by rfl) ⟨733046, by rfl⟩ : syracuseStep 977395 = 1466093) B1466093
theorem B1862129 : Blo 868566 1862129 := bstep (se 2 (by rfl) ⟨698298, by rfl⟩ : syracuseStep 1862129 = 1396597) B1396597
theorem B1305089 : Blo 868566 1305089 := bstep (se 2 (by rfl) ⟨489408, by rfl⟩ : syracuseStep 1305089 = 978817) B978817
theorem B1960451 : Blo 868566 1960451 := bstep (se 1 (by rfl) ⟨1470338, by rfl⟩ : syracuseStep 1960451 = 2940677) B2940677
theorem B3303949 : Blo 868566 3303949 := bstep (se 3 (by rfl) ⟨619490, by rfl⟩ : syracuseStep 3303949 = 1238981) B1238981
theorem B1305107 : Blo 868566 1305107 := bstep (se 1 (by rfl) ⟨978830, by rfl⟩ : syracuseStep 1305107 = 1957661) B1957661
theorem B1305137 : Blo 868566 1305137 := bstep (se 2 (by rfl) ⟨489426, by rfl⟩ : syracuseStep 1305137 = 978853) B978853
theorem B1305155 : Blo 868566 1305155 := bstep (se 1 (by rfl) ⟨978866, by rfl⟩ : syracuseStep 1305155 = 1957733) B1957733
theorem B1239619 : Blo 868566 1239619 := bstep (se 1 (by rfl) ⟨929714, by rfl⟩ : syracuseStep 1239619 = 1859429) B1859429
theorem B1469009 : Blo 868566 1469009 := bstep (se 2 (by rfl) ⟨550878, by rfl⟩ : syracuseStep 1469009 = 1101757) B1101757
theorem B1305185 : Blo 868566 1305185 := bstep (se 2 (by rfl) ⟨489444, by rfl⟩ : syracuseStep 1305185 = 978889) B978889
theorem B1305203 : Blo 868566 1305203 := bstep (se 1 (by rfl) ⟨978902, by rfl⟩ : syracuseStep 1305203 = 1957805) B1957805
theorem B977539 : Blo 868566 977539 := bstep (se 1 (by rfl) ⟨733154, by rfl⟩ : syracuseStep 977539 = 1466309) B1466309
theorem B1305233 : Blo 868566 1305233 := bstep (se 2 (by rfl) ⟨489462, by rfl⟩ : syracuseStep 1305233 = 978925) B978925
theorem B1305251 : Blo 868566 1305251 := bstep (se 1 (by rfl) ⟨978938, by rfl⟩ : syracuseStep 1305251 = 1957877) B1957877
theorem B1305281 : Blo 868566 1305281 := bstep (se 2 (by rfl) ⟨489480, by rfl⟩ : syracuseStep 1305281 = 978961) B978961
theorem B1469137 : Blo 868566 1469137 := bstep (se 2 (by rfl) ⟨550926, by rfl⟩ : syracuseStep 1469137 = 1101853) B1101853
theorem B1305299 : Blo 868566 1305299 := bstep (se 1 (by rfl) ⟨978974, by rfl⟩ : syracuseStep 1305299 = 1957949) B1957949
theorem B1305329 : Blo 868566 1305329 := bstep (se 2 (by rfl) ⟨489498, by rfl⟩ : syracuseStep 1305329 = 978997) B978997
theorem B1469171 : Blo 868566 1469171 := bstep (se 1 (by rfl) ⟨1101878, by rfl⟩ : syracuseStep 1469171 = 2203757) B2203757
theorem B1305347 : Blo 868566 1305347 := bstep (se 1 (by rfl) ⟨979010, by rfl⟩ : syracuseStep 1305347 = 1958021) B1958021
theorem B1960721 : Blo 868566 1960721 := bstep (se 2 (by rfl) ⟨735270, by rfl⟩ : syracuseStep 1960721 = 1470541) B1470541
theorem B977683 : Blo 868566 977683 := bstep (se 1 (by rfl) ⟨733262, by rfl⟩ : syracuseStep 977683 = 1466525) B1466525
theorem B1305377 : Blo 868566 1305377 := bstep (se 2 (by rfl) ⟨489516, by rfl⟩ : syracuseStep 1305377 = 979033) B979033
theorem B1960739 : Blo 868566 1960739 := bstep (se 1 (by rfl) ⟨1470554, by rfl⟩ : syracuseStep 1960739 = 2941109) B2941109
theorem B1305395 : Blo 868566 1305395 := bstep (se 1 (by rfl) ⟨979046, by rfl⟩ : syracuseStep 1305395 = 1958093) B1958093
theorem B1305425 : Blo 868566 1305425 := bstep (se 2 (by rfl) ⟨489534, by rfl⟩ : syracuseStep 1305425 = 979069) B979069
theorem B1305443 : Blo 868566 1305443 := bstep (se 1 (by rfl) ⟨979082, by rfl⟩ : syracuseStep 1305443 = 1958165) B1958165
theorem B1469299 : Blo 868566 1469299 := bstep (se 1 (by rfl) ⟨1101974, by rfl⟩ : syracuseStep 1469299 = 2203949) B2203949
theorem B1305473 : Blo 868566 1305473 := bstep (se 2 (by rfl) ⟨489552, by rfl⟩ : syracuseStep 1305473 = 979105) B979105
theorem B1305491 : Blo 868566 1305491 := bstep (se 1 (by rfl) ⟨979118, by rfl⟩ : syracuseStep 1305491 = 1958237) B1958237
theorem B5565347 : Blo 868566 5565347 := bstep (se 1 (by rfl) ⟨4174010, by rfl⟩ : syracuseStep 5565347 = 8348021) B8348021
theorem B977827 : Blo 868566 977827 := bstep (se 1 (by rfl) ⟨733370, by rfl⟩ : syracuseStep 977827 = 1466741) B1466741
theorem B2943917 : Blo 868566 2943917 := bstep (se 3 (by rfl) ⟨551984, by rfl⟩ : syracuseStep 2943917 = 1103969) B1103969
theorem B1305521 : Blo 868566 1305521 := bstep (se 2 (by rfl) ⟨489570, by rfl⟩ : syracuseStep 1305521 = 979141) B979141
theorem B1305539 : Blo 868566 1305539 := bstep (se 1 (by rfl) ⟨979154, by rfl⟩ : syracuseStep 1305539 = 1958309) B1958309
theorem B1305569 : Blo 868566 1305569 := bstep (se 2 (by rfl) ⟨489588, by rfl⟩ : syracuseStep 1305569 = 979177) B979177
theorem B2943971 : Blo 868566 2943971 := bstep (se 1 (by rfl) ⟨2207978, by rfl⟩ : syracuseStep 2943971 = 4415957) B4415957
theorem B1305587 : Blo 868566 1305587 := bstep (se 1 (by rfl) ⟨979190, by rfl⟩ : syracuseStep 1305587 = 1958381) B1958381
theorem B1469441 : Blo 868566 1469441 := bstep (se 2 (by rfl) ⟨551040, by rfl⟩ : syracuseStep 1469441 = 1102081) B1102081
theorem B10742797 : Blo 868566 10742797 := bstep (se 3 (by rfl) ⟨2014274, by rfl⟩ : syracuseStep 10742797 = 4028549) B4028549
theorem B1305617 : Blo 868566 1305617 := bstep (se 2 (by rfl) ⟨489606, by rfl⟩ : syracuseStep 1305617 = 979213) B979213
theorem B1305635 : Blo 868566 1305635 := bstep (se 1 (by rfl) ⟨979226, by rfl⟩ : syracuseStep 1305635 = 1958453) B1958453
theorem B1961009 : Blo 868566 1961009 := bstep (se 2 (by rfl) ⟨735378, by rfl⟩ : syracuseStep 1961009 = 1470757) B1470757
theorem B977971 : Blo 868566 977971 := bstep (se 1 (by rfl) ⟨733478, by rfl⟩ : syracuseStep 977971 = 1466957) B1466957
theorem B1305665 : Blo 868566 1305665 := bstep (se 2 (by rfl) ⟨489624, by rfl⟩ : syracuseStep 1305665 = 979249) B979249
theorem B1961027 : Blo 868566 1961027 := bstep (se 1 (by rfl) ⟨1470770, by rfl⟩ : syracuseStep 1961027 = 2941541) B2941541
theorem B1305683 : Blo 868566 1305683 := bstep (se 1 (by rfl) ⟨979262, by rfl⟩ : syracuseStep 1305683 = 1958525) B1958525
theorem B5958755 : Blo 868566 5958755 := bstep (se 1 (by rfl) ⟨4469066, by rfl⟩ : syracuseStep 5958755 = 8938133) B8938133
theorem B1305713 : Blo 868566 1305713 := bstep (se 2 (by rfl) ⟨489642, by rfl⟩ : syracuseStep 1305713 = 979285) B979285
theorem B1469569 : Blo 868566 1469569 := bstep (se 2 (by rfl) ⟨551088, by rfl⟩ : syracuseStep 1469569 = 1102177) B1102177
theorem B1305731 : Blo 868566 1305731 := bstep (se 1 (by rfl) ⟨979298, by rfl⟩ : syracuseStep 1305731 = 1958597) B1958597
theorem B1305761 : Blo 868566 1305761 := bstep (se 2 (by rfl) ⟨489660, by rfl⟩ : syracuseStep 1305761 = 979321) B979321
theorem B1469603 : Blo 868566 1469603 := bstep (se 1 (by rfl) ⟨1102202, by rfl⟩ : syracuseStep 1469603 = 2204405) B2204405
theorem B3140785 : Blo 868566 3140785 := bstep (se 2 (by rfl) ⟨1177794, by rfl⟩ : syracuseStep 3140785 = 2355589) B2355589
theorem B1305779 : Blo 868566 1305779 := bstep (se 1 (by rfl) ⟨979334, by rfl⟩ : syracuseStep 1305779 = 1958669) B1958669
theorem B978115 : Blo 868566 978115 := bstep (se 1 (by rfl) ⟨733586, by rfl⟩ : syracuseStep 978115 = 1467173) B1467173
theorem B1305809 : Blo 868566 1305809 := bstep (se 2 (by rfl) ⟨489678, by rfl⟩ : syracuseStep 1305809 = 979357) B979357
theorem B1305827 : Blo 868566 1305827 := bstep (se 1 (by rfl) ⟨979370, by rfl⟩ : syracuseStep 1305827 = 1958741) B1958741
theorem B2944241 : Blo 868566 2944241 := bstep (se 2 (by rfl) ⟨1104090, by rfl⟩ : syracuseStep 2944241 = 2208181) B2208181
theorem B1043699 : Blo 868566 1043699 := bstep (se 1 (by rfl) ⟨782774, by rfl⟩ : syracuseStep 1043699 = 1565549) B1565549
theorem B1305857 : Blo 868566 1305857 := bstep (se 2 (by rfl) ⟨489696, by rfl⟩ : syracuseStep 1305857 = 979393) B979393
theorem B1305875 : Blo 868566 1305875 := bstep (se 1 (by rfl) ⟨979406, by rfl⟩ : syracuseStep 1305875 = 1958813) B1958813
theorem B3304739 : Blo 868566 3304739 := bstep (se 1 (by rfl) ⟨2478554, by rfl⟩ : syracuseStep 3304739 = 4957109) B4957109
theorem B1469731 : Blo 868566 1469731 := bstep (se 1 (by rfl) ⟨1102298, by rfl⟩ : syracuseStep 1469731 = 2204597) B2204597
theorem B1305905 : Blo 868566 1305905 := bstep (se 2 (by rfl) ⟨489714, by rfl⟩ : syracuseStep 1305905 = 979429) B979429
theorem B1305923 : Blo 868566 1305923 := bstep (se 1 (by rfl) ⟨979442, by rfl⟩ : syracuseStep 1305923 = 1958885) B1958885
theorem B1961297 : Blo 868566 1961297 := bstep (se 2 (by rfl) ⟨735486, by rfl⟩ : syracuseStep 1961297 = 1470973) B1470973
theorem B978259 : Blo 868566 978259 := bstep (se 1 (by rfl) ⟨733694, by rfl⟩ : syracuseStep 978259 = 1467389) B1467389
theorem B1305953 : Blo 868566 1305953 := bstep (se 2 (by rfl) ⟨489732, by rfl⟩ : syracuseStep 1305953 = 979465) B979465
theorem B1961315 : Blo 868566 1961315 := bstep (se 1 (by rfl) ⟨1470986, by rfl⟩ : syracuseStep 1961315 = 2941973) B2941973
theorem B1305971 : Blo 868566 1305971 := bstep (se 1 (by rfl) ⟨979478, by rfl⟩ : syracuseStep 1305971 = 1958957) B1958957
theorem B1306001 : Blo 868566 1306001 := bstep (se 2 (by rfl) ⟨489750, by rfl⟩ : syracuseStep 1306001 = 979501) B979501
theorem B1306019 : Blo 868566 1306019 := bstep (se 1 (by rfl) ⟨979514, by rfl⟩ : syracuseStep 1306019 = 1959029) B1959029
theorem B1469873 : Blo 868566 1469873 := bstep (se 2 (by rfl) ⟨551202, by rfl⟩ : syracuseStep 1469873 = 1102405) B1102405
theorem B1306049 : Blo 868566 1306049 := bstep (se 2 (by rfl) ⟨489768, by rfl⟩ : syracuseStep 1306049 = 979537) B979537
theorem B1306067 : Blo 868566 1306067 := bstep (se 1 (by rfl) ⟨979550, by rfl⟩ : syracuseStep 1306067 = 1959101) B1959101
theorem B978403 : Blo 868566 978403 := bstep (se 1 (by rfl) ⟨733802, by rfl⟩ : syracuseStep 978403 = 1467605) B1467605
theorem B1306097 : Blo 868566 1306097 := bstep (se 2 (by rfl) ⟨489786, by rfl⟩ : syracuseStep 1306097 = 979573) B979573
theorem B1306115 : Blo 868566 1306115 := bstep (se 1 (by rfl) ⟨979586, by rfl⟩ : syracuseStep 1306115 = 1959173) B1959173
theorem B1306145 : Blo 868566 1306145 := bstep (se 2 (by rfl) ⟨489804, by rfl⟩ : syracuseStep 1306145 = 979609) B979609
theorem B1470001 : Blo 868566 1470001 := bstep (se 2 (by rfl) ⟨551250, by rfl⟩ : syracuseStep 1470001 = 1102501) B1102501
theorem B4714033 : Blo 868566 4714033 := bstep (se 2 (by rfl) ⟨1767762, by rfl⟩ : syracuseStep 4714033 = 3535525) B3535525
theorem B1306163 : Blo 868566 1306163 := bstep (se 1 (by rfl) ⟨979622, by rfl⟩ : syracuseStep 1306163 = 1959245) B1959245
theorem B1306193 : Blo 868566 1306193 := bstep (se 2 (by rfl) ⟨489822, by rfl⟩ : syracuseStep 1306193 = 979645) B979645
theorem B1470035 : Blo 868566 1470035 := bstep (se 1 (by rfl) ⟨1102526, by rfl⟩ : syracuseStep 1470035 = 2205053) B2205053
theorem B1306211 : Blo 868566 1306211 := bstep (se 1 (by rfl) ⟨979658, by rfl⟩ : syracuseStep 1306211 = 1959317) B1959317
theorem B1961585 : Blo 868566 1961585 := bstep (se 2 (by rfl) ⟨735594, by rfl⟩ : syracuseStep 1961585 = 1471189) B1471189
theorem B978547 : Blo 868566 978547 := bstep (se 1 (by rfl) ⟨733910, by rfl⟩ : syracuseStep 978547 = 1467821) B1467821
theorem B1306241 : Blo 868566 1306241 := bstep (se 2 (by rfl) ⟨489840, by rfl⟩ : syracuseStep 1306241 = 979681) B979681
theorem B1961603 : Blo 868566 1961603 := bstep (se 1 (by rfl) ⟨1471202, by rfl⟩ : syracuseStep 1961603 = 2942405) B2942405
theorem B1306259 : Blo 868566 1306259 := bstep (se 1 (by rfl) ⟨979694, by rfl⟩ : syracuseStep 1306259 = 1959389) B1959389
theorem B1306289 : Blo 868566 1306289 := bstep (se 2 (by rfl) ⟨489858, by rfl⟩ : syracuseStep 1306289 = 979717) B979717
theorem B1240753 : Blo 868566 1240753 := bstep (se 2 (by rfl) ⟨465282, by rfl⟩ : syracuseStep 1240753 = 930565) B930565
theorem B1306307 : Blo 868566 1306307 := bstep (se 1 (by rfl) ⟨979730, by rfl⟩ : syracuseStep 1306307 = 1959461) B1959461
theorem B1470163 : Blo 868566 1470163 := bstep (se 1 (by rfl) ⟨1102622, by rfl⟩ : syracuseStep 1470163 = 2205245) B2205245
theorem B1306337 : Blo 868566 1306337 := bstep (se 2 (by rfl) ⟨489876, by rfl⟩ : syracuseStep 1306337 = 979753) B979753
theorem B1306355 : Blo 868566 1306355 := bstep (se 1 (by rfl) ⟨979766, by rfl⟩ : syracuseStep 1306355 = 1959533) B1959533
theorem B978691 : Blo 868566 978691 := bstep (se 1 (by rfl) ⟨734018, by rfl⟩ : syracuseStep 978691 = 1468037) B1468037
theorem B1863427 : Blo 868566 1863427 := bstep (se 1 (by rfl) ⟨1397570, by rfl⟩ : syracuseStep 1863427 = 2795141) B2795141
theorem B2944781 : Blo 868566 2944781 := bstep (se 3 (by rfl) ⟨552146, by rfl⟩ : syracuseStep 2944781 = 1104293) B1104293
theorem B1306385 : Blo 868566 1306385 := bstep (se 2 (by rfl) ⟨489894, by rfl⟩ : syracuseStep 1306385 = 979789) B979789
theorem B1240849 : Blo 868566 1240849 := bstep (se 2 (by rfl) ⟨465318, by rfl⟩ : syracuseStep 1240849 = 930637) B930637
theorem B1175329 : Blo 868566 1175329 := bstep (se 2 (by rfl) ⟨440748, by rfl⟩ : syracuseStep 1175329 = 881497) B881497
theorem B1306403 : Blo 868566 1306403 := bstep (se 1 (by rfl) ⟨979802, by rfl⟩ : syracuseStep 1306403 = 1959605) B1959605
theorem B1306433 : Blo 868566 1306433 := bstep (se 2 (by rfl) ⟨489912, by rfl⟩ : syracuseStep 1306433 = 979825) B979825
theorem B2944835 : Blo 868566 2944835 := bstep (se 1 (by rfl) ⟨2208626, by rfl⟩ : syracuseStep 2944835 = 4417253) B4417253
theorem B1306451 : Blo 868566 1306451 := bstep (se 1 (by rfl) ⟨979838, by rfl⟩ : syracuseStep 1306451 = 1959677) B1959677
theorem B1470305 : Blo 868566 1470305 := bstep (se 2 (by rfl) ⟨551364, by rfl⟩ : syracuseStep 1470305 = 1102729) B1102729
theorem B5304163 : Blo 868566 5304163 := bstep (se 1 (by rfl) ⟨3978122, by rfl⟩ : syracuseStep 5304163 = 7956245) B7956245
theorem B1306481 : Blo 868566 1306481 := bstep (se 2 (by rfl) ⟨489930, by rfl⟩ : syracuseStep 1306481 = 979861) B979861
theorem B1306499 : Blo 868566 1306499 := bstep (se 1 (by rfl) ⟨979874, by rfl⟩ : syracuseStep 1306499 = 1959749) B1959749
theorem B1961873 : Blo 868566 1961873 := bstep (se 2 (by rfl) ⟨735702, by rfl⟩ : syracuseStep 1961873 = 1471405) B1471405
theorem B978835 : Blo 868566 978835 := bstep (se 1 (by rfl) ⟨734126, by rfl⟩ : syracuseStep 978835 = 1468253) B1468253
theorem B1306529 : Blo 868566 1306529 := bstep (se 2 (by rfl) ⟨489948, by rfl⟩ : syracuseStep 1306529 = 979897) B979897
theorem B1961891 : Blo 868566 1961891 := bstep (se 1 (by rfl) ⟨1471418, by rfl⟩ : syracuseStep 1961891 = 2942837) B2942837
theorem B3305393 : Blo 868566 3305393 := bstep (se 2 (by rfl) ⟨1239522, by rfl⟩ : syracuseStep 3305393 = 2479045) B2479045
theorem B1306547 : Blo 868566 1306547 := bstep (se 1 (by rfl) ⟨979910, by rfl⟩ : syracuseStep 1306547 = 1959821) B1959821
theorem B10579909 : Blo 868566 10579909 := bstep (se 4 (by rfl) ⟨991866, by rfl⟩ : syracuseStep 10579909 = 1983733) B1983733
theorem B1306577 : Blo 868566 1306577 := bstep (se 2 (by rfl) ⟨489966, by rfl⟩ : syracuseStep 1306577 = 979933) B979933
theorem B1470433 : Blo 868566 1470433 := bstep (se 2 (by rfl) ⟨551412, by rfl⟩ : syracuseStep 1470433 = 1102825) B1102825
theorem B1306595 : Blo 868566 1306595 := bstep (se 1 (by rfl) ⟨979946, by rfl⟩ : syracuseStep 1306595 = 1959893) B1959893
theorem B1306625 : Blo 868566 1306625 := bstep (se 2 (by rfl) ⟨489984, by rfl⟩ : syracuseStep 1306625 = 979969) B979969
theorem B1470467 : Blo 868566 1470467 := bstep (se 1 (by rfl) ⟨1102850, by rfl⟩ : syracuseStep 1470467 = 2205701) B2205701
theorem B1306643 : Blo 868566 1306643 := bstep (se 1 (by rfl) ⟨979982, by rfl⟩ : syracuseStep 1306643 = 1959965) B1959965
theorem B978979 : Blo 868566 978979 := bstep (se 1 (by rfl) ⟨734234, by rfl⟩ : syracuseStep 978979 = 1468469) B1468469
theorem B1306673 : Blo 868566 1306673 := bstep (se 2 (by rfl) ⟨490002, by rfl⟩ : syracuseStep 1306673 = 980005) B980005
theorem B1306691 : Blo 868566 1306691 := bstep (se 1 (by rfl) ⟨980018, by rfl⟩ : syracuseStep 1306691 = 1960037) B1960037
theorem B1306721 : Blo 868566 1306721 := bstep (se 2 (by rfl) ⟨490020, by rfl⟩ : syracuseStep 1306721 = 980041) B980041
theorem B1306739 : Blo 868566 1306739 := bstep (se 1 (by rfl) ⟨980054, by rfl⟩ : syracuseStep 1306739 = 1960109) B1960109
theorem B1470595 : Blo 868566 1470595 := bstep (se 1 (by rfl) ⟨1102946, by rfl⟩ : syracuseStep 1470595 = 2205893) B2205893
theorem B1306769 : Blo 868566 1306769 := bstep (se 2 (by rfl) ⟨490038, by rfl⟩ : syracuseStep 1306769 = 980077) B980077
theorem B1306787 : Blo 868566 1306787 := bstep (se 1 (by rfl) ⟨980090, by rfl⟩ : syracuseStep 1306787 = 1960181) B1960181
theorem B1568945 : Blo 868566 1568945 := bstep (se 2 (by rfl) ⟨588354, by rfl⟩ : syracuseStep 1568945 = 1176709) B1176709
theorem B1962161 : Blo 868566 1962161 := bstep (se 2 (by rfl) ⟨735810, by rfl⟩ : syracuseStep 1962161 = 1471621) B1471621
theorem B979123 : Blo 868566 979123 := bstep (se 1 (by rfl) ⟨734342, by rfl⟩ : syracuseStep 979123 = 1468685) B1468685
theorem B1306817 : Blo 868566 1306817 := bstep (se 2 (by rfl) ⟨490056, by rfl⟩ : syracuseStep 1306817 = 980113) B980113
theorem B1962179 : Blo 868566 1962179 := bstep (se 1 (by rfl) ⟨1471634, by rfl⟩ : syracuseStep 1962179 = 2943269) B2943269
theorem B1306835 : Blo 868566 1306835 := bstep (se 1 (by rfl) ⟨980126, by rfl⟩ : syracuseStep 1306835 = 1960253) B1960253
theorem B1306865 : Blo 868566 1306865 := bstep (se 2 (by rfl) ⟨490074, by rfl⟩ : syracuseStep 1306865 = 980149) B980149
theorem B1241345 : Blo 868566 1241345 := bstep (se 2 (by rfl) ⟨465504, by rfl⟩ : syracuseStep 1241345 = 931009) B931009
theorem B1306883 : Blo 868566 1306883 := bstep (se 1 (by rfl) ⟨980162, by rfl⟩ : syracuseStep 1306883 = 1960325) B1960325
theorem B1470737 : Blo 868566 1470737 := bstep (se 2 (by rfl) ⟨551526, by rfl⟩ : syracuseStep 1470737 = 1103053) B1103053
theorem B1306913 : Blo 868566 1306913 := bstep (se 2 (by rfl) ⟨490092, by rfl⟩ : syracuseStep 1306913 = 980185) B980185
theorem B1306931 : Blo 868566 1306931 := bstep (se 1 (by rfl) ⟨980198, by rfl⟩ : syracuseStep 1306931 = 1960397) B1960397
theorem B979267 : Blo 868566 979267 := bstep (se 1 (by rfl) ⟨734450, by rfl⟩ : syracuseStep 979267 = 1468901) B1468901
theorem B1306961 : Blo 868566 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B1306979 : Blo 868566 1306979 := bstep (se 1 (by rfl) ⟨980234, by rfl⟩ : syracuseStep 1306979 = 1960469) B1960469
theorem B1307009 : Blo 868566 1307009 := bstep (se 2 (by rfl) ⟨490128, by rfl⟩ : syracuseStep 1307009 = 980257) B980257
theorem B1470865 : Blo 868566 1470865 := bstep (se 2 (by rfl) ⟨551574, by rfl⟩ : syracuseStep 1470865 = 1103149) B1103149
theorem B1307027 : Blo 868566 1307027 := bstep (se 1 (by rfl) ⟨980270, by rfl⟩ : syracuseStep 1307027 = 1960541) B1960541
theorem B1307057 : Blo 868566 1307057 := bstep (se 2 (by rfl) ⟨490146, by rfl⟩ : syracuseStep 1307057 = 980293) B980293
theorem B1470899 : Blo 868566 1470899 := bstep (se 1 (by rfl) ⟨1103174, by rfl⟩ : syracuseStep 1470899 = 2206349) B2206349
theorem B1307075 : Blo 868566 1307075 := bstep (se 1 (by rfl) ⟨980306, by rfl⟩ : syracuseStep 1307075 = 1960613) B1960613
theorem B1569233 : Blo 868566 1569233 := bstep (se 2 (by rfl) ⟨588462, by rfl⟩ : syracuseStep 1569233 = 1176925) B1176925
theorem B1962449 : Blo 868566 1962449 := bstep (se 2 (by rfl) ⟨735918, by rfl⟩ : syracuseStep 1962449 = 1471837) B1471837
theorem B979411 : Blo 868566 979411 := bstep (se 1 (by rfl) ⟨734558, by rfl⟩ : syracuseStep 979411 = 1469117) B1469117
theorem B1307105 : Blo 868566 1307105 := bstep (se 2 (by rfl) ⟨490164, by rfl⟩ : syracuseStep 1307105 = 980329) B980329
theorem B1962467 : Blo 868566 1962467 := bstep (se 1 (by rfl) ⟨1471850, by rfl⟩ : syracuseStep 1962467 = 2943701) B2943701
theorem B1307123 : Blo 868566 1307123 := bstep (se 1 (by rfl) ⟨980342, by rfl⟩ : syracuseStep 1307123 = 1960685) B1960685
theorem B1307153 : Blo 868566 1307153 := bstep (se 2 (by rfl) ⟨490182, by rfl⟩ : syracuseStep 1307153 = 980365) B980365
theorem B1307171 : Blo 868566 1307171 := bstep (se 1 (by rfl) ⟨980378, by rfl⟩ : syracuseStep 1307171 = 1960757) B1960757
theorem B1471027 : Blo 868566 1471027 := bstep (se 1 (by rfl) ⟨1103270, by rfl⟩ : syracuseStep 1471027 = 2206541) B2206541
theorem B1307201 : Blo 868566 1307201 := bstep (se 2 (by rfl) ⟨490200, by rfl⟩ : syracuseStep 1307201 = 980401) B980401
theorem B1307219 : Blo 868566 1307219 := bstep (se 1 (by rfl) ⟨980414, by rfl⟩ : syracuseStep 1307219 = 1960829) B1960829
theorem B979555 : Blo 868566 979555 := bstep (se 1 (by rfl) ⟨734666, by rfl⟩ : syracuseStep 979555 = 1469333) B1469333
theorem B1307249 : Blo 868566 1307249 := bstep (se 2 (by rfl) ⟨490218, by rfl⟩ : syracuseStep 1307249 = 980437) B980437
theorem B1307267 : Blo 868566 1307267 := bstep (se 1 (by rfl) ⟨980450, by rfl⟩ : syracuseStep 1307267 = 1960901) B1960901
theorem B1307297 : Blo 868566 1307297 := bstep (se 2 (by rfl) ⟨490236, by rfl⟩ : syracuseStep 1307297 = 980473) B980473
theorem B1307315 : Blo 868566 1307315 := bstep (se 1 (by rfl) ⟨980486, by rfl⟩ : syracuseStep 1307315 = 1960973) B1960973
theorem B1471169 : Blo 868566 1471169 := bstep (se 2 (by rfl) ⟨551688, by rfl⟩ : syracuseStep 1471169 = 1103377) B1103377
theorem B1307345 : Blo 868566 1307345 := bstep (se 2 (by rfl) ⟨490254, by rfl⟩ : syracuseStep 1307345 = 980509) B980509
theorem B1307363 : Blo 868566 1307363 := bstep (se 1 (by rfl) ⟨980522, by rfl⟩ : syracuseStep 1307363 = 1961045) B1961045
theorem B1962737 : Blo 868566 1962737 := bstep (se 2 (by rfl) ⟨736026, by rfl⟩ : syracuseStep 1962737 = 1472053) B1472053
theorem B979699 : Blo 868566 979699 := bstep (se 1 (by rfl) ⟨734774, by rfl⟩ : syracuseStep 979699 = 1469549) B1469549
theorem B1307393 : Blo 868566 1307393 := bstep (se 2 (by rfl) ⟨490272, by rfl⟩ : syracuseStep 1307393 = 980545) B980545
theorem B1962755 : Blo 868566 1962755 := bstep (se 1 (by rfl) ⟨1472066, by rfl⟩ : syracuseStep 1962755 = 2944133) B2944133
theorem B1307411 : Blo 868566 1307411 := bstep (se 1 (by rfl) ⟨980558, by rfl⟩ : syracuseStep 1307411 = 1961117) B1961117
theorem B1307441 : Blo 868566 1307441 := bstep (se 2 (by rfl) ⟨490290, by rfl⟩ : syracuseStep 1307441 = 980581) B980581
theorem B1471297 : Blo 868566 1471297 := bstep (se 2 (by rfl) ⟨551736, by rfl⟩ : syracuseStep 1471297 = 1103473) B1103473
theorem B1307459 : Blo 868566 1307459 := bstep (se 1 (by rfl) ⟨980594, by rfl⟩ : syracuseStep 1307459 = 1961189) B1961189
theorem B4715333 : Blo 868566 4715333 := bstep (se 4 (by rfl) ⟨442062, by rfl⟩ : syracuseStep 4715333 = 884125) B884125
theorem B1307489 : Blo 868566 1307489 := bstep (se 2 (by rfl) ⟨490308, by rfl⟩ : syracuseStep 1307489 = 980617) B980617
theorem B2356067 : Blo 868566 2356067 := bstep (se 1 (by rfl) ⟨1767050, by rfl⟩ : syracuseStep 2356067 = 3534101) B3534101
theorem B1471331 : Blo 868566 1471331 := bstep (se 1 (by rfl) ⟨1103498, by rfl⟩ : syracuseStep 1471331 = 2206997) B2206997
theorem B1307507 : Blo 868566 1307507 := bstep (se 1 (by rfl) ⟨980630, by rfl⟩ : syracuseStep 1307507 = 1961261) B1961261
theorem B979843 : Blo 868566 979843 := bstep (se 1 (by rfl) ⟨734882, by rfl⟩ : syracuseStep 979843 = 1469765) B1469765
theorem B1307537 : Blo 868566 1307537 := bstep (se 2 (by rfl) ⟨490326, by rfl⟩ : syracuseStep 1307537 = 980653) B980653
theorem B1307555 : Blo 868566 1307555 := bstep (se 1 (by rfl) ⟨980666, by rfl⟩ : syracuseStep 1307555 = 1961333) B1961333
theorem B1307585 : Blo 868566 1307585 := bstep (se 2 (by rfl) ⟨490344, by rfl⟩ : syracuseStep 1307585 = 980689) B980689
theorem B1307603 : Blo 868566 1307603 := bstep (se 1 (by rfl) ⟨980702, by rfl⟩ : syracuseStep 1307603 = 1961405) B1961405
theorem B1471459 : Blo 868566 1471459 := bstep (se 1 (by rfl) ⟨1103594, by rfl⟩ : syracuseStep 1471459 = 2207189) B2207189
theorem B1307633 : Blo 868566 1307633 := bstep (se 2 (by rfl) ⟨490362, by rfl⟩ : syracuseStep 1307633 = 980725) B980725
theorem B1307651 : Blo 868566 1307651 := bstep (se 1 (by rfl) ⟨980738, by rfl⟩ : syracuseStep 1307651 = 1961477) B1961477
theorem B1963025 : Blo 868566 1963025 := bstep (se 2 (by rfl) ⟨736134, by rfl⟩ : syracuseStep 1963025 = 1472269) B1472269
theorem B979987 : Blo 868566 979987 := bstep (se 1 (by rfl) ⟨734990, by rfl⟩ : syracuseStep 979987 = 1469981) B1469981
theorem B1307681 : Blo 868566 1307681 := bstep (se 2 (by rfl) ⟨490380, by rfl⟩ : syracuseStep 1307681 = 980761) B980761
theorem B1963043 : Blo 868566 1963043 := bstep (se 1 (by rfl) ⟨1472282, by rfl⟩ : syracuseStep 1963043 = 2944565) B2944565
theorem B1307699 : Blo 868566 1307699 := bstep (se 1 (by rfl) ⟨980774, by rfl⟩ : syracuseStep 1307699 = 1961549) B1961549
theorem B1307729 : Blo 868566 1307729 := bstep (se 2 (by rfl) ⟨490398, by rfl⟩ : syracuseStep 1307729 = 980797) B980797
theorem B1307747 : Blo 868566 1307747 := bstep (se 1 (by rfl) ⟨980810, by rfl⟩ : syracuseStep 1307747 = 1961621) B1961621
theorem B1242211 : Blo 868566 1242211 := bstep (se 1 (by rfl) ⟨931658, by rfl⟩ : syracuseStep 1242211 = 1863317) B1863317
theorem B1471601 : Blo 868566 1471601 := bstep (se 2 (by rfl) ⟨551850, by rfl⟩ : syracuseStep 1471601 = 1103701) B1103701
theorem B1307777 : Blo 868566 1307777 := bstep (se 2 (by rfl) ⟨490416, by rfl⟩ : syracuseStep 1307777 = 980833) B980833
theorem B1307795 : Blo 868566 1307795 := bstep (se 1 (by rfl) ⟨980846, by rfl⟩ : syracuseStep 1307795 = 1961693) B1961693
theorem B980131 : Blo 868566 980131 := bstep (se 1 (by rfl) ⟨735098, by rfl⟩ : syracuseStep 980131 = 1470197) B1470197
theorem B1307825 : Blo 868566 1307825 := bstep (se 2 (by rfl) ⟨490434, by rfl⟩ : syracuseStep 1307825 = 980869) B980869
theorem B1307843 : Blo 868566 1307843 := bstep (se 1 (by rfl) ⟨980882, by rfl⟩ : syracuseStep 1307843 = 1961765) B1961765
theorem B1242307 : Blo 868566 1242307 := bstep (se 1 (by rfl) ⟨931730, by rfl⟩ : syracuseStep 1242307 = 1863461) B1863461
theorem B1307873 : Blo 868566 1307873 := bstep (se 2 (by rfl) ⟨490452, by rfl⟩ : syracuseStep 1307873 = 980905) B980905
theorem B1471729 : Blo 868566 1471729 := bstep (se 2 (by rfl) ⟨551898, by rfl⟩ : syracuseStep 1471729 = 1103797) B1103797
theorem B1045747 : Blo 868566 1045747 := bstep (se 1 (by rfl) ⟨784310, by rfl⟩ : syracuseStep 1045747 = 1568621) B1568621
theorem B1307891 : Blo 868566 1307891 := bstep (se 1 (by rfl) ⟨980918, by rfl⟩ : syracuseStep 1307891 = 1961837) B1961837
theorem B1307921 : Blo 868566 1307921 := bstep (se 2 (by rfl) ⟨490470, by rfl⟩ : syracuseStep 1307921 = 980941) B980941
theorem B1471763 : Blo 868566 1471763 := bstep (se 1 (by rfl) ⟨1103822, by rfl⟩ : syracuseStep 1471763 = 2207645) B2207645
theorem B1307939 : Blo 868566 1307939 := bstep (se 1 (by rfl) ⟨980954, by rfl⟩ : syracuseStep 1307939 = 1961909) B1961909
theorem B3437873 : Blo 868566 3437873 := bstep (se 2 (by rfl) ⟨1289202, by rfl⟩ : syracuseStep 3437873 = 2578405) B2578405
theorem B980275 : Blo 868566 980275 := bstep (se 1 (by rfl) ⟨735206, by rfl⟩ : syracuseStep 980275 = 1470413) B1470413
theorem B1307969 : Blo 868566 1307969 := bstep (se 2 (by rfl) ⟨490488, by rfl⟩ : syracuseStep 1307969 = 980977) B980977
theorem B1307987 : Blo 868566 1307987 := bstep (se 1 (by rfl) ⟨980990, by rfl⟩ : syracuseStep 1307987 = 1961981) B1961981
theorem B3306851 : Blo 868566 3306851 := bstep (se 1 (by rfl) ⟨2480138, by rfl⟩ : syracuseStep 3306851 = 4960277) B4960277
theorem B3306865 : Blo 868566 3306865 := bstep (se 2 (by rfl) ⟨1240074, by rfl⟩ : syracuseStep 3306865 = 2480149) B2480149
theorem B1308017 : Blo 868566 1308017 := bstep (se 2 (by rfl) ⟨490506, by rfl⟩ : syracuseStep 1308017 = 981013) B981013
theorem B1308035 : Blo 868566 1308035 := bstep (se 1 (by rfl) ⟨981026, by rfl⟩ : syracuseStep 1308035 = 1962053) B1962053
theorem B1471891 : Blo 868566 1471891 := bstep (se 1 (by rfl) ⟨1103918, by rfl⟩ : syracuseStep 1471891 = 2207837) B2207837
theorem B1308065 : Blo 868566 1308065 := bstep (se 2 (by rfl) ⟨490524, by rfl⟩ : syracuseStep 1308065 = 981049) B981049
theorem B1045939 : Blo 868566 1045939 := bstep (se 1 (by rfl) ⟨784454, by rfl⟩ : syracuseStep 1045939 = 1568909) B1568909
theorem B1308083 : Blo 868566 1308083 := bstep (se 1 (by rfl) ⟨981062, by rfl⟩ : syracuseStep 1308083 = 1962125) B1962125
theorem B980419 : Blo 868566 980419 := bstep (se 1 (by rfl) ⟨735314, by rfl⟩ : syracuseStep 980419 = 1470629) B1470629
theorem B1308113 : Blo 868566 1308113 := bstep (se 2 (by rfl) ⟨490542, by rfl⟩ : syracuseStep 1308113 = 981085) B981085
theorem B1308131 : Blo 868566 1308131 := bstep (se 1 (by rfl) ⟨981098, by rfl⟩ : syracuseStep 1308131 = 1962197) B1962197
theorem B1308161 : Blo 868566 1308161 := bstep (se 2 (by rfl) ⟨490560, by rfl⟩ : syracuseStep 1308161 = 981121) B981121
theorem B1308179 : Blo 868566 1308179 := bstep (se 1 (by rfl) ⟨981134, by rfl⟩ : syracuseStep 1308179 = 1962269) B1962269
theorem B1472033 : Blo 868566 1472033 := bstep (se 2 (by rfl) ⟨552012, by rfl⟩ : syracuseStep 1472033 = 1104025) B1104025
theorem B1308209 : Blo 868566 1308209 := bstep (se 2 (by rfl) ⟨490578, by rfl⟩ : syracuseStep 1308209 = 981157) B981157
theorem B1308227 : Blo 868566 1308227 := bstep (se 1 (by rfl) ⟨981170, by rfl⟩ : syracuseStep 1308227 = 1962341) B1962341
theorem B980563 : Blo 868566 980563 := bstep (se 1 (by rfl) ⟨735422, by rfl⟩ : syracuseStep 980563 = 1470845) B1470845
theorem B1308257 : Blo 868566 1308257 := bstep (se 2 (by rfl) ⟨490596, by rfl⟩ : syracuseStep 1308257 = 981193) B981193
theorem B1308275 : Blo 868566 1308275 := bstep (se 1 (by rfl) ⟨981206, by rfl⟩ : syracuseStep 1308275 = 1962413) B1962413
theorem B1308305 : Blo 868566 1308305 := bstep (se 2 (by rfl) ⟨490614, by rfl⟩ : syracuseStep 1308305 = 981229) B981229
theorem B1472161 : Blo 868566 1472161 := bstep (se 2 (by rfl) ⟨552060, by rfl⟩ : syracuseStep 1472161 = 1104121) B1104121
theorem B1308323 : Blo 868566 1308323 := bstep (se 1 (by rfl) ⟨981242, by rfl⟩ : syracuseStep 1308323 = 1962485) B1962485
theorem B1308353 : Blo 868566 1308353 := bstep (se 2 (by rfl) ⟨490632, by rfl⟩ : syracuseStep 1308353 = 981265) B981265
theorem B1472195 : Blo 868566 1472195 := bstep (se 1 (by rfl) ⟨1104146, by rfl⟩ : syracuseStep 1472195 = 2208293) B2208293
theorem B1308371 : Blo 868566 1308371 := bstep (se 1 (by rfl) ⟨981278, by rfl⟩ : syracuseStep 1308371 = 1962557) B1962557
theorem B980707 : Blo 868566 980707 := bstep (se 1 (by rfl) ⟨735530, by rfl⟩ : syracuseStep 980707 = 1471061) B1471061
theorem B1308401 : Blo 868566 1308401 := bstep (se 2 (by rfl) ⟨490650, by rfl⟩ : syracuseStep 1308401 = 981301) B981301
theorem B1308419 : Blo 868566 1308419 := bstep (se 1 (by rfl) ⟨981314, by rfl⟩ : syracuseStep 1308419 = 1962629) B1962629
theorem B1308449 : Blo 868566 1308449 := bstep (se 2 (by rfl) ⟨490668, by rfl⟩ : syracuseStep 1308449 = 981337) B981337
theorem B1308467 : Blo 868566 1308467 := bstep (se 1 (by rfl) ⟨981350, by rfl⟩ : syracuseStep 1308467 = 1962701) B1962701
theorem B1472323 : Blo 868566 1472323 := bstep (se 1 (by rfl) ⟨1104242, by rfl⟩ : syracuseStep 1472323 = 2208485) B2208485
theorem B1308497 : Blo 868566 1308497 := bstep (se 2 (by rfl) ⟨490686, by rfl⟩ : syracuseStep 1308497 = 981373) B981373
theorem B1308515 : Blo 868566 1308515 := bstep (se 1 (by rfl) ⟨981386, by rfl⟩ : syracuseStep 1308515 = 1962773) B1962773
theorem B980851 : Blo 868566 980851 := bstep (se 1 (by rfl) ⟨735638, by rfl⟩ : syracuseStep 980851 = 1471277) B1471277
theorem B1308545 : Blo 868566 1308545 := bstep (se 2 (by rfl) ⟨490704, by rfl⟩ : syracuseStep 1308545 = 981409) B981409
theorem B1308563 : Blo 868566 1308563 := bstep (se 1 (by rfl) ⟨981422, by rfl⟩ : syracuseStep 1308563 = 1962845) B1962845
theorem B1308593 : Blo 868566 1308593 := bstep (se 2 (by rfl) ⟨490722, by rfl⟩ : syracuseStep 1308593 = 981445) B981445
theorem B1046467 : Blo 868566 1046467 := bstep (se 1 (by rfl) ⟨784850, by rfl⟩ : syracuseStep 1046467 = 1569701) B1569701
theorem B1308611 : Blo 868566 1308611 := bstep (se 1 (by rfl) ⟨981458, by rfl⟩ : syracuseStep 1308611 = 1962917) B1962917
theorem B1308641 : Blo 868566 1308641 := bstep (se 2 (by rfl) ⟨490740, by rfl⟩ : syracuseStep 1308641 = 981481) B981481
theorem B2652131 : Blo 868566 2652131 := bstep (se 1 (by rfl) ⟨1989098, by rfl⟩ : syracuseStep 2652131 = 3978197) B3978197
theorem B5568497 : Blo 868566 5568497 := bstep (se 2 (by rfl) ⟨2088186, by rfl⟩ : syracuseStep 5568497 = 4176373) B4176373
theorem B1308659 : Blo 868566 1308659 := bstep (se 1 (by rfl) ⟨981494, by rfl⟩ : syracuseStep 1308659 = 1962989) B1962989
theorem B980995 : Blo 868566 980995 := bstep (se 1 (by rfl) ⟨735746, by rfl⟩ : syracuseStep 980995 = 1471493) B1471493
theorem B1308689 : Blo 868566 1308689 := bstep (se 2 (by rfl) ⟨490758, by rfl⟩ : syracuseStep 1308689 = 981517) B981517
theorem B5568547 : Blo 868566 5568547 := bstep (se 1 (by rfl) ⟨4176410, by rfl⟩ : syracuseStep 5568547 = 8352821) B8352821
theorem B1046563 : Blo 868566 1046563 := bstep (se 1 (by rfl) ⟨784922, by rfl⟩ : syracuseStep 1046563 = 1569845) B1569845
theorem B1308707 : Blo 868566 1308707 := bstep (se 1 (by rfl) ⟨981530, by rfl⟩ : syracuseStep 1308707 = 1963061) B1963061
theorem B1308737 : Blo 868566 1308737 := bstep (se 2 (by rfl) ⟨490776, by rfl⟩ : syracuseStep 1308737 = 981553) B981553
theorem B1308755 : Blo 868566 1308755 := bstep (se 1 (by rfl) ⟨981566, by rfl⟩ : syracuseStep 1308755 = 1963133) B1963133
theorem B9893987 : Blo 868566 9893987 := bstep (se 1 (by rfl) ⟨7420490, by rfl⟩ : syracuseStep 9893987 = 14840981) B14840981
theorem B1308785 : Blo 868566 1308785 := bstep (se 2 (by rfl) ⟨490794, by rfl⟩ : syracuseStep 1308785 = 981589) B981589
theorem B1308803 : Blo 868566 1308803 := bstep (se 1 (by rfl) ⟨981602, by rfl⟩ : syracuseStep 1308803 = 1963205) B1963205
theorem B981139 : Blo 868566 981139 := bstep (se 1 (by rfl) ⟨735854, by rfl⟩ : syracuseStep 981139 = 1471709) B1471709
theorem B1308833 : Blo 868566 1308833 := bstep (se 2 (by rfl) ⟨490812, by rfl⟩ : syracuseStep 1308833 = 981625) B981625
theorem B3143843 : Blo 868566 3143843 := bstep (se 1 (by rfl) ⟨2357882, by rfl⟩ : syracuseStep 3143843 = 4715765) B4715765
theorem B1767665 : Blo 868566 1767665 := bstep (se 2 (by rfl) ⟨662874, by rfl⟩ : syracuseStep 1767665 = 1325749) B1325749
theorem B981283 : Blo 868566 981283 := bstep (se 1 (by rfl) ⟨735962, by rfl⟩ : syracuseStep 981283 = 1471925) B1471925
theorem B1341841 : Blo 868566 1341841 := bstep (se 2 (by rfl) ⟨503190, by rfl⟩ : syracuseStep 1341841 = 1006381) B1006381
theorem B981427 : Blo 868566 981427 := bstep (se 1 (by rfl) ⟨736070, by rfl⟩ : syracuseStep 981427 = 1472141) B1472141
theorem B981571 : Blo 868566 981571 := bstep (se 1 (by rfl) ⟨736178, by rfl⟩ : syracuseStep 981571 = 1472357) B1472357
theorem B26835569 : Blo 868566 26835569 := bstep (se 2 (by rfl) ⟨10063338, by rfl⟩ : syracuseStep 26835569 = 20126677) B20126677
theorem B2784017 : Blo 868566 2784017 := bstep (se 2 (by rfl) ⟨1044006, by rfl⟩ : syracuseStep 2784017 = 2088013) B2088013
theorem B3308323 : Blo 868566 3308323 := bstep (se 1 (by rfl) ⟨2481242, by rfl⟩ : syracuseStep 3308323 = 4962485) B4962485
theorem B1768241 : Blo 868566 1768241 := bstep (se 2 (by rfl) ⟨663090, by rfl⟩ : syracuseStep 1768241 = 1326181) B1326181
theorem B1047539 : Blo 868566 1047539 := bstep (se 1 (by rfl) ⟨785654, by rfl⟩ : syracuseStep 1047539 = 1571309) B1571309
theorem B25426997 : Blo 868566 25426997 := bstep (se 5 (by rfl) ⟨1191890, by rfl⟩ : syracuseStep 25426997 = 2383781) B2383781
theorem B2358467 : Blo 868566 2358467 := bstep (se 1 (by rfl) ⟨1768850, by rfl⟩ : syracuseStep 2358467 = 3537701) B3537701
theorem B3177677 : Blo 868566 3177677 := bstep (se 3 (by rfl) ⟨595814, by rfl⟩ : syracuseStep 3177677 = 1191629) B1191629
theorem B2784557 : Blo 868566 2784557 := bstep (se 3 (by rfl) ⟨522104, by rfl⟩ : syracuseStep 2784557 = 1044209) B1044209
theorem B2981539 : Blo 868566 2981539 := bstep (se 1 (by rfl) ⟨2236154, by rfl⟩ : syracuseStep 2981539 = 4472309) B4472309
theorem B11894627 : Blo 868566 11894627 := bstep (se 1 (by rfl) ⟨8920970, by rfl⟩ : syracuseStep 11894627 = 17841941) B17841941
theorem B3310253 : Blo 868566 3310253 := bstep (se 3 (by rfl) ⟨620672, by rfl⟩ : syracuseStep 3310253 = 1241345) B1241345
theorem B103383793 : Blo 868566 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B1671959 : Blo 868566 1671959 := bstep (se 1 (by rfl) ⟨1253969, by rfl⟩ : syracuseStep 1671959 = 2507939) B2507939
theorem B6620291 : Blo 868566 6620291 := bstep (se 1 (by rfl) ⟨4965218, by rfl⟩ : syracuseStep 6620291 = 9930437) B9930437
theorem B3966155 : Blo 868566 3966155 := bstep (se 1 (by rfl) ⟨2974616, by rfl⟩ : syracuseStep 3966155 = 5949233) B5949233
theorem B3311027 : Blo 868566 3311027 := bstep (se 1 (by rfl) ⟨2483270, by rfl⟩ : syracuseStep 3311027 = 4966541) B4966541
theorem B1672663 : Blo 868566 1672663 := bstep (se 1 (by rfl) ⟨1254497, by rfl⟩ : syracuseStep 1672663 = 2508995) B2508995
theorem B2229811 : Blo 868566 2229811 := bstep (se 1 (by rfl) ⟨1672358, by rfl⟩ : syracuseStep 2229811 = 3344717) B3344717
theorem B2983513 : Blo 868566 2983513 := bstep (se 2 (by rfl) ⟨1118817, by rfl⟩ : syracuseStep 2983513 = 2237635) B2237635
theorem B30214295 : Blo 868566 30214295 := bstep (se 1 (by rfl) ⟨22660721, by rfl⟩ : syracuseStep 30214295 = 45321443) B45321443
theorem B11897093 : Blo 868566 11897093 := bstep (se 4 (by rfl) ⟨1115352, by rfl⟩ : syracuseStep 11897093 = 2230705) B2230705
theorem B3967321 : Blo 868566 3967321 := bstep (se 2 (by rfl) ⟨1487745, by rfl⟩ : syracuseStep 3967321 = 2975491) B2975491
theorem B2984471 : Blo 868566 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B10029719 : Blo 868566 10029719 := bstep (se 1 (by rfl) ⟨7522289, by rfl⟩ : syracuseStep 10029719 = 15044579) B15044579
theorem B3312515 : Blo 868566 3312515 := bstep (se 1 (by rfl) ⟨2484386, by rfl⟩ : syracuseStep 3312515 = 4968773) B4968773
theorem B1674263 : Blo 868566 1674263 := bstep (se 1 (by rfl) ⟨1255697, by rfl⟩ : syracuseStep 1674263 = 2511395) B2511395
theorem B2198603 : Blo 868566 2198603 := bstep (se 1 (by rfl) ⟨1648952, by rfl⟩ : syracuseStep 2198603 = 3297905) B3297905
theorem B2788631 : Blo 868566 2788631 := bstep (se 1 (by rfl) ⟨2091473, by rfl⟩ : syracuseStep 2788631 = 4182947) B4182947
theorem B3312971 : Blo 868566 3312971 := bstep (se 1 (by rfl) ⟨2484728, by rfl⟩ : syracuseStep 3312971 = 4969457) B4969457
theorem B2788759 : Blo 868566 2788759 := bstep (se 1 (by rfl) ⟨2091569, by rfl⟩ : syracuseStep 2788759 = 4183139) B4183139
theorem B2232215 : Blo 868566 2232215 := bstep (se 1 (by rfl) ⟨1674161, by rfl⟩ : syracuseStep 2232215 = 3348323) B3348323
theorem B14323729 : Blo 868566 14323729 := bstep (se 2 (by rfl) ⟨5371398, by rfl⟩ : syracuseStep 14323729 = 10742797) B10742797
theorem B2199575 : Blo 868566 2199575 := bstep (se 1 (by rfl) ⟨1649681, by rfl⟩ : syracuseStep 2199575 = 3299363) B3299363
theorem B4460609 : Blo 868566 4460609 := bstep (se 2 (by rfl) ⟨1672728, by rfl⟩ : syracuseStep 4460609 = 3345457) B3345457
theorem B2789579 : Blo 868566 2789579 := bstep (se 1 (by rfl) ⟨2092184, by rfl⟩ : syracuseStep 2789579 = 4184369) B4184369
theorem B6623693 : Blo 868566 6623693 := bstep (se 3 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 6623693 = 2483885) B2483885
theorem B3969587 : Blo 868566 3969587 := bstep (se 1 (by rfl) ⟨2977190, by rfl⟩ : syracuseStep 3969587 = 5954381) B5954381
theorem B3772993 : Blo 868566 3772993 := bstep (se 2 (by rfl) ⟨1414872, by rfl⟩ : syracuseStep 3772993 = 2829745) B2829745
theorem B2200243 : Blo 868566 2200243 := bstep (se 1 (by rfl) ⟨1650182, by rfl⟩ : syracuseStep 2200243 = 3300365) B3300365
theorem B21205745 : Blo 868566 21205745 := bstep (se 2 (by rfl) ⟨7952154, by rfl⟩ : syracuseStep 21205745 = 15904309) B15904309
theorem B2200385 : Blo 868566 2200385 := bstep (se 2 (by rfl) ⟨825144, by rfl⟩ : syracuseStep 2200385 = 1650289) B1650289
theorem B6624179 : Blo 868566 6624179 := bstep (se 1 (by rfl) ⟨4968134, by rfl⟩ : syracuseStep 6624179 = 9936269) B9936269
theorem B9409553 : Blo 868566 9409553 := bstep (se 2 (by rfl) ⟨3528582, by rfl⟩ : syracuseStep 9409553 = 7057165) B7057165
theorem B6264013 : Blo 868566 6264013 := bstep (se 3 (by rfl) ⟨1174502, by rfl⟩ : syracuseStep 6264013 = 2349005) B2349005
theorem B13407437 : Blo 868566 13407437 := bstep (se 3 (by rfl) ⟨2513894, by rfl⟩ : syracuseStep 13407437 = 5027789) B5027789
theorem B4953419 : Blo 868566 4953419 := bstep (se 1 (by rfl) ⟨3715064, by rfl⟩ : syracuseStep 4953419 = 7430129) B7430129
theorem B1414667 : Blo 868566 1414667 := bstep (se 1 (by rfl) ⟨1061000, by rfl⟩ : syracuseStep 1414667 = 2122001) B2122001
theorem B2791091 : Blo 868566 2791091 := bstep (se 1 (by rfl) ⟨2093318, by rfl⟩ : syracuseStep 2791091 = 4186637) B4186637
theorem B2201651 : Blo 868566 2201651 := bstep (se 1 (by rfl) ⟨1651238, by rfl⟩ : syracuseStep 2201651 = 3302477) B3302477
theorem B1906931 : Blo 868566 1906931 := bstep (se 1 (by rfl) ⟨1430198, by rfl⟩ : syracuseStep 1906931 = 2860397) B2860397
theorem B21174533 : Blo 868566 21174533 := bstep (se 4 (by rfl) ⟨1985112, by rfl⟩ : syracuseStep 21174533 = 3970225) B3970225
theorem B6625637 : Blo 868566 6625637 := bstep (se 4 (by rfl) ⟨621153, by rfl⟩ : syracuseStep 6625637 = 1242307) B1242307
theorem B2202187 : Blo 868566 2202187 := bstep (se 1 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 2202187 = 3303281) B3303281
theorem B2202329 : Blo 868566 2202329 := bstep (se 2 (by rfl) ⟨825873, by rfl⟩ : syracuseStep 2202329 = 1651747) B1651747
theorem B4397975 : Blo 868566 4397975 := bstep (se 1 (by rfl) ⟨3298481, by rfl⟩ : syracuseStep 4397975 = 6596963) B6596963
theorem B13376663 : Blo 868566 13376663 := bstep (se 1 (by rfl) ⟨10032497, by rfl⟩ : syracuseStep 13376663 = 20064995) B20064995
theorem B3710231 : Blo 868566 3710231 := bstep (se 1 (by rfl) ⟨2782673, by rfl⟩ : syracuseStep 3710231 = 5565347) B5565347
theorem B3972503 : Blo 868566 3972503 := bstep (se 1 (by rfl) ⟨2979377, by rfl⟩ : syracuseStep 3972503 = 5958755) B5958755
theorem B2203159 : Blo 868566 2203159 := bstep (se 1 (by rfl) ⟨1652369, by rfl⟩ : syracuseStep 2203159 = 3304739) B3304739
theorem B2203595 : Blo 868566 2203595 := bstep (se 1 (by rfl) ⟨1652696, by rfl⟩ : syracuseStep 2203595 = 3305393) B3305393
theorem B2793437 : Blo 868566 2793437 := bstep (se 3 (by rfl) ⟨523769, by rfl⟩ : syracuseStep 2793437 = 1047539) B1047539
theorem B4464715 : Blo 868566 4464715 := bstep (se 1 (by rfl) ⟨3348536, by rfl⟩ : syracuseStep 4464715 = 6697073) B6697073
theorem B2859229 : Blo 868566 2859229 := bstep (se 3 (by rfl) ⟨536105, by rfl⟩ : syracuseStep 2859229 = 1072211) B1072211
theorem B2203969 : Blo 868566 2203969 := bstep (se 2 (by rfl) ⟨826488, by rfl⟩ : syracuseStep 2203969 = 1652977) B1652977
theorem B3023581 : Blo 868566 3023581 := bstep (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) B1133843
theorem B5808997 : Blo 868566 5808997 := bstep (se 4 (by rfl) ⟨544593, by rfl⟩ : syracuseStep 5808997 = 1089187) B1089187
theorem B15901541 : Blo 868566 15901541 := bstep (se 4 (by rfl) ⟨1490769, by rfl⟩ : syracuseStep 15901541 = 2981539) B2981539
theorem B2204567 : Blo 868566 2204567 := bstep (se 1 (by rfl) ⟨1653425, by rfl⟩ : syracuseStep 2204567 = 3306851) B3306851
theorem B3351617 : Blo 868566 3351617 := bstep (se 2 (by rfl) ⟨1256856, by rfl⟩ : syracuseStep 3351617 = 2513713) B2513713
theorem B5579927 : Blo 868566 5579927 := bstep (se 1 (by rfl) ⟨4184945, by rfl⟩ : syracuseStep 5579927 = 8369891) B8369891
theorem B3712331 : Blo 868566 3712331 := bstep (se 1 (by rfl) ⟨2784248, by rfl⟩ : syracuseStep 3712331 = 5568497) B5568497
theorem B6595991 : Blo 868566 6595991 := bstep (se 1 (by rfl) ⟨4946993, by rfl⟩ : syracuseStep 6595991 = 9893987) B9893987
theorem B6268421 : Blo 868566 6268421 := bstep (se 4 (by rfl) ⟨587664, by rfl⟩ : syracuseStep 6268421 = 1175329) B1175329
theorem B2205377 : Blo 868566 2205377 := bstep (se 2 (by rfl) ⟨827016, by rfl⟩ : syracuseStep 2205377 = 1654033) B1654033
theorem B16951331 : Blo 868566 16951331 := bstep (se 1 (by rfl) ⟨12713498, by rfl⟩ : syracuseStep 16951331 = 25426997) B25426997
theorem B2205913 : Blo 868566 2205913 := bstep (se 2 (by rfl) ⟨827217, by rfl⟩ : syracuseStep 2205913 = 1654435) B1654435
theorem B993655 : Blo 868566 993655 := bstep (se 1 (by rfl) ⟨745241, by rfl⟩ : syracuseStep 993655 = 1490483) B1490483
theorem B4401539 : Blo 868566 4401539 := bstep (se 1 (by rfl) ⟨3301154, by rfl⟩ : syracuseStep 4401539 = 6602309) B6602309
theorem B1649089 : Blo 868566 1649089 := bstep (se 2 (by rfl) ⟨618408, by rfl⟩ : syracuseStep 1649089 = 1236817) B1236817
theorem B928279 : Blo 868566 928279 := bstep (se 1 (by rfl) ⟨696209, by rfl⟩ : syracuseStep 928279 = 1392419) B1392419
theorem B928459 : Blo 868566 928459 := bstep (se 1 (by rfl) ⟨696344, by rfl⟩ : syracuseStep 928459 = 1392689) B1392689
theorem B1288921 : Blo 868566 1288921 := bstep (se 2 (by rfl) ⟨483345, by rfl⟩ : syracuseStep 1288921 = 966691) B966691
theorem B5581669 : Blo 868566 5581669 := bstep (se 4 (by rfl) ⟨523281, by rfl⟩ : syracuseStep 5581669 = 1046563) B1046563
theorem B3713971 : Blo 868566 3713971 := bstep (se 1 (by rfl) ⟨2785478, by rfl⟩ : syracuseStep 3713971 = 5570957) B5570957
theorem B1485899 : Blo 868566 1485899 := bstep (se 1 (by rfl) ⟨1114424, by rfl⟩ : syracuseStep 1485899 = 2228849) B2228849
theorem B1649803 : Blo 868566 1649803 := bstep (se 1 (by rfl) ⟨1237352, by rfl⟩ : syracuseStep 1649803 = 2474705) B2474705
theorem B1649879 : Blo 868566 1649879 := bstep (se 1 (by rfl) ⟨1237409, by rfl⟩ : syracuseStep 1649879 = 2474819) B2474819
theorem B2207027 : Blo 868566 2207027 := bstep (se 1 (by rfl) ⟨1655270, by rfl⟩ : syracuseStep 2207027 = 3310541) B3310541
theorem B3714605 : Blo 868566 3714605 := bstep (se 3 (by rfl) ⟨696488, by rfl⟩ : syracuseStep 3714605 = 1392977) B1392977
theorem B7056971 : Blo 868566 7056971 := bstep (se 1 (by rfl) ⟨5292728, by rfl⟩ : syracuseStep 7056971 = 10585457) B10585457
theorem B2207321 : Blo 868566 2207321 := bstep (se 2 (by rfl) ⟨827745, by rfl⟩ : syracuseStep 2207321 = 1655491) B1655491
theorem B1322635 : Blo 868566 1322635 := bstep (se 1 (by rfl) ⟨991976, by rfl⟩ : syracuseStep 1322635 = 1983953) B1983953
theorem B7450289 : Blo 868566 7450289 := bstep (se 2 (by rfl) ⟨2793858, by rfl⟩ : syracuseStep 7450289 = 5587717) B5587717
theorem B1650547 : Blo 868566 1650547 := bstep (se 1 (by rfl) ⟨1237910, by rfl⟩ : syracuseStep 1650547 = 2475821) B2475821
theorem B1650775 : Blo 868566 1650775 := bstep (se 1 (by rfl) ⟨1238081, by rfl⟩ : syracuseStep 1650775 = 2476163) B2476163
theorem B1060951 : Blo 868566 1060951 := bstep (se 1 (by rfl) ⟨795713, by rfl⟩ : syracuseStep 1060951 = 1591427) B1591427
theorem B1650881 : Blo 868566 1650881 := bstep (se 2 (by rfl) ⟨619080, by rfl⟩ : syracuseStep 1650881 = 1238161) B1238161
theorem B1651033 : Blo 868566 1651033 := bstep (se 2 (by rfl) ⟨619137, by rfl⟩ : syracuseStep 1651033 = 1238275) B1238275
theorem B7450973 : Blo 868566 7450973 := bstep (se 3 (by rfl) ⟨1397057, by rfl⟩ : syracuseStep 7450973 = 2794115) B2794115
theorem B930475 : Blo 868566 930475 := bstep (se 1 (by rfl) ⟨697856, by rfl⟩ : syracuseStep 930475 = 1395713) B1395713
theorem B1487575 : Blo 868566 1487575 := bstep (se 1 (by rfl) ⟨1115681, by rfl⟩ : syracuseStep 1487575 = 2231363) B2231363
theorem B32158565 : Blo 868566 32158565 := bstep (se 4 (by rfl) ⟨3014865, by rfl⟩ : syracuseStep 32158565 = 6029731) B6029731
theorem B3978413 : Blo 868566 3978413 := bstep (se 3 (by rfl) ⟨745952, by rfl⟩ : syracuseStep 3978413 = 1491905) B1491905
theorem B1324363 : Blo 868566 1324363 := bstep (se 1 (by rfl) ⟨993272, by rfl⟩ : syracuseStep 1324363 = 1986545) B1986545
theorem B6698371 : Blo 868566 6698371 := bstep (se 1 (by rfl) ⟨5023778, by rfl⟩ : syracuseStep 6698371 = 10047557) B10047557
theorem B1652339 : Blo 868566 1652339 := bstep (se 1 (by rfl) ⟨1239254, by rfl⟩ : syracuseStep 1652339 = 2478509) B2478509
theorem B1652491 : Blo 868566 1652491 := bstep (se 1 (by rfl) ⟨1239368, by rfl⟩ : syracuseStep 1652491 = 2478737) B2478737
theorem B4405265 : Blo 868566 4405265 := bstep (se 2 (by rfl) ⟨1651974, by rfl⟩ : syracuseStep 4405265 = 3303949) B3303949
theorem B1652825 : Blo 868566 1652825 := bstep (se 2 (by rfl) ⟨619809, by rfl⟩ : syracuseStep 1652825 = 1239619) B1239619
theorem B4405427 : Blo 868566 4405427 := bstep (se 1 (by rfl) ⟨3304070, by rfl⟩ : syracuseStep 4405427 = 6608141) B6608141
theorem B1653463 : Blo 868566 1653463 := bstep (se 1 (by rfl) ⟨1240097, by rfl⟩ : syracuseStep 1653463 = 2480195) B2480195
theorem B2931659 : Blo 868566 2931659 := bstep (se 1 (by rfl) ⟨2198744, by rfl⟩ : syracuseStep 2931659 = 4397489) B4397489
theorem B3718295 : Blo 868566 3718295 := bstep (se 1 (by rfl) ⟨2788721, by rfl⟩ : syracuseStep 3718295 = 5577443) B5577443
theorem B2931929 : Blo 868566 2931929 := bstep (se 2 (by rfl) ⟨1099473, by rfl⟩ : syracuseStep 2931929 = 2198947) B2198947
theorem B6438275 : Blo 868566 6438275 := bstep (se 1 (by rfl) ⟨4828706, by rfl⟩ : syracuseStep 6438275 = 9657413) B9657413
theorem B1654283 : Blo 868566 1654283 := bstep (se 1 (by rfl) ⟨1240712, by rfl⟩ : syracuseStep 1654283 = 2481425) B2481425
theorem B1654337 : Blo 868566 1654337 := bstep (se 2 (by rfl) ⟨620376, by rfl⟩ : syracuseStep 1654337 = 1240753) B1240753
theorem B2932631 : Blo 868566 2932631 := bstep (se 1 (by rfl) ⟨2199473, by rfl⟩ : syracuseStep 2932631 = 4398947) B4398947
theorem B14106545 : Blo 868566 14106545 := bstep (se 2 (by rfl) ⟨5289954, by rfl⟩ : syracuseStep 14106545 = 10579909) B10579909
theorem B4407371 : Blo 868566 4407371 := bstep (se 1 (by rfl) ⟨3305528, by rfl⟩ : syracuseStep 4407371 = 6611057) B6611057
theorem B7061579 : Blo 868566 7061579 := bstep (se 1 (by rfl) ⟨5296184, by rfl⟩ : syracuseStep 7061579 = 10592369) B10592369
theorem B2474135 : Blo 868566 2474135 := bstep (se 1 (by rfl) ⟨1855601, by rfl⟩ : syracuseStep 2474135 = 3711203) B3711203
theorem B1884313 : Blo 868566 1884313 := bstep (se 2 (by rfl) ⟨706617, by rfl⟩ : syracuseStep 1884313 = 1413235) B1413235
theorem B7422131 : Blo 868566 7422131 := bstep (se 1 (by rfl) ⟨5566598, by rfl⟩ : syracuseStep 7422131 = 11133197) B11133197
theorem B8372429 : Blo 868566 8372429 := bstep (se 3 (by rfl) ⟨1569830, by rfl⟩ : syracuseStep 8372429 = 3139661) B3139661
theorem B868567 : Blo 868566 868567 := bstep (se 1 (by rfl) ⟨651425, by rfl⟩ : syracuseStep 868567 = 1302851) B1302851
theorem B868587 : Blo 868566 868587 := bstep (se 1 (by rfl) ⟨651440, by rfl⟩ : syracuseStep 868587 = 1302881) B1302881
theorem B868599 : Blo 868566 868599 := bstep (se 1 (by rfl) ⟨651449, by rfl⟩ : syracuseStep 868599 = 1302899) B1302899
theorem B868619 : Blo 868566 868619 := bstep (se 1 (by rfl) ⟨651464, by rfl⟩ : syracuseStep 868619 = 1302929) B1302929
theorem B868631 : Blo 868566 868631 := bstep (se 1 (by rfl) ⟨651473, by rfl⟩ : syracuseStep 868631 = 1302947) B1302947
theorem B868651 : Blo 868566 868651 := bstep (se 1 (by rfl) ⟨651488, by rfl⟩ : syracuseStep 868651 = 1302977) B1302977
theorem B868663 : Blo 868566 868663 := bstep (se 1 (by rfl) ⟨651497, by rfl⟩ : syracuseStep 868663 = 1302995) B1302995
theorem B4702529 : Blo 868566 4702529 := bstep (se 2 (by rfl) ⟨1763448, by rfl⟩ : syracuseStep 4702529 = 3526897) B3526897
theorem B868683 : Blo 868566 868683 := bstep (se 1 (by rfl) ⟨651512, by rfl⟩ : syracuseStep 868683 = 1303025) B1303025
theorem B868695 : Blo 868566 868695 := bstep (se 1 (by rfl) ⟨651521, by rfl⟩ : syracuseStep 868695 = 1303043) B1303043
theorem B868715 : Blo 868566 868715 := bstep (se 1 (by rfl) ⟨651536, by rfl⟩ : syracuseStep 868715 = 1303073) B1303073
theorem B868727 : Blo 868566 868727 := bstep (se 1 (by rfl) ⟨651545, by rfl⟩ : syracuseStep 868727 = 1303091) B1303091
theorem B868747 : Blo 868566 868747 := bstep (se 1 (by rfl) ⟨651560, by rfl⟩ : syracuseStep 868747 = 1303121) B1303121
theorem B868759 : Blo 868566 868759 := bstep (se 1 (by rfl) ⟨651569, by rfl⟩ : syracuseStep 868759 = 1303139) B1303139
theorem B868779 : Blo 868566 868779 := bstep (se 1 (by rfl) ⟨651584, by rfl⟩ : syracuseStep 868779 = 1303169) B1303169
theorem B2933171 : Blo 868566 2933171 := bstep (se 1 (by rfl) ⟨2199878, by rfl⟩ : syracuseStep 2933171 = 4399757) B4399757
theorem B868791 : Blo 868566 868791 := bstep (se 1 (by rfl) ⟨651593, by rfl⟩ : syracuseStep 868791 = 1303187) B1303187
theorem B868811 : Blo 868566 868811 := bstep (se 1 (by rfl) ⟨651608, by rfl⟩ : syracuseStep 868811 = 1303217) B1303217
theorem B868823 : Blo 868566 868823 := bstep (se 1 (by rfl) ⟨651617, by rfl⟩ : syracuseStep 868823 = 1303235) B1303235
theorem B1655255 : Blo 868566 1655255 := bstep (se 1 (by rfl) ⟨1241441, by rfl⟩ : syracuseStep 1655255 = 2482883) B2482883
theorem B868843 : Blo 868566 868843 := bstep (se 1 (by rfl) ⟨651632, by rfl⟩ : syracuseStep 868843 = 1303265) B1303265
theorem B868855 : Blo 868566 868855 := bstep (se 1 (by rfl) ⟨651641, by rfl⟩ : syracuseStep 868855 = 1303283) B1303283
theorem B868875 : Blo 868566 868875 := bstep (se 1 (by rfl) ⟨651656, by rfl⟩ : syracuseStep 868875 = 1303313) B1303313
theorem B6603281 : Blo 868566 6603281 := bstep (se 2 (by rfl) ⟨2476230, by rfl⟩ : syracuseStep 6603281 = 4952461) B4952461
theorem B868887 : Blo 868566 868887 := bstep (se 1 (by rfl) ⟨651665, by rfl⟩ : syracuseStep 868887 = 1303331) B1303331
theorem B868907 : Blo 868566 868907 := bstep (se 1 (by rfl) ⟨651680, by rfl⟩ : syracuseStep 868907 = 1303361) B1303361
theorem B868919 : Blo 868566 868919 := bstep (se 1 (by rfl) ⟨651689, by rfl⟩ : syracuseStep 868919 = 1303379) B1303379
theorem B868939 : Blo 868566 868939 := bstep (se 1 (by rfl) ⟨651704, by rfl⟩ : syracuseStep 868939 = 1303409) B1303409
theorem B868951 : Blo 868566 868951 := bstep (se 1 (by rfl) ⟨651713, by rfl⟩ : syracuseStep 868951 = 1303427) B1303427
theorem B868971 : Blo 868566 868971 := bstep (se 1 (by rfl) ⟨651728, by rfl⟩ : syracuseStep 868971 = 1303457) B1303457
theorem B868983 : Blo 868566 868983 := bstep (se 1 (by rfl) ⟨651737, by rfl⟩ : syracuseStep 868983 = 1303475) B1303475
theorem B869003 : Blo 868566 869003 := bstep (se 1 (by rfl) ⟨651752, by rfl⟩ : syracuseStep 869003 = 1303505) B1303505
theorem B869015 : Blo 868566 869015 := bstep (se 1 (by rfl) ⟨651761, by rfl⟩ : syracuseStep 869015 = 1303523) B1303523
theorem B869035 : Blo 868566 869035 := bstep (se 1 (by rfl) ⟨651776, by rfl⟩ : syracuseStep 869035 = 1303553) B1303553
theorem B869047 : Blo 868566 869047 := bstep (se 1 (by rfl) ⟨651785, by rfl⟩ : syracuseStep 869047 = 1303571) B1303571
theorem B2933441 : Blo 868566 2933441 := bstep (se 2 (by rfl) ⟨1100040, by rfl⟩ : syracuseStep 2933441 = 2200081) B2200081
theorem B869067 : Blo 868566 869067 := bstep (se 1 (by rfl) ⟨651800, by rfl⟩ : syracuseStep 869067 = 1303601) B1303601
theorem B1393355 : Blo 868566 1393355 := bstep (se 1 (by rfl) ⟨1045016, by rfl⟩ : syracuseStep 1393355 = 2090033) B2090033
theorem B869079 : Blo 868566 869079 := bstep (se 1 (by rfl) ⟨651809, by rfl⟩ : syracuseStep 869079 = 1303619) B1303619
theorem B1393367 : Blo 868566 1393367 := bstep (se 1 (by rfl) ⟨1045025, by rfl⟩ : syracuseStep 1393367 = 2090051) B2090051
theorem B869099 : Blo 868566 869099 := bstep (se 1 (by rfl) ⟨651824, by rfl⟩ : syracuseStep 869099 = 1303649) B1303649
theorem B869111 : Blo 868566 869111 := bstep (se 1 (by rfl) ⟨651833, by rfl⟩ : syracuseStep 869111 = 1303667) B1303667
theorem B869131 : Blo 868566 869131 := bstep (se 1 (by rfl) ⟨651848, by rfl⟩ : syracuseStep 869131 = 1303697) B1303697
theorem B869143 : Blo 868566 869143 := bstep (se 1 (by rfl) ⟨651857, by rfl⟩ : syracuseStep 869143 = 1303715) B1303715
theorem B869163 : Blo 868566 869163 := bstep (se 1 (by rfl) ⟨651872, by rfl⟩ : syracuseStep 869163 = 1303745) B1303745
theorem B869175 : Blo 868566 869175 := bstep (se 1 (by rfl) ⟨651881, by rfl⟩ : syracuseStep 869175 = 1303763) B1303763
theorem B869195 : Blo 868566 869195 := bstep (se 1 (by rfl) ⟨651896, by rfl⟩ : syracuseStep 869195 = 1303793) B1303793
theorem B869207 : Blo 868566 869207 := bstep (se 1 (by rfl) ⟨651905, by rfl⟩ : syracuseStep 869207 = 1303811) B1303811
theorem B869227 : Blo 868566 869227 := bstep (se 1 (by rfl) ⟨651920, by rfl⟩ : syracuseStep 869227 = 1303841) B1303841
theorem B14140277 : Blo 868566 14140277 := bstep (se 5 (by rfl) ⟨662825, by rfl⟩ : syracuseStep 14140277 = 1325651) B1325651
theorem B869239 : Blo 868566 869239 := bstep (se 1 (by rfl) ⟨651929, by rfl⟩ : syracuseStep 869239 = 1303859) B1303859
theorem B869259 : Blo 868566 869259 := bstep (se 1 (by rfl) ⟨651944, by rfl⟩ : syracuseStep 869259 = 1303889) B1303889
theorem B869271 : Blo 868566 869271 := bstep (se 1 (by rfl) ⟨651953, by rfl⟩ : syracuseStep 869271 = 1303907) B1303907
theorem B869291 : Blo 868566 869291 := bstep (se 1 (by rfl) ⟨651968, by rfl⟩ : syracuseStep 869291 = 1303937) B1303937
theorem B869303 : Blo 868566 869303 := bstep (se 1 (by rfl) ⟨651977, by rfl⟩ : syracuseStep 869303 = 1303955) B1303955
theorem B2474945 : Blo 868566 2474945 := bstep (se 2 (by rfl) ⟨928104, by rfl⟩ : syracuseStep 2474945 = 1856209) B1856209
theorem B869323 : Blo 868566 869323 := bstep (se 1 (by rfl) ⟨651992, by rfl⟩ : syracuseStep 869323 = 1303985) B1303985
theorem B869335 : Blo 868566 869335 := bstep (se 1 (by rfl) ⟨652001, by rfl⟩ : syracuseStep 869335 = 1304003) B1304003
theorem B869355 : Blo 868566 869355 := bstep (se 1 (by rfl) ⟨652016, by rfl⟩ : syracuseStep 869355 = 1304033) B1304033
theorem B1655795 : Blo 868566 1655795 := bstep (se 1 (by rfl) ⟨1241846, by rfl⟩ : syracuseStep 1655795 = 2483693) B2483693
theorem B869367 : Blo 868566 869367 := bstep (se 1 (by rfl) ⟨652025, by rfl⟩ : syracuseStep 869367 = 1304051) B1304051
theorem B869387 : Blo 868566 869387 := bstep (se 1 (by rfl) ⟨652040, by rfl⟩ : syracuseStep 869387 = 1304081) B1304081
theorem B869399 : Blo 868566 869399 := bstep (se 1 (by rfl) ⟨652049, by rfl⟩ : syracuseStep 869399 = 1304099) B1304099
theorem B25150499 : Blo 868566 25150499 := bstep (se 1 (by rfl) ⟨18862874, by rfl⟩ : syracuseStep 25150499 = 37725749) B37725749
theorem B869419 : Blo 868566 869419 := bstep (se 1 (by rfl) ⟨652064, by rfl⟩ : syracuseStep 869419 = 1304129) B1304129
theorem B869431 : Blo 868566 869431 := bstep (se 1 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 869431 = 1304147) B1304147
theorem B869451 : Blo 868566 869451 := bstep (se 1 (by rfl) ⟨652088, by rfl⟩ : syracuseStep 869451 = 1304177) B1304177
theorem B869463 : Blo 868566 869463 := bstep (se 1 (by rfl) ⟨652097, by rfl⟩ : syracuseStep 869463 = 1304195) B1304195
theorem B1590359 : Blo 868566 1590359 := bstep (se 1 (by rfl) ⟨1192769, by rfl⟩ : syracuseStep 1590359 = 2385539) B2385539
theorem B869483 : Blo 868566 869483 := bstep (se 1 (by rfl) ⟨652112, by rfl⟩ : syracuseStep 869483 = 1304225) B1304225
theorem B869495 : Blo 868566 869495 := bstep (se 1 (by rfl) ⟨652121, by rfl⟩ : syracuseStep 869495 = 1304243) B1304243
theorem B869515 : Blo 868566 869515 := bstep (se 1 (by rfl) ⟨652136, by rfl⟩ : syracuseStep 869515 = 1304273) B1304273
theorem B869527 : Blo 868566 869527 := bstep (se 1 (by rfl) ⟨652145, by rfl⟩ : syracuseStep 869527 = 1304291) B1304291
theorem B869547 : Blo 868566 869547 := bstep (se 1 (by rfl) ⟨652160, by rfl⟩ : syracuseStep 869547 = 1304321) B1304321
theorem B869559 : Blo 868566 869559 := bstep (se 1 (by rfl) ⟨652169, by rfl⟩ : syracuseStep 869559 = 1304339) B1304339
theorem B869579 : Blo 868566 869579 := bstep (se 1 (by rfl) ⟨652184, by rfl⟩ : syracuseStep 869579 = 1304369) B1304369
theorem B869591 : Blo 868566 869591 := bstep (se 1 (by rfl) ⟨652193, by rfl⟩ : syracuseStep 869591 = 1304387) B1304387
theorem B2933981 : Blo 868566 2933981 := bstep (se 3 (by rfl) ⟨550121, by rfl⟩ : syracuseStep 2933981 = 1100243) B1100243
theorem B869611 : Blo 868566 869611 := bstep (se 1 (by rfl) ⟨652208, by rfl⟩ : syracuseStep 869611 = 1304417) B1304417
theorem B869623 : Blo 868566 869623 := bstep (se 1 (by rfl) ⟨652217, by rfl⟩ : syracuseStep 869623 = 1304435) B1304435
theorem B869643 : Blo 868566 869643 := bstep (se 1 (by rfl) ⟨652232, by rfl⟩ : syracuseStep 869643 = 1304465) B1304465
theorem B869655 : Blo 868566 869655 := bstep (se 1 (by rfl) ⟨652241, by rfl⟩ : syracuseStep 869655 = 1304483) B1304483
theorem B869675 : Blo 868566 869675 := bstep (se 1 (by rfl) ⟨652256, by rfl⟩ : syracuseStep 869675 = 1304513) B1304513
theorem B9684269 : Blo 868566 9684269 := bstep (se 3 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 9684269 = 3631601) B3631601
theorem B869687 : Blo 868566 869687 := bstep (se 1 (by rfl) ⟨652265, by rfl⟩ : syracuseStep 869687 = 1304531) B1304531
theorem B869707 : Blo 868566 869707 := bstep (se 1 (by rfl) ⟨652280, by rfl⟩ : syracuseStep 869707 = 1304561) B1304561
theorem B869719 : Blo 868566 869719 := bstep (se 1 (by rfl) ⟨652289, by rfl⟩ : syracuseStep 869719 = 1304579) B1304579
theorem B869739 : Blo 868566 869739 := bstep (se 1 (by rfl) ⟨652304, by rfl⟩ : syracuseStep 869739 = 1304609) B1304609
theorem B869751 : Blo 868566 869751 := bstep (se 1 (by rfl) ⟨652313, by rfl⟩ : syracuseStep 869751 = 1304627) B1304627
theorem B869771 : Blo 868566 869771 := bstep (se 1 (by rfl) ⟨652328, by rfl⟩ : syracuseStep 869771 = 1304657) B1304657
theorem B1394059 : Blo 868566 1394059 := bstep (se 1 (by rfl) ⟨1045544, by rfl⟩ : syracuseStep 1394059 = 2091089) B2091089
theorem B869783 : Blo 868566 869783 := bstep (se 1 (by rfl) ⟨652337, by rfl⟩ : syracuseStep 869783 = 1304675) B1304675
theorem B869803 : Blo 868566 869803 := bstep (se 1 (by rfl) ⟨652352, by rfl⟩ : syracuseStep 869803 = 1304705) B1304705
theorem B869815 : Blo 868566 869815 := bstep (se 1 (by rfl) ⟨652361, by rfl⟩ : syracuseStep 869815 = 1304723) B1304723
theorem B869835 : Blo 868566 869835 := bstep (se 1 (by rfl) ⟨652376, by rfl⟩ : syracuseStep 869835 = 1304753) B1304753
theorem B869847 : Blo 868566 869847 := bstep (se 1 (by rfl) ⟨652385, by rfl⟩ : syracuseStep 869847 = 1304771) B1304771
theorem B1656281 : Blo 868566 1656281 := bstep (se 2 (by rfl) ⟨621105, by rfl⟩ : syracuseStep 1656281 = 1242211) B1242211
theorem B869867 : Blo 868566 869867 := bstep (se 1 (by rfl) ⟨652400, by rfl⟩ : syracuseStep 869867 = 1304801) B1304801
theorem B869879 : Blo 868566 869879 := bstep (se 1 (by rfl) ⟨652409, by rfl⟩ : syracuseStep 869879 = 1304819) B1304819
theorem B869899 : Blo 868566 869899 := bstep (se 1 (by rfl) ⟨652424, by rfl⟩ : syracuseStep 869899 = 1304849) B1304849
theorem B869911 : Blo 868566 869911 := bstep (se 1 (by rfl) ⟨652433, by rfl⟩ : syracuseStep 869911 = 1304867) B1304867
theorem B869931 : Blo 868566 869931 := bstep (se 1 (by rfl) ⟨652448, by rfl⟩ : syracuseStep 869931 = 1304897) B1304897
theorem B3720755 : Blo 868566 3720755 := bstep (se 1 (by rfl) ⟨2790566, by rfl⟩ : syracuseStep 3720755 = 5581133) B5581133
theorem B869943 : Blo 868566 869943 := bstep (se 1 (by rfl) ⟨652457, by rfl⟩ : syracuseStep 869943 = 1304915) B1304915
theorem B869963 : Blo 868566 869963 := bstep (se 1 (by rfl) ⟨652472, by rfl⟩ : syracuseStep 869963 = 1304945) B1304945
theorem B869975 : Blo 868566 869975 := bstep (se 1 (by rfl) ⟨652481, by rfl⟩ : syracuseStep 869975 = 1304963) B1304963
theorem B869995 : Blo 868566 869995 := bstep (se 1 (by rfl) ⟨652496, by rfl⟩ : syracuseStep 869995 = 1304993) B1304993
theorem B870007 : Blo 868566 870007 := bstep (se 1 (by rfl) ⟨652505, by rfl⟩ : syracuseStep 870007 = 1305011) B1305011
theorem B870027 : Blo 868566 870027 := bstep (se 1 (by rfl) ⟨652520, by rfl⟩ : syracuseStep 870027 = 1305041) B1305041
theorem B870039 : Blo 868566 870039 := bstep (se 1 (by rfl) ⟨652529, by rfl⟩ : syracuseStep 870039 = 1305059) B1305059
theorem B1394329 : Blo 868566 1394329 := bstep (se 2 (by rfl) ⟨522873, by rfl⟩ : syracuseStep 1394329 = 1045747) B1045747
theorem B870059 : Blo 868566 870059 := bstep (se 1 (by rfl) ⟨652544, by rfl⟩ : syracuseStep 870059 = 1305089) B1305089
theorem B870071 : Blo 868566 870071 := bstep (se 1 (by rfl) ⟨652553, by rfl⟩ : syracuseStep 870071 = 1305107) B1305107
theorem B870091 : Blo 868566 870091 := bstep (se 1 (by rfl) ⟨652568, by rfl⟩ : syracuseStep 870091 = 1305137) B1305137
theorem B3720907 : Blo 868566 3720907 := bstep (se 1 (by rfl) ⟨2790680, by rfl⟩ : syracuseStep 3720907 = 5581361) B5581361
theorem B870103 : Blo 868566 870103 := bstep (se 1 (by rfl) ⟨652577, by rfl⟩ : syracuseStep 870103 = 1305155) B1305155
theorem B870123 : Blo 868566 870123 := bstep (se 1 (by rfl) ⟨652592, by rfl⟩ : syracuseStep 870123 = 1305185) B1305185
theorem B870135 : Blo 868566 870135 := bstep (se 1 (by rfl) ⟨652601, by rfl⟩ : syracuseStep 870135 = 1305203) B1305203
theorem B870155 : Blo 868566 870155 := bstep (se 1 (by rfl) ⟨652616, by rfl⟩ : syracuseStep 870155 = 1305233) B1305233
theorem B3720977 : Blo 868566 3720977 := bstep (se 2 (by rfl) ⟨1395366, by rfl⟩ : syracuseStep 3720977 = 2790733) B2790733
theorem B870167 : Blo 868566 870167 := bstep (se 1 (by rfl) ⟨652625, by rfl⟩ : syracuseStep 870167 = 1305251) B1305251
theorem B870187 : Blo 868566 870187 := bstep (se 1 (by rfl) ⟨652640, by rfl⟩ : syracuseStep 870187 = 1305281) B1305281
theorem B870199 : Blo 868566 870199 := bstep (se 1 (by rfl) ⟨652649, by rfl⟩ : syracuseStep 870199 = 1305299) B1305299
theorem B4409153 : Blo 868566 4409153 := bstep (se 2 (by rfl) ⟨1653432, by rfl⟩ : syracuseStep 4409153 = 3306865) B3306865
theorem B1099595 : Blo 868566 1099595 := bstep (se 1 (by rfl) ⟨824696, by rfl⟩ : syracuseStep 1099595 = 1649393) B1649393
theorem B870219 : Blo 868566 870219 := bstep (se 1 (by rfl) ⟨652664, by rfl⟩ : syracuseStep 870219 = 1305329) B1305329
theorem B870231 : Blo 868566 870231 := bstep (se 1 (by rfl) ⟨652673, by rfl⟩ : syracuseStep 870231 = 1305347) B1305347
theorem B870251 : Blo 868566 870251 := bstep (se 1 (by rfl) ⟨652688, by rfl⟩ : syracuseStep 870251 = 1305377) B1305377
theorem B870263 : Blo 868566 870263 := bstep (se 1 (by rfl) ⟨652697, by rfl⟩ : syracuseStep 870263 = 1305395) B1305395
theorem B870283 : Blo 868566 870283 := bstep (se 1 (by rfl) ⟨652712, by rfl⟩ : syracuseStep 870283 = 1305425) B1305425
theorem B870295 : Blo 868566 870295 := bstep (se 1 (by rfl) ⟨652721, by rfl⟩ : syracuseStep 870295 = 1305443) B1305443
theorem B1394585 : Blo 868566 1394585 := bstep (se 2 (by rfl) ⟨522969, by rfl⟩ : syracuseStep 1394585 = 1045939) B1045939
theorem B870315 : Blo 868566 870315 := bstep (se 1 (by rfl) ⟨652736, by rfl⟩ : syracuseStep 870315 = 1305473) B1305473
theorem B870327 : Blo 868566 870327 := bstep (se 1 (by rfl) ⟨652745, by rfl⟩ : syracuseStep 870327 = 1305491) B1305491
theorem B870347 : Blo 868566 870347 := bstep (se 1 (by rfl) ⟨652760, by rfl⟩ : syracuseStep 870347 = 1305521) B1305521
theorem B870359 : Blo 868566 870359 := bstep (se 1 (by rfl) ⟨652769, by rfl⟩ : syracuseStep 870359 = 1305539) B1305539
theorem B870379 : Blo 868566 870379 := bstep (se 1 (by rfl) ⟨652784, by rfl⟩ : syracuseStep 870379 = 1305569) B1305569
theorem B870391 : Blo 868566 870391 := bstep (se 1 (by rfl) ⟨652793, by rfl⟩ : syracuseStep 870391 = 1305587) B1305587
theorem B870411 : Blo 868566 870411 := bstep (se 1 (by rfl) ⟨652808, by rfl⟩ : syracuseStep 870411 = 1305617) B1305617
theorem B870423 : Blo 868566 870423 := bstep (se 1 (by rfl) ⟨652817, by rfl⟩ : syracuseStep 870423 = 1305635) B1305635
theorem B870443 : Blo 868566 870443 := bstep (se 1 (by rfl) ⟨652832, by rfl⟩ : syracuseStep 870443 = 1305665) B1305665
theorem B7424045 : Blo 868566 7424045 := bstep (se 3 (by rfl) ⟨1392008, by rfl⟩ : syracuseStep 7424045 = 2784017) B2784017
theorem B870455 : Blo 868566 870455 := bstep (se 1 (by rfl) ⟨652841, by rfl⟩ : syracuseStep 870455 = 1305683) B1305683
theorem B870475 : Blo 868566 870475 := bstep (se 1 (by rfl) ⟨652856, by rfl⟩ : syracuseStep 870475 = 1305713) B1305713
theorem B870487 : Blo 868566 870487 := bstep (se 1 (by rfl) ⟨652865, by rfl⟩ : syracuseStep 870487 = 1305731) B1305731
theorem B870507 : Blo 868566 870507 := bstep (se 1 (by rfl) ⟨652880, by rfl⟩ : syracuseStep 870507 = 1305761) B1305761
theorem B870519 : Blo 868566 870519 := bstep (se 1 (by rfl) ⟨652889, by rfl⟩ : syracuseStep 870519 = 1305779) B1305779
theorem B4245635 : Blo 868566 4245635 := bstep (se 1 (by rfl) ⟨3184226, by rfl⟩ : syracuseStep 4245635 = 6368453) B6368453
theorem B870539 : Blo 868566 870539 := bstep (se 1 (by rfl) ⟨652904, by rfl⟩ : syracuseStep 870539 = 1305809) B1305809
theorem B870551 : Blo 868566 870551 := bstep (se 1 (by rfl) ⟨652913, by rfl⟩ : syracuseStep 870551 = 1305827) B1305827
theorem B870571 : Blo 868566 870571 := bstep (se 1 (by rfl) ⟨652928, by rfl⟩ : syracuseStep 870571 = 1305857) B1305857
theorem B870583 : Blo 868566 870583 := bstep (se 1 (by rfl) ⟨652937, by rfl⟩ : syracuseStep 870583 = 1305875) B1305875
theorem B870603 : Blo 868566 870603 := bstep (se 1 (by rfl) ⟨652952, by rfl⟩ : syracuseStep 870603 = 1305905) B1305905
theorem B870615 : Blo 868566 870615 := bstep (se 1 (by rfl) ⟨652961, by rfl⟩ : syracuseStep 870615 = 1305923) B1305923
theorem B870635 : Blo 868566 870635 := bstep (se 1 (by rfl) ⟨652976, by rfl⟩ : syracuseStep 870635 = 1305953) B1305953
theorem B870647 : Blo 868566 870647 := bstep (se 1 (by rfl) ⟨652985, by rfl⟩ : syracuseStep 870647 = 1305971) B1305971
theorem B870667 : Blo 868566 870667 := bstep (se 1 (by rfl) ⟨653000, by rfl⟩ : syracuseStep 870667 = 1306001) B1306001
theorem B870679 : Blo 868566 870679 := bstep (se 1 (by rfl) ⟨653009, by rfl⟩ : syracuseStep 870679 = 1306019) B1306019
theorem B870699 : Blo 868566 870699 := bstep (se 1 (by rfl) ⟨653024, by rfl⟩ : syracuseStep 870699 = 1306049) B1306049
theorem B870711 : Blo 868566 870711 := bstep (se 1 (by rfl) ⟨653033, by rfl⟩ : syracuseStep 870711 = 1306067) B1306067
theorem B2935115 : Blo 868566 2935115 := bstep (se 1 (by rfl) ⟨2201336, by rfl⟩ : syracuseStep 2935115 = 4402673) B4402673
theorem B4704587 : Blo 868566 4704587 := bstep (se 1 (by rfl) ⟨3528440, by rfl⟩ : syracuseStep 4704587 = 7056881) B7056881
theorem B870731 : Blo 868566 870731 := bstep (se 1 (by rfl) ⟨653048, by rfl⟩ : syracuseStep 870731 = 1306097) B1306097
theorem B870743 : Blo 868566 870743 := bstep (se 1 (by rfl) ⟨653057, by rfl⟩ : syracuseStep 870743 = 1306115) B1306115
theorem B870763 : Blo 868566 870763 := bstep (se 1 (by rfl) ⟨653072, by rfl⟩ : syracuseStep 870763 = 1306145) B1306145
theorem B870775 : Blo 868566 870775 := bstep (se 1 (by rfl) ⟨653081, by rfl⟩ : syracuseStep 870775 = 1306163) B1306163
theorem B870795 : Blo 868566 870795 := bstep (se 1 (by rfl) ⟨653096, by rfl⟩ : syracuseStep 870795 = 1306193) B1306193
theorem B870807 : Blo 868566 870807 := bstep (se 1 (by rfl) ⟨653105, by rfl⟩ : syracuseStep 870807 = 1306211) B1306211
theorem B870827 : Blo 868566 870827 := bstep (se 1 (by rfl) ⟨653120, by rfl⟩ : syracuseStep 870827 = 1306241) B1306241
theorem B870839 : Blo 868566 870839 := bstep (se 1 (by rfl) ⟨653129, by rfl⟩ : syracuseStep 870839 = 1306259) B1306259
theorem B870859 : Blo 868566 870859 := bstep (se 1 (by rfl) ⟨653144, by rfl⟩ : syracuseStep 870859 = 1306289) B1306289
theorem B870871 : Blo 868566 870871 := bstep (se 1 (by rfl) ⟨653153, by rfl⟩ : syracuseStep 870871 = 1306307) B1306307
theorem B870891 : Blo 868566 870891 := bstep (se 1 (by rfl) ⟨653168, by rfl⟩ : syracuseStep 870891 = 1306337) B1306337
theorem B870903 : Blo 868566 870903 := bstep (se 1 (by rfl) ⟨653177, by rfl⟩ : syracuseStep 870903 = 1306355) B1306355
theorem B1100299 : Blo 868566 1100299 := bstep (se 1 (by rfl) ⟨825224, by rfl⟩ : syracuseStep 1100299 = 1650449) B1650449
theorem B870923 : Blo 868566 870923 := bstep (se 1 (by rfl) ⟨653192, by rfl⟩ : syracuseStep 870923 = 1306385) B1306385
theorem B15092237 : Blo 868566 15092237 := bstep (se 3 (by rfl) ⟨2829794, by rfl⟩ : syracuseStep 15092237 = 5659589) B5659589
theorem B870935 : Blo 868566 870935 := bstep (se 1 (by rfl) ⟨653201, by rfl⟩ : syracuseStep 870935 = 1306403) B1306403
theorem B870955 : Blo 868566 870955 := bstep (se 1 (by rfl) ⟨653216, by rfl⟩ : syracuseStep 870955 = 1306433) B1306433
theorem B2476595 : Blo 868566 2476595 := bstep (se 1 (by rfl) ⟨1857446, by rfl⟩ : syracuseStep 2476595 = 3714893) B3714893
theorem B870967 : Blo 868566 870967 := bstep (se 1 (by rfl) ⟨653225, by rfl⟩ : syracuseStep 870967 = 1306451) B1306451
theorem B2476619 : Blo 868566 2476619 := bstep (se 1 (by rfl) ⟨1857464, by rfl⟩ : syracuseStep 2476619 = 3714929) B3714929
theorem B870987 : Blo 868566 870987 := bstep (se 1 (by rfl) ⟨653240, by rfl⟩ : syracuseStep 870987 = 1306481) B1306481
theorem B870999 : Blo 868566 870999 := bstep (se 1 (by rfl) ⟨653249, by rfl⟩ : syracuseStep 870999 = 1306499) B1306499
theorem B1886807 : Blo 868566 1886807 := bstep (se 1 (by rfl) ⟨1415105, by rfl⟩ : syracuseStep 1886807 = 2830211) B2830211
theorem B2935385 : Blo 868566 2935385 := bstep (se 2 (by rfl) ⟨1100769, by rfl⟩ : syracuseStep 2935385 = 2201539) B2201539
theorem B1395289 : Blo 868566 1395289 := bstep (se 2 (by rfl) ⟨523233, by rfl⟩ : syracuseStep 1395289 = 1046467) B1046467
theorem B871019 : Blo 868566 871019 := bstep (se 1 (by rfl) ⟨653264, by rfl⟩ : syracuseStep 871019 = 1306529) B1306529
theorem B871031 : Blo 868566 871031 := bstep (se 1 (by rfl) ⟨653273, by rfl⟩ : syracuseStep 871031 = 1306547) B1306547
theorem B871051 : Blo 868566 871051 := bstep (se 1 (by rfl) ⟨653288, by rfl⟩ : syracuseStep 871051 = 1306577) B1306577
theorem B871063 : Blo 868566 871063 := bstep (se 1 (by rfl) ⟨653297, by rfl⟩ : syracuseStep 871063 = 1306595) B1306595
theorem B871083 : Blo 868566 871083 := bstep (se 1 (by rfl) ⟨653312, by rfl⟩ : syracuseStep 871083 = 1306625) B1306625
theorem B871095 : Blo 868566 871095 := bstep (se 1 (by rfl) ⟨653321, by rfl⟩ : syracuseStep 871095 = 1306643) B1306643
theorem B871115 : Blo 868566 871115 := bstep (se 1 (by rfl) ⟨653336, by rfl⟩ : syracuseStep 871115 = 1306673) B1306673
theorem B871127 : Blo 868566 871127 := bstep (se 1 (by rfl) ⟨653345, by rfl⟩ : syracuseStep 871127 = 1306691) B1306691
theorem B7424729 : Blo 868566 7424729 := bstep (se 2 (by rfl) ⟨2784273, by rfl⟩ : syracuseStep 7424729 = 5568547) B5568547
theorem B871147 : Blo 868566 871147 := bstep (se 1 (by rfl) ⟨653360, by rfl⟩ : syracuseStep 871147 = 1306721) B1306721
theorem B871159 : Blo 868566 871159 := bstep (se 1 (by rfl) ⟨653369, by rfl⟩ : syracuseStep 871159 = 1306739) B1306739
theorem B871179 : Blo 868566 871179 := bstep (se 1 (by rfl) ⟨653384, by rfl⟩ : syracuseStep 871179 = 1306769) B1306769
theorem B1100567 : Blo 868566 1100567 := bstep (se 1 (by rfl) ⟨825425, by rfl⟩ : syracuseStep 1100567 = 1650851) B1650851
theorem B871191 : Blo 868566 871191 := bstep (se 1 (by rfl) ⟨653393, by rfl⟩ : syracuseStep 871191 = 1306787) B1306787
theorem B871211 : Blo 868566 871211 := bstep (se 1 (by rfl) ⟨653408, by rfl⟩ : syracuseStep 871211 = 1306817) B1306817
theorem B871223 : Blo 868566 871223 := bstep (se 1 (by rfl) ⟨653417, by rfl⟩ : syracuseStep 871223 = 1306835) B1306835
theorem B871243 : Blo 868566 871243 := bstep (se 1 (by rfl) ⟨653432, by rfl⟩ : syracuseStep 871243 = 1306865) B1306865
theorem B871255 : Blo 868566 871255 := bstep (se 1 (by rfl) ⟨653441, by rfl⟩ : syracuseStep 871255 = 1306883) B1306883
theorem B871275 : Blo 868566 871275 := bstep (se 1 (by rfl) ⟨653456, by rfl⟩ : syracuseStep 871275 = 1306913) B1306913
theorem B871287 : Blo 868566 871287 := bstep (se 1 (by rfl) ⟨653465, by rfl⟩ : syracuseStep 871287 = 1306931) B1306931
theorem B871307 : Blo 868566 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B871319 : Blo 868566 871319 := bstep (se 1 (by rfl) ⟨653489, by rfl⟩ : syracuseStep 871319 = 1306979) B1306979
theorem B871339 : Blo 868566 871339 := bstep (se 1 (by rfl) ⟨653504, by rfl⟩ : syracuseStep 871339 = 1307009) B1307009
theorem B871351 : Blo 868566 871351 := bstep (se 1 (by rfl) ⟨653513, by rfl⟩ : syracuseStep 871351 = 1307027) B1307027
theorem B871371 : Blo 868566 871371 := bstep (se 1 (by rfl) ⟨653528, by rfl⟩ : syracuseStep 871371 = 1307057) B1307057
theorem B871383 : Blo 868566 871383 := bstep (se 1 (by rfl) ⟨653537, by rfl⟩ : syracuseStep 871383 = 1307075) B1307075
theorem B871403 : Blo 868566 871403 := bstep (se 1 (by rfl) ⟨653552, by rfl⟩ : syracuseStep 871403 = 1307105) B1307105
theorem B871415 : Blo 868566 871415 := bstep (se 1 (by rfl) ⟨653561, by rfl⟩ : syracuseStep 871415 = 1307123) B1307123
theorem B871435 : Blo 868566 871435 := bstep (se 1 (by rfl) ⟨653576, by rfl⟩ : syracuseStep 871435 = 1307153) B1307153
theorem B871447 : Blo 868566 871447 := bstep (se 1 (by rfl) ⟨653585, by rfl⟩ : syracuseStep 871447 = 1307171) B1307171
theorem B1592345 : Blo 868566 1592345 := bstep (se 2 (by rfl) ⟨597129, by rfl⟩ : syracuseStep 1592345 = 1194259) B1194259
theorem B871467 : Blo 868566 871467 := bstep (se 1 (by rfl) ⟨653600, by rfl⟩ : syracuseStep 871467 = 1307201) B1307201
theorem B871479 : Blo 868566 871479 := bstep (se 1 (by rfl) ⟨653609, by rfl⟩ : syracuseStep 871479 = 1307219) B1307219
theorem B871499 : Blo 868566 871499 := bstep (se 1 (by rfl) ⟨653624, by rfl⟩ : syracuseStep 871499 = 1307249) B1307249
theorem B871511 : Blo 868566 871511 := bstep (se 1 (by rfl) ⟨653633, by rfl⟩ : syracuseStep 871511 = 1307267) B1307267
theorem B871531 : Blo 868566 871531 := bstep (se 1 (by rfl) ⟨653648, by rfl⟩ : syracuseStep 871531 = 1307297) B1307297
theorem B871543 : Blo 868566 871543 := bstep (se 1 (by rfl) ⟨653657, by rfl⟩ : syracuseStep 871543 = 1307315) B1307315
theorem B871563 : Blo 868566 871563 := bstep (se 1 (by rfl) ⟨653672, by rfl⟩ : syracuseStep 871563 = 1307345) B1307345
theorem B3394705 : Blo 868566 3394705 := bstep (se 2 (by rfl) ⟨1273014, by rfl⟩ : syracuseStep 3394705 = 2546029) B2546029
theorem B871575 : Blo 868566 871575 := bstep (se 1 (by rfl) ⟨653681, by rfl⟩ : syracuseStep 871575 = 1307363) B1307363
theorem B871595 : Blo 868566 871595 := bstep (se 1 (by rfl) ⟨653696, by rfl⟩ : syracuseStep 871595 = 1307393) B1307393
theorem B871607 : Blo 868566 871607 := bstep (se 1 (by rfl) ⟨653705, by rfl⟩ : syracuseStep 871607 = 1307411) B1307411
theorem B1789121 : Blo 868566 1789121 := bstep (se 2 (by rfl) ⟨670920, by rfl⟩ : syracuseStep 1789121 = 1341841) B1341841
theorem B871627 : Blo 868566 871627 := bstep (se 1 (by rfl) ⟨653720, by rfl⟩ : syracuseStep 871627 = 1307441) B1307441
theorem B8473805 : Blo 868566 8473805 := bstep (se 3 (by rfl) ⟨1588838, by rfl⟩ : syracuseStep 8473805 = 3177677) B3177677
theorem B871639 : Blo 868566 871639 := bstep (se 1 (by rfl) ⟨653729, by rfl⟩ : syracuseStep 871639 = 1307459) B1307459
theorem B871659 : Blo 868566 871659 := bstep (se 1 (by rfl) ⟨653744, by rfl⟩ : syracuseStep 871659 = 1307489) B1307489
theorem B871671 : Blo 868566 871671 := bstep (se 1 (by rfl) ⟨653753, by rfl⟩ : syracuseStep 871671 = 1307507) B1307507
theorem B871691 : Blo 868566 871691 := bstep (se 1 (by rfl) ⟨653768, by rfl⟩ : syracuseStep 871691 = 1307537) B1307537
theorem B2936087 : Blo 868566 2936087 := bstep (se 1 (by rfl) ⟨2202065, by rfl⟩ : syracuseStep 2936087 = 4404131) B4404131
theorem B871703 : Blo 868566 871703 := bstep (se 1 (by rfl) ⟨653777, by rfl⟩ : syracuseStep 871703 = 1307555) B1307555
theorem B871723 : Blo 868566 871723 := bstep (se 1 (by rfl) ⟨653792, by rfl⟩ : syracuseStep 871723 = 1307585) B1307585
theorem B871735 : Blo 868566 871735 := bstep (se 1 (by rfl) ⟨653801, by rfl⟩ : syracuseStep 871735 = 1307603) B1307603
theorem B871755 : Blo 868566 871755 := bstep (se 1 (by rfl) ⟨653816, by rfl⟩ : syracuseStep 871755 = 1307633) B1307633
theorem B871767 : Blo 868566 871767 := bstep (se 1 (by rfl) ⟨653825, by rfl⟩ : syracuseStep 871767 = 1307651) B1307651
theorem B2477405 : Blo 868566 2477405 := bstep (se 3 (by rfl) ⟨464513, by rfl⟩ : syracuseStep 2477405 = 929027) B929027
theorem B871787 : Blo 868566 871787 := bstep (se 1 (by rfl) ⟨653840, by rfl⟩ : syracuseStep 871787 = 1307681) B1307681
theorem B871799 : Blo 868566 871799 := bstep (se 1 (by rfl) ⟨653849, by rfl⟩ : syracuseStep 871799 = 1307699) B1307699
theorem B871819 : Blo 868566 871819 := bstep (se 1 (by rfl) ⟨653864, by rfl⟩ : syracuseStep 871819 = 1307729) B1307729
theorem B871831 : Blo 868566 871831 := bstep (se 1 (by rfl) ⟨653873, by rfl⟩ : syracuseStep 871831 = 1307747) B1307747
theorem B871851 : Blo 868566 871851 := bstep (se 1 (by rfl) ⟨653888, by rfl⟩ : syracuseStep 871851 = 1307777) B1307777
theorem B3722669 : Blo 868566 3722669 := bstep (se 3 (by rfl) ⟨698000, by rfl⟩ : syracuseStep 3722669 = 1396001) B1396001
theorem B871863 : Blo 868566 871863 := bstep (se 1 (by rfl) ⟨653897, by rfl⟩ : syracuseStep 871863 = 1307795) B1307795
theorem B871883 : Blo 868566 871883 := bstep (se 1 (by rfl) ⟨653912, by rfl⟩ : syracuseStep 871883 = 1307825) B1307825
theorem B1101271 : Blo 868566 1101271 := bstep (se 1 (by rfl) ⟨825953, by rfl⟩ : syracuseStep 1101271 = 1651907) B1651907
theorem B871895 : Blo 868566 871895 := bstep (se 1 (by rfl) ⟨653921, by rfl⟩ : syracuseStep 871895 = 1307843) B1307843
theorem B871915 : Blo 868566 871915 := bstep (se 1 (by rfl) ⟨653936, by rfl⟩ : syracuseStep 871915 = 1307873) B1307873
theorem B871927 : Blo 868566 871927 := bstep (se 1 (by rfl) ⟨653945, by rfl⟩ : syracuseStep 871927 = 1307891) B1307891
theorem B871947 : Blo 868566 871947 := bstep (se 1 (by rfl) ⟨653960, by rfl⟩ : syracuseStep 871947 = 1307921) B1307921
theorem B871959 : Blo 868566 871959 := bstep (se 1 (by rfl) ⟨653969, by rfl⟩ : syracuseStep 871959 = 1307939) B1307939
theorem B871979 : Blo 868566 871979 := bstep (se 1 (by rfl) ⟨653984, by rfl⟩ : syracuseStep 871979 = 1307969) B1307969
theorem B871991 : Blo 868566 871991 := bstep (se 1 (by rfl) ⟨653993, by rfl⟩ : syracuseStep 871991 = 1307987) B1307987
theorem B872011 : Blo 868566 872011 := bstep (se 1 (by rfl) ⟨654008, by rfl⟩ : syracuseStep 872011 = 1308017) B1308017
theorem B872023 : Blo 868566 872023 := bstep (se 1 (by rfl) ⟨654017, by rfl⟩ : syracuseStep 872023 = 1308035) B1308035
theorem B872043 : Blo 868566 872043 := bstep (se 1 (by rfl) ⟨654032, by rfl⟩ : syracuseStep 872043 = 1308065) B1308065
theorem B872055 : Blo 868566 872055 := bstep (se 1 (by rfl) ⟨654041, by rfl⟩ : syracuseStep 872055 = 1308083) B1308083
theorem B872075 : Blo 868566 872075 := bstep (se 1 (by rfl) ⟨654056, by rfl⟩ : syracuseStep 872075 = 1308113) B1308113
theorem B872087 : Blo 868566 872087 := bstep (se 1 (by rfl) ⟨654065, by rfl⟩ : syracuseStep 872087 = 1308131) B1308131
theorem B872107 : Blo 868566 872107 := bstep (se 1 (by rfl) ⟨654080, by rfl⟩ : syracuseStep 872107 = 1308161) B1308161
theorem B872119 : Blo 868566 872119 := bstep (se 1 (by rfl) ⟨654089, by rfl⟩ : syracuseStep 872119 = 1308179) B1308179
theorem B872139 : Blo 868566 872139 := bstep (se 1 (by rfl) ⟨654104, by rfl⟩ : syracuseStep 872139 = 1308209) B1308209
theorem B872151 : Blo 868566 872151 := bstep (se 1 (by rfl) ⟨654113, by rfl⟩ : syracuseStep 872151 = 1308227) B1308227
theorem B4411097 : Blo 868566 4411097 := bstep (se 2 (by rfl) ⟨1654161, by rfl⟩ : syracuseStep 4411097 = 3308323) B3308323
theorem B872171 : Blo 868566 872171 := bstep (se 1 (by rfl) ⟨654128, by rfl⟩ : syracuseStep 872171 = 1308257) B1308257
theorem B872183 : Blo 868566 872183 := bstep (se 1 (by rfl) ⟨654137, by rfl⟩ : syracuseStep 872183 = 1308275) B1308275
theorem B872203 : Blo 868566 872203 := bstep (se 1 (by rfl) ⟨654152, by rfl⟩ : syracuseStep 872203 = 1308305) B1308305
theorem B872215 : Blo 868566 872215 := bstep (se 1 (by rfl) ⟨654161, by rfl⟩ : syracuseStep 872215 = 1308323) B1308323
theorem B872235 : Blo 868566 872235 := bstep (se 1 (by rfl) ⟨654176, by rfl⟩ : syracuseStep 872235 = 1308353) B1308353
theorem B2936627 : Blo 868566 2936627 := bstep (se 1 (by rfl) ⟨2202470, by rfl⟩ : syracuseStep 2936627 = 4404941) B4404941
theorem B872247 : Blo 868566 872247 := bstep (se 1 (by rfl) ⟨654185, by rfl⟩ : syracuseStep 872247 = 1308371) B1308371
theorem B872267 : Blo 868566 872267 := bstep (se 1 (by rfl) ⟨654200, by rfl⟩ : syracuseStep 872267 = 1308401) B1308401
theorem B872279 : Blo 868566 872279 := bstep (se 1 (by rfl) ⟨654209, by rfl⟩ : syracuseStep 872279 = 1308419) B1308419
theorem B872299 : Blo 868566 872299 := bstep (se 1 (by rfl) ⟨654224, by rfl⟩ : syracuseStep 872299 = 1308449) B1308449
theorem B872311 : Blo 868566 872311 := bstep (se 1 (by rfl) ⟨654233, by rfl⟩ : syracuseStep 872311 = 1308467) B1308467
theorem B872331 : Blo 868566 872331 := bstep (se 1 (by rfl) ⟨654248, by rfl⟩ : syracuseStep 872331 = 1308497) B1308497
theorem B872343 : Blo 868566 872343 := bstep (se 1 (by rfl) ⟨654257, by rfl⟩ : syracuseStep 872343 = 1308515) B1308515
theorem B872363 : Blo 868566 872363 := bstep (se 1 (by rfl) ⟨654272, by rfl⟩ : syracuseStep 872363 = 1308545) B1308545
theorem B872375 : Blo 868566 872375 := bstep (se 1 (by rfl) ⟨654281, by rfl⟩ : syracuseStep 872375 = 1308563) B1308563
theorem B872395 : Blo 868566 872395 := bstep (se 1 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 872395 = 1308593) B1308593
theorem B872407 : Blo 868566 872407 := bstep (se 1 (by rfl) ⟨654305, by rfl⟩ : syracuseStep 872407 = 1308611) B1308611
theorem B872427 : Blo 868566 872427 := bstep (se 1 (by rfl) ⟨654320, by rfl⟩ : syracuseStep 872427 = 1308641) B1308641
theorem B872439 : Blo 868566 872439 := bstep (se 1 (by rfl) ⟨654329, by rfl⟩ : syracuseStep 872439 = 1308659) B1308659
theorem B872459 : Blo 868566 872459 := bstep (se 1 (by rfl) ⟨654344, by rfl⟩ : syracuseStep 872459 = 1308689) B1308689
theorem B872471 : Blo 868566 872471 := bstep (se 1 (by rfl) ⟨654353, by rfl⟩ : syracuseStep 872471 = 1308707) B1308707
theorem B872491 : Blo 868566 872491 := bstep (se 1 (by rfl) ⟨654368, by rfl⟩ : syracuseStep 872491 = 1308737) B1308737
theorem B872503 : Blo 868566 872503 := bstep (se 1 (by rfl) ⟨654377, by rfl⟩ : syracuseStep 872503 = 1308755) B1308755
theorem B2936897 : Blo 868566 2936897 := bstep (se 2 (by rfl) ⟨1101336, by rfl⟩ : syracuseStep 2936897 = 2202673) B2202673
theorem B872523 : Blo 868566 872523 := bstep (se 1 (by rfl) ⟨654392, by rfl⟩ : syracuseStep 872523 = 1308785) B1308785
theorem B872535 : Blo 868566 872535 := bstep (se 1 (by rfl) ⟨654401, by rfl⟩ : syracuseStep 872535 = 1308803) B1308803
theorem B3723353 : Blo 868566 3723353 := bstep (se 2 (by rfl) ⟨1396257, by rfl⟩ : syracuseStep 3723353 = 2792515) B2792515
theorem B872555 : Blo 868566 872555 := bstep (se 1 (by rfl) ⟨654416, by rfl⟩ : syracuseStep 872555 = 1308833) B1308833
theorem B11161901 : Blo 868566 11161901 := bstep (se 3 (by rfl) ⟨2092856, by rfl⟩ : syracuseStep 11161901 = 4185713) B4185713
theorem B6607169 : Blo 868566 6607169 := bstep (se 2 (by rfl) ⟨2477688, by rfl⟩ : syracuseStep 6607169 = 4955377) B4955377
theorem B6279697 : Blo 868566 6279697 := bstep (se 2 (by rfl) ⟨2354886, by rfl⟩ : syracuseStep 6279697 = 4709773) B4709773
theorem B4969025 : Blo 868566 4969025 := bstep (se 2 (by rfl) ⟨1863384, by rfl⟩ : syracuseStep 4969025 = 3726769) B3726769
theorem B2937437 : Blo 868566 2937437 := bstep (se 3 (by rfl) ⟨550769, by rfl⟩ : syracuseStep 2937437 = 1101539) B1101539
theorem B1954457 : Blo 868566 1954457 := bstep (se 2 (by rfl) ⟨732921, by rfl⟩ : syracuseStep 1954457 = 1465843) B1465843
theorem B1954547 : Blo 868566 1954547 := bstep (se 1 (by rfl) ⟨1465910, by rfl⟩ : syracuseStep 1954547 = 2931821) B2931821
theorem B1954583 : Blo 868566 1954583 := bstep (se 1 (by rfl) ⟨1465937, by rfl⟩ : syracuseStep 1954583 = 2931875) B2931875
theorem B1856371 : Blo 868566 1856371 := bstep (se 1 (by rfl) ⟨1392278, by rfl⟩ : syracuseStep 1856371 = 2784557) B2784557
theorem B21418931 : Blo 868566 21418931 := bstep (se 1 (by rfl) ⟨16064198, by rfl⟩ : syracuseStep 21418931 = 32128397) B32128397
theorem B1954763 : Blo 868566 1954763 := bstep (se 1 (by rfl) ⟨1466072, by rfl⟩ : syracuseStep 1954763 = 2932145) B2932145
theorem B1954817 : Blo 868566 1954817 := bstep (se 2 (by rfl) ⟨733056, by rfl⟩ : syracuseStep 1954817 = 1466113) B1466113
theorem B2479193 : Blo 868566 2479193 := bstep (se 2 (by rfl) ⟨929697, by rfl⟩ : syracuseStep 2479193 = 1859395) B1859395
theorem B11293789 : Blo 868566 11293789 := bstep (se 3 (by rfl) ⟨2117585, by rfl⟩ : syracuseStep 11293789 = 4235171) B4235171
theorem B1102987 : Blo 868566 1102987 := bstep (se 1 (by rfl) ⟨827240, by rfl⟩ : syracuseStep 1102987 = 1654481) B1654481
theorem B1955033 : Blo 868566 1955033 := bstep (se 2 (by rfl) ⟨733137, by rfl⟩ : syracuseStep 1955033 = 1466275) B1466275
theorem B1856729 : Blo 868566 1856729 := bstep (se 2 (by rfl) ⟨696273, by rfl⟩ : syracuseStep 1856729 = 1392547) B1392547
theorem B4412717 : Blo 868566 4412717 := bstep (se 3 (by rfl) ⟨827384, by rfl⟩ : syracuseStep 4412717 = 1654769) B1654769
theorem B1955123 : Blo 868566 1955123 := bstep (se 1 (by rfl) ⟨1466342, by rfl⟩ : syracuseStep 1955123 = 2932685) B2932685
theorem B1955159 : Blo 868566 1955159 := bstep (se 1 (by rfl) ⟨1466369, by rfl⟩ : syracuseStep 1955159 = 2932739) B2932739
theorem B4183447 : Blo 868566 4183447 := bstep (se 1 (by rfl) ⟨3137585, by rfl⟩ : syracuseStep 4183447 = 6275171) B6275171
theorem B2479511 : Blo 868566 2479511 := bstep (se 1 (by rfl) ⟨1859633, by rfl⟩ : syracuseStep 2479511 = 3719267) B3719267
theorem B2119115 : Blo 868566 2119115 := bstep (se 1 (by rfl) ⟨1589336, by rfl⟩ : syracuseStep 2119115 = 3178673) B3178673
theorem B1955339 : Blo 868566 1955339 := bstep (se 1 (by rfl) ⟨1466504, by rfl⟩ : syracuseStep 1955339 = 2933009) B2933009
theorem B1955393 : Blo 868566 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B2938571 : Blo 868566 2938571 := bstep (se 1 (by rfl) ⟨2203928, by rfl⟩ : syracuseStep 2938571 = 4407857) B4407857
theorem B3299075 : Blo 868566 3299075 := bstep (se 1 (by rfl) ⟨2474306, by rfl⟩ : syracuseStep 3299075 = 4948613) B4948613
theorem B3299089 : Blo 868566 3299089 := bstep (se 2 (by rfl) ⟨1237158, by rfl⟩ : syracuseStep 3299089 = 2474317) B2474317
theorem B1955609 : Blo 868566 1955609 := bstep (se 2 (by rfl) ⟨733353, by rfl⟩ : syracuseStep 1955609 = 1466707) B1466707
theorem B1955699 : Blo 868566 1955699 := bstep (se 1 (by rfl) ⟨1466774, by rfl⟩ : syracuseStep 1955699 = 2933549) B2933549
theorem B1955735 : Blo 868566 1955735 := bstep (se 1 (by rfl) ⟨1466801, by rfl⟩ : syracuseStep 1955735 = 2933603) B2933603
theorem B2938841 : Blo 868566 2938841 := bstep (se 2 (by rfl) ⟨1102065, by rfl⟩ : syracuseStep 2938841 = 2204131) B2204131
theorem B3299393 : Blo 868566 3299393 := bstep (se 2 (by rfl) ⟨1237272, by rfl⟩ : syracuseStep 3299393 = 2474545) B2474545
theorem B1955915 : Blo 868566 1955915 := bstep (se 1 (by rfl) ⟨1466936, by rfl⟩ : syracuseStep 1955915 = 2933873) B2933873
theorem B5036107 : Blo 868566 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B1103959 : Blo 868566 1103959 := bstep (se 1 (by rfl) ⟨827969, by rfl⟩ : syracuseStep 1103959 = 1655939) B1655939
theorem B1955969 : Blo 868566 1955969 := bstep (se 2 (by rfl) ⟨733488, by rfl⟩ : syracuseStep 1955969 = 1466977) B1466977
theorem B9394327 : Blo 868566 9394327 := bstep (se 1 (by rfl) ⟨7045745, by rfl⟩ : syracuseStep 9394327 = 14091491) B14091491
theorem B2480321 : Blo 868566 2480321 := bstep (se 2 (by rfl) ⟨930120, by rfl⟩ : syracuseStep 2480321 = 1860241) B1860241
theorem B6609113 : Blo 868566 6609113 := bstep (se 2 (by rfl) ⟨2478417, by rfl⟩ : syracuseStep 6609113 = 4956835) B4956835
theorem B1956185 : Blo 868566 1956185 := bstep (se 2 (by rfl) ⟨733569, by rfl⟩ : syracuseStep 1956185 = 1467139) B1467139
theorem B1956275 : Blo 868566 1956275 := bstep (se 1 (by rfl) ⟨1467206, by rfl⟩ : syracuseStep 1956275 = 2934413) B2934413
theorem B1956311 : Blo 868566 1956311 := bstep (se 1 (by rfl) ⟨1467233, by rfl⟩ : syracuseStep 1956311 = 2934467) B2934467
theorem B2513369 : Blo 868566 2513369 := bstep (se 2 (by rfl) ⟨942513, by rfl⟩ : syracuseStep 2513369 = 1885027) B1885027
theorem B4184621 : Blo 868566 4184621 := bstep (se 3 (by rfl) ⟨784616, by rfl⟩ : syracuseStep 4184621 = 1569233) B1569233
theorem B15096395 : Blo 868566 15096395 := bstep (se 1 (by rfl) ⟨11322296, by rfl⟩ : syracuseStep 15096395 = 22644593) B22644593
theorem B2415193 : Blo 868566 2415193 := bstep (se 2 (by rfl) ⟨905697, by rfl⟩ : syracuseStep 2415193 = 1811395) B1811395
theorem B1956491 : Blo 868566 1956491 := bstep (se 1 (by rfl) ⟨1467368, by rfl⟩ : syracuseStep 1956491 = 2934737) B2934737
theorem B2939543 : Blo 868566 2939543 := bstep (se 1 (by rfl) ⟨2204657, by rfl⟩ : syracuseStep 2939543 = 4409315) B4409315
theorem B1956545 : Blo 868566 1956545 := bstep (se 2 (by rfl) ⟨733704, by rfl⟩ : syracuseStep 1956545 = 1467409) B1467409
theorem B3300061 : Blo 868566 3300061 := bstep (se 3 (by rfl) ⟨618761, by rfl⟩ : syracuseStep 3300061 = 1237523) B1237523
theorem B1956761 : Blo 868566 1956761 := bstep (se 2 (by rfl) ⟨733785, by rfl⟩ : syracuseStep 1956761 = 1467571) B1467571
theorem B941015 : Blo 868566 941015 := bstep (se 1 (by rfl) ⟨705761, by rfl⟩ : syracuseStep 941015 = 1411523) B1411523
theorem B1989593 : Blo 868566 1989593 := bstep (se 2 (by rfl) ⟨746097, by rfl⟩ : syracuseStep 1989593 = 1492195) B1492195
theorem B1956851 : Blo 868566 1956851 := bstep (se 1 (by rfl) ⟨1467638, by rfl⟩ : syracuseStep 1956851 = 2935277) B2935277
theorem B1956887 : Blo 868566 1956887 := bstep (se 1 (by rfl) ⟨1467665, by rfl⟩ : syracuseStep 1956887 = 2935331) B2935331
theorem B2940083 : Blo 868566 2940083 := bstep (se 1 (by rfl) ⟨2205062, by rfl⟩ : syracuseStep 2940083 = 4410125) B4410125
theorem B47733941 : Blo 868566 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B1957067 : Blo 868566 1957067 := bstep (se 1 (by rfl) ⟨1467800, by rfl⟩ : syracuseStep 1957067 = 2935601) B2935601
theorem B1858763 : Blo 868566 1858763 := bstep (se 1 (by rfl) ⟨1394072, by rfl⟩ : syracuseStep 1858763 = 2788145) B2788145
theorem B11164877 : Blo 868566 11164877 := bstep (se 3 (by rfl) ⟨2093414, by rfl⟩ : syracuseStep 11164877 = 4186829) B4186829
theorem B1957121 : Blo 868566 1957121 := bstep (se 2 (by rfl) ⟨733920, by rfl⟩ : syracuseStep 1957121 = 1467841) B1467841
theorem B12541229 : Blo 868566 12541229 := bstep (se 3 (by rfl) ⟨2351480, by rfl⟩ : syracuseStep 12541229 = 4702961) B4702961
theorem B1990003 : Blo 868566 1990003 := bstep (se 1 (by rfl) ⟨1492502, by rfl⟩ : syracuseStep 1990003 = 2985005) B2985005
theorem B2940353 : Blo 868566 2940353 := bstep (se 2 (by rfl) ⟨1102632, by rfl⟩ : syracuseStep 2940353 = 2205265) B2205265
theorem B3726785 : Blo 868566 3726785 := bstep (se 2 (by rfl) ⟨1397544, by rfl⟩ : syracuseStep 3726785 = 2795089) B2795089
theorem B1957337 : Blo 868566 1957337 := bstep (se 2 (by rfl) ⟨734001, by rfl⟩ : syracuseStep 1957337 = 1468003) B1468003
theorem B1957427 : Blo 868566 1957427 := bstep (se 1 (by rfl) ⟨1468070, by rfl⟩ : syracuseStep 1957427 = 2936141) B2936141
theorem B1465931 : Blo 868566 1465931 := bstep (se 1 (by rfl) ⟨1099448, by rfl⟩ : syracuseStep 1465931 = 2198897) B2198897
theorem B1957463 : Blo 868566 1957463 := bstep (se 1 (by rfl) ⟨1468097, by rfl⟩ : syracuseStep 1957463 = 2936195) B2936195
theorem B1466059 : Blo 868566 1466059 := bstep (se 1 (by rfl) ⟨1099544, by rfl⟩ : syracuseStep 1466059 = 2199089) B2199089
theorem B1957643 : Blo 868566 1957643 := bstep (se 1 (by rfl) ⟨1468232, by rfl⟩ : syracuseStep 1957643 = 2936465) B2936465
theorem B3727127 : Blo 868566 3727127 := bstep (se 1 (by rfl) ⟨2795345, by rfl⟩ : syracuseStep 3727127 = 5590691) B5590691
theorem B1957697 : Blo 868566 1957697 := bstep (se 2 (by rfl) ⟨734136, by rfl⟩ : syracuseStep 1957697 = 1468273) B1468273
theorem B2481995 : Blo 868566 2481995 := bstep (se 1 (by rfl) ⟨1861496, by rfl⟩ : syracuseStep 2481995 = 3722993) B3722993
theorem B1466201 : Blo 868566 1466201 := bstep (se 2 (by rfl) ⟨549825, by rfl⟩ : syracuseStep 1466201 = 1099651) B1099651
theorem B1466329 : Blo 868566 1466329 := bstep (se 2 (by rfl) ⟨549873, by rfl⟩ : syracuseStep 1466329 = 1099747) B1099747
theorem B3301337 : Blo 868566 3301337 := bstep (se 2 (by rfl) ⟨1238001, by rfl⟩ : syracuseStep 3301337 = 2476003) B2476003
theorem B2940893 : Blo 868566 2940893 := bstep (se 3 (by rfl) ⟨551417, by rfl⟩ : syracuseStep 2940893 = 1102835) B1102835
theorem B1957913 : Blo 868566 1957913 := bstep (se 2 (by rfl) ⟨734217, by rfl⟩ : syracuseStep 1957913 = 1468435) B1468435
theorem B1237079 : Blo 868566 1237079 := bstep (se 1 (by rfl) ⟨927809, by rfl⟩ : syracuseStep 1237079 = 1855619) B1855619
theorem B1958003 : Blo 868566 1958003 := bstep (se 1 (by rfl) ⟨1468502, by rfl⟩ : syracuseStep 1958003 = 2937005) B2937005
theorem B1958039 : Blo 868566 1958039 := bstep (se 1 (by rfl) ⟨1468529, by rfl⟩ : syracuseStep 1958039 = 2937059) B2937059
theorem B1958219 : Blo 868566 1958219 := bstep (se 1 (by rfl) ⟨1468664, by rfl⟩ : syracuseStep 1958219 = 2937329) B2937329
theorem B1761625 : Blo 868566 1761625 := bstep (se 2 (by rfl) ⟨660609, by rfl⟩ : syracuseStep 1761625 = 1321219) B1321219
theorem B1958273 : Blo 868566 1958273 := bstep (se 2 (by rfl) ⟨734352, by rfl⟩ : syracuseStep 1958273 = 1468705) B1468705
theorem B1302923 : Blo 868566 1302923 := bstep (se 1 (by rfl) ⟨977192, by rfl⟩ : syracuseStep 1302923 = 1954385) B1954385
theorem B1302935 : Blo 868566 1302935 := bstep (se 1 (by rfl) ⟨977201, by rfl⟩ : syracuseStep 1302935 = 1954403) B1954403
theorem B1859993 : Blo 868566 1859993 := bstep (se 2 (by rfl) ⟨697497, by rfl⟩ : syracuseStep 1859993 = 1394995) B1394995
theorem B1303001 : Blo 868566 1303001 := bstep (se 2 (by rfl) ⟨488625, by rfl⟩ : syracuseStep 1303001 = 977251) B977251
theorem B1466903 : Blo 868566 1466903 := bstep (se 1 (by rfl) ⟨1100177, by rfl⟩ : syracuseStep 1466903 = 2200355) B2200355
theorem B1303115 : Blo 868566 1303115 := bstep (se 1 (by rfl) ⟨977336, by rfl⟩ : syracuseStep 1303115 = 1954673) B1954673
theorem B1303127 : Blo 868566 1303127 := bstep (se 1 (by rfl) ⟨977345, by rfl⟩ : syracuseStep 1303127 = 1954691) B1954691
theorem B1958489 : Blo 868566 1958489 := bstep (se 2 (by rfl) ⟨734433, by rfl⟩ : syracuseStep 1958489 = 1468867) B1468867
theorem B6709853 : Blo 868566 6709853 := bstep (se 3 (by rfl) ⟨1258097, by rfl⟩ : syracuseStep 6709853 = 2516195) B2516195
theorem B1467031 : Blo 868566 1467031 := bstep (se 1 (by rfl) ⟨1100273, by rfl⟩ : syracuseStep 1467031 = 2200547) B2200547
theorem B1303193 : Blo 868566 1303193 := bstep (se 2 (by rfl) ⟨488697, by rfl⟩ : syracuseStep 1303193 = 977395) B977395
theorem B1958579 : Blo 868566 1958579 := bstep (se 1 (by rfl) ⟨1468934, by rfl⟩ : syracuseStep 1958579 = 2937869) B2937869
theorem B1958615 : Blo 868566 1958615 := bstep (se 1 (by rfl) ⟨1468961, by rfl⟩ : syracuseStep 1958615 = 2937923) B2937923
theorem B1303307 : Blo 868566 1303307 := bstep (se 1 (by rfl) ⟨977480, by rfl⟩ : syracuseStep 1303307 = 1954961) B1954961
theorem B1303319 : Blo 868566 1303319 := bstep (se 1 (by rfl) ⟨977489, by rfl⟩ : syracuseStep 1303319 = 1954979) B1954979
theorem B1860403 : Blo 868566 1860403 := bstep (se 1 (by rfl) ⟨1395302, by rfl⟩ : syracuseStep 1860403 = 2790605) B2790605
theorem B1303385 : Blo 868566 1303385 := bstep (se 2 (by rfl) ⟨488769, by rfl⟩ : syracuseStep 1303385 = 977539) B977539
theorem B5956453 : Blo 868566 5956453 := bstep (se 4 (by rfl) ⟨558417, by rfl⟩ : syracuseStep 5956453 = 1116835) B1116835
theorem B1958795 : Blo 868566 1958795 := bstep (se 1 (by rfl) ⟨1469096, by rfl⟩ : syracuseStep 1958795 = 2938193) B2938193
theorem B6710195 : Blo 868566 6710195 := bstep (se 1 (by rfl) ⟨5032646, by rfl⟩ : syracuseStep 6710195 = 10065293) B10065293
theorem B1958849 : Blo 868566 1958849 := bstep (se 2 (by rfl) ⟨734568, by rfl⟩ : syracuseStep 1958849 = 1469137) B1469137
theorem B1303499 : Blo 868566 1303499 := bstep (se 1 (by rfl) ⟨977624, by rfl⟩ : syracuseStep 1303499 = 1955249) B1955249
theorem B1303511 : Blo 868566 1303511 := bstep (se 1 (by rfl) ⟨977633, by rfl⟩ : syracuseStep 1303511 = 1955267) B1955267
theorem B1303577 : Blo 868566 1303577 := bstep (se 2 (by rfl) ⟨488841, by rfl⟩ : syracuseStep 1303577 = 977683) B977683
theorem B1860659 : Blo 868566 1860659 := bstep (se 1 (by rfl) ⟨1395494, by rfl⟩ : syracuseStep 1860659 = 2790989) B2790989
theorem B2942027 : Blo 868566 2942027 := bstep (se 1 (by rfl) ⟨2206520, by rfl⟩ : syracuseStep 2942027 = 4413041) B4413041
theorem B2483293 : Blo 868566 2483293 := bstep (se 3 (by rfl) ⟨465617, by rfl⟩ : syracuseStep 2483293 = 931235) B931235
theorem B4416605 : Blo 868566 4416605 := bstep (se 3 (by rfl) ⟨828113, by rfl⟩ : syracuseStep 4416605 = 1656227) B1656227
theorem B1303691 : Blo 868566 1303691 := bstep (se 1 (by rfl) ⟨977768, by rfl⟩ : syracuseStep 1303691 = 1955537) B1955537
theorem B1303703 : Blo 868566 1303703 := bstep (se 1 (by rfl) ⟨977777, by rfl⟩ : syracuseStep 1303703 = 1955555) B1955555
theorem B1959065 : Blo 868566 1959065 := bstep (se 2 (by rfl) ⟨734649, by rfl⟩ : syracuseStep 1959065 = 1469299) B1469299
theorem B1303769 : Blo 868566 1303769 := bstep (se 2 (by rfl) ⟨488913, by rfl⟩ : syracuseStep 1303769 = 977827) B977827
theorem B1959155 : Blo 868566 1959155 := bstep (se 1 (by rfl) ⟨1469366, by rfl⟩ : syracuseStep 1959155 = 2938733) B2938733
theorem B1467659 : Blo 868566 1467659 := bstep (se 1 (by rfl) ⟨1100744, by rfl⟩ : syracuseStep 1467659 = 2201489) B2201489
theorem B1959191 : Blo 868566 1959191 := bstep (se 1 (by rfl) ⟨1469393, by rfl⟩ : syracuseStep 1959191 = 2938787) B2938787
theorem B7529773 : Blo 868566 7529773 := bstep (se 3 (by rfl) ⟨1411832, by rfl⟩ : syracuseStep 7529773 = 2823665) B2823665
theorem B1303883 : Blo 868566 1303883 := bstep (se 1 (by rfl) ⟨977912, by rfl⟩ : syracuseStep 1303883 = 1955825) B1955825
theorem B1303895 : Blo 868566 1303895 := bstep (se 1 (by rfl) ⟨977921, by rfl⟩ : syracuseStep 1303895 = 1955843) B1955843
theorem B2942297 : Blo 868566 2942297 := bstep (se 2 (by rfl) ⟨1103361, by rfl⟩ : syracuseStep 2942297 = 2206723) B2206723
theorem B1467787 : Blo 868566 1467787 := bstep (se 1 (by rfl) ⟨1100840, by rfl⟩ : syracuseStep 1467787 = 2201681) B2201681
theorem B1303961 : Blo 868566 1303961 := bstep (se 2 (by rfl) ⟨488985, by rfl⟩ : syracuseStep 1303961 = 977971) B977971
theorem B2483635 : Blo 868566 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B1959371 : Blo 868566 1959371 := bstep (se 1 (by rfl) ⟨1469528, by rfl⟩ : syracuseStep 1959371 = 2939057) B2939057
theorem B2123225 : Blo 868566 2123225 := bstep (se 2 (by rfl) ⟨796209, by rfl⟩ : syracuseStep 2123225 = 1592419) B1592419
theorem B1959425 : Blo 868566 1959425 := bstep (se 2 (by rfl) ⟨734784, by rfl⟩ : syracuseStep 1959425 = 1469569) B1469569
theorem B1304075 : Blo 868566 1304075 := bstep (se 1 (by rfl) ⟨978056, by rfl⟩ : syracuseStep 1304075 = 1956113) B1956113
theorem B1304087 : Blo 868566 1304087 := bstep (se 1 (by rfl) ⟨978065, by rfl⟩ : syracuseStep 1304087 = 1956131) B1956131
theorem B1467929 : Blo 868566 1467929 := bstep (se 2 (by rfl) ⟨550473, by rfl⟩ : syracuseStep 1467929 = 1100947) B1100947
theorem B6612515 : Blo 868566 6612515 := bstep (se 1 (by rfl) ⟨4959386, by rfl⟩ : syracuseStep 6612515 = 9918773) B9918773
theorem B3302963 : Blo 868566 3302963 := bstep (se 1 (by rfl) ⟨2477222, by rfl⟩ : syracuseStep 3302963 = 4954445) B4954445
theorem B3302977 : Blo 868566 3302977 := bstep (se 2 (by rfl) ⟨1238616, by rfl⟩ : syracuseStep 3302977 = 2477233) B2477233
theorem B4187713 : Blo 868566 4187713 := bstep (se 2 (by rfl) ⟨1570392, by rfl⟩ : syracuseStep 4187713 = 3140785) B3140785
theorem B6350411 : Blo 868566 6350411 := bstep (se 1 (by rfl) ⟨4762808, by rfl⟩ : syracuseStep 6350411 = 9525617) B9525617
theorem B1304153 : Blo 868566 1304153 := bstep (se 2 (by rfl) ⟨489057, by rfl⟩ : syracuseStep 1304153 = 978115) B978115
theorem B2090647 : Blo 868566 2090647 := bstep (se 1 (by rfl) ⟨1567985, by rfl⟩ : syracuseStep 2090647 = 3135971) B3135971
theorem B1468057 : Blo 868566 1468057 := bstep (se 2 (by rfl) ⟨550521, by rfl⟩ : syracuseStep 1468057 = 1101043) B1101043
theorem B1304267 : Blo 868566 1304267 := bstep (se 1 (by rfl) ⟨978200, by rfl⟩ : syracuseStep 1304267 = 1956401) B1956401
theorem B1304279 : Blo 868566 1304279 := bstep (se 1 (by rfl) ⟨978209, by rfl⟩ : syracuseStep 1304279 = 1956419) B1956419
theorem B1959641 : Blo 868566 1959641 := bstep (se 2 (by rfl) ⟨734865, by rfl⟩ : syracuseStep 1959641 = 1469731) B1469731
theorem B1304345 : Blo 868566 1304345 := bstep (se 2 (by rfl) ⟨489129, by rfl⟩ : syracuseStep 1304345 = 978259) B978259
theorem B1959731 : Blo 868566 1959731 := bstep (se 1 (by rfl) ⟨1469798, by rfl⟩ : syracuseStep 1959731 = 2939597) B2939597
theorem B1959767 : Blo 868566 1959767 := bstep (se 1 (by rfl) ⟨1469825, by rfl⟩ : syracuseStep 1959767 = 2939651) B2939651
theorem B1304459 : Blo 868566 1304459 := bstep (se 1 (by rfl) ⟨978344, by rfl⟩ : syracuseStep 1304459 = 1956689) B1956689
theorem B1304471 : Blo 868566 1304471 := bstep (se 1 (by rfl) ⟨978353, by rfl⟩ : syracuseStep 1304471 = 1956707) B1956707
theorem B1304537 : Blo 868566 1304537 := bstep (se 2 (by rfl) ⟨489201, by rfl⟩ : syracuseStep 1304537 = 978403) B978403
theorem B1861633 : Blo 868566 1861633 := bstep (se 2 (by rfl) ⟨698112, by rfl⟩ : syracuseStep 1861633 = 1396225) B1396225
theorem B1959947 : Blo 868566 1959947 := bstep (se 1 (by rfl) ⟨1469960, by rfl⟩ : syracuseStep 1959947 = 2939921) B2939921
theorem B2942999 : Blo 868566 2942999 := bstep (se 1 (by rfl) ⟨2207249, by rfl⟩ : syracuseStep 2942999 = 4414499) B4414499
theorem B1960001 : Blo 868566 1960001 := bstep (se 2 (by rfl) ⟨735000, by rfl⟩ : syracuseStep 1960001 = 1470001) B1470001
theorem B6285377 : Blo 868566 6285377 := bstep (se 2 (by rfl) ⟨2357016, by rfl⟩ : syracuseStep 6285377 = 4714033) B4714033
theorem B1304651 : Blo 868566 1304651 := bstep (se 1 (by rfl) ⟨978488, by rfl⟩ : syracuseStep 1304651 = 1956977) B1956977
theorem B1304663 : Blo 868566 1304663 := bstep (se 1 (by rfl) ⟨978497, by rfl⟩ : syracuseStep 1304663 = 1956995) B1956995
theorem B1763417 : Blo 868566 1763417 := bstep (se 2 (by rfl) ⟨661281, by rfl⟩ : syracuseStep 1763417 = 1322563) B1322563
theorem B3139735 : Blo 868566 3139735 := bstep (se 1 (by rfl) ⟨2354801, by rfl⟩ : syracuseStep 3139735 = 4709603) B4709603
theorem B4188311 : Blo 868566 4188311 := bstep (se 1 (by rfl) ⟨3141233, by rfl⟩ : syracuseStep 4188311 = 6282467) B6282467
theorem B1304729 : Blo 868566 1304729 := bstep (se 2 (by rfl) ⟨489273, by rfl⟩ : syracuseStep 1304729 = 978547) B978547
theorem B1468631 : Blo 868566 1468631 := bstep (se 1 (by rfl) ⟨1101473, by rfl⟩ : syracuseStep 1468631 = 2202947) B2202947
theorem B977143 : Blo 868566 977143 := bstep (se 1 (by rfl) ⟨732857, by rfl⟩ : syracuseStep 977143 = 1465715) B1465715
theorem B1304843 : Blo 868566 1304843 := bstep (se 1 (by rfl) ⟨978632, by rfl⟩ : syracuseStep 1304843 = 1957265) B1957265
theorem B1304855 : Blo 868566 1304855 := bstep (se 1 (by rfl) ⟨978641, by rfl⟩ : syracuseStep 1304855 = 1957283) B1957283
theorem B1960217 : Blo 868566 1960217 := bstep (se 2 (by rfl) ⟨735081, by rfl⟩ : syracuseStep 1960217 = 1470163) B1470163
theorem B1567063 : Blo 868566 1567063 := bstep (se 1 (by rfl) ⟨1175297, by rfl⟩ : syracuseStep 1567063 = 2350595) B2350595
theorem B1304921 : Blo 868566 1304921 := bstep (se 2 (by rfl) ⟨489345, by rfl⟩ : syracuseStep 1304921 = 978691) B978691
theorem B1468759 : Blo 868566 1468759 := bstep (se 1 (by rfl) ⟨1101569, by rfl⟩ : syracuseStep 1468759 = 2203139) B2203139
theorem B2484569 : Blo 868566 2484569 := bstep (se 2 (by rfl) ⟨931713, by rfl⟩ : syracuseStep 2484569 = 1863427) B1863427
theorem B1960307 : Blo 868566 1960307 := bstep (se 1 (by rfl) ⟨1470230, by rfl⟩ : syracuseStep 1960307 = 2940461) B2940461
theorem B1960343 : Blo 868566 1960343 := bstep (se 1 (by rfl) ⟨1470257, by rfl⟩ : syracuseStep 1960343 = 2940515) B2940515
theorem B977323 : Blo 868566 977323 := bstep (se 1 (by rfl) ⟨732992, by rfl⟩ : syracuseStep 977323 = 1465985) B1465985
theorem B1305035 : Blo 868566 1305035 := bstep (se 1 (by rfl) ⟨978776, by rfl⟩ : syracuseStep 1305035 = 1957553) B1957553
theorem B1305047 : Blo 868566 1305047 := bstep (se 1 (by rfl) ⟨978785, by rfl⟩ : syracuseStep 1305047 = 1957571) B1957571
theorem B7072217 : Blo 868566 7072217 := bstep (se 2 (by rfl) ⟨2652081, by rfl⟩ : syracuseStep 7072217 = 5304163) B5304163
theorem B977431 : Blo 868566 977431 := bstep (se 1 (by rfl) ⟨733073, by rfl⟩ : syracuseStep 977431 = 1466147) B1466147
theorem B1305113 : Blo 868566 1305113 := bstep (se 2 (by rfl) ⟨489417, by rfl⟩ : syracuseStep 1305113 = 978835) B978835
theorem B2943539 : Blo 868566 2943539 := bstep (se 1 (by rfl) ⟨2207654, by rfl⟩ : syracuseStep 2943539 = 4415309) B4415309
theorem B9923147 : Blo 868566 9923147 := bstep (se 1 (by rfl) ⟨7442360, by rfl⟩ : syracuseStep 9923147 = 14884721) B14884721
theorem B1960523 : Blo 868566 1960523 := bstep (se 1 (by rfl) ⟨1470392, by rfl⟩ : syracuseStep 1960523 = 2940785) B2940785
theorem B1960577 : Blo 868566 1960577 := bstep (se 2 (by rfl) ⟨735216, by rfl⟩ : syracuseStep 1960577 = 1470433) B1470433
theorem B1305227 : Blo 868566 1305227 := bstep (se 1 (by rfl) ⟨978920, by rfl⟩ : syracuseStep 1305227 = 1957841) B1957841
theorem B1305239 : Blo 868566 1305239 := bstep (se 1 (by rfl) ⟨978929, by rfl⟩ : syracuseStep 1305239 = 1957859) B1957859
theorem B977611 : Blo 868566 977611 := bstep (se 1 (by rfl) ⟨733208, by rfl⟩ : syracuseStep 977611 = 1466417) B1466417
theorem B1305305 : Blo 868566 1305305 := bstep (se 2 (by rfl) ⟨489489, by rfl⟩ : syracuseStep 1305305 = 978979) B978979
theorem B977719 : Blo 868566 977719 := bstep (se 1 (by rfl) ⟨733289, by rfl⟩ : syracuseStep 977719 = 1466579) B1466579
theorem B2943809 : Blo 868566 2943809 := bstep (se 2 (by rfl) ⟨1103928, by rfl⟩ : syracuseStep 2943809 = 2207857) B2207857
theorem B1305419 : Blo 868566 1305419 := bstep (se 1 (by rfl) ⟨979064, by rfl⟩ : syracuseStep 1305419 = 1958129) B1958129
theorem B1305431 : Blo 868566 1305431 := bstep (se 1 (by rfl) ⟨979073, by rfl⟩ : syracuseStep 1305431 = 1958147) B1958147
theorem B1960793 : Blo 868566 1960793 := bstep (se 2 (by rfl) ⟨735297, by rfl⟩ : syracuseStep 1960793 = 1470595) B1470595
theorem B5303191 : Blo 868566 5303191 := bstep (se 1 (by rfl) ⟨3977393, by rfl⟩ : syracuseStep 5303191 = 7954787) B7954787
theorem B1305497 : Blo 868566 1305497 := bstep (se 2 (by rfl) ⟨489561, by rfl⟩ : syracuseStep 1305497 = 979123) B979123
theorem B1239961 : Blo 868566 1239961 := bstep (se 2 (by rfl) ⟨464985, by rfl⟩ : syracuseStep 1239961 = 929971) B929971
theorem B1960883 : Blo 868566 1960883 := bstep (se 1 (by rfl) ⟨1470662, by rfl⟩ : syracuseStep 1960883 = 2941325) B2941325
theorem B1469387 : Blo 868566 1469387 := bstep (se 1 (by rfl) ⟨1102040, by rfl⟩ : syracuseStep 1469387 = 2204081) B2204081
theorem B1960919 : Blo 868566 1960919 := bstep (se 1 (by rfl) ⟨1470689, by rfl⟩ : syracuseStep 1960919 = 2941379) B2941379
theorem B167668697 : Blo 868566 167668697 := bstep (se 2 (by rfl) ⟨62875761, by rfl⟩ : syracuseStep 167668697 = 125751523) B125751523
theorem B977899 : Blo 868566 977899 := bstep (se 1 (by rfl) ⟨733424, by rfl⟩ : syracuseStep 977899 = 1466849) B1466849
theorem B1305611 : Blo 868566 1305611 := bstep (se 1 (by rfl) ⟨979208, by rfl⟩ : syracuseStep 1305611 = 1958417) B1958417
theorem B1305623 : Blo 868566 1305623 := bstep (se 1 (by rfl) ⟨979217, by rfl⟩ : syracuseStep 1305623 = 1958435) B1958435
theorem B1469515 : Blo 868566 1469515 := bstep (se 1 (by rfl) ⟨1102136, by rfl⟩ : syracuseStep 1469515 = 2204273) B2204273
theorem B978007 : Blo 868566 978007 := bstep (se 1 (by rfl) ⟨733505, by rfl⟩ : syracuseStep 978007 = 1467011) B1467011
theorem B1305689 : Blo 868566 1305689 := bstep (se 2 (by rfl) ⟨489633, by rfl⟩ : syracuseStep 1305689 = 979267) B979267
theorem B1961099 : Blo 868566 1961099 := bstep (se 1 (by rfl) ⟨1470824, by rfl⟩ : syracuseStep 1961099 = 2941649) B2941649
theorem B1961153 : Blo 868566 1961153 := bstep (se 2 (by rfl) ⟨735432, by rfl⟩ : syracuseStep 1961153 = 1470865) B1470865
theorem B1305803 : Blo 868566 1305803 := bstep (se 1 (by rfl) ⟨979352, by rfl⟩ : syracuseStep 1305803 = 1958705) B1958705
theorem B1305815 : Blo 868566 1305815 := bstep (se 1 (by rfl) ⟨979361, by rfl⟩ : syracuseStep 1305815 = 1958723) B1958723
theorem B1469657 : Blo 868566 1469657 := bstep (se 2 (by rfl) ⟨551121, by rfl⟩ : syracuseStep 1469657 = 1102243) B1102243
theorem B7433477 : Blo 868566 7433477 := bstep (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) B1393777
theorem B978187 : Blo 868566 978187 := bstep (se 1 (by rfl) ⟨733640, by rfl⟩ : syracuseStep 978187 = 1467281) B1467281
theorem B1305881 : Blo 868566 1305881 := bstep (se 2 (by rfl) ⟨489705, by rfl⟩ : syracuseStep 1305881 = 979411) B979411
theorem B22605101 : Blo 868566 22605101 := bstep (se 3 (by rfl) ⟨4238456, by rfl⟩ : syracuseStep 22605101 = 8476913) B8476913
theorem B1469785 : Blo 868566 1469785 := bstep (se 2 (by rfl) ⟨551169, by rfl⟩ : syracuseStep 1469785 = 1102339) B1102339
theorem B2944349 : Blo 868566 2944349 := bstep (se 3 (by rfl) ⟨552065, by rfl⟩ : syracuseStep 2944349 = 1104131) B1104131
theorem B978295 : Blo 868566 978295 := bstep (se 1 (by rfl) ⟨733721, by rfl⟩ : syracuseStep 978295 = 1467443) B1467443
theorem B1305995 : Blo 868566 1305995 := bstep (se 1 (by rfl) ⟨979496, by rfl⟩ : syracuseStep 1305995 = 1958993) B1958993
theorem B1306007 : Blo 868566 1306007 := bstep (se 1 (by rfl) ⟨979505, by rfl⟩ : syracuseStep 1306007 = 1959011) B1959011
theorem B1961369 : Blo 868566 1961369 := bstep (se 2 (by rfl) ⟨735513, by rfl⟩ : syracuseStep 1961369 = 1471027) B1471027
theorem B3304907 : Blo 868566 3304907 := bstep (se 1 (by rfl) ⟨2478680, by rfl⟩ : syracuseStep 3304907 = 4957361) B4957361
theorem B3304921 : Blo 868566 3304921 := bstep (se 2 (by rfl) ⟨1239345, by rfl⟩ : syracuseStep 3304921 = 2478691) B2478691
theorem B1306073 : Blo 868566 1306073 := bstep (se 2 (by rfl) ⟨489777, by rfl⟩ : syracuseStep 1306073 = 979555) B979555
theorem B1961459 : Blo 868566 1961459 := bstep (se 1 (by rfl) ⟨1471094, by rfl⟩ : syracuseStep 1961459 = 2942189) B2942189
theorem B1961495 : Blo 868566 1961495 := bstep (se 1 (by rfl) ⟨1471121, by rfl⟩ : syracuseStep 1961495 = 2942243) B2942243
theorem B978475 : Blo 868566 978475 := bstep (se 1 (by rfl) ⟨733856, by rfl⟩ : syracuseStep 978475 = 1467713) B1467713
theorem B1306187 : Blo 868566 1306187 := bstep (se 1 (by rfl) ⟨979640, by rfl⟩ : syracuseStep 1306187 = 1959281) B1959281
theorem B1306199 : Blo 868566 1306199 := bstep (se 1 (by rfl) ⟨979649, by rfl⟩ : syracuseStep 1306199 = 1959299) B1959299
theorem B978583 : Blo 868566 978583 := bstep (se 1 (by rfl) ⟨733937, by rfl⟩ : syracuseStep 978583 = 1467875) B1467875
theorem B1306265 : Blo 868566 1306265 := bstep (se 2 (by rfl) ⟨489849, by rfl⟩ : syracuseStep 1306265 = 979699) B979699
theorem B1961675 : Blo 868566 1961675 := bstep (se 1 (by rfl) ⟨1471256, by rfl⟩ : syracuseStep 1961675 = 2942513) B2942513
theorem B1961729 : Blo 868566 1961729 := bstep (se 2 (by rfl) ⟨735648, by rfl⟩ : syracuseStep 1961729 = 1471297) B1471297
theorem B1306379 : Blo 868566 1306379 := bstep (se 1 (by rfl) ⟨979784, by rfl⟩ : syracuseStep 1306379 = 1959569) B1959569
theorem B1306391 : Blo 868566 1306391 := bstep (se 1 (by rfl) ⟨979793, by rfl⟩ : syracuseStep 1306391 = 1959587) B1959587
theorem B880427 : Blo 868566 880427 := bstep (se 1 (by rfl) ⟨660320, by rfl⟩ : syracuseStep 880427 = 1320641) B1320641
theorem B978763 : Blo 868566 978763 := bstep (se 1 (by rfl) ⟨734072, by rfl⟩ : syracuseStep 978763 = 1468145) B1468145
theorem B1306457 : Blo 868566 1306457 := bstep (se 2 (by rfl) ⟨489921, by rfl⟩ : syracuseStep 1306457 = 979843) B979843
theorem B1470359 : Blo 868566 1470359 := bstep (se 1 (by rfl) ⟨1102769, by rfl⟩ : syracuseStep 1470359 = 2205539) B2205539
theorem B978871 : Blo 868566 978871 := bstep (se 1 (by rfl) ⟨734153, by rfl⟩ : syracuseStep 978871 = 1468307) B1468307
theorem B1306571 : Blo 868566 1306571 := bstep (se 1 (by rfl) ⟨979928, by rfl⟩ : syracuseStep 1306571 = 1959857) B1959857
theorem B1306583 : Blo 868566 1306583 := bstep (se 1 (by rfl) ⟨979937, by rfl⟩ : syracuseStep 1306583 = 1959875) B1959875
theorem B1961945 : Blo 868566 1961945 := bstep (se 2 (by rfl) ⟨735729, by rfl⟩ : syracuseStep 1961945 = 1471459) B1471459
theorem B1470487 : Blo 868566 1470487 := bstep (se 1 (by rfl) ⟨1102865, by rfl⟩ : syracuseStep 1470487 = 2205731) B2205731
theorem B1306649 : Blo 868566 1306649 := bstep (se 2 (by rfl) ⟨489993, by rfl⟩ : syracuseStep 1306649 = 979987) B979987
theorem B1962035 : Blo 868566 1962035 := bstep (se 1 (by rfl) ⟨1471526, by rfl⟩ : syracuseStep 1962035 = 2943053) B2943053
theorem B1962071 : Blo 868566 1962071 := bstep (se 1 (by rfl) ⟨1471553, by rfl⟩ : syracuseStep 1962071 = 2943107) B2943107
theorem B3534941 : Blo 868566 3534941 := bstep (se 3 (by rfl) ⟨662801, by rfl⟩ : syracuseStep 3534941 = 1325603) B1325603
theorem B979051 : Blo 868566 979051 := bstep (se 1 (by rfl) ⟨734288, by rfl⟩ : syracuseStep 979051 = 1468577) B1468577
theorem B1306763 : Blo 868566 1306763 := bstep (se 1 (by rfl) ⟨980072, by rfl⟩ : syracuseStep 1306763 = 1960145) B1960145
theorem B1306775 : Blo 868566 1306775 := bstep (se 1 (by rfl) ⟨980081, by rfl⟩ : syracuseStep 1306775 = 1960163) B1960163
theorem B979159 : Blo 868566 979159 := bstep (se 1 (by rfl) ⟨734369, by rfl⟩ : syracuseStep 979159 = 1468739) B1468739
theorem B1306841 : Blo 868566 1306841 := bstep (se 2 (by rfl) ⟨490065, by rfl⟩ : syracuseStep 1306841 = 980131) B980131
theorem B1962251 : Blo 868566 1962251 := bstep (se 1 (by rfl) ⟨1471688, by rfl⟩ : syracuseStep 1962251 = 2943377) B2943377
theorem B1962305 : Blo 868566 1962305 := bstep (se 2 (by rfl) ⟨735864, by rfl⟩ : syracuseStep 1962305 = 1471729) B1471729
theorem B1306955 : Blo 868566 1306955 := bstep (se 1 (by rfl) ⟨980216, by rfl⟩ : syracuseStep 1306955 = 1960433) B1960433
theorem B1241419 : Blo 868566 1241419 := bstep (se 1 (by rfl) ⟨931064, by rfl⟩ : syracuseStep 1241419 = 1862129) B1862129
theorem B1306967 : Blo 868566 1306967 := bstep (se 1 (by rfl) ⟨980225, by rfl⟩ : syracuseStep 1306967 = 1960451) B1960451
theorem B979339 : Blo 868566 979339 := bstep (se 1 (by rfl) ⟨734504, by rfl⟩ : syracuseStep 979339 = 1469009) B1469009
theorem B3305879 : Blo 868566 3305879 := bstep (se 1 (by rfl) ⟨2479409, by rfl⟩ : syracuseStep 3305879 = 4958819) B4958819
theorem B1307033 : Blo 868566 1307033 := bstep (se 2 (by rfl) ⟨490137, by rfl⟩ : syracuseStep 1307033 = 980275) B980275
theorem B979447 : Blo 868566 979447 := bstep (se 1 (by rfl) ⟨734585, by rfl⟩ : syracuseStep 979447 = 1469171) B1469171
theorem B1307147 : Blo 868566 1307147 := bstep (se 1 (by rfl) ⟨980360, by rfl⟩ : syracuseStep 1307147 = 1960721) B1960721
theorem B1307159 : Blo 868566 1307159 := bstep (se 1 (by rfl) ⟨980369, by rfl⟩ : syracuseStep 1307159 = 1960739) B1960739
theorem B1962521 : Blo 868566 1962521 := bstep (se 2 (by rfl) ⟨735945, by rfl⟩ : syracuseStep 1962521 = 1471891) B1471891
theorem B1307225 : Blo 868566 1307225 := bstep (se 2 (by rfl) ⟨490209, by rfl⟩ : syracuseStep 1307225 = 980419) B980419
theorem B1962611 : Blo 868566 1962611 := bstep (se 1 (by rfl) ⟨1471958, by rfl⟩ : syracuseStep 1962611 = 2943917) B2943917
theorem B1471115 : Blo 868566 1471115 := bstep (se 1 (by rfl) ⟨1103336, by rfl⟩ : syracuseStep 1471115 = 2206673) B2206673
theorem B1962647 : Blo 868566 1962647 := bstep (se 1 (by rfl) ⟨1471985, by rfl⟩ : syracuseStep 1962647 = 2943971) B2943971
theorem B979627 : Blo 868566 979627 := bstep (se 1 (by rfl) ⟨734720, by rfl⟩ : syracuseStep 979627 = 1469441) B1469441
theorem B1307339 : Blo 868566 1307339 := bstep (se 1 (by rfl) ⟨980504, by rfl⟩ : syracuseStep 1307339 = 1961009) B1961009
theorem B1307351 : Blo 868566 1307351 := bstep (se 1 (by rfl) ⟨980513, by rfl⟩ : syracuseStep 1307351 = 1961027) B1961027
theorem B1471243 : Blo 868566 1471243 := bstep (se 1 (by rfl) ⟨1103432, by rfl⟩ : syracuseStep 1471243 = 2206865) B2206865
theorem B979735 : Blo 868566 979735 := bstep (se 1 (by rfl) ⟨734801, by rfl⟩ : syracuseStep 979735 = 1469603) B1469603
theorem B1307417 : Blo 868566 1307417 := bstep (se 2 (by rfl) ⟨490281, by rfl⟩ : syracuseStep 1307417 = 980563) B980563
theorem B4715309 : Blo 868566 4715309 := bstep (se 3 (by rfl) ⟨884120, by rfl⟩ : syracuseStep 4715309 = 1768241) B1768241
theorem B1962827 : Blo 868566 1962827 := bstep (se 1 (by rfl) ⟨1472120, by rfl⟩ : syracuseStep 1962827 = 2944241) B2944241
theorem B1962881 : Blo 868566 1962881 := bstep (se 2 (by rfl) ⟨736080, by rfl⟩ : syracuseStep 1962881 = 1472161) B1472161
theorem B1307531 : Blo 868566 1307531 := bstep (se 1 (by rfl) ⟨980648, by rfl⟩ : syracuseStep 1307531 = 1961297) B1961297
theorem B1307543 : Blo 868566 1307543 := bstep (se 1 (by rfl) ⟨980657, by rfl⟩ : syracuseStep 1307543 = 1961315) B1961315
theorem B1471385 : Blo 868566 1471385 := bstep (se 2 (by rfl) ⟨551769, by rfl⟩ : syracuseStep 1471385 = 1103539) B1103539
theorem B979915 : Blo 868566 979915 := bstep (se 1 (by rfl) ⟨734936, by rfl⟩ : syracuseStep 979915 = 1469873) B1469873
theorem B1307609 : Blo 868566 1307609 := bstep (se 2 (by rfl) ⟨490353, by rfl⟩ : syracuseStep 1307609 = 980707) B980707
theorem B1471513 : Blo 868566 1471513 := bstep (se 2 (by rfl) ⟨551817, by rfl⟩ : syracuseStep 1471513 = 1103635) B1103635
theorem B980023 : Blo 868566 980023 := bstep (se 1 (by rfl) ⟨735017, by rfl⟩ : syracuseStep 980023 = 1470035) B1470035
theorem B1307723 : Blo 868566 1307723 := bstep (se 1 (by rfl) ⟨980792, by rfl⟩ : syracuseStep 1307723 = 1961585) B1961585
theorem B1307735 : Blo 868566 1307735 := bstep (se 1 (by rfl) ⟨980801, by rfl⟩ : syracuseStep 1307735 = 1961603) B1961603
theorem B1963097 : Blo 868566 1963097 := bstep (se 2 (by rfl) ⟨736161, by rfl⟩ : syracuseStep 1963097 = 1472323) B1472323
theorem B1307801 : Blo 868566 1307801 := bstep (se 2 (by rfl) ⟨490425, by rfl⟩ : syracuseStep 1307801 = 980851) B980851
theorem B1963187 : Blo 868566 1963187 := bstep (se 1 (by rfl) ⟨1472390, by rfl⟩ : syracuseStep 1963187 = 2944781) B2944781
theorem B8352973 : Blo 868566 8352973 := bstep (se 3 (by rfl) ⟨1566182, by rfl⟩ : syracuseStep 8352973 = 3132365) B3132365
theorem B1963223 : Blo 868566 1963223 := bstep (se 1 (by rfl) ⟨1472417, by rfl⟩ : syracuseStep 1963223 = 2944835) B2944835
theorem B980203 : Blo 868566 980203 := bstep (se 1 (by rfl) ⟨735152, by rfl⟩ : syracuseStep 980203 = 1470305) B1470305
theorem B1307915 : Blo 868566 1307915 := bstep (se 1 (by rfl) ⟨980936, by rfl⟩ : syracuseStep 1307915 = 1961873) B1961873
theorem B1307927 : Blo 868566 1307927 := bstep (se 1 (by rfl) ⟨980945, by rfl⟩ : syracuseStep 1307927 = 1961891) B1961891
theorem B980311 : Blo 868566 980311 := bstep (se 1 (by rfl) ⟨735233, by rfl⟩ : syracuseStep 980311 = 1470467) B1470467
theorem B1307993 : Blo 868566 1307993 := bstep (se 2 (by rfl) ⟨490497, by rfl⟩ : syracuseStep 1307993 = 980995) B980995
theorem B1045963 : Blo 868566 1045963 := bstep (se 1 (by rfl) ⟨784472, by rfl⟩ : syracuseStep 1045963 = 1568945) B1568945
theorem B1308107 : Blo 868566 1308107 := bstep (se 1 (by rfl) ⟨981080, by rfl⟩ : syracuseStep 1308107 = 1962161) B1962161
theorem B1308119 : Blo 868566 1308119 := bstep (se 1 (by rfl) ⟨981089, by rfl⟩ : syracuseStep 1308119 = 1962179) B1962179
theorem B980491 : Blo 868566 980491 := bstep (se 1 (by rfl) ⟨735368, by rfl⟩ : syracuseStep 980491 = 1470737) B1470737
theorem B1308185 : Blo 868566 1308185 := bstep (se 2 (by rfl) ⟨490569, by rfl⟩ : syracuseStep 1308185 = 981139) B981139
theorem B1472087 : Blo 868566 1472087 := bstep (se 1 (by rfl) ⟨1104065, by rfl⟩ : syracuseStep 1472087 = 2208131) B2208131
theorem B980599 : Blo 868566 980599 := bstep (se 1 (by rfl) ⟨735449, by rfl⟩ : syracuseStep 980599 = 1470899) B1470899
theorem B3307139 : Blo 868566 3307139 := bstep (se 1 (by rfl) ⟨2480354, by rfl⟩ : syracuseStep 3307139 = 4960709) B4960709
theorem B1308299 : Blo 868566 1308299 := bstep (se 1 (by rfl) ⟨981224, by rfl⟩ : syracuseStep 1308299 = 1962449) B1962449
theorem B1308311 : Blo 868566 1308311 := bstep (se 1 (by rfl) ⟨981233, by rfl⟩ : syracuseStep 1308311 = 1962467) B1962467
theorem B1472215 : Blo 868566 1472215 := bstep (se 1 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 1472215 = 2208323) B2208323
theorem B1308377 : Blo 868566 1308377 := bstep (se 2 (by rfl) ⟨490641, by rfl⟩ : syracuseStep 1308377 = 981283) B981283
theorem B6616849 : Blo 868566 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B980779 : Blo 868566 980779 := bstep (se 1 (by rfl) ⟨735584, by rfl⟩ : syracuseStep 980779 = 1471169) B1471169
theorem B1308491 : Blo 868566 1308491 := bstep (se 1 (by rfl) ⟨981368, by rfl⟩ : syracuseStep 1308491 = 1962737) B1962737
theorem B1308503 : Blo 868566 1308503 := bstep (se 1 (by rfl) ⟨981377, by rfl⟩ : syracuseStep 1308503 = 1962755) B1962755
theorem B3143555 : Blo 868566 3143555 := bstep (se 1 (by rfl) ⟨2357666, by rfl⟩ : syracuseStep 3143555 = 4715333) B4715333
theorem B1570711 : Blo 868566 1570711 := bstep (se 1 (by rfl) ⟨1178033, by rfl⟩ : syracuseStep 1570711 = 2356067) B2356067
theorem B980887 : Blo 868566 980887 := bstep (se 1 (by rfl) ⟨735665, by rfl⟩ : syracuseStep 980887 = 1471331) B1471331
theorem B1308569 : Blo 868566 1308569 := bstep (se 2 (by rfl) ⟨490713, by rfl⟩ : syracuseStep 1308569 = 981427) B981427
theorem B2783197 : Blo 868566 2783197 := bstep (se 3 (by rfl) ⟨521849, by rfl⟩ : syracuseStep 2783197 = 1043699) B1043699
theorem B1308683 : Blo 868566 1308683 := bstep (se 1 (by rfl) ⟨981512, by rfl⟩ : syracuseStep 1308683 = 1963025) B1963025
theorem B1308695 : Blo 868566 1308695 := bstep (se 1 (by rfl) ⟨981521, by rfl⟩ : syracuseStep 1308695 = 1963043) B1963043
theorem B981067 : Blo 868566 981067 := bstep (se 1 (by rfl) ⟨735800, by rfl⟩ : syracuseStep 981067 = 1471601) B1471601
theorem B1308761 : Blo 868566 1308761 := bstep (se 2 (by rfl) ⟨490785, by rfl⟩ : syracuseStep 1308761 = 981571) B981571
theorem B981175 : Blo 868566 981175 := bstep (se 1 (by rfl) ⟨735881, by rfl⟩ : syracuseStep 981175 = 1471763) B1471763
theorem B2291915 : Blo 868566 2291915 := bstep (se 1 (by rfl) ⟨1718936, by rfl⟩ : syracuseStep 2291915 = 3437873) B3437873
theorem B981355 : Blo 868566 981355 := bstep (se 1 (by rfl) ⟨736016, by rfl⟩ : syracuseStep 981355 = 1472033) B1472033
theorem B981463 : Blo 868566 981463 := bstep (se 1 (by rfl) ⟨736097, by rfl⟩ : syracuseStep 981463 = 1472195) B1472195
theorem B2259479 : Blo 868566 2259479 := bstep (se 1 (by rfl) ⟨1694609, by rfl⟩ : syracuseStep 2259479 = 3389219) B3389219
theorem B7436893 : Blo 868566 7436893 := bstep (se 3 (by rfl) ⟨1394417, by rfl⟩ : syracuseStep 7436893 = 2788835) B2788835
theorem B1768087 : Blo 868566 1768087 := bstep (se 1 (by rfl) ⟨1326065, by rfl⟩ : syracuseStep 1768087 = 2652131) B2652131
theorem B6617861 : Blo 868566 6617861 := bstep (se 4 (by rfl) ⟨620424, by rfl⟩ : syracuseStep 6617861 = 1240849) B1240849
theorem B2095895 : Blo 868566 2095895 := bstep (se 1 (by rfl) ⟨1571921, by rfl⟩ : syracuseStep 2095895 = 3143843) B3143843
theorem B1178443 : Blo 868566 1178443 := bstep (se 1 (by rfl) ⟨883832, by rfl⟩ : syracuseStep 1178443 = 1767665) B1767665
theorem B17890379 : Blo 868566 17890379 := bstep (se 1 (by rfl) ⟨13417784, by rfl⟩ : syracuseStep 17890379 = 26835569) B26835569
theorem B883991 : Blo 868566 883991 := bstep (se 1 (by rfl) ⟨662993, by rfl⟩ : syracuseStep 883991 = 1325987) B1325987
theorem B1572311 : Blo 868566 1572311 := bstep (se 1 (by rfl) ⟨1179233, by rfl⟩ : syracuseStep 1572311 = 2358467) B2358467
theorem B4947587 : Blo 868566 4947587 := bstep (se 1 (by rfl) ⟨3710690, by rfl⟩ : syracuseStep 4947587 = 7421381) B7421381
theorem B2981569 : Blo 868566 2981569 := bstep (se 2 (by rfl) ⟨1118088, by rfl⟩ : syracuseStep 2981569 = 2236177) B2236177
theorem B7929751 : Blo 868566 7929751 := bstep (se 1 (by rfl) ⟨5947313, by rfl⟩ : syracuseStep 7929751 = 11894627) B11894627
theorem B4948087 : Blo 868566 4948087 := bstep (se 1 (by rfl) ⟨3711065, by rfl⟩ : syracuseStep 4948087 = 7422131) B7422131
theorem B11894957 : Blo 868566 11894957 := bstep (se 3 (by rfl) ⟨2230304, by rfl⟩ : syracuseStep 11894957 = 4460609) B4460609
theorem B7438877 : Blo 868566 7438877 := bstep (se 3 (by rfl) ⟨1394789, by rfl⟩ : syracuseStep 7438877 = 2789579) B2789579
theorem B6456179 : Blo 868566 6456179 := bstep (se 1 (by rfl) ⟨4842134, by rfl⟩ : syracuseStep 6456179 = 9684269) B9684269
theorem B4031441 : Blo 868566 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B4949363 : Blo 868566 4949363 := bstep (se 1 (by rfl) ⟨3712022, by rfl⟩ : syracuseStep 4949363 = 7424045) B7424045
theorem B3311057 : Blo 868566 3311057 := bstep (se 2 (by rfl) ⟨1241646, by rfl⟩ : syracuseStep 3311057 = 2483293) B2483293
theorem B7931395 : Blo 868566 7931395 := bstep (se 1 (by rfl) ⟨5948546, by rfl⟩ : syracuseStep 7931395 = 11897093) B11897093
theorem B10061491 : Blo 868566 10061491 := bstep (se 1 (by rfl) ⟨7546118, by rfl⟩ : syracuseStep 10061491 = 15092237) B15092237
theorem B6686479 : Blo 868566 6686479 := bstep (se 1 (by rfl) ⟨5014859, by rfl⟩ : syracuseStep 6686479 = 10029719) B10029719
theorem B4949819 : Blo 868566 4949819 := bstep (se 1 (by rfl) ⟨3712364, by rfl⟩ : syracuseStep 4949819 = 7424729) B7424729
theorem B3311513 : Blo 868566 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B2230217 : Blo 868566 2230217 := bstep (se 2 (by rfl) ⟨836331, by rfl⟩ : syracuseStep 2230217 = 1672663) B1672663
theorem B1116175 : Blo 868566 1116175 := bstep (se 1 (by rfl) ⟨837131, by rfl⟩ : syracuseStep 1116175 = 1674263) B1674263
theorem B4458557 : Blo 868566 4458557 := bstep (se 3 (by rfl) ⟨835979, by rfl⟩ : syracuseStep 4458557 = 1671959) B1671959
theorem B2787529 : Blo 868566 2787529 := bstep (se 2 (by rfl) ⟨1045323, by rfl⟩ : syracuseStep 2787529 = 2090647) B2090647
theorem B57117149 : Blo 868566 57117149 := bstep (se 3 (by rfl) ⟨10709465, by rfl⟩ : syracuseStep 57117149 = 21418931) B21418931
theorem B4950821 : Blo 868566 4950821 := bstep (se 4 (by rfl) ⟨464139, by rfl⟩ : syracuseStep 4950821 = 928279) B928279
theorem B7441267 : Blo 868566 7441267 := bstep (se 1 (by rfl) ⟨5580950, by rfl⟩ : syracuseStep 7441267 = 11161901) B11161901
theorem B3312683 : Blo 868566 3312683 := bstep (se 1 (by rfl) ⟨2484512, by rfl⟩ : syracuseStep 3312683 = 4969025) B4969025
theorem B12881029 : Blo 868566 12881029 := bstep (se 4 (by rfl) ⟨1207596, by rfl⟩ : syracuseStep 12881029 = 2415193) B2415193
theorem B7441541 : Blo 868566 7441541 := bstep (se 4 (by rfl) ⟨697644, by rfl⟩ : syracuseStep 7441541 = 1395289) B1395289
theorem B4951277 : Blo 868566 4951277 := bstep (se 3 (by rfl) ⟨928364, by rfl⟩ : syracuseStep 4951277 = 1856729) B1856729
theorem B2198785 : Blo 868566 2198785 := bstep (se 2 (by rfl) ⟨824544, by rfl⟩ : syracuseStep 2198785 = 1649089) B1649089
theorem B1412743 : Blo 868566 1412743 := bstep (se 1 (by rfl) ⟨1059557, by rfl⟩ : syracuseStep 1412743 = 2119115) B2119115
theorem B7442225 : Blo 868566 7442225 := bstep (se 2 (by rfl) ⟨2790834, by rfl⟩ : syracuseStep 7442225 = 5581669) B5581669
theorem B2199383 : Blo 868566 2199383 := bstep (se 1 (by rfl) ⟨1649537, by rfl⟩ : syracuseStep 2199383 = 3299075) B3299075
theorem B4951961 : Blo 868566 4951961 := bstep (se 2 (by rfl) ⟨1856985, by rfl⟩ : syracuseStep 4951961 = 3713971) B3713971
theorem B2199595 : Blo 868566 2199595 := bstep (se 1 (by rfl) ⟨1649696, by rfl⟩ : syracuseStep 2199595 = 3299393) B3299393
theorem B2199737 : Blo 868566 2199737 := bstep (se 2 (by rfl) ⟨824901, by rfl⟩ : syracuseStep 2199737 = 1649803) B1649803
theorem B4526273 : Blo 868566 4526273 := bstep (se 2 (by rfl) ⟨1697352, by rfl⟩ : syracuseStep 4526273 = 3394705) B3394705
theorem B1675579 : Blo 868566 1675579 := bstep (se 1 (by rfl) ⟨1256684, by rfl⟩ : syracuseStep 1675579 = 2513369) B2513369
theorem B2789747 : Blo 868566 2789747 := bstep (se 1 (by rfl) ⟨2092310, by rfl⟩ : syracuseStep 2789747 = 4184621) B4184621
theorem B10064263 : Blo 868566 10064263 := bstep (se 1 (by rfl) ⟨7548197, by rfl⟩ : syracuseStep 10064263 = 15096395) B15096395
theorem B8917775 : Blo 868566 8917775 := bstep (se 1 (by rfl) ⟨6688331, by rfl⟩ : syracuseStep 8917775 = 13376663) B13376663
theorem B31822627 : Blo 868566 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B7443251 : Blo 868566 7443251 := bstep (se 1 (by rfl) ⟨5582438, by rfl⟩ : syracuseStep 7443251 = 11164877) B11164877
theorem B8360819 : Blo 868566 8360819 := bstep (se 1 (by rfl) ⟨6270614, by rfl⟩ : syracuseStep 8360819 = 12541229) B12541229
theorem B2200729 : Blo 868566 2200729 := bstep (se 2 (by rfl) ⟨825273, by rfl⟩ : syracuseStep 2200729 = 1650547) B1650547
theorem B2200891 : Blo 868566 2200891 := bstep (se 1 (by rfl) ⟨1650668, by rfl⟩ : syracuseStep 2200891 = 3301337) B3301337
theorem B2201033 : Blo 868566 2201033 := bstep (se 2 (by rfl) ⟨825387, by rfl⟩ : syracuseStep 2201033 = 1650775) B1650775
theorem B1414601 : Blo 868566 1414601 := bstep (se 2 (by rfl) ⟨530475, by rfl⟩ : syracuseStep 1414601 = 1060951) B1060951
theorem B2201377 : Blo 868566 2201377 := bstep (se 2 (by rfl) ⟨825516, by rfl⟩ : syracuseStep 2201377 = 1651033) B1651033
theorem B5085149 : Blo 868566 5085149 := bstep (se 3 (by rfl) ⟨953465, by rfl⟩ : syracuseStep 5085149 = 1906931) B1906931
theorem B2234411 : Blo 868566 2234411 := bstep (se 1 (by rfl) ⟨1675808, by rfl⟩ : syracuseStep 2234411 = 3351617) B3351617
theorem B4397327 : Blo 868566 4397327 := bstep (se 1 (by rfl) ⟨3297995, by rfl⟩ : syracuseStep 4397327 = 6595991) B6595991
theorem B1415483 : Blo 868566 1415483 := bstep (se 1 (by rfl) ⟨1061612, by rfl⟩ : syracuseStep 1415483 = 2123225) B2123225
theorem B2201975 : Blo 868566 2201975 := bstep (se 1 (by rfl) ⟨1651481, by rfl⟩ : syracuseStep 2201975 = 3302963) B3302963
theorem B2792207 : Blo 868566 2792207 := bstep (se 1 (by rfl) ⟨2094155, by rfl⟩ : syracuseStep 2792207 = 4188311) B4188311
theorem B5577929 : Blo 868566 5577929 := bstep (se 2 (by rfl) ⟨2091723, by rfl⟩ : syracuseStep 5577929 = 4183447) B4183447
theorem B111779131 : Blo 868566 111779131 := bstep (se 1 (by rfl) ⟨83834348, by rfl⟩ : syracuseStep 111779131 = 167668697) B167668697
theorem B990599 : Blo 868566 990599 := bstep (se 1 (by rfl) ⟨742949, by rfl⟩ : syracuseStep 990599 = 1485899) B1485899
theorem B4955651 : Blo 868566 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B2203271 : Blo 868566 2203271 := bstep (se 1 (by rfl) ⟨1652453, by rfl⟩ : syracuseStep 2203271 = 3304907) B3304907
theorem B2203321 : Blo 868566 2203321 := bstep (se 2 (by rfl) ⟨826245, by rfl⟩ : syracuseStep 2203321 = 1652491) B1652491
theorem B4398785 : Blo 868566 4398785 := bstep (se 2 (by rfl) ⟨1649544, by rfl⟩ : syracuseStep 4398785 = 3299089) B3299089
theorem B8822465 : Blo 868566 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B5578469 : Blo 868566 5578469 := bstep (se 4 (by rfl) ⟨522981, by rfl⟩ : syracuseStep 5578469 = 1045963) B1045963
theorem B3710929 : Blo 868566 3710929 := bstep (se 2 (by rfl) ⟨1391598, by rfl⟩ : syracuseStep 3710929 = 2783197) B2783197
theorem B12525769 : Blo 868566 12525769 := bstep (se 2 (by rfl) ⟨4697163, by rfl⟩ : syracuseStep 12525769 = 9394327) B9394327
theorem B2203919 : Blo 868566 2203919 := bstep (se 1 (by rfl) ⟨1652939, by rfl⟩ : syracuseStep 2203919 = 3305879) B3305879
theorem B21439043 : Blo 868566 21439043 := bstep (se 1 (by rfl) ⟨16079282, by rfl⟩ : syracuseStep 21439043 = 32158565) B32158565
theorem B2204617 : Blo 868566 2204617 := bstep (se 2 (by rfl) ⟨826731, by rfl⟩ : syracuseStep 2204617 = 1653463) B1653463
theorem B4400081 : Blo 868566 4400081 := bstep (se 2 (by rfl) ⟨1650030, by rfl⟩ : syracuseStep 4400081 = 3300061) B3300061
theorem B10593341 : Blo 868566 10593341 := bstep (se 3 (by rfl) ⟨1986251, by rfl⟩ : syracuseStep 10593341 = 3972503) B3972503
theorem B2204759 : Blo 868566 2204759 := bstep (se 1 (by rfl) ⟨1653569, by rfl⟩ : syracuseStep 2204759 = 3307139) B3307139
theorem B3975425 : Blo 868566 3975425 := bstep (se 2 (by rfl) ⟨1490784, by rfl⟩ : syracuseStep 3975425 = 2981569) B2981569
theorem B1649423 : Blo 868566 1649423 := bstep (se 1 (by rfl) ⟨1237067, by rfl⟩ : syracuseStep 1649423 = 2474135) B2474135
theorem B5581619 : Blo 868566 5581619 := bstep (se 1 (by rfl) ⟨4186214, by rfl⟩ : syracuseStep 5581619 = 8372429) B8372429
theorem B4402187 : Blo 868566 4402187 := bstep (se 1 (by rfl) ⟨3301640, by rfl⟩ : syracuseStep 4402187 = 6603281) B6603281
theorem B2206835 : Blo 868566 2206835 := bstep (se 1 (by rfl) ⟨1655126, by rfl⟩ : syracuseStep 2206835 = 3310253) B3310253
theorem B928903 : Blo 868566 928903 := bstep (se 1 (by rfl) ⟨696677, by rfl⟩ : syracuseStep 928903 = 1393355) B1393355
theorem B4402349 : Blo 868566 4402349 := bstep (se 3 (by rfl) ⟨825440, by rfl⟩ : syracuseStep 4402349 = 1650881) B1650881
theorem B1649963 : Blo 868566 1649963 := bstep (se 1 (by rfl) ⟨1237472, by rfl⟩ : syracuseStep 1649963 = 2474945) B2474945
theorem B2207351 : Blo 868566 2207351 := bstep (se 1 (by rfl) ⟨1655513, by rfl⟩ : syracuseStep 2207351 = 3311027) B3311027
theorem B7745329 : Blo 868566 7745329 := bstep (se 2 (by rfl) ⟨2904498, by rfl⟩ : syracuseStep 7745329 = 5808997) B5808997
theorem B7941937 : Blo 868566 7941937 := bstep (se 2 (by rfl) ⟨2978226, by rfl⟩ : syracuseStep 7941937 = 5956453) B5956453
theorem B15249221 : Blo 868566 15249221 := bstep (se 4 (by rfl) ⟨1429614, by rfl⟩ : syracuseStep 15249221 = 2859229) B2859229
theorem B929723 : Blo 868566 929723 := bstep (se 1 (by rfl) ⟨697292, by rfl⟩ : syracuseStep 929723 = 1394585) B1394585
theorem B2830423 : Blo 868566 2830423 := bstep (se 1 (by rfl) ⟨2122817, by rfl⟩ : syracuseStep 2830423 = 4245635) B4245635
theorem B1651079 : Blo 868566 1651079 := bstep (se 1 (by rfl) ⟨1238309, by rfl⟩ : syracuseStep 1651079 = 2476619) B2476619
theorem B1257871 : Blo 868566 1257871 := bstep (se 1 (by rfl) ⟨943403, by rfl⟩ : syracuseStep 1257871 = 1886807) B1886807
theorem B10039697 : Blo 868566 10039697 := bstep (se 2 (by rfl) ⟨3764886, by rfl⟩ : syracuseStep 10039697 = 7529773) B7529773
theorem B3715645 : Blo 868566 3715645 := bstep (se 3 (by rfl) ⟨696683, by rfl⟩ : syracuseStep 3715645 = 1393367) B1393367
theorem B2208343 : Blo 868566 2208343 := bstep (se 1 (by rfl) ⟨1656257, by rfl⟩ : syracuseStep 2208343 = 3312515) B3312515
theorem B4403969 : Blo 868566 4403969 := bstep (se 2 (by rfl) ⟨1651488, by rfl⟩ : syracuseStep 4403969 = 3302977) B3302977
theorem B5583617 : Blo 868566 5583617 := bstep (se 2 (by rfl) ⟨2093856, by rfl⟩ : syracuseStep 5583617 = 4187713) B4187713
theorem B3978017 : Blo 868566 3978017 := bstep (se 2 (by rfl) ⟨1491756, by rfl⟩ : syracuseStep 3978017 = 2983513) B2983513
theorem B1192747 : Blo 868566 1192747 := bstep (se 1 (by rfl) ⟨894560, by rfl⟩ : syracuseStep 1192747 = 1789121) B1789121
theorem B5649203 : Blo 868566 5649203 := bstep (se 1 (by rfl) ⟨4236902, by rfl⟩ : syracuseStep 5649203 = 8473805) B8473805
theorem B2208647 : Blo 868566 2208647 := bstep (se 1 (by rfl) ⟨1656485, by rfl⟩ : syracuseStep 2208647 = 3312971) B3312971
theorem B1651603 : Blo 868566 1651603 := bstep (se 1 (by rfl) ⟨1238702, by rfl⟩ : syracuseStep 1651603 = 2477405) B2477405
theorem B4961209 : Blo 868566 4961209 := bstep (se 2 (by rfl) ⟨1860453, by rfl⟩ : syracuseStep 4961209 = 3720907) B3720907
theorem B1488143 : Blo 868566 1488143 := bstep (se 1 (by rfl) ⟨1116107, by rfl⟩ : syracuseStep 1488143 = 2232215) B2232215
theorem B4404779 : Blo 868566 4404779 := bstep (se 1 (by rfl) ⟨3303584, by rfl⟩ : syracuseStep 4404779 = 6607169) B6607169
theorem B5289761 : Blo 868566 5289761 := bstep (se 2 (by rfl) ⟨1983660, by rfl⟩ : syracuseStep 5289761 = 3967321) B3967321
theorem B1324873 : Blo 868566 1324873 := bstep (se 2 (by rfl) ⟨496827, by rfl⟩ : syracuseStep 1324873 = 993655) B993655
theorem B14137163 : Blo 868566 14137163 := bstep (se 1 (by rfl) ⟨10602872, by rfl⟩ : syracuseStep 14137163 = 21205745) B21205745
theorem B6273035 : Blo 868566 6273035 := bstep (se 1 (by rfl) ⟨4704776, by rfl⟩ : syracuseStep 6273035 = 9409553) B9409553
theorem B1652795 : Blo 868566 1652795 := bstep (se 1 (by rfl) ⟨1239596, by rfl⟩ : syracuseStep 1652795 = 2479193) B2479193
theorem B1718561 : Blo 868566 1718561 := bstep (se 2 (by rfl) ⟨644460, by rfl⟩ : syracuseStep 1718561 = 1288921) B1288921
theorem B1653281 : Blo 868566 1653281 := bstep (se 2 (by rfl) ⟨619980, by rfl⟩ : syracuseStep 1653281 = 1239961) B1239961
theorem B1653547 : Blo 868566 1653547 := bstep (se 1 (by rfl) ⟨1240160, by rfl⟩ : syracuseStep 1653547 = 2480321) B2480321
theorem B4406075 : Blo 868566 4406075 := bstep (se 1 (by rfl) ⟨3304556, by rfl⟩ : syracuseStep 4406075 = 6609113) B6609113
theorem B4406237 : Blo 868566 4406237 := bstep (se 3 (by rfl) ⟨826169, by rfl⟩ : syracuseStep 4406237 = 1652339) B1652339
theorem B3718345 : Blo 868566 3718345 := bstep (se 2 (by rfl) ⟨1394379, by rfl⟩ : syracuseStep 3718345 = 2788759) B2788759
theorem B2931983 : Blo 868566 2931983 := bstep (se 1 (by rfl) ⟨2198987, by rfl⟩ : syracuseStep 2931983 = 4397975) B4397975
theorem B4406561 : Blo 868566 4406561 := bstep (se 2 (by rfl) ⟨1652460, by rfl⟩ : syracuseStep 4406561 = 3304921) B3304921
theorem B1326395 : Blo 868566 1326395 := bstep (se 1 (by rfl) ⟨994796, by rfl⟩ : syracuseStep 1326395 = 1989593) B1989593
theorem B2473487 : Blo 868566 2473487 := bstep (se 1 (by rfl) ⟨1855115, by rfl⟩ : syracuseStep 2473487 = 3710231) B3710231
theorem B2932253 : Blo 868566 2932253 := bstep (se 3 (by rfl) ⟨549797, by rfl⟩ : syracuseStep 2932253 = 1099595) B1099595
theorem B1654663 : Blo 868566 1654663 := bstep (se 1 (by rfl) ⟨1240997, by rfl⟩ : syracuseStep 1654663 = 2481995) B2481995
theorem B4702445 : Blo 868566 4702445 := bstep (se 3 (by rfl) ⟨881708, by rfl⟩ : syracuseStep 4702445 = 1763417) B1763417
theorem B4407533 : Blo 868566 4407533 := bstep (se 3 (by rfl) ⟨826412, by rfl⟩ : syracuseStep 4407533 = 1652825) B1652825
theorem B868615 : Blo 868566 868615 := bstep (se 1 (by rfl) ⟨651461, by rfl⟩ : syracuseStep 868615 = 1302923) B1302923
theorem B868623 : Blo 868566 868623 := bstep (se 1 (by rfl) ⟨651467, by rfl⟩ : syracuseStep 868623 = 1302935) B1302935
theorem B868667 : Blo 868566 868667 := bstep (se 1 (by rfl) ⟨651500, by rfl⟩ : syracuseStep 868667 = 1303001) B1303001
theorem B868743 : Blo 868566 868743 := bstep (se 1 (by rfl) ⟨651557, by rfl⟩ : syracuseStep 868743 = 1303115) B1303115
theorem B868751 : Blo 868566 868751 := bstep (se 1 (by rfl) ⟨651563, by rfl⟩ : syracuseStep 868751 = 1303127) B1303127
theorem B4473235 : Blo 868566 4473235 := bstep (se 1 (by rfl) ⟨3354926, by rfl⟩ : syracuseStep 4473235 = 6709853) B6709853
theorem B1655225 : Blo 868566 1655225 := bstep (se 2 (by rfl) ⟨620709, by rfl⟩ : syracuseStep 1655225 = 1241419) B1241419
theorem B868795 : Blo 868566 868795 := bstep (se 1 (by rfl) ⟨651596, by rfl⟩ : syracuseStep 868795 = 1303193) B1303193
theorem B868871 : Blo 868566 868871 := bstep (se 1 (by rfl) ⟨651653, by rfl⟩ : syracuseStep 868871 = 1303307) B1303307
theorem B868879 : Blo 868566 868879 := bstep (se 1 (by rfl) ⟨651659, by rfl⟩ : syracuseStep 868879 = 1303319) B1303319
theorem B6111773 : Blo 868566 6111773 := bstep (se 3 (by rfl) ⟨1145957, by rfl⟩ : syracuseStep 6111773 = 2291915) B2291915
theorem B868923 : Blo 868566 868923 := bstep (se 1 (by rfl) ⟨651692, by rfl⟩ : syracuseStep 868923 = 1303385) B1303385
theorem B10601027 : Blo 868566 10601027 := bstep (se 1 (by rfl) ⟨7950770, by rfl⟩ : syracuseStep 10601027 = 15901541) B15901541
theorem B4473463 : Blo 868566 4473463 := bstep (se 1 (by rfl) ⟨3355097, by rfl⟩ : syracuseStep 4473463 = 6710195) B6710195
theorem B868999 : Blo 868566 868999 := bstep (se 1 (by rfl) ⟨651749, by rfl⟩ : syracuseStep 868999 = 1303499) B1303499
theorem B869007 : Blo 868566 869007 := bstep (se 1 (by rfl) ⟨651755, by rfl⟩ : syracuseStep 869007 = 1303511) B1303511
theorem B869051 : Blo 868566 869051 := bstep (se 1 (by rfl) ⟨651788, by rfl⟩ : syracuseStep 869051 = 1303577) B1303577
theorem B8372929 : Blo 868566 8372929 := bstep (se 2 (by rfl) ⟨3139848, by rfl⟩ : syracuseStep 8372929 = 6279697) B6279697
theorem B5030657 : Blo 868566 5030657 := bstep (se 2 (by rfl) ⟨1886496, by rfl⟩ : syracuseStep 5030657 = 3772993) B3772993
theorem B869127 : Blo 868566 869127 := bstep (se 1 (by rfl) ⟨651845, by rfl⟩ : syracuseStep 869127 = 1303691) B1303691
theorem B869135 : Blo 868566 869135 := bstep (se 1 (by rfl) ⟨651851, by rfl⟩ : syracuseStep 869135 = 1303703) B1303703
theorem B3719951 : Blo 868566 3719951 := bstep (se 1 (by rfl) ⟨2789963, by rfl⟩ : syracuseStep 3719951 = 5579927) B5579927
theorem B869179 : Blo 868566 869179 := bstep (se 1 (by rfl) ⟨651884, by rfl⟩ : syracuseStep 869179 = 1303769) B1303769
theorem B2474887 : Blo 868566 2474887 := bstep (se 1 (by rfl) ⟨1856165, by rfl⟩ : syracuseStep 2474887 = 3712331) B3712331
theorem B869255 : Blo 868566 869255 := bstep (se 1 (by rfl) ⟨651941, by rfl⟩ : syracuseStep 869255 = 1303883) B1303883
theorem B869263 : Blo 868566 869263 := bstep (se 1 (by rfl) ⟨651947, by rfl⟩ : syracuseStep 869263 = 1303895) B1303895
theorem B2933657 : Blo 868566 2933657 := bstep (se 2 (by rfl) ⟨1100121, by rfl⟩ : syracuseStep 2933657 = 2200243) B2200243
theorem B869307 : Blo 868566 869307 := bstep (se 1 (by rfl) ⟨651980, by rfl⟩ : syracuseStep 869307 = 1303961) B1303961
theorem B1983433 : Blo 868566 1983433 := bstep (se 2 (by rfl) ⟨743787, by rfl⟩ : syracuseStep 1983433 = 1487575) B1487575
theorem B4178947 : Blo 868566 4178947 := bstep (se 1 (by rfl) ⟨3134210, by rfl⟩ : syracuseStep 4178947 = 6268421) B6268421
theorem B869383 : Blo 868566 869383 := bstep (se 1 (by rfl) ⟨652037, by rfl⟩ : syracuseStep 869383 = 1304075) B1304075
theorem B869391 : Blo 868566 869391 := bstep (se 1 (by rfl) ⟨652043, by rfl⟩ : syracuseStep 869391 = 1304087) B1304087
theorem B4408343 : Blo 868566 4408343 := bstep (se 1 (by rfl) ⟨3306257, by rfl⟩ : syracuseStep 4408343 = 6612515) B6612515
theorem B869435 : Blo 868566 869435 := bstep (se 1 (by rfl) ⟨652076, by rfl⟩ : syracuseStep 869435 = 1304153) B1304153
theorem B869511 : Blo 868566 869511 := bstep (se 1 (by rfl) ⟨652133, by rfl⟩ : syracuseStep 869511 = 1304267) B1304267
theorem B869519 : Blo 868566 869519 := bstep (se 1 (by rfl) ⟨652139, by rfl⟩ : syracuseStep 869519 = 1304279) B1304279
theorem B2475161 : Blo 868566 2475161 := bstep (se 2 (by rfl) ⟨928185, by rfl⟩ : syracuseStep 2475161 = 1856371) B1856371
theorem B869563 : Blo 868566 869563 := bstep (se 1 (by rfl) ⟨652172, by rfl⟩ : syracuseStep 869563 = 1304345) B1304345
theorem B869639 : Blo 868566 869639 := bstep (se 1 (by rfl) ⟨652229, by rfl⟩ : syracuseStep 869639 = 1304459) B1304459
theorem B869647 : Blo 868566 869647 := bstep (se 1 (by rfl) ⟨652235, by rfl⟩ : syracuseStep 869647 = 1304471) B1304471
theorem B869691 : Blo 868566 869691 := bstep (se 1 (by rfl) ⟨652268, by rfl⟩ : syracuseStep 869691 = 1304537) B1304537
theorem B869767 : Blo 868566 869767 := bstep (se 1 (by rfl) ⟨652325, by rfl⟩ : syracuseStep 869767 = 1304651) B1304651
theorem B869775 : Blo 868566 869775 := bstep (se 1 (by rfl) ⟨652331, by rfl⟩ : syracuseStep 869775 = 1304663) B1304663
theorem B869819 : Blo 868566 869819 := bstep (se 1 (by rfl) ⟨652364, by rfl⟩ : syracuseStep 869819 = 1304729) B1304729
theorem B15058385 : Blo 868566 15058385 := bstep (se 2 (by rfl) ⟨5646894, by rfl⟩ : syracuseStep 15058385 = 11293789) B11293789
theorem B6604253 : Blo 868566 6604253 := bstep (se 3 (by rfl) ⟨1238297, by rfl⟩ : syracuseStep 6604253 = 2476595) B2476595
theorem B869895 : Blo 868566 869895 := bstep (se 1 (by rfl) ⟨652421, by rfl⟩ : syracuseStep 869895 = 1304843) B1304843
theorem B869903 : Blo 868566 869903 := bstep (se 1 (by rfl) ⟨652427, by rfl⟩ : syracuseStep 869903 = 1304855) B1304855
theorem B869947 : Blo 868566 869947 := bstep (se 1 (by rfl) ⟨652460, by rfl⟩ : syracuseStep 869947 = 1304921) B1304921
theorem B1656379 : Blo 868566 1656379 := bstep (se 1 (by rfl) ⟨1242284, by rfl⟩ : syracuseStep 1656379 = 2484569) B2484569
theorem B2934359 : Blo 868566 2934359 := bstep (se 1 (by rfl) ⟨2200769, by rfl⟩ : syracuseStep 2934359 = 4401539) B4401539
theorem B870023 : Blo 868566 870023 := bstep (se 1 (by rfl) ⟨652517, by rfl⟩ : syracuseStep 870023 = 1305035) B1305035
theorem B870031 : Blo 868566 870031 := bstep (se 1 (by rfl) ⟨652523, by rfl⟩ : syracuseStep 870031 = 1305047) B1305047
theorem B870075 : Blo 868566 870075 := bstep (se 1 (by rfl) ⟨652556, by rfl⟩ : syracuseStep 870075 = 1305113) B1305113
theorem B870151 : Blo 868566 870151 := bstep (se 1 (by rfl) ⟨652613, by rfl⟩ : syracuseStep 870151 = 1305227) B1305227
theorem B870159 : Blo 868566 870159 := bstep (se 1 (by rfl) ⟨652619, by rfl⟩ : syracuseStep 870159 = 1305239) B1305239
theorem B870203 : Blo 868566 870203 := bstep (se 1 (by rfl) ⟨652652, by rfl⟩ : syracuseStep 870203 = 1305305) B1305305
theorem B8931161 : Blo 868566 8931161 := bstep (se 2 (by rfl) ⟨3349185, by rfl⟩ : syracuseStep 8931161 = 6698371) B6698371
theorem B870279 : Blo 868566 870279 := bstep (se 1 (by rfl) ⟨652709, by rfl⟩ : syracuseStep 870279 = 1305419) B1305419
theorem B870287 : Blo 868566 870287 := bstep (se 1 (by rfl) ⟨652715, by rfl⟩ : syracuseStep 870287 = 1305431) B1305431
theorem B870331 : Blo 868566 870331 := bstep (se 1 (by rfl) ⟨652748, by rfl⟩ : syracuseStep 870331 = 1305497) B1305497
theorem B870407 : Blo 868566 870407 := bstep (se 1 (by rfl) ⟨652805, by rfl⟩ : syracuseStep 870407 = 1305611) B1305611
theorem B870415 : Blo 868566 870415 := bstep (se 1 (by rfl) ⟨652811, by rfl⟩ : syracuseStep 870415 = 1305623) B1305623
theorem B870459 : Blo 868566 870459 := bstep (se 1 (by rfl) ⟨652844, by rfl⟩ : syracuseStep 870459 = 1305689) B1305689
theorem B2934845 : Blo 868566 2934845 := bstep (se 3 (by rfl) ⟨550283, by rfl⟩ : syracuseStep 2934845 = 1100567) B1100567
theorem B870535 : Blo 868566 870535 := bstep (se 1 (by rfl) ⟨652901, by rfl⟩ : syracuseStep 870535 = 1305803) B1305803
theorem B1099919 : Blo 868566 1099919 := bstep (se 1 (by rfl) ⟨824939, by rfl⟩ : syracuseStep 1099919 = 1649879) B1649879
theorem B870543 : Blo 868566 870543 := bstep (se 1 (by rfl) ⟨652907, by rfl⟩ : syracuseStep 870543 = 1305815) B1305815
theorem B870587 : Blo 868566 870587 := bstep (se 1 (by rfl) ⟨652940, by rfl⟩ : syracuseStep 870587 = 1305881) B1305881
theorem B870663 : Blo 868566 870663 := bstep (se 1 (by rfl) ⟨652997, by rfl⟩ : syracuseStep 870663 = 1305995) B1305995
theorem B870671 : Blo 868566 870671 := bstep (se 1 (by rfl) ⟨653003, by rfl⟩ : syracuseStep 870671 = 1306007) B1306007
theorem B870715 : Blo 868566 870715 := bstep (se 1 (by rfl) ⟨653036, by rfl⟩ : syracuseStep 870715 = 1306073) B1306073
theorem B2476403 : Blo 868566 2476403 := bstep (se 1 (by rfl) ⟨1857302, by rfl⟩ : syracuseStep 2476403 = 3714605) B3714605
theorem B4704647 : Blo 868566 4704647 := bstep (se 1 (by rfl) ⟨3528485, by rfl⟩ : syracuseStep 4704647 = 7056971) B7056971
theorem B870791 : Blo 868566 870791 := bstep (se 1 (by rfl) ⟨653093, by rfl⟩ : syracuseStep 870791 = 1306187) B1306187
theorem B870799 : Blo 868566 870799 := bstep (se 1 (by rfl) ⟨653099, by rfl⟩ : syracuseStep 870799 = 1306199) B1306199
theorem B870843 : Blo 868566 870843 := bstep (se 1 (by rfl) ⟨653132, by rfl⟩ : syracuseStep 870843 = 1306265) B1306265
theorem B4966859 : Blo 868566 4966859 := bstep (se 1 (by rfl) ⟨3725144, by rfl⟩ : syracuseStep 4966859 = 7450289) B7450289
theorem B870919 : Blo 868566 870919 := bstep (se 1 (by rfl) ⟨653189, by rfl⟩ : syracuseStep 870919 = 1306379) B1306379
theorem B870927 : Blo 868566 870927 := bstep (se 1 (by rfl) ⟨653195, by rfl⟩ : syracuseStep 870927 = 1306391) B1306391
theorem B870971 : Blo 868566 870971 := bstep (se 1 (by rfl) ⟨653228, by rfl⟩ : syracuseStep 870971 = 1306457) B1306457
theorem B2509373 : Blo 868566 2509373 := bstep (se 3 (by rfl) ⟨470507, by rfl⟩ : syracuseStep 2509373 = 941015) B941015
theorem B871047 : Blo 868566 871047 := bstep (se 1 (by rfl) ⟨653285, by rfl⟩ : syracuseStep 871047 = 1306571) B1306571
theorem B871055 : Blo 868566 871055 := bstep (se 1 (by rfl) ⟨653291, by rfl⟩ : syracuseStep 871055 = 1306583) B1306583
theorem B871099 : Blo 868566 871099 := bstep (se 1 (by rfl) ⟨653324, by rfl⟩ : syracuseStep 871099 = 1306649) B1306649
theorem B4246253 : Blo 868566 4246253 := bstep (se 3 (by rfl) ⟨796172, by rfl⟩ : syracuseStep 4246253 = 1592345) B1592345
theorem B871175 : Blo 868566 871175 := bstep (se 1 (by rfl) ⟨653381, by rfl⟩ : syracuseStep 871175 = 1306763) B1306763
theorem B871183 : Blo 868566 871183 := bstep (se 1 (by rfl) ⟨653387, by rfl⟩ : syracuseStep 871183 = 1306775) B1306775
theorem B871227 : Blo 868566 871227 := bstep (se 1 (by rfl) ⟨653420, by rfl⟩ : syracuseStep 871227 = 1306841) B1306841
theorem B871303 : Blo 868566 871303 := bstep (se 1 (by rfl) ⟨653477, by rfl⟩ : syracuseStep 871303 = 1306955) B1306955
theorem B871311 : Blo 868566 871311 := bstep (se 1 (by rfl) ⟨653483, by rfl⟩ : syracuseStep 871311 = 1306967) B1306967
theorem B4967315 : Blo 868566 4967315 := bstep (se 1 (by rfl) ⟨3725486, by rfl⟩ : syracuseStep 4967315 = 7450973) B7450973
theorem B871355 : Blo 868566 871355 := bstep (se 1 (by rfl) ⟨653516, by rfl⟩ : syracuseStep 871355 = 1307033) B1307033
theorem B871431 : Blo 868566 871431 := bstep (se 1 (by rfl) ⟨653573, by rfl⟩ : syracuseStep 871431 = 1307147) B1307147
theorem B871439 : Blo 868566 871439 := bstep (se 1 (by rfl) ⟨653579, by rfl⟩ : syracuseStep 871439 = 1307159) B1307159
theorem B871483 : Blo 868566 871483 := bstep (se 1 (by rfl) ⟨653612, by rfl⟩ : syracuseStep 871483 = 1307225) B1307225
theorem B871559 : Blo 868566 871559 := bstep (se 1 (by rfl) ⟨653669, by rfl⟩ : syracuseStep 871559 = 1307339) B1307339
theorem B871567 : Blo 868566 871567 := bstep (se 1 (by rfl) ⟨653675, by rfl⟩ : syracuseStep 871567 = 1307351) B1307351
theorem B871611 : Blo 868566 871611 := bstep (se 1 (by rfl) ⟨653708, by rfl⟩ : syracuseStep 871611 = 1307417) B1307417
theorem B871687 : Blo 868566 871687 := bstep (se 1 (by rfl) ⟨653765, by rfl⟩ : syracuseStep 871687 = 1307531) B1307531
theorem B871695 : Blo 868566 871695 := bstep (se 1 (by rfl) ⟨653771, by rfl⟩ : syracuseStep 871695 = 1307543) B1307543
theorem B871739 : Blo 868566 871739 := bstep (se 1 (by rfl) ⟨653804, by rfl⟩ : syracuseStep 871739 = 1307609) B1307609
theorem B871815 : Blo 868566 871815 := bstep (se 1 (by rfl) ⟨653861, by rfl⟩ : syracuseStep 871815 = 1307723) B1307723
theorem B871823 : Blo 868566 871823 := bstep (se 1 (by rfl) ⟨653867, by rfl⟩ : syracuseStep 871823 = 1307735) B1307735
theorem B2936249 : Blo 868566 2936249 := bstep (se 2 (by rfl) ⟨1101093, by rfl⟩ : syracuseStep 2936249 = 2202187) B2202187
theorem B871867 : Blo 868566 871867 := bstep (se 1 (by rfl) ⟨653900, by rfl⟩ : syracuseStep 871867 = 1307801) B1307801
theorem B9915857 : Blo 868566 9915857 := bstep (se 2 (by rfl) ⟨3718446, by rfl⟩ : syracuseStep 9915857 = 7436893) B7436893
theorem B871943 : Blo 868566 871943 := bstep (se 1 (by rfl) ⟨653957, by rfl⟩ : syracuseStep 871943 = 1307915) B1307915
theorem B871951 : Blo 868566 871951 := bstep (se 1 (by rfl) ⟨653963, by rfl⟩ : syracuseStep 871951 = 1307927) B1307927
theorem B871995 : Blo 868566 871995 := bstep (se 1 (by rfl) ⟨653996, by rfl⟩ : syracuseStep 871995 = 1307993) B1307993
theorem B872071 : Blo 868566 872071 := bstep (se 1 (by rfl) ⟨654053, by rfl⟩ : syracuseStep 872071 = 1308107) B1308107
theorem B872079 : Blo 868566 872079 := bstep (se 1 (by rfl) ⟨654059, by rfl⟩ : syracuseStep 872079 = 1308119) B1308119
theorem B872123 : Blo 868566 872123 := bstep (se 1 (by rfl) ⟨654092, by rfl⟩ : syracuseStep 872123 = 1308185) B1308185
theorem B872199 : Blo 868566 872199 := bstep (se 1 (by rfl) ⟨654149, by rfl⟩ : syracuseStep 872199 = 1308299) B1308299
theorem B872207 : Blo 868566 872207 := bstep (se 1 (by rfl) ⟨654155, by rfl⟩ : syracuseStep 872207 = 1308311) B1308311
theorem B872251 : Blo 868566 872251 := bstep (se 1 (by rfl) ⟨654188, by rfl⟩ : syracuseStep 872251 = 1308377) B1308377
theorem B872327 : Blo 868566 872327 := bstep (se 1 (by rfl) ⟨654245, by rfl⟩ : syracuseStep 872327 = 1308491) B1308491
theorem B872335 : Blo 868566 872335 := bstep (se 1 (by rfl) ⟨654251, by rfl⟩ : syracuseStep 872335 = 1308503) B1308503
theorem B872379 : Blo 868566 872379 := bstep (se 1 (by rfl) ⟨654284, by rfl⟩ : syracuseStep 872379 = 1308569) B1308569
theorem B872455 : Blo 868566 872455 := bstep (se 1 (by rfl) ⟨654341, by rfl⟩ : syracuseStep 872455 = 1308683) B1308683
theorem B2936843 : Blo 868566 2936843 := bstep (se 1 (by rfl) ⟨2202632, by rfl⟩ : syracuseStep 2936843 = 4405265) B4405265
theorem B872463 : Blo 868566 872463 := bstep (se 1 (by rfl) ⟨654347, by rfl⟩ : syracuseStep 872463 = 1308695) B1308695
theorem B4411421 : Blo 868566 4411421 := bstep (se 3 (by rfl) ⟨827141, by rfl⟩ : syracuseStep 4411421 = 1654283) B1654283
theorem B872507 : Blo 868566 872507 := bstep (se 1 (by rfl) ⟨654380, by rfl⟩ : syracuseStep 872507 = 1308761) B1308761
theorem B2936951 : Blo 868566 2936951 := bstep (se 1 (by rfl) ⟨2202713, by rfl⟩ : syracuseStep 2936951 = 4405427) B4405427
theorem B4411907 : Blo 868566 4411907 := bstep (se 1 (by rfl) ⟨3308930, by rfl⟩ : syracuseStep 4411907 = 6617861) B6617861
theorem B1397263 : Blo 868566 1397263 := bstep (se 1 (by rfl) ⟨1047947, by rfl⟩ : syracuseStep 1397263 = 2095895) B2095895
theorem B1954439 : Blo 868566 1954439 := bstep (se 1 (by rfl) ⟨1465829, by rfl⟩ : syracuseStep 1954439 = 2931659) B2931659
theorem B2937545 : Blo 868566 2937545 := bstep (se 2 (by rfl) ⟨1101579, by rfl⟩ : syracuseStep 2937545 = 2203159) B2203159
theorem B2478863 : Blo 868566 2478863 := bstep (se 1 (by rfl) ⟨1859147, by rfl⟩ : syracuseStep 2478863 = 3718295) B3718295
theorem B2347805 : Blo 868566 2347805 := bstep (se 3 (by rfl) ⟨440213, by rfl⟩ : syracuseStep 2347805 = 880427) B880427
theorem B1954619 : Blo 868566 1954619 := bstep (se 1 (by rfl) ⟨1465964, by rfl⟩ : syracuseStep 1954619 = 2931929) B2931929
theorem B1954745 : Blo 868566 1954745 := bstep (se 2 (by rfl) ⟨733029, by rfl⟩ : syracuseStep 1954745 = 1466059) B1466059
theorem B1102891 : Blo 868566 1102891 := bstep (se 1 (by rfl) ⟨827168, by rfl⟩ : syracuseStep 1102891 = 1654337) B1654337
theorem B3298391 : Blo 868566 3298391 := bstep (se 1 (by rfl) ⟨2473793, by rfl⟩ : syracuseStep 3298391 = 4947587) B4947587
theorem B10573001 : Blo 868566 10573001 := bstep (se 2 (by rfl) ⟨3964875, by rfl⟩ : syracuseStep 10573001 = 7929751) B7929751
theorem B1955087 : Blo 868566 1955087 := bstep (se 1 (by rfl) ⟨1466315, by rfl⟩ : syracuseStep 1955087 = 2932631) B2932631
theorem B1955105 : Blo 868566 1955105 := bstep (se 2 (by rfl) ⟨733164, by rfl⟩ : syracuseStep 1955105 = 1466329) B1466329
theorem B2938247 : Blo 868566 2938247 := bstep (se 1 (by rfl) ⟨2203685, by rfl⟩ : syracuseStep 2938247 = 4407371) B4407371
theorem B4707719 : Blo 868566 4707719 := bstep (se 1 (by rfl) ⟨3530789, by rfl⟩ : syracuseStep 4707719 = 7061579) B7061579
theorem B5952953 : Blo 868566 5952953 := bstep (se 2 (by rfl) ⟨2232357, by rfl⟩ : syracuseStep 5952953 = 4464715) B4464715
theorem B3135019 : Blo 868566 3135019 := bstep (se 1 (by rfl) ⟨2351264, by rfl⟩ : syracuseStep 3135019 = 4702529) B4702529
theorem B3298877 : Blo 868566 3298877 := bstep (se 3 (by rfl) ⟨618539, by rfl⟩ : syracuseStep 3298877 = 1237079) B1237079
theorem B1955447 : Blo 868566 1955447 := bstep (se 1 (by rfl) ⟨1466585, by rfl⟩ : syracuseStep 1955447 = 2933171) B2933171
theorem B2938625 : Blo 868566 2938625 := bstep (se 2 (by rfl) ⟨1101984, by rfl⟩ : syracuseStep 2938625 = 2203969) B2203969
theorem B2348833 : Blo 868566 2348833 := bstep (se 2 (by rfl) ⟨880812, by rfl⟩ : syracuseStep 2348833 = 1761625) B1761625
theorem B1955627 : Blo 868566 1955627 := bstep (se 1 (by rfl) ⟨1466720, by rfl⟩ : syracuseStep 1955627 = 2933441) B2933441
theorem B9426851 : Blo 868566 9426851 := bstep (se 1 (by rfl) ⟨7070138, by rfl⟩ : syracuseStep 9426851 = 14140277) B14140277
theorem B1103863 : Blo 868566 1103863 := bstep (se 1 (by rfl) ⟨827897, by rfl⟩ : syracuseStep 1103863 = 1655795) B1655795
theorem B16766999 : Blo 868566 16766999 := bstep (se 1 (by rfl) ⟨12575249, by rfl⟩ : syracuseStep 16766999 = 25150499) B25150499
theorem B4413527 : Blo 868566 4413527 := bstep (se 1 (by rfl) ⟨3310145, by rfl⟩ : syracuseStep 4413527 = 6620291) B6620291
theorem B10049669 : Blo 868566 10049669 := bstep (se 4 (by rfl) ⟨942156, by rfl⟩ : syracuseStep 10049669 = 1884313) B1884313
theorem B2644103 : Blo 868566 2644103 := bstep (se 1 (by rfl) ⟨1983077, by rfl⟩ : syracuseStep 2644103 = 3966155) B3966155
theorem B1955987 : Blo 868566 1955987 := bstep (se 1 (by rfl) ⟨1466990, by rfl⟩ : syracuseStep 1955987 = 2933981) B2933981
theorem B1956041 : Blo 868566 1956041 := bstep (se 2 (by rfl) ⟨733515, by rfl⟩ : syracuseStep 1956041 = 1467031) B1467031
theorem B16963829 : Blo 868566 16963829 := bstep (se 5 (by rfl) ⟨795179, by rfl⟩ : syracuseStep 16963829 = 1590359) B1590359
theorem B1104187 : Blo 868566 1104187 := bstep (se 1 (by rfl) ⟨828140, by rfl⟩ : syracuseStep 1104187 = 1656281) B1656281
theorem B2480503 : Blo 868566 2480503 := bstep (se 1 (by rfl) ⟨1860377, by rfl⟩ : syracuseStep 2480503 = 3720755) B3720755
theorem B47569301 : Blo 868566 47569301 := bstep (se 6 (by rfl) ⟨1114905, by rfl⟩ : syracuseStep 47569301 = 2229811) B2229811
theorem B2480537 : Blo 868566 2480537 := bstep (se 2 (by rfl) ⟨930201, by rfl⟩ : syracuseStep 2480537 = 1860403) B1860403
theorem B2480651 : Blo 868566 2480651 := bstep (se 1 (by rfl) ⟨1860488, by rfl⟩ : syracuseStep 2480651 = 3720977) B3720977
theorem B2939435 : Blo 868566 2939435 := bstep (se 1 (by rfl) ⟨2204576, by rfl⟩ : syracuseStep 2939435 = 4409153) B4409153
theorem B4414013 : Blo 868566 4414013 := bstep (se 3 (by rfl) ⟨827627, by rfl⟩ : syracuseStep 4414013 = 1655255) B1655255
theorem B20142863 : Blo 868566 20142863 := bstep (se 1 (by rfl) ⟨15107147, by rfl⟩ : syracuseStep 20142863 = 30214295) B30214295
theorem B1956743 : Blo 868566 1956743 := bstep (se 1 (by rfl) ⟨1467557, by rfl⟩ : syracuseStep 1956743 = 2935115) B2935115
theorem B3136391 : Blo 868566 3136391 := bstep (se 1 (by rfl) ⟨2352293, by rfl⟩ : syracuseStep 3136391 = 4704587) B4704587
theorem B1989647 : Blo 868566 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B1956923 : Blo 868566 1956923 := bstep (se 1 (by rfl) ⟨1467692, by rfl⟩ : syracuseStep 1956923 = 2935385) B2935385
theorem B1957049 : Blo 868566 1957049 := bstep (se 2 (by rfl) ⟨733893, by rfl⟩ : syracuseStep 1957049 = 1467787) B1467787
theorem B1858745 : Blo 868566 1858745 := bstep (se 2 (by rfl) ⟨697029, by rfl⟩ : syracuseStep 1858745 = 1394059) B1394059
theorem B1465735 : Blo 868566 1465735 := bstep (se 1 (by rfl) ⟨1099301, by rfl⟩ : syracuseStep 1465735 = 2198603) B2198603
theorem B1957391 : Blo 868566 1957391 := bstep (se 1 (by rfl) ⟨1468043, by rfl⟩ : syracuseStep 1957391 = 2936087) B2936087
theorem B1859087 : Blo 868566 1859087 := bstep (se 1 (by rfl) ⟨1394315, by rfl⟩ : syracuseStep 1859087 = 2788631) B2788631
theorem B1957409 : Blo 868566 1957409 := bstep (se 2 (by rfl) ⟨734028, by rfl⟩ : syracuseStep 1957409 = 1468057) B1468057
theorem B1859105 : Blo 868566 1859105 := bstep (se 2 (by rfl) ⟨697164, by rfl⟩ : syracuseStep 1859105 = 1394329) B1394329
theorem B2481779 : Blo 868566 2481779 := bstep (se 1 (by rfl) ⟨1861334, by rfl⟩ : syracuseStep 2481779 = 3722669) B3722669
theorem B2940731 : Blo 868566 2940731 := bstep (se 1 (by rfl) ⟨2205548, by rfl⟩ : syracuseStep 2940731 = 4411097) B4411097
theorem B1957751 : Blo 868566 1957751 := bstep (se 1 (by rfl) ⟨1468313, by rfl⟩ : syracuseStep 1957751 = 2936627) B2936627
theorem B2482177 : Blo 868566 2482177 := bstep (se 2 (by rfl) ⟨930816, by rfl⟩ : syracuseStep 2482177 = 1861633) B1861633
theorem B1466383 : Blo 868566 1466383 := bstep (se 1 (by rfl) ⟨1099787, by rfl⟩ : syracuseStep 1466383 = 2199575) B2199575
theorem B1957931 : Blo 868566 1957931 := bstep (se 1 (by rfl) ⟨1468448, by rfl⟩ : syracuseStep 1957931 = 2936897) B2936897
theorem B2482235 : Blo 868566 2482235 := bstep (se 1 (by rfl) ⟨1861676, by rfl⟩ : syracuseStep 2482235 = 3723353) B3723353
theorem B4186313 : Blo 868566 4186313 := bstep (se 2 (by rfl) ⟨1569867, by rfl⟩ : syracuseStep 4186313 = 3139735) B3139735
theorem B2941217 : Blo 868566 2941217 := bstep (se 2 (by rfl) ⟨1102956, by rfl⟩ : syracuseStep 2941217 = 2205913) B2205913
theorem B4415795 : Blo 868566 4415795 := bstep (se 1 (by rfl) ⟨3311846, by rfl⟩ : syracuseStep 4415795 = 6623693) B6623693
theorem B1302857 : Blo 868566 1302857 := bstep (se 2 (by rfl) ⟨488571, by rfl⟩ : syracuseStep 1302857 = 977143) B977143
theorem B2646391 : Blo 868566 2646391 := bstep (se 1 (by rfl) ⟨1984793, by rfl⟩ : syracuseStep 2646391 = 3969587) B3969587
theorem B1958291 : Blo 868566 1958291 := bstep (se 1 (by rfl) ⟨1468718, by rfl⟩ : syracuseStep 1958291 = 2937437) B2937437
theorem B1302971 : Blo 868566 1302971 := bstep (se 1 (by rfl) ⟨977228, by rfl⟩ : syracuseStep 1302971 = 1954457) B1954457
theorem B2089417 : Blo 868566 2089417 := bstep (se 2 (by rfl) ⟨783531, by rfl⟩ : syracuseStep 2089417 = 1567063) B1567063
theorem B1958345 : Blo 868566 1958345 := bstep (se 2 (by rfl) ⟨734379, by rfl⟩ : syracuseStep 1958345 = 1468759) B1468759
theorem B1303031 : Blo 868566 1303031 := bstep (se 1 (by rfl) ⟨977273, by rfl⟩ : syracuseStep 1303031 = 1954547) B1954547
theorem B1303055 : Blo 868566 1303055 := bstep (se 1 (by rfl) ⟨977291, by rfl⟩ : syracuseStep 1303055 = 1954583) B1954583
theorem B1466923 : Blo 868566 1466923 := bstep (se 1 (by rfl) ⟨1100192, by rfl⟩ : syracuseStep 1466923 = 2200385) B2200385
theorem B1303097 : Blo 868566 1303097 := bstep (se 2 (by rfl) ⟨488661, by rfl⟩ : syracuseStep 1303097 = 977323) B977323
theorem B4416119 : Blo 868566 4416119 := bstep (se 1 (by rfl) ⟨3312089, by rfl⟩ : syracuseStep 4416119 = 6624179) B6624179
theorem B1303175 : Blo 868566 1303175 := bstep (se 1 (by rfl) ⟨977381, by rfl⟩ : syracuseStep 1303175 = 1954763) B1954763
theorem B1303211 : Blo 868566 1303211 := bstep (se 1 (by rfl) ⟨977408, by rfl⟩ : syracuseStep 1303211 = 1954817) B1954817
theorem B1467065 : Blo 868566 1467065 := bstep (se 2 (by rfl) ⟨550149, by rfl⟩ : syracuseStep 1467065 = 1100299) B1100299
theorem B1303241 : Blo 868566 1303241 := bstep (se 2 (by rfl) ⟨488715, by rfl⟩ : syracuseStep 1303241 = 977431) B977431
theorem B9429797 : Blo 868566 9429797 := bstep (se 4 (by rfl) ⟨884043, by rfl⟩ : syracuseStep 9429797 = 1768087) B1768087
theorem B8938291 : Blo 868566 8938291 := bstep (se 1 (by rfl) ⟨6703718, by rfl⟩ : syracuseStep 8938291 = 13407437) B13407437
theorem B1303355 : Blo 868566 1303355 := bstep (se 1 (by rfl) ⟨977516, by rfl⟩ : syracuseStep 1303355 = 1955033) B1955033
theorem B2941811 : Blo 868566 2941811 := bstep (se 1 (by rfl) ⟨2206358, by rfl⟩ : syracuseStep 2941811 = 4412717) B4412717
theorem B1303415 : Blo 868566 1303415 := bstep (se 1 (by rfl) ⟨977561, by rfl⟩ : syracuseStep 1303415 = 1955123) B1955123
theorem B3302279 : Blo 868566 3302279 := bstep (se 1 (by rfl) ⟨2476709, by rfl⟩ : syracuseStep 3302279 = 4953419) B4953419
theorem B1303439 : Blo 868566 1303439 := bstep (se 1 (by rfl) ⟨977579, by rfl⟩ : syracuseStep 1303439 = 1955159) B1955159
theorem B1303481 : Blo 868566 1303481 := bstep (se 2 (by rfl) ⟨488805, by rfl⟩ : syracuseStep 1303481 = 977611) B977611
theorem B1237945 : Blo 868566 1237945 := bstep (se 2 (by rfl) ⟨464229, by rfl⟩ : syracuseStep 1237945 = 928459) B928459
theorem B1303559 : Blo 868566 1303559 := bstep (se 1 (by rfl) ⟨977669, by rfl⟩ : syracuseStep 1303559 = 1955339) B1955339
theorem B943111 : Blo 868566 943111 := bstep (se 1 (by rfl) ⟨707333, by rfl⟩ : syracuseStep 943111 = 1414667) B1414667
theorem B1303595 : Blo 868566 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B6612029 : Blo 868566 6612029 := bstep (se 3 (by rfl) ⟨1239755, by rfl⟩ : syracuseStep 6612029 = 2479511) B2479511
theorem B1303625 : Blo 868566 1303625 := bstep (se 2 (by rfl) ⟨488859, by rfl⟩ : syracuseStep 1303625 = 977719) B977719
theorem B1860727 : Blo 868566 1860727 := bstep (se 1 (by rfl) ⟨1395545, by rfl⟩ : syracuseStep 1860727 = 2791091) B2791091
theorem B1959047 : Blo 868566 1959047 := bstep (se 1 (by rfl) ⟨1469285, by rfl⟩ : syracuseStep 1959047 = 2938571) B2938571
theorem B1303739 : Blo 868566 1303739 := bstep (se 1 (by rfl) ⟨977804, by rfl⟩ : syracuseStep 1303739 = 1955609) B1955609
theorem B7070921 : Blo 868566 7070921 := bstep (se 2 (by rfl) ⟨2651595, by rfl⟩ : syracuseStep 7070921 = 5303191) B5303191
theorem B1303799 : Blo 868566 1303799 := bstep (se 1 (by rfl) ⟨977849, by rfl⟩ : syracuseStep 1303799 = 1955699) B1955699
theorem B551380229 : Blo 868566 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B1303823 : Blo 868566 1303823 := bstep (se 1 (by rfl) ⟨977867, by rfl⟩ : syracuseStep 1303823 = 1955735) B1955735
theorem B1303865 : Blo 868566 1303865 := bstep (se 2 (by rfl) ⟨488949, by rfl⟩ : syracuseStep 1303865 = 977899) B977899
theorem B1959227 : Blo 868566 1959227 := bstep (se 1 (by rfl) ⟨1469420, by rfl⟩ : syracuseStep 1959227 = 2938841) B2938841
theorem B1467767 : Blo 868566 1467767 := bstep (se 1 (by rfl) ⟨1100825, by rfl⟩ : syracuseStep 1467767 = 2201651) B2201651
theorem B1303943 : Blo 868566 1303943 := bstep (se 1 (by rfl) ⟨977957, by rfl⟩ : syracuseStep 1303943 = 1955915) B1955915
theorem B1303979 : Blo 868566 1303979 := bstep (se 1 (by rfl) ⟨977984, by rfl⟩ : syracuseStep 1303979 = 1955969) B1955969
theorem B1959353 : Blo 868566 1959353 := bstep (se 2 (by rfl) ⟨734757, by rfl⟩ : syracuseStep 1959353 = 1469515) B1469515
theorem B1304009 : Blo 868566 1304009 := bstep (se 2 (by rfl) ⟨489003, by rfl⟩ : syracuseStep 1304009 = 978007) B978007
theorem B14116355 : Blo 868566 14116355 := bstep (se 1 (by rfl) ⟨10587266, by rfl⟩ : syracuseStep 14116355 = 21174533) B21174533
theorem B16934429 : Blo 868566 16934429 := bstep (se 3 (by rfl) ⟨3175205, by rfl⟩ : syracuseStep 16934429 = 6350411) B6350411
theorem B1304123 : Blo 868566 1304123 := bstep (se 1 (by rfl) ⟨978092, by rfl⟩ : syracuseStep 1304123 = 1956185) B1956185
theorem B4417091 : Blo 868566 4417091 := bstep (se 1 (by rfl) ⟨3312818, by rfl⟩ : syracuseStep 4417091 = 6625637) B6625637
theorem B1304183 : Blo 868566 1304183 := bstep (se 1 (by rfl) ⟨978137, by rfl⟩ : syracuseStep 1304183 = 1956275) B1956275
theorem B1304207 : Blo 868566 1304207 := bstep (se 1 (by rfl) ⟨978155, by rfl⟩ : syracuseStep 1304207 = 1956311) B1956311
theorem B1304249 : Blo 868566 1304249 := bstep (se 2 (by rfl) ⟨489093, by rfl⟩ : syracuseStep 1304249 = 978187) B978187
theorem B1304327 : Blo 868566 1304327 := bstep (se 1 (by rfl) ⟨978245, by rfl⟩ : syracuseStep 1304327 = 1956491) B1956491
theorem B1959695 : Blo 868566 1959695 := bstep (se 1 (by rfl) ⟨1469771, by rfl⟩ : syracuseStep 1959695 = 2939543) B2939543
theorem B1959713 : Blo 868566 1959713 := bstep (se 2 (by rfl) ⟨734892, by rfl⟩ : syracuseStep 1959713 = 1469785) B1469785
theorem B1304363 : Blo 868566 1304363 := bstep (se 1 (by rfl) ⟨978272, by rfl⟩ : syracuseStep 1304363 = 1956545) B1956545
theorem B1468219 : Blo 868566 1468219 := bstep (se 1 (by rfl) ⟨1101164, by rfl⟩ : syracuseStep 1468219 = 2202329) B2202329
theorem B1304393 : Blo 868566 1304393 := bstep (se 2 (by rfl) ⟨489147, by rfl⟩ : syracuseStep 1304393 = 978295) B978295
theorem B1304507 : Blo 868566 1304507 := bstep (se 1 (by rfl) ⟨978380, by rfl⟩ : syracuseStep 1304507 = 1956761) B1956761
theorem B1468361 : Blo 868566 1468361 := bstep (se 2 (by rfl) ⟨550635, by rfl⟩ : syracuseStep 1468361 = 1101271) B1101271
theorem B1304567 : Blo 868566 1304567 := bstep (se 1 (by rfl) ⟨978425, by rfl⟩ : syracuseStep 1304567 = 1956851) B1956851
theorem B1304591 : Blo 868566 1304591 := bstep (se 1 (by rfl) ⟨978443, by rfl⟩ : syracuseStep 1304591 = 1956887) B1956887
theorem B1304633 : Blo 868566 1304633 := bstep (se 2 (by rfl) ⟨489237, by rfl⟩ : syracuseStep 1304633 = 978475) B978475
theorem B1960055 : Blo 868566 1960055 := bstep (se 1 (by rfl) ⟨1470041, by rfl⟩ : syracuseStep 1960055 = 2940083) B2940083
theorem B1304711 : Blo 868566 1304711 := bstep (se 1 (by rfl) ⟨978533, by rfl⟩ : syracuseStep 1304711 = 1957067) B1957067
theorem B1239175 : Blo 868566 1239175 := bstep (se 1 (by rfl) ⟨929381, by rfl⟩ : syracuseStep 1239175 = 1858763) B1858763
theorem B1304747 : Blo 868566 1304747 := bstep (se 1 (by rfl) ⟨978560, by rfl⟩ : syracuseStep 1304747 = 1957121) B1957121
theorem B1763513 : Blo 868566 1763513 := bstep (se 2 (by rfl) ⟨661317, by rfl⟩ : syracuseStep 1763513 = 1322635) B1322635
theorem B1304777 : Blo 868566 1304777 := bstep (se 2 (by rfl) ⟨489291, by rfl⟩ : syracuseStep 1304777 = 978583) B978583
theorem B1960235 : Blo 868566 1960235 := bstep (se 1 (by rfl) ⟨1470176, by rfl⟩ : syracuseStep 1960235 = 2940353) B2940353
theorem B2484523 : Blo 868566 2484523 := bstep (se 1 (by rfl) ⟨1863392, by rfl⟩ : syracuseStep 2484523 = 3726785) B3726785
theorem B1304891 : Blo 868566 1304891 := bstep (se 1 (by rfl) ⟨978668, by rfl⟩ : syracuseStep 1304891 = 1957337) B1957337
theorem B1304951 : Blo 868566 1304951 := bstep (se 1 (by rfl) ⟨978713, by rfl⟩ : syracuseStep 1304951 = 1957427) B1957427
theorem B977287 : Blo 868566 977287 := bstep (se 1 (by rfl) ⟨732965, by rfl⟩ : syracuseStep 977287 = 1465931) B1465931
theorem B1304975 : Blo 868566 1304975 := bstep (se 1 (by rfl) ⟨978731, by rfl⟩ : syracuseStep 1304975 = 1957463) B1957463
theorem B1305017 : Blo 868566 1305017 := bstep (se 2 (by rfl) ⟨489381, by rfl⟩ : syracuseStep 1305017 = 978763) B978763
theorem B1305095 : Blo 868566 1305095 := bstep (se 1 (by rfl) ⟨978821, by rfl⟩ : syracuseStep 1305095 = 1957643) B1957643
theorem B2484751 : Blo 868566 2484751 := bstep (se 1 (by rfl) ⟨1863563, by rfl⟩ : syracuseStep 2484751 = 3727127) B3727127
theorem B1305131 : Blo 868566 1305131 := bstep (se 1 (by rfl) ⟨978848, by rfl⟩ : syracuseStep 1305131 = 1957697) B1957697
theorem B977467 : Blo 868566 977467 := bstep (se 1 (by rfl) ⟨733100, by rfl⟩ : syracuseStep 977467 = 1466201) B1466201
theorem B1305161 : Blo 868566 1305161 := bstep (se 2 (by rfl) ⟨489435, by rfl⟩ : syracuseStep 1305161 = 978871) B978871
theorem B1469063 : Blo 868566 1469063 := bstep (se 1 (by rfl) ⟨1101797, by rfl⟩ : syracuseStep 1469063 = 2203595) B2203595
theorem B1960595 : Blo 868566 1960595 := bstep (se 1 (by rfl) ⟨1470446, by rfl⟩ : syracuseStep 1960595 = 2940893) B2940893
theorem B1862291 : Blo 868566 1862291 := bstep (se 1 (by rfl) ⟨1396718, by rfl⟩ : syracuseStep 1862291 = 2793437) B2793437
theorem B1305275 : Blo 868566 1305275 := bstep (se 1 (by rfl) ⟨978956, by rfl⟩ : syracuseStep 1305275 = 1957913) B1957913
theorem B19098305 : Blo 868566 19098305 := bstep (se 2 (by rfl) ⟨7161864, by rfl⟩ : syracuseStep 19098305 = 14323729) B14323729
theorem B1960649 : Blo 868566 1960649 := bstep (se 2 (by rfl) ⟨735243, by rfl⟩ : syracuseStep 1960649 = 1470487) B1470487
theorem B1305335 : Blo 868566 1305335 := bstep (se 1 (by rfl) ⟨979001, by rfl⟩ : syracuseStep 1305335 = 1958003) B1958003
theorem B1305359 : Blo 868566 1305359 := bstep (se 1 (by rfl) ⟨979019, by rfl⟩ : syracuseStep 1305359 = 1958039) B1958039
theorem B1305401 : Blo 868566 1305401 := bstep (se 2 (by rfl) ⟨489525, by rfl⟩ : syracuseStep 1305401 = 979051) B979051
theorem B1305479 : Blo 868566 1305479 := bstep (se 1 (by rfl) ⟨979109, by rfl⟩ : syracuseStep 1305479 = 1958219) B1958219
theorem B1305515 : Blo 868566 1305515 := bstep (se 1 (by rfl) ⟨979136, by rfl⟩ : syracuseStep 1305515 = 1958273) B1958273
theorem B1239995 : Blo 868566 1239995 := bstep (se 1 (by rfl) ⟨929996, by rfl⟩ : syracuseStep 1239995 = 1859993) B1859993
theorem B1305545 : Blo 868566 1305545 := bstep (se 2 (by rfl) ⟨489579, by rfl⟩ : syracuseStep 1305545 = 979159) B979159
theorem B977935 : Blo 868566 977935 := bstep (se 1 (by rfl) ⟨733451, by rfl⟩ : syracuseStep 977935 = 1466903) B1466903
theorem B1305659 : Blo 868566 1305659 := bstep (se 1 (by rfl) ⟨979244, by rfl⟩ : syracuseStep 1305659 = 1958489) B1958489
theorem B1305719 : Blo 868566 1305719 := bstep (se 1 (by rfl) ⟨979289, by rfl⟩ : syracuseStep 1305719 = 1958579) B1958579
theorem B1305743 : Blo 868566 1305743 := bstep (se 1 (by rfl) ⟨979307, by rfl⟩ : syracuseStep 1305743 = 1958615) B1958615
theorem B1305785 : Blo 868566 1305785 := bstep (se 2 (by rfl) ⟨489669, by rfl⟩ : syracuseStep 1305785 = 979339) B979339
theorem B1305863 : Blo 868566 1305863 := bstep (se 1 (by rfl) ⟨979397, by rfl⟩ : syracuseStep 1305863 = 1958795) B1958795
theorem B1469711 : Blo 868566 1469711 := bstep (se 1 (by rfl) ⟨1102283, by rfl⟩ : syracuseStep 1469711 = 2204567) B2204567
theorem B1305899 : Blo 868566 1305899 := bstep (se 1 (by rfl) ⟨979424, by rfl⟩ : syracuseStep 1305899 = 1958849) B1958849
theorem B1305929 : Blo 868566 1305929 := bstep (se 2 (by rfl) ⟨489723, by rfl⟩ : syracuseStep 1305929 = 979447) B979447
theorem B1240439 : Blo 868566 1240439 := bstep (se 1 (by rfl) ⟨930329, by rfl⟩ : syracuseStep 1240439 = 1860659) B1860659
theorem B1961351 : Blo 868566 1961351 := bstep (se 1 (by rfl) ⟨1471013, by rfl⟩ : syracuseStep 1961351 = 2942027) B2942027
theorem B2944403 : Blo 868566 2944403 := bstep (se 1 (by rfl) ⟨2208302, by rfl⟩ : syracuseStep 2944403 = 4416605) B4416605
theorem B1306043 : Blo 868566 1306043 := bstep (se 1 (by rfl) ⟨979532, by rfl⟩ : syracuseStep 1306043 = 1959065) B1959065
theorem B1306103 : Blo 868566 1306103 := bstep (se 1 (by rfl) ⟨979577, by rfl⟩ : syracuseStep 1306103 = 1959155) B1959155
theorem B978439 : Blo 868566 978439 := bstep (se 1 (by rfl) ⟨733829, by rfl⟩ : syracuseStep 978439 = 1467659) B1467659
theorem B1306127 : Blo 868566 1306127 := bstep (se 1 (by rfl) ⟨979595, by rfl⟩ : syracuseStep 1306127 = 1959191) B1959191
theorem B1306169 : Blo 868566 1306169 := bstep (se 2 (by rfl) ⟨489813, by rfl⟩ : syracuseStep 1306169 = 979627) B979627
theorem B1240633 : Blo 868566 1240633 := bstep (se 2 (by rfl) ⟨465237, by rfl⟩ : syracuseStep 1240633 = 930475) B930475
theorem B1961531 : Blo 868566 1961531 := bstep (se 1 (by rfl) ⟨1471148, by rfl⟩ : syracuseStep 1961531 = 2942297) B2942297
theorem B1306247 : Blo 868566 1306247 := bstep (se 1 (by rfl) ⟨979685, by rfl⟩ : syracuseStep 1306247 = 1959371) B1959371
theorem B1306283 : Blo 868566 1306283 := bstep (se 1 (by rfl) ⟨979712, by rfl⟩ : syracuseStep 1306283 = 1959425) B1959425
theorem B1961657 : Blo 868566 1961657 := bstep (se 2 (by rfl) ⟨735621, by rfl⟩ : syracuseStep 1961657 = 1471243) B1471243
theorem B978619 : Blo 868566 978619 := bstep (se 1 (by rfl) ⟨733964, by rfl⟩ : syracuseStep 978619 = 1467929) B1467929
theorem B1306313 : Blo 868566 1306313 := bstep (se 2 (by rfl) ⟨489867, by rfl⟩ : syracuseStep 1306313 = 979735) B979735
theorem B1470251 : Blo 868566 1470251 := bstep (se 1 (by rfl) ⟨1102688, by rfl⟩ : syracuseStep 1470251 = 2205377) B2205377
theorem B1306427 : Blo 868566 1306427 := bstep (se 1 (by rfl) ⟨979820, by rfl⟩ : syracuseStep 1306427 = 1959641) B1959641
theorem B1306487 : Blo 868566 1306487 := bstep (se 1 (by rfl) ⟨979865, by rfl⟩ : syracuseStep 1306487 = 1959731) B1959731
theorem B1306511 : Blo 868566 1306511 := bstep (se 1 (by rfl) ⟨979883, by rfl⟩ : syracuseStep 1306511 = 1959767) B1959767
theorem B1306553 : Blo 868566 1306553 := bstep (se 2 (by rfl) ⟨489957, by rfl⟩ : syracuseStep 1306553 = 979915) B979915
theorem B1306631 : Blo 868566 1306631 := bstep (se 1 (by rfl) ⟨979973, by rfl⟩ : syracuseStep 1306631 = 1959947) B1959947
theorem B1961999 : Blo 868566 1961999 := bstep (se 1 (by rfl) ⟨1471499, by rfl⟩ : syracuseStep 1961999 = 2942999) B2942999
theorem B11300887 : Blo 868566 11300887 := bstep (se 1 (by rfl) ⟨8475665, by rfl⟩ : syracuseStep 11300887 = 16951331) B16951331
theorem B1962017 : Blo 868566 1962017 := bstep (se 2 (by rfl) ⟨735756, by rfl⟩ : syracuseStep 1962017 = 1471513) B1471513
theorem B1306667 : Blo 868566 1306667 := bstep (se 1 (by rfl) ⟨980000, by rfl⟩ : syracuseStep 1306667 = 1960001) B1960001
theorem B4190251 : Blo 868566 4190251 := bstep (se 1 (by rfl) ⟨3142688, by rfl⟩ : syracuseStep 4190251 = 6285377) B6285377
theorem B1306697 : Blo 868566 1306697 := bstep (se 2 (by rfl) ⟨490011, by rfl⟩ : syracuseStep 1306697 = 980023) B980023
theorem B979087 : Blo 868566 979087 := bstep (se 1 (by rfl) ⟨734315, by rfl⟩ : syracuseStep 979087 = 1468631) B1468631
theorem B1470649 : Blo 868566 1470649 := bstep (se 2 (by rfl) ⟨551493, by rfl⟩ : syracuseStep 1470649 = 1102987) B1102987
theorem B1306811 : Blo 868566 1306811 := bstep (se 1 (by rfl) ⟨980108, by rfl⟩ : syracuseStep 1306811 = 1960217) B1960217
theorem B1306871 : Blo 868566 1306871 := bstep (se 1 (by rfl) ⟨980153, by rfl⟩ : syracuseStep 1306871 = 1960307) B1960307
theorem B1306895 : Blo 868566 1306895 := bstep (se 1 (by rfl) ⟨980171, by rfl⟩ : syracuseStep 1306895 = 1960343) B1960343
theorem B8352017 : Blo 868566 8352017 := bstep (se 2 (by rfl) ⟨3132006, by rfl⟩ : syracuseStep 8352017 = 6264013) B6264013
theorem B11137297 : Blo 868566 11137297 := bstep (se 2 (by rfl) ⟨4176486, by rfl⟩ : syracuseStep 11137297 = 8352973) B8352973
theorem B1306937 : Blo 868566 1306937 := bstep (se 2 (by rfl) ⟨490101, by rfl⟩ : syracuseStep 1306937 = 980203) B980203
theorem B4714811 : Blo 868566 4714811 := bstep (se 1 (by rfl) ⟨3536108, by rfl⟩ : syracuseStep 4714811 = 7072217) B7072217
theorem B1962359 : Blo 868566 1962359 := bstep (se 1 (by rfl) ⟨1471769, by rfl⟩ : syracuseStep 1962359 = 2943539) B2943539
theorem B6615431 : Blo 868566 6615431 := bstep (se 1 (by rfl) ⟨4961573, by rfl⟩ : syracuseStep 6615431 = 9923147) B9923147
theorem B1307015 : Blo 868566 1307015 := bstep (se 1 (by rfl) ⟨980261, by rfl⟩ : syracuseStep 1307015 = 1960523) B1960523
theorem B1307051 : Blo 868566 1307051 := bstep (se 1 (by rfl) ⟨980288, by rfl⟩ : syracuseStep 1307051 = 1960577) B1960577
theorem B1765817 : Blo 868566 1765817 := bstep (se 2 (by rfl) ⟨662181, by rfl⟩ : syracuseStep 1765817 = 1324363) B1324363
theorem B1307081 : Blo 868566 1307081 := bstep (se 2 (by rfl) ⟨490155, by rfl⟩ : syracuseStep 1307081 = 980311) B980311
theorem B1962539 : Blo 868566 1962539 := bstep (se 1 (by rfl) ⟨1471904, by rfl⟩ : syracuseStep 1962539 = 2943809) B2943809
theorem B1307195 : Blo 868566 1307195 := bstep (se 1 (by rfl) ⟨980396, by rfl⟩ : syracuseStep 1307195 = 1960793) B1960793
theorem B1307255 : Blo 868566 1307255 := bstep (se 1 (by rfl) ⟨980441, by rfl⟩ : syracuseStep 1307255 = 1960883) B1960883
theorem B979591 : Blo 868566 979591 := bstep (se 1 (by rfl) ⟨734693, by rfl⟩ : syracuseStep 979591 = 1469387) B1469387
theorem B1307279 : Blo 868566 1307279 := bstep (se 1 (by rfl) ⟨980459, by rfl⟩ : syracuseStep 1307279 = 1960919) B1960919
theorem B1307321 : Blo 868566 1307321 := bstep (se 2 (by rfl) ⟨490245, by rfl⟩ : syracuseStep 1307321 = 980491) B980491
theorem B1307399 : Blo 868566 1307399 := bstep (se 1 (by rfl) ⟨980549, by rfl⟩ : syracuseStep 1307399 = 1961099) B1961099
theorem B1307435 : Blo 868566 1307435 := bstep (se 1 (by rfl) ⟨980576, by rfl⟩ : syracuseStep 1307435 = 1961153) B1961153
theorem B979771 : Blo 868566 979771 := bstep (se 1 (by rfl) ⟨734828, by rfl⟩ : syracuseStep 979771 = 1469657) B1469657
theorem B1307465 : Blo 868566 1307465 := bstep (se 2 (by rfl) ⟨490299, by rfl⟩ : syracuseStep 1307465 = 980599) B980599
theorem B15070067 : Blo 868566 15070067 := bstep (se 1 (by rfl) ⟨11302550, by rfl⟩ : syracuseStep 15070067 = 22605101) B22605101
theorem B1471351 : Blo 868566 1471351 := bstep (se 1 (by rfl) ⟨1103513, by rfl⟩ : syracuseStep 1471351 = 2207027) B2207027
theorem B1962899 : Blo 868566 1962899 := bstep (se 1 (by rfl) ⟨1472174, by rfl⟩ : syracuseStep 1962899 = 2944349) B2944349
theorem B1307579 : Blo 868566 1307579 := bstep (se 1 (by rfl) ⟨980684, by rfl⟩ : syracuseStep 1307579 = 1961369) B1961369
theorem B1962953 : Blo 868566 1962953 := bstep (se 2 (by rfl) ⟨736107, by rfl⟩ : syracuseStep 1962953 = 1472215) B1472215
theorem B1307639 : Blo 868566 1307639 := bstep (se 1 (by rfl) ⟨980729, by rfl⟩ : syracuseStep 1307639 = 1961459) B1961459
theorem B1307663 : Blo 868566 1307663 := bstep (se 1 (by rfl) ⟨980747, by rfl⟩ : syracuseStep 1307663 = 1961495) B1961495
theorem B1307705 : Blo 868566 1307705 := bstep (se 2 (by rfl) ⟨490389, by rfl⟩ : syracuseStep 1307705 = 980779) B980779
theorem B1471547 : Blo 868566 1471547 := bstep (se 1 (by rfl) ⟨1103660, by rfl⟩ : syracuseStep 1471547 = 2207321) B2207321
theorem B1307783 : Blo 868566 1307783 := bstep (se 1 (by rfl) ⟨980837, by rfl⟩ : syracuseStep 1307783 = 1961675) B1961675
theorem B1307819 : Blo 868566 1307819 := bstep (se 1 (by rfl) ⟨980864, by rfl⟩ : syracuseStep 1307819 = 1961729) B1961729
theorem B2094281 : Blo 868566 2094281 := bstep (se 2 (by rfl) ⟨785355, by rfl⟩ : syracuseStep 2094281 = 1570711) B1570711
theorem B1307849 : Blo 868566 1307849 := bstep (se 2 (by rfl) ⟨490443, by rfl⟩ : syracuseStep 1307849 = 980887) B980887
theorem B980239 : Blo 868566 980239 := bstep (se 1 (by rfl) ⟨735179, by rfl⟩ : syracuseStep 980239 = 1470359) B1470359
theorem B1307963 : Blo 868566 1307963 := bstep (se 1 (by rfl) ⟨980972, by rfl⟩ : syracuseStep 1307963 = 1961945) B1961945
theorem B1308023 : Blo 868566 1308023 := bstep (se 1 (by rfl) ⟨981017, by rfl⟩ : syracuseStep 1308023 = 1962035) B1962035
theorem B1308047 : Blo 868566 1308047 := bstep (se 1 (by rfl) ⟨981035, by rfl⟩ : syracuseStep 1308047 = 1962071) B1962071
theorem B2356627 : Blo 868566 2356627 := bstep (se 1 (by rfl) ⟨1767470, by rfl⟩ : syracuseStep 2356627 = 3534941) B3534941
theorem B1308089 : Blo 868566 1308089 := bstep (se 2 (by rfl) ⟨490533, by rfl⟩ : syracuseStep 1308089 = 981067) B981067
theorem B6714809 : Blo 868566 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B1471945 : Blo 868566 1471945 := bstep (se 2 (by rfl) ⟨551979, by rfl⟩ : syracuseStep 1471945 = 1103959) B1103959
theorem B1308167 : Blo 868566 1308167 := bstep (se 1 (by rfl) ⟨981125, by rfl⟩ : syracuseStep 1308167 = 1962251) B1962251
theorem B1308203 : Blo 868566 1308203 := bstep (se 1 (by rfl) ⟨981152, by rfl⟩ : syracuseStep 1308203 = 1962305) B1962305
theorem B1308233 : Blo 868566 1308233 := bstep (se 2 (by rfl) ⟨490587, by rfl⟩ : syracuseStep 1308233 = 981175) B981175
theorem B1308347 : Blo 868566 1308347 := bstep (se 1 (by rfl) ⟨981260, by rfl⟩ : syracuseStep 1308347 = 1962521) B1962521
theorem B1308407 : Blo 868566 1308407 := bstep (se 1 (by rfl) ⟨981305, by rfl⟩ : syracuseStep 1308407 = 1962611) B1962611
theorem B980743 : Blo 868566 980743 := bstep (se 1 (by rfl) ⟨735557, by rfl⟩ : syracuseStep 980743 = 1471115) B1471115
theorem B1308431 : Blo 868566 1308431 := bstep (se 1 (by rfl) ⟨981323, by rfl⟩ : syracuseStep 1308431 = 1962647) B1962647
theorem B1308473 : Blo 868566 1308473 := bstep (se 2 (by rfl) ⟨490677, by rfl⟩ : syracuseStep 1308473 = 981355) B981355
theorem B3143539 : Blo 868566 3143539 := bstep (se 1 (by rfl) ⟨2357654, by rfl⟩ : syracuseStep 3143539 = 4715309) B4715309
theorem B1308551 : Blo 868566 1308551 := bstep (se 1 (by rfl) ⟨981413, by rfl⟩ : syracuseStep 1308551 = 1962827) B1962827
theorem B1308587 : Blo 868566 1308587 := bstep (se 1 (by rfl) ⟨981440, by rfl⟩ : syracuseStep 1308587 = 1962881) B1962881
theorem B980923 : Blo 868566 980923 := bstep (se 1 (by rfl) ⟨735692, by rfl⟩ : syracuseStep 980923 = 1471385) B1471385
theorem B1308617 : Blo 868566 1308617 := bstep (se 2 (by rfl) ⟨490731, by rfl⟩ : syracuseStep 1308617 = 981463) B981463
theorem B1308731 : Blo 868566 1308731 := bstep (se 1 (by rfl) ⟨981548, by rfl⟩ : syracuseStep 1308731 = 1963097) B1963097
theorem B2357309 : Blo 868566 2357309 := bstep (se 3 (by rfl) ⟨441995, by rfl⟩ : syracuseStep 2357309 = 883991) B883991
theorem B2652275 : Blo 868566 2652275 := bstep (se 1 (by rfl) ⟨1989206, by rfl⟩ : syracuseStep 2652275 = 3978413) B3978413
theorem B1308791 : Blo 868566 1308791 := bstep (se 1 (by rfl) ⟨981593, by rfl⟩ : syracuseStep 1308791 = 1963187) B1963187
theorem B1308815 : Blo 868566 1308815 := bstep (se 1 (by rfl) ⟨981611, by rfl⟩ : syracuseStep 1308815 = 1963223) B1963223
theorem B981391 : Blo 868566 981391 := bstep (se 1 (by rfl) ⟨736043, by rfl⟩ : syracuseStep 981391 = 1472087) B1472087
theorem B1571257 : Blo 868566 1571257 := bstep (se 2 (by rfl) ⟨589221, by rfl⟩ : syracuseStep 1571257 = 1178443) B1178443
theorem B4192829 : Blo 868566 4192829 := bstep (se 3 (by rfl) ⟨786155, by rfl⟩ : syracuseStep 4192829 = 1572311) B1572311
theorem B2095703 : Blo 868566 2095703 := bstep (se 1 (by rfl) ⟨1571777, by rfl⟩ : syracuseStep 2095703 = 3143555) B3143555
theorem B1506319 : Blo 868566 1506319 := bstep (se 1 (by rfl) ⟨1129739, by rfl⟩ : syracuseStep 1506319 = 2259479) B2259479
theorem B2653337 : Blo 868566 2653337 := bstep (se 2 (by rfl) ⟨995001, by rfl⟩ : syracuseStep 2653337 = 1990003) B1990003
theorem B11926919 : Blo 868566 11926919 := bstep (se 1 (by rfl) ⟨8945189, by rfl⟩ : syracuseStep 11926919 = 17890379) B17890379
theorem B4292183 : Blo 868566 4292183 := bstep (se 1 (by rfl) ⟨3219137, by rfl⟩ : syracuseStep 4292183 = 6438275) B6438275
theorem B9404363 : Blo 868566 9404363 := bstep (se 1 (by rfl) ⟨7053272, by rfl⟩ : syracuseStep 9404363 = 14106545) B14106545
theorem B3309569 : Blo 868566 3309569 := bstep (se 2 (by rfl) ⟨1241088, by rfl⟩ : syracuseStep 3309569 = 2482177) B2482177
theorem B7929971 : Blo 868566 7929971 := bstep (se 1 (by rfl) ⟨5947478, by rfl⟩ : syracuseStep 7929971 = 11894957) B11894957
theorem B5964313 : Blo 868566 5964313 := bstep (se 2 (by rfl) ⟨2236617, by rfl⟩ : syracuseStep 5964313 = 4473235) B4473235
theorem B2785889 : Blo 868566 2785889 := bstep (se 2 (by rfl) ⟨1044708, by rfl⟩ : syracuseStep 2785889 = 2089417) B2089417
theorem B2687627 : Blo 868566 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B5964617 : Blo 868566 5964617 := bstep (se 2 (by rfl) ⟨2236731, by rfl⟩ : syracuseStep 5964617 = 4473463) B4473463
theorem B5571929 : Blo 868566 5571929 := bstep (se 2 (by rfl) ⟨2089473, by rfl⟩ : syracuseStep 5571929 = 4178947) B4178947
theorem B3311239 : Blo 868566 3311239 := bstep (se 1 (by rfl) ⟨2483429, by rfl⟩ : syracuseStep 3311239 = 4966859) B4966859
theorem B38078099 : Blo 868566 38078099 := bstep (se 1 (by rfl) ⟨28558574, by rfl⟩ : syracuseStep 38078099 = 57117149) B57117149
theorem B1672915 : Blo 868566 1672915 := bstep (se 1 (by rfl) ⟨1254686, by rfl⟩ : syracuseStep 1672915 = 2509373) B2509373
theorem B3311543 : Blo 868566 3311543 := bstep (se 1 (by rfl) ⟨2483657, by rfl⟩ : syracuseStep 3311543 = 4967315) B4967315
theorem B6260813 : Blo 868566 6260813 := bstep (se 3 (by rfl) ⟨1173902, by rfl⟩ : syracuseStep 6260813 = 2347805) B2347805
theorem B3017515 : Blo 868566 3017515 := bstep (se 1 (by rfl) ⟨2263136, by rfl⟩ : syracuseStep 3017515 = 4526273) B4526273
theorem B3312697 : Blo 868566 3312697 := bstep (se 2 (by rfl) ⟨1242261, by rfl⟩ : syracuseStep 3312697 = 2484523) B2484523
theorem B5573879 : Blo 868566 5573879 := bstep (se 1 (by rfl) ⟨4180409, by rfl⟩ : syracuseStep 5573879 = 8360819) B8360819
theorem B3313001 : Blo 868566 3313001 := bstep (se 2 (by rfl) ⟨1242375, by rfl⟩ : syracuseStep 3313001 = 2484751) B2484751
theorem B2198927 : Blo 868566 2198927 := bstep (se 1 (by rfl) ⟨1649195, by rfl⟩ : syracuseStep 2198927 = 3298391) B3298391
theorem B7048667 : Blo 868566 7048667 := bstep (se 1 (by rfl) ⟨5286500, by rfl⟩ : syracuseStep 7048667 = 10573001) B10573001
theorem B3968635 : Blo 868566 3968635 := bstep (se 1 (by rfl) ⟨2976476, by rfl⟩ : syracuseStep 3968635 = 5952953) B5952953
theorem B2199251 : Blo 868566 2199251 := bstep (se 1 (by rfl) ⟨1649438, by rfl⟩ : syracuseStep 2199251 = 3298877) B3298877
theorem B11177999 : Blo 868566 11177999 := bstep (se 1 (by rfl) ⟨8383499, by rfl⟩ : syracuseStep 11177999 = 16766999) B16766999
theorem B11309219 : Blo 868566 11309219 := bstep (se 1 (by rfl) ⟨8481914, by rfl⟩ : syracuseStep 11309219 = 16963829) B16963829
theorem B17174705 : Blo 868566 17174705 := bstep (se 2 (by rfl) ⟨6440514, by rfl⟩ : syracuseStep 17174705 = 12881029) B12881029
theorem B10327105 : Blo 868566 10327105 := bstep (se 2 (by rfl) ⟨3872664, by rfl⟩ : syracuseStep 10327105 = 7745329) B7745329
theorem B10589249 : Blo 868566 10589249 := bstep (se 2 (by rfl) ⟨3970968, by rfl⟩ : syracuseStep 10589249 = 7941937) B7941937
theorem B8033701 : Blo 868566 8033701 := bstep (se 4 (by rfl) ⟨753159, by rfl⟩ : syracuseStep 8033701 = 1506319) B1506319
theorem B3773897 : Blo 868566 3773897 := bstep (se 2 (by rfl) ⟨1415211, by rfl⟩ : syracuseStep 3773897 = 2830423) B2830423
theorem B2790875 : Blo 868566 2790875 := bstep (se 1 (by rfl) ⟨2093156, by rfl⟩ : syracuseStep 2790875 = 4186313) B4186313
theorem B14849729 : Blo 868566 14849729 := bstep (se 2 (by rfl) ⟨5568648, by rfl⟩ : syracuseStep 14849729 = 11137297) B11137297
theorem B14292695 : Blo 868566 14292695 := bstep (se 1 (by rfl) ⟨10719521, by rfl⟩ : syracuseStep 14292695 = 21439043) B21439043
theorem B2234105 : Blo 868566 2234105 := bstep (se 2 (by rfl) ⟨837789, by rfl⟩ : syracuseStep 2234105 = 1675579) B1675579
theorem B2201519 : Blo 868566 2201519 := bstep (se 1 (by rfl) ⟨1651139, by rfl⟩ : syracuseStep 2201519 = 3302279) B3302279
theorem B4954193 : Blo 868566 4954193 := bstep (se 2 (by rfl) ⟨1857822, by rfl⟩ : syracuseStep 4954193 = 3715645) B3715645
theorem B9410903 : Blo 868566 9410903 := bstep (se 1 (by rfl) ⟨7058177, by rfl⟩ : syracuseStep 9410903 = 14116355) B14116355
theorem B2202137 : Blo 868566 2202137 := bstep (se 2 (by rfl) ⟨825801, by rfl⟩ : syracuseStep 2202137 = 1651603) B1651603
theorem B4398461 : Blo 868566 4398461 := bstep (se 3 (by rfl) ⟨824711, by rfl⟩ : syracuseStep 4398461 = 1649423) B1649423
theorem B10166147 : Blo 868566 10166147 := bstep (se 1 (by rfl) ⟨7624610, by rfl⟩ : syracuseStep 10166147 = 15249221) B15249221
theorem B6693131 : Blo 868566 6693131 := bstep (se 1 (by rfl) ⟨5019848, by rfl⟩ : syracuseStep 6693131 = 10039697) B10039697
theorem B4956653 : Blo 868566 4956653 := bstep (se 3 (by rfl) ⟨929372, by rfl⟩ : syracuseStep 4956653 = 1858745) B1858745
theorem B992095 : Blo 868566 992095 := bstep (se 1 (by rfl) ⟨744071, by rfl⟩ : syracuseStep 992095 = 1488143) B1488143
theorem B2204729 : Blo 868566 2204729 := bstep (se 2 (by rfl) ⟨826773, by rfl⟩ : syracuseStep 2204729 = 1653547) B1653547
theorem B35661221 : Blo 868566 35661221 := bstep (se 4 (by rfl) ⟨3343239, by rfl⟩ : syracuseStep 35661221 = 6686479) B6686479
theorem B4957793 : Blo 868566 4957793 := bstep (se 2 (by rfl) ⟨1859172, by rfl⟩ : syracuseStep 4957793 = 3718345) B3718345
theorem B2795219 : Blo 868566 2795219 := bstep (se 1 (by rfl) ⟨2096414, by rfl⟩ : syracuseStep 2795219 = 4192829) B4192829
theorem B149038841 : Blo 868566 149038841 := bstep (se 2 (by rfl) ⟨55889565, by rfl⟩ : syracuseStep 149038841 = 111779131) B111779131
theorem B54241589 : Blo 868566 54241589 := bstep (se 5 (by rfl) ⟨2542574, by rfl⟩ : syracuseStep 54241589 = 5085149) B5085149
theorem B1648991 : Blo 868566 1648991 := bstep (se 1 (by rfl) ⟨1236743, by rfl⟩ : syracuseStep 1648991 = 2473487) B2473487
theorem B2861455 : Blo 868566 2861455 := bstep (se 1 (by rfl) ⟨2146091, by rfl⟩ : syracuseStep 2861455 = 4292183) B4292183
theorem B2206217 : Blo 868566 2206217 := bstep (se 2 (by rfl) ⟨827331, by rfl⟩ : syracuseStep 2206217 = 1654663) B1654663
theorem B6269575 : Blo 868566 6269575 := bstep (se 1 (by rfl) ⟨4702181, by rfl⟩ : syracuseStep 6269575 = 9404363) B9404363
theorem B60271397 : Blo 868566 60271397 := bstep (se 4 (by rfl) ⟨5650443, by rfl⟩ : syracuseStep 60271397 = 11300887) B11300887
theorem B6597449 : Blo 868566 6597449 := bstep (se 2 (by rfl) ⟨2474043, by rfl⟩ : syracuseStep 6597449 = 4948087) B4948087
theorem B4074515 : Blo 868566 4074515 := bstep (se 1 (by rfl) ⟨3055886, by rfl⟩ : syracuseStep 4074515 = 6111773) B6111773
theorem B4959251 : Blo 868566 4959251 := bstep (se 1 (by rfl) ⟨3719438, by rfl⟩ : syracuseStep 4959251 = 7438877) B7438877
theorem B3353771 : Blo 868566 3353771 := bstep (se 1 (by rfl) ⟨2515328, by rfl⟩ : syracuseStep 3353771 = 5030657) B5030657
theorem B4304119 : Blo 868566 4304119 := bstep (se 1 (by rfl) ⟨3228089, by rfl⟩ : syracuseStep 4304119 = 6456179) B6456179
theorem B1650107 : Blo 868566 1650107 := bstep (se 1 (by rfl) ⟨1237580, by rfl⟩ : syracuseStep 1650107 = 2475161) B2475161
theorem B10038923 : Blo 868566 10038923 := bstep (se 1 (by rfl) ⟨7529192, by rfl⟩ : syracuseStep 10038923 = 15058385) B15058385
theorem B2207371 : Blo 868566 2207371 := bstep (se 1 (by rfl) ⟨1655528, by rfl⟩ : syracuseStep 2207371 = 3311057) B3311057
theorem B4402835 : Blo 868566 4402835 := bstep (se 1 (by rfl) ⟨3302126, by rfl⟩ : syracuseStep 4402835 = 6604253) B6604253
theorem B1650593 : Blo 868566 1650593 := bstep (se 2 (by rfl) ⟨618972, by rfl⟩ : syracuseStep 1650593 = 1237945) B1237945
theorem B2207675 : Blo 868566 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B1486811 : Blo 868566 1486811 := bstep (se 1 (by rfl) ⟨1115108, by rfl⟩ : syracuseStep 1486811 = 2230217) B2230217
theorem B1257481 : Blo 868566 1257481 := bstep (se 2 (by rfl) ⟨471555, by rfl⟩ : syracuseStep 1257481 = 943111) B943111
theorem B1650935 : Blo 868566 1650935 := bstep (se 1 (by rfl) ⟨1238201, by rfl⟩ : syracuseStep 1650935 = 2476403) B2476403
theorem B2830835 : Blo 868566 2830835 := bstep (se 1 (by rfl) ⟨2123126, by rfl⟩ : syracuseStep 2830835 = 4246253) B4246253
theorem B2208455 : Blo 868566 2208455 := bstep (se 1 (by rfl) ⟨1656341, by rfl⟩ : syracuseStep 2208455 = 3312683) B3312683
theorem B2208505 : Blo 868566 2208505 := bstep (se 2 (by rfl) ⟨828189, by rfl⟩ : syracuseStep 2208505 = 1656379) B1656379
theorem B4961027 : Blo 868566 4961027 := bstep (se 1 (by rfl) ⟨3720770, by rfl⟩ : syracuseStep 4961027 = 7441541) B7441541
theorem B13415321 : Blo 868566 13415321 := bstep (se 2 (by rfl) ⟨5030745, by rfl⟩ : syracuseStep 13415321 = 10061491) B10061491
theorem B4961483 : Blo 868566 4961483 := bstep (se 1 (by rfl) ⟨3721112, by rfl⟩ : syracuseStep 4961483 = 7442225) B7442225
theorem B1488233 : Blo 868566 1488233 := bstep (se 2 (by rfl) ⟨558087, by rfl⟩ : syracuseStep 1488233 = 1116175) B1116175
theorem B1652233 : Blo 868566 1652233 := bstep (se 2 (by rfl) ⟨619587, by rfl⟩ : syracuseStep 1652233 = 1239175) B1239175
theorem B3716705 : Blo 868566 3716705 := bstep (se 2 (by rfl) ⟨1393764, by rfl⟩ : syracuseStep 3716705 = 2787529) B2787529
theorem B5945183 : Blo 868566 5945183 := bstep (se 1 (by rfl) ⟨4458887, by rfl⟩ : syracuseStep 5945183 = 8917775) B8917775
theorem B1652575 : Blo 868566 1652575 := bstep (se 1 (by rfl) ⟨1239431, by rfl⟩ : syracuseStep 1652575 = 2478863) B2478863
theorem B4962167 : Blo 868566 4962167 := bstep (se 1 (by rfl) ⟨3721625, by rfl⟩ : syracuseStep 4962167 = 7443251) B7443251
theorem B1489607 : Blo 868566 1489607 := bstep (se 1 (by rfl) ⟨1117205, by rfl⟩ : syracuseStep 1489607 = 2234411) B2234411
theorem B10566389 : Blo 868566 10566389 := bstep (se 5 (by rfl) ⟨495299, by rfl⟩ : syracuseStep 10566389 = 990599) B990599
theorem B6699779 : Blo 868566 6699779 := bstep (se 1 (by rfl) ⟨5024834, by rfl⟩ : syracuseStep 6699779 = 10049669) B10049669
theorem B2931551 : Blo 868566 2931551 := bstep (se 1 (by rfl) ⟨2198663, by rfl⟩ : syracuseStep 2931551 = 4397327) B4397327
theorem B1653691 : Blo 868566 1653691 := bstep (se 1 (by rfl) ⟨1240268, by rfl⟩ : syracuseStep 1653691 = 2480537) B2480537
theorem B2931713 : Blo 868566 2931713 := bstep (se 2 (by rfl) ⟨1099392, by rfl⟩ : syracuseStep 2931713 = 2198785) B2198785
theorem B1653767 : Blo 868566 1653767 := bstep (se 1 (by rfl) ⟨1240325, by rfl⟩ : syracuseStep 1653767 = 2480651) B2480651
theorem B1326431 : Blo 868566 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B1654177 : Blo 868566 1654177 := bstep (se 2 (by rfl) ⟨620316, by rfl⟩ : syracuseStep 1654177 = 1240633) B1240633
theorem B3718619 : Blo 868566 3718619 := bstep (se 1 (by rfl) ⟨2788964, by rfl⟩ : syracuseStep 3718619 = 5577929) B5577929
theorem B1883657 : Blo 868566 1883657 := bstep (se 2 (by rfl) ⟨706371, by rfl⟩ : syracuseStep 1883657 = 1412743) B1412743
theorem B1654519 : Blo 868566 1654519 := bstep (se 1 (by rfl) ⟨1240889, by rfl⟩ : syracuseStep 1654519 = 2481779) B2481779
theorem B2932523 : Blo 868566 2932523 := bstep (se 1 (by rfl) ⟨2199392, by rfl⟩ : syracuseStep 2932523 = 4398785) B4398785
theorem B5881643 : Blo 868566 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B3718979 : Blo 868566 3718979 := bstep (se 1 (by rfl) ⟨2789234, by rfl⟩ : syracuseStep 3718979 = 5578469) B5578469
theorem B1654823 : Blo 868566 1654823 := bstep (se 1 (by rfl) ⟨1241117, by rfl⟩ : syracuseStep 1654823 = 2482235) B2482235
theorem B2932793 : Blo 868566 2932793 := bstep (se 2 (by rfl) ⟨1099797, by rfl⟩ : syracuseStep 2932793 = 2199595) B2199595
theorem B5587001 : Blo 868566 5587001 := bstep (se 2 (by rfl) ⟨2095125, by rfl⟩ : syracuseStep 5587001 = 4190251) B4190251
theorem B868571 : Blo 868566 868571 := bstep (se 1 (by rfl) ⟨651428, by rfl⟩ : syracuseStep 868571 = 1302857) B1302857
theorem B868647 : Blo 868566 868647 := bstep (se 1 (by rfl) ⟨651485, by rfl⟩ : syracuseStep 868647 = 1302971) B1302971
theorem B868687 : Blo 868566 868687 := bstep (se 1 (by rfl) ⟨651515, by rfl⟩ : syracuseStep 868687 = 1303031) B1303031
theorem B868703 : Blo 868566 868703 := bstep (se 1 (by rfl) ⟨651527, by rfl⟩ : syracuseStep 868703 = 1303055) B1303055
theorem B868731 : Blo 868566 868731 := bstep (se 1 (by rfl) ⟨651548, by rfl⟩ : syracuseStep 868731 = 1303097) B1303097
theorem B2933117 : Blo 868566 2933117 := bstep (se 3 (by rfl) ⟨549959, by rfl⟩ : syracuseStep 2933117 = 1099919) B1099919
theorem B868783 : Blo 868566 868783 := bstep (se 1 (by rfl) ⟨651587, by rfl⟩ : syracuseStep 868783 = 1303175) B1303175
theorem B868807 : Blo 868566 868807 := bstep (se 1 (by rfl) ⟨651605, by rfl⟩ : syracuseStep 868807 = 1303211) B1303211
theorem B868827 : Blo 868566 868827 := bstep (se 1 (by rfl) ⟨651620, by rfl⟩ : syracuseStep 868827 = 1303241) B1303241
theorem B13419017 : Blo 868566 13419017 := bstep (se 2 (by rfl) ⟨5032131, by rfl⟩ : syracuseStep 13419017 = 10064263) B10064263
theorem B868903 : Blo 868566 868903 := bstep (se 1 (by rfl) ⟨651677, by rfl⟩ : syracuseStep 868903 = 1303355) B1303355
theorem B868943 : Blo 868566 868943 := bstep (se 1 (by rfl) ⟨651707, by rfl⟩ : syracuseStep 868943 = 1303415) B1303415
theorem B868959 : Blo 868566 868959 := bstep (se 1 (by rfl) ⟨651719, by rfl⟩ : syracuseStep 868959 = 1303439) B1303439
theorem B868987 : Blo 868566 868987 := bstep (se 1 (by rfl) ⟨651740, by rfl⟩ : syracuseStep 868987 = 1303481) B1303481
theorem B2933387 : Blo 868566 2933387 := bstep (se 1 (by rfl) ⟨2200040, by rfl⟩ : syracuseStep 2933387 = 4400081) B4400081
theorem B869039 : Blo 868566 869039 := bstep (se 1 (by rfl) ⟨651779, by rfl⟩ : syracuseStep 869039 = 1303559) B1303559
theorem B869063 : Blo 868566 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B4408019 : Blo 868566 4408019 := bstep (se 1 (by rfl) ⟨3306014, by rfl⟩ : syracuseStep 4408019 = 6612029) B6612029
theorem B7062227 : Blo 868566 7062227 := bstep (se 1 (by rfl) ⟨5296670, by rfl⟩ : syracuseStep 7062227 = 10593341) B10593341
theorem B869083 : Blo 868566 869083 := bstep (se 1 (by rfl) ⟨651812, by rfl⟩ : syracuseStep 869083 = 1303625) B1303625
theorem B869159 : Blo 868566 869159 := bstep (se 1 (by rfl) ⟨651869, by rfl⟩ : syracuseStep 869159 = 1303739) B1303739
theorem B869199 : Blo 868566 869199 := bstep (se 1 (by rfl) ⟨651899, by rfl⟩ : syracuseStep 869199 = 1303799) B1303799
theorem B869215 : Blo 868566 869215 := bstep (se 1 (by rfl) ⟨651911, by rfl⟩ : syracuseStep 869215 = 1303823) B1303823
theorem B869243 : Blo 868566 869243 := bstep (se 1 (by rfl) ⟨651932, by rfl⟩ : syracuseStep 869243 = 1303865) B1303865
theorem B869295 : Blo 868566 869295 := bstep (se 1 (by rfl) ⟨651971, by rfl⟩ : syracuseStep 869295 = 1303943) B1303943
theorem B869319 : Blo 868566 869319 := bstep (se 1 (by rfl) ⟨651989, by rfl⟩ : syracuseStep 869319 = 1303979) B1303979
theorem B869339 : Blo 868566 869339 := bstep (se 1 (by rfl) ⟨652004, by rfl⟩ : syracuseStep 869339 = 1304009) B1304009
theorem B11289619 : Blo 868566 11289619 := bstep (se 1 (by rfl) ⟨8467214, by rfl⟩ : syracuseStep 11289619 = 16934429) B16934429
theorem B869415 : Blo 868566 869415 := bstep (se 1 (by rfl) ⟨652061, by rfl⟩ : syracuseStep 869415 = 1304123) B1304123
theorem B1590329 : Blo 868566 1590329 := bstep (se 2 (by rfl) ⟨596373, by rfl⟩ : syracuseStep 1590329 = 1192747) B1192747
theorem B869455 : Blo 868566 869455 := bstep (se 1 (by rfl) ⟨652091, by rfl⟩ : syracuseStep 869455 = 1304183) B1304183
theorem B869471 : Blo 868566 869471 := bstep (se 1 (by rfl) ⟨652103, by rfl⟩ : syracuseStep 869471 = 1304207) B1304207
theorem B869499 : Blo 868566 869499 := bstep (se 1 (by rfl) ⟨652124, by rfl⟩ : syracuseStep 869499 = 1304249) B1304249
theorem B869551 : Blo 868566 869551 := bstep (se 1 (by rfl) ⟨652163, by rfl⟩ : syracuseStep 869551 = 1304327) B1304327
theorem B869575 : Blo 868566 869575 := bstep (se 1 (by rfl) ⟨652181, by rfl⟩ : syracuseStep 869575 = 1304363) B1304363
theorem B869595 : Blo 868566 869595 := bstep (se 1 (by rfl) ⟨652196, by rfl⟩ : syracuseStep 869595 = 1304393) B1304393
theorem B869671 : Blo 868566 869671 := bstep (se 1 (by rfl) ⟨652253, by rfl⟩ : syracuseStep 869671 = 1304507) B1304507
theorem B869711 : Blo 868566 869711 := bstep (se 1 (by rfl) ⟨652283, by rfl⟩ : syracuseStep 869711 = 1304567) B1304567
theorem B869727 : Blo 868566 869727 := bstep (se 1 (by rfl) ⟨652295, by rfl⟩ : syracuseStep 869727 = 1304591) B1304591
theorem B869755 : Blo 868566 869755 := bstep (se 1 (by rfl) ⟨652316, by rfl⟩ : syracuseStep 869755 = 1304633) B1304633
theorem B869807 : Blo 868566 869807 := bstep (se 1 (by rfl) ⟨652355, by rfl⟩ : syracuseStep 869807 = 1304711) B1304711
theorem B869831 : Blo 868566 869831 := bstep (se 1 (by rfl) ⟨652373, by rfl⟩ : syracuseStep 869831 = 1304747) B1304747
theorem B869851 : Blo 868566 869851 := bstep (se 1 (by rfl) ⟨652388, by rfl⟩ : syracuseStep 869851 = 1304777) B1304777
theorem B2934305 : Blo 868566 2934305 := bstep (se 2 (by rfl) ⟨1100364, by rfl⟩ : syracuseStep 2934305 = 2200729) B2200729
theorem B869927 : Blo 868566 869927 := bstep (se 1 (by rfl) ⟨652445, by rfl⟩ : syracuseStep 869927 = 1304891) B1304891
theorem B869967 : Blo 868566 869967 := bstep (se 1 (by rfl) ⟨652475, by rfl⟩ : syracuseStep 869967 = 1304951) B1304951
theorem B869983 : Blo 868566 869983 := bstep (se 1 (by rfl) ⟨652487, by rfl⟩ : syracuseStep 869983 = 1304975) B1304975
theorem B870011 : Blo 868566 870011 := bstep (se 1 (by rfl) ⟨652508, by rfl⟩ : syracuseStep 870011 = 1305017) B1305017
theorem B870063 : Blo 868566 870063 := bstep (se 1 (by rfl) ⟨652547, by rfl⟩ : syracuseStep 870063 = 1305095) B1305095
theorem B870087 : Blo 868566 870087 := bstep (se 1 (by rfl) ⟨652565, by rfl⟩ : syracuseStep 870087 = 1305131) B1305131
theorem B870107 : Blo 868566 870107 := bstep (se 1 (by rfl) ⟨652580, by rfl⟩ : syracuseStep 870107 = 1305161) B1305161
theorem B4966109 : Blo 868566 4966109 := bstep (se 3 (by rfl) ⟨931145, by rfl⟩ : syracuseStep 4966109 = 1862291) B1862291
theorem B2934521 : Blo 868566 2934521 := bstep (se 2 (by rfl) ⟨1100445, by rfl⟩ : syracuseStep 2934521 = 2200891) B2200891
theorem B870183 : Blo 868566 870183 := bstep (se 1 (by rfl) ⟨652637, by rfl⟩ : syracuseStep 870183 = 1305275) B1305275
theorem B12732203 : Blo 868566 12732203 := bstep (se 1 (by rfl) ⟨9549152, by rfl⟩ : syracuseStep 12732203 = 19098305) B19098305
theorem B870223 : Blo 868566 870223 := bstep (se 1 (by rfl) ⟨652667, by rfl⟩ : syracuseStep 870223 = 1305335) B1305335
theorem B870239 : Blo 868566 870239 := bstep (se 1 (by rfl) ⟨652679, by rfl⟩ : syracuseStep 870239 = 1305359) B1305359
theorem B3721079 : Blo 868566 3721079 := bstep (se 1 (by rfl) ⟨2790809, by rfl⟩ : syracuseStep 3721079 = 5581619) B5581619
theorem B870267 : Blo 868566 870267 := bstep (se 1 (by rfl) ⟨652700, by rfl⟩ : syracuseStep 870267 = 1305401) B1305401
theorem B870319 : Blo 868566 870319 := bstep (se 1 (by rfl) ⟨652739, by rfl⟩ : syracuseStep 870319 = 1305479) B1305479
theorem B870343 : Blo 868566 870343 := bstep (se 1 (by rfl) ⟨652757, by rfl⟩ : syracuseStep 870343 = 1305515) B1305515
theorem B870363 : Blo 868566 870363 := bstep (se 1 (by rfl) ⟨652772, by rfl⟩ : syracuseStep 870363 = 1305545) B1305545
theorem B2934791 : Blo 868566 2934791 := bstep (se 1 (by rfl) ⟨2201093, by rfl⟩ : syracuseStep 2934791 = 4402187) B4402187
theorem B870439 : Blo 868566 870439 := bstep (se 1 (by rfl) ⟨652829, by rfl⟩ : syracuseStep 870439 = 1305659) B1305659
theorem B4180025 : Blo 868566 4180025 := bstep (se 2 (by rfl) ⟨1567509, by rfl⟩ : syracuseStep 4180025 = 3135019) B3135019
theorem B870479 : Blo 868566 870479 := bstep (se 1 (by rfl) ⟨652859, by rfl⟩ : syracuseStep 870479 = 1305719) B1305719
theorem B870495 : Blo 868566 870495 := bstep (se 1 (by rfl) ⟨652871, by rfl⟩ : syracuseStep 870495 = 1305743) B1305743
theorem B2934899 : Blo 868566 2934899 := bstep (se 1 (by rfl) ⟨2201174, by rfl⟩ : syracuseStep 2934899 = 4402349) B4402349
theorem B870523 : Blo 868566 870523 := bstep (se 1 (by rfl) ⟨652892, by rfl⟩ : syracuseStep 870523 = 1305785) B1305785
theorem B870575 : Blo 868566 870575 := bstep (se 1 (by rfl) ⟨652931, by rfl⟩ : syracuseStep 870575 = 1305863) B1305863
theorem B1099975 : Blo 868566 1099975 := bstep (se 1 (by rfl) ⟨824981, by rfl⟩ : syracuseStep 1099975 = 1649963) B1649963
theorem B870599 : Blo 868566 870599 := bstep (se 1 (by rfl) ⟨652949, by rfl⟩ : syracuseStep 870599 = 1305899) B1305899
theorem B870619 : Blo 868566 870619 := bstep (se 1 (by rfl) ⟨652964, by rfl⟩ : syracuseStep 870619 = 1305929) B1305929
theorem B870695 : Blo 868566 870695 := bstep (se 1 (by rfl) ⟨653021, by rfl⟩ : syracuseStep 870695 = 1306043) B1306043
theorem B870735 : Blo 868566 870735 := bstep (se 1 (by rfl) ⟨653051, by rfl⟩ : syracuseStep 870735 = 1306103) B1306103
theorem B870751 : Blo 868566 870751 := bstep (se 1 (by rfl) ⟨653063, by rfl⟩ : syracuseStep 870751 = 1306127) B1306127
theorem B870779 : Blo 868566 870779 := bstep (se 1 (by rfl) ⟨653084, by rfl⟩ : syracuseStep 870779 = 1306169) B1306169
theorem B3131777 : Blo 868566 3131777 := bstep (se 2 (by rfl) ⟨1174416, by rfl⟩ : syracuseStep 3131777 = 2348833) B2348833
theorem B2935169 : Blo 868566 2935169 := bstep (se 2 (by rfl) ⟨1100688, by rfl⟩ : syracuseStep 2935169 = 2201377) B2201377
theorem B870831 : Blo 868566 870831 := bstep (se 1 (by rfl) ⟨653123, by rfl⟩ : syracuseStep 870831 = 1306247) B1306247
theorem B870855 : Blo 868566 870855 := bstep (se 1 (by rfl) ⟨653141, by rfl⟩ : syracuseStep 870855 = 1306283) B1306283
theorem B870875 : Blo 868566 870875 := bstep (se 1 (by rfl) ⟨653156, by rfl⟩ : syracuseStep 870875 = 1306313) B1306313
theorem B870951 : Blo 868566 870951 := bstep (se 1 (by rfl) ⟨653213, by rfl⟩ : syracuseStep 870951 = 1306427) B1306427
theorem B870991 : Blo 868566 870991 := bstep (se 1 (by rfl) ⟨653243, by rfl⟩ : syracuseStep 870991 = 1306487) B1306487
theorem B871007 : Blo 868566 871007 := bstep (se 1 (by rfl) ⟨653255, by rfl⟩ : syracuseStep 871007 = 1306511) B1306511
theorem B871035 : Blo 868566 871035 := bstep (se 1 (by rfl) ⟨653276, by rfl⟩ : syracuseStep 871035 = 1306553) B1306553
theorem B871087 : Blo 868566 871087 := bstep (se 1 (by rfl) ⟨653315, by rfl⟩ : syracuseStep 871087 = 1306631) B1306631
theorem B871111 : Blo 868566 871111 := bstep (se 1 (by rfl) ⟨653333, by rfl⟩ : syracuseStep 871111 = 1306667) B1306667
theorem B871131 : Blo 868566 871131 := bstep (se 1 (by rfl) ⟨653348, by rfl⟩ : syracuseStep 871131 = 1306697) B1306697
theorem B871207 : Blo 868566 871207 := bstep (se 1 (by rfl) ⟨653405, by rfl⟩ : syracuseStep 871207 = 1306811) B1306811
theorem B871247 : Blo 868566 871247 := bstep (se 1 (by rfl) ⟨653435, by rfl⟩ : syracuseStep 871247 = 1306871) B1306871
theorem B871263 : Blo 868566 871263 := bstep (se 1 (by rfl) ⟨653447, by rfl⟩ : syracuseStep 871263 = 1306895) B1306895
theorem B871291 : Blo 868566 871291 := bstep (se 1 (by rfl) ⟨653468, by rfl⟩ : syracuseStep 871291 = 1306937) B1306937
theorem B1100719 : Blo 868566 1100719 := bstep (se 1 (by rfl) ⟨825539, by rfl⟩ : syracuseStep 1100719 = 1651079) B1651079
theorem B4410287 : Blo 868566 4410287 := bstep (se 1 (by rfl) ⟨3307715, by rfl⟩ : syracuseStep 4410287 = 6615431) B6615431
theorem B871343 : Blo 868566 871343 := bstep (se 1 (by rfl) ⟨653507, by rfl⟩ : syracuseStep 871343 = 1307015) B1307015
theorem B871367 : Blo 868566 871367 := bstep (se 1 (by rfl) ⟨653525, by rfl⟩ : syracuseStep 871367 = 1307051) B1307051
theorem B871387 : Blo 868566 871387 := bstep (se 1 (by rfl) ⟨653540, by rfl⟩ : syracuseStep 871387 = 1307081) B1307081
theorem B871463 : Blo 868566 871463 := bstep (se 1 (by rfl) ⟨653597, by rfl⟩ : syracuseStep 871463 = 1307195) B1307195
theorem B871503 : Blo 868566 871503 := bstep (se 1 (by rfl) ⟨653627, by rfl⟩ : syracuseStep 871503 = 1307255) B1307255
theorem B871519 : Blo 868566 871519 := bstep (se 1 (by rfl) ⟨653639, by rfl⟩ : syracuseStep 871519 = 1307279) B1307279
theorem B871547 : Blo 868566 871547 := bstep (se 1 (by rfl) ⟨653660, by rfl⟩ : syracuseStep 871547 = 1307321) B1307321
theorem B2935979 : Blo 868566 2935979 := bstep (se 1 (by rfl) ⟨2201984, by rfl⟩ : syracuseStep 2935979 = 4403969) B4403969
theorem B3722411 : Blo 868566 3722411 := bstep (se 1 (by rfl) ⟨2791808, by rfl⟩ : syracuseStep 3722411 = 5583617) B5583617
theorem B871599 : Blo 868566 871599 := bstep (se 1 (by rfl) ⟨653699, by rfl⟩ : syracuseStep 871599 = 1307399) B1307399
theorem B871623 : Blo 868566 871623 := bstep (se 1 (by rfl) ⟨653717, by rfl⟩ : syracuseStep 871623 = 1307435) B1307435
theorem B871643 : Blo 868566 871643 := bstep (se 1 (by rfl) ⟨653732, by rfl⟩ : syracuseStep 871643 = 1307465) B1307465
theorem B10046711 : Blo 868566 10046711 := bstep (se 1 (by rfl) ⟨7535033, by rfl⟩ : syracuseStep 10046711 = 15070067) B15070067
theorem B871719 : Blo 868566 871719 := bstep (se 1 (by rfl) ⟨653789, by rfl⟩ : syracuseStep 871719 = 1307579) B1307579
theorem B871759 : Blo 868566 871759 := bstep (se 1 (by rfl) ⟨653819, by rfl⟩ : syracuseStep 871759 = 1307639) B1307639
theorem B871775 : Blo 868566 871775 := bstep (se 1 (by rfl) ⟨653831, by rfl⟩ : syracuseStep 871775 = 1307663) B1307663
theorem B871803 : Blo 868566 871803 := bstep (se 1 (by rfl) ⟨653852, by rfl⟩ : syracuseStep 871803 = 1307705) B1307705
theorem B871855 : Blo 868566 871855 := bstep (se 1 (by rfl) ⟨653891, by rfl⟩ : syracuseStep 871855 = 1307783) B1307783
theorem B871879 : Blo 868566 871879 := bstep (se 1 (by rfl) ⟨653909, by rfl⟩ : syracuseStep 871879 = 1307819) B1307819
theorem B1396187 : Blo 868566 1396187 := bstep (se 1 (by rfl) ⟨1047140, by rfl⟩ : syracuseStep 1396187 = 2094281) B2094281
theorem B871899 : Blo 868566 871899 := bstep (se 1 (by rfl) ⟨653924, by rfl⟩ : syracuseStep 871899 = 1307849) B1307849
theorem B871975 : Blo 868566 871975 := bstep (se 1 (by rfl) ⟨653981, by rfl⟩ : syracuseStep 871975 = 1307963) B1307963
theorem B872015 : Blo 868566 872015 := bstep (se 1 (by rfl) ⟨654011, by rfl⟩ : syracuseStep 872015 = 1308023) B1308023
theorem B872031 : Blo 868566 872031 := bstep (se 1 (by rfl) ⟨654023, by rfl⟩ : syracuseStep 872031 = 1308047) B1308047
theorem B872059 : Blo 868566 872059 := bstep (se 1 (by rfl) ⟨654044, by rfl⟩ : syracuseStep 872059 = 1308089) B1308089
theorem B4476539 : Blo 868566 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B872111 : Blo 868566 872111 := bstep (se 1 (by rfl) ⟨654083, by rfl⟩ : syracuseStep 872111 = 1308167) B1308167
theorem B2936519 : Blo 868566 2936519 := bstep (se 1 (by rfl) ⟨2202389, by rfl⟩ : syracuseStep 2936519 = 4404779) B4404779
theorem B872135 : Blo 868566 872135 := bstep (se 1 (by rfl) ⟨654101, by rfl⟩ : syracuseStep 872135 = 1308203) B1308203
theorem B872155 : Blo 868566 872155 := bstep (se 1 (by rfl) ⟨654116, by rfl⟩ : syracuseStep 872155 = 1308233) B1308233
theorem B872231 : Blo 868566 872231 := bstep (se 1 (by rfl) ⟨654173, by rfl⟩ : syracuseStep 872231 = 1308347) B1308347
theorem B872271 : Blo 868566 872271 := bstep (se 1 (by rfl) ⟨654203, by rfl⟩ : syracuseStep 872271 = 1308407) B1308407
theorem B872287 : Blo 868566 872287 := bstep (se 1 (by rfl) ⟨654215, by rfl⟩ : syracuseStep 872287 = 1308431) B1308431
theorem B3526507 : Blo 868566 3526507 := bstep (se 1 (by rfl) ⟨2644880, by rfl⟩ : syracuseStep 3526507 = 5289761) B5289761
theorem B872315 : Blo 868566 872315 := bstep (se 1 (by rfl) ⟨654236, by rfl⟩ : syracuseStep 872315 = 1308473) B1308473
theorem B9424775 : Blo 868566 9424775 := bstep (se 1 (by rfl) ⟨7068581, by rfl⟩ : syracuseStep 9424775 = 14137163) B14137163
theorem B872367 : Blo 868566 872367 := bstep (se 1 (by rfl) ⟨654275, by rfl⟩ : syracuseStep 872367 = 1308551) B1308551
theorem B872391 : Blo 868566 872391 := bstep (se 1 (by rfl) ⟨654293, by rfl⟩ : syracuseStep 872391 = 1308587) B1308587
theorem B872411 : Blo 868566 872411 := bstep (se 1 (by rfl) ⟨654308, by rfl⟩ : syracuseStep 872411 = 1308617) B1308617
theorem B4182023 : Blo 868566 4182023 := bstep (se 1 (by rfl) ⟨3136517, by rfl⟩ : syracuseStep 4182023 = 6273035) B6273035
theorem B1101863 : Blo 868566 1101863 := bstep (se 1 (by rfl) ⟨826397, by rfl⟩ : syracuseStep 1101863 = 1652795) B1652795
theorem B872487 : Blo 868566 872487 := bstep (se 1 (by rfl) ⟨654365, by rfl⟩ : syracuseStep 872487 = 1308731) B1308731
theorem B872527 : Blo 868566 872527 := bstep (se 1 (by rfl) ⟨654395, by rfl⟩ : syracuseStep 872527 = 1308791) B1308791
theorem B872543 : Blo 868566 872543 := bstep (se 1 (by rfl) ⟨654407, by rfl⟩ : syracuseStep 872543 = 1308815) B1308815
theorem B1102187 : Blo 868566 1102187 := bstep (se 1 (by rfl) ⟨826640, by rfl⟩ : syracuseStep 1102187 = 1653281) B1653281
theorem B1397135 : Blo 868566 1397135 := bstep (se 1 (by rfl) ⟨1047851, by rfl⟩ : syracuseStep 1397135 = 2095703) B2095703
theorem B1954313 : Blo 868566 1954313 := bstep (se 2 (by rfl) ⟨732867, by rfl⟩ : syracuseStep 1954313 = 1465735) B1465735
theorem B2937383 : Blo 868566 2937383 := bstep (se 1 (by rfl) ⟨2203037, by rfl⟩ : syracuseStep 2937383 = 4406075) B4406075
theorem B16765541 : Blo 868566 16765541 := bstep (se 4 (by rfl) ⟨1571769, by rfl⟩ : syracuseStep 16765541 = 3143539) B3143539
theorem B2937491 : Blo 868566 2937491 := bstep (se 1 (by rfl) ⟨2203118, by rfl⟩ : syracuseStep 2937491 = 4406237) B4406237
theorem B1954655 : Blo 868566 1954655 := bstep (se 1 (by rfl) ⟨1465991, by rfl⟩ : syracuseStep 1954655 = 2931983) B2931983
theorem B2937707 : Blo 868566 2937707 := bstep (se 1 (by rfl) ⟨2203280, by rfl⟩ : syracuseStep 2937707 = 4406561) B4406561
theorem B2937761 : Blo 868566 2937761 := bstep (se 2 (by rfl) ⟨1101660, by rfl⟩ : syracuseStep 2937761 = 2203321) B2203321
theorem B7951279 : Blo 868566 7951279 := bstep (se 1 (by rfl) ⟨5963459, by rfl⟩ : syracuseStep 7951279 = 11926919) B11926919
theorem B1954835 : Blo 868566 1954835 := bstep (se 1 (by rfl) ⟨1466126, by rfl⟩ : syracuseStep 1954835 = 2932253) B2932253
theorem B2479261 : Blo 868566 2479261 := bstep (se 3 (by rfl) ⟨464861, by rfl⟩ : syracuseStep 2479261 = 929723) B929723
theorem B1955177 : Blo 868566 1955177 := bstep (se 2 (by rfl) ⟨733191, by rfl⟩ : syracuseStep 1955177 = 1466383) B1466383
theorem B3134963 : Blo 868566 3134963 := bstep (se 1 (by rfl) ⟨2351222, by rfl⟩ : syracuseStep 3134963 = 4702445) B4702445
theorem B2938355 : Blo 868566 2938355 := bstep (se 1 (by rfl) ⟨2203766, by rfl⟩ : syracuseStep 2938355 = 4407533) B4407533
theorem B16701025 : Blo 868566 16701025 := bstep (se 2 (by rfl) ⟨6262884, by rfl⟩ : syracuseStep 16701025 = 12525769) B12525769
theorem B1103483 : Blo 868566 1103483 := bstep (se 1 (by rfl) ⟨827612, by rfl⟩ : syracuseStep 1103483 = 1655225) B1655225
theorem B7067351 : Blo 868566 7067351 := bstep (se 1 (by rfl) ⟨5300513, by rfl⟩ : syracuseStep 7067351 = 10601027) B10601027
theorem B3528521 : Blo 868566 3528521 := bstep (se 2 (by rfl) ⟨1323195, by rfl⟩ : syracuseStep 3528521 = 2646391) B2646391
theorem B2479967 : Blo 868566 2479967 := bstep (se 1 (by rfl) ⟨1859975, by rfl⟩ : syracuseStep 2479967 = 3719951) B3719951
theorem B1955771 : Blo 868566 1955771 := bstep (se 1 (by rfl) ⟨1466828, by rfl⟩ : syracuseStep 1955771 = 2933657) B2933657
theorem B2938895 : Blo 868566 2938895 := bstep (se 1 (by rfl) ⟨2204171, by rfl⟩ : syracuseStep 2938895 = 4408343) B4408343
theorem B1955897 : Blo 868566 1955897 := bstep (se 2 (by rfl) ⟨733461, by rfl⟩ : syracuseStep 1955897 = 1466923) B1466923
theorem B3299575 : Blo 868566 3299575 := bstep (se 1 (by rfl) ⟨2474681, by rfl⟩ : syracuseStep 3299575 = 4949363) B4949363
theorem B11163905 : Blo 868566 11163905 := bstep (se 2 (by rfl) ⟨4186464, by rfl⟩ : syracuseStep 11163905 = 8372929) B8372929
theorem B1956239 : Blo 868566 1956239 := bstep (se 1 (by rfl) ⟨1467179, by rfl⟩ : syracuseStep 1956239 = 2934359) B2934359
theorem B11917721 : Blo 868566 11917721 := bstep (se 2 (by rfl) ⟨4469145, by rfl⟩ : syracuseStep 11917721 = 8938291) B8938291
theorem B3299849 : Blo 868566 3299849 := bstep (se 2 (by rfl) ⟨1237443, by rfl⟩ : syracuseStep 3299849 = 2474887) B2474887
theorem B3299879 : Blo 868566 3299879 := bstep (se 1 (by rfl) ⟨2474909, by rfl⟩ : syracuseStep 3299879 = 4949819) B4949819
theorem B2644577 : Blo 868566 2644577 := bstep (se 2 (by rfl) ⟨991716, by rfl⟩ : syracuseStep 2644577 = 1983433) B1983433
theorem B2939489 : Blo 868566 2939489 := bstep (se 2 (by rfl) ⟨1102308, by rfl⟩ : syracuseStep 2939489 = 2204617) B2204617
theorem B2972371 : Blo 868566 2972371 := bstep (se 1 (by rfl) ⟨2229278, by rfl⟩ : syracuseStep 2972371 = 4458557) B4458557
theorem B1956563 : Blo 868566 1956563 := bstep (se 1 (by rfl) ⟨1467422, by rfl⟩ : syracuseStep 1956563 = 2934845) B2934845
theorem B2480969 : Blo 868566 2480969 := bstep (se 2 (by rfl) ⟨930363, by rfl⟩ : syracuseStep 2480969 = 1860727) B1860727
theorem B3300547 : Blo 868566 3300547 := bstep (se 1 (by rfl) ⟨2475410, by rfl⟩ : syracuseStep 3300547 = 4950821) B4950821
theorem B10575193 : Blo 868566 10575193 := bstep (se 2 (by rfl) ⟨3965697, by rfl⟩ : syracuseStep 10575193 = 7931395) B7931395
theorem B3300851 : Blo 868566 3300851 := bstep (se 1 (by rfl) ⟨2475638, by rfl⟩ : syracuseStep 3300851 = 4951277) B4951277
theorem B1957499 : Blo 868566 1957499 := bstep (se 1 (by rfl) ⟨1468124, by rfl⟩ : syracuseStep 1957499 = 2936249) B2936249
theorem B8380037 : Blo 868566 8380037 := bstep (se 4 (by rfl) ⟨785628, by rfl⟩ : syracuseStep 8380037 = 1571257) B1571257
theorem B6610571 : Blo 868566 6610571 := bstep (se 1 (by rfl) ⟨4957928, by rfl⟩ : syracuseStep 6610571 = 9915857) B9915857
theorem B1957625 : Blo 868566 1957625 := bstep (se 2 (by rfl) ⟨734109, by rfl⟩ : syracuseStep 1957625 = 1468219) B1468219
theorem B1466255 : Blo 868566 1466255 := bstep (se 1 (by rfl) ⟨1099691, by rfl⟩ : syracuseStep 1466255 = 2199383) B2199383
theorem B3301307 : Blo 868566 3301307 := bstep (se 1 (by rfl) ⟨2475980, by rfl⟩ : syracuseStep 3301307 = 4951961) B4951961
theorem B1957895 : Blo 868566 1957895 := bstep (se 1 (by rfl) ⟨1468421, by rfl⟩ : syracuseStep 1957895 = 2936843) B2936843
theorem B2940947 : Blo 868566 2940947 := bstep (se 1 (by rfl) ⟨2205710, by rfl⟩ : syracuseStep 2940947 = 4411421) B4411421
theorem B1957967 : Blo 868566 1957967 := bstep (se 1 (by rfl) ⟨1468475, by rfl⟩ : syracuseStep 1957967 = 2936951) B2936951
theorem B1466491 : Blo 868566 1466491 := bstep (se 1 (by rfl) ⟨1099868, by rfl⟩ : syracuseStep 1466491 = 2199737) B2199737
theorem B1859831 : Blo 868566 1859831 := bstep (se 1 (by rfl) ⟨1394873, by rfl⟩ : syracuseStep 1859831 = 2789747) B2789747
theorem B2941271 : Blo 868566 2941271 := bstep (se 1 (by rfl) ⟨2205953, by rfl⟩ : syracuseStep 2941271 = 4411907) B4411907
theorem B1302959 : Blo 868566 1302959 := bstep (se 1 (by rfl) ⟨977219, by rfl⟩ : syracuseStep 1302959 = 1954439) B1954439
theorem B1958363 : Blo 868566 1958363 := bstep (se 1 (by rfl) ⟨1468772, by rfl⟩ : syracuseStep 1958363 = 2937545) B2937545
theorem B1303049 : Blo 868566 1303049 := bstep (se 2 (by rfl) ⟨488643, by rfl⟩ : syracuseStep 1303049 = 977287) B977287
theorem B1303079 : Blo 868566 1303079 := bstep (se 1 (by rfl) ⟨977309, by rfl⟩ : syracuseStep 1303079 = 1954619) B1954619
theorem B1303163 : Blo 868566 1303163 := bstep (se 1 (by rfl) ⟨977372, by rfl⟩ : syracuseStep 1303163 = 1954745) B1954745
theorem B1303289 : Blo 868566 1303289 := bstep (se 2 (by rfl) ⟨488733, by rfl⟩ : syracuseStep 1303289 = 977467) B977467
theorem B1303391 : Blo 868566 1303391 := bstep (se 1 (by rfl) ⟨977543, by rfl⟩ : syracuseStep 1303391 = 1955087) B1955087
theorem B1303403 : Blo 868566 1303403 := bstep (se 1 (by rfl) ⟨977552, by rfl⟩ : syracuseStep 1303403 = 1955105) B1955105
theorem B1958831 : Blo 868566 1958831 := bstep (se 1 (by rfl) ⟨1469123, by rfl⟩ : syracuseStep 1958831 = 2938247) B2938247
theorem B3138479 : Blo 868566 3138479 := bstep (se 1 (by rfl) ⟨2353859, by rfl⟩ : syracuseStep 3138479 = 4707719) B4707719
theorem B1467355 : Blo 868566 1467355 := bstep (se 1 (by rfl) ⟨1100516, by rfl⟩ : syracuseStep 1467355 = 2201033) B2201033
theorem B943067 : Blo 868566 943067 := bstep (se 1 (by rfl) ⟨707300, by rfl⟩ : syracuseStep 943067 = 1414601) B1414601
theorem B1303631 : Blo 868566 1303631 := bstep (se 1 (by rfl) ⟨977723, by rfl⟩ : syracuseStep 1303631 = 1955447) B1955447
theorem B9921689 : Blo 868566 9921689 := bstep (se 2 (by rfl) ⟨3720633, by rfl⟩ : syracuseStep 9921689 = 7441267) B7441267
theorem B1959083 : Blo 868566 1959083 := bstep (se 1 (by rfl) ⟨1469312, by rfl⟩ : syracuseStep 1959083 = 2938625) B2938625
theorem B1303751 : Blo 868566 1303751 := bstep (se 1 (by rfl) ⟨977813, by rfl⟩ : syracuseStep 1303751 = 1955627) B1955627
theorem B6284567 : Blo 868566 6284567 := bstep (se 1 (by rfl) ⟨4713425, by rfl⟩ : syracuseStep 6284567 = 9426851) B9426851
theorem B1303913 : Blo 868566 1303913 := bstep (se 2 (by rfl) ⟨488967, by rfl⟩ : syracuseStep 1303913 = 977935) B977935
theorem B2942351 : Blo 868566 2942351 := bstep (se 1 (by rfl) ⟨2206763, by rfl⟩ : syracuseStep 2942351 = 4413527) B4413527
theorem B1762735 : Blo 868566 1762735 := bstep (se 1 (by rfl) ⟨1322051, by rfl⟩ : syracuseStep 1762735 = 2644103) B2644103
theorem B1303991 : Blo 868566 1303991 := bstep (se 1 (by rfl) ⟨977993, by rfl⟩ : syracuseStep 1303991 = 1955987) B1955987
theorem B1304027 : Blo 868566 1304027 := bstep (se 1 (by rfl) ⟨978020, by rfl⟩ : syracuseStep 1304027 = 1956041) B1956041
theorem B1238537 : Blo 868566 1238537 := bstep (se 2 (by rfl) ⟨464451, by rfl⟩ : syracuseStep 1238537 = 928903) B928903
theorem B943655 : Blo 868566 943655 := bstep (se 1 (by rfl) ⟨707741, by rfl⟩ : syracuseStep 943655 = 1415483) B1415483
theorem B1467983 : Blo 868566 1467983 := bstep (se 1 (by rfl) ⟨1100987, by rfl⟩ : syracuseStep 1467983 = 2201975) B2201975
theorem B31712867 : Blo 868566 31712867 := bstep (se 1 (by rfl) ⟨23784650, by rfl⟩ : syracuseStep 31712867 = 47569301) B47569301
theorem B1959623 : Blo 868566 1959623 := bstep (se 1 (by rfl) ⟨1469717, by rfl⟩ : syracuseStep 1959623 = 2939435) B2939435
theorem B2942675 : Blo 868566 2942675 := bstep (se 1 (by rfl) ⟨2207006, by rfl⟩ : syracuseStep 2942675 = 4414013) B4414013
theorem B1861471 : Blo 868566 1861471 := bstep (se 1 (by rfl) ⟨1396103, by rfl⟩ : syracuseStep 1861471 = 2792207) B2792207
theorem B13428575 : Blo 868566 13428575 := bstep (se 1 (by rfl) ⟨10071431, by rfl⟩ : syracuseStep 13428575 = 20142863) B20142863
theorem B1304495 : Blo 868566 1304495 := bstep (se 1 (by rfl) ⟨978371, by rfl⟩ : syracuseStep 1304495 = 1956743) B1956743
theorem B2090927 : Blo 868566 2090927 := bstep (se 1 (by rfl) ⟨1568195, by rfl⟩ : syracuseStep 2090927 = 3136391) B3136391
theorem B1304585 : Blo 868566 1304585 := bstep (se 2 (by rfl) ⟨489219, by rfl⟩ : syracuseStep 1304585 = 978439) B978439
theorem B1304615 : Blo 868566 1304615 := bstep (se 1 (by rfl) ⟨978461, by rfl⟩ : syracuseStep 1304615 = 1956923) B1956923
theorem B1304699 : Blo 868566 1304699 := bstep (se 1 (by rfl) ⟨978524, by rfl⟩ : syracuseStep 1304699 = 1957049) B1957049
theorem B23816429 : Blo 868566 23816429 := bstep (se 3 (by rfl) ⟨4465580, by rfl⟩ : syracuseStep 23816429 = 8931161) B8931161
theorem B1304825 : Blo 868566 1304825 := bstep (se 2 (by rfl) ⟨489309, by rfl⟩ : syracuseStep 1304825 = 978619) B978619
theorem B3303767 : Blo 868566 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B1304927 : Blo 868566 1304927 := bstep (se 1 (by rfl) ⟨978695, by rfl⟩ : syracuseStep 1304927 = 1957391) B1957391
theorem B1239391 : Blo 868566 1239391 := bstep (se 1 (by rfl) ⟨929543, by rfl⟩ : syracuseStep 1239391 = 1859087) B1859087
theorem B1304939 : Blo 868566 1304939 := bstep (se 1 (by rfl) ⟨978704, by rfl⟩ : syracuseStep 1304939 = 1957409) B1957409
theorem B1239403 : Blo 868566 1239403 := bstep (se 1 (by rfl) ⟨929552, by rfl⟩ : syracuseStep 1239403 = 1859105) B1859105
theorem B1468847 : Blo 868566 1468847 := bstep (se 1 (by rfl) ⟨1101635, by rfl⟩ : syracuseStep 1468847 = 2203271) B2203271
theorem B1960487 : Blo 868566 1960487 := bstep (se 1 (by rfl) ⟨1470365, by rfl⟩ : syracuseStep 1960487 = 2940731) B2940731
theorem B1305167 : Blo 868566 1305167 := bstep (se 1 (by rfl) ⟨978875, by rfl⟩ : syracuseStep 1305167 = 1957751) B1957751
theorem B1305287 : Blo 868566 1305287 := bstep (se 1 (by rfl) ⟨978965, by rfl⟩ : syracuseStep 1305287 = 1957931) B1957931
theorem B6286157 : Blo 868566 6286157 := bstep (se 3 (by rfl) ⟨1178654, by rfl⟩ : syracuseStep 6286157 = 2357309) B2357309
theorem B1469279 : Blo 868566 1469279 := bstep (se 1 (by rfl) ⟨1101959, by rfl⟩ : syracuseStep 1469279 = 2203919) B2203919
theorem B1305449 : Blo 868566 1305449 := bstep (se 2 (by rfl) ⟨489543, by rfl⟩ : syracuseStep 1305449 = 979087) B979087
theorem B1960811 : Blo 868566 1960811 := bstep (se 1 (by rfl) ⟨1470608, by rfl⟩ : syracuseStep 1960811 = 2941217) B2941217
theorem B2943863 : Blo 868566 2943863 := bstep (se 1 (by rfl) ⟨2207897, by rfl⟩ : syracuseStep 2943863 = 4415795) B4415795
theorem B1960865 : Blo 868566 1960865 := bstep (se 2 (by rfl) ⟨735324, by rfl⟩ : syracuseStep 1960865 = 1470649) B1470649
theorem B1305527 : Blo 868566 1305527 := bstep (se 1 (by rfl) ⟨979145, by rfl⟩ : syracuseStep 1305527 = 1958291) B1958291
theorem B1305563 : Blo 868566 1305563 := bstep (se 1 (by rfl) ⟨979172, by rfl⟩ : syracuseStep 1305563 = 1958345) B1958345
theorem B7072733 : Blo 868566 7072733 := bstep (se 3 (by rfl) ⟨1326137, by rfl⟩ : syracuseStep 7072733 = 2652275) B2652275
theorem B2944079 : Blo 868566 2944079 := bstep (se 1 (by rfl) ⟨2208059, by rfl⟩ : syracuseStep 2944079 = 4416119) B4416119
theorem B978043 : Blo 868566 978043 := bstep (se 1 (by rfl) ⟨733532, by rfl⟩ : syracuseStep 978043 = 1467065) B1467065
theorem B6286531 : Blo 868566 6286531 := bstep (se 1 (by rfl) ⟨4714898, by rfl⟩ : syracuseStep 6286531 = 9429797) B9429797
theorem B1961207 : Blo 868566 1961207 := bstep (se 1 (by rfl) ⟨1470905, by rfl⟩ : syracuseStep 1961207 = 2941811) B2941811
theorem B1863017 : Blo 868566 1863017 := bstep (se 2 (by rfl) ⟨698631, by rfl⟩ : syracuseStep 1863017 = 1397263) B1397263
theorem B1469839 : Blo 868566 1469839 := bstep (se 1 (by rfl) ⟨1102379, by rfl⟩ : syracuseStep 1469839 = 2204759) B2204759
theorem B1306031 : Blo 868566 1306031 := bstep (se 1 (by rfl) ⟨979523, by rfl⟩ : syracuseStep 1306031 = 1959047) B1959047
theorem B2944457 : Blo 868566 2944457 := bstep (se 2 (by rfl) ⟨1104171, by rfl⟩ : syracuseStep 2944457 = 2208343) B2208343
theorem B4713947 : Blo 868566 4713947 := bstep (se 1 (by rfl) ⟨3535460, by rfl⟩ : syracuseStep 4713947 = 7070921) B7070921
theorem B367586819 : Blo 868566 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B1306121 : Blo 868566 1306121 := bstep (se 2 (by rfl) ⟨489795, by rfl⟩ : syracuseStep 1306121 = 979591) B979591
theorem B1306151 : Blo 868566 1306151 := bstep (se 1 (by rfl) ⟨979613, by rfl⟩ : syracuseStep 1306151 = 1959227) B1959227
theorem B978511 : Blo 868566 978511 := bstep (se 1 (by rfl) ⟨733883, by rfl⟩ : syracuseStep 978511 = 1467767) B1467767
theorem B1306235 : Blo 868566 1306235 := bstep (se 1 (by rfl) ⟨979676, by rfl⟩ : syracuseStep 1306235 = 1959353) B1959353
theorem B12545725 : Blo 868566 12545725 := bstep (se 3 (by rfl) ⟨2352323, by rfl⟩ : syracuseStep 12545725 = 4704647) B4704647
theorem B2944727 : Blo 868566 2944727 := bstep (se 1 (by rfl) ⟨2208545, by rfl⟩ : syracuseStep 2944727 = 4417091) B4417091
theorem B42430169 : Blo 868566 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B1306361 : Blo 868566 1306361 := bstep (se 2 (by rfl) ⟨489885, by rfl⟩ : syracuseStep 1306361 = 979771) B979771
theorem B1961801 : Blo 868566 1961801 := bstep (se 2 (by rfl) ⟨735675, by rfl⟩ : syracuseStep 1961801 = 1471351) B1471351
theorem B1306463 : Blo 868566 1306463 := bstep (se 1 (by rfl) ⟨979847, by rfl⟩ : syracuseStep 1306463 = 1959695) B1959695
theorem B1306475 : Blo 868566 1306475 := bstep (se 1 (by rfl) ⟨979856, by rfl⟩ : syracuseStep 1306475 = 1959713) B1959713
theorem B6614945 : Blo 868566 6614945 := bstep (se 2 (by rfl) ⟨2480604, by rfl⟩ : syracuseStep 6614945 = 4961209) B4961209
theorem B978907 : Blo 868566 978907 := bstep (se 1 (by rfl) ⟨734180, by rfl⟩ : syracuseStep 978907 = 1468361) B1468361
theorem B1470521 : Blo 868566 1470521 := bstep (se 2 (by rfl) ⟨551445, by rfl⟩ : syracuseStep 1470521 = 1102891) B1102891
theorem B1306703 : Blo 868566 1306703 := bstep (se 1 (by rfl) ⟨980027, by rfl⟩ : syracuseStep 1306703 = 1960055) B1960055
theorem B1175675 : Blo 868566 1175675 := bstep (se 1 (by rfl) ⟨881756, by rfl⟩ : syracuseStep 1175675 = 1763513) B1763513
theorem B2650283 : Blo 868566 2650283 := bstep (se 1 (by rfl) ⟨1987712, by rfl⟩ : syracuseStep 2650283 = 3975425) B3975425
theorem B1306823 : Blo 868566 1306823 := bstep (se 1 (by rfl) ⟨980117, by rfl⟩ : syracuseStep 1306823 = 1960235) B1960235
theorem B1306985 : Blo 868566 1306985 := bstep (se 2 (by rfl) ⟨490119, by rfl⟩ : syracuseStep 1306985 = 980239) B980239
theorem B979375 : Blo 868566 979375 := bstep (se 1 (by rfl) ⟨734531, by rfl⟩ : syracuseStep 979375 = 1469063) B1469063
theorem B1307063 : Blo 868566 1307063 := bstep (se 1 (by rfl) ⟨980297, by rfl⟩ : syracuseStep 1307063 = 1960595) B1960595
theorem B1307099 : Blo 868566 1307099 := bstep (se 1 (by rfl) ⟨980324, by rfl⟩ : syracuseStep 1307099 = 1960649) B1960649
theorem B3142169 : Blo 868566 3142169 := bstep (se 2 (by rfl) ⟨1178313, by rfl⟩ : syracuseStep 3142169 = 2356627) B2356627
theorem B1962593 : Blo 868566 1962593 := bstep (se 2 (by rfl) ⟨735972, by rfl⟩ : syracuseStep 1962593 = 1471945) B1471945
theorem B1471223 : Blo 868566 1471223 := bstep (se 1 (by rfl) ⟨1103417, by rfl⟩ : syracuseStep 1471223 = 2206835) B2206835
theorem B979807 : Blo 868566 979807 := bstep (se 1 (by rfl) ⟨734855, by rfl⟩ : syracuseStep 979807 = 1469711) B1469711
theorem B1307567 : Blo 868566 1307567 := bstep (se 1 (by rfl) ⟨980675, by rfl⟩ : syracuseStep 1307567 = 1961351) B1961351
theorem B1962935 : Blo 868566 1962935 := bstep (se 1 (by rfl) ⟨1472201, by rfl⟩ : syracuseStep 1962935 = 2944403) B2944403
theorem B1307657 : Blo 868566 1307657 := bstep (se 2 (by rfl) ⟨490371, by rfl⟩ : syracuseStep 1307657 = 980743) B980743
theorem B1307687 : Blo 868566 1307687 := bstep (se 1 (by rfl) ⟨980765, by rfl⟩ : syracuseStep 1307687 = 1961531) B1961531
theorem B1471567 : Blo 868566 1471567 := bstep (se 1 (by rfl) ⟨1103675, by rfl⟩ : syracuseStep 1471567 = 2207351) B2207351
theorem B1766497 : Blo 868566 1766497 := bstep (se 2 (by rfl) ⟨662436, by rfl⟩ : syracuseStep 1766497 = 1324873) B1324873
theorem B1307771 : Blo 868566 1307771 := bstep (se 1 (by rfl) ⟨980828, by rfl⟩ : syracuseStep 1307771 = 1961657) B1961657
theorem B3306653 : Blo 868566 3306653 := bstep (se 3 (by rfl) ⟨619997, by rfl⟩ : syracuseStep 3306653 = 1239995) B1239995
theorem B980167 : Blo 868566 980167 := bstep (se 1 (by rfl) ⟨735125, by rfl⟩ : syracuseStep 980167 = 1470251) B1470251
theorem B1307897 : Blo 868566 1307897 := bstep (se 2 (by rfl) ⟨490461, by rfl⟩ : syracuseStep 1307897 = 980923) B980923
theorem B1471817 : Blo 868566 1471817 := bstep (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) B1103863
theorem B1307999 : Blo 868566 1307999 := bstep (se 1 (by rfl) ⟨980999, by rfl⟩ : syracuseStep 1307999 = 1961999) B1961999
theorem B1308011 : Blo 868566 1308011 := bstep (se 1 (by rfl) ⟨981008, by rfl⟩ : syracuseStep 1308011 = 1962017) B1962017
theorem B5568011 : Blo 868566 5568011 := bstep (se 1 (by rfl) ⟨4176008, by rfl⟩ : syracuseStep 5568011 = 8352017) B8352017
theorem B3143207 : Blo 868566 3143207 := bstep (se 1 (by rfl) ⟨2357405, by rfl⟩ : syracuseStep 3143207 = 4714811) B4714811
theorem B1308239 : Blo 868566 1308239 := bstep (se 1 (by rfl) ⟨981179, by rfl⟩ : syracuseStep 1308239 = 1962359) B1962359
theorem B1177211 : Blo 868566 1177211 := bstep (se 1 (by rfl) ⟨882908, by rfl⟩ : syracuseStep 1177211 = 1765817) B1765817
theorem B26834581 : Blo 868566 26834581 := bstep (se 6 (by rfl) ⟨628935, by rfl⟩ : syracuseStep 26834581 = 1257871) B1257871
theorem B1308359 : Blo 868566 1308359 := bstep (se 1 (by rfl) ⟨981269, by rfl⟩ : syracuseStep 1308359 = 1962539) B1962539
theorem B1472249 : Blo 868566 1472249 := bstep (se 2 (by rfl) ⟨552093, by rfl⟩ : syracuseStep 1472249 = 1104187) B1104187
theorem B3307337 : Blo 868566 3307337 := bstep (se 2 (by rfl) ⟨1240251, by rfl⟩ : syracuseStep 3307337 = 2480503) B2480503
theorem B1308521 : Blo 868566 1308521 := bstep (se 2 (by rfl) ⟨490695, by rfl⟩ : syracuseStep 1308521 = 981391) B981391
theorem B2652011 : Blo 868566 2652011 := bstep (se 1 (by rfl) ⟨1989008, by rfl⟩ : syracuseStep 2652011 = 3978017) B3978017
theorem B3766135 : Blo 868566 3766135 := bstep (se 1 (by rfl) ⟨2824601, by rfl⟩ : syracuseStep 3766135 = 5649203) B5649203
theorem B1472431 : Blo 868566 1472431 := bstep (se 1 (by rfl) ⟨1104323, by rfl⟩ : syracuseStep 1472431 = 2208647) B2208647
theorem B1308599 : Blo 868566 1308599 := bstep (se 1 (by rfl) ⟨981449, by rfl⟩ : syracuseStep 1308599 = 1962899) B1962899
theorem B1308635 : Blo 868566 1308635 := bstep (se 1 (by rfl) ⟨981476, by rfl⟩ : syracuseStep 1308635 = 1962953) B1962953
theorem B981031 : Blo 868566 981031 := bstep (se 1 (by rfl) ⟨735773, by rfl⟩ : syracuseStep 981031 = 1471547) B1471547
theorem B3537053 : Blo 868566 3537053 := bstep (se 3 (by rfl) ⟨663197, by rfl⟩ : syracuseStep 3537053 = 1326395) B1326395
theorem B3307837 : Blo 868566 3307837 := bstep (se 3 (by rfl) ⟨620219, by rfl⟩ : syracuseStep 3307837 = 1240439) B1240439
theorem B1145707 : Blo 868566 1145707 := bstep (se 1 (by rfl) ⟨859280, by rfl⟩ : syracuseStep 1145707 = 1718561) B1718561
theorem B1768891 : Blo 868566 1768891 := bstep (se 1 (by rfl) ⟨1326668, by rfl⟩ : syracuseStep 1768891 = 2653337) B2653337
theorem B4947905 : Blo 868566 4947905 := bstep (se 2 (by rfl) ⟨1855464, by rfl⟩ : syracuseStep 4947905 = 3710929) B3710929
theorem B8946011 : Blo 868566 8946011 := bstep (se 1 (by rfl) ⟨6709508, by rfl⟩ : syracuseStep 8946011 = 13419017) B13419017
theorem B3310739 : Blo 868566 3310739 := bstep (se 1 (by rfl) ⟨2483054, by rfl⟩ : syracuseStep 3310739 = 4966109) B4966109
theorem B2786683 : Blo 868566 2786683 := bstep (se 1 (by rfl) ⟨2090012, by rfl⟩ : syracuseStep 2786683 = 4180025) B4180025
theorem B2230553 : Blo 868566 2230553 := bstep (se 2 (by rfl) ⟨836457, by rfl⟩ : syracuseStep 2230553 = 1672915) B1672915
theorem B2984359 : Blo 868566 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B2788015 : Blo 868566 2788015 := bstep (se 1 (by rfl) ⟨2091011, by rfl⟩ : syracuseStep 2788015 = 4182023) B4182023
theorem B7539479 : Blo 868566 7539479 := bstep (se 1 (by rfl) ⟨5654609, by rfl⟩ : syracuseStep 7539479 = 11309219) B11309219
theorem B11177027 : Blo 868566 11177027 := bstep (se 1 (by rfl) ⟨8382770, by rfl⟩ : syracuseStep 11177027 = 16765541) B16765541
theorem B8359433 : Blo 868566 8359433 := bstep (se 2 (by rfl) ⟨3134787, by rfl⟩ : syracuseStep 8359433 = 6269575) B6269575
theorem B3968621 : Blo 868566 3968621 := bstep (se 3 (by rfl) ⟨744116, by rfl⟩ : syracuseStep 3968621 = 1488233) B1488233
theorem B9899819 : Blo 868566 9899819 := bstep (se 1 (by rfl) ⟨7424864, by rfl⟩ : syracuseStep 9899819 = 14849729) B14849729
theorem B7442603 : Blo 868566 7442603 := bstep (se 1 (by rfl) ⟨5581952, by rfl⟩ : syracuseStep 7442603 = 11163905) B11163905
theorem B5738825 : Blo 868566 5738825 := bstep (se 2 (by rfl) ⟨2152059, by rfl⟩ : syracuseStep 5738825 = 4304119) B4304119
theorem B2199899 : Blo 868566 2199899 := bstep (se 1 (by rfl) ⟨1649924, by rfl⟩ : syracuseStep 2199899 = 3299849) B3299849
theorem B2199919 : Blo 868566 2199919 := bstep (se 1 (by rfl) ⟨1649939, by rfl⟩ : syracuseStep 2199919 = 3299879) B3299879
theorem B18846269 : Blo 868566 18846269 := bstep (se 3 (by rfl) ⟨3533675, by rfl⟩ : syracuseStep 18846269 = 7067351) B7067351
theorem B33952541 : Blo 868566 33952541 := bstep (se 3 (by rfl) ⟨6366101, by rfl⟩ : syracuseStep 33952541 = 12732203) B12732203
theorem B2200567 : Blo 868566 2200567 := bstep (se 1 (by rfl) ⟨1650425, by rfl⟩ : syracuseStep 2200567 = 3300851) B3300851
theorem B2200871 : Blo 868566 2200871 := bstep (se 1 (by rfl) ⟨1650653, by rfl⟩ : syracuseStep 2200871 = 3301307) B3301307
theorem B1676641 : Blo 868566 1676641 := bstep (se 2 (by rfl) ⟨628740, by rfl⟩ : syracuseStep 1676641 = 1257481) B1257481
theorem B10065653 : Blo 868566 10065653 := bstep (se 5 (by rfl) ⟨471827, by rfl⟩ : syracuseStep 10065653 = 943655) B943655
theorem B144644237 : Blo 868566 144644237 := bstep (se 3 (by rfl) ⟨27120794, by rfl⟩ : syracuseStep 144644237 = 54241589) B54241589
theorem B21141911 : Blo 868566 21141911 := bstep (se 1 (by rfl) ⟨15856433, by rfl⟩ : syracuseStep 21141911 = 31712867) B31712867
theorem B99359227 : Blo 868566 99359227 := bstep (se 1 (by rfl) ⟨74519420, by rfl⟩ : syracuseStep 99359227 = 149038841) B149038841
theorem B8952383 : Blo 868566 8952383 := bstep (se 1 (by rfl) ⟨6714287, by rfl⟩ : syracuseStep 8952383 = 13428575) B13428575
theorem B13769473 : Blo 868566 13769473 := bstep (se 2 (by rfl) ⟨5163552, by rfl⟩ : syracuseStep 13769473 = 10327105) B10327105
theorem B2202511 : Blo 868566 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B40180931 : Blo 868566 40180931 := bstep (se 1 (by rfl) ⟨30135698, by rfl⟩ : syracuseStep 40180931 = 60271397) B60271397
theorem B4398299 : Blo 868566 4398299 := bstep (se 1 (by rfl) ⟨3298724, by rfl⟩ : syracuseStep 4398299 = 6597449) B6597449
theorem B2202977 : Blo 868566 2202977 := bstep (se 2 (by rfl) ⟨826116, by rfl⟩ : syracuseStep 2202977 = 1652233) B1652233
theorem B2235847 : Blo 868566 2235847 := bstep (se 1 (by rfl) ⟨1676885, by rfl⟩ : syracuseStep 2235847 = 3353771) B3353771
theorem B6692615 : Blo 868566 6692615 := bstep (se 1 (by rfl) ⟨5019461, by rfl⟩ : syracuseStep 6692615 = 10038923) B10038923
theorem B2203433 : Blo 868566 2203433 := bstep (se 2 (by rfl) ⟨826287, by rfl⟩ : syracuseStep 2203433 = 1652575) B1652575
theorem B28286779 : Blo 868566 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B5021513 : Blo 868566 5021513 := bstep (se 2 (by rfl) ⟨1883067, by rfl⟩ : syracuseStep 5021513 = 3766135) B3766135
theorem B991207 : Blo 868566 991207 := bstep (se 1 (by rfl) ⟨743405, by rfl⟩ : syracuseStep 991207 = 1486811) B1486811
theorem B4399433 : Blo 868566 4399433 := bstep (se 2 (by rfl) ⟨1649787, by rfl⟩ : syracuseStep 4399433 = 3299575) B3299575
theorem B2204435 : Blo 868566 2204435 := bstep (se 1 (by rfl) ⟨1653326, by rfl⟩ : syracuseStep 2204435 = 3306653) B3306653
theorem B3712007 : Blo 868566 3712007 := bstep (se 1 (by rfl) ⟨2784005, by rfl⟩ : syracuseStep 3712007 = 5568011) B5568011
theorem B2204891 : Blo 868566 2204891 := bstep (se 1 (by rfl) ⟨1653668, by rfl⟩ : syracuseStep 2204891 = 3307337) B3307337
theorem B2204921 : Blo 868566 2204921 := bstep (se 2 (by rfl) ⟨826845, by rfl⟩ : syracuseStep 2204921 = 1653691) B1653691
theorem B4400729 : Blo 868566 4400729 := bstep (se 2 (by rfl) ⟨1650273, by rfl⟩ : syracuseStep 4400729 = 3300547) B3300547
theorem B14100257 : Blo 868566 14100257 := bstep (se 2 (by rfl) ⟨5287596, by rfl⟩ : syracuseStep 14100257 = 10575193) B10575193
theorem B993071 : Blo 868566 993071 := bstep (se 1 (by rfl) ⟨744803, by rfl⟩ : syracuseStep 993071 = 1489607) B1489607
theorem B4466519 : Blo 868566 4466519 := bstep (se 1 (by rfl) ⟨3349889, by rfl⟩ : syracuseStep 4466519 = 6699779) B6699779
theorem B2205569 : Blo 868566 2205569 := bstep (se 2 (by rfl) ⟨827088, by rfl⟩ : syracuseStep 2205569 = 1654177) B1654177
theorem B2206025 : Blo 868566 2206025 := bstep (se 2 (by rfl) ⟨827259, by rfl⟩ : syracuseStep 2206025 = 1654519) B1654519
theorem B1255771 : Blo 868566 1255771 := bstep (se 1 (by rfl) ⟨941828, by rfl⟩ : syracuseStep 1255771 = 1883657) B1883657
theorem B2206379 : Blo 868566 2206379 := bstep (se 1 (by rfl) ⟨1654784, by rfl⟩ : syracuseStep 2206379 = 3309569) B3309569
theorem B5286647 : Blo 868566 5286647 := bstep (se 1 (by rfl) ⟨3964985, by rfl⟩ : syracuseStep 5286647 = 7929971) B7929971
theorem B3976411 : Blo 868566 3976411 := bstep (se 1 (by rfl) ⟨2982308, by rfl⟩ : syracuseStep 3976411 = 5964617) B5964617
theorem B1060219 : Blo 868566 1060219 := bstep (se 1 (by rfl) ⟨795164, by rfl⟩ : syracuseStep 1060219 = 1590329) B1590329
theorem B2207695 : Blo 868566 2207695 := bstep (se 1 (by rfl) ⟨1655771, by rfl⟩ : syracuseStep 2207695 = 3311543) B3311543
theorem B7548893 : Blo 868566 7548893 := bstep (se 3 (by rfl) ⟨1415417, by rfl⟩ : syracuseStep 7548893 = 2830835) B2830835
theorem B15052825 : Blo 868566 15052825 := bstep (se 2 (by rfl) ⟨5644809, by rfl⟩ : syracuseStep 15052825 = 11289619) B11289619
theorem B4173875 : Blo 868566 4173875 := bstep (se 1 (by rfl) ⟨3130406, by rfl⟩ : syracuseStep 4173875 = 6260813) B6260813
theorem B3715919 : Blo 868566 3715919 := bstep (se 1 (by rfl) ⟨2786939, by rfl⟩ : syracuseStep 3715919 = 5573879) B5573879
theorem B2208667 : Blo 868566 2208667 := bstep (se 1 (by rfl) ⟨1656500, by rfl⟩ : syracuseStep 2208667 = 3313001) B3313001
theorem B930791 : Blo 868566 930791 := bstep (se 1 (by rfl) ⟨698093, by rfl⟩ : syracuseStep 930791 = 1396187) B1396187
theorem B7451999 : Blo 868566 7451999 := bstep (se 1 (by rfl) ⟨5588999, by rfl⟩ : syracuseStep 7451999 = 11177999) B11177999
theorem B931423 : Blo 868566 931423 := bstep (se 1 (by rfl) ⟨698567, by rfl⟩ : syracuseStep 931423 = 1397135) B1397135
theorem B1652537 : Blo 868566 1652537 := bstep (se 2 (by rfl) ⟨619701, by rfl⟩ : syracuseStep 1652537 = 1239403) B1239403
theorem B3815273 : Blo 868566 3815273 := bstep (se 2 (by rfl) ⟨1430727, by rfl⟩ : syracuseStep 3815273 = 2861455) B2861455
theorem B16758845 : Blo 868566 16758845 := bstep (se 3 (by rfl) ⟨3142283, by rfl⟩ : syracuseStep 16758845 = 6284567) B6284567
theorem B14858477 : Blo 868566 14858477 := bstep (se 3 (by rfl) ⟨2785964, by rfl⟩ : syracuseStep 14858477 = 5571929) B5571929
theorem B1489403 : Blo 868566 1489403 := bstep (se 1 (by rfl) ⟨1117052, by rfl⟩ : syracuseStep 1489403 = 2234105) B2234105
theorem B1653311 : Blo 868566 1653311 := bstep (se 1 (by rfl) ⟨1239983, by rfl⟩ : syracuseStep 1653311 = 2479967) B2479967
theorem B6273935 : Blo 868566 6273935 := bstep (se 1 (by rfl) ⟨4705451, by rfl⟩ : syracuseStep 6273935 = 9410903) B9410903
theorem B7945147 : Blo 868566 7945147 := bstep (se 1 (by rfl) ⟨5958860, by rfl⟩ : syracuseStep 7945147 = 11917721) B11917721
theorem B5291173 : Blo 868566 5291173 := bstep (se 4 (by rfl) ⟨496047, by rfl⟩ : syracuseStep 5291173 = 992095) B992095
theorem B6110437 : Blo 868566 6110437 := bstep (se 4 (by rfl) ⟨572853, by rfl⟩ : syracuseStep 6110437 = 1145707) B1145707
theorem B5291513 : Blo 868566 5291513 := bstep (se 2 (by rfl) ⟨1984317, by rfl⟩ : syracuseStep 5291513 = 3968635) B3968635
theorem B16727633 : Blo 868566 16727633 := bstep (se 2 (by rfl) ⟨6272862, by rfl⟩ : syracuseStep 16727633 = 12545725) B12545725
theorem B2932307 : Blo 868566 2932307 := bstep (se 1 (by rfl) ⟨2199230, by rfl⟩ : syracuseStep 2932307 = 4398461) B4398461
theorem B4407047 : Blo 868566 4407047 := bstep (se 1 (by rfl) ⟨3305285, by rfl⟩ : syracuseStep 4407047 = 6610571) B6610571
theorem B4702009 : Blo 868566 4702009 := bstep (se 2 (by rfl) ⟨1763253, by rfl⟩ : syracuseStep 4702009 = 3526507) B3526507
theorem B868639 : Blo 868566 868639 := bstep (se 1 (by rfl) ⟨651479, by rfl⟩ : syracuseStep 868639 = 1302959) B1302959
theorem B868699 : Blo 868566 868699 := bstep (se 1 (by rfl) ⟨651524, by rfl⟩ : syracuseStep 868699 = 1303049) B1303049
theorem B868719 : Blo 868566 868719 := bstep (se 1 (by rfl) ⟨651539, by rfl⟩ : syracuseStep 868719 = 1303079) B1303079
theorem B868775 : Blo 868566 868775 := bstep (se 1 (by rfl) ⟨651581, by rfl⟩ : syracuseStep 868775 = 1303163) B1303163
theorem B868859 : Blo 868566 868859 := bstep (se 1 (by rfl) ⟨651644, by rfl⟩ : syracuseStep 868859 = 1303289) B1303289
theorem B868927 : Blo 868566 868927 := bstep (se 1 (by rfl) ⟨651695, by rfl⟩ : syracuseStep 868927 = 1303391) B1303391
theorem B868935 : Blo 868566 868935 := bstep (se 1 (by rfl) ⟨651701, by rfl⟩ : syracuseStep 868935 = 1303403) B1303403
theorem B869087 : Blo 868566 869087 := bstep (se 1 (by rfl) ⟨651815, by rfl⟩ : syracuseStep 869087 = 1303631) B1303631
theorem B869167 : Blo 868566 869167 := bstep (se 1 (by rfl) ⟨651875, by rfl⟩ : syracuseStep 869167 = 1303751) B1303751
theorem B869275 : Blo 868566 869275 := bstep (se 1 (by rfl) ⟨651956, by rfl⟩ : syracuseStep 869275 = 1303913) B1303913
theorem B23774147 : Blo 868566 23774147 := bstep (se 1 (by rfl) ⟨17830610, by rfl⟩ : syracuseStep 23774147 = 35661221) B35661221
theorem B869327 : Blo 868566 869327 := bstep (se 1 (by rfl) ⟨651995, by rfl⟩ : syracuseStep 869327 = 1303991) B1303991
theorem B869351 : Blo 868566 869351 := bstep (se 1 (by rfl) ⟨652013, by rfl⟩ : syracuseStep 869351 = 1304027) B1304027
theorem B10601705 : Blo 868566 10601705 := bstep (se 2 (by rfl) ⟨3975639, by rfl⟩ : syracuseStep 10601705 = 7951279) B7951279
theorem B869663 : Blo 868566 869663 := bstep (se 1 (by rfl) ⟨652247, by rfl⟩ : syracuseStep 869663 = 1304495) B1304495
theorem B1393951 : Blo 868566 1393951 := bstep (se 1 (by rfl) ⟨1045463, by rfl⟩ : syracuseStep 1393951 = 2090927) B2090927
theorem B869723 : Blo 868566 869723 := bstep (se 1 (by rfl) ⟨652292, by rfl⟩ : syracuseStep 869723 = 1304585) B1304585
theorem B869743 : Blo 868566 869743 := bstep (se 1 (by rfl) ⟨652307, by rfl⟩ : syracuseStep 869743 = 1304615) B1304615
theorem B869799 : Blo 868566 869799 := bstep (se 1 (by rfl) ⟨652349, by rfl⟩ : syracuseStep 869799 = 1304699) B1304699
theorem B15877619 : Blo 868566 15877619 := bstep (se 1 (by rfl) ⟨11908214, by rfl⟩ : syracuseStep 15877619 = 23816429) B23816429
theorem B869883 : Blo 868566 869883 := bstep (se 1 (by rfl) ⟨652412, by rfl⟩ : syracuseStep 869883 = 1304825) B1304825
theorem B1099327 : Blo 868566 1099327 := bstep (se 1 (by rfl) ⟨824495, by rfl⟩ : syracuseStep 1099327 = 1648991) B1648991
theorem B869951 : Blo 868566 869951 := bstep (se 1 (by rfl) ⟨652463, by rfl⟩ : syracuseStep 869951 = 1304927) B1304927
theorem B869959 : Blo 868566 869959 := bstep (se 1 (by rfl) ⟨652469, by rfl⟩ : syracuseStep 869959 = 1304939) B1304939
theorem B870111 : Blo 868566 870111 := bstep (se 1 (by rfl) ⟨652583, by rfl⟩ : syracuseStep 870111 = 1305167) B1305167
theorem B870191 : Blo 868566 870191 := bstep (se 1 (by rfl) ⟨652643, by rfl⟩ : syracuseStep 870191 = 1305287) B1305287
theorem B870299 : Blo 868566 870299 := bstep (se 1 (by rfl) ⟨652724, by rfl⟩ : syracuseStep 870299 = 1305449) B1305449
theorem B870351 : Blo 868566 870351 := bstep (se 1 (by rfl) ⟨652763, by rfl⟩ : syracuseStep 870351 = 1305527) B1305527
theorem B870375 : Blo 868566 870375 := bstep (se 1 (by rfl) ⟨652781, by rfl⟩ : syracuseStep 870375 = 1305563) B1305563
theorem B22268033 : Blo 868566 22268033 := bstep (se 2 (by rfl) ⟨8350512, by rfl⟩ : syracuseStep 22268033 = 16701025) B16701025
theorem B870687 : Blo 868566 870687 := bstep (se 1 (by rfl) ⟨653015, by rfl⟩ : syracuseStep 870687 = 1306031) B1306031
theorem B1100071 : Blo 868566 1100071 := bstep (se 1 (by rfl) ⟨825053, by rfl⟩ : syracuseStep 1100071 = 1650107) B1650107
theorem B245057879 : Blo 868566 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B870747 : Blo 868566 870747 := bstep (se 1 (by rfl) ⟨653060, by rfl⟩ : syracuseStep 870747 = 1306121) B1306121
theorem B870767 : Blo 868566 870767 := bstep (se 1 (by rfl) ⟨653075, by rfl⟩ : syracuseStep 870767 = 1306151) B1306151
theorem B870823 : Blo 868566 870823 := bstep (se 1 (by rfl) ⟨653117, by rfl⟩ : syracuseStep 870823 = 1306235) B1306235
theorem B2935223 : Blo 868566 2935223 := bstep (se 1 (by rfl) ⟨2201417, by rfl⟩ : syracuseStep 2935223 = 4402835) B4402835
theorem B870907 : Blo 868566 870907 := bstep (se 1 (by rfl) ⟨653180, by rfl⟩ : syracuseStep 870907 = 1306361) B1306361
theorem B870975 : Blo 868566 870975 := bstep (se 1 (by rfl) ⟨653231, by rfl⟩ : syracuseStep 870975 = 1306463) B1306463
theorem B870983 : Blo 868566 870983 := bstep (se 1 (by rfl) ⟨653237, by rfl⟩ : syracuseStep 870983 = 1306475) B1306475
theorem B1100395 : Blo 868566 1100395 := bstep (se 1 (by rfl) ⟨825296, by rfl⟩ : syracuseStep 1100395 = 1650593) B1650593
theorem B4409963 : Blo 868566 4409963 := bstep (se 1 (by rfl) ⟨3307472, by rfl⟩ : syracuseStep 4409963 = 6614945) B6614945
theorem B871135 : Blo 868566 871135 := bstep (se 1 (by rfl) ⟨653351, by rfl⟩ : syracuseStep 871135 = 1306703) B1306703
theorem B871215 : Blo 868566 871215 := bstep (se 1 (by rfl) ⟨653411, by rfl⟩ : syracuseStep 871215 = 1306823) B1306823
theorem B1100623 : Blo 868566 1100623 := bstep (se 1 (by rfl) ⟨825467, by rfl⟩ : syracuseStep 1100623 = 1650935) B1650935
theorem B871323 : Blo 868566 871323 := bstep (se 1 (by rfl) ⟨653492, by rfl⟩ : syracuseStep 871323 = 1306985) B1306985
theorem B871375 : Blo 868566 871375 := bstep (se 1 (by rfl) ⟨653531, by rfl⟩ : syracuseStep 871375 = 1307063) B1307063
theorem B871399 : Blo 868566 871399 := bstep (se 1 (by rfl) ⟨653549, by rfl⟩ : syracuseStep 871399 = 1307099) B1307099
theorem B4410449 : Blo 868566 4410449 := bstep (se 2 (by rfl) ⟨1653918, by rfl⟩ : syracuseStep 4410449 = 3307837) B3307837
theorem B871711 : Blo 868566 871711 := bstep (se 1 (by rfl) ⟨653783, by rfl⟩ : syracuseStep 871711 = 1307567) B1307567
theorem B26791229 : Blo 868566 26791229 := bstep (se 3 (by rfl) ⟨5023355, by rfl⟩ : syracuseStep 26791229 = 10046711) B10046711
theorem B871771 : Blo 868566 871771 := bstep (se 1 (by rfl) ⟨653828, by rfl⟩ : syracuseStep 871771 = 1307657) B1307657
theorem B871791 : Blo 868566 871791 := bstep (se 1 (by rfl) ⟨653843, by rfl⟩ : syracuseStep 871791 = 1307687) B1307687
theorem B871847 : Blo 868566 871847 := bstep (se 1 (by rfl) ⟨653885, by rfl⟩ : syracuseStep 871847 = 1307771) B1307771
theorem B871931 : Blo 868566 871931 := bstep (se 1 (by rfl) ⟨653948, by rfl⟩ : syracuseStep 871931 = 1307897) B1307897
theorem B871999 : Blo 868566 871999 := bstep (se 1 (by rfl) ⟨653999, by rfl⟩ : syracuseStep 871999 = 1307999) B1307999
theorem B872007 : Blo 868566 872007 := bstep (se 1 (by rfl) ⟨654005, by rfl⟩ : syracuseStep 872007 = 1308011) B1308011
theorem B872159 : Blo 868566 872159 := bstep (se 1 (by rfl) ⟨654119, by rfl⟩ : syracuseStep 872159 = 1308239) B1308239
theorem B2477803 : Blo 868566 2477803 := bstep (se 1 (by rfl) ⟨1858352, by rfl⟩ : syracuseStep 2477803 = 3716705) B3716705
theorem B872239 : Blo 868566 872239 := bstep (se 1 (by rfl) ⟨654179, by rfl⟩ : syracuseStep 872239 = 1308359) B1308359
theorem B872347 : Blo 868566 872347 := bstep (se 1 (by rfl) ⟨654260, by rfl⟩ : syracuseStep 872347 = 1308521) B1308521
theorem B18796445 : Blo 868566 18796445 := bstep (se 3 (by rfl) ⟨3524333, by rfl⟩ : syracuseStep 18796445 = 7048667) B7048667
theorem B872399 : Blo 868566 872399 := bstep (se 1 (by rfl) ⟨654299, by rfl⟩ : syracuseStep 872399 = 1308599) B1308599
theorem B872423 : Blo 868566 872423 := bstep (se 1 (by rfl) ⟨654317, by rfl⟩ : syracuseStep 872423 = 1308635) B1308635
theorem B1954367 : Blo 868566 1954367 := bstep (se 1 (by rfl) ⟨1465775, by rfl⟩ : syracuseStep 1954367 = 2931551) B2931551
theorem B1954475 : Blo 868566 1954475 := bstep (se 1 (by rfl) ⟨1465856, by rfl⟩ : syracuseStep 1954475 = 2931713) B2931713
theorem B1102511 : Blo 868566 1102511 := bstep (se 1 (by rfl) ⟨826883, by rfl⟩ : syracuseStep 1102511 = 1653767) B1653767
theorem B2479079 : Blo 868566 2479079 := bstep (se 1 (by rfl) ⟨1859309, by rfl⟩ : syracuseStep 2479079 = 3718619) B3718619
theorem B1955015 : Blo 868566 1955015 := bstep (se 1 (by rfl) ⟨1466261, by rfl⟩ : syracuseStep 1955015 = 2932523) B2932523
theorem B3921095 : Blo 868566 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B2479319 : Blo 868566 2479319 := bstep (se 1 (by rfl) ⟨1859489, by rfl⟩ : syracuseStep 2479319 = 3718979) B3718979
theorem B3298603 : Blo 868566 3298603 := bstep (se 1 (by rfl) ⟨2473952, by rfl⟩ : syracuseStep 3298603 = 4947905) B4947905
theorem B1103215 : Blo 868566 1103215 := bstep (se 1 (by rfl) ⟨827411, by rfl⟩ : syracuseStep 1103215 = 1654823) B1654823
theorem B1955195 : Blo 868566 1955195 := bstep (se 1 (by rfl) ⟨1466396, by rfl⟩ : syracuseStep 1955195 = 2932793) B2932793
theorem B3724667 : Blo 868566 3724667 := bstep (se 1 (by rfl) ⟨2793500, by rfl⟩ : syracuseStep 3724667 = 5587001) B5587001
theorem B2938301 : Blo 868566 2938301 := bstep (se 3 (by rfl) ⟨550931, by rfl⟩ : syracuseStep 2938301 = 1101863) B1101863
theorem B1955321 : Blo 868566 1955321 := bstep (se 2 (by rfl) ⟨733245, by rfl⟩ : syracuseStep 1955321 = 1466491) B1466491
theorem B1955411 : Blo 868566 1955411 := bstep (se 1 (by rfl) ⟨1466558, by rfl⟩ : syracuseStep 1955411 = 2933117) B2933117
theorem B3135133 : Blo 868566 3135133 := bstep (se 3 (by rfl) ⟨587837, by rfl⟩ : syracuseStep 3135133 = 1175675) B1175675
theorem B1857259 : Blo 868566 1857259 := bstep (se 1 (by rfl) ⟨1392944, by rfl⟩ : syracuseStep 1857259 = 2785889) B2785889
theorem B1955591 : Blo 868566 1955591 := bstep (se 1 (by rfl) ⟨1466693, by rfl⟩ : syracuseStep 1955591 = 2933387) B2933387
theorem B2938679 : Blo 868566 2938679 := bstep (se 1 (by rfl) ⟨2204009, by rfl⟩ : syracuseStep 2938679 = 4408019) B4408019
theorem B4708151 : Blo 868566 4708151 := bstep (se 1 (by rfl) ⟨3531113, by rfl⟩ : syracuseStep 4708151 = 7062227) B7062227
theorem B17848349 : Blo 868566 17848349 := bstep (se 3 (by rfl) ⟨3346565, by rfl⟩ : syracuseStep 17848349 = 6693131) B6693131
theorem B7952417 : Blo 868566 7952417 := bstep (se 2 (by rfl) ⟨2982156, by rfl⟩ : syracuseStep 7952417 = 5964313) B5964313
theorem B2939165 : Blo 868566 2939165 := bstep (se 3 (by rfl) ⟨551093, by rfl⟩ : syracuseStep 2939165 = 1102187) B1102187
theorem B1956203 : Blo 868566 1956203 := bstep (se 1 (by rfl) ⟨1467152, by rfl⟩ : syracuseStep 1956203 = 2934305) B2934305
theorem B25385399 : Blo 868566 25385399 := bstep (se 1 (by rfl) ⟨19039049, by rfl⟩ : syracuseStep 25385399 = 38078099) B38078099
theorem B1956347 : Blo 868566 1956347 := bstep (se 1 (by rfl) ⟨1467260, by rfl⟩ : syracuseStep 1956347 = 2934521) B2934521
theorem B2480719 : Blo 868566 2480719 := bstep (se 1 (by rfl) ⟨1860539, by rfl⟩ : syracuseStep 2480719 = 3721079) B3721079
theorem B1956473 : Blo 868566 1956473 := bstep (se 2 (by rfl) ⟨733677, by rfl⟩ : syracuseStep 1956473 = 1467355) B1467355
theorem B1956527 : Blo 868566 1956527 := bstep (se 1 (by rfl) ⟨1467395, by rfl⟩ : syracuseStep 1956527 = 2934791) B2934791
theorem B1956599 : Blo 868566 1956599 := bstep (se 1 (by rfl) ⟨1467449, by rfl⟩ : syracuseStep 1956599 = 2934899) B2934899
theorem B2087851 : Blo 868566 2087851 := bstep (se 1 (by rfl) ⟨1565888, by rfl⟩ : syracuseStep 2087851 = 3131777) B3131777
theorem B1956779 : Blo 868566 1956779 := bstep (se 1 (by rfl) ⟨1467584, by rfl⟩ : syracuseStep 1956779 = 2935169) B2935169
theorem B7167005 : Blo 868566 7167005 := bstep (se 3 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 7167005 = 2687627) B2687627
theorem B6610085 : Blo 868566 6610085 := bstep (se 4 (by rfl) ⟨619695, by rfl⟩ : syracuseStep 6610085 = 1239391) B1239391
theorem B183196853 : Blo 868566 183196853 := bstep (se 5 (by rfl) ⟨8587352, by rfl⟩ : syracuseStep 183196853 = 17174705) B17174705
theorem B2350313 : Blo 868566 2350313 := bstep (se 2 (by rfl) ⟨881367, by rfl⟩ : syracuseStep 2350313 = 1762735) B1762735
theorem B2940191 : Blo 868566 2940191 := bstep (se 1 (by rfl) ⟨2205143, by rfl⟩ : syracuseStep 2940191 = 4410287) B4410287
theorem B1957319 : Blo 868566 1957319 := bstep (se 1 (by rfl) ⟨1467989, by rfl⟩ : syracuseStep 1957319 = 2935979) B2935979
theorem B2481607 : Blo 868566 2481607 := bstep (se 1 (by rfl) ⟨1861205, by rfl⟩ : syracuseStep 2481607 = 3722411) B3722411
theorem B4414985 : Blo 868566 4414985 := bstep (se 2 (by rfl) ⟨1655619, by rfl⟩ : syracuseStep 4414985 = 3311239) B3311239
theorem B1465951 : Blo 868566 1465951 := bstep (se 1 (by rfl) ⟨1099463, by rfl⟩ : syracuseStep 1465951 = 2198927) B2198927
theorem B2481961 : Blo 868566 2481961 := bstep (se 2 (by rfl) ⟨930735, by rfl⟩ : syracuseStep 2481961 = 1861471) B1861471
theorem B1957679 : Blo 868566 1957679 := bstep (se 1 (by rfl) ⟨1468259, by rfl⟩ : syracuseStep 1957679 = 2936519) B2936519
theorem B1466167 : Blo 868566 1466167 := bstep (se 1 (by rfl) ⟨1099625, by rfl⟩ : syracuseStep 1466167 = 2199251) B2199251
theorem B2514845 : Blo 868566 2514845 := bstep (se 3 (by rfl) ⟨471533, by rfl⟩ : syracuseStep 2514845 = 943067) B943067
theorem B6283183 : Blo 868566 6283183 := bstep (se 1 (by rfl) ⟨4712387, by rfl⟩ : syracuseStep 6283183 = 9424775) B9424775
theorem B28237997 : Blo 868566 28237997 := bstep (se 3 (by rfl) ⟨5294624, by rfl⟩ : syracuseStep 28237997 = 10589249) B10589249
theorem B1466633 : Blo 868566 1466633 := bstep (se 2 (by rfl) ⟨549987, by rfl⟩ : syracuseStep 1466633 = 1099975) B1099975
theorem B1302875 : Blo 868566 1302875 := bstep (se 1 (by rfl) ⟨977156, by rfl⟩ : syracuseStep 1302875 = 1954313) B1954313
theorem B1958255 : Blo 868566 1958255 := bstep (se 1 (by rfl) ⟨1468691, by rfl⟩ : syracuseStep 1958255 = 2937383) B2937383
theorem B1958327 : Blo 868566 1958327 := bstep (se 1 (by rfl) ⟨1468745, by rfl⟩ : syracuseStep 1958327 = 2937491) B2937491
theorem B1303103 : Blo 868566 1303103 := bstep (se 1 (by rfl) ⟨977327, by rfl⟩ : syracuseStep 1303103 = 1954655) B1954655
theorem B1958471 : Blo 868566 1958471 := bstep (se 1 (by rfl) ⟨1468853, by rfl⟩ : syracuseStep 1958471 = 2937707) B2937707
theorem B1958507 : Blo 868566 1958507 := bstep (se 1 (by rfl) ⟨1468880, by rfl⟩ : syracuseStep 1958507 = 2937761) B2937761
theorem B1303223 : Blo 868566 1303223 := bstep (se 1 (by rfl) ⟨977417, by rfl⟩ : syracuseStep 1303223 = 1954835) B1954835
theorem B1303451 : Blo 868566 1303451 := bstep (se 1 (by rfl) ⟨977588, by rfl⟩ : syracuseStep 1303451 = 1955177) B1955177
theorem B2515931 : Blo 868566 2515931 := bstep (se 1 (by rfl) ⟨1886948, by rfl⟩ : syracuseStep 2515931 = 3773897) B3773897
theorem B1860583 : Blo 868566 1860583 := bstep (se 1 (by rfl) ⟨1395437, by rfl⟩ : syracuseStep 1860583 = 2790875) B2790875
theorem B1958903 : Blo 868566 1958903 := bstep (se 1 (by rfl) ⟨1469177, by rfl⟩ : syracuseStep 1958903 = 2938355) B2938355
theorem B2089975 : Blo 868566 2089975 := bstep (se 1 (by rfl) ⟨1567481, by rfl⟩ : syracuseStep 2089975 = 3134963) B3134963
theorem B4023353 : Blo 868566 4023353 := bstep (se 2 (by rfl) ⟨1508757, by rfl⟩ : syracuseStep 4023353 = 3017515) B3017515
theorem B9528463 : Blo 868566 9528463 := bstep (se 1 (by rfl) ⟨7146347, by rfl⟩ : syracuseStep 9528463 = 14292695) B14292695
theorem B2352347 : Blo 868566 2352347 := bstep (se 1 (by rfl) ⟨1764260, by rfl⟩ : syracuseStep 2352347 = 3528521) B3528521
theorem B1467625 : Blo 868566 1467625 := bstep (se 2 (by rfl) ⟨550359, by rfl⟩ : syracuseStep 1467625 = 1100719) B1100719
theorem B1467679 : Blo 868566 1467679 := bstep (se 1 (by rfl) ⟨1100759, by rfl⟩ : syracuseStep 1467679 = 2201519) B2201519
theorem B1303847 : Blo 868566 1303847 := bstep (se 1 (by rfl) ⟨977885, by rfl⟩ : syracuseStep 1303847 = 1955771) B1955771
theorem B1959263 : Blo 868566 1959263 := bstep (se 1 (by rfl) ⟨1469447, by rfl⟩ : syracuseStep 1959263 = 2938895) B2938895
theorem B3302765 : Blo 868566 3302765 := bstep (se 3 (by rfl) ⟨619268, by rfl⟩ : syracuseStep 3302765 = 1238537) B1238537
theorem B1303931 : Blo 868566 1303931 := bstep (se 1 (by rfl) ⟨977948, by rfl⟩ : syracuseStep 1303931 = 1955897) B1955897
theorem B3302795 : Blo 868566 3302795 := bstep (se 1 (by rfl) ⟨2477096, by rfl⟩ : syracuseStep 3302795 = 4954193) B4954193
theorem B4416929 : Blo 868566 4416929 := bstep (se 2 (by rfl) ⟨1656348, by rfl⟩ : syracuseStep 4416929 = 3312697) B3312697
theorem B1304057 : Blo 868566 1304057 := bstep (se 2 (by rfl) ⟨489021, by rfl⟩ : syracuseStep 1304057 = 978043) B978043
theorem B8382041 : Blo 868566 8382041 := bstep (se 2 (by rfl) ⟨3143265, by rfl⟩ : syracuseStep 8382041 = 6286531) B6286531
theorem B1304159 : Blo 868566 1304159 := bstep (se 1 (by rfl) ⟨978119, by rfl⟩ : syracuseStep 1304159 = 1956239) B1956239
theorem B3139229 : Blo 868566 3139229 := bstep (se 3 (by rfl) ⟨588605, by rfl⟩ : syracuseStep 3139229 = 1177211) B1177211
theorem B2942621 : Blo 868566 2942621 := bstep (se 3 (by rfl) ⟨551741, by rfl⟩ : syracuseStep 2942621 = 1103483) B1103483
theorem B1468091 : Blo 868566 1468091 := bstep (se 1 (by rfl) ⟨1101068, by rfl⟩ : syracuseStep 1468091 = 2202137) B2202137
theorem B1763051 : Blo 868566 1763051 := bstep (se 1 (by rfl) ⟨1322288, by rfl⟩ : syracuseStep 1763051 = 2644577) B2644577
theorem B1959659 : Blo 868566 1959659 := bstep (se 1 (by rfl) ⟨1469744, by rfl⟩ : syracuseStep 1959659 = 2939489) B2939489
theorem B1304375 : Blo 868566 1304375 := bstep (se 1 (by rfl) ⟨978281, by rfl⟩ : syracuseStep 1304375 = 1956563) B1956563
theorem B1959785 : Blo 868566 1959785 := bstep (se 2 (by rfl) ⟨734919, by rfl⟩ : syracuseStep 1959785 = 1469839) B1469839
theorem B1304681 : Blo 868566 1304681 := bstep (se 2 (by rfl) ⟨489255, by rfl⟩ : syracuseStep 1304681 = 978511) B978511
theorem B2943161 : Blo 868566 2943161 := bstep (se 2 (by rfl) ⟨1103685, by rfl⟩ : syracuseStep 2943161 = 2207371) B2207371
theorem B1304999 : Blo 868566 1304999 := bstep (se 1 (by rfl) ⟨978749, by rfl⟩ : syracuseStep 1304999 = 1957499) B1957499
theorem B1305083 : Blo 868566 1305083 := bstep (se 1 (by rfl) ⟨978812, by rfl⟩ : syracuseStep 1305083 = 1957625) B1957625
theorem B6777431 : Blo 868566 6777431 := bstep (se 1 (by rfl) ⟨5083073, by rfl⟩ : syracuseStep 6777431 = 10166147) B10166147
theorem B977503 : Blo 868566 977503 := bstep (se 1 (by rfl) ⟨733127, by rfl⟩ : syracuseStep 977503 = 1466255) B1466255
theorem B1305209 : Blo 868566 1305209 := bstep (se 2 (by rfl) ⟨489453, by rfl⟩ : syracuseStep 1305209 = 978907) B978907
theorem B1305263 : Blo 868566 1305263 := bstep (se 1 (by rfl) ⟨978947, by rfl⟩ : syracuseStep 1305263 = 1957895) B1957895
theorem B1960631 : Blo 868566 1960631 := bstep (se 1 (by rfl) ⟨1470473, by rfl⟩ : syracuseStep 1960631 = 2940947) B2940947
theorem B1305311 : Blo 868566 1305311 := bstep (se 1 (by rfl) ⟨978983, by rfl⟩ : syracuseStep 1305311 = 1957967) B1957967
theorem B1239887 : Blo 868566 1239887 := bstep (se 1 (by rfl) ⟨929915, by rfl⟩ : syracuseStep 1239887 = 1859831) B1859831
theorem B1960847 : Blo 868566 1960847 := bstep (se 1 (by rfl) ⟨1470635, by rfl⟩ : syracuseStep 1960847 = 2941271) B2941271
theorem B1305575 : Blo 868566 1305575 := bstep (se 1 (by rfl) ⟨979181, by rfl⟩ : syracuseStep 1305575 = 1958363) B1958363
theorem B3304435 : Blo 868566 3304435 := bstep (se 1 (by rfl) ⟨2478326, by rfl⟩ : syracuseStep 3304435 = 4956653) B4956653
theorem B1305833 : Blo 868566 1305833 := bstep (se 2 (by rfl) ⟨489687, by rfl⟩ : syracuseStep 1305833 = 979375) B979375
theorem B1305887 : Blo 868566 1305887 := bstep (se 1 (by rfl) ⟨979415, by rfl⟩ : syracuseStep 1305887 = 1958831) B1958831
theorem B2092319 : Blo 868566 2092319 := bstep (se 1 (by rfl) ⟨1569239, by rfl⟩ : syracuseStep 2092319 = 3138479) B3138479
theorem B1469819 : Blo 868566 1469819 := bstep (se 1 (by rfl) ⟨1102364, by rfl⟩ : syracuseStep 1469819 = 2204729) B2204729
theorem B6614459 : Blo 868566 6614459 := bstep (se 1 (by rfl) ⟨4960844, by rfl⟩ : syracuseStep 6614459 = 9921689) B9921689
theorem B1306055 : Blo 868566 1306055 := bstep (se 1 (by rfl) ⟨979541, by rfl⟩ : syracuseStep 1306055 = 1959083) B1959083
theorem B1961567 : Blo 868566 1961567 := bstep (se 1 (by rfl) ⟨1471175, by rfl⟩ : syracuseStep 1961567 = 2942351) B2942351
theorem B2944673 : Blo 868566 2944673 := bstep (se 2 (by rfl) ⟨1104252, by rfl⟩ : syracuseStep 2944673 = 2208505) B2208505
theorem B978655 : Blo 868566 978655 := bstep (se 1 (by rfl) ⟨733991, by rfl⟩ : syracuseStep 978655 = 1467983) B1467983
theorem B3305195 : Blo 868566 3305195 := bstep (se 1 (by rfl) ⟨2478896, by rfl⟩ : syracuseStep 3305195 = 4957793) B4957793
theorem B1306409 : Blo 868566 1306409 := bstep (se 2 (by rfl) ⟨489903, by rfl⟩ : syracuseStep 1306409 = 979807) B979807
theorem B1306415 : Blo 868566 1306415 := bstep (se 1 (by rfl) ⟨979811, by rfl⟩ : syracuseStep 1306415 = 1959623) B1959623
theorem B1961783 : Blo 868566 1961783 := bstep (se 1 (by rfl) ⟨1471337, by rfl⟩ : syracuseStep 1961783 = 2942675) B2942675
theorem B1863479 : Blo 868566 1863479 := bstep (se 1 (by rfl) ⟨1397609, by rfl⟩ : syracuseStep 1863479 = 2795219) B2795219
theorem B1962089 : Blo 868566 1962089 := bstep (se 2 (by rfl) ⟨735783, by rfl⟩ : syracuseStep 1962089 = 1471567) B1471567
theorem B2355329 : Blo 868566 2355329 := bstep (se 2 (by rfl) ⟨883248, by rfl⟩ : syracuseStep 2355329 = 1766497) B1766497
theorem B3305681 : Blo 868566 3305681 := bstep (se 2 (by rfl) ⟨1239630, by rfl⟩ : syracuseStep 3305681 = 2479261) B2479261
theorem B1306889 : Blo 868566 1306889 := bstep (se 2 (by rfl) ⟨490083, by rfl⟩ : syracuseStep 1306889 = 980167) B980167
theorem B979231 : Blo 868566 979231 := bstep (se 1 (by rfl) ⟨734423, by rfl⟩ : syracuseStep 979231 = 1468847) B1468847
theorem B1470811 : Blo 868566 1470811 := bstep (se 1 (by rfl) ⟨1103108, by rfl⟩ : syracuseStep 1470811 = 2206217) B2206217
theorem B1306991 : Blo 868566 1306991 := bstep (se 1 (by rfl) ⟨980243, by rfl⟩ : syracuseStep 1306991 = 1960487) B1960487
theorem B10711601 : Blo 868566 10711601 := bstep (se 2 (by rfl) ⟨4016850, by rfl⟩ : syracuseStep 10711601 = 8033701) B8033701
theorem B4190771 : Blo 868566 4190771 := bstep (se 1 (by rfl) ⟨3143078, by rfl⟩ : syracuseStep 4190771 = 6286157) B6286157
theorem B979519 : Blo 868566 979519 := bstep (se 1 (by rfl) ⟨734639, by rfl⟩ : syracuseStep 979519 = 1469279) B1469279
theorem B1307207 : Blo 868566 1307207 := bstep (se 1 (by rfl) ⟨980405, by rfl⟩ : syracuseStep 1307207 = 1960811) B1960811
theorem B1962575 : Blo 868566 1962575 := bstep (se 1 (by rfl) ⟨1471931, by rfl⟩ : syracuseStep 1962575 = 2943863) B2943863
theorem B1307243 : Blo 868566 1307243 := bstep (se 1 (by rfl) ⟨980432, by rfl⟩ : syracuseStep 1307243 = 1960865) B1960865
theorem B4715155 : Blo 868566 4715155 := bstep (se 1 (by rfl) ⟨3536366, by rfl⟩ : syracuseStep 4715155 = 7072733) B7072733
theorem B2716343 : Blo 868566 2716343 := bstep (se 1 (by rfl) ⟨2037257, by rfl⟩ : syracuseStep 2716343 = 4074515) B4074515
theorem B3306167 : Blo 868566 3306167 := bstep (se 1 (by rfl) ⟨2479625, by rfl⟩ : syracuseStep 3306167 = 4959251) B4959251
theorem B1962719 : Blo 868566 1962719 := bstep (se 1 (by rfl) ⟨1472039, by rfl⟩ : syracuseStep 1962719 = 2944079) B2944079
theorem B1307471 : Blo 868566 1307471 := bstep (se 1 (by rfl) ⟨980603, by rfl⟩ : syracuseStep 1307471 = 1961207) B1961207
theorem B6615917 : Blo 868566 6615917 := bstep (se 3 (by rfl) ⟨1240484, by rfl⟩ : syracuseStep 6615917 = 2480969) B2480969
theorem B35779441 : Blo 868566 35779441 := bstep (se 2 (by rfl) ⟨13417290, by rfl⟩ : syracuseStep 35779441 = 26834581) B26834581
theorem B1242011 : Blo 868566 1242011 := bstep (se 1 (by rfl) ⟨931508, by rfl⟩ : syracuseStep 1242011 = 1863017) B1863017
theorem B1962971 : Blo 868566 1962971 := bstep (se 1 (by rfl) ⟨1472228, by rfl⟩ : syracuseStep 1962971 = 2944457) B2944457
theorem B3142631 : Blo 868566 3142631 := bstep (se 1 (by rfl) ⟨2356973, by rfl⟩ : syracuseStep 3142631 = 4713947) B4713947
theorem B1963151 : Blo 868566 1963151 := bstep (se 1 (by rfl) ⟨1472363, by rfl⟩ : syracuseStep 1963151 = 2944727) B2944727
theorem B1307867 : Blo 868566 1307867 := bstep (se 1 (by rfl) ⟨980900, by rfl⟩ : syracuseStep 1307867 = 1961801) B1961801
theorem B1963241 : Blo 868566 1963241 := bstep (se 2 (by rfl) ⟨736215, by rfl⟩ : syracuseStep 1963241 = 1472431) B1472431
theorem B1471783 : Blo 868566 1471783 := bstep (se 1 (by rfl) ⟨1103837, by rfl⟩ : syracuseStep 1471783 = 2207675) B2207675
theorem B980347 : Blo 868566 980347 := bstep (se 1 (by rfl) ⟨735260, by rfl⟩ : syracuseStep 980347 = 1470521) B1470521
theorem B1308041 : Blo 868566 1308041 := bstep (se 2 (by rfl) ⟨490515, by rfl⟩ : syracuseStep 1308041 = 981031) B981031
theorem B1766855 : Blo 868566 1766855 := bstep (se 1 (by rfl) ⟨1325141, by rfl⟩ : syracuseStep 1766855 = 2650283) B2650283
theorem B2094779 : Blo 868566 2094779 := bstep (se 1 (by rfl) ⟨1571084, by rfl⟩ : syracuseStep 2094779 = 3142169) B3142169
theorem B1308395 : Blo 868566 1308395 := bstep (se 1 (by rfl) ⟨981296, by rfl⟩ : syracuseStep 1308395 = 1962593) B1962593
theorem B1472303 : Blo 868566 1472303 := bstep (se 1 (by rfl) ⟨1104227, by rfl⟩ : syracuseStep 1472303 = 2208455) B2208455
theorem B980815 : Blo 868566 980815 := bstep (se 1 (by rfl) ⟨735611, by rfl⟩ : syracuseStep 980815 = 1471223) B1471223
theorem B3307351 : Blo 868566 3307351 := bstep (se 1 (by rfl) ⟨2480513, by rfl⟩ : syracuseStep 3307351 = 4961027) B4961027
theorem B8943547 : Blo 868566 8943547 := bstep (se 1 (by rfl) ⟨6707660, by rfl⟩ : syracuseStep 8943547 = 13415321) B13415321
theorem B1308623 : Blo 868566 1308623 := bstep (se 1 (by rfl) ⟨981467, by rfl⟩ : syracuseStep 1308623 = 1962935) B1962935
theorem B3307655 : Blo 868566 3307655 := bstep (se 1 (by rfl) ⟨2480741, by rfl⟩ : syracuseStep 3307655 = 4961483) B4961483
theorem B981211 : Blo 868566 981211 := bstep (se 1 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 981211 = 1471817) B1471817
theorem B3963161 : Blo 868566 3963161 := bstep (se 2 (by rfl) ⟨1486185, by rfl⟩ : syracuseStep 3963161 = 2972371) B2972371
theorem B2095471 : Blo 868566 2095471 := bstep (se 1 (by rfl) ⟨1571603, by rfl⟩ : syracuseStep 2095471 = 3143207) B3143207
theorem B981499 : Blo 868566 981499 := bstep (se 1 (by rfl) ⟨736124, by rfl⟩ : syracuseStep 981499 = 1472249) B1472249
theorem B3963455 : Blo 868566 3963455 := bstep (se 1 (by rfl) ⟨2972591, by rfl⟩ : syracuseStep 3963455 = 5945183) B5945183
theorem B1768007 : Blo 868566 1768007 := bstep (se 1 (by rfl) ⟨1326005, by rfl⟩ : syracuseStep 1768007 = 2652011) B2652011
theorem B3308111 : Blo 868566 3308111 := bstep (se 1 (by rfl) ⟨2481083, by rfl⟩ : syracuseStep 3308111 = 4962167) B4962167
theorem B2358035 : Blo 868566 2358035 := bstep (se 1 (by rfl) ⟨1768526, by rfl⟩ : syracuseStep 2358035 = 3537053) B3537053
theorem B22346765 : Blo 868566 22346765 := bstep (se 3 (by rfl) ⟨4190018, by rfl⟩ : syracuseStep 22346765 = 8380037) B8380037
theorem B7044259 : Blo 868566 7044259 := bstep (se 1 (by rfl) ⟨5283194, by rfl⟩ : syracuseStep 7044259 = 10566389) B10566389
theorem B2358521 : Blo 868566 2358521 := bstep (se 2 (by rfl) ⟨884445, by rfl⟩ : syracuseStep 2358521 = 1768891) B1768891
theorem B884287 : Blo 868566 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B23856029 : Blo 868566 23856029 := bstep (se 3 (by rfl) ⟨4473005, by rfl⟩ : syracuseStep 23856029 = 8946011) B8946011
theorem B10585079 : Blo 868566 10585079 := bstep (se 1 (by rfl) ⟨7938809, by rfl⟩ : syracuseStep 10585079 = 15877619) B15877619
theorem B2786633 : Blo 868566 2786633 := bstep (se 2 (by rfl) ⟨1044987, by rfl⟩ : syracuseStep 2786633 = 2089975) B2089975
theorem B14845355 : Blo 868566 14845355 := bstep (se 1 (by rfl) ⟨11134016, by rfl⟩ : syracuseStep 14845355 = 22268033) B22268033
theorem B90540109 : Blo 868566 90540109 := bstep (se 3 (by rfl) ⟨16976270, by rfl⟩ : syracuseStep 90540109 = 33952541) B33952541
theorem B17860819 : Blo 868566 17860819 := bstep (se 1 (by rfl) ⟨13395614, by rfl⟩ : syracuseStep 17860819 = 26791229) B26791229
theorem B5572955 : Blo 868566 5572955 := bstep (se 1 (by rfl) ⟨4179716, by rfl⟩ : syracuseStep 5572955 = 8359433) B8359433
theorem B3312029 : Blo 868566 3312029 := bstep (se 3 (by rfl) ⟨621005, by rfl⟩ : syracuseStep 3312029 = 1242011) B1242011
theorem B1674361 : Blo 868566 1674361 := bstep (se 2 (by rfl) ⟨627885, by rfl⟩ : syracuseStep 1674361 = 1255771) B1255771
theorem B10456253 : Blo 868566 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B11898899 : Blo 868566 11898899 := bstep (se 1 (by rfl) ⟨8924174, by rfl⟩ : syracuseStep 11898899 = 17848349) B17848349
theorem B14094607 : Blo 868566 14094607 := bstep (se 1 (by rfl) ⟨10570955, by rfl⟩ : syracuseStep 14094607 = 21141911) B21141911
theorem B5968255 : Blo 868566 5968255 := bstep (se 1 (by rfl) ⟨4476191, by rfl⟩ : syracuseStep 5968255 = 8952383) B8952383
theorem B1413625 : Blo 868566 1413625 := bstep (se 2 (by rfl) ⟨530109, by rfl⟩ : syracuseStep 1413625 = 1060219) B1060219
theorem B122131235 : Blo 868566 122131235 := bstep (se 1 (by rfl) ⟨91598426, by rfl⟩ : syracuseStep 122131235 = 183196853) B183196853
theorem B42374117 : Blo 868566 42374117 := bstep (se 4 (by rfl) ⟨3972573, by rfl⟩ : syracuseStep 42374117 = 7945147) B7945147
theorem B4461743 : Blo 868566 4461743 := bstep (se 1 (by rfl) ⟨3346307, by rfl⟩ : syracuseStep 4461743 = 6692615) B6692615
theorem B3347675 : Blo 868566 3347675 := bstep (se 1 (by rfl) ⟨2510756, by rfl⟩ : syracuseStep 3347675 = 5021513) B5021513
theorem B1677287 : Blo 868566 1677287 := bstep (se 1 (by rfl) ⟨1257965, by rfl⟩ : syracuseStep 1677287 = 2515931) B2515931
theorem B2201843 : Blo 868566 2201843 := bstep (se 1 (by rfl) ⟨1651382, by rfl⟩ : syracuseStep 2201843 = 3302765) B3302765
theorem B2201863 : Blo 868566 2201863 := bstep (se 1 (by rfl) ⟨1651397, by rfl⟩ : syracuseStep 2201863 = 3302795) B3302795
theorem B4398137 : Blo 868566 4398137 := bstep (se 2 (by rfl) ⟨1649301, by rfl⟩ : syracuseStep 4398137 = 3298603) B3298603
theorem B2235521 : Blo 868566 2235521 := bstep (se 2 (by rfl) ⟨838320, by rfl⟩ : syracuseStep 2235521 = 1676641) B1676641
theorem B2203463 : Blo 868566 2203463 := bstep (se 1 (by rfl) ⟨1652597, by rfl⟩ : syracuseStep 2203463 = 3305195) B3305195
theorem B2203787 : Blo 868566 2203787 := bstep (se 1 (by rfl) ⟨1652840, by rfl⟩ : syracuseStep 2203787 = 3305681) B3305681
theorem B2793847 : Blo 868566 2793847 := bstep (se 1 (by rfl) ⟨2095385, by rfl⟩ : syracuseStep 2793847 = 4190771) B4190771
theorem B1810895 : Blo 868566 1810895 := bstep (se 1 (by rfl) ⟨1358171, by rfl⟩ : syracuseStep 1810895 = 2716343) B2716343
theorem B2204111 : Blo 868566 2204111 := bstep (se 1 (by rfl) ⟨1653083, by rfl⟩ : syracuseStep 2204111 = 3306167) B3306167
theorem B2793961 : Blo 868566 2793961 := bstep (se 2 (by rfl) ⟨1047735, by rfl⟩ : syracuseStep 2793961 = 2095471) B2095471
theorem B18359297 : Blo 868566 18359297 := bstep (se 2 (by rfl) ⟨6884736, by rfl⟩ : syracuseStep 18359297 = 13769473) B13769473
theorem B2205103 : Blo 868566 2205103 := bstep (se 1 (by rfl) ⟨1653827, by rfl⟩ : syracuseStep 2205103 = 3307655) B3307655
theorem B9905651 : Blo 868566 9905651 := bstep (se 1 (by rfl) ⟨7429238, by rfl⟩ : syracuseStep 9905651 = 14858477) B14858477
theorem B7054897 : Blo 868566 7054897 := bstep (se 2 (by rfl) ⟨2645586, by rfl⟩ : syracuseStep 7054897 = 5291173) B5291173
theorem B992935 : Blo 868566 992935 := bstep (se 1 (by rfl) ⟨744701, by rfl⟩ : syracuseStep 992935 = 1489403) B1489403
theorem B2205407 : Blo 868566 2205407 := bstep (se 1 (by rfl) ⟨1654055, by rfl⟩ : syracuseStep 2205407 = 3308111) B3308111
theorem B11151755 : Blo 868566 11151755 := bstep (se 1 (by rfl) ⟨8363816, by rfl⟩ : syracuseStep 11151755 = 16727633) B16727633
theorem B6269345 : Blo 868566 6269345 := bstep (se 2 (by rfl) ⟨2351004, by rfl⟩ : syracuseStep 6269345 = 4702009) B4702009
theorem B1321609 : Blo 868566 1321609 := bstep (se 2 (by rfl) ⟨495603, by rfl⟩ : syracuseStep 1321609 = 991207) B991207
theorem B2207159 : Blo 868566 2207159 := bstep (se 1 (by rfl) ⟨1655369, by rfl⟩ : syracuseStep 2207159 = 3310739) B3310739
theorem B1487035 : Blo 868566 1487035 := bstep (se 1 (by rfl) ⟨1115276, by rfl⟩ : syracuseStep 1487035 = 2230553) B2230553
theorem B3715577 : Blo 868566 3715577 := bstep (se 2 (by rfl) ⟨1393341, by rfl⟩ : syracuseStep 3715577 = 2786683) B2786683
theorem B5026319 : Blo 868566 5026319 := bstep (se 1 (by rfl) ⟨3769739, by rfl⟩ : syracuseStep 5026319 = 7539479) B7539479
theorem B7451351 : Blo 868566 7451351 := bstep (se 1 (by rfl) ⟨5588513, by rfl⟩ : syracuseStep 7451351 = 11177027) B11177027
theorem B6599879 : Blo 868566 6599879 := bstep (se 1 (by rfl) ⟨4949909, by rfl⟩ : syracuseStep 6599879 = 9899819) B9899819
theorem B12530963 : Blo 868566 12530963 := bstep (se 1 (by rfl) ⟨9398222, by rfl⟩ : syracuseStep 12530963 = 18796445) B18796445
theorem B4961735 : Blo 868566 4961735 := bstep (se 1 (by rfl) ⟨3721301, by rfl⟩ : syracuseStep 4961735 = 7442603) B7442603
theorem B10728941 : Blo 868566 10728941 := bstep (se 3 (by rfl) ⟨2011676, by rfl⟩ : syracuseStep 10728941 = 4023353) B4023353
theorem B12564179 : Blo 868566 12564179 := bstep (se 1 (by rfl) ⟨9423134, by rfl⟩ : syracuseStep 12564179 = 18846269) B18846269
theorem B3979145 : Blo 868566 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B1652719 : Blo 868566 1652719 := bstep (se 1 (by rfl) ⟨1239539, by rfl⟩ : syracuseStep 1652719 = 2479079) B2479079
theorem B25147493 : Blo 868566 25147493 := bstep (se 4 (by rfl) ⟨2357577, by rfl⟩ : syracuseStep 25147493 = 4715155) B4715155
theorem B1652879 : Blo 868566 1652879 := bstep (se 1 (by rfl) ⟨1239659, by rfl⟩ : syracuseStep 1652879 = 2479319) B2479319
theorem B3717353 : Blo 868566 3717353 := bstep (se 2 (by rfl) ⟨1394007, by rfl⟩ : syracuseStep 3717353 = 2788015) B2788015
theorem B4405913 : Blo 868566 4405913 := bstep (se 2 (by rfl) ⟨1652217, by rfl⟩ : syracuseStep 4405913 = 3304435) B3304435
theorem B16923599 : Blo 868566 16923599 := bstep (se 1 (by rfl) ⟨12692699, by rfl⟩ : syracuseStep 16923599 = 25385399) B25385399
theorem B5586077 : Blo 868566 5586077 := bstep (se 3 (by rfl) ⟨1047389, by rfl⟩ : syracuseStep 5586077 = 2094779) B2094779
theorem B4406723 : Blo 868566 4406723 := bstep (se 1 (by rfl) ⟨3305042, by rfl⟩ : syracuseStep 4406723 = 6610085) B6610085
theorem B26787287 : Blo 868566 26787287 := bstep (se 1 (by rfl) ⟨20090465, by rfl⟩ : syracuseStep 26787287 = 40180931) B40180931
theorem B2932199 : Blo 868566 2932199 := bstep (se 1 (by rfl) ⟨2199149, by rfl⟩ : syracuseStep 2932199 = 4398299) B4398299
theorem B10174061 : Blo 868566 10174061 := bstep (se 3 (by rfl) ⟨1907636, by rfl⟩ : syracuseStep 10174061 = 3815273) B3815273
theorem B20070433 : Blo 868566 20070433 := bstep (se 2 (by rfl) ⟨7526412, by rfl⟩ : syracuseStep 20070433 = 15052825) B15052825
theorem B18825331 : Blo 868566 18825331 := bstep (se 1 (by rfl) ⟨14118998, by rfl⟩ : syracuseStep 18825331 = 28237997) B28237997
theorem B2932955 : Blo 868566 2932955 := bstep (se 1 (by rfl) ⟨2199716, by rfl⟩ : syracuseStep 2932955 = 4399433) B4399433
theorem B868583 : Blo 868566 868583 := bstep (se 1 (by rfl) ⟨651437, by rfl⟩ : syracuseStep 868583 = 1302875) B1302875
theorem B868735 : Blo 868566 868735 := bstep (se 1 (by rfl) ⟨651551, by rfl⟩ : syracuseStep 868735 = 1303103) B1303103
theorem B868815 : Blo 868566 868815 := bstep (se 1 (by rfl) ⟨651611, by rfl⟩ : syracuseStep 868815 = 1303223) B1303223
theorem B2933225 : Blo 868566 2933225 := bstep (se 2 (by rfl) ⟨1099959, by rfl⟩ : syracuseStep 2933225 = 2199919) B2199919
theorem B868967 : Blo 868566 868967 := bstep (se 1 (by rfl) ⟨651725, by rfl⟩ : syracuseStep 868967 = 1303451) B1303451
theorem B2474671 : Blo 868566 2474671 := bstep (se 1 (by rfl) ⟨1856003, by rfl⟩ : syracuseStep 2474671 = 3712007) B3712007
theorem B869231 : Blo 868566 869231 := bstep (se 1 (by rfl) ⟨651923, by rfl⟩ : syracuseStep 869231 = 1303847) B1303847
theorem B869287 : Blo 868566 869287 := bstep (se 1 (by rfl) ⟨651965, by rfl⟩ : syracuseStep 869287 = 1303931) B1303931
theorem B869371 : Blo 868566 869371 := bstep (se 1 (by rfl) ⟨652028, by rfl⟩ : syracuseStep 869371 = 1304057) B1304057
theorem B2933819 : Blo 868566 2933819 := bstep (se 1 (by rfl) ⟨2200364, by rfl⟩ : syracuseStep 2933819 = 4400729) B4400729
theorem B5588027 : Blo 868566 5588027 := bstep (se 1 (by rfl) ⟨4191020, by rfl⟩ : syracuseStep 5588027 = 8382041) B8382041
theorem B869439 : Blo 868566 869439 := bstep (se 1 (by rfl) ⟨652079, by rfl⟩ : syracuseStep 869439 = 1304159) B1304159
theorem B869583 : Blo 868566 869583 := bstep (se 1 (by rfl) ⟨652187, by rfl⟩ : syracuseStep 869583 = 1304375) B1304375
theorem B2934089 : Blo 868566 2934089 := bstep (se 2 (by rfl) ⟨1100283, by rfl⟩ : syracuseStep 2934089 = 2200567) B2200567
theorem B869787 : Blo 868566 869787 := bstep (se 1 (by rfl) ⟨652340, by rfl⟩ : syracuseStep 869787 = 1304681) B1304681
theorem B4408829 : Blo 868566 4408829 := bstep (se 3 (by rfl) ⟨826655, by rfl⟩ : syracuseStep 4408829 = 1653311) B1653311
theorem B869999 : Blo 868566 869999 := bstep (se 1 (by rfl) ⟨652499, by rfl⟩ : syracuseStep 869999 = 1304999) B1304999
theorem B870055 : Blo 868566 870055 := bstep (se 1 (by rfl) ⟨652541, by rfl⟩ : syracuseStep 870055 = 1305083) B1305083
theorem B870139 : Blo 868566 870139 := bstep (se 1 (by rfl) ⟨652604, by rfl⟩ : syracuseStep 870139 = 1305209) B1305209
theorem B870175 : Blo 868566 870175 := bstep (se 1 (by rfl) ⟨652631, by rfl⟩ : syracuseStep 870175 = 1305263) B1305263
theorem B870207 : Blo 868566 870207 := bstep (se 1 (by rfl) ⟨652655, by rfl⟩ : syracuseStep 870207 = 1305311) B1305311
theorem B3524431 : Blo 868566 3524431 := bstep (se 1 (by rfl) ⟨2643323, by rfl⟩ : syracuseStep 3524431 = 5286647) B5286647
theorem B870383 : Blo 868566 870383 := bstep (se 1 (by rfl) ⟨652787, by rfl⟩ : syracuseStep 870383 = 1305575) B1305575
theorem B870555 : Blo 868566 870555 := bstep (se 1 (by rfl) ⟨652916, by rfl⟩ : syracuseStep 870555 = 1305833) B1305833
theorem B870591 : Blo 868566 870591 := bstep (se 1 (by rfl) ⟨652943, by rfl⟩ : syracuseStep 870591 = 1305887) B1305887
theorem B1394879 : Blo 868566 1394879 := bstep (se 1 (by rfl) ⟨1046159, by rfl⟩ : syracuseStep 1394879 = 2092319) B2092319
theorem B4180177 : Blo 868566 4180177 := bstep (se 2 (by rfl) ⟨1567566, by rfl⟩ : syracuseStep 4180177 = 3135133) B3135133
theorem B4409639 : Blo 868566 4409639 := bstep (se 1 (by rfl) ⟨3307229, by rfl⟩ : syracuseStep 4409639 = 6614459) B6614459
theorem B870703 : Blo 868566 870703 := bstep (se 1 (by rfl) ⟨653027, by rfl⟩ : syracuseStep 870703 = 1306055) B1306055
theorem B2476345 : Blo 868566 2476345 := bstep (se 2 (by rfl) ⟨928629, by rfl⟩ : syracuseStep 2476345 = 1857259) B1857259
theorem B4409801 : Blo 868566 4409801 := bstep (se 2 (by rfl) ⟨1653675, by rfl⟩ : syracuseStep 4409801 = 3307351) B3307351
theorem B870939 : Blo 868566 870939 := bstep (se 1 (by rfl) ⟨653204, by rfl⟩ : syracuseStep 870939 = 1306409) B1306409
theorem B870943 : Blo 868566 870943 := bstep (se 1 (by rfl) ⟨653207, by rfl⟩ : syracuseStep 870943 = 1306415) B1306415
theorem B5032595 : Blo 868566 5032595 := bstep (se 1 (by rfl) ⟨3774446, by rfl⟩ : syracuseStep 5032595 = 7548893) B7548893
theorem B871259 : Blo 868566 871259 := bstep (se 1 (by rfl) ⟨653444, by rfl⟩ : syracuseStep 871259 = 1306889) B1306889
theorem B871327 : Blo 868566 871327 := bstep (se 1 (by rfl) ⟨653495, by rfl⟩ : syracuseStep 871327 = 1306991) B1306991
theorem B871471 : Blo 868566 871471 := bstep (se 1 (by rfl) ⟨653603, by rfl⟩ : syracuseStep 871471 = 1307207) B1307207
theorem B871495 : Blo 868566 871495 := bstep (se 1 (by rfl) ⟨653621, by rfl⟩ : syracuseStep 871495 = 1307243) B1307243
theorem B2477279 : Blo 868566 2477279 := bstep (se 1 (by rfl) ⟨1857959, by rfl⟩ : syracuseStep 2477279 = 3715919) B3715919
theorem B871647 : Blo 868566 871647 := bstep (se 1 (by rfl) ⟨653735, by rfl⟩ : syracuseStep 871647 = 1307471) B1307471
theorem B4410611 : Blo 868566 4410611 := bstep (se 1 (by rfl) ⟨3307958, by rfl⟩ : syracuseStep 4410611 = 6615917) B6615917
theorem B871911 : Blo 868566 871911 := bstep (se 1 (by rfl) ⟨653933, by rfl⟩ : syracuseStep 871911 = 1307867) B1307867
theorem B4967999 : Blo 868566 4967999 := bstep (se 1 (by rfl) ⟨3725999, by rfl⟩ : syracuseStep 4967999 = 7451999) B7451999
theorem B872027 : Blo 868566 872027 := bstep (se 1 (by rfl) ⟨654020, by rfl⟩ : syracuseStep 872027 = 1308041) B1308041
theorem B872263 : Blo 868566 872263 := bstep (se 1 (by rfl) ⟨654197, by rfl⟩ : syracuseStep 872263 = 1308395) B1308395
theorem B2936681 : Blo 868566 2936681 := bstep (se 2 (by rfl) ⟨1101255, by rfl⟩ : syracuseStep 2936681 = 2202511) B2202511
theorem B1101691 : Blo 868566 1101691 := bstep (se 1 (by rfl) ⟨826268, by rfl⟩ : syracuseStep 1101691 = 1652537) B1652537
theorem B872415 : Blo 868566 872415 := bstep (se 1 (by rfl) ⟨654311, by rfl⟩ : syracuseStep 872415 = 1308623) B1308623
theorem B2642107 : Blo 868566 2642107 := bstep (se 1 (by rfl) ⟨1981580, by rfl⟩ : syracuseStep 2642107 = 3963161) B3963161
theorem B9392345 : Blo 868566 9392345 := bstep (se 2 (by rfl) ⟨3522129, by rfl⟩ : syracuseStep 9392345 = 7044259) B7044259
theorem B8147249 : Blo 868566 8147249 := bstep (se 2 (by rfl) ⟨3055218, by rfl⟩ : syracuseStep 8147249 = 6110437) B6110437
theorem B2642303 : Blo 868566 2642303 := bstep (se 1 (by rfl) ⟨1981727, by rfl⟩ : syracuseStep 2642303 = 3963455) B3963455
theorem B4182623 : Blo 868566 4182623 := bstep (se 1 (by rfl) ⟨3136967, by rfl⟩ : syracuseStep 4182623 = 6273935) B6273935
theorem B14897843 : Blo 868566 14897843 := bstep (se 1 (by rfl) ⟨11173382, by rfl⟩ : syracuseStep 14897843 = 22346765) B22346765
theorem B1954601 : Blo 868566 1954601 := bstep (se 2 (by rfl) ⟨732975, by rfl⟩ : syracuseStep 1954601 = 1465951) B1465951
theorem B3527675 : Blo 868566 3527675 := bstep (se 1 (by rfl) ⟨2645756, by rfl⟩ : syracuseStep 3527675 = 5291513) B5291513
theorem B1954871 : Blo 868566 1954871 := bstep (se 1 (by rfl) ⟨1466153, by rfl⟩ : syracuseStep 1954871 = 2932307) B2932307
theorem B1954889 : Blo 868566 1954889 := bstep (se 2 (by rfl) ⟨733083, by rfl⟩ : syracuseStep 1954889 = 1466167) B1466167
theorem B6706253 : Blo 868566 6706253 := bstep (se 3 (by rfl) ⟨1257422, by rfl⟩ : syracuseStep 6706253 = 2514845) B2514845
theorem B2938031 : Blo 868566 2938031 := bstep (se 1 (by rfl) ⟨2203523, by rfl⟩ : syracuseStep 2938031 = 4407047) B4407047
theorem B8377577 : Blo 868566 8377577 := bstep (se 2 (by rfl) ⟨3141591, by rfl⟩ : syracuseStep 8377577 = 6283183) B6283183
theorem B6280877 : Blo 868566 6280877 := bstep (se 3 (by rfl) ⟨1177664, by rfl⟩ : syracuseStep 6280877 = 2355329) B2355329
theorem B15849431 : Blo 868566 15849431 := bstep (se 1 (by rfl) ⟨11887073, by rfl⟩ : syracuseStep 15849431 = 23774147) B23774147
theorem B2480777 : Blo 868566 2480777 := bstep (se 2 (by rfl) ⟨930291, by rfl⟩ : syracuseStep 2480777 = 1860583) B1860583
theorem B12704617 : Blo 868566 12704617 := bstep (se 2 (by rfl) ⟨4764231, by rfl⟩ : syracuseStep 12704617 = 9528463) B9528463
theorem B163371919 : Blo 868566 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B1956815 : Blo 868566 1956815 := bstep (se 1 (by rfl) ⟨1467611, by rfl⟩ : syracuseStep 1956815 = 2935223) B2935223
theorem B1956833 : Blo 868566 1956833 := bstep (se 2 (by rfl) ⟨733812, by rfl⟩ : syracuseStep 1956833 = 1467625) B1467625
theorem B1956905 : Blo 868566 1956905 := bstep (se 2 (by rfl) ⟨733839, by rfl⟩ : syracuseStep 1956905 = 1467679) B1467679
theorem B1858601 : Blo 868566 1858601 := bstep (se 2 (by rfl) ⟨696975, by rfl⟩ : syracuseStep 1858601 = 1393951) B1393951
theorem B2939975 : Blo 868566 2939975 := bstep (se 1 (by rfl) ⟨2204981, by rfl⟩ : syracuseStep 2939975 = 4409963) B4409963
theorem B2940029 : Blo 868566 2940029 := bstep (se 3 (by rfl) ⟨551255, by rfl⟩ : syracuseStep 2940029 = 1102511) B1102511
theorem B2940299 : Blo 868566 2940299 := bstep (se 1 (by rfl) ⟨2205224, by rfl⟩ : syracuseStep 2940299 = 4410449) B4410449
theorem B1465769 : Blo 868566 1465769 := bstep (se 2 (by rfl) ⟨549663, by rfl⟩ : syracuseStep 1465769 = 1099327) B1099327
theorem B2645747 : Blo 868566 2645747 := bstep (se 1 (by rfl) ⟨1984310, by rfl⟩ : syracuseStep 2645747 = 3968621) B3968621
theorem B2482109 : Blo 868566 2482109 := bstep (se 3 (by rfl) ⟨465395, by rfl⟩ : syracuseStep 2482109 = 930791) B930791
theorem B529915877 : Blo 868566 529915877 := bstep (se 4 (by rfl) ⟨49679613, by rfl⟩ : syracuseStep 529915877 = 99359227) B99359227
theorem B3825883 : Blo 868566 3825883 := bstep (se 1 (by rfl) ⟨2869412, by rfl⟩ : syracuseStep 3825883 = 5738825) B5738825
theorem B1466599 : Blo 868566 1466599 := bstep (se 1 (by rfl) ⟨1099949, by rfl⟩ : syracuseStep 1466599 = 2199899) B2199899
theorem B1302911 : Blo 868566 1302911 := bstep (se 1 (by rfl) ⟨977183, by rfl⟩ : syracuseStep 1302911 = 1954367) B1954367
theorem B1466761 : Blo 868566 1466761 := bstep (se 2 (by rfl) ⟨550035, by rfl⟩ : syracuseStep 1466761 = 1100071) B1100071
theorem B1302983 : Blo 868566 1302983 := bstep (se 1 (by rfl) ⟨977237, by rfl⟩ : syracuseStep 1302983 = 1954475) B1954475
theorem B28271213 : Blo 868566 28271213 := bstep (se 3 (by rfl) ⟨5300852, by rfl⟩ : syracuseStep 28271213 = 10601705) B10601705
theorem B1303337 : Blo 868566 1303337 := bstep (se 2 (by rfl) ⟨488751, by rfl⟩ : syracuseStep 1303337 = 977503) B977503
theorem B1303343 : Blo 868566 1303343 := bstep (se 1 (by rfl) ⟨977507, by rfl⟩ : syracuseStep 1303343 = 1955015) B1955015
theorem B1467193 : Blo 868566 1467193 := bstep (se 2 (by rfl) ⟨550197, by rfl⟩ : syracuseStep 1467193 = 1100395) B1100395
theorem B1467247 : Blo 868566 1467247 := bstep (se 1 (by rfl) ⟨1100435, by rfl⟩ : syracuseStep 1467247 = 2200871) B2200871
theorem B1303463 : Blo 868566 1303463 := bstep (se 1 (by rfl) ⟨977597, by rfl⟩ : syracuseStep 1303463 = 1955195) B1955195
theorem B2483111 : Blo 868566 2483111 := bstep (se 1 (by rfl) ⟨1862333, by rfl⟩ : syracuseStep 2483111 = 3724667) B3724667
theorem B1958867 : Blo 868566 1958867 := bstep (se 1 (by rfl) ⟨1469150, by rfl⟩ : syracuseStep 1958867 = 2938301) B2938301
theorem B1303547 : Blo 868566 1303547 := bstep (se 1 (by rfl) ⟨977660, by rfl⟩ : syracuseStep 1303547 = 1955321) B1955321
theorem B1303607 : Blo 868566 1303607 := bstep (se 1 (by rfl) ⟨977705, by rfl⟩ : syracuseStep 1303607 = 1955411) B1955411
theorem B1467497 : Blo 868566 1467497 := bstep (se 2 (by rfl) ⟨550311, by rfl⟩ : syracuseStep 1467497 = 1100623) B1100623
theorem B6710435 : Blo 868566 6710435 := bstep (se 1 (by rfl) ⟨5032826, by rfl⟩ : syracuseStep 6710435 = 10065653) B10065653
theorem B1303727 : Blo 868566 1303727 := bstep (se 1 (by rfl) ⟨977795, by rfl⟩ : syracuseStep 1303727 = 1955591) B1955591
theorem B1959119 : Blo 868566 1959119 := bstep (se 1 (by rfl) ⟨1469339, by rfl⟩ : syracuseStep 1959119 = 2938679) B2938679
theorem B3138767 : Blo 868566 3138767 := bstep (se 1 (by rfl) ⟨2354075, by rfl⟩ : syracuseStep 3138767 = 4708151) B4708151
theorem B5301611 : Blo 868566 5301611 := bstep (se 1 (by rfl) ⟨3976208, by rfl⟩ : syracuseStep 5301611 = 7952417) B7952417
theorem B96429491 : Blo 868566 96429491 := bstep (se 1 (by rfl) ⟨72322118, by rfl⟩ : syracuseStep 96429491 = 144644237) B144644237
theorem B1959443 : Blo 868566 1959443 := bstep (se 1 (by rfl) ⟨1469582, by rfl⟩ : syracuseStep 1959443 = 2939165) B2939165
theorem B1304135 : Blo 868566 1304135 := bstep (se 1 (by rfl) ⟨978101, by rfl⟩ : syracuseStep 1304135 = 1956203) B1956203
theorem B5301881 : Blo 868566 5301881 := bstep (se 2 (by rfl) ⟨1988205, by rfl⟩ : syracuseStep 5301881 = 3976411) B3976411
theorem B1304231 : Blo 868566 1304231 := bstep (se 1 (by rfl) ⟨978173, by rfl⟩ : syracuseStep 1304231 = 1956347) B1956347
theorem B1304315 : Blo 868566 1304315 := bstep (se 1 (by rfl) ⟨978236, by rfl⟩ : syracuseStep 1304315 = 1956473) B1956473
theorem B1304351 : Blo 868566 1304351 := bstep (se 1 (by rfl) ⟨978263, by rfl⟩ : syracuseStep 1304351 = 1956527) B1956527
theorem B1304399 : Blo 868566 1304399 := bstep (se 1 (by rfl) ⟨978299, by rfl⟩ : syracuseStep 1304399 = 1956599) B1956599
theorem B1304519 : Blo 868566 1304519 := bstep (se 1 (by rfl) ⟨978389, by rfl⟩ : syracuseStep 1304519 = 1956779) B1956779
theorem B4778003 : Blo 868566 4778003 := bstep (se 1 (by rfl) ⟨3583502, by rfl⟩ : syracuseStep 4778003 = 7167005) B7167005
theorem B2648189 : Blo 868566 2648189 := bstep (se 3 (by rfl) ⟨496535, by rfl⟩ : syracuseStep 2648189 = 993071) B993071
theorem B1566875 : Blo 868566 1566875 := bstep (se 1 (by rfl) ⟨1175156, by rfl⟩ : syracuseStep 1566875 = 2350313) B2350313
theorem B1960127 : Blo 868566 1960127 := bstep (se 1 (by rfl) ⟨1470095, by rfl⟩ : syracuseStep 1960127 = 2940191) B2940191
theorem B1468651 : Blo 868566 1468651 := bstep (se 1 (by rfl) ⟨1101488, by rfl⟩ : syracuseStep 1468651 = 2202977) B2202977
theorem B1304873 : Blo 868566 1304873 := bstep (se 2 (by rfl) ⟨489327, by rfl⟩ : syracuseStep 1304873 = 978655) B978655
theorem B1304879 : Blo 868566 1304879 := bstep (se 1 (by rfl) ⟨978659, by rfl⟩ : syracuseStep 1304879 = 1957319) B1957319
theorem B3303737 : Blo 868566 3303737 := bstep (se 2 (by rfl) ⟨1238901, by rfl⟩ : syracuseStep 3303737 = 2477803) B2477803
theorem B2943323 : Blo 868566 2943323 := bstep (se 1 (by rfl) ⟨2207492, by rfl⟩ : syracuseStep 2943323 = 4414985) B4414985
theorem B1468955 : Blo 868566 1468955 := bstep (se 1 (by rfl) ⟨1101716, by rfl⟩ : syracuseStep 1468955 = 2203433) B2203433
theorem B1305119 : Blo 868566 1305119 := bstep (se 1 (by rfl) ⟨978839, by rfl⟩ : syracuseStep 1305119 = 1957679) B1957679
theorem B2943593 : Blo 868566 2943593 := bstep (se 2 (by rfl) ⟨1103847, by rfl⟩ : syracuseStep 2943593 = 2207695) B2207695
theorem B977755 : Blo 868566 977755 := bstep (se 1 (by rfl) ⟨733316, by rfl⟩ : syracuseStep 977755 = 1466633) B1466633
theorem B1305503 : Blo 868566 1305503 := bstep (se 1 (by rfl) ⟨979127, by rfl⟩ : syracuseStep 1305503 = 1958255) B1958255
theorem B1305551 : Blo 868566 1305551 := bstep (se 1 (by rfl) ⟨979163, by rfl⟩ : syracuseStep 1305551 = 1958327) B1958327
theorem B1305641 : Blo 868566 1305641 := bstep (se 2 (by rfl) ⟨489615, by rfl⟩ : syracuseStep 1305641 = 979231) B979231
theorem B1305647 : Blo 868566 1305647 := bstep (se 1 (by rfl) ⟨979235, by rfl⟩ : syracuseStep 1305647 = 1958471) B1958471
theorem B1305671 : Blo 868566 1305671 := bstep (se 1 (by rfl) ⟨979253, by rfl⟩ : syracuseStep 1305671 = 1958507) B1958507
theorem B1961081 : Blo 868566 1961081 := bstep (se 2 (by rfl) ⟨735405, by rfl⟩ : syracuseStep 1961081 = 1470811) B1470811
theorem B1469623 : Blo 868566 1469623 := bstep (se 1 (by rfl) ⟨1102217, by rfl⟩ : syracuseStep 1469623 = 2204435) B2204435
theorem B1305935 : Blo 868566 1305935 := bstep (se 1 (by rfl) ⟨979451, by rfl⟩ : syracuseStep 1305935 = 1958903) B1958903
theorem B1306025 : Blo 868566 1306025 := bstep (se 2 (by rfl) ⟨489759, by rfl⟩ : syracuseStep 1306025 = 979519) B979519
theorem B1568231 : Blo 868566 1568231 := bstep (se 1 (by rfl) ⟨1176173, by rfl⟩ : syracuseStep 1568231 = 2352347) B2352347
theorem B1469927 : Blo 868566 1469927 := bstep (se 1 (by rfl) ⟨1102445, by rfl⟩ : syracuseStep 1469927 = 2204891) B2204891
theorem B1469947 : Blo 868566 1469947 := bstep (se 1 (by rfl) ⟨1102460, by rfl⟩ : syracuseStep 1469947 = 2204921) B2204921
theorem B1306175 : Blo 868566 1306175 := bstep (se 1 (by rfl) ⟨979631, by rfl⟩ : syracuseStep 1306175 = 1959263) B1959263
theorem B2944619 : Blo 868566 2944619 := bstep (se 1 (by rfl) ⟨2208464, by rfl⟩ : syracuseStep 2944619 = 4416929) B4416929
theorem B2092819 : Blo 868566 2092819 := bstep (se 1 (by rfl) ⟨1569614, by rfl⟩ : syracuseStep 2092819 = 3139229) B3139229
theorem B1961747 : Blo 868566 1961747 := bstep (se 1 (by rfl) ⟨1471310, by rfl⟩ : syracuseStep 1961747 = 2942621) B2942621
theorem B978727 : Blo 868566 978727 := bstep (se 1 (by rfl) ⟨734045, by rfl⟩ : syracuseStep 978727 = 1468091) B1468091
theorem B47705921 : Blo 868566 47705921 := bstep (se 2 (by rfl) ⟨17889720, by rfl⟩ : syracuseStep 47705921 = 35779441) B35779441
theorem B1306439 : Blo 868566 1306439 := bstep (se 1 (by rfl) ⟨979829, by rfl⟩ : syracuseStep 1306439 = 1959659) B1959659
theorem B9400171 : Blo 868566 9400171 := bstep (se 1 (by rfl) ⟨7050128, by rfl⟩ : syracuseStep 9400171 = 14100257) B14100257
theorem B2944889 : Blo 868566 2944889 := bstep (se 2 (by rfl) ⟨1104333, by rfl⟩ : syracuseStep 2944889 = 2208667) B2208667
theorem B2977679 : Blo 868566 2977679 := bstep (se 1 (by rfl) ⟨2233259, by rfl⟩ : syracuseStep 2977679 = 4466519) B4466519
theorem B1306523 : Blo 868566 1306523 := bstep (se 1 (by rfl) ⟨979892, by rfl⟩ : syracuseStep 1306523 = 1959785) B1959785
theorem B1470379 : Blo 868566 1470379 := bstep (se 1 (by rfl) ⟨1102784, by rfl⟩ : syracuseStep 1470379 = 2205569) B2205569
theorem B1962107 : Blo 868566 1962107 := bstep (se 1 (by rfl) ⟨1471580, by rfl⟩ : syracuseStep 1962107 = 2943161) B2943161
theorem B4714685 : Blo 868566 4714685 := bstep (se 3 (by rfl) ⟨884003, by rfl⟩ : syracuseStep 4714685 = 1768007) B1768007
theorem B1470683 : Blo 868566 1470683 := bstep (se 1 (by rfl) ⟨1103012, by rfl⟩ : syracuseStep 1470683 = 2206025) B2206025
theorem B1962377 : Blo 868566 1962377 := bstep (se 2 (by rfl) ⟨735891, by rfl⟩ : syracuseStep 1962377 = 1471783) B1471783
theorem B4518287 : Blo 868566 4518287 := bstep (se 1 (by rfl) ⟨3388715, by rfl⟩ : syracuseStep 4518287 = 6777431) B6777431
theorem B1470919 : Blo 868566 1470919 := bstep (se 1 (by rfl) ⟨1103189, by rfl⟩ : syracuseStep 1470919 = 2206379) B2206379
theorem B1307087 : Blo 868566 1307087 := bstep (se 1 (by rfl) ⟨980315, by rfl⟩ : syracuseStep 1307087 = 1960631) B1960631
theorem B1470953 : Blo 868566 1470953 := bstep (se 2 (by rfl) ⟨551607, by rfl⟩ : syracuseStep 1470953 = 1103215) B1103215
theorem B1307129 : Blo 868566 1307129 := bstep (se 2 (by rfl) ⟨490173, by rfl⟩ : syracuseStep 1307129 = 980347) B980347
theorem B1307231 : Blo 868566 1307231 := bstep (se 1 (by rfl) ⟨980423, by rfl⟩ : syracuseStep 1307231 = 1960847) B1960847
theorem B1241897 : Blo 868566 1241897 := bstep (se 2 (by rfl) ⟨465711, by rfl⟩ : syracuseStep 1241897 = 931423) B931423
theorem B3306365 : Blo 868566 3306365 := bstep (se 3 (by rfl) ⟨619943, by rfl⟩ : syracuseStep 3306365 = 1239887) B1239887
theorem B979879 : Blo 868566 979879 := bstep (se 1 (by rfl) ⟨734909, by rfl⟩ : syracuseStep 979879 = 1469819) B1469819
theorem B1307711 : Blo 868566 1307711 := bstep (se 1 (by rfl) ⟨980783, by rfl⟩ : syracuseStep 1307711 = 1961567) B1961567
theorem B1307753 : Blo 868566 1307753 := bstep (se 2 (by rfl) ⟨490407, by rfl⟩ : syracuseStep 1307753 = 980815) B980815
theorem B1963115 : Blo 868566 1963115 := bstep (se 1 (by rfl) ⟨1472336, by rfl⟩ : syracuseStep 1963115 = 2944673) B2944673
theorem B18805877 : Blo 868566 18805877 := bstep (se 5 (by rfl) ⟨881525, by rfl⟩ : syracuseStep 18805877 = 1763051) B1763051
theorem B1307855 : Blo 868566 1307855 := bstep (se 1 (by rfl) ⟨980891, by rfl⟩ : syracuseStep 1307855 = 1961783) B1961783
theorem B1242319 : Blo 868566 1242319 := bstep (se 1 (by rfl) ⟨931739, by rfl⟩ : syracuseStep 1242319 = 1863479) B1863479
theorem B11924729 : Blo 868566 11924729 := bstep (se 2 (by rfl) ⟨4471773, by rfl⟩ : syracuseStep 11924729 = 8943547) B8943547
theorem B2782583 : Blo 868566 2782583 := bstep (se 1 (by rfl) ⟨2086937, by rfl⟩ : syracuseStep 2782583 = 4173875) B4173875
theorem B1308059 : Blo 868566 1308059 := bstep (se 1 (by rfl) ⟨981044, by rfl⟩ : syracuseStep 1308059 = 1962089) B1962089
theorem B1308281 : Blo 868566 1308281 := bstep (se 2 (by rfl) ⟨490605, by rfl⟩ : syracuseStep 1308281 = 981211) B981211
theorem B7141067 : Blo 868566 7141067 := bstep (se 1 (by rfl) ⟨5355800, by rfl⟩ : syracuseStep 7141067 = 10711601) B10711601
theorem B1308383 : Blo 868566 1308383 := bstep (se 1 (by rfl) ⟨981287, by rfl⟩ : syracuseStep 1308383 = 1962575) B1962575
theorem B1308479 : Blo 868566 1308479 := bstep (se 1 (by rfl) ⟨981359, by rfl⟩ : syracuseStep 1308479 = 1962719) B1962719
theorem B1308647 : Blo 868566 1308647 := bstep (se 1 (by rfl) ⟨981485, by rfl⟩ : syracuseStep 1308647 = 1962971) B1962971
theorem B2095087 : Blo 868566 2095087 := bstep (se 1 (by rfl) ⟨1571315, by rfl⟩ : syracuseStep 2095087 = 3142631) B3142631
theorem B1308665 : Blo 868566 1308665 := bstep (se 2 (by rfl) ⟨490749, by rfl⟩ : syracuseStep 1308665 = 981499) B981499
theorem B1308767 : Blo 868566 1308767 := bstep (se 1 (by rfl) ⟨981575, by rfl⟩ : syracuseStep 1308767 = 1963151) B1963151
theorem B3307625 : Blo 868566 3307625 := bstep (se 2 (by rfl) ⟨1240359, by rfl⟩ : syracuseStep 3307625 = 2480719) B2480719
theorem B1308827 : Blo 868566 1308827 := bstep (se 1 (by rfl) ⟨981620, by rfl⟩ : syracuseStep 1308827 = 1963241) B1963241
theorem B1177903 : Blo 868566 1177903 := bstep (se 1 (by rfl) ⟨883427, by rfl⟩ : syracuseStep 1177903 = 1766855) B1766855
theorem B981535 : Blo 868566 981535 := bstep (se 1 (by rfl) ⟨736151, by rfl⟩ : syracuseStep 981535 = 1472303) B1472303
theorem B2783801 : Blo 868566 2783801 := bstep (se 2 (by rfl) ⟨1043925, by rfl⟩ : syracuseStep 2783801 = 2087851) B2087851
theorem B11172563 : Blo 868566 11172563 := bstep (se 1 (by rfl) ⟨8379422, by rfl⟩ : syracuseStep 11172563 = 16758845) B16758845
theorem B1572023 : Blo 868566 1572023 := bstep (se 1 (by rfl) ⟨1179017, by rfl⟩ : syracuseStep 1572023 = 2358035) B2358035
theorem B2981129 : Blo 868566 2981129 := bstep (se 2 (by rfl) ⟨1117923, by rfl⟩ : syracuseStep 2981129 = 2235847) B2235847
theorem B3308809 : Blo 868566 3308809 := bstep (se 2 (by rfl) ⟨1240803, by rfl⟩ : syracuseStep 3308809 = 2481607) B2481607
theorem B1179049 : Blo 868566 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B1572347 : Blo 868566 1572347 := bstep (se 1 (by rfl) ⟨1179260, by rfl⟩ : syracuseStep 1572347 = 2358521) B2358521
theorem B3309281 : Blo 868566 3309281 := bstep (se 2 (by rfl) ⟨1240980, by rfl⟩ : syracuseStep 3309281 = 2481961) B2481961
theorem B37715705 : Blo 868566 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B25100441 : Blo 868566 25100441 := bstep (se 2 (by rfl) ⟨9412665, by rfl⟩ : syracuseStep 25100441 = 18825331) B18825331
theorem B9896903 : Blo 868566 9896903 := bstep (se 1 (by rfl) ⟨7422677, by rfl⟩ : syracuseStep 9896903 = 14845355) B14845355
theorem B9406529 : Blo 868566 9406529 := bstep (se 2 (by rfl) ⟨3527448, by rfl⟩ : syracuseStep 9406529 = 7054897) B7054897
theorem B3311725 : Blo 868566 3311725 := bstep (se 3 (by rfl) ⟨620948, by rfl⟩ : syracuseStep 3311725 = 1241897) B1241897
theorem B3311999 : Blo 868566 3311999 := bstep (se 1 (by rfl) ⟨2483999, by rfl⟩ : syracuseStep 3311999 = 4967999) B4967999
theorem B7932599 : Blo 868566 7932599 := bstep (se 1 (by rfl) ⟨5949449, by rfl⟩ : syracuseStep 7932599 = 11898899) B11898899
theorem B120720145 : Blo 868566 120720145 := bstep (se 2 (by rfl) ⟨45270054, by rfl⟩ : syracuseStep 120720145 = 90540109) B90540109
theorem B6261563 : Blo 868566 6261563 := bstep (se 1 (by rfl) ⟨4696172, by rfl⟩ : syracuseStep 6261563 = 9392345) B9392345
theorem B2788415 : Blo 868566 2788415 := bstep (se 1 (by rfl) ⟨2091311, by rfl⟩ : syracuseStep 2788415 = 4182623) B4182623
theorem B9931895 : Blo 868566 9931895 := bstep (se 1 (by rfl) ⟨7448921, by rfl⟩ : syracuseStep 9931895 = 14897843) B14897843
theorem B28249411 : Blo 868566 28249411 := bstep (se 1 (by rfl) ⟨21187058, by rfl⟩ : syracuseStep 28249411 = 42374117) B42374117
theorem B2231783 : Blo 868566 2231783 := bstep (se 1 (by rfl) ⟨1673837, by rfl⟩ : syracuseStep 2231783 = 3347675) B3347675
theorem B2790425 : Blo 868566 2790425 := bstep (se 2 (by rfl) ⟨1046409, by rfl⟩ : syracuseStep 2790425 = 2092819) B2092819
theorem B353277251 : Blo 868566 353277251 := bstep (se 1 (by rfl) ⟨264957938, by rfl⟩ : syracuseStep 353277251 = 529915877) B529915877
theorem B18847475 : Blo 868566 18847475 := bstep (se 1 (by rfl) ⟨14135606, by rfl⟩ : syracuseStep 18847475 = 28271213) B28271213
theorem B3185335 : Blo 868566 3185335 := bstep (se 1 (by rfl) ⟨2389001, by rfl⟩ : syracuseStep 3185335 = 4778003) B4778003
theorem B2202491 : Blo 868566 2202491 := bstep (se 1 (by rfl) ⟨1651868, by rfl⟩ : syracuseStep 2202491 = 3303737) B3303737
theorem B2203625 : Blo 868566 2203625 := bstep (se 2 (by rfl) ⟨826359, by rfl⟩ : syracuseStep 2203625 = 1652719) B1652719
theorem B2793449 : Blo 868566 2793449 := bstep (se 2 (by rfl) ⟨1047543, by rfl⟩ : syracuseStep 2793449 = 2095087) B2095087
theorem B3350879 : Blo 868566 3350879 := bstep (se 1 (by rfl) ⟨2513159, by rfl⟩ : syracuseStep 3350879 = 5026319) B5026319
theorem B2204243 : Blo 868566 2204243 := bstep (se 1 (by rfl) ⟨1653182, by rfl⟩ : syracuseStep 2204243 = 3306365) B3306365
theorem B4399919 : Blo 868566 4399919 := bstep (se 1 (by rfl) ⟨3299939, by rfl⟩ : syracuseStep 4399919 = 6599879) B6599879
theorem B4760711 : Blo 868566 4760711 := bstep (se 1 (by rfl) ⟨3570533, by rfl⟩ : syracuseStep 4760711 = 7141067) B7141067
theorem B2205083 : Blo 868566 2205083 := bstep (se 1 (by rfl) ⟨1653812, by rfl⟩ : syracuseStep 2205083 = 3307625) B3307625
theorem B7448375 : Blo 868566 7448375 := bstep (se 1 (by rfl) ⟨5586281, by rfl⟩ : syracuseStep 7448375 = 11172563) B11172563
theorem B11282399 : Blo 868566 11282399 := bstep (se 1 (by rfl) ⟨8461799, by rfl⟩ : syracuseStep 11282399 = 16923599) B16923599
theorem B2206187 : Blo 868566 2206187 := bstep (se 1 (by rfl) ⟨1654640, by rfl⟩ : syracuseStep 2206187 = 3309281) B3309281
theorem B25143803 : Blo 868566 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B15904019 : Blo 868566 15904019 := bstep (se 1 (by rfl) ⟨11928014, by rfl⟩ : syracuseStep 15904019 = 23856029) B23856029
theorem B7056719 : Blo 868566 7056719 := bstep (se 1 (by rfl) ⟨5292539, by rfl⟩ : syracuseStep 7056719 = 10585079) B10585079
theorem B22294277 : Blo 868566 22294277 := bstep (se 4 (by rfl) ⟨2090088, by rfl⟩ : syracuseStep 22294277 = 4180177) B4180177
theorem B4829053 : Blo 868566 4829053 := bstep (se 3 (by rfl) ⟨905447, by rfl⟩ : syracuseStep 4829053 = 1810895) B1810895
theorem B3715303 : Blo 868566 3715303 := bstep (se 1 (by rfl) ⟨2786477, by rfl⟩ : syracuseStep 3715303 = 5572955) B5572955
theorem B2208019 : Blo 868566 2208019 := bstep (se 1 (by rfl) ⟨1656014, by rfl⟩ : syracuseStep 2208019 = 3312029) B3312029
theorem B3355063 : Blo 868566 3355063 := bstep (se 1 (by rfl) ⟨2516297, by rfl⟩ : syracuseStep 3355063 = 5032595) B5032595
theorem B1651519 : Blo 868566 1651519 := bstep (se 1 (by rfl) ⟨1238639, by rfl⟩ : syracuseStep 1651519 = 2477279) B2477279
theorem B1323913 : Blo 868566 1323913 := bstep (se 2 (by rfl) ⟨496467, by rfl⟩ : syracuseStep 1323913 = 992935) B992935
theorem B4699241 : Blo 868566 4699241 := bstep (se 2 (by rfl) ⟨1762215, by rfl⟩ : syracuseStep 4699241 = 3524431) B3524431
theorem B5585051 : Blo 868566 5585051 := bstep (se 1 (by rfl) ⟨4188788, by rfl⟩ : syracuseStep 5585051 = 8377577) B8377577
theorem B10566287 : Blo 868566 10566287 := bstep (se 1 (by rfl) ⟨7924715, by rfl⟩ : syracuseStep 10566287 = 15849431) B15849431
theorem B1653851 : Blo 868566 1653851 := bstep (se 1 (by rfl) ⟨1240388, by rfl⟩ : syracuseStep 1653851 = 2480777) B2480777
theorem B2932091 : Blo 868566 2932091 := bstep (se 1 (by rfl) ⟨2199068, by rfl⟩ : syracuseStep 2932091 = 4398137) B4398137
theorem B1490347 : Blo 868566 1490347 := bstep (se 1 (by rfl) ⟨1117760, by rfl⟩ : syracuseStep 1490347 = 2235521) B2235521
theorem B114442037 : Blo 868566 114442037 := bstep (se 5 (by rfl) ⟨5364470, by rfl⟩ : syracuseStep 114442037 = 10728941) B10728941
theorem B12533561 : Blo 868566 12533561 := bstep (se 2 (by rfl) ⟨4700085, by rfl⟩ : syracuseStep 12533561 = 9400171) B9400171
theorem B4472765 : Blo 868566 4472765 := bstep (se 3 (by rfl) ⟨838643, by rfl⟩ : syracuseStep 4472765 = 1677287) B1677287
theorem B1654739 : Blo 868566 1654739 := bstep (se 1 (by rfl) ⟨1241054, by rfl⟩ : syracuseStep 1654739 = 2482109) B2482109
theorem B3522809 : Blo 868566 3522809 := bstep (se 2 (by rfl) ⟨1321053, by rfl⟩ : syracuseStep 3522809 = 2642107) B2642107
theorem B1982713 : Blo 868566 1982713 := bstep (se 2 (by rfl) ⟨743517, by rfl⟩ : syracuseStep 1982713 = 1487035) B1487035
theorem B868607 : Blo 868566 868607 := bstep (se 1 (by rfl) ⟨651455, by rfl⟩ : syracuseStep 868607 = 1302911) B1302911
theorem B868655 : Blo 868566 868655 := bstep (se 1 (by rfl) ⟨651491, by rfl⟩ : syracuseStep 868655 = 1302983) B1302983
theorem B18792809 : Blo 868566 18792809 := bstep (se 2 (by rfl) ⟨7047303, by rfl⟩ : syracuseStep 18792809 = 14094607) B14094607
theorem B3719677 : Blo 868566 3719677 := bstep (se 3 (by rfl) ⟨697439, by rfl⟩ : syracuseStep 3719677 = 1394879) B1394879
theorem B868891 : Blo 868566 868891 := bstep (se 1 (by rfl) ⟨651668, by rfl⟩ : syracuseStep 868891 = 1303337) B1303337
theorem B868895 : Blo 868566 868895 := bstep (se 1 (by rfl) ⟨651671, by rfl⟩ : syracuseStep 868895 = 1303343) B1303343
theorem B9912941 : Blo 868566 9912941 := bstep (se 3 (by rfl) ⟨1858676, by rfl⟩ : syracuseStep 9912941 = 3717353) B3717353
theorem B868975 : Blo 868566 868975 := bstep (se 1 (by rfl) ⟨651731, by rfl⟩ : syracuseStep 868975 = 1303463) B1303463
theorem B1655407 : Blo 868566 1655407 := bstep (se 1 (by rfl) ⟨1241555, by rfl⟩ : syracuseStep 1655407 = 2483111) B2483111
theorem B8929925 : Blo 868566 8929925 := bstep (se 4 (by rfl) ⟨837180, by rfl⟩ : syracuseStep 8929925 = 1674361) B1674361
theorem B1884833 : Blo 868566 1884833 := bstep (se 2 (by rfl) ⟨706812, by rfl⟩ : syracuseStep 1884833 = 1413625) B1413625
theorem B869031 : Blo 868566 869031 := bstep (se 1 (by rfl) ⟨651773, by rfl⟩ : syracuseStep 869031 = 1303547) B1303547
theorem B12239531 : Blo 868566 12239531 := bstep (se 1 (by rfl) ⟨9179648, by rfl⟩ : syracuseStep 12239531 = 18359297) B18359297
theorem B869071 : Blo 868566 869071 := bstep (se 1 (by rfl) ⟨651803, by rfl⟩ : syracuseStep 869071 = 1303607) B1303607
theorem B4473623 : Blo 868566 4473623 := bstep (se 1 (by rfl) ⟨3355217, by rfl⟩ : syracuseStep 4473623 = 6710435) B6710435
theorem B869151 : Blo 868566 869151 := bstep (se 1 (by rfl) ⟨651863, by rfl⟩ : syracuseStep 869151 = 1303727) B1303727
theorem B6603767 : Blo 868566 6603767 := bstep (se 1 (by rfl) ⟨4952825, by rfl⟩ : syracuseStep 6603767 = 9905651) B9905651
theorem B869423 : Blo 868566 869423 := bstep (se 1 (by rfl) ⟨652067, by rfl⟩ : syracuseStep 869423 = 1304135) B1304135
theorem B869487 : Blo 868566 869487 := bstep (se 1 (by rfl) ⟨652115, by rfl⟩ : syracuseStep 869487 = 1304231) B1304231
theorem B869543 : Blo 868566 869543 := bstep (se 1 (by rfl) ⟨652157, by rfl⟩ : syracuseStep 869543 = 1304315) B1304315
theorem B869567 : Blo 868566 869567 := bstep (se 1 (by rfl) ⟨652175, by rfl⟩ : syracuseStep 869567 = 1304351) B1304351
theorem B869599 : Blo 868566 869599 := bstep (se 1 (by rfl) ⟨652199, by rfl⟩ : syracuseStep 869599 = 1304399) B1304399
theorem B869679 : Blo 868566 869679 := bstep (se 1 (by rfl) ⟨652259, by rfl⟩ : syracuseStep 869679 = 1304519) B1304519
theorem B869915 : Blo 868566 869915 := bstep (se 1 (by rfl) ⟨652436, by rfl⟩ : syracuseStep 869915 = 1304873) B1304873
theorem B869919 : Blo 868566 869919 := bstep (se 1 (by rfl) ⟨652439, by rfl⟩ : syracuseStep 869919 = 1304879) B1304879
theorem B1656425 : Blo 868566 1656425 := bstep (se 2 (by rfl) ⟨621159, by rfl⟩ : syracuseStep 1656425 = 1242319) B1242319
theorem B4179563 : Blo 868566 4179563 := bstep (se 1 (by rfl) ⟨3134672, by rfl⟩ : syracuseStep 4179563 = 6269345) B6269345
theorem B870079 : Blo 868566 870079 := bstep (se 1 (by rfl) ⟨652559, by rfl⟩ : syracuseStep 870079 = 1305119) B1305119
theorem B870335 : Blo 868566 870335 := bstep (se 1 (by rfl) ⟨652751, by rfl⟩ : syracuseStep 870335 = 1305503) B1305503
theorem B870367 : Blo 868566 870367 := bstep (se 1 (by rfl) ⟨652775, by rfl⟩ : syracuseStep 870367 = 1305551) B1305551
theorem B870427 : Blo 868566 870427 := bstep (se 1 (by rfl) ⟨652820, by rfl⟩ : syracuseStep 870427 = 1305641) B1305641
theorem B870431 : Blo 868566 870431 := bstep (se 1 (by rfl) ⟨652823, by rfl⟩ : syracuseStep 870431 = 1305647) B1305647
theorem B870447 : Blo 868566 870447 := bstep (se 1 (by rfl) ⟨652835, by rfl⟩ : syracuseStep 870447 = 1305671) B1305671
theorem B870623 : Blo 868566 870623 := bstep (se 1 (by rfl) ⟨652967, by rfl⟩ : syracuseStep 870623 = 1305935) B1305935
theorem B870683 : Blo 868566 870683 := bstep (se 1 (by rfl) ⟨653012, by rfl⟩ : syracuseStep 870683 = 1306025) B1306025
theorem B870783 : Blo 868566 870783 := bstep (se 1 (by rfl) ⟨653087, by rfl⟩ : syracuseStep 870783 = 1306175) B1306175
theorem B31803947 : Blo 868566 31803947 := bstep (se 1 (by rfl) ⟨23852960, by rfl⟩ : syracuseStep 31803947 = 47705921) B47705921
theorem B870959 : Blo 868566 870959 := bstep (se 1 (by rfl) ⟨653219, by rfl⟩ : syracuseStep 870959 = 1306439) B1306439
theorem B1985119 : Blo 868566 1985119 := bstep (se 1 (by rfl) ⟨1488839, by rfl⟩ : syracuseStep 1985119 = 2977679) B2977679
theorem B871015 : Blo 868566 871015 := bstep (se 1 (by rfl) ⟨653261, by rfl⟩ : syracuseStep 871015 = 1306523) B1306523
theorem B871391 : Blo 868566 871391 := bstep (se 1 (by rfl) ⟨653543, by rfl⟩ : syracuseStep 871391 = 1307087) B1307087
theorem B2477051 : Blo 868566 2477051 := bstep (se 1 (by rfl) ⟨1857788, by rfl⟩ : syracuseStep 2477051 = 3715577) B3715577
theorem B871419 : Blo 868566 871419 := bstep (se 1 (by rfl) ⟨653564, by rfl⟩ : syracuseStep 871419 = 1307129) B1307129
theorem B2935817 : Blo 868566 2935817 := bstep (se 2 (by rfl) ⟨1100931, by rfl⟩ : syracuseStep 2935817 = 2201863) B2201863
theorem B871487 : Blo 868566 871487 := bstep (se 1 (by rfl) ⟨653615, by rfl⟩ : syracuseStep 871487 = 1307231) B1307231
theorem B4967567 : Blo 868566 4967567 := bstep (se 1 (by rfl) ⟨3725675, by rfl⟩ : syracuseStep 4967567 = 7451351) B7451351
theorem B7949677 : Blo 868566 7949677 := bstep (se 3 (by rfl) ⟨1490564, by rfl⟩ : syracuseStep 7949677 = 2981129) B2981129
theorem B871807 : Blo 868566 871807 := bstep (se 1 (by rfl) ⟨653855, by rfl⟩ : syracuseStep 871807 = 1307711) B1307711
theorem B871835 : Blo 868566 871835 := bstep (se 1 (by rfl) ⟨653876, by rfl⟩ : syracuseStep 871835 = 1307753) B1307753
theorem B12537251 : Blo 868566 12537251 := bstep (se 1 (by rfl) ⟨9402938, by rfl⟩ : syracuseStep 12537251 = 18805877) B18805877
theorem B871903 : Blo 868566 871903 := bstep (se 1 (by rfl) ⟨653927, by rfl⟩ : syracuseStep 871903 = 1307855) B1307855
theorem B7949819 : Blo 868566 7949819 := bstep (se 1 (by rfl) ⟨5962364, by rfl⟩ : syracuseStep 7949819 = 11924729) B11924729
theorem B1855055 : Blo 868566 1855055 := bstep (se 1 (by rfl) ⟨1391291, by rfl⟩ : syracuseStep 1855055 = 2782583) B2782583
theorem B872039 : Blo 868566 872039 := bstep (se 1 (by rfl) ⟨654029, by rfl⟩ : syracuseStep 872039 = 1308059) B1308059
theorem B872187 : Blo 868566 872187 := bstep (se 1 (by rfl) ⟨654140, by rfl⟩ : syracuseStep 872187 = 1308281) B1308281
theorem B8376119 : Blo 868566 8376119 := bstep (se 1 (by rfl) ⟨6282089, by rfl⟩ : syracuseStep 8376119 = 12564179) B12564179
theorem B872255 : Blo 868566 872255 := bstep (se 1 (by rfl) ⟨654191, by rfl⟩ : syracuseStep 872255 = 1308383) B1308383
theorem B217829225 : Blo 868566 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B872319 : Blo 868566 872319 := bstep (se 1 (by rfl) ⟨654239, by rfl⟩ : syracuseStep 872319 = 1308479) B1308479
theorem B872431 : Blo 868566 872431 := bstep (se 1 (by rfl) ⟨654323, by rfl⟩ : syracuseStep 872431 = 1308647) B1308647
theorem B872443 : Blo 868566 872443 := bstep (se 1 (by rfl) ⟨654332, by rfl⟩ : syracuseStep 872443 = 1308665) B1308665
theorem B872511 : Blo 868566 872511 := bstep (se 1 (by rfl) ⟨654383, by rfl⟩ : syracuseStep 872511 = 1308767) B1308767
theorem B16764995 : Blo 868566 16764995 := bstep (se 1 (by rfl) ⟨12573746, by rfl⟩ : syracuseStep 16764995 = 25147493) B25147493
theorem B1101919 : Blo 868566 1101919 := bstep (se 1 (by rfl) ⟨826439, by rfl⟩ : syracuseStep 1101919 = 1652879) B1652879
theorem B872551 : Blo 868566 872551 := bstep (se 1 (by rfl) ⟨654413, by rfl⟩ : syracuseStep 872551 = 1308827) B1308827
theorem B4411745 : Blo 868566 4411745 := bstep (se 2 (by rfl) ⟨1654404, by rfl⟩ : syracuseStep 4411745 = 3308809) B3308809
theorem B1855867 : Blo 868566 1855867 := bstep (se 1 (by rfl) ⟨1391900, by rfl⟩ : syracuseStep 1855867 = 2783801) B2783801
theorem B2937275 : Blo 868566 2937275 := bstep (se 1 (by rfl) ⟨2202956, by rfl⟩ : syracuseStep 2937275 = 4405913) B4405913
theorem B3724051 : Blo 868566 3724051 := bstep (se 1 (by rfl) ⟨2793038, by rfl⟩ : syracuseStep 3724051 = 5586077) B5586077
theorem B2937815 : Blo 868566 2937815 := bstep (se 1 (by rfl) ⟨2203361, by rfl⟩ : syracuseStep 2937815 = 4406723) B4406723
theorem B1954799 : Blo 868566 1954799 := bstep (se 1 (by rfl) ⟨1466099, by rfl⟩ : syracuseStep 1954799 = 2932199) B2932199
theorem B26760577 : Blo 868566 26760577 := bstep (se 2 (by rfl) ⟨10035216, by rfl⟩ : syracuseStep 26760577 = 20070433) B20070433
theorem B1955303 : Blo 868566 1955303 := bstep (se 1 (by rfl) ⟨1466477, by rfl⟩ : syracuseStep 1955303 = 2932955) B2932955
theorem B5101177 : Blo 868566 5101177 := bstep (se 2 (by rfl) ⟨1912941, by rfl⟩ : syracuseStep 5101177 = 3825883) B3825883
theorem B1955465 : Blo 868566 1955465 := bstep (se 2 (by rfl) ⟨733299, by rfl⟩ : syracuseStep 1955465 = 1466599) B1466599
theorem B1955483 : Blo 868566 1955483 := bstep (se 1 (by rfl) ⟨1466612, by rfl⟩ : syracuseStep 1955483 = 2933225) B2933225
theorem B3725129 : Blo 868566 3725129 := bstep (se 2 (by rfl) ⟨1396923, by rfl⟩ : syracuseStep 3725129 = 2793847) B2793847
theorem B1955681 : Blo 868566 1955681 := bstep (se 2 (by rfl) ⟨733380, by rfl⟩ : syracuseStep 1955681 = 1466761) B1466761
theorem B3725281 : Blo 868566 3725281 := bstep (se 2 (by rfl) ⟨1396980, by rfl⟩ : syracuseStep 3725281 = 2793961) B2793961
theorem B1955879 : Blo 868566 1955879 := bstep (se 1 (by rfl) ⟨1466909, by rfl⟩ : syracuseStep 1955879 = 2933819) B2933819
theorem B3725351 : Blo 868566 3725351 := bstep (se 1 (by rfl) ⟨2794013, by rfl⟩ : syracuseStep 3725351 = 5588027) B5588027
theorem B1956059 : Blo 868566 1956059 := bstep (se 1 (by rfl) ⟨1467044, by rfl⟩ : syracuseStep 1956059 = 2934089) B2934089
theorem B1857755 : Blo 868566 1857755 := bstep (se 1 (by rfl) ⟨1393316, by rfl⟩ : syracuseStep 1857755 = 2786633) B2786633
theorem B3299561 : Blo 868566 3299561 := bstep (se 2 (by rfl) ⟨1237335, by rfl⟩ : syracuseStep 3299561 = 2474671) B2474671
theorem B2939219 : Blo 868566 2939219 := bstep (se 1 (by rfl) ⟨2204414, by rfl⟩ : syracuseStep 2939219 = 4408829) B4408829
theorem B1956257 : Blo 868566 1956257 := bstep (se 2 (by rfl) ⟨733596, by rfl⟩ : syracuseStep 1956257 = 1467193) B1467193
theorem B1956329 : Blo 868566 1956329 := bstep (se 2 (by rfl) ⟨733623, by rfl⟩ : syracuseStep 1956329 = 1467247) B1467247
theorem B2939759 : Blo 868566 2939759 := bstep (se 1 (by rfl) ⟨2204819, by rfl⟩ : syracuseStep 2939759 = 4409639) B4409639
theorem B2939867 : Blo 868566 2939867 := bstep (se 1 (by rfl) ⟨2204900, by rfl⟩ : syracuseStep 2939867 = 4409801) B4409801
theorem B2940137 : Blo 868566 2940137 := bstep (se 2 (by rfl) ⟨1102551, by rfl⟩ : syracuseStep 2940137 = 2205103) B2205103
theorem B6970835 : Blo 868566 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B2940407 : Blo 868566 2940407 := bstep (se 1 (by rfl) ⟨2205305, by rfl⟩ : syracuseStep 2940407 = 4410611) B4410611
theorem B1957787 : Blo 868566 1957787 := bstep (se 1 (by rfl) ⟨1468340, by rfl⟩ : syracuseStep 1957787 = 2936681) B2936681
theorem B5431499 : Blo 868566 5431499 := bstep (se 1 (by rfl) ⟨4073624, by rfl⟩ : syracuseStep 5431499 = 8147249) B8147249
theorem B17883341 : Blo 868566 17883341 := bstep (se 3 (by rfl) ⟨3353126, by rfl⟩ : syracuseStep 17883341 = 6706253) B6706253
theorem B1761535 : Blo 868566 1761535 := bstep (se 1 (by rfl) ⟨1321151, by rfl⟩ : syracuseStep 1761535 = 2642303) B2642303
theorem B23814425 : Blo 868566 23814425 := bstep (se 2 (by rfl) ⟨8930409, by rfl⟩ : syracuseStep 23814425 = 17860819) B17860819
theorem B1958201 : Blo 868566 1958201 := bstep (se 2 (by rfl) ⟨734325, by rfl⟩ : syracuseStep 1958201 = 1468651) B1468651
theorem B3301793 : Blo 868566 3301793 := bstep (se 2 (by rfl) ⟨1238172, by rfl⟩ : syracuseStep 3301793 = 2476345) B2476345
theorem B81420823 : Blo 868566 81420823 := bstep (se 1 (by rfl) ⟨61065617, by rfl⟩ : syracuseStep 81420823 = 122131235) B122131235
theorem B1303067 : Blo 868566 1303067 := bstep (se 1 (by rfl) ⟨977300, by rfl⟩ : syracuseStep 1303067 = 1954601) B1954601
theorem B2351783 : Blo 868566 2351783 := bstep (se 1 (by rfl) ⟨1763837, by rfl⟩ : syracuseStep 2351783 = 3527675) B3527675
theorem B1303247 : Blo 868566 1303247 := bstep (se 1 (by rfl) ⟨977435, by rfl⟩ : syracuseStep 1303247 = 1954871) B1954871
theorem B1303259 : Blo 868566 1303259 := bstep (se 1 (by rfl) ⟨977444, by rfl⟩ : syracuseStep 1303259 = 1954889) B1954889
theorem B2974495 : Blo 868566 2974495 := bstep (se 1 (by rfl) ⟨2230871, by rfl⟩ : syracuseStep 2974495 = 4461743) B4461743
theorem B1958687 : Blo 868566 1958687 := bstep (se 1 (by rfl) ⟨1469015, by rfl⟩ : syracuseStep 1958687 = 2938031) B2938031
theorem B1762145 : Blo 868566 1762145 := bstep (se 2 (by rfl) ⟨660804, by rfl⟩ : syracuseStep 1762145 = 1321609) B1321609
theorem B4187251 : Blo 868566 4187251 := bstep (se 1 (by rfl) ⟨3140438, by rfl⟩ : syracuseStep 4187251 = 6280877) B6280877
theorem B1303673 : Blo 868566 1303673 := bstep (se 2 (by rfl) ⟨488877, by rfl⟩ : syracuseStep 1303673 = 977755) B977755
theorem B1467895 : Blo 868566 1467895 := bstep (se 1 (by rfl) ⟨1100921, by rfl⟩ : syracuseStep 1467895 = 2201843) B2201843
theorem B1959497 : Blo 868566 1959497 := bstep (se 2 (by rfl) ⟨734811, by rfl⟩ : syracuseStep 1959497 = 1469623) B1469623
theorem B1304543 : Blo 868566 1304543 := bstep (se 1 (by rfl) ⟨978407, by rfl⟩ : syracuseStep 1304543 = 1956815) B1956815
theorem B1304555 : Blo 868566 1304555 := bstep (se 1 (by rfl) ⟨978416, by rfl⟩ : syracuseStep 1304555 = 1956833) B1956833
theorem B1959929 : Blo 868566 1959929 := bstep (se 2 (by rfl) ⟨734973, by rfl⟩ : syracuseStep 1959929 = 1469947) B1469947
theorem B1304603 : Blo 868566 1304603 := bstep (se 1 (by rfl) ⟨978452, by rfl⟩ : syracuseStep 1304603 = 1956905) B1956905
theorem B1239067 : Blo 868566 1239067 := bstep (se 1 (by rfl) ⟨929300, by rfl⟩ : syracuseStep 1239067 = 1858601) B1858601
theorem B1959983 : Blo 868566 1959983 := bstep (se 1 (by rfl) ⟨1469987, by rfl⟩ : syracuseStep 1959983 = 2939975) B2939975
theorem B1960019 : Blo 868566 1960019 := bstep (se 1 (by rfl) ⟨1470014, by rfl⟩ : syracuseStep 1960019 = 2940029) B2940029
theorem B1960199 : Blo 868566 1960199 := bstep (se 1 (by rfl) ⟨1470149, by rfl⟩ : syracuseStep 1960199 = 2940299) B2940299
theorem B977179 : Blo 868566 977179 := bstep (se 1 (by rfl) ⟨732884, by rfl⟩ : syracuseStep 977179 = 1465769) B1465769
theorem B1304969 : Blo 868566 1304969 := bstep (se 2 (by rfl) ⟨489363, by rfl⟩ : syracuseStep 1304969 = 978727) B978727
theorem B1763831 : Blo 868566 1763831 := bstep (se 1 (by rfl) ⟨1322873, by rfl⟩ : syracuseStep 1763831 = 2645747) B2645747
theorem B1468921 : Blo 868566 1468921 := bstep (se 2 (by rfl) ⟨550845, by rfl⟩ : syracuseStep 1468921 = 1101691) B1101691
theorem B1468975 : Blo 868566 1468975 := bstep (se 1 (by rfl) ⟨1101731, by rfl⟩ : syracuseStep 1468975 = 2203463) B2203463
theorem B1960505 : Blo 868566 1960505 := bstep (se 2 (by rfl) ⟨735189, by rfl⟩ : syracuseStep 1960505 = 1470379) B1470379
theorem B1469191 : Blo 868566 1469191 := bstep (se 1 (by rfl) ⟨1101893, by rfl⟩ : syracuseStep 1469191 = 2203787) B2203787
theorem B1469407 : Blo 868566 1469407 := bstep (se 1 (by rfl) ⟨1102055, by rfl⟩ : syracuseStep 1469407 = 2204111) B2204111
theorem B7957673 : Blo 868566 7957673 := bstep (se 2 (by rfl) ⟨2984127, by rfl⟩ : syracuseStep 7957673 = 5968255) B5968255
theorem B1961225 : Blo 868566 1961225 := bstep (se 2 (by rfl) ⟨735459, by rfl⟩ : syracuseStep 1961225 = 1470919) B1470919
theorem B1305911 : Blo 868566 1305911 := bstep (se 1 (by rfl) ⟨979433, by rfl⟩ : syracuseStep 1305911 = 1958867) B1958867
theorem B978331 : Blo 868566 978331 := bstep (se 1 (by rfl) ⟨733748, by rfl⟩ : syracuseStep 978331 = 1467497) B1467497
theorem B1306079 : Blo 868566 1306079 := bstep (se 1 (by rfl) ⟨979559, by rfl⟩ : syracuseStep 1306079 = 1959119) B1959119
theorem B2092511 : Blo 868566 2092511 := bstep (se 1 (by rfl) ⟨1569383, by rfl⟩ : syracuseStep 2092511 = 3138767) B3138767
theorem B3534407 : Blo 868566 3534407 := bstep (se 1 (by rfl) ⟨2650805, by rfl⟩ : syracuseStep 3534407 = 5301611) B5301611
theorem B64286327 : Blo 868566 64286327 := bstep (se 1 (by rfl) ⟨48214745, by rfl⟩ : syracuseStep 64286327 = 96429491) B96429491
theorem B1306295 : Blo 868566 1306295 := bstep (se 1 (by rfl) ⟨979721, by rfl⟩ : syracuseStep 1306295 = 1959443) B1959443
theorem B3534587 : Blo 868566 3534587 := bstep (se 1 (by rfl) ⟨2650940, by rfl⟩ : syracuseStep 3534587 = 5301881) B5301881
theorem B1470271 : Blo 868566 1470271 := bstep (se 1 (by rfl) ⟨1102703, by rfl⟩ : syracuseStep 1470271 = 2205407) B2205407
theorem B1306505 : Blo 868566 1306505 := bstep (se 2 (by rfl) ⟨489939, by rfl⟩ : syracuseStep 1306505 = 979879) B979879
theorem B1765459 : Blo 868566 1765459 := bstep (se 1 (by rfl) ⟨1324094, by rfl⟩ : syracuseStep 1765459 = 2648189) B2648189
theorem B1044583 : Blo 868566 1044583 := bstep (se 1 (by rfl) ⟨783437, by rfl⟩ : syracuseStep 1044583 = 1566875) B1566875
theorem B1306751 : Blo 868566 1306751 := bstep (se 1 (by rfl) ⟨980063, by rfl⟩ : syracuseStep 1306751 = 1960127) B1960127
theorem B1962215 : Blo 868566 1962215 := bstep (se 1 (by rfl) ⟨1471661, by rfl⟩ : syracuseStep 1962215 = 2943323) B2943323
theorem B7434503 : Blo 868566 7434503 := bstep (se 1 (by rfl) ⟨5575877, by rfl⟩ : syracuseStep 7434503 = 11151755) B11151755
theorem B979303 : Blo 868566 979303 := bstep (se 1 (by rfl) ⟨734477, by rfl⟩ : syracuseStep 979303 = 1468955) B1468955
theorem B1962395 : Blo 868566 1962395 := bstep (se 1 (by rfl) ⟨1471796, by rfl⟩ : syracuseStep 1962395 = 2943593) B2943593
theorem B1307387 : Blo 868566 1307387 := bstep (se 1 (by rfl) ⟨980540, by rfl⟩ : syracuseStep 1307387 = 1961081) B1961081
theorem B1471439 : Blo 868566 1471439 := bstep (se 1 (by rfl) ⟨1103579, by rfl⟩ : syracuseStep 1471439 = 2207159) B2207159
theorem B1045487 : Blo 868566 1045487 := bstep (se 1 (by rfl) ⟨784115, by rfl⟩ : syracuseStep 1045487 = 1568231) B1568231
theorem B979951 : Blo 868566 979951 := bstep (se 1 (by rfl) ⟨734963, by rfl⟩ : syracuseStep 979951 = 1469927) B1469927
theorem B1963079 : Blo 868566 1963079 := bstep (se 1 (by rfl) ⟨1472309, by rfl⟩ : syracuseStep 1963079 = 2944619) B2944619
theorem B1307831 : Blo 868566 1307831 := bstep (se 1 (by rfl) ⟨980873, by rfl⟩ : syracuseStep 1307831 = 1961747) B1961747
theorem B1963259 : Blo 868566 1963259 := bstep (se 1 (by rfl) ⟨1472444, by rfl⟩ : syracuseStep 1963259 = 2944889) B2944889
theorem B1308071 : Blo 868566 1308071 := bstep (se 1 (by rfl) ⟨981053, by rfl⟩ : syracuseStep 1308071 = 1962107) B1962107
theorem B3143123 : Blo 868566 3143123 := bstep (se 1 (by rfl) ⟨2357342, by rfl⟩ : syracuseStep 3143123 = 4714685) B4714685
theorem B980455 : Blo 868566 980455 := bstep (se 1 (by rfl) ⟨735341, by rfl⟩ : syracuseStep 980455 = 1470683) B1470683
theorem B1308251 : Blo 868566 1308251 := bstep (se 1 (by rfl) ⟨981188, by rfl⟩ : syracuseStep 1308251 = 1962377) B1962377
theorem B3012191 : Blo 868566 3012191 := bstep (se 1 (by rfl) ⟨2259143, by rfl⟩ : syracuseStep 3012191 = 4518287) B4518287
theorem B980635 : Blo 868566 980635 := bstep (se 1 (by rfl) ⟨735476, by rfl⟩ : syracuseStep 980635 = 1470953) B1470953
theorem B1570537 : Blo 868566 1570537 := bstep (se 2 (by rfl) ⟨588951, by rfl⟩ : syracuseStep 1570537 = 1177903) B1177903
theorem B1308713 : Blo 868566 1308713 := bstep (se 2 (by rfl) ⟨490767, by rfl⟩ : syracuseStep 1308713 = 981535) B981535
theorem B1308743 : Blo 868566 1308743 := bstep (se 1 (by rfl) ⟨981557, by rfl⟩ : syracuseStep 1308743 = 1963115) B1963115
theorem B8353975 : Blo 868566 8353975 := bstep (se 1 (by rfl) ⟨6265481, by rfl⟩ : syracuseStep 8353975 = 12530963) B12530963
theorem B3307823 : Blo 868566 3307823 := bstep (se 1 (by rfl) ⟨2480867, by rfl⟩ : syracuseStep 3307823 = 4961735) B4961735
theorem B16939489 : Blo 868566 16939489 := bstep (se 2 (by rfl) ⟨6352308, by rfl⟩ : syracuseStep 16939489 = 12704617) B12704617
theorem B71432765 : Blo 868566 71432765 := bstep (se 3 (by rfl) ⟨13393643, by rfl⟩ : syracuseStep 71432765 = 26787287) B26787287
theorem B2652763 : Blo 868566 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B1572065 : Blo 868566 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B1048015 : Blo 868566 1048015 := bstep (se 1 (by rfl) ⟨786011, by rfl⟩ : syracuseStep 1048015 = 1572023) B1572023
theorem B1048231 : Blo 868566 1048231 := bstep (se 1 (by rfl) ⟨786173, by rfl⟩ : syracuseStep 1048231 = 1572347) B1572347
theorem B6782707 : Blo 868566 6782707 := bstep (se 1 (by rfl) ⟨5087030, by rfl⟩ : syracuseStep 6782707 = 10174061) B10174061
theorem B8159687 : Blo 868566 8159687 := bstep (se 1 (by rfl) ⟨6119765, by rfl⟩ : syracuseStep 8159687 = 12239531) B12239531
theorem B2982415 : Blo 868566 2982415 := bstep (se 1 (by rfl) ⟨2236811, by rfl⟩ : syracuseStep 2982415 = 4473623) B4473623
theorem B5571109 : Blo 868566 5571109 := bstep (se 4 (by rfl) ⟨522291, by rfl⟩ : syracuseStep 5571109 = 1044583) B1044583
theorem B108561097 : Blo 868566 108561097 := bstep (se 2 (by rfl) ⟨40710411, by rfl⟩ : syracuseStep 108561097 = 81420823) B81420823
theorem B3965993 : Blo 868566 3965993 := bstep (se 2 (by rfl) ⟨1487247, by rfl⟩ : syracuseStep 3965993 = 2974495) B2974495
theorem B2786375 : Blo 868566 2786375 := bstep (se 1 (by rfl) ⟨2089781, by rfl⟩ : syracuseStep 2786375 = 4179563) B4179563
theorem B21202631 : Blo 868566 21202631 := bstep (se 1 (by rfl) ⟨15901973, by rfl⟩ : syracuseStep 21202631 = 31803947) B31803947
theorem B6621263 : Blo 868566 6621263 := bstep (se 1 (by rfl) ⟨4965947, by rfl⟩ : syracuseStep 6621263 = 9931895) B9931895
theorem B3311711 : Blo 868566 3311711 := bstep (se 1 (by rfl) ⟨2483783, by rfl⟩ : syracuseStep 3311711 = 4967567) B4967567
theorem B8358167 : Blo 868566 8358167 := bstep (se 1 (by rfl) ⟨6268625, by rfl⟩ : syracuseStep 8358167 = 12537251) B12537251
theorem B17893669 : Blo 868566 17893669 := bstep (se 4 (by rfl) ⟨1677531, by rfl⟩ : syracuseStep 17893669 = 3355063) B3355063
theorem B2787965 : Blo 868566 2787965 := bstep (se 3 (by rfl) ⟨522743, by rfl⟩ : syracuseStep 2787965 = 1045487) B1045487
theorem B11176663 : Blo 868566 11176663 := bstep (se 1 (by rfl) ⟨8382497, by rfl⟩ : syracuseStep 11176663 = 16764995) B16764995
theorem B160960193 : Blo 868566 160960193 := bstep (se 2 (by rfl) ⟨60360072, by rfl⟩ : syracuseStep 160960193 = 120720145) B120720145
theorem B2199707 : Blo 868566 2199707 := bstep (se 1 (by rfl) ⟨1649780, by rfl⟩ : syracuseStep 2199707 = 3299561) B3299561
theorem B2233919 : Blo 868566 2233919 := bstep (se 1 (by rfl) ⟨1675439, by rfl⟩ : syracuseStep 2233919 = 3350879) B3350879
theorem B2201195 : Blo 868566 2201195 := bstep (se 1 (by rfl) ⟨1650896, by rfl⟩ : syracuseStep 2201195 = 3301793) B3301793
theorem B4953737 : Blo 868566 4953737 := bstep (se 2 (by rfl) ⟨1857651, by rfl⟩ : syracuseStep 4953737 = 3715303) B3715303
theorem B2202025 : Blo 868566 2202025 := bstep (se 2 (by rfl) ⟨825759, by rfl⟩ : syracuseStep 2202025 = 1651519) B1651519
theorem B4956335 : Blo 868566 4956335 := bstep (se 1 (by rfl) ⟨3717251, by rfl⟩ : syracuseStep 4956335 = 7434503) B7434503
theorem B22585985 : Blo 868566 22585985 := bstep (se 2 (by rfl) ⟨8469744, by rfl⟩ : syracuseStep 22585985 = 16939489) B16939489
theorem B2008127 : Blo 868566 2008127 := bstep (se 1 (by rfl) ⟨1506095, by rfl⟩ : syracuseStep 2008127 = 3012191) B3012191
theorem B5580029 : Blo 868566 5580029 := bstep (se 3 (by rfl) ⟨1046255, by rfl⟩ : syracuseStep 5580029 = 2092511) B2092511
theorem B2205215 : Blo 868566 2205215 := bstep (se 1 (by rfl) ⟨1653911, by rfl⟩ : syracuseStep 2205215 = 3307823) B3307823
theorem B47621843 : Blo 868566 47621843 := bstep (se 1 (by rfl) ⟨35716382, by rfl⟩ : syracuseStep 47621843 = 71432765) B71432765
theorem B76294691 : Blo 868566 76294691 := bstep (se 1 (by rfl) ⟨57221018, by rfl⟩ : syracuseStep 76294691 = 114442037) B114442037
theorem B12528539 : Blo 868566 12528539 := bstep (se 1 (by rfl) ⟨9396404, by rfl⟩ : syracuseStep 12528539 = 18792809) B18792809
theorem B1256555 : Blo 868566 1256555 := bstep (se 1 (by rfl) ⟨942416, by rfl⟩ : syracuseStep 1256555 = 1884833) B1884833
theorem B6597935 : Blo 868566 6597935 := bstep (se 1 (by rfl) ⟨4948451, by rfl⟩ : syracuseStep 6597935 = 9896903) B9896903
theorem B4402511 : Blo 868566 4402511 := bstep (se 1 (by rfl) ⟨3301883, by rfl⟩ : syracuseStep 4402511 = 6603767) B6603767
theorem B4959569 : Blo 868566 4959569 := bstep (se 2 (by rfl) ⟨1859838, by rfl⟩ : syracuseStep 4959569 = 3719677) B3719677
theorem B2207209 : Blo 868566 2207209 := bstep (se 2 (by rfl) ⟨827703, by rfl⟩ : syracuseStep 2207209 = 1655407) B1655407
theorem B6271019 : Blo 868566 6271019 := bstep (se 1 (by rfl) ⟨4703264, by rfl⟩ : syracuseStep 6271019 = 9406529) B9406529
theorem B5583001 : Blo 868566 5583001 := bstep (se 2 (by rfl) ⟨2093625, by rfl⟩ : syracuseStep 5583001 = 4187251) B4187251
theorem B2207999 : Blo 868566 2207999 := bstep (se 1 (by rfl) ⟨1655999, by rfl⟩ : syracuseStep 2207999 = 3311999) B3311999
theorem B5288399 : Blo 868566 5288399 := bstep (se 1 (by rfl) ⟨3966299, by rfl⟩ : syracuseStep 5288399 = 7932599) B7932599
theorem B4174375 : Blo 868566 4174375 := bstep (se 1 (by rfl) ⟨3130781, by rfl⟩ : syracuseStep 4174375 = 6261563) B6261563
theorem B42349205 : Blo 868566 42349205 := bstep (se 6 (by rfl) ⟨992559, by rfl⟩ : syracuseStep 42349205 = 1985119) B1985119
theorem B1651367 : Blo 868566 1651367 := bstep (se 1 (by rfl) ⟨1238525, by rfl⟩ : syracuseStep 1651367 = 2477051) B2477051
theorem B1487855 : Blo 868566 1487855 := bstep (se 1 (by rfl) ⟨1115891, by rfl⟩ : syracuseStep 1487855 = 2231783) B2231783
theorem B5584079 : Blo 868566 5584079 := bstep (se 1 (by rfl) ⟨4188059, by rfl⟩ : syracuseStep 5584079 = 8376119) B8376119
theorem B1652089 : Blo 868566 1652089 := bstep (se 2 (by rfl) ⟨619533, by rfl⟩ : syracuseStep 1652089 = 1239067) B1239067
theorem B235518167 : Blo 868566 235518167 := bstep (se 1 (by rfl) ⟨176638625, by rfl⟩ : syracuseStep 235518167 = 353277251) B353277251
theorem B12564983 : Blo 868566 12564983 := bstep (se 1 (by rfl) ⟨9423737, by rfl⟩ : syracuseStep 12564983 = 18847475) B18847475
theorem B37665881 : Blo 868566 37665881 := bstep (se 2 (by rfl) ⟨14124705, by rfl⟩ : syracuseStep 37665881 = 28249411) B28249411
theorem B10599569 : Blo 868566 10599569 := bstep (se 2 (by rfl) ⟨3974838, by rfl⟩ : syracuseStep 10599569 = 7949677) B7949677
theorem B6438737 : Blo 868566 6438737 := bstep (se 2 (by rfl) ⟨2414526, by rfl⟩ : syracuseStep 6438737 = 4829053) B4829053
theorem B3620999 : Blo 868566 3620999 := bstep (se 1 (by rfl) ⟨2715749, by rfl⟩ : syracuseStep 3620999 = 5431499) B5431499
theorem B15876283 : Blo 868566 15876283 := bstep (se 1 (by rfl) ⟨11907212, by rfl⟩ : syracuseStep 15876283 = 23814425) B23814425
theorem B868711 : Blo 868566 868711 := bstep (se 1 (by rfl) ⟨651533, by rfl⟩ : syracuseStep 868711 = 1303067) B1303067
theorem B14893469 : Blo 868566 14893469 := bstep (se 3 (by rfl) ⟨2792525, by rfl⟩ : syracuseStep 14893469 = 5585051) B5585051
theorem B868831 : Blo 868566 868831 := bstep (se 1 (by rfl) ⟨651623, by rfl⟩ : syracuseStep 868831 = 1303247) B1303247
theorem B868839 : Blo 868566 868839 := bstep (se 1 (by rfl) ⟨651629, by rfl⟩ : syracuseStep 868839 = 1303259) B1303259
theorem B2474489 : Blo 868566 2474489 := bstep (se 2 (by rfl) ⟨927933, by rfl⟩ : syracuseStep 2474489 = 1855867) B1855867
theorem B2933279 : Blo 868566 2933279 := bstep (se 1 (by rfl) ⟨2199959, by rfl⟩ : syracuseStep 2933279 = 4399919) B4399919
theorem B869115 : Blo 868566 869115 := bstep (se 1 (by rfl) ⟨651836, by rfl⟩ : syracuseStep 869115 = 1303673) B1303673
theorem B4965401 : Blo 868566 4965401 := bstep (se 2 (by rfl) ⟨1862025, by rfl⟩ : syracuseStep 4965401 = 3724051) B3724051
theorem B4965583 : Blo 868566 4965583 := bstep (se 1 (by rfl) ⟨3724187, by rfl⟩ : syracuseStep 4965583 = 7448375) B7448375
theorem B7521599 : Blo 868566 7521599 := bstep (se 1 (by rfl) ⟨5641199, by rfl⟩ : syracuseStep 7521599 = 11282399) B11282399
theorem B869695 : Blo 868566 869695 := bstep (se 1 (by rfl) ⟨652271, by rfl⟩ : syracuseStep 869695 = 1304543) B1304543
theorem B869703 : Blo 868566 869703 := bstep (se 1 (by rfl) ⟨652277, by rfl⟩ : syracuseStep 869703 = 1304555) B1304555
theorem B869735 : Blo 868566 869735 := bstep (se 1 (by rfl) ⟨652301, by rfl⟩ : syracuseStep 869735 = 1304603) B1304603
theorem B869979 : Blo 868566 869979 := bstep (se 1 (by rfl) ⟨652484, by rfl⟩ : syracuseStep 869979 = 1304969) B1304969
theorem B16762535 : Blo 868566 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B6801569 : Blo 868566 6801569 := bstep (se 2 (by rfl) ⟨2550588, by rfl⟩ : syracuseStep 6801569 = 5101177) B5101177
theorem B10602679 : Blo 868566 10602679 := bstep (se 1 (by rfl) ⟨7952009, by rfl⟩ : syracuseStep 10602679 = 15904019) B15904019
theorem B870607 : Blo 868566 870607 := bstep (se 1 (by rfl) ⟨652955, by rfl⟩ : syracuseStep 870607 = 1305911) B1305911
theorem B4704479 : Blo 868566 4704479 := bstep (se 1 (by rfl) ⟨3528359, by rfl⟩ : syracuseStep 4704479 = 7056719) B7056719
theorem B870719 : Blo 868566 870719 := bstep (se 1 (by rfl) ⟨653039, by rfl⟩ : syracuseStep 870719 = 1306079) B1306079
theorem B870863 : Blo 868566 870863 := bstep (se 1 (by rfl) ⟨653147, by rfl⟩ : syracuseStep 870863 = 1306295) B1306295
theorem B14862851 : Blo 868566 14862851 := bstep (se 1 (by rfl) ⟨11147138, by rfl⟩ : syracuseStep 14862851 = 22294277) B22294277
theorem B871003 : Blo 868566 871003 := bstep (se 1 (by rfl) ⟨653252, by rfl⟩ : syracuseStep 871003 = 1306505) B1306505
theorem B4967041 : Blo 868566 4967041 := bstep (se 2 (by rfl) ⟨1862640, by rfl⟩ : syracuseStep 4967041 = 3725281) B3725281
theorem B871167 : Blo 868566 871167 := bstep (se 1 (by rfl) ⟨653375, by rfl⟩ : syracuseStep 871167 = 1306751) B1306751
theorem B871591 : Blo 868566 871591 := bstep (se 1 (by rfl) ⟨653693, by rfl⟩ : syracuseStep 871591 = 1307387) B1307387
theorem B3132827 : Blo 868566 3132827 := bstep (se 1 (by rfl) ⟨2349620, by rfl⟩ : syracuseStep 3132827 = 4699241) B4699241
theorem B871887 : Blo 868566 871887 := bstep (se 1 (by rfl) ⟨653915, by rfl⟩ : syracuseStep 871887 = 1307831) B1307831
theorem B5590565 : Blo 868566 5590565 := bstep (se 4 (by rfl) ⟨524115, by rfl⟩ : syracuseStep 5590565 = 1048231) B1048231
theorem B4247113 : Blo 868566 4247113 := bstep (se 2 (by rfl) ⟨1592667, by rfl⟩ : syracuseStep 4247113 = 3185335) B3185335
theorem B872047 : Blo 868566 872047 := bstep (se 1 (by rfl) ⟨654035, by rfl⟩ : syracuseStep 872047 = 1308071) B1308071
theorem B872167 : Blo 868566 872167 := bstep (se 1 (by rfl) ⟨654125, by rfl⟩ : syracuseStep 872167 = 1308251) B1308251
theorem B872475 : Blo 868566 872475 := bstep (se 1 (by rfl) ⟨654356, by rfl⟩ : syracuseStep 872475 = 1308713) B1308713
theorem B872495 : Blo 868566 872495 := bstep (se 1 (by rfl) ⟨654371, by rfl⟩ : syracuseStep 872495 = 1308743) B1308743
theorem B1987129 : Blo 868566 1987129 := bstep (se 2 (by rfl) ⟨745173, by rfl⟩ : syracuseStep 1987129 = 1490347) B1490347
theorem B1397353 : Blo 868566 1397353 := bstep (se 2 (by rfl) ⟨524007, by rfl⟩ : syracuseStep 1397353 = 1048015) B1048015
theorem B1102567 : Blo 868566 1102567 := bstep (se 1 (by rfl) ⟨826925, by rfl⟩ : syracuseStep 1102567 = 1653851) B1653851
theorem B1954727 : Blo 868566 1954727 := bstep (se 1 (by rfl) ⟨1466045, by rfl⟩ : syracuseStep 1954727 = 2932091) B2932091
theorem B1103159 : Blo 868566 1103159 := bstep (se 1 (by rfl) ⟨827369, by rfl⟩ : syracuseStep 1103159 = 1654739) B1654739
theorem B16733627 : Blo 868566 16733627 := bstep (se 1 (by rfl) ⟨12550220, by rfl⟩ : syracuseStep 16733627 = 25100441) B25100441
theorem B2643617 : Blo 868566 2643617 := bstep (se 2 (by rfl) ⟨991356, by rfl⟩ : syracuseStep 2643617 = 1982713) B1982713
theorem B2348713 : Blo 868566 2348713 := bstep (se 2 (by rfl) ⟨880767, by rfl⟩ : syracuseStep 2348713 = 1761535) B1761535
theorem B6608627 : Blo 868566 6608627 := bstep (se 1 (by rfl) ⟨4956470, by rfl⟩ : syracuseStep 6608627 = 9912941) B9912941
theorem B5953283 : Blo 868566 5953283 := bstep (se 1 (by rfl) ⟨4464962, by rfl⟩ : syracuseStep 5953283 = 8929925) B8929925
theorem B9394157 : Blo 868566 9394157 := bstep (se 3 (by rfl) ⟨1761404, by rfl⟩ : syracuseStep 9394157 = 3522809) B3522809
theorem B1104283 : Blo 868566 1104283 := bstep (se 1 (by rfl) ⟨828212, by rfl⟩ : syracuseStep 1104283 = 1656425) B1656425
theorem B1957193 : Blo 868566 1957193 := bstep (se 2 (by rfl) ⟨733947, by rfl⟩ : syracuseStep 1957193 = 1467895) B1467895
theorem B1957211 : Blo 868566 1957211 := bstep (se 1 (by rfl) ⟨1467908, by rfl⟩ : syracuseStep 1957211 = 2935817) B2935817
theorem B1858943 : Blo 868566 1858943 := bstep (se 1 (by rfl) ⟨1394207, by rfl⟩ : syracuseStep 1858943 = 2788415) B2788415
theorem B5299879 : Blo 868566 5299879 := bstep (se 1 (by rfl) ⟨3974909, by rfl⟩ : syracuseStep 5299879 = 7949819) B7949819
theorem B1236703 : Blo 868566 1236703 := bstep (se 1 (by rfl) ⟨927527, by rfl⟩ : syracuseStep 1236703 = 1855055) B1855055
theorem B145219483 : Blo 868566 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B4415633 : Blo 868566 4415633 := bstep (se 2 (by rfl) ⟨1655862, by rfl⟩ : syracuseStep 4415633 = 3311725) B3311725
theorem B2941163 : Blo 868566 2941163 := bstep (se 1 (by rfl) ⟨2205872, by rfl⟩ : syracuseStep 2941163 = 4411745) B4411745
theorem B1958183 : Blo 868566 1958183 := bstep (se 1 (by rfl) ⟨1468637, by rfl⟩ : syracuseStep 1958183 = 2937275) B2937275
theorem B1302905 : Blo 868566 1302905 := bstep (se 2 (by rfl) ⟨488589, by rfl⟩ : syracuseStep 1302905 = 977179) B977179
theorem B1958543 : Blo 868566 1958543 := bstep (se 1 (by rfl) ⟨1468907, by rfl⟩ : syracuseStep 1958543 = 2937815) B2937815
theorem B1303199 : Blo 868566 1303199 := bstep (se 1 (by rfl) ⟨977399, by rfl⟩ : syracuseStep 1303199 = 1954799) B1954799
theorem B1958561 : Blo 868566 1958561 := bstep (se 2 (by rfl) ⟨734460, by rfl⟩ : syracuseStep 1958561 = 1468921) B1468921
theorem B1860283 : Blo 868566 1860283 := bstep (se 1 (by rfl) ⟨1395212, by rfl⟩ : syracuseStep 1860283 = 2790425) B2790425
theorem B1958633 : Blo 868566 1958633 := bstep (se 2 (by rfl) ⟨734487, by rfl⟩ : syracuseStep 1958633 = 1468975) B1468975
theorem B1303535 : Blo 868566 1303535 := bstep (se 1 (by rfl) ⟨977651, by rfl⟩ : syracuseStep 1303535 = 1955303) B1955303
theorem B1958921 : Blo 868566 1958921 := bstep (se 2 (by rfl) ⟨734595, by rfl⟩ : syracuseStep 1958921 = 1469191) B1469191
theorem B1303643 : Blo 868566 1303643 := bstep (se 1 (by rfl) ⟨977732, by rfl⟩ : syracuseStep 1303643 = 1955465) B1955465
theorem B1303655 : Blo 868566 1303655 := bstep (se 1 (by rfl) ⟨977741, by rfl⟩ : syracuseStep 1303655 = 1955483) B1955483
theorem B2483419 : Blo 868566 2483419 := bstep (se 1 (by rfl) ⟨1862564, by rfl⟩ : syracuseStep 2483419 = 3725129) B3725129
theorem B1303787 : Blo 868566 1303787 := bstep (se 1 (by rfl) ⟨977840, by rfl⟩ : syracuseStep 1303787 = 1955681) B1955681
theorem B1959209 : Blo 868566 1959209 := bstep (se 2 (by rfl) ⟨734703, by rfl⟩ : syracuseStep 1959209 = 1469407) B1469407
theorem B1303919 : Blo 868566 1303919 := bstep (se 1 (by rfl) ⟨977939, by rfl⟩ : syracuseStep 1303919 = 1955879) B1955879
theorem B2483567 : Blo 868566 2483567 := bstep (se 1 (by rfl) ⟨1862675, by rfl⟩ : syracuseStep 2483567 = 3725351) B3725351
theorem B1304039 : Blo 868566 1304039 := bstep (se 1 (by rfl) ⟨978029, by rfl⟩ : syracuseStep 1304039 = 1956059) B1956059
theorem B1238503 : Blo 868566 1238503 := bstep (se 1 (by rfl) ⟨928877, by rfl⟩ : syracuseStep 1238503 = 1857755) B1857755
theorem B1959479 : Blo 868566 1959479 := bstep (se 1 (by rfl) ⟨1469609, by rfl⟩ : syracuseStep 1959479 = 2939219) B2939219
theorem B1304171 : Blo 868566 1304171 := bstep (se 1 (by rfl) ⟨978128, by rfl⟩ : syracuseStep 1304171 = 1956257) B1956257
theorem B1304219 : Blo 868566 1304219 := bstep (se 1 (by rfl) ⟨978164, by rfl⟩ : syracuseStep 1304219 = 1956329) B1956329
theorem B1304441 : Blo 868566 1304441 := bstep (se 2 (by rfl) ⟨489165, by rfl⟩ : syracuseStep 1304441 = 978331) B978331
theorem B1959839 : Blo 868566 1959839 := bstep (se 1 (by rfl) ⟨1469879, by rfl⟩ : syracuseStep 1959839 = 2939759) B2939759
theorem B1468327 : Blo 868566 1468327 := bstep (se 1 (by rfl) ⟨1101245, by rfl⟩ : syracuseStep 1468327 = 2202491) B2202491
theorem B1959911 : Blo 868566 1959911 := bstep (se 1 (by rfl) ⟨1469933, by rfl⟩ : syracuseStep 1959911 = 2939867) B2939867
theorem B1960091 : Blo 868566 1960091 := bstep (se 1 (by rfl) ⟨1470068, by rfl⟩ : syracuseStep 1960091 = 2940137) B2940137
theorem B4647223 : Blo 868566 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B1960271 : Blo 868566 1960271 := bstep (se 1 (by rfl) ⟨1470203, by rfl⟩ : syracuseStep 1960271 = 2940407) B2940407
theorem B1960361 : Blo 868566 1960361 := bstep (se 2 (by rfl) ⟨735135, by rfl⟩ : syracuseStep 1960361 = 1470271) B1470271
theorem B1305191 : Blo 868566 1305191 := bstep (se 1 (by rfl) ⟨978893, by rfl⟩ : syracuseStep 1305191 = 1957787) B1957787
theorem B1469083 : Blo 868566 1469083 := bstep (se 1 (by rfl) ⟨1101812, by rfl⟩ : syracuseStep 1469083 = 2203625) B2203625
theorem B1862299 : Blo 868566 1862299 := bstep (se 1 (by rfl) ⟨1396724, by rfl⟩ : syracuseStep 1862299 = 2793449) B2793449
theorem B2353945 : Blo 868566 2353945 := bstep (se 2 (by rfl) ⟨882729, by rfl⟩ : syracuseStep 2353945 = 1765459) B1765459
theorem B1469225 : Blo 868566 1469225 := bstep (se 2 (by rfl) ⟨550959, by rfl⟩ : syracuseStep 1469225 = 1101919) B1101919
theorem B11922227 : Blo 868566 11922227 := bstep (se 1 (by rfl) ⟨8941670, by rfl⟩ : syracuseStep 11922227 = 17883341) B17883341
theorem B1305467 : Blo 868566 1305467 := bstep (se 1 (by rfl) ⟨979100, by rfl⟩ : syracuseStep 1305467 = 1958201) B1958201
theorem B2944025 : Blo 868566 2944025 := bstep (se 2 (by rfl) ⟨1104009, by rfl⟩ : syracuseStep 2944025 = 2208019) B2208019
theorem B1469495 : Blo 868566 1469495 := bstep (se 1 (by rfl) ⟨1102121, by rfl⟩ : syracuseStep 1469495 = 2204243) B2204243
theorem B1567855 : Blo 868566 1567855 := bstep (se 1 (by rfl) ⟨1175891, by rfl⟩ : syracuseStep 1567855 = 2351783) B2351783
theorem B1305737 : Blo 868566 1305737 := bstep (se 2 (by rfl) ⟨489651, by rfl⟩ : syracuseStep 1305737 = 979303) B979303
theorem B1305791 : Blo 868566 1305791 := bstep (se 1 (by rfl) ⟨979343, by rfl⟩ : syracuseStep 1305791 = 1958687) B1958687
theorem B1174763 : Blo 868566 1174763 := bstep (se 1 (by rfl) ⟨881072, by rfl⟩ : syracuseStep 1174763 = 1762145) B1762145
theorem B3173807 : Blo 868566 3173807 := bstep (se 1 (by rfl) ⟨2380355, by rfl⟩ : syracuseStep 3173807 = 4760711) B4760711
theorem B1470055 : Blo 868566 1470055 := bstep (se 1 (by rfl) ⟨1102541, by rfl⟩ : syracuseStep 1470055 = 2205083) B2205083
theorem B1306331 : Blo 868566 1306331 := bstep (se 1 (by rfl) ⟨979748, by rfl⟩ : syracuseStep 1306331 = 1959497) B1959497
theorem B1765217 : Blo 868566 1765217 := bstep (se 2 (by rfl) ⟨661956, by rfl⟩ : syracuseStep 1765217 = 1323913) B1323913
theorem B1306601 : Blo 868566 1306601 := bstep (se 2 (by rfl) ⟨489975, by rfl⟩ : syracuseStep 1306601 = 979951) B979951
theorem B1306619 : Blo 868566 1306619 := bstep (se 1 (by rfl) ⟨979964, by rfl⟩ : syracuseStep 1306619 = 1959929) B1959929
theorem B1306655 : Blo 868566 1306655 := bstep (se 1 (by rfl) ⟨979991, by rfl⟩ : syracuseStep 1306655 = 1959983) B1959983
theorem B1306679 : Blo 868566 1306679 := bstep (se 1 (by rfl) ⟨980009, by rfl⟩ : syracuseStep 1306679 = 1960019) B1960019
theorem B1306799 : Blo 868566 1306799 := bstep (se 1 (by rfl) ⟨980099, by rfl⟩ : syracuseStep 1306799 = 1960199) B1960199
theorem B1470791 : Blo 868566 1470791 := bstep (se 1 (by rfl) ⟨1103093, by rfl⟩ : syracuseStep 1470791 = 2206187) B2206187
theorem B1175887 : Blo 868566 1175887 := bstep (se 1 (by rfl) ⟨881915, by rfl⟩ : syracuseStep 1175887 = 1763831) B1763831
theorem B1307003 : Blo 868566 1307003 := bstep (se 1 (by rfl) ⟨980252, by rfl⟩ : syracuseStep 1307003 = 1960505) B1960505
theorem B35680769 : Blo 868566 35680769 := bstep (se 2 (by rfl) ⟨13380288, by rfl⟩ : syracuseStep 35680769 = 26760577) B26760577
theorem B1307273 : Blo 868566 1307273 := bstep (se 2 (by rfl) ⟨490227, by rfl⟩ : syracuseStep 1307273 = 980455) B980455
theorem B5305115 : Blo 868566 5305115 := bstep (se 1 (by rfl) ⟨3978836, by rfl⟩ : syracuseStep 5305115 = 7957673) B7957673
theorem B1307483 : Blo 868566 1307483 := bstep (se 1 (by rfl) ⟨980612, by rfl⟩ : syracuseStep 1307483 = 1961225) B1961225
theorem B1307513 : Blo 868566 1307513 := bstep (se 2 (by rfl) ⟨490317, by rfl⟩ : syracuseStep 1307513 = 980635) B980635
theorem B2094049 : Blo 868566 2094049 := bstep (se 2 (by rfl) ⟨785268, by rfl⟩ : syracuseStep 2094049 = 1570537) B1570537
theorem B2356271 : Blo 868566 2356271 := bstep (se 1 (by rfl) ⟨1767203, by rfl⟩ : syracuseStep 2356271 = 3534407) B3534407
theorem B42857551 : Blo 868566 42857551 := bstep (se 1 (by rfl) ⟨32143163, by rfl⟩ : syracuseStep 42857551 = 64286327) B64286327
theorem B2356391 : Blo 868566 2356391 := bstep (se 1 (by rfl) ⟨1767293, by rfl⟩ : syracuseStep 2356391 = 3534587) B3534587
theorem B1308143 : Blo 868566 1308143 := bstep (se 1 (by rfl) ⟨981107, by rfl⟩ : syracuseStep 1308143 = 1962215) B1962215
theorem B11138633 : Blo 868566 11138633 := bstep (se 2 (by rfl) ⟨4176987, by rfl⟩ : syracuseStep 11138633 = 8353975) B8353975
theorem B1308263 : Blo 868566 1308263 := bstep (se 1 (by rfl) ⟨981197, by rfl⟩ : syracuseStep 1308263 = 1962395) B1962395
theorem B980959 : Blo 868566 980959 := bstep (se 1 (by rfl) ⟨735719, by rfl⟩ : syracuseStep 980959 = 1471439) B1471439
theorem B1308719 : Blo 868566 1308719 := bstep (se 1 (by rfl) ⟨981539, by rfl⟩ : syracuseStep 1308719 = 1963079) B1963079
theorem B3537017 : Blo 868566 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1308839 : Blo 868566 1308839 := bstep (se 1 (by rfl) ⟨981629, by rfl⟩ : syracuseStep 1308839 = 1963259) B1963259
theorem B2095415 : Blo 868566 2095415 := bstep (se 1 (by rfl) ⟨1571561, by rfl⟩ : syracuseStep 2095415 = 3143123) B3143123
theorem B36174437 : Blo 868566 36174437 := bstep (se 4 (by rfl) ⟨3391353, by rfl⟩ : syracuseStep 36174437 = 6782707) B6782707
theorem B7044191 : Blo 868566 7044191 := bstep (se 1 (by rfl) ⟨5283143, by rfl⟩ : syracuseStep 7044191 = 10566287) B10566287
theorem B1048043 : Blo 868566 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B8355707 : Blo 868566 8355707 := bstep (se 1 (by rfl) ⟨6266780, by rfl⟩ : syracuseStep 8355707 = 12533561) B12533561
theorem B2981843 : Blo 868566 2981843 := bstep (se 1 (by rfl) ⟨2236382, by rfl⟩ : syracuseStep 2981843 = 4472765) B4472765
theorem B21168377 : Blo 868566 21168377 := bstep (se 2 (by rfl) ⟨7938141, by rfl⟩ : syracuseStep 21168377 = 15876283) B15876283
theorem B9928979 : Blo 868566 9928979 := bstep (se 1 (by rfl) ⟨7446734, by rfl⟩ : syracuseStep 9928979 = 14893469) B14893469
theorem B5439791 : Blo 868566 5439791 := bstep (se 1 (by rfl) ⟨4079843, by rfl⟩ : syracuseStep 5439791 = 8159687) B8159687
theorem B3310267 : Blo 868566 3310267 := bstep (se 1 (by rfl) ⟨2482700, by rfl⟩ : syracuseStep 3310267 = 4965401) B4965401
theorem B5014399 : Blo 868566 5014399 := bstep (se 1 (by rfl) ⟨3760799, by rfl⟩ : syracuseStep 5014399 = 7521599) B7521599
theorem B11175023 : Blo 868566 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B5572111 : Blo 868566 5572111 := bstep (se 1 (by rfl) ⟨4179083, by rfl⟩ : syracuseStep 5572111 = 8358167) B8358167
theorem B6620777 : Blo 868566 6620777 := bstep (se 2 (by rfl) ⟨2482791, by rfl⟩ : syracuseStep 6620777 = 4965583) B4965583
theorem B3311225 : Blo 868566 3311225 := bstep (se 2 (by rfl) ⟨1241709, by rfl⟩ : syracuseStep 3311225 = 2483419) B2483419
theorem B23858225 : Blo 868566 23858225 := bstep (se 2 (by rfl) ⟨8946834, by rfl⟩ : syracuseStep 23858225 = 17893669) B17893669
theorem B6622721 : Blo 868566 6622721 := bstep (se 2 (by rfl) ⟨2483520, by rfl⟩ : syracuseStep 6622721 = 4967041) B4967041
theorem B3968855 : Blo 868566 3968855 := bstep (se 1 (by rfl) ⟨2976641, by rfl⟩ : syracuseStep 3968855 = 5953283) B5953283
theorem B6262771 : Blo 868566 6262771 := bstep (se 1 (by rfl) ⟨4697078, by rfl⟩ : syracuseStep 6262771 = 9394157) B9394157
theorem B7444001 : Blo 868566 7444001 := bstep (se 2 (by rfl) ⟨2791500, by rfl⟩ : syracuseStep 7444001 = 5583001) B5583001
theorem B8361893 : Blo 868566 8361893 := bstep (se 4 (by rfl) ⟨783927, by rfl⟩ : syracuseStep 8361893 = 1567855) B1567855
theorem B2792065 : Blo 868566 2792065 := bstep (se 2 (by rfl) ⟨1047024, by rfl⟩ : syracuseStep 2792065 = 2094049) B2094049
theorem B2202785 : Blo 868566 2202785 := bstep (se 2 (by rfl) ⟨826044, by rfl⟩ : syracuseStep 2202785 = 1652089) B1652089
theorem B4398623 : Blo 868566 4398623 := bstep (se 1 (by rfl) ⟨3298967, by rfl⟩ : syracuseStep 4398623 = 6597935) B6597935
theorem B3350813 : Blo 868566 3350813 := bstep (se 3 (by rfl) ⟨628277, by rfl⟩ : syracuseStep 3350813 = 1256555) B1256555
theorem B991903 : Blo 868566 991903 := bstep (se 1 (by rfl) ⟨743927, by rfl⟩ : syracuseStep 991903 = 1487855) B1487855
theorem B8463485 : Blo 868566 8463485 := bstep (se 3 (by rfl) ⟨1586903, by rfl⟩ : syracuseStep 8463485 = 3173807) B3173807
theorem B2794781 : Blo 868566 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B25110587 : Blo 868566 25110587 := bstep (se 1 (by rfl) ⟨18832940, by rfl⟩ : syracuseStep 25110587 = 37665881) B37665881
theorem B4696127 : Blo 868566 4696127 := bstep (se 1 (by rfl) ⟨3522095, by rfl⟩ : syracuseStep 4696127 = 7044191) B7044191
theorem B1648937 : Blo 868566 1648937 := bstep (se 2 (by rfl) ⟨618351, by rfl⟩ : syracuseStep 1648937 = 1236703) B1236703
theorem B1649659 : Blo 868566 1649659 := bstep (se 1 (by rfl) ⟨1237244, by rfl⟩ : syracuseStep 1649659 = 2474489) B2474489
theorem B3976553 : Blo 868566 3976553 := bstep (se 2 (by rfl) ⟨1491207, by rfl⟩ : syracuseStep 3976553 = 2982415) B2982415
theorem B144748129 : Blo 868566 144748129 := bstep (se 2 (by rfl) ⟨54280548, by rfl⟩ : syracuseStep 144748129 = 108561097) B108561097
theorem B14135087 : Blo 868566 14135087 := bstep (se 1 (by rfl) ⟨10601315, by rfl⟩ : syracuseStep 14135087 = 21202631) B21202631
theorem B2207807 : Blo 868566 2207807 := bstep (se 1 (by rfl) ⟨1655855, by rfl⟩ : syracuseStep 2207807 = 3311711) B3311711
theorem B4534379 : Blo 868566 4534379 := bstep (se 1 (by rfl) ⟨3400784, by rfl⟩ : syracuseStep 4534379 = 6801569) B6801569
theorem B24785189 : Blo 868566 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B9908567 : Blo 868566 9908567 := bstep (se 1 (by rfl) ⟨7431425, by rfl⟩ : syracuseStep 9908567 = 14862851) B14862851
theorem B4403645 : Blo 868566 4403645 := bstep (se 3 (by rfl) ⟨825683, by rfl⟩ : syracuseStep 4403645 = 1651367) B1651367
theorem B1651337 : Blo 868566 1651337 := bstep (se 2 (by rfl) ⟨619251, by rfl⟩ : syracuseStep 1651337 = 1238503) B1238503
theorem B5355005 : Blo 868566 5355005 := bstep (se 3 (by rfl) ⟨1004063, by rfl⟩ : syracuseStep 5355005 = 2008127) B2008127
theorem B14136905 : Blo 868566 14136905 := bstep (se 2 (by rfl) ⟨5301339, by rfl⟩ : syracuseStep 14136905 = 10602679) B10602679
theorem B11155751 : Blo 868566 11155751 := bstep (se 1 (by rfl) ⟨8366813, by rfl⟩ : syracuseStep 11155751 = 16733627) B16733627
theorem B1489279 : Blo 868566 1489279 := bstep (se 1 (by rfl) ⟨1116959, by rfl⟩ : syracuseStep 1489279 = 2233919) B2233919
theorem B4405751 : Blo 868566 4405751 := bstep (se 1 (by rfl) ⟨3304313, by rfl⟩ : syracuseStep 4405751 = 6608627) B6608627
theorem B868603 : Blo 868566 868603 := bstep (se 1 (by rfl) ⟨651452, by rfl⟩ : syracuseStep 868603 = 1302905) B1302905
theorem B813810037 : Blo 868566 813810037 := bstep (se 5 (by rfl) ⟨38147345, by rfl⟩ : syracuseStep 813810037 = 76294691) B76294691
theorem B228573605 : Blo 868566 228573605 := bstep (se 4 (by rfl) ⟨21428775, by rfl⟩ : syracuseStep 228573605 = 42857551) B42857551
theorem B15057323 : Blo 868566 15057323 := bstep (se 1 (by rfl) ⟨11292992, by rfl⟩ : syracuseStep 15057323 = 22585985) B22585985
theorem B868799 : Blo 868566 868799 := bstep (se 1 (by rfl) ⟨651599, by rfl⟩ : syracuseStep 868799 = 1303199) B1303199
theorem B869023 : Blo 868566 869023 := bstep (se 1 (by rfl) ⟨651767, by rfl⟩ : syracuseStep 869023 = 1303535) B1303535
theorem B869095 : Blo 868566 869095 := bstep (se 1 (by rfl) ⟨651821, by rfl⟩ : syracuseStep 869095 = 1303643) B1303643
theorem B869103 : Blo 868566 869103 := bstep (se 1 (by rfl) ⟨651827, by rfl⟩ : syracuseStep 869103 = 1303655) B1303655
theorem B869191 : Blo 868566 869191 := bstep (se 1 (by rfl) ⟨651893, by rfl⟩ : syracuseStep 869191 = 1303787) B1303787
theorem B3720019 : Blo 868566 3720019 := bstep (se 1 (by rfl) ⟨2790014, by rfl⟩ : syracuseStep 3720019 = 5580029) B5580029
theorem B869279 : Blo 868566 869279 := bstep (se 1 (by rfl) ⟨651959, by rfl⟩ : syracuseStep 869279 = 1303919) B1303919
theorem B1655711 : Blo 868566 1655711 := bstep (se 1 (by rfl) ⟨1241783, by rfl⟩ : syracuseStep 1655711 = 2483567) B2483567
theorem B869359 : Blo 868566 869359 := bstep (se 1 (by rfl) ⟨652019, by rfl⟩ : syracuseStep 869359 = 1304039) B1304039
theorem B869447 : Blo 868566 869447 := bstep (se 1 (by rfl) ⟨652085, by rfl⟩ : syracuseStep 869447 = 1304171) B1304171
theorem B869479 : Blo 868566 869479 := bstep (se 1 (by rfl) ⟨652109, by rfl⟩ : syracuseStep 869479 = 1304219) B1304219
theorem B869627 : Blo 868566 869627 := bstep (se 1 (by rfl) ⟨652220, by rfl⟩ : syracuseStep 869627 = 1304441) B1304441
theorem B870127 : Blo 868566 870127 := bstep (se 1 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 870127 = 1305191) B1305191
theorem B7948151 : Blo 868566 7948151 := bstep (se 1 (by rfl) ⟨5961113, by rfl⟩ : syracuseStep 7948151 = 11922227) B11922227
theorem B870311 : Blo 868566 870311 := bstep (se 1 (by rfl) ⟨652733, by rfl⟩ : syracuseStep 870311 = 1305467) B1305467
theorem B870491 : Blo 868566 870491 := bstep (se 1 (by rfl) ⟨652868, by rfl⟩ : syracuseStep 870491 = 1305737) B1305737
theorem B870527 : Blo 868566 870527 := bstep (se 1 (by rfl) ⟨652895, by rfl⟩ : syracuseStep 870527 = 1305791) B1305791
theorem B2935007 : Blo 868566 2935007 := bstep (se 1 (by rfl) ⟨2201255, by rfl⟩ : syracuseStep 2935007 = 4402511) B4402511
theorem B3131617 : Blo 868566 3131617 := bstep (se 2 (by rfl) ⟨1174356, by rfl⟩ : syracuseStep 3131617 = 2348713) B2348713
theorem B870887 : Blo 868566 870887 := bstep (se 1 (by rfl) ⟨653165, by rfl⟩ : syracuseStep 870887 = 1306331) B1306331
theorem B871067 : Blo 868566 871067 := bstep (se 1 (by rfl) ⟨653300, by rfl⟩ : syracuseStep 871067 = 1306601) B1306601
theorem B871079 : Blo 868566 871079 := bstep (se 1 (by rfl) ⟨653309, by rfl⟩ : syracuseStep 871079 = 1306619) B1306619
theorem B871103 : Blo 868566 871103 := bstep (se 1 (by rfl) ⟨653327, by rfl⟩ : syracuseStep 871103 = 1306655) B1306655
theorem B4180679 : Blo 868566 4180679 := bstep (se 1 (by rfl) ⟨3135509, by rfl⟩ : syracuseStep 4180679 = 6271019) B6271019
theorem B871119 : Blo 868566 871119 := bstep (se 1 (by rfl) ⟨653339, by rfl⟩ : syracuseStep 871119 = 1306679) B1306679
theorem B871199 : Blo 868566 871199 := bstep (se 1 (by rfl) ⟨653399, by rfl⟩ : syracuseStep 871199 = 1306799) B1306799
theorem B871335 : Blo 868566 871335 := bstep (se 1 (by rfl) ⟨653501, by rfl⟩ : syracuseStep 871335 = 1307003) B1307003
theorem B3525599 : Blo 868566 3525599 := bstep (se 1 (by rfl) ⟨2644199, by rfl⟩ : syracuseStep 3525599 = 5288399) B5288399
theorem B871515 : Blo 868566 871515 := bstep (se 1 (by rfl) ⟨653636, by rfl⟩ : syracuseStep 871515 = 1307273) B1307273
theorem B28232803 : Blo 868566 28232803 := bstep (se 1 (by rfl) ⟨21174602, by rfl⟩ : syracuseStep 28232803 = 42349205) B42349205
theorem B2936033 : Blo 868566 2936033 := bstep (se 2 (by rfl) ⟨1101012, by rfl⟩ : syracuseStep 2936033 = 2202025) B2202025
theorem B871655 : Blo 868566 871655 := bstep (se 1 (by rfl) ⟨653741, by rfl⟩ : syracuseStep 871655 = 1307483) B1307483
theorem B871675 : Blo 868566 871675 := bstep (se 1 (by rfl) ⟨653756, by rfl⟩ : syracuseStep 871675 = 1307513) B1307513
theorem B3132701 : Blo 868566 3132701 := bstep (se 3 (by rfl) ⟨587381, by rfl⟩ : syracuseStep 3132701 = 1174763) B1174763
theorem B3722719 : Blo 868566 3722719 := bstep (se 1 (by rfl) ⟨2792039, by rfl⟩ : syracuseStep 3722719 = 5584079) B5584079
theorem B872095 : Blo 868566 872095 := bstep (se 1 (by rfl) ⟨654071, by rfl⟩ : syracuseStep 872095 = 1308143) B1308143
theorem B7425755 : Blo 868566 7425755 := bstep (se 1 (by rfl) ⟨5569316, by rfl⟩ : syracuseStep 7425755 = 11138633) B11138633
theorem B872175 : Blo 868566 872175 := bstep (se 1 (by rfl) ⟨654131, by rfl⟩ : syracuseStep 872175 = 1308263) B1308263
theorem B872479 : Blo 868566 872479 := bstep (se 1 (by rfl) ⟨654359, by rfl⟩ : syracuseStep 872479 = 1308719) B1308719
theorem B872559 : Blo 868566 872559 := bstep (se 1 (by rfl) ⟨654419, by rfl⟩ : syracuseStep 872559 = 1308839) B1308839
theorem B157012111 : Blo 868566 157012111 := bstep (se 1 (by rfl) ⟨117759083, by rfl⟩ : syracuseStep 157012111 = 235518167) B235518167
theorem B1396943 : Blo 868566 1396943 := bstep (se 1 (by rfl) ⟨1047707, by rfl⟩ : syracuseStep 1396943 = 2095415) B2095415
theorem B8376655 : Blo 868566 8376655 := bstep (se 1 (by rfl) ⟨6282491, by rfl⟩ : syracuseStep 8376655 = 12564983) B12564983
theorem B7066379 : Blo 868566 7066379 := bstep (se 1 (by rfl) ⟨5299784, by rfl⟩ : syracuseStep 7066379 = 10599569) B10599569
theorem B7066505 : Blo 868566 7066505 := bstep (se 2 (by rfl) ⟨2649939, by rfl⟩ : syracuseStep 7066505 = 5299879) B5299879
theorem B1987895 : Blo 868566 1987895 := bstep (se 1 (by rfl) ⟨1490921, by rfl⟩ : syracuseStep 1987895 = 2981843) B2981843
theorem B2413999 : Blo 868566 2413999 := bstep (se 1 (by rfl) ⟨1810499, by rfl⟩ : syracuseStep 2413999 = 3620999) B3620999
theorem B1955519 : Blo 868566 1955519 := bstep (se 1 (by rfl) ⟨1466639, by rfl⟩ : syracuseStep 1955519 = 2933279) B2933279
theorem B2643995 : Blo 868566 2643995 := bstep (se 1 (by rfl) ⟨1982996, by rfl⟩ : syracuseStep 2643995 = 3965993) B3965993
theorem B1857583 : Blo 868566 1857583 := bstep (se 1 (by rfl) ⟨1393187, by rfl⟩ : syracuseStep 1857583 = 2786375) B2786375
theorem B7428145 : Blo 868566 7428145 := bstep (se 2 (by rfl) ⟨2785554, by rfl⟩ : syracuseStep 7428145 = 5571109) B5571109
theorem B2480377 : Blo 868566 2480377 := bstep (se 2 (by rfl) ⟨930141, by rfl⟩ : syracuseStep 2480377 = 1860283) B1860283
theorem B4414175 : Blo 868566 4414175 := bstep (se 1 (by rfl) ⟨3310631, by rfl⟩ : syracuseStep 4414175 = 6621263) B6621263
theorem B3136319 : Blo 868566 3136319 := bstep (se 1 (by rfl) ⟨2352239, by rfl⟩ : syracuseStep 3136319 = 4704479) B4704479
theorem B1858643 : Blo 868566 1858643 := bstep (se 1 (by rfl) ⟨1393982, by rfl⟩ : syracuseStep 1858643 = 2787965) B2787965
theorem B14146973 : Blo 868566 14146973 := bstep (se 3 (by rfl) ⟨2652557, by rfl⟩ : syracuseStep 14146973 = 5305115) B5305115
theorem B2088551 : Blo 868566 2088551 := bstep (se 1 (by rfl) ⟨1566413, by rfl⟩ : syracuseStep 2088551 = 3132827) B3132827
theorem B3727043 : Blo 868566 3727043 := bstep (se 1 (by rfl) ⟨2795282, by rfl⟩ : syracuseStep 3727043 = 5590565) B5590565
theorem B107306795 : Blo 868566 107306795 := bstep (se 1 (by rfl) ⟨80480096, by rfl⟩ : syracuseStep 107306795 = 160960193) B160960193
theorem B1957769 : Blo 868566 1957769 := bstep (se 2 (by rfl) ⟨734163, by rfl⟩ : syracuseStep 1957769 = 1468327) B1468327
theorem B1466471 : Blo 868566 1466471 := bstep (se 1 (by rfl) ⟨1099853, by rfl⟩ : syracuseStep 1466471 = 2199707) B2199707
theorem B1303151 : Blo 868566 1303151 := bstep (se 1 (by rfl) ⟨977363, by rfl⟩ : syracuseStep 1303151 = 1954727) B1954727
theorem B2941757 : Blo 868566 2941757 := bstep (se 3 (by rfl) ⟨551579, by rfl⟩ : syracuseStep 2941757 = 1103159) B1103159
theorem B1958777 : Blo 868566 1958777 := bstep (se 2 (by rfl) ⟨734541, by rfl⟩ : syracuseStep 1958777 = 1469083) B1469083
theorem B2483065 : Blo 868566 2483065 := bstep (se 2 (by rfl) ⟨931149, by rfl⟩ : syracuseStep 2483065 = 1862299) B1862299
theorem B14902217 : Blo 868566 14902217 := bstep (se 2 (by rfl) ⟨5588331, by rfl⟩ : syracuseStep 14902217 = 11176663) B11176663
theorem B3138593 : Blo 868566 3138593 := bstep (se 2 (by rfl) ⟨1176972, by rfl⟩ : syracuseStep 3138593 = 2353945) B2353945
theorem B1467463 : Blo 868566 1467463 := bstep (se 1 (by rfl) ⟨1100597, by rfl⟩ : syracuseStep 1467463 = 2201195) B2201195
theorem B3302491 : Blo 868566 3302491 := bstep (se 1 (by rfl) ⟨2476868, by rfl⟩ : syracuseStep 3302491 = 4953737) B4953737
theorem B1762411 : Blo 868566 1762411 := bstep (se 1 (by rfl) ⟨1321808, by rfl⟩ : syracuseStep 1762411 = 2643617) B2643617
theorem B2942945 : Blo 868566 2942945 := bstep (se 2 (by rfl) ⟨1103604, by rfl⟩ : syracuseStep 2942945 = 2207209) B2207209
theorem B5662817 : Blo 868566 5662817 := bstep (se 2 (by rfl) ⟨2123556, by rfl⟩ : syracuseStep 5662817 = 4247113) B4247113
theorem B1960073 : Blo 868566 1960073 := bstep (se 2 (by rfl) ⟨735027, by rfl⟩ : syracuseStep 1960073 = 1470055) B1470055
theorem B1304795 : Blo 868566 1304795 := bstep (se 1 (by rfl) ⟨978596, by rfl⟩ : syracuseStep 1304795 = 1957193) B1957193
theorem B1304807 : Blo 868566 1304807 := bstep (se 1 (by rfl) ⟨978605, by rfl⟩ : syracuseStep 1304807 = 1957211) B1957211
theorem B1239295 : Blo 868566 1239295 := bstep (se 1 (by rfl) ⟨929471, by rfl⟩ : syracuseStep 1239295 = 1858943) B1858943
theorem B2943755 : Blo 868566 2943755 := bstep (se 1 (by rfl) ⟨2207816, by rfl⟩ : syracuseStep 2943755 = 4415633) B4415633
theorem B3304223 : Blo 868566 3304223 := bstep (se 1 (by rfl) ⟨2478167, by rfl⟩ : syracuseStep 3304223 = 4956335) B4956335
theorem B1960775 : Blo 868566 1960775 := bstep (se 1 (by rfl) ⟨1470581, by rfl⟩ : syracuseStep 1960775 = 2941163) B2941163
theorem B1305455 : Blo 868566 1305455 := bstep (se 1 (by rfl) ⟨979091, by rfl⟩ : syracuseStep 1305455 = 1958183) B1958183
theorem B1305695 : Blo 868566 1305695 := bstep (se 1 (by rfl) ⟨979271, by rfl⟩ : syracuseStep 1305695 = 1958543) B1958543
theorem B1567849 : Blo 868566 1567849 := bstep (se 2 (by rfl) ⟨587943, by rfl⟩ : syracuseStep 1567849 = 1175887) B1175887
theorem B1305707 : Blo 868566 1305707 := bstep (se 1 (by rfl) ⟨979280, by rfl⟩ : syracuseStep 1305707 = 1958561) B1958561
theorem B1305755 : Blo 868566 1305755 := bstep (se 1 (by rfl) ⟨979316, by rfl⟩ : syracuseStep 1305755 = 1958633) B1958633
theorem B1305947 : Blo 868566 1305947 := bstep (se 1 (by rfl) ⟨979460, by rfl⟩ : syracuseStep 1305947 = 1958921) B1958921
theorem B5565833 : Blo 868566 5565833 := bstep (se 2 (by rfl) ⟨2087187, by rfl⟩ : syracuseStep 5565833 = 4174375) B4174375
theorem B2649505 : Blo 868566 2649505 := bstep (se 2 (by rfl) ⟨993564, by rfl⟩ : syracuseStep 2649505 = 1987129) B1987129
theorem B1863137 : Blo 868566 1863137 := bstep (se 2 (by rfl) ⟨698676, by rfl⟩ : syracuseStep 1863137 = 1397353) B1397353
theorem B1306139 : Blo 868566 1306139 := bstep (se 1 (by rfl) ⟨979604, by rfl⟩ : syracuseStep 1306139 = 1959209) B1959209
theorem B1470089 : Blo 868566 1470089 := bstep (se 2 (by rfl) ⟨551283, by rfl⟩ : syracuseStep 1470089 = 1102567) B1102567
theorem B1470143 : Blo 868566 1470143 := bstep (se 1 (by rfl) ⟨1102607, by rfl⟩ : syracuseStep 1470143 = 2205215) B2205215
theorem B1306319 : Blo 868566 1306319 := bstep (se 1 (by rfl) ⟨979739, by rfl⟩ : syracuseStep 1306319 = 1959479) B1959479
theorem B31747895 : Blo 868566 31747895 := bstep (se 1 (by rfl) ⟨23810921, by rfl⟩ : syracuseStep 31747895 = 47621843) B47621843
theorem B1306559 : Blo 868566 1306559 := bstep (se 1 (by rfl) ⟨979919, by rfl⟩ : syracuseStep 1306559 = 1959839) B1959839
theorem B1306607 : Blo 868566 1306607 := bstep (se 1 (by rfl) ⟨979955, by rfl⟩ : syracuseStep 1306607 = 1959911) B1959911
theorem B1306727 : Blo 868566 1306727 := bstep (se 1 (by rfl) ⟨980045, by rfl⟩ : syracuseStep 1306727 = 1960091) B1960091
theorem B1306847 : Blo 868566 1306847 := bstep (se 1 (by rfl) ⟨980135, by rfl⟩ : syracuseStep 1306847 = 1960271) B1960271
theorem B1306907 : Blo 868566 1306907 := bstep (se 1 (by rfl) ⟨980180, by rfl⟩ : syracuseStep 1306907 = 1960361) B1960361
theorem B979483 : Blo 868566 979483 := bstep (se 1 (by rfl) ⟨734612, by rfl⟩ : syracuseStep 979483 = 1469225) B1469225
theorem B8352359 : Blo 868566 8352359 := bstep (se 1 (by rfl) ⟨6264269, by rfl⟩ : syracuseStep 8352359 = 12528539) B12528539
theorem B1962683 : Blo 868566 1962683 := bstep (se 1 (by rfl) ⟨1472012, by rfl⟩ : syracuseStep 1962683 = 2944025) B2944025
theorem B979663 : Blo 868566 979663 := bstep (se 1 (by rfl) ⟨734747, by rfl⟩ : syracuseStep 979663 = 1469495) B1469495
theorem B3306379 : Blo 868566 3306379 := bstep (se 1 (by rfl) ⟨2479784, by rfl⟩ : syracuseStep 3306379 = 4959569) B4959569
theorem B1176811 : Blo 868566 1176811 := bstep (se 1 (by rfl) ⟨882608, by rfl⟩ : syracuseStep 1176811 = 1765217) B1765217
theorem B1307945 : Blo 868566 1307945 := bstep (se 2 (by rfl) ⟨490479, by rfl⟩ : syracuseStep 1307945 = 980959) B980959
theorem B1471999 : Blo 868566 1471999 := bstep (se 1 (by rfl) ⟨1103999, by rfl⟩ : syracuseStep 1471999 = 2207999) B2207999
theorem B980527 : Blo 868566 980527 := bstep (se 1 (by rfl) ⟨735395, by rfl⟩ : syracuseStep 980527 = 1470791) B1470791
theorem B23787179 : Blo 868566 23787179 := bstep (se 1 (by rfl) ⟨17840384, by rfl⟩ : syracuseStep 23787179 = 35680769) B35680769
theorem B1472377 : Blo 868566 1472377 := bstep (se 2 (by rfl) ⟨552141, by rfl⟩ : syracuseStep 1472377 = 1104283) B1104283
theorem B1570847 : Blo 868566 1570847 := bstep (se 1 (by rfl) ⟨1178135, by rfl⟩ : syracuseStep 1570847 = 2356271) B2356271
theorem B1570927 : Blo 868566 1570927 := bstep (se 1 (by rfl) ⟨1178195, by rfl⟩ : syracuseStep 1570927 = 2356391) B2356391
theorem B2358011 : Blo 868566 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B24116291 : Blo 868566 24116291 := bstep (se 1 (by rfl) ⟨18087218, by rfl⟩ : syracuseStep 24116291 = 36174437) B36174437
theorem B17169965 : Blo 868566 17169965 := bstep (se 3 (by rfl) ⟨3219368, by rfl⟩ : syracuseStep 17169965 = 6438737) B6438737
theorem B193625977 : Blo 868566 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B5570471 : Blo 868566 5570471 := bstep (se 1 (by rfl) ⟨4177853, by rfl⟩ : syracuseStep 5570471 = 8355707) B8355707
theorem B6619319 : Blo 868566 6619319 := bstep (se 1 (by rfl) ⟨4964489, by rfl⟩ : syracuseStep 6619319 = 9928979) B9928979
theorem B1085080049 : Blo 868566 1085080049 := bstep (se 2 (by rfl) ⟨406905018, by rfl⟩ : syracuseStep 1085080049 = 813810037) B813810037
theorem B3310753 : Blo 868566 3310753 := bstep (se 2 (by rfl) ⟨1241532, by rfl⟩ : syracuseStep 3310753 = 2483065) B2483065
theorem B6685865 : Blo 868566 6685865 := bstep (se 2 (by rfl) ⟨2507199, by rfl⟩ : syracuseStep 6685865 = 5014399) B5014399
theorem B2787119 : Blo 868566 2787119 := bstep (se 1 (by rfl) ⟨2090339, by rfl⟩ : syracuseStep 2787119 = 4180679) B4180679
theorem B4950503 : Blo 868566 4950503 := bstep (se 1 (by rfl) ⟨3712877, by rfl⟩ : syracuseStep 4950503 = 7425755) B7425755
theorem B5574595 : Blo 868566 5574595 := bstep (se 1 (by rfl) ⟨4180946, by rfl⟩ : syracuseStep 5574595 = 8361893) B8361893
theorem B2199545 : Blo 868566 2199545 := bstep (se 2 (by rfl) ⟨824829, by rfl⟩ : syracuseStep 2199545 = 1649659) B1649659
theorem B71537863 : Blo 868566 71537863 := bstep (se 1 (by rfl) ⟨53653397, by rfl⟩ : syracuseStep 71537863 = 107306795) B107306795
theorem B9934811 : Blo 868566 9934811 := bstep (se 1 (by rfl) ⟨7451108, by rfl⟩ : syracuseStep 9934811 = 14902217) B14902217
theorem B4397165 : Blo 868566 4397165 := bstep (se 3 (by rfl) ⟨824468, by rfl⟩ : syracuseStep 4397165 = 1648937) B1648937
theorem B3775211 : Blo 868566 3775211 := bstep (se 1 (by rfl) ⟨2831408, by rfl⟩ : syracuseStep 3775211 = 5662817) B5662817
theorem B2202815 : Blo 868566 2202815 := bstep (se 1 (by rfl) ⟨1652111, by rfl⟩ : syracuseStep 2202815 = 3304223) B3304223
theorem B3218665 : Blo 868566 3218665 := bstep (se 2 (by rfl) ⟨1206999, by rfl⟩ : syracuseStep 3218665 = 2413999) B2413999
theorem B3710555 : Blo 868566 3710555 := bstep (se 1 (by rfl) ⟨2782916, by rfl⟩ : syracuseStep 3710555 = 5565833) B5565833
theorem B9904193 : Blo 868566 9904193 := bstep (se 2 (by rfl) ⟨3714072, by rfl⟩ : syracuseStep 9904193 = 7428145) B7428145
theorem B3022919 : Blo 868566 3022919 := bstep (se 1 (by rfl) ⟨2267189, by rfl⟩ : syracuseStep 3022919 = 4534379) B4534379
theorem B16523459 : Blo 868566 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B11446643 : Blo 868566 11446643 := bstep (se 1 (by rfl) ⟨8584982, by rfl⟩ : syracuseStep 11446643 = 17169965) B17169965
theorem B3713647 : Blo 868566 3713647 := bstep (se 1 (by rfl) ⟨2785235, by rfl⟩ : syracuseStep 3713647 = 5570471) B5570471
theorem B9907109 : Blo 868566 9907109 := bstep (se 4 (by rfl) ⟨928791, by rfl⟩ : syracuseStep 9907109 = 1857583) B1857583
theorem B152382403 : Blo 868566 152382403 := bstep (se 1 (by rfl) ⟨114286802, by rfl⟩ : syracuseStep 152382403 = 228573605) B228573605
theorem B10038215 : Blo 868566 10038215 := bstep (se 1 (by rfl) ⟨7528661, by rfl⟩ : syracuseStep 10038215 = 15057323) B15057323
theorem B7450015 : Blo 868566 7450015 := bstep (se 1 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 7450015 = 11175023) B11175023
theorem B837397925 : Blo 868566 837397925 := bstep (se 4 (by rfl) ⟨78506055, by rfl⟩ : syracuseStep 837397925 = 157012111) B157012111
theorem B1322537 : Blo 868566 1322537 := bstep (se 2 (by rfl) ⟨495951, by rfl⟩ : syracuseStep 1322537 = 991903) B991903
theorem B2207483 : Blo 868566 2207483 := bstep (se 1 (by rfl) ⟨1655612, by rfl⟩ : syracuseStep 2207483 = 3311225) B3311225
theorem B4960025 : Blo 868566 4960025 := bstep (se 2 (by rfl) ⟨1860009, by rfl⟩ : syracuseStep 4960025 = 3720019) B3720019
theorem B4403321 : Blo 868566 4403321 := bstep (se 2 (by rfl) ⟨1651245, by rfl⟩ : syracuseStep 4403321 = 3302491) B3302491
theorem B15905483 : Blo 868566 15905483 := bstep (se 1 (by rfl) ⟨11929112, by rfl⟩ : syracuseStep 15905483 = 23858225) B23858225
theorem B8369581 : Blo 868566 8369581 := bstep (se 3 (by rfl) ⟨1569296, by rfl⟩ : syracuseStep 8369581 = 3138593) B3138593
theorem B931295 : Blo 868566 931295 := bstep (se 1 (by rfl) ⟨698471, by rfl⟩ : syracuseStep 931295 = 1396943) B1396943
theorem B4175489 : Blo 868566 4175489 := bstep (se 2 (by rfl) ⟨1565808, by rfl⟩ : syracuseStep 4175489 = 3131617) B3131617
theorem B1652393 : Blo 868566 1652393 := bstep (se 2 (by rfl) ⟨619647, by rfl⟩ : syracuseStep 1652393 = 1239295) B1239295
theorem B7452749 : Blo 868566 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B1325263 : Blo 868566 1325263 := bstep (se 1 (by rfl) ⟨993947, by rfl⟩ : syracuseStep 1325263 = 1987895) B1987895
theorem B4962667 : Blo 868566 4962667 := bstep (se 1 (by rfl) ⟨3722000, by rfl⟩ : syracuseStep 4962667 = 7444001) B7444001
theorem B4963625 : Blo 868566 4963625 := bstep (se 2 (by rfl) ⟨1861359, by rfl⟩ : syracuseStep 4963625 = 3722719) B3722719
theorem B2932415 : Blo 868566 2932415 := bstep (se 1 (by rfl) ⟨2199311, by rfl⟩ : syracuseStep 2932415 = 4398623) B4398623
theorem B868767 : Blo 868566 868767 := bstep (se 1 (by rfl) ⟨651575, by rfl⟩ : syracuseStep 868767 = 1303151) B1303151
theorem B4408505 : Blo 868566 4408505 := bstep (se 2 (by rfl) ⟨1653189, by rfl⟩ : syracuseStep 4408505 = 3306379) B3306379
theorem B6276325 : Blo 868566 6276325 := bstep (se 4 (by rfl) ⟨588405, by rfl⟩ : syracuseStep 6276325 = 1176811) B1176811
theorem B3130751 : Blo 868566 3130751 := bstep (se 1 (by rfl) ⟨2348063, by rfl⟩ : syracuseStep 3130751 = 4696127) B4696127
theorem B869863 : Blo 868566 869863 := bstep (se 1 (by rfl) ⟨652397, by rfl⟩ : syracuseStep 869863 = 1304795) B1304795
theorem B869871 : Blo 868566 869871 := bstep (se 1 (by rfl) ⟨652403, by rfl⟩ : syracuseStep 869871 = 1304807) B1304807
theorem B870303 : Blo 868566 870303 := bstep (se 1 (by rfl) ⟨652727, by rfl⟩ : syracuseStep 870303 = 1305455) B1305455
theorem B870463 : Blo 868566 870463 := bstep (se 1 (by rfl) ⟨652847, by rfl⟩ : syracuseStep 870463 = 1305695) B1305695
theorem B870471 : Blo 868566 870471 := bstep (se 1 (by rfl) ⟨652853, by rfl⟩ : syracuseStep 870471 = 1305707) B1305707
theorem B870503 : Blo 868566 870503 := bstep (se 1 (by rfl) ⟨652877, by rfl⟩ : syracuseStep 870503 = 1305755) B1305755
theorem B870631 : Blo 868566 870631 := bstep (se 1 (by rfl) ⟨652973, by rfl⟩ : syracuseStep 870631 = 1305947) B1305947
theorem B870759 : Blo 868566 870759 := bstep (se 1 (by rfl) ⟨653069, by rfl⟩ : syracuseStep 870759 = 1306139) B1306139
theorem B870879 : Blo 868566 870879 := bstep (se 1 (by rfl) ⟨653159, by rfl⟩ : syracuseStep 870879 = 1306319) B1306319
theorem B9423391 : Blo 868566 9423391 := bstep (se 1 (by rfl) ⟨7067543, by rfl⟩ : syracuseStep 9423391 = 14135087) B14135087
theorem B871039 : Blo 868566 871039 := bstep (se 1 (by rfl) ⟨653279, by rfl⟩ : syracuseStep 871039 = 1306559) B1306559
theorem B871071 : Blo 868566 871071 := bstep (se 1 (by rfl) ⟨653303, by rfl⟩ : syracuseStep 871071 = 1306607) B1306607
theorem B871151 : Blo 868566 871151 := bstep (se 1 (by rfl) ⟨653363, by rfl⟩ : syracuseStep 871151 = 1306727) B1306727
theorem B871231 : Blo 868566 871231 := bstep (se 1 (by rfl) ⟨653423, by rfl⟩ : syracuseStep 871231 = 1306847) B1306847
theorem B871271 : Blo 868566 871271 := bstep (se 1 (by rfl) ⟨653453, by rfl⟩ : syracuseStep 871271 = 1306907) B1306907
theorem B6605711 : Blo 868566 6605711 := bstep (se 1 (by rfl) ⟨4954283, by rfl⟩ : syracuseStep 6605711 = 9908567) B9908567
theorem B2935763 : Blo 868566 2935763 := bstep (se 1 (by rfl) ⟨2201822, by rfl⟩ : syracuseStep 2935763 = 4403645) B4403645
theorem B1100891 : Blo 868566 1100891 := bstep (se 1 (by rfl) ⟨825668, by rfl⟩ : syracuseStep 1100891 = 1651337) B1651337
theorem B1985705 : Blo 868566 1985705 := bstep (se 2 (by rfl) ⟨744639, by rfl⟩ : syracuseStep 1985705 = 1489279) B1489279
theorem B3722753 : Blo 868566 3722753 := bstep (se 2 (by rfl) ⟨1396032, by rfl⟩ : syracuseStep 3722753 = 2792065) B2792065
theorem B871963 : Blo 868566 871963 := bstep (se 1 (by rfl) ⟨653972, by rfl⟩ : syracuseStep 871963 = 1307945) B1307945
theorem B10604141 : Blo 868566 10604141 := bstep (se 3 (by rfl) ⟨1988276, by rfl⟩ : syracuseStep 10604141 = 3976553) B3976553
theorem B9424603 : Blo 868566 9424603 := bstep (se 1 (by rfl) ⟨7068452, by rfl⟩ : syracuseStep 9424603 = 14136905) B14136905
theorem B2937167 : Blo 868566 2937167 := bstep (se 1 (by rfl) ⟨2202875, by rfl⟩ : syracuseStep 2937167 = 4405751) B4405751
theorem B16077527 : Blo 868566 16077527 := bstep (se 1 (by rfl) ⟨12058145, by rfl⟩ : syracuseStep 16077527 = 24116291) B24116291
theorem B258167969 : Blo 868566 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B14112251 : Blo 868566 14112251 := bstep (se 1 (by rfl) ⟨10584188, by rfl⟩ : syracuseStep 14112251 = 21168377) B21168377
theorem B3626527 : Blo 868566 3626527 := bstep (se 1 (by rfl) ⟨2719895, by rfl⟩ : syracuseStep 3626527 = 5439791) B5439791
theorem B1103807 : Blo 868566 1103807 := bstep (se 1 (by rfl) ⟨827855, by rfl⟩ : syracuseStep 1103807 = 1655711) B1655711
theorem B4413689 : Blo 868566 4413689 := bstep (se 2 (by rfl) ⟨1655133, by rfl⟩ : syracuseStep 4413689 = 3310267) B3310267
theorem B4413851 : Blo 868566 4413851 := bstep (se 1 (by rfl) ⟨3310388, by rfl⟩ : syracuseStep 4413851 = 6620777) B6620777
theorem B5298767 : Blo 868566 5298767 := bstep (se 1 (by rfl) ⟨3974075, by rfl⟩ : syracuseStep 5298767 = 7948151) B7948151
theorem B1956617 : Blo 868566 1956617 := bstep (se 2 (by rfl) ⟨733731, by rfl⟩ : syracuseStep 1956617 = 1467463) B1467463
theorem B2349881 : Blo 868566 2349881 := bstep (se 2 (by rfl) ⟨881205, by rfl⟩ : syracuseStep 2349881 = 1762411) B1762411
theorem B1956671 : Blo 868566 1956671 := bstep (se 1 (by rfl) ⟨1467503, by rfl⟩ : syracuseStep 1956671 = 2935007) B2935007
theorem B2350399 : Blo 868566 2350399 := bstep (se 1 (by rfl) ⟨1762799, by rfl⟩ : syracuseStep 2350399 = 3525599) B3525599
theorem B7429481 : Blo 868566 7429481 := bstep (se 2 (by rfl) ⟨2786055, by rfl⟩ : syracuseStep 7429481 = 5572111) B5572111
theorem B1957355 : Blo 868566 1957355 := bstep (se 1 (by rfl) ⟨1468016, by rfl⟩ : syracuseStep 1957355 = 2936033) B2936033
theorem B2088467 : Blo 868566 2088467 := bstep (se 1 (by rfl) ⟨1566350, by rfl⟩ : syracuseStep 2088467 = 3132701) B3132701
theorem B4415147 : Blo 868566 4415147 := bstep (se 1 (by rfl) ⟨3311360, by rfl⟩ : syracuseStep 4415147 = 6622721) B6622721
theorem B2645903 : Blo 868566 2645903 := bstep (se 1 (by rfl) ⟨1984427, by rfl⟩ : syracuseStep 2645903 = 3968855) B3968855
theorem B35742005 : Blo 868566 35742005 := bstep (se 5 (by rfl) ⟨1675406, by rfl⟩ : syracuseStep 35742005 = 3350813) B3350813
theorem B22569293 : Blo 868566 22569293 := bstep (se 3 (by rfl) ⟨4231742, by rfl⟩ : syracuseStep 22569293 = 8463485) B8463485
theorem B4710919 : Blo 868566 4710919 := bstep (se 1 (by rfl) ⟨3533189, by rfl⟩ : syracuseStep 4710919 = 7066379) B7066379
theorem B4711003 : Blo 868566 4711003 := bstep (se 1 (by rfl) ⟨3533252, by rfl⟩ : syracuseStep 4711003 = 7066505) B7066505
theorem B1303679 : Blo 868566 1303679 := bstep (se 1 (by rfl) ⟨977759, by rfl⟩ : syracuseStep 1303679 = 1955519) B1955519
theorem B14280013 : Blo 868566 14280013 := bstep (se 3 (by rfl) ⟨2677502, by rfl⟩ : syracuseStep 14280013 = 5355005) B5355005
theorem B1762663 : Blo 868566 1762663 := bstep (se 1 (by rfl) ⟨1321997, by rfl⟩ : syracuseStep 1762663 = 2643995) B2643995
theorem B37643737 : Blo 868566 37643737 := bstep (se 2 (by rfl) ⟨14116401, by rfl⟩ : syracuseStep 37643737 = 28232803) B28232803
theorem B2090465 : Blo 868566 2090465 := bstep (se 2 (by rfl) ⟨783924, by rfl⟩ : syracuseStep 2090465 = 1567849) B1567849
theorem B2942783 : Blo 868566 2942783 := bstep (se 1 (by rfl) ⟨2207087, by rfl⟩ : syracuseStep 2942783 = 4414175) B4414175
theorem B2090879 : Blo 868566 2090879 := bstep (se 1 (by rfl) ⟨1568159, by rfl⟩ : syracuseStep 2090879 = 3136319) B3136319
theorem B3532673 : Blo 868566 3532673 := bstep (se 2 (by rfl) ⟨1324752, by rfl⟩ : syracuseStep 3532673 = 2649505) B2649505
theorem B1239095 : Blo 868566 1239095 := bstep (se 1 (by rfl) ⟨929321, by rfl⟩ : syracuseStep 1239095 = 1858643) B1858643
theorem B1468523 : Blo 868566 1468523 := bstep (se 1 (by rfl) ⟨1101392, by rfl⟩ : syracuseStep 1468523 = 2202785) B2202785
theorem B192997505 : Blo 868566 192997505 := bstep (se 2 (by rfl) ⟨72374064, by rfl⟩ : syracuseStep 192997505 = 144748129) B144748129
theorem B9431315 : Blo 868566 9431315 := bstep (se 1 (by rfl) ⟨7073486, by rfl⟩ : syracuseStep 9431315 = 14146973) B14146973
theorem B2484695 : Blo 868566 2484695 := bstep (se 1 (by rfl) ⟨1863521, by rfl⟩ : syracuseStep 2484695 = 3727043) B3727043
theorem B1305179 : Blo 868566 1305179 := bstep (se 1 (by rfl) ⟨978884, by rfl⟩ : syracuseStep 1305179 = 1957769) B1957769
theorem B8350361 : Blo 868566 8350361 := bstep (se 2 (by rfl) ⟨3131385, by rfl⟩ : syracuseStep 8350361 = 6262771) B6262771
theorem B977647 : Blo 868566 977647 := bstep (se 1 (by rfl) ⟨733235, by rfl⟩ : syracuseStep 977647 = 1466471) B1466471
theorem B4188925 : Blo 868566 4188925 := bstep (se 3 (by rfl) ⟨785423, by rfl⟩ : syracuseStep 4188925 = 1570847) B1570847
theorem B11168873 : Blo 868566 11168873 := bstep (se 2 (by rfl) ⟨4188327, by rfl⟩ : syracuseStep 11168873 = 8376655) B8376655
theorem B1961171 : Blo 868566 1961171 := bstep (se 1 (by rfl) ⟨1470878, by rfl⟩ : syracuseStep 1961171 = 2941757) B2941757
theorem B1305851 : Blo 868566 1305851 := bstep (se 1 (by rfl) ⟨979388, by rfl⟩ : syracuseStep 1305851 = 1958777) B1958777
theorem B1305977 : Blo 868566 1305977 := bstep (se 2 (by rfl) ⟨489741, by rfl⟩ : syracuseStep 1305977 = 979483) B979483
theorem B1306217 : Blo 868566 1306217 := bstep (se 2 (by rfl) ⟨489831, by rfl⟩ : syracuseStep 1306217 = 979663) B979663
theorem B1961963 : Blo 868566 1961963 := bstep (se 1 (by rfl) ⟨1471472, by rfl⟩ : syracuseStep 1961963 = 2942945) B2942945
theorem B16740391 : Blo 868566 16740391 := bstep (se 1 (by rfl) ⟨12555293, by rfl⟩ : syracuseStep 16740391 = 25110587) B25110587
theorem B1306715 : Blo 868566 1306715 := bstep (se 1 (by rfl) ⟨980036, by rfl⟩ : syracuseStep 1306715 = 1960073) B1960073
theorem B1962503 : Blo 868566 1962503 := bstep (se 1 (by rfl) ⟨1471877, by rfl⟩ : syracuseStep 1962503 = 2943755) B2943755
theorem B1307183 : Blo 868566 1307183 := bstep (se 1 (by rfl) ⟨980387, by rfl⟩ : syracuseStep 1307183 = 1960775) B1960775
theorem B6288029 : Blo 868566 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B1962665 : Blo 868566 1962665 := bstep (se 2 (by rfl) ⟨735999, by rfl⟩ : syracuseStep 1962665 = 1471999) B1471999
theorem B1307369 : Blo 868566 1307369 := bstep (se 2 (by rfl) ⟨490263, by rfl⟩ : syracuseStep 1307369 = 980527) B980527
theorem B1242091 : Blo 868566 1242091 := bstep (se 1 (by rfl) ⟨931568, by rfl⟩ : syracuseStep 1242091 = 1863137) B1863137
theorem B980059 : Blo 868566 980059 := bstep (se 1 (by rfl) ⟨735044, by rfl⟩ : syracuseStep 980059 = 1470089) B1470089
theorem B980095 : Blo 868566 980095 := bstep (se 1 (by rfl) ⟨735071, by rfl⟩ : syracuseStep 980095 = 1470143) B1470143
theorem B1963169 : Blo 868566 1963169 := bstep (se 2 (by rfl) ⟨736188, by rfl⟩ : syracuseStep 1963169 = 1472377) B1472377
theorem B21165263 : Blo 868566 21165263 := bstep (se 1 (by rfl) ⟨15873947, by rfl⟩ : syracuseStep 21165263 = 31747895) B31747895
theorem B1471871 : Blo 868566 1471871 := bstep (se 1 (by rfl) ⟨1103903, by rfl⟩ : syracuseStep 1471871 = 2207807) B2207807
theorem B2094569 : Blo 868566 2094569 := bstep (se 2 (by rfl) ⟨785463, by rfl⟩ : syracuseStep 2094569 = 1570927) B1570927
theorem B3307169 : Blo 868566 3307169 := bstep (se 2 (by rfl) ⟨1240188, by rfl⟩ : syracuseStep 3307169 = 2480377) B2480377
theorem B5568239 : Blo 868566 5568239 := bstep (se 1 (by rfl) ⟨4176179, by rfl⟩ : syracuseStep 5568239 = 8352359) B8352359
theorem B1308455 : Blo 868566 1308455 := bstep (se 1 (by rfl) ⟨981341, by rfl⟩ : syracuseStep 1308455 = 1962683) B1962683
theorem B15858119 : Blo 868566 15858119 := bstep (se 1 (by rfl) ⟨11893589, by rfl⟩ : syracuseStep 15858119 = 23787179) B23787179
theorem B7437167 : Blo 868566 7437167 := bstep (se 1 (by rfl) ⟨5577875, by rfl⟩ : syracuseStep 7437167 = 11155751) B11155751
theorem B5569469 : Blo 868566 5569469 := bstep (se 3 (by rfl) ⟨1044275, by rfl⟩ : syracuseStep 5569469 = 2088551) B2088551
theorem B723386699 : Blo 868566 723386699 := bstep (se 1 (by rfl) ⟨542540024, by rfl⟩ : syracuseStep 723386699 = 1085080049) B1085080049
theorem B4457243 : Blo 868566 4457243 := bstep (se 1 (by rfl) ⟨3342932, by rfl⟩ : syracuseStep 4457243 = 6685865) B6685865
theorem B19040017 : Blo 868566 19040017 := bstep (se 2 (by rfl) ⟨7140006, by rfl⟩ : syracuseStep 19040017 = 14280013) B14280013
theorem B10718351 : Blo 868566 10718351 := bstep (se 1 (by rfl) ⟨8038763, by rfl⟩ : syracuseStep 10718351 = 16077527) B16077527
theorem B4951529 : Blo 868566 4951529 := bstep (se 2 (by rfl) ⟨1856823, by rfl⟩ : syracuseStep 4951529 = 3713647) B3713647
theorem B9408167 : Blo 868566 9408167 := bstep (se 1 (by rfl) ⟨7056125, by rfl⟩ : syracuseStep 9408167 = 14112251) B14112251
theorem B6623207 : Blo 868566 6623207 := bstep (se 1 (by rfl) ⟨4967405, by rfl⟩ : syracuseStep 6623207 = 9934811) B9934811
theorem B9933353 : Blo 868566 9933353 := bstep (se 2 (by rfl) ⟨3725007, by rfl⟩ : syracuseStep 9933353 = 7450015) B7450015
theorem B4952987 : Blo 868566 4952987 := bstep (se 1 (by rfl) ⟨3714740, by rfl⟩ : syracuseStep 4952987 = 7429481) B7429481
theorem B22320521 : Blo 868566 22320521 := bstep (se 2 (by rfl) ⟨8370195, by rfl⟩ : syracuseStep 22320521 = 16740391) B16740391
theorem B11015639 : Blo 868566 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B23828003 : Blo 868566 23828003 := bstep (se 1 (by rfl) ⟨17871002, by rfl⟩ : syracuseStep 23828003 = 35742005) B35742005
theorem B15046195 : Blo 868566 15046195 := bstep (se 1 (by rfl) ⟨11284646, by rfl⟩ : syracuseStep 15046195 = 22569293) B22569293
theorem B514660013 : Blo 868566 514660013 := bstep (se 3 (by rfl) ⟨96498752, by rfl⟩ : syracuseStep 514660013 = 192997505) B192997505
theorem B7445915 : Blo 868566 7445915 := bstep (se 1 (by rfl) ⟨5584436, by rfl⟩ : syracuseStep 7445915 = 11168873) B11168873
theorem B2204779 : Blo 868566 2204779 := bstep (se 1 (by rfl) ⟨1653584, by rfl⟩ : syracuseStep 2204779 = 3307169) B3307169
theorem B3712159 : Blo 868566 3712159 := bstep (se 1 (by rfl) ⟨2784119, by rfl⟩ : syracuseStep 3712159 = 5568239) B5568239
theorem B4958111 : Blo 868566 4958111 := bstep (se 1 (by rfl) ⟨3718583, by rfl⟩ : syracuseStep 4958111 = 7437167) B7437167
theorem B3712979 : Blo 868566 3712979 := bstep (se 1 (by rfl) ⟨2784734, by rfl⟩ : syracuseStep 3712979 = 5569469) B5569469
theorem B7055741 : Blo 868566 7055741 := bstep (se 3 (by rfl) ⟨1322951, by rfl⟩ : syracuseStep 7055741 = 2645903) B2645903
theorem B8368433 : Blo 868566 8368433 := bstep (se 2 (by rfl) ⟨3138162, by rfl⟩ : syracuseStep 8368433 = 6276325) B6276325
theorem B4403807 : Blo 868566 4403807 := bstep (se 1 (by rfl) ⟨3302855, by rfl⟩ : syracuseStep 4403807 = 6605711) B6605711
theorem B1323803 : Blo 868566 1323803 := bstep (se 1 (by rfl) ⟨992852, by rfl⟩ : syracuseStep 1323803 = 1985705) B1985705
theorem B12564521 : Blo 868566 12564521 := bstep (se 2 (by rfl) ⟨4711695, by rfl⟩ : syracuseStep 12564521 = 9423391) B9423391
theorem B172111979 : Blo 868566 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B5585233 : Blo 868566 5585233 := bstep (se 2 (by rfl) ⟨2094462, by rfl⟩ : syracuseStep 5585233 = 4188925) B4188925
theorem B2931443 : Blo 868566 2931443 := bstep (se 1 (by rfl) ⟨2198582, by rfl⟩ : syracuseStep 2931443 = 4397165) B4397165
theorem B12566137 : Blo 868566 12566137 := bstep (se 2 (by rfl) ⟨4712301, by rfl⟩ : syracuseStep 12566137 = 9424603) B9424603
theorem B1392311 : Blo 868566 1392311 := bstep (se 1 (by rfl) ⟨1044233, by rfl⟩ : syracuseStep 1392311 = 2088467) B2088467
theorem B2473703 : Blo 868566 2473703 := bstep (se 1 (by rfl) ⟨1855277, by rfl⟩ : syracuseStep 2473703 = 3710555) B3710555
theorem B6602795 : Blo 868566 6602795 := bstep (se 1 (by rfl) ⟨4952096, by rfl⟩ : syracuseStep 6602795 = 9904193) B9904193
theorem B2015279 : Blo 868566 2015279 := bstep (se 1 (by rfl) ⟨1511459, by rfl⟩ : syracuseStep 2015279 = 3022919) B3022919
theorem B14107061 : Blo 868566 14107061 := bstep (se 5 (by rfl) ⟨661268, by rfl⟩ : syracuseStep 14107061 = 1322537) B1322537
theorem B869119 : Blo 868566 869119 := bstep (se 1 (by rfl) ⟨651839, by rfl⟩ : syracuseStep 869119 = 1303679) B1303679
theorem B30524381 : Blo 868566 30524381 := bstep (se 3 (by rfl) ⟨5723321, by rfl⟩ : syracuseStep 30524381 = 11446643) B11446643
theorem B1393643 : Blo 868566 1393643 := bstep (se 1 (by rfl) ⟨1045232, by rfl⟩ : syracuseStep 1393643 = 2090465) B2090465
theorem B1393919 : Blo 868566 1393919 := bstep (se 1 (by rfl) ⟨1045439, by rfl⟩ : syracuseStep 1393919 = 2090879) B2090879
theorem B1656121 : Blo 868566 1656121 := bstep (se 2 (by rfl) ⟨621045, by rfl⟩ : syracuseStep 1656121 = 1242091) B1242091
theorem B1656463 : Blo 868566 1656463 := bstep (se 1 (by rfl) ⟨1242347, by rfl⟩ : syracuseStep 1656463 = 2484695) B2484695
theorem B870119 : Blo 868566 870119 := bstep (se 1 (by rfl) ⟨652589, by rfl⟩ : syracuseStep 870119 = 1305179) B1305179
theorem B11159441 : Blo 868566 11159441 := bstep (se 2 (by rfl) ⟨4184790, by rfl⟩ : syracuseStep 11159441 = 8369581) B8369581
theorem B6604739 : Blo 868566 6604739 := bstep (se 1 (by rfl) ⟨4953554, by rfl⟩ : syracuseStep 6604739 = 9907109) B9907109
theorem B4835369 : Blo 868566 4835369 := bstep (se 2 (by rfl) ⟨1813263, by rfl⟩ : syracuseStep 4835369 = 3626527) B3626527
theorem B870567 : Blo 868566 870567 := bstep (se 1 (by rfl) ⟨652925, by rfl⟩ : syracuseStep 870567 = 1305851) B1305851
theorem B870651 : Blo 868566 870651 := bstep (se 1 (by rfl) ⟨652988, by rfl⟩ : syracuseStep 870651 = 1305977) B1305977
theorem B870811 : Blo 868566 870811 := bstep (se 1 (by rfl) ⟨653108, by rfl⟩ : syracuseStep 870811 = 1306217) B1306217
theorem B871143 : Blo 868566 871143 := bstep (se 1 (by rfl) ⟨653357, by rfl⟩ : syracuseStep 871143 = 1306715) B1306715
theorem B2935547 : Blo 868566 2935547 := bstep (se 1 (by rfl) ⟨2201660, by rfl⟩ : syracuseStep 2935547 = 4403321) B4403321
theorem B2935709 : Blo 868566 2935709 := bstep (se 3 (by rfl) ⟨550445, by rfl⟩ : syracuseStep 2935709 = 1100891) B1100891
theorem B871455 : Blo 868566 871455 := bstep (se 1 (by rfl) ⟨653591, by rfl⟩ : syracuseStep 871455 = 1307183) B1307183
theorem B10603655 : Blo 868566 10603655 := bstep (se 1 (by rfl) ⟨7952741, by rfl⟩ : syracuseStep 10603655 = 15905483) B15905483
theorem B871579 : Blo 868566 871579 := bstep (se 1 (by rfl) ⟨653684, by rfl⟩ : syracuseStep 871579 = 1307369) B1307369
theorem B14110175 : Blo 868566 14110175 := bstep (se 1 (by rfl) ⟨10582631, by rfl⟩ : syracuseStep 14110175 = 21165263) B21165263
theorem B1396379 : Blo 868566 1396379 := bstep (se 1 (by rfl) ⟨1047284, by rfl⟩ : syracuseStep 1396379 = 2094569) B2094569
theorem B1101595 : Blo 868566 1101595 := bstep (se 1 (by rfl) ⟨826196, by rfl⟩ : syracuseStep 1101595 = 1652393) B1652393
theorem B872303 : Blo 868566 872303 := bstep (se 1 (by rfl) ⟨654227, by rfl⟩ : syracuseStep 872303 = 1308455) B1308455
theorem B4968499 : Blo 868566 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B10572079 : Blo 868566 10572079 := bstep (se 1 (by rfl) ⟨7929059, by rfl⟩ : syracuseStep 10572079 = 15858119) B15858119
theorem B3133865 : Blo 868566 3133865 := bstep (se 2 (by rfl) ⟨1175199, by rfl⟩ : syracuseStep 3133865 = 2350399) B2350399
theorem B1954943 : Blo 868566 1954943 := bstep (se 1 (by rfl) ⟨1466207, by rfl⟩ : syracuseStep 1954943 = 2932415) B2932415
theorem B4412879 : Blo 868566 4412879 := bstep (se 1 (by rfl) ⟨3309659, by rfl⟩ : syracuseStep 4412879 = 6619319) B6619319
theorem B6281225 : Blo 868566 6281225 := bstep (se 2 (by rfl) ⟨2355459, by rfl⟩ : syracuseStep 6281225 = 4710919) B4710919
theorem B2939003 : Blo 868566 2939003 := bstep (se 1 (by rfl) ⟨2204252, by rfl⟩ : syracuseStep 2939003 = 4408505) B4408505
theorem B1858079 : Blo 868566 1858079 := bstep (se 1 (by rfl) ⟨1393559, by rfl⟩ : syracuseStep 1858079 = 2787119) B2787119
theorem B4414337 : Blo 868566 4414337 := bstep (se 2 (by rfl) ⟨1655376, by rfl⟩ : syracuseStep 4414337 = 3310753) B3310753
theorem B3300335 : Blo 868566 3300335 := bstep (se 1 (by rfl) ⟨2475251, by rfl⟩ : syracuseStep 3300335 = 4950503) B4950503
theorem B2350217 : Blo 868566 2350217 := bstep (se 2 (by rfl) ⟨881331, by rfl⟩ : syracuseStep 2350217 = 1762663) B1762663
theorem B50191649 : Blo 868566 50191649 := bstep (se 2 (by rfl) ⟨18821868, by rfl⟩ : syracuseStep 50191649 = 37643737) B37643737
theorem B1957175 : Blo 868566 1957175 := bstep (se 1 (by rfl) ⟨1467881, by rfl⟩ : syracuseStep 1957175 = 2935763) B2935763
theorem B2481835 : Blo 868566 2481835 := bstep (se 1 (by rfl) ⟨1861376, by rfl⟩ : syracuseStep 2481835 = 3722753) B3722753
theorem B7069427 : Blo 868566 7069427 := bstep (se 1 (by rfl) ⟨5302070, by rfl⟩ : syracuseStep 7069427 = 10604141) B10604141
theorem B1466363 : Blo 868566 1466363 := bstep (se 1 (by rfl) ⟨1099772, by rfl⟩ : syracuseStep 1466363 = 2199545) B2199545
theorem B1958111 : Blo 868566 1958111 := bstep (se 1 (by rfl) ⟨1468583, by rfl⟩ : syracuseStep 1958111 = 2937167) B2937167
theorem B25125349 : Blo 868566 25125349 := bstep (se 4 (by rfl) ⟨2355501, by rfl⟩ : syracuseStep 25125349 = 4711003) B4711003
theorem B1303529 : Blo 868566 1303529 := bstep (se 2 (by rfl) ⟨488823, by rfl⟩ : syracuseStep 1303529 = 977647) B977647
theorem B8348669 : Blo 868566 8348669 := bstep (se 3 (by rfl) ⟨1565375, by rfl⟩ : syracuseStep 8348669 = 3130751) B3130751
theorem B2483453 : Blo 868566 2483453 := bstep (se 3 (by rfl) ⟨465647, by rfl⟩ : syracuseStep 2483453 = 931295) B931295
theorem B2942459 : Blo 868566 2942459 := bstep (se 1 (by rfl) ⟨2206844, by rfl⟩ : syracuseStep 2942459 = 4413689) B4413689
theorem B2942567 : Blo 868566 2942567 := bstep (se 1 (by rfl) ⟨2206925, by rfl⟩ : syracuseStep 2942567 = 4413851) B4413851
theorem B3532511 : Blo 868566 3532511 := bstep (se 1 (by rfl) ⟨2649383, by rfl⟩ : syracuseStep 3532511 = 5298767) B5298767
theorem B2516807 : Blo 868566 2516807 := bstep (se 1 (by rfl) ⟨1887605, by rfl⟩ : syracuseStep 2516807 = 3775211) B3775211
theorem B1304411 : Blo 868566 1304411 := bstep (se 1 (by rfl) ⟨978308, by rfl⟩ : syracuseStep 1304411 = 1956617) B1956617
theorem B1566587 : Blo 868566 1566587 := bstep (se 1 (by rfl) ⟨1174940, by rfl⟩ : syracuseStep 1566587 = 2349881) B2349881
theorem B1304447 : Blo 868566 1304447 := bstep (se 1 (by rfl) ⟨978335, by rfl⟩ : syracuseStep 1304447 = 1956671) B1956671
theorem B1468543 : Blo 868566 1468543 := bstep (se 1 (by rfl) ⟨1101407, by rfl⟩ : syracuseStep 1468543 = 2202815) B2202815
theorem B1304903 : Blo 868566 1304903 := bstep (se 1 (by rfl) ⟨978677, by rfl⟩ : syracuseStep 1304903 = 1957355) B1957355
theorem B812706149 : Blo 868566 812706149 := bstep (se 4 (by rfl) ⟨76191201, by rfl⟩ : syracuseStep 812706149 = 152382403) B152382403
theorem B2943431 : Blo 868566 2943431 := bstep (se 1 (by rfl) ⟨2207573, by rfl⟩ : syracuseStep 2943431 = 4415147) B4415147
theorem B2943485 : Blo 868566 2943485 := bstep (se 3 (by rfl) ⟨551903, by rfl⟩ : syracuseStep 2943485 = 1103807) B1103807
theorem B7432793 : Blo 868566 7432793 := bstep (se 2 (by rfl) ⟨2787297, by rfl⟩ : syracuseStep 7432793 = 5574595) B5574595
theorem B3304253 : Blo 868566 3304253 := bstep (se 3 (by rfl) ⟨619547, by rfl⟩ : syracuseStep 3304253 = 1239095) B1239095
theorem B1961855 : Blo 868566 1961855 := bstep (se 1 (by rfl) ⟨1471391, by rfl⟩ : syracuseStep 1961855 = 2942783) B2942783
theorem B2355115 : Blo 868566 2355115 := bstep (se 1 (by rfl) ⟨1766336, by rfl⟩ : syracuseStep 2355115 = 3532673) B3532673
theorem B979015 : Blo 868566 979015 := bstep (se 1 (by rfl) ⟨734261, by rfl⟩ : syracuseStep 979015 = 1468523) B1468523
theorem B1306745 : Blo 868566 1306745 := bstep (se 2 (by rfl) ⟨490029, by rfl⟩ : syracuseStep 1306745 = 980059) B980059
theorem B1306793 : Blo 868566 1306793 := bstep (se 2 (by rfl) ⟨490047, by rfl⟩ : syracuseStep 1306793 = 980095) B980095
theorem B6287543 : Blo 868566 6287543 := bstep (se 1 (by rfl) ⟨4715657, by rfl⟩ : syracuseStep 6287543 = 9431315) B9431315
theorem B95383817 : Blo 868566 95383817 := bstep (se 2 (by rfl) ⟨35768931, by rfl⟩ : syracuseStep 95383817 = 71537863) B71537863
theorem B5566907 : Blo 868566 5566907 := bstep (se 1 (by rfl) ⟨4175180, by rfl⟩ : syracuseStep 5566907 = 8350361) B8350361
theorem B1307447 : Blo 868566 1307447 := bstep (se 1 (by rfl) ⟨980585, by rfl⟩ : syracuseStep 1307447 = 1961171) B1961171
theorem B558265283 : Blo 868566 558265283 := bstep (se 1 (by rfl) ⟨418698962, by rfl⟩ : syracuseStep 558265283 = 837397925) B837397925
theorem B1471655 : Blo 868566 1471655 := bstep (se 1 (by rfl) ⟨1103741, by rfl⟩ : syracuseStep 1471655 = 2207483) B2207483
theorem B3306683 : Blo 868566 3306683 := bstep (se 1 (by rfl) ⟨2480012, by rfl⟩ : syracuseStep 3306683 = 4960025) B4960025
theorem B26768573 : Blo 868566 26768573 := bstep (se 3 (by rfl) ⟨5019107, by rfl⟩ : syracuseStep 26768573 = 10038215) B10038215
theorem B1307975 : Blo 868566 1307975 := bstep (se 1 (by rfl) ⟨980981, by rfl⟩ : syracuseStep 1307975 = 1961963) B1961963
theorem B1767017 : Blo 868566 1767017 := bstep (se 2 (by rfl) ⟨662631, by rfl⟩ : syracuseStep 1767017 = 1325263) B1325263
theorem B1308335 : Blo 868566 1308335 := bstep (se 1 (by rfl) ⟨981251, by rfl⟩ : syracuseStep 1308335 = 1962503) B1962503
theorem B4192019 : Blo 868566 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B1308443 : Blo 868566 1308443 := bstep (se 1 (by rfl) ⟨981332, by rfl⟩ : syracuseStep 1308443 = 1962665) B1962665
theorem B6616889 : Blo 868566 6616889 := bstep (se 2 (by rfl) ⟨2481333, by rfl⟩ : syracuseStep 6616889 = 4962667) B4962667
theorem B1308779 : Blo 868566 1308779 := bstep (se 1 (by rfl) ⟨981584, by rfl⟩ : syracuseStep 1308779 = 1963169) B1963169
theorem B981247 : Blo 868566 981247 := bstep (se 1 (by rfl) ⟨735935, by rfl⟩ : syracuseStep 981247 = 1471871) B1471871
theorem B2783659 : Blo 868566 2783659 := bstep (se 1 (by rfl) ⟨2087744, by rfl⟩ : syracuseStep 2783659 = 4175489) B4175489
theorem B4291553 : Blo 868566 4291553 := bstep (se 2 (by rfl) ⟨1609332, by rfl⟩ : syracuseStep 4291553 = 3218665) B3218665
theorem B3309083 : Blo 868566 3309083 := bstep (se 1 (by rfl) ⟨2481812, by rfl⟩ : syracuseStep 3309083 = 4963625) B4963625
theorem B1343519 : Blo 868566 1343519 := bstep (se 1 (by rfl) ⟨1007639, by rfl⟩ : syracuseStep 1343519 = 2015279) B2015279
theorem B20349587 : Blo 868566 20349587 := bstep (se 1 (by rfl) ⟨15262190, by rfl⟩ : syracuseStep 20349587 = 30524381) B30524381
theorem B37618829 : Blo 868566 37618829 := bstep (se 3 (by rfl) ⟨7053530, by rfl⟩ : syracuseStep 37618829 = 14107061) B14107061
theorem B7439627 : Blo 868566 7439627 := bstep (se 1 (by rfl) ⟨5579720, by rfl⟩ : syracuseStep 7439627 = 11159441) B11159441
theorem B4949545 : Blo 868566 4949545 := bstep (se 2 (by rfl) ⟨1856079, by rfl⟩ : syracuseStep 4949545 = 3712159) B3712159
theorem B7145567 : Blo 868566 7145567 := bstep (se 1 (by rfl) ⟨5359175, by rfl⟩ : syracuseStep 7145567 = 10718351) B10718351
theorem B9406783 : Blo 868566 9406783 := bstep (se 1 (by rfl) ⟨7055087, by rfl⟩ : syracuseStep 9406783 = 14110175) B14110175
theorem B6622235 : Blo 868566 6622235 := bstep (se 1 (by rfl) ⟨4966676, by rfl⟩ : syracuseStep 6622235 = 9933353) B9933353
theorem B14880347 : Blo 868566 14880347 := bstep (se 1 (by rfl) ⟨11160260, by rfl⟩ : syracuseStep 14880347 = 22320521) B22320521
theorem B7343759 : Blo 868566 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B2200223 : Blo 868566 2200223 := bstep (se 1 (by rfl) ⟨1650167, by rfl⟩ : syracuseStep 2200223 = 3300335) B3300335
theorem B33461099 : Blo 868566 33461099 := bstep (se 1 (by rfl) ⟨25095824, by rfl⟩ : syracuseStep 33461099 = 50191649) B50191649
theorem B9901277 : Blo 868566 9901277 := bstep (se 3 (by rfl) ⟨1856489, by rfl⟩ : syracuseStep 9901277 = 3712979) B3712979
theorem B6624665 : Blo 868566 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B14096105 : Blo 868566 14096105 := bstep (se 2 (by rfl) ⟨5286039, by rfl⟩ : syracuseStep 14096105 = 10572079) B10572079
theorem B1677871 : Blo 868566 1677871 := bstep (se 1 (by rfl) ⟨1258403, by rfl⟩ : syracuseStep 1677871 = 2516807) B2516807
theorem B4954877 : Blo 868566 4954877 := bstep (se 3 (by rfl) ⟨929039, by rfl⟩ : syracuseStep 4954877 = 1858079) B1858079
theorem B4955195 : Blo 868566 4955195 := bstep (se 1 (by rfl) ⟨3716396, by rfl⟩ : syracuseStep 4955195 = 7432793) B7432793
theorem B2202835 : Blo 868566 2202835 := bstep (se 1 (by rfl) ⟨1652126, by rfl⟩ : syracuseStep 2202835 = 3304253) B3304253
theorem B20061593 : Blo 868566 20061593 := bstep (se 2 (by rfl) ⟨7523097, by rfl⟩ : syracuseStep 20061593 = 15046195) B15046195
theorem B11444141 : Blo 868566 11444141 := bstep (se 3 (by rfl) ⟨2145776, by rfl⟩ : syracuseStep 11444141 = 4291553) B4291553
theorem B5578955 : Blo 868566 5578955 := bstep (se 1 (by rfl) ⟨4184216, by rfl⟩ : syracuseStep 5578955 = 8368433) B8368433
theorem B3711271 : Blo 868566 3711271 := bstep (se 1 (by rfl) ⟨2783453, by rfl⟩ : syracuseStep 3711271 = 5566907) B5566907
theorem B7446977 : Blo 868566 7446977 := bstep (se 2 (by rfl) ⟨2792616, by rfl⟩ : syracuseStep 7446977 = 5585233) B5585233
theorem B3711545 : Blo 868566 3711545 := bstep (se 2 (by rfl) ⟨1391829, by rfl⟩ : syracuseStep 3711545 = 2783659) B2783659
theorem B2204455 : Blo 868566 2204455 := bstep (se 1 (by rfl) ⟨1653341, by rfl⟩ : syracuseStep 2204455 = 3306683) B3306683
theorem B2794679 : Blo 868566 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B16754849 : Blo 868566 16754849 := bstep (se 2 (by rfl) ⟨6283068, by rfl⟩ : syracuseStep 16754849 = 12566137) B12566137
theorem B2206055 : Blo 868566 2206055 := bstep (se 1 (by rfl) ⟨1654541, by rfl⟩ : syracuseStep 2206055 = 3309083) B3309083
theorem B928207 : Blo 868566 928207 := bstep (se 1 (by rfl) ⟨696155, by rfl⟩ : syracuseStep 928207 = 1392311) B1392311
theorem B1649135 : Blo 868566 1649135 := bstep (se 1 (by rfl) ⟨1236851, by rfl⟩ : syracuseStep 1649135 = 2473703) B2473703
theorem B4401863 : Blo 868566 4401863 := bstep (se 1 (by rfl) ⟨3301397, by rfl⟩ : syracuseStep 4401863 = 6602795) B6602795
theorem B482257799 : Blo 868566 482257799 := bstep (se 1 (by rfl) ⟨361693349, by rfl⟩ : syracuseStep 482257799 = 723386699) B723386699
theorem B33500465 : Blo 868566 33500465 := bstep (se 2 (by rfl) ⟨12562674, by rfl⟩ : syracuseStep 33500465 = 25125349) B25125349
theorem B929279 : Blo 868566 929279 := bstep (se 1 (by rfl) ⟨696959, by rfl⟩ : syracuseStep 929279 = 1393919) B1393919
theorem B4403159 : Blo 868566 4403159 := bstep (se 1 (by rfl) ⟨3302369, by rfl⟩ : syracuseStep 4403159 = 6604739) B6604739
theorem B3223579 : Blo 868566 3223579 := bstep (se 1 (by rfl) ⟨2417684, by rfl⟩ : syracuseStep 3223579 = 4835369) B4835369
theorem B2208161 : Blo 868566 2208161 := bstep (se 2 (by rfl) ⟨828060, by rfl⟩ : syracuseStep 2208161 = 1656121) B1656121
theorem B2208617 : Blo 868566 2208617 := bstep (se 2 (by rfl) ⟨828231, by rfl⟩ : syracuseStep 2208617 = 1656463) B1656463
theorem B6272111 : Blo 868566 6272111 := bstep (se 1 (by rfl) ⟨4704083, by rfl⟩ : syracuseStep 6272111 = 9408167) B9408167
theorem B3716381 : Blo 868566 3716381 := bstep (se 3 (by rfl) ⟨696821, by rfl⟩ : syracuseStep 3716381 = 1393643) B1393643
theorem B4963943 : Blo 868566 4963943 := bstep (se 1 (by rfl) ⟨3722957, by rfl⟩ : syracuseStep 4963943 = 7445915) B7445915
theorem B4177565 : Blo 868566 4177565 := bstep (se 3 (by rfl) ⟨783293, by rfl⟩ : syracuseStep 4177565 = 1566587) B1566587
theorem B458965277 : Blo 868566 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B869019 : Blo 868566 869019 := bstep (se 1 (by rfl) ⟨651764, by rfl⟩ : syracuseStep 869019 = 1303529) B1303529
theorem B1655635 : Blo 868566 1655635 := bstep (se 1 (by rfl) ⟨1241726, by rfl⟩ : syracuseStep 1655635 = 2483453) B2483453
theorem B869607 : Blo 868566 869607 := bstep (se 1 (by rfl) ⟨652205, by rfl⟩ : syracuseStep 869607 = 1304411) B1304411
theorem B869631 : Blo 868566 869631 := bstep (se 1 (by rfl) ⟨652223, by rfl⟩ : syracuseStep 869631 = 1304447) B1304447
theorem B869935 : Blo 868566 869935 := bstep (se 1 (by rfl) ⟨652451, by rfl⟩ : syracuseStep 869935 = 1304903) B1304903
theorem B541804099 : Blo 868566 541804099 := bstep (se 1 (by rfl) ⟨406353074, by rfl⟩ : syracuseStep 541804099 = 812706149) B812706149
theorem B4703827 : Blo 868566 4703827 := bstep (se 1 (by rfl) ⟨3527870, by rfl⟩ : syracuseStep 4703827 = 7055741) B7055741
theorem B871163 : Blo 868566 871163 := bstep (se 1 (by rfl) ⟨653372, by rfl⟩ : syracuseStep 871163 = 1306745) B1306745
theorem B871195 : Blo 868566 871195 := bstep (se 1 (by rfl) ⟨653396, by rfl⟩ : syracuseStep 871195 = 1306793) B1306793
theorem B63589211 : Blo 868566 63589211 := bstep (se 1 (by rfl) ⟨47691908, by rfl⟩ : syracuseStep 63589211 = 95383817) B95383817
theorem B2935871 : Blo 868566 2935871 := bstep (se 1 (by rfl) ⟨2201903, by rfl⟩ : syracuseStep 2935871 = 4403807) B4403807
theorem B871631 : Blo 868566 871631 := bstep (se 1 (by rfl) ⟨653723, by rfl⟩ : syracuseStep 871631 = 1307447) B1307447
theorem B17845715 : Blo 868566 17845715 := bstep (se 1 (by rfl) ⟨13384286, by rfl⟩ : syracuseStep 17845715 = 26768573) B26768573
theorem B871983 : Blo 868566 871983 := bstep (se 1 (by rfl) ⟨653987, by rfl⟩ : syracuseStep 871983 = 1307975) B1307975
theorem B872223 : Blo 868566 872223 := bstep (se 1 (by rfl) ⟨654167, by rfl⟩ : syracuseStep 872223 = 1308335) B1308335
theorem B872295 : Blo 868566 872295 := bstep (se 1 (by rfl) ⟨654221, by rfl⟩ : syracuseStep 872295 = 1308443) B1308443
theorem B4411259 : Blo 868566 4411259 := bstep (se 1 (by rfl) ⟨3308444, by rfl⟩ : syracuseStep 4411259 = 6616889) B6616889
theorem B8376347 : Blo 868566 8376347 := bstep (se 1 (by rfl) ⟨6282260, by rfl⟩ : syracuseStep 8376347 = 12564521) B12564521
theorem B872519 : Blo 868566 872519 := bstep (se 1 (by rfl) ⟨654389, by rfl⟩ : syracuseStep 872519 = 1308779) B1308779
theorem B3723677 : Blo 868566 3723677 := bstep (se 3 (by rfl) ⟨698189, by rfl⟩ : syracuseStep 3723677 = 1396379) B1396379
theorem B1954295 : Blo 868566 1954295 := bstep (se 1 (by rfl) ⟨1465721, by rfl⟩ : syracuseStep 1954295 = 2931443) B2931443
theorem B2971495 : Blo 868566 2971495 := bstep (se 1 (by rfl) ⟨2228621, by rfl⟩ : syracuseStep 2971495 = 4457243) B4457243
theorem B2939705 : Blo 868566 2939705 := bstep (se 2 (by rfl) ⟨1102389, by rfl⟩ : syracuseStep 2939705 = 2204779) B2204779
theorem B1957031 : Blo 868566 1957031 := bstep (se 1 (by rfl) ⟨1467773, by rfl⟩ : syracuseStep 1957031 = 2935547) B2935547
theorem B1957139 : Blo 868566 1957139 := bstep (se 1 (by rfl) ⟨1467854, by rfl⟩ : syracuseStep 1957139 = 2935709) B2935709
theorem B3530141 : Blo 868566 3530141 := bstep (se 3 (by rfl) ⟨661901, by rfl⟩ : syracuseStep 3530141 = 1323803) B1323803
theorem B7069103 : Blo 868566 7069103 := bstep (se 1 (by rfl) ⟨5301827, by rfl⟩ : syracuseStep 7069103 = 10603655) B10603655
theorem B3301019 : Blo 868566 3301019 := bstep (se 1 (by rfl) ⟨2475764, by rfl⟩ : syracuseStep 3301019 = 4951529) B4951529
theorem B25386689 : Blo 868566 25386689 := bstep (se 2 (by rfl) ⟨9520008, by rfl⟩ : syracuseStep 25386689 = 19040017) B19040017
theorem B4415471 : Blo 868566 4415471 := bstep (se 1 (by rfl) ⟨3311603, by rfl⟩ : syracuseStep 4415471 = 6623207) B6623207
theorem B1958057 : Blo 868566 1958057 := bstep (se 2 (by rfl) ⟨734271, by rfl⟩ : syracuseStep 1958057 = 1468543) B1468543
theorem B2089243 : Blo 868566 2089243 := bstep (se 1 (by rfl) ⟨1566932, by rfl⟩ : syracuseStep 2089243 = 3133865) B3133865
theorem B3301991 : Blo 868566 3301991 := bstep (se 1 (by rfl) ⟨2476493, by rfl⟩ : syracuseStep 3301991 = 4952987) B4952987
theorem B1303295 : Blo 868566 1303295 := bstep (se 1 (by rfl) ⟨977471, by rfl⟩ : syracuseStep 1303295 = 1954943) B1954943
theorem B2941919 : Blo 868566 2941919 := bstep (se 1 (by rfl) ⟨2206439, by rfl⟩ : syracuseStep 2941919 = 4412879) B4412879
theorem B15885335 : Blo 868566 15885335 := bstep (se 1 (by rfl) ⟨11914001, by rfl⟩ : syracuseStep 15885335 = 23828003) B23828003
theorem B343106675 : Blo 868566 343106675 := bstep (se 1 (by rfl) ⟨257330006, by rfl⟩ : syracuseStep 343106675 = 514660013) B514660013
theorem B4187483 : Blo 868566 4187483 := bstep (se 1 (by rfl) ⟨3140612, by rfl⟩ : syracuseStep 4187483 = 6281225) B6281225
theorem B1959335 : Blo 868566 1959335 := bstep (se 1 (by rfl) ⟨1469501, by rfl⟩ : syracuseStep 1959335 = 2939003) B2939003
theorem B2942891 : Blo 868566 2942891 := bstep (se 1 (by rfl) ⟨2207168, by rfl⟩ : syracuseStep 2942891 = 4414337) B4414337
theorem B1566811 : Blo 868566 1566811 := bstep (se 1 (by rfl) ⟨1175108, by rfl⟩ : syracuseStep 1566811 = 2350217) B2350217
theorem B1304783 : Blo 868566 1304783 := bstep (se 1 (by rfl) ⟨978587, by rfl⟩ : syracuseStep 1304783 = 1957175) B1957175
theorem B1468793 : Blo 868566 1468793 := bstep (se 2 (by rfl) ⟨550797, by rfl⟩ : syracuseStep 1468793 = 1101595) B1101595
theorem B4712951 : Blo 868566 4712951 := bstep (se 1 (by rfl) ⟨3534713, by rfl⟩ : syracuseStep 4712951 = 7069427) B7069427
theorem B3140153 : Blo 868566 3140153 := bstep (se 2 (by rfl) ⟨1177557, by rfl⟩ : syracuseStep 3140153 = 2355115) B2355115
theorem B977575 : Blo 868566 977575 := bstep (se 1 (by rfl) ⟨733181, by rfl⟩ : syracuseStep 977575 = 1466363) B1466363
theorem B1305353 : Blo 868566 1305353 := bstep (se 2 (by rfl) ⟨489507, by rfl⟩ : syracuseStep 1305353 = 979015) B979015
theorem B1305407 : Blo 868566 1305407 := bstep (se 1 (by rfl) ⟨979055, by rfl⟩ : syracuseStep 1305407 = 1958111) B1958111
theorem B5565779 : Blo 868566 5565779 := bstep (se 1 (by rfl) ⟨4174334, by rfl⟩ : syracuseStep 5565779 = 8348669) B8348669
theorem B1961639 : Blo 868566 1961639 := bstep (se 1 (by rfl) ⟨1471229, by rfl⟩ : syracuseStep 1961639 = 2942459) B2942459
theorem B1961711 : Blo 868566 1961711 := bstep (se 1 (by rfl) ⟨1471283, by rfl⟩ : syracuseStep 1961711 = 2942567) B2942567
theorem B2355007 : Blo 868566 2355007 := bstep (se 1 (by rfl) ⟨1766255, by rfl⟩ : syracuseStep 2355007 = 3532511) B3532511
theorem B3305407 : Blo 868566 3305407 := bstep (se 1 (by rfl) ⟨2479055, by rfl⟩ : syracuseStep 3305407 = 4958111) B4958111
theorem B1962287 : Blo 868566 1962287 := bstep (se 1 (by rfl) ⟨1471715, by rfl⟩ : syracuseStep 1962287 = 2943431) B2943431
theorem B1962323 : Blo 868566 1962323 := bstep (se 1 (by rfl) ⟨1471742, by rfl⟩ : syracuseStep 1962323 = 2943485) B2943485
theorem B1307903 : Blo 868566 1307903 := bstep (se 1 (by rfl) ⟨980927, by rfl⟩ : syracuseStep 1307903 = 1961855) B1961855
theorem B4191695 : Blo 868566 4191695 := bstep (se 1 (by rfl) ⟨3143771, by rfl⟩ : syracuseStep 4191695 = 6287543) B6287543
theorem B1308329 : Blo 868566 1308329 := bstep (se 2 (by rfl) ⟨490623, by rfl⟩ : syracuseStep 1308329 = 981247) B981247
theorem B372176855 : Blo 868566 372176855 := bstep (se 1 (by rfl) ⟨279132641, by rfl⟩ : syracuseStep 372176855 = 558265283) B558265283
theorem B981103 : Blo 868566 981103 := bstep (se 1 (by rfl) ⟨735827, by rfl⟩ : syracuseStep 981103 = 1471655) B1471655
theorem B1178011 : Blo 868566 1178011 := bstep (se 1 (by rfl) ⟨883508, by rfl⟩ : syracuseStep 1178011 = 1767017) B1767017
theorem B3309113 : Blo 868566 3309113 := bstep (se 2 (by rfl) ⟨1240917, by rfl⟩ : syracuseStep 3309113 = 2481835) B2481835
theorem B4948361 : Blo 868566 4948361 := bstep (se 2 (by rfl) ⟨1855635, by rfl⟩ : syracuseStep 4948361 = 3711271) B3711271
theorem B11142629 : Blo 868566 11142629 := bstep (se 4 (by rfl) ⟨1044621, by rfl⟩ : syracuseStep 11142629 = 2089243) B2089243
theorem B54265565 : Blo 868566 54265565 := bstep (se 3 (by rfl) ⟨10174793, by rfl⟩ : syracuseStep 54265565 = 20349587) B20349587
theorem B722405465 : Blo 868566 722405465 := bstep (se 2 (by rfl) ⟨270902049, by rfl⟩ : syracuseStep 722405465 = 541804099) B541804099
theorem B13374395 : Blo 868566 13374395 := bstep (se 1 (by rfl) ⟨10030796, by rfl⟩ : syracuseStep 13374395 = 20061593) B20061593
theorem B2200679 : Blo 868566 2200679 := bstep (se 1 (by rfl) ⟨1650509, by rfl⟩ : syracuseStep 2200679 = 3301019) B3301019
theorem B4298105 : Blo 868566 4298105 := bstep (se 2 (by rfl) ⟨1611789, by rfl⟩ : syracuseStep 4298105 = 3223579) B3223579
theorem B2201327 : Blo 868566 2201327 := bstep (se 1 (by rfl) ⟨1650995, by rfl⟩ : syracuseStep 2201327 = 3301991) B3301991
theorem B2791655 : Blo 868566 2791655 := bstep (se 1 (by rfl) ⟨2093741, by rfl⟩ : syracuseStep 2791655 = 4187483) B4187483
theorem B3710519 : Blo 868566 3710519 := bstep (se 1 (by rfl) ⟨2782889, by rfl⟩ : syracuseStep 3710519 = 5565779) B5565779
theorem B2237161 : Blo 868566 2237161 := bstep (se 2 (by rfl) ⟨838935, by rfl⟩ : syracuseStep 2237161 = 1677871) B1677871
theorem B2794463 : Blo 868566 2794463 := bstep (se 1 (by rfl) ⟨2095847, by rfl⟩ : syracuseStep 2794463 = 4191695) B4191695
theorem B47588573 : Blo 868566 47588573 := bstep (se 3 (by rfl) ⟨8922857, by rfl⟩ : syracuseStep 47588573 = 17845715) B17845715
theorem B2206075 : Blo 868566 2206075 := bstep (se 1 (by rfl) ⟨1654556, by rfl⟩ : syracuseStep 2206075 = 3309113) B3309113
theorem B895679 : Blo 868566 895679 := bstep (se 1 (by rfl) ⟨671759, by rfl⟩ : syracuseStep 895679 = 1343519) B1343519
theorem B25079219 : Blo 868566 25079219 := bstep (se 1 (by rfl) ⟨18809414, by rfl⟩ : syracuseStep 25079219 = 37618829) B37618829
theorem B4959751 : Blo 868566 4959751 := bstep (se 1 (by rfl) ⟨3719813, by rfl⟩ : syracuseStep 4959751 = 7439627) B7439627
theorem B2207513 : Blo 868566 2207513 := bstep (se 2 (by rfl) ⟨827817, by rfl⟩ : syracuseStep 2207513 = 1655635) B1655635
theorem B4763711 : Blo 868566 4763711 := bstep (se 1 (by rfl) ⟨3572783, by rfl⟩ : syracuseStep 4763711 = 7145567) B7145567
theorem B6599393 : Blo 868566 6599393 := bstep (se 2 (by rfl) ⟨2474772, by rfl⟩ : syracuseStep 6599393 = 4949545) B4949545
theorem B6271769 : Blo 868566 6271769 := bstep (se 2 (by rfl) ⟨2351913, by rfl⟩ : syracuseStep 6271769 = 4703827) B4703827
theorem B4895839 : Blo 868566 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B5584231 : Blo 868566 5584231 := bstep (se 1 (by rfl) ⟨4188173, by rfl⟩ : syracuseStep 5584231 = 8376347) B8376347
theorem B16725629 : Blo 868566 16725629 := bstep (se 3 (by rfl) ⟨3136055, by rfl⟩ : syracuseStep 16725629 = 6272111) B6272111
theorem B6600851 : Blo 868566 6600851 := bstep (se 1 (by rfl) ⟨4950638, by rfl⟩ : syracuseStep 6600851 = 9901277) B9901277
theorem B16924459 : Blo 868566 16924459 := bstep (se 1 (by rfl) ⟨12693344, by rfl⟩ : syracuseStep 16924459 = 25386689) B25386689
theorem B4407209 : Blo 868566 4407209 := bstep (se 2 (by rfl) ⟨1652703, by rfl⟩ : syracuseStep 4407209 = 3305407) B3305407
theorem B3719303 : Blo 868566 3719303 := bstep (se 1 (by rfl) ⟨2789477, by rfl⟩ : syracuseStep 3719303 = 5578955) B5578955
theorem B4964651 : Blo 868566 4964651 := bstep (se 1 (by rfl) ⟨3723488, by rfl⟩ : syracuseStep 4964651 = 7446977) B7446977
theorem B2474363 : Blo 868566 2474363 := bstep (se 1 (by rfl) ⟨1855772, by rfl⟩ : syracuseStep 2474363 = 3711545) B3711545
theorem B868863 : Blo 868566 868863 := bstep (se 1 (by rfl) ⟨651647, by rfl⟩ : syracuseStep 868863 = 1303295) B1303295
theorem B228737783 : Blo 868566 228737783 := bstep (se 1 (by rfl) ⟨171553337, by rfl⟩ : syracuseStep 228737783 = 343106675) B343106675
theorem B12567869 : Blo 868566 12567869 := bstep (se 3 (by rfl) ⟨2356475, by rfl⟩ : syracuseStep 12567869 = 4712951) B4712951
theorem B869855 : Blo 868566 869855 := bstep (se 1 (by rfl) ⟨652391, by rfl⟩ : syracuseStep 869855 = 1304783) B1304783
theorem B1099423 : Blo 868566 1099423 := bstep (se 1 (by rfl) ⟨824567, by rfl⟩ : syracuseStep 1099423 = 1649135) B1649135
theorem B2934575 : Blo 868566 2934575 := bstep (se 1 (by rfl) ⟨2200931, by rfl⟩ : syracuseStep 2934575 = 4401863) B4401863
theorem B870235 : Blo 868566 870235 := bstep (se 1 (by rfl) ⟨652676, by rfl⟩ : syracuseStep 870235 = 1305353) B1305353
theorem B870271 : Blo 868566 870271 := bstep (se 1 (by rfl) ⟨652703, by rfl⟩ : syracuseStep 870271 = 1305407) B1305407
theorem B321505199 : Blo 868566 321505199 := bstep (se 1 (by rfl) ⟨241128899, by rfl⟩ : syracuseStep 321505199 = 482257799) B482257799
theorem B22333643 : Blo 868566 22333643 := bstep (se 1 (by rfl) ⟨16750232, by rfl⟩ : syracuseStep 22333643 = 33500465) B33500465
theorem B2935439 : Blo 868566 2935439 := bstep (se 1 (by rfl) ⟨2201579, by rfl⟩ : syracuseStep 2935439 = 4403159) B4403159
theorem B871935 : Blo 868566 871935 := bstep (se 1 (by rfl) ⟨653951, by rfl⟩ : syracuseStep 871935 = 1307903) B1307903
theorem B2477587 : Blo 868566 2477587 := bstep (se 1 (by rfl) ⟨1858190, by rfl⟩ : syracuseStep 2477587 = 3716381) B3716381
theorem B872219 : Blo 868566 872219 := bstep (se 1 (by rfl) ⟨654164, by rfl⟩ : syracuseStep 872219 = 1308329) B1308329
theorem B2478077 : Blo 868566 2478077 := bstep (se 3 (by rfl) ⟨464639, by rfl⟩ : syracuseStep 2478077 = 929279) B929279
theorem B2937113 : Blo 868566 2937113 := bstep (se 2 (by rfl) ⟨1101417, by rfl⟩ : syracuseStep 2937113 = 2202835) B2202835
theorem B15847973 : Blo 868566 15847973 := bstep (se 4 (by rfl) ⟨1485747, by rfl⟩ : syracuseStep 15847973 = 2971495) B2971495
theorem B305976851 : Blo 868566 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B2939273 : Blo 868566 2939273 := bstep (se 2 (by rfl) ⟨1102227, by rfl⟩ : syracuseStep 2939273 = 2204455) B2204455
theorem B42392807 : Blo 868566 42392807 := bstep (se 1 (by rfl) ⟨31794605, by rfl⟩ : syracuseStep 42392807 = 63589211) B63589211
theorem B4414823 : Blo 868566 4414823 := bstep (se 1 (by rfl) ⟨3311117, by rfl⟩ : syracuseStep 4414823 = 6622235) B6622235
theorem B1957247 : Blo 868566 1957247 := bstep (se 1 (by rfl) ⟨1467935, by rfl⟩ : syracuseStep 1957247 = 2935871) B2935871
theorem B9920231 : Blo 868566 9920231 := bstep (se 1 (by rfl) ⟨7440173, by rfl⟩ : syracuseStep 9920231 = 14880347) B14880347
theorem B2940839 : Blo 868566 2940839 := bstep (se 1 (by rfl) ⟨2205629, by rfl⟩ : syracuseStep 2940839 = 4411259) B4411259
theorem B42360893 : Blo 868566 42360893 := bstep (se 3 (by rfl) ⟨7942667, by rfl⟩ : syracuseStep 42360893 = 15885335) B15885335
theorem B2089081 : Blo 868566 2089081 := bstep (se 2 (by rfl) ⟨783405, by rfl⟩ : syracuseStep 2089081 = 1566811) B1566811
theorem B2482451 : Blo 868566 2482451 := bstep (se 1 (by rfl) ⟨1861838, by rfl⟩ : syracuseStep 2482451 = 3723677) B3723677
theorem B1302863 : Blo 868566 1302863 := bstep (se 1 (by rfl) ⟨977147, by rfl⟩ : syracuseStep 1302863 = 1954295) B1954295
theorem B12542377 : Blo 868566 12542377 := bstep (se 2 (by rfl) ⟨4703391, by rfl⟩ : syracuseStep 12542377 = 9406783) B9406783
theorem B1466815 : Blo 868566 1466815 := bstep (se 1 (by rfl) ⟨1100111, by rfl⟩ : syracuseStep 1466815 = 2200223) B2200223
theorem B22307399 : Blo 868566 22307399 := bstep (se 1 (by rfl) ⟨16730549, by rfl⟩ : syracuseStep 22307399 = 33461099) B33461099
theorem B1237609 : Blo 868566 1237609 := bstep (se 2 (by rfl) ⟨464103, by rfl⟩ : syracuseStep 1237609 = 928207) B928207
theorem B1303433 : Blo 868566 1303433 := bstep (se 2 (by rfl) ⟨488787, by rfl⟩ : syracuseStep 1303433 = 977575) B977575
theorem B4416443 : Blo 868566 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B9397403 : Blo 868566 9397403 := bstep (se 1 (by rfl) ⟨7048052, by rfl⟩ : syracuseStep 9397403 = 14096105) B14096105
theorem B3303251 : Blo 868566 3303251 := bstep (se 1 (by rfl) ⟨2477438, by rfl⟩ : syracuseStep 3303251 = 4954877) B4954877
theorem B1959803 : Blo 868566 1959803 := bstep (se 1 (by rfl) ⟨1469852, by rfl⟩ : syracuseStep 1959803 = 2939705) B2939705
theorem B3303463 : Blo 868566 3303463 := bstep (se 1 (by rfl) ⟨2477597, by rfl⟩ : syracuseStep 3303463 = 4955195) B4955195
theorem B1304687 : Blo 868566 1304687 := bstep (se 1 (by rfl) ⟨978515, by rfl⟩ : syracuseStep 1304687 = 1957031) B1957031
theorem B1304759 : Blo 868566 1304759 := bstep (se 1 (by rfl) ⟨978569, by rfl⟩ : syracuseStep 1304759 = 1957139) B1957139
theorem B2353427 : Blo 868566 2353427 := bstep (se 1 (by rfl) ⟨1765070, by rfl⟩ : syracuseStep 2353427 = 3530141) B3530141
theorem B4712735 : Blo 868566 4712735 := bstep (se 1 (by rfl) ⟨3534551, by rfl⟩ : syracuseStep 4712735 = 7069103) B7069103
theorem B3140009 : Blo 868566 3140009 := bstep (se 2 (by rfl) ⟨1177503, by rfl⟩ : syracuseStep 3140009 = 2355007) B2355007
theorem B7629427 : Blo 868566 7629427 := bstep (se 1 (by rfl) ⟨5722070, by rfl⟩ : syracuseStep 7629427 = 11444141) B11444141
theorem B2943647 : Blo 868566 2943647 := bstep (se 1 (by rfl) ⟨2207735, by rfl⟩ : syracuseStep 2943647 = 4415471) B4415471
theorem B1305371 : Blo 868566 1305371 := bstep (se 1 (by rfl) ⟨979028, by rfl⟩ : syracuseStep 1305371 = 1958057) B1958057
theorem B1961279 : Blo 868566 1961279 := bstep (se 1 (by rfl) ⟨1470959, by rfl⟩ : syracuseStep 1961279 = 2941919) B2941919
theorem B1863119 : Blo 868566 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B1306223 : Blo 868566 1306223 := bstep (se 1 (by rfl) ⟨979667, by rfl⟩ : syracuseStep 1306223 = 1959335) B1959335
theorem B1961927 : Blo 868566 1961927 := bstep (se 1 (by rfl) ⟨1471445, by rfl⟩ : syracuseStep 1961927 = 2942891) B2942891
theorem B11169899 : Blo 868566 11169899 := bstep (se 1 (by rfl) ⟨8377424, by rfl⟩ : syracuseStep 11169899 = 16754849) B16754849
theorem B1470703 : Blo 868566 1470703 := bstep (se 1 (by rfl) ⟨1103027, by rfl⟩ : syracuseStep 1470703 = 2206055) B2206055
theorem B979195 : Blo 868566 979195 := bstep (se 1 (by rfl) ⟨734396, by rfl⟩ : syracuseStep 979195 = 1468793) B1468793
theorem B2093435 : Blo 868566 2093435 := bstep (se 1 (by rfl) ⟨1570076, by rfl⟩ : syracuseStep 2093435 = 3140153) B3140153
theorem B1307759 : Blo 868566 1307759 := bstep (se 1 (by rfl) ⟨980819, by rfl⟩ : syracuseStep 1307759 = 1961639) B1961639
theorem B1307807 : Blo 868566 1307807 := bstep (se 1 (by rfl) ⟨980855, by rfl⟩ : syracuseStep 1307807 = 1961711) B1961711
theorem B1308137 : Blo 868566 1308137 := bstep (se 2 (by rfl) ⟨490551, by rfl⟩ : syracuseStep 1308137 = 981103) B981103
theorem B1308191 : Blo 868566 1308191 := bstep (se 1 (by rfl) ⟨981143, by rfl⟩ : syracuseStep 1308191 = 1962287) B1962287
theorem B1308215 : Blo 868566 1308215 := bstep (se 1 (by rfl) ⟨981161, by rfl⟩ : syracuseStep 1308215 = 1962323) B1962323
theorem B1472107 : Blo 868566 1472107 := bstep (se 1 (by rfl) ⟨1104080, by rfl⟩ : syracuseStep 1472107 = 2208161) B2208161
theorem B1570681 : Blo 868566 1570681 := bstep (se 2 (by rfl) ⟨589005, by rfl⟩ : syracuseStep 1570681 = 1178011) B1178011
theorem B1472411 : Blo 868566 1472411 := bstep (se 1 (by rfl) ⟨1104308, by rfl⟩ : syracuseStep 1472411 = 2208617) B2208617
theorem B248117903 : Blo 868566 248117903 := bstep (se 1 (by rfl) ⟨186088427, by rfl⟩ : syracuseStep 248117903 = 372176855) B372176855
theorem B3309295 : Blo 868566 3309295 := bstep (se 1 (by rfl) ⟨2481971, by rfl⟩ : syracuseStep 3309295 = 4963943) B4963943
theorem B2785043 : Blo 868566 2785043 := bstep (se 1 (by rfl) ⟨2088782, by rfl⟩ : syracuseStep 2785043 = 4177565) B4177565
theorem B2785441 : Blo 868566 2785441 := bstep (se 2 (by rfl) ⟨1044540, by rfl⟩ : syracuseStep 2785441 = 2089081) B2089081
theorem B3309767 : Blo 868566 3309767 := bstep (se 1 (by rfl) ⟨2482325, by rfl⟩ : syracuseStep 3309767 = 4964651) B4964651
theorem B2982881 : Blo 868566 2982881 := bstep (se 2 (by rfl) ⟨1118580, by rfl⟩ : syracuseStep 2982881 = 2237161) B2237161
theorem B36177043 : Blo 868566 36177043 := bstep (se 1 (by rfl) ⟨27132782, by rfl⟩ : syracuseStep 36177043 = 54265565) B54265565
theorem B214336799 : Blo 868566 214336799 := bstep (se 1 (by rfl) ⟨160752599, by rfl⟩ : syracuseStep 214336799 = 321505199) B321505199
theorem B8916263 : Blo 868566 8916263 := bstep (se 1 (by rfl) ⟨6687197, by rfl⟩ : syracuseStep 8916263 = 13374395) B13374395
theorem B203984567 : Blo 868566 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B6264935 : Blo 868566 6264935 := bstep (se 1 (by rfl) ⟨4698701, by rfl⟩ : syracuseStep 6264935 = 9397403) B9397403
theorem B31725715 : Blo 868566 31725715 := bstep (se 1 (by rfl) ⟨23794286, by rfl⟩ : syracuseStep 31725715 = 47588573) B47588573
theorem B2202167 : Blo 868566 2202167 := bstep (se 1 (by rfl) ⟨1651625, by rfl⟩ : syracuseStep 2202167 = 3303251) B3303251
theorem B6527785 : Blo 868566 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B7445641 : Blo 868566 7445641 := bstep (se 2 (by rfl) ⟨2792115, by rfl⟩ : syracuseStep 7445641 = 5584231) B5584231
theorem B16719479 : Blo 868566 16719479 := bstep (se 1 (by rfl) ⟨12539609, by rfl⟩ : syracuseStep 16719479 = 25079219) B25079219
theorem B7446599 : Blo 868566 7446599 := bstep (se 1 (by rfl) ⟨5584949, by rfl⟩ : syracuseStep 7446599 = 11169899) B11169899
theorem B4399595 : Blo 868566 4399595 := bstep (se 1 (by rfl) ⟨3299696, by rfl⟩ : syracuseStep 4399595 = 6599393) B6599393
theorem B11150419 : Blo 868566 11150419 := bstep (se 1 (by rfl) ⟨8362814, by rfl⟩ : syracuseStep 11150419 = 16725629) B16725629
theorem B4400567 : Blo 868566 4400567 := bstep (se 1 (by rfl) ⟨3300425, by rfl⟩ : syracuseStep 4400567 = 6600851) B6600851
theorem B1649575 : Blo 868566 1649575 := bstep (se 1 (by rfl) ⟨1237181, by rfl⟩ : syracuseStep 1649575 = 2474363) B2474363
theorem B16723169 : Blo 868566 16723169 := bstep (se 2 (by rfl) ⟨6271188, by rfl⟩ : syracuseStep 16723169 = 12542377) B12542377
theorem B1650145 : Blo 868566 1650145 := bstep (se 2 (by rfl) ⟨618804, by rfl⟩ : syracuseStep 1650145 = 1237609) B1237609
theorem B481603643 : Blo 868566 481603643 := bstep (se 1 (by rfl) ⟨361202732, by rfl⟩ : syracuseStep 481603643 = 722405465) B722405465
theorem B14889095 : Blo 868566 14889095 := bstep (se 1 (by rfl) ⟨11166821, by rfl⟩ : syracuseStep 14889095 = 22333643) B22333643
theorem B1652051 : Blo 868566 1652051 := bstep (se 1 (by rfl) ⟨1239038, by rfl⟩ : syracuseStep 1652051 = 2478077) B2478077
theorem B4404617 : Blo 868566 4404617 := bstep (se 2 (by rfl) ⟨1651731, by rfl⟩ : syracuseStep 4404617 = 3303463) B3303463
theorem B10565315 : Blo 868566 10565315 := bstep (se 1 (by rfl) ⟨7923986, by rfl⟩ : syracuseStep 10565315 = 15847973) B15847973
theorem B10172569 : Blo 868566 10172569 := bstep (se 2 (by rfl) ⟨3814713, by rfl⟩ : syracuseStep 10172569 = 7629427) B7629427
theorem B2865403 : Blo 868566 2865403 := bstep (se 1 (by rfl) ⟨2149052, by rfl⟩ : syracuseStep 2865403 = 4298105) B4298105
theorem B28261871 : Blo 868566 28261871 := bstep (se 1 (by rfl) ⟨21196403, by rfl⟩ : syracuseStep 28261871 = 42392807) B42392807
theorem B2473679 : Blo 868566 2473679 := bstep (se 1 (by rfl) ⟨1855259, by rfl⟩ : syracuseStep 2473679 = 3710519) B3710519
theorem B1654967 : Blo 868566 1654967 := bstep (se 1 (by rfl) ⟨1241225, by rfl⟩ : syracuseStep 1654967 = 2482451) B2482451
theorem B868575 : Blo 868566 868575 := bstep (se 1 (by rfl) ⟨651431, by rfl⟩ : syracuseStep 868575 = 1302863) B1302863
theorem B868955 : Blo 868566 868955 := bstep (se 1 (by rfl) ⟨651716, by rfl⟩ : syracuseStep 868955 = 1303433) B1303433
theorem B869791 : Blo 868566 869791 := bstep (se 1 (by rfl) ⟨652343, by rfl⟩ : syracuseStep 869791 = 1304687) B1304687
theorem B869839 : Blo 868566 869839 := bstep (se 1 (by rfl) ⟨652379, by rfl⟩ : syracuseStep 869839 = 1304759) B1304759
theorem B870247 : Blo 868566 870247 := bstep (se 1 (by rfl) ⟨652685, by rfl⟩ : syracuseStep 870247 = 1305371) B1305371
theorem B9553909 : Blo 868566 9553909 := bstep (se 5 (by rfl) ⟨447839, by rfl⟩ : syracuseStep 9553909 = 895679) B895679
theorem B870815 : Blo 868566 870815 := bstep (se 1 (by rfl) ⟨653111, by rfl⟩ : syracuseStep 870815 = 1306223) B1306223
theorem B1395623 : Blo 868566 1395623 := bstep (se 1 (by rfl) ⟨1046717, by rfl⟩ : syracuseStep 1395623 = 2093435) B2093435
theorem B4181179 : Blo 868566 4181179 := bstep (se 1 (by rfl) ⟨3135884, by rfl⟩ : syracuseStep 4181179 = 6271769) B6271769
theorem B871839 : Blo 868566 871839 := bstep (se 1 (by rfl) ⟨653879, by rfl⟩ : syracuseStep 871839 = 1307759) B1307759
theorem B871871 : Blo 868566 871871 := bstep (se 1 (by rfl) ⟨653903, by rfl⟩ : syracuseStep 871871 = 1307807) B1307807
theorem B872091 : Blo 868566 872091 := bstep (se 1 (by rfl) ⟨654068, by rfl⟩ : syracuseStep 872091 = 1308137) B1308137
theorem B872127 : Blo 868566 872127 := bstep (se 1 (by rfl) ⟨654095, by rfl⟩ : syracuseStep 872127 = 1308191) B1308191
theorem B872143 : Blo 868566 872143 := bstep (se 1 (by rfl) ⟨654107, by rfl⟩ : syracuseStep 872143 = 1308215) B1308215
theorem B4968317 : Blo 868566 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B4412393 : Blo 868566 4412393 := bstep (se 2 (by rfl) ⟨1654647, by rfl⟩ : syracuseStep 4412393 = 3309295) B3309295
theorem B22565945 : Blo 868566 22565945 := bstep (se 2 (by rfl) ⟨8462229, by rfl⟩ : syracuseStep 22565945 = 16924459) B16924459
theorem B1856695 : Blo 868566 1856695 := bstep (se 1 (by rfl) ⟨1392521, by rfl⟩ : syracuseStep 1856695 = 2785043) B2785043
theorem B2938139 : Blo 868566 2938139 := bstep (se 1 (by rfl) ⟨2203604, by rfl⟩ : syracuseStep 2938139 = 4407209) B4407209
theorem B2479535 : Blo 868566 2479535 := bstep (se 1 (by rfl) ⟨1859651, by rfl⟩ : syracuseStep 2479535 = 3719303) B3719303
theorem B3298907 : Blo 868566 3298907 := bstep (se 1 (by rfl) ⟨2474180, by rfl⟩ : syracuseStep 3298907 = 4948361) B4948361
theorem B152491855 : Blo 868566 152491855 := bstep (se 1 (by rfl) ⟨114368891, by rfl⟩ : syracuseStep 152491855 = 228737783) B228737783
theorem B1955753 : Blo 868566 1955753 := bstep (se 2 (by rfl) ⟨733407, by rfl⟩ : syracuseStep 1955753 = 1466815) B1466815
theorem B8378579 : Blo 868566 8378579 := bstep (se 1 (by rfl) ⟨6283934, by rfl⟩ : syracuseStep 8378579 = 12567869) B12567869
theorem B7428419 : Blo 868566 7428419 := bstep (se 1 (by rfl) ⟨5571314, by rfl⟩ : syracuseStep 7428419 = 11142629) B11142629
theorem B1956383 : Blo 868566 1956383 := bstep (se 1 (by rfl) ⟨1467287, by rfl⟩ : syracuseStep 1956383 = 2934575) B2934575
theorem B1956959 : Blo 868566 1956959 := bstep (se 1 (by rfl) ⟨1467719, by rfl⟩ : syracuseStep 1956959 = 2935439) B2935439
theorem B1465897 : Blo 868566 1465897 := bstep (se 2 (by rfl) ⟨549711, by rfl⟩ : syracuseStep 1465897 = 1099423) B1099423
theorem B1958075 : Blo 868566 1958075 := bstep (se 1 (by rfl) ⟨1468556, by rfl⟩ : syracuseStep 1958075 = 2937113) B2937113
theorem B2941433 : Blo 868566 2941433 := bstep (se 2 (by rfl) ⟨1103037, by rfl⟩ : syracuseStep 2941433 = 2206075) B2206075
theorem B1467119 : Blo 868566 1467119 := bstep (se 1 (by rfl) ⟨1100339, by rfl⟩ : syracuseStep 1467119 = 2200679) B2200679
theorem B1467551 : Blo 868566 1467551 := bstep (se 1 (by rfl) ⟨1100663, by rfl⟩ : syracuseStep 1467551 = 2201327) B2201327
theorem B1861103 : Blo 868566 1861103 := bstep (se 1 (by rfl) ⟨1395827, by rfl⟩ : syracuseStep 1861103 = 2791655) B2791655
theorem B1959515 : Blo 868566 1959515 := bstep (se 1 (by rfl) ⟨1469636, by rfl⟩ : syracuseStep 1959515 = 2939273) B2939273
theorem B6613001 : Blo 868566 6613001 := bstep (se 2 (by rfl) ⟨2479875, by rfl⟩ : syracuseStep 6613001 = 4959751) B4959751
theorem B3303449 : Blo 868566 3303449 := bstep (se 2 (by rfl) ⟨1238793, by rfl⟩ : syracuseStep 3303449 = 2477587) B2477587
theorem B2943215 : Blo 868566 2943215 := bstep (se 1 (by rfl) ⟨2207411, by rfl⟩ : syracuseStep 2943215 = 4414823) B4414823
theorem B1304831 : Blo 868566 1304831 := bstep (se 1 (by rfl) ⟨978623, by rfl⟩ : syracuseStep 1304831 = 1957247) B1957247
theorem B6613487 : Blo 868566 6613487 := bstep (se 1 (by rfl) ⟨4960115, by rfl⟩ : syracuseStep 6613487 = 9920231) B9920231
theorem B1960559 : Blo 868566 1960559 := bstep (se 1 (by rfl) ⟨1470419, by rfl⟩ : syracuseStep 1960559 = 2940839) B2940839
theorem B28240595 : Blo 868566 28240595 := bstep (se 1 (by rfl) ⟨21180446, by rfl⟩ : syracuseStep 28240595 = 42360893) B42360893
theorem B1960937 : Blo 868566 1960937 := bstep (se 2 (by rfl) ⟨735351, by rfl⟩ : syracuseStep 1960937 = 1470703) B1470703
theorem B1305593 : Blo 868566 1305593 := bstep (se 2 (by rfl) ⟨489597, by rfl⟩ : syracuseStep 1305593 = 979195) B979195
theorem B14871599 : Blo 868566 14871599 := bstep (se 1 (by rfl) ⟨11153699, by rfl⟩ : syracuseStep 14871599 = 22307399) B22307399
theorem B2944295 : Blo 868566 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B1862975 : Blo 868566 1862975 := bstep (se 1 (by rfl) ⟨1397231, by rfl⟩ : syracuseStep 1862975 = 2794463) B2794463
theorem B1306535 : Blo 868566 1306535 := bstep (se 1 (by rfl) ⟨979901, by rfl⟩ : syracuseStep 1306535 = 1959803) B1959803
theorem B1568951 : Blo 868566 1568951 := bstep (se 1 (by rfl) ⟨1176713, by rfl⟩ : syracuseStep 1568951 = 2353427) B2353427
theorem B3141823 : Blo 868566 3141823 := bstep (se 1 (by rfl) ⟨2356367, by rfl⟩ : syracuseStep 3141823 = 4712735) B4712735
theorem B2093339 : Blo 868566 2093339 := bstep (se 1 (by rfl) ⟨1570004, by rfl⟩ : syracuseStep 2093339 = 3140009) B3140009
theorem B1962431 : Blo 868566 1962431 := bstep (se 1 (by rfl) ⟨1471823, by rfl⟩ : syracuseStep 1962431 = 2943647) B2943647
theorem B1962809 : Blo 868566 1962809 := bstep (se 2 (by rfl) ⟨736053, by rfl⟩ : syracuseStep 1962809 = 1472107) B1472107
theorem B1307519 : Blo 868566 1307519 := bstep (se 1 (by rfl) ⟨980639, by rfl⟩ : syracuseStep 1307519 = 1961279) B1961279
theorem B2094241 : Blo 868566 2094241 := bstep (se 2 (by rfl) ⟨785340, by rfl⟩ : syracuseStep 2094241 = 1570681) B1570681
theorem B1471675 : Blo 868566 1471675 := bstep (se 1 (by rfl) ⟨1103756, by rfl⟩ : syracuseStep 1471675 = 2207513) B2207513
theorem B1307951 : Blo 868566 1307951 := bstep (se 1 (by rfl) ⟨980963, by rfl⟩ : syracuseStep 1307951 = 1961927) B1961927
theorem B3175807 : Blo 868566 3175807 := bstep (se 1 (by rfl) ⟨2381855, by rfl⟩ : syracuseStep 3175807 = 4763711) B4763711
theorem B981607 : Blo 868566 981607 := bstep (se 1 (by rfl) ⟨736205, by rfl⟩ : syracuseStep 981607 = 1472411) B1472411
theorem B165411935 : Blo 868566 165411935 := bstep (se 1 (by rfl) ⟨124058951, by rfl⟩ : syracuseStep 165411935 = 248117903) B248117903
theorem B48236057 : Blo 868566 48236057 := bstep (se 2 (by rfl) ⟨18088521, by rfl⟩ : syracuseStep 48236057 = 36177043) B36177043
theorem B135989711 : Blo 868566 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B3312211 : Blo 868566 3312211 := bstep (se 1 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 3312211 = 4968317) B4968317
theorem B15043963 : Blo 868566 15043963 := bstep (se 1 (by rfl) ⟨11282972, by rfl⟩ : syracuseStep 15043963 = 22565945) B22565945
theorem B2199271 : Blo 868566 2199271 := bstep (se 1 (by rfl) ⟨1649453, by rfl⟩ : syracuseStep 2199271 = 3298907) B3298907
theorem B2199433 : Blo 868566 2199433 := bstep (se 2 (by rfl) ⟨824787, by rfl⟩ : syracuseStep 2199433 = 1649575) B1649575
theorem B4952279 : Blo 868566 4952279 := bstep (se 1 (by rfl) ⟨3714209, by rfl⟩ : syracuseStep 4952279 = 7428419) B7428419
theorem B5574905 : Blo 868566 5574905 := bstep (se 2 (by rfl) ⟨2090589, by rfl⟩ : syracuseStep 5574905 = 4181179) B4181179
theorem B2200193 : Blo 868566 2200193 := bstep (se 2 (by rfl) ⟨825072, by rfl⟩ : syracuseStep 2200193 = 1650145) B1650145
theorem B11146319 : Blo 868566 11146319 := bstep (se 1 (by rfl) ⟨8359739, by rfl⟩ : syracuseStep 11146319 = 16719479) B16719479
theorem B2202299 : Blo 868566 2202299 := bstep (se 1 (by rfl) ⟨1651724, by rfl⟩ : syracuseStep 2202299 = 3303449) B3303449
theorem B2792321 : Blo 868566 2792321 := bstep (se 2 (by rfl) ⟨1047120, by rfl⟩ : syracuseStep 2792321 = 2094241) B2094241
theorem B4234409 : Blo 868566 4234409 := bstep (se 2 (by rfl) ⟨1587903, by rfl⟩ : syracuseStep 4234409 = 3175807) B3175807
theorem B11148779 : Blo 868566 11148779 := bstep (se 1 (by rfl) ⟨8361584, by rfl⟩ : syracuseStep 11148779 = 16723169) B16723169
theorem B321069095 : Blo 868566 321069095 := bstep (se 1 (by rfl) ⟨240801821, by rfl⟩ : syracuseStep 321069095 = 481603643) B481603643
theorem B6596477 : Blo 868566 6596477 := bstep (se 3 (by rfl) ⟨1236839, by rfl⟩ : syracuseStep 6596477 = 2473679) B2473679
theorem B110274623 : Blo 868566 110274623 := bstep (se 1 (by rfl) ⟨82705967, by rfl⟩ : syracuseStep 110274623 = 165411935) B165411935
theorem B2206511 : Blo 868566 2206511 := bstep (se 1 (by rfl) ⟨1654883, by rfl⟩ : syracuseStep 2206511 = 3309767) B3309767
theorem B3713921 : Blo 868566 3713921 := bstep (se 2 (by rfl) ⟨1392720, by rfl⟩ : syracuseStep 3713921 = 2785441) B2785441
theorem B930415 : Blo 868566 930415 := bstep (se 1 (by rfl) ⟨697811, by rfl⟩ : syracuseStep 930415 = 1395623) B1395623
theorem B5944175 : Blo 868566 5944175 := bstep (se 1 (by rfl) ⟨4458131, by rfl⟩ : syracuseStep 5944175 = 8916263) B8916263
theorem B1653023 : Blo 868566 1653023 := bstep (se 1 (by rfl) ⟨1239767, by rfl⟩ : syracuseStep 1653023 = 2479535) B2479535
theorem B4962941 : Blo 868566 4962941 := bstep (se 3 (by rfl) ⟨930551, by rfl⟩ : syracuseStep 4962941 = 1861103) B1861103
theorem B4176623 : Blo 868566 4176623 := bstep (se 1 (by rfl) ⟨3132467, by rfl⟩ : syracuseStep 4176623 = 6264935) B6264935
theorem B5585719 : Blo 868566 5585719 := bstep (se 1 (by rfl) ⟨4189289, by rfl⟩ : syracuseStep 5585719 = 8378579) B8378579
theorem B4964399 : Blo 868566 4964399 := bstep (se 1 (by rfl) ⟨3723299, by rfl⟩ : syracuseStep 4964399 = 7446599) B7446599
theorem B2933063 : Blo 868566 2933063 := bstep (se 1 (by rfl) ⟨2199797, by rfl⟩ : syracuseStep 2933063 = 4399595) B4399595
theorem B2933711 : Blo 868566 2933711 := bstep (se 1 (by rfl) ⟨2200283, by rfl⟩ : syracuseStep 2933711 = 4400567) B4400567
theorem B4408667 : Blo 868566 4408667 := bstep (se 1 (by rfl) ⟨3306500, by rfl⟩ : syracuseStep 4408667 = 6613001) B6613001
theorem B869887 : Blo 868566 869887 := bstep (se 1 (by rfl) ⟨652415, by rfl⟩ : syracuseStep 869887 = 1304831) B1304831
theorem B2475593 : Blo 868566 2475593 := bstep (se 2 (by rfl) ⟨928347, by rfl⟩ : syracuseStep 2475593 = 1856695) B1856695
theorem B4408991 : Blo 868566 4408991 := bstep (se 1 (by rfl) ⟨3306743, by rfl⟩ : syracuseStep 4408991 = 6613487) B6613487
theorem B18827063 : Blo 868566 18827063 := bstep (se 1 (by rfl) ⟨14120297, by rfl⟩ : syracuseStep 18827063 = 28240595) B28240595
theorem B870395 : Blo 868566 870395 := bstep (se 1 (by rfl) ⟨652796, by rfl⟩ : syracuseStep 870395 = 1305593) B1305593
theorem B9914399 : Blo 868566 9914399 := bstep (se 1 (by rfl) ⟨7435799, by rfl⟩ : syracuseStep 9914399 = 14871599) B14871599
theorem B871023 : Blo 868566 871023 := bstep (se 1 (by rfl) ⟨653267, by rfl⟩ : syracuseStep 871023 = 1306535) B1306535
theorem B1395559 : Blo 868566 1395559 := bstep (se 1 (by rfl) ⟨1046669, by rfl⟩ : syracuseStep 1395559 = 2093339) B2093339
theorem B3820537 : Blo 868566 3820537 := bstep (se 2 (by rfl) ⟨1432701, by rfl⟩ : syracuseStep 3820537 = 2865403) B2865403
theorem B871679 : Blo 868566 871679 := bstep (se 1 (by rfl) ⟨653759, by rfl⟩ : syracuseStep 871679 = 1307519) B1307519
theorem B871967 : Blo 868566 871967 := bstep (se 1 (by rfl) ⟨653975, by rfl⟩ : syracuseStep 871967 = 1307951) B1307951
theorem B1101367 : Blo 868566 1101367 := bstep (se 1 (by rfl) ⟨826025, by rfl⟩ : syracuseStep 1101367 = 1652051) B1652051
theorem B2936411 : Blo 868566 2936411 := bstep (se 1 (by rfl) ⟨2202308, by rfl⟩ : syracuseStep 2936411 = 4404617) B4404617
theorem B8703713 : Blo 868566 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B1954529 : Blo 868566 1954529 := bstep (se 2 (by rfl) ⟨732948, by rfl⟩ : syracuseStep 1954529 = 1465897) B1465897
theorem B1103311 : Blo 868566 1103311 := bstep (se 1 (by rfl) ⟨827483, by rfl⟩ : syracuseStep 1103311 = 1654967) B1654967
theorem B1988587 : Blo 868566 1988587 := bstep (se 1 (by rfl) ⟨1491440, by rfl⟩ : syracuseStep 1988587 = 2982881) B2982881
theorem B142891199 : Blo 868566 142891199 := bstep (se 1 (by rfl) ⟨107168399, by rfl⟩ : syracuseStep 142891199 = 214336799) B214336799
theorem B14867225 : Blo 868566 14867225 := bstep (se 2 (by rfl) ⟨5575209, by rfl⟩ : syracuseStep 14867225 = 11150419) B11150419
theorem B12738545 : Blo 868566 12738545 := bstep (se 2 (by rfl) ⟨4776954, by rfl⟩ : syracuseStep 12738545 = 9553909) B9553909
theorem B2941595 : Blo 868566 2941595 := bstep (se 1 (by rfl) ⟨2206196, by rfl⟩ : syracuseStep 2941595 = 4412393) B4412393
theorem B1958759 : Blo 868566 1958759 := bstep (se 1 (by rfl) ⟨1469069, by rfl⟩ : syracuseStep 1958759 = 2938139) B2938139
theorem B1303835 : Blo 868566 1303835 := bstep (se 1 (by rfl) ⟨977876, by rfl⟩ : syracuseStep 1303835 = 1955753) B1955753
theorem B1304255 : Blo 868566 1304255 := bstep (se 1 (by rfl) ⟨978191, by rfl⟩ : syracuseStep 1304255 = 1956383) B1956383
theorem B1468111 : Blo 868566 1468111 := bstep (se 1 (by rfl) ⟨1101083, by rfl⟩ : syracuseStep 1468111 = 2202167) B2202167
theorem B1304639 : Blo 868566 1304639 := bstep (se 1 (by rfl) ⟨978479, by rfl⟩ : syracuseStep 1304639 = 1956959) B1956959
theorem B1305383 : Blo 868566 1305383 := bstep (se 1 (by rfl) ⟨979037, by rfl⟩ : syracuseStep 1305383 = 1958075) B1958075
theorem B4189097 : Blo 868566 4189097 := bstep (se 2 (by rfl) ⟨1570911, by rfl⟩ : syracuseStep 4189097 = 3141823) B3141823
theorem B1960955 : Blo 868566 1960955 := bstep (se 1 (by rfl) ⟨1470716, by rfl⟩ : syracuseStep 1960955 = 2941433) B2941433
theorem B978079 : Blo 868566 978079 := bstep (se 1 (by rfl) ⟨733559, by rfl⟩ : syracuseStep 978079 = 1467119) B1467119
theorem B978367 : Blo 868566 978367 := bstep (se 1 (by rfl) ⟨733775, by rfl⟩ : syracuseStep 978367 = 1467551) B1467551
theorem B1306343 : Blo 868566 1306343 := bstep (se 1 (by rfl) ⟨979757, by rfl⟩ : syracuseStep 1306343 = 1959515) B1959515
theorem B1962143 : Blo 868566 1962143 := bstep (se 1 (by rfl) ⟨1471607, by rfl⟩ : syracuseStep 1962143 = 2943215) B2943215
theorem B1962233 : Blo 868566 1962233 := bstep (se 2 (by rfl) ⟨735837, by rfl⟩ : syracuseStep 1962233 = 1471675) B1471675
theorem B1307039 : Blo 868566 1307039 := bstep (se 1 (by rfl) ⟨980279, by rfl⟩ : syracuseStep 1307039 = 1960559) B1960559
theorem B1307291 : Blo 868566 1307291 := bstep (se 1 (by rfl) ⟨980468, by rfl⟩ : syracuseStep 1307291 = 1960937) B1960937
theorem B1962863 : Blo 868566 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B1241983 : Blo 868566 1241983 := bstep (se 1 (by rfl) ⟨931487, by rfl⟩ : syracuseStep 1241983 = 1862975) B1862975
theorem B203322473 : Blo 868566 203322473 := bstep (se 2 (by rfl) ⟨76245927, by rfl⟩ : syracuseStep 203322473 = 152491855) B152491855
theorem B9926063 : Blo 868566 9926063 := bstep (se 1 (by rfl) ⟨7444547, by rfl⟩ : syracuseStep 9926063 = 14889095) B14889095
theorem B1045967 : Blo 868566 1045967 := bstep (se 1 (by rfl) ⟨784475, by rfl⟩ : syracuseStep 1045967 = 1568951) B1568951
theorem B42300953 : Blo 868566 42300953 := bstep (se 2 (by rfl) ⟨15862857, by rfl⟩ : syracuseStep 42300953 = 31725715) B31725715
theorem B13563425 : Blo 868566 13563425 := bstep (se 2 (by rfl) ⟨5086284, by rfl⟩ : syracuseStep 13563425 = 10172569) B10172569
theorem B1308287 : Blo 868566 1308287 := bstep (se 1 (by rfl) ⟨981215, by rfl⟩ : syracuseStep 1308287 = 1962431) B1962431
theorem B1308539 : Blo 868566 1308539 := bstep (se 1 (by rfl) ⟨981404, by rfl⟩ : syracuseStep 1308539 = 1962809) B1962809
theorem B1308809 : Blo 868566 1308809 := bstep (se 2 (by rfl) ⟨490803, by rfl⟩ : syracuseStep 1308809 = 981607) B981607
theorem B7043543 : Blo 868566 7043543 := bstep (se 1 (by rfl) ⟨5282657, by rfl⟩ : syracuseStep 7043543 = 10565315) B10565315
theorem B9927521 : Blo 868566 9927521 := bstep (se 2 (by rfl) ⟨3722820, by rfl⟩ : syracuseStep 9927521 = 7445641) B7445641
theorem B18841247 : Blo 868566 18841247 := bstep (se 1 (by rfl) ⟨14130935, by rfl⟩ : syracuseStep 18841247 = 28261871) B28261871
theorem B3309599 : Blo 868566 3309599 := bstep (se 1 (by rfl) ⟨2482199, by rfl⟩ : syracuseStep 3309599 = 4964399) B4964399
theorem B12551375 : Blo 868566 12551375 := bstep (se 1 (by rfl) ⟨9413531, by rfl⟩ : syracuseStep 12551375 = 18827063) B18827063
theorem B2789245 : Blo 868566 2789245 := bstep (se 3 (by rfl) ⟨522983, by rfl⟩ : syracuseStep 2789245 = 1045967) B1045967
theorem B95260799 : Blo 868566 95260799 := bstep (se 1 (by rfl) ⟨71445599, by rfl⟩ : syracuseStep 95260799 = 142891199) B142891199
theorem B20058617 : Blo 868566 20058617 := bstep (se 2 (by rfl) ⟨7521981, by rfl⟩ : syracuseStep 20058617 = 15043963) B15043963
theorem B2822939 : Blo 868566 2822939 := bstep (se 1 (by rfl) ⟨2117204, by rfl⟩ : syracuseStep 2822939 = 4234409) B4234409
theorem B8492363 : Blo 868566 8492363 := bstep (se 1 (by rfl) ⟨6369272, by rfl⟩ : syracuseStep 8492363 = 12738545) B12738545
theorem B214046063 : Blo 868566 214046063 := bstep (se 1 (by rfl) ⟨160534547, by rfl⟩ : syracuseStep 214046063 = 321069095) B321069095
theorem B4397651 : Blo 868566 4397651 := bstep (se 1 (by rfl) ⟨3298238, by rfl⟩ : syracuseStep 4397651 = 6596477) B6596477
theorem B2792731 : Blo 868566 2792731 := bstep (se 1 (by rfl) ⟨2094548, by rfl⟩ : syracuseStep 2792731 = 4189097) B4189097
theorem B7447625 : Blo 868566 7447625 := bstep (se 2 (by rfl) ⟨2792859, by rfl⟩ : syracuseStep 7447625 = 5585719) B5585719
theorem B4695695 : Blo 868566 4695695 := bstep (se 1 (by rfl) ⟨3521771, by rfl⟩ : syracuseStep 4695695 = 7043543) B7043543
theorem B23209901 : Blo 868566 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B12560831 : Blo 868566 12560831 := bstep (se 1 (by rfl) ⟨9420623, by rfl⟩ : syracuseStep 12560831 = 18841247) B18841247
theorem B32157371 : Blo 868566 32157371 := bstep (se 1 (by rfl) ⟨24118028, by rfl⟩ : syracuseStep 32157371 = 48236057) B48236057
theorem B1650395 : Blo 868566 1650395 := bstep (se 1 (by rfl) ⟨1237796, by rfl⟩ : syracuseStep 1650395 = 2475593) B2475593
theorem B3716603 : Blo 868566 3716603 := bstep (se 1 (by rfl) ⟨2787452, by rfl⟩ : syracuseStep 3716603 = 5574905) B5574905
theorem B9911483 : Blo 868566 9911483 := bstep (se 1 (by rfl) ⟨7433612, by rfl⟩ : syracuseStep 9911483 = 14867225) B14867225
theorem B2932361 : Blo 868566 2932361 := bstep (se 2 (by rfl) ⟨1099635, by rfl⟩ : syracuseStep 2932361 = 2199271) B2199271
theorem B2932577 : Blo 868566 2932577 := bstep (se 2 (by rfl) ⟨1099716, by rfl⟩ : syracuseStep 2932577 = 2199433) B2199433
theorem B869223 : Blo 868566 869223 := bstep (se 1 (by rfl) ⟨651917, by rfl⟩ : syracuseStep 869223 = 1303835) B1303835
theorem B869503 : Blo 868566 869503 := bstep (se 1 (by rfl) ⟨652127, by rfl⟩ : syracuseStep 869503 = 1304255) B1304255
theorem B1655977 : Blo 868566 1655977 := bstep (se 2 (by rfl) ⟨620991, by rfl⟩ : syracuseStep 1655977 = 1241983) B1241983
theorem B869759 : Blo 868566 869759 := bstep (se 1 (by rfl) ⟨652319, by rfl⟩ : syracuseStep 869759 = 1304639) B1304639
theorem B73516415 : Blo 868566 73516415 := bstep (se 1 (by rfl) ⟨55137311, by rfl⟩ : syracuseStep 73516415 = 110274623) B110274623
theorem B870255 : Blo 868566 870255 := bstep (se 1 (by rfl) ⟨652691, by rfl⟩ : syracuseStep 870255 = 1305383) B1305383
theorem B2475947 : Blo 868566 2475947 := bstep (se 1 (by rfl) ⟨1856960, by rfl⟩ : syracuseStep 2475947 = 3713921) B3713921
theorem B870895 : Blo 868566 870895 := bstep (se 1 (by rfl) ⟨653171, by rfl⟩ : syracuseStep 870895 = 1306343) B1306343
theorem B871359 : Blo 868566 871359 := bstep (se 1 (by rfl) ⟨653519, by rfl⟩ : syracuseStep 871359 = 1307039) B1307039
theorem B871527 : Blo 868566 871527 := bstep (se 1 (by rfl) ⟨653645, by rfl⟩ : syracuseStep 871527 = 1307291) B1307291
theorem B135548315 : Blo 868566 135548315 := bstep (se 1 (by rfl) ⟨101661236, by rfl⟩ : syracuseStep 135548315 = 203322473) B203322473
theorem B28200635 : Blo 868566 28200635 := bstep (se 1 (by rfl) ⟨21150476, by rfl⟩ : syracuseStep 28200635 = 42300953) B42300953
theorem B872191 : Blo 868566 872191 := bstep (se 1 (by rfl) ⟨654143, by rfl⟩ : syracuseStep 872191 = 1308287) B1308287
theorem B872359 : Blo 868566 872359 := bstep (se 1 (by rfl) ⟨654269, by rfl⟩ : syracuseStep 872359 = 1308539) B1308539
theorem B872539 : Blo 868566 872539 := bstep (se 1 (by rfl) ⟨654404, by rfl⟩ : syracuseStep 872539 = 1308809) B1308809
theorem B1102015 : Blo 868566 1102015 := bstep (se 1 (by rfl) ⟨826511, by rfl⟩ : syracuseStep 1102015 = 1653023) B1653023
theorem B1955375 : Blo 868566 1955375 := bstep (se 1 (by rfl) ⟨1466531, by rfl⟩ : syracuseStep 1955375 = 2933063) B2933063
theorem B1955807 : Blo 868566 1955807 := bstep (se 1 (by rfl) ⟨1466855, by rfl⟩ : syracuseStep 1955807 = 2933711) B2933711
theorem B2939111 : Blo 868566 2939111 := bstep (se 1 (by rfl) ⟨2204333, by rfl⟩ : syracuseStep 2939111 = 4408667) B4408667
theorem B2939327 : Blo 868566 2939327 := bstep (se 1 (by rfl) ⟨2204495, by rfl⟩ : syracuseStep 2939327 = 4408991) B4408991
theorem B6609599 : Blo 868566 6609599 := bstep (se 1 (by rfl) ⟨4957199, by rfl⟩ : syracuseStep 6609599 = 9914399) B9914399
theorem B90659807 : Blo 868566 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B1957481 : Blo 868566 1957481 := bstep (se 2 (by rfl) ⟨734055, by rfl⟩ : syracuseStep 1957481 = 1468111) B1468111
theorem B1957607 : Blo 868566 1957607 := bstep (se 1 (by rfl) ⟨1468205, by rfl⟩ : syracuseStep 1957607 = 2936411) B2936411
theorem B3301519 : Blo 868566 3301519 := bstep (se 1 (by rfl) ⟨2476139, by rfl⟩ : syracuseStep 3301519 = 4952279) B4952279
theorem B1466795 : Blo 868566 1466795 := bstep (se 1 (by rfl) ⟨1100096, by rfl⟩ : syracuseStep 1466795 = 2200193) B2200193
theorem B1303019 : Blo 868566 1303019 := bstep (se 1 (by rfl) ⟨977264, by rfl⟩ : syracuseStep 1303019 = 1954529) B1954529
theorem B7430879 : Blo 868566 7430879 := bstep (se 1 (by rfl) ⟨5573159, by rfl⟩ : syracuseStep 7430879 = 11146319) B11146319
theorem B4416281 : Blo 868566 4416281 := bstep (se 2 (by rfl) ⟨1656105, by rfl⟩ : syracuseStep 4416281 = 3312211) B3312211
theorem B1860745 : Blo 868566 1860745 := bstep (se 2 (by rfl) ⟨697779, by rfl⟩ : syracuseStep 1860745 = 1395559) B1395559
theorem B1304105 : Blo 868566 1304105 := bstep (se 2 (by rfl) ⟨489039, by rfl⟩ : syracuseStep 1304105 = 978079) B978079
theorem B1468199 : Blo 868566 1468199 := bstep (se 1 (by rfl) ⟨1101149, by rfl⟩ : syracuseStep 1468199 = 2202299) B2202299
theorem B1304489 : Blo 868566 1304489 := bstep (se 2 (by rfl) ⟨489183, by rfl⟩ : syracuseStep 1304489 = 978367) B978367
theorem B1861547 : Blo 868566 1861547 := bstep (se 1 (by rfl) ⟨1396160, by rfl⟩ : syracuseStep 1861547 = 2792321) B2792321
theorem B1468489 : Blo 868566 1468489 := bstep (se 2 (by rfl) ⟨550683, by rfl⟩ : syracuseStep 1468489 = 1101367) B1101367
theorem B7432519 : Blo 868566 7432519 := bstep (se 1 (by rfl) ⟨5574389, by rfl⟩ : syracuseStep 7432519 = 11148779) B11148779
theorem B20376197 : Blo 868566 20376197 := bstep (se 4 (by rfl) ⟨1910268, by rfl⟩ : syracuseStep 20376197 = 3820537) B3820537
theorem B1961063 : Blo 868566 1961063 := bstep (se 1 (by rfl) ⟨1470797, by rfl⟩ : syracuseStep 1961063 = 2941595) B2941595
theorem B1305839 : Blo 868566 1305839 := bstep (se 1 (by rfl) ⟨979379, by rfl⟩ : syracuseStep 1305839 = 1958759) B1958759
theorem B1240553 : Blo 868566 1240553 := bstep (se 2 (by rfl) ⟨465207, by rfl⟩ : syracuseStep 1240553 = 930415) B930415
theorem B1471007 : Blo 868566 1471007 := bstep (se 1 (by rfl) ⟨1103255, by rfl⟩ : syracuseStep 1471007 = 2206511) B2206511
theorem B1471081 : Blo 868566 1471081 := bstep (se 2 (by rfl) ⟨551655, by rfl⟩ : syracuseStep 1471081 = 1103311) B1103311
theorem B11137661 : Blo 868566 11137661 := bstep (se 3 (by rfl) ⟨2088311, by rfl⟩ : syracuseStep 11137661 = 4176623) B4176623
theorem B1307303 : Blo 868566 1307303 := bstep (se 1 (by rfl) ⟨980477, by rfl⟩ : syracuseStep 1307303 = 1960955) B1960955
theorem B2651449 : Blo 868566 2651449 := bstep (se 2 (by rfl) ⟨994293, by rfl⟩ : syracuseStep 2651449 = 1988587) B1988587
theorem B1308095 : Blo 868566 1308095 := bstep (se 1 (by rfl) ⟨981071, by rfl⟩ : syracuseStep 1308095 = 1962143) B1962143
theorem B1308155 : Blo 868566 1308155 := bstep (se 1 (by rfl) ⟨981116, by rfl⟩ : syracuseStep 1308155 = 1962233) B1962233
theorem B3962783 : Blo 868566 3962783 := bstep (se 1 (by rfl) ⟨2972087, by rfl⟩ : syracuseStep 3962783 = 5944175) B5944175
theorem B1308575 : Blo 868566 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B6617375 : Blo 868566 6617375 := bstep (se 1 (by rfl) ⟨4963031, by rfl⟩ : syracuseStep 6617375 = 9926063) B9926063
theorem B9042283 : Blo 868566 9042283 := bstep (se 1 (by rfl) ⟨6781712, by rfl⟩ : syracuseStep 9042283 = 13563425) B13563425
theorem B3308627 : Blo 868566 3308627 := bstep (se 1 (by rfl) ⟨2481470, by rfl⟩ : syracuseStep 3308627 = 4962941) B4962941
theorem B6618347 : Blo 868566 6618347 := bstep (se 1 (by rfl) ⟨4963760, by rfl⟩ : syracuseStep 6618347 = 9927521) B9927521
theorem B63507199 : Blo 868566 63507199 := bstep (se 1 (by rfl) ⟨47630399, by rfl⟩ : syracuseStep 63507199 = 95260799) B95260799
theorem B13372411 : Blo 868566 13372411 := bstep (se 1 (by rfl) ⟨10029308, by rfl⟩ : syracuseStep 13372411 = 20058617) B20058617
theorem B4953919 : Blo 868566 4953919 := bstep (se 1 (by rfl) ⟨3715439, by rfl⟩ : syracuseStep 4953919 = 7430879) B7430879
theorem B15473267 : Blo 868566 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B4401053 : Blo 868566 4401053 := bstep (se 3 (by rfl) ⟨825197, by rfl⟩ : syracuseStep 4401053 = 1650395) B1650395
theorem B2205751 : Blo 868566 2205751 := bstep (se 1 (by rfl) ⟨1654313, by rfl⟩ : syracuseStep 2205751 = 3308627) B3308627
theorem B2206399 : Blo 868566 2206399 := bstep (se 1 (by rfl) ⟨1654799, by rfl⟩ : syracuseStep 2206399 = 3309599) B3309599
theorem B4402025 : Blo 868566 4402025 := bstep (se 2 (by rfl) ⟨1650759, by rfl⟩ : syracuseStep 4402025 = 3301519) B3301519
theorem B8367583 : Blo 868566 8367583 := bstep (se 1 (by rfl) ⟨6275687, by rfl⟩ : syracuseStep 8367583 = 12551375) B12551375
theorem B1650631 : Blo 868566 1650631 := bstep (se 1 (by rfl) ⟨1237973, by rfl⟩ : syracuseStep 1650631 = 2475947) B2475947
theorem B2207969 : Blo 868566 2207969 := bstep (se 2 (by rfl) ⟨827988, by rfl⟩ : syracuseStep 2207969 = 1655977) B1655977
theorem B9910025 : Blo 868566 9910025 := bstep (se 2 (by rfl) ⟨3716259, by rfl⟩ : syracuseStep 9910025 = 7432519) B7432519
theorem B1881959 : Blo 868566 1881959 := bstep (se 1 (by rfl) ⟨1411469, by rfl⟩ : syracuseStep 1881959 = 2822939) B2822939
theorem B2931767 : Blo 868566 2931767 := bstep (se 1 (by rfl) ⟨2198825, by rfl⟩ : syracuseStep 2931767 = 4397651) B4397651
theorem B4406399 : Blo 868566 4406399 := bstep (se 1 (by rfl) ⟨3304799, by rfl⟩ : syracuseStep 4406399 = 6609599) B6609599
theorem B60439871 : Blo 868566 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B4964125 : Blo 868566 4964125 := bstep (se 3 (by rfl) ⟨930773, by rfl⟩ : syracuseStep 4964125 = 1861547) B1861547
theorem B868679 : Blo 868566 868679 := bstep (se 1 (by rfl) ⟨651509, by rfl⟩ : syracuseStep 868679 = 1303019) B1303019
theorem B4965083 : Blo 868566 4965083 := bstep (se 1 (by rfl) ⟨3723812, by rfl⟩ : syracuseStep 4965083 = 7447625) B7447625
theorem B869403 : Blo 868566 869403 := bstep (se 1 (by rfl) ⟨652052, by rfl⟩ : syracuseStep 869403 = 1304105) B1304105
theorem B3130463 : Blo 868566 3130463 := bstep (se 1 (by rfl) ⟨2347847, by rfl⟩ : syracuseStep 3130463 = 4695695) B4695695
theorem B869659 : Blo 868566 869659 := bstep (se 1 (by rfl) ⟨652244, by rfl⟩ : syracuseStep 869659 = 1304489) B1304489
theorem B8373887 : Blo 868566 8373887 := bstep (se 1 (by rfl) ⟨6280415, by rfl⟩ : syracuseStep 8373887 = 12560831) B12560831
theorem B13584131 : Blo 868566 13584131 := bstep (se 1 (by rfl) ⟨10188098, by rfl⟩ : syracuseStep 13584131 = 20376197) B20376197
theorem B870559 : Blo 868566 870559 := bstep (se 1 (by rfl) ⟨652919, by rfl⟩ : syracuseStep 870559 = 1305839) B1305839
theorem B7425107 : Blo 868566 7425107 := bstep (se 1 (by rfl) ⟨5568830, by rfl⟩ : syracuseStep 7425107 = 11137661) B11137661
theorem B871535 : Blo 868566 871535 := bstep (se 1 (by rfl) ⟨653651, by rfl⟩ : syracuseStep 871535 = 1307303) B1307303
theorem B872063 : Blo 868566 872063 := bstep (se 1 (by rfl) ⟨654047, by rfl⟩ : syracuseStep 872063 = 1308095) B1308095
theorem B2477735 : Blo 868566 2477735 := bstep (se 1 (by rfl) ⟨1858301, by rfl⟩ : syracuseStep 2477735 = 3716603) B3716603
theorem B872103 : Blo 868566 872103 := bstep (se 1 (by rfl) ⟨654077, by rfl⟩ : syracuseStep 872103 = 1308155) B1308155
theorem B2641855 : Blo 868566 2641855 := bstep (se 1 (by rfl) ⟨1981391, by rfl⟩ : syracuseStep 2641855 = 3962783) B3962783
theorem B872383 : Blo 868566 872383 := bstep (se 1 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 872383 = 1308575) B1308575
theorem B4411583 : Blo 868566 4411583 := bstep (se 1 (by rfl) ⟨3308687, by rfl⟩ : syracuseStep 4411583 = 6617375) B6617375
theorem B3723641 : Blo 868566 3723641 := bstep (se 2 (by rfl) ⟨1396365, by rfl⟩ : syracuseStep 3723641 = 2792731) B2792731
theorem B6607655 : Blo 868566 6607655 := bstep (se 1 (by rfl) ⟨4955741, by rfl⟩ : syracuseStep 6607655 = 9911483) B9911483
theorem B4412231 : Blo 868566 4412231 := bstep (se 1 (by rfl) ⟨3309173, by rfl⟩ : syracuseStep 4412231 = 6618347) B6618347
theorem B1954907 : Blo 868566 1954907 := bstep (se 1 (by rfl) ⟨1466180, by rfl⟩ : syracuseStep 1954907 = 2932361) B2932361
theorem B1955051 : Blo 868566 1955051 := bstep (se 1 (by rfl) ⟨1466288, by rfl⟩ : syracuseStep 1955051 = 2932577) B2932577
theorem B2480993 : Blo 868566 2480993 := bstep (se 2 (by rfl) ⟨930372, by rfl⟩ : syracuseStep 2480993 = 1860745) B1860745
theorem B90365543 : Blo 868566 90365543 := bstep (se 1 (by rfl) ⟨67774157, by rfl⟩ : syracuseStep 90365543 = 135548315) B135548315
theorem B18800423 : Blo 868566 18800423 := bstep (se 1 (by rfl) ⟨14100317, by rfl⟩ : syracuseStep 18800423 = 28200635) B28200635
theorem B1957985 : Blo 868566 1957985 := bstep (se 2 (by rfl) ⟨734244, by rfl⟩ : syracuseStep 1957985 = 1468489) B1468489
theorem B5661575 : Blo 868566 5661575 := bstep (se 1 (by rfl) ⟨4246181, by rfl⟩ : syracuseStep 5661575 = 8492363) B8492363
theorem B142697375 : Blo 868566 142697375 := bstep (se 1 (by rfl) ⟨107023031, by rfl⟩ : syracuseStep 142697375 = 214046063) B214046063
theorem B196043773 : Blo 868566 196043773 := bstep (se 3 (by rfl) ⟨36758207, by rfl⟩ : syracuseStep 196043773 = 73516415) B73516415
theorem B1303583 : Blo 868566 1303583 := bstep (se 1 (by rfl) ⟨977687, by rfl⟩ : syracuseStep 1303583 = 1955375) B1955375
theorem B1303871 : Blo 868566 1303871 := bstep (se 1 (by rfl) ⟨977903, by rfl⟩ : syracuseStep 1303871 = 1955807) B1955807
theorem B1959407 : Blo 868566 1959407 := bstep (se 1 (by rfl) ⟨1469555, by rfl⟩ : syracuseStep 1959407 = 2939111) B2939111
theorem B1959551 : Blo 868566 1959551 := bstep (se 1 (by rfl) ⟨1469663, by rfl⟩ : syracuseStep 1959551 = 2939327) B2939327
theorem B1304987 : Blo 868566 1304987 := bstep (se 1 (by rfl) ⟨978740, by rfl⟩ : syracuseStep 1304987 = 1957481) B1957481
theorem B1305071 : Blo 868566 1305071 := bstep (se 1 (by rfl) ⟨978803, by rfl⟩ : syracuseStep 1305071 = 1957607) B1957607
theorem B1469353 : Blo 868566 1469353 := bstep (se 2 (by rfl) ⟨551007, by rfl⟩ : syracuseStep 1469353 = 1102015) B1102015
theorem B977863 : Blo 868566 977863 := bstep (se 1 (by rfl) ⟨733397, by rfl⟩ : syracuseStep 977863 = 1466795) B1466795
theorem B2944187 : Blo 868566 2944187 := bstep (se 1 (by rfl) ⟨2208140, by rfl⟩ : syracuseStep 2944187 = 4416281) B4416281
theorem B1961441 : Blo 868566 1961441 := bstep (se 2 (by rfl) ⟨735540, by rfl⟩ : syracuseStep 1961441 = 1471081) B1471081
theorem B978799 : Blo 868566 978799 := bstep (se 1 (by rfl) ⟨734099, by rfl⟩ : syracuseStep 978799 = 1468199) B1468199
theorem B3535265 : Blo 868566 3535265 := bstep (se 2 (by rfl) ⟨1325724, by rfl⟩ : syracuseStep 3535265 = 2651449) B2651449
theorem B1307375 : Blo 868566 1307375 := bstep (se 1 (by rfl) ⟨980531, by rfl⟩ : syracuseStep 1307375 = 1961063) B1961063
theorem B980671 : Blo 868566 980671 := bstep (se 1 (by rfl) ⟨735503, by rfl⟩ : syracuseStep 980671 = 1471007) B1471007
theorem B12056377 : Blo 868566 12056377 := bstep (se 2 (by rfl) ⟨4521141, by rfl⟩ : syracuseStep 12056377 = 9042283) B9042283
theorem B3308141 : Blo 868566 3308141 := bstep (se 3 (by rfl) ⟨620276, by rfl⟩ : syracuseStep 3308141 = 1240553) B1240553
theorem B85752989 : Blo 868566 85752989 := bstep (se 3 (by rfl) ⟨16078685, by rfl⟩ : syracuseStep 85752989 = 32157371) B32157371
theorem B14875973 : Blo 868566 14875973 := bstep (se 4 (by rfl) ⟨1394622, by rfl⟩ : syracuseStep 14875973 = 2789245) B2789245
theorem B3310055 : Blo 868566 3310055 := bstep (se 1 (by rfl) ⟨2482541, by rfl⟩ : syracuseStep 3310055 = 4965083) B4965083
theorem B261391697 : Blo 868566 261391697 := bstep (se 2 (by rfl) ⟨98021886, by rfl⟩ : syracuseStep 261391697 = 196043773) B196043773
theorem B4950071 : Blo 868566 4950071 := bstep (se 1 (by rfl) ⟨3712553, by rfl⟩ : syracuseStep 4950071 = 7425107) B7425107
theorem B84676265 : Blo 868566 84676265 := bstep (se 2 (by rfl) ⟨31753599, by rfl⟩ : syracuseStep 84676265 = 63507199) B63507199
theorem B17829881 : Blo 868566 17829881 := bstep (se 2 (by rfl) ⟨6686205, by rfl⟩ : syracuseStep 17829881 = 13372411) B13372411
theorem B5018557 : Blo 868566 5018557 := bstep (se 3 (by rfl) ⟨940979, by rfl⟩ : syracuseStep 5018557 = 1881959) B1881959
theorem B2200841 : Blo 868566 2200841 := bstep (se 2 (by rfl) ⟨825315, by rfl⟩ : syracuseStep 2200841 = 1650631) B1650631
theorem B3774383 : Blo 868566 3774383 := bstep (se 1 (by rfl) ⟨2830787, by rfl⟩ : syracuseStep 3774383 = 5661575) B5661575
theorem B95131583 : Blo 868566 95131583 := bstep (se 1 (by rfl) ⟨71348687, by rfl⟩ : syracuseStep 95131583 = 142697375) B142697375
theorem B2205427 : Blo 868566 2205427 := bstep (se 1 (by rfl) ⟨1654070, by rfl⟩ : syracuseStep 2205427 = 3308141) B3308141
theorem B5582591 : Blo 868566 5582591 := bstep (se 1 (by rfl) ⟨4186943, by rfl⟩ : syracuseStep 5582591 = 8373887) B8373887
theorem B9056087 : Blo 868566 9056087 := bstep (se 1 (by rfl) ⟨6792065, by rfl⟩ : syracuseStep 9056087 = 13584131) B13584131
theorem B1651823 : Blo 868566 1651823 := bstep (se 1 (by rfl) ⟨1238867, by rfl⟩ : syracuseStep 1651823 = 2477735) B2477735
theorem B4405103 : Blo 868566 4405103 := bstep (se 1 (by rfl) ⟨3303827, by rfl⟩ : syracuseStep 4405103 = 6607655) B6607655
theorem B1653995 : Blo 868566 1653995 := bstep (se 1 (by rfl) ⟨1240496, by rfl⟩ : syracuseStep 1653995 = 2480993) B2480993
theorem B11156777 : Blo 868566 11156777 := bstep (se 2 (by rfl) ⟨4183791, by rfl⟩ : syracuseStep 11156777 = 8367583) B8367583
theorem B60243695 : Blo 868566 60243695 := bstep (se 1 (by rfl) ⟨45182771, by rfl⟩ : syracuseStep 60243695 = 90365543) B90365543
theorem B12533615 : Blo 868566 12533615 := bstep (se 1 (by rfl) ⟨9400211, by rfl⟩ : syracuseStep 12533615 = 18800423) B18800423
theorem B3522473 : Blo 868566 3522473 := bstep (se 2 (by rfl) ⟨1320927, by rfl⟩ : syracuseStep 3522473 = 2641855) B2641855
theorem B869055 : Blo 868566 869055 := bstep (se 1 (by rfl) ⟨651791, by rfl⟩ : syracuseStep 869055 = 1303583) B1303583
theorem B869247 : Blo 868566 869247 := bstep (se 1 (by rfl) ⟨651935, by rfl⟩ : syracuseStep 869247 = 1303871) B1303871
theorem B2934035 : Blo 868566 2934035 := bstep (se 1 (by rfl) ⟨2200526, by rfl⟩ : syracuseStep 2934035 = 4401053) B4401053
theorem B869991 : Blo 868566 869991 := bstep (se 1 (by rfl) ⟨652493, by rfl⟩ : syracuseStep 869991 = 1304987) B1304987
theorem B870047 : Blo 868566 870047 := bstep (se 1 (by rfl) ⟨652535, by rfl⟩ : syracuseStep 870047 = 1305071) B1305071
theorem B2934683 : Blo 868566 2934683 := bstep (se 1 (by rfl) ⟨2201012, by rfl⟩ : syracuseStep 2934683 = 4402025) B4402025
theorem B16075169 : Blo 868566 16075169 := bstep (se 2 (by rfl) ⟨6028188, by rfl⟩ : syracuseStep 16075169 = 12056377) B12056377
theorem B6605225 : Blo 868566 6605225 := bstep (se 2 (by rfl) ⟨2476959, by rfl⟩ : syracuseStep 6605225 = 4953919) B4953919
theorem B871583 : Blo 868566 871583 := bstep (se 1 (by rfl) ⟨653687, by rfl⟩ : syracuseStep 871583 = 1307375) B1307375
theorem B6606683 : Blo 868566 6606683 := bstep (se 1 (by rfl) ⟨4955012, by rfl⟩ : syracuseStep 6606683 = 9910025) B9910025
theorem B1954511 : Blo 868566 1954511 := bstep (se 1 (by rfl) ⟨1465883, by rfl⟩ : syracuseStep 1954511 = 2931767) B2931767
theorem B2937599 : Blo 868566 2937599 := bstep (se 1 (by rfl) ⟨2203199, by rfl⟩ : syracuseStep 2937599 = 4406399) B4406399
theorem B57168659 : Blo 868566 57168659 := bstep (se 1 (by rfl) ⟨42876494, by rfl⟩ : syracuseStep 57168659 = 85752989) B85752989
theorem B40293247 : Blo 868566 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B9917315 : Blo 868566 9917315 := bstep (se 1 (by rfl) ⟨7437986, by rfl⟩ : syracuseStep 9917315 = 14875973) B14875973
theorem B2086975 : Blo 868566 2086975 := bstep (se 1 (by rfl) ⟨1565231, by rfl⟩ : syracuseStep 2086975 = 3130463) B3130463
theorem B9427373 : Blo 868566 9427373 := bstep (se 3 (by rfl) ⟨1767632, by rfl⟩ : syracuseStep 9427373 = 3535265) B3535265
theorem B2941001 : Blo 868566 2941001 := bstep (se 2 (by rfl) ⟨1102875, by rfl⟩ : syracuseStep 2941001 = 2205751) B2205751
theorem B2941055 : Blo 868566 2941055 := bstep (se 1 (by rfl) ⟨2205791, by rfl⟩ : syracuseStep 2941055 = 4411583) B4411583
theorem B2482427 : Blo 868566 2482427 := bstep (se 1 (by rfl) ⟨1861820, by rfl⟩ : syracuseStep 2482427 = 3723641) B3723641
theorem B2941487 : Blo 868566 2941487 := bstep (se 1 (by rfl) ⟨2206115, by rfl⟩ : syracuseStep 2941487 = 4412231) B4412231
theorem B1303271 : Blo 868566 1303271 := bstep (se 1 (by rfl) ⟨977453, by rfl⟩ : syracuseStep 1303271 = 1954907) B1954907
theorem B1303367 : Blo 868566 1303367 := bstep (se 1 (by rfl) ⟨977525, by rfl⟩ : syracuseStep 1303367 = 1955051) B1955051
theorem B2941865 : Blo 868566 2941865 := bstep (se 2 (by rfl) ⟨1103199, by rfl⟩ : syracuseStep 2941865 = 2206399) B2206399
theorem B1959137 : Blo 868566 1959137 := bstep (se 2 (by rfl) ⟨734676, by rfl⟩ : syracuseStep 1959137 = 1469353) B1469353
theorem B1303817 : Blo 868566 1303817 := bstep (se 2 (by rfl) ⟨488931, by rfl⟩ : syracuseStep 1303817 = 977863) B977863
theorem B10315511 : Blo 868566 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B1305065 : Blo 868566 1305065 := bstep (se 2 (by rfl) ⟨489399, by rfl⟩ : syracuseStep 1305065 = 978799) B978799
theorem B1305323 : Blo 868566 1305323 := bstep (se 1 (by rfl) ⟨978992, by rfl⟩ : syracuseStep 1305323 = 1957985) B1957985
theorem B1306271 : Blo 868566 1306271 := bstep (se 1 (by rfl) ⟨979703, by rfl⟩ : syracuseStep 1306271 = 1959407) B1959407
theorem B1306367 : Blo 868566 1306367 := bstep (se 1 (by rfl) ⟨979775, by rfl⟩ : syracuseStep 1306367 = 1959551) B1959551
theorem B1962791 : Blo 868566 1962791 := bstep (se 1 (by rfl) ⟨1472093, by rfl⟩ : syracuseStep 1962791 = 2944187) B2944187
theorem B1307561 : Blo 868566 1307561 := bstep (se 2 (by rfl) ⟨490335, by rfl⟩ : syracuseStep 1307561 = 980671) B980671
theorem B1307627 : Blo 868566 1307627 := bstep (se 1 (by rfl) ⟨980720, by rfl⟩ : syracuseStep 1307627 = 1961441) B1961441
theorem B1471979 : Blo 868566 1471979 := bstep (se 1 (by rfl) ⟨1103984, by rfl⟩ : syracuseStep 1471979 = 2207969) B2207969
theorem B6618833 : Blo 868566 6618833 := bstep (se 2 (by rfl) ⟨2482062, by rfl⟩ : syracuseStep 6618833 = 4964125) B4964125
theorem B6619805 : Blo 868566 6619805 := bstep (se 3 (by rfl) ⟨1241213, by rfl⟩ : syracuseStep 6619805 = 2482427) B2482427
theorem B174261131 : Blo 868566 174261131 := bstep (se 1 (by rfl) ⟨130695848, by rfl⟩ : syracuseStep 174261131 = 261391697) B261391697
theorem B10716779 : Blo 868566 10716779 := bstep (se 1 (by rfl) ⟨8037584, by rfl⟩ : syracuseStep 10716779 = 16075169) B16075169
theorem B38112439 : Blo 868566 38112439 := bstep (se 1 (by rfl) ⟨28584329, by rfl⟩ : syracuseStep 38112439 = 57168659) B57168659
theorem B6691409 : Blo 868566 6691409 := bstep (se 2 (by rfl) ⟨2509278, by rfl⟩ : syracuseStep 6691409 = 5018557) B5018557
theorem B6037391 : Blo 868566 6037391 := bstep (se 1 (by rfl) ⟨4528043, by rfl⟩ : syracuseStep 6037391 = 9056087) B9056087
theorem B2206703 : Blo 868566 2206703 := bstep (se 1 (by rfl) ⟨1655027, by rfl⟩ : syracuseStep 2206703 = 3310055) B3310055
theorem B4403483 : Blo 868566 4403483 := bstep (se 1 (by rfl) ⟨3302612, by rfl⟩ : syracuseStep 4403483 = 6605225) B6605225
theorem B4404455 : Blo 868566 4404455 := bstep (se 1 (by rfl) ⟨3303341, by rfl⟩ : syracuseStep 4404455 = 6606683) B6606683
theorem B63421055 : Blo 868566 63421055 := bstep (se 1 (by rfl) ⟨47565791, by rfl⟩ : syracuseStep 63421055 = 95131583) B95131583
theorem B868847 : Blo 868566 868847 := bstep (se 1 (by rfl) ⟨651635, by rfl⟩ : syracuseStep 868847 = 1303271) B1303271
theorem B868911 : Blo 868566 868911 := bstep (se 1 (by rfl) ⟨651683, by rfl⟩ : syracuseStep 868911 = 1303367) B1303367
theorem B869211 : Blo 868566 869211 := bstep (se 1 (by rfl) ⟨651908, by rfl⟩ : syracuseStep 869211 = 1303817) B1303817
theorem B53724329 : Blo 868566 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B870043 : Blo 868566 870043 := bstep (se 1 (by rfl) ⟨652532, by rfl⟩ : syracuseStep 870043 = 1305065) B1305065
theorem B870215 : Blo 868566 870215 := bstep (se 1 (by rfl) ⟨652661, by rfl⟩ : syracuseStep 870215 = 1305323) B1305323
theorem B870847 : Blo 868566 870847 := bstep (se 1 (by rfl) ⟨653135, by rfl⟩ : syracuseStep 870847 = 1306271) B1306271
theorem B870911 : Blo 868566 870911 := bstep (se 1 (by rfl) ⟨653183, by rfl⟩ : syracuseStep 870911 = 1306367) B1306367
theorem B3721727 : Blo 868566 3721727 := bstep (se 1 (by rfl) ⟨2791295, by rfl⟩ : syracuseStep 3721727 = 5582591) B5582591
theorem B871707 : Blo 868566 871707 := bstep (se 1 (by rfl) ⟨653780, by rfl⟩ : syracuseStep 871707 = 1307561) B1307561
theorem B871751 : Blo 868566 871751 := bstep (se 1 (by rfl) ⟨653813, by rfl⟩ : syracuseStep 871751 = 1307627) B1307627
theorem B1101215 : Blo 868566 1101215 := bstep (se 1 (by rfl) ⟨825911, by rfl⟩ : syracuseStep 1101215 = 1651823) B1651823
theorem B2936735 : Blo 868566 2936735 := bstep (se 1 (by rfl) ⟨2202551, by rfl⟩ : syracuseStep 2936735 = 4405103) B4405103
theorem B1102663 : Blo 868566 1102663 := bstep (se 1 (by rfl) ⟨826997, by rfl⟩ : syracuseStep 1102663 = 1653995) B1653995
theorem B4412555 : Blo 868566 4412555 := bstep (se 1 (by rfl) ⟨3309416, by rfl⟩ : syracuseStep 4412555 = 6618833) B6618833
theorem B40162463 : Blo 868566 40162463 := bstep (se 1 (by rfl) ⟨30121847, by rfl⟩ : syracuseStep 40162463 = 60243695) B60243695
theorem B2348315 : Blo 868566 2348315 := bstep (se 1 (by rfl) ⟨1761236, by rfl⟩ : syracuseStep 2348315 = 3522473) B3522473
theorem B11130533 : Blo 868566 11130533 := bstep (se 4 (by rfl) ⟨1043487, by rfl⟩ : syracuseStep 11130533 = 2086975) B2086975
theorem B1956023 : Blo 868566 1956023 := bstep (se 1 (by rfl) ⟨1467017, by rfl⟩ : syracuseStep 1956023 = 2934035) B2934035
theorem B1956455 : Blo 868566 1956455 := bstep (se 1 (by rfl) ⟨1467341, by rfl⟩ : syracuseStep 1956455 = 2934683) B2934683
theorem B3300047 : Blo 868566 3300047 := bstep (se 1 (by rfl) ⟨2475035, by rfl⟩ : syracuseStep 3300047 = 4950071) B4950071
theorem B2940569 : Blo 868566 2940569 := bstep (se 2 (by rfl) ⟨1102713, by rfl⟩ : syracuseStep 2940569 = 2205427) B2205427
theorem B56450843 : Blo 868566 56450843 := bstep (se 1 (by rfl) ⟨42338132, by rfl⟩ : syracuseStep 56450843 = 84676265) B84676265
theorem B11886587 : Blo 868566 11886587 := bstep (se 1 (by rfl) ⟨8914940, by rfl⟩ : syracuseStep 11886587 = 17829881) B17829881
theorem B1303007 : Blo 868566 1303007 := bstep (se 1 (by rfl) ⟨977255, by rfl⟩ : syracuseStep 1303007 = 1954511) B1954511
theorem B1958399 : Blo 868566 1958399 := bstep (se 1 (by rfl) ⟨1468799, by rfl⟩ : syracuseStep 1958399 = 2937599) B2937599
theorem B6611543 : Blo 868566 6611543 := bstep (se 1 (by rfl) ⟨4958657, by rfl⟩ : syracuseStep 6611543 = 9917315) B9917315
theorem B1467227 : Blo 868566 1467227 := bstep (se 1 (by rfl) ⟨1100420, by rfl⟩ : syracuseStep 1467227 = 2200841) B2200841
theorem B2516255 : Blo 868566 2516255 := bstep (se 1 (by rfl) ⟨1887191, by rfl⟩ : syracuseStep 2516255 = 3774383) B3774383
theorem B6284915 : Blo 868566 6284915 := bstep (se 1 (by rfl) ⟨4713686, by rfl⟩ : syracuseStep 6284915 = 9427373) B9427373
theorem B1960667 : Blo 868566 1960667 := bstep (se 1 (by rfl) ⟨1470500, by rfl⟩ : syracuseStep 1960667 = 2941001) B2941001
theorem B1960703 : Blo 868566 1960703 := bstep (se 1 (by rfl) ⟨1470527, by rfl⟩ : syracuseStep 1960703 = 2941055) B2941055
theorem B1960991 : Blo 868566 1960991 := bstep (se 1 (by rfl) ⟨1470743, by rfl⟩ : syracuseStep 1960991 = 2941487) B2941487
theorem B1961243 : Blo 868566 1961243 := bstep (se 1 (by rfl) ⟨1470932, by rfl⟩ : syracuseStep 1961243 = 2941865) B2941865
theorem B1306091 : Blo 868566 1306091 := bstep (se 1 (by rfl) ⟨979568, by rfl⟩ : syracuseStep 1306091 = 1959137) B1959137
theorem B6877007 : Blo 868566 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B1308527 : Blo 868566 1308527 := bstep (se 1 (by rfl) ⟨981395, by rfl⟩ : syracuseStep 1308527 = 1962791) B1962791
theorem B981319 : Blo 868566 981319 := bstep (se 1 (by rfl) ⟨735989, by rfl⟩ : syracuseStep 981319 = 1471979) B1471979
theorem B7437851 : Blo 868566 7437851 := bstep (se 1 (by rfl) ⟨5578388, by rfl⟩ : syracuseStep 7437851 = 11156777) B11156777
theorem B8355743 : Blo 868566 8355743 := bstep (se 1 (by rfl) ⟨6266807, by rfl⟩ : syracuseStep 8355743 = 12533615) B12533615
theorem B35816219 : Blo 868566 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B7144519 : Blo 868566 7144519 := bstep (se 1 (by rfl) ⟨5358389, by rfl⟩ : syracuseStep 7144519 = 10716779) B10716779
theorem B26774975 : Blo 868566 26774975 := bstep (se 1 (by rfl) ⟨20081231, by rfl⟩ : syracuseStep 26774975 = 40162463) B40162463
theorem B4460939 : Blo 868566 4460939 := bstep (se 1 (by rfl) ⟨3345704, by rfl⟩ : syracuseStep 4460939 = 6691409) B6691409
theorem B2200031 : Blo 868566 2200031 := bstep (se 1 (by rfl) ⟨1650023, by rfl⟩ : syracuseStep 2200031 = 3300047) B3300047
theorem B1677503 : Blo 868566 1677503 := bstep (se 1 (by rfl) ⟨1258127, by rfl⟩ : syracuseStep 1677503 = 2516255) B2516255
theorem B42280703 : Blo 868566 42280703 := bstep (se 1 (by rfl) ⟨31710527, by rfl⟩ : syracuseStep 42280703 = 63421055) B63421055
theorem B4958567 : Blo 868566 4958567 := bstep (se 1 (by rfl) ⟨3718925, by rfl⟩ : syracuseStep 4958567 = 7437851) B7437851
theorem B116174087 : Blo 868566 116174087 := bstep (se 1 (by rfl) ⟨87130565, by rfl⟩ : syracuseStep 116174087 = 174261131) B174261131
theorem B7420355 : Blo 868566 7420355 := bstep (se 1 (by rfl) ⟨5565266, by rfl⟩ : syracuseStep 7420355 = 11130533) B11130533
theorem B37633895 : Blo 868566 37633895 := bstep (se 1 (by rfl) ⟨28225421, by rfl⟩ : syracuseStep 37633895 = 56450843) B56450843
theorem B868671 : Blo 868566 868671 := bstep (se 1 (by rfl) ⟨651503, by rfl⟩ : syracuseStep 868671 = 1303007) B1303007
theorem B4407695 : Blo 868566 4407695 := bstep (se 1 (by rfl) ⟨3305771, by rfl⟩ : syracuseStep 4407695 = 6611543) B6611543
theorem B870727 : Blo 868566 870727 := bstep (se 1 (by rfl) ⟨653045, by rfl⟩ : syracuseStep 870727 = 1306091) B1306091
theorem B2935655 : Blo 868566 2935655 := bstep (se 1 (by rfl) ⟨2201741, by rfl⟩ : syracuseStep 2935655 = 4403483) B4403483
theorem B2936303 : Blo 868566 2936303 := bstep (se 1 (by rfl) ⟨2202227, by rfl⟩ : syracuseStep 2936303 = 4404455) B4404455
theorem B2936573 : Blo 868566 2936573 := bstep (se 3 (by rfl) ⟨550607, by rfl⟩ : syracuseStep 2936573 = 1101215) B1101215
theorem B872351 : Blo 868566 872351 := bstep (se 1 (by rfl) ⟨654263, by rfl⟩ : syracuseStep 872351 = 1308527) B1308527
theorem B4413203 : Blo 868566 4413203 := bstep (se 1 (by rfl) ⟨3309902, by rfl⟩ : syracuseStep 4413203 = 6619805) B6619805
theorem B1957823 : Blo 868566 1957823 := bstep (se 1 (by rfl) ⟨1468367, by rfl⟩ : syracuseStep 1957823 = 2936735) B2936735
theorem B2941703 : Blo 868566 2941703 := bstep (se 1 (by rfl) ⟨2206277, by rfl⟩ : syracuseStep 2941703 = 4412555) B4412555
theorem B1565543 : Blo 868566 1565543 := bstep (se 1 (by rfl) ⟨1174157, by rfl⟩ : syracuseStep 1565543 = 2348315) B2348315
theorem B1304015 : Blo 868566 1304015 := bstep (se 1 (by rfl) ⟨978011, by rfl⟩ : syracuseStep 1304015 = 1956023) B1956023
theorem B50816585 : Blo 868566 50816585 := bstep (se 2 (by rfl) ⟨19056219, by rfl⟩ : syracuseStep 50816585 = 38112439) B38112439
theorem B1304303 : Blo 868566 1304303 := bstep (se 1 (by rfl) ⟨978227, by rfl⟩ : syracuseStep 1304303 = 1956455) B1956455
theorem B1960379 : Blo 868566 1960379 := bstep (se 1 (by rfl) ⟨1470284, by rfl⟩ : syracuseStep 1960379 = 2940569) B2940569
theorem B4024927 : Blo 868566 4024927 := bstep (se 1 (by rfl) ⟨3018695, by rfl⟩ : syracuseStep 4024927 = 6037391) B6037391
theorem B7924391 : Blo 868566 7924391 := bstep (se 1 (by rfl) ⟨5943293, by rfl⟩ : syracuseStep 7924391 = 11886587) B11886587
theorem B1305599 : Blo 868566 1305599 := bstep (se 1 (by rfl) ⟨979199, by rfl⟩ : syracuseStep 1305599 = 1958399) B1958399
theorem B978151 : Blo 868566 978151 := bstep (se 1 (by rfl) ⟨733613, by rfl⟩ : syracuseStep 978151 = 1467227) B1467227
theorem B4189943 : Blo 868566 4189943 := bstep (se 1 (by rfl) ⟨3142457, by rfl⟩ : syracuseStep 4189943 = 6284915) B6284915
theorem B1470217 : Blo 868566 1470217 := bstep (se 2 (by rfl) ⟨551331, by rfl⟩ : syracuseStep 1470217 = 1102663) B1102663
theorem B9924605 : Blo 868566 9924605 := bstep (se 3 (by rfl) ⟨1860863, by rfl⟩ : syracuseStep 9924605 = 3721727) B3721727
theorem B1307111 : Blo 868566 1307111 := bstep (se 1 (by rfl) ⟨980333, by rfl⟩ : syracuseStep 1307111 = 1960667) B1960667
theorem B1307135 : Blo 868566 1307135 := bstep (se 1 (by rfl) ⟨980351, by rfl⟩ : syracuseStep 1307135 = 1960703) B1960703
theorem B1471135 : Blo 868566 1471135 := bstep (se 1 (by rfl) ⟨1103351, by rfl⟩ : syracuseStep 1471135 = 2206703) B2206703
theorem B1307327 : Blo 868566 1307327 := bstep (se 1 (by rfl) ⟨980495, by rfl⟩ : syracuseStep 1307327 = 1960991) B1960991
theorem B1307495 : Blo 868566 1307495 := bstep (se 1 (by rfl) ⟨980621, by rfl⟩ : syracuseStep 1307495 = 1961243) B1961243
theorem B4584671 : Blo 868566 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B1308425 : Blo 868566 1308425 := bstep (se 2 (by rfl) ⟨490659, by rfl⟩ : syracuseStep 1308425 = 981319) B981319
theorem B5570495 : Blo 868566 5570495 := bstep (se 1 (by rfl) ⟨4177871, by rfl⟩ : syracuseStep 5570495 = 8355743) B8355743
theorem B1118335 : Blo 868566 1118335 := bstep (se 1 (by rfl) ⟨838751, by rfl⟩ : syracuseStep 1118335 = 1677503) B1677503
theorem B28187135 : Blo 868566 28187135 := bstep (se 1 (by rfl) ⟨21140351, by rfl⟩ : syracuseStep 28187135 = 42280703) B42280703
theorem B5282927 : Blo 868566 5282927 := bstep (se 1 (by rfl) ⟨3962195, by rfl⟩ : syracuseStep 5282927 = 7924391) B7924391
theorem B2793295 : Blo 868566 2793295 := bstep (se 1 (by rfl) ⟨2094971, by rfl⟩ : syracuseStep 2793295 = 4189943) B4189943
theorem B3056447 : Blo 868566 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B3713663 : Blo 868566 3713663 := bstep (se 1 (by rfl) ⟨2785247, by rfl⟩ : syracuseStep 3713663 = 5570495) B5570495
theorem B135510893 : Blo 868566 135510893 := bstep (se 3 (by rfl) ⟨25408292, by rfl⟩ : syracuseStep 135510893 = 50816585) B50816585
theorem B869343 : Blo 868566 869343 := bstep (se 1 (by rfl) ⟨652007, by rfl⟩ : syracuseStep 869343 = 1304015) B1304015
theorem B869535 : Blo 868566 869535 := bstep (se 1 (by rfl) ⟨652151, by rfl⟩ : syracuseStep 869535 = 1304303) B1304303
theorem B870399 : Blo 868566 870399 := bstep (se 1 (by rfl) ⟨652799, by rfl⟩ : syracuseStep 870399 = 1305599) B1305599
theorem B77449391 : Blo 868566 77449391 := bstep (se 1 (by rfl) ⟨58087043, by rfl⟩ : syracuseStep 77449391 = 116174087) B116174087
theorem B871407 : Blo 868566 871407 := bstep (se 1 (by rfl) ⟨653555, by rfl⟩ : syracuseStep 871407 = 1307111) B1307111
theorem B871423 : Blo 868566 871423 := bstep (se 1 (by rfl) ⟨653567, by rfl⟩ : syracuseStep 871423 = 1307135) B1307135
theorem B871551 : Blo 868566 871551 := bstep (se 1 (by rfl) ⟨653663, by rfl⟩ : syracuseStep 871551 = 1307327) B1307327
theorem B871663 : Blo 868566 871663 := bstep (se 1 (by rfl) ⟨653747, by rfl⟩ : syracuseStep 871663 = 1307495) B1307495
theorem B872283 : Blo 868566 872283 := bstep (se 1 (by rfl) ⟨654212, by rfl⟩ : syracuseStep 872283 = 1308425) B1308425
theorem B25089263 : Blo 868566 25089263 := bstep (se 1 (by rfl) ⟨18816947, by rfl⟩ : syracuseStep 25089263 = 37633895) B37633895
theorem B2938463 : Blo 868566 2938463 := bstep (se 1 (by rfl) ⟨2203847, by rfl⟩ : syracuseStep 2938463 = 4407695) B4407695
theorem B23877479 : Blo 868566 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B9526025 : Blo 868566 9526025 := bstep (se 2 (by rfl) ⟨3572259, by rfl⟩ : syracuseStep 9526025 = 7144519) B7144519
theorem B1957103 : Blo 868566 1957103 := bstep (se 1 (by rfl) ⟨1467827, by rfl⟩ : syracuseStep 1957103 = 2935655) B2935655
theorem B17849983 : Blo 868566 17849983 := bstep (se 1 (by rfl) ⟨13387487, by rfl⟩ : syracuseStep 17849983 = 26774975) B26774975
theorem B1957535 : Blo 868566 1957535 := bstep (se 1 (by rfl) ⟨1468151, by rfl⟩ : syracuseStep 1957535 = 2936303) B2936303
theorem B1957715 : Blo 868566 1957715 := bstep (se 1 (by rfl) ⟨1468286, by rfl⟩ : syracuseStep 1957715 = 2936573) B2936573
theorem B2973959 : Blo 868566 2973959 := bstep (se 1 (by rfl) ⟨2230469, by rfl⟩ : syracuseStep 2973959 = 4460939) B4460939
theorem B1466687 : Blo 868566 1466687 := bstep (se 1 (by rfl) ⟨1100015, by rfl⟩ : syracuseStep 1466687 = 2200031) B2200031
theorem B5366569 : Blo 868566 5366569 := bstep (se 2 (by rfl) ⟨2012463, by rfl⟩ : syracuseStep 5366569 = 4024927) B4024927
theorem B2942135 : Blo 868566 2942135 := bstep (se 1 (by rfl) ⟨2206601, by rfl⟩ : syracuseStep 2942135 = 4413203) B4413203
theorem B1304201 : Blo 868566 1304201 := bstep (se 2 (by rfl) ⟨489075, by rfl⟩ : syracuseStep 1304201 = 978151) B978151
theorem B1960289 : Blo 868566 1960289 := bstep (se 2 (by rfl) ⟨735108, by rfl⟩ : syracuseStep 1960289 = 1470217) B1470217
theorem B1305215 : Blo 868566 1305215 := bstep (se 1 (by rfl) ⟨978911, by rfl⟩ : syracuseStep 1305215 = 1957823) B1957823
theorem B1961135 : Blo 868566 1961135 := bstep (se 1 (by rfl) ⟨1470851, by rfl⟩ : syracuseStep 1961135 = 2941703) B2941703
theorem B1043695 : Blo 868566 1043695 := bstep (se 1 (by rfl) ⟨782771, by rfl⟩ : syracuseStep 1043695 = 1565543) B1565543
theorem B1961513 : Blo 868566 1961513 := bstep (se 2 (by rfl) ⟨735567, by rfl⟩ : syracuseStep 1961513 = 1471135) B1471135
theorem B3305711 : Blo 868566 3305711 := bstep (se 1 (by rfl) ⟨2479283, by rfl⟩ : syracuseStep 3305711 = 4958567) B4958567
theorem B1306919 : Blo 868566 1306919 := bstep (se 1 (by rfl) ⟨980189, by rfl⟩ : syracuseStep 1306919 = 1960379) B1960379
theorem B6616403 : Blo 868566 6616403 := bstep (se 1 (by rfl) ⟨4962302, by rfl⟩ : syracuseStep 6616403 = 9924605) B9924605
theorem B4946903 : Blo 868566 4946903 := bstep (se 1 (by rfl) ⟨3710177, by rfl⟩ : syracuseStep 4946903 = 7420355) B7420355
theorem B2037631 : Blo 868566 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B2203807 : Blo 868566 2203807 := bstep (se 1 (by rfl) ⟨1652855, by rfl⟩ : syracuseStep 2203807 = 3305711) B3305711
theorem B23799977 : Blo 868566 23799977 := bstep (se 2 (by rfl) ⟨8924991, by rfl⟩ : syracuseStep 23799977 = 17849983) B17849983
theorem B7155425 : Blo 868566 7155425 := bstep (se 2 (by rfl) ⟨2683284, by rfl⟩ : syracuseStep 7155425 = 5366569) B5366569
theorem B16726175 : Blo 868566 16726175 := bstep (se 1 (by rfl) ⟨12544631, by rfl⟩ : syracuseStep 16726175 = 25089263) B25089263
theorem B1391593 : Blo 868566 1391593 := bstep (se 2 (by rfl) ⟨521847, by rfl⟩ : syracuseStep 1391593 = 1043695) B1043695
theorem B18791423 : Blo 868566 18791423 := bstep (se 1 (by rfl) ⟨14093567, by rfl⟩ : syracuseStep 18791423 = 28187135) B28187135
theorem B3521951 : Blo 868566 3521951 := bstep (se 1 (by rfl) ⟨2641463, by rfl⟩ : syracuseStep 3521951 = 5282927) B5282927
theorem B1491113 : Blo 868566 1491113 := bstep (se 2 (by rfl) ⟨559167, by rfl⟩ : syracuseStep 1491113 = 1118335) B1118335
theorem B1982639 : Blo 868566 1982639 := bstep (se 1 (by rfl) ⟨1486979, by rfl⟩ : syracuseStep 1982639 = 2973959) B2973959
theorem B869467 : Blo 868566 869467 := bstep (se 1 (by rfl) ⟨652100, by rfl⟩ : syracuseStep 869467 = 1304201) B1304201
theorem B2475775 : Blo 868566 2475775 := bstep (se 1 (by rfl) ⟨1856831, by rfl⟩ : syracuseStep 2475775 = 3713663) B3713663
theorem B870143 : Blo 868566 870143 := bstep (se 1 (by rfl) ⟨652607, by rfl⟩ : syracuseStep 870143 = 1305215) B1305215
theorem B871279 : Blo 868566 871279 := bstep (se 1 (by rfl) ⟨653459, by rfl⟩ : syracuseStep 871279 = 1306919) B1306919
theorem B4410935 : Blo 868566 4410935 := bstep (se 1 (by rfl) ⟨3308201, by rfl⟩ : syracuseStep 4410935 = 6616403) B6616403
theorem B3297935 : Blo 868566 3297935 := bstep (se 1 (by rfl) ⟨2473451, by rfl⟩ : syracuseStep 3297935 = 4946903) B4946903
theorem B3724393 : Blo 868566 3724393 := bstep (se 2 (by rfl) ⟨1396647, by rfl⟩ : syracuseStep 3724393 = 2793295) B2793295
theorem B51632927 : Blo 868566 51632927 := bstep (se 1 (by rfl) ⟨38724695, by rfl⟩ : syracuseStep 51632927 = 77449391) B77449391
theorem B1958975 : Blo 868566 1958975 := bstep (se 1 (by rfl) ⟨1469231, by rfl⟩ : syracuseStep 1958975 = 2938463) B2938463
theorem B15918319 : Blo 868566 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B6350683 : Blo 868566 6350683 := bstep (se 1 (by rfl) ⟨4763012, by rfl⟩ : syracuseStep 6350683 = 9526025) B9526025
theorem B1304735 : Blo 868566 1304735 := bstep (se 1 (by rfl) ⟨978551, by rfl⟩ : syracuseStep 1304735 = 1957103) B1957103
theorem B1305023 : Blo 868566 1305023 := bstep (se 1 (by rfl) ⟨978767, by rfl⟩ : syracuseStep 1305023 = 1957535) B1957535
theorem B1305143 : Blo 868566 1305143 := bstep (se 1 (by rfl) ⟨978857, by rfl⟩ : syracuseStep 1305143 = 1957715) B1957715
theorem B977791 : Blo 868566 977791 := bstep (se 1 (by rfl) ⟨733343, by rfl⟩ : syracuseStep 977791 = 1466687) B1466687
theorem B1961423 : Blo 868566 1961423 := bstep (se 1 (by rfl) ⟨1471067, by rfl⟩ : syracuseStep 1961423 = 2942135) B2942135
theorem B1306859 : Blo 868566 1306859 := bstep (se 1 (by rfl) ⟨980144, by rfl⟩ : syracuseStep 1306859 = 1960289) B1960289
theorem B1307423 : Blo 868566 1307423 := bstep (se 1 (by rfl) ⟨980567, by rfl⟩ : syracuseStep 1307423 = 1961135) B1961135
theorem B1307675 : Blo 868566 1307675 := bstep (se 1 (by rfl) ⟨980756, by rfl⟩ : syracuseStep 1307675 = 1961513) B1961513
theorem B90340595 : Blo 868566 90340595 := bstep (se 1 (by rfl) ⟨67755446, by rfl⟩ : syracuseStep 90340595 = 135510893) B135510893
theorem B2198623 : Blo 868566 2198623 := bstep (se 1 (by rfl) ⟨1648967, by rfl⟩ : syracuseStep 2198623 = 3297935) B3297935
theorem B15866651 : Blo 868566 15866651 := bstep (se 1 (by rfl) ⟨11899988, by rfl⟩ : syracuseStep 15866651 = 23799977) B23799977
theorem B11150783 : Blo 868566 11150783 := bstep (se 1 (by rfl) ⟨8363087, by rfl⟩ : syracuseStep 11150783 = 16726175) B16726175
theorem B12527615 : Blo 868566 12527615 := bstep (se 1 (by rfl) ⟨9395711, by rfl⟩ : syracuseStep 12527615 = 18791423) B18791423
theorem B994075 : Blo 868566 994075 := bstep (se 1 (by rfl) ⟨745556, by rfl⟩ : syracuseStep 994075 = 1491113) B1491113
theorem B1321759 : Blo 868566 1321759 := bstep (se 1 (by rfl) ⟨991319, by rfl⟩ : syracuseStep 1321759 = 1982639) B1982639
theorem B8467577 : Blo 868566 8467577 := bstep (se 2 (by rfl) ⟨3175341, by rfl⟩ : syracuseStep 8467577 = 6350683) B6350683
theorem B34421951 : Blo 868566 34421951 := bstep (se 1 (by rfl) ⟨25816463, by rfl⟩ : syracuseStep 34421951 = 51632927) B51632927
theorem B869823 : Blo 868566 869823 := bstep (se 1 (by rfl) ⟨652367, by rfl⟩ : syracuseStep 869823 = 1304735) B1304735
theorem B4965857 : Blo 868566 4965857 := bstep (se 2 (by rfl) ⟨1862196, by rfl⟩ : syracuseStep 4965857 = 3724393) B3724393
theorem B870015 : Blo 868566 870015 := bstep (se 1 (by rfl) ⟨652511, by rfl⟩ : syracuseStep 870015 = 1305023) B1305023
theorem B870095 : Blo 868566 870095 := bstep (se 1 (by rfl) ⟨652571, by rfl⟩ : syracuseStep 870095 = 1305143) B1305143
theorem B4770283 : Blo 868566 4770283 := bstep (se 1 (by rfl) ⟨3577712, by rfl⟩ : syracuseStep 4770283 = 7155425) B7155425
theorem B871239 : Blo 868566 871239 := bstep (se 1 (by rfl) ⟨653429, by rfl⟩ : syracuseStep 871239 = 1306859) B1306859
theorem B871615 : Blo 868566 871615 := bstep (se 1 (by rfl) ⟨653711, by rfl⟩ : syracuseStep 871615 = 1307423) B1307423
theorem B871783 : Blo 868566 871783 := bstep (se 1 (by rfl) ⟨653837, by rfl⟩ : syracuseStep 871783 = 1307675) B1307675
theorem B1855457 : Blo 868566 1855457 := bstep (se 2 (by rfl) ⟨695796, by rfl⟩ : syracuseStep 1855457 = 1391593) B1391593
theorem B2347967 : Blo 868566 2347967 := bstep (se 1 (by rfl) ⟨1760975, by rfl⟩ : syracuseStep 2347967 = 3521951) B3521951
theorem B2938409 : Blo 868566 2938409 := bstep (se 2 (by rfl) ⟨1101903, by rfl⟩ : syracuseStep 2938409 = 2203807) B2203807
theorem B21224425 : Blo 868566 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B3301033 : Blo 868566 3301033 := bstep (se 2 (by rfl) ⟨1237887, by rfl⟩ : syracuseStep 3301033 = 2475775) B2475775
theorem B2940623 : Blo 868566 2940623 := bstep (se 1 (by rfl) ⟨2205467, by rfl⟩ : syracuseStep 2940623 = 4410935) B4410935
theorem B1303721 : Blo 868566 1303721 := bstep (se 2 (by rfl) ⟨488895, by rfl⟩ : syracuseStep 1303721 = 977791) B977791
theorem B1305983 : Blo 868566 1305983 := bstep (se 1 (by rfl) ⟨979487, by rfl⟩ : syracuseStep 1305983 = 1958975) B1958975
theorem B1307615 : Blo 868566 1307615 := bstep (se 1 (by rfl) ⟨980711, by rfl⟩ : syracuseStep 1307615 = 1961423) B1961423
theorem B2716841 : Blo 868566 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B60227063 : Blo 868566 60227063 := bstep (se 1 (by rfl) ⟨45170297, by rfl⟩ : syracuseStep 60227063 = 90340595) B90340595
theorem B3310571 : Blo 868566 3310571 := bstep (se 1 (by rfl) ⟨2482928, by rfl⟩ : syracuseStep 3310571 = 4965857) B4965857
theorem B6261245 : Blo 868566 6261245 := bstep (se 3 (by rfl) ⟨1173983, by rfl⟩ : syracuseStep 6261245 = 2347967) B2347967
theorem B7244909 : Blo 868566 7244909 := bstep (se 3 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 7244909 = 2716841) B2716841
theorem B6360377 : Blo 868566 6360377 := bstep (se 2 (by rfl) ⟨2385141, by rfl⟩ : syracuseStep 6360377 = 4770283) B4770283
theorem B42311069 : Blo 868566 42311069 := bstep (se 3 (by rfl) ⟨7933325, by rfl⟩ : syracuseStep 42311069 = 15866651) B15866651
theorem B5645051 : Blo 868566 5645051 := bstep (se 1 (by rfl) ⟨4233788, by rfl⟩ : syracuseStep 5645051 = 8467577) B8467577
theorem B22947967 : Blo 868566 22947967 := bstep (se 1 (by rfl) ⟨17210975, by rfl⟩ : syracuseStep 22947967 = 34421951) B34421951
theorem B4401377 : Blo 868566 4401377 := bstep (se 2 (by rfl) ⟨1650516, by rfl⟩ : syracuseStep 4401377 = 3301033) B3301033
theorem B40151375 : Blo 868566 40151375 := bstep (se 1 (by rfl) ⟨30113531, by rfl⟩ : syracuseStep 40151375 = 60227063) B60227063
theorem B2931497 : Blo 868566 2931497 := bstep (se 2 (by rfl) ⟨1099311, by rfl⟩ : syracuseStep 2931497 = 2198623) B2198623
theorem B869147 : Blo 868566 869147 := bstep (se 1 (by rfl) ⟨651860, by rfl⟩ : syracuseStep 869147 = 1303721) B1303721
theorem B870655 : Blo 868566 870655 := bstep (se 1 (by rfl) ⟨652991, by rfl⟩ : syracuseStep 870655 = 1305983) B1305983
theorem B871743 : Blo 868566 871743 := bstep (se 1 (by rfl) ⟨653807, by rfl⟩ : syracuseStep 871743 = 1307615) B1307615
theorem B28299233 : Blo 868566 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B1236971 : Blo 868566 1236971 := bstep (se 1 (by rfl) ⟨927728, by rfl⟩ : syracuseStep 1236971 = 1855457) B1855457
theorem B1958939 : Blo 868566 1958939 := bstep (se 1 (by rfl) ⟨1469204, by rfl⟩ : syracuseStep 1958939 = 2938409) B2938409
theorem B1762345 : Blo 868566 1762345 := bstep (se 2 (by rfl) ⟨660879, by rfl⟩ : syracuseStep 1762345 = 1321759) B1321759
theorem B5301733 : Blo 868566 5301733 := bstep (se 4 (by rfl) ⟨497037, by rfl⟩ : syracuseStep 5301733 = 994075) B994075
theorem B1960415 : Blo 868566 1960415 := bstep (se 1 (by rfl) ⟨1470311, by rfl⟩ : syracuseStep 1960415 = 2940623) B2940623
theorem B7433855 : Blo 868566 7433855 := bstep (se 1 (by rfl) ⟨5575391, by rfl⟩ : syracuseStep 7433855 = 11150783) B11150783
theorem B8351743 : Blo 868566 8351743 := bstep (se 1 (by rfl) ⟨6263807, by rfl⟩ : syracuseStep 8351743 = 12527615) B12527615
theorem B122389157 : Blo 868566 122389157 := bstep (se 4 (by rfl) ⟨11473983, by rfl⟩ : syracuseStep 122389157 = 22947967) B22947967
theorem B4955903 : Blo 868566 4955903 := bstep (se 1 (by rfl) ⟨3716927, by rfl⟩ : syracuseStep 4955903 = 7433855) B7433855
theorem B2207047 : Blo 868566 2207047 := bstep (se 1 (by rfl) ⟨1655285, by rfl⟩ : syracuseStep 2207047 = 3310571) B3310571
theorem B4174163 : Blo 868566 4174163 := bstep (se 1 (by rfl) ⟨3130622, by rfl⟩ : syracuseStep 4174163 = 6261245) B6261245
theorem B4829939 : Blo 868566 4829939 := bstep (se 1 (by rfl) ⟨3622454, by rfl⟩ : syracuseStep 4829939 = 7244909) B7244909
theorem B2934251 : Blo 868566 2934251 := bstep (se 1 (by rfl) ⟨2200688, by rfl⟩ : syracuseStep 2934251 = 4401377) B4401377
theorem B16961005 : Blo 868566 16961005 := bstep (se 3 (by rfl) ⟨3180188, by rfl⟩ : syracuseStep 16961005 = 6360377) B6360377
theorem B1954331 : Blo 868566 1954331 := bstep (se 1 (by rfl) ⟨1465748, by rfl⟩ : syracuseStep 1954331 = 2931497) B2931497
theorem B3298589 : Blo 868566 3298589 := bstep (se 3 (by rfl) ⟨618485, by rfl⟩ : syracuseStep 3298589 = 1236971) B1236971
theorem B2349793 : Blo 868566 2349793 := bstep (se 2 (by rfl) ⟨881172, by rfl⟩ : syracuseStep 2349793 = 1762345) B1762345
theorem B7068977 : Blo 868566 7068977 := bstep (se 2 (by rfl) ⟨2650866, by rfl⟩ : syracuseStep 7068977 = 5301733) B5301733
theorem B28207379 : Blo 868566 28207379 := bstep (se 1 (by rfl) ⟨21155534, by rfl⟩ : syracuseStep 28207379 = 42311069) B42311069
theorem B11135657 : Blo 868566 11135657 := bstep (se 2 (by rfl) ⟨4175871, by rfl⟩ : syracuseStep 11135657 = 8351743) B8351743
theorem B3763367 : Blo 868566 3763367 := bstep (se 1 (by rfl) ⟨2822525, by rfl⟩ : syracuseStep 3763367 = 5645051) B5645051
theorem B1305959 : Blo 868566 1305959 := bstep (se 1 (by rfl) ⟨979469, by rfl⟩ : syracuseStep 1305959 = 1958939) B1958939
theorem B26767583 : Blo 868566 26767583 := bstep (se 1 (by rfl) ⟨20075687, by rfl⟩ : syracuseStep 26767583 = 40151375) B40151375
theorem B1306943 : Blo 868566 1306943 := bstep (se 1 (by rfl) ⟨980207, by rfl⟩ : syracuseStep 1306943 = 1960415) B1960415
theorem B75464621 : Blo 868566 75464621 := bstep (se 3 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 75464621 = 28299233) B28299233
theorem B81592771 : Blo 868566 81592771 := bstep (se 1 (by rfl) ⟨61194578, by rfl⟩ : syracuseStep 81592771 = 122389157) B122389157
theorem B2199059 : Blo 868566 2199059 := bstep (se 1 (by rfl) ⟨1649294, by rfl⟩ : syracuseStep 2199059 = 3298589) B3298589
theorem B3219959 : Blo 868566 3219959 := bstep (se 1 (by rfl) ⟨2414969, by rfl⟩ : syracuseStep 3219959 = 4829939) B4829939
theorem B50309747 : Blo 868566 50309747 := bstep (se 1 (by rfl) ⟨37732310, by rfl⟩ : syracuseStep 50309747 = 75464621) B75464621
theorem B12532229 : Blo 868566 12532229 := bstep (se 4 (by rfl) ⟨1174896, by rfl⟩ : syracuseStep 12532229 = 2349793) B2349793
theorem B7423771 : Blo 868566 7423771 := bstep (se 1 (by rfl) ⟨5567828, by rfl⟩ : syracuseStep 7423771 = 11135657) B11135657
theorem B2508911 : Blo 868566 2508911 := bstep (se 1 (by rfl) ⟨1881683, by rfl⟩ : syracuseStep 2508911 = 3763367) B3763367
theorem B870639 : Blo 868566 870639 := bstep (se 1 (by rfl) ⟨652979, by rfl⟩ : syracuseStep 870639 = 1305959) B1305959
theorem B90458693 : Blo 868566 90458693 := bstep (se 4 (by rfl) ⟨8480502, by rfl⟩ : syracuseStep 90458693 = 16961005) B16961005
theorem B17845055 : Blo 868566 17845055 := bstep (se 1 (by rfl) ⟨13383791, by rfl⟩ : syracuseStep 17845055 = 26767583) B26767583
theorem B871295 : Blo 868566 871295 := bstep (se 1 (by rfl) ⟨653471, by rfl⟩ : syracuseStep 871295 = 1306943) B1306943
theorem B1956167 : Blo 868566 1956167 := bstep (se 1 (by rfl) ⟨1467125, by rfl⟩ : syracuseStep 1956167 = 2934251) B2934251
theorem B1302887 : Blo 868566 1302887 := bstep (se 1 (by rfl) ⟨977165, by rfl⟩ : syracuseStep 1302887 = 1954331) B1954331
theorem B2942729 : Blo 868566 2942729 := bstep (se 2 (by rfl) ⟨1103523, by rfl⟩ : syracuseStep 2942729 = 2207047) B2207047
theorem B4712651 : Blo 868566 4712651 := bstep (se 1 (by rfl) ⟨3534488, by rfl⟩ : syracuseStep 4712651 = 7068977) B7068977
theorem B3303935 : Blo 868566 3303935 := bstep (se 1 (by rfl) ⟨2477951, by rfl⟩ : syracuseStep 3303935 = 4955903) B4955903
theorem B18804919 : Blo 868566 18804919 := bstep (se 1 (by rfl) ⟨14103689, by rfl⟩ : syracuseStep 18804919 = 28207379) B28207379
theorem B2782775 : Blo 868566 2782775 := bstep (se 1 (by rfl) ⟨2087081, by rfl⟩ : syracuseStep 2782775 = 4174163) B4174163
theorem B108790361 : Blo 868566 108790361 := bstep (se 2 (by rfl) ⟨40796385, by rfl⟩ : syracuseStep 108790361 = 81592771) B81592771
theorem B8586557 : Blo 868566 8586557 := bstep (se 3 (by rfl) ⟨1609979, by rfl⟩ : syracuseStep 8586557 = 3219959) B3219959
theorem B1672607 : Blo 868566 1672607 := bstep (se 1 (by rfl) ⟨1254455, by rfl⟩ : syracuseStep 1672607 = 2508911) B2508911
theorem B11896703 : Blo 868566 11896703 := bstep (se 1 (by rfl) ⟨8922527, by rfl⟩ : syracuseStep 11896703 = 17845055) B17845055
theorem B9898361 : Blo 868566 9898361 := bstep (se 2 (by rfl) ⟨3711885, by rfl⟩ : syracuseStep 9898361 = 7423771) B7423771
theorem B25073225 : Blo 868566 25073225 := bstep (se 2 (by rfl) ⟨9402459, by rfl⟩ : syracuseStep 25073225 = 18804919) B18804919
theorem B2202623 : Blo 868566 2202623 := bstep (se 1 (by rfl) ⟨1651967, by rfl⟩ : syracuseStep 2202623 = 3303935) B3303935
theorem B60305795 : Blo 868566 60305795 := bstep (se 1 (by rfl) ⟨45229346, by rfl⟩ : syracuseStep 60305795 = 90458693) B90458693
theorem B7420733 : Blo 868566 7420733 := bstep (se 3 (by rfl) ⟨1391387, by rfl⟩ : syracuseStep 7420733 = 2782775) B2782775
theorem B868591 : Blo 868566 868591 := bstep (se 1 (by rfl) ⟨651443, by rfl⟩ : syracuseStep 868591 = 1302887) B1302887
theorem B33539831 : Blo 868566 33539831 := bstep (se 1 (by rfl) ⟨25154873, by rfl⟩ : syracuseStep 33539831 = 50309747) B50309747
theorem B1466039 : Blo 868566 1466039 := bstep (se 1 (by rfl) ⟨1099529, by rfl⟩ : syracuseStep 1466039 = 2199059) B2199059
theorem B1304111 : Blo 868566 1304111 := bstep (se 1 (by rfl) ⟨978083, by rfl⟩ : syracuseStep 1304111 = 1956167) B1956167
theorem B1961819 : Blo 868566 1961819 := bstep (se 1 (by rfl) ⟨1471364, by rfl⟩ : syracuseStep 1961819 = 2942729) B2942729
theorem B3141767 : Blo 868566 3141767 := bstep (se 1 (by rfl) ⟨2356325, by rfl⟩ : syracuseStep 3141767 = 4712651) B4712651
theorem B8354819 : Blo 868566 8354819 := bstep (se 1 (by rfl) ⟨6266114, by rfl⟩ : syracuseStep 8354819 = 12532229) B12532229
theorem B7931135 : Blo 868566 7931135 := bstep (se 1 (by rfl) ⟨5948351, by rfl⟩ : syracuseStep 7931135 = 11896703) B11896703
theorem B16715483 : Blo 868566 16715483 := bstep (se 1 (by rfl) ⟨12536612, by rfl⟩ : syracuseStep 16715483 = 25073225) B25073225
theorem B4460285 : Blo 868566 4460285 := bstep (se 3 (by rfl) ⟨836303, by rfl⟩ : syracuseStep 4460285 = 1672607) B1672607
theorem B72526907 : Blo 868566 72526907 := bstep (se 1 (by rfl) ⟨54395180, by rfl⟩ : syracuseStep 72526907 = 108790361) B108790361
theorem B22359887 : Blo 868566 22359887 := bstep (se 1 (by rfl) ⟨16769915, by rfl⟩ : syracuseStep 22359887 = 33539831) B33539831
theorem B6598907 : Blo 868566 6598907 := bstep (se 1 (by rfl) ⟨4949180, by rfl⟩ : syracuseStep 6598907 = 9898361) B9898361
theorem B869407 : Blo 868566 869407 := bstep (se 1 (by rfl) ⟨652055, by rfl⟩ : syracuseStep 869407 = 1304111) B1304111
theorem B5724371 : Blo 868566 5724371 := bstep (se 1 (by rfl) ⟨4293278, by rfl⟩ : syracuseStep 5724371 = 8586557) B8586557
theorem B1468415 : Blo 868566 1468415 := bstep (se 1 (by rfl) ⟨1101311, by rfl⟩ : syracuseStep 1468415 = 2202623) B2202623
theorem B977359 : Blo 868566 977359 := bstep (se 1 (by rfl) ⟨733019, by rfl⟩ : syracuseStep 977359 = 1466039) B1466039
theorem B1307879 : Blo 868566 1307879 := bstep (se 1 (by rfl) ⟨980909, by rfl⟩ : syracuseStep 1307879 = 1961819) B1961819
theorem B2094511 : Blo 868566 2094511 := bstep (se 1 (by rfl) ⟨1570883, by rfl⟩ : syracuseStep 2094511 = 3141767) B3141767
theorem B40203863 : Blo 868566 40203863 := bstep (se 1 (by rfl) ⟨30152897, by rfl⟩ : syracuseStep 40203863 = 60305795) B60305795
theorem B4947155 : Blo 868566 4947155 := bstep (se 1 (by rfl) ⟨3710366, by rfl⟩ : syracuseStep 4947155 = 7420733) B7420733
theorem B5569879 : Blo 868566 5569879 := bstep (se 1 (by rfl) ⟨4177409, by rfl⟩ : syracuseStep 5569879 = 8354819) B8354819
theorem B11143655 : Blo 868566 11143655 := bstep (se 1 (by rfl) ⟨8357741, by rfl⟩ : syracuseStep 11143655 = 16715483) B16715483
theorem B2792681 : Blo 868566 2792681 := bstep (se 2 (by rfl) ⟨1047255, by rfl⟩ : syracuseStep 2792681 = 2094511) B2094511
theorem B4399271 : Blo 868566 4399271 := bstep (se 1 (by rfl) ⟨3299453, by rfl⟩ : syracuseStep 4399271 = 6598907) B6598907
theorem B21149693 : Blo 868566 21149693 := bstep (se 3 (by rfl) ⟨3965567, by rfl⟩ : syracuseStep 21149693 = 7931135) B7931135
theorem B3816247 : Blo 868566 3816247 := bstep (se 1 (by rfl) ⟨2862185, by rfl⟩ : syracuseStep 3816247 = 5724371) B5724371
theorem B48351271 : Blo 868566 48351271 := bstep (se 1 (by rfl) ⟨36263453, by rfl⟩ : syracuseStep 48351271 = 72526907) B72526907
theorem B871919 : Blo 868566 871919 := bstep (se 1 (by rfl) ⟨653939, by rfl⟩ : syracuseStep 871919 = 1307879) B1307879
theorem B7426505 : Blo 868566 7426505 := bstep (se 2 (by rfl) ⟨2784939, by rfl⟩ : syracuseStep 7426505 = 5569879) B5569879
theorem B3298103 : Blo 868566 3298103 := bstep (se 1 (by rfl) ⟨2473577, by rfl⟩ : syracuseStep 3298103 = 4947155) B4947155
theorem B2973523 : Blo 868566 2973523 := bstep (se 1 (by rfl) ⟨2230142, by rfl⟩ : syracuseStep 2973523 = 4460285) B4460285
theorem B1303145 : Blo 868566 1303145 := bstep (se 2 (by rfl) ⟨488679, by rfl⟩ : syracuseStep 1303145 = 977359) B977359
theorem B978943 : Blo 868566 978943 := bstep (se 1 (by rfl) ⟨734207, by rfl⟩ : syracuseStep 978943 = 1468415) B1468415
theorem B14906591 : Blo 868566 14906591 := bstep (se 1 (by rfl) ⟨11179943, by rfl⟩ : syracuseStep 14906591 = 22359887) B22359887
theorem B26802575 : Blo 868566 26802575 := bstep (se 1 (by rfl) ⟨20101931, by rfl⟩ : syracuseStep 26802575 = 40203863) B40203863
theorem B4951003 : Blo 868566 4951003 := bstep (se 1 (by rfl) ⟨3713252, by rfl⟩ : syracuseStep 4951003 = 7426505) B7426505
theorem B2198735 : Blo 868566 2198735 := bstep (se 1 (by rfl) ⟨1649051, by rfl⟩ : syracuseStep 2198735 = 3298103) B3298103
theorem B9937727 : Blo 868566 9937727 := bstep (se 1 (by rfl) ⟨7453295, by rfl⟩ : syracuseStep 9937727 = 14906591) B14906591
theorem B5088329 : Blo 868566 5088329 := bstep (se 2 (by rfl) ⟨1908123, by rfl⟩ : syracuseStep 5088329 = 3816247) B3816247
theorem B14099795 : Blo 868566 14099795 := bstep (se 1 (by rfl) ⟨10574846, by rfl⟩ : syracuseStep 14099795 = 21149693) B21149693
theorem B17868383 : Blo 868566 17868383 := bstep (se 1 (by rfl) ⟨13401287, by rfl⟩ : syracuseStep 17868383 = 26802575) B26802575
theorem B64468361 : Blo 868566 64468361 := bstep (se 2 (by rfl) ⟨24175635, by rfl⟩ : syracuseStep 64468361 = 48351271) B48351271
theorem B2932847 : Blo 868566 2932847 := bstep (se 1 (by rfl) ⟨2199635, by rfl⟩ : syracuseStep 2932847 = 4399271) B4399271
theorem B868763 : Blo 868566 868763 := bstep (se 1 (by rfl) ⟨651572, by rfl⟩ : syracuseStep 868763 = 1303145) B1303145
theorem B7429103 : Blo 868566 7429103 := bstep (se 1 (by rfl) ⟨5571827, by rfl⟩ : syracuseStep 7429103 = 11143655) B11143655
theorem B1861787 : Blo 868566 1861787 := bstep (se 1 (by rfl) ⟨1396340, by rfl⟩ : syracuseStep 1861787 = 2792681) B2792681
theorem B1305257 : Blo 868566 1305257 := bstep (se 2 (by rfl) ⟨489471, by rfl⟩ : syracuseStep 1305257 = 978943) B978943
theorem B3964697 : Blo 868566 3964697 := bstep (se 2 (by rfl) ⟨1486761, by rfl⟩ : syracuseStep 3964697 = 2973523) B2973523
theorem B4952735 : Blo 868566 4952735 := bstep (se 1 (by rfl) ⟨3714551, by rfl⟩ : syracuseStep 4952735 = 7429103) B7429103
theorem B6625151 : Blo 868566 6625151 := bstep (se 1 (by rfl) ⟨4968863, by rfl⟩ : syracuseStep 6625151 = 9937727) B9937727
theorem B6601337 : Blo 868566 6601337 := bstep (se 2 (by rfl) ⟨2475501, by rfl⟩ : syracuseStep 6601337 = 4951003) B4951003
theorem B3392219 : Blo 868566 3392219 := bstep (se 1 (by rfl) ⟨2544164, by rfl⟩ : syracuseStep 3392219 = 5088329) B5088329
theorem B11912255 : Blo 868566 11912255 := bstep (se 1 (by rfl) ⟨8934191, by rfl⟩ : syracuseStep 11912255 = 17868383) B17868383
theorem B870171 : Blo 868566 870171 := bstep (se 1 (by rfl) ⟨652628, by rfl⟩ : syracuseStep 870171 = 1305257) B1305257
theorem B42978907 : Blo 868566 42978907 := bstep (se 1 (by rfl) ⟨32234180, by rfl⟩ : syracuseStep 42978907 = 64468361) B64468361
theorem B2643131 : Blo 868566 2643131 := bstep (se 1 (by rfl) ⟨1982348, by rfl⟩ : syracuseStep 2643131 = 3964697) B3964697
theorem B1955231 : Blo 868566 1955231 := bstep (se 1 (by rfl) ⟨1466423, by rfl⟩ : syracuseStep 1955231 = 2932847) B2932847
theorem B1465823 : Blo 868566 1465823 := bstep (se 1 (by rfl) ⟨1099367, by rfl⟩ : syracuseStep 1465823 = 2198735) B2198735
theorem B9399863 : Blo 868566 9399863 := bstep (se 1 (by rfl) ⟨7049897, by rfl⟩ : syracuseStep 9399863 = 14099795) B14099795
theorem B1241191 : Blo 868566 1241191 := bstep (se 1 (by rfl) ⟨930893, by rfl⟩ : syracuseStep 1241191 = 1861787) B1861787
theorem B2261479 : Blo 868566 2261479 := bstep (se 1 (by rfl) ⟨1696109, by rfl⟩ : syracuseStep 2261479 = 3392219) B3392219
theorem B6266575 : Blo 868566 6266575 := bstep (se 1 (by rfl) ⟨4699931, by rfl⟩ : syracuseStep 6266575 = 9399863) B9399863
theorem B229220837 : Blo 868566 229220837 := bstep (se 4 (by rfl) ⟨21489453, by rfl⟩ : syracuseStep 229220837 = 42978907) B42978907
theorem B4400891 : Blo 868566 4400891 := bstep (se 1 (by rfl) ⟨3300668, by rfl⟩ : syracuseStep 4400891 = 6601337) B6601337
theorem B7941503 : Blo 868566 7941503 := bstep (se 1 (by rfl) ⟨5956127, by rfl⟩ : syracuseStep 7941503 = 11912255) B11912255
theorem B1654921 : Blo 868566 1654921 := bstep (se 2 (by rfl) ⟨620595, by rfl⟩ : syracuseStep 1654921 = 1241191) B1241191
theorem B3301823 : Blo 868566 3301823 := bstep (se 1 (by rfl) ⟨2476367, by rfl⟩ : syracuseStep 3301823 = 4952735) B4952735
theorem B1762087 : Blo 868566 1762087 := bstep (se 1 (by rfl) ⟨1321565, by rfl⟩ : syracuseStep 1762087 = 2643131) B2643131
theorem B1303487 : Blo 868566 1303487 := bstep (se 1 (by rfl) ⟨977615, by rfl⟩ : syracuseStep 1303487 = 1955231) B1955231
theorem B4416767 : Blo 868566 4416767 := bstep (se 1 (by rfl) ⟨3312575, by rfl⟩ : syracuseStep 4416767 = 6625151) B6625151
theorem B977215 : Blo 868566 977215 := bstep (se 1 (by rfl) ⟨732911, by rfl⟩ : syracuseStep 977215 = 1465823) B1465823
theorem B3015305 : Blo 868566 3015305 := bstep (se 2 (by rfl) ⟨1130739, by rfl⟩ : syracuseStep 3015305 = 2261479) B2261479
theorem B2201215 : Blo 868566 2201215 := bstep (se 1 (by rfl) ⟨1650911, by rfl⟩ : syracuseStep 2201215 = 3301823) B3301823
theorem B2206561 : Blo 868566 2206561 := bstep (se 2 (by rfl) ⟨827460, by rfl⟩ : syracuseStep 2206561 = 1654921) B1654921
theorem B152813891 : Blo 868566 152813891 := bstep (se 1 (by rfl) ⟨114610418, by rfl⟩ : syracuseStep 152813891 = 229220837) B229220837
theorem B868991 : Blo 868566 868991 := bstep (se 1 (by rfl) ⟨651743, by rfl⟩ : syracuseStep 868991 = 1303487) B1303487
theorem B2933927 : Blo 868566 2933927 := bstep (se 1 (by rfl) ⟨2200445, by rfl⟩ : syracuseStep 2933927 = 4400891) B4400891
theorem B5294335 : Blo 868566 5294335 := bstep (se 1 (by rfl) ⟨3970751, by rfl⟩ : syracuseStep 5294335 = 7941503) B7941503
theorem B2349449 : Blo 868566 2349449 := bstep (se 2 (by rfl) ⟨881043, by rfl⟩ : syracuseStep 2349449 = 1762087) B1762087
theorem B1302953 : Blo 868566 1302953 := bstep (se 2 (by rfl) ⟨488607, by rfl⟩ : syracuseStep 1302953 = 977215) B977215
theorem B2944511 : Blo 868566 2944511 := bstep (se 1 (by rfl) ⟨2208383, by rfl⟩ : syracuseStep 2944511 = 4416767) B4416767
theorem B33421733 : Blo 868566 33421733 := bstep (se 4 (by rfl) ⟨3133287, by rfl⟩ : syracuseStep 33421733 = 6266575) B6266575
theorem B101875927 : Blo 868566 101875927 := bstep (se 1 (by rfl) ⟨76406945, by rfl⟩ : syracuseStep 101875927 = 152813891) B152813891
theorem B2010203 : Blo 868566 2010203 := bstep (se 1 (by rfl) ⟨1507652, by rfl⟩ : syracuseStep 2010203 = 3015305) B3015305
theorem B7059113 : Blo 868566 7059113 := bstep (se 2 (by rfl) ⟨2647167, by rfl⟩ : syracuseStep 7059113 = 5294335) B5294335
theorem B868635 : Blo 868566 868635 := bstep (se 1 (by rfl) ⟨651476, by rfl⟩ : syracuseStep 868635 = 1302953) B1302953
theorem B2934953 : Blo 868566 2934953 := bstep (se 2 (by rfl) ⟨1100607, by rfl⟩ : syracuseStep 2934953 = 2201215) B2201215
theorem B1955951 : Blo 868566 1955951 := bstep (se 1 (by rfl) ⟨1466963, by rfl⟩ : syracuseStep 1955951 = 2933927) B2933927
theorem B2942081 : Blo 868566 2942081 := bstep (se 2 (by rfl) ⟨1103280, by rfl⟩ : syracuseStep 2942081 = 2206561) B2206561
theorem B1566299 : Blo 868566 1566299 := bstep (se 1 (by rfl) ⟨1174724, by rfl⟩ : syracuseStep 1566299 = 2349449) B2349449
theorem B1963007 : Blo 868566 1963007 := bstep (se 1 (by rfl) ⟨1472255, by rfl⟩ : syracuseStep 1963007 = 2944511) B2944511
theorem B22281155 : Blo 868566 22281155 := bstep (se 1 (by rfl) ⟨16710866, by rfl⟩ : syracuseStep 22281155 = 33421733) B33421733
theorem B14854103 : Blo 868566 14854103 := bstep (se 1 (by rfl) ⟨11140577, by rfl⟩ : syracuseStep 14854103 = 22281155) B22281155
theorem B135834569 : Blo 868566 135834569 := bstep (se 2 (by rfl) ⟨50937963, by rfl⟩ : syracuseStep 135834569 = 101875927) B101875927
theorem B4706075 : Blo 868566 4706075 := bstep (se 1 (by rfl) ⟨3529556, by rfl⟩ : syracuseStep 4706075 = 7059113) B7059113
theorem B1956635 : Blo 868566 1956635 := bstep (se 1 (by rfl) ⟨1467476, by rfl⟩ : syracuseStep 1956635 = 2934953) B2934953
theorem B1303967 : Blo 868566 1303967 := bstep (se 1 (by rfl) ⟨977975, by rfl⟩ : syracuseStep 1303967 = 1955951) B1955951
theorem B1961387 : Blo 868566 1961387 := bstep (se 1 (by rfl) ⟨1471040, by rfl⟩ : syracuseStep 1961387 = 2942081) B2942081
theorem B1044199 : Blo 868566 1044199 := bstep (se 1 (by rfl) ⟨783149, by rfl⟩ : syracuseStep 1044199 = 1566299) B1566299
theorem B1340135 : Blo 868566 1340135 := bstep (se 1 (by rfl) ⟨1005101, by rfl⟩ : syracuseStep 1340135 = 2010203) B2010203
theorem B1308671 : Blo 868566 1308671 := bstep (se 1 (by rfl) ⟨981503, by rfl⟩ : syracuseStep 1308671 = 1963007) B1963007
theorem B9902735 : Blo 868566 9902735 := bstep (se 1 (by rfl) ⟨7427051, by rfl⟩ : syracuseStep 9902735 = 14854103) B14854103
theorem B893423 : Blo 868566 893423 := bstep (se 1 (by rfl) ⟨670067, by rfl⟩ : syracuseStep 893423 = 1340135) B1340135
theorem B1392265 : Blo 868566 1392265 := bstep (se 2 (by rfl) ⟨522099, by rfl⟩ : syracuseStep 1392265 = 1044199) B1044199
theorem B869311 : Blo 868566 869311 := bstep (se 1 (by rfl) ⟨651983, by rfl⟩ : syracuseStep 869311 = 1303967) B1303967
theorem B90556379 : Blo 868566 90556379 := bstep (se 1 (by rfl) ⟨67917284, by rfl⟩ : syracuseStep 90556379 = 135834569) B135834569
theorem B872447 : Blo 868566 872447 := bstep (se 1 (by rfl) ⟨654335, by rfl⟩ : syracuseStep 872447 = 1308671) B1308671
theorem B3137383 : Blo 868566 3137383 := bstep (se 1 (by rfl) ⟨2353037, by rfl⟩ : syracuseStep 3137383 = 4706075) B4706075
theorem B1304423 : Blo 868566 1304423 := bstep (se 1 (by rfl) ⟨978317, by rfl⟩ : syracuseStep 1304423 = 1956635) B1956635
theorem B1307591 : Blo 868566 1307591 := bstep (se 1 (by rfl) ⟨980693, by rfl⟩ : syracuseStep 1307591 = 1961387) B1961387
theorem B60370919 : Blo 868566 60370919 := bstep (se 1 (by rfl) ⟨45278189, by rfl⟩ : syracuseStep 60370919 = 90556379) B90556379
theorem B6601823 : Blo 868566 6601823 := bstep (se 1 (by rfl) ⟨4951367, by rfl⟩ : syracuseStep 6601823 = 9902735) B9902735
theorem B869615 : Blo 868566 869615 := bstep (se 1 (by rfl) ⟨652211, by rfl⟩ : syracuseStep 869615 = 1304423) B1304423
theorem B871727 : Blo 868566 871727 := bstep (se 1 (by rfl) ⟨653795, by rfl⟩ : syracuseStep 871727 = 1307591) B1307591
theorem B1856353 : Blo 868566 1856353 := bstep (se 2 (by rfl) ⟨696132, by rfl⟩ : syracuseStep 1856353 = 1392265) B1392265
theorem B4183177 : Blo 868566 4183177 := bstep (se 2 (by rfl) ⟨1568691, by rfl⟩ : syracuseStep 4183177 = 3137383) B3137383
theorem B2382461 : Blo 868566 2382461 := bstep (se 3 (by rfl) ⟨446711, by rfl⟩ : syracuseStep 2382461 = 893423) B893423
theorem B5577569 : Blo 868566 5577569 := bstep (se 2 (by rfl) ⟨2091588, by rfl⟩ : syracuseStep 5577569 = 4183177) B4183177
theorem B40247279 : Blo 868566 40247279 := bstep (se 1 (by rfl) ⟨30185459, by rfl⟩ : syracuseStep 40247279 = 60370919) B60370919
theorem B4401215 : Blo 868566 4401215 := bstep (se 1 (by rfl) ⟨3300911, by rfl⟩ : syracuseStep 4401215 = 6601823) B6601823
theorem B1588307 : Blo 868566 1588307 := bstep (se 1 (by rfl) ⟨1191230, by rfl⟩ : syracuseStep 1588307 = 2382461) B2382461
theorem B2475137 : Blo 868566 2475137 := bstep (se 2 (by rfl) ⟨928176, by rfl⟩ : syracuseStep 2475137 = 1856353) B1856353
theorem B4235485 : Blo 868566 4235485 := bstep (se 3 (by rfl) ⟨794153, by rfl⟩ : syracuseStep 4235485 = 1588307) B1588307
theorem B6600365 : Blo 868566 6600365 := bstep (se 3 (by rfl) ⟨1237568, by rfl⟩ : syracuseStep 6600365 = 2475137) B2475137
theorem B3718379 : Blo 868566 3718379 := bstep (se 1 (by rfl) ⟨2788784, by rfl⟩ : syracuseStep 3718379 = 5577569) B5577569
theorem B2934143 : Blo 868566 2934143 := bstep (se 1 (by rfl) ⟨2200607, by rfl⟩ : syracuseStep 2934143 = 4401215) B4401215
theorem B26831519 : Blo 868566 26831519 := bstep (se 1 (by rfl) ⟨20123639, by rfl⟩ : syracuseStep 26831519 = 40247279) B40247279
theorem B4400243 : Blo 868566 4400243 := bstep (se 1 (by rfl) ⟨3300182, by rfl⟩ : syracuseStep 4400243 = 6600365) B6600365
theorem B5647313 : Blo 868566 5647313 := bstep (se 2 (by rfl) ⟨2117742, by rfl⟩ : syracuseStep 5647313 = 4235485) B4235485
theorem B2478919 : Blo 868566 2478919 := bstep (se 1 (by rfl) ⟨1859189, by rfl⟩ : syracuseStep 2478919 = 3718379) B3718379
theorem B1956095 : Blo 868566 1956095 := bstep (se 1 (by rfl) ⟨1467071, by rfl⟩ : syracuseStep 1956095 = 2934143) B2934143
theorem B17887679 : Blo 868566 17887679 := bstep (se 1 (by rfl) ⟨13415759, by rfl⟩ : syracuseStep 17887679 = 26831519) B26831519
theorem B2933495 : Blo 868566 2933495 := bstep (se 1 (by rfl) ⟨2200121, by rfl⟩ : syracuseStep 2933495 = 4400243) B4400243
theorem B1304063 : Blo 868566 1304063 := bstep (se 1 (by rfl) ⟨978047, by rfl⟩ : syracuseStep 1304063 = 1956095) B1956095
theorem B3305225 : Blo 868566 3305225 := bstep (se 2 (by rfl) ⟨1239459, by rfl⟩ : syracuseStep 3305225 = 2478919) B2478919
theorem B3764875 : Blo 868566 3764875 := bstep (se 1 (by rfl) ⟨2823656, by rfl⟩ : syracuseStep 3764875 = 5647313) B5647313
theorem B11925119 : Blo 868566 11925119 := bstep (se 1 (by rfl) ⟨8943839, by rfl⟩ : syracuseStep 11925119 = 17887679) B17887679
theorem B5019833 : Blo 868566 5019833 := bstep (se 2 (by rfl) ⟨1882437, by rfl⟩ : syracuseStep 5019833 = 3764875) B3764875
theorem B2203483 : Blo 868566 2203483 := bstep (se 1 (by rfl) ⟨1652612, by rfl⟩ : syracuseStep 2203483 = 3305225) B3305225
theorem B869375 : Blo 868566 869375 := bstep (se 1 (by rfl) ⟨652031, by rfl⟩ : syracuseStep 869375 = 1304063) B1304063
theorem B7950079 : Blo 868566 7950079 := bstep (se 1 (by rfl) ⟨5962559, by rfl⟩ : syracuseStep 7950079 = 11925119) B11925119
theorem B1955663 : Blo 868566 1955663 := bstep (se 1 (by rfl) ⟨1466747, by rfl⟩ : syracuseStep 1955663 = 2933495) B2933495
theorem B3346555 : Blo 868566 3346555 := bstep (se 1 (by rfl) ⟨2509916, by rfl⟩ : syracuseStep 3346555 = 5019833) B5019833
theorem B10600105 : Blo 868566 10600105 := bstep (se 2 (by rfl) ⟨3975039, by rfl⟩ : syracuseStep 10600105 = 7950079) B7950079
theorem B2937977 : Blo 868566 2937977 := bstep (se 2 (by rfl) ⟨1101741, by rfl⟩ : syracuseStep 2937977 = 2203483) B2203483
theorem B1303775 : Blo 868566 1303775 := bstep (se 1 (by rfl) ⟨977831, by rfl⟩ : syracuseStep 1303775 = 1955663) B1955663
theorem B4462073 : Blo 868566 4462073 := bstep (se 2 (by rfl) ⟨1673277, by rfl⟩ : syracuseStep 4462073 = 3346555) B3346555
theorem B14133473 : Blo 868566 14133473 := bstep (se 2 (by rfl) ⟨5300052, by rfl⟩ : syracuseStep 14133473 = 10600105) B10600105
theorem B869183 : Blo 868566 869183 := bstep (se 1 (by rfl) ⟨651887, by rfl⟩ : syracuseStep 869183 = 1303775) B1303775
theorem B1958651 : Blo 868566 1958651 := bstep (se 1 (by rfl) ⟨1468988, by rfl⟩ : syracuseStep 1958651 = 2937977) B2937977
theorem B9422315 : Blo 868566 9422315 := bstep (se 1 (by rfl) ⟨7066736, by rfl⟩ : syracuseStep 9422315 = 14133473) B14133473
theorem B2974715 : Blo 868566 2974715 := bstep (se 1 (by rfl) ⟨2231036, by rfl⟩ : syracuseStep 2974715 = 4462073) B4462073
theorem B1305767 : Blo 868566 1305767 := bstep (se 1 (by rfl) ⟨979325, by rfl⟩ : syracuseStep 1305767 = 1958651) B1958651
theorem B1983143 : Blo 868566 1983143 := bstep (se 1 (by rfl) ⟨1487357, by rfl⟩ : syracuseStep 1983143 = 2974715) B2974715
theorem B870511 : Blo 868566 870511 := bstep (se 1 (by rfl) ⟨652883, by rfl⟩ : syracuseStep 870511 = 1305767) B1305767
theorem B6281543 : Blo 868566 6281543 := bstep (se 1 (by rfl) ⟨4711157, by rfl⟩ : syracuseStep 6281543 = 9422315) B9422315
theorem B1322095 : Blo 868566 1322095 := bstep (se 1 (by rfl) ⟨991571, by rfl⟩ : syracuseStep 1322095 = 1983143) B1983143
theorem B4187695 : Blo 868566 4187695 := bstep (se 1 (by rfl) ⟨3140771, by rfl⟩ : syracuseStep 4187695 = 6281543) B6281543
theorem B5583593 : Blo 868566 5583593 := bstep (se 2 (by rfl) ⟨2093847, by rfl⟩ : syracuseStep 5583593 = 4187695) B4187695
theorem B1762793 : Blo 868566 1762793 := bstep (se 2 (by rfl) ⟨661047, by rfl⟩ : syracuseStep 1762793 = 1322095) B1322095
theorem B3722395 : Blo 868566 3722395 := bstep (se 1 (by rfl) ⟨2791796, by rfl⟩ : syracuseStep 3722395 = 5583593) B5583593
theorem B1175195 : Blo 868566 1175195 := bstep (se 1 (by rfl) ⟨881396, by rfl⟩ : syracuseStep 1175195 = 1762793) B1762793
theorem B4963193 : Blo 868566 4963193 := bstep (se 2 (by rfl) ⟨1861197, by rfl⟩ : syracuseStep 4963193 = 3722395) B3722395
theorem B3133853 : Blo 868566 3133853 := bstep (se 3 (by rfl) ⟨587597, by rfl⟩ : syracuseStep 3133853 = 1175195) B1175195
theorem B2089235 : Blo 868566 2089235 := bstep (se 1 (by rfl) ⟨1566926, by rfl⟩ : syracuseStep 2089235 = 3133853) B3133853
theorem B3308795 : Blo 868566 3308795 := bstep (se 1 (by rfl) ⟨2481596, by rfl⟩ : syracuseStep 3308795 = 4963193) B4963193
theorem B2205863 : Blo 868566 2205863 := bstep (se 1 (by rfl) ⟨1654397, by rfl⟩ : syracuseStep 2205863 = 3308795) B3308795
theorem B1392823 : Blo 868566 1392823 := bstep (se 1 (by rfl) ⟨1044617, by rfl⟩ : syracuseStep 1392823 = 2089235) B2089235
theorem B1857097 : Blo 868566 1857097 := bstep (se 2 (by rfl) ⟨696411, by rfl⟩ : syracuseStep 1857097 = 1392823) B1392823
theorem B1470575 : Blo 868566 1470575 := bstep (se 1 (by rfl) ⟨1102931, by rfl⟩ : syracuseStep 1470575 = 2205863) B2205863
theorem B2476129 : Blo 868566 2476129 := bstep (se 2 (by rfl) ⟨928548, by rfl⟩ : syracuseStep 2476129 = 1857097) B1857097
theorem B980383 : Blo 868566 980383 := bstep (se 1 (by rfl) ⟨735287, by rfl⟩ : syracuseStep 980383 = 1470575) B1470575
theorem B3301505 : Blo 868566 3301505 := bstep (se 2 (by rfl) ⟨1238064, by rfl⟩ : syracuseStep 3301505 = 2476129) B2476129
theorem B1307177 : Blo 868566 1307177 := bstep (se 2 (by rfl) ⟨490191, by rfl⟩ : syracuseStep 1307177 = 980383) B980383
theorem B2201003 : Blo 868566 2201003 := bstep (se 1 (by rfl) ⟨1650752, by rfl⟩ : syracuseStep 2201003 = 3301505) B3301505
theorem B871451 : Blo 868566 871451 := bstep (se 1 (by rfl) ⟨653588, by rfl⟩ : syracuseStep 871451 = 1307177) B1307177
theorem B1467335 : Blo 868566 1467335 := bstep (se 1 (by rfl) ⟨1100501, by rfl⟩ : syracuseStep 1467335 = 2201003) B2201003
theorem B978223 : Blo 868566 978223 := bstep (se 1 (by rfl) ⟨733667, by rfl⟩ : syracuseStep 978223 = 1467335) B1467335
theorem B1304297 : Blo 868566 1304297 := bstep (se 2 (by rfl) ⟨489111, by rfl⟩ : syracuseStep 1304297 = 978223) B978223
theorem B869531 : Blo 868566 869531 := bstep (se 1 (by rfl) ⟨652148, by rfl⟩ : syracuseStep 869531 = 1304297) B1304297

theorem C0 (j : ℕ) (h1 : 217141 ≤ j) (h2 : j ≤ 217840) : Blo 868566 (4 * j + 3) := by
  interval_cases j
  · exact B868567
  · exact B868571
  · exact B868575
  · exact B868579
  · exact B868583
  · exact B868587
  · exact B868591
  · exact B868595
  · exact B868599
  · exact B868603
  · exact B868607
  · exact B868611
  · exact B868615
  · exact B868619
  · exact B868623
  · exact B868627
  · exact B868631
  · exact B868635
  · exact B868639
  · exact B868643
  · exact B868647
  · exact B868651
  · exact B868655
  · exact B868659
  · exact B868663
  · exact B868667
  · exact B868671
  · exact B868675
  · exact B868679
  · exact B868683
  · exact B868687
  · exact B868691
  · exact B868695
  · exact B868699
  · exact B868703
  · exact B868707
  · exact B868711
  · exact B868715
  · exact B868719
  · exact B868723
  · exact B868727
  · exact B868731
  · exact B868735
  · exact B868739
  · exact B868743
  · exact B868747
  · exact B868751
  · exact B868755
  · exact B868759
  · exact B868763
  · exact B868767
  · exact B868771
  · exact B868775
  · exact B868779
  · exact B868783
  · exact B868787
  · exact B868791
  · exact B868795
  · exact B868799
  · exact B868803
  · exact B868807
  · exact B868811
  · exact B868815
  · exact B868819
  · exact B868823
  · exact B868827
  · exact B868831
  · exact B868835
  · exact B868839
  · exact B868843
  · exact B868847
  · exact B868851
  · exact B868855
  · exact B868859
  · exact B868863
  · exact B868867
  · exact B868871
  · exact B868875
  · exact B868879
  · exact B868883
  · exact B868887
  · exact B868891
  · exact B868895
  · exact B868899
  · exact B868903
  · exact B868907
  · exact B868911
  · exact B868915
  · exact B868919
  · exact B868923
  · exact B868927
  · exact B868931
  · exact B868935
  · exact B868939
  · exact B868943
  · exact B868947
  · exact B868951
  · exact B868955
  · exact B868959
  · exact B868963
  · exact B868967
  · exact B868971
  · exact B868975
  · exact B868979
  · exact B868983
  · exact B868987
  · exact B868991
  · exact B868995
  · exact B868999
  · exact B869003
  · exact B869007
  · exact B869011
  · exact B869015
  · exact B869019
  · exact B869023
  · exact B869027
  · exact B869031
  · exact B869035
  · exact B869039
  · exact B869043
  · exact B869047
  · exact B869051
  · exact B869055
  · exact B869059
  · exact B869063
  · exact B869067
  · exact B869071
  · exact B869075
  · exact B869079
  · exact B869083
  · exact B869087
  · exact B869091
  · exact B869095
  · exact B869099
  · exact B869103
  · exact B869107
  · exact B869111
  · exact B869115
  · exact B869119
  · exact B869123
  · exact B869127
  · exact B869131
  · exact B869135
  · exact B869139
  · exact B869143
  · exact B869147
  · exact B869151
  · exact B869155
  · exact B869159
  · exact B869163
  · exact B869167
  · exact B869171
  · exact B869175
  · exact B869179
  · exact B869183
  · exact B869187
  · exact B869191
  · exact B869195
  · exact B869199
  · exact B869203
  · exact B869207
  · exact B869211
  · exact B869215
  · exact B869219
  · exact B869223
  · exact B869227
  · exact B869231
  · exact B869235
  · exact B869239
  · exact B869243
  · exact B869247
  · exact B869251
  · exact B869255
  · exact B869259
  · exact B869263
  · exact B869267
  · exact B869271
  · exact B869275
  · exact B869279
  · exact B869283
  · exact B869287
  · exact B869291
  · exact B869295
  · exact B869299
  · exact B869303
  · exact B869307
  · exact B869311
  · exact B869315
  · exact B869319
  · exact B869323
  · exact B869327
  · exact B869331
  · exact B869335
  · exact B869339
  · exact B869343
  · exact B869347
  · exact B869351
  · exact B869355
  · exact B869359
  · exact B869363
  · exact B869367
  · exact B869371
  · exact B869375
  · exact B869379
  · exact B869383
  · exact B869387
  · exact B869391
  · exact B869395
  · exact B869399
  · exact B869403
  · exact B869407
  · exact B869411
  · exact B869415
  · exact B869419
  · exact B869423
  · exact B869427
  · exact B869431
  · exact B869435
  · exact B869439
  · exact B869443
  · exact B869447
  · exact B869451
  · exact B869455
  · exact B869459
  · exact B869463
  · exact B869467
  · exact B869471
  · exact B869475
  · exact B869479
  · exact B869483
  · exact B869487
  · exact B869491
  · exact B869495
  · exact B869499
  · exact B869503
  · exact B869507
  · exact B869511
  · exact B869515
  · exact B869519
  · exact B869523
  · exact B869527
  · exact B869531
  · exact B869535
  · exact B869539
  · exact B869543
  · exact B869547
  · exact B869551
  · exact B869555
  · exact B869559
  · exact B869563
  · exact B869567
  · exact B869571
  · exact B869575
  · exact B869579
  · exact B869583
  · exact B869587
  · exact B869591
  · exact B869595
  · exact B869599
  · exact B869603
  · exact B869607
  · exact B869611
  · exact B869615
  · exact B869619
  · exact B869623
  · exact B869627
  · exact B869631
  · exact B869635
  · exact B869639
  · exact B869643
  · exact B869647
  · exact B869651
  · exact B869655
  · exact B869659
  · exact B869663
  · exact B869667
  · exact B869671
  · exact B869675
  · exact B869679
  · exact B869683
  · exact B869687
  · exact B869691
  · exact B869695
  · exact B869699
  · exact B869703
  · exact B869707
  · exact B869711
  · exact B869715
  · exact B869719
  · exact B869723
  · exact B869727
  · exact B869731
  · exact B869735
  · exact B869739
  · exact B869743
  · exact B869747
  · exact B869751
  · exact B869755
  · exact B869759
  · exact B869763
  · exact B869767
  · exact B869771
  · exact B869775
  · exact B869779
  · exact B869783
  · exact B869787
  · exact B869791
  · exact B869795
  · exact B869799
  · exact B869803
  · exact B869807
  · exact B869811
  · exact B869815
  · exact B869819
  · exact B869823
  · exact B869827
  · exact B869831
  · exact B869835
  · exact B869839
  · exact B869843
  · exact B869847
  · exact B869851
  · exact B869855
  · exact B869859
  · exact B869863
  · exact B869867
  · exact B869871
  · exact B869875
  · exact B869879
  · exact B869883
  · exact B869887
  · exact B869891
  · exact B869895
  · exact B869899
  · exact B869903
  · exact B869907
  · exact B869911
  · exact B869915
  · exact B869919
  · exact B869923
  · exact B869927
  · exact B869931
  · exact B869935
  · exact B869939
  · exact B869943
  · exact B869947
  · exact B869951
  · exact B869955
  · exact B869959
  · exact B869963
  · exact B869967
  · exact B869971
  · exact B869975
  · exact B869979
  · exact B869983
  · exact B869987
  · exact B869991
  · exact B869995
  · exact B869999
  · exact B870003
  · exact B870007
  · exact B870011
  · exact B870015
  · exact B870019
  · exact B870023
  · exact B870027
  · exact B870031
  · exact B870035
  · exact B870039
  · exact B870043
  · exact B870047
  · exact B870051
  · exact B870055
  · exact B870059
  · exact B870063
  · exact B870067
  · exact B870071
  · exact B870075
  · exact B870079
  · exact B870083
  · exact B870087
  · exact B870091
  · exact B870095
  · exact B870099
  · exact B870103
  · exact B870107
  · exact B870111
  · exact B870115
  · exact B870119
  · exact B870123
  · exact B870127
  · exact B870131
  · exact B870135
  · exact B870139
  · exact B870143
  · exact B870147
  · exact B870151
  · exact B870155
  · exact B870159
  · exact B870163
  · exact B870167
  · exact B870171
  · exact B870175
  · exact B870179
  · exact B870183
  · exact B870187
  · exact B870191
  · exact B870195
  · exact B870199
  · exact B870203
  · exact B870207
  · exact B870211
  · exact B870215
  · exact B870219
  · exact B870223
  · exact B870227
  · exact B870231
  · exact B870235
  · exact B870239
  · exact B870243
  · exact B870247
  · exact B870251
  · exact B870255
  · exact B870259
  · exact B870263
  · exact B870267
  · exact B870271
  · exact B870275
  · exact B870279
  · exact B870283
  · exact B870287
  · exact B870291
  · exact B870295
  · exact B870299
  · exact B870303
  · exact B870307
  · exact B870311
  · exact B870315
  · exact B870319
  · exact B870323
  · exact B870327
  · exact B870331
  · exact B870335
  · exact B870339
  · exact B870343
  · exact B870347
  · exact B870351
  · exact B870355
  · exact B870359
  · exact B870363
  · exact B870367
  · exact B870371
  · exact B870375
  · exact B870379
  · exact B870383
  · exact B870387
  · exact B870391
  · exact B870395
  · exact B870399
  · exact B870403
  · exact B870407
  · exact B870411
  · exact B870415
  · exact B870419
  · exact B870423
  · exact B870427
  · exact B870431
  · exact B870435
  · exact B870439
  · exact B870443
  · exact B870447
  · exact B870451
  · exact B870455
  · exact B870459
  · exact B870463
  · exact B870467
  · exact B870471
  · exact B870475
  · exact B870479
  · exact B870483
  · exact B870487
  · exact B870491
  · exact B870495
  · exact B870499
  · exact B870503
  · exact B870507
  · exact B870511
  · exact B870515
  · exact B870519
  · exact B870523
  · exact B870527
  · exact B870531
  · exact B870535
  · exact B870539
  · exact B870543
  · exact B870547
  · exact B870551
  · exact B870555
  · exact B870559
  · exact B870563
  · exact B870567
  · exact B870571
  · exact B870575
  · exact B870579
  · exact B870583
  · exact B870587
  · exact B870591
  · exact B870595
  · exact B870599
  · exact B870603
  · exact B870607
  · exact B870611
  · exact B870615
  · exact B870619
  · exact B870623
  · exact B870627
  · exact B870631
  · exact B870635
  · exact B870639
  · exact B870643
  · exact B870647
  · exact B870651
  · exact B870655
  · exact B870659
  · exact B870663
  · exact B870667
  · exact B870671
  · exact B870675
  · exact B870679
  · exact B870683
  · exact B870687
  · exact B870691
  · exact B870695
  · exact B870699
  · exact B870703
  · exact B870707
  · exact B870711
  · exact B870715
  · exact B870719
  · exact B870723
  · exact B870727
  · exact B870731
  · exact B870735
  · exact B870739
  · exact B870743
  · exact B870747
  · exact B870751
  · exact B870755
  · exact B870759
  · exact B870763
  · exact B870767
  · exact B870771
  · exact B870775
  · exact B870779
  · exact B870783
  · exact B870787
  · exact B870791
  · exact B870795
  · exact B870799
  · exact B870803
  · exact B870807
  · exact B870811
  · exact B870815
  · exact B870819
  · exact B870823
  · exact B870827
  · exact B870831
  · exact B870835
  · exact B870839
  · exact B870843
  · exact B870847
  · exact B870851
  · exact B870855
  · exact B870859
  · exact B870863
  · exact B870867
  · exact B870871
  · exact B870875
  · exact B870879
  · exact B870883
  · exact B870887
  · exact B870891
  · exact B870895
  · exact B870899
  · exact B870903
  · exact B870907
  · exact B870911
  · exact B870915
  · exact B870919
  · exact B870923
  · exact B870927
  · exact B870931
  · exact B870935
  · exact B870939
  · exact B870943
  · exact B870947
  · exact B870951
  · exact B870955
  · exact B870959
  · exact B870963
  · exact B870967
  · exact B870971
  · exact B870975
  · exact B870979
  · exact B870983
  · exact B870987
  · exact B870991
  · exact B870995
  · exact B870999
  · exact B871003
  · exact B871007
  · exact B871011
  · exact B871015
  · exact B871019
  · exact B871023
  · exact B871027
  · exact B871031
  · exact B871035
  · exact B871039
  · exact B871043
  · exact B871047
  · exact B871051
  · exact B871055
  · exact B871059
  · exact B871063
  · exact B871067
  · exact B871071
  · exact B871075
  · exact B871079
  · exact B871083
  · exact B871087
  · exact B871091
  · exact B871095
  · exact B871099
  · exact B871103
  · exact B871107
  · exact B871111
  · exact B871115
  · exact B871119
  · exact B871123
  · exact B871127
  · exact B871131
  · exact B871135
  · exact B871139
  · exact B871143
  · exact B871147
  · exact B871151
  · exact B871155
  · exact B871159
  · exact B871163
  · exact B871167
  · exact B871171
  · exact B871175
  · exact B871179
  · exact B871183
  · exact B871187
  · exact B871191
  · exact B871195
  · exact B871199
  · exact B871203
  · exact B871207
  · exact B871211
  · exact B871215
  · exact B871219
  · exact B871223
  · exact B871227
  · exact B871231
  · exact B871235
  · exact B871239
  · exact B871243
  · exact B871247
  · exact B871251
  · exact B871255
  · exact B871259
  · exact B871263
  · exact B871267
  · exact B871271
  · exact B871275
  · exact B871279
  · exact B871283
  · exact B871287
  · exact B871291
  · exact B871295
  · exact B871299
  · exact B871303
  · exact B871307
  · exact B871311
  · exact B871315
  · exact B871319
  · exact B871323
  · exact B871327
  · exact B871331
  · exact B871335
  · exact B871339
  · exact B871343
  · exact B871347
  · exact B871351
  · exact B871355
  · exact B871359
  · exact B871363

theorem C1 (j : ℕ) (h1 : 217841 ≤ j) (h2 : j ≤ 218140) : Blo 868566 (4 * j + 3) := by
  interval_cases j
  · exact B871367
  · exact B871371
  · exact B871375
  · exact B871379
  · exact B871383
  · exact B871387
  · exact B871391
  · exact B871395
  · exact B871399
  · exact B871403
  · exact B871407
  · exact B871411
  · exact B871415
  · exact B871419
  · exact B871423
  · exact B871427
  · exact B871431
  · exact B871435
  · exact B871439
  · exact B871443
  · exact B871447
  · exact B871451
  · exact B871455
  · exact B871459
  · exact B871463
  · exact B871467
  · exact B871471
  · exact B871475
  · exact B871479
  · exact B871483
  · exact B871487
  · exact B871491
  · exact B871495
  · exact B871499
  · exact B871503
  · exact B871507
  · exact B871511
  · exact B871515
  · exact B871519
  · exact B871523
  · exact B871527
  · exact B871531
  · exact B871535
  · exact B871539
  · exact B871543
  · exact B871547
  · exact B871551
  · exact B871555
  · exact B871559
  · exact B871563
  · exact B871567
  · exact B871571
  · exact B871575
  · exact B871579
  · exact B871583
  · exact B871587
  · exact B871591
  · exact B871595
  · exact B871599
  · exact B871603
  · exact B871607
  · exact B871611
  · exact B871615
  · exact B871619
  · exact B871623
  · exact B871627
  · exact B871631
  · exact B871635
  · exact B871639
  · exact B871643
  · exact B871647
  · exact B871651
  · exact B871655
  · exact B871659
  · exact B871663
  · exact B871667
  · exact B871671
  · exact B871675
  · exact B871679
  · exact B871683
  · exact B871687
  · exact B871691
  · exact B871695
  · exact B871699
  · exact B871703
  · exact B871707
  · exact B871711
  · exact B871715
  · exact B871719
  · exact B871723
  · exact B871727
  · exact B871731
  · exact B871735
  · exact B871739
  · exact B871743
  · exact B871747
  · exact B871751
  · exact B871755
  · exact B871759
  · exact B871763
  · exact B871767
  · exact B871771
  · exact B871775
  · exact B871779
  · exact B871783
  · exact B871787
  · exact B871791
  · exact B871795
  · exact B871799
  · exact B871803
  · exact B871807
  · exact B871811
  · exact B871815
  · exact B871819
  · exact B871823
  · exact B871827
  · exact B871831
  · exact B871835
  · exact B871839
  · exact B871843
  · exact B871847
  · exact B871851
  · exact B871855
  · exact B871859
  · exact B871863
  · exact B871867
  · exact B871871
  · exact B871875
  · exact B871879
  · exact B871883
  · exact B871887
  · exact B871891
  · exact B871895
  · exact B871899
  · exact B871903
  · exact B871907
  · exact B871911
  · exact B871915
  · exact B871919
  · exact B871923
  · exact B871927
  · exact B871931
  · exact B871935
  · exact B871939
  · exact B871943
  · exact B871947
  · exact B871951
  · exact B871955
  · exact B871959
  · exact B871963
  · exact B871967
  · exact B871971
  · exact B871975
  · exact B871979
  · exact B871983
  · exact B871987
  · exact B871991
  · exact B871995
  · exact B871999
  · exact B872003
  · exact B872007
  · exact B872011
  · exact B872015
  · exact B872019
  · exact B872023
  · exact B872027
  · exact B872031
  · exact B872035
  · exact B872039
  · exact B872043
  · exact B872047
  · exact B872051
  · exact B872055
  · exact B872059
  · exact B872063
  · exact B872067
  · exact B872071
  · exact B872075
  · exact B872079
  · exact B872083
  · exact B872087
  · exact B872091
  · exact B872095
  · exact B872099
  · exact B872103
  · exact B872107
  · exact B872111
  · exact B872115
  · exact B872119
  · exact B872123
  · exact B872127
  · exact B872131
  · exact B872135
  · exact B872139
  · exact B872143
  · exact B872147
  · exact B872151
  · exact B872155
  · exact B872159
  · exact B872163
  · exact B872167
  · exact B872171
  · exact B872175
  · exact B872179
  · exact B872183
  · exact B872187
  · exact B872191
  · exact B872195
  · exact B872199
  · exact B872203
  · exact B872207
  · exact B872211
  · exact B872215
  · exact B872219
  · exact B872223
  · exact B872227
  · exact B872231
  · exact B872235
  · exact B872239
  · exact B872243
  · exact B872247
  · exact B872251
  · exact B872255
  · exact B872259
  · exact B872263
  · exact B872267
  · exact B872271
  · exact B872275
  · exact B872279
  · exact B872283
  · exact B872287
  · exact B872291
  · exact B872295
  · exact B872299
  · exact B872303
  · exact B872307
  · exact B872311
  · exact B872315
  · exact B872319
  · exact B872323
  · exact B872327
  · exact B872331
  · exact B872335
  · exact B872339
  · exact B872343
  · exact B872347
  · exact B872351
  · exact B872355
  · exact B872359
  · exact B872363
  · exact B872367
  · exact B872371
  · exact B872375
  · exact B872379
  · exact B872383
  · exact B872387
  · exact B872391
  · exact B872395
  · exact B872399
  · exact B872403
  · exact B872407
  · exact B872411
  · exact B872415
  · exact B872419
  · exact B872423
  · exact B872427
  · exact B872431
  · exact B872435
  · exact B872439
  · exact B872443
  · exact B872447
  · exact B872451
  · exact B872455
  · exact B872459
  · exact B872463
  · exact B872467
  · exact B872471
  · exact B872475
  · exact B872479
  · exact B872483
  · exact B872487
  · exact B872491
  · exact B872495
  · exact B872499
  · exact B872503
  · exact B872507
  · exact B872511
  · exact B872515
  · exact B872519
  · exact B872523
  · exact B872527
  · exact B872531
  · exact B872535
  · exact B872539
  · exact B872543
  · exact B872547
  · exact B872551
  · exact B872555
  · exact B872559
  · exact B872563

theorem solution (m : ℕ) (hlo : 868566 ≤ m) (hhi : m ≤ 872566) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 217141 ≤ j := by omega
    have hj2 : j ≤ 218140 := by omega
    have hb : Blo 868566 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 217841 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
