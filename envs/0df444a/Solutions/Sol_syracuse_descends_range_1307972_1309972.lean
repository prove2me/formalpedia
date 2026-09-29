-- Prove2me | solution 1 for syracuse_descends_range_1307972_1309972
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:30.166813+00:00
-- url     : https://prove2.me/submissions/38926871-2b26-4655-8e1a-1659d38d73f6

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


theorem B4415525 : Blo 1307972 4415525 := bbase (se 4 (by rfl) ⟨413955, by rfl⟩ : syracuseStep 4415525 = 827911) (by norm_num)
theorem B1417253 : Blo 1307972 1417253 := bbase (se 4 (by rfl) ⟨132867, by rfl⟩ : syracuseStep 1417253 = 265735) (by norm_num)
theorem B3315077 : Blo 1307972 3315077 := bbase (se 4 (by rfl) ⟨310788, by rfl⟩ : syracuseStep 3315077 = 621577) (by norm_num)
theorem B2359381 : Blo 1307972 2359381 := bbase (se 8 (by rfl) ⟨13824, by rfl⟩ : syracuseStep 2359381 = 27649) (by norm_num)
theorem B4972661 : Blo 1307972 4972661 := bbase (se 5 (by rfl) ⟨233093, by rfl⟩ : syracuseStep 4972661 = 466187) (by norm_num)
theorem B1991117 : Blo 1307972 1991117 := bbase (se 3 (by rfl) ⟨373334, by rfl⟩ : syracuseStep 1991117 = 746669) (by norm_num)
theorem B4415957 : Blo 1307972 4415957 := bbase (se 7 (by rfl) ⟨51749, by rfl⟩ : syracuseStep 4415957 = 103499) (by norm_num)
theorem B3146197 : Blo 1307972 3146197 := bbase (se 7 (by rfl) ⟨36869, by rfl⟩ : syracuseStep 3146197 = 73739) (by norm_num)
theorem B1573333 : Blo 1307972 1573333 := bbase (se 7 (by rfl) ⟨18437, by rfl⟩ : syracuseStep 1573333 = 36875) (by norm_num)
theorem B4719077 : Blo 1307972 4719077 := bbase (se 4 (by rfl) ⟨442413, by rfl⟩ : syracuseStep 4719077 = 884827) (by norm_num)
theorem B6644213 : Blo 1307972 6644213 := bbase (se 5 (by rfl) ⟨311447, by rfl⟩ : syracuseStep 6644213 = 622895) (by norm_num)
theorem B6291989 : Blo 1307972 6291989 := bbase (se 6 (by rfl) ⟨147468, by rfl⟩ : syracuseStep 6291989 = 294937) (by norm_num)
theorem B2654741 : Blo 1307972 2654741 := bbase (se 6 (by rfl) ⟨62220, by rfl⟩ : syracuseStep 2654741 = 124441) (by norm_num)
theorem B3539557 : Blo 1307972 3539557 := bbase (se 4 (by rfl) ⟨331833, by rfl⟩ : syracuseStep 3539557 = 663667) (by norm_num)
theorem B1655417 : Blo 1307972 1655417 := bbase (se 2 (by rfl) ⟨620781, by rfl⟩ : syracuseStep 1655417 = 1241563) (by norm_num)
theorem B11936405 : Blo 1307972 11936405 := bbase (se 6 (by rfl) ⟨279759, by rfl⟩ : syracuseStep 11936405 = 559519) (by norm_num)
theorem B2097829 : Blo 1307972 2097829 := bbase (se 4 (by rfl) ⟨196671, by rfl⟩ : syracuseStep 2097829 = 393343) (by norm_num)
theorem B1655473 : Blo 1307972 1655473 := bbase (se 2 (by rfl) ⟨620802, by rfl⟩ : syracuseStep 1655473 = 1241605) (by norm_num)
theorem B6292181 : Blo 1307972 6292181 := bbase (se 7 (by rfl) ⟨73736, by rfl⟩ : syracuseStep 6292181 = 147473) (by norm_num)
theorem B5587717 : Blo 1307972 5587717 := bbase (se 4 (by rfl) ⟨523848, by rfl⟩ : syracuseStep 5587717 = 1047697) (by norm_num)
theorem B1655569 : Blo 1307972 1655569 := bbase (se 2 (by rfl) ⟨620838, by rfl⟩ : syracuseStep 1655569 = 1241677) (by norm_num)
theorem B5309221 : Blo 1307972 5309221 := bbase (se 4 (by rfl) ⟨497739, by rfl⟩ : syracuseStep 5309221 = 995479) (by norm_num)
theorem B3728197 : Blo 1307972 3728197 := bbase (se 4 (by rfl) ⟨349518, by rfl⟩ : syracuseStep 3728197 = 699037) (by norm_num)
theorem B2360173 : Blo 1307972 2360173 := bbase (se 3 (by rfl) ⟨442532, by rfl⟩ : syracuseStep 2360173 = 885065) (by norm_num)
theorem B4416389 : Blo 1307972 4416389 := bbase (se 4 (by rfl) ⟨414036, by rfl⟩ : syracuseStep 4416389 = 828073) (by norm_num)
theorem B6628229 : Blo 1307972 6628229 := bbase (se 4 (by rfl) ⟨621396, by rfl⟩ : syracuseStep 6628229 = 1242793) (by norm_num)
theorem B1655741 : Blo 1307972 1655741 := bbase (se 3 (by rfl) ⟨310451, by rfl⟩ : syracuseStep 1655741 = 620903) (by norm_num)
theorem B1491905 : Blo 1307972 1491905 := bbase (se 2 (by rfl) ⟨559464, by rfl⟩ : syracuseStep 1491905 = 1118929) (by norm_num)
theorem B2483149 : Blo 1307972 2483149 := bbase (se 3 (by rfl) ⟨465590, by rfl⟩ : syracuseStep 2483149 = 931181) (by norm_num)
theorem B1655797 : Blo 1307972 1655797 := bbase (se 5 (by rfl) ⟨77615, by rfl⟩ : syracuseStep 1655797 = 155231) (by norm_num)
theorem B3146813 : Blo 1307972 3146813 := bbase (se 3 (by rfl) ⟨590027, by rfl⟩ : syracuseStep 3146813 = 1180055) (by norm_num)
theorem B1655893 : Blo 1307972 1655893 := bbase (se 8 (by rfl) ⟨9702, by rfl⟩ : syracuseStep 1655893 = 19405) (by norm_num)
theorem B6292565 : Blo 1307972 6292565 := bbase (se 8 (by rfl) ⟨36870, by rfl⟩ : syracuseStep 6292565 = 73741) (by norm_num)
theorem B2483293 : Blo 1307972 2483293 := bbase (se 3 (by rfl) ⟨465617, by rfl⟩ : syracuseStep 2483293 = 931235) (by norm_num)
theorem B2794637 : Blo 1307972 2794637 := bbase (se 3 (by rfl) ⟨523994, by rfl⟩ : syracuseStep 2794637 = 1047989) (by norm_num)
theorem B2655389 : Blo 1307972 2655389 := bbase (se 3 (by rfl) ⟨497885, by rfl⟩ : syracuseStep 2655389 = 995771) (by norm_num)
theorem B2835685 : Blo 1307972 2835685 := bbase (se 4 (by rfl) ⟨265845, by rfl⟩ : syracuseStep 2835685 = 531691) (by norm_num)
theorem B2483453 : Blo 1307972 2483453 := bbase (se 3 (by rfl) ⟨465647, by rfl⟩ : syracuseStep 2483453 = 931295) (by norm_num)
theorem B1656065 : Blo 1307972 1656065 := bbase (se 2 (by rfl) ⟨621024, by rfl⟩ : syracuseStep 1656065 = 1242049) (by norm_num)
theorem B2794781 : Blo 1307972 2794781 := bbase (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) (by norm_num)
theorem B4416821 : Blo 1307972 4416821 := bbase (se 5 (by rfl) ⟨207038, by rfl⟩ : syracuseStep 4416821 = 414077) (by norm_num)
theorem B1656121 : Blo 1307972 1656121 := bbase (se 2 (by rfl) ⟨621045, by rfl⟩ : syracuseStep 1656121 = 1242091) (by norm_num)
theorem B2483597 : Blo 1307972 2483597 := bbase (se 3 (by rfl) ⟨465674, by rfl⟩ : syracuseStep 2483597 = 931349) (by norm_num)
theorem B1656217 : Blo 1307972 1656217 := bbase (se 2 (by rfl) ⟨621081, by rfl⟩ : syracuseStep 1656217 = 1242163) (by norm_num)
theorem B3311077 : Blo 1307972 3311077 := bbase (se 4 (by rfl) ⟨310413, by rfl⟩ : syracuseStep 3311077 = 620827) (by norm_num)
theorem B5588453 : Blo 1307972 5588453 := bbase (se 4 (by rfl) ⟨523917, by rfl⟩ : syracuseStep 5588453 = 1047835) (by norm_num)
theorem B7071221 : Blo 1307972 7071221 := bbase (se 5 (by rfl) ⟨331463, by rfl⟩ : syracuseStep 7071221 = 662927) (by norm_num)
theorem B1492489 : Blo 1307972 1492489 := bbase (se 2 (by rfl) ⟨559683, by rfl⟩ : syracuseStep 1492489 = 1119367) (by norm_num)
theorem B1656389 : Blo 1307972 1656389 := bbase (se 4 (by rfl) ⟨155286, by rfl⟩ : syracuseStep 1656389 = 310573) (by norm_num)
theorem B3311189 : Blo 1307972 3311189 := bbase (se 8 (by rfl) ⟨19401, by rfl⟩ : syracuseStep 3311189 = 38803) (by norm_num)
theorem B7456373 : Blo 1307972 7456373 := bbase (se 5 (by rfl) ⟨349517, by rfl⟩ : syracuseStep 7456373 = 699035) (by norm_num)
theorem B1656445 : Blo 1307972 1656445 := bbase (se 3 (by rfl) ⟨310583, by rfl⟩ : syracuseStep 1656445 = 621167) (by norm_num)
theorem B2795141 : Blo 1307972 2795141 := bbase (se 4 (by rfl) ⟨262044, by rfl⟩ : syracuseStep 2795141 = 524089) (by norm_num)
theorem B2483885 : Blo 1307972 2483885 := bbase (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) (by norm_num)
theorem B1656541 : Blo 1307972 1656541 := bbase (se 3 (by rfl) ⟨310601, by rfl⟩ : syracuseStep 1656541 = 621203) (by norm_num)
theorem B4417253 : Blo 1307972 4417253 := bbase (se 4 (by rfl) ⟨414117, by rfl⟩ : syracuseStep 4417253 = 828235) (by norm_num)
theorem B5310197 : Blo 1307972 5310197 := bbase (se 5 (by rfl) ⟨248915, by rfl⟩ : syracuseStep 5310197 = 497831) (by norm_num)
theorem B7956245 : Blo 1307972 7956245 := bbase (se 6 (by rfl) ⟨186474, by rfl⟩ : syracuseStep 7956245 = 372949) (by norm_num)
theorem B3311381 : Blo 1307972 3311381 := bbase (se 6 (by rfl) ⟨77610, by rfl⟩ : syracuseStep 3311381 = 155221) (by norm_num)
theorem B3360565 : Blo 1307972 3360565 := bbase (se 5 (by rfl) ⟨157526, by rfl⟩ : syracuseStep 3360565 = 315053) (by norm_num)
theorem B2484037 : Blo 1307972 2484037 := bbase (se 4 (by rfl) ⟨232878, by rfl⟩ : syracuseStep 2484037 = 465757) (by norm_num)
theorem B1656713 : Blo 1307972 1656713 := bbase (se 2 (by rfl) ⟨621267, by rfl⟩ : syracuseStep 1656713 = 1242535) (by norm_num)
theorem B2238365 : Blo 1307972 2238365 := bbase (se 3 (by rfl) ⟨419693, by rfl⟩ : syracuseStep 2238365 = 839387) (by norm_num)
theorem B4196261 : Blo 1307972 4196261 := bbase (se 4 (by rfl) ⟨393399, by rfl⟩ : syracuseStep 4196261 = 786799) (by norm_num)
theorem B1656769 : Blo 1307972 1656769 := bbase (se 2 (by rfl) ⟨621288, by rfl⟩ : syracuseStep 1656769 = 1242577) (by norm_num)
theorem B4966373 : Blo 1307972 4966373 := bbase (se 4 (by rfl) ⟨465597, by rfl⟩ : syracuseStep 4966373 = 931195) (by norm_num)
theorem B2942981 : Blo 1307972 2942981 := bbase (se 4 (by rfl) ⟨275904, by rfl⟩ : syracuseStep 2942981 = 551809) (by norm_num)
theorem B1656865 : Blo 1307972 1656865 := bbase (se 2 (by rfl) ⟨621324, by rfl⟩ : syracuseStep 1656865 = 1242649) (by norm_num)
theorem B2943053 : Blo 1307972 2943053 := bbase (se 3 (by rfl) ⟨551822, by rfl⟩ : syracuseStep 2943053 = 1103645) (by norm_num)
theorem B3311725 : Blo 1307972 3311725 := bbase (se 3 (by rfl) ⟨620948, by rfl⟩ : syracuseStep 3311725 = 1241897) (by norm_num)
theorem B1493105 : Blo 1307972 1493105 := bbase (se 2 (by rfl) ⟨559914, by rfl⟩ : syracuseStep 1493105 = 1119829) (by norm_num)
theorem B2484341 : Blo 1307972 2484341 := bbase (se 5 (by rfl) ⟨116453, by rfl⟩ : syracuseStep 2484341 = 232907) (by norm_num)
theorem B2943125 : Blo 1307972 2943125 := bbase (se 6 (by rfl) ⟨68979, by rfl⟩ : syracuseStep 2943125 = 137959) (by norm_num)
theorem B4417685 : Blo 1307972 4417685 := bbase (se 6 (by rfl) ⟨103539, by rfl⟩ : syracuseStep 4417685 = 207079) (by norm_num)
theorem B6629525 : Blo 1307972 6629525 := bbase (se 6 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 6629525 = 310759) (by norm_num)
theorem B2017445 : Blo 1307972 2017445 := bbase (se 4 (by rfl) ⟨189135, by rfl⟩ : syracuseStep 2017445 = 378271) (by norm_num)
theorem B4720837 : Blo 1307972 4720837 := bbase (se 4 (by rfl) ⟨442578, by rfl⟩ : syracuseStep 4720837 = 885157) (by norm_num)
theorem B1657037 : Blo 1307972 1657037 := bbase (se 3 (by rfl) ⟨310694, by rfl⟩ : syracuseStep 1657037 = 621389) (by norm_num)
theorem B1493201 : Blo 1307972 1493201 := bbase (se 2 (by rfl) ⟨559950, by rfl⟩ : syracuseStep 1493201 = 1119901) (by norm_num)
theorem B2943197 : Blo 1307972 2943197 := bbase (se 3 (by rfl) ⟨551849, by rfl⟩ : syracuseStep 2943197 = 1103699) (by norm_num)
theorem B3311837 : Blo 1307972 3311837 := bbase (se 3 (by rfl) ⟨620969, by rfl⟩ : syracuseStep 3311837 = 1241939) (by norm_num)
theorem B1657093 : Blo 1307972 1657093 := bbase (se 4 (by rfl) ⟨155352, by rfl⟩ : syracuseStep 1657093 = 310705) (by norm_num)
theorem B2943269 : Blo 1307972 2943269 := bbase (se 4 (by rfl) ⟨275931, by rfl⟩ : syracuseStep 2943269 = 551863) (by norm_num)
theorem B3729701 : Blo 1307972 3729701 := bbase (se 4 (by rfl) ⟨349659, by rfl⟩ : syracuseStep 3729701 = 699319) (by norm_num)
theorem B1657189 : Blo 1307972 1657189 := bbase (se 4 (by rfl) ⟨155361, by rfl⟩ : syracuseStep 1657189 = 310723) (by norm_num)
theorem B2943341 : Blo 1307972 2943341 := bbase (se 3 (by rfl) ⟨551876, by rfl⟩ : syracuseStep 2943341 = 1103753) (by norm_num)
theorem B1493365 : Blo 1307972 1493365 := bbase (se 5 (by rfl) ⟨70001, by rfl⟩ : syracuseStep 1493365 = 140003) (by norm_num)
theorem B3312029 : Blo 1307972 3312029 := bbase (se 3 (by rfl) ⟨621005, by rfl⟩ : syracuseStep 3312029 = 1242011) (by norm_num)
theorem B2943413 : Blo 1307972 2943413 := bbase (se 5 (by rfl) ⟨137972, by rfl⟩ : syracuseStep 2943413 = 275945) (by norm_num)
theorem B2238925 : Blo 1307972 2238925 := bbase (se 3 (by rfl) ⟨419798, by rfl⟩ : syracuseStep 2238925 = 839597) (by norm_num)
theorem B25151957 : Blo 1307972 25151957 := bbase (se 7 (by rfl) ⟨294749, by rfl⟩ : syracuseStep 25151957 = 589499) (by norm_num)
theorem B6048229 : Blo 1307972 6048229 := bbase (se 4 (by rfl) ⟨567021, by rfl⟩ : syracuseStep 6048229 = 1134043) (by norm_num)
theorem B5974517 : Blo 1307972 5974517 := bbase (se 5 (by rfl) ⟨280055, by rfl⟩ : syracuseStep 5974517 = 560111) (by norm_num)
theorem B4721141 : Blo 1307972 4721141 := bbase (se 5 (by rfl) ⟨221303, by rfl⟩ : syracuseStep 4721141 = 442607) (by norm_num)
theorem B2943485 : Blo 1307972 2943485 := bbase (se 3 (by rfl) ⟨551903, by rfl⟩ : syracuseStep 2943485 = 1103807) (by norm_num)
theorem B2796029 : Blo 1307972 2796029 := bbase (se 3 (by rfl) ⟨524255, by rfl⟩ : syracuseStep 2796029 = 1048511) (by norm_num)
theorem B1657361 : Blo 1307972 1657361 := bbase (se 2 (by rfl) ⟨621510, by rfl⟩ : syracuseStep 1657361 = 1243021) (by norm_num)
theorem B6621749 : Blo 1307972 6621749 := bbase (se 5 (by rfl) ⟨310394, by rfl⟩ : syracuseStep 6621749 = 620789) (by norm_num)
theorem B2943557 : Blo 1307972 2943557 := bbase (se 4 (by rfl) ⟨275958, by rfl⟩ : syracuseStep 2943557 = 551917) (by norm_num)
theorem B4418117 : Blo 1307972 4418117 := bbase (se 4 (by rfl) ⟨414198, by rfl⟩ : syracuseStep 4418117 = 828397) (by norm_num)
theorem B1657417 : Blo 1307972 1657417 := bbase (se 2 (by rfl) ⟨621531, by rfl⟩ : syracuseStep 1657417 = 1243063) (by norm_num)
theorem B2943629 : Blo 1307972 2943629 := bbase (se 3 (by rfl) ⟨551930, by rfl⟩ : syracuseStep 2943629 = 1103861) (by norm_num)
theorem B1657513 : Blo 1307972 1657513 := bbase (se 2 (by rfl) ⟨621567, by rfl⟩ : syracuseStep 1657513 = 1243135) (by norm_num)
theorem B2943701 : Blo 1307972 2943701 := bbase (se 7 (by rfl) ⟨34496, by rfl⟩ : syracuseStep 2943701 = 68993) (by norm_num)
theorem B3312373 : Blo 1307972 3312373 := bbase (se 5 (by rfl) ⟨155267, by rfl⟩ : syracuseStep 3312373 = 310535) (by norm_num)
theorem B2796277 : Blo 1307972 2796277 := bbase (se 5 (by rfl) ⟨131075, by rfl⟩ : syracuseStep 2796277 = 262151) (by norm_num)
theorem B2943773 : Blo 1307972 2943773 := bbase (se 3 (by rfl) ⟨551957, by rfl⟩ : syracuseStep 2943773 = 1103915) (by norm_num)
theorem B1862453 : Blo 1307972 1862453 := bbase (se 5 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 1862453 = 174605) (by norm_num)
theorem B7269173 : Blo 1307972 7269173 := bbase (se 5 (by rfl) ⟨340742, by rfl⟩ : syracuseStep 7269173 = 681485) (by norm_num)
theorem B1657685 : Blo 1307972 1657685 := bbase (se 9 (by rfl) ⟨4856, by rfl⟩ : syracuseStep 1657685 = 9713) (by norm_num)
theorem B2943845 : Blo 1307972 2943845 := bbase (se 4 (by rfl) ⟨275985, by rfl⟩ : syracuseStep 2943845 = 551971) (by norm_num)
theorem B3312485 : Blo 1307972 3312485 := bbase (se 4 (by rfl) ⟨310545, by rfl⟩ : syracuseStep 3312485 = 621091) (by norm_num)
theorem B2485093 : Blo 1307972 2485093 := bbase (se 4 (by rfl) ⟨232977, by rfl⟩ : syracuseStep 2485093 = 465955) (by norm_num)
theorem B1657741 : Blo 1307972 1657741 := bbase (se 3 (by rfl) ⟨310826, by rfl⟩ : syracuseStep 1657741 = 621653) (by norm_num)
theorem B2943917 : Blo 1307972 2943917 := bbase (se 3 (by rfl) ⟨551984, by rfl⟩ : syracuseStep 2943917 = 1103969) (by norm_num)
theorem B1657837 : Blo 1307972 1657837 := bbase (se 3 (by rfl) ⟨310844, by rfl⟩ : syracuseStep 1657837 = 621689) (by norm_num)
theorem B2943989 : Blo 1307972 2943989 := bbase (se 5 (by rfl) ⟨137999, by rfl⟩ : syracuseStep 2943989 = 275999) (by norm_num)
theorem B2485237 : Blo 1307972 2485237 := bbase (se 5 (by rfl) ⟨116495, by rfl⟩ : syracuseStep 2485237 = 232991) (by norm_num)
theorem B4418549 : Blo 1307972 4418549 := bbase (se 5 (by rfl) ⟨207119, by rfl⟩ : syracuseStep 4418549 = 414239) (by norm_num)
theorem B8391701 : Blo 1307972 8391701 := bbase (se 6 (by rfl) ⟨196680, by rfl⟩ : syracuseStep 8391701 = 393361) (by norm_num)
theorem B3312677 : Blo 1307972 3312677 := bbase (se 4 (by rfl) ⟨310563, by rfl⟩ : syracuseStep 3312677 = 621127) (by norm_num)
theorem B2944061 : Blo 1307972 2944061 := bbase (se 3 (by rfl) ⟨552011, by rfl⟩ : syracuseStep 2944061 = 1104023) (by norm_num)
theorem B2944133 : Blo 1307972 2944133 := bbase (se 4 (by rfl) ⟨276012, by rfl⟩ : syracuseStep 2944133 = 552025) (by norm_num)
theorem B2485397 : Blo 1307972 2485397 := bbase (se 6 (by rfl) ⟨58251, by rfl⟩ : syracuseStep 2485397 = 116503) (by norm_num)
theorem B2944205 : Blo 1307972 2944205 := bbase (se 3 (by rfl) ⟨552038, by rfl⟩ : syracuseStep 2944205 = 1104077) (by norm_num)
theorem B2796781 : Blo 1307972 2796781 := bbase (se 3 (by rfl) ⟨524396, by rfl⟩ : syracuseStep 2796781 = 1048793) (by norm_num)
theorem B2944277 : Blo 1307972 2944277 := bbase (se 6 (by rfl) ⟨69006, by rfl⟩ : syracuseStep 2944277 = 138013) (by norm_num)
theorem B25849109 : Blo 1307972 25849109 := bbase (se 6 (by rfl) ⟨605838, by rfl⟩ : syracuseStep 25849109 = 1211677) (by norm_num)
theorem B2485541 : Blo 1307972 2485541 := bbase (se 4 (by rfl) ⟨233019, by rfl⟩ : syracuseStep 2485541 = 466039) (by norm_num)
theorem B1863005 : Blo 1307972 1863005 := bbase (se 3 (by rfl) ⟨349313, by rfl⟩ : syracuseStep 1863005 = 698627) (by norm_num)
theorem B2944349 : Blo 1307972 2944349 := bbase (se 3 (by rfl) ⟨552065, by rfl⟩ : syracuseStep 2944349 = 1104131) (by norm_num)
theorem B3313021 : Blo 1307972 3313021 := bbase (se 3 (by rfl) ⟨621191, by rfl⟩ : syracuseStep 3313021 = 1242383) (by norm_num)
theorem B2944421 : Blo 1307972 2944421 := bbase (se 4 (by rfl) ⟨276039, by rfl⟩ : syracuseStep 2944421 = 552079) (by norm_num)
theorem B4418981 : Blo 1307972 4418981 := bbase (se 4 (by rfl) ⟨414279, by rfl⟩ : syracuseStep 4418981 = 828559) (by norm_num)
theorem B6630821 : Blo 1307972 6630821 := bbase (se 4 (by rfl) ⟨621639, by rfl⟩ : syracuseStep 6630821 = 1243279) (by norm_num)
theorem B2944493 : Blo 1307972 2944493 := bbase (se 3 (by rfl) ⟨552092, by rfl⟩ : syracuseStep 2944493 = 1104185) (by norm_num)
theorem B3313133 : Blo 1307972 3313133 := bbase (se 3 (by rfl) ⟨621212, by rfl⟩ : syracuseStep 3313133 = 1242425) (by norm_num)
theorem B11185685 : Blo 1307972 11185685 := bbase (se 6 (by rfl) ⟨262164, by rfl⟩ : syracuseStep 11185685 = 524329) (by norm_num)
theorem B2944565 : Blo 1307972 2944565 := bbase (se 5 (by rfl) ⟨138026, by rfl⟩ : syracuseStep 2944565 = 276053) (by norm_num)
theorem B2485829 : Blo 1307972 2485829 := bbase (se 4 (by rfl) ⟨233046, by rfl⟩ : syracuseStep 2485829 = 466093) (by norm_num)
theorem B2207317 : Blo 1307972 2207317 := bbase (se 8 (by rfl) ⟨12933, by rfl⟩ : syracuseStep 2207317 = 25867) (by norm_num)
theorem B2944637 : Blo 1307972 2944637 := bbase (se 3 (by rfl) ⟨552119, by rfl⟩ : syracuseStep 2944637 = 1104239) (by norm_num)
theorem B11177621 : Blo 1307972 11177621 := bbase (se 6 (by rfl) ⟨261975, by rfl⟩ : syracuseStep 11177621 = 523951) (by norm_num)
theorem B2207405 : Blo 1307972 2207405 := bbase (se 3 (by rfl) ⟨413888, by rfl⟩ : syracuseStep 2207405 = 827777) (by norm_num)
theorem B3313325 : Blo 1307972 3313325 := bbase (se 3 (by rfl) ⟨621248, by rfl⟩ : syracuseStep 3313325 = 1242497) (by norm_num)
theorem B2944709 : Blo 1307972 2944709 := bbase (se 4 (by rfl) ⟨276066, by rfl⟩ : syracuseStep 2944709 = 552133) (by norm_num)
theorem B2485981 : Blo 1307972 2485981 := bbase (se 3 (by rfl) ⟨466121, by rfl⟩ : syracuseStep 2485981 = 932243) (by norm_num)
theorem B2944781 : Blo 1307972 2944781 := bbase (se 3 (by rfl) ⟨552146, by rfl⟩ : syracuseStep 2944781 = 1104293) (by norm_num)
theorem B7458581 : Blo 1307972 7458581 := bbase (se 6 (by rfl) ⟨174810, by rfl⟩ : syracuseStep 7458581 = 349621) (by norm_num)
theorem B2207533 : Blo 1307972 2207533 := bbase (se 3 (by rfl) ⟨413912, by rfl⟩ : syracuseStep 2207533 = 827825) (by norm_num)
theorem B6623045 : Blo 1307972 6623045 := bbase (se 4 (by rfl) ⟨620910, by rfl⟩ : syracuseStep 6623045 = 1241821) (by norm_num)
theorem B5304149 : Blo 1307972 5304149 := bbase (se 9 (by rfl) ⟨15539, by rfl⟩ : syracuseStep 5304149 = 31079) (by norm_num)
theorem B2944853 : Blo 1307972 2944853 := bbase (se 9 (by rfl) ⟨8627, by rfl⟩ : syracuseStep 2944853 = 17255) (by norm_num)
theorem B4419413 : Blo 1307972 4419413 := bbase (se 9 (by rfl) ⟨12947, by rfl⟩ : syracuseStep 4419413 = 25895) (by norm_num)
theorem B2207621 : Blo 1307972 2207621 := bbase (se 4 (by rfl) ⟨206964, by rfl⟩ : syracuseStep 2207621 = 413929) (by norm_num)
theorem B2944925 : Blo 1307972 2944925 := bbase (se 3 (by rfl) ⟨552173, by rfl⟩ : syracuseStep 2944925 = 1104347) (by norm_num)
theorem B2944997 : Blo 1307972 2944997 := bbase (se 4 (by rfl) ⟨276093, by rfl⟩ : syracuseStep 2944997 = 552187) (by norm_num)
theorem B9441269 : Blo 1307972 9441269 := bbase (se 5 (by rfl) ⟨442559, by rfl⟩ : syracuseStep 9441269 = 885119) (by norm_num)
theorem B1961981 : Blo 1307972 1961981 := bbase (se 3 (by rfl) ⟨367871, by rfl⟩ : syracuseStep 1961981 = 735743) (by norm_num)
theorem B2207749 : Blo 1307972 2207749 := bbase (se 4 (by rfl) ⟨206976, by rfl⟩ : syracuseStep 2207749 = 413953) (by norm_num)
theorem B3313669 : Blo 1307972 3313669 := bbase (se 4 (by rfl) ⟨310656, by rfl⟩ : syracuseStep 3313669 = 621313) (by norm_num)
theorem B2486285 : Blo 1307972 2486285 := bbase (se 3 (by rfl) ⟨466178, by rfl⟩ : syracuseStep 2486285 = 932357) (by norm_num)
theorem B1962005 : Blo 1307972 1962005 := bbase (se 6 (by rfl) ⟨45984, by rfl⟩ : syracuseStep 1962005 = 91969) (by norm_num)
theorem B4968485 : Blo 1307972 4968485 := bbase (se 4 (by rfl) ⟨465795, by rfl⟩ : syracuseStep 4968485 = 931591) (by norm_num)
theorem B1962029 : Blo 1307972 1962029 := bbase (se 3 (by rfl) ⟨367880, by rfl⟩ : syracuseStep 1962029 = 735761) (by norm_num)
theorem B2945069 : Blo 1307972 2945069 := bbase (se 3 (by rfl) ⟨552200, by rfl⟩ : syracuseStep 2945069 = 1104401) (by norm_num)
theorem B1962053 : Blo 1307972 1962053 := bbase (se 4 (by rfl) ⟨183942, by rfl⟩ : syracuseStep 1962053 = 367885) (by norm_num)
theorem B1863757 : Blo 1307972 1863757 := bbase (se 3 (by rfl) ⟨349454, by rfl⟩ : syracuseStep 1863757 = 698909) (by norm_num)
theorem B1962077 : Blo 1307972 1962077 := bbase (se 3 (by rfl) ⟨367889, by rfl⟩ : syracuseStep 1962077 = 735779) (by norm_num)
theorem B2207837 : Blo 1307972 2207837 := bbase (se 3 (by rfl) ⟨413969, by rfl⟩ : syracuseStep 2207837 = 827939) (by norm_num)
theorem B2797669 : Blo 1307972 2797669 := bbase (se 4 (by rfl) ⟨262281, by rfl⟩ : syracuseStep 2797669 = 524563) (by norm_num)
theorem B1962101 : Blo 1307972 1962101 := bbase (se 5 (by rfl) ⟨91973, by rfl⟩ : syracuseStep 1962101 = 183947) (by norm_num)
theorem B5967989 : Blo 1307972 5967989 := bbase (se 5 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 5967989 = 559499) (by norm_num)
theorem B2945141 : Blo 1307972 2945141 := bbase (se 5 (by rfl) ⟨138053, by rfl⟩ : syracuseStep 2945141 = 276107) (by norm_num)
theorem B3313781 : Blo 1307972 3313781 := bbase (se 5 (by rfl) ⟨155333, by rfl⟩ : syracuseStep 3313781 = 310667) (by norm_num)
theorem B1962125 : Blo 1307972 1962125 := bbase (se 3 (by rfl) ⟨367898, by rfl⟩ : syracuseStep 1962125 = 735797) (by norm_num)
theorem B1962149 : Blo 1307972 1962149 := bbase (se 4 (by rfl) ⟨183951, by rfl⟩ : syracuseStep 1962149 = 367903) (by norm_num)
theorem B1396921 : Blo 1307972 1396921 := bbase (se 2 (by rfl) ⟨523845, by rfl⟩ : syracuseStep 1396921 = 1047691) (by norm_num)
theorem B1962173 : Blo 1307972 1962173 := bbase (se 3 (by rfl) ⟨367907, by rfl⟩ : syracuseStep 1962173 = 735815) (by norm_num)
theorem B2945213 : Blo 1307972 2945213 := bbase (se 3 (by rfl) ⟨552227, by rfl⟩ : syracuseStep 2945213 = 1104455) (by norm_num)
theorem B1962197 : Blo 1307972 1962197 := bbase (se 7 (by rfl) ⟨22994, by rfl⟩ : syracuseStep 1962197 = 45989) (by norm_num)
theorem B2207965 : Blo 1307972 2207965 := bbase (se 3 (by rfl) ⟨413993, by rfl⟩ : syracuseStep 2207965 = 827987) (by norm_num)
theorem B1962221 : Blo 1307972 1962221 := bbase (se 3 (by rfl) ⟨367916, by rfl⟩ : syracuseStep 1962221 = 735833) (by norm_num)
theorem B1962245 : Blo 1307972 1962245 := bbase (se 4 (by rfl) ⟨183960, by rfl⟩ : syracuseStep 1962245 = 367921) (by norm_num)
theorem B2945285 : Blo 1307972 2945285 := bbase (se 4 (by rfl) ⟨276120, by rfl⟩ : syracuseStep 2945285 = 552241) (by norm_num)
theorem B4419845 : Blo 1307972 4419845 := bbase (se 4 (by rfl) ⟨414360, by rfl⟩ : syracuseStep 4419845 = 828721) (by norm_num)
theorem B1962269 : Blo 1307972 1962269 := bbase (se 3 (by rfl) ⟨367925, by rfl⟩ : syracuseStep 1962269 = 735851) (by norm_num)
theorem B1962293 : Blo 1307972 1962293 := bbase (se 5 (by rfl) ⟨91982, by rfl⟩ : syracuseStep 1962293 = 183965) (by norm_num)
theorem B1397045 : Blo 1307972 1397045 := bbase (se 5 (by rfl) ⟨65486, by rfl⟩ : syracuseStep 1397045 = 130973) (by norm_num)
theorem B2208053 : Blo 1307972 2208053 := bbase (se 5 (by rfl) ⟨103502, by rfl⟩ : syracuseStep 2208053 = 207005) (by norm_num)
theorem B3313973 : Blo 1307972 3313973 := bbase (se 5 (by rfl) ⟨155342, by rfl⟩ : syracuseStep 3313973 = 310685) (by norm_num)
theorem B4968773 : Blo 1307972 4968773 := bbase (se 4 (by rfl) ⟨465822, by rfl⟩ : syracuseStep 4968773 = 931645) (by norm_num)
theorem B1962317 : Blo 1307972 1962317 := bbase (se 3 (by rfl) ⟨367934, by rfl⟩ : syracuseStep 1962317 = 735869) (by norm_num)
theorem B2945357 : Blo 1307972 2945357 := bbase (se 3 (by rfl) ⟨552254, by rfl⟩ : syracuseStep 2945357 = 1104509) (by norm_num)
theorem B1962341 : Blo 1307972 1962341 := bbase (se 4 (by rfl) ⟨183969, by rfl⟩ : syracuseStep 1962341 = 367939) (by norm_num)
theorem B1962365 : Blo 1307972 1962365 := bbase (se 3 (by rfl) ⟨367943, by rfl⟩ : syracuseStep 1962365 = 735887) (by norm_num)
theorem B1962389 : Blo 1307972 1962389 := bbase (se 6 (by rfl) ⟨45993, by rfl⟩ : syracuseStep 1962389 = 91987) (by norm_num)
theorem B2945429 : Blo 1307972 2945429 := bbase (se 6 (by rfl) ⟨69033, by rfl⟩ : syracuseStep 2945429 = 138067) (by norm_num)
theorem B1962413 : Blo 1307972 1962413 := bbase (se 3 (by rfl) ⟨367952, by rfl⟩ : syracuseStep 1962413 = 735905) (by norm_num)
theorem B2208181 : Blo 1307972 2208181 := bbase (se 5 (by rfl) ⟨103508, by rfl⟩ : syracuseStep 2208181 = 207017) (by norm_num)
theorem B1962437 : Blo 1307972 1962437 := bbase (se 4 (by rfl) ⟨183978, by rfl⟩ : syracuseStep 1962437 = 367957) (by norm_num)
theorem B1962461 : Blo 1307972 1962461 := bbase (se 3 (by rfl) ⟨367961, by rfl⟩ : syracuseStep 1962461 = 735923) (by norm_num)
theorem B2945501 : Blo 1307972 2945501 := bbase (se 3 (by rfl) ⟨552281, by rfl⟩ : syracuseStep 2945501 = 1104563) (by norm_num)
theorem B1962485 : Blo 1307972 1962485 := bbase (se 5 (by rfl) ⟨91991, by rfl⟩ : syracuseStep 1962485 = 183983) (by norm_num)
theorem B1962509 : Blo 1307972 1962509 := bbase (se 3 (by rfl) ⟨367970, by rfl⟩ : syracuseStep 1962509 = 735941) (by norm_num)
theorem B2208269 : Blo 1307972 2208269 := bbase (se 3 (by rfl) ⟨414050, by rfl⟩ : syracuseStep 2208269 = 828101) (by norm_num)
theorem B1962533 : Blo 1307972 1962533 := bbase (se 4 (by rfl) ⟨183987, by rfl⟩ : syracuseStep 1962533 = 367975) (by norm_num)
theorem B2945573 : Blo 1307972 2945573 := bbase (se 4 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 2945573 = 552295) (by norm_num)
theorem B1397297 : Blo 1307972 1397297 := bbase (se 2 (by rfl) ⟨523986, by rfl⟩ : syracuseStep 1397297 = 1047973) (by norm_num)
theorem B9441845 : Blo 1307972 9441845 := bbase (se 5 (by rfl) ⟨442586, by rfl⟩ : syracuseStep 9441845 = 885173) (by norm_num)
theorem B1962557 : Blo 1307972 1962557 := bbase (se 3 (by rfl) ⟨367979, by rfl⟩ : syracuseStep 1962557 = 735959) (by norm_num)
theorem B1962581 : Blo 1307972 1962581 := bbase (se 8 (by rfl) ⟨11499, by rfl⟩ : syracuseStep 1962581 = 22999) (by norm_num)
theorem B1962605 : Blo 1307972 1962605 := bbase (se 3 (by rfl) ⟨367988, by rfl⟩ : syracuseStep 1962605 = 735977) (by norm_num)
theorem B2945645 : Blo 1307972 2945645 := bbase (se 3 (by rfl) ⟨552308, by rfl⟩ : syracuseStep 2945645 = 1104617) (by norm_num)
theorem B1962629 : Blo 1307972 1962629 := bbase (se 4 (by rfl) ⟨183996, by rfl⟩ : syracuseStep 1962629 = 367993) (by norm_num)
theorem B2208397 : Blo 1307972 2208397 := bbase (se 3 (by rfl) ⟨414074, by rfl⟩ : syracuseStep 2208397 = 828149) (by norm_num)
theorem B3314317 : Blo 1307972 3314317 := bbase (se 3 (by rfl) ⟨621434, by rfl⟩ : syracuseStep 3314317 = 1242869) (by norm_num)
theorem B1962653 : Blo 1307972 1962653 := bbase (se 3 (by rfl) ⟨367997, by rfl⟩ : syracuseStep 1962653 = 735995) (by norm_num)
theorem B3535525 : Blo 1307972 3535525 := bbase (se 4 (by rfl) ⟨331455, by rfl⟩ : syracuseStep 3535525 = 662911) (by norm_num)
theorem B1962677 : Blo 1307972 1962677 := bbase (se 5 (by rfl) ⟨92000, by rfl⟩ : syracuseStep 1962677 = 184001) (by norm_num)
theorem B2945717 : Blo 1307972 2945717 := bbase (se 5 (by rfl) ⟨138080, by rfl⟩ : syracuseStep 2945717 = 276161) (by norm_num)
theorem B4420277 : Blo 1307972 4420277 := bbase (se 5 (by rfl) ⟨207200, by rfl⟩ : syracuseStep 4420277 = 414401) (by norm_num)
theorem B5591749 : Blo 1307972 5591749 := bbase (se 4 (by rfl) ⟨524226, by rfl⟩ : syracuseStep 5591749 = 1048453) (by norm_num)
theorem B1962701 : Blo 1307972 1962701 := bbase (se 3 (by rfl) ⟨368006, by rfl⟩ : syracuseStep 1962701 = 736013) (by norm_num)
theorem B1962725 : Blo 1307972 1962725 := bbase (se 4 (by rfl) ⟨184005, by rfl⟩ : syracuseStep 1962725 = 368011) (by norm_num)
theorem B2208485 : Blo 1307972 2208485 := bbase (se 4 (by rfl) ⟨207045, by rfl⟩ : syracuseStep 2208485 = 414091) (by norm_num)
theorem B1962749 : Blo 1307972 1962749 := bbase (se 3 (by rfl) ⟨368015, by rfl⟩ : syracuseStep 1962749 = 736031) (by norm_num)
theorem B2945789 : Blo 1307972 2945789 := bbase (se 3 (by rfl) ⟨552335, by rfl⟩ : syracuseStep 2945789 = 1104671) (by norm_num)
theorem B3314429 : Blo 1307972 3314429 := bbase (se 3 (by rfl) ⟨621455, by rfl⟩ : syracuseStep 3314429 = 1242911) (by norm_num)
theorem B1962773 : Blo 1307972 1962773 := bbase (se 6 (by rfl) ⟨46002, by rfl⟩ : syracuseStep 1962773 = 92005) (by norm_num)
theorem B1962797 : Blo 1307972 1962797 := bbase (se 3 (by rfl) ⟨368024, by rfl⟩ : syracuseStep 1962797 = 736049) (by norm_num)
theorem B7557941 : Blo 1307972 7557941 := bbase (se 5 (by rfl) ⟨354278, by rfl⟩ : syracuseStep 7557941 = 708557) (by norm_num)
theorem B1962821 : Blo 1307972 1962821 := bbase (se 4 (by rfl) ⟨184014, by rfl⟩ : syracuseStep 1962821 = 368029) (by norm_num)
theorem B2945861 : Blo 1307972 2945861 := bbase (se 4 (by rfl) ⟨276174, by rfl⟩ : syracuseStep 2945861 = 552349) (by norm_num)
theorem B5665621 : Blo 1307972 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B1962845 : Blo 1307972 1962845 := bbase (se 3 (by rfl) ⟨368033, by rfl⟩ : syracuseStep 1962845 = 736067) (by norm_num)
theorem B2208613 : Blo 1307972 2208613 := bbase (se 4 (by rfl) ⟨207057, by rfl⟩ : syracuseStep 2208613 = 414115) (by norm_num)
theorem B1864549 : Blo 1307972 1864549 := bbase (se 4 (by rfl) ⟨174801, by rfl⟩ : syracuseStep 1864549 = 349603) (by norm_num)
theorem B1962869 : Blo 1307972 1962869 := bbase (se 5 (by rfl) ⟨92009, by rfl⟩ : syracuseStep 1962869 = 184019) (by norm_num)
theorem B1962893 : Blo 1307972 1962893 := bbase (se 3 (by rfl) ⟨368042, by rfl⟩ : syracuseStep 1962893 = 736085) (by norm_num)
theorem B2945933 : Blo 1307972 2945933 := bbase (se 3 (by rfl) ⟨552362, by rfl⟩ : syracuseStep 2945933 = 1104725) (by norm_num)
theorem B1962917 : Blo 1307972 1962917 := bbase (se 4 (by rfl) ⟨184023, by rfl⟩ : syracuseStep 1962917 = 368047) (by norm_num)
theorem B1962941 : Blo 1307972 1962941 := bbase (se 3 (by rfl) ⟨368051, by rfl⟩ : syracuseStep 1962941 = 736103) (by norm_num)
theorem B2208701 : Blo 1307972 2208701 := bbase (se 3 (by rfl) ⟨414131, by rfl⟩ : syracuseStep 2208701 = 828263) (by norm_num)
theorem B3314621 : Blo 1307972 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B4191173 : Blo 1307972 4191173 := bbase (se 4 (by rfl) ⟨392922, by rfl⟩ : syracuseStep 4191173 = 785845) (by norm_num)
theorem B1962965 : Blo 1307972 1962965 := bbase (se 7 (by rfl) ⟨23003, by rfl⟩ : syracuseStep 1962965 = 46007) (by norm_num)
theorem B2946005 : Blo 1307972 2946005 := bbase (se 7 (by rfl) ⟨34523, by rfl⟩ : syracuseStep 2946005 = 69047) (by norm_num)
theorem B1455085 : Blo 1307972 1455085 := bbase (se 3 (by rfl) ⟨272828, by rfl⟩ : syracuseStep 1455085 = 545657) (by norm_num)
theorem B1962989 : Blo 1307972 1962989 := bbase (se 3 (by rfl) ⟨368060, by rfl⟩ : syracuseStep 1962989 = 736121) (by norm_num)
theorem B1397741 : Blo 1307972 1397741 := bbase (se 3 (by rfl) ⟨262076, by rfl⟩ : syracuseStep 1397741 = 524153) (by norm_num)
theorem B1471477 : Blo 1307972 1471477 := bbase (se 5 (by rfl) ⟨68975, by rfl⟩ : syracuseStep 1471477 = 137951) (by norm_num)
theorem B1963013 : Blo 1307972 1963013 := bbase (se 4 (by rfl) ⟨184032, by rfl⟩ : syracuseStep 1963013 = 368065) (by norm_num)
theorem B1471513 : Blo 1307972 1471513 := bbase (se 2 (by rfl) ⟨551817, by rfl⟩ : syracuseStep 1471513 = 1103635) (by norm_num)
theorem B1963037 : Blo 1307972 1963037 := bbase (se 3 (by rfl) ⟨368069, by rfl⟩ : syracuseStep 1963037 = 736139) (by norm_num)
theorem B2946077 : Blo 1307972 2946077 := bbase (se 3 (by rfl) ⟨552389, by rfl⟩ : syracuseStep 2946077 = 1104779) (by norm_num)
theorem B2126893 : Blo 1307972 2126893 := bbase (se 3 (by rfl) ⟨398792, by rfl⟩ : syracuseStep 2126893 = 797585) (by norm_num)
theorem B1963061 : Blo 1307972 1963061 := bbase (se 5 (by rfl) ⟨92018, by rfl⟩ : syracuseStep 1963061 = 184037) (by norm_num)
theorem B1471549 : Blo 1307972 1471549 := bbase (se 3 (by rfl) ⟨275915, by rfl⟩ : syracuseStep 1471549 = 551831) (by norm_num)
theorem B2208829 : Blo 1307972 2208829 := bbase (se 3 (by rfl) ⟨414155, by rfl⟩ : syracuseStep 2208829 = 828311) (by norm_num)
theorem B1963085 : Blo 1307972 1963085 := bbase (se 3 (by rfl) ⟨368078, by rfl⟩ : syracuseStep 1963085 = 736157) (by norm_num)
theorem B6624341 : Blo 1307972 6624341 := bbase (se 8 (by rfl) ⟨38814, by rfl⟩ : syracuseStep 6624341 = 77629) (by norm_num)
theorem B9942101 : Blo 1307972 9942101 := bbase (se 8 (by rfl) ⟨58254, by rfl⟩ : syracuseStep 9942101 = 116509) (by norm_num)
theorem B1471585 : Blo 1307972 1471585 := bbase (se 2 (by rfl) ⟨551844, by rfl⟩ : syracuseStep 1471585 = 1103689) (by norm_num)
theorem B1963109 : Blo 1307972 1963109 := bbase (se 4 (by rfl) ⟨184041, by rfl⟩ : syracuseStep 1963109 = 368083) (by norm_num)
theorem B2946149 : Blo 1307972 2946149 := bbase (se 4 (by rfl) ⟨276201, by rfl⟩ : syracuseStep 2946149 = 552403) (by norm_num)
theorem B4420709 : Blo 1307972 4420709 := bbase (se 4 (by rfl) ⟨414441, by rfl⟩ : syracuseStep 4420709 = 828883) (by norm_num)
theorem B1963133 : Blo 1307972 1963133 := bbase (se 3 (by rfl) ⟨368087, by rfl⟩ : syracuseStep 1963133 = 736175) (by norm_num)
theorem B1471621 : Blo 1307972 1471621 := bbase (se 4 (by rfl) ⟨137964, by rfl⟩ : syracuseStep 1471621 = 275929) (by norm_num)
theorem B3536021 : Blo 1307972 3536021 := bbase (se 6 (by rfl) ⟨82875, by rfl⟩ : syracuseStep 3536021 = 165751) (by norm_num)
theorem B1963157 : Blo 1307972 1963157 := bbase (se 6 (by rfl) ⟨46011, by rfl⟩ : syracuseStep 1963157 = 92023) (by norm_num)
theorem B2208917 : Blo 1307972 2208917 := bbase (se 6 (by rfl) ⟨51771, by rfl⟩ : syracuseStep 2208917 = 103543) (by norm_num)
theorem B1471657 : Blo 1307972 1471657 := bbase (se 2 (by rfl) ⟨551871, by rfl⟩ : syracuseStep 1471657 = 1103743) (by norm_num)
theorem B1963181 : Blo 1307972 1963181 := bbase (se 3 (by rfl) ⟨368096, by rfl⟩ : syracuseStep 1963181 = 736193) (by norm_num)
theorem B2946221 : Blo 1307972 2946221 := bbase (se 3 (by rfl) ⟨552416, by rfl⟩ : syracuseStep 2946221 = 1104833) (by norm_num)
theorem B1864885 : Blo 1307972 1864885 := bbase (se 5 (by rfl) ⟨87416, by rfl⟩ : syracuseStep 1864885 = 174833) (by norm_num)
theorem B1963205 : Blo 1307972 1963205 := bbase (se 4 (by rfl) ⟨184050, by rfl⟩ : syracuseStep 1963205 = 368101) (by norm_num)
theorem B1471693 : Blo 1307972 1471693 := bbase (se 3 (by rfl) ⟨275942, by rfl⟩ : syracuseStep 1471693 = 551885) (by norm_num)
theorem B1963229 : Blo 1307972 1963229 := bbase (se 3 (by rfl) ⟨368105, by rfl⟩ : syracuseStep 1963229 = 736211) (by norm_num)
theorem B1397989 : Blo 1307972 1397989 := bbase (se 4 (by rfl) ⟨131061, by rfl⟩ : syracuseStep 1397989 = 262123) (by norm_num)
theorem B1471729 : Blo 1307972 1471729 := bbase (se 2 (by rfl) ⟨551898, by rfl⟩ : syracuseStep 1471729 = 1103797) (by norm_num)
theorem B1963253 : Blo 1307972 1963253 := bbase (se 5 (by rfl) ⟨92027, by rfl⟩ : syracuseStep 1963253 = 184055) (by norm_num)
theorem B2946293 : Blo 1307972 2946293 := bbase (se 5 (by rfl) ⟨138107, by rfl⟩ : syracuseStep 2946293 = 276215) (by norm_num)
theorem B1963277 : Blo 1307972 1963277 := bbase (se 3 (by rfl) ⟨368114, by rfl⟩ : syracuseStep 1963277 = 736229) (by norm_num)
theorem B1471765 : Blo 1307972 1471765 := bbase (se 6 (by rfl) ⟨34494, by rfl⟩ : syracuseStep 1471765 = 68989) (by norm_num)
theorem B2209045 : Blo 1307972 2209045 := bbase (se 6 (by rfl) ⟨51774, by rfl⟩ : syracuseStep 2209045 = 103549) (by norm_num)
theorem B3314965 : Blo 1307972 3314965 := bbase (se 6 (by rfl) ⟨77694, by rfl⟩ : syracuseStep 3314965 = 155389) (by norm_num)
theorem B1963301 : Blo 1307972 1963301 := bbase (se 4 (by rfl) ⟨184059, by rfl⟩ : syracuseStep 1963301 = 368119) (by norm_num)
theorem B1471801 : Blo 1307972 1471801 := bbase (se 2 (by rfl) ⟨551925, by rfl⟩ : syracuseStep 1471801 = 1103851) (by norm_num)
theorem B1963325 : Blo 1307972 1963325 := bbase (se 3 (by rfl) ⟨368123, by rfl⟩ : syracuseStep 1963325 = 736247) (by norm_num)
theorem B2946365 : Blo 1307972 2946365 := bbase (se 3 (by rfl) ⟨552443, by rfl⟩ : syracuseStep 2946365 = 1104887) (by norm_num)
theorem B1963349 : Blo 1307972 1963349 := bbase (se 13 (by rfl) ⟨359, by rfl⟩ : syracuseStep 1963349 = 719) (by norm_num)
theorem B1471837 : Blo 1307972 1471837 := bbase (se 3 (by rfl) ⟨275969, by rfl⟩ : syracuseStep 1471837 = 551939) (by norm_num)
theorem B1963373 : Blo 1307972 1963373 := bbase (se 3 (by rfl) ⟨368132, by rfl⟩ : syracuseStep 1963373 = 736265) (by norm_num)
theorem B2209133 : Blo 1307972 2209133 := bbase (se 3 (by rfl) ⟨414212, by rfl⟩ : syracuseStep 2209133 = 828425) (by norm_num)
theorem B1471873 : Blo 1307972 1471873 := bbase (se 2 (by rfl) ⟨551952, by rfl⟩ : syracuseStep 1471873 = 1103905) (by norm_num)
theorem B1963397 : Blo 1307972 1963397 := bbase (se 4 (by rfl) ⟨184068, by rfl⟩ : syracuseStep 1963397 = 368137) (by norm_num)
theorem B3143053 : Blo 1307972 3143053 := bbase (se 3 (by rfl) ⟨589322, by rfl⟩ : syracuseStep 3143053 = 1178645) (by norm_num)
theorem B2946437 : Blo 1307972 2946437 := bbase (se 4 (by rfl) ⟨276228, by rfl⟩ : syracuseStep 2946437 = 552457) (by norm_num)
theorem B1865101 : Blo 1307972 1865101 := bbase (se 3 (by rfl) ⟨349706, by rfl⟩ : syracuseStep 1865101 = 699413) (by norm_num)
theorem B1963421 : Blo 1307972 1963421 := bbase (se 3 (by rfl) ⟨368141, by rfl⟩ : syracuseStep 1963421 = 736283) (by norm_num)
theorem B1471909 : Blo 1307972 1471909 := bbase (se 4 (by rfl) ⟨137991, by rfl⟩ : syracuseStep 1471909 = 275983) (by norm_num)
theorem B1963445 : Blo 1307972 1963445 := bbase (se 5 (by rfl) ⟨92036, by rfl⟩ : syracuseStep 1963445 = 184073) (by norm_num)
theorem B1471945 : Blo 1307972 1471945 := bbase (se 2 (by rfl) ⟨551979, by rfl⟩ : syracuseStep 1471945 = 1103959) (by norm_num)
theorem B1963469 : Blo 1307972 1963469 := bbase (se 3 (by rfl) ⟨368150, by rfl⟩ : syracuseStep 1963469 = 736301) (by norm_num)
theorem B2946509 : Blo 1307972 2946509 := bbase (se 3 (by rfl) ⟨552470, by rfl⟩ : syracuseStep 2946509 = 1104941) (by norm_num)
theorem B4969957 : Blo 1307972 4969957 := bbase (se 4 (by rfl) ⟨465933, by rfl⟩ : syracuseStep 4969957 = 931867) (by norm_num)
theorem B1963493 : Blo 1307972 1963493 := bbase (se 4 (by rfl) ⟨184077, by rfl⟩ : syracuseStep 1963493 = 368155) (by norm_num)
theorem B1471981 : Blo 1307972 1471981 := bbase (se 3 (by rfl) ⟨275996, by rfl⟩ : syracuseStep 1471981 = 551993) (by norm_num)
theorem B2209261 : Blo 1307972 2209261 := bbase (se 3 (by rfl) ⟨414236, by rfl⟩ : syracuseStep 2209261 = 828473) (by norm_num)
theorem B9934325 : Blo 1307972 9934325 := bbase (se 5 (by rfl) ⟨465671, by rfl⟩ : syracuseStep 9934325 = 931343) (by norm_num)
theorem B8386037 : Blo 1307972 8386037 := bbase (se 5 (by rfl) ⟨393095, by rfl⟩ : syracuseStep 8386037 = 786191) (by norm_num)
theorem B1963517 : Blo 1307972 1963517 := bbase (se 3 (by rfl) ⟨368159, by rfl⟩ : syracuseStep 1963517 = 736319) (by norm_num)
theorem B1472017 : Blo 1307972 1472017 := bbase (se 2 (by rfl) ⟨552006, by rfl⟩ : syracuseStep 1472017 = 1104013) (by norm_num)
theorem B1963541 : Blo 1307972 1963541 := bbase (se 6 (by rfl) ⟨46020, by rfl⟩ : syracuseStep 1963541 = 92041) (by norm_num)
theorem B2946581 : Blo 1307972 2946581 := bbase (se 6 (by rfl) ⟨69060, by rfl⟩ : syracuseStep 2946581 = 138121) (by norm_num)
theorem B4421141 : Blo 1307972 4421141 := bbase (se 6 (by rfl) ⟨103620, by rfl⟩ : syracuseStep 4421141 = 207241) (by norm_num)
theorem B1963565 : Blo 1307972 1963565 := bbase (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) (by norm_num)
theorem B1472053 : Blo 1307972 1472053 := bbase (se 5 (by rfl) ⟨69002, by rfl⟩ : syracuseStep 1472053 = 138005) (by norm_num)
theorem B1963589 : Blo 1307972 1963589 := bbase (se 4 (by rfl) ⟨184086, by rfl⟩ : syracuseStep 1963589 = 368173) (by norm_num)
theorem B2209349 : Blo 1307972 2209349 := bbase (se 4 (by rfl) ⟨207126, by rfl⟩ : syracuseStep 2209349 = 414253) (by norm_num)
theorem B1513033 : Blo 1307972 1513033 := bbase (se 2 (by rfl) ⟨567387, by rfl⟩ : syracuseStep 1513033 = 1134775) (by norm_num)
theorem B3315269 : Blo 1307972 3315269 := bbase (se 4 (by rfl) ⟨310806, by rfl⟩ : syracuseStep 3315269 = 621613) (by norm_num)
theorem B1472089 : Blo 1307972 1472089 := bbase (se 2 (by rfl) ⟨552033, by rfl⟩ : syracuseStep 1472089 = 1104067) (by norm_num)
theorem B1963613 : Blo 1307972 1963613 := bbase (se 3 (by rfl) ⟨368177, by rfl⟩ : syracuseStep 1963613 = 736355) (by norm_num)
theorem B2946653 : Blo 1307972 2946653 := bbase (se 3 (by rfl) ⟨552497, by rfl⟩ : syracuseStep 2946653 = 1104995) (by norm_num)
theorem B1963637 : Blo 1307972 1963637 := bbase (se 5 (by rfl) ⟨92045, by rfl⟩ : syracuseStep 1963637 = 184091) (by norm_num)
theorem B1472125 : Blo 1307972 1472125 := bbase (se 3 (by rfl) ⟨276023, by rfl⟩ : syracuseStep 1472125 = 552047) (by norm_num)
theorem B3356293 : Blo 1307972 3356293 := bbase (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) (by norm_num)
theorem B1963661 : Blo 1307972 1963661 := bbase (se 3 (by rfl) ⟨368186, by rfl⟩ : syracuseStep 1963661 = 736373) (by norm_num)
theorem B1472161 : Blo 1307972 1472161 := bbase (se 2 (by rfl) ⟨552060, by rfl⟩ : syracuseStep 1472161 = 1104121) (by norm_num)
theorem B1398433 : Blo 1307972 1398433 := bbase (se 2 (by rfl) ⟨524412, by rfl⟩ : syracuseStep 1398433 = 1048825) (by norm_num)
theorem B1963685 : Blo 1307972 1963685 := bbase (se 4 (by rfl) ⟨184095, by rfl⟩ : syracuseStep 1963685 = 368191) (by norm_num)
theorem B2946725 : Blo 1307972 2946725 := bbase (se 4 (by rfl) ⟨276255, by rfl⟩ : syracuseStep 2946725 = 552511) (by norm_num)
theorem B2651821 : Blo 1307972 2651821 := bbase (se 3 (by rfl) ⟨497216, by rfl⟩ : syracuseStep 2651821 = 994433) (by norm_num)
theorem B1963709 : Blo 1307972 1963709 := bbase (se 3 (by rfl) ⟨368195, by rfl⟩ : syracuseStep 1963709 = 736391) (by norm_num)
theorem B2422469 : Blo 1307972 2422469 := bbase (se 4 (by rfl) ⟨227106, by rfl⟩ : syracuseStep 2422469 = 454213) (by norm_num)
theorem B1472197 : Blo 1307972 1472197 := bbase (se 4 (by rfl) ⟨138018, by rfl⟩ : syracuseStep 1472197 = 276037) (by norm_num)
theorem B2209477 : Blo 1307972 2209477 := bbase (se 4 (by rfl) ⟨207138, by rfl⟩ : syracuseStep 2209477 = 414277) (by norm_num)
theorem B1963733 : Blo 1307972 1963733 := bbase (se 7 (by rfl) ⟨23012, by rfl⟩ : syracuseStep 1963733 = 46025) (by norm_num)
theorem B1398493 : Blo 1307972 1398493 := bbase (se 3 (by rfl) ⟨262217, by rfl⟩ : syracuseStep 1398493 = 524435) (by norm_num)
theorem B1472233 : Blo 1307972 1472233 := bbase (se 2 (by rfl) ⟨552087, by rfl⟩ : syracuseStep 1472233 = 1104175) (by norm_num)
theorem B1963757 : Blo 1307972 1963757 := bbase (se 3 (by rfl) ⟨368204, by rfl⟩ : syracuseStep 1963757 = 736409) (by norm_num)
theorem B2946797 : Blo 1307972 2946797 := bbase (se 3 (by rfl) ⟨552524, by rfl⟩ : syracuseStep 2946797 = 1105049) (by norm_num)
theorem B1963781 : Blo 1307972 1963781 := bbase (se 4 (by rfl) ⟨184104, by rfl⟩ : syracuseStep 1963781 = 368209) (by norm_num)
theorem B1472269 : Blo 1307972 1472269 := bbase (se 3 (by rfl) ⟨276050, by rfl⟩ : syracuseStep 1472269 = 552101) (by norm_num)
theorem B4970261 : Blo 1307972 4970261 := bbase (se 6 (by rfl) ⟨116490, by rfl⟩ : syracuseStep 4970261 = 232981) (by norm_num)
theorem B1963805 : Blo 1307972 1963805 := bbase (se 3 (by rfl) ⟨368213, by rfl⟩ : syracuseStep 1963805 = 736427) (by norm_num)
theorem B2209565 : Blo 1307972 2209565 := bbase (se 3 (by rfl) ⟨414293, by rfl⟩ : syracuseStep 2209565 = 828587) (by norm_num)
theorem B1472305 : Blo 1307972 1472305 := bbase (se 2 (by rfl) ⟨552114, by rfl⟩ : syracuseStep 1472305 = 1104229) (by norm_num)
theorem B1963829 : Blo 1307972 1963829 := bbase (se 5 (by rfl) ⟨92054, by rfl⟩ : syracuseStep 1963829 = 184109) (by norm_num)
theorem B2946869 : Blo 1307972 2946869 := bbase (se 5 (by rfl) ⟨138134, by rfl⟩ : syracuseStep 2946869 = 276269) (by norm_num)
theorem B4192069 : Blo 1307972 4192069 := bbase (se 4 (by rfl) ⟨393006, by rfl⟩ : syracuseStep 4192069 = 786013) (by norm_num)
theorem B1963853 : Blo 1307972 1963853 := bbase (se 3 (by rfl) ⟨368222, by rfl⟩ : syracuseStep 1963853 = 736445) (by norm_num)
theorem B1472341 : Blo 1307972 1472341 := bbase (se 9 (by rfl) ⟨4313, by rfl⟩ : syracuseStep 1472341 = 8627) (by norm_num)
theorem B1963877 : Blo 1307972 1963877 := bbase (se 4 (by rfl) ⟨184113, by rfl⟩ : syracuseStep 1963877 = 368227) (by norm_num)
theorem B1472377 : Blo 1307972 1472377 := bbase (se 2 (by rfl) ⟨552141, by rfl⟩ : syracuseStep 1472377 = 1104283) (by norm_num)
theorem B2357117 : Blo 1307972 2357117 := bbase (se 3 (by rfl) ⟨441959, by rfl⟩ : syracuseStep 2357117 = 883919) (by norm_num)
theorem B1963901 : Blo 1307972 1963901 := bbase (se 3 (by rfl) ⟨368231, by rfl⟩ : syracuseStep 1963901 = 736463) (by norm_num)
theorem B2946941 : Blo 1307972 2946941 := bbase (se 3 (by rfl) ⟨552551, by rfl⟩ : syracuseStep 2946941 = 1105103) (by norm_num)
theorem B3536789 : Blo 1307972 3536789 := bbase (se 6 (by rfl) ⟨82893, by rfl⟩ : syracuseStep 3536789 = 165787) (by norm_num)
theorem B1963925 : Blo 1307972 1963925 := bbase (se 6 (by rfl) ⟨46029, by rfl⟩ : syracuseStep 1963925 = 92059) (by norm_num)
theorem B1472413 : Blo 1307972 1472413 := bbase (se 3 (by rfl) ⟨276077, by rfl⟩ : syracuseStep 1472413 = 552155) (by norm_num)
theorem B2209693 : Blo 1307972 2209693 := bbase (se 3 (by rfl) ⟨414317, by rfl⟩ : syracuseStep 2209693 = 828635) (by norm_num)
theorem B3315613 : Blo 1307972 3315613 := bbase (se 3 (by rfl) ⟨621677, by rfl⟩ : syracuseStep 3315613 = 1243355) (by norm_num)
theorem B1963949 : Blo 1307972 1963949 := bbase (se 3 (by rfl) ⟨368240, by rfl⟩ : syracuseStep 1963949 = 736481) (by norm_num)
theorem B1472449 : Blo 1307972 1472449 := bbase (se 2 (by rfl) ⟨552168, by rfl⟩ : syracuseStep 1472449 = 1104337) (by norm_num)
theorem B1963973 : Blo 1307972 1963973 := bbase (se 4 (by rfl) ⟨184122, by rfl⟩ : syracuseStep 1963973 = 368245) (by norm_num)
theorem B2947013 : Blo 1307972 2947013 := bbase (se 4 (by rfl) ⟨276282, by rfl⟩ : syracuseStep 2947013 = 552565) (by norm_num)
theorem B1963997 : Blo 1307972 1963997 := bbase (se 3 (by rfl) ⟨368249, by rfl⟩ : syracuseStep 1963997 = 736499) (by norm_num)
theorem B1472485 : Blo 1307972 1472485 := bbase (se 4 (by rfl) ⟨138045, by rfl⟩ : syracuseStep 1472485 = 276091) (by norm_num)
theorem B1964021 : Blo 1307972 1964021 := bbase (se 5 (by rfl) ⟨92063, by rfl⟩ : syracuseStep 1964021 = 184127) (by norm_num)
theorem B2209781 : Blo 1307972 2209781 := bbase (se 5 (by rfl) ⟨103583, by rfl⟩ : syracuseStep 2209781 = 207167) (by norm_num)
theorem B1472521 : Blo 1307972 1472521 := bbase (se 2 (by rfl) ⟨552195, by rfl⟩ : syracuseStep 1472521 = 1104391) (by norm_num)
theorem B1964045 : Blo 1307972 1964045 := bbase (se 3 (by rfl) ⟨368258, by rfl⟩ : syracuseStep 1964045 = 736517) (by norm_num)
theorem B2947085 : Blo 1307972 2947085 := bbase (se 3 (by rfl) ⟨552578, by rfl⟩ : syracuseStep 2947085 = 1105157) (by norm_num)
theorem B3315725 : Blo 1307972 3315725 := bbase (se 3 (by rfl) ⟨621698, by rfl⟩ : syracuseStep 3315725 = 1243397) (by norm_num)
theorem B1398809 : Blo 1307972 1398809 := bbase (se 2 (by rfl) ⟨524553, by rfl⟩ : syracuseStep 1398809 = 1049107) (by norm_num)
theorem B1964069 : Blo 1307972 1964069 := bbase (se 4 (by rfl) ⟨184131, by rfl⟩ : syracuseStep 1964069 = 368263) (by norm_num)
theorem B1472557 : Blo 1307972 1472557 := bbase (se 3 (by rfl) ⟨276104, by rfl⟩ : syracuseStep 1472557 = 552209) (by norm_num)
theorem B1964093 : Blo 1307972 1964093 := bbase (se 3 (by rfl) ⟨368267, by rfl⟩ : syracuseStep 1964093 = 736535) (by norm_num)
theorem B1472593 : Blo 1307972 1472593 := bbase (se 2 (by rfl) ⟨552222, by rfl⟩ : syracuseStep 1472593 = 1104445) (by norm_num)
theorem B1964117 : Blo 1307972 1964117 := bbase (se 8 (by rfl) ⟨11508, by rfl⟩ : syracuseStep 1964117 = 23017) (by norm_num)
theorem B2947157 : Blo 1307972 2947157 := bbase (se 8 (by rfl) ⟨17268, by rfl⟩ : syracuseStep 2947157 = 34537) (by norm_num)
theorem B1964141 : Blo 1307972 1964141 := bbase (se 3 (by rfl) ⟨368276, by rfl⟩ : syracuseStep 1964141 = 736553) (by norm_num)
theorem B1472629 : Blo 1307972 1472629 := bbase (se 5 (by rfl) ⟨69029, by rfl⟩ : syracuseStep 1472629 = 138059) (by norm_num)
theorem B2209909 : Blo 1307972 2209909 := bbase (se 5 (by rfl) ⟨103589, by rfl⟩ : syracuseStep 2209909 = 207179) (by norm_num)
theorem B1964165 : Blo 1307972 1964165 := bbase (se 4 (by rfl) ⟨184140, by rfl⟩ : syracuseStep 1964165 = 368281) (by norm_num)
theorem B1472665 : Blo 1307972 1472665 := bbase (se 2 (by rfl) ⟨552249, by rfl⟩ : syracuseStep 1472665 = 1104499) (by norm_num)
theorem B1964189 : Blo 1307972 1964189 := bbase (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) (by norm_num)
theorem B2947229 : Blo 1307972 2947229 := bbase (se 3 (by rfl) ⟨552605, by rfl⟩ : syracuseStep 2947229 = 1105211) (by norm_num)
theorem B1964213 : Blo 1307972 1964213 := bbase (se 5 (by rfl) ⟨92072, by rfl⟩ : syracuseStep 1964213 = 184145) (by norm_num)
theorem B1472701 : Blo 1307972 1472701 := bbase (se 3 (by rfl) ⟨276131, by rfl⟩ : syracuseStep 1472701 = 552263) (by norm_num)
theorem B3725509 : Blo 1307972 3725509 := bbase (se 4 (by rfl) ⟨349266, by rfl⟩ : syracuseStep 3725509 = 698533) (by norm_num)
theorem B1964237 : Blo 1307972 1964237 := bbase (se 3 (by rfl) ⟨368294, by rfl⟩ : syracuseStep 1964237 = 736589) (by norm_num)
theorem B2209997 : Blo 1307972 2209997 := bbase (se 3 (by rfl) ⟨414374, by rfl⟩ : syracuseStep 2209997 = 828749) (by norm_num)
theorem B4192469 : Blo 1307972 4192469 := bbase (se 7 (by rfl) ⟨49130, by rfl⟩ : syracuseStep 4192469 = 98261) (by norm_num)
theorem B1472737 : Blo 1307972 1472737 := bbase (se 2 (by rfl) ⟨552276, by rfl⟩ : syracuseStep 1472737 = 1104553) (by norm_num)
theorem B1964261 : Blo 1307972 1964261 := bbase (se 4 (by rfl) ⟨184149, by rfl⟩ : syracuseStep 1964261 = 368299) (by norm_num)
theorem B2947301 : Blo 1307972 2947301 := bbase (se 4 (by rfl) ⟨276309, by rfl⟩ : syracuseStep 2947301 = 552619) (by norm_num)
theorem B1964285 : Blo 1307972 1964285 := bbase (se 3 (by rfl) ⟨368303, by rfl⟩ : syracuseStep 1964285 = 736607) (by norm_num)
theorem B1472773 : Blo 1307972 1472773 := bbase (se 4 (by rfl) ⟨138072, by rfl⟩ : syracuseStep 1472773 = 276145) (by norm_num)
theorem B1964309 : Blo 1307972 1964309 := bbase (se 6 (by rfl) ⟨46038, by rfl⟩ : syracuseStep 1964309 = 92077) (by norm_num)
theorem B1472809 : Blo 1307972 1472809 := bbase (se 2 (by rfl) ⟨552303, by rfl⟩ : syracuseStep 1472809 = 1104607) (by norm_num)
theorem B1964333 : Blo 1307972 1964333 := bbase (se 3 (by rfl) ⟨368312, by rfl⟩ : syracuseStep 1964333 = 736625) (by norm_num)
theorem B2947373 : Blo 1307972 2947373 := bbase (se 3 (by rfl) ⟨552632, by rfl⟩ : syracuseStep 2947373 = 1105265) (by norm_num)
theorem B12572981 : Blo 1307972 12572981 := bbase (se 5 (by rfl) ⟨589358, by rfl⟩ : syracuseStep 12572981 = 1178717) (by norm_num)
theorem B1964357 : Blo 1307972 1964357 := bbase (se 4 (by rfl) ⟨184158, by rfl⟩ : syracuseStep 1964357 = 368317) (by norm_num)
theorem B1472845 : Blo 1307972 1472845 := bbase (se 3 (by rfl) ⟨276158, by rfl⟩ : syracuseStep 1472845 = 552317) (by norm_num)
theorem B2210125 : Blo 1307972 2210125 := bbase (se 3 (by rfl) ⟨414398, by rfl⟩ : syracuseStep 2210125 = 828797) (by norm_num)
theorem B1964381 : Blo 1307972 1964381 := bbase (se 3 (by rfl) ⟨368321, by rfl⟩ : syracuseStep 1964381 = 736643) (by norm_num)
theorem B3725669 : Blo 1307972 3725669 := bbase (se 4 (by rfl) ⟨349281, by rfl⟩ : syracuseStep 3725669 = 698563) (by norm_num)
theorem B6625637 : Blo 1307972 6625637 := bbase (se 4 (by rfl) ⟨621153, by rfl⟩ : syracuseStep 6625637 = 1242307) (by norm_num)
theorem B1472881 : Blo 1307972 1472881 := bbase (se 2 (by rfl) ⟨552330, by rfl⟩ : syracuseStep 1472881 = 1104661) (by norm_num)
theorem B1964405 : Blo 1307972 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B1964429 : Blo 1307972 1964429 := bbase (se 3 (by rfl) ⟨368330, by rfl⟩ : syracuseStep 1964429 = 736661) (by norm_num)
theorem B1472917 : Blo 1307972 1472917 := bbase (se 6 (by rfl) ⟨34521, by rfl⟩ : syracuseStep 1472917 = 69043) (by norm_num)
theorem B1964453 : Blo 1307972 1964453 := bbase (se 4 (by rfl) ⟨184167, by rfl⟩ : syracuseStep 1964453 = 368335) (by norm_num)
theorem B2210213 : Blo 1307972 2210213 := bbase (se 4 (by rfl) ⟨207207, by rfl⟩ : syracuseStep 2210213 = 414415) (by norm_num)
theorem B1472953 : Blo 1307972 1472953 := bbase (se 2 (by rfl) ⟨552357, by rfl⟩ : syracuseStep 1472953 = 1104715) (by norm_num)
theorem B1964477 : Blo 1307972 1964477 := bbase (se 3 (by rfl) ⟨368339, by rfl⟩ : syracuseStep 1964477 = 736679) (by norm_num)
theorem B1964501 : Blo 1307972 1964501 := bbase (se 7 (by rfl) ⟨23021, by rfl⟩ : syracuseStep 1964501 = 46043) (by norm_num)
theorem B1472989 : Blo 1307972 1472989 := bbase (se 3 (by rfl) ⟨276185, by rfl⟩ : syracuseStep 1472989 = 552371) (by norm_num)
theorem B1964525 : Blo 1307972 1964525 := bbase (se 3 (by rfl) ⟨368348, by rfl⟩ : syracuseStep 1964525 = 736697) (by norm_num)
theorem B1473025 : Blo 1307972 1473025 := bbase (se 2 (by rfl) ⟨552384, by rfl⟩ : syracuseStep 1473025 = 1104769) (by norm_num)
theorem B1964549 : Blo 1307972 1964549 := bbase (se 4 (by rfl) ⟨184176, by rfl⟩ : syracuseStep 1964549 = 368353) (by norm_num)
theorem B7453205 : Blo 1307972 7453205 := bbase (se 6 (by rfl) ⟨174684, by rfl⟩ : syracuseStep 7453205 = 349369) (by norm_num)
theorem B1964573 : Blo 1307972 1964573 := bbase (se 3 (by rfl) ⟨368357, by rfl⟩ : syracuseStep 1964573 = 736715) (by norm_num)
theorem B1915429 : Blo 1307972 1915429 := bbase (se 4 (by rfl) ⟨179571, by rfl⟩ : syracuseStep 1915429 = 359143) (by norm_num)
theorem B1473061 : Blo 1307972 1473061 := bbase (se 4 (by rfl) ⟨138099, by rfl⟩ : syracuseStep 1473061 = 276199) (by norm_num)
theorem B2210341 : Blo 1307972 2210341 := bbase (se 4 (by rfl) ⟨207219, by rfl⟩ : syracuseStep 2210341 = 414439) (by norm_num)
theorem B1964597 : Blo 1307972 1964597 := bbase (se 5 (by rfl) ⟨92090, by rfl⟩ : syracuseStep 1964597 = 184181) (by norm_num)
theorem B1473097 : Blo 1307972 1473097 := bbase (se 2 (by rfl) ⟨552411, by rfl⟩ : syracuseStep 1473097 = 1104823) (by norm_num)
theorem B1964621 : Blo 1307972 1964621 := bbase (se 3 (by rfl) ⟨368366, by rfl⟩ : syracuseStep 1964621 = 736733) (by norm_num)
theorem B3725909 : Blo 1307972 3725909 := bbase (se 8 (by rfl) ⟨21831, by rfl⟩ : syracuseStep 3725909 = 43663) (by norm_num)
theorem B1964645 : Blo 1307972 1964645 := bbase (se 4 (by rfl) ⟨184185, by rfl⟩ : syracuseStep 1964645 = 368371) (by norm_num)
theorem B1473133 : Blo 1307972 1473133 := bbase (se 3 (by rfl) ⟨276212, by rfl⟩ : syracuseStep 1473133 = 552425) (by norm_num)
theorem B1964669 : Blo 1307972 1964669 := bbase (se 3 (by rfl) ⟨368375, by rfl⟩ : syracuseStep 1964669 = 736751) (by norm_num)
theorem B2210429 : Blo 1307972 2210429 := bbase (se 3 (by rfl) ⟨414455, by rfl⟩ : syracuseStep 2210429 = 828911) (by norm_num)
theorem B1473169 : Blo 1307972 1473169 := bbase (se 2 (by rfl) ⟨552438, by rfl⟩ : syracuseStep 1473169 = 1104877) (by norm_num)
theorem B1964693 : Blo 1307972 1964693 := bbase (se 6 (by rfl) ⟨46047, by rfl⟩ : syracuseStep 1964693 = 92095) (by norm_num)
theorem B1964717 : Blo 1307972 1964717 := bbase (se 3 (by rfl) ⟨368384, by rfl⟩ : syracuseStep 1964717 = 736769) (by norm_num)
theorem B1473205 : Blo 1307972 1473205 := bbase (se 5 (by rfl) ⟨69056, by rfl⟩ : syracuseStep 1473205 = 138113) (by norm_num)
theorem B1964741 : Blo 1307972 1964741 := bbase (se 4 (by rfl) ⟨184194, by rfl⟩ : syracuseStep 1964741 = 368389) (by norm_num)
theorem B1473241 : Blo 1307972 1473241 := bbase (se 2 (by rfl) ⟨552465, by rfl⟩ : syracuseStep 1473241 = 1104931) (by norm_num)
theorem B1964765 : Blo 1307972 1964765 := bbase (se 3 (by rfl) ⟨368393, by rfl⟩ : syracuseStep 1964765 = 736787) (by norm_num)
theorem B1989365 : Blo 1307972 1989365 := bbase (se 5 (by rfl) ⟨93251, by rfl⟩ : syracuseStep 1989365 = 186503) (by norm_num)
theorem B3144437 : Blo 1307972 3144437 := bbase (se 5 (by rfl) ⟨147395, by rfl⟩ : syracuseStep 3144437 = 294791) (by norm_num)
theorem B1964789 : Blo 1307972 1964789 := bbase (se 5 (by rfl) ⟨92099, by rfl⟩ : syracuseStep 1964789 = 184199) (by norm_num)
theorem B2652925 : Blo 1307972 2652925 := bbase (se 3 (by rfl) ⟨497423, by rfl⟩ : syracuseStep 2652925 = 994847) (by norm_num)
theorem B1473277 : Blo 1307972 1473277 := bbase (se 3 (by rfl) ⟨276239, by rfl⟩ : syracuseStep 1473277 = 552479) (by norm_num)
theorem B2210557 : Blo 1307972 2210557 := bbase (se 3 (by rfl) ⟨414479, by rfl⟩ : syracuseStep 2210557 = 828959) (by norm_num)
theorem B1964813 : Blo 1307972 1964813 := bbase (se 3 (by rfl) ⟨368402, by rfl⟩ : syracuseStep 1964813 = 736805) (by norm_num)
theorem B3726101 : Blo 1307972 3726101 := bbase (se 6 (by rfl) ⟨87330, by rfl⟩ : syracuseStep 3726101 = 174661) (by norm_num)
theorem B1473313 : Blo 1307972 1473313 := bbase (se 2 (by rfl) ⟨552492, by rfl⟩ : syracuseStep 1473313 = 1104985) (by norm_num)
theorem B4717349 : Blo 1307972 4717349 := bbase (se 4 (by rfl) ⟨442251, by rfl⟩ : syracuseStep 4717349 = 884503) (by norm_num)
theorem B1964837 : Blo 1307972 1964837 := bbase (se 4 (by rfl) ⟨184203, by rfl⟩ : syracuseStep 1964837 = 368407) (by norm_num)
theorem B1964861 : Blo 1307972 1964861 := bbase (se 3 (by rfl) ⟨368411, by rfl⟩ : syracuseStep 1964861 = 736823) (by norm_num)
theorem B1473349 : Blo 1307972 1473349 := bbase (se 4 (by rfl) ⟨138126, by rfl⟩ : syracuseStep 1473349 = 276253) (by norm_num)
theorem B1964885 : Blo 1307972 1964885 := bbase (se 9 (by rfl) ⟨5756, by rfl⟩ : syracuseStep 1964885 = 11513) (by norm_num)
theorem B1473385 : Blo 1307972 1473385 := bbase (se 2 (by rfl) ⟨552519, by rfl⟩ : syracuseStep 1473385 = 1105039) (by norm_num)
theorem B1964909 : Blo 1307972 1964909 := bbase (se 3 (by rfl) ⟨368420, by rfl⟩ : syracuseStep 1964909 = 736841) (by norm_num)
theorem B1964933 : Blo 1307972 1964933 := bbase (se 4 (by rfl) ⟨184212, by rfl⟩ : syracuseStep 1964933 = 368425) (by norm_num)
theorem B1473421 : Blo 1307972 1473421 := bbase (se 3 (by rfl) ⟨276266, by rfl⟩ : syracuseStep 1473421 = 552533) (by norm_num)
theorem B1964957 : Blo 1307972 1964957 := bbase (se 3 (by rfl) ⟨368429, by rfl⟩ : syracuseStep 1964957 = 736859) (by norm_num)
theorem B1473457 : Blo 1307972 1473457 := bbase (se 2 (by rfl) ⟨552546, by rfl⟩ : syracuseStep 1473457 = 1105093) (by norm_num)
theorem B3144629 : Blo 1307972 3144629 := bbase (se 5 (by rfl) ⟨147404, by rfl⟩ : syracuseStep 3144629 = 294809) (by norm_num)
theorem B1473493 : Blo 1307972 1473493 := bbase (se 7 (by rfl) ⟨17267, by rfl⟩ : syracuseStep 1473493 = 34535) (by norm_num)
theorem B1473529 : Blo 1307972 1473529 := bbase (se 2 (by rfl) ⟨552573, by rfl⟩ : syracuseStep 1473529 = 1105147) (by norm_num)
theorem B1473565 : Blo 1307972 1473565 := bbase (se 3 (by rfl) ⟨276293, by rfl⟩ : syracuseStep 1473565 = 552587) (by norm_num)
theorem B2096189 : Blo 1307972 2096189 := bbase (se 3 (by rfl) ⟨393035, by rfl⟩ : syracuseStep 2096189 = 786071) (by norm_num)
theorem B1473601 : Blo 1307972 1473601 := bbase (se 2 (by rfl) ⟨552600, by rfl⟩ : syracuseStep 1473601 = 1105201) (by norm_num)
theorem B1473637 : Blo 1307972 1473637 := bbase (se 4 (by rfl) ⟨138153, by rfl⟩ : syracuseStep 1473637 = 276307) (by norm_num)
theorem B1473673 : Blo 1307972 1473673 := bbase (se 2 (by rfl) ⟨552627, by rfl⟩ : syracuseStep 1473673 = 1105255) (by norm_num)
theorem B2096285 : Blo 1307972 2096285 := bbase (se 3 (by rfl) ⟨393053, by rfl⟩ : syracuseStep 2096285 = 786107) (by norm_num)
theorem B1473709 : Blo 1307972 1473709 := bbase (se 3 (by rfl) ⟨276320, by rfl⟩ : syracuseStep 1473709 = 552641) (by norm_num)
theorem B2096317 : Blo 1307972 2096317 := bbase (se 3 (by rfl) ⟨393059, by rfl⟩ : syracuseStep 2096317 = 786119) (by norm_num)
theorem B4414661 : Blo 1307972 4414661 := bbase (se 4 (by rfl) ⟨413874, by rfl⟩ : syracuseStep 4414661 = 827749) (by norm_num)
theorem B11943125 : Blo 1307972 11943125 := bbase (se 7 (by rfl) ⟨139958, by rfl⟩ : syracuseStep 11943125 = 279917) (by norm_num)
theorem B8502581 : Blo 1307972 8502581 := bbase (se 5 (by rfl) ⟨398558, by rfl⟩ : syracuseStep 8502581 = 797117) (by norm_num)
theorem B4717925 : Blo 1307972 4717925 := bbase (se 4 (by rfl) ⟨442305, by rfl⟩ : syracuseStep 4717925 = 884611) (by norm_num)
theorem B2653573 : Blo 1307972 2653573 := bbase (se 4 (by rfl) ⟨248772, by rfl⟩ : syracuseStep 2653573 = 497545) (by norm_num)
theorem B3980677 : Blo 1307972 3980677 := bbase (se 4 (by rfl) ⟨373188, by rfl⟩ : syracuseStep 3980677 = 746377) (by norm_num)
theorem B5307781 : Blo 1307972 5307781 := bbase (se 4 (by rfl) ⟨497604, by rfl⟩ : syracuseStep 5307781 = 995209) (by norm_num)
theorem B5037461 : Blo 1307972 5037461 := bbase (se 6 (by rfl) ⟨118065, by rfl⟩ : syracuseStep 5037461 = 236131) (by norm_num)
theorem B1572257 : Blo 1307972 1572257 := bbase (se 2 (by rfl) ⟨589596, by rfl⟩ : syracuseStep 1572257 = 1179193) (by norm_num)
theorem B2358725 : Blo 1307972 2358725 := bbase (se 4 (by rfl) ⟨221130, by rfl⟩ : syracuseStep 2358725 = 442261) (by norm_num)
theorem B1572305 : Blo 1307972 1572305 := bbase (se 2 (by rfl) ⟨589614, by rfl⟩ : syracuseStep 1572305 = 1179229) (by norm_num)
theorem B1916389 : Blo 1307972 1916389 := bbase (se 4 (by rfl) ⟨179661, by rfl⟩ : syracuseStep 1916389 = 359323) (by norm_num)
theorem B4415093 : Blo 1307972 4415093 := bbase (se 5 (by rfl) ⟨206957, by rfl⟩ : syracuseStep 4415093 = 413915) (by norm_num)
theorem B6626933 : Blo 1307972 6626933 := bbase (se 5 (by rfl) ⟨310637, by rfl⟩ : syracuseStep 6626933 = 621275) (by norm_num)
theorem B5594741 : Blo 1307972 5594741 := bbase (se 5 (by rfl) ⟨262253, by rfl⟩ : syracuseStep 5594741 = 524507) (by norm_num)
theorem B1679005 : Blo 1307972 1679005 := bbase (se 3 (by rfl) ⟨314813, by rfl⟩ : syracuseStep 1679005 = 629627) (by norm_num)
theorem B7454389 : Blo 1307972 7454389 := bbase (se 5 (by rfl) ⟨349424, by rfl⟩ : syracuseStep 7454389 = 698849) (by norm_num)
theorem B3727093 : Blo 1307972 3727093 := bbase (se 5 (by rfl) ⟨174707, by rfl⟩ : syracuseStep 3727093 = 349415) (by norm_num)
theorem B2391805 : Blo 1307972 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B1941301 : Blo 1307972 1941301 := bbase (se 5 (by rfl) ⟨90998, by rfl⟩ : syracuseStep 1941301 = 181997) (by norm_num)
theorem B4972373 : Blo 1307972 4972373 := bbase (se 9 (by rfl) ⟨14567, by rfl⟩ : syracuseStep 4972373 = 29135) (by norm_num)
theorem B1679297 : Blo 1307972 1679297 := bbase (se 2 (by rfl) ⟨629736, by rfl⟩ : syracuseStep 1679297 = 1259473) (by norm_num)
theorem B1572853 : Blo 1307972 1572853 := bbase (se 5 (by rfl) ⟨73727, by rfl⟩ : syracuseStep 1572853 = 147455) (by norm_num)
theorem B3145841 : Blo 1307972 3145841 := bstep (se 2 (by rfl) ⟨1179690, by rfl⟩ : syracuseStep 3145841 = 2359381) B2359381
theorem B4415633 : Blo 1307972 4415633 := bstep (se 2 (by rfl) ⟨1655862, by rfl⟩ : syracuseStep 4415633 = 3311725) B3311725
theorem B1327411 : Blo 1307972 1327411 := bstep (se 1 (by rfl) ⟨995558, by rfl⟩ : syracuseStep 1327411 = 1991117) B1991117
theorem B3146051 : Blo 1307972 3146051 := bstep (se 1 (by rfl) ⟨2359538, by rfl⟩ : syracuseStep 3146051 = 4719077) B4719077
theorem B4194659 : Blo 1307972 4194659 := bstep (se 1 (by rfl) ⟨3145994, by rfl⟩ : syracuseStep 4194659 = 6291989) B6291989
theorem B8069509 : Blo 1307972 8069509 := bstep (se 4 (by rfl) ⟨756516, by rfl⟩ : syracuseStep 8069509 = 1513033) B1513033
theorem B4194787 : Blo 1307972 4194787 := bstep (se 1 (by rfl) ⟨3146090, by rfl⟩ : syracuseStep 4194787 = 6292181) B6292181
theorem B1991153 : Blo 1307972 1991153 := bstep (se 2 (by rfl) ⟨746682, by rfl⟩ : syracuseStep 1991153 = 1493365) B1493365
theorem B5038627 : Blo 1307972 5038627 := bstep (se 1 (by rfl) ⟨3778970, by rfl⟩ : syracuseStep 5038627 = 7557941) B7557941
theorem B3981869 : Blo 1307972 3981869 := bstep (se 3 (by rfl) ⟨746600, by rfl⟩ : syracuseStep 3981869 = 1493201) B1493201
theorem B77537845 : Blo 1307972 77537845 := bstep (se 5 (by rfl) ⟨3634586, by rfl⟩ : syracuseStep 77537845 = 7269173) B7269173
theorem B4194929 : Blo 1307972 4194929 := bstep (se 2 (by rfl) ⟨1573098, by rfl⟩ : syracuseStep 4194929 = 3146197) B3146197
theorem B2794115 : Blo 1307972 2794115 := bstep (se 1 (by rfl) ⟨2095586, by rfl⟩ : syracuseStep 2794115 = 4191173) B4191173
theorem B4416173 : Blo 1307972 4416173 := bstep (se 3 (by rfl) ⟨828032, by rfl⟩ : syracuseStep 4416173 = 1656065) B1656065
theorem B2097875 : Blo 1307972 2097875 := bstep (se 1 (by rfl) ⟨1573406, by rfl⟩ : syracuseStep 2097875 = 3146813) B3146813
theorem B4416227 : Blo 1307972 4416227 := bstep (se 1 (by rfl) ⟨3312170, by rfl⟩ : syracuseStep 4416227 = 6624341) B6624341
theorem B6628067 : Blo 1307972 6628067 := bstep (se 1 (by rfl) ⟨4971050, by rfl⟩ : syracuseStep 6628067 = 9942101) B9942101
theorem B4195043 : Blo 1307972 4195043 := bstep (se 1 (by rfl) ⟨3146282, by rfl⟩ : syracuseStep 4195043 = 6292565) B6292565
theorem B40862485 : Blo 1307972 40862485 := bstep (se 6 (by rfl) ⟨957714, by rfl⟩ : syracuseStep 40862485 = 1915429) B1915429
theorem B1655635 : Blo 1307972 1655635 := bstep (se 1 (by rfl) ⟨1241726, by rfl⟩ : syracuseStep 1655635 = 2483453) B2483453
theorem B7455665 : Blo 1307972 7455665 := bstep (se 2 (by rfl) ⟨2795874, by rfl⟩ : syracuseStep 7455665 = 5591749) B5591749
theorem B1655731 : Blo 1307972 1655731 := bstep (se 1 (by rfl) ⟨1241798, by rfl⟩ : syracuseStep 1655731 = 2483597) B2483597
theorem B4416497 : Blo 1307972 4416497 := bstep (se 2 (by rfl) ⟨1656186, by rfl⟩ : syracuseStep 4416497 = 3312373) B3312373
theorem B3728369 : Blo 1307972 3728369 := bstep (se 2 (by rfl) ⟨1398138, by rfl⟩ : syracuseStep 3728369 = 2796277) B2796277
theorem B7078961 : Blo 1307972 7078961 := bstep (se 2 (by rfl) ⟨2654610, by rfl⟩ : syracuseStep 7078961 = 5309221) B5309221
theorem B7554161 : Blo 1307972 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1614979 : Blo 1307972 1614979 := bstep (se 1 (by rfl) ⟨1211234, by rfl⟩ : syracuseStep 1614979 = 2422469) B2422469
theorem B3146897 : Blo 1307972 3146897 := bstep (se 2 (by rfl) ⟨1180086, by rfl⟩ : syracuseStep 3146897 = 2360173) B2360173
theorem B3540131 : Blo 1307972 3540131 := bstep (se 1 (by rfl) ⟨2655098, by rfl⟩ : syracuseStep 3540131 = 5310197) B5310197
theorem B15926453 : Blo 1307972 15926453 := bstep (se 5 (by rfl) ⟨746552, by rfl⟩ : syracuseStep 15926453 = 1493105) B1493105
theorem B3310865 : Blo 1307972 3310865 := bstep (se 2 (by rfl) ⟨1241574, by rfl⟩ : syracuseStep 3310865 = 2483149) B2483149
theorem B3310915 : Blo 1307972 3310915 := bstep (se 1 (by rfl) ⟨2483186, by rfl⟩ : syracuseStep 3310915 = 4966373) B4966373
theorem B7079309 : Blo 1307972 7079309 := bstep (se 3 (by rfl) ⟨1327370, by rfl⟩ : syracuseStep 7079309 = 2654741) B2654741
theorem B2835857 : Blo 1307972 2835857 := bstep (se 2 (by rfl) ⟨1063446, by rfl⟩ : syracuseStep 2835857 = 2126893) B2126893
theorem B1656227 : Blo 1307972 1656227 := bstep (se 1 (by rfl) ⟨1242170, by rfl⟩ : syracuseStep 1656227 = 2484341) B2484341
theorem B3311057 : Blo 1307972 3311057 := bstep (se 2 (by rfl) ⟨1241646, by rfl⟩ : syracuseStep 3311057 = 2483293) B2483293
theorem B2794979 : Blo 1307972 2794979 := bstep (se 1 (by rfl) ⟨2096234, by rfl⟩ : syracuseStep 2794979 = 4192469) B4192469
theorem B4417037 : Blo 1307972 4417037 := bstep (se 3 (by rfl) ⟨828194, by rfl⟩ : syracuseStep 4417037 = 1656389) B1656389
theorem B6628877 : Blo 1307972 6628877 := bstep (se 3 (by rfl) ⟨1242914, by rfl⟩ : syracuseStep 6628877 = 2485829) B2485829
theorem B8381987 : Blo 1307972 8381987 := bstep (se 1 (by rfl) ⟨6286490, by rfl⟩ : syracuseStep 8381987 = 12572981) B12572981
theorem B37725749 : Blo 1307972 37725749 := bstep (se 5 (by rfl) ⟨1768394, by rfl⟩ : syracuseStep 37725749 = 3536789) B3536789
theorem B2483779 : Blo 1307972 2483779 := bstep (se 1 (by rfl) ⟨1862834, by rfl⟩ : syracuseStep 2483779 = 3725669) B3725669
theorem B4417091 : Blo 1307972 4417091 := bstep (se 1 (by rfl) ⟨3312818, by rfl⟩ : syracuseStep 4417091 = 6625637) B6625637
theorem B2795089 : Blo 1307972 2795089 := bstep (se 2 (by rfl) ⟨1048158, by rfl⟩ : syracuseStep 2795089 = 2096317) B2096317
theorem B3729041 : Blo 1307972 3729041 := bstep (se 2 (by rfl) ⟨1398390, by rfl⟩ : syracuseStep 3729041 = 2796781) B2796781
theorem B3147427 : Blo 1307972 3147427 := bstep (se 1 (by rfl) ⟨2360570, by rfl⟩ : syracuseStep 3147427 = 4721141) B4721141
theorem B2483939 : Blo 1307972 2483939 := bstep (se 1 (by rfl) ⟨1862954, by rfl⟩ : syracuseStep 2483939 = 3725909) B3725909
theorem B4417361 : Blo 1307972 4417361 := bstep (se 2 (by rfl) ⟨1656510, by rfl⟩ : syracuseStep 4417361 = 3313021) B3313021
theorem B1656931 : Blo 1307972 1656931 := bstep (se 1 (by rfl) ⟨1242698, by rfl⟩ : syracuseStep 1656931 = 2485397) B2485397
theorem B2943089 : Blo 1307972 2943089 := bstep (se 2 (by rfl) ⟨1103658, by rfl⟩ : syracuseStep 2943089 = 2207317) B2207317
theorem B2943107 : Blo 1307972 2943107 := bstep (se 1 (by rfl) ⟨2207330, by rfl⟩ : syracuseStep 2943107 = 4414661) B4414661
theorem B4966541 : Blo 1307972 4966541 := bstep (se 3 (by rfl) ⟨931226, by rfl⟩ : syracuseStep 4966541 = 1862453) B1862453
theorem B4475057 : Blo 1307972 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B1657027 : Blo 1307972 1657027 := bstep (se 1 (by rfl) ⟨1242770, by rfl⟩ : syracuseStep 1657027 = 2485541) B2485541
theorem B2238673 : Blo 1307972 2238673 := bstep (se 2 (by rfl) ⟨839502, by rfl⟩ : syracuseStep 2238673 = 1679005) B1679005
theorem B9939185 : Blo 1307972 9939185 := bstep (se 2 (by rfl) ⟨3727194, by rfl⟩ : syracuseStep 9939185 = 7454389) B7454389
theorem B3189073 : Blo 1307972 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B7457123 : Blo 1307972 7457123 := bstep (se 1 (by rfl) ⟨5592842, by rfl⟩ : syracuseStep 7457123 = 11185685) B11185685
theorem B4417901 : Blo 1307972 4417901 := bstep (se 3 (by rfl) ⟨828356, by rfl⟩ : syracuseStep 4417901 = 1656713) B1656713
theorem B2943377 : Blo 1307972 2943377 := bstep (se 2 (by rfl) ⟨1103766, by rfl⟩ : syracuseStep 2943377 = 2207533) B2207533
theorem B2943395 : Blo 1307972 2943395 := bstep (se 1 (by rfl) ⟨2207546, by rfl⟩ : syracuseStep 2943395 = 4415093) B4415093
theorem B4417955 : Blo 1307972 4417955 := bstep (se 1 (by rfl) ⟨3313466, by rfl⟩ : syracuseStep 4417955 = 6626933) B6626933
theorem B3729827 : Blo 1307972 3729827 := bstep (se 1 (by rfl) ⟨2797370, by rfl⟩ : syracuseStep 3729827 = 5594741) B5594741
theorem B3312049 : Blo 1307972 3312049 := bstep (se 2 (by rfl) ⟨1242018, by rfl⟩ : syracuseStep 3312049 = 2484037) B2484037
theorem B5589425 : Blo 1307972 5589425 := bstep (se 2 (by rfl) ⟨2096034, by rfl⟩ : syracuseStep 5589425 = 4192069) B4192069
theorem B8391109 : Blo 1307972 8391109 := bstep (se 4 (by rfl) ⟨786666, by rfl⟩ : syracuseStep 8391109 = 1573333) B1573333
theorem B21219893 : Blo 1307972 21219893 := bstep (se 5 (by rfl) ⟨994682, by rfl⟩ : syracuseStep 21219893 = 1989365) B1989365
theorem B7760453 : Blo 1307972 7760453 := bstep (se 4 (by rfl) ⟨727542, by rfl⟩ : syracuseStep 7760453 = 1455085) B1455085
theorem B6294179 : Blo 1307972 6294179 := bstep (se 1 (by rfl) ⟨4720634, by rfl⟩ : syracuseStep 6294179 = 9441269) B9441269
theorem B2943665 : Blo 1307972 2943665 := bstep (se 2 (by rfl) ⟨1103874, by rfl⟩ : syracuseStep 2943665 = 2207749) B2207749
theorem B4418225 : Blo 1307972 4418225 := bstep (se 2 (by rfl) ⟨1656834, by rfl⟩ : syracuseStep 4418225 = 3313669) B3313669
theorem B1657523 : Blo 1307972 1657523 := bstep (se 1 (by rfl) ⟨1243142, by rfl⟩ : syracuseStep 1657523 = 2486285) B2486285
theorem B2943683 : Blo 1307972 2943683 := bstep (se 1 (by rfl) ⟨2207762, by rfl⟩ : syracuseStep 2943683 = 4415525) B4415525
theorem B3312323 : Blo 1307972 3312323 := bstep (se 1 (by rfl) ⟨2484242, by rfl⟩ : syracuseStep 3312323 = 4968485) B4968485
theorem B2210051 : Blo 1307972 2210051 := bstep (se 1 (by rfl) ⟨1657538, by rfl⟩ : syracuseStep 2210051 = 3315077) B3315077
theorem B3730157 : Blo 1307972 3730157 := bstep (se 3 (by rfl) ⟨699404, by rfl⟩ : syracuseStep 3730157 = 1398809) B1398809
theorem B3779341 : Blo 1307972 3779341 := bstep (se 3 (by rfl) ⟨708626, by rfl⟩ : syracuseStep 3779341 = 1417253) B1417253
theorem B2485009 : Blo 1307972 2485009 := bstep (se 2 (by rfl) ⟨931878, by rfl⟩ : syracuseStep 2485009 = 1863757) B1863757
theorem B3730225 : Blo 1307972 3730225 := bstep (se 2 (by rfl) ⟨1398834, by rfl⟩ : syracuseStep 3730225 = 2797669) B2797669
theorem B3312515 : Blo 1307972 3312515 := bstep (se 1 (by rfl) ⟨2484386, by rfl⟩ : syracuseStep 3312515 = 4968773) B4968773
theorem B1862561 : Blo 1307972 1862561 := bstep (se 2 (by rfl) ⟨698460, by rfl⟩ : syracuseStep 1862561 = 1396921) B1396921
theorem B4967345 : Blo 1307972 4967345 := bstep (se 2 (by rfl) ⟨1862754, by rfl⟩ : syracuseStep 4967345 = 3725509) B3725509
theorem B6294449 : Blo 1307972 6294449 := bstep (se 2 (by rfl) ⟨2360418, by rfl⟩ : syracuseStep 6294449 = 4720837) B4720837
theorem B2943953 : Blo 1307972 2943953 := bstep (se 2 (by rfl) ⟨1103982, by rfl⟩ : syracuseStep 2943953 = 2207965) B2207965
theorem B2943971 : Blo 1307972 2943971 := bstep (se 1 (by rfl) ⟨2207978, by rfl⟩ : syracuseStep 2943971 = 4415957) B4415957
theorem B6294563 : Blo 1307972 6294563 := bstep (se 1 (by rfl) ⟨4720922, by rfl⟩ : syracuseStep 6294563 = 9441845) B9441845
theorem B5590093 : Blo 1307972 5590093 := bstep (se 3 (by rfl) ⟨1048142, by rfl⟩ : syracuseStep 5590093 = 2096285) B2096285
theorem B7081037 : Blo 1307972 7081037 := bstep (se 3 (by rfl) ⟨1327694, by rfl⟩ : syracuseStep 7081037 = 2655389) B2655389
theorem B7957603 : Blo 1307972 7957603 := bstep (se 1 (by rfl) ⟨5968202, by rfl⟩ : syracuseStep 7957603 = 11936405) B11936405
theorem B18877637 : Blo 1307972 18877637 := bstep (se 4 (by rfl) ⟨1769778, by rfl⟩ : syracuseStep 18877637 = 3539557) B3539557
theorem B4418765 : Blo 1307972 4418765 := bstep (se 3 (by rfl) ⟨828518, by rfl⟩ : syracuseStep 4418765 = 1657037) B1657037
theorem B2944241 : Blo 1307972 2944241 := bstep (se 2 (by rfl) ⟨1104090, by rfl⟩ : syracuseStep 2944241 = 2208181) B2208181
theorem B2944259 : Blo 1307972 2944259 := bstep (se 1 (by rfl) ⟨2208194, by rfl⟩ : syracuseStep 2944259 = 4416389) B4416389
theorem B4418819 : Blo 1307972 4418819 := bstep (se 1 (by rfl) ⟨3314114, by rfl⟩ : syracuseStep 4418819 = 6628229) B6628229
theorem B2985233 : Blo 1307972 2985233 := bstep (se 2 (by rfl) ⟨1119462, by rfl⟩ : syracuseStep 2985233 = 2238925) B2238925
theorem B8064305 : Blo 1307972 8064305 := bstep (se 2 (by rfl) ⟨3024114, by rfl⟩ : syracuseStep 8064305 = 6048229) B6048229
theorem B68930957 : Blo 1307972 68930957 := bstep (se 3 (by rfl) ⟨12924554, by rfl⟩ : syracuseStep 68930957 = 25849109) B25849109
theorem B1863091 : Blo 1307972 1863091 := bstep (se 1 (by rfl) ⟨1397318, by rfl⟩ : syracuseStep 1863091 = 2794637) B2794637
theorem B2944529 : Blo 1307972 2944529 := bstep (se 2 (by rfl) ⟨1104198, by rfl⟩ : syracuseStep 2944529 = 2208397) B2208397
theorem B4419089 : Blo 1307972 4419089 := bstep (se 2 (by rfl) ⟨1657158, by rfl⟩ : syracuseStep 4419089 = 3314317) B3314317
theorem B2944547 : Blo 1307972 2944547 := bstep (se 1 (by rfl) ⟨2208410, by rfl⟩ : syracuseStep 2944547 = 4416821) B4416821
theorem B4714033 : Blo 1307972 4714033 := bstep (se 2 (by rfl) ⟨1767762, by rfl⟩ : syracuseStep 4714033 = 3535525) B3535525
theorem B2797105 : Blo 1307972 2797105 := bstep (se 2 (by rfl) ⟨1048914, by rfl⟩ : syracuseStep 2797105 = 2097829) B2097829
theorem B2207297 : Blo 1307972 2207297 := bstep (se 2 (by rfl) ⟨827736, by rfl⟩ : syracuseStep 2207297 = 1655473) B1655473
theorem B14143045 : Blo 1307972 14143045 := bstep (se 4 (by rfl) ⟨1325910, by rfl⟩ : syracuseStep 14143045 = 2651821) B2651821
theorem B4968013 : Blo 1307972 4968013 := bstep (se 3 (by rfl) ⟨931502, by rfl⟩ : syracuseStep 4968013 = 1863005) B1863005
theorem B4714147 : Blo 1307972 4714147 := bstep (se 1 (by rfl) ⟨3535610, by rfl⟩ : syracuseStep 4714147 = 7071221) B7071221
theorem B6622883 : Blo 1307972 6622883 := bstep (se 1 (by rfl) ⟨4967162, by rfl⟩ : syracuseStep 6622883 = 9934325) B9934325
theorem B5590691 : Blo 1307972 5590691 := bstep (se 1 (by rfl) ⟨4193018, by rfl⟩ : syracuseStep 5590691 = 8386037) B8386037
theorem B7450289 : Blo 1307972 7450289 := bstep (se 2 (by rfl) ⟨2793858, by rfl⟩ : syracuseStep 7450289 = 5587717) B5587717
theorem B2207425 : Blo 1307972 2207425 := bstep (se 2 (by rfl) ⟨827784, by rfl⟩ : syracuseStep 2207425 = 1655569) B1655569
theorem B2207459 : Blo 1307972 2207459 := bstep (se 1 (by rfl) ⟨1655594, by rfl⟩ : syracuseStep 2207459 = 3311189) B3311189
theorem B1863427 : Blo 1307972 1863427 := bstep (se 1 (by rfl) ⟨1397570, by rfl⟩ : syracuseStep 1863427 = 2795141) B2795141
theorem B2944817 : Blo 1307972 2944817 := bstep (se 2 (by rfl) ⟨1104306, by rfl⟩ : syracuseStep 2944817 = 2208613) B2208613
theorem B3313457 : Blo 1307972 3313457 := bstep (se 2 (by rfl) ⟨1242546, by rfl⟩ : syracuseStep 3313457 = 2485093) B2485093
theorem B2486065 : Blo 1307972 2486065 := bstep (se 2 (by rfl) ⟨932274, by rfl⟩ : syracuseStep 2486065 = 1864549) B1864549
theorem B2944835 : Blo 1307972 2944835 := bstep (se 1 (by rfl) ⟨2208626, by rfl⟩ : syracuseStep 2944835 = 4417253) B4417253
theorem B5304163 : Blo 1307972 5304163 := bstep (se 1 (by rfl) ⟨3978122, by rfl⟩ : syracuseStep 5304163 = 7956245) B7956245
theorem B2207587 : Blo 1307972 2207587 := bstep (se 1 (by rfl) ⟨1655690, by rfl⟩ : syracuseStep 2207587 = 3311381) B3311381
theorem B3313507 : Blo 1307972 3313507 := bstep (se 1 (by rfl) ⟨2485130, by rfl⟩ : syracuseStep 3313507 = 4970261) B4970261
theorem B2797507 : Blo 1307972 2797507 := bstep (se 1 (by rfl) ⟨2098130, by rfl⟩ : syracuseStep 2797507 = 4196261) B4196261
theorem B1961969 : Blo 1307972 1961969 := bstep (se 2 (by rfl) ⟨735738, by rfl⟩ : syracuseStep 1961969 = 1471477) B1471477
theorem B2207729 : Blo 1307972 2207729 := bstep (se 2 (by rfl) ⟨827898, by rfl⟩ : syracuseStep 2207729 = 1655797) B1655797
theorem B3313649 : Blo 1307972 3313649 := bstep (se 2 (by rfl) ⟨1242618, by rfl⟩ : syracuseStep 3313649 = 2485237) B2485237
theorem B1961987 : Blo 1307972 1961987 := bstep (se 1 (by rfl) ⟨1471490, by rfl⟩ : syracuseStep 1961987 = 2942981) B2942981
theorem B1962017 : Blo 1307972 1962017 := bstep (se 2 (by rfl) ⟨735756, by rfl⟩ : syracuseStep 1962017 = 1471513) B1471513
theorem B4419629 : Blo 1307972 4419629 := bstep (se 3 (by rfl) ⟨828680, by rfl⟩ : syracuseStep 4419629 = 1657361) B1657361
theorem B1962035 : Blo 1307972 1962035 := bstep (se 1 (by rfl) ⟨1471526, by rfl⟩ : syracuseStep 1962035 = 2943053) B2943053
theorem B1962065 : Blo 1307972 1962065 := bstep (se 2 (by rfl) ⟨735774, by rfl⟩ : syracuseStep 1962065 = 1471549) B1471549
theorem B2945105 : Blo 1307972 2945105 := bstep (se 2 (by rfl) ⟨1104414, by rfl⟩ : syracuseStep 2945105 = 2208829) B2208829
theorem B1962083 : Blo 1307972 1962083 := bstep (se 1 (by rfl) ⟨1471562, by rfl⟩ : syracuseStep 1962083 = 2943125) B2943125
theorem B2945123 : Blo 1307972 2945123 := bstep (se 1 (by rfl) ⟨2208842, by rfl⟩ : syracuseStep 2945123 = 4417685) B4417685
theorem B4419683 : Blo 1307972 4419683 := bstep (se 1 (by rfl) ⟨3314762, by rfl⟩ : syracuseStep 4419683 = 6629525) B6629525
theorem B2207857 : Blo 1307972 2207857 := bstep (se 2 (by rfl) ⟨827946, by rfl⟩ : syracuseStep 2207857 = 1655893) B1655893
theorem B1962113 : Blo 1307972 1962113 := bstep (se 2 (by rfl) ⟨735792, by rfl⟩ : syracuseStep 1962113 = 1471585) B1471585
theorem B1962131 : Blo 1307972 1962131 := bstep (se 1 (by rfl) ⟨1471598, by rfl⟩ : syracuseStep 1962131 = 2943197) B2943197
theorem B2207891 : Blo 1307972 2207891 := bstep (se 1 (by rfl) ⟨1655918, by rfl⟩ : syracuseStep 2207891 = 3311837) B3311837
theorem B1962161 : Blo 1307972 1962161 := bstep (se 2 (by rfl) ⟨735810, by rfl⟩ : syracuseStep 1962161 = 1471621) B1471621
theorem B1962179 : Blo 1307972 1962179 := bstep (se 1 (by rfl) ⟨1471634, by rfl⟩ : syracuseStep 1962179 = 2943269) B2943269
theorem B2486467 : Blo 1307972 2486467 := bstep (se 1 (by rfl) ⟨1864850, by rfl⟩ : syracuseStep 2486467 = 3729701) B3729701
theorem B1962209 : Blo 1307972 1962209 := bstep (se 2 (by rfl) ⟨735828, by rfl⟩ : syracuseStep 1962209 = 1471657) B1471657
theorem B2486513 : Blo 1307972 2486513 := bstep (se 2 (by rfl) ⟨932442, by rfl⟩ : syracuseStep 2486513 = 1864885) B1864885
theorem B1962227 : Blo 1307972 1962227 := bstep (se 1 (by rfl) ⟨1471670, by rfl⟩ : syracuseStep 1962227 = 2943341) B2943341
theorem B1962257 : Blo 1307972 1962257 := bstep (se 2 (by rfl) ⟨735846, by rfl⟩ : syracuseStep 1962257 = 1471693) B1471693
theorem B2208019 : Blo 1307972 2208019 := bstep (se 1 (by rfl) ⟨1656014, by rfl⟩ : syracuseStep 2208019 = 3312029) B3312029
theorem B1962275 : Blo 1307972 1962275 := bstep (se 1 (by rfl) ⟨1471706, by rfl⟩ : syracuseStep 1962275 = 2943413) B2943413
theorem B1863985 : Blo 1307972 1863985 := bstep (se 2 (by rfl) ⟨698994, by rfl⟩ : syracuseStep 1863985 = 1397989) B1397989
theorem B3780913 : Blo 1307972 3780913 := bstep (se 2 (by rfl) ⟨1417842, by rfl⟩ : syracuseStep 3780913 = 2835685) B2835685
theorem B1962305 : Blo 1307972 1962305 := bstep (se 2 (by rfl) ⟨735864, by rfl⟩ : syracuseStep 1962305 = 1471729) B1471729
theorem B1962323 : Blo 1307972 1962323 := bstep (se 1 (by rfl) ⟨1471742, by rfl⟩ : syracuseStep 1962323 = 2943485) B2943485
theorem B1864019 : Blo 1307972 1864019 := bstep (se 1 (by rfl) ⟨1398014, by rfl⟩ : syracuseStep 1864019 = 2796029) B2796029
theorem B4968803 : Blo 1307972 4968803 := bstep (se 1 (by rfl) ⟨3726602, by rfl⟩ : syracuseStep 4968803 = 7453205) B7453205
theorem B1962353 : Blo 1307972 1962353 := bstep (se 2 (by rfl) ⟨735882, by rfl⟩ : syracuseStep 1962353 = 1471765) B1471765
theorem B2945393 : Blo 1307972 2945393 := bstep (se 2 (by rfl) ⟨1104522, by rfl⟩ : syracuseStep 2945393 = 2209045) B2209045
theorem B4419953 : Blo 1307972 4419953 := bstep (se 2 (by rfl) ⟨1657482, by rfl⟩ : syracuseStep 4419953 = 3314965) B3314965
theorem B1962371 : Blo 1307972 1962371 := bstep (se 1 (by rfl) ⟨1471778, by rfl⟩ : syracuseStep 1962371 = 2943557) B2943557
theorem B2945411 : Blo 1307972 2945411 := bstep (se 1 (by rfl) ⟨2209058, by rfl⟩ : syracuseStep 2945411 = 4418117) B4418117
theorem B1962401 : Blo 1307972 1962401 := bstep (se 2 (by rfl) ⟨735900, by rfl⟩ : syracuseStep 1962401 = 1471801) B1471801
theorem B2208161 : Blo 1307972 2208161 := bstep (se 2 (by rfl) ⟨828060, by rfl⟩ : syracuseStep 2208161 = 1656121) B1656121
theorem B1962419 : Blo 1307972 1962419 := bstep (se 1 (by rfl) ⟨1471814, by rfl⟩ : syracuseStep 1962419 = 2943629) B2943629
theorem B6623693 : Blo 1307972 6623693 := bstep (se 3 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 6623693 = 2483885) B2483885
theorem B1962449 : Blo 1307972 1962449 := bstep (se 2 (by rfl) ⟨735918, by rfl⟩ : syracuseStep 1962449 = 1471837) B1471837
theorem B1962467 : Blo 1307972 1962467 := bstep (se 1 (by rfl) ⟨1471850, by rfl⟩ : syracuseStep 1962467 = 2943701) B2943701
theorem B1962497 : Blo 1307972 1962497 := bstep (se 2 (by rfl) ⟨735936, by rfl⟩ : syracuseStep 1962497 = 1471873) B1471873
theorem B4190737 : Blo 1307972 4190737 := bstep (se 2 (by rfl) ⟨1571526, by rfl⟩ : syracuseStep 4190737 = 3143053) B3143053
theorem B2486801 : Blo 1307972 2486801 := bstep (se 2 (by rfl) ⟨932550, by rfl⟩ : syracuseStep 2486801 = 1865101) B1865101
theorem B1962515 : Blo 1307972 1962515 := bstep (se 1 (by rfl) ⟨1471886, by rfl⟩ : syracuseStep 1962515 = 2943773) B2943773
theorem B2208289 : Blo 1307972 2208289 := bstep (se 2 (by rfl) ⟨828108, by rfl⟩ : syracuseStep 2208289 = 1656217) B1656217
theorem B1962545 : Blo 1307972 1962545 := bstep (se 2 (by rfl) ⟨735954, by rfl⟩ : syracuseStep 1962545 = 1471909) B1471909
theorem B1962563 : Blo 1307972 1962563 := bstep (se 1 (by rfl) ⟨1471922, by rfl⟩ : syracuseStep 1962563 = 2943845) B2943845
theorem B2208323 : Blo 1307972 2208323 := bstep (se 1 (by rfl) ⟨1656242, by rfl⟩ : syracuseStep 2208323 = 3312485) B3312485
theorem B1962593 : Blo 1307972 1962593 := bstep (se 2 (by rfl) ⟨735972, by rfl⟩ : syracuseStep 1962593 = 1471945) B1471945
theorem B1962611 : Blo 1307972 1962611 := bstep (se 1 (by rfl) ⟨1471958, by rfl⟩ : syracuseStep 1962611 = 2943917) B2943917
theorem B1962641 : Blo 1307972 1962641 := bstep (se 2 (by rfl) ⟨735990, by rfl⟩ : syracuseStep 1962641 = 1471981) B1471981
theorem B2945681 : Blo 1307972 2945681 := bstep (se 2 (by rfl) ⟨1104630, by rfl⟩ : syracuseStep 2945681 = 2209261) B2209261
theorem B1962659 : Blo 1307972 1962659 := bstep (se 1 (by rfl) ⟨1471994, by rfl⟩ : syracuseStep 1962659 = 2943989) B2943989
theorem B2945699 : Blo 1307972 2945699 := bstep (se 1 (by rfl) ⟨2209274, by rfl⟩ : syracuseStep 2945699 = 4418549) B4418549
theorem B1962689 : Blo 1307972 1962689 := bstep (se 2 (by rfl) ⟨736008, by rfl⟩ : syracuseStep 1962689 = 1472017) B1472017
theorem B2208451 : Blo 1307972 2208451 := bstep (se 1 (by rfl) ⟨1656338, by rfl⟩ : syracuseStep 2208451 = 3312677) B3312677
theorem B1962707 : Blo 1307972 1962707 := bstep (se 1 (by rfl) ⟨1472030, by rfl⟩ : syracuseStep 1962707 = 2944061) B2944061
theorem B1397459 : Blo 1307972 1397459 := bstep (se 1 (by rfl) ⟨1048094, by rfl⟩ : syracuseStep 1397459 = 2096189) B2096189
theorem B1962737 : Blo 1307972 1962737 := bstep (se 2 (by rfl) ⟨736026, by rfl⟩ : syracuseStep 1962737 = 1472053) B1472053
theorem B1962755 : Blo 1307972 1962755 := bstep (se 1 (by rfl) ⟨1472066, by rfl⟩ : syracuseStep 1962755 = 2944133) B2944133
theorem B1962785 : Blo 1307972 1962785 := bstep (se 2 (by rfl) ⟨736044, by rfl⟩ : syracuseStep 1962785 = 1472089) B1472089
theorem B1962803 : Blo 1307972 1962803 := bstep (se 1 (by rfl) ⟨1472102, by rfl⟩ : syracuseStep 1962803 = 2944205) B2944205
theorem B1962833 : Blo 1307972 1962833 := bstep (se 2 (by rfl) ⟨736062, by rfl⟩ : syracuseStep 1962833 = 1472125) B1472125
theorem B2208593 : Blo 1307972 2208593 := bstep (se 2 (by rfl) ⟨828222, by rfl⟩ : syracuseStep 2208593 = 1656445) B1656445
theorem B1962851 : Blo 1307972 1962851 := bstep (se 1 (by rfl) ⟨1472138, by rfl⟩ : syracuseStep 1962851 = 2944277) B2944277
theorem B1962881 : Blo 1307972 1962881 := bstep (se 2 (by rfl) ⟨736080, by rfl⟩ : syracuseStep 1962881 = 1472161) B1472161
theorem B1864577 : Blo 1307972 1864577 := bstep (se 2 (by rfl) ⟨699216, by rfl⟩ : syracuseStep 1864577 = 1398433) B1398433
theorem B4420493 : Blo 1307972 4420493 := bstep (se 3 (by rfl) ⟨828842, by rfl⟩ : syracuseStep 4420493 = 1657685) B1657685
theorem B1962899 : Blo 1307972 1962899 := bstep (se 1 (by rfl) ⟨1472174, by rfl⟩ : syracuseStep 1962899 = 2944349) B2944349
theorem B1962929 : Blo 1307972 1962929 := bstep (se 2 (by rfl) ⟨736098, by rfl⟩ : syracuseStep 1962929 = 1472197) B1472197
theorem B2945969 : Blo 1307972 2945969 := bstep (se 2 (by rfl) ⟨1104738, by rfl⟩ : syracuseStep 2945969 = 2209477) B2209477
theorem B1962947 : Blo 1307972 1962947 := bstep (se 1 (by rfl) ⟨1472210, by rfl⟩ : syracuseStep 1962947 = 2944421) B2944421
theorem B2945987 : Blo 1307972 2945987 := bstep (se 1 (by rfl) ⟨2209490, by rfl⟩ : syracuseStep 2945987 = 4418981) B4418981
theorem B4420547 : Blo 1307972 4420547 := bstep (se 1 (by rfl) ⟨3315410, by rfl⟩ : syracuseStep 4420547 = 6630821) B6630821
theorem B2208721 : Blo 1307972 2208721 := bstep (se 2 (by rfl) ⟨828270, by rfl⟩ : syracuseStep 2208721 = 1656541) B1656541
theorem B3314641 : Blo 1307972 3314641 := bstep (se 2 (by rfl) ⟨1242990, by rfl⟩ : syracuseStep 3314641 = 2485981) B2485981
theorem B1864657 : Blo 1307972 1864657 := bstep (se 2 (by rfl) ⟨699246, by rfl⟩ : syracuseStep 1864657 = 1398493) B1398493
theorem B1962977 : Blo 1307972 1962977 := bstep (se 2 (by rfl) ⟨736116, by rfl⟩ : syracuseStep 1962977 = 1472233) B1472233
theorem B4969457 : Blo 1307972 4969457 := bstep (se 2 (by rfl) ⟨1863546, by rfl⟩ : syracuseStep 4969457 = 3727093) B3727093
theorem B1962995 : Blo 1307972 1962995 := bstep (se 1 (by rfl) ⟨1472246, by rfl⟩ : syracuseStep 1962995 = 2944493) B2944493
theorem B2208755 : Blo 1307972 2208755 := bstep (se 1 (by rfl) ⟨1656566, by rfl⟩ : syracuseStep 2208755 = 3313133) B3313133
theorem B1963025 : Blo 1307972 1963025 := bstep (se 2 (by rfl) ⟨736134, by rfl⟩ : syracuseStep 1963025 = 1472269) B1472269
theorem B1963043 : Blo 1307972 1963043 := bstep (se 1 (by rfl) ⟨1472282, by rfl⟩ : syracuseStep 1963043 = 2944565) B2944565
theorem B1963073 : Blo 1307972 1963073 := bstep (se 2 (by rfl) ⟨736152, by rfl⟩ : syracuseStep 1963073 = 1472305) B1472305
theorem B5968973 : Blo 1307972 5968973 := bstep (se 3 (by rfl) ⟨1119182, by rfl⟩ : syracuseStep 5968973 = 2238365) B2238365
theorem B1963091 : Blo 1307972 1963091 := bstep (se 1 (by rfl) ⟨1472318, by rfl⟩ : syracuseStep 1963091 = 2944637) B2944637
theorem B7451747 : Blo 1307972 7451747 := bstep (se 1 (by rfl) ⟨5588810, by rfl⟩ : syracuseStep 7451747 = 11177621) B11177621
theorem B1963121 : Blo 1307972 1963121 := bstep (se 2 (by rfl) ⟨736170, by rfl⟩ : syracuseStep 1963121 = 1472341) B1472341
theorem B1471603 : Blo 1307972 1471603 := bstep (se 1 (by rfl) ⟨1103702, by rfl⟩ : syracuseStep 1471603 = 2207405) B2207405
theorem B2208883 : Blo 1307972 2208883 := bstep (se 1 (by rfl) ⟨1656662, by rfl⟩ : syracuseStep 2208883 = 3313325) B3313325
theorem B1963139 : Blo 1307972 1963139 := bstep (se 1 (by rfl) ⟨1472354, by rfl⟩ : syracuseStep 1963139 = 2944709) B2944709
theorem B8385677 : Blo 1307972 8385677 := bstep (se 3 (by rfl) ⟨1572314, by rfl⟩ : syracuseStep 8385677 = 3144629) B3144629
theorem B1963169 : Blo 1307972 1963169 := bstep (se 2 (by rfl) ⟨736188, by rfl⟩ : syracuseStep 1963169 = 1472377) B1472377
theorem B3978413 : Blo 1307972 3978413 := bstep (se 3 (by rfl) ⟨745952, by rfl⟩ : syracuseStep 3978413 = 1491905) B1491905
theorem B4478125 : Blo 1307972 4478125 := bstep (se 3 (by rfl) ⟨839648, by rfl⟩ : syracuseStep 4478125 = 1679297) B1679297
theorem B1963187 : Blo 1307972 1963187 := bstep (se 1 (by rfl) ⟨1472390, by rfl⟩ : syracuseStep 1963187 = 2944781) B2944781
theorem B10220741 : Blo 1307972 10220741 := bstep (se 4 (by rfl) ⟨958194, by rfl⟩ : syracuseStep 10220741 = 1916389) B1916389
theorem B1963217 : Blo 1307972 1963217 := bstep (se 2 (by rfl) ⟨736206, by rfl⟩ : syracuseStep 1963217 = 1472413) B1472413
theorem B2946257 : Blo 1307972 2946257 := bstep (se 2 (by rfl) ⟨1104846, by rfl⟩ : syracuseStep 2946257 = 2209693) B2209693
theorem B4420817 : Blo 1307972 4420817 := bstep (se 2 (by rfl) ⟨1657806, by rfl⟩ : syracuseStep 4420817 = 3315613) B3315613
theorem B3536099 : Blo 1307972 3536099 := bstep (se 1 (by rfl) ⟨2652074, by rfl⟩ : syracuseStep 3536099 = 5304149) B5304149
theorem B1963235 : Blo 1307972 1963235 := bstep (se 1 (by rfl) ⟨1472426, by rfl⟩ : syracuseStep 1963235 = 2944853) B2944853
theorem B2946275 : Blo 1307972 2946275 := bstep (se 1 (by rfl) ⟨2209706, by rfl⟩ : syracuseStep 2946275 = 4419413) B4419413
theorem B3314915 : Blo 1307972 3314915 := bstep (se 1 (by rfl) ⟨2486186, by rfl⟩ : syracuseStep 3314915 = 4972373) B4972373
theorem B1963265 : Blo 1307972 1963265 := bstep (se 2 (by rfl) ⟨736224, by rfl⟩ : syracuseStep 1963265 = 1472449) B1472449
theorem B2209025 : Blo 1307972 2209025 := bstep (se 2 (by rfl) ⟨828384, by rfl⟩ : syracuseStep 2209025 = 1656769) B1656769
theorem B1471747 : Blo 1307972 1471747 := bstep (se 1 (by rfl) ⟨1103810, by rfl⟩ : syracuseStep 1471747 = 2207621) B2207621
theorem B1963283 : Blo 1307972 1963283 := bstep (se 1 (by rfl) ⟨1472462, by rfl⟩ : syracuseStep 1963283 = 2944925) B2944925
theorem B1963313 : Blo 1307972 1963313 := bstep (se 2 (by rfl) ⟨736242, by rfl⟩ : syracuseStep 1963313 = 1472485) B1472485
theorem B1963331 : Blo 1307972 1963331 := bstep (se 1 (by rfl) ⟨1472498, by rfl⟩ : syracuseStep 1963331 = 2944997) B2944997
theorem B1307987 : Blo 1307972 1307987 := bstep (se 1 (by rfl) ⟨980990, by rfl⟩ : syracuseStep 1307987 = 1961981) B1961981
theorem B1963361 : Blo 1307972 1963361 := bstep (se 2 (by rfl) ⟨736260, by rfl⟩ : syracuseStep 1963361 = 1472521) B1472521
theorem B1308003 : Blo 1307972 1308003 := bstep (se 1 (by rfl) ⟨981002, by rfl⟩ : syracuseStep 1308003 = 1962005) B1962005
theorem B1308019 : Blo 1307972 1308019 := bstep (se 1 (by rfl) ⟨981014, by rfl⟩ : syracuseStep 1308019 = 1962029) B1962029
theorem B1963379 : Blo 1307972 1963379 := bstep (se 1 (by rfl) ⟨1472534, by rfl⟩ : syracuseStep 1963379 = 2945069) B2945069
theorem B1308035 : Blo 1307972 1308035 := bstep (se 1 (by rfl) ⟨981026, by rfl⟩ : syracuseStep 1308035 = 1962053) B1962053
theorem B2209153 : Blo 1307972 2209153 := bstep (se 2 (by rfl) ⟨828432, by rfl⟩ : syracuseStep 2209153 = 1656865) B1656865
theorem B7959941 : Blo 1307972 7959941 := bstep (se 4 (by rfl) ⟨746244, by rfl⟩ : syracuseStep 7959941 = 1492489) B1492489
theorem B1963409 : Blo 1307972 1963409 := bstep (se 2 (by rfl) ⟨736278, by rfl⟩ : syracuseStep 1963409 = 1472557) B1472557
theorem B1308051 : Blo 1307972 1308051 := bstep (se 1 (by rfl) ⟨981038, by rfl⟩ : syracuseStep 1308051 = 1962077) B1962077
theorem B1471891 : Blo 1307972 1471891 := bstep (se 1 (by rfl) ⟨1103918, by rfl⟩ : syracuseStep 1471891 = 2207837) B2207837
theorem B1308067 : Blo 1307972 1308067 := bstep (se 1 (by rfl) ⟨981050, by rfl⟩ : syracuseStep 1308067 = 1962101) B1962101
theorem B3978659 : Blo 1307972 3978659 := bstep (se 1 (by rfl) ⟨2983994, by rfl⟩ : syracuseStep 3978659 = 5967989) B5967989
theorem B1963427 : Blo 1307972 1963427 := bstep (se 1 (by rfl) ⟨1472570, by rfl⟩ : syracuseStep 1963427 = 2945141) B2945141
theorem B2209187 : Blo 1307972 2209187 := bstep (se 1 (by rfl) ⟨1656890, by rfl⟩ : syracuseStep 2209187 = 3313781) B3313781
theorem B3315107 : Blo 1307972 3315107 := bstep (se 1 (by rfl) ⟨2486330, by rfl⟩ : syracuseStep 3315107 = 4972661) B4972661
theorem B1308083 : Blo 1307972 1308083 := bstep (se 1 (by rfl) ⟨981062, by rfl⟩ : syracuseStep 1308083 = 1962125) B1962125
theorem B1963457 : Blo 1307972 1963457 := bstep (se 2 (by rfl) ⟨736296, by rfl⟩ : syracuseStep 1963457 = 1472593) B1472593
theorem B1308099 : Blo 1307972 1308099 := bstep (se 1 (by rfl) ⟨981074, by rfl⟩ : syracuseStep 1308099 = 1962149) B1962149
theorem B1308115 : Blo 1307972 1308115 := bstep (se 1 (by rfl) ⟨981086, by rfl⟩ : syracuseStep 1308115 = 1962173) B1962173
theorem B1963475 : Blo 1307972 1963475 := bstep (se 1 (by rfl) ⟨1472606, by rfl⟩ : syracuseStep 1963475 = 2945213) B2945213
theorem B1308131 : Blo 1307972 1308131 := bstep (se 1 (by rfl) ⟨981098, by rfl⟩ : syracuseStep 1308131 = 1962197) B1962197
theorem B1963505 : Blo 1307972 1963505 := bstep (se 2 (by rfl) ⟨736314, by rfl⟩ : syracuseStep 1963505 = 1472629) B1472629
theorem B2946545 : Blo 1307972 2946545 := bstep (se 2 (by rfl) ⟨1104954, by rfl⟩ : syracuseStep 2946545 = 2209909) B2209909
theorem B1308147 : Blo 1307972 1308147 := bstep (se 1 (by rfl) ⟨981110, by rfl⟩ : syracuseStep 1308147 = 1962221) B1962221
theorem B1308163 : Blo 1307972 1308163 := bstep (se 1 (by rfl) ⟨981122, by rfl⟩ : syracuseStep 1308163 = 1962245) B1962245
theorem B1963523 : Blo 1307972 1963523 := bstep (se 1 (by rfl) ⟨1472642, by rfl⟩ : syracuseStep 1963523 = 2945285) B2945285
theorem B2946563 : Blo 1307972 2946563 := bstep (se 1 (by rfl) ⟨2209922, by rfl⟩ : syracuseStep 2946563 = 4419845) B4419845
theorem B1308179 : Blo 1307972 1308179 := bstep (se 1 (by rfl) ⟨981134, by rfl⟩ : syracuseStep 1308179 = 1962269) B1962269
theorem B1963553 : Blo 1307972 1963553 := bstep (se 2 (by rfl) ⟨736332, by rfl⟩ : syracuseStep 1963553 = 1472665) B1472665
theorem B1308195 : Blo 1307972 1308195 := bstep (se 1 (by rfl) ⟨981146, by rfl⟩ : syracuseStep 1308195 = 1962293) B1962293
theorem B1472035 : Blo 1307972 1472035 := bstep (se 1 (by rfl) ⟨1104026, by rfl⟩ : syracuseStep 1472035 = 2208053) B2208053
theorem B2209315 : Blo 1307972 2209315 := bstep (se 1 (by rfl) ⟨1656986, by rfl⟩ : syracuseStep 2209315 = 3313973) B3313973
theorem B1308211 : Blo 1307972 1308211 := bstep (se 1 (by rfl) ⟨981158, by rfl⟩ : syracuseStep 1308211 = 1962317) B1962317
theorem B1963571 : Blo 1307972 1963571 := bstep (se 1 (by rfl) ⟨1472678, by rfl⟩ : syracuseStep 1963571 = 2945357) B2945357
theorem B1308227 : Blo 1307972 1308227 := bstep (se 1 (by rfl) ⟨981170, by rfl⟩ : syracuseStep 1308227 = 1962341) B1962341
theorem B1963601 : Blo 1307972 1963601 := bstep (se 2 (by rfl) ⟨736350, by rfl⟩ : syracuseStep 1963601 = 1472701) B1472701
theorem B1308243 : Blo 1307972 1308243 := bstep (se 1 (by rfl) ⟨981182, by rfl⟩ : syracuseStep 1308243 = 1962365) B1962365
theorem B1308259 : Blo 1307972 1308259 := bstep (se 1 (by rfl) ⟨981194, by rfl⟩ : syracuseStep 1308259 = 1962389) B1962389
theorem B1963619 : Blo 1307972 1963619 := bstep (se 1 (by rfl) ⟨1472714, by rfl⟩ : syracuseStep 1963619 = 2945429) B2945429
theorem B1308275 : Blo 1307972 1308275 := bstep (se 1 (by rfl) ⟨981206, by rfl⟩ : syracuseStep 1308275 = 1962413) B1962413
theorem B1963649 : Blo 1307972 1963649 := bstep (se 2 (by rfl) ⟨736368, by rfl⟩ : syracuseStep 1963649 = 1472737) B1472737
theorem B1308291 : Blo 1307972 1308291 := bstep (se 1 (by rfl) ⟨981218, by rfl⟩ : syracuseStep 1308291 = 1962437) B1962437
theorem B1308307 : Blo 1307972 1308307 := bstep (se 1 (by rfl) ⟨981230, by rfl⟩ : syracuseStep 1308307 = 1962461) B1962461
theorem B1963667 : Blo 1307972 1963667 := bstep (se 1 (by rfl) ⟨1472750, by rfl⟩ : syracuseStep 1963667 = 2945501) B2945501
theorem B1308323 : Blo 1307972 1308323 := bstep (se 1 (by rfl) ⟨981242, by rfl⟩ : syracuseStep 1308323 = 1962485) B1962485
theorem B4429475 : Blo 1307972 4429475 := bstep (se 1 (by rfl) ⟨3322106, by rfl⟩ : syracuseStep 4429475 = 6644213) B6644213
theorem B1963697 : Blo 1307972 1963697 := bstep (se 2 (by rfl) ⟨736386, by rfl⟩ : syracuseStep 1963697 = 1472773) B1472773
theorem B2209457 : Blo 1307972 2209457 := bstep (se 2 (by rfl) ⟨828546, by rfl⟩ : syracuseStep 2209457 = 1657093) B1657093
theorem B1308339 : Blo 1307972 1308339 := bstep (se 1 (by rfl) ⟨981254, by rfl⟩ : syracuseStep 1308339 = 1962509) B1962509
theorem B1472179 : Blo 1307972 1472179 := bstep (se 1 (by rfl) ⟨1104134, by rfl⟩ : syracuseStep 1472179 = 2208269) B2208269
theorem B1308355 : Blo 1307972 1308355 := bstep (se 1 (by rfl) ⟨981266, by rfl⟩ : syracuseStep 1308355 = 1962533) B1962533
theorem B1963715 : Blo 1307972 1963715 := bstep (se 1 (by rfl) ⟨1472786, by rfl⟩ : syracuseStep 1963715 = 2945573) B2945573
theorem B1308371 : Blo 1307972 1308371 := bstep (se 1 (by rfl) ⟨981278, by rfl⟩ : syracuseStep 1308371 = 1962557) B1962557
theorem B1963745 : Blo 1307972 1963745 := bstep (se 2 (by rfl) ⟨736404, by rfl⟩ : syracuseStep 1963745 = 1472809) B1472809
theorem B1308387 : Blo 1307972 1308387 := bstep (se 1 (by rfl) ⟨981290, by rfl⟩ : syracuseStep 1308387 = 1962581) B1962581
theorem B1308403 : Blo 1307972 1308403 := bstep (se 1 (by rfl) ⟨981302, by rfl⟩ : syracuseStep 1308403 = 1962605) B1962605
theorem B1963763 : Blo 1307972 1963763 := bstep (se 1 (by rfl) ⟨1472822, by rfl⟩ : syracuseStep 1963763 = 2945645) B2945645
theorem B1308419 : Blo 1307972 1308419 := bstep (se 1 (by rfl) ⟨981314, by rfl⟩ : syracuseStep 1308419 = 1962629) B1962629
theorem B5379853 : Blo 1307972 5379853 := bstep (se 3 (by rfl) ⟨1008722, by rfl⟩ : syracuseStep 5379853 = 2017445) B2017445
theorem B1963793 : Blo 1307972 1963793 := bstep (se 2 (by rfl) ⟨736422, by rfl⟩ : syracuseStep 1963793 = 1472845) B1472845
theorem B1308435 : Blo 1307972 1308435 := bstep (se 1 (by rfl) ⟨981326, by rfl⟩ : syracuseStep 1308435 = 1962653) B1962653
theorem B2946833 : Blo 1307972 2946833 := bstep (se 2 (by rfl) ⟨1105062, by rfl⟩ : syracuseStep 2946833 = 2210125) B2210125
theorem B1308451 : Blo 1307972 1308451 := bstep (se 1 (by rfl) ⟨981338, by rfl⟩ : syracuseStep 1308451 = 1962677) B1962677
theorem B1963811 : Blo 1307972 1963811 := bstep (se 1 (by rfl) ⟨1472858, by rfl⟩ : syracuseStep 1963811 = 2945717) B2945717
theorem B2946851 : Blo 1307972 2946851 := bstep (se 1 (by rfl) ⟨2210138, by rfl⟩ : syracuseStep 2946851 = 4420277) B4420277
theorem B2209585 : Blo 1307972 2209585 := bstep (se 2 (by rfl) ⟨828594, by rfl⟩ : syracuseStep 2209585 = 1657189) B1657189
theorem B1308467 : Blo 1307972 1308467 := bstep (se 1 (by rfl) ⟨981350, by rfl⟩ : syracuseStep 1308467 = 1962701) B1962701
theorem B1963841 : Blo 1307972 1963841 := bstep (se 2 (by rfl) ⟨736440, by rfl⟩ : syracuseStep 1963841 = 1472881) B1472881
theorem B1308483 : Blo 1307972 1308483 := bstep (se 1 (by rfl) ⟨981362, by rfl⟩ : syracuseStep 1308483 = 1962725) B1962725
theorem B1472323 : Blo 1307972 1472323 := bstep (se 1 (by rfl) ⟨1104242, by rfl⟩ : syracuseStep 1472323 = 2208485) B2208485
theorem B1308499 : Blo 1307972 1308499 := bstep (se 1 (by rfl) ⟨981374, by rfl⟩ : syracuseStep 1308499 = 1962749) B1962749
theorem B1963859 : Blo 1307972 1963859 := bstep (se 1 (by rfl) ⟨1472894, by rfl⟩ : syracuseStep 1963859 = 2945789) B2945789
theorem B2209619 : Blo 1307972 2209619 := bstep (se 1 (by rfl) ⟨1657214, by rfl⟩ : syracuseStep 2209619 = 3314429) B3314429
theorem B1308515 : Blo 1307972 1308515 := bstep (se 1 (by rfl) ⟨981386, by rfl⟩ : syracuseStep 1308515 = 1962773) B1962773
theorem B1963889 : Blo 1307972 1963889 := bstep (se 2 (by rfl) ⟨736458, by rfl⟩ : syracuseStep 1963889 = 1472917) B1472917
theorem B1308531 : Blo 1307972 1308531 := bstep (se 1 (by rfl) ⟨981398, by rfl⟩ : syracuseStep 1308531 = 1962797) B1962797
theorem B1308547 : Blo 1307972 1308547 := bstep (se 1 (by rfl) ⟨981410, by rfl⟩ : syracuseStep 1308547 = 1962821) B1962821
theorem B1963907 : Blo 1307972 1963907 := bstep (se 1 (by rfl) ⟨1472930, by rfl⟩ : syracuseStep 1963907 = 2945861) B2945861
theorem B1308563 : Blo 1307972 1308563 := bstep (se 1 (by rfl) ⟨981422, by rfl⟩ : syracuseStep 1308563 = 1962845) B1962845
theorem B1963937 : Blo 1307972 1963937 := bstep (se 2 (by rfl) ⟨736476, by rfl⟩ : syracuseStep 1963937 = 1472953) B1472953
theorem B1308579 : Blo 1307972 1308579 := bstep (se 1 (by rfl) ⟨981434, by rfl⟩ : syracuseStep 1308579 = 1962869) B1962869
theorem B1308595 : Blo 1307972 1308595 := bstep (se 1 (by rfl) ⟨981446, by rfl⟩ : syracuseStep 1308595 = 1962893) B1962893
theorem B1963955 : Blo 1307972 1963955 := bstep (se 1 (by rfl) ⟨1472966, by rfl⟩ : syracuseStep 1963955 = 2945933) B2945933
theorem B1308611 : Blo 1307972 1308611 := bstep (se 1 (by rfl) ⟨981458, by rfl⟩ : syracuseStep 1308611 = 1962917) B1962917
theorem B1963985 : Blo 1307972 1963985 := bstep (se 2 (by rfl) ⟨736494, by rfl⟩ : syracuseStep 1963985 = 1472989) B1472989
theorem B1308627 : Blo 1307972 1308627 := bstep (se 1 (by rfl) ⟨981470, by rfl⟩ : syracuseStep 1308627 = 1962941) B1962941
theorem B1472467 : Blo 1307972 1472467 := bstep (se 1 (by rfl) ⟨1104350, by rfl⟩ : syracuseStep 1472467 = 2208701) B2208701
theorem B2209747 : Blo 1307972 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B1308643 : Blo 1307972 1308643 := bstep (se 1 (by rfl) ⟨981482, by rfl⟩ : syracuseStep 1308643 = 1962965) B1962965
theorem B1964003 : Blo 1307972 1964003 := bstep (se 1 (by rfl) ⟨1473002, by rfl⟩ : syracuseStep 1964003 = 2946005) B2946005
theorem B1308659 : Blo 1307972 1308659 := bstep (se 1 (by rfl) ⟨981494, by rfl⟩ : syracuseStep 1308659 = 1962989) B1962989
theorem B1964033 : Blo 1307972 1964033 := bstep (se 2 (by rfl) ⟨736512, by rfl⟩ : syracuseStep 1964033 = 1473025) B1473025
theorem B1308675 : Blo 1307972 1308675 := bstep (se 1 (by rfl) ⟨981506, by rfl⟩ : syracuseStep 1308675 = 1963013) B1963013
theorem B1308691 : Blo 1307972 1308691 := bstep (se 1 (by rfl) ⟨981518, by rfl⟩ : syracuseStep 1308691 = 1963037) B1963037
theorem B1964051 : Blo 1307972 1964051 := bstep (se 1 (by rfl) ⟨1473038, by rfl⟩ : syracuseStep 1964051 = 2946077) B2946077
theorem B1308707 : Blo 1307972 1308707 := bstep (se 1 (by rfl) ⟨981530, by rfl⟩ : syracuseStep 1308707 = 1963061) B1963061
theorem B1964081 : Blo 1307972 1964081 := bstep (se 2 (by rfl) ⟨736530, by rfl⟩ : syracuseStep 1964081 = 1473061) B1473061
theorem B1308723 : Blo 1307972 1308723 := bstep (se 1 (by rfl) ⟨981542, by rfl⟩ : syracuseStep 1308723 = 1963085) B1963085
theorem B2947121 : Blo 1307972 2947121 := bstep (se 2 (by rfl) ⟨1105170, by rfl⟩ : syracuseStep 2947121 = 2210341) B2210341
theorem B1308739 : Blo 1307972 1308739 := bstep (se 1 (by rfl) ⟨981554, by rfl⟩ : syracuseStep 1308739 = 1963109) B1963109
theorem B1964099 : Blo 1307972 1964099 := bstep (se 1 (by rfl) ⟨1473074, by rfl⟩ : syracuseStep 1964099 = 2946149) B2946149
theorem B2947139 : Blo 1307972 2947139 := bstep (se 1 (by rfl) ⟨2210354, by rfl⟩ : syracuseStep 2947139 = 4420709) B4420709
theorem B7452749 : Blo 1307972 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B1308755 : Blo 1307972 1308755 := bstep (se 1 (by rfl) ⟨981566, by rfl⟩ : syracuseStep 1308755 = 1963133) B1963133
theorem B1964129 : Blo 1307972 1964129 := bstep (se 2 (by rfl) ⟨736548, by rfl⟩ : syracuseStep 1964129 = 1473097) B1473097
theorem B2357347 : Blo 1307972 2357347 := bstep (se 1 (by rfl) ⟨1768010, by rfl⟩ : syracuseStep 2357347 = 3536021) B3536021
theorem B1308771 : Blo 1307972 1308771 := bstep (se 1 (by rfl) ⟨981578, by rfl⟩ : syracuseStep 1308771 = 1963157) B1963157
theorem B1472611 : Blo 1307972 1472611 := bstep (se 1 (by rfl) ⟨1104458, by rfl⟩ : syracuseStep 1472611 = 2208917) B2208917
theorem B2209889 : Blo 1307972 2209889 := bstep (se 2 (by rfl) ⟨828708, by rfl⟩ : syracuseStep 2209889 = 1657417) B1657417
theorem B1308787 : Blo 1307972 1308787 := bstep (se 1 (by rfl) ⟨981590, by rfl⟩ : syracuseStep 1308787 = 1963181) B1963181
theorem B1964147 : Blo 1307972 1964147 := bstep (se 1 (by rfl) ⟨1473110, by rfl⟩ : syracuseStep 1964147 = 2946221) B2946221
theorem B1308803 : Blo 1307972 1308803 := bstep (se 1 (by rfl) ⟨981602, by rfl⟩ : syracuseStep 1308803 = 1963205) B1963205
theorem B3725453 : Blo 1307972 3725453 := bstep (se 3 (by rfl) ⟨698522, by rfl⟩ : syracuseStep 3725453 = 1397045) B1397045
theorem B1964177 : Blo 1307972 1964177 := bstep (se 2 (by rfl) ⟨736566, by rfl⟩ : syracuseStep 1964177 = 1473133) B1473133
theorem B1308819 : Blo 1307972 1308819 := bstep (se 1 (by rfl) ⟨981614, by rfl⟩ : syracuseStep 1308819 = 1963229) B1963229
theorem B1308835 : Blo 1307972 1308835 := bstep (se 1 (by rfl) ⟨981626, by rfl⟩ : syracuseStep 1308835 = 1963253) B1963253
theorem B1964195 : Blo 1307972 1964195 := bstep (se 1 (by rfl) ⟨1473146, by rfl⟩ : syracuseStep 1964195 = 2946293) B2946293
theorem B1308851 : Blo 1307972 1308851 := bstep (se 1 (by rfl) ⟨981638, by rfl⟩ : syracuseStep 1308851 = 1963277) B1963277
theorem B1964225 : Blo 1307972 1964225 := bstep (se 2 (by rfl) ⟨736584, by rfl⟩ : syracuseStep 1964225 = 1473169) B1473169
theorem B1308867 : Blo 1307972 1308867 := bstep (se 1 (by rfl) ⟨981650, by rfl⟩ : syracuseStep 1308867 = 1963301) B1963301
theorem B1308883 : Blo 1307972 1308883 := bstep (se 1 (by rfl) ⟨981662, by rfl⟩ : syracuseStep 1308883 = 1963325) B1963325
theorem B1964243 : Blo 1307972 1964243 := bstep (se 1 (by rfl) ⟨1473182, by rfl⟩ : syracuseStep 1964243 = 2946365) B2946365
theorem B2210017 : Blo 1307972 2210017 := bstep (se 2 (by rfl) ⟨828756, by rfl⟩ : syracuseStep 2210017 = 1657513) B1657513
theorem B1308899 : Blo 1307972 1308899 := bstep (se 1 (by rfl) ⟨981674, by rfl⟩ : syracuseStep 1308899 = 1963349) B1963349
theorem B1964273 : Blo 1307972 1964273 := bstep (se 2 (by rfl) ⟨736602, by rfl⟩ : syracuseStep 1964273 = 1473205) B1473205
theorem B1308915 : Blo 1307972 1308915 := bstep (se 1 (by rfl) ⟨981686, by rfl⟩ : syracuseStep 1308915 = 1963373) B1963373
theorem B1472755 : Blo 1307972 1472755 := bstep (se 1 (by rfl) ⟨1104566, by rfl⟩ : syracuseStep 1472755 = 2209133) B2209133
theorem B1308931 : Blo 1307972 1308931 := bstep (se 1 (by rfl) ⟨981698, by rfl⟩ : syracuseStep 1308931 = 1963397) B1963397
theorem B1964291 : Blo 1307972 1964291 := bstep (se 1 (by rfl) ⟨1473218, by rfl⟩ : syracuseStep 1964291 = 2946437) B2946437
theorem B1308947 : Blo 1307972 1308947 := bstep (se 1 (by rfl) ⟨981710, by rfl⟩ : syracuseStep 1308947 = 1963421) B1963421
theorem B1964321 : Blo 1307972 1964321 := bstep (se 2 (by rfl) ⟨736620, by rfl⟩ : syracuseStep 1964321 = 1473241) B1473241
theorem B1308963 : Blo 1307972 1308963 := bstep (se 1 (by rfl) ⟨981722, by rfl⟩ : syracuseStep 1308963 = 1963445) B1963445
theorem B1308979 : Blo 1307972 1308979 := bstep (se 1 (by rfl) ⟨981734, by rfl⟩ : syracuseStep 1308979 = 1963469) B1963469
theorem B1964339 : Blo 1307972 1964339 := bstep (se 1 (by rfl) ⟨1473254, by rfl⟩ : syracuseStep 1964339 = 2946509) B2946509
theorem B3725635 : Blo 1307972 3725635 := bstep (se 1 (by rfl) ⟨2794226, by rfl⟩ : syracuseStep 3725635 = 5588453) B5588453
theorem B1308995 : Blo 1307972 1308995 := bstep (se 1 (by rfl) ⟨981746, by rfl⟩ : syracuseStep 1308995 = 1963493) B1963493
theorem B3537233 : Blo 1307972 3537233 := bstep (se 2 (by rfl) ⟨1326462, by rfl⟩ : syracuseStep 3537233 = 2652925) B2652925
theorem B1964369 : Blo 1307972 1964369 := bstep (se 2 (by rfl) ⟨736638, by rfl⟩ : syracuseStep 1964369 = 1473277) B1473277
theorem B1309011 : Blo 1307972 1309011 := bstep (se 1 (by rfl) ⟨981758, by rfl⟩ : syracuseStep 1309011 = 1963517) B1963517
theorem B2947409 : Blo 1307972 2947409 := bstep (se 2 (by rfl) ⟨1105278, by rfl⟩ : syracuseStep 2947409 = 2210557) B2210557
theorem B1309027 : Blo 1307972 1309027 := bstep (se 1 (by rfl) ⟨981770, by rfl⟩ : syracuseStep 1309027 = 1963541) B1963541
theorem B1964387 : Blo 1307972 1964387 := bstep (se 1 (by rfl) ⟨1473290, by rfl⟩ : syracuseStep 1964387 = 2946581) B2946581
theorem B2947427 : Blo 1307972 2947427 := bstep (se 1 (by rfl) ⟨2210570, by rfl⟩ : syracuseStep 2947427 = 4421141) B4421141
theorem B1309043 : Blo 1307972 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B1309059 : Blo 1307972 1309059 := bstep (se 1 (by rfl) ⟨981794, by rfl⟩ : syracuseStep 1309059 = 1963589) B1963589
theorem B1472899 : Blo 1307972 1472899 := bstep (se 1 (by rfl) ⟨1104674, by rfl⟩ : syracuseStep 1472899 = 2209349) B2209349
theorem B1964417 : Blo 1307972 1964417 := bstep (se 2 (by rfl) ⟨736656, by rfl⟩ : syracuseStep 1964417 = 1473313) B1473313
theorem B2210179 : Blo 1307972 2210179 := bstep (se 1 (by rfl) ⟨1657634, by rfl⟩ : syracuseStep 2210179 = 3315269) B3315269
theorem B1309075 : Blo 1307972 1309075 := bstep (se 1 (by rfl) ⟨981806, by rfl⟩ : syracuseStep 1309075 = 1963613) B1963613
theorem B1964435 : Blo 1307972 1964435 := bstep (se 1 (by rfl) ⟨1473326, by rfl⟩ : syracuseStep 1964435 = 2946653) B2946653
theorem B1309091 : Blo 1307972 1309091 := bstep (se 1 (by rfl) ⟨981818, by rfl⟩ : syracuseStep 1309091 = 1963637) B1963637
theorem B4970915 : Blo 1307972 4970915 := bstep (se 1 (by rfl) ⟨3728186, by rfl⟩ : syracuseStep 4970915 = 7456373) B7456373
theorem B4192685 : Blo 1307972 4192685 := bstep (se 3 (by rfl) ⟨786128, by rfl⟩ : syracuseStep 4192685 = 1572257) B1572257
theorem B4970929 : Blo 1307972 4970929 := bstep (se 2 (by rfl) ⟨1864098, by rfl⟩ : syracuseStep 4970929 = 3728197) B3728197
theorem B1964465 : Blo 1307972 1964465 := bstep (se 2 (by rfl) ⟨736674, by rfl⟩ : syracuseStep 1964465 = 1473349) B1473349
theorem B1309107 : Blo 1307972 1309107 := bstep (se 1 (by rfl) ⟨981830, by rfl⟩ : syracuseStep 1309107 = 1963661) B1963661
theorem B1309123 : Blo 1307972 1309123 := bstep (se 1 (by rfl) ⟨981842, by rfl⟩ : syracuseStep 1309123 = 1963685) B1963685
theorem B1964483 : Blo 1307972 1964483 := bstep (se 1 (by rfl) ⟨1473362, by rfl⟩ : syracuseStep 1964483 = 2946725) B2946725
theorem B1309139 : Blo 1307972 1309139 := bstep (se 1 (by rfl) ⟨981854, by rfl⟩ : syracuseStep 1309139 = 1963709) B1963709
theorem B1964513 : Blo 1307972 1964513 := bstep (se 2 (by rfl) ⟨736692, by rfl⟩ : syracuseStep 1964513 = 1473385) B1473385
theorem B1309155 : Blo 1307972 1309155 := bstep (se 1 (by rfl) ⟨981866, by rfl⟩ : syracuseStep 1309155 = 1963733) B1963733
theorem B1309171 : Blo 1307972 1309171 := bstep (se 1 (by rfl) ⟨981878, by rfl⟩ : syracuseStep 1309171 = 1963757) B1963757
theorem B1964531 : Blo 1307972 1964531 := bstep (se 1 (by rfl) ⟨1473398, by rfl⟩ : syracuseStep 1964531 = 2946797) B2946797
theorem B1309187 : Blo 1307972 1309187 := bstep (se 1 (by rfl) ⟨981890, by rfl⟩ : syracuseStep 1309187 = 1963781) B1963781
theorem B6289933 : Blo 1307972 6289933 := bstep (se 3 (by rfl) ⟨1179362, by rfl⟩ : syracuseStep 6289933 = 2358725) B2358725
theorem B1964561 : Blo 1307972 1964561 := bstep (se 2 (by rfl) ⟨736710, by rfl⟩ : syracuseStep 1964561 = 1473421) B1473421
theorem B2210321 : Blo 1307972 2210321 := bstep (se 2 (by rfl) ⟨828870, by rfl⟩ : syracuseStep 2210321 = 1657741) B1657741
theorem B1309203 : Blo 1307972 1309203 := bstep (se 1 (by rfl) ⟨981902, by rfl⟩ : syracuseStep 1309203 = 1963805) B1963805
theorem B1473043 : Blo 1307972 1473043 := bstep (se 1 (by rfl) ⟨1104782, by rfl⟩ : syracuseStep 1473043 = 2209565) B2209565
theorem B1309219 : Blo 1307972 1309219 := bstep (se 1 (by rfl) ⟨981914, by rfl⟩ : syracuseStep 1309219 = 1963829) B1963829
theorem B1964579 : Blo 1307972 1964579 := bstep (se 1 (by rfl) ⟨1473434, by rfl⟩ : syracuseStep 1964579 = 2946869) B2946869
theorem B4192813 : Blo 1307972 4192813 := bstep (se 3 (by rfl) ⟨786152, by rfl⟩ : syracuseStep 4192813 = 1572305) B1572305
theorem B1309235 : Blo 1307972 1309235 := bstep (se 1 (by rfl) ⟨981926, by rfl⟩ : syracuseStep 1309235 = 1963853) B1963853
theorem B1964609 : Blo 1307972 1964609 := bstep (se 2 (by rfl) ⟨736728, by rfl⟩ : syracuseStep 1964609 = 1473457) B1473457
theorem B1309251 : Blo 1307972 1309251 := bstep (se 1 (by rfl) ⟨981938, by rfl⟩ : syracuseStep 1309251 = 1963877) B1963877
theorem B1571411 : Blo 1307972 1571411 := bstep (se 1 (by rfl) ⟨1178558, by rfl⟩ : syracuseStep 1571411 = 2357117) B2357117
theorem B1309267 : Blo 1307972 1309267 := bstep (se 1 (by rfl) ⟨981950, by rfl⟩ : syracuseStep 1309267 = 1963901) B1963901
theorem B1964627 : Blo 1307972 1964627 := bstep (se 1 (by rfl) ⟨1473470, by rfl⟩ : syracuseStep 1964627 = 2946941) B2946941
theorem B1309283 : Blo 1307972 1309283 := bstep (se 1 (by rfl) ⟨981962, by rfl⟩ : syracuseStep 1309283 = 1963925) B1963925
theorem B1964657 : Blo 1307972 1964657 := bstep (se 2 (by rfl) ⟨736746, by rfl⟩ : syracuseStep 1964657 = 1473493) B1473493
theorem B1309299 : Blo 1307972 1309299 := bstep (se 1 (by rfl) ⟨981974, by rfl⟩ : syracuseStep 1309299 = 1963949) B1963949
theorem B1309315 : Blo 1307972 1309315 := bstep (se 1 (by rfl) ⟨981986, by rfl⟩ : syracuseStep 1309315 = 1963973) B1963973
theorem B1964675 : Blo 1307972 1964675 := bstep (se 1 (by rfl) ⟨1473506, by rfl⟩ : syracuseStep 1964675 = 2947013) B2947013
theorem B15932045 : Blo 1307972 15932045 := bstep (se 3 (by rfl) ⟨2987258, by rfl⟩ : syracuseStep 15932045 = 5974517) B5974517
theorem B1309331 : Blo 1307972 1309331 := bstep (se 1 (by rfl) ⟨981998, by rfl⟩ : syracuseStep 1309331 = 1963997) B1963997
theorem B2210449 : Blo 1307972 2210449 := bstep (se 2 (by rfl) ⟨828918, by rfl⟩ : syracuseStep 2210449 = 1657837) B1657837
theorem B1964705 : Blo 1307972 1964705 := bstep (se 2 (by rfl) ⟨736764, by rfl⟩ : syracuseStep 1964705 = 1473529) B1473529
theorem B1309347 : Blo 1307972 1309347 := bstep (se 1 (by rfl) ⟨982010, by rfl⟩ : syracuseStep 1309347 = 1964021) B1964021
theorem B1473187 : Blo 1307972 1473187 := bstep (se 1 (by rfl) ⟨1104890, by rfl⟩ : syracuseStep 1473187 = 2209781) B2209781
theorem B1309363 : Blo 1307972 1309363 := bstep (se 1 (by rfl) ⟨982022, by rfl⟩ : syracuseStep 1309363 = 1964045) B1964045
theorem B1964723 : Blo 1307972 1964723 := bstep (se 1 (by rfl) ⟨1473542, by rfl⟩ : syracuseStep 1964723 = 2947085) B2947085
theorem B2210483 : Blo 1307972 2210483 := bstep (se 1 (by rfl) ⟨1657862, by rfl⟩ : syracuseStep 2210483 = 3315725) B3315725
theorem B1309379 : Blo 1307972 1309379 := bstep (se 1 (by rfl) ⟨982034, by rfl⟩ : syracuseStep 1309379 = 1964069) B1964069
theorem B1964753 : Blo 1307972 1964753 := bstep (se 2 (by rfl) ⟨736782, by rfl⟩ : syracuseStep 1964753 = 1473565) B1473565
theorem B1309395 : Blo 1307972 1309395 := bstep (se 1 (by rfl) ⟨982046, by rfl⟩ : syracuseStep 1309395 = 1964093) B1964093
theorem B1309411 : Blo 1307972 1309411 := bstep (se 1 (by rfl) ⟨982058, by rfl⟩ : syracuseStep 1309411 = 1964117) B1964117
theorem B1964771 : Blo 1307972 1964771 := bstep (se 1 (by rfl) ⟨1473578, by rfl⟩ : syracuseStep 1964771 = 2947157) B2947157
theorem B1309427 : Blo 1307972 1309427 := bstep (se 1 (by rfl) ⟨982070, by rfl⟩ : syracuseStep 1309427 = 1964141) B1964141
theorem B1309443 : Blo 1307972 1309443 := bstep (se 1 (by rfl) ⟨982082, by rfl⟩ : syracuseStep 1309443 = 1964165) B1964165
theorem B1964801 : Blo 1307972 1964801 := bstep (se 2 (by rfl) ⟨736800, by rfl⟩ : syracuseStep 1964801 = 1473601) B1473601
theorem B1309459 : Blo 1307972 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B1964819 : Blo 1307972 1964819 := bstep (se 1 (by rfl) ⟨1473614, by rfl⟩ : syracuseStep 1964819 = 2947229) B2947229
theorem B1309475 : Blo 1307972 1309475 := bstep (se 1 (by rfl) ⟨982106, by rfl⟩ : syracuseStep 1309475 = 1964213) B1964213
theorem B3726125 : Blo 1307972 3726125 := bstep (se 3 (by rfl) ⟨698648, by rfl⟩ : syracuseStep 3726125 = 1397297) B1397297
theorem B1964849 : Blo 1307972 1964849 := bstep (se 2 (by rfl) ⟨736818, by rfl⟩ : syracuseStep 1964849 = 1473637) B1473637
theorem B1309491 : Blo 1307972 1309491 := bstep (se 1 (by rfl) ⟨982118, by rfl⟩ : syracuseStep 1309491 = 1964237) B1964237
theorem B1473331 : Blo 1307972 1473331 := bstep (se 1 (by rfl) ⟨1104998, by rfl⟩ : syracuseStep 1473331 = 2209997) B2209997
theorem B1309507 : Blo 1307972 1309507 := bstep (se 1 (by rfl) ⟨982130, by rfl⟩ : syracuseStep 1309507 = 1964261) B1964261
theorem B1964867 : Blo 1307972 1964867 := bstep (se 1 (by rfl) ⟨1473650, by rfl⟩ : syracuseStep 1964867 = 2947301) B2947301
theorem B1309523 : Blo 1307972 1309523 := bstep (se 1 (by rfl) ⟨982142, by rfl⟩ : syracuseStep 1309523 = 1964285) B1964285
theorem B1964897 : Blo 1307972 1964897 := bstep (se 2 (by rfl) ⟨736836, by rfl⟩ : syracuseStep 1964897 = 1473673) B1473673
theorem B1309539 : Blo 1307972 1309539 := bstep (se 1 (by rfl) ⟨982154, by rfl⟩ : syracuseStep 1309539 = 1964309) B1964309
theorem B1309555 : Blo 1307972 1309555 := bstep (se 1 (by rfl) ⟨982166, by rfl⟩ : syracuseStep 1309555 = 1964333) B1964333
theorem B1964915 : Blo 1307972 1964915 := bstep (se 1 (by rfl) ⟨1473686, by rfl⟩ : syracuseStep 1964915 = 2947373) B2947373
theorem B1309571 : Blo 1307972 1309571 := bstep (se 1 (by rfl) ⟨982178, by rfl⟩ : syracuseStep 1309571 = 1964357) B1964357
theorem B1964945 : Blo 1307972 1964945 := bstep (se 2 (by rfl) ⟨736854, by rfl⟩ : syracuseStep 1964945 = 1473709) B1473709
theorem B1309587 : Blo 1307972 1309587 := bstep (se 1 (by rfl) ⟨982190, by rfl⟩ : syracuseStep 1309587 = 1964381) B1964381
theorem B1309603 : Blo 1307972 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B1309619 : Blo 1307972 1309619 := bstep (se 1 (by rfl) ⟨982214, by rfl⟩ : syracuseStep 1309619 = 1964429) B1964429
theorem B1309635 : Blo 1307972 1309635 := bstep (se 1 (by rfl) ⟨982226, by rfl⟩ : syracuseStep 1309635 = 1964453) B1964453
theorem B1473475 : Blo 1307972 1473475 := bstep (se 1 (by rfl) ⟨1105106, by rfl⟩ : syracuseStep 1473475 = 2210213) B2210213
theorem B1309651 : Blo 1307972 1309651 := bstep (se 1 (by rfl) ⟨982238, by rfl⟩ : syracuseStep 1309651 = 1964477) B1964477
theorem B16767971 : Blo 1307972 16767971 := bstep (se 1 (by rfl) ⟨12575978, by rfl⟩ : syracuseStep 16767971 = 25151957) B25151957
theorem B1309667 : Blo 1307972 1309667 := bstep (se 1 (by rfl) ⟨982250, by rfl⟩ : syracuseStep 1309667 = 1964501) B1964501
theorem B4414445 : Blo 1307972 4414445 := bstep (se 3 (by rfl) ⟨827708, by rfl⟩ : syracuseStep 4414445 = 1655417) B1655417
theorem B1309683 : Blo 1307972 1309683 := bstep (se 1 (by rfl) ⟨982262, by rfl⟩ : syracuseStep 1309683 = 1964525) B1964525
theorem B1309699 : Blo 1307972 1309699 := bstep (se 1 (by rfl) ⟨982274, by rfl⟩ : syracuseStep 1309699 = 1964549) B1964549
theorem B1309715 : Blo 1307972 1309715 := bstep (se 1 (by rfl) ⟨982286, by rfl⟩ : syracuseStep 1309715 = 1964573) B1964573
theorem B4414499 : Blo 1307972 4414499 := bstep (se 1 (by rfl) ⟨3310874, by rfl⟩ : syracuseStep 4414499 = 6621749) B6621749
theorem B1309731 : Blo 1307972 1309731 := bstep (se 1 (by rfl) ⟨982298, by rfl⟩ : syracuseStep 1309731 = 1964597) B1964597
theorem B1309747 : Blo 1307972 1309747 := bstep (se 1 (by rfl) ⟨982310, by rfl⟩ : syracuseStep 1309747 = 1964621) B1964621
theorem B1309763 : Blo 1307972 1309763 := bstep (se 1 (by rfl) ⟨982322, by rfl⟩ : syracuseStep 1309763 = 1964645) B1964645
theorem B1309779 : Blo 1307972 1309779 := bstep (se 1 (by rfl) ⟨982334, by rfl⟩ : syracuseStep 1309779 = 1964669) B1964669
theorem B1473619 : Blo 1307972 1473619 := bstep (se 1 (by rfl) ⟨1105214, by rfl⟩ : syracuseStep 1473619 = 2210429) B2210429
theorem B1309795 : Blo 1307972 1309795 := bstep (se 1 (by rfl) ⟨982346, by rfl⟩ : syracuseStep 1309795 = 1964693) B1964693
theorem B1309811 : Blo 1307972 1309811 := bstep (se 1 (by rfl) ⟨982358, by rfl⟩ : syracuseStep 1309811 = 1964717) B1964717
theorem B1309827 : Blo 1307972 1309827 := bstep (se 1 (by rfl) ⟨982370, by rfl⟩ : syracuseStep 1309827 = 1964741) B1964741
theorem B1309843 : Blo 1307972 1309843 := bstep (se 1 (by rfl) ⟨982382, by rfl⟩ : syracuseStep 1309843 = 1964765) B1964765
theorem B2096291 : Blo 1307972 2096291 := bstep (se 1 (by rfl) ⟨1572218, by rfl⟩ : syracuseStep 2096291 = 3144437) B3144437
theorem B1309859 : Blo 1307972 1309859 := bstep (se 1 (by rfl) ⟨982394, by rfl⟩ : syracuseStep 1309859 = 1964789) B1964789
theorem B3538097 : Blo 1307972 3538097 := bstep (se 2 (by rfl) ⟨1326786, by rfl⟩ : syracuseStep 3538097 = 2653573) B2653573
theorem B5307569 : Blo 1307972 5307569 := bstep (se 2 (by rfl) ⟨1990338, by rfl⟩ : syracuseStep 5307569 = 3980677) B3980677
theorem B7077041 : Blo 1307972 7077041 := bstep (se 2 (by rfl) ⟨2653890, by rfl⟩ : syracuseStep 7077041 = 5307781) B5307781
theorem B1309875 : Blo 1307972 1309875 := bstep (se 1 (by rfl) ⟨982406, by rfl⟩ : syracuseStep 1309875 = 1964813) B1964813
theorem B3144899 : Blo 1307972 3144899 := bstep (se 1 (by rfl) ⟨2358674, by rfl⟩ : syracuseStep 3144899 = 4717349) B4717349
theorem B1309891 : Blo 1307972 1309891 := bstep (se 1 (by rfl) ⟨982418, by rfl⟩ : syracuseStep 1309891 = 1964837) B1964837
theorem B1309907 : Blo 1307972 1309907 := bstep (se 1 (by rfl) ⟨982430, by rfl⟩ : syracuseStep 1309907 = 1964861) B1964861
theorem B1309923 : Blo 1307972 1309923 := bstep (se 1 (by rfl) ⟨982442, by rfl⟩ : syracuseStep 1309923 = 1964885) B1964885
theorem B1309939 : Blo 1307972 1309939 := bstep (se 1 (by rfl) ⟨982454, by rfl⟩ : syracuseStep 1309939 = 1964909) B1964909
theorem B1309955 : Blo 1307972 1309955 := bstep (se 1 (by rfl) ⟨982466, by rfl⟩ : syracuseStep 1309955 = 1964933) B1964933
theorem B1309971 : Blo 1307972 1309971 := bstep (se 1 (by rfl) ⟨982478, by rfl⟩ : syracuseStep 1309971 = 1964957) B1964957
theorem B4414769 : Blo 1307972 4414769 := bstep (se 2 (by rfl) ⟨1655538, by rfl⟩ : syracuseStep 4414769 = 3311077) B3311077
theorem B6626609 : Blo 1307972 6626609 := bstep (se 2 (by rfl) ⟨2484978, by rfl⟩ : syracuseStep 6626609 = 4969957) B4969957
theorem B5594467 : Blo 1307972 5594467 := bstep (se 1 (by rfl) ⟨4195850, by rfl⟩ : syracuseStep 5594467 = 8391701) B8391701
theorem B9936269 : Blo 1307972 9936269 := bstep (se 3 (by rfl) ⟨1863050, by rfl⟩ : syracuseStep 9936269 = 3726101) B3726101
theorem B7962083 : Blo 1307972 7962083 := bstep (se 1 (by rfl) ⟨5971562, by rfl⟩ : syracuseStep 7962083 = 11943125) B11943125
theorem B5668387 : Blo 1307972 5668387 := bstep (se 1 (by rfl) ⟨4251290, by rfl⟩ : syracuseStep 5668387 = 8502581) B8502581
theorem B3145283 : Blo 1307972 3145283 := bstep (se 1 (by rfl) ⟨2358962, by rfl⟩ : syracuseStep 3145283 = 4717925) B4717925
theorem B3358307 : Blo 1307972 3358307 := bstep (se 1 (by rfl) ⟨2518730, by rfl⟩ : syracuseStep 3358307 = 5037461) B5037461
theorem B2588401 : Blo 1307972 2588401 := bstep (se 2 (by rfl) ⟨970650, by rfl⟩ : syracuseStep 2588401 = 1941301) B1941301
theorem B4480753 : Blo 1307972 4480753 := bstep (se 2 (by rfl) ⟨1680282, by rfl⟩ : syracuseStep 4480753 = 3360565) B3360565
theorem B4415309 : Blo 1307972 4415309 := bstep (se 3 (by rfl) ⟨827870, by rfl⟩ : syracuseStep 4415309 = 1655741) B1655741
theorem B4972387 : Blo 1307972 4972387 := bstep (se 1 (by rfl) ⟨3729290, by rfl⟩ : syracuseStep 4972387 = 7458581) B7458581
theorem B4415363 : Blo 1307972 4415363 := bstep (se 1 (by rfl) ⟨3311522, by rfl⟩ : syracuseStep 4415363 = 6623045) B6623045
theorem B3727309 : Blo 1307972 3727309 := bstep (se 3 (by rfl) ⟨698870, by rfl⟩ : syracuseStep 3727309 = 1397741) B1397741
theorem B2097137 : Blo 1307972 2097137 := bstep (se 2 (by rfl) ⟨786426, by rfl⟩ : syracuseStep 2097137 = 1572853) B1572853
theorem B2097227 : Blo 1307972 2097227 := bstep (se 1 (by rfl) ⟨1572920, by rfl⟩ : syracuseStep 2097227 = 3145841) B3145841
theorem B4415795 : Blo 1307972 4415795 := bstep (se 1 (by rfl) ⟨3311846, by rfl⟩ : syracuseStep 4415795 = 6623693) B6623693
theorem B1327435 : Blo 1307972 1327435 := bstep (se 1 (by rfl) ⟨995576, by rfl⟩ : syracuseStep 1327435 = 1991153) B1991153
theorem B2654579 : Blo 1307972 2654579 := bstep (se 1 (by rfl) ⟨1990934, by rfl⟩ : syracuseStep 2654579 = 3981869) B3981869
theorem B4252097 : Blo 1307972 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B4416065 : Blo 1307972 4416065 := bstep (se 2 (by rfl) ⟨1656024, by rfl⟩ : syracuseStep 4416065 = 3312049) B3312049
theorem B6627905 : Blo 1307972 6627905 := bstep (se 2 (by rfl) ⟨2485464, by rfl⟩ : syracuseStep 6627905 = 4970929) B4970929
theorem B5587649 : Blo 1307972 5587649 := bstep (se 2 (by rfl) ⟨2095368, by rfl⟩ : syracuseStep 5587649 = 4190737) B4190737
theorem B4719307 : Blo 1307972 4719307 := bstep (se 1 (by rfl) ⟨3539480, by rfl⟩ : syracuseStep 4719307 = 7078961) B7078961
theorem B6718169 : Blo 1307972 6718169 := bstep (se 2 (by rfl) ⟨2519313, by rfl⟩ : syracuseStep 6718169 = 5038627) B5038627
theorem B103383793 : Blo 1307972 103383793 := bstep (se 2 (by rfl) ⟨38768922, by rfl⟩ : syracuseStep 103383793 = 77537845) B77537845
theorem B2360087 : Blo 1307972 2360087 := bstep (se 1 (by rfl) ⟨1770065, by rfl⟩ : syracuseStep 2360087 = 3540131) B3540131
theorem B10617635 : Blo 1307972 10617635 := bstep (se 1 (by rfl) ⟨7963226, by rfl⟩ : syracuseStep 10617635 = 15926453) B15926453
theorem B8389469 : Blo 1307972 8389469 := bstep (se 3 (by rfl) ⟨1573025, by rfl⟩ : syracuseStep 8389469 = 3146051) B3146051
theorem B4719539 : Blo 1307972 4719539 := bstep (se 1 (by rfl) ⟨3539654, by rfl⟩ : syracuseStep 4719539 = 7079309) B7079309
theorem B5587991 : Blo 1307972 5587991 := bstep (se 1 (by rfl) ⟨4190993, by rfl⟩ : syracuseStep 5587991 = 8381987) B8381987
theorem B25150499 : Blo 1307972 25150499 := bstep (se 1 (by rfl) ⟨18862874, by rfl⟩ : syracuseStep 25150499 = 37725749) B37725749
theorem B7562285 : Blo 1307972 7562285 := bstep (se 3 (by rfl) ⟨1417928, by rfl⟩ : syracuseStep 7562285 = 2835857) B2835857
theorem B4973633 : Blo 1307972 4973633 := bstep (se 2 (by rfl) ⟨1865112, by rfl⟩ : syracuseStep 4973633 = 3730225) B3730225
theorem B4416605 : Blo 1307972 4416605 := bstep (se 3 (by rfl) ⟨828113, by rfl⟩ : syracuseStep 4416605 = 1656227) B1656227
theorem B1655959 : Blo 1307972 1655959 := bstep (se 1 (by rfl) ⟨1241969, by rfl⟩ : syracuseStep 1655959 = 2483939) B2483939
theorem B13804805 : Blo 1307972 13804805 := bstep (se 4 (by rfl) ⟨1294200, by rfl⟩ : syracuseStep 13804805 = 2588401) B2588401
theorem B3311027 : Blo 1307972 3311027 := bstep (se 1 (by rfl) ⟨2483270, by rfl⟩ : syracuseStep 3311027 = 4966541) B4966541
theorem B2483635 : Blo 1307972 2483635 := bstep (se 1 (by rfl) ⟨1862726, by rfl⟩ : syracuseStep 2483635 = 3725453) B3725453
theorem B217933253 : Blo 1307972 217933253 := bstep (se 4 (by rfl) ⟨20431242, by rfl⟩ : syracuseStep 217933253 = 40862485) B40862485
theorem B10610137 : Blo 1307972 10610137 := bstep (se 2 (by rfl) ⟨3978801, by rfl⟩ : syracuseStep 10610137 = 7957603) B7957603
theorem B8955485 : Blo 1307972 8955485 := bstep (se 3 (by rfl) ⟨1679153, by rfl⟩ : syracuseStep 8955485 = 3358307) B3358307
theorem B7079525 : Blo 1307972 7079525 := bstep (se 4 (by rfl) ⟨663705, by rfl⟩ : syracuseStep 7079525 = 1327411) B1327411
theorem B2795123 : Blo 1307972 2795123 := bstep (se 1 (by rfl) ⟨2096342, by rfl⟩ : syracuseStep 2795123 = 4192685) B4192685
theorem B4196119 : Blo 1307972 4196119 := bstep (se 1 (by rfl) ⟨3147089, by rfl⟩ : syracuseStep 4196119 = 6294179) B6294179
theorem B2484083 : Blo 1307972 2484083 := bstep (se 1 (by rfl) ⟨1863062, by rfl⟩ : syracuseStep 2484083 = 3726125) B3726125
theorem B2484121 : Blo 1307972 2484121 := bstep (se 2 (by rfl) ⟨931545, by rfl⟩ : syracuseStep 2484121 = 1863091) B1863091
theorem B3311563 : Blo 1307972 3311563 := bstep (se 1 (by rfl) ⟨2483672, by rfl⟩ : syracuseStep 3311563 = 4967345) B4967345
theorem B4196299 : Blo 1307972 4196299 := bstep (se 1 (by rfl) ⟨3147224, by rfl⟩ : syracuseStep 4196299 = 6294449) B6294449
theorem B2942963 : Blo 1307972 2942963 := bstep (se 1 (by rfl) ⟨2207222, by rfl⟩ : syracuseStep 2942963 = 4414445) B4414445
theorem B2942999 : Blo 1307972 2942999 := bstep (se 1 (by rfl) ⟨2207249, by rfl⟩ : syracuseStep 2942999 = 4414499) B4414499
theorem B4196375 : Blo 1307972 4196375 := bstep (se 1 (by rfl) ⟨3147281, by rfl⟩ : syracuseStep 4196375 = 6294563) B6294563
theorem B4720691 : Blo 1307972 4720691 := bstep (se 1 (by rfl) ⟨3540518, by rfl⟩ : syracuseStep 4720691 = 7081037) B7081037
theorem B6285377 : Blo 1307972 6285377 := bstep (se 2 (by rfl) ⟨2357016, by rfl⟩ : syracuseStep 6285377 = 4714033) B4714033
theorem B3729473 : Blo 1307972 3729473 := bstep (se 2 (by rfl) ⟨1398552, by rfl⟩ : syracuseStep 3729473 = 2797105) B2797105
theorem B3311705 : Blo 1307972 3311705 := bstep (se 2 (by rfl) ⟨1241889, by rfl⟩ : syracuseStep 3311705 = 2483779) B2483779
theorem B12585091 : Blo 1307972 12585091 := bstep (se 1 (by rfl) ⟨9438818, by rfl⟩ : syracuseStep 12585091 = 18877637) B18877637
theorem B2943179 : Blo 1307972 2943179 := bstep (se 1 (by rfl) ⟨2207384, by rfl⟩ : syracuseStep 2943179 = 4414769) B4414769
theorem B5376203 : Blo 1307972 5376203 := bstep (se 1 (by rfl) ⟨4032152, by rfl⟩ : syracuseStep 5376203 = 8064305) B8064305
theorem B4417739 : Blo 1307972 4417739 := bstep (se 1 (by rfl) ⟨3313304, by rfl⟩ : syracuseStep 4417739 = 6626609) B6626609
theorem B6285529 : Blo 1307972 6285529 := bstep (se 2 (by rfl) ⟨2357073, by rfl⟩ : syracuseStep 6285529 = 4714147) B4714147
theorem B4196569 : Blo 1307972 4196569 := bstep (se 2 (by rfl) ⟨1573713, by rfl⟩ : syracuseStep 4196569 = 3147427) B3147427
theorem B2943233 : Blo 1307972 2943233 := bstep (se 2 (by rfl) ⟨1103712, by rfl⟩ : syracuseStep 2943233 = 2207425) B2207425
theorem B5974337 : Blo 1307972 5974337 := bstep (se 2 (by rfl) ⟨2240376, by rfl⟩ : syracuseStep 5974337 = 4480753) B4480753
theorem B2484569 : Blo 1307972 2484569 := bstep (se 2 (by rfl) ⟨931713, by rfl⟩ : syracuseStep 2484569 = 1863427) B1863427
theorem B4966829 : Blo 1307972 4966829 := bstep (se 3 (by rfl) ⟨931280, by rfl⟩ : syracuseStep 4966829 = 1862561) B1862561
theorem B4966859 : Blo 1307972 4966859 := bstep (se 1 (by rfl) ⟨3725144, by rfl⟩ : syracuseStep 4966859 = 7450289) B7450289
theorem B7072217 : Blo 1307972 7072217 := bstep (se 2 (by rfl) ⟨2652081, by rfl⟩ : syracuseStep 7072217 = 5304163) B5304163
theorem B2943449 : Blo 1307972 2943449 := bstep (se 2 (by rfl) ⟨1103793, by rfl⟩ : syracuseStep 2943449 = 2207587) B2207587
theorem B4418009 : Blo 1307972 4418009 := bstep (se 2 (by rfl) ⟨1656753, by rfl⟩ : syracuseStep 4418009 = 3313507) B3313507
theorem B6629849 : Blo 1307972 6629849 := bstep (se 2 (by rfl) ⟨2486193, by rfl⟩ : syracuseStep 6629849 = 4972387) B4972387
theorem B2943539 : Blo 1307972 2943539 := bstep (se 1 (by rfl) ⟨2207654, by rfl⟩ : syracuseStep 2943539 = 4415309) B4415309
theorem B2943575 : Blo 1307972 2943575 := bstep (se 1 (by rfl) ⟨2207681, by rfl⟩ : syracuseStep 2943575 = 4415363) B4415363
theorem B3730009 : Blo 1307972 3730009 := bstep (se 2 (by rfl) ⟨1398753, by rfl⟩ : syracuseStep 3730009 = 2797507) B2797507
theorem B2943755 : Blo 1307972 2943755 := bstep (se 1 (by rfl) ⟨2207816, by rfl⟩ : syracuseStep 2943755 = 4415633) B4415633
theorem B2943809 : Blo 1307972 2943809 := bstep (se 2 (by rfl) ⟨1103928, by rfl⟩ : syracuseStep 2943809 = 2207857) B2207857
theorem B1657675 : Blo 1307972 1657675 := bstep (se 1 (by rfl) ⟨1243256, by rfl⟩ : syracuseStep 1657675 = 2486513) B2486513
theorem B30231397 : Blo 1307972 30231397 := bstep (se 4 (by rfl) ⟨2834193, by rfl⟩ : syracuseStep 30231397 = 5668387) B5668387
theorem B3312535 : Blo 1307972 3312535 := bstep (se 1 (by rfl) ⟨2484401, by rfl⟩ : syracuseStep 3312535 = 4968803) B4968803
theorem B2796439 : Blo 1307972 2796439 := bstep (se 1 (by rfl) ⟨2097329, by rfl⟩ : syracuseStep 2796439 = 4194659) B4194659
theorem B2984897 : Blo 1307972 2984897 := bstep (se 2 (by rfl) ⟨1119336, by rfl⟩ : syracuseStep 2984897 = 2238673) B2238673
theorem B2944025 : Blo 1307972 2944025 := bstep (se 2 (by rfl) ⟨1104009, by rfl⟩ : syracuseStep 2944025 = 2208019) B2208019
theorem B8391725 : Blo 1307972 8391725 := bstep (se 3 (by rfl) ⟨1573448, by rfl⟩ : syracuseStep 8391725 = 3146897) B3146897
theorem B2485313 : Blo 1307972 2485313 := bstep (se 2 (by rfl) ⟨931992, by rfl⟩ : syracuseStep 2485313 = 1863985) B1863985
theorem B5041217 : Blo 1307972 5041217 := bstep (se 2 (by rfl) ⟨1890456, by rfl⟩ : syracuseStep 5041217 = 3780913) B3780913
theorem B2796619 : Blo 1307972 2796619 := bstep (se 1 (by rfl) ⟨2097464, by rfl⟩ : syracuseStep 2796619 = 4194929) B4194929
theorem B4967513 : Blo 1307972 4967513 := bstep (se 2 (by rfl) ⟨1862817, by rfl⟩ : syracuseStep 4967513 = 3725635) B3725635
theorem B5590109 : Blo 1307972 5590109 := bstep (se 3 (by rfl) ⟨1048145, by rfl⟩ : syracuseStep 5590109 = 2096291) B2096291
theorem B2944115 : Blo 1307972 2944115 := bstep (se 1 (by rfl) ⟨2208086, by rfl⟩ : syracuseStep 2944115 = 4416173) B4416173
theorem B2944151 : Blo 1307972 2944151 := bstep (se 1 (by rfl) ⟨2208113, by rfl⟩ : syracuseStep 2944151 = 4416227) B4416227
theorem B4418711 : Blo 1307972 4418711 := bstep (se 1 (by rfl) ⟨3314033, by rfl⟩ : syracuseStep 4418711 = 6628067) B6628067
theorem B2796695 : Blo 1307972 2796695 := bstep (se 1 (by rfl) ⟨2097521, by rfl⟩ : syracuseStep 2796695 = 4195043) B4195043
theorem B2944331 : Blo 1307972 2944331 := bstep (se 1 (by rfl) ⟨2208248, by rfl⟩ : syracuseStep 2944331 = 4416497) B4416497
theorem B3312971 : Blo 1307972 3312971 := bstep (se 1 (by rfl) ⟨2484728, by rfl⟩ : syracuseStep 3312971 = 4969457) B4969457
theorem B2485579 : Blo 1307972 2485579 := bstep (se 1 (by rfl) ⟨1864184, by rfl⟩ : syracuseStep 2485579 = 3728369) B3728369
theorem B2944385 : Blo 1307972 2944385 := bstep (se 2 (by rfl) ⟨1104144, by rfl⟩ : syracuseStep 2944385 = 2208289) B2208289
theorem B5590417 : Blo 1307972 5590417 := bstep (se 2 (by rfl) ⟨2096406, by rfl⟩ : syracuseStep 5590417 = 4192813) B4192813
theorem B4967831 : Blo 1307972 4967831 := bstep (se 1 (by rfl) ⟨3725873, by rfl⟩ : syracuseStep 4967831 = 7451747) B7451747
theorem B5590451 : Blo 1307972 5590451 := bstep (se 1 (by rfl) ⟨4192838, by rfl⟩ : syracuseStep 5590451 = 8385677) B8385677
theorem B2207243 : Blo 1307972 2207243 := bstep (se 1 (by rfl) ⟨1655432, by rfl⟩ : syracuseStep 2207243 = 3310865) B3310865
theorem B2944601 : Blo 1307972 2944601 := bstep (se 2 (by rfl) ⟨1104225, by rfl⟩ : syracuseStep 2944601 = 2208451) B2208451
theorem B2207371 : Blo 1307972 2207371 := bstep (se 1 (by rfl) ⟨1655528, by rfl⟩ : syracuseStep 2207371 = 3311057) B3311057
theorem B1863319 : Blo 1307972 1863319 := bstep (se 1 (by rfl) ⟨1397489, by rfl⟩ : syracuseStep 1863319 = 2794979) B2794979
theorem B2944691 : Blo 1307972 2944691 := bstep (se 1 (by rfl) ⟨2208518, by rfl⟩ : syracuseStep 2944691 = 4417037) B4417037
theorem B4419251 : Blo 1307972 4419251 := bstep (se 1 (by rfl) ⟨3314438, by rfl⟩ : syracuseStep 4419251 = 6628877) B6628877
theorem B3313345 : Blo 1307972 3313345 := bstep (se 2 (by rfl) ⟨1242504, by rfl⟩ : syracuseStep 3313345 = 2485009) B2485009
theorem B183815885 : Blo 1307972 183815885 := bstep (se 3 (by rfl) ⟨34465478, by rfl⟩ : syracuseStep 183815885 = 68930957) B68930957
theorem B2944727 : Blo 1307972 2944727 := bstep (se 1 (by rfl) ⟨2208545, by rfl⟩ : syracuseStep 2944727 = 4417091) B4417091
theorem B2486027 : Blo 1307972 2486027 := bstep (se 1 (by rfl) ⟨1864520, by rfl⟩ : syracuseStep 2486027 = 3729041) B3729041
theorem B2952983 : Blo 1307972 2952983 := bstep (se 1 (by rfl) ⟨2214737, by rfl⟩ : syracuseStep 2952983 = 4429475) B4429475
theorem B2207513 : Blo 1307972 2207513 := bstep (se 2 (by rfl) ⟨827817, by rfl⟩ : syracuseStep 2207513 = 1655635) B1655635
theorem B14905133 : Blo 1307972 14905133 := bstep (se 3 (by rfl) ⟨2794712, by rfl⟩ : syracuseStep 14905133 = 5589425) B5589425
theorem B2944907 : Blo 1307972 2944907 := bstep (se 1 (by rfl) ⟨2208680, by rfl⟩ : syracuseStep 2944907 = 4417361) B4417361
theorem B2207641 : Blo 1307972 2207641 := bstep (se 2 (by rfl) ⟨827865, by rfl⟩ : syracuseStep 2207641 = 1655731) B1655731
theorem B2944961 : Blo 1307972 2944961 := bstep (se 2 (by rfl) ⟨1104360, by rfl⟩ : syracuseStep 2944961 = 2208721) B2208721
theorem B4419521 : Blo 1307972 4419521 := bstep (se 2 (by rfl) ⟨1657320, by rfl⟩ : syracuseStep 4419521 = 3314641) B3314641
theorem B2486209 : Blo 1307972 2486209 := bstep (se 2 (by rfl) ⟨932328, by rfl⟩ : syracuseStep 2486209 = 1864657) B1864657
theorem B6631469 : Blo 1307972 6631469 := bstep (se 3 (by rfl) ⟨1243400, by rfl⟩ : syracuseStep 6631469 = 2486801) B2486801
theorem B4968499 : Blo 1307972 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B20156485 : Blo 1307972 20156485 := bstep (se 4 (by rfl) ⟨1889670, by rfl⟩ : syracuseStep 20156485 = 3779341) B3779341
theorem B1962059 : Blo 1307972 1962059 := bstep (se 1 (by rfl) ⟨1471544, by rfl⟩ : syracuseStep 1962059 = 2943089) B2943089
theorem B1962071 : Blo 1307972 1962071 := bstep (se 1 (by rfl) ⟨1471553, by rfl⟩ : syracuseStep 1962071 = 2943107) B2943107
theorem B1962137 : Blo 1307972 1962137 := bstep (se 2 (by rfl) ⟨735801, by rfl⟩ : syracuseStep 1962137 = 1471603) B1471603
theorem B2945177 : Blo 1307972 2945177 := bstep (se 2 (by rfl) ⟨1104441, by rfl⟩ : syracuseStep 2945177 = 2208883) B2208883
theorem B4190429 : Blo 1307972 4190429 := bstep (se 3 (by rfl) ⟨785705, by rfl⟩ : syracuseStep 4190429 = 1571411) B1571411
theorem B2945267 : Blo 1307972 2945267 := bstep (se 1 (by rfl) ⟨2208950, by rfl⟩ : syracuseStep 2945267 = 4417901) B4417901
theorem B1962251 : Blo 1307972 1962251 := bstep (se 1 (by rfl) ⟨1471688, by rfl⟩ : syracuseStep 1962251 = 2943377) B2943377
theorem B1962263 : Blo 1307972 1962263 := bstep (se 1 (by rfl) ⟨1471697, by rfl⟩ : syracuseStep 1962263 = 2943395) B2943395
theorem B2945303 : Blo 1307972 2945303 := bstep (se 1 (by rfl) ⟨2208977, by rfl⟩ : syracuseStep 2945303 = 4417955) B4417955
theorem B3313943 : Blo 1307972 3313943 := bstep (se 1 (by rfl) ⟨2485457, by rfl⟩ : syracuseStep 3313943 = 4970915) B4970915
theorem B2486551 : Blo 1307972 2486551 := bstep (se 1 (by rfl) ⟨1864913, by rfl⟩ : syracuseStep 2486551 = 3729827) B3729827
theorem B1962329 : Blo 1307972 1962329 := bstep (se 2 (by rfl) ⟨735873, by rfl⟩ : syracuseStep 1962329 = 1471747) B1471747
theorem B7450973 : Blo 1307972 7450973 := bstep (se 3 (by rfl) ⟨1397057, by rfl⟩ : syracuseStep 7450973 = 2794115) B2794115
theorem B10621363 : Blo 1307972 10621363 := bstep (se 1 (by rfl) ⟨7966022, by rfl⟩ : syracuseStep 10621363 = 15932045) B15932045
theorem B1962443 : Blo 1307972 1962443 := bstep (se 1 (by rfl) ⟨1471832, by rfl⟩ : syracuseStep 1962443 = 2943665) B2943665
theorem B2945483 : Blo 1307972 2945483 := bstep (se 1 (by rfl) ⟨2209112, by rfl⟩ : syracuseStep 2945483 = 4418225) B4418225
theorem B1962455 : Blo 1307972 1962455 := bstep (se 1 (by rfl) ⟨1471841, by rfl⟩ : syracuseStep 1962455 = 2943683) B2943683
theorem B2208215 : Blo 1307972 2208215 := bstep (se 1 (by rfl) ⟨1656161, by rfl⟩ : syracuseStep 2208215 = 3312323) B3312323
theorem B7459289 : Blo 1307972 7459289 := bstep (se 2 (by rfl) ⟨2797233, by rfl⟩ : syracuseStep 7459289 = 5594467) B5594467
theorem B4420061 : Blo 1307972 4420061 := bstep (se 3 (by rfl) ⟨828761, by rfl⟩ : syracuseStep 4420061 = 1657523) B1657523
theorem B2486771 : Blo 1307972 2486771 := bstep (se 1 (by rfl) ⟨1865078, by rfl⟩ : syracuseStep 2486771 = 3730157) B3730157
theorem B2945537 : Blo 1307972 2945537 := bstep (se 2 (by rfl) ⟨1104576, by rfl⟩ : syracuseStep 2945537 = 2209153) B2209153
theorem B1962521 : Blo 1307972 1962521 := bstep (se 2 (by rfl) ⟨735945, by rfl⟩ : syracuseStep 1962521 = 1471891) B1471891
theorem B2208343 : Blo 1307972 2208343 := bstep (se 1 (by rfl) ⟨1656257, by rfl⟩ : syracuseStep 2208343 = 3312515) B3312515
theorem B1962635 : Blo 1307972 1962635 := bstep (se 1 (by rfl) ⟨1471976, by rfl⟩ : syracuseStep 1962635 = 2943953) B2943953
theorem B1962647 : Blo 1307972 1962647 := bstep (se 1 (by rfl) ⟨1471985, by rfl⟩ : syracuseStep 1962647 = 2943971) B2943971
theorem B11178647 : Blo 1307972 11178647 := bstep (se 1 (by rfl) ⟨8383985, by rfl⟩ : syracuseStep 11178647 = 16767971) B16767971
theorem B43037381 : Blo 1307972 43037381 := bstep (se 4 (by rfl) ⟨4034754, by rfl⟩ : syracuseStep 43037381 = 8069509) B8069509
theorem B1962713 : Blo 1307972 1962713 := bstep (se 2 (by rfl) ⟨736017, by rfl⟩ : syracuseStep 1962713 = 1472035) B1472035
theorem B2945753 : Blo 1307972 2945753 := bstep (se 2 (by rfl) ⟨1104657, by rfl⟩ : syracuseStep 2945753 = 2209315) B2209315
theorem B6624017 : Blo 1307972 6624017 := bstep (se 2 (by rfl) ⟨2484006, by rfl⟩ : syracuseStep 6624017 = 4968013) B4968013
theorem B2945843 : Blo 1307972 2945843 := bstep (se 1 (by rfl) ⟨2209382, by rfl⟩ : syracuseStep 2945843 = 4418765) B4418765
theorem B1962827 : Blo 1307972 1962827 := bstep (se 1 (by rfl) ⟨1472120, by rfl⟩ : syracuseStep 1962827 = 2944241) B2944241
theorem B1962839 : Blo 1307972 1962839 := bstep (se 1 (by rfl) ⟨1472129, by rfl⟩ : syracuseStep 1962839 = 2944259) B2944259
theorem B2945879 : Blo 1307972 2945879 := bstep (se 1 (by rfl) ⟨2209409, by rfl⟩ : syracuseStep 2945879 = 4418819) B4418819
theorem B1962905 : Blo 1307972 1962905 := bstep (se 2 (by rfl) ⟨736089, by rfl⟩ : syracuseStep 1962905 = 1472179) B1472179
theorem B6624179 : Blo 1307972 6624179 := bstep (se 1 (by rfl) ⟨4968134, by rfl⟩ : syracuseStep 6624179 = 9936269) B9936269
theorem B1963019 : Blo 1307972 1963019 := bstep (se 1 (by rfl) ⟨1472264, by rfl⟩ : syracuseStep 1963019 = 2944529) B2944529
theorem B2946059 : Blo 1307972 2946059 := bstep (se 1 (by rfl) ⟨2209544, by rfl⟩ : syracuseStep 2946059 = 4419089) B4419089
theorem B7173137 : Blo 1307972 7173137 := bstep (se 2 (by rfl) ⟨2689926, by rfl⟩ : syracuseStep 7173137 = 5379853) B5379853
theorem B1963031 : Blo 1307972 1963031 := bstep (se 1 (by rfl) ⟨1472273, by rfl⟩ : syracuseStep 1963031 = 2944547) B2944547
theorem B1471531 : Blo 1307972 1471531 := bstep (se 1 (by rfl) ⟨1103648, by rfl⟩ : syracuseStep 1471531 = 2207297) B2207297
theorem B2946113 : Blo 1307972 2946113 := bstep (se 2 (by rfl) ⟨1104792, by rfl⟩ : syracuseStep 2946113 = 2209585) B2209585
theorem B3314753 : Blo 1307972 3314753 := bstep (se 2 (by rfl) ⟨1243032, by rfl⟩ : syracuseStep 3314753 = 2486065) B2486065
theorem B1963097 : Blo 1307972 1963097 := bstep (se 2 (by rfl) ⟨736161, by rfl⟩ : syracuseStep 1963097 = 1472323) B1472323
theorem B1471639 : Blo 1307972 1471639 := bstep (se 1 (by rfl) ⟨1103729, by rfl⟩ : syracuseStep 1471639 = 2207459) B2207459
theorem B1963211 : Blo 1307972 1963211 := bstep (se 1 (by rfl) ⟨1472408, by rfl⟩ : syracuseStep 1963211 = 2944817) B2944817
theorem B2208971 : Blo 1307972 2208971 := bstep (se 1 (by rfl) ⟨1656728, by rfl⟩ : syracuseStep 2208971 = 3313457) B3313457
theorem B1963223 : Blo 1307972 1963223 := bstep (se 1 (by rfl) ⟨1472417, by rfl⟩ : syracuseStep 1963223 = 2944835) B2944835
theorem B4969745 : Blo 1307972 4969745 := bstep (se 2 (by rfl) ⟨1863654, by rfl⟩ : syracuseStep 4969745 = 3727309) B3727309
theorem B1963289 : Blo 1307972 1963289 := bstep (se 2 (by rfl) ⟨736233, by rfl⟩ : syracuseStep 1963289 = 1472467) B1472467
theorem B2946329 : Blo 1307972 2946329 := bstep (se 2 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 2946329 = 2209747) B2209747
theorem B5592365 : Blo 1307972 5592365 := bstep (se 3 (by rfl) ⟨1048568, by rfl⟩ : syracuseStep 5592365 = 2097137) B2097137
theorem B1307979 : Blo 1307972 1307979 := bstep (se 1 (by rfl) ⟨980984, by rfl⟩ : syracuseStep 1307979 = 1961969) B1961969
theorem B1471819 : Blo 1307972 1471819 := bstep (se 1 (by rfl) ⟨1103864, by rfl⟩ : syracuseStep 1471819 = 2207729) B2207729
theorem B2209099 : Blo 1307972 2209099 := bstep (se 1 (by rfl) ⟨1656824, by rfl⟩ : syracuseStep 2209099 = 3313649) B3313649
theorem B1307991 : Blo 1307972 1307991 := bstep (se 1 (by rfl) ⟨980993, by rfl⟩ : syracuseStep 1307991 = 1961987) B1961987
theorem B1308011 : Blo 1307972 1308011 := bstep (se 1 (by rfl) ⟨981008, by rfl⟩ : syracuseStep 1308011 = 1962017) B1962017
theorem B2946419 : Blo 1307972 2946419 := bstep (se 1 (by rfl) ⟨2209814, by rfl⟩ : syracuseStep 2946419 = 4419629) B4419629
theorem B1308023 : Blo 1307972 1308023 := bstep (se 1 (by rfl) ⟨981017, by rfl⟩ : syracuseStep 1308023 = 1962035) B1962035
theorem B1308043 : Blo 1307972 1308043 := bstep (se 1 (by rfl) ⟨981032, by rfl⟩ : syracuseStep 1308043 = 1962065) B1962065
theorem B1963403 : Blo 1307972 1963403 := bstep (se 1 (by rfl) ⟨1472552, by rfl⟩ : syracuseStep 1963403 = 2945105) B2945105
theorem B1308055 : Blo 1307972 1308055 := bstep (se 1 (by rfl) ⟨981041, by rfl⟩ : syracuseStep 1308055 = 1962083) B1962083
theorem B1963415 : Blo 1307972 1963415 := bstep (se 1 (by rfl) ⟨1472561, by rfl⟩ : syracuseStep 1963415 = 2945123) B2945123
theorem B2946455 : Blo 1307972 2946455 := bstep (se 1 (by rfl) ⟨2209841, by rfl⟩ : syracuseStep 2946455 = 4419683) B4419683
theorem B1308075 : Blo 1307972 1308075 := bstep (se 1 (by rfl) ⟨981056, by rfl⟩ : syracuseStep 1308075 = 1962113) B1962113
theorem B1308087 : Blo 1307972 1308087 := bstep (se 1 (by rfl) ⟨981065, by rfl⟩ : syracuseStep 1308087 = 1962131) B1962131
theorem B1471927 : Blo 1307972 1471927 := bstep (se 1 (by rfl) ⟨1103945, by rfl⟩ : syracuseStep 1471927 = 2207891) B2207891
theorem B1308107 : Blo 1307972 1308107 := bstep (se 1 (by rfl) ⟨981080, by rfl⟩ : syracuseStep 1308107 = 1962161) B1962161
theorem B1308119 : Blo 1307972 1308119 := bstep (se 1 (by rfl) ⟨981089, by rfl⟩ : syracuseStep 1308119 = 1962179) B1962179
theorem B3143129 : Blo 1307972 3143129 := bstep (se 2 (by rfl) ⟨1178673, by rfl⟩ : syracuseStep 3143129 = 2357347) B2357347
theorem B1963481 : Blo 1307972 1963481 := bstep (se 2 (by rfl) ⟨736305, by rfl⟩ : syracuseStep 1963481 = 1472611) B1472611
theorem B2209241 : Blo 1307972 2209241 := bstep (se 2 (by rfl) ⟨828465, by rfl⟩ : syracuseStep 2209241 = 1656931) B1656931
theorem B1308139 : Blo 1307972 1308139 := bstep (se 1 (by rfl) ⟨981104, by rfl⟩ : syracuseStep 1308139 = 1962209) B1962209
theorem B1308151 : Blo 1307972 1308151 := bstep (se 1 (by rfl) ⟨981113, by rfl⟩ : syracuseStep 1308151 = 1962227) B1962227
theorem B1308171 : Blo 1307972 1308171 := bstep (se 1 (by rfl) ⟨981128, by rfl⟩ : syracuseStep 1308171 = 1962257) B1962257
theorem B1308183 : Blo 1307972 1308183 := bstep (se 1 (by rfl) ⟨981137, by rfl⟩ : syracuseStep 1308183 = 1962275) B1962275
theorem B1308203 : Blo 1307972 1308203 := bstep (se 1 (by rfl) ⟨981152, by rfl⟩ : syracuseStep 1308203 = 1962305) B1962305
theorem B1308215 : Blo 1307972 1308215 := bstep (se 1 (by rfl) ⟨981161, by rfl⟩ : syracuseStep 1308215 = 1962323) B1962323
theorem B1308235 : Blo 1307972 1308235 := bstep (se 1 (by rfl) ⟨981176, by rfl⟩ : syracuseStep 1308235 = 1962353) B1962353
theorem B1963595 : Blo 1307972 1963595 := bstep (se 1 (by rfl) ⟨1472696, by rfl⟩ : syracuseStep 1963595 = 2945393) B2945393
theorem B2946635 : Blo 1307972 2946635 := bstep (se 1 (by rfl) ⟨2209976, by rfl⟩ : syracuseStep 2946635 = 4419953) B4419953
theorem B1308247 : Blo 1307972 1308247 := bstep (se 1 (by rfl) ⟨981185, by rfl⟩ : syracuseStep 1308247 = 1962371) B1962371
theorem B1963607 : Blo 1307972 1963607 := bstep (se 1 (by rfl) ⟨1472705, by rfl⟩ : syracuseStep 1963607 = 2945411) B2945411
theorem B2209369 : Blo 1307972 2209369 := bstep (se 2 (by rfl) ⟨828513, by rfl⟩ : syracuseStep 2209369 = 1657027) B1657027
theorem B3315289 : Blo 1307972 3315289 := bstep (se 2 (by rfl) ⟨1243233, by rfl⟩ : syracuseStep 3315289 = 2486467) B2486467
theorem B1308267 : Blo 1307972 1308267 := bstep (se 1 (by rfl) ⟨981200, by rfl⟩ : syracuseStep 1308267 = 1962401) B1962401
theorem B1472107 : Blo 1307972 1472107 := bstep (se 1 (by rfl) ⟨1104080, by rfl⟩ : syracuseStep 1472107 = 2208161) B2208161
theorem B1308279 : Blo 1307972 1308279 := bstep (se 1 (by rfl) ⟨981209, by rfl⟩ : syracuseStep 1308279 = 1962419) B1962419
theorem B2946689 : Blo 1307972 2946689 := bstep (se 2 (by rfl) ⟨1105008, by rfl⟩ : syracuseStep 2946689 = 2210017) B2210017
theorem B1308299 : Blo 1307972 1308299 := bstep (se 1 (by rfl) ⟨981224, by rfl⟩ : syracuseStep 1308299 = 1962449) B1962449
theorem B1308311 : Blo 1307972 1308311 := bstep (se 1 (by rfl) ⟨981233, by rfl⟩ : syracuseStep 1308311 = 1962467) B1962467
theorem B1963673 : Blo 1307972 1963673 := bstep (se 2 (by rfl) ⟨736377, by rfl⟩ : syracuseStep 1963673 = 1472755) B1472755
theorem B1308331 : Blo 1307972 1308331 := bstep (se 1 (by rfl) ⟨981248, by rfl⟩ : syracuseStep 1308331 = 1962497) B1962497
theorem B1308343 : Blo 1307972 1308343 := bstep (se 1 (by rfl) ⟨981257, by rfl⟩ : syracuseStep 1308343 = 1962515) B1962515
theorem B1308363 : Blo 1307972 1308363 := bstep (se 1 (by rfl) ⟨981272, by rfl⟩ : syracuseStep 1308363 = 1962545) B1962545
theorem B1308375 : Blo 1307972 1308375 := bstep (se 1 (by rfl) ⟨981281, by rfl⟩ : syracuseStep 1308375 = 1962563) B1962563
theorem B1472215 : Blo 1307972 1472215 := bstep (se 1 (by rfl) ⟨1104161, by rfl⟩ : syracuseStep 1472215 = 2208323) B2208323
theorem B1308395 : Blo 1307972 1308395 := bstep (se 1 (by rfl) ⟨981296, by rfl⟩ : syracuseStep 1308395 = 1962593) B1962593
theorem B1308407 : Blo 1307972 1308407 := bstep (se 1 (by rfl) ⟨981305, by rfl⟩ : syracuseStep 1308407 = 1962611) B1962611
theorem B1308427 : Blo 1307972 1308427 := bstep (se 1 (by rfl) ⟨981320, by rfl⟩ : syracuseStep 1308427 = 1962641) B1962641
theorem B1963787 : Blo 1307972 1963787 := bstep (se 1 (by rfl) ⟨1472840, by rfl⟩ : syracuseStep 1963787 = 2945681) B2945681
theorem B1308439 : Blo 1307972 1308439 := bstep (se 1 (by rfl) ⟨981329, by rfl⟩ : syracuseStep 1308439 = 1962659) B1962659
theorem B1963799 : Blo 1307972 1963799 := bstep (se 1 (by rfl) ⟨1472849, by rfl⟩ : syracuseStep 1963799 = 2945699) B2945699
theorem B1308459 : Blo 1307972 1308459 := bstep (se 1 (by rfl) ⟨981344, by rfl⟩ : syracuseStep 1308459 = 1962689) B1962689
theorem B1308471 : Blo 1307972 1308471 := bstep (se 1 (by rfl) ⟨981353, by rfl⟩ : syracuseStep 1308471 = 1962707) B1962707
theorem B1398583 : Blo 1307972 1398583 := bstep (se 1 (by rfl) ⟨1048937, by rfl⟩ : syracuseStep 1398583 = 2097875) B2097875
theorem B1308491 : Blo 1307972 1308491 := bstep (se 1 (by rfl) ⟨981368, by rfl⟩ : syracuseStep 1308491 = 1962737) B1962737
theorem B1308503 : Blo 1307972 1308503 := bstep (se 1 (by rfl) ⟨981377, by rfl⟩ : syracuseStep 1308503 = 1962755) B1962755
theorem B1963865 : Blo 1307972 1963865 := bstep (se 2 (by rfl) ⟨736449, by rfl⟩ : syracuseStep 1963865 = 1472899) B1472899
theorem B2946905 : Blo 1307972 2946905 := bstep (se 2 (by rfl) ⟨1105089, by rfl⟩ : syracuseStep 2946905 = 2210179) B2210179
theorem B1308523 : Blo 1307972 1308523 := bstep (se 1 (by rfl) ⟨981392, by rfl⟩ : syracuseStep 1308523 = 1962785) B1962785
theorem B1308535 : Blo 1307972 1308535 := bstep (se 1 (by rfl) ⟨981401, by rfl⟩ : syracuseStep 1308535 = 1962803) B1962803
theorem B1308555 : Blo 1307972 1308555 := bstep (se 1 (by rfl) ⟨981416, by rfl⟩ : syracuseStep 1308555 = 1962833) B1962833
theorem B1472395 : Blo 1307972 1472395 := bstep (se 1 (by rfl) ⟨1104296, by rfl⟩ : syracuseStep 1472395 = 2208593) B2208593
theorem B1308567 : Blo 1307972 1308567 := bstep (se 1 (by rfl) ⟨981425, by rfl⟩ : syracuseStep 1308567 = 1962851) B1962851
theorem B1308587 : Blo 1307972 1308587 := bstep (se 1 (by rfl) ⟨981440, by rfl⟩ : syracuseStep 1308587 = 1962881) B1962881
theorem B11188145 : Blo 1307972 11188145 := bstep (se 2 (by rfl) ⟨4195554, by rfl⟩ : syracuseStep 11188145 = 8391109) B8391109
theorem B2946995 : Blo 1307972 2946995 := bstep (se 1 (by rfl) ⟨2210246, by rfl⟩ : syracuseStep 2946995 = 4420493) B4420493
theorem B1308599 : Blo 1307972 1308599 := bstep (se 1 (by rfl) ⟨981449, by rfl⟩ : syracuseStep 1308599 = 1962899) B1962899
theorem B1308619 : Blo 1307972 1308619 := bstep (se 1 (by rfl) ⟨981464, by rfl⟩ : syracuseStep 1308619 = 1962929) B1962929
theorem B4970443 : Blo 1307972 4970443 := bstep (se 1 (by rfl) ⟨3727832, by rfl⟩ : syracuseStep 4970443 = 7455665) B7455665
theorem B1963979 : Blo 1307972 1963979 := bstep (se 1 (by rfl) ⟨1472984, by rfl⟩ : syracuseStep 1963979 = 2945969) B2945969
theorem B1308631 : Blo 1307972 1308631 := bstep (se 1 (by rfl) ⟨981473, by rfl⟩ : syracuseStep 1308631 = 1962947) B1962947
theorem B1963991 : Blo 1307972 1963991 := bstep (se 1 (by rfl) ⟨1472993, by rfl⟩ : syracuseStep 1963991 = 2945987) B2945987
theorem B5593049 : Blo 1307972 5593049 := bstep (se 2 (by rfl) ⟨2097393, by rfl⟩ : syracuseStep 5593049 = 4194787) B4194787
theorem B2947031 : Blo 1307972 2947031 := bstep (se 1 (by rfl) ⟨2210273, by rfl⟩ : syracuseStep 2947031 = 4420547) B4420547
theorem B1308651 : Blo 1307972 1308651 := bstep (se 1 (by rfl) ⟨981488, by rfl⟩ : syracuseStep 1308651 = 1962977) B1962977
theorem B1308663 : Blo 1307972 1308663 := bstep (se 1 (by rfl) ⟨981497, by rfl⟩ : syracuseStep 1308663 = 1962995) B1962995
theorem B1472503 : Blo 1307972 1472503 := bstep (se 1 (by rfl) ⟨1104377, by rfl⟩ : syracuseStep 1472503 = 2208755) B2208755
theorem B1308683 : Blo 1307972 1308683 := bstep (se 1 (by rfl) ⟨981512, by rfl⟩ : syracuseStep 1308683 = 1963025) B1963025
theorem B8386577 : Blo 1307972 8386577 := bstep (se 2 (by rfl) ⟨3144966, by rfl⟩ : syracuseStep 8386577 = 6289933) B6289933
theorem B1308695 : Blo 1307972 1308695 := bstep (se 1 (by rfl) ⟨981521, by rfl⟩ : syracuseStep 1308695 = 1963043) B1963043
theorem B1964057 : Blo 1307972 1964057 := bstep (se 2 (by rfl) ⟨736521, by rfl⟩ : syracuseStep 1964057 = 1473043) B1473043
theorem B1308715 : Blo 1307972 1308715 := bstep (se 1 (by rfl) ⟨981536, by rfl⟩ : syracuseStep 1308715 = 1963073) B1963073
theorem B7960621 : Blo 1307972 7960621 := bstep (se 3 (by rfl) ⟨1492616, by rfl⟩ : syracuseStep 7960621 = 2985233) B2985233
theorem B3979315 : Blo 1307972 3979315 := bstep (se 1 (by rfl) ⟨2984486, by rfl⟩ : syracuseStep 3979315 = 5968973) B5968973
theorem B82778165 : Blo 1307972 82778165 := bstep (se 5 (by rfl) ⟨3880226, by rfl⟩ : syracuseStep 82778165 = 7760453) B7760453
theorem B1308727 : Blo 1307972 1308727 := bstep (se 1 (by rfl) ⟨981545, by rfl⟩ : syracuseStep 1308727 = 1963091) B1963091
theorem B5036107 : Blo 1307972 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B1308747 : Blo 1307972 1308747 := bstep (se 1 (by rfl) ⟨981560, by rfl⟩ : syracuseStep 1308747 = 1963121) B1963121
theorem B1308759 : Blo 1307972 1308759 := bstep (se 1 (by rfl) ⟨981569, by rfl⟩ : syracuseStep 1308759 = 1963139) B1963139
theorem B1308779 : Blo 1307972 1308779 := bstep (se 1 (by rfl) ⟨981584, by rfl⟩ : syracuseStep 1308779 = 1963169) B1963169
theorem B2652275 : Blo 1307972 2652275 := bstep (se 1 (by rfl) ⟨1989206, by rfl⟩ : syracuseStep 2652275 = 3978413) B3978413
theorem B1308791 : Blo 1307972 1308791 := bstep (se 1 (by rfl) ⟨981593, by rfl⟩ : syracuseStep 1308791 = 1963187) B1963187
theorem B6813827 : Blo 1307972 6813827 := bstep (se 1 (by rfl) ⟨5110370, by rfl⟩ : syracuseStep 6813827 = 10220741) B10220741
theorem B1308811 : Blo 1307972 1308811 := bstep (se 1 (by rfl) ⟨981608, by rfl⟩ : syracuseStep 1308811 = 1963217) B1963217
theorem B1964171 : Blo 1307972 1964171 := bstep (se 1 (by rfl) ⟨1473128, by rfl⟩ : syracuseStep 1964171 = 2946257) B2946257
theorem B2947211 : Blo 1307972 2947211 := bstep (se 1 (by rfl) ⟨2210408, by rfl⟩ : syracuseStep 2947211 = 4420817) B4420817
theorem B2357399 : Blo 1307972 2357399 := bstep (se 1 (by rfl) ⟨1768049, by rfl⟩ : syracuseStep 2357399 = 3536099) B3536099
theorem B1308823 : Blo 1307972 1308823 := bstep (se 1 (by rfl) ⟨981617, by rfl⟩ : syracuseStep 1308823 = 1963235) B1963235
theorem B1964183 : Blo 1307972 1964183 := bstep (se 1 (by rfl) ⟨1473137, by rfl⟩ : syracuseStep 1964183 = 2946275) B2946275
theorem B2209943 : Blo 1307972 2209943 := bstep (se 1 (by rfl) ⟨1657457, by rfl⟩ : syracuseStep 2209943 = 3314915) B3314915
theorem B1308843 : Blo 1307972 1308843 := bstep (se 1 (by rfl) ⟨981632, by rfl⟩ : syracuseStep 1308843 = 1963265) B1963265
theorem B1472683 : Blo 1307972 1472683 := bstep (se 1 (by rfl) ⟨1104512, by rfl⟩ : syracuseStep 1472683 = 2209025) B2209025
theorem B1308855 : Blo 1307972 1308855 := bstep (se 1 (by rfl) ⟨981641, by rfl⟩ : syracuseStep 1308855 = 1963283) B1963283
theorem B2947265 : Blo 1307972 2947265 := bstep (se 2 (by rfl) ⟨1105224, by rfl⟩ : syracuseStep 2947265 = 2210449) B2210449
theorem B1308875 : Blo 1307972 1308875 := bstep (se 1 (by rfl) ⟨981656, by rfl⟩ : syracuseStep 1308875 = 1963313) B1963313
theorem B1308887 : Blo 1307972 1308887 := bstep (se 1 (by rfl) ⟨981665, by rfl⟩ : syracuseStep 1308887 = 1963331) B1963331
theorem B1964249 : Blo 1307972 1964249 := bstep (se 2 (by rfl) ⟨736593, by rfl⟩ : syracuseStep 1964249 = 1473187) B1473187
theorem B4970717 : Blo 1307972 4970717 := bstep (se 3 (by rfl) ⟨932009, by rfl⟩ : syracuseStep 4970717 = 1864019) B1864019
theorem B1308907 : Blo 1307972 1308907 := bstep (se 1 (by rfl) ⟨981680, by rfl⟩ : syracuseStep 1308907 = 1963361) B1963361
theorem B1308919 : Blo 1307972 1308919 := bstep (se 1 (by rfl) ⟨981689, by rfl⟩ : syracuseStep 1308919 = 1963379) B1963379
theorem B5306627 : Blo 1307972 5306627 := bstep (se 1 (by rfl) ⟨3979970, by rfl⟩ : syracuseStep 5306627 = 7959941) B7959941
theorem B1308939 : Blo 1307972 1308939 := bstep (se 1 (by rfl) ⟨981704, by rfl⟩ : syracuseStep 1308939 = 1963409) B1963409
theorem B2652439 : Blo 1307972 2652439 := bstep (se 1 (by rfl) ⟨1989329, by rfl⟩ : syracuseStep 2652439 = 3978659) B3978659
theorem B1308951 : Blo 1307972 1308951 := bstep (se 1 (by rfl) ⟨981713, by rfl⟩ : syracuseStep 1308951 = 1963427) B1963427
theorem B1472791 : Blo 1307972 1472791 := bstep (se 1 (by rfl) ⟨1104593, by rfl⟩ : syracuseStep 1472791 = 2209187) B2209187
theorem B2210071 : Blo 1307972 2210071 := bstep (se 1 (by rfl) ⟨1657553, by rfl⟩ : syracuseStep 2210071 = 3315107) B3315107
theorem B1308971 : Blo 1307972 1308971 := bstep (se 1 (by rfl) ⟨981728, by rfl⟩ : syracuseStep 1308971 = 1963457) B1963457
theorem B1308983 : Blo 1307972 1308983 := bstep (se 1 (by rfl) ⟨981737, by rfl⟩ : syracuseStep 1308983 = 1963475) B1963475
theorem B1309003 : Blo 1307972 1309003 := bstep (se 1 (by rfl) ⟨981752, by rfl⟩ : syracuseStep 1309003 = 1963505) B1963505
theorem B1964363 : Blo 1307972 1964363 := bstep (se 1 (by rfl) ⟨1473272, by rfl⟩ : syracuseStep 1964363 = 2946545) B2946545
theorem B1309015 : Blo 1307972 1309015 := bstep (se 1 (by rfl) ⟨981761, by rfl⟩ : syracuseStep 1309015 = 1963523) B1963523
theorem B1964375 : Blo 1307972 1964375 := bstep (se 1 (by rfl) ⟨1473281, by rfl⟩ : syracuseStep 1964375 = 2946563) B2946563
theorem B1309035 : Blo 1307972 1309035 := bstep (se 1 (by rfl) ⟨981776, by rfl⟩ : syracuseStep 1309035 = 1963553) B1963553
theorem B1309047 : Blo 1307972 1309047 := bstep (se 1 (by rfl) ⟨981785, by rfl⟩ : syracuseStep 1309047 = 1963571) B1963571
theorem B1309067 : Blo 1307972 1309067 := bstep (se 1 (by rfl) ⟨981800, by rfl⟩ : syracuseStep 1309067 = 1963601) B1963601
theorem B1309079 : Blo 1307972 1309079 := bstep (se 1 (by rfl) ⟨981809, by rfl⟩ : syracuseStep 1309079 = 1963619) B1963619
theorem B1964441 : Blo 1307972 1964441 := bstep (se 2 (by rfl) ⟨736665, by rfl⟩ : syracuseStep 1964441 = 1473331) B1473331
theorem B1309099 : Blo 1307972 1309099 := bstep (se 1 (by rfl) ⟨981824, by rfl⟩ : syracuseStep 1309099 = 1963649) B1963649
theorem B1309111 : Blo 1307972 1309111 := bstep (se 1 (by rfl) ⟨981833, by rfl⟩ : syracuseStep 1309111 = 1963667) B1963667
theorem B1309131 : Blo 1307972 1309131 := bstep (se 1 (by rfl) ⟨981848, by rfl⟩ : syracuseStep 1309131 = 1963697) B1963697
theorem B1472971 : Blo 1307972 1472971 := bstep (se 1 (by rfl) ⟨1104728, by rfl⟩ : syracuseStep 1472971 = 2209457) B2209457
theorem B1309143 : Blo 1307972 1309143 := bstep (se 1 (by rfl) ⟨981857, by rfl⟩ : syracuseStep 1309143 = 1963715) B1963715
theorem B1309163 : Blo 1307972 1309163 := bstep (se 1 (by rfl) ⟨981872, by rfl⟩ : syracuseStep 1309163 = 1963745) B1963745
theorem B1309175 : Blo 1307972 1309175 := bstep (se 1 (by rfl) ⟨981881, by rfl⟩ : syracuseStep 1309175 = 1963763) B1963763
theorem B1309195 : Blo 1307972 1309195 := bstep (se 1 (by rfl) ⟨981896, by rfl⟩ : syracuseStep 1309195 = 1963793) B1963793
theorem B1964555 : Blo 1307972 1964555 := bstep (se 1 (by rfl) ⟨1473416, by rfl⟩ : syracuseStep 1964555 = 2946833) B2946833
theorem B1309207 : Blo 1307972 1309207 := bstep (se 1 (by rfl) ⟨981905, by rfl⟩ : syracuseStep 1309207 = 1963811) B1963811
theorem B1964567 : Blo 1307972 1964567 := bstep (se 1 (by rfl) ⟨1473425, by rfl⟩ : syracuseStep 1964567 = 2946851) B2946851
theorem B1309227 : Blo 1307972 1309227 := bstep (se 1 (by rfl) ⟨981920, by rfl⟩ : syracuseStep 1309227 = 1963841) B1963841
theorem B1309239 : Blo 1307972 1309239 := bstep (se 1 (by rfl) ⟨981929, by rfl⟩ : syracuseStep 1309239 = 1963859) B1963859
theorem B1473079 : Blo 1307972 1473079 := bstep (se 1 (by rfl) ⟨1104809, by rfl⟩ : syracuseStep 1473079 = 2209619) B2209619
theorem B1309259 : Blo 1307972 1309259 := bstep (se 1 (by rfl) ⟨981944, by rfl⟩ : syracuseStep 1309259 = 1963889) B1963889
theorem B1309271 : Blo 1307972 1309271 := bstep (se 1 (by rfl) ⟨981953, by rfl⟩ : syracuseStep 1309271 = 1963907) B1963907
theorem B1964633 : Blo 1307972 1964633 := bstep (se 2 (by rfl) ⟨736737, by rfl⟩ : syracuseStep 1964633 = 1473475) B1473475
theorem B1309291 : Blo 1307972 1309291 := bstep (se 1 (by rfl) ⟨981968, by rfl⟩ : syracuseStep 1309291 = 1963937) B1963937
theorem B1309303 : Blo 1307972 1309303 := bstep (se 1 (by rfl) ⟨981977, by rfl⟩ : syracuseStep 1309303 = 1963955) B1963955
theorem B1309323 : Blo 1307972 1309323 := bstep (se 1 (by rfl) ⟨981992, by rfl⟩ : syracuseStep 1309323 = 1963985) B1963985
theorem B1309335 : Blo 1307972 1309335 := bstep (se 1 (by rfl) ⟨982001, by rfl⟩ : syracuseStep 1309335 = 1964003) B1964003
theorem B1309355 : Blo 1307972 1309355 := bstep (se 1 (by rfl) ⟨982016, by rfl⟩ : syracuseStep 1309355 = 1964033) B1964033
theorem B1309367 : Blo 1307972 1309367 := bstep (se 1 (by rfl) ⟨982025, by rfl⟩ : syracuseStep 1309367 = 1964051) B1964051
theorem B1309387 : Blo 1307972 1309387 := bstep (se 1 (by rfl) ⟨982040, by rfl⟩ : syracuseStep 1309387 = 1964081) B1964081
theorem B1964747 : Blo 1307972 1964747 := bstep (se 1 (by rfl) ⟨1473560, by rfl⟩ : syracuseStep 1964747 = 2947121) B2947121
theorem B1309399 : Blo 1307972 1309399 := bstep (se 1 (by rfl) ⟨982049, by rfl⟩ : syracuseStep 1309399 = 1964099) B1964099
theorem B1964759 : Blo 1307972 1964759 := bstep (se 1 (by rfl) ⟨1473569, by rfl⟩ : syracuseStep 1964759 = 2947139) B2947139
theorem B1309419 : Blo 1307972 1309419 := bstep (se 1 (by rfl) ⟨982064, by rfl⟩ : syracuseStep 1309419 = 1964129) B1964129
theorem B1473259 : Blo 1307972 1473259 := bstep (se 1 (by rfl) ⟨1104944, by rfl⟩ : syracuseStep 1473259 = 2209889) B2209889
theorem B1309431 : Blo 1307972 1309431 := bstep (se 1 (by rfl) ⟨982073, by rfl⟩ : syracuseStep 1309431 = 1964147) B1964147
theorem B1309451 : Blo 1307972 1309451 := bstep (se 1 (by rfl) ⟨982088, by rfl⟩ : syracuseStep 1309451 = 1964177) B1964177
theorem B7453457 : Blo 1307972 7453457 := bstep (se 2 (by rfl) ⟨2795046, by rfl⟩ : syracuseStep 7453457 = 5590093) B5590093
theorem B1309463 : Blo 1307972 1309463 := bstep (se 1 (by rfl) ⟨982097, by rfl⟩ : syracuseStep 1309463 = 1964195) B1964195
theorem B1964825 : Blo 1307972 1964825 := bstep (se 2 (by rfl) ⟨736809, by rfl⟩ : syracuseStep 1964825 = 1473619) B1473619
theorem B1309483 : Blo 1307972 1309483 := bstep (se 1 (by rfl) ⟨982112, by rfl⟩ : syracuseStep 1309483 = 1964225) B1964225
theorem B1309495 : Blo 1307972 1309495 := bstep (se 1 (by rfl) ⟨982121, by rfl⟩ : syracuseStep 1309495 = 1964243) B1964243
theorem B6626123 : Blo 1307972 6626123 := bstep (se 1 (by rfl) ⟨4969592, by rfl⟩ : syracuseStep 6626123 = 9939185) B9939185
theorem B1309515 : Blo 1307972 1309515 := bstep (se 1 (by rfl) ⟨982136, by rfl⟩ : syracuseStep 1309515 = 1964273) B1964273
theorem B1309527 : Blo 1307972 1309527 := bstep (se 1 (by rfl) ⟨982145, by rfl⟩ : syracuseStep 1309527 = 1964291) B1964291
theorem B2153305 : Blo 1307972 2153305 := bstep (se 2 (by rfl) ⟨807489, by rfl⟩ : syracuseStep 2153305 = 1614979) B1614979
theorem B1473367 : Blo 1307972 1473367 := bstep (se 1 (by rfl) ⟨1105025, by rfl⟩ : syracuseStep 1473367 = 2210051) B2210051
theorem B1309547 : Blo 1307972 1309547 := bstep (se 1 (by rfl) ⟨982160, by rfl⟩ : syracuseStep 1309547 = 1964321) B1964321
theorem B1309559 : Blo 1307972 1309559 := bstep (se 1 (by rfl) ⟨982169, by rfl⟩ : syracuseStep 1309559 = 1964339) B1964339
theorem B2358155 : Blo 1307972 2358155 := bstep (se 1 (by rfl) ⟨1768616, by rfl⟩ : syracuseStep 2358155 = 3537233) B3537233
theorem B1309579 : Blo 1307972 1309579 := bstep (se 1 (by rfl) ⟨982184, by rfl⟩ : syracuseStep 1309579 = 1964369) B1964369
theorem B1964939 : Blo 1307972 1964939 := bstep (se 1 (by rfl) ⟨1473704, by rfl⟩ : syracuseStep 1964939 = 2947409) B2947409
theorem B5970833 : Blo 1307972 5970833 := bstep (se 2 (by rfl) ⟨2239062, by rfl⟩ : syracuseStep 5970833 = 4478125) B4478125
theorem B4971415 : Blo 1307972 4971415 := bstep (se 1 (by rfl) ⟨3728561, by rfl⟩ : syracuseStep 4971415 = 7457123) B7457123
theorem B1309591 : Blo 1307972 1309591 := bstep (se 1 (by rfl) ⟨982193, by rfl⟩ : syracuseStep 1309591 = 1964387) B1964387
theorem B1964951 : Blo 1307972 1964951 := bstep (se 1 (by rfl) ⟨1473713, by rfl⟩ : syracuseStep 1964951 = 2947427) B2947427
theorem B1309611 : Blo 1307972 1309611 := bstep (se 1 (by rfl) ⟨982208, by rfl⟩ : syracuseStep 1309611 = 1964417) B1964417
theorem B1309623 : Blo 1307972 1309623 := bstep (se 1 (by rfl) ⟨982217, by rfl⟩ : syracuseStep 1309623 = 1964435) B1964435
theorem B1309643 : Blo 1307972 1309643 := bstep (se 1 (by rfl) ⟨982232, by rfl⟩ : syracuseStep 1309643 = 1964465) B1964465
theorem B1309655 : Blo 1307972 1309655 := bstep (se 1 (by rfl) ⟨982241, by rfl⟩ : syracuseStep 1309655 = 1964483) B1964483
theorem B1309675 : Blo 1307972 1309675 := bstep (se 1 (by rfl) ⟨982256, by rfl⟩ : syracuseStep 1309675 = 1964513) B1964513
theorem B1309687 : Blo 1307972 1309687 := bstep (se 1 (by rfl) ⟨982265, by rfl⟩ : syracuseStep 1309687 = 1964531) B1964531
theorem B1309707 : Blo 1307972 1309707 := bstep (se 1 (by rfl) ⟨982280, by rfl⟩ : syracuseStep 1309707 = 1964561) B1964561
theorem B1473547 : Blo 1307972 1473547 := bstep (se 1 (by rfl) ⟨1105160, by rfl⟩ : syracuseStep 1473547 = 2210321) B2210321
theorem B1309719 : Blo 1307972 1309719 := bstep (se 1 (by rfl) ⟨982289, by rfl⟩ : syracuseStep 1309719 = 1964579) B1964579
theorem B14146595 : Blo 1307972 14146595 := bstep (se 1 (by rfl) ⟨10609946, by rfl⟩ : syracuseStep 14146595 = 21219893) B21219893
theorem B1309739 : Blo 1307972 1309739 := bstep (se 1 (by rfl) ⟨982304, by rfl⟩ : syracuseStep 1309739 = 1964609) B1964609
theorem B1309751 : Blo 1307972 1309751 := bstep (se 1 (by rfl) ⟨982313, by rfl⟩ : syracuseStep 1309751 = 1964627) B1964627
theorem B1309771 : Blo 1307972 1309771 := bstep (se 1 (by rfl) ⟨982328, by rfl⟩ : syracuseStep 1309771 = 1964657) B1964657
theorem B1309783 : Blo 1307972 1309783 := bstep (se 1 (by rfl) ⟨982337, by rfl⟩ : syracuseStep 1309783 = 1964675) B1964675
theorem B4414553 : Blo 1307972 4414553 := bstep (se 2 (by rfl) ⟨1655457, by rfl⟩ : syracuseStep 4414553 = 3310915) B3310915
theorem B1309803 : Blo 1307972 1309803 := bstep (se 1 (by rfl) ⟨982352, by rfl⟩ : syracuseStep 1309803 = 1964705) B1964705
theorem B1309815 : Blo 1307972 1309815 := bstep (se 1 (by rfl) ⟨982361, by rfl⟩ : syracuseStep 1309815 = 1964723) B1964723
theorem B1473655 : Blo 1307972 1473655 := bstep (se 1 (by rfl) ⟨1105241, by rfl⟩ : syracuseStep 1473655 = 2210483) B2210483
theorem B1309835 : Blo 1307972 1309835 := bstep (se 1 (by rfl) ⟨982376, by rfl⟩ : syracuseStep 1309835 = 1964753) B1964753
theorem B1309847 : Blo 1307972 1309847 := bstep (se 1 (by rfl) ⟨982385, by rfl⟩ : syracuseStep 1309847 = 1964771) B1964771
theorem B1309867 : Blo 1307972 1309867 := bstep (se 1 (by rfl) ⟨982400, by rfl⟩ : syracuseStep 1309867 = 1964801) B1964801
theorem B47733941 : Blo 1307972 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B1309879 : Blo 1307972 1309879 := bstep (se 1 (by rfl) ⟨982409, by rfl⟩ : syracuseStep 1309879 = 1964819) B1964819
theorem B1309899 : Blo 1307972 1309899 := bstep (se 1 (by rfl) ⟨982424, by rfl⟩ : syracuseStep 1309899 = 1964849) B1964849
theorem B1309911 : Blo 1307972 1309911 := bstep (se 1 (by rfl) ⟨982433, by rfl⟩ : syracuseStep 1309911 = 1964867) B1964867
theorem B3726557 : Blo 1307972 3726557 := bstep (se 3 (by rfl) ⟨698729, by rfl⟩ : syracuseStep 3726557 = 1397459) B1397459
theorem B1309931 : Blo 1307972 1309931 := bstep (se 1 (by rfl) ⟨982448, by rfl⟩ : syracuseStep 1309931 = 1964897) B1964897
theorem B1309943 : Blo 1307972 1309943 := bstep (se 1 (by rfl) ⟨982457, by rfl⟩ : syracuseStep 1309943 = 1964915) B1964915
theorem B1309963 : Blo 1307972 1309963 := bstep (se 1 (by rfl) ⟨982472, by rfl⟩ : syracuseStep 1309963 = 1964945) B1964945
theorem B18857393 : Blo 1307972 18857393 := bstep (se 2 (by rfl) ⟨7071522, by rfl⟩ : syracuseStep 18857393 = 14143045) B14143045
theorem B3726785 : Blo 1307972 3726785 := bstep (se 2 (by rfl) ⟨1397544, by rfl⟩ : syracuseStep 3726785 = 2795089) B2795089
theorem B2358731 : Blo 1307972 2358731 := bstep (se 1 (by rfl) ⟨1769048, by rfl⟩ : syracuseStep 2358731 = 3538097) B3538097
theorem B3538379 : Blo 1307972 3538379 := bstep (se 1 (by rfl) ⟨2653784, by rfl⟩ : syracuseStep 3538379 = 5307569) B5307569
theorem B4718027 : Blo 1307972 4718027 := bstep (se 1 (by rfl) ⟨3538520, by rfl⟩ : syracuseStep 4718027 = 7077041) B7077041
theorem B2096599 : Blo 1307972 2096599 := bstep (se 1 (by rfl) ⟨1572449, by rfl⟩ : syracuseStep 2096599 = 3144899) B3144899
theorem B5308055 : Blo 1307972 5308055 := bstep (se 1 (by rfl) ⟨3981041, by rfl⟩ : syracuseStep 5308055 = 7962083) B7962083
theorem B4972205 : Blo 1307972 4972205 := bstep (se 3 (by rfl) ⟨932288, by rfl⟩ : syracuseStep 4972205 = 1864577) B1864577
theorem B2096855 : Blo 1307972 2096855 := bstep (se 1 (by rfl) ⟨1572641, by rfl⟩ : syracuseStep 2096855 = 3145283) B3145283
theorem B4415255 : Blo 1307972 4415255 := bstep (se 1 (by rfl) ⟨3311441, by rfl⟩ : syracuseStep 4415255 = 6622883) B6622883
theorem B3727127 : Blo 1307972 3727127 := bstep (se 1 (by rfl) ⟨2795345, by rfl⟩ : syracuseStep 3727127 = 5590691) B5590691
theorem B2793619 : Blo 1307972 2793619 := bstep (se 1 (by rfl) ⟨2095214, by rfl⟩ : syracuseStep 2793619 = 4190429) B4190429
theorem B1769719 : Blo 1307972 1769719 := bstep (se 1 (by rfl) ⟨1327289, by rfl⟩ : syracuseStep 1769719 = 2654579) B2654579
theorem B8380705 : Blo 1307972 8380705 := bstep (se 2 (by rfl) ⟨3142764, by rfl⟩ : syracuseStep 8380705 = 6285529) B6285529
theorem B5595425 : Blo 1307972 5595425 := bstep (se 2 (by rfl) ⟨2098284, by rfl⟩ : syracuseStep 5595425 = 4196569) B4196569
theorem B2834731 : Blo 1307972 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B4972859 : Blo 1307972 4972859 := bstep (se 1 (by rfl) ⟨3729644, by rfl⟩ : syracuseStep 4972859 = 7459289) B7459289
theorem B4416011 : Blo 1307972 4416011 := bstep (se 1 (by rfl) ⟨3312008, by rfl⟩ : syracuseStep 4416011 = 6624017) B6624017
theorem B1573391 : Blo 1307972 1573391 := bstep (se 1 (by rfl) ⟨1180043, by rfl⟩ : syracuseStep 1573391 = 2360087) B2360087
theorem B7078423 : Blo 1307972 7078423 := bstep (se 1 (by rfl) ⟨5308817, by rfl⟩ : syracuseStep 7078423 = 10617635) B10617635
theorem B4416119 : Blo 1307972 4416119 := bstep (se 1 (by rfl) ⟨3312089, by rfl⟩ : syracuseStep 4416119 = 6624179) B6624179
theorem B3146359 : Blo 1307972 3146359 := bstep (se 1 (by rfl) ⟨2359769, by rfl⟩ : syracuseStep 3146359 = 4719539) B4719539
theorem B4973345 : Blo 1307972 4973345 := bstep (se 2 (by rfl) ⟨1865004, by rfl⟩ : syracuseStep 4973345 = 3730009) B3730009
theorem B3728243 : Blo 1307972 3728243 := bstep (se 1 (by rfl) ⟨2796182, by rfl⟩ : syracuseStep 3728243 = 5592365) B5592365
theorem B6292409 : Blo 1307972 6292409 := bstep (se 2 (by rfl) ⟨2359653, by rfl⟩ : syracuseStep 6292409 = 4719307) B4719307
theorem B4719683 : Blo 1307972 4719683 := bstep (se 1 (by rfl) ⟨3539762, by rfl⟩ : syracuseStep 4719683 = 7079525) B7079525
theorem B4416713 : Blo 1307972 4416713 := bstep (se 2 (by rfl) ⟨1656267, by rfl⟩ : syracuseStep 4416713 = 3312535) B3312535
theorem B6628553 : Blo 1307972 6628553 := bstep (se 2 (by rfl) ⟨2485707, by rfl⟩ : syracuseStep 6628553 = 4971415) B4971415
theorem B3728585 : Blo 1307972 3728585 := bstep (se 2 (by rfl) ⟨1398219, by rfl⟩ : syracuseStep 3728585 = 2796439) B2796439
theorem B1656055 : Blo 1307972 1656055 := bstep (se 1 (by rfl) ⟨1242041, by rfl⟩ : syracuseStep 1656055 = 2484083) B2484083
theorem B551380229 : Blo 1307972 551380229 := bstep (se 4 (by rfl) ⟨51691896, by rfl⟩ : syracuseStep 551380229 = 103383793) B103383793
theorem B3728699 : Blo 1307972 3728699 := bstep (se 1 (by rfl) ⟨2796524, by rfl⟩ : syracuseStep 3728699 = 5593049) B5593049
theorem B3728825 : Blo 1307972 3728825 := bstep (se 2 (by rfl) ⟨1398309, by rfl⟩ : syracuseStep 3728825 = 2796619) B2796619
theorem B1656379 : Blo 1307972 1656379 := bstep (se 1 (by rfl) ⟨1242284, by rfl⟩ : syracuseStep 1656379 = 2484569) B2484569
theorem B3311219 : Blo 1307972 3311219 := bstep (se 1 (by rfl) ⟨2483414, by rfl⟩ : syracuseStep 3311219 = 4966829) B4966829
theorem B3311239 : Blo 1307972 3311239 := bstep (se 1 (by rfl) ⟨2483429, by rfl⟩ : syracuseStep 3311239 = 4966859) B4966859
theorem B7079653 : Blo 1307972 7079653 := bstep (se 4 (by rfl) ⟨663717, by rfl⟩ : syracuseStep 7079653 = 1327435) B1327435
theorem B4417415 : Blo 1307972 4417415 := bstep (se 1 (by rfl) ⟨3313061, by rfl⟩ : syracuseStep 4417415 = 6626123) B6626123
theorem B3311513 : Blo 1307972 3311513 := bstep (se 2 (by rfl) ⟨1241817, by rfl⟩ : syracuseStep 3311513 = 2483635) B2483635
theorem B2795465 : Blo 1307972 2795465 := bstep (se 2 (by rfl) ⟨1048299, by rfl⟩ : syracuseStep 2795465 = 2096599) B2096599
theorem B9431063 : Blo 1307972 9431063 := bstep (se 1 (by rfl) ⟨7073297, by rfl⟩ : syracuseStep 9431063 = 14146595) B14146595
theorem B1656875 : Blo 1307972 1656875 := bstep (se 1 (by rfl) ⟨1242656, by rfl⟩ : syracuseStep 1656875 = 2485313) B2485313
theorem B3360811 : Blo 1307972 3360811 := bstep (se 1 (by rfl) ⟨2520608, by rfl⟩ : syracuseStep 3360811 = 5041217) B5041217
theorem B2943035 : Blo 1307972 2943035 := bstep (se 1 (by rfl) ⟨2207276, by rfl⟩ : syracuseStep 2943035 = 4414553) B4414553
theorem B3311675 : Blo 1307972 3311675 := bstep (se 1 (by rfl) ⟨2483756, by rfl⟩ : syracuseStep 3311675 = 4967513) B4967513
theorem B7874621 : Blo 1307972 7874621 := bstep (se 3 (by rfl) ⟨1476491, by rfl⟩ : syracuseStep 7874621 = 2952983) B2952983
theorem B2484371 : Blo 1307972 2484371 := bstep (se 1 (by rfl) ⟨1863278, by rfl⟩ : syracuseStep 2484371 = 3726557) B3726557
theorem B2943161 : Blo 1307972 2943161 := bstep (se 2 (by rfl) ⟨1103685, by rfl⟩ : syracuseStep 2943161 = 2207371) B2207371
theorem B2484425 : Blo 1307972 2484425 := bstep (se 2 (by rfl) ⟨931659, by rfl⟩ : syracuseStep 2484425 = 1863319) B1863319
theorem B4417793 : Blo 1307972 4417793 := bstep (se 2 (by rfl) ⟨1656672, by rfl⟩ : syracuseStep 4417793 = 3313345) B3313345
theorem B3311887 : Blo 1307972 3311887 := bstep (se 1 (by rfl) ⟨2483915, by rfl⟩ : syracuseStep 3311887 = 4967831) B4967831
theorem B2484523 : Blo 1307972 2484523 := bstep (se 1 (by rfl) ⟨1863392, by rfl⟩ : syracuseStep 2484523 = 3726785) B3726785
theorem B1657351 : Blo 1307972 1657351 := bstep (se 1 (by rfl) ⟨1243013, by rfl⟩ : syracuseStep 1657351 = 2486027) B2486027
theorem B2943503 : Blo 1307972 2943503 := bstep (se 1 (by rfl) ⟨2207627, by rfl⟩ : syracuseStep 2943503 = 4415255) B4415255
theorem B2484751 : Blo 1307972 2484751 := bstep (se 1 (by rfl) ⟨1863563, by rfl⟩ : syracuseStep 2484751 = 3727127) B3727127
theorem B2943521 : Blo 1307972 2943521 := bstep (se 2 (by rfl) ⟨1103820, by rfl⟩ : syracuseStep 2943521 = 2207641) B2207641
theorem B3312161 : Blo 1307972 3312161 := bstep (se 2 (by rfl) ⟨1242060, by rfl⟩ : syracuseStep 3312161 = 2484121) B2484121
theorem B16780121 : Blo 1307972 16780121 := bstep (se 2 (by rfl) ⟨6292545, by rfl⟩ : syracuseStep 16780121 = 12585091) B12585091
theorem B2943863 : Blo 1307972 2943863 := bstep (se 1 (by rfl) ⟨2207897, by rfl⟩ : syracuseStep 2943863 = 4415795) B4415795
theorem B4967315 : Blo 1307972 4967315 := bstep (se 1 (by rfl) ⟨3725486, by rfl⟩ : syracuseStep 4967315 = 7450973) B7450973
theorem B7072733 : Blo 1307972 7072733 := bstep (se 3 (by rfl) ⟨1326137, by rfl⟩ : syracuseStep 7072733 = 2652275) B2652275
theorem B1657847 : Blo 1307972 1657847 := bstep (se 1 (by rfl) ⟨1243385, by rfl⟩ : syracuseStep 1657847 = 2486771) B2486771
theorem B2944043 : Blo 1307972 2944043 := bstep (se 1 (by rfl) ⟨2208032, by rfl⟩ : syracuseStep 2944043 = 4416065) B4416065
theorem B4418603 : Blo 1307972 4418603 := bstep (se 1 (by rfl) ⟨3313952, by rfl⟩ : syracuseStep 4418603 = 6627905) B6627905
theorem B28691587 : Blo 1307972 28691587 := bstep (se 1 (by rfl) ⟨21518690, by rfl⟩ : syracuseStep 28691587 = 43037381) B43037381
theorem B5041523 : Blo 1307972 5041523 := bstep (se 1 (by rfl) ⟨3781142, by rfl⟩ : syracuseStep 5041523 = 7562285) B7562285
theorem B2944403 : Blo 1307972 2944403 := bstep (se 1 (by rfl) ⟨2208302, by rfl⟩ : syracuseStep 2944403 = 4416605) B4416605
theorem B3315755 : Blo 1307972 3315755 := bstep (se 1 (by rfl) ⟨2486816, by rfl⟩ : syracuseStep 3315755 = 4973633) B4973633
theorem B2944457 : Blo 1307972 2944457 := bstep (se 2 (by rfl) ⟨1104171, by rfl⟩ : syracuseStep 2944457 = 2208343) B2208343
theorem B9203203 : Blo 1307972 9203203 := bstep (se 1 (by rfl) ⟨6902402, by rfl⟩ : syracuseStep 9203203 = 13804805) B13804805
theorem B3313163 : Blo 1307972 3313163 := bstep (se 1 (by rfl) ⟨2484872, by rfl⟩ : syracuseStep 3313163 = 4969745) B4969745
theorem B2207351 : Blo 1307972 2207351 := bstep (se 1 (by rfl) ⟨1655513, by rfl⟩ : syracuseStep 2207351 = 3311027) B3311027
theorem B145288835 : Blo 1307972 145288835 := bstep (se 1 (by rfl) ⟨108966626, by rfl⟩ : syracuseStep 145288835 = 217933253) B217933253
theorem B1863415 : Blo 1307972 1863415 := bstep (se 1 (by rfl) ⟨1397561, by rfl⟩ : syracuseStep 1863415 = 2795123) B2795123
theorem B2871073 : Blo 1307972 2871073 := bstep (se 2 (by rfl) ⟨1076652, by rfl⟩ : syracuseStep 2871073 = 2153305) B2153305
theorem B40308529 : Blo 1307972 40308529 := bstep (se 2 (by rfl) ⟨15115698, by rfl⟩ : syracuseStep 40308529 = 30231397) B30231397
theorem B7458763 : Blo 1307972 7458763 := bstep (se 1 (by rfl) ⟨5594072, by rfl⟩ : syracuseStep 7458763 = 11188145) B11188145
theorem B1961975 : Blo 1307972 1961975 := bstep (se 1 (by rfl) ⟨1471481, by rfl⟩ : syracuseStep 1961975 = 2942963) B2942963
theorem B5591051 : Blo 1307972 5591051 := bstep (se 1 (by rfl) ⟨4193288, by rfl⟩ : syracuseStep 5591051 = 8386577) B8386577
theorem B1961999 : Blo 1307972 1961999 := bstep (se 1 (by rfl) ⟨1471499, by rfl⟩ : syracuseStep 1961999 = 2942999) B2942999
theorem B2797583 : Blo 1307972 2797583 := bstep (se 1 (by rfl) ⟨2098187, by rfl⟩ : syracuseStep 2797583 = 4196375) B4196375
theorem B55185443 : Blo 1307972 55185443 := bstep (se 1 (by rfl) ⟨41389082, by rfl⟩ : syracuseStep 55185443 = 82778165) B82778165
theorem B4190251 : Blo 1307972 4190251 := bstep (se 1 (by rfl) ⟨3142688, by rfl⟩ : syracuseStep 4190251 = 6285377) B6285377
theorem B2486315 : Blo 1307972 2486315 := bstep (se 1 (by rfl) ⟨1864736, by rfl⟩ : syracuseStep 2486315 = 3729473) B3729473
theorem B1962041 : Blo 1307972 1962041 := bstep (se 2 (by rfl) ⟨735765, by rfl⟩ : syracuseStep 1962041 = 1471531) B1471531
theorem B2207803 : Blo 1307972 2207803 := bstep (se 1 (by rfl) ⟨1655852, by rfl⟩ : syracuseStep 2207803 = 3311705) B3311705
theorem B4542551 : Blo 1307972 4542551 := bstep (se 1 (by rfl) ⟨3406913, by rfl⟩ : syracuseStep 4542551 = 6813827) B6813827
theorem B1962119 : Blo 1307972 1962119 := bstep (se 1 (by rfl) ⟨1471589, by rfl⟩ : syracuseStep 1962119 = 2943179) B2943179
theorem B3584135 : Blo 1307972 3584135 := bstep (se 1 (by rfl) ⟨2688101, by rfl⟩ : syracuseStep 3584135 = 5376203) B5376203
theorem B2945159 : Blo 1307972 2945159 := bstep (se 1 (by rfl) ⟨2208869, by rfl⟩ : syracuseStep 2945159 = 4417739) B4417739
theorem B3313811 : Blo 1307972 3313811 := bstep (se 1 (by rfl) ⟨2485358, by rfl⟩ : syracuseStep 3313811 = 4970717) B4970717
theorem B1962155 : Blo 1307972 1962155 := bstep (se 1 (by rfl) ⟨1471616, by rfl⟩ : syracuseStep 1962155 = 2943233) B2943233
theorem B1962185 : Blo 1307972 1962185 := bstep (se 2 (by rfl) ⟨735819, by rfl⟩ : syracuseStep 1962185 = 1471639) B1471639
theorem B2207945 : Blo 1307972 2207945 := bstep (se 2 (by rfl) ⟨827979, by rfl⟩ : syracuseStep 2207945 = 1655959) B1655959
theorem B4714811 : Blo 1307972 4714811 := bstep (se 1 (by rfl) ⟨3536108, by rfl⟩ : syracuseStep 4714811 = 7072217) B7072217
theorem B1962299 : Blo 1307972 1962299 := bstep (se 1 (by rfl) ⟨1471724, by rfl⟩ : syracuseStep 1962299 = 2943449) B2943449
theorem B2945339 : Blo 1307972 2945339 := bstep (se 1 (by rfl) ⟨2209004, by rfl⟩ : syracuseStep 2945339 = 4418009) B4418009
theorem B4419899 : Blo 1307972 4419899 := bstep (se 1 (by rfl) ⟨3314924, by rfl⟩ : syracuseStep 4419899 = 6629849) B6629849
theorem B1962359 : Blo 1307972 1962359 := bstep (se 1 (by rfl) ⟨1471769, by rfl⟩ : syracuseStep 1962359 = 2943539) B2943539
theorem B1962383 : Blo 1307972 1962383 := bstep (se 1 (by rfl) ⟨1471787, by rfl⟩ : syracuseStep 1962383 = 2943575) B2943575
theorem B1962425 : Blo 1307972 1962425 := bstep (se 2 (by rfl) ⟨735909, by rfl⟩ : syracuseStep 1962425 = 1471819) B1471819
theorem B2945465 : Blo 1307972 2945465 := bstep (se 2 (by rfl) ⟨1104549, by rfl⟩ : syracuseStep 2945465 = 2209099) B2209099
theorem B3314105 : Blo 1307972 3314105 := bstep (se 2 (by rfl) ⟨1242789, by rfl⟩ : syracuseStep 3314105 = 2485579) B2485579
theorem B1962503 : Blo 1307972 1962503 := bstep (se 1 (by rfl) ⟨1471877, by rfl⟩ : syracuseStep 1962503 = 2943755) B2943755
theorem B4968971 : Blo 1307972 4968971 := bstep (se 1 (by rfl) ⟨3726728, by rfl⟩ : syracuseStep 4968971 = 7453457) B7453457
theorem B1962539 : Blo 1307972 1962539 := bstep (se 1 (by rfl) ⟨1471904, by rfl⟩ : syracuseStep 1962539 = 2943809) B2943809
theorem B1962569 : Blo 1307972 1962569 := bstep (se 2 (by rfl) ⟨735963, by rfl⟩ : syracuseStep 1962569 = 1471927) B1471927
theorem B1962683 : Blo 1307972 1962683 := bstep (se 1 (by rfl) ⟨1472012, by rfl⟩ : syracuseStep 1962683 = 2944025) B2944025
theorem B1962743 : Blo 1307972 1962743 := bstep (se 1 (by rfl) ⟨1472057, by rfl⟩ : syracuseStep 1962743 = 2944115) B2944115
theorem B1962767 : Blo 1307972 1962767 := bstep (se 1 (by rfl) ⟨1472075, by rfl⟩ : syracuseStep 1962767 = 2944151) B2944151
theorem B2945807 : Blo 1307972 2945807 := bstep (se 1 (by rfl) ⟨2209355, by rfl⟩ : syracuseStep 2945807 = 4418711) B4418711
theorem B1864463 : Blo 1307972 1864463 := bstep (se 1 (by rfl) ⟨1398347, by rfl⟩ : syracuseStep 1864463 = 2796695) B2796695
theorem B31822627 : Blo 1307972 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B2945825 : Blo 1307972 2945825 := bstep (se 2 (by rfl) ⟨1104684, by rfl⟩ : syracuseStep 2945825 = 2209369) B2209369
theorem B4420385 : Blo 1307972 4420385 := bstep (se 2 (by rfl) ⟨1657644, by rfl⟩ : syracuseStep 4420385 = 3315289) B3315289
theorem B1962809 : Blo 1307972 1962809 := bstep (se 2 (by rfl) ⟨736053, by rfl⟩ : syracuseStep 1962809 = 1472107) B1472107
theorem B1962887 : Blo 1307972 1962887 := bstep (se 1 (by rfl) ⟨1472165, by rfl⟩ : syracuseStep 1962887 = 2944331) B2944331
theorem B2208647 : Blo 1307972 2208647 := bstep (se 1 (by rfl) ⟨1656485, by rfl⟩ : syracuseStep 2208647 = 3312971) B3312971
theorem B1962923 : Blo 1307972 1962923 := bstep (se 1 (by rfl) ⟨1472192, by rfl⟩ : syracuseStep 1962923 = 2944385) B2944385
theorem B33526709 : Blo 1307972 33526709 := bstep (se 5 (by rfl) ⟨1571564, by rfl⟩ : syracuseStep 33526709 = 3143129) B3143129
theorem B1962953 : Blo 1307972 1962953 := bstep (se 2 (by rfl) ⟨736107, by rfl⟩ : syracuseStep 1962953 = 1472215) B1472215
theorem B12571595 : Blo 1307972 12571595 := bstep (se 1 (by rfl) ⟨9428696, by rfl⟩ : syracuseStep 12571595 = 18857393) B18857393
theorem B1471495 : Blo 1307972 1471495 := bstep (se 1 (by rfl) ⟨1103621, by rfl⟩ : syracuseStep 1471495 = 2207243) B2207243
theorem B1963067 : Blo 1307972 1963067 := bstep (se 1 (by rfl) ⟨1472300, by rfl⟩ : syracuseStep 1963067 = 2944601) B2944601
theorem B1864777 : Blo 1307972 1864777 := bstep (se 2 (by rfl) ⟨699291, by rfl⟩ : syracuseStep 1864777 = 1398583) B1398583
theorem B3314803 : Blo 1307972 3314803 := bstep (se 1 (by rfl) ⟨2486102, by rfl⟩ : syracuseStep 3314803 = 4972205) B4972205
theorem B1963127 : Blo 1307972 1963127 := bstep (se 1 (by rfl) ⟨1472345, by rfl⟩ : syracuseStep 1963127 = 2944691) B2944691
theorem B2946167 : Blo 1307972 2946167 := bstep (se 1 (by rfl) ⟨2209625, by rfl⟩ : syracuseStep 2946167 = 4419251) B4419251
theorem B1963151 : Blo 1307972 1963151 := bstep (se 1 (by rfl) ⟨1472363, by rfl⟩ : syracuseStep 1963151 = 2944727) B2944727
theorem B1397903 : Blo 1307972 1397903 := bstep (se 1 (by rfl) ⟨1048427, by rfl⟩ : syracuseStep 1397903 = 2096855) B2096855
theorem B1963193 : Blo 1307972 1963193 := bstep (se 2 (by rfl) ⟨736197, by rfl⟩ : syracuseStep 1963193 = 1472395) B1472395
theorem B1471675 : Blo 1307972 1471675 := bstep (se 1 (by rfl) ⟨1103756, by rfl⟩ : syracuseStep 1471675 = 2207513) B2207513
theorem B3314945 : Blo 1307972 3314945 := bstep (se 2 (by rfl) ⟨1243104, by rfl⟩ : syracuseStep 3314945 = 2486209) B2486209
theorem B1963271 : Blo 1307972 1963271 := bstep (se 1 (by rfl) ⟨1472453, by rfl⟩ : syracuseStep 1963271 = 2944907) B2944907
theorem B1963307 : Blo 1307972 1963307 := bstep (se 1 (by rfl) ⟨1472480, by rfl⟩ : syracuseStep 1963307 = 2944961) B2944961
theorem B2946347 : Blo 1307972 2946347 := bstep (se 1 (by rfl) ⟨2209760, by rfl⟩ : syracuseStep 2946347 = 4419521) B4419521
theorem B1963337 : Blo 1307972 1963337 := bstep (se 2 (by rfl) ⟨736251, by rfl⟩ : syracuseStep 1963337 = 1472503) B1472503
theorem B4420979 : Blo 1307972 4420979 := bstep (se 1 (by rfl) ⟨3315734, by rfl⟩ : syracuseStep 4420979 = 6631469) B6631469
theorem B1308039 : Blo 1307972 1308039 := bstep (se 1 (by rfl) ⟨981029, by rfl⟩ : syracuseStep 1308039 = 1962059) B1962059
theorem B1398151 : Blo 1307972 1398151 := bstep (se 1 (by rfl) ⟨1048613, by rfl⟩ : syracuseStep 1398151 = 2097227) B2097227
theorem B1308047 : Blo 1307972 1308047 := bstep (se 1 (by rfl) ⟨981035, by rfl⟩ : syracuseStep 1308047 = 1962071) B1962071
theorem B10614161 : Blo 1307972 10614161 := bstep (se 2 (by rfl) ⟨3980310, by rfl⟩ : syracuseStep 10614161 = 7960621) B7960621
theorem B6624665 : Blo 1307972 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B5305753 : Blo 1307972 5305753 := bstep (se 2 (by rfl) ⟨1989657, by rfl⟩ : syracuseStep 5305753 = 3979315) B3979315
theorem B26875313 : Blo 1307972 26875313 := bstep (se 2 (by rfl) ⟨10078242, by rfl⟩ : syracuseStep 26875313 = 20156485) B20156485
theorem B6714809 : Blo 1307972 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B1308091 : Blo 1307972 1308091 := bstep (se 1 (by rfl) ⟨981068, by rfl⟩ : syracuseStep 1308091 = 1962137) B1962137
theorem B1963451 : Blo 1307972 1963451 := bstep (se 1 (by rfl) ⟨1472588, by rfl⟩ : syracuseStep 1963451 = 2945177) B2945177
theorem B12588509 : Blo 1307972 12588509 := bstep (se 3 (by rfl) ⟨2360345, by rfl⟩ : syracuseStep 12588509 = 4720691) B4720691
theorem B1963511 : Blo 1307972 1963511 := bstep (se 1 (by rfl) ⟨1472633, by rfl⟩ : syracuseStep 1963511 = 2945267) B2945267
theorem B1308167 : Blo 1307972 1308167 := bstep (se 1 (by rfl) ⟨981125, by rfl⟩ : syracuseStep 1308167 = 1962251) B1962251
theorem B1308175 : Blo 1307972 1308175 := bstep (se 1 (by rfl) ⟨981131, by rfl⟩ : syracuseStep 1308175 = 1962263) B1962263
theorem B1963535 : Blo 1307972 1963535 := bstep (se 1 (by rfl) ⟨1472651, by rfl⟩ : syracuseStep 1963535 = 2945303) B2945303
theorem B2209295 : Blo 1307972 2209295 := bstep (se 1 (by rfl) ⟨1656971, by rfl⟩ : syracuseStep 2209295 = 3313943) B3313943
theorem B1963577 : Blo 1307972 1963577 := bstep (se 2 (by rfl) ⟨736341, by rfl⟩ : syracuseStep 1963577 = 1472683) B1472683
theorem B1308219 : Blo 1307972 1308219 := bstep (se 1 (by rfl) ⟨981164, by rfl⟩ : syracuseStep 1308219 = 1962329) B1962329
theorem B1308295 : Blo 1307972 1308295 := bstep (se 1 (by rfl) ⟨981221, by rfl⟩ : syracuseStep 1308295 = 1962443) B1962443
theorem B1963655 : Blo 1307972 1963655 := bstep (se 1 (by rfl) ⟨1472741, by rfl⟩ : syracuseStep 1963655 = 2945483) B2945483
theorem B1308303 : Blo 1307972 1308303 := bstep (se 1 (by rfl) ⟨981227, by rfl⟩ : syracuseStep 1308303 = 1962455) B1962455
theorem B1472143 : Blo 1307972 1472143 := bstep (se 1 (by rfl) ⟨1104107, by rfl⟩ : syracuseStep 1472143 = 2208215) B2208215
theorem B2946707 : Blo 1307972 2946707 := bstep (se 1 (by rfl) ⟨2210030, by rfl⟩ : syracuseStep 2946707 = 4420061) B4420061
theorem B1963691 : Blo 1307972 1963691 := bstep (se 1 (by rfl) ⟨1472768, by rfl⟩ : syracuseStep 1963691 = 2945537) B2945537
theorem B1308347 : Blo 1307972 1308347 := bstep (se 1 (by rfl) ⟨981260, by rfl⟩ : syracuseStep 1308347 = 1962521) B1962521
theorem B3536585 : Blo 1307972 3536585 := bstep (se 2 (by rfl) ⟨1326219, by rfl⟩ : syracuseStep 3536585 = 2652439) B2652439
theorem B1963721 : Blo 1307972 1963721 := bstep (se 2 (by rfl) ⟨736395, by rfl⟩ : syracuseStep 1963721 = 1472791) B1472791
theorem B2946761 : Blo 1307972 2946761 := bstep (se 2 (by rfl) ⟨1105035, by rfl⟩ : syracuseStep 2946761 = 2210071) B2210071
theorem B3315401 : Blo 1307972 3315401 := bstep (se 2 (by rfl) ⟨1243275, by rfl⟩ : syracuseStep 3315401 = 2486551) B2486551
theorem B1308423 : Blo 1307972 1308423 := bstep (se 1 (by rfl) ⟨981317, by rfl⟩ : syracuseStep 1308423 = 1962635) B1962635
theorem B1308431 : Blo 1307972 1308431 := bstep (se 1 (by rfl) ⟨981323, by rfl⟩ : syracuseStep 1308431 = 1962647) B1962647
theorem B7452431 : Blo 1307972 7452431 := bstep (se 1 (by rfl) ⟨5589323, by rfl⟩ : syracuseStep 7452431 = 11178647) B11178647
theorem B3725099 : Blo 1307972 3725099 := bstep (se 1 (by rfl) ⟨2793824, by rfl⟩ : syracuseStep 3725099 = 5587649) B5587649
theorem B1308475 : Blo 1307972 1308475 := bstep (se 1 (by rfl) ⟨981356, by rfl⟩ : syracuseStep 1308475 = 1962713) B1962713
theorem B4478779 : Blo 1307972 4478779 := bstep (se 1 (by rfl) ⟨3359084, by rfl⟩ : syracuseStep 4478779 = 6718169) B6718169
theorem B1963835 : Blo 1307972 1963835 := bstep (se 1 (by rfl) ⟨1472876, by rfl⟩ : syracuseStep 1963835 = 2945753) B2945753
theorem B1963895 : Blo 1307972 1963895 := bstep (se 1 (by rfl) ⟨1472921, by rfl⟩ : syracuseStep 1963895 = 2945843) B2945843
theorem B1308551 : Blo 1307972 1308551 := bstep (se 1 (by rfl) ⟨981413, by rfl⟩ : syracuseStep 1308551 = 1962827) B1962827
theorem B1308559 : Blo 1307972 1308559 := bstep (se 1 (by rfl) ⟨981419, by rfl⟩ : syracuseStep 1308559 = 1962839) B1962839
theorem B1963919 : Blo 1307972 1963919 := bstep (se 1 (by rfl) ⟨1472939, by rfl⟩ : syracuseStep 1963919 = 2945879) B2945879
theorem B5592979 : Blo 1307972 5592979 := bstep (se 1 (by rfl) ⟨4194734, by rfl⟩ : syracuseStep 5592979 = 8389469) B8389469
theorem B14161817 : Blo 1307972 14161817 := bstep (se 2 (by rfl) ⟨5310681, by rfl⟩ : syracuseStep 14161817 = 10621363) B10621363
theorem B1963961 : Blo 1307972 1963961 := bstep (se 2 (by rfl) ⟨736485, by rfl⟩ : syracuseStep 1963961 = 1472971) B1472971
theorem B1308603 : Blo 1307972 1308603 := bstep (se 1 (by rfl) ⟨981452, by rfl⟩ : syracuseStep 1308603 = 1962905) B1962905
theorem B1308679 : Blo 1307972 1308679 := bstep (se 1 (by rfl) ⟨981509, by rfl⟩ : syracuseStep 1308679 = 1963019) B1963019
theorem B1964039 : Blo 1307972 1964039 := bstep (se 1 (by rfl) ⟨1473029, by rfl⟩ : syracuseStep 1964039 = 2946059) B2946059
theorem B4782091 : Blo 1307972 4782091 := bstep (se 1 (by rfl) ⟨3586568, by rfl⟩ : syracuseStep 4782091 = 7173137) B7173137
theorem B3725327 : Blo 1307972 3725327 := bstep (se 1 (by rfl) ⟨2793995, by rfl⟩ : syracuseStep 3725327 = 5587991) B5587991
theorem B1308687 : Blo 1307972 1308687 := bstep (se 1 (by rfl) ⟨981515, by rfl⟩ : syracuseStep 1308687 = 1963031) B1963031
theorem B16766999 : Blo 1307972 16766999 := bstep (se 1 (by rfl) ⟨12575249, by rfl⟩ : syracuseStep 16766999 = 25150499) B25150499
theorem B1964075 : Blo 1307972 1964075 := bstep (se 1 (by rfl) ⟨1473056, by rfl⟩ : syracuseStep 1964075 = 2946113) B2946113
theorem B2209835 : Blo 1307972 2209835 := bstep (se 1 (by rfl) ⟨1657376, by rfl⟩ : syracuseStep 2209835 = 3314753) B3314753
theorem B1308731 : Blo 1307972 1308731 := bstep (se 1 (by rfl) ⟨981548, by rfl⟩ : syracuseStep 1308731 = 1963097) B1963097
theorem B1964105 : Blo 1307972 1964105 := bstep (se 2 (by rfl) ⟨736539, by rfl⟩ : syracuseStep 1964105 = 1473079) B1473079
theorem B1308807 : Blo 1307972 1308807 := bstep (se 1 (by rfl) ⟨981605, by rfl⟩ : syracuseStep 1308807 = 1963211) B1963211
theorem B1472647 : Blo 1307972 1472647 := bstep (se 1 (by rfl) ⟨1104485, by rfl⟩ : syracuseStep 1472647 = 2208971) B2208971
theorem B1308815 : Blo 1307972 1308815 := bstep (se 1 (by rfl) ⟨981611, by rfl⟩ : syracuseStep 1308815 = 1963223) B1963223
theorem B15931565 : Blo 1307972 15931565 := bstep (se 3 (by rfl) ⟨2987168, by rfl⟩ : syracuseStep 15931565 = 5974337) B5974337
theorem B1308859 : Blo 1307972 1308859 := bstep (se 1 (by rfl) ⟨981644, by rfl⟩ : syracuseStep 1308859 = 1963289) B1963289
theorem B1964219 : Blo 1307972 1964219 := bstep (se 1 (by rfl) ⟨1473164, by rfl⟩ : syracuseStep 1964219 = 2946329) B2946329
theorem B1964279 : Blo 1307972 1964279 := bstep (se 1 (by rfl) ⟨1473209, by rfl⟩ : syracuseStep 1964279 = 2946419) B2946419
theorem B1308935 : Blo 1307972 1308935 := bstep (se 1 (by rfl) ⟨981701, by rfl⟩ : syracuseStep 1308935 = 1963403) B1963403
theorem B1308943 : Blo 1307972 1308943 := bstep (se 1 (by rfl) ⟨981707, by rfl⟩ : syracuseStep 1308943 = 1963415) B1963415
theorem B1964303 : Blo 1307972 1964303 := bstep (se 1 (by rfl) ⟨1473227, by rfl⟩ : syracuseStep 1964303 = 2946455) B2946455
theorem B1964345 : Blo 1307972 1964345 := bstep (se 2 (by rfl) ⟨736629, by rfl⟩ : syracuseStep 1964345 = 1473259) B1473259
theorem B1308987 : Blo 1307972 1308987 := bstep (se 1 (by rfl) ⟨981740, by rfl⟩ : syracuseStep 1308987 = 1963481) B1963481
theorem B1472827 : Blo 1307972 1472827 := bstep (se 1 (by rfl) ⟨1104620, by rfl⟩ : syracuseStep 1472827 = 2209241) B2209241
theorem B1309063 : Blo 1307972 1309063 := bstep (se 1 (by rfl) ⟨981797, by rfl⟩ : syracuseStep 1309063 = 1963595) B1963595
theorem B1964423 : Blo 1307972 1964423 := bstep (se 1 (by rfl) ⟨1473317, by rfl⟩ : syracuseStep 1964423 = 2946635) B2946635
theorem B1309071 : Blo 1307972 1309071 := bstep (se 1 (by rfl) ⟨981803, by rfl⟩ : syracuseStep 1309071 = 1963607) B1963607
theorem B5970323 : Blo 1307972 5970323 := bstep (se 1 (by rfl) ⟨4477742, by rfl⟩ : syracuseStep 5970323 = 8955485) B8955485
theorem B1964459 : Blo 1307972 1964459 := bstep (se 1 (by rfl) ⟨1473344, by rfl⟩ : syracuseStep 1964459 = 2946689) B2946689
theorem B2210233 : Blo 1307972 2210233 := bstep (se 2 (by rfl) ⟨828837, by rfl⟩ : syracuseStep 2210233 = 1657675) B1657675
theorem B1309115 : Blo 1307972 1309115 := bstep (se 1 (by rfl) ⟨981836, by rfl⟩ : syracuseStep 1309115 = 1963673) B1963673
theorem B1964489 : Blo 1307972 1964489 := bstep (se 2 (by rfl) ⟨736683, by rfl⟩ : syracuseStep 1964489 = 1473367) B1473367
theorem B1309191 : Blo 1307972 1309191 := bstep (se 1 (by rfl) ⟨981893, by rfl⟩ : syracuseStep 1309191 = 1963787) B1963787
theorem B1309199 : Blo 1307972 1309199 := bstep (se 1 (by rfl) ⟨981899, by rfl⟩ : syracuseStep 1309199 = 1963799) B1963799
theorem B6289949 : Blo 1307972 6289949 := bstep (se 3 (by rfl) ⟨1179365, by rfl⟩ : syracuseStep 6289949 = 2358731) B2358731
theorem B1309243 : Blo 1307972 1309243 := bstep (se 1 (by rfl) ⟨981932, by rfl⟩ : syracuseStep 1309243 = 1963865) B1963865
theorem B1964603 : Blo 1307972 1964603 := bstep (se 1 (by rfl) ⟨1473452, by rfl⟩ : syracuseStep 1964603 = 2946905) B2946905
theorem B1964663 : Blo 1307972 1964663 := bstep (se 1 (by rfl) ⟨1473497, by rfl⟩ : syracuseStep 1964663 = 2946995) B2946995
theorem B1309319 : Blo 1307972 1309319 := bstep (se 1 (by rfl) ⟨981989, by rfl⟩ : syracuseStep 1309319 = 1963979) B1963979
theorem B1309327 : Blo 1307972 1309327 := bstep (se 1 (by rfl) ⟨981995, by rfl⟩ : syracuseStep 1309327 = 1963991) B1963991
theorem B1964687 : Blo 1307972 1964687 := bstep (se 1 (by rfl) ⟨1473515, by rfl⟩ : syracuseStep 1964687 = 2947031) B2947031
theorem B1964729 : Blo 1307972 1964729 := bstep (se 2 (by rfl) ⟨736773, by rfl⟩ : syracuseStep 1964729 = 1473547) B1473547
theorem B1309371 : Blo 1307972 1309371 := bstep (se 1 (by rfl) ⟨982028, by rfl⟩ : syracuseStep 1309371 = 1964057) B1964057
theorem B1309447 : Blo 1307972 1309447 := bstep (se 1 (by rfl) ⟨982085, by rfl⟩ : syracuseStep 1309447 = 1964171) B1964171
theorem B1964807 : Blo 1307972 1964807 := bstep (se 1 (by rfl) ⟨1473605, by rfl⟩ : syracuseStep 1964807 = 2947211) B2947211
theorem B1571599 : Blo 1307972 1571599 := bstep (se 1 (by rfl) ⟨1178699, by rfl⟩ : syracuseStep 1571599 = 2357399) B2357399
theorem B1309455 : Blo 1307972 1309455 := bstep (se 1 (by rfl) ⟨982091, by rfl⟩ : syracuseStep 1309455 = 1964183) B1964183
theorem B1473295 : Blo 1307972 1473295 := bstep (se 1 (by rfl) ⟨1104971, by rfl⟩ : syracuseStep 1473295 = 2209943) B2209943
theorem B1964843 : Blo 1307972 1964843 := bstep (se 1 (by rfl) ⟨1473632, by rfl⟩ : syracuseStep 1964843 = 2947265) B2947265
theorem B1309499 : Blo 1307972 1309499 := bstep (se 1 (by rfl) ⟨982124, by rfl⟩ : syracuseStep 1309499 = 1964249) B1964249
theorem B1964873 : Blo 1307972 1964873 := bstep (se 2 (by rfl) ⟨736827, by rfl⟩ : syracuseStep 1964873 = 1473655) B1473655
theorem B3537751 : Blo 1307972 3537751 := bstep (se 1 (by rfl) ⟨2653313, by rfl⟩ : syracuseStep 3537751 = 5306627) B5306627
theorem B1309575 : Blo 1307972 1309575 := bstep (se 1 (by rfl) ⟨982181, by rfl⟩ : syracuseStep 1309575 = 1964363) B1964363
theorem B1309583 : Blo 1307972 1309583 := bstep (se 1 (by rfl) ⟨982187, by rfl⟩ : syracuseStep 1309583 = 1964375) B1964375
theorem B1309627 : Blo 1307972 1309627 := bstep (se 1 (by rfl) ⟨982220, by rfl⟩ : syracuseStep 1309627 = 1964441) B1964441
theorem B1309703 : Blo 1307972 1309703 := bstep (se 1 (by rfl) ⟨982277, by rfl⟩ : syracuseStep 1309703 = 1964555) B1964555
theorem B1309711 : Blo 1307972 1309711 := bstep (se 1 (by rfl) ⟨982283, by rfl⟩ : syracuseStep 1309711 = 1964567) B1964567
theorem B1309755 : Blo 1307972 1309755 := bstep (se 1 (by rfl) ⟨982316, by rfl⟩ : syracuseStep 1309755 = 1964633) B1964633
theorem B1309831 : Blo 1307972 1309831 := bstep (se 1 (by rfl) ⟨982373, by rfl⟩ : syracuseStep 1309831 = 1964747) B1964747
theorem B1309839 : Blo 1307972 1309839 := bstep (se 1 (by rfl) ⟨982379, by rfl⟩ : syracuseStep 1309839 = 1964759) B1964759
theorem B1309883 : Blo 1307972 1309883 := bstep (se 1 (by rfl) ⟨982412, by rfl⟩ : syracuseStep 1309883 = 1964825) B1964825
theorem B7453889 : Blo 1307972 7453889 := bstep (se 2 (by rfl) ⟨2795208, by rfl⟩ : syracuseStep 7453889 = 5590417) B5590417
theorem B1572103 : Blo 1307972 1572103 := bstep (se 1 (by rfl) ⟨1179077, by rfl⟩ : syracuseStep 1572103 = 2358155) B2358155
theorem B1309959 : Blo 1307972 1309959 := bstep (se 1 (by rfl) ⟨982469, by rfl⟩ : syracuseStep 1309959 = 1964939) B1964939
theorem B3980555 : Blo 1307972 3980555 := bstep (se 1 (by rfl) ⟨2985416, by rfl⟩ : syracuseStep 3980555 = 5970833) B5970833
theorem B1309967 : Blo 1307972 1309967 := bstep (se 1 (by rfl) ⟨982475, by rfl⟩ : syracuseStep 1309967 = 1964951) B1964951
theorem B14146849 : Blo 1307972 14146849 := bstep (se 2 (by rfl) ⟨5305068, by rfl⟩ : syracuseStep 14146849 = 10610137) B10610137
theorem B1989931 : Blo 1307972 1989931 := bstep (se 1 (by rfl) ⟨1492448, by rfl⟩ : syracuseStep 1989931 = 2984897) B2984897
theorem B5594483 : Blo 1307972 5594483 := bstep (se 1 (by rfl) ⟨4195862, by rfl⟩ : syracuseStep 5594483 = 8391725) B8391725
theorem B3726739 : Blo 1307972 3726739 := bstep (se 1 (by rfl) ⟨2795054, by rfl⟩ : syracuseStep 3726739 = 5590109) B5590109
theorem B3726967 : Blo 1307972 3726967 := bstep (se 1 (by rfl) ⟨2795225, by rfl⟩ : syracuseStep 3726967 = 5590451) B5590451
theorem B2358919 : Blo 1307972 2358919 := bstep (se 1 (by rfl) ⟨1769189, by rfl⟩ : syracuseStep 2358919 = 3538379) B3538379
theorem B3145351 : Blo 1307972 3145351 := bstep (se 1 (by rfl) ⟨2359013, by rfl⟩ : syracuseStep 3145351 = 4718027) B4718027
theorem B5594825 : Blo 1307972 5594825 := bstep (se 2 (by rfl) ⟨2098059, by rfl⟩ : syracuseStep 5594825 = 4196119) B4196119
theorem B3538703 : Blo 1307972 3538703 := bstep (se 1 (by rfl) ⟨2654027, by rfl⟩ : syracuseStep 3538703 = 5308055) B5308055
theorem B122543923 : Blo 1307972 122543923 := bstep (se 1 (by rfl) ⟨91907942, by rfl⟩ : syracuseStep 122543923 = 183815885) B183815885
theorem B9936755 : Blo 1307972 9936755 := bstep (se 1 (by rfl) ⟨7452566, by rfl⟩ : syracuseStep 9936755 = 14905133) B14905133
theorem B4415417 : Blo 1307972 4415417 := bstep (se 2 (by rfl) ⟨1655781, by rfl⟩ : syracuseStep 4415417 = 3311563) B3311563
theorem B6627257 : Blo 1307972 6627257 := bstep (se 2 (by rfl) ⟨2485221, by rfl⟩ : syracuseStep 6627257 = 4970443) B4970443
theorem B5595065 : Blo 1307972 5595065 := bstep (se 2 (by rfl) ⟨2098149, by rfl⟩ : syracuseStep 5595065 = 4196299) B4196299
theorem B3727367 : Blo 1307972 3727367 := bstep (se 1 (by rfl) ⟨2795525, by rfl⟩ : syracuseStep 3727367 = 5591051) B5591051
theorem B36790295 : Blo 1307972 36790295 := bstep (se 1 (by rfl) ⟨27592721, by rfl⟩ : syracuseStep 36790295 = 55185443) B55185443
theorem B5587001 : Blo 1307972 5587001 := bstep (se 2 (by rfl) ⟨2095125, by rfl⟩ : syracuseStep 5587001 = 4190251) B4190251
theorem B4481081 : Blo 1307972 4481081 := bstep (se 2 (by rfl) ⟨1680405, by rfl⟩ : syracuseStep 4481081 = 3360811) B3360811
theorem B2359625 : Blo 1307972 2359625 := bstep (se 2 (by rfl) ⟨884859, by rfl⟩ : syracuseStep 2359625 = 1769719) B1769719
theorem B4415849 : Blo 1307972 4415849 := bstep (se 2 (by rfl) ⟨1655943, by rfl⟩ : syracuseStep 4415849 = 3311887) B3311887
theorem B11174273 : Blo 1307972 11174273 := bstep (se 2 (by rfl) ⟨4190352, by rfl⟩ : syracuseStep 11174273 = 8380705) B8380705
theorem B8381063 : Blo 1307972 8381063 := bstep (se 1 (by rfl) ⟨6285797, by rfl⟩ : syracuseStep 8381063 = 12571595) B12571595
theorem B9437897 : Blo 1307972 9437897 := bstep (se 2 (by rfl) ⟨3539211, by rfl⟩ : syracuseStep 9437897 = 7078423) B7078423
theorem B3146455 : Blo 1307972 3146455 := bstep (se 1 (by rfl) ⟨2359841, by rfl⟩ : syracuseStep 3146455 = 4719683) B4719683
theorem B4195145 : Blo 1307972 4195145 := bstep (se 2 (by rfl) ⟨1573179, by rfl⟩ : syracuseStep 4195145 = 3146359) B3146359
theorem B4416443 : Blo 1307972 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B17916875 : Blo 1307972 17916875 := bstep (se 1 (by rfl) ⟨13437656, by rfl⟩ : syracuseStep 17916875 = 26875313) B26875313
theorem B2483399 : Blo 1307972 2483399 := bstep (se 1 (by rfl) ⟨1862549, by rfl⟩ : syracuseStep 2483399 = 3725099) B3725099
theorem B9938213 : Blo 1307972 9938213 := bstep (se 4 (by rfl) ⟨931707, by rfl⟩ : syracuseStep 9938213 = 1863415) B1863415
theorem B2483551 : Blo 1307972 2483551 := bstep (se 1 (by rfl) ⟨1862663, by rfl⟩ : syracuseStep 2483551 = 3725327) B3725327
theorem B4195709 : Blo 1307972 4195709 := bstep (se 3 (by rfl) ⟨786695, by rfl⟩ : syracuseStep 4195709 = 1573391) B1573391
theorem B1656283 : Blo 1307972 1656283 := bstep (se 1 (by rfl) ⟨1242212, by rfl⟩ : syracuseStep 1656283 = 2484425) B2484425
theorem B14910965 : Blo 1307972 14910965 := bstep (se 5 (by rfl) ⟨698951, by rfl⟩ : syracuseStep 14910965 = 1397903) B1397903
theorem B3311543 : Blo 1307972 3311543 := bstep (se 1 (by rfl) ⟨2483657, by rfl⟩ : syracuseStep 3311543 = 4967315) B4967315
theorem B7456805 : Blo 1307972 7456805 := bstep (se 4 (by rfl) ⟨699075, by rfl⟩ : syracuseStep 7456805 = 1398151) B1398151
theorem B3729655 : Blo 1307972 3729655 := bstep (se 1 (by rfl) ⟨2797241, by rfl⟩ : syracuseStep 3729655 = 5594483) B5594483
theorem B3361015 : Blo 1307972 3361015 := bstep (se 1 (by rfl) ⟨2520761, by rfl⟩ : syracuseStep 3361015 = 5041523) B5041523
theorem B9439537 : Blo 1307972 9439537 := bstep (se 2 (by rfl) ⟨3539826, by rfl⟩ : syracuseStep 9439537 = 7079653) B7079653
theorem B3828097 : Blo 1307972 3828097 := bstep (se 2 (by rfl) ⟨1435536, by rfl⟩ : syracuseStep 3828097 = 2871073) B2871073
theorem B163391897 : Blo 1307972 163391897 := bstep (se 2 (by rfl) ⟨61271961, by rfl⟩ : syracuseStep 163391897 = 122543923) B122543923
theorem B3729883 : Blo 1307972 3729883 := bstep (se 1 (by rfl) ⟨2797412, by rfl⟩ : syracuseStep 3729883 = 5594825) B5594825
theorem B16779757 : Blo 1307972 16779757 := bstep (se 3 (by rfl) ⟨3146204, by rfl⟩ : syracuseStep 16779757 = 6292409) B6292409
theorem B7457305 : Blo 1307972 7457305 := bstep (se 2 (by rfl) ⟨2796489, by rfl⟩ : syracuseStep 7457305 = 5592979) B5592979
theorem B2943611 : Blo 1307972 2943611 := bstep (se 1 (by rfl) ⟨2207708, by rfl⟩ : syracuseStep 2943611 = 4415417) B4415417
theorem B4418171 : Blo 1307972 4418171 := bstep (se 1 (by rfl) ⟨3313628, by rfl⟩ : syracuseStep 4418171 = 6627257) B6627257
theorem B3730043 : Blo 1307972 3730043 := bstep (se 1 (by rfl) ⟨2797532, by rfl⟩ : syracuseStep 3730043 = 5595065) B5595065
theorem B6376121 : Blo 1307972 6376121 := bstep (se 2 (by rfl) ⟨2391045, by rfl⟩ : syracuseStep 6376121 = 4782091) B4782091
theorem B2943737 : Blo 1307972 2943737 := bstep (se 2 (by rfl) ⟨1103901, by rfl⟩ : syracuseStep 2943737 = 2207803) B2207803
theorem B4418333 : Blo 1307972 4418333 := bstep (se 3 (by rfl) ⟨828437, by rfl⟩ : syracuseStep 4418333 = 1656875) B1656875
theorem B6630173 : Blo 1307972 6630173 := bstep (se 3 (by rfl) ⟨1243157, by rfl⟩ : syracuseStep 6630173 = 2486315) B2486315
theorem B3730283 : Blo 1307972 3730283 := bstep (se 1 (by rfl) ⟨2797712, by rfl⟩ : syracuseStep 3730283 = 5595425) B5595425
theorem B2944007 : Blo 1307972 2944007 := bstep (se 1 (by rfl) ⟨2208005, by rfl⟩ : syracuseStep 2944007 = 4416011) B4416011
theorem B3312647 : Blo 1307972 3312647 := bstep (se 1 (by rfl) ⟨2484485, by rfl⟩ : syracuseStep 3312647 = 4968971) B4968971
theorem B3312697 : Blo 1307972 3312697 := bstep (se 2 (by rfl) ⟨1242261, by rfl⟩ : syracuseStep 3312697 = 2484523) B2484523
theorem B3779641 : Blo 1307972 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B2944079 : Blo 1307972 2944079 := bstep (se 1 (by rfl) ⟨2208059, by rfl⟩ : syracuseStep 2944079 = 4416119) B4416119
theorem B2485495 : Blo 1307972 2485495 := bstep (se 1 (by rfl) ⟨1864121, by rfl⟩ : syracuseStep 2485495 = 3728243) B3728243
theorem B22351139 : Blo 1307972 22351139 := bstep (se 1 (by rfl) ⟨16763354, by rfl⟩ : syracuseStep 22351139 = 33526709) B33526709
theorem B3313001 : Blo 1307972 3313001 := bstep (se 2 (by rfl) ⟨1242375, by rfl⟩ : syracuseStep 3313001 = 2484751) B2484751
theorem B2944475 : Blo 1307972 2944475 := bstep (se 1 (by rfl) ⟨2208356, by rfl⟩ : syracuseStep 2944475 = 4416713) B4416713
theorem B4419035 : Blo 1307972 4419035 := bstep (se 1 (by rfl) ⟨3314276, by rfl⟩ : syracuseStep 4419035 = 6628553) B6628553
theorem B2485723 : Blo 1307972 2485723 := bstep (se 1 (by rfl) ⟨1864292, by rfl⟩ : syracuseStep 2485723 = 3728585) B3728585
theorem B367586819 : Blo 1307972 367586819 := bstep (se 1 (by rfl) ⟨275690114, by rfl⟩ : syracuseStep 367586819 = 551380229) B551380229
theorem B2485799 : Blo 1307972 2485799 := bstep (se 1 (by rfl) ⟨1864349, by rfl⟩ : syracuseStep 2485799 = 3728699) B3728699
theorem B4476539 : Blo 1307972 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B2485883 : Blo 1307972 2485883 := bstep (se 1 (by rfl) ⟨1864412, by rfl⟩ : syracuseStep 2485883 = 3728825) B3728825
theorem B8392339 : Blo 1307972 8392339 := bstep (se 1 (by rfl) ⟨6294254, by rfl⟩ : syracuseStep 8392339 = 12588509) B12588509
theorem B42430169 : Blo 1307972 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B2207479 : Blo 1307972 2207479 := bstep (se 1 (by rfl) ⟨1655609, by rfl⟩ : syracuseStep 2207479 = 3311219) B3311219
theorem B4968287 : Blo 1307972 4968287 := bstep (se 1 (by rfl) ⟨3726215, by rfl⟩ : syracuseStep 4968287 = 7452431) B7452431
theorem B2944943 : Blo 1307972 2944943 := bstep (se 1 (by rfl) ⟨2208707, by rfl⟩ : syracuseStep 2944943 = 4417415) B4417415
theorem B2207675 : Blo 1307972 2207675 := bstep (se 1 (by rfl) ⟨1655756, by rfl⟩ : syracuseStep 2207675 = 3311513) B3311513
theorem B9441211 : Blo 1307972 9441211 := bstep (se 1 (by rfl) ⟨7080908, by rfl⟩ : syracuseStep 9441211 = 14161817) B14161817
theorem B1863643 : Blo 1307972 1863643 := bstep (se 1 (by rfl) ⟨1397732, by rfl⟩ : syracuseStep 1863643 = 2795465) B2795465
theorem B1961993 : Blo 1307972 1961993 := bstep (se 2 (by rfl) ⟨735747, by rfl⟩ : syracuseStep 1961993 = 1471495) B1471495
theorem B6287375 : Blo 1307972 6287375 := bstep (se 1 (by rfl) ⟨4715531, by rfl⟩ : syracuseStep 6287375 = 9431063) B9431063
theorem B11177999 : Blo 1307972 11177999 := bstep (se 1 (by rfl) ⟨8383499, by rfl⟩ : syracuseStep 11177999 = 16766999) B16766999
theorem B1962023 : Blo 1307972 1962023 := bstep (se 1 (by rfl) ⟨1471517, by rfl⟩ : syracuseStep 1962023 = 2943035) B2943035
theorem B2207783 : Blo 1307972 2207783 := bstep (se 1 (by rfl) ⟨1655837, by rfl⟩ : syracuseStep 2207783 = 3311675) B3311675
theorem B2486369 : Blo 1307972 2486369 := bstep (se 2 (by rfl) ⟨932388, by rfl⟩ : syracuseStep 2486369 = 1864777) B1864777
theorem B10621043 : Blo 1307972 10621043 := bstep (se 1 (by rfl) ⟨7965782, by rfl⟩ : syracuseStep 10621043 = 15931565) B15931565
theorem B1962107 : Blo 1307972 1962107 := bstep (se 1 (by rfl) ⟨1471580, by rfl⟩ : syracuseStep 1962107 = 2943161) B2943161
theorem B4419737 : Blo 1307972 4419737 := bstep (se 2 (by rfl) ⟨1657401, by rfl⟩ : syracuseStep 4419737 = 3314803) B3314803
theorem B2945195 : Blo 1307972 2945195 := bstep (se 1 (by rfl) ⟨2208896, by rfl⟩ : syracuseStep 2945195 = 4417793) B4417793
theorem B1962233 : Blo 1307972 1962233 := bstep (se 2 (by rfl) ⟨735837, by rfl⟩ : syracuseStep 1962233 = 1471675) B1471675
theorem B2208073 : Blo 1307972 2208073 := bstep (se 2 (by rfl) ⟨828027, by rfl⟩ : syracuseStep 2208073 = 1656055) B1656055
theorem B1962335 : Blo 1307972 1962335 := bstep (se 1 (by rfl) ⟨1471751, by rfl⟩ : syracuseStep 1962335 = 2943503) B2943503
theorem B1962347 : Blo 1307972 1962347 := bstep (se 1 (by rfl) ⟨1471760, by rfl⟩ : syracuseStep 1962347 = 2943521) B2943521
theorem B2208107 : Blo 1307972 2208107 := bstep (se 1 (by rfl) ⟨1656080, by rfl⟩ : syracuseStep 2208107 = 3312161) B3312161
theorem B18862465 : Blo 1307972 18862465 := bstep (se 2 (by rfl) ⟨7073424, by rfl⟩ : syracuseStep 18862465 = 14146849) B14146849
theorem B4968985 : Blo 1307972 4968985 := bstep (se 2 (by rfl) ⟨1863369, by rfl⟩ : syracuseStep 4968985 = 3726739) B3726739
theorem B7074337 : Blo 1307972 7074337 := bstep (se 2 (by rfl) ⟨2652876, by rfl⟩ : syracuseStep 7074337 = 5305753) B5305753
theorem B11186747 : Blo 1307972 11186747 := bstep (se 1 (by rfl) ⟨8390060, by rfl⟩ : syracuseStep 11186747 = 16780121) B16780121
theorem B1962575 : Blo 1307972 1962575 := bstep (se 1 (by rfl) ⟨1471931, by rfl⟩ : syracuseStep 1962575 = 2943863) B2943863
theorem B4715155 : Blo 1307972 4715155 := bstep (se 1 (by rfl) ⟨3536366, by rfl⟩ : syracuseStep 4715155 = 7072733) B7072733
theorem B1962695 : Blo 1307972 1962695 := bstep (se 1 (by rfl) ⟨1472021, by rfl⟩ : syracuseStep 1962695 = 2944043) B2944043
theorem B2945735 : Blo 1307972 2945735 := bstep (se 1 (by rfl) ⟨2209301, by rfl⟩ : syracuseStep 2945735 = 4418603) B4418603
theorem B2208505 : Blo 1307972 2208505 := bstep (se 2 (by rfl) ⟨828189, by rfl⟩ : syracuseStep 2208505 = 1656379) B1656379
theorem B4969259 : Blo 1307972 4969259 := bstep (se 1 (by rfl) ⟨3726944, by rfl⟩ : syracuseStep 4969259 = 7453889) B7453889
theorem B4969289 : Blo 1307972 4969289 := bstep (se 2 (by rfl) ⟨1863483, by rfl⟩ : syracuseStep 4969289 = 3726967) B3726967
theorem B1962857 : Blo 1307972 1962857 := bstep (se 2 (by rfl) ⟨736071, by rfl⟩ : syracuseStep 1962857 = 1472143) B1472143
theorem B1962935 : Blo 1307972 1962935 := bstep (se 1 (by rfl) ⟨1472201, by rfl⟩ : syracuseStep 1962935 = 2944403) B2944403
theorem B1962971 : Blo 1307972 1962971 := bstep (se 1 (by rfl) ⟨1472228, by rfl⟩ : syracuseStep 1962971 = 2944457) B2944457
theorem B2208775 : Blo 1307972 2208775 := bstep (se 1 (by rfl) ⟨1656581, by rfl⟩ : syracuseStep 2208775 = 3313163) B3313163
theorem B53744705 : Blo 1307972 53744705 := bstep (se 2 (by rfl) ⟨20154264, by rfl⟩ : syracuseStep 53744705 = 40308529) B40308529
theorem B1471567 : Blo 1307972 1471567 := bstep (se 1 (by rfl) ⟨1103675, by rfl⟩ : syracuseStep 1471567 = 2207351) B2207351
theorem B96859223 : Blo 1307972 96859223 := bstep (se 1 (by rfl) ⟨72644417, by rfl⟩ : syracuseStep 96859223 = 145288835) B145288835
theorem B6624503 : Blo 1307972 6624503 := bstep (se 1 (by rfl) ⟨4968377, by rfl⟩ : syracuseStep 6624503 = 9936755) B9936755
theorem B4420925 : Blo 1307972 4420925 := bstep (se 3 (by rfl) ⟨828923, by rfl⟩ : syracuseStep 4420925 = 1657847) B1657847
theorem B1307983 : Blo 1307972 1307983 := bstep (se 1 (by rfl) ⟨980987, by rfl⟩ : syracuseStep 1307983 = 1961975) B1961975
theorem B1307999 : Blo 1307972 1307999 := bstep (se 1 (by rfl) ⟨980999, by rfl⟩ : syracuseStep 1307999 = 1961999) B1961999
theorem B1308027 : Blo 1307972 1308027 := bstep (se 1 (by rfl) ⟨981020, by rfl⟩ : syracuseStep 1308027 = 1962041) B1962041
theorem B7460221 : Blo 1307972 7460221 := bstep (se 3 (by rfl) ⟨1398791, by rfl⟩ : syracuseStep 7460221 = 2797583) B2797583
theorem B3028367 : Blo 1307972 3028367 := bstep (se 1 (by rfl) ⟨2271275, by rfl⟩ : syracuseStep 3028367 = 4542551) B4542551
theorem B1308079 : Blo 1307972 1308079 := bstep (se 1 (by rfl) ⟨981059, by rfl⟩ : syracuseStep 1308079 = 1962119) B1962119
theorem B1963439 : Blo 1307972 1963439 := bstep (se 1 (by rfl) ⟨1472579, by rfl⟩ : syracuseStep 1963439 = 2945159) B2945159
theorem B2209207 : Blo 1307972 2209207 := bstep (se 1 (by rfl) ⟨1656905, by rfl⟩ : syracuseStep 2209207 = 3313811) B3313811
theorem B1308103 : Blo 1307972 1308103 := bstep (se 1 (by rfl) ⟨981077, by rfl⟩ : syracuseStep 1308103 = 1962155) B1962155
theorem B1308123 : Blo 1307972 1308123 := bstep (se 1 (by rfl) ⟨981092, by rfl⟩ : syracuseStep 1308123 = 1962185) B1962185
theorem B1471963 : Blo 1307972 1471963 := bstep (se 1 (by rfl) ⟨1103972, by rfl⟩ : syracuseStep 1471963 = 2207945) B2207945
theorem B1963529 : Blo 1307972 1963529 := bstep (se 2 (by rfl) ⟨736323, by rfl⟩ : syracuseStep 1963529 = 1472647) B1472647
theorem B3143207 : Blo 1307972 3143207 := bstep (se 1 (by rfl) ⟨2357405, by rfl⟩ : syracuseStep 3143207 = 4714811) B4714811
theorem B1308199 : Blo 1307972 1308199 := bstep (se 1 (by rfl) ⟨981149, by rfl⟩ : syracuseStep 1308199 = 1962299) B1962299
theorem B1963559 : Blo 1307972 1963559 := bstep (se 1 (by rfl) ⟨1472669, by rfl⟩ : syracuseStep 1963559 = 2945339) B2945339
theorem B2946599 : Blo 1307972 2946599 := bstep (se 1 (by rfl) ⟨2209949, by rfl⟩ : syracuseStep 2946599 = 4419899) B4419899
theorem B3315239 : Blo 1307972 3315239 := bstep (se 1 (by rfl) ⟨2486429, by rfl⟩ : syracuseStep 3315239 = 4972859) B4972859
theorem B1308239 : Blo 1307972 1308239 := bstep (se 1 (by rfl) ⟨981179, by rfl⟩ : syracuseStep 1308239 = 1962359) B1962359
theorem B1308255 : Blo 1307972 1308255 := bstep (se 1 (by rfl) ⟨981191, by rfl⟩ : syracuseStep 1308255 = 1962383) B1962383
theorem B1308283 : Blo 1307972 1308283 := bstep (se 1 (by rfl) ⟨981212, by rfl⟩ : syracuseStep 1308283 = 1962425) B1962425
theorem B1963643 : Blo 1307972 1963643 := bstep (se 1 (by rfl) ⟨1472732, by rfl⟩ : syracuseStep 1963643 = 2945465) B2945465
theorem B2209403 : Blo 1307972 2209403 := bstep (se 1 (by rfl) ⟨1657052, by rfl⟩ : syracuseStep 2209403 = 3314105) B3314105
theorem B1308335 : Blo 1307972 1308335 := bstep (se 1 (by rfl) ⟨981251, by rfl⟩ : syracuseStep 1308335 = 1962503) B1962503
theorem B9557693 : Blo 1307972 9557693 := bstep (se 3 (by rfl) ⟨1792067, by rfl⟩ : syracuseStep 9557693 = 3584135) B3584135
theorem B1308359 : Blo 1307972 1308359 := bstep (se 1 (by rfl) ⟨981269, by rfl⟩ : syracuseStep 1308359 = 1962539) B1962539
theorem B1308379 : Blo 1307972 1308379 := bstep (se 1 (by rfl) ⟨981284, by rfl⟩ : syracuseStep 1308379 = 1962569) B1962569
theorem B6624989 : Blo 1307972 6624989 := bstep (se 3 (by rfl) ⟨1242185, by rfl⟩ : syracuseStep 6624989 = 2484371) B2484371
theorem B1963769 : Blo 1307972 1963769 := bstep (se 2 (by rfl) ⟨736413, by rfl⟩ : syracuseStep 1963769 = 1472827) B1472827
theorem B1308455 : Blo 1307972 1308455 := bstep (se 1 (by rfl) ⟨981341, by rfl⟩ : syracuseStep 1308455 = 1962683) B1962683
theorem B1308495 : Blo 1307972 1308495 := bstep (se 1 (by rfl) ⟨981371, by rfl⟩ : syracuseStep 1308495 = 1962743) B1962743
theorem B1308511 : Blo 1307972 1308511 := bstep (se 1 (by rfl) ⟨981383, by rfl⟩ : syracuseStep 1308511 = 1962767) B1962767
theorem B1963871 : Blo 1307972 1963871 := bstep (se 1 (by rfl) ⟨1472903, by rfl⟩ : syracuseStep 1963871 = 2945807) B2945807
theorem B1963883 : Blo 1307972 1963883 := bstep (se 1 (by rfl) ⟨1472912, by rfl⟩ : syracuseStep 1963883 = 2945825) B2945825
theorem B2946923 : Blo 1307972 2946923 := bstep (se 1 (by rfl) ⟨2210192, by rfl⟩ : syracuseStep 2946923 = 4420385) B4420385
theorem B3315563 : Blo 1307972 3315563 := bstep (se 1 (by rfl) ⟨2486672, by rfl⟩ : syracuseStep 3315563 = 4973345) B4973345
theorem B1308539 : Blo 1307972 1308539 := bstep (se 1 (by rfl) ⟨981404, by rfl⟩ : syracuseStep 1308539 = 1962809) B1962809
theorem B2946977 : Blo 1307972 2946977 := bstep (se 2 (by rfl) ⟨1105116, by rfl⟩ : syracuseStep 2946977 = 2210233) B2210233
theorem B1308591 : Blo 1307972 1308591 := bstep (se 1 (by rfl) ⟨981443, by rfl⟩ : syracuseStep 1308591 = 1962887) B1962887
theorem B1472431 : Blo 1307972 1472431 := bstep (se 1 (by rfl) ⟨1104323, by rfl⟩ : syracuseStep 1472431 = 2208647) B2208647
theorem B1308615 : Blo 1307972 1308615 := bstep (se 1 (by rfl) ⟨981461, by rfl⟩ : syracuseStep 1308615 = 1962923) B1962923
theorem B1308635 : Blo 1307972 1308635 := bstep (se 1 (by rfl) ⟨981476, by rfl⟩ : syracuseStep 1308635 = 1962953) B1962953
theorem B2209801 : Blo 1307972 2209801 := bstep (se 2 (by rfl) ⟨828675, by rfl⟩ : syracuseStep 2209801 = 1657351) B1657351
theorem B1308711 : Blo 1307972 1308711 := bstep (se 1 (by rfl) ⟨981533, by rfl⟩ : syracuseStep 1308711 = 1963067) B1963067
theorem B1308751 : Blo 1307972 1308751 := bstep (se 1 (by rfl) ⟨981563, by rfl⟩ : syracuseStep 1308751 = 1963127) B1963127
theorem B1964111 : Blo 1307972 1964111 := bstep (se 1 (by rfl) ⟨1473083, by rfl⟩ : syracuseStep 1964111 = 2946167) B2946167
theorem B1308767 : Blo 1307972 1308767 := bstep (se 1 (by rfl) ⟨981575, by rfl⟩ : syracuseStep 1308767 = 1963151) B1963151
theorem B14899301 : Blo 1307972 14899301 := bstep (se 4 (by rfl) ⟨1396809, by rfl⟩ : syracuseStep 14899301 = 2793619) B2793619
theorem B1308795 : Blo 1307972 1308795 := bstep (se 1 (by rfl) ⟨981596, by rfl⟩ : syracuseStep 1308795 = 1963193) B1963193
theorem B2209963 : Blo 1307972 2209963 := bstep (se 1 (by rfl) ⟨1657472, by rfl⟩ : syracuseStep 2209963 = 3314945) B3314945
theorem B1308847 : Blo 1307972 1308847 := bstep (se 1 (by rfl) ⟨981635, by rfl⟩ : syracuseStep 1308847 = 1963271) B1963271
theorem B1308871 : Blo 1307972 1308871 := bstep (se 1 (by rfl) ⟨981653, by rfl⟩ : syracuseStep 1308871 = 1963307) B1963307
theorem B1964231 : Blo 1307972 1964231 := bstep (se 1 (by rfl) ⟨1473173, by rfl⟩ : syracuseStep 1964231 = 2946347) B2946347
theorem B1308891 : Blo 1307972 1308891 := bstep (se 1 (by rfl) ⟨981668, by rfl⟩ : syracuseStep 1308891 = 1963337) B1963337
theorem B2947319 : Blo 1307972 2947319 := bstep (se 1 (by rfl) ⟨2210489, by rfl⟩ : syracuseStep 2947319 = 4420979) B4420979
theorem B7076107 : Blo 1307972 7076107 := bstep (se 1 (by rfl) ⟨5307080, by rfl⟩ : syracuseStep 7076107 = 10614161) B10614161
theorem B1308967 : Blo 1307972 1308967 := bstep (se 1 (by rfl) ⟨981725, by rfl⟩ : syracuseStep 1308967 = 1963451) B1963451
theorem B1309007 : Blo 1307972 1309007 := bstep (se 1 (by rfl) ⟨981755, by rfl⟩ : syracuseStep 1309007 = 1963511) B1963511
theorem B1309023 : Blo 1307972 1309023 := bstep (se 1 (by rfl) ⟨981767, by rfl⟩ : syracuseStep 1309023 = 1963535) B1963535
theorem B1472863 : Blo 1307972 1472863 := bstep (se 1 (by rfl) ⟨1104647, by rfl⟩ : syracuseStep 1472863 = 2209295) B2209295
theorem B2095465 : Blo 1307972 2095465 := bstep (se 2 (by rfl) ⟨785799, by rfl⟩ : syracuseStep 2095465 = 1571599) B1571599
theorem B1964393 : Blo 1307972 1964393 := bstep (se 2 (by rfl) ⟨736647, by rfl⟩ : syracuseStep 1964393 = 1473295) B1473295
theorem B1309051 : Blo 1307972 1309051 := bstep (se 1 (by rfl) ⟨981788, by rfl⟩ : syracuseStep 1309051 = 1963577) B1963577
theorem B1309103 : Blo 1307972 1309103 := bstep (se 1 (by rfl) ⟨981827, by rfl⟩ : syracuseStep 1309103 = 1963655) B1963655
theorem B1964471 : Blo 1307972 1964471 := bstep (se 1 (by rfl) ⟨1473353, by rfl⟩ : syracuseStep 1964471 = 2946707) B2946707
theorem B1309127 : Blo 1307972 1309127 := bstep (se 1 (by rfl) ⟨981845, by rfl⟩ : syracuseStep 1309127 = 1963691) B1963691
theorem B4717001 : Blo 1307972 4717001 := bstep (se 2 (by rfl) ⟨1768875, by rfl⟩ : syracuseStep 4717001 = 3537751) B3537751
theorem B2357723 : Blo 1307972 2357723 := bstep (se 1 (by rfl) ⟨1768292, by rfl⟩ : syracuseStep 2357723 = 3536585) B3536585
theorem B1309147 : Blo 1307972 1309147 := bstep (se 1 (by rfl) ⟨981860, by rfl⟩ : syracuseStep 1309147 = 1963721) B1963721
theorem B1964507 : Blo 1307972 1964507 := bstep (se 1 (by rfl) ⟨1473380, by rfl⟩ : syracuseStep 1964507 = 2946761) B2946761
theorem B2210267 : Blo 1307972 2210267 := bstep (se 1 (by rfl) ⟨1657700, by rfl⟩ : syracuseStep 2210267 = 3315401) B3315401
theorem B1309223 : Blo 1307972 1309223 := bstep (se 1 (by rfl) ⟨981917, by rfl⟩ : syracuseStep 1309223 = 1963835) B1963835
theorem B1309263 : Blo 1307972 1309263 := bstep (se 1 (by rfl) ⟨981947, by rfl⟩ : syracuseStep 1309263 = 1963895) B1963895
theorem B1309279 : Blo 1307972 1309279 := bstep (se 1 (by rfl) ⟨981959, by rfl⟩ : syracuseStep 1309279 = 1963919) B1963919
theorem B1309307 : Blo 1307972 1309307 := bstep (se 1 (by rfl) ⟨981980, by rfl⟩ : syracuseStep 1309307 = 1963961) B1963961
theorem B1309359 : Blo 1307972 1309359 := bstep (se 1 (by rfl) ⟨982019, by rfl⟩ : syracuseStep 1309359 = 1964039) B1964039
theorem B1309383 : Blo 1307972 1309383 := bstep (se 1 (by rfl) ⟨982037, by rfl⟩ : syracuseStep 1309383 = 1964075) B1964075
theorem B1473223 : Blo 1307972 1473223 := bstep (se 1 (by rfl) ⟨1104917, by rfl⟩ : syracuseStep 1473223 = 2209835) B2209835
theorem B2210503 : Blo 1307972 2210503 := bstep (se 1 (by rfl) ⟨1657877, by rfl⟩ : syracuseStep 2210503 = 3315755) B3315755
theorem B5249747 : Blo 1307972 5249747 := bstep (se 1 (by rfl) ⟨3937310, by rfl⟩ : syracuseStep 5249747 = 7874621) B7874621
theorem B1309403 : Blo 1307972 1309403 := bstep (se 1 (by rfl) ⟨982052, by rfl⟩ : syracuseStep 1309403 = 1964105) B1964105
theorem B1309479 : Blo 1307972 1309479 := bstep (se 1 (by rfl) ⟨982109, by rfl⟩ : syracuseStep 1309479 = 1964219) B1964219
theorem B1309519 : Blo 1307972 1309519 := bstep (se 1 (by rfl) ⟨982139, by rfl⟩ : syracuseStep 1309519 = 1964279) B1964279
theorem B38255449 : Blo 1307972 38255449 := bstep (se 2 (by rfl) ⟨14345793, by rfl⟩ : syracuseStep 38255449 = 28691587) B28691587
theorem B1309535 : Blo 1307972 1309535 := bstep (se 1 (by rfl) ⟨982151, by rfl⟩ : syracuseStep 1309535 = 1964303) B1964303
theorem B1309563 : Blo 1307972 1309563 := bstep (se 1 (by rfl) ⟨982172, by rfl⟩ : syracuseStep 1309563 = 1964345) B1964345
theorem B1309615 : Blo 1307972 1309615 := bstep (se 1 (by rfl) ⟨982211, by rfl⟩ : syracuseStep 1309615 = 1964423) B1964423
theorem B3980215 : Blo 1307972 3980215 := bstep (se 1 (by rfl) ⟨2985161, by rfl⟩ : syracuseStep 3980215 = 5970323) B5970323
theorem B1309639 : Blo 1307972 1309639 := bstep (se 1 (by rfl) ⟨982229, by rfl⟩ : syracuseStep 1309639 = 1964459) B1964459
theorem B1309659 : Blo 1307972 1309659 := bstep (se 1 (by rfl) ⟨982244, by rfl⟩ : syracuseStep 1309659 = 1964489) B1964489
theorem B23886821 : Blo 1307972 23886821 := bstep (se 4 (by rfl) ⟨2239389, by rfl⟩ : syracuseStep 23886821 = 4478779) B4478779
theorem B2096137 : Blo 1307972 2096137 := bstep (se 2 (by rfl) ⟨786051, by rfl⟩ : syracuseStep 2096137 = 1572103) B1572103
theorem B4193299 : Blo 1307972 4193299 := bstep (se 1 (by rfl) ⟨3144974, by rfl⟩ : syracuseStep 4193299 = 6289949) B6289949
theorem B1309735 : Blo 1307972 1309735 := bstep (se 1 (by rfl) ⟨982301, by rfl⟩ : syracuseStep 1309735 = 1964603) B1964603
theorem B2653241 : Blo 1307972 2653241 := bstep (se 2 (by rfl) ⟨994965, by rfl⟩ : syracuseStep 2653241 = 1989931) B1989931
theorem B1309775 : Blo 1307972 1309775 := bstep (se 1 (by rfl) ⟨982331, by rfl⟩ : syracuseStep 1309775 = 1964663) B1964663
theorem B1309791 : Blo 1307972 1309791 := bstep (se 1 (by rfl) ⟨982343, by rfl⟩ : syracuseStep 1309791 = 1964687) B1964687
theorem B1309819 : Blo 1307972 1309819 := bstep (se 1 (by rfl) ⟨982364, by rfl⟩ : syracuseStep 1309819 = 1964729) B1964729
theorem B1309871 : Blo 1307972 1309871 := bstep (se 1 (by rfl) ⟨982403, by rfl⟩ : syracuseStep 1309871 = 1964807) B1964807
theorem B1309895 : Blo 1307972 1309895 := bstep (se 1 (by rfl) ⟨982421, by rfl⟩ : syracuseStep 1309895 = 1964843) B1964843
theorem B1309915 : Blo 1307972 1309915 := bstep (se 1 (by rfl) ⟨982436, by rfl⟩ : syracuseStep 1309915 = 1964873) B1964873
theorem B12270937 : Blo 1307972 12270937 := bstep (se 2 (by rfl) ⟨4601601, by rfl⟩ : syracuseStep 12270937 = 9203203) B9203203
theorem B4971901 : Blo 1307972 4971901 := bstep (se 3 (by rfl) ⟨932231, by rfl⟩ : syracuseStep 4971901 = 1864463) B1864463
theorem B2653703 : Blo 1307972 2653703 := bstep (se 1 (by rfl) ⟨1990277, by rfl⟩ : syracuseStep 2653703 = 3980555) B3980555
theorem B4414985 : Blo 1307972 4414985 := bstep (se 2 (by rfl) ⟨1655619, by rfl⟩ : syracuseStep 4414985 = 3311239) B3311239
theorem B3145225 : Blo 1307972 3145225 := bstep (se 2 (by rfl) ⟨1179459, by rfl⟩ : syracuseStep 3145225 = 2358919) B2358919
theorem B4193801 : Blo 1307972 4193801 := bstep (se 2 (by rfl) ⟨1572675, by rfl⟩ : syracuseStep 4193801 = 3145351) B3145351
theorem B2359135 : Blo 1307972 2359135 := bstep (se 1 (by rfl) ⟨1769351, by rfl⟩ : syracuseStep 2359135 = 3538703) B3538703
theorem B9945017 : Blo 1307972 9945017 := bstep (se 2 (by rfl) ⟨3729381, by rfl⟩ : syracuseStep 9945017 = 7458763) B7458763
theorem B98107453 : Blo 1307972 98107453 := bstep (se 3 (by rfl) ⟨18395147, by rfl⟩ : syracuseStep 98107453 = 36790295) B36790295
theorem B22364261 : Blo 1307972 22364261 := bstep (se 4 (by rfl) ⟨2096649, by rfl⟩ : syracuseStep 22364261 = 4193299) B4193299
theorem B4972873 : Blo 1307972 4972873 := bstep (se 2 (by rfl) ⟨1864827, by rfl⟩ : syracuseStep 4972873 = 3729655) B3729655
theorem B4481353 : Blo 1307972 4481353 := bstep (se 2 (by rfl) ⟨1680507, by rfl⟩ : syracuseStep 4481353 = 3361015) B3361015
theorem B5587375 : Blo 1307972 5587375 := bstep (se 1 (by rfl) ⟨4190531, by rfl⟩ : syracuseStep 5587375 = 8381063) B8381063
theorem B6291931 : Blo 1307972 6291931 := bstep (se 1 (by rfl) ⟨4718948, by rfl⟩ : syracuseStep 6291931 = 9437897) B9437897
theorem B2793953 : Blo 1307972 2793953 := bstep (se 2 (by rfl) ⟨1047732, by rfl⟩ : syracuseStep 2793953 = 2095465) B2095465
theorem B5104129 : Blo 1307972 5104129 := bstep (se 2 (by rfl) ⟨1914048, by rfl⟩ : syracuseStep 5104129 = 3828097) B3828097
theorem B25149953 : Blo 1307972 25149953 := bstep (se 2 (by rfl) ⟨9431232, by rfl⟩ : syracuseStep 25149953 = 18862465) B18862465
theorem B4973177 : Blo 1307972 4973177 := bstep (se 2 (by rfl) ⟨1864941, by rfl⟩ : syracuseStep 4973177 = 3729883) B3729883
theorem B11944583 : Blo 1307972 11944583 := bstep (se 1 (by rfl) ⟨8958437, by rfl⟩ : syracuseStep 11944583 = 17916875) B17916875
theorem B22373009 : Blo 1307972 22373009 := bstep (se 2 (by rfl) ⟨8389878, by rfl⟩ : syracuseStep 22373009 = 16779757) B16779757
theorem B4416335 : Blo 1307972 4416335 := bstep (se 1 (by rfl) ⟨3312251, by rfl⟩ : syracuseStep 4416335 = 6624503) B6624503
theorem B6292333 : Blo 1307972 6292333 := bstep (se 3 (by rfl) ⟨1179812, by rfl⟩ : syracuseStep 6292333 = 2359625) B2359625
theorem B4416659 : Blo 1307972 4416659 := bstep (se 1 (by rfl) ⟨3312494, by rfl⟩ : syracuseStep 4416659 = 6624989) B6624989
theorem B4416929 : Blo 1307972 4416929 := bstep (se 2 (by rfl) ⟨1656348, by rfl⟩ : syracuseStep 4416929 = 3312697) B3312697
theorem B16361249 : Blo 1307972 16361249 := bstep (se 2 (by rfl) ⟨6135468, by rfl⟩ : syracuseStep 16361249 = 12270937) B12270937
theorem B3311401 : Blo 1307972 3311401 := bstep (se 2 (by rfl) ⟨1241775, by rfl⟩ : syracuseStep 3311401 = 2483551) B2483551
theorem B3499831 : Blo 1307972 3499831 := bstep (se 1 (by rfl) ⟨2624873, by rfl⟩ : syracuseStep 3499831 = 5249747) B5249747
theorem B6629201 : Blo 1307972 6629201 := bstep (se 2 (by rfl) ⟨2485950, by rfl⟩ : syracuseStep 6629201 = 4971901) B4971901
theorem B9946961 : Blo 1307972 9946961 := bstep (se 2 (by rfl) ⟨3730110, by rfl⟩ : syracuseStep 9946961 = 7460221) B7460221
theorem B2943305 : Blo 1307972 2943305 := bstep (se 2 (by rfl) ⟨1103739, by rfl⟩ : syracuseStep 2943305 = 2207479) B2207479
theorem B245057879 : Blo 1307972 245057879 := bstep (se 1 (by rfl) ⟨183793409, by rfl⟩ : syracuseStep 245057879 = 367586819) B367586819
theorem B2943323 : Blo 1307972 2943323 := bstep (se 1 (by rfl) ⟨2207492, by rfl⟩ : syracuseStep 2943323 = 4414985) B4414985
theorem B2795867 : Blo 1307972 2795867 := bstep (se 1 (by rfl) ⟨2096900, by rfl⟩ : syracuseStep 2795867 = 4193801) B4193801
theorem B1657199 : Blo 1307972 1657199 := bstep (se 1 (by rfl) ⟨1242899, by rfl⟩ : syracuseStep 1657199 = 2485799) B2485799
theorem B2984359 : Blo 1307972 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B1657255 : Blo 1307972 1657255 := bstep (se 1 (by rfl) ⟨1242941, by rfl⟩ : syracuseStep 1657255 = 2485883) B2485883
theorem B3312191 : Blo 1307972 3312191 := bstep (se 1 (by rfl) ⟨2484143, by rfl⟩ : syracuseStep 3312191 = 4968287) B4968287
theorem B2484857 : Blo 1307972 2484857 := bstep (se 2 (by rfl) ⟨931821, by rfl⟩ : syracuseStep 2484857 = 1863643) B1863643
theorem B6630011 : Blo 1307972 6630011 := bstep (se 1 (by rfl) ⟨4972508, by rfl⟩ : syracuseStep 6630011 = 9945017) B9945017
theorem B2484911 : Blo 1307972 2484911 := bstep (se 1 (by rfl) ⟨1863683, by rfl⟩ : syracuseStep 2484911 = 3727367) B3727367
theorem B1657579 : Blo 1307972 1657579 := bstep (se 1 (by rfl) ⟨1243184, by rfl⟩ : syracuseStep 1657579 = 2486369) B2486369
theorem B7080695 : Blo 1307972 7080695 := bstep (se 1 (by rfl) ⟨5310521, by rfl⟩ : syracuseStep 7080695 = 10621043) B10621043
theorem B2943899 : Blo 1307972 2943899 := bstep (se 1 (by rfl) ⟨2207924, by rfl⟩ : syracuseStep 2943899 = 4415849) B4415849
theorem B7449515 : Blo 1307972 7449515 := bstep (se 1 (by rfl) ⟨5587136, by rfl⟩ : syracuseStep 7449515 = 11174273) B11174273
theorem B7457831 : Blo 1307972 7457831 := bstep (se 1 (by rfl) ⟨5593373, by rfl⟩ : syracuseStep 7457831 = 11186747) B11186747
theorem B12586049 : Blo 1307972 12586049 := bstep (se 2 (by rfl) ⟨4719768, by rfl⟩ : syracuseStep 12586049 = 9439537) B9439537
theorem B2944097 : Blo 1307972 2944097 := bstep (se 2 (by rfl) ⟨1104036, by rfl⟩ : syracuseStep 2944097 = 2208073) B2208073
theorem B6622397 : Blo 1307972 6622397 := bstep (se 3 (by rfl) ⟨1241699, by rfl⟩ : syracuseStep 6622397 = 2483399) B2483399
theorem B3312839 : Blo 1307972 3312839 := bstep (se 1 (by rfl) ⟨2484629, by rfl⟩ : syracuseStep 3312839 = 4969259) B4969259
theorem B3312859 : Blo 1307972 3312859 := bstep (se 1 (by rfl) ⟨2484644, by rfl⟩ : syracuseStep 3312859 = 4969289) B4969289
theorem B2796763 : Blo 1307972 2796763 := bstep (se 1 (by rfl) ⟨2097572, by rfl⟩ : syracuseStep 2796763 = 4195145) B4195145
theorem B2944295 : Blo 1307972 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B9432449 : Blo 1307972 9432449 := bstep (se 2 (by rfl) ⟨3537168, by rfl⟩ : syracuseStep 9432449 = 7074337) B7074337
theorem B64572815 : Blo 1307972 64572815 := bstep (se 1 (by rfl) ⟨48429611, by rfl⟩ : syracuseStep 64572815 = 96859223) B96859223
theorem B2797139 : Blo 1307972 2797139 := bstep (se 1 (by rfl) ⟨2097854, by rfl⟩ : syracuseStep 2797139 = 4195709) B4195709
theorem B2944673 : Blo 1307972 2944673 := bstep (se 2 (by rfl) ⟨1104252, by rfl⟩ : syracuseStep 2944673 = 2208505) B2208505
theorem B9940643 : Blo 1307972 9940643 := bstep (se 1 (by rfl) ⟨7455482, by rfl⟩ : syracuseStep 9940643 = 14910965) B14910965
theorem B51007265 : Blo 1307972 51007265 := bstep (se 2 (by rfl) ⟨19127724, by rfl⟩ : syracuseStep 51007265 = 38255449) B38255449
theorem B16781093 : Blo 1307972 16781093 := bstep (se 4 (by rfl) ⟨1573227, by rfl⟩ : syracuseStep 16781093 = 3146455) B3146455
theorem B2207695 : Blo 1307972 2207695 := bstep (se 1 (by rfl) ⟨1655771, by rfl⟩ : syracuseStep 2207695 = 3311543) B3311543
theorem B2945033 : Blo 1307972 2945033 := bstep (se 2 (by rfl) ⟨1104387, by rfl⟩ : syracuseStep 2945033 = 2208775) B2208775
theorem B9932867 : Blo 1307972 9932867 := bstep (se 1 (by rfl) ⟨7449650, by rfl⟩ : syracuseStep 9932867 = 14899301) B14899301
theorem B1962089 : Blo 1307972 1962089 := bstep (se 2 (by rfl) ⟨735783, by rfl⟩ : syracuseStep 1962089 = 1471567) B1471567
theorem B3313993 : Blo 1307972 3313993 := bstep (se 2 (by rfl) ⟨1242747, by rfl⟩ : syracuseStep 3313993 = 2485495) B2485495
theorem B1962407 : Blo 1307972 1962407 := bstep (se 1 (by rfl) ⟨1471805, by rfl⟩ : syracuseStep 1962407 = 2943611) B2943611
theorem B2945447 : Blo 1307972 2945447 := bstep (se 1 (by rfl) ⟨2209085, by rfl⟩ : syracuseStep 2945447 = 4418171) B4418171
theorem B2486695 : Blo 1307972 2486695 := bstep (se 1 (by rfl) ⟨1865021, by rfl⟩ : syracuseStep 2486695 = 3730043) B3730043
theorem B1962491 : Blo 1307972 1962491 := bstep (se 1 (by rfl) ⟨1471868, by rfl⟩ : syracuseStep 1962491 = 2943737) B2943737
theorem B2945555 : Blo 1307972 2945555 := bstep (se 1 (by rfl) ⟨2209166, by rfl⟩ : syracuseStep 2945555 = 4418333) B4418333
theorem B4420115 : Blo 1307972 4420115 := bstep (se 1 (by rfl) ⟨3315086, by rfl⟩ : syracuseStep 4420115 = 6630173) B6630173
theorem B2486855 : Blo 1307972 2486855 := bstep (se 1 (by rfl) ⟨1865141, by rfl⟩ : syracuseStep 2486855 = 3730283) B3730283
theorem B2945609 : Blo 1307972 2945609 := bstep (se 2 (by rfl) ⟨1104603, by rfl⟩ : syracuseStep 2945609 = 2209207) B2209207
theorem B1962617 : Blo 1307972 1962617 := bstep (se 2 (by rfl) ⟨735981, by rfl⟩ : syracuseStep 1962617 = 1471963) B1471963
theorem B2208377 : Blo 1307972 2208377 := bstep (se 2 (by rfl) ⟨828141, by rfl⟩ : syracuseStep 2208377 = 1656283) B1656283
theorem B3314297 : Blo 1307972 3314297 := bstep (se 2 (by rfl) ⟨1242861, by rfl⟩ : syracuseStep 3314297 = 2485723) B2485723
theorem B1962671 : Blo 1307972 1962671 := bstep (se 1 (by rfl) ⟨1472003, by rfl⟩ : syracuseStep 1962671 = 2944007) B2944007
theorem B2208431 : Blo 1307972 2208431 := bstep (se 1 (by rfl) ⟨1656323, by rfl⟩ : syracuseStep 2208431 = 3312647) B3312647
theorem B1962719 : Blo 1307972 1962719 := bstep (se 1 (by rfl) ⟨1472039, by rfl⟩ : syracuseStep 1962719 = 2944079) B2944079
theorem B2208667 : Blo 1307972 2208667 := bstep (se 1 (by rfl) ⟨1656500, by rfl⟩ : syracuseStep 2208667 = 3313001) B3313001
theorem B1962983 : Blo 1307972 1962983 := bstep (se 1 (by rfl) ⟨1472237, by rfl⟩ : syracuseStep 1962983 = 2944475) B2944475
theorem B2946023 : Blo 1307972 2946023 := bstep (se 1 (by rfl) ⟨2209517, by rfl⟩ : syracuseStep 2946023 = 4419035) B4419035
theorem B1963241 : Blo 1307972 1963241 := bstep (se 2 (by rfl) ⟨736215, by rfl⟩ : syracuseStep 1963241 = 1472431) B1472431
theorem B12588281 : Blo 1307972 12588281 := bstep (se 2 (by rfl) ⟨4720605, by rfl⟩ : syracuseStep 12588281 = 9441211) B9441211
theorem B1963295 : Blo 1307972 1963295 := bstep (se 1 (by rfl) ⟨1472471, by rfl⟩ : syracuseStep 1963295 = 2944943) B2944943
theorem B1471783 : Blo 1307972 1471783 := bstep (se 1 (by rfl) ⟨1103837, by rfl⟩ : syracuseStep 1471783 = 2207675) B2207675
theorem B1307995 : Blo 1307972 1307995 := bstep (se 1 (by rfl) ⟨980996, by rfl⟩ : syracuseStep 1307995 = 1961993) B1961993
theorem B4191583 : Blo 1307972 4191583 := bstep (se 1 (by rfl) ⟨3143687, by rfl⟩ : syracuseStep 4191583 = 6287375) B6287375
theorem B7451999 : Blo 1307972 7451999 := bstep (se 1 (by rfl) ⟨5588999, by rfl⟩ : syracuseStep 7451999 = 11177999) B11177999
theorem B2946401 : Blo 1307972 2946401 := bstep (se 2 (by rfl) ⟨1104900, by rfl⟩ : syracuseStep 2946401 = 2209801) B2209801
theorem B1308015 : Blo 1307972 1308015 := bstep (se 1 (by rfl) ⟨981011, by rfl⟩ : syracuseStep 1308015 = 1962023) B1962023
theorem B1471855 : Blo 1307972 1471855 := bstep (se 1 (by rfl) ⟨1103891, by rfl⟩ : syracuseStep 1471855 = 2207783) B2207783
theorem B3724667 : Blo 1307972 3724667 := bstep (se 1 (by rfl) ⟨2793500, by rfl⟩ : syracuseStep 3724667 = 5587001) B5587001
theorem B2987387 : Blo 1307972 2987387 := bstep (se 1 (by rfl) ⟨2240540, by rfl⟩ : syracuseStep 2987387 = 4481081) B4481081
theorem B11179397 : Blo 1307972 11179397 := bstep (se 4 (by rfl) ⟨1048068, by rfl⟩ : syracuseStep 11179397 = 2096137) B2096137
theorem B1308071 : Blo 1307972 1308071 := bstep (se 1 (by rfl) ⟨981053, by rfl⟩ : syracuseStep 1308071 = 1962107) B1962107
theorem B2946491 : Blo 1307972 2946491 := bstep (se 1 (by rfl) ⟨2209868, by rfl⟩ : syracuseStep 2946491 = 4419737) B4419737
theorem B1963463 : Blo 1307972 1963463 := bstep (se 1 (by rfl) ⟨1472597, by rfl⟩ : syracuseStep 1963463 = 2945195) B2945195
theorem B1308155 : Blo 1307972 1308155 := bstep (se 1 (by rfl) ⟨981116, by rfl⟩ : syracuseStep 1308155 = 1962233) B1962233
theorem B2946617 : Blo 1307972 2946617 := bstep (se 2 (by rfl) ⟨1104981, by rfl⟩ : syracuseStep 2946617 = 2209963) B2209963
theorem B1308223 : Blo 1307972 1308223 := bstep (se 1 (by rfl) ⟨981167, by rfl⟩ : syracuseStep 1308223 = 1962335) B1962335
theorem B1308231 : Blo 1307972 1308231 := bstep (se 1 (by rfl) ⟨981173, by rfl⟩ : syracuseStep 1308231 = 1962347) B1962347
theorem B1472071 : Blo 1307972 1472071 := bstep (se 1 (by rfl) ⟨1104053, by rfl⟩ : syracuseStep 1472071 = 2208107) B2208107
theorem B20158085 : Blo 1307972 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B9434809 : Blo 1307972 9434809 := bstep (se 2 (by rfl) ⟨3538053, by rfl⟩ : syracuseStep 9434809 = 7076107) B7076107
theorem B1308383 : Blo 1307972 1308383 := bstep (se 1 (by rfl) ⟨981287, by rfl⟩ : syracuseStep 1308383 = 1962575) B1962575
theorem B1963817 : Blo 1307972 1963817 := bstep (se 2 (by rfl) ⟨736431, by rfl⟩ : syracuseStep 1963817 = 1472863) B1472863
theorem B1308463 : Blo 1307972 1308463 := bstep (se 1 (by rfl) ⟨981347, by rfl⟩ : syracuseStep 1308463 = 1962695) B1962695
theorem B1963823 : Blo 1307972 1963823 := bstep (se 1 (by rfl) ⟨1472867, by rfl⟩ : syracuseStep 1963823 = 2945735) B2945735
theorem B1308571 : Blo 1307972 1308571 := bstep (se 1 (by rfl) ⟨981428, by rfl⟩ : syracuseStep 1308571 = 1962857) B1962857
theorem B28301237 : Blo 1307972 28301237 := bstep (se 5 (by rfl) ⟨1326620, by rfl⟩ : syracuseStep 28301237 = 2653241) B2653241
theorem B1308623 : Blo 1307972 1308623 := bstep (se 1 (by rfl) ⟨981467, by rfl⟩ : syracuseStep 1308623 = 1962935) B1962935
theorem B1308647 : Blo 1307972 1308647 := bstep (se 1 (by rfl) ⟨981485, by rfl⟩ : syracuseStep 1308647 = 1962971) B1962971
theorem B6625313 : Blo 1307972 6625313 := bstep (se 2 (by rfl) ⟨2484492, by rfl⟩ : syracuseStep 6625313 = 4968985) B4968985
theorem B9943073 : Blo 1307972 9943073 := bstep (se 2 (by rfl) ⟨3728652, by rfl⟩ : syracuseStep 9943073 = 7457305) B7457305
theorem B35829803 : Blo 1307972 35829803 := bstep (se 1 (by rfl) ⟨26872352, by rfl⟩ : syracuseStep 35829803 = 53744705) B53744705
theorem B25147493 : Blo 1307972 25147493 := bstep (se 4 (by rfl) ⟨2357577, by rfl⟩ : syracuseStep 25147493 = 4715155) B4715155
theorem B6625475 : Blo 1307972 6625475 := bstep (se 1 (by rfl) ⟨4969106, by rfl⟩ : syracuseStep 6625475 = 9938213) B9938213
theorem B2947283 : Blo 1307972 2947283 := bstep (se 1 (by rfl) ⟨2210462, by rfl⟩ : syracuseStep 2947283 = 4420925) B4420925
theorem B1964297 : Blo 1307972 1964297 := bstep (se 2 (by rfl) ⟨736611, by rfl⟩ : syracuseStep 1964297 = 1473223) B1473223
theorem B2947337 : Blo 1307972 2947337 := bstep (se 2 (by rfl) ⟨1105251, by rfl⟩ : syracuseStep 2947337 = 2210503) B2210503
theorem B1308959 : Blo 1307972 1308959 := bstep (se 1 (by rfl) ⟨981719, by rfl⟩ : syracuseStep 1308959 = 1963439) B1963439
theorem B1309019 : Blo 1307972 1309019 := bstep (se 1 (by rfl) ⟨981764, by rfl⟩ : syracuseStep 1309019 = 1963529) B1963529
theorem B2095471 : Blo 1307972 2095471 := bstep (se 1 (by rfl) ⟨1571603, by rfl⟩ : syracuseStep 2095471 = 3143207) B3143207
theorem B1309039 : Blo 1307972 1309039 := bstep (se 1 (by rfl) ⟨981779, by rfl⟩ : syracuseStep 1309039 = 1963559) B1963559
theorem B1964399 : Blo 1307972 1964399 := bstep (se 1 (by rfl) ⟨1473299, by rfl⟩ : syracuseStep 1964399 = 2946599) B2946599
theorem B2210159 : Blo 1307972 2210159 := bstep (se 1 (by rfl) ⟨1657619, by rfl⟩ : syracuseStep 2210159 = 3315239) B3315239
theorem B8075645 : Blo 1307972 8075645 := bstep (se 3 (by rfl) ⟨1514183, by rfl⟩ : syracuseStep 8075645 = 3028367) B3028367
theorem B1309095 : Blo 1307972 1309095 := bstep (se 1 (by rfl) ⟨981821, by rfl⟩ : syracuseStep 1309095 = 1963643) B1963643
theorem B1472935 : Blo 1307972 1472935 := bstep (se 1 (by rfl) ⟨1104701, by rfl⟩ : syracuseStep 1472935 = 2209403) B2209403
theorem B6371795 : Blo 1307972 6371795 := bstep (se 1 (by rfl) ⟨4778846, by rfl⟩ : syracuseStep 6371795 = 9557693) B9557693
theorem B1309179 : Blo 1307972 1309179 := bstep (se 1 (by rfl) ⟨981884, by rfl⟩ : syracuseStep 1309179 = 1963769) B1963769
theorem B1309247 : Blo 1307972 1309247 := bstep (se 1 (by rfl) ⟨981935, by rfl⟩ : syracuseStep 1309247 = 1963871) B1963871
theorem B1309255 : Blo 1307972 1309255 := bstep (se 1 (by rfl) ⟨981941, by rfl⟩ : syracuseStep 1309255 = 1963883) B1963883
theorem B5306953 : Blo 1307972 5306953 := bstep (se 2 (by rfl) ⟨1990107, by rfl⟩ : syracuseStep 5306953 = 3980215) B3980215
theorem B1964615 : Blo 1307972 1964615 := bstep (se 1 (by rfl) ⟨1473461, by rfl⟩ : syracuseStep 1964615 = 2946923) B2946923
theorem B2210375 : Blo 1307972 2210375 := bstep (se 1 (by rfl) ⟨1657781, by rfl⟩ : syracuseStep 2210375 = 3315563) B3315563
theorem B1964651 : Blo 1307972 1964651 := bstep (se 1 (by rfl) ⟨1473488, by rfl⟩ : syracuseStep 1964651 = 2946977) B2946977
theorem B4971203 : Blo 1307972 4971203 := bstep (se 1 (by rfl) ⟨3728402, by rfl⟩ : syracuseStep 4971203 = 7456805) B7456805
theorem B1309407 : Blo 1307972 1309407 := bstep (se 1 (by rfl) ⟨982055, by rfl⟩ : syracuseStep 1309407 = 1964111) B1964111
theorem B1309487 : Blo 1307972 1309487 := bstep (se 1 (by rfl) ⟨982115, by rfl⟩ : syracuseStep 1309487 = 1964231) B1964231
theorem B1964879 : Blo 1307972 1964879 := bstep (se 1 (by rfl) ⟨1473659, by rfl⟩ : syracuseStep 1964879 = 2947319) B2947319
theorem B1309595 : Blo 1307972 1309595 := bstep (se 1 (by rfl) ⟨982196, by rfl⟩ : syracuseStep 1309595 = 1964393) B1964393
theorem B108927931 : Blo 1307972 108927931 := bstep (se 1 (by rfl) ⟨81695948, by rfl⟩ : syracuseStep 108927931 = 163391897) B163391897
theorem B1309647 : Blo 1307972 1309647 := bstep (se 1 (by rfl) ⟨982235, by rfl⟩ : syracuseStep 1309647 = 1964471) B1964471
theorem B3144667 : Blo 1307972 3144667 := bstep (se 1 (by rfl) ⟨2358500, by rfl⟩ : syracuseStep 3144667 = 4717001) B4717001
theorem B1571815 : Blo 1307972 1571815 := bstep (se 1 (by rfl) ⟨1178861, by rfl⟩ : syracuseStep 1571815 = 2357723) B2357723
theorem B1309671 : Blo 1307972 1309671 := bstep (se 1 (by rfl) ⟨982253, by rfl⟩ : syracuseStep 1309671 = 1964507) B1964507
theorem B1473511 : Blo 1307972 1473511 := bstep (se 1 (by rfl) ⟨1105133, by rfl⟩ : syracuseStep 1473511 = 2210267) B2210267
theorem B4250747 : Blo 1307972 4250747 := bstep (se 1 (by rfl) ⟨3188060, by rfl⟩ : syracuseStep 4250747 = 6376121) B6376121
theorem B12582053 : Blo 1307972 12582053 := bstep (se 4 (by rfl) ⟨1179567, by rfl⟩ : syracuseStep 12582053 = 2359135) B2359135
theorem B15924547 : Blo 1307972 15924547 := bstep (se 1 (by rfl) ⟨11943410, by rfl⟩ : syracuseStep 15924547 = 23886821) B23886821
theorem B4193633 : Blo 1307972 4193633 := bstep (se 2 (by rfl) ⟨1572612, by rfl⟩ : syracuseStep 4193633 = 3145225) B3145225
theorem B14900759 : Blo 1307972 14900759 := bstep (se 1 (by rfl) ⟨11175569, by rfl⟩ : syracuseStep 14900759 = 22351139) B22351139
theorem B11189785 : Blo 1307972 11189785 := bstep (se 2 (by rfl) ⟨4196169, by rfl⟩ : syracuseStep 11189785 = 8392339) B8392339
theorem B1769135 : Blo 1307972 1769135 := bstep (se 1 (by rfl) ⟨1326851, by rfl⟩ : syracuseStep 1769135 = 2653703) B2653703
theorem B28286779 : Blo 1307972 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B14909507 : Blo 1307972 14909507 := bstep (se 1 (by rfl) ⟨11182130, by rfl⟩ : syracuseStep 14909507 = 22364261) B22364261
theorem B130809937 : Blo 1307972 130809937 := bstep (se 2 (by rfl) ⟨49053726, by rfl⟩ : syracuseStep 130809937 = 98107453) B98107453
theorem B7963055 : Blo 1307972 7963055 := bstep (se 1 (by rfl) ⟨5972291, by rfl⟩ : syracuseStep 7963055 = 11944583) B11944583
theorem B2793961 : Blo 1307972 2793961 := bstep (se 2 (by rfl) ⟨1047735, by rfl⟩ : syracuseStep 2793961 = 2095471) B2095471
theorem B8389241 : Blo 1307972 8389241 := bstep (se 2 (by rfl) ⟨3145965, by rfl⟩ : syracuseStep 8389241 = 6291931) B6291931
theorem B2483111 : Blo 1307972 2483111 := bstep (se 1 (by rfl) ⟨1862333, by rfl⟩ : syracuseStep 2483111 = 3724667) B3724667
theorem B1991591 : Blo 1307972 1991591 := bstep (se 1 (by rfl) ⟨1493693, by rfl⟩ : syracuseStep 1991591 = 2987387) B2987387
theorem B11183021 : Blo 1307972 11183021 := bstep (se 3 (by rfl) ⟨2096816, by rfl⟩ : syracuseStep 11183021 = 4193633) B4193633
theorem B8389777 : Blo 1307972 8389777 := bstep (se 2 (by rfl) ⟨3146166, by rfl⟩ : syracuseStep 8389777 = 6292333) B6292333
theorem B16991453 : Blo 1307972 16991453 := bstep (se 3 (by rfl) ⟨3185897, by rfl⟩ : syracuseStep 16991453 = 6371795) B6371795
theorem B145237241 : Blo 1307972 145237241 := bstep (se 2 (by rfl) ⟨54463965, by rfl⟩ : syracuseStep 145237241 = 108927931) B108927931
theorem B18867491 : Blo 1307972 18867491 := bstep (se 1 (by rfl) ⟨14150618, by rfl⟩ : syracuseStep 18867491 = 28301237) B28301237
theorem B4416875 : Blo 1307972 4416875 := bstep (se 1 (by rfl) ⟨3312656, by rfl⟩ : syracuseStep 4416875 = 6625313) B6625313
theorem B6628715 : Blo 1307972 6628715 := bstep (se 1 (by rfl) ⟨4971536, by rfl⟩ : syracuseStep 6628715 = 9943073) B9943073
theorem B4416983 : Blo 1307972 4416983 := bstep (se 1 (by rfl) ⟨3312737, by rfl⟩ : syracuseStep 4416983 = 6625475) B6625475
theorem B5383763 : Blo 1307972 5383763 := bstep (se 1 (by rfl) ⟨4037822, by rfl⟩ : syracuseStep 5383763 = 8075645) B8075645
theorem B4417145 : Blo 1307972 4417145 := bstep (se 2 (by rfl) ⟨1656429, by rfl⟩ : syracuseStep 4417145 = 3312859) B3312859
theorem B3729017 : Blo 1307972 3729017 := bstep (se 2 (by rfl) ⟨1398381, by rfl⟩ : syracuseStep 3729017 = 2796763) B2796763
theorem B1656607 : Blo 1307972 1656607 := bstep (se 1 (by rfl) ⟨1242455, by rfl⟩ : syracuseStep 1656607 = 2484911) B2484911
theorem B5588777 : Blo 1307972 5588777 := bstep (se 2 (by rfl) ⟨2095791, by rfl⟩ : syracuseStep 5588777 = 4191583) B4191583
theorem B4720463 : Blo 1307972 4720463 := bstep (se 1 (by rfl) ⟨3540347, by rfl⟩ : syracuseStep 4720463 = 7080695) B7080695
theorem B4966343 : Blo 1307972 4966343 := bstep (se 1 (by rfl) ⟨3724757, by rfl⟩ : syracuseStep 4966343 = 7449515) B7449515
theorem B14919713 : Blo 1307972 14919713 := bstep (se 2 (by rfl) ⟨5594892, by rfl⟩ : syracuseStep 14919713 = 11189785) B11189785
theorem B8390699 : Blo 1307972 8390699 := bstep (se 1 (by rfl) ⟨6293024, by rfl⟩ : syracuseStep 8390699 = 12586049) B12586049
theorem B8383013 : Blo 1307972 8383013 := bstep (se 4 (by rfl) ⟨785907, by rfl⟩ : syracuseStep 8383013 = 1571815) B1571815
theorem B2943593 : Blo 1307972 2943593 := bstep (se 2 (by rfl) ⟨1103847, by rfl⟩ : syracuseStep 2943593 = 2207695) B2207695
theorem B6621911 : Blo 1307972 6621911 := bstep (se 1 (by rfl) ⟨4966433, by rfl⟩ : syracuseStep 6621911 = 9932867) B9932867
theorem B1657903 : Blo 1307972 1657903 := bstep (se 1 (by rfl) ⟨1243427, by rfl⟩ : syracuseStep 1657903 = 2486855) B2486855
theorem B4418657 : Blo 1307972 4418657 := bstep (se 2 (by rfl) ⟨1656996, by rfl⟩ : syracuseStep 4418657 = 3313993) B3313993
theorem B6630497 : Blo 1307972 6630497 := bstep (se 2 (by rfl) ⟨2486436, by rfl⟩ : syracuseStep 6630497 = 4972873) B4972873
theorem B5975137 : Blo 1307972 5975137 := bstep (se 2 (by rfl) ⟨2240676, by rfl⟩ : syracuseStep 5975137 = 4481353) B4481353
theorem B2944223 : Blo 1307972 2944223 := bstep (se 1 (by rfl) ⟨2208167, by rfl⟩ : syracuseStep 2944223 = 4416335) B4416335
theorem B7449833 : Blo 1307972 7449833 := bstep (se 2 (by rfl) ⟨2793687, by rfl⟩ : syracuseStep 7449833 = 5587375) B5587375
theorem B2944439 : Blo 1307972 2944439 := bstep (se 1 (by rfl) ⟨2208329, by rfl⟩ : syracuseStep 2944439 = 4416659) B4416659
theorem B8392187 : Blo 1307972 8392187 := bstep (se 1 (by rfl) ⟨6294140, by rfl⟩ : syracuseStep 8392187 = 12588281) B12588281
theorem B4967999 : Blo 1307972 4967999 := bstep (se 1 (by rfl) ⟨3725999, by rfl⟩ : syracuseStep 4967999 = 7451999) B7451999
theorem B2944619 : Blo 1307972 2944619 := bstep (se 1 (by rfl) ⟨2208464, by rfl⟩ : syracuseStep 2944619 = 4416929) B4416929
theorem B4419197 : Blo 1307972 4419197 := bstep (se 3 (by rfl) ⟨828599, by rfl⟩ : syracuseStep 4419197 = 1657199) B1657199
theorem B13438723 : Blo 1307972 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B2944889 : Blo 1307972 2944889 := bstep (se 2 (by rfl) ⟨1104333, by rfl⟩ : syracuseStep 2944889 = 2208667) B2208667
theorem B4419467 : Blo 1307972 4419467 := bstep (se 1 (by rfl) ⟨3314600, by rfl⟩ : syracuseStep 4419467 = 6629201) B6629201
theorem B6631307 : Blo 1307972 6631307 := bstep (se 1 (by rfl) ⟨4973480, by rfl⟩ : syracuseStep 6631307 = 9946961) B9946961
theorem B7450541 : Blo 1307972 7450541 := bstep (se 3 (by rfl) ⟨1396976, by rfl⟩ : syracuseStep 7450541 = 2793953) B2793953
theorem B16764995 : Blo 1307972 16764995 := bstep (se 1 (by rfl) ⟨12573746, by rfl⟩ : syracuseStep 16764995 = 25147493) B25147493
theorem B1962203 : Blo 1307972 1962203 := bstep (se 1 (by rfl) ⟨1471652, by rfl⟩ : syracuseStep 1962203 = 2943305) B2943305
theorem B7459037 : Blo 1307972 7459037 := bstep (se 3 (by rfl) ⟨1398569, by rfl⟩ : syracuseStep 7459037 = 2797139) B2797139
theorem B1962215 : Blo 1307972 1962215 := bstep (se 1 (by rfl) ⟨1471661, by rfl⟩ : syracuseStep 1962215 = 2943323) B2943323
theorem B1863911 : Blo 1307972 1863911 := bstep (se 1 (by rfl) ⟨1397933, by rfl⟩ : syracuseStep 1863911 = 2795867) B2795867
theorem B18665765 : Blo 1307972 18665765 := bstep (se 4 (by rfl) ⟨1749915, by rfl⟩ : syracuseStep 18665765 = 3499831) B3499831
theorem B2208127 : Blo 1307972 2208127 := bstep (se 1 (by rfl) ⟨1656095, by rfl⟩ : syracuseStep 2208127 = 3312191) B3312191
theorem B1962377 : Blo 1307972 1962377 := bstep (se 2 (by rfl) ⟨735891, by rfl⟩ : syracuseStep 1962377 = 1471783) B1471783
theorem B4420007 : Blo 1307972 4420007 := bstep (se 1 (by rfl) ⟨3315005, by rfl⟩ : syracuseStep 4420007 = 6630011) B6630011
theorem B3314135 : Blo 1307972 3314135 := bstep (se 1 (by rfl) ⟨2485601, by rfl⟩ : syracuseStep 3314135 = 4971203) B4971203
theorem B1962473 : Blo 1307972 1962473 := bstep (se 2 (by rfl) ⟨735927, by rfl⟩ : syracuseStep 1962473 = 1471855) B1471855
theorem B1962599 : Blo 1307972 1962599 := bstep (se 1 (by rfl) ⟨1471949, by rfl⟩ : syracuseStep 1962599 = 2943899) B2943899
theorem B1962731 : Blo 1307972 1962731 := bstep (se 1 (by rfl) ⟨1472048, by rfl⟩ : syracuseStep 1962731 = 2944097) B2944097
theorem B1962761 : Blo 1307972 1962761 := bstep (se 2 (by rfl) ⟨736035, by rfl⟩ : syracuseStep 1962761 = 1472071) B1472071
theorem B2208559 : Blo 1307972 2208559 := bstep (se 1 (by rfl) ⟨1656419, by rfl⟩ : syracuseStep 2208559 = 3312839) B3312839
theorem B1962863 : Blo 1307972 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B12579745 : Blo 1307972 12579745 := bstep (se 2 (by rfl) ⟨4717404, by rfl⟩ : syracuseStep 12579745 = 9434809) B9434809
theorem B6288299 : Blo 1307972 6288299 := bstep (se 1 (by rfl) ⟨4716224, by rfl⟩ : syracuseStep 6288299 = 9432449) B9432449
theorem B9933839 : Blo 1307972 9933839 := bstep (se 1 (by rfl) ⟨7450379, by rfl⟩ : syracuseStep 9933839 = 14900759) B14900759
theorem B1963115 : Blo 1307972 1963115 := bstep (se 1 (by rfl) ⟨1472336, by rfl⟩ : syracuseStep 1963115 = 2944673) B2944673
theorem B11187395 : Blo 1307972 11187395 := bstep (se 1 (by rfl) ⟨8390546, by rfl⟩ : syracuseStep 11187395 = 16781093) B16781093
theorem B1963355 : Blo 1307972 1963355 := bstep (se 1 (by rfl) ⟨1472516, by rfl⟩ : syracuseStep 1963355 = 2945033) B2945033
theorem B1308059 : Blo 1307972 1308059 := bstep (se 1 (by rfl) ⟨981044, by rfl⟩ : syracuseStep 1308059 = 1962089) B1962089
theorem B1308271 : Blo 1307972 1308271 := bstep (se 1 (by rfl) ⟨981203, by rfl⟩ : syracuseStep 1308271 = 1962407) B1962407
theorem B1963631 : Blo 1307972 1963631 := bstep (se 1 (by rfl) ⟨1472723, by rfl⟩ : syracuseStep 1963631 = 2945447) B2945447
theorem B1308327 : Blo 1307972 1308327 := bstep (se 1 (by rfl) ⟨981245, by rfl⟩ : syracuseStep 1308327 = 1962491) B1962491
theorem B16766635 : Blo 1307972 16766635 := bstep (se 1 (by rfl) ⟨12574976, by rfl⟩ : syracuseStep 16766635 = 25149953) B25149953
theorem B1963703 : Blo 1307972 1963703 := bstep (se 1 (by rfl) ⟨1472777, by rfl⟩ : syracuseStep 1963703 = 2945555) B2945555
theorem B2946743 : Blo 1307972 2946743 := bstep (se 1 (by rfl) ⟨2210057, by rfl⟩ : syracuseStep 2946743 = 4420115) B4420115
theorem B1963739 : Blo 1307972 1963739 := bstep (se 1 (by rfl) ⟨1472804, by rfl⟩ : syracuseStep 1963739 = 2945609) B2945609
theorem B1308411 : Blo 1307972 1308411 := bstep (se 1 (by rfl) ⟨981308, by rfl⟩ : syracuseStep 1308411 = 1962617) B1962617
theorem B1472251 : Blo 1307972 1472251 := bstep (se 1 (by rfl) ⟨1104188, by rfl⟩ : syracuseStep 1472251 = 2208377) B2208377
theorem B2209531 : Blo 1307972 2209531 := bstep (se 1 (by rfl) ⟨1657148, by rfl⟩ : syracuseStep 2209531 = 3314297) B3314297
theorem B3315451 : Blo 1307972 3315451 := bstep (se 1 (by rfl) ⟨2486588, by rfl⟩ : syracuseStep 3315451 = 4973177) B4973177
theorem B14915339 : Blo 1307972 14915339 := bstep (se 1 (by rfl) ⟨11186504, by rfl⟩ : syracuseStep 14915339 = 22373009) B22373009
theorem B1308447 : Blo 1307972 1308447 := bstep (se 1 (by rfl) ⟨981335, by rfl⟩ : syracuseStep 1308447 = 1962671) B1962671
theorem B1472287 : Blo 1307972 1472287 := bstep (se 1 (by rfl) ⟨1104215, by rfl⟩ : syracuseStep 1472287 = 2208431) B2208431
theorem B1308479 : Blo 1307972 1308479 := bstep (se 1 (by rfl) ⟨981359, by rfl⟩ : syracuseStep 1308479 = 1962719) B1962719
theorem B3979145 : Blo 1307972 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B1963913 : Blo 1307972 1963913 := bstep (se 2 (by rfl) ⟨736467, by rfl⟩ : syracuseStep 1963913 = 1472935) B1472935
theorem B2209673 : Blo 1307972 2209673 := bstep (se 2 (by rfl) ⟨828627, by rfl⟩ : syracuseStep 2209673 = 1657255) B1657255
theorem B3315593 : Blo 1307972 3315593 := bstep (se 2 (by rfl) ⟨1243347, by rfl⟩ : syracuseStep 3315593 = 2486695) B2486695
theorem B1308655 : Blo 1307972 1308655 := bstep (se 1 (by rfl) ⟨981491, by rfl⟩ : syracuseStep 1308655 = 1962983) B1962983
theorem B1964015 : Blo 1307972 1964015 := bstep (se 1 (by rfl) ⟨1473011, by rfl⟩ : syracuseStep 1964015 = 2946023) B2946023
theorem B6805505 : Blo 1307972 6805505 := bstep (se 2 (by rfl) ⟨2552064, by rfl⟩ : syracuseStep 6805505 = 5104129) B5104129
theorem B7075937 : Blo 1307972 7075937 := bstep (se 2 (by rfl) ⟨2653476, by rfl⟩ : syracuseStep 7075937 = 5306953) B5306953
theorem B1308827 : Blo 1307972 1308827 := bstep (se 1 (by rfl) ⟨981620, by rfl⟩ : syracuseStep 1308827 = 1963241) B1963241
theorem B1308863 : Blo 1307972 1308863 := bstep (se 1 (by rfl) ⟨981647, by rfl⟩ : syracuseStep 1308863 = 1963295) B1963295
theorem B1964267 : Blo 1307972 1964267 := bstep (se 1 (by rfl) ⟨1473200, by rfl⟩ : syracuseStep 1964267 = 2946401) B2946401
theorem B7452931 : Blo 1307972 7452931 := bstep (se 1 (by rfl) ⟨5589698, by rfl⟩ : syracuseStep 7452931 = 11179397) B11179397
theorem B1964327 : Blo 1307972 1964327 := bstep (se 1 (by rfl) ⟨1473245, by rfl⟩ : syracuseStep 1964327 = 2946491) B2946491
theorem B1308975 : Blo 1307972 1308975 := bstep (se 1 (by rfl) ⟨981731, by rfl⟩ : syracuseStep 1308975 = 1963463) B1963463
theorem B2210105 : Blo 1307972 2210105 := bstep (se 2 (by rfl) ⟨828789, by rfl⟩ : syracuseStep 2210105 = 1657579) B1657579
theorem B1964411 : Blo 1307972 1964411 := bstep (se 1 (by rfl) ⟨1473308, by rfl⟩ : syracuseStep 1964411 = 2946617) B2946617
theorem B1309211 : Blo 1307972 1309211 := bstep (se 1 (by rfl) ⟨981908, by rfl⟩ : syracuseStep 1309211 = 1963817) B1963817
theorem B1309215 : Blo 1307972 1309215 := bstep (se 1 (by rfl) ⟨981911, by rfl⟩ : syracuseStep 1309215 = 1963823) B1963823
theorem B4192889 : Blo 1307972 4192889 := bstep (se 2 (by rfl) ⟨1572333, by rfl⟩ : syracuseStep 4192889 = 3144667) B3144667
theorem B1964681 : Blo 1307972 1964681 := bstep (se 2 (by rfl) ⟨736755, by rfl⟩ : syracuseStep 1964681 = 1473511) B1473511
theorem B23886535 : Blo 1307972 23886535 := bstep (se 1 (by rfl) ⟨17914901, by rfl⟩ : syracuseStep 23886535 = 35829803) B35829803
theorem B1964855 : Blo 1307972 1964855 := bstep (se 1 (by rfl) ⟨1473641, by rfl⟩ : syracuseStep 1964855 = 2947283) B2947283
theorem B1309531 : Blo 1307972 1309531 := bstep (se 1 (by rfl) ⟨982148, by rfl⟩ : syracuseStep 1309531 = 1964297) B1964297
theorem B1964891 : Blo 1307972 1964891 := bstep (se 1 (by rfl) ⟨1473668, by rfl⟩ : syracuseStep 1964891 = 2947337) B2947337
theorem B163371919 : Blo 1307972 163371919 := bstep (se 1 (by rfl) ⟨122528939, by rfl⟩ : syracuseStep 163371919 = 245057879) B245057879
theorem B1309599 : Blo 1307972 1309599 := bstep (se 1 (by rfl) ⟨982199, by rfl⟩ : syracuseStep 1309599 = 1964399) B1964399
theorem B1473439 : Blo 1307972 1473439 := bstep (se 1 (by rfl) ⟨1105079, by rfl⟩ : syracuseStep 1473439 = 2210159) B2210159
theorem B6626285 : Blo 1307972 6626285 := bstep (se 3 (by rfl) ⟨1242428, by rfl⟩ : syracuseStep 6626285 = 2484857) B2484857
theorem B1309743 : Blo 1307972 1309743 := bstep (se 1 (by rfl) ⟨982307, by rfl⟩ : syracuseStep 1309743 = 1964615) B1964615
theorem B1473583 : Blo 1307972 1473583 := bstep (se 1 (by rfl) ⟨1105187, by rfl⟩ : syracuseStep 1473583 = 2210375) B2210375
theorem B1309767 : Blo 1307972 1309767 := bstep (se 1 (by rfl) ⟨982325, by rfl⟩ : syracuseStep 1309767 = 1964651) B1964651
theorem B21232729 : Blo 1307972 21232729 := bstep (se 2 (by rfl) ⟨7962273, by rfl⟩ : syracuseStep 21232729 = 15924547) B15924547
theorem B4717693 : Blo 1307972 4717693 := bstep (se 3 (by rfl) ⟨884567, by rfl⟩ : syracuseStep 4717693 = 1769135) B1769135
theorem B1309919 : Blo 1307972 1309919 := bstep (se 1 (by rfl) ⟨982439, by rfl⟩ : syracuseStep 1309919 = 1964879) B1964879
theorem B4971887 : Blo 1307972 4971887 := bstep (se 1 (by rfl) ⟨3728915, by rfl⟩ : syracuseStep 4971887 = 7457831) B7457831
theorem B2833831 : Blo 1307972 2833831 := bstep (se 1 (by rfl) ⟨2125373, by rfl⟩ : syracuseStep 2833831 = 4250747) B4250747
theorem B43629997 : Blo 1307972 43629997 := bstep (se 3 (by rfl) ⟨8180624, by rfl⟩ : syracuseStep 43629997 = 16361249) B16361249
theorem B8388035 : Blo 1307972 8388035 := bstep (se 1 (by rfl) ⟨6291026, by rfl⟩ : syracuseStep 8388035 = 12582053) B12582053
theorem B4414931 : Blo 1307972 4414931 := bstep (se 1 (by rfl) ⟨3311198, by rfl⟩ : syracuseStep 4414931 = 6622397) B6622397
theorem B43048543 : Blo 1307972 43048543 := bstep (se 1 (by rfl) ⟨32286407, by rfl⟩ : syracuseStep 43048543 = 64572815) B64572815
theorem B4415201 : Blo 1307972 4415201 := bstep (se 2 (by rfl) ⟨1655700, by rfl⟩ : syracuseStep 4415201 = 3311401) B3311401
theorem B37715705 : Blo 1307972 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B6627095 : Blo 1307972 6627095 := bstep (se 1 (by rfl) ⟨4970321, by rfl⟩ : syracuseStep 6627095 = 9940643) B9940643
theorem B34004843 : Blo 1307972 34004843 := bstep (se 1 (by rfl) ⟨25503632, by rfl⟩ : syracuseStep 34004843 = 51007265) B51007265
theorem B4972691 : Blo 1307972 4972691 := bstep (se 1 (by rfl) ⟨3729518, by rfl⟩ : syracuseStep 4972691 = 7459037) B7459037
theorem B12443843 : Blo 1307972 12443843 := bstep (se 1 (by rfl) ⟨9332882, by rfl⟩ : syracuseStep 12443843 = 18665765) B18665765
theorem B5308703 : Blo 1307972 5308703 := bstep (se 1 (by rfl) ⟨3981527, by rfl⟩ : syracuseStep 5308703 = 7963055) B7963055
theorem B9937241 : Blo 1307972 9937241 := bstep (se 2 (by rfl) ⟨3726465, by rfl⟩ : syracuseStep 9937241 = 7452931) B7452931
theorem B1655407 : Blo 1307972 1655407 := bstep (se 1 (by rfl) ⟨1241555, by rfl⟩ : syracuseStep 1655407 = 2483111) B2483111
theorem B1327727 : Blo 1307972 1327727 := bstep (se 1 (by rfl) ⟨995795, by rfl⟩ : syracuseStep 1327727 = 1991591) B1991591
theorem B7455347 : Blo 1307972 7455347 := bstep (se 1 (by rfl) ⟨5591510, by rfl⟩ : syracuseStep 7455347 = 11183021) B11183021
theorem B3589175 : Blo 1307972 3589175 := bstep (se 1 (by rfl) ⟨2691881, by rfl⟩ : syracuseStep 3589175 = 5383763) B5383763
theorem B3146975 : Blo 1307972 3146975 := bstep (se 1 (by rfl) ⟨2360231, by rfl⟩ : syracuseStep 3146975 = 4720463) B4720463
theorem B3310895 : Blo 1307972 3310895 := bstep (se 1 (by rfl) ⟨2483171, by rfl⟩ : syracuseStep 3310895 = 4966343) B4966343
theorem B9946475 : Blo 1307972 9946475 := bstep (se 1 (by rfl) ⟨7459856, by rfl⟩ : syracuseStep 9946475 = 14919713) B14919713
theorem B5588675 : Blo 1307972 5588675 := bstep (se 1 (by rfl) ⟨4191506, by rfl⟩ : syracuseStep 5588675 = 8383013) B8383013
theorem B58173329 : Blo 1307972 58173329 := bstep (se 2 (by rfl) ⟨21814998, by rfl⟩ : syracuseStep 58173329 = 43629997) B43629997
theorem B4417523 : Blo 1307972 4417523 := bstep (se 1 (by rfl) ⟨3313142, by rfl⟩ : syracuseStep 4417523 = 6626285) B6626285
theorem B4966555 : Blo 1307972 4966555 := bstep (se 1 (by rfl) ⟨3724916, by rfl⟩ : syracuseStep 4966555 = 7449833) B7449833
theorem B2943287 : Blo 1307972 2943287 := bstep (se 1 (by rfl) ⟨2207465, by rfl⟩ : syracuseStep 2943287 = 4414931) B4414931
theorem B17918297 : Blo 1307972 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B3311999 : Blo 1307972 3311999 := bstep (se 1 (by rfl) ⟨2483999, by rfl⟩ : syracuseStep 3311999 = 4967999) B4967999
theorem B2943467 : Blo 1307972 2943467 := bstep (se 1 (by rfl) ⟨2207600, by rfl⟩ : syracuseStep 2943467 = 4415201) B4415201
theorem B25143803 : Blo 1307972 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B4418063 : Blo 1307972 4418063 := bstep (se 1 (by rfl) ⟨3313547, by rfl⟩ : syracuseStep 4418063 = 6627095) B6627095
theorem B22669895 : Blo 1307972 22669895 := bstep (se 1 (by rfl) ⟨17002421, by rfl⟩ : syracuseStep 22669895 = 34004843) B34004843
theorem B4967027 : Blo 1307972 4967027 := bstep (se 1 (by rfl) ⟨3725270, by rfl⟩ : syracuseStep 4967027 = 7450541) B7450541
theorem B11176663 : Blo 1307972 11176663 := bstep (se 1 (by rfl) ⟨8382497, by rfl⟩ : syracuseStep 11176663 = 16764995) B16764995
theorem B9939671 : Blo 1307972 9939671 := bstep (se 1 (by rfl) ⟨7454753, by rfl⟩ : syracuseStep 9939671 = 14909507) B14909507
theorem B2944169 : Blo 1307972 2944169 := bstep (se 2 (by rfl) ⟨1104063, by rfl⟩ : syracuseStep 2944169 = 2208127) B2208127
theorem B6622559 : Blo 1307972 6622559 := bstep (se 1 (by rfl) ⟨4966919, by rfl⟩ : syracuseStep 6622559 = 9933839) B9933839
theorem B7458263 : Blo 1307972 7458263 := bstep (se 1 (by rfl) ⟨5593697, by rfl⟩ : syracuseStep 7458263 = 11187395) B11187395
theorem B96824827 : Blo 1307972 96824827 := bstep (se 1 (by rfl) ⟨72618620, by rfl⟩ : syracuseStep 96824827 = 145237241) B145237241
theorem B12578327 : Blo 1307972 12578327 := bstep (se 1 (by rfl) ⟨9433745, by rfl⟩ : syracuseStep 12578327 = 18867491) B18867491
theorem B2944583 : Blo 1307972 2944583 := bstep (se 1 (by rfl) ⟨2208437, by rfl⟩ : syracuseStep 2944583 = 4416875) B4416875
theorem B4419143 : Blo 1307972 4419143 := bstep (se 1 (by rfl) ⟨3314357, by rfl⟩ : syracuseStep 4419143 = 6628715) B6628715
theorem B2944655 : Blo 1307972 2944655 := bstep (se 1 (by rfl) ⟨2208491, by rfl⟩ : syracuseStep 2944655 = 4416983) B4416983
theorem B2944745 : Blo 1307972 2944745 := bstep (se 2 (by rfl) ⟨1104279, by rfl⟩ : syracuseStep 2944745 = 2208559) B2208559
theorem B2944763 : Blo 1307972 2944763 := bstep (se 1 (by rfl) ⟨2208572, by rfl⟩ : syracuseStep 2944763 = 4417145) B4417145
theorem B217829225 : Blo 1307972 217829225 := bstep (se 2 (by rfl) ⟨81685959, by rfl⟩ : syracuseStep 217829225 = 163371919) B163371919
theorem B16772993 : Blo 1307972 16772993 := bstep (se 2 (by rfl) ⟨6289872, by rfl⟩ : syracuseStep 16772993 = 12579745) B12579745
theorem B7966849 : Blo 1307972 7966849 := bstep (se 2 (by rfl) ⟨2987568, by rfl⟩ : syracuseStep 7966849 = 5975137) B5975137
theorem B11186369 : Blo 1307972 11186369 := bstep (se 2 (by rfl) ⟨4194888, by rfl⟩ : syracuseStep 11186369 = 8389777) B8389777
theorem B1962395 : Blo 1307972 1962395 := bstep (se 1 (by rfl) ⟨1471796, by rfl⟩ : syracuseStep 1962395 = 2943593) B2943593
theorem B2945771 : Blo 1307972 2945771 := bstep (se 1 (by rfl) ⟨2209328, by rfl⟩ : syracuseStep 2945771 = 4418657) B4418657
theorem B4420331 : Blo 1307972 4420331 := bstep (se 1 (by rfl) ⟨3315248, by rfl⟩ : syracuseStep 4420331 = 6630497) B6630497
theorem B57398057 : Blo 1307972 57398057 := bstep (se 2 (by rfl) ⟨21524271, by rfl⟩ : syracuseStep 57398057 = 43048543) B43048543
theorem B1962815 : Blo 1307972 1962815 := bstep (se 1 (by rfl) ⟨1472111, by rfl⟩ : syracuseStep 1962815 = 2944223) B2944223
theorem B3314591 : Blo 1307972 3314591 := bstep (se 1 (by rfl) ⟨2485943, by rfl⟩ : syracuseStep 3314591 = 4971887) B4971887
theorem B1962959 : Blo 1307972 1962959 := bstep (se 1 (by rfl) ⟨1472219, by rfl⟩ : syracuseStep 1962959 = 2944439) B2944439
theorem B5592023 : Blo 1307972 5592023 := bstep (se 1 (by rfl) ⟨4194017, by rfl⟩ : syracuseStep 5592023 = 8388035) B8388035
theorem B1963001 : Blo 1307972 1963001 := bstep (se 2 (by rfl) ⟨736125, by rfl⟩ : syracuseStep 1963001 = 1472251) B1472251
theorem B2946041 : Blo 1307972 2946041 := bstep (se 2 (by rfl) ⟨1104765, by rfl⟩ : syracuseStep 2946041 = 2209531) B2209531
theorem B4420601 : Blo 1307972 4420601 := bstep (se 2 (by rfl) ⟨1657725, by rfl⟩ : syracuseStep 4420601 = 3315451) B3315451
theorem B1963049 : Blo 1307972 1963049 := bstep (se 2 (by rfl) ⟨736143, by rfl⟩ : syracuseStep 1963049 = 1472287) B1472287
theorem B2208809 : Blo 1307972 2208809 := bstep (se 2 (by rfl) ⟨828303, by rfl⟩ : syracuseStep 2208809 = 1656607) B1656607
theorem B1963079 : Blo 1307972 1963079 := bstep (se 1 (by rfl) ⟨1472309, by rfl⟩ : syracuseStep 1963079 = 2944619) B2944619
theorem B2946131 : Blo 1307972 2946131 := bstep (se 1 (by rfl) ⟨2209598, by rfl⟩ : syracuseStep 2946131 = 4419197) B4419197
theorem B1963259 : Blo 1307972 1963259 := bstep (se 1 (by rfl) ⟨1472444, by rfl⟩ : syracuseStep 1963259 = 2944889) B2944889
theorem B2946311 : Blo 1307972 2946311 := bstep (se 1 (by rfl) ⟨2209733, by rfl⟩ : syracuseStep 2946311 = 4419467) B4419467
theorem B4420871 : Blo 1307972 4420871 := bstep (se 1 (by rfl) ⟨3315653, by rfl⟩ : syracuseStep 4420871 = 6631307) B6631307
theorem B174413249 : Blo 1307972 174413249 := bstep (se 2 (by rfl) ⟨65404968, by rfl⟩ : syracuseStep 174413249 = 130809937) B130809937
theorem B1308135 : Blo 1307972 1308135 := bstep (se 1 (by rfl) ⟨981101, by rfl⟩ : syracuseStep 1308135 = 1962203) B1962203
theorem B1308143 : Blo 1307972 1308143 := bstep (se 1 (by rfl) ⟨981107, by rfl⟩ : syracuseStep 1308143 = 1962215) B1962215
theorem B1308251 : Blo 1307972 1308251 := bstep (se 1 (by rfl) ⟨981188, by rfl⟩ : syracuseStep 1308251 = 1962377) B1962377
theorem B2946671 : Blo 1307972 2946671 := bstep (se 1 (by rfl) ⟨2210003, by rfl⟩ : syracuseStep 2946671 = 4420007) B4420007
theorem B2209423 : Blo 1307972 2209423 := bstep (se 1 (by rfl) ⟨1657067, by rfl⟩ : syracuseStep 2209423 = 3314135) B3314135
theorem B1308315 : Blo 1307972 1308315 := bstep (se 1 (by rfl) ⟨981236, by rfl⟩ : syracuseStep 1308315 = 1962473) B1962473
theorem B1308399 : Blo 1307972 1308399 := bstep (se 1 (by rfl) ⟨981299, by rfl⟩ : syracuseStep 1308399 = 1962599) B1962599
theorem B5592827 : Blo 1307972 5592827 := bstep (se 1 (by rfl) ⟨4194620, by rfl⟩ : syracuseStep 5592827 = 8389241) B8389241
theorem B1308487 : Blo 1307972 1308487 := bstep (se 1 (by rfl) ⟨981365, by rfl⟩ : syracuseStep 1308487 = 1962731) B1962731
theorem B1308507 : Blo 1307972 1308507 := bstep (se 1 (by rfl) ⟨981380, by rfl⟩ : syracuseStep 1308507 = 1962761) B1962761
theorem B1308575 : Blo 1307972 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B4970429 : Blo 1307972 4970429 := bstep (se 3 (by rfl) ⟨931955, by rfl⟩ : syracuseStep 4970429 = 1863911) B1863911
theorem B4192199 : Blo 1307972 4192199 := bstep (se 1 (by rfl) ⟨3144149, by rfl⟩ : syracuseStep 4192199 = 6288299) B6288299
theorem B3725281 : Blo 1307972 3725281 := bstep (se 2 (by rfl) ⟨1396980, by rfl⟩ : syracuseStep 3725281 = 2793961) B2793961
theorem B1308743 : Blo 1307972 1308743 := bstep (se 1 (by rfl) ⟨981557, by rfl⟩ : syracuseStep 1308743 = 1963115) B1963115
theorem B11327635 : Blo 1307972 11327635 := bstep (se 1 (by rfl) ⟨8495726, by rfl⟩ : syracuseStep 11327635 = 16991453) B16991453
theorem B1308903 : Blo 1307972 1308903 := bstep (se 1 (by rfl) ⟨981677, by rfl⟩ : syracuseStep 1308903 = 1963355) B1963355
theorem B31848713 : Blo 1307972 31848713 := bstep (se 2 (by rfl) ⟨11943267, by rfl⟩ : syracuseStep 31848713 = 23886535) B23886535
theorem B1309087 : Blo 1307972 1309087 := bstep (se 1 (by rfl) ⟨981815, by rfl⟩ : syracuseStep 1309087 = 1963631) B1963631
theorem B1309135 : Blo 1307972 1309135 := bstep (se 1 (by rfl) ⟨981851, by rfl⟩ : syracuseStep 1309135 = 1963703) B1963703
theorem B1964495 : Blo 1307972 1964495 := bstep (se 1 (by rfl) ⟨1473371, by rfl⟩ : syracuseStep 1964495 = 2946743) B2946743
theorem B1309159 : Blo 1307972 1309159 := bstep (se 1 (by rfl) ⟨981869, by rfl⟩ : syracuseStep 1309159 = 1963739) B1963739
theorem B9943559 : Blo 1307972 9943559 := bstep (se 1 (by rfl) ⟨7457669, by rfl⟩ : syracuseStep 9943559 = 14915339) B14915339
theorem B3725851 : Blo 1307972 3725851 := bstep (se 1 (by rfl) ⟨2794388, by rfl⟩ : syracuseStep 3725851 = 5588777) B5588777
theorem B1964585 : Blo 1307972 1964585 := bstep (se 2 (by rfl) ⟨736719, by rfl⟩ : syracuseStep 1964585 = 1473439) B1473439
theorem B2652763 : Blo 1307972 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B1309275 : Blo 1307972 1309275 := bstep (se 1 (by rfl) ⟨981956, by rfl⟩ : syracuseStep 1309275 = 1963913) B1963913
theorem B1473115 : Blo 1307972 1473115 := bstep (se 1 (by rfl) ⟨1104836, by rfl⟩ : syracuseStep 1473115 = 2209673) B2209673
theorem B2210395 : Blo 1307972 2210395 := bstep (se 1 (by rfl) ⟨1657796, by rfl⟩ : syracuseStep 2210395 = 3315593) B3315593
theorem B1309343 : Blo 1307972 1309343 := bstep (se 1 (by rfl) ⟨982007, by rfl⟩ : syracuseStep 1309343 = 1964015) B1964015
theorem B4537003 : Blo 1307972 4537003 := bstep (se 1 (by rfl) ⟨3402752, by rfl⟩ : syracuseStep 4537003 = 6805505) B6805505
theorem B5593799 : Blo 1307972 5593799 := bstep (se 1 (by rfl) ⟨4195349, by rfl⟩ : syracuseStep 5593799 = 8390699) B8390699
theorem B4717291 : Blo 1307972 4717291 := bstep (se 1 (by rfl) ⟨3537968, by rfl⟩ : syracuseStep 4717291 = 7075937) B7075937
theorem B1964777 : Blo 1307972 1964777 := bstep (se 2 (by rfl) ⟨736791, by rfl⟩ : syracuseStep 1964777 = 1473583) B1473583
theorem B2210537 : Blo 1307972 2210537 := bstep (se 2 (by rfl) ⟨828951, by rfl⟩ : syracuseStep 2210537 = 1657903) B1657903
theorem B28310305 : Blo 1307972 28310305 := bstep (se 2 (by rfl) ⟨10616364, by rfl⟩ : syracuseStep 28310305 = 21232729) B21232729
theorem B1309511 : Blo 1307972 1309511 := bstep (se 1 (by rfl) ⟨982133, by rfl⟩ : syracuseStep 1309511 = 1964267) B1964267
theorem B6290257 : Blo 1307972 6290257 := bstep (se 2 (by rfl) ⟨2358846, by rfl⟩ : syracuseStep 6290257 = 4717693) B4717693
theorem B1309551 : Blo 1307972 1309551 := bstep (se 1 (by rfl) ⟨982163, by rfl⟩ : syracuseStep 1309551 = 1964327) B1964327
theorem B1473403 : Blo 1307972 1473403 := bstep (se 1 (by rfl) ⟨1105052, by rfl⟩ : syracuseStep 1473403 = 2210105) B2210105
theorem B1309607 : Blo 1307972 1309607 := bstep (se 1 (by rfl) ⟨982205, by rfl⟩ : syracuseStep 1309607 = 1964411) B1964411
theorem B11181037 : Blo 1307972 11181037 := bstep (se 3 (by rfl) ⟨2096444, by rfl⟩ : syracuseStep 11181037 = 4192889) B4192889
theorem B9944045 : Blo 1307972 9944045 := bstep (se 3 (by rfl) ⟨1864508, by rfl⟩ : syracuseStep 9944045 = 3729017) B3729017
theorem B1309787 : Blo 1307972 1309787 := bstep (se 1 (by rfl) ⟨982340, by rfl⟩ : syracuseStep 1309787 = 1964681) B1964681
theorem B4414607 : Blo 1307972 4414607 := bstep (se 1 (by rfl) ⟨3310955, by rfl⟩ : syracuseStep 4414607 = 6621911) B6621911
theorem B1309903 : Blo 1307972 1309903 := bstep (se 1 (by rfl) ⟨982427, by rfl⟩ : syracuseStep 1309903 = 1964855) B1964855
theorem B1309927 : Blo 1307972 1309927 := bstep (se 1 (by rfl) ⟨982445, by rfl⟩ : syracuseStep 1309927 = 1964891) B1964891
theorem B15113765 : Blo 1307972 15113765 := bstep (se 4 (by rfl) ⟨1416915, by rfl⟩ : syracuseStep 15113765 = 2833831) B2833831
theorem B22355513 : Blo 1307972 22355513 := bstep (se 2 (by rfl) ⟨8383317, by rfl⟩ : syracuseStep 22355513 = 16766635) B16766635
theorem B5594791 : Blo 1307972 5594791 := bstep (se 1 (by rfl) ⟨4196093, by rfl⟩ : syracuseStep 5594791 = 8392187) B8392187
theorem B3539135 : Blo 1307972 3539135 := bstep (se 1 (by rfl) ⟨2654351, by rfl⟩ : syracuseStep 3539135 = 5308703) B5308703
theorem B3315127 : Blo 1307972 3315127 := bstep (se 1 (by rfl) ⟨2486345, by rfl⟩ : syracuseStep 3315127 = 4972691) B4972691
theorem B38265371 : Blo 1307972 38265371 := bstep (se 1 (by rfl) ⟨28699028, by rfl⟩ : syracuseStep 38265371 = 57398057) B57398057
theorem B3728015 : Blo 1307972 3728015 := bstep (se 1 (by rfl) ⟨2796011, by rfl⟩ : syracuseStep 3728015 = 5592023) B5592023
theorem B2392783 : Blo 1307972 2392783 := bstep (se 1 (by rfl) ⟨1794587, by rfl⟩ : syracuseStep 2392783 = 3589175) B3589175
theorem B2097983 : Blo 1307972 2097983 := bstep (se 1 (by rfl) ⟨1573487, by rfl⟩ : syracuseStep 2097983 = 3146975) B3146975
theorem B14902217 : Blo 1307972 14902217 := bstep (se 2 (by rfl) ⟨5588331, by rfl⟩ : syracuseStep 14902217 = 11176663) B11176663
theorem B3728551 : Blo 1307972 3728551 := bstep (se 1 (by rfl) ⟨2796413, by rfl⟩ : syracuseStep 3728551 = 5592827) B5592827
theorem B2794799 : Blo 1307972 2794799 := bstep (se 1 (by rfl) ⟨2096099, by rfl⟩ : syracuseStep 2794799 = 4192199) B4192199
theorem B11945531 : Blo 1307972 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B3540605 : Blo 1307972 3540605 := bstep (se 3 (by rfl) ⟨663863, by rfl⟩ : syracuseStep 3540605 = 1327727) B1327727
theorem B16762535 : Blo 1307972 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B6629039 : Blo 1307972 6629039 := bstep (se 1 (by rfl) ⟨4971779, by rfl⟩ : syracuseStep 6629039 = 9943559) B9943559
theorem B3311351 : Blo 1307972 3311351 := bstep (se 1 (by rfl) ⟨2483513, by rfl⟩ : syracuseStep 3311351 = 4967027) B4967027
theorem B6629363 : Blo 1307972 6629363 := bstep (se 1 (by rfl) ⟨4972022, by rfl⟩ : syracuseStep 6629363 = 9944045) B9944045
theorem B2943071 : Blo 1307972 2943071 := bstep (se 1 (by rfl) ⟨2207303, by rfl⟩ : syracuseStep 2943071 = 4414607) B4414607
theorem B14903675 : Blo 1307972 14903675 := bstep (se 1 (by rfl) ⟨11177756, by rfl⟩ : syracuseStep 14903675 = 22355513) B22355513
theorem B4967041 : Blo 1307972 4967041 := bstep (se 2 (by rfl) ⟨1862640, by rfl⟩ : syracuseStep 4967041 = 3725281) B3725281
theorem B7457579 : Blo 1307972 7457579 := bstep (se 1 (by rfl) ⟨5593184, by rfl⟩ : syracuseStep 7457579 = 11186369) B11186369
theorem B6622073 : Blo 1307972 6622073 := bstep (se 2 (by rfl) ⟨2483277, by rfl⟩ : syracuseStep 6622073 = 4966555) B4966555
theorem B4967801 : Blo 1307972 4967801 := bstep (se 2 (by rfl) ⟨1862925, by rfl⟩ : syracuseStep 4967801 = 3725851) B3725851
theorem B2207209 : Blo 1307972 2207209 := bstep (se 2 (by rfl) ⟨827703, by rfl⟩ : syracuseStep 2207209 = 1655407) B1655407
theorem B2207263 : Blo 1307972 2207263 := bstep (se 1 (by rfl) ⟨1655447, by rfl⟩ : syracuseStep 2207263 = 3310895) B3310895
theorem B6049337 : Blo 1307972 6049337 := bstep (se 2 (by rfl) ⟨2268501, by rfl⟩ : syracuseStep 6049337 = 4537003) B4537003
theorem B6630983 : Blo 1307972 6630983 := bstep (se 1 (by rfl) ⟨4973237, by rfl⟩ : syracuseStep 6630983 = 9946475) B9946475
theorem B3313619 : Blo 1307972 3313619 := bstep (se 1 (by rfl) ⟨2485214, by rfl⟩ : syracuseStep 3313619 = 4970429) B4970429
theorem B2945015 : Blo 1307972 2945015 := bstep (se 1 (by rfl) ⟨2208761, by rfl⟩ : syracuseStep 2945015 = 4417523) B4417523
theorem B1962191 : Blo 1307972 1962191 := bstep (se 1 (by rfl) ⟨1471643, by rfl⟩ : syracuseStep 1962191 = 2943287) B2943287
theorem B2207999 : Blo 1307972 2207999 := bstep (se 1 (by rfl) ⟨1655999, by rfl⟩ : syracuseStep 2207999 = 3311999) B3311999
theorem B1962311 : Blo 1307972 1962311 := bstep (se 1 (by rfl) ⟨1471733, by rfl⟩ : syracuseStep 1962311 = 2943467) B2943467
theorem B2945375 : Blo 1307972 2945375 := bstep (se 1 (by rfl) ⟨2209031, by rfl⟩ : syracuseStep 2945375 = 4418063) B4418063
theorem B1962779 : Blo 1307972 1962779 := bstep (se 1 (by rfl) ⟨1472084, by rfl⟩ : syracuseStep 1962779 = 2944169) B2944169
theorem B2945897 : Blo 1307972 2945897 := bstep (se 2 (by rfl) ⟨1104711, by rfl⟩ : syracuseStep 2945897 = 2209423) B2209423
theorem B7459721 : Blo 1307972 7459721 := bstep (se 2 (by rfl) ⟨2797395, by rfl⟩ : syracuseStep 7459721 = 5594791) B5594791
theorem B8385551 : Blo 1307972 8385551 := bstep (se 1 (by rfl) ⟨6289163, by rfl⟩ : syracuseStep 8385551 = 12578327) B12578327
theorem B155128877 : Blo 1307972 155128877 := bstep (se 3 (by rfl) ⟨29086664, by rfl⟩ : syracuseStep 155128877 = 58173329) B58173329
theorem B1963055 : Blo 1307972 1963055 := bstep (se 1 (by rfl) ⟨1472291, by rfl⟩ : syracuseStep 1963055 = 2944583) B2944583
theorem B2946095 : Blo 1307972 2946095 := bstep (se 1 (by rfl) ⟨2209571, by rfl⟩ : syracuseStep 2946095 = 4419143) B4419143
theorem B1963103 : Blo 1307972 1963103 := bstep (se 1 (by rfl) ⟨1472327, by rfl⟩ : syracuseStep 1963103 = 2944655) B2944655
theorem B1963163 : Blo 1307972 1963163 := bstep (se 1 (by rfl) ⟨1472372, by rfl⟩ : syracuseStep 1963163 = 2944745) B2944745
theorem B1963175 : Blo 1307972 1963175 := bstep (se 1 (by rfl) ⟨1472381, by rfl⟩ : syracuseStep 1963175 = 2944763) B2944763
theorem B8295895 : Blo 1307972 8295895 := bstep (se 1 (by rfl) ⟨6221921, by rfl⟩ : syracuseStep 8295895 = 12443843) B12443843
theorem B10622465 : Blo 1307972 10622465 := bstep (se 2 (by rfl) ⟨3983424, by rfl⟩ : syracuseStep 10622465 = 7966849) B7966849
theorem B15103513 : Blo 1307972 15103513 := bstep (se 2 (by rfl) ⟨5663817, by rfl⟩ : syracuseStep 15103513 = 11327635) B11327635
theorem B6624827 : Blo 1307972 6624827 := bstep (se 1 (by rfl) ⟨4968620, by rfl⟩ : syracuseStep 6624827 = 9937241) B9937241
theorem B1308263 : Blo 1307972 1308263 := bstep (se 1 (by rfl) ⟨981197, by rfl⟩ : syracuseStep 1308263 = 1962395) B1962395
theorem B4970231 : Blo 1307972 4970231 := bstep (se 1 (by rfl) ⟨3727673, by rfl⟩ : syracuseStep 4970231 = 7455347) B7455347
theorem B1963847 : Blo 1307972 1963847 := bstep (se 1 (by rfl) ⟨1472885, by rfl⟩ : syracuseStep 1963847 = 2945771) B2945771
theorem B2946887 : Blo 1307972 2946887 := bstep (se 1 (by rfl) ⟨2210165, by rfl⟩ : syracuseStep 2946887 = 4420331) B4420331
theorem B1308543 : Blo 1307972 1308543 := bstep (se 1 (by rfl) ⟨981407, by rfl⟩ : syracuseStep 1308543 = 1962815) B1962815
theorem B2209727 : Blo 1307972 2209727 := bstep (se 1 (by rfl) ⟨1657295, by rfl⟩ : syracuseStep 2209727 = 3314591) B3314591
theorem B1308639 : Blo 1307972 1308639 := bstep (se 1 (by rfl) ⟨981479, by rfl⟩ : syracuseStep 1308639 = 1962959) B1962959
theorem B1308667 : Blo 1307972 1308667 := bstep (se 1 (by rfl) ⟨981500, by rfl⟩ : syracuseStep 1308667 = 1963001) B1963001
theorem B1964027 : Blo 1307972 1964027 := bstep (se 1 (by rfl) ⟨1473020, by rfl⟩ : syracuseStep 1964027 = 2946041) B2946041
theorem B2947067 : Blo 1307972 2947067 := bstep (se 1 (by rfl) ⟨2210300, by rfl⟩ : syracuseStep 2947067 = 4420601) B4420601
theorem B1308699 : Blo 1307972 1308699 := bstep (se 1 (by rfl) ⟨981524, by rfl⟩ : syracuseStep 1308699 = 1963049) B1963049
theorem B1472539 : Blo 1307972 1472539 := bstep (se 1 (by rfl) ⟨1104404, by rfl⟩ : syracuseStep 1472539 = 2208809) B2208809
theorem B1308719 : Blo 1307972 1308719 := bstep (se 1 (by rfl) ⟨981539, by rfl⟩ : syracuseStep 1308719 = 1963079) B1963079
theorem B1964087 : Blo 1307972 1964087 := bstep (se 1 (by rfl) ⟨1473065, by rfl⟩ : syracuseStep 1964087 = 2946131) B2946131
theorem B3537017 : Blo 1307972 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1964153 : Blo 1307972 1964153 := bstep (se 2 (by rfl) ⟨736557, by rfl⟩ : syracuseStep 1964153 = 1473115) B1473115
theorem B2947193 : Blo 1307972 2947193 := bstep (se 2 (by rfl) ⟨1105197, by rfl⟩ : syracuseStep 2947193 = 2210395) B2210395
theorem B1308839 : Blo 1307972 1308839 := bstep (se 1 (by rfl) ⟨981629, by rfl⟩ : syracuseStep 1308839 = 1963259) B1963259
theorem B1964207 : Blo 1307972 1964207 := bstep (se 1 (by rfl) ⟨1473155, by rfl⟩ : syracuseStep 1964207 = 2946311) B2946311
theorem B2947247 : Blo 1307972 2947247 := bstep (se 1 (by rfl) ⟨2210435, by rfl⟩ : syracuseStep 2947247 = 4420871) B4420871
theorem B116275499 : Blo 1307972 116275499 := bstep (se 1 (by rfl) ⟨87206624, by rfl⟩ : syracuseStep 116275499 = 174413249) B174413249
theorem B6289721 : Blo 1307972 6289721 := bstep (se 2 (by rfl) ⟨2358645, by rfl⟩ : syracuseStep 6289721 = 4717291) B4717291
theorem B37747073 : Blo 1307972 37747073 := bstep (se 2 (by rfl) ⟨14155152, by rfl⟩ : syracuseStep 37747073 = 28310305) B28310305
theorem B1964447 : Blo 1307972 1964447 := bstep (se 1 (by rfl) ⟨1473335, by rfl⟩ : syracuseStep 1964447 = 2946671) B2946671
theorem B8387009 : Blo 1307972 8387009 := bstep (se 2 (by rfl) ⟨3145128, by rfl⟩ : syracuseStep 8387009 = 6290257) B6290257
theorem B3725783 : Blo 1307972 3725783 := bstep (se 1 (by rfl) ⟨2794337, by rfl⟩ : syracuseStep 3725783 = 5588675) B5588675
theorem B1964537 : Blo 1307972 1964537 := bstep (se 2 (by rfl) ⟨736701, by rfl⟩ : syracuseStep 1964537 = 1473403) B1473403
theorem B14908049 : Blo 1307972 14908049 := bstep (se 2 (by rfl) ⟨5590518, by rfl⟩ : syracuseStep 14908049 = 11181037) B11181037
theorem B21232475 : Blo 1307972 21232475 := bstep (se 1 (by rfl) ⟨15924356, by rfl⟩ : syracuseStep 21232475 = 31848713) B31848713
theorem B1309663 : Blo 1307972 1309663 := bstep (se 1 (by rfl) ⟨982247, by rfl⟩ : syracuseStep 1309663 = 1964495) B1964495
theorem B1309723 : Blo 1307972 1309723 := bstep (se 1 (by rfl) ⟨982292, by rfl⟩ : syracuseStep 1309723 = 1964585) B1964585
theorem B15113263 : Blo 1307972 15113263 := bstep (se 1 (by rfl) ⟨11334947, by rfl⟩ : syracuseStep 15113263 = 22669895) B22669895
theorem B6626447 : Blo 1307972 6626447 := bstep (se 1 (by rfl) ⟨4969835, by rfl⟩ : syracuseStep 6626447 = 9939671) B9939671
theorem B1309851 : Blo 1307972 1309851 := bstep (se 1 (by rfl) ⟨982388, by rfl⟩ : syracuseStep 1309851 = 1964777) B1964777
theorem B1473691 : Blo 1307972 1473691 := bstep (se 1 (by rfl) ⟨1105268, by rfl⟩ : syracuseStep 1473691 = 2210537) B2210537
theorem B14916797 : Blo 1307972 14916797 := bstep (se 3 (by rfl) ⟨2796899, by rfl⟩ : syracuseStep 14916797 = 5593799) B5593799
theorem B4415039 : Blo 1307972 4415039 := bstep (se 1 (by rfl) ⟨3311279, by rfl⟩ : syracuseStep 4415039 = 6622559) B6622559
theorem B4972175 : Blo 1307972 4972175 := bstep (se 1 (by rfl) ⟨3729131, by rfl⟩ : syracuseStep 4972175 = 7458263) B7458263
theorem B10075843 : Blo 1307972 10075843 := bstep (se 1 (by rfl) ⟨7556882, by rfl⟩ : syracuseStep 10075843 = 15113765) B15113765
theorem B145219483 : Blo 1307972 145219483 := bstep (se 1 (by rfl) ⟨108914612, by rfl⟩ : syracuseStep 145219483 = 217829225) B217829225
theorem B11181995 : Blo 1307972 11181995 := bstep (se 1 (by rfl) ⟨8386496, by rfl⟩ : syracuseStep 11181995 = 16772993) B16772993
theorem B516399077 : Blo 1307972 516399077 := bstep (se 4 (by rfl) ⟨48412413, by rfl⟩ : syracuseStep 516399077 = 96824827) B96824827
theorem B2359423 : Blo 1307972 2359423 := bstep (se 1 (by rfl) ⟨1769567, by rfl⟩ : syracuseStep 2359423 = 3539135) B3539135
theorem B25510247 : Blo 1307972 25510247 := bstep (se 1 (by rfl) ⟨19132685, by rfl⟩ : syracuseStep 25510247 = 38265371) B38265371
theorem B4973147 : Blo 1307972 4973147 := bstep (se 1 (by rfl) ⟨3729860, by rfl⟩ : syracuseStep 4973147 = 7459721) B7459721
theorem B4416551 : Blo 1307972 4416551 := bstep (se 1 (by rfl) ⟨3312413, by rfl⟩ : syracuseStep 4416551 = 6624827) B6624827
theorem B7963687 : Blo 1307972 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B11175023 : Blo 1307972 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B16131565 : Blo 1307972 16131565 := bstep (se 3 (by rfl) ⟨3024668, by rfl⟩ : syracuseStep 16131565 = 6049337) B6049337
theorem B2483855 : Blo 1307972 2483855 := bstep (se 1 (by rfl) ⟨1862891, by rfl⟩ : syracuseStep 2483855 = 3725783) B3725783
theorem B51046037 : Blo 1307972 51046037 := bstep (se 6 (by rfl) ⟨1196391, by rfl⟩ : syracuseStep 51046037 = 2392783) B2392783
theorem B9938699 : Blo 1307972 9938699 := bstep (se 1 (by rfl) ⟨7454024, by rfl⟩ : syracuseStep 9938699 = 14908049) B14908049
theorem B11061193 : Blo 1307972 11061193 := bstep (se 2 (by rfl) ⟨4147947, by rfl⟩ : syracuseStep 11061193 = 8295895) B8295895
theorem B2942945 : Blo 1307972 2942945 := bstep (se 2 (by rfl) ⟨1103604, by rfl⟩ : syracuseStep 2942945 = 2207209) B2207209
theorem B20138017 : Blo 1307972 20138017 := bstep (se 2 (by rfl) ⟨7551756, by rfl⟩ : syracuseStep 20138017 = 15103513) B15103513
theorem B2943017 : Blo 1307972 2943017 := bstep (se 2 (by rfl) ⟨1103631, by rfl⟩ : syracuseStep 2943017 = 2207263) B2207263
theorem B4417631 : Blo 1307972 4417631 := bstep (se 1 (by rfl) ⟨3313223, by rfl⟩ : syracuseStep 4417631 = 6626447) B6626447
theorem B3311867 : Blo 1307972 3311867 := bstep (se 1 (by rfl) ⟨2483900, by rfl⟩ : syracuseStep 3311867 = 4967801) B4967801
theorem B2943359 : Blo 1307972 2943359 := bstep (se 1 (by rfl) ⟨2207519, by rfl⟩ : syracuseStep 2943359 = 4415039) B4415039
theorem B2485343 : Blo 1307972 2485343 := bstep (se 1 (by rfl) ⟨1864007, by rfl⟩ : syracuseStep 2485343 = 3728015) B3728015
theorem B5590367 : Blo 1307972 5590367 := bstep (se 1 (by rfl) ⟨4192775, by rfl⟩ : syracuseStep 5590367 = 8385551) B8385551
theorem B103419251 : Blo 1307972 103419251 := bstep (se 1 (by rfl) ⟨77564438, by rfl⟩ : syracuseStep 103419251 = 155128877) B155128877
theorem B6622721 : Blo 1307972 6622721 := bstep (se 2 (by rfl) ⟨2483520, by rfl⟩ : syracuseStep 6622721 = 4967041) B4967041
theorem B1863199 : Blo 1307972 1863199 := bstep (se 1 (by rfl) ⟨1397399, by rfl⟩ : syracuseStep 1863199 = 2794799) B2794799
theorem B7081643 : Blo 1307972 7081643 := bstep (se 1 (by rfl) ⟨5311232, by rfl⟩ : syracuseStep 7081643 = 10622465) B10622465
theorem B4419359 : Blo 1307972 4419359 := bstep (se 1 (by rfl) ⟨3314519, by rfl⟩ : syracuseStep 4419359 = 6629039) B6629039
theorem B2207567 : Blo 1307972 2207567 := bstep (se 1 (by rfl) ⟨1655675, by rfl⟩ : syracuseStep 2207567 = 3311351) B3311351
theorem B3313487 : Blo 1307972 3313487 := bstep (se 1 (by rfl) ⟨2485115, by rfl⟩ : syracuseStep 3313487 = 4970231) B4970231
theorem B4419575 : Blo 1307972 4419575 := bstep (se 1 (by rfl) ⟨3314681, by rfl⟩ : syracuseStep 4419575 = 6629363) B6629363
theorem B1962047 : Blo 1307972 1962047 := bstep (se 1 (by rfl) ⟨1471535, by rfl⟩ : syracuseStep 1962047 = 2943071) B2943071
theorem B77516999 : Blo 1307972 77516999 := bstep (se 1 (by rfl) ⟨58137749, by rfl⟩ : syracuseStep 77516999 = 116275499) B116275499
theorem B5591339 : Blo 1307972 5591339 := bstep (se 1 (by rfl) ⟨4193504, by rfl⟩ : syracuseStep 5591339 = 8387009) B8387009
theorem B9441613 : Blo 1307972 9441613 := bstep (se 3 (by rfl) ⟨1770302, by rfl⟩ : syracuseStep 9441613 = 3540605) B3540605
theorem B4420169 : Blo 1307972 4420169 := bstep (se 2 (by rfl) ⟨1657563, by rfl⟩ : syracuseStep 4420169 = 3315127) B3315127
theorem B4420655 : Blo 1307972 4420655 := bstep (se 1 (by rfl) ⟨3315491, by rfl⟩ : syracuseStep 4420655 = 6630983) B6630983
theorem B3314783 : Blo 1307972 3314783 := bstep (se 1 (by rfl) ⟨2486087, by rfl⟩ : syracuseStep 3314783 = 4972175) B4972175
theorem B2209079 : Blo 1307972 2209079 := bstep (se 1 (by rfl) ⟨1656809, by rfl⟩ : syracuseStep 2209079 = 3313619) B3313619
theorem B344266051 : Blo 1307972 344266051 := bstep (se 1 (by rfl) ⟨258199538, by rfl⟩ : syracuseStep 344266051 = 516399077) B516399077
theorem B1963343 : Blo 1307972 1963343 := bstep (se 1 (by rfl) ⟨1472507, by rfl⟩ : syracuseStep 1963343 = 2945015) B2945015
theorem B1963385 : Blo 1307972 1963385 := bstep (se 2 (by rfl) ⟨736269, by rfl⟩ : syracuseStep 1963385 = 1472539) B1472539
theorem B1308127 : Blo 1307972 1308127 := bstep (se 1 (by rfl) ⟨981095, by rfl⟩ : syracuseStep 1308127 = 1962191) B1962191
theorem B1471999 : Blo 1307972 1471999 := bstep (se 1 (by rfl) ⟨1103999, by rfl⟩ : syracuseStep 1471999 = 2207999) B2207999
theorem B1308207 : Blo 1307972 1308207 := bstep (se 1 (by rfl) ⟨981155, by rfl⟩ : syracuseStep 1308207 = 1962311) B1962311
theorem B1963583 : Blo 1307972 1963583 := bstep (se 1 (by rfl) ⟨1472687, by rfl⟩ : syracuseStep 1963583 = 2945375) B2945375
theorem B1308519 : Blo 1307972 1308519 := bstep (se 1 (by rfl) ⟨981389, by rfl⟩ : syracuseStep 1308519 = 1962779) B1962779
theorem B1398655 : Blo 1307972 1398655 := bstep (se 1 (by rfl) ⟨1048991, by rfl⟩ : syracuseStep 1398655 = 2097983) B2097983
theorem B1963931 : Blo 1307972 1963931 := bstep (se 1 (by rfl) ⟨1472948, by rfl⟩ : syracuseStep 1963931 = 2945897) B2945897
theorem B9934811 : Blo 1307972 9934811 := bstep (se 1 (by rfl) ⟨7451108, by rfl⟩ : syracuseStep 9934811 = 14902217) B14902217
theorem B1308703 : Blo 1307972 1308703 := bstep (se 1 (by rfl) ⟨981527, by rfl⟩ : syracuseStep 1308703 = 1963055) B1963055
theorem B1964063 : Blo 1307972 1964063 := bstep (se 1 (by rfl) ⟨1473047, by rfl⟩ : syracuseStep 1964063 = 2946095) B2946095
theorem B1308735 : Blo 1307972 1308735 := bstep (se 1 (by rfl) ⟨981551, by rfl⟩ : syracuseStep 1308735 = 1963103) B1963103
theorem B1308775 : Blo 1307972 1308775 := bstep (se 1 (by rfl) ⟨981581, by rfl⟩ : syracuseStep 1308775 = 1963163) B1963163
theorem B1308783 : Blo 1307972 1308783 := bstep (se 1 (by rfl) ⟨981587, by rfl⟩ : syracuseStep 1308783 = 1963175) B1963175
theorem B1309231 : Blo 1307972 1309231 := bstep (se 1 (by rfl) ⟨981923, by rfl⟩ : syracuseStep 1309231 = 1963847) B1963847
theorem B1964591 : Blo 1307972 1964591 := bstep (se 1 (by rfl) ⟨1473443, by rfl⟩ : syracuseStep 1964591 = 2946887) B2946887
theorem B1473151 : Blo 1307972 1473151 := bstep (se 1 (by rfl) ⟨1104863, by rfl⟩ : syracuseStep 1473151 = 2209727) B2209727
theorem B1309351 : Blo 1307972 1309351 := bstep (se 1 (by rfl) ⟨982013, by rfl⟩ : syracuseStep 1309351 = 1964027) B1964027
theorem B1964711 : Blo 1307972 1964711 := bstep (se 1 (by rfl) ⟨1473533, by rfl⟩ : syracuseStep 1964711 = 2947067) B2947067
theorem B1309391 : Blo 1307972 1309391 := bstep (se 1 (by rfl) ⟨982043, by rfl⟩ : syracuseStep 1309391 = 1964087) B1964087
theorem B20151017 : Blo 1307972 20151017 := bstep (se 2 (by rfl) ⟨7556631, by rfl⟩ : syracuseStep 20151017 = 15113263) B15113263
theorem B2358011 : Blo 1307972 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B1309435 : Blo 1307972 1309435 := bstep (se 1 (by rfl) ⟨982076, by rfl⟩ : syracuseStep 1309435 = 1964153) B1964153
theorem B1964795 : Blo 1307972 1964795 := bstep (se 1 (by rfl) ⟨1473596, by rfl⟩ : syracuseStep 1964795 = 2947193) B2947193
theorem B1309471 : Blo 1307972 1309471 := bstep (se 1 (by rfl) ⟨982103, by rfl⟩ : syracuseStep 1309471 = 1964207) B1964207
theorem B1964831 : Blo 1307972 1964831 := bstep (se 1 (by rfl) ⟨1473623, by rfl⟩ : syracuseStep 1964831 = 2947247) B2947247
theorem B1964921 : Blo 1307972 1964921 := bstep (se 2 (by rfl) ⟨736845, by rfl⟩ : syracuseStep 1964921 = 1473691) B1473691
theorem B4193147 : Blo 1307972 4193147 := bstep (se 1 (by rfl) ⟨3144860, by rfl⟩ : syracuseStep 4193147 = 6289721) B6289721
theorem B4971401 : Blo 1307972 4971401 := bstep (se 2 (by rfl) ⟨1864275, by rfl⟩ : syracuseStep 4971401 = 3728551) B3728551
theorem B9935783 : Blo 1307972 9935783 := bstep (se 1 (by rfl) ⟨7451837, by rfl⟩ : syracuseStep 9935783 = 14903675) B14903675
theorem B25164715 : Blo 1307972 25164715 := bstep (se 1 (by rfl) ⟨18873536, by rfl⟩ : syracuseStep 25164715 = 37747073) B37747073
theorem B1309631 : Blo 1307972 1309631 := bstep (se 1 (by rfl) ⟨982223, by rfl⟩ : syracuseStep 1309631 = 1964447) B1964447
theorem B1309691 : Blo 1307972 1309691 := bstep (se 1 (by rfl) ⟨982268, by rfl⟩ : syracuseStep 1309691 = 1964537) B1964537
theorem B4971719 : Blo 1307972 4971719 := bstep (se 1 (by rfl) ⟨3728789, by rfl⟩ : syracuseStep 4971719 = 7457579) B7457579
theorem B14154983 : Blo 1307972 14154983 := bstep (se 1 (by rfl) ⟨10616237, by rfl⟩ : syracuseStep 14154983 = 21232475) B21232475
theorem B4414715 : Blo 1307972 4414715 := bstep (se 1 (by rfl) ⟨3311036, by rfl⟩ : syracuseStep 4414715 = 6622073) B6622073
theorem B9944531 : Blo 1307972 9944531 := bstep (se 1 (by rfl) ⟨7458398, by rfl⟩ : syracuseStep 9944531 = 14916797) B14916797
theorem B13434457 : Blo 1307972 13434457 := bstep (se 2 (by rfl) ⟨5037921, by rfl⟩ : syracuseStep 13434457 = 10075843) B10075843
theorem B193625977 : Blo 1307972 193625977 := bstep (se 2 (by rfl) ⟨72609741, by rfl⟩ : syracuseStep 193625977 = 145219483) B145219483
theorem B7454663 : Blo 1307972 7454663 := bstep (se 1 (by rfl) ⟨5590997, by rfl⟩ : syracuseStep 7454663 = 11181995) B11181995
theorem B3145897 : Blo 1307972 3145897 := bstep (se 2 (by rfl) ⟨1179711, by rfl⟩ : syracuseStep 3145897 = 2359423) B2359423
theorem B3727559 : Blo 1307972 3727559 := bstep (se 1 (by rfl) ⟨2795669, by rfl⟩ : syracuseStep 3727559 = 5591339) B5591339
theorem B17006831 : Blo 1307972 17006831 := bstep (se 1 (by rfl) ⟨12755123, by rfl⟩ : syracuseStep 17006831 = 25510247) B25510247
theorem B6627581 : Blo 1307972 6627581 := bstep (se 3 (by rfl) ⟨1242671, by rfl⟩ : syracuseStep 6627581 = 2485343) B2485343
theorem B1655903 : Blo 1307972 1655903 := bstep (se 1 (by rfl) ⟨1241927, by rfl⟩ : syracuseStep 1655903 = 2483855) B2483855
theorem B34030691 : Blo 1307972 34030691 := bstep (se 1 (by rfl) ⟨25523018, by rfl⟩ : syracuseStep 34030691 = 51046037) B51046037
theorem B2795431 : Blo 1307972 2795431 := bstep (se 1 (by rfl) ⟨2096573, by rfl⟩ : syracuseStep 2795431 = 4193147) B4193147
theorem B2484265 : Blo 1307972 2484265 := bstep (se 2 (by rfl) ⟨931599, by rfl⟩ : syracuseStep 2484265 = 1863199) B1863199
theorem B2943143 : Blo 1307972 2943143 := bstep (se 1 (by rfl) ⟨2207357, by rfl⟩ : syracuseStep 2943143 = 4414715) B4414715
theorem B68946167 : Blo 1307972 68946167 := bstep (se 1 (by rfl) ⟨51709625, by rfl⟩ : syracuseStep 68946167 = 103419251) B103419251
theorem B6629687 : Blo 1307972 6629687 := bstep (se 1 (by rfl) ⟨4972265, by rfl⟩ : syracuseStep 6629687 = 9944531) B9944531
theorem B4721095 : Blo 1307972 4721095 := bstep (se 1 (by rfl) ⟨3540821, by rfl⟩ : syracuseStep 4721095 = 7081643) B7081643
theorem B14748257 : Blo 1307972 14748257 := bstep (se 2 (by rfl) ⟨5530596, by rfl⟩ : syracuseStep 14748257 = 11061193) B11061193
theorem B51677999 : Blo 1307972 51677999 := bstep (se 1 (by rfl) ⟨38758499, by rfl⟩ : syracuseStep 51677999 = 77516999) B77516999
theorem B2944367 : Blo 1307972 2944367 := bstep (se 1 (by rfl) ⟨2208275, by rfl⟩ : syracuseStep 2944367 = 4416551) B4416551
theorem B7450015 : Blo 1307972 7450015 := bstep (se 1 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 7450015 = 11175023) B11175023
theorem B6623207 : Blo 1307972 6623207 := bstep (se 1 (by rfl) ⟨4967405, by rfl⟩ : syracuseStep 6623207 = 9934811) B9934811
theorem B1961963 : Blo 1307972 1961963 := bstep (se 1 (by rfl) ⟨1471472, by rfl⟩ : syracuseStep 1961963 = 2942945) B2942945
theorem B1962011 : Blo 1307972 1962011 := bstep (se 1 (by rfl) ⟨1471508, by rfl⟩ : syracuseStep 1962011 = 2943017) B2943017
theorem B2945087 : Blo 1307972 2945087 := bstep (se 1 (by rfl) ⟨2208815, by rfl⟩ : syracuseStep 2945087 = 4417631) B4417631
theorem B2207911 : Blo 1307972 2207911 := bstep (se 1 (by rfl) ⟨1655933, by rfl⟩ : syracuseStep 2207911 = 3311867) B3311867
theorem B1962239 : Blo 1307972 1962239 := bstep (se 1 (by rfl) ⟨1471679, by rfl⟩ : syracuseStep 1962239 = 2943359) B2943359
theorem B3314267 : Blo 1307972 3314267 := bstep (se 1 (by rfl) ⟨2485700, by rfl⟩ : syracuseStep 3314267 = 4971401) B4971401
theorem B6623855 : Blo 1307972 6623855 := bstep (se 1 (by rfl) ⟨4967891, by rfl⟩ : syracuseStep 6623855 = 9935783) B9935783
theorem B21508753 : Blo 1307972 21508753 := bstep (se 2 (by rfl) ⟨8065782, by rfl⟩ : syracuseStep 21508753 = 16131565) B16131565
theorem B6288029 : Blo 1307972 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B1962665 : Blo 1307972 1962665 := bstep (se 2 (by rfl) ⟨735999, by rfl⟩ : syracuseStep 1962665 = 1471999) B1471999
theorem B17912609 : Blo 1307972 17912609 := bstep (se 2 (by rfl) ⟨6717228, by rfl⟩ : syracuseStep 17912609 = 13434457) B13434457
theorem B3314479 : Blo 1307972 3314479 := bstep (se 1 (by rfl) ⟨2485859, by rfl⟩ : syracuseStep 3314479 = 4971719) B4971719
theorem B258167969 : Blo 1307972 258167969 := bstep (se 2 (by rfl) ⟨96812988, by rfl⟩ : syracuseStep 258167969 = 193625977) B193625977
theorem B1864873 : Blo 1307972 1864873 := bstep (se 2 (by rfl) ⟨699327, by rfl⟩ : syracuseStep 1864873 = 1398655) B1398655
theorem B2946239 : Blo 1307972 2946239 := bstep (se 1 (by rfl) ⟨2209679, by rfl⟩ : syracuseStep 2946239 = 4419359) B4419359
theorem B1471711 : Blo 1307972 1471711 := bstep (se 1 (by rfl) ⟨1103783, by rfl⟩ : syracuseStep 1471711 = 2207567) B2207567
theorem B2208991 : Blo 1307972 2208991 := bstep (se 1 (by rfl) ⟨1656743, by rfl⟩ : syracuseStep 2208991 = 3313487) B3313487
theorem B4969775 : Blo 1307972 4969775 := bstep (se 1 (by rfl) ⟨3727331, by rfl⟩ : syracuseStep 4969775 = 7454663) B7454663
theorem B2946383 : Blo 1307972 2946383 := bstep (se 1 (by rfl) ⟨2209787, by rfl⟩ : syracuseStep 2946383 = 4419575) B4419575
theorem B1308031 : Blo 1307972 1308031 := bstep (se 1 (by rfl) ⟨981023, by rfl⟩ : syracuseStep 1308031 = 1962047) B1962047
theorem B26850689 : Blo 1307972 26850689 := bstep (se 2 (by rfl) ⟨10069008, by rfl⟩ : syracuseStep 26850689 = 20138017) B20138017
theorem B42472997 : Blo 1307972 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B2946779 : Blo 1307972 2946779 := bstep (se 1 (by rfl) ⟨2210084, by rfl⟩ : syracuseStep 2946779 = 4420169) B4420169
theorem B3315431 : Blo 1307972 3315431 := bstep (se 1 (by rfl) ⟨2486573, by rfl⟩ : syracuseStep 3315431 = 4973147) B4973147
theorem B12588817 : Blo 1307972 12588817 := bstep (se 2 (by rfl) ⟨4720806, by rfl⟩ : syracuseStep 12588817 = 9441613) B9441613
theorem B2947103 : Blo 1307972 2947103 := bstep (se 1 (by rfl) ⟨2210327, by rfl⟩ : syracuseStep 2947103 = 4420655) B4420655
theorem B2209855 : Blo 1307972 2209855 := bstep (se 1 (by rfl) ⟨1657391, by rfl⟩ : syracuseStep 2209855 = 3314783) B3314783
theorem B1964201 : Blo 1307972 1964201 := bstep (se 2 (by rfl) ⟨736575, by rfl⟩ : syracuseStep 1964201 = 1473151) B1473151
theorem B1472719 : Blo 1307972 1472719 := bstep (se 1 (by rfl) ⟨1104539, by rfl⟩ : syracuseStep 1472719 = 2209079) B2209079
theorem B1308895 : Blo 1307972 1308895 := bstep (se 1 (by rfl) ⟨981671, by rfl⟩ : syracuseStep 1308895 = 1963343) B1963343
theorem B1308923 : Blo 1307972 1308923 := bstep (se 1 (by rfl) ⟨981692, by rfl⟩ : syracuseStep 1308923 = 1963385) B1963385
theorem B1309055 : Blo 1307972 1309055 := bstep (se 1 (by rfl) ⟨981791, by rfl⟩ : syracuseStep 1309055 = 1963583) B1963583
theorem B6625799 : Blo 1307972 6625799 := bstep (se 1 (by rfl) ⟨4969349, by rfl⟩ : syracuseStep 6625799 = 9938699) B9938699
theorem B33552953 : Blo 1307972 33552953 := bstep (se 2 (by rfl) ⟨12582357, by rfl⟩ : syracuseStep 33552953 = 25164715) B25164715
theorem B1309287 : Blo 1307972 1309287 := bstep (se 1 (by rfl) ⟨981965, by rfl⟩ : syracuseStep 1309287 = 1963931) B1963931
theorem B1309375 : Blo 1307972 1309375 := bstep (se 1 (by rfl) ⟨982031, by rfl⟩ : syracuseStep 1309375 = 1964063) B1964063
theorem B1309727 : Blo 1307972 1309727 := bstep (se 1 (by rfl) ⟨982295, by rfl⟩ : syracuseStep 1309727 = 1964591) B1964591
theorem B459021401 : Blo 1307972 459021401 := bstep (se 2 (by rfl) ⟨172133025, by rfl⟩ : syracuseStep 459021401 = 344266051) B344266051
theorem B1309807 : Blo 1307972 1309807 := bstep (se 1 (by rfl) ⟨982355, by rfl⟩ : syracuseStep 1309807 = 1964711) B1964711
theorem B13434011 : Blo 1307972 13434011 := bstep (se 1 (by rfl) ⟨10075508, by rfl⟩ : syracuseStep 13434011 = 20151017) B20151017
theorem B1309863 : Blo 1307972 1309863 := bstep (se 1 (by rfl) ⟨982397, by rfl⟩ : syracuseStep 1309863 = 1964795) B1964795
theorem B1309887 : Blo 1307972 1309887 := bstep (se 1 (by rfl) ⟨982415, by rfl⟩ : syracuseStep 1309887 = 1964831) B1964831
theorem B1309947 : Blo 1307972 1309947 := bstep (se 1 (by rfl) ⟨982460, by rfl⟩ : syracuseStep 1309947 = 1964921) B1964921
theorem B9436655 : Blo 1307972 9436655 := bstep (se 1 (by rfl) ⟨7077491, by rfl⟩ : syracuseStep 9436655 = 14154983) B14154983
theorem B3726911 : Blo 1307972 3726911 := bstep (se 1 (by rfl) ⟨2795183, by rfl⟩ : syracuseStep 3726911 = 5590367) B5590367
theorem B4415147 : Blo 1307972 4415147 := bstep (se 1 (by rfl) ⟨3311360, by rfl⟩ : syracuseStep 4415147 = 6622721) B6622721
theorem B11337887 : Blo 1307972 11337887 := bstep (se 1 (by rfl) ⟨8503415, by rfl⟩ : syracuseStep 11337887 = 17006831) B17006831
theorem B4415741 : Blo 1307972 4415741 := bstep (se 3 (by rfl) ⟨827951, by rfl⟩ : syracuseStep 4415741 = 1655903) B1655903
theorem B4415903 : Blo 1307972 4415903 := bstep (se 1 (by rfl) ⟨3311927, by rfl⟩ : syracuseStep 4415903 = 6623855) B6623855
theorem B16778117 : Blo 1307972 16778117 := bstep (se 4 (by rfl) ⟨1572948, by rfl⟩ : syracuseStep 16778117 = 3145897) B3145897
theorem B9945989 : Blo 1307972 9945989 := bstep (se 4 (by rfl) ⟨932436, by rfl⟩ : syracuseStep 9945989 = 1864873) B1864873
theorem B17900459 : Blo 1307972 17900459 := bstep (se 1 (by rfl) ⟨13425344, by rfl⟩ : syracuseStep 17900459 = 26850689) B26850689
theorem B4417199 : Blo 1307972 4417199 := bstep (se 1 (by rfl) ⟨3312899, by rfl⟩ : syracuseStep 4417199 = 6625799) B6625799
theorem B306014267 : Blo 1307972 306014267 := bstep (se 1 (by rfl) ⟨229510700, by rfl⟩ : syracuseStep 306014267 = 459021401) B459021401
theorem B8956007 : Blo 1307972 8956007 := bstep (se 1 (by rfl) ⟨6717005, by rfl⟩ : syracuseStep 8956007 = 13434011) B13434011
theorem B2484607 : Blo 1307972 2484607 := bstep (se 1 (by rfl) ⟨1863455, by rfl⟩ : syracuseStep 2484607 = 3726911) B3726911
theorem B2943431 : Blo 1307972 2943431 := bstep (se 1 (by rfl) ⟨2207573, by rfl⟩ : syracuseStep 2943431 = 4415147) B4415147
theorem B3312353 : Blo 1307972 3312353 := bstep (se 2 (by rfl) ⟨1242132, by rfl⟩ : syracuseStep 3312353 = 2484265) B2484265
theorem B4418387 : Blo 1307972 4418387 := bstep (se 1 (by rfl) ⟨3313790, by rfl⟩ : syracuseStep 4418387 = 6627581) B6627581
theorem B2943881 : Blo 1307972 2943881 := bstep (se 2 (by rfl) ⟨1103955, by rfl⟩ : syracuseStep 2943881 = 2207911) B2207911
theorem B9940157 : Blo 1307972 9940157 := bstep (se 3 (by rfl) ⟨1863779, by rfl⟩ : syracuseStep 9940157 = 3727559) B3727559
theorem B22687127 : Blo 1307972 22687127 := bstep (se 1 (by rfl) ⟨17015345, by rfl⟩ : syracuseStep 22687127 = 34030691) B34030691
theorem B3313183 : Blo 1307972 3313183 := bstep (se 1 (by rfl) ⟨2484887, by rfl⟩ : syracuseStep 3313183 = 4969775) B4969775
theorem B28315331 : Blo 1307972 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B4419305 : Blo 1307972 4419305 := bstep (se 2 (by rfl) ⟨1657239, by rfl⟩ : syracuseStep 4419305 = 3314479) B3314479
theorem B1962095 : Blo 1307972 1962095 := bstep (se 1 (by rfl) ⟨1471571, by rfl⟩ : syracuseStep 1962095 = 2943143) B2943143
theorem B4419791 : Blo 1307972 4419791 := bstep (se 1 (by rfl) ⟨3314843, by rfl⟩ : syracuseStep 4419791 = 6629687) B6629687
theorem B1962281 : Blo 1307972 1962281 := bstep (se 2 (by rfl) ⟨735855, by rfl⟩ : syracuseStep 1962281 = 1471711) B1471711
theorem B2945321 : Blo 1307972 2945321 := bstep (se 2 (by rfl) ⟨1104495, by rfl⟩ : syracuseStep 2945321 = 2208991) B2208991
theorem B22368635 : Blo 1307972 22368635 := bstep (se 1 (by rfl) ⟨16776476, by rfl⟩ : syracuseStep 22368635 = 33552953) B33552953
theorem B34451999 : Blo 1307972 34451999 := bstep (se 1 (by rfl) ⟨25838999, by rfl⟩ : syracuseStep 34451999 = 51677999) B51677999
theorem B9933353 : Blo 1307972 9933353 := bstep (se 2 (by rfl) ⟨3725007, by rfl⟩ : syracuseStep 9933353 = 7450015) B7450015
theorem B1962911 : Blo 1307972 1962911 := bstep (se 1 (by rfl) ⟨1472183, by rfl⟩ : syracuseStep 1962911 = 2944367) B2944367
theorem B25179173 : Blo 1307972 25179173 := bstep (se 4 (by rfl) ⟨2360547, by rfl⟩ : syracuseStep 25179173 = 4721095) B4721095
theorem B1307975 : Blo 1307972 1307975 := bstep (se 1 (by rfl) ⟨980981, by rfl⟩ : syracuseStep 1307975 = 1961963) B1961963
theorem B1308007 : Blo 1307972 1308007 := bstep (se 1 (by rfl) ⟨981005, by rfl⟩ : syracuseStep 1308007 = 1962011) B1962011
theorem B1963391 : Blo 1307972 1963391 := bstep (se 1 (by rfl) ⟨1472543, by rfl⟩ : syracuseStep 1963391 = 2945087) B2945087
theorem B2946473 : Blo 1307972 2946473 := bstep (se 2 (by rfl) ⟨1104927, by rfl⟩ : syracuseStep 2946473 = 2209855) B2209855
theorem B1308159 : Blo 1307972 1308159 := bstep (se 1 (by rfl) ⟨981119, by rfl⟩ : syracuseStep 1308159 = 1962239) B1962239
theorem B1963625 : Blo 1307972 1963625 := bstep (se 2 (by rfl) ⟨736359, by rfl⟩ : syracuseStep 1963625 = 1472719) B1472719
theorem B2209511 : Blo 1307972 2209511 := bstep (se 1 (by rfl) ⟨1657133, by rfl⟩ : syracuseStep 2209511 = 3314267) B3314267
theorem B4192019 : Blo 1307972 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B1308443 : Blo 1307972 1308443 := bstep (se 1 (by rfl) ⟨981332, by rfl⟩ : syracuseStep 1308443 = 1962665) B1962665
theorem B11941739 : Blo 1307972 11941739 := bstep (se 1 (by rfl) ⟨8956304, by rfl⟩ : syracuseStep 11941739 = 17912609) B17912609
theorem B172111979 : Blo 1307972 172111979 := bstep (se 1 (by rfl) ⟨129083984, by rfl⟩ : syracuseStep 172111979 = 258167969) B258167969
theorem B1964159 : Blo 1307972 1964159 := bstep (se 1 (by rfl) ⟨1473119, by rfl⟩ : syracuseStep 1964159 = 2946239) B2946239
theorem B28678337 : Blo 1307972 28678337 := bstep (se 2 (by rfl) ⟨10754376, by rfl⟩ : syracuseStep 28678337 = 21508753) B21508753
theorem B1964255 : Blo 1307972 1964255 := bstep (se 1 (by rfl) ⟨1473191, by rfl⟩ : syracuseStep 1964255 = 2946383) B2946383
theorem B1964519 : Blo 1307972 1964519 := bstep (se 1 (by rfl) ⟨1473389, by rfl⟩ : syracuseStep 1964519 = 2946779) B2946779
theorem B2210287 : Blo 1307972 2210287 := bstep (se 1 (by rfl) ⟨1657715, by rfl⟩ : syracuseStep 2210287 = 3315431) B3315431
theorem B1964735 : Blo 1307972 1964735 := bstep (se 1 (by rfl) ⟨1473551, by rfl⟩ : syracuseStep 1964735 = 2947103) B2947103
theorem B1309467 : Blo 1307972 1309467 := bstep (se 1 (by rfl) ⟨982100, by rfl⟩ : syracuseStep 1309467 = 1964201) B1964201
theorem B45964111 : Blo 1307972 45964111 := bstep (se 1 (by rfl) ⟨34473083, by rfl⟩ : syracuseStep 45964111 = 68946167) B68946167
theorem B39328685 : Blo 1307972 39328685 := bstep (se 3 (by rfl) ⟨7374128, by rfl⟩ : syracuseStep 39328685 = 14748257) B14748257
theorem B6291103 : Blo 1307972 6291103 := bstep (se 1 (by rfl) ⟨4718327, by rfl⟩ : syracuseStep 6291103 = 9436655) B9436655
theorem B16785089 : Blo 1307972 16785089 := bstep (se 2 (by rfl) ⟨6294408, by rfl⟩ : syracuseStep 16785089 = 12588817) B12588817
theorem B3727241 : Blo 1307972 3727241 := bstep (se 2 (by rfl) ⟨1397715, by rfl⟩ : syracuseStep 3727241 = 2795431) B2795431
theorem B4415471 : Blo 1307972 4415471 := bstep (se 1 (by rfl) ⟨3311603, by rfl⟩ : syracuseStep 4415471 = 6623207) B6623207
theorem B458965277 : Blo 1307972 458965277 := bstep (se 3 (by rfl) ⟨86055989, by rfl⟩ : syracuseStep 458965277 = 172111979) B172111979
theorem B16786115 : Blo 1307972 16786115 := bstep (se 1 (by rfl) ⟨12589586, by rfl⟩ : syracuseStep 16786115 = 25179173) B25179173
theorem B61285481 : Blo 1307972 61285481 := bstep (se 2 (by rfl) ⟨22982055, by rfl⟩ : syracuseStep 61285481 = 45964111) B45964111
theorem B2794679 : Blo 1307972 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B4417577 : Blo 1307972 4417577 := bstep (se 2 (by rfl) ⟨1656591, by rfl⟩ : syracuseStep 4417577 = 3313183) B3313183
theorem B15124751 : Blo 1307972 15124751 := bstep (se 1 (by rfl) ⟨11343563, by rfl⟩ : syracuseStep 15124751 = 22687127) B22687127
theorem B18876887 : Blo 1307972 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B2484827 : Blo 1307972 2484827 := bstep (se 1 (by rfl) ⟨1863620, by rfl⟩ : syracuseStep 2484827 = 3727241) B3727241
theorem B2943647 : Blo 1307972 2943647 := bstep (se 1 (by rfl) ⟨2207735, by rfl⟩ : syracuseStep 2943647 = 4415471) B4415471
theorem B2943827 : Blo 1307972 2943827 := bstep (se 1 (by rfl) ⟨2207870, by rfl⟩ : syracuseStep 2943827 = 4415741) B4415741
theorem B14912423 : Blo 1307972 14912423 := bstep (se 1 (by rfl) ⟨11184317, by rfl⟩ : syracuseStep 14912423 = 22368635) B22368635
theorem B2943935 : Blo 1307972 2943935 := bstep (se 1 (by rfl) ⟨2207951, by rfl⟩ : syracuseStep 2943935 = 4415903) B4415903
theorem B6622235 : Blo 1307972 6622235 := bstep (se 1 (by rfl) ⟨4966676, by rfl⟩ : syracuseStep 6622235 = 9933353) B9933353
theorem B3312809 : Blo 1307972 3312809 := bstep (se 2 (by rfl) ⟨1242303, by rfl⟩ : syracuseStep 3312809 = 2484607) B2484607
theorem B11185411 : Blo 1307972 11185411 := bstep (se 1 (by rfl) ⟨8389058, by rfl⟩ : syracuseStep 11185411 = 16778117) B16778117
theorem B6630659 : Blo 1307972 6630659 := bstep (se 1 (by rfl) ⟨4972994, by rfl⟩ : syracuseStep 6630659 = 9945989) B9945989
theorem B2944799 : Blo 1307972 2944799 := bstep (se 1 (by rfl) ⟨2208599, by rfl⟩ : syracuseStep 2944799 = 4417199) B4417199
theorem B204009511 : Blo 1307972 204009511 := bstep (se 1 (by rfl) ⟨153007133, by rfl⟩ : syracuseStep 204009511 = 306014267) B306014267
theorem B1962287 : Blo 1307972 1962287 := bstep (se 1 (by rfl) ⟨1471715, by rfl⟩ : syracuseStep 1962287 = 2943431) B2943431
theorem B2208235 : Blo 1307972 2208235 := bstep (se 1 (by rfl) ⟨1656176, by rfl⟩ : syracuseStep 2208235 = 3312353) B3312353
theorem B2945591 : Blo 1307972 2945591 := bstep (se 1 (by rfl) ⟨2209193, by rfl⟩ : syracuseStep 2945591 = 4418387) B4418387
theorem B1962587 : Blo 1307972 1962587 := bstep (se 1 (by rfl) ⟨1471940, by rfl⟩ : syracuseStep 1962587 = 2943881) B2943881
theorem B26219123 : Blo 1307972 26219123 := bstep (se 1 (by rfl) ⟨19664342, by rfl⟩ : syracuseStep 26219123 = 39328685) B39328685
theorem B2946203 : Blo 1307972 2946203 := bstep (se 1 (by rfl) ⟨2209652, by rfl⟩ : syracuseStep 2946203 = 4419305) B4419305
theorem B1308063 : Blo 1307972 1308063 := bstep (se 1 (by rfl) ⟨981047, by rfl⟩ : syracuseStep 1308063 = 1962095) B1962095
theorem B7558591 : Blo 1307972 7558591 := bstep (se 1 (by rfl) ⟨5668943, by rfl⟩ : syracuseStep 7558591 = 11337887) B11337887
theorem B2946527 : Blo 1307972 2946527 := bstep (se 1 (by rfl) ⟨2209895, by rfl⟩ : syracuseStep 2946527 = 4419791) B4419791
theorem B1308187 : Blo 1307972 1308187 := bstep (se 1 (by rfl) ⟨981140, by rfl⟩ : syracuseStep 1308187 = 1962281) B1962281
theorem B1963547 : Blo 1307972 1963547 := bstep (se 1 (by rfl) ⟨1472660, by rfl⟩ : syracuseStep 1963547 = 2945321) B2945321
theorem B22967999 : Blo 1307972 22967999 := bstep (se 1 (by rfl) ⟨17225999, by rfl⟩ : syracuseStep 22967999 = 34451999) B34451999
theorem B1308607 : Blo 1307972 1308607 := bstep (se 1 (by rfl) ⟨981455, by rfl⟩ : syracuseStep 1308607 = 1962911) B1962911
theorem B11933639 : Blo 1307972 11933639 := bstep (se 1 (by rfl) ⟨8950229, by rfl⟩ : syracuseStep 11933639 = 17900459) B17900459
theorem B2947049 : Blo 1307972 2947049 := bstep (se 2 (by rfl) ⟨1105143, by rfl⟩ : syracuseStep 2947049 = 2210287) B2210287
theorem B1308927 : Blo 1307972 1308927 := bstep (se 1 (by rfl) ⟨981695, by rfl⟩ : syracuseStep 1308927 = 1963391) B1963391
theorem B1964315 : Blo 1307972 1964315 := bstep (se 1 (by rfl) ⟨1473236, by rfl⟩ : syracuseStep 1964315 = 2946473) B2946473
theorem B1309083 : Blo 1307972 1309083 := bstep (se 1 (by rfl) ⟨981812, by rfl⟩ : syracuseStep 1309083 = 1963625) B1963625
theorem B1473007 : Blo 1307972 1473007 := bstep (se 1 (by rfl) ⟨1104755, by rfl⟩ : syracuseStep 1473007 = 2209511) B2209511
theorem B7961159 : Blo 1307972 7961159 := bstep (se 1 (by rfl) ⟨5970869, by rfl⟩ : syracuseStep 7961159 = 11941739) B11941739
theorem B5970671 : Blo 1307972 5970671 := bstep (se 1 (by rfl) ⟨4478003, by rfl⟩ : syracuseStep 5970671 = 8956007) B8956007
theorem B1309439 : Blo 1307972 1309439 := bstep (se 1 (by rfl) ⟨982079, by rfl⟩ : syracuseStep 1309439 = 1964159) B1964159
theorem B19118891 : Blo 1307972 19118891 := bstep (se 1 (by rfl) ⟨14339168, by rfl⟩ : syracuseStep 19118891 = 28678337) B28678337
theorem B1309503 : Blo 1307972 1309503 := bstep (se 1 (by rfl) ⟨982127, by rfl⟩ : syracuseStep 1309503 = 1964255) B1964255
theorem B1309679 : Blo 1307972 1309679 := bstep (se 1 (by rfl) ⟨982259, by rfl⟩ : syracuseStep 1309679 = 1964519) B1964519
theorem B1309823 : Blo 1307972 1309823 := bstep (se 1 (by rfl) ⟨982367, by rfl⟩ : syracuseStep 1309823 = 1964735) B1964735
theorem B6626771 : Blo 1307972 6626771 := bstep (se 1 (by rfl) ⟨4970078, by rfl⟩ : syracuseStep 6626771 = 9940157) B9940157
theorem B8388137 : Blo 1307972 8388137 := bstep (se 2 (by rfl) ⟨3145551, by rfl⟩ : syracuseStep 8388137 = 6291103) B6291103
theorem B11190059 : Blo 1307972 11190059 := bstep (se 1 (by rfl) ⟨8392544, by rfl⟩ : syracuseStep 11190059 = 16785089) B16785089
theorem B11190743 : Blo 1307972 11190743 := bstep (se 1 (by rfl) ⟨8393057, by rfl⟩ : syracuseStep 11190743 = 16786115) B16786115
theorem B7955759 : Blo 1307972 7955759 := bstep (se 1 (by rfl) ⟨5966819, by rfl⟩ : syracuseStep 7955759 = 11933639) B11933639
theorem B12584591 : Blo 1307972 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B1656551 : Blo 1307972 1656551 := bstep (se 1 (by rfl) ⟨1242413, by rfl⟩ : syracuseStep 1656551 = 2484827) B2484827
theorem B10078121 : Blo 1307972 10078121 := bstep (se 2 (by rfl) ⟨3779295, by rfl⟩ : syracuseStep 10078121 = 7558591) B7558591
theorem B244991989 : Blo 1307972 244991989 := bstep (se 5 (by rfl) ⟨11483999, by rfl⟩ : syracuseStep 244991989 = 22967999) B22967999
theorem B4417847 : Blo 1307972 4417847 := bstep (se 1 (by rfl) ⟨3313385, by rfl⟩ : syracuseStep 4417847 = 6626771) B6626771
theorem B2944313 : Blo 1307972 2944313 := bstep (se 2 (by rfl) ⟨1104117, by rfl⟩ : syracuseStep 2944313 = 2208235) B2208235
theorem B40856987 : Blo 1307972 40856987 := bstep (se 1 (by rfl) ⟨30642740, by rfl⟩ : syracuseStep 40856987 = 61285481) B61285481
theorem B1863119 : Blo 1307972 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B2945051 : Blo 1307972 2945051 := bstep (se 1 (by rfl) ⟨2208788, by rfl⟩ : syracuseStep 2945051 = 4417577) B4417577
theorem B14913881 : Blo 1307972 14913881 := bstep (se 2 (by rfl) ⟨5592705, by rfl⟩ : syracuseStep 14913881 = 11185411) B11185411
theorem B1962431 : Blo 1307972 1962431 := bstep (se 1 (by rfl) ⟨1471823, by rfl⟩ : syracuseStep 1962431 = 2943647) B2943647
theorem B1962551 : Blo 1307972 1962551 := bstep (se 1 (by rfl) ⟨1471913, by rfl⟩ : syracuseStep 1962551 = 2943827) B2943827
theorem B9941615 : Blo 1307972 9941615 := bstep (se 1 (by rfl) ⟨7456211, by rfl⟩ : syracuseStep 9941615 = 14912423) B14912423
theorem B1962623 : Blo 1307972 1962623 := bstep (se 1 (by rfl) ⟨1471967, by rfl⟩ : syracuseStep 1962623 = 2943935) B2943935
theorem B2208539 : Blo 1307972 2208539 := bstep (se 1 (by rfl) ⟨1656404, by rfl⟩ : syracuseStep 2208539 = 3312809) B3312809
theorem B4420439 : Blo 1307972 4420439 := bstep (se 1 (by rfl) ⟨3315329, by rfl⟩ : syracuseStep 4420439 = 6630659) B6630659
theorem B5592091 : Blo 1307972 5592091 := bstep (se 1 (by rfl) ⟨4194068, by rfl⟩ : syracuseStep 5592091 = 8388137) B8388137
theorem B1963199 : Blo 1307972 1963199 := bstep (se 1 (by rfl) ⟨1472399, by rfl⟩ : syracuseStep 1963199 = 2944799) B2944799
theorem B7460039 : Blo 1307972 7460039 := bstep (se 1 (by rfl) ⟨5595029, by rfl⟩ : syracuseStep 7460039 = 11190059) B11190059
theorem B272012681 : Blo 1307972 272012681 := bstep (se 2 (by rfl) ⟨102004755, by rfl⟩ : syracuseStep 272012681 = 204009511) B204009511
theorem B305976851 : Blo 1307972 305976851 := bstep (se 1 (by rfl) ⟨229482638, by rfl⟩ : syracuseStep 305976851 = 458965277) B458965277
theorem B1308191 : Blo 1307972 1308191 := bstep (se 1 (by rfl) ⟨981143, by rfl⟩ : syracuseStep 1308191 = 1962287) B1962287
theorem B1963727 : Blo 1307972 1963727 := bstep (se 1 (by rfl) ⟨1472795, by rfl⟩ : syracuseStep 1963727 = 2945591) B2945591
theorem B1308391 : Blo 1307972 1308391 := bstep (se 1 (by rfl) ⟨981293, by rfl⟩ : syracuseStep 1308391 = 1962587) B1962587
theorem B17479415 : Blo 1307972 17479415 := bstep (se 1 (by rfl) ⟨13109561, by rfl⟩ : syracuseStep 17479415 = 26219123) B26219123
theorem B1964009 : Blo 1307972 1964009 := bstep (se 2 (by rfl) ⟨736503, by rfl⟩ : syracuseStep 1964009 = 1473007) B1473007
theorem B1964135 : Blo 1307972 1964135 := bstep (se 1 (by rfl) ⟨1473101, by rfl⟩ : syracuseStep 1964135 = 2946203) B2946203
theorem B1964351 : Blo 1307972 1964351 := bstep (se 1 (by rfl) ⟨1473263, by rfl⟩ : syracuseStep 1964351 = 2946527) B2946527
theorem B1309031 : Blo 1307972 1309031 := bstep (se 1 (by rfl) ⟨981773, by rfl⟩ : syracuseStep 1309031 = 1963547) B1963547
theorem B1964699 : Blo 1307972 1964699 := bstep (se 1 (by rfl) ⟨1473524, by rfl⟩ : syracuseStep 1964699 = 2947049) B2947049
theorem B10083167 : Blo 1307972 10083167 := bstep (se 1 (by rfl) ⟨7562375, by rfl⟩ : syracuseStep 10083167 = 15124751) B15124751
theorem B1309543 : Blo 1307972 1309543 := bstep (se 1 (by rfl) ⟨982157, by rfl⟩ : syracuseStep 1309543 = 1964315) B1964315
theorem B5307439 : Blo 1307972 5307439 := bstep (se 1 (by rfl) ⟨3980579, by rfl⟩ : syracuseStep 5307439 = 7961159) B7961159
theorem B3980447 : Blo 1307972 3980447 := bstep (se 1 (by rfl) ⟨2985335, by rfl⟩ : syracuseStep 3980447 = 5970671) B5970671
theorem B12745927 : Blo 1307972 12745927 := bstep (se 1 (by rfl) ⟨9559445, by rfl⟩ : syracuseStep 12745927 = 19118891) B19118891
theorem B4414823 : Blo 1307972 4414823 := bstep (se 1 (by rfl) ⟨3311117, by rfl⟩ : syracuseStep 4414823 = 6622235) B6622235
theorem B6627743 : Blo 1307972 6627743 := bstep (se 1 (by rfl) ⟨4970807, by rfl⟩ : syracuseStep 6627743 = 9941615) B9941615
theorem B4973359 : Blo 1307972 4973359 := bstep (se 1 (by rfl) ⟨3730019, by rfl⟩ : syracuseStep 4973359 = 7460039) B7460039
theorem B8389727 : Blo 1307972 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B6718747 : Blo 1307972 6718747 := bstep (se 1 (by rfl) ⟨5039060, by rfl⟩ : syracuseStep 6718747 = 10078121) B10078121
theorem B7456121 : Blo 1307972 7456121 := bstep (se 2 (by rfl) ⟨2796045, by rfl⟩ : syracuseStep 7456121 = 5592091) B5592091
theorem B4417469 : Blo 1307972 4417469 := bstep (se 3 (by rfl) ⟨828275, by rfl⟩ : syracuseStep 4417469 = 1656551) B1656551
theorem B2943215 : Blo 1307972 2943215 := bstep (se 1 (by rfl) ⟨2207411, by rfl⟩ : syracuseStep 2943215 = 4414823) B4414823
theorem B181341787 : Blo 1307972 181341787 := bstep (se 1 (by rfl) ⟨136006340, by rfl⟩ : syracuseStep 181341787 = 272012681) B272012681
theorem B203984567 : Blo 1307972 203984567 := bstep (se 1 (by rfl) ⟨152988425, by rfl⟩ : syracuseStep 203984567 = 305976851) B305976851
theorem B4968317 : Blo 1307972 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B2945231 : Blo 1307972 2945231 := bstep (se 1 (by rfl) ⟨2208923, by rfl⟩ : syracuseStep 2945231 = 4417847) B4417847
theorem B16994569 : Blo 1307972 16994569 := bstep (se 2 (by rfl) ⟨6372963, by rfl⟩ : syracuseStep 16994569 = 12745927) B12745927
theorem B6722111 : Blo 1307972 6722111 := bstep (se 1 (by rfl) ⟨5041583, by rfl⟩ : syracuseStep 6722111 = 10083167) B10083167
theorem B1962875 : Blo 1307972 1962875 := bstep (se 1 (by rfl) ⟨1472156, by rfl⟩ : syracuseStep 1962875 = 2944313) B2944313
theorem B1963367 : Blo 1307972 1963367 := bstep (se 1 (by rfl) ⟨1472525, by rfl⟩ : syracuseStep 1963367 = 2945051) B2945051
theorem B9942587 : Blo 1307972 9942587 := bstep (se 1 (by rfl) ⟨7456940, by rfl⟩ : syracuseStep 9942587 = 14913881) B14913881
theorem B1308287 : Blo 1307972 1308287 := bstep (se 1 (by rfl) ⟨981215, by rfl⟩ : syracuseStep 1308287 = 1962431) B1962431
theorem B7460495 : Blo 1307972 7460495 := bstep (se 1 (by rfl) ⟨5595371, by rfl⟩ : syracuseStep 7460495 = 11190743) B11190743
theorem B1308367 : Blo 1307972 1308367 := bstep (se 1 (by rfl) ⟨981275, by rfl⟩ : syracuseStep 1308367 = 1962551) B1962551
theorem B1308415 : Blo 1307972 1308415 := bstep (se 1 (by rfl) ⟨981311, by rfl⟩ : syracuseStep 1308415 = 1962623) B1962623
theorem B1472359 : Blo 1307972 1472359 := bstep (se 1 (by rfl) ⟨1104269, by rfl⟩ : syracuseStep 1472359 = 2208539) B2208539
theorem B2946959 : Blo 1307972 2946959 := bstep (se 1 (by rfl) ⟨2210219, by rfl⟩ : syracuseStep 2946959 = 4420439) B4420439
theorem B21215357 : Blo 1307972 21215357 := bstep (se 3 (by rfl) ⟨3977879, by rfl⟩ : syracuseStep 21215357 = 7955759) B7955759
theorem B1308799 : Blo 1307972 1308799 := bstep (se 1 (by rfl) ⟨981599, by rfl⟩ : syracuseStep 1308799 = 1963199) B1963199
theorem B1309151 : Blo 1307972 1309151 := bstep (se 1 (by rfl) ⟨981863, by rfl⟩ : syracuseStep 1309151 = 1963727) B1963727
theorem B1309339 : Blo 1307972 1309339 := bstep (se 1 (by rfl) ⟨982004, by rfl⟩ : syracuseStep 1309339 = 1964009) B1964009
theorem B7076585 : Blo 1307972 7076585 := bstep (se 2 (by rfl) ⟨2653719, by rfl⟩ : syracuseStep 7076585 = 5307439) B5307439
theorem B1309423 : Blo 1307972 1309423 := bstep (se 1 (by rfl) ⟨982067, by rfl⟩ : syracuseStep 1309423 = 1964135) B1964135
theorem B1309567 : Blo 1307972 1309567 := bstep (se 1 (by rfl) ⟨982175, by rfl⟩ : syracuseStep 1309567 = 1964351) B1964351
theorem B1309799 : Blo 1307972 1309799 := bstep (se 1 (by rfl) ⟨982349, by rfl⟩ : syracuseStep 1309799 = 1964699) B1964699
theorem B46611773 : Blo 1307972 46611773 := bstep (se 3 (by rfl) ⟨8739707, by rfl⟩ : syracuseStep 46611773 = 17479415) B17479415
theorem B2653631 : Blo 1307972 2653631 := bstep (se 1 (by rfl) ⟨1990223, by rfl⟩ : syracuseStep 2653631 = 3980447) B3980447
theorem B27237991 : Blo 1307972 27237991 := bstep (se 1 (by rfl) ⟨20428493, by rfl⟩ : syracuseStep 27237991 = 40856987) B40856987
theorem B326655985 : Blo 1307972 326655985 := bstep (se 2 (by rfl) ⟨122495994, by rfl⟩ : syracuseStep 326655985 = 244991989) B244991989
theorem B22659425 : Blo 1307972 22659425 := bstep (se 2 (by rfl) ⟨8497284, by rfl⟩ : syracuseStep 22659425 = 16994569) B16994569
theorem B4481407 : Blo 1307972 4481407 := bstep (se 1 (by rfl) ⟨3361055, by rfl⟩ : syracuseStep 4481407 = 6722111) B6722111
theorem B6628391 : Blo 1307972 6628391 := bstep (se 1 (by rfl) ⟨4971293, by rfl⟩ : syracuseStep 6628391 = 9942587) B9942587
theorem B4973663 : Blo 1307972 4973663 := bstep (se 1 (by rfl) ⟨3730247, by rfl⟩ : syracuseStep 4973663 = 7460495) B7460495
theorem B241789049 : Blo 1307972 241789049 := bstep (se 2 (by rfl) ⟨90670893, by rfl⟩ : syracuseStep 241789049 = 181341787) B181341787
theorem B36317321 : Blo 1307972 36317321 := bstep (se 2 (by rfl) ⟨13618995, by rfl⟩ : syracuseStep 36317321 = 27237991) B27237991
theorem B31074515 : Blo 1307972 31074515 := bstep (se 1 (by rfl) ⟨23305886, by rfl⟩ : syracuseStep 31074515 = 46611773) B46611773
theorem B135989711 : Blo 1307972 135989711 := bstep (se 1 (by rfl) ⟨101992283, by rfl⟩ : syracuseStep 135989711 = 203984567) B203984567
theorem B3312211 : Blo 1307972 3312211 := bstep (se 1 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 3312211 = 4968317) B4968317
theorem B4418495 : Blo 1307972 4418495 := bstep (se 1 (by rfl) ⟨3313871, by rfl⟩ : syracuseStep 4418495 = 6627743) B6627743
theorem B6631145 : Blo 1307972 6631145 := bstep (se 2 (by rfl) ⟨2486679, by rfl⟩ : syracuseStep 6631145 = 4973359) B4973359
theorem B2944979 : Blo 1307972 2944979 := bstep (se 1 (by rfl) ⟨2208734, by rfl⟩ : syracuseStep 2944979 = 4417469) B4417469
theorem B14143571 : Blo 1307972 14143571 := bstep (se 1 (by rfl) ⟨10607678, by rfl⟩ : syracuseStep 14143571 = 21215357) B21215357
theorem B1962143 : Blo 1307972 1962143 := bstep (se 1 (by rfl) ⟨1471607, by rfl⟩ : syracuseStep 1962143 = 2943215) B2943215
theorem B8958329 : Blo 1307972 8958329 := bstep (se 2 (by rfl) ⟨3359373, by rfl⟩ : syracuseStep 8958329 = 6718747) B6718747
theorem B18870893 : Blo 1307972 18870893 := bstep (se 3 (by rfl) ⟨3538292, by rfl⟩ : syracuseStep 18870893 = 7076585) B7076585
theorem B1963145 : Blo 1307972 1963145 := bstep (se 2 (by rfl) ⟨736179, by rfl⟩ : syracuseStep 1963145 = 1472359) B1472359
theorem B435541313 : Blo 1307972 435541313 := bstep (se 2 (by rfl) ⟨163327992, by rfl⟩ : syracuseStep 435541313 = 326655985) B326655985
theorem B1963487 : Blo 1307972 1963487 := bstep (se 1 (by rfl) ⟨1472615, by rfl⟩ : syracuseStep 1963487 = 2945231) B2945231
theorem B1308583 : Blo 1307972 1308583 := bstep (se 1 (by rfl) ⟨981437, by rfl⟩ : syracuseStep 1308583 = 1962875) B1962875
theorem B5593151 : Blo 1307972 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B1308911 : Blo 1307972 1308911 := bstep (se 1 (by rfl) ⟨981683, by rfl⟩ : syracuseStep 1308911 = 1963367) B1963367
theorem B4970747 : Blo 1307972 4970747 := bstep (se 1 (by rfl) ⟨3728060, by rfl⟩ : syracuseStep 4970747 = 7456121) B7456121
theorem B1964639 : Blo 1307972 1964639 := bstep (se 1 (by rfl) ⟨1473479, by rfl⟩ : syracuseStep 1964639 = 2946959) B2946959
theorem B1769087 : Blo 1307972 1769087 := bstep (se 1 (by rfl) ⟨1326815, by rfl⟩ : syracuseStep 1769087 = 2653631) B2653631
theorem B9429047 : Blo 1307972 9429047 := bstep (se 1 (by rfl) ⟨7071785, by rfl⟩ : syracuseStep 9429047 = 14143571) B14143571
theorem B15106283 : Blo 1307972 15106283 := bstep (se 1 (by rfl) ⟨11329712, by rfl⟩ : syracuseStep 15106283 = 22659425) B22659425
theorem B5972219 : Blo 1307972 5972219 := bstep (se 1 (by rfl) ⟨4479164, by rfl⟩ : syracuseStep 5972219 = 8958329) B8958329
theorem B4416281 : Blo 1307972 4416281 := bstep (se 2 (by rfl) ⟨1656105, by rfl⟩ : syracuseStep 4416281 = 3312211) B3312211
theorem B3728767 : Blo 1307972 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B5975209 : Blo 1307972 5975209 := bstep (se 2 (by rfl) ⟨2240703, by rfl⟩ : syracuseStep 5975209 = 4481407) B4481407
theorem B4418927 : Blo 1307972 4418927 := bstep (se 1 (by rfl) ⟨3314195, by rfl⟩ : syracuseStep 4418927 = 6628391) B6628391
theorem B290360875 : Blo 1307972 290360875 := bstep (se 1 (by rfl) ⟨217770656, by rfl⟩ : syracuseStep 290360875 = 435541313) B435541313
theorem B24211547 : Blo 1307972 24211547 := bstep (se 1 (by rfl) ⟨18158660, by rfl⟩ : syracuseStep 24211547 = 36317321) B36317321
theorem B3313831 : Blo 1307972 3313831 := bstep (se 1 (by rfl) ⟨2485373, by rfl⟩ : syracuseStep 3313831 = 4970747) B4970747
theorem B2945663 : Blo 1307972 2945663 := bstep (se 1 (by rfl) ⟨2209247, by rfl⟩ : syracuseStep 2945663 = 4418495) B4418495
theorem B4420763 : Blo 1307972 4420763 := bstep (se 1 (by rfl) ⟨3315572, by rfl⟩ : syracuseStep 4420763 = 6631145) B6631145
theorem B1963319 : Blo 1307972 1963319 := bstep (se 1 (by rfl) ⟨1472489, by rfl⟩ : syracuseStep 1963319 = 2944979) B2944979
theorem B1308095 : Blo 1307972 1308095 := bstep (se 1 (by rfl) ⟨981071, by rfl⟩ : syracuseStep 1308095 = 1962143) B1962143
theorem B12580595 : Blo 1307972 12580595 := bstep (se 1 (by rfl) ⟨9435446, by rfl⟩ : syracuseStep 12580595 = 18870893) B18870893
theorem B3315775 : Blo 1307972 3315775 := bstep (se 1 (by rfl) ⟨2486831, by rfl⟩ : syracuseStep 3315775 = 4973663) B4973663
theorem B1308763 : Blo 1307972 1308763 := bstep (se 1 (by rfl) ⟨981572, by rfl⟩ : syracuseStep 1308763 = 1963145) B1963145
theorem B1308991 : Blo 1307972 1308991 := bstep (se 1 (by rfl) ⟨981743, by rfl⟩ : syracuseStep 1308991 = 1963487) B1963487
theorem B161192699 : Blo 1307972 161192699 := bstep (se 1 (by rfl) ⟨120894524, by rfl⟩ : syracuseStep 161192699 = 241789049) B241789049
theorem B20716343 : Blo 1307972 20716343 := bstep (se 1 (by rfl) ⟨15537257, by rfl⟩ : syracuseStep 20716343 = 31074515) B31074515
theorem B90659807 : Blo 1307972 90659807 := bstep (se 1 (by rfl) ⟨67994855, by rfl⟩ : syracuseStep 90659807 = 135989711) B135989711
theorem B4717565 : Blo 1307972 4717565 := bstep (se 3 (by rfl) ⟨884543, by rfl⟩ : syracuseStep 4717565 = 1769087) B1769087
theorem B1309759 : Blo 1307972 1309759 := bstep (se 1 (by rfl) ⟨982319, by rfl⟩ : syracuseStep 1309759 = 1964639) B1964639
theorem B3981479 : Blo 1307972 3981479 := bstep (se 1 (by rfl) ⟨2986109, by rfl⟩ : syracuseStep 3981479 = 5972219) B5972219
theorem B387147833 : Blo 1307972 387147833 := bstep (se 2 (by rfl) ⟨145180437, by rfl⟩ : syracuseStep 387147833 = 290360875) B290360875
theorem B6286031 : Blo 1307972 6286031 := bstep (se 1 (by rfl) ⟨4714523, by rfl⟩ : syracuseStep 6286031 = 9429047) B9429047
theorem B16141031 : Blo 1307972 16141031 := bstep (se 1 (by rfl) ⟨12105773, by rfl⟩ : syracuseStep 16141031 = 24211547) B24211547
theorem B10070855 : Blo 1307972 10070855 := bstep (se 1 (by rfl) ⟨7553141, by rfl⟩ : syracuseStep 10070855 = 15106283) B15106283
theorem B4418441 : Blo 1307972 4418441 := bstep (se 2 (by rfl) ⟨1656915, by rfl⟩ : syracuseStep 4418441 = 3313831) B3313831
theorem B2944187 : Blo 1307972 2944187 := bstep (se 1 (by rfl) ⟨2208140, by rfl⟩ : syracuseStep 2944187 = 4416281) B4416281
theorem B7966945 : Blo 1307972 7966945 := bstep (se 2 (by rfl) ⟨2987604, by rfl⟩ : syracuseStep 7966945 = 5975209) B5975209
theorem B2945951 : Blo 1307972 2945951 := bstep (se 1 (by rfl) ⟨2209463, by rfl⟩ : syracuseStep 2945951 = 4418927) B4418927
theorem B4421033 : Blo 1307972 4421033 := bstep (se 2 (by rfl) ⟨1657887, by rfl⟩ : syracuseStep 4421033 = 3315775) B3315775
theorem B1963775 : Blo 1307972 1963775 := bstep (se 1 (by rfl) ⟨1472831, by rfl⟩ : syracuseStep 1963775 = 2945663) B2945663
theorem B2947175 : Blo 1307972 2947175 := bstep (se 1 (by rfl) ⟨2210381, by rfl⟩ : syracuseStep 2947175 = 4420763) B4420763
theorem B1308879 : Blo 1307972 1308879 := bstep (se 1 (by rfl) ⟨981659, by rfl⟩ : syracuseStep 1308879 = 1963319) B1963319
theorem B8387063 : Blo 1307972 8387063 := bstep (se 1 (by rfl) ⟨6290297, by rfl⟩ : syracuseStep 8387063 = 12580595) B12580595
theorem B107461799 : Blo 1307972 107461799 := bstep (se 1 (by rfl) ⟨80596349, by rfl⟩ : syracuseStep 107461799 = 161192699) B161192699
theorem B4971689 : Blo 1307972 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B13810895 : Blo 1307972 13810895 := bstep (se 1 (by rfl) ⟨10358171, by rfl⟩ : syracuseStep 13810895 = 20716343) B20716343
theorem B60439871 : Blo 1307972 60439871 := bstep (se 1 (by rfl) ⟨45329903, by rfl⟩ : syracuseStep 60439871 = 90659807) B90659807
theorem B3145043 : Blo 1307972 3145043 := bstep (se 1 (by rfl) ⟨2358782, by rfl⟩ : syracuseStep 3145043 = 4717565) B4717565
theorem B10617277 : Blo 1307972 10617277 := bstep (se 3 (by rfl) ⟨1990739, by rfl⟩ : syracuseStep 10617277 = 3981479) B3981479
theorem B258098555 : Blo 1307972 258098555 := bstep (se 1 (by rfl) ⟨193573916, by rfl⟩ : syracuseStep 258098555 = 387147833) B387147833
theorem B71641199 : Blo 1307972 71641199 := bstep (se 1 (by rfl) ⟨53730899, by rfl⟩ : syracuseStep 71641199 = 107461799) B107461799
theorem B5591375 : Blo 1307972 5591375 := bstep (se 1 (by rfl) ⟨4193531, by rfl⟩ : syracuseStep 5591375 = 8387063) B8387063
theorem B4190687 : Blo 1307972 4190687 := bstep (se 1 (by rfl) ⟨3143015, by rfl⟩ : syracuseStep 4190687 = 6286031) B6286031
theorem B10760687 : Blo 1307972 10760687 := bstep (se 1 (by rfl) ⟨8070515, by rfl⟩ : syracuseStep 10760687 = 16141031) B16141031
theorem B6713903 : Blo 1307972 6713903 := bstep (se 1 (by rfl) ⟨5035427, by rfl⟩ : syracuseStep 6713903 = 10070855) B10070855
theorem B2945627 : Blo 1307972 2945627 := bstep (se 1 (by rfl) ⟨2209220, by rfl⟩ : syracuseStep 2945627 = 4418441) B4418441
theorem B3314459 : Blo 1307972 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B1962791 : Blo 1307972 1962791 := bstep (se 1 (by rfl) ⟨1472093, by rfl⟩ : syracuseStep 1962791 = 2944187) B2944187
theorem B40293247 : Blo 1307972 40293247 := bstep (se 1 (by rfl) ⟨30219935, by rfl⟩ : syracuseStep 40293247 = 60439871) B60439871
theorem B10622593 : Blo 1307972 10622593 := bstep (se 2 (by rfl) ⟨3983472, by rfl⟩ : syracuseStep 10622593 = 7966945) B7966945
theorem B1963967 : Blo 1307972 1963967 := bstep (se 1 (by rfl) ⟨1472975, by rfl⟩ : syracuseStep 1963967 = 2945951) B2945951
theorem B2947355 : Blo 1307972 2947355 := bstep (se 1 (by rfl) ⟨2210516, by rfl⟩ : syracuseStep 2947355 = 4421033) B4421033
theorem B1309183 : Blo 1307972 1309183 := bstep (se 1 (by rfl) ⟨981887, by rfl⟩ : syracuseStep 1309183 = 1963775) B1963775
theorem B1964783 : Blo 1307972 1964783 := bstep (se 1 (by rfl) ⟨1473587, by rfl⟩ : syracuseStep 1964783 = 2947175) B2947175
theorem B9207263 : Blo 1307972 9207263 := bstep (se 1 (by rfl) ⟨6905447, by rfl⟩ : syracuseStep 9207263 = 13810895) B13810895
theorem B2096695 : Blo 1307972 2096695 := bstep (se 1 (by rfl) ⟨1572521, by rfl⟩ : syracuseStep 2096695 = 3145043) B3145043
theorem B3727583 : Blo 1307972 3727583 := bstep (se 1 (by rfl) ⟨2795687, by rfl⟩ : syracuseStep 3727583 = 5591375) B5591375
theorem B11182373 : Blo 1307972 11182373 := bstep (se 4 (by rfl) ⟨1048347, by rfl⟩ : syracuseStep 11182373 = 2096695) B2096695
theorem B2793791 : Blo 1307972 2793791 := bstep (se 1 (by rfl) ⟨2095343, by rfl⟩ : syracuseStep 2793791 = 4190687) B4190687
theorem B14156369 : Blo 1307972 14156369 := bstep (se 2 (by rfl) ⟨5308638, by rfl⟩ : syracuseStep 14156369 = 10617277) B10617277
theorem B172065703 : Blo 1307972 172065703 := bstep (se 1 (by rfl) ⟨129049277, by rfl⟩ : syracuseStep 172065703 = 258098555) B258098555
theorem B53724329 : Blo 1307972 53724329 := bstep (se 2 (by rfl) ⟨20146623, by rfl⟩ : syracuseStep 53724329 = 40293247) B40293247
theorem B6138175 : Blo 1307972 6138175 := bstep (se 1 (by rfl) ⟨4603631, by rfl⟩ : syracuseStep 6138175 = 9207263) B9207263
theorem B4475935 : Blo 1307972 4475935 := bstep (se 1 (by rfl) ⟨3356951, by rfl⟩ : syracuseStep 4475935 = 6713903) B6713903
theorem B191043197 : Blo 1307972 191043197 := bstep (se 3 (by rfl) ⟨35820599, by rfl⟩ : syracuseStep 191043197 = 71641199) B71641199
theorem B7173791 : Blo 1307972 7173791 := bstep (se 1 (by rfl) ⟨5380343, by rfl⟩ : syracuseStep 7173791 = 10760687) B10760687
theorem B1963751 : Blo 1307972 1963751 := bstep (se 1 (by rfl) ⟨1472813, by rfl⟩ : syracuseStep 1963751 = 2945627) B2945627
theorem B2209639 : Blo 1307972 2209639 := bstep (se 1 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 2209639 = 3314459) B3314459
theorem B1308527 : Blo 1307972 1308527 := bstep (se 1 (by rfl) ⟨981395, by rfl⟩ : syracuseStep 1308527 = 1962791) B1962791
theorem B1309311 : Blo 1307972 1309311 := bstep (se 1 (by rfl) ⟨981983, by rfl⟩ : syracuseStep 1309311 = 1963967) B1963967
theorem B1964903 : Blo 1307972 1964903 := bstep (se 1 (by rfl) ⟨1473677, by rfl⟩ : syracuseStep 1964903 = 2947355) B2947355
theorem B1309855 : Blo 1307972 1309855 := bstep (se 1 (by rfl) ⟨982391, by rfl⟩ : syracuseStep 1309855 = 1964783) B1964783
theorem B14163457 : Blo 1307972 14163457 := bstep (se 2 (by rfl) ⟨5311296, by rfl⟩ : syracuseStep 14163457 = 10622593) B10622593
theorem B7454915 : Blo 1307972 7454915 := bstep (se 1 (by rfl) ⟨5591186, by rfl⟩ : syracuseStep 7454915 = 11182373) B11182373
theorem B9437579 : Blo 1307972 9437579 := bstep (se 1 (by rfl) ⟨7078184, by rfl⟩ : syracuseStep 9437579 = 14156369) B14156369
theorem B8184233 : Blo 1307972 8184233 := bstep (se 2 (by rfl) ⟨3069087, by rfl⟩ : syracuseStep 8184233 = 6138175) B6138175
theorem B35816219 : Blo 1307972 35816219 := bstep (se 1 (by rfl) ⟨26862164, by rfl⟩ : syracuseStep 35816219 = 53724329) B53724329
theorem B127362131 : Blo 1307972 127362131 := bstep (se 1 (by rfl) ⟨95521598, by rfl⟩ : syracuseStep 127362131 = 191043197) B191043197
theorem B18884609 : Blo 1307972 18884609 := bstep (se 2 (by rfl) ⟨7081728, by rfl⟩ : syracuseStep 18884609 = 14163457) B14163457
theorem B2485055 : Blo 1307972 2485055 := bstep (se 1 (by rfl) ⟨1863791, by rfl⟩ : syracuseStep 2485055 = 3727583) B3727583
theorem B1862527 : Blo 1307972 1862527 := bstep (se 1 (by rfl) ⟨1396895, by rfl⟩ : syracuseStep 1862527 = 2793791) B2793791
theorem B229420937 : Blo 1307972 229420937 := bstep (se 2 (by rfl) ⟨86032851, by rfl⟩ : syracuseStep 229420937 = 172065703) B172065703
theorem B5967913 : Blo 1307972 5967913 := bstep (se 2 (by rfl) ⟨2237967, by rfl⟩ : syracuseStep 5967913 = 4475935) B4475935
theorem B2946185 : Blo 1307972 2946185 := bstep (se 2 (by rfl) ⟨1104819, by rfl⟩ : syracuseStep 2946185 = 2209639) B2209639
theorem B4782527 : Blo 1307972 4782527 := bstep (se 1 (by rfl) ⟨3586895, by rfl⟩ : syracuseStep 4782527 = 7173791) B7173791
theorem B1309167 : Blo 1307972 1309167 := bstep (se 1 (by rfl) ⟨981875, by rfl⟩ : syracuseStep 1309167 = 1963751) B1963751
theorem B1309935 : Blo 1307972 1309935 := bstep (se 1 (by rfl) ⟨982451, by rfl⟩ : syracuseStep 1309935 = 1964903) B1964903
theorem B6291719 : Blo 1307972 6291719 := bstep (se 1 (by rfl) ⟨4718789, by rfl⟩ : syracuseStep 6291719 = 9437579) B9437579
theorem B5456155 : Blo 1307972 5456155 := bstep (se 1 (by rfl) ⟨4092116, by rfl⟩ : syracuseStep 5456155 = 8184233) B8184233
theorem B2483369 : Blo 1307972 2483369 := bstep (se 2 (by rfl) ⟨931263, by rfl⟩ : syracuseStep 2483369 = 1862527) B1862527
theorem B3188351 : Blo 1307972 3188351 := bstep (se 1 (by rfl) ⟨2391263, by rfl⟩ : syracuseStep 3188351 = 4782527) B4782527
theorem B1656703 : Blo 1307972 1656703 := bstep (se 1 (by rfl) ⟨1242527, by rfl⟩ : syracuseStep 1656703 = 2485055) B2485055
theorem B152947291 : Blo 1307972 152947291 := bstep (se 1 (by rfl) ⟨114710468, by rfl⟩ : syracuseStep 152947291 = 229420937) B229420937
theorem B7957217 : Blo 1307972 7957217 := bstep (se 2 (by rfl) ⟨2983956, by rfl⟩ : syracuseStep 7957217 = 5967913) B5967913
theorem B4969943 : Blo 1307972 4969943 := bstep (se 1 (by rfl) ⟨3727457, by rfl⟩ : syracuseStep 4969943 = 7454915) B7454915
theorem B23877479 : Blo 1307972 23877479 := bstep (se 1 (by rfl) ⟨17908109, by rfl⟩ : syracuseStep 23877479 = 35816219) B35816219
theorem B84908087 : Blo 1307972 84908087 := bstep (se 1 (by rfl) ⟨63681065, by rfl⟩ : syracuseStep 84908087 = 127362131) B127362131
theorem B1964123 : Blo 1307972 1964123 := bstep (se 1 (by rfl) ⟨1473092, by rfl⟩ : syracuseStep 1964123 = 2946185) B2946185
theorem B12589739 : Blo 1307972 12589739 := bstep (se 1 (by rfl) ⟨9442304, by rfl⟩ : syracuseStep 12589739 = 18884609) B18884609
theorem B4194479 : Blo 1307972 4194479 := bstep (se 1 (by rfl) ⟨3145859, by rfl⟩ : syracuseStep 4194479 = 6291719) B6291719
theorem B7274873 : Blo 1307972 7274873 := bstep (se 2 (by rfl) ⟨2728077, by rfl⟩ : syracuseStep 7274873 = 5456155) B5456155
theorem B1655579 : Blo 1307972 1655579 := bstep (se 1 (by rfl) ⟨1241684, by rfl⟩ : syracuseStep 1655579 = 2483369) B2483369
theorem B15918319 : Blo 1307972 15918319 := bstep (se 1 (by rfl) ⟨11938739, by rfl⟩ : syracuseStep 15918319 = 23877479) B23877479
theorem B3313295 : Blo 1307972 3313295 := bstep (se 1 (by rfl) ⟨2484971, by rfl⟩ : syracuseStep 3313295 = 4969943) B4969943
theorem B2125567 : Blo 1307972 2125567 := bstep (se 1 (by rfl) ⟨1594175, by rfl⟩ : syracuseStep 2125567 = 3188351) B3188351
theorem B8393159 : Blo 1307972 8393159 := bstep (se 1 (by rfl) ⟨6294869, by rfl⟩ : syracuseStep 8393159 = 12589739) B12589739
theorem B5304811 : Blo 1307972 5304811 := bstep (se 1 (by rfl) ⟨3978608, by rfl⟩ : syracuseStep 5304811 = 7957217) B7957217
theorem B2208937 : Blo 1307972 2208937 := bstep (se 2 (by rfl) ⟨828351, by rfl⟩ : syracuseStep 2208937 = 1656703) B1656703
theorem B203929721 : Blo 1307972 203929721 := bstep (se 2 (by rfl) ⟨76473645, by rfl⟩ : syracuseStep 203929721 = 152947291) B152947291
theorem B56605391 : Blo 1307972 56605391 := bstep (se 1 (by rfl) ⟨42454043, by rfl⟩ : syracuseStep 56605391 = 84908087) B84908087
theorem B1309415 : Blo 1307972 1309415 := bstep (se 1 (by rfl) ⟨982061, by rfl⟩ : syracuseStep 1309415 = 1964123) B1964123
theorem B19399661 : Blo 1307972 19399661 := bstep (se 3 (by rfl) ⟨3637436, by rfl⟩ : syracuseStep 19399661 = 7274873) B7274873
theorem B22381757 : Blo 1307972 22381757 := bstep (se 3 (by rfl) ⟨4196579, by rfl⟩ : syracuseStep 22381757 = 8393159) B8393159
theorem B2796319 : Blo 1307972 2796319 := bstep (se 1 (by rfl) ⟨2097239, by rfl⟩ : syracuseStep 2796319 = 4194479) B4194479
theorem B7073081 : Blo 1307972 7073081 := bstep (se 2 (by rfl) ⟨2652405, by rfl⟩ : syracuseStep 7073081 = 5304811) B5304811
theorem B2945249 : Blo 1307972 2945249 := bstep (se 2 (by rfl) ⟨1104468, by rfl⟩ : syracuseStep 2945249 = 2208937) B2208937
theorem B37736927 : Blo 1307972 37736927 := bstep (se 1 (by rfl) ⟨28302695, by rfl⟩ : syracuseStep 37736927 = 56605391) B56605391
theorem B2208863 : Blo 1307972 2208863 := bstep (se 1 (by rfl) ⟨1656647, by rfl⟩ : syracuseStep 2208863 = 3313295) B3313295
theorem B11336357 : Blo 1307972 11336357 := bstep (se 4 (by rfl) ⟨1062783, by rfl⟩ : syracuseStep 11336357 = 2125567) B2125567
theorem B135953147 : Blo 1307972 135953147 := bstep (se 1 (by rfl) ⟨101964860, by rfl⟩ : syracuseStep 135953147 = 203929721) B203929721
theorem B21224425 : Blo 1307972 21224425 := bstep (se 2 (by rfl) ⟨7959159, by rfl⟩ : syracuseStep 21224425 = 15918319) B15918319
theorem B4414877 : Blo 1307972 4414877 := bstep (se 3 (by rfl) ⟨827789, by rfl⟩ : syracuseStep 4414877 = 1655579) B1655579
theorem B25157951 : Blo 1307972 25157951 := bstep (se 1 (by rfl) ⟨18868463, by rfl⟩ : syracuseStep 25157951 = 37736927) B37736927
theorem B3728425 : Blo 1307972 3728425 := bstep (se 2 (by rfl) ⟨1398159, by rfl⟩ : syracuseStep 3728425 = 2796319) B2796319
theorem B2943251 : Blo 1307972 2943251 := bstep (se 1 (by rfl) ⟨2207438, by rfl⟩ : syracuseStep 2943251 = 4414877) B4414877
theorem B14921171 : Blo 1307972 14921171 := bstep (se 1 (by rfl) ⟨11190878, by rfl⟩ : syracuseStep 14921171 = 22381757) B22381757
theorem B28299233 : Blo 1307972 28299233 := bstep (se 2 (by rfl) ⟨10612212, by rfl⟩ : syracuseStep 28299233 = 21224425) B21224425
theorem B7557571 : Blo 1307972 7557571 := bstep (se 1 (by rfl) ⟨5668178, by rfl⟩ : syracuseStep 7557571 = 11336357) B11336357
theorem B4715387 : Blo 1307972 4715387 := bstep (se 1 (by rfl) ⟨3536540, by rfl⟩ : syracuseStep 4715387 = 7073081) B7073081
theorem B1963499 : Blo 1307972 1963499 := bstep (se 1 (by rfl) ⟨1472624, by rfl⟩ : syracuseStep 1963499 = 2945249) B2945249
theorem B12933107 : Blo 1307972 12933107 := bstep (se 1 (by rfl) ⟨9699830, by rfl⟩ : syracuseStep 12933107 = 19399661) B19399661
theorem B1472575 : Blo 1307972 1472575 := bstep (se 1 (by rfl) ⟨1104431, by rfl⟩ : syracuseStep 1472575 = 2208863) B2208863
theorem B90635431 : Blo 1307972 90635431 := bstep (se 1 (by rfl) ⟨67976573, by rfl⟩ : syracuseStep 90635431 = 135953147) B135953147
theorem B10076761 : Blo 1307972 10076761 := bstep (se 2 (by rfl) ⟨3778785, by rfl⟩ : syracuseStep 10076761 = 7557571) B7557571
theorem B9947447 : Blo 1307972 9947447 := bstep (se 1 (by rfl) ⟨7460585, by rfl⟩ : syracuseStep 9947447 = 14921171) B14921171
theorem B16771967 : Blo 1307972 16771967 := bstep (se 1 (by rfl) ⟨12578975, by rfl⟩ : syracuseStep 16771967 = 25157951) B25157951
theorem B8622071 : Blo 1307972 8622071 := bstep (se 1 (by rfl) ⟨6466553, by rfl⟩ : syracuseStep 8622071 = 12933107) B12933107
theorem B1962167 : Blo 1307972 1962167 := bstep (se 1 (by rfl) ⟨1471625, by rfl⟩ : syracuseStep 1962167 = 2943251) B2943251
theorem B1963433 : Blo 1307972 1963433 := bstep (se 2 (by rfl) ⟨736287, by rfl⟩ : syracuseStep 1963433 = 1472575) B1472575
theorem B3143591 : Blo 1307972 3143591 := bstep (se 1 (by rfl) ⟨2357693, by rfl⟩ : syracuseStep 3143591 = 4715387) B4715387
theorem B1308999 : Blo 1307972 1308999 := bstep (se 1 (by rfl) ⟨981749, by rfl⟩ : syracuseStep 1308999 = 1963499) B1963499
theorem B4971233 : Blo 1307972 4971233 := bstep (se 2 (by rfl) ⟨1864212, by rfl⟩ : syracuseStep 4971233 = 3728425) B3728425
theorem B120847241 : Blo 1307972 120847241 := bstep (se 2 (by rfl) ⟨45317715, by rfl⟩ : syracuseStep 120847241 = 90635431) B90635431
theorem B75464621 : Blo 1307972 75464621 := bstep (se 3 (by rfl) ⟨14149616, by rfl⟩ : syracuseStep 75464621 = 28299233) B28299233
theorem B13435681 : Blo 1307972 13435681 := bstep (se 2 (by rfl) ⟨5038380, by rfl⟩ : syracuseStep 13435681 = 10076761) B10076761
theorem B50309747 : Blo 1307972 50309747 := bstep (se 1 (by rfl) ⟨37732310, by rfl⟩ : syracuseStep 50309747 = 75464621) B75464621
theorem B6631631 : Blo 1307972 6631631 := bstep (se 1 (by rfl) ⟨4973723, by rfl⟩ : syracuseStep 6631631 = 9947447) B9947447
theorem B3314155 : Blo 1307972 3314155 := bstep (se 1 (by rfl) ⟨2485616, by rfl⟩ : syracuseStep 3314155 = 4971233) B4971233
theorem B80564827 : Blo 1307972 80564827 := bstep (se 1 (by rfl) ⟨60423620, by rfl⟩ : syracuseStep 80564827 = 120847241) B120847241
theorem B5748047 : Blo 1307972 5748047 := bstep (se 1 (by rfl) ⟨4311035, by rfl⟩ : syracuseStep 5748047 = 8622071) B8622071
theorem B1308111 : Blo 1307972 1308111 := bstep (se 1 (by rfl) ⟨981083, by rfl⟩ : syracuseStep 1308111 = 1962167) B1962167
theorem B1308955 : Blo 1307972 1308955 := bstep (se 1 (by rfl) ⟨981716, by rfl⟩ : syracuseStep 1308955 = 1963433) B1963433
theorem B2095727 : Blo 1307972 2095727 := bstep (se 1 (by rfl) ⟨1571795, by rfl⟩ : syracuseStep 2095727 = 3143591) B3143591
theorem B11181311 : Blo 1307972 11181311 := bstep (se 1 (by rfl) ⟨8385983, by rfl⟩ : syracuseStep 11181311 = 16771967) B16771967
theorem B5588605 : Blo 1307972 5588605 := bstep (se 3 (by rfl) ⟨1047863, by rfl⟩ : syracuseStep 5588605 = 2095727) B2095727
theorem B33539831 : Blo 1307972 33539831 := bstep (se 1 (by rfl) ⟨25154873, by rfl⟩ : syracuseStep 33539831 = 50309747) B50309747
theorem B4418873 : Blo 1307972 4418873 := bstep (se 2 (by rfl) ⟨1657077, by rfl⟩ : syracuseStep 4418873 = 3314155) B3314155
theorem B4421087 : Blo 1307972 4421087 := bstep (se 1 (by rfl) ⟨3315815, by rfl⟩ : syracuseStep 4421087 = 6631631) B6631631
theorem B107419769 : Blo 1307972 107419769 := bstep (se 2 (by rfl) ⟨40282413, by rfl⟩ : syracuseStep 107419769 = 80564827) B80564827
theorem B3832031 : Blo 1307972 3832031 := bstep (se 1 (by rfl) ⟨2874023, by rfl⟩ : syracuseStep 3832031 = 5748047) B5748047
theorem B17914241 : Blo 1307972 17914241 := bstep (se 2 (by rfl) ⟨6717840, by rfl⟩ : syracuseStep 17914241 = 13435681) B13435681
theorem B7454207 : Blo 1307972 7454207 := bstep (se 1 (by rfl) ⟨5590655, by rfl⟩ : syracuseStep 7454207 = 11181311) B11181311
theorem B47771309 : Blo 1307972 47771309 := bstep (se 3 (by rfl) ⟨8957120, by rfl⟩ : syracuseStep 47771309 = 17914241) B17914241
theorem B22359887 : Blo 1307972 22359887 := bstep (se 1 (by rfl) ⟨16769915, by rfl⟩ : syracuseStep 22359887 = 33539831) B33539831
theorem B7451473 : Blo 1307972 7451473 := bstep (se 2 (by rfl) ⟨2794302, by rfl⟩ : syracuseStep 7451473 = 5588605) B5588605
theorem B2945915 : Blo 1307972 2945915 := bstep (se 1 (by rfl) ⟨2209436, by rfl⟩ : syracuseStep 2945915 = 4418873) B4418873
theorem B4969471 : Blo 1307972 4969471 := bstep (se 1 (by rfl) ⟨3727103, by rfl⟩ : syracuseStep 4969471 = 7454207) B7454207
theorem B2947391 : Blo 1307972 2947391 := bstep (se 1 (by rfl) ⟨2210543, by rfl⟩ : syracuseStep 2947391 = 4421087) B4421087
theorem B71613179 : Blo 1307972 71613179 := bstep (se 1 (by rfl) ⟨53709884, by rfl⟩ : syracuseStep 71613179 = 107419769) B107419769
theorem B2554687 : Blo 1307972 2554687 := bstep (se 1 (by rfl) ⟨1916015, by rfl⟩ : syracuseStep 2554687 = 3832031) B3832031
theorem B31847539 : Blo 1307972 31847539 := bstep (se 1 (by rfl) ⟨23885654, by rfl⟩ : syracuseStep 31847539 = 47771309) B47771309
theorem B14906591 : Blo 1307972 14906591 := bstep (se 1 (by rfl) ⟨11179943, by rfl⟩ : syracuseStep 14906591 = 22359887) B22359887
theorem B1963943 : Blo 1307972 1963943 := bstep (se 1 (by rfl) ⟨1472957, by rfl⟩ : syracuseStep 1963943 = 2945915) B2945915
theorem B3406249 : Blo 1307972 3406249 := bstep (se 2 (by rfl) ⟨1277343, by rfl⟩ : syracuseStep 3406249 = 2554687) B2554687
theorem B9935297 : Blo 1307972 9935297 := bstep (se 2 (by rfl) ⟨3725736, by rfl⟩ : syracuseStep 9935297 = 7451473) B7451473
theorem B6625961 : Blo 1307972 6625961 := bstep (se 2 (by rfl) ⟨2484735, by rfl⟩ : syracuseStep 6625961 = 4969471) B4969471
theorem B1964927 : Blo 1307972 1964927 := bstep (se 1 (by rfl) ⟨1473695, by rfl⟩ : syracuseStep 1964927 = 2947391) B2947391
theorem B47742119 : Blo 1307972 47742119 := bstep (se 1 (by rfl) ⟨35806589, by rfl⟩ : syracuseStep 47742119 = 71613179) B71613179
theorem B9937727 : Blo 1307972 9937727 := bstep (se 1 (by rfl) ⟨7453295, by rfl⟩ : syracuseStep 9937727 = 14906591) B14906591
theorem B4417307 : Blo 1307972 4417307 := bstep (se 1 (by rfl) ⟨3312980, by rfl⟩ : syracuseStep 4417307 = 6625961) B6625961
theorem B31828079 : Blo 1307972 31828079 := bstep (se 1 (by rfl) ⟨23871059, by rfl⟩ : syracuseStep 31828079 = 47742119) B47742119
theorem B4541665 : Blo 1307972 4541665 := bstep (se 2 (by rfl) ⟨1703124, by rfl⟩ : syracuseStep 4541665 = 3406249) B3406249
theorem B42463385 : Blo 1307972 42463385 := bstep (se 2 (by rfl) ⟨15923769, by rfl⟩ : syracuseStep 42463385 = 31847539) B31847539
theorem B6623531 : Blo 1307972 6623531 := bstep (se 1 (by rfl) ⟨4967648, by rfl⟩ : syracuseStep 6623531 = 9935297) B9935297
theorem B1309295 : Blo 1307972 1309295 := bstep (se 1 (by rfl) ⟨981971, by rfl⟩ : syracuseStep 1309295 = 1963943) B1963943
theorem B1309951 : Blo 1307972 1309951 := bstep (se 1 (by rfl) ⟨982463, by rfl⟩ : syracuseStep 1309951 = 1964927) B1964927
theorem B4415687 : Blo 1307972 4415687 := bstep (se 1 (by rfl) ⟨3311765, by rfl⟩ : syracuseStep 4415687 = 6623531) B6623531
theorem B21218719 : Blo 1307972 21218719 := bstep (se 1 (by rfl) ⟨15914039, by rfl⟩ : syracuseStep 21218719 = 31828079) B31828079
theorem B6055553 : Blo 1307972 6055553 := bstep (se 2 (by rfl) ⟨2270832, by rfl⟩ : syracuseStep 6055553 = 4541665) B4541665
theorem B2944871 : Blo 1307972 2944871 := bstep (se 1 (by rfl) ⟨2208653, by rfl⟩ : syracuseStep 2944871 = 4417307) B4417307
theorem B28308923 : Blo 1307972 28308923 := bstep (se 1 (by rfl) ⟨21231692, by rfl⟩ : syracuseStep 28308923 = 42463385) B42463385
theorem B6625151 : Blo 1307972 6625151 := bstep (se 1 (by rfl) ⟨4968863, by rfl⟩ : syracuseStep 6625151 = 9937727) B9937727
theorem B4416767 : Blo 1307972 4416767 := bstep (se 1 (by rfl) ⟨3312575, by rfl⟩ : syracuseStep 4416767 = 6625151) B6625151
theorem B2943791 : Blo 1307972 2943791 := bstep (se 1 (by rfl) ⟨2207843, by rfl⟩ : syracuseStep 2943791 = 4415687) B4415687
theorem B28291625 : Blo 1307972 28291625 := bstep (se 2 (by rfl) ⟨10609359, by rfl⟩ : syracuseStep 28291625 = 21218719) B21218719
theorem B1963247 : Blo 1307972 1963247 := bstep (se 1 (by rfl) ⟨1472435, by rfl⟩ : syracuseStep 1963247 = 2944871) B2944871
theorem B18872615 : Blo 1307972 18872615 := bstep (se 1 (by rfl) ⟨14154461, by rfl⟩ : syracuseStep 18872615 = 28308923) B28308923
theorem B4037035 : Blo 1307972 4037035 := bstep (se 1 (by rfl) ⟨3027776, by rfl⟩ : syracuseStep 4037035 = 6055553) B6055553
theorem B5382713 : Blo 1307972 5382713 := bstep (se 2 (by rfl) ⟨2018517, by rfl⟩ : syracuseStep 5382713 = 4037035) B4037035
theorem B18861083 : Blo 1307972 18861083 := bstep (se 1 (by rfl) ⟨14145812, by rfl⟩ : syracuseStep 18861083 = 28291625) B28291625
theorem B2944511 : Blo 1307972 2944511 := bstep (se 1 (by rfl) ⟨2208383, by rfl⟩ : syracuseStep 2944511 = 4416767) B4416767
theorem B1962527 : Blo 1307972 1962527 := bstep (se 1 (by rfl) ⟨1471895, by rfl⟩ : syracuseStep 1962527 = 2943791) B2943791
theorem B1308831 : Blo 1307972 1308831 := bstep (se 1 (by rfl) ⟨981623, by rfl⟩ : syracuseStep 1308831 = 1963247) B1963247
theorem B12581743 : Blo 1307972 12581743 := bstep (se 1 (by rfl) ⟨9436307, by rfl⟩ : syracuseStep 12581743 = 18872615) B18872615
theorem B3588475 : Blo 1307972 3588475 := bstep (se 1 (by rfl) ⟨2691356, by rfl⟩ : syracuseStep 3588475 = 5382713) B5382713
theorem B1963007 : Blo 1307972 1963007 := bstep (se 1 (by rfl) ⟨1472255, by rfl⟩ : syracuseStep 1963007 = 2944511) B2944511
theorem B1308351 : Blo 1307972 1308351 := bstep (se 1 (by rfl) ⟨981263, by rfl⟩ : syracuseStep 1308351 = 1962527) B1962527
theorem B16775657 : Blo 1307972 16775657 := bstep (se 2 (by rfl) ⟨6290871, by rfl⟩ : syracuseStep 16775657 = 12581743) B12581743
theorem B12574055 : Blo 1307972 12574055 := bstep (se 1 (by rfl) ⟨9430541, by rfl⟩ : syracuseStep 12574055 = 18861083) B18861083
theorem B4784633 : Blo 1307972 4784633 := bstep (se 2 (by rfl) ⟨1794237, by rfl⟩ : syracuseStep 4784633 = 3588475) B3588475
theorem B11183771 : Blo 1307972 11183771 := bstep (se 1 (by rfl) ⟨8387828, by rfl⟩ : syracuseStep 11183771 = 16775657) B16775657
theorem B8382703 : Blo 1307972 8382703 := bstep (se 1 (by rfl) ⟨6287027, by rfl⟩ : syracuseStep 8382703 = 12574055) B12574055
theorem B1308671 : Blo 1307972 1308671 := bstep (se 1 (by rfl) ⟨981503, by rfl⟩ : syracuseStep 1308671 = 1963007) B1963007
theorem B7455847 : Blo 1307972 7455847 := bstep (se 1 (by rfl) ⟨5591885, by rfl⟩ : syracuseStep 7455847 = 11183771) B11183771
theorem B11176937 : Blo 1307972 11176937 := bstep (se 2 (by rfl) ⟨4191351, by rfl⟩ : syracuseStep 11176937 = 8382703) B8382703
theorem B3189755 : Blo 1307972 3189755 := bstep (se 1 (by rfl) ⟨2392316, by rfl⟩ : syracuseStep 3189755 = 4784633) B4784633
theorem B9941129 : Blo 1307972 9941129 := bstep (se 2 (by rfl) ⟨3727923, by rfl⟩ : syracuseStep 9941129 = 7455847) B7455847
theorem B7451291 : Blo 1307972 7451291 := bstep (se 1 (by rfl) ⟨5588468, by rfl⟩ : syracuseStep 7451291 = 11176937) B11176937
theorem B2126503 : Blo 1307972 2126503 := bstep (se 1 (by rfl) ⟨1594877, by rfl⟩ : syracuseStep 2126503 = 3189755) B3189755
theorem B6627419 : Blo 1307972 6627419 := bstep (se 1 (by rfl) ⟨4970564, by rfl⟩ : syracuseStep 6627419 = 9941129) B9941129
theorem B2835337 : Blo 1307972 2835337 := bstep (se 2 (by rfl) ⟨1063251, by rfl⟩ : syracuseStep 2835337 = 2126503) B2126503
theorem B4967527 : Blo 1307972 4967527 := bstep (se 1 (by rfl) ⟨3725645, by rfl⟩ : syracuseStep 4967527 = 7451291) B7451291
theorem B4418279 : Blo 1307972 4418279 := bstep (se 1 (by rfl) ⟨3313709, by rfl⟩ : syracuseStep 4418279 = 6627419) B6627419
theorem B3780449 : Blo 1307972 3780449 := bstep (se 2 (by rfl) ⟨1417668, by rfl⟩ : syracuseStep 3780449 = 2835337) B2835337
theorem B6623369 : Blo 1307972 6623369 := bstep (se 2 (by rfl) ⟨2483763, by rfl⟩ : syracuseStep 6623369 = 4967527) B4967527
theorem B4415579 : Blo 1307972 4415579 := bstep (se 1 (by rfl) ⟨3311684, by rfl⟩ : syracuseStep 4415579 = 6623369) B6623369
theorem B2945519 : Blo 1307972 2945519 := bstep (se 1 (by rfl) ⟨2209139, by rfl⟩ : syracuseStep 2945519 = 4418279) B4418279
theorem B2520299 : Blo 1307972 2520299 := bstep (se 1 (by rfl) ⟨1890224, by rfl⟩ : syracuseStep 2520299 = 3780449) B3780449
theorem B1680199 : Blo 1307972 1680199 := bstep (se 1 (by rfl) ⟨1260149, by rfl⟩ : syracuseStep 1680199 = 2520299) B2520299
theorem B2943719 : Blo 1307972 2943719 := bstep (se 1 (by rfl) ⟨2207789, by rfl⟩ : syracuseStep 2943719 = 4415579) B4415579
theorem B1963679 : Blo 1307972 1963679 := bstep (se 1 (by rfl) ⟨1472759, by rfl⟩ : syracuseStep 1963679 = 2945519) B2945519
theorem B1962479 : Blo 1307972 1962479 := bstep (se 1 (by rfl) ⟨1471859, by rfl⟩ : syracuseStep 1962479 = 2943719) B2943719
theorem B1309119 : Blo 1307972 1309119 := bstep (se 1 (by rfl) ⟨981839, by rfl⟩ : syracuseStep 1309119 = 1963679) B1963679
theorem B8961061 : Blo 1307972 8961061 := bstep (se 4 (by rfl) ⟨840099, by rfl⟩ : syracuseStep 8961061 = 1680199) B1680199
theorem B11948081 : Blo 1307972 11948081 := bstep (se 2 (by rfl) ⟨4480530, by rfl⟩ : syracuseStep 11948081 = 8961061) B8961061
theorem B1308319 : Blo 1307972 1308319 := bstep (se 1 (by rfl) ⟨981239, by rfl⟩ : syracuseStep 1308319 = 1962479) B1962479
theorem B31861549 : Blo 1307972 31861549 := bstep (se 3 (by rfl) ⟨5974040, by rfl⟩ : syracuseStep 31861549 = 11948081) B11948081
theorem B42482065 : Blo 1307972 42482065 := bstep (se 2 (by rfl) ⟨15930774, by rfl⟩ : syracuseStep 42482065 = 31861549) B31861549
theorem B56642753 : Blo 1307972 56642753 := bstep (se 2 (by rfl) ⟨21241032, by rfl⟩ : syracuseStep 56642753 = 42482065) B42482065
theorem B37761835 : Blo 1307972 37761835 := bstep (se 1 (by rfl) ⟨28321376, by rfl⟩ : syracuseStep 37761835 = 56642753) B56642753
theorem B50349113 : Blo 1307972 50349113 := bstep (se 2 (by rfl) ⟨18880917, by rfl⟩ : syracuseStep 50349113 = 37761835) B37761835
theorem B33566075 : Blo 1307972 33566075 := bstep (se 1 (by rfl) ⟨25174556, by rfl⟩ : syracuseStep 33566075 = 50349113) B50349113
theorem B22377383 : Blo 1307972 22377383 := bstep (se 1 (by rfl) ⟨16783037, by rfl⟩ : syracuseStep 22377383 = 33566075) B33566075
theorem B14918255 : Blo 1307972 14918255 := bstep (se 1 (by rfl) ⟨11188691, by rfl⟩ : syracuseStep 14918255 = 22377383) B22377383
theorem B9945503 : Blo 1307972 9945503 := bstep (se 1 (by rfl) ⟨7459127, by rfl⟩ : syracuseStep 9945503 = 14918255) B14918255
theorem B6630335 : Blo 1307972 6630335 := bstep (se 1 (by rfl) ⟨4972751, by rfl⟩ : syracuseStep 6630335 = 9945503) B9945503
theorem B4420223 : Blo 1307972 4420223 := bstep (se 1 (by rfl) ⟨3315167, by rfl⟩ : syracuseStep 4420223 = 6630335) B6630335
theorem B2946815 : Blo 1307972 2946815 := bstep (se 1 (by rfl) ⟨2210111, by rfl⟩ : syracuseStep 2946815 = 4420223) B4420223
theorem B1964543 : Blo 1307972 1964543 := bstep (se 1 (by rfl) ⟨1473407, by rfl⟩ : syracuseStep 1964543 = 2946815) B2946815
theorem B1309695 : Blo 1307972 1309695 := bstep (se 1 (by rfl) ⟨982271, by rfl⟩ : syracuseStep 1309695 = 1964543) B1964543

theorem C0 (j : ℕ) (h1 : 326993 ≤ j) (h2 : j ≤ 327492) : Blo 1307972 (4 * j + 3) := by
  interval_cases j
  · exact B1307975
  · exact B1307979
  · exact B1307983
  · exact B1307987
  · exact B1307991
  · exact B1307995
  · exact B1307999
  · exact B1308003
  · exact B1308007
  · exact B1308011
  · exact B1308015
  · exact B1308019
  · exact B1308023
  · exact B1308027
  · exact B1308031
  · exact B1308035
  · exact B1308039
  · exact B1308043
  · exact B1308047
  · exact B1308051
  · exact B1308055
  · exact B1308059
  · exact B1308063
  · exact B1308067
  · exact B1308071
  · exact B1308075
  · exact B1308079
  · exact B1308083
  · exact B1308087
  · exact B1308091
  · exact B1308095
  · exact B1308099
  · exact B1308103
  · exact B1308107
  · exact B1308111
  · exact B1308115
  · exact B1308119
  · exact B1308123
  · exact B1308127
  · exact B1308131
  · exact B1308135
  · exact B1308139
  · exact B1308143
  · exact B1308147
  · exact B1308151
  · exact B1308155
  · exact B1308159
  · exact B1308163
  · exact B1308167
  · exact B1308171
  · exact B1308175
  · exact B1308179
  · exact B1308183
  · exact B1308187
  · exact B1308191
  · exact B1308195
  · exact B1308199
  · exact B1308203
  · exact B1308207
  · exact B1308211
  · exact B1308215
  · exact B1308219
  · exact B1308223
  · exact B1308227
  · exact B1308231
  · exact B1308235
  · exact B1308239
  · exact B1308243
  · exact B1308247
  · exact B1308251
  · exact B1308255
  · exact B1308259
  · exact B1308263
  · exact B1308267
  · exact B1308271
  · exact B1308275
  · exact B1308279
  · exact B1308283
  · exact B1308287
  · exact B1308291
  · exact B1308295
  · exact B1308299
  · exact B1308303
  · exact B1308307
  · exact B1308311
  · exact B1308315
  · exact B1308319
  · exact B1308323
  · exact B1308327
  · exact B1308331
  · exact B1308335
  · exact B1308339
  · exact B1308343
  · exact B1308347
  · exact B1308351
  · exact B1308355
  · exact B1308359
  · exact B1308363
  · exact B1308367
  · exact B1308371
  · exact B1308375
  · exact B1308379
  · exact B1308383
  · exact B1308387
  · exact B1308391
  · exact B1308395
  · exact B1308399
  · exact B1308403
  · exact B1308407
  · exact B1308411
  · exact B1308415
  · exact B1308419
  · exact B1308423
  · exact B1308427
  · exact B1308431
  · exact B1308435
  · exact B1308439
  · exact B1308443
  · exact B1308447
  · exact B1308451
  · exact B1308455
  · exact B1308459
  · exact B1308463
  · exact B1308467
  · exact B1308471
  · exact B1308475
  · exact B1308479
  · exact B1308483
  · exact B1308487
  · exact B1308491
  · exact B1308495
  · exact B1308499
  · exact B1308503
  · exact B1308507
  · exact B1308511
  · exact B1308515
  · exact B1308519
  · exact B1308523
  · exact B1308527
  · exact B1308531
  · exact B1308535
  · exact B1308539
  · exact B1308543
  · exact B1308547
  · exact B1308551
  · exact B1308555
  · exact B1308559
  · exact B1308563
  · exact B1308567
  · exact B1308571
  · exact B1308575
  · exact B1308579
  · exact B1308583
  · exact B1308587
  · exact B1308591
  · exact B1308595
  · exact B1308599
  · exact B1308603
  · exact B1308607
  · exact B1308611
  · exact B1308615
  · exact B1308619
  · exact B1308623
  · exact B1308627
  · exact B1308631
  · exact B1308635
  · exact B1308639
  · exact B1308643
  · exact B1308647
  · exact B1308651
  · exact B1308655
  · exact B1308659
  · exact B1308663
  · exact B1308667
  · exact B1308671
  · exact B1308675
  · exact B1308679
  · exact B1308683
  · exact B1308687
  · exact B1308691
  · exact B1308695
  · exact B1308699
  · exact B1308703
  · exact B1308707
  · exact B1308711
  · exact B1308715
  · exact B1308719
  · exact B1308723
  · exact B1308727
  · exact B1308731
  · exact B1308735
  · exact B1308739
  · exact B1308743
  · exact B1308747
  · exact B1308751
  · exact B1308755
  · exact B1308759
  · exact B1308763
  · exact B1308767
  · exact B1308771
  · exact B1308775
  · exact B1308779
  · exact B1308783
  · exact B1308787
  · exact B1308791
  · exact B1308795
  · exact B1308799
  · exact B1308803
  · exact B1308807
  · exact B1308811
  · exact B1308815
  · exact B1308819
  · exact B1308823
  · exact B1308827
  · exact B1308831
  · exact B1308835
  · exact B1308839
  · exact B1308843
  · exact B1308847
  · exact B1308851
  · exact B1308855
  · exact B1308859
  · exact B1308863
  · exact B1308867
  · exact B1308871
  · exact B1308875
  · exact B1308879
  · exact B1308883
  · exact B1308887
  · exact B1308891
  · exact B1308895
  · exact B1308899
  · exact B1308903
  · exact B1308907
  · exact B1308911
  · exact B1308915
  · exact B1308919
  · exact B1308923
  · exact B1308927
  · exact B1308931
  · exact B1308935
  · exact B1308939
  · exact B1308943
  · exact B1308947
  · exact B1308951
  · exact B1308955
  · exact B1308959
  · exact B1308963
  · exact B1308967
  · exact B1308971
  · exact B1308975
  · exact B1308979
  · exact B1308983
  · exact B1308987
  · exact B1308991
  · exact B1308995
  · exact B1308999
  · exact B1309003
  · exact B1309007
  · exact B1309011
  · exact B1309015
  · exact B1309019
  · exact B1309023
  · exact B1309027
  · exact B1309031
  · exact B1309035
  · exact B1309039
  · exact B1309043
  · exact B1309047
  · exact B1309051
  · exact B1309055
  · exact B1309059
  · exact B1309063
  · exact B1309067
  · exact B1309071
  · exact B1309075
  · exact B1309079
  · exact B1309083
  · exact B1309087
  · exact B1309091
  · exact B1309095
  · exact B1309099
  · exact B1309103
  · exact B1309107
  · exact B1309111
  · exact B1309115
  · exact B1309119
  · exact B1309123
  · exact B1309127
  · exact B1309131
  · exact B1309135
  · exact B1309139
  · exact B1309143
  · exact B1309147
  · exact B1309151
  · exact B1309155
  · exact B1309159
  · exact B1309163
  · exact B1309167
  · exact B1309171
  · exact B1309175
  · exact B1309179
  · exact B1309183
  · exact B1309187
  · exact B1309191
  · exact B1309195
  · exact B1309199
  · exact B1309203
  · exact B1309207
  · exact B1309211
  · exact B1309215
  · exact B1309219
  · exact B1309223
  · exact B1309227
  · exact B1309231
  · exact B1309235
  · exact B1309239
  · exact B1309243
  · exact B1309247
  · exact B1309251
  · exact B1309255
  · exact B1309259
  · exact B1309263
  · exact B1309267
  · exact B1309271
  · exact B1309275
  · exact B1309279
  · exact B1309283
  · exact B1309287
  · exact B1309291
  · exact B1309295
  · exact B1309299
  · exact B1309303
  · exact B1309307
  · exact B1309311
  · exact B1309315
  · exact B1309319
  · exact B1309323
  · exact B1309327
  · exact B1309331
  · exact B1309335
  · exact B1309339
  · exact B1309343
  · exact B1309347
  · exact B1309351
  · exact B1309355
  · exact B1309359
  · exact B1309363
  · exact B1309367
  · exact B1309371
  · exact B1309375
  · exact B1309379
  · exact B1309383
  · exact B1309387
  · exact B1309391
  · exact B1309395
  · exact B1309399
  · exact B1309403
  · exact B1309407
  · exact B1309411
  · exact B1309415
  · exact B1309419
  · exact B1309423
  · exact B1309427
  · exact B1309431
  · exact B1309435
  · exact B1309439
  · exact B1309443
  · exact B1309447
  · exact B1309451
  · exact B1309455
  · exact B1309459
  · exact B1309463
  · exact B1309467
  · exact B1309471
  · exact B1309475
  · exact B1309479
  · exact B1309483
  · exact B1309487
  · exact B1309491
  · exact B1309495
  · exact B1309499
  · exact B1309503
  · exact B1309507
  · exact B1309511
  · exact B1309515
  · exact B1309519
  · exact B1309523
  · exact B1309527
  · exact B1309531
  · exact B1309535
  · exact B1309539
  · exact B1309543
  · exact B1309547
  · exact B1309551
  · exact B1309555
  · exact B1309559
  · exact B1309563
  · exact B1309567
  · exact B1309571
  · exact B1309575
  · exact B1309579
  · exact B1309583
  · exact B1309587
  · exact B1309591
  · exact B1309595
  · exact B1309599
  · exact B1309603
  · exact B1309607
  · exact B1309611
  · exact B1309615
  · exact B1309619
  · exact B1309623
  · exact B1309627
  · exact B1309631
  · exact B1309635
  · exact B1309639
  · exact B1309643
  · exact B1309647
  · exact B1309651
  · exact B1309655
  · exact B1309659
  · exact B1309663
  · exact B1309667
  · exact B1309671
  · exact B1309675
  · exact B1309679
  · exact B1309683
  · exact B1309687
  · exact B1309691
  · exact B1309695
  · exact B1309699
  · exact B1309703
  · exact B1309707
  · exact B1309711
  · exact B1309715
  · exact B1309719
  · exact B1309723
  · exact B1309727
  · exact B1309731
  · exact B1309735
  · exact B1309739
  · exact B1309743
  · exact B1309747
  · exact B1309751
  · exact B1309755
  · exact B1309759
  · exact B1309763
  · exact B1309767
  · exact B1309771
  · exact B1309775
  · exact B1309779
  · exact B1309783
  · exact B1309787
  · exact B1309791
  · exact B1309795
  · exact B1309799
  · exact B1309803
  · exact B1309807
  · exact B1309811
  · exact B1309815
  · exact B1309819
  · exact B1309823
  · exact B1309827
  · exact B1309831
  · exact B1309835
  · exact B1309839
  · exact B1309843
  · exact B1309847
  · exact B1309851
  · exact B1309855
  · exact B1309859
  · exact B1309863
  · exact B1309867
  · exact B1309871
  · exact B1309875
  · exact B1309879
  · exact B1309883
  · exact B1309887
  · exact B1309891
  · exact B1309895
  · exact B1309899
  · exact B1309903
  · exact B1309907
  · exact B1309911
  · exact B1309915
  · exact B1309919
  · exact B1309923
  · exact B1309927
  · exact B1309931
  · exact B1309935
  · exact B1309939
  · exact B1309943
  · exact B1309947
  · exact B1309951
  · exact B1309955
  · exact B1309959
  · exact B1309963
  · exact B1309967
  · exact B1309971

theorem solution (m : ℕ) (hlo : 1307972 ≤ m) (hhi : m ≤ 1309972) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 326993 ≤ j := by omega
    have hj2 : j ≤ 327492 := by omega
    have hb : Blo 1307972 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
