-- Prove2me | solution 1 for syracuse_descends_range_1072617_1076617
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T20:22:31.17402+00:00
-- url     : https://prove2.me/submissions/849c3d3c-a62d-4a0c-b45c-1bfb0bca641d

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


theorem B2719757 : Blo 1072617 2719757 := bbase (se 3 (by rfl) ⟨509954, by rfl⟩ : syracuseStep 2719757 = 1019909) (by norm_num)
theorem B1835045 : Blo 1072617 1835045 := bbase (se 4 (by rfl) ⟨172035, by rfl⟩ : syracuseStep 1835045 = 344071) (by norm_num)
theorem B2326573 : Blo 1072617 2326573 := bbase (se 3 (by rfl) ⟨436232, by rfl⟩ : syracuseStep 2326573 = 872465) (by norm_num)
theorem B1147133 : Blo 1072617 1147133 := bbase (se 3 (by rfl) ⟨215087, by rfl⟩ : syracuseStep 1147133 = 430175) (by norm_num)
theorem B5505317 : Blo 1072617 5505317 := bbase (se 4 (by rfl) ⟨516123, by rfl⟩ : syracuseStep 5505317 = 1032247) (by norm_num)
theorem B5439797 : Blo 1072617 5439797 := bbase (se 5 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 5439797 = 509981) (by norm_num)
theorem B2720101 : Blo 1072617 2720101 := bbase (se 4 (by rfl) ⟨255009, by rfl⟩ : syracuseStep 2720101 = 510019) (by norm_num)
theorem B2687381 : Blo 1072617 2687381 := bbase (se 6 (by rfl) ⟨62985, by rfl⟩ : syracuseStep 2687381 = 125971) (by norm_num)
theorem B1147321 : Blo 1072617 1147321 := bbase (se 2 (by rfl) ⟨430245, by rfl⟩ : syracuseStep 1147321 = 860491) (by norm_num)
theorem B2720213 : Blo 1072617 2720213 := bbase (se 7 (by rfl) ⟨31877, by rfl⟩ : syracuseStep 2720213 = 63755) (by norm_num)
theorem B5898869 : Blo 1072617 5898869 := bbase (se 5 (by rfl) ⟨276509, by rfl⟩ : syracuseStep 5898869 = 553019) (by norm_num)
theorem B2720405 : Blo 1072617 2720405 := bbase (se 6 (by rfl) ⟨63759, by rfl⟩ : syracuseStep 2720405 = 127519) (by norm_num)
theorem B3867365 : Blo 1072617 3867365 := bbase (se 4 (by rfl) ⟨362565, by rfl⟩ : syracuseStep 3867365 = 725131) (by norm_num)
theorem B2294573 : Blo 1072617 2294573 := bbase (se 3 (by rfl) ⟨430232, by rfl⟩ : syracuseStep 2294573 = 860465) (by norm_num)
theorem B3441541 : Blo 1072617 3441541 := bbase (se 4 (by rfl) ⟨322644, by rfl⟩ : syracuseStep 3441541 = 645289) (by norm_num)
theorem B2720749 : Blo 1072617 2720749 := bbase (se 3 (by rfl) ⟨510140, by rfl⟩ : syracuseStep 2720749 = 1020281) (by norm_num)
theorem B2294813 : Blo 1072617 2294813 := bbase (se 3 (by rfl) ⟨430277, by rfl⟩ : syracuseStep 2294813 = 860555) (by norm_num)
theorem B2720861 : Blo 1072617 2720861 := bbase (se 3 (by rfl) ⟨510161, by rfl⟩ : syracuseStep 2720861 = 1020323) (by norm_num)
theorem B1148141 : Blo 1072617 1148141 := bbase (se 3 (by rfl) ⟨215276, by rfl⟩ : syracuseStep 1148141 = 430553) (by norm_num)
theorem B6128885 : Blo 1072617 6128885 := bbase (se 5 (by rfl) ⟨287291, by rfl⟩ : syracuseStep 6128885 = 574583) (by norm_num)
theorem B4588805 : Blo 1072617 4588805 := bbase (se 4 (by rfl) ⟨430200, by rfl⟩ : syracuseStep 4588805 = 860401) (by norm_num)
theorem B1934605 : Blo 1072617 1934605 := bbase (se 3 (by rfl) ⟨362738, by rfl⟩ : syracuseStep 1934605 = 725477) (by norm_num)
theorem B2721053 : Blo 1072617 2721053 := bbase (se 3 (by rfl) ⟨510197, by rfl⟩ : syracuseStep 2721053 = 1020395) (by norm_num)
theorem B3441989 : Blo 1072617 3441989 := bbase (se 4 (by rfl) ⟨322686, by rfl⟩ : syracuseStep 3441989 = 645373) (by norm_num)
theorem B1934749 : Blo 1072617 1934749 := bbase (se 3 (by rfl) ⟨362765, by rfl⟩ : syracuseStep 1934749 = 725531) (by norm_num)
theorem B4589045 : Blo 1072617 4589045 := bbase (se 5 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 4589045 = 430223) (by norm_num)
theorem B2295317 : Blo 1072617 2295317 := bbase (se 6 (by rfl) ⟨53796, by rfl⟩ : syracuseStep 2295317 = 107593) (by norm_num)
theorem B2295325 : Blo 1072617 2295325 := bbase (se 3 (by rfl) ⟨430373, by rfl⟩ : syracuseStep 2295325 = 860747) (by norm_num)
theorem B3671621 : Blo 1072617 3671621 := bbase (se 4 (by rfl) ⟨344214, by rfl⟩ : syracuseStep 3671621 = 688429) (by norm_num)
theorem B5441093 : Blo 1072617 5441093 := bbase (se 4 (by rfl) ⟨510102, by rfl⟩ : syracuseStep 5441093 = 1020205) (by norm_num)
theorem B2721397 : Blo 1072617 2721397 := bbase (se 5 (by rfl) ⟨127565, by rfl⟩ : syracuseStep 2721397 = 255131) (by norm_num)
theorem B1148585 : Blo 1072617 1148585 := bbase (se 2 (by rfl) ⟨430719, by rfl⟩ : syracuseStep 1148585 = 861439) (by norm_num)
theorem B2721509 : Blo 1072617 2721509 := bbase (se 4 (by rfl) ⟨255141, by rfl⟩ : syracuseStep 2721509 = 510283) (by norm_num)
theorem B6883157 : Blo 1072617 6883157 := bbase (se 9 (by rfl) ⟨20165, by rfl⟩ : syracuseStep 6883157 = 40331) (by norm_num)
theorem B1148833 : Blo 1072617 1148833 := bbase (se 2 (by rfl) ⟨430812, by rfl⟩ : syracuseStep 1148833 = 861625) (by norm_num)
theorem B2721701 : Blo 1072617 2721701 := bbase (se 4 (by rfl) ⟨255159, by rfl⟩ : syracuseStep 2721701 = 510319) (by norm_num)
theorem B8161397 : Blo 1072617 8161397 := bbase (se 5 (by rfl) ⟨382565, by rfl⟩ : syracuseStep 8161397 = 765131) (by norm_num)
theorem B2722045 : Blo 1072617 2722045 := bbase (se 3 (by rfl) ⟨510383, by rfl⟩ : syracuseStep 2722045 = 1020767) (by norm_num)
theorem B4360517 : Blo 1072617 4360517 := bbase (se 4 (by rfl) ⟨408798, by rfl⟩ : syracuseStep 4360517 = 817597) (by norm_num)
theorem B1149265 : Blo 1072617 1149265 := bbase (se 2 (by rfl) ⟨430974, by rfl⟩ : syracuseStep 1149265 = 861949) (by norm_num)
theorem B2754917 : Blo 1072617 2754917 := bbase (se 4 (by rfl) ⟨258273, by rfl⟩ : syracuseStep 2754917 = 516547) (by norm_num)
theorem B1378669 : Blo 1072617 1378669 := bbase (se 3 (by rfl) ⟨258500, by rfl⟩ : syracuseStep 1378669 = 517001) (by norm_num)
theorem B2722157 : Blo 1072617 2722157 := bbase (se 3 (by rfl) ⟨510404, by rfl⟩ : syracuseStep 2722157 = 1020809) (by norm_num)
theorem B1149337 : Blo 1072617 1149337 := bbase (se 2 (by rfl) ⟨431001, by rfl⟩ : syracuseStep 1149337 = 862003) (by norm_num)
theorem B2394541 : Blo 1072617 2394541 := bbase (se 3 (by rfl) ⟨448976, by rfl⟩ : syracuseStep 2394541 = 897953) (by norm_num)
theorem B2722349 : Blo 1072617 2722349 := bbase (se 3 (by rfl) ⟨510440, by rfl⟩ : syracuseStep 2722349 = 1020881) (by norm_num)
theorem B2099773 : Blo 1072617 2099773 := bbase (se 3 (by rfl) ⟨393707, by rfl⟩ : syracuseStep 2099773 = 787415) (by norm_num)
theorem B1935989 : Blo 1072617 1935989 := bbase (se 5 (by rfl) ⟨90749, by rfl⟩ : syracuseStep 1935989 = 181499) (by norm_num)
theorem B2296453 : Blo 1072617 2296453 := bbase (se 4 (by rfl) ⟨215292, by rfl⟩ : syracuseStep 2296453 = 430585) (by norm_num)
theorem B5442389 : Blo 1072617 5442389 := bbase (se 9 (by rfl) ⟨15944, by rfl⟩ : syracuseStep 5442389 = 31889) (by norm_num)
theorem B2722693 : Blo 1072617 2722693 := bbase (se 4 (by rfl) ⟨255252, by rfl⟩ : syracuseStep 2722693 = 510505) (by norm_num)
theorem B2722805 : Blo 1072617 2722805 := bbase (se 5 (by rfl) ⟨127631, by rfl⟩ : syracuseStep 2722805 = 255263) (by norm_num)
theorem B2296829 : Blo 1072617 2296829 := bbase (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) (by norm_num)
theorem B1379449 : Blo 1072617 1379449 := bbase (se 2 (by rfl) ⟨517293, by rfl⟩ : syracuseStep 1379449 = 1034587) (by norm_num)
theorem B2722997 : Blo 1072617 2722997 := bbase (se 5 (by rfl) ⟨127640, by rfl⟩ : syracuseStep 2722997 = 255281) (by norm_num)
theorem B1608941 : Blo 1072617 1608941 := bbase (se 3 (by rfl) ⟨301676, by rfl⟩ : syracuseStep 1608941 = 603353) (by norm_num)
theorem B1608965 : Blo 1072617 1608965 := bbase (se 4 (by rfl) ⟨150840, by rfl⟩ : syracuseStep 1608965 = 301681) (by norm_num)
theorem B1608989 : Blo 1072617 1608989 := bbase (se 3 (by rfl) ⟨301685, by rfl⟩ : syracuseStep 1608989 = 603371) (by norm_num)
theorem B1609013 : Blo 1072617 1609013 := bbase (se 5 (by rfl) ⟨75422, by rfl⟩ : syracuseStep 1609013 = 150845) (by norm_num)
theorem B1609037 : Blo 1072617 1609037 := bbase (se 3 (by rfl) ⟨301694, by rfl⟩ : syracuseStep 1609037 = 603389) (by norm_num)
theorem B1609061 : Blo 1072617 1609061 := bbase (se 4 (by rfl) ⟨150849, by rfl⟩ : syracuseStep 1609061 = 301699) (by norm_num)
theorem B1609085 : Blo 1072617 1609085 := bbase (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) (by norm_num)
theorem B1609109 : Blo 1072617 1609109 := bbase (se 6 (by rfl) ⟨37713, by rfl⟩ : syracuseStep 1609109 = 75427) (by norm_num)
theorem B3673493 : Blo 1072617 3673493 := bbase (se 6 (by rfl) ⟨86097, by rfl⟩ : syracuseStep 3673493 = 172195) (by norm_num)
theorem B1609133 : Blo 1072617 1609133 := bbase (se 3 (by rfl) ⟨301712, by rfl⟩ : syracuseStep 1609133 = 603425) (by norm_num)
theorem B1609157 : Blo 1072617 1609157 := bbase (se 4 (by rfl) ⟨150858, by rfl⟩ : syracuseStep 1609157 = 301717) (by norm_num)
theorem B1609181 : Blo 1072617 1609181 := bbase (se 3 (by rfl) ⟨301721, by rfl⟩ : syracuseStep 1609181 = 603443) (by norm_num)
theorem B2067941 : Blo 1072617 2067941 := bbase (se 4 (by rfl) ⟨193869, by rfl⟩ : syracuseStep 2067941 = 387739) (by norm_num)
theorem B1609205 : Blo 1072617 1609205 := bbase (se 5 (by rfl) ⟨75431, by rfl⟩ : syracuseStep 1609205 = 150863) (by norm_num)
theorem B1609229 : Blo 1072617 1609229 := bbase (se 3 (by rfl) ⟨301730, by rfl⟩ : syracuseStep 1609229 = 603461) (by norm_num)
theorem B2723341 : Blo 1072617 2723341 := bbase (se 3 (by rfl) ⟨510626, by rfl⟩ : syracuseStep 2723341 = 1021253) (by norm_num)
theorem B3444245 : Blo 1072617 3444245 := bbase (se 6 (by rfl) ⟨80724, by rfl⟩ : syracuseStep 3444245 = 161449) (by norm_num)
theorem B1609253 : Blo 1072617 1609253 := bbase (se 4 (by rfl) ⟨150867, by rfl⟩ : syracuseStep 1609253 = 301735) (by norm_num)
theorem B1609277 : Blo 1072617 1609277 := bbase (se 3 (by rfl) ⟨301739, by rfl⟩ : syracuseStep 1609277 = 603479) (by norm_num)
theorem B1609301 : Blo 1072617 1609301 := bbase (se 8 (by rfl) ⟨9429, by rfl⟩ : syracuseStep 1609301 = 18859) (by norm_num)
theorem B1609325 : Blo 1072617 1609325 := bbase (se 3 (by rfl) ⟨301748, by rfl⟩ : syracuseStep 1609325 = 603497) (by norm_num)
theorem B2723453 : Blo 1072617 2723453 := bbase (se 3 (by rfl) ⟨510647, by rfl⟩ : syracuseStep 2723453 = 1021295) (by norm_num)
theorem B1609349 : Blo 1072617 1609349 := bbase (se 4 (by rfl) ⟨150876, by rfl⟩ : syracuseStep 1609349 = 301753) (by norm_num)
theorem B1609373 : Blo 1072617 1609373 := bbase (se 3 (by rfl) ⟨301757, by rfl⟩ : syracuseStep 1609373 = 603515) (by norm_num)
theorem B1609397 : Blo 1072617 1609397 := bbase (se 5 (by rfl) ⟨75440, by rfl⟩ : syracuseStep 1609397 = 150881) (by norm_num)
theorem B1609421 : Blo 1072617 1609421 := bbase (se 3 (by rfl) ⟨301766, by rfl⟩ : syracuseStep 1609421 = 603533) (by norm_num)
theorem B1609445 : Blo 1072617 1609445 := bbase (se 4 (by rfl) ⟨150885, by rfl⟩ : syracuseStep 1609445 = 301771) (by norm_num)
theorem B4591333 : Blo 1072617 4591333 := bbase (se 4 (by rfl) ⟨430437, by rfl⟩ : syracuseStep 4591333 = 860875) (by norm_num)
theorem B1609469 : Blo 1072617 1609469 := bbase (se 3 (by rfl) ⟨301775, by rfl⟩ : syracuseStep 1609469 = 603551) (by norm_num)
theorem B1609493 : Blo 1072617 1609493 := bbase (se 6 (by rfl) ⟨37722, by rfl⟩ : syracuseStep 1609493 = 75445) (by norm_num)
theorem B1609517 : Blo 1072617 1609517 := bbase (se 3 (by rfl) ⟨301784, by rfl⟩ : syracuseStep 1609517 = 603569) (by norm_num)
theorem B2723645 : Blo 1072617 2723645 := bbase (se 3 (by rfl) ⟨510683, by rfl⟩ : syracuseStep 2723645 = 1021367) (by norm_num)
theorem B1609541 : Blo 1072617 1609541 := bbase (se 4 (by rfl) ⟨150894, by rfl⟩ : syracuseStep 1609541 = 301789) (by norm_num)
theorem B1609565 : Blo 1072617 1609565 := bbase (se 3 (by rfl) ⟨301793, by rfl⟩ : syracuseStep 1609565 = 603587) (by norm_num)
theorem B1609589 : Blo 1072617 1609589 := bbase (se 5 (by rfl) ⟨75449, by rfl⟩ : syracuseStep 1609589 = 150899) (by norm_num)
theorem B1609613 : Blo 1072617 1609613 := bbase (se 3 (by rfl) ⟨301802, by rfl⟩ : syracuseStep 1609613 = 603605) (by norm_num)
theorem B1609637 : Blo 1072617 1609637 := bbase (se 4 (by rfl) ⟨150903, by rfl⟩ : syracuseStep 1609637 = 301807) (by norm_num)
theorem B1609661 : Blo 1072617 1609661 := bbase (se 3 (by rfl) ⟨301811, by rfl⟩ : syracuseStep 1609661 = 603623) (by norm_num)
theorem B1609685 : Blo 1072617 1609685 := bbase (se 7 (by rfl) ⟨18863, by rfl⟩ : syracuseStep 1609685 = 37727) (by norm_num)
theorem B11636693 : Blo 1072617 11636693 := bbase (se 7 (by rfl) ⟨136367, by rfl⟩ : syracuseStep 11636693 = 272735) (by norm_num)
theorem B1609709 : Blo 1072617 1609709 := bbase (se 3 (by rfl) ⟨301820, by rfl⟩ : syracuseStep 1609709 = 603641) (by norm_num)
theorem B1609733 : Blo 1072617 1609733 := bbase (se 4 (by rfl) ⟨150912, by rfl⟩ : syracuseStep 1609733 = 301825) (by norm_num)
theorem B1609757 : Blo 1072617 1609757 := bbase (se 3 (by rfl) ⟨301829, by rfl⟩ : syracuseStep 1609757 = 603659) (by norm_num)
theorem B1609781 : Blo 1072617 1609781 := bbase (se 5 (by rfl) ⟨75458, by rfl⟩ : syracuseStep 1609781 = 150917) (by norm_num)
theorem B2330677 : Blo 1072617 2330677 := bbase (se 5 (by rfl) ⟨109250, by rfl⟩ : syracuseStep 2330677 = 218501) (by norm_num)
theorem B1609805 : Blo 1072617 1609805 := bbase (se 3 (by rfl) ⟨301838, by rfl⟩ : syracuseStep 1609805 = 603677) (by norm_num)
theorem B1609829 : Blo 1072617 1609829 := bbase (se 4 (by rfl) ⟨150921, by rfl⟩ : syracuseStep 1609829 = 301843) (by norm_num)
theorem B5443685 : Blo 1072617 5443685 := bbase (se 4 (by rfl) ⟨510345, by rfl⟩ : syracuseStep 5443685 = 1020691) (by norm_num)
theorem B1609853 : Blo 1072617 1609853 := bbase (se 3 (by rfl) ⟨301847, by rfl⟩ : syracuseStep 1609853 = 603695) (by norm_num)
theorem B1609877 : Blo 1072617 1609877 := bbase (se 6 (by rfl) ⟨37731, by rfl⟩ : syracuseStep 1609877 = 75463) (by norm_num)
theorem B2723989 : Blo 1072617 2723989 := bbase (se 6 (by rfl) ⟨63843, by rfl⟩ : syracuseStep 2723989 = 127687) (by norm_num)
theorem B1609901 : Blo 1072617 1609901 := bbase (se 3 (by rfl) ⟨301856, by rfl⟩ : syracuseStep 1609901 = 603713) (by norm_num)
theorem B1609925 : Blo 1072617 1609925 := bbase (se 4 (by rfl) ⟨150930, by rfl⟩ : syracuseStep 1609925 = 301861) (by norm_num)
theorem B30937301 : Blo 1072617 30937301 := bbase (se 7 (by rfl) ⟨362546, by rfl⟩ : syracuseStep 30937301 = 725093) (by norm_num)
theorem B1609949 : Blo 1072617 1609949 := bbase (se 3 (by rfl) ⟨301865, by rfl⟩ : syracuseStep 1609949 = 603731) (by norm_num)
theorem B1609973 : Blo 1072617 1609973 := bbase (se 5 (by rfl) ⟨75467, by rfl⟩ : syracuseStep 1609973 = 150935) (by norm_num)
theorem B2724101 : Blo 1072617 2724101 := bbase (se 4 (by rfl) ⟨255384, by rfl⟩ : syracuseStep 2724101 = 510769) (by norm_num)
theorem B1609997 : Blo 1072617 1609997 := bbase (se 3 (by rfl) ⟨301874, by rfl⟩ : syracuseStep 1609997 = 603749) (by norm_num)
theorem B1937677 : Blo 1072617 1937677 := bbase (se 3 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 1937677 = 726629) (by norm_num)
theorem B1610021 : Blo 1072617 1610021 := bbase (se 4 (by rfl) ⟨150939, by rfl⟩ : syracuseStep 1610021 = 301879) (by norm_num)
theorem B1610045 : Blo 1072617 1610045 := bbase (se 3 (by rfl) ⟨301883, by rfl⟩ : syracuseStep 1610045 = 603767) (by norm_num)
theorem B1610069 : Blo 1072617 1610069 := bbase (se 10 (by rfl) ⟨2358, by rfl⟩ : syracuseStep 1610069 = 4717) (by norm_num)
theorem B1610093 : Blo 1072617 1610093 := bbase (se 3 (by rfl) ⟨301892, by rfl⟩ : syracuseStep 1610093 = 603785) (by norm_num)
theorem B1610117 : Blo 1072617 1610117 := bbase (se 4 (by rfl) ⟨150948, by rfl⟩ : syracuseStep 1610117 = 301897) (by norm_num)
theorem B1610141 : Blo 1072617 1610141 := bbase (se 3 (by rfl) ⟨301901, by rfl⟩ : syracuseStep 1610141 = 603803) (by norm_num)
theorem B1610165 : Blo 1072617 1610165 := bbase (se 5 (by rfl) ⟨75476, by rfl⟩ : syracuseStep 1610165 = 150953) (by norm_num)
theorem B2724293 : Blo 1072617 2724293 := bbase (se 4 (by rfl) ⟨255402, by rfl⟩ : syracuseStep 2724293 = 510805) (by norm_num)
theorem B1610189 : Blo 1072617 1610189 := bbase (se 3 (by rfl) ⟨301910, by rfl⟩ : syracuseStep 1610189 = 603821) (by norm_num)
theorem B1610213 : Blo 1072617 1610213 := bbase (se 4 (by rfl) ⟨150957, by rfl⟩ : syracuseStep 1610213 = 301915) (by norm_num)
theorem B1610237 : Blo 1072617 1610237 := bbase (se 3 (by rfl) ⟨301919, by rfl⟩ : syracuseStep 1610237 = 603839) (by norm_num)
theorem B1610261 : Blo 1072617 1610261 := bbase (se 6 (by rfl) ⟨37740, by rfl⟩ : syracuseStep 1610261 = 75481) (by norm_num)
theorem B1610285 : Blo 1072617 1610285 := bbase (se 3 (by rfl) ⟨301928, by rfl⟩ : syracuseStep 1610285 = 603857) (by norm_num)
theorem B1937965 : Blo 1072617 1937965 := bbase (se 3 (by rfl) ⟨363368, by rfl⟩ : syracuseStep 1937965 = 726737) (by norm_num)
theorem B1610309 : Blo 1072617 1610309 := bbase (se 4 (by rfl) ⟨150966, by rfl⟩ : syracuseStep 1610309 = 301933) (by norm_num)
theorem B1610333 : Blo 1072617 1610333 := bbase (se 3 (by rfl) ⟨301937, by rfl⟩ : syracuseStep 1610333 = 603875) (by norm_num)
theorem B2298469 : Blo 1072617 2298469 := bbase (se 4 (by rfl) ⟨215481, by rfl⟩ : syracuseStep 2298469 = 430963) (by norm_num)
theorem B2036333 : Blo 1072617 2036333 := bbase (se 3 (by rfl) ⟨381812, by rfl⟩ : syracuseStep 2036333 = 763625) (by norm_num)
theorem B1610357 : Blo 1072617 1610357 := bbase (se 5 (by rfl) ⟨75485, by rfl⟩ : syracuseStep 1610357 = 150971) (by norm_num)
theorem B1610381 : Blo 1072617 1610381 := bbase (se 3 (by rfl) ⟨301946, by rfl⟩ : syracuseStep 1610381 = 603893) (by norm_num)
theorem B1610405 : Blo 1072617 1610405 := bbase (se 4 (by rfl) ⟨150975, by rfl⟩ : syracuseStep 1610405 = 301951) (by norm_num)
theorem B1610429 : Blo 1072617 1610429 := bbase (se 3 (by rfl) ⟨301955, by rfl⟩ : syracuseStep 1610429 = 603911) (by norm_num)
theorem B1610453 : Blo 1072617 1610453 := bbase (se 7 (by rfl) ⟨18872, by rfl⟩ : syracuseStep 1610453 = 37745) (by norm_num)
theorem B1610477 : Blo 1072617 1610477 := bbase (se 3 (by rfl) ⟨301964, by rfl⟩ : syracuseStep 1610477 = 603929) (by norm_num)
theorem B2036477 : Blo 1072617 2036477 := bbase (se 3 (by rfl) ⟨381839, by rfl⟩ : syracuseStep 2036477 = 763679) (by norm_num)
theorem B1610501 : Blo 1072617 1610501 := bbase (se 4 (by rfl) ⟨150984, by rfl⟩ : syracuseStep 1610501 = 301969) (by norm_num)
theorem B1610525 : Blo 1072617 1610525 := bbase (se 3 (by rfl) ⟨301973, by rfl⟩ : syracuseStep 1610525 = 603947) (by norm_num)
theorem B2724637 : Blo 1072617 2724637 := bbase (se 3 (by rfl) ⟨510869, by rfl⟩ : syracuseStep 2724637 = 1021739) (by norm_num)
theorem B1610549 : Blo 1072617 1610549 := bbase (se 5 (by rfl) ⟨75494, by rfl⟩ : syracuseStep 1610549 = 150989) (by norm_num)
theorem B1610573 : Blo 1072617 1610573 := bbase (se 3 (by rfl) ⟨301982, by rfl⟩ : syracuseStep 1610573 = 603965) (by norm_num)
theorem B1610597 : Blo 1072617 1610597 := bbase (se 4 (by rfl) ⟨150993, by rfl⟩ : syracuseStep 1610597 = 301987) (by norm_num)
theorem B2069357 : Blo 1072617 2069357 := bbase (se 3 (by rfl) ⟨388004, by rfl⟩ : syracuseStep 2069357 = 776009) (by norm_num)
theorem B1610621 : Blo 1072617 1610621 := bbase (se 3 (by rfl) ⟨301991, by rfl⟩ : syracuseStep 1610621 = 603983) (by norm_num)
theorem B2724749 : Blo 1072617 2724749 := bbase (se 3 (by rfl) ⟨510890, by rfl⟩ : syracuseStep 2724749 = 1021781) (by norm_num)
theorem B1610645 : Blo 1072617 1610645 := bbase (se 6 (by rfl) ⟨37749, by rfl⟩ : syracuseStep 1610645 = 75499) (by norm_num)
theorem B1610669 : Blo 1072617 1610669 := bbase (se 3 (by rfl) ⟨302000, by rfl⟩ : syracuseStep 1610669 = 604001) (by norm_num)
theorem B1610693 : Blo 1072617 1610693 := bbase (se 4 (by rfl) ⟨151002, by rfl⟩ : syracuseStep 1610693 = 302005) (by norm_num)
theorem B1610717 : Blo 1072617 1610717 := bbase (se 3 (by rfl) ⟨302009, by rfl⟩ : syracuseStep 1610717 = 604019) (by norm_num)
theorem B1610741 : Blo 1072617 1610741 := bbase (se 5 (by rfl) ⟨75503, by rfl⟩ : syracuseStep 1610741 = 151007) (by norm_num)
theorem B1610765 : Blo 1072617 1610765 := bbase (se 3 (by rfl) ⟨302018, by rfl⟩ : syracuseStep 1610765 = 604037) (by norm_num)
theorem B2036765 : Blo 1072617 2036765 := bbase (se 3 (by rfl) ⟨381893, by rfl⟩ : syracuseStep 2036765 = 763787) (by norm_num)
theorem B1610789 : Blo 1072617 1610789 := bbase (se 4 (by rfl) ⟨151011, by rfl⟩ : syracuseStep 1610789 = 302023) (by norm_num)
theorem B1610813 : Blo 1072617 1610813 := bbase (se 3 (by rfl) ⟨302027, by rfl⟩ : syracuseStep 1610813 = 604055) (by norm_num)
theorem B2724941 : Blo 1072617 2724941 := bbase (se 3 (by rfl) ⟨510926, by rfl⟩ : syracuseStep 2724941 = 1021853) (by norm_num)
theorem B1610837 : Blo 1072617 1610837 := bbase (se 8 (by rfl) ⟨9438, by rfl⟩ : syracuseStep 1610837 = 18877) (by norm_num)
theorem B1610861 : Blo 1072617 1610861 := bbase (se 3 (by rfl) ⟨302036, by rfl⟩ : syracuseStep 1610861 = 604073) (by norm_num)
theorem B1610885 : Blo 1072617 1610885 := bbase (se 4 (by rfl) ⟨151020, by rfl⟩ : syracuseStep 1610885 = 302041) (by norm_num)
theorem B1610909 : Blo 1072617 1610909 := bbase (se 3 (by rfl) ⟨302045, by rfl⟩ : syracuseStep 1610909 = 604091) (by norm_num)
theorem B2036917 : Blo 1072617 2036917 := bbase (se 5 (by rfl) ⟨95480, by rfl⟩ : syracuseStep 2036917 = 190961) (by norm_num)
theorem B1610933 : Blo 1072617 1610933 := bbase (se 5 (by rfl) ⟨75512, by rfl⟩ : syracuseStep 1610933 = 151025) (by norm_num)
theorem B4592821 : Blo 1072617 4592821 := bbase (se 5 (by rfl) ⟨215288, by rfl⟩ : syracuseStep 4592821 = 430577) (by norm_num)
theorem B4592837 : Blo 1072617 4592837 := bbase (se 4 (by rfl) ⟨430578, by rfl⟩ : syracuseStep 4592837 = 861157) (by norm_num)
theorem B1610957 : Blo 1072617 1610957 := bbase (se 3 (by rfl) ⟨302054, by rfl⟩ : syracuseStep 1610957 = 604109) (by norm_num)
theorem B1610981 : Blo 1072617 1610981 := bbase (se 4 (by rfl) ⟨151029, by rfl⟩ : syracuseStep 1610981 = 302059) (by norm_num)
theorem B1611005 : Blo 1072617 1611005 := bbase (se 3 (by rfl) ⟨302063, by rfl⟩ : syracuseStep 1611005 = 604127) (by norm_num)
theorem B1611029 : Blo 1072617 1611029 := bbase (se 6 (by rfl) ⟨37758, by rfl⟩ : syracuseStep 1611029 = 75517) (by norm_num)
theorem B1611053 : Blo 1072617 1611053 := bbase (se 3 (by rfl) ⟨302072, by rfl⟩ : syracuseStep 1611053 = 604145) (by norm_num)
theorem B8262965 : Blo 1072617 8262965 := bbase (se 5 (by rfl) ⟨387326, by rfl⟩ : syracuseStep 8262965 = 774653) (by norm_num)
theorem B1611077 : Blo 1072617 1611077 := bbase (se 4 (by rfl) ⟨151038, by rfl⟩ : syracuseStep 1611077 = 302077) (by norm_num)
theorem B1938757 : Blo 1072617 1938757 := bbase (se 4 (by rfl) ⟨181758, by rfl⟩ : syracuseStep 1938757 = 363517) (by norm_num)
theorem B1611101 : Blo 1072617 1611101 := bbase (se 3 (by rfl) ⟨302081, by rfl⟩ : syracuseStep 1611101 = 604163) (by norm_num)
theorem B2692445 : Blo 1072617 2692445 := bbase (se 3 (by rfl) ⟨504833, by rfl⟩ : syracuseStep 2692445 = 1009667) (by norm_num)
theorem B1611125 : Blo 1072617 1611125 := bbase (se 5 (by rfl) ⟨75521, by rfl⟩ : syracuseStep 1611125 = 151043) (by norm_num)
theorem B5444981 : Blo 1072617 5444981 := bbase (se 5 (by rfl) ⟨255233, by rfl⟩ : syracuseStep 5444981 = 510467) (by norm_num)
theorem B1611149 : Blo 1072617 1611149 := bbase (se 3 (by rfl) ⟨302090, by rfl⟩ : syracuseStep 1611149 = 604181) (by norm_num)
theorem B1611173 : Blo 1072617 1611173 := bbase (se 4 (by rfl) ⟨151047, by rfl⟩ : syracuseStep 1611173 = 302095) (by norm_num)
theorem B1611197 : Blo 1072617 1611197 := bbase (se 3 (by rfl) ⟨302099, by rfl⟩ : syracuseStep 1611197 = 604199) (by norm_num)
theorem B1611221 : Blo 1072617 1611221 := bbase (se 7 (by rfl) ⟨18881, by rfl⟩ : syracuseStep 1611221 = 37763) (by norm_num)
theorem B8721877 : Blo 1072617 8721877 := bbase (se 7 (by rfl) ⟨102209, by rfl⟩ : syracuseStep 8721877 = 204419) (by norm_num)
theorem B1938901 : Blo 1072617 1938901 := bbase (se 7 (by rfl) ⟨22721, by rfl⟩ : syracuseStep 1938901 = 45443) (by norm_num)
theorem B2299357 : Blo 1072617 2299357 := bbase (se 3 (by rfl) ⟨431129, by rfl⟩ : syracuseStep 2299357 = 862259) (by norm_num)
theorem B2037221 : Blo 1072617 2037221 := bbase (se 4 (by rfl) ⟨190989, by rfl⟩ : syracuseStep 2037221 = 381979) (by norm_num)
theorem B1611245 : Blo 1072617 1611245 := bbase (se 3 (by rfl) ⟨302108, by rfl⟩ : syracuseStep 1611245 = 604217) (by norm_num)
theorem B1611269 : Blo 1072617 1611269 := bbase (se 4 (by rfl) ⟨151056, by rfl⟩ : syracuseStep 1611269 = 302113) (by norm_num)
theorem B5805589 : Blo 1072617 5805589 := bbase (se 6 (by rfl) ⟨136068, by rfl⟩ : syracuseStep 5805589 = 272137) (by norm_num)
theorem B1611293 : Blo 1072617 1611293 := bbase (se 3 (by rfl) ⟨302117, by rfl⟩ : syracuseStep 1611293 = 604235) (by norm_num)
theorem B1611317 : Blo 1072617 1611317 := bbase (se 5 (by rfl) ⟨75530, by rfl⟩ : syracuseStep 1611317 = 151061) (by norm_num)
theorem B1611341 : Blo 1072617 1611341 := bbase (se 3 (by rfl) ⟨302126, by rfl⟩ : syracuseStep 1611341 = 604253) (by norm_num)
theorem B1611365 : Blo 1072617 1611365 := bbase (se 4 (by rfl) ⟨151065, by rfl⟩ : syracuseStep 1611365 = 302131) (by norm_num)
theorem B1939061 : Blo 1072617 1939061 := bbase (se 5 (by rfl) ⟨90893, by rfl⟩ : syracuseStep 1939061 = 181787) (by norm_num)
theorem B1611389 : Blo 1072617 1611389 := bbase (se 3 (by rfl) ⟨302135, by rfl⟩ : syracuseStep 1611389 = 604271) (by norm_num)
theorem B12228245 : Blo 1072617 12228245 := bbase (se 6 (by rfl) ⟨286599, by rfl⟩ : syracuseStep 12228245 = 573199) (by norm_num)
theorem B1611413 : Blo 1072617 1611413 := bbase (se 6 (by rfl) ⟨37767, by rfl⟩ : syracuseStep 1611413 = 75535) (by norm_num)
theorem B1611437 : Blo 1072617 1611437 := bbase (se 3 (by rfl) ⟨302144, by rfl⟩ : syracuseStep 1611437 = 604289) (by norm_num)
theorem B10327733 : Blo 1072617 10327733 := bbase (se 5 (by rfl) ⟨484112, by rfl⟩ : syracuseStep 10327733 = 968225) (by norm_num)
theorem B1939133 : Blo 1072617 1939133 := bbase (se 3 (by rfl) ⟨363587, by rfl⟩ : syracuseStep 1939133 = 727175) (by norm_num)
theorem B1611461 : Blo 1072617 1611461 := bbase (se 4 (by rfl) ⟨151074, by rfl⟩ : syracuseStep 1611461 = 302149) (by norm_num)
theorem B1611485 : Blo 1072617 1611485 := bbase (se 3 (by rfl) ⟨302153, by rfl⟩ : syracuseStep 1611485 = 604307) (by norm_num)
theorem B1611509 : Blo 1072617 1611509 := bbase (se 5 (by rfl) ⟨75539, by rfl⟩ : syracuseStep 1611509 = 151079) (by norm_num)
theorem B1611533 : Blo 1072617 1611533 := bbase (se 3 (by rfl) ⟨302162, by rfl⟩ : syracuseStep 1611533 = 604325) (by norm_num)
theorem B1611557 : Blo 1072617 1611557 := bbase (se 4 (by rfl) ⟨151083, by rfl⟩ : syracuseStep 1611557 = 302167) (by norm_num)
theorem B1611581 : Blo 1072617 1611581 := bbase (se 3 (by rfl) ⟨302171, by rfl⟩ : syracuseStep 1611581 = 604343) (by norm_num)
theorem B1611605 : Blo 1072617 1611605 := bbase (se 9 (by rfl) ⟨4721, by rfl⟩ : syracuseStep 1611605 = 9443) (by norm_num)
theorem B1611629 : Blo 1072617 1611629 := bbase (se 3 (by rfl) ⟨302180, by rfl⟩ : syracuseStep 1611629 = 604361) (by norm_num)
theorem B1611653 : Blo 1072617 1611653 := bbase (se 4 (by rfl) ⟨151092, by rfl⟩ : syracuseStep 1611653 = 302185) (by norm_num)
theorem B1087381 : Blo 1072617 1087381 := bbase (se 6 (by rfl) ⟨25485, by rfl⟩ : syracuseStep 1087381 = 50971) (by norm_num)
theorem B1611677 : Blo 1072617 1611677 := bbase (se 3 (by rfl) ⟨302189, by rfl⟩ : syracuseStep 1611677 = 604379) (by norm_num)
theorem B1611701 : Blo 1072617 1611701 := bbase (se 5 (by rfl) ⟨75548, by rfl⟩ : syracuseStep 1611701 = 151097) (by norm_num)
theorem B1611725 : Blo 1072617 1611725 := bbase (se 3 (by rfl) ⟨302198, by rfl⟩ : syracuseStep 1611725 = 604397) (by norm_num)
theorem B1611749 : Blo 1072617 1611749 := bbase (se 4 (by rfl) ⟨151101, by rfl⟩ : syracuseStep 1611749 = 302203) (by norm_num)
theorem B1611773 : Blo 1072617 1611773 := bbase (se 3 (by rfl) ⟨302207, by rfl⟩ : syracuseStep 1611773 = 604415) (by norm_num)
theorem B1611797 : Blo 1072617 1611797 := bbase (se 6 (by rfl) ⟨37776, by rfl⟩ : syracuseStep 1611797 = 75553) (by norm_num)
theorem B1611821 : Blo 1072617 1611821 := bbase (se 3 (by rfl) ⟨302216, by rfl⟩ : syracuseStep 1611821 = 604433) (by norm_num)
theorem B1611845 : Blo 1072617 1611845 := bbase (se 4 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 1611845 = 302221) (by norm_num)
theorem B1611869 : Blo 1072617 1611869 := bbase (se 3 (by rfl) ⟨302225, by rfl⟩ : syracuseStep 1611869 = 604451) (by norm_num)
theorem B1611893 : Blo 1072617 1611893 := bbase (se 5 (by rfl) ⟨75557, by rfl⟩ : syracuseStep 1611893 = 151115) (by norm_num)
theorem B1611917 : Blo 1072617 1611917 := bbase (se 3 (by rfl) ⟨302234, by rfl⟩ : syracuseStep 1611917 = 604469) (by norm_num)
theorem B1611941 : Blo 1072617 1611941 := bbase (se 4 (by rfl) ⟨151119, by rfl⟩ : syracuseStep 1611941 = 302239) (by norm_num)
theorem B1611965 : Blo 1072617 1611965 := bbase (se 3 (by rfl) ⟨302243, by rfl⟩ : syracuseStep 1611965 = 604487) (by norm_num)
theorem B2037973 : Blo 1072617 2037973 := bbase (se 7 (by rfl) ⟨23882, by rfl⟩ : syracuseStep 2037973 = 47765) (by norm_num)
theorem B1611989 : Blo 1072617 1611989 := bbase (se 7 (by rfl) ⟨18890, by rfl⟩ : syracuseStep 1611989 = 37781) (by norm_num)
theorem B1612013 : Blo 1072617 1612013 := bbase (se 3 (by rfl) ⟨302252, by rfl⟩ : syracuseStep 1612013 = 604505) (by norm_num)
theorem B1612037 : Blo 1072617 1612037 := bbase (se 4 (by rfl) ⟨151128, by rfl⟩ : syracuseStep 1612037 = 302257) (by norm_num)
theorem B1612061 : Blo 1072617 1612061 := bbase (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) (by norm_num)
theorem B1612085 : Blo 1072617 1612085 := bbase (se 5 (by rfl) ⟨75566, by rfl⟩ : syracuseStep 1612085 = 151133) (by norm_num)
theorem B1612109 : Blo 1072617 1612109 := bbase (se 3 (by rfl) ⟨302270, by rfl⟩ : syracuseStep 1612109 = 604541) (by norm_num)
theorem B2038117 : Blo 1072617 2038117 := bbase (se 4 (by rfl) ⟨191073, by rfl⟩ : syracuseStep 2038117 = 382147) (by norm_num)
theorem B1612133 : Blo 1072617 1612133 := bbase (se 4 (by rfl) ⟨151137, by rfl⟩ : syracuseStep 1612133 = 302275) (by norm_num)
theorem B1743229 : Blo 1072617 1743229 := bbase (se 3 (by rfl) ⟨326855, by rfl⟩ : syracuseStep 1743229 = 653711) (by norm_num)
theorem B1612157 : Blo 1072617 1612157 := bbase (se 3 (by rfl) ⟨302279, by rfl⟩ : syracuseStep 1612157 = 604559) (by norm_num)
theorem B1612181 : Blo 1072617 1612181 := bbase (se 6 (by rfl) ⟨37785, by rfl⟩ : syracuseStep 1612181 = 75571) (by norm_num)
theorem B1612205 : Blo 1072617 1612205 := bbase (se 3 (by rfl) ⟨302288, by rfl⟩ : syracuseStep 1612205 = 604577) (by norm_num)
theorem B1612229 : Blo 1072617 1612229 := bbase (se 4 (by rfl) ⟨151146, by rfl⟩ : syracuseStep 1612229 = 302293) (by norm_num)
theorem B1612253 : Blo 1072617 1612253 := bbase (se 3 (by rfl) ⟨302297, by rfl⟩ : syracuseStep 1612253 = 604595) (by norm_num)
theorem B1612277 : Blo 1072617 1612277 := bbase (se 5 (by rfl) ⟨75575, by rfl⟩ : syracuseStep 1612277 = 151151) (by norm_num)
theorem B2038277 : Blo 1072617 2038277 := bbase (se 4 (by rfl) ⟨191088, by rfl⟩ : syracuseStep 2038277 = 382177) (by norm_num)
theorem B1612301 : Blo 1072617 1612301 := bbase (se 3 (by rfl) ⟨302306, by rfl⟩ : syracuseStep 1612301 = 604613) (by norm_num)
theorem B1612325 : Blo 1072617 1612325 := bbase (se 4 (by rfl) ⟨151155, by rfl⟩ : syracuseStep 1612325 = 302311) (by norm_num)
theorem B1612349 : Blo 1072617 1612349 := bbase (se 3 (by rfl) ⟨302315, by rfl⟩ : syracuseStep 1612349 = 604631) (by norm_num)
theorem B1612373 : Blo 1072617 1612373 := bbase (se 8 (by rfl) ⟨9447, by rfl⟩ : syracuseStep 1612373 = 18895) (by norm_num)
theorem B1612397 : Blo 1072617 1612397 := bbase (se 3 (by rfl) ⟨302324, by rfl⟩ : syracuseStep 1612397 = 604649) (by norm_num)
theorem B1612421 : Blo 1072617 1612421 := bbase (se 4 (by rfl) ⟨151164, by rfl⟩ : syracuseStep 1612421 = 302329) (by norm_num)
theorem B5446277 : Blo 1072617 5446277 := bbase (se 4 (by rfl) ⟨510588, by rfl⟩ : syracuseStep 5446277 = 1021177) (by norm_num)
theorem B2038421 : Blo 1072617 2038421 := bbase (se 6 (by rfl) ⟨47775, by rfl⟩ : syracuseStep 2038421 = 95551) (by norm_num)
theorem B1612445 : Blo 1072617 1612445 := bbase (se 3 (by rfl) ⟨302333, by rfl⟩ : syracuseStep 1612445 = 604667) (by norm_num)
theorem B1612469 : Blo 1072617 1612469 := bbase (se 5 (by rfl) ⟨75584, by rfl⟩ : syracuseStep 1612469 = 151169) (by norm_num)
theorem B1612493 : Blo 1072617 1612493 := bbase (se 3 (by rfl) ⟨302342, by rfl⟩ : syracuseStep 1612493 = 604685) (by norm_num)
theorem B1612517 : Blo 1072617 1612517 := bbase (se 4 (by rfl) ⟨151173, by rfl⟩ : syracuseStep 1612517 = 302347) (by norm_num)
theorem B1612541 : Blo 1072617 1612541 := bbase (se 3 (by rfl) ⟨302351, by rfl⟩ : syracuseStep 1612541 = 604703) (by norm_num)
theorem B1612565 : Blo 1072617 1612565 := bbase (se 6 (by rfl) ⟨37794, by rfl⟩ : syracuseStep 1612565 = 75589) (by norm_num)
theorem B1612589 : Blo 1072617 1612589 := bbase (se 3 (by rfl) ⟨302360, by rfl⟩ : syracuseStep 1612589 = 604721) (by norm_num)
theorem B1612613 : Blo 1072617 1612613 := bbase (se 4 (by rfl) ⟨151182, by rfl⟩ : syracuseStep 1612613 = 302365) (by norm_num)
theorem B1612637 : Blo 1072617 1612637 := bbase (se 3 (by rfl) ⟨302369, by rfl⟩ : syracuseStep 1612637 = 604739) (by norm_num)
theorem B1612661 : Blo 1072617 1612661 := bbase (se 5 (by rfl) ⟨75593, by rfl⟩ : syracuseStep 1612661 = 151187) (by norm_num)
theorem B1612685 : Blo 1072617 1612685 := bbase (se 3 (by rfl) ⟨302378, by rfl⟩ : syracuseStep 1612685 = 604757) (by norm_num)
theorem B1612709 : Blo 1072617 1612709 := bbase (se 4 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 1612709 = 302383) (by norm_num)
theorem B2038709 : Blo 1072617 2038709 := bbase (se 5 (by rfl) ⟨95564, by rfl⟩ : syracuseStep 2038709 = 191129) (by norm_num)
theorem B1612733 : Blo 1072617 1612733 := bbase (se 3 (by rfl) ⟨302387, by rfl⟩ : syracuseStep 1612733 = 604775) (by norm_num)
theorem B1612757 : Blo 1072617 1612757 := bbase (se 7 (by rfl) ⟨18899, by rfl⟩ : syracuseStep 1612757 = 37799) (by norm_num)
theorem B1612781 : Blo 1072617 1612781 := bbase (se 3 (by rfl) ⟨302396, by rfl⟩ : syracuseStep 1612781 = 604793) (by norm_num)
theorem B1612805 : Blo 1072617 1612805 := bbase (se 4 (by rfl) ⟨151200, by rfl⟩ : syracuseStep 1612805 = 302401) (by norm_num)
theorem B1612829 : Blo 1072617 1612829 := bbase (se 3 (by rfl) ⟨302405, by rfl⟩ : syracuseStep 1612829 = 604811) (by norm_num)
theorem B1612853 : Blo 1072617 1612853 := bbase (se 5 (by rfl) ⟨75602, by rfl⟩ : syracuseStep 1612853 = 151205) (by norm_num)
theorem B1088569 : Blo 1072617 1088569 := bbase (se 2 (by rfl) ⟨408213, by rfl⟩ : syracuseStep 1088569 = 816427) (by norm_num)
theorem B2038861 : Blo 1072617 2038861 := bbase (se 3 (by rfl) ⟨382286, by rfl⟩ : syracuseStep 2038861 = 764573) (by norm_num)
theorem B1612877 : Blo 1072617 1612877 := bbase (se 3 (by rfl) ⟨302414, by rfl⟩ : syracuseStep 1612877 = 604829) (by norm_num)
theorem B41294933 : Blo 1072617 41294933 := bbase (se 8 (by rfl) ⟨241962, by rfl⟩ : syracuseStep 41294933 = 483925) (by norm_num)
theorem B1612901 : Blo 1072617 1612901 := bbase (se 4 (by rfl) ⟨151209, by rfl⟩ : syracuseStep 1612901 = 302419) (by norm_num)
theorem B1612925 : Blo 1072617 1612925 := bbase (se 3 (by rfl) ⟨302423, by rfl⟩ : syracuseStep 1612925 = 604847) (by norm_num)
theorem B1612949 : Blo 1072617 1612949 := bbase (se 6 (by rfl) ⟨37803, by rfl⟩ : syracuseStep 1612949 = 75607) (by norm_num)
theorem B1612973 : Blo 1072617 1612973 := bbase (se 3 (by rfl) ⟨302432, by rfl⟩ : syracuseStep 1612973 = 604865) (by norm_num)
theorem B3054773 : Blo 1072617 3054773 := bbase (se 5 (by rfl) ⟨143192, by rfl⟩ : syracuseStep 3054773 = 286385) (by norm_num)
theorem B1612997 : Blo 1072617 1612997 := bbase (se 4 (by rfl) ⟨151218, by rfl⟩ : syracuseStep 1612997 = 302437) (by norm_num)
theorem B1613021 : Blo 1072617 1613021 := bbase (se 3 (by rfl) ⟨302441, by rfl⟩ : syracuseStep 1613021 = 604883) (by norm_num)
theorem B1613045 : Blo 1072617 1613045 := bbase (se 5 (by rfl) ⟨75611, by rfl⟩ : syracuseStep 1613045 = 151223) (by norm_num)
theorem B1613069 : Blo 1072617 1613069 := bbase (se 3 (by rfl) ⟨302450, by rfl⟩ : syracuseStep 1613069 = 604901) (by norm_num)
theorem B1613093 : Blo 1072617 1613093 := bbase (se 4 (by rfl) ⟨151227, by rfl⟩ : syracuseStep 1613093 = 302455) (by norm_num)
theorem B1613117 : Blo 1072617 1613117 := bbase (se 3 (by rfl) ⟨302459, by rfl⟩ : syracuseStep 1613117 = 604919) (by norm_num)
theorem B1613141 : Blo 1072617 1613141 := bbase (se 11 (by rfl) ⟨1181, by rfl⟩ : syracuseStep 1613141 = 2363) (by norm_num)
theorem B3448165 : Blo 1072617 3448165 := bbase (se 4 (by rfl) ⟨323265, by rfl⟩ : syracuseStep 3448165 = 646531) (by norm_num)
theorem B1613165 : Blo 1072617 1613165 := bbase (se 3 (by rfl) ⟨302468, by rfl⟩ : syracuseStep 1613165 = 604937) (by norm_num)
theorem B2039165 : Blo 1072617 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B1613189 : Blo 1072617 1613189 := bbase (se 4 (by rfl) ⟨151236, by rfl⟩ : syracuseStep 1613189 = 302473) (by norm_num)
theorem B4595093 : Blo 1072617 4595093 := bbase (se 6 (by rfl) ⟨107697, by rfl⟩ : syracuseStep 4595093 = 215395) (by norm_num)
theorem B8723861 : Blo 1072617 8723861 := bbase (se 6 (by rfl) ⟨204465, by rfl⟩ : syracuseStep 8723861 = 408931) (by norm_num)
theorem B9444757 : Blo 1072617 9444757 := bbase (se 6 (by rfl) ⟨221361, by rfl⟩ : syracuseStep 9444757 = 442723) (by norm_num)
theorem B1613213 : Blo 1072617 1613213 := bbase (se 3 (by rfl) ⟨302477, by rfl⟩ : syracuseStep 1613213 = 604955) (by norm_num)
theorem B1613237 : Blo 1072617 1613237 := bbase (se 5 (by rfl) ⟨75620, by rfl⟩ : syracuseStep 1613237 = 151241) (by norm_num)
theorem B1613261 : Blo 1072617 1613261 := bbase (se 3 (by rfl) ⟨302486, by rfl⟩ : syracuseStep 1613261 = 604973) (by norm_num)
theorem B1613285 : Blo 1072617 1613285 := bbase (se 4 (by rfl) ⟨151245, by rfl⟩ : syracuseStep 1613285 = 302491) (by norm_num)
theorem B1613309 : Blo 1072617 1613309 := bbase (se 3 (by rfl) ⟨302495, by rfl⟩ : syracuseStep 1613309 = 604991) (by norm_num)
theorem B1613333 : Blo 1072617 1613333 := bbase (se 6 (by rfl) ⟨37812, by rfl⟩ : syracuseStep 1613333 = 75625) (by norm_num)
theorem B1613357 : Blo 1072617 1613357 := bbase (se 3 (by rfl) ⟨302504, by rfl⟩ : syracuseStep 1613357 = 605009) (by norm_num)
theorem B1613381 : Blo 1072617 1613381 := bbase (se 4 (by rfl) ⟨151254, by rfl⟩ : syracuseStep 1613381 = 302509) (by norm_num)
theorem B1613405 : Blo 1072617 1613405 := bbase (se 3 (by rfl) ⟨302513, by rfl⟩ : syracuseStep 1613405 = 605027) (by norm_num)
theorem B3448421 : Blo 1072617 3448421 := bbase (se 4 (by rfl) ⟨323289, by rfl⟩ : syracuseStep 3448421 = 646579) (by norm_num)
theorem B1613429 : Blo 1072617 1613429 := bbase (se 5 (by rfl) ⟨75629, by rfl⟩ : syracuseStep 1613429 = 151259) (by norm_num)
theorem B1613453 : Blo 1072617 1613453 := bbase (se 3 (by rfl) ⟨302522, by rfl⟩ : syracuseStep 1613453 = 605045) (by norm_num)
theorem B1613477 : Blo 1072617 1613477 := bbase (se 4 (by rfl) ⟨151263, by rfl⟩ : syracuseStep 1613477 = 302527) (by norm_num)
theorem B1810093 : Blo 1072617 1810093 := bbase (se 3 (by rfl) ⟨339392, by rfl⟩ : syracuseStep 1810093 = 678785) (by norm_num)
theorem B1613501 : Blo 1072617 1613501 := bbase (se 3 (by rfl) ⟨302531, by rfl⟩ : syracuseStep 1613501 = 605063) (by norm_num)
theorem B1089221 : Blo 1072617 1089221 := bbase (se 4 (by rfl) ⟨102114, by rfl⟩ : syracuseStep 1089221 = 204229) (by norm_num)
theorem B1613525 : Blo 1072617 1613525 := bbase (se 7 (by rfl) ⟨18908, by rfl⟩ : syracuseStep 1613525 = 37817) (by norm_num)
theorem B1613549 : Blo 1072617 1613549 := bbase (se 3 (by rfl) ⟨302540, by rfl⟩ : syracuseStep 1613549 = 605081) (by norm_num)
theorem B1810181 : Blo 1072617 1810181 := bbase (se 4 (by rfl) ⟨169704, by rfl⟩ : syracuseStep 1810181 = 339409) (by norm_num)
theorem B1613573 : Blo 1072617 1613573 := bbase (se 4 (by rfl) ⟨151272, by rfl⟩ : syracuseStep 1613573 = 302545) (by norm_num)
theorem B1613597 : Blo 1072617 1613597 := bbase (se 3 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 1613597 = 605099) (by norm_num)
theorem B1613621 : Blo 1072617 1613621 := bbase (se 5 (by rfl) ⟨75638, by rfl⟩ : syracuseStep 1613621 = 151277) (by norm_num)
theorem B1613645 : Blo 1072617 1613645 := bbase (se 3 (by rfl) ⟨302558, by rfl⟩ : syracuseStep 1613645 = 605117) (by norm_num)
theorem B3055445 : Blo 1072617 3055445 := bbase (se 9 (by rfl) ⟨8951, by rfl⟩ : syracuseStep 3055445 = 17903) (by norm_num)
theorem B1613669 : Blo 1072617 1613669 := bbase (se 4 (by rfl) ⟨151281, by rfl⟩ : syracuseStep 1613669 = 302563) (by norm_num)
theorem B1613693 : Blo 1072617 1613693 := bbase (se 3 (by rfl) ⟨302567, by rfl⟩ : syracuseStep 1613693 = 605135) (by norm_num)
theorem B1810309 : Blo 1072617 1810309 := bbase (se 4 (by rfl) ⟨169716, by rfl⟩ : syracuseStep 1810309 = 339433) (by norm_num)
theorem B1613717 : Blo 1072617 1613717 := bbase (se 6 (by rfl) ⟨37821, by rfl⟩ : syracuseStep 1613717 = 75643) (by norm_num)
theorem B5447573 : Blo 1072617 5447573 := bbase (se 6 (by rfl) ⟨127677, by rfl⟩ : syracuseStep 5447573 = 255355) (by norm_num)
theorem B1089445 : Blo 1072617 1089445 := bbase (se 4 (by rfl) ⟨102135, by rfl⟩ : syracuseStep 1089445 = 204271) (by norm_num)
theorem B1613741 : Blo 1072617 1613741 := bbase (se 3 (by rfl) ⟨302576, by rfl⟩ : syracuseStep 1613741 = 605153) (by norm_num)
theorem B1613765 : Blo 1072617 1613765 := bbase (se 4 (by rfl) ⟨151290, by rfl⟩ : syracuseStep 1613765 = 302581) (by norm_num)
theorem B1810397 : Blo 1072617 1810397 := bbase (se 3 (by rfl) ⟨339449, by rfl⟩ : syracuseStep 1810397 = 678899) (by norm_num)
theorem B1613789 : Blo 1072617 1613789 := bbase (se 3 (by rfl) ⟨302585, by rfl⟩ : syracuseStep 1613789 = 605171) (by norm_num)
theorem B1548277 : Blo 1072617 1548277 := bbase (se 5 (by rfl) ⟨72575, by rfl⟩ : syracuseStep 1548277 = 145151) (by norm_num)
theorem B1613813 : Blo 1072617 1613813 := bbase (se 5 (by rfl) ⟨75647, by rfl⟩ : syracuseStep 1613813 = 151295) (by norm_num)
theorem B1613837 : Blo 1072617 1613837 := bbase (se 3 (by rfl) ⟨302594, by rfl⟩ : syracuseStep 1613837 = 605189) (by norm_num)
theorem B1613861 : Blo 1072617 1613861 := bbase (se 4 (by rfl) ⟨151299, by rfl⟩ : syracuseStep 1613861 = 302599) (by norm_num)
theorem B1613885 : Blo 1072617 1613885 := bbase (se 3 (by rfl) ⟨302603, by rfl⟩ : syracuseStep 1613885 = 605207) (by norm_num)
theorem B1613909 : Blo 1072617 1613909 := bbase (se 8 (by rfl) ⟨9456, by rfl⟩ : syracuseStep 1613909 = 18913) (by norm_num)
theorem B1810525 : Blo 1072617 1810525 := bbase (se 3 (by rfl) ⟨339473, by rfl⟩ : syracuseStep 1810525 = 678947) (by norm_num)
theorem B2039917 : Blo 1072617 2039917 := bbase (se 3 (by rfl) ⟨382484, by rfl⟩ : syracuseStep 2039917 = 764969) (by norm_num)
theorem B1613933 : Blo 1072617 1613933 := bbase (se 3 (by rfl) ⟨302612, by rfl⟩ : syracuseStep 1613933 = 605225) (by norm_num)
theorem B1613957 : Blo 1072617 1613957 := bbase (se 4 (by rfl) ⟨151308, by rfl⟩ : syracuseStep 1613957 = 302617) (by norm_num)
theorem B1613981 : Blo 1072617 1613981 := bbase (se 3 (by rfl) ⟨302621, by rfl⟩ : syracuseStep 1613981 = 605243) (by norm_num)
theorem B1810613 : Blo 1072617 1810613 := bbase (se 5 (by rfl) ⟨84872, by rfl⟩ : syracuseStep 1810613 = 169745) (by norm_num)
theorem B1614005 : Blo 1072617 1614005 := bbase (se 5 (by rfl) ⟨75656, by rfl⟩ : syracuseStep 1614005 = 151313) (by norm_num)
theorem B1745101 : Blo 1072617 1745101 := bbase (se 3 (by rfl) ⟨327206, by rfl⟩ : syracuseStep 1745101 = 654413) (by norm_num)
theorem B1614029 : Blo 1072617 1614029 := bbase (se 3 (by rfl) ⟨302630, by rfl⟩ : syracuseStep 1614029 = 605261) (by norm_num)
theorem B1614053 : Blo 1072617 1614053 := bbase (se 4 (by rfl) ⟨151317, by rfl⟩ : syracuseStep 1614053 = 302635) (by norm_num)
theorem B2040061 : Blo 1072617 2040061 := bbase (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) (by norm_num)
theorem B1614077 : Blo 1072617 1614077 := bbase (se 3 (by rfl) ⟨302639, by rfl⟩ : syracuseStep 1614077 = 605279) (by norm_num)
theorem B3055877 : Blo 1072617 3055877 := bbase (se 4 (by rfl) ⟨286488, by rfl⟩ : syracuseStep 3055877 = 572977) (by norm_num)
theorem B1614101 : Blo 1072617 1614101 := bbase (se 6 (by rfl) ⟨37830, by rfl⟩ : syracuseStep 1614101 = 75661) (by norm_num)
theorem B1614125 : Blo 1072617 1614125 := bbase (se 3 (by rfl) ⟨302648, by rfl⟩ : syracuseStep 1614125 = 605297) (by norm_num)
theorem B1810741 : Blo 1072617 1810741 := bbase (se 5 (by rfl) ⟨84878, by rfl⟩ : syracuseStep 1810741 = 169757) (by norm_num)
theorem B1614149 : Blo 1072617 1614149 := bbase (se 4 (by rfl) ⟨151326, by rfl⟩ : syracuseStep 1614149 = 302653) (by norm_num)
theorem B1614173 : Blo 1072617 1614173 := bbase (se 3 (by rfl) ⟨302657, by rfl⟩ : syracuseStep 1614173 = 605315) (by norm_num)
theorem B1614197 : Blo 1072617 1614197 := bbase (se 5 (by rfl) ⟨75665, by rfl⟩ : syracuseStep 1614197 = 151331) (by norm_num)
theorem B1810829 : Blo 1072617 1810829 := bbase (se 3 (by rfl) ⟨339530, by rfl⟩ : syracuseStep 1810829 = 679061) (by norm_num)
theorem B1614221 : Blo 1072617 1614221 := bbase (se 3 (by rfl) ⟨302666, by rfl⟩ : syracuseStep 1614221 = 605333) (by norm_num)
theorem B2040221 : Blo 1072617 2040221 := bbase (se 3 (by rfl) ⟨382541, by rfl⟩ : syracuseStep 2040221 = 765083) (by norm_num)
theorem B1614245 : Blo 1072617 1614245 := bbase (se 4 (by rfl) ⟨151335, by rfl⟩ : syracuseStep 1614245 = 302671) (by norm_num)
theorem B1614269 : Blo 1072617 1614269 := bbase (se 3 (by rfl) ⟨302675, by rfl⟩ : syracuseStep 1614269 = 605351) (by norm_num)
theorem B1614293 : Blo 1072617 1614293 := bbase (se 7 (by rfl) ⟨18917, by rfl⟩ : syracuseStep 1614293 = 37835) (by norm_num)
theorem B1614317 : Blo 1072617 1614317 := bbase (se 3 (by rfl) ⟨302684, by rfl⟩ : syracuseStep 1614317 = 605369) (by norm_num)
theorem B1614341 : Blo 1072617 1614341 := bbase (se 4 (by rfl) ⟨151344, by rfl⟩ : syracuseStep 1614341 = 302689) (by norm_num)
theorem B1810957 : Blo 1072617 1810957 := bbase (se 3 (by rfl) ⟨339554, by rfl⟩ : syracuseStep 1810957 = 679109) (by norm_num)
theorem B1614365 : Blo 1072617 1614365 := bbase (se 3 (by rfl) ⟨302693, by rfl⟩ : syracuseStep 1614365 = 605387) (by norm_num)
theorem B1090081 : Blo 1072617 1090081 := bbase (se 2 (by rfl) ⟨408780, by rfl⟩ : syracuseStep 1090081 = 817561) (by norm_num)
theorem B2040365 : Blo 1072617 2040365 := bbase (se 3 (by rfl) ⟨382568, by rfl⟩ : syracuseStep 2040365 = 765137) (by norm_num)
theorem B1614389 : Blo 1072617 1614389 := bbase (se 5 (by rfl) ⟨75674, by rfl⟩ : syracuseStep 1614389 = 151349) (by norm_num)
theorem B1614413 : Blo 1072617 1614413 := bbase (se 3 (by rfl) ⟨302702, by rfl⟩ : syracuseStep 1614413 = 605405) (by norm_num)
theorem B1811045 : Blo 1072617 1811045 := bbase (se 4 (by rfl) ⟨169785, by rfl⟩ : syracuseStep 1811045 = 339571) (by norm_num)
theorem B1614437 : Blo 1072617 1614437 := bbase (se 4 (by rfl) ⟨151353, by rfl⟩ : syracuseStep 1614437 = 302707) (by norm_num)
theorem B1614461 : Blo 1072617 1614461 := bbase (se 3 (by rfl) ⟨302711, by rfl⟩ : syracuseStep 1614461 = 605423) (by norm_num)
theorem B1614485 : Blo 1072617 1614485 := bbase (se 6 (by rfl) ⟨37839, by rfl⟩ : syracuseStep 1614485 = 75679) (by norm_num)
theorem B1614509 : Blo 1072617 1614509 := bbase (se 3 (by rfl) ⟨302720, by rfl⟩ : syracuseStep 1614509 = 605441) (by norm_num)
theorem B1614533 : Blo 1072617 1614533 := bbase (se 4 (by rfl) ⟨151362, by rfl⟩ : syracuseStep 1614533 = 302725) (by norm_num)
theorem B1614557 : Blo 1072617 1614557 := bbase (se 3 (by rfl) ⟨302729, by rfl⟩ : syracuseStep 1614557 = 605459) (by norm_num)
theorem B1811173 : Blo 1072617 1811173 := bbase (se 4 (by rfl) ⟨169797, by rfl⟩ : syracuseStep 1811173 = 339595) (by norm_num)
theorem B1614581 : Blo 1072617 1614581 := bbase (se 5 (by rfl) ⟨75683, by rfl⟩ : syracuseStep 1614581 = 151367) (by norm_num)
theorem B1614605 : Blo 1072617 1614605 := bbase (se 3 (by rfl) ⟨302738, by rfl⟩ : syracuseStep 1614605 = 605477) (by norm_num)
theorem B1614629 : Blo 1072617 1614629 := bbase (se 4 (by rfl) ⟨151371, by rfl⟩ : syracuseStep 1614629 = 302743) (by norm_num)
theorem B1811261 : Blo 1072617 1811261 := bbase (se 3 (by rfl) ⟨339611, by rfl⟩ : syracuseStep 1811261 = 679223) (by norm_num)
theorem B1614653 : Blo 1072617 1614653 := bbase (se 3 (by rfl) ⟨302747, by rfl⟩ : syracuseStep 1614653 = 605495) (by norm_num)
theorem B2040653 : Blo 1072617 2040653 := bbase (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) (by norm_num)
theorem B1614677 : Blo 1072617 1614677 := bbase (se 9 (by rfl) ⟨4730, by rfl⟩ : syracuseStep 1614677 = 9461) (by norm_num)
theorem B1614701 : Blo 1072617 1614701 := bbase (se 3 (by rfl) ⟨302756, by rfl⟩ : syracuseStep 1614701 = 605513) (by norm_num)
theorem B1614725 : Blo 1072617 1614725 := bbase (se 4 (by rfl) ⟨151380, by rfl⟩ : syracuseStep 1614725 = 302761) (by norm_num)
theorem B1614749 : Blo 1072617 1614749 := bbase (se 3 (by rfl) ⟨302765, by rfl⟩ : syracuseStep 1614749 = 605531) (by norm_num)
theorem B1614773 : Blo 1072617 1614773 := bbase (se 5 (by rfl) ⟨75692, by rfl⟩ : syracuseStep 1614773 = 151385) (by norm_num)
theorem B1811389 : Blo 1072617 1811389 := bbase (se 3 (by rfl) ⟨339635, by rfl⟩ : syracuseStep 1811389 = 679271) (by norm_num)
theorem B1614797 : Blo 1072617 1614797 := bbase (se 3 (by rfl) ⟨302774, by rfl⟩ : syracuseStep 1614797 = 605549) (by norm_num)
theorem B2040805 : Blo 1072617 2040805 := bbase (se 4 (by rfl) ⟨191325, by rfl⟩ : syracuseStep 2040805 = 382651) (by norm_num)
theorem B1614821 : Blo 1072617 1614821 := bbase (se 4 (by rfl) ⟨151389, by rfl⟩ : syracuseStep 1614821 = 302779) (by norm_num)
theorem B3056629 : Blo 1072617 3056629 := bbase (se 5 (by rfl) ⟨143279, by rfl⟩ : syracuseStep 3056629 = 286559) (by norm_num)
theorem B1614845 : Blo 1072617 1614845 := bbase (se 3 (by rfl) ⟨302783, by rfl⟩ : syracuseStep 1614845 = 605567) (by norm_num)
theorem B1811477 : Blo 1072617 1811477 := bbase (se 6 (by rfl) ⟨42456, by rfl⟩ : syracuseStep 1811477 = 84913) (by norm_num)
theorem B1614869 : Blo 1072617 1614869 := bbase (se 6 (by rfl) ⟨37848, by rfl⟩ : syracuseStep 1614869 = 75697) (by norm_num)
theorem B1614893 : Blo 1072617 1614893 := bbase (se 3 (by rfl) ⟨302792, by rfl⟩ : syracuseStep 1614893 = 605585) (by norm_num)
theorem B1614917 : Blo 1072617 1614917 := bbase (se 4 (by rfl) ⟨151398, by rfl⟩ : syracuseStep 1614917 = 302797) (by norm_num)
theorem B1811605 : Blo 1072617 1811605 := bbase (se 6 (by rfl) ⟨42459, by rfl⟩ : syracuseStep 1811605 = 84919) (by norm_num)
theorem B5448869 : Blo 1072617 5448869 := bbase (se 4 (by rfl) ⟨510831, by rfl⟩ : syracuseStep 5448869 = 1021663) (by norm_num)
theorem B1811693 : Blo 1072617 1811693 := bbase (se 3 (by rfl) ⟨339692, by rfl⟩ : syracuseStep 1811693 = 679385) (by norm_num)
theorem B2041109 : Blo 1072617 2041109 := bbase (se 6 (by rfl) ⟨47838, by rfl⟩ : syracuseStep 2041109 = 95677) (by norm_num)
theorem B1811821 : Blo 1072617 1811821 := bbase (se 3 (by rfl) ⟨339716, by rfl⟩ : syracuseStep 1811821 = 679433) (by norm_num)
theorem B3876245 : Blo 1072617 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B1811909 : Blo 1072617 1811909 := bbase (se 4 (by rfl) ⟨169866, by rfl⟩ : syracuseStep 1811909 = 339733) (by norm_num)
theorem B1812037 : Blo 1072617 1812037 := bbase (se 4 (by rfl) ⟨169878, by rfl⟩ : syracuseStep 1812037 = 339757) (by norm_num)
theorem B9184853 : Blo 1072617 9184853 := bbase (se 8 (by rfl) ⟨53817, by rfl⟩ : syracuseStep 9184853 = 107635) (by norm_num)
theorem B1812125 : Blo 1072617 1812125 := bbase (se 3 (by rfl) ⟨339773, by rfl⟩ : syracuseStep 1812125 = 679547) (by norm_num)
theorem B8169173 : Blo 1072617 8169173 := bbase (se 7 (by rfl) ⟨95732, by rfl⟩ : syracuseStep 8169173 = 191465) (by norm_num)
theorem B2041573 : Blo 1072617 2041573 := bbase (se 4 (by rfl) ⟨191397, by rfl⟩ : syracuseStep 2041573 = 382795) (by norm_num)
theorem B1812253 : Blo 1072617 1812253 := bbase (se 3 (by rfl) ⟨339797, by rfl⟩ : syracuseStep 1812253 = 679595) (by norm_num)
theorem B1812341 : Blo 1072617 1812341 := bbase (se 5 (by rfl) ⟨84953, by rfl⟩ : syracuseStep 1812341 = 169907) (by norm_num)
theorem B1812469 : Blo 1072617 1812469 := bbase (se 5 (by rfl) ⟨84959, by rfl⟩ : syracuseStep 1812469 = 169919) (by norm_num)
theorem B2041861 : Blo 1072617 2041861 := bbase (se 4 (by rfl) ⟨191424, by rfl⟩ : syracuseStep 2041861 = 382849) (by norm_num)
theorem B1812557 : Blo 1072617 1812557 := bbase (se 3 (by rfl) ⟨339854, by rfl⟩ : syracuseStep 1812557 = 679709) (by norm_num)
theorem B2042005 : Blo 1072617 2042005 := bbase (se 6 (by rfl) ⟨47859, by rfl⟩ : syracuseStep 2042005 = 95719) (by norm_num)
theorem B1812685 : Blo 1072617 1812685 := bbase (se 3 (by rfl) ⟨339878, by rfl⟩ : syracuseStep 1812685 = 679757) (by norm_num)
theorem B4892885 : Blo 1072617 4892885 := bbase (se 7 (by rfl) ⟨57338, by rfl⟩ : syracuseStep 4892885 = 114677) (by norm_num)
theorem B8726741 : Blo 1072617 8726741 := bbase (se 7 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 8726741 = 204533) (by norm_num)
theorem B1812773 : Blo 1072617 1812773 := bbase (se 4 (by rfl) ⟨169947, by rfl⟩ : syracuseStep 1812773 = 339895) (by norm_num)
theorem B2042165 : Blo 1072617 2042165 := bbase (se 5 (by rfl) ⟨95726, by rfl⟩ : syracuseStep 2042165 = 191453) (by norm_num)
theorem B1812901 : Blo 1072617 1812901 := bbase (se 4 (by rfl) ⟨169959, by rfl⟩ : syracuseStep 1812901 = 339919) (by norm_num)
theorem B5450165 : Blo 1072617 5450165 := bbase (se 5 (by rfl) ⟨255476, by rfl⟩ : syracuseStep 5450165 = 510953) (by norm_num)
theorem B2042309 : Blo 1072617 2042309 := bbase (se 4 (by rfl) ⟨191466, by rfl⟩ : syracuseStep 2042309 = 382933) (by norm_num)
theorem B1812989 : Blo 1072617 1812989 := bbase (se 3 (by rfl) ⟨339935, by rfl⟩ : syracuseStep 1812989 = 679871) (by norm_num)
theorem B1813117 : Blo 1072617 1813117 := bbase (se 3 (by rfl) ⟨339959, by rfl⟩ : syracuseStep 1813117 = 679919) (by norm_num)
theorem B1452749 : Blo 1072617 1452749 := bbase (se 3 (by rfl) ⟨272390, by rfl⟩ : syracuseStep 1452749 = 544781) (by norm_num)
theorem B1813205 : Blo 1072617 1813205 := bbase (se 7 (by rfl) ⟨21248, by rfl⟩ : syracuseStep 1813205 = 42497) (by norm_num)
theorem B2042597 : Blo 1072617 2042597 := bbase (se 4 (by rfl) ⟨191493, by rfl⟩ : syracuseStep 2042597 = 382987) (by norm_num)
theorem B4074245 : Blo 1072617 4074245 := bbase (se 4 (by rfl) ⟨381960, by rfl⟩ : syracuseStep 4074245 = 763921) (by norm_num)
theorem B1223473 : Blo 1072617 1223473 := bbase (se 2 (by rfl) ⟨458802, by rfl⟩ : syracuseStep 1223473 = 917605) (by norm_num)
theorem B1813333 : Blo 1072617 1813333 := bbase (se 9 (by rfl) ⟨5312, by rfl⟩ : syracuseStep 1813333 = 10625) (by norm_num)
theorem B2042749 : Blo 1072617 2042749 := bbase (se 3 (by rfl) ⟨383015, by rfl⟩ : syracuseStep 2042749 = 766031) (by norm_num)
theorem B1813421 : Blo 1072617 1813421 := bbase (se 3 (by rfl) ⟨340016, by rfl⟩ : syracuseStep 1813421 = 680033) (by norm_num)
theorem B19639253 : Blo 1072617 19639253 := bbase (se 7 (by rfl) ⟨230147, by rfl⟩ : syracuseStep 19639253 = 460295) (by norm_num)
theorem B1289233 : Blo 1072617 1289233 := bbase (se 2 (by rfl) ⟨483462, by rfl⟩ : syracuseStep 1289233 = 966925) (by norm_num)
theorem B4074533 : Blo 1072617 4074533 := bbase (se 4 (by rfl) ⟨381987, by rfl⟩ : syracuseStep 4074533 = 763975) (by norm_num)
theorem B1813549 : Blo 1072617 1813549 := bbase (se 3 (by rfl) ⟨340040, by rfl⟩ : syracuseStep 1813549 = 680081) (by norm_num)
theorem B1813637 : Blo 1072617 1813637 := bbase (se 4 (by rfl) ⟨170028, by rfl⟩ : syracuseStep 1813637 = 340057) (by norm_num)
theorem B2043053 : Blo 1072617 2043053 := bbase (se 3 (by rfl) ⟨383072, by rfl⟩ : syracuseStep 2043053 = 766145) (by norm_num)
theorem B1289425 : Blo 1072617 1289425 := bbase (se 2 (by rfl) ⟨483534, by rfl⟩ : syracuseStep 1289425 = 967069) (by norm_num)
theorem B1813765 : Blo 1072617 1813765 := bbase (se 4 (by rfl) ⟨170040, by rfl⟩ : syracuseStep 1813765 = 340081) (by norm_num)
theorem B1289525 : Blo 1072617 1289525 := bbase (se 5 (by rfl) ⟨60446, by rfl⟩ : syracuseStep 1289525 = 120893) (by norm_num)
theorem B1813853 : Blo 1072617 1813853 := bbase (se 3 (by rfl) ⟨340097, by rfl⟩ : syracuseStep 1813853 = 680195) (by norm_num)
theorem B1453501 : Blo 1072617 1453501 := bbase (se 3 (by rfl) ⟨272531, by rfl⟩ : syracuseStep 1453501 = 545063) (by norm_num)
theorem B1813981 : Blo 1072617 1813981 := bbase (se 3 (by rfl) ⟨340121, by rfl⟩ : syracuseStep 1813981 = 680243) (by norm_num)
theorem B1814069 : Blo 1072617 1814069 := bbase (se 5 (by rfl) ⟨85034, by rfl⟩ : syracuseStep 1814069 = 170069) (by norm_num)
theorem B1551949 : Blo 1072617 1551949 := bbase (se 3 (by rfl) ⟨290990, by rfl⟩ : syracuseStep 1551949 = 581981) (by norm_num)
theorem B1551973 : Blo 1072617 1551973 := bbase (se 4 (by rfl) ⟨145497, by rfl⟩ : syracuseStep 1551973 = 290995) (by norm_num)
theorem B1453717 : Blo 1072617 1453717 := bbase (se 6 (by rfl) ⟨34071, by rfl⟩ : syracuseStep 1453717 = 68143) (by norm_num)
theorem B1814197 : Blo 1072617 1814197 := bbase (se 5 (by rfl) ⟨85040, by rfl⟩ : syracuseStep 1814197 = 170081) (by norm_num)
theorem B1814285 : Blo 1072617 1814285 := bbase (se 3 (by rfl) ⟨340178, by rfl⟩ : syracuseStep 1814285 = 680357) (by norm_num)
theorem B3059477 : Blo 1072617 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B6893333 : Blo 1072617 6893333 := bbase (se 6 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 6893333 = 323125) (by norm_num)
theorem B3878725 : Blo 1072617 3878725 := bbase (se 4 (by rfl) ⟨363630, by rfl⟩ : syracuseStep 3878725 = 727261) (by norm_num)
theorem B1814413 : Blo 1072617 1814413 := bbase (se 3 (by rfl) ⟨340202, by rfl⟩ : syracuseStep 1814413 = 680405) (by norm_num)
theorem B2043805 : Blo 1072617 2043805 := bbase (se 3 (by rfl) ⟨383213, by rfl⟩ : syracuseStep 2043805 = 766427) (by norm_num)
theorem B1814501 : Blo 1072617 1814501 := bbase (se 4 (by rfl) ⟨170109, by rfl⟩ : syracuseStep 1814501 = 340219) (by norm_num)
theorem B1290313 : Blo 1072617 1290313 := bbase (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) (by norm_num)
theorem B1814629 : Blo 1072617 1814629 := bbase (se 4 (by rfl) ⟨170121, by rfl⟩ : syracuseStep 1814629 = 340243) (by norm_num)
theorem B1814717 : Blo 1072617 1814717 := bbase (se 3 (by rfl) ⟨340259, by rfl⟩ : syracuseStep 1814717 = 680519) (by norm_num)
theorem B4075717 : Blo 1072617 4075717 := bbase (se 4 (by rfl) ⟨382098, by rfl⟩ : syracuseStep 4075717 = 764197) (by norm_num)
theorem B1814845 : Blo 1072617 1814845 := bbase (se 3 (by rfl) ⟨340283, by rfl⟩ : syracuseStep 1814845 = 680567) (by norm_num)
theorem B1814933 : Blo 1072617 1814933 := bbase (se 6 (by rfl) ⟨42537, by rfl⟩ : syracuseStep 1814933 = 85075) (by norm_num)
theorem B4076021 : Blo 1072617 4076021 := bbase (se 5 (by rfl) ⟨191063, by rfl⟩ : syracuseStep 4076021 = 382127) (by norm_num)
theorem B9187829 : Blo 1072617 9187829 := bbase (se 5 (by rfl) ⟨430679, by rfl⟩ : syracuseStep 9187829 = 861359) (by norm_num)
theorem B1815061 : Blo 1072617 1815061 := bbase (se 6 (by rfl) ⟨42540, by rfl⟩ : syracuseStep 1815061 = 85081) (by norm_num)
theorem B1225301 : Blo 1072617 1225301 := bbase (se 8 (by rfl) ⟨7179, by rfl⟩ : syracuseStep 1225301 = 14359) (by norm_num)
theorem B1815149 : Blo 1072617 1815149 := bbase (se 3 (by rfl) ⟨340340, by rfl⟩ : syracuseStep 1815149 = 680681) (by norm_num)
theorem B2175653 : Blo 1072617 2175653 := bbase (se 4 (by rfl) ⟨203967, by rfl⟩ : syracuseStep 2175653 = 407935) (by norm_num)
theorem B1815277 : Blo 1072617 1815277 := bbase (se 3 (by rfl) ⟨340364, by rfl⟩ : syracuseStep 1815277 = 680729) (by norm_num)
theorem B1291025 : Blo 1072617 1291025 := bbase (se 2 (by rfl) ⟨484134, by rfl⟩ : syracuseStep 1291025 = 968269) (by norm_num)
theorem B1815365 : Blo 1072617 1815365 := bbase (se 4 (by rfl) ⟨170190, by rfl⟩ : syracuseStep 1815365 = 340381) (by norm_num)
theorem B3060661 : Blo 1072617 3060661 := bbase (se 5 (by rfl) ⟨143468, by rfl⟩ : syracuseStep 3060661 = 286937) (by norm_num)
theorem B1815493 : Blo 1072617 1815493 := bbase (se 4 (by rfl) ⟨170202, by rfl⟩ : syracuseStep 1815493 = 340405) (by norm_num)
theorem B1815581 : Blo 1072617 1815581 := bbase (se 3 (by rfl) ⟨340421, by rfl⟩ : syracuseStep 1815581 = 680843) (by norm_num)
theorem B3060821 : Blo 1072617 3060821 := bbase (se 8 (by rfl) ⟨17934, by rfl⟩ : syracuseStep 3060821 = 35869) (by norm_num)
theorem B1291361 : Blo 1072617 1291361 := bbase (se 2 (by rfl) ⟨484260, by rfl⟩ : syracuseStep 1291361 = 968521) (by norm_num)
theorem B1815709 : Blo 1072617 1815709 := bbase (se 3 (by rfl) ⟨340445, by rfl⟩ : syracuseStep 1815709 = 680891) (by norm_num)
theorem B1291477 : Blo 1072617 1291477 := bbase (se 7 (by rfl) ⟨15134, by rfl⟩ : syracuseStep 1291477 = 30269) (by norm_num)
theorem B1291501 : Blo 1072617 1291501 := bbase (se 3 (by rfl) ⟨242156, by rfl⟩ : syracuseStep 1291501 = 484313) (by norm_num)
theorem B1815797 : Blo 1072617 1815797 := bbase (se 5 (by rfl) ⟨85115, by rfl⟩ : syracuseStep 1815797 = 170231) (by norm_num)
theorem B1914149 : Blo 1072617 1914149 := bbase (se 4 (by rfl) ⟨179451, by rfl⟩ : syracuseStep 1914149 = 358903) (by norm_num)
theorem B3061061 : Blo 1072617 3061061 := bbase (se 4 (by rfl) ⟨286974, by rfl⟩ : syracuseStep 3061061 = 573949) (by norm_num)
theorem B1815925 : Blo 1072617 1815925 := bbase (se 5 (by rfl) ⟨85121, by rfl⟩ : syracuseStep 1815925 = 170243) (by norm_num)
theorem B1816013 : Blo 1072617 1816013 := bbase (se 3 (by rfl) ⟨340502, by rfl⟩ : syracuseStep 1816013 = 681005) (by norm_num)
theorem B1226209 : Blo 1072617 1226209 := bbase (se 2 (by rfl) ⟨459828, by rfl⟩ : syracuseStep 1226209 = 919657) (by norm_num)
theorem B3061253 : Blo 1072617 3061253 := bbase (se 4 (by rfl) ⟨286992, by rfl⟩ : syracuseStep 3061253 = 573985) (by norm_num)
theorem B5879317 : Blo 1072617 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B1816141 : Blo 1072617 1816141 := bbase (se 3 (by rfl) ⟨340526, by rfl⟩ : syracuseStep 1816141 = 681053) (by norm_num)
theorem B1226377 : Blo 1072617 1226377 := bbase (se 2 (by rfl) ⟨459891, by rfl⟩ : syracuseStep 1226377 = 919783) (by norm_num)
theorem B1816229 : Blo 1072617 1816229 := bbase (se 4 (by rfl) ⟨170271, by rfl⟩ : syracuseStep 1816229 = 340543) (by norm_num)
theorem B1816357 : Blo 1072617 1816357 := bbase (se 4 (by rfl) ⟨170283, by rfl⟩ : syracuseStep 1816357 = 340567) (by norm_num)
theorem B1357661 : Blo 1072617 1357661 := bbase (se 3 (by rfl) ⟨254561, by rfl⟩ : syracuseStep 1357661 = 509123) (by norm_num)
theorem B1816445 : Blo 1072617 1816445 := bbase (se 3 (by rfl) ⟨340583, by rfl⟩ : syracuseStep 1816445 = 681167) (by norm_num)
theorem B1357717 : Blo 1072617 1357717 := bbase (se 6 (by rfl) ⟨31821, by rfl⟩ : syracuseStep 1357717 = 63643) (by norm_num)
theorem B1292197 : Blo 1072617 1292197 := bbase (se 4 (by rfl) ⟨121143, by rfl⟩ : syracuseStep 1292197 = 242287) (by norm_num)
theorem B1357813 : Blo 1072617 1357813 := bbase (se 5 (by rfl) ⟨63647, by rfl⟩ : syracuseStep 1357813 = 127295) (by norm_num)
theorem B1816573 : Blo 1072617 1816573 := bbase (se 3 (by rfl) ⟨340607, by rfl⟩ : syracuseStep 1816573 = 681215) (by norm_num)
theorem B1292293 : Blo 1072617 1292293 := bbase (se 4 (by rfl) ⟨121152, by rfl⟩ : syracuseStep 1292293 = 242305) (by norm_num)
theorem B1226833 : Blo 1072617 1226833 := bbase (se 2 (by rfl) ⟨460062, by rfl⟩ : syracuseStep 1226833 = 920125) (by norm_num)
theorem B1816661 : Blo 1072617 1816661 := bbase (se 8 (by rfl) ⟨10644, by rfl⟩ : syracuseStep 1816661 = 21289) (by norm_num)
theorem B1357985 : Blo 1072617 1357985 := bbase (se 2 (by rfl) ⟨509244, by rfl⟩ : syracuseStep 1357985 = 1018489) (by norm_num)
theorem B1816789 : Blo 1072617 1816789 := bbase (se 7 (by rfl) ⟨21290, by rfl⟩ : syracuseStep 1816789 = 42581) (by norm_num)
theorem B1358041 : Blo 1072617 1358041 := bbase (se 2 (by rfl) ⟨509265, by rfl⟩ : syracuseStep 1358041 = 1018531) (by norm_num)
theorem B1358137 : Blo 1072617 1358137 := bbase (se 2 (by rfl) ⟨509301, by rfl⟩ : syracuseStep 1358137 = 1018603) (by norm_num)
theorem B11614549 : Blo 1072617 11614549 := bbase (se 10 (by rfl) ⟨17013, by rfl⟩ : syracuseStep 11614549 = 34027) (by norm_num)
theorem B1227125 : Blo 1072617 1227125 := bbase (se 5 (by rfl) ⟨57521, by rfl⟩ : syracuseStep 1227125 = 115043) (by norm_num)
theorem B5519765 : Blo 1072617 5519765 := bbase (se 6 (by rfl) ⟨129369, by rfl⟩ : syracuseStep 5519765 = 258739) (by norm_num)
theorem B1358309 : Blo 1072617 1358309 := bbase (se 4 (by rfl) ⟨127341, by rfl⟩ : syracuseStep 1358309 = 254683) (by norm_num)
theorem B3062245 : Blo 1072617 3062245 := bbase (se 4 (by rfl) ⟨287085, by rfl⟩ : syracuseStep 3062245 = 574171) (by norm_num)
theorem B1161745 : Blo 1072617 1161745 := bbase (se 2 (by rfl) ⟨435654, by rfl⟩ : syracuseStep 1161745 = 871309) (by norm_num)
theorem B1358365 : Blo 1072617 1358365 := bbase (se 3 (by rfl) ⟨254693, by rfl⟩ : syracuseStep 1358365 = 509387) (by norm_num)
theorem B4078133 : Blo 1072617 4078133 := bbase (se 5 (by rfl) ⟨191162, by rfl⟩ : syracuseStep 4078133 = 382325) (by norm_num)
theorem B1161797 : Blo 1072617 1161797 := bbase (se 4 (by rfl) ⟨108918, by rfl⟩ : syracuseStep 1161797 = 217837) (by norm_num)
theorem B1358461 : Blo 1072617 1358461 := bbase (se 3 (by rfl) ⟨254711, by rfl⟩ : syracuseStep 1358461 = 509423) (by norm_num)
theorem B1718957 : Blo 1072617 1718957 := bbase (se 3 (by rfl) ⟨322304, by rfl⟩ : syracuseStep 1718957 = 644609) (by norm_num)
theorem B1358633 : Blo 1072617 1358633 := bbase (se 2 (by rfl) ⟨509487, by rfl⟩ : syracuseStep 1358633 = 1018975) (by norm_num)
theorem B1719085 : Blo 1072617 1719085 := bbase (se 3 (by rfl) ⟨322328, by rfl⟩ : syracuseStep 1719085 = 644657) (by norm_num)
theorem B4078421 : Blo 1072617 4078421 := bbase (se 9 (by rfl) ⟨11948, by rfl⟩ : syracuseStep 4078421 = 23897) (by norm_num)
theorem B1358689 : Blo 1072617 1358689 := bbase (se 2 (by rfl) ⟨509508, by rfl⟩ : syracuseStep 1358689 = 1019017) (by norm_num)
theorem B1719149 : Blo 1072617 1719149 := bbase (se 3 (by rfl) ⟨322340, by rfl⟩ : syracuseStep 1719149 = 644681) (by norm_num)
theorem B7650229 : Blo 1072617 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B1358785 : Blo 1072617 1358785 := bbase (se 2 (by rfl) ⟨509544, by rfl⟩ : syracuseStep 1358785 = 1019089) (by norm_num)
theorem B1293293 : Blo 1072617 1293293 := bbase (se 3 (by rfl) ⟨242492, by rfl⟩ : syracuseStep 1293293 = 484985) (by norm_num)
theorem B1358957 : Blo 1072617 1358957 := bbase (se 3 (by rfl) ⟨254804, by rfl⟩ : syracuseStep 1358957 = 509609) (by norm_num)
theorem B1359013 : Blo 1072617 1359013 := bbase (se 4 (by rfl) ⟨127407, by rfl⟩ : syracuseStep 1359013 = 254815) (by norm_num)
theorem B1359109 : Blo 1072617 1359109 := bbase (se 4 (by rfl) ⟨127416, by rfl⟩ : syracuseStep 1359109 = 254833) (by norm_num)
theorem B3620213 : Blo 1072617 3620213 := bbase (se 5 (by rfl) ⟨169697, by rfl⟩ : syracuseStep 3620213 = 339395) (by norm_num)
theorem B1359281 : Blo 1072617 1359281 := bbase (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) (by norm_num)
theorem B1359337 : Blo 1072617 1359337 := bbase (se 2 (by rfl) ⟨509751, by rfl⟩ : syracuseStep 1359337 = 1019503) (by norm_num)
theorem B3063349 : Blo 1072617 3063349 := bbase (se 5 (by rfl) ⟨143594, by rfl⟩ : syracuseStep 3063349 = 287189) (by norm_num)
theorem B1359433 : Blo 1072617 1359433 := bbase (se 2 (by rfl) ⟨509787, by rfl⟩ : syracuseStep 1359433 = 1019575) (by norm_num)
theorem B1359605 : Blo 1072617 1359605 := bbase (se 5 (by rfl) ⟨63731, by rfl⟩ : syracuseStep 1359605 = 127463) (by norm_num)
theorem B3620645 : Blo 1072617 3620645 := bbase (se 4 (by rfl) ⟨339435, by rfl⟩ : syracuseStep 3620645 = 678871) (by norm_num)
theorem B1359661 : Blo 1072617 1359661 := bbase (se 3 (by rfl) ⟨254936, by rfl⟩ : syracuseStep 1359661 = 509873) (by norm_num)
theorem B5160773 : Blo 1072617 5160773 := bbase (se 4 (by rfl) ⟨483822, by rfl⟩ : syracuseStep 5160773 = 967645) (by norm_num)
theorem B6537077 : Blo 1072617 6537077 := bbase (se 5 (by rfl) ⟨306425, by rfl⟩ : syracuseStep 6537077 = 612851) (by norm_num)
theorem B1359757 : Blo 1072617 1359757 := bbase (se 3 (by rfl) ⟨254954, by rfl⟩ : syracuseStep 1359757 = 509909) (by norm_num)
theorem B4079605 : Blo 1072617 4079605 := bbase (se 5 (by rfl) ⟨191231, by rfl⟩ : syracuseStep 4079605 = 382463) (by norm_num)
theorem B11190325 : Blo 1072617 11190325 := bbase (se 5 (by rfl) ⟨524546, by rfl⟩ : syracuseStep 11190325 = 1049093) (by norm_num)
theorem B1359929 : Blo 1072617 1359929 := bbase (se 2 (by rfl) ⟨509973, by rfl⟩ : syracuseStep 1359929 = 1019947) (by norm_num)
theorem B1359985 : Blo 1072617 1359985 := bbase (se 2 (by rfl) ⟨509994, by rfl⟩ : syracuseStep 1359985 = 1019989) (by norm_num)
theorem B1720469 : Blo 1072617 1720469 := bbase (se 6 (by rfl) ⟨40323, by rfl⟩ : syracuseStep 1720469 = 80647) (by norm_num)
theorem B1360081 : Blo 1072617 1360081 := bbase (se 2 (by rfl) ⟨510030, by rfl⟩ : syracuseStep 1360081 = 1020061) (by norm_num)
theorem B3621077 : Blo 1072617 3621077 := bbase (se 7 (by rfl) ⟨42434, by rfl⟩ : syracuseStep 3621077 = 84869) (by norm_num)
theorem B1720597 : Blo 1072617 1720597 := bbase (se 6 (by rfl) ⟨40326, by rfl⟩ : syracuseStep 1720597 = 80653) (by norm_num)
theorem B4079909 : Blo 1072617 4079909 := bbase (se 4 (by rfl) ⟨382491, by rfl⟩ : syracuseStep 4079909 = 764983) (by norm_num)
theorem B1360253 : Blo 1072617 1360253 := bbase (se 3 (by rfl) ⟨255047, by rfl⟩ : syracuseStep 1360253 = 510095) (by norm_num)
theorem B1360309 : Blo 1072617 1360309 := bbase (se 5 (by rfl) ⟨63764, by rfl⟩ : syracuseStep 1360309 = 127529) (by norm_num)
theorem B5816789 : Blo 1072617 5816789 := bbase (se 7 (by rfl) ⟨68165, by rfl⟩ : syracuseStep 5816789 = 136331) (by norm_num)
theorem B15483413 : Blo 1072617 15483413 := bbase (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) (by norm_num)
theorem B1360405 : Blo 1072617 1360405 := bbase (se 6 (by rfl) ⟨31884, by rfl⟩ : syracuseStep 1360405 = 63769) (by norm_num)
theorem B3621509 : Blo 1072617 3621509 := bbase (se 4 (by rfl) ⟨339516, by rfl⟩ : syracuseStep 3621509 = 679033) (by norm_num)
theorem B1360577 : Blo 1072617 1360577 := bbase (se 2 (by rfl) ⟨510216, by rfl⟩ : syracuseStep 1360577 = 1020433) (by norm_num)
theorem B1360633 : Blo 1072617 1360633 := bbase (se 2 (by rfl) ⟨510237, by rfl⟩ : syracuseStep 1360633 = 1020475) (by norm_num)
theorem B1360729 : Blo 1072617 1360729 := bbase (se 2 (by rfl) ⟨510273, by rfl⟩ : syracuseStep 1360729 = 1020547) (by norm_num)
theorem B15516629 : Blo 1072617 15516629 := bbase (se 7 (by rfl) ⟨181835, by rfl⟩ : syracuseStep 15516629 = 363671) (by norm_num)
theorem B1360901 : Blo 1072617 1360901 := bbase (se 4 (by rfl) ⟨127584, by rfl⟩ : syracuseStep 1360901 = 255169) (by norm_num)
theorem B3064853 : Blo 1072617 3064853 := bbase (se 6 (by rfl) ⟨71832, by rfl⟩ : syracuseStep 3064853 = 143665) (by norm_num)
theorem B3621941 : Blo 1072617 3621941 := bbase (se 5 (by rfl) ⟨169778, by rfl⟩ : syracuseStep 3621941 = 339557) (by norm_num)
theorem B1721405 : Blo 1072617 1721405 := bbase (se 3 (by rfl) ⟨322763, by rfl⟩ : syracuseStep 1721405 = 645527) (by norm_num)
theorem B1360957 : Blo 1072617 1360957 := bbase (se 3 (by rfl) ⟨255179, by rfl⟩ : syracuseStep 1360957 = 510359) (by norm_num)
theorem B1361053 : Blo 1072617 1361053 := bbase (se 3 (by rfl) ⟨255197, by rfl⟩ : syracuseStep 1361053 = 510395) (by norm_num)
theorem B2180405 : Blo 1072617 2180405 := bbase (se 5 (by rfl) ⟨102206, by rfl⟩ : syracuseStep 2180405 = 204413) (by norm_num)
theorem B1361225 : Blo 1072617 1361225 := bbase (se 2 (by rfl) ⟨510459, by rfl⟩ : syracuseStep 1361225 = 1020919) (by norm_num)
theorem B1721693 : Blo 1072617 1721693 := bbase (se 3 (by rfl) ⟨322817, by rfl⟩ : syracuseStep 1721693 = 645635) (by norm_num)
theorem B1361281 : Blo 1072617 1361281 := bbase (se 2 (by rfl) ⟨510480, by rfl⟩ : syracuseStep 1361281 = 1020961) (by norm_num)
theorem B1361377 : Blo 1072617 1361377 := bbase (se 2 (by rfl) ⟨510516, by rfl⟩ : syracuseStep 1361377 = 1021033) (by norm_num)
theorem B3622373 : Blo 1072617 3622373 := bbase (se 4 (by rfl) ⟨339597, by rfl⟩ : syracuseStep 3622373 = 679195) (by norm_num)
theorem B1361549 : Blo 1072617 1361549 := bbase (se 3 (by rfl) ⟨255290, by rfl⟩ : syracuseStep 1361549 = 510581) (by norm_num)
theorem B1361605 : Blo 1072617 1361605 := bbase (se 4 (by rfl) ⟨127650, by rfl⟩ : syracuseStep 1361605 = 255301) (by norm_num)
theorem B1722109 : Blo 1072617 1722109 := bbase (se 3 (by rfl) ⟨322895, by rfl⟩ : syracuseStep 1722109 = 645791) (by norm_num)
theorem B1361701 : Blo 1072617 1361701 := bbase (se 4 (by rfl) ⟨127659, by rfl⟩ : syracuseStep 1361701 = 255319) (by norm_num)
theorem B3622805 : Blo 1072617 3622805 := bbase (se 6 (by rfl) ⟨84909, by rfl⟩ : syracuseStep 3622805 = 169819) (by norm_num)
theorem B1361873 : Blo 1072617 1361873 := bbase (se 2 (by rfl) ⟨510702, by rfl⟩ : syracuseStep 1361873 = 1021405) (by norm_num)
theorem B20662229 : Blo 1072617 20662229 := bbase (se 7 (by rfl) ⟨242135, by rfl⟩ : syracuseStep 20662229 = 484271) (by norm_num)
theorem B4900837 : Blo 1072617 4900837 := bbase (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) (by norm_num)
theorem B1361929 : Blo 1072617 1361929 := bbase (se 2 (by rfl) ⟨510723, by rfl⟩ : syracuseStep 1361929 = 1021447) (by norm_num)
theorem B1362025 : Blo 1072617 1362025 := bbase (se 2 (by rfl) ⟨510759, by rfl⟩ : syracuseStep 1362025 = 1021519) (by norm_num)
theorem B1394857 : Blo 1072617 1394857 := bbase (se 2 (by rfl) ⟨523071, by rfl⟩ : syracuseStep 1394857 = 1046143) (by norm_num)
theorem B1362197 : Blo 1072617 1362197 := bbase (se 6 (by rfl) ⟨31926, by rfl⟩ : syracuseStep 1362197 = 63853) (by norm_num)
theorem B3623237 : Blo 1072617 3623237 := bbase (se 4 (by rfl) ⟨339678, by rfl⟩ : syracuseStep 3623237 = 679357) (by norm_num)
theorem B1362253 : Blo 1072617 1362253 := bbase (se 3 (by rfl) ⟨255422, by rfl⟩ : syracuseStep 1362253 = 510845) (by norm_num)
theorem B4082021 : Blo 1072617 4082021 := bbase (se 4 (by rfl) ⟨382689, by rfl⟩ : syracuseStep 4082021 = 765379) (by norm_num)
theorem B1362349 : Blo 1072617 1362349 := bbase (se 3 (by rfl) ⟨255440, by rfl⟩ : syracuseStep 1362349 = 510881) (by norm_num)
theorem B1362521 : Blo 1072617 1362521 := bbase (se 2 (by rfl) ⟨510945, by rfl⟩ : syracuseStep 1362521 = 1021891) (by norm_num)
theorem B4082309 : Blo 1072617 4082309 := bbase (se 4 (by rfl) ⟨382716, by rfl⟩ : syracuseStep 4082309 = 765433) (by norm_num)
theorem B1362577 : Blo 1072617 1362577 := bbase (se 2 (by rfl) ⟨510966, by rfl⟩ : syracuseStep 1362577 = 1021933) (by norm_num)
theorem B1723045 : Blo 1072617 1723045 := bbase (se 4 (by rfl) ⟨161535, by rfl⟩ : syracuseStep 1723045 = 323071) (by norm_num)
theorem B3623669 : Blo 1072617 3623669 := bbase (se 5 (by rfl) ⟨169859, by rfl⟩ : syracuseStep 3623669 = 339719) (by norm_num)
theorem B8702741 : Blo 1072617 8702741 := bbase (se 6 (by rfl) ⟨203970, by rfl⟩ : syracuseStep 8702741 = 407941) (by norm_num)
theorem B8145845 : Blo 1072617 8145845 := bbase (se 5 (by rfl) ⟨381836, by rfl⟩ : syracuseStep 8145845 = 763673) (by norm_num)
theorem B2182133 : Blo 1072617 2182133 := bbase (se 5 (by rfl) ⟨102287, by rfl⟩ : syracuseStep 2182133 = 204575) (by norm_num)
theorem B2182157 : Blo 1072617 2182157 := bbase (se 3 (by rfl) ⟨409154, by rfl⟩ : syracuseStep 2182157 = 818309) (by norm_num)
theorem B3624101 : Blo 1072617 3624101 := bbase (se 4 (by rfl) ⟨339759, by rfl⟩ : syracuseStep 3624101 = 679519) (by norm_num)
theorem B9293237 : Blo 1072617 9293237 := bbase (se 5 (by rfl) ⟨435620, by rfl⟩ : syracuseStep 9293237 = 871241) (by norm_num)
theorem B3624533 : Blo 1072617 3624533 := bbase (se 8 (by rfl) ⟨21237, by rfl⟩ : syracuseStep 3624533 = 42475) (by norm_num)
theorem B3264149 : Blo 1072617 3264149 := bbase (se 6 (by rfl) ⟨76503, by rfl⟩ : syracuseStep 3264149 = 153007) (by norm_num)
theorem B4083493 : Blo 1072617 4083493 := bbase (se 4 (by rfl) ⟨382827, by rfl⟩ : syracuseStep 4083493 = 765655) (by norm_num)
theorem B1724237 : Blo 1072617 1724237 := bbase (se 3 (by rfl) ⟨323294, by rfl⟩ : syracuseStep 1724237 = 646589) (by norm_num)
theorem B5230565 : Blo 1072617 5230565 := bbase (se 4 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 5230565 = 980731) (by norm_num)
theorem B3624965 : Blo 1072617 3624965 := bbase (se 4 (by rfl) ⟨339840, by rfl⟩ : syracuseStep 3624965 = 679681) (by norm_num)
theorem B1724429 : Blo 1072617 1724429 := bbase (se 3 (by rfl) ⟨323330, by rfl⟩ : syracuseStep 1724429 = 646661) (by norm_num)
theorem B4083797 : Blo 1072617 4083797 := bbase (se 8 (by rfl) ⟨23928, by rfl⟩ : syracuseStep 4083797 = 47857) (by norm_num)
theorem B6115445 : Blo 1072617 6115445 := bbase (se 5 (by rfl) ⟨286661, by rfl⟩ : syracuseStep 6115445 = 573323) (by norm_num)
theorem B3920021 : Blo 1072617 3920021 := bbase (se 6 (by rfl) ⟨91875, by rfl⟩ : syracuseStep 3920021 = 183751) (by norm_num)
theorem B3625397 : Blo 1072617 3625397 := bbase (se 5 (by rfl) ⟨169940, by rfl⟩ : syracuseStep 3625397 = 339881) (by norm_num)
theorem B16536149 : Blo 1072617 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B2577205 : Blo 1072617 2577205 := bbase (se 5 (by rfl) ⟨120806, by rfl⟩ : syracuseStep 2577205 = 241613) (by norm_num)
theorem B1528645 : Blo 1072617 1528645 := bbase (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) (by norm_num)
theorem B3625829 : Blo 1072617 3625829 := bbase (se 4 (by rfl) ⟨339921, by rfl⟩ : syracuseStep 3625829 = 679843) (by norm_num)
theorem B2413421 : Blo 1072617 2413421 := bbase (se 3 (by rfl) ⟨452516, by rfl⟩ : syracuseStep 2413421 = 905033) (by norm_num)
theorem B2413493 : Blo 1072617 2413493 := bbase (se 5 (by rfl) ⟨113132, by rfl⟩ : syracuseStep 2413493 = 226265) (by norm_num)
theorem B5297125 : Blo 1072617 5297125 := bbase (se 4 (by rfl) ⟨496605, by rfl⟩ : syracuseStep 5297125 = 993211) (by norm_num)
theorem B2413565 : Blo 1072617 2413565 := bbase (se 3 (by rfl) ⟨452543, by rfl⟩ : syracuseStep 2413565 = 905087) (by norm_num)
theorem B2413637 : Blo 1072617 2413637 := bbase (se 4 (by rfl) ⟨226278, by rfl⟩ : syracuseStep 2413637 = 452557) (by norm_num)
theorem B2413709 : Blo 1072617 2413709 := bbase (se 3 (by rfl) ⟨452570, by rfl⟩ : syracuseStep 2413709 = 905141) (by norm_num)
theorem B2413781 : Blo 1072617 2413781 := bbase (se 7 (by rfl) ⟨28286, by rfl⟩ : syracuseStep 2413781 = 56573) (by norm_num)
theorem B4412645 : Blo 1072617 4412645 := bbase (se 4 (by rfl) ⟨413685, by rfl⟩ : syracuseStep 4412645 = 827371) (by norm_num)
theorem B3626261 : Blo 1072617 3626261 := bbase (se 6 (by rfl) ⟨84990, by rfl⟩ : syracuseStep 3626261 = 169981) (by norm_num)
theorem B2413853 : Blo 1072617 2413853 := bbase (se 3 (by rfl) ⟨452597, by rfl⟩ : syracuseStep 2413853 = 905195) (by norm_num)
theorem B2413925 : Blo 1072617 2413925 := bbase (se 4 (by rfl) ⟨226305, by rfl⟩ : syracuseStep 2413925 = 452611) (by norm_num)
theorem B2446733 : Blo 1072617 2446733 := bbase (se 3 (by rfl) ⟨458762, by rfl⟩ : syracuseStep 2446733 = 917525) (by norm_num)
theorem B1529237 : Blo 1072617 1529237 := bbase (se 6 (by rfl) ⟨35841, by rfl⟩ : syracuseStep 1529237 = 71683) (by norm_num)
theorem B2413997 : Blo 1072617 2413997 := bbase (se 3 (by rfl) ⟨452624, by rfl⟩ : syracuseStep 2413997 = 905249) (by norm_num)
theorem B1529317 : Blo 1072617 1529317 := bbase (se 4 (by rfl) ⟨143373, by rfl⟩ : syracuseStep 1529317 = 286747) (by norm_num)
theorem B2414069 : Blo 1072617 2414069 := bbase (se 5 (by rfl) ⟨113159, by rfl⟩ : syracuseStep 2414069 = 226319) (by norm_num)
theorem B2414141 : Blo 1072617 2414141 := bbase (se 3 (by rfl) ⟨452651, by rfl⟩ : syracuseStep 2414141 = 905303) (by norm_num)
theorem B2578013 : Blo 1072617 2578013 := bbase (se 3 (by rfl) ⟨483377, by rfl⟩ : syracuseStep 2578013 = 966755) (by norm_num)
theorem B1529437 : Blo 1072617 1529437 := bbase (se 3 (by rfl) ⟨286769, by rfl⟩ : syracuseStep 1529437 = 573539) (by norm_num)
theorem B2414213 : Blo 1072617 2414213 := bbase (se 4 (by rfl) ⟨226332, by rfl⟩ : syracuseStep 2414213 = 452665) (by norm_num)
theorem B5166773 : Blo 1072617 5166773 := bbase (se 5 (by rfl) ⟨242192, by rfl⟩ : syracuseStep 5166773 = 484385) (by norm_num)
theorem B1529533 : Blo 1072617 1529533 := bbase (se 3 (by rfl) ⟨286787, by rfl⟩ : syracuseStep 1529533 = 573575) (by norm_num)
theorem B3626693 : Blo 1072617 3626693 := bbase (se 4 (by rfl) ⟨340002, by rfl⟩ : syracuseStep 3626693 = 680005) (by norm_num)
theorem B2414285 : Blo 1072617 2414285 := bbase (se 3 (by rfl) ⟨452678, by rfl⟩ : syracuseStep 2414285 = 905357) (by norm_num)
theorem B2414357 : Blo 1072617 2414357 := bbase (se 6 (by rfl) ⟨56586, by rfl⟩ : syracuseStep 2414357 = 113173) (by norm_num)
theorem B2447165 : Blo 1072617 2447165 := bbase (se 3 (by rfl) ⟨458843, by rfl⟩ : syracuseStep 2447165 = 917687) (by norm_num)
theorem B2414429 : Blo 1072617 2414429 := bbase (se 3 (by rfl) ⟨452705, by rfl⟩ : syracuseStep 2414429 = 905411) (by norm_num)
theorem B2905973 : Blo 1072617 2905973 := bbase (se 5 (by rfl) ⟨136217, by rfl⟩ : syracuseStep 2905973 = 272435) (by norm_num)
theorem B2414501 : Blo 1072617 2414501 := bbase (se 4 (by rfl) ⟨226359, by rfl⟩ : syracuseStep 2414501 = 452719) (by norm_num)
theorem B2414573 : Blo 1072617 2414573 := bbase (se 3 (by rfl) ⟨452732, by rfl⟩ : syracuseStep 2414573 = 905465) (by norm_num)
theorem B2414645 : Blo 1072617 2414645 := bbase (se 5 (by rfl) ⟨113186, by rfl⟩ : syracuseStep 2414645 = 226373) (by norm_num)
theorem B3627125 : Blo 1072617 3627125 := bbase (se 5 (by rfl) ⟨170021, by rfl⟩ : syracuseStep 3627125 = 340043) (by norm_num)
theorem B2414717 : Blo 1072617 2414717 := bbase (se 3 (by rfl) ⟨452759, by rfl⟩ : syracuseStep 2414717 = 905519) (by norm_num)
theorem B4085909 : Blo 1072617 4085909 := bbase (se 6 (by rfl) ⟨95763, by rfl⟩ : syracuseStep 4085909 = 191527) (by norm_num)
theorem B1530029 : Blo 1072617 1530029 := bbase (se 3 (by rfl) ⟨286880, by rfl⟩ : syracuseStep 1530029 = 573761) (by norm_num)
theorem B2414789 : Blo 1072617 2414789 := bbase (se 4 (by rfl) ⟨226386, by rfl⟩ : syracuseStep 2414789 = 452773) (by norm_num)
theorem B9296117 : Blo 1072617 9296117 := bbase (se 5 (by rfl) ⟨435755, by rfl⟩ : syracuseStep 9296117 = 871511) (by norm_num)
theorem B2414861 : Blo 1072617 2414861 := bbase (se 3 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 2414861 = 905573) (by norm_num)
theorem B3266885 : Blo 1072617 3266885 := bbase (se 4 (by rfl) ⟨306270, by rfl⟩ : syracuseStep 3266885 = 612541) (by norm_num)
theorem B2414933 : Blo 1072617 2414933 := bbase (se 10 (by rfl) ⟨3537, by rfl⟩ : syracuseStep 2414933 = 7075) (by norm_num)
theorem B18340181 : Blo 1072617 18340181 := bbase (se 10 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 18340181 = 53731) (by norm_num)
theorem B2578781 : Blo 1072617 2578781 := bbase (se 3 (by rfl) ⟨483521, by rfl⟩ : syracuseStep 2578781 = 967043) (by norm_num)
theorem B7756181 : Blo 1072617 7756181 := bbase (se 6 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 7756181 = 363571) (by norm_num)
theorem B2415005 : Blo 1072617 2415005 := bbase (se 3 (by rfl) ⟨452813, by rfl⟩ : syracuseStep 2415005 = 905627) (by norm_num)
theorem B5233061 : Blo 1072617 5233061 := bbase (se 4 (by rfl) ⟨490599, by rfl⟩ : syracuseStep 5233061 = 981199) (by norm_num)
theorem B4086197 : Blo 1072617 4086197 := bbase (se 5 (by rfl) ⟨191540, by rfl⟩ : syracuseStep 4086197 = 383081) (by norm_num)
theorem B2415077 : Blo 1072617 2415077 := bbase (se 4 (by rfl) ⟨226413, by rfl⟩ : syracuseStep 2415077 = 452827) (by norm_num)
theorem B3627557 : Blo 1072617 3627557 := bbase (se 4 (by rfl) ⟨340083, by rfl⟩ : syracuseStep 3627557 = 680167) (by norm_num)
theorem B2415149 : Blo 1072617 2415149 := bbase (se 3 (by rfl) ⟨452840, by rfl⟩ : syracuseStep 2415149 = 905681) (by norm_num)
theorem B2415221 : Blo 1072617 2415221 := bbase (se 5 (by rfl) ⟨113213, by rfl⟩ : syracuseStep 2415221 = 226427) (by norm_num)
theorem B4414085 : Blo 1072617 4414085 := bbase (se 4 (by rfl) ⟨413820, by rfl⟩ : syracuseStep 4414085 = 827641) (by norm_num)
theorem B7756469 : Blo 1072617 7756469 := bbase (se 5 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 7756469 = 727169) (by norm_num)
theorem B2415293 : Blo 1072617 2415293 := bbase (se 3 (by rfl) ⟨452867, by rfl⟩ : syracuseStep 2415293 = 905735) (by norm_num)
theorem B1530581 : Blo 1072617 1530581 := bbase (se 7 (by rfl) ⟨17936, by rfl⟩ : syracuseStep 1530581 = 35873) (by norm_num)
theorem B2415365 : Blo 1072617 2415365 := bbase (se 4 (by rfl) ⟨226440, by rfl⟩ : syracuseStep 2415365 = 452881) (by norm_num)
theorem B2415437 : Blo 1072617 2415437 := bbase (se 3 (by rfl) ⟨452894, by rfl⟩ : syracuseStep 2415437 = 905789) (by norm_num)
theorem B3103573 : Blo 1072617 3103573 := bbase (se 9 (by rfl) ⟨9092, by rfl⟩ : syracuseStep 3103573 = 18185) (by norm_num)
theorem B2415509 : Blo 1072617 2415509 := bbase (se 6 (by rfl) ⟨56613, by rfl⟩ : syracuseStep 2415509 = 113227) (by norm_num)
theorem B3627989 : Blo 1072617 3627989 := bbase (se 7 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 3627989 = 85031) (by norm_num)
theorem B2415581 : Blo 1072617 2415581 := bbase (se 3 (by rfl) ⟨452921, by rfl⟩ : syracuseStep 2415581 = 905843) (by norm_num)
theorem B7461877 : Blo 1072617 7461877 := bbase (se 5 (by rfl) ⟨349775, by rfl⟩ : syracuseStep 7461877 = 699551) (by norm_num)
theorem B2415653 : Blo 1072617 2415653 := bbase (se 4 (by rfl) ⟨226467, by rfl⟩ : syracuseStep 2415653 = 452935) (by norm_num)
theorem B2415725 : Blo 1072617 2415725 := bbase (se 3 (by rfl) ⟨452948, by rfl⟩ : syracuseStep 2415725 = 905897) (by norm_num)
theorem B2415797 : Blo 1072617 2415797 := bbase (se 5 (by rfl) ⟨113240, by rfl⟩ : syracuseStep 2415797 = 226481) (by norm_num)
theorem B2415869 : Blo 1072617 2415869 := bbase (se 3 (by rfl) ⟨452975, by rfl⟩ : syracuseStep 2415869 = 905951) (by norm_num)
theorem B2415941 : Blo 1072617 2415941 := bbase (se 4 (by rfl) ⟨226494, by rfl⟩ : syracuseStep 2415941 = 452989) (by norm_num)
theorem B3628421 : Blo 1072617 3628421 := bbase (se 4 (by rfl) ⟨340164, by rfl⟩ : syracuseStep 3628421 = 680329) (by norm_num)
theorem B2416013 : Blo 1072617 2416013 := bbase (se 3 (by rfl) ⟨453002, by rfl⟩ : syracuseStep 2416013 = 906005) (by norm_num)
theorem B10345877 : Blo 1072617 10345877 := bbase (se 6 (by rfl) ⟨242481, by rfl⟩ : syracuseStep 10345877 = 484963) (by norm_num)
theorem B5430725 : Blo 1072617 5430725 := bbase (se 4 (by rfl) ⟨509130, by rfl⟩ : syracuseStep 5430725 = 1018261) (by norm_num)
theorem B1531333 : Blo 1072617 1531333 := bbase (se 4 (by rfl) ⟨143562, by rfl⟩ : syracuseStep 1531333 = 287125) (by norm_num)
theorem B2416085 : Blo 1072617 2416085 := bbase (se 7 (by rfl) ⟨28313, by rfl⟩ : syracuseStep 2416085 = 56627) (by norm_num)
theorem B2448917 : Blo 1072617 2448917 := bbase (se 6 (by rfl) ⟨57396, by rfl⟩ : syracuseStep 2448917 = 114793) (by norm_num)
theorem B2416157 : Blo 1072617 2416157 := bbase (se 3 (by rfl) ⟨453029, by rfl⟩ : syracuseStep 2416157 = 906059) (by norm_num)
theorem B5103173 : Blo 1072617 5103173 := bbase (se 4 (by rfl) ⟨478422, by rfl⟩ : syracuseStep 5103173 = 956845) (by norm_num)
theorem B4087381 : Blo 1072617 4087381 := bbase (se 8 (by rfl) ⟨23949, by rfl⟩ : syracuseStep 4087381 = 47899) (by norm_num)
theorem B2416229 : Blo 1072617 2416229 := bbase (se 4 (by rfl) ⟨226521, by rfl⟩ : syracuseStep 2416229 = 453043) (by norm_num)
theorem B2416301 : Blo 1072617 2416301 := bbase (se 3 (by rfl) ⟨453056, by rfl⟩ : syracuseStep 2416301 = 906113) (by norm_num)
theorem B1892045 : Blo 1072617 1892045 := bbase (se 3 (by rfl) ⟨354758, by rfl⟩ : syracuseStep 1892045 = 709517) (by norm_num)
theorem B2416373 : Blo 1072617 2416373 := bbase (se 5 (by rfl) ⟨113267, by rfl⟩ : syracuseStep 2416373 = 226535) (by norm_num)
theorem B3628853 : Blo 1072617 3628853 := bbase (se 5 (by rfl) ⟨170102, by rfl⟩ : syracuseStep 3628853 = 340205) (by norm_num)
theorem B2416445 : Blo 1072617 2416445 := bbase (se 3 (by rfl) ⟨453083, by rfl⟩ : syracuseStep 2416445 = 906167) (by norm_num)
theorem B88137557 : Blo 1072617 88137557 := bbase (se 9 (by rfl) ⟨258215, by rfl⟩ : syracuseStep 88137557 = 516431) (by norm_num)
theorem B2416517 : Blo 1072617 2416517 := bbase (se 4 (by rfl) ⟨226548, by rfl⟩ : syracuseStep 2416517 = 453097) (by norm_num)
theorem B4087685 : Blo 1072617 4087685 := bbase (se 4 (by rfl) ⟨383220, by rfl⟩ : syracuseStep 4087685 = 766441) (by norm_num)
theorem B7364501 : Blo 1072617 7364501 := bbase (se 6 (by rfl) ⟨172605, by rfl⟩ : syracuseStep 7364501 = 345211) (by norm_num)
theorem B2416589 : Blo 1072617 2416589 := bbase (se 3 (by rfl) ⟨453110, by rfl⟩ : syracuseStep 2416589 = 906221) (by norm_num)
theorem B2580493 : Blo 1072617 2580493 := bbase (se 3 (by rfl) ⟨483842, by rfl⟩ : syracuseStep 2580493 = 967685) (by norm_num)
theorem B2416661 : Blo 1072617 2416661 := bbase (se 6 (by rfl) ⟨56640, by rfl⟩ : syracuseStep 2416661 = 113281) (by norm_num)
theorem B83845205 : Blo 1072617 83845205 := bbase (se 8 (by rfl) ⟨491280, by rfl⟩ : syracuseStep 83845205 = 982561) (by norm_num)
theorem B2416733 : Blo 1072617 2416733 := bbase (se 3 (by rfl) ⟨453137, by rfl⟩ : syracuseStep 2416733 = 906275) (by norm_num)
theorem B2416805 : Blo 1072617 2416805 := bbase (se 4 (by rfl) ⟨226575, by rfl⟩ : syracuseStep 2416805 = 453151) (by norm_num)
theorem B1532125 : Blo 1072617 1532125 := bbase (se 3 (by rfl) ⟨287273, by rfl⟩ : syracuseStep 1532125 = 574547) (by norm_num)
theorem B3629285 : Blo 1072617 3629285 := bbase (se 4 (by rfl) ⟨340245, by rfl⟩ : syracuseStep 3629285 = 680491) (by norm_num)
theorem B2416877 : Blo 1072617 2416877 := bbase (se 3 (by rfl) ⟨453164, by rfl⟩ : syracuseStep 2416877 = 906329) (by norm_num)
theorem B2416949 : Blo 1072617 2416949 := bbase (se 5 (by rfl) ⟨113294, by rfl⟩ : syracuseStep 2416949 = 226589) (by norm_num)
theorem B2417021 : Blo 1072617 2417021 := bbase (se 3 (by rfl) ⟨453191, by rfl⟩ : syracuseStep 2417021 = 906383) (by norm_num)
theorem B2417093 : Blo 1072617 2417093 := bbase (se 4 (by rfl) ⟨226602, by rfl⟩ : syracuseStep 2417093 = 453205) (by norm_num)
theorem B2417165 : Blo 1072617 2417165 := bbase (se 3 (by rfl) ⟨453218, by rfl⟩ : syracuseStep 2417165 = 906437) (by norm_num)
theorem B1532461 : Blo 1072617 1532461 := bbase (se 3 (by rfl) ⟨287336, by rfl⟩ : syracuseStep 1532461 = 574673) (by norm_num)
theorem B3269173 : Blo 1072617 3269173 := bbase (se 5 (by rfl) ⟨153242, by rfl⟩ : syracuseStep 3269173 = 306485) (by norm_num)
theorem B2417237 : Blo 1072617 2417237 := bbase (se 8 (by rfl) ⟨14163, by rfl⟩ : syracuseStep 2417237 = 28327) (by norm_num)
theorem B2581109 : Blo 1072617 2581109 := bbase (se 5 (by rfl) ⟨120989, by rfl⟩ : syracuseStep 2581109 = 241979) (by norm_num)
theorem B2941589 : Blo 1072617 2941589 := bbase (se 6 (by rfl) ⟨68943, by rfl⟩ : syracuseStep 2941589 = 137887) (by norm_num)
theorem B3629717 : Blo 1072617 3629717 := bbase (se 6 (by rfl) ⟨85071, by rfl⟩ : syracuseStep 3629717 = 170143) (by norm_num)
theorem B2417309 : Blo 1072617 2417309 := bbase (se 3 (by rfl) ⟨453245, by rfl⟩ : syracuseStep 2417309 = 906491) (by norm_num)
theorem B5432021 : Blo 1072617 5432021 := bbase (se 7 (by rfl) ⟨63656, by rfl⟩ : syracuseStep 5432021 = 127313) (by norm_num)
theorem B2417381 : Blo 1072617 2417381 := bbase (se 4 (by rfl) ⟨226629, by rfl⟩ : syracuseStep 2417381 = 453259) (by norm_num)
theorem B1532677 : Blo 1072617 1532677 := bbase (se 4 (by rfl) ⟨143688, by rfl⟩ : syracuseStep 1532677 = 287377) (by norm_num)
theorem B2417453 : Blo 1072617 2417453 := bbase (se 3 (by rfl) ⟨453272, by rfl⟩ : syracuseStep 2417453 = 906545) (by norm_num)
theorem B2417525 : Blo 1072617 2417525 := bbase (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) (by norm_num)
theorem B2417597 : Blo 1072617 2417597 := bbase (se 3 (by rfl) ⟨453299, by rfl⟩ : syracuseStep 2417597 = 906599) (by norm_num)
theorem B2417669 : Blo 1072617 2417669 := bbase (se 4 (by rfl) ⟨226656, by rfl⟩ : syracuseStep 2417669 = 453313) (by norm_num)
theorem B2581541 : Blo 1072617 2581541 := bbase (se 4 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 2581541 = 484039) (by norm_num)
theorem B3630149 : Blo 1072617 3630149 := bbase (se 4 (by rfl) ⟨340326, by rfl⟩ : syracuseStep 3630149 = 680653) (by norm_num)
theorem B2417741 : Blo 1072617 2417741 := bbase (se 3 (by rfl) ⟨453326, by rfl⟩ : syracuseStep 2417741 = 906653) (by norm_num)
theorem B2417813 : Blo 1072617 2417813 := bbase (se 6 (by rfl) ⟨56667, by rfl⟩ : syracuseStep 2417813 = 113335) (by norm_num)
theorem B2450621 : Blo 1072617 2450621 := bbase (se 3 (by rfl) ⟨459491, by rfl⟩ : syracuseStep 2450621 = 918983) (by norm_num)
theorem B2417885 : Blo 1072617 2417885 := bbase (se 3 (by rfl) ⟨453353, by rfl⟩ : syracuseStep 2417885 = 906707) (by norm_num)
theorem B2450693 : Blo 1072617 2450693 := bbase (se 4 (by rfl) ⟨229752, by rfl⟩ : syracuseStep 2450693 = 459505) (by norm_num)
theorem B2417957 : Blo 1072617 2417957 := bbase (se 4 (by rfl) ⟨226683, by rfl⟩ : syracuseStep 2417957 = 453367) (by norm_num)
theorem B1795429 : Blo 1072617 1795429 := bbase (se 4 (by rfl) ⟨168321, by rfl⟩ : syracuseStep 1795429 = 336643) (by norm_num)
theorem B2418029 : Blo 1072617 2418029 := bbase (se 3 (by rfl) ⟨453380, by rfl⟩ : syracuseStep 2418029 = 906761) (by norm_num)
theorem B1860989 : Blo 1072617 1860989 := bbase (se 3 (by rfl) ⟨348935, by rfl⟩ : syracuseStep 1860989 = 697871) (by norm_num)
theorem B2418101 : Blo 1072617 2418101 := bbase (se 5 (by rfl) ⟨113348, by rfl⟩ : syracuseStep 2418101 = 226697) (by norm_num)
theorem B3630581 : Blo 1072617 3630581 := bbase (se 5 (by rfl) ⟨170183, by rfl⟩ : syracuseStep 3630581 = 340367) (by norm_num)
theorem B2418173 : Blo 1072617 2418173 := bbase (se 3 (by rfl) ⟨453407, by rfl⟩ : syracuseStep 2418173 = 906815) (by norm_num)
theorem B2451005 : Blo 1072617 2451005 := bbase (se 3 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 2451005 = 919127) (by norm_num)
theorem B2418245 : Blo 1072617 2418245 := bbase (se 4 (by rfl) ⟨226710, by rfl⟩ : syracuseStep 2418245 = 453421) (by norm_num)
theorem B2418317 : Blo 1072617 2418317 := bbase (se 3 (by rfl) ⟨453434, by rfl⟩ : syracuseStep 2418317 = 906869) (by norm_num)
theorem B2418389 : Blo 1072617 2418389 := bbase (se 7 (by rfl) ⟨28340, by rfl⟩ : syracuseStep 2418389 = 56681) (by norm_num)
theorem B2418461 : Blo 1072617 2418461 := bbase (se 3 (by rfl) ⟨453461, by rfl⟩ : syracuseStep 2418461 = 906923) (by norm_num)
theorem B2418533 : Blo 1072617 2418533 := bbase (se 4 (by rfl) ⟨226737, by rfl⟩ : syracuseStep 2418533 = 453475) (by norm_num)
theorem B3631013 : Blo 1072617 3631013 := bbase (se 4 (by rfl) ⟨340407, by rfl⟩ : syracuseStep 3631013 = 680815) (by norm_num)
theorem B2418605 : Blo 1072617 2418605 := bbase (se 3 (by rfl) ⟨453488, by rfl⟩ : syracuseStep 2418605 = 906977) (by norm_num)
theorem B5433317 : Blo 1072617 5433317 := bbase (se 4 (by rfl) ⟨509373, by rfl⟩ : syracuseStep 5433317 = 1018747) (by norm_num)
theorem B2418677 : Blo 1072617 2418677 := bbase (se 5 (by rfl) ⟨113375, by rfl⟩ : syracuseStep 2418677 = 226751) (by norm_num)
theorem B2418749 : Blo 1072617 2418749 := bbase (se 3 (by rfl) ⟨453515, by rfl⟩ : syracuseStep 2418749 = 907031) (by norm_num)
theorem B2418821 : Blo 1072617 2418821 := bbase (se 4 (by rfl) ⟨226764, by rfl⟩ : syracuseStep 2418821 = 453529) (by norm_num)
theorem B1632421 : Blo 1072617 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B2615485 : Blo 1072617 2615485 := bbase (se 3 (by rfl) ⟨490403, by rfl⟩ : syracuseStep 2615485 = 980807) (by norm_num)
theorem B2418893 : Blo 1072617 2418893 := bbase (se 3 (by rfl) ⟨453542, by rfl⟩ : syracuseStep 2418893 = 907085) (by norm_num)
theorem B2582741 : Blo 1072617 2582741 := bbase (se 7 (by rfl) ⟨30266, by rfl⟩ : syracuseStep 2582741 = 60533) (by norm_num)
theorem B2418965 : Blo 1072617 2418965 := bbase (se 6 (by rfl) ⟨56694, by rfl⟩ : syracuseStep 2418965 = 113389) (by norm_num)
theorem B3631445 : Blo 1072617 3631445 := bbase (se 10 (by rfl) ⟨5319, by rfl⟩ : syracuseStep 3631445 = 10639) (by norm_num)
theorem B2419037 : Blo 1072617 2419037 := bbase (se 3 (by rfl) ⟨453569, by rfl⟩ : syracuseStep 2419037 = 907139) (by norm_num)
theorem B2419109 : Blo 1072617 2419109 := bbase (se 4 (by rfl) ⟨226791, by rfl⟩ : syracuseStep 2419109 = 453583) (by norm_num)
theorem B1206697 : Blo 1072617 1206697 := bbase (se 2 (by rfl) ⟨452511, by rfl⟩ : syracuseStep 1206697 = 905023) (by norm_num)
theorem B1206733 : Blo 1072617 1206733 := bbase (se 3 (by rfl) ⟨226262, by rfl⟩ : syracuseStep 1206733 = 452525) (by norm_num)
theorem B5302741 : Blo 1072617 5302741 := bbase (se 7 (by rfl) ⟨62141, by rfl⟩ : syracuseStep 5302741 = 124283) (by norm_num)
theorem B2419181 : Blo 1072617 2419181 := bbase (se 3 (by rfl) ⟨453596, by rfl⟩ : syracuseStep 2419181 = 907193) (by norm_num)
theorem B1206769 : Blo 1072617 1206769 := bbase (se 2 (by rfl) ⟨452538, by rfl⟩ : syracuseStep 1206769 = 905077) (by norm_num)
theorem B1206805 : Blo 1072617 1206805 := bbase (se 6 (by rfl) ⟨28284, by rfl⟩ : syracuseStep 1206805 = 56569) (by norm_num)
theorem B8153621 : Blo 1072617 8153621 := bbase (se 6 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 8153621 = 382201) (by norm_num)
theorem B2419253 : Blo 1072617 2419253 := bbase (se 5 (by rfl) ⟨113402, by rfl⟩ : syracuseStep 2419253 = 226805) (by norm_num)
theorem B1206841 : Blo 1072617 1206841 := bbase (se 2 (by rfl) ⟨452565, by rfl⟩ : syracuseStep 1206841 = 905131) (by norm_num)
theorem B1206877 : Blo 1072617 1206877 := bbase (se 3 (by rfl) ⟨226289, by rfl⟩ : syracuseStep 1206877 = 452579) (by norm_num)
theorem B2419325 : Blo 1072617 2419325 := bbase (se 3 (by rfl) ⟨453623, by rfl⟩ : syracuseStep 2419325 = 907247) (by norm_num)
theorem B1206913 : Blo 1072617 1206913 := bbase (se 2 (by rfl) ⟨452592, by rfl⟩ : syracuseStep 1206913 = 905185) (by norm_num)
theorem B5171845 : Blo 1072617 5171845 := bbase (se 4 (by rfl) ⟨484860, by rfl⟩ : syracuseStep 5171845 = 969721) (by norm_num)
theorem B1206949 : Blo 1072617 1206949 := bbase (se 4 (by rfl) ⟨113151, by rfl⟩ : syracuseStep 1206949 = 226303) (by norm_num)
theorem B2419397 : Blo 1072617 2419397 := bbase (se 4 (by rfl) ⟨226818, by rfl⟩ : syracuseStep 2419397 = 453637) (by norm_num)
theorem B1206985 : Blo 1072617 1206985 := bbase (se 2 (by rfl) ⟨452619, by rfl⟩ : syracuseStep 1206985 = 905239) (by norm_num)
theorem B1207021 : Blo 1072617 1207021 := bbase (se 3 (by rfl) ⟨226316, by rfl⟩ : syracuseStep 1207021 = 452633) (by norm_num)
theorem B3631877 : Blo 1072617 3631877 := bbase (se 4 (by rfl) ⟨340488, by rfl⟩ : syracuseStep 3631877 = 680977) (by norm_num)
theorem B2419469 : Blo 1072617 2419469 := bbase (se 3 (by rfl) ⟨453650, by rfl⟩ : syracuseStep 2419469 = 907301) (by norm_num)
theorem B1207057 : Blo 1072617 1207057 := bbase (se 2 (by rfl) ⟨452646, by rfl⟩ : syracuseStep 1207057 = 905293) (by norm_num)
theorem B1207093 : Blo 1072617 1207093 := bbase (se 5 (by rfl) ⟨56582, by rfl⟩ : syracuseStep 1207093 = 113165) (by norm_num)
theorem B2419541 : Blo 1072617 2419541 := bbase (se 9 (by rfl) ⟨7088, by rfl⟩ : syracuseStep 2419541 = 14177) (by norm_num)
theorem B1207129 : Blo 1072617 1207129 := bbase (se 2 (by rfl) ⟨452673, by rfl⟩ : syracuseStep 1207129 = 905347) (by norm_num)
theorem B1207165 : Blo 1072617 1207165 := bbase (se 3 (by rfl) ⟨226343, by rfl⟩ : syracuseStep 1207165 = 452687) (by norm_num)
theorem B2419613 : Blo 1072617 2419613 := bbase (se 3 (by rfl) ⟨453677, by rfl⟩ : syracuseStep 2419613 = 907355) (by norm_num)
theorem B1207201 : Blo 1072617 1207201 := bbase (se 2 (by rfl) ⟨452700, by rfl⟩ : syracuseStep 1207201 = 905401) (by norm_num)
theorem B1207237 : Blo 1072617 1207237 := bbase (se 4 (by rfl) ⟨113178, by rfl⟩ : syracuseStep 1207237 = 226357) (by norm_num)
theorem B2452445 : Blo 1072617 2452445 := bbase (se 3 (by rfl) ⟨459833, by rfl⟩ : syracuseStep 2452445 = 919667) (by norm_num)
theorem B2419685 : Blo 1072617 2419685 := bbase (se 4 (by rfl) ⟨226845, by rfl⟩ : syracuseStep 2419685 = 453691) (by norm_num)
theorem B1207273 : Blo 1072617 1207273 := bbase (se 2 (by rfl) ⟨452727, by rfl⟩ : syracuseStep 1207273 = 905455) (by norm_num)
theorem B1207309 : Blo 1072617 1207309 := bbase (se 3 (by rfl) ⟨226370, by rfl⟩ : syracuseStep 1207309 = 452741) (by norm_num)
theorem B2419757 : Blo 1072617 2419757 := bbase (se 3 (by rfl) ⟨453704, by rfl⟩ : syracuseStep 2419757 = 907409) (by norm_num)
theorem B1207345 : Blo 1072617 1207345 := bbase (se 2 (by rfl) ⟨452754, by rfl⟩ : syracuseStep 1207345 = 905509) (by norm_num)
theorem B1207381 : Blo 1072617 1207381 := bbase (se 8 (by rfl) ⟨7074, by rfl⟩ : syracuseStep 1207381 = 14149) (by norm_num)
theorem B2419829 : Blo 1072617 2419829 := bbase (se 5 (by rfl) ⟨113429, by rfl⟩ : syracuseStep 2419829 = 226859) (by norm_num)
theorem B1207417 : Blo 1072617 1207417 := bbase (se 2 (by rfl) ⟨452781, by rfl⟩ : syracuseStep 1207417 = 905563) (by norm_num)
theorem B1207453 : Blo 1072617 1207453 := bbase (se 3 (by rfl) ⟨226397, by rfl⟩ : syracuseStep 1207453 = 452795) (by norm_num)
theorem B3632309 : Blo 1072617 3632309 := bbase (se 5 (by rfl) ⟨170264, by rfl⟩ : syracuseStep 3632309 = 340529) (by norm_num)
theorem B2419901 : Blo 1072617 2419901 := bbase (se 3 (by rfl) ⟨453731, by rfl⟩ : syracuseStep 2419901 = 907463) (by norm_num)
theorem B1207489 : Blo 1072617 1207489 := bbase (se 2 (by rfl) ⟨452808, by rfl⟩ : syracuseStep 1207489 = 905617) (by norm_num)
theorem B1207525 : Blo 1072617 1207525 := bbase (se 4 (by rfl) ⟨113205, by rfl⟩ : syracuseStep 1207525 = 226411) (by norm_num)
theorem B5434613 : Blo 1072617 5434613 := bbase (se 5 (by rfl) ⟨254747, by rfl⟩ : syracuseStep 5434613 = 509495) (by norm_num)
theorem B2419973 : Blo 1072617 2419973 := bbase (se 4 (by rfl) ⟨226872, by rfl⟩ : syracuseStep 2419973 = 453745) (by norm_num)
theorem B1207561 : Blo 1072617 1207561 := bbase (se 2 (by rfl) ⟨452835, by rfl⟩ : syracuseStep 1207561 = 905671) (by norm_num)
theorem B1207597 : Blo 1072617 1207597 := bbase (se 3 (by rfl) ⟨226424, by rfl⟩ : syracuseStep 1207597 = 452849) (by norm_num)
theorem B9301301 : Blo 1072617 9301301 := bbase (se 5 (by rfl) ⟨435998, by rfl⟩ : syracuseStep 9301301 = 871997) (by norm_num)
theorem B2420045 : Blo 1072617 2420045 := bbase (se 3 (by rfl) ⟨453758, by rfl⟩ : syracuseStep 2420045 = 907517) (by norm_num)
theorem B1207633 : Blo 1072617 1207633 := bbase (se 2 (by rfl) ⟨452862, by rfl⟩ : syracuseStep 1207633 = 905725) (by norm_num)
theorem B4582757 : Blo 1072617 4582757 := bbase (se 4 (by rfl) ⟨429633, by rfl⟩ : syracuseStep 4582757 = 859267) (by norm_num)
theorem B1633637 : Blo 1072617 1633637 := bbase (se 4 (by rfl) ⟨153153, by rfl⟩ : syracuseStep 1633637 = 306307) (by norm_num)
theorem B1207669 : Blo 1072617 1207669 := bbase (se 5 (by rfl) ⟨56609, by rfl⟩ : syracuseStep 1207669 = 113219) (by norm_num)
theorem B2420117 : Blo 1072617 2420117 := bbase (se 6 (by rfl) ⟨56721, by rfl⟩ : syracuseStep 2420117 = 113443) (by norm_num)
theorem B1207705 : Blo 1072617 1207705 := bbase (se 2 (by rfl) ⟨452889, by rfl⟩ : syracuseStep 1207705 = 905779) (by norm_num)
theorem B1469869 : Blo 1072617 1469869 := bbase (se 3 (by rfl) ⟨275600, by rfl⟩ : syracuseStep 1469869 = 551201) (by norm_num)
theorem B1207741 : Blo 1072617 1207741 := bbase (se 3 (by rfl) ⟨226451, by rfl⟩ : syracuseStep 1207741 = 452903) (by norm_num)
theorem B2420189 : Blo 1072617 2420189 := bbase (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) (by norm_num)
theorem B1207777 : Blo 1072617 1207777 := bbase (se 2 (by rfl) ⟨452916, by rfl⟩ : syracuseStep 1207777 = 905833) (by norm_num)
theorem B1207813 : Blo 1072617 1207813 := bbase (se 4 (by rfl) ⟨113232, by rfl⟩ : syracuseStep 1207813 = 226465) (by norm_num)
theorem B2420261 : Blo 1072617 2420261 := bbase (se 4 (by rfl) ⟨226899, by rfl⟩ : syracuseStep 2420261 = 453799) (by norm_num)
theorem B1207849 : Blo 1072617 1207849 := bbase (se 2 (by rfl) ⟨452943, by rfl⟩ : syracuseStep 1207849 = 905887) (by norm_num)
theorem B1207885 : Blo 1072617 1207885 := bbase (se 3 (by rfl) ⟨226478, by rfl⟩ : syracuseStep 1207885 = 452957) (by norm_num)
theorem B2715221 : Blo 1072617 2715221 := bbase (se 8 (by rfl) ⟨15909, by rfl⟩ : syracuseStep 2715221 = 31819) (by norm_num)
theorem B3632741 : Blo 1072617 3632741 := bbase (se 4 (by rfl) ⟨340569, by rfl⟩ : syracuseStep 3632741 = 681139) (by norm_num)
theorem B2420333 : Blo 1072617 2420333 := bbase (se 3 (by rfl) ⟨453812, by rfl⟩ : syracuseStep 2420333 = 907625) (by norm_num)
theorem B1207921 : Blo 1072617 1207921 := bbase (se 2 (by rfl) ⟨452970, by rfl⟩ : syracuseStep 1207921 = 905941) (by norm_num)
theorem B1207957 : Blo 1072617 1207957 := bbase (se 6 (by rfl) ⟨28311, by rfl⟩ : syracuseStep 1207957 = 56623) (by norm_num)
theorem B2420405 : Blo 1072617 2420405 := bbase (se 5 (by rfl) ⟨113456, by rfl⟩ : syracuseStep 2420405 = 226913) (by norm_num)
theorem B1207993 : Blo 1072617 1207993 := bbase (se 2 (by rfl) ⟨452997, by rfl⟩ : syracuseStep 1207993 = 905995) (by norm_num)
theorem B1208029 : Blo 1072617 1208029 := bbase (se 3 (by rfl) ⟨226505, by rfl⟩ : syracuseStep 1208029 = 453011) (by norm_num)
theorem B2420477 : Blo 1072617 2420477 := bbase (se 3 (by rfl) ⟨453839, by rfl⟩ : syracuseStep 2420477 = 907679) (by norm_num)
theorem B1208065 : Blo 1072617 1208065 := bbase (se 2 (by rfl) ⟨453024, by rfl⟩ : syracuseStep 1208065 = 906049) (by norm_num)
theorem B1208101 : Blo 1072617 1208101 := bbase (se 4 (by rfl) ⟨113259, by rfl⟩ : syracuseStep 1208101 = 226519) (by norm_num)
theorem B2322245 : Blo 1072617 2322245 := bbase (se 4 (by rfl) ⟨217710, by rfl⟩ : syracuseStep 2322245 = 435421) (by norm_num)
theorem B2420549 : Blo 1072617 2420549 := bbase (se 4 (by rfl) ⟨226926, by rfl⟩ : syracuseStep 2420549 = 453853) (by norm_num)
theorem B1208137 : Blo 1072617 1208137 := bbase (se 2 (by rfl) ⟨453051, by rfl⟩ : syracuseStep 1208137 = 906103) (by norm_num)
theorem B1208173 : Blo 1072617 1208173 := bbase (se 3 (by rfl) ⟨226532, by rfl⟩ : syracuseStep 1208173 = 453065) (by norm_num)
theorem B2420621 : Blo 1072617 2420621 := bbase (se 3 (by rfl) ⟨453866, by rfl⟩ : syracuseStep 2420621 = 907733) (by norm_num)
theorem B1208209 : Blo 1072617 1208209 := bbase (se 2 (by rfl) ⟨453078, by rfl⟩ : syracuseStep 1208209 = 906157) (by norm_num)
theorem B2715565 : Blo 1072617 2715565 := bbase (se 3 (by rfl) ⟨509168, by rfl⟩ : syracuseStep 2715565 = 1018337) (by norm_num)
theorem B1208245 : Blo 1072617 1208245 := bbase (se 5 (by rfl) ⟨56636, by rfl⟩ : syracuseStep 1208245 = 113273) (by norm_num)
theorem B2420693 : Blo 1072617 2420693 := bbase (se 7 (by rfl) ⟨28367, by rfl⟩ : syracuseStep 2420693 = 56735) (by norm_num)
theorem B1208281 : Blo 1072617 1208281 := bbase (se 2 (by rfl) ⟨453105, by rfl⟩ : syracuseStep 1208281 = 906211) (by norm_num)
theorem B6123509 : Blo 1072617 6123509 := bbase (se 5 (by rfl) ⟨287039, by rfl⟩ : syracuseStep 6123509 = 574079) (by norm_num)
theorem B1208317 : Blo 1072617 1208317 := bbase (se 3 (by rfl) ⟨226559, by rfl⟩ : syracuseStep 1208317 = 453119) (by norm_num)
theorem B3633173 : Blo 1072617 3633173 := bbase (se 6 (by rfl) ⟨85152, by rfl⟩ : syracuseStep 3633173 = 170305) (by norm_num)
theorem B2715677 : Blo 1072617 2715677 := bbase (se 3 (by rfl) ⟨509189, by rfl⟩ : syracuseStep 2715677 = 1018379) (by norm_num)
theorem B2420765 : Blo 1072617 2420765 := bbase (se 3 (by rfl) ⟨453893, by rfl⟩ : syracuseStep 2420765 = 907787) (by norm_num)
theorem B1208353 : Blo 1072617 1208353 := bbase (se 2 (by rfl) ⟨453132, by rfl⟩ : syracuseStep 1208353 = 906265) (by norm_num)
theorem B1208389 : Blo 1072617 1208389 := bbase (se 4 (by rfl) ⟨113286, by rfl⟩ : syracuseStep 1208389 = 226573) (by norm_num)
theorem B2420837 : Blo 1072617 2420837 := bbase (se 4 (by rfl) ⟨226953, by rfl⟩ : syracuseStep 2420837 = 453907) (by norm_num)
theorem B1208425 : Blo 1072617 1208425 := bbase (se 2 (by rfl) ⟨453159, by rfl⟩ : syracuseStep 1208425 = 906319) (by norm_num)
theorem B1208461 : Blo 1072617 1208461 := bbase (se 3 (by rfl) ⟨226586, by rfl⟩ : syracuseStep 1208461 = 453173) (by norm_num)
theorem B2420909 : Blo 1072617 2420909 := bbase (se 3 (by rfl) ⟨453920, by rfl⟩ : syracuseStep 2420909 = 907841) (by norm_num)
theorem B1208497 : Blo 1072617 1208497 := bbase (se 2 (by rfl) ⟨453186, by rfl⟩ : syracuseStep 1208497 = 906373) (by norm_num)
theorem B2519221 : Blo 1072617 2519221 := bbase (se 5 (by rfl) ⟨118088, by rfl⟩ : syracuseStep 2519221 = 236177) (by norm_num)
theorem B1208533 : Blo 1072617 1208533 := bbase (se 7 (by rfl) ⟨14162, by rfl⟩ : syracuseStep 1208533 = 28325) (by norm_num)
theorem B2715869 : Blo 1072617 2715869 := bbase (se 3 (by rfl) ⟨509225, by rfl⟩ : syracuseStep 2715869 = 1018451) (by norm_num)
theorem B2355437 : Blo 1072617 2355437 := bbase (se 3 (by rfl) ⟨441644, by rfl⟩ : syracuseStep 2355437 = 883289) (by norm_num)
theorem B2420981 : Blo 1072617 2420981 := bbase (se 5 (by rfl) ⟨113483, by rfl⟩ : syracuseStep 2420981 = 226967) (by norm_num)
theorem B1208569 : Blo 1072617 1208569 := bbase (se 2 (by rfl) ⟨453213, by rfl⟩ : syracuseStep 1208569 = 906427) (by norm_num)
theorem B1208605 : Blo 1072617 1208605 := bbase (se 3 (by rfl) ⟨226613, by rfl⟩ : syracuseStep 1208605 = 453227) (by norm_num)
theorem B2421053 : Blo 1072617 2421053 := bbase (se 3 (by rfl) ⟨453947, by rfl⟩ : syracuseStep 2421053 = 907895) (by norm_num)
theorem B1208641 : Blo 1072617 1208641 := bbase (se 2 (by rfl) ⟨453240, by rfl⟩ : syracuseStep 1208641 = 906481) (by norm_num)
theorem B1208677 : Blo 1072617 1208677 := bbase (se 4 (by rfl) ⟨113313, by rfl⟩ : syracuseStep 1208677 = 226627) (by norm_num)
theorem B2421125 : Blo 1072617 2421125 := bbase (se 4 (by rfl) ⟨226980, by rfl⟩ : syracuseStep 2421125 = 453961) (by norm_num)
theorem B1208713 : Blo 1072617 1208713 := bbase (se 2 (by rfl) ⟨453267, by rfl⟩ : syracuseStep 1208713 = 906535) (by norm_num)
theorem B1208749 : Blo 1072617 1208749 := bbase (se 3 (by rfl) ⟨226640, by rfl⟩ : syracuseStep 1208749 = 453281) (by norm_num)
theorem B2585029 : Blo 1072617 2585029 := bbase (se 4 (by rfl) ⟨242346, by rfl⟩ : syracuseStep 2585029 = 484693) (by norm_num)
theorem B2421197 : Blo 1072617 2421197 := bbase (se 3 (by rfl) ⟨453974, by rfl⟩ : syracuseStep 2421197 = 907949) (by norm_num)
theorem B1208785 : Blo 1072617 1208785 := bbase (se 2 (by rfl) ⟨453294, by rfl⟩ : syracuseStep 1208785 = 906589) (by norm_num)
theorem B1208821 : Blo 1072617 1208821 := bbase (se 5 (by rfl) ⟨56663, by rfl⟩ : syracuseStep 1208821 = 113327) (by norm_num)
theorem B5435909 : Blo 1072617 5435909 := bbase (se 4 (by rfl) ⟨509616, by rfl⟩ : syracuseStep 5435909 = 1019233) (by norm_num)
theorem B2421269 : Blo 1072617 2421269 := bbase (se 6 (by rfl) ⟨56748, by rfl⟩ : syracuseStep 2421269 = 113497) (by norm_num)
theorem B1208857 : Blo 1072617 1208857 := bbase (se 2 (by rfl) ⟨453321, by rfl⟩ : syracuseStep 1208857 = 906643) (by norm_num)
theorem B3437093 : Blo 1072617 3437093 := bbase (se 4 (by rfl) ⟨322227, by rfl⟩ : syracuseStep 3437093 = 644455) (by norm_num)
theorem B2585125 : Blo 1072617 2585125 := bbase (se 4 (by rfl) ⟨242355, by rfl⟩ : syracuseStep 2585125 = 484711) (by norm_num)
theorem B2716213 : Blo 1072617 2716213 := bbase (se 5 (by rfl) ⟨127322, by rfl⟩ : syracuseStep 2716213 = 254645) (by norm_num)
theorem B1208893 : Blo 1072617 1208893 := bbase (se 3 (by rfl) ⟨226667, by rfl⟩ : syracuseStep 1208893 = 453335) (by norm_num)
theorem B9433685 : Blo 1072617 9433685 := bbase (se 8 (by rfl) ⟨55275, by rfl⟩ : syracuseStep 9433685 = 110551) (by norm_num)
theorem B2421341 : Blo 1072617 2421341 := bbase (se 3 (by rfl) ⟨454001, by rfl⟩ : syracuseStep 2421341 = 908003) (by norm_num)
theorem B1208929 : Blo 1072617 1208929 := bbase (se 2 (by rfl) ⟨453348, by rfl⟩ : syracuseStep 1208929 = 906697) (by norm_num)
theorem B1208965 : Blo 1072617 1208965 := bbase (se 4 (by rfl) ⟨113340, by rfl⟩ : syracuseStep 1208965 = 226681) (by norm_num)
theorem B2323109 : Blo 1072617 2323109 := bbase (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) (by norm_num)
theorem B2716325 : Blo 1072617 2716325 := bbase (se 4 (by rfl) ⟨254655, by rfl⟩ : syracuseStep 2716325 = 509311) (by norm_num)
theorem B2421413 : Blo 1072617 2421413 := bbase (se 4 (by rfl) ⟨227007, by rfl⟩ : syracuseStep 2421413 = 454015) (by norm_num)
theorem B1209001 : Blo 1072617 1209001 := bbase (se 2 (by rfl) ⟨453375, by rfl⟩ : syracuseStep 1209001 = 906751) (by norm_num)
theorem B1209037 : Blo 1072617 1209037 := bbase (se 3 (by rfl) ⟨226694, by rfl⟩ : syracuseStep 1209037 = 453389) (by norm_num)
theorem B2585317 : Blo 1072617 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B2421485 : Blo 1072617 2421485 := bbase (se 3 (by rfl) ⟨454028, by rfl⟩ : syracuseStep 2421485 = 908057) (by norm_num)
theorem B1209073 : Blo 1072617 1209073 := bbase (se 2 (by rfl) ⟨453402, by rfl⟩ : syracuseStep 1209073 = 906805) (by norm_num)
theorem B1635061 : Blo 1072617 1635061 := bbase (se 5 (by rfl) ⟨76643, by rfl⟩ : syracuseStep 1635061 = 153287) (by norm_num)
theorem B1209109 : Blo 1072617 1209109 := bbase (se 6 (by rfl) ⟨28338, by rfl⟩ : syracuseStep 1209109 = 56677) (by norm_num)
theorem B2421557 : Blo 1072617 2421557 := bbase (se 5 (by rfl) ⟨113510, by rfl⟩ : syracuseStep 2421557 = 227021) (by norm_num)
theorem B1209145 : Blo 1072617 1209145 := bbase (se 2 (by rfl) ⟨453429, by rfl⟩ : syracuseStep 1209145 = 906859) (by norm_num)
theorem B1209181 : Blo 1072617 1209181 := bbase (se 3 (by rfl) ⟨226721, by rfl⟩ : syracuseStep 1209181 = 453443) (by norm_num)
theorem B2716517 : Blo 1072617 2716517 := bbase (se 4 (by rfl) ⟨254673, by rfl⟩ : syracuseStep 2716517 = 509347) (by norm_num)
theorem B2421629 : Blo 1072617 2421629 := bbase (se 3 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 2421629 = 908111) (by norm_num)
theorem B1209217 : Blo 1072617 1209217 := bbase (se 2 (by rfl) ⟨453456, by rfl⟩ : syracuseStep 1209217 = 906913) (by norm_num)
theorem B1209253 : Blo 1072617 1209253 := bbase (se 4 (by rfl) ⟨113367, by rfl⟩ : syracuseStep 1209253 = 226735) (by norm_num)
theorem B2421701 : Blo 1072617 2421701 := bbase (se 4 (by rfl) ⟨227034, by rfl⟩ : syracuseStep 2421701 = 454069) (by norm_num)
theorem B1209289 : Blo 1072617 1209289 := bbase (se 2 (by rfl) ⟨453483, by rfl⟩ : syracuseStep 1209289 = 906967) (by norm_num)
theorem B1209325 : Blo 1072617 1209325 := bbase (se 3 (by rfl) ⟨226748, by rfl⟩ : syracuseStep 1209325 = 453497) (by norm_num)
theorem B2421773 : Blo 1072617 2421773 := bbase (se 3 (by rfl) ⟨454082, by rfl⟩ : syracuseStep 2421773 = 908165) (by norm_num)
theorem B1209361 : Blo 1072617 1209361 := bbase (se 2 (by rfl) ⟨453510, by rfl⟩ : syracuseStep 1209361 = 907021) (by norm_num)
theorem B2585645 : Blo 1072617 2585645 := bbase (se 3 (by rfl) ⟨484808, by rfl⟩ : syracuseStep 2585645 = 969617) (by norm_num)
theorem B1209397 : Blo 1072617 1209397 := bbase (se 5 (by rfl) ⟨56690, by rfl⟩ : syracuseStep 1209397 = 113381) (by norm_num)
theorem B2421845 : Blo 1072617 2421845 := bbase (se 8 (by rfl) ⟨14190, by rfl⟩ : syracuseStep 2421845 = 28381) (by norm_num)
theorem B1209433 : Blo 1072617 1209433 := bbase (se 2 (by rfl) ⟨453537, by rfl⟩ : syracuseStep 1209433 = 907075) (by norm_num)
theorem B1209469 : Blo 1072617 1209469 := bbase (se 3 (by rfl) ⟨226775, by rfl⟩ : syracuseStep 1209469 = 453551) (by norm_num)
theorem B6124693 : Blo 1072617 6124693 := bbase (se 6 (by rfl) ⟨143547, by rfl⟩ : syracuseStep 6124693 = 287095) (by norm_num)
theorem B2421917 : Blo 1072617 2421917 := bbase (se 3 (by rfl) ⟨454109, by rfl⟩ : syracuseStep 2421917 = 908219) (by norm_num)
theorem B1209505 : Blo 1072617 1209505 := bbase (se 2 (by rfl) ⟨453564, by rfl⟩ : syracuseStep 1209505 = 907129) (by norm_num)
theorem B2716861 : Blo 1072617 2716861 := bbase (se 3 (by rfl) ⟨509411, by rfl⟩ : syracuseStep 2716861 = 1018823) (by norm_num)
theorem B1209541 : Blo 1072617 1209541 := bbase (se 4 (by rfl) ⟨113394, by rfl⟩ : syracuseStep 1209541 = 226789) (by norm_num)
theorem B2421989 : Blo 1072617 2421989 := bbase (se 4 (by rfl) ⟨227061, by rfl⟩ : syracuseStep 2421989 = 454123) (by norm_num)
theorem B1209577 : Blo 1072617 1209577 := bbase (se 2 (by rfl) ⟨453591, by rfl⟩ : syracuseStep 1209577 = 907183) (by norm_num)
theorem B1209613 : Blo 1072617 1209613 := bbase (se 3 (by rfl) ⟨226802, by rfl⟩ : syracuseStep 1209613 = 453605) (by norm_num)
theorem B1766677 : Blo 1072617 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B2716973 : Blo 1072617 2716973 := bbase (se 3 (by rfl) ⟨509432, by rfl⟩ : syracuseStep 2716973 = 1018865) (by norm_num)
theorem B2422061 : Blo 1072617 2422061 := bbase (se 3 (by rfl) ⟨454136, by rfl⟩ : syracuseStep 2422061 = 908273) (by norm_num)
theorem B1209649 : Blo 1072617 1209649 := bbase (se 2 (by rfl) ⟨453618, by rfl⟩ : syracuseStep 1209649 = 907237) (by norm_num)
theorem B1209685 : Blo 1072617 1209685 := bbase (se 13 (by rfl) ⟨221, by rfl⟩ : syracuseStep 1209685 = 443) (by norm_num)
theorem B2422133 : Blo 1072617 2422133 := bbase (se 5 (by rfl) ⟨113537, by rfl⟩ : syracuseStep 2422133 = 227075) (by norm_num)
theorem B1209721 : Blo 1072617 1209721 := bbase (se 2 (by rfl) ⟨453645, by rfl⟩ : syracuseStep 1209721 = 907291) (by norm_num)
theorem B1209757 : Blo 1072617 1209757 := bbase (se 3 (by rfl) ⟨226829, by rfl⟩ : syracuseStep 1209757 = 453659) (by norm_num)
theorem B11040181 : Blo 1072617 11040181 := bbase (se 5 (by rfl) ⟨517508, by rfl⟩ : syracuseStep 11040181 = 1035017) (by norm_num)
theorem B2422205 : Blo 1072617 2422205 := bbase (se 3 (by rfl) ⟨454163, by rfl⟩ : syracuseStep 2422205 = 908327) (by norm_num)
theorem B1209793 : Blo 1072617 1209793 := bbase (se 2 (by rfl) ⟨453672, by rfl⟩ : syracuseStep 1209793 = 907345) (by norm_num)
theorem B2586077 : Blo 1072617 2586077 := bbase (se 3 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 2586077 = 969779) (by norm_num)
theorem B1209829 : Blo 1072617 1209829 := bbase (se 4 (by rfl) ⟨113421, by rfl⟩ : syracuseStep 1209829 = 226843) (by norm_num)
theorem B2717165 : Blo 1072617 2717165 := bbase (se 3 (by rfl) ⟨509468, by rfl⟩ : syracuseStep 2717165 = 1018937) (by norm_num)
theorem B2422277 : Blo 1072617 2422277 := bbase (se 4 (by rfl) ⟨227088, by rfl⟩ : syracuseStep 2422277 = 454177) (by norm_num)
theorem B1209865 : Blo 1072617 1209865 := bbase (se 2 (by rfl) ⟨453699, by rfl⟩ : syracuseStep 1209865 = 907399) (by norm_num)
theorem B1963565 : Blo 1072617 1963565 := bbase (se 3 (by rfl) ⟨368168, by rfl⟩ : syracuseStep 1963565 = 736337) (by norm_num)
theorem B1209901 : Blo 1072617 1209901 := bbase (se 3 (by rfl) ⟨226856, by rfl⟩ : syracuseStep 1209901 = 453713) (by norm_num)
theorem B2422349 : Blo 1072617 2422349 := bbase (se 3 (by rfl) ⟨454190, by rfl⟩ : syracuseStep 2422349 = 908381) (by norm_num)
theorem B1209937 : Blo 1072617 1209937 := bbase (se 2 (by rfl) ⟨453726, by rfl⟩ : syracuseStep 1209937 = 907453) (by norm_num)
theorem B3438197 : Blo 1072617 3438197 := bbase (se 5 (by rfl) ⟨161165, by rfl⟩ : syracuseStep 3438197 = 322331) (by norm_num)
theorem B1209973 : Blo 1072617 1209973 := bbase (se 5 (by rfl) ⟨56717, by rfl⟩ : syracuseStep 1209973 = 113435) (by norm_num)
theorem B3929717 : Blo 1072617 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B1210009 : Blo 1072617 1210009 := bbase (se 2 (by rfl) ⟨453753, by rfl⟩ : syracuseStep 1210009 = 907507) (by norm_num)
theorem B1210045 : Blo 1072617 1210045 := bbase (se 3 (by rfl) ⟨226883, by rfl⟩ : syracuseStep 1210045 = 453767) (by norm_num)
theorem B1210081 : Blo 1072617 1210081 := bbase (se 2 (by rfl) ⟨453780, by rfl⟩ : syracuseStep 1210081 = 907561) (by norm_num)
theorem B1210117 : Blo 1072617 1210117 := bbase (se 4 (by rfl) ⟨113448, by rfl⟩ : syracuseStep 1210117 = 226897) (by norm_num)
theorem B5437205 : Blo 1072617 5437205 := bbase (se 6 (by rfl) ⟨127434, by rfl⟩ : syracuseStep 5437205 = 254869) (by norm_num)
theorem B1210153 : Blo 1072617 1210153 := bbase (se 2 (by rfl) ⟨453807, by rfl⟩ : syracuseStep 1210153 = 907615) (by norm_num)
theorem B2586413 : Blo 1072617 2586413 := bbase (se 3 (by rfl) ⟨484952, by rfl⟩ : syracuseStep 2586413 = 969905) (by norm_num)
theorem B2717509 : Blo 1072617 2717509 := bbase (se 4 (by rfl) ⟨254766, by rfl⟩ : syracuseStep 2717509 = 509533) (by norm_num)
theorem B1210189 : Blo 1072617 1210189 := bbase (se 3 (by rfl) ⟨226910, by rfl⟩ : syracuseStep 1210189 = 453821) (by norm_num)
theorem B1210225 : Blo 1072617 1210225 := bbase (se 2 (by rfl) ⟨453834, by rfl⟩ : syracuseStep 1210225 = 907669) (by norm_num)
theorem B1210261 : Blo 1072617 1210261 := bbase (se 6 (by rfl) ⟨28365, by rfl⟩ : syracuseStep 1210261 = 56731) (by norm_num)
theorem B2717621 : Blo 1072617 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B1210297 : Blo 1072617 1210297 := bbase (se 2 (by rfl) ⟨453861, by rfl⟩ : syracuseStep 1210297 = 907723) (by norm_num)
theorem B2291669 : Blo 1072617 2291669 := bbase (se 7 (by rfl) ⟨26855, by rfl⟩ : syracuseStep 2291669 = 53711) (by norm_num)
theorem B1210333 : Blo 1072617 1210333 := bbase (se 3 (by rfl) ⟨226937, by rfl⟩ : syracuseStep 1210333 = 453875) (by norm_num)
theorem B1210369 : Blo 1072617 1210369 := bbase (se 2 (by rfl) ⟨453888, by rfl⟩ : syracuseStep 1210369 = 907777) (by norm_num)
theorem B1210405 : Blo 1072617 1210405 := bbase (se 4 (by rfl) ⟨113475, by rfl⟩ : syracuseStep 1210405 = 226951) (by norm_num)
theorem B1210441 : Blo 1072617 1210441 := bbase (se 2 (by rfl) ⟨453915, by rfl⟩ : syracuseStep 1210441 = 907831) (by norm_num)
theorem B2291789 : Blo 1072617 2291789 := bbase (se 3 (by rfl) ⟨429710, by rfl⟩ : syracuseStep 2291789 = 859421) (by norm_num)
theorem B1210477 : Blo 1072617 1210477 := bbase (se 3 (by rfl) ⟨226964, by rfl⟩ : syracuseStep 1210477 = 453929) (by norm_num)
theorem B2717813 : Blo 1072617 2717813 := bbase (se 5 (by rfl) ⟨127397, by rfl⟩ : syracuseStep 2717813 = 254795) (by norm_num)
theorem B1210513 : Blo 1072617 1210513 := bbase (se 2 (by rfl) ⟨453942, by rfl⟩ : syracuseStep 1210513 = 907885) (by norm_num)
theorem B1308853 : Blo 1072617 1308853 := bbase (se 5 (by rfl) ⟨61352, by rfl⟩ : syracuseStep 1308853 = 122705) (by norm_num)
theorem B1210549 : Blo 1072617 1210549 := bbase (se 5 (by rfl) ⟨56744, by rfl⟩ : syracuseStep 1210549 = 113489) (by norm_num)
theorem B1210585 : Blo 1072617 1210585 := bbase (se 2 (by rfl) ⟨453969, by rfl⟩ : syracuseStep 1210585 = 907939) (by norm_num)
theorem B1210621 : Blo 1072617 1210621 := bbase (se 3 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 1210621 = 453983) (by norm_num)
theorem B1210657 : Blo 1072617 1210657 := bbase (se 2 (by rfl) ⟨453996, by rfl⟩ : syracuseStep 1210657 = 907993) (by norm_num)
theorem B1210693 : Blo 1072617 1210693 := bbase (se 4 (by rfl) ⟨113502, by rfl⟩ : syracuseStep 1210693 = 227005) (by norm_num)
theorem B1210729 : Blo 1072617 1210729 := bbase (se 2 (by rfl) ⟨454023, by rfl⟩ : syracuseStep 1210729 = 908047) (by norm_num)
theorem B1210765 : Blo 1072617 1210765 := bbase (se 3 (by rfl) ⟨227018, by rfl⟩ : syracuseStep 1210765 = 454037) (by norm_num)
theorem B1210801 : Blo 1072617 1210801 := bbase (se 2 (by rfl) ⟨454050, by rfl⟩ : syracuseStep 1210801 = 908101) (by norm_num)
theorem B2718157 : Blo 1072617 2718157 := bbase (se 3 (by rfl) ⟨509654, by rfl⟩ : syracuseStep 2718157 = 1019309) (by norm_num)
theorem B1210837 : Blo 1072617 1210837 := bbase (se 7 (by rfl) ⟨14189, by rfl⟩ : syracuseStep 1210837 = 28379) (by norm_num)
theorem B1210873 : Blo 1072617 1210873 := bbase (se 2 (by rfl) ⟨454077, by rfl⟩ : syracuseStep 1210873 = 908155) (by norm_num)
theorem B1210909 : Blo 1072617 1210909 := bbase (se 3 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 1210909 = 454091) (by norm_num)
theorem B2718269 : Blo 1072617 2718269 := bbase (se 3 (by rfl) ⟨509675, by rfl⟩ : syracuseStep 2718269 = 1019351) (by norm_num)
theorem B1210945 : Blo 1072617 1210945 := bbase (se 2 (by rfl) ⟨454104, by rfl⟩ : syracuseStep 1210945 = 908209) (by norm_num)
theorem B1210981 : Blo 1072617 1210981 := bbase (se 4 (by rfl) ⟨113529, by rfl⟩ : syracuseStep 1210981 = 227059) (by norm_num)
theorem B1211017 : Blo 1072617 1211017 := bbase (se 2 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 1211017 = 908263) (by norm_num)
theorem B1211053 : Blo 1072617 1211053 := bbase (se 3 (by rfl) ⟨227072, by rfl⟩ : syracuseStep 1211053 = 454145) (by norm_num)
theorem B2292421 : Blo 1072617 2292421 := bbase (se 4 (by rfl) ⟨214914, by rfl⟩ : syracuseStep 2292421 = 429829) (by norm_num)
theorem B1211089 : Blo 1072617 1211089 := bbase (se 2 (by rfl) ⟨454158, by rfl⟩ : syracuseStep 1211089 = 908317) (by norm_num)
theorem B1145561 : Blo 1072617 1145561 := bbase (se 2 (by rfl) ⟨429585, by rfl⟩ : syracuseStep 1145561 = 859171) (by norm_num)
theorem B1211125 : Blo 1072617 1211125 := bbase (se 5 (by rfl) ⟨56771, by rfl⟩ : syracuseStep 1211125 = 113543) (by norm_num)
theorem B2718461 : Blo 1072617 2718461 := bbase (se 3 (by rfl) ⟨509711, by rfl⟩ : syracuseStep 2718461 = 1019423) (by norm_num)
theorem B1145621 : Blo 1072617 1145621 := bbase (se 6 (by rfl) ⟨26850, by rfl⟩ : syracuseStep 1145621 = 53701) (by norm_num)
theorem B1211161 : Blo 1072617 1211161 := bbase (se 2 (by rfl) ⟨454185, by rfl⟩ : syracuseStep 1211161 = 908371) (by norm_num)
theorem B1145749 : Blo 1072617 1145749 := bbase (se 6 (by rfl) ⟨26853, by rfl⟩ : syracuseStep 1145749 = 53707) (by norm_num)
theorem B9796565 : Blo 1072617 9796565 := bbase (se 7 (by rfl) ⟨114803, by rfl⟩ : syracuseStep 9796565 = 229607) (by norm_num)
theorem B2948069 : Blo 1072617 2948069 := bbase (se 4 (by rfl) ⟨276381, by rfl⟩ : syracuseStep 2948069 = 552763) (by norm_num)
theorem B5438501 : Blo 1072617 5438501 := bbase (se 4 (by rfl) ⟨509859, by rfl⟩ : syracuseStep 5438501 = 1019719) (by norm_num)
theorem B2718805 : Blo 1072617 2718805 := bbase (se 8 (by rfl) ⟨15930, by rfl⟩ : syracuseStep 2718805 = 31861) (by norm_num)
theorem B6126677 : Blo 1072617 6126677 := bbase (se 8 (by rfl) ⟨35898, by rfl⟩ : syracuseStep 6126677 = 71797) (by norm_num)
theorem B2718917 : Blo 1072617 2718917 := bbase (se 4 (by rfl) ⟨254898, by rfl⟩ : syracuseStep 2718917 = 509797) (by norm_num)
theorem B1146193 : Blo 1072617 1146193 := bbase (se 2 (by rfl) ⟨429822, by rfl⟩ : syracuseStep 1146193 = 859645) (by norm_num)
theorem B2719109 : Blo 1072617 2719109 := bbase (se 4 (by rfl) ⟨254916, by rfl⟩ : syracuseStep 2719109 = 509833) (by norm_num)
theorem B1146313 : Blo 1072617 1146313 := bbase (se 2 (by rfl) ⟨429867, by rfl⟩ : syracuseStep 1146313 = 859735) (by norm_num)
theorem B3440117 : Blo 1072617 3440117 := bbase (se 5 (by rfl) ⟨161255, by rfl⟩ : syracuseStep 3440117 = 322511) (by norm_num)
theorem B4587029 : Blo 1072617 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B2293309 : Blo 1072617 2293309 := bbase (se 3 (by rfl) ⟨429995, by rfl⟩ : syracuseStep 2293309 = 859991) (by norm_num)
theorem B2293429 : Blo 1072617 2293429 := bbase (se 5 (by rfl) ⟨107504, by rfl⟩ : syracuseStep 2293429 = 215009) (by norm_num)
theorem B1146565 : Blo 1072617 1146565 := bbase (se 4 (by rfl) ⟨107490, by rfl⟩ : syracuseStep 1146565 = 214981) (by norm_num)
theorem B1146569 : Blo 1072617 1146569 := bbase (se 2 (by rfl) ⟨429963, by rfl⟩ : syracuseStep 1146569 = 859927) (by norm_num)
theorem B2719453 : Blo 1072617 2719453 := bbase (se 3 (by rfl) ⟨509897, by rfl⟩ : syracuseStep 2719453 = 1019795) (by norm_num)
theorem B2752237 : Blo 1072617 2752237 := bbase (se 3 (by rfl) ⟨516044, by rfl⟩ : syracuseStep 2752237 = 1032089) (by norm_num)
theorem B2719565 : Blo 1072617 2719565 := bbase (se 3 (by rfl) ⟨509918, by rfl⟩ : syracuseStep 2719565 = 1019837) (by norm_num)
theorem B2293685 : Blo 1072617 2293685 := bbase (se 5 (by rfl) ⟨107516, by rfl⟩ : syracuseStep 2293685 = 215033) (by norm_num)
theorem B3440657 : Blo 1072617 3440657 := bstep (se 2 (by rfl) ⟨1290246, by rfl⟩ : syracuseStep 3440657 = 2580493) B2580493
theorem B1146979 : Blo 1072617 1146979 := bstep (se 1 (by rfl) ⟨860234, by rfl⟩ : syracuseStep 1146979 = 1720469) B1720469
theorem B2719889 : Blo 1072617 2719889 := bstep (se 2 (by rfl) ⟨1019958, by rfl⟩ : syracuseStep 2719889 = 2039917) B2039917
theorem B3670211 : Blo 1072617 3670211 := bstep (se 1 (by rfl) ⟨2752658, by rfl⟩ : syracuseStep 3670211 = 5505317) B5505317
theorem B2719939 : Blo 1072617 2719939 := bstep (se 1 (by rfl) ⟨2039954, by rfl⟩ : syracuseStep 2719939 = 4079909) B4079909
theorem B2326801 : Blo 1072617 2326801 := bstep (se 2 (by rfl) ⟨872550, by rfl⟩ : syracuseStep 2326801 = 1745101) B1745101
theorem B2720081 : Blo 1072617 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B10322275 : Blo 1072617 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B2294129 : Blo 1072617 2294129 := bstep (se 2 (by rfl) ⟨860298, by rfl⟩ : syracuseStep 2294129 = 1720597) B1720597
theorem B6881669 : Blo 1072617 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B3932579 : Blo 1072617 3932579 := bstep (se 1 (by rfl) ⟨2949434, by rfl⟩ : syracuseStep 3932579 = 5898869) B5898869
theorem B1147603 : Blo 1072617 1147603 := bstep (se 1 (by rfl) ⟨860702, by rfl⟩ : syracuseStep 1147603 = 1721405) B1721405
theorem B4358897 : Blo 1072617 4358897 := bstep (se 2 (by rfl) ⟨1634586, by rfl⟩ : syracuseStep 4358897 = 3269173) B3269173
theorem B2294659 : Blo 1072617 2294659 := bstep (se 1 (by rfl) ⟨1720994, by rfl⟩ : syracuseStep 2294659 = 3441989) B3441989
theorem B4588721 : Blo 1072617 4588721 := bstep (se 2 (by rfl) ⟨1720770, by rfl⟩ : syracuseStep 4588721 = 3441541) B3441541
theorem B4588771 : Blo 1072617 4588771 := bstep (se 1 (by rfl) ⟨3441578, by rfl⟩ : syracuseStep 4588771 = 6883157) B6883157
theorem B2721073 : Blo 1072617 2721073 := bstep (se 2 (by rfl) ⟨1020402, by rfl⟩ : syracuseStep 2721073 = 2040805) B2040805
theorem B5440931 : Blo 1072617 5440931 := bstep (se 1 (by rfl) ⟨4080698, by rfl⟩ : syracuseStep 5440931 = 8161397) B8161397
theorem B1836611 : Blo 1072617 1836611 := bstep (se 1 (by rfl) ⟨1377458, by rfl⟩ : syracuseStep 1836611 = 2754917) B2754917
theorem B2721347 : Blo 1072617 2721347 := bstep (se 1 (by rfl) ⟨2041010, by rfl⟩ : syracuseStep 2721347 = 4082021) B4082021
theorem B2721539 : Blo 1072617 2721539 := bstep (se 1 (by rfl) ⟨2041154, by rfl⟩ : syracuseStep 2721539 = 4082309) B4082309
theorem B5801827 : Blo 1072617 5801827 := bstep (se 1 (by rfl) ⟨4351370, by rfl⟩ : syracuseStep 5801827 = 8702741) B8702741
theorem B3442733 : Blo 1072617 3442733 := bstep (se 3 (by rfl) ⟨645512, by rfl⟩ : syracuseStep 3442733 = 1291025) B1291025
theorem B5441741 : Blo 1072617 5441741 := bstep (se 3 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 5441741 = 2040653) B2040653
theorem B6195491 : Blo 1072617 6195491 := bstep (se 1 (by rfl) ⟨4646618, by rfl⟩ : syracuseStep 6195491 = 9293237) B9293237
theorem B2722097 : Blo 1072617 2722097 := bstep (se 2 (by rfl) ⟨1020786, by rfl⟩ : syracuseStep 2722097 = 2041573) B2041573
theorem B1378627 : Blo 1072617 1378627 := bstep (se 1 (by rfl) ⟨1033970, by rfl⟩ : syracuseStep 1378627 = 2067941) B2067941
theorem B2296145 : Blo 1072617 2296145 := bstep (se 2 (by rfl) ⟨861054, by rfl⟩ : syracuseStep 2296145 = 1722109) B1722109
theorem B2296163 : Blo 1072617 2296163 := bstep (se 1 (by rfl) ⟨1722122, by rfl⟩ : syracuseStep 2296163 = 3444245) B3444245
theorem B1149491 : Blo 1072617 1149491 := bstep (se 1 (by rfl) ⟨862118, by rfl⟩ : syracuseStep 1149491 = 1724237) B1724237
theorem B2722481 : Blo 1072617 2722481 := bstep (se 2 (by rfl) ⟨1020930, by rfl⟩ : syracuseStep 2722481 = 2041861) B2041861
theorem B2722531 : Blo 1072617 2722531 := bstep (se 1 (by rfl) ⟨2041898, by rfl⟩ : syracuseStep 2722531 = 4083797) B4083797
theorem B6195973 : Blo 1072617 6195973 := bstep (se 4 (by rfl) ⟨580872, by rfl⟩ : syracuseStep 6195973 = 1161745) B1161745
theorem B2722673 : Blo 1072617 2722673 := bstep (se 2 (by rfl) ⟨1021002, by rfl⟩ : syracuseStep 2722673 = 2042005) B2042005
theorem B3443629 : Blo 1072617 3443629 := bstep (se 3 (by rfl) ⟨645680, by rfl⟩ : syracuseStep 3443629 = 1291361) B1291361
theorem B1838225 : Blo 1072617 1838225 := bstep (se 2 (by rfl) ⟨689334, by rfl⟩ : syracuseStep 1838225 = 1378669) B1378669
theorem B1608929 : Blo 1072617 1608929 := bstep (se 2 (by rfl) ⟨603348, by rfl⟩ : syracuseStep 1608929 = 1206697) B1206697
theorem B1608947 : Blo 1072617 1608947 := bstep (se 1 (by rfl) ⟨1206710, by rfl⟩ : syracuseStep 1608947 = 2413421) B2413421
theorem B1608977 : Blo 1072617 1608977 := bstep (se 2 (by rfl) ⟨603366, by rfl⟩ : syracuseStep 1608977 = 1206733) B1206733
theorem B1608995 : Blo 1072617 1608995 := bstep (se 1 (by rfl) ⟨1206746, by rfl⟩ : syracuseStep 1608995 = 2413493) B2413493
theorem B1609025 : Blo 1072617 1609025 := bstep (se 2 (by rfl) ⟨603384, by rfl⟩ : syracuseStep 1609025 = 1206769) B1206769
theorem B1609043 : Blo 1072617 1609043 := bstep (se 1 (by rfl) ⟨1206782, by rfl⟩ : syracuseStep 1609043 = 2413565) B2413565
theorem B1609073 : Blo 1072617 1609073 := bstep (se 2 (by rfl) ⟨603402, by rfl⟩ : syracuseStep 1609073 = 1206805) B1206805
theorem B1609091 : Blo 1072617 1609091 := bstep (se 1 (by rfl) ⟨1206818, by rfl⟩ : syracuseStep 1609091 = 2413637) B2413637
theorem B1609121 : Blo 1072617 1609121 := bstep (se 2 (by rfl) ⟨603420, by rfl⟩ : syracuseStep 1609121 = 1206841) B1206841
theorem B1609139 : Blo 1072617 1609139 := bstep (se 1 (by rfl) ⟨1206854, by rfl⟩ : syracuseStep 1609139 = 2413709) B2413709
theorem B1609169 : Blo 1072617 1609169 := bstep (se 2 (by rfl) ⟨603438, by rfl⟩ : syracuseStep 1609169 = 1206877) B1206877
theorem B1609187 : Blo 1072617 1609187 := bstep (se 1 (by rfl) ⟨1206890, by rfl⟩ : syracuseStep 1609187 = 2413781) B2413781
theorem B1609217 : Blo 1072617 1609217 := bstep (se 2 (by rfl) ⟨603456, by rfl⟩ : syracuseStep 1609217 = 1206913) B1206913
theorem B1609235 : Blo 1072617 1609235 := bstep (se 1 (by rfl) ⟨1206926, by rfl⟩ : syracuseStep 1609235 = 2413853) B2413853
theorem B5508643 : Blo 1072617 5508643 := bstep (se 1 (by rfl) ⟨4131482, by rfl⟩ : syracuseStep 5508643 = 8262965) B8262965
theorem B1609265 : Blo 1072617 1609265 := bstep (se 2 (by rfl) ⟨603474, by rfl⟩ : syracuseStep 1609265 = 1206949) B1206949
theorem B2297393 : Blo 1072617 2297393 := bstep (se 2 (by rfl) ⟨861522, by rfl⟩ : syracuseStep 2297393 = 1723045) B1723045
theorem B1609283 : Blo 1072617 1609283 := bstep (se 1 (by rfl) ⟨1206962, by rfl⟩ : syracuseStep 1609283 = 2413925) B2413925
theorem B4591181 : Blo 1072617 4591181 := bstep (se 3 (by rfl) ⟨860846, by rfl⟩ : syracuseStep 4591181 = 1721693) B1721693
theorem B7179853 : Blo 1072617 7179853 := bstep (se 3 (by rfl) ⟨1346222, by rfl⟩ : syracuseStep 7179853 = 2692445) B2692445
theorem B1609313 : Blo 1072617 1609313 := bstep (se 2 (by rfl) ⟨603492, by rfl⟩ : syracuseStep 1609313 = 1206985) B1206985
theorem B1609331 : Blo 1072617 1609331 := bstep (se 1 (by rfl) ⟨1206998, by rfl⟩ : syracuseStep 1609331 = 2413997) B2413997
theorem B1609361 : Blo 1072617 1609361 := bstep (se 2 (by rfl) ⟨603510, by rfl⟩ : syracuseStep 1609361 = 1207021) B1207021
theorem B1609379 : Blo 1072617 1609379 := bstep (se 1 (by rfl) ⟨1207034, by rfl⟩ : syracuseStep 1609379 = 2414069) B2414069
theorem B1609409 : Blo 1072617 1609409 := bstep (se 2 (by rfl) ⟨603528, by rfl⟩ : syracuseStep 1609409 = 1207057) B1207057
theorem B6524621 : Blo 1072617 6524621 := bstep (se 3 (by rfl) ⟨1223366, by rfl⟩ : syracuseStep 6524621 = 2446733) B2446733
theorem B1609427 : Blo 1072617 1609427 := bstep (se 1 (by rfl) ⟨1207070, by rfl⟩ : syracuseStep 1609427 = 2414141) B2414141
theorem B1609457 : Blo 1072617 1609457 := bstep (se 2 (by rfl) ⟨603546, by rfl⟩ : syracuseStep 1609457 = 1207093) B1207093
theorem B1609475 : Blo 1072617 1609475 := bstep (se 1 (by rfl) ⟨1207106, by rfl⟩ : syracuseStep 1609475 = 2414213) B2414213
theorem B1609505 : Blo 1072617 1609505 := bstep (se 2 (by rfl) ⟨603564, by rfl⟩ : syracuseStep 1609505 = 1207129) B1207129
theorem B6885155 : Blo 1072617 6885155 := bstep (se 1 (by rfl) ⟨5163866, by rfl⟩ : syracuseStep 6885155 = 10327733) B10327733
theorem B3444515 : Blo 1072617 3444515 := bstep (se 1 (by rfl) ⟨2583386, by rfl⟩ : syracuseStep 3444515 = 5166773) B5166773
theorem B1609523 : Blo 1072617 1609523 := bstep (se 1 (by rfl) ⟨1207142, by rfl⟩ : syracuseStep 1609523 = 2414285) B2414285
theorem B1609553 : Blo 1072617 1609553 := bstep (se 2 (by rfl) ⟨603582, by rfl⟩ : syracuseStep 1609553 = 1207165) B1207165
theorem B2723665 : Blo 1072617 2723665 := bstep (se 2 (by rfl) ⟨1021374, by rfl⟩ : syracuseStep 2723665 = 2042749) B2042749
theorem B1609571 : Blo 1072617 1609571 := bstep (se 1 (by rfl) ⟨1207178, by rfl⟩ : syracuseStep 1609571 = 2414357) B2414357
theorem B1609601 : Blo 1072617 1609601 := bstep (se 2 (by rfl) ⟨603600, by rfl⟩ : syracuseStep 1609601 = 1207201) B1207201
theorem B1609619 : Blo 1072617 1609619 := bstep (se 1 (by rfl) ⟨1207214, by rfl⟩ : syracuseStep 1609619 = 2414429) B2414429
theorem B1937315 : Blo 1072617 1937315 := bstep (se 1 (by rfl) ⟨1452986, by rfl⟩ : syracuseStep 1937315 = 2905973) B2905973
theorem B1609649 : Blo 1072617 1609649 := bstep (se 2 (by rfl) ⟨603618, by rfl⟩ : syracuseStep 1609649 = 1207237) B1207237
theorem B1609667 : Blo 1072617 1609667 := bstep (se 1 (by rfl) ⟨1207250, by rfl⟩ : syracuseStep 1609667 = 2414501) B2414501
theorem B1609697 : Blo 1072617 1609697 := bstep (se 2 (by rfl) ⟨603636, by rfl⟩ : syracuseStep 1609697 = 1207273) B1207273
theorem B1609715 : Blo 1072617 1609715 := bstep (se 1 (by rfl) ⟨1207286, by rfl⟩ : syracuseStep 1609715 = 2414573) B2414573
theorem B8163341 : Blo 1072617 8163341 := bstep (se 3 (by rfl) ⟨1530626, by rfl⟩ : syracuseStep 8163341 = 3061253) B3061253
theorem B1609745 : Blo 1072617 1609745 := bstep (se 2 (by rfl) ⟨603654, by rfl⟩ : syracuseStep 1609745 = 1207309) B1207309
theorem B1609763 : Blo 1072617 1609763 := bstep (se 1 (by rfl) ⟨1207322, by rfl⟩ : syracuseStep 1609763 = 2414645) B2414645
theorem B1609793 : Blo 1072617 1609793 := bstep (se 2 (by rfl) ⟨603672, by rfl⟩ : syracuseStep 1609793 = 1207345) B1207345
theorem B1609811 : Blo 1072617 1609811 := bstep (se 1 (by rfl) ⟨1207358, by rfl⟩ : syracuseStep 1609811 = 2414717) B2414717
theorem B2723939 : Blo 1072617 2723939 := bstep (se 1 (by rfl) ⟨2042954, by rfl⟩ : syracuseStep 2723939 = 4085909) B4085909
theorem B1609841 : Blo 1072617 1609841 := bstep (se 2 (by rfl) ⟨603690, by rfl⟩ : syracuseStep 1609841 = 1207381) B1207381
theorem B1609859 : Blo 1072617 1609859 := bstep (se 1 (by rfl) ⟨1207394, by rfl⟩ : syracuseStep 1609859 = 2414789) B2414789
theorem B1609889 : Blo 1072617 1609889 := bstep (se 2 (by rfl) ⟨603708, by rfl⟩ : syracuseStep 1609889 = 1207417) B1207417
theorem B6197411 : Blo 1072617 6197411 := bstep (se 1 (by rfl) ⟨4648058, by rfl⟩ : syracuseStep 6197411 = 9296117) B9296117
theorem B1609907 : Blo 1072617 1609907 := bstep (se 1 (by rfl) ⟨1207430, by rfl⟩ : syracuseStep 1609907 = 2414861) B2414861
theorem B1609937 : Blo 1072617 1609937 := bstep (se 2 (by rfl) ⟨603726, by rfl⟩ : syracuseStep 1609937 = 1207453) B1207453
theorem B1609955 : Blo 1072617 1609955 := bstep (se 1 (by rfl) ⟨1207466, by rfl⟩ : syracuseStep 1609955 = 2414933) B2414933
theorem B12226787 : Blo 1072617 12226787 := bstep (se 1 (by rfl) ⟨9170090, by rfl⟩ : syracuseStep 12226787 = 18340181) B18340181
theorem B1609985 : Blo 1072617 1609985 := bstep (se 2 (by rfl) ⟨603744, by rfl⟩ : syracuseStep 1609985 = 1207489) B1207489
theorem B1610003 : Blo 1072617 1610003 := bstep (se 1 (by rfl) ⟨1207502, by rfl⟩ : syracuseStep 1610003 = 2415005) B2415005
theorem B2724131 : Blo 1072617 2724131 := bstep (se 1 (by rfl) ⟨2043098, by rfl⟩ : syracuseStep 2724131 = 4086197) B4086197
theorem B1610033 : Blo 1072617 1610033 := bstep (se 2 (by rfl) ⟨603762, by rfl⟩ : syracuseStep 1610033 = 1207525) B1207525
theorem B1610051 : Blo 1072617 1610051 := bstep (se 1 (by rfl) ⟨1207538, by rfl⟩ : syracuseStep 1610051 = 2415077) B2415077
theorem B1610081 : Blo 1072617 1610081 := bstep (se 2 (by rfl) ⟨603780, by rfl⟩ : syracuseStep 1610081 = 1207561) B1207561
theorem B1610099 : Blo 1072617 1610099 := bstep (se 1 (by rfl) ⟨1207574, by rfl⟩ : syracuseStep 1610099 = 2415149) B2415149
theorem B1610129 : Blo 1072617 1610129 := bstep (se 2 (by rfl) ⟨603798, by rfl⟩ : syracuseStep 1610129 = 1207597) B1207597
theorem B1610147 : Blo 1072617 1610147 := bstep (se 1 (by rfl) ⟨1207610, by rfl⟩ : syracuseStep 1610147 = 2415221) B2415221
theorem B1610177 : Blo 1072617 1610177 := bstep (se 2 (by rfl) ⟨603816, by rfl⟩ : syracuseStep 1610177 = 1207633) B1207633
theorem B1610195 : Blo 1072617 1610195 := bstep (se 1 (by rfl) ⟨1207646, by rfl⟩ : syracuseStep 1610195 = 2415293) B2415293
theorem B1610225 : Blo 1072617 1610225 := bstep (se 2 (by rfl) ⟨603834, by rfl⟩ : syracuseStep 1610225 = 1207669) B1207669
theorem B1610243 : Blo 1072617 1610243 := bstep (se 1 (by rfl) ⟨1207682, by rfl⟩ : syracuseStep 1610243 = 2415365) B2415365
theorem B1610273 : Blo 1072617 1610273 := bstep (se 2 (by rfl) ⟨603852, by rfl⟩ : syracuseStep 1610273 = 1207705) B1207705
theorem B1610291 : Blo 1072617 1610291 := bstep (se 1 (by rfl) ⟨1207718, by rfl⟩ : syracuseStep 1610291 = 2415437) B2415437
theorem B1610321 : Blo 1072617 1610321 := bstep (se 2 (by rfl) ⟨603870, by rfl⟩ : syracuseStep 1610321 = 1207741) B1207741
theorem B1938001 : Blo 1072617 1938001 := bstep (se 2 (by rfl) ⟨726750, by rfl⟩ : syracuseStep 1938001 = 1453501) B1453501
theorem B1610339 : Blo 1072617 1610339 := bstep (se 1 (by rfl) ⟨1207754, by rfl⟩ : syracuseStep 1610339 = 2415509) B2415509
theorem B1610369 : Blo 1072617 1610369 := bstep (se 2 (by rfl) ⟨603888, by rfl⟩ : syracuseStep 1610369 = 1207777) B1207777
theorem B1610387 : Blo 1072617 1610387 := bstep (se 1 (by rfl) ⟨1207790, by rfl⟩ : syracuseStep 1610387 = 2415581) B2415581
theorem B1610417 : Blo 1072617 1610417 := bstep (se 2 (by rfl) ⟨603906, by rfl⟩ : syracuseStep 1610417 = 1207813) B1207813
theorem B1610435 : Blo 1072617 1610435 := bstep (se 1 (by rfl) ⟨1207826, by rfl⟩ : syracuseStep 1610435 = 2415653) B2415653
theorem B1610465 : Blo 1072617 1610465 := bstep (se 2 (by rfl) ⟨603924, by rfl⟩ : syracuseStep 1610465 = 1207849) B1207849
theorem B27529955 : Blo 1072617 27529955 := bstep (se 1 (by rfl) ⟨20647466, by rfl⟩ : syracuseStep 27529955 = 41294933) B41294933
theorem B1610483 : Blo 1072617 1610483 := bstep (se 1 (by rfl) ⟨1207862, by rfl⟩ : syracuseStep 1610483 = 2415725) B2415725
theorem B1610513 : Blo 1072617 1610513 := bstep (se 2 (by rfl) ⟨603942, by rfl⟩ : syracuseStep 1610513 = 1207885) B1207885
theorem B2036515 : Blo 1072617 2036515 := bstep (se 1 (by rfl) ⟨1527386, by rfl⟩ : syracuseStep 2036515 = 3054773) B3054773
theorem B1610531 : Blo 1072617 1610531 := bstep (se 1 (by rfl) ⟨1207898, by rfl⟩ : syracuseStep 1610531 = 2415797) B2415797
theorem B2069297 : Blo 1072617 2069297 := bstep (se 2 (by rfl) ⟨775986, by rfl⟩ : syracuseStep 2069297 = 1551973) B1551973
theorem B1610561 : Blo 1072617 1610561 := bstep (se 2 (by rfl) ⟨603960, by rfl⟩ : syracuseStep 1610561 = 1207921) B1207921
theorem B1610579 : Blo 1072617 1610579 := bstep (se 1 (by rfl) ⟨1207934, by rfl⟩ : syracuseStep 1610579 = 2415869) B2415869
theorem B1610609 : Blo 1072617 1610609 := bstep (se 2 (by rfl) ⟨603978, by rfl⟩ : syracuseStep 1610609 = 1207957) B1207957
theorem B1610627 : Blo 1072617 1610627 := bstep (se 1 (by rfl) ⟨1207970, by rfl⟩ : syracuseStep 1610627 = 2415941) B2415941
theorem B1610657 : Blo 1072617 1610657 := bstep (se 2 (by rfl) ⟨603996, by rfl⟩ : syracuseStep 1610657 = 1207993) B1207993
theorem B1610675 : Blo 1072617 1610675 := bstep (se 1 (by rfl) ⟨1208006, by rfl⟩ : syracuseStep 1610675 = 2416013) B2416013
theorem B1610705 : Blo 1072617 1610705 := bstep (se 2 (by rfl) ⟨604014, by rfl⟩ : syracuseStep 1610705 = 1208029) B1208029
theorem B1610723 : Blo 1072617 1610723 := bstep (se 1 (by rfl) ⟨1208042, by rfl⟩ : syracuseStep 1610723 = 2416085) B2416085
theorem B1610753 : Blo 1072617 1610753 := bstep (se 2 (by rfl) ⟨604032, by rfl⟩ : syracuseStep 1610753 = 1208065) B1208065
theorem B1610771 : Blo 1072617 1610771 := bstep (se 1 (by rfl) ⟨1208078, by rfl⟩ : syracuseStep 1610771 = 2416157) B2416157
theorem B1610801 : Blo 1072617 1610801 := bstep (se 2 (by rfl) ⟨604050, by rfl⟩ : syracuseStep 1610801 = 1208101) B1208101
theorem B5444657 : Blo 1072617 5444657 := bstep (se 2 (by rfl) ⟨2041746, by rfl⟩ : syracuseStep 5444657 = 4083493) B4083493
theorem B1610819 : Blo 1072617 1610819 := bstep (se 1 (by rfl) ⟨1208114, by rfl⟩ : syracuseStep 1610819 = 2416229) B2416229
theorem B2298947 : Blo 1072617 2298947 := bstep (se 1 (by rfl) ⟨1724210, by rfl⟩ : syracuseStep 2298947 = 3448421) B3448421
theorem B1610849 : Blo 1072617 1610849 := bstep (se 2 (by rfl) ⟨604068, by rfl⟩ : syracuseStep 1610849 = 1208137) B1208137
theorem B1610867 : Blo 1072617 1610867 := bstep (se 1 (by rfl) ⟨1208150, by rfl⟩ : syracuseStep 1610867 = 2416301) B2416301
theorem B1610897 : Blo 1072617 1610897 := bstep (se 2 (by rfl) ⟨604086, by rfl⟩ : syracuseStep 1610897 = 1208173) B1208173
theorem B1610915 : Blo 1072617 1610915 := bstep (se 1 (by rfl) ⟨1208186, by rfl⟩ : syracuseStep 1610915 = 2416373) B2416373
theorem B1610945 : Blo 1072617 1610945 := bstep (se 2 (by rfl) ⟨604104, by rfl⟩ : syracuseStep 1610945 = 1208209) B1208209
theorem B2725073 : Blo 1072617 2725073 := bstep (se 2 (by rfl) ⟨1021902, by rfl⟩ : syracuseStep 2725073 = 2043805) B2043805
theorem B1610963 : Blo 1072617 1610963 := bstep (se 1 (by rfl) ⟨1208222, by rfl⟩ : syracuseStep 1610963 = 2416445) B2416445
theorem B2036963 : Blo 1072617 2036963 := bstep (se 1 (by rfl) ⟨1527722, by rfl⟩ : syracuseStep 2036963 = 3055445) B3055445
theorem B58758371 : Blo 1072617 58758371 := bstep (se 1 (by rfl) ⟨44068778, by rfl⟩ : syracuseStep 58758371 = 88137557) B88137557
theorem B1610993 : Blo 1072617 1610993 := bstep (se 2 (by rfl) ⟨604122, by rfl⟩ : syracuseStep 1610993 = 1208245) B1208245
theorem B1611011 : Blo 1072617 1611011 := bstep (se 1 (by rfl) ⟨1208258, by rfl⟩ : syracuseStep 1611011 = 2416517) B2416517
theorem B2725123 : Blo 1072617 2725123 := bstep (se 1 (by rfl) ⟨2043842, by rfl⟩ : syracuseStep 2725123 = 4087685) B4087685
theorem B1611041 : Blo 1072617 1611041 := bstep (se 2 (by rfl) ⟨604140, by rfl⟩ : syracuseStep 1611041 = 1208281) B1208281
theorem B1611059 : Blo 1072617 1611059 := bstep (se 1 (by rfl) ⟨1208294, by rfl⟩ : syracuseStep 1611059 = 2416589) B2416589
theorem B1611089 : Blo 1072617 1611089 := bstep (se 2 (by rfl) ⟨604158, by rfl⟩ : syracuseStep 1611089 = 1208317) B1208317
theorem B1611107 : Blo 1072617 1611107 := bstep (se 1 (by rfl) ⟨1208330, by rfl⟩ : syracuseStep 1611107 = 2416661) B2416661
theorem B1611137 : Blo 1072617 1611137 := bstep (se 2 (by rfl) ⟨604176, by rfl⟩ : syracuseStep 1611137 = 1208353) B1208353
theorem B1611155 : Blo 1072617 1611155 := bstep (se 1 (by rfl) ⟨1208366, by rfl⟩ : syracuseStep 1611155 = 2416733) B2416733
theorem B1611185 : Blo 1072617 1611185 := bstep (se 2 (by rfl) ⟨604194, by rfl⟩ : syracuseStep 1611185 = 1208389) B1208389
theorem B1611203 : Blo 1072617 1611203 := bstep (se 1 (by rfl) ⟨1208402, by rfl⟩ : syracuseStep 1611203 = 2416805) B2416805
theorem B1611233 : Blo 1072617 1611233 := bstep (se 2 (by rfl) ⟨604212, by rfl⟩ : syracuseStep 1611233 = 1208425) B1208425
theorem B1611251 : Blo 1072617 1611251 := bstep (se 1 (by rfl) ⟨1208438, by rfl⟩ : syracuseStep 1611251 = 2416877) B2416877
theorem B2037251 : Blo 1072617 2037251 := bstep (se 1 (by rfl) ⟨1527938, by rfl⟩ : syracuseStep 2037251 = 3055877) B3055877
theorem B1611281 : Blo 1072617 1611281 := bstep (se 2 (by rfl) ⟨604230, by rfl⟩ : syracuseStep 1611281 = 1208461) B1208461
theorem B1611299 : Blo 1072617 1611299 := bstep (se 1 (by rfl) ⟨1208474, by rfl⟩ : syracuseStep 1611299 = 2416949) B2416949
theorem B1611329 : Blo 1072617 1611329 := bstep (se 2 (by rfl) ⟨604248, by rfl⟩ : syracuseStep 1611329 = 1208497) B1208497
theorem B1611347 : Blo 1072617 1611347 := bstep (se 1 (by rfl) ⟨1208510, by rfl⟩ : syracuseStep 1611347 = 2417021) B2417021
theorem B1611377 : Blo 1072617 1611377 := bstep (se 2 (by rfl) ⟨604266, by rfl⟩ : syracuseStep 1611377 = 1208533) B1208533
theorem B1611395 : Blo 1072617 1611395 := bstep (se 1 (by rfl) ⟨1208546, by rfl⟩ : syracuseStep 1611395 = 2417093) B2417093
theorem B5805701 : Blo 1072617 5805701 := bstep (se 4 (by rfl) ⟨544284, by rfl⟩ : syracuseStep 5805701 = 1088569) B1088569
theorem B1611425 : Blo 1072617 1611425 := bstep (se 2 (by rfl) ⟨604284, by rfl⟩ : syracuseStep 1611425 = 1208569) B1208569
theorem B1611443 : Blo 1072617 1611443 := bstep (se 1 (by rfl) ⟨1208582, by rfl⟩ : syracuseStep 1611443 = 2417165) B2417165
theorem B1611473 : Blo 1072617 1611473 := bstep (se 2 (by rfl) ⟨604302, by rfl⟩ : syracuseStep 1611473 = 1208605) B1208605
theorem B1611491 : Blo 1072617 1611491 := bstep (se 1 (by rfl) ⟨1208618, by rfl⟩ : syracuseStep 1611491 = 2417237) B2417237
theorem B1611521 : Blo 1072617 1611521 := bstep (se 2 (by rfl) ⟨604320, by rfl⟩ : syracuseStep 1611521 = 1208641) B1208641
theorem B1611539 : Blo 1072617 1611539 := bstep (se 1 (by rfl) ⟨1208654, by rfl⟩ : syracuseStep 1611539 = 2417309) B2417309
theorem B1611569 : Blo 1072617 1611569 := bstep (se 2 (by rfl) ⟨604338, by rfl⟩ : syracuseStep 1611569 = 1208677) B1208677
theorem B1611587 : Blo 1072617 1611587 := bstep (se 1 (by rfl) ⟨1208690, by rfl⟩ : syracuseStep 1611587 = 2417381) B2417381
theorem B1611617 : Blo 1072617 1611617 := bstep (se 2 (by rfl) ⟨604356, by rfl⟩ : syracuseStep 1611617 = 1208713) B1208713
theorem B1611635 : Blo 1072617 1611635 := bstep (se 1 (by rfl) ⟨1208726, by rfl⟩ : syracuseStep 1611635 = 2417453) B2417453
theorem B1611665 : Blo 1072617 1611665 := bstep (se 2 (by rfl) ⟨604374, by rfl⟩ : syracuseStep 1611665 = 1208749) B1208749
theorem B1611683 : Blo 1072617 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B3446705 : Blo 1072617 3446705 := bstep (se 2 (by rfl) ⟨1292514, by rfl⟩ : syracuseStep 3446705 = 2585029) B2585029
theorem B1611713 : Blo 1072617 1611713 := bstep (se 2 (by rfl) ⟨604392, by rfl⟩ : syracuseStep 1611713 = 1208785) B1208785
theorem B1611731 : Blo 1072617 1611731 := bstep (se 1 (by rfl) ⟨1208798, by rfl⟩ : syracuseStep 1611731 = 2417597) B2417597
theorem B1611761 : Blo 1072617 1611761 := bstep (se 2 (by rfl) ⟨604410, by rfl⟩ : syracuseStep 1611761 = 1208821) B1208821
theorem B1611779 : Blo 1072617 1611779 := bstep (se 1 (by rfl) ⟨1208834, by rfl⟩ : syracuseStep 1611779 = 2417669) B2417669
theorem B1611809 : Blo 1072617 1611809 := bstep (se 2 (by rfl) ⟨604428, by rfl⟩ : syracuseStep 1611809 = 1208857) B1208857
theorem B3446833 : Blo 1072617 3446833 := bstep (se 2 (by rfl) ⟨1292562, by rfl⟩ : syracuseStep 3446833 = 2585125) B2585125
theorem B1611827 : Blo 1072617 1611827 := bstep (se 1 (by rfl) ⟨1208870, by rfl⟩ : syracuseStep 1611827 = 2417741) B2417741
theorem B1611857 : Blo 1072617 1611857 := bstep (se 2 (by rfl) ⟨604446, by rfl⟩ : syracuseStep 1611857 = 1208893) B1208893
theorem B1611875 : Blo 1072617 1611875 := bstep (se 1 (by rfl) ⟨1208906, by rfl⟩ : syracuseStep 1611875 = 2417813) B2417813
theorem B1611905 : Blo 1072617 1611905 := bstep (se 2 (by rfl) ⟨604464, by rfl⟩ : syracuseStep 1611905 = 1208929) B1208929
theorem B1611923 : Blo 1072617 1611923 := bstep (se 1 (by rfl) ⟨1208942, by rfl⟩ : syracuseStep 1611923 = 2417885) B2417885
theorem B1611953 : Blo 1072617 1611953 := bstep (se 2 (by rfl) ⟨604482, by rfl⟩ : syracuseStep 1611953 = 1208965) B1208965
theorem B1611971 : Blo 1072617 1611971 := bstep (se 1 (by rfl) ⟨1208978, by rfl⟩ : syracuseStep 1611971 = 2417957) B2417957
theorem B1612001 : Blo 1072617 1612001 := bstep (se 2 (by rfl) ⟨604500, by rfl⟩ : syracuseStep 1612001 = 1209001) B1209001
theorem B1612019 : Blo 1072617 1612019 := bstep (se 1 (by rfl) ⟨1209014, by rfl⟩ : syracuseStep 1612019 = 2418029) B2418029
theorem B1612049 : Blo 1072617 1612049 := bstep (se 2 (by rfl) ⟨604518, by rfl⟩ : syracuseStep 1612049 = 1209037) B1209037
theorem B1612067 : Blo 1072617 1612067 := bstep (se 1 (by rfl) ⟨1209050, by rfl⟩ : syracuseStep 1612067 = 2418101) B2418101
theorem B3447089 : Blo 1072617 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B1612097 : Blo 1072617 1612097 := bstep (se 2 (by rfl) ⟨604536, by rfl⟩ : syracuseStep 1612097 = 1209073) B1209073
theorem B1612115 : Blo 1072617 1612115 := bstep (se 1 (by rfl) ⟨1209086, by rfl⟩ : syracuseStep 1612115 = 2418173) B2418173
theorem B1612145 : Blo 1072617 1612145 := bstep (se 2 (by rfl) ⟨604554, by rfl⟩ : syracuseStep 1612145 = 1209109) B1209109
theorem B1612163 : Blo 1072617 1612163 := bstep (se 1 (by rfl) ⟨1209122, by rfl⟩ : syracuseStep 1612163 = 2418245) B2418245
theorem B1612193 : Blo 1072617 1612193 := bstep (se 2 (by rfl) ⟨604572, by rfl⟩ : syracuseStep 1612193 = 1209145) B1209145
theorem B2038193 : Blo 1072617 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B1612211 : Blo 1072617 1612211 := bstep (se 1 (by rfl) ⟨1209158, by rfl⟩ : syracuseStep 1612211 = 2418317) B2418317
theorem B1612241 : Blo 1072617 1612241 := bstep (se 2 (by rfl) ⟨604590, by rfl⟩ : syracuseStep 1612241 = 1209181) B1209181
theorem B1612259 : Blo 1072617 1612259 := bstep (se 1 (by rfl) ⟨1209194, by rfl⟩ : syracuseStep 1612259 = 2418389) B2418389
theorem B5446115 : Blo 1072617 5446115 := bstep (se 1 (by rfl) ⟨4084586, by rfl⟩ : syracuseStep 5446115 = 8169173) B8169173
theorem B1612289 : Blo 1072617 1612289 := bstep (se 2 (by rfl) ⟨604608, by rfl⟩ : syracuseStep 1612289 = 1209217) B1209217
theorem B1612307 : Blo 1072617 1612307 := bstep (se 1 (by rfl) ⟨1209230, by rfl⟩ : syracuseStep 1612307 = 2418461) B2418461
theorem B1612337 : Blo 1072617 1612337 := bstep (se 2 (by rfl) ⟨604626, by rfl⟩ : syracuseStep 1612337 = 1209253) B1209253
theorem B1612355 : Blo 1072617 1612355 := bstep (se 1 (by rfl) ⟨1209266, by rfl⟩ : syracuseStep 1612355 = 2418533) B2418533
theorem B1612385 : Blo 1072617 1612385 := bstep (se 2 (by rfl) ⟨604644, by rfl⟩ : syracuseStep 1612385 = 1209289) B1209289
theorem B1612403 : Blo 1072617 1612403 := bstep (se 1 (by rfl) ⟨1209302, by rfl⟩ : syracuseStep 1612403 = 2418605) B2418605
theorem B1612433 : Blo 1072617 1612433 := bstep (se 2 (by rfl) ⟨604662, by rfl⟩ : syracuseStep 1612433 = 1209325) B1209325
theorem B1612451 : Blo 1072617 1612451 := bstep (se 1 (by rfl) ⟨1209338, by rfl⟩ : syracuseStep 1612451 = 2418677) B2418677
theorem B1612481 : Blo 1072617 1612481 := bstep (se 2 (by rfl) ⟨604680, by rfl⟩ : syracuseStep 1612481 = 1209361) B1209361
theorem B1612499 : Blo 1072617 1612499 := bstep (se 1 (by rfl) ⟨1209374, by rfl⟩ : syracuseStep 1612499 = 2418749) B2418749
theorem B1612529 : Blo 1072617 1612529 := bstep (se 2 (by rfl) ⟨604698, by rfl⟩ : syracuseStep 1612529 = 1209397) B1209397
theorem B1612547 : Blo 1072617 1612547 := bstep (se 1 (by rfl) ⟨1209410, by rfl⟩ : syracuseStep 1612547 = 2418821) B2418821
theorem B1612577 : Blo 1072617 1612577 := bstep (se 2 (by rfl) ⟨604716, by rfl⟩ : syracuseStep 1612577 = 1209433) B1209433
theorem B1612595 : Blo 1072617 1612595 := bstep (se 1 (by rfl) ⟨1209446, by rfl⟩ : syracuseStep 1612595 = 2418893) B2418893
theorem B1612625 : Blo 1072617 1612625 := bstep (se 2 (by rfl) ⟨604734, by rfl⟩ : syracuseStep 1612625 = 1209469) B1209469
theorem B1612643 : Blo 1072617 1612643 := bstep (se 1 (by rfl) ⟨1209482, by rfl⟩ : syracuseStep 1612643 = 2418965) B2418965
theorem B8166257 : Blo 1072617 8166257 := bstep (se 2 (by rfl) ⟨3062346, by rfl⟩ : syracuseStep 8166257 = 6124693) B6124693
theorem B1612673 : Blo 1072617 1612673 := bstep (se 2 (by rfl) ⟨604752, by rfl⟩ : syracuseStep 1612673 = 1209505) B1209505
theorem B1612691 : Blo 1072617 1612691 := bstep (se 1 (by rfl) ⟨1209518, by rfl⟩ : syracuseStep 1612691 = 2419037) B2419037
theorem B1612721 : Blo 1072617 1612721 := bstep (se 2 (by rfl) ⟨604770, by rfl⟩ : syracuseStep 1612721 = 1209541) B1209541
theorem B1612739 : Blo 1072617 1612739 := bstep (se 1 (by rfl) ⟨1209554, by rfl⟩ : syracuseStep 1612739 = 2419109) B2419109
theorem B1612769 : Blo 1072617 1612769 := bstep (se 2 (by rfl) ⟨604788, by rfl⟩ : syracuseStep 1612769 = 1209577) B1209577
theorem B1612787 : Blo 1072617 1612787 := bstep (se 1 (by rfl) ⟨1209590, by rfl⟩ : syracuseStep 1612787 = 2419181) B2419181
theorem B1612817 : Blo 1072617 1612817 := bstep (se 2 (by rfl) ⟨604806, by rfl⟩ : syracuseStep 1612817 = 1209613) B1209613
theorem B1612835 : Blo 1072617 1612835 := bstep (se 1 (by rfl) ⟨1209626, by rfl⟩ : syracuseStep 1612835 = 2419253) B2419253
theorem B1612865 : Blo 1072617 1612865 := bstep (se 2 (by rfl) ⟨604824, by rfl⟩ : syracuseStep 1612865 = 1209649) B1209649
theorem B1612883 : Blo 1072617 1612883 := bstep (se 1 (by rfl) ⟨1209662, by rfl⟩ : syracuseStep 1612883 = 2419325) B2419325
theorem B1612913 : Blo 1072617 1612913 := bstep (se 2 (by rfl) ⟨604842, by rfl⟩ : syracuseStep 1612913 = 1209685) B1209685
theorem B1612931 : Blo 1072617 1612931 := bstep (se 1 (by rfl) ⟨1209698, by rfl⟩ : syracuseStep 1612931 = 2419397) B2419397
theorem B1612961 : Blo 1072617 1612961 := bstep (se 2 (by rfl) ⟨604860, by rfl⟩ : syracuseStep 1612961 = 1209721) B1209721
theorem B1612979 : Blo 1072617 1612979 := bstep (se 1 (by rfl) ⟨1209734, by rfl⟩ : syracuseStep 1612979 = 2419469) B2419469
theorem B9575621 : Blo 1072617 9575621 := bstep (se 4 (by rfl) ⟨897714, by rfl⟩ : syracuseStep 9575621 = 1795429) B1795429
theorem B3873997 : Blo 1072617 3873997 := bstep (se 3 (by rfl) ⟨726374, by rfl⟩ : syracuseStep 3873997 = 1452749) B1452749
theorem B1613009 : Blo 1072617 1613009 := bstep (se 2 (by rfl) ⟨604878, by rfl⟩ : syracuseStep 1613009 = 1209757) B1209757
theorem B1613027 : Blo 1072617 1613027 := bstep (se 1 (by rfl) ⟨1209770, by rfl⟩ : syracuseStep 1613027 = 2419541) B2419541
theorem B3054829 : Blo 1072617 3054829 := bstep (se 3 (by rfl) ⟨572780, by rfl⟩ : syracuseStep 3054829 = 1145561) B1145561
theorem B1613057 : Blo 1072617 1613057 := bstep (se 2 (by rfl) ⟨604896, by rfl⟩ : syracuseStep 1613057 = 1209793) B1209793
theorem B5446925 : Blo 1072617 5446925 := bstep (se 3 (by rfl) ⟨1021298, by rfl⟩ : syracuseStep 5446925 = 2042597) B2042597
theorem B1613075 : Blo 1072617 1613075 := bstep (se 1 (by rfl) ⟨1209806, by rfl⟩ : syracuseStep 1613075 = 2419613) B2419613
theorem B2039089 : Blo 1072617 2039089 := bstep (se 2 (by rfl) ⟨764658, by rfl⟩ : syracuseStep 2039089 = 1529317) B1529317
theorem B1613105 : Blo 1072617 1613105 := bstep (se 2 (by rfl) ⟨604914, by rfl⟩ : syracuseStep 1613105 = 1209829) B1209829
theorem B1613123 : Blo 1072617 1613123 := bstep (se 1 (by rfl) ⟨1209842, by rfl⟩ : syracuseStep 1613123 = 2419685) B2419685
theorem B1613153 : Blo 1072617 1613153 := bstep (se 2 (by rfl) ⟨604932, by rfl⟩ : syracuseStep 1613153 = 1209865) B1209865
theorem B7839089 : Blo 1072617 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B7740785 : Blo 1072617 7740785 := bstep (se 2 (by rfl) ⟨2902794, by rfl⟩ : syracuseStep 7740785 = 5805589) B5805589
theorem B1613171 : Blo 1072617 1613171 := bstep (se 1 (by rfl) ⟨1209878, by rfl⟩ : syracuseStep 1613171 = 2419757) B2419757
theorem B3054989 : Blo 1072617 3054989 := bstep (se 3 (by rfl) ⟨572810, by rfl⟩ : syracuseStep 3054989 = 1145621) B1145621
theorem B1613201 : Blo 1072617 1613201 := bstep (se 2 (by rfl) ⟨604950, by rfl⟩ : syracuseStep 1613201 = 1209901) B1209901
theorem B1613219 : Blo 1072617 1613219 := bstep (se 1 (by rfl) ⟨1209914, by rfl⟩ : syracuseStep 1613219 = 2419829) B2419829
theorem B1613249 : Blo 1072617 1613249 := bstep (se 2 (by rfl) ⟨604968, by rfl⟩ : syracuseStep 1613249 = 1209937) B1209937
theorem B2039249 : Blo 1072617 2039249 := bstep (se 2 (by rfl) ⟨764718, by rfl⟩ : syracuseStep 2039249 = 1529437) B1529437
theorem B1613267 : Blo 1072617 1613267 := bstep (se 1 (by rfl) ⟨1209950, by rfl⟩ : syracuseStep 1613267 = 2419901) B2419901
theorem B1613297 : Blo 1072617 1613297 := bstep (se 2 (by rfl) ⟨604986, by rfl⟩ : syracuseStep 1613297 = 1209973) B1209973
theorem B1613315 : Blo 1072617 1613315 := bstep (se 1 (by rfl) ⟨1209986, by rfl⟩ : syracuseStep 1613315 = 2419973) B2419973
theorem B1613345 : Blo 1072617 1613345 := bstep (se 2 (by rfl) ⟨605004, by rfl⟩ : syracuseStep 1613345 = 1210009) B1210009
theorem B6200867 : Blo 1072617 6200867 := bstep (se 1 (by rfl) ⟨4650650, by rfl⟩ : syracuseStep 6200867 = 9301301) B9301301
theorem B1613363 : Blo 1072617 1613363 := bstep (se 1 (by rfl) ⟨1210022, by rfl⟩ : syracuseStep 1613363 = 2420045) B2420045
theorem B3055171 : Blo 1072617 3055171 := bstep (se 1 (by rfl) ⟨2291378, by rfl⟩ : syracuseStep 3055171 = 4582757) B4582757
theorem B1089091 : Blo 1072617 1089091 := bstep (se 1 (by rfl) ⟨816818, by rfl⟩ : syracuseStep 1089091 = 1633637) B1633637
theorem B7839301 : Blo 1072617 7839301 := bstep (se 4 (by rfl) ⟨734934, by rfl⟩ : syracuseStep 7839301 = 1469869) B1469869
theorem B1613393 : Blo 1072617 1613393 := bstep (se 2 (by rfl) ⟨605022, by rfl⟩ : syracuseStep 1613393 = 1210045) B1210045
theorem B1613411 : Blo 1072617 1613411 := bstep (se 1 (by rfl) ⟨1210058, by rfl⟩ : syracuseStep 1613411 = 2420117) B2420117
theorem B1613441 : Blo 1072617 1613441 := bstep (se 2 (by rfl) ⟨605040, by rfl⟩ : syracuseStep 1613441 = 1210081) B1210081
theorem B1613459 : Blo 1072617 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B1613489 : Blo 1072617 1613489 := bstep (se 2 (by rfl) ⟨605058, by rfl⟩ : syracuseStep 1613489 = 1210117) B1210117
theorem B1613507 : Blo 1072617 1613507 := bstep (se 1 (by rfl) ⟨1210130, by rfl⟩ : syracuseStep 1613507 = 2420261) B2420261
theorem B1613537 : Blo 1072617 1613537 := bstep (se 2 (by rfl) ⟨605076, by rfl⟩ : syracuseStep 1613537 = 1210153) B1210153
theorem B1810147 : Blo 1072617 1810147 := bstep (se 1 (by rfl) ⟨1357610, by rfl⟩ : syracuseStep 1810147 = 2715221) B2715221
theorem B1613555 : Blo 1072617 1613555 := bstep (se 1 (by rfl) ⟨1210166, by rfl⟩ : syracuseStep 1613555 = 2420333) B2420333
theorem B1613585 : Blo 1072617 1613585 := bstep (se 2 (by rfl) ⟨605094, by rfl⟩ : syracuseStep 1613585 = 1210189) B1210189
theorem B1613603 : Blo 1072617 1613603 := bstep (se 1 (by rfl) ⟨1210202, by rfl⟩ : syracuseStep 1613603 = 2420405) B2420405
theorem B1613633 : Blo 1072617 1613633 := bstep (se 2 (by rfl) ⟨605112, by rfl⟩ : syracuseStep 1613633 = 1210225) B1210225
theorem B12263237 : Blo 1072617 12263237 := bstep (se 4 (by rfl) ⟨1149678, by rfl⟩ : syracuseStep 12263237 = 2299357) B2299357
theorem B1613651 : Blo 1072617 1613651 := bstep (se 1 (by rfl) ⟨1210238, by rfl⟩ : syracuseStep 1613651 = 2420477) B2420477
theorem B4595555 : Blo 1072617 4595555 := bstep (se 1 (by rfl) ⟨3446666, by rfl⟩ : syracuseStep 4595555 = 6893333) B6893333
theorem B2039651 : Blo 1072617 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B1449841 : Blo 1072617 1449841 := bstep (se 2 (by rfl) ⟨543690, by rfl⟩ : syracuseStep 1449841 = 1087381) B1087381
theorem B1810289 : Blo 1072617 1810289 := bstep (se 2 (by rfl) ⟨678858, by rfl⟩ : syracuseStep 1810289 = 1357717) B1357717
theorem B1613681 : Blo 1072617 1613681 := bstep (se 2 (by rfl) ⟨605130, by rfl⟩ : syracuseStep 1613681 = 1210261) B1210261
theorem B1548163 : Blo 1072617 1548163 := bstep (se 1 (by rfl) ⟨1161122, by rfl⟩ : syracuseStep 1548163 = 2322245) B2322245
theorem B1613699 : Blo 1072617 1613699 := bstep (se 1 (by rfl) ⟨1210274, by rfl⟩ : syracuseStep 1613699 = 2420549) B2420549
theorem B1613729 : Blo 1072617 1613729 := bstep (se 2 (by rfl) ⟨605148, by rfl⟩ : syracuseStep 1613729 = 1210297) B1210297
theorem B1613747 : Blo 1072617 1613747 := bstep (se 1 (by rfl) ⟨1210310, by rfl⟩ : syracuseStep 1613747 = 2420621) B2420621
theorem B3448781 : Blo 1072617 3448781 := bstep (se 3 (by rfl) ⟨646646, by rfl⟩ : syracuseStep 3448781 = 1293293) B1293293
theorem B1613777 : Blo 1072617 1613777 := bstep (se 2 (by rfl) ⟨605166, by rfl⟩ : syracuseStep 1613777 = 1210333) B1210333
theorem B1613795 : Blo 1072617 1613795 := bstep (se 1 (by rfl) ⟨1210346, by rfl⟩ : syracuseStep 1613795 = 2420693) B2420693
theorem B1810417 : Blo 1072617 1810417 := bstep (se 2 (by rfl) ⟨678906, by rfl⟩ : syracuseStep 1810417 = 1357813) B1357813
theorem B1613825 : Blo 1072617 1613825 := bstep (se 2 (by rfl) ⟨605184, by rfl⟩ : syracuseStep 1613825 = 1210369) B1210369
theorem B1810451 : Blo 1072617 1810451 := bstep (se 1 (by rfl) ⟨1357838, by rfl⟩ : syracuseStep 1810451 = 2715677) B2715677
theorem B1613843 : Blo 1072617 1613843 := bstep (se 1 (by rfl) ⟨1210382, by rfl⟩ : syracuseStep 1613843 = 2420765) B2420765
theorem B1613873 : Blo 1072617 1613873 := bstep (se 2 (by rfl) ⟨605202, by rfl⟩ : syracuseStep 1613873 = 1210405) B1210405
theorem B1613891 : Blo 1072617 1613891 := bstep (se 1 (by rfl) ⟨1210418, by rfl⟩ : syracuseStep 1613891 = 2420837) B2420837
theorem B1613921 : Blo 1072617 1613921 := bstep (se 2 (by rfl) ⟨605220, by rfl⟩ : syracuseStep 1613921 = 1210441) B1210441
theorem B1613939 : Blo 1072617 1613939 := bstep (se 1 (by rfl) ⟨1210454, by rfl⟩ : syracuseStep 1613939 = 2420909) B2420909
theorem B1613969 : Blo 1072617 1613969 := bstep (se 2 (by rfl) ⟨605238, by rfl⟩ : syracuseStep 1613969 = 1210477) B1210477
theorem B1810579 : Blo 1072617 1810579 := bstep (se 1 (by rfl) ⟨1357934, by rfl⟩ : syracuseStep 1810579 = 2715869) B2715869
theorem B1613987 : Blo 1072617 1613987 := bstep (se 1 (by rfl) ⟨1210490, by rfl⟩ : syracuseStep 1613987 = 2420981) B2420981
theorem B1614017 : Blo 1072617 1614017 := bstep (se 2 (by rfl) ⟨605256, by rfl⟩ : syracuseStep 1614017 = 1210513) B1210513
theorem B1614035 : Blo 1072617 1614035 := bstep (se 1 (by rfl) ⟨1210526, by rfl⟩ : syracuseStep 1614035 = 2421053) B2421053
theorem B1745137 : Blo 1072617 1745137 := bstep (se 2 (by rfl) ⟨654426, by rfl⟩ : syracuseStep 1745137 = 1308853) B1308853
theorem B1614065 : Blo 1072617 1614065 := bstep (se 2 (by rfl) ⟨605274, by rfl⟩ : syracuseStep 1614065 = 1210549) B1210549
theorem B1614083 : Blo 1072617 1614083 := bstep (se 1 (by rfl) ⟨1210562, by rfl⟩ : syracuseStep 1614083 = 2421125) B2421125
theorem B1810721 : Blo 1072617 1810721 := bstep (se 2 (by rfl) ⟨679020, by rfl⟩ : syracuseStep 1810721 = 1358041) B1358041
theorem B1614113 : Blo 1072617 1614113 := bstep (se 2 (by rfl) ⟨605292, by rfl⟩ : syracuseStep 1614113 = 1210585) B1210585
theorem B1614131 : Blo 1072617 1614131 := bstep (se 1 (by rfl) ⟨1210598, by rfl⟩ : syracuseStep 1614131 = 2421197) B2421197
theorem B1614161 : Blo 1072617 1614161 := bstep (se 2 (by rfl) ⟨605310, by rfl⟩ : syracuseStep 1614161 = 1210621) B1210621
theorem B1614179 : Blo 1072617 1614179 := bstep (se 1 (by rfl) ⟨1210634, by rfl⟩ : syracuseStep 1614179 = 2421269) B2421269
theorem B1614209 : Blo 1072617 1614209 := bstep (se 2 (by rfl) ⟨605328, by rfl⟩ : syracuseStep 1614209 = 1210657) B1210657
theorem B1614227 : Blo 1072617 1614227 := bstep (se 1 (by rfl) ⟨1210670, by rfl⟩ : syracuseStep 1614227 = 2421341) B2421341
theorem B1810849 : Blo 1072617 1810849 := bstep (se 2 (by rfl) ⟨679068, by rfl⟩ : syracuseStep 1810849 = 1358137) B1358137
theorem B1614257 : Blo 1072617 1614257 := bstep (se 2 (by rfl) ⟨605346, by rfl⟩ : syracuseStep 1614257 = 1210693) B1210693
theorem B1548739 : Blo 1072617 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1810883 : Blo 1072617 1810883 := bstep (se 1 (by rfl) ⟨1358162, by rfl⟩ : syracuseStep 1810883 = 2716325) B2716325
theorem B1450435 : Blo 1072617 1450435 := bstep (se 1 (by rfl) ⟨1087826, by rfl⟩ : syracuseStep 1450435 = 2175653) B2175653
theorem B1614275 : Blo 1072617 1614275 := bstep (se 1 (by rfl) ⟨1210706, by rfl⟩ : syracuseStep 1614275 = 2421413) B2421413
theorem B1614305 : Blo 1072617 1614305 := bstep (se 2 (by rfl) ⟨605364, by rfl⟩ : syracuseStep 1614305 = 1210729) B1210729
theorem B1614323 : Blo 1072617 1614323 := bstep (se 1 (by rfl) ⟨1210742, by rfl⟩ : syracuseStep 1614323 = 2421485) B2421485
theorem B1614353 : Blo 1072617 1614353 := bstep (se 2 (by rfl) ⟨605382, by rfl⟩ : syracuseStep 1614353 = 1210765) B1210765
theorem B1614371 : Blo 1072617 1614371 := bstep (se 1 (by rfl) ⟨1210778, by rfl⟩ : syracuseStep 1614371 = 2421557) B2421557
theorem B1614401 : Blo 1072617 1614401 := bstep (se 2 (by rfl) ⟨605400, by rfl⟩ : syracuseStep 1614401 = 1210801) B1210801
theorem B1811011 : Blo 1072617 1811011 := bstep (se 1 (by rfl) ⟨1358258, by rfl⟩ : syracuseStep 1811011 = 2716517) B2716517
theorem B1614419 : Blo 1072617 1614419 := bstep (se 1 (by rfl) ⟨1210814, by rfl⟩ : syracuseStep 1614419 = 2421629) B2421629
theorem B1614449 : Blo 1072617 1614449 := bstep (se 2 (by rfl) ⟨605418, by rfl⟩ : syracuseStep 1614449 = 1210837) B1210837
theorem B1614467 : Blo 1072617 1614467 := bstep (se 1 (by rfl) ⟨1210850, by rfl⟩ : syracuseStep 1614467 = 2421701) B2421701
theorem B1614497 : Blo 1072617 1614497 := bstep (se 2 (by rfl) ⟨605436, by rfl⟩ : syracuseStep 1614497 = 1210873) B1210873
theorem B1614515 : Blo 1072617 1614515 := bstep (se 1 (by rfl) ⟨1210886, by rfl⟩ : syracuseStep 1614515 = 2421773) B2421773
theorem B1811153 : Blo 1072617 1811153 := bstep (se 2 (by rfl) ⟨679182, by rfl⟩ : syracuseStep 1811153 = 1358365) B1358365
theorem B1614545 : Blo 1072617 1614545 := bstep (se 2 (by rfl) ⟨605454, by rfl⟩ : syracuseStep 1614545 = 1210909) B1210909
theorem B2040547 : Blo 1072617 2040547 := bstep (se 1 (by rfl) ⟨1530410, by rfl⟩ : syracuseStep 2040547 = 3060821) B3060821
theorem B1614563 : Blo 1072617 1614563 := bstep (se 1 (by rfl) ⟨1210922, by rfl⟩ : syracuseStep 1614563 = 2421845) B2421845
theorem B1614593 : Blo 1072617 1614593 := bstep (se 2 (by rfl) ⟨605472, by rfl⟩ : syracuseStep 1614593 = 1210945) B1210945
theorem B1614611 : Blo 1072617 1614611 := bstep (se 1 (by rfl) ⟨1210958, by rfl⟩ : syracuseStep 1614611 = 2421917) B2421917
theorem B1614641 : Blo 1072617 1614641 := bstep (se 2 (by rfl) ⟨605490, by rfl⟩ : syracuseStep 1614641 = 1210981) B1210981
theorem B1614659 : Blo 1072617 1614659 := bstep (se 1 (by rfl) ⟨1210994, by rfl⟩ : syracuseStep 1614659 = 2421989) B2421989
theorem B1811281 : Blo 1072617 1811281 := bstep (se 2 (by rfl) ⟨679230, by rfl⟩ : syracuseStep 1811281 = 1358461) B1358461
theorem B1614689 : Blo 1072617 1614689 := bstep (se 2 (by rfl) ⟨605508, by rfl⟩ : syracuseStep 1614689 = 1211017) B1211017
theorem B1811315 : Blo 1072617 1811315 := bstep (se 1 (by rfl) ⟨1358486, by rfl⟩ : syracuseStep 1811315 = 2716973) B2716973
theorem B1614707 : Blo 1072617 1614707 := bstep (se 1 (by rfl) ⟨1211030, by rfl⟩ : syracuseStep 1614707 = 2422061) B2422061
theorem B2040707 : Blo 1072617 2040707 := bstep (se 1 (by rfl) ⟨1530530, by rfl⟩ : syracuseStep 2040707 = 3061061) B3061061
theorem B1614737 : Blo 1072617 1614737 := bstep (se 2 (by rfl) ⟨605526, by rfl⟩ : syracuseStep 1614737 = 1211053) B1211053
theorem B1614755 : Blo 1072617 1614755 := bstep (se 1 (by rfl) ⟨1211066, by rfl⟩ : syracuseStep 1614755 = 2422133) B2422133
theorem B3056561 : Blo 1072617 3056561 := bstep (se 2 (by rfl) ⟨1146210, by rfl⟩ : syracuseStep 3056561 = 2292421) B2292421
theorem B1614785 : Blo 1072617 1614785 := bstep (se 2 (by rfl) ⟨605544, by rfl⟩ : syracuseStep 1614785 = 1211089) B1211089
theorem B1614803 : Blo 1072617 1614803 := bstep (se 1 (by rfl) ⟨1211102, by rfl⟩ : syracuseStep 1614803 = 2422205) B2422205
theorem B1614833 : Blo 1072617 1614833 := bstep (se 2 (by rfl) ⟨605562, by rfl⟩ : syracuseStep 1614833 = 1211125) B1211125
theorem B1811443 : Blo 1072617 1811443 := bstep (se 1 (by rfl) ⟨1358582, by rfl⟩ : syracuseStep 1811443 = 2717165) B2717165
theorem B1614851 : Blo 1072617 1614851 := bstep (se 1 (by rfl) ⟨1211138, by rfl⟩ : syracuseStep 1614851 = 2422277) B2422277
theorem B1614881 : Blo 1072617 1614881 := bstep (se 2 (by rfl) ⟨605580, by rfl⟩ : syracuseStep 1614881 = 1211161) B1211161
theorem B1614899 : Blo 1072617 1614899 := bstep (se 1 (by rfl) ⟨1211174, by rfl⟩ : syracuseStep 1614899 = 2422349) B2422349
theorem B1811585 : Blo 1072617 1811585 := bstep (se 2 (by rfl) ⟨679344, by rfl⟩ : syracuseStep 1811585 = 1358689) B1358689
theorem B10200305 : Blo 1072617 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B1811713 : Blo 1072617 1811713 := bstep (se 2 (by rfl) ⟨679392, by rfl⟩ : syracuseStep 1811713 = 1358785) B1358785
theorem B1811747 : Blo 1072617 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B1811875 : Blo 1072617 1811875 := bstep (se 1 (by rfl) ⟨1358906, by rfl⟩ : syracuseStep 1811875 = 2717813) B2717813
theorem B13608461 : Blo 1072617 13608461 := bstep (se 3 (by rfl) ⟨2551586, by rfl⟩ : syracuseStep 13608461 = 5103173) B5103173
theorem B1812017 : Blo 1072617 1812017 := bstep (se 2 (by rfl) ⟨679506, by rfl⟩ : syracuseStep 1812017 = 1359013) B1359013
theorem B3679843 : Blo 1072617 3679843 := bstep (se 1 (by rfl) ⟨2759882, by rfl⟩ : syracuseStep 3679843 = 5519765) B5519765
theorem B1812145 : Blo 1072617 1812145 := bstep (se 2 (by rfl) ⟨679554, by rfl⟩ : syracuseStep 1812145 = 1359109) B1359109
theorem B1812179 : Blo 1072617 1812179 := bstep (se 1 (by rfl) ⟨1359134, by rfl⟩ : syracuseStep 1812179 = 2718269) B2718269
theorem B4597553 : Blo 1072617 4597553 := bstep (se 2 (by rfl) ⟨1724082, by rfl⟩ : syracuseStep 4597553 = 3448165) B3448165
theorem B1812307 : Blo 1072617 1812307 := bstep (se 1 (by rfl) ⟨1359230, by rfl⟩ : syracuseStep 1812307 = 2718461) B2718461
theorem B3057517 : Blo 1072617 3057517 := bstep (se 3 (by rfl) ⟨573284, by rfl⟩ : syracuseStep 3057517 = 1146569) B1146569
theorem B12593009 : Blo 1072617 12593009 := bstep (se 2 (by rfl) ⟨4722378, by rfl⟩ : syracuseStep 12593009 = 9444757) B9444757
theorem B2041777 : Blo 1072617 2041777 := bstep (se 2 (by rfl) ⟨765666, by rfl⟩ : syracuseStep 2041777 = 1531333) B1531333
theorem B1812449 : Blo 1072617 1812449 := bstep (se 2 (by rfl) ⟨679668, by rfl⟩ : syracuseStep 1812449 = 1359337) B1359337
theorem B6531043 : Blo 1072617 6531043 := bstep (se 1 (by rfl) ⟨4898282, by rfl⟩ : syracuseStep 6531043 = 9796565) B9796565
theorem B3057745 : Blo 1072617 3057745 := bstep (se 2 (by rfl) ⟨1146654, by rfl⟩ : syracuseStep 3057745 = 2293309) B2293309
theorem B1812577 : Blo 1072617 1812577 := bstep (se 2 (by rfl) ⟨679716, by rfl⟩ : syracuseStep 1812577 = 1359433) B1359433
theorem B5449841 : Blo 1072617 5449841 := bstep (se 2 (by rfl) ⟨2043690, by rfl⟩ : syracuseStep 5449841 = 4087381) B4087381
theorem B1812611 : Blo 1072617 1812611 := bstep (se 1 (by rfl) ⟨1359458, by rfl⟩ : syracuseStep 1812611 = 2718917) B2718917
theorem B3057905 : Blo 1072617 3057905 := bstep (se 2 (by rfl) ⟨1146714, by rfl⟩ : syracuseStep 3057905 = 2293429) B2293429
theorem B1812739 : Blo 1072617 1812739 := bstep (se 1 (by rfl) ⟨1359554, by rfl⟩ : syracuseStep 1812739 = 2719109) B2719109
theorem B3058019 : Blo 1072617 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B1812881 : Blo 1072617 1812881 := bstep (se 2 (by rfl) ⟨679830, by rfl⟩ : syracuseStep 1812881 = 1359661) B1359661
theorem B1813009 : Blo 1072617 1813009 := bstep (se 2 (by rfl) ⟨679878, by rfl⟩ : syracuseStep 1813009 = 1359757) B1359757
theorem B1452593 : Blo 1072617 1452593 := bstep (se 2 (by rfl) ⟨544722, by rfl⟩ : syracuseStep 1452593 = 1089445) B1089445
theorem B1813043 : Blo 1072617 1813043 := bstep (se 1 (by rfl) ⟨1359782, by rfl⟩ : syracuseStep 1813043 = 2719565) B2719565
theorem B1813171 : Blo 1072617 1813171 := bstep (se 1 (by rfl) ⟨1359878, by rfl⟩ : syracuseStep 1813171 = 2719757) B2719757
theorem B1223363 : Blo 1072617 1223363 := bstep (se 1 (by rfl) ⟨917522, by rfl⟩ : syracuseStep 1223363 = 1835045) B1835045
theorem B6892229 : Blo 1072617 6892229 := bstep (se 4 (by rfl) ⟨646146, by rfl⟩ : syracuseStep 6892229 = 1292293) B1292293
theorem B4598477 : Blo 1072617 4598477 := bstep (se 3 (by rfl) ⟨862214, by rfl⟩ : syracuseStep 4598477 = 1724429) B1724429
theorem B14920433 : Blo 1072617 14920433 := bstep (se 2 (by rfl) ⟨5595162, by rfl⟩ : syracuseStep 14920433 = 11190325) B11190325
theorem B1813313 : Blo 1072617 1813313 := bstep (se 2 (by rfl) ⟨679992, by rfl⟩ : syracuseStep 1813313 = 1359985) B1359985
theorem B1813441 : Blo 1072617 1813441 := bstep (se 2 (by rfl) ⟨680040, by rfl⟩ : syracuseStep 1813441 = 1360081) B1360081
theorem B12430277 : Blo 1072617 12430277 := bstep (se 4 (by rfl) ⟨1165338, by rfl⟩ : syracuseStep 12430277 = 2330677) B2330677
theorem B2042833 : Blo 1072617 2042833 := bstep (se 2 (by rfl) ⟨766062, by rfl⟩ : syracuseStep 2042833 = 1532125) B1532125
theorem B1813475 : Blo 1072617 1813475 := bstep (se 1 (by rfl) ⟨1360106, by rfl⟩ : syracuseStep 1813475 = 2720213) B2720213
theorem B3877859 : Blo 1072617 3877859 := bstep (se 1 (by rfl) ⟨2908394, by rfl⟩ : syracuseStep 3877859 = 5816789) B5816789
theorem B1813603 : Blo 1072617 1813603 := bstep (se 1 (by rfl) ⟨1360202, by rfl⟩ : syracuseStep 1813603 = 2720405) B2720405
theorem B1813745 : Blo 1072617 1813745 := bstep (se 2 (by rfl) ⟨680154, by rfl⟩ : syracuseStep 1813745 = 1360309) B1360309
theorem B3059021 : Blo 1072617 3059021 := bstep (se 3 (by rfl) ⟨573566, by rfl⟩ : syracuseStep 3059021 = 1147133) B1147133
theorem B2043235 : Blo 1072617 2043235 := bstep (se 1 (by rfl) ⟨1532426, by rfl⟩ : syracuseStep 2043235 = 3064853) B3064853
theorem B1813873 : Blo 1072617 1813873 := bstep (se 2 (by rfl) ⟨680202, by rfl⟩ : syracuseStep 1813873 = 1360405) B1360405
theorem B2043281 : Blo 1072617 2043281 := bstep (se 2 (by rfl) ⟨766230, by rfl⟩ : syracuseStep 2043281 = 1532461) B1532461
theorem B1813907 : Blo 1072617 1813907 := bstep (se 1 (by rfl) ⟨1360430, by rfl⟩ : syracuseStep 1813907 = 2720861) B2720861
theorem B3059203 : Blo 1072617 3059203 := bstep (se 1 (by rfl) ⟨2294402, by rfl⟩ : syracuseStep 3059203 = 4588805) B4588805
theorem B1814035 : Blo 1072617 1814035 := bstep (se 1 (by rfl) ⟨1360526, by rfl⟩ : syracuseStep 1814035 = 2721053) B2721053
theorem B1814177 : Blo 1072617 1814177 := bstep (se 2 (by rfl) ⟨680316, by rfl⟩ : syracuseStep 1814177 = 1360633) B1360633
theorem B3059363 : Blo 1072617 3059363 := bstep (se 1 (by rfl) ⟨2294522, by rfl⟩ : syracuseStep 3059363 = 4589045) B4589045
theorem B2043569 : Blo 1072617 2043569 := bstep (se 2 (by rfl) ⟨766338, by rfl⟩ : syracuseStep 2043569 = 1532677) B1532677
theorem B1814305 : Blo 1072617 1814305 := bstep (se 2 (by rfl) ⟨680364, by rfl⟩ : syracuseStep 1814305 = 1360729) B1360729
theorem B1814339 : Blo 1072617 1814339 := bstep (se 1 (by rfl) ⟨1360754, by rfl⟩ : syracuseStep 1814339 = 2721509) B2721509
theorem B1814467 : Blo 1072617 1814467 := bstep (se 1 (by rfl) ⟨1360850, by rfl⟩ : syracuseStep 1814467 = 2721701) B2721701
theorem B13774819 : Blo 1072617 13774819 := bstep (se 1 (by rfl) ⟨10331114, by rfl⟩ : syracuseStep 13774819 = 20662229) B20662229
theorem B4075505 : Blo 1072617 4075505 := bstep (se 2 (by rfl) ⟨1528314, by rfl⟩ : syracuseStep 4075505 = 3056629) B3056629
theorem B1814609 : Blo 1072617 1814609 := bstep (se 2 (by rfl) ⟨680478, by rfl⟩ : syracuseStep 1814609 = 1360957) B1360957
theorem B1814737 : Blo 1072617 1814737 := bstep (se 2 (by rfl) ⟨680526, by rfl⟩ : syracuseStep 1814737 = 1361053) B1361053
theorem B1814771 : Blo 1072617 1814771 := bstep (se 1 (by rfl) ⟨1361078, by rfl⟩ : syracuseStep 1814771 = 2722157) B2722157
theorem B1814899 : Blo 1072617 1814899 := bstep (se 1 (by rfl) ⟨1361174, by rfl⟩ : syracuseStep 1814899 = 2722349) B2722349
theorem B1290659 : Blo 1072617 1290659 := bstep (se 1 (by rfl) ⟨967994, by rfl⟩ : syracuseStep 1290659 = 1935989) B1935989
theorem B1815041 : Blo 1072617 1815041 := bstep (se 2 (by rfl) ⟨680640, by rfl⟩ : syracuseStep 1815041 = 1361281) B1361281
theorem B1815169 : Blo 1072617 1815169 := bstep (se 2 (by rfl) ⟨680688, by rfl⟩ : syracuseStep 1815169 = 1361377) B1361377
theorem B1815203 : Blo 1072617 1815203 := bstep (se 1 (by rfl) ⟨1361402, by rfl⟩ : syracuseStep 1815203 = 2722805) B2722805
theorem B1454755 : Blo 1072617 1454755 := bstep (se 1 (by rfl) ⟨1091066, by rfl⟩ : syracuseStep 1454755 = 2182133) B2182133
theorem B1454771 : Blo 1072617 1454771 := bstep (se 1 (by rfl) ⟨1091078, by rfl⟩ : syracuseStep 1454771 = 2182157) B2182157
theorem B3060433 : Blo 1072617 3060433 := bstep (se 2 (by rfl) ⟨1147662, by rfl⟩ : syracuseStep 3060433 = 2295325) B2295325
theorem B1815331 : Blo 1072617 1815331 := bstep (se 1 (by rfl) ⟨1361498, by rfl⟩ : syracuseStep 1815331 = 2722997) B2722997
theorem B1815473 : Blo 1072617 1815473 := bstep (se 2 (by rfl) ⟨680802, by rfl⟩ : syracuseStep 1815473 = 1361605) B1361605
theorem B1815601 : Blo 1072617 1815601 := bstep (se 2 (by rfl) ⟨680850, by rfl⟩ : syracuseStep 1815601 = 1361701) B1361701
theorem B1815635 : Blo 1072617 1815635 := bstep (se 1 (by rfl) ⟨1361726, by rfl⟩ : syracuseStep 1815635 = 2723453) B2723453
theorem B1815763 : Blo 1072617 1815763 := bstep (se 1 (by rfl) ⟨1361822, by rfl⟩ : syracuseStep 1815763 = 2723645) B2723645
theorem B6534449 : Blo 1072617 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B3487043 : Blo 1072617 3487043 := bstep (se 1 (by rfl) ⟨2615282, by rfl⟩ : syracuseStep 3487043 = 5230565) B5230565
theorem B1815905 : Blo 1072617 1815905 := bstep (se 2 (by rfl) ⟨680964, by rfl⟩ : syracuseStep 1815905 = 1361929) B1361929
theorem B4076963 : Blo 1072617 4076963 := bstep (se 1 (by rfl) ⟨3057722, by rfl⟩ : syracuseStep 4076963 = 6115445) B6115445
theorem B1816033 : Blo 1072617 1816033 := bstep (se 2 (by rfl) ⟨681012, by rfl⟩ : syracuseStep 1816033 = 1362025) B1362025
theorem B20624867 : Blo 1072617 20624867 := bstep (se 1 (by rfl) ⟨15468650, by rfl⟩ : syracuseStep 20624867 = 30937301) B30937301
theorem B1816067 : Blo 1072617 1816067 := bstep (se 1 (by rfl) ⟨1362050, by rfl⟩ : syracuseStep 1816067 = 2724101) B2724101
theorem B5813765 : Blo 1072617 5813765 := bstep (se 4 (by rfl) ⟨545040, by rfl⟩ : syracuseStep 5813765 = 1090081) B1090081
theorem B2176561 : Blo 1072617 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B3487313 : Blo 1072617 3487313 := bstep (se 2 (by rfl) ⟨1307742, by rfl⟩ : syracuseStep 3487313 = 2615485) B2615485
theorem B1816195 : Blo 1072617 1816195 := bstep (se 1 (by rfl) ⟨1362146, by rfl⟩ : syracuseStep 1816195 = 2724293) B2724293
theorem B11024099 : Blo 1072617 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B1357555 : Blo 1072617 1357555 := bstep (se 1 (by rfl) ⟨1018166, by rfl⟩ : syracuseStep 1357555 = 2036333) B2036333
theorem B1816337 : Blo 1072617 1816337 := bstep (se 2 (by rfl) ⟨681126, by rfl⟩ : syracuseStep 1816337 = 1362253) B1362253
theorem B6534989 : Blo 1072617 6534989 := bstep (se 3 (by rfl) ⟨1225310, by rfl⟩ : syracuseStep 6534989 = 2450621) B2450621
theorem B1357651 : Blo 1072617 1357651 := bstep (se 1 (by rfl) ⟨1018238, by rfl⟩ : syracuseStep 1357651 = 2036477) B2036477
theorem B1816465 : Blo 1072617 1816465 := bstep (se 2 (by rfl) ⟨681174, by rfl⟩ : syracuseStep 1816465 = 1362349) B1362349
theorem B3192721 : Blo 1072617 3192721 := bstep (se 2 (by rfl) ⟨1197270, by rfl⟩ : syracuseStep 3192721 = 2394541) B2394541
theorem B1816499 : Blo 1072617 1816499 := bstep (se 1 (by rfl) ⟨1362374, by rfl⟩ : syracuseStep 1816499 = 2724749) B2724749
theorem B3061709 : Blo 1072617 3061709 := bstep (se 3 (by rfl) ⟨574070, by rfl⟩ : syracuseStep 3061709 = 1148141) B1148141
theorem B6535181 : Blo 1072617 6535181 := bstep (se 3 (by rfl) ⟨1225346, by rfl⟩ : syracuseStep 6535181 = 2450693) B2450693
theorem B1816627 : Blo 1072617 1816627 := bstep (se 1 (by rfl) ⟨1362470, by rfl⟩ : syracuseStep 1816627 = 2724941) B2724941
theorem B2799697 : Blo 1072617 2799697 := bstep (se 2 (by rfl) ⟨1049886, by rfl⟩ : syracuseStep 2799697 = 2099773) B2099773
theorem B3061891 : Blo 1072617 3061891 := bstep (se 1 (by rfl) ⟨2296418, by rfl⟩ : syracuseStep 3061891 = 4592837) B4592837
theorem B5814413 : Blo 1072617 5814413 := bstep (se 3 (by rfl) ⟨1090202, by rfl⟩ : syracuseStep 5814413 = 2180405) B2180405
theorem B3061937 : Blo 1072617 3061937 := bstep (se 2 (by rfl) ⟨1148226, by rfl⟩ : syracuseStep 3061937 = 2296453) B2296453
theorem B6895793 : Blo 1072617 6895793 := bstep (se 2 (by rfl) ⟨2585922, by rfl⟩ : syracuseStep 6895793 = 5171845) B5171845
theorem B1816769 : Blo 1072617 1816769 := bstep (se 2 (by rfl) ⟨681288, by rfl⟩ : syracuseStep 1816769 = 1362577) B1362577
theorem B1358147 : Blo 1072617 1358147 := bstep (se 1 (by rfl) ⟨1018610, by rfl⟩ : syracuseStep 1358147 = 2037221) B2037221
theorem B4962637 : Blo 1072617 4962637 := bstep (se 3 (by rfl) ⟨930494, by rfl⟩ : syracuseStep 4962637 = 1860989) B1860989
theorem B4077965 : Blo 1072617 4077965 := bstep (se 3 (by rfl) ⟨764618, by rfl⟩ : syracuseStep 4077965 = 1529237) B1529237
theorem B1718675 : Blo 1072617 1718675 := bstep (se 1 (by rfl) ⟨1289006, by rfl⟩ : syracuseStep 1718675 = 2578013) B2578013
theorem B1292707 : Blo 1072617 1292707 := bstep (se 1 (by rfl) ⟨969530, by rfl⟩ : syracuseStep 1292707 = 1939061) B1939061
theorem B1292755 : Blo 1072617 1292755 := bstep (se 1 (by rfl) ⟨969566, by rfl⟩ : syracuseStep 1292755 = 1939133) B1939133
theorem B1718977 : Blo 1072617 1718977 := bstep (se 2 (by rfl) ⟨644616, by rfl⟩ : syracuseStep 1718977 = 1289233) B1289233
theorem B2177923 : Blo 1072617 2177923 := bstep (se 1 (by rfl) ⟨1633442, by rfl⟩ : syracuseStep 2177923 = 3266885) B3266885
theorem B1719187 : Blo 1072617 1719187 := bstep (se 1 (by rfl) ⟨1289390, by rfl⟩ : syracuseStep 1719187 = 2578781) B2578781
theorem B1719233 : Blo 1072617 1719233 := bstep (se 2 (by rfl) ⟨644712, by rfl⟩ : syracuseStep 1719233 = 1289425) B1289425
theorem B3488707 : Blo 1072617 3488707 := bstep (se 1 (by rfl) ⟨2616530, by rfl⟩ : syracuseStep 3488707 = 5233061) B5233061
theorem B1358851 : Blo 1072617 1358851 := bstep (se 1 (by rfl) ⟨1019138, by rfl⟩ : syracuseStep 1358851 = 2038277) B2038277
theorem B1358947 : Blo 1072617 1358947 := bstep (se 1 (by rfl) ⟨1019210, by rfl⟩ : syracuseStep 1358947 = 2038421) B2038421
theorem B3620429 : Blo 1072617 3620429 := bstep (se 3 (by rfl) ⟨678830, by rfl⟩ : syracuseStep 3620429 = 1357661) B1357661
theorem B1359443 : Blo 1072617 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B5815907 : Blo 1072617 5815907 := bstep (se 1 (by rfl) ⟨4361930, by rfl⟩ : syracuseStep 5815907 = 8723861) B8723861
theorem B3063395 : Blo 1072617 3063395 := bstep (se 1 (by rfl) ⟨2297546, by rfl⟩ : syracuseStep 3063395 = 4595093) B4595093
theorem B6897251 : Blo 1072617 6897251 := bstep (se 1 (by rfl) ⟨5172938, by rfl⟩ : syracuseStep 6897251 = 10345877) B10345877
theorem B3620483 : Blo 1072617 3620483 := bstep (se 1 (by rfl) ⟨2715362, by rfl⟩ : syracuseStep 3620483 = 5430725) B5430725
theorem B1261363 : Blo 1072617 1261363 := bstep (se 1 (by rfl) ⟨946022, by rfl⟩ : syracuseStep 1261363 = 1892045) B1892045
theorem B3620753 : Blo 1072617 3620753 := bstep (se 2 (by rfl) ⟨1357782, by rfl⟩ : syracuseStep 3620753 = 2715565) B2715565
theorem B3358961 : Blo 1072617 3358961 := bstep (se 2 (by rfl) ⟨1259610, by rfl⟩ : syracuseStep 3358961 = 2519221) B2519221
theorem B1360147 : Blo 1072617 1360147 := bstep (se 1 (by rfl) ⟨1020110, by rfl⟩ : syracuseStep 1360147 = 2040221) B2040221
theorem B1360243 : Blo 1072617 1360243 := bstep (se 1 (by rfl) ⟨1020182, by rfl⟩ : syracuseStep 1360243 = 2040365) B2040365
theorem B1720739 : Blo 1072617 1720739 := bstep (se 1 (by rfl) ⟨1290554, by rfl⟩ : syracuseStep 1720739 = 2581109) B2581109
theorem B3621293 : Blo 1072617 3621293 := bstep (se 3 (by rfl) ⟨678992, by rfl⟩ : syracuseStep 3621293 = 1357985) B1357985
theorem B4080077 : Blo 1072617 4080077 := bstep (se 3 (by rfl) ⟨765014, by rfl⟩ : syracuseStep 4080077 = 1530029) B1530029
theorem B3621347 : Blo 1072617 3621347 := bstep (se 1 (by rfl) ⟨2716010, by rfl⟩ : syracuseStep 3621347 = 5432021) B5432021
theorem B7357061 : Blo 1072617 7357061 := bstep (se 4 (by rfl) ⟨689724, by rfl⟩ : syracuseStep 7357061 = 1379449) B1379449
theorem B1721027 : Blo 1072617 1721027 := bstep (se 1 (by rfl) ⟨1290770, by rfl⟩ : syracuseStep 1721027 = 2581541) B2581541
theorem B3621617 : Blo 1072617 3621617 := bstep (se 2 (by rfl) ⟨1358106, by rfl⟩ : syracuseStep 3621617 = 2716213) B2716213
theorem B3064625 : Blo 1072617 3064625 := bstep (se 2 (by rfl) ⟨1149234, by rfl⟩ : syracuseStep 3064625 = 2298469) B2298469
theorem B1360739 : Blo 1072617 1360739 := bstep (se 1 (by rfl) ⟨1020554, by rfl⟩ : syracuseStep 1360739 = 2041109) B2041109
theorem B2180081 : Blo 1072617 2180081 := bstep (se 2 (by rfl) ⟨817530, by rfl⟩ : syracuseStep 2180081 = 1635061) B1635061
theorem B4080881 : Blo 1072617 4080881 := bstep (se 2 (by rfl) ⟨1530330, by rfl⟩ : syracuseStep 4080881 = 3060661) B3060661
theorem B3622157 : Blo 1072617 3622157 := bstep (se 3 (by rfl) ⟨679154, by rfl⟩ : syracuseStep 3622157 = 1358309) B1358309
theorem B7062833 : Blo 1072617 7062833 := bstep (se 2 (by rfl) ⟨2648562, by rfl⟩ : syracuseStep 7062833 = 5297125) B5297125
theorem B3622211 : Blo 1072617 3622211 := bstep (se 1 (by rfl) ⟨2716658, by rfl⟩ : syracuseStep 3622211 = 5433317) B5433317
theorem B3261923 : Blo 1072617 3261923 := bstep (se 1 (by rfl) ⟨2446442, by rfl⟩ : syracuseStep 3261923 = 4892885) B4892885
theorem B1721827 : Blo 1072617 1721827 := bstep (se 1 (by rfl) ⟨1291370, by rfl⟩ : syracuseStep 1721827 = 2582741) B2582741
theorem B5817827 : Blo 1072617 5817827 := bstep (se 1 (by rfl) ⟨4363370, by rfl⟩ : syracuseStep 5817827 = 8726741) B8726741
theorem B3098125 : Blo 1072617 3098125 := bstep (se 3 (by rfl) ⟨580898, by rfl⟩ : syracuseStep 3098125 = 1161797) B1161797
theorem B1361443 : Blo 1072617 1361443 := bstep (se 1 (by rfl) ⟨1021082, by rfl⟩ : syracuseStep 1361443 = 2042165) B2042165
theorem B3622481 : Blo 1072617 3622481 := bstep (se 2 (by rfl) ⟨1358430, by rfl⟩ : syracuseStep 3622481 = 2716861) B2716861
theorem B1721969 : Blo 1072617 1721969 := bstep (se 2 (by rfl) ⟨645738, by rfl⟩ : syracuseStep 1721969 = 1291477) B1291477
theorem B1361539 : Blo 1072617 1361539 := bstep (se 1 (by rfl) ⟨1021154, by rfl⟩ : syracuseStep 1361539 = 2042309) B2042309
theorem B1722001 : Blo 1072617 1722001 := bstep (se 2 (by rfl) ⟨645750, by rfl⟩ : syracuseStep 1722001 = 1291501) B1291501
theorem B6113029 : Blo 1072617 6113029 := bstep (se 4 (by rfl) ⟨573096, by rfl⟩ : syracuseStep 6113029 = 1146193) B1146193
theorem B66209557 : Blo 1072617 66209557 := bstep (se 6 (by rfl) ⟨1551786, by rfl⟩ : syracuseStep 66209557 = 3103573) B3103573
theorem B4081549 : Blo 1072617 4081549 := bstep (se 3 (by rfl) ⟨765290, by rfl⟩ : syracuseStep 4081549 = 1530581) B1530581
theorem B13092835 : Blo 1072617 13092835 := bstep (se 1 (by rfl) ⟨9819626, by rfl⟩ : syracuseStep 13092835 = 19639253) B19639253
theorem B3623021 : Blo 1072617 3623021 := bstep (se 3 (by rfl) ⟨679316, by rfl⟩ : syracuseStep 3623021 = 1358633) B1358633
theorem B1362035 : Blo 1072617 1362035 := bstep (se 1 (by rfl) ⟨1021526, by rfl⟩ : syracuseStep 1362035 = 2043053) B2043053
theorem B3623075 : Blo 1072617 3623075 := bstep (se 1 (by rfl) ⟨2717306, by rfl⟩ : syracuseStep 3623075 = 5434613) B5434613
theorem B3623345 : Blo 1072617 3623345 := bstep (se 2 (by rfl) ⟨1358754, by rfl⟩ : syracuseStep 3623345 = 2717509) B2717509
theorem B1722929 : Blo 1072617 1722929 := bstep (se 2 (by rfl) ⟨646098, by rfl⟩ : syracuseStep 1722929 = 1292197) B1292197
theorem B4082339 : Blo 1072617 4082339 := bstep (se 1 (by rfl) ⟨3061754, by rfl⟩ : syracuseStep 4082339 = 6123509) B6123509
theorem B3623885 : Blo 1072617 3623885 := bstep (se 3 (by rfl) ⟨679478, by rfl⟩ : syracuseStep 3623885 = 1358957) B1358957
theorem B3623939 : Blo 1072617 3623939 := bstep (se 1 (by rfl) ⟨2717954, by rfl⟩ : syracuseStep 3623939 = 5435909) B5435909
theorem B8277061 : Blo 1072617 8277061 := bstep (se 4 (by rfl) ⟨775974, by rfl⟩ : syracuseStep 8277061 = 1551949) B1551949
theorem B15486065 : Blo 1072617 15486065 := bstep (se 2 (by rfl) ⟨5807274, by rfl⟩ : syracuseStep 15486065 = 11614549) B11614549
theorem B3624209 : Blo 1072617 3624209 := bstep (se 2 (by rfl) ⟨1359078, by rfl⟩ : syracuseStep 3624209 = 2718157) B2718157
theorem B4082993 : Blo 1072617 4082993 := bstep (se 2 (by rfl) ⟨1531122, by rfl⟩ : syracuseStep 4082993 = 3062245) B3062245
theorem B1723763 : Blo 1072617 1723763 := bstep (se 1 (by rfl) ⟨1292822, by rfl⟩ : syracuseStep 1723763 = 2585645) B2585645
theorem B6540677 : Blo 1072617 6540677 := bstep (se 4 (by rfl) ⟨613188, by rfl⟩ : syracuseStep 6540677 = 1226377) B1226377
theorem B7753157 : Blo 1072617 7753157 := bstep (se 4 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 7753157 = 1453717) B1453717
theorem B1724051 : Blo 1072617 1724051 := bstep (se 1 (by rfl) ⟨1293038, by rfl⟩ : syracuseStep 1724051 = 2586077) B2586077
theorem B6115013 : Blo 1072617 6115013 := bstep (se 4 (by rfl) ⟨573282, by rfl⟩ : syracuseStep 6115013 = 1146565) B1146565
theorem B235523861 : Blo 1072617 235523861 := bstep (se 6 (by rfl) ⟨5520090, by rfl⟩ : syracuseStep 235523861 = 11040181) B11040181
theorem B3624749 : Blo 1072617 3624749 := bstep (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) B1359281
theorem B22073141 : Blo 1072617 22073141 := bstep (se 5 (by rfl) ⟨1034678, by rfl⟩ : syracuseStep 22073141 = 2069357) B2069357
theorem B3624803 : Blo 1072617 3624803 := bstep (se 1 (by rfl) ⟨2718602, by rfl⟩ : syracuseStep 3624803 = 5437205) B5437205
theorem B1527665 : Blo 1072617 1527665 := bstep (se 2 (by rfl) ⟨572874, by rfl⟩ : syracuseStep 1527665 = 1145749) B1145749
theorem B1724275 : Blo 1072617 1724275 := bstep (se 1 (by rfl) ⟨1293206, by rfl⟩ : syracuseStep 1724275 = 2586413) B2586413
theorem B1527779 : Blo 1072617 1527779 := bstep (se 1 (by rfl) ⟨1145834, by rfl⟩ : syracuseStep 1527779 = 2291669) B2291669
theorem B9949169 : Blo 1072617 9949169 := bstep (se 2 (by rfl) ⟨3730938, by rfl⟩ : syracuseStep 9949169 = 7461877) B7461877
theorem B1527859 : Blo 1072617 1527859 := bstep (se 1 (by rfl) ⟨1145894, by rfl⟩ : syracuseStep 1527859 = 2291789) B2291789
theorem B3625073 : Blo 1072617 3625073 := bstep (se 2 (by rfl) ⟨1359402, by rfl⟩ : syracuseStep 3625073 = 2718805) B2718805
theorem B8704397 : Blo 1072617 8704397 := bstep (se 3 (by rfl) ⟨1632074, by rfl⟩ : syracuseStep 8704397 = 3264149) B3264149
theorem B2904589 : Blo 1072617 2904589 := bstep (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) B1089221
theorem B1528417 : Blo 1072617 1528417 := bstep (se 2 (by rfl) ⟨573156, by rfl⟩ : syracuseStep 1528417 = 1146313) B1146313
theorem B3625613 : Blo 1072617 3625613 := bstep (se 3 (by rfl) ⟨679802, by rfl⟩ : syracuseStep 3625613 = 1359605) B1359605
theorem B3625667 : Blo 1072617 3625667 := bstep (se 1 (by rfl) ⟨2719250, by rfl⟩ : syracuseStep 3625667 = 5438501) B5438501
theorem B4084451 : Blo 1072617 4084451 := bstep (se 1 (by rfl) ⟨3063338, by rfl⟩ : syracuseStep 4084451 = 6126677) B6126677
theorem B4084465 : Blo 1072617 4084465 := bstep (se 2 (by rfl) ⟨1531674, by rfl⟩ : syracuseStep 4084465 = 3063349) B3063349
theorem B2413457 : Blo 1072617 2413457 := bstep (se 2 (by rfl) ⟨905046, by rfl⟩ : syracuseStep 2413457 = 1810093) B1810093
theorem B2413475 : Blo 1072617 2413475 := bstep (se 1 (by rfl) ⟨1810106, by rfl⟩ : syracuseStep 2413475 = 3620213) B3620213
theorem B3625937 : Blo 1072617 3625937 := bstep (se 2 (by rfl) ⟨1359726, by rfl⟩ : syracuseStep 3625937 = 2719453) B2719453
theorem B2413745 : Blo 1072617 2413745 := bstep (se 2 (by rfl) ⟨905154, by rfl⟩ : syracuseStep 2413745 = 1810309) B1810309
theorem B2413763 : Blo 1072617 2413763 := bstep (se 1 (by rfl) ⟨1810322, by rfl⟩ : syracuseStep 2413763 = 3620645) B3620645
theorem B1529123 : Blo 1072617 1529123 := bstep (se 1 (by rfl) ⟨1146842, by rfl⟩ : syracuseStep 1529123 = 2293685) B2293685
theorem B3102097 : Blo 1072617 3102097 := bstep (se 2 (by rfl) ⟨1163286, by rfl⟩ : syracuseStep 3102097 = 2326573) B2326573
theorem B2414033 : Blo 1072617 2414033 := bstep (se 2 (by rfl) ⟨905262, by rfl⟩ : syracuseStep 2414033 = 1810525) B1810525
theorem B2414051 : Blo 1072617 2414051 := bstep (se 1 (by rfl) ⟨1810538, by rfl⟩ : syracuseStep 2414051 = 3621077) B3621077
theorem B3626477 : Blo 1072617 3626477 := bstep (se 3 (by rfl) ⟨679964, by rfl⟩ : syracuseStep 3626477 = 1359929) B1359929
theorem B3626531 : Blo 1072617 3626531 := bstep (se 1 (by rfl) ⟨2719898, by rfl⟩ : syracuseStep 3626531 = 5439797) B5439797
theorem B1791587 : Blo 1072617 1791587 := bstep (se 1 (by rfl) ⟨1343690, by rfl⟩ : syracuseStep 1791587 = 2687381) B2687381
theorem B2414321 : Blo 1072617 2414321 := bstep (se 2 (by rfl) ⟨905370, by rfl⟩ : syracuseStep 2414321 = 1810741) B1810741
theorem B2414339 : Blo 1072617 2414339 := bstep (se 1 (by rfl) ⟨1810754, by rfl⟩ : syracuseStep 2414339 = 3621509) B3621509
theorem B6543109 : Blo 1072617 6543109 := bstep (se 4 (by rfl) ⟨613416, by rfl⟩ : syracuseStep 6543109 = 1226833) B1226833
theorem B3626801 : Blo 1072617 3626801 := bstep (se 2 (by rfl) ⟨1360050, by rfl⟩ : syracuseStep 3626801 = 2720101) B2720101
theorem B2578243 : Blo 1072617 2578243 := bstep (se 1 (by rfl) ⟨1933682, by rfl⟩ : syracuseStep 2578243 = 3867365) B3867365
theorem B1529761 : Blo 1072617 1529761 := bstep (se 2 (by rfl) ⟨573660, by rfl⟩ : syracuseStep 1529761 = 1147321) B1147321
theorem B10344419 : Blo 1072617 10344419 := bstep (se 1 (by rfl) ⟨7758314, by rfl⟩ : syracuseStep 10344419 = 15516629) B15516629
theorem B2414609 : Blo 1072617 2414609 := bstep (se 2 (by rfl) ⟨905478, by rfl⟩ : syracuseStep 2414609 = 1810957) B1810957
theorem B1529875 : Blo 1072617 1529875 := bstep (se 1 (by rfl) ⟨1147406, by rfl⟩ : syracuseStep 1529875 = 2294813) B2294813
theorem B2414627 : Blo 1072617 2414627 := bstep (se 1 (by rfl) ⟨1810970, by rfl⟩ : syracuseStep 2414627 = 3621941) B3621941
theorem B4085923 : Blo 1072617 4085923 := bstep (se 1 (by rfl) ⟨3064442, by rfl⟩ : syracuseStep 4085923 = 6128885) B6128885
theorem B2414897 : Blo 1072617 2414897 := bstep (se 2 (by rfl) ⟨905586, by rfl⟩ : syracuseStep 2414897 = 1811173) B1811173
theorem B2414915 : Blo 1072617 2414915 := bstep (se 1 (by rfl) ⟨1811186, by rfl⟩ : syracuseStep 2414915 = 3622373) B3622373
theorem B3627341 : Blo 1072617 3627341 := bstep (se 3 (by rfl) ⟨680126, by rfl⟩ : syracuseStep 3627341 = 1360253) B1360253
theorem B2447747 : Blo 1072617 2447747 := bstep (se 1 (by rfl) ⟨1835810, by rfl⟩ : syracuseStep 2447747 = 3671621) B3671621
theorem B3627395 : Blo 1072617 3627395 := bstep (se 1 (by rfl) ⟨2720546, by rfl⟩ : syracuseStep 3627395 = 5441093) B5441093
theorem B2415185 : Blo 1072617 2415185 := bstep (se 2 (by rfl) ⟨905694, by rfl⟩ : syracuseStep 2415185 = 1811389) B1811389
theorem B2415203 : Blo 1072617 2415203 := bstep (se 1 (by rfl) ⟨1811402, by rfl⟩ : syracuseStep 2415203 = 3622805) B3622805
theorem B3627665 : Blo 1072617 3627665 := bstep (se 2 (by rfl) ⟨1360374, by rfl⟩ : syracuseStep 3627665 = 2720749) B2720749
theorem B9165581 : Blo 1072617 9165581 := bstep (se 3 (by rfl) ⟨1718546, by rfl⟩ : syracuseStep 9165581 = 3437093) B3437093
theorem B2415473 : Blo 1072617 2415473 := bstep (se 2 (by rfl) ⟨905802, by rfl⟩ : syracuseStep 2415473 = 1811605) B1811605
theorem B2415491 : Blo 1072617 2415491 := bstep (se 1 (by rfl) ⟨1811618, by rfl⟩ : syracuseStep 2415491 = 3623237) B3623237
theorem B2907011 : Blo 1072617 2907011 := bstep (se 1 (by rfl) ⟨2180258, by rfl⟩ : syracuseStep 2907011 = 4360517) B4360517
theorem B3267469 : Blo 1072617 3267469 := bstep (se 3 (by rfl) ⟨612650, by rfl⟩ : syracuseStep 3267469 = 1225301) B1225301
theorem B25156493 : Blo 1072617 25156493 := bstep (se 3 (by rfl) ⟨4716842, by rfl⟩ : syracuseStep 25156493 = 9433685) B9433685
theorem B2579473 : Blo 1072617 2579473 := bstep (se 2 (by rfl) ⟨967302, by rfl⟩ : syracuseStep 2579473 = 1934605) B1934605
theorem B2415761 : Blo 1072617 2415761 := bstep (se 2 (by rfl) ⟨905910, by rfl⟩ : syracuseStep 2415761 = 1811821) B1811821
theorem B2415779 : Blo 1072617 2415779 := bstep (se 1 (by rfl) ⟨1811834, by rfl⟩ : syracuseStep 2415779 = 3623669) B3623669
theorem B3628205 : Blo 1072617 3628205 := bstep (se 3 (by rfl) ⟨680288, by rfl⟩ : syracuseStep 3628205 = 1360577) B1360577
theorem B3628259 : Blo 1072617 3628259 := bstep (se 1 (by rfl) ⟨2721194, by rfl⟩ : syracuseStep 3628259 = 5442389) B5442389
theorem B5430563 : Blo 1072617 5430563 := bstep (se 1 (by rfl) ⟨4072922, by rfl⟩ : syracuseStep 5430563 = 8145845) B8145845
theorem B1531219 : Blo 1072617 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B2416049 : Blo 1072617 2416049 := bstep (se 2 (by rfl) ⟨906018, by rfl⟩ : syracuseStep 2416049 = 1812037) B1812037
theorem B2416067 : Blo 1072617 2416067 := bstep (se 1 (by rfl) ⟨1812050, by rfl⟩ : syracuseStep 2416067 = 3624101) B3624101
theorem B6118861 : Blo 1072617 6118861 := bstep (se 3 (by rfl) ⟨1147286, by rfl⟩ : syracuseStep 6118861 = 2294573) B2294573
theorem B3628529 : Blo 1072617 3628529 := bstep (se 2 (by rfl) ⟨1360698, by rfl⟩ : syracuseStep 3628529 = 2721397) B2721397
theorem B1072627 : Blo 1072617 1072627 := bstep (se 1 (by rfl) ⟨804470, by rfl⟩ : syracuseStep 1072627 = 1608941) B1608941
theorem B1072643 : Blo 1072617 1072643 := bstep (se 1 (by rfl) ⟨804482, by rfl⟩ : syracuseStep 1072643 = 1608965) B1608965
theorem B1072659 : Blo 1072617 1072659 := bstep (se 1 (by rfl) ⟨804494, by rfl⟩ : syracuseStep 1072659 = 1608989) B1608989
theorem B1072675 : Blo 1072617 1072675 := bstep (se 1 (by rfl) ⟨804506, by rfl⟩ : syracuseStep 1072675 = 1609013) B1609013
theorem B1072691 : Blo 1072617 1072691 := bstep (se 1 (by rfl) ⟨804518, by rfl⟩ : syracuseStep 1072691 = 1609037) B1609037
theorem B1072707 : Blo 1072617 1072707 := bstep (se 1 (by rfl) ⟨804530, by rfl⟩ : syracuseStep 1072707 = 1609061) B1609061
theorem B1072723 : Blo 1072617 1072723 := bstep (se 1 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 1072723 = 1609085) B1609085
theorem B1072739 : Blo 1072617 1072739 := bstep (se 1 (by rfl) ⟨804554, by rfl⟩ : syracuseStep 1072739 = 1609109) B1609109
theorem B2448995 : Blo 1072617 2448995 := bstep (se 1 (by rfl) ⟨1836746, by rfl⟩ : syracuseStep 2448995 = 3673493) B3673493
theorem B1072755 : Blo 1072617 1072755 := bstep (se 1 (by rfl) ⟨804566, by rfl⟩ : syracuseStep 1072755 = 1609133) B1609133
theorem B1072771 : Blo 1072617 1072771 := bstep (se 1 (by rfl) ⟨804578, by rfl⟩ : syracuseStep 1072771 = 1609157) B1609157
theorem B1072787 : Blo 1072617 1072787 := bstep (se 1 (by rfl) ⟨804590, by rfl⟩ : syracuseStep 1072787 = 1609181) B1609181
theorem B1072803 : Blo 1072617 1072803 := bstep (se 1 (by rfl) ⟨804602, by rfl⟩ : syracuseStep 1072803 = 1609205) B1609205
theorem B1072819 : Blo 1072617 1072819 := bstep (se 1 (by rfl) ⟨804614, by rfl⟩ : syracuseStep 1072819 = 1609229) B1609229
theorem B1072835 : Blo 1072617 1072835 := bstep (se 1 (by rfl) ⟨804626, by rfl⟩ : syracuseStep 1072835 = 1609253) B1609253
theorem B2416337 : Blo 1072617 2416337 := bstep (se 2 (by rfl) ⟨906126, by rfl⟩ : syracuseStep 2416337 = 1812253) B1812253
theorem B1072851 : Blo 1072617 1072851 := bstep (se 1 (by rfl) ⟨804638, by rfl⟩ : syracuseStep 1072851 = 1609277) B1609277
theorem B1072867 : Blo 1072617 1072867 := bstep (se 1 (by rfl) ⟨804650, by rfl⟩ : syracuseStep 1072867 = 1609301) B1609301
theorem B2416355 : Blo 1072617 2416355 := bstep (se 1 (by rfl) ⟨1812266, by rfl⟩ : syracuseStep 2416355 = 3624533) B3624533
theorem B1072883 : Blo 1072617 1072883 := bstep (se 1 (by rfl) ⟨804662, by rfl⟩ : syracuseStep 1072883 = 1609325) B1609325
theorem B1072899 : Blo 1072617 1072899 := bstep (se 1 (by rfl) ⟨804674, by rfl⟩ : syracuseStep 1072899 = 1609349) B1609349
theorem B1072915 : Blo 1072617 1072915 := bstep (se 1 (by rfl) ⟨804686, by rfl⟩ : syracuseStep 1072915 = 1609373) B1609373
theorem B1072931 : Blo 1072617 1072931 := bstep (se 1 (by rfl) ⟨804698, by rfl⟩ : syracuseStep 1072931 = 1609397) B1609397
theorem B1072947 : Blo 1072617 1072947 := bstep (se 1 (by rfl) ⟨804710, by rfl⟩ : syracuseStep 1072947 = 1609421) B1609421
theorem B1072963 : Blo 1072617 1072963 := bstep (se 1 (by rfl) ⟨804722, by rfl⟩ : syracuseStep 1072963 = 1609445) B1609445
theorem B1072979 : Blo 1072617 1072979 := bstep (se 1 (by rfl) ⟨804734, by rfl⟩ : syracuseStep 1072979 = 1609469) B1609469
theorem B1072995 : Blo 1072617 1072995 := bstep (se 1 (by rfl) ⟨804746, by rfl⟩ : syracuseStep 1072995 = 1609493) B1609493
theorem B1073011 : Blo 1072617 1073011 := bstep (se 1 (by rfl) ⟨804758, by rfl⟩ : syracuseStep 1073011 = 1609517) B1609517
theorem B1073027 : Blo 1072617 1073027 := bstep (se 1 (by rfl) ⟨804770, by rfl⟩ : syracuseStep 1073027 = 1609541) B1609541
theorem B1073043 : Blo 1072617 1073043 := bstep (se 1 (by rfl) ⟨804782, by rfl⟩ : syracuseStep 1073043 = 1609565) B1609565
theorem B1073059 : Blo 1072617 1073059 := bstep (se 1 (by rfl) ⟨804794, by rfl⟩ : syracuseStep 1073059 = 1609589) B1609589
theorem B1073075 : Blo 1072617 1073075 := bstep (se 1 (by rfl) ⟨804806, by rfl⟩ : syracuseStep 1073075 = 1609613) B1609613
theorem B1073091 : Blo 1072617 1073091 := bstep (se 1 (by rfl) ⟨804818, by rfl⟩ : syracuseStep 1073091 = 1609637) B1609637
theorem B1073107 : Blo 1072617 1073107 := bstep (se 1 (by rfl) ⟨804830, by rfl⟩ : syracuseStep 1073107 = 1609661) B1609661
theorem B1073123 : Blo 1072617 1073123 := bstep (se 1 (by rfl) ⟨804842, by rfl⟩ : syracuseStep 1073123 = 1609685) B1609685
theorem B7757795 : Blo 1072617 7757795 := bstep (se 1 (by rfl) ⟨5818346, by rfl⟩ : syracuseStep 7757795 = 11636693) B11636693
theorem B2416625 : Blo 1072617 2416625 := bstep (se 2 (by rfl) ⟨906234, by rfl⟩ : syracuseStep 2416625 = 1812469) B1812469
theorem B1073139 : Blo 1072617 1073139 := bstep (se 1 (by rfl) ⟨804854, by rfl⟩ : syracuseStep 1073139 = 1609709) B1609709
theorem B1073155 : Blo 1072617 1073155 := bstep (se 1 (by rfl) ⟨804866, by rfl⟩ : syracuseStep 1073155 = 1609733) B1609733
theorem B2416643 : Blo 1072617 2416643 := bstep (se 1 (by rfl) ⟨1812482, by rfl⟩ : syracuseStep 2416643 = 3624965) B3624965
theorem B3629069 : Blo 1072617 3629069 := bstep (se 3 (by rfl) ⟨680450, by rfl⟩ : syracuseStep 3629069 = 1360901) B1360901
theorem B1073171 : Blo 1072617 1073171 := bstep (se 1 (by rfl) ⟨804878, by rfl⟩ : syracuseStep 1073171 = 1609757) B1609757
theorem B1073187 : Blo 1072617 1073187 := bstep (se 1 (by rfl) ⟨804890, by rfl⟩ : syracuseStep 1073187 = 1609781) B1609781
theorem B1073203 : Blo 1072617 1073203 := bstep (se 1 (by rfl) ⟨804902, by rfl⟩ : syracuseStep 1073203 = 1609805) B1609805
theorem B1073219 : Blo 1072617 1073219 := bstep (se 1 (by rfl) ⟨804914, by rfl⟩ : syracuseStep 1073219 = 1609829) B1609829
theorem B3629123 : Blo 1072617 3629123 := bstep (se 1 (by rfl) ⟨2721842, by rfl⟩ : syracuseStep 3629123 = 5443685) B5443685
theorem B5431373 : Blo 1072617 5431373 := bstep (se 3 (by rfl) ⟨1018382, by rfl⟩ : syracuseStep 5431373 = 2036765) B2036765
theorem B1073235 : Blo 1072617 1073235 := bstep (se 1 (by rfl) ⟨804926, by rfl⟩ : syracuseStep 1073235 = 1609853) B1609853
theorem B2613347 : Blo 1072617 2613347 := bstep (se 1 (by rfl) ⟨1960010, by rfl⟩ : syracuseStep 2613347 = 3920021) B3920021
theorem B1073251 : Blo 1072617 1073251 := bstep (se 1 (by rfl) ⟨804938, by rfl⟩ : syracuseStep 1073251 = 1609877) B1609877
theorem B1073267 : Blo 1072617 1073267 := bstep (se 1 (by rfl) ⟨804950, by rfl⟩ : syracuseStep 1073267 = 1609901) B1609901
theorem B1073283 : Blo 1072617 1073283 := bstep (se 1 (by rfl) ⟨804962, by rfl⟩ : syracuseStep 1073283 = 1609925) B1609925
theorem B1073299 : Blo 1072617 1073299 := bstep (se 1 (by rfl) ⟨804974, by rfl⟩ : syracuseStep 1073299 = 1609949) B1609949
theorem B1073315 : Blo 1072617 1073315 := bstep (se 1 (by rfl) ⟨804986, by rfl⟩ : syracuseStep 1073315 = 1609973) B1609973
theorem B1073331 : Blo 1072617 1073331 := bstep (se 1 (by rfl) ⟨804998, by rfl⟩ : syracuseStep 1073331 = 1609997) B1609997
theorem B1073347 : Blo 1072617 1073347 := bstep (se 1 (by rfl) ⟨805010, by rfl⟩ : syracuseStep 1073347 = 1610021) B1610021
theorem B1073363 : Blo 1072617 1073363 := bstep (se 1 (by rfl) ⟨805022, by rfl⟩ : syracuseStep 1073363 = 1610045) B1610045
theorem B1859809 : Blo 1072617 1859809 := bstep (se 2 (by rfl) ⟨697428, by rfl⟩ : syracuseStep 1859809 = 1394857) B1394857
theorem B1073379 : Blo 1072617 1073379 := bstep (se 1 (by rfl) ⟨805034, by rfl⟩ : syracuseStep 1073379 = 1610069) B1610069
theorem B1073395 : Blo 1072617 1073395 := bstep (se 1 (by rfl) ⟨805046, by rfl⟩ : syracuseStep 1073395 = 1610093) B1610093
theorem B1073411 : Blo 1072617 1073411 := bstep (se 1 (by rfl) ⟨805058, by rfl⟩ : syracuseStep 1073411 = 1610117) B1610117
theorem B2416913 : Blo 1072617 2416913 := bstep (se 2 (by rfl) ⟨906342, by rfl⟩ : syracuseStep 2416913 = 1812685) B1812685
theorem B1073427 : Blo 1072617 1073427 := bstep (se 1 (by rfl) ⟨805070, by rfl⟩ : syracuseStep 1073427 = 1610141) B1610141
theorem B1073443 : Blo 1072617 1073443 := bstep (se 1 (by rfl) ⟨805082, by rfl⟩ : syracuseStep 1073443 = 1610165) B1610165
theorem B2416931 : Blo 1072617 2416931 := bstep (se 1 (by rfl) ⟨1812698, by rfl⟩ : syracuseStep 2416931 = 3625397) B3625397
theorem B1073459 : Blo 1072617 1073459 := bstep (se 1 (by rfl) ⟨805094, by rfl⟩ : syracuseStep 1073459 = 1610189) B1610189
theorem B1073475 : Blo 1072617 1073475 := bstep (se 1 (by rfl) ⟨805106, by rfl⟩ : syracuseStep 1073475 = 1610213) B1610213
theorem B3629393 : Blo 1072617 3629393 := bstep (se 2 (by rfl) ⟨1361022, by rfl⟩ : syracuseStep 3629393 = 2722045) B2722045
theorem B1073491 : Blo 1072617 1073491 := bstep (se 1 (by rfl) ⟨805118, by rfl⟩ : syracuseStep 1073491 = 1610237) B1610237
theorem B1073507 : Blo 1072617 1073507 := bstep (se 1 (by rfl) ⟨805130, by rfl⟩ : syracuseStep 1073507 = 1610261) B1610261
theorem B1073523 : Blo 1072617 1073523 := bstep (se 1 (by rfl) ⟨805142, by rfl⟩ : syracuseStep 1073523 = 1610285) B1610285
theorem B1073539 : Blo 1072617 1073539 := bstep (se 1 (by rfl) ⟨805154, by rfl⟩ : syracuseStep 1073539 = 1610309) B1610309
theorem B1073555 : Blo 1072617 1073555 := bstep (se 1 (by rfl) ⟨805166, by rfl⟩ : syracuseStep 1073555 = 1610333) B1610333
theorem B1073571 : Blo 1072617 1073571 := bstep (se 1 (by rfl) ⟨805178, by rfl⟩ : syracuseStep 1073571 = 1610357) B1610357
theorem B1073587 : Blo 1072617 1073587 := bstep (se 1 (by rfl) ⟨805190, by rfl⟩ : syracuseStep 1073587 = 1610381) B1610381
theorem B1532353 : Blo 1072617 1532353 := bstep (se 2 (by rfl) ⟨574632, by rfl⟩ : syracuseStep 1532353 = 1149265) B1149265
theorem B1073603 : Blo 1072617 1073603 := bstep (se 1 (by rfl) ⟨805202, by rfl⟩ : syracuseStep 1073603 = 1610405) B1610405
theorem B1073619 : Blo 1072617 1073619 := bstep (se 1 (by rfl) ⟨805214, by rfl⟩ : syracuseStep 1073619 = 1610429) B1610429
theorem B1073635 : Blo 1072617 1073635 := bstep (se 1 (by rfl) ⟨805226, by rfl⟩ : syracuseStep 1073635 = 1610453) B1610453
theorem B1073651 : Blo 1072617 1073651 := bstep (se 1 (by rfl) ⟨805238, by rfl⟩ : syracuseStep 1073651 = 1610477) B1610477
theorem B1073667 : Blo 1072617 1073667 := bstep (se 1 (by rfl) ⟨805250, by rfl⟩ : syracuseStep 1073667 = 1610501) B1610501
theorem B1073683 : Blo 1072617 1073683 := bstep (se 1 (by rfl) ⟨805262, by rfl⟩ : syracuseStep 1073683 = 1610525) B1610525
theorem B1532449 : Blo 1072617 1532449 := bstep (se 2 (by rfl) ⟨574668, by rfl⟩ : syracuseStep 1532449 = 1149337) B1149337
theorem B1073699 : Blo 1072617 1073699 := bstep (se 1 (by rfl) ⟨805274, by rfl⟩ : syracuseStep 1073699 = 1610549) B1610549
theorem B2417201 : Blo 1072617 2417201 := bstep (se 2 (by rfl) ⟨906450, by rfl⟩ : syracuseStep 2417201 = 1812901) B1812901
theorem B1073715 : Blo 1072617 1073715 := bstep (se 1 (by rfl) ⟨805286, by rfl⟩ : syracuseStep 1073715 = 1610573) B1610573
theorem B13754933 : Blo 1072617 13754933 := bstep (se 5 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 13754933 = 1289525) B1289525
theorem B1073731 : Blo 1072617 1073731 := bstep (se 1 (by rfl) ⟨805298, by rfl⟩ : syracuseStep 1073731 = 1610597) B1610597
theorem B2417219 : Blo 1072617 2417219 := bstep (se 1 (by rfl) ⟨1812914, by rfl⟩ : syracuseStep 2417219 = 3625829) B3625829
theorem B1073747 : Blo 1072617 1073747 := bstep (se 1 (by rfl) ⟨805310, by rfl⟩ : syracuseStep 1073747 = 1610621) B1610621
theorem B1073763 : Blo 1072617 1073763 := bstep (se 1 (by rfl) ⟨805322, by rfl⟩ : syracuseStep 1073763 = 1610645) B1610645
theorem B7070321 : Blo 1072617 7070321 := bstep (se 2 (by rfl) ⟨2651370, by rfl⟩ : syracuseStep 7070321 = 5302741) B5302741
theorem B1073779 : Blo 1072617 1073779 := bstep (se 1 (by rfl) ⟨805334, by rfl⟩ : syracuseStep 1073779 = 1610669) B1610669
theorem B1073795 : Blo 1072617 1073795 := bstep (se 1 (by rfl) ⟨805346, by rfl⟩ : syracuseStep 1073795 = 1610693) B1610693
theorem B1073811 : Blo 1072617 1073811 := bstep (se 1 (by rfl) ⟨805358, by rfl⟩ : syracuseStep 1073811 = 1610717) B1610717
theorem B1073827 : Blo 1072617 1073827 := bstep (se 1 (by rfl) ⟨805370, by rfl⟩ : syracuseStep 1073827 = 1610741) B1610741
theorem B1073843 : Blo 1072617 1073843 := bstep (se 1 (by rfl) ⟨805382, by rfl⟩ : syracuseStep 1073843 = 1610765) B1610765
theorem B1073859 : Blo 1072617 1073859 := bstep (se 1 (by rfl) ⟨805394, by rfl⟩ : syracuseStep 1073859 = 1610789) B1610789
theorem B1073875 : Blo 1072617 1073875 := bstep (se 1 (by rfl) ⟨805406, by rfl⟩ : syracuseStep 1073875 = 1610813) B1610813
theorem B1073891 : Blo 1072617 1073891 := bstep (se 1 (by rfl) ⟨805418, by rfl⟩ : syracuseStep 1073891 = 1610837) B1610837
theorem B1073907 : Blo 1072617 1073907 := bstep (se 1 (by rfl) ⟨805430, by rfl⟩ : syracuseStep 1073907 = 1610861) B1610861
theorem B1073923 : Blo 1072617 1073923 := bstep (se 1 (by rfl) ⟨805442, by rfl⟩ : syracuseStep 1073923 = 1610885) B1610885
theorem B5104397 : Blo 1072617 5104397 := bstep (se 3 (by rfl) ⟨957074, by rfl⟩ : syracuseStep 5104397 = 1914149) B1914149
theorem B1073939 : Blo 1072617 1073939 := bstep (se 1 (by rfl) ⟨805454, by rfl⟩ : syracuseStep 1073939 = 1610909) B1610909
theorem B1073955 : Blo 1072617 1073955 := bstep (se 1 (by rfl) ⟨805466, by rfl⟩ : syracuseStep 1073955 = 1610933) B1610933
theorem B1073971 : Blo 1072617 1073971 := bstep (se 1 (by rfl) ⟨805478, by rfl⟩ : syracuseStep 1073971 = 1610957) B1610957
theorem B2941763 : Blo 1072617 2941763 := bstep (se 1 (by rfl) ⟨2206322, by rfl⟩ : syracuseStep 2941763 = 4412645) B4412645
theorem B1073987 : Blo 1072617 1073987 := bstep (se 1 (by rfl) ⟨805490, by rfl⟩ : syracuseStep 1073987 = 1610981) B1610981
theorem B2417489 : Blo 1072617 2417489 := bstep (se 2 (by rfl) ⟨906558, by rfl⟩ : syracuseStep 2417489 = 1813117) B1813117
theorem B1074003 : Blo 1072617 1074003 := bstep (se 1 (by rfl) ⟨805502, by rfl⟩ : syracuseStep 1074003 = 1611005) B1611005
theorem B1074019 : Blo 1072617 1074019 := bstep (se 1 (by rfl) ⟨805514, by rfl⟩ : syracuseStep 1074019 = 1611029) B1611029
theorem B2417507 : Blo 1072617 2417507 := bstep (se 1 (by rfl) ⟨1813130, by rfl⟩ : syracuseStep 2417507 = 3626261) B3626261
theorem B3629933 : Blo 1072617 3629933 := bstep (se 3 (by rfl) ⟨680612, by rfl⟩ : syracuseStep 3629933 = 1361225) B1361225
theorem B1074035 : Blo 1072617 1074035 := bstep (se 1 (by rfl) ⟨805526, by rfl⟩ : syracuseStep 1074035 = 1611053) B1611053
theorem B1074051 : Blo 1072617 1074051 := bstep (se 1 (by rfl) ⟨805538, by rfl⟩ : syracuseStep 1074051 = 1611077) B1611077
theorem B1074067 : Blo 1072617 1074067 := bstep (se 1 (by rfl) ⟨805550, by rfl⟩ : syracuseStep 1074067 = 1611101) B1611101
theorem B1074083 : Blo 1072617 1074083 := bstep (se 1 (by rfl) ⟨805562, by rfl⟩ : syracuseStep 1074083 = 1611125) B1611125
theorem B3629987 : Blo 1072617 3629987 := bstep (se 1 (by rfl) ⟨2722490, by rfl⟩ : syracuseStep 3629987 = 5444981) B5444981
theorem B1074099 : Blo 1072617 1074099 := bstep (se 1 (by rfl) ⟨805574, by rfl⟩ : syracuseStep 1074099 = 1611149) B1611149
theorem B1074115 : Blo 1072617 1074115 := bstep (se 1 (by rfl) ⟨805586, by rfl⟩ : syracuseStep 1074115 = 1611173) B1611173
theorem B1074131 : Blo 1072617 1074131 := bstep (se 1 (by rfl) ⟨805598, by rfl⟩ : syracuseStep 1074131 = 1611197) B1611197
theorem B1074147 : Blo 1072617 1074147 := bstep (se 1 (by rfl) ⟨805610, by rfl⟩ : syracuseStep 1074147 = 1611221) B1611221
theorem B1074163 : Blo 1072617 1074163 := bstep (se 1 (by rfl) ⟨805622, by rfl⟩ : syracuseStep 1074163 = 1611245) B1611245
theorem B1074179 : Blo 1072617 1074179 := bstep (se 1 (by rfl) ⟨805634, by rfl⟩ : syracuseStep 1074179 = 1611269) B1611269
theorem B1074195 : Blo 1072617 1074195 := bstep (se 1 (by rfl) ⟨805646, by rfl⟩ : syracuseStep 1074195 = 1611293) B1611293
theorem B1074211 : Blo 1072617 1074211 := bstep (se 1 (by rfl) ⟨805658, by rfl⟩ : syracuseStep 1074211 = 1611317) B1611317
theorem B1074227 : Blo 1072617 1074227 := bstep (se 1 (by rfl) ⟨805670, by rfl⟩ : syracuseStep 1074227 = 1611341) B1611341
theorem B1631297 : Blo 1072617 1631297 := bstep (se 2 (by rfl) ⟨611736, by rfl⟩ : syracuseStep 1631297 = 1223473) B1223473
theorem B1074243 : Blo 1072617 1074243 := bstep (se 1 (by rfl) ⟨805682, by rfl⟩ : syracuseStep 1074243 = 1611365) B1611365
theorem B1074259 : Blo 1072617 1074259 := bstep (se 1 (by rfl) ⟨805694, by rfl⟩ : syracuseStep 1074259 = 1611389) B1611389
theorem B8152163 : Blo 1072617 8152163 := bstep (se 1 (by rfl) ⟨6114122, by rfl⟩ : syracuseStep 8152163 = 12228245) B12228245
theorem B1074275 : Blo 1072617 1074275 := bstep (se 1 (by rfl) ⟨805706, by rfl⟩ : syracuseStep 1074275 = 1611413) B1611413
theorem B2417777 : Blo 1072617 2417777 := bstep (se 2 (by rfl) ⟨906666, by rfl⟩ : syracuseStep 2417777 = 1813333) B1813333
theorem B1074291 : Blo 1072617 1074291 := bstep (se 1 (by rfl) ⟨805718, by rfl⟩ : syracuseStep 1074291 = 1611437) B1611437
theorem B1074307 : Blo 1072617 1074307 := bstep (se 1 (by rfl) ⟨805730, by rfl⟩ : syracuseStep 1074307 = 1611461) B1611461
theorem B2417795 : Blo 1072617 2417795 := bstep (se 1 (by rfl) ⟨1813346, by rfl⟩ : syracuseStep 2417795 = 3626693) B3626693
theorem B1074323 : Blo 1072617 1074323 := bstep (se 1 (by rfl) ⟨805742, by rfl⟩ : syracuseStep 1074323 = 1611485) B1611485
theorem B1074339 : Blo 1072617 1074339 := bstep (se 1 (by rfl) ⟨805754, by rfl⟩ : syracuseStep 1074339 = 1611509) B1611509
theorem B3630257 : Blo 1072617 3630257 := bstep (se 2 (by rfl) ⟨1361346, by rfl⟩ : syracuseStep 3630257 = 2722693) B2722693
theorem B1074355 : Blo 1072617 1074355 := bstep (se 1 (by rfl) ⟨805766, by rfl⟩ : syracuseStep 1074355 = 1611533) B1611533
theorem B1074371 : Blo 1072617 1074371 := bstep (se 1 (by rfl) ⟨805778, by rfl⟩ : syracuseStep 1074371 = 1611557) B1611557
theorem B1631443 : Blo 1072617 1631443 := bstep (se 1 (by rfl) ⟨1223582, by rfl⟩ : syracuseStep 1631443 = 2447165) B2447165
theorem B1074387 : Blo 1072617 1074387 := bstep (se 1 (by rfl) ⟨805790, by rfl⟩ : syracuseStep 1074387 = 1611581) B1611581
theorem B1074403 : Blo 1072617 1074403 := bstep (se 1 (by rfl) ⟨805802, by rfl⟩ : syracuseStep 1074403 = 1611605) B1611605
theorem B1074419 : Blo 1072617 1074419 := bstep (se 1 (by rfl) ⟨805814, by rfl⟩ : syracuseStep 1074419 = 1611629) B1611629
theorem B1074435 : Blo 1072617 1074435 := bstep (se 1 (by rfl) ⟨805826, by rfl⟩ : syracuseStep 1074435 = 1611653) B1611653
theorem B1074451 : Blo 1072617 1074451 := bstep (se 1 (by rfl) ⟨805838, by rfl⟩ : syracuseStep 1074451 = 1611677) B1611677
theorem B1074467 : Blo 1072617 1074467 := bstep (se 1 (by rfl) ⟨805850, by rfl⟩ : syracuseStep 1074467 = 1611701) B1611701
theorem B1074483 : Blo 1072617 1074483 := bstep (se 1 (by rfl) ⟨805862, by rfl⟩ : syracuseStep 1074483 = 1611725) B1611725
theorem B1074499 : Blo 1072617 1074499 := bstep (se 1 (by rfl) ⟨805874, by rfl⟩ : syracuseStep 1074499 = 1611749) B1611749
theorem B1074515 : Blo 1072617 1074515 := bstep (se 1 (by rfl) ⟨805886, by rfl⟩ : syracuseStep 1074515 = 1611773) B1611773
theorem B1074531 : Blo 1072617 1074531 := bstep (se 1 (by rfl) ⟨805898, by rfl⟩ : syracuseStep 1074531 = 1611797) B1611797
theorem B1074547 : Blo 1072617 1074547 := bstep (se 1 (by rfl) ⟨805910, by rfl⟩ : syracuseStep 1074547 = 1611821) B1611821
theorem B1074563 : Blo 1072617 1074563 := bstep (se 1 (by rfl) ⟨805922, by rfl⟩ : syracuseStep 1074563 = 1611845) B1611845
theorem B6120845 : Blo 1072617 6120845 := bstep (se 3 (by rfl) ⟨1147658, by rfl⟩ : syracuseStep 6120845 = 2295317) B2295317
theorem B2418065 : Blo 1072617 2418065 := bstep (se 2 (by rfl) ⟨906774, by rfl⟩ : syracuseStep 2418065 = 1813549) B1813549
theorem B1074579 : Blo 1072617 1074579 := bstep (se 1 (by rfl) ⟨805934, by rfl⟩ : syracuseStep 1074579 = 1611869) B1611869
theorem B1074595 : Blo 1072617 1074595 := bstep (se 1 (by rfl) ⟨805946, by rfl⟩ : syracuseStep 1074595 = 1611893) B1611893
theorem B2418083 : Blo 1072617 2418083 := bstep (se 1 (by rfl) ⟨1813562, by rfl⟩ : syracuseStep 2418083 = 3627125) B3627125
theorem B1074611 : Blo 1072617 1074611 := bstep (se 1 (by rfl) ⟨805958, by rfl⟩ : syracuseStep 1074611 = 1611917) B1611917
theorem B1074627 : Blo 1072617 1074627 := bstep (se 1 (by rfl) ⟨805970, by rfl⟩ : syracuseStep 1074627 = 1611941) B1611941
theorem B1074643 : Blo 1072617 1074643 := bstep (se 1 (by rfl) ⟨805982, by rfl⟩ : syracuseStep 1074643 = 1611965) B1611965
theorem B1074659 : Blo 1072617 1074659 := bstep (se 1 (by rfl) ⟨805994, by rfl⟩ : syracuseStep 1074659 = 1611989) B1611989
theorem B1074675 : Blo 1072617 1074675 := bstep (se 1 (by rfl) ⟨806006, by rfl⟩ : syracuseStep 1074675 = 1612013) B1612013
theorem B1074691 : Blo 1072617 1074691 := bstep (se 1 (by rfl) ⟨806018, by rfl⟩ : syracuseStep 1074691 = 1612037) B1612037
theorem B1074707 : Blo 1072617 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B1074723 : Blo 1072617 1074723 := bstep (se 1 (by rfl) ⟨806042, by rfl⟩ : syracuseStep 1074723 = 1612085) B1612085
theorem B1074739 : Blo 1072617 1074739 := bstep (se 1 (by rfl) ⟨806054, by rfl⟩ : syracuseStep 1074739 = 1612109) B1612109
theorem B1074755 : Blo 1072617 1074755 := bstep (se 1 (by rfl) ⟨806066, by rfl⟩ : syracuseStep 1074755 = 1612133) B1612133
theorem B1074771 : Blo 1072617 1074771 := bstep (se 1 (by rfl) ⟨806078, by rfl⟩ : syracuseStep 1074771 = 1612157) B1612157
theorem B1074787 : Blo 1072617 1074787 := bstep (se 1 (by rfl) ⟨806090, by rfl⟩ : syracuseStep 1074787 = 1612181) B1612181
theorem B5170787 : Blo 1072617 5170787 := bstep (se 1 (by rfl) ⟨3878090, by rfl⟩ : syracuseStep 5170787 = 7756181) B7756181
theorem B1074803 : Blo 1072617 1074803 := bstep (se 1 (by rfl) ⟨806102, by rfl⟩ : syracuseStep 1074803 = 1612205) B1612205
theorem B1074819 : Blo 1072617 1074819 := bstep (se 1 (by rfl) ⟨806114, by rfl⟩ : syracuseStep 1074819 = 1612229) B1612229
theorem B1074835 : Blo 1072617 1074835 := bstep (se 1 (by rfl) ⟨806126, by rfl⟩ : syracuseStep 1074835 = 1612253) B1612253
theorem B1074851 : Blo 1072617 1074851 := bstep (se 1 (by rfl) ⟨806138, by rfl⟩ : syracuseStep 1074851 = 1612277) B1612277
theorem B2418353 : Blo 1072617 2418353 := bstep (se 2 (by rfl) ⟨906882, by rfl⟩ : syracuseStep 2418353 = 1813765) B1813765
theorem B1074867 : Blo 1072617 1074867 := bstep (se 1 (by rfl) ⟨806150, by rfl⟩ : syracuseStep 1074867 = 1612301) B1612301
theorem B2418371 : Blo 1072617 2418371 := bstep (se 1 (by rfl) ⟨1813778, by rfl⟩ : syracuseStep 2418371 = 3627557) B3627557
theorem B1074883 : Blo 1072617 1074883 := bstep (se 1 (by rfl) ⟨806162, by rfl⟩ : syracuseStep 1074883 = 1612325) B1612325
theorem B3630797 : Blo 1072617 3630797 := bstep (se 3 (by rfl) ⟨680774, by rfl⟩ : syracuseStep 3630797 = 1361549) B1361549
theorem B1074899 : Blo 1072617 1074899 := bstep (se 1 (by rfl) ⟨806174, by rfl⟩ : syracuseStep 1074899 = 1612349) B1612349
theorem B1074915 : Blo 1072617 1074915 := bstep (se 1 (by rfl) ⟨806186, by rfl⟩ : syracuseStep 1074915 = 1612373) B1612373
theorem B1074931 : Blo 1072617 1074931 := bstep (se 1 (by rfl) ⟨806198, by rfl⟩ : syracuseStep 1074931 = 1612397) B1612397
theorem B3630851 : Blo 1072617 3630851 := bstep (se 1 (by rfl) ⟨2723138, by rfl⟩ : syracuseStep 3630851 = 5446277) B5446277
theorem B2942723 : Blo 1072617 2942723 := bstep (se 1 (by rfl) ⟨2207042, by rfl⟩ : syracuseStep 2942723 = 4414085) B4414085
theorem B1074947 : Blo 1072617 1074947 := bstep (se 1 (by rfl) ⟨806210, by rfl⟩ : syracuseStep 1074947 = 1612421) B1612421
theorem B1074963 : Blo 1072617 1074963 := bstep (se 1 (by rfl) ⟨806222, by rfl⟩ : syracuseStep 1074963 = 1612445) B1612445
theorem B1074979 : Blo 1072617 1074979 := bstep (se 1 (by rfl) ⟨806234, by rfl⟩ : syracuseStep 1074979 = 1612469) B1612469
theorem B5170979 : Blo 1072617 5170979 := bstep (se 1 (by rfl) ⟨3878234, by rfl⟩ : syracuseStep 5170979 = 7756469) B7756469
theorem B1074995 : Blo 1072617 1074995 := bstep (se 1 (by rfl) ⟨806246, by rfl⟩ : syracuseStep 1074995 = 1612493) B1612493
theorem B1075011 : Blo 1072617 1075011 := bstep (se 1 (by rfl) ⟨806258, by rfl⟩ : syracuseStep 1075011 = 1612517) B1612517
theorem B1075027 : Blo 1072617 1075027 := bstep (se 1 (by rfl) ⟨806270, by rfl⟩ : syracuseStep 1075027 = 1612541) B1612541
theorem B1075043 : Blo 1072617 1075043 := bstep (se 1 (by rfl) ⟨806282, by rfl⟩ : syracuseStep 1075043 = 1612565) B1612565
theorem B1075059 : Blo 1072617 1075059 := bstep (se 1 (by rfl) ⟨806294, by rfl⟩ : syracuseStep 1075059 = 1612589) B1612589
theorem B1075075 : Blo 1072617 1075075 := bstep (se 1 (by rfl) ⟨806306, by rfl⟩ : syracuseStep 1075075 = 1612613) B1612613
theorem B1075091 : Blo 1072617 1075091 := bstep (se 1 (by rfl) ⟨806318, by rfl⟩ : syracuseStep 1075091 = 1612637) B1612637
theorem B1075107 : Blo 1072617 1075107 := bstep (se 1 (by rfl) ⟨806330, by rfl⟩ : syracuseStep 1075107 = 1612661) B1612661
theorem B1075123 : Blo 1072617 1075123 := bstep (se 1 (by rfl) ⟨806342, by rfl⟩ : syracuseStep 1075123 = 1612685) B1612685
theorem B1075139 : Blo 1072617 1075139 := bstep (se 1 (by rfl) ⟨806354, by rfl⟩ : syracuseStep 1075139 = 1612709) B1612709
theorem B2418641 : Blo 1072617 2418641 := bstep (se 2 (by rfl) ⟨906990, by rfl⟩ : syracuseStep 2418641 = 1813981) B1813981
theorem B1075155 : Blo 1072617 1075155 := bstep (se 1 (by rfl) ⟨806366, by rfl⟩ : syracuseStep 1075155 = 1612733) B1612733
theorem B2418659 : Blo 1072617 2418659 := bstep (se 1 (by rfl) ⟨1813994, by rfl⟩ : syracuseStep 2418659 = 3627989) B3627989
theorem B1075171 : Blo 1072617 1075171 := bstep (se 1 (by rfl) ⟨806378, by rfl⟩ : syracuseStep 1075171 = 1612757) B1612757
theorem B1075187 : Blo 1072617 1075187 := bstep (se 1 (by rfl) ⟨806390, by rfl⟩ : syracuseStep 1075187 = 1612781) B1612781
theorem B1075203 : Blo 1072617 1075203 := bstep (se 1 (by rfl) ⟨806402, by rfl⟩ : syracuseStep 1075203 = 1612805) B1612805
theorem B3631121 : Blo 1072617 3631121 := bstep (se 2 (by rfl) ⟨1361670, by rfl⟩ : syracuseStep 3631121 = 2723341) B2723341
theorem B1075219 : Blo 1072617 1075219 := bstep (se 1 (by rfl) ⟨806414, by rfl⟩ : syracuseStep 1075219 = 1612829) B1612829
theorem B1075235 : Blo 1072617 1075235 := bstep (se 1 (by rfl) ⟨806426, by rfl⟩ : syracuseStep 1075235 = 1612853) B1612853
theorem B1075251 : Blo 1072617 1075251 := bstep (se 1 (by rfl) ⟨806438, by rfl⟩ : syracuseStep 1075251 = 1612877) B1612877
theorem B1075267 : Blo 1072617 1075267 := bstep (se 1 (by rfl) ⟨806450, by rfl⟩ : syracuseStep 1075267 = 1612901) B1612901
theorem B1075283 : Blo 1072617 1075283 := bstep (se 1 (by rfl) ⟨806462, by rfl⟩ : syracuseStep 1075283 = 1612925) B1612925
theorem B1075299 : Blo 1072617 1075299 := bstep (se 1 (by rfl) ⟨806474, by rfl⟩ : syracuseStep 1075299 = 1612949) B1612949
theorem B1075315 : Blo 1072617 1075315 := bstep (se 1 (by rfl) ⟨806486, by rfl⟩ : syracuseStep 1075315 = 1612973) B1612973
theorem B1075331 : Blo 1072617 1075331 := bstep (se 1 (by rfl) ⟨806498, by rfl⟩ : syracuseStep 1075331 = 1612997) B1612997
theorem B1075347 : Blo 1072617 1075347 := bstep (se 1 (by rfl) ⟨806510, by rfl⟩ : syracuseStep 1075347 = 1613021) B1613021
theorem B1075363 : Blo 1072617 1075363 := bstep (se 1 (by rfl) ⟨806522, by rfl⟩ : syracuseStep 1075363 = 1613045) B1613045
theorem B1075379 : Blo 1072617 1075379 := bstep (se 1 (by rfl) ⟨806534, by rfl⟩ : syracuseStep 1075379 = 1613069) B1613069
theorem B1075395 : Blo 1072617 1075395 := bstep (se 1 (by rfl) ⟨806546, by rfl⟩ : syracuseStep 1075395 = 1613093) B1613093
theorem B1075411 : Blo 1072617 1075411 := bstep (se 1 (by rfl) ⟨806558, by rfl⟩ : syracuseStep 1075411 = 1613117) B1613117
theorem B1075427 : Blo 1072617 1075427 := bstep (se 1 (by rfl) ⟨806570, by rfl⟩ : syracuseStep 1075427 = 1613141) B1613141
theorem B2418929 : Blo 1072617 2418929 := bstep (se 2 (by rfl) ⟨907098, by rfl⟩ : syracuseStep 2418929 = 1814197) B1814197
theorem B1075443 : Blo 1072617 1075443 := bstep (se 1 (by rfl) ⟨806582, by rfl⟩ : syracuseStep 1075443 = 1613165) B1613165
theorem B2418947 : Blo 1072617 2418947 := bstep (se 1 (by rfl) ⟨1814210, by rfl⟩ : syracuseStep 2418947 = 3628421) B3628421
theorem B1075459 : Blo 1072617 1075459 := bstep (se 1 (by rfl) ⟨806594, by rfl⟩ : syracuseStep 1075459 = 1613189) B1613189
theorem B1075475 : Blo 1072617 1075475 := bstep (se 1 (by rfl) ⟨806606, by rfl⟩ : syracuseStep 1075475 = 1613213) B1613213
theorem B1075491 : Blo 1072617 1075491 := bstep (se 1 (by rfl) ⟨806618, by rfl⟩ : syracuseStep 1075491 = 1613237) B1613237
theorem B6121777 : Blo 1072617 6121777 := bstep (se 2 (by rfl) ⟨2295666, by rfl⟩ : syracuseStep 6121777 = 4591333) B4591333
theorem B1075507 : Blo 1072617 1075507 := bstep (se 1 (by rfl) ⟨806630, by rfl⟩ : syracuseStep 1075507 = 1613261) B1613261
theorem B1075523 : Blo 1072617 1075523 := bstep (se 1 (by rfl) ⟨806642, by rfl⟩ : syracuseStep 1075523 = 1613285) B1613285
theorem B1075539 : Blo 1072617 1075539 := bstep (se 1 (by rfl) ⟨806654, by rfl⟩ : syracuseStep 1075539 = 1613309) B1613309
theorem B1632611 : Blo 1072617 1632611 := bstep (se 1 (by rfl) ⟨1224458, by rfl⟩ : syracuseStep 1632611 = 2448917) B2448917
theorem B1075555 : Blo 1072617 1075555 := bstep (se 1 (by rfl) ⟨806666, by rfl⟩ : syracuseStep 1075555 = 1613333) B1613333
theorem B1075571 : Blo 1072617 1075571 := bstep (se 1 (by rfl) ⟨806678, by rfl⟩ : syracuseStep 1075571 = 1613357) B1613357
theorem B1075587 : Blo 1072617 1075587 := bstep (se 1 (by rfl) ⟨806690, by rfl⟩ : syracuseStep 1075587 = 1613381) B1613381
theorem B1075603 : Blo 1072617 1075603 := bstep (se 1 (by rfl) ⟨806702, by rfl⟩ : syracuseStep 1075603 = 1613405) B1613405
theorem B1075619 : Blo 1072617 1075619 := bstep (se 1 (by rfl) ⟨806714, by rfl⟩ : syracuseStep 1075619 = 1613429) B1613429
theorem B5171633 : Blo 1072617 5171633 := bstep (se 2 (by rfl) ⟨1939362, by rfl⟩ : syracuseStep 5171633 = 3878725) B3878725
theorem B1075635 : Blo 1072617 1075635 := bstep (se 1 (by rfl) ⟨806726, by rfl⟩ : syracuseStep 1075635 = 1613453) B1613453
theorem B1075651 : Blo 1072617 1075651 := bstep (se 1 (by rfl) ⟨806738, by rfl⟩ : syracuseStep 1075651 = 1613477) B1613477
theorem B1075667 : Blo 1072617 1075667 := bstep (se 1 (by rfl) ⟨806750, by rfl⟩ : syracuseStep 1075667 = 1613501) B1613501
theorem B1075683 : Blo 1072617 1075683 := bstep (se 1 (by rfl) ⟨806762, by rfl⟩ : syracuseStep 1075683 = 1613525) B1613525
theorem B1075699 : Blo 1072617 1075699 := bstep (se 1 (by rfl) ⟨806774, by rfl⟩ : syracuseStep 1075699 = 1613549) B1613549
theorem B1206787 : Blo 1072617 1206787 := bstep (se 1 (by rfl) ⟨905090, by rfl⟩ : syracuseStep 1206787 = 1810181) B1810181
theorem B1075715 : Blo 1072617 1075715 := bstep (se 1 (by rfl) ⟨806786, by rfl⟩ : syracuseStep 1075715 = 1613573) B1613573
theorem B2419217 : Blo 1072617 2419217 := bstep (se 2 (by rfl) ⟨907206, by rfl⟩ : syracuseStep 2419217 = 1814413) B1814413
theorem B1075731 : Blo 1072617 1075731 := bstep (se 1 (by rfl) ⟨806798, by rfl⟩ : syracuseStep 1075731 = 1613597) B1613597
theorem B2419235 : Blo 1072617 2419235 := bstep (se 1 (by rfl) ⟨1814426, by rfl⟩ : syracuseStep 2419235 = 3628853) B3628853
theorem B1075747 : Blo 1072617 1075747 := bstep (se 1 (by rfl) ⟨806810, by rfl⟩ : syracuseStep 1075747 = 1613621) B1613621
theorem B3631661 : Blo 1072617 3631661 := bstep (se 3 (by rfl) ⟨680936, by rfl⟩ : syracuseStep 3631661 = 1361873) B1361873
theorem B1075763 : Blo 1072617 1075763 := bstep (se 1 (by rfl) ⟨806822, by rfl⟩ : syracuseStep 1075763 = 1613645) B1613645
theorem B1075779 : Blo 1072617 1075779 := bstep (se 1 (by rfl) ⟨806834, by rfl⟩ : syracuseStep 1075779 = 1613669) B1613669
theorem B1075795 : Blo 1072617 1075795 := bstep (se 1 (by rfl) ⟨806846, by rfl⟩ : syracuseStep 1075795 = 1613693) B1613693
theorem B1075811 : Blo 1072617 1075811 := bstep (se 1 (by rfl) ⟨806858, by rfl⟩ : syracuseStep 1075811 = 1613717) B1613717
theorem B3631715 : Blo 1072617 3631715 := bstep (se 1 (by rfl) ⟨2723786, by rfl⟩ : syracuseStep 3631715 = 5447573) B5447573
theorem B4909667 : Blo 1072617 4909667 := bstep (se 1 (by rfl) ⟨3682250, by rfl⟩ : syracuseStep 4909667 = 7364501) B7364501
theorem B1075827 : Blo 1072617 1075827 := bstep (se 1 (by rfl) ⟨806870, by rfl⟩ : syracuseStep 1075827 = 1613741) B1613741
theorem B1075843 : Blo 1072617 1075843 := bstep (se 1 (by rfl) ⟨806882, by rfl⟩ : syracuseStep 1075843 = 1613765) B1613765
theorem B1206931 : Blo 1072617 1206931 := bstep (se 1 (by rfl) ⟨905198, by rfl⟩ : syracuseStep 1206931 = 1810397) B1810397
theorem B1075859 : Blo 1072617 1075859 := bstep (se 1 (by rfl) ⟨806894, by rfl⟩ : syracuseStep 1075859 = 1613789) B1613789
theorem B1075875 : Blo 1072617 1075875 := bstep (se 1 (by rfl) ⟨806906, by rfl⟩ : syracuseStep 1075875 = 1613813) B1613813
theorem B1075891 : Blo 1072617 1075891 := bstep (se 1 (by rfl) ⟨806918, by rfl⟩ : syracuseStep 1075891 = 1613837) B1613837
theorem B1075907 : Blo 1072617 1075907 := bstep (se 1 (by rfl) ⟨806930, by rfl⟩ : syracuseStep 1075907 = 1613861) B1613861
theorem B1075923 : Blo 1072617 1075923 := bstep (se 1 (by rfl) ⟨806942, by rfl⟩ : syracuseStep 1075923 = 1613885) B1613885
theorem B55896803 : Blo 1072617 55896803 := bstep (se 1 (by rfl) ⟨41922602, by rfl⟩ : syracuseStep 55896803 = 83845205) B83845205
theorem B1075939 : Blo 1072617 1075939 := bstep (se 1 (by rfl) ⟨806954, by rfl⟩ : syracuseStep 1075939 = 1613909) B1613909
theorem B1075955 : Blo 1072617 1075955 := bstep (se 1 (by rfl) ⟨806966, by rfl⟩ : syracuseStep 1075955 = 1613933) B1613933
theorem B1075971 : Blo 1072617 1075971 := bstep (se 1 (by rfl) ⟨806978, by rfl⟩ : syracuseStep 1075971 = 1613957) B1613957
theorem B1075987 : Blo 1072617 1075987 := bstep (se 1 (by rfl) ⟨806990, by rfl⟩ : syracuseStep 1075987 = 1613981) B1613981
theorem B1207075 : Blo 1072617 1207075 := bstep (se 1 (by rfl) ⟨905306, by rfl⟩ : syracuseStep 1207075 = 1810613) B1810613
theorem B1076003 : Blo 1072617 1076003 := bstep (se 1 (by rfl) ⟨807002, by rfl⟩ : syracuseStep 1076003 = 1614005) B1614005
theorem B2419505 : Blo 1072617 2419505 := bstep (se 2 (by rfl) ⟨907314, by rfl⟩ : syracuseStep 2419505 = 1814629) B1814629
theorem B1076019 : Blo 1072617 1076019 := bstep (se 1 (by rfl) ⟨807014, by rfl⟩ : syracuseStep 1076019 = 1614029) B1614029
theorem B2419523 : Blo 1072617 2419523 := bstep (se 1 (by rfl) ⟨1814642, by rfl⟩ : syracuseStep 2419523 = 3629285) B3629285
theorem B1076035 : Blo 1072617 1076035 := bstep (se 1 (by rfl) ⟨807026, by rfl⟩ : syracuseStep 1076035 = 1614053) B1614053
theorem B1076051 : Blo 1072617 1076051 := bstep (se 1 (by rfl) ⟨807038, by rfl⟩ : syracuseStep 1076051 = 1614077) B1614077
theorem B1076067 : Blo 1072617 1076067 := bstep (se 1 (by rfl) ⟨807050, by rfl⟩ : syracuseStep 1076067 = 1614101) B1614101
theorem B3631985 : Blo 1072617 3631985 := bstep (se 2 (by rfl) ⟨1361994, by rfl⟩ : syracuseStep 3631985 = 2723989) B2723989
theorem B1076083 : Blo 1072617 1076083 := bstep (se 1 (by rfl) ⟨807062, by rfl⟩ : syracuseStep 1076083 = 1614125) B1614125
theorem B1076099 : Blo 1072617 1076099 := bstep (se 1 (by rfl) ⟨807074, by rfl⟩ : syracuseStep 1076099 = 1614149) B1614149
theorem B1076115 : Blo 1072617 1076115 := bstep (se 1 (by rfl) ⟨807086, by rfl⟩ : syracuseStep 1076115 = 1614173) B1614173
theorem B1076131 : Blo 1072617 1076131 := bstep (se 1 (by rfl) ⟨807098, by rfl⟩ : syracuseStep 1076131 = 1614197) B1614197
theorem B5434289 : Blo 1072617 5434289 := bstep (se 2 (by rfl) ⟨2037858, by rfl⟩ : syracuseStep 5434289 = 4075717) B4075717
theorem B1207219 : Blo 1072617 1207219 := bstep (se 1 (by rfl) ⟨905414, by rfl⟩ : syracuseStep 1207219 = 1810829) B1810829
theorem B1076147 : Blo 1072617 1076147 := bstep (se 1 (by rfl) ⟨807110, by rfl⟩ : syracuseStep 1076147 = 1614221) B1614221
theorem B1076163 : Blo 1072617 1076163 := bstep (se 1 (by rfl) ⟨807122, by rfl⟩ : syracuseStep 1076163 = 1614245) B1614245
theorem B1076179 : Blo 1072617 1076179 := bstep (se 1 (by rfl) ⟨807134, by rfl⟩ : syracuseStep 1076179 = 1614269) B1614269
theorem B1076195 : Blo 1072617 1076195 := bstep (se 1 (by rfl) ⟨807146, by rfl⟩ : syracuseStep 1076195 = 1614293) B1614293
theorem B1076211 : Blo 1072617 1076211 := bstep (se 1 (by rfl) ⟨807158, by rfl⟩ : syracuseStep 1076211 = 1614317) B1614317
theorem B1076227 : Blo 1072617 1076227 := bstep (se 1 (by rfl) ⟨807170, by rfl⟩ : syracuseStep 1076227 = 1614341) B1614341
theorem B2583569 : Blo 1072617 2583569 := bstep (se 2 (by rfl) ⟨968838, by rfl⟩ : syracuseStep 2583569 = 1937677) B1937677
theorem B1076243 : Blo 1072617 1076243 := bstep (se 1 (by rfl) ⟨807182, by rfl⟩ : syracuseStep 1076243 = 1614365) B1614365
theorem B1076259 : Blo 1072617 1076259 := bstep (se 1 (by rfl) ⟨807194, by rfl⟩ : syracuseStep 1076259 = 1614389) B1614389
theorem B1076275 : Blo 1072617 1076275 := bstep (se 1 (by rfl) ⟨807206, by rfl⟩ : syracuseStep 1076275 = 1614413) B1614413
theorem B1207363 : Blo 1072617 1207363 := bstep (se 1 (by rfl) ⟨905522, by rfl⟩ : syracuseStep 1207363 = 1811045) B1811045
theorem B1076291 : Blo 1072617 1076291 := bstep (se 1 (by rfl) ⟨807218, by rfl⟩ : syracuseStep 1076291 = 1614437) B1614437
theorem B2419793 : Blo 1072617 2419793 := bstep (se 2 (by rfl) ⟨907422, by rfl⟩ : syracuseStep 2419793 = 1814845) B1814845
theorem B1076307 : Blo 1072617 1076307 := bstep (se 1 (by rfl) ⟨807230, by rfl⟩ : syracuseStep 1076307 = 1614461) B1614461
theorem B1961059 : Blo 1072617 1961059 := bstep (se 1 (by rfl) ⟨1470794, by rfl⟩ : syracuseStep 1961059 = 2941589) B2941589
theorem B2419811 : Blo 1072617 2419811 := bstep (se 1 (by rfl) ⟨1814858, by rfl⟩ : syracuseStep 2419811 = 3629717) B3629717
theorem B1076323 : Blo 1072617 1076323 := bstep (se 1 (by rfl) ⟨807242, by rfl⟩ : syracuseStep 1076323 = 1614485) B1614485
theorem B1076339 : Blo 1072617 1076339 := bstep (se 1 (by rfl) ⟨807254, by rfl⟩ : syracuseStep 1076339 = 1614509) B1614509
theorem B1076355 : Blo 1072617 1076355 := bstep (se 1 (by rfl) ⟨807266, by rfl⟩ : syracuseStep 1076355 = 1614533) B1614533
theorem B1076371 : Blo 1072617 1076371 := bstep (se 1 (by rfl) ⟨807278, by rfl⟩ : syracuseStep 1076371 = 1614557) B1614557
theorem B1076387 : Blo 1072617 1076387 := bstep (se 1 (by rfl) ⟨807290, by rfl⟩ : syracuseStep 1076387 = 1614581) B1614581
theorem B1076403 : Blo 1072617 1076403 := bstep (se 1 (by rfl) ⟨807302, by rfl⟩ : syracuseStep 1076403 = 1614605) B1614605
theorem B1076419 : Blo 1072617 1076419 := bstep (se 1 (by rfl) ⟨807314, by rfl⟩ : syracuseStep 1076419 = 1614629) B1614629
theorem B1207507 : Blo 1072617 1207507 := bstep (se 1 (by rfl) ⟨905630, by rfl⟩ : syracuseStep 1207507 = 1811261) B1811261
theorem B1076435 : Blo 1072617 1076435 := bstep (se 1 (by rfl) ⟨807326, by rfl⟩ : syracuseStep 1076435 = 1614653) B1614653
theorem B1076451 : Blo 1072617 1076451 := bstep (se 1 (by rfl) ⟨807338, by rfl⟩ : syracuseStep 1076451 = 1614677) B1614677
theorem B1076467 : Blo 1072617 1076467 := bstep (se 1 (by rfl) ⟨807350, by rfl⟩ : syracuseStep 1076467 = 1614701) B1614701
theorem B1076483 : Blo 1072617 1076483 := bstep (se 1 (by rfl) ⟨807362, by rfl⟩ : syracuseStep 1076483 = 1614725) B1614725
theorem B1076499 : Blo 1072617 1076499 := bstep (se 1 (by rfl) ⟨807374, by rfl⟩ : syracuseStep 1076499 = 1614749) B1614749
theorem B1076515 : Blo 1072617 1076515 := bstep (se 1 (by rfl) ⟨807386, by rfl⟩ : syracuseStep 1076515 = 1614773) B1614773
theorem B1076531 : Blo 1072617 1076531 := bstep (se 1 (by rfl) ⟨807398, by rfl⟩ : syracuseStep 1076531 = 1614797) B1614797
theorem B1076547 : Blo 1072617 1076547 := bstep (se 1 (by rfl) ⟨807410, by rfl⟩ : syracuseStep 1076547 = 1614821) B1614821
theorem B1076563 : Blo 1072617 1076563 := bstep (se 1 (by rfl) ⟨807422, by rfl⟩ : syracuseStep 1076563 = 1614845) B1614845
theorem B1207651 : Blo 1072617 1207651 := bstep (se 1 (by rfl) ⟨905738, by rfl⟩ : syracuseStep 1207651 = 1811477) B1811477
theorem B1076579 : Blo 1072617 1076579 := bstep (se 1 (by rfl) ⟨807434, by rfl⟩ : syracuseStep 1076579 = 1614869) B1614869
theorem B2420081 : Blo 1072617 2420081 := bstep (se 2 (by rfl) ⟨907530, by rfl⟩ : syracuseStep 2420081 = 1815061) B1815061
theorem B1076595 : Blo 1072617 1076595 := bstep (se 1 (by rfl) ⟨807446, by rfl⟩ : syracuseStep 1076595 = 1614893) B1614893
theorem B2420099 : Blo 1072617 2420099 := bstep (se 1 (by rfl) ⟨1815074, by rfl⟩ : syracuseStep 2420099 = 3630149) B3630149
theorem B1076611 : Blo 1072617 1076611 := bstep (se 1 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 1076611 = 1614917) B1614917
theorem B3632525 : Blo 1072617 3632525 := bstep (se 3 (by rfl) ⟨681098, by rfl⟩ : syracuseStep 3632525 = 1362197) B1362197
theorem B2583953 : Blo 1072617 2583953 := bstep (se 2 (by rfl) ⟨968982, by rfl⟩ : syracuseStep 2583953 = 1937965) B1937965
theorem B3632579 : Blo 1072617 3632579 := bstep (se 1 (by rfl) ⟨2724434, by rfl⟩ : syracuseStep 3632579 = 5448869) B5448869
theorem B1207795 : Blo 1072617 1207795 := bstep (se 1 (by rfl) ⟨905846, by rfl⟩ : syracuseStep 1207795 = 1811693) B1811693
theorem B2584163 : Blo 1072617 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B1207939 : Blo 1072617 1207939 := bstep (se 1 (by rfl) ⟨905954, by rfl⟩ : syracuseStep 1207939 = 1811909) B1811909
theorem B3272333 : Blo 1072617 3272333 := bstep (se 3 (by rfl) ⟨613562, by rfl⟩ : syracuseStep 3272333 = 1227125) B1227125
theorem B2420369 : Blo 1072617 2420369 := bstep (se 2 (by rfl) ⟨907638, by rfl⟩ : syracuseStep 2420369 = 1815277) B1815277
theorem B2420387 : Blo 1072617 2420387 := bstep (se 1 (by rfl) ⟨1815290, by rfl⟩ : syracuseStep 2420387 = 3630581) B3630581
theorem B3632849 : Blo 1072617 3632849 := bstep (se 2 (by rfl) ⟨1362318, by rfl⟩ : syracuseStep 3632849 = 2724637) B2724637
theorem B1634003 : Blo 1072617 1634003 := bstep (se 1 (by rfl) ⟨1225502, by rfl⟩ : syracuseStep 1634003 = 2451005) B2451005
theorem B6123235 : Blo 1072617 6123235 := bstep (se 1 (by rfl) ⟨4592426, by rfl⟩ : syracuseStep 6123235 = 9184853) B9184853
theorem B3436273 : Blo 1072617 3436273 := bstep (se 2 (by rfl) ⟨1288602, by rfl⟩ : syracuseStep 3436273 = 2577205) B2577205
theorem B1208083 : Blo 1072617 1208083 := bstep (se 1 (by rfl) ⟨906062, by rfl⟩ : syracuseStep 1208083 = 1812125) B1812125
theorem B1208227 : Blo 1072617 1208227 := bstep (se 1 (by rfl) ⟨906170, by rfl⟩ : syracuseStep 1208227 = 1812341) B1812341
theorem B2420657 : Blo 1072617 2420657 := bstep (se 2 (by rfl) ⟨907746, by rfl⟩ : syracuseStep 2420657 = 1815493) B1815493
theorem B2420675 : Blo 1072617 2420675 := bstep (se 1 (by rfl) ⟨1815506, by rfl⟩ : syracuseStep 2420675 = 3631013) B3631013
theorem B1208371 : Blo 1072617 1208371 := bstep (se 1 (by rfl) ⟨906278, by rfl⟩ : syracuseStep 1208371 = 1812557) B1812557
theorem B1208515 : Blo 1072617 1208515 := bstep (se 1 (by rfl) ⟨906386, by rfl⟩ : syracuseStep 1208515 = 1812773) B1812773
theorem B2420945 : Blo 1072617 2420945 := bstep (se 2 (by rfl) ⟨907854, by rfl⟩ : syracuseStep 2420945 = 1815709) B1815709
theorem B2420963 : Blo 1072617 2420963 := bstep (se 1 (by rfl) ⟨1815722, by rfl⟩ : syracuseStep 2420963 = 3631445) B3631445
theorem B3633389 : Blo 1072617 3633389 := bstep (se 3 (by rfl) ⟨681260, by rfl⟩ : syracuseStep 3633389 = 1362521) B1362521
theorem B2715889 : Blo 1072617 2715889 := bstep (se 2 (by rfl) ⟨1018458, by rfl⟩ : syracuseStep 2715889 = 2036917) B2036917
theorem B6123761 : Blo 1072617 6123761 := bstep (se 2 (by rfl) ⟨2296410, by rfl⟩ : syracuseStep 6123761 = 4592821) B4592821
theorem B3633443 : Blo 1072617 3633443 := bstep (se 1 (by rfl) ⟨2725082, by rfl⟩ : syracuseStep 3633443 = 5450165) B5450165
theorem B1208659 : Blo 1072617 1208659 := bstep (se 1 (by rfl) ⟨906494, by rfl⟩ : syracuseStep 1208659 = 1812989) B1812989
theorem B5435747 : Blo 1072617 5435747 := bstep (se 1 (by rfl) ⟨4076810, by rfl⟩ : syracuseStep 5435747 = 8153621) B8153621
theorem B2355569 : Blo 1072617 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B2585009 : Blo 1072617 2585009 := bstep (se 2 (by rfl) ⟨969378, by rfl⟩ : syracuseStep 2585009 = 1938757) B1938757
theorem B12251573 : Blo 1072617 12251573 := bstep (se 5 (by rfl) ⟨574292, by rfl⟩ : syracuseStep 12251573 = 1148585) B1148585
theorem B1208803 : Blo 1072617 1208803 := bstep (se 1 (by rfl) ⟨906602, by rfl⟩ : syracuseStep 1208803 = 1813205) B1813205
theorem B2421233 : Blo 1072617 2421233 := bstep (se 2 (by rfl) ⟨907962, by rfl⟩ : syracuseStep 2421233 = 1815925) B1815925
theorem B2716163 : Blo 1072617 2716163 := bstep (se 1 (by rfl) ⟨2037122, by rfl⟩ : syracuseStep 2716163 = 4074245) B4074245
theorem B2421251 : Blo 1072617 2421251 := bstep (se 1 (by rfl) ⟨1815938, by rfl⟩ : syracuseStep 2421251 = 3631877) B3631877
theorem B11629169 : Blo 1072617 11629169 := bstep (se 2 (by rfl) ⟨4360938, by rfl⟩ : syracuseStep 11629169 = 8721877) B8721877
theorem B2585201 : Blo 1072617 2585201 := bstep (se 2 (by rfl) ⟨969450, by rfl⟩ : syracuseStep 2585201 = 1938901) B1938901
theorem B1208947 : Blo 1072617 1208947 := bstep (se 1 (by rfl) ⟨906710, by rfl⟩ : syracuseStep 1208947 = 1813421) B1813421
theorem B1634945 : Blo 1072617 1634945 := bstep (se 2 (by rfl) ⟨613104, by rfl⟩ : syracuseStep 1634945 = 1226209) B1226209
theorem B1634963 : Blo 1072617 1634963 := bstep (se 1 (by rfl) ⟨1226222, by rfl⟩ : syracuseStep 1634963 = 2452445) B2452445
theorem B2716355 : Blo 1072617 2716355 := bstep (se 1 (by rfl) ⟨2037266, by rfl⟩ : syracuseStep 2716355 = 4074533) B4074533
theorem B1209091 : Blo 1072617 1209091 := bstep (se 1 (by rfl) ⟨906818, by rfl⟩ : syracuseStep 1209091 = 1813637) B1813637
theorem B2421521 : Blo 1072617 2421521 := bstep (se 2 (by rfl) ⟨908070, by rfl⟩ : syracuseStep 2421521 = 1816141) B1816141
theorem B2421539 : Blo 1072617 2421539 := bstep (se 1 (by rfl) ⟨1816154, by rfl⟩ : syracuseStep 2421539 = 3632309) B3632309
theorem B10318661 : Blo 1072617 10318661 := bstep (se 4 (by rfl) ⟨967374, by rfl⟩ : syracuseStep 10318661 = 1934749) B1934749
theorem B1209235 : Blo 1072617 1209235 := bstep (se 1 (by rfl) ⟨906926, by rfl⟩ : syracuseStep 1209235 = 1813853) B1813853
theorem B4584397 : Blo 1072617 4584397 := bstep (se 3 (by rfl) ⟨859574, by rfl⟩ : syracuseStep 4584397 = 1719149) B1719149
theorem B1209379 : Blo 1072617 1209379 := bstep (se 1 (by rfl) ⟨907034, by rfl⟩ : syracuseStep 1209379 = 1814069) B1814069
theorem B2421809 : Blo 1072617 2421809 := bstep (se 2 (by rfl) ⟨908178, by rfl⟩ : syracuseStep 2421809 = 1816357) B1816357
theorem B2421827 : Blo 1072617 2421827 := bstep (se 1 (by rfl) ⟨1816370, by rfl⟩ : syracuseStep 2421827 = 3632741) B3632741
theorem B5436557 : Blo 1072617 5436557 := bstep (se 3 (by rfl) ⟨1019354, by rfl⟩ : syracuseStep 5436557 = 2038709) B2038709
theorem B1209523 : Blo 1072617 1209523 := bstep (se 1 (by rfl) ⟨907142, by rfl⟩ : syracuseStep 1209523 = 1814285) B1814285
theorem B1209667 : Blo 1072617 1209667 := bstep (se 1 (by rfl) ⟨907250, by rfl⟩ : syracuseStep 1209667 = 1814501) B1814501
theorem B2422097 : Blo 1072617 2422097 := bstep (se 2 (by rfl) ⟨908286, by rfl⟩ : syracuseStep 2422097 = 1816573) B1816573
theorem B2422115 : Blo 1072617 2422115 := bstep (se 1 (by rfl) ⟨1816586, by rfl⟩ : syracuseStep 2422115 = 3633173) B3633173
theorem B1209811 : Blo 1072617 1209811 := bstep (se 1 (by rfl) ⟨907358, by rfl⟩ : syracuseStep 1209811 = 1814717) B1814717
theorem B1570291 : Blo 1072617 1570291 := bstep (se 1 (by rfl) ⟨1177718, by rfl⟩ : syracuseStep 1570291 = 2355437) B2355437
theorem B1209955 : Blo 1072617 1209955 := bstep (se 1 (by rfl) ⟨907466, by rfl⟩ : syracuseStep 1209955 = 1814933) B1814933
theorem B2717297 : Blo 1072617 2717297 := bstep (se 2 (by rfl) ⟨1018986, by rfl⟩ : syracuseStep 2717297 = 2037973) B2037973
theorem B2422385 : Blo 1072617 2422385 := bstep (se 2 (by rfl) ⟨908394, by rfl⟩ : syracuseStep 2422385 = 1816789) B1816789
theorem B2717347 : Blo 1072617 2717347 := bstep (se 1 (by rfl) ⟨2038010, by rfl⟩ : syracuseStep 2717347 = 4076021) B4076021
theorem B6125219 : Blo 1072617 6125219 := bstep (se 1 (by rfl) ⟨4593914, by rfl⟩ : syracuseStep 6125219 = 9187829) B9187829
theorem B1210099 : Blo 1072617 1210099 := bstep (se 1 (by rfl) ⟨907574, by rfl⟩ : syracuseStep 1210099 = 1815149) B1815149
theorem B2717489 : Blo 1072617 2717489 := bstep (se 2 (by rfl) ⟨1019058, by rfl⟩ : syracuseStep 2717489 = 2038117) B2038117
theorem B2324305 : Blo 1072617 2324305 := bstep (se 2 (by rfl) ⟨871614, by rfl⟩ : syracuseStep 2324305 = 1743229) B1743229
theorem B1210243 : Blo 1072617 1210243 := bstep (se 1 (by rfl) ⟨907682, by rfl⟩ : syracuseStep 1210243 = 1815365) B1815365
theorem B1210387 : Blo 1072617 1210387 := bstep (se 1 (by rfl) ⟨907790, by rfl⟩ : syracuseStep 1210387 = 1815581) B1815581
theorem B1210531 : Blo 1072617 1210531 := bstep (se 1 (by rfl) ⟨907898, by rfl⟩ : syracuseStep 1210531 = 1815797) B1815797
theorem B1210675 : Blo 1072617 1210675 := bstep (se 1 (by rfl) ⟨908006, by rfl⟩ : syracuseStep 1210675 = 1816013) B1816013
theorem B8157509 : Blo 1072617 8157509 := bstep (se 4 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 8157509 = 1529533) B1529533
theorem B1309043 : Blo 1072617 1309043 := bstep (se 1 (by rfl) ⟨981782, by rfl⟩ : syracuseStep 1309043 = 1963565) B1963565
theorem B2292113 : Blo 1072617 2292113 := bstep (se 2 (by rfl) ⟨859542, by rfl⟩ : syracuseStep 2292113 = 1719085) B1719085
theorem B2292131 : Blo 1072617 2292131 := bstep (se 1 (by rfl) ⟨1719098, by rfl⟩ : syracuseStep 2292131 = 3438197) B3438197
theorem B2619811 : Blo 1072617 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B1210819 : Blo 1072617 1210819 := bstep (se 1 (by rfl) ⟨908114, by rfl⟩ : syracuseStep 1210819 = 1816229) B1816229
theorem B14678597 : Blo 1072617 14678597 := bstep (se 4 (by rfl) ⟨1376118, by rfl⟩ : syracuseStep 14678597 = 2752237) B2752237
theorem B1210963 : Blo 1072617 1210963 := bstep (se 1 (by rfl) ⟨908222, by rfl⟩ : syracuseStep 1210963 = 1816445) B1816445
theorem B9173645 : Blo 1072617 9173645 := bstep (se 3 (by rfl) ⟨1720058, by rfl⟩ : syracuseStep 9173645 = 3440117) B3440117
theorem B1211107 : Blo 1072617 1211107 := bstep (se 1 (by rfl) ⟨908330, by rfl⟩ : syracuseStep 1211107 = 1816661) B1816661
theorem B2718481 : Blo 1072617 2718481 := bstep (se 2 (by rfl) ⟨1019430, by rfl⟩ : syracuseStep 2718481 = 2038861) B2038861
theorem B2718755 : Blo 1072617 2718755 := bstep (se 1 (by rfl) ⟨2039066, by rfl⟩ : syracuseStep 2718755 = 4078133) B4078133
theorem B1145971 : Blo 1072617 1145971 := bstep (se 1 (by rfl) ⟨859478, by rfl⟩ : syracuseStep 1145971 = 1718957) B1718957
theorem B2718947 : Blo 1072617 2718947 := bstep (se 1 (by rfl) ⟨2039210, by rfl⟩ : syracuseStep 2718947 = 4078421) B4078421
theorem B1965379 : Blo 1072617 1965379 := bstep (se 1 (by rfl) ⟨1474034, by rfl⟩ : syracuseStep 1965379 = 2948069) B2948069
theorem B6127109 : Blo 1072617 6127109 := bstep (se 4 (by rfl) ⟨574416, by rfl⟩ : syracuseStep 6127109 = 1148833) B1148833
theorem B13762061 : Blo 1072617 13762061 := bstep (se 3 (by rfl) ⟨2580386, by rfl⟩ : syracuseStep 13762061 = 5160773) B5160773
theorem B4358051 : Blo 1072617 4358051 := bstep (se 1 (by rfl) ⟨3268538, by rfl⟩ : syracuseStep 4358051 = 6537077) B6537077
theorem B8257477 : Blo 1072617 8257477 := bstep (se 4 (by rfl) ⟨774138, by rfl⟩ : syracuseStep 8257477 = 1548277) B1548277
theorem B5439473 : Blo 1072617 5439473 := bstep (se 2 (by rfl) ⟨2039802, by rfl⟩ : syracuseStep 5439473 = 4079605) B4079605
theorem B2293771 : Blo 1072617 2293771 := bstep (se 1 (by rfl) ⟨1720328, by rfl⟩ : syracuseStep 2293771 = 3440657) B3440657
theorem B4587779 : Blo 1072617 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B1147159 : Blo 1072617 1147159 := bstep (se 1 (by rfl) ⟨860369, by rfl⟩ : syracuseStep 1147159 = 1720739) B1720739
theorem B2621719 : Blo 1072617 2621719 := bstep (se 1 (by rfl) ⟨1966289, by rfl⟩ : syracuseStep 2621719 = 3932579) B3932579
theorem B2720051 : Blo 1072617 2720051 := bstep (se 1 (by rfl) ⟨2040038, by rfl⟩ : syracuseStep 2720051 = 4080077) B4080077
theorem B2326849 : Blo 1072617 2326849 := bstep (se 2 (by rfl) ⟨872568, by rfl⟩ : syracuseStep 2326849 = 1745137) B1745137
theorem B13763033 : Blo 1072617 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B1933913 : Blo 1072617 1933913 := bstep (se 2 (by rfl) ⟨725217, by rfl⟩ : syracuseStep 1933913 = 1450435) B1450435
theorem B2720587 : Blo 1072617 2720587 := bstep (se 1 (by rfl) ⟨2040440, by rfl⟩ : syracuseStep 2720587 = 4080881) B4080881
theorem B2720729 : Blo 1072617 2720729 := bstep (se 2 (by rfl) ⟨1020273, by rfl⟩ : syracuseStep 2720729 = 2040547) B2040547
theorem B1147979 : Blo 1072617 1147979 := bstep (se 1 (by rfl) ⟨860984, by rfl⟩ : syracuseStep 1147979 = 1721969) B1721969
theorem B2295155 : Blo 1072617 2295155 := bstep (se 1 (by rfl) ⟨1721366, by rfl⟩ : syracuseStep 2295155 = 3442733) B3442733
theorem B4130327 : Blo 1072617 4130327 := bstep (se 1 (by rfl) ⟨3097745, by rfl⟩ : syracuseStep 4130327 = 6195491) B6195491
theorem B4359853 : Blo 1072617 4359853 := bstep (se 3 (by rfl) ⟨817472, by rfl⟩ : syracuseStep 4359853 = 1634945) B1634945
theorem B4359901 : Blo 1072617 4359901 := bstep (se 3 (by rfl) ⟨817481, by rfl⟩ : syracuseStep 4359901 = 1634963) B1634963
theorem B2721559 : Blo 1072617 2721559 := bstep (se 1 (by rfl) ⟨2041169, by rfl⟩ : syracuseStep 2721559 = 4082339) B4082339
theorem B4589405 : Blo 1072617 4589405 := bstep (se 3 (by rfl) ⟨860513, by rfl⟩ : syracuseStep 4589405 = 1721027) B1721027
theorem B4130833 : Blo 1072617 4130833 := bstep (se 2 (by rfl) ⟨1549062, by rfl⟩ : syracuseStep 4130833 = 3098125) B3098125
theorem B102139957 : Blo 1072617 102139957 := bstep (se 5 (by rfl) ⟨4787810, by rfl⟩ : syracuseStep 102139957 = 9575621) B9575621
theorem B10324043 : Blo 1072617 10324043 := bstep (se 1 (by rfl) ⟨7743032, by rfl⟩ : syracuseStep 10324043 = 15486065) B15486065
theorem B2296001 : Blo 1072617 2296001 := bstep (se 2 (by rfl) ⟨861000, by rfl⟩ : syracuseStep 2296001 = 1722001) B1722001
theorem B2721995 : Blo 1072617 2721995 := bstep (se 1 (by rfl) ⟨2041496, by rfl⟩ : syracuseStep 2721995 = 4082993) B4082993
theorem B1149175 : Blo 1072617 1149175 := bstep (se 1 (by rfl) ⟨861881, by rfl⟩ : syracuseStep 1149175 = 1723763) B1723763
theorem B4360451 : Blo 1072617 4360451 := bstep (se 1 (by rfl) ⟨3270338, by rfl⟩ : syracuseStep 4360451 = 6540677) B6540677
theorem B8259941 : Blo 1072617 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B88279409 : Blo 1072617 88279409 := bstep (se 2 (by rfl) ⟨33104778, by rfl⟩ : syracuseStep 88279409 = 66209557) B66209557
theorem B7735769 : Blo 1072617 7735769 := bstep (se 2 (by rfl) ⟨2900913, by rfl⟩ : syracuseStep 7735769 = 5801827) B5801827
theorem B5442065 : Blo 1072617 5442065 := bstep (se 2 (by rfl) ⟨2040774, by rfl⟩ : syracuseStep 5442065 = 4081549) B4081549
theorem B4590103 : Blo 1072617 4590103 := bstep (se 1 (by rfl) ⟨3442577, by rfl⟩ : syracuseStep 4590103 = 6885155) B6885155
theorem B2296343 : Blo 1072617 2296343 := bstep (se 1 (by rfl) ⟨1722257, by rfl⟩ : syracuseStep 2296343 = 3444515) B3444515
theorem B14715427 : Blo 1072617 14715427 := bstep (se 1 (by rfl) ⟨11036570, by rfl⟩ : syracuseStep 14715427 = 22073141) B22073141
theorem B2722369 : Blo 1072617 2722369 := bstep (se 2 (by rfl) ⟨1020888, by rfl⟩ : syracuseStep 2722369 = 2041777) B2041777
theorem B5442227 : Blo 1072617 5442227 := bstep (se 1 (by rfl) ⟨4081670, by rfl⟩ : syracuseStep 5442227 = 8163341) B8163341
theorem B4131607 : Blo 1072617 4131607 := bstep (se 1 (by rfl) ⟨3098705, by rfl⟩ : syracuseStep 4131607 = 6197411) B6197411
theorem B6130525 : Blo 1072617 6130525 := bstep (se 3 (by rfl) ⟨1149473, by rfl⟩ : syracuseStep 6130525 = 2298947) B2298947
theorem B5802931 : Blo 1072617 5802931 := bstep (se 1 (by rfl) ⟨4352198, by rfl⟩ : syracuseStep 5802931 = 8704397) B8704397
theorem B8162369 : Blo 1072617 8162369 := bstep (se 2 (by rfl) ⟨3060888, by rfl⟩ : syracuseStep 8162369 = 6121777) B6121777
theorem B18353303 : Blo 1072617 18353303 := bstep (se 1 (by rfl) ⟨13764977, by rfl⟩ : syracuseStep 18353303 = 27529955) B27529955
theorem B2722967 : Blo 1072617 2722967 := bstep (se 1 (by rfl) ⟨2042225, by rfl⟩ : syracuseStep 2722967 = 4084451) B4084451
theorem B1379531 : Blo 1072617 1379531 := bstep (se 1 (by rfl) ⟨1034648, by rfl⟩ : syracuseStep 1379531 = 2069297) B2069297
theorem B1608971 : Blo 1072617 1608971 := bstep (se 1 (by rfl) ⟨1206728, by rfl⟩ : syracuseStep 1608971 = 2413457) B2413457
theorem B1608983 : Blo 1072617 1608983 := bstep (se 1 (by rfl) ⟨1206737, by rfl⟩ : syracuseStep 1608983 = 2413475) B2413475
theorem B1609049 : Blo 1072617 1609049 := bstep (se 2 (by rfl) ⟨603393, by rfl⟩ : syracuseStep 1609049 = 1206787) B1206787
theorem B1609163 : Blo 1072617 1609163 := bstep (se 1 (by rfl) ⟨1206872, by rfl⟩ : syracuseStep 1609163 = 2413745) B2413745
theorem B1609175 : Blo 1072617 1609175 := bstep (se 1 (by rfl) ⟨1206881, by rfl⟩ : syracuseStep 1609175 = 2413763) B2413763
theorem B1609241 : Blo 1072617 1609241 := bstep (se 2 (by rfl) ⟨603465, by rfl⟩ : syracuseStep 1609241 = 1206931) B1206931
theorem B1609355 : Blo 1072617 1609355 := bstep (se 1 (by rfl) ⟨1207016, by rfl⟩ : syracuseStep 1609355 = 2414033) B2414033
theorem B1609367 : Blo 1072617 1609367 := bstep (se 1 (by rfl) ⟨1207025, by rfl⟩ : syracuseStep 1609367 = 2414051) B2414051
theorem B8261297 : Blo 1072617 8261297 := bstep (se 2 (by rfl) ⟨3097986, by rfl⟩ : syracuseStep 8261297 = 6195973) B6195973
theorem B1609433 : Blo 1072617 1609433 := bstep (se 2 (by rfl) ⟨603537, by rfl⟩ : syracuseStep 1609433 = 1207075) B1207075
theorem B3870467 : Blo 1072617 3870467 := bstep (se 1 (by rfl) ⟨2902850, by rfl⟩ : syracuseStep 3870467 = 5805701) B5805701
theorem B1609547 : Blo 1072617 1609547 := bstep (se 1 (by rfl) ⟨1207160, by rfl⟩ : syracuseStep 1609547 = 2414321) B2414321
theorem B1609559 : Blo 1072617 1609559 := bstep (se 1 (by rfl) ⟨1207169, by rfl⟩ : syracuseStep 1609559 = 2414339) B2414339
theorem B4591505 : Blo 1072617 4591505 := bstep (se 2 (by rfl) ⟨1721814, by rfl⟩ : syracuseStep 4591505 = 3443629) B3443629
theorem B1609625 : Blo 1072617 1609625 := bstep (se 2 (by rfl) ⟨603609, by rfl⟩ : syracuseStep 1609625 = 1207219) B1207219
theorem B2723777 : Blo 1072617 2723777 := bstep (se 2 (by rfl) ⟨1021416, by rfl⟩ : syracuseStep 2723777 = 2042833) B2042833
theorem B2297803 : Blo 1072617 2297803 := bstep (se 1 (by rfl) ⟨1723352, by rfl⟩ : syracuseStep 2297803 = 3446705) B3446705
theorem B1609739 : Blo 1072617 1609739 := bstep (se 1 (by rfl) ⟨1207304, by rfl⟩ : syracuseStep 1609739 = 2414609) B2414609
theorem B1609751 : Blo 1072617 1609751 := bstep (se 1 (by rfl) ⟨1207313, by rfl⟩ : syracuseStep 1609751 = 2414627) B2414627
theorem B1609817 : Blo 1072617 1609817 := bstep (se 2 (by rfl) ⟨603681, by rfl⟩ : syracuseStep 1609817 = 1207363) B1207363
theorem B1609931 : Blo 1072617 1609931 := bstep (se 1 (by rfl) ⟨1207448, by rfl⟩ : syracuseStep 1609931 = 2414897) B2414897
theorem B2298059 : Blo 1072617 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B1609943 : Blo 1072617 1609943 := bstep (se 1 (by rfl) ⟨1207457, by rfl⟩ : syracuseStep 1609943 = 2414915) B2414915
theorem B1610009 : Blo 1072617 1610009 := bstep (se 2 (by rfl) ⟨603753, by rfl⟩ : syracuseStep 1610009 = 1207507) B1207507
theorem B13767029 : Blo 1072617 13767029 := bstep (se 5 (by rfl) ⟨645329, by rfl⟩ : syracuseStep 13767029 = 1290659) B1290659
theorem B1610123 : Blo 1072617 1610123 := bstep (se 1 (by rfl) ⟨1207592, by rfl⟩ : syracuseStep 1610123 = 2415185) B2415185
theorem B1610135 : Blo 1072617 1610135 := bstep (se 1 (by rfl) ⟨1207601, by rfl⟩ : syracuseStep 1610135 = 2415203) B2415203
theorem B1610201 : Blo 1072617 1610201 := bstep (se 2 (by rfl) ⟨603825, by rfl⟩ : syracuseStep 1610201 = 1207651) B1207651
theorem B2724313 : Blo 1072617 2724313 := bstep (se 2 (by rfl) ⟨1021617, by rfl⟩ : syracuseStep 2724313 = 2043235) B2043235
theorem B1610315 : Blo 1072617 1610315 := bstep (se 1 (by rfl) ⟨1207736, by rfl⟩ : syracuseStep 1610315 = 2415473) B2415473
theorem B5444171 : Blo 1072617 5444171 := bstep (se 1 (by rfl) ⟨4083128, by rfl⟩ : syracuseStep 5444171 = 8166257) B8166257
theorem B1610327 : Blo 1072617 1610327 := bstep (se 1 (by rfl) ⟨1207745, by rfl⟩ : syracuseStep 1610327 = 2415491) B2415491
theorem B1938007 : Blo 1072617 1938007 := bstep (se 1 (by rfl) ⟨1453505, by rfl⟩ : syracuseStep 1938007 = 2907011) B2907011
theorem B1610393 : Blo 1072617 1610393 := bstep (se 2 (by rfl) ⟨603897, by rfl⟩ : syracuseStep 1610393 = 1207795) B1207795
theorem B7344857 : Blo 1072617 7344857 := bstep (se 2 (by rfl) ⟨2754321, by rfl⟩ : syracuseStep 7344857 = 5508643) B5508643
theorem B1610507 : Blo 1072617 1610507 := bstep (se 1 (by rfl) ⟨1207880, by rfl⟩ : syracuseStep 1610507 = 2415761) B2415761
theorem B9573137 : Blo 1072617 9573137 := bstep (se 2 (by rfl) ⟨3589926, by rfl⟩ : syracuseStep 9573137 = 7179853) B7179853
theorem B1610519 : Blo 1072617 1610519 := bstep (se 1 (by rfl) ⟨1207889, by rfl⟩ : syracuseStep 1610519 = 2415779) B2415779
theorem B1610585 : Blo 1072617 1610585 := bstep (se 2 (by rfl) ⟨603969, by rfl⟩ : syracuseStep 1610585 = 1207939) B1207939
theorem B2036659 : Blo 1072617 2036659 := bstep (se 1 (by rfl) ⟨1527494, by rfl⟩ : syracuseStep 2036659 = 3054989) B3054989
theorem B1610699 : Blo 1072617 1610699 := bstep (se 1 (by rfl) ⟨1208024, by rfl⟩ : syracuseStep 1610699 = 2416049) B2416049
theorem B1610711 : Blo 1072617 1610711 := bstep (se 1 (by rfl) ⟨1208033, by rfl⟩ : syracuseStep 1610711 = 2416067) B2416067
theorem B8164313 : Blo 1072617 8164313 := bstep (se 2 (by rfl) ⟨3061617, by rfl⟩ : syracuseStep 8164313 = 6123235) B6123235
theorem B4133911 : Blo 1072617 4133911 := bstep (se 1 (by rfl) ⟨3100433, by rfl⟩ : syracuseStep 4133911 = 6200867) B6200867
theorem B1610777 : Blo 1072617 1610777 := bstep (se 2 (by rfl) ⟨604041, by rfl⟩ : syracuseStep 1610777 = 1208083) B1208083
theorem B1610891 : Blo 1072617 1610891 := bstep (se 1 (by rfl) ⟨1208168, by rfl⟩ : syracuseStep 1610891 = 2416337) B2416337
theorem B1610903 : Blo 1072617 1610903 := bstep (se 1 (by rfl) ⟨1208177, by rfl⟩ : syracuseStep 1610903 = 2416355) B2416355
theorem B2299033 : Blo 1072617 2299033 := bstep (se 2 (by rfl) ⟨862137, by rfl⟩ : syracuseStep 2299033 = 1724275) B1724275
theorem B1610969 : Blo 1072617 1610969 := bstep (se 2 (by rfl) ⟨604113, by rfl⟩ : syracuseStep 1610969 = 1208227) B1208227
theorem B2299187 : Blo 1072617 2299187 := bstep (se 1 (by rfl) ⟨1724390, by rfl⟩ : syracuseStep 2299187 = 3448781) B3448781
theorem B1611083 : Blo 1072617 1611083 := bstep (se 1 (by rfl) ⟨1208312, by rfl⟩ : syracuseStep 1611083 = 2416625) B2416625
theorem B1611095 : Blo 1072617 1611095 := bstep (se 1 (by rfl) ⟨1208321, by rfl⟩ : syracuseStep 1611095 = 2416643) B2416643
theorem B1742231 : Blo 1072617 1742231 := bstep (se 1 (by rfl) ⟨1306673, by rfl⟩ : syracuseStep 1742231 = 2613347) B2613347
theorem B2037145 : Blo 1072617 2037145 := bstep (se 2 (by rfl) ⟨763929, by rfl⟩ : syracuseStep 2037145 = 1527859) B1527859
theorem B1611161 : Blo 1072617 1611161 := bstep (se 2 (by rfl) ⟨604185, by rfl⟩ : syracuseStep 1611161 = 1208371) B1208371
theorem B1611275 : Blo 1072617 1611275 := bstep (se 1 (by rfl) ⟨1208456, by rfl⟩ : syracuseStep 1611275 = 2416913) B2416913
theorem B1611287 : Blo 1072617 1611287 := bstep (se 1 (by rfl) ⟨1208465, by rfl⟩ : syracuseStep 1611287 = 2416931) B2416931
theorem B1611353 : Blo 1072617 1611353 := bstep (se 2 (by rfl) ⟨604257, by rfl⟩ : syracuseStep 1611353 = 1208515) B1208515
theorem B1611467 : Blo 1072617 1611467 := bstep (se 1 (by rfl) ⟨1208600, by rfl⟩ : syracuseStep 1611467 = 2417201) B2417201
theorem B1611479 : Blo 1072617 1611479 := bstep (se 1 (by rfl) ⟨1208609, by rfl⟩ : syracuseStep 1611479 = 2417219) B2417219
theorem B1611545 : Blo 1072617 1611545 := bstep (se 2 (by rfl) ⟨604329, by rfl⟩ : syracuseStep 1611545 = 1208659) B1208659
theorem B1611659 : Blo 1072617 1611659 := bstep (se 1 (by rfl) ⟨1208744, by rfl⟩ : syracuseStep 1611659 = 2417489) B2417489
theorem B1611671 : Blo 1072617 1611671 := bstep (se 1 (by rfl) ⟨1208753, by rfl⟩ : syracuseStep 1611671 = 2417507) B2417507
theorem B2037707 : Blo 1072617 2037707 := bstep (se 1 (by rfl) ⟨1528280, by rfl⟩ : syracuseStep 2037707 = 3056561) B3056561
theorem B1611737 : Blo 1072617 1611737 := bstep (se 2 (by rfl) ⟨604401, by rfl⟩ : syracuseStep 1611737 = 1208803) B1208803
theorem B3872785 : Blo 1072617 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B1611851 : Blo 1072617 1611851 := bstep (se 1 (by rfl) ⟨1208888, by rfl⟩ : syracuseStep 1611851 = 2417777) B2417777
theorem B1611863 : Blo 1072617 1611863 := bstep (se 1 (by rfl) ⟨1208897, by rfl⟩ : syracuseStep 1611863 = 2417795) B2417795
theorem B2037889 : Blo 1072617 2037889 := bstep (se 2 (by rfl) ⟨764208, by rfl⟩ : syracuseStep 2037889 = 1528417) B1528417
theorem B1611929 : Blo 1072617 1611929 := bstep (se 2 (by rfl) ⟨604473, by rfl⟩ : syracuseStep 1611929 = 1208947) B1208947
theorem B1939673 : Blo 1072617 1939673 := bstep (se 2 (by rfl) ⟨727377, by rfl⟩ : syracuseStep 1939673 = 1454755) B1454755
theorem B1612043 : Blo 1072617 1612043 := bstep (se 1 (by rfl) ⟨1209032, by rfl⟩ : syracuseStep 1612043 = 2418065) B2418065
theorem B1612055 : Blo 1072617 1612055 := bstep (se 1 (by rfl) ⟨1209041, by rfl⟩ : syracuseStep 1612055 = 2418083) B2418083
theorem B5445953 : Blo 1072617 5445953 := bstep (se 2 (by rfl) ⟨2042232, by rfl⟩ : syracuseStep 5445953 = 4084465) B4084465
theorem B1612121 : Blo 1072617 1612121 := bstep (se 2 (by rfl) ⟨604545, by rfl⟩ : syracuseStep 1612121 = 1209091) B1209091
theorem B3447191 : Blo 1072617 3447191 := bstep (se 1 (by rfl) ⟨2585393, by rfl⟩ : syracuseStep 3447191 = 5170787) B5170787
theorem B1612235 : Blo 1072617 1612235 := bstep (se 1 (by rfl) ⟨1209176, by rfl⟩ : syracuseStep 1612235 = 2418353) B2418353
theorem B1612247 : Blo 1072617 1612247 := bstep (se 1 (by rfl) ⟨1209185, by rfl⟩ : syracuseStep 1612247 = 2418371) B2418371
theorem B1612313 : Blo 1072617 1612313 := bstep (se 2 (by rfl) ⟨604617, by rfl⟩ : syracuseStep 1612313 = 1209235) B1209235
theorem B8395339 : Blo 1072617 8395339 := bstep (se 1 (by rfl) ⟨6296504, by rfl⟩ : syracuseStep 8395339 = 12593009) B12593009
theorem B1612427 : Blo 1072617 1612427 := bstep (se 1 (by rfl) ⟨1209320, by rfl⟩ : syracuseStep 1612427 = 2418641) B2418641
theorem B1612439 : Blo 1072617 1612439 := bstep (se 1 (by rfl) ⟨1209329, by rfl⟩ : syracuseStep 1612439 = 2418659) B2418659
theorem B1612505 : Blo 1072617 1612505 := bstep (se 2 (by rfl) ⟨604689, by rfl⟩ : syracuseStep 1612505 = 1209379) B1209379
theorem B3873581 : Blo 1072617 3873581 := bstep (se 3 (by rfl) ⟨726296, by rfl⟩ : syracuseStep 3873581 = 1452593) B1452593
theorem B4594477 : Blo 1072617 4594477 := bstep (se 3 (by rfl) ⟨861464, by rfl⟩ : syracuseStep 4594477 = 1722929) B1722929
theorem B2038603 : Blo 1072617 2038603 := bstep (se 1 (by rfl) ⟨1528952, by rfl⟩ : syracuseStep 2038603 = 3057905) B3057905
theorem B1612619 : Blo 1072617 1612619 := bstep (se 1 (by rfl) ⟨1209464, by rfl⟩ : syracuseStep 1612619 = 2418929) B2418929
theorem B1612631 : Blo 1072617 1612631 := bstep (se 1 (by rfl) ⟨1209473, by rfl⟩ : syracuseStep 1612631 = 2418947) B2418947
theorem B1088407 : Blo 1072617 1088407 := bstep (se 1 (by rfl) ⟨816305, by rfl⟩ : syracuseStep 1088407 = 1632611) B1632611
theorem B2038679 : Blo 1072617 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B1612697 : Blo 1072617 1612697 := bstep (se 2 (by rfl) ⟨604761, by rfl⟩ : syracuseStep 1612697 = 1209523) B1209523
theorem B3447755 : Blo 1072617 3447755 := bstep (se 1 (by rfl) ⟨2585816, by rfl⟩ : syracuseStep 3447755 = 5171633) B5171633
theorem B1612811 : Blo 1072617 1612811 := bstep (se 1 (by rfl) ⟨1209608, by rfl⟩ : syracuseStep 1612811 = 2419217) B2419217
theorem B1612823 : Blo 1072617 1612823 := bstep (se 1 (by rfl) ⟨1209617, by rfl⟩ : syracuseStep 1612823 = 2419235) B2419235
theorem B1612889 : Blo 1072617 1612889 := bstep (se 2 (by rfl) ⟨604833, by rfl⟩ : syracuseStep 1612889 = 1209667) B1209667
theorem B4594819 : Blo 1072617 4594819 := bstep (se 1 (by rfl) ⟨3446114, by rfl⟩ : syracuseStep 4594819 = 6892229) B6892229
theorem B37264535 : Blo 1072617 37264535 := bstep (se 1 (by rfl) ⟨27948401, by rfl⟩ : syracuseStep 37264535 = 55896803) B55896803
theorem B4136129 : Blo 1072617 4136129 := bstep (se 2 (by rfl) ⟨1551048, by rfl⟩ : syracuseStep 4136129 = 3102097) B3102097
theorem B1613003 : Blo 1072617 1613003 := bstep (se 1 (by rfl) ⟨1209752, by rfl⟩ : syracuseStep 1613003 = 2419505) B2419505
theorem B1613015 : Blo 1072617 1613015 := bstep (se 1 (by rfl) ⟨1209761, by rfl⟩ : syracuseStep 1613015 = 2419523) B2419523
theorem B1613081 : Blo 1072617 1613081 := bstep (se 2 (by rfl) ⟨604905, by rfl⟩ : syracuseStep 1613081 = 1209811) B1209811
theorem B1613195 : Blo 1072617 1613195 := bstep (se 1 (by rfl) ⟨1209896, by rfl⟩ : syracuseStep 1613195 = 2419793) B2419793
theorem B1613207 : Blo 1072617 1613207 := bstep (se 1 (by rfl) ⟨1209905, by rfl⟩ : syracuseStep 1613207 = 2419811) B2419811
theorem B1613273 : Blo 1072617 1613273 := bstep (se 2 (by rfl) ⟨604977, by rfl⟩ : syracuseStep 1613273 = 1209955) B1209955
theorem B2039347 : Blo 1072617 2039347 := bstep (se 1 (by rfl) ⟨1529510, by rfl⟩ : syracuseStep 2039347 = 3059021) B3059021
theorem B1613387 : Blo 1072617 1613387 := bstep (se 1 (by rfl) ⟨1210040, by rfl⟩ : syracuseStep 1613387 = 2420081) B2420081
theorem B1613399 : Blo 1072617 1613399 := bstep (se 1 (by rfl) ⟨1210049, by rfl⟩ : syracuseStep 1613399 = 2420099) B2420099
theorem B1810073 : Blo 1072617 1810073 := bstep (se 2 (by rfl) ⟨678777, by rfl⟩ : syracuseStep 1810073 = 1357555) B1357555
theorem B1613465 : Blo 1072617 1613465 := bstep (se 2 (by rfl) ⟨605049, by rfl⟩ : syracuseStep 1613465 = 1210099) B1210099
theorem B8724145 : Blo 1072617 8724145 := bstep (se 2 (by rfl) ⟨3271554, by rfl⟩ : syracuseStep 8724145 = 6543109) B6543109
theorem B1613579 : Blo 1072617 1613579 := bstep (se 1 (by rfl) ⟨1210184, by rfl⟩ : syracuseStep 1613579 = 2420369) B2420369
theorem B2039575 : Blo 1072617 2039575 := bstep (se 1 (by rfl) ⟨1529681, by rfl⟩ : syracuseStep 2039575 = 3059363) B3059363
theorem B1613591 : Blo 1072617 1613591 := bstep (se 1 (by rfl) ⟨1210193, by rfl⟩ : syracuseStep 1613591 = 2420387) B2420387
theorem B1810201 : Blo 1072617 1810201 := bstep (se 2 (by rfl) ⟨678825, by rfl⟩ : syracuseStep 1810201 = 1357651) B1357651
theorem B1089335 : Blo 1072617 1089335 := bstep (se 1 (by rfl) ⟨817001, by rfl⟩ : syracuseStep 1089335 = 1634003) B1634003
theorem B1613657 : Blo 1072617 1613657 := bstep (se 2 (by rfl) ⟨605121, by rfl⟩ : syracuseStep 1613657 = 1210243) B1210243
theorem B9183077 : Blo 1072617 9183077 := bstep (se 4 (by rfl) ⟨860913, by rfl⟩ : syracuseStep 9183077 = 1721827) B1721827
theorem B2039681 : Blo 1072617 2039681 := bstep (se 2 (by rfl) ⟨764880, by rfl⟩ : syracuseStep 2039681 = 1529761) B1529761
theorem B1613771 : Blo 1072617 1613771 := bstep (se 1 (by rfl) ⟨1210328, by rfl⟩ : syracuseStep 1613771 = 2420657) B2420657
theorem B1613783 : Blo 1072617 1613783 := bstep (se 1 (by rfl) ⟨1210337, by rfl⟩ : syracuseStep 1613783 = 2420675) B2420675
theorem B2039833 : Blo 1072617 2039833 := bstep (se 2 (by rfl) ⟨764937, by rfl⟩ : syracuseStep 2039833 = 1529875) B1529875
theorem B1613849 : Blo 1072617 1613849 := bstep (se 2 (by rfl) ⟨605193, by rfl⟩ : syracuseStep 1613849 = 1210387) B1210387
theorem B4595777 : Blo 1072617 4595777 := bstep (se 2 (by rfl) ⟨1723416, by rfl⟩ : syracuseStep 4595777 = 3446833) B3446833
theorem B1613963 : Blo 1072617 1613963 := bstep (se 1 (by rfl) ⟨1210472, by rfl⟩ : syracuseStep 1613963 = 2420945) B2420945
theorem B1613975 : Blo 1072617 1613975 := bstep (se 1 (by rfl) ⟨1210481, by rfl⟩ : syracuseStep 1613975 = 2420963) B2420963
theorem B1614041 : Blo 1072617 1614041 := bstep (se 2 (by rfl) ⟨605265, by rfl⟩ : syracuseStep 1614041 = 1210531) B1210531
theorem B5447897 : Blo 1072617 5447897 := bstep (se 2 (by rfl) ⟨2042961, by rfl⟩ : syracuseStep 5447897 = 4085923) B4085923
theorem B8167715 : Blo 1072617 8167715 := bstep (se 1 (by rfl) ⟨6125786, by rfl⟩ : syracuseStep 8167715 = 12251573) B12251573
theorem B1614155 : Blo 1072617 1614155 := bstep (se 1 (by rfl) ⟨1210616, by rfl⟩ : syracuseStep 1614155 = 2421233) B2421233
theorem B1810775 : Blo 1072617 1810775 := bstep (se 1 (by rfl) ⟨1358081, by rfl⟩ : syracuseStep 1810775 = 2716163) B2716163
theorem B1614167 : Blo 1072617 1614167 := bstep (se 1 (by rfl) ⟨1210625, by rfl⟩ : syracuseStep 1614167 = 2421251) B2421251
theorem B5808485 : Blo 1072617 5808485 := bstep (se 4 (by rfl) ⟨544545, by rfl⟩ : syracuseStep 5808485 = 1089091) B1089091
theorem B1614233 : Blo 1072617 1614233 := bstep (se 2 (by rfl) ⟨605337, by rfl⟩ : syracuseStep 1614233 = 1210675) B1210675
theorem B1810903 : Blo 1072617 1810903 := bstep (se 1 (by rfl) ⟨1358177, by rfl⟩ : syracuseStep 1810903 = 2716355) B2716355
theorem B1614347 : Blo 1072617 1614347 := bstep (se 1 (by rfl) ⟨1210760, by rfl⟩ : syracuseStep 1614347 = 2421521) B2421521
theorem B1614359 : Blo 1072617 1614359 := bstep (se 1 (by rfl) ⟨1210769, by rfl⟩ : syracuseStep 1614359 = 2421539) B2421539
theorem B1614425 : Blo 1072617 1614425 := bstep (se 2 (by rfl) ⟨605409, by rfl⟩ : syracuseStep 1614425 = 1210819) B1210819
theorem B1614539 : Blo 1072617 1614539 := bstep (se 1 (by rfl) ⟨1210904, by rfl⟩ : syracuseStep 1614539 = 2421809) B2421809
theorem B1614551 : Blo 1072617 1614551 := bstep (se 1 (by rfl) ⟨1210913, by rfl⟩ : syracuseStep 1614551 = 2421827) B2421827
theorem B1614617 : Blo 1072617 1614617 := bstep (se 2 (by rfl) ⟨605481, by rfl⟩ : syracuseStep 1614617 = 1210963) B1210963
theorem B1614731 : Blo 1072617 1614731 := bstep (se 1 (by rfl) ⟨1211048, by rfl⟩ : syracuseStep 1614731 = 2422097) B2422097
theorem B1614743 : Blo 1072617 1614743 := bstep (se 1 (by rfl) ⟨1211057, by rfl⟩ : syracuseStep 1614743 = 2422115) B2422115
theorem B1614809 : Blo 1072617 1614809 := bstep (se 2 (by rfl) ⟨605553, by rfl⟩ : syracuseStep 1614809 = 1211107) B1211107
theorem B3875843 : Blo 1072617 3875843 := bstep (se 1 (by rfl) ⟨2906882, by rfl⟩ : syracuseStep 3875843 = 5813765) B5813765
theorem B1811531 : Blo 1072617 1811531 := bstep (se 1 (by rfl) ⟨1358648, by rfl⟩ : syracuseStep 1811531 = 2717297) B2717297
theorem B1614923 : Blo 1072617 1614923 := bstep (se 1 (by rfl) ⟨1211192, by rfl⟩ : syracuseStep 1614923 = 2422385) B2422385
theorem B7349399 : Blo 1072617 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B1811659 : Blo 1072617 1811659 := bstep (se 1 (by rfl) ⟨1358744, by rfl⟩ : syracuseStep 1811659 = 2717489) B2717489
theorem B2041139 : Blo 1072617 2041139 := bstep (se 1 (by rfl) ⟨1530854, by rfl⟩ : syracuseStep 2041139 = 3061709) B3061709
theorem B1811801 : Blo 1072617 1811801 := bstep (se 2 (by rfl) ⟨679425, by rfl⟩ : syracuseStep 1811801 = 1358851) B1358851
theorem B3876275 : Blo 1072617 3876275 := bstep (se 1 (by rfl) ⟨2907206, by rfl⟩ : syracuseStep 3876275 = 5814413) B5814413
theorem B2041291 : Blo 1072617 2041291 := bstep (se 1 (by rfl) ⟨1530968, by rfl⟩ : syracuseStep 2041291 = 3061937) B3061937
theorem B4597195 : Blo 1072617 4597195 := bstep (se 1 (by rfl) ⟨3447896, by rfl⟩ : syracuseStep 4597195 = 6895793) B6895793
theorem B1811929 : Blo 1072617 1811929 := bstep (se 2 (by rfl) ⟨679473, by rfl⟩ : syracuseStep 1811929 = 1358947) B1358947
theorem B6530653 : Blo 1072617 6530653 := bstep (se 3 (by rfl) ⟨1224497, by rfl⟩ : syracuseStep 6530653 = 2448995) B2448995
theorem B6891101 : Blo 1072617 6891101 := bstep (se 3 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 6891101 = 2584163) B2584163
theorem B18392669 : Blo 1072617 18392669 := bstep (se 3 (by rfl) ⟨3448625, by rfl⟩ : syracuseStep 18392669 = 6897251) B6897251
theorem B4073105 : Blo 1072617 4073105 := bstep (se 2 (by rfl) ⟨1527414, by rfl⟩ : syracuseStep 4073105 = 3054829) B3054829
theorem B8726221 : Blo 1072617 8726221 := bstep (se 3 (by rfl) ⟨1636166, by rfl⟩ : syracuseStep 8726221 = 3272333) B3272333
theorem B4597469 : Blo 1072617 4597469 := bstep (se 3 (by rfl) ⟨862025, by rfl⟩ : syracuseStep 4597469 = 1724051) B1724051
theorem B12396293 : Blo 1072617 12396293 := bstep (se 4 (by rfl) ⟨1162152, by rfl⟩ : syracuseStep 12396293 = 2324305) B2324305
theorem B2041625 : Blo 1072617 2041625 := bstep (se 2 (by rfl) ⟨765609, by rfl⟩ : syracuseStep 2041625 = 1531219) B1531219
theorem B5449517 : Blo 1072617 5449517 := bstep (se 3 (by rfl) ⟨1021784, by rfl⟩ : syracuseStep 5449517 = 2043569) B2043569
theorem B1812503 : Blo 1072617 1812503 := bstep (se 1 (by rfl) ⟨1359377, by rfl⟩ : syracuseStep 1812503 = 2718755) B2718755
theorem B4073561 : Blo 1072617 4073561 := bstep (se 2 (by rfl) ⟨1527585, by rfl⟩ : syracuseStep 4073561 = 3055171) B3055171
theorem B1812631 : Blo 1072617 1812631 := bstep (se 1 (by rfl) ⟨1359473, by rfl⟩ : syracuseStep 1812631 = 2718947) B2718947
theorem B4073773 : Blo 1072617 4073773 := bstep (se 3 (by rfl) ⟨763832, by rfl⟩ : syracuseStep 4073773 = 1527665) B1527665
theorem B33499541 : Blo 1072617 33499541 := bstep (se 6 (by rfl) ⟨785145, by rfl⟩ : syracuseStep 33499541 = 1570291) B1570291
theorem B2042263 : Blo 1072617 2042263 := bstep (se 1 (by rfl) ⟨1531697, by rfl⟩ : syracuseStep 2042263 = 3063395) B3063395
theorem B3877271 : Blo 1072617 3877271 := bstep (se 1 (by rfl) ⟨2907953, by rfl⟩ : syracuseStep 3877271 = 5815907) B5815907
theorem B1681817 : Blo 1072617 1681817 := bstep (se 2 (by rfl) ⟨630681, by rfl⟩ : syracuseStep 1681817 = 1261363) B1261363
theorem B4074077 : Blo 1072617 4074077 := bstep (se 3 (by rfl) ⟨763889, by rfl⟩ : syracuseStep 4074077 = 1527779) B1527779
theorem B1813259 : Blo 1072617 1813259 := bstep (se 1 (by rfl) ⟨1359944, by rfl⟩ : syracuseStep 1813259 = 2719889) B2719889
theorem B2239307 : Blo 1072617 2239307 := bstep (se 1 (by rfl) ⟨1679480, by rfl⟩ : syracuseStep 2239307 = 3358961) B3358961
theorem B1813387 : Blo 1072617 1813387 := bstep (se 1 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 1813387 = 2720081) B2720081
theorem B1813529 : Blo 1072617 1813529 := bstep (se 2 (by rfl) ⟨680073, by rfl⟩ : syracuseStep 1813529 = 1360147) B1360147
theorem B1813657 : Blo 1072617 1813657 := bstep (se 2 (by rfl) ⟨680121, by rfl⟩ : syracuseStep 1813657 = 1360243) B1360243
theorem B2043083 : Blo 1072617 2043083 := bstep (se 1 (by rfl) ⟨1532312, by rfl⟩ : syracuseStep 2043083 = 3064625) B3064625
theorem B2043137 : Blo 1072617 2043137 := bstep (se 2 (by rfl) ⟨766176, by rfl⟩ : syracuseStep 2043137 = 1532353) B1532353
theorem B1453387 : Blo 1072617 1453387 := bstep (se 1 (by rfl) ⟨1090040, by rfl⟩ : syracuseStep 1453387 = 2180081) B2180081
theorem B3059147 : Blo 1072617 3059147 := bstep (se 1 (by rfl) ⟨2294360, by rfl⟩ : syracuseStep 3059147 = 4588721) B4588721
theorem B2174615 : Blo 1072617 2174615 := bstep (se 1 (by rfl) ⟨1630961, by rfl⟩ : syracuseStep 2174615 = 3261923) B3261923
theorem B3878551 : Blo 1072617 3878551 := bstep (se 1 (by rfl) ⟨2908913, by rfl⟩ : syracuseStep 3878551 = 5817827) B5817827
theorem B1224407 : Blo 1072617 1224407 := bstep (se 1 (by rfl) ⟨918305, by rfl⟩ : syracuseStep 1224407 = 1836611) B1836611
theorem B1814231 : Blo 1072617 1814231 := bstep (se 1 (by rfl) ⟨1360673, by rfl⟩ : syracuseStep 1814231 = 2721347) B2721347
theorem B1814359 : Blo 1072617 1814359 := bstep (se 1 (by rfl) ⟨1360769, by rfl⟩ : syracuseStep 1814359 = 2721539) B2721539
theorem B3059545 : Blo 1072617 3059545 := bstep (se 2 (by rfl) ⟨1147329, by rfl⟩ : syracuseStep 3059545 = 2294659) B2294659
theorem B1814731 : Blo 1072617 1814731 := bstep (se 1 (by rfl) ⟨1361048, by rfl⟩ : syracuseStep 1814731 = 2722097) B2722097
theorem B2175257 : Blo 1072617 2175257 := bstep (se 2 (by rfl) ⟨815721, by rfl⟩ : syracuseStep 2175257 = 1631443) B1631443
theorem B6893869 : Blo 1072617 6893869 := bstep (se 3 (by rfl) ⟨1292600, by rfl⟩ : syracuseStep 6893869 = 2585201) B2585201
theorem B7352677 : Blo 1072617 7352677 := bstep (se 4 (by rfl) ⟨689313, by rfl⟩ : syracuseStep 7352677 = 1378627) B1378627
theorem B1814987 : Blo 1072617 1814987 := bstep (se 1 (by rfl) ⟨1361240, by rfl⟩ : syracuseStep 1814987 = 2722481) B2722481
theorem B3879389 : Blo 1072617 3879389 := bstep (se 3 (by rfl) ⟨727385, by rfl⟩ : syracuseStep 3879389 = 1454771) B1454771
theorem B1815115 : Blo 1072617 1815115 := bstep (se 1 (by rfl) ⟨1361336, by rfl⟩ : syracuseStep 1815115 = 2722673) B2722673
theorem B1815257 : Blo 1072617 1815257 := bstep (se 2 (by rfl) ⟨680721, by rfl⟩ : syracuseStep 1815257 = 1361443) B1361443
theorem B1815385 : Blo 1072617 1815385 := bstep (se 2 (by rfl) ⟨680769, by rfl⟩ : syracuseStep 1815385 = 1361539) B1361539
theorem B7844701 : Blo 1072617 7844701 := bstep (se 3 (by rfl) ⟨1470881, by rfl⟩ : syracuseStep 7844701 = 2941763) B2941763
theorem B3060787 : Blo 1072617 3060787 := bstep (se 1 (by rfl) ⟨2295590, by rfl⟩ : syracuseStep 3060787 = 4591181) B4591181
theorem B4076675 : Blo 1072617 4076675 := bstep (se 1 (by rfl) ⟨3057506, by rfl⟩ : syracuseStep 4076675 = 6115013) B6115013
theorem B4076689 : Blo 1072617 4076689 := bstep (se 2 (by rfl) ⟨1528758, by rfl⟩ : syracuseStep 4076689 = 3057517) B3057517
theorem B6632779 : Blo 1072617 6632779 := bstep (se 1 (by rfl) ⟨4974584, by rfl⟩ : syracuseStep 6632779 = 9949169) B9949169
theorem B1815959 : Blo 1072617 1815959 := bstep (se 1 (by rfl) ⟨1361969, by rfl⟩ : syracuseStep 1815959 = 2723939) B2723939
theorem B4076993 : Blo 1072617 4076993 := bstep (se 2 (by rfl) ⟨1528872, by rfl⟩ : syracuseStep 4076993 = 3057745) B3057745
theorem B8173061 : Blo 1072617 8173061 := bstep (se 4 (by rfl) ⟨766224, by rfl⟩ : syracuseStep 8173061 = 1532449) B1532449
theorem B1816087 : Blo 1072617 1816087 := bstep (se 1 (by rfl) ⟨1362065, by rfl⟩ : syracuseStep 1816087 = 2724131) B2724131
theorem B4077661 : Blo 1072617 4077661 := bstep (se 3 (by rfl) ⟨764561, by rfl⟩ : syracuseStep 4077661 = 1529123) B1529123
theorem B1816715 : Blo 1072617 1816715 := bstep (se 1 (by rfl) ⟨1362536, by rfl⟩ : syracuseStep 1816715 = 2725073) B2725073
theorem B1357975 : Blo 1072617 1357975 := bstep (se 1 (by rfl) ⟨1018481, by rfl⟩ : syracuseStep 1357975 = 2036963) B2036963
theorem B39172247 : Blo 1072617 39172247 := bstep (se 1 (by rfl) ⟨29379185, by rfl⟩ : syracuseStep 39172247 = 58758371) B58758371
theorem B1194391 : Blo 1072617 1194391 := bstep (se 1 (by rfl) ⟨895793, by rfl⟩ : syracuseStep 1194391 = 1791587) B1791587
theorem B6896279 : Blo 1072617 6896279 := bstep (se 1 (by rfl) ⟨5172209, by rfl⟩ : syracuseStep 6896279 = 10344419) B10344419
theorem B1358795 : Blo 1072617 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B6110387 : Blo 1072617 6110387 := bstep (se 1 (by rfl) ⟨4582790, by rfl⟩ : syracuseStep 6110387 = 9165581) B9165581
theorem B4078937 : Blo 1072617 4078937 := bstep (se 2 (by rfl) ⟨1529601, by rfl⟩ : syracuseStep 4078937 = 3059203) B3059203
theorem B3620375 : Blo 1072617 3620375 := bstep (se 1 (by rfl) ⟨2715281, by rfl⟩ : syracuseStep 3620375 = 5430563) B5430563
theorem B5226059 : Blo 1072617 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B5160523 : Blo 1072617 5160523 := bstep (se 1 (by rfl) ⟨3870392, by rfl⟩ : syracuseStep 5160523 = 7740785) B7740785
theorem B1359499 : Blo 1072617 1359499 := bstep (se 1 (by rfl) ⟨1019624, by rfl⟩ : syracuseStep 1359499 = 2039249) B2039249
theorem B8175491 : Blo 1072617 8175491 := bstep (se 1 (by rfl) ⟨6131618, by rfl⟩ : syracuseStep 8175491 = 12263237) B12263237
theorem B1359767 : Blo 1072617 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B3063703 : Blo 1072617 3063703 := bstep (se 1 (by rfl) ⟨2297777, by rfl⟩ : syracuseStep 3063703 = 4595555) B4595555
theorem B18366425 : Blo 1072617 18366425 := bstep (se 2 (by rfl) ⟨6887409, by rfl⟩ : syracuseStep 18366425 = 13774819) B13774819
theorem B3620915 : Blo 1072617 3620915 := bstep (se 1 (by rfl) ⟨2715686, by rfl⟩ : syracuseStep 3620915 = 5431373) B5431373
theorem B3621185 : Blo 1072617 3621185 := bstep (se 2 (by rfl) ⟨1357944, by rfl⟩ : syracuseStep 3621185 = 2715889) B2715889
theorem B1360471 : Blo 1072617 1360471 := bstep (se 1 (by rfl) ⟨1020353, by rfl⟩ : syracuseStep 1360471 = 2040707) B2040707
theorem B6111845 : Blo 1072617 6111845 := bstep (se 4 (by rfl) ⟨572985, by rfl⟩ : syracuseStep 6111845 = 1145971) B1145971
theorem B6800203 : Blo 1072617 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B3621725 : Blo 1072617 3621725 := bstep (se 3 (by rfl) ⟨679073, by rfl⟩ : syracuseStep 3621725 = 1358147) B1358147
theorem B4080563 : Blo 1072617 4080563 := bstep (se 1 (by rfl) ⟨3060422, by rfl⟩ : syracuseStep 4080563 = 6120845) B6120845
theorem B4080577 : Blo 1072617 4080577 := bstep (se 2 (by rfl) ⟨1530216, by rfl⟩ : syracuseStep 4080577 = 3060433) B3060433
theorem B3490781 : Blo 1072617 3490781 := bstep (se 3 (by rfl) ⟨654521, by rfl⟩ : syracuseStep 3490781 = 1309043) B1309043
theorem B3065035 : Blo 1072617 3065035 := bstep (se 1 (by rfl) ⟨2298776, by rfl⟩ : syracuseStep 3065035 = 4597553) B4597553
theorem B6112529 : Blo 1072617 6112529 := bstep (se 2 (by rfl) ⟨2292198, by rfl⟩ : syracuseStep 6112529 = 4584397) B4584397
theorem B3065309 : Blo 1072617 3065309 := bstep (se 3 (by rfl) ⟨574745, by rfl⟩ : syracuseStep 3065309 = 1149491) B1149491
theorem B39142925 : Blo 1072617 39142925 := bstep (se 3 (by rfl) ⟨7339298, by rfl⟩ : syracuseStep 39142925 = 14678597) B14678597
theorem B13092445 : Blo 1072617 13092445 := bstep (se 3 (by rfl) ⟨2454833, by rfl⟩ : syracuseStep 13092445 = 4909667) B4909667
theorem B3065651 : Blo 1072617 3065651 := bstep (se 1 (by rfl) ⟨2299238, by rfl⟩ : syracuseStep 3065651 = 4598477) B4598477
theorem B9946955 : Blo 1072617 9946955 := bstep (se 1 (by rfl) ⟨7460216, by rfl⟩ : syracuseStep 9946955 = 14920433) B14920433
theorem B3262301 : Blo 1072617 3262301 := bstep (se 3 (by rfl) ⟨611681, by rfl⟩ : syracuseStep 3262301 = 1223363) B1223363
theorem B3622859 : Blo 1072617 3622859 := bstep (se 1 (by rfl) ⟨2717144, by rfl⟩ : syracuseStep 3622859 = 5434289) B5434289
theorem B1722379 : Blo 1072617 1722379 := bstep (se 1 (by rfl) ⟨1291784, by rfl⟩ : syracuseStep 1722379 = 2583569) B2583569
theorem B2902081 : Blo 1072617 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B3623129 : Blo 1072617 3623129 := bstep (se 2 (by rfl) ⟨1358673, by rfl⟩ : syracuseStep 3623129 = 2717347) B2717347
theorem B1722635 : Blo 1072617 1722635 := bstep (se 1 (by rfl) ⟨1291976, by rfl⟩ : syracuseStep 1722635 = 2583953) B2583953
theorem B1362187 : Blo 1072617 1362187 := bstep (se 1 (by rfl) ⟨1021640, by rfl⟩ : syracuseStep 1362187 = 2043281) B2043281
theorem B4082507 : Blo 1072617 4082507 := bstep (se 1 (by rfl) ⟨3061880, by rfl⟩ : syracuseStep 4082507 = 6123761) B6123761
theorem B4082521 : Blo 1072617 4082521 := bstep (se 2 (by rfl) ⟨1530945, by rfl⟩ : syracuseStep 4082521 = 3061891) B3061891
theorem B3623831 : Blo 1072617 3623831 := bstep (se 1 (by rfl) ⟨2717873, by rfl⟩ : syracuseStep 3623831 = 5435747) B5435747
theorem B1723339 : Blo 1072617 1723339 := bstep (se 1 (by rfl) ⟨1292504, by rfl⟩ : syracuseStep 1723339 = 2585009) B2585009
theorem B68111381 : Blo 1072617 68111381 := bstep (se 6 (by rfl) ⟨1596360, by rfl⟩ : syracuseStep 68111381 = 3192721) B3192721
theorem B4901933 : Blo 1072617 4901933 := bstep (se 3 (by rfl) ⟨919112, by rfl⟩ : syracuseStep 4901933 = 1838225) B1838225
theorem B7752779 : Blo 1072617 7752779 := bstep (se 1 (by rfl) ⟨5814584, by rfl⟩ : syracuseStep 7752779 = 11629169) B11629169
theorem B3493081 : Blo 1072617 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B1723609 : Blo 1072617 1723609 := bstep (se 2 (by rfl) ⟨646353, by rfl⟩ : syracuseStep 1723609 = 1292707) B1292707
theorem B1723673 : Blo 1072617 1723673 := bstep (se 2 (by rfl) ⟨646377, by rfl⟩ : syracuseStep 1723673 = 1292755) B1292755
theorem B3624371 : Blo 1072617 3624371 := bstep (se 1 (by rfl) ⟨2718278, by rfl⟩ : syracuseStep 3624371 = 5436557) B5436557
theorem B13749911 : Blo 1072617 13749911 := bstep (se 1 (by rfl) ⟨10312433, by rfl⟩ : syracuseStep 13749911 = 20624867) B20624867
theorem B3624641 : Blo 1072617 3624641 := bstep (se 2 (by rfl) ⟨1359240, by rfl⟩ : syracuseStep 3624641 = 2718481) B2718481
theorem B4083479 : Blo 1072617 4083479 := bstep (se 1 (by rfl) ⟨3062609, by rfl⟩ : syracuseStep 4083479 = 6125219) B6125219
theorem B2903897 : Blo 1072617 2903897 := bstep (se 2 (by rfl) ⟨1088961, by rfl⟩ : syracuseStep 2903897 = 2177923) B2177923
theorem B3625181 : Blo 1072617 3625181 := bstep (se 3 (by rfl) ⟨679721, by rfl⟩ : syracuseStep 3625181 = 1359443) B1359443
theorem B1528075 : Blo 1072617 1528075 := bstep (se 1 (by rfl) ⟨1146056, by rfl⟩ : syracuseStep 1528075 = 2292113) B2292113
theorem B5165329 : Blo 1072617 5165329 := bstep (se 2 (by rfl) ⟨1936998, by rfl⟩ : syracuseStep 5165329 = 3873997) B3873997
theorem B1528087 : Blo 1072617 1528087 := bstep (se 1 (by rfl) ⟨1146065, by rfl⟩ : syracuseStep 1528087 = 2292131) B2292131
theorem B6115763 : Blo 1072617 6115763 := bstep (se 1 (by rfl) ⟨4586822, by rfl⟩ : syracuseStep 6115763 = 9173645) B9173645
theorem B2413529 : Blo 1072617 2413529 := bstep (se 2 (by rfl) ⟨905073, by rfl⟩ : syracuseStep 2413529 = 1810147) B1810147
theorem B4084739 : Blo 1072617 4084739 := bstep (se 1 (by rfl) ⟨3063554, by rfl⟩ : syracuseStep 4084739 = 6127109) B6127109
theorem B2413619 : Blo 1072617 2413619 := bstep (se 1 (by rfl) ⟨1810214, by rfl⟩ : syracuseStep 2413619 = 3620429) B3620429
theorem B2413655 : Blo 1072617 2413655 := bstep (se 1 (by rfl) ⟨1810241, by rfl⟩ : syracuseStep 2413655 = 3620483) B3620483
theorem B5166173 : Blo 1072617 5166173 := bstep (se 3 (by rfl) ⟨968657, by rfl⟩ : syracuseStep 5166173 = 1937315) B1937315
theorem B2413835 : Blo 1072617 2413835 := bstep (se 1 (by rfl) ⟨1810376, by rfl⟩ : syracuseStep 2413835 = 3620753) B3620753
theorem B2905367 : Blo 1072617 2905367 := bstep (se 1 (by rfl) ⟨2179025, by rfl⟩ : syracuseStep 2905367 = 4358051) B4358051
theorem B2413889 : Blo 1072617 2413889 := bstep (se 2 (by rfl) ⟨905208, by rfl⟩ : syracuseStep 2413889 = 1810417) B1810417
theorem B3626315 : Blo 1072617 3626315 := bstep (se 1 (by rfl) ⟨2719736, by rfl⟩ : syracuseStep 3626315 = 5439473) B5439473
theorem B2446807 : Blo 1072617 2446807 := bstep (se 1 (by rfl) ⟨1835105, by rfl⟩ : syracuseStep 2446807 = 3670211) B3670211
theorem B2414105 : Blo 1072617 2414105 := bstep (se 2 (by rfl) ⟨905289, by rfl⟩ : syracuseStep 2414105 = 1810579) B1810579
theorem B3626585 : Blo 1072617 3626585 := bstep (se 2 (by rfl) ⟨1359969, by rfl⟩ : syracuseStep 3626585 = 2719939) B2719939
theorem B2414195 : Blo 1072617 2414195 := bstep (se 1 (by rfl) ⟨1810646, by rfl⟩ : syracuseStep 2414195 = 3621293) B3621293
theorem B2479745 : Blo 1072617 2479745 := bstep (se 2 (by rfl) ⟨929904, by rfl⟩ : syracuseStep 2479745 = 1859809) B1859809
theorem B2414231 : Blo 1072617 2414231 := bstep (se 1 (by rfl) ⟨1810673, by rfl⟩ : syracuseStep 2414231 = 3621347) B3621347
theorem B3102401 : Blo 1072617 3102401 := bstep (se 2 (by rfl) ⟨1163400, by rfl⟩ : syracuseStep 3102401 = 2326801) B2326801
theorem B4904707 : Blo 1072617 4904707 := bstep (se 1 (by rfl) ⟨3678530, by rfl⟩ : syracuseStep 4904707 = 7357061) B7357061
theorem B2414411 : Blo 1072617 2414411 := bstep (se 1 (by rfl) ⟨1810808, by rfl⟩ : syracuseStep 2414411 = 3621617) B3621617
theorem B2905931 : Blo 1072617 2905931 := bstep (se 1 (by rfl) ⟨2179448, by rfl⟩ : syracuseStep 2905931 = 4358897) B4358897
theorem B6117221 : Blo 1072617 6117221 := bstep (se 4 (by rfl) ⟨573489, by rfl⟩ : syracuseStep 6117221 = 1146979) B1146979
theorem B2414465 : Blo 1072617 2414465 := bstep (se 2 (by rfl) ⟨905424, by rfl⟩ : syracuseStep 2414465 = 1810849) B1810849
theorem B2414681 : Blo 1072617 2414681 := bstep (se 2 (by rfl) ⟨905505, by rfl⟩ : syracuseStep 2414681 = 1811011) B1811011
theorem B2414771 : Blo 1072617 2414771 := bstep (se 1 (by rfl) ⟨1811078, by rfl⟩ : syracuseStep 2414771 = 3622157) B3622157
theorem B2414807 : Blo 1072617 2414807 := bstep (se 1 (by rfl) ⟨1811105, by rfl⟩ : syracuseStep 2414807 = 3622211) B3622211
theorem B3627287 : Blo 1072617 3627287 := bstep (se 1 (by rfl) ⟨2720465, by rfl⟩ : syracuseStep 3627287 = 5440931) B5440931
theorem B1530137 : Blo 1072617 1530137 := bstep (se 2 (by rfl) ⟨573801, by rfl⟩ : syracuseStep 1530137 = 1147603) B1147603
theorem B6117677 : Blo 1072617 6117677 := bstep (se 3 (by rfl) ⟨1147064, by rfl⟩ : syracuseStep 6117677 = 2294129) B2294129
theorem B2414987 : Blo 1072617 2414987 := bstep (se 1 (by rfl) ⟨1811240, by rfl⟩ : syracuseStep 2414987 = 3622481) B3622481
theorem B2415041 : Blo 1072617 2415041 := bstep (se 2 (by rfl) ⟨905640, by rfl⟩ : syracuseStep 2415041 = 1811281) B1811281
theorem B2415257 : Blo 1072617 2415257 := bstep (se 2 (by rfl) ⟨905721, by rfl⟩ : syracuseStep 2415257 = 1811443) B1811443
theorem B2415347 : Blo 1072617 2415347 := bstep (se 1 (by rfl) ⟨1811510, by rfl⟩ : syracuseStep 2415347 = 3623021) B3623021
theorem B2415383 : Blo 1072617 2415383 := bstep (se 1 (by rfl) ⟨1811537, by rfl⟩ : syracuseStep 2415383 = 3623075) B3623075
theorem B3627827 : Blo 1072617 3627827 := bstep (se 1 (by rfl) ⟨2720870, by rfl⟩ : syracuseStep 3627827 = 5441741) B5441741
theorem B1530775 : Blo 1072617 1530775 := bstep (se 1 (by rfl) ⟨1148081, by rfl⟩ : syracuseStep 1530775 = 2296163) B2296163
theorem B2415563 : Blo 1072617 2415563 := bstep (se 1 (by rfl) ⟨1811672, by rfl⟩ : syracuseStep 2415563 = 3623345) B3623345
theorem B6118361 : Blo 1072617 6118361 := bstep (se 2 (by rfl) ⟨2294385, by rfl⟩ : syracuseStep 6118361 = 4588771) B4588771
theorem B2415617 : Blo 1072617 2415617 := bstep (se 2 (by rfl) ⟨905856, by rfl⟩ : syracuseStep 2415617 = 1811713) B1811713
theorem B3628097 : Blo 1072617 3628097 := bstep (se 2 (by rfl) ⟨1360536, by rfl⟩ : syracuseStep 3628097 = 2721073) B2721073
theorem B2415833 : Blo 1072617 2415833 := bstep (se 2 (by rfl) ⟨905937, by rfl⟩ : syracuseStep 2415833 = 1811875) B1811875
theorem B2415923 : Blo 1072617 2415923 := bstep (se 1 (by rfl) ⟨1811942, by rfl⟩ : syracuseStep 2415923 = 3623885) B3623885
theorem B2415959 : Blo 1072617 2415959 := bstep (se 1 (by rfl) ⟨1811969, by rfl⟩ : syracuseStep 2415959 = 3623939) B3623939
theorem B4906457 : Blo 1072617 4906457 := bstep (se 2 (by rfl) ⟨1839921, by rfl⟩ : syracuseStep 4906457 = 3679843) B3679843
theorem B1072619 : Blo 1072617 1072619 := bstep (se 1 (by rfl) ⟨804464, by rfl⟩ : syracuseStep 1072619 = 1608929) B1608929
theorem B1072631 : Blo 1072617 1072631 := bstep (se 1 (by rfl) ⟨804473, by rfl⟩ : syracuseStep 1072631 = 1608947) B1608947
theorem B1072651 : Blo 1072617 1072651 := bstep (se 1 (by rfl) ⟨804488, by rfl⟩ : syracuseStep 1072651 = 1608977) B1608977
theorem B2416139 : Blo 1072617 2416139 := bstep (se 1 (by rfl) ⟨1812104, by rfl⟩ : syracuseStep 2416139 = 3624209) B3624209
theorem B1072663 : Blo 1072617 1072663 := bstep (se 1 (by rfl) ⟨804497, by rfl⟩ : syracuseStep 1072663 = 1608995) B1608995
theorem B1072683 : Blo 1072617 1072683 := bstep (se 1 (by rfl) ⟨804512, by rfl⟩ : syracuseStep 1072683 = 1609025) B1609025
theorem B1072695 : Blo 1072617 1072695 := bstep (se 1 (by rfl) ⟨804521, by rfl⟩ : syracuseStep 1072695 = 1609043) B1609043
theorem B2416193 : Blo 1072617 2416193 := bstep (se 2 (by rfl) ⟨906072, by rfl⟩ : syracuseStep 2416193 = 1812145) B1812145
theorem B1072715 : Blo 1072617 1072715 := bstep (se 1 (by rfl) ⟨804536, by rfl⟩ : syracuseStep 1072715 = 1609073) B1609073
theorem B1072727 : Blo 1072617 1072727 := bstep (se 1 (by rfl) ⟨804545, by rfl⟩ : syracuseStep 1072727 = 1609091) B1609091
theorem B3628637 : Blo 1072617 3628637 := bstep (se 3 (by rfl) ⟨680369, by rfl⟩ : syracuseStep 3628637 = 1360739) B1360739
theorem B1072747 : Blo 1072617 1072747 := bstep (se 1 (by rfl) ⟨804560, by rfl⟩ : syracuseStep 1072747 = 1609121) B1609121
theorem B1072759 : Blo 1072617 1072759 := bstep (se 1 (by rfl) ⟨804569, by rfl⟩ : syracuseStep 1072759 = 1609139) B1609139
theorem B5168771 : Blo 1072617 5168771 := bstep (se 1 (by rfl) ⟨3876578, by rfl⟩ : syracuseStep 5168771 = 7753157) B7753157
theorem B1072779 : Blo 1072617 1072779 := bstep (se 1 (by rfl) ⟨804584, by rfl⟩ : syracuseStep 1072779 = 1609169) B1609169
theorem B1072791 : Blo 1072617 1072791 := bstep (se 1 (by rfl) ⟨804593, by rfl⟩ : syracuseStep 1072791 = 1609187) B1609187
theorem B1072811 : Blo 1072617 1072811 := bstep (se 1 (by rfl) ⟨804608, by rfl⟩ : syracuseStep 1072811 = 1609217) B1609217
theorem B8150705 : Blo 1072617 8150705 := bstep (se 2 (by rfl) ⟨3056514, by rfl⟩ : syracuseStep 8150705 = 6113029) B6113029
theorem B1072823 : Blo 1072617 1072823 := bstep (se 1 (by rfl) ⟨804617, by rfl⟩ : syracuseStep 1072823 = 1609235) B1609235
theorem B1072843 : Blo 1072617 1072843 := bstep (se 1 (by rfl) ⟨804632, by rfl⟩ : syracuseStep 1072843 = 1609265) B1609265
theorem B1531595 : Blo 1072617 1531595 := bstep (se 1 (by rfl) ⟨1148696, by rfl⟩ : syracuseStep 1531595 = 2297393) B2297393
theorem B1072855 : Blo 1072617 1072855 := bstep (se 1 (by rfl) ⟨804641, by rfl⟩ : syracuseStep 1072855 = 1609283) B1609283
theorem B1072875 : Blo 1072617 1072875 := bstep (se 1 (by rfl) ⟨804656, by rfl⟩ : syracuseStep 1072875 = 1609313) B1609313
theorem B1072887 : Blo 1072617 1072887 := bstep (se 1 (by rfl) ⟨804665, by rfl⟩ : syracuseStep 1072887 = 1609331) B1609331
theorem B1072907 : Blo 1072617 1072907 := bstep (se 1 (by rfl) ⟨804680, by rfl⟩ : syracuseStep 1072907 = 1609361) B1609361
theorem B1072919 : Blo 1072617 1072919 := bstep (se 1 (by rfl) ⟨804689, by rfl⟩ : syracuseStep 1072919 = 1609379) B1609379
theorem B2416409 : Blo 1072617 2416409 := bstep (se 2 (by rfl) ⟨906153, by rfl⟩ : syracuseStep 2416409 = 1812307) B1812307
theorem B1072939 : Blo 1072617 1072939 := bstep (se 1 (by rfl) ⟨804704, by rfl⟩ : syracuseStep 1072939 = 1609409) B1609409
theorem B4349747 : Blo 1072617 4349747 := bstep (se 1 (by rfl) ⟨3262310, by rfl⟩ : syracuseStep 4349747 = 6524621) B6524621
theorem B1072951 : Blo 1072617 1072951 := bstep (se 1 (by rfl) ⟨804713, by rfl⟩ : syracuseStep 1072951 = 1609427) B1609427
theorem B1072971 : Blo 1072617 1072971 := bstep (se 1 (by rfl) ⟨804728, by rfl⟩ : syracuseStep 1072971 = 1609457) B1609457
theorem B1072983 : Blo 1072617 1072983 := bstep (se 1 (by rfl) ⟨804737, by rfl⟩ : syracuseStep 1072983 = 1609475) B1609475
theorem B157015907 : Blo 1072617 157015907 := bstep (se 1 (by rfl) ⟨117761930, by rfl⟩ : syracuseStep 157015907 = 235523861) B235523861
theorem B1073003 : Blo 1072617 1073003 := bstep (se 1 (by rfl) ⟨804752, by rfl⟩ : syracuseStep 1073003 = 1609505) B1609505
theorem B2416499 : Blo 1072617 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B1073015 : Blo 1072617 1073015 := bstep (se 1 (by rfl) ⟨804761, by rfl⟩ : syracuseStep 1073015 = 1609523) B1609523
theorem B1073035 : Blo 1072617 1073035 := bstep (se 1 (by rfl) ⟨804776, by rfl⟩ : syracuseStep 1073035 = 1609553) B1609553
theorem B1073047 : Blo 1072617 1073047 := bstep (se 1 (by rfl) ⟨804785, by rfl⟩ : syracuseStep 1073047 = 1609571) B1609571
theorem B2416535 : Blo 1072617 2416535 := bstep (se 1 (by rfl) ⟨1812401, by rfl⟩ : syracuseStep 2416535 = 3624803) B3624803
theorem B1073067 : Blo 1072617 1073067 := bstep (se 1 (by rfl) ⟨804800, by rfl⟩ : syracuseStep 1073067 = 1609601) B1609601
theorem B1073079 : Blo 1072617 1073079 := bstep (se 1 (by rfl) ⟨804809, by rfl⟩ : syracuseStep 1073079 = 1609619) B1609619
theorem B1073099 : Blo 1072617 1073099 := bstep (se 1 (by rfl) ⟨804824, by rfl⟩ : syracuseStep 1073099 = 1609649) B1609649
theorem B1073111 : Blo 1072617 1073111 := bstep (se 1 (by rfl) ⟨804833, by rfl⟩ : syracuseStep 1073111 = 1609667) B1609667
theorem B8708057 : Blo 1072617 8708057 := bstep (se 2 (by rfl) ⟨3265521, by rfl⟩ : syracuseStep 8708057 = 6531043) B6531043
theorem B17457113 : Blo 1072617 17457113 := bstep (se 2 (by rfl) ⟨6546417, by rfl⟩ : syracuseStep 17457113 = 13092835) B13092835
theorem B1073131 : Blo 1072617 1073131 := bstep (se 1 (by rfl) ⟨804848, by rfl⟩ : syracuseStep 1073131 = 1609697) B1609697
theorem B1073143 : Blo 1072617 1073143 := bstep (se 1 (by rfl) ⟨804857, by rfl⟩ : syracuseStep 1073143 = 1609715) B1609715
theorem B1073163 : Blo 1072617 1073163 := bstep (se 1 (by rfl) ⟨804872, by rfl⟩ : syracuseStep 1073163 = 1609745) B1609745
theorem B1073175 : Blo 1072617 1073175 := bstep (se 1 (by rfl) ⟨804881, by rfl⟩ : syracuseStep 1073175 = 1609763) B1609763
theorem B1073195 : Blo 1072617 1073195 := bstep (se 1 (by rfl) ⟨804896, by rfl⟩ : syracuseStep 1073195 = 1609793) B1609793
theorem B1073207 : Blo 1072617 1073207 := bstep (se 1 (by rfl) ⟨804905, by rfl⟩ : syracuseStep 1073207 = 1609811) B1609811
theorem B1073227 : Blo 1072617 1073227 := bstep (se 1 (by rfl) ⟨804920, by rfl⟩ : syracuseStep 1073227 = 1609841) B1609841
theorem B2416715 : Blo 1072617 2416715 := bstep (se 1 (by rfl) ⟨1812536, by rfl⟩ : syracuseStep 2416715 = 3625073) B3625073
theorem B1073239 : Blo 1072617 1073239 := bstep (se 1 (by rfl) ⟨804929, by rfl⟩ : syracuseStep 1073239 = 1609859) B1609859
theorem B1073259 : Blo 1072617 1073259 := bstep (se 1 (by rfl) ⟨804944, by rfl⟩ : syracuseStep 1073259 = 1609889) B1609889
theorem B1073271 : Blo 1072617 1073271 := bstep (se 1 (by rfl) ⟨804953, by rfl⟩ : syracuseStep 1073271 = 1609907) B1609907
theorem B2416769 : Blo 1072617 2416769 := bstep (se 2 (by rfl) ⟨906288, by rfl⟩ : syracuseStep 2416769 = 1812577) B1812577
theorem B1073291 : Blo 1072617 1073291 := bstep (se 1 (by rfl) ⟨804968, by rfl⟩ : syracuseStep 1073291 = 1609937) B1609937
theorem B1073303 : Blo 1072617 1073303 := bstep (se 1 (by rfl) ⟨804977, by rfl⟩ : syracuseStep 1073303 = 1609955) B1609955
theorem B8151191 : Blo 1072617 8151191 := bstep (se 1 (by rfl) ⟨6113393, by rfl⟩ : syracuseStep 8151191 = 12226787) B12226787
theorem B1073323 : Blo 1072617 1073323 := bstep (se 1 (by rfl) ⟨804992, by rfl⟩ : syracuseStep 1073323 = 1609985) B1609985
theorem B4350125 : Blo 1072617 4350125 := bstep (se 3 (by rfl) ⟨815648, by rfl⟩ : syracuseStep 4350125 = 1631297) B1631297
theorem B1073335 : Blo 1072617 1073335 := bstep (se 1 (by rfl) ⟨805001, by rfl⟩ : syracuseStep 1073335 = 1610003) B1610003
theorem B1073355 : Blo 1072617 1073355 := bstep (se 1 (by rfl) ⟨805016, by rfl⟩ : syracuseStep 1073355 = 1610033) B1610033
theorem B1073367 : Blo 1072617 1073367 := bstep (se 1 (by rfl) ⟨805025, by rfl⟩ : syracuseStep 1073367 = 1610051) B1610051
theorem B1073387 : Blo 1072617 1073387 := bstep (se 1 (by rfl) ⟨805040, by rfl⟩ : syracuseStep 1073387 = 1610081) B1610081
theorem B1073399 : Blo 1072617 1073399 := bstep (se 1 (by rfl) ⟨805049, by rfl⟩ : syracuseStep 1073399 = 1610099) B1610099
theorem B1073419 : Blo 1072617 1073419 := bstep (se 1 (by rfl) ⟨805064, by rfl⟩ : syracuseStep 1073419 = 1610129) B1610129
theorem B1073431 : Blo 1072617 1073431 := bstep (se 1 (by rfl) ⟨805073, by rfl⟩ : syracuseStep 1073431 = 1610147) B1610147
theorem B1073451 : Blo 1072617 1073451 := bstep (se 1 (by rfl) ⟨805088, by rfl⟩ : syracuseStep 1073451 = 1610177) B1610177
theorem B1073463 : Blo 1072617 1073463 := bstep (se 1 (by rfl) ⟨805097, by rfl⟩ : syracuseStep 1073463 = 1610195) B1610195
theorem B1073483 : Blo 1072617 1073483 := bstep (se 1 (by rfl) ⟨805112, by rfl⟩ : syracuseStep 1073483 = 1610225) B1610225
theorem B1073495 : Blo 1072617 1073495 := bstep (se 1 (by rfl) ⟨805121, by rfl⟩ : syracuseStep 1073495 = 1610243) B1610243
theorem B2416985 : Blo 1072617 2416985 := bstep (se 2 (by rfl) ⟨906369, by rfl⟩ : syracuseStep 2416985 = 1812739) B1812739
theorem B1073515 : Blo 1072617 1073515 := bstep (se 1 (by rfl) ⟨805136, by rfl⟩ : syracuseStep 1073515 = 1610273) B1610273
theorem B1073527 : Blo 1072617 1073527 := bstep (se 1 (by rfl) ⟨805145, by rfl⟩ : syracuseStep 1073527 = 1610291) B1610291
theorem B1073547 : Blo 1072617 1073547 := bstep (se 1 (by rfl) ⟨805160, by rfl⟩ : syracuseStep 1073547 = 1610321) B1610321
theorem B1073559 : Blo 1072617 1073559 := bstep (se 1 (by rfl) ⟨805169, by rfl⟩ : syracuseStep 1073559 = 1610339) B1610339
theorem B1073579 : Blo 1072617 1073579 := bstep (se 1 (by rfl) ⟨805184, by rfl⟩ : syracuseStep 1073579 = 1610369) B1610369
theorem B2417075 : Blo 1072617 2417075 := bstep (se 1 (by rfl) ⟨1812806, by rfl⟩ : syracuseStep 2417075 = 3625613) B3625613
theorem B1073591 : Blo 1072617 1073591 := bstep (se 1 (by rfl) ⟨805193, by rfl⟩ : syracuseStep 1073591 = 1610387) B1610387
theorem B1073611 : Blo 1072617 1073611 := bstep (se 1 (by rfl) ⟨805208, by rfl⟩ : syracuseStep 1073611 = 1610417) B1610417
theorem B1073623 : Blo 1072617 1073623 := bstep (se 1 (by rfl) ⟨805217, by rfl⟩ : syracuseStep 1073623 = 1610435) B1610435
theorem B2417111 : Blo 1072617 2417111 := bstep (se 1 (by rfl) ⟨1812833, by rfl⟩ : syracuseStep 2417111 = 3625667) B3625667
theorem B1073643 : Blo 1072617 1073643 := bstep (se 1 (by rfl) ⟨805232, by rfl⟩ : syracuseStep 1073643 = 1610465) B1610465
theorem B1073655 : Blo 1072617 1073655 := bstep (se 1 (by rfl) ⟨805241, by rfl⟩ : syracuseStep 1073655 = 1610483) B1610483
theorem B1073675 : Blo 1072617 1073675 := bstep (se 1 (by rfl) ⟨805256, by rfl⟩ : syracuseStep 1073675 = 1610513) B1610513
theorem B1073687 : Blo 1072617 1073687 := bstep (se 1 (by rfl) ⟨805265, by rfl⟩ : syracuseStep 1073687 = 1610531) B1610531
theorem B1073707 : Blo 1072617 1073707 := bstep (se 1 (by rfl) ⟨805280, by rfl⟩ : syracuseStep 1073707 = 1610561) B1610561
theorem B1073719 : Blo 1072617 1073719 := bstep (se 1 (by rfl) ⟨805289, by rfl⟩ : syracuseStep 1073719 = 1610579) B1610579
theorem B1073739 : Blo 1072617 1073739 := bstep (se 1 (by rfl) ⟨805304, by rfl⟩ : syracuseStep 1073739 = 1610609) B1610609
theorem B1073751 : Blo 1072617 1073751 := bstep (se 1 (by rfl) ⟨805313, by rfl⟩ : syracuseStep 1073751 = 1610627) B1610627
theorem B1073771 : Blo 1072617 1073771 := bstep (se 1 (by rfl) ⟨805328, by rfl⟩ : syracuseStep 1073771 = 1610657) B1610657
theorem B1073783 : Blo 1072617 1073783 := bstep (se 1 (by rfl) ⟨805337, by rfl⟩ : syracuseStep 1073783 = 1610675) B1610675
theorem B1073803 : Blo 1072617 1073803 := bstep (se 1 (by rfl) ⟨805352, by rfl⟩ : syracuseStep 1073803 = 1610705) B1610705
theorem B2417291 : Blo 1072617 2417291 := bstep (se 1 (by rfl) ⟨1812968, by rfl⟩ : syracuseStep 2417291 = 3625937) B3625937
theorem B1073815 : Blo 1072617 1073815 := bstep (se 1 (by rfl) ⟨805361, by rfl⟩ : syracuseStep 1073815 = 1610723) B1610723
theorem B1073835 : Blo 1072617 1073835 := bstep (se 1 (by rfl) ⟨805376, by rfl⟩ : syracuseStep 1073835 = 1610753) B1610753
theorem B1073847 : Blo 1072617 1073847 := bstep (se 1 (by rfl) ⟨805385, by rfl⟩ : syracuseStep 1073847 = 1610771) B1610771
theorem B2417345 : Blo 1072617 2417345 := bstep (se 2 (by rfl) ⟨906504, by rfl⟩ : syracuseStep 2417345 = 1813009) B1813009
theorem B1073867 : Blo 1072617 1073867 := bstep (se 1 (by rfl) ⟨805400, by rfl⟩ : syracuseStep 1073867 = 1610801) B1610801
theorem B3629771 : Blo 1072617 3629771 := bstep (se 1 (by rfl) ⟨2722328, by rfl⟩ : syracuseStep 3629771 = 5444657) B5444657
theorem B1073879 : Blo 1072617 1073879 := bstep (se 1 (by rfl) ⟨805409, by rfl⟩ : syracuseStep 1073879 = 1610819) B1610819
theorem B1073899 : Blo 1072617 1073899 := bstep (se 1 (by rfl) ⟨805424, by rfl⟩ : syracuseStep 1073899 = 1610849) B1610849
theorem B1073911 : Blo 1072617 1073911 := bstep (se 1 (by rfl) ⟨805433, by rfl⟩ : syracuseStep 1073911 = 1610867) B1610867
theorem B1073931 : Blo 1072617 1073931 := bstep (se 1 (by rfl) ⟨805448, by rfl⟩ : syracuseStep 1073931 = 1610897) B1610897
theorem B1073943 : Blo 1072617 1073943 := bstep (se 1 (by rfl) ⟨805457, by rfl⟩ : syracuseStep 1073943 = 1610915) B1610915
theorem B1073963 : Blo 1072617 1073963 := bstep (se 1 (by rfl) ⟨805472, by rfl⟩ : syracuseStep 1073963 = 1610945) B1610945
theorem B18834221 : Blo 1072617 18834221 := bstep (se 3 (by rfl) ⟨3531416, by rfl⟩ : syracuseStep 18834221 = 7062833) B7062833
theorem B1073975 : Blo 1072617 1073975 := bstep (se 1 (by rfl) ⟨805481, by rfl⟩ : syracuseStep 1073975 = 1610963) B1610963
theorem B1073995 : Blo 1072617 1073995 := bstep (se 1 (by rfl) ⟨805496, by rfl⟩ : syracuseStep 1073995 = 1610993) B1610993
theorem B1074007 : Blo 1072617 1074007 := bstep (se 1 (by rfl) ⟨805505, by rfl⟩ : syracuseStep 1074007 = 1611011) B1611011
theorem B1074027 : Blo 1072617 1074027 := bstep (se 1 (by rfl) ⟨805520, by rfl⟩ : syracuseStep 1074027 = 1611041) B1611041
theorem B1074039 : Blo 1072617 1074039 := bstep (se 1 (by rfl) ⟨805529, by rfl⟩ : syracuseStep 1074039 = 1611059) B1611059
theorem B1074059 : Blo 1072617 1074059 := bstep (se 1 (by rfl) ⟨805544, by rfl⟩ : syracuseStep 1074059 = 1611089) B1611089
theorem B1074071 : Blo 1072617 1074071 := bstep (se 1 (by rfl) ⟨805553, by rfl⟩ : syracuseStep 1074071 = 1611107) B1611107
theorem B2417561 : Blo 1072617 2417561 := bstep (se 2 (by rfl) ⟨906585, by rfl⟩ : syracuseStep 2417561 = 1813171) B1813171
theorem B1074091 : Blo 1072617 1074091 := bstep (se 1 (by rfl) ⟨805568, by rfl⟩ : syracuseStep 1074091 = 1611137) B1611137
theorem B1074103 : Blo 1072617 1074103 := bstep (se 1 (by rfl) ⟨805577, by rfl⟩ : syracuseStep 1074103 = 1611155) B1611155
theorem B1074123 : Blo 1072617 1074123 := bstep (se 1 (by rfl) ⟨805592, by rfl⟩ : syracuseStep 1074123 = 1611185) B1611185
theorem B1074135 : Blo 1072617 1074135 := bstep (se 1 (by rfl) ⟨805601, by rfl⟩ : syracuseStep 1074135 = 1611203) B1611203
theorem B3630041 : Blo 1072617 3630041 := bstep (se 2 (by rfl) ⟨1361265, by rfl⟩ : syracuseStep 3630041 = 2722531) B2722531
theorem B1074155 : Blo 1072617 1074155 := bstep (se 1 (by rfl) ⟨805616, by rfl⟩ : syracuseStep 1074155 = 1611233) B1611233
theorem B2417651 : Blo 1072617 2417651 := bstep (se 1 (by rfl) ⟨1813238, by rfl⟩ : syracuseStep 2417651 = 3626477) B3626477
theorem B1074167 : Blo 1072617 1074167 := bstep (se 1 (by rfl) ⟨805625, by rfl⟩ : syracuseStep 1074167 = 1611251) B1611251
theorem B1074187 : Blo 1072617 1074187 := bstep (se 1 (by rfl) ⟨805640, by rfl⟩ : syracuseStep 1074187 = 1611281) B1611281
theorem B1074199 : Blo 1072617 1074199 := bstep (se 1 (by rfl) ⟨805649, by rfl⟩ : syracuseStep 1074199 = 1611299) B1611299
theorem B2417687 : Blo 1072617 2417687 := bstep (se 1 (by rfl) ⟨1813265, by rfl⟩ : syracuseStep 2417687 = 3626531) B3626531
theorem B1074219 : Blo 1072617 1074219 := bstep (se 1 (by rfl) ⟨805664, by rfl⟩ : syracuseStep 1074219 = 1611329) B1611329
theorem B1074231 : Blo 1072617 1074231 := bstep (se 1 (by rfl) ⟨805673, by rfl⟩ : syracuseStep 1074231 = 1611347) B1611347
theorem B1074251 : Blo 1072617 1074251 := bstep (se 1 (by rfl) ⟨805688, by rfl⟩ : syracuseStep 1074251 = 1611377) B1611377
theorem B1074263 : Blo 1072617 1074263 := bstep (se 1 (by rfl) ⟨805697, by rfl⟩ : syracuseStep 1074263 = 1611395) B1611395
theorem B1074283 : Blo 1072617 1074283 := bstep (se 1 (by rfl) ⟨805712, by rfl⟩ : syracuseStep 1074283 = 1611425) B1611425
theorem B1074295 : Blo 1072617 1074295 := bstep (se 1 (by rfl) ⟨805721, by rfl⟩ : syracuseStep 1074295 = 1611443) B1611443
theorem B1074315 : Blo 1072617 1074315 := bstep (se 1 (by rfl) ⟨805736, by rfl⟩ : syracuseStep 1074315 = 1611473) B1611473
theorem B1074327 : Blo 1072617 1074327 := bstep (se 1 (by rfl) ⟨805745, by rfl⟩ : syracuseStep 1074327 = 1611491) B1611491
theorem B1074347 : Blo 1072617 1074347 := bstep (se 1 (by rfl) ⟨805760, by rfl⟩ : syracuseStep 1074347 = 1611521) B1611521
theorem B1074359 : Blo 1072617 1074359 := bstep (se 1 (by rfl) ⟨805769, by rfl⟩ : syracuseStep 1074359 = 1611539) B1611539
theorem B1074379 : Blo 1072617 1074379 := bstep (se 1 (by rfl) ⟨805784, by rfl⟩ : syracuseStep 1074379 = 1611569) B1611569
theorem B2417867 : Blo 1072617 2417867 := bstep (se 1 (by rfl) ⟨1813400, by rfl⟩ : syracuseStep 2417867 = 3626801) B3626801
theorem B1074391 : Blo 1072617 1074391 := bstep (se 1 (by rfl) ⟨805793, by rfl⟩ : syracuseStep 1074391 = 1611587) B1611587
theorem B1074411 : Blo 1072617 1074411 := bstep (se 1 (by rfl) ⟨805808, by rfl⟩ : syracuseStep 1074411 = 1611617) B1611617
theorem B1074423 : Blo 1072617 1074423 := bstep (se 1 (by rfl) ⟨805817, by rfl⟩ : syracuseStep 1074423 = 1611635) B1611635
theorem B2417921 : Blo 1072617 2417921 := bstep (se 2 (by rfl) ⟨906720, by rfl⟩ : syracuseStep 2417921 = 1813441) B1813441
theorem B1074443 : Blo 1072617 1074443 := bstep (se 1 (by rfl) ⟨805832, by rfl⟩ : syracuseStep 1074443 = 1611665) B1611665
theorem B1074455 : Blo 1072617 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B1074475 : Blo 1072617 1074475 := bstep (se 1 (by rfl) ⟨805856, by rfl⟩ : syracuseStep 1074475 = 1611713) B1611713
theorem B1074487 : Blo 1072617 1074487 := bstep (se 1 (by rfl) ⟨805865, by rfl⟩ : syracuseStep 1074487 = 1611731) B1611731
theorem B1074507 : Blo 1072617 1074507 := bstep (se 1 (by rfl) ⟨805880, by rfl⟩ : syracuseStep 1074507 = 1611761) B1611761
theorem B1074519 : Blo 1072617 1074519 := bstep (se 1 (by rfl) ⟨805889, by rfl⟩ : syracuseStep 1074519 = 1611779) B1611779
theorem B5432669 : Blo 1072617 5432669 := bstep (se 3 (by rfl) ⟨1018625, by rfl⟩ : syracuseStep 5432669 = 2037251) B2037251
theorem B1074539 : Blo 1072617 1074539 := bstep (se 1 (by rfl) ⟨805904, by rfl⟩ : syracuseStep 1074539 = 1611809) B1611809
theorem B1074551 : Blo 1072617 1074551 := bstep (se 1 (by rfl) ⟨805913, by rfl⟩ : syracuseStep 1074551 = 1611827) B1611827
theorem B1074571 : Blo 1072617 1074571 := bstep (se 1 (by rfl) ⟨805928, by rfl⟩ : syracuseStep 1074571 = 1611857) B1611857
theorem B1074583 : Blo 1072617 1074583 := bstep (se 1 (by rfl) ⟨805937, by rfl⟩ : syracuseStep 1074583 = 1611875) B1611875
theorem B1074603 : Blo 1072617 1074603 := bstep (se 1 (by rfl) ⟨805952, by rfl⟩ : syracuseStep 1074603 = 1611905) B1611905
theorem B11036081 : Blo 1072617 11036081 := bstep (se 2 (by rfl) ⟨4138530, by rfl⟩ : syracuseStep 11036081 = 8277061) B8277061
theorem B1074615 : Blo 1072617 1074615 := bstep (se 1 (by rfl) ⟨805961, by rfl⟩ : syracuseStep 1074615 = 1611923) B1611923
theorem B1074635 : Blo 1072617 1074635 := bstep (se 1 (by rfl) ⟨805976, by rfl⟩ : syracuseStep 1074635 = 1611953) B1611953
theorem B1074647 : Blo 1072617 1074647 := bstep (se 1 (by rfl) ⟨805985, by rfl⟩ : syracuseStep 1074647 = 1611971) B1611971
theorem B2614745 : Blo 1072617 2614745 := bstep (se 2 (by rfl) ⟨980529, by rfl⟩ : syracuseStep 2614745 = 1961059) B1961059
theorem B2418137 : Blo 1072617 2418137 := bstep (se 2 (by rfl) ⟨906801, by rfl⟩ : syracuseStep 2418137 = 1813603) B1813603
theorem B1074667 : Blo 1072617 1074667 := bstep (se 1 (by rfl) ⟨806000, by rfl⟩ : syracuseStep 1074667 = 1612001) B1612001
theorem B1074679 : Blo 1072617 1074679 := bstep (se 1 (by rfl) ⟨806009, by rfl⟩ : syracuseStep 1074679 = 1612019) B1612019
theorem B1074699 : Blo 1072617 1074699 := bstep (se 1 (by rfl) ⟨806024, by rfl⟩ : syracuseStep 1074699 = 1612049) B1612049
theorem B1074711 : Blo 1072617 1074711 := bstep (se 1 (by rfl) ⟨806033, by rfl⟩ : syracuseStep 1074711 = 1612067) B1612067
theorem B1074731 : Blo 1072617 1074731 := bstep (se 1 (by rfl) ⟨806048, by rfl⟩ : syracuseStep 1074731 = 1612097) B1612097
theorem B9299501 : Blo 1072617 9299501 := bstep (se 3 (by rfl) ⟨1743656, by rfl⟩ : syracuseStep 9299501 = 3487313) B3487313
theorem B2418227 : Blo 1072617 2418227 := bstep (se 1 (by rfl) ⟨1813670, by rfl⟩ : syracuseStep 2418227 = 3627341) B3627341
theorem B1074743 : Blo 1072617 1074743 := bstep (se 1 (by rfl) ⟨806057, by rfl⟩ : syracuseStep 1074743 = 1612115) B1612115
theorem B1074763 : Blo 1072617 1074763 := bstep (se 1 (by rfl) ⟨806072, by rfl⟩ : syracuseStep 1074763 = 1612145) B1612145
theorem B1631831 : Blo 1072617 1631831 := bstep (se 1 (by rfl) ⟨1223873, by rfl⟩ : syracuseStep 1631831 = 2447747) B2447747
theorem B1074775 : Blo 1072617 1074775 := bstep (se 1 (by rfl) ⟨806081, by rfl⟩ : syracuseStep 1074775 = 1612163) B1612163
theorem B2418263 : Blo 1072617 2418263 := bstep (se 1 (by rfl) ⟨1813697, by rfl⟩ : syracuseStep 2418263 = 3627395) B3627395
theorem B1074795 : Blo 1072617 1074795 := bstep (se 1 (by rfl) ⟨806096, by rfl⟩ : syracuseStep 1074795 = 1612193) B1612193
theorem B1074807 : Blo 1072617 1074807 := bstep (se 1 (by rfl) ⟨806105, by rfl⟩ : syracuseStep 1074807 = 1612211) B1612211
theorem B1074827 : Blo 1072617 1074827 := bstep (se 1 (by rfl) ⟨806120, by rfl⟩ : syracuseStep 1074827 = 1612241) B1612241
theorem B1074839 : Blo 1072617 1074839 := bstep (se 1 (by rfl) ⟨806129, by rfl⟩ : syracuseStep 1074839 = 1612259) B1612259
theorem B3630743 : Blo 1072617 3630743 := bstep (se 1 (by rfl) ⟨2723057, by rfl⟩ : syracuseStep 3630743 = 5446115) B5446115
theorem B1074859 : Blo 1072617 1074859 := bstep (se 1 (by rfl) ⟨806144, by rfl⟩ : syracuseStep 1074859 = 1612289) B1612289
theorem B1074871 : Blo 1072617 1074871 := bstep (se 1 (by rfl) ⟨806153, by rfl⟩ : syracuseStep 1074871 = 1612307) B1612307
theorem B1074891 : Blo 1072617 1074891 := bstep (se 1 (by rfl) ⟨806168, by rfl⟩ : syracuseStep 1074891 = 1612337) B1612337
theorem B1074903 : Blo 1072617 1074903 := bstep (se 1 (by rfl) ⟨806177, by rfl⟩ : syracuseStep 1074903 = 1612355) B1612355
theorem B1074923 : Blo 1072617 1074923 := bstep (se 1 (by rfl) ⟨806192, by rfl⟩ : syracuseStep 1074923 = 1612385) B1612385
theorem B1074935 : Blo 1072617 1074935 := bstep (se 1 (by rfl) ⟨806201, by rfl⟩ : syracuseStep 1074935 = 1612403) B1612403
theorem B2418443 : Blo 1072617 2418443 := bstep (se 1 (by rfl) ⟨1813832, by rfl⟩ : syracuseStep 2418443 = 3627665) B3627665
theorem B1074955 : Blo 1072617 1074955 := bstep (se 1 (by rfl) ⟨806216, by rfl⟩ : syracuseStep 1074955 = 1612433) B1612433
theorem B1074967 : Blo 1072617 1074967 := bstep (se 1 (by rfl) ⟨806225, by rfl⟩ : syracuseStep 1074967 = 1612451) B1612451
theorem B1074987 : Blo 1072617 1074987 := bstep (se 1 (by rfl) ⟨806240, by rfl⟩ : syracuseStep 1074987 = 1612481) B1612481
theorem B1074999 : Blo 1072617 1074999 := bstep (se 1 (by rfl) ⟨806249, by rfl⟩ : syracuseStep 1074999 = 1612499) B1612499
theorem B2418497 : Blo 1072617 2418497 := bstep (se 2 (by rfl) ⟨906936, by rfl⟩ : syracuseStep 2418497 = 1813873) B1813873
theorem B1075019 : Blo 1072617 1075019 := bstep (se 1 (by rfl) ⟨806264, by rfl⟩ : syracuseStep 1075019 = 1612529) B1612529
theorem B1075031 : Blo 1072617 1075031 := bstep (se 1 (by rfl) ⟨806273, by rfl⟩ : syracuseStep 1075031 = 1612547) B1612547
theorem B1075051 : Blo 1072617 1075051 := bstep (se 1 (by rfl) ⟨806288, by rfl⟩ : syracuseStep 1075051 = 1612577) B1612577
theorem B1075063 : Blo 1072617 1075063 := bstep (se 1 (by rfl) ⟨806297, by rfl⟩ : syracuseStep 1075063 = 1612595) B1612595
theorem B1075083 : Blo 1072617 1075083 := bstep (se 1 (by rfl) ⟨806312, by rfl⟩ : syracuseStep 1075083 = 1612625) B1612625
theorem B1075095 : Blo 1072617 1075095 := bstep (se 1 (by rfl) ⟨806321, by rfl⟩ : syracuseStep 1075095 = 1612643) B1612643
theorem B1075115 : Blo 1072617 1075115 := bstep (se 1 (by rfl) ⟨806336, by rfl⟩ : syracuseStep 1075115 = 1612673) B1612673
theorem B16770995 : Blo 1072617 16770995 := bstep (se 1 (by rfl) ⟨12578246, by rfl⟩ : syracuseStep 16770995 = 25156493) B25156493
theorem B1075127 : Blo 1072617 1075127 := bstep (se 1 (by rfl) ⟨806345, by rfl⟩ : syracuseStep 1075127 = 1612691) B1612691
theorem B1075147 : Blo 1072617 1075147 := bstep (se 1 (by rfl) ⟨806360, by rfl⟩ : syracuseStep 1075147 = 1612721) B1612721
theorem B1075159 : Blo 1072617 1075159 := bstep (se 1 (by rfl) ⟨806369, by rfl⟩ : syracuseStep 1075159 = 1612739) B1612739
theorem B1075179 : Blo 1072617 1075179 := bstep (se 1 (by rfl) ⟨806384, by rfl⟩ : syracuseStep 1075179 = 1612769) B1612769
theorem B1075191 : Blo 1072617 1075191 := bstep (se 1 (by rfl) ⟨806393, by rfl⟩ : syracuseStep 1075191 = 1612787) B1612787
theorem B1075211 : Blo 1072617 1075211 := bstep (se 1 (by rfl) ⟨806408, by rfl⟩ : syracuseStep 1075211 = 1612817) B1612817
theorem B1075223 : Blo 1072617 1075223 := bstep (se 1 (by rfl) ⟨806417, by rfl⟩ : syracuseStep 1075223 = 1612835) B1612835
theorem B2418713 : Blo 1072617 2418713 := bstep (se 2 (by rfl) ⟨907017, by rfl⟩ : syracuseStep 2418713 = 1814035) B1814035
theorem B1075243 : Blo 1072617 1075243 := bstep (se 1 (by rfl) ⟨806432, by rfl⟩ : syracuseStep 1075243 = 1612865) B1612865
theorem B1075255 : Blo 1072617 1075255 := bstep (se 1 (by rfl) ⟨806441, by rfl⟩ : syracuseStep 1075255 = 1612883) B1612883
theorem B1075275 : Blo 1072617 1075275 := bstep (se 1 (by rfl) ⟨806456, by rfl⟩ : syracuseStep 1075275 = 1612913) B1612913
theorem B1075287 : Blo 1072617 1075287 := bstep (se 1 (by rfl) ⟨806465, by rfl⟩ : syracuseStep 1075287 = 1612931) B1612931
theorem B13789277 : Blo 1072617 13789277 := bstep (se 3 (by rfl) ⟨2585489, by rfl⟩ : syracuseStep 13789277 = 5170979) B5170979
theorem B9168997 : Blo 1072617 9168997 := bstep (se 4 (by rfl) ⟨859593, by rfl⟩ : syracuseStep 9168997 = 1719187) B1719187
theorem B1075307 : Blo 1072617 1075307 := bstep (se 1 (by rfl) ⟨806480, by rfl⟩ : syracuseStep 1075307 = 1612961) B1612961
theorem B2418803 : Blo 1072617 2418803 := bstep (se 1 (by rfl) ⟨1814102, by rfl⟩ : syracuseStep 2418803 = 3628205) B3628205
theorem B1075319 : Blo 1072617 1075319 := bstep (se 1 (by rfl) ⟨806489, by rfl⟩ : syracuseStep 1075319 = 1612979) B1612979
theorem B1075339 : Blo 1072617 1075339 := bstep (se 1 (by rfl) ⟨806504, by rfl⟩ : syracuseStep 1075339 = 1613009) B1613009
theorem B2418839 : Blo 1072617 2418839 := bstep (se 1 (by rfl) ⟨1814129, by rfl⟩ : syracuseStep 2418839 = 3628259) B3628259
theorem B1075351 : Blo 1072617 1075351 := bstep (se 1 (by rfl) ⟨806513, by rfl⟩ : syracuseStep 1075351 = 1613027) B1613027
theorem B1075371 : Blo 1072617 1075371 := bstep (se 1 (by rfl) ⟨806528, by rfl⟩ : syracuseStep 1075371 = 1613057) B1613057
theorem B3631283 : Blo 1072617 3631283 := bstep (se 1 (by rfl) ⟨2723462, by rfl⟩ : syracuseStep 3631283 = 5446925) B5446925
theorem B1075383 : Blo 1072617 1075383 := bstep (se 1 (by rfl) ⟨806537, by rfl⟩ : syracuseStep 1075383 = 1613075) B1613075
theorem B1075403 : Blo 1072617 1075403 := bstep (se 1 (by rfl) ⟨806552, by rfl⟩ : syracuseStep 1075403 = 1613105) B1613105
theorem B1075415 : Blo 1072617 1075415 := bstep (se 1 (by rfl) ⟨806561, by rfl⟩ : syracuseStep 1075415 = 1613123) B1613123
theorem B1075435 : Blo 1072617 1075435 := bstep (se 1 (by rfl) ⟨806576, by rfl⟩ : syracuseStep 1075435 = 1613153) B1613153
theorem B1075447 : Blo 1072617 1075447 := bstep (se 1 (by rfl) ⟨806585, by rfl⟩ : syracuseStep 1075447 = 1613171) B1613171
theorem B1075467 : Blo 1072617 1075467 := bstep (se 1 (by rfl) ⟨806600, by rfl⟩ : syracuseStep 1075467 = 1613201) B1613201
theorem B1075479 : Blo 1072617 1075479 := bstep (se 1 (by rfl) ⟨806609, by rfl⟩ : syracuseStep 1075479 = 1613219) B1613219
theorem B1075499 : Blo 1072617 1075499 := bstep (se 1 (by rfl) ⟨806624, by rfl⟩ : syracuseStep 1075499 = 1613249) B1613249
theorem B1075511 : Blo 1072617 1075511 := bstep (se 1 (by rfl) ⟨806633, by rfl⟩ : syracuseStep 1075511 = 1613267) B1613267
theorem B4581697 : Blo 1072617 4581697 := bstep (se 2 (by rfl) ⟨1718136, by rfl⟩ : syracuseStep 4581697 = 3436273) B3436273
theorem B2419019 : Blo 1072617 2419019 := bstep (se 1 (by rfl) ⟨1814264, by rfl⟩ : syracuseStep 2419019 = 3628529) B3628529
theorem B1075531 : Blo 1072617 1075531 := bstep (se 1 (by rfl) ⟨806648, by rfl⟩ : syracuseStep 1075531 = 1613297) B1613297
theorem B1075543 : Blo 1072617 1075543 := bstep (se 1 (by rfl) ⟨806657, by rfl⟩ : syracuseStep 1075543 = 1613315) B1613315
theorem B1075563 : Blo 1072617 1075563 := bstep (se 1 (by rfl) ⟨806672, by rfl⟩ : syracuseStep 1075563 = 1613345) B1613345
theorem B1075575 : Blo 1072617 1075575 := bstep (se 1 (by rfl) ⟨806681, by rfl⟩ : syracuseStep 1075575 = 1613363) B1613363
theorem B2419073 : Blo 1072617 2419073 := bstep (se 2 (by rfl) ⟨907152, by rfl⟩ : syracuseStep 2419073 = 1814305) B1814305
theorem B1075595 : Blo 1072617 1075595 := bstep (se 1 (by rfl) ⟨806696, by rfl⟩ : syracuseStep 1075595 = 1613393) B1613393
theorem B1075607 : Blo 1072617 1075607 := bstep (se 1 (by rfl) ⟨806705, by rfl⟩ : syracuseStep 1075607 = 1613411) B1613411
theorem B1075627 : Blo 1072617 1075627 := bstep (se 1 (by rfl) ⟨806720, by rfl⟩ : syracuseStep 1075627 = 1613441) B1613441
theorem B1075639 : Blo 1072617 1075639 := bstep (se 1 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 1075639 = 1613459) B1613459
theorem B3631553 : Blo 1072617 3631553 := bstep (se 2 (by rfl) ⟨1361832, by rfl⟩ : syracuseStep 3631553 = 2723665) B2723665
theorem B1075659 : Blo 1072617 1075659 := bstep (se 1 (by rfl) ⟨806744, by rfl⟩ : syracuseStep 1075659 = 1613489) B1613489
theorem B1075671 : Blo 1072617 1075671 := bstep (se 1 (by rfl) ⟨806753, by rfl⟩ : syracuseStep 1075671 = 1613507) B1613507
theorem B1075691 : Blo 1072617 1075691 := bstep (se 1 (by rfl) ⟨806768, by rfl⟩ : syracuseStep 1075691 = 1613537) B1613537
theorem B1075703 : Blo 1072617 1075703 := bstep (se 1 (by rfl) ⟨806777, by rfl⟩ : syracuseStep 1075703 = 1613555) B1613555
theorem B1075723 : Blo 1072617 1075723 := bstep (se 1 (by rfl) ⟨806792, by rfl⟩ : syracuseStep 1075723 = 1613585) B1613585
theorem B1075735 : Blo 1072617 1075735 := bstep (se 1 (by rfl) ⟨806801, by rfl⟩ : syracuseStep 1075735 = 1613603) B1613603
theorem B1075755 : Blo 1072617 1075755 := bstep (se 1 (by rfl) ⟨806816, by rfl⟩ : syracuseStep 1075755 = 1613633) B1613633
theorem B1075767 : Blo 1072617 1075767 := bstep (se 1 (by rfl) ⟨806825, by rfl⟩ : syracuseStep 1075767 = 1613651) B1613651
theorem B1206859 : Blo 1072617 1206859 := bstep (se 1 (by rfl) ⟨905144, by rfl⟩ : syracuseStep 1206859 = 1810289) B1810289
theorem B1075787 : Blo 1072617 1075787 := bstep (se 1 (by rfl) ⟨806840, by rfl⟩ : syracuseStep 1075787 = 1613681) B1613681
theorem B1075799 : Blo 1072617 1075799 := bstep (se 1 (by rfl) ⟨806849, by rfl⟩ : syracuseStep 1075799 = 1613699) B1613699
theorem B2419289 : Blo 1072617 2419289 := bstep (se 2 (by rfl) ⟨907233, by rfl⟩ : syracuseStep 2419289 = 1814467) B1814467
theorem B1075819 : Blo 1072617 1075819 := bstep (se 1 (by rfl) ⟨806864, by rfl⟩ : syracuseStep 1075819 = 1613729) B1613729
theorem B1075831 : Blo 1072617 1075831 := bstep (se 1 (by rfl) ⟨806873, by rfl⟩ : syracuseStep 1075831 = 1613747) B1613747
theorem B1075851 : Blo 1072617 1075851 := bstep (se 1 (by rfl) ⟨806888, by rfl⟩ : syracuseStep 1075851 = 1613777) B1613777
theorem B1075863 : Blo 1072617 1075863 := bstep (se 1 (by rfl) ⟨806897, by rfl⟩ : syracuseStep 1075863 = 1613795) B1613795
theorem B5171863 : Blo 1072617 5171863 := bstep (se 1 (by rfl) ⟨3878897, by rfl⟩ : syracuseStep 5171863 = 7757795) B7757795
theorem B1075883 : Blo 1072617 1075883 := bstep (se 1 (by rfl) ⟨806912, by rfl⟩ : syracuseStep 1075883 = 1613825) B1613825
theorem B2419379 : Blo 1072617 2419379 := bstep (se 1 (by rfl) ⟨1814534, by rfl⟩ : syracuseStep 2419379 = 3629069) B3629069
theorem B1206967 : Blo 1072617 1206967 := bstep (se 1 (by rfl) ⟨905225, by rfl⟩ : syracuseStep 1206967 = 1810451) B1810451
theorem B1075895 : Blo 1072617 1075895 := bstep (se 1 (by rfl) ⟨806921, by rfl⟩ : syracuseStep 1075895 = 1613843) B1613843
theorem B1075915 : Blo 1072617 1075915 := bstep (se 1 (by rfl) ⟨806936, by rfl⟩ : syracuseStep 1075915 = 1613873) B1613873
theorem B2419415 : Blo 1072617 2419415 := bstep (se 1 (by rfl) ⟨1814561, by rfl⟩ : syracuseStep 2419415 = 3629123) B3629123
theorem B1075927 : Blo 1072617 1075927 := bstep (se 1 (by rfl) ⟨806945, by rfl⟩ : syracuseStep 1075927 = 1613891) B1613891
theorem B1075947 : Blo 1072617 1075947 := bstep (se 1 (by rfl) ⟨806960, by rfl⟩ : syracuseStep 1075947 = 1613921) B1613921
theorem B1075959 : Blo 1072617 1075959 := bstep (se 1 (by rfl) ⟨806969, by rfl⟩ : syracuseStep 1075959 = 1613939) B1613939
theorem B1075979 : Blo 1072617 1075979 := bstep (se 1 (by rfl) ⟨806984, by rfl⟩ : syracuseStep 1075979 = 1613969) B1613969
theorem B1075991 : Blo 1072617 1075991 := bstep (se 1 (by rfl) ⟨806993, by rfl⟩ : syracuseStep 1075991 = 1613987) B1613987
theorem B1076011 : Blo 1072617 1076011 := bstep (se 1 (by rfl) ⟨807008, by rfl⟩ : syracuseStep 1076011 = 1614017) B1614017
theorem B1076023 : Blo 1072617 1076023 := bstep (se 1 (by rfl) ⟨807017, by rfl⟩ : syracuseStep 1076023 = 1614035) B1614035
theorem B1076043 : Blo 1072617 1076043 := bstep (se 1 (by rfl) ⟨807032, by rfl⟩ : syracuseStep 1076043 = 1614065) B1614065
theorem B1076055 : Blo 1072617 1076055 := bstep (se 1 (by rfl) ⟨807041, by rfl⟩ : syracuseStep 1076055 = 1614083) B1614083
theorem B1207147 : Blo 1072617 1207147 := bstep (se 1 (by rfl) ⟨905360, by rfl⟩ : syracuseStep 1207147 = 1810721) B1810721
theorem B1076075 : Blo 1072617 1076075 := bstep (se 1 (by rfl) ⟨807056, by rfl⟩ : syracuseStep 1076075 = 1614113) B1614113
theorem B1076087 : Blo 1072617 1076087 := bstep (se 1 (by rfl) ⟨807065, by rfl⟩ : syracuseStep 1076087 = 1614131) B1614131
theorem B2419595 : Blo 1072617 2419595 := bstep (se 1 (by rfl) ⟨1814696, by rfl⟩ : syracuseStep 2419595 = 3629393) B3629393
theorem B1076107 : Blo 1072617 1076107 := bstep (se 1 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 1076107 = 1614161) B1614161
theorem B1076119 : Blo 1072617 1076119 := bstep (se 1 (by rfl) ⟨807089, by rfl⟩ : syracuseStep 1076119 = 1614179) B1614179
theorem B1076139 : Blo 1072617 1076139 := bstep (se 1 (by rfl) ⟨807104, by rfl⟩ : syracuseStep 1076139 = 1614209) B1614209
theorem B1076151 : Blo 1072617 1076151 := bstep (se 1 (by rfl) ⟨807113, by rfl⟩ : syracuseStep 1076151 = 1614227) B1614227
theorem B2419649 : Blo 1072617 2419649 := bstep (se 2 (by rfl) ⟨907368, by rfl⟩ : syracuseStep 2419649 = 1814737) B1814737
theorem B1076171 : Blo 1072617 1076171 := bstep (se 1 (by rfl) ⟨807128, by rfl⟩ : syracuseStep 1076171 = 1614257) B1614257
theorem B1207255 : Blo 1072617 1207255 := bstep (se 1 (by rfl) ⟨905441, by rfl⟩ : syracuseStep 1207255 = 1810883) B1810883
theorem B1076183 : Blo 1072617 1076183 := bstep (se 1 (by rfl) ⟨807137, by rfl⟩ : syracuseStep 1076183 = 1614275) B1614275
theorem B3632093 : Blo 1072617 3632093 := bstep (se 3 (by rfl) ⟨681017, by rfl⟩ : syracuseStep 3632093 = 1362035) B1362035
theorem B1076203 : Blo 1072617 1076203 := bstep (se 1 (by rfl) ⟨807152, by rfl⟩ : syracuseStep 1076203 = 1614305) B1614305
theorem B1076215 : Blo 1072617 1076215 := bstep (se 1 (by rfl) ⟨807161, by rfl⟩ : syracuseStep 1076215 = 1614323) B1614323
theorem B1076235 : Blo 1072617 1076235 := bstep (se 1 (by rfl) ⟨807176, by rfl⟩ : syracuseStep 1076235 = 1614353) B1614353
theorem B1076247 : Blo 1072617 1076247 := bstep (se 1 (by rfl) ⟨807185, by rfl⟩ : syracuseStep 1076247 = 1614371) B1614371
theorem B9169955 : Blo 1072617 9169955 := bstep (se 1 (by rfl) ⟨6877466, by rfl⟩ : syracuseStep 9169955 = 13754933) B13754933
theorem B1076267 : Blo 1072617 1076267 := bstep (se 1 (by rfl) ⟨807200, by rfl⟩ : syracuseStep 1076267 = 1614401) B1614401
theorem B1076279 : Blo 1072617 1076279 := bstep (se 1 (by rfl) ⟨807209, by rfl⟩ : syracuseStep 1076279 = 1614419) B1614419
theorem B4713547 : Blo 1072617 4713547 := bstep (se 1 (by rfl) ⟨3535160, by rfl⟩ : syracuseStep 4713547 = 7070321) B7070321
theorem B1076299 : Blo 1072617 1076299 := bstep (se 1 (by rfl) ⟨807224, by rfl⟩ : syracuseStep 1076299 = 1614449) B1614449
theorem B1076311 : Blo 1072617 1076311 := bstep (se 1 (by rfl) ⟨807233, by rfl⟩ : syracuseStep 1076311 = 1614467) B1614467
theorem B1076331 : Blo 1072617 1076331 := bstep (se 1 (by rfl) ⟨807248, by rfl⟩ : syracuseStep 1076331 = 1614497) B1614497
theorem B1076343 : Blo 1072617 1076343 := bstep (se 1 (by rfl) ⟨807257, by rfl⟩ : syracuseStep 1076343 = 1614515) B1614515
theorem B1207435 : Blo 1072617 1207435 := bstep (se 1 (by rfl) ⟨905576, by rfl⟩ : syracuseStep 1207435 = 1811153) B1811153
theorem B1076363 : Blo 1072617 1076363 := bstep (se 1 (by rfl) ⟨807272, by rfl⟩ : syracuseStep 1076363 = 1614545) B1614545
theorem B1076375 : Blo 1072617 1076375 := bstep (se 1 (by rfl) ⟨807281, by rfl⟩ : syracuseStep 1076375 = 1614563) B1614563
theorem B2419865 : Blo 1072617 2419865 := bstep (se 2 (by rfl) ⟨907449, by rfl⟩ : syracuseStep 2419865 = 1814899) B1814899
theorem B1076395 : Blo 1072617 1076395 := bstep (se 1 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 1076395 = 1614593) B1614593
theorem B3402931 : Blo 1072617 3402931 := bstep (se 1 (by rfl) ⟨2552198, by rfl⟩ : syracuseStep 3402931 = 5104397) B5104397
theorem B1076407 : Blo 1072617 1076407 := bstep (se 1 (by rfl) ⟨807305, by rfl⟩ : syracuseStep 1076407 = 1614611) B1614611
theorem B1076427 : Blo 1072617 1076427 := bstep (se 1 (by rfl) ⟨807320, by rfl⟩ : syracuseStep 1076427 = 1614641) B1614641
theorem B1076439 : Blo 1072617 1076439 := bstep (se 1 (by rfl) ⟨807329, by rfl⟩ : syracuseStep 1076439 = 1614659) B1614659
theorem B1076459 : Blo 1072617 1076459 := bstep (se 1 (by rfl) ⟨807344, by rfl⟩ : syracuseStep 1076459 = 1614689) B1614689
theorem B2419955 : Blo 1072617 2419955 := bstep (se 1 (by rfl) ⟨1814966, by rfl⟩ : syracuseStep 2419955 = 3629933) B3629933
theorem B1207543 : Blo 1072617 1207543 := bstep (se 1 (by rfl) ⟨905657, by rfl⟩ : syracuseStep 1207543 = 1811315) B1811315
theorem B1076471 : Blo 1072617 1076471 := bstep (se 1 (by rfl) ⟨807353, by rfl⟩ : syracuseStep 1076471 = 1614707) B1614707
theorem B1076491 : Blo 1072617 1076491 := bstep (se 1 (by rfl) ⟨807368, by rfl⟩ : syracuseStep 1076491 = 1614737) B1614737
theorem B2419991 : Blo 1072617 2419991 := bstep (se 1 (by rfl) ⟨1814993, by rfl⟩ : syracuseStep 2419991 = 3629987) B3629987
theorem B1076503 : Blo 1072617 1076503 := bstep (se 1 (by rfl) ⟨807377, by rfl⟩ : syracuseStep 1076503 = 1614755) B1614755
theorem B1076523 : Blo 1072617 1076523 := bstep (se 1 (by rfl) ⟨807392, by rfl⟩ : syracuseStep 1076523 = 1614785) B1614785
theorem B1076535 : Blo 1072617 1076535 := bstep (se 1 (by rfl) ⟨807401, by rfl⟩ : syracuseStep 1076535 = 1614803) B1614803
theorem B1076555 : Blo 1072617 1076555 := bstep (se 1 (by rfl) ⟨807416, by rfl⟩ : syracuseStep 1076555 = 1614833) B1614833
theorem B1076567 : Blo 1072617 1076567 := bstep (se 1 (by rfl) ⟨807425, by rfl⟩ : syracuseStep 1076567 = 1614851) B1614851
theorem B1076587 : Blo 1072617 1076587 := bstep (se 1 (by rfl) ⟨807440, by rfl⟩ : syracuseStep 1076587 = 1614881) B1614881
theorem B1076599 : Blo 1072617 1076599 := bstep (se 1 (by rfl) ⟨807449, by rfl⟩ : syracuseStep 1076599 = 1614899) B1614899
theorem B5434775 : Blo 1072617 5434775 := bstep (se 1 (by rfl) ⟨4076081, by rfl⟩ : syracuseStep 5434775 = 8152163) B8152163
theorem B1207723 : Blo 1072617 1207723 := bstep (se 1 (by rfl) ⟨905792, by rfl⟩ : syracuseStep 1207723 = 1811585) B1811585
theorem B2584001 : Blo 1072617 2584001 := bstep (se 2 (by rfl) ⟨969000, by rfl⟩ : syracuseStep 2584001 = 1938001) B1938001
theorem B2420171 : Blo 1072617 2420171 := bstep (se 1 (by rfl) ⟨1815128, by rfl⟩ : syracuseStep 2420171 = 3630257) B3630257
theorem B2420225 : Blo 1072617 2420225 := bstep (se 2 (by rfl) ⟨907584, by rfl⟩ : syracuseStep 2420225 = 1815169) B1815169
theorem B1207831 : Blo 1072617 1207831 := bstep (se 1 (by rfl) ⟨905873, by rfl⟩ : syracuseStep 1207831 = 1811747) B1811747
theorem B6123053 : Blo 1072617 6123053 := bstep (se 3 (by rfl) ⟨1148072, by rfl⟩ : syracuseStep 6123053 = 2296145) B2296145
theorem B9072307 : Blo 1072617 9072307 := bstep (se 1 (by rfl) ⟨6804230, by rfl⟩ : syracuseStep 9072307 = 13608461) B13608461
theorem B1208011 : Blo 1072617 1208011 := bstep (se 1 (by rfl) ⟨906008, by rfl⟩ : syracuseStep 1208011 = 1812017) B1812017
theorem B2715353 : Blo 1072617 2715353 := bstep (se 2 (by rfl) ⟨1018257, by rfl⟩ : syracuseStep 2715353 = 2036515) B2036515
theorem B2420441 : Blo 1072617 2420441 := bstep (se 2 (by rfl) ⟨907665, by rfl⟩ : syracuseStep 2420441 = 1815331) B1815331
theorem B2420531 : Blo 1072617 2420531 := bstep (se 1 (by rfl) ⟨1815398, by rfl⟩ : syracuseStep 2420531 = 3630797) B3630797
theorem B1208119 : Blo 1072617 1208119 := bstep (se 1 (by rfl) ⟨906089, by rfl⟩ : syracuseStep 1208119 = 1812179) B1812179
theorem B1961815 : Blo 1072617 1961815 := bstep (se 1 (by rfl) ⟨1471361, by rfl⟩ : syracuseStep 1961815 = 2942723) B2942723
theorem B2420567 : Blo 1072617 2420567 := bstep (se 1 (by rfl) ⟨1815425, by rfl⟩ : syracuseStep 2420567 = 3630851) B3630851
theorem B1208299 : Blo 1072617 1208299 := bstep (se 1 (by rfl) ⟨906224, by rfl⟩ : syracuseStep 1208299 = 1812449) B1812449
theorem B2420747 : Blo 1072617 2420747 := bstep (se 1 (by rfl) ⟨1815560, by rfl⟩ : syracuseStep 2420747 = 3631121) B3631121
theorem B2420801 : Blo 1072617 2420801 := bstep (se 2 (by rfl) ⟨907800, by rfl⟩ : syracuseStep 2420801 = 1815601) B1815601
theorem B3633227 : Blo 1072617 3633227 := bstep (se 1 (by rfl) ⟨2724920, by rfl⟩ : syracuseStep 3633227 = 5449841) B5449841
theorem B1208407 : Blo 1072617 1208407 := bstep (se 1 (by rfl) ⟨906305, by rfl⟩ : syracuseStep 1208407 = 1812611) B1812611
theorem B1208587 : Blo 1072617 1208587 := bstep (se 1 (by rfl) ⟨906440, by rfl⟩ : syracuseStep 1208587 = 1812881) B1812881
theorem B2421017 : Blo 1072617 2421017 := bstep (se 2 (by rfl) ⟨907881, by rfl⟩ : syracuseStep 2421017 = 1815763) B1815763
theorem B3633497 : Blo 1072617 3633497 := bstep (se 2 (by rfl) ⟨1362561, by rfl⟩ : syracuseStep 3633497 = 2725123) B2725123
theorem B2421107 : Blo 1072617 2421107 := bstep (se 1 (by rfl) ⟨1815830, by rfl⟩ : syracuseStep 2421107 = 3631661) B3631661
theorem B1208695 : Blo 1072617 1208695 := bstep (se 1 (by rfl) ⟨906521, by rfl⟩ : syracuseStep 1208695 = 1813043) B1813043
theorem B2421143 : Blo 1072617 2421143 := bstep (se 1 (by rfl) ⟨1815857, by rfl⟩ : syracuseStep 2421143 = 3631715) B3631715
theorem B1208875 : Blo 1072617 1208875 := bstep (se 1 (by rfl) ⟨906656, by rfl⟩ : syracuseStep 1208875 = 1813313) B1813313
theorem B2421323 : Blo 1072617 2421323 := bstep (se 1 (by rfl) ⟨1815992, by rfl⟩ : syracuseStep 2421323 = 3631985) B3631985
theorem B2421377 : Blo 1072617 2421377 := bstep (se 2 (by rfl) ⟨908016, by rfl⟩ : syracuseStep 2421377 = 1816033) B1816033
theorem B8286851 : Blo 1072617 8286851 := bstep (se 1 (by rfl) ⟨6215138, by rfl⟩ : syracuseStep 8286851 = 12430277) B12430277
theorem B1208983 : Blo 1072617 1208983 := bstep (se 1 (by rfl) ⟨906737, by rfl⟩ : syracuseStep 1208983 = 1813475) B1813475
theorem B2585239 : Blo 1072617 2585239 := bstep (se 1 (by rfl) ⟨1938929, by rfl⟩ : syracuseStep 2585239 = 3877859) B3877859
theorem B1209163 : Blo 1072617 1209163 := bstep (se 1 (by rfl) ⟨906872, by rfl⟩ : syracuseStep 1209163 = 1813745) B1813745
theorem B2421593 : Blo 1072617 2421593 := bstep (se 2 (by rfl) ⟨908097, by rfl⟩ : syracuseStep 2421593 = 1816195) B1816195
theorem B2421683 : Blo 1072617 2421683 := bstep (se 1 (by rfl) ⟨1816262, by rfl⟩ : syracuseStep 2421683 = 3632525) B3632525
theorem B1209271 : Blo 1072617 1209271 := bstep (se 1 (by rfl) ⟨906953, by rfl⟩ : syracuseStep 1209271 = 1813907) B1813907
theorem B2421719 : Blo 1072617 2421719 := bstep (se 1 (by rfl) ⟨1816289, by rfl⟩ : syracuseStep 2421719 = 3632579) B3632579
theorem B3437657 : Blo 1072617 3437657 := bstep (se 2 (by rfl) ⟨1289121, by rfl⟩ : syracuseStep 3437657 = 2578243) B2578243
theorem B1209451 : Blo 1072617 1209451 := bstep (se 1 (by rfl) ⟨907088, by rfl⟩ : syracuseStep 1209451 = 1814177) B1814177
theorem B2421899 : Blo 1072617 2421899 := bstep (se 1 (by rfl) ⟨1816424, by rfl⟩ : syracuseStep 2421899 = 3632849) B3632849
theorem B2421953 : Blo 1072617 2421953 := bstep (se 2 (by rfl) ⟨908232, by rfl⟩ : syracuseStep 2421953 = 1816465) B1816465
theorem B1209559 : Blo 1072617 1209559 := bstep (se 1 (by rfl) ⟨907169, by rfl⟩ : syracuseStep 1209559 = 1814339) B1814339
theorem B2717003 : Blo 1072617 2717003 := bstep (se 1 (by rfl) ⟨2037752, by rfl⟩ : syracuseStep 2717003 = 4075505) B4075505
theorem B1209739 : Blo 1072617 1209739 := bstep (se 1 (by rfl) ⟨907304, by rfl⟩ : syracuseStep 1209739 = 1814609) B1814609
theorem B2422169 : Blo 1072617 2422169 := bstep (se 2 (by rfl) ⟨908313, by rfl⟩ : syracuseStep 2422169 = 1816627) B1816627
theorem B3732929 : Blo 1072617 3732929 := bstep (se 2 (by rfl) ⟨1399848, by rfl⟩ : syracuseStep 3732929 = 2799697) B2799697
theorem B2422259 : Blo 1072617 2422259 := bstep (se 1 (by rfl) ⟨1816694, by rfl⟩ : syracuseStep 2422259 = 3633389) B3633389
theorem B1209847 : Blo 1072617 1209847 := bstep (se 1 (by rfl) ⟨907385, by rfl⟩ : syracuseStep 1209847 = 1814771) B1814771
theorem B2422295 : Blo 1072617 2422295 := bstep (se 1 (by rfl) ⟨1816721, by rfl⟩ : syracuseStep 2422295 = 3633443) B3633443
theorem B1570379 : Blo 1072617 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B1210027 : Blo 1072617 1210027 := bstep (se 1 (by rfl) ⟨907520, by rfl⟩ : syracuseStep 1210027 = 1815041) B1815041
theorem B6616849 : Blo 1072617 6616849 := bstep (se 2 (by rfl) ⟨2481318, by rfl⟩ : syracuseStep 6616849 = 4962637) B4962637
theorem B1210135 : Blo 1072617 1210135 := bstep (se 1 (by rfl) ⟨907601, by rfl⟩ : syracuseStep 1210135 = 1815203) B1815203
theorem B6879107 : Blo 1072617 6879107 := bstep (se 1 (by rfl) ⟨5159330, by rfl⟩ : syracuseStep 6879107 = 10318661) B10318661
theorem B1210315 : Blo 1072617 1210315 := bstep (se 1 (by rfl) ⟨907736, by rfl⟩ : syracuseStep 1210315 = 1815473) B1815473
theorem B1210423 : Blo 1072617 1210423 := bstep (se 1 (by rfl) ⟨907817, by rfl⟩ : syracuseStep 1210423 = 1815635) B1815635
theorem B4356299 : Blo 1072617 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B2324695 : Blo 1072617 2324695 := bstep (se 1 (by rfl) ⟨1743521, by rfl⟩ : syracuseStep 2324695 = 3487043) B3487043
theorem B1210603 : Blo 1072617 1210603 := bstep (se 1 (by rfl) ⟨907952, by rfl⟩ : syracuseStep 1210603 = 1815905) B1815905
theorem B2291969 : Blo 1072617 2291969 := bstep (se 2 (by rfl) ⟨859488, by rfl⟩ : syracuseStep 2291969 = 1718977) B1718977
theorem B2717975 : Blo 1072617 2717975 := bstep (se 1 (by rfl) ⟨2038481, by rfl⟩ : syracuseStep 2717975 = 4076963) B4076963
theorem B1210711 : Blo 1072617 1210711 := bstep (se 1 (by rfl) ⟨908033, by rfl⟩ : syracuseStep 1210711 = 1816067) B1816067
theorem B1210891 : Blo 1072617 1210891 := bstep (se 1 (by rfl) ⟨908168, by rfl⟩ : syracuseStep 1210891 = 1816337) B1816337
theorem B4356625 : Blo 1072617 4356625 := bstep (se 2 (by rfl) ⟨1633734, by rfl⟩ : syracuseStep 4356625 = 3267469) B3267469
theorem B4356659 : Blo 1072617 4356659 := bstep (se 1 (by rfl) ⟨3267494, by rfl⟩ : syracuseStep 4356659 = 6534989) B6534989
theorem B4651609 : Blo 1072617 4651609 := bstep (se 2 (by rfl) ⟨1744353, by rfl⟩ : syracuseStep 4651609 = 3488707) B3488707
theorem B1210999 : Blo 1072617 1210999 := bstep (se 1 (by rfl) ⟨908249, by rfl⟩ : syracuseStep 1210999 = 1816499) B1816499
theorem B4356787 : Blo 1072617 4356787 := bstep (se 1 (by rfl) ⟨3267590, by rfl⟩ : syracuseStep 4356787 = 6535181) B6535181
theorem B3439297 : Blo 1072617 3439297 := bstep (se 2 (by rfl) ⟨1289736, by rfl⟩ : syracuseStep 3439297 = 2579473) B2579473
theorem B1211179 : Blo 1072617 1211179 := bstep (se 1 (by rfl) ⟨908384, by rfl⟩ : syracuseStep 1211179 = 1816769) B1816769
theorem B5438339 : Blo 1072617 5438339 := bstep (se 1 (by rfl) ⟨4078754, by rfl⟩ : syracuseStep 5438339 = 8157509) B8157509
theorem B2718643 : Blo 1072617 2718643 := bstep (se 1 (by rfl) ⟨2038982, by rfl⟩ : syracuseStep 2718643 = 4077965) B4077965
theorem B1145783 : Blo 1072617 1145783 := bstep (se 1 (by rfl) ⟨859337, by rfl⟩ : syracuseStep 1145783 = 1718675) B1718675
theorem B2718785 : Blo 1072617 2718785 := bstep (se 2 (by rfl) ⟨1019544, by rfl⟩ : syracuseStep 2718785 = 2039089) B2039089
theorem B2620505 : Blo 1072617 2620505 := bstep (se 2 (by rfl) ⟨982689, by rfl⟩ : syracuseStep 2620505 = 1965379) B1965379
theorem B8158481 : Blo 1072617 8158481 := bstep (se 2 (by rfl) ⟨3059430, by rfl⟩ : syracuseStep 8158481 = 6118861) B6118861
theorem B1146155 : Blo 1072617 1146155 := bstep (se 1 (by rfl) ⟨859616, by rfl⟩ : syracuseStep 1146155 = 1719233) B1719233
theorem B10452401 : Blo 1072617 10452401 := bstep (se 2 (by rfl) ⟨3919650, by rfl⟩ : syracuseStep 10452401 = 7839301) B7839301
theorem B9174707 : Blo 1072617 9174707 := bstep (se 1 (by rfl) ⟨6881030, by rfl⟩ : syracuseStep 9174707 = 13762061) B13762061
theorem B1933121 : Blo 1072617 1933121 := bstep (se 2 (by rfl) ⟨724920, by rfl⟩ : syracuseStep 1933121 = 1449841) B1449841
theorem B2064217 : Blo 1072617 2064217 := bstep (se 2 (by rfl) ⟨774081, by rfl⟩ : syracuseStep 2064217 = 1548163) B1548163
theorem B11009969 : Blo 1072617 11009969 := bstep (se 2 (by rfl) ⟨4128738, by rfl⟩ : syracuseStep 11009969 = 8257477) B8257477
theorem B2719777 : Blo 1072617 2719777 := bstep (se 2 (by rfl) ⟨1019916, by rfl⟩ : syracuseStep 2719777 = 2039833) B2039833
theorem B9175355 : Blo 1072617 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B2720375 : Blo 1072617 2720375 := bstep (se 1 (by rfl) ⟨2040281, by rfl⟩ : syracuseStep 2720375 = 4080563) B4080563
theorem B2753551 : Blo 1072617 2753551 := bstep (se 1 (by rfl) ⟨2065163, by rfl⟩ : syracuseStep 2753551 = 4130327) B4130327
theorem B5440769 : Blo 1072617 5440769 := bstep (se 2 (by rfl) ⟨2040288, by rfl⟩ : syracuseStep 5440769 = 4080577) B4080577
theorem B6882695 : Blo 1072617 6882695 := bstep (se 1 (by rfl) ⟨5162021, by rfl⟩ : syracuseStep 6882695 = 10324043) B10324043
theorem B1148423 : Blo 1072617 1148423 := bstep (se 1 (by rfl) ⟨861317, by rfl⟩ : syracuseStep 1148423 = 1722635) B1722635
theorem B5506627 : Blo 1072617 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B2721671 : Blo 1072617 2721671 := bstep (se 1 (by rfl) ⟨2041253, by rfl⟩ : syracuseStep 2721671 = 4082507) B4082507
theorem B2721721 : Blo 1072617 2721721 := bstep (se 2 (by rfl) ⟨1020645, by rfl⟩ : syracuseStep 2721721 = 2041291) B2041291
theorem B6129593 : Blo 1072617 6129593 := bstep (se 2 (by rfl) ⟨2298597, by rfl⟩ : syracuseStep 6129593 = 4597195) B4597195
theorem B5441579 : Blo 1072617 5441579 := bstep (se 1 (by rfl) ⟨4081184, by rfl⟩ : syracuseStep 5441579 = 8162369) B8162369
theorem B1149115 : Blo 1072617 1149115 := bstep (se 1 (by rfl) ⟨861836, by rfl⟩ : syracuseStep 1149115 = 1723673) B1723673
theorem B11634961 : Blo 1072617 11634961 := bstep (se 2 (by rfl) ⟨4363110, by rfl⟩ : syracuseStep 11634961 = 8726221) B8726221
theorem B5507531 : Blo 1072617 5507531 := bstep (se 1 (by rfl) ⟨4130648, by rfl⟩ : syracuseStep 5507531 = 8261297) B8261297
theorem B2722319 : Blo 1072617 2722319 := bstep (se 1 (by rfl) ⟨2041739, by rfl⟩ : syracuseStep 2722319 = 4083479) B4083479
theorem B1935931 : Blo 1072617 1935931 := bstep (se 1 (by rfl) ⟨1451948, by rfl⟩ : syracuseStep 1935931 = 2903897) B2903897
theorem B2296505 : Blo 1072617 2296505 := bstep (se 2 (by rfl) ⟨861189, by rfl⟩ : syracuseStep 2296505 = 1722379) B1722379
theorem B5507777 : Blo 1072617 5507777 := bstep (se 2 (by rfl) ⟨2065416, by rfl⟩ : syracuseStep 5507777 = 4130833) B4130833
theorem B136186609 : Blo 1072617 136186609 := bstep (se 2 (by rfl) ⟨51069978, by rfl⟩ : syracuseStep 136186609 = 102139957) B102139957
theorem B3869441 : Blo 1072617 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B12225329 : Blo 1072617 12225329 := bstep (se 2 (by rfl) ⟨4584498, by rfl⟩ : syracuseStep 12225329 = 9168997) B9168997
theorem B9178019 : Blo 1072617 9178019 := bstep (se 1 (by rfl) ⟨6883514, by rfl⟩ : syracuseStep 9178019 = 13767029) B13767029
theorem B2723017 : Blo 1072617 2723017 := bstep (se 2 (by rfl) ⟨1021131, by rfl⟩ : syracuseStep 2723017 = 2042263) B2042263
theorem B1609019 : Blo 1072617 1609019 := bstep (se 1 (by rfl) ⟨1206764, by rfl⟩ : syracuseStep 1609019 = 2413529) B2413529
theorem B5442875 : Blo 1072617 5442875 := bstep (se 1 (by rfl) ⟨4082156, by rfl⟩ : syracuseStep 5442875 = 8164313) B8164313
theorem B2723159 : Blo 1072617 2723159 := bstep (se 1 (by rfl) ⟨2042369, by rfl⟩ : syracuseStep 2723159 = 4084739) B4084739
theorem B1609079 : Blo 1072617 1609079 := bstep (se 1 (by rfl) ⟨1206809, by rfl⟩ : syracuseStep 1609079 = 2413619) B2413619
theorem B1609103 : Blo 1072617 1609103 := bstep (se 1 (by rfl) ⟨1206827, by rfl⟩ : syracuseStep 1609103 = 2413655) B2413655
theorem B3444115 : Blo 1072617 3444115 := bstep (se 1 (by rfl) ⟨2583086, by rfl⟩ : syracuseStep 3444115 = 5166173) B5166173
theorem B1609145 : Blo 1072617 1609145 := bstep (se 2 (by rfl) ⟨603429, by rfl⟩ : syracuseStep 1609145 = 1206859) B1206859
theorem B5443037 : Blo 1072617 5443037 := bstep (se 3 (by rfl) ⟨1020569, by rfl⟩ : syracuseStep 5443037 = 2041139) B2041139
theorem B1609223 : Blo 1072617 1609223 := bstep (se 1 (by rfl) ⟨1206917, by rfl⟩ : syracuseStep 1609223 = 2413835) B2413835
theorem B1609259 : Blo 1072617 1609259 := bstep (se 1 (by rfl) ⟨1206944, by rfl⟩ : syracuseStep 1609259 = 2413889) B2413889
theorem B1609289 : Blo 1072617 1609289 := bstep (se 2 (by rfl) ⟨603483, by rfl⟩ : syracuseStep 1609289 = 1206967) B1206967
theorem B1609403 : Blo 1072617 1609403 := bstep (se 1 (by rfl) ⟨1207052, by rfl⟩ : syracuseStep 1609403 = 2414105) B2414105
theorem B5508809 : Blo 1072617 5508809 := bstep (se 2 (by rfl) ⟨2065803, by rfl⟩ : syracuseStep 5508809 = 4131607) B4131607
theorem B1609463 : Blo 1072617 1609463 := bstep (se 1 (by rfl) ⟨1207097, by rfl⟩ : syracuseStep 1609463 = 2414195) B2414195
theorem B1609487 : Blo 1072617 1609487 := bstep (se 1 (by rfl) ⟨1207115, by rfl⟩ : syracuseStep 1609487 = 2414231) B2414231
theorem B5443361 : Blo 1072617 5443361 := bstep (se 2 (by rfl) ⟨2041260, by rfl⟩ : syracuseStep 5443361 = 4082521) B4082521
theorem B2068267 : Blo 1072617 2068267 := bstep (se 1 (by rfl) ⟨1551200, by rfl⟩ : syracuseStep 2068267 = 3102401) B3102401
theorem B1609529 : Blo 1072617 1609529 := bstep (se 2 (by rfl) ⟨603573, by rfl⟩ : syracuseStep 1609529 = 1207147) B1207147
theorem B1609607 : Blo 1072617 1609607 := bstep (se 1 (by rfl) ⟨1207205, by rfl⟩ : syracuseStep 1609607 = 2414411) B2414411
theorem B1937287 : Blo 1072617 1937287 := bstep (se 1 (by rfl) ⟨1452965, by rfl⟩ : syracuseStep 1937287 = 2905931) B2905931
theorem B7737241 : Blo 1072617 7737241 := bstep (se 2 (by rfl) ⟨2901465, by rfl⟩ : syracuseStep 7737241 = 5802931) B5802931
theorem B1609643 : Blo 1072617 1609643 := bstep (se 1 (by rfl) ⟨1207232, by rfl⟩ : syracuseStep 1609643 = 2414465) B2414465
theorem B1609673 : Blo 1072617 1609673 := bstep (se 2 (by rfl) ⟨603627, by rfl⟩ : syracuseStep 1609673 = 1207255) B1207255
theorem B1609787 : Blo 1072617 1609787 := bstep (se 1 (by rfl) ⟨1207340, by rfl⟩ : syracuseStep 1609787 = 2414681) B2414681
theorem B1609847 : Blo 1072617 1609847 := bstep (se 1 (by rfl) ⟨1207385, by rfl⟩ : syracuseStep 1609847 = 2414771) B2414771
theorem B1609871 : Blo 1072617 1609871 := bstep (se 1 (by rfl) ⟨1207403, by rfl⟩ : syracuseStep 1609871 = 2414807) B2414807
theorem B1609913 : Blo 1072617 1609913 := bstep (se 2 (by rfl) ⟨603717, by rfl⟩ : syracuseStep 1609913 = 1207435) B1207435
theorem B1609991 : Blo 1072617 1609991 := bstep (se 1 (by rfl) ⟨1207493, by rfl⟩ : syracuseStep 1609991 = 2414987) B2414987
theorem B2298127 : Blo 1072617 2298127 := bstep (se 1 (by rfl) ⟨1723595, by rfl⟩ : syracuseStep 2298127 = 3447191) B3447191
theorem B4657441 : Blo 1072617 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B2298145 : Blo 1072617 2298145 := bstep (se 2 (by rfl) ⟨861804, by rfl⟩ : syracuseStep 2298145 = 1723609) B1723609
theorem B1610027 : Blo 1072617 1610027 := bstep (se 1 (by rfl) ⟨1207520, by rfl⟩ : syracuseStep 1610027 = 2415041) B2415041
theorem B1610057 : Blo 1072617 1610057 := bstep (se 2 (by rfl) ⟨603771, by rfl⟩ : syracuseStep 1610057 = 1207543) B1207543
theorem B1937849 : Blo 1072617 1937849 := bstep (se 2 (by rfl) ⟨726693, by rfl⟩ : syracuseStep 1937849 = 1453387) B1453387
theorem B1610171 : Blo 1072617 1610171 := bstep (se 1 (by rfl) ⟨1207628, by rfl⟩ : syracuseStep 1610171 = 2415257) B2415257
theorem B1610231 : Blo 1072617 1610231 := bstep (se 1 (by rfl) ⟨1207673, by rfl⟩ : syracuseStep 1610231 = 2415347) B2415347
theorem B1610255 : Blo 1072617 1610255 := bstep (se 1 (by rfl) ⟨1207691, by rfl⟩ : syracuseStep 1610255 = 2415383) B2415383
theorem B1610297 : Blo 1072617 1610297 := bstep (se 2 (by rfl) ⟨603861, by rfl⟩ : syracuseStep 1610297 = 1207723) B1207723
theorem B1610375 : Blo 1072617 1610375 := bstep (se 1 (by rfl) ⟨1207781, by rfl⟩ : syracuseStep 1610375 = 2415563) B2415563
theorem B2298503 : Blo 1072617 2298503 := bstep (se 1 (by rfl) ⟨1723877, by rfl⟩ : syracuseStep 2298503 = 3447755) B3447755
theorem B1610411 : Blo 1072617 1610411 := bstep (se 1 (by rfl) ⟨1207808, by rfl⟩ : syracuseStep 1610411 = 2415617) B2415617
theorem B1610441 : Blo 1072617 1610441 := bstep (se 2 (by rfl) ⟨603915, by rfl⟩ : syracuseStep 1610441 = 1207831) B1207831
theorem B5444333 : Blo 1072617 5444333 := bstep (se 3 (by rfl) ⟨1020812, by rfl⟩ : syracuseStep 5444333 = 2041625) B2041625
theorem B24843023 : Blo 1072617 24843023 := bstep (se 1 (by rfl) ⟨18632267, by rfl⟩ : syracuseStep 24843023 = 37264535) B37264535
theorem B2757419 : Blo 1072617 2757419 := bstep (se 1 (by rfl) ⟨2068064, by rfl⟩ : syracuseStep 2757419 = 4136129) B4136129
theorem B1610555 : Blo 1072617 1610555 := bstep (se 1 (by rfl) ⟨1207916, by rfl⟩ : syracuseStep 1610555 = 2415833) B2415833
theorem B1610615 : Blo 1072617 1610615 := bstep (se 1 (by rfl) ⟨1207961, by rfl⟩ : syracuseStep 1610615 = 2415923) B2415923
theorem B1610639 : Blo 1072617 1610639 := bstep (se 1 (by rfl) ⟨1207979, by rfl⟩ : syracuseStep 1610639 = 2415959) B2415959
theorem B1610681 : Blo 1072617 1610681 := bstep (se 2 (by rfl) ⟨604005, by rfl⟩ : syracuseStep 1610681 = 1208011) B1208011
theorem B1610759 : Blo 1072617 1610759 := bstep (se 1 (by rfl) ⟨1208069, by rfl⟩ : syracuseStep 1610759 = 2416139) B2416139
theorem B1610795 : Blo 1072617 1610795 := bstep (se 1 (by rfl) ⟨1208096, by rfl⟩ : syracuseStep 1610795 = 2416193) B2416193
theorem B1610825 : Blo 1072617 1610825 := bstep (se 2 (by rfl) ⟨604059, by rfl⟩ : syracuseStep 1610825 = 1208119) B1208119
theorem B3445847 : Blo 1072617 3445847 := bstep (se 1 (by rfl) ⟨2584385, by rfl⟩ : syracuseStep 3445847 = 5168771) B5168771
theorem B1610939 : Blo 1072617 1610939 := bstep (se 1 (by rfl) ⟨1208204, by rfl⟩ : syracuseStep 1610939 = 2416409) B2416409
theorem B1610999 : Blo 1072617 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B1611023 : Blo 1072617 1611023 := bstep (se 1 (by rfl) ⟨1208267, by rfl⟩ : syracuseStep 1611023 = 2416535) B2416535
theorem B1611065 : Blo 1072617 1611065 := bstep (se 2 (by rfl) ⟨604149, by rfl⟩ : syracuseStep 1611065 = 1208299) B1208299
theorem B5805371 : Blo 1072617 5805371 := bstep (se 1 (by rfl) ⟨4354028, by rfl⟩ : syracuseStep 5805371 = 8708057) B8708057
theorem B11638075 : Blo 1072617 11638075 := bstep (se 1 (by rfl) ⟨8728556, by rfl⟩ : syracuseStep 11638075 = 17457113) B17457113
theorem B1611143 : Blo 1072617 1611143 := bstep (se 1 (by rfl) ⟨1208357, by rfl⟩ : syracuseStep 1611143 = 2416715) B2416715
theorem B1611179 : Blo 1072617 1611179 := bstep (se 1 (by rfl) ⟨1208384, by rfl⟩ : syracuseStep 1611179 = 2416769) B2416769
theorem B1611209 : Blo 1072617 1611209 := bstep (se 2 (by rfl) ⟨604203, by rfl⟩ : syracuseStep 1611209 = 1208407) B1208407
theorem B5445143 : Blo 1072617 5445143 := bstep (se 1 (by rfl) ⟨4083857, by rfl⟩ : syracuseStep 5445143 = 8167715) B8167715
theorem B1611323 : Blo 1072617 1611323 := bstep (se 1 (by rfl) ⟨1208492, by rfl⟩ : syracuseStep 1611323 = 2416985) B2416985
theorem B3872323 : Blo 1072617 3872323 := bstep (se 1 (by rfl) ⟨2904242, by rfl⟩ : syracuseStep 3872323 = 5808485) B5808485
theorem B1611383 : Blo 1072617 1611383 := bstep (se 1 (by rfl) ⟨1208537, by rfl⟩ : syracuseStep 1611383 = 2417075) B2417075
theorem B1611407 : Blo 1072617 1611407 := bstep (se 1 (by rfl) ⟨1208555, by rfl⟩ : syracuseStep 1611407 = 2417111) B2417111
theorem B1611449 : Blo 1072617 1611449 := bstep (se 2 (by rfl) ⟨604293, by rfl⟩ : syracuseStep 1611449 = 1208587) B1208587
theorem B6887105 : Blo 1072617 6887105 := bstep (se 2 (by rfl) ⟨2582664, by rfl⟩ : syracuseStep 6887105 = 5165329) B5165329
theorem B2037449 : Blo 1072617 2037449 := bstep (se 2 (by rfl) ⟨764043, by rfl⟩ : syracuseStep 2037449 = 1528087) B1528087
theorem B1611527 : Blo 1072617 1611527 := bstep (se 1 (by rfl) ⟨1208645, by rfl⟩ : syracuseStep 1611527 = 2417291) B2417291
theorem B1611563 : Blo 1072617 1611563 := bstep (se 1 (by rfl) ⟨1208672, by rfl⟩ : syracuseStep 1611563 = 2417345) B2417345
theorem B1611593 : Blo 1072617 1611593 := bstep (se 2 (by rfl) ⟨604347, by rfl⟩ : syracuseStep 1611593 = 1208695) B1208695
theorem B12556147 : Blo 1072617 12556147 := bstep (se 1 (by rfl) ⟨9417110, by rfl⟩ : syracuseStep 12556147 = 18834221) B18834221
theorem B1611707 : Blo 1072617 1611707 := bstep (se 1 (by rfl) ⟨1208780, by rfl⟩ : syracuseStep 1611707 = 2417561) B2417561
theorem B1611767 : Blo 1072617 1611767 := bstep (se 1 (by rfl) ⟨1208825, by rfl⟩ : syracuseStep 1611767 = 2417651) B2417651
theorem B1611791 : Blo 1072617 1611791 := bstep (se 1 (by rfl) ⟨1208843, by rfl⟩ : syracuseStep 1611791 = 2417687) B2417687
theorem B1611833 : Blo 1072617 1611833 := bstep (se 2 (by rfl) ⟨604437, by rfl⟩ : syracuseStep 1611833 = 1208875) B1208875
theorem B16750709 : Blo 1072617 16750709 := bstep (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) B1570379
theorem B1611911 : Blo 1072617 1611911 := bstep (se 1 (by rfl) ⟨1208933, by rfl⟩ : syracuseStep 1611911 = 2417867) B2417867
theorem B1611947 : Blo 1072617 1611947 := bstep (se 1 (by rfl) ⟨1208960, by rfl⟩ : syracuseStep 1611947 = 2417921) B2417921
theorem B1611977 : Blo 1072617 1611977 := bstep (se 2 (by rfl) ⟨604491, by rfl⟩ : syracuseStep 1611977 = 1208983) B1208983
theorem B17406197 : Blo 1072617 17406197 := bstep (se 5 (by rfl) ⟨815915, by rfl⟩ : syracuseStep 17406197 = 1631831) B1631831
theorem B235411757 : Blo 1072617 235411757 := bstep (se 3 (by rfl) ⟨44139704, by rfl⟩ : syracuseStep 235411757 = 88279409) B88279409
theorem B1743163 : Blo 1072617 1743163 := bstep (se 1 (by rfl) ⟨1307372, by rfl⟩ : syracuseStep 1743163 = 2614745) B2614745
theorem B1612091 : Blo 1072617 1612091 := bstep (se 1 (by rfl) ⟨1209068, by rfl⟩ : syracuseStep 1612091 = 2418137) B2418137
theorem B6199667 : Blo 1072617 6199667 := bstep (se 1 (by rfl) ⟨4649750, by rfl⟩ : syracuseStep 6199667 = 9299501) B9299501
theorem B1612151 : Blo 1072617 1612151 := bstep (se 1 (by rfl) ⟨1209113, by rfl⟩ : syracuseStep 1612151 = 2418227) B2418227
theorem B89332109 : Blo 1072617 89332109 := bstep (se 3 (by rfl) ⟨16749770, by rfl⟩ : syracuseStep 89332109 = 33499541) B33499541
theorem B1612175 : Blo 1072617 1612175 := bstep (se 1 (by rfl) ⟨1209131, by rfl⟩ : syracuseStep 1612175 = 2418263) B2418263
theorem B4594067 : Blo 1072617 4594067 := bstep (se 1 (by rfl) ⟨3445550, by rfl⟩ : syracuseStep 4594067 = 6891101) B6891101
theorem B12261779 : Blo 1072617 12261779 := bstep (se 1 (by rfl) ⟨9196334, by rfl⟩ : syracuseStep 12261779 = 18392669) B18392669
theorem B1612217 : Blo 1072617 1612217 := bstep (se 2 (by rfl) ⟨604581, by rfl⟩ : syracuseStep 1612217 = 1209163) B1209163
theorem B10459601 : Blo 1072617 10459601 := bstep (se 2 (by rfl) ⟨3922350, by rfl⟩ : syracuseStep 10459601 = 7844701) B7844701
theorem B8264195 : Blo 1072617 8264195 := bstep (se 1 (by rfl) ⟨6198146, by rfl⟩ : syracuseStep 8264195 = 12396293) B12396293
theorem B1612295 : Blo 1072617 1612295 := bstep (se 1 (by rfl) ⟨1209221, by rfl⟩ : syracuseStep 1612295 = 2418443) B2418443
theorem B1612331 : Blo 1072617 1612331 := bstep (se 1 (by rfl) ⟨1209248, by rfl⟩ : syracuseStep 1612331 = 2418497) B2418497
theorem B1612361 : Blo 1072617 1612361 := bstep (se 2 (by rfl) ⟨604635, by rfl⟩ : syracuseStep 1612361 = 1209271) B1209271
theorem B11180663 : Blo 1072617 11180663 := bstep (se 1 (by rfl) ⟨8385497, by rfl⟩ : syracuseStep 11180663 = 16770995) B16770995
theorem B1612475 : Blo 1072617 1612475 := bstep (se 1 (by rfl) ⟨1209356, by rfl⟩ : syracuseStep 1612475 = 2418713) B2418713
theorem B5511881 : Blo 1072617 5511881 := bstep (se 2 (by rfl) ⟨2066955, by rfl⟩ : syracuseStep 5511881 = 4133911) B4133911
theorem B1612535 : Blo 1072617 1612535 := bstep (se 1 (by rfl) ⟨1209401, by rfl⟩ : syracuseStep 1612535 = 2418803) B2418803
theorem B1612559 : Blo 1072617 1612559 := bstep (se 1 (by rfl) ⟨1209419, by rfl⟩ : syracuseStep 1612559 = 2418839) B2418839
theorem B1612601 : Blo 1072617 1612601 := bstep (se 2 (by rfl) ⟨604725, by rfl⟩ : syracuseStep 1612601 = 1209451) B1209451
theorem B1612679 : Blo 1072617 1612679 := bstep (se 1 (by rfl) ⟨1209509, by rfl⟩ : syracuseStep 1612679 = 2419019) B2419019
theorem B1612715 : Blo 1072617 1612715 := bstep (se 1 (by rfl) ⟨1209536, by rfl⟩ : syracuseStep 1612715 = 2419073) B2419073
theorem B1612745 : Blo 1072617 1612745 := bstep (se 2 (by rfl) ⟨604779, by rfl⟩ : syracuseStep 1612745 = 1209559) B1209559
theorem B1612859 : Blo 1072617 1612859 := bstep (se 1 (by rfl) ⟨1209644, by rfl⟩ : syracuseStep 1612859 = 2419289) B2419289
theorem B1612919 : Blo 1072617 1612919 := bstep (se 1 (by rfl) ⟨1209689, by rfl⟩ : syracuseStep 1612919 = 2419379) B2419379
theorem B1612943 : Blo 1072617 1612943 := bstep (se 1 (by rfl) ⟨1209707, by rfl⟩ : syracuseStep 1612943 = 2419415) B2419415
theorem B1612985 : Blo 1072617 1612985 := bstep (se 2 (by rfl) ⟨604869, by rfl⟩ : syracuseStep 1612985 = 1209739) B1209739
theorem B1613063 : Blo 1072617 1613063 := bstep (se 1 (by rfl) ⟨1209797, by rfl⟩ : syracuseStep 1613063 = 2419595) B2419595
theorem B1613099 : Blo 1072617 1613099 := bstep (se 1 (by rfl) ⟨1209824, by rfl⟩ : syracuseStep 1613099 = 2419649) B2419649
theorem B1613129 : Blo 1072617 1613129 := bstep (se 2 (by rfl) ⟨604923, by rfl⟩ : syracuseStep 1613129 = 1209847) B1209847
theorem B1613243 : Blo 1072617 1613243 := bstep (se 1 (by rfl) ⟨1209932, by rfl⟩ : syracuseStep 1613243 = 2419865) B2419865
theorem B1613303 : Blo 1072617 1613303 := bstep (se 1 (by rfl) ⟨1209977, by rfl⟩ : syracuseStep 1613303 = 2419955) B2419955
theorem B1613327 : Blo 1072617 1613327 := bstep (se 1 (by rfl) ⟨1209995, by rfl⟩ : syracuseStep 1613327 = 2419991) B2419991
theorem B1613369 : Blo 1072617 1613369 := bstep (se 2 (by rfl) ⟨605013, by rfl⟩ : syracuseStep 1613369 = 1210027) B1210027
theorem B2039431 : Blo 1072617 2039431 := bstep (se 1 (by rfl) ⟨1529573, by rfl⟩ : syracuseStep 2039431 = 3059147) B3059147
theorem B1613447 : Blo 1072617 1613447 := bstep (se 1 (by rfl) ⟨1210085, by rfl⟩ : syracuseStep 1613447 = 2420171) B2420171
theorem B1613483 : Blo 1072617 1613483 := bstep (se 1 (by rfl) ⟨1210112, by rfl⟩ : syracuseStep 1613483 = 2420225) B2420225
theorem B8822465 : Blo 1072617 8822465 := bstep (se 2 (by rfl) ⟨3308424, by rfl⟩ : syracuseStep 8822465 = 6616849) B6616849
theorem B1613513 : Blo 1072617 1613513 := bstep (se 2 (by rfl) ⟨605067, by rfl⟩ : syracuseStep 1613513 = 1210135) B1210135
theorem B1449743 : Blo 1072617 1449743 := bstep (se 1 (by rfl) ⟨1087307, by rfl⟩ : syracuseStep 1449743 = 2174615) B2174615
theorem B1613627 : Blo 1072617 1613627 := bstep (se 1 (by rfl) ⟨1210220, by rfl⟩ : syracuseStep 1613627 = 2420441) B2420441
theorem B1810235 : Blo 1072617 1810235 := bstep (se 1 (by rfl) ⟨1357676, by rfl⟩ : syracuseStep 1810235 = 2715353) B2715353
theorem B3055421 : Blo 1072617 3055421 := bstep (se 3 (by rfl) ⟨572891, by rfl⟩ : syracuseStep 3055421 = 1145783) B1145783
theorem B1613687 : Blo 1072617 1613687 := bstep (se 1 (by rfl) ⟨1210265, by rfl⟩ : syracuseStep 1613687 = 2420531) B2420531
theorem B1613711 : Blo 1072617 1613711 := bstep (se 1 (by rfl) ⟨1210283, by rfl⟩ : syracuseStep 1613711 = 2420567) B2420567
theorem B1613753 : Blo 1072617 1613753 := bstep (se 2 (by rfl) ⟨605157, by rfl⟩ : syracuseStep 1613753 = 1210315) B1210315
theorem B1613831 : Blo 1072617 1613831 := bstep (se 1 (by rfl) ⟨1210373, by rfl⟩ : syracuseStep 1613831 = 2420747) B2420747
theorem B1613867 : Blo 1072617 1613867 := bstep (se 1 (by rfl) ⟨1210400, by rfl⟩ : syracuseStep 1613867 = 2420801) B2420801
theorem B1613897 : Blo 1072617 1613897 := bstep (se 2 (by rfl) ⟨605211, by rfl⟩ : syracuseStep 1613897 = 1210423) B1210423
theorem B1450171 : Blo 1072617 1450171 := bstep (se 1 (by rfl) ⟨1087628, by rfl⟩ : syracuseStep 1450171 = 2175257) B2175257
theorem B1614011 : Blo 1072617 1614011 := bstep (se 1 (by rfl) ⟨1210508, by rfl⟩ : syracuseStep 1614011 = 2421017) B2421017
theorem B1810633 : Blo 1072617 1810633 := bstep (se 2 (by rfl) ⟨678987, by rfl⟩ : syracuseStep 1810633 = 1357975) B1357975
theorem B1614071 : Blo 1072617 1614071 := bstep (se 1 (by rfl) ⟨1210553, by rfl⟩ : syracuseStep 1614071 = 2421107) B2421107
theorem B1614095 : Blo 1072617 1614095 := bstep (se 1 (by rfl) ⟨1210571, by rfl⟩ : syracuseStep 1614095 = 2421143) B2421143
theorem B1614137 : Blo 1072617 1614137 := bstep (se 2 (by rfl) ⟨605301, by rfl⟩ : syracuseStep 1614137 = 1210603) B1210603
theorem B1614215 : Blo 1072617 1614215 := bstep (se 1 (by rfl) ⟨1210661, by rfl⟩ : syracuseStep 1614215 = 2421323) B2421323
theorem B1614251 : Blo 1072617 1614251 := bstep (se 1 (by rfl) ⟨1210688, by rfl⟩ : syracuseStep 1614251 = 2421377) B2421377
theorem B1614281 : Blo 1072617 1614281 := bstep (se 2 (by rfl) ⟨605355, by rfl⟩ : syracuseStep 1614281 = 1210711) B1210711
theorem B3678749 : Blo 1072617 3678749 := bstep (se 3 (by rfl) ⟨689765, by rfl⟩ : syracuseStep 3678749 = 1379531) B1379531
theorem B5448221 : Blo 1072617 5448221 := bstep (se 3 (by rfl) ⟨1021541, by rfl⟩ : syracuseStep 5448221 = 2043083) B2043083
theorem B1614395 : Blo 1072617 1614395 := bstep (se 1 (by rfl) ⟨1210796, by rfl⟩ : syracuseStep 1614395 = 2421593) B2421593
theorem B1614455 : Blo 1072617 1614455 := bstep (se 1 (by rfl) ⟨1210841, by rfl⟩ : syracuseStep 1614455 = 2421683) B2421683
theorem B1614479 : Blo 1072617 1614479 := bstep (se 1 (by rfl) ⟨1210859, by rfl⟩ : syracuseStep 1614479 = 2421719) B2421719
theorem B1614521 : Blo 1072617 1614521 := bstep (se 2 (by rfl) ⟨605445, by rfl⟩ : syracuseStep 1614521 = 1210891) B1210891
theorem B5808833 : Blo 1072617 5808833 := bstep (se 2 (by rfl) ⟨2178312, by rfl⟩ : syracuseStep 5808833 = 4356625) B4356625
theorem B1614599 : Blo 1072617 1614599 := bstep (se 1 (by rfl) ⟨1210949, by rfl⟩ : syracuseStep 1614599 = 2421899) B2421899
theorem B3056413 : Blo 1072617 3056413 := bstep (se 3 (by rfl) ⟨573077, by rfl⟩ : syracuseStep 3056413 = 1146155) B1146155
theorem B6202145 : Blo 1072617 6202145 := bstep (se 2 (by rfl) ⟨2325804, by rfl⟩ : syracuseStep 6202145 = 4651609) B4651609
theorem B1614635 : Blo 1072617 1614635 := bstep (se 1 (by rfl) ⟨1210976, by rfl⟩ : syracuseStep 1614635 = 2421953) B2421953
theorem B1614665 : Blo 1072617 1614665 := bstep (se 2 (by rfl) ⟨605499, by rfl⟩ : syracuseStep 1614665 = 1210999) B1210999
theorem B1811335 : Blo 1072617 1811335 := bstep (se 1 (by rfl) ⟨1358501, by rfl⟩ : syracuseStep 1811335 = 2717003) B2717003
theorem B5809049 : Blo 1072617 5809049 := bstep (se 2 (by rfl) ⟨2178393, by rfl⟩ : syracuseStep 5809049 = 4356787) B4356787
theorem B1614779 : Blo 1072617 1614779 := bstep (se 1 (by rfl) ⟨1211084, by rfl⟩ : syracuseStep 1614779 = 2422169) B2422169
theorem B1614839 : Blo 1072617 1614839 := bstep (se 1 (by rfl) ⟨1211129, by rfl⟩ : syracuseStep 1614839 = 2422259) B2422259
theorem B5448707 : Blo 1072617 5448707 := bstep (se 1 (by rfl) ⟨4086530, by rfl⟩ : syracuseStep 5448707 = 8173061) B8173061
theorem B1614863 : Blo 1072617 1614863 := bstep (se 1 (by rfl) ⟨1211147, by rfl⟩ : syracuseStep 1614863 = 2422295) B2422295
theorem B1614905 : Blo 1072617 1614905 := bstep (se 2 (by rfl) ⟨605589, by rfl⟩ : syracuseStep 1614905 = 1211179) B1211179
theorem B6890669 : Blo 1072617 6890669 := bstep (se 3 (by rfl) ⟨1292000, by rfl⟩ : syracuseStep 6890669 = 2584001) B2584001
theorem B1451209 : Blo 1072617 1451209 := bstep (se 2 (by rfl) ⟨544203, by rfl⟩ : syracuseStep 1451209 = 1088407) B1088407
theorem B2041033 : Blo 1072617 2041033 := bstep (se 2 (by rfl) ⟨765387, by rfl⟩ : syracuseStep 2041033 = 1530775) B1530775
theorem B1811983 : Blo 1072617 1811983 := bstep (se 1 (by rfl) ⟨1358987, by rfl⟩ : syracuseStep 1811983 = 2717975) B2717975
theorem B13936157 : Blo 1072617 13936157 := bstep (se 3 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 13936157 = 5226059) B5226059
theorem B4597519 : Blo 1072617 4597519 := bstep (se 1 (by rfl) ⟨3448139, by rfl⟩ : syracuseStep 4597519 = 6896279) B6896279
theorem B1812523 : Blo 1072617 1812523 := bstep (se 1 (by rfl) ⟨1359392, by rfl⟩ : syracuseStep 1812523 = 2718785) B2718785
theorem B1747003 : Blo 1072617 1747003 := bstep (se 1 (by rfl) ⟨1310252, by rfl⟩ : syracuseStep 1747003 = 2620505) B2620505
theorem B4073591 : Blo 1072617 4073591 := bstep (se 1 (by rfl) ⟨3055193, by rfl⟩ : syracuseStep 4073591 = 6110387) B6110387
theorem B1812665 : Blo 1072617 1812665 := bstep (se 2 (by rfl) ⟨679749, by rfl⟩ : syracuseStep 1812665 = 1359499) B1359499
theorem B37234997 : Blo 1072617 37234997 := bstep (se 5 (by rfl) ⟨1745390, by rfl⟩ : syracuseStep 37234997 = 3490781) B3490781
theorem B1288747 : Blo 1072617 1288747 := bstep (se 1 (by rfl) ⟨966560, by rfl⟩ : syracuseStep 1288747 = 1933121) B1933121
theorem B5450327 : Blo 1072617 5450327 := bstep (se 1 (by rfl) ⟨4087745, by rfl⟩ : syracuseStep 5450327 = 8175491) B8175491
theorem B3058361 : Blo 1072617 3058361 := bstep (se 2 (by rfl) ⟨1146885, by rfl⟩ : syracuseStep 3058361 = 2293771) B2293771
theorem B1813367 : Blo 1072617 1813367 := bstep (se 1 (by rfl) ⟨1360025, by rfl⟩ : syracuseStep 1813367 = 2720051) B2720051
theorem B4074563 : Blo 1072617 4074563 := bstep (se 1 (by rfl) ⟨3055922, by rfl⟩ : syracuseStep 4074563 = 6111845) B6111845
theorem B1813819 : Blo 1072617 1813819 := bstep (se 1 (by rfl) ⟨1360364, by rfl⟩ : syracuseStep 1813819 = 2720729) B2720729
theorem B12234077 : Blo 1072617 12234077 := bstep (se 3 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 12234077 = 4587779) B4587779
theorem B1813961 : Blo 1072617 1813961 := bstep (se 2 (by rfl) ⟨680235, by rfl⟩ : syracuseStep 1813961 = 1360471) B1360471
theorem B4075019 : Blo 1072617 4075019 := bstep (se 1 (by rfl) ⟨3056264, by rfl⟩ : syracuseStep 4075019 = 6112529) B6112529
theorem B2043539 : Blo 1072617 2043539 := bstep (se 1 (by rfl) ⟨1532654, by rfl⟩ : syracuseStep 2043539 = 3065309) B3065309
theorem B26095283 : Blo 1072617 26095283 := bstep (se 1 (by rfl) ⟨19571462, by rfl⟩ : syracuseStep 26095283 = 39142925) B39142925
theorem B9678565 : Blo 1072617 9678565 := bstep (se 4 (by rfl) ⟨907365, by rfl⟩ : syracuseStep 9678565 = 1814731) B1814731
theorem B2043767 : Blo 1072617 2043767 := bstep (se 1 (by rfl) ⟨1532825, by rfl⟩ : syracuseStep 2043767 = 3065651) B3065651
theorem B6631303 : Blo 1072617 6631303 := bstep (se 1 (by rfl) ⟨4973477, by rfl⟩ : syracuseStep 6631303 = 9946955) B9946955
theorem B2174867 : Blo 1072617 2174867 := bstep (se 1 (by rfl) ⟨1631150, by rfl⟩ : syracuseStep 2174867 = 3262301) B3262301
theorem B3059603 : Blo 1072617 3059603 := bstep (se 1 (by rfl) ⟨2294702, by rfl⟩ : syracuseStep 3059603 = 4589405) B4589405
theorem B1814663 : Blo 1072617 1814663 := bstep (se 1 (by rfl) ⟨1360997, by rfl⟩ : syracuseStep 1814663 = 2721995) B2721995
theorem B5157101 : Blo 1072617 5157101 := bstep (se 3 (by rfl) ⟨966956, by rfl⟩ : syracuseStep 5157101 = 1933913) B1933913
theorem B5157179 : Blo 1072617 5157179 := bstep (se 1 (by rfl) ⟨3867884, by rfl⟩ : syracuseStep 5157179 = 7735769) B7735769
theorem B12235535 : Blo 1072617 12235535 := bstep (se 1 (by rfl) ⟨9176651, by rfl⟩ : syracuseStep 12235535 = 18353303) B18353303
theorem B1815311 : Blo 1072617 1815311 := bstep (se 1 (by rfl) ⟨1361483, by rfl⟩ : syracuseStep 1815311 = 2722967) B2722967
theorem B6370085 : Blo 1072617 6370085 := bstep (se 4 (by rfl) ⟨597195, by rfl⟩ : syracuseStep 6370085 = 1194391) B1194391
theorem B5813137 : Blo 1072617 5813137 := bstep (se 2 (by rfl) ⟨2179926, by rfl⟩ : syracuseStep 5813137 = 4359853) B4359853
theorem B5813201 : Blo 1072617 5813201 := bstep (se 2 (by rfl) ⟨2179950, by rfl⟩ : syracuseStep 5813201 = 4359901) B4359901
theorem B3061003 : Blo 1072617 3061003 := bstep (se 1 (by rfl) ⟨2295752, by rfl⟩ : syracuseStep 3061003 = 4591505) B4591505
theorem B1815851 : Blo 1072617 1815851 := bstep (se 1 (by rfl) ⟨1361888, by rfl⟩ : syracuseStep 1815851 = 2723777) B2723777
theorem B3061277 : Blo 1072617 3061277 := bstep (se 3 (by rfl) ⟨573989, by rfl⟩ : syracuseStep 3061277 = 1147979) B1147979
theorem B4077175 : Blo 1072617 4077175 := bstep (se 1 (by rfl) ⟨3057881, by rfl⟩ : syracuseStep 4077175 = 6115763) B6115763
theorem B1816249 : Blo 1072617 1816249 := bstep (se 2 (by rfl) ⟨681093, by rfl⟩ : syracuseStep 1816249 = 1362187) B1362187
theorem B6108929 : Blo 1072617 6108929 := bstep (se 2 (by rfl) ⟨2290848, by rfl⟩ : syracuseStep 6108929 = 4581697) B4581697
theorem B4896571 : Blo 1072617 4896571 := bstep (se 1 (by rfl) ⟨3672428, by rfl⟩ : syracuseStep 4896571 = 7344857) B7344857
theorem B7747645 : Blo 1072617 7747645 := bstep (se 3 (by rfl) ⟨1452683, by rfl⟩ : syracuseStep 7747645 = 2905367) B2905367
theorem B6895817 : Blo 1072617 6895817 := bstep (se 2 (by rfl) ⟨2585931, by rfl⟩ : syracuseStep 6895817 = 5171863) B5171863
theorem B1161487 : Blo 1072617 1161487 := bstep (se 1 (by rfl) ⟨871115, by rfl⟩ : syracuseStep 1161487 = 1742231) B1742231
theorem B8174033 : Blo 1072617 8174033 := bstep (se 2 (by rfl) ⟨3065262, by rfl⟩ : syracuseStep 8174033 = 6130525) B6130525
theorem B10336733 : Blo 1072617 10336733 := bstep (se 3 (by rfl) ⟨1938137, by rfl⟩ : syracuseStep 10336733 = 3876275) B3876275
theorem B4078147 : Blo 1072617 4078147 := bstep (se 1 (by rfl) ⟨3058610, by rfl⟩ : syracuseStep 4078147 = 6117221) B6117221
theorem B1358471 : Blo 1072617 1358471 := bstep (se 1 (by rfl) ⟨1018853, by rfl⟩ : syracuseStep 1358471 = 2037707) B2037707
theorem B4078451 : Blo 1072617 4078451 := bstep (se 1 (by rfl) ⟨3058838, by rfl⟩ : syracuseStep 4078451 = 6117677) B6117677
theorem B4537241 : Blo 1072617 4537241 := bstep (se 2 (by rfl) ⟨1701465, by rfl⟩ : syracuseStep 4537241 = 3402931) B3402931
theorem B1359119 : Blo 1072617 1359119 := bstep (se 1 (by rfl) ⟨1019339, by rfl⟩ : syracuseStep 1359119 = 2038679) B2038679
theorem B4078907 : Blo 1072617 4078907 := bstep (se 1 (by rfl) ⟨3059180, by rfl⟩ : syracuseStep 4078907 = 6118361) B6118361
theorem B9191141 : Blo 1072617 9191141 := bstep (se 4 (by rfl) ⟨861669, by rfl⟩ : syracuseStep 9191141 = 1723339) B1723339
theorem B4079393 : Blo 1072617 4079393 := bstep (se 2 (by rfl) ⟨1529772, by rfl⟩ : syracuseStep 4079393 = 3059545) B3059545
theorem B104677271 : Blo 1072617 104677271 := bstep (se 1 (by rfl) ⟨78507953, by rfl⟩ : syracuseStep 104677271 = 157015907) B157015907
theorem B3063737 : Blo 1072617 3063737 := bstep (se 2 (by rfl) ⟨1148901, by rfl⟩ : syracuseStep 3063737 = 2297803) B2297803
theorem B3063851 : Blo 1072617 3063851 := bstep (se 1 (by rfl) ⟨2297888, by rfl⟩ : syracuseStep 3063851 = 4595777) B4595777
theorem B2900083 : Blo 1072617 2900083 := bstep (se 1 (by rfl) ⟨2175062, by rfl⟩ : syracuseStep 2900083 = 4350125) B4350125
theorem B9191825 : Blo 1072617 9191825 := bstep (se 2 (by rfl) ⟨3446934, by rfl⟩ : syracuseStep 9191825 = 6893869) B6893869
theorem B11616797 : Blo 1072617 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B4080365 : Blo 1072617 4080365 := bstep (se 3 (by rfl) ⟨765068, by rfl⟩ : syracuseStep 4080365 = 1530137) B1530137
theorem B4899599 : Blo 1072617 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B3621779 : Blo 1072617 3621779 := bstep (se 1 (by rfl) ⟨2716334, by rfl⟩ : syracuseStep 3621779 = 5432669) B5432669
theorem B7357387 : Blo 1072617 7357387 := bstep (se 1 (by rfl) ⟨5518040, by rfl⟩ : syracuseStep 7357387 = 11036081) B11036081
theorem B3064979 : Blo 1072617 3064979 := bstep (se 1 (by rfl) ⟨2298734, by rfl⟩ : syracuseStep 3064979 = 4597469) B4597469
theorem B9192851 : Blo 1072617 9192851 := bstep (se 1 (by rfl) ⟨6894638, by rfl⟩ : syracuseStep 9192851 = 13789277) B13789277
theorem B4081049 : Blo 1072617 4081049 := bstep (se 2 (by rfl) ⟨1530393, by rfl⟩ : syracuseStep 4081049 = 3060787) B3060787
theorem B3065377 : Blo 1072617 3065377 := bstep (se 2 (by rfl) ⟨1149516, by rfl⟩ : syracuseStep 3065377 = 2299033) B2299033
theorem B1492871 : Blo 1072617 1492871 := bstep (se 1 (by rfl) ⟨1119653, by rfl⟩ : syracuseStep 1492871 = 2239307) B2239307
theorem B3262409 : Blo 1072617 3262409 := bstep (se 2 (by rfl) ⟨1223403, by rfl⟩ : syracuseStep 3262409 = 2446807) B2446807
theorem B6113303 : Blo 1072617 6113303 := bstep (se 1 (by rfl) ⟨4584977, by rfl⟩ : syracuseStep 6113303 = 9169955) B9169955
theorem B1362091 : Blo 1072617 1362091 := bstep (se 1 (by rfl) ⟨1021568, by rfl⟩ : syracuseStep 1362091 = 2043137) B2043137
theorem B3623183 : Blo 1072617 3623183 := bstep (se 1 (by rfl) ⟨2717387, by rfl⟩ : syracuseStep 3623183 = 5434775) B5434775
theorem B6539609 : Blo 1072617 6539609 := bstep (se 2 (by rfl) ⟨2452353, by rfl⟩ : syracuseStep 6539609 = 4904707) B4904707
theorem B4082035 : Blo 1072617 4082035 := bstep (se 1 (by rfl) ⟨3061526, by rfl⟩ : syracuseStep 4082035 = 6123053) B6123053
theorem B3623453 : Blo 1072617 3623453 := bstep (se 3 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 3623453 = 1358795) B1358795
theorem B5163713 : Blo 1072617 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B3099593 : Blo 1072617 3099593 := bstep (se 2 (by rfl) ⟨1162347, by rfl⟩ : syracuseStep 3099593 = 2324695) B2324695
theorem B5524567 : Blo 1072617 5524567 := bstep (se 1 (by rfl) ⟨4143425, by rfl⟩ : syracuseStep 5524567 = 8286851) B8286851
theorem B11193785 : Blo 1072617 11193785 := bstep (se 2 (by rfl) ⟨4197669, by rfl⟩ : syracuseStep 11193785 = 8395339) B8395339
theorem B48385637 : Blo 1072617 48385637 := bstep (se 4 (by rfl) ⟨4536153, by rfl⟩ : syracuseStep 48385637 = 9072307) B9072307
theorem B3624857 : Blo 1072617 3624857 := bstep (se 2 (by rfl) ⟨1359321, by rfl⟩ : syracuseStep 3624857 = 2718643) B2718643
theorem B1527979 : Blo 1072617 1527979 := bstep (se 1 (by rfl) ⟨1145984, by rfl⟩ : syracuseStep 1527979 = 2291969) B2291969
theorem B2904439 : Blo 1072617 2904439 := bstep (se 1 (by rfl) ⟨2178329, by rfl⟩ : syracuseStep 2904439 = 4356659) B4356659
theorem B4084253 : Blo 1072617 4084253 := bstep (se 3 (by rfl) ⟨765797, by rfl⟩ : syracuseStep 4084253 = 1531595) B1531595
theorem B3265085 : Blo 1072617 3265085 := bstep (se 3 (by rfl) ⟨612203, by rfl⟩ : syracuseStep 3265085 = 1224407) B1224407
theorem B3625559 : Blo 1072617 3625559 := bstep (se 1 (by rfl) ⟨2719169, by rfl⟩ : syracuseStep 3625559 = 5438339) B5438339
theorem B2904893 : Blo 1072617 2904893 := bstep (se 3 (by rfl) ⟨544667, by rfl⟩ : syracuseStep 2904893 = 1089335) B1089335
theorem B6968267 : Blo 1072617 6968267 := bstep (se 1 (by rfl) ⟨5226200, by rfl⟩ : syracuseStep 6968267 = 10452401) B10452401
theorem B2413583 : Blo 1072617 2413583 := bstep (se 1 (by rfl) ⟨1810187, by rfl⟩ : syracuseStep 2413583 = 3620375) B3620375
theorem B2413601 : Blo 1072617 2413601 := bstep (se 2 (by rfl) ⟨905100, by rfl⟩ : syracuseStep 2413601 = 1810201) B1810201
theorem B3626045 : Blo 1072617 3626045 := bstep (se 3 (by rfl) ⟨679883, by rfl⟩ : syracuseStep 3626045 = 1359767) B1359767
theorem B6116471 : Blo 1072617 6116471 := bstep (se 1 (by rfl) ⟨4587353, by rfl⟩ : syracuseStep 6116471 = 9174707) B9174707
theorem B4084937 : Blo 1072617 4084937 := bstep (se 2 (by rfl) ⟨1531851, by rfl⟩ : syracuseStep 4084937 = 3063703) B3063703
theorem B12244283 : Blo 1072617 12244283 := bstep (se 1 (by rfl) ⟨9183212, by rfl⟩ : syracuseStep 12244283 = 18366425) B18366425
theorem B2413943 : Blo 1072617 2413943 := bstep (se 1 (by rfl) ⟨1810457, by rfl⟩ : syracuseStep 2413943 = 3620915) B3620915
theorem B2414123 : Blo 1072617 2414123 := bstep (se 1 (by rfl) ⟨1810592, by rfl⟩ : syracuseStep 2414123 = 3621185) B3621185
theorem B1529545 : Blo 1072617 1529545 := bstep (se 2 (by rfl) ⟨573579, by rfl⟩ : syracuseStep 1529545 = 1147159) B1147159
theorem B2414483 : Blo 1072617 2414483 := bstep (se 1 (by rfl) ⟨1810862, by rfl⟩ : syracuseStep 2414483 = 3621725) B3621725
theorem B2414537 : Blo 1072617 2414537 := bstep (se 2 (by rfl) ⟨905451, by rfl⟩ : syracuseStep 2414537 = 1810903) B1810903
theorem B1530103 : Blo 1072617 1530103 := bstep (se 1 (by rfl) ⟨1147577, by rfl⟩ : syracuseStep 1530103 = 2295155) B2295155
theorem B9066937 : Blo 1072617 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B3627449 : Blo 1072617 3627449 := bstep (se 2 (by rfl) ⟨1360293, by rfl⟩ : syracuseStep 3627449 = 2720587) B2720587
theorem B2415239 : Blo 1072617 2415239 := bstep (se 1 (by rfl) ⟨1811429, by rfl⟩ : syracuseStep 2415239 = 3622859) B3622859
theorem B8149733 : Blo 1072617 8149733 := bstep (se 4 (by rfl) ⟨764037, by rfl⟩ : syracuseStep 8149733 = 1528075) B1528075
theorem B13982501 : Blo 1072617 13982501 := bstep (se 4 (by rfl) ⟨1310859, by rfl⟩ : syracuseStep 13982501 = 2621719) B2621719
theorem B1530667 : Blo 1072617 1530667 := bstep (se 1 (by rfl) ⟨1148000, by rfl⟩ : syracuseStep 1530667 = 2296001) B2296001
theorem B2415419 : Blo 1072617 2415419 := bstep (se 1 (by rfl) ⟨1811564, by rfl⟩ : syracuseStep 2415419 = 3623129) B3623129
theorem B2415545 : Blo 1072617 2415545 := bstep (se 2 (by rfl) ⟨905829, by rfl⟩ : syracuseStep 2415545 = 1811659) B1811659
theorem B4086713 : Blo 1072617 4086713 := bstep (se 2 (by rfl) ⟨1532517, by rfl⟩ : syracuseStep 4086713 = 3065035) B3065035
theorem B12409861 : Blo 1072617 12409861 := bstep (se 4 (by rfl) ⟨1163424, by rfl⟩ : syracuseStep 12409861 = 2326849) B2326849
theorem B3628043 : Blo 1072617 3628043 := bstep (se 1 (by rfl) ⟨2721032, by rfl⟩ : syracuseStep 3628043 = 5442065) B5442065
theorem B1530895 : Blo 1072617 1530895 := bstep (se 1 (by rfl) ⟨1148171, by rfl⟩ : syracuseStep 1530895 = 2296343) B2296343
theorem B3628151 : Blo 1072617 3628151 := bstep (se 1 (by rfl) ⟨2721113, by rfl⟩ : syracuseStep 3628151 = 5442227) B5442227
theorem B39214277 : Blo 1072617 39214277 := bstep (se 4 (by rfl) ⟨3676338, by rfl⟩ : syracuseStep 39214277 = 7352677) B7352677
theorem B2415887 : Blo 1072617 2415887 := bstep (se 1 (by rfl) ⟨1811915, by rfl⟩ : syracuseStep 2415887 = 3623831) B3623831
theorem B2415905 : Blo 1072617 2415905 := bstep (se 2 (by rfl) ⟨905964, by rfl⟩ : syracuseStep 2415905 = 1811929) B1811929
theorem B3267955 : Blo 1072617 3267955 := bstep (se 1 (by rfl) ⟨2450966, by rfl⟩ : syracuseStep 3267955 = 4901933) B4901933
theorem B5168519 : Blo 1072617 5168519 := bstep (se 1 (by rfl) ⟨3876389, by rfl⟩ : syracuseStep 5168519 = 7752779) B7752779
theorem B8707537 : Blo 1072617 8707537 := bstep (se 2 (by rfl) ⟨3265326, by rfl⟩ : syracuseStep 8707537 = 6530653) B6530653
theorem B17456593 : Blo 1072617 17456593 := bstep (se 2 (by rfl) ⟨6546222, by rfl⟩ : syracuseStep 17456593 = 13092445) B13092445
theorem B1072647 : Blo 1072617 1072647 := bstep (se 1 (by rfl) ⟨804485, by rfl⟩ : syracuseStep 1072647 = 1608971) B1608971
theorem B1072655 : Blo 1072617 1072655 := bstep (se 1 (by rfl) ⟨804491, by rfl⟩ : syracuseStep 1072655 = 1608983) B1608983
theorem B1072699 : Blo 1072617 1072699 := bstep (se 1 (by rfl) ⟨804524, by rfl⟩ : syracuseStep 1072699 = 1609049) B1609049
theorem B2416247 : Blo 1072617 2416247 := bstep (se 1 (by rfl) ⟨1812185, by rfl⟩ : syracuseStep 2416247 = 3624371) B3624371
theorem B1072775 : Blo 1072617 1072775 := bstep (se 1 (by rfl) ⟨804581, by rfl⟩ : syracuseStep 1072775 = 1609163) B1609163
theorem B1072783 : Blo 1072617 1072783 := bstep (se 1 (by rfl) ⟨804587, by rfl⟩ : syracuseStep 1072783 = 1609175) B1609175
theorem B1072827 : Blo 1072617 1072827 := bstep (se 1 (by rfl) ⟨804620, by rfl⟩ : syracuseStep 1072827 = 1609241) B1609241
theorem B3628745 : Blo 1072617 3628745 := bstep (se 2 (by rfl) ⟨1360779, by rfl⟩ : syracuseStep 3628745 = 2721559) B2721559
theorem B1072903 : Blo 1072617 1072903 := bstep (se 1 (by rfl) ⟨804677, by rfl⟩ : syracuseStep 1072903 = 1609355) B1609355
theorem B1072911 : Blo 1072617 1072911 := bstep (se 1 (by rfl) ⟨804683, by rfl⟩ : syracuseStep 1072911 = 1609367) B1609367
theorem B9166607 : Blo 1072617 9166607 := bstep (se 1 (by rfl) ⟨6874955, by rfl⟩ : syracuseStep 9166607 = 13749911) B13749911
theorem B2416427 : Blo 1072617 2416427 := bstep (se 1 (by rfl) ⟨1812320, by rfl⟩ : syracuseStep 2416427 = 3624641) B3624641
theorem B1072955 : Blo 1072617 1072955 := bstep (se 1 (by rfl) ⟨804716, by rfl⟩ : syracuseStep 1072955 = 1609433) B1609433
theorem B2580311 : Blo 1072617 2580311 := bstep (se 1 (by rfl) ⟨1935233, by rfl⟩ : syracuseStep 2580311 = 3870467) B3870467
theorem B1073031 : Blo 1072617 1073031 := bstep (se 1 (by rfl) ⟨804773, by rfl⟩ : syracuseStep 1073031 = 1609547) B1609547
theorem B1073039 : Blo 1072617 1073039 := bstep (se 1 (by rfl) ⟨804779, by rfl⟩ : syracuseStep 1073039 = 1609559) B1609559
theorem B1073083 : Blo 1072617 1073083 := bstep (se 1 (by rfl) ⟨804812, by rfl⟩ : syracuseStep 1073083 = 1609625) B1609625
theorem B1073159 : Blo 1072617 1073159 := bstep (se 1 (by rfl) ⟨804869, by rfl⟩ : syracuseStep 1073159 = 1609739) B1609739
theorem B1073167 : Blo 1072617 1073167 := bstep (se 1 (by rfl) ⟨804875, by rfl⟩ : syracuseStep 1073167 = 1609751) B1609751
theorem B1073211 : Blo 1072617 1073211 := bstep (se 1 (by rfl) ⟨804908, by rfl⟩ : syracuseStep 1073211 = 1609817) B1609817
theorem B1073287 : Blo 1072617 1073287 := bstep (se 1 (by rfl) ⟨804965, by rfl⟩ : syracuseStep 1073287 = 1609931) B1609931
theorem B1532039 : Blo 1072617 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B1073295 : Blo 1072617 1073295 := bstep (se 1 (by rfl) ⟨804971, by rfl⟩ : syracuseStep 1073295 = 1609943) B1609943
theorem B2416787 : Blo 1072617 2416787 := bstep (se 1 (by rfl) ⟨1812590, by rfl⟩ : syracuseStep 2416787 = 3625181) B3625181
theorem B1073339 : Blo 1072617 1073339 := bstep (se 1 (by rfl) ⟨805004, by rfl⟩ : syracuseStep 1073339 = 1610009) B1610009
theorem B2416841 : Blo 1072617 2416841 := bstep (se 2 (by rfl) ⟨906315, by rfl⟩ : syracuseStep 2416841 = 1812631) B1812631
theorem B1073415 : Blo 1072617 1073415 := bstep (se 1 (by rfl) ⟨805061, by rfl⟩ : syracuseStep 1073415 = 1610123) B1610123
theorem B1073423 : Blo 1072617 1073423 := bstep (se 1 (by rfl) ⟨805067, by rfl⟩ : syracuseStep 1073423 = 1610135) B1610135
theorem B1073467 : Blo 1072617 1073467 := bstep (se 1 (by rfl) ⟨805100, by rfl⟩ : syracuseStep 1073467 = 1610201) B1610201
theorem B1532233 : Blo 1072617 1532233 := bstep (se 2 (by rfl) ⟨574587, by rfl⟩ : syracuseStep 1532233 = 1149175) B1149175
theorem B1073543 : Blo 1072617 1073543 := bstep (se 1 (by rfl) ⟨805157, by rfl⟩ : syracuseStep 1073543 = 1610315) B1610315
theorem B3629447 : Blo 1072617 3629447 := bstep (se 1 (by rfl) ⟨2722085, by rfl⟩ : syracuseStep 3629447 = 5444171) B5444171
theorem B1073551 : Blo 1072617 1073551 := bstep (se 1 (by rfl) ⟨805163, by rfl⟩ : syracuseStep 1073551 = 1610327) B1610327
theorem B5431697 : Blo 1072617 5431697 := bstep (se 2 (by rfl) ⟨2036886, by rfl⟩ : syracuseStep 5431697 = 4073773) B4073773
theorem B1073595 : Blo 1072617 1073595 := bstep (se 1 (by rfl) ⟨805196, by rfl⟩ : syracuseStep 1073595 = 1610393) B1610393
theorem B1073671 : Blo 1072617 1073671 := bstep (se 1 (by rfl) ⟨805253, by rfl⟩ : syracuseStep 1073671 = 1610507) B1610507
theorem B6382091 : Blo 1072617 6382091 := bstep (se 1 (by rfl) ⟨4786568, by rfl⟩ : syracuseStep 6382091 = 9573137) B9573137
theorem B1073679 : Blo 1072617 1073679 := bstep (se 1 (by rfl) ⟨805259, by rfl⟩ : syracuseStep 1073679 = 1610519) B1610519
theorem B1073723 : Blo 1072617 1073723 := bstep (se 1 (by rfl) ⟨805292, by rfl⟩ : syracuseStep 1073723 = 1610585) B1610585
theorem B1073799 : Blo 1072617 1073799 := bstep (se 1 (by rfl) ⟨805349, by rfl⟩ : syracuseStep 1073799 = 1610699) B1610699
theorem B1073807 : Blo 1072617 1073807 := bstep (se 1 (by rfl) ⟨805355, by rfl⟩ : syracuseStep 1073807 = 1610711) B1610711
theorem B1073851 : Blo 1072617 1073851 := bstep (se 1 (by rfl) ⟨805388, by rfl⟩ : syracuseStep 1073851 = 1610777) B1610777
theorem B6120137 : Blo 1072617 6120137 := bstep (se 2 (by rfl) ⟨2295051, by rfl⟩ : syracuseStep 6120137 = 4590103) B4590103
theorem B19620569 : Blo 1072617 19620569 := bstep (se 2 (by rfl) ⟨7357713, by rfl⟩ : syracuseStep 19620569 = 14715427) B14715427
theorem B3629825 : Blo 1072617 3629825 := bstep (se 2 (by rfl) ⟨1361184, by rfl⟩ : syracuseStep 3629825 = 2722369) B2722369
theorem B1073927 : Blo 1072617 1073927 := bstep (se 1 (by rfl) ⟨805445, by rfl⟩ : syracuseStep 1073927 = 1610891) B1610891
theorem B1073935 : Blo 1072617 1073935 := bstep (se 1 (by rfl) ⟨805451, by rfl⟩ : syracuseStep 1073935 = 1610903) B1610903
theorem B13787941 : Blo 1072617 13787941 := bstep (se 4 (by rfl) ⟨1292619, by rfl⟩ : syracuseStep 13787941 = 2585239) B2585239
theorem B1073979 : Blo 1072617 1073979 := bstep (se 1 (by rfl) ⟨805484, by rfl⟩ : syracuseStep 1073979 = 1610969) B1610969
theorem B1532791 : Blo 1072617 1532791 := bstep (se 1 (by rfl) ⟨1149593, by rfl⟩ : syracuseStep 1532791 = 2299187) B2299187
theorem B1074055 : Blo 1072617 1074055 := bstep (se 1 (by rfl) ⟨805541, by rfl⟩ : syracuseStep 1074055 = 1611083) B1611083
theorem B2417543 : Blo 1072617 2417543 := bstep (se 1 (by rfl) ⟨1813157, by rfl⟩ : syracuseStep 2417543 = 3626315) B3626315
theorem B1074063 : Blo 1072617 1074063 := bstep (se 1 (by rfl) ⟨805547, by rfl⟩ : syracuseStep 1074063 = 1611095) B1611095
theorem B1074107 : Blo 1072617 1074107 := bstep (se 1 (by rfl) ⟨805580, by rfl⟩ : syracuseStep 1074107 = 1611161) B1611161
theorem B1074183 : Blo 1072617 1074183 := bstep (se 1 (by rfl) ⟨805637, by rfl⟩ : syracuseStep 1074183 = 1611275) B1611275
theorem B1074191 : Blo 1072617 1074191 := bstep (se 1 (by rfl) ⟨805643, by rfl⟩ : syracuseStep 1074191 = 1611287) B1611287
theorem B1074235 : Blo 1072617 1074235 := bstep (se 1 (by rfl) ⟨805676, by rfl⟩ : syracuseStep 1074235 = 1611353) B1611353
theorem B2417723 : Blo 1072617 2417723 := bstep (se 1 (by rfl) ⟨1813292, by rfl⟩ : syracuseStep 2417723 = 3626585) B3626585
theorem B1074311 : Blo 1072617 1074311 := bstep (se 1 (by rfl) ⟨805733, by rfl⟩ : syracuseStep 1074311 = 1611467) B1611467
theorem B1074319 : Blo 1072617 1074319 := bstep (se 1 (by rfl) ⟨805739, by rfl⟩ : syracuseStep 1074319 = 1611479) B1611479
theorem B2417849 : Blo 1072617 2417849 := bstep (se 2 (by rfl) ⟨906693, by rfl⟩ : syracuseStep 2417849 = 1813387) B1813387
theorem B1074363 : Blo 1072617 1074363 := bstep (se 1 (by rfl) ⟨805772, by rfl⟩ : syracuseStep 1074363 = 1611545) B1611545
theorem B1074439 : Blo 1072617 1074439 := bstep (se 1 (by rfl) ⟨805829, by rfl⟩ : syracuseStep 1074439 = 1611659) B1611659
theorem B1074447 : Blo 1072617 1074447 := bstep (se 1 (by rfl) ⟨805835, by rfl⟩ : syracuseStep 1074447 = 1611671) B1611671
theorem B1074491 : Blo 1072617 1074491 := bstep (se 1 (by rfl) ⟨805868, by rfl⟩ : syracuseStep 1074491 = 1611737) B1611737
theorem B1074567 : Blo 1072617 1074567 := bstep (se 1 (by rfl) ⟨805925, by rfl⟩ : syracuseStep 1074567 = 1611851) B1611851
theorem B1074575 : Blo 1072617 1074575 := bstep (se 1 (by rfl) ⟨805931, by rfl⟩ : syracuseStep 1074575 = 1611863) B1611863
theorem B6284729 : Blo 1072617 6284729 := bstep (se 2 (by rfl) ⟨2356773, by rfl⟩ : syracuseStep 6284729 = 4713547) B4713547
theorem B1074619 : Blo 1072617 1074619 := bstep (se 1 (by rfl) ⟨805964, by rfl⟩ : syracuseStep 1074619 = 1611929) B1611929
theorem B1074695 : Blo 1072617 1074695 := bstep (se 1 (by rfl) ⟨806021, by rfl⟩ : syracuseStep 1074695 = 1612043) B1612043
theorem B1074703 : Blo 1072617 1074703 := bstep (se 1 (by rfl) ⟨806027, by rfl⟩ : syracuseStep 1074703 = 1612055) B1612055
theorem B2418191 : Blo 1072617 2418191 := bstep (se 1 (by rfl) ⟨1813643, by rfl⟩ : syracuseStep 2418191 = 3627287) B3627287
theorem B2418209 : Blo 1072617 2418209 := bstep (se 2 (by rfl) ⟨906828, by rfl⟩ : syracuseStep 2418209 = 1813657) B1813657
theorem B3630635 : Blo 1072617 3630635 := bstep (se 1 (by rfl) ⟨2722976, by rfl⟩ : syracuseStep 3630635 = 5445953) B5445953
theorem B1074747 : Blo 1072617 1074747 := bstep (se 1 (by rfl) ⟨806060, by rfl⟩ : syracuseStep 1074747 = 1612121) B1612121
theorem B1074823 : Blo 1072617 1074823 := bstep (se 1 (by rfl) ⟨806117, by rfl⟩ : syracuseStep 1074823 = 1612235) B1612235
theorem B1074831 : Blo 1072617 1074831 := bstep (se 1 (by rfl) ⟨806123, by rfl⟩ : syracuseStep 1074831 = 1612247) B1612247
theorem B6612653 : Blo 1072617 6612653 := bstep (se 3 (by rfl) ⟨1239872, by rfl⟩ : syracuseStep 6612653 = 2479745) B2479745
theorem B1074875 : Blo 1072617 1074875 := bstep (se 1 (by rfl) ⟨806156, by rfl⟩ : syracuseStep 1074875 = 1612313) B1612313
theorem B1074951 : Blo 1072617 1074951 := bstep (se 1 (by rfl) ⟨806213, by rfl⟩ : syracuseStep 1074951 = 1612427) B1612427
theorem B1074959 : Blo 1072617 1074959 := bstep (se 1 (by rfl) ⟨806219, by rfl⟩ : syracuseStep 1074959 = 1612439) B1612439
theorem B1075003 : Blo 1072617 1075003 := bstep (se 1 (by rfl) ⟨806252, by rfl⟩ : syracuseStep 1075003 = 1612505) B1612505
theorem B2582387 : Blo 1072617 2582387 := bstep (se 1 (by rfl) ⟨1936790, by rfl⟩ : syracuseStep 2582387 = 3873581) B3873581
theorem B2418551 : Blo 1072617 2418551 := bstep (se 1 (by rfl) ⟨1813913, by rfl⟩ : syracuseStep 2418551 = 3627827) B3627827
theorem B1075079 : Blo 1072617 1075079 := bstep (se 1 (by rfl) ⟨806309, by rfl⟩ : syracuseStep 1075079 = 1612619) B1612619
theorem B1075087 : Blo 1072617 1075087 := bstep (se 1 (by rfl) ⟨806315, by rfl⟩ : syracuseStep 1075087 = 1612631) B1612631
theorem B1075131 : Blo 1072617 1075131 := bstep (se 1 (by rfl) ⟨806348, by rfl⟩ : syracuseStep 1075131 = 1612697) B1612697
theorem B1075207 : Blo 1072617 1075207 := bstep (se 1 (by rfl) ⟨806405, by rfl⟩ : syracuseStep 1075207 = 1612811) B1612811
theorem B1075215 : Blo 1072617 1075215 := bstep (se 1 (by rfl) ⟨806411, by rfl⟩ : syracuseStep 1075215 = 1612823) B1612823
theorem B2418731 : Blo 1072617 2418731 := bstep (se 1 (by rfl) ⟨1814048, by rfl⟩ : syracuseStep 2418731 = 3628097) B3628097
theorem B1075259 : Blo 1072617 1075259 := bstep (se 1 (by rfl) ⟨806444, by rfl⟩ : syracuseStep 1075259 = 1612889) B1612889
theorem B1075335 : Blo 1072617 1075335 := bstep (se 1 (by rfl) ⟨806501, by rfl⟩ : syracuseStep 1075335 = 1613003) B1613003
theorem B1075343 : Blo 1072617 1075343 := bstep (se 1 (by rfl) ⟨806507, by rfl⟩ : syracuseStep 1075343 = 1613015) B1613015
theorem B1075387 : Blo 1072617 1075387 := bstep (se 1 (by rfl) ⟨806540, by rfl⟩ : syracuseStep 1075387 = 1613081) B1613081
theorem B5171401 : Blo 1072617 5171401 := bstep (se 2 (by rfl) ⟨1939275, by rfl⟩ : syracuseStep 5171401 = 3878551) B3878551
theorem B1075463 : Blo 1072617 1075463 := bstep (se 1 (by rfl) ⟨806597, by rfl⟩ : syracuseStep 1075463 = 1613195) B1613195
theorem B1075471 : Blo 1072617 1075471 := bstep (se 1 (by rfl) ⟨806603, by rfl⟩ : syracuseStep 1075471 = 1613207) B1613207
theorem B1075515 : Blo 1072617 1075515 := bstep (se 1 (by rfl) ⟨806636, by rfl⟩ : syracuseStep 1075515 = 1613273) B1613273
theorem B3270971 : Blo 1072617 3270971 := bstep (se 1 (by rfl) ⟨2453228, by rfl⟩ : syracuseStep 3270971 = 4906457) B4906457
theorem B1075591 : Blo 1072617 1075591 := bstep (se 1 (by rfl) ⟨806693, by rfl⟩ : syracuseStep 1075591 = 1613387) B1613387
theorem B1075599 : Blo 1072617 1075599 := bstep (se 1 (by rfl) ⟨806699, by rfl⟩ : syracuseStep 1075599 = 1613399) B1613399
theorem B2419091 : Blo 1072617 2419091 := bstep (se 1 (by rfl) ⟨1814318, by rfl⟩ : syracuseStep 2419091 = 3628637) B3628637
theorem B1206715 : Blo 1072617 1206715 := bstep (se 1 (by rfl) ⟨905036, by rfl⟩ : syracuseStep 1206715 = 1810073) B1810073
theorem B1075643 : Blo 1072617 1075643 := bstep (se 1 (by rfl) ⟨806732, by rfl⟩ : syracuseStep 1075643 = 1613465) B1613465
theorem B2615753 : Blo 1072617 2615753 := bstep (se 2 (by rfl) ⟨980907, by rfl⟩ : syracuseStep 2615753 = 1961815) B1961815
theorem B2419145 : Blo 1072617 2419145 := bstep (se 2 (by rfl) ⟨907179, by rfl⟩ : syracuseStep 2419145 = 1814359) B1814359
theorem B5433803 : Blo 1072617 5433803 := bstep (se 1 (by rfl) ⟨4075352, by rfl⟩ : syracuseStep 5433803 = 8150705) B8150705
theorem B1075719 : Blo 1072617 1075719 := bstep (se 1 (by rfl) ⟨806789, by rfl⟩ : syracuseStep 1075719 = 1613579) B1613579
theorem B1075727 : Blo 1072617 1075727 := bstep (se 1 (by rfl) ⟨806795, by rfl⟩ : syracuseStep 1075727 = 1613591) B1613591
theorem B1075771 : Blo 1072617 1075771 := bstep (se 1 (by rfl) ⟨806828, by rfl⟩ : syracuseStep 1075771 = 1613657) B1613657
theorem B6122051 : Blo 1072617 6122051 := bstep (se 1 (by rfl) ⟨4591538, by rfl⟩ : syracuseStep 6122051 = 9183077) B9183077
theorem B1075847 : Blo 1072617 1075847 := bstep (se 1 (by rfl) ⟨806885, by rfl⟩ : syracuseStep 1075847 = 1613771) B1613771
theorem B1075855 : Blo 1072617 1075855 := bstep (se 1 (by rfl) ⟨806891, by rfl⟩ : syracuseStep 1075855 = 1613783) B1613783
theorem B1075899 : Blo 1072617 1075899 := bstep (se 1 (by rfl) ⟨806924, by rfl⟩ : syracuseStep 1075899 = 1613849) B1613849
theorem B1075975 : Blo 1072617 1075975 := bstep (se 1 (by rfl) ⟨806981, by rfl⟩ : syracuseStep 1075975 = 1613963) B1613963
theorem B5434127 : Blo 1072617 5434127 := bstep (se 1 (by rfl) ⟨4075595, by rfl⟩ : syracuseStep 5434127 = 8151191) B8151191
theorem B1075983 : Blo 1072617 1075983 := bstep (se 1 (by rfl) ⟨806987, by rfl⟩ : syracuseStep 1075983 = 1613975) B1613975
theorem B1076027 : Blo 1072617 1076027 := bstep (se 1 (by rfl) ⟨807020, by rfl⟩ : syracuseStep 1076027 = 1614041) B1614041
theorem B3631931 : Blo 1072617 3631931 := bstep (se 1 (by rfl) ⟨2723948, by rfl⟩ : syracuseStep 3631931 = 5447897) B5447897
theorem B1076103 : Blo 1072617 1076103 := bstep (se 1 (by rfl) ⟨807077, by rfl⟩ : syracuseStep 1076103 = 1614155) B1614155
theorem B1207183 : Blo 1072617 1207183 := bstep (se 1 (by rfl) ⟨905387, by rfl⟩ : syracuseStep 1207183 = 1810775) B1810775
theorem B1076111 : Blo 1072617 1076111 := bstep (se 1 (by rfl) ⟨807083, by rfl⟩ : syracuseStep 1076111 = 1614167) B1614167
theorem B1076155 : Blo 1072617 1076155 := bstep (se 1 (by rfl) ⟨807116, by rfl⟩ : syracuseStep 1076155 = 1614233) B1614233
theorem B1076231 : Blo 1072617 1076231 := bstep (se 1 (by rfl) ⟨807173, by rfl⟩ : syracuseStep 1076231 = 1614347) B1614347
theorem B1076239 : Blo 1072617 1076239 := bstep (se 1 (by rfl) ⟨807179, by rfl⟩ : syracuseStep 1076239 = 1614359) B1614359
theorem B1076283 : Blo 1072617 1076283 := bstep (se 1 (by rfl) ⟨807212, by rfl⟩ : syracuseStep 1076283 = 1614425) B1614425
theorem B2419847 : Blo 1072617 2419847 := bstep (se 1 (by rfl) ⟨1814885, by rfl⟩ : syracuseStep 2419847 = 3629771) B3629771
theorem B1076359 : Blo 1072617 1076359 := bstep (se 1 (by rfl) ⟨807269, by rfl⟩ : syracuseStep 1076359 = 1614539) B1614539
theorem B1076367 : Blo 1072617 1076367 := bstep (se 1 (by rfl) ⟨807275, by rfl⟩ : syracuseStep 1076367 = 1614551) B1614551
theorem B1076411 : Blo 1072617 1076411 := bstep (se 1 (by rfl) ⟨807308, by rfl⟩ : syracuseStep 1076411 = 1614617) B1614617
theorem B5172461 : Blo 1072617 5172461 := bstep (se 3 (by rfl) ⟨969836, by rfl⟩ : syracuseStep 5172461 = 1939673) B1939673
theorem B1076487 : Blo 1072617 1076487 := bstep (se 1 (by rfl) ⟨807365, by rfl⟩ : syracuseStep 1076487 = 1614731) B1614731
theorem B1076495 : Blo 1072617 1076495 := bstep (se 1 (by rfl) ⟨807371, by rfl⟩ : syracuseStep 1076495 = 1614743) B1614743
theorem B3632417 : Blo 1072617 3632417 := bstep (se 2 (by rfl) ⟨1362156, by rfl⟩ : syracuseStep 3632417 = 2724313) B2724313
theorem B2420027 : Blo 1072617 2420027 := bstep (se 1 (by rfl) ⟨1815020, by rfl⟩ : syracuseStep 2420027 = 3630041) B3630041
theorem B1076539 : Blo 1072617 1076539 := bstep (se 1 (by rfl) ⟨807404, by rfl⟩ : syracuseStep 1076539 = 1614809) B1614809
theorem B2583895 : Blo 1072617 2583895 := bstep (se 1 (by rfl) ⟨1937921, by rfl⟩ : syracuseStep 2583895 = 3875843) B3875843
theorem B11627869 : Blo 1072617 11627869 := bstep (se 3 (by rfl) ⟨2180225, by rfl⟩ : syracuseStep 11627869 = 4360451) B4360451
theorem B1207687 : Blo 1072617 1207687 := bstep (se 1 (by rfl) ⟨905765, by rfl⟩ : syracuseStep 1207687 = 1811531) B1811531
theorem B1076615 : Blo 1072617 1076615 := bstep (se 1 (by rfl) ⟨807461, by rfl⟩ : syracuseStep 1076615 = 1614923) B1614923
theorem B2420153 : Blo 1072617 2420153 := bstep (se 2 (by rfl) ⟨907557, by rfl⟩ : syracuseStep 2420153 = 1815115) B1815115
theorem B2584009 : Blo 1072617 2584009 := bstep (se 2 (by rfl) ⟨969003, by rfl⟩ : syracuseStep 2584009 = 1938007) B1938007
theorem B1207867 : Blo 1072617 1207867 := bstep (se 1 (by rfl) ⟨905900, by rfl⟩ : syracuseStep 1207867 = 1811801) B1811801
theorem B4484845 : Blo 1072617 4484845 := bstep (se 3 (by rfl) ⟨840908, by rfl⟩ : syracuseStep 4484845 = 1681817) B1681817
theorem B2715403 : Blo 1072617 2715403 := bstep (se 1 (by rfl) ⟨2036552, by rfl⟩ : syracuseStep 2715403 = 4073105) B4073105
theorem B2420495 : Blo 1072617 2420495 := bstep (se 1 (by rfl) ⟨1815371, by rfl⟩ : syracuseStep 2420495 = 3630743) B3630743
theorem B2420513 : Blo 1072617 2420513 := bstep (se 2 (by rfl) ⟨907692, by rfl⟩ : syracuseStep 2420513 = 1815385) B1815385
theorem B3633011 : Blo 1072617 3633011 := bstep (se 1 (by rfl) ⟨2724758, by rfl⟩ : syracuseStep 3633011 = 5449517) B5449517
theorem B2715545 : Blo 1072617 2715545 := bstep (se 2 (by rfl) ⟨1018329, by rfl⟩ : syracuseStep 2715545 = 2036659) B2036659
theorem B1208335 : Blo 1072617 1208335 := bstep (se 1 (by rfl) ⟨906251, by rfl⟩ : syracuseStep 1208335 = 1812503) B1812503
theorem B2715707 : Blo 1072617 2715707 := bstep (se 1 (by rfl) ⟨2036780, by rfl⟩ : syracuseStep 2715707 = 4073561) B4073561
theorem B2420855 : Blo 1072617 2420855 := bstep (se 1 (by rfl) ⟨1815641, by rfl⟩ : syracuseStep 2420855 = 3631283) B3631283
theorem B5435585 : Blo 1072617 5435585 := bstep (se 2 (by rfl) ⟨2038344, by rfl⟩ : syracuseStep 5435585 = 4076689) B4076689
theorem B2584847 : Blo 1072617 2584847 := bstep (se 1 (by rfl) ⟨1938635, by rfl⟩ : syracuseStep 2584847 = 3877271) B3877271
theorem B2421035 : Blo 1072617 2421035 := bstep (se 1 (by rfl) ⟨1815776, by rfl⟩ : syracuseStep 2421035 = 3631553) B3631553
theorem B2716051 : Blo 1072617 2716051 := bstep (se 1 (by rfl) ⟨2037038, by rfl⟩ : syracuseStep 2716051 = 4074077) B4074077
theorem B8843705 : Blo 1072617 8843705 := bstep (se 2 (by rfl) ⟨3316389, by rfl⟩ : syracuseStep 8843705 = 6632779) B6632779
theorem B1208839 : Blo 1072617 1208839 := bstep (se 1 (by rfl) ⟨906629, by rfl⟩ : syracuseStep 1208839 = 1813259) B1813259
theorem B2716193 : Blo 1072617 2716193 := bstep (se 2 (by rfl) ⟨1018572, by rfl⟩ : syracuseStep 2716193 = 2037145) B2037145
theorem B2421395 : Blo 1072617 2421395 := bstep (se 1 (by rfl) ⟨1816046, by rfl⟩ : syracuseStep 2421395 = 3632093) B3632093
theorem B1209019 : Blo 1072617 1209019 := bstep (se 1 (by rfl) ⟨906764, by rfl⟩ : syracuseStep 1209019 = 1813529) B1813529
theorem B2421449 : Blo 1072617 2421449 := bstep (se 2 (by rfl) ⟨908043, by rfl⟩ : syracuseStep 2421449 = 1816087) B1816087
theorem B1209487 : Blo 1072617 1209487 := bstep (se 1 (by rfl) ⟨907115, by rfl⟩ : syracuseStep 1209487 = 1814231) B1814231
theorem B2422151 : Blo 1072617 2422151 := bstep (se 1 (by rfl) ⟨1816613, by rfl⟩ : syracuseStep 2422151 = 3633227) B3633227
theorem B181630349 : Blo 1072617 181630349 := bstep (se 3 (by rfl) ⟨34055690, by rfl⟩ : syracuseStep 181630349 = 68111381) B68111381
theorem B5436881 : Blo 1072617 5436881 := bstep (se 2 (by rfl) ⟨2038830, by rfl⟩ : syracuseStep 5436881 = 4077661) B4077661
theorem B2717185 : Blo 1072617 2717185 := bstep (se 2 (by rfl) ⟨1018944, by rfl⟩ : syracuseStep 2717185 = 2037889) B2037889
theorem B2422331 : Blo 1072617 2422331 := bstep (se 1 (by rfl) ⟨1816748, by rfl⟩ : syracuseStep 2422331 = 3633497) B3633497
theorem B1209991 : Blo 1072617 1209991 := bstep (se 1 (by rfl) ⟨907493, by rfl⟩ : syracuseStep 1209991 = 1814987) B1814987
theorem B2586259 : Blo 1072617 2586259 := bstep (se 1 (by rfl) ⟨1939694, by rfl⟩ : syracuseStep 2586259 = 3879389) B3879389
theorem B1210171 : Blo 1072617 1210171 := bstep (se 1 (by rfl) ⟨907628, by rfl⟩ : syracuseStep 1210171 = 1815257) B1815257
theorem B2291771 : Blo 1072617 2291771 := bstep (se 1 (by rfl) ⟨1718828, by rfl⟩ : syracuseStep 2291771 = 3437657) B3437657
theorem B2717783 : Blo 1072617 2717783 := bstep (se 1 (by rfl) ⟨2038337, by rfl⟩ : syracuseStep 2717783 = 4076675) B4076675
theorem B4585729 : Blo 1072617 4585729 := bstep (se 2 (by rfl) ⟨1719648, by rfl⟩ : syracuseStep 4585729 = 3439297) B3439297
theorem B1210639 : Blo 1072617 1210639 := bstep (se 1 (by rfl) ⟨907979, by rfl⟩ : syracuseStep 1210639 = 1815959) B1815959
theorem B2717995 : Blo 1072617 2717995 := bstep (se 1 (by rfl) ⟨2038496, by rfl⟩ : syracuseStep 2717995 = 4076993) B4076993
theorem B2488619 : Blo 1072617 2488619 := bstep (se 1 (by rfl) ⟨1866464, by rfl⟩ : syracuseStep 2488619 = 3732929) B3732929
theorem B6125969 : Blo 1072617 6125969 := bstep (se 2 (by rfl) ⟨2297238, by rfl⟩ : syracuseStep 6125969 = 4594477) B4594477
theorem B2718137 : Blo 1072617 2718137 := bstep (se 2 (by rfl) ⟨1019301, by rfl⟩ : syracuseStep 2718137 = 2038603) B2038603
theorem B4586071 : Blo 1072617 4586071 := bstep (se 1 (by rfl) ⟨3439553, by rfl⟩ : syracuseStep 4586071 = 6879107) B6879107
theorem B1211143 : Blo 1072617 1211143 := bstep (se 1 (by rfl) ⟨908357, by rfl⟩ : syracuseStep 1211143 = 1816715) B1816715
theorem B26114831 : Blo 1072617 26114831 := bstep (se 1 (by rfl) ⟨19586123, by rfl⟩ : syracuseStep 26114831 = 39172247) B39172247
theorem B6126425 : Blo 1072617 6126425 := bstep (se 2 (by rfl) ⟨2297409, by rfl⟩ : syracuseStep 6126425 = 4594819) B4594819
theorem B2719129 : Blo 1072617 2719129 := bstep (se 2 (by rfl) ⟨1019673, by rfl⟩ : syracuseStep 2719129 = 2039347) B2039347
theorem B6880697 : Blo 1072617 6880697 := bstep (se 2 (by rfl) ⟨2580261, by rfl⟩ : syracuseStep 6880697 = 5160523) B5160523
theorem B11599325 : Blo 1072617 11599325 := bstep (se 3 (by rfl) ⟨2174873, by rfl⟩ : syracuseStep 11599325 = 4349747) B4349747
theorem B5438987 : Blo 1072617 5438987 := bstep (se 1 (by rfl) ⟨4079240, by rfl⟩ : syracuseStep 5438987 = 8158481) B8158481
theorem B2719291 : Blo 1072617 2719291 := bstep (se 1 (by rfl) ⟨2039468, by rfl⟩ : syracuseStep 2719291 = 4078937) B4078937
theorem B11632193 : Blo 1072617 11632193 := bstep (se 2 (by rfl) ⟨4362072, by rfl⟩ : syracuseStep 11632193 = 8724145) B8724145
theorem B5439149 : Blo 1072617 5439149 := bstep (se 3 (by rfl) ⟨1019840, by rfl⟩ : syracuseStep 5439149 = 2039681) B2039681
theorem B2719433 : Blo 1072617 2719433 := bstep (se 2 (by rfl) ⟨1019787, by rfl⟩ : syracuseStep 2719433 = 2039575) B2039575
theorem B2752289 : Blo 1072617 2752289 := bstep (se 2 (by rfl) ⟨1032108, by rfl⟩ : syracuseStep 2752289 = 2064217) B2064217
theorem B7339979 : Blo 1072617 7339979 := bstep (se 1 (by rfl) ⟨5504984, by rfl⟩ : syracuseStep 7339979 = 11009969) B11009969
theorem B3866777 : Blo 1072617 3866777 := bstep (se 2 (by rfl) ⟨1450041, by rfl⟩ : syracuseStep 3866777 = 2900083) B2900083
theorem B1933561 : Blo 1072617 1933561 := bstep (se 2 (by rfl) ⟨725085, by rfl⟩ : syracuseStep 1933561 = 1450171) B1450171
theorem B6127883 : Blo 1072617 6127883 := bstep (se 1 (by rfl) ⟨4595912, by rfl⟩ : syracuseStep 6127883 = 9191825) B9191825
theorem B2720243 : Blo 1072617 2720243 := bstep (se 1 (by rfl) ⟨2040182, by rfl⟩ : syracuseStep 2720243 = 4080365) B4080365
theorem B4588463 : Blo 1072617 4588463 := bstep (se 1 (by rfl) ⟨3441347, by rfl⟩ : syracuseStep 4588463 = 6882695) B6882695
theorem B6128567 : Blo 1072617 6128567 := bstep (se 1 (by rfl) ⟨4596425, by rfl⟩ : syracuseStep 6128567 = 9192851) B9192851
theorem B2720699 : Blo 1072617 2720699 := bstep (se 1 (by rfl) ⟨2040524, by rfl⟩ : syracuseStep 2720699 = 4081049) B4081049
theorem B18383921 : Blo 1072617 18383921 := bstep (se 2 (by rfl) ⟨6893970, by rfl⟩ : syracuseStep 18383921 = 13787941) B13787941
theorem B3671401 : Blo 1072617 3671401 := bstep (se 2 (by rfl) ⟨1376775, by rfl⟩ : syracuseStep 3671401 = 2753551) B2753551
theorem B4359739 : Blo 1072617 4359739 := bstep (se 1 (by rfl) ⟨3269804, by rfl⟩ : syracuseStep 4359739 = 6539609) B6539609
theorem B1934945 : Blo 1072617 1934945 := bstep (se 2 (by rfl) ⟨725604, by rfl⟩ : syracuseStep 1934945 = 1451209) B1451209
theorem B2721377 : Blo 1072617 2721377 := bstep (se 2 (by rfl) ⟨1020516, by rfl⟩ : syracuseStep 2721377 = 2041033) B2041033
theorem B3671687 : Blo 1072617 3671687 := bstep (se 1 (by rfl) ⟨2753765, by rfl⟩ : syracuseStep 3671687 = 5507531) B5507531
theorem B6129341 : Blo 1072617 6129341 := bstep (se 3 (by rfl) ⟨1149251, by rfl⟩ : syracuseStep 6129341 = 2298503) B2298503
theorem B3442475 : Blo 1072617 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B2066395 : Blo 1072617 2066395 := bstep (se 1 (by rfl) ⟨1549796, by rfl⟩ : syracuseStep 2066395 = 3099593) B3099593
theorem B7342169 : Blo 1072617 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B6130025 : Blo 1072617 6130025 := bstep (se 2 (by rfl) ⟨2298759, by rfl⟩ : syracuseStep 6130025 = 4597519) B4597519
theorem B3672539 : Blo 1072617 3672539 := bstep (se 1 (by rfl) ⟨2754404, by rfl⟩ : syracuseStep 3672539 = 5508809) B5508809
theorem B2329337 : Blo 1072617 2329337 := bstep (se 2 (by rfl) ⟨873501, by rfl⟩ : syracuseStep 2329337 = 1747003) B1747003
theorem B2722835 : Blo 1072617 2722835 := bstep (se 1 (by rfl) ⟨2042126, by rfl⟩ : syracuseStep 2722835 = 4084253) B4084253
theorem B5442713 : Blo 1072617 5442713 := bstep (se 2 (by rfl) ⟨2041017, by rfl⟩ : syracuseStep 5442713 = 4082035) B4082035
theorem B1838279 : Blo 1072617 1838279 := bstep (se 1 (by rfl) ⟨1378709, by rfl⟩ : syracuseStep 1838279 = 2757419) B2757419
theorem B1936595 : Blo 1072617 1936595 := bstep (se 1 (by rfl) ⟨1452446, by rfl⟩ : syracuseStep 1936595 = 2904893) B2904893
theorem B1608953 : Blo 1072617 1608953 := bstep (se 2 (by rfl) ⟨603357, by rfl⟩ : syracuseStep 1608953 = 1206715) B1206715
theorem B1609055 : Blo 1072617 1609055 := bstep (se 1 (by rfl) ⟨1206791, by rfl⟩ : syracuseStep 1609055 = 2413583) B2413583
theorem B1609067 : Blo 1072617 1609067 := bstep (se 1 (by rfl) ⟨1206800, by rfl⟩ : syracuseStep 1609067 = 2413601) B2413601
theorem B2297231 : Blo 1072617 2297231 := bstep (se 1 (by rfl) ⟨1722923, by rfl⟩ : syracuseStep 2297231 = 3445847) B3445847
theorem B2723291 : Blo 1072617 2723291 := bstep (se 1 (by rfl) ⟨2042468, by rfl⟩ : syracuseStep 2723291 = 4084937) B4084937
theorem B8162855 : Blo 1072617 8162855 := bstep (se 1 (by rfl) ⟨6122141, by rfl⟩ : syracuseStep 8162855 = 12244283) B12244283
theorem B1609295 : Blo 1072617 1609295 := bstep (se 1 (by rfl) ⟨1206971, by rfl⟩ : syracuseStep 1609295 = 2413943) B2413943
theorem B1609415 : Blo 1072617 1609415 := bstep (se 1 (by rfl) ⟨1207061, by rfl⟩ : syracuseStep 1609415 = 2414123) B2414123
theorem B4591403 : Blo 1072617 4591403 := bstep (se 1 (by rfl) ⟨3443552, by rfl⟩ : syracuseStep 4591403 = 6887105) B6887105
theorem B1609577 : Blo 1072617 1609577 := bstep (se 2 (by rfl) ⟨603591, by rfl⟩ : syracuseStep 1609577 = 1207183) B1207183
theorem B1609655 : Blo 1072617 1609655 := bstep (se 1 (by rfl) ⟨1207241, by rfl⟩ : syracuseStep 1609655 = 2414483) B2414483
theorem B1609691 : Blo 1072617 1609691 := bstep (se 1 (by rfl) ⟨1207268, by rfl⟩ : syracuseStep 1609691 = 2414537) B2414537
theorem B11604131 : Blo 1072617 11604131 := bstep (se 1 (by rfl) ⟨8703098, by rfl⟩ : syracuseStep 11604131 = 17406197) B17406197
theorem B4133111 : Blo 1072617 4133111 := bstep (se 1 (by rfl) ⟨3099833, by rfl⟩ : syracuseStep 4133111 = 6199667) B6199667
theorem B5509463 : Blo 1072617 5509463 := bstep (se 1 (by rfl) ⟨4132097, by rfl⟩ : syracuseStep 5509463 = 8264195) B8264195
theorem B1610159 : Blo 1072617 1610159 := bstep (se 1 (by rfl) ⟨1207619, by rfl⟩ : syracuseStep 1610159 = 2415239) B2415239
theorem B3445193 : Blo 1072617 3445193 := bstep (se 2 (by rfl) ⟨1291947, by rfl⟩ : syracuseStep 3445193 = 2583895) B2583895
theorem B15503825 : Blo 1072617 15503825 := bstep (se 2 (by rfl) ⟨5813934, by rfl⟩ : syracuseStep 15503825 = 11627869) B11627869
theorem B1610249 : Blo 1072617 1610249 := bstep (se 2 (by rfl) ⟨603843, by rfl⟩ : syracuseStep 1610249 = 1207687) B1207687
theorem B4592153 : Blo 1072617 4592153 := bstep (se 2 (by rfl) ⟨1722057, by rfl⟩ : syracuseStep 4592153 = 3444115) B3444115
theorem B1610279 : Blo 1072617 1610279 := bstep (se 1 (by rfl) ⟨1207709, by rfl⟩ : syracuseStep 1610279 = 2415419) B2415419
theorem B3445345 : Blo 1072617 3445345 := bstep (se 2 (by rfl) ⟨1292004, by rfl⟩ : syracuseStep 3445345 = 2584009) B2584009
theorem B1610363 : Blo 1072617 1610363 := bstep (se 1 (by rfl) ⟨1207772, by rfl⟩ : syracuseStep 1610363 = 2415545) B2415545
theorem B2724475 : Blo 1072617 2724475 := bstep (se 1 (by rfl) ⟨2043356, by rfl⟩ : syracuseStep 2724475 = 4086713) B4086713
theorem B1610489 : Blo 1072617 1610489 := bstep (se 2 (by rfl) ⟨603933, by rfl⟩ : syracuseStep 1610489 = 1207867) B1207867
theorem B1610591 : Blo 1072617 1610591 := bstep (se 1 (by rfl) ⟨1207943, by rfl⟩ : syracuseStep 1610591 = 2415887) B2415887
theorem B1610603 : Blo 1072617 1610603 := bstep (se 1 (by rfl) ⟨1207952, by rfl⟩ : syracuseStep 1610603 = 2415905) B2415905
theorem B3445679 : Blo 1072617 3445679 := bstep (se 1 (by rfl) ⟨2584259, by rfl⟩ : syracuseStep 3445679 = 5168519) B5168519
theorem B2757689 : Blo 1072617 2757689 := bstep (se 2 (by rfl) ⟨1034133, by rfl⟩ : syracuseStep 2757689 = 2068267) B2068267
theorem B1610831 : Blo 1072617 1610831 := bstep (se 1 (by rfl) ⟨1208123, by rfl⟩ : syracuseStep 1610831 = 2416247) B2416247
theorem B1610951 : Blo 1072617 1610951 := bstep (se 1 (by rfl) ⟨1208213, by rfl⟩ : syracuseStep 1610951 = 2416427) B2416427
theorem B1611113 : Blo 1072617 1611113 := bstep (se 2 (by rfl) ⟨604167, by rfl⟩ : syracuseStep 1611113 = 1208335) B1208335
theorem B1611191 : Blo 1072617 1611191 := bstep (se 1 (by rfl) ⟨1208393, by rfl⟩ : syracuseStep 1611191 = 2416787) B2416787
theorem B1611227 : Blo 1072617 1611227 := bstep (se 1 (by rfl) ⟨1208420, by rfl⟩ : syracuseStep 1611227 = 2416841) B2416841
theorem B2037305 : Blo 1072617 2037305 := bstep (se 2 (by rfl) ⟨763989, by rfl⟩ : syracuseStep 2037305 = 1527979) B1527979
theorem B3872555 : Blo 1072617 3872555 := bstep (se 1 (by rfl) ⟨2904416, by rfl⟩ : syracuseStep 3872555 = 5808833) B5808833
theorem B13080379 : Blo 1072617 13080379 := bstep (se 1 (by rfl) ⟨9810284, by rfl⟩ : syracuseStep 13080379 = 19620569) B19620569
theorem B3872585 : Blo 1072617 3872585 := bstep (se 2 (by rfl) ⟨1452219, by rfl⟩ : syracuseStep 3872585 = 2904439) B2904439
theorem B4134763 : Blo 1072617 4134763 := bstep (se 1 (by rfl) ⟨3101072, by rfl⟩ : syracuseStep 4134763 = 6202145) B6202145
theorem B1611695 : Blo 1072617 1611695 := bstep (se 1 (by rfl) ⟨1208771, by rfl⟩ : syracuseStep 1611695 = 2417543) B2417543
theorem B3872699 : Blo 1072617 3872699 := bstep (se 1 (by rfl) ⟨2904524, by rfl⟩ : syracuseStep 3872699 = 5809049) B5809049
theorem B1611785 : Blo 1072617 1611785 := bstep (se 2 (by rfl) ⟨604419, by rfl⟩ : syracuseStep 1611785 = 1208839) B1208839
theorem B1611815 : Blo 1072617 1611815 := bstep (se 1 (by rfl) ⟨1208861, by rfl⟩ : syracuseStep 1611815 = 2417723) B2417723
theorem B4593779 : Blo 1072617 4593779 := bstep (se 1 (by rfl) ⟨3445334, by rfl⟩ : syracuseStep 4593779 = 6890669) B6890669
theorem B1611899 : Blo 1072617 1611899 := bstep (se 1 (by rfl) ⟨1208924, by rfl⟩ : syracuseStep 1611899 = 2417849) B2417849
theorem B1612025 : Blo 1072617 1612025 := bstep (se 2 (by rfl) ⟨604509, by rfl⟩ : syracuseStep 1612025 = 1209019) B1209019
theorem B1612127 : Blo 1072617 1612127 := bstep (se 1 (by rfl) ⟨1209095, by rfl⟩ : syracuseStep 1612127 = 2418191) B2418191
theorem B1612139 : Blo 1072617 1612139 := bstep (se 1 (by rfl) ⟨1209104, by rfl⟩ : syracuseStep 1612139 = 2418209) B2418209
theorem B1612367 : Blo 1072617 1612367 := bstep (se 1 (by rfl) ⟨1209275, by rfl⟩ : syracuseStep 1612367 = 2418551) B2418551
theorem B1612487 : Blo 1072617 1612487 := bstep (se 1 (by rfl) ⟨1209365, by rfl⟩ : syracuseStep 1612487 = 2418731) B2418731
theorem B1612649 : Blo 1072617 1612649 := bstep (se 2 (by rfl) ⟨604743, by rfl⟩ : syracuseStep 1612649 = 1209487) B1209487
theorem B1612727 : Blo 1072617 1612727 := bstep (se 1 (by rfl) ⟨1209545, by rfl⟩ : syracuseStep 1612727 = 2419091) B2419091
theorem B1743835 : Blo 1072617 1743835 := bstep (se 1 (by rfl) ⟨1307876, by rfl⟩ : syracuseStep 1743835 = 2615753) B2615753
theorem B1612763 : Blo 1072617 1612763 := bstep (se 1 (by rfl) ⟨1209572, by rfl⟩ : syracuseStep 1612763 = 2419145) B2419145
theorem B2038907 : Blo 1072617 2038907 := bstep (se 1 (by rfl) ⟨1529180, by rfl⟩ : syracuseStep 2038907 = 3058361) B3058361
theorem B14687405 : Blo 1072617 14687405 := bstep (se 3 (by rfl) ⟨2753888, by rfl⟩ : syracuseStep 14687405 = 5507777) B5507777
theorem B1613231 : Blo 1072617 1613231 := bstep (se 1 (by rfl) ⟨1209923, by rfl⟩ : syracuseStep 1613231 = 2419847) B2419847
theorem B3448307 : Blo 1072617 3448307 := bstep (se 1 (by rfl) ⟨2586230, by rfl⟩ : syracuseStep 3448307 = 5172461) B5172461
theorem B1613321 : Blo 1072617 1613321 := bstep (se 2 (by rfl) ⟨604995, by rfl⟩ : syracuseStep 1613321 = 1209991) B1209991
theorem B3448345 : Blo 1072617 3448345 := bstep (se 2 (by rfl) ⟨1293129, by rfl⟩ : syracuseStep 3448345 = 2586259) B2586259
theorem B1613351 : Blo 1072617 1613351 := bstep (se 1 (by rfl) ⟨1210013, by rfl⟩ : syracuseStep 1613351 = 2420027) B2420027
theorem B2039393 : Blo 1072617 2039393 := bstep (se 2 (by rfl) ⟨764772, by rfl⟩ : syracuseStep 2039393 = 1529545) B1529545
theorem B1613435 : Blo 1072617 1613435 := bstep (se 1 (by rfl) ⟨1210076, by rfl⟩ : syracuseStep 1613435 = 2420153) B2420153
theorem B6528761 : Blo 1072617 6528761 := bstep (se 2 (by rfl) ⟨2448285, by rfl⟩ : syracuseStep 6528761 = 4896571) B4896571
theorem B1613561 : Blo 1072617 1613561 := bstep (se 2 (by rfl) ⟨605085, by rfl⟩ : syracuseStep 1613561 = 1210171) B1210171
theorem B1613663 : Blo 1072617 1613663 := bstep (se 1 (by rfl) ⟨1210247, by rfl⟩ : syracuseStep 1613663 = 2420495) B2420495
theorem B1613675 : Blo 1072617 1613675 := bstep (se 1 (by rfl) ⟨1210256, by rfl⟩ : syracuseStep 1613675 = 2420513) B2420513
theorem B1449911 : Blo 1072617 1449911 := bstep (se 1 (by rfl) ⟨1087433, by rfl⟩ : syracuseStep 1449911 = 2174867) B2174867
theorem B2039735 : Blo 1072617 2039735 := bstep (se 1 (by rfl) ⟨1529801, by rfl⟩ : syracuseStep 2039735 = 3059603) B3059603
theorem B1810363 : Blo 1072617 1810363 := bstep (se 1 (by rfl) ⟨1357772, by rfl⟩ : syracuseStep 1810363 = 2715545) B2715545
theorem B1810471 : Blo 1072617 1810471 := bstep (se 1 (by rfl) ⟨1357853, by rfl⟩ : syracuseStep 1810471 = 2715707) B2715707
theorem B1613903 : Blo 1072617 1613903 := bstep (se 1 (by rfl) ⟨1210427, by rfl⟩ : syracuseStep 1613903 = 2420855) B2420855
theorem B10330193 : Blo 1072617 10330193 := bstep (se 2 (by rfl) ⟨3873822, by rfl⟩ : syracuseStep 10330193 = 7747645) B7747645
theorem B1614023 : Blo 1072617 1614023 := bstep (se 1 (by rfl) ⟨1210517, by rfl⟩ : syracuseStep 1614023 = 2421035) B2421035
theorem B2040137 : Blo 1072617 2040137 := bstep (se 2 (by rfl) ⟨765051, by rfl⟩ : syracuseStep 2040137 = 1530103) B1530103
theorem B1548649 : Blo 1072617 1548649 := bstep (se 2 (by rfl) ⟨580743, by rfl⟩ : syracuseStep 1548649 = 1161487) B1161487
theorem B1614185 : Blo 1072617 1614185 := bstep (se 2 (by rfl) ⟨605319, by rfl⟩ : syracuseStep 1614185 = 1210639) B1210639
theorem B1810795 : Blo 1072617 1810795 := bstep (se 1 (by rfl) ⟨1358096, by rfl⟩ : syracuseStep 1810795 = 2716193) B2716193
theorem B1614263 : Blo 1072617 1614263 := bstep (se 1 (by rfl) ⟨1210697, by rfl⟩ : syracuseStep 1614263 = 2421395) B2421395
theorem B1614299 : Blo 1072617 1614299 := bstep (se 1 (by rfl) ⟨1210724, by rfl⟩ : syracuseStep 1614299 = 2421449) B2421449
theorem B3875467 : Blo 1072617 3875467 := bstep (se 1 (by rfl) ⟨2906600, by rfl⟩ : syracuseStep 3875467 = 5813201) B5813201
theorem B1614767 : Blo 1072617 1614767 := bstep (se 1 (by rfl) ⟨1211075, by rfl⟩ : syracuseStep 1614767 = 2422151) B2422151
theorem B121086899 : Blo 1072617 121086899 := bstep (se 1 (by rfl) ⟨90815174, by rfl⟩ : syracuseStep 121086899 = 181630349) B181630349
theorem B1614857 : Blo 1072617 1614857 := bstep (se 2 (by rfl) ⟨605571, by rfl⟩ : syracuseStep 1614857 = 1211143) B1211143
theorem B2040851 : Blo 1072617 2040851 := bstep (se 1 (by rfl) ⟨1530638, by rfl⟩ : syracuseStep 2040851 = 3061277) B3061277
theorem B1614887 : Blo 1072617 1614887 := bstep (se 1 (by rfl) ⟨1211165, by rfl⟩ : syracuseStep 1614887 = 2422331) B2422331
theorem B2040889 : Blo 1072617 2040889 := bstep (se 2 (by rfl) ⟨765333, by rfl⟩ : syracuseStep 2040889 = 1530667) B1530667
theorem B4072619 : Blo 1072617 4072619 := bstep (se 1 (by rfl) ⟨3054464, by rfl⟩ : syracuseStep 4072619 = 6108929) B6108929
theorem B2041193 : Blo 1072617 2041193 := bstep (se 2 (by rfl) ⟨765447, by rfl⟩ : syracuseStep 2041193 = 1530895) B1530895
theorem B1811855 : Blo 1072617 1811855 := bstep (se 1 (by rfl) ⟨1358891, by rfl⟩ : syracuseStep 1811855 = 2717783) B2717783
theorem B4597211 : Blo 1072617 4597211 := bstep (se 1 (by rfl) ⟨3447908, by rfl⟩ : syracuseStep 4597211 = 6895817) B6895817
theorem B1812091 : Blo 1072617 1812091 := bstep (se 1 (by rfl) ⟨1359068, by rfl⟩ : syracuseStep 1812091 = 2718137) B2718137
theorem B5449355 : Blo 1072617 5449355 := bstep (se 1 (by rfl) ⟨4087016, by rfl⟩ : syracuseStep 5449355 = 8174033) B8174033
theorem B6891155 : Blo 1072617 6891155 := bstep (se 1 (by rfl) ⟨5168366, by rfl⟩ : syracuseStep 6891155 = 10336733) B10336733
theorem B17409887 : Blo 1072617 17409887 := bstep (se 1 (by rfl) ⟨13057415, by rfl⟩ : syracuseStep 17409887 = 26114831) B26114831
theorem B3024827 : Blo 1072617 3024827 := bstep (se 1 (by rfl) ⟨2268620, by rfl⟩ : syracuseStep 3024827 = 4537241) B4537241
theorem B11610049 : Blo 1072617 11610049 := bstep (se 2 (by rfl) ⟨4353768, by rfl⟩ : syracuseStep 11610049 = 8707537) B8707537
theorem B23275457 : Blo 1072617 23275457 := bstep (se 2 (by rfl) ⟨8728296, by rfl⟩ : syracuseStep 23275457 = 17456593) B17456593
theorem B1812955 : Blo 1072617 1812955 := bstep (se 1 (by rfl) ⟨1359716, by rfl⟩ : syracuseStep 1812955 = 2719433) B2719433
theorem B2042491 : Blo 1072617 2042491 := bstep (se 1 (by rfl) ⟨1531868, by rfl⟩ : syracuseStep 2042491 = 3063737) B3063737
theorem B4893319 : Blo 1072617 4893319 := bstep (se 1 (by rfl) ⟨3669989, by rfl⟩ : syracuseStep 4893319 = 7339979) B7339979
theorem B2042567 : Blo 1072617 2042567 := bstep (se 1 (by rfl) ⟨1531925, by rfl⟩ : syracuseStep 2042567 = 3063851) B3063851
theorem B1813583 : Blo 1072617 1813583 := bstep (se 1 (by rfl) ⟨1360187, by rfl⟩ : syracuseStep 1813583 = 2720375) B2720375
theorem B2042977 : Blo 1072617 2042977 := bstep (se 2 (by rfl) ⟨766116, by rfl⟩ : syracuseStep 2042977 = 1532233) B1532233
theorem B2043319 : Blo 1072617 2043319 := bstep (se 1 (by rfl) ⟨1532489, by rfl⟩ : syracuseStep 2043319 = 3064979) B3064979
theorem B4075217 : Blo 1072617 4075217 := bstep (se 2 (by rfl) ⟨1528206, by rfl⟩ : syracuseStep 4075217 = 3056413) B3056413
theorem B2043721 : Blo 1072617 2043721 := bstep (se 2 (by rfl) ⟨766395, by rfl⟩ : syracuseStep 2043721 = 1532791) B1532791
theorem B1814447 : Blo 1072617 1814447 := bstep (se 1 (by rfl) ⟨1360835, by rfl⟩ : syracuseStep 1814447 = 2721671) B2721671
theorem B9809849 : Blo 1072617 9809849 := bstep (se 2 (by rfl) ⟨3678693, by rfl⟩ : syracuseStep 9809849 = 7357387) B7357387
theorem B2174939 : Blo 1072617 2174939 := bstep (se 1 (by rfl) ⟨1631204, by rfl⟩ : syracuseStep 2174939 = 3262409) B3262409
theorem B4075535 : Blo 1072617 4075535 := bstep (se 1 (by rfl) ⟨3056651, by rfl⟩ : syracuseStep 4075535 = 6113303) B6113303
theorem B17018909 : Blo 1072617 17018909 := bstep (se 3 (by rfl) ⟨3191045, by rfl⟩ : syracuseStep 17018909 = 6382091) B6382091
theorem B30978125 : Blo 1072617 30978125 := bstep (se 3 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 30978125 = 11616797) B11616797
theorem B1814879 : Blo 1072617 1814879 := bstep (se 1 (by rfl) ⟨1361159, by rfl⟩ : syracuseStep 1814879 = 2722319) B2722319
theorem B1815439 : Blo 1072617 1815439 := bstep (se 1 (by rfl) ⟨1361579, by rfl⟩ : syracuseStep 1815439 = 2723159) B2723159
theorem B32257091 : Blo 1072617 32257091 := bstep (se 1 (by rfl) ⟨24192818, by rfl⟩ : syracuseStep 32257091 = 48385637) B48385637
theorem B1816121 : Blo 1072617 1816121 := bstep (se 2 (by rfl) ⟨681045, by rfl⟩ : syracuseStep 1816121 = 1362091) B1362091
theorem B6895201 : Blo 1072617 6895201 := bstep (se 2 (by rfl) ⟨2585700, by rfl⟩ : syracuseStep 6895201 = 5171401) B5171401
theorem B15513281 : Blo 1072617 15513281 := bstep (se 2 (by rfl) ⟨5817480, by rfl⟩ : syracuseStep 15513281 = 11634961) B11634961
theorem B2176723 : Blo 1072617 2176723 := bstep (se 1 (by rfl) ⟨1632542, by rfl⟩ : syracuseStep 2176723 = 3265085) B3265085
theorem B16562015 : Blo 1072617 16562015 := bstep (se 1 (by rfl) ⟨12421511, by rfl⟩ : syracuseStep 16562015 = 24843023) B24843023
theorem B1718329 : Blo 1072617 1718329 := bstep (se 2 (by rfl) ⟨644373, by rfl⟩ : syracuseStep 1718329 = 1288747) B1288747
theorem B4077647 : Blo 1072617 4077647 := bstep (se 1 (by rfl) ⟨3058235, by rfl⟩ : syracuseStep 4077647 = 6116471) B6116471
theorem B15480989 : Blo 1072617 15480989 := bstep (se 3 (by rfl) ⟨2902685, by rfl⟩ : syracuseStep 15480989 = 5805371) B5805371
theorem B181582145 : Blo 1072617 181582145 := bstep (se 2 (by rfl) ⟨68093304, by rfl⟩ : syracuseStep 181582145 = 136186609) B136186609
theorem B1358299 : Blo 1072617 1358299 := bstep (se 1 (by rfl) ⟨1018724, by rfl⟩ : syracuseStep 1358299 = 2037449) B2037449
theorem B3062461 : Blo 1072617 3062461 := bstep (se 3 (by rfl) ⟨574211, by rfl⟩ : syracuseStep 3062461 = 1148423) B1148423
theorem B156941171 : Blo 1072617 156941171 := bstep (se 1 (by rfl) ⟨117705878, by rfl⟩ : syracuseStep 156941171 = 235411757) B235411757
theorem B59554739 : Blo 1072617 59554739 := bstep (se 1 (by rfl) ⟨44666054, by rfl⟩ : syracuseStep 59554739 = 89332109) B89332109
theorem B3062711 : Blo 1072617 3062711 := bstep (se 1 (by rfl) ⟨2297033, by rfl⟩ : syracuseStep 3062711 = 4594067) B4594067
theorem B8174519 : Blo 1072617 8174519 := bstep (se 1 (by rfl) ⟨6130889, by rfl⟩ : syracuseStep 8174519 = 12261779) B12261779
theorem B7453775 : Blo 1072617 7453775 := bstep (se 1 (by rfl) ⟨5590331, by rfl⟩ : syracuseStep 7453775 = 11180663) B11180663
theorem B5979793 : Blo 1072617 5979793 := bstep (se 2 (by rfl) ⟨2242422, by rfl⟩ : syracuseStep 5979793 = 4484845) B4484845
theorem B3620537 : Blo 1072617 3620537 := bstep (se 2 (by rfl) ⟨1357701, by rfl⟩ : syracuseStep 3620537 = 2715403) B2715403
theorem B5881643 : Blo 1072617 5881643 := bstep (se 1 (by rfl) ⟨4411232, by rfl⟩ : syracuseStep 5881643 = 8822465) B8822465
theorem B6111071 : Blo 1072617 6111071 := bstep (se 1 (by rfl) ⟨4583303, by rfl⟩ : syracuseStep 6111071 = 9166607) B9166607
theorem B1720207 : Blo 1072617 1720207 := bstep (se 1 (by rfl) ⟨1290155, by rfl⟩ : syracuseStep 1720207 = 2580311) B2580311
theorem B6111389 : Blo 1072617 6111389 := bstep (se 3 (by rfl) ⟨1145885, by rfl⟩ : syracuseStep 6111389 = 2291771) B2291771
theorem B3621131 : Blo 1072617 3621131 := bstep (se 1 (by rfl) ⟨2715848, by rfl⟩ : syracuseStep 3621131 = 5431697) B5431697
theorem B3064169 : Blo 1072617 3064169 := bstep (se 2 (by rfl) ⟨1149063, by rfl⟩ : syracuseStep 3064169 = 2298127) B2298127
theorem B6209921 : Blo 1072617 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B3064193 : Blo 1072617 3064193 := bstep (se 2 (by rfl) ⟨1149072, by rfl⟩ : syracuseStep 3064193 = 2298145) B2298145
theorem B4080091 : Blo 1072617 4080091 := bstep (se 1 (by rfl) ⟨3060068, by rfl⟩ : syracuseStep 4080091 = 6120137) B6120137
theorem B3621401 : Blo 1072617 3621401 := bstep (se 2 (by rfl) ⟨1358025, by rfl⟩ : syracuseStep 3621401 = 2716051) B2716051
theorem B9290771 : Blo 1072617 9290771 := bstep (se 1 (by rfl) ⟨6968078, by rfl⟩ : syracuseStep 9290771 = 13936157) B13936157
theorem B4408435 : Blo 1072617 4408435 := bstep (se 1 (by rfl) ⟨3306326, by rfl⟩ : syracuseStep 4408435 = 6612653) B6612653
theorem B7750849 : Blo 1072617 7750849 := bstep (se 2 (by rfl) ⟨2906568, by rfl⟩ : syracuseStep 7750849 = 5813137) B5813137
theorem B1721591 : Blo 1072617 1721591 := bstep (se 1 (by rfl) ⟨1291193, by rfl⟩ : syracuseStep 1721591 = 2582387) B2582387
theorem B24823331 : Blo 1072617 24823331 := bstep (se 1 (by rfl) ⟨18617498, by rfl⟩ : syracuseStep 24823331 = 37234997) B37234997
theorem B2180647 : Blo 1072617 2180647 := bstep (se 1 (by rfl) ⟨1635485, by rfl⟩ : syracuseStep 2180647 = 3270971) B3270971
theorem B3622535 : Blo 1072617 3622535 := bstep (se 1 (by rfl) ⟨2716901, by rfl⟩ : syracuseStep 3622535 = 5433803) B5433803
theorem B4081337 : Blo 1072617 4081337 := bstep (se 2 (by rfl) ⟨1530501, by rfl⟩ : syracuseStep 4081337 = 3061003) B3061003
theorem B3622589 : Blo 1072617 3622589 := bstep (se 3 (by rfl) ⟨679235, by rfl⟩ : syracuseStep 3622589 = 1358471) B1358471
theorem B4081367 : Blo 1072617 4081367 := bstep (se 1 (by rfl) ⟨3061025, by rfl⟩ : syracuseStep 4081367 = 6122051) B6122051
theorem B15517433 : Blo 1072617 15517433 := bstep (se 2 (by rfl) ⟨5819037, by rfl⟩ : syracuseStep 15517433 = 11638075) B11638075
theorem B3622751 : Blo 1072617 3622751 := bstep (se 1 (by rfl) ⟨2717063, by rfl⟩ : syracuseStep 3622751 = 5434127) B5434127
theorem B14698349 : Blo 1072617 14698349 := bstep (se 3 (by rfl) ⟨2755940, by rfl⟩ : syracuseStep 14698349 = 5511881) B5511881
theorem B3622913 : Blo 1072617 3622913 := bstep (se 2 (by rfl) ⟨1358592, by rfl⟩ : syracuseStep 3622913 = 2717185) B2717185
theorem B5163097 : Blo 1072617 5163097 := bstep (se 2 (by rfl) ⟨1936161, by rfl⟩ : syracuseStep 5163097 = 3872323) B3872323
theorem B1362359 : Blo 1072617 1362359 := bstep (se 1 (by rfl) ⟨1021769, by rfl⟩ : syracuseStep 1362359 = 2043539) B2043539
theorem B1362511 : Blo 1072617 1362511 := bstep (se 1 (by rfl) ⟨1021883, by rfl⟩ : syracuseStep 1362511 = 2043767) B2043767
theorem B3623723 : Blo 1072617 3623723 := bstep (se 1 (by rfl) ⟨2717792, by rfl⟩ : syracuseStep 3623723 = 5435585) B5435585
theorem B1723231 : Blo 1072617 1723231 := bstep (se 1 (by rfl) ⟨1292423, by rfl⟩ : syracuseStep 1723231 = 2584847) B2584847
theorem B6114305 : Blo 1072617 6114305 := bstep (se 2 (by rfl) ⟨2292864, by rfl⟩ : syracuseStep 6114305 = 4585729) B4585729
theorem B3623993 : Blo 1072617 3623993 := bstep (se 2 (by rfl) ⟨1358997, by rfl⟩ : syracuseStep 3623993 = 2717995) B2717995
theorem B4246723 : Blo 1072617 4246723 := bstep (se 1 (by rfl) ⟨3185042, by rfl⟩ : syracuseStep 4246723 = 6370085) B6370085
theorem B3624317 : Blo 1072617 3624317 := bstep (se 3 (by rfl) ⟨679559, by rfl⟩ : syracuseStep 3624317 = 1359119) B1359119
theorem B6114761 : Blo 1072617 6114761 := bstep (se 2 (by rfl) ⟨2293035, by rfl⟩ : syracuseStep 6114761 = 4586071) B4586071
theorem B3624587 : Blo 1072617 3624587 := bstep (se 1 (by rfl) ⟨2718440, by rfl⟩ : syracuseStep 3624587 = 5436881) B5436881
theorem B1659079 : Blo 1072617 1659079 := bstep (se 1 (by rfl) ⟨1244309, by rfl⟩ : syracuseStep 1659079 = 2488619) B2488619
theorem B4083979 : Blo 1072617 4083979 := bstep (se 1 (by rfl) ⟨3062984, by rfl⟩ : syracuseStep 4083979 = 6125969) B6125969
theorem B3625505 : Blo 1072617 3625505 := bstep (se 2 (by rfl) ⟨1359564, by rfl⟩ : syracuseStep 3625505 = 2719129) B2719129
theorem B4084283 : Blo 1072617 4084283 := bstep (se 1 (by rfl) ⟨3063212, by rfl⟩ : syracuseStep 4084283 = 6126425) B6126425
theorem B3625721 : Blo 1072617 3625721 := bstep (se 2 (by rfl) ⟨1359645, by rfl⟩ : syracuseStep 3625721 = 2719291) B2719291
theorem B8147789 : Blo 1072617 8147789 := bstep (se 3 (by rfl) ⟨1527710, by rfl⟩ : syracuseStep 8147789 = 3055421) B3055421
theorem B3625991 : Blo 1072617 3625991 := bstep (se 1 (by rfl) ⟨2719493, by rfl⟩ : syracuseStep 3625991 = 5438987) B5438987
theorem B7754795 : Blo 1072617 7754795 := bstep (se 1 (by rfl) ⟨5816096, by rfl⟩ : syracuseStep 7754795 = 11632193) B11632193
theorem B3626099 : Blo 1072617 3626099 := bstep (se 1 (by rfl) ⟨2719574, by rfl⟩ : syracuseStep 3626099 = 5439149) B5439149
theorem B69784847 : Blo 1072617 69784847 := bstep (se 1 (by rfl) ⟨52338635, by rfl⟩ : syracuseStep 69784847 = 104677271) B104677271
theorem B3626369 : Blo 1072617 3626369 := bstep (se 2 (by rfl) ⟨1359888, by rfl⟩ : syracuseStep 3626369 = 2719777) B2719777
theorem B6116903 : Blo 1072617 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B2414177 : Blo 1072617 2414177 := bstep (se 2 (by rfl) ⟨905316, by rfl⟩ : syracuseStep 2414177 = 1810633) B1810633
theorem B4085437 : Blo 1072617 4085437 := bstep (se 3 (by rfl) ⟨766019, by rfl⟩ : syracuseStep 4085437 = 1532039) B1532039
theorem B3266399 : Blo 1072617 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B2414519 : Blo 1072617 2414519 := bstep (se 1 (by rfl) ⟨1810889, by rfl⟩ : syracuseStep 2414519 = 3621779) B3621779
theorem B3627179 : Blo 1072617 3627179 := bstep (se 1 (by rfl) ⟨2720384, by rfl⟩ : syracuseStep 3627179 = 5440769) B5440769
theorem B5167597 : Blo 1072617 5167597 := bstep (se 3 (by rfl) ⟨968924, by rfl⟩ : syracuseStep 5167597 = 1937849) B1937849
theorem B2415113 : Blo 1072617 2415113 := bstep (se 2 (by rfl) ⟨905667, by rfl⟩ : syracuseStep 2415113 = 1811335) B1811335
theorem B4086395 : Blo 1072617 4086395 := bstep (se 1 (by rfl) ⟨3064796, by rfl⟩ : syracuseStep 4086395 = 6129593) B6129593
theorem B3627719 : Blo 1072617 3627719 := bstep (se 1 (by rfl) ⟨2720789, by rfl⟩ : syracuseStep 3627719 = 5441579) B5441579
theorem B2415455 : Blo 1072617 2415455 := bstep (se 1 (by rfl) ⟨1811591, by rfl⟩ : syracuseStep 2415455 = 3623183) B3623183
theorem B9296869 : Blo 1072617 9296869 := bstep (se 4 (by rfl) ⟨871581, by rfl⟩ : syracuseStep 9296869 = 1743163) B1743163
theorem B2415635 : Blo 1072617 2415635 := bstep (se 1 (by rfl) ⟨1811726, by rfl⟩ : syracuseStep 2415635 = 3623453) B3623453
theorem B1531003 : Blo 1072617 1531003 := bstep (se 1 (by rfl) ⟨1148252, by rfl⟩ : syracuseStep 1531003 = 2296505) B2296505
theorem B117857429 : Blo 1072617 117857429 := bstep (se 6 (by rfl) ⟨2762283, by rfl⟩ : syracuseStep 117857429 = 5524567) B5524567
theorem B2579627 : Blo 1072617 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B8150219 : Blo 1072617 8150219 := bstep (se 1 (by rfl) ⟨6112664, by rfl⟩ : syracuseStep 8150219 = 12225329) B12225329
theorem B6118679 : Blo 1072617 6118679 := bstep (se 1 (by rfl) ⟨4589009, by rfl⟩ : syracuseStep 6118679 = 9178019) B9178019
theorem B2415977 : Blo 1072617 2415977 := bstep (se 2 (by rfl) ⟨905991, by rfl⟩ : syracuseStep 2415977 = 1811983) B1811983
theorem B4087169 : Blo 1072617 4087169 := bstep (se 2 (by rfl) ⟨1532688, by rfl⟩ : syracuseStep 4087169 = 3065377) B3065377
theorem B1072679 : Blo 1072617 1072679 := bstep (se 1 (by rfl) ⟨804509, by rfl⟩ : syracuseStep 1072679 = 1609019) B1609019
theorem B3628583 : Blo 1072617 3628583 := bstep (se 1 (by rfl) ⟨2721437, by rfl⟩ : syracuseStep 3628583 = 5442875) B5442875
theorem B1072719 : Blo 1072617 1072719 := bstep (se 1 (by rfl) ⟨804539, by rfl⟩ : syracuseStep 1072719 = 1609079) B1609079
theorem B1072735 : Blo 1072617 1072735 := bstep (se 1 (by rfl) ⟨804551, by rfl⟩ : syracuseStep 1072735 = 1609103) B1609103
theorem B1072763 : Blo 1072617 1072763 := bstep (se 1 (by rfl) ⟨804572, by rfl⟩ : syracuseStep 1072763 = 1609145) B1609145
theorem B7462523 : Blo 1072617 7462523 := bstep (se 1 (by rfl) ⟨5596892, by rfl⟩ : syracuseStep 7462523 = 11193785) B11193785
theorem B3628691 : Blo 1072617 3628691 := bstep (se 1 (by rfl) ⟨2721518, by rfl⟩ : syracuseStep 3628691 = 5443037) B5443037
theorem B1072815 : Blo 1072617 1072815 := bstep (se 1 (by rfl) ⟨804611, by rfl⟩ : syracuseStep 1072815 = 1609223) B1609223
theorem B1072839 : Blo 1072617 1072839 := bstep (se 1 (by rfl) ⟨804629, by rfl⟩ : syracuseStep 1072839 = 1609259) B1609259
theorem B1072859 : Blo 1072617 1072859 := bstep (se 1 (by rfl) ⟨804644, by rfl⟩ : syracuseStep 1072859 = 1609289) B1609289
theorem B1072935 : Blo 1072617 1072935 := bstep (se 1 (by rfl) ⟨804701, by rfl⟩ : syracuseStep 1072935 = 1609403) B1609403
theorem B1072975 : Blo 1072617 1072975 := bstep (se 1 (by rfl) ⟨804731, by rfl⟩ : syracuseStep 1072975 = 1609463) B1609463
theorem B1072991 : Blo 1072617 1072991 := bstep (se 1 (by rfl) ⟨804743, by rfl⟩ : syracuseStep 1072991 = 1609487) B1609487
theorem B3628907 : Blo 1072617 3628907 := bstep (se 1 (by rfl) ⟨2721680, by rfl⟩ : syracuseStep 3628907 = 5443361) B5443361
theorem B1073019 : Blo 1072617 1073019 := bstep (se 1 (by rfl) ⟨804764, by rfl⟩ : syracuseStep 1073019 = 1609529) B1609529
theorem B3628961 : Blo 1072617 3628961 := bstep (se 2 (by rfl) ⟨1360860, by rfl⟩ : syracuseStep 3628961 = 2721721) B2721721
theorem B1073071 : Blo 1072617 1073071 := bstep (se 1 (by rfl) ⟨804803, by rfl⟩ : syracuseStep 1073071 = 1609607) B1609607
theorem B2416571 : Blo 1072617 2416571 := bstep (se 1 (by rfl) ⟨1812428, by rfl⟩ : syracuseStep 2416571 = 3624857) B3624857
theorem B1073095 : Blo 1072617 1073095 := bstep (se 1 (by rfl) ⟨804821, by rfl⟩ : syracuseStep 1073095 = 1609643) B1609643
theorem B1073115 : Blo 1072617 1073115 := bstep (se 1 (by rfl) ⟨804836, by rfl⟩ : syracuseStep 1073115 = 1609673) B1609673
theorem B1073191 : Blo 1072617 1073191 := bstep (se 1 (by rfl) ⟨804893, by rfl⟩ : syracuseStep 1073191 = 1609787) B1609787
theorem B2416697 : Blo 1072617 2416697 := bstep (se 2 (by rfl) ⟨906261, by rfl⟩ : syracuseStep 2416697 = 1812523) B1812523
theorem B1073231 : Blo 1072617 1073231 := bstep (se 1 (by rfl) ⟨804923, by rfl⟩ : syracuseStep 1073231 = 1609847) B1609847
theorem B1073247 : Blo 1072617 1073247 := bstep (se 1 (by rfl) ⟨804935, by rfl⟩ : syracuseStep 1073247 = 1609871) B1609871
theorem B1073275 : Blo 1072617 1073275 := bstep (se 1 (by rfl) ⟨804956, by rfl⟩ : syracuseStep 1073275 = 1609913) B1609913
theorem B1073327 : Blo 1072617 1073327 := bstep (se 1 (by rfl) ⟨804995, by rfl⟩ : syracuseStep 1073327 = 1609991) B1609991
theorem B1073351 : Blo 1072617 1073351 := bstep (se 1 (by rfl) ⟨805013, by rfl⟩ : syracuseStep 1073351 = 1610027) B1610027
theorem B1073371 : Blo 1072617 1073371 := bstep (se 1 (by rfl) ⟨805028, by rfl⟩ : syracuseStep 1073371 = 1610057) B1610057
theorem B1532153 : Blo 1072617 1532153 := bstep (se 2 (by rfl) ⟨574557, by rfl⟩ : syracuseStep 1532153 = 1149115) B1149115
theorem B1073447 : Blo 1072617 1073447 := bstep (se 1 (by rfl) ⟨805085, by rfl⟩ : syracuseStep 1073447 = 1610171) B1610171
theorem B1073487 : Blo 1072617 1073487 := bstep (se 1 (by rfl) ⟨805115, by rfl⟩ : syracuseStep 1073487 = 1610231) B1610231
theorem B1073503 : Blo 1072617 1073503 := bstep (se 1 (by rfl) ⟨805127, by rfl⟩ : syracuseStep 1073503 = 1610255) B1610255
theorem B1073531 : Blo 1072617 1073531 := bstep (se 1 (by rfl) ⟨805148, by rfl⟩ : syracuseStep 1073531 = 1610297) B1610297
theorem B2417039 : Blo 1072617 2417039 := bstep (se 1 (by rfl) ⟨1812779, by rfl⟩ : syracuseStep 2417039 = 3625559) B3625559
theorem B1073583 : Blo 1072617 1073583 := bstep (se 1 (by rfl) ⟨805187, by rfl⟩ : syracuseStep 1073583 = 1610375) B1610375
theorem B1073607 : Blo 1072617 1073607 := bstep (se 1 (by rfl) ⟨805205, by rfl⟩ : syracuseStep 1073607 = 1610411) B1610411
theorem B1073627 : Blo 1072617 1073627 := bstep (se 1 (by rfl) ⟨805220, by rfl⟩ : syracuseStep 1073627 = 1610441) B1610441
theorem B3629555 : Blo 1072617 3629555 := bstep (se 1 (by rfl) ⟨2722166, by rfl⟩ : syracuseStep 3629555 = 5444333) B5444333
theorem B1073703 : Blo 1072617 1073703 := bstep (se 1 (by rfl) ⟨805277, by rfl⟩ : syracuseStep 1073703 = 1610555) B1610555
theorem B1073743 : Blo 1072617 1073743 := bstep (se 1 (by rfl) ⟨805307, by rfl⟩ : syracuseStep 1073743 = 1610615) B1610615
theorem B1073759 : Blo 1072617 1073759 := bstep (se 1 (by rfl) ⟨805319, by rfl⟩ : syracuseStep 1073759 = 1610639) B1610639
theorem B1073787 : Blo 1072617 1073787 := bstep (se 1 (by rfl) ⟨805340, by rfl⟩ : syracuseStep 1073787 = 1610681) B1610681
theorem B4645511 : Blo 1072617 4645511 := bstep (se 1 (by rfl) ⟨3484133, by rfl⟩ : syracuseStep 4645511 = 6968267) B6968267
theorem B1073839 : Blo 1072617 1073839 := bstep (se 1 (by rfl) ⟨805379, by rfl⟩ : syracuseStep 1073839 = 1610759) B1610759
theorem B1073863 : Blo 1072617 1073863 := bstep (se 1 (by rfl) ⟨805397, by rfl⟩ : syracuseStep 1073863 = 1610795) B1610795
theorem B2417363 : Blo 1072617 2417363 := bstep (se 1 (by rfl) ⟨1813022, by rfl⟩ : syracuseStep 2417363 = 3626045) B3626045
theorem B1073883 : Blo 1072617 1073883 := bstep (se 1 (by rfl) ⟨805412, by rfl⟩ : syracuseStep 1073883 = 1610825) B1610825
theorem B2581241 : Blo 1072617 2581241 := bstep (se 2 (by rfl) ⟨967965, by rfl⟩ : syracuseStep 2581241 = 1935931) B1935931
theorem B1073959 : Blo 1072617 1073959 := bstep (se 1 (by rfl) ⟨805469, by rfl⟩ : syracuseStep 1073959 = 1610939) B1610939
theorem B1073999 : Blo 1072617 1073999 := bstep (se 1 (by rfl) ⟨805499, by rfl⟩ : syracuseStep 1073999 = 1610999) B1610999
theorem B1074015 : Blo 1072617 1074015 := bstep (se 1 (by rfl) ⟨805511, by rfl⟩ : syracuseStep 1074015 = 1611023) B1611023
theorem B1074043 : Blo 1072617 1074043 := bstep (se 1 (by rfl) ⟨805532, by rfl⟩ : syracuseStep 1074043 = 1611065) B1611065
theorem B1074095 : Blo 1072617 1074095 := bstep (se 1 (by rfl) ⟨805571, by rfl⟩ : syracuseStep 1074095 = 1611143) B1611143
theorem B1074119 : Blo 1072617 1074119 := bstep (se 1 (by rfl) ⟨805589, by rfl⟩ : syracuseStep 1074119 = 1611179) B1611179
theorem B1074139 : Blo 1072617 1074139 := bstep (se 1 (by rfl) ⟨805604, by rfl⟩ : syracuseStep 1074139 = 1611209) B1611209
theorem B3630095 : Blo 1072617 3630095 := bstep (se 1 (by rfl) ⟨2722571, by rfl⟩ : syracuseStep 3630095 = 5445143) B5445143
theorem B1074215 : Blo 1072617 1074215 := bstep (se 1 (by rfl) ⟨805661, by rfl⟩ : syracuseStep 1074215 = 1611323) B1611323
theorem B1074255 : Blo 1072617 1074255 := bstep (se 1 (by rfl) ⟨805691, by rfl⟩ : syracuseStep 1074255 = 1611383) B1611383
theorem B1074271 : Blo 1072617 1074271 := bstep (se 1 (by rfl) ⟨805703, by rfl⟩ : syracuseStep 1074271 = 1611407) B1611407
theorem B1074299 : Blo 1072617 1074299 := bstep (se 1 (by rfl) ⟨805724, by rfl⟩ : syracuseStep 1074299 = 1611449) B1611449
theorem B1074351 : Blo 1072617 1074351 := bstep (se 1 (by rfl) ⟨805763, by rfl⟩ : syracuseStep 1074351 = 1611527) B1611527
theorem B1074375 : Blo 1072617 1074375 := bstep (se 1 (by rfl) ⟨805781, by rfl⟩ : syracuseStep 1074375 = 1611563) B1611563
theorem B1074395 : Blo 1072617 1074395 := bstep (se 1 (by rfl) ⟨805796, by rfl⟩ : syracuseStep 1074395 = 1611593) B1611593
theorem B1074471 : Blo 1072617 1074471 := bstep (se 1 (by rfl) ⟨805853, by rfl⟩ : syracuseStep 1074471 = 1611707) B1611707
theorem B1074511 : Blo 1072617 1074511 := bstep (se 1 (by rfl) ⟨805883, by rfl⟩ : syracuseStep 1074511 = 1611767) B1611767
theorem B1074527 : Blo 1072617 1074527 := bstep (se 1 (by rfl) ⟨805895, by rfl⟩ : syracuseStep 1074527 = 1611791) B1611791
theorem B1074555 : Blo 1072617 1074555 := bstep (se 1 (by rfl) ⟨805916, by rfl⟩ : syracuseStep 1074555 = 1611833) B1611833
theorem B11167139 : Blo 1072617 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B1074607 : Blo 1072617 1074607 := bstep (se 1 (by rfl) ⟨805955, by rfl⟩ : syracuseStep 1074607 = 1611911) B1611911
theorem B1074631 : Blo 1072617 1074631 := bstep (se 1 (by rfl) ⟨805973, by rfl⟩ : syracuseStep 1074631 = 1611947) B1611947
theorem B1074651 : Blo 1072617 1074651 := bstep (se 1 (by rfl) ⟨805988, by rfl⟩ : syracuseStep 1074651 = 1611977) B1611977
theorem B1074727 : Blo 1072617 1074727 := bstep (se 1 (by rfl) ⟨806045, by rfl⟩ : syracuseStep 1074727 = 1612091) B1612091
theorem B1074767 : Blo 1072617 1074767 := bstep (se 1 (by rfl) ⟨806075, by rfl⟩ : syracuseStep 1074767 = 1612151) B1612151
theorem B1074783 : Blo 1072617 1074783 := bstep (se 1 (by rfl) ⟨806087, by rfl⟩ : syracuseStep 1074783 = 1612175) B1612175
theorem B3630689 : Blo 1072617 3630689 := bstep (se 2 (by rfl) ⟨1361508, by rfl⟩ : syracuseStep 3630689 = 2723017) B2723017
theorem B2418299 : Blo 1072617 2418299 := bstep (se 1 (by rfl) ⟨1813724, by rfl⟩ : syracuseStep 2418299 = 3627449) B3627449
theorem B1074811 : Blo 1072617 1074811 := bstep (se 1 (by rfl) ⟨806108, by rfl⟩ : syracuseStep 1074811 = 1612217) B1612217
theorem B6973067 : Blo 1072617 6973067 := bstep (se 1 (by rfl) ⟨5229800, by rfl⟩ : syracuseStep 6973067 = 10459601) B10459601
theorem B1074863 : Blo 1072617 1074863 := bstep (se 1 (by rfl) ⟨806147, by rfl⟩ : syracuseStep 1074863 = 1612295) B1612295
theorem B1074887 : Blo 1072617 1074887 := bstep (se 1 (by rfl) ⟨806165, by rfl⟩ : syracuseStep 1074887 = 1612331) B1612331
theorem B1074907 : Blo 1072617 1074907 := bstep (se 1 (by rfl) ⟨806180, by rfl⟩ : syracuseStep 1074907 = 1612361) B1612361
theorem B2418425 : Blo 1072617 2418425 := bstep (se 2 (by rfl) ⟨906909, by rfl⟩ : syracuseStep 2418425 = 1813819) B1813819
theorem B1074983 : Blo 1072617 1074983 := bstep (se 1 (by rfl) ⟨806237, by rfl⟩ : syracuseStep 1074983 = 1612475) B1612475
theorem B5433155 : Blo 1072617 5433155 := bstep (se 1 (by rfl) ⟨4074866, by rfl⟩ : syracuseStep 5433155 = 8149733) B8149733
theorem B1075023 : Blo 1072617 1075023 := bstep (se 1 (by rfl) ⟨806267, by rfl⟩ : syracuseStep 1075023 = 1612535) B1612535
theorem B1075039 : Blo 1072617 1075039 := bstep (se 1 (by rfl) ⟨806279, by rfl⟩ : syracuseStep 1075039 = 1612559) B1612559
theorem B1075067 : Blo 1072617 1075067 := bstep (se 1 (by rfl) ⟨806300, by rfl⟩ : syracuseStep 1075067 = 1612601) B1612601
theorem B1075119 : Blo 1072617 1075119 := bstep (se 1 (by rfl) ⟨806339, by rfl⟩ : syracuseStep 1075119 = 1612679) B1612679
theorem B1075143 : Blo 1072617 1075143 := bstep (se 1 (by rfl) ⟨806357, by rfl⟩ : syracuseStep 1075143 = 1612715) B1612715
theorem B1075163 : Blo 1072617 1075163 := bstep (se 1 (by rfl) ⟨806372, by rfl⟩ : syracuseStep 1075163 = 1612745) B1612745
theorem B2418695 : Blo 1072617 2418695 := bstep (se 1 (by rfl) ⟨1814021, by rfl⟩ : syracuseStep 2418695 = 3628043) B3628043
theorem B1075239 : Blo 1072617 1075239 := bstep (se 1 (by rfl) ⟨806429, by rfl⟩ : syracuseStep 1075239 = 1612859) B1612859
theorem B2418767 : Blo 1072617 2418767 := bstep (se 1 (by rfl) ⟨1814075, by rfl⟩ : syracuseStep 2418767 = 3628151) B3628151
theorem B1075279 : Blo 1072617 1075279 := bstep (se 1 (by rfl) ⟨806459, by rfl⟩ : syracuseStep 1075279 = 1612919) B1612919
theorem B1075295 : Blo 1072617 1075295 := bstep (se 1 (by rfl) ⟨806471, by rfl⟩ : syracuseStep 1075295 = 1612943) B1612943
theorem B1075323 : Blo 1072617 1075323 := bstep (se 1 (by rfl) ⟨806492, by rfl⟩ : syracuseStep 1075323 = 1612985) B1612985
theorem B26142851 : Blo 1072617 26142851 := bstep (se 1 (by rfl) ⟨19607138, by rfl⟩ : syracuseStep 26142851 = 39214277) B39214277
theorem B1075375 : Blo 1072617 1075375 := bstep (se 1 (by rfl) ⟨806531, by rfl⟩ : syracuseStep 1075375 = 1613063) B1613063
theorem B1075399 : Blo 1072617 1075399 := bstep (se 1 (by rfl) ⟨806549, by rfl⟩ : syracuseStep 1075399 = 1613099) B1613099
theorem B1075419 : Blo 1072617 1075419 := bstep (se 1 (by rfl) ⟨806564, by rfl⟩ : syracuseStep 1075419 = 1613129) B1613129
theorem B1075495 : Blo 1072617 1075495 := bstep (se 1 (by rfl) ⟨806621, by rfl⟩ : syracuseStep 1075495 = 1613243) B1613243
theorem B12904753 : Blo 1072617 12904753 := bstep (se 2 (by rfl) ⟨4839282, by rfl⟩ : syracuseStep 12904753 = 9678565) B9678565
theorem B1075535 : Blo 1072617 1075535 := bstep (se 1 (by rfl) ⟨806651, by rfl⟩ : syracuseStep 1075535 = 1613303) B1613303
theorem B1075551 : Blo 1072617 1075551 := bstep (se 1 (by rfl) ⟨806663, by rfl⟩ : syracuseStep 1075551 = 1613327) B1613327
theorem B1075579 : Blo 1072617 1075579 := bstep (se 1 (by rfl) ⟨806684, by rfl⟩ : syracuseStep 1075579 = 1613369) B1613369
theorem B1075631 : Blo 1072617 1075631 := bstep (se 1 (by rfl) ⟨806723, by rfl⟩ : syracuseStep 1075631 = 1613447) B1613447
theorem B1075655 : Blo 1072617 1075655 := bstep (se 1 (by rfl) ⟨806741, by rfl⟩ : syracuseStep 1075655 = 1613483) B1613483
theorem B2419163 : Blo 1072617 2419163 := bstep (se 1 (by rfl) ⟨1814372, by rfl⟩ : syracuseStep 2419163 = 3628745) B3628745
theorem B1075675 : Blo 1072617 1075675 := bstep (se 1 (by rfl) ⟨806756, by rfl⟩ : syracuseStep 1075675 = 1613513) B1613513
theorem B2583049 : Blo 1072617 2583049 := bstep (se 2 (by rfl) ⟨968643, by rfl⟩ : syracuseStep 2583049 = 1937287) B1937287
theorem B8841737 : Blo 1072617 8841737 := bstep (se 2 (by rfl) ⟨3315651, by rfl⟩ : syracuseStep 8841737 = 6631303) B6631303
theorem B10316321 : Blo 1072617 10316321 := bstep (se 2 (by rfl) ⟨3868620, by rfl⟩ : syracuseStep 10316321 = 7737241) B7737241
theorem B1206823 : Blo 1072617 1206823 := bstep (se 1 (by rfl) ⟨905117, by rfl⟩ : syracuseStep 1206823 = 1810235) B1810235
theorem B1075751 : Blo 1072617 1075751 := bstep (se 1 (by rfl) ⟨806813, by rfl⟩ : syracuseStep 1075751 = 1613627) B1613627
theorem B1075791 : Blo 1072617 1075791 := bstep (se 1 (by rfl) ⟨806843, by rfl⟩ : syracuseStep 1075791 = 1613687) B1613687
theorem B1075807 : Blo 1072617 1075807 := bstep (se 1 (by rfl) ⟨806855, by rfl⟩ : syracuseStep 1075807 = 1613711) B1613711
theorem B1075835 : Blo 1072617 1075835 := bstep (se 1 (by rfl) ⟨806876, by rfl⟩ : syracuseStep 1075835 = 1613753) B1613753
theorem B1075887 : Blo 1072617 1075887 := bstep (se 1 (by rfl) ⟨806915, by rfl⟩ : syracuseStep 1075887 = 1613831) B1613831
theorem B1075911 : Blo 1072617 1075911 := bstep (se 1 (by rfl) ⟨806933, by rfl⟩ : syracuseStep 1075911 = 1613867) B1613867
theorem B1075931 : Blo 1072617 1075931 := bstep (se 1 (by rfl) ⟨806948, by rfl⟩ : syracuseStep 1075931 = 1613897) B1613897
theorem B1076007 : Blo 1072617 1076007 := bstep (se 1 (by rfl) ⟨807005, by rfl⟩ : syracuseStep 1076007 = 1614011) B1614011
theorem B1076047 : Blo 1072617 1076047 := bstep (se 1 (by rfl) ⟨807035, by rfl⟩ : syracuseStep 1076047 = 1614071) B1614071
theorem B1076063 : Blo 1072617 1076063 := bstep (se 1 (by rfl) ⟨807047, by rfl⟩ : syracuseStep 1076063 = 1614095) B1614095
theorem B1076091 : Blo 1072617 1076091 := bstep (se 1 (by rfl) ⟨807068, by rfl⟩ : syracuseStep 1076091 = 1614137) B1614137
theorem B2419631 : Blo 1072617 2419631 := bstep (se 1 (by rfl) ⟨1814723, by rfl⟩ : syracuseStep 2419631 = 3629447) B3629447
theorem B1076143 : Blo 1072617 1076143 := bstep (se 1 (by rfl) ⟨807107, by rfl⟩ : syracuseStep 1076143 = 1614215) B1614215
theorem B1076167 : Blo 1072617 1076167 := bstep (se 1 (by rfl) ⟨807125, by rfl⟩ : syracuseStep 1076167 = 1614251) B1614251
theorem B1076187 : Blo 1072617 1076187 := bstep (se 1 (by rfl) ⟨807140, by rfl⟩ : syracuseStep 1076187 = 1614281) B1614281
theorem B2452499 : Blo 1072617 2452499 := bstep (se 1 (by rfl) ⟨1839374, by rfl⟩ : syracuseStep 2452499 = 3678749) B3678749
theorem B3632147 : Blo 1072617 3632147 := bstep (se 1 (by rfl) ⟨2724110, by rfl⟩ : syracuseStep 3632147 = 5448221) B5448221
theorem B1076263 : Blo 1072617 1076263 := bstep (se 1 (by rfl) ⟨807197, by rfl⟩ : syracuseStep 1076263 = 1614395) B1614395
theorem B1076303 : Blo 1072617 1076303 := bstep (se 1 (by rfl) ⟨807227, by rfl⟩ : syracuseStep 1076303 = 1614455) B1614455
theorem B1076319 : Blo 1072617 1076319 := bstep (se 1 (by rfl) ⟨807239, by rfl⟩ : syracuseStep 1076319 = 1614479) B1614479
theorem B1076347 : Blo 1072617 1076347 := bstep (se 1 (by rfl) ⟨807260, by rfl⟩ : syracuseStep 1076347 = 1614521) B1614521
theorem B2419883 : Blo 1072617 2419883 := bstep (se 1 (by rfl) ⟨1814912, by rfl⟩ : syracuseStep 2419883 = 3629825) B3629825
theorem B1076399 : Blo 1072617 1076399 := bstep (se 1 (by rfl) ⟨807299, by rfl⟩ : syracuseStep 1076399 = 1614599) B1614599
theorem B1076423 : Blo 1072617 1076423 := bstep (se 1 (by rfl) ⟨807317, by rfl⟩ : syracuseStep 1076423 = 1614635) B1614635
theorem B1076443 : Blo 1072617 1076443 := bstep (se 1 (by rfl) ⟨807332, by rfl⟩ : syracuseStep 1076443 = 1614665) B1614665
theorem B1076519 : Blo 1072617 1076519 := bstep (se 1 (by rfl) ⟨807389, by rfl⟩ : syracuseStep 1076519 = 1614779) B1614779
theorem B1076559 : Blo 1072617 1076559 := bstep (se 1 (by rfl) ⟨807419, by rfl⟩ : syracuseStep 1076559 = 1614839) B1614839
theorem B3632471 : Blo 1072617 3632471 := bstep (se 1 (by rfl) ⟨2724353, by rfl⟩ : syracuseStep 3632471 = 5448707) B5448707
theorem B1076575 : Blo 1072617 1076575 := bstep (se 1 (by rfl) ⟨807431, by rfl⟩ : syracuseStep 1076575 = 1614863) B1614863
theorem B1076603 : Blo 1072617 1076603 := bstep (se 1 (by rfl) ⟨807452, by rfl⟩ : syracuseStep 1076603 = 1614905) B1614905
theorem B4189819 : Blo 1072617 4189819 := bstep (se 1 (by rfl) ⟨3142364, by rfl⟩ : syracuseStep 4189819 = 6284729) B6284729
theorem B2420423 : Blo 1072617 2420423 := bstep (se 1 (by rfl) ⟨1815317, by rfl⟩ : syracuseStep 2420423 = 3630635) B3630635
theorem B2715727 : Blo 1072617 2715727 := bstep (se 1 (by rfl) ⟨2036795, by rfl⟩ : syracuseStep 2715727 = 4073591) B4073591
theorem B1208443 : Blo 1072617 1208443 := bstep (se 1 (by rfl) ⟨906332, by rfl⟩ : syracuseStep 1208443 = 1812665) B1812665
theorem B3633551 : Blo 1072617 3633551 := bstep (se 1 (by rfl) ⟨2725163, by rfl⟩ : syracuseStep 3633551 = 5450327) B5450327
theorem B2421287 : Blo 1072617 2421287 := bstep (se 1 (by rfl) ⟨1815965, by rfl⟩ : syracuseStep 2421287 = 3631931) B3631931
theorem B1208911 : Blo 1072617 1208911 := bstep (se 1 (by rfl) ⟨906683, by rfl⟩ : syracuseStep 1208911 = 1813367) B1813367
theorem B17429093 : Blo 1072617 17429093 := bstep (se 4 (by rfl) ⟨1633977, by rfl⟩ : syracuseStep 17429093 = 3267955) B3267955
theorem B2716375 : Blo 1072617 2716375 := bstep (se 1 (by rfl) ⟨2037281, by rfl⟩ : syracuseStep 2716375 = 4074563) B4074563
theorem B37286669 : Blo 1072617 37286669 := bstep (se 3 (by rfl) ⟨6991250, by rfl⟩ : syracuseStep 37286669 = 13982501) B13982501
theorem B5436233 : Blo 1072617 5436233 := bstep (se 2 (by rfl) ⟨2038587, by rfl⟩ : syracuseStep 5436233 = 4077175) B4077175
theorem B2421611 : Blo 1072617 2421611 := bstep (se 1 (by rfl) ⟨1816208, by rfl⟩ : syracuseStep 2421611 = 3632417) B3632417
theorem B8156051 : Blo 1072617 8156051 := bstep (se 1 (by rfl) ⟨6117038, by rfl⟩ : syracuseStep 8156051 = 12234077) B12234077
theorem B2421665 : Blo 1072617 2421665 := bstep (se 2 (by rfl) ⟨908124, by rfl⟩ : syracuseStep 2421665 = 1816249) B1816249
theorem B1209307 : Blo 1072617 1209307 := bstep (se 1 (by rfl) ⟨906980, by rfl⟩ : syracuseStep 1209307 = 1813961) B1813961
theorem B2716679 : Blo 1072617 2716679 := bstep (se 1 (by rfl) ⟨2037509, by rfl⟩ : syracuseStep 2716679 = 4075019) B4075019
theorem B17396855 : Blo 1072617 17396855 := bstep (se 1 (by rfl) ⟨13047641, by rfl⟩ : syracuseStep 17396855 = 26095283) B26095283
theorem B16741529 : Blo 1072617 16741529 := bstep (se 2 (by rfl) ⟨6278073, by rfl⟩ : syracuseStep 16741529 = 12556147) B12556147
theorem B2422007 : Blo 1072617 2422007 := bstep (se 1 (by rfl) ⟨1816505, by rfl⟩ : syracuseStep 2422007 = 3633011) B3633011
theorem B1209775 : Blo 1072617 1209775 := bstep (se 1 (by rfl) ⟨907331, by rfl⟩ : syracuseStep 1209775 = 1814663) B1814663
theorem B3438067 : Blo 1072617 3438067 := bstep (se 1 (by rfl) ⟨2578550, by rfl⟩ : syracuseStep 3438067 = 5157101) B5157101
theorem B3438119 : Blo 1072617 3438119 := bstep (se 1 (by rfl) ⟨2578589, by rfl⟩ : syracuseStep 3438119 = 5157179) B5157179
theorem B5895803 : Blo 1072617 5895803 := bstep (se 1 (by rfl) ⟨4421852, by rfl⟩ : syracuseStep 5895803 = 8843705) B8843705
theorem B8157023 : Blo 1072617 8157023 := bstep (se 1 (by rfl) ⟨6117767, by rfl⟩ : syracuseStep 8157023 = 12235535) B12235535
theorem B1210207 : Blo 1072617 1210207 := bstep (se 1 (by rfl) ⟨907655, by rfl⟩ : syracuseStep 1210207 = 1815311) B1815311
theorem B12089249 : Blo 1072617 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B5437529 : Blo 1072617 5437529 := bstep (se 2 (by rfl) ⟨2039073, by rfl⟩ : syracuseStep 5437529 = 4078147) B4078147
theorem B1210567 : Blo 1072617 1210567 := bstep (se 1 (by rfl) ⟨907925, by rfl⟩ : syracuseStep 1210567 = 1815851) B1815851
theorem B16546481 : Blo 1072617 16546481 := bstep (se 2 (by rfl) ⟨6204930, by rfl⟩ : syracuseStep 16546481 = 12409861) B12409861
theorem B15923957 : Blo 1072617 15923957 := bstep (se 5 (by rfl) ⟨746435, by rfl⟩ : syracuseStep 15923957 = 1492871) B1492871
theorem B2718967 : Blo 1072617 2718967 := bstep (se 1 (by rfl) ⟨2039225, by rfl⟩ : syracuseStep 2718967 = 4078451) B4078451
theorem B3865981 : Blo 1072617 3865981 := bstep (se 3 (by rfl) ⟨724871, by rfl⟩ : syracuseStep 3865981 = 1449743) B1449743
theorem B2719241 : Blo 1072617 2719241 := bstep (se 2 (by rfl) ⟨1019715, by rfl⟩ : syracuseStep 2719241 = 2039431) B2039431
theorem B2719271 : Blo 1072617 2719271 := bstep (se 1 (by rfl) ⟨2039453, by rfl⟩ : syracuseStep 2719271 = 4078907) B4078907
theorem B4587131 : Blo 1072617 4587131 := bstep (se 1 (by rfl) ⟨3440348, by rfl⟩ : syracuseStep 4587131 = 6880697) B6880697
theorem B7732883 : Blo 1072617 7732883 := bstep (se 1 (by rfl) ⟨5799662, by rfl⟩ : syracuseStep 7732883 = 11599325) B11599325
theorem B6127427 : Blo 1072617 6127427 := bstep (se 1 (by rfl) ⟨4595570, by rfl⟩ : syracuseStep 6127427 = 9191141) B9191141
theorem B1834859 : Blo 1072617 1834859 := bstep (se 1 (by rfl) ⟨1376144, by rfl⟩ : syracuseStep 1834859 = 2752289) B2752289
theorem B2719595 : Blo 1072617 2719595 := bstep (se 1 (by rfl) ⟨2039696, by rfl⟩ : syracuseStep 2719595 = 4079393) B4079393
theorem B2064865 : Blo 1072617 2064865 := bstep (se 2 (by rfl) ⟨774324, by rfl⟩ : syracuseStep 2064865 = 1548649) B1548649
theorem B5440121 : Blo 1072617 5440121 := bstep (se 2 (by rfl) ⟨2040045, by rfl⟩ : syracuseStep 5440121 = 4080091) B4080091
theorem B6193847 : Blo 1072617 6193847 := bstep (se 1 (by rfl) ⟨4645385, by rfl⟩ : syracuseStep 6193847 = 9290771) B9290771
theorem B12255947 : Blo 1072617 12255947 := bstep (se 1 (by rfl) ⟨9191960, by rfl⟩ : syracuseStep 12255947 = 18383921) B18383921
theorem B1147727 : Blo 1072617 1147727 := bstep (se 1 (by rfl) ⟨860795, by rfl⟩ : syracuseStep 1147727 = 1721591) B1721591
theorem B16548887 : Blo 1072617 16548887 := bstep (se 1 (by rfl) ⟨12411665, by rfl⟩ : syracuseStep 16548887 = 24823331) B24823331
theorem B2720891 : Blo 1072617 2720891 := bstep (se 1 (by rfl) ⟨2040668, by rfl⟩ : syracuseStep 2720891 = 4081337) B4081337
theorem B2720911 : Blo 1072617 2720911 := bstep (se 1 (by rfl) ⟨2040683, by rfl⟩ : syracuseStep 2720911 = 4081367) B4081367
theorem B2294983 : Blo 1072617 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B9798899 : Blo 1072617 9798899 := bstep (se 1 (by rfl) ⟨7349174, by rfl⟩ : syracuseStep 9798899 = 14698349) B14698349
theorem B2721185 : Blo 1072617 2721185 := bstep (se 2 (by rfl) ⟨1020444, by rfl⟩ : syracuseStep 2721185 = 2040889) B2040889
theorem B6883309 : Blo 1072617 6883309 := bstep (se 3 (by rfl) ⟨1290620, by rfl⟩ : syracuseStep 6883309 = 2581241) B2581241
theorem B5441903 : Blo 1072617 5441903 := bstep (se 1 (by rfl) ⟨4081427, by rfl⟩ : syracuseStep 5441903 = 8162855) B8162855
theorem B2755193 : Blo 1072617 2755193 := bstep (se 2 (by rfl) ⟨1033197, by rfl⟩ : syracuseStep 2755193 = 2066395) B2066395
theorem B7736087 : Blo 1072617 7736087 := bstep (se 1 (by rfl) ⟨5802065, by rfl⟩ : syracuseStep 7736087 = 11604131) B11604131
theorem B6884129 : Blo 1072617 6884129 := bstep (se 2 (by rfl) ⟨2581548, by rfl⟩ : syracuseStep 6884129 = 5163097) B5163097
theorem B2296795 : Blo 1072617 2296795 := bstep (se 1 (by rfl) ⟨1722596, by rfl⟩ : syracuseStep 2296795 = 3445193) B3445193
theorem B2722855 : Blo 1072617 2722855 := bstep (se 1 (by rfl) ⟨2042141, by rfl⟩ : syracuseStep 2722855 = 4084283) B4084283
theorem B17206337 : Blo 1072617 17206337 := bstep (se 2 (by rfl) ⟨6452376, by rfl⟩ : syracuseStep 17206337 = 12904753) B12904753
theorem B3444065 : Blo 1072617 3444065 := bstep (se 2 (by rfl) ⟨1291524, by rfl⟩ : syracuseStep 3444065 = 2583049) B2583049
theorem B1838459 : Blo 1072617 1838459 := bstep (se 1 (by rfl) ⟨1378844, by rfl⟩ : syracuseStep 1838459 = 2757689) B2757689
theorem B1609097 : Blo 1072617 1609097 := bstep (se 2 (by rfl) ⟨603411, by rfl⟩ : syracuseStep 1609097 = 1206823) B1206823
theorem B2723321 : Blo 1072617 2723321 := bstep (se 2 (by rfl) ⟨1021245, by rfl⟩ : syracuseStep 2723321 = 2042491) B2042491
theorem B6524425 : Blo 1072617 6524425 := bstep (se 2 (by rfl) ⟨2446659, by rfl⟩ : syracuseStep 6524425 = 4893319) B4893319
theorem B1609451 : Blo 1072617 1609451 := bstep (se 1 (by rfl) ⟨1207088, by rfl⟩ : syracuseStep 1609451 = 2414177) B2414177
theorem B2297641 : Blo 1072617 2297641 := bstep (se 2 (by rfl) ⟨861615, by rfl⟩ : syracuseStep 2297641 = 1723231) B1723231
theorem B1609679 : Blo 1072617 1609679 := bstep (se 1 (by rfl) ⟨1207259, by rfl⟩ : syracuseStep 1609679 = 2414519) B2414519
theorem B2723969 : Blo 1072617 2723969 := bstep (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) B2042977
theorem B1610075 : Blo 1072617 1610075 := bstep (se 1 (by rfl) ⟨1207556, by rfl⟩ : syracuseStep 1610075 = 2415113) B2415113
theorem B2724263 : Blo 1072617 2724263 := bstep (se 1 (by rfl) ⟨2043197, by rfl⟩ : syracuseStep 2724263 = 4086395) B4086395
theorem B1610303 : Blo 1072617 1610303 := bstep (se 1 (by rfl) ⟨1207727, by rfl⟩ : syracuseStep 1610303 = 2415455) B2415455
theorem B2724425 : Blo 1072617 2724425 := bstep (se 2 (by rfl) ⟨1021659, by rfl⟩ : syracuseStep 2724425 = 2043319) B2043319
theorem B1610423 : Blo 1072617 1610423 := bstep (se 1 (by rfl) ⟨1207817, by rfl⟩ : syracuseStep 1610423 = 2415635) B2415635
theorem B1610651 : Blo 1072617 1610651 := bstep (se 1 (by rfl) ⟨1207988, by rfl⟩ : syracuseStep 1610651 = 2415977) B2415977
theorem B2724779 : Blo 1072617 2724779 := bstep (se 1 (by rfl) ⟨2043584, by rfl⟩ : syracuseStep 2724779 = 4087169) B4087169
theorem B2298871 : Blo 1072617 2298871 := bstep (se 1 (by rfl) ⟨1724153, by rfl⟩ : syracuseStep 2298871 = 3448307) B3448307
theorem B2724961 : Blo 1072617 2724961 := bstep (se 2 (by rfl) ⟨1021860, by rfl⟩ : syracuseStep 2724961 = 2043721) B2043721
theorem B1611047 : Blo 1072617 1611047 := bstep (se 1 (by rfl) ⟨1208285, by rfl⟩ : syracuseStep 1611047 = 2416571) B2416571
theorem B1611131 : Blo 1072617 1611131 := bstep (se 1 (by rfl) ⟨1208348, by rfl⟩ : syracuseStep 1611131 = 2416697) B2416697
theorem B6886795 : Blo 1072617 6886795 := bstep (se 1 (by rfl) ⟨5165096, by rfl⟩ : syracuseStep 6886795 = 10330193) B10330193
theorem B1611257 : Blo 1072617 1611257 := bstep (se 2 (by rfl) ⟨604221, by rfl⟩ : syracuseStep 1611257 = 1208443) B1208443
theorem B1611359 : Blo 1072617 1611359 := bstep (se 1 (by rfl) ⟨1208519, by rfl⟩ : syracuseStep 1611359 = 2417039) B2417039
theorem B5445305 : Blo 1072617 5445305 := bstep (se 2 (by rfl) ⟨2041989, by rfl⟩ : syracuseStep 5445305 = 4083979) B4083979
theorem B1611575 : Blo 1072617 1611575 := bstep (se 1 (by rfl) ⟨1208681, by rfl⟩ : syracuseStep 1611575 = 2417363) B2417363
theorem B1611881 : Blo 1072617 1611881 := bstep (se 2 (by rfl) ⟨604455, by rfl⟩ : syracuseStep 1611881 = 1208911) B1208911
theorem B7444759 : Blo 1072617 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B1612199 : Blo 1072617 1612199 := bstep (se 1 (by rfl) ⟨1209149, by rfl⟩ : syracuseStep 1612199 = 2418299) B2418299
theorem B4594103 : Blo 1072617 4594103 := bstep (se 1 (by rfl) ⟨3445577, by rfl⟩ : syracuseStep 4594103 = 6891155) B6891155
theorem B1612283 : Blo 1072617 1612283 := bstep (se 1 (by rfl) ⟨1209212, by rfl⟩ : syracuseStep 1612283 = 2418425) B2418425
theorem B11606591 : Blo 1072617 11606591 := bstep (se 1 (by rfl) ⟨8704943, by rfl⟩ : syracuseStep 11606591 = 17409887) B17409887
theorem B1612409 : Blo 1072617 1612409 := bstep (se 2 (by rfl) ⟨604653, by rfl⟩ : syracuseStep 1612409 = 1209307) B1209307
theorem B1612463 : Blo 1072617 1612463 := bstep (se 1 (by rfl) ⟨1209347, by rfl⟩ : syracuseStep 1612463 = 2418695) B2418695
theorem B1612511 : Blo 1072617 1612511 := bstep (se 1 (by rfl) ⟨1209383, by rfl⟩ : syracuseStep 1612511 = 2418767) B2418767
theorem B1612775 : Blo 1072617 1612775 := bstep (se 1 (by rfl) ⟨1209581, by rfl⟩ : syracuseStep 1612775 = 2419163) B2419163
theorem B1613033 : Blo 1072617 1613033 := bstep (se 2 (by rfl) ⟨604887, by rfl⟩ : syracuseStep 1613033 = 1209775) B1209775
theorem B1613087 : Blo 1072617 1613087 := bstep (se 1 (by rfl) ⟨1209815, by rfl⟩ : syracuseStep 1613087 = 2419631) B2419631
theorem B1613255 : Blo 1072617 1613255 := bstep (se 1 (by rfl) ⟨1209941, by rfl⟩ : syracuseStep 1613255 = 2419883) B2419883
theorem B5447249 : Blo 1072617 5447249 := bstep (se 2 (by rfl) ⟨2042718, by rfl⟩ : syracuseStep 5447249 = 4085437) B4085437
theorem B17440505 : Blo 1072617 17440505 := bstep (se 2 (by rfl) ⟨6540189, by rfl⟩ : syracuseStep 17440505 = 13080379) B13080379
theorem B1613609 : Blo 1072617 1613609 := bstep (se 2 (by rfl) ⟨605103, by rfl⟩ : syracuseStep 1613609 = 1210207) B1210207
theorem B1613615 : Blo 1072617 1613615 := bstep (se 1 (by rfl) ⟨1210211, by rfl⟩ : syracuseStep 1613615 = 2420423) B2420423
theorem B5513017 : Blo 1072617 5513017 := bstep (se 2 (by rfl) ⟨2067381, by rfl⟩ : syracuseStep 5513017 = 4134763) B4134763
theorem B8167229 : Blo 1072617 8167229 := bstep (se 3 (by rfl) ⟨1531355, by rfl⟩ : syracuseStep 8167229 = 3062711) B3062711
theorem B1449959 : Blo 1072617 1449959 := bstep (se 1 (by rfl) ⟨1087469, by rfl⟩ : syracuseStep 1449959 = 2174939) B2174939
theorem B11345939 : Blo 1072617 11345939 := bstep (se 1 (by rfl) ⟨8509454, by rfl⟩ : syracuseStep 11345939 = 17018909) B17018909
theorem B20652083 : Blo 1072617 20652083 := bstep (se 1 (by rfl) ⟨15489062, by rfl⟩ : syracuseStep 20652083 = 30978125) B30978125
theorem B1614089 : Blo 1072617 1614089 := bstep (se 2 (by rfl) ⟨605283, by rfl⟩ : syracuseStep 1614089 = 1210567) B1210567
theorem B1614191 : Blo 1072617 1614191 := bstep (se 1 (by rfl) ⟨1210643, by rfl⟩ : syracuseStep 1614191 = 2421287) B2421287
theorem B1614407 : Blo 1072617 1614407 := bstep (se 1 (by rfl) ⟨1210805, by rfl⟩ : syracuseStep 1614407 = 2421611) B2421611
theorem B1614443 : Blo 1072617 1614443 := bstep (se 1 (by rfl) ⟨1210832, by rfl⟩ : syracuseStep 1614443 = 2421665) B2421665
theorem B1811065 : Blo 1072617 1811065 := bstep (se 2 (by rfl) ⟨679149, by rfl⟩ : syracuseStep 1811065 = 1358299) B1358299
theorem B6890129 : Blo 1072617 6890129 := bstep (se 2 (by rfl) ⟨2583798, by rfl⟩ : syracuseStep 6890129 = 5167597) B5167597
theorem B1811119 : Blo 1072617 1811119 := bstep (se 1 (by rfl) ⟨1358339, by rfl⟩ : syracuseStep 1811119 = 2716679) B2716679
theorem B21504727 : Blo 1072617 21504727 := bstep (se 1 (by rfl) ⟨16128545, by rfl⟩ : syracuseStep 21504727 = 32257091) B32257091
theorem B1614671 : Blo 1072617 1614671 := bstep (se 1 (by rfl) ⟨1211003, by rfl⟩ : syracuseStep 1614671 = 2422007) B2422007
theorem B11609189 : Blo 1072617 11609189 := bstep (se 4 (by rfl) ⟨1088361, by rfl⟩ : syracuseStep 11609189 = 2176723) B2176723
theorem B12395825 : Blo 1072617 12395825 := bstep (se 2 (by rfl) ⟨4648434, by rfl⟩ : syracuseStep 12395825 = 9296869) B9296869
theorem B2041337 : Blo 1072617 2041337 := bstep (se 2 (by rfl) ⟨765501, by rfl⟩ : syracuseStep 2041337 = 1531003) B1531003
theorem B121054763 : Blo 1072617 121054763 := bstep (se 1 (by rfl) ⟨90791072, by rfl⟩ : syracuseStep 121054763 = 181582145) B181582145
theorem B5154641 : Blo 1072617 5154641 := bstep (se 2 (by rfl) ⟨1932990, by rfl⟩ : syracuseStep 5154641 = 3865981) B3865981
theorem B5449679 : Blo 1072617 5449679 := bstep (se 1 (by rfl) ⟨4087259, by rfl⟩ : syracuseStep 5449679 = 8174519) B8174519
theorem B4597793 : Blo 1072617 4597793 := bstep (se 2 (by rfl) ⟨1724172, by rfl⟩ : syracuseStep 4597793 = 3448345) B3448345
theorem B7973057 : Blo 1072617 7973057 := bstep (se 2 (by rfl) ⟨2989896, by rfl⟩ : syracuseStep 7973057 = 5979793) B5979793
theorem B4892957 : Blo 1072617 4892957 := bstep (se 3 (by rfl) ⟨917429, by rfl⟩ : syracuseStep 4892957 = 1834859) B1834859
theorem B1812827 : Blo 1072617 1812827 := bstep (se 1 (by rfl) ⟨1359620, by rfl⟩ : syracuseStep 1812827 = 2719241) B2719241
theorem B1812847 : Blo 1072617 1812847 := bstep (se 1 (by rfl) ⟨1359635, by rfl⟩ : syracuseStep 1812847 = 2719271) B2719271
theorem B3058087 : Blo 1072617 3058087 := bstep (se 1 (by rfl) ⟨2293565, by rfl⟩ : syracuseStep 3058087 = 4587131) B4587131
theorem B5155255 : Blo 1072617 5155255 := bstep (se 1 (by rfl) ⟨3866441, by rfl⟩ : syracuseStep 5155255 = 7732883) B7732883
theorem B26159597 : Blo 1072617 26159597 := bstep (se 3 (by rfl) ⟨4904924, by rfl⟩ : syracuseStep 26159597 = 9809849) B9809849
theorem B4074047 : Blo 1072617 4074047 := bstep (se 1 (by rfl) ⟨3055535, by rfl⟩ : syracuseStep 4074047 = 6111071) B6111071
theorem B1813063 : Blo 1072617 1813063 := bstep (se 1 (by rfl) ⟨1359797, by rfl⟩ : syracuseStep 1813063 = 2719595) B2719595
theorem B4074259 : Blo 1072617 4074259 := bstep (se 1 (by rfl) ⟨3055694, by rfl⟩ : syracuseStep 4074259 = 6111389) B6111389
theorem B4139947 : Blo 1072617 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B2042795 : Blo 1072617 2042795 := bstep (se 1 (by rfl) ⟨1532096, by rfl⟩ : syracuseStep 2042795 = 3064193) B3064193
theorem B1813495 : Blo 1072617 1813495 := bstep (se 1 (by rfl) ⟨1360121, by rfl⟩ : syracuseStep 1813495 = 2720243) B2720243
theorem B3058975 : Blo 1072617 3058975 := bstep (se 1 (by rfl) ⟨2294231, by rfl⟩ : syracuseStep 3058975 = 4588463) B4588463
theorem B1813799 : Blo 1072617 1813799 := bstep (se 1 (by rfl) ⟨1360349, by rfl⟩ : syracuseStep 1813799 = 2720699) B2720699
theorem B14691901 : Blo 1072617 14691901 := bstep (se 3 (by rfl) ⟨2754731, by rfl⟩ : syracuseStep 14691901 = 5509463) B5509463
theorem B8171117 : Blo 1072617 8171117 := bstep (se 3 (by rfl) ⟨1532084, by rfl⟩ : syracuseStep 8171117 = 3064169) B3064169
theorem B1289963 : Blo 1072617 1289963 := bstep (se 1 (by rfl) ⟨967472, by rfl⟩ : syracuseStep 1289963 = 1934945) B1934945
theorem B1814251 : Blo 1072617 1814251 := bstep (se 1 (by rfl) ⟨1360688, by rfl⟩ : syracuseStep 1814251 = 2721377) B2721377
theorem B10334465 : Blo 1072617 10334465 := bstep (se 2 (by rfl) ⟨3875424, by rfl⟩ : syracuseStep 10334465 = 7750849) B7750849
theorem B4895201 : Blo 1072617 4895201 := bstep (se 2 (by rfl) ⟨1835700, by rfl⟩ : syracuseStep 4895201 = 3671401) B3671401
theorem B4076203 : Blo 1072617 4076203 := bstep (se 1 (by rfl) ⟨3057152, by rfl⟩ : syracuseStep 4076203 = 6114305) B6114305
theorem B1815223 : Blo 1072617 1815223 := bstep (se 1 (by rfl) ⟨1361417, by rfl⟩ : syracuseStep 1815223 = 2722835) B2722835
theorem B5812985 : Blo 1072617 5812985 := bstep (se 2 (by rfl) ⟨2179869, by rfl⟩ : syracuseStep 5812985 = 4359739) B4359739
theorem B1291063 : Blo 1072617 1291063 := bstep (se 1 (by rfl) ⟨968297, by rfl⟩ : syracuseStep 1291063 = 1936595) B1936595
theorem B4076507 : Blo 1072617 4076507 := bstep (se 1 (by rfl) ⟨3057380, by rfl⟩ : syracuseStep 4076507 = 6114761) B6114761
theorem B1815527 : Blo 1072617 1815527 := bstep (se 1 (by rfl) ⟨1361645, by rfl⟩ : syracuseStep 1815527 = 2723291) B2723291
theorem B9188477 : Blo 1072617 9188477 := bstep (se 3 (by rfl) ⟨1722839, by rfl⟩ : syracuseStep 9188477 = 3445679) B3445679
theorem B3060935 : Blo 1072617 3060935 := bstep (se 1 (by rfl) ⟨2295701, by rfl⟩ : syracuseStep 3060935 = 4591403) B4591403
theorem B44086517 : Blo 1072617 44086517 := bstep (se 5 (by rfl) ⟨2066555, by rfl⟩ : syracuseStep 44086517 = 4133111) B4133111
theorem B15480065 : Blo 1072617 15480065 := bstep (se 2 (by rfl) ⟨5805024, by rfl⟩ : syracuseStep 15480065 = 11610049) B11610049
theorem B10335883 : Blo 1072617 10335883 := bstep (se 1 (by rfl) ⟨7751912, by rfl⟩ : syracuseStep 10335883 = 15503825) B15503825
theorem B1816681 : Blo 1072617 1816681 := bstep (se 2 (by rfl) ⟨681255, by rfl⟩ : syracuseStep 1816681 = 1362511) B1362511
theorem B4077935 : Blo 1072617 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B1358203 : Blo 1072617 1358203 := bstep (se 1 (by rfl) ⟨1018652, by rfl⟩ : syracuseStep 1358203 = 2037305) B2037305
theorem B2177599 : Blo 1072617 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B3062519 : Blo 1072617 3062519 := bstep (se 1 (by rfl) ⟨2296889, by rfl⟩ : syracuseStep 3062519 = 4593779) B4593779
theorem B18594845 : Blo 1072617 18594845 := bstep (se 3 (by rfl) ⟨3486533, by rfl⟩ : syracuseStep 18594845 = 6973067) B6973067
theorem B1359271 : Blo 1072617 1359271 := bstep (se 1 (by rfl) ⟨1019453, by rfl⟩ : syracuseStep 1359271 = 2038907) B2038907
theorem B5586425 : Blo 1072617 5586425 := bstep (se 2 (by rfl) ⟨2094909, by rfl⟩ : syracuseStep 5586425 = 4189819) B4189819
theorem B4079119 : Blo 1072617 4079119 := bstep (se 1 (by rfl) ⟨3059339, by rfl⟩ : syracuseStep 4079119 = 6118679) B6118679
theorem B1359595 : Blo 1072617 1359595 := bstep (se 1 (by rfl) ⟨1019696, by rfl⟩ : syracuseStep 1359595 = 2039393) B2039393
theorem B1359823 : Blo 1072617 1359823 := bstep (se 1 (by rfl) ⟨1019867, by rfl⟩ : syracuseStep 1359823 = 2039735) B2039735
theorem B3620969 : Blo 1072617 3620969 := bstep (se 2 (by rfl) ⟨1357863, by rfl⟩ : syracuseStep 3620969 = 2715727) B2715727
theorem B1360091 : Blo 1072617 1360091 := bstep (se 1 (by rfl) ⟨1020068, by rfl⟩ : syracuseStep 1360091 = 2040137) B2040137
theorem B19579117 : Blo 1072617 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B2212105 : Blo 1072617 2212105 := bstep (se 2 (by rfl) ⟨829539, by rfl⟩ : syracuseStep 2212105 = 1659079) B1659079
theorem B69714269 : Blo 1072617 69714269 := bstep (se 3 (by rfl) ⟨13071425, by rfl⟩ : syracuseStep 69714269 = 26142851) B26142851
theorem B3097007 : Blo 1072617 3097007 := bstep (se 1 (by rfl) ⟨2322755, by rfl⟩ : syracuseStep 3097007 = 4645511) B4645511
theorem B23511653 : Blo 1072617 23511653 := bstep (se 4 (by rfl) ⟨2204217, by rfl⟩ : syracuseStep 23511653 = 4408435) B4408435
theorem B80724599 : Blo 1072617 80724599 := bstep (se 1 (by rfl) ⟨60543449, by rfl⟩ : syracuseStep 80724599 = 121086899) B121086899
theorem B1360567 : Blo 1072617 1360567 := bstep (se 1 (by rfl) ⟨1020425, by rfl⟩ : syracuseStep 1360567 = 2040851) B2040851
theorem B1360795 : Blo 1072617 1360795 := bstep (se 1 (by rfl) ⟨1020596, by rfl⟩ : syracuseStep 1360795 = 2041193) B2041193
theorem B3621833 : Blo 1072617 3621833 := bstep (se 2 (by rfl) ⟨1358187, by rfl⟩ : syracuseStep 3621833 = 2716375) B2716375
theorem B3064807 : Blo 1072617 3064807 := bstep (se 1 (by rfl) ⟨2298605, by rfl⟩ : syracuseStep 3064807 = 4597211) B4597211
theorem B3622103 : Blo 1072617 3622103 := bstep (se 1 (by rfl) ⟨2716577, by rfl⟩ : syracuseStep 3622103 = 5433155) B5433155
theorem B2016551 : Blo 1072617 2016551 := bstep (se 1 (by rfl) ⟨1512413, by rfl⟩ : syracuseStep 2016551 = 3024827) B3024827
theorem B15516971 : Blo 1072617 15516971 := bstep (se 1 (by rfl) ⟨11637728, by rfl⟩ : syracuseStep 15516971 = 23275457) B23275457
theorem B23577965 : Blo 1072617 23577965 := bstep (se 3 (by rfl) ⟨4420868, by rfl⟩ : syracuseStep 23577965 = 8841737) B8841737
theorem B1361711 : Blo 1072617 1361711 := bstep (se 1 (by rfl) ⟨1021283, by rfl⟩ : syracuseStep 1361711 = 2042567) B2042567
theorem B6211565 : Blo 1072617 6211565 := bstep (se 3 (by rfl) ⟨1164668, by rfl⟩ : syracuseStep 6211565 = 2329337) B2329337
theorem B9193601 : Blo 1072617 9193601 := bstep (se 2 (by rfl) ⟨3447600, by rfl⟩ : syracuseStep 9193601 = 6895201) B6895201
theorem B11619395 : Blo 1072617 11619395 := bstep (se 1 (by rfl) ⟨8714546, by rfl⟩ : syracuseStep 11619395 = 17429093) B17429093
theorem B24857779 : Blo 1072617 24857779 := bstep (se 1 (by rfl) ⟨18643334, by rfl⟩ : syracuseStep 24857779 = 37286669) B37286669
theorem B4902077 : Blo 1072617 4902077 := bstep (se 3 (by rfl) ⟨919139, by rfl⟩ : syracuseStep 4902077 = 1838279) B1838279
theorem B3624155 : Blo 1072617 3624155 := bstep (se 1 (by rfl) ⟨2718116, by rfl⟩ : syracuseStep 3624155 = 5436233) B5436233
theorem B11161019 : Blo 1072617 11161019 := bstep (se 1 (by rfl) ⟨8370764, by rfl⟩ : syracuseStep 11161019 = 16741529) B16741529
theorem B4083281 : Blo 1072617 4083281 := bstep (se 2 (by rfl) ⟨1531230, by rfl⟩ : syracuseStep 4083281 = 3062461) B3062461
theorem B10342187 : Blo 1072617 10342187 := bstep (se 1 (by rfl) ⟨7756640, by rfl⟩ : syracuseStep 10342187 = 15513281) B15513281
theorem B3625019 : Blo 1072617 3625019 := bstep (se 1 (by rfl) ⟨2718764, by rfl⟩ : syracuseStep 3625019 = 5437529) B5437529
theorem B3625289 : Blo 1072617 3625289 := bstep (se 2 (by rfl) ⟨1359483, by rfl⟩ : syracuseStep 3625289 = 2718967) B2718967
theorem B11030987 : Blo 1072617 11030987 := bstep (se 1 (by rfl) ⟨8273240, by rfl⟩ : syracuseStep 11030987 = 16546481) B16546481
theorem B39703159 : Blo 1072617 39703159 := bstep (se 1 (by rfl) ⟨29777369, by rfl⟩ : syracuseStep 39703159 = 59554739) B59554739
theorem B4969183 : Blo 1072617 4969183 := bstep (se 1 (by rfl) ⟨3726887, by rfl⟩ : syracuseStep 4969183 = 7453775) B7453775
theorem B2413691 : Blo 1072617 2413691 := bstep (se 1 (by rfl) ⟨1810268, by rfl⟩ : syracuseStep 2413691 = 3620537) B3620537
theorem B3921095 : Blo 1072617 3921095 := bstep (se 1 (by rfl) ⟨2940821, by rfl⟩ : syracuseStep 3921095 = 5881643) B5881643
theorem B4084951 : Blo 1072617 4084951 := bstep (se 1 (by rfl) ⟨3063713, by rfl⟩ : syracuseStep 4084951 = 6127427) B6127427
theorem B2413817 : Blo 1072617 2413817 := bstep (se 2 (by rfl) ⟨905181, by rfl⟩ : syracuseStep 2413817 = 1810363) B1810363
theorem B2413961 : Blo 1072617 2413961 := bstep (se 2 (by rfl) ⟨905235, by rfl⟩ : syracuseStep 2413961 = 1810471) B1810471
theorem B2577851 : Blo 1072617 2577851 := bstep (se 1 (by rfl) ⟨1933388, by rfl⟩ : syracuseStep 2577851 = 3866777) B3866777
theorem B2414087 : Blo 1072617 2414087 := bstep (se 1 (by rfl) ⟨1810565, by rfl⟩ : syracuseStep 2414087 = 3621131) B3621131
theorem B4085255 : Blo 1072617 4085255 := bstep (se 1 (by rfl) ⟨3063941, by rfl⟩ : syracuseStep 4085255 = 6127883) B6127883
theorem B2578081 : Blo 1072617 2578081 := bstep (se 2 (by rfl) ⟨966780, by rfl⟩ : syracuseStep 2578081 = 1933561) B1933561
theorem B2414267 : Blo 1072617 2414267 := bstep (se 1 (by rfl) ⟨1810700, by rfl⟩ : syracuseStep 2414267 = 3621401) B3621401
theorem B2414393 : Blo 1072617 2414393 := bstep (se 2 (by rfl) ⟨905397, by rfl⟩ : syracuseStep 2414393 = 1810795) B1810795
theorem B4085711 : Blo 1072617 4085711 := bstep (se 1 (by rfl) ⟨3064283, by rfl⟩ : syracuseStep 4085711 = 6128567) B6128567
theorem B4085741 : Blo 1072617 4085741 := bstep (se 3 (by rfl) ⟨766076, by rfl⟩ : syracuseStep 4085741 = 1532153) B1532153
theorem B5167289 : Blo 1072617 5167289 := bstep (se 2 (by rfl) ⟨1937733, by rfl⟩ : syracuseStep 5167289 = 3875467) B3875467
theorem B2415023 : Blo 1072617 2415023 := bstep (se 1 (by rfl) ⟨1811267, by rfl⟩ : syracuseStep 2415023 = 3622535) B3622535
theorem B2415059 : Blo 1072617 2415059 := bstep (se 1 (by rfl) ⟨1811294, by rfl⟩ : syracuseStep 2415059 = 3622589) B3622589
theorem B4086227 : Blo 1072617 4086227 := bstep (se 1 (by rfl) ⟨3064670, by rfl⟩ : syracuseStep 4086227 = 6129341) B6129341
theorem B10344955 : Blo 1072617 10344955 := bstep (se 1 (by rfl) ⟨7758716, by rfl⟩ : syracuseStep 10344955 = 15517433) B15517433
theorem B2415167 : Blo 1072617 2415167 := bstep (se 1 (by rfl) ⟨1811375, by rfl⟩ : syracuseStep 2415167 = 3622751) B3622751
theorem B2415275 : Blo 1072617 2415275 := bstep (se 1 (by rfl) ⟨1811456, by rfl⟩ : syracuseStep 2415275 = 3622913) B3622913
theorem B12245741 : Blo 1072617 12245741 := bstep (se 3 (by rfl) ⟨2296076, by rfl⟩ : syracuseStep 12245741 = 4592153) B4592153
theorem B4086683 : Blo 1072617 4086683 := bstep (se 1 (by rfl) ⟨3065012, by rfl⟩ : syracuseStep 4086683 = 6130025) B6130025
theorem B2448359 : Blo 1072617 2448359 := bstep (se 1 (by rfl) ⟨1836269, by rfl⟩ : syracuseStep 2448359 = 3672539) B3672539
theorem B2415815 : Blo 1072617 2415815 := bstep (se 1 (by rfl) ⟨1811861, by rfl⟩ : syracuseStep 2415815 = 3623723) B3623723
theorem B2415995 : Blo 1072617 2415995 := bstep (se 1 (by rfl) ⟨1811996, by rfl⟩ : syracuseStep 2415995 = 3623993) B3623993
theorem B3628475 : Blo 1072617 3628475 := bstep (se 1 (by rfl) ⟨2721356, by rfl⟩ : syracuseStep 3628475 = 5442713) B5442713
theorem B2416121 : Blo 1072617 2416121 := bstep (se 2 (by rfl) ⟨906045, by rfl⟩ : syracuseStep 2416121 = 1812091) B1812091
theorem B1072635 : Blo 1072617 1072635 := bstep (se 1 (by rfl) ⟨804476, by rfl⟩ : syracuseStep 1072635 = 1608953) B1608953
theorem B1072703 : Blo 1072617 1072703 := bstep (se 1 (by rfl) ⟨804527, by rfl⟩ : syracuseStep 1072703 = 1609055) B1609055
theorem B1072711 : Blo 1072617 1072711 := bstep (se 1 (by rfl) ⟨804533, by rfl⟩ : syracuseStep 1072711 = 1609067) B1609067
theorem B2416211 : Blo 1072617 2416211 := bstep (se 1 (by rfl) ⟨1812158, by rfl⟩ : syracuseStep 2416211 = 3624317) B3624317
theorem B1531487 : Blo 1072617 1531487 := bstep (se 1 (by rfl) ⟨1148615, by rfl⟩ : syracuseStep 1531487 = 2297231) B2297231
theorem B1072863 : Blo 1072617 1072863 := bstep (se 1 (by rfl) ⟨804647, by rfl⟩ : syracuseStep 1072863 = 1609295) B1609295
theorem B2416391 : Blo 1072617 2416391 := bstep (se 1 (by rfl) ⟨1812293, by rfl⟩ : syracuseStep 2416391 = 3624587) B3624587
theorem B1072943 : Blo 1072617 1072943 := bstep (se 1 (by rfl) ⟨804707, by rfl⟩ : syracuseStep 1072943 = 1609415) B1609415
theorem B1073051 : Blo 1072617 1073051 := bstep (se 1 (by rfl) ⟨804788, by rfl⟩ : syracuseStep 1073051 = 1609577) B1609577
theorem B1073103 : Blo 1072617 1073103 := bstep (se 1 (by rfl) ⟨804827, by rfl⟩ : syracuseStep 1073103 = 1609655) B1609655
theorem B1073127 : Blo 1072617 1073127 := bstep (se 1 (by rfl) ⟨804845, by rfl⟩ : syracuseStep 1073127 = 1609691) B1609691
theorem B1073439 : Blo 1072617 1073439 := bstep (se 1 (by rfl) ⟨805079, by rfl⟩ : syracuseStep 1073439 = 1610159) B1610159
theorem B1073499 : Blo 1072617 1073499 := bstep (se 1 (by rfl) ⟨805124, by rfl⟩ : syracuseStep 1073499 = 1610249) B1610249
theorem B2417003 : Blo 1072617 2417003 := bstep (se 1 (by rfl) ⟨1812752, by rfl⟩ : syracuseStep 2417003 = 3625505) B3625505
theorem B1073519 : Blo 1072617 1073519 := bstep (se 1 (by rfl) ⟨805139, by rfl⟩ : syracuseStep 1073519 = 1610279) B1610279
theorem B1073575 : Blo 1072617 1073575 := bstep (se 1 (by rfl) ⟨805181, by rfl⟩ : syracuseStep 1073575 = 1610363) B1610363
theorem B1073659 : Blo 1072617 1073659 := bstep (se 1 (by rfl) ⟨805244, by rfl⟩ : syracuseStep 1073659 = 1610489) B1610489
theorem B2417147 : Blo 1072617 2417147 := bstep (se 1 (by rfl) ⟨1812860, by rfl⟩ : syracuseStep 2417147 = 3625721) B3625721
theorem B18375173 : Blo 1072617 18375173 := bstep (se 4 (by rfl) ⟨1722672, by rfl⟩ : syracuseStep 18375173 = 3445345) B3445345
theorem B5431859 : Blo 1072617 5431859 := bstep (se 1 (by rfl) ⟨4073894, by rfl⟩ : syracuseStep 5431859 = 8147789) B8147789
theorem B1073727 : Blo 1072617 1073727 := bstep (se 1 (by rfl) ⟨805295, by rfl⟩ : syracuseStep 1073727 = 1610591) B1610591
theorem B1073735 : Blo 1072617 1073735 := bstep (se 1 (by rfl) ⟨805301, by rfl⟩ : syracuseStep 1073735 = 1610603) B1610603
theorem B2417273 : Blo 1072617 2417273 := bstep (se 2 (by rfl) ⟨906477, by rfl⟩ : syracuseStep 2417273 = 1812955) B1812955
theorem B2417327 : Blo 1072617 2417327 := bstep (se 1 (by rfl) ⟨1812995, by rfl⟩ : syracuseStep 2417327 = 3625991) B3625991
theorem B5169863 : Blo 1072617 5169863 := bstep (se 1 (by rfl) ⟨3877397, by rfl⟩ : syracuseStep 5169863 = 7754795) B7754795
theorem B1073887 : Blo 1072617 1073887 := bstep (se 1 (by rfl) ⟨805415, by rfl⟩ : syracuseStep 1073887 = 1610831) B1610831
theorem B2417399 : Blo 1072617 2417399 := bstep (se 1 (by rfl) ⟨1813049, by rfl⟩ : syracuseStep 2417399 = 3626099) B3626099
theorem B1073967 : Blo 1072617 1073967 := bstep (se 1 (by rfl) ⟨805475, by rfl⟩ : syracuseStep 1073967 = 1610951) B1610951
theorem B46523231 : Blo 1072617 46523231 := bstep (se 1 (by rfl) ⟨34892423, by rfl⟩ : syracuseStep 46523231 = 69784847) B69784847
theorem B1074075 : Blo 1072617 1074075 := bstep (se 1 (by rfl) ⟨805556, by rfl⟩ : syracuseStep 1074075 = 1611113) B1611113
theorem B2417579 : Blo 1072617 2417579 := bstep (se 1 (by rfl) ⟨1813184, by rfl⟩ : syracuseStep 2417579 = 3626369) B3626369
theorem B1074127 : Blo 1072617 1074127 := bstep (se 1 (by rfl) ⟨805595, by rfl⟩ : syracuseStep 1074127 = 1611191) B1611191
theorem B1074151 : Blo 1072617 1074151 := bstep (se 1 (by rfl) ⟨805613, by rfl⟩ : syracuseStep 1074151 = 1611227) B1611227
theorem B2581703 : Blo 1072617 2581703 := bstep (se 1 (by rfl) ⟨1936277, by rfl⟩ : syracuseStep 2581703 = 3872555) B3872555
theorem B2581723 : Blo 1072617 2581723 := bstep (se 1 (by rfl) ⟨1936292, by rfl⟩ : syracuseStep 2581723 = 3872585) B3872585
theorem B1074463 : Blo 1072617 1074463 := bstep (se 1 (by rfl) ⟨805847, by rfl⟩ : syracuseStep 1074463 = 1611695) B1611695
theorem B2581799 : Blo 1072617 2581799 := bstep (se 1 (by rfl) ⟨1936349, by rfl⟩ : syracuseStep 2581799 = 3872699) B3872699
theorem B1074523 : Blo 1072617 1074523 := bstep (se 1 (by rfl) ⟨805892, by rfl⟩ : syracuseStep 1074523 = 1611785) B1611785
theorem B1074543 : Blo 1072617 1074543 := bstep (se 1 (by rfl) ⟨805907, by rfl⟩ : syracuseStep 1074543 = 1611815) B1611815
theorem B1074599 : Blo 1072617 1074599 := bstep (se 1 (by rfl) ⟨805949, by rfl⟩ : syracuseStep 1074599 = 1611899) B1611899
theorem B2418119 : Blo 1072617 2418119 := bstep (se 1 (by rfl) ⟨1813589, by rfl⟩ : syracuseStep 2418119 = 3627179) B3627179
theorem B1074683 : Blo 1072617 1074683 := bstep (se 1 (by rfl) ⟨806012, by rfl⟩ : syracuseStep 1074683 = 1612025) B1612025
theorem B1074751 : Blo 1072617 1074751 := bstep (se 1 (by rfl) ⟨806063, by rfl⟩ : syracuseStep 1074751 = 1612127) B1612127
theorem B1074759 : Blo 1072617 1074759 := bstep (se 1 (by rfl) ⟨806069, by rfl⟩ : syracuseStep 1074759 = 1612139) B1612139
theorem B5662297 : Blo 1072617 5662297 := bstep (se 2 (by rfl) ⟨2123361, by rfl⟩ : syracuseStep 5662297 = 4246723) B4246723
theorem B9791165 : Blo 1072617 9791165 := bstep (se 3 (by rfl) ⟨1835843, by rfl⟩ : syracuseStep 9791165 = 3671687) B3671687
theorem B1074911 : Blo 1072617 1074911 := bstep (se 1 (by rfl) ⟨806183, by rfl⟩ : syracuseStep 1074911 = 1612367) B1612367
theorem B2418479 : Blo 1072617 2418479 := bstep (se 1 (by rfl) ⟨1813859, by rfl⟩ : syracuseStep 2418479 = 3627719) B3627719
theorem B1074991 : Blo 1072617 1074991 := bstep (se 1 (by rfl) ⟨806243, by rfl⟩ : syracuseStep 1074991 = 1612487) B1612487
theorem B1075099 : Blo 1072617 1075099 := bstep (se 1 (by rfl) ⟨806324, by rfl⟩ : syracuseStep 1075099 = 1612649) B1612649
theorem B1075151 : Blo 1072617 1075151 := bstep (se 1 (by rfl) ⟨806363, by rfl⟩ : syracuseStep 1075151 = 1612727) B1612727
theorem B1075175 : Blo 1072617 1075175 := bstep (se 1 (by rfl) ⟨806381, by rfl⟩ : syracuseStep 1075175 = 1612763) B1612763
theorem B78571619 : Blo 1072617 78571619 := bstep (se 1 (by rfl) ⟨58928714, by rfl⟩ : syracuseStep 78571619 = 117857429) B117857429
theorem B9791603 : Blo 1072617 9791603 := bstep (se 1 (by rfl) ⟨7343702, by rfl⟩ : syracuseStep 9791603 = 14687405) B14687405
theorem B5433479 : Blo 1072617 5433479 := bstep (se 1 (by rfl) ⟨4075109, by rfl⟩ : syracuseStep 5433479 = 8150219) B8150219
theorem B1075487 : Blo 1072617 1075487 := bstep (se 1 (by rfl) ⟨806615, by rfl⟩ : syracuseStep 1075487 = 1613231) B1613231
theorem B1075547 : Blo 1072617 1075547 := bstep (se 1 (by rfl) ⟨806660, by rfl⟩ : syracuseStep 1075547 = 1613321) B1613321
theorem B2419055 : Blo 1072617 2419055 := bstep (se 1 (by rfl) ⟨1814291, by rfl⟩ : syracuseStep 2419055 = 3628583) B3628583
theorem B1075567 : Blo 1072617 1075567 := bstep (se 1 (by rfl) ⟨806675, by rfl⟩ : syracuseStep 1075567 = 1613351) B1613351
theorem B1075623 : Blo 1072617 1075623 := bstep (se 1 (by rfl) ⟨806717, by rfl⟩ : syracuseStep 1075623 = 1613435) B1613435
theorem B4975015 : Blo 1072617 4975015 := bstep (se 1 (by rfl) ⟨3731261, by rfl⟩ : syracuseStep 4975015 = 7462523) B7462523
theorem B2419127 : Blo 1072617 2419127 := bstep (se 1 (by rfl) ⟨1814345, by rfl⟩ : syracuseStep 2419127 = 3628691) B3628691
theorem B4352507 : Blo 1072617 4352507 := bstep (se 1 (by rfl) ⟨3264380, by rfl⟩ : syracuseStep 4352507 = 6528761) B6528761
theorem B1075707 : Blo 1072617 1075707 := bstep (se 1 (by rfl) ⟨806780, by rfl⟩ : syracuseStep 1075707 = 1613561) B1613561
theorem B1075775 : Blo 1072617 1075775 := bstep (se 1 (by rfl) ⟨806831, by rfl⟩ : syracuseStep 1075775 = 1613663) B1613663
theorem B2419271 : Blo 1072617 2419271 := bstep (se 1 (by rfl) ⟨1814453, by rfl⟩ : syracuseStep 2419271 = 3628907) B3628907
theorem B1075783 : Blo 1072617 1075783 := bstep (se 1 (by rfl) ⟨806837, by rfl⟩ : syracuseStep 1075783 = 1613675) B1613675
theorem B2419307 : Blo 1072617 2419307 := bstep (se 1 (by rfl) ⟨1814480, by rfl⟩ : syracuseStep 2419307 = 3628961) B3628961
theorem B1075935 : Blo 1072617 1075935 := bstep (se 1 (by rfl) ⟨806951, by rfl⟩ : syracuseStep 1075935 = 1613903) B1613903
theorem B1076015 : Blo 1072617 1076015 := bstep (se 1 (by rfl) ⟨807011, by rfl⟩ : syracuseStep 1076015 = 1614023) B1614023
theorem B1076123 : Blo 1072617 1076123 := bstep (se 1 (by rfl) ⟨807092, by rfl⟩ : syracuseStep 1076123 = 1614185) B1614185
theorem B1076175 : Blo 1072617 1076175 := bstep (se 1 (by rfl) ⟨807131, by rfl⟩ : syracuseStep 1076175 = 1614263) B1614263
theorem B1076199 : Blo 1072617 1076199 := bstep (se 1 (by rfl) ⟨807149, by rfl⟩ : syracuseStep 1076199 = 1614299) B1614299
theorem B2419703 : Blo 1072617 2419703 := bstep (se 1 (by rfl) ⟨1814777, by rfl⟩ : syracuseStep 2419703 = 3629555) B3629555
theorem B1076511 : Blo 1072617 1076511 := bstep (se 1 (by rfl) ⟨807383, by rfl⟩ : syracuseStep 1076511 = 1614767) B1614767
theorem B1076571 : Blo 1072617 1076571 := bstep (se 1 (by rfl) ⟨807428, by rfl⟩ : syracuseStep 1076571 = 1614857) B1614857
theorem B2420063 : Blo 1072617 2420063 := bstep (se 1 (by rfl) ⟨1815047, by rfl⟩ : syracuseStep 2420063 = 3630095) B3630095
theorem B1076591 : Blo 1072617 1076591 := bstep (se 1 (by rfl) ⟨807443, by rfl⟩ : syracuseStep 1076591 = 1614887) B1614887
theorem B2715079 : Blo 1072617 2715079 := bstep (se 1 (by rfl) ⟨2036309, by rfl⟩ : syracuseStep 2715079 = 4072619) B4072619
theorem B3632633 : Blo 1072617 3632633 := bstep (se 2 (by rfl) ⟨1362237, by rfl⟩ : syracuseStep 3632633 = 2724475) B2724475
theorem B1207903 : Blo 1072617 1207903 := bstep (se 1 (by rfl) ⟨905927, by rfl⟩ : syracuseStep 1207903 = 1811855) B1811855
theorem B2420459 : Blo 1072617 2420459 := bstep (se 1 (by rfl) ⟨1815344, by rfl⟩ : syracuseStep 2420459 = 3630689) B3630689
theorem B3632903 : Blo 1072617 3632903 := bstep (se 1 (by rfl) ⟨2724677, by rfl⟩ : syracuseStep 3632903 = 5449355) B5449355
theorem B3632957 : Blo 1072617 3632957 := bstep (se 3 (by rfl) ⟨681179, by rfl⟩ : syracuseStep 3632957 = 1362359) B1362359
theorem B2420585 : Blo 1072617 2420585 := bstep (se 2 (by rfl) ⟨907719, by rfl⟩ : syracuseStep 2420585 = 1815439) B1815439
theorem B6877547 : Blo 1072617 6877547 := bstep (se 1 (by rfl) ⟨5158160, by rfl⟩ : syracuseStep 6877547 = 10316321) B10316321
theorem B42463885 : Blo 1072617 42463885 := bstep (se 3 (by rfl) ⟨7961978, by rfl⟩ : syracuseStep 42463885 = 15923957) B15923957
theorem B4584089 : Blo 1072617 4584089 := bstep (se 2 (by rfl) ⟨1719033, by rfl⟩ : syracuseStep 4584089 = 3438067) B3438067
theorem B1634999 : Blo 1072617 1634999 := bstep (se 1 (by rfl) ⟨1226249, by rfl⟩ : syracuseStep 1634999 = 2452499) B2452499
theorem B2421431 : Blo 1072617 2421431 := bstep (se 1 (by rfl) ⟨1816073, by rfl⟩ : syracuseStep 2421431 = 3632147) B3632147
theorem B1209055 : Blo 1072617 1209055 := bstep (se 1 (by rfl) ⟨906791, by rfl⟩ : syracuseStep 1209055 = 1813583) B1813583
theorem B2421647 : Blo 1072617 2421647 := bstep (se 1 (by rfl) ⟨1816235, by rfl⟩ : syracuseStep 2421647 = 3632471) B3632471
theorem B2716811 : Blo 1072617 2716811 := bstep (se 1 (by rfl) ⟨2037608, by rfl⟩ : syracuseStep 2716811 = 4075217) B4075217
theorem B1209631 : Blo 1072617 1209631 := bstep (se 1 (by rfl) ⟨907223, by rfl⟩ : syracuseStep 1209631 = 1814447) B1814447
theorem B2717023 : Blo 1072617 2717023 := bstep (se 1 (by rfl) ⟨2037767, by rfl⟩ : syracuseStep 2717023 = 4075535) B4075535
theorem B2291105 : Blo 1072617 2291105 := bstep (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) B1718329
theorem B11630117 : Blo 1072617 11630117 := bstep (se 4 (by rfl) ⟨1090323, by rfl⟩ : syracuseStep 11630117 = 2180647) B2180647
theorem B1209919 : Blo 1072617 1209919 := bstep (se 1 (by rfl) ⟨907439, by rfl⟩ : syracuseStep 1209919 = 1814879) B1814879
theorem B2422367 : Blo 1072617 2422367 := bstep (se 1 (by rfl) ⟨1816775, by rfl⟩ : syracuseStep 2422367 = 3633551) B3633551
theorem B6879005 : Blo 1072617 6879005 := bstep (se 3 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 6879005 = 2579627) B2579627
theorem B5437367 : Blo 1072617 5437367 := bstep (se 1 (by rfl) ⟨4078025, by rfl⟩ : syracuseStep 5437367 = 8156051) B8156051
theorem B11597903 : Blo 1072617 11597903 := bstep (se 1 (by rfl) ⟨8698427, by rfl⟩ : syracuseStep 11597903 = 17396855) B17396855
theorem B2292079 : Blo 1072617 2292079 := bstep (se 1 (by rfl) ⟨1719059, by rfl⟩ : syracuseStep 2292079 = 3438119) B3438119
theorem B1210747 : Blo 1072617 1210747 := bstep (se 1 (by rfl) ⟨908060, by rfl⟩ : syracuseStep 1210747 = 1816121) B1816121
theorem B3930535 : Blo 1072617 3930535 := bstep (se 1 (by rfl) ⟨2947901, by rfl⟩ : syracuseStep 3930535 = 5895803) B5895803
theorem B5438015 : Blo 1072617 5438015 := bstep (se 1 (by rfl) ⟨4078511, by rfl⟩ : syracuseStep 5438015 = 8157023) B8157023
theorem B11041343 : Blo 1072617 11041343 := bstep (se 1 (by rfl) ⟨8281007, by rfl⟩ : syracuseStep 11041343 = 16562015) B16562015
theorem B8059499 : Blo 1072617 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B2325113 : Blo 1072617 2325113 := bstep (se 2 (by rfl) ⟨871917, by rfl⟩ : syracuseStep 2325113 = 1743835) B1743835
theorem B2718431 : Blo 1072617 2718431 := bstep (se 1 (by rfl) ⟨2038823, by rfl⟩ : syracuseStep 2718431 = 4077647) B4077647
theorem B10320659 : Blo 1072617 10320659 := bstep (se 1 (by rfl) ⟨7740494, by rfl⟩ : syracuseStep 10320659 = 15480989) B15480989
theorem B104627447 : Blo 1072617 104627447 := bstep (se 1 (by rfl) ⟨78470585, by rfl⟩ : syracuseStep 104627447 = 156941171) B156941171
theorem B3866429 : Blo 1072617 3866429 := bstep (se 3 (by rfl) ⟨724955, by rfl⟩ : syracuseStep 3866429 = 1449911) B1449911
theorem B2293609 : Blo 1072617 2293609 := bstep (se 2 (by rfl) ⟨860103, by rfl⟩ : syracuseStep 2293609 = 1720207) B1720207
theorem B2064671 : Blo 1072617 2064671 := bstep (se 1 (by rfl) ⟨1548503, by rfl⟩ : syracuseStep 2064671 = 3097007) B3097007
theorem B2949473 : Blo 1072617 2949473 := bstep (se 2 (by rfl) ⟨1106052, by rfl⟩ : syracuseStep 2949473 = 2212105) B2212105
theorem B4129231 : Blo 1072617 4129231 := bstep (se 1 (by rfl) ⟨3096923, by rfl⟩ : syracuseStep 4129231 = 6193847) B6193847
theorem B2753153 : Blo 1072617 2753153 := bstep (se 2 (by rfl) ⟨1032432, by rfl⟩ : syracuseStep 2753153 = 2064865) B2064865
theorem B1344367 : Blo 1072617 1344367 := bstep (se 1 (by rfl) ⟨1008275, by rfl⟩ : syracuseStep 1344367 = 2016551) B2016551
theorem B28672969 : Blo 1072617 28672969 := bstep (se 2 (by rfl) ⟨10752363, by rfl⟩ : syracuseStep 28672969 = 21504727) B21504727
theorem B6129067 : Blo 1072617 6129067 := bstep (se 1 (by rfl) ⟨4596800, by rfl⟩ : syracuseStep 6129067 = 9193601) B9193601
theorem B3442297 : Blo 1072617 3442297 := bstep (se 2 (by rfl) ⟨1290861, by rfl⟩ : syracuseStep 3442297 = 2581723) B2581723
theorem B4359997 : Blo 1072617 4359997 := bstep (se 3 (by rfl) ⟨817499, by rfl⟩ : syracuseStep 4359997 = 1634999) B1634999
theorem B11470891 : Blo 1072617 11470891 := bstep (se 1 (by rfl) ⟨8603168, by rfl⟩ : syracuseStep 11470891 = 17206337) B17206337
theorem B2296043 : Blo 1072617 2296043 := bstep (se 1 (by rfl) ⟨1722032, by rfl⟩ : syracuseStep 2296043 = 3444065) B3444065
theorem B7440679 : Blo 1072617 7440679 := bstep (se 1 (by rfl) ⟨5580509, by rfl⟩ : syracuseStep 7440679 = 11161019) B11161019
theorem B2722187 : Blo 1072617 2722187 := bstep (se 1 (by rfl) ⟨2041640, by rfl⟩ : syracuseStep 2722187 = 4083281) B4083281
theorem B9177745 : Blo 1072617 9177745 := bstep (se 2 (by rfl) ⟨3441654, by rfl⟩ : syracuseStep 9177745 = 6883309) B6883309
theorem B10456253 : Blo 1072617 10456253 := bstep (se 3 (by rfl) ⟨1960547, by rfl⟩ : syracuseStep 10456253 = 3921095) B3921095
theorem B1609127 : Blo 1072617 1609127 := bstep (se 1 (by rfl) ⟨1206845, by rfl⟩ : syracuseStep 1609127 = 2413691) B2413691
theorem B6884797 : Blo 1072617 6884797 := bstep (se 3 (by rfl) ⟨1290899, by rfl⟩ : syracuseStep 6884797 = 2581799) B2581799
theorem B1609211 : Blo 1072617 1609211 := bstep (se 1 (by rfl) ⟨1206908, by rfl⟩ : syracuseStep 1609211 = 2413817) B2413817
theorem B1609307 : Blo 1072617 1609307 := bstep (se 1 (by rfl) ⟨1206980, by rfl⟩ : syracuseStep 1609307 = 2413961) B2413961
theorem B1609391 : Blo 1072617 1609391 := bstep (se 1 (by rfl) ⟨1207043, by rfl⟩ : syracuseStep 1609391 = 2414087) B2414087
theorem B2723503 : Blo 1072617 2723503 := bstep (se 1 (by rfl) ⟨2042627, by rfl⟩ : syracuseStep 2723503 = 4085255) B4085255
theorem B1609511 : Blo 1072617 1609511 := bstep (se 1 (by rfl) ⟨1207133, by rfl⟩ : syracuseStep 1609511 = 2414267) B2414267
theorem B1609595 : Blo 1072617 1609595 := bstep (se 1 (by rfl) ⟨1207196, by rfl⟩ : syracuseStep 1609595 = 2414393) B2414393
theorem B2723807 : Blo 1072617 2723807 := bstep (se 1 (by rfl) ⟨2042855, by rfl⟩ : syracuseStep 2723807 = 4085711) B4085711
theorem B2723827 : Blo 1072617 2723827 := bstep (se 1 (by rfl) ⟨2042870, by rfl⟩ : syracuseStep 2723827 = 4085741) B4085741
theorem B3444859 : Blo 1072617 3444859 := bstep (se 1 (by rfl) ⟨2583644, by rfl⟩ : syracuseStep 3444859 = 5167289) B5167289
theorem B1610015 : Blo 1072617 1610015 := bstep (se 1 (by rfl) ⟨1207511, by rfl⟩ : syracuseStep 1610015 = 2415023) B2415023
theorem B1610039 : Blo 1072617 1610039 := bstep (se 1 (by rfl) ⟨1207529, by rfl⟩ : syracuseStep 1610039 = 2415059) B2415059
theorem B2724151 : Blo 1072617 2724151 := bstep (se 1 (by rfl) ⟨2043113, by rfl⟩ : syracuseStep 2724151 = 4086227) B4086227
theorem B1610111 : Blo 1072617 1610111 := bstep (se 1 (by rfl) ⟨1207583, by rfl⟩ : syracuseStep 1610111 = 2415167) B2415167
theorem B7737727 : Blo 1072617 7737727 := bstep (se 1 (by rfl) ⟨5803295, by rfl⟩ : syracuseStep 7737727 = 11606591) B11606591
theorem B1610183 : Blo 1072617 1610183 := bstep (se 1 (by rfl) ⟨1207637, by rfl⟩ : syracuseStep 1610183 = 2415275) B2415275
theorem B8163827 : Blo 1072617 8163827 := bstep (se 1 (by rfl) ⟨6122870, by rfl⟩ : syracuseStep 8163827 = 12245741) B12245741
theorem B2724455 : Blo 1072617 2724455 := bstep (se 1 (by rfl) ⟨2043341, by rfl⟩ : syracuseStep 2724455 = 4086683) B4086683
theorem B1610537 : Blo 1072617 1610537 := bstep (se 2 (by rfl) ⟨603951, by rfl⟩ : syracuseStep 1610537 = 1207903) B1207903
theorem B1610543 : Blo 1072617 1610543 := bstep (se 1 (by rfl) ⟨1207907, by rfl⟩ : syracuseStep 1610543 = 2415815) B2415815
theorem B1610663 : Blo 1072617 1610663 := bstep (se 1 (by rfl) ⟨1207997, by rfl⟩ : syracuseStep 1610663 = 2415995) B2415995
theorem B1610747 : Blo 1072617 1610747 := bstep (se 1 (by rfl) ⟨1208060, by rfl⟩ : syracuseStep 1610747 = 2416121) B2416121
theorem B1610807 : Blo 1072617 1610807 := bstep (se 1 (by rfl) ⟨1208105, by rfl⟩ : syracuseStep 1610807 = 2416211) B2416211
theorem B1610927 : Blo 1072617 1610927 := bstep (se 1 (by rfl) ⟨1208195, by rfl⟩ : syracuseStep 1610927 = 2416391) B2416391
theorem B5444819 : Blo 1072617 5444819 := bstep (se 1 (by rfl) ⟨4083614, by rfl⟩ : syracuseStep 5444819 = 8167229) B8167229
theorem B13768055 : Blo 1072617 13768055 := bstep (se 1 (by rfl) ⟨10326041, by rfl⟩ : syracuseStep 13768055 = 20652083) B20652083
theorem B1611335 : Blo 1072617 1611335 := bstep (se 1 (by rfl) ⟨1208501, by rfl⟩ : syracuseStep 1611335 = 2417003) B2417003
theorem B1611431 : Blo 1072617 1611431 := bstep (se 1 (by rfl) ⟨1208573, by rfl⟩ : syracuseStep 1611431 = 2417147) B2417147
theorem B1611515 : Blo 1072617 1611515 := bstep (se 1 (by rfl) ⟨1208636, by rfl⟩ : syracuseStep 1611515 = 2417273) B2417273
theorem B4593419 : Blo 1072617 4593419 := bstep (se 1 (by rfl) ⟨3445064, by rfl⟩ : syracuseStep 4593419 = 6890129) B6890129
theorem B1611551 : Blo 1072617 1611551 := bstep (se 1 (by rfl) ⟨1208663, by rfl⟩ : syracuseStep 1611551 = 2417327) B2417327
theorem B1611599 : Blo 1072617 1611599 := bstep (se 1 (by rfl) ⟨1208699, by rfl⟩ : syracuseStep 1611599 = 2417399) B2417399
theorem B1611719 : Blo 1072617 1611719 := bstep (se 1 (by rfl) ⟨1208789, by rfl⟩ : syracuseStep 1611719 = 2417579) B2417579
theorem B7739459 : Blo 1072617 7739459 := bstep (se 1 (by rfl) ⟨5804594, by rfl⟩ : syracuseStep 7739459 = 11609189) B11609189
theorem B8263883 : Blo 1072617 8263883 := bstep (se 1 (by rfl) ⟨6197912, by rfl⟩ : syracuseStep 8263883 = 12395825) B12395825
theorem B1612073 : Blo 1072617 1612073 := bstep (se 2 (by rfl) ⟨604527, by rfl⟩ : syracuseStep 1612073 = 1209055) B1209055
theorem B6625577 : Blo 1072617 6625577 := bstep (se 2 (by rfl) ⟨2484591, by rfl⟩ : syracuseStep 6625577 = 4969183) B4969183
theorem B1612079 : Blo 1072617 1612079 := bstep (se 1 (by rfl) ⟨1209059, by rfl⟩ : syracuseStep 1612079 = 2418119) B2418119
theorem B1612319 : Blo 1072617 1612319 := bstep (se 1 (by rfl) ⟨1209239, by rfl⟩ : syracuseStep 1612319 = 2418479) B2418479
theorem B6527735 : Blo 1072617 6527735 := bstep (se 1 (by rfl) ⟨4895801, by rfl⟩ : syracuseStep 6527735 = 9791603) B9791603
theorem B5315371 : Blo 1072617 5315371 := bstep (se 1 (by rfl) ⟨3986528, by rfl⟩ : syracuseStep 5315371 = 7973057) B7973057
theorem B1612703 : Blo 1072617 1612703 := bstep (se 1 (by rfl) ⟨1209527, by rfl⟩ : syracuseStep 1612703 = 2419055) B2419055
theorem B5446601 : Blo 1072617 5446601 := bstep (se 2 (by rfl) ⟨2042475, by rfl⟩ : syracuseStep 5446601 = 4084951) B4084951
theorem B1612751 : Blo 1072617 1612751 := bstep (se 1 (by rfl) ⟨1209563, by rfl⟩ : syracuseStep 1612751 = 2419127) B2419127
theorem B7347181 : Blo 1072617 7347181 := bstep (se 3 (by rfl) ⟨1377596, by rfl⟩ : syracuseStep 7347181 = 2755193) B2755193
theorem B17439731 : Blo 1072617 17439731 := bstep (se 1 (by rfl) ⟨13079798, by rfl⟩ : syracuseStep 17439731 = 26159597) B26159597
theorem B1612841 : Blo 1072617 1612841 := bstep (se 2 (by rfl) ⟨604815, by rfl⟩ : syracuseStep 1612841 = 1209631) B1209631
theorem B1612847 : Blo 1072617 1612847 := bstep (se 1 (by rfl) ⟨1209635, by rfl⟩ : syracuseStep 1612847 = 2419271) B2419271
theorem B1612871 : Blo 1072617 1612871 := bstep (se 1 (by rfl) ⟨1209653, by rfl⟩ : syracuseStep 1612871 = 2419307) B2419307
theorem B9182393 : Blo 1072617 9182393 := bstep (se 2 (by rfl) ⟨3443397, by rfl⟩ : syracuseStep 9182393 = 6886795) B6886795
theorem B1613135 : Blo 1072617 1613135 := bstep (se 1 (by rfl) ⟨1209851, by rfl⟩ : syracuseStep 1613135 = 2419703) B2419703
theorem B1613225 : Blo 1072617 1613225 := bstep (se 2 (by rfl) ⟨604959, by rfl⟩ : syracuseStep 1613225 = 1209919) B1209919
theorem B18357677 : Blo 1072617 18357677 := bstep (se 3 (by rfl) ⟨3442064, by rfl⟩ : syracuseStep 18357677 = 6884129) B6884129
theorem B1613375 : Blo 1072617 1613375 := bstep (se 1 (by rfl) ⟨1210031, by rfl⟩ : syracuseStep 1613375 = 2420063) B2420063
theorem B5447411 : Blo 1072617 5447411 := bstep (se 1 (by rfl) ⟨4085558, by rfl⟩ : syracuseStep 5447411 = 8171117) B8171117
theorem B1613639 : Blo 1072617 1613639 := bstep (se 1 (by rfl) ⟨1210229, by rfl⟩ : syracuseStep 1613639 = 2420459) B2420459
theorem B1613723 : Blo 1072617 1613723 := bstep (se 1 (by rfl) ⟨1210292, by rfl⟩ : syracuseStep 1613723 = 2420585) B2420585
theorem B6889643 : Blo 1072617 6889643 := bstep (se 1 (by rfl) ⟨5167232, by rfl⟩ : syracuseStep 6889643 = 10334465) B10334465
theorem B3056059 : Blo 1072617 3056059 := bstep (se 1 (by rfl) ⟨2292044, by rfl⟩ : syracuseStep 3056059 = 4584089) B4584089
theorem B1614287 : Blo 1072617 1614287 := bstep (se 1 (by rfl) ⟨1210715, by rfl⟩ : syracuseStep 1614287 = 2421431) B2421431
theorem B3056105 : Blo 1072617 3056105 := bstep (se 2 (by rfl) ⟨1146039, by rfl⟩ : syracuseStep 3056105 = 2292079) B2292079
theorem B1810937 : Blo 1072617 1810937 := bstep (se 2 (by rfl) ⟨679101, by rfl⟩ : syracuseStep 1810937 = 1358203) B1358203
theorem B3875323 : Blo 1072617 3875323 := bstep (se 1 (by rfl) ⟨2906492, by rfl⟩ : syracuseStep 3875323 = 5812985) B5812985
theorem B1614329 : Blo 1072617 1614329 := bstep (se 2 (by rfl) ⟨605373, by rfl⟩ : syracuseStep 1614329 = 1210747) B1210747
theorem B1614431 : Blo 1072617 1614431 := bstep (se 1 (by rfl) ⟨1210823, by rfl⟩ : syracuseStep 1614431 = 2421647) B2421647
theorem B1811207 : Blo 1072617 1811207 := bstep (se 1 (by rfl) ⟨1358405, by rfl⟩ : syracuseStep 1811207 = 2716811) B2716811
theorem B2040623 : Blo 1072617 2040623 := bstep (se 1 (by rfl) ⟨1530467, by rfl⟩ : syracuseStep 2040623 = 3060935) B3060935
theorem B1614911 : Blo 1072617 1614911 := bstep (se 1 (by rfl) ⟨1211183, by rfl⟩ : syracuseStep 1614911 = 2422367) B2422367
theorem B1550075 : Blo 1072617 1550075 := bstep (se 1 (by rfl) ⟨1162556, by rfl⟩ : syracuseStep 1550075 = 2325113) B2325113
theorem B1812287 : Blo 1072617 1812287 := bstep (se 1 (by rfl) ⟨1359215, by rfl⟩ : syracuseStep 1812287 = 2718431) B2718431
theorem B2041679 : Blo 1072617 2041679 := bstep (se 1 (by rfl) ⟨1531259, by rfl⟩ : syracuseStep 2041679 = 3062519) B3062519
theorem B1812361 : Blo 1072617 1812361 := bstep (se 2 (by rfl) ⟨679635, by rfl⟩ : syracuseStep 1812361 = 1359271) B1359271
theorem B12396563 : Blo 1072617 12396563 := bstep (se 1 (by rfl) ⟨9297422, by rfl⟩ : syracuseStep 12396563 = 18594845) B18594845
theorem B1812793 : Blo 1072617 1812793 := bstep (se 2 (by rfl) ⟨679797, by rfl⟩ : syracuseStep 1812793 = 1359595) B1359595
theorem B7350689 : Blo 1072617 7350689 := bstep (se 2 (by rfl) ⟨2756508, by rfl⟩ : syracuseStep 7350689 = 5513017) B5513017
theorem B3058145 : Blo 1072617 3058145 := bstep (se 2 (by rfl) ⟨1146804, by rfl⟩ : syracuseStep 3058145 = 2293609) B2293609
theorem B1813097 : Blo 1072617 1813097 := bstep (se 2 (by rfl) ⟨679911, by rfl⟩ : syracuseStep 1813097 = 1359823) B1359823
theorem B46476179 : Blo 1072617 46476179 := bstep (se 1 (by rfl) ⟨34857134, by rfl⟩ : syracuseStep 46476179 = 69714269) B69714269
theorem B15674435 : Blo 1072617 15674435 := bstep (se 1 (by rfl) ⟨11755826, by rfl⟩ : syracuseStep 15674435 = 23511653) B23511653
theorem B53816399 : Blo 1072617 53816399 := bstep (se 1 (by rfl) ⟨40362299, by rfl⟩ : syracuseStep 53816399 = 80724599) B80724599
theorem B8170631 : Blo 1072617 8170631 := bstep (se 1 (by rfl) ⟨6127973, by rfl⟩ : syracuseStep 8170631 = 12255947) B12255947
theorem B1813927 : Blo 1072617 1813927 := bstep (se 1 (by rfl) ⟨1360445, by rfl⟩ : syracuseStep 1813927 = 2720891) B2720891
theorem B1814089 : Blo 1072617 1814089 := bstep (se 2 (by rfl) ⟨680283, by rfl⟩ : syracuseStep 1814089 = 1360567) B1360567
theorem B1814123 : Blo 1072617 1814123 := bstep (se 1 (by rfl) ⟨1360592, by rfl⟩ : syracuseStep 1814123 = 2721185) B2721185
theorem B1814393 : Blo 1072617 1814393 := bstep (se 2 (by rfl) ⟨680397, by rfl⟩ : syracuseStep 1814393 = 1360795) B1360795
theorem B13053869 : Blo 1072617 13053869 := bstep (se 3 (by rfl) ⟨2447600, by rfl⟩ : syracuseStep 13053869 = 4895201) B4895201
theorem B4141043 : Blo 1072617 4141043 := bstep (se 1 (by rfl) ⟨3105782, by rfl⟩ : syracuseStep 4141043 = 6211565) B6211565
theorem B5157391 : Blo 1072617 5157391 := bstep (se 1 (by rfl) ⟨3868043, by rfl⟩ : syracuseStep 5157391 = 7736087) B7736087
theorem B7746263 : Blo 1072617 7746263 := bstep (se 1 (by rfl) ⟨5809697, by rfl⟩ : syracuseStep 7746263 = 11619395) B11619395
theorem B7549729 : Blo 1072617 7549729 := bstep (se 2 (by rfl) ⟨2831148, by rfl⟩ : syracuseStep 7549729 = 5662297) B5662297
theorem B3060605 : Blo 1072617 3060605 := bstep (se 3 (by rfl) ⟨573863, by rfl⟩ : syracuseStep 3060605 = 1147727) B1147727
theorem B1225639 : Blo 1072617 1225639 := bstep (se 1 (by rfl) ⟨919229, by rfl⟩ : syracuseStep 1225639 = 1838459) B1838459
theorem B1815547 : Blo 1072617 1815547 := bstep (se 1 (by rfl) ⟨1361660, by rfl⟩ : syracuseStep 1815547 = 2723321) B2723321
theorem B6894791 : Blo 1072617 6894791 := bstep (se 1 (by rfl) ⟨5171093, by rfl⟩ : syracuseStep 6894791 = 10342187) B10342187
theorem B1815979 : Blo 1072617 1815979 := bstep (se 1 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 1815979 = 2723969) B2723969
theorem B1816175 : Blo 1072617 1816175 := bstep (se 1 (by rfl) ⟨1362131, by rfl⟩ : syracuseStep 1816175 = 2724263) B2724263
theorem B7353991 : Blo 1072617 7353991 := bstep (se 1 (by rfl) ⟨5515493, by rfl⟩ : syracuseStep 7353991 = 11030987) B11030987
theorem B1816283 : Blo 1072617 1816283 := bstep (se 1 (by rfl) ⟨1362212, by rfl⟩ : syracuseStep 1816283 = 2724425) B2724425
theorem B4077449 : Blo 1072617 4077449 := bstep (se 2 (by rfl) ⟨1529043, by rfl⟩ : syracuseStep 4077449 = 3058087) B3058087
theorem B6633353 : Blo 1072617 6633353 := bstep (se 2 (by rfl) ⟨2487507, by rfl⟩ : syracuseStep 6633353 = 4975015) B4975015
theorem B1816519 : Blo 1072617 1816519 := bstep (se 1 (by rfl) ⟨1362389, by rfl⟩ : syracuseStep 1816519 = 2724779) B2724779
theorem B26130397 : Blo 1072617 26130397 := bstep (se 3 (by rfl) ⟨4899449, by rfl⟩ : syracuseStep 26130397 = 9798899) B9798899
theorem B1718567 : Blo 1072617 1718567 := bstep (se 1 (by rfl) ⟨1288925, by rfl⟩ : syracuseStep 1718567 = 2577851) B2577851
theorem B6109613 : Blo 1072617 6109613 := bstep (se 3 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 6109613 = 2291105) B2291105
theorem B5519929 : Blo 1072617 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B3062393 : Blo 1072617 3062393 := bstep (se 2 (by rfl) ⟨1148397, by rfl⟩ : syracuseStep 3062393 = 2296795) B2296795
theorem B33143705 : Blo 1072617 33143705 := bstep (se 2 (by rfl) ⟨12428889, by rfl⟩ : syracuseStep 33143705 = 24857779) B24857779
theorem B3062735 : Blo 1072617 3062735 := bstep (se 1 (by rfl) ⟨2297051, by rfl⟩ : syracuseStep 3062735 = 4594103) B4594103
theorem B4078633 : Blo 1072617 4078633 := bstep (se 2 (by rfl) ⟨1529487, by rfl⟩ : syracuseStep 4078633 = 3058975) B3058975
theorem B3620105 : Blo 1072617 3620105 := bstep (se 2 (by rfl) ⟨1357539, by rfl⟩ : syracuseStep 3620105 = 2715079) B2715079
theorem B8699233 : Blo 1072617 8699233 := bstep (se 2 (by rfl) ⟨3262212, by rfl⟩ : syracuseStep 8699233 = 6524425) B6524425
theorem B3063521 : Blo 1072617 3063521 := bstep (se 2 (by rfl) ⟨1148820, by rfl⟩ : syracuseStep 3063521 = 2297641) B2297641
theorem B3621239 : Blo 1072617 3621239 := bstep (se 1 (by rfl) ⟨2715929, by rfl⟩ : syracuseStep 3621239 = 5431859) B5431859
theorem B31015487 : Blo 1072617 31015487 := bstep (se 1 (by rfl) ⟨23261615, by rfl⟩ : syracuseStep 31015487 = 46523231) B46523231
theorem B1721135 : Blo 1072617 1721135 := bstep (se 1 (by rfl) ⟨1290851, by rfl⟩ : syracuseStep 1721135 = 2581703) B2581703
theorem B52937545 : Blo 1072617 52937545 := bstep (se 2 (by rfl) ⟨19851579, by rfl⟩ : syracuseStep 52937545 = 39703159) B39703159
theorem B1360891 : Blo 1072617 1360891 := bstep (se 1 (by rfl) ⟨1020668, by rfl⟩ : syracuseStep 1360891 = 2041337) B2041337
theorem B12239909 : Blo 1072617 12239909 := bstep (se 4 (by rfl) ⟨1147491, by rfl⟩ : syracuseStep 12239909 = 2294983) B2294983
theorem B1721417 : Blo 1072617 1721417 := bstep (se 2 (by rfl) ⟨645531, by rfl⟩ : syracuseStep 1721417 = 1291063) B1291063
theorem B3065161 : Blo 1072617 3065161 := bstep (se 2 (by rfl) ⟨1149435, by rfl⟩ : syracuseStep 3065161 = 2298871) B2298871
theorem B3065195 : Blo 1072617 3065195 := bstep (se 1 (by rfl) ⟨2298896, by rfl⟩ : syracuseStep 3065195 = 4597793) B4597793
theorem B52381079 : Blo 1072617 52381079 := bstep (se 1 (by rfl) ⟨39285809, by rfl⟩ : syracuseStep 52381079 = 78571619) B78571619
theorem B3622319 : Blo 1072617 3622319 := bstep (se 1 (by rfl) ⟨2716739, by rfl⟩ : syracuseStep 3622319 = 5433479) B5433479
theorem B3261971 : Blo 1072617 3261971 := bstep (se 1 (by rfl) ⟨2446478, by rfl⟩ : syracuseStep 3261971 = 4892957) B4892957
theorem B2901671 : Blo 1072617 2901671 := bstep (se 1 (by rfl) ⟨2176253, by rfl⟩ : syracuseStep 2901671 = 4352507) B4352507
theorem B3622697 : Blo 1072617 3622697 := bstep (se 2 (by rfl) ⟨1358511, by rfl⟩ : syracuseStep 3622697 = 2717023) B2717023
theorem B1361863 : Blo 1072617 1361863 := bstep (se 1 (by rfl) ⟨1021397, by rfl⟩ : syracuseStep 1361863 = 2042795) B2042795
theorem B13781177 : Blo 1072617 13781177 := bstep (se 2 (by rfl) ⟨5167941, by rfl⟩ : syracuseStep 13781177 = 10335883) B10335883
theorem B2903465 : Blo 1072617 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B7753411 : Blo 1072617 7753411 := bstep (se 1 (by rfl) ⟨5815058, by rfl⟩ : syracuseStep 7753411 = 11630117) B11630117
theorem B3624911 : Blo 1072617 3624911 := bstep (se 1 (by rfl) ⟨2718683, by rfl⟩ : syracuseStep 3624911 = 5437367) B5437367
theorem B4083965 : Blo 1072617 4083965 := bstep (se 3 (by rfl) ⟨765743, by rfl⟩ : syracuseStep 4083965 = 1531487) B1531487
theorem B3625343 : Blo 1072617 3625343 := bstep (se 1 (by rfl) ⟨2719007, by rfl⟩ : syracuseStep 3625343 = 5438015) B5438015
theorem B7360895 : Blo 1072617 7360895 := bstep (se 1 (by rfl) ⟨5520671, by rfl⟩ : syracuseStep 7360895 = 11041343) B11041343
theorem B69751631 : Blo 1072617 69751631 := bstep (se 1 (by rfl) ⟨52313723, by rfl⟩ : syracuseStep 69751631 = 104627447) B104627447
theorem B3724283 : Blo 1072617 3724283 := bstep (se 1 (by rfl) ⟨2793212, by rfl⟩ : syracuseStep 3724283 = 5586425) B5586425
theorem B2577619 : Blo 1072617 2577619 := bstep (se 1 (by rfl) ⟨1933214, by rfl⟩ : syracuseStep 2577619 = 3866429) B3866429
theorem B2413979 : Blo 1072617 2413979 := bstep (se 1 (by rfl) ⟨1810484, by rfl⟩ : syracuseStep 2413979 = 3620969) B3620969
theorem B26105489 : Blo 1072617 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B3626747 : Blo 1072617 3626747 := bstep (se 1 (by rfl) ⟨2720060, by rfl⟩ : syracuseStep 3626747 = 5440121) B5440121
theorem B3626909 : Blo 1072617 3626909 := bstep (se 3 (by rfl) ⟨680045, by rfl⟩ : syracuseStep 3626909 = 1360091) B1360091
theorem B2414555 : Blo 1072617 2414555 := bstep (se 1 (by rfl) ⟨1810916, by rfl⟩ : syracuseStep 2414555 = 3621833) B3621833
theorem B2414735 : Blo 1072617 2414735 := bstep (se 1 (by rfl) ⟨1811051, by rfl⟩ : syracuseStep 2414735 = 3622103) B3622103
theorem B2414753 : Blo 1072617 2414753 := bstep (se 2 (by rfl) ⟨905532, by rfl⟩ : syracuseStep 2414753 = 1811065) B1811065
theorem B10344647 : Blo 1072617 10344647 := bstep (se 1 (by rfl) ⟨7758485, by rfl⟩ : syracuseStep 10344647 = 15516971) B15516971
theorem B2414825 : Blo 1072617 2414825 := bstep (se 2 (by rfl) ⟨905559, by rfl⟩ : syracuseStep 2414825 = 1811119) B1811119
theorem B15718643 : Blo 1072617 15718643 := bstep (se 1 (by rfl) ⟨11788982, by rfl⟩ : syracuseStep 15718643 = 23577965) B23577965
theorem B4086409 : Blo 1072617 4086409 := bstep (se 2 (by rfl) ⟨1532403, by rfl⟩ : syracuseStep 4086409 = 3064807) B3064807
theorem B3627881 : Blo 1072617 3627881 := bstep (se 2 (by rfl) ⟨1360455, by rfl⟩ : syracuseStep 3627881 = 2720911) B2720911
theorem B3627935 : Blo 1072617 3627935 := bstep (se 1 (by rfl) ⟨2720951, by rfl⟩ : syracuseStep 3627935 = 5441903) B5441903
theorem B13786301 : Blo 1072617 13786301 := bstep (se 3 (by rfl) ⟨2584931, by rfl⟩ : syracuseStep 13786301 = 5169863) B5169863
theorem B2416103 : Blo 1072617 2416103 := bstep (se 1 (by rfl) ⟨1812077, by rfl⟩ : syracuseStep 2416103 = 3624155) B3624155
theorem B1072731 : Blo 1072617 1072731 := bstep (se 1 (by rfl) ⟨804548, by rfl⟩ : syracuseStep 1072731 = 1609097) B1609097
theorem B1072967 : Blo 1072617 1072967 := bstep (se 1 (by rfl) ⟨804725, by rfl⟩ : syracuseStep 1072967 = 1609451) B1609451
theorem B1073119 : Blo 1072617 1073119 := bstep (se 1 (by rfl) ⟨804839, by rfl⟩ : syracuseStep 1073119 = 1609679) B1609679
theorem B2416679 : Blo 1072617 2416679 := bstep (se 1 (by rfl) ⟨1812509, by rfl⟩ : syracuseStep 2416679 = 3625019) B3625019
theorem B44130365 : Blo 1072617 44130365 := bstep (se 3 (by rfl) ⟨8274443, by rfl⟩ : syracuseStep 44130365 = 16548887) B16548887
theorem B2416859 : Blo 1072617 2416859 := bstep (se 1 (by rfl) ⟨1812644, by rfl⟩ : syracuseStep 2416859 = 3625289) B3625289
theorem B1073383 : Blo 1072617 1073383 := bstep (se 1 (by rfl) ⟨805037, by rfl⟩ : syracuseStep 1073383 = 1610075) B1610075
theorem B1073535 : Blo 1072617 1073535 := bstep (se 1 (by rfl) ⟨805151, by rfl⟩ : syracuseStep 1073535 = 1610303) B1610303
theorem B1073615 : Blo 1072617 1073615 := bstep (se 1 (by rfl) ⟨805211, by rfl⟩ : syracuseStep 1073615 = 1610423) B1610423
theorem B2417129 : Blo 1072617 2417129 := bstep (se 2 (by rfl) ⟨906423, by rfl⟩ : syracuseStep 2417129 = 1812847) B1812847
theorem B6873673 : Blo 1072617 6873673 := bstep (se 2 (by rfl) ⟨2577627, by rfl⟩ : syracuseStep 6873673 = 5155255) B5155255
theorem B1073767 : Blo 1072617 1073767 := bstep (se 1 (by rfl) ⟨805325, by rfl⟩ : syracuseStep 1073767 = 1610651) B1610651
theorem B2417417 : Blo 1072617 2417417 := bstep (se 2 (by rfl) ⟨906531, by rfl⟩ : syracuseStep 2417417 = 1813063) B1813063
theorem B1074031 : Blo 1072617 1074031 := bstep (se 1 (by rfl) ⟨805523, by rfl⟩ : syracuseStep 1074031 = 1611047) B1611047
theorem B1074087 : Blo 1072617 1074087 := bstep (se 1 (by rfl) ⟨805565, by rfl⟩ : syracuseStep 1074087 = 1611131) B1611131
theorem B1074171 : Blo 1072617 1074171 := bstep (se 1 (by rfl) ⟨805628, by rfl⟩ : syracuseStep 1074171 = 1611257) B1611257
theorem B5432345 : Blo 1072617 5432345 := bstep (se 2 (by rfl) ⟨2037129, by rfl⟩ : syracuseStep 5432345 = 4074259) B4074259
theorem B1074239 : Blo 1072617 1074239 := bstep (se 1 (by rfl) ⟨805679, by rfl⟩ : syracuseStep 1074239 = 1611359) B1611359
theorem B3630203 : Blo 1072617 3630203 := bstep (se 1 (by rfl) ⟨2722652, by rfl⟩ : syracuseStep 3630203 = 5445305) B5445305
theorem B1074383 : Blo 1072617 1074383 := bstep (se 1 (by rfl) ⟨805787, by rfl⟩ : syracuseStep 1074383 = 1611575) B1611575
theorem B2417993 : Blo 1072617 2417993 := bstep (se 2 (by rfl) ⟨906747, by rfl⟩ : syracuseStep 2417993 = 1813495) B1813495
theorem B3630473 : Blo 1072617 3630473 := bstep (se 2 (by rfl) ⟨1361427, by rfl⟩ : syracuseStep 3630473 = 2722855) B2722855
theorem B1074587 : Blo 1072617 1074587 := bstep (se 1 (by rfl) ⟨805940, by rfl⟩ : syracuseStep 1074587 = 1611881) B1611881
theorem B1074799 : Blo 1072617 1074799 := bstep (se 1 (by rfl) ⟨806099, by rfl⟩ : syracuseStep 1074799 = 1612199) B1612199
theorem B1074855 : Blo 1072617 1074855 := bstep (se 1 (by rfl) ⟨806141, by rfl⟩ : syracuseStep 1074855 = 1612283) B1612283
theorem B1074939 : Blo 1072617 1074939 := bstep (se 1 (by rfl) ⟨806204, by rfl⟩ : syracuseStep 1074939 = 1612409) B1612409
theorem B1074975 : Blo 1072617 1074975 := bstep (se 1 (by rfl) ⟨806231, by rfl⟩ : syracuseStep 1074975 = 1612463) B1612463
theorem B1075007 : Blo 1072617 1075007 := bstep (se 1 (by rfl) ⟨806255, by rfl⟩ : syracuseStep 1075007 = 1612511) B1612511
theorem B26109773 : Blo 1072617 26109773 := bstep (se 3 (by rfl) ⟨4895582, by rfl⟩ : syracuseStep 26109773 = 9791165) B9791165
theorem B1632239 : Blo 1072617 1632239 := bstep (se 1 (by rfl) ⟨1224179, by rfl⟩ : syracuseStep 1632239 = 2448359) B2448359
theorem B1075183 : Blo 1072617 1075183 := bstep (se 1 (by rfl) ⟨806387, by rfl⟩ : syracuseStep 1075183 = 1612775) B1612775
theorem B19589201 : Blo 1072617 19589201 := bstep (se 2 (by rfl) ⟨7345950, by rfl⟩ : syracuseStep 19589201 = 14691901) B14691901
theorem B3631229 : Blo 1072617 3631229 := bstep (se 3 (by rfl) ⟨680855, by rfl⟩ : syracuseStep 3631229 = 1361711) B1361711
theorem B1075355 : Blo 1072617 1075355 := bstep (se 1 (by rfl) ⟨806516, by rfl⟩ : syracuseStep 1075355 = 1613033) B1613033
theorem B1075391 : Blo 1072617 1075391 := bstep (se 1 (by rfl) ⟨806543, by rfl⟩ : syracuseStep 1075391 = 1613087) B1613087
theorem B2418983 : Blo 1072617 2418983 := bstep (se 1 (by rfl) ⟨1814237, by rfl⟩ : syracuseStep 2418983 = 3628475) B3628475
theorem B1075503 : Blo 1072617 1075503 := bstep (se 1 (by rfl) ⟨806627, by rfl⟩ : syracuseStep 1075503 = 1613255) B1613255
theorem B2419001 : Blo 1072617 2419001 := bstep (se 2 (by rfl) ⟨907125, by rfl⟩ : syracuseStep 2419001 = 1814251) B1814251
theorem B3631499 : Blo 1072617 3631499 := bstep (se 1 (by rfl) ⟨2723624, by rfl⟩ : syracuseStep 3631499 = 5447249) B5447249
theorem B11627003 : Blo 1072617 11627003 := bstep (se 1 (by rfl) ⟨8720252, by rfl⟩ : syracuseStep 11627003 = 17440505) B17440505
theorem B1075739 : Blo 1072617 1075739 := bstep (se 1 (by rfl) ⟨806804, by rfl⟩ : syracuseStep 1075739 = 1613609) B1613609
theorem B1075743 : Blo 1072617 1075743 := bstep (se 1 (by rfl) ⟨806807, by rfl⟩ : syracuseStep 1075743 = 1613615) B1613615
theorem B7563959 : Blo 1072617 7563959 := bstep (se 1 (by rfl) ⟨5672969, by rfl⟩ : syracuseStep 7563959 = 11345939) B11345939
theorem B1076059 : Blo 1072617 1076059 := bstep (se 1 (by rfl) ⟨807044, by rfl⟩ : syracuseStep 1076059 = 1614089) B1614089
theorem B1076127 : Blo 1072617 1076127 := bstep (se 1 (by rfl) ⟨807095, by rfl⟩ : syracuseStep 1076127 = 1614191) B1614191
theorem B12250115 : Blo 1072617 12250115 := bstep (se 1 (by rfl) ⟨9187586, by rfl⟩ : syracuseStep 12250115 = 18375173) B18375173
theorem B1076271 : Blo 1072617 1076271 := bstep (se 1 (by rfl) ⟨807203, by rfl⟩ : syracuseStep 1076271 = 1614407) B1614407
theorem B1076295 : Blo 1072617 1076295 := bstep (se 1 (by rfl) ⟨807221, by rfl⟩ : syracuseStep 1076295 = 1614443) B1614443
theorem B1076447 : Blo 1072617 1076447 := bstep (se 1 (by rfl) ⟨807335, by rfl⟩ : syracuseStep 1076447 = 1614671) B1614671
theorem B56618513 : Blo 1072617 56618513 := bstep (se 2 (by rfl) ⟨21231942, by rfl⟩ : syracuseStep 56618513 = 42463885) B42463885
theorem B5434937 : Blo 1072617 5434937 := bstep (se 2 (by rfl) ⟨2038101, by rfl⟩ : syracuseStep 5434937 = 4076203) B4076203
theorem B2420297 : Blo 1072617 2420297 := bstep (se 2 (by rfl) ⟨907611, by rfl⟩ : syracuseStep 2420297 = 1815223) B1815223
theorem B80703175 : Blo 1072617 80703175 := bstep (se 1 (by rfl) ⟨60527381, by rfl⟩ : syracuseStep 80703175 = 121054763) B121054763
theorem B3436427 : Blo 1072617 3436427 := bstep (se 1 (by rfl) ⟨2577320, by rfl⟩ : syracuseStep 3436427 = 5154641) B5154641
theorem B3633119 : Blo 1072617 3633119 := bstep (se 1 (by rfl) ⟨2724839, by rfl⟩ : syracuseStep 3633119 = 5449679) B5449679
theorem B3633281 : Blo 1072617 3633281 := bstep (se 2 (by rfl) ⟨1362480, by rfl⟩ : syracuseStep 3633281 = 2724961) B2724961
theorem B1208551 : Blo 1072617 1208551 := bstep (se 1 (by rfl) ⟨906413, by rfl⟩ : syracuseStep 1208551 = 1812827) B1812827
theorem B2716031 : Blo 1072617 2716031 := bstep (se 1 (by rfl) ⟨2037023, by rfl⟩ : syracuseStep 2716031 = 4074047) B4074047
theorem B1209199 : Blo 1072617 1209199 := bstep (se 1 (by rfl) ⟨906899, by rfl⟩ : syracuseStep 1209199 = 1813799) B1813799
theorem B3437441 : Blo 1072617 3437441 := bstep (se 2 (by rfl) ⟨1289040, by rfl⟩ : syracuseStep 3437441 = 2578081) B2578081
theorem B2421755 : Blo 1072617 2421755 := bstep (se 1 (by rfl) ⟨1816316, by rfl⟩ : syracuseStep 2421755 = 3632633) B3632633
theorem B2421935 : Blo 1072617 2421935 := bstep (se 1 (by rfl) ⟨1816451, by rfl⟩ : syracuseStep 2421935 = 3632903) B3632903
theorem B2421971 : Blo 1072617 2421971 := bstep (se 1 (by rfl) ⟨1816478, by rfl⟩ : syracuseStep 2421971 = 3632957) B3632957
theorem B2422241 : Blo 1072617 2422241 := bstep (se 2 (by rfl) ⟨908340, by rfl⟩ : syracuseStep 2422241 = 1816681) B1816681
theorem B4585031 : Blo 1072617 4585031 := bstep (se 1 (by rfl) ⟨3438773, by rfl⟩ : syracuseStep 4585031 = 6877547) B6877547
theorem B9926345 : Blo 1072617 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B13072205 : Blo 1072617 13072205 := bstep (se 3 (by rfl) ⟨2451038, by rfl⟩ : syracuseStep 13072205 = 4902077) B4902077
theorem B5240713 : Blo 1072617 5240713 := bstep (se 2 (by rfl) ⟨1965267, by rfl⟩ : syracuseStep 5240713 = 3930535) B3930535
theorem B2717671 : Blo 1072617 2717671 := bstep (se 1 (by rfl) ⟨2038253, by rfl⟩ : syracuseStep 2717671 = 4076507) B4076507
theorem B1210351 : Blo 1072617 1210351 := bstep (se 1 (by rfl) ⟨907763, by rfl⟩ : syracuseStep 1210351 = 1815527) B1815527
theorem B13793273 : Blo 1072617 13793273 := bstep (se 2 (by rfl) ⟨5172477, by rfl⟩ : syracuseStep 13793273 = 10344955) B10344955
theorem B6125651 : Blo 1072617 6125651 := bstep (se 1 (by rfl) ⟨4594238, by rfl⟩ : syracuseStep 6125651 = 9188477) B9188477
theorem B29391011 : Blo 1072617 29391011 := bstep (se 1 (by rfl) ⟨22043258, by rfl⟩ : syracuseStep 29391011 = 44086517) B44086517
theorem B10320043 : Blo 1072617 10320043 := bstep (se 1 (by rfl) ⟨7740032, by rfl⟩ : syracuseStep 10320043 = 15480065) B15480065
theorem B4586003 : Blo 1072617 4586003 := bstep (se 1 (by rfl) ⟨3439502, by rfl⟩ : syracuseStep 4586003 = 6879005) B6879005
theorem B7731935 : Blo 1072617 7731935 := bstep (se 1 (by rfl) ⟨5798951, by rfl⟩ : syracuseStep 7731935 = 11597903) B11597903
theorem B2718623 : Blo 1072617 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B5372999 : Blo 1072617 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B6880439 : Blo 1072617 6880439 := bstep (se 1 (by rfl) ⟨5160329, by rfl⟩ : syracuseStep 6880439 = 10320659) B10320659
theorem B3439901 : Blo 1072617 3439901 := bstep (se 3 (by rfl) ⟨644981, by rfl⟩ : syracuseStep 3439901 = 1289963) B1289963
theorem B5438825 : Blo 1072617 5438825 := bstep (se 2 (by rfl) ⟨2039559, by rfl⟩ : syracuseStep 5438825 = 4079119) B4079119
theorem B3866557 : Blo 1072617 3866557 := bstep (se 3 (by rfl) ⟨724979, by rfl⟩ : syracuseStep 3866557 = 1449959) B1449959
theorem B1376447 : Blo 1072617 1376447 := bstep (se 1 (by rfl) ⟨1032335, by rfl⟩ : syracuseStep 1376447 = 2064671) B2064671
theorem B1966315 : Blo 1072617 1966315 := bstep (se 1 (by rfl) ⟨1474736, by rfl⟩ : syracuseStep 1966315 = 2949473) B2949473
theorem B20676991 : Blo 1072617 20676991 := bstep (se 1 (by rfl) ⟨15507743, by rfl⟩ : syracuseStep 20676991 = 31015487) B31015487
theorem B1835435 : Blo 1072617 1835435 := bstep (se 1 (by rfl) ⟨1376576, by rfl⟩ : syracuseStep 1835435 = 2753153) B2753153
theorem B5505641 : Blo 1072617 5505641 := bstep (se 2 (by rfl) ⟨2064615, by rfl⟩ : syracuseStep 5505641 = 4129231) B4129231
theorem B8159939 : Blo 1072617 8159939 := bstep (se 1 (by rfl) ⟨6119954, by rfl⟩ : syracuseStep 8159939 = 12239909) B12239909
theorem B70583393 : Blo 1072617 70583393 := bstep (se 2 (by rfl) ⟨26468772, by rfl⟩ : syracuseStep 70583393 = 52937545) B52937545
theorem B1934447 : Blo 1072617 1934447 := bstep (se 1 (by rfl) ⟨1450835, by rfl⟩ : syracuseStep 1934447 = 2901671) B2901671
theorem B39683621 : Blo 1072617 39683621 := bstep (se 4 (by rfl) ⟨3720339, by rfl⟩ : syracuseStep 39683621 = 7440679) B7440679
theorem B4589693 : Blo 1072617 4589693 := bstep (se 3 (by rfl) ⟨860567, by rfl⟩ : syracuseStep 4589693 = 1721135) B1721135
theorem B4589729 : Blo 1072617 4589729 := bstep (se 2 (by rfl) ⟨1721148, by rfl⟩ : syracuseStep 4589729 = 3442297) B3442297
theorem B2722643 : Blo 1072617 2722643 := bstep (se 1 (by rfl) ⟨2041982, by rfl⟩ : syracuseStep 2722643 = 4083965) B4083965
theorem B4590445 : Blo 1072617 4590445 := bstep (se 3 (by rfl) ⟨860708, by rfl⟩ : syracuseStep 4590445 = 1721417) B1721417
theorem B5442551 : Blo 1072617 5442551 := bstep (se 1 (by rfl) ⟨4081913, by rfl⟩ : syracuseStep 5442551 = 8163827) B8163827
theorem B46501087 : Blo 1072617 46501087 := bstep (se 1 (by rfl) ⟨34875815, by rfl⟩ : syracuseStep 46501087 = 69751631) B69751631
theorem B9178703 : Blo 1072617 9178703 := bstep (se 1 (by rfl) ⟨6884027, by rfl⟩ : syracuseStep 9178703 = 13768055) B13768055
theorem B1609319 : Blo 1072617 1609319 := bstep (se 1 (by rfl) ⟨1206989, by rfl⟩ : syracuseStep 1609319 = 2413979) B2413979
theorem B17403659 : Blo 1072617 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B1609703 : Blo 1072617 1609703 := bstep (se 1 (by rfl) ⟨1207277, by rfl⟩ : syracuseStep 1609703 = 2414555) B2414555
theorem B1609823 : Blo 1072617 1609823 := bstep (se 1 (by rfl) ⟨1207367, by rfl⟩ : syracuseStep 1609823 = 2414735) B2414735
theorem B1609835 : Blo 1072617 1609835 := bstep (se 1 (by rfl) ⟨1207376, by rfl⟩ : syracuseStep 1609835 = 2414753) B2414753
theorem B5509255 : Blo 1072617 5509255 := bstep (se 1 (by rfl) ⟨4131941, by rfl⟩ : syracuseStep 5509255 = 8263883) B8263883
theorem B1609883 : Blo 1072617 1609883 := bstep (se 1 (by rfl) ⟨1207412, by rfl⟩ : syracuseStep 1609883 = 2414825) B2414825
theorem B28348645 : Blo 1072617 28348645 := bstep (se 4 (by rfl) ⟨2657685, by rfl⟩ : syracuseStep 28348645 = 5315371) B5315371
theorem B9179729 : Blo 1072617 9179729 := bstep (se 2 (by rfl) ⟨3442398, by rfl⟩ : syracuseStep 9179729 = 6884797) B6884797
theorem B4133533 : Blo 1072617 4133533 := bstep (se 3 (by rfl) ⟨775037, by rfl⟩ : syracuseStep 4133533 = 1550075) B1550075
theorem B1610735 : Blo 1072617 1610735 := bstep (se 1 (by rfl) ⟨1208051, by rfl⟩ : syracuseStep 1610735 = 2416103) B2416103
theorem B1611119 : Blo 1072617 1611119 := bstep (se 1 (by rfl) ⟨1208339, by rfl⟩ : syracuseStep 1611119 = 2416679) B2416679
theorem B4593095 : Blo 1072617 4593095 := bstep (se 1 (by rfl) ⟨3444821, by rfl⟩ : syracuseStep 4593095 = 6889643) B6889643
theorem B1611239 : Blo 1072617 1611239 := bstep (se 1 (by rfl) ⟨1208429, by rfl⟩ : syracuseStep 1611239 = 2416859) B2416859
theorem B4593145 : Blo 1072617 4593145 := bstep (se 2 (by rfl) ⟨1722429, by rfl⟩ : syracuseStep 4593145 = 3444859) B3444859
theorem B1611401 : Blo 1072617 1611401 := bstep (se 2 (by rfl) ⟨604275, by rfl⟩ : syracuseStep 1611401 = 1208551) B1208551
theorem B2037403 : Blo 1072617 2037403 := bstep (se 1 (by rfl) ⟨1528052, by rfl⟩ : syracuseStep 2037403 = 3056105) B3056105
theorem B1611419 : Blo 1072617 1611419 := bstep (se 1 (by rfl) ⟨1208564, by rfl⟩ : syracuseStep 1611419 = 2417129) B2417129
theorem B1611611 : Blo 1072617 1611611 := bstep (se 1 (by rfl) ⟨1208708, by rfl⟩ : syracuseStep 1611611 = 2417417) B2417417
theorem B161060885 : Blo 1072617 161060885 := bstep (se 6 (by rfl) ⟨3774864, by rfl⟩ : syracuseStep 161060885 = 7549729) B7549729
theorem B17668205 : Blo 1072617 17668205 := bstep (se 3 (by rfl) ⟨3312788, by rfl⟩ : syracuseStep 17668205 = 6625577) B6625577
theorem B1611995 : Blo 1072617 1611995 := bstep (se 1 (by rfl) ⟨1208996, by rfl⟩ : syracuseStep 1611995 = 2417993) B2417993
theorem B1612265 : Blo 1072617 1612265 := bstep (se 2 (by rfl) ⟨604599, by rfl⟩ : syracuseStep 1612265 = 1209199) B1209199
theorem B17406515 : Blo 1072617 17406515 := bstep (se 1 (by rfl) ⟨13054886, by rfl⟩ : syracuseStep 17406515 = 26109773) B26109773
theorem B31005341 : Blo 1072617 31005341 := bstep (se 3 (by rfl) ⟨5813501, by rfl⟩ : syracuseStep 31005341 = 11627003) B11627003
theorem B1088159 : Blo 1072617 1088159 := bstep (se 1 (by rfl) ⟨816119, by rfl⟩ : syracuseStep 1088159 = 1632239) B1632239
theorem B8264375 : Blo 1072617 8264375 := bstep (se 1 (by rfl) ⟨6198281, by rfl⟩ : syracuseStep 8264375 = 12396563) B12396563
theorem B1612655 : Blo 1072617 1612655 := bstep (se 1 (by rfl) ⟨1209491, by rfl⟩ : syracuseStep 1612655 = 2418983) B2418983
theorem B1612667 : Blo 1072617 1612667 := bstep (se 1 (by rfl) ⟨1209500, by rfl⟩ : syracuseStep 1612667 = 2419001) B2419001
theorem B2038763 : Blo 1072617 2038763 := bstep (se 1 (by rfl) ⟨1529072, by rfl⟩ : syracuseStep 2038763 = 3058145) B3058145
theorem B8166743 : Blo 1072617 8166743 := bstep (se 1 (by rfl) ⟨6125057, by rfl⟩ : syracuseStep 8166743 = 12250115) B12250115
theorem B5447087 : Blo 1072617 5447087 := bstep (se 1 (by rfl) ⟨4085315, by rfl⟩ : syracuseStep 5447087 = 8170631) B8170631
theorem B9805321 : Blo 1072617 9805321 := bstep (se 2 (by rfl) ⟨3676995, by rfl⟩ : syracuseStep 9805321 = 7353991) B7353991
theorem B1613531 : Blo 1072617 1613531 := bstep (se 1 (by rfl) ⟨1210148, by rfl⟩ : syracuseStep 1613531 = 2420297) B2420297
theorem B6987617 : Blo 1072617 6987617 := bstep (se 2 (by rfl) ⟨2620356, by rfl⟩ : syracuseStep 6987617 = 5240713) B5240713
theorem B34840529 : Blo 1072617 34840529 := bstep (se 2 (by rfl) ⟨13065198, by rfl⟩ : syracuseStep 34840529 = 26130397) B26130397
theorem B1613801 : Blo 1072617 1613801 := bstep (se 2 (by rfl) ⟨605175, by rfl⟩ : syracuseStep 1613801 = 1210351) B1210351
theorem B2760695 : Blo 1072617 2760695 := bstep (se 1 (by rfl) ⟨2070521, by rfl⟩ : syracuseStep 2760695 = 4141043) B4141043
theorem B1810687 : Blo 1072617 1810687 := bstep (se 1 (by rfl) ⟨1358015, by rfl⟩ : syracuseStep 1810687 = 2716031) B2716031
theorem B2040403 : Blo 1072617 2040403 := bstep (se 1 (by rfl) ⟨1530302, by rfl⟩ : syracuseStep 2040403 = 3060605) B3060605
theorem B1614503 : Blo 1072617 1614503 := bstep (se 1 (by rfl) ⟨1210877, by rfl⟩ : syracuseStep 1614503 = 2421755) B2421755
theorem B1614623 : Blo 1072617 1614623 := bstep (se 1 (by rfl) ⟨1210967, by rfl⟩ : syracuseStep 1614623 = 2421935) B2421935
theorem B4596527 : Blo 1072617 4596527 := bstep (se 1 (by rfl) ⟨3447395, by rfl⟩ : syracuseStep 4596527 = 6894791) B6894791
theorem B1614647 : Blo 1072617 1614647 := bstep (se 1 (by rfl) ⟨1210985, by rfl⟩ : syracuseStep 1614647 = 2421971) B2421971
theorem B5448545 : Blo 1072617 5448545 := bstep (se 2 (by rfl) ⟨2043204, by rfl⟩ : syracuseStep 5448545 = 4086409) B4086409
theorem B1614827 : Blo 1072617 1614827 := bstep (se 1 (by rfl) ⟨1211120, by rfl⟩ : syracuseStep 1614827 = 2422241) B2422241
theorem B3056687 : Blo 1072617 3056687 := bstep (se 1 (by rfl) ⟨2292515, by rfl⟩ : syracuseStep 3056687 = 4585031) B4585031
theorem B7742573 : Blo 1072617 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B4073075 : Blo 1072617 4073075 := bstep (se 1 (by rfl) ⟨3054806, by rfl⟩ : syracuseStep 4073075 = 6109613) B6109613
theorem B3057335 : Blo 1072617 3057335 := bstep (se 1 (by rfl) ⟨2293001, by rfl⟩ : syracuseStep 3057335 = 4586003) B4586003
theorem B2041595 : Blo 1072617 2041595 := bstep (se 1 (by rfl) ⟨1531196, by rfl⟩ : syracuseStep 2041595 = 3062393) B3062393
theorem B5154623 : Blo 1072617 5154623 := bstep (se 1 (by rfl) ⟨3865967, by rfl⟩ : syracuseStep 5154623 = 7731935) B7731935
theorem B22095803 : Blo 1072617 22095803 := bstep (se 1 (by rfl) ⟨16571852, by rfl⟩ : syracuseStep 22095803 = 33143705) B33143705
theorem B1812415 : Blo 1072617 1812415 := bstep (se 1 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 1812415 = 2718623) B2718623
theorem B2041823 : Blo 1072617 2041823 := bstep (se 1 (by rfl) ⟨1531367, by rfl⟩ : syracuseStep 2041823 = 3062735) B3062735
theorem B3581999 : Blo 1072617 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B2042347 : Blo 1072617 2042347 := bstep (se 1 (by rfl) ⟨1531760, by rfl⟩ : syracuseStep 2042347 = 3063521) B3063521
theorem B5155409 : Blo 1072617 5155409 := bstep (se 2 (by rfl) ⟨1933278, by rfl⟩ : syracuseStep 5155409 = 3866557) B3866557
theorem B4074745 : Blo 1072617 4074745 := bstep (se 2 (by rfl) ⟨1528029, by rfl⟩ : syracuseStep 4074745 = 3056059) B3056059
theorem B2043463 : Blo 1072617 2043463 := bstep (se 1 (by rfl) ⟨1532597, by rfl⟩ : syracuseStep 2043463 = 3065195) B3065195
theorem B1814521 : Blo 1072617 1814521 := bstep (se 2 (by rfl) ⟨680445, by rfl⟩ : syracuseStep 1814521 = 1360891) B1360891
theorem B9187451 : Blo 1072617 9187451 := bstep (se 1 (by rfl) ⟨6890588, by rfl⟩ : syracuseStep 9187451 = 13781177) B13781177
theorem B1814791 : Blo 1072617 1814791 := bstep (se 1 (by rfl) ⟨1361093, by rfl⟩ : syracuseStep 1814791 = 2722187) B2722187
theorem B8172089 : Blo 1072617 8172089 := bstep (se 2 (by rfl) ⟨3064533, by rfl⟩ : syracuseStep 8172089 = 6129067) B6129067
theorem B5813329 : Blo 1072617 5813329 := bstep (se 2 (by rfl) ⟨2179998, by rfl⟩ : syracuseStep 5813329 = 4359997) B4359997
theorem B1815817 : Blo 1072617 1815817 := bstep (se 2 (by rfl) ⟨680931, by rfl⟩ : syracuseStep 1815817 = 1361863) B1361863
theorem B1815871 : Blo 1072617 1815871 := bstep (se 1 (by rfl) ⟨1361903, by rfl⟩ : syracuseStep 1815871 = 2723807) B2723807
theorem B1816303 : Blo 1072617 1816303 := bstep (se 1 (by rfl) ⟨1362227, by rfl⟩ : syracuseStep 1816303 = 2724455) B2724455
theorem B12236993 : Blo 1072617 12236993 := bstep (se 2 (by rfl) ⟨4588872, by rfl⟩ : syracuseStep 12236993 = 9177745) B9177745
theorem B3062279 : Blo 1072617 3062279 := bstep (se 1 (by rfl) ⟨2296709, by rfl⟩ : syracuseStep 3062279 = 4593419) B4593419
theorem B5159639 : Blo 1072617 5159639 := bstep (se 1 (by rfl) ⟨3869729, by rfl⟩ : syracuseStep 5159639 = 7739459) B7739459
theorem B8698589 : Blo 1072617 8698589 := bstep (se 3 (by rfl) ⟨1630985, by rfl⟩ : syracuseStep 8698589 = 3261971) B3261971
theorem B6896431 : Blo 1072617 6896431 := bstep (se 1 (by rfl) ⟨5172323, by rfl⟩ : syracuseStep 6896431 = 10344647) B10344647
theorem B9190867 : Blo 1072617 9190867 := bstep (se 1 (by rfl) ⟨6893150, by rfl⟩ : syracuseStep 9190867 = 13786301) B13786301
theorem B10337881 : Blo 1072617 10337881 := bstep (se 2 (by rfl) ⟨3876705, by rfl⟩ : syracuseStep 10337881 = 7753411) B7753411
theorem B12238451 : Blo 1072617 12238451 := bstep (se 1 (by rfl) ⟨9178838, by rfl⟩ : syracuseStep 12238451 = 18357677) B18357677
theorem B1360415 : Blo 1072617 1360415 := bstep (se 1 (by rfl) ⟨1020311, by rfl⟩ : syracuseStep 1360415 = 2040623) B2040623
theorem B3621563 : Blo 1072617 3621563 := bstep (se 1 (by rfl) ⟨2716172, by rfl⟩ : syracuseStep 3621563 = 5432345) B5432345
theorem B1361119 : Blo 1072617 1361119 := bstep (se 1 (by rfl) ⟨1020839, by rfl⟩ : syracuseStep 1361119 = 2041679) B2041679
theorem B13059467 : Blo 1072617 13059467 := bstep (se 1 (by rfl) ⟨9794600, by rfl⟩ : syracuseStep 13059467 = 19589201) B19589201
theorem B4900459 : Blo 1072617 4900459 := bstep (se 1 (by rfl) ⟨3675344, by rfl⟩ : syracuseStep 4900459 = 7350689) B7350689
theorem B30984119 : Blo 1072617 30984119 := bstep (se 1 (by rfl) ⟨23238089, by rfl⟩ : syracuseStep 30984119 = 46476179) B46476179
theorem B3623291 : Blo 1072617 3623291 := bstep (se 1 (by rfl) ⟨2717468, by rfl⟩ : syracuseStep 3623291 = 5434937) B5434937
theorem B8702579 : Blo 1072617 8702579 := bstep (se 1 (by rfl) ⟨6526934, by rfl⟩ : syracuseStep 8702579 = 13053869) B13053869
theorem B3623561 : Blo 1072617 3623561 := bstep (se 2 (by rfl) ⟨1358835, by rfl⟩ : syracuseStep 3623561 = 2717671) B2717671
theorem B5164175 : Blo 1072617 5164175 := bstep (se 1 (by rfl) ⟨3873131, by rfl⟩ : syracuseStep 5164175 = 7746263) B7746263
theorem B7359905 : Blo 1072617 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B9195515 : Blo 1072617 9195515 := bstep (se 1 (by rfl) ⟨6896636, by rfl⟩ : syracuseStep 9195515 = 13793273) B13793273
theorem B4083767 : Blo 1072617 4083767 := bstep (se 1 (by rfl) ⟨3062825, by rfl⟩ : syracuseStep 4083767 = 6125651) B6125651
theorem B2413403 : Blo 1072617 2413403 := bstep (se 1 (by rfl) ⟨1810052, by rfl⟩ : syracuseStep 2413403 = 3620105) B3620105
theorem B3625883 : Blo 1072617 3625883 := bstep (se 1 (by rfl) ⟨2719412, by rfl⟩ : syracuseStep 3625883 = 5438825) B5438825
theorem B2414159 : Blo 1072617 2414159 := bstep (se 1 (by rfl) ⟨1810619, by rfl⟩ : syracuseStep 2414159 = 3621239) B3621239
theorem B5167097 : Blo 1072617 5167097 := bstep (se 2 (by rfl) ⟨1937661, by rfl⟩ : syracuseStep 5167097 = 3875323) B3875323
theorem B9164897 : Blo 1072617 9164897 := bstep (se 2 (by rfl) ⟨3436836, by rfl⟩ : syracuseStep 9164897 = 6873673) B6873673
theorem B34920719 : Blo 1072617 34920719 := bstep (se 1 (by rfl) ⟨26190539, by rfl⟩ : syracuseStep 34920719 = 52381079) B52381079
theorem B2414879 : Blo 1072617 2414879 := bstep (se 1 (by rfl) ⟨1811159, by rfl⟩ : syracuseStep 2414879 = 3622319) B3622319
theorem B2415131 : Blo 1072617 2415131 := bstep (se 1 (by rfl) ⟨1811348, by rfl⟩ : syracuseStep 2415131 = 3622697) B3622697
theorem B38230625 : Blo 1072617 38230625 := bstep (se 2 (by rfl) ⟨14336484, by rfl⟩ : syracuseStep 38230625 = 28672969) B28672969
theorem B1530695 : Blo 1072617 1530695 := bstep (se 1 (by rfl) ⟨1148021, by rfl⟩ : syracuseStep 1530695 = 2296043) B2296043
theorem B4086881 : Blo 1072617 4086881 := bstep (se 2 (by rfl) ⟨1532580, by rfl⟩ : syracuseStep 4086881 = 3065161) B3065161
theorem B6970835 : Blo 1072617 6970835 := bstep (se 1 (by rfl) ⟨5228126, by rfl⟩ : syracuseStep 6970835 = 10456253) B10456253
theorem B1072751 : Blo 1072617 1072751 := bstep (se 1 (by rfl) ⟨804563, by rfl⟩ : syracuseStep 1072751 = 1609127) B1609127
theorem B1072807 : Blo 1072617 1072807 := bstep (se 1 (by rfl) ⟨804605, by rfl⟩ : syracuseStep 1072807 = 1609211) B1609211
theorem B1072871 : Blo 1072617 1072871 := bstep (se 1 (by rfl) ⟨804653, by rfl⟩ : syracuseStep 1072871 = 1609307) B1609307
theorem B1072927 : Blo 1072617 1072927 := bstep (se 1 (by rfl) ⟨804695, by rfl⟩ : syracuseStep 1072927 = 1609391) B1609391
theorem B2416481 : Blo 1072617 2416481 := bstep (se 2 (by rfl) ⟨906180, by rfl⟩ : syracuseStep 2416481 = 1812361) B1812361
theorem B1073007 : Blo 1072617 1073007 := bstep (se 1 (by rfl) ⟨804755, by rfl⟩ : syracuseStep 1073007 = 1609511) B1609511
theorem B1073063 : Blo 1072617 1073063 := bstep (se 1 (by rfl) ⟨804797, by rfl⟩ : syracuseStep 1073063 = 1609595) B1609595
theorem B2416607 : Blo 1072617 2416607 := bstep (se 1 (by rfl) ⟨1812455, by rfl⟩ : syracuseStep 2416607 = 3624911) B3624911
theorem B15294521 : Blo 1072617 15294521 := bstep (se 2 (by rfl) ⟨5735445, by rfl⟩ : syracuseStep 15294521 = 11470891) B11470891
theorem B1073343 : Blo 1072617 1073343 := bstep (se 1 (by rfl) ⟨805007, by rfl⟩ : syracuseStep 1073343 = 1610015) B1610015
theorem B1073359 : Blo 1072617 1073359 := bstep (se 1 (by rfl) ⟨805019, by rfl⟩ : syracuseStep 1073359 = 1610039) B1610039
theorem B1073407 : Blo 1072617 1073407 := bstep (se 1 (by rfl) ⟨805055, by rfl⟩ : syracuseStep 1073407 = 1610111) B1610111
theorem B2416895 : Blo 1072617 2416895 := bstep (se 1 (by rfl) ⟨1812671, by rfl⟩ : syracuseStep 2416895 = 3625343) B3625343
theorem B4907263 : Blo 1072617 4907263 := bstep (se 1 (by rfl) ⟨3680447, by rfl⟩ : syracuseStep 4907263 = 7360895) B7360895
theorem B1073455 : Blo 1072617 1073455 := bstep (se 1 (by rfl) ⟨805091, by rfl⟩ : syracuseStep 1073455 = 1610183) B1610183
theorem B2417057 : Blo 1072617 2417057 := bstep (se 2 (by rfl) ⟨906396, by rfl⟩ : syracuseStep 2417057 = 1812793) B1812793
theorem B1073691 : Blo 1072617 1073691 := bstep (se 1 (by rfl) ⟨805268, by rfl⟩ : syracuseStep 1073691 = 1610537) B1610537
theorem B1073695 : Blo 1072617 1073695 := bstep (se 1 (by rfl) ⟨805271, by rfl⟩ : syracuseStep 1073695 = 1610543) B1610543
theorem B1073775 : Blo 1072617 1073775 := bstep (se 1 (by rfl) ⟨805331, by rfl⟩ : syracuseStep 1073775 = 1610663) B1610663
theorem B1073831 : Blo 1072617 1073831 := bstep (se 1 (by rfl) ⟨805373, by rfl⟩ : syracuseStep 1073831 = 1610747) B1610747
theorem B2482855 : Blo 1072617 2482855 := bstep (se 1 (by rfl) ⟨1862141, by rfl⟩ : syracuseStep 2482855 = 3724283) B3724283
theorem B1073871 : Blo 1072617 1073871 := bstep (se 1 (by rfl) ⟨805403, by rfl⟩ : syracuseStep 1073871 = 1610807) B1610807
theorem B1073951 : Blo 1072617 1073951 := bstep (se 1 (by rfl) ⟨805463, by rfl⟩ : syracuseStep 1073951 = 1610927) B1610927
theorem B3629879 : Blo 1072617 3629879 := bstep (se 1 (by rfl) ⟨2722409, by rfl⟩ : syracuseStep 3629879 = 5444819) B5444819
theorem B1074223 : Blo 1072617 1074223 := bstep (se 1 (by rfl) ⟨805667, by rfl⟩ : syracuseStep 1074223 = 1611335) B1611335
theorem B1074287 : Blo 1072617 1074287 := bstep (se 1 (by rfl) ⟨805715, by rfl⟩ : syracuseStep 1074287 = 1611431) B1611431
theorem B1074343 : Blo 1072617 1074343 := bstep (se 1 (by rfl) ⟨805757, by rfl⟩ : syracuseStep 1074343 = 1611515) B1611515
theorem B2417831 : Blo 1072617 2417831 := bstep (se 1 (by rfl) ⟨1813373, by rfl⟩ : syracuseStep 2417831 = 3626747) B3626747
theorem B1074367 : Blo 1072617 1074367 := bstep (se 1 (by rfl) ⟨805775, by rfl⟩ : syracuseStep 1074367 = 1611551) B1611551
theorem B1074399 : Blo 1072617 1074399 := bstep (se 1 (by rfl) ⟨805799, by rfl⟩ : syracuseStep 1074399 = 1611599) B1611599
theorem B2417939 : Blo 1072617 2417939 := bstep (se 1 (by rfl) ⟨1813454, by rfl⟩ : syracuseStep 2417939 = 3626909) B3626909
theorem B1074479 : Blo 1072617 1074479 := bstep (se 1 (by rfl) ⟨805859, by rfl⟩ : syracuseStep 1074479 = 1611719) B1611719
theorem B10479095 : Blo 1072617 10479095 := bstep (se 1 (by rfl) ⟨7859321, by rfl⟩ : syracuseStep 10479095 = 15718643) B15718643
theorem B1074715 : Blo 1072617 1074715 := bstep (se 1 (by rfl) ⟨806036, by rfl⟩ : syracuseStep 1074715 = 1612073) B1612073
theorem B1074719 : Blo 1072617 1074719 := bstep (se 1 (by rfl) ⟨806039, by rfl⟩ : syracuseStep 1074719 = 1612079) B1612079
theorem B1074879 : Blo 1072617 1074879 := bstep (se 1 (by rfl) ⟨806159, by rfl⟩ : syracuseStep 1074879 = 1612319) B1612319
theorem B4351823 : Blo 1072617 4351823 := bstep (se 1 (by rfl) ⟨3263867, by rfl⟩ : syracuseStep 4351823 = 6527735) B6527735
theorem B26470253 : Blo 1072617 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B2418569 : Blo 1072617 2418569 := bstep (se 2 (by rfl) ⟨906963, by rfl⟩ : syracuseStep 2418569 = 1813927) B1813927
theorem B2418587 : Blo 1072617 2418587 := bstep (se 1 (by rfl) ⟨1813940, by rfl⟩ : syracuseStep 2418587 = 3627881) B3627881
theorem B7169957 : Blo 1072617 7169957 := bstep (se 4 (by rfl) ⟨672183, by rfl⟩ : syracuseStep 7169957 = 1344367) B1344367
theorem B2418623 : Blo 1072617 2418623 := bstep (se 1 (by rfl) ⟨1813967, by rfl⟩ : syracuseStep 2418623 = 3627935) B3627935
theorem B1075135 : Blo 1072617 1075135 := bstep (se 1 (by rfl) ⟨806351, by rfl⟩ : syracuseStep 1075135 = 1612703) B1612703
theorem B3631067 : Blo 1072617 3631067 := bstep (se 1 (by rfl) ⟨2723300, by rfl⟩ : syracuseStep 3631067 = 5446601) B5446601
theorem B1075167 : Blo 1072617 1075167 := bstep (se 1 (by rfl) ⟨806375, by rfl⟩ : syracuseStep 1075167 = 1612751) B1612751
theorem B11626487 : Blo 1072617 11626487 := bstep (se 1 (by rfl) ⟨8719865, by rfl⟩ : syracuseStep 11626487 = 17439731) B17439731
theorem B1075227 : Blo 1072617 1075227 := bstep (se 1 (by rfl) ⟨806420, by rfl⟩ : syracuseStep 1075227 = 1612841) B1612841
theorem B1075231 : Blo 1072617 1075231 := bstep (se 1 (by rfl) ⟨806423, by rfl⟩ : syracuseStep 1075231 = 1612847) B1612847
theorem B1075247 : Blo 1072617 1075247 := bstep (se 1 (by rfl) ⟨806435, by rfl⟩ : syracuseStep 1075247 = 1612871) B1612871
theorem B2418785 : Blo 1072617 2418785 := bstep (se 2 (by rfl) ⟨907044, by rfl⟩ : syracuseStep 2418785 = 1814089) B1814089
theorem B6121595 : Blo 1072617 6121595 := bstep (se 1 (by rfl) ⟨4591196, by rfl⟩ : syracuseStep 6121595 = 9182393) B9182393
theorem B1075423 : Blo 1072617 1075423 := bstep (se 1 (by rfl) ⟨806567, by rfl⟩ : syracuseStep 1075423 = 1613135) B1613135
theorem B3631337 : Blo 1072617 3631337 := bstep (se 2 (by rfl) ⟨1361751, by rfl⟩ : syracuseStep 3631337 = 2723503) B2723503
theorem B107604233 : Blo 1072617 107604233 := bstep (se 2 (by rfl) ⟨40351587, by rfl⟩ : syracuseStep 107604233 = 80703175) B80703175
theorem B1075483 : Blo 1072617 1075483 := bstep (se 1 (by rfl) ⟨806612, by rfl⟩ : syracuseStep 1075483 = 1613225) B1613225
theorem B1075583 : Blo 1072617 1075583 := bstep (se 1 (by rfl) ⟨806687, by rfl⟩ : syracuseStep 1075583 = 1613375) B1613375
theorem B3631607 : Blo 1072617 3631607 := bstep (se 1 (by rfl) ⟨2723705, by rfl⟩ : syracuseStep 3631607 = 5447411) B5447411
theorem B1075759 : Blo 1072617 1075759 := bstep (se 1 (by rfl) ⟨806819, by rfl⟩ : syracuseStep 1075759 = 1613639) B1613639
theorem B1075815 : Blo 1072617 1075815 := bstep (se 1 (by rfl) ⟨806861, by rfl⟩ : syracuseStep 1075815 = 1613723) B1613723
theorem B3631769 : Blo 1072617 3631769 := bstep (se 2 (by rfl) ⟨1361913, by rfl⟩ : syracuseStep 3631769 = 2723827) B2723827
theorem B29420243 : Blo 1072617 29420243 := bstep (se 1 (by rfl) ⟨22065182, by rfl⟩ : syracuseStep 29420243 = 44130365) B44130365
theorem B1076191 : Blo 1072617 1076191 := bstep (se 1 (by rfl) ⟨807143, by rfl⟩ : syracuseStep 1076191 = 1614287) B1614287
theorem B1207291 : Blo 1072617 1207291 := bstep (se 1 (by rfl) ⟨905468, by rfl⟩ : syracuseStep 1207291 = 1810937) B1810937
theorem B1076219 : Blo 1072617 1076219 := bstep (se 1 (by rfl) ⟨807164, by rfl⟩ : syracuseStep 1076219 = 1614329) B1614329
theorem B1076287 : Blo 1072617 1076287 := bstep (se 1 (by rfl) ⟨807215, by rfl⟩ : syracuseStep 1076287 = 1614431) B1614431
theorem B3632201 : Blo 1072617 3632201 := bstep (se 2 (by rfl) ⟨1362075, by rfl⟩ : syracuseStep 3632201 = 2724151) B2724151
theorem B10316969 : Blo 1072617 10316969 := bstep (se 2 (by rfl) ⟨3868863, by rfl⟩ : syracuseStep 10316969 = 7737727) B7737727
theorem B1207471 : Blo 1072617 1207471 := bstep (se 1 (by rfl) ⟨905603, by rfl⟩ : syracuseStep 1207471 = 1811207) B1811207
theorem B6876521 : Blo 1072617 6876521 := bstep (se 2 (by rfl) ⟨2578695, by rfl⟩ : syracuseStep 6876521 = 5157391) B5157391
theorem B1076607 : Blo 1072617 1076607 := bstep (se 1 (by rfl) ⟨807455, by rfl⟩ : syracuseStep 1076607 = 1614911) B1614911
theorem B2420135 : Blo 1072617 2420135 := bstep (se 1 (by rfl) ⟨1815101, by rfl⟩ : syracuseStep 2420135 = 3630203) B3630203
theorem B2420315 : Blo 1072617 2420315 := bstep (se 1 (by rfl) ⟨1815236, by rfl⟩ : syracuseStep 2420315 = 3630473) B3630473
theorem B1208191 : Blo 1072617 1208191 := bstep (se 1 (by rfl) ⟨906143, by rfl⟩ : syracuseStep 1208191 = 1812287) B1812287
theorem B1634185 : Blo 1072617 1634185 := bstep (se 2 (by rfl) ⟨612819, by rfl⟩ : syracuseStep 1634185 = 1225639) B1225639
theorem B2420729 : Blo 1072617 2420729 := bstep (se 2 (by rfl) ⟨907773, by rfl⟩ : syracuseStep 2420729 = 1815547) B1815547
theorem B2420819 : Blo 1072617 2420819 := bstep (se 1 (by rfl) ⟨1815614, by rfl⟩ : syracuseStep 2420819 = 3631229) B3631229
theorem B2420999 : Blo 1072617 2420999 := bstep (se 1 (by rfl) ⟨1815749, by rfl⟩ : syracuseStep 2420999 = 3631499) B3631499
theorem B3436825 : Blo 1072617 3436825 := bstep (se 2 (by rfl) ⟨1288809, by rfl⟩ : syracuseStep 3436825 = 2577619) B2577619
theorem B1208731 : Blo 1072617 1208731 := bstep (se 1 (by rfl) ⟨906548, by rfl⟩ : syracuseStep 1208731 = 1813097) B1813097
theorem B5042639 : Blo 1072617 5042639 := bstep (se 1 (by rfl) ⟨3781979, by rfl⟩ : syracuseStep 5042639 = 7563959) B7563959
theorem B2421305 : Blo 1072617 2421305 := bstep (se 2 (by rfl) ⟨907989, by rfl⟩ : syracuseStep 2421305 = 1815979) B1815979
theorem B10449623 : Blo 1072617 10449623 := bstep (se 1 (by rfl) ⟨7837217, by rfl⟩ : syracuseStep 10449623 = 15674435) B15674435
theorem B35877599 : Blo 1072617 35877599 := bstep (se 1 (by rfl) ⟨26908199, by rfl⟩ : syracuseStep 35877599 = 53816399) B53816399
theorem B37745675 : Blo 1072617 37745675 := bstep (se 1 (by rfl) ⟨28309256, by rfl⟩ : syracuseStep 37745675 = 56618513) B56618513
theorem B1209415 : Blo 1072617 1209415 := bstep (se 1 (by rfl) ⟨907061, by rfl⟩ : syracuseStep 1209415 = 1814123) B1814123
theorem B1209595 : Blo 1072617 1209595 := bstep (se 1 (by rfl) ⟨907196, by rfl⟩ : syracuseStep 1209595 = 1814393) B1814393
theorem B2290951 : Blo 1072617 2290951 := bstep (se 1 (by rfl) ⟨1718213, by rfl⟩ : syracuseStep 2290951 = 3436427) B3436427
theorem B2422025 : Blo 1072617 2422025 := bstep (se 2 (by rfl) ⟨908259, by rfl⟩ : syracuseStep 2422025 = 1816519) B1816519
theorem B2422079 : Blo 1072617 2422079 := bstep (se 1 (by rfl) ⟨1816559, by rfl⟩ : syracuseStep 2422079 = 3633119) B3633119
theorem B2422187 : Blo 1072617 2422187 := bstep (se 1 (by rfl) ⟨1816640, by rfl⟩ : syracuseStep 2422187 = 3633281) B3633281
theorem B13760057 : Blo 1072617 13760057 := bstep (se 2 (by rfl) ⟨5160021, by rfl⟩ : syracuseStep 13760057 = 10320043) B10320043
theorem B2291627 : Blo 1072617 2291627 := bstep (se 1 (by rfl) ⟨1718720, by rfl⟩ : syracuseStep 2291627 = 3437441) B3437441
theorem B1210783 : Blo 1072617 1210783 := bstep (se 1 (by rfl) ⟨908087, by rfl⟩ : syracuseStep 1210783 = 1816175) B1816175
theorem B1210855 : Blo 1072617 1210855 := bstep (se 1 (by rfl) ⟨908141, by rfl⟩ : syracuseStep 1210855 = 1816283) B1816283
theorem B8714803 : Blo 1072617 8714803 := bstep (se 1 (by rfl) ⟨6536102, by rfl⟩ : syracuseStep 8714803 = 13072205) B13072205
theorem B2718299 : Blo 1072617 2718299 := bstep (se 1 (by rfl) ⟨2038724, by rfl⟩ : syracuseStep 2718299 = 4077449) B4077449
theorem B4422235 : Blo 1072617 4422235 := bstep (se 1 (by rfl) ⟨3316676, by rfl⟩ : syracuseStep 4422235 = 6633353) B6633353
theorem B9796241 : Blo 1072617 9796241 := bstep (se 2 (by rfl) ⟨3673590, by rfl⟩ : syracuseStep 9796241 = 7347181) B7347181
theorem B5438177 : Blo 1072617 5438177 := bstep (se 2 (by rfl) ⟨2039316, by rfl⟩ : syracuseStep 5438177 = 4078633) B4078633
theorem B19594007 : Blo 1072617 19594007 := bstep (se 1 (by rfl) ⟨14695505, by rfl⟩ : syracuseStep 19594007 = 29391011) B29391011
theorem B1145711 : Blo 1072617 1145711 := bstep (se 1 (by rfl) ⟨859283, by rfl⟩ : syracuseStep 1145711 = 1718567) B1718567
theorem B11598977 : Blo 1072617 11598977 := bstep (se 2 (by rfl) ⟨4349616, by rfl⟩ : syracuseStep 11598977 = 8699233) B8699233
theorem B4586959 : Blo 1072617 4586959 := bstep (se 1 (by rfl) ⟨3440219, by rfl⟩ : syracuseStep 4586959 = 6880439) B6880439
theorem B2293267 : Blo 1072617 2293267 := bstep (se 1 (by rfl) ⟨1719950, by rfl⟩ : syracuseStep 2293267 = 3439901) B3439901
theorem B2621753 : Blo 1072617 2621753 := bstep (se 2 (by rfl) ⟨983157, by rfl⟩ : syracuseStep 2621753 = 1966315) B1966315
theorem B3670427 : Blo 1072617 3670427 := bstep (se 1 (by rfl) ⟨2752820, by rfl⟩ : syracuseStep 3670427 = 5505641) B5505641
theorem B5439959 : Blo 1072617 5439959 := bstep (se 1 (by rfl) ⟨4079969, by rfl⟩ : syracuseStep 5439959 = 8159939) B8159939
theorem B3670525 : Blo 1072617 3670525 := bstep (se 3 (by rfl) ⟨688223, by rfl⟩ : syracuseStep 3670525 = 1376447) B1376447
theorem B47055595 : Blo 1072617 47055595 := bstep (se 1 (by rfl) ⟨35291696, by rfl⟩ : syracuseStep 47055595 = 70583393) B70583393
theorem B2720537 : Blo 1072617 2720537 := bstep (se 2 (by rfl) ⟨1020201, by rfl⟩ : syracuseStep 2720537 = 2040403) B2040403
theorem B5801719 : Blo 1072617 5801719 := bstep (se 1 (by rfl) ⟨4351289, by rfl⟩ : syracuseStep 5801719 = 8702579) B8702579
theorem B3442783 : Blo 1072617 3442783 := bstep (se 1 (by rfl) ⟨2582087, by rfl⟩ : syracuseStep 3442783 = 5164175) B5164175
theorem B12257405 : Blo 1072617 12257405 := bstep (se 3 (by rfl) ⟨2298263, by rfl⟩ : syracuseStep 12257405 = 4596527) B4596527
theorem B11602439 : Blo 1072617 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B6130343 : Blo 1072617 6130343 := bstep (se 1 (by rfl) ⟨4597757, by rfl⟩ : syracuseStep 6130343 = 9195515) B9195515
theorem B2722511 : Blo 1072617 2722511 := bstep (se 1 (by rfl) ⟨2041883, by rfl⟩ : syracuseStep 2722511 = 4083767) B4083767
theorem B1608935 : Blo 1072617 1608935 := bstep (se 1 (by rfl) ⟨1206701, by rfl⟩ : syracuseStep 1608935 = 2413403) B2413403
theorem B2723129 : Blo 1072617 2723129 := bstep (se 2 (by rfl) ⟨1021173, by rfl⟩ : syracuseStep 2723129 = 2042347) B2042347
theorem B13241893 : Blo 1072617 13241893 := bstep (se 4 (by rfl) ⟨1241427, by rfl⟩ : syracuseStep 13241893 = 2482855) B2482855
theorem B1609439 : Blo 1072617 1609439 := bstep (se 1 (by rfl) ⟨1207079, by rfl⟩ : syracuseStep 1609439 = 2414159) B2414159
theorem B1609721 : Blo 1072617 1609721 := bstep (se 2 (by rfl) ⟨603645, by rfl⟩ : syracuseStep 1609721 = 1207291) B1207291
theorem B3444731 : Blo 1072617 3444731 := bstep (se 1 (by rfl) ⟨2583548, by rfl⟩ : syracuseStep 3444731 = 5167097) B5167097
theorem B1609919 : Blo 1072617 1609919 := bstep (se 1 (by rfl) ⟨1207439, by rfl⟩ : syracuseStep 1609919 = 2414879) B2414879
theorem B1609961 : Blo 1072617 1609961 := bstep (se 2 (by rfl) ⟨603735, by rfl⟩ : syracuseStep 1609961 = 1207471) B1207471
theorem B62001449 : Blo 1072617 62001449 := bstep (se 2 (by rfl) ⟨23250543, by rfl⟩ : syracuseStep 62001449 = 46501087) B46501087
theorem B1610087 : Blo 1072617 1610087 := bstep (se 1 (by rfl) ⟨1207565, by rfl⟩ : syracuseStep 1610087 = 2415131) B2415131
theorem B11604343 : Blo 1072617 11604343 := bstep (se 1 (by rfl) ⟨8703257, by rfl⟩ : syracuseStep 11604343 = 17406515) B17406515
theorem B5509583 : Blo 1072617 5509583 := bstep (se 1 (by rfl) ⟨4132187, by rfl⟩ : syracuseStep 5509583 = 8264375) B8264375
theorem B2724587 : Blo 1072617 2724587 := bstep (se 1 (by rfl) ⟨2043440, by rfl⟩ : syracuseStep 2724587 = 4086881) B4086881
theorem B2724617 : Blo 1072617 2724617 := bstep (se 2 (by rfl) ⟨1021731, by rfl⟩ : syracuseStep 2724617 = 2043463) B2043463
theorem B604771093 : Blo 1072617 604771093 := bstep (se 6 (by rfl) ⟨14174322, by rfl⟩ : syracuseStep 604771093 = 28348645) B28348645
theorem B5444495 : Blo 1072617 5444495 := bstep (se 1 (by rfl) ⟨4083371, by rfl⟩ : syracuseStep 5444495 = 8166743) B8166743
theorem B1610921 : Blo 1072617 1610921 := bstep (se 2 (by rfl) ⟨604095, by rfl⟩ : syracuseStep 1610921 = 1208191) B1208191
theorem B1610987 : Blo 1072617 1610987 := bstep (se 1 (by rfl) ⟨1208240, by rfl⟩ : syracuseStep 1610987 = 2416481) B2416481
theorem B4658411 : Blo 1072617 4658411 := bstep (se 1 (by rfl) ⟨3493808, by rfl⟩ : syracuseStep 4658411 = 6987617) B6987617
theorem B1611071 : Blo 1072617 1611071 := bstep (se 1 (by rfl) ⟨1208303, by rfl⟩ : syracuseStep 1611071 = 2416607) B2416607
theorem B1840463 : Blo 1072617 1840463 := bstep (se 1 (by rfl) ⟨1380347, by rfl⟩ : syracuseStep 1840463 = 2760695) B2760695
theorem B10196347 : Blo 1072617 10196347 := bstep (se 1 (by rfl) ⟨7647260, by rfl⟩ : syracuseStep 10196347 = 15294521) B15294521
theorem B1611263 : Blo 1072617 1611263 := bstep (se 1 (by rfl) ⟨1208447, by rfl⟩ : syracuseStep 1611263 = 2416895) B2416895
theorem B7345673 : Blo 1072617 7345673 := bstep (se 2 (by rfl) ⟨2754627, by rfl⟩ : syracuseStep 7345673 = 5509255) B5509255
theorem B1611371 : Blo 1072617 1611371 := bstep (se 1 (by rfl) ⟨1208528, by rfl⟩ : syracuseStep 1611371 = 2417057) B2417057
theorem B1611641 : Blo 1072617 1611641 := bstep (se 2 (by rfl) ⟨604365, by rfl⟩ : syracuseStep 1611641 = 1208731) B1208731
theorem B2037791 : Blo 1072617 2037791 := bstep (se 1 (by rfl) ⟨1528343, by rfl⟩ : syracuseStep 2037791 = 3056687) B3056687
theorem B1611887 : Blo 1072617 1611887 := bstep (se 1 (by rfl) ⟨1208915, by rfl⟩ : syracuseStep 1611887 = 2417831) B2417831
theorem B1611959 : Blo 1072617 1611959 := bstep (se 1 (by rfl) ⟨1208969, by rfl⟩ : syracuseStep 1611959 = 2417939) B2417939
theorem B5511377 : Blo 1072617 5511377 := bstep (se 2 (by rfl) ⟨2066766, by rfl⟩ : syracuseStep 5511377 = 4133533) B4133533
theorem B6986063 : Blo 1072617 6986063 := bstep (se 1 (by rfl) ⟨5239547, by rfl⟩ : syracuseStep 6986063 = 10479095) B10479095
theorem B2038223 : Blo 1072617 2038223 := bstep (se 1 (by rfl) ⟨1528667, by rfl⟩ : syracuseStep 2038223 = 3057335) B3057335
theorem B1612379 : Blo 1072617 1612379 := bstep (se 1 (by rfl) ⟨1209284, by rfl⟩ : syracuseStep 1612379 = 2418569) B2418569
theorem B1612391 : Blo 1072617 1612391 := bstep (se 1 (by rfl) ⟨1209293, by rfl⟩ : syracuseStep 1612391 = 2418587) B2418587
theorem B1612415 : Blo 1072617 1612415 := bstep (se 1 (by rfl) ⟨1209311, by rfl⟩ : syracuseStep 1612415 = 2418623) B2418623
theorem B1612523 : Blo 1072617 1612523 := bstep (se 1 (by rfl) ⟨1209392, by rfl⟩ : syracuseStep 1612523 = 2418785) B2418785
theorem B1612553 : Blo 1072617 1612553 := bstep (se 2 (by rfl) ⟨604707, by rfl⟩ : syracuseStep 1612553 = 1209415) B1209415
theorem B71736155 : Blo 1072617 71736155 := bstep (se 1 (by rfl) ⟨53802116, by rfl⟩ : syracuseStep 71736155 = 107604233) B107604233
theorem B1612793 : Blo 1072617 1612793 := bstep (se 2 (by rfl) ⟨604797, by rfl⟩ : syracuseStep 1612793 = 1209595) B1209595
theorem B3054601 : Blo 1072617 3054601 := bstep (se 2 (by rfl) ⟨1145475, by rfl⟩ : syracuseStep 3054601 = 2290951) B2290951
theorem B1613423 : Blo 1072617 1613423 := bstep (se 1 (by rfl) ⟨1210067, by rfl⟩ : syracuseStep 1613423 = 2420135) B2420135
theorem B3055229 : Blo 1072617 3055229 := bstep (se 3 (by rfl) ⟨572855, by rfl⟩ : syracuseStep 3055229 = 1145711) B1145711
theorem B1613543 : Blo 1072617 1613543 := bstep (se 1 (by rfl) ⟨1210157, by rfl⟩ : syracuseStep 1613543 = 2420315) B2420315
theorem B1613819 : Blo 1072617 1613819 := bstep (se 1 (by rfl) ⟨1210364, by rfl⟩ : syracuseStep 1613819 = 2420729) B2420729
theorem B1613879 : Blo 1072617 1613879 := bstep (se 1 (by rfl) ⟨1210409, by rfl⟩ : syracuseStep 1613879 = 2420819) B2420819
theorem B1613999 : Blo 1072617 1613999 := bstep (se 1 (by rfl) ⟨1210499, by rfl⟩ : syracuseStep 1613999 = 2420999) B2420999
theorem B1614203 : Blo 1072617 1614203 := bstep (se 1 (by rfl) ⟨1210652, by rfl⟩ : syracuseStep 1614203 = 2421305) B2421305
theorem B5448059 : Blo 1072617 5448059 := bstep (se 1 (by rfl) ⟨4086044, by rfl⟩ : syracuseStep 5448059 = 8172089) B8172089
theorem B1614377 : Blo 1072617 1614377 := bstep (se 2 (by rfl) ⟨605391, by rfl⟩ : syracuseStep 1614377 = 1210783) B1210783
theorem B1614473 : Blo 1072617 1614473 := bstep (se 2 (by rfl) ⟨605427, by rfl⟩ : syracuseStep 1614473 = 1210855) B1210855
theorem B1614683 : Blo 1072617 1614683 := bstep (se 1 (by rfl) ⟨1211012, by rfl⟩ : syracuseStep 1614683 = 2422025) B2422025
theorem B1614719 : Blo 1072617 1614719 := bstep (se 1 (by rfl) ⟨1211039, by rfl⟩ : syracuseStep 1614719 = 2422079) B2422079
theorem B1614791 : Blo 1072617 1614791 := bstep (se 1 (by rfl) ⟨1211093, by rfl⟩ : syracuseStep 1614791 = 2422187) B2422187
theorem B2041519 : Blo 1072617 2041519 := bstep (se 1 (by rfl) ⟨1531139, by rfl⟩ : syracuseStep 2041519 = 3062279) B3062279
theorem B1812199 : Blo 1072617 1812199 := bstep (se 1 (by rfl) ⟨1359149, by rfl⟩ : syracuseStep 1812199 = 2718299) B2718299
theorem B6530827 : Blo 1072617 6530827 := bstep (se 1 (by rfl) ⟨4898120, by rfl⟩ : syracuseStep 6530827 = 9796241) B9796241
theorem B3057689 : Blo 1072617 3057689 := bstep (se 2 (by rfl) ⟨1146633, by rfl⟩ : syracuseStep 3057689 = 2293267) B2293267
theorem B1223623 : Blo 1072617 1223623 := bstep (se 1 (by rfl) ⟨917717, by rfl⟩ : syracuseStep 1223623 = 1835435) B1835435
theorem B27569321 : Blo 1072617 27569321 := bstep (se 2 (by rfl) ⟨10338495, by rfl⟩ : syracuseStep 27569321 = 20676991) B20676991
theorem B26455747 : Blo 1072617 26455747 := bstep (se 1 (by rfl) ⟨19841810, by rfl⟩ : syracuseStep 26455747 = 39683621) B39683621
theorem B13447037 : Blo 1072617 13447037 := bstep (se 3 (by rfl) ⟨2521319, by rfl⟩ : syracuseStep 13447037 = 5042639) B5042639
theorem B20656079 : Blo 1072617 20656079 := bstep (se 1 (by rfl) ⟨15492059, by rfl⟩ : syracuseStep 20656079 = 30984119) B30984119
theorem B3059795 : Blo 1072617 3059795 := bstep (se 1 (by rfl) ⟨2294846, by rfl⟩ : syracuseStep 3059795 = 4589693) B4589693
theorem B3059819 : Blo 1072617 3059819 := bstep (se 1 (by rfl) ⟨2294864, by rfl⟩ : syracuseStep 3059819 = 4589729) B4589729
theorem B1814825 : Blo 1072617 1814825 := bstep (se 2 (by rfl) ⟨680559, by rfl⟩ : syracuseStep 1814825 = 1361119) B1361119
theorem B1815095 : Blo 1072617 1815095 := bstep (se 1 (by rfl) ⟨1361321, by rfl⟩ : syracuseStep 1815095 = 2722643) B2722643
theorem B6533945 : Blo 1072617 6533945 := bstep (se 2 (by rfl) ⟨2450229, by rfl⟩ : syracuseStep 6533945 = 4900459) B4900459
theorem B5158525 : Blo 1072617 5158525 := bstep (se 3 (by rfl) ⟨967223, by rfl⟩ : syracuseStep 5158525 = 1934447) B1934447
theorem B3062063 : Blo 1072617 3062063 := bstep (se 1 (by rfl) ⟨2296547, by rfl⟩ : syracuseStep 3062063 = 4593095) B4593095
theorem B6109931 : Blo 1072617 6109931 := bstep (se 1 (by rfl) ⟨4582448, by rfl⟩ : syracuseStep 6109931 = 9164897) B9164897
theorem B11778803 : Blo 1072617 11778803 := bstep (se 1 (by rfl) ⟨8834102, by rfl⟩ : syracuseStep 11778803 = 17668205) B17668205
theorem B23280479 : Blo 1072617 23280479 := bstep (se 1 (by rfl) ⟨17460359, by rfl⟩ : syracuseStep 23280479 = 34920719) B34920719
theorem B1359175 : Blo 1072617 1359175 := bstep (se 1 (by rfl) ⟨1019381, by rfl⟩ : syracuseStep 1359175 = 2038763) B2038763
theorem B2178913 : Blo 1072617 2178913 := bstep (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) B1634185
theorem B5161715 : Blo 1072617 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B1361063 : Blo 1072617 1361063 := bstep (se 1 (by rfl) ⟨1020797, by rfl⟩ : syracuseStep 1361063 = 2041595) B2041595
theorem B2901215 : Blo 1072617 2901215 := bstep (se 1 (by rfl) ⟨2175911, by rfl⟩ : syracuseStep 2901215 = 4351823) B4351823
theorem B17646835 : Blo 1072617 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B14730535 : Blo 1072617 14730535 := bstep (se 1 (by rfl) ⟨11047901, by rfl⟩ : syracuseStep 14730535 = 22095803) B22095803
theorem B1361215 : Blo 1072617 1361215 := bstep (se 1 (by rfl) ⟨1020911, by rfl⟩ : syracuseStep 1361215 = 2041823) B2041823
theorem B7750991 : Blo 1072617 7750991 := bstep (se 1 (by rfl) ⟨5813243, by rfl⟩ : syracuseStep 7750991 = 11626487) B11626487
theorem B4081063 : Blo 1072617 4081063 := bstep (se 1 (by rfl) ⟨3060797, by rfl⟩ : syracuseStep 4081063 = 6121595) B6121595
theorem B7751105 : Blo 1072617 7751105 := bstep (se 2 (by rfl) ⟨2906664, by rfl⟩ : syracuseStep 7751105 = 5813329) B5813329
theorem B2901757 : Blo 1072617 2901757 := bstep (se 3 (by rfl) ⟨544079, by rfl⟩ : syracuseStep 2901757 = 1088159) B1088159
theorem B19613495 : Blo 1072617 19613495 := bstep (se 1 (by rfl) ⟨14710121, by rfl⟩ : syracuseStep 19613495 = 29420243) B29420243
theorem B4081853 : Blo 1072617 4081853 := bstep (se 3 (by rfl) ⟨765347, by rfl⟩ : syracuseStep 4081853 = 1530695) B1530695
theorem B6966415 : Blo 1072617 6966415 := bstep (se 1 (by rfl) ⟨5224811, by rfl⟩ : syracuseStep 6966415 = 10449623) B10449623
theorem B11619737 : Blo 1072617 11619737 := bstep (se 2 (by rfl) ⟨4357401, by rfl⟩ : syracuseStep 11619737 = 8714803) B8714803
theorem B9195241 : Blo 1072617 9195241 := bstep (se 2 (by rfl) ⟨3448215, by rfl⟩ : syracuseStep 9195241 = 6896431) B6896431
theorem B1527751 : Blo 1072617 1527751 := bstep (se 1 (by rfl) ⟨1145813, by rfl⟩ : syracuseStep 1527751 = 2291627) B2291627
theorem B3625451 : Blo 1072617 3625451 := bstep (se 1 (by rfl) ⟨2719088, by rfl⟩ : syracuseStep 3625451 = 5438177) B5438177
theorem B13062671 : Blo 1072617 13062671 := bstep (se 1 (by rfl) ⟨9797003, by rfl⟩ : syracuseStep 13062671 = 19594007) B19594007
theorem B6115945 : Blo 1072617 6115945 := bstep (se 2 (by rfl) ⟨2293479, by rfl⟩ : syracuseStep 6115945 = 4586959) B4586959
theorem B13783841 : Blo 1072617 13783841 := bstep (se 2 (by rfl) ⟨5168940, by rfl⟩ : syracuseStep 13783841 = 10337881) B10337881
theorem B2414249 : Blo 1072617 2414249 := bstep (se 2 (by rfl) ⟨905343, by rfl⟩ : syracuseStep 2414249 = 1810687) B1810687
theorem B6543017 : Blo 1072617 6543017 := bstep (se 2 (by rfl) ⟨2453631, by rfl⟩ : syracuseStep 6543017 = 4907263) B4907263
theorem B2414375 : Blo 1072617 2414375 := bstep (se 1 (by rfl) ⟨1810781, by rfl⟩ : syracuseStep 2414375 = 3621563) B3621563
theorem B8706311 : Blo 1072617 8706311 := bstep (se 1 (by rfl) ⟨6529733, by rfl⟩ : syracuseStep 8706311 = 13059467) B13059467
theorem B3627773 : Blo 1072617 3627773 := bstep (se 3 (by rfl) ⟨680207, by rfl⟩ : syracuseStep 3627773 = 1360415) B1360415
theorem B2415527 : Blo 1072617 2415527 := bstep (se 1 (by rfl) ⟨1811645, by rfl⟩ : syracuseStep 2415527 = 3623291) B3623291
theorem B2415707 : Blo 1072617 2415707 := bstep (se 1 (by rfl) ⟨1811780, by rfl⟩ : syracuseStep 2415707 = 3623561) B3623561
theorem B3628367 : Blo 1072617 3628367 := bstep (se 1 (by rfl) ⟨2721275, by rfl⟩ : syracuseStep 3628367 = 5442551) B5442551
theorem B4906603 : Blo 1072617 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B6119135 : Blo 1072617 6119135 := bstep (se 1 (by rfl) ⟨4589351, by rfl⟩ : syracuseStep 6119135 = 9178703) B9178703
theorem B1072879 : Blo 1072617 1072879 := bstep (se 1 (by rfl) ⟨804659, by rfl⟩ : syracuseStep 1072879 = 1609319) B1609319
theorem B2416553 : Blo 1072617 2416553 := bstep (se 2 (by rfl) ⟨906207, by rfl⟩ : syracuseStep 2416553 = 1812415) B1812415
theorem B1073135 : Blo 1072617 1073135 := bstep (se 1 (by rfl) ⟨804851, by rfl⟩ : syracuseStep 1073135 = 1609703) B1609703
theorem B1073215 : Blo 1072617 1073215 := bstep (se 1 (by rfl) ⟨804911, by rfl⟩ : syracuseStep 1073215 = 1609823) B1609823
theorem B1073223 : Blo 1072617 1073223 := bstep (se 1 (by rfl) ⟨804917, by rfl⟩ : syracuseStep 1073223 = 1609835) B1609835
theorem B1073255 : Blo 1072617 1073255 := bstep (se 1 (by rfl) ⟨804941, by rfl⟩ : syracuseStep 1073255 = 1609883) B1609883
theorem B6119819 : Blo 1072617 6119819 := bstep (se 1 (by rfl) ⟨4589864, by rfl⟩ : syracuseStep 6119819 = 9179729) B9179729
theorem B2417255 : Blo 1072617 2417255 := bstep (se 1 (by rfl) ⟨1812941, by rfl⟩ : syracuseStep 2417255 = 3625883) B3625883
theorem B1073823 : Blo 1072617 1073823 := bstep (se 1 (by rfl) ⟨805367, by rfl⟩ : syracuseStep 1073823 = 1610735) B1610735
theorem B1074079 : Blo 1072617 1074079 := bstep (se 1 (by rfl) ⟨805559, by rfl⟩ : syracuseStep 1074079 = 1611119) B1611119
theorem B1074159 : Blo 1072617 1074159 := bstep (se 1 (by rfl) ⟨805619, by rfl⟩ : syracuseStep 1074159 = 1611239) B1611239
theorem B1074267 : Blo 1072617 1074267 := bstep (se 1 (by rfl) ⟨805700, by rfl⟩ : syracuseStep 1074267 = 1611401) B1611401
theorem B1074279 : Blo 1072617 1074279 := bstep (se 1 (by rfl) ⟨805709, by rfl⟩ : syracuseStep 1074279 = 1611419) B1611419
theorem B6120593 : Blo 1072617 6120593 := bstep (se 2 (by rfl) ⟨2295222, by rfl⟩ : syracuseStep 6120593 = 4590445) B4590445
theorem B1074407 : Blo 1072617 1074407 := bstep (se 1 (by rfl) ⟨805805, by rfl⟩ : syracuseStep 1074407 = 1611611) B1611611
theorem B107373923 : Blo 1072617 107373923 := bstep (se 1 (by rfl) ⟨80530442, by rfl⟩ : syracuseStep 107373923 = 161060885) B161060885
theorem B1074663 : Blo 1072617 1074663 := bstep (se 1 (by rfl) ⟨805997, by rfl⟩ : syracuseStep 1074663 = 1611995) B1611995
theorem B1074843 : Blo 1072617 1074843 := bstep (se 1 (by rfl) ⟨806132, by rfl⟩ : syracuseStep 1074843 = 1612265) B1612265
theorem B5432993 : Blo 1072617 5432993 := bstep (se 2 (by rfl) ⟨2037372, by rfl⟩ : syracuseStep 5432993 = 4074745) B4074745
theorem B25487083 : Blo 1072617 25487083 := bstep (se 1 (by rfl) ⟨19115312, by rfl⟩ : syracuseStep 25487083 = 38230625) B38230625
theorem B20670227 : Blo 1072617 20670227 := bstep (se 1 (by rfl) ⟨15502670, by rfl⟩ : syracuseStep 20670227 = 31005341) B31005341
theorem B1075103 : Blo 1072617 1075103 := bstep (se 1 (by rfl) ⟨806327, by rfl⟩ : syracuseStep 1075103 = 1612655) B1612655
theorem B1075111 : Blo 1072617 1075111 := bstep (se 1 (by rfl) ⟨806333, by rfl⟩ : syracuseStep 1075111 = 1612667) B1612667
theorem B3631391 : Blo 1072617 3631391 := bstep (se 1 (by rfl) ⟨2723543, by rfl⟩ : syracuseStep 3631391 = 5447087) B5447087
theorem B4647223 : Blo 1072617 4647223 := bstep (se 1 (by rfl) ⟨3485417, by rfl⟩ : syracuseStep 4647223 = 6970835) B6970835
theorem B1075687 : Blo 1072617 1075687 := bstep (se 1 (by rfl) ⟨806765, by rfl⟩ : syracuseStep 1075687 = 1613531) B1613531
theorem B23227019 : Blo 1072617 23227019 := bstep (se 1 (by rfl) ⟨17420264, by rfl⟩ : syracuseStep 23227019 = 34840529) B34840529
theorem B1075867 : Blo 1072617 1075867 := bstep (se 1 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 1075867 = 1613801) B1613801
theorem B2419361 : Blo 1072617 2419361 := bstep (se 2 (by rfl) ⟨907260, by rfl⟩ : syracuseStep 2419361 = 1814521) B1814521
theorem B2419721 : Blo 1072617 2419721 := bstep (se 2 (by rfl) ⟨907395, by rfl⟩ : syracuseStep 2419721 = 1814791) B1814791
theorem B4582433 : Blo 1072617 4582433 := bstep (se 2 (by rfl) ⟨1718412, by rfl⟩ : syracuseStep 4582433 = 3436825) B3436825
theorem B1076335 : Blo 1072617 1076335 := bstep (se 1 (by rfl) ⟨807251, by rfl⟩ : syracuseStep 1076335 = 1614503) B1614503
theorem B1076415 : Blo 1072617 1076415 := bstep (se 1 (by rfl) ⟨807311, by rfl⟩ : syracuseStep 1076415 = 1614623) B1614623
theorem B2419919 : Blo 1072617 2419919 := bstep (se 1 (by rfl) ⟨1814939, by rfl⟩ : syracuseStep 2419919 = 3629879) B3629879
theorem B1076431 : Blo 1072617 1076431 := bstep (se 1 (by rfl) ⟨807323, by rfl⟩ : syracuseStep 1076431 = 1614647) B1614647
theorem B3632363 : Blo 1072617 3632363 := bstep (se 1 (by rfl) ⟨2724272, by rfl⟩ : syracuseStep 3632363 = 5448545) B5448545
theorem B1076551 : Blo 1072617 1076551 := bstep (se 1 (by rfl) ⟨807413, by rfl⟩ : syracuseStep 1076551 = 1614827) B1614827
theorem B2715383 : Blo 1072617 2715383 := bstep (se 1 (by rfl) ⟨2036537, by rfl⟩ : syracuseStep 2715383 = 4073075) B4073075
theorem B3436415 : Blo 1072617 3436415 := bstep (se 1 (by rfl) ⟨2577311, by rfl⟩ : syracuseStep 3436415 = 5154623) B5154623
theorem B4779971 : Blo 1072617 4779971 := bstep (se 1 (by rfl) ⟨3584978, by rfl⟩ : syracuseStep 4779971 = 7169957) B7169957
theorem B2420711 : Blo 1072617 2420711 := bstep (se 1 (by rfl) ⟨1815533, by rfl⟩ : syracuseStep 2420711 = 3631067) B3631067
theorem B2387999 : Blo 1072617 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B2420891 : Blo 1072617 2420891 := bstep (se 1 (by rfl) ⟨1815668, by rfl⟩ : syracuseStep 2420891 = 3631337) B3631337
theorem B2421071 : Blo 1072617 2421071 := bstep (se 1 (by rfl) ⟨1815803, by rfl⟩ : syracuseStep 2421071 = 3631607) B3631607
theorem B2421089 : Blo 1072617 2421089 := bstep (se 2 (by rfl) ⟨907908, by rfl⟩ : syracuseStep 2421089 = 1815817) B1815817
theorem B3436939 : Blo 1072617 3436939 := bstep (se 1 (by rfl) ⟨2577704, by rfl⟩ : syracuseStep 3436939 = 5155409) B5155409
theorem B2421161 : Blo 1072617 2421161 := bstep (se 2 (by rfl) ⟨907935, by rfl⟩ : syracuseStep 2421161 = 1815871) B1815871
theorem B2421179 : Blo 1072617 2421179 := bstep (se 1 (by rfl) ⟨1815884, by rfl⟩ : syracuseStep 2421179 = 3631769) B3631769
theorem B6124193 : Blo 1072617 6124193 := bstep (se 2 (by rfl) ⟨2296572, by rfl⟩ : syracuseStep 6124193 = 4593145) B4593145
theorem B2421467 : Blo 1072617 2421467 := bstep (se 1 (by rfl) ⟨1816100, by rfl⟩ : syracuseStep 2421467 = 3632201) B3632201
theorem B6877979 : Blo 1072617 6877979 := bstep (se 1 (by rfl) ⟨5158484, by rfl⟩ : syracuseStep 6877979 = 10316969) B10316969
theorem B2716537 : Blo 1072617 2716537 := bstep (se 2 (by rfl) ⟨1018701, by rfl⟩ : syracuseStep 2716537 = 2037403) B2037403
theorem B4584347 : Blo 1072617 4584347 := bstep (se 1 (by rfl) ⟨3438260, by rfl⟩ : syracuseStep 4584347 = 6876521) B6876521
theorem B2421737 : Blo 1072617 2421737 := bstep (se 2 (by rfl) ⟨908151, by rfl⟩ : syracuseStep 2421737 = 1816303) B1816303
theorem B6124967 : Blo 1072617 6124967 := bstep (se 1 (by rfl) ⟨4593725, by rfl⟩ : syracuseStep 6124967 = 9187451) B9187451
theorem B30930605 : Blo 1072617 30930605 := bstep (se 3 (by rfl) ⟨5799488, by rfl⟩ : syracuseStep 30930605 = 11598977) B11598977
theorem B23918399 : Blo 1072617 23918399 := bstep (se 1 (by rfl) ⟨17938799, by rfl⟩ : syracuseStep 23918399 = 35877599) B35877599
theorem B25163783 : Blo 1072617 25163783 := bstep (se 1 (by rfl) ⟨18872837, by rfl⟩ : syracuseStep 25163783 = 37745675) B37745675
theorem B5896313 : Blo 1072617 5896313 := bstep (se 2 (by rfl) ⟨2211117, by rfl⟩ : syracuseStep 5896313 = 4422235) B4422235
theorem B9173371 : Blo 1072617 9173371 := bstep (se 1 (by rfl) ⟨6880028, by rfl⟩ : syracuseStep 9173371 = 13760057) B13760057
theorem B8157995 : Blo 1072617 8157995 := bstep (se 1 (by rfl) ⟨6118496, by rfl⟩ : syracuseStep 8157995 = 12236993) B12236993
theorem B3439759 : Blo 1072617 3439759 := bstep (se 1 (by rfl) ⟨2579819, by rfl⟩ : syracuseStep 3439759 = 5159639) B5159639
theorem B5799059 : Blo 1072617 5799059 := bstep (se 1 (by rfl) ⟨4349294, by rfl⟩ : syracuseStep 5799059 = 8698589) B8698589
theorem B12254489 : Blo 1072617 12254489 := bstep (se 2 (by rfl) ⟨4595433, by rfl⟩ : syracuseStep 12254489 = 9190867) B9190867
theorem B13073761 : Blo 1072617 13073761 := bstep (se 2 (by rfl) ⟨4902660, by rfl⟩ : syracuseStep 13073761 = 9805321) B9805321
theorem B8158967 : Blo 1072617 8158967 := bstep (se 1 (by rfl) ⟨6119225, by rfl⟩ : syracuseStep 8158967 = 12238451) B12238451
theorem B8159453 : Blo 1072617 8159453 := bstep (se 3 (by rfl) ⟨1529897, by rfl⟩ : syracuseStep 8159453 = 3059795) B3059795
theorem B3441143 : Blo 1072617 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B13075663 : Blo 1072617 13075663 := bstep (se 1 (by rfl) ⟨9806747, by rfl⟩ : syracuseStep 13075663 = 19613495) B19613495
theorem B2721235 : Blo 1072617 2721235 := bstep (se 1 (by rfl) ⟨2040926, by rfl⟩ : syracuseStep 2721235 = 4081853) B4081853
theorem B23529113 : Blo 1072617 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B7734959 : Blo 1072617 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B5441417 : Blo 1072617 5441417 := bstep (se 2 (by rfl) ⟨2040531, by rfl⟩ : syracuseStep 5441417 = 4081063) B4081063
theorem B2722025 : Blo 1072617 2722025 := bstep (se 2 (by rfl) ⟨1020759, by rfl⟩ : syracuseStep 2722025 = 2041519) B2041519
theorem B33982777 : Blo 1072617 33982777 := bstep (se 2 (by rfl) ⟨12743541, by rfl⟩ : syracuseStep 33982777 = 25487083) B25487083
theorem B7735625 : Blo 1072617 7735625 := bstep (se 2 (by rfl) ⟨2900859, by rfl⟩ : syracuseStep 7735625 = 5801719) B5801719
theorem B3869009 : Blo 1072617 3869009 := bstep (se 2 (by rfl) ⟨1450878, by rfl⟩ : syracuseStep 3869009 = 2901757) B2901757
theorem B2296487 : Blo 1072617 2296487 := bstep (se 1 (by rfl) ⟨1722365, by rfl⟩ : syracuseStep 2296487 = 3444731) B3444731
theorem B4590377 : Blo 1072617 4590377 := bstep (se 2 (by rfl) ⟨1721391, by rfl⟩ : syracuseStep 4590377 = 3442783) B3442783
theorem B3673055 : Blo 1072617 3673055 := bstep (se 1 (by rfl) ⟨2754791, by rfl⟩ : syracuseStep 3673055 = 5509583) B5509583
theorem B7736573 : Blo 1072617 7736573 := bstep (se 3 (by rfl) ⟨1450607, by rfl⟩ : syracuseStep 7736573 = 2901215) B2901215
theorem B19631605 : Blo 1072617 19631605 := bstep (se 5 (by rfl) ⟨920231, by rfl⟩ : syracuseStep 19631605 = 1840463) B1840463
theorem B1609499 : Blo 1072617 1609499 := bstep (se 1 (by rfl) ⟨1207124, by rfl⟩ : syracuseStep 1609499 = 2414249) B2414249
theorem B4362011 : Blo 1072617 4362011 := bstep (se 1 (by rfl) ⟨3271508, by rfl⟩ : syracuseStep 4362011 = 6543017) B6543017
theorem B1609583 : Blo 1072617 1609583 := bstep (se 1 (by rfl) ⟨1207187, by rfl⟩ : syracuseStep 1609583 = 2414375) B2414375
theorem B3674251 : Blo 1072617 3674251 := bstep (se 1 (by rfl) ⟨2755688, by rfl⟩ : syracuseStep 3674251 = 5511377) B5511377
theorem B5804207 : Blo 1072617 5804207 := bstep (se 1 (by rfl) ⟨4353155, by rfl⟩ : syracuseStep 5804207 = 8706311) B8706311
theorem B4657375 : Blo 1072617 4657375 := bstep (se 1 (by rfl) ⟨3493031, by rfl⟩ : syracuseStep 4657375 = 6986063) B6986063
theorem B1610351 : Blo 1072617 1610351 := bstep (se 1 (by rfl) ⟨1207763, by rfl⟩ : syracuseStep 1610351 = 2415527) B2415527
theorem B1610471 : Blo 1072617 1610471 := bstep (se 1 (by rfl) ⟨1207853, by rfl⟩ : syracuseStep 1610471 = 2415707) B2415707
theorem B12260321 : Blo 1072617 12260321 := bstep (se 2 (by rfl) ⟨4597620, by rfl⟩ : syracuseStep 12260321 = 9195241) B9195241
theorem B2036819 : Blo 1072617 2036819 := bstep (se 1 (by rfl) ⟨1527614, by rfl⟩ : syracuseStep 2036819 = 3055229) B3055229
theorem B2037001 : Blo 1072617 2037001 := bstep (se 2 (by rfl) ⟨763875, by rfl⟩ : syracuseStep 2037001 = 1527751) B1527751
theorem B1611035 : Blo 1072617 1611035 := bstep (se 1 (by rfl) ⟨1208276, by rfl⟩ : syracuseStep 1611035 = 2416553) B2416553
theorem B1611503 : Blo 1072617 1611503 := bstep (se 1 (by rfl) ⟨1208627, by rfl⟩ : syracuseStep 1611503 = 2417255) B2417255
theorem B15472457 : Blo 1072617 15472457 := bstep (se 2 (by rfl) ⟨5802171, by rfl⟩ : syracuseStep 15472457 = 11604343) B11604343
theorem B2038459 : Blo 1072617 2038459 := bstep (se 1 (by rfl) ⟨1528844, by rfl⟩ : syracuseStep 2038459 = 3057689) B3057689
theorem B1612907 : Blo 1072617 1612907 := bstep (se 1 (by rfl) ⟨1209680, by rfl⟩ : syracuseStep 1612907 = 2419361) B2419361
theorem B1613147 : Blo 1072617 1613147 := bstep (se 1 (by rfl) ⟨1209860, by rfl⟩ : syracuseStep 1613147 = 2419721) B2419721
theorem B3054955 : Blo 1072617 3054955 := bstep (se 1 (by rfl) ⟨2291216, by rfl⟩ : syracuseStep 3054955 = 4582433) B4582433
theorem B1613279 : Blo 1072617 1613279 := bstep (se 1 (by rfl) ⟨1209959, by rfl⟩ : syracuseStep 1613279 = 2419919) B2419919
theorem B1810255 : Blo 1072617 1810255 := bstep (se 1 (by rfl) ⟨1357691, by rfl⟩ : syracuseStep 1810255 = 2715383) B2715383
theorem B3186647 : Blo 1072617 3186647 := bstep (se 1 (by rfl) ⟨2389985, by rfl⟩ : syracuseStep 3186647 = 4779971) B4779971
theorem B13770719 : Blo 1072617 13770719 := bstep (se 1 (by rfl) ⟨10328039, by rfl⟩ : syracuseStep 13770719 = 20656079) B20656079
theorem B1613807 : Blo 1072617 1613807 := bstep (se 1 (by rfl) ⟨1210355, by rfl⟩ : syracuseStep 1613807 = 2420711) B2420711
theorem B2039879 : Blo 1072617 2039879 := bstep (se 1 (by rfl) ⟨1529909, by rfl⟩ : syracuseStep 2039879 = 3059819) B3059819
theorem B1613927 : Blo 1072617 1613927 := bstep (se 1 (by rfl) ⟨1210445, by rfl⟩ : syracuseStep 1613927 = 2420891) B2420891
theorem B1614047 : Blo 1072617 1614047 := bstep (se 1 (by rfl) ⟨1210535, by rfl⟩ : syracuseStep 1614047 = 2421071) B2421071
theorem B1614059 : Blo 1072617 1614059 := bstep (se 1 (by rfl) ⟨1210544, by rfl⟩ : syracuseStep 1614059 = 2421089) B2421089
theorem B1614107 : Blo 1072617 1614107 := bstep (se 1 (by rfl) ⟨1210580, by rfl⟩ : syracuseStep 1614107 = 2421161) B2421161
theorem B1614119 : Blo 1072617 1614119 := bstep (se 1 (by rfl) ⟨1210589, by rfl⟩ : syracuseStep 1614119 = 2421179) B2421179
theorem B1614311 : Blo 1072617 1614311 := bstep (se 1 (by rfl) ⟨1210733, by rfl⟩ : syracuseStep 1614311 = 2421467) B2421467
theorem B12231161 : Blo 1072617 12231161 := bstep (se 2 (by rfl) ⟨4586685, by rfl⟩ : syracuseStep 12231161 = 9173371) B9173371
theorem B3056231 : Blo 1072617 3056231 := bstep (se 1 (by rfl) ⟨2292173, by rfl⟩ : syracuseStep 3056231 = 4584347) B4584347
theorem B1614491 : Blo 1072617 1614491 := bstep (se 1 (by rfl) ⟨1210868, by rfl⟩ : syracuseStep 1614491 = 2421737) B2421737
theorem B20620403 : Blo 1072617 20620403 := bstep (se 1 (by rfl) ⟨15465302, by rfl⟩ : syracuseStep 20620403 = 30930605) B30930605
theorem B4072801 : Blo 1072617 4072801 := bstep (se 2 (by rfl) ⟨1527300, by rfl⟩ : syracuseStep 4072801 = 3054601) B3054601
theorem B2041375 : Blo 1072617 2041375 := bstep (se 1 (by rfl) ⟨1531031, by rfl⟩ : syracuseStep 2041375 = 3062063) B3062063
theorem B1812233 : Blo 1072617 1812233 := bstep (se 2 (by rfl) ⟨679587, by rfl⟩ : syracuseStep 1812233 = 1359175) B1359175
theorem B4073287 : Blo 1072617 4073287 := bstep (se 1 (by rfl) ⟨3054965, by rfl⟩ : syracuseStep 4073287 = 6109931) B6109931
theorem B8169659 : Blo 1072617 8169659 := bstep (se 1 (by rfl) ⟨6127244, by rfl⟩ : syracuseStep 8169659 = 12254489) B12254489
theorem B35858765 : Blo 1072617 35858765 := bstep (se 3 (by rfl) ⟨6723518, by rfl⟩ : syracuseStep 35858765 = 13447037) B13447037
theorem B6367997 : Blo 1072617 6367997 := bstep (se 3 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 6367997 = 2387999) B2387999
theorem B1747835 : Blo 1072617 1747835 := bstep (se 1 (by rfl) ⟨1310876, by rfl⟩ : syracuseStep 1747835 = 2621753) B2621753
theorem B1813691 : Blo 1072617 1813691 := bstep (se 1 (by rfl) ⟨1360268, by rfl⟩ : syracuseStep 1813691 = 2720537) B2720537
theorem B4894033 : Blo 1072617 4894033 := bstep (se 2 (by rfl) ⟨1835262, by rfl⟩ : syracuseStep 4894033 = 3670525) B3670525
theorem B8171603 : Blo 1072617 8171603 := bstep (se 1 (by rfl) ⟨6128702, by rfl⟩ : syracuseStep 8171603 = 12257405) B12257405
theorem B24785189 : Blo 1072617 24785189 := bstep (se 4 (by rfl) ⟨2323611, by rfl⟩ : syracuseStep 24785189 = 4647223) B4647223
theorem B19640713 : Blo 1072617 19640713 := bstep (se 2 (by rfl) ⟨7365267, by rfl⟩ : syracuseStep 19640713 = 14730535) B14730535
theorem B1814953 : Blo 1072617 1814953 := bstep (se 2 (by rfl) ⟨680607, by rfl⟩ : syracuseStep 1814953 = 1361215) B1361215
theorem B1815007 : Blo 1072617 1815007 := bstep (se 1 (by rfl) ⟨1361255, by rfl⟩ : syracuseStep 1815007 = 2722511) B2722511
theorem B1815419 : Blo 1072617 1815419 := bstep (se 1 (by rfl) ⟨1361564, by rfl⟩ : syracuseStep 1815419 = 2723129) B2723129
theorem B7746491 : Blo 1072617 7746491 := bstep (se 1 (by rfl) ⟨5809868, by rfl⟩ : syracuseStep 7746491 = 11619737) B11619737
theorem B41334299 : Blo 1072617 41334299 := bstep (se 1 (by rfl) ⟨31000724, by rfl⟩ : syracuseStep 41334299 = 62001449) B62001449
theorem B1816391 : Blo 1072617 1816391 := bstep (se 1 (by rfl) ⟨1362293, by rfl⟩ : syracuseStep 1816391 = 2724587) B2724587
theorem B1816411 : Blo 1072617 1816411 := bstep (se 1 (by rfl) ⟨1362308, by rfl⟩ : syracuseStep 1816411 = 2724617) B2724617
theorem B9189227 : Blo 1072617 9189227 := bstep (se 1 (by rfl) ⟨6891920, by rfl⟩ : syracuseStep 9189227 = 13783841) B13783841
theorem B4897115 : Blo 1072617 4897115 := bstep (se 1 (by rfl) ⟨3672836, by rfl⟩ : syracuseStep 4897115 = 7345673) B7345673
theorem B1358527 : Blo 1072617 1358527 := bstep (se 1 (by rfl) ⟨1018895, by rfl⟩ : syracuseStep 1358527 = 2037791) B2037791
theorem B47824103 : Blo 1072617 47824103 := bstep (se 1 (by rfl) ⟨35868077, by rfl⟩ : syracuseStep 47824103 = 71736155) B71736155
theorem B35274329 : Blo 1072617 35274329 := bstep (se 2 (by rfl) ⟨13227873, by rfl⟩ : syracuseStep 35274329 = 26455747) B26455747
theorem B4079423 : Blo 1072617 4079423 := bstep (se 1 (by rfl) ⟨3059567, by rfl⟩ : syracuseStep 4079423 = 6119135) B6119135
theorem B4079879 : Blo 1072617 4079879 := bstep (se 1 (by rfl) ⟨3059909, by rfl⟩ : syracuseStep 4079879 = 6119819) B6119819
theorem B4080395 : Blo 1072617 4080395 := bstep (se 1 (by rfl) ⟨3060296, by rfl⟩ : syracuseStep 4080395 = 6120593) B6120593
theorem B71582615 : Blo 1072617 71582615 := bstep (se 1 (by rfl) ⟨53686961, by rfl⟩ : syracuseStep 71582615 = 107373923) B107373923
theorem B3621995 : Blo 1072617 3621995 := bstep (se 1 (by rfl) ⟨2716496, by rfl⟩ : syracuseStep 3621995 = 5432993) B5432993
theorem B3622049 : Blo 1072617 3622049 := bstep (se 2 (by rfl) ⟨1358268, by rfl⟩ : syracuseStep 3622049 = 2716537) B2716537
theorem B13780151 : Blo 1072617 13780151 := bstep (se 1 (by rfl) ⟨10335113, by rfl⟩ : syracuseStep 13780151 = 20670227) B20670227
theorem B15484679 : Blo 1072617 15484679 := bstep (se 1 (by rfl) ⟨11613509, by rfl⟩ : syracuseStep 15484679 = 23227019) B23227019
theorem B4082795 : Blo 1072617 4082795 := bstep (se 1 (by rfl) ⟨3062096, by rfl⟩ : syracuseStep 4082795 = 6124193) B6124193
theorem B4083311 : Blo 1072617 4083311 := bstep (se 1 (by rfl) ⟨3062483, by rfl⟩ : syracuseStep 4083311 = 6124967) B6124967
theorem B15945599 : Blo 1072617 15945599 := bstep (se 1 (by rfl) ⟨11959199, by rfl⟩ : syracuseStep 15945599 = 23918399) B23918399
theorem B7852535 : Blo 1072617 7852535 := bstep (se 1 (by rfl) ⟨5889401, by rfl⟩ : syracuseStep 7852535 = 11778803) B11778803
theorem B15520319 : Blo 1072617 15520319 := bstep (se 1 (by rfl) ⟨11640239, by rfl⟩ : syracuseStep 15520319 = 23280479) B23280479
theorem B6542137 : Blo 1072617 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B2905217 : Blo 1072617 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B3626639 : Blo 1072617 3626639 := bstep (se 1 (by rfl) ⟨2719979, by rfl⟩ : syracuseStep 3626639 = 5439959) B5439959
theorem B5167327 : Blo 1072617 5167327 := bstep (se 1 (by rfl) ⟨3875495, by rfl⟩ : syracuseStep 5167327 = 7750991) B7750991
theorem B5167403 : Blo 1072617 5167403 := bstep (se 1 (by rfl) ⟨3875552, by rfl⟩ : syracuseStep 5167403 = 7751105) B7751105
theorem B62740793 : Blo 1072617 62740793 := bstep (se 2 (by rfl) ⟨23527797, by rfl⟩ : syracuseStep 62740793 = 47055595) B47055595
theorem B9787805 : Blo 1072617 9787805 := bstep (se 3 (by rfl) ⟨1835213, by rfl⟩ : syracuseStep 9787805 = 3670427) B3670427
theorem B4086895 : Blo 1072617 4086895 := bstep (se 1 (by rfl) ⟨3065171, by rfl⟩ : syracuseStep 4086895 = 6130343) B6130343
theorem B1072623 : Blo 1072617 1072623 := bstep (se 1 (by rfl) ⟨804467, by rfl⟩ : syracuseStep 1072623 = 1608935) B1608935
theorem B2416265 : Blo 1072617 2416265 := bstep (se 2 (by rfl) ⟨906099, by rfl⟩ : syracuseStep 2416265 = 1812199) B1812199
theorem B8707769 : Blo 1072617 8707769 := bstep (se 2 (by rfl) ⟨3265413, by rfl⟩ : syracuseStep 8707769 = 6530827) B6530827
theorem B1072959 : Blo 1072617 1072959 := bstep (se 1 (by rfl) ⟨804719, by rfl⟩ : syracuseStep 1072959 = 1609439) B1609439
theorem B1073147 : Blo 1072617 1073147 := bstep (se 1 (by rfl) ⟨804860, by rfl⟩ : syracuseStep 1073147 = 1609721) B1609721
theorem B1073279 : Blo 1072617 1073279 := bstep (se 1 (by rfl) ⟨804959, by rfl⟩ : syracuseStep 1073279 = 1609919) B1609919
theorem B1073307 : Blo 1072617 1073307 := bstep (se 1 (by rfl) ⟨804980, by rfl⟩ : syracuseStep 1073307 = 1609961) B1609961
theorem B1073391 : Blo 1072617 1073391 := bstep (se 1 (by rfl) ⟨805043, by rfl⟩ : syracuseStep 1073391 = 1610087) B1610087
theorem B2416967 : Blo 1072617 2416967 := bstep (se 1 (by rfl) ⟨1812725, by rfl⟩ : syracuseStep 2416967 = 3625451) B3625451
theorem B8708447 : Blo 1072617 8708447 := bstep (se 1 (by rfl) ⟨6531335, by rfl⟩ : syracuseStep 8708447 = 13062671) B13062671
theorem B3629501 : Blo 1072617 3629501 := bstep (se 3 (by rfl) ⟨680531, by rfl⟩ : syracuseStep 3629501 = 1361063) B1361063
theorem B3629663 : Blo 1072617 3629663 := bstep (se 1 (by rfl) ⟨2722247, by rfl⟩ : syracuseStep 3629663 = 5444495) B5444495
theorem B1073947 : Blo 1072617 1073947 := bstep (se 1 (by rfl) ⟨805460, by rfl⟩ : syracuseStep 1073947 = 1610921) B1610921
theorem B1073991 : Blo 1072617 1073991 := bstep (se 1 (by rfl) ⟨805493, by rfl⟩ : syracuseStep 1073991 = 1610987) B1610987
theorem B3105607 : Blo 1072617 3105607 := bstep (se 1 (by rfl) ⟨2329205, by rfl⟩ : syracuseStep 3105607 = 4658411) B4658411
theorem B1074047 : Blo 1072617 1074047 := bstep (se 1 (by rfl) ⟨805535, by rfl⟩ : syracuseStep 1074047 = 1611071) B1611071
theorem B1074175 : Blo 1072617 1074175 := bstep (se 1 (by rfl) ⟨805631, by rfl⟩ : syracuseStep 1074175 = 1611263) B1611263
theorem B1074247 : Blo 1072617 1074247 := bstep (se 1 (by rfl) ⟨805685, by rfl⟩ : syracuseStep 1074247 = 1611371) B1611371
theorem B1074427 : Blo 1072617 1074427 := bstep (se 1 (by rfl) ⟨805820, by rfl⟩ : syracuseStep 1074427 = 1611641) B1611641
theorem B1631497 : Blo 1072617 1631497 := bstep (se 2 (by rfl) ⟨611811, by rfl⟩ : syracuseStep 1631497 = 1223623) B1223623
theorem B1074591 : Blo 1072617 1074591 := bstep (se 1 (by rfl) ⟨805943, by rfl⟩ : syracuseStep 1074591 = 1611887) B1611887
theorem B3225445829 : Blo 1072617 3225445829 := bstep (se 4 (by rfl) ⟨302385546, by rfl⟩ : syracuseStep 3225445829 = 604771093) B604771093
theorem B1074639 : Blo 1072617 1074639 := bstep (se 1 (by rfl) ⟨805979, by rfl⟩ : syracuseStep 1074639 = 1611959) B1611959
theorem B1074919 : Blo 1072617 1074919 := bstep (se 1 (by rfl) ⟨806189, by rfl⟩ : syracuseStep 1074919 = 1612379) B1612379
theorem B1074927 : Blo 1072617 1074927 := bstep (se 1 (by rfl) ⟨806195, by rfl⟩ : syracuseStep 1074927 = 1612391) B1612391
theorem B1074943 : Blo 1072617 1074943 := bstep (se 1 (by rfl) ⟨806207, by rfl⟩ : syracuseStep 1074943 = 1612415) B1612415
theorem B1075015 : Blo 1072617 1075015 := bstep (se 1 (by rfl) ⟨806261, by rfl⟩ : syracuseStep 1075015 = 1612523) B1612523
theorem B2418515 : Blo 1072617 2418515 := bstep (se 1 (by rfl) ⟨1813886, by rfl⟩ : syracuseStep 2418515 = 3627773) B3627773
theorem B1075035 : Blo 1072617 1075035 := bstep (se 1 (by rfl) ⟨806276, by rfl⟩ : syracuseStep 1075035 = 1612553) B1612553
theorem B1075195 : Blo 1072617 1075195 := bstep (se 1 (by rfl) ⟨806396, by rfl⟩ : syracuseStep 1075195 = 1612793) B1612793
theorem B17655857 : Blo 1072617 17655857 := bstep (se 2 (by rfl) ⟨6620946, by rfl⟩ : syracuseStep 17655857 = 13241893) B13241893
theorem B2418911 : Blo 1072617 2418911 := bstep (se 1 (by rfl) ⟨1814183, by rfl⟩ : syracuseStep 2418911 = 3628367) B3628367
theorem B1075615 : Blo 1072617 1075615 := bstep (se 1 (by rfl) ⟨806711, by rfl⟩ : syracuseStep 1075615 = 1613423) B1613423
theorem B1075695 : Blo 1072617 1075695 := bstep (se 1 (by rfl) ⟨806771, by rfl⟩ : syracuseStep 1075695 = 1613543) B1613543
theorem B1075879 : Blo 1072617 1075879 := bstep (se 1 (by rfl) ⟨806909, by rfl⟩ : syracuseStep 1075879 = 1613819) B1613819
theorem B1075919 : Blo 1072617 1075919 := bstep (se 1 (by rfl) ⟨806939, by rfl⟩ : syracuseStep 1075919 = 1613879) B1613879
theorem B1075999 : Blo 1072617 1075999 := bstep (se 1 (by rfl) ⟨806999, by rfl⟩ : syracuseStep 1075999 = 1613999) B1613999
theorem B1076135 : Blo 1072617 1076135 := bstep (se 1 (by rfl) ⟨807101, by rfl⟩ : syracuseStep 1076135 = 1614203) B1614203
theorem B3632039 : Blo 1072617 3632039 := bstep (se 1 (by rfl) ⟨2724029, by rfl⟩ : syracuseStep 3632039 = 5448059) B5448059
theorem B1076251 : Blo 1072617 1076251 := bstep (se 1 (by rfl) ⟨807188, by rfl⟩ : syracuseStep 1076251 = 1614377) B1614377
theorem B1076315 : Blo 1072617 1076315 := bstep (se 1 (by rfl) ⟨807236, by rfl⟩ : syracuseStep 1076315 = 1614473) B1614473
theorem B4582585 : Blo 1072617 4582585 := bstep (se 2 (by rfl) ⟨1718469, by rfl⟩ : syracuseStep 4582585 = 3436939) B3436939
theorem B1076455 : Blo 1072617 1076455 := bstep (se 1 (by rfl) ⟨807341, by rfl⟩ : syracuseStep 1076455 = 1614683) B1614683
theorem B1076479 : Blo 1072617 1076479 := bstep (se 1 (by rfl) ⟨807359, by rfl⟩ : syracuseStep 1076479 = 1614719) B1614719
theorem B1076527 : Blo 1072617 1076527 := bstep (se 1 (by rfl) ⟨807395, by rfl⟩ : syracuseStep 1076527 = 1614791) B1614791
theorem B37154213 : Blo 1072617 37154213 := bstep (se 4 (by rfl) ⟨3483207, by rfl⟩ : syracuseStep 37154213 = 6966415) B6966415
theorem B8154593 : Blo 1072617 8154593 := bstep (se 2 (by rfl) ⟨3057972, by rfl⟩ : syracuseStep 8154593 = 6115945) B6115945
theorem B5435261 : Blo 1072617 5435261 := bstep (se 3 (by rfl) ⟨1019111, by rfl⟩ : syracuseStep 5435261 = 2038223) B2038223
theorem B2420927 : Blo 1072617 2420927 := bstep (se 1 (by rfl) ⟨1815695, by rfl⟩ : syracuseStep 2420927 = 3631391) B3631391
theorem B13595129 : Blo 1072617 13595129 := bstep (se 2 (by rfl) ⟨5098173, by rfl⟩ : syracuseStep 13595129 = 10196347) B10196347
theorem B18379547 : Blo 1072617 18379547 := bstep (se 1 (by rfl) ⟨13784660, by rfl⟩ : syracuseStep 18379547 = 27569321) B27569321
theorem B2421575 : Blo 1072617 2421575 := bstep (se 1 (by rfl) ⟨1816181, by rfl⟩ : syracuseStep 2421575 = 3632363) B3632363
theorem B6878033 : Blo 1072617 6878033 := bstep (se 2 (by rfl) ⟨2579262, by rfl⟩ : syracuseStep 6878033 = 5158525) B5158525
theorem B2290943 : Blo 1072617 2290943 := bstep (se 1 (by rfl) ⟨1718207, by rfl⟩ : syracuseStep 2290943 = 3436415) B3436415
theorem B1209883 : Blo 1072617 1209883 := bstep (se 1 (by rfl) ⟨907412, by rfl⟩ : syracuseStep 1209883 = 1814825) B1814825
theorem B1210063 : Blo 1072617 1210063 := bstep (se 1 (by rfl) ⟨907547, by rfl⟩ : syracuseStep 1210063 = 1815095) B1815095
theorem B4585319 : Blo 1072617 4585319 := bstep (se 1 (by rfl) ⟨3438989, by rfl⟩ : syracuseStep 4585319 = 6877979) B6877979
theorem B4355963 : Blo 1072617 4355963 := bstep (se 1 (by rfl) ⟨3266972, by rfl⟩ : syracuseStep 4355963 = 6533945) B6533945
theorem B16775855 : Blo 1072617 16775855 := bstep (se 1 (by rfl) ⟨12581891, by rfl⟩ : syracuseStep 16775855 = 25163783) B25163783
theorem B3930875 : Blo 1072617 3930875 := bstep (se 1 (by rfl) ⟨2948156, by rfl⟩ : syracuseStep 3930875 = 5896313) B5896313
theorem B4586345 : Blo 1072617 4586345 := bstep (se 2 (by rfl) ⟨1719879, by rfl⟩ : syracuseStep 4586345 = 3439759) B3439759
theorem B17431681 : Blo 1072617 17431681 := bstep (se 2 (by rfl) ⟨6536880, by rfl⟩ : syracuseStep 17431681 = 13073761) B13073761
theorem B5438663 : Blo 1072617 5438663 := bstep (se 1 (by rfl) ⟨4078997, by rfl⟩ : syracuseStep 5438663 = 8157995) B8157995
theorem B3866039 : Blo 1072617 3866039 := bstep (se 1 (by rfl) ⟨2899529, by rfl⟩ : syracuseStep 3866039 = 5799059) B5799059
theorem B5439311 : Blo 1072617 5439311 := bstep (se 1 (by rfl) ⟨4079483, by rfl⟩ : syracuseStep 5439311 = 8158967) B8158967
theorem B5439635 : Blo 1072617 5439635 := bstep (se 1 (by rfl) ⟨4079726, by rfl⟩ : syracuseStep 5439635 = 8159453) B8159453
theorem B2719919 : Blo 1072617 2719919 := bstep (se 1 (by rfl) ⟨2039939, by rfl⟩ : syracuseStep 2719919 = 4079879) B4079879
theorem B2294095 : Blo 1072617 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B2720263 : Blo 1072617 2720263 := bstep (se 1 (by rfl) ⟨2040197, by rfl⟩ : syracuseStep 2720263 = 4080395) B4080395
theorem B10323119 : Blo 1072617 10323119 := bstep (se 1 (by rfl) ⟨7742339, by rfl⟩ : syracuseStep 10323119 = 15484679) B15484679
theorem B17434217 : Blo 1072617 17434217 := bstep (se 2 (by rfl) ⟨6537831, by rfl⟩ : syracuseStep 17434217 = 13075663) B13075663
theorem B2721833 : Blo 1072617 2721833 := bstep (se 2 (by rfl) ⟨1020687, by rfl⟩ : syracuseStep 2721833 = 2041375) B2041375
theorem B2721863 : Blo 1072617 2721863 := bstep (se 1 (by rfl) ⟨2041397, by rfl⟩ : syracuseStep 2721863 = 4082795) B4082795
theorem B2722207 : Blo 1072617 2722207 := bstep (se 1 (by rfl) ⟨2041655, by rfl⟩ : syracuseStep 2722207 = 4083311) B4083311
theorem B3869471 : Blo 1072617 3869471 := bstep (se 1 (by rfl) ⟨2902103, by rfl⟩ : syracuseStep 3869471 = 5804207) B5804207
theorem B1936811 : Blo 1072617 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B3444935 : Blo 1072617 3444935 := bstep (se 1 (by rfl) ⟨2583701, by rfl⟩ : syracuseStep 3444935 = 5167403) B5167403
theorem B6525203 : Blo 1072617 6525203 := bstep (se 1 (by rfl) ⟨4893902, by rfl⟩ : syracuseStep 6525203 = 9787805) B9787805
theorem B6525377 : Blo 1072617 6525377 := bstep (se 2 (by rfl) ⟨2447016, by rfl⟩ : syracuseStep 6525377 = 4894033) B4894033
theorem B1610843 : Blo 1072617 1610843 := bstep (se 1 (by rfl) ⟨1208132, by rfl⟩ : syracuseStep 1610843 = 2416265) B2416265
theorem B5805179 : Blo 1072617 5805179 := bstep (se 1 (by rfl) ⟨4353884, by rfl⟩ : syracuseStep 5805179 = 8707769) B8707769
theorem B9180479 : Blo 1072617 9180479 := bstep (se 1 (by rfl) ⟨6885359, by rfl⟩ : syracuseStep 9180479 = 13770719) B13770719
theorem B1611311 : Blo 1072617 1611311 := bstep (se 1 (by rfl) ⟨1208483, by rfl⟩ : syracuseStep 1611311 = 2416967) B2416967
theorem B5805631 : Blo 1072617 5805631 := bstep (se 1 (by rfl) ⟨4354223, by rfl⟩ : syracuseStep 5805631 = 8708447) B8708447
theorem B2037487 : Blo 1072617 2037487 := bstep (se 1 (by rfl) ⟨1528115, by rfl⟩ : syracuseStep 2037487 = 3056231) B3056231
theorem B26187617 : Blo 1072617 26187617 := bstep (se 2 (by rfl) ⟨9820356, by rfl⟩ : syracuseStep 26187617 = 19640713) B19640713
theorem B1612343 : Blo 1072617 1612343 := bstep (se 1 (by rfl) ⟨1209257, by rfl⟩ : syracuseStep 1612343 = 2418515) B2418515
theorem B11770571 : Blo 1072617 11770571 := bstep (se 1 (by rfl) ⟨8827928, by rfl⟩ : syracuseStep 11770571 = 17655857) B17655857
theorem B5446439 : Blo 1072617 5446439 := bstep (se 1 (by rfl) ⟨4084829, by rfl⟩ : syracuseStep 5446439 = 8169659) B8169659
theorem B1612607 : Blo 1072617 1612607 := bstep (se 1 (by rfl) ⟨1209455, by rfl⟩ : syracuseStep 1612607 = 2418911) B2418911
theorem B16981325 : Blo 1072617 16981325 := bstep (se 3 (by rfl) ⟨3183998, by rfl⟩ : syracuseStep 16981325 = 6367997) B6367997
theorem B1613177 : Blo 1072617 1613177 := bstep (se 2 (by rfl) ⟨604941, by rfl⟩ : syracuseStep 1613177 = 1209883) B1209883
theorem B1613417 : Blo 1072617 1613417 := bstep (se 2 (by rfl) ⟨605031, by rfl⟩ : syracuseStep 1613417 = 1210063) B1210063
theorem B5447735 : Blo 1072617 5447735 := bstep (se 1 (by rfl) ⟨4085801, by rfl⟩ : syracuseStep 5447735 = 8171603) B8171603
theorem B1613951 : Blo 1072617 1613951 := bstep (se 1 (by rfl) ⟨1210463, by rfl⟩ : syracuseStep 1613951 = 2420927) B2420927
theorem B16523459 : Blo 1072617 16523459 := bstep (se 1 (by rfl) ⟨12392594, by rfl⟩ : syracuseStep 16523459 = 24785189) B24785189
theorem B6889769 : Blo 1072617 6889769 := bstep (se 2 (by rfl) ⟨2583663, by rfl⟩ : syracuseStep 6889769 = 5167327) B5167327
theorem B1614383 : Blo 1072617 1614383 := bstep (se 1 (by rfl) ⟨1210787, by rfl⟩ : syracuseStep 1614383 = 2421575) B2421575
theorem B1811369 : Blo 1072617 1811369 := bstep (se 2 (by rfl) ⟨679263, by rfl⟩ : syracuseStep 1811369 = 1358527) B1358527
theorem B3056879 : Blo 1072617 3056879 := bstep (se 1 (by rfl) ⟨2292659, by rfl⟩ : syracuseStep 3056879 = 4585319) B4585319
theorem B5449193 : Blo 1072617 5449193 := bstep (se 2 (by rfl) ⟨2043447, by rfl⟩ : syracuseStep 5449193 = 4086895) B4086895
theorem B23242241 : Blo 1072617 23242241 := bstep (se 2 (by rfl) ⟨8715840, by rfl⟩ : syracuseStep 23242241 = 17431681) B17431681
theorem B11183903 : Blo 1072617 11183903 := bstep (se 1 (by rfl) ⟨8387927, by rfl⟩ : syracuseStep 11183903 = 16775855) B16775855
theorem B4073273 : Blo 1072617 4073273 := bstep (se 2 (by rfl) ⟨1527477, by rfl⟩ : syracuseStep 4073273 = 3054955) B3054955
theorem B3057563 : Blo 1072617 3057563 := bstep (se 1 (by rfl) ⟨2293172, by rfl⟩ : syracuseStep 3057563 = 4586345) B4586345
theorem B47721743 : Blo 1072617 47721743 := bstep (se 1 (by rfl) ⟨35791307, by rfl⟩ : syracuseStep 47721743 = 71582615) B71582615
theorem B9186767 : Blo 1072617 9186767 := bstep (se 1 (by rfl) ⟨6890075, by rfl⟩ : syracuseStep 9186767 = 13780151) B13780151
theorem B4140809 : Blo 1072617 4140809 := bstep (se 2 (by rfl) ⟨1552803, by rfl⟩ : syracuseStep 4140809 = 3105607) B3105607
theorem B5156639 : Blo 1072617 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B1814683 : Blo 1072617 1814683 := bstep (se 1 (by rfl) ⟨1361012, by rfl⟩ : syracuseStep 1814683 = 2722025) B2722025
theorem B5157083 : Blo 1072617 5157083 := bstep (se 1 (by rfl) ⟨3867812, by rfl⟩ : syracuseStep 5157083 = 7735625) B7735625
theorem B2175329 : Blo 1072617 2175329 := bstep (se 2 (by rfl) ⟨815748, by rfl⟩ : syracuseStep 2175329 = 1631497) B1631497
theorem B3060251 : Blo 1072617 3060251 := bstep (se 1 (by rfl) ⟨2295188, by rfl⟩ : syracuseStep 3060251 = 4590377) B4590377
theorem B10630399 : Blo 1072617 10630399 := bstep (se 1 (by rfl) ⟨7972799, by rfl⟩ : syracuseStep 10630399 = 15945599) B15945599
theorem B8173547 : Blo 1072617 8173547 := bstep (se 1 (by rfl) ⟨6130160, by rfl⟩ : syracuseStep 8173547 = 12260321) B12260321
theorem B6109181 : Blo 1072617 6109181 := bstep (se 3 (by rfl) ⟨1145471, by rfl⟩ : syracuseStep 6109181 = 2290943) B2290943
theorem B1357879 : Blo 1072617 1357879 := bstep (se 1 (by rfl) ⟨1018409, by rfl⟩ : syracuseStep 1357879 = 2036819) B2036819
theorem B41827195 : Blo 1072617 41827195 := bstep (se 1 (by rfl) ⟨31370396, by rfl⟩ : syracuseStep 41827195 = 62740793) B62740793
theorem B6110113 : Blo 1072617 6110113 := bstep (se 2 (by rfl) ⟨2291292, by rfl⟩ : syracuseStep 6110113 = 4582585) B4582585
theorem B1359919 : Blo 1072617 1359919 := bstep (se 1 (by rfl) ⟨1019939, by rfl⟩ : syracuseStep 1359919 = 2039879) B2039879
theorem B4899001 : Blo 1072617 4899001 := bstep (se 2 (by rfl) ⟨1837125, by rfl⟩ : syracuseStep 4899001 = 3674251) B3674251
theorem B6209833 : Blo 1072617 6209833 := bstep (se 2 (by rfl) ⟨2328687, by rfl⟩ : syracuseStep 6209833 = 4657375) B4657375
theorem B13746935 : Blo 1072617 13746935 := bstep (se 1 (by rfl) ⟨10310201, by rfl⟩ : syracuseStep 13746935 = 20620403) B20620403
theorem B23905843 : Blo 1072617 23905843 := bstep (se 1 (by rfl) ⟨17929382, by rfl⟩ : syracuseStep 23905843 = 35858765) B35858765
theorem B1165223 : Blo 1072617 1165223 := bstep (se 1 (by rfl) ⟨873917, by rfl⟩ : syracuseStep 1165223 = 1747835) B1747835
theorem B3623507 : Blo 1072617 3623507 := bstep (se 1 (by rfl) ⟨2717630, by rfl⟩ : syracuseStep 3623507 = 5435261) B5435261
theorem B9063419 : Blo 1072617 9063419 := bstep (se 1 (by rfl) ⟨6797564, by rfl⟩ : syracuseStep 9063419 = 13595129) B13595129
theorem B5164327 : Blo 1072617 5164327 := bstep (se 1 (by rfl) ⟨3873245, by rfl⟩ : syracuseStep 5164327 = 7746491) B7746491
theorem B20630861 : Blo 1072617 20630861 := bstep (se 3 (by rfl) ⟨3868286, by rfl⟩ : syracuseStep 20630861 = 7736573) B7736573
theorem B2903975 : Blo 1072617 2903975 := bstep (se 1 (by rfl) ⟨2177981, by rfl⟩ : syracuseStep 2903975 = 4355963) B4355963
theorem B3264743 : Blo 1072617 3264743 := bstep (se 1 (by rfl) ⟨2448557, by rfl⟩ : syracuseStep 3264743 = 4897115) B4897115
theorem B3625775 : Blo 1072617 3625775 := bstep (se 1 (by rfl) ⟨2719331, by rfl⟩ : syracuseStep 3625775 = 5438663) B5438663
theorem B2577359 : Blo 1072617 2577359 := bstep (se 1 (by rfl) ⟨1933019, by rfl⟩ : syracuseStep 2577359 = 3866039) B3866039
theorem B23516219 : Blo 1072617 23516219 := bstep (se 1 (by rfl) ⟨17637164, by rfl⟩ : syracuseStep 23516219 = 35274329) B35274329
theorem B2413673 : Blo 1072617 2413673 := bstep (se 2 (by rfl) ⟨905127, by rfl⟩ : syracuseStep 2413673 = 1810255) B1810255
theorem B3626207 : Blo 1072617 3626207 := bstep (se 1 (by rfl) ⟨2719655, by rfl⟩ : syracuseStep 3626207 = 5439311) B5439311
theorem B2414663 : Blo 1072617 2414663 := bstep (se 1 (by rfl) ⟨1810997, by rfl⟩ : syracuseStep 2414663 = 3621995) B3621995
theorem B2414699 : Blo 1072617 2414699 := bstep (se 1 (by rfl) ⟨1811024, by rfl⟩ : syracuseStep 2414699 = 3622049) B3622049
theorem B15686075 : Blo 1072617 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B3627611 : Blo 1072617 3627611 := bstep (se 1 (by rfl) ⟨2720708, by rfl⟩ : syracuseStep 3627611 = 5441417) B5441417
theorem B2579339 : Blo 1072617 2579339 := bstep (se 1 (by rfl) ⟨1934504, by rfl⟩ : syracuseStep 2579339 = 3869009) B3869009
theorem B1530991 : Blo 1072617 1530991 := bstep (se 1 (by rfl) ⟨1148243, by rfl⟩ : syracuseStep 1530991 = 2296487) B2296487
theorem B5430401 : Blo 1072617 5430401 := bstep (se 2 (by rfl) ⟨2036400, by rfl⟩ : syracuseStep 5430401 = 4072801) B4072801
theorem B3628313 : Blo 1072617 3628313 := bstep (se 2 (by rfl) ⟨1360617, by rfl⟩ : syracuseStep 3628313 = 2721235) B2721235
theorem B2448703 : Blo 1072617 2448703 := bstep (se 1 (by rfl) ⟨1836527, by rfl⟩ : syracuseStep 2448703 = 3673055) B3673055
theorem B5431049 : Blo 1072617 5431049 := bstep (se 2 (by rfl) ⟨2036643, by rfl⟩ : syracuseStep 5431049 = 4073287) B4073287
theorem B2908007 : Blo 1072617 2908007 := bstep (se 1 (by rfl) ⟨2181005, by rfl⟩ : syracuseStep 2908007 = 4362011) B4362011
theorem B1072999 : Blo 1072617 1072999 := bstep (se 1 (by rfl) ⟨804749, by rfl⟩ : syracuseStep 1072999 = 1609499) B1609499
theorem B1073055 : Blo 1072617 1073055 := bstep (se 1 (by rfl) ⟨804791, by rfl⟩ : syracuseStep 1073055 = 1609583) B1609583
theorem B5235023 : Blo 1072617 5235023 := bstep (se 1 (by rfl) ⟨3926267, by rfl⟩ : syracuseStep 5235023 = 7852535) B7852535
theorem B10346879 : Blo 1072617 10346879 := bstep (se 1 (by rfl) ⟨7760159, by rfl⟩ : syracuseStep 10346879 = 15520319) B15520319
theorem B1073567 : Blo 1072617 1073567 := bstep (se 1 (by rfl) ⟨805175, by rfl⟩ : syracuseStep 1073567 = 1610351) B1610351
theorem B45310369 : Blo 1072617 45310369 := bstep (se 2 (by rfl) ⟨16991388, by rfl⟩ : syracuseStep 45310369 = 33982777) B33982777
theorem B1073647 : Blo 1072617 1073647 := bstep (se 1 (by rfl) ⟨805235, by rfl⟩ : syracuseStep 1073647 = 1610471) B1610471
theorem B1074023 : Blo 1072617 1074023 := bstep (se 1 (by rfl) ⟨805517, by rfl⟩ : syracuseStep 1074023 = 1611035) B1611035
theorem B2417759 : Blo 1072617 2417759 := bstep (se 1 (by rfl) ⟨1813319, by rfl⟩ : syracuseStep 2417759 = 3626639) B3626639
theorem B1074335 : Blo 1072617 1074335 := bstep (se 1 (by rfl) ⟨805751, by rfl⟩ : syracuseStep 1074335 = 1611503) B1611503
theorem B10314971 : Blo 1072617 10314971 := bstep (se 1 (by rfl) ⟨7736228, by rfl⟩ : syracuseStep 10314971 = 15472457) B15472457
theorem B34891397 : Blo 1072617 34891397 := bstep (se 4 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 34891397 = 6542137) B6542137
theorem B26175473 : Blo 1072617 26175473 := bstep (se 2 (by rfl) ⟨9815802, by rfl⟩ : syracuseStep 26175473 = 19631605) B19631605
theorem B1075271 : Blo 1072617 1075271 := bstep (se 1 (by rfl) ⟨806453, by rfl⟩ : syracuseStep 1075271 = 1612907) B1612907
theorem B1075431 : Blo 1072617 1075431 := bstep (se 1 (by rfl) ⟨806573, by rfl⟩ : syracuseStep 1075431 = 1613147) B1613147
theorem B1075519 : Blo 1072617 1075519 := bstep (se 1 (by rfl) ⟨806639, by rfl⟩ : syracuseStep 1075519 = 1613279) B1613279
theorem B2124431 : Blo 1072617 2124431 := bstep (se 1 (by rfl) ⟨1593323, by rfl⟩ : syracuseStep 2124431 = 3186647) B3186647
theorem B1075871 : Blo 1072617 1075871 := bstep (se 1 (by rfl) ⟨806903, by rfl⟩ : syracuseStep 1075871 = 1613807) B1613807
theorem B1075951 : Blo 1072617 1075951 := bstep (se 1 (by rfl) ⟨806963, by rfl⟩ : syracuseStep 1075951 = 1613927) B1613927
theorem B1076031 : Blo 1072617 1076031 := bstep (se 1 (by rfl) ⟨807023, by rfl⟩ : syracuseStep 1076031 = 1614047) B1614047
theorem B1076039 : Blo 1072617 1076039 := bstep (se 1 (by rfl) ⟨807029, by rfl⟩ : syracuseStep 1076039 = 1614059) B1614059
theorem B1076071 : Blo 1072617 1076071 := bstep (se 1 (by rfl) ⟨807053, by rfl⟩ : syracuseStep 1076071 = 1614107) B1614107
theorem B1076079 : Blo 1072617 1076079 := bstep (se 1 (by rfl) ⟨807059, by rfl⟩ : syracuseStep 1076079 = 1614119) B1614119
theorem B2419667 : Blo 1072617 2419667 := bstep (se 1 (by rfl) ⟨1814750, by rfl⟩ : syracuseStep 2419667 = 3629501) B3629501
theorem B1076207 : Blo 1072617 1076207 := bstep (se 1 (by rfl) ⟨807155, by rfl⟩ : syracuseStep 1076207 = 1614311) B1614311
theorem B8154107 : Blo 1072617 8154107 := bstep (se 1 (by rfl) ⟨6115580, by rfl⟩ : syracuseStep 8154107 = 12231161) B12231161
theorem B2419775 : Blo 1072617 2419775 := bstep (se 1 (by rfl) ⟨1814831, by rfl⟩ : syracuseStep 2419775 = 3629663) B3629663
theorem B1076327 : Blo 1072617 1076327 := bstep (se 1 (by rfl) ⟨807245, by rfl⟩ : syracuseStep 1076327 = 1614491) B1614491
theorem B2419937 : Blo 1072617 2419937 := bstep (se 2 (by rfl) ⟨907476, by rfl⟩ : syracuseStep 2419937 = 1814953) B1814953
theorem B2420009 : Blo 1072617 2420009 := bstep (se 2 (by rfl) ⟨907503, by rfl⟩ : syracuseStep 2420009 = 1815007) B1815007
theorem B2150297219 : Blo 1072617 2150297219 := bstep (se 1 (by rfl) ⟨1612722914, by rfl⟩ : syracuseStep 2150297219 = 3225445829) B3225445829
theorem B1208155 : Blo 1072617 1208155 := bstep (se 1 (by rfl) ⟨906116, by rfl⟩ : syracuseStep 1208155 = 1812233) B1812233
theorem B2716001 : Blo 1072617 2716001 := bstep (se 2 (by rfl) ⟨1018500, by rfl⟩ : syracuseStep 2716001 = 2037001) B2037001
theorem B2421359 : Blo 1072617 2421359 := bstep (se 1 (by rfl) ⟨1816019, by rfl⟩ : syracuseStep 2421359 = 3632039) B3632039
theorem B1209127 : Blo 1072617 1209127 := bstep (se 1 (by rfl) ⟨906845, by rfl⟩ : syracuseStep 1209127 = 1813691) B1813691
theorem B24769475 : Blo 1072617 24769475 := bstep (se 1 (by rfl) ⟨18577106, by rfl⟩ : syracuseStep 24769475 = 37154213) B37154213
theorem B5436395 : Blo 1072617 5436395 := bstep (se 1 (by rfl) ⟨4077296, by rfl⟩ : syracuseStep 5436395 = 8154593) B8154593
theorem B2421881 : Blo 1072617 2421881 := bstep (se 2 (by rfl) ⟨908205, by rfl⟩ : syracuseStep 2421881 = 1816411) B1816411
theorem B12253031 : Blo 1072617 12253031 := bstep (se 1 (by rfl) ⟨9189773, by rfl⟩ : syracuseStep 12253031 = 18379547) B18379547
theorem B4585355 : Blo 1072617 4585355 := bstep (se 1 (by rfl) ⟨3439016, by rfl⟩ : syracuseStep 4585355 = 6878033) B6878033
theorem B1210279 : Blo 1072617 1210279 := bstep (se 1 (by rfl) ⟨907709, by rfl⟩ : syracuseStep 1210279 = 1815419) B1815419
theorem B127530941 : Blo 1072617 127530941 := bstep (se 3 (by rfl) ⟨23912051, by rfl⟩ : syracuseStep 127530941 = 47824103) B47824103
theorem B2717945 : Blo 1072617 2717945 := bstep (se 2 (by rfl) ⟨1019229, by rfl⟩ : syracuseStep 2717945 = 2038459) B2038459
theorem B27556199 : Blo 1072617 27556199 := bstep (se 1 (by rfl) ⟨20667149, by rfl⟩ : syracuseStep 27556199 = 41334299) B41334299
theorem B1210927 : Blo 1072617 1210927 := bstep (se 1 (by rfl) ⟨908195, by rfl⟩ : syracuseStep 1210927 = 1816391) B1816391
theorem B6126151 : Blo 1072617 6126151 := bstep (se 1 (by rfl) ⟨4594613, by rfl⟩ : syracuseStep 6126151 = 9189227) B9189227
theorem B2620583 : Blo 1072617 2620583 := bstep (se 1 (by rfl) ⟨1965437, by rfl⟩ : syracuseStep 2620583 = 3930875) B3930875
theorem B2719615 : Blo 1072617 2719615 := bstep (se 1 (by rfl) ⟨2039711, by rfl⟩ : syracuseStep 2719615 = 4079423) B4079423
theorem B6882079 : Blo 1072617 6882079 := bstep (se 1 (by rfl) ⟨5161559, by rfl⟩ : syracuseStep 6882079 = 10323119) B10323119
theorem B1935983 : Blo 1072617 1935983 := bstep (se 1 (by rfl) ⟨1451987, by rfl⟩ : syracuseStep 1935983 = 2903975) B2903975
theorem B69602165 : Blo 1072617 69602165 := bstep (se 5 (by rfl) ⟨3262601, by rfl⟩ : syracuseStep 69602165 = 6525203) B6525203
theorem B1609115 : Blo 1072617 1609115 := bstep (se 1 (by rfl) ⟨1206836, by rfl⟩ : syracuseStep 1609115 = 2413673) B2413673
theorem B3870119 : Blo 1072617 3870119 := bstep (se 1 (by rfl) ⟨2902589, by rfl⟩ : syracuseStep 3870119 = 5805179) B5805179
theorem B1609775 : Blo 1072617 1609775 := bstep (se 1 (by rfl) ⟨1207331, by rfl⟩ : syracuseStep 1609775 = 2414663) B2414663
theorem B1609799 : Blo 1072617 1609799 := bstep (se 1 (by rfl) ⟨1207349, by rfl⟩ : syracuseStep 1609799 = 2414699) B2414699
theorem B1610873 : Blo 1072617 1610873 := bstep (se 2 (by rfl) ⟨604077, by rfl⟩ : syracuseStep 1610873 = 1208155) B1208155
theorem B1938671 : Blo 1072617 1938671 := bstep (se 1 (by rfl) ⟨1454003, by rfl⟩ : syracuseStep 1938671 = 2908007) B2908007
theorem B11015639 : Blo 1072617 11015639 := bstep (se 1 (by rfl) ⟨8261729, by rfl⟩ : syracuseStep 11015639 = 16523459) B16523459
theorem B4593179 : Blo 1072617 4593179 := bstep (se 1 (by rfl) ⟨3444884, by rfl⟩ : syracuseStep 4593179 = 6889769) B6889769
theorem B8165285 : Blo 1072617 8165285 := bstep (se 4 (by rfl) ⟨765495, by rfl⟩ : syracuseStep 8165285 = 1530991) B1530991
theorem B1611839 : Blo 1072617 1611839 := bstep (se 1 (by rfl) ⟨1208879, by rfl⟩ : syracuseStep 1611839 = 2417759) B2417759
theorem B1612169 : Blo 1072617 1612169 := bstep (se 2 (by rfl) ⟨604563, by rfl⟩ : syracuseStep 1612169 = 1209127) B1209127
theorem B2038375 : Blo 1072617 2038375 := bstep (se 1 (by rfl) ⟨1528781, by rfl⟩ : syracuseStep 2038375 = 3057563) B3057563
theorem B1416287 : Blo 1072617 1416287 := bstep (se 1 (by rfl) ⟨1062215, by rfl⟩ : syracuseStep 1416287 = 2124431) B2124431
theorem B1613111 : Blo 1072617 1613111 := bstep (se 1 (by rfl) ⟨1209833, by rfl⟩ : syracuseStep 1613111 = 2419667) B2419667
theorem B1613183 : Blo 1072617 1613183 := bstep (se 1 (by rfl) ⟨1209887, by rfl⟩ : syracuseStep 1613183 = 2419775) B2419775
theorem B7740841 : Blo 1072617 7740841 := bstep (se 2 (by rfl) ⟨2902815, by rfl⟩ : syracuseStep 7740841 = 5805631) B5805631
theorem B1613291 : Blo 1072617 1613291 := bstep (se 1 (by rfl) ⟨1209968, by rfl⟩ : syracuseStep 1613291 = 2419937) B2419937
theorem B1613339 : Blo 1072617 1613339 := bstep (se 1 (by rfl) ⟨1210004, by rfl⟩ : syracuseStep 1613339 = 2420009) B2420009
theorem B2760539 : Blo 1072617 2760539 := bstep (se 1 (by rfl) ⟨2070404, by rfl⟩ : syracuseStep 2760539 = 4140809) B4140809
theorem B1613705 : Blo 1072617 1613705 := bstep (se 2 (by rfl) ⟨605139, by rfl⟩ : syracuseStep 1613705 = 1210279) B1210279
theorem B1810505 : Blo 1072617 1810505 := bstep (se 2 (by rfl) ⟨678939, by rfl⟩ : syracuseStep 1810505 = 1357879) B1357879
theorem B1810667 : Blo 1072617 1810667 := bstep (se 1 (by rfl) ⟨1358000, by rfl⟩ : syracuseStep 1810667 = 2716001) B2716001
theorem B1450219 : Blo 1072617 1450219 := bstep (se 1 (by rfl) ⟨1087664, by rfl⟩ : syracuseStep 1450219 = 2175329) B2175329
theorem B2040167 : Blo 1072617 2040167 := bstep (se 1 (by rfl) ⟨1530125, by rfl⟩ : syracuseStep 2040167 = 3060251) B3060251
theorem B1614239 : Blo 1072617 1614239 := bstep (se 1 (by rfl) ⟨1210679, by rfl⟩ : syracuseStep 1614239 = 2421359) B2421359
theorem B1614569 : Blo 1072617 1614569 := bstep (se 2 (by rfl) ⟨605463, by rfl⟩ : syracuseStep 1614569 = 1210927) B1210927
theorem B1614587 : Blo 1072617 1614587 := bstep (se 1 (by rfl) ⟨1210940, by rfl⟩ : syracuseStep 1614587 = 2421881) B2421881
theorem B8168201 : Blo 1072617 8168201 := bstep (se 2 (by rfl) ⟨3063075, by rfl⟩ : syracuseStep 8168201 = 6126151) B6126151
theorem B8168687 : Blo 1072617 8168687 := bstep (se 1 (by rfl) ⟨6126515, by rfl⟩ : syracuseStep 8168687 = 12253031) B12253031
theorem B3056903 : Blo 1072617 3056903 := bstep (se 1 (by rfl) ⟨2292677, by rfl⟩ : syracuseStep 3056903 = 4585355) B4585355
theorem B5449031 : Blo 1072617 5449031 := bstep (se 1 (by rfl) ⟨4086773, by rfl⟩ : syracuseStep 5449031 = 8173547) B8173547
theorem B4072787 : Blo 1072617 4072787 := bstep (se 1 (by rfl) ⟨3054590, by rfl⟩ : syracuseStep 4072787 = 6109181) B6109181
theorem B1811963 : Blo 1072617 1811963 := bstep (se 1 (by rfl) ⟨1358972, by rfl⟩ : syracuseStep 1811963 = 2717945) B2717945
theorem B1747055 : Blo 1072617 1747055 := bstep (se 1 (by rfl) ⟨1310291, by rfl⟩ : syracuseStep 1747055 = 2620583) B2620583
theorem B1813225 : Blo 1072617 1813225 := bstep (se 2 (by rfl) ⟨679959, by rfl⟩ : syracuseStep 1813225 = 1359919) B1359919
theorem B1813279 : Blo 1072617 1813279 := bstep (se 1 (by rfl) ⟨1359959, by rfl⟩ : syracuseStep 1813279 = 2719919) B2719919
theorem B6532001 : Blo 1072617 6532001 := bstep (se 2 (by rfl) ⟨2449500, by rfl⟩ : syracuseStep 6532001 = 4899001) B4899001
theorem B3058793 : Blo 1072617 3058793 := bstep (se 2 (by rfl) ⟨1147047, by rfl⟩ : syracuseStep 3058793 = 2294095) B2294095
theorem B9186493 : Blo 1072617 9186493 := bstep (se 3 (by rfl) ⟨1722467, by rfl⟩ : syracuseStep 9186493 = 3444935) B3444935
theorem B1814555 : Blo 1072617 1814555 := bstep (se 1 (by rfl) ⟨1360916, by rfl⟩ : syracuseStep 1814555 = 2721833) B2721833
theorem B1814575 : Blo 1072617 1814575 := bstep (se 1 (by rfl) ⟨1360931, by rfl⟩ : syracuseStep 1814575 = 2721863) B2721863
theorem B15677479 : Blo 1072617 15677479 := bstep (se 1 (by rfl) ⟨11758109, by rfl⟩ : syracuseStep 15677479 = 23516219) B23516219
theorem B7847047 : Blo 1072617 7847047 := bstep (se 1 (by rfl) ⟨5885285, by rfl⟩ : syracuseStep 7847047 = 11770571) B11770571
theorem B1719559 : Blo 1072617 1719559 := bstep (se 1 (by rfl) ⟨1289669, by rfl⟩ : syracuseStep 1719559 = 2579339) B2579339
theorem B3620267 : Blo 1072617 3620267 := bstep (se 1 (by rfl) ⟨2715200, by rfl⟩ : syracuseStep 3620267 = 5430401) B5430401
theorem B11320883 : Blo 1072617 11320883 := bstep (se 1 (by rfl) ⟨8490662, by rfl⟩ : syracuseStep 11320883 = 16981325) B16981325
theorem B340082509 : Blo 1072617 340082509 := bstep (se 3 (by rfl) ⟨63765470, by rfl⟩ : syracuseStep 340082509 = 127530941) B127530941
theorem B3620699 : Blo 1072617 3620699 := bstep (se 1 (by rfl) ⟨2715524, by rfl⟩ : syracuseStep 3620699 = 5431049) B5431049
theorem B3490015 : Blo 1072617 3490015 := bstep (se 1 (by rfl) ⟨2617511, by rfl⟩ : syracuseStep 3490015 = 5235023) B5235023
theorem B6897919 : Blo 1072617 6897919 := bstep (se 1 (by rfl) ⟨5173439, by rfl⟩ : syracuseStep 6897919 = 10346879) B10346879
theorem B41829533 : Blo 1072617 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B7455935 : Blo 1072617 7455935 := bstep (se 1 (by rfl) ⟨5591951, by rfl⟩ : syracuseStep 7455935 = 11183903) B11183903
theorem B17450315 : Blo 1072617 17450315 := bstep (se 1 (by rfl) ⟨13087736, by rfl⟩ : syracuseStep 17450315 = 26175473) B26175473
theorem B27543077 : Blo 1072617 27543077 := bstep (se 4 (by rfl) ⟨2582163, by rfl⟩ : syracuseStep 27543077 = 5164327) B5164327
theorem B14173865 : Blo 1072617 14173865 := bstep (se 2 (by rfl) ⟨5315199, by rfl⟩ : syracuseStep 14173865 = 10630399) B10630399
theorem B24169117 : Blo 1072617 24169117 := bstep (se 3 (by rfl) ⟨4531709, by rfl⟩ : syracuseStep 24169117 = 9063419) B9063419
theorem B3624263 : Blo 1072617 3624263 := bstep (se 1 (by rfl) ⟨2718197, by rfl⟩ : syracuseStep 3624263 = 5436395) B5436395
theorem B5164829 : Blo 1072617 5164829 := bstep (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) B1936811
theorem B8146817 : Blo 1072617 8146817 := bstep (se 2 (by rfl) ⟨3055056, by rfl⟩ : syracuseStep 8146817 = 6110113) B6110113
theorem B18370799 : Blo 1072617 18370799 := bstep (se 1 (by rfl) ⟨13778099, by rfl⟩ : syracuseStep 18370799 = 27556199) B27556199
theorem B5734125917 : Blo 1072617 5734125917 := bstep (se 3 (by rfl) ⟨1075148609, by rfl⟩ : syracuseStep 5734125917 = 2150297219) B2150297219
theorem B3264937 : Blo 1072617 3264937 := bstep (se 2 (by rfl) ⟨1224351, by rfl⟩ : syracuseStep 3264937 = 2448703) B2448703
theorem B3626153 : Blo 1072617 3626153 := bstep (se 2 (by rfl) ⟨1359807, by rfl⟩ : syracuseStep 3626153 = 2719615) B2719615
theorem B3626423 : Blo 1072617 3626423 := bstep (se 1 (by rfl) ⟨2719817, by rfl⟩ : syracuseStep 3626423 = 5439635) B5439635
theorem B8279777 : Blo 1072617 8279777 := bstep (se 2 (by rfl) ⟨3104916, by rfl⟩ : syracuseStep 8279777 = 6209833) B6209833
theorem B9164623 : Blo 1072617 9164623 := bstep (se 1 (by rfl) ⟨6873467, by rfl⟩ : syracuseStep 9164623 = 13746935) B13746935
theorem B60413825 : Blo 1072617 60413825 := bstep (se 2 (by rfl) ⟨22655184, by rfl⟩ : syracuseStep 60413825 = 45310369) B45310369
theorem B8705981 : Blo 1072617 8705981 := bstep (se 3 (by rfl) ⟨1632371, by rfl⟩ : syracuseStep 8705981 = 3264743) B3264743
theorem B3627017 : Blo 1072617 3627017 := bstep (se 2 (by rfl) ⟨1360131, by rfl⟩ : syracuseStep 3627017 = 2720263) B2720263
theorem B2415671 : Blo 1072617 2415671 := bstep (se 1 (by rfl) ⟨1811753, by rfl⟩ : syracuseStep 2415671 = 3623507) B3623507
theorem B2579647 : Blo 1072617 2579647 := bstep (se 1 (by rfl) ⟨1934735, by rfl⟩ : syracuseStep 2579647 = 3869471) B3869471
theorem B13753907 : Blo 1072617 13753907 := bstep (se 1 (by rfl) ⟨10315430, by rfl⟩ : syracuseStep 13753907 = 20630861) B20630861
theorem B6872957 : Blo 1072617 6872957 := bstep (se 3 (by rfl) ⟨1288679, by rfl⟩ : syracuseStep 6872957 = 2577359) B2577359
theorem B4350251 : Blo 1072617 4350251 := bstep (se 1 (by rfl) ⟨3262688, by rfl⟩ : syracuseStep 4350251 = 6525377) B6525377
theorem B2417183 : Blo 1072617 2417183 := bstep (se 1 (by rfl) ⟨1812887, by rfl⟩ : syracuseStep 2417183 = 3625775) B3625775
theorem B3629609 : Blo 1072617 3629609 := bstep (se 2 (by rfl) ⟨1361103, by rfl⟩ : syracuseStep 3629609 = 2722207) B2722207
theorem B8151677 : Blo 1072617 8151677 := bstep (se 3 (by rfl) ⟨1528439, by rfl⟩ : syracuseStep 8151677 = 3056879) B3056879
theorem B1073895 : Blo 1072617 1073895 := bstep (se 1 (by rfl) ⟨805421, by rfl⟩ : syracuseStep 1073895 = 1610843) B1610843
theorem B2417471 : Blo 1072617 2417471 := bstep (se 1 (by rfl) ⟨1813103, by rfl⟩ : syracuseStep 2417471 = 3626207) B3626207
theorem B6120319 : Blo 1072617 6120319 := bstep (se 1 (by rfl) ⟨4590239, by rfl⟩ : syracuseStep 6120319 = 9180479) B9180479
theorem B1074207 : Blo 1072617 1074207 := bstep (se 1 (by rfl) ⟨805655, by rfl⟩ : syracuseStep 1074207 = 1611311) B1611311
theorem B17458411 : Blo 1072617 17458411 := bstep (se 1 (by rfl) ⟨13093808, by rfl⟩ : syracuseStep 17458411 = 26187617) B26187617
theorem B46491245 : Blo 1072617 46491245 := bstep (se 3 (by rfl) ⟨8717108, by rfl⟩ : syracuseStep 46491245 = 17434217) B17434217
theorem B1074895 : Blo 1072617 1074895 := bstep (se 1 (by rfl) ⟨806171, by rfl⟩ : syracuseStep 1074895 = 1612343) B1612343
theorem B2418407 : Blo 1072617 2418407 := bstep (se 1 (by rfl) ⟨1813805, by rfl⟩ : syracuseStep 2418407 = 3627611) B3627611
theorem B3630959 : Blo 1072617 3630959 := bstep (se 1 (by rfl) ⟨2723219, by rfl⟩ : syracuseStep 3630959 = 5446439) B5446439
theorem B1075071 : Blo 1072617 1075071 := bstep (se 1 (by rfl) ⟨806303, by rfl⟩ : syracuseStep 1075071 = 1612607) B1612607
theorem B2418875 : Blo 1072617 2418875 := bstep (se 1 (by rfl) ⟨1814156, by rfl⟩ : syracuseStep 2418875 = 3628313) B3628313
theorem B1075451 : Blo 1072617 1075451 := bstep (se 1 (by rfl) ⟨806588, by rfl⟩ : syracuseStep 1075451 = 1613177) B1613177
theorem B1075611 : Blo 1072617 1075611 := bstep (se 1 (by rfl) ⟨806708, by rfl⟩ : syracuseStep 1075611 = 1613417) B1613417
theorem B3107261 : Blo 1072617 3107261 := bstep (se 3 (by rfl) ⟨582611, by rfl⟩ : syracuseStep 3107261 = 1165223) B1165223
theorem B3631823 : Blo 1072617 3631823 := bstep (se 1 (by rfl) ⟨2723867, by rfl⟩ : syracuseStep 3631823 = 5447735) B5447735
theorem B1075967 : Blo 1072617 1075967 := bstep (se 1 (by rfl) ⟨806975, by rfl⟩ : syracuseStep 1075967 = 1613951) B1613951
theorem B2419577 : Blo 1072617 2419577 := bstep (se 2 (by rfl) ⟨907341, by rfl⟩ : syracuseStep 2419577 = 1814683) B1814683
theorem B1076255 : Blo 1072617 1076255 := bstep (se 1 (by rfl) ⟨807191, by rfl⟩ : syracuseStep 1076255 = 1614383) B1614383
theorem B1207579 : Blo 1072617 1207579 := bstep (se 1 (by rfl) ⟨905684, by rfl⟩ : syracuseStep 1207579 = 1811369) B1811369
theorem B6876647 : Blo 1072617 6876647 := bstep (se 1 (by rfl) ⟨5157485, by rfl⟩ : syracuseStep 6876647 = 10314971) B10314971
theorem B3632795 : Blo 1072617 3632795 := bstep (se 1 (by rfl) ⟨2724596, by rfl⟩ : syracuseStep 3632795 = 5449193) B5449193
theorem B15494827 : Blo 1072617 15494827 := bstep (se 1 (by rfl) ⟨11621120, by rfl⟩ : syracuseStep 15494827 = 23242241) B23242241
theorem B23260931 : Blo 1072617 23260931 := bstep (se 1 (by rfl) ⟨17445698, by rfl⟩ : syracuseStep 23260931 = 34891397) B34891397
theorem B2715515 : Blo 1072617 2715515 := bstep (se 1 (by rfl) ⟨2036636, by rfl⟩ : syracuseStep 2715515 = 4073273) B4073273
theorem B5436071 : Blo 1072617 5436071 := bstep (se 1 (by rfl) ⟨4077053, by rfl⟩ : syracuseStep 5436071 = 8154107) B8154107
theorem B31814495 : Blo 1072617 31814495 := bstep (se 1 (by rfl) ⟨23860871, by rfl⟩ : syracuseStep 31814495 = 47721743) B47721743
theorem B6124511 : Blo 1072617 6124511 := bstep (se 1 (by rfl) ⟨4593383, by rfl⟩ : syracuseStep 6124511 = 9186767) B9186767
theorem B2716649 : Blo 1072617 2716649 := bstep (se 2 (by rfl) ⟨1018743, by rfl⟩ : syracuseStep 2716649 = 2037487) B2037487
theorem B3437759 : Blo 1072617 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B3438055 : Blo 1072617 3438055 := bstep (se 1 (by rfl) ⟨2578541, by rfl⟩ : syracuseStep 3438055 = 5157083) B5157083
theorem B127497829 : Blo 1072617 127497829 := bstep (se 4 (by rfl) ⟨11952921, by rfl⟩ : syracuseStep 127497829 = 23905843) B23905843
theorem B16512983 : Blo 1072617 16512983 := bstep (se 1 (by rfl) ⟨12384737, by rfl⟩ : syracuseStep 16512983 = 24769475) B24769475
theorem B55769593 : Blo 1072617 55769593 := bstep (se 2 (by rfl) ⟨20913597, by rfl⟩ : syracuseStep 55769593 = 41827195) B41827195
theorem B4653353 : Blo 1072617 4653353 := bstep (se 2 (by rfl) ⟨1745007, by rfl⟩ : syracuseStep 4653353 = 3490015) B3490015
theorem B1933625 : Blo 1072617 1933625 := bstep (se 2 (by rfl) ⟨725109, by rfl⟩ : syracuseStep 1933625 = 1450219) B1450219
theorem B27886355 : Blo 1072617 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B11633543 : Blo 1072617 11633543 := bstep (se 1 (by rfl) ⟨8725157, by rfl⟩ : syracuseStep 11633543 = 17450315) B17450315
theorem B5440445 : Blo 1072617 5440445 := bstep (se 3 (by rfl) ⟨1020083, by rfl⟩ : syracuseStep 5440445 = 2040167) B2040167
theorem B9176105 : Blo 1072617 9176105 := bstep (se 2 (by rfl) ⟨3441039, by rfl⟩ : syracuseStep 9176105 = 6882079) B6882079
theorem B8160425 : Blo 1072617 8160425 := bstep (se 2 (by rfl) ⟨3060159, by rfl⟩ : syracuseStep 8160425 = 6120319) B6120319
theorem B46401443 : Blo 1072617 46401443 := bstep (se 1 (by rfl) ⟨34801082, by rfl⟩ : syracuseStep 46401443 = 69602165) B69602165
theorem B3443219 : Blo 1072617 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B3822750611 : Blo 1072617 3822750611 := bstep (se 1 (by rfl) ⟨2867062958, by rfl⟩ : syracuseStep 3822750611 = 5734125917) B5734125917
theorem B7343759 : Blo 1072617 7343759 := bstep (se 1 (by rfl) ⟨5507819, by rfl⟩ : syracuseStep 7343759 = 11015639) B11015639
theorem B40275883 : Blo 1072617 40275883 := bstep (se 1 (by rfl) ⟨30206912, by rfl⟩ : syracuseStep 40275883 = 60413825) B60413825
theorem B5443523 : Blo 1072617 5443523 := bstep (se 1 (by rfl) ⟨4082642, by rfl⟩ : syracuseStep 5443523 = 8165285) B8165285
theorem B5803987 : Blo 1072617 5803987 := bstep (se 1 (by rfl) ⟨4352990, by rfl⟩ : syracuseStep 5803987 = 8705981) B8705981
theorem B1610105 : Blo 1072617 1610105 := bstep (se 2 (by rfl) ⟨603789, by rfl⟩ : syracuseStep 1610105 = 1207579) B1207579
theorem B1610447 : Blo 1072617 1610447 := bstep (se 1 (by rfl) ⟨1207835, by rfl⟩ : syracuseStep 1610447 = 2415671) B2415671
theorem B1611455 : Blo 1072617 1611455 := bstep (se 1 (by rfl) ⟨1208591, by rfl⟩ : syracuseStep 1611455 = 2417183) B2417183
theorem B5445467 : Blo 1072617 5445467 := bstep (se 1 (by rfl) ⟨4084100, by rfl⟩ : syracuseStep 5445467 = 8168201) B8168201
theorem B1611647 : Blo 1072617 1611647 := bstep (se 1 (by rfl) ⟨1208735, by rfl⟩ : syracuseStep 1611647 = 2417471) B2417471
theorem B5445791 : Blo 1072617 5445791 := bstep (se 1 (by rfl) ⟨4084343, by rfl⟩ : syracuseStep 5445791 = 8168687) B8168687
theorem B2037935 : Blo 1072617 2037935 := bstep (se 1 (by rfl) ⟨1528451, by rfl⟩ : syracuseStep 2037935 = 3056903) B3056903
theorem B1612271 : Blo 1072617 1612271 := bstep (se 1 (by rfl) ⟨1209203, by rfl⟩ : syracuseStep 1612271 = 2418407) B2418407
theorem B1612583 : Blo 1072617 1612583 := bstep (se 1 (by rfl) ⟨1209437, by rfl⟩ : syracuseStep 1612583 = 2418875) B2418875
theorem B2071507 : Blo 1072617 2071507 := bstep (se 1 (by rfl) ⟨1553630, by rfl⟩ : syracuseStep 2071507 = 3107261) B3107261
theorem B1613051 : Blo 1072617 1613051 := bstep (se 1 (by rfl) ⟨1209788, by rfl⟩ : syracuseStep 1613051 = 2419577) B2419577
theorem B2039195 : Blo 1072617 2039195 := bstep (se 1 (by rfl) ⟨1529396, by rfl⟩ : syracuseStep 2039195 = 3058793) B3058793
theorem B15507287 : Blo 1072617 15507287 := bstep (se 1 (by rfl) ⟨11630465, by rfl⟩ : syracuseStep 15507287 = 23260931) B23260931
theorem B1810343 : Blo 1072617 1810343 := bstep (se 1 (by rfl) ⟨1357757, by rfl⟩ : syracuseStep 1810343 = 2715515) B2715515
theorem B3776765 : Blo 1072617 3776765 := bstep (se 3 (by rfl) ⟨708143, by rfl⟩ : syracuseStep 3776765 = 1416287) B1416287
theorem B21209663 : Blo 1072617 21209663 := bstep (se 1 (by rfl) ⟨15907247, by rfl⟩ : syracuseStep 21209663 = 31814495) B31814495
theorem B1811099 : Blo 1072617 1811099 := bstep (se 1 (by rfl) ⟨1358324, by rfl⟩ : syracuseStep 1811099 = 2716649) B2716649
theorem B74359457 : Blo 1072617 74359457 := bstep (se 2 (by rfl) ⟨27884796, by rfl⟩ : syracuseStep 74359457 = 55769593) B55769593
theorem B10462729 : Blo 1072617 10462729 := bstep (se 2 (by rfl) ⟨3923523, by rfl⟩ : syracuseStep 10462729 = 7847047) B7847047
theorem B7547255 : Blo 1072617 7547255 := bstep (se 1 (by rfl) ⟨5660441, by rfl⟩ : syracuseStep 7547255 = 11320883) B11320883
theorem B18362051 : Blo 1072617 18362051 := bstep (se 1 (by rfl) ⟨13771538, by rfl⟩ : syracuseStep 18362051 = 27543077) B27543077
theorem B9449243 : Blo 1072617 9449243 := bstep (se 1 (by rfl) ⟨7086932, by rfl⟩ : syracuseStep 9449243 = 14173865) B14173865
theorem B23277881 : Blo 1072617 23277881 := bstep (se 2 (by rfl) ⟨8729205, by rfl⟩ : syracuseStep 23277881 = 17458411) B17458411
theorem B1290655 : Blo 1072617 1290655 := bstep (se 1 (by rfl) ⟨967991, by rfl⟩ : syracuseStep 1290655 = 1935983) B1935983
theorem B17412997 : Blo 1072617 17412997 := bstep (se 4 (by rfl) ⟨1632468, by rfl⟩ : syracuseStep 17412997 = 3264937) B3264937
theorem B1292447 : Blo 1072617 1292447 := bstep (se 1 (by rfl) ⟨969335, by rfl⟩ : syracuseStep 1292447 = 1938671) B1938671
theorem B32225489 : Blo 1072617 32225489 := bstep (se 2 (by rfl) ⟨12084558, by rfl⟩ : syracuseStep 32225489 = 24169117) B24169117
theorem B3062119 : Blo 1072617 3062119 := bstep (se 1 (by rfl) ⟨2296589, by rfl⟩ : syracuseStep 3062119 = 4593179) B4593179
theorem B20659769 : Blo 1072617 20659769 := bstep (se 2 (by rfl) ⟨7747413, by rfl⟩ : syracuseStep 20659769 = 15494827) B15494827
theorem B2900167 : Blo 1072617 2900167 := bstep (se 1 (by rfl) ⟨2175125, by rfl⟩ : syracuseStep 2900167 = 4350251) B4350251
theorem B1164703 : Blo 1072617 1164703 := bstep (se 1 (by rfl) ⟨873527, by rfl⟩ : syracuseStep 1164703 = 1747055) B1747055
theorem B3624047 : Blo 1072617 3624047 := bstep (se 1 (by rfl) ⟨2718035, by rfl⟩ : syracuseStep 3624047 = 5436071) B5436071
theorem B4083007 : Blo 1072617 4083007 := bstep (se 1 (by rfl) ⟨3062255, by rfl⟩ : syracuseStep 4083007 = 6124511) B6124511
theorem B7361437 : Blo 1072617 7361437 := bstep (se 3 (by rfl) ⟨1380269, by rfl⟩ : syracuseStep 7361437 = 2760539) B2760539
theorem B2413511 : Blo 1072617 2413511 := bstep (se 1 (by rfl) ⟨1810133, by rfl⟩ : syracuseStep 2413511 = 3620267) B3620267
theorem B2413799 : Blo 1072617 2413799 := bstep (se 1 (by rfl) ⟨1810349, by rfl⟩ : syracuseStep 2413799 = 3620699) B3620699
theorem B9197225 : Blo 1072617 9197225 := bstep (se 2 (by rfl) ⟨3448959, by rfl⟩ : syracuseStep 9197225 = 6897919) B6897919
theorem B2416175 : Blo 1072617 2416175 := bstep (se 1 (by rfl) ⟨1812131, by rfl⟩ : syracuseStep 2416175 = 3624263) B3624263
theorem B1072743 : Blo 1072617 1072743 := bstep (se 1 (by rfl) ⟨804557, by rfl⟩ : syracuseStep 1072743 = 1609115) B1609115
theorem B5431211 : Blo 1072617 5431211 := bstep (se 1 (by rfl) ⟨4073408, by rfl⟩ : syracuseStep 5431211 = 8146817) B8146817
theorem B1073183 : Blo 1072617 1073183 := bstep (se 1 (by rfl) ⟨804887, by rfl⟩ : syracuseStep 1073183 = 1609775) B1609775
theorem B1073199 : Blo 1072617 1073199 := bstep (se 1 (by rfl) ⟨804899, by rfl⟩ : syracuseStep 1073199 = 1609799) B1609799
theorem B12247199 : Blo 1072617 12247199 := bstep (se 1 (by rfl) ⟨9185399, by rfl⟩ : syracuseStep 12247199 = 18370799) B18370799
theorem B9167357 : Blo 1072617 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B19882493 : Blo 1072617 19882493 := bstep (se 3 (by rfl) ⟨3727967, by rfl⟩ : syracuseStep 19882493 = 7455935) B7455935
theorem B1073915 : Blo 1072617 1073915 := bstep (se 1 (by rfl) ⟨805436, by rfl⟩ : syracuseStep 1073915 = 1610873) B1610873
theorem B2417435 : Blo 1072617 2417435 := bstep (se 1 (by rfl) ⟨1813076, by rfl⟩ : syracuseStep 2417435 = 3626153) B3626153
theorem B2417615 : Blo 1072617 2417615 := bstep (se 1 (by rfl) ⟨1813211, by rfl⟩ : syracuseStep 2417615 = 3626423) B3626423
theorem B2417633 : Blo 1072617 2417633 := bstep (se 2 (by rfl) ⟨906612, by rfl⟩ : syracuseStep 2417633 = 1813225) B1813225
theorem B2417705 : Blo 1072617 2417705 := bstep (se 2 (by rfl) ⟨906639, by rfl⟩ : syracuseStep 2417705 = 1813279) B1813279
theorem B2418011 : Blo 1072617 2418011 := bstep (se 1 (by rfl) ⟨1813508, by rfl⟩ : syracuseStep 2418011 = 3627017) B3627017
theorem B1074559 : Blo 1072617 1074559 := bstep (se 1 (by rfl) ⟨805919, by rfl⟩ : syracuseStep 1074559 = 1611839) B1611839
theorem B12248657 : Blo 1072617 12248657 := bstep (se 2 (by rfl) ⟨4593246, by rfl⟩ : syracuseStep 12248657 = 9186493) B9186493
theorem B1074779 : Blo 1072617 1074779 := bstep (se 1 (by rfl) ⟨806084, by rfl⟩ : syracuseStep 1074779 = 1612169) B1612169
theorem B22079405 : Blo 1072617 22079405 := bstep (se 3 (by rfl) ⟨4139888, by rfl⟩ : syracuseStep 22079405 = 8279777) B8279777
theorem B1075407 : Blo 1072617 1075407 := bstep (se 1 (by rfl) ⟨806555, by rfl⟩ : syracuseStep 1075407 = 1613111) B1613111
theorem B1075455 : Blo 1072617 1075455 := bstep (se 1 (by rfl) ⟨806591, by rfl⟩ : syracuseStep 1075455 = 1613183) B1613183
theorem B1075527 : Blo 1072617 1075527 := bstep (se 1 (by rfl) ⟨806645, by rfl⟩ : syracuseStep 1075527 = 1613291) B1613291
theorem B1075559 : Blo 1072617 1075559 := bstep (se 1 (by rfl) ⟨806669, by rfl⟩ : syracuseStep 1075559 = 1613339) B1613339
theorem B9169271 : Blo 1072617 9169271 := bstep (se 1 (by rfl) ⟨6876953, by rfl⟩ : syracuseStep 9169271 = 13753907) B13753907
theorem B4581971 : Blo 1072617 4581971 := bstep (se 1 (by rfl) ⟨3436478, by rfl⟩ : syracuseStep 4581971 = 6872957) B6872957
theorem B1075803 : Blo 1072617 1075803 := bstep (se 1 (by rfl) ⟨806852, by rfl⟩ : syracuseStep 1075803 = 1613705) B1613705
theorem B1207003 : Blo 1072617 1207003 := bstep (se 1 (by rfl) ⟨905252, by rfl⟩ : syracuseStep 1207003 = 1810505) B1810505
theorem B2419433 : Blo 1072617 2419433 := bstep (se 2 (by rfl) ⟨907287, by rfl⟩ : syracuseStep 2419433 = 1814575) B1814575
theorem B1207111 : Blo 1072617 1207111 := bstep (se 1 (by rfl) ⟨905333, by rfl⟩ : syracuseStep 1207111 = 1810667) B1810667
theorem B1076159 : Blo 1072617 1076159 := bstep (se 1 (by rfl) ⟨807119, by rfl⟩ : syracuseStep 1076159 = 1614239) B1614239
theorem B2419739 : Blo 1072617 2419739 := bstep (se 1 (by rfl) ⟨1814804, by rfl⟩ : syracuseStep 2419739 = 3629609) B3629609
theorem B5434451 : Blo 1072617 5434451 := bstep (se 1 (by rfl) ⟨4075838, by rfl⟩ : syracuseStep 5434451 = 8151677) B8151677
theorem B1076379 : Blo 1072617 1076379 := bstep (se 1 (by rfl) ⟨807284, by rfl⟩ : syracuseStep 1076379 = 1614569) B1614569
theorem B1076391 : Blo 1072617 1076391 := bstep (se 1 (by rfl) ⟨807293, by rfl⟩ : syracuseStep 1076391 = 1614587) B1614587
theorem B3632687 : Blo 1072617 3632687 := bstep (se 1 (by rfl) ⟨2724515, by rfl⟩ : syracuseStep 3632687 = 5449031) B5449031
theorem B2715191 : Blo 1072617 2715191 := bstep (se 1 (by rfl) ⟨2036393, by rfl⟩ : syracuseStep 2715191 = 4072787) B4072787
theorem B1207975 : Blo 1072617 1207975 := bstep (se 1 (by rfl) ⟨905981, by rfl⟩ : syracuseStep 1207975 = 1811963) B1811963
theorem B30994163 : Blo 1072617 30994163 := bstep (se 1 (by rfl) ⟨23245622, by rfl⟩ : syracuseStep 30994163 = 46491245) B46491245
theorem B2420639 : Blo 1072617 2420639 := bstep (se 1 (by rfl) ⟨1815479, by rfl⟩ : syracuseStep 2420639 = 3630959) B3630959
theorem B9170981 : Blo 1072617 9170981 := bstep (se 4 (by rfl) ⟨859779, by rfl⟩ : syracuseStep 9170981 = 1719559) B1719559
theorem B2421215 : Blo 1072617 2421215 := bstep (se 1 (by rfl) ⟨1815911, by rfl⟩ : syracuseStep 2421215 = 3631823) B3631823
theorem B4354667 : Blo 1072617 4354667 := bstep (se 1 (by rfl) ⟨3266000, by rfl⟩ : syracuseStep 4354667 = 6532001) B6532001
theorem B4584073 : Blo 1072617 4584073 := bstep (se 2 (by rfl) ⟨1719027, by rfl⟩ : syracuseStep 4584073 = 3438055) B3438055
theorem B169997105 : Blo 1072617 169997105 := bstep (se 2 (by rfl) ⟨63748914, by rfl⟩ : syracuseStep 169997105 = 127497829) B127497829
theorem B4584431 : Blo 1072617 4584431 := bstep (se 1 (by rfl) ⟨3438323, by rfl⟩ : syracuseStep 4584431 = 6876647) B6876647
theorem B2421863 : Blo 1072617 2421863 := bstep (se 1 (by rfl) ⟨1816397, by rfl⟩ : syracuseStep 2421863 = 3632795) B3632795
theorem B12219497 : Blo 1072617 12219497 := bstep (se 2 (by rfl) ⟨4582311, by rfl⟩ : syracuseStep 12219497 = 9164623) B9164623
theorem B1209703 : Blo 1072617 1209703 := bstep (se 1 (by rfl) ⟨907277, by rfl⟩ : syracuseStep 1209703 = 1814555) B1814555
theorem B20903305 : Blo 1072617 20903305 := bstep (se 2 (by rfl) ⟨7838739, by rfl⟩ : syracuseStep 20903305 = 15677479) B15677479
theorem B2717833 : Blo 1072617 2717833 := bstep (se 2 (by rfl) ⟨1019187, by rfl⟩ : syracuseStep 2717833 = 2038375) B2038375
theorem B10320317 : Blo 1072617 10320317 := bstep (se 3 (by rfl) ⟨1935059, by rfl⟩ : syracuseStep 10320317 = 3870119) B3870119
theorem B11008655 : Blo 1072617 11008655 := bstep (se 1 (by rfl) ⟨8256491, by rfl⟩ : syracuseStep 11008655 = 16512983) B16512983
theorem B3439529 : Blo 1072617 3439529 := bstep (se 2 (by rfl) ⟨1289823, by rfl⟩ : syracuseStep 3439529 = 2579647) B2579647
theorem B10321121 : Blo 1072617 10321121 := bstep (se 2 (by rfl) ⟨3870420, by rfl⟩ : syracuseStep 10321121 = 7740841) B7740841
theorem B453443345 : Blo 1072617 453443345 := bstep (se 2 (by rfl) ⟨170041254, by rfl⟩ : syracuseStep 453443345 = 340082509) B340082509
theorem B5440283 : Blo 1072617 5440283 := bstep (se 1 (by rfl) ⟨4080212, by rfl⟩ : syracuseStep 5440283 = 8160425) B8160425
theorem B15467557 : Blo 1072617 15467557 := bstep (se 4 (by rfl) ⟨1450083, by rfl⟩ : syracuseStep 15467557 = 2900167) B2900167
theorem B30934295 : Blo 1072617 30934295 := bstep (se 1 (by rfl) ⟨23200721, by rfl⟩ : syracuseStep 30934295 = 46401443) B46401443
theorem B2295479 : Blo 1072617 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B2548500407 : Blo 1072617 2548500407 := bstep (se 1 (by rfl) ⟨1911375305, by rfl⟩ : syracuseStep 2548500407 = 3822750611) B3822750611
theorem B1609007 : Blo 1072617 1609007 := bstep (se 1 (by rfl) ⟨1206755, by rfl⟩ : syracuseStep 1609007 = 2413511) B2413511
theorem B1609199 : Blo 1072617 1609199 := bstep (se 1 (by rfl) ⟨1206899, by rfl⟩ : syracuseStep 1609199 = 2413799) B2413799
theorem B1609337 : Blo 1072617 1609337 := bstep (se 2 (by rfl) ⟨603501, by rfl⟩ : syracuseStep 1609337 = 1207003) B1207003
theorem B1609481 : Blo 1072617 1609481 := bstep (se 2 (by rfl) ⟨603555, by rfl⟩ : syracuseStep 1609481 = 1207111) B1207111
theorem B6131483 : Blo 1072617 6131483 := bstep (se 1 (by rfl) ⟨4598612, by rfl⟩ : syracuseStep 6131483 = 9197225) B9197225
theorem B5444009 : Blo 1072617 5444009 := bstep (se 2 (by rfl) ⟨2041503, by rfl⟩ : syracuseStep 5444009 = 4083007) B4083007
theorem B1610633 : Blo 1072617 1610633 := bstep (se 2 (by rfl) ⟨603987, by rfl⟩ : syracuseStep 1610633 = 1207975) B1207975
theorem B1610783 : Blo 1072617 1610783 := bstep (se 1 (by rfl) ⟨1208087, by rfl⟩ : syracuseStep 1610783 = 2416175) B2416175
theorem B7738649 : Blo 1072617 7738649 := bstep (se 2 (by rfl) ⟨2901993, by rfl⟩ : syracuseStep 7738649 = 5803987) B5803987
theorem B8164799 : Blo 1072617 8164799 := bstep (se 1 (by rfl) ⟨6123599, by rfl⟩ : syracuseStep 8164799 = 12247199) B12247199
theorem B3446525 : Blo 1072617 3446525 := bstep (se 3 (by rfl) ⟨646223, by rfl⟩ : syracuseStep 3446525 = 1292447) B1292447
theorem B1611623 : Blo 1072617 1611623 := bstep (se 1 (by rfl) ⟨1208717, by rfl⟩ : syracuseStep 1611623 = 2417435) B2417435
theorem B1611743 : Blo 1072617 1611743 := bstep (se 1 (by rfl) ⟨1208807, by rfl⟩ : syracuseStep 1611743 = 2417615) B2417615
theorem B1611755 : Blo 1072617 1611755 := bstep (se 1 (by rfl) ⟨1208816, by rfl⟩ : syracuseStep 1611755 = 2417633) B2417633
theorem B1611803 : Blo 1072617 1611803 := bstep (se 1 (by rfl) ⟨1208852, by rfl⟩ : syracuseStep 1611803 = 2417705) B2417705
theorem B1612007 : Blo 1072617 1612007 := bstep (se 1 (by rfl) ⟨1209005, by rfl⟩ : syracuseStep 1612007 = 2418011) B2418011
theorem B8165771 : Blo 1072617 8165771 := bstep (se 1 (by rfl) ⟨6124328, by rfl⟩ : syracuseStep 8165771 = 12248657) B12248657
theorem B14719603 : Blo 1072617 14719603 := bstep (se 1 (by rfl) ⟨11039702, by rfl⟩ : syracuseStep 14719603 = 22079405) B22079405
theorem B3054647 : Blo 1072617 3054647 := bstep (se 1 (by rfl) ⟨2290985, by rfl⟩ : syracuseStep 3054647 = 4581971) B4581971
theorem B1612937 : Blo 1072617 1612937 := bstep (se 2 (by rfl) ⟨604851, by rfl⟩ : syracuseStep 1612937 = 1209703) B1209703
theorem B1612955 : Blo 1072617 1612955 := bstep (se 1 (by rfl) ⟨1209716, by rfl⟩ : syracuseStep 1612955 = 2419433) B2419433
theorem B1613159 : Blo 1072617 1613159 := bstep (se 1 (by rfl) ⟨1209869, by rfl⟩ : syracuseStep 1613159 = 2419739) B2419739
theorem B1810127 : Blo 1072617 1810127 := bstep (se 1 (by rfl) ⟨1357595, by rfl⟩ : syracuseStep 1810127 = 2715191) B2715191
theorem B6299495 : Blo 1072617 6299495 := bstep (se 1 (by rfl) ⟨4724621, by rfl⟩ : syracuseStep 6299495 = 9449243) B9449243
theorem B1613759 : Blo 1072617 1613759 := bstep (se 1 (by rfl) ⟨1210319, by rfl⟩ : syracuseStep 1613759 = 2420639) B2420639
theorem B1614143 : Blo 1072617 1614143 := bstep (se 1 (by rfl) ⟨1210607, by rfl⟩ : syracuseStep 1614143 = 2421215) B2421215
theorem B3056287 : Blo 1072617 3056287 := bstep (se 1 (by rfl) ⟨2292215, by rfl⟩ : syracuseStep 3056287 = 4584431) B4584431
theorem B1614575 : Blo 1072617 1614575 := bstep (se 1 (by rfl) ⟨1210931, by rfl⟩ : syracuseStep 1614575 = 2421863) B2421863
theorem B2762009 : Blo 1072617 2762009 := bstep (se 2 (by rfl) ⟨1035753, by rfl⟩ : syracuseStep 2762009 = 2071507) B2071507
theorem B13773179 : Blo 1072617 13773179 := bstep (se 1 (by rfl) ⟨10329884, by rfl⟩ : syracuseStep 13773179 = 20659769) B20659769
theorem B302295563 : Blo 1072617 302295563 := bstep (se 1 (by rfl) ⟨226721672, by rfl⟩ : syracuseStep 302295563 = 453443345) B453443345
theorem B1289083 : Blo 1072617 1289083 := bstep (se 1 (by rfl) ⟨966812, by rfl⟩ : syracuseStep 1289083 = 1933625) B1933625
theorem B18590903 : Blo 1072617 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B10071373 : Blo 1072617 10071373 := bstep (se 3 (by rfl) ⟨1888382, by rfl⟩ : syracuseStep 10071373 = 3776765) B3776765
theorem B1552937 : Blo 1072617 1552937 := bstep (se 2 (by rfl) ⟨582351, by rfl⟩ : syracuseStep 1552937 = 1164703) B1164703
theorem B4895839 : Blo 1072617 4895839 := bstep (se 1 (by rfl) ⟨3671879, by rfl⟩ : syracuseStep 4895839 = 7343759) B7343759
theorem B1358623 : Blo 1072617 1358623 := bstep (se 1 (by rfl) ⟨1018967, by rfl⟩ : syracuseStep 1358623 = 2037935) B2037935
theorem B10338191 : Blo 1072617 10338191 := bstep (se 1 (by rfl) ⟨7753643, by rfl⟩ : syracuseStep 10338191 = 15507287) B15507287
theorem B3620807 : Blo 1072617 3620807 := bstep (se 1 (by rfl) ⟨2715605, by rfl⟩ : syracuseStep 3620807 = 5431211) B5431211
theorem B6111571 : Blo 1072617 6111571 := bstep (se 1 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 6111571 = 9167357) B9167357
theorem B13254995 : Blo 1072617 13254995 := bstep (se 1 (by rfl) ⟨9941246, by rfl⟩ : syracuseStep 13254995 = 19882493) B19882493
theorem B14139775 : Blo 1072617 14139775 := bstep (se 1 (by rfl) ⟨10604831, by rfl⟩ : syracuseStep 14139775 = 21209663) B21209663
theorem B1720873 : Blo 1072617 1720873 := bstep (se 2 (by rfl) ⟨645327, by rfl⟩ : syracuseStep 1720873 = 1290655) B1290655
theorem B6112097 : Blo 1072617 6112097 := bstep (se 2 (by rfl) ⟨2292036, by rfl⟩ : syracuseStep 6112097 = 4584073) B4584073
theorem B23217329 : Blo 1072617 23217329 := bstep (se 2 (by rfl) ⟨8706498, by rfl⟩ : syracuseStep 23217329 = 17412997) B17412997
theorem B9815249 : Blo 1072617 9815249 := bstep (se 2 (by rfl) ⟨3680718, by rfl⟩ : syracuseStep 9815249 = 7361437) B7361437
theorem B6112847 : Blo 1072617 6112847 := bstep (se 1 (by rfl) ⟨4584635, by rfl⟩ : syracuseStep 6112847 = 9169271) B9169271
theorem B5031503 : Blo 1072617 5031503 := bstep (se 1 (by rfl) ⟨3773627, by rfl⟩ : syracuseStep 5031503 = 7547255) B7547255
theorem B27871073 : Blo 1072617 27871073 := bstep (se 2 (by rfl) ⟨10451652, by rfl⟩ : syracuseStep 27871073 = 20903305) B20903305
theorem B3622967 : Blo 1072617 3622967 := bstep (se 1 (by rfl) ⟨2717225, by rfl⟩ : syracuseStep 3622967 = 5434451) B5434451
theorem B12241367 : Blo 1072617 12241367 := bstep (se 1 (by rfl) ⟨9181025, by rfl⟩ : syracuseStep 12241367 = 18362051) B18362051
theorem B20662775 : Blo 1072617 20662775 := bstep (se 1 (by rfl) ⟨15497081, by rfl⟩ : syracuseStep 20662775 = 30994163) B30994163
theorem B6113987 : Blo 1072617 6113987 := bstep (se 1 (by rfl) ⟨4585490, by rfl⟩ : syracuseStep 6113987 = 9170981) B9170981
theorem B3623777 : Blo 1072617 3623777 := bstep (se 2 (by rfl) ⟨1358916, by rfl⟩ : syracuseStep 3623777 = 2717833) B2717833
theorem B15518587 : Blo 1072617 15518587 := bstep (se 1 (by rfl) ⟨11638940, by rfl⟩ : syracuseStep 15518587 = 23277881) B23277881
theorem B2903111 : Blo 1072617 2903111 := bstep (se 1 (by rfl) ⟨2177333, by rfl⟩ : syracuseStep 2903111 = 4354667) B4354667
theorem B4082825 : Blo 1072617 4082825 := bstep (se 2 (by rfl) ⟨1531059, by rfl⟩ : syracuseStep 4082825 = 3062119) B3062119
theorem B113331403 : Blo 1072617 113331403 := bstep (se 1 (by rfl) ⟨84998552, by rfl⟩ : syracuseStep 113331403 = 169997105) B169997105
theorem B8146331 : Blo 1072617 8146331 := bstep (se 1 (by rfl) ⟨6109748, by rfl⟩ : syracuseStep 8146331 = 12219497) B12219497
theorem B21483659 : Blo 1072617 21483659 := bstep (se 1 (by rfl) ⟨16112744, by rfl⟩ : syracuseStep 21483659 = 32225489) B32225489
theorem B3102235 : Blo 1072617 3102235 := bstep (se 1 (by rfl) ⟨2326676, by rfl⟩ : syracuseStep 3102235 = 4653353) B4653353
theorem B7755695 : Blo 1072617 7755695 := bstep (se 1 (by rfl) ⟨5816771, by rfl⟩ : syracuseStep 7755695 = 11633543) B11633543
theorem B3626963 : Blo 1072617 3626963 := bstep (se 1 (by rfl) ⟨2720222, by rfl⟩ : syracuseStep 3626963 = 5440445) B5440445
theorem B6117403 : Blo 1072617 6117403 := bstep (se 1 (by rfl) ⟨4588052, by rfl⟩ : syracuseStep 6117403 = 9176105) B9176105
theorem B13950305 : Blo 1072617 13950305 := bstep (se 2 (by rfl) ⟨5231364, by rfl⟩ : syracuseStep 13950305 = 10462729) B10462729
theorem B2416031 : Blo 1072617 2416031 := bstep (se 1 (by rfl) ⟨1812023, by rfl⟩ : syracuseStep 2416031 = 3624047) B3624047
theorem B3629015 : Blo 1072617 3629015 := bstep (se 1 (by rfl) ⟨2721761, by rfl⟩ : syracuseStep 3629015 = 5443523) B5443523
theorem B1073403 : Blo 1072617 1073403 := bstep (se 1 (by rfl) ⟨805052, by rfl⟩ : syracuseStep 1073403 = 1610105) B1610105
theorem B1073631 : Blo 1072617 1073631 := bstep (se 1 (by rfl) ⟨805223, by rfl⟩ : syracuseStep 1073631 = 1610447) B1610447
theorem B1074303 : Blo 1072617 1074303 := bstep (se 1 (by rfl) ⟨805727, by rfl⟩ : syracuseStep 1074303 = 1611455) B1611455
theorem B3630311 : Blo 1072617 3630311 := bstep (se 1 (by rfl) ⟨2722733, by rfl⟩ : syracuseStep 3630311 = 5445467) B5445467
theorem B1074431 : Blo 1072617 1074431 := bstep (se 1 (by rfl) ⟨805823, by rfl⟩ : syracuseStep 1074431 = 1611647) B1611647
theorem B3630527 : Blo 1072617 3630527 := bstep (se 1 (by rfl) ⟨2722895, by rfl⟩ : syracuseStep 3630527 = 5445791) B5445791
theorem B1074847 : Blo 1072617 1074847 := bstep (se 1 (by rfl) ⟨806135, by rfl⟩ : syracuseStep 1074847 = 1612271) B1612271
theorem B1075055 : Blo 1072617 1075055 := bstep (se 1 (by rfl) ⟨806291, by rfl⟩ : syracuseStep 1075055 = 1612583) B1612583
theorem B1075367 : Blo 1072617 1075367 := bstep (se 1 (by rfl) ⟨806525, by rfl⟩ : syracuseStep 1075367 = 1613051) B1613051
theorem B53701177 : Blo 1072617 53701177 := bstep (se 2 (by rfl) ⟨20137941, by rfl⟩ : syracuseStep 53701177 = 40275883) B40275883
theorem B1206895 : Blo 1072617 1206895 := bstep (se 1 (by rfl) ⟨905171, by rfl⟩ : syracuseStep 1206895 = 1810343) B1810343
theorem B1207399 : Blo 1072617 1207399 := bstep (se 1 (by rfl) ⟨905549, by rfl⟩ : syracuseStep 1207399 = 1811099) B1811099
theorem B49572971 : Blo 1072617 49572971 := bstep (se 1 (by rfl) ⟨37179728, by rfl⟩ : syracuseStep 49572971 = 74359457) B74359457
theorem B2421791 : Blo 1072617 2421791 := bstep (se 1 (by rfl) ⟨1816343, by rfl⟩ : syracuseStep 2421791 = 3632687) B3632687
theorem B5437853 : Blo 1072617 5437853 := bstep (se 3 (by rfl) ⟨1019597, by rfl⟩ : syracuseStep 5437853 = 2039195) B2039195
theorem B6880211 : Blo 1072617 6880211 := bstep (se 1 (by rfl) ⟨5160158, by rfl⟩ : syracuseStep 6880211 = 10320317) B10320317
theorem B7339103 : Blo 1072617 7339103 := bstep (se 1 (by rfl) ⟨5504327, by rfl⟩ : syracuseStep 7339103 = 11008655) B11008655
theorem B2293019 : Blo 1072617 2293019 := bstep (se 1 (by rfl) ⟨1719764, by rfl⟩ : syracuseStep 2293019 = 3439529) B3439529
theorem B6880747 : Blo 1072617 6880747 := bstep (se 1 (by rfl) ⟨5160560, by rfl⟩ : syracuseStep 6880747 = 10321121) B10321121
theorem B2294497 : Blo 1072617 2294497 := bstep (se 2 (by rfl) ⟨860436, by rfl⟩ : syracuseStep 2294497 = 1720873) B1720873
theorem B18580715 : Blo 1072617 18580715 := bstep (se 1 (by rfl) ⟨13935536, by rfl⟩ : syracuseStep 18580715 = 27871073) B27871073
theorem B8160911 : Blo 1072617 8160911 := bstep (se 1 (by rfl) ⟨6120683, by rfl⟩ : syracuseStep 8160911 = 12241367) B12241367
theorem B1935407 : Blo 1072617 1935407 := bstep (se 1 (by rfl) ⟨1451555, by rfl⟩ : syracuseStep 1935407 = 2903111) B2903111
theorem B2721883 : Blo 1072617 2721883 := bstep (se 1 (by rfl) ⟨2041412, by rfl⟩ : syracuseStep 2721883 = 4082825) B4082825
theorem B14322439 : Blo 1072617 14322439 := bstep (se 1 (by rfl) ⟨10741829, by rfl⟩ : syracuseStep 14322439 = 21483659) B21483659
theorem B71601569 : Blo 1072617 71601569 := bstep (se 2 (by rfl) ⟨26850588, by rfl⟩ : syracuseStep 71601569 = 53701177) B53701177
theorem B1609193 : Blo 1072617 1609193 := bstep (se 2 (by rfl) ⟨603447, by rfl⟩ : syracuseStep 1609193 = 1206895) B1206895
theorem B5443199 : Blo 1072617 5443199 := bstep (se 1 (by rfl) ⟨4082399, by rfl⟩ : syracuseStep 5443199 = 8164799) B8164799
theorem B2297683 : Blo 1072617 2297683 := bstep (se 1 (by rfl) ⟨1723262, by rfl⟩ : syracuseStep 2297683 = 3446525) B3446525
theorem B1609865 : Blo 1072617 1609865 := bstep (se 2 (by rfl) ⟨603699, by rfl⟩ : syracuseStep 1609865 = 1207399) B1207399
theorem B5443847 : Blo 1072617 5443847 := bstep (se 1 (by rfl) ⟨4082885, by rfl⟩ : syracuseStep 5443847 = 8165771) B8165771
theorem B2036431 : Blo 1072617 2036431 := bstep (se 1 (by rfl) ⟨1527323, by rfl⟩ : syracuseStep 2036431 = 3054647) B3054647
theorem B1610687 : Blo 1072617 1610687 := bstep (se 1 (by rfl) ⟨1208015, by rfl⟩ : syracuseStep 1610687 = 2416031) B2416031
theorem B4199663 : Blo 1072617 4199663 := bstep (se 1 (by rfl) ⟨3149747, by rfl⟩ : syracuseStep 4199663 = 6299495) B6299495
theorem B1841339 : Blo 1072617 1841339 := bstep (se 1 (by rfl) ⟨1381004, by rfl⟩ : syracuseStep 1841339 = 2762009) B2762009
theorem B6527785 : Blo 1072617 6527785 := bstep (se 2 (by rfl) ⟨2447919, by rfl⟩ : syracuseStep 6527785 = 4895839) B4895839
theorem B9182119 : Blo 1072617 9182119 := bstep (se 1 (by rfl) ⟨6886589, by rfl⟩ : syracuseStep 9182119 = 13773179) B13773179
theorem B201530375 : Blo 1072617 201530375 := bstep (se 1 (by rfl) ⟨151147781, by rfl⟩ : syracuseStep 201530375 = 302295563) B302295563
theorem B12393935 : Blo 1072617 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B1614527 : Blo 1072617 1614527 := bstep (se 1 (by rfl) ⟨1210895, by rfl⟩ : syracuseStep 1614527 = 2421791) B2421791
theorem B1811497 : Blo 1072617 1811497 := bstep (se 2 (by rfl) ⟨679311, by rfl⟩ : syracuseStep 1811497 = 1358623) B1358623
theorem B4892735 : Blo 1072617 4892735 := bstep (se 1 (by rfl) ⟨3669551, by rfl⟩ : syracuseStep 4892735 = 7339103) B7339103
theorem B6892127 : Blo 1072617 6892127 := bstep (se 1 (by rfl) ⟨5169095, by rfl⟩ : syracuseStep 6892127 = 10338191) B10338191
theorem B4074731 : Blo 1072617 4074731 := bstep (se 1 (by rfl) ⟨3056048, by rfl⟩ : syracuseStep 4074731 = 6112097) B6112097
theorem B15478219 : Blo 1072617 15478219 := bstep (se 1 (by rfl) ⟨11608664, by rfl⟩ : syracuseStep 15478219 = 23217329) B23217329
theorem B20622863 : Blo 1072617 20622863 := bstep (se 1 (by rfl) ⟨15467147, by rfl⟩ : syracuseStep 20622863 = 30934295) B30934295
theorem B4075049 : Blo 1072617 4075049 := bstep (se 2 (by rfl) ⟨1528143, by rfl⟩ : syracuseStep 4075049 = 3056287) B3056287
theorem B4075231 : Blo 1072617 4075231 := bstep (se 1 (by rfl) ⟨3056423, by rfl⟩ : syracuseStep 4075231 = 6112847) B6112847
theorem B3354335 : Blo 1072617 3354335 := bstep (se 1 (by rfl) ⟨2515751, by rfl⟩ : syracuseStep 3354335 = 5031503) B5031503
theorem B1699000271 : Blo 1072617 1699000271 := bstep (se 1 (by rfl) ⟨1274250203, by rfl⟩ : syracuseStep 1699000271 = 2548500407) B2548500407
theorem B20623409 : Blo 1072617 20623409 := bstep (se 2 (by rfl) ⟨7733778, by rfl⟩ : syracuseStep 20623409 = 15467557) B15467557
theorem B4141165 : Blo 1072617 4141165 := bstep (se 3 (by rfl) ⟨776468, by rfl⟩ : syracuseStep 4141165 = 1552937) B1552937
theorem B13775183 : Blo 1072617 13775183 := bstep (se 1 (by rfl) ⟨10331387, by rfl⟩ : syracuseStep 13775183 = 20662775) B20662775
theorem B4075991 : Blo 1072617 4075991 := bstep (se 1 (by rfl) ⟨3056993, by rfl⟩ : syracuseStep 4075991 = 6113987) B6113987
theorem B75412133 : Blo 1072617 75412133 := bstep (se 4 (by rfl) ⟨7069887, by rfl⟩ : syracuseStep 75412133 = 14139775) B14139775
theorem B5159099 : Blo 1072617 5159099 := bstep (se 1 (by rfl) ⟨3869324, by rfl⟩ : syracuseStep 5159099 = 7738649) B7738649
theorem B1718777 : Blo 1072617 1718777 := bstep (se 2 (by rfl) ⟨644541, by rfl⟩ : syracuseStep 1718777 = 1289083) B1289083
theorem B20691449 : Blo 1072617 20691449 := bstep (se 2 (by rfl) ⟨7759293, by rfl⟩ : syracuseStep 20691449 = 15518587) B15518587
theorem B151108537 : Blo 1072617 151108537 := bstep (se 2 (by rfl) ⟨56665701, by rfl⟩ : syracuseStep 151108537 = 113331403) B113331403
theorem B33048647 : Blo 1072617 33048647 := bstep (se 1 (by rfl) ⟨24786485, by rfl⟩ : syracuseStep 33048647 = 49572971) B49572971
theorem B3625235 : Blo 1072617 3625235 := bstep (se 1 (by rfl) ⟨2718926, by rfl⟩ : syracuseStep 3625235 = 5437853) B5437853
theorem B1528679 : Blo 1072617 1528679 := bstep (se 1 (by rfl) ⟨1146509, by rfl⟩ : syracuseStep 1528679 = 2293019) B2293019
theorem B2413871 : Blo 1072617 2413871 := bstep (se 1 (by rfl) ⟨1810403, by rfl⟩ : syracuseStep 2413871 = 3620807) B3620807
theorem B8836663 : Blo 1072617 8836663 := bstep (se 1 (by rfl) ⟨6627497, by rfl⟩ : syracuseStep 8836663 = 13254995) B13254995
theorem B8148761 : Blo 1072617 8148761 := bstep (se 2 (by rfl) ⟨3055785, by rfl⟩ : syracuseStep 8148761 = 6111571) B6111571
theorem B3626855 : Blo 1072617 3626855 := bstep (se 1 (by rfl) ⟨2720141, by rfl⟩ : syracuseStep 3626855 = 5440283) B5440283
theorem B66181013 : Blo 1072617 66181013 := bstep (se 6 (by rfl) ⟨1551117, by rfl⟩ : syracuseStep 66181013 = 3102235) B3102235
theorem B6543499 : Blo 1072617 6543499 := bstep (se 1 (by rfl) ⟨4907624, by rfl⟩ : syracuseStep 6543499 = 9815249) B9815249
theorem B2415311 : Blo 1072617 2415311 := bstep (se 1 (by rfl) ⟨1811483, by rfl⟩ : syracuseStep 2415311 = 3622967) B3622967
theorem B2415851 : Blo 1072617 2415851 := bstep (se 1 (by rfl) ⟨1811888, by rfl⟩ : syracuseStep 2415851 = 3623777) B3623777
theorem B1072671 : Blo 1072617 1072671 := bstep (se 1 (by rfl) ⟨804503, by rfl⟩ : syracuseStep 1072671 = 1609007) B1609007
theorem B5430887 : Blo 1072617 5430887 := bstep (se 1 (by rfl) ⟨4073165, by rfl⟩ : syracuseStep 5430887 = 8146331) B8146331
theorem B1072799 : Blo 1072617 1072799 := bstep (se 1 (by rfl) ⟨804599, by rfl⟩ : syracuseStep 1072799 = 1609199) B1609199
theorem B1072891 : Blo 1072617 1072891 := bstep (se 1 (by rfl) ⟨804668, by rfl⟩ : syracuseStep 1072891 = 1609337) B1609337
theorem B1072987 : Blo 1072617 1072987 := bstep (se 1 (by rfl) ⟨804740, by rfl⟩ : syracuseStep 1072987 = 1609481) B1609481
theorem B4087655 : Blo 1072617 4087655 := bstep (se 1 (by rfl) ⟨3065741, by rfl⟩ : syracuseStep 4087655 = 6131483) B6131483
theorem B3629339 : Blo 1072617 3629339 := bstep (se 1 (by rfl) ⟨2722004, by rfl⟩ : syracuseStep 3629339 = 5444009) B5444009
theorem B1073755 : Blo 1072617 1073755 := bstep (se 1 (by rfl) ⟨805316, by rfl⟩ : syracuseStep 1073755 = 1610633) B1610633
theorem B1073855 : Blo 1072617 1073855 := bstep (se 1 (by rfl) ⟨805391, by rfl⟩ : syracuseStep 1073855 = 1610783) B1610783
theorem B1074415 : Blo 1072617 1074415 := bstep (se 1 (by rfl) ⟨805811, by rfl⟩ : syracuseStep 1074415 = 1611623) B1611623
theorem B5170463 : Blo 1072617 5170463 := bstep (se 1 (by rfl) ⟨3877847, by rfl⟩ : syracuseStep 5170463 = 7755695) B7755695
theorem B2417975 : Blo 1072617 2417975 := bstep (se 1 (by rfl) ⟨1813481, by rfl⟩ : syracuseStep 2417975 = 3626963) B3626963
theorem B1074495 : Blo 1072617 1074495 := bstep (se 1 (by rfl) ⟨805871, by rfl⟩ : syracuseStep 1074495 = 1611743) B1611743
theorem B1074503 : Blo 1072617 1074503 := bstep (se 1 (by rfl) ⟨805877, by rfl⟩ : syracuseStep 1074503 = 1611755) B1611755
theorem B1074535 : Blo 1072617 1074535 := bstep (se 1 (by rfl) ⟨805901, by rfl⟩ : syracuseStep 1074535 = 1611803) B1611803
theorem B1074671 : Blo 1072617 1074671 := bstep (se 1 (by rfl) ⟨806003, by rfl⟩ : syracuseStep 1074671 = 1612007) B1612007
theorem B13428497 : Blo 1072617 13428497 := bstep (se 2 (by rfl) ⟨5035686, by rfl⟩ : syracuseStep 13428497 = 10071373) B10071373
theorem B6121277 : Blo 1072617 6121277 := bstep (se 3 (by rfl) ⟨1147739, by rfl⟩ : syracuseStep 6121277 = 2295479) B2295479
theorem B1075291 : Blo 1072617 1075291 := bstep (se 1 (by rfl) ⟨806468, by rfl⟩ : syracuseStep 1075291 = 1612937) B1612937
theorem B1075303 : Blo 1072617 1075303 := bstep (se 1 (by rfl) ⟨806477, by rfl⟩ : syracuseStep 1075303 = 1612955) B1612955
theorem B9300203 : Blo 1072617 9300203 := bstep (se 1 (by rfl) ⟨6975152, by rfl⟩ : syracuseStep 9300203 = 13950305) B13950305
theorem B1075439 : Blo 1072617 1075439 := bstep (se 1 (by rfl) ⟨806579, by rfl⟩ : syracuseStep 1075439 = 1613159) B1613159
theorem B1206751 : Blo 1072617 1206751 := bstep (se 1 (by rfl) ⟨905063, by rfl⟩ : syracuseStep 1206751 = 1810127) B1810127
theorem B1075839 : Blo 1072617 1075839 := bstep (se 1 (by rfl) ⟨806879, by rfl⟩ : syracuseStep 1075839 = 1613759) B1613759
theorem B2419343 : Blo 1072617 2419343 := bstep (se 1 (by rfl) ⟨1814507, by rfl⟩ : syracuseStep 2419343 = 3629015) B3629015
theorem B1076095 : Blo 1072617 1076095 := bstep (se 1 (by rfl) ⟨807071, by rfl⟩ : syracuseStep 1076095 = 1614143) B1614143
theorem B1076383 : Blo 1072617 1076383 := bstep (se 1 (by rfl) ⟨807287, by rfl⟩ : syracuseStep 1076383 = 1614575) B1614575
theorem B2420207 : Blo 1072617 2420207 := bstep (se 1 (by rfl) ⟨1815155, by rfl⟩ : syracuseStep 2420207 = 3630311) B3630311
theorem B2420351 : Blo 1072617 2420351 := bstep (se 1 (by rfl) ⟨1815263, by rfl⟩ : syracuseStep 2420351 = 3630527) B3630527
theorem B8156537 : Blo 1072617 8156537 := bstep (se 2 (by rfl) ⟨3058701, by rfl⟩ : syracuseStep 8156537 = 6117403) B6117403
theorem B19626137 : Blo 1072617 19626137 := bstep (se 2 (by rfl) ⟨7359801, by rfl⟩ : syracuseStep 19626137 = 14719603) B14719603
theorem B4586807 : Blo 1072617 4586807 := bstep (se 1 (by rfl) ⟨3440105, by rfl⟩ : syracuseStep 4586807 = 6880211) B6880211
theorem B9174329 : Blo 1072617 9174329 := bstep (se 2 (by rfl) ⟨3440373, by rfl⟩ : syracuseStep 9174329 = 6880747) B6880747
theorem B12387143 : Blo 1072617 12387143 := bstep (se 1 (by rfl) ⟨9290357, by rfl⟩ : syracuseStep 12387143 = 18580715) B18580715
theorem B5440607 : Blo 1072617 5440607 := bstep (se 1 (by rfl) ⟨4080455, by rfl⟩ : syracuseStep 5440607 = 8160911) B8160911
theorem B1609001 : Blo 1072617 1609001 := bstep (se 2 (by rfl) ⟨603375, by rfl⟩ : syracuseStep 1609001 = 1206751) B1206751
theorem B1609247 : Blo 1072617 1609247 := bstep (se 1 (by rfl) ⟨1206935, by rfl⟩ : syracuseStep 1609247 = 2413871) B2413871
theorem B76386341 : Blo 1072617 76386341 := bstep (se 4 (by rfl) ⟨7161219, by rfl⟩ : syracuseStep 76386341 = 14322439) B14322439
theorem B1610207 : Blo 1072617 1610207 := bstep (se 1 (by rfl) ⟨1207655, by rfl⟩ : syracuseStep 1610207 = 2415311) B2415311
theorem B134353583 : Blo 1072617 134353583 := bstep (se 1 (by rfl) ⟨100765187, by rfl⟩ : syracuseStep 134353583 = 201530375) B201530375
theorem B1610567 : Blo 1072617 1610567 := bstep (se 1 (by rfl) ⟨1207925, by rfl⟩ : syracuseStep 1610567 = 2415851) B2415851
theorem B8262623 : Blo 1072617 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B2725103 : Blo 1072617 2725103 := bstep (se 1 (by rfl) ⟨2043827, by rfl⟩ : syracuseStep 2725103 = 4087655) B4087655
theorem B13047293 : Blo 1072617 13047293 := bstep (se 3 (by rfl) ⟨2446367, by rfl⟩ : syracuseStep 13047293 = 4892735) B4892735
theorem B3446975 : Blo 1072617 3446975 := bstep (se 1 (by rfl) ⟨2585231, by rfl⟩ : syracuseStep 3446975 = 5170463) B5170463
theorem B1611983 : Blo 1072617 1611983 := bstep (se 1 (by rfl) ⟨1208987, by rfl⟩ : syracuseStep 1611983 = 2417975) B2417975
theorem B8952331 : Blo 1072617 8952331 := bstep (se 1 (by rfl) ⟨6714248, by rfl⟩ : syracuseStep 8952331 = 13428497) B13428497
theorem B6200135 : Blo 1072617 6200135 := bstep (se 1 (by rfl) ⟨4650101, by rfl⟩ : syracuseStep 6200135 = 9300203) B9300203
theorem B4594751 : Blo 1072617 4594751 := bstep (se 1 (by rfl) ⟨3446063, by rfl⟩ : syracuseStep 4594751 = 6892127) B6892127
theorem B1612895 : Blo 1072617 1612895 := bstep (se 1 (by rfl) ⟨1209671, by rfl⟩ : syracuseStep 1612895 = 2419343) B2419343
theorem B1613471 : Blo 1072617 1613471 := bstep (se 1 (by rfl) ⟨1210103, by rfl⟩ : syracuseStep 1613471 = 2420207) B2420207
theorem B1613567 : Blo 1072617 1613567 := bstep (se 1 (by rfl) ⟨1210175, by rfl⟩ : syracuseStep 1613567 = 2420351) B2420351
theorem B2236223 : Blo 1072617 2236223 := bstep (se 1 (by rfl) ⟨1677167, by rfl⟩ : syracuseStep 2236223 = 3354335) B3354335
theorem B1132666847 : Blo 1072617 1132666847 := bstep (se 1 (by rfl) ⟨849500135, by rfl⟩ : syracuseStep 1132666847 = 1699000271) B1699000271
theorem B8724665 : Blo 1072617 8724665 := bstep (se 2 (by rfl) ⟨3271749, by rfl⟩ : syracuseStep 8724665 = 6543499) B6543499
theorem B9183455 : Blo 1072617 9183455 := bstep (se 1 (by rfl) ⟨6887591, by rfl⟩ : syracuseStep 9183455 = 13775183) B13775183
theorem B50274755 : Blo 1072617 50274755 := bstep (se 1 (by rfl) ⟨37706066, by rfl⟩ : syracuseStep 50274755 = 75412133) B75412133
theorem B13084091 : Blo 1072617 13084091 := bstep (se 1 (by rfl) ⟨9813068, by rfl⟩ : syracuseStep 13084091 = 19626137) B19626137
theorem B3057871 : Blo 1072617 3057871 := bstep (se 1 (by rfl) ⟨2293403, by rfl⟩ : syracuseStep 3057871 = 4586807) B4586807
theorem B3059329 : Blo 1072617 3059329 := bstep (se 2 (by rfl) ⟨1147248, by rfl⟩ : syracuseStep 3059329 = 2294497) B2294497
theorem B1290271 : Blo 1072617 1290271 := bstep (se 1 (by rfl) ⟨967703, by rfl⟩ : syracuseStep 1290271 = 1935407) B1935407
theorem B22032431 : Blo 1072617 22032431 := bstep (se 1 (by rfl) ⟨16524323, by rfl⟩ : syracuseStep 22032431 = 33048647) B33048647
theorem B4076477 : Blo 1072617 4076477 := bstep (se 3 (by rfl) ⟨764339, by rfl⟩ : syracuseStep 4076477 = 1528679) B1528679
theorem B2799775 : Blo 1072617 2799775 := bstep (se 1 (by rfl) ⟨2099831, by rfl⟩ : syracuseStep 2799775 = 4199663) B4199663
theorem B44120675 : Blo 1072617 44120675 := bstep (se 1 (by rfl) ⟨33090506, by rfl⟩ : syracuseStep 44120675 = 66181013) B66181013
theorem B3620591 : Blo 1072617 3620591 := bstep (se 1 (by rfl) ⟨2715443, by rfl⟩ : syracuseStep 3620591 = 5430887) B5430887
theorem B3063577 : Blo 1072617 3063577 := bstep (se 2 (by rfl) ⟨1148841, by rfl⟩ : syracuseStep 3063577 = 2297683) B2297683
theorem B5521553 : Blo 1072617 5521553 := bstep (se 2 (by rfl) ⟨2070582, by rfl⟩ : syracuseStep 5521553 = 4141165) B4141165
theorem B4080851 : Blo 1072617 4080851 := bstep (se 1 (by rfl) ⟨3060638, by rfl⟩ : syracuseStep 4080851 = 6121277) B6121277
theorem B11782217 : Blo 1072617 11782217 := bstep (se 2 (by rfl) ⟨4418331, by rfl⟩ : syracuseStep 11782217 = 8836663) B8836663
theorem B13748575 : Blo 1072617 13748575 := bstep (se 1 (by rfl) ⟨10311431, by rfl⟩ : syracuseStep 13748575 = 20622863) B20622863
theorem B13748939 : Blo 1072617 13748939 := bstep (se 1 (by rfl) ⟨10311704, by rfl⟩ : syracuseStep 13748939 = 20623409) B20623409
theorem B8703713 : Blo 1072617 8703713 := bstep (se 2 (by rfl) ⟨3263892, by rfl⟩ : syracuseStep 8703713 = 6527785) B6527785
theorem B12242825 : Blo 1072617 12242825 := bstep (se 2 (by rfl) ⟨4591059, by rfl⟩ : syracuseStep 12242825 = 9182119) B9182119
theorem B201478049 : Blo 1072617 201478049 := bstep (se 2 (by rfl) ⟨75554268, by rfl⟩ : syracuseStep 201478049 = 151108537) B151108537
theorem B6116219 : Blo 1072617 6116219 := bstep (se 1 (by rfl) ⟨4587164, by rfl⟩ : syracuseStep 6116219 = 9174329) B9174329
theorem B2415329 : Blo 1072617 2415329 := bstep (se 2 (by rfl) ⟨905748, by rfl⟩ : syracuseStep 2415329 = 1811497) B1811497
theorem B47734379 : Blo 1072617 47734379 := bstep (se 1 (by rfl) ⟨35800784, by rfl⟩ : syracuseStep 47734379 = 71601569) B71601569
theorem B1072795 : Blo 1072617 1072795 := bstep (se 1 (by rfl) ⟨804596, by rfl⟩ : syracuseStep 1072795 = 1609193) B1609193
theorem B3628799 : Blo 1072617 3628799 := bstep (se 1 (by rfl) ⟨2721599, by rfl⟩ : syracuseStep 3628799 = 5443199) B5443199
theorem B1073243 : Blo 1072617 1073243 := bstep (se 1 (by rfl) ⟨804932, by rfl⟩ : syracuseStep 1073243 = 1609865) B1609865
theorem B3629177 : Blo 1072617 3629177 := bstep (se 2 (by rfl) ⟨1360941, by rfl⟩ : syracuseStep 3629177 = 2721883) B2721883
theorem B3629231 : Blo 1072617 3629231 := bstep (se 1 (by rfl) ⟨2721923, by rfl⟩ : syracuseStep 3629231 = 5443847) B5443847
theorem B2416823 : Blo 1072617 2416823 := bstep (se 1 (by rfl) ⟨1812617, by rfl⟩ : syracuseStep 2416823 = 3625235) B3625235
theorem B1073791 : Blo 1072617 1073791 := bstep (se 1 (by rfl) ⟨805343, by rfl⟩ : syracuseStep 1073791 = 1610687) B1610687
theorem B5432507 : Blo 1072617 5432507 := bstep (se 1 (by rfl) ⟨4074380, by rfl⟩ : syracuseStep 5432507 = 8148761) B8148761
theorem B2417903 : Blo 1072617 2417903 := bstep (se 1 (by rfl) ⟨1813427, by rfl⟩ : syracuseStep 2417903 = 3626855) B3626855
theorem B20637625 : Blo 1072617 20637625 := bstep (se 2 (by rfl) ⟨7739109, by rfl⟩ : syracuseStep 20637625 = 15478219) B15478219
theorem B5433641 : Blo 1072617 5433641 := bstep (se 2 (by rfl) ⟨2037615, by rfl⟩ : syracuseStep 5433641 = 4075231) B4075231
theorem B2419559 : Blo 1072617 2419559 := bstep (se 1 (by rfl) ⟨1814669, by rfl⟩ : syracuseStep 2419559 = 3629339) B3629339
theorem B1076351 : Blo 1072617 1076351 := bstep (se 1 (by rfl) ⟨807263, by rfl⟩ : syracuseStep 1076351 = 1614527) B1614527
theorem B13757597 : Blo 1072617 13757597 := bstep (se 3 (by rfl) ⟨2579549, by rfl⟩ : syracuseStep 13757597 = 5159099) B5159099
theorem B4910237 : Blo 1072617 4910237 := bstep (se 3 (by rfl) ⟨920669, by rfl⟩ : syracuseStep 4910237 = 1841339) B1841339
theorem B2715241 : Blo 1072617 2715241 := bstep (se 2 (by rfl) ⟨1018215, by rfl⟩ : syracuseStep 2715241 = 2036431) B2036431
theorem B4583405 : Blo 1072617 4583405 := bstep (se 3 (by rfl) ⟨859388, by rfl⟩ : syracuseStep 4583405 = 1718777) B1718777
theorem B2716487 : Blo 1072617 2716487 := bstep (se 1 (by rfl) ⟨2037365, by rfl⟩ : syracuseStep 2716487 = 4074731) B4074731
theorem B2716699 : Blo 1072617 2716699 := bstep (se 1 (by rfl) ⟨2037524, by rfl⟩ : syracuseStep 2716699 = 4075049) B4075049
theorem B2717327 : Blo 1072617 2717327 := bstep (se 1 (by rfl) ⟨2037995, by rfl⟩ : syracuseStep 2717327 = 4075991) B4075991
theorem B5437691 : Blo 1072617 5437691 := bstep (se 1 (by rfl) ⟨4078268, by rfl⟩ : syracuseStep 5437691 = 8156537) B8156537
theorem B13794299 : Blo 1072617 13794299 := bstep (se 1 (by rfl) ⟨10345724, by rfl⟩ : syracuseStep 13794299 = 20691449) B20691449
theorem B8258095 : Blo 1072617 8258095 := bstep (se 1 (by rfl) ⟨6193571, by rfl⟩ : syracuseStep 8258095 = 12387143) B12387143
theorem B2720567 : Blo 1072617 2720567 := bstep (se 1 (by rfl) ⟨2040425, by rfl⟩ : syracuseStep 2720567 = 4080851) B4080851
theorem B8161883 : Blo 1072617 8161883 := bstep (se 1 (by rfl) ⟨6121412, by rfl⟩ : syracuseStep 8161883 = 12242825) B12242825
theorem B134318699 : Blo 1072617 134318699 := bstep (se 1 (by rfl) ⟨100739024, by rfl⟩ : syracuseStep 134318699 = 201478049) B201478049
theorem B50924227 : Blo 1072617 50924227 := bstep (se 1 (by rfl) ⟨38193170, by rfl⟩ : syracuseStep 50924227 = 76386341) B76386341
theorem B5508415 : Blo 1072617 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B2297983 : Blo 1072617 2297983 := bstep (se 1 (by rfl) ⟨1723487, by rfl⟩ : syracuseStep 2297983 = 3446975) B3446975
theorem B1610219 : Blo 1072617 1610219 := bstep (se 1 (by rfl) ⟨1207664, by rfl⟩ : syracuseStep 1610219 = 2415329) B2415329
theorem B4133423 : Blo 1072617 4133423 := bstep (se 1 (by rfl) ⟨3100067, by rfl⟩ : syracuseStep 4133423 = 6200135) B6200135
theorem B31822919 : Blo 1072617 31822919 := bstep (se 1 (by rfl) ⟨23867189, by rfl⟩ : syracuseStep 31822919 = 47734379) B47734379
theorem B755111231 : Blo 1072617 755111231 := bstep (se 1 (by rfl) ⟨566333423, by rfl⟩ : syracuseStep 755111231 = 1132666847) B1132666847
theorem B1611215 : Blo 1072617 1611215 := bstep (se 1 (by rfl) ⟨1208411, by rfl⟩ : syracuseStep 1611215 = 2416823) B2416823
theorem B1611935 : Blo 1072617 1611935 := bstep (se 1 (by rfl) ⟨1208951, by rfl⟩ : syracuseStep 1611935 = 2417903) B2417903
theorem B8722727 : Blo 1072617 8722727 := bstep (se 1 (by rfl) ⟨6542045, by rfl⟩ : syracuseStep 8722727 = 13084091) B13084091
theorem B1613039 : Blo 1072617 1613039 := bstep (se 1 (by rfl) ⟨1209779, by rfl⟩ : syracuseStep 1613039 = 2419559) B2419559
theorem B14688287 : Blo 1072617 14688287 := bstep (se 1 (by rfl) ⟨11016215, by rfl⟩ : syracuseStep 14688287 = 22032431) B22032431
theorem B1810991 : Blo 1072617 1810991 := bstep (se 1 (by rfl) ⟨1358243, by rfl⟩ : syracuseStep 1810991 = 2716487) B2716487
theorem B11936441 : Blo 1072617 11936441 := bstep (se 2 (by rfl) ⟨4476165, by rfl⟩ : syracuseStep 11936441 = 8952331) B8952331
theorem B1811551 : Blo 1072617 1811551 := bstep (se 1 (by rfl) ⟨1358663, by rfl⟩ : syracuseStep 1811551 = 2717327) B2717327
theorem B23209901 : Blo 1072617 23209901 := bstep (se 3 (by rfl) ⟨4351856, by rfl⟩ : syracuseStep 23209901 = 8703713) B8703713
theorem B3681035 : Blo 1072617 3681035 := bstep (se 1 (by rfl) ⟨2760776, by rfl⟩ : syracuseStep 3681035 = 5521553) B5521553
theorem B4077161 : Blo 1072617 4077161 := bstep (se 2 (by rfl) ⟨1528935, by rfl⟩ : syracuseStep 4077161 = 3057871) B3057871
theorem B89569055 : Blo 1072617 89569055 := bstep (se 1 (by rfl) ⟨67176791, by rfl⟩ : syracuseStep 89569055 = 134353583) B134353583
theorem B18331433 : Blo 1072617 18331433 := bstep (se 2 (by rfl) ⟨6874287, by rfl⟩ : syracuseStep 18331433 = 13748575) B13748575
theorem B4077479 : Blo 1072617 4077479 := bstep (se 1 (by rfl) ⟨3058109, by rfl⟩ : syracuseStep 4077479 = 6116219) B6116219
theorem B1816735 : Blo 1072617 1816735 := bstep (se 1 (by rfl) ⟨1362551, by rfl⟩ : syracuseStep 1816735 = 2725103) B2725103
theorem B8698195 : Blo 1072617 8698195 := bstep (se 1 (by rfl) ⟨6523646, by rfl⟩ : syracuseStep 8698195 = 13047293) B13047293
theorem B3063167 : Blo 1072617 3063167 := bstep (se 1 (by rfl) ⟨2297375, by rfl⟩ : syracuseStep 3063167 = 4594751) B4594751
theorem B3620321 : Blo 1072617 3620321 := bstep (se 2 (by rfl) ⟨1357620, by rfl⟩ : syracuseStep 3620321 = 2715241) B2715241
theorem B4079105 : Blo 1072617 4079105 := bstep (se 2 (by rfl) ⟨1529664, by rfl⟩ : syracuseStep 4079105 = 3059329) B3059329
theorem B1490815 : Blo 1072617 1490815 := bstep (se 1 (by rfl) ⟨1118111, by rfl⟩ : syracuseStep 1490815 = 2236223) B2236223
theorem B1720361 : Blo 1072617 1720361 := bstep (se 2 (by rfl) ⟨645135, by rfl⟩ : syracuseStep 1720361 = 1290271) B1290271
theorem B5816443 : Blo 1072617 5816443 := bstep (se 1 (by rfl) ⟨4362332, by rfl⟩ : syracuseStep 5816443 = 8724665) B8724665
theorem B3621671 : Blo 1072617 3621671 := bstep (se 1 (by rfl) ⟨2716253, by rfl⟩ : syracuseStep 3621671 = 5432507) B5432507
theorem B3622265 : Blo 1072617 3622265 := bstep (se 2 (by rfl) ⟨1358349, by rfl⟩ : syracuseStep 3622265 = 2716699) B2716699
theorem B3622427 : Blo 1072617 3622427 := bstep (se 1 (by rfl) ⟨2716820, by rfl⟩ : syracuseStep 3622427 = 5433641) B5433641
theorem B3625127 : Blo 1072617 3625127 := bstep (se 1 (by rfl) ⟨2718845, by rfl⟩ : syracuseStep 3625127 = 5437691) B5437691
theorem B29413783 : Blo 1072617 29413783 := bstep (se 1 (by rfl) ⟨22060337, by rfl⟩ : syracuseStep 29413783 = 44120675) B44120675
theorem B9196199 : Blo 1072617 9196199 := bstep (se 1 (by rfl) ⟨6897149, by rfl⟩ : syracuseStep 9196199 = 13794299) B13794299
theorem B4084769 : Blo 1072617 4084769 := bstep (se 2 (by rfl) ⟨1531788, by rfl⟩ : syracuseStep 4084769 = 3063577) B3063577
theorem B2413727 : Blo 1072617 2413727 := bstep (se 1 (by rfl) ⟨1810295, by rfl⟩ : syracuseStep 2413727 = 3620591) B3620591
theorem B3627071 : Blo 1072617 3627071 := bstep (se 1 (by rfl) ⟨2720303, by rfl⟩ : syracuseStep 3627071 = 5440607) B5440607
theorem B9165959 : Blo 1072617 9165959 := bstep (se 1 (by rfl) ⟨6874469, by rfl⟩ : syracuseStep 9165959 = 13748939) B13748939
theorem B1072667 : Blo 1072617 1072667 := bstep (se 1 (by rfl) ⟨804500, by rfl⟩ : syracuseStep 1072667 = 1609001) B1609001
theorem B1072831 : Blo 1072617 1072831 := bstep (se 1 (by rfl) ⟨804623, by rfl⟩ : syracuseStep 1072831 = 1609247) B1609247
theorem B27516833 : Blo 1072617 27516833 := bstep (se 2 (by rfl) ⟨10318812, by rfl⟩ : syracuseStep 27516833 = 20637625) B20637625
theorem B1073471 : Blo 1072617 1073471 := bstep (se 1 (by rfl) ⟨805103, by rfl⟩ : syracuseStep 1073471 = 1610207) B1610207
theorem B1073711 : Blo 1072617 1073711 := bstep (se 1 (by rfl) ⟨805283, by rfl⟩ : syracuseStep 1073711 = 1610567) B1610567
theorem B1074655 : Blo 1072617 1074655 := bstep (se 1 (by rfl) ⟨805991, by rfl⟩ : syracuseStep 1074655 = 1611983) B1611983
theorem B1075263 : Blo 1072617 1075263 := bstep (se 1 (by rfl) ⟨806447, by rfl⟩ : syracuseStep 1075263 = 1612895) B1612895
theorem B1075647 : Blo 1072617 1075647 := bstep (se 1 (by rfl) ⟨806735, by rfl⟩ : syracuseStep 1075647 = 1613471) B1613471
theorem B2419199 : Blo 1072617 2419199 := bstep (se 1 (by rfl) ⟨1814399, by rfl⟩ : syracuseStep 2419199 = 3628799) B3628799
theorem B1075711 : Blo 1072617 1075711 := bstep (se 1 (by rfl) ⟨806783, by rfl⟩ : syracuseStep 1075711 = 1613567) B1613567
theorem B2419451 : Blo 1072617 2419451 := bstep (se 1 (by rfl) ⟨1814588, by rfl⟩ : syracuseStep 2419451 = 3629177) B3629177
theorem B2419487 : Blo 1072617 2419487 := bstep (se 1 (by rfl) ⟨1814615, by rfl⟩ : syracuseStep 2419487 = 3629231) B3629231
theorem B6122303 : Blo 1072617 6122303 := bstep (se 1 (by rfl) ⟨4591727, by rfl⟩ : syracuseStep 6122303 = 9183455) B9183455
theorem B31419245 : Blo 1072617 31419245 := bstep (se 3 (by rfl) ⟨5891108, by rfl⟩ : syracuseStep 31419245 = 11782217) B11782217
theorem B33516503 : Blo 1072617 33516503 := bstep (se 1 (by rfl) ⟨25137377, by rfl⟩ : syracuseStep 33516503 = 50274755) B50274755
theorem B9171731 : Blo 1072617 9171731 := bstep (se 1 (by rfl) ⟨6878798, by rfl⟩ : syracuseStep 9171731 = 13757597) B13757597
theorem B3273491 : Blo 1072617 3273491 := bstep (se 1 (by rfl) ⟨2455118, by rfl⟩ : syracuseStep 3273491 = 4910237) B4910237
theorem B3733033 : Blo 1072617 3733033 := bstep (se 2 (by rfl) ⟨1399887, by rfl⟩ : syracuseStep 3733033 = 2799775) B2799775
theorem B2717651 : Blo 1072617 2717651 := bstep (se 1 (by rfl) ⟨2038238, by rfl⟩ : syracuseStep 2717651 = 4076477) B4076477
theorem B12222413 : Blo 1072617 12222413 := bstep (se 3 (by rfl) ⟨2291702, by rfl⟩ : syracuseStep 12222413 = 4583405) B4583405
theorem B1146907 : Blo 1072617 1146907 := bstep (se 1 (by rfl) ⟨860180, by rfl⟩ : syracuseStep 1146907 = 1720361) B1720361
theorem B5441255 : Blo 1072617 5441255 := bstep (se 1 (by rfl) ⟨4080941, by rfl⟩ : syracuseStep 5441255 = 8161883) B8161883
theorem B44043173 : Blo 1072617 44043173 := bstep (se 4 (by rfl) ⟨4129047, by rfl⟩ : syracuseStep 44043173 = 8258095) B8258095
theorem B2755615 : Blo 1072617 2755615 := bstep (se 1 (by rfl) ⟨2066711, by rfl⟩ : syracuseStep 2755615 = 4133423) B4133423
theorem B6130799 : Blo 1072617 6130799 := bstep (se 1 (by rfl) ⟨4598099, by rfl⟩ : syracuseStep 6130799 = 9196199) B9196199
theorem B2723179 : Blo 1072617 2723179 := bstep (se 1 (by rfl) ⟨2042384, by rfl⟩ : syracuseStep 2723179 = 4084769) B4084769
theorem B1609151 : Blo 1072617 1609151 := bstep (se 1 (by rfl) ⟨1206863, by rfl⟩ : syracuseStep 1609151 = 2413727) B2413727
theorem B67898969 : Blo 1072617 67898969 := bstep (se 2 (by rfl) ⟨25462113, by rfl⟩ : syracuseStep 67898969 = 50924227) B50924227
theorem B238850813 : Blo 1072617 238850813 := bstep (se 3 (by rfl) ⟨44784527, by rfl⟩ : syracuseStep 238850813 = 89569055) B89569055
theorem B15473267 : Blo 1072617 15473267 := bstep (se 1 (by rfl) ⟨11604950, by rfl⟩ : syracuseStep 15473267 = 23209901) B23209901
theorem B1612799 : Blo 1072617 1612799 := bstep (se 1 (by rfl) ⟨1209599, by rfl⟩ : syracuseStep 1612799 = 2419199) B2419199
theorem B1612967 : Blo 1072617 1612967 := bstep (se 1 (by rfl) ⟨1209725, by rfl⟩ : syracuseStep 1612967 = 2419451) B2419451
theorem B1612991 : Blo 1072617 1612991 := bstep (se 1 (by rfl) ⟨1209743, by rfl⟩ : syracuseStep 1612991 = 2419487) B2419487
theorem B20946163 : Blo 1072617 20946163 := bstep (se 1 (by rfl) ⟨15709622, by rfl⟩ : syracuseStep 20946163 = 31419245) B31419245
theorem B1811767 : Blo 1072617 1811767 := bstep (se 1 (by rfl) ⟨1358825, by rfl⟩ : syracuseStep 1811767 = 2717651) B2717651
theorem B2042111 : Blo 1072617 2042111 := bstep (se 1 (by rfl) ⟨1531583, by rfl⟩ : syracuseStep 2042111 = 3063167) B3063167
theorem B1813711 : Blo 1072617 1813711 := bstep (se 1 (by rfl) ⟨1360283, by rfl⟩ : syracuseStep 1813711 = 2720567) B2720567
theorem B31830509 : Blo 1072617 31830509 := bstep (se 3 (by rfl) ⟨5968220, by rfl⟩ : syracuseStep 31830509 = 11936441) B11936441
theorem B8729309 : Blo 1072617 8729309 := bstep (se 3 (by rfl) ⟨1636745, by rfl⟩ : syracuseStep 8729309 = 3273491) B3273491
theorem B21215279 : Blo 1072617 21215279 := bstep (se 1 (by rfl) ⟨15911459, by rfl⟩ : syracuseStep 21215279 = 31822919) B31822919
theorem B5815151 : Blo 1072617 5815151 := bstep (se 1 (by rfl) ⟨4361363, by rfl⟩ : syracuseStep 5815151 = 8722727) B8722727
theorem B6110639 : Blo 1072617 6110639 := bstep (se 1 (by rfl) ⟨4582979, by rfl⟩ : syracuseStep 6110639 = 9165959) B9165959
theorem B3063977 : Blo 1072617 3063977 := bstep (se 2 (by rfl) ⟨1148991, by rfl⟩ : syracuseStep 3063977 = 2297983) B2297983
theorem B29378213 : Blo 1072617 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B4081535 : Blo 1072617 4081535 := bstep (se 1 (by rfl) ⟨3061151, by rfl⟩ : syracuseStep 4081535 = 6122303) B6122303
theorem B6114487 : Blo 1072617 6114487 := bstep (se 1 (by rfl) ⟨4585865, by rfl⟩ : syracuseStep 6114487 = 9171731) B9171731
theorem B2413547 : Blo 1072617 2413547 := bstep (se 1 (by rfl) ⟨1810160, by rfl⟩ : syracuseStep 2413547 = 3620321) B3620321
theorem B1987753 : Blo 1072617 1987753 := bstep (se 2 (by rfl) ⟨745407, by rfl⟩ : syracuseStep 1987753 = 1490815) B1490815
theorem B8148275 : Blo 1072617 8148275 := bstep (se 1 (by rfl) ⟨6111206, by rfl⟩ : syracuseStep 8148275 = 12222413) B12222413
theorem B7755257 : Blo 1072617 7755257 := bstep (se 2 (by rfl) ⟨2908221, by rfl⟩ : syracuseStep 7755257 = 5816443) B5816443
theorem B2414447 : Blo 1072617 2414447 := bstep (se 1 (by rfl) ⟨1810835, by rfl⟩ : syracuseStep 2414447 = 3621671) B3621671
theorem B2414843 : Blo 1072617 2414843 := bstep (se 1 (by rfl) ⟨1811132, by rfl⟩ : syracuseStep 2414843 = 3622265) B3622265
theorem B2414951 : Blo 1072617 2414951 := bstep (se 1 (by rfl) ⟨1811213, by rfl⟩ : syracuseStep 2414951 = 3622427) B3622427
theorem B2415401 : Blo 1072617 2415401 := bstep (se 2 (by rfl) ⟨905775, by rfl⟩ : syracuseStep 2415401 = 1811551) B1811551
theorem B89545799 : Blo 1072617 89545799 := bstep (se 1 (by rfl) ⟨67159349, by rfl⟩ : syracuseStep 89545799 = 134318699) B134318699
theorem B2416751 : Blo 1072617 2416751 := bstep (se 1 (by rfl) ⟨1812563, by rfl⟩ : syracuseStep 2416751 = 3625127) B3625127
theorem B1073479 : Blo 1072617 1073479 := bstep (se 1 (by rfl) ⟨805109, by rfl⟩ : syracuseStep 1073479 = 1610219) B1610219
theorem B503407487 : Blo 1072617 503407487 := bstep (se 1 (by rfl) ⟨377555615, by rfl⟩ : syracuseStep 503407487 = 755111231) B755111231
theorem B1074143 : Blo 1072617 1074143 := bstep (se 1 (by rfl) ⟨805607, by rfl⟩ : syracuseStep 1074143 = 1611215) B1611215
theorem B2418047 : Blo 1072617 2418047 := bstep (se 1 (by rfl) ⟨1813535, by rfl⟩ : syracuseStep 2418047 = 3627071) B3627071
theorem B1074623 : Blo 1072617 1074623 := bstep (se 1 (by rfl) ⟨805967, by rfl⟩ : syracuseStep 1074623 = 1611935) B1611935
theorem B1075359 : Blo 1072617 1075359 := bstep (se 1 (by rfl) ⟨806519, by rfl⟩ : syracuseStep 1075359 = 1613039) B1613039
theorem B18344555 : Blo 1072617 18344555 := bstep (se 1 (by rfl) ⟨13758416, by rfl⟩ : syracuseStep 18344555 = 27516833) B27516833
theorem B9792191 : Blo 1072617 9792191 := bstep (se 1 (by rfl) ⟨7344143, by rfl⟩ : syracuseStep 9792191 = 14688287) B14688287
theorem B1207327 : Blo 1072617 1207327 := bstep (se 1 (by rfl) ⟨905495, by rfl⟩ : syracuseStep 1207327 = 1810991) B1810991
theorem B39218377 : Blo 1072617 39218377 := bstep (se 2 (by rfl) ⟨14706891, by rfl⟩ : syracuseStep 39218377 = 29413783) B29413783
theorem B2454023 : Blo 1072617 2454023 := bstep (se 1 (by rfl) ⟨1840517, by rfl⟩ : syracuseStep 2454023 = 3681035) B3681035
theorem B22344335 : Blo 1072617 22344335 := bstep (se 1 (by rfl) ⟨16758251, by rfl⟩ : syracuseStep 22344335 = 33516503) B33516503
theorem B4977377 : Blo 1072617 4977377 := bstep (se 2 (by rfl) ⟨1866516, by rfl⟩ : syracuseStep 4977377 = 3733033) B3733033
theorem B2422313 : Blo 1072617 2422313 := bstep (se 2 (by rfl) ⟨908367, by rfl⟩ : syracuseStep 2422313 = 1816735) B1816735
theorem B11597593 : Blo 1072617 11597593 := bstep (se 2 (by rfl) ⟨4349097, by rfl⟩ : syracuseStep 11597593 = 8698195) B8698195
theorem B2718107 : Blo 1072617 2718107 := bstep (se 1 (by rfl) ⟨2038580, by rfl⟩ : syracuseStep 2718107 = 4077161) B4077161
theorem B12220955 : Blo 1072617 12220955 := bstep (se 1 (by rfl) ⟨9165716, by rfl⟩ : syracuseStep 12220955 = 18331433) B18331433
theorem B2718319 : Blo 1072617 2718319 := bstep (se 1 (by rfl) ⟨2038739, by rfl⟩ : syracuseStep 2718319 = 4077479) B4077479
theorem B2719403 : Blo 1072617 2719403 := bstep (se 1 (by rfl) ⟨2039552, by rfl⟩ : syracuseStep 2719403 = 4079105) B4079105
theorem B2721023 : Blo 1072617 2721023 := bstep (se 1 (by rfl) ⟨2040767, by rfl⟩ : syracuseStep 2721023 = 4081535) B4081535
theorem B29362115 : Blo 1072617 29362115 := bstep (se 1 (by rfl) ⟨22021586, by rfl⟩ : syracuseStep 29362115 = 44043173) B44043173
theorem B1609031 : Blo 1072617 1609031 := bstep (se 1 (by rfl) ⟨1206773, by rfl⟩ : syracuseStep 1609031 = 2413547) B2413547
theorem B1609631 : Blo 1072617 1609631 := bstep (se 1 (by rfl) ⟨1207223, by rfl⟩ : syracuseStep 1609631 = 2414447) B2414447
theorem B1609769 : Blo 1072617 1609769 := bstep (se 2 (by rfl) ⟨603663, by rfl⟩ : syracuseStep 1609769 = 1207327) B1207327
theorem B3674153 : Blo 1072617 3674153 := bstep (se 2 (by rfl) ⟨1377807, by rfl⟩ : syracuseStep 3674153 = 2755615) B2755615
theorem B1609895 : Blo 1072617 1609895 := bstep (se 1 (by rfl) ⟨1207421, by rfl⟩ : syracuseStep 1609895 = 2414843) B2414843
theorem B1609967 : Blo 1072617 1609967 := bstep (se 1 (by rfl) ⟨1207475, by rfl⟩ : syracuseStep 1609967 = 2414951) B2414951
theorem B1610267 : Blo 1072617 1610267 := bstep (se 1 (by rfl) ⟨1207700, by rfl⟩ : syracuseStep 1610267 = 2415401) B2415401
theorem B1611167 : Blo 1072617 1611167 := bstep (se 1 (by rfl) ⟨1208375, by rfl⟩ : syracuseStep 1611167 = 2416751) B2416751
theorem B5445629 : Blo 1072617 5445629 := bstep (se 3 (by rfl) ⟨1021055, by rfl⟩ : syracuseStep 5445629 = 2042111) B2042111
theorem B1612031 : Blo 1072617 1612031 := bstep (se 1 (by rfl) ⟨1209023, by rfl⟩ : syracuseStep 1612031 = 2418047) B2418047
theorem B12229703 : Blo 1072617 12229703 := bstep (se 1 (by rfl) ⟨9172277, by rfl⟩ : syracuseStep 12229703 = 18344555) B18344555
theorem B6528127 : Blo 1072617 6528127 := bstep (se 1 (by rfl) ⟨4896095, by rfl⟩ : syracuseStep 6528127 = 9792191) B9792191
theorem B3318251 : Blo 1072617 3318251 := bstep (se 1 (by rfl) ⟨2488688, by rfl⟩ : syracuseStep 3318251 = 4977377) B4977377
theorem B1614875 : Blo 1072617 1614875 := bstep (se 1 (by rfl) ⟨1211156, by rfl⟩ : syracuseStep 1614875 = 2422313) B2422313
theorem B1812071 : Blo 1072617 1812071 := bstep (se 1 (by rfl) ⟨1359053, by rfl⟩ : syracuseStep 1812071 = 2718107) B2718107
theorem B27928217 : Blo 1072617 27928217 := bstep (se 2 (by rfl) ⟨10473081, by rfl⟩ : syracuseStep 27928217 = 20946163) B20946163
theorem B3876767 : Blo 1072617 3876767 := bstep (se 1 (by rfl) ⟨2907575, by rfl⟩ : syracuseStep 3876767 = 5815151) B5815151
theorem B4073759 : Blo 1072617 4073759 := bstep (se 1 (by rfl) ⟨3055319, by rfl⟩ : syracuseStep 4073759 = 6110639) B6110639
theorem B1812935 : Blo 1072617 1812935 := bstep (se 1 (by rfl) ⟨1359701, by rfl⟩ : syracuseStep 1812935 = 2719403) B2719403
theorem B2042651 : Blo 1072617 2042651 := bstep (se 1 (by rfl) ⟨1531988, by rfl⟩ : syracuseStep 2042651 = 3063977) B3063977
theorem B84881357 : Blo 1072617 84881357 := bstep (se 3 (by rfl) ⟨15915254, by rfl⟩ : syracuseStep 84881357 = 31830509) B31830509
theorem B45265979 : Blo 1072617 45265979 := bstep (se 1 (by rfl) ⟨33949484, by rfl⟩ : syracuseStep 45265979 = 67898969) B67898969
theorem B14896223 : Blo 1072617 14896223 := bstep (se 1 (by rfl) ⟨11172167, by rfl⟩ : syracuseStep 14896223 = 22344335) B22344335
theorem B5819539 : Blo 1072617 5819539 := bstep (se 1 (by rfl) ⟨4364654, by rfl⟩ : syracuseStep 5819539 = 8729309) B8729309
theorem B3624425 : Blo 1072617 3624425 := bstep (se 2 (by rfl) ⟨1359159, by rfl⟩ : syracuseStep 3624425 = 2718319) B2718319
theorem B14143519 : Blo 1072617 14143519 := bstep (se 1 (by rfl) ⟨10607639, by rfl⟩ : syracuseStep 14143519 = 21215279) B21215279
theorem B8147303 : Blo 1072617 8147303 := bstep (se 1 (by rfl) ⟨6110477, by rfl⟩ : syracuseStep 8147303 = 12220955) B12220955
theorem B1529209 : Blo 1072617 1529209 := bstep (se 2 (by rfl) ⟨573453, by rfl⟩ : syracuseStep 1529209 = 1146907) B1146907
theorem B19585475 : Blo 1072617 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B3627503 : Blo 1072617 3627503 := bstep (se 1 (by rfl) ⟨2720627, by rfl⟩ : syracuseStep 3627503 = 5441255) B5441255
theorem B6544061 : Blo 1072617 6544061 := bstep (se 3 (by rfl) ⟨1227011, by rfl⟩ : syracuseStep 6544061 = 2454023) B2454023
theorem B2415689 : Blo 1072617 2415689 := bstep (se 2 (by rfl) ⟨905883, by rfl⟩ : syracuseStep 2415689 = 1811767) B1811767
theorem B636935501 : Blo 1072617 636935501 := bstep (se 3 (by rfl) ⟨119425406, by rfl⟩ : syracuseStep 636935501 = 238850813) B238850813
theorem B4087199 : Blo 1072617 4087199 := bstep (se 1 (by rfl) ⟨3065399, by rfl⟩ : syracuseStep 4087199 = 6130799) B6130799
theorem B1072767 : Blo 1072617 1072767 := bstep (se 1 (by rfl) ⟨804575, by rfl⟩ : syracuseStep 1072767 = 1609151) B1609151
theorem B5432183 : Blo 1072617 5432183 := bstep (se 1 (by rfl) ⟨4074137, by rfl⟩ : syracuseStep 5432183 = 8148275) B8148275
theorem B5170171 : Blo 1072617 5170171 := bstep (se 1 (by rfl) ⟨3877628, by rfl⟩ : syracuseStep 5170171 = 7755257) B7755257
theorem B8152649 : Blo 1072617 8152649 := bstep (se 2 (by rfl) ⟨3057243, by rfl⟩ : syracuseStep 8152649 = 6114487) B6114487
theorem B52291169 : Blo 1072617 52291169 := bstep (se 2 (by rfl) ⟨19609188, by rfl⟩ : syracuseStep 52291169 = 39218377) B39218377
theorem B2418281 : Blo 1072617 2418281 := bstep (se 2 (by rfl) ⟨906855, by rfl⟩ : syracuseStep 2418281 = 1813711) B1813711
theorem B10315511 : Blo 1072617 10315511 := bstep (se 1 (by rfl) ⟨7736633, by rfl⟩ : syracuseStep 10315511 = 15473267) B15473267
theorem B3630905 : Blo 1072617 3630905 := bstep (se 2 (by rfl) ⟨1361589, by rfl⟩ : syracuseStep 3630905 = 2723179) B2723179
theorem B1075199 : Blo 1072617 1075199 := bstep (se 1 (by rfl) ⟨806399, by rfl⟩ : syracuseStep 1075199 = 1612799) B1612799
theorem B59697199 : Blo 1072617 59697199 := bstep (se 1 (by rfl) ⟨44772899, by rfl⟩ : syracuseStep 59697199 = 89545799) B89545799
theorem B1075311 : Blo 1072617 1075311 := bstep (se 1 (by rfl) ⟨806483, by rfl⟩ : syracuseStep 1075311 = 1612967) B1612967
theorem B1075327 : Blo 1072617 1075327 := bstep (se 1 (by rfl) ⟨806495, by rfl⟩ : syracuseStep 1075327 = 1612991) B1612991
theorem B335604991 : Blo 1072617 335604991 := bstep (se 1 (by rfl) ⟨251703743, by rfl⟩ : syracuseStep 335604991 = 503407487) B503407487
theorem B2650337 : Blo 1072617 2650337 := bstep (se 2 (by rfl) ⟨993876, by rfl⟩ : syracuseStep 2650337 = 1987753) B1987753
theorem B15463457 : Blo 1072617 15463457 := bstep (se 2 (by rfl) ⟨5798796, by rfl⟩ : syracuseStep 15463457 = 11597593) B11597593
theorem B8848669 : Blo 1072617 8848669 := bstep (se 3 (by rfl) ⟨1659125, by rfl⟩ : syracuseStep 8848669 = 3318251) B3318251
theorem B9930815 : Blo 1072617 9930815 := bstep (se 1 (by rfl) ⟨7448111, by rfl⟩ : syracuseStep 9930815 = 14896223) B14896223
theorem B79596265 : Blo 1072617 79596265 := bstep (se 2 (by rfl) ⟨29848599, by rfl⟩ : syracuseStep 79596265 = 59697199) B59697199
theorem B4362707 : Blo 1072617 4362707 := bstep (se 1 (by rfl) ⟨3272030, by rfl⟩ : syracuseStep 4362707 = 6544061) B6544061
theorem B1610459 : Blo 1072617 1610459 := bstep (se 1 (by rfl) ⟨1207844, by rfl⟩ : syracuseStep 1610459 = 2415689) B2415689
theorem B2724799 : Blo 1072617 2724799 := bstep (se 1 (by rfl) ⟨2043599, by rfl⟩ : syracuseStep 2724799 = 4087199) B4087199
theorem B1612187 : Blo 1072617 1612187 := bstep (se 1 (by rfl) ⟨1209140, by rfl⟩ : syracuseStep 1612187 = 2418281) B2418281
theorem B18618811 : Blo 1072617 18618811 := bstep (se 1 (by rfl) ⟨13964108, by rfl⟩ : syracuseStep 18618811 = 27928217) B27928217
theorem B2038945 : Blo 1072617 2038945 := bstep (se 2 (by rfl) ⟨764604, by rfl⟩ : syracuseStep 2038945 = 1529209) B1529209
theorem B1814015 : Blo 1072617 1814015 := bstep (se 1 (by rfl) ⟨1360511, by rfl⟩ : syracuseStep 1814015 = 2721023) B2721023
theorem B6893561 : Blo 1072617 6893561 := bstep (se 2 (by rfl) ⟨2585085, by rfl⟩ : syracuseStep 6893561 = 5170171) B5170171
theorem B13056983 : Blo 1072617 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B424623667 : Blo 1072617 424623667 := bstep (se 1 (by rfl) ⟨318467750, by rfl⟩ : syracuseStep 424623667 = 636935501) B636935501
theorem B78298973 : Blo 1072617 78298973 := bstep (se 3 (by rfl) ⟨14681057, by rfl⟩ : syracuseStep 78298973 = 29362115) B29362115
theorem B18858025 : Blo 1072617 18858025 := bstep (se 2 (by rfl) ⟨7071759, by rfl⟩ : syracuseStep 18858025 = 14143519) B14143519
theorem B3621455 : Blo 1072617 3621455 := bstep (se 1 (by rfl) ⟨2716091, by rfl⟩ : syracuseStep 3621455 = 5432183) B5432183
theorem B1361767 : Blo 1072617 1361767 := bstep (se 1 (by rfl) ⟨1021325, by rfl⟩ : syracuseStep 1361767 = 2042651) B2042651
theorem B10308971 : Blo 1072617 10308971 := bstep (se 1 (by rfl) ⟨7731728, by rfl⟩ : syracuseStep 10308971 = 15463457) B15463457
theorem B8704169 : Blo 1072617 8704169 := bstep (se 2 (by rfl) ⟨3264063, by rfl⟩ : syracuseStep 8704169 = 6528127) B6528127
theorem B1072687 : Blo 1072617 1072687 := bstep (se 1 (by rfl) ⟨804515, by rfl⟩ : syracuseStep 1072687 = 1609031) B1609031
theorem B2416283 : Blo 1072617 2416283 := bstep (se 1 (by rfl) ⟨1812212, by rfl⟩ : syracuseStep 2416283 = 3624425) B3624425
theorem B1073087 : Blo 1072617 1073087 := bstep (se 1 (by rfl) ⟨804815, by rfl⟩ : syracuseStep 1073087 = 1609631) B1609631
theorem B1073179 : Blo 1072617 1073179 := bstep (se 1 (by rfl) ⟨804884, by rfl⟩ : syracuseStep 1073179 = 1609769) B1609769
theorem B2449435 : Blo 1072617 2449435 := bstep (se 1 (by rfl) ⟨1837076, by rfl⟩ : syracuseStep 2449435 = 3674153) B3674153
theorem B1073263 : Blo 1072617 1073263 := bstep (se 1 (by rfl) ⟨804947, by rfl⟩ : syracuseStep 1073263 = 1609895) B1609895
theorem B1073311 : Blo 1072617 1073311 := bstep (se 1 (by rfl) ⟨804983, by rfl⟩ : syracuseStep 1073311 = 1609967) B1609967
theorem B5431535 : Blo 1072617 5431535 := bstep (se 1 (by rfl) ⟨4073651, by rfl⟩ : syracuseStep 5431535 = 8147303) B8147303
theorem B1073511 : Blo 1072617 1073511 := bstep (se 1 (by rfl) ⟨805133, by rfl⟩ : syracuseStep 1073511 = 1610267) B1610267
theorem B1074111 : Blo 1072617 1074111 := bstep (se 1 (by rfl) ⟨805583, by rfl⟩ : syracuseStep 1074111 = 1611167) B1611167
theorem B3630419 : Blo 1072617 3630419 := bstep (se 1 (by rfl) ⟨2722814, by rfl⟩ : syracuseStep 3630419 = 5445629) B5445629
theorem B1074687 : Blo 1072617 1074687 := bstep (se 1 (by rfl) ⟨806015, by rfl⟩ : syracuseStep 1074687 = 1612031) B1612031
theorem B7759385 : Blo 1072617 7759385 := bstep (se 2 (by rfl) ⟨2909769, by rfl⟩ : syracuseStep 7759385 = 5819539) B5819539
theorem B2418335 : Blo 1072617 2418335 := bstep (se 1 (by rfl) ⟨1813751, by rfl⟩ : syracuseStep 2418335 = 3627503) B3627503
theorem B447473321 : Blo 1072617 447473321 := bstep (se 2 (by rfl) ⟨167802495, by rfl⟩ : syracuseStep 447473321 = 335604991) B335604991
theorem B8153135 : Blo 1072617 8153135 := bstep (se 1 (by rfl) ⟨6114851, by rfl⟩ : syracuseStep 8153135 = 12229703) B12229703
theorem B1076583 : Blo 1072617 1076583 := bstep (se 1 (by rfl) ⟨807437, by rfl⟩ : syracuseStep 1076583 = 1614875) B1614875
theorem B5435099 : Blo 1072617 5435099 := bstep (se 1 (by rfl) ⟨4076324, by rfl⟩ : syracuseStep 5435099 = 8152649) B8152649
theorem B34860779 : Blo 1072617 34860779 := bstep (se 1 (by rfl) ⟨26145584, by rfl⟩ : syracuseStep 34860779 = 52291169) B52291169
theorem B1208047 : Blo 1072617 1208047 := bstep (se 1 (by rfl) ⟨906035, by rfl⟩ : syracuseStep 1208047 = 1812071) B1812071
theorem B6877007 : Blo 1072617 6877007 := bstep (se 1 (by rfl) ⟨5157755, by rfl⟩ : syracuseStep 6877007 = 10315511) B10315511
theorem B2420603 : Blo 1072617 2420603 := bstep (se 1 (by rfl) ⟨1815452, by rfl⟩ : syracuseStep 2420603 = 3630905) B3630905
theorem B2584511 : Blo 1072617 2584511 := bstep (se 1 (by rfl) ⟨1938383, by rfl⟩ : syracuseStep 2584511 = 3876767) B3876767
theorem B2715839 : Blo 1072617 2715839 := bstep (se 1 (by rfl) ⟨2036879, by rfl⟩ : syracuseStep 2715839 = 4073759) B4073759
theorem B1208623 : Blo 1072617 1208623 := bstep (se 1 (by rfl) ⟨906467, by rfl⟩ : syracuseStep 1208623 = 1812935) B1812935
theorem B56587571 : Blo 1072617 56587571 := bstep (se 1 (by rfl) ⟨42440678, by rfl⟩ : syracuseStep 56587571 = 84881357) B84881357
theorem B1766891 : Blo 1072617 1766891 := bstep (se 1 (by rfl) ⟨1325168, by rfl⟩ : syracuseStep 1766891 = 2650337) B2650337
theorem B30177319 : Blo 1072617 30177319 := bstep (se 1 (by rfl) ⟨22632989, by rfl⟩ : syracuseStep 30177319 = 45265979) B45265979
theorem B6620543 : Blo 1072617 6620543 := bstep (se 1 (by rfl) ⟨4965407, by rfl⟩ : syracuseStep 6620543 = 9930815) B9930815
theorem B11798225 : Blo 1072617 11798225 := bstep (se 2 (by rfl) ⟨4424334, by rfl⟩ : syracuseStep 11798225 = 8848669) B8848669
theorem B5802779 : Blo 1072617 5802779 := bstep (se 1 (by rfl) ⟨4352084, by rfl⟩ : syracuseStep 5802779 = 8704169) B8704169
theorem B1610729 : Blo 1072617 1610729 := bstep (se 2 (by rfl) ⟨604023, by rfl⟩ : syracuseStep 1610729 = 1208047) B1208047
theorem B1610855 : Blo 1072617 1610855 := bstep (se 1 (by rfl) ⟨1208141, by rfl⟩ : syracuseStep 1610855 = 2416283) B2416283
theorem B1611497 : Blo 1072617 1611497 := bstep (se 2 (by rfl) ⟨604311, by rfl⟩ : syracuseStep 1611497 = 1208623) B1208623
theorem B1612223 : Blo 1072617 1612223 := bstep (se 1 (by rfl) ⟨1209167, by rfl⟩ : syracuseStep 1612223 = 2418335) B2418335
theorem B23240519 : Blo 1072617 23240519 := bstep (se 1 (by rfl) ⟨17430389, by rfl⟩ : syracuseStep 23240519 = 34860779) B34860779
theorem B1613735 : Blo 1072617 1613735 := bstep (se 1 (by rfl) ⟨1210301, by rfl⟩ : syracuseStep 1613735 = 2420603) B2420603
theorem B4595707 : Blo 1072617 4595707 := bstep (se 1 (by rfl) ⟨3446780, by rfl⟩ : syracuseStep 4595707 = 6893561) B6893561
theorem B1810559 : Blo 1072617 1810559 := bstep (se 1 (by rfl) ⟨1357919, by rfl⟩ : syracuseStep 1810559 = 2715839) B2715839
theorem B37725047 : Blo 1072617 37725047 := bstep (se 1 (by rfl) ⟨28293785, by rfl⟩ : syracuseStep 37725047 = 56587571) B56587571
theorem B100576133 : Blo 1072617 100576133 := bstep (se 4 (by rfl) ⟨9429012, by rfl⟩ : syracuseStep 100576133 = 18858025) B18858025
theorem B99300325 : Blo 1072617 99300325 := bstep (se 4 (by rfl) ⟨9309405, by rfl⟩ : syracuseStep 99300325 = 18618811) B18618811
theorem B1815689 : Blo 1072617 1815689 := bstep (se 2 (by rfl) ⟨680883, by rfl⟩ : syracuseStep 1815689 = 1361767) B1361767
theorem B3621023 : Blo 1072617 3621023 := bstep (se 1 (by rfl) ⟨2715767, by rfl⟩ : syracuseStep 3621023 = 5431535) B5431535
theorem B3623399 : Blo 1072617 3623399 := bstep (se 1 (by rfl) ⟨2717549, by rfl⟩ : syracuseStep 3623399 = 5435099) B5435099
theorem B1723007 : Blo 1072617 1723007 := bstep (se 1 (by rfl) ⟨1292255, by rfl⟩ : syracuseStep 1723007 = 2584511) B2584511
theorem B8704655 : Blo 1072617 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B3265913 : Blo 1072617 3265913 := bstep (se 2 (by rfl) ⟨1224717, by rfl⟩ : syracuseStep 3265913 = 2449435) B2449435
theorem B2414303 : Blo 1072617 2414303 := bstep (se 1 (by rfl) ⟨1810727, by rfl⟩ : syracuseStep 2414303 = 3621455) B3621455
theorem B2908471 : Blo 1072617 2908471 := bstep (se 1 (by rfl) ⟨2181353, by rfl⟩ : syracuseStep 2908471 = 4362707) B4362707
theorem B1073639 : Blo 1072617 1073639 := bstep (se 1 (by rfl) ⟨805229, by rfl⟩ : syracuseStep 1073639 = 1610459) B1610459
theorem B106128353 : Blo 1072617 106128353 := bstep (se 2 (by rfl) ⟨39798132, by rfl⟩ : syracuseStep 106128353 = 79596265) B79596265
theorem B4711709 : Blo 1072617 4711709 := bstep (se 3 (by rfl) ⟨883445, by rfl⟩ : syracuseStep 4711709 = 1766891) B1766891
theorem B1074791 : Blo 1072617 1074791 := bstep (se 1 (by rfl) ⟨806093, by rfl⟩ : syracuseStep 1074791 = 1612187) B1612187
theorem B2420279 : Blo 1072617 2420279 := bstep (se 1 (by rfl) ⟨1815209, by rfl⟩ : syracuseStep 2420279 = 3630419) B3630419
theorem B5172923 : Blo 1072617 5172923 := bstep (se 1 (by rfl) ⟨3879692, by rfl⟩ : syracuseStep 5172923 = 7759385) B7759385
theorem B298315547 : Blo 1072617 298315547 := bstep (se 1 (by rfl) ⟨223736660, by rfl⟩ : syracuseStep 298315547 = 447473321) B447473321
theorem B3633065 : Blo 1072617 3633065 := bstep (se 2 (by rfl) ⟨1362399, by rfl⟩ : syracuseStep 3633065 = 2724799) B2724799
theorem B5435423 : Blo 1072617 5435423 := bstep (se 1 (by rfl) ⟨4076567, by rfl⟩ : syracuseStep 5435423 = 8153135) B8153135
theorem B1209343 : Blo 1072617 1209343 := bstep (se 1 (by rfl) ⟨907007, by rfl⟩ : syracuseStep 1209343 = 1814015) B1814015
theorem B4584671 : Blo 1072617 4584671 := bstep (se 1 (by rfl) ⟨3438503, by rfl⟩ : syracuseStep 4584671 = 6877007) B6877007
theorem B40236425 : Blo 1072617 40236425 := bstep (se 2 (by rfl) ⟨15088659, by rfl⟩ : syracuseStep 40236425 = 30177319) B30177319
theorem B27490589 : Blo 1072617 27490589 := bstep (se 3 (by rfl) ⟨5154485, by rfl⟩ : syracuseStep 27490589 = 10308971) B10308971
theorem B2718593 : Blo 1072617 2718593 := bstep (se 2 (by rfl) ⟨1019472, by rfl⟩ : syracuseStep 2718593 = 2038945) B2038945
theorem B566164889 : Blo 1072617 566164889 := bstep (se 2 (by rfl) ⟨212311833, by rfl⟩ : syracuseStep 566164889 = 424623667) B424623667
theorem B52199315 : Blo 1072617 52199315 := bstep (se 1 (by rfl) ⟨39149486, by rfl⟩ : syracuseStep 52199315 = 78298973) B78298973
theorem B7865483 : Blo 1072617 7865483 := bstep (se 1 (by rfl) ⟨5899112, by rfl⟩ : syracuseStep 7865483 = 11798225) B11798225
theorem B1148671 : Blo 1072617 1148671 := bstep (se 1 (by rfl) ⟨861503, by rfl⟩ : syracuseStep 1148671 = 1723007) B1723007
theorem B3868519 : Blo 1072617 3868519 := bstep (se 1 (by rfl) ⟨2901389, by rfl⟩ : syracuseStep 3868519 = 5802779) B5802779
theorem B5803103 : Blo 1072617 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B1609535 : Blo 1072617 1609535 := bstep (se 1 (by rfl) ⟨1207151, by rfl⟩ : syracuseStep 1609535 = 2414303) B2414303
theorem B1612457 : Blo 1072617 1612457 := bstep (se 2 (by rfl) ⟨604671, by rfl⟩ : syracuseStep 1612457 = 1209343) B1209343
theorem B67050755 : Blo 1072617 67050755 := bstep (se 1 (by rfl) ⟨50288066, by rfl⟩ : syracuseStep 67050755 = 100576133) B100576133
theorem B1613519 : Blo 1072617 1613519 := bstep (se 1 (by rfl) ⟨1210139, by rfl⟩ : syracuseStep 1613519 = 2420279) B2420279
theorem B3448615 : Blo 1072617 3448615 := bstep (se 1 (by rfl) ⟨2586461, by rfl⟩ : syracuseStep 3448615 = 5172923) B5172923
theorem B198877031 : Blo 1072617 198877031 := bstep (se 1 (by rfl) ⟨149157773, by rfl⟩ : syracuseStep 198877031 = 298315547) B298315547
theorem B3056447 : Blo 1072617 3056447 := bstep (se 1 (by rfl) ⟨2292335, by rfl⟩ : syracuseStep 3056447 = 4584671) B4584671
theorem B18327059 : Blo 1072617 18327059 := bstep (se 1 (by rfl) ⟨13745294, by rfl⟩ : syracuseStep 18327059 = 27490589) B27490589
theorem B1812395 : Blo 1072617 1812395 := bstep (se 1 (by rfl) ⟨1359296, by rfl⟩ : syracuseStep 1812395 = 2718593) B2718593
theorem B3877961 : Blo 1072617 3877961 := bstep (se 2 (by rfl) ⟨1454235, by rfl⟩ : syracuseStep 3877961 = 2908471) B2908471
theorem B12564557 : Blo 1072617 12564557 := bstep (se 3 (by rfl) ⟨2355854, by rfl⟩ : syracuseStep 12564557 = 4711709) B4711709
theorem B2177275 : Blo 1072617 2177275 := bstep (se 1 (by rfl) ⟨1632956, by rfl⟩ : syracuseStep 2177275 = 3265913) B3265913
theorem B25150031 : Blo 1072617 25150031 := bstep (se 1 (by rfl) ⟨18862523, by rfl⟩ : syracuseStep 25150031 = 37725047) B37725047
theorem B132400433 : Blo 1072617 132400433 := bstep (se 2 (by rfl) ⟨49650162, by rfl⟩ : syracuseStep 132400433 = 99300325) B99300325
theorem B3623615 : Blo 1072617 3623615 := bstep (se 1 (by rfl) ⟨2717711, by rfl⟩ : syracuseStep 3623615 = 5435423) B5435423
theorem B26824283 : Blo 1072617 26824283 := bstep (se 1 (by rfl) ⟨20118212, by rfl⟩ : syracuseStep 26824283 = 40236425) B40236425
theorem B377443259 : Blo 1072617 377443259 := bstep (se 1 (by rfl) ⟨283082444, by rfl⟩ : syracuseStep 377443259 = 566164889) B566164889
theorem B2414015 : Blo 1072617 2414015 := bstep (se 1 (by rfl) ⟨1810511, by rfl⟩ : syracuseStep 2414015 = 3621023) B3621023
theorem B4413695 : Blo 1072617 4413695 := bstep (se 1 (by rfl) ⟨3310271, by rfl⟩ : syracuseStep 4413695 = 6620543) B6620543
theorem B2415599 : Blo 1072617 2415599 := bstep (se 1 (by rfl) ⟨1811699, by rfl⟩ : syracuseStep 2415599 = 3623399) B3623399
theorem B283008941 : Blo 1072617 283008941 := bstep (se 3 (by rfl) ⟨53064176, by rfl⟩ : syracuseStep 283008941 = 106128353) B106128353
theorem B1073819 : Blo 1072617 1073819 := bstep (se 1 (by rfl) ⟨805364, by rfl⟩ : syracuseStep 1073819 = 1610729) B1610729
theorem B1073903 : Blo 1072617 1073903 := bstep (se 1 (by rfl) ⟨805427, by rfl⟩ : syracuseStep 1073903 = 1610855) B1610855
theorem B1074331 : Blo 1072617 1074331 := bstep (se 1 (by rfl) ⟨805748, by rfl⟩ : syracuseStep 1074331 = 1611497) B1611497
theorem B1074815 : Blo 1072617 1074815 := bstep (se 1 (by rfl) ⟨806111, by rfl⟩ : syracuseStep 1074815 = 1612223) B1612223
theorem B15493679 : Blo 1072617 15493679 := bstep (se 1 (by rfl) ⟨11620259, by rfl⟩ : syracuseStep 15493679 = 23240519) B23240519
theorem B1075823 : Blo 1072617 1075823 := bstep (se 1 (by rfl) ⟨806867, by rfl⟩ : syracuseStep 1075823 = 1613735) B1613735
theorem B1207039 : Blo 1072617 1207039 := bstep (se 1 (by rfl) ⟨905279, by rfl⟩ : syracuseStep 1207039 = 1810559) B1810559
theorem B2422043 : Blo 1072617 2422043 := bstep (se 1 (by rfl) ⟨1816532, by rfl⟩ : syracuseStep 2422043 = 3633065) B3633065
theorem B1210459 : Blo 1072617 1210459 := bstep (se 1 (by rfl) ⟨907844, by rfl⟩ : syracuseStep 1210459 = 1815689) B1815689
theorem B34799543 : Blo 1072617 34799543 := bstep (se 1 (by rfl) ⟨26099657, by rfl⟩ : syracuseStep 34799543 = 52199315) B52199315
theorem B6127609 : Blo 1072617 6127609 := bstep (se 2 (by rfl) ⟨2297853, by rfl⟩ : syracuseStep 6127609 = 4595707) B4595707
theorem B3868735 : Blo 1072617 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B20974621 : Blo 1072617 20974621 := bstep (se 3 (by rfl) ⟨3932741, by rfl⟩ : syracuseStep 20974621 = 7865483) B7865483
theorem B251628839 : Blo 1072617 251628839 := bstep (se 1 (by rfl) ⟨188721629, by rfl⟩ : syracuseStep 251628839 = 377443259) B377443259
theorem B1609343 : Blo 1072617 1609343 := bstep (se 1 (by rfl) ⟨1207007, by rfl⟩ : syracuseStep 1609343 = 2414015) B2414015
theorem B1609385 : Blo 1072617 1609385 := bstep (se 2 (by rfl) ⟨603519, by rfl⟩ : syracuseStep 1609385 = 1207039) B1207039
theorem B1610399 : Blo 1072617 1610399 := bstep (se 1 (by rfl) ⟨1207799, by rfl⟩ : syracuseStep 1610399 = 2415599) B2415599
theorem B44700503 : Blo 1072617 44700503 := bstep (se 1 (by rfl) ⟨33525377, by rfl⟩ : syracuseStep 44700503 = 67050755) B67050755
theorem B132584687 : Blo 1072617 132584687 := bstep (se 1 (by rfl) ⟨99438515, by rfl⟩ : syracuseStep 132584687 = 198877031) B198877031
theorem B2037631 : Blo 1072617 2037631 := bstep (se 1 (by rfl) ⟨1528223, by rfl⟩ : syracuseStep 2037631 = 3056447) B3056447
theorem B10329119 : Blo 1072617 10329119 := bstep (se 1 (by rfl) ⟨7746839, by rfl⟩ : syracuseStep 10329119 = 15493679) B15493679
theorem B1613945 : Blo 1072617 1613945 := bstep (se 2 (by rfl) ⟨605229, by rfl⟩ : syracuseStep 1613945 = 1210459) B1210459
theorem B1614695 : Blo 1072617 1614695 := bstep (se 1 (by rfl) ⟨1211021, by rfl⟩ : syracuseStep 1614695 = 2422043) B2422043
theorem B4598153 : Blo 1072617 4598153 := bstep (se 2 (by rfl) ⟨1724307, by rfl⟩ : syracuseStep 4598153 = 3448615) B3448615
theorem B8170145 : Blo 1072617 8170145 := bstep (se 2 (by rfl) ⟨3063804, by rfl⟩ : syracuseStep 8170145 = 6127609) B6127609
theorem B5158025 : Blo 1072617 5158025 := bstep (se 2 (by rfl) ⟨1934259, by rfl⟩ : syracuseStep 5158025 = 3868519) B3868519
theorem B10341229 : Blo 1072617 10341229 := bstep (se 3 (by rfl) ⟨1938980, by rfl⟩ : syracuseStep 10341229 = 3877961) B3877961
theorem B2903033 : Blo 1072617 2903033 := bstep (se 2 (by rfl) ⟨1088637, by rfl⟩ : syracuseStep 2903033 = 2177275) B2177275
theorem B8376371 : Blo 1072617 8376371 := bstep (se 1 (by rfl) ⟨6282278, by rfl⟩ : syracuseStep 8376371 = 12564557) B12564557
theorem B16766687 : Blo 1072617 16766687 := bstep (se 1 (by rfl) ⟨12575015, by rfl⟩ : syracuseStep 16766687 = 25150031) B25150031
theorem B88266955 : Blo 1072617 88266955 := bstep (se 1 (by rfl) ⟨66200216, by rfl⟩ : syracuseStep 88266955 = 132400433) B132400433
theorem B2415743 : Blo 1072617 2415743 := bstep (se 1 (by rfl) ⟨1811807, by rfl⟩ : syracuseStep 2415743 = 3623615) B3623615
theorem B1531561 : Blo 1072617 1531561 := bstep (se 2 (by rfl) ⟨574335, by rfl⟩ : syracuseStep 1531561 = 1148671) B1148671
theorem B17882855 : Blo 1072617 17882855 := bstep (se 1 (by rfl) ⟨13412141, by rfl⟩ : syracuseStep 17882855 = 26824283) B26824283
theorem B1073023 : Blo 1072617 1073023 := bstep (se 1 (by rfl) ⟨804767, by rfl⟩ : syracuseStep 1073023 = 1609535) B1609535
theorem B47079413 : Blo 1072617 47079413 := bstep (se 5 (by rfl) ⟨2206847, by rfl⟩ : syracuseStep 47079413 = 4413695) B4413695
theorem B1074971 : Blo 1072617 1074971 := bstep (se 1 (by rfl) ⟨806228, by rfl⟩ : syracuseStep 1074971 = 1612457) B1612457
theorem B1075679 : Blo 1072617 1075679 := bstep (se 1 (by rfl) ⟨806759, by rfl⟩ : syracuseStep 1075679 = 1613519) B1613519
theorem B188672627 : Blo 1072617 188672627 := bstep (se 1 (by rfl) ⟨141504470, by rfl⟩ : syracuseStep 188672627 = 283008941) B283008941
theorem B12218039 : Blo 1072617 12218039 := bstep (se 1 (by rfl) ⟨9163529, by rfl⟩ : syracuseStep 12218039 = 18327059) B18327059
theorem B1208263 : Blo 1072617 1208263 := bstep (se 1 (by rfl) ⟨906197, by rfl⟩ : syracuseStep 1208263 = 1812395) B1812395
theorem B23199695 : Blo 1072617 23199695 := bstep (se 1 (by rfl) ⟨17399771, by rfl⟩ : syracuseStep 23199695 = 34799543) B34799543
theorem B1935355 : Blo 1072617 1935355 := bstep (se 1 (by rfl) ⟨1451516, by rfl⟩ : syracuseStep 1935355 = 2903033) B2903033
theorem B6886079 : Blo 1072617 6886079 := bstep (se 1 (by rfl) ⟨5164559, by rfl⟩ : syracuseStep 6886079 = 10329119) B10329119
theorem B1610495 : Blo 1072617 1610495 := bstep (se 1 (by rfl) ⟨1207871, by rfl⟩ : syracuseStep 1610495 = 2415743) B2415743
theorem B1611017 : Blo 1072617 1611017 := bstep (se 2 (by rfl) ⟨604131, by rfl⟩ : syracuseStep 1611017 = 1208263) B1208263
theorem B5446763 : Blo 1072617 5446763 := bstep (se 1 (by rfl) ⟨4085072, by rfl⟩ : syracuseStep 5446763 = 8170145) B8170145
theorem B2042081 : Blo 1072617 2042081 := bstep (se 2 (by rfl) ⟨765780, by rfl⟩ : syracuseStep 2042081 = 1531561) B1531561
theorem B167752559 : Blo 1072617 167752559 := bstep (se 1 (by rfl) ⟨125814419, by rfl⟩ : syracuseStep 167752559 = 251628839) B251628839
theorem B5584247 : Blo 1072617 5584247 := bstep (se 1 (by rfl) ⟨4188185, by rfl⟩ : syracuseStep 5584247 = 8376371) B8376371
theorem B5158313 : Blo 1072617 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B88389791 : Blo 1072617 88389791 := bstep (se 1 (by rfl) ⟨66292343, by rfl⟩ : syracuseStep 88389791 = 132584687) B132584687
theorem B27966161 : Blo 1072617 27966161 := bstep (se 2 (by rfl) ⟨10487310, by rfl⟩ : syracuseStep 27966161 = 20974621) B20974621
theorem B44711165 : Blo 1072617 44711165 := bstep (se 3 (by rfl) ⟨8383343, by rfl⟩ : syracuseStep 44711165 = 16766687) B16766687
theorem B3065435 : Blo 1072617 3065435 := bstep (se 1 (by rfl) ⟨2299076, by rfl⟩ : syracuseStep 3065435 = 4598153) B4598153
theorem B125781751 : Blo 1072617 125781751 := bstep (se 1 (by rfl) ⟨94336313, by rfl⟩ : syracuseStep 125781751 = 188672627) B188672627
theorem B8145359 : Blo 1072617 8145359 := bstep (se 1 (by rfl) ⟨6109019, by rfl⟩ : syracuseStep 8145359 = 12218039) B12218039
theorem B117689273 : Blo 1072617 117689273 := bstep (se 2 (by rfl) ⟨44133477, by rfl⟩ : syracuseStep 117689273 = 88266955) B88266955
theorem B119201341 : Blo 1072617 119201341 := bstep (se 3 (by rfl) ⟨22350251, by rfl⟩ : syracuseStep 119201341 = 44700503) B44700503
theorem B1072895 : Blo 1072617 1072895 := bstep (se 1 (by rfl) ⟨804671, by rfl⟩ : syracuseStep 1072895 = 1609343) B1609343
theorem B1072923 : Blo 1072617 1072923 := bstep (se 1 (by rfl) ⟨804692, by rfl⟩ : syracuseStep 1072923 = 1609385) B1609385
theorem B1073599 : Blo 1072617 1073599 := bstep (se 1 (by rfl) ⟨805199, by rfl⟩ : syracuseStep 1073599 = 1610399) B1610399
theorem B13788305 : Blo 1072617 13788305 := bstep (se 2 (by rfl) ⟨5170614, by rfl⟩ : syracuseStep 13788305 = 10341229) B10341229
theorem B11921903 : Blo 1072617 11921903 := bstep (se 1 (by rfl) ⟨8941427, by rfl⟩ : syracuseStep 11921903 = 17882855) B17882855
theorem B31386275 : Blo 1072617 31386275 := bstep (se 1 (by rfl) ⟨23539706, by rfl⟩ : syracuseStep 31386275 = 47079413) B47079413
theorem B1075963 : Blo 1072617 1075963 := bstep (se 1 (by rfl) ⟨806972, by rfl⟩ : syracuseStep 1075963 = 1613945) B1613945
theorem B1076463 : Blo 1072617 1076463 := bstep (se 1 (by rfl) ⟨807347, by rfl⟩ : syracuseStep 1076463 = 1614695) B1614695
theorem B2716841 : Blo 1072617 2716841 := bstep (se 2 (by rfl) ⟨1018815, by rfl⟩ : syracuseStep 2716841 = 2037631) B2037631
theorem B3438683 : Blo 1072617 3438683 := bstep (se 1 (by rfl) ⟨2579012, by rfl⟩ : syracuseStep 3438683 = 5158025) B5158025
theorem B15466463 : Blo 1072617 15466463 := bstep (se 1 (by rfl) ⟨11599847, by rfl⟩ : syracuseStep 15466463 = 23199695) B23199695
theorem B167709001 : Blo 1072617 167709001 := bstep (se 2 (by rfl) ⟨62890875, by rfl⟩ : syracuseStep 167709001 = 125781751) B125781751
theorem B4590719 : Blo 1072617 4590719 := bstep (se 1 (by rfl) ⟨3443039, by rfl⟩ : syracuseStep 4590719 = 6886079) B6886079
theorem B1811227 : Blo 1072617 1811227 := bstep (se 1 (by rfl) ⟨1358420, by rfl⟩ : syracuseStep 1811227 = 2716841) B2716841
theorem B58926527 : Blo 1072617 58926527 := bstep (se 1 (by rfl) ⟨44194895, by rfl⟩ : syracuseStep 58926527 = 88389791) B88389791
theorem B158935121 : Blo 1072617 158935121 := bstep (se 2 (by rfl) ⟨59600670, by rfl⟩ : syracuseStep 158935121 = 119201341) B119201341
theorem B2043623 : Blo 1072617 2043623 := bstep (se 1 (by rfl) ⟨1532717, by rfl⟩ : syracuseStep 2043623 = 3065435) B3065435
theorem B78459515 : Blo 1072617 78459515 := bstep (se 1 (by rfl) ⟨58844636, by rfl⟩ : syracuseStep 78459515 = 117689273) B117689273
theorem B9192203 : Blo 1072617 9192203 := bstep (se 1 (by rfl) ⟨6894152, by rfl⟩ : syracuseStep 9192203 = 13788305) B13788305
theorem B1361387 : Blo 1072617 1361387 := bstep (se 1 (by rfl) ⟨1021040, by rfl⟩ : syracuseStep 1361387 = 2042081) B2042081
theorem B7947935 : Blo 1072617 7947935 := bstep (se 1 (by rfl) ⟨5960951, by rfl⟩ : syracuseStep 7947935 = 11921903) B11921903
theorem B20924183 : Blo 1072617 20924183 := bstep (se 1 (by rfl) ⟨15693137, by rfl⟩ : syracuseStep 20924183 = 31386275) B31386275
theorem B3722831 : Blo 1072617 3722831 := bstep (se 1 (by rfl) ⟨2792123, by rfl⟩ : syracuseStep 3722831 = 5584247) B5584247
theorem B29807443 : Blo 1072617 29807443 := bstep (se 1 (by rfl) ⟨22355582, by rfl⟩ : syracuseStep 29807443 = 44711165) B44711165
theorem B10310975 : Blo 1072617 10310975 := bstep (se 1 (by rfl) ⟨7733231, by rfl⟩ : syracuseStep 10310975 = 15466463) B15466463
theorem B5430239 : Blo 1072617 5430239 := bstep (se 1 (by rfl) ⟨4072679, by rfl⟩ : syracuseStep 5430239 = 8145359) B8145359
theorem B447340157 : Blo 1072617 447340157 := bstep (se 3 (by rfl) ⟨83876279, by rfl⟩ : syracuseStep 447340157 = 167752559) B167752559
theorem B2580473 : Blo 1072617 2580473 := bstep (se 2 (by rfl) ⟨967677, by rfl⟩ : syracuseStep 2580473 = 1935355) B1935355
theorem B1073663 : Blo 1072617 1073663 := bstep (se 1 (by rfl) ⟨805247, by rfl⟩ : syracuseStep 1073663 = 1610495) B1610495
theorem B1074011 : Blo 1072617 1074011 := bstep (se 1 (by rfl) ⟨805508, by rfl⟩ : syracuseStep 1074011 = 1611017) B1611017
theorem B3631175 : Blo 1072617 3631175 := bstep (se 1 (by rfl) ⟨2723381, by rfl⟩ : syracuseStep 3631175 = 5446763) B5446763
theorem B3438875 : Blo 1072617 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B2292455 : Blo 1072617 2292455 := bstep (se 1 (by rfl) ⟨1719341, by rfl⟩ : syracuseStep 2292455 = 3438683) B3438683
theorem B18644107 : Blo 1072617 18644107 := bstep (se 1 (by rfl) ⟨13983080, by rfl⟩ : syracuseStep 18644107 = 27966161) B27966161
theorem B6128135 : Blo 1072617 6128135 := bstep (se 1 (by rfl) ⟨4596101, by rfl⟩ : syracuseStep 6128135 = 9192203) B9192203
theorem B223612001 : Blo 1072617 223612001 := bstep (se 2 (by rfl) ⟨83854500, by rfl⟩ : syracuseStep 223612001 = 167709001) B167709001
theorem B298226771 : Blo 1072617 298226771 := bstep (se 1 (by rfl) ⟨223670078, by rfl⟩ : syracuseStep 298226771 = 447340157) B447340157
theorem B52306343 : Blo 1072617 52306343 := bstep (se 1 (by rfl) ⟨39229757, by rfl⟩ : syracuseStep 52306343 = 78459515) B78459515
theorem B3060479 : Blo 1072617 3060479 := bstep (se 1 (by rfl) ⟨2295359, by rfl⟩ : syracuseStep 3060479 = 4590719) B4590719
theorem B3620159 : Blo 1072617 3620159 := bstep (se 1 (by rfl) ⟨2715119, by rfl⟩ : syracuseStep 3620159 = 5430239) B5430239
theorem B1720315 : Blo 1072617 1720315 := bstep (se 1 (by rfl) ⟨1290236, by rfl⟩ : syracuseStep 1720315 = 2580473) B2580473
theorem B105956747 : Blo 1072617 105956747 := bstep (se 1 (by rfl) ⟨79467560, by rfl⟩ : syracuseStep 105956747 = 158935121) B158935121
theorem B1362415 : Blo 1072617 1362415 := bstep (se 1 (by rfl) ⟨1021811, by rfl⟩ : syracuseStep 1362415 = 2043623) B2043623
theorem B24858809 : Blo 1072617 24858809 := bstep (se 2 (by rfl) ⟨9322053, by rfl⟩ : syracuseStep 24858809 = 18644107) B18644107
theorem B1528303 : Blo 1072617 1528303 := bstep (se 1 (by rfl) ⟨1146227, by rfl⟩ : syracuseStep 1528303 = 2292455) B2292455
theorem B2414969 : Blo 1072617 2414969 := bstep (se 2 (by rfl) ⟨905613, by rfl⟩ : syracuseStep 2414969 = 1811227) B1811227
theorem B5298623 : Blo 1072617 5298623 := bstep (se 1 (by rfl) ⟨3973967, by rfl⟩ : syracuseStep 5298623 = 7947935) B7947935
theorem B2481887 : Blo 1072617 2481887 := bstep (se 1 (by rfl) ⟨1861415, by rfl⟩ : syracuseStep 2481887 = 3722831) B3722831
theorem B6873983 : Blo 1072617 6873983 := bstep (se 1 (by rfl) ⟨5155487, by rfl⟩ : syracuseStep 6873983 = 10310975) B10310975
theorem B3630365 : Blo 1072617 3630365 := bstep (se 3 (by rfl) ⟨680693, by rfl⟩ : syracuseStep 3630365 = 1361387) B1361387
theorem B55797821 : Blo 1072617 55797821 := bstep (se 3 (by rfl) ⟨10462091, by rfl⟩ : syracuseStep 55797821 = 20924183) B20924183
theorem B9170333 : Blo 1072617 9170333 := bstep (se 3 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 9170333 = 3438875) B3438875
theorem B39284351 : Blo 1072617 39284351 := bstep (se 1 (by rfl) ⟨29463263, by rfl⟩ : syracuseStep 39284351 = 58926527) B58926527
theorem B39743257 : Blo 1072617 39743257 := bstep (se 2 (by rfl) ⟨14903721, by rfl⟩ : syracuseStep 39743257 = 29807443) B29807443
theorem B2420783 : Blo 1072617 2420783 := bstep (se 1 (by rfl) ⟨1815587, by rfl⟩ : syracuseStep 2420783 = 3631175) B3631175
theorem B1609979 : Blo 1072617 1609979 := bstep (se 1 (by rfl) ⟨1207484, by rfl⟩ : syracuseStep 1609979 = 2414969) B2414969
theorem B52991009 : Blo 1072617 52991009 := bstep (se 2 (by rfl) ⟨19871628, by rfl⟩ : syracuseStep 52991009 = 39743257) B39743257
theorem B34870895 : Blo 1072617 34870895 := bstep (se 1 (by rfl) ⟨26153171, by rfl⟩ : syracuseStep 34870895 = 52306343) B52306343
theorem B2293753 : Blo 1072617 2293753 := bstep (se 2 (by rfl) ⟨860157, by rfl⟩ : syracuseStep 2293753 = 1720315) B1720315
theorem B2037737 : Blo 1072617 2037737 := bstep (se 2 (by rfl) ⟨764151, by rfl⟩ : syracuseStep 2037737 = 1528303) B1528303
theorem B37198547 : Blo 1072617 37198547 := bstep (se 1 (by rfl) ⟨27898910, by rfl⟩ : syracuseStep 37198547 = 55797821) B55797821
theorem B26189567 : Blo 1072617 26189567 := bstep (se 1 (by rfl) ⟨19642175, by rfl⟩ : syracuseStep 26189567 = 39284351) B39284351
theorem B1613855 : Blo 1072617 1613855 := bstep (se 1 (by rfl) ⟨1210391, by rfl⟩ : syracuseStep 1613855 = 2420783) B2420783
theorem B2040319 : Blo 1072617 2040319 := bstep (se 1 (by rfl) ⟨1530239, by rfl⟩ : syracuseStep 2040319 = 3060479) B3060479
theorem B149074667 : Blo 1072617 149074667 := bstep (se 1 (by rfl) ⟨111806000, by rfl⟩ : syracuseStep 149074667 = 223612001) B223612001
theorem B1816553 : Blo 1072617 1816553 := bstep (se 2 (by rfl) ⟨681207, by rfl⟩ : syracuseStep 1816553 = 1362415) B1362415
theorem B198817847 : Blo 1072617 198817847 := bstep (se 1 (by rfl) ⟨149113385, by rfl⟩ : syracuseStep 198817847 = 298226771) B298226771
theorem B1654591 : Blo 1072617 1654591 := bstep (se 1 (by rfl) ⟨1240943, by rfl⟩ : syracuseStep 1654591 = 2481887) B2481887
theorem B6113555 : Blo 1072617 6113555 := bstep (se 1 (by rfl) ⟨4585166, by rfl⟩ : syracuseStep 6113555 = 9170333) B9170333
theorem B2413439 : Blo 1072617 2413439 := bstep (se 1 (by rfl) ⟨1810079, by rfl⟩ : syracuseStep 2413439 = 3620159) B3620159
theorem B4085423 : Blo 1072617 4085423 := bstep (se 1 (by rfl) ⟨3064067, by rfl⟩ : syracuseStep 4085423 = 6128135) B6128135
theorem B70637831 : Blo 1072617 70637831 := bstep (se 1 (by rfl) ⟨52978373, by rfl⟩ : syracuseStep 70637831 = 105956747) B105956747
theorem B16572539 : Blo 1072617 16572539 := bstep (se 1 (by rfl) ⟨12429404, by rfl⟩ : syracuseStep 16572539 = 24858809) B24858809
theorem B3532415 : Blo 1072617 3532415 := bstep (se 1 (by rfl) ⟨2649311, by rfl⟩ : syracuseStep 3532415 = 5298623) B5298623
theorem B4582655 : Blo 1072617 4582655 := bstep (se 1 (by rfl) ⟨3436991, by rfl⟩ : syracuseStep 4582655 = 6873983) B6873983
theorem B2420243 : Blo 1072617 2420243 := bstep (se 1 (by rfl) ⟨1815182, by rfl⟩ : syracuseStep 2420243 = 3630365) B3630365
theorem B2720425 : Blo 1072617 2720425 := bstep (se 2 (by rfl) ⟨1020159, by rfl⟩ : syracuseStep 2720425 = 2040319) B2040319
theorem B1608959 : Blo 1072617 1608959 := bstep (se 1 (by rfl) ⟨1206719, by rfl⟩ : syracuseStep 1608959 = 2413439) B2413439
theorem B35327339 : Blo 1072617 35327339 := bstep (se 1 (by rfl) ⟨26495504, by rfl⟩ : syracuseStep 35327339 = 52991009) B52991009
theorem B2723615 : Blo 1072617 2723615 := bstep (se 1 (by rfl) ⟨2042711, by rfl⟩ : syracuseStep 2723615 = 4085423) B4085423
theorem B47091887 : Blo 1072617 47091887 := bstep (se 1 (by rfl) ⟨35318915, by rfl⟩ : syracuseStep 47091887 = 70637831) B70637831
theorem B11048359 : Blo 1072617 11048359 := bstep (se 1 (by rfl) ⟨8286269, by rfl⟩ : syracuseStep 11048359 = 16572539) B16572539
theorem B3055103 : Blo 1072617 3055103 := bstep (se 1 (by rfl) ⟨2291327, by rfl⟩ : syracuseStep 3055103 = 4582655) B4582655
theorem B1613495 : Blo 1072617 1613495 := bstep (se 1 (by rfl) ⟨1210121, by rfl⟩ : syracuseStep 1613495 = 2420243) B2420243
theorem B2206121 : Blo 1072617 2206121 := bstep (se 2 (by rfl) ⟨827295, by rfl⟩ : syracuseStep 2206121 = 1654591) B1654591
theorem B3058337 : Blo 1072617 3058337 := bstep (se 2 (by rfl) ⟨1146876, by rfl⟩ : syracuseStep 3058337 = 2293753) B2293753
theorem B4075703 : Blo 1072617 4075703 := bstep (se 1 (by rfl) ⟨3056777, by rfl⟩ : syracuseStep 4075703 = 6113555) B6113555
theorem B23247263 : Blo 1072617 23247263 := bstep (se 1 (by rfl) ⟨17435447, by rfl⟩ : syracuseStep 23247263 = 34870895) B34870895
theorem B1073319 : Blo 1072617 1073319 := bstep (se 1 (by rfl) ⟨804989, by rfl⟩ : syracuseStep 1073319 = 1609979) B1609979
theorem B24799031 : Blo 1072617 24799031 := bstep (se 1 (by rfl) ⟨18599273, by rfl⟩ : syracuseStep 24799031 = 37198547) B37198547
theorem B17459711 : Blo 1072617 17459711 := bstep (se 1 (by rfl) ⟨13094783, by rfl⟩ : syracuseStep 17459711 = 26189567) B26189567
theorem B5433965 : Blo 1072617 5433965 := bstep (se 3 (by rfl) ⟨1018868, by rfl⟩ : syracuseStep 5433965 = 2037737) B2037737
theorem B1075903 : Blo 1072617 1075903 := bstep (se 1 (by rfl) ⟨806927, by rfl⟩ : syracuseStep 1075903 = 1613855) B1613855
theorem B37679093 : Blo 1072617 37679093 := bstep (se 5 (by rfl) ⟨1766207, by rfl⟩ : syracuseStep 37679093 = 3532415) B3532415
theorem B99383111 : Blo 1072617 99383111 := bstep (se 1 (by rfl) ⟨74537333, by rfl⟩ : syracuseStep 99383111 = 149074667) B149074667
theorem B1211035 : Blo 1072617 1211035 := bstep (se 1 (by rfl) ⟨908276, by rfl⟩ : syracuseStep 1211035 = 1816553) B1816553
theorem B132545231 : Blo 1072617 132545231 := bstep (se 1 (by rfl) ⟨99408923, by rfl⟩ : syracuseStep 132545231 = 198817847) B198817847
theorem B31394591 : Blo 1072617 31394591 := bstep (se 1 (by rfl) ⟨23545943, by rfl⟩ : syracuseStep 31394591 = 47091887) B47091887
theorem B2036735 : Blo 1072617 2036735 := bstep (se 1 (by rfl) ⟨1527551, by rfl⟩ : syracuseStep 2036735 = 3055103) B3055103
theorem B11639807 : Blo 1072617 11639807 := bstep (se 1 (by rfl) ⟨8729855, by rfl⟩ : syracuseStep 11639807 = 17459711) B17459711
theorem B1614713 : Blo 1072617 1614713 := bstep (se 2 (by rfl) ⟨605517, by rfl⟩ : syracuseStep 1614713 = 1211035) B1211035
theorem B1815743 : Blo 1072617 1815743 := bstep (se 1 (by rfl) ⟨1361807, by rfl⟩ : syracuseStep 1815743 = 2723615) B2723615
theorem B5882989 : Blo 1072617 5882989 := bstep (se 3 (by rfl) ⟨1103060, by rfl⟩ : syracuseStep 5882989 = 2206121) B2206121
theorem B16532687 : Blo 1072617 16532687 := bstep (se 1 (by rfl) ⟨12399515, by rfl⟩ : syracuseStep 16532687 = 24799031) B24799031
theorem B3622643 : Blo 1072617 3622643 := bstep (se 1 (by rfl) ⟨2716982, by rfl⟩ : syracuseStep 3622643 = 5433965) B5433965
theorem B14731145 : Blo 1072617 14731145 := bstep (se 2 (by rfl) ⟨5524179, by rfl⟩ : syracuseStep 14731145 = 11048359) B11048359
theorem B25119395 : Blo 1072617 25119395 := bstep (se 1 (by rfl) ⟨18839546, by rfl⟩ : syracuseStep 25119395 = 37679093) B37679093
theorem B88363487 : Blo 1072617 88363487 := bstep (se 1 (by rfl) ⟨66272615, by rfl⟩ : syracuseStep 88363487 = 132545231) B132545231
theorem B3627233 : Blo 1072617 3627233 := bstep (se 2 (by rfl) ⟨1360212, by rfl⟩ : syracuseStep 3627233 = 2720425) B2720425
theorem B1072639 : Blo 1072617 1072639 := bstep (se 1 (by rfl) ⟨804479, by rfl⟩ : syracuseStep 1072639 = 1608959) B1608959
theorem B23551559 : Blo 1072617 23551559 := bstep (se 1 (by rfl) ⟨17663669, by rfl⟩ : syracuseStep 23551559 = 35327339) B35327339
theorem B1075663 : Blo 1072617 1075663 := bstep (se 1 (by rfl) ⟨806747, by rfl⟩ : syracuseStep 1075663 = 1613495) B1613495
theorem B8155565 : Blo 1072617 8155565 := bstep (se 3 (by rfl) ⟨1529168, by rfl⟩ : syracuseStep 8155565 = 3058337) B3058337
theorem B2717135 : Blo 1072617 2717135 := bstep (se 1 (by rfl) ⟨2037851, by rfl⟩ : syracuseStep 2717135 = 4075703) B4075703
theorem B66255407 : Blo 1072617 66255407 := bstep (se 1 (by rfl) ⟨49691555, by rfl⟩ : syracuseStep 66255407 = 99383111) B99383111
theorem B15498175 : Blo 1072617 15498175 := bstep (se 1 (by rfl) ⟨11623631, by rfl⟩ : syracuseStep 15498175 = 23247263) B23247263
theorem B16746263 : Blo 1072617 16746263 := bstep (se 1 (by rfl) ⟨12559697, by rfl⟩ : syracuseStep 16746263 = 25119395) B25119395
theorem B15701039 : Blo 1072617 15701039 := bstep (se 1 (by rfl) ⟨11775779, by rfl⟩ : syracuseStep 15701039 = 23551559) B23551559
theorem B1811423 : Blo 1072617 1811423 := bstep (se 1 (by rfl) ⟨1358567, by rfl⟩ : syracuseStep 1811423 = 2717135) B2717135
theorem B7843985 : Blo 1072617 7843985 := bstep (se 2 (by rfl) ⟨2941494, by rfl⟩ : syracuseStep 7843985 = 5882989) B5882989
theorem B44087165 : Blo 1072617 44087165 := bstep (se 3 (by rfl) ⟨8266343, by rfl⟩ : syracuseStep 44087165 = 16532687) B16532687
theorem B1357823 : Blo 1072617 1357823 := bstep (se 1 (by rfl) ⟨1018367, by rfl⟩ : syracuseStep 1357823 = 2036735) B2036735
theorem B20664233 : Blo 1072617 20664233 := bstep (se 2 (by rfl) ⟨7749087, by rfl⟩ : syracuseStep 20664233 = 15498175) B15498175
theorem B2415095 : Blo 1072617 2415095 := bstep (se 1 (by rfl) ⟨1811321, by rfl⟩ : syracuseStep 2415095 = 3622643) B3622643
theorem B9820763 : Blo 1072617 9820763 := bstep (se 1 (by rfl) ⟨7365572, by rfl⟩ : syracuseStep 9820763 = 14731145) B14731145
theorem B20929727 : Blo 1072617 20929727 := bstep (se 1 (by rfl) ⟨15697295, by rfl⟩ : syracuseStep 20929727 = 31394591) B31394591
theorem B58908991 : Blo 1072617 58908991 := bstep (se 1 (by rfl) ⟨44181743, by rfl⟩ : syracuseStep 58908991 = 88363487) B88363487
theorem B2418155 : Blo 1072617 2418155 := bstep (se 1 (by rfl) ⟨1813616, by rfl⟩ : syracuseStep 2418155 = 3627233) B3627233
theorem B7759871 : Blo 1072617 7759871 := bstep (se 1 (by rfl) ⟨5819903, by rfl⟩ : syracuseStep 7759871 = 11639807) B11639807
theorem B1076475 : Blo 1072617 1076475 := bstep (se 1 (by rfl) ⟨807356, by rfl⟩ : syracuseStep 1076475 = 1614713) B1614713
theorem B5437043 : Blo 1072617 5437043 := bstep (se 1 (by rfl) ⟨4077782, by rfl⟩ : syracuseStep 5437043 = 8155565) B8155565
theorem B1210495 : Blo 1072617 1210495 := bstep (se 1 (by rfl) ⟨907871, by rfl⟩ : syracuseStep 1210495 = 1815743) B1815743
theorem B44170271 : Blo 1072617 44170271 := bstep (se 1 (by rfl) ⟨33127703, by rfl⟩ : syracuseStep 44170271 = 66255407) B66255407
theorem B78545321 : Blo 1072617 78545321 := bstep (se 2 (by rfl) ⟨29454495, by rfl⟩ : syracuseStep 78545321 = 58908991) B58908991
theorem B1610063 : Blo 1072617 1610063 := bstep (se 1 (by rfl) ⟨1207547, by rfl⟩ : syracuseStep 1610063 = 2415095) B2415095
theorem B1612103 : Blo 1072617 1612103 := bstep (se 1 (by rfl) ⟨1209077, by rfl⟩ : syracuseStep 1612103 = 2418155) B2418155
theorem B1613993 : Blo 1072617 1613993 := bstep (se 2 (by rfl) ⟨605247, by rfl⟩ : syracuseStep 1613993 = 1210495) B1210495
theorem B13776155 : Blo 1072617 13776155 := bstep (se 1 (by rfl) ⟨10332116, by rfl⟩ : syracuseStep 13776155 = 20664233) B20664233
theorem B10467359 : Blo 1072617 10467359 := bstep (se 1 (by rfl) ⟨7850519, by rfl⟩ : syracuseStep 10467359 = 15701039) B15701039
theorem B3620861 : Blo 1072617 3620861 := bstep (se 3 (by rfl) ⟨678911, by rfl⟩ : syracuseStep 3620861 = 1357823) B1357823
theorem B5229323 : Blo 1072617 5229323 := bstep (se 1 (by rfl) ⟨3921992, by rfl⟩ : syracuseStep 5229323 = 7843985) B7843985
theorem B3624695 : Blo 1072617 3624695 := bstep (se 1 (by rfl) ⟨2718521, by rfl⟩ : syracuseStep 3624695 = 5437043) B5437043
theorem B29446847 : Blo 1072617 29446847 := bstep (se 1 (by rfl) ⟨22085135, by rfl⟩ : syracuseStep 29446847 = 44170271) B44170271
theorem B11164175 : Blo 1072617 11164175 := bstep (se 1 (by rfl) ⟨8373131, by rfl⟩ : syracuseStep 11164175 = 16746263) B16746263
theorem B6547175 : Blo 1072617 6547175 := bstep (se 1 (by rfl) ⟨4910381, by rfl⟩ : syracuseStep 6547175 = 9820763) B9820763
theorem B13953151 : Blo 1072617 13953151 := bstep (se 1 (by rfl) ⟨10464863, by rfl⟩ : syracuseStep 13953151 = 20929727) B20929727
theorem B1207615 : Blo 1072617 1207615 := bstep (se 1 (by rfl) ⟨905711, by rfl⟩ : syracuseStep 1207615 = 1811423) B1811423
theorem B5173247 : Blo 1072617 5173247 := bstep (se 1 (by rfl) ⟨3879935, by rfl⟩ : syracuseStep 5173247 = 7759871) B7759871
theorem B29391443 : Blo 1072617 29391443 := bstep (se 1 (by rfl) ⟨22043582, by rfl⟩ : syracuseStep 29391443 = 44087165) B44087165
theorem B52363547 : Blo 1072617 52363547 := bstep (se 1 (by rfl) ⟨39272660, by rfl⟩ : syracuseStep 52363547 = 78545321) B78545321
theorem B19631231 : Blo 1072617 19631231 := bstep (se 1 (by rfl) ⟨14723423, by rfl⟩ : syracuseStep 19631231 = 29446847) B29446847
theorem B7442783 : Blo 1072617 7442783 := bstep (se 1 (by rfl) ⟨5582087, by rfl⟩ : syracuseStep 7442783 = 11164175) B11164175
theorem B1610153 : Blo 1072617 1610153 := bstep (se 2 (by rfl) ⟨603807, by rfl⟩ : syracuseStep 1610153 = 1207615) B1207615
theorem B4364783 : Blo 1072617 4364783 := bstep (se 1 (by rfl) ⟨3273587, by rfl⟩ : syracuseStep 4364783 = 6547175) B6547175
theorem B3448831 : Blo 1072617 3448831 := bstep (se 1 (by rfl) ⟨2586623, by rfl⟩ : syracuseStep 3448831 = 5173247) B5173247
theorem B9184103 : Blo 1072617 9184103 := bstep (se 1 (by rfl) ⟨6888077, by rfl⟩ : syracuseStep 9184103 = 13776155) B13776155
theorem B3486215 : Blo 1072617 3486215 := bstep (se 1 (by rfl) ⟨2614661, by rfl⟩ : syracuseStep 3486215 = 5229323) B5229323
theorem B2413907 : Blo 1072617 2413907 := bstep (se 1 (by rfl) ⟨1810430, by rfl⟩ : syracuseStep 2413907 = 3620861) B3620861
theorem B2416463 : Blo 1072617 2416463 := bstep (se 1 (by rfl) ⟨1812347, by rfl⟩ : syracuseStep 2416463 = 3624695) B3624695
theorem B18604201 : Blo 1072617 18604201 := bstep (se 2 (by rfl) ⟨6976575, by rfl⟩ : syracuseStep 18604201 = 13953151) B13953151
theorem B1073375 : Blo 1072617 1073375 := bstep (se 1 (by rfl) ⟨805031, by rfl⟩ : syracuseStep 1073375 = 1610063) B1610063
theorem B1074735 : Blo 1072617 1074735 := bstep (se 1 (by rfl) ⟨806051, by rfl⟩ : syracuseStep 1074735 = 1612103) B1612103
theorem B1075995 : Blo 1072617 1075995 := bstep (se 1 (by rfl) ⟨806996, by rfl⟩ : syracuseStep 1075995 = 1613993) B1613993
theorem B6978239 : Blo 1072617 6978239 := bstep (se 1 (by rfl) ⟨5233679, by rfl⟩ : syracuseStep 6978239 = 10467359) B10467359
theorem B19594295 : Blo 1072617 19594295 := bstep (se 1 (by rfl) ⟨14695721, by rfl⟩ : syracuseStep 19594295 = 29391443) B29391443
theorem B24805601 : Blo 1072617 24805601 := bstep (se 2 (by rfl) ⟨9302100, by rfl⟩ : syracuseStep 24805601 = 18604201) B18604201
theorem B1609271 : Blo 1072617 1609271 := bstep (se 1 (by rfl) ⟨1206953, by rfl⟩ : syracuseStep 1609271 = 2413907) B2413907
theorem B1610975 : Blo 1072617 1610975 := bstep (se 1 (by rfl) ⟨1208231, by rfl⟩ : syracuseStep 1610975 = 2416463) B2416463
theorem B4598441 : Blo 1072617 4598441 := bstep (se 2 (by rfl) ⟨1724415, by rfl⟩ : syracuseStep 4598441 = 3448831) B3448831
theorem B34909031 : Blo 1072617 34909031 := bstep (se 1 (by rfl) ⟨26181773, by rfl⟩ : syracuseStep 34909031 = 52363547) B52363547
theorem B13087487 : Blo 1072617 13087487 := bstep (se 1 (by rfl) ⟨9815615, by rfl⟩ : syracuseStep 13087487 = 19631231) B19631231
theorem B4961855 : Blo 1072617 4961855 := bstep (se 1 (by rfl) ⟨3721391, by rfl⟩ : syracuseStep 4961855 = 7442783) B7442783
theorem B13062863 : Blo 1072617 13062863 := bstep (se 1 (by rfl) ⟨9797147, by rfl⟩ : syracuseStep 13062863 = 19594295) B19594295
theorem B1073435 : Blo 1072617 1073435 := bstep (se 1 (by rfl) ⟨805076, by rfl⟩ : syracuseStep 1073435 = 1610153) B1610153
theorem B2909855 : Blo 1072617 2909855 := bstep (se 1 (by rfl) ⟨2182391, by rfl⟩ : syracuseStep 2909855 = 4364783) B4364783
theorem B6122735 : Blo 1072617 6122735 := bstep (se 1 (by rfl) ⟨4592051, by rfl⟩ : syracuseStep 6122735 = 9184103) B9184103
theorem B2324143 : Blo 1072617 2324143 := bstep (se 1 (by rfl) ⟨1743107, by rfl⟩ : syracuseStep 2324143 = 3486215) B3486215
theorem B4652159 : Blo 1072617 4652159 := bstep (se 1 (by rfl) ⟨3489119, by rfl⟩ : syracuseStep 4652159 = 6978239) B6978239
theorem B23272687 : Blo 1072617 23272687 := bstep (se 1 (by rfl) ⟨17454515, by rfl⟩ : syracuseStep 23272687 = 34909031) B34909031
theorem B8724991 : Blo 1072617 8724991 := bstep (se 1 (by rfl) ⟨6543743, by rfl⟩ : syracuseStep 8724991 = 13087487) B13087487
theorem B49623029 : Blo 1072617 49623029 := bstep (se 5 (by rfl) ⟨2326079, by rfl⟩ : syracuseStep 49623029 = 4652159) B4652159
theorem B3065627 : Blo 1072617 3065627 := bstep (se 1 (by rfl) ⟨2299220, by rfl⟩ : syracuseStep 3065627 = 4598441) B4598441
theorem B4081823 : Blo 1072617 4081823 := bstep (se 1 (by rfl) ⟨3061367, by rfl⟩ : syracuseStep 4081823 = 6122735) B6122735
theorem B3098857 : Blo 1072617 3098857 := bstep (se 2 (by rfl) ⟨1162071, by rfl⟩ : syracuseStep 3098857 = 2324143) B2324143
theorem B16537067 : Blo 1072617 16537067 := bstep (se 1 (by rfl) ⟨12402800, by rfl⟩ : syracuseStep 16537067 = 24805601) B24805601
theorem B1072847 : Blo 1072617 1072847 := bstep (se 1 (by rfl) ⟨804635, by rfl⟩ : syracuseStep 1072847 = 1609271) B1609271
theorem B8708575 : Blo 1072617 8708575 := bstep (se 1 (by rfl) ⟨6531431, by rfl⟩ : syracuseStep 8708575 = 13062863) B13062863
theorem B1073983 : Blo 1072617 1073983 := bstep (se 1 (by rfl) ⟨805487, by rfl⟩ : syracuseStep 1073983 = 1610975) B1610975
theorem B13231613 : Blo 1072617 13231613 := bstep (se 3 (by rfl) ⟨2480927, by rfl⟩ : syracuseStep 13231613 = 4961855) B4961855
theorem B7759613 : Blo 1072617 7759613 := bstep (se 3 (by rfl) ⟨1454927, by rfl⟩ : syracuseStep 7759613 = 2909855) B2909855
theorem B11633321 : Blo 1072617 11633321 := bstep (se 2 (by rfl) ⟨4362495, by rfl⟩ : syracuseStep 11633321 = 8724991) B8724991
theorem B2721215 : Blo 1072617 2721215 := bstep (se 1 (by rfl) ⟨2040911, by rfl⟩ : syracuseStep 2721215 = 4081823) B4081823
theorem B4131809 : Blo 1072617 4131809 := bstep (se 2 (by rfl) ⟨1549428, by rfl⟩ : syracuseStep 4131809 = 3098857) B3098857
theorem B11611433 : Blo 1072617 11611433 := bstep (se 2 (by rfl) ⟨4354287, by rfl⟩ : syracuseStep 11611433 = 8708575) B8708575
theorem B11024711 : Blo 1072617 11024711 := bstep (se 1 (by rfl) ⟨8268533, by rfl⟩ : syracuseStep 11024711 = 16537067) B16537067
theorem B8175005 : Blo 1072617 8175005 := bstep (se 3 (by rfl) ⟨1532813, by rfl⟩ : syracuseStep 8175005 = 3065627) B3065627
theorem B33082019 : Blo 1072617 33082019 := bstep (se 1 (by rfl) ⟨24811514, by rfl⟩ : syracuseStep 33082019 = 49623029) B49623029
theorem B35284301 : Blo 1072617 35284301 := bstep (se 3 (by rfl) ⟨6615806, by rfl⟩ : syracuseStep 35284301 = 13231613) B13231613
theorem B5173075 : Blo 1072617 5173075 := bstep (se 1 (by rfl) ⟨3879806, by rfl⟩ : syracuseStep 5173075 = 7759613) B7759613
theorem B31030249 : Blo 1072617 31030249 := bstep (se 2 (by rfl) ⟨11636343, by rfl⟩ : syracuseStep 31030249 = 23272687) B23272687
theorem B22054679 : Blo 1072617 22054679 := bstep (se 1 (by rfl) ⟨16541009, by rfl⟩ : syracuseStep 22054679 = 33082019) B33082019
theorem B2754539 : Blo 1072617 2754539 := bstep (se 1 (by rfl) ⟨2065904, by rfl⟩ : syracuseStep 2754539 = 4131809) B4131809
theorem B7740955 : Blo 1072617 7740955 := bstep (se 1 (by rfl) ⟨5805716, by rfl⟩ : syracuseStep 7740955 = 11611433) B11611433
theorem B7349807 : Blo 1072617 7349807 := bstep (se 1 (by rfl) ⟨5512355, by rfl⟩ : syracuseStep 7349807 = 11024711) B11024711
theorem B5450003 : Blo 1072617 5450003 := bstep (se 1 (by rfl) ⟨4087502, by rfl⟩ : syracuseStep 5450003 = 8175005) B8175005
theorem B1814143 : Blo 1072617 1814143 := bstep (se 1 (by rfl) ⟨1360607, by rfl⟩ : syracuseStep 1814143 = 2721215) B2721215
theorem B6897433 : Blo 1072617 6897433 := bstep (se 2 (by rfl) ⟨2586537, by rfl⟩ : syracuseStep 6897433 = 5173075) B5173075
theorem B41373665 : Blo 1072617 41373665 := bstep (se 2 (by rfl) ⟨15515124, by rfl⟩ : syracuseStep 41373665 = 31030249) B31030249
theorem B7755547 : Blo 1072617 7755547 := bstep (se 1 (by rfl) ⟨5816660, by rfl⟩ : syracuseStep 7755547 = 11633321) B11633321
theorem B23522867 : Blo 1072617 23522867 := bstep (se 1 (by rfl) ⟨17642150, by rfl⟩ : syracuseStep 23522867 = 35284301) B35284301
theorem B1836359 : Blo 1072617 1836359 := bstep (se 1 (by rfl) ⟨1377269, by rfl⟩ : syracuseStep 1836359 = 2754539) B2754539
theorem B250910581 : Blo 1072617 250910581 := bstep (se 5 (by rfl) ⟨11761433, by rfl⟩ : syracuseStep 250910581 = 23522867) B23522867
theorem B4899871 : Blo 1072617 4899871 := bstep (se 1 (by rfl) ⟨3674903, by rfl⟩ : syracuseStep 4899871 = 7349807) B7349807
theorem B10340729 : Blo 1072617 10340729 := bstep (se 2 (by rfl) ⟨3877773, by rfl⟩ : syracuseStep 10340729 = 7755547) B7755547
theorem B9196577 : Blo 1072617 9196577 := bstep (se 2 (by rfl) ⟨3448716, by rfl⟩ : syracuseStep 9196577 = 6897433) B6897433
theorem B14703119 : Blo 1072617 14703119 := bstep (se 1 (by rfl) ⟨11027339, by rfl⟩ : syracuseStep 14703119 = 22054679) B22054679
theorem B27582443 : Blo 1072617 27582443 := bstep (se 1 (by rfl) ⟨20686832, by rfl⟩ : syracuseStep 27582443 = 41373665) B41373665
theorem B2418857 : Blo 1072617 2418857 := bstep (se 2 (by rfl) ⟨907071, by rfl⟩ : syracuseStep 2418857 = 1814143) B1814143
theorem B3633335 : Blo 1072617 3633335 := bstep (se 1 (by rfl) ⟨2725001, by rfl⟩ : syracuseStep 3633335 = 5450003) B5450003
theorem B10321273 : Blo 1072617 10321273 := bstep (se 2 (by rfl) ⟨3870477, by rfl⟩ : syracuseStep 10321273 = 7740955) B7740955
theorem B6131051 : Blo 1072617 6131051 := bstep (se 1 (by rfl) ⟨4598288, by rfl⟩ : syracuseStep 6131051 = 9196577) B9196577
theorem B9802079 : Blo 1072617 9802079 := bstep (se 1 (by rfl) ⟨7351559, by rfl⟩ : syracuseStep 9802079 = 14703119) B14703119
theorem B18388295 : Blo 1072617 18388295 := bstep (se 1 (by rfl) ⟨13791221, by rfl⟩ : syracuseStep 18388295 = 27582443) B27582443
theorem B1612571 : Blo 1072617 1612571 := bstep (se 1 (by rfl) ⟨1209428, by rfl⟩ : syracuseStep 1612571 = 2418857) B2418857
theorem B1224239 : Blo 1072617 1224239 := bstep (se 1 (by rfl) ⟨918179, by rfl⟩ : syracuseStep 1224239 = 1836359) B1836359
theorem B6893819 : Blo 1072617 6893819 := bstep (se 1 (by rfl) ⟨5170364, by rfl⟩ : syracuseStep 6893819 = 10340729) B10340729
theorem B26132645 : Blo 1072617 26132645 := bstep (se 4 (by rfl) ⟨2449935, by rfl⟩ : syracuseStep 26132645 = 4899871) B4899871
theorem B334547441 : Blo 1072617 334547441 := bstep (se 2 (by rfl) ⟨125455290, by rfl⟩ : syracuseStep 334547441 = 250910581) B250910581
theorem B2422223 : Blo 1072617 2422223 := bstep (se 1 (by rfl) ⟨1816667, by rfl⟩ : syracuseStep 2422223 = 3633335) B3633335
theorem B13761697 : Blo 1072617 13761697 := bstep (se 2 (by rfl) ⟨5160636, by rfl⟩ : syracuseStep 13761697 = 10321273) B10321273
theorem B12258863 : Blo 1072617 12258863 := bstep (se 1 (by rfl) ⟨9194147, by rfl⟩ : syracuseStep 12258863 = 18388295) B18388295
theorem B4595879 : Blo 1072617 4595879 := bstep (se 1 (by rfl) ⟨3446909, by rfl⟩ : syracuseStep 4595879 = 6893819) B6893819
theorem B1614815 : Blo 1072617 1614815 := bstep (se 1 (by rfl) ⟨1211111, by rfl⟩ : syracuseStep 1614815 = 2422223) B2422223
theorem B223031627 : Blo 1072617 223031627 := bstep (se 1 (by rfl) ⟨167273720, by rfl⟩ : syracuseStep 223031627 = 334547441) B334547441
theorem B6534719 : Blo 1072617 6534719 := bstep (se 1 (by rfl) ⟨4901039, by rfl⟩ : syracuseStep 6534719 = 9802079) B9802079
theorem B3264637 : Blo 1072617 3264637 := bstep (se 3 (by rfl) ⟨612119, by rfl⟩ : syracuseStep 3264637 = 1224239) B1224239
theorem B17421763 : Blo 1072617 17421763 := bstep (se 1 (by rfl) ⟨13066322, by rfl⟩ : syracuseStep 17421763 = 26132645) B26132645
theorem B4087367 : Blo 1072617 4087367 := bstep (se 1 (by rfl) ⟨3065525, by rfl⟩ : syracuseStep 4087367 = 6131051) B6131051
theorem B1075047 : Blo 1072617 1075047 := bstep (se 1 (by rfl) ⟨806285, by rfl⟩ : syracuseStep 1075047 = 1612571) B1612571
theorem B18348929 : Blo 1072617 18348929 := bstep (se 2 (by rfl) ⟨6880848, by rfl⟩ : syracuseStep 18348929 = 13761697) B13761697
theorem B2724911 : Blo 1072617 2724911 := bstep (se 1 (by rfl) ⟨2043683, by rfl⟩ : syracuseStep 2724911 = 4087367) B4087367
theorem B12232619 : Blo 1072617 12232619 := bstep (se 1 (by rfl) ⟨9174464, by rfl⟩ : syracuseStep 12232619 = 18348929) B18348929
theorem B8172575 : Blo 1072617 8172575 := bstep (se 1 (by rfl) ⟨6129431, by rfl⟩ : syracuseStep 8172575 = 12258863) B12258863
theorem B3063919 : Blo 1072617 3063919 := bstep (se 1 (by rfl) ⟨2297939, by rfl⟩ : syracuseStep 3063919 = 4595879) B4595879
theorem B148687751 : Blo 1072617 148687751 := bstep (se 1 (by rfl) ⟨111515813, by rfl⟩ : syracuseStep 148687751 = 223031627) B223031627
theorem B4352849 : Blo 1072617 4352849 := bstep (se 2 (by rfl) ⟨1632318, by rfl⟩ : syracuseStep 4352849 = 3264637) B3264637
theorem B1076543 : Blo 1072617 1076543 := bstep (se 1 (by rfl) ⟨807407, by rfl⟩ : syracuseStep 1076543 = 1614815) B1614815
theorem B23229017 : Blo 1072617 23229017 := bstep (se 2 (by rfl) ⟨8710881, by rfl⟩ : syracuseStep 23229017 = 17421763) B17421763
theorem B4356479 : Blo 1072617 4356479 := bstep (se 1 (by rfl) ⟨3267359, by rfl⟩ : syracuseStep 4356479 = 6534719) B6534719
theorem B99125167 : Blo 1072617 99125167 := bstep (se 1 (by rfl) ⟨74343875, by rfl⟩ : syracuseStep 99125167 = 148687751) B148687751
theorem B5448383 : Blo 1072617 5448383 := bstep (se 1 (by rfl) ⟨4086287, by rfl⟩ : syracuseStep 5448383 = 8172575) B8172575
theorem B1816607 : Blo 1072617 1816607 := bstep (se 1 (by rfl) ⟨1362455, by rfl⟩ : syracuseStep 1816607 = 2724911) B2724911
theorem B2901899 : Blo 1072617 2901899 := bstep (se 1 (by rfl) ⟨2176424, by rfl⟩ : syracuseStep 2901899 = 4352849) B4352849
theorem B15486011 : Blo 1072617 15486011 := bstep (se 1 (by rfl) ⟨11614508, by rfl⟩ : syracuseStep 15486011 = 23229017) B23229017
theorem B2904319 : Blo 1072617 2904319 := bstep (se 1 (by rfl) ⟨2178239, by rfl⟩ : syracuseStep 2904319 = 4356479) B4356479
theorem B4085225 : Blo 1072617 4085225 := bstep (se 2 (by rfl) ⟨1531959, by rfl⟩ : syracuseStep 4085225 = 3063919) B3063919
theorem B8155079 : Blo 1072617 8155079 := bstep (se 1 (by rfl) ⟨6116309, by rfl⟩ : syracuseStep 8155079 = 12232619) B12232619
theorem B1934599 : Blo 1072617 1934599 := bstep (se 1 (by rfl) ⟨1450949, by rfl⟩ : syracuseStep 1934599 = 2901899) B2901899
theorem B10324007 : Blo 1072617 10324007 := bstep (se 1 (by rfl) ⟨7743005, by rfl⟩ : syracuseStep 10324007 = 15486011) B15486011
theorem B2723483 : Blo 1072617 2723483 := bstep (se 1 (by rfl) ⟨2042612, by rfl⟩ : syracuseStep 2723483 = 4085225) B4085225
theorem B132166889 : Blo 1072617 132166889 := bstep (se 2 (by rfl) ⟨49562583, by rfl⟩ : syracuseStep 132166889 = 99125167) B99125167
theorem B15489701 : Blo 1072617 15489701 := bstep (se 4 (by rfl) ⟨1452159, by rfl⟩ : syracuseStep 15489701 = 2904319) B2904319
theorem B3632255 : Blo 1072617 3632255 := bstep (se 1 (by rfl) ⟨2724191, by rfl⟩ : syracuseStep 3632255 = 5448383) B5448383
theorem B5436719 : Blo 1072617 5436719 := bstep (se 1 (by rfl) ⟨4077539, by rfl⟩ : syracuseStep 5436719 = 8155079) B8155079
theorem B1211071 : Blo 1072617 1211071 := bstep (se 1 (by rfl) ⟨908303, by rfl⟩ : syracuseStep 1211071 = 1816607) B1816607
theorem B6882671 : Blo 1072617 6882671 := bstep (se 1 (by rfl) ⟨5162003, by rfl⟩ : syracuseStep 6882671 = 10324007) B10324007
theorem B10326467 : Blo 1072617 10326467 := bstep (se 1 (by rfl) ⟨7744850, by rfl⟩ : syracuseStep 10326467 = 15489701) B15489701
theorem B1614761 : Blo 1072617 1614761 := bstep (se 2 (by rfl) ⟨605535, by rfl⟩ : syracuseStep 1614761 = 1211071) B1211071
theorem B1815655 : Blo 1072617 1815655 := bstep (se 1 (by rfl) ⟨1361741, by rfl⟩ : syracuseStep 1815655 = 2723483) B2723483
theorem B3624479 : Blo 1072617 3624479 := bstep (se 1 (by rfl) ⟨2718359, by rfl⟩ : syracuseStep 3624479 = 5436719) B5436719
theorem B2579465 : Blo 1072617 2579465 := bstep (se 2 (by rfl) ⟨967299, by rfl⟩ : syracuseStep 2579465 = 1934599) B1934599
theorem B2421503 : Blo 1072617 2421503 := bstep (se 1 (by rfl) ⟨1816127, by rfl⟩ : syracuseStep 2421503 = 3632255) B3632255
theorem B88111259 : Blo 1072617 88111259 := bstep (se 1 (by rfl) ⟨66083444, by rfl⟩ : syracuseStep 88111259 = 132166889) B132166889
theorem B4588447 : Blo 1072617 4588447 := bstep (se 1 (by rfl) ⟨3441335, by rfl⟩ : syracuseStep 4588447 = 6882671) B6882671
theorem B6884311 : Blo 1072617 6884311 := bstep (se 1 (by rfl) ⟨5163233, by rfl⟩ : syracuseStep 6884311 = 10326467) B10326467
theorem B1614335 : Blo 1072617 1614335 := bstep (se 1 (by rfl) ⟨1210751, by rfl⟩ : syracuseStep 1614335 = 2421503) B2421503
theorem B1719643 : Blo 1072617 1719643 := bstep (se 1 (by rfl) ⟨1289732, by rfl⟩ : syracuseStep 1719643 = 2579465) B2579465
theorem B58740839 : Blo 1072617 58740839 := bstep (se 1 (by rfl) ⟨44055629, by rfl⟩ : syracuseStep 58740839 = 88111259) B88111259
theorem B2416319 : Blo 1072617 2416319 := bstep (se 1 (by rfl) ⟨1812239, by rfl⟩ : syracuseStep 2416319 = 3624479) B3624479
theorem B1076507 : Blo 1072617 1076507 := bstep (se 1 (by rfl) ⟨807380, by rfl⟩ : syracuseStep 1076507 = 1614761) B1614761
theorem B2420873 : Blo 1072617 2420873 := bstep (se 2 (by rfl) ⟨907827, by rfl⟩ : syracuseStep 2420873 = 1815655) B1815655
theorem B39160559 : Blo 1072617 39160559 := bstep (se 1 (by rfl) ⟨29370419, by rfl⟩ : syracuseStep 39160559 = 58740839) B58740839
theorem B9179081 : Blo 1072617 9179081 := bstep (se 2 (by rfl) ⟨3442155, by rfl⟩ : syracuseStep 9179081 = 6884311) B6884311
theorem B1610879 : Blo 1072617 1610879 := bstep (se 1 (by rfl) ⟨1208159, by rfl⟩ : syracuseStep 1610879 = 2416319) B2416319
theorem B1613915 : Blo 1072617 1613915 := bstep (se 1 (by rfl) ⟨1210436, by rfl⟩ : syracuseStep 1613915 = 2420873) B2420873
theorem B6117929 : Blo 1072617 6117929 := bstep (se 2 (by rfl) ⟨2294223, by rfl⟩ : syracuseStep 6117929 = 4588447) B4588447
theorem B1076223 : Blo 1072617 1076223 := bstep (se 1 (by rfl) ⟨807167, by rfl⟩ : syracuseStep 1076223 = 1614335) B1614335
theorem B2292857 : Blo 1072617 2292857 := bstep (se 2 (by rfl) ⟨859821, by rfl⟩ : syracuseStep 2292857 = 1719643) B1719643
theorem B4078619 : Blo 1072617 4078619 := bstep (se 1 (by rfl) ⟨3058964, by rfl⟩ : syracuseStep 4078619 = 6117929) B6117929
theorem B1528571 : Blo 1072617 1528571 := bstep (se 1 (by rfl) ⟨1146428, by rfl⟩ : syracuseStep 1528571 = 2292857) B2292857
theorem B26107039 : Blo 1072617 26107039 := bstep (se 1 (by rfl) ⟨19580279, by rfl⟩ : syracuseStep 26107039 = 39160559) B39160559
theorem B6119387 : Blo 1072617 6119387 := bstep (se 1 (by rfl) ⟨4589540, by rfl⟩ : syracuseStep 6119387 = 9179081) B9179081
theorem B1073919 : Blo 1072617 1073919 := bstep (se 1 (by rfl) ⟨805439, by rfl⟩ : syracuseStep 1073919 = 1610879) B1610879
theorem B1075943 : Blo 1072617 1075943 := bstep (se 1 (by rfl) ⟨806957, by rfl⟩ : syracuseStep 1075943 = 1613915) B1613915
theorem B139237541 : Blo 1072617 139237541 := bstep (se 4 (by rfl) ⟨13053519, by rfl⟩ : syracuseStep 139237541 = 26107039) B26107039
theorem B4076189 : Blo 1072617 4076189 := bstep (se 3 (by rfl) ⟨764285, by rfl⟩ : syracuseStep 4076189 = 1528571) B1528571
theorem B4079591 : Blo 1072617 4079591 := bstep (se 1 (by rfl) ⟨3059693, by rfl⟩ : syracuseStep 4079591 = 6119387) B6119387
theorem B2719079 : Blo 1072617 2719079 := bstep (se 1 (by rfl) ⟨2039309, by rfl⟩ : syracuseStep 2719079 = 4078619) B4078619
theorem B1812719 : Blo 1072617 1812719 := bstep (se 1 (by rfl) ⟨1359539, by rfl⟩ : syracuseStep 1812719 = 2719079) B2719079
theorem B92825027 : Blo 1072617 92825027 := bstep (se 1 (by rfl) ⟨69618770, by rfl⟩ : syracuseStep 92825027 = 139237541) B139237541
theorem B2717459 : Blo 1072617 2717459 := bstep (se 1 (by rfl) ⟨2038094, by rfl⟩ : syracuseStep 2717459 = 4076189) B4076189
theorem B2719727 : Blo 1072617 2719727 := bstep (se 1 (by rfl) ⟨2039795, by rfl⟩ : syracuseStep 2719727 = 4079591) B4079591
theorem B1811639 : Blo 1072617 1811639 := bstep (se 1 (by rfl) ⟨1358729, by rfl⟩ : syracuseStep 1811639 = 2717459) B2717459
theorem B1813151 : Blo 1072617 1813151 := bstep (se 1 (by rfl) ⟨1359863, by rfl⟩ : syracuseStep 1813151 = 2719727) B2719727
theorem B61883351 : Blo 1072617 61883351 := bstep (se 1 (by rfl) ⟨46412513, by rfl⟩ : syracuseStep 61883351 = 92825027) B92825027
theorem B1208479 : Blo 1072617 1208479 := bstep (se 1 (by rfl) ⟨906359, by rfl⟩ : syracuseStep 1208479 = 1812719) B1812719
theorem B41255567 : Blo 1072617 41255567 := bstep (se 1 (by rfl) ⟨30941675, by rfl⟩ : syracuseStep 41255567 = 61883351) B61883351
theorem B1611305 : Blo 1072617 1611305 := bstep (se 2 (by rfl) ⟨604239, by rfl⟩ : syracuseStep 1611305 = 1208479) B1208479
theorem B1207759 : Blo 1072617 1207759 := bstep (se 1 (by rfl) ⟨905819, by rfl⟩ : syracuseStep 1207759 = 1811639) B1811639
theorem B1208767 : Blo 1072617 1208767 := bstep (se 1 (by rfl) ⟨906575, by rfl⟩ : syracuseStep 1208767 = 1813151) B1813151
theorem B1610345 : Blo 1072617 1610345 := bstep (se 2 (by rfl) ⟨603879, by rfl⟩ : syracuseStep 1610345 = 1207759) B1207759
theorem B1611689 : Blo 1072617 1611689 := bstep (se 2 (by rfl) ⟨604383, by rfl⟩ : syracuseStep 1611689 = 1208767) B1208767
theorem B27503711 : Blo 1072617 27503711 := bstep (se 1 (by rfl) ⟨20627783, by rfl⟩ : syracuseStep 27503711 = 41255567) B41255567
theorem B1074203 : Blo 1072617 1074203 := bstep (se 1 (by rfl) ⟨805652, by rfl⟩ : syracuseStep 1074203 = 1611305) B1611305
theorem B18335807 : Blo 1072617 18335807 := bstep (se 1 (by rfl) ⟨13751855, by rfl⟩ : syracuseStep 18335807 = 27503711) B27503711
theorem B1073563 : Blo 1072617 1073563 := bstep (se 1 (by rfl) ⟨805172, by rfl⟩ : syracuseStep 1073563 = 1610345) B1610345
theorem B1074459 : Blo 1072617 1074459 := bstep (se 1 (by rfl) ⟨805844, by rfl⟩ : syracuseStep 1074459 = 1611689) B1611689
theorem B12223871 : Blo 1072617 12223871 := bstep (se 1 (by rfl) ⟨9167903, by rfl⟩ : syracuseStep 12223871 = 18335807) B18335807
theorem B8149247 : Blo 1072617 8149247 := bstep (se 1 (by rfl) ⟨6111935, by rfl⟩ : syracuseStep 8149247 = 12223871) B12223871
theorem B5432831 : Blo 1072617 5432831 := bstep (se 1 (by rfl) ⟨4074623, by rfl⟩ : syracuseStep 5432831 = 8149247) B8149247
theorem B3621887 : Blo 1072617 3621887 := bstep (se 1 (by rfl) ⟨2716415, by rfl⟩ : syracuseStep 3621887 = 5432831) B5432831
theorem B2414591 : Blo 1072617 2414591 := bstep (se 1 (by rfl) ⟨1810943, by rfl⟩ : syracuseStep 2414591 = 3621887) B3621887
theorem B1609727 : Blo 1072617 1609727 := bstep (se 1 (by rfl) ⟨1207295, by rfl⟩ : syracuseStep 1609727 = 2414591) B2414591
theorem B1073151 : Blo 1072617 1073151 := bstep (se 1 (by rfl) ⟨804863, by rfl⟩ : syracuseStep 1073151 = 1609727) B1609727

theorem C0 (j : ℕ) (h1 : 268154 ≤ j) (h2 : j ≤ 268853) : Blo 1072617 (4 * j + 3) := by
  interval_cases j
  · exact B1072619
  · exact B1072623
  · exact B1072627
  · exact B1072631
  · exact B1072635
  · exact B1072639
  · exact B1072643
  · exact B1072647
  · exact B1072651
  · exact B1072655
  · exact B1072659
  · exact B1072663
  · exact B1072667
  · exact B1072671
  · exact B1072675
  · exact B1072679
  · exact B1072683
  · exact B1072687
  · exact B1072691
  · exact B1072695
  · exact B1072699
  · exact B1072703
  · exact B1072707
  · exact B1072711
  · exact B1072715
  · exact B1072719
  · exact B1072723
  · exact B1072727
  · exact B1072731
  · exact B1072735
  · exact B1072739
  · exact B1072743
  · exact B1072747
  · exact B1072751
  · exact B1072755
  · exact B1072759
  · exact B1072763
  · exact B1072767
  · exact B1072771
  · exact B1072775
  · exact B1072779
  · exact B1072783
  · exact B1072787
  · exact B1072791
  · exact B1072795
  · exact B1072799
  · exact B1072803
  · exact B1072807
  · exact B1072811
  · exact B1072815
  · exact B1072819
  · exact B1072823
  · exact B1072827
  · exact B1072831
  · exact B1072835
  · exact B1072839
  · exact B1072843
  · exact B1072847
  · exact B1072851
  · exact B1072855
  · exact B1072859
  · exact B1072863
  · exact B1072867
  · exact B1072871
  · exact B1072875
  · exact B1072879
  · exact B1072883
  · exact B1072887
  · exact B1072891
  · exact B1072895
  · exact B1072899
  · exact B1072903
  · exact B1072907
  · exact B1072911
  · exact B1072915
  · exact B1072919
  · exact B1072923
  · exact B1072927
  · exact B1072931
  · exact B1072935
  · exact B1072939
  · exact B1072943
  · exact B1072947
  · exact B1072951
  · exact B1072955
  · exact B1072959
  · exact B1072963
  · exact B1072967
  · exact B1072971
  · exact B1072975
  · exact B1072979
  · exact B1072983
  · exact B1072987
  · exact B1072991
  · exact B1072995
  · exact B1072999
  · exact B1073003
  · exact B1073007
  · exact B1073011
  · exact B1073015
  · exact B1073019
  · exact B1073023
  · exact B1073027
  · exact B1073031
  · exact B1073035
  · exact B1073039
  · exact B1073043
  · exact B1073047
  · exact B1073051
  · exact B1073055
  · exact B1073059
  · exact B1073063
  · exact B1073067
  · exact B1073071
  · exact B1073075
  · exact B1073079
  · exact B1073083
  · exact B1073087
  · exact B1073091
  · exact B1073095
  · exact B1073099
  · exact B1073103
  · exact B1073107
  · exact B1073111
  · exact B1073115
  · exact B1073119
  · exact B1073123
  · exact B1073127
  · exact B1073131
  · exact B1073135
  · exact B1073139
  · exact B1073143
  · exact B1073147
  · exact B1073151
  · exact B1073155
  · exact B1073159
  · exact B1073163
  · exact B1073167
  · exact B1073171
  · exact B1073175
  · exact B1073179
  · exact B1073183
  · exact B1073187
  · exact B1073191
  · exact B1073195
  · exact B1073199
  · exact B1073203
  · exact B1073207
  · exact B1073211
  · exact B1073215
  · exact B1073219
  · exact B1073223
  · exact B1073227
  · exact B1073231
  · exact B1073235
  · exact B1073239
  · exact B1073243
  · exact B1073247
  · exact B1073251
  · exact B1073255
  · exact B1073259
  · exact B1073263
  · exact B1073267
  · exact B1073271
  · exact B1073275
  · exact B1073279
  · exact B1073283
  · exact B1073287
  · exact B1073291
  · exact B1073295
  · exact B1073299
  · exact B1073303
  · exact B1073307
  · exact B1073311
  · exact B1073315
  · exact B1073319
  · exact B1073323
  · exact B1073327
  · exact B1073331
  · exact B1073335
  · exact B1073339
  · exact B1073343
  · exact B1073347
  · exact B1073351
  · exact B1073355
  · exact B1073359
  · exact B1073363
  · exact B1073367
  · exact B1073371
  · exact B1073375
  · exact B1073379
  · exact B1073383
  · exact B1073387
  · exact B1073391
  · exact B1073395
  · exact B1073399
  · exact B1073403
  · exact B1073407
  · exact B1073411
  · exact B1073415
  · exact B1073419
  · exact B1073423
  · exact B1073427
  · exact B1073431
  · exact B1073435
  · exact B1073439
  · exact B1073443
  · exact B1073447
  · exact B1073451
  · exact B1073455
  · exact B1073459
  · exact B1073463
  · exact B1073467
  · exact B1073471
  · exact B1073475
  · exact B1073479
  · exact B1073483
  · exact B1073487
  · exact B1073491
  · exact B1073495
  · exact B1073499
  · exact B1073503
  · exact B1073507
  · exact B1073511
  · exact B1073515
  · exact B1073519
  · exact B1073523
  · exact B1073527
  · exact B1073531
  · exact B1073535
  · exact B1073539
  · exact B1073543
  · exact B1073547
  · exact B1073551
  · exact B1073555
  · exact B1073559
  · exact B1073563
  · exact B1073567
  · exact B1073571
  · exact B1073575
  · exact B1073579
  · exact B1073583
  · exact B1073587
  · exact B1073591
  · exact B1073595
  · exact B1073599
  · exact B1073603
  · exact B1073607
  · exact B1073611
  · exact B1073615
  · exact B1073619
  · exact B1073623
  · exact B1073627
  · exact B1073631
  · exact B1073635
  · exact B1073639
  · exact B1073643
  · exact B1073647
  · exact B1073651
  · exact B1073655
  · exact B1073659
  · exact B1073663
  · exact B1073667
  · exact B1073671
  · exact B1073675
  · exact B1073679
  · exact B1073683
  · exact B1073687
  · exact B1073691
  · exact B1073695
  · exact B1073699
  · exact B1073703
  · exact B1073707
  · exact B1073711
  · exact B1073715
  · exact B1073719
  · exact B1073723
  · exact B1073727
  · exact B1073731
  · exact B1073735
  · exact B1073739
  · exact B1073743
  · exact B1073747
  · exact B1073751
  · exact B1073755
  · exact B1073759
  · exact B1073763
  · exact B1073767
  · exact B1073771
  · exact B1073775
  · exact B1073779
  · exact B1073783
  · exact B1073787
  · exact B1073791
  · exact B1073795
  · exact B1073799
  · exact B1073803
  · exact B1073807
  · exact B1073811
  · exact B1073815
  · exact B1073819
  · exact B1073823
  · exact B1073827
  · exact B1073831
  · exact B1073835
  · exact B1073839
  · exact B1073843
  · exact B1073847
  · exact B1073851
  · exact B1073855
  · exact B1073859
  · exact B1073863
  · exact B1073867
  · exact B1073871
  · exact B1073875
  · exact B1073879
  · exact B1073883
  · exact B1073887
  · exact B1073891
  · exact B1073895
  · exact B1073899
  · exact B1073903
  · exact B1073907
  · exact B1073911
  · exact B1073915
  · exact B1073919
  · exact B1073923
  · exact B1073927
  · exact B1073931
  · exact B1073935
  · exact B1073939
  · exact B1073943
  · exact B1073947
  · exact B1073951
  · exact B1073955
  · exact B1073959
  · exact B1073963
  · exact B1073967
  · exact B1073971
  · exact B1073975
  · exact B1073979
  · exact B1073983
  · exact B1073987
  · exact B1073991
  · exact B1073995
  · exact B1073999
  · exact B1074003
  · exact B1074007
  · exact B1074011
  · exact B1074015
  · exact B1074019
  · exact B1074023
  · exact B1074027
  · exact B1074031
  · exact B1074035
  · exact B1074039
  · exact B1074043
  · exact B1074047
  · exact B1074051
  · exact B1074055
  · exact B1074059
  · exact B1074063
  · exact B1074067
  · exact B1074071
  · exact B1074075
  · exact B1074079
  · exact B1074083
  · exact B1074087
  · exact B1074091
  · exact B1074095
  · exact B1074099
  · exact B1074103
  · exact B1074107
  · exact B1074111
  · exact B1074115
  · exact B1074119
  · exact B1074123
  · exact B1074127
  · exact B1074131
  · exact B1074135
  · exact B1074139
  · exact B1074143
  · exact B1074147
  · exact B1074151
  · exact B1074155
  · exact B1074159
  · exact B1074163
  · exact B1074167
  · exact B1074171
  · exact B1074175
  · exact B1074179
  · exact B1074183
  · exact B1074187
  · exact B1074191
  · exact B1074195
  · exact B1074199
  · exact B1074203
  · exact B1074207
  · exact B1074211
  · exact B1074215
  · exact B1074219
  · exact B1074223
  · exact B1074227
  · exact B1074231
  · exact B1074235
  · exact B1074239
  · exact B1074243
  · exact B1074247
  · exact B1074251
  · exact B1074255
  · exact B1074259
  · exact B1074263
  · exact B1074267
  · exact B1074271
  · exact B1074275
  · exact B1074279
  · exact B1074283
  · exact B1074287
  · exact B1074291
  · exact B1074295
  · exact B1074299
  · exact B1074303
  · exact B1074307
  · exact B1074311
  · exact B1074315
  · exact B1074319
  · exact B1074323
  · exact B1074327
  · exact B1074331
  · exact B1074335
  · exact B1074339
  · exact B1074343
  · exact B1074347
  · exact B1074351
  · exact B1074355
  · exact B1074359
  · exact B1074363
  · exact B1074367
  · exact B1074371
  · exact B1074375
  · exact B1074379
  · exact B1074383
  · exact B1074387
  · exact B1074391
  · exact B1074395
  · exact B1074399
  · exact B1074403
  · exact B1074407
  · exact B1074411
  · exact B1074415
  · exact B1074419
  · exact B1074423
  · exact B1074427
  · exact B1074431
  · exact B1074435
  · exact B1074439
  · exact B1074443
  · exact B1074447
  · exact B1074451
  · exact B1074455
  · exact B1074459
  · exact B1074463
  · exact B1074467
  · exact B1074471
  · exact B1074475
  · exact B1074479
  · exact B1074483
  · exact B1074487
  · exact B1074491
  · exact B1074495
  · exact B1074499
  · exact B1074503
  · exact B1074507
  · exact B1074511
  · exact B1074515
  · exact B1074519
  · exact B1074523
  · exact B1074527
  · exact B1074531
  · exact B1074535
  · exact B1074539
  · exact B1074543
  · exact B1074547
  · exact B1074551
  · exact B1074555
  · exact B1074559
  · exact B1074563
  · exact B1074567
  · exact B1074571
  · exact B1074575
  · exact B1074579
  · exact B1074583
  · exact B1074587
  · exact B1074591
  · exact B1074595
  · exact B1074599
  · exact B1074603
  · exact B1074607
  · exact B1074611
  · exact B1074615
  · exact B1074619
  · exact B1074623
  · exact B1074627
  · exact B1074631
  · exact B1074635
  · exact B1074639
  · exact B1074643
  · exact B1074647
  · exact B1074651
  · exact B1074655
  · exact B1074659
  · exact B1074663
  · exact B1074667
  · exact B1074671
  · exact B1074675
  · exact B1074679
  · exact B1074683
  · exact B1074687
  · exact B1074691
  · exact B1074695
  · exact B1074699
  · exact B1074703
  · exact B1074707
  · exact B1074711
  · exact B1074715
  · exact B1074719
  · exact B1074723
  · exact B1074727
  · exact B1074731
  · exact B1074735
  · exact B1074739
  · exact B1074743
  · exact B1074747
  · exact B1074751
  · exact B1074755
  · exact B1074759
  · exact B1074763
  · exact B1074767
  · exact B1074771
  · exact B1074775
  · exact B1074779
  · exact B1074783
  · exact B1074787
  · exact B1074791
  · exact B1074795
  · exact B1074799
  · exact B1074803
  · exact B1074807
  · exact B1074811
  · exact B1074815
  · exact B1074819
  · exact B1074823
  · exact B1074827
  · exact B1074831
  · exact B1074835
  · exact B1074839
  · exact B1074843
  · exact B1074847
  · exact B1074851
  · exact B1074855
  · exact B1074859
  · exact B1074863
  · exact B1074867
  · exact B1074871
  · exact B1074875
  · exact B1074879
  · exact B1074883
  · exact B1074887
  · exact B1074891
  · exact B1074895
  · exact B1074899
  · exact B1074903
  · exact B1074907
  · exact B1074911
  · exact B1074915
  · exact B1074919
  · exact B1074923
  · exact B1074927
  · exact B1074931
  · exact B1074935
  · exact B1074939
  · exact B1074943
  · exact B1074947
  · exact B1074951
  · exact B1074955
  · exact B1074959
  · exact B1074963
  · exact B1074967
  · exact B1074971
  · exact B1074975
  · exact B1074979
  · exact B1074983
  · exact B1074987
  · exact B1074991
  · exact B1074995
  · exact B1074999
  · exact B1075003
  · exact B1075007
  · exact B1075011
  · exact B1075015
  · exact B1075019
  · exact B1075023
  · exact B1075027
  · exact B1075031
  · exact B1075035
  · exact B1075039
  · exact B1075043
  · exact B1075047
  · exact B1075051
  · exact B1075055
  · exact B1075059
  · exact B1075063
  · exact B1075067
  · exact B1075071
  · exact B1075075
  · exact B1075079
  · exact B1075083
  · exact B1075087
  · exact B1075091
  · exact B1075095
  · exact B1075099
  · exact B1075103
  · exact B1075107
  · exact B1075111
  · exact B1075115
  · exact B1075119
  · exact B1075123
  · exact B1075127
  · exact B1075131
  · exact B1075135
  · exact B1075139
  · exact B1075143
  · exact B1075147
  · exact B1075151
  · exact B1075155
  · exact B1075159
  · exact B1075163
  · exact B1075167
  · exact B1075171
  · exact B1075175
  · exact B1075179
  · exact B1075183
  · exact B1075187
  · exact B1075191
  · exact B1075195
  · exact B1075199
  · exact B1075203
  · exact B1075207
  · exact B1075211
  · exact B1075215
  · exact B1075219
  · exact B1075223
  · exact B1075227
  · exact B1075231
  · exact B1075235
  · exact B1075239
  · exact B1075243
  · exact B1075247
  · exact B1075251
  · exact B1075255
  · exact B1075259
  · exact B1075263
  · exact B1075267
  · exact B1075271
  · exact B1075275
  · exact B1075279
  · exact B1075283
  · exact B1075287
  · exact B1075291
  · exact B1075295
  · exact B1075299
  · exact B1075303
  · exact B1075307
  · exact B1075311
  · exact B1075315
  · exact B1075319
  · exact B1075323
  · exact B1075327
  · exact B1075331
  · exact B1075335
  · exact B1075339
  · exact B1075343
  · exact B1075347
  · exact B1075351
  · exact B1075355
  · exact B1075359
  · exact B1075363
  · exact B1075367
  · exact B1075371
  · exact B1075375
  · exact B1075379
  · exact B1075383
  · exact B1075387
  · exact B1075391
  · exact B1075395
  · exact B1075399
  · exact B1075403
  · exact B1075407
  · exact B1075411
  · exact B1075415

theorem C1 (j : ℕ) (h1 : 268854 ≤ j) (h2 : j ≤ 269153) : Blo 1072617 (4 * j + 3) := by
  interval_cases j
  · exact B1075419
  · exact B1075423
  · exact B1075427
  · exact B1075431
  · exact B1075435
  · exact B1075439
  · exact B1075443
  · exact B1075447
  · exact B1075451
  · exact B1075455
  · exact B1075459
  · exact B1075463
  · exact B1075467
  · exact B1075471
  · exact B1075475
  · exact B1075479
  · exact B1075483
  · exact B1075487
  · exact B1075491
  · exact B1075495
  · exact B1075499
  · exact B1075503
  · exact B1075507
  · exact B1075511
  · exact B1075515
  · exact B1075519
  · exact B1075523
  · exact B1075527
  · exact B1075531
  · exact B1075535
  · exact B1075539
  · exact B1075543
  · exact B1075547
  · exact B1075551
  · exact B1075555
  · exact B1075559
  · exact B1075563
  · exact B1075567
  · exact B1075571
  · exact B1075575
  · exact B1075579
  · exact B1075583
  · exact B1075587
  · exact B1075591
  · exact B1075595
  · exact B1075599
  · exact B1075603
  · exact B1075607
  · exact B1075611
  · exact B1075615
  · exact B1075619
  · exact B1075623
  · exact B1075627
  · exact B1075631
  · exact B1075635
  · exact B1075639
  · exact B1075643
  · exact B1075647
  · exact B1075651
  · exact B1075655
  · exact B1075659
  · exact B1075663
  · exact B1075667
  · exact B1075671
  · exact B1075675
  · exact B1075679
  · exact B1075683
  · exact B1075687
  · exact B1075691
  · exact B1075695
  · exact B1075699
  · exact B1075703
  · exact B1075707
  · exact B1075711
  · exact B1075715
  · exact B1075719
  · exact B1075723
  · exact B1075727
  · exact B1075731
  · exact B1075735
  · exact B1075739
  · exact B1075743
  · exact B1075747
  · exact B1075751
  · exact B1075755
  · exact B1075759
  · exact B1075763
  · exact B1075767
  · exact B1075771
  · exact B1075775
  · exact B1075779
  · exact B1075783
  · exact B1075787
  · exact B1075791
  · exact B1075795
  · exact B1075799
  · exact B1075803
  · exact B1075807
  · exact B1075811
  · exact B1075815
  · exact B1075819
  · exact B1075823
  · exact B1075827
  · exact B1075831
  · exact B1075835
  · exact B1075839
  · exact B1075843
  · exact B1075847
  · exact B1075851
  · exact B1075855
  · exact B1075859
  · exact B1075863
  · exact B1075867
  · exact B1075871
  · exact B1075875
  · exact B1075879
  · exact B1075883
  · exact B1075887
  · exact B1075891
  · exact B1075895
  · exact B1075899
  · exact B1075903
  · exact B1075907
  · exact B1075911
  · exact B1075915
  · exact B1075919
  · exact B1075923
  · exact B1075927
  · exact B1075931
  · exact B1075935
  · exact B1075939
  · exact B1075943
  · exact B1075947
  · exact B1075951
  · exact B1075955
  · exact B1075959
  · exact B1075963
  · exact B1075967
  · exact B1075971
  · exact B1075975
  · exact B1075979
  · exact B1075983
  · exact B1075987
  · exact B1075991
  · exact B1075995
  · exact B1075999
  · exact B1076003
  · exact B1076007
  · exact B1076011
  · exact B1076015
  · exact B1076019
  · exact B1076023
  · exact B1076027
  · exact B1076031
  · exact B1076035
  · exact B1076039
  · exact B1076043
  · exact B1076047
  · exact B1076051
  · exact B1076055
  · exact B1076059
  · exact B1076063
  · exact B1076067
  · exact B1076071
  · exact B1076075
  · exact B1076079
  · exact B1076083
  · exact B1076087
  · exact B1076091
  · exact B1076095
  · exact B1076099
  · exact B1076103
  · exact B1076107
  · exact B1076111
  · exact B1076115
  · exact B1076119
  · exact B1076123
  · exact B1076127
  · exact B1076131
  · exact B1076135
  · exact B1076139
  · exact B1076143
  · exact B1076147
  · exact B1076151
  · exact B1076155
  · exact B1076159
  · exact B1076163
  · exact B1076167
  · exact B1076171
  · exact B1076175
  · exact B1076179
  · exact B1076183
  · exact B1076187
  · exact B1076191
  · exact B1076195
  · exact B1076199
  · exact B1076203
  · exact B1076207
  · exact B1076211
  · exact B1076215
  · exact B1076219
  · exact B1076223
  · exact B1076227
  · exact B1076231
  · exact B1076235
  · exact B1076239
  · exact B1076243
  · exact B1076247
  · exact B1076251
  · exact B1076255
  · exact B1076259
  · exact B1076263
  · exact B1076267
  · exact B1076271
  · exact B1076275
  · exact B1076279
  · exact B1076283
  · exact B1076287
  · exact B1076291
  · exact B1076295
  · exact B1076299
  · exact B1076303
  · exact B1076307
  · exact B1076311
  · exact B1076315
  · exact B1076319
  · exact B1076323
  · exact B1076327
  · exact B1076331
  · exact B1076335
  · exact B1076339
  · exact B1076343
  · exact B1076347
  · exact B1076351
  · exact B1076355
  · exact B1076359
  · exact B1076363
  · exact B1076367
  · exact B1076371
  · exact B1076375
  · exact B1076379
  · exact B1076383
  · exact B1076387
  · exact B1076391
  · exact B1076395
  · exact B1076399
  · exact B1076403
  · exact B1076407
  · exact B1076411
  · exact B1076415
  · exact B1076419
  · exact B1076423
  · exact B1076427
  · exact B1076431
  · exact B1076435
  · exact B1076439
  · exact B1076443
  · exact B1076447
  · exact B1076451
  · exact B1076455
  · exact B1076459
  · exact B1076463
  · exact B1076467
  · exact B1076471
  · exact B1076475
  · exact B1076479
  · exact B1076483
  · exact B1076487
  · exact B1076491
  · exact B1076495
  · exact B1076499
  · exact B1076503
  · exact B1076507
  · exact B1076511
  · exact B1076515
  · exact B1076519
  · exact B1076523
  · exact B1076527
  · exact B1076531
  · exact B1076535
  · exact B1076539
  · exact B1076543
  · exact B1076547
  · exact B1076551
  · exact B1076555
  · exact B1076559
  · exact B1076563
  · exact B1076567
  · exact B1076571
  · exact B1076575
  · exact B1076579
  · exact B1076583
  · exact B1076587
  · exact B1076591
  · exact B1076595
  · exact B1076599
  · exact B1076603
  · exact B1076607
  · exact B1076611
  · exact B1076615

theorem solution (m : ℕ) (hlo : 1072617 ≤ m) (hhi : m ≤ 1076617) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 268154 ≤ j := by omega
    have hj2 : j ≤ 269153 := by omega
    have hb : Blo 1072617 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 268854 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
