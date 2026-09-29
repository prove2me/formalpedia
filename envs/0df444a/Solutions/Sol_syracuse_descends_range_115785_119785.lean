-- Prove2me | solution 1 for syracuse_descends_range_115785_119785
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:31.000629+00:00
-- url     : https://prove2.me/submissions/1bcd2584-7397-42f9-abec-141b035dd4b6

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


theorem B131089 : Blo 115785 131089 := bbase (se 2 (by rfl) ⟨49158, by rfl⟩ : syracuseStep 131089 = 98317) (by norm_num)
theorem B294941 : Blo 115785 294941 := bbase (se 3 (by rfl) ⟨55301, by rfl⟩ : syracuseStep 294941 = 110603) (by norm_num)
theorem B196661 : Blo 115785 196661 := bbase (se 5 (by rfl) ⟨9218, by rfl⟩ : syracuseStep 196661 = 18437) (by norm_num)
theorem B131125 : Blo 115785 131125 := bbase (se 5 (by rfl) ⟨6146, by rfl⟩ : syracuseStep 131125 = 12293) (by norm_num)
theorem B1015861 : Blo 115785 1015861 := bbase (se 5 (by rfl) ⟨47618, by rfl⟩ : syracuseStep 1015861 = 95237) (by norm_num)
theorem B262205 : Blo 115785 262205 := bbase (se 3 (by rfl) ⟨49163, by rfl⟩ : syracuseStep 262205 = 98327) (by norm_num)
theorem B131161 : Blo 115785 131161 := bbase (se 2 (by rfl) ⟨49185, by rfl⟩ : syracuseStep 131161 = 98371) (by norm_num)
theorem B131197 : Blo 115785 131197 := bbase (se 3 (by rfl) ⟨24599, by rfl⟩ : syracuseStep 131197 = 49199) (by norm_num)
theorem B262277 : Blo 115785 262277 := bbase (se 4 (by rfl) ⟨24588, by rfl⟩ : syracuseStep 262277 = 49177) (by norm_num)
theorem B131233 : Blo 115785 131233 := bbase (se 2 (by rfl) ⟨49212, by rfl⟩ : syracuseStep 131233 = 98425) (by norm_num)
theorem B196789 : Blo 115785 196789 := bbase (se 5 (by rfl) ⟨9224, by rfl⟩ : syracuseStep 196789 = 18449) (by norm_num)
theorem B557237 : Blo 115785 557237 := bbase (se 5 (by rfl) ⟨26120, by rfl⟩ : syracuseStep 557237 = 52241) (by norm_num)
theorem B131269 : Blo 115785 131269 := bbase (se 4 (by rfl) ⟨12306, by rfl⟩ : syracuseStep 131269 = 24613) (by norm_num)
theorem B262349 : Blo 115785 262349 := bbase (se 3 (by rfl) ⟨49190, by rfl⟩ : syracuseStep 262349 = 98381) (by norm_num)
theorem B131305 : Blo 115785 131305 := bbase (se 2 (by rfl) ⟨49239, by rfl⟩ : syracuseStep 131305 = 98479) (by norm_num)
theorem B196877 : Blo 115785 196877 := bbase (se 3 (by rfl) ⟨36914, by rfl⟩ : syracuseStep 196877 = 73829) (by norm_num)
theorem B131341 : Blo 115785 131341 := bbase (se 3 (by rfl) ⟨24626, by rfl⟩ : syracuseStep 131341 = 49253) (by norm_num)
theorem B262421 : Blo 115785 262421 := bbase (se 6 (by rfl) ⟨6150, by rfl⟩ : syracuseStep 262421 = 12301) (by norm_num)
theorem B131377 : Blo 115785 131377 := bbase (se 2 (by rfl) ⟨49266, by rfl⟩ : syracuseStep 131377 = 98533) (by norm_num)
theorem B590165 : Blo 115785 590165 := bbase (se 10 (by rfl) ⟨864, by rfl⟩ : syracuseStep 590165 = 1729) (by norm_num)
theorem B131413 : Blo 115785 131413 := bbase (se 10 (by rfl) ⟨192, by rfl⟩ : syracuseStep 131413 = 385) (by norm_num)
theorem B262493 : Blo 115785 262493 := bbase (se 3 (by rfl) ⟨49217, by rfl⟩ : syracuseStep 262493 = 98435) (by norm_num)
theorem B295285 : Blo 115785 295285 := bbase (se 5 (by rfl) ⟨13841, by rfl⟩ : syracuseStep 295285 = 27683) (by norm_num)
theorem B131449 : Blo 115785 131449 := bbase (se 2 (by rfl) ⟨49293, by rfl⟩ : syracuseStep 131449 = 98587) (by norm_num)
theorem B393605 : Blo 115785 393605 := bbase (se 4 (by rfl) ⟨36900, by rfl⟩ : syracuseStep 393605 = 73801) (by norm_num)
theorem B197005 : Blo 115785 197005 := bbase (se 3 (by rfl) ⟨36938, by rfl⟩ : syracuseStep 197005 = 73877) (by norm_num)
theorem B131485 : Blo 115785 131485 := bbase (se 3 (by rfl) ⟨24653, by rfl⟩ : syracuseStep 131485 = 49307) (by norm_num)
theorem B262565 : Blo 115785 262565 := bbase (se 4 (by rfl) ⟨24615, by rfl⟩ : syracuseStep 262565 = 49231) (by norm_num)
theorem B131521 : Blo 115785 131521 := bbase (se 2 (by rfl) ⟨49320, by rfl⟩ : syracuseStep 131521 = 98641) (by norm_num)
theorem B295397 : Blo 115785 295397 := bbase (se 4 (by rfl) ⟨27693, by rfl⟩ : syracuseStep 295397 = 55387) (by norm_num)
theorem B197093 : Blo 115785 197093 := bbase (se 4 (by rfl) ⟨18477, by rfl⟩ : syracuseStep 197093 = 36955) (by norm_num)
theorem B131557 : Blo 115785 131557 := bbase (se 4 (by rfl) ⟨12333, by rfl⟩ : syracuseStep 131557 = 24667) (by norm_num)
theorem B262637 : Blo 115785 262637 := bbase (se 3 (by rfl) ⟨49244, by rfl⟩ : syracuseStep 262637 = 98489) (by norm_num)
theorem B131593 : Blo 115785 131593 := bbase (se 2 (by rfl) ⟨49347, by rfl⟩ : syracuseStep 131593 = 98695) (by norm_num)
theorem B131629 : Blo 115785 131629 := bbase (se 3 (by rfl) ⟨24680, by rfl⟩ : syracuseStep 131629 = 49361) (by norm_num)
theorem B262709 : Blo 115785 262709 := bbase (se 5 (by rfl) ⟨12314, by rfl⟩ : syracuseStep 262709 = 24629) (by norm_num)
theorem B131665 : Blo 115785 131665 := bbase (se 2 (by rfl) ⟨49374, by rfl⟩ : syracuseStep 131665 = 98749) (by norm_num)
theorem B197221 : Blo 115785 197221 := bbase (se 4 (by rfl) ⟨18489, by rfl⟩ : syracuseStep 197221 = 36979) (by norm_num)
theorem B131701 : Blo 115785 131701 := bbase (se 5 (by rfl) ⟨6173, by rfl⟩ : syracuseStep 131701 = 12347) (by norm_num)
theorem B262781 : Blo 115785 262781 := bbase (se 3 (by rfl) ⟨49271, by rfl⟩ : syracuseStep 262781 = 98543) (by norm_num)
theorem B131737 : Blo 115785 131737 := bbase (se 2 (by rfl) ⟨49401, by rfl⟩ : syracuseStep 131737 = 98803) (by norm_num)
theorem B295589 : Blo 115785 295589 := bbase (se 4 (by rfl) ⟨27711, by rfl⟩ : syracuseStep 295589 = 55423) (by norm_num)
theorem B197309 : Blo 115785 197309 := bbase (se 3 (by rfl) ⟨36995, by rfl⟩ : syracuseStep 197309 = 73991) (by norm_num)
theorem B131773 : Blo 115785 131773 := bbase (se 3 (by rfl) ⟨24707, by rfl⟩ : syracuseStep 131773 = 49415) (by norm_num)
theorem B262853 : Blo 115785 262853 := bbase (se 4 (by rfl) ⟨24642, by rfl⟩ : syracuseStep 262853 = 49285) (by norm_num)
theorem B131809 : Blo 115785 131809 := bbase (se 2 (by rfl) ⟨49428, by rfl⟩ : syracuseStep 131809 = 98857) (by norm_num)
theorem B131845 : Blo 115785 131845 := bbase (se 4 (by rfl) ⟨12360, by rfl⟩ : syracuseStep 131845 = 24721) (by norm_num)
theorem B262925 : Blo 115785 262925 := bbase (se 3 (by rfl) ⟨49298, by rfl⟩ : syracuseStep 262925 = 98597) (by norm_num)
theorem B131881 : Blo 115785 131881 := bbase (se 2 (by rfl) ⟨49455, by rfl⟩ : syracuseStep 131881 = 98911) (by norm_num)
theorem B394037 : Blo 115785 394037 := bbase (se 5 (by rfl) ⟨18470, by rfl⟩ : syracuseStep 394037 = 36941) (by norm_num)
theorem B197437 : Blo 115785 197437 := bbase (se 3 (by rfl) ⟨37019, by rfl⟩ : syracuseStep 197437 = 74039) (by norm_num)
theorem B131917 : Blo 115785 131917 := bbase (se 3 (by rfl) ⟨24734, by rfl⟩ : syracuseStep 131917 = 49469) (by norm_num)
theorem B262997 : Blo 115785 262997 := bbase (se 9 (by rfl) ⟨770, by rfl⟩ : syracuseStep 262997 = 1541) (by norm_num)
theorem B131953 : Blo 115785 131953 := bbase (se 2 (by rfl) ⟨49482, by rfl⟩ : syracuseStep 131953 = 98965) (by norm_num)
theorem B426869 : Blo 115785 426869 := bbase (se 5 (by rfl) ⟨20009, by rfl⟩ : syracuseStep 426869 = 40019) (by norm_num)
theorem B1147765 : Blo 115785 1147765 := bbase (se 5 (by rfl) ⟨53801, by rfl⟩ : syracuseStep 1147765 = 107603) (by norm_num)
theorem B197525 : Blo 115785 197525 := bbase (se 6 (by rfl) ⟨4629, by rfl⟩ : syracuseStep 197525 = 9259) (by norm_num)
theorem B131989 : Blo 115785 131989 := bbase (se 6 (by rfl) ⟨3093, by rfl⟩ : syracuseStep 131989 = 6187) (by norm_num)
theorem B263069 : Blo 115785 263069 := bbase (se 3 (by rfl) ⟨49325, by rfl⟩ : syracuseStep 263069 = 98651) (by norm_num)
theorem B132025 : Blo 115785 132025 := bbase (se 2 (by rfl) ⟨49509, by rfl⟩ : syracuseStep 132025 = 99019) (by norm_num)
theorem B132061 : Blo 115785 132061 := bbase (se 3 (by rfl) ⟨24761, by rfl⟩ : syracuseStep 132061 = 49523) (by norm_num)
theorem B263141 : Blo 115785 263141 := bbase (se 4 (by rfl) ⟨24669, by rfl⟩ : syracuseStep 263141 = 49339) (by norm_num)
theorem B295933 : Blo 115785 295933 := bbase (se 3 (by rfl) ⟨55487, by rfl⟩ : syracuseStep 295933 = 110975) (by norm_num)
theorem B132097 : Blo 115785 132097 := bbase (se 2 (by rfl) ⟨49536, by rfl⟩ : syracuseStep 132097 = 99073) (by norm_num)
theorem B197653 : Blo 115785 197653 := bbase (se 6 (by rfl) ⟨4632, by rfl⟩ : syracuseStep 197653 = 9265) (by norm_num)
theorem B230429 : Blo 115785 230429 := bbase (se 3 (by rfl) ⟨43205, by rfl⟩ : syracuseStep 230429 = 86411) (by norm_num)
theorem B132133 : Blo 115785 132133 := bbase (se 4 (by rfl) ⟨12387, by rfl⟩ : syracuseStep 132133 = 24775) (by norm_num)
theorem B263213 : Blo 115785 263213 := bbase (se 3 (by rfl) ⟨49352, by rfl⟩ : syracuseStep 263213 = 98705) (by norm_num)
theorem B132169 : Blo 115785 132169 := bbase (se 2 (by rfl) ⟨49563, by rfl⟩ : syracuseStep 132169 = 99127) (by norm_num)
theorem B296045 : Blo 115785 296045 := bbase (se 3 (by rfl) ⟨55508, by rfl⟩ : syracuseStep 296045 = 111017) (by norm_num)
theorem B197741 : Blo 115785 197741 := bbase (se 3 (by rfl) ⟨37076, by rfl⟩ : syracuseStep 197741 = 74153) (by norm_num)
theorem B132205 : Blo 115785 132205 := bbase (se 3 (by rfl) ⟨24788, by rfl⟩ : syracuseStep 132205 = 49577) (by norm_num)
theorem B263285 : Blo 115785 263285 := bbase (se 5 (by rfl) ⟨12341, by rfl⟩ : syracuseStep 263285 = 24683) (by norm_num)
theorem B132241 : Blo 115785 132241 := bbase (se 2 (by rfl) ⟨49590, by rfl⟩ : syracuseStep 132241 = 99181) (by norm_num)
theorem B132277 : Blo 115785 132277 := bbase (se 5 (by rfl) ⟨6200, by rfl⟩ : syracuseStep 132277 = 12401) (by norm_num)
theorem B263357 : Blo 115785 263357 := bbase (se 3 (by rfl) ⟨49379, by rfl⟩ : syracuseStep 263357 = 98759) (by norm_num)
theorem B132313 : Blo 115785 132313 := bbase (se 2 (by rfl) ⟨49617, by rfl⟩ : syracuseStep 132313 = 99235) (by norm_num)
theorem B394469 : Blo 115785 394469 := bbase (se 4 (by rfl) ⟨36981, by rfl⟩ : syracuseStep 394469 = 73963) (by norm_num)
theorem B197869 : Blo 115785 197869 := bbase (se 3 (by rfl) ⟨37100, by rfl⟩ : syracuseStep 197869 = 74201) (by norm_num)
theorem B132349 : Blo 115785 132349 := bbase (se 3 (by rfl) ⟨24815, by rfl⟩ : syracuseStep 132349 = 49631) (by norm_num)
theorem B263429 : Blo 115785 263429 := bbase (se 4 (by rfl) ⟨24696, by rfl⟩ : syracuseStep 263429 = 49393) (by norm_num)
theorem B427285 : Blo 115785 427285 := bbase (se 6 (by rfl) ⟨10014, by rfl⟩ : syracuseStep 427285 = 20029) (by norm_num)
theorem B132385 : Blo 115785 132385 := bbase (se 2 (by rfl) ⟨49644, by rfl⟩ : syracuseStep 132385 = 99289) (by norm_num)
theorem B427301 : Blo 115785 427301 := bbase (se 4 (by rfl) ⟨40059, by rfl⟩ : syracuseStep 427301 = 80119) (by norm_num)
theorem B296237 : Blo 115785 296237 := bbase (se 3 (by rfl) ⟨55544, by rfl⟩ : syracuseStep 296237 = 111089) (by norm_num)
theorem B197957 : Blo 115785 197957 := bbase (se 4 (by rfl) ⟨18558, by rfl⟩ : syracuseStep 197957 = 37117) (by norm_num)
theorem B132421 : Blo 115785 132421 := bbase (se 4 (by rfl) ⟨12414, by rfl⟩ : syracuseStep 132421 = 24829) (by norm_num)
theorem B263501 : Blo 115785 263501 := bbase (se 3 (by rfl) ⟨49406, by rfl⟩ : syracuseStep 263501 = 98813) (by norm_num)
theorem B132457 : Blo 115785 132457 := bbase (se 2 (by rfl) ⟨49671, by rfl⟩ : syracuseStep 132457 = 99343) (by norm_num)
theorem B132493 : Blo 115785 132493 := bbase (se 3 (by rfl) ⟨24842, by rfl⟩ : syracuseStep 132493 = 49685) (by norm_num)
theorem B263573 : Blo 115785 263573 := bbase (se 6 (by rfl) ⟨6177, by rfl⟩ : syracuseStep 263573 = 12355) (by norm_num)
theorem B132529 : Blo 115785 132529 := bbase (se 2 (by rfl) ⟨49698, by rfl⟩ : syracuseStep 132529 = 99397) (by norm_num)
theorem B198085 : Blo 115785 198085 := bbase (se 4 (by rfl) ⟨18570, by rfl⟩ : syracuseStep 198085 = 37141) (by norm_num)
theorem B132565 : Blo 115785 132565 := bbase (se 7 (by rfl) ⟨1553, by rfl⟩ : syracuseStep 132565 = 3107) (by norm_num)
theorem B165341 : Blo 115785 165341 := bbase (se 3 (by rfl) ⟨31001, by rfl⟩ : syracuseStep 165341 = 62003) (by norm_num)
theorem B263645 : Blo 115785 263645 := bbase (se 3 (by rfl) ⟨49433, by rfl⟩ : syracuseStep 263645 = 98867) (by norm_num)
theorem B132601 : Blo 115785 132601 := bbase (se 2 (by rfl) ⟨49725, by rfl⟩ : syracuseStep 132601 = 99451) (by norm_num)
theorem B198173 : Blo 115785 198173 := bbase (se 3 (by rfl) ⟨37157, by rfl⟩ : syracuseStep 198173 = 74315) (by norm_num)
theorem B132637 : Blo 115785 132637 := bbase (se 3 (by rfl) ⟨24869, by rfl⟩ : syracuseStep 132637 = 49739) (by norm_num)
theorem B263717 : Blo 115785 263717 := bbase (se 4 (by rfl) ⟨24723, by rfl⟩ : syracuseStep 263717 = 49447) (by norm_num)
theorem B132673 : Blo 115785 132673 := bbase (se 2 (by rfl) ⟨49752, by rfl⟩ : syracuseStep 132673 = 99505) (by norm_num)
theorem B427589 : Blo 115785 427589 := bbase (se 4 (by rfl) ⟨40086, by rfl⟩ : syracuseStep 427589 = 80173) (by norm_num)
theorem B591461 : Blo 115785 591461 := bbase (se 4 (by rfl) ⟨55449, by rfl⟩ : syracuseStep 591461 = 110899) (by norm_num)
theorem B132709 : Blo 115785 132709 := bbase (se 4 (by rfl) ⟨12441, by rfl⟩ : syracuseStep 132709 = 24883) (by norm_num)
theorem B263789 : Blo 115785 263789 := bbase (se 3 (by rfl) ⟨49460, by rfl⟩ : syracuseStep 263789 = 98921) (by norm_num)
theorem B296581 : Blo 115785 296581 := bbase (se 4 (by rfl) ⟨27804, by rfl⟩ : syracuseStep 296581 = 55609) (by norm_num)
theorem B132745 : Blo 115785 132745 := bbase (se 2 (by rfl) ⟨49779, by rfl⟩ : syracuseStep 132745 = 99559) (by norm_num)
theorem B394901 : Blo 115785 394901 := bbase (se 6 (by rfl) ⟨9255, by rfl⟩ : syracuseStep 394901 = 18511) (by norm_num)
theorem B198301 : Blo 115785 198301 := bbase (se 3 (by rfl) ⟨37181, by rfl⟩ : syracuseStep 198301 = 74363) (by norm_num)
theorem B132781 : Blo 115785 132781 := bbase (se 3 (by rfl) ⟨24896, by rfl⟩ : syracuseStep 132781 = 49793) (by norm_num)
theorem B263861 : Blo 115785 263861 := bbase (se 5 (by rfl) ⟨12368, by rfl⟩ : syracuseStep 263861 = 24737) (by norm_num)
theorem B132817 : Blo 115785 132817 := bbase (se 2 (by rfl) ⟨49806, by rfl⟩ : syracuseStep 132817 = 99613) (by norm_num)
theorem B296693 : Blo 115785 296693 := bbase (se 5 (by rfl) ⟨13907, by rfl⟩ : syracuseStep 296693 = 27815) (by norm_num)
theorem B198389 : Blo 115785 198389 := bbase (se 5 (by rfl) ⟨9299, by rfl⟩ : syracuseStep 198389 = 18599) (by norm_num)
theorem B132853 : Blo 115785 132853 := bbase (se 5 (by rfl) ⟨6227, by rfl⟩ : syracuseStep 132853 = 12455) (by norm_num)
theorem B263933 : Blo 115785 263933 := bbase (se 3 (by rfl) ⟨49487, by rfl⟩ : syracuseStep 263933 = 98975) (by norm_num)
theorem B132889 : Blo 115785 132889 := bbase (se 2 (by rfl) ⟨49833, by rfl⟩ : syracuseStep 132889 = 99667) (by norm_num)
theorem B132925 : Blo 115785 132925 := bbase (se 3 (by rfl) ⟨24923, by rfl⟩ : syracuseStep 132925 = 49847) (by norm_num)
theorem B264005 : Blo 115785 264005 := bbase (se 4 (by rfl) ⟨24750, by rfl⟩ : syracuseStep 264005 = 49501) (by norm_num)
theorem B132961 : Blo 115785 132961 := bbase (se 2 (by rfl) ⟨49860, by rfl⟩ : syracuseStep 132961 = 99721) (by norm_num)
theorem B198517 : Blo 115785 198517 := bbase (se 5 (by rfl) ⟨9305, by rfl⟩ : syracuseStep 198517 = 18611) (by norm_num)
theorem B132997 : Blo 115785 132997 := bbase (se 4 (by rfl) ⟨12468, by rfl⟩ : syracuseStep 132997 = 24937) (by norm_num)
theorem B264077 : Blo 115785 264077 := bbase (se 3 (by rfl) ⟨49514, by rfl⟩ : syracuseStep 264077 = 99029) (by norm_num)
theorem B133033 : Blo 115785 133033 := bbase (se 2 (by rfl) ⟨49887, by rfl⟩ : syracuseStep 133033 = 99775) (by norm_num)
theorem B296885 : Blo 115785 296885 := bbase (se 5 (by rfl) ⟨13916, by rfl⟩ : syracuseStep 296885 = 27833) (by norm_num)
theorem B198605 : Blo 115785 198605 := bbase (se 3 (by rfl) ⟨37238, by rfl⟩ : syracuseStep 198605 = 74477) (by norm_num)
theorem B133069 : Blo 115785 133069 := bbase (se 3 (by rfl) ⟨24950, by rfl⟩ : syracuseStep 133069 = 49901) (by norm_num)
theorem B755669 : Blo 115785 755669 := bbase (se 7 (by rfl) ⟨8855, by rfl⟩ : syracuseStep 755669 = 17711) (by norm_num)
theorem B264149 : Blo 115785 264149 := bbase (se 7 (by rfl) ⟨3095, by rfl⟩ : syracuseStep 264149 = 6191) (by norm_num)
theorem B133105 : Blo 115785 133105 := bbase (se 2 (by rfl) ⟨49914, by rfl⟩ : syracuseStep 133105 = 99829) (by norm_num)
theorem B1017845 : Blo 115785 1017845 := bbase (se 5 (by rfl) ⟨47711, by rfl⟩ : syracuseStep 1017845 = 95423) (by norm_num)
theorem B165893 : Blo 115785 165893 := bbase (se 4 (by rfl) ⟨15552, by rfl⟩ : syracuseStep 165893 = 31105) (by norm_num)
theorem B133141 : Blo 115785 133141 := bbase (se 6 (by rfl) ⟨3120, by rfl⟩ : syracuseStep 133141 = 6241) (by norm_num)
theorem B264221 : Blo 115785 264221 := bbase (se 3 (by rfl) ⟨49541, by rfl⟩ : syracuseStep 264221 = 99083) (by norm_num)
theorem B133177 : Blo 115785 133177 := bbase (se 2 (by rfl) ⟨49941, by rfl⟩ : syracuseStep 133177 = 99883) (by norm_num)
theorem B395333 : Blo 115785 395333 := bbase (se 4 (by rfl) ⟨37062, by rfl⟩ : syracuseStep 395333 = 74125) (by norm_num)
theorem B198733 : Blo 115785 198733 := bbase (se 3 (by rfl) ⟨37262, by rfl⟩ : syracuseStep 198733 = 74525) (by norm_num)
theorem B133213 : Blo 115785 133213 := bbase (se 3 (by rfl) ⟨24977, by rfl⟩ : syracuseStep 133213 = 49955) (by norm_num)
theorem B264293 : Blo 115785 264293 := bbase (se 4 (by rfl) ⟨24777, by rfl⟩ : syracuseStep 264293 = 49555) (by norm_num)
theorem B133249 : Blo 115785 133249 := bbase (se 2 (by rfl) ⟨49968, by rfl⟩ : syracuseStep 133249 = 99937) (by norm_num)
theorem B198821 : Blo 115785 198821 := bbase (se 4 (by rfl) ⟨18639, by rfl⟩ : syracuseStep 198821 = 37279) (by norm_num)
theorem B133285 : Blo 115785 133285 := bbase (se 4 (by rfl) ⟨12495, by rfl⟩ : syracuseStep 133285 = 24991) (by norm_num)
theorem B264365 : Blo 115785 264365 := bbase (se 3 (by rfl) ⟨49568, by rfl⟩ : syracuseStep 264365 = 99137) (by norm_num)
theorem B133321 : Blo 115785 133321 := bbase (se 2 (by rfl) ⟨49995, by rfl⟩ : syracuseStep 133321 = 99991) (by norm_num)
theorem B133357 : Blo 115785 133357 := bbase (se 3 (by rfl) ⟨25004, by rfl⟩ : syracuseStep 133357 = 50009) (by norm_num)
theorem B264437 : Blo 115785 264437 := bbase (se 5 (by rfl) ⟨12395, by rfl⟩ : syracuseStep 264437 = 24791) (by norm_num)
theorem B297229 : Blo 115785 297229 := bbase (se 3 (by rfl) ⟨55730, by rfl⟩ : syracuseStep 297229 = 111461) (by norm_num)
theorem B133393 : Blo 115785 133393 := bbase (se 2 (by rfl) ⟨50022, by rfl⟩ : syracuseStep 133393 = 100045) (by norm_num)
theorem B198949 : Blo 115785 198949 := bbase (se 4 (by rfl) ⟨18651, by rfl⟩ : syracuseStep 198949 = 37303) (by norm_num)
theorem B133429 : Blo 115785 133429 := bbase (se 5 (by rfl) ⟨6254, by rfl⟩ : syracuseStep 133429 = 12509) (by norm_num)
theorem B264509 : Blo 115785 264509 := bbase (se 3 (by rfl) ⟨49595, by rfl⟩ : syracuseStep 264509 = 99191) (by norm_num)
theorem B133465 : Blo 115785 133465 := bbase (se 2 (by rfl) ⟨50049, by rfl⟩ : syracuseStep 133465 = 100099) (by norm_num)
theorem B330101 : Blo 115785 330101 := bbase (se 5 (by rfl) ⟨15473, by rfl⟩ : syracuseStep 330101 = 30947) (by norm_num)
theorem B297341 : Blo 115785 297341 := bbase (se 3 (by rfl) ⟨55751, by rfl⟩ : syracuseStep 297341 = 111503) (by norm_num)
theorem B199037 : Blo 115785 199037 := bbase (se 3 (by rfl) ⟨37319, by rfl⟩ : syracuseStep 199037 = 74639) (by norm_num)
theorem B133501 : Blo 115785 133501 := bbase (se 3 (by rfl) ⟨25031, by rfl⟩ : syracuseStep 133501 = 50063) (by norm_num)
theorem B264581 : Blo 115785 264581 := bbase (se 4 (by rfl) ⟨24804, by rfl⟩ : syracuseStep 264581 = 49609) (by norm_num)
theorem B133537 : Blo 115785 133537 := bbase (se 2 (by rfl) ⟨50076, by rfl⟩ : syracuseStep 133537 = 100153) (by norm_num)
theorem B133573 : Blo 115785 133573 := bbase (se 4 (by rfl) ⟨12522, by rfl⟩ : syracuseStep 133573 = 25045) (by norm_num)
theorem B264653 : Blo 115785 264653 := bbase (se 3 (by rfl) ⟨49622, by rfl⟩ : syracuseStep 264653 = 99245) (by norm_num)
theorem B133609 : Blo 115785 133609 := bbase (se 2 (by rfl) ⟨50103, by rfl⟩ : syracuseStep 133609 = 100207) (by norm_num)
theorem B395765 : Blo 115785 395765 := bbase (se 5 (by rfl) ⟨18551, by rfl⟩ : syracuseStep 395765 = 37103) (by norm_num)
theorem B199165 : Blo 115785 199165 := bbase (se 3 (by rfl) ⟨37343, by rfl⟩ : syracuseStep 199165 = 74687) (by norm_num)
theorem B133645 : Blo 115785 133645 := bbase (se 3 (by rfl) ⟨25058, by rfl⟩ : syracuseStep 133645 = 50117) (by norm_num)
theorem B264725 : Blo 115785 264725 := bbase (se 6 (by rfl) ⟨6204, by rfl⟩ : syracuseStep 264725 = 12409) (by norm_num)
theorem B133681 : Blo 115785 133681 := bbase (se 2 (by rfl) ⟨50130, by rfl⟩ : syracuseStep 133681 = 100261) (by norm_num)
theorem B297533 : Blo 115785 297533 := bbase (se 3 (by rfl) ⟨55787, by rfl⟩ : syracuseStep 297533 = 111575) (by norm_num)
theorem B232013 : Blo 115785 232013 := bbase (se 3 (by rfl) ⟨43502, by rfl⟩ : syracuseStep 232013 = 87005) (by norm_num)
theorem B133717 : Blo 115785 133717 := bbase (se 8 (by rfl) ⟨783, by rfl⟩ : syracuseStep 133717 = 1567) (by norm_num)
theorem B199253 : Blo 115785 199253 := bbase (se 8 (by rfl) ⟨1167, by rfl⟩ : syracuseStep 199253 = 2335) (by norm_num)
theorem B264797 : Blo 115785 264797 := bbase (se 3 (by rfl) ⟨49649, by rfl⟩ : syracuseStep 264797 = 99299) (by norm_num)
theorem B133753 : Blo 115785 133753 := bbase (se 2 (by rfl) ⟨50157, by rfl⟩ : syracuseStep 133753 = 100315) (by norm_num)
theorem B133789 : Blo 115785 133789 := bbase (se 3 (by rfl) ⟨25085, by rfl⟩ : syracuseStep 133789 = 50171) (by norm_num)
theorem B264869 : Blo 115785 264869 := bbase (se 4 (by rfl) ⟨24831, by rfl⟩ : syracuseStep 264869 = 49663) (by norm_num)
theorem B1215157 : Blo 115785 1215157 := bbase (se 5 (by rfl) ⟨56960, by rfl⟩ : syracuseStep 1215157 = 113921) (by norm_num)
theorem B133825 : Blo 115785 133825 := bbase (se 2 (by rfl) ⟨50184, by rfl⟩ : syracuseStep 133825 = 100369) (by norm_num)
theorem B199381 : Blo 115785 199381 := bbase (se 7 (by rfl) ⟨2336, by rfl⟩ : syracuseStep 199381 = 4673) (by norm_num)
theorem B133861 : Blo 115785 133861 := bbase (se 4 (by rfl) ⟨12549, by rfl⟩ : syracuseStep 133861 = 25099) (by norm_num)
theorem B264941 : Blo 115785 264941 := bbase (se 3 (by rfl) ⟨49676, by rfl⟩ : syracuseStep 264941 = 99353) (by norm_num)
theorem B166645 : Blo 115785 166645 := bbase (se 5 (by rfl) ⟨7811, by rfl⟩ : syracuseStep 166645 = 15623) (by norm_num)
theorem B133897 : Blo 115785 133897 := bbase (se 2 (by rfl) ⟨50211, by rfl⟩ : syracuseStep 133897 = 100423) (by norm_num)
theorem B199469 : Blo 115785 199469 := bbase (se 3 (by rfl) ⟨37400, by rfl⟩ : syracuseStep 199469 = 74801) (by norm_num)
theorem B133933 : Blo 115785 133933 := bbase (se 3 (by rfl) ⟨25112, by rfl⟩ : syracuseStep 133933 = 50225) (by norm_num)
theorem B265013 : Blo 115785 265013 := bbase (se 5 (by rfl) ⟨12422, by rfl⟩ : syracuseStep 265013 = 24845) (by norm_num)
theorem B265037 : Blo 115785 265037 := bbase (se 3 (by rfl) ⟨49694, by rfl⟩ : syracuseStep 265037 = 99389) (by norm_num)
theorem B133969 : Blo 115785 133969 := bbase (se 2 (by rfl) ⟨50238, by rfl⟩ : syracuseStep 133969 = 100477) (by norm_num)
theorem B592757 : Blo 115785 592757 := bbase (se 5 (by rfl) ⟨27785, by rfl⟩ : syracuseStep 592757 = 55571) (by norm_num)
theorem B134005 : Blo 115785 134005 := bbase (se 5 (by rfl) ⟨6281, by rfl⟩ : syracuseStep 134005 = 12563) (by norm_num)
theorem B265085 : Blo 115785 265085 := bbase (se 3 (by rfl) ⟨49703, by rfl⟩ : syracuseStep 265085 = 99407) (by norm_num)
theorem B297877 : Blo 115785 297877 := bbase (se 6 (by rfl) ⟨6981, by rfl⟩ : syracuseStep 297877 = 13963) (by norm_num)
theorem B134041 : Blo 115785 134041 := bbase (se 2 (by rfl) ⟨50265, by rfl⟩ : syracuseStep 134041 = 100531) (by norm_num)
theorem B396197 : Blo 115785 396197 := bbase (se 4 (by rfl) ⟨37143, by rfl⟩ : syracuseStep 396197 = 74287) (by norm_num)
theorem B199597 : Blo 115785 199597 := bbase (se 3 (by rfl) ⟨37424, by rfl⟩ : syracuseStep 199597 = 74849) (by norm_num)
theorem B134077 : Blo 115785 134077 := bbase (se 3 (by rfl) ⟨25139, by rfl⟩ : syracuseStep 134077 = 50279) (by norm_num)
theorem B265157 : Blo 115785 265157 := bbase (se 4 (by rfl) ⟨24858, by rfl⟩ : syracuseStep 265157 = 49717) (by norm_num)
theorem B134113 : Blo 115785 134113 := bbase (se 2 (by rfl) ⟨50292, by rfl⟩ : syracuseStep 134113 = 100585) (by norm_num)
theorem B429029 : Blo 115785 429029 := bbase (se 4 (by rfl) ⟨40221, by rfl⟩ : syracuseStep 429029 = 80443) (by norm_num)
theorem B297989 : Blo 115785 297989 := bbase (se 4 (by rfl) ⟨27936, by rfl⟩ : syracuseStep 297989 = 55873) (by norm_num)
theorem B199685 : Blo 115785 199685 := bbase (se 4 (by rfl) ⟨18720, by rfl⟩ : syracuseStep 199685 = 37441) (by norm_num)
theorem B134149 : Blo 115785 134149 := bbase (se 4 (by rfl) ⟨12576, by rfl⟩ : syracuseStep 134149 = 25153) (by norm_num)
theorem B265229 : Blo 115785 265229 := bbase (se 3 (by rfl) ⟨49730, by rfl⟩ : syracuseStep 265229 = 99461) (by norm_num)
theorem B134185 : Blo 115785 134185 := bbase (se 2 (by rfl) ⟨50319, by rfl⟩ : syracuseStep 134185 = 100639) (by norm_num)
theorem B134221 : Blo 115785 134221 := bbase (se 3 (by rfl) ⟨25166, by rfl⟩ : syracuseStep 134221 = 50333) (by norm_num)
theorem B265301 : Blo 115785 265301 := bbase (se 8 (by rfl) ⟨1554, by rfl⟩ : syracuseStep 265301 = 3109) (by norm_num)
theorem B134257 : Blo 115785 134257 := bbase (se 2 (by rfl) ⟨50346, by rfl⟩ : syracuseStep 134257 = 100693) (by norm_num)
theorem B199813 : Blo 115785 199813 := bbase (se 4 (by rfl) ⟨18732, by rfl⟩ : syracuseStep 199813 = 37465) (by norm_num)
theorem B494741 : Blo 115785 494741 := bbase (se 6 (by rfl) ⟨11595, by rfl⟩ : syracuseStep 494741 = 23191) (by norm_num)
theorem B134293 : Blo 115785 134293 := bbase (se 6 (by rfl) ⟨3147, by rfl⟩ : syracuseStep 134293 = 6295) (by norm_num)
theorem B265373 : Blo 115785 265373 := bbase (se 3 (by rfl) ⟨49757, by rfl⟩ : syracuseStep 265373 = 99515) (by norm_num)
theorem B134329 : Blo 115785 134329 := bbase (se 2 (by rfl) ⟨50373, by rfl⟩ : syracuseStep 134329 = 100747) (by norm_num)
theorem B298181 : Blo 115785 298181 := bbase (se 4 (by rfl) ⟨27954, by rfl⟩ : syracuseStep 298181 = 55909) (by norm_num)
theorem B199901 : Blo 115785 199901 := bbase (se 3 (by rfl) ⟨37481, by rfl⟩ : syracuseStep 199901 = 74963) (by norm_num)
theorem B134365 : Blo 115785 134365 := bbase (se 3 (by rfl) ⟨25193, by rfl⟩ : syracuseStep 134365 = 50387) (by norm_num)
theorem B265445 : Blo 115785 265445 := bbase (se 4 (by rfl) ⟨24885, by rfl⟩ : syracuseStep 265445 = 49771) (by norm_num)
theorem B134401 : Blo 115785 134401 := bbase (se 2 (by rfl) ⟨50400, by rfl⟩ : syracuseStep 134401 = 100801) (by norm_num)
theorem B134437 : Blo 115785 134437 := bbase (se 4 (by rfl) ⟨12603, by rfl⟩ : syracuseStep 134437 = 25207) (by norm_num)
theorem B265517 : Blo 115785 265517 := bbase (se 3 (by rfl) ⟨49784, by rfl⟩ : syracuseStep 265517 = 99569) (by norm_num)
theorem B134473 : Blo 115785 134473 := bbase (se 2 (by rfl) ⟨50427, by rfl⟩ : syracuseStep 134473 = 100855) (by norm_num)
theorem B396629 : Blo 115785 396629 := bbase (se 11 (by rfl) ⟨290, by rfl⟩ : syracuseStep 396629 = 581) (by norm_num)
theorem B200029 : Blo 115785 200029 := bbase (se 3 (by rfl) ⟨37505, by rfl⟩ : syracuseStep 200029 = 75011) (by norm_num)
theorem B134509 : Blo 115785 134509 := bbase (se 3 (by rfl) ⟨25220, by rfl⟩ : syracuseStep 134509 = 50441) (by norm_num)
theorem B265589 : Blo 115785 265589 := bbase (se 5 (by rfl) ⟨12449, by rfl⟩ : syracuseStep 265589 = 24899) (by norm_num)
theorem B494981 : Blo 115785 494981 := bbase (se 4 (by rfl) ⟨46404, by rfl⟩ : syracuseStep 494981 = 92809) (by norm_num)
theorem B134545 : Blo 115785 134545 := bbase (se 2 (by rfl) ⟨50454, by rfl⟩ : syracuseStep 134545 = 100909) (by norm_num)
theorem B200117 : Blo 115785 200117 := bbase (se 5 (by rfl) ⟨9380, by rfl⟩ : syracuseStep 200117 = 18761) (by norm_num)
theorem B134581 : Blo 115785 134581 := bbase (se 5 (by rfl) ⟨6308, by rfl⟩ : syracuseStep 134581 = 12617) (by norm_num)
theorem B265661 : Blo 115785 265661 := bbase (se 3 (by rfl) ⟨49811, by rfl⟩ : syracuseStep 265661 = 99623) (by norm_num)
theorem B134617 : Blo 115785 134617 := bbase (se 2 (by rfl) ⟨50481, by rfl⟩ : syracuseStep 134617 = 100963) (by norm_num)
theorem B134653 : Blo 115785 134653 := bbase (se 3 (by rfl) ⟨25247, by rfl⟩ : syracuseStep 134653 = 50495) (by norm_num)
theorem B265733 : Blo 115785 265733 := bbase (se 4 (by rfl) ⟨24912, by rfl⟩ : syracuseStep 265733 = 49825) (by norm_num)
theorem B167437 : Blo 115785 167437 := bbase (se 3 (by rfl) ⟨31394, by rfl⟩ : syracuseStep 167437 = 62789) (by norm_num)
theorem B331285 : Blo 115785 331285 := bbase (se 6 (by rfl) ⟨7764, by rfl⟩ : syracuseStep 331285 = 15529) (by norm_num)
theorem B298525 : Blo 115785 298525 := bbase (se 3 (by rfl) ⟨55973, by rfl⟩ : syracuseStep 298525 = 111947) (by norm_num)
theorem B134689 : Blo 115785 134689 := bbase (se 2 (by rfl) ⟨50508, by rfl⟩ : syracuseStep 134689 = 101017) (by norm_num)
theorem B200245 : Blo 115785 200245 := bbase (se 5 (by rfl) ⟨9386, by rfl⟩ : syracuseStep 200245 = 18773) (by norm_num)
theorem B134725 : Blo 115785 134725 := bbase (se 4 (by rfl) ⟨12630, by rfl⟩ : syracuseStep 134725 = 25261) (by norm_num)
theorem B265805 : Blo 115785 265805 := bbase (se 3 (by rfl) ⟨49838, by rfl⟩ : syracuseStep 265805 = 99677) (by norm_num)
theorem B298637 : Blo 115785 298637 := bbase (se 3 (by rfl) ⟨55994, by rfl⟩ : syracuseStep 298637 = 111989) (by norm_num)
theorem B200333 : Blo 115785 200333 := bbase (se 3 (by rfl) ⟨37562, by rfl⟩ : syracuseStep 200333 = 75125) (by norm_num)
theorem B265877 : Blo 115785 265877 := bbase (se 6 (by rfl) ⟨6231, by rfl⟩ : syracuseStep 265877 = 12463) (by norm_num)
theorem B331445 : Blo 115785 331445 := bbase (se 5 (by rfl) ⟨15536, by rfl⟩ : syracuseStep 331445 = 31073) (by norm_num)
theorem B265949 : Blo 115785 265949 := bbase (se 3 (by rfl) ⟨49865, by rfl⟩ : syracuseStep 265949 = 99731) (by norm_num)
theorem B397061 : Blo 115785 397061 := bbase (se 4 (by rfl) ⟨37224, by rfl⟩ : syracuseStep 397061 = 74449) (by norm_num)
theorem B200461 : Blo 115785 200461 := bbase (se 3 (by rfl) ⟨37586, by rfl⟩ : syracuseStep 200461 = 75173) (by norm_num)
theorem B266021 : Blo 115785 266021 := bbase (se 4 (by rfl) ⟨24939, by rfl⟩ : syracuseStep 266021 = 49879) (by norm_num)
theorem B298829 : Blo 115785 298829 := bbase (se 3 (by rfl) ⟨56030, by rfl⟩ : syracuseStep 298829 = 112061) (by norm_num)
theorem B167773 : Blo 115785 167773 := bbase (se 3 (by rfl) ⟨31457, by rfl⟩ : syracuseStep 167773 = 62915) (by norm_num)
theorem B200549 : Blo 115785 200549 := bbase (se 4 (by rfl) ⟨18801, by rfl⟩ : syracuseStep 200549 = 37603) (by norm_num)
theorem B266093 : Blo 115785 266093 := bbase (se 3 (by rfl) ⟨49892, by rfl⟩ : syracuseStep 266093 = 99785) (by norm_num)
theorem B331685 : Blo 115785 331685 := bbase (se 4 (by rfl) ⟨31095, by rfl⟩ : syracuseStep 331685 = 62191) (by norm_num)
theorem B266165 : Blo 115785 266165 := bbase (se 5 (by rfl) ⟨12476, by rfl⟩ : syracuseStep 266165 = 24953) (by norm_num)
theorem B200677 : Blo 115785 200677 := bbase (se 4 (by rfl) ⟨18813, by rfl⟩ : syracuseStep 200677 = 37627) (by norm_num)
theorem B266237 : Blo 115785 266237 := bbase (se 3 (by rfl) ⟨49919, by rfl⟩ : syracuseStep 266237 = 99839) (by norm_num)
theorem B167989 : Blo 115785 167989 := bbase (se 5 (by rfl) ⟨7874, by rfl⟩ : syracuseStep 167989 = 15749) (by norm_num)
theorem B200765 : Blo 115785 200765 := bbase (se 3 (by rfl) ⟨37643, by rfl⟩ : syracuseStep 200765 = 75287) (by norm_num)
theorem B266309 : Blo 115785 266309 := bbase (se 4 (by rfl) ⟨24966, by rfl⟩ : syracuseStep 266309 = 49933) (by norm_num)
theorem B331877 : Blo 115785 331877 := bbase (se 4 (by rfl) ⟨31113, by rfl⟩ : syracuseStep 331877 = 62227) (by norm_num)
theorem B594053 : Blo 115785 594053 := bbase (se 4 (by rfl) ⟨55692, by rfl⟩ : syracuseStep 594053 = 111385) (by norm_num)
theorem B266381 : Blo 115785 266381 := bbase (se 3 (by rfl) ⟨49946, by rfl⟩ : syracuseStep 266381 = 99893) (by norm_num)
theorem B299173 : Blo 115785 299173 := bbase (se 4 (by rfl) ⟨28047, by rfl⟩ : syracuseStep 299173 = 56095) (by norm_num)
theorem B200885 : Blo 115785 200885 := bbase (se 5 (by rfl) ⟨9416, by rfl⟩ : syracuseStep 200885 = 18833) (by norm_num)
theorem B397493 : Blo 115785 397493 := bbase (se 5 (by rfl) ⟨18632, by rfl⟩ : syracuseStep 397493 = 37265) (by norm_num)
theorem B200893 : Blo 115785 200893 := bbase (se 3 (by rfl) ⟨37667, by rfl⟩ : syracuseStep 200893 = 75335) (by norm_num)
theorem B266453 : Blo 115785 266453 := bbase (se 7 (by rfl) ⟨3122, by rfl⟩ : syracuseStep 266453 = 6245) (by norm_num)
theorem B299285 : Blo 115785 299285 := bbase (se 6 (by rfl) ⟨7014, by rfl⟩ : syracuseStep 299285 = 14029) (by norm_num)
theorem B200981 : Blo 115785 200981 := bbase (se 6 (by rfl) ⟨4710, by rfl⟩ : syracuseStep 200981 = 9421) (by norm_num)
theorem B200989 : Blo 115785 200989 := bbase (se 3 (by rfl) ⟨37685, by rfl⟩ : syracuseStep 200989 = 75371) (by norm_num)
theorem B266525 : Blo 115785 266525 := bbase (se 3 (by rfl) ⟨49973, by rfl⟩ : syracuseStep 266525 = 99947) (by norm_num)
theorem B1118549 : Blo 115785 1118549 := bbase (se 10 (by rfl) ⟨1638, by rfl⟩ : syracuseStep 1118549 = 3277) (by norm_num)
theorem B266597 : Blo 115785 266597 := bbase (se 4 (by rfl) ⟨24993, by rfl⟩ : syracuseStep 266597 = 49987) (by norm_num)
theorem B201109 : Blo 115785 201109 := bbase (se 6 (by rfl) ⟨4713, by rfl⟩ : syracuseStep 201109 = 9427) (by norm_num)
theorem B168365 : Blo 115785 168365 := bbase (se 3 (by rfl) ⟨31568, by rfl⟩ : syracuseStep 168365 = 63137) (by norm_num)
theorem B266669 : Blo 115785 266669 := bbase (se 3 (by rfl) ⟨50000, by rfl⟩ : syracuseStep 266669 = 100001) (by norm_num)
theorem B299477 : Blo 115785 299477 := bbase (se 7 (by rfl) ⟨3509, by rfl⟩ : syracuseStep 299477 = 7019) (by norm_num)
theorem B201197 : Blo 115785 201197 := bbase (se 3 (by rfl) ⟨37724, by rfl⟩ : syracuseStep 201197 = 75449) (by norm_num)
theorem B266741 : Blo 115785 266741 := bbase (se 5 (by rfl) ⟨12503, by rfl⟩ : syracuseStep 266741 = 25007) (by norm_num)
theorem B266813 : Blo 115785 266813 := bbase (se 3 (by rfl) ⟨50027, by rfl⟩ : syracuseStep 266813 = 100055) (by norm_num)
theorem B397925 : Blo 115785 397925 := bbase (se 4 (by rfl) ⟨37305, by rfl⟩ : syracuseStep 397925 = 74611) (by norm_num)
theorem B201325 : Blo 115785 201325 := bbase (se 3 (by rfl) ⟨37748, by rfl⟩ : syracuseStep 201325 = 75497) (by norm_num)
theorem B266885 : Blo 115785 266885 := bbase (se 4 (by rfl) ⟨25020, by rfl⟩ : syracuseStep 266885 = 50041) (by norm_num)
theorem B201413 : Blo 115785 201413 := bbase (se 4 (by rfl) ⟨18882, by rfl⟩ : syracuseStep 201413 = 37765) (by norm_num)
theorem B266957 : Blo 115785 266957 := bbase (se 3 (by rfl) ⟨50054, by rfl⟩ : syracuseStep 266957 = 100109) (by norm_num)
theorem B267029 : Blo 115785 267029 := bbase (se 6 (by rfl) ⟨6258, by rfl⟩ : syracuseStep 267029 = 12517) (by norm_num)
theorem B299821 : Blo 115785 299821 := bbase (se 3 (by rfl) ⟨56216, by rfl⟩ : syracuseStep 299821 = 112433) (by norm_num)
theorem B201541 : Blo 115785 201541 := bbase (se 4 (by rfl) ⟨18894, by rfl⟩ : syracuseStep 201541 = 37789) (by norm_num)
theorem B267101 : Blo 115785 267101 := bbase (se 3 (by rfl) ⟨50081, by rfl⟩ : syracuseStep 267101 = 100163) (by norm_num)
theorem B299933 : Blo 115785 299933 := bbase (se 3 (by rfl) ⟨56237, by rfl⟩ : syracuseStep 299933 = 112475) (by norm_num)
theorem B201629 : Blo 115785 201629 := bbase (se 3 (by rfl) ⟨37805, by rfl⟩ : syracuseStep 201629 = 75611) (by norm_num)
theorem B267173 : Blo 115785 267173 := bbase (se 4 (by rfl) ⟨25047, by rfl⟩ : syracuseStep 267173 = 50095) (by norm_num)
theorem B267245 : Blo 115785 267245 := bbase (se 3 (by rfl) ⟨50108, by rfl⟩ : syracuseStep 267245 = 100217) (by norm_num)
theorem B398357 : Blo 115785 398357 := bbase (se 6 (by rfl) ⟨9336, by rfl⟩ : syracuseStep 398357 = 18673) (by norm_num)
theorem B201757 : Blo 115785 201757 := bbase (se 3 (by rfl) ⟨37829, by rfl⟩ : syracuseStep 201757 = 75659) (by norm_num)
theorem B267317 : Blo 115785 267317 := bbase (se 5 (by rfl) ⟨12530, by rfl⟩ : syracuseStep 267317 = 25061) (by norm_num)
theorem B332869 : Blo 115785 332869 := bbase (se 4 (by rfl) ⟨31206, by rfl⟩ : syracuseStep 332869 = 62413) (by norm_num)
theorem B300125 : Blo 115785 300125 := bbase (se 3 (by rfl) ⟨56273, by rfl⟩ : syracuseStep 300125 = 112547) (by norm_num)
theorem B201845 : Blo 115785 201845 := bbase (se 5 (by rfl) ⟨9461, by rfl⟩ : syracuseStep 201845 = 18923) (by norm_num)
theorem B267389 : Blo 115785 267389 := bbase (se 3 (by rfl) ⟨50135, by rfl⟩ : syracuseStep 267389 = 100271) (by norm_num)
theorem B267461 : Blo 115785 267461 := bbase (se 4 (by rfl) ⟨25074, by rfl⟩ : syracuseStep 267461 = 50149) (by norm_num)
theorem B136417 : Blo 115785 136417 := bbase (se 2 (by rfl) ⟨51156, by rfl⟩ : syracuseStep 136417 = 102313) (by norm_num)
theorem B201973 : Blo 115785 201973 := bbase (se 5 (by rfl) ⟨9467, by rfl⟩ : syracuseStep 201973 = 18935) (by norm_num)
theorem B267533 : Blo 115785 267533 := bbase (se 3 (by rfl) ⟨50162, by rfl⟩ : syracuseStep 267533 = 100325) (by norm_num)
theorem B202061 : Blo 115785 202061 := bbase (se 3 (by rfl) ⟨37886, by rfl⟩ : syracuseStep 202061 = 75773) (by norm_num)
theorem B267605 : Blo 115785 267605 := bbase (se 14 (by rfl) ⟨24, by rfl⟩ : syracuseStep 267605 = 49) (by norm_num)
theorem B595349 : Blo 115785 595349 := bbase (se 6 (by rfl) ⟨13953, by rfl⟩ : syracuseStep 595349 = 27907) (by norm_num)
theorem B267677 : Blo 115785 267677 := bbase (se 3 (by rfl) ⟨50189, by rfl⟩ : syracuseStep 267677 = 100379) (by norm_num)
theorem B300469 : Blo 115785 300469 := bbase (se 5 (by rfl) ⟨14084, by rfl⟩ : syracuseStep 300469 = 28169) (by norm_num)
theorem B398789 : Blo 115785 398789 := bbase (se 4 (by rfl) ⟨37386, by rfl⟩ : syracuseStep 398789 = 74773) (by norm_num)
theorem B267749 : Blo 115785 267749 := bbase (se 4 (by rfl) ⟨25101, by rfl⟩ : syracuseStep 267749 = 50203) (by norm_num)
theorem B300581 : Blo 115785 300581 := bbase (se 4 (by rfl) ⟨28179, by rfl⟩ : syracuseStep 300581 = 56359) (by norm_num)
theorem B267821 : Blo 115785 267821 := bbase (se 3 (by rfl) ⟨50216, by rfl⟩ : syracuseStep 267821 = 100433) (by norm_num)
theorem B497269 : Blo 115785 497269 := bbase (se 5 (by rfl) ⟨23309, by rfl⟩ : syracuseStep 497269 = 46619) (by norm_num)
theorem B267893 : Blo 115785 267893 := bbase (se 5 (by rfl) ⟨12557, by rfl⟩ : syracuseStep 267893 = 25115) (by norm_num)
theorem B267965 : Blo 115785 267965 := bbase (se 3 (by rfl) ⟨50243, by rfl⟩ : syracuseStep 267965 = 100487) (by norm_num)
theorem B300773 : Blo 115785 300773 := bbase (se 4 (by rfl) ⟨28197, by rfl⟩ : syracuseStep 300773 = 56395) (by norm_num)
theorem B562949 : Blo 115785 562949 := bbase (se 4 (by rfl) ⟨52776, by rfl⟩ : syracuseStep 562949 = 105553) (by norm_num)
theorem B268037 : Blo 115785 268037 := bbase (se 4 (by rfl) ⟨25128, by rfl⟩ : syracuseStep 268037 = 50257) (by norm_num)
theorem B169789 : Blo 115785 169789 := bbase (se 3 (by rfl) ⟨31835, by rfl⟩ : syracuseStep 169789 = 63671) (by norm_num)
theorem B268109 : Blo 115785 268109 := bbase (se 3 (by rfl) ⟨50270, by rfl⟩ : syracuseStep 268109 = 100541) (by norm_num)
theorem B399221 : Blo 115785 399221 := bbase (se 5 (by rfl) ⟨18713, by rfl⟩ : syracuseStep 399221 = 37427) (by norm_num)
theorem B202637 : Blo 115785 202637 := bbase (se 3 (by rfl) ⟨37994, by rfl⟩ : syracuseStep 202637 = 75989) (by norm_num)
theorem B268181 : Blo 115785 268181 := bbase (se 6 (by rfl) ⟨6285, by rfl⟩ : syracuseStep 268181 = 12571) (by norm_num)
theorem B890837 : Blo 115785 890837 := bbase (se 7 (by rfl) ⟨10439, by rfl⟩ : syracuseStep 890837 = 20879) (by norm_num)
theorem B268253 : Blo 115785 268253 := bbase (se 3 (by rfl) ⟨50297, by rfl⟩ : syracuseStep 268253 = 100595) (by norm_num)
theorem B268325 : Blo 115785 268325 := bbase (se 4 (by rfl) ⟨25155, by rfl⟩ : syracuseStep 268325 = 50311) (by norm_num)
theorem B301117 : Blo 115785 301117 := bbase (se 3 (by rfl) ⟨56459, by rfl⟩ : syracuseStep 301117 = 112919) (by norm_num)
theorem B268397 : Blo 115785 268397 := bbase (se 3 (by rfl) ⟨50324, by rfl⟩ : syracuseStep 268397 = 100649) (by norm_num)
theorem B333973 : Blo 115785 333973 := bbase (se 6 (by rfl) ⟨7827, by rfl⟩ : syracuseStep 333973 = 15655) (by norm_num)
theorem B301229 : Blo 115785 301229 := bbase (se 3 (by rfl) ⟨56480, by rfl⟩ : syracuseStep 301229 = 112961) (by norm_num)
theorem B268469 : Blo 115785 268469 := bbase (se 5 (by rfl) ⟨12584, by rfl⟩ : syracuseStep 268469 = 25169) (by norm_num)
theorem B268541 : Blo 115785 268541 := bbase (se 3 (by rfl) ⟨50351, by rfl⟩ : syracuseStep 268541 = 100703) (by norm_num)
theorem B399653 : Blo 115785 399653 := bbase (se 4 (by rfl) ⟨37467, by rfl⟩ : syracuseStep 399653 = 74935) (by norm_num)
theorem B268613 : Blo 115785 268613 := bbase (se 4 (by rfl) ⟨25182, by rfl⟩ : syracuseStep 268613 = 50365) (by norm_num)
theorem B301421 : Blo 115785 301421 := bbase (se 3 (by rfl) ⟨56516, by rfl⟩ : syracuseStep 301421 = 113033) (by norm_num)
theorem B268685 : Blo 115785 268685 := bbase (se 3 (by rfl) ⟨50378, by rfl⟩ : syracuseStep 268685 = 100757) (by norm_num)
theorem B170381 : Blo 115785 170381 := bbase (se 3 (by rfl) ⟨31946, by rfl⟩ : syracuseStep 170381 = 63893) (by norm_num)
theorem B268757 : Blo 115785 268757 := bbase (se 7 (by rfl) ⟨3149, by rfl⟩ : syracuseStep 268757 = 6299) (by norm_num)
theorem B170461 : Blo 115785 170461 := bbase (se 3 (by rfl) ⟨31961, by rfl⟩ : syracuseStep 170461 = 63923) (by norm_num)
theorem B203293 : Blo 115785 203293 := bbase (se 3 (by rfl) ⟨38117, by rfl⟩ : syracuseStep 203293 = 76235) (by norm_num)
theorem B268829 : Blo 115785 268829 := bbase (se 3 (by rfl) ⟨50405, by rfl⟩ : syracuseStep 268829 = 100811) (by norm_num)
theorem B268901 : Blo 115785 268901 := bbase (se 4 (by rfl) ⟨25209, by rfl⟩ : syracuseStep 268901 = 50419) (by norm_num)
theorem B596645 : Blo 115785 596645 := bbase (se 4 (by rfl) ⟨55935, by rfl⟩ : syracuseStep 596645 = 111871) (by norm_num)
theorem B268973 : Blo 115785 268973 := bbase (se 3 (by rfl) ⟨50432, by rfl⟩ : syracuseStep 268973 = 100865) (by norm_num)
theorem B301765 : Blo 115785 301765 := bbase (se 4 (by rfl) ⟨28290, by rfl⟩ : syracuseStep 301765 = 56581) (by norm_num)
theorem B301781 : Blo 115785 301781 := bbase (se 7 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 301781 = 7073) (by norm_num)
theorem B400085 : Blo 115785 400085 := bbase (se 7 (by rfl) ⟨4688, by rfl⟩ : syracuseStep 400085 = 9377) (by norm_num)
theorem B269045 : Blo 115785 269045 := bbase (se 5 (by rfl) ⟨12611, by rfl⟩ : syracuseStep 269045 = 25223) (by norm_num)
theorem B301877 : Blo 115785 301877 := bbase (se 5 (by rfl) ⟨14150, by rfl⟩ : syracuseStep 301877 = 28301) (by norm_num)
theorem B269117 : Blo 115785 269117 := bbase (se 3 (by rfl) ⟨50459, by rfl⟩ : syracuseStep 269117 = 100919) (by norm_num)
theorem B269189 : Blo 115785 269189 := bbase (se 4 (by rfl) ⟨25236, by rfl⟩ : syracuseStep 269189 = 50473) (by norm_num)
theorem B269261 : Blo 115785 269261 := bbase (se 3 (by rfl) ⟨50486, by rfl⟩ : syracuseStep 269261 = 100973) (by norm_num)
theorem B302069 : Blo 115785 302069 := bbase (se 5 (by rfl) ⟨14159, by rfl⟩ : syracuseStep 302069 = 28319) (by norm_num)
theorem B269333 : Blo 115785 269333 := bbase (se 6 (by rfl) ⟨6312, by rfl⟩ : syracuseStep 269333 = 12625) (by norm_num)
theorem B498757 : Blo 115785 498757 := bbase (se 4 (by rfl) ⟨46758, by rfl⟩ : syracuseStep 498757 = 93517) (by norm_num)
theorem B498773 : Blo 115785 498773 := bbase (se 8 (by rfl) ⟨2922, by rfl⟩ : syracuseStep 498773 = 5845) (by norm_num)
theorem B269405 : Blo 115785 269405 := bbase (se 3 (by rfl) ⟨50513, by rfl⟩ : syracuseStep 269405 = 101027) (by norm_num)
theorem B400517 : Blo 115785 400517 := bbase (se 4 (by rfl) ⟨37548, by rfl⟩ : syracuseStep 400517 = 75097) (by norm_num)
theorem B302221 : Blo 115785 302221 := bbase (se 3 (by rfl) ⟨56666, by rfl⟩ : syracuseStep 302221 = 113333) (by norm_num)
theorem B269477 : Blo 115785 269477 := bbase (se 4 (by rfl) ⟨25263, by rfl⟩ : syracuseStep 269477 = 50527) (by norm_num)
theorem B269525 : Blo 115785 269525 := bbase (se 7 (by rfl) ⟨3158, by rfl⟩ : syracuseStep 269525 = 6317) (by norm_num)
theorem B204005 : Blo 115785 204005 := bbase (se 4 (by rfl) ⟨19125, by rfl⟩ : syracuseStep 204005 = 38251) (by norm_num)
theorem B302413 : Blo 115785 302413 := bbase (se 3 (by rfl) ⟨56702, by rfl⟩ : syracuseStep 302413 = 113405) (by norm_num)
theorem B302525 : Blo 115785 302525 := bbase (se 3 (by rfl) ⟨56723, by rfl⟩ : syracuseStep 302525 = 113447) (by norm_num)
theorem B400949 : Blo 115785 400949 := bbase (se 5 (by rfl) ⟨18794, by rfl⟩ : syracuseStep 400949 = 37589) (by norm_num)
theorem B859733 : Blo 115785 859733 := bbase (se 8 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 859733 = 10075) (by norm_num)
theorem B335477 : Blo 115785 335477 := bbase (se 5 (by rfl) ⟨15725, by rfl⟩ : syracuseStep 335477 = 31451) (by norm_num)
theorem B302717 : Blo 115785 302717 := bbase (se 3 (by rfl) ⟨56759, by rfl⟩ : syracuseStep 302717 = 113519) (by norm_num)
theorem B564965 : Blo 115785 564965 := bbase (se 4 (by rfl) ⟨52965, by rfl⟩ : syracuseStep 564965 = 105931) (by norm_num)
theorem B270101 : Blo 115785 270101 := bbase (se 6 (by rfl) ⟨6330, by rfl⟩ : syracuseStep 270101 = 12661) (by norm_num)
theorem B434069 : Blo 115785 434069 := bbase (se 6 (by rfl) ⟨10173, by rfl⟩ : syracuseStep 434069 = 20347) (by norm_num)
theorem B139165 : Blo 115785 139165 := bbase (se 3 (by rfl) ⟨26093, by rfl⟩ : syracuseStep 139165 = 52187) (by norm_num)
theorem B565157 : Blo 115785 565157 := bbase (se 4 (by rfl) ⟨52983, by rfl⟩ : syracuseStep 565157 = 105967) (by norm_num)
theorem B597941 : Blo 115785 597941 := bbase (se 5 (by rfl) ⟨28028, by rfl⟩ : syracuseStep 597941 = 56057) (by norm_num)
theorem B303061 : Blo 115785 303061 := bbase (se 7 (by rfl) ⟨3551, by rfl⟩ : syracuseStep 303061 = 7103) (by norm_num)
theorem B401381 : Blo 115785 401381 := bbase (se 4 (by rfl) ⟨37629, by rfl⟩ : syracuseStep 401381 = 75259) (by norm_num)
theorem B303173 : Blo 115785 303173 := bbase (se 4 (by rfl) ⟨28422, by rfl⟩ : syracuseStep 303173 = 56845) (by norm_num)
theorem B303421 : Blo 115785 303421 := bbase (se 3 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 303421 = 113783) (by norm_num)
theorem B401813 : Blo 115785 401813 := bbase (se 6 (by rfl) ⟨9417, by rfl⟩ : syracuseStep 401813 = 18835) (by norm_num)
theorem B140069 : Blo 115785 140069 := bbase (se 4 (by rfl) ⟨13131, by rfl⟩ : syracuseStep 140069 = 26263) (by norm_num)
theorem B402245 : Blo 115785 402245 := bbase (se 4 (by rfl) ⟨37710, by rfl⟩ : syracuseStep 402245 = 75421) (by norm_num)
theorem B140329 : Blo 115785 140329 := bbase (se 2 (by rfl) ⟨52623, by rfl⟩ : syracuseStep 140329 = 105247) (by norm_num)
theorem B337061 : Blo 115785 337061 := bbase (se 4 (by rfl) ⟨31599, by rfl⟩ : syracuseStep 337061 = 63199) (by norm_num)
theorem B664757 : Blo 115785 664757 := bbase (se 5 (by rfl) ⟨31160, by rfl⟩ : syracuseStep 664757 = 62321) (by norm_num)
theorem B599237 : Blo 115785 599237 := bbase (se 4 (by rfl) ⟨56178, by rfl⟩ : syracuseStep 599237 = 112357) (by norm_num)
theorem B140521 : Blo 115785 140521 := bbase (se 2 (by rfl) ⟨52695, by rfl⟩ : syracuseStep 140521 = 105391) (by norm_num)
theorem B402677 : Blo 115785 402677 := bbase (se 5 (by rfl) ⟨18875, by rfl⟩ : syracuseStep 402677 = 37751) (by norm_num)
theorem B140545 : Blo 115785 140545 := bbase (se 2 (by rfl) ⟨52704, by rfl⟩ : syracuseStep 140545 = 105409) (by norm_num)
theorem B140549 : Blo 115785 140549 := bbase (se 4 (by rfl) ⟨13176, by rfl⟩ : syracuseStep 140549 = 26353) (by norm_num)
theorem B501029 : Blo 115785 501029 := bbase (se 4 (by rfl) ⟨46971, by rfl⟩ : syracuseStep 501029 = 93943) (by norm_num)
theorem B2041301 : Blo 115785 2041301 := bbase (se 7 (by rfl) ⟨23921, by rfl⟩ : syracuseStep 2041301 = 47843) (by norm_num)
theorem B173693 : Blo 115785 173693 := bbase (se 3 (by rfl) ⟨32567, by rfl⟩ : syracuseStep 173693 = 65135) (by norm_num)
theorem B173717 : Blo 115785 173717 := bbase (se 6 (by rfl) ⟨4071, by rfl⟩ : syracuseStep 173717 = 8143) (by norm_num)
theorem B403109 : Blo 115785 403109 := bbase (se 4 (by rfl) ⟨37791, by rfl⟩ : syracuseStep 403109 = 75583) (by norm_num)
theorem B173741 : Blo 115785 173741 := bbase (se 3 (by rfl) ⟨32576, by rfl⟩ : syracuseStep 173741 = 65153) (by norm_num)
theorem B173765 : Blo 115785 173765 := bbase (se 4 (by rfl) ⟨16290, by rfl⟩ : syracuseStep 173765 = 32581) (by norm_num)
theorem B173789 : Blo 115785 173789 := bbase (se 3 (by rfl) ⟨32585, by rfl⟩ : syracuseStep 173789 = 65171) (by norm_num)
theorem B173813 : Blo 115785 173813 := bbase (se 5 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 173813 = 16295) (by norm_num)
theorem B141049 : Blo 115785 141049 := bbase (se 2 (by rfl) ⟨52893, by rfl⟩ : syracuseStep 141049 = 105787) (by norm_num)
theorem B173837 : Blo 115785 173837 := bbase (se 3 (by rfl) ⟨32594, by rfl⟩ : syracuseStep 173837 = 65189) (by norm_num)
theorem B173861 : Blo 115785 173861 := bbase (se 4 (by rfl) ⟨16299, by rfl⟩ : syracuseStep 173861 = 32599) (by norm_num)
theorem B173885 : Blo 115785 173885 := bbase (se 3 (by rfl) ⟨32603, by rfl⟩ : syracuseStep 173885 = 65207) (by norm_num)
theorem B337733 : Blo 115785 337733 := bbase (se 4 (by rfl) ⟨31662, by rfl⟩ : syracuseStep 337733 = 63325) (by norm_num)
theorem B173909 : Blo 115785 173909 := bbase (se 9 (by rfl) ⟨509, by rfl⟩ : syracuseStep 173909 = 1019) (by norm_num)
theorem B141145 : Blo 115785 141145 := bbase (se 2 (by rfl) ⟨52929, by rfl⟩ : syracuseStep 141145 = 105859) (by norm_num)
theorem B173933 : Blo 115785 173933 := bbase (se 3 (by rfl) ⟨32612, by rfl⟩ : syracuseStep 173933 = 65225) (by norm_num)
theorem B173957 : Blo 115785 173957 := bbase (se 4 (by rfl) ⟨16308, by rfl⟩ : syracuseStep 173957 = 32617) (by norm_num)
theorem B173981 : Blo 115785 173981 := bbase (se 3 (by rfl) ⟨32621, by rfl⟩ : syracuseStep 173981 = 65243) (by norm_num)
theorem B141221 : Blo 115785 141221 := bbase (se 4 (by rfl) ⟨13239, by rfl⟩ : syracuseStep 141221 = 26479) (by norm_num)
theorem B174005 : Blo 115785 174005 := bbase (se 5 (by rfl) ⟨8156, by rfl⟩ : syracuseStep 174005 = 16313) (by norm_num)
theorem B174029 : Blo 115785 174029 := bbase (se 3 (by rfl) ⟨32630, by rfl⟩ : syracuseStep 174029 = 65261) (by norm_num)
theorem B567253 : Blo 115785 567253 := bbase (se 7 (by rfl) ⟨6647, by rfl⟩ : syracuseStep 567253 = 13295) (by norm_num)
theorem B174053 : Blo 115785 174053 := bbase (se 4 (by rfl) ⟨16317, by rfl⟩ : syracuseStep 174053 = 32635) (by norm_num)
theorem B174077 : Blo 115785 174077 := bbase (se 3 (by rfl) ⟨32639, by rfl⟩ : syracuseStep 174077 = 65279) (by norm_num)
theorem B174101 : Blo 115785 174101 := bbase (se 6 (by rfl) ⟨4080, by rfl⟩ : syracuseStep 174101 = 8161) (by norm_num)
theorem B174125 : Blo 115785 174125 := bbase (se 3 (by rfl) ⟨32648, by rfl⟩ : syracuseStep 174125 = 65297) (by norm_num)
theorem B174149 : Blo 115785 174149 := bbase (se 4 (by rfl) ⟨16326, by rfl⟩ : syracuseStep 174149 = 32653) (by norm_num)
theorem B403541 : Blo 115785 403541 := bbase (se 8 (by rfl) ⟨2364, by rfl⟩ : syracuseStep 403541 = 4729) (by norm_num)
theorem B174173 : Blo 115785 174173 := bbase (se 3 (by rfl) ⟨32657, by rfl⟩ : syracuseStep 174173 = 65315) (by norm_num)
theorem B174197 : Blo 115785 174197 := bbase (se 5 (by rfl) ⟨8165, by rfl⟩ : syracuseStep 174197 = 16331) (by norm_num)
theorem B174221 : Blo 115785 174221 := bbase (se 3 (by rfl) ⟨32666, by rfl⟩ : syracuseStep 174221 = 65333) (by norm_num)
theorem B174245 : Blo 115785 174245 := bbase (se 4 (by rfl) ⟨16335, by rfl⟩ : syracuseStep 174245 = 32671) (by norm_num)
theorem B174269 : Blo 115785 174269 := bbase (se 3 (by rfl) ⟨32675, by rfl⟩ : syracuseStep 174269 = 65351) (by norm_num)
theorem B174293 : Blo 115785 174293 := bbase (se 7 (by rfl) ⟨2042, by rfl⟩ : syracuseStep 174293 = 4085) (by norm_num)
theorem B403685 : Blo 115785 403685 := bbase (se 4 (by rfl) ⟨37845, by rfl⟩ : syracuseStep 403685 = 75691) (by norm_num)
theorem B174317 : Blo 115785 174317 := bbase (se 3 (by rfl) ⟨32684, by rfl⟩ : syracuseStep 174317 = 65369) (by norm_num)
theorem B338165 : Blo 115785 338165 := bbase (se 5 (by rfl) ⟨15851, by rfl⟩ : syracuseStep 338165 = 31703) (by norm_num)
theorem B174341 : Blo 115785 174341 := bbase (se 4 (by rfl) ⟨16344, by rfl⟩ : syracuseStep 174341 = 32689) (by norm_num)
theorem B174365 : Blo 115785 174365 := bbase (se 3 (by rfl) ⟨32693, by rfl⟩ : syracuseStep 174365 = 65387) (by norm_num)
theorem B174389 : Blo 115785 174389 := bbase (se 5 (by rfl) ⟨8174, by rfl⟩ : syracuseStep 174389 = 16349) (by norm_num)
theorem B174413 : Blo 115785 174413 := bbase (se 3 (by rfl) ⟨32702, by rfl⟩ : syracuseStep 174413 = 65405) (by norm_num)
theorem B665941 : Blo 115785 665941 := bbase (se 10 (by rfl) ⟨975, by rfl⟩ : syracuseStep 665941 = 1951) (by norm_num)
theorem B174437 : Blo 115785 174437 := bbase (se 4 (by rfl) ⟨16353, by rfl⟩ : syracuseStep 174437 = 32707) (by norm_num)
theorem B174461 : Blo 115785 174461 := bbase (se 3 (by rfl) ⟨32711, by rfl⟩ : syracuseStep 174461 = 65423) (by norm_num)
theorem B174485 : Blo 115785 174485 := bbase (se 6 (by rfl) ⟨4089, by rfl⟩ : syracuseStep 174485 = 8179) (by norm_num)
theorem B174509 : Blo 115785 174509 := bbase (se 3 (by rfl) ⟨32720, by rfl⟩ : syracuseStep 174509 = 65441) (by norm_num)
theorem B174533 : Blo 115785 174533 := bbase (se 4 (by rfl) ⟨16362, by rfl⟩ : syracuseStep 174533 = 32725) (by norm_num)
theorem B600533 : Blo 115785 600533 := bbase (se 7 (by rfl) ⟨7037, by rfl⟩ : syracuseStep 600533 = 14075) (by norm_num)
theorem B174557 : Blo 115785 174557 := bbase (se 3 (by rfl) ⟨32729, by rfl⟩ : syracuseStep 174557 = 65459) (by norm_num)
theorem B174581 : Blo 115785 174581 := bbase (se 5 (by rfl) ⟨8183, by rfl⟩ : syracuseStep 174581 = 16367) (by norm_num)
theorem B403973 : Blo 115785 403973 := bbase (se 4 (by rfl) ⟨37872, by rfl⟩ : syracuseStep 403973 = 75745) (by norm_num)
theorem B174605 : Blo 115785 174605 := bbase (se 3 (by rfl) ⟨32738, by rfl⟩ : syracuseStep 174605 = 65477) (by norm_num)
theorem B174629 : Blo 115785 174629 := bbase (se 4 (by rfl) ⟨16371, by rfl⟩ : syracuseStep 174629 = 32743) (by norm_num)
theorem B174653 : Blo 115785 174653 := bbase (se 3 (by rfl) ⟨32747, by rfl⟩ : syracuseStep 174653 = 65495) (by norm_num)
theorem B174677 : Blo 115785 174677 := bbase (se 8 (by rfl) ⟨1023, by rfl⟩ : syracuseStep 174677 = 2047) (by norm_num)
theorem B174701 : Blo 115785 174701 := bbase (se 3 (by rfl) ⟨32756, by rfl⟩ : syracuseStep 174701 = 65513) (by norm_num)
theorem B174725 : Blo 115785 174725 := bbase (se 4 (by rfl) ⟨16380, by rfl⟩ : syracuseStep 174725 = 32761) (by norm_num)
theorem B174749 : Blo 115785 174749 := bbase (se 3 (by rfl) ⟨32765, by rfl⟩ : syracuseStep 174749 = 65531) (by norm_num)
theorem B174773 : Blo 115785 174773 := bbase (se 5 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 174773 = 16385) (by norm_num)
theorem B174797 : Blo 115785 174797 := bbase (se 3 (by rfl) ⟨32774, by rfl⟩ : syracuseStep 174797 = 65549) (by norm_num)
theorem B174821 : Blo 115785 174821 := bbase (se 4 (by rfl) ⟨16389, by rfl⟩ : syracuseStep 174821 = 32779) (by norm_num)
theorem B174845 : Blo 115785 174845 := bbase (se 3 (by rfl) ⟨32783, by rfl⟩ : syracuseStep 174845 = 65567) (by norm_num)
theorem B174869 : Blo 115785 174869 := bbase (se 6 (by rfl) ⟨4098, by rfl⟩ : syracuseStep 174869 = 8197) (by norm_num)
theorem B142121 : Blo 115785 142121 := bbase (se 2 (by rfl) ⟨53295, by rfl⟩ : syracuseStep 142121 = 106591) (by norm_num)
theorem B174893 : Blo 115785 174893 := bbase (se 3 (by rfl) ⟨32792, by rfl⟩ : syracuseStep 174893 = 65585) (by norm_num)
theorem B469813 : Blo 115785 469813 := bbase (se 5 (by rfl) ⟨22022, by rfl⟩ : syracuseStep 469813 = 44045) (by norm_num)
theorem B174917 : Blo 115785 174917 := bbase (se 4 (by rfl) ⟨16398, by rfl⟩ : syracuseStep 174917 = 32797) (by norm_num)
theorem B174941 : Blo 115785 174941 := bbase (se 3 (by rfl) ⟨32801, by rfl⟩ : syracuseStep 174941 = 65603) (by norm_num)
theorem B174965 : Blo 115785 174965 := bbase (se 5 (by rfl) ⟨8201, by rfl⟩ : syracuseStep 174965 = 16403) (by norm_num)
theorem B174989 : Blo 115785 174989 := bbase (se 3 (by rfl) ⟨32810, by rfl⟩ : syracuseStep 174989 = 65621) (by norm_num)
theorem B175013 : Blo 115785 175013 := bbase (se 4 (by rfl) ⟨16407, by rfl⟩ : syracuseStep 175013 = 32815) (by norm_num)
theorem B175037 : Blo 115785 175037 := bbase (se 3 (by rfl) ⟨32819, by rfl⟩ : syracuseStep 175037 = 65639) (by norm_num)
theorem B175061 : Blo 115785 175061 := bbase (se 7 (by rfl) ⟨2051, by rfl⟩ : syracuseStep 175061 = 4103) (by norm_num)
theorem B338917 : Blo 115785 338917 := bbase (se 4 (by rfl) ⟨31773, by rfl⟩ : syracuseStep 338917 = 63547) (by norm_num)
theorem B175085 : Blo 115785 175085 := bbase (se 3 (by rfl) ⟨32828, by rfl⟩ : syracuseStep 175085 = 65657) (by norm_num)
theorem B175109 : Blo 115785 175109 := bbase (se 4 (by rfl) ⟨16416, by rfl⟩ : syracuseStep 175109 = 32833) (by norm_num)
theorem B175133 : Blo 115785 175133 := bbase (se 3 (by rfl) ⟨32837, by rfl⟩ : syracuseStep 175133 = 65675) (by norm_num)
theorem B371749 : Blo 115785 371749 := bbase (se 4 (by rfl) ⟨34851, by rfl⟩ : syracuseStep 371749 = 69703) (by norm_num)
theorem B175157 : Blo 115785 175157 := bbase (se 5 (by rfl) ⟨8210, by rfl⟩ : syracuseStep 175157 = 16421) (by norm_num)
theorem B175181 : Blo 115785 175181 := bbase (se 3 (by rfl) ⟨32846, by rfl⟩ : syracuseStep 175181 = 65693) (by norm_num)
theorem B175205 : Blo 115785 175205 := bbase (se 4 (by rfl) ⟨16425, by rfl⟩ : syracuseStep 175205 = 32851) (by norm_num)
theorem B175229 : Blo 115785 175229 := bbase (se 3 (by rfl) ⟨32855, by rfl⟩ : syracuseStep 175229 = 65711) (by norm_num)
theorem B797845 : Blo 115785 797845 := bbase (se 6 (by rfl) ⟨18699, by rfl⟩ : syracuseStep 797845 = 37399) (by norm_num)
theorem B175253 : Blo 115785 175253 := bbase (se 6 (by rfl) ⟨4107, by rfl⟩ : syracuseStep 175253 = 8215) (by norm_num)
theorem B339109 : Blo 115785 339109 := bbase (se 4 (by rfl) ⟨31791, by rfl⟩ : syracuseStep 339109 = 63583) (by norm_num)
theorem B175277 : Blo 115785 175277 := bbase (se 3 (by rfl) ⟨32864, by rfl⟩ : syracuseStep 175277 = 65729) (by norm_num)
theorem B175301 : Blo 115785 175301 := bbase (se 4 (by rfl) ⟨16434, by rfl⟩ : syracuseStep 175301 = 32869) (by norm_num)
theorem B175325 : Blo 115785 175325 := bbase (se 3 (by rfl) ⟨32873, by rfl⟩ : syracuseStep 175325 = 65747) (by norm_num)
theorem B175349 : Blo 115785 175349 := bbase (se 5 (by rfl) ⟨8219, by rfl⟩ : syracuseStep 175349 = 16439) (by norm_num)
theorem B142597 : Blo 115785 142597 := bbase (se 4 (by rfl) ⟨13368, by rfl⟩ : syracuseStep 142597 = 26737) (by norm_num)
theorem B175373 : Blo 115785 175373 := bbase (se 3 (by rfl) ⟨32882, by rfl⟩ : syracuseStep 175373 = 65765) (by norm_num)
theorem B142625 : Blo 115785 142625 := bbase (se 2 (by rfl) ⟨53484, by rfl⟩ : syracuseStep 142625 = 106969) (by norm_num)
theorem B175397 : Blo 115785 175397 := bbase (se 4 (by rfl) ⟨16443, by rfl⟩ : syracuseStep 175397 = 32887) (by norm_num)
theorem B175421 : Blo 115785 175421 := bbase (se 3 (by rfl) ⟨32891, by rfl⟩ : syracuseStep 175421 = 65783) (by norm_num)
theorem B175445 : Blo 115785 175445 := bbase (se 11 (by rfl) ⟨128, by rfl⟩ : syracuseStep 175445 = 257) (by norm_num)
theorem B175469 : Blo 115785 175469 := bbase (se 3 (by rfl) ⟨32900, by rfl⟩ : syracuseStep 175469 = 65801) (by norm_num)
theorem B175493 : Blo 115785 175493 := bbase (se 4 (by rfl) ⟨16452, by rfl⟩ : syracuseStep 175493 = 32905) (by norm_num)
theorem B175517 : Blo 115785 175517 := bbase (se 3 (by rfl) ⟨32909, by rfl⟩ : syracuseStep 175517 = 65819) (by norm_num)
theorem B175541 : Blo 115785 175541 := bbase (se 5 (by rfl) ⟨8228, by rfl⟩ : syracuseStep 175541 = 16457) (by norm_num)
theorem B175565 : Blo 115785 175565 := bbase (se 3 (by rfl) ⟨32918, by rfl⟩ : syracuseStep 175565 = 65837) (by norm_num)
theorem B142813 : Blo 115785 142813 := bbase (se 3 (by rfl) ⟨26777, by rfl⟩ : syracuseStep 142813 = 53555) (by norm_num)
theorem B175589 : Blo 115785 175589 := bbase (se 4 (by rfl) ⟨16461, by rfl⟩ : syracuseStep 175589 = 32923) (by norm_num)
theorem B175613 : Blo 115785 175613 := bbase (se 3 (by rfl) ⟨32927, by rfl⟩ : syracuseStep 175613 = 65855) (by norm_num)
theorem B175637 : Blo 115785 175637 := bbase (se 6 (by rfl) ⟨4116, by rfl⟩ : syracuseStep 175637 = 8233) (by norm_num)
theorem B175661 : Blo 115785 175661 := bbase (se 3 (by rfl) ⟨32936, by rfl⟩ : syracuseStep 175661 = 65873) (by norm_num)
theorem B175685 : Blo 115785 175685 := bbase (se 4 (by rfl) ⟨16470, by rfl⟩ : syracuseStep 175685 = 32941) (by norm_num)
theorem B142933 : Blo 115785 142933 := bbase (se 8 (by rfl) ⟨837, by rfl⟩ : syracuseStep 142933 = 1675) (by norm_num)
theorem B175709 : Blo 115785 175709 := bbase (se 3 (by rfl) ⟨32945, by rfl⟩ : syracuseStep 175709 = 65891) (by norm_num)
theorem B175733 : Blo 115785 175733 := bbase (se 5 (by rfl) ⟨8237, by rfl⟩ : syracuseStep 175733 = 16475) (by norm_num)
theorem B175757 : Blo 115785 175757 := bbase (se 3 (by rfl) ⟨32954, by rfl⟩ : syracuseStep 175757 = 65909) (by norm_num)
theorem B175781 : Blo 115785 175781 := bbase (se 4 (by rfl) ⟨16479, by rfl⟩ : syracuseStep 175781 = 32959) (by norm_num)
theorem B175805 : Blo 115785 175805 := bbase (se 3 (by rfl) ⟨32963, by rfl⟩ : syracuseStep 175805 = 65927) (by norm_num)
theorem B175829 : Blo 115785 175829 := bbase (se 7 (by rfl) ⟨2060, by rfl⟩ : syracuseStep 175829 = 4121) (by norm_num)
theorem B601829 : Blo 115785 601829 := bbase (se 4 (by rfl) ⟨56421, by rfl⟩ : syracuseStep 601829 = 112843) (by norm_num)
theorem B175853 : Blo 115785 175853 := bbase (se 3 (by rfl) ⟨32972, by rfl⟩ : syracuseStep 175853 = 65945) (by norm_num)
theorem B175877 : Blo 115785 175877 := bbase (se 4 (by rfl) ⟨16488, by rfl⟩ : syracuseStep 175877 = 32977) (by norm_num)
theorem B175901 : Blo 115785 175901 := bbase (se 3 (by rfl) ⟨32981, by rfl⟩ : syracuseStep 175901 = 65963) (by norm_num)
theorem B175925 : Blo 115785 175925 := bbase (se 5 (by rfl) ⟨8246, by rfl⟩ : syracuseStep 175925 = 16493) (by norm_num)
theorem B175949 : Blo 115785 175949 := bbase (se 3 (by rfl) ⟨32990, by rfl⟩ : syracuseStep 175949 = 65981) (by norm_num)
theorem B175973 : Blo 115785 175973 := bbase (se 4 (by rfl) ⟨16497, by rfl⟩ : syracuseStep 175973 = 32995) (by norm_num)
theorem B175997 : Blo 115785 175997 := bbase (se 3 (by rfl) ⟨32999, by rfl⟩ : syracuseStep 175997 = 65999) (by norm_num)
theorem B176021 : Blo 115785 176021 := bbase (se 6 (by rfl) ⟨4125, by rfl⟩ : syracuseStep 176021 = 8251) (by norm_num)
theorem B765845 : Blo 115785 765845 := bbase (se 6 (by rfl) ⟨17949, by rfl⟩ : syracuseStep 765845 = 35899) (by norm_num)
theorem B176045 : Blo 115785 176045 := bbase (se 3 (by rfl) ⟨33008, by rfl⟩ : syracuseStep 176045 = 66017) (by norm_num)
theorem B176069 : Blo 115785 176069 := bbase (se 4 (by rfl) ⟨16506, by rfl⟩ : syracuseStep 176069 = 33013) (by norm_num)
theorem B176093 : Blo 115785 176093 := bbase (se 3 (by rfl) ⟨33017, by rfl⟩ : syracuseStep 176093 = 66035) (by norm_num)
theorem B176117 : Blo 115785 176117 := bbase (se 5 (by rfl) ⟨8255, by rfl⟩ : syracuseStep 176117 = 16511) (by norm_num)
theorem B176141 : Blo 115785 176141 := bbase (se 3 (by rfl) ⟨33026, by rfl⟩ : syracuseStep 176141 = 66053) (by norm_num)
theorem B176165 : Blo 115785 176165 := bbase (se 4 (by rfl) ⟨16515, by rfl⟩ : syracuseStep 176165 = 33031) (by norm_num)
theorem B176189 : Blo 115785 176189 := bbase (se 3 (by rfl) ⟨33035, by rfl⟩ : syracuseStep 176189 = 66071) (by norm_num)
theorem B208973 : Blo 115785 208973 := bbase (se 3 (by rfl) ⟨39182, by rfl⟩ : syracuseStep 208973 = 78365) (by norm_num)
theorem B176213 : Blo 115785 176213 := bbase (se 8 (by rfl) ⟨1032, by rfl⟩ : syracuseStep 176213 = 2065) (by norm_num)
theorem B176237 : Blo 115785 176237 := bbase (se 3 (by rfl) ⟨33044, by rfl⟩ : syracuseStep 176237 = 66089) (by norm_num)
theorem B602245 : Blo 115785 602245 := bbase (se 4 (by rfl) ⟨56460, by rfl⟩ : syracuseStep 602245 = 112921) (by norm_num)
theorem B176261 : Blo 115785 176261 := bbase (se 4 (by rfl) ⟨16524, by rfl⟩ : syracuseStep 176261 = 33049) (by norm_num)
theorem B176285 : Blo 115785 176285 := bbase (se 3 (by rfl) ⟨33053, by rfl⟩ : syracuseStep 176285 = 66107) (by norm_num)
theorem B176309 : Blo 115785 176309 := bbase (se 5 (by rfl) ⟨8264, by rfl⟩ : syracuseStep 176309 = 16529) (by norm_num)
theorem B176333 : Blo 115785 176333 := bbase (se 3 (by rfl) ⟨33062, by rfl⟩ : syracuseStep 176333 = 66125) (by norm_num)
theorem B176357 : Blo 115785 176357 := bbase (se 4 (by rfl) ⟨16533, by rfl⟩ : syracuseStep 176357 = 33067) (by norm_num)
theorem B143597 : Blo 115785 143597 := bbase (se 3 (by rfl) ⟨26924, by rfl⟩ : syracuseStep 143597 = 53849) (by norm_num)
theorem B176381 : Blo 115785 176381 := bbase (se 3 (by rfl) ⟨33071, by rfl⟩ : syracuseStep 176381 = 66143) (by norm_num)
theorem B667925 : Blo 115785 667925 := bbase (se 6 (by rfl) ⟨15654, by rfl⟩ : syracuseStep 667925 = 31309) (by norm_num)
theorem B176405 : Blo 115785 176405 := bbase (se 6 (by rfl) ⟨4134, by rfl⟩ : syracuseStep 176405 = 8269) (by norm_num)
theorem B176429 : Blo 115785 176429 := bbase (se 3 (by rfl) ⟨33080, by rfl⟩ : syracuseStep 176429 = 66161) (by norm_num)
theorem B176453 : Blo 115785 176453 := bbase (se 4 (by rfl) ⟨16542, by rfl⟩ : syracuseStep 176453 = 33085) (by norm_num)
theorem B176477 : Blo 115785 176477 := bbase (se 3 (by rfl) ⟨33089, by rfl⟩ : syracuseStep 176477 = 66179) (by norm_num)
theorem B176501 : Blo 115785 176501 := bbase (se 5 (by rfl) ⟨8273, by rfl⟩ : syracuseStep 176501 = 16547) (by norm_num)
theorem B176525 : Blo 115785 176525 := bbase (se 3 (by rfl) ⟨33098, by rfl⟩ : syracuseStep 176525 = 66197) (by norm_num)
theorem B176549 : Blo 115785 176549 := bbase (se 4 (by rfl) ⟨16551, by rfl⟩ : syracuseStep 176549 = 33103) (by norm_num)
theorem B176573 : Blo 115785 176573 := bbase (se 3 (by rfl) ⟨33107, by rfl⟩ : syracuseStep 176573 = 66215) (by norm_num)
theorem B176597 : Blo 115785 176597 := bbase (se 7 (by rfl) ⟨2069, by rfl⟩ : syracuseStep 176597 = 4139) (by norm_num)
theorem B176621 : Blo 115785 176621 := bbase (se 3 (by rfl) ⟨33116, by rfl⟩ : syracuseStep 176621 = 66233) (by norm_num)
theorem B176645 : Blo 115785 176645 := bbase (se 4 (by rfl) ⟨16560, by rfl⟩ : syracuseStep 176645 = 33121) (by norm_num)
theorem B176669 : Blo 115785 176669 := bbase (se 3 (by rfl) ⟨33125, by rfl⟩ : syracuseStep 176669 = 66251) (by norm_num)
theorem B176693 : Blo 115785 176693 := bbase (se 5 (by rfl) ⟨8282, by rfl⟩ : syracuseStep 176693 = 16565) (by norm_num)
theorem B242237 : Blo 115785 242237 := bbase (se 3 (by rfl) ⟨45419, by rfl⟩ : syracuseStep 242237 = 90839) (by norm_num)
theorem B176717 : Blo 115785 176717 := bbase (se 3 (by rfl) ⟨33134, by rfl⟩ : syracuseStep 176717 = 66269) (by norm_num)
theorem B176741 : Blo 115785 176741 := bbase (se 4 (by rfl) ⟨16569, by rfl⟩ : syracuseStep 176741 = 33139) (by norm_num)
theorem B176765 : Blo 115785 176765 := bbase (se 3 (by rfl) ⟨33143, by rfl⟩ : syracuseStep 176765 = 66287) (by norm_num)
theorem B176789 : Blo 115785 176789 := bbase (se 6 (by rfl) ⟨4143, by rfl⟩ : syracuseStep 176789 = 8287) (by norm_num)
theorem B176813 : Blo 115785 176813 := bbase (se 3 (by rfl) ⟨33152, by rfl⟩ : syracuseStep 176813 = 66305) (by norm_num)
theorem B176837 : Blo 115785 176837 := bbase (se 4 (by rfl) ⟨16578, by rfl⟩ : syracuseStep 176837 = 33157) (by norm_num)
theorem B176861 : Blo 115785 176861 := bbase (se 3 (by rfl) ⟨33161, by rfl⟩ : syracuseStep 176861 = 66323) (by norm_num)
theorem B176885 : Blo 115785 176885 := bbase (se 5 (by rfl) ⟨8291, by rfl⟩ : syracuseStep 176885 = 16583) (by norm_num)
theorem B176909 : Blo 115785 176909 := bbase (se 3 (by rfl) ⟨33170, by rfl⟩ : syracuseStep 176909 = 66341) (by norm_num)
theorem B176933 : Blo 115785 176933 := bbase (se 4 (by rfl) ⟨16587, by rfl⟩ : syracuseStep 176933 = 33175) (by norm_num)
theorem B176957 : Blo 115785 176957 := bbase (se 3 (by rfl) ⟨33179, by rfl⟩ : syracuseStep 176957 = 66359) (by norm_num)
theorem B176981 : Blo 115785 176981 := bbase (se 9 (by rfl) ⟨518, by rfl⟩ : syracuseStep 176981 = 1037) (by norm_num)
theorem B177005 : Blo 115785 177005 := bbase (se 3 (by rfl) ⟨33188, by rfl⟩ : syracuseStep 177005 = 66377) (by norm_num)
theorem B177029 : Blo 115785 177029 := bbase (se 4 (by rfl) ⟨16596, by rfl⟩ : syracuseStep 177029 = 33193) (by norm_num)
theorem B177053 : Blo 115785 177053 := bbase (se 3 (by rfl) ⟨33197, by rfl⟩ : syracuseStep 177053 = 66395) (by norm_num)
theorem B177077 : Blo 115785 177077 := bbase (se 5 (by rfl) ⟨8300, by rfl⟩ : syracuseStep 177077 = 16601) (by norm_num)
theorem B177101 : Blo 115785 177101 := bbase (se 3 (by rfl) ⟨33206, by rfl⟩ : syracuseStep 177101 = 66413) (by norm_num)
theorem B177125 : Blo 115785 177125 := bbase (se 4 (by rfl) ⟨16605, by rfl⟩ : syracuseStep 177125 = 33211) (by norm_num)
theorem B603125 : Blo 115785 603125 := bbase (se 5 (by rfl) ⟨28271, by rfl⟩ : syracuseStep 603125 = 56543) (by norm_num)
theorem B177149 : Blo 115785 177149 := bbase (se 3 (by rfl) ⟨33215, by rfl⟩ : syracuseStep 177149 = 66431) (by norm_num)
theorem B472085 : Blo 115785 472085 := bbase (se 6 (by rfl) ⟨11064, by rfl⟩ : syracuseStep 472085 = 22129) (by norm_num)
theorem B177173 : Blo 115785 177173 := bbase (se 6 (by rfl) ⟨4152, by rfl⟩ : syracuseStep 177173 = 8305) (by norm_num)
theorem B177197 : Blo 115785 177197 := bbase (se 3 (by rfl) ⟨33224, by rfl⟩ : syracuseStep 177197 = 66449) (by norm_num)
theorem B177221 : Blo 115785 177221 := bbase (se 4 (by rfl) ⟨16614, by rfl⟩ : syracuseStep 177221 = 33229) (by norm_num)
theorem B177245 : Blo 115785 177245 := bbase (se 3 (by rfl) ⟨33233, by rfl⟩ : syracuseStep 177245 = 66467) (by norm_num)
theorem B177269 : Blo 115785 177269 := bbase (se 5 (by rfl) ⟨8309, by rfl⟩ : syracuseStep 177269 = 16619) (by norm_num)
theorem B177293 : Blo 115785 177293 := bbase (se 3 (by rfl) ⟨33242, by rfl⟩ : syracuseStep 177293 = 66485) (by norm_num)
theorem B177317 : Blo 115785 177317 := bbase (se 4 (by rfl) ⟨16623, by rfl⟩ : syracuseStep 177317 = 33247) (by norm_num)
theorem B177341 : Blo 115785 177341 := bbase (se 3 (by rfl) ⟨33251, by rfl⟩ : syracuseStep 177341 = 66503) (by norm_num)
theorem B472277 : Blo 115785 472277 := bbase (se 7 (by rfl) ⟨5534, by rfl⟩ : syracuseStep 472277 = 11069) (by norm_num)
theorem B177365 : Blo 115785 177365 := bbase (se 7 (by rfl) ⟨2078, by rfl⟩ : syracuseStep 177365 = 4157) (by norm_num)
theorem B505061 : Blo 115785 505061 := bbase (se 4 (by rfl) ⟨47349, by rfl⟩ : syracuseStep 505061 = 94699) (by norm_num)
theorem B177389 : Blo 115785 177389 := bbase (se 3 (by rfl) ⟨33260, by rfl⟩ : syracuseStep 177389 = 66521) (by norm_num)
theorem B177413 : Blo 115785 177413 := bbase (se 4 (by rfl) ⟨16632, by rfl⟩ : syracuseStep 177413 = 33265) (by norm_num)
theorem B144649 : Blo 115785 144649 := bbase (se 2 (by rfl) ⟨54243, by rfl⟩ : syracuseStep 144649 = 108487) (by norm_num)
theorem B210205 : Blo 115785 210205 := bbase (se 3 (by rfl) ⟨39413, by rfl⟩ : syracuseStep 210205 = 78827) (by norm_num)
theorem B177437 : Blo 115785 177437 := bbase (se 3 (by rfl) ⟨33269, by rfl⟩ : syracuseStep 177437 = 66539) (by norm_num)
theorem B177461 : Blo 115785 177461 := bbase (se 5 (by rfl) ⟨8318, by rfl⟩ : syracuseStep 177461 = 16637) (by norm_num)
theorem B177485 : Blo 115785 177485 := bbase (se 3 (by rfl) ⟨33278, by rfl⟩ : syracuseStep 177485 = 66557) (by norm_num)
theorem B177493 : Blo 115785 177493 := bbase (se 13 (by rfl) ⟨32, by rfl⟩ : syracuseStep 177493 = 65) (by norm_num)
theorem B177509 : Blo 115785 177509 := bbase (se 4 (by rfl) ⟨16641, by rfl⟩ : syracuseStep 177509 = 33283) (by norm_num)
theorem B996725 : Blo 115785 996725 := bbase (se 5 (by rfl) ⟨46721, by rfl⟩ : syracuseStep 996725 = 93443) (by norm_num)
theorem B636277 : Blo 115785 636277 := bbase (se 5 (by rfl) ⟨29825, by rfl⟩ : syracuseStep 636277 = 59651) (by norm_num)
theorem B177533 : Blo 115785 177533 := bbase (se 3 (by rfl) ⟨33287, by rfl⟩ : syracuseStep 177533 = 66575) (by norm_num)
theorem B177557 : Blo 115785 177557 := bbase (se 6 (by rfl) ⟨4161, by rfl⟩ : syracuseStep 177557 = 8323) (by norm_num)
theorem B177581 : Blo 115785 177581 := bbase (se 3 (by rfl) ⟨33296, by rfl⟩ : syracuseStep 177581 = 66593) (by norm_num)
theorem B177605 : Blo 115785 177605 := bbase (se 4 (by rfl) ⟨16650, by rfl⟩ : syracuseStep 177605 = 33301) (by norm_num)
theorem B177629 : Blo 115785 177629 := bbase (se 3 (by rfl) ⟨33305, by rfl⟩ : syracuseStep 177629 = 66611) (by norm_num)
theorem B177653 : Blo 115785 177653 := bbase (se 5 (by rfl) ⟨8327, by rfl⟩ : syracuseStep 177653 = 16655) (by norm_num)
theorem B177677 : Blo 115785 177677 := bbase (se 3 (by rfl) ⟨33314, by rfl⟩ : syracuseStep 177677 = 66629) (by norm_num)
theorem B177701 : Blo 115785 177701 := bbase (se 4 (by rfl) ⟨16659, by rfl⟩ : syracuseStep 177701 = 33319) (by norm_num)
theorem B898613 : Blo 115785 898613 := bbase (se 5 (by rfl) ⟨42122, by rfl⟩ : syracuseStep 898613 = 84245) (by norm_num)
theorem B177725 : Blo 115785 177725 := bbase (se 3 (by rfl) ⟨33323, by rfl⟩ : syracuseStep 177725 = 66647) (by norm_num)
theorem B177749 : Blo 115785 177749 := bbase (se 8 (by rfl) ⟨1041, by rfl⟩ : syracuseStep 177749 = 2083) (by norm_num)
theorem B1357397 : Blo 115785 1357397 := bbase (se 8 (by rfl) ⟨7953, by rfl⟩ : syracuseStep 1357397 = 15907) (by norm_num)
theorem B177773 : Blo 115785 177773 := bbase (se 3 (by rfl) ⟨33332, by rfl⟩ : syracuseStep 177773 = 66665) (by norm_num)
theorem B177797 : Blo 115785 177797 := bbase (se 4 (by rfl) ⟨16668, by rfl⟩ : syracuseStep 177797 = 33337) (by norm_num)
theorem B407189 : Blo 115785 407189 := bbase (se 6 (by rfl) ⟨9543, by rfl⟩ : syracuseStep 407189 = 19087) (by norm_num)
theorem B177821 : Blo 115785 177821 := bbase (se 3 (by rfl) ⟨33341, by rfl⟩ : syracuseStep 177821 = 66683) (by norm_num)
theorem B177845 : Blo 115785 177845 := bbase (se 5 (by rfl) ⟨8336, by rfl⟩ : syracuseStep 177845 = 16673) (by norm_num)
theorem B177869 : Blo 115785 177869 := bbase (se 3 (by rfl) ⟨33350, by rfl⟩ : syracuseStep 177869 = 66701) (by norm_num)
theorem B177893 : Blo 115785 177893 := bbase (se 4 (by rfl) ⟨16677, by rfl⟩ : syracuseStep 177893 = 33355) (by norm_num)
theorem B177917 : Blo 115785 177917 := bbase (se 3 (by rfl) ⟨33359, by rfl⟩ : syracuseStep 177917 = 66719) (by norm_num)
theorem B177941 : Blo 115785 177941 := bbase (se 6 (by rfl) ⟨4170, by rfl⟩ : syracuseStep 177941 = 8341) (by norm_num)
theorem B571157 : Blo 115785 571157 := bbase (se 6 (by rfl) ⟨13386, by rfl⟩ : syracuseStep 571157 = 26773) (by norm_num)
theorem B177965 : Blo 115785 177965 := bbase (se 3 (by rfl) ⟨33368, by rfl⟩ : syracuseStep 177965 = 66737) (by norm_num)
theorem B177989 : Blo 115785 177989 := bbase (se 4 (by rfl) ⟨16686, by rfl⟩ : syracuseStep 177989 = 33373) (by norm_num)
theorem B178013 : Blo 115785 178013 := bbase (se 3 (by rfl) ⟨33377, by rfl⟩ : syracuseStep 178013 = 66755) (by norm_num)
theorem B374645 : Blo 115785 374645 := bbase (se 5 (by rfl) ⟨17561, by rfl⟩ : syracuseStep 374645 = 35123) (by norm_num)
theorem B178037 : Blo 115785 178037 := bbase (se 5 (by rfl) ⟨8345, by rfl⟩ : syracuseStep 178037 = 16691) (by norm_num)
theorem B178061 : Blo 115785 178061 := bbase (se 3 (by rfl) ⟨33386, by rfl⟩ : syracuseStep 178061 = 66773) (by norm_num)
theorem B145309 : Blo 115785 145309 := bbase (se 3 (by rfl) ⟨27245, by rfl⟩ : syracuseStep 145309 = 54491) (by norm_num)
theorem B178085 : Blo 115785 178085 := bbase (se 4 (by rfl) ⟨16695, by rfl⟩ : syracuseStep 178085 = 33391) (by norm_num)
theorem B178109 : Blo 115785 178109 := bbase (se 3 (by rfl) ⟨33395, by rfl⟩ : syracuseStep 178109 = 66791) (by norm_num)
theorem B669653 : Blo 115785 669653 := bbase (se 7 (by rfl) ⟨7847, by rfl⟩ : syracuseStep 669653 = 15695) (by norm_num)
theorem B178133 : Blo 115785 178133 := bbase (se 7 (by rfl) ⟨2087, by rfl⟩ : syracuseStep 178133 = 4175) (by norm_num)
theorem B178157 : Blo 115785 178157 := bbase (se 3 (by rfl) ⟨33404, by rfl⟩ : syracuseStep 178157 = 66809) (by norm_num)
theorem B538613 : Blo 115785 538613 := bbase (se 5 (by rfl) ⟨25247, by rfl⟩ : syracuseStep 538613 = 50495) (by norm_num)
theorem B178181 : Blo 115785 178181 := bbase (se 4 (by rfl) ⟨16704, by rfl⟩ : syracuseStep 178181 = 33409) (by norm_num)
theorem B178205 : Blo 115785 178205 := bbase (se 3 (by rfl) ⟨33413, by rfl⟩ : syracuseStep 178205 = 66827) (by norm_num)
theorem B178229 : Blo 115785 178229 := bbase (se 5 (by rfl) ⟨8354, by rfl⟩ : syracuseStep 178229 = 16709) (by norm_num)
theorem B178237 : Blo 115785 178237 := bbase (se 3 (by rfl) ⟨33419, by rfl⟩ : syracuseStep 178237 = 66839) (by norm_num)
theorem B178253 : Blo 115785 178253 := bbase (se 3 (by rfl) ⟨33422, by rfl⟩ : syracuseStep 178253 = 66845) (by norm_num)
theorem B178277 : Blo 115785 178277 := bbase (se 4 (by rfl) ⟨16713, by rfl⟩ : syracuseStep 178277 = 33427) (by norm_num)
theorem B440437 : Blo 115785 440437 := bbase (se 5 (by rfl) ⟨20645, by rfl⟩ : syracuseStep 440437 = 41291) (by norm_num)
theorem B178301 : Blo 115785 178301 := bbase (se 3 (by rfl) ⟨33431, by rfl⟩ : syracuseStep 178301 = 66863) (by norm_num)
theorem B178325 : Blo 115785 178325 := bbase (se 6 (by rfl) ⟨4179, by rfl⟩ : syracuseStep 178325 = 8359) (by norm_num)
theorem B178349 : Blo 115785 178349 := bbase (se 3 (by rfl) ⟨33440, by rfl⟩ : syracuseStep 178349 = 66881) (by norm_num)
theorem B178373 : Blo 115785 178373 := bbase (se 4 (by rfl) ⟨16722, by rfl⟩ : syracuseStep 178373 = 33445) (by norm_num)
theorem B178397 : Blo 115785 178397 := bbase (se 3 (by rfl) ⟨33449, by rfl⟩ : syracuseStep 178397 = 66899) (by norm_num)
theorem B178421 : Blo 115785 178421 := bbase (se 5 (by rfl) ⟨8363, by rfl⟩ : syracuseStep 178421 = 16727) (by norm_num)
theorem B604421 : Blo 115785 604421 := bbase (se 4 (by rfl) ⟨56664, by rfl⟩ : syracuseStep 604421 = 113329) (by norm_num)
theorem B178445 : Blo 115785 178445 := bbase (se 3 (by rfl) ⟨33458, by rfl⟩ : syracuseStep 178445 = 66917) (by norm_num)
theorem B178469 : Blo 115785 178469 := bbase (se 4 (by rfl) ⟨16731, by rfl⟩ : syracuseStep 178469 = 33463) (by norm_num)
theorem B178493 : Blo 115785 178493 := bbase (se 3 (by rfl) ⟨33467, by rfl⟩ : syracuseStep 178493 = 66935) (by norm_num)
theorem B178517 : Blo 115785 178517 := bbase (se 10 (by rfl) ⟨261, by rfl⟩ : syracuseStep 178517 = 523) (by norm_num)
theorem B178541 : Blo 115785 178541 := bbase (se 3 (by rfl) ⟨33476, by rfl⟩ : syracuseStep 178541 = 66953) (by norm_num)
theorem B178565 : Blo 115785 178565 := bbase (se 4 (by rfl) ⟨16740, by rfl⟩ : syracuseStep 178565 = 33481) (by norm_num)
theorem B178589 : Blo 115785 178589 := bbase (se 3 (by rfl) ⟨33485, by rfl⟩ : syracuseStep 178589 = 66971) (by norm_num)
theorem B440741 : Blo 115785 440741 := bbase (se 4 (by rfl) ⟨41319, by rfl⟩ : syracuseStep 440741 = 82639) (by norm_num)
theorem B670133 : Blo 115785 670133 := bbase (se 5 (by rfl) ⟨31412, by rfl⟩ : syracuseStep 670133 = 62825) (by norm_num)
theorem B178613 : Blo 115785 178613 := bbase (se 5 (by rfl) ⟨8372, by rfl⟩ : syracuseStep 178613 = 16745) (by norm_num)
theorem B178637 : Blo 115785 178637 := bbase (se 3 (by rfl) ⟨33494, by rfl⟩ : syracuseStep 178637 = 66989) (by norm_num)
theorem B178661 : Blo 115785 178661 := bbase (se 4 (by rfl) ⟨16749, by rfl⟩ : syracuseStep 178661 = 33499) (by norm_num)
theorem B178685 : Blo 115785 178685 := bbase (se 3 (by rfl) ⟨33503, by rfl⟩ : syracuseStep 178685 = 67007) (by norm_num)
theorem B178709 : Blo 115785 178709 := bbase (se 6 (by rfl) ⟨4188, by rfl⟩ : syracuseStep 178709 = 8377) (by norm_num)
theorem B178733 : Blo 115785 178733 := bbase (se 3 (by rfl) ⟨33512, by rfl⟩ : syracuseStep 178733 = 67025) (by norm_num)
theorem B178757 : Blo 115785 178757 := bbase (se 4 (by rfl) ⟨16758, by rfl⟩ : syracuseStep 178757 = 33517) (by norm_num)
theorem B178781 : Blo 115785 178781 := bbase (se 3 (by rfl) ⟨33521, by rfl⟩ : syracuseStep 178781 = 67043) (by norm_num)
theorem B178805 : Blo 115785 178805 := bbase (se 5 (by rfl) ⟨8381, by rfl⟩ : syracuseStep 178805 = 16763) (by norm_num)
theorem B211589 : Blo 115785 211589 := bbase (se 4 (by rfl) ⟨19836, by rfl⟩ : syracuseStep 211589 = 39673) (by norm_num)
theorem B178829 : Blo 115785 178829 := bbase (se 3 (by rfl) ⟨33530, by rfl⟩ : syracuseStep 178829 = 67061) (by norm_num)
theorem B178853 : Blo 115785 178853 := bbase (se 4 (by rfl) ⟨16767, by rfl⟩ : syracuseStep 178853 = 33535) (by norm_num)
theorem B178877 : Blo 115785 178877 := bbase (se 3 (by rfl) ⟨33539, by rfl⟩ : syracuseStep 178877 = 67079) (by norm_num)
theorem B211661 : Blo 115785 211661 := bbase (se 3 (by rfl) ⟨39686, by rfl⟩ : syracuseStep 211661 = 79373) (by norm_num)
theorem B178901 : Blo 115785 178901 := bbase (se 7 (by rfl) ⟨2096, by rfl⟩ : syracuseStep 178901 = 4193) (by norm_num)
theorem B178925 : Blo 115785 178925 := bbase (se 3 (by rfl) ⟨33548, by rfl⟩ : syracuseStep 178925 = 67097) (by norm_num)
theorem B178949 : Blo 115785 178949 := bbase (se 4 (by rfl) ⟨16776, by rfl⟩ : syracuseStep 178949 = 33553) (by norm_num)
theorem B178973 : Blo 115785 178973 := bbase (se 3 (by rfl) ⟨33557, by rfl⟩ : syracuseStep 178973 = 67115) (by norm_num)
theorem B178997 : Blo 115785 178997 := bbase (se 5 (by rfl) ⟨8390, by rfl⟩ : syracuseStep 178997 = 16781) (by norm_num)
theorem B179021 : Blo 115785 179021 := bbase (se 3 (by rfl) ⟨33566, by rfl⟩ : syracuseStep 179021 = 67133) (by norm_num)
theorem B211805 : Blo 115785 211805 := bbase (se 3 (by rfl) ⟨39713, by rfl⟩ : syracuseStep 211805 = 79427) (by norm_num)
theorem B179045 : Blo 115785 179045 := bbase (se 4 (by rfl) ⟨16785, by rfl⟩ : syracuseStep 179045 = 33571) (by norm_num)
theorem B179069 : Blo 115785 179069 := bbase (se 3 (by rfl) ⟨33575, by rfl⟩ : syracuseStep 179069 = 67151) (by norm_num)
theorem B179093 : Blo 115785 179093 := bbase (se 6 (by rfl) ⟨4197, by rfl⟩ : syracuseStep 179093 = 8395) (by norm_num)
theorem B179117 : Blo 115785 179117 := bbase (se 3 (by rfl) ⟨33584, by rfl⟩ : syracuseStep 179117 = 67169) (by norm_num)
theorem B179141 : Blo 115785 179141 := bbase (se 4 (by rfl) ⟨16794, by rfl⟩ : syracuseStep 179141 = 33589) (by norm_num)
theorem B506837 : Blo 115785 506837 := bbase (se 7 (by rfl) ⟨5939, by rfl⟩ : syracuseStep 506837 = 11879) (by norm_num)
theorem B179165 : Blo 115785 179165 := bbase (se 3 (by rfl) ⟨33593, by rfl⟩ : syracuseStep 179165 = 67187) (by norm_num)
theorem B179189 : Blo 115785 179189 := bbase (se 5 (by rfl) ⟨8399, by rfl⟩ : syracuseStep 179189 = 16799) (by norm_num)
theorem B179213 : Blo 115785 179213 := bbase (se 3 (by rfl) ⟨33602, by rfl⟩ : syracuseStep 179213 = 67205) (by norm_num)
theorem B179237 : Blo 115785 179237 := bbase (se 4 (by rfl) ⟨16803, by rfl⟩ : syracuseStep 179237 = 33607) (by norm_num)
theorem B179245 : Blo 115785 179245 := bbase (se 3 (by rfl) ⟨33608, by rfl⟩ : syracuseStep 179245 = 67217) (by norm_num)
theorem B179261 : Blo 115785 179261 := bbase (se 3 (by rfl) ⟨33611, by rfl⟩ : syracuseStep 179261 = 67223) (by norm_num)
theorem B179285 : Blo 115785 179285 := bbase (se 8 (by rfl) ⟨1050, by rfl⟩ : syracuseStep 179285 = 2101) (by norm_num)
theorem B179309 : Blo 115785 179309 := bbase (se 3 (by rfl) ⟨33620, by rfl⟩ : syracuseStep 179309 = 67241) (by norm_num)
theorem B146549 : Blo 115785 146549 := bbase (se 5 (by rfl) ⟨6869, by rfl⟩ : syracuseStep 146549 = 13739) (by norm_num)
theorem B179333 : Blo 115785 179333 := bbase (se 4 (by rfl) ⟨16812, by rfl⟩ : syracuseStep 179333 = 33625) (by norm_num)
theorem B179357 : Blo 115785 179357 := bbase (se 3 (by rfl) ⟨33629, by rfl⟩ : syracuseStep 179357 = 67259) (by norm_num)
theorem B146605 : Blo 115785 146605 := bbase (se 3 (by rfl) ⟨27488, by rfl⟩ : syracuseStep 146605 = 54977) (by norm_num)
theorem B179381 : Blo 115785 179381 := bbase (se 5 (by rfl) ⟨8408, by rfl⟩ : syracuseStep 179381 = 16817) (by norm_num)
theorem B179405 : Blo 115785 179405 := bbase (se 3 (by rfl) ⟨33638, by rfl⟩ : syracuseStep 179405 = 67277) (by norm_num)
theorem B179429 : Blo 115785 179429 := bbase (se 4 (by rfl) ⟨16821, by rfl⟩ : syracuseStep 179429 = 33643) (by norm_num)
theorem B179453 : Blo 115785 179453 := bbase (se 3 (by rfl) ⟨33647, by rfl⟩ : syracuseStep 179453 = 67295) (by norm_num)
theorem B146701 : Blo 115785 146701 := bbase (se 3 (by rfl) ⟨27506, by rfl⟩ : syracuseStep 146701 = 55013) (by norm_num)
theorem B179477 : Blo 115785 179477 := bbase (se 6 (by rfl) ⟨4206, by rfl⟩ : syracuseStep 179477 = 8413) (by norm_num)
theorem B179501 : Blo 115785 179501 := bbase (se 3 (by rfl) ⟨33656, by rfl⟩ : syracuseStep 179501 = 67313) (by norm_num)
theorem B179525 : Blo 115785 179525 := bbase (se 4 (by rfl) ⟨16830, by rfl⟩ : syracuseStep 179525 = 33661) (by norm_num)
theorem B179549 : Blo 115785 179549 := bbase (se 3 (by rfl) ⟨33665, by rfl⟩ : syracuseStep 179549 = 67331) (by norm_num)
theorem B179573 : Blo 115785 179573 := bbase (se 5 (by rfl) ⟨8417, by rfl⟩ : syracuseStep 179573 = 16835) (by norm_num)
theorem B179597 : Blo 115785 179597 := bbase (se 3 (by rfl) ⟨33674, by rfl⟩ : syracuseStep 179597 = 67349) (by norm_num)
theorem B179621 : Blo 115785 179621 := bbase (se 4 (by rfl) ⟨16839, by rfl⟩ : syracuseStep 179621 = 33679) (by norm_num)
theorem B146873 : Blo 115785 146873 := bbase (se 2 (by rfl) ⟨55077, by rfl⟩ : syracuseStep 146873 = 110155) (by norm_num)
theorem B179645 : Blo 115785 179645 := bbase (se 3 (by rfl) ⟨33683, by rfl⟩ : syracuseStep 179645 = 67367) (by norm_num)
theorem B179669 : Blo 115785 179669 := bbase (se 7 (by rfl) ⟨2105, by rfl⟩ : syracuseStep 179669 = 4211) (by norm_num)
theorem B146929 : Blo 115785 146929 := bbase (se 2 (by rfl) ⟨55098, by rfl⟩ : syracuseStep 146929 = 110197) (by norm_num)
theorem B605717 : Blo 115785 605717 := bbase (se 6 (by rfl) ⟨14196, by rfl⟩ : syracuseStep 605717 = 28393) (by norm_num)
theorem B147025 : Blo 115785 147025 := bbase (se 2 (by rfl) ⟨55134, by rfl⟩ : syracuseStep 147025 = 110269) (by norm_num)
theorem B278245 : Blo 115785 278245 := bbase (se 4 (by rfl) ⟨26085, by rfl⟩ : syracuseStep 278245 = 52171) (by norm_num)
theorem B147197 : Blo 115785 147197 := bbase (se 3 (by rfl) ⟨27599, by rfl⟩ : syracuseStep 147197 = 55199) (by norm_num)
theorem B540437 : Blo 115785 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B147253 : Blo 115785 147253 := bbase (se 5 (by rfl) ⟨6902, by rfl⟩ : syracuseStep 147253 = 13805) (by norm_num)
theorem B147349 : Blo 115785 147349 := bbase (se 6 (by rfl) ⟨3453, by rfl⟩ : syracuseStep 147349 = 6907) (by norm_num)
theorem B376741 : Blo 115785 376741 := bbase (se 4 (by rfl) ⟨35319, by rfl⟩ : syracuseStep 376741 = 70639) (by norm_num)
theorem B507829 : Blo 115785 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B966613 : Blo 115785 966613 := bbase (se 7 (by rfl) ⟨11327, by rfl⟩ : syracuseStep 966613 = 22655) (by norm_num)
theorem B278581 : Blo 115785 278581 := bbase (se 5 (by rfl) ⟨13058, by rfl⟩ : syracuseStep 278581 = 26117) (by norm_num)
theorem B147521 : Blo 115785 147521 := bbase (se 2 (by rfl) ⟨55320, by rfl⟩ : syracuseStep 147521 = 110641) (by norm_num)
theorem B147577 : Blo 115785 147577 := bbase (se 2 (by rfl) ⟨55341, by rfl⟩ : syracuseStep 147577 = 110683) (by norm_num)
theorem B147673 : Blo 115785 147673 := bbase (se 2 (by rfl) ⟨55377, by rfl⟩ : syracuseStep 147673 = 110755) (by norm_num)
theorem B213229 : Blo 115785 213229 := bbase (se 3 (by rfl) ⟨39980, by rfl⟩ : syracuseStep 213229 = 79961) (by norm_num)
theorem B147725 : Blo 115785 147725 := bbase (se 3 (by rfl) ⟨27698, by rfl⟩ : syracuseStep 147725 = 55397) (by norm_num)
theorem B999701 : Blo 115785 999701 := bbase (se 6 (by rfl) ⟨23430, by rfl⟩ : syracuseStep 999701 = 46861) (by norm_num)
theorem B147845 : Blo 115785 147845 := bbase (se 4 (by rfl) ⟨13860, by rfl⟩ : syracuseStep 147845 = 27721) (by norm_num)
theorem B147901 : Blo 115785 147901 := bbase (se 3 (by rfl) ⟨27731, by rfl⟩ : syracuseStep 147901 = 55463) (by norm_num)
theorem B442853 : Blo 115785 442853 := bbase (se 4 (by rfl) ⟨41517, by rfl⟩ : syracuseStep 442853 = 83035) (by norm_num)
theorem B147997 : Blo 115785 147997 := bbase (se 3 (by rfl) ⟨27749, by rfl⟩ : syracuseStep 147997 = 55499) (by norm_num)
theorem B574037 : Blo 115785 574037 := bbase (se 8 (by rfl) ⟨3363, by rfl⟩ : syracuseStep 574037 = 6727) (by norm_num)
theorem B279197 : Blo 115785 279197 := bbase (se 3 (by rfl) ⟨52349, by rfl⟩ : syracuseStep 279197 = 104699) (by norm_num)
theorem B705205 : Blo 115785 705205 := bbase (se 5 (by rfl) ⟨33056, by rfl⟩ : syracuseStep 705205 = 66113) (by norm_num)
theorem B410309 : Blo 115785 410309 := bbase (se 4 (by rfl) ⟨38466, by rfl⟩ : syracuseStep 410309 = 76933) (by norm_num)
theorem B148169 : Blo 115785 148169 := bbase (se 2 (by rfl) ⟨55563, by rfl⟩ : syracuseStep 148169 = 111127) (by norm_num)
theorem B180949 : Blo 115785 180949 := bbase (se 7 (by rfl) ⟨2120, by rfl⟩ : syracuseStep 180949 = 4241) (by norm_num)
theorem B148225 : Blo 115785 148225 := bbase (se 2 (by rfl) ⟨55584, by rfl⟩ : syracuseStep 148225 = 111169) (by norm_num)
theorem B443141 : Blo 115785 443141 := bbase (se 4 (by rfl) ⟨41544, by rfl⟩ : syracuseStep 443141 = 83089) (by norm_num)
theorem B148321 : Blo 115785 148321 := bbase (se 2 (by rfl) ⟨55620, by rfl⟩ : syracuseStep 148321 = 111241) (by norm_num)
theorem B574373 : Blo 115785 574373 := bbase (se 4 (by rfl) ⟨53847, by rfl⟩ : syracuseStep 574373 = 107695) (by norm_num)
theorem B377797 : Blo 115785 377797 := bbase (se 4 (by rfl) ⟨35418, by rfl⟩ : syracuseStep 377797 = 70837) (by norm_num)
theorem B148493 : Blo 115785 148493 := bbase (se 3 (by rfl) ⟨27842, by rfl⟩ : syracuseStep 148493 = 55685) (by norm_num)
theorem B148549 : Blo 115785 148549 := bbase (se 4 (by rfl) ⟨13926, by rfl⟩ : syracuseStep 148549 = 27853) (by norm_num)
theorem B279629 : Blo 115785 279629 := bbase (se 3 (by rfl) ⟨52430, by rfl⟩ : syracuseStep 279629 = 104861) (by norm_num)
theorem B148645 : Blo 115785 148645 := bbase (se 4 (by rfl) ⟨13935, by rfl⟩ : syracuseStep 148645 = 27871) (by norm_num)
theorem B1525013 : Blo 115785 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B148817 : Blo 115785 148817 := bbase (se 2 (by rfl) ⟨55806, by rfl⟩ : syracuseStep 148817 = 111613) (by norm_num)
theorem B148873 : Blo 115785 148873 := bbase (se 2 (by rfl) ⟨55827, by rfl⟩ : syracuseStep 148873 = 111655) (by norm_num)
theorem B214429 : Blo 115785 214429 := bbase (se 3 (by rfl) ⟨40205, by rfl⟩ : syracuseStep 214429 = 80411) (by norm_num)
theorem B2803157 : Blo 115785 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B148969 : Blo 115785 148969 := bbase (se 2 (by rfl) ⟨55863, by rfl⟩ : syracuseStep 148969 = 111727) (by norm_num)
theorem B148981 : Blo 115785 148981 := bbase (se 5 (by rfl) ⟨6983, by rfl⟩ : syracuseStep 148981 = 13967) (by norm_num)
theorem B149021 : Blo 115785 149021 := bbase (se 3 (by rfl) ⟨27941, by rfl⟩ : syracuseStep 149021 = 55883) (by norm_num)
theorem B476725 : Blo 115785 476725 := bbase (se 5 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 476725 = 44693) (by norm_num)
theorem B214645 : Blo 115785 214645 := bbase (se 5 (by rfl) ⟨10061, by rfl⟩ : syracuseStep 214645 = 20123) (by norm_num)
theorem B149141 : Blo 115785 149141 := bbase (se 6 (by rfl) ⟨3495, by rfl⟩ : syracuseStep 149141 = 6991) (by norm_num)
theorem B280253 : Blo 115785 280253 := bbase (se 3 (by rfl) ⟨52547, by rfl⟩ : syracuseStep 280253 = 105095) (by norm_num)
theorem B149197 : Blo 115785 149197 := bbase (se 3 (by rfl) ⟨27974, by rfl⟩ : syracuseStep 149197 = 55949) (by norm_num)
theorem B247541 : Blo 115785 247541 := bbase (se 5 (by rfl) ⟨11603, by rfl⟩ : syracuseStep 247541 = 23207) (by norm_num)
theorem B149293 : Blo 115785 149293 := bbase (se 3 (by rfl) ⟨27992, by rfl⟩ : syracuseStep 149293 = 55985) (by norm_num)
theorem B411493 : Blo 115785 411493 := bbase (se 4 (by rfl) ⟨38577, by rfl⟩ : syracuseStep 411493 = 77155) (by norm_num)
theorem B444325 : Blo 115785 444325 := bbase (se 4 (by rfl) ⟨41655, by rfl⟩ : syracuseStep 444325 = 83311) (by norm_num)
theorem B149465 : Blo 115785 149465 := bbase (se 2 (by rfl) ⟨56049, by rfl⟩ : syracuseStep 149465 = 112099) (by norm_num)
theorem B247781 : Blo 115785 247781 := bbase (se 4 (by rfl) ⟨23229, by rfl⟩ : syracuseStep 247781 = 46459) (by norm_num)
theorem B149521 : Blo 115785 149521 := bbase (se 2 (by rfl) ⟨56070, by rfl⟩ : syracuseStep 149521 = 112141) (by norm_num)
theorem B149617 : Blo 115785 149617 := bbase (se 2 (by rfl) ⟨56106, by rfl⟩ : syracuseStep 149617 = 112213) (by norm_num)
theorem B444629 : Blo 115785 444629 := bbase (se 7 (by rfl) ⟨5210, by rfl⟩ : syracuseStep 444629 = 10421) (by norm_num)
theorem B149789 : Blo 115785 149789 := bbase (se 3 (by rfl) ⟨28085, by rfl⟩ : syracuseStep 149789 = 56171) (by norm_num)
theorem B149845 : Blo 115785 149845 := bbase (se 10 (by rfl) ⟨219, by rfl⟩ : syracuseStep 149845 = 439) (by norm_num)
theorem B149941 : Blo 115785 149941 := bbase (se 5 (by rfl) ⟨7028, by rfl⟩ : syracuseStep 149941 = 14057) (by norm_num)
theorem B248285 : Blo 115785 248285 := bbase (se 3 (by rfl) ⟨46553, by rfl⟩ : syracuseStep 248285 = 93107) (by norm_num)
theorem B248293 : Blo 115785 248293 := bbase (se 4 (by rfl) ⟨23277, by rfl⟩ : syracuseStep 248293 = 46555) (by norm_num)
theorem B150113 : Blo 115785 150113 := bbase (se 2 (by rfl) ⟨56292, by rfl⟩ : syracuseStep 150113 = 112585) (by norm_num)
theorem B117397 : Blo 115785 117397 := bbase (se 6 (by rfl) ⟨2751, by rfl⟩ : syracuseStep 117397 = 5503) (by norm_num)
theorem B477845 : Blo 115785 477845 := bbase (se 6 (by rfl) ⟨11199, by rfl⟩ : syracuseStep 477845 = 22399) (by norm_num)
theorem B150169 : Blo 115785 150169 := bbase (se 2 (by rfl) ⟨56313, by rfl⟩ : syracuseStep 150169 = 112627) (by norm_num)
theorem B150265 : Blo 115785 150265 := bbase (se 2 (by rfl) ⟨56349, by rfl⟩ : syracuseStep 150265 = 112699) (by norm_num)
theorem B150437 : Blo 115785 150437 := bbase (se 4 (by rfl) ⟨14103, by rfl⟩ : syracuseStep 150437 = 28207) (by norm_num)
theorem B150493 : Blo 115785 150493 := bbase (se 3 (by rfl) ⟨28217, by rfl⟩ : syracuseStep 150493 = 56435) (by norm_num)
theorem B248845 : Blo 115785 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B150589 : Blo 115785 150589 := bbase (se 3 (by rfl) ⟨28235, by rfl⟩ : syracuseStep 150589 = 56471) (by norm_num)
theorem B183461 : Blo 115785 183461 := bbase (se 4 (by rfl) ⟨17199, by rfl⟩ : syracuseStep 183461 = 34399) (by norm_num)
theorem B150761 : Blo 115785 150761 := bbase (se 2 (by rfl) ⟨56535, by rfl⟩ : syracuseStep 150761 = 113071) (by norm_num)
theorem B150817 : Blo 115785 150817 := bbase (se 2 (by rfl) ⟨56556, by rfl⟩ : syracuseStep 150817 = 113113) (by norm_num)
theorem B544085 : Blo 115785 544085 := bbase (se 11 (by rfl) ⟨398, by rfl⟩ : syracuseStep 544085 = 797) (by norm_num)
theorem B150913 : Blo 115785 150913 := bbase (se 2 (by rfl) ⟨56592, by rfl⟩ : syracuseStep 150913 = 113185) (by norm_num)
theorem B151085 : Blo 115785 151085 := bbase (se 3 (by rfl) ⟨28328, by rfl⟩ : syracuseStep 151085 = 56657) (by norm_num)
theorem B249421 : Blo 115785 249421 := bbase (se 3 (by rfl) ⟨46766, by rfl⟩ : syracuseStep 249421 = 93533) (by norm_num)
theorem B216677 : Blo 115785 216677 := bbase (se 4 (by rfl) ⟨20313, by rfl⟩ : syracuseStep 216677 = 40627) (by norm_num)
theorem B151141 : Blo 115785 151141 := bbase (se 4 (by rfl) ⟨14169, by rfl⟩ : syracuseStep 151141 = 28339) (by norm_num)
theorem B151237 : Blo 115785 151237 := bbase (se 4 (by rfl) ⟨14178, by rfl⟩ : syracuseStep 151237 = 28357) (by norm_num)
theorem B380629 : Blo 115785 380629 := bbase (se 7 (by rfl) ⟨4460, by rfl⟩ : syracuseStep 380629 = 8921) (by norm_num)
theorem B380693 : Blo 115785 380693 := bbase (se 6 (by rfl) ⟨8922, by rfl⟩ : syracuseStep 380693 = 17845) (by norm_num)
theorem B151409 : Blo 115785 151409 := bbase (se 2 (by rfl) ⟨56778, by rfl⟩ : syracuseStep 151409 = 113557) (by norm_num)
theorem B151465 : Blo 115785 151465 := bbase (se 2 (by rfl) ⟨56799, by rfl⟩ : syracuseStep 151465 = 113599) (by norm_num)
theorem B249797 : Blo 115785 249797 := bbase (se 4 (by rfl) ⟨23418, by rfl⟩ : syracuseStep 249797 = 46837) (by norm_num)
theorem B151561 : Blo 115785 151561 := bbase (se 2 (by rfl) ⟨56835, by rfl⟩ : syracuseStep 151561 = 113671) (by norm_num)
theorem B1527893 : Blo 115785 1527893 := bbase (se 8 (by rfl) ⟨8952, by rfl⟩ : syracuseStep 1527893 = 17905) (by norm_num)
theorem B315589 : Blo 115785 315589 := bbase (se 4 (by rfl) ⟨29586, by rfl⟩ : syracuseStep 315589 = 59173) (by norm_num)
theorem B119053 : Blo 115785 119053 := bbase (se 3 (by rfl) ⟨22322, by rfl⟩ : syracuseStep 119053 = 44645) (by norm_num)
theorem B446741 : Blo 115785 446741 := bbase (se 6 (by rfl) ⟨10470, by rfl⟩ : syracuseStep 446741 = 20941) (by norm_num)
theorem B447029 : Blo 115785 447029 := bbase (se 5 (by rfl) ⟨20954, by rfl⟩ : syracuseStep 447029 = 41909) (by norm_num)
theorem B283213 : Blo 115785 283213 := bbase (se 3 (by rfl) ⟨53102, by rfl⟩ : syracuseStep 283213 = 106205) (by norm_num)
theorem B283405 : Blo 115785 283405 := bbase (se 3 (by rfl) ⟨53138, by rfl⟩ : syracuseStep 283405 = 106277) (by norm_num)
theorem B283445 : Blo 115785 283445 := bbase (se 5 (by rfl) ⟨13286, by rfl⟩ : syracuseStep 283445 = 26573) (by norm_num)
theorem B119777 : Blo 115785 119777 := bbase (se 2 (by rfl) ⟨44916, by rfl⟩ : syracuseStep 119777 = 89833) (by norm_num)
theorem B283733 : Blo 115785 283733 := bbase (se 8 (by rfl) ⟨1662, by rfl⟩ : syracuseStep 283733 = 3325) (by norm_num)
theorem B906389 : Blo 115785 906389 := bbase (se 6 (by rfl) ⟨21243, by rfl⟩ : syracuseStep 906389 = 42487) (by norm_num)
theorem B480581 : Blo 115785 480581 := bbase (se 4 (by rfl) ⟨45054, by rfl⟩ : syracuseStep 480581 = 90109) (by norm_num)
theorem B316885 : Blo 115785 316885 := bbase (se 7 (by rfl) ⟨3713, by rfl⟩ : syracuseStep 316885 = 7427) (by norm_num)
theorem B185861 : Blo 115785 185861 := bbase (se 4 (by rfl) ⟨17424, by rfl⟩ : syracuseStep 185861 = 34849) (by norm_num)
theorem B251437 : Blo 115785 251437 := bbase (se 3 (by rfl) ⟨47144, by rfl⟩ : syracuseStep 251437 = 94289) (by norm_num)
theorem B874037 : Blo 115785 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B448213 : Blo 115785 448213 := bbase (se 7 (by rfl) ⟨5252, by rfl⟩ : syracuseStep 448213 = 10505) (by norm_num)
theorem B186317 : Blo 115785 186317 := bbase (se 3 (by rfl) ⟨34934, by rfl⟩ : syracuseStep 186317 = 69869) (by norm_num)
theorem B448517 : Blo 115785 448517 := bbase (se 4 (by rfl) ⟨42048, by rfl⟩ : syracuseStep 448517 = 84097) (by norm_num)
theorem B1136693 : Blo 115785 1136693 := bbase (se 5 (by rfl) ⟨53282, by rfl⟩ : syracuseStep 1136693 = 106565) (by norm_num)
theorem B743701 : Blo 115785 743701 := bbase (se 6 (by rfl) ⟨17430, by rfl⟩ : syracuseStep 743701 = 34861) (by norm_num)
theorem B252325 : Blo 115785 252325 := bbase (se 4 (by rfl) ⟨23655, by rfl⟩ : syracuseStep 252325 = 47311) (by norm_num)
theorem B121289 : Blo 115785 121289 := bbase (se 2 (by rfl) ⟨45483, by rfl⟩ : syracuseStep 121289 = 90967) (by norm_num)
theorem B383717 : Blo 115785 383717 := bbase (se 4 (by rfl) ⟨35973, by rfl⟩ : syracuseStep 383717 = 71947) (by norm_num)
theorem B252821 : Blo 115785 252821 := bbase (se 6 (by rfl) ⟨5925, by rfl⟩ : syracuseStep 252821 = 11851) (by norm_num)
theorem B252965 : Blo 115785 252965 := bbase (se 4 (by rfl) ⟨23715, by rfl⟩ : syracuseStep 252965 = 47431) (by norm_num)
theorem B613493 : Blo 115785 613493 := bbase (se 5 (by rfl) ⟨28757, by rfl⟩ : syracuseStep 613493 = 57515) (by norm_num)
theorem B973973 : Blo 115785 973973 := bbase (se 6 (by rfl) ⟨22827, by rfl⟩ : syracuseStep 973973 = 45655) (by norm_num)
theorem B253085 : Blo 115785 253085 := bbase (se 3 (by rfl) ⟨47453, by rfl⟩ : syracuseStep 253085 = 94907) (by norm_num)
theorem B220333 : Blo 115785 220333 := bbase (se 3 (by rfl) ⟨41312, by rfl⟩ : syracuseStep 220333 = 82625) (by norm_num)
theorem B220477 : Blo 115785 220477 := bbase (se 3 (by rfl) ⟨41339, by rfl⟩ : syracuseStep 220477 = 82679) (by norm_num)
theorem B187733 : Blo 115785 187733 := bbase (se 11 (by rfl) ⟨137, by rfl⟩ : syracuseStep 187733 = 275) (by norm_num)
theorem B482773 : Blo 115785 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B220637 : Blo 115785 220637 := bbase (se 3 (by rfl) ⟨41369, by rfl⟩ : syracuseStep 220637 = 82739) (by norm_num)
theorem B581093 : Blo 115785 581093 := bbase (se 4 (by rfl) ⟨54477, by rfl⟩ : syracuseStep 581093 = 108955) (by norm_num)
theorem B187957 : Blo 115785 187957 := bbase (se 5 (by rfl) ⟨8810, by rfl⟩ : syracuseStep 187957 = 17621) (by norm_num)
theorem B482917 : Blo 115785 482917 := bbase (se 4 (by rfl) ⟨45273, by rfl⟩ : syracuseStep 482917 = 90547) (by norm_num)
theorem B220781 : Blo 115785 220781 := bbase (se 3 (by rfl) ⟨41396, by rfl⟩ : syracuseStep 220781 = 82793) (by norm_num)
theorem B253685 : Blo 115785 253685 := bbase (se 5 (by rfl) ⟨11891, by rfl⟩ : syracuseStep 253685 = 23783) (by norm_num)
theorem B319285 : Blo 115785 319285 := bbase (se 5 (by rfl) ⟨14966, by rfl⟩ : syracuseStep 319285 = 29933) (by norm_num)
theorem B253829 : Blo 115785 253829 := bbase (se 4 (by rfl) ⟨23796, by rfl⟩ : syracuseStep 253829 = 47593) (by norm_num)
theorem B221069 : Blo 115785 221069 := bbase (se 3 (by rfl) ⟨41450, by rfl⟩ : syracuseStep 221069 = 82901) (by norm_num)
theorem B221221 : Blo 115785 221221 := bbase (se 4 (by rfl) ⟨20739, by rfl⟩ : syracuseStep 221221 = 41479) (by norm_num)
theorem B450629 : Blo 115785 450629 := bbase (se 4 (by rfl) ⟨42246, by rfl⟩ : syracuseStep 450629 = 84493) (by norm_num)
theorem B286805 : Blo 115785 286805 := bbase (se 8 (by rfl) ⟨1680, by rfl⟩ : syracuseStep 286805 = 3361) (by norm_num)
theorem B680021 : Blo 115785 680021 := bbase (se 8 (by rfl) ⟨3984, by rfl⟩ : syracuseStep 680021 = 7969) (by norm_num)
theorem B122969 : Blo 115785 122969 := bbase (se 2 (by rfl) ⟨46113, by rfl⟩ : syracuseStep 122969 = 92227) (by norm_num)
theorem B221525 : Blo 115785 221525 := bbase (se 10 (by rfl) ⟨324, by rfl⟩ : syracuseStep 221525 = 649) (by norm_num)
theorem B450917 : Blo 115785 450917 := bbase (se 4 (by rfl) ⟨42273, by rfl⟩ : syracuseStep 450917 = 84547) (by norm_num)
theorem B483893 : Blo 115785 483893 := bbase (se 5 (by rfl) ⟨22682, by rfl⟩ : syracuseStep 483893 = 45365) (by norm_num)
theorem B647765 : Blo 115785 647765 := bbase (se 8 (by rfl) ⟨3795, by rfl⟩ : syracuseStep 647765 = 7591) (by norm_num)
theorem B287317 : Blo 115785 287317 := bbase (se 8 (by rfl) ⟨1683, by rfl⟩ : syracuseStep 287317 = 3367) (by norm_num)
theorem B254573 : Blo 115785 254573 := bbase (se 3 (by rfl) ⟨47732, by rfl⟩ : syracuseStep 254573 = 95465) (by norm_num)
theorem B418709 : Blo 115785 418709 := bbase (se 6 (by rfl) ⟨9813, by rfl⟩ : syracuseStep 418709 = 19627) (by norm_num)
theorem B123805 : Blo 115785 123805 := bbase (se 3 (by rfl) ⟨23213, by rfl⟩ : syracuseStep 123805 = 46427) (by norm_num)
theorem B189373 : Blo 115785 189373 := bbase (se 3 (by rfl) ⟨35507, by rfl⟩ : syracuseStep 189373 = 71015) (by norm_num)
theorem B1369045 : Blo 115785 1369045 := bbase (se 7 (by rfl) ⟨16043, by rfl⟩ : syracuseStep 1369045 = 32087) (by norm_num)
theorem B222277 : Blo 115785 222277 := bbase (se 4 (by rfl) ⟨20838, by rfl⟩ : syracuseStep 222277 = 41677) (by norm_num)
theorem B189629 : Blo 115785 189629 := bbase (se 3 (by rfl) ⟨35555, by rfl⟩ : syracuseStep 189629 = 71111) (by norm_num)
theorem B222421 : Blo 115785 222421 := bbase (se 7 (by rfl) ⟨2606, by rfl⟩ : syracuseStep 222421 = 5213) (by norm_num)
theorem B517429 : Blo 115785 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B255325 : Blo 115785 255325 := bbase (se 3 (by rfl) ⟨47873, by rfl⟩ : syracuseStep 255325 = 95747) (by norm_num)
theorem B157037 : Blo 115785 157037 := bbase (se 3 (by rfl) ⟨29444, by rfl⟩ : syracuseStep 157037 = 58889) (by norm_num)
theorem B222581 : Blo 115785 222581 := bbase (se 5 (by rfl) ⟨10433, by rfl⟩ : syracuseStep 222581 = 20867) (by norm_num)
theorem B189821 : Blo 115785 189821 := bbase (se 3 (by rfl) ⟨35591, by rfl⟩ : syracuseStep 189821 = 71183) (by norm_num)
theorem B255469 : Blo 115785 255469 := bbase (se 3 (by rfl) ⟨47900, by rfl⟩ : syracuseStep 255469 = 95801) (by norm_num)
theorem B222725 : Blo 115785 222725 := bbase (se 4 (by rfl) ⟨20880, by rfl⟩ : syracuseStep 222725 = 41761) (by norm_num)
theorem B452101 : Blo 115785 452101 := bbase (se 4 (by rfl) ⟨42384, by rfl⟩ : syracuseStep 452101 = 84769) (by norm_num)
theorem B124625 : Blo 115785 124625 := bbase (se 2 (by rfl) ⟨46734, by rfl⟩ : syracuseStep 124625 = 93469) (by norm_num)
theorem B157405 : Blo 115785 157405 := bbase (se 3 (by rfl) ⟨29513, by rfl⟩ : syracuseStep 157405 = 59027) (by norm_num)
theorem B223013 : Blo 115785 223013 := bbase (se 4 (by rfl) ⟨20907, by rfl⟩ : syracuseStep 223013 = 41815) (by norm_num)
theorem B452405 : Blo 115785 452405 := bbase (se 5 (by rfl) ⟨21206, by rfl⟩ : syracuseStep 452405 = 42413) (by norm_num)
theorem B419717 : Blo 115785 419717 := bbase (se 4 (by rfl) ⟨39348, by rfl⟩ : syracuseStep 419717 = 78697) (by norm_num)
theorem B223165 : Blo 115785 223165 := bbase (se 3 (by rfl) ⟨41843, by rfl⟩ : syracuseStep 223165 = 83687) (by norm_num)
theorem B256117 : Blo 115785 256117 := bbase (se 5 (by rfl) ⟨12005, by rfl⟩ : syracuseStep 256117 = 24011) (by norm_num)
theorem B125069 : Blo 115785 125069 := bbase (se 3 (by rfl) ⟨23450, by rfl⟩ : syracuseStep 125069 = 46901) (by norm_num)
theorem B223469 : Blo 115785 223469 := bbase (se 3 (by rfl) ⟨41900, by rfl⟩ : syracuseStep 223469 = 83801) (by norm_num)
theorem B190757 : Blo 115785 190757 := bbase (se 4 (by rfl) ⟨17883, by rfl⟩ : syracuseStep 190757 = 35767) (by norm_num)
theorem B125317 : Blo 115785 125317 := bbase (se 4 (by rfl) ⟨11748, by rfl⟩ : syracuseStep 125317 = 23497) (by norm_num)
theorem B191141 : Blo 115785 191141 := bbase (se 4 (by rfl) ⟨17919, by rfl⟩ : syracuseStep 191141 = 35839) (by norm_num)
theorem B125669 : Blo 115785 125669 := bbase (se 4 (by rfl) ⟨11781, by rfl⟩ : syracuseStep 125669 = 23563) (by norm_num)
theorem B191269 : Blo 115785 191269 := bbase (se 4 (by rfl) ⟨17931, by rfl⟩ : syracuseStep 191269 = 35863) (by norm_num)
theorem B125749 : Blo 115785 125749 := bbase (se 5 (by rfl) ⟨5894, by rfl⟩ : syracuseStep 125749 = 11789) (by norm_num)
theorem B125821 : Blo 115785 125821 := bbase (se 3 (by rfl) ⟨23591, by rfl⟩ : syracuseStep 125821 = 47183) (by norm_num)
theorem B224221 : Blo 115785 224221 := bbase (se 3 (by rfl) ⟨42041, by rfl⟩ : syracuseStep 224221 = 84083) (by norm_num)
theorem B224365 : Blo 115785 224365 := bbase (se 3 (by rfl) ⟨42068, by rfl⟩ : syracuseStep 224365 = 84137) (by norm_num)
theorem B126193 : Blo 115785 126193 := bbase (se 2 (by rfl) ⟨47322, by rfl⟩ : syracuseStep 126193 = 94645) (by norm_num)
theorem B224525 : Blo 115785 224525 := bbase (se 3 (by rfl) ⟨42098, by rfl⟩ : syracuseStep 224525 = 84197) (by norm_num)
theorem B847189 : Blo 115785 847189 := bbase (se 11 (by rfl) ⟨620, by rfl⟩ : syracuseStep 847189 = 1241) (by norm_num)
theorem B224669 : Blo 115785 224669 := bbase (se 3 (by rfl) ⟨42125, by rfl⟩ : syracuseStep 224669 = 84251) (by norm_num)
theorem B224765 : Blo 115785 224765 := bbase (se 3 (by rfl) ⟨42143, by rfl⟩ : syracuseStep 224765 = 84287) (by norm_num)
theorem B126569 : Blo 115785 126569 := bbase (se 2 (by rfl) ⟨47463, by rfl⟩ : syracuseStep 126569 = 94927) (by norm_num)
theorem B126641 : Blo 115785 126641 := bbase (se 2 (by rfl) ⟨47490, by rfl⟩ : syracuseStep 126641 = 94981) (by norm_num)
theorem B224957 : Blo 115785 224957 := bbase (se 3 (by rfl) ⟨42179, by rfl⟩ : syracuseStep 224957 = 84359) (by norm_num)
theorem B225109 : Blo 115785 225109 := bbase (se 9 (by rfl) ⟨659, by rfl⟩ : syracuseStep 225109 = 1319) (by norm_num)
theorem B126829 : Blo 115785 126829 := bbase (se 3 (by rfl) ⟨23780, by rfl⟩ : syracuseStep 126829 = 47561) (by norm_num)
theorem B454517 : Blo 115785 454517 := bbase (se 5 (by rfl) ⟨21305, by rfl⟩ : syracuseStep 454517 = 42611) (by norm_num)
theorem B127013 : Blo 115785 127013 := bbase (se 4 (by rfl) ⟨11907, by rfl⟩ : syracuseStep 127013 = 23815) (by norm_num)
theorem B225413 : Blo 115785 225413 := bbase (se 4 (by rfl) ⟨21132, by rfl⟩ : syracuseStep 225413 = 42265) (by norm_num)
theorem B454805 : Blo 115785 454805 := bbase (se 6 (by rfl) ⟨10659, by rfl⟩ : syracuseStep 454805 = 21319) (by norm_num)
theorem B913589 : Blo 115785 913589 := bbase (se 5 (by rfl) ⟨42824, by rfl⟩ : syracuseStep 913589 = 85649) (by norm_num)
theorem B750005 : Blo 115785 750005 := bbase (se 5 (by rfl) ⟨35156, by rfl⟩ : syracuseStep 750005 = 70313) (by norm_num)
theorem B586277 : Blo 115785 586277 := bbase (se 4 (by rfl) ⟨54963, by rfl⟩ : syracuseStep 586277 = 109927) (by norm_num)
theorem B356933 : Blo 115785 356933 := bbase (se 4 (by rfl) ⟨33462, by rfl⟩ : syracuseStep 356933 = 66925) (by norm_num)
theorem B127637 : Blo 115785 127637 := bbase (se 6 (by rfl) ⟨2991, by rfl⟩ : syracuseStep 127637 = 5983) (by norm_num)
theorem B127765 : Blo 115785 127765 := bbase (se 6 (by rfl) ⟨2994, by rfl⟩ : syracuseStep 127765 = 5989) (by norm_num)
theorem B127837 : Blo 115785 127837 := bbase (se 3 (by rfl) ⟨23969, by rfl⟩ : syracuseStep 127837 = 47939) (by norm_num)
theorem B226165 : Blo 115785 226165 := bbase (se 5 (by rfl) ⟨10601, by rfl⟩ : syracuseStep 226165 = 21203) (by norm_num)
theorem B226309 : Blo 115785 226309 := bbase (se 4 (by rfl) ⟨21216, by rfl⟩ : syracuseStep 226309 = 42433) (by norm_num)
theorem B455813 : Blo 115785 455813 := bbase (se 4 (by rfl) ⟨42732, by rfl⟩ : syracuseStep 455813 = 85465) (by norm_num)
theorem B226469 : Blo 115785 226469 := bbase (se 4 (by rfl) ⟨21231, by rfl⟩ : syracuseStep 226469 = 42463) (by norm_num)
theorem B947477 : Blo 115785 947477 := bbase (se 6 (by rfl) ⟨22206, by rfl⟩ : syracuseStep 947477 = 44413) (by norm_num)
theorem B226613 : Blo 115785 226613 := bbase (se 5 (by rfl) ⟨10622, by rfl⟩ : syracuseStep 226613 = 21245) (by norm_num)
theorem B3437909 : Blo 115785 3437909 := bbase (se 13 (by rfl) ⟨629, by rfl⟩ : syracuseStep 3437909 = 1259) (by norm_num)
theorem B128413 : Blo 115785 128413 := bbase (se 3 (by rfl) ⟨24077, by rfl⟩ : syracuseStep 128413 = 48155) (by norm_num)
theorem B161357 : Blo 115785 161357 := bbase (se 3 (by rfl) ⟨30254, by rfl⟩ : syracuseStep 161357 = 60509) (by norm_num)
theorem B226901 : Blo 115785 226901 := bbase (se 8 (by rfl) ⟨1329, by rfl⟩ : syracuseStep 226901 = 2659) (by norm_num)
theorem B227053 : Blo 115785 227053 := bbase (se 3 (by rfl) ⟨42572, by rfl⟩ : syracuseStep 227053 = 85145) (by norm_num)
theorem B587573 : Blo 115785 587573 := bbase (se 5 (by rfl) ⟨27542, by rfl⟩ : syracuseStep 587573 = 55085) (by norm_num)
theorem B391013 : Blo 115785 391013 := bbase (se 4 (by rfl) ⟨36657, by rfl⟩ : syracuseStep 391013 = 73315) (by norm_num)
theorem B227357 : Blo 115785 227357 := bbase (se 3 (by rfl) ⟨42629, by rfl⟩ : syracuseStep 227357 = 85259) (by norm_num)
theorem B391445 : Blo 115785 391445 := bbase (se 6 (by rfl) ⟨9174, by rfl⟩ : syracuseStep 391445 = 18349) (by norm_num)
theorem B883061 : Blo 115785 883061 := bbase (se 5 (by rfl) ⟨41393, by rfl⟩ : syracuseStep 883061 = 82787) (by norm_num)
theorem B260549 : Blo 115785 260549 := bbase (se 4 (by rfl) ⟨24426, by rfl⟩ : syracuseStep 260549 = 48853) (by norm_num)
theorem B1505749 : Blo 115785 1505749 := bbase (se 7 (by rfl) ⟨17645, by rfl⟩ : syracuseStep 1505749 = 35291) (by norm_num)
theorem B293341 : Blo 115785 293341 := bbase (se 3 (by rfl) ⟨55001, by rfl⟩ : syracuseStep 293341 = 110003) (by norm_num)
theorem B260621 : Blo 115785 260621 := bbase (se 3 (by rfl) ⟨48866, by rfl⟩ : syracuseStep 260621 = 97733) (by norm_num)
theorem B293453 : Blo 115785 293453 := bbase (se 3 (by rfl) ⟨55022, by rfl⟩ : syracuseStep 293453 = 110045) (by norm_num)
theorem B260693 : Blo 115785 260693 := bbase (se 8 (by rfl) ⟨1527, by rfl⟩ : syracuseStep 260693 = 3055) (by norm_num)
theorem B424597 : Blo 115785 424597 := bbase (se 6 (by rfl) ⟨9951, by rfl⟩ : syracuseStep 424597 = 19903) (by norm_num)
theorem B260765 : Blo 115785 260765 := bbase (se 3 (by rfl) ⟨48893, by rfl⟩ : syracuseStep 260765 = 97787) (by norm_num)
theorem B391877 : Blo 115785 391877 := bbase (se 4 (by rfl) ⟨36738, by rfl⟩ : syracuseStep 391877 = 73477) (by norm_num)
theorem B260837 : Blo 115785 260837 := bbase (se 4 (by rfl) ⟨24453, by rfl⟩ : syracuseStep 260837 = 48907) (by norm_num)
theorem B293645 : Blo 115785 293645 := bbase (se 3 (by rfl) ⟨55058, by rfl⟩ : syracuseStep 293645 = 110117) (by norm_num)
theorem B260909 : Blo 115785 260909 := bbase (se 3 (by rfl) ⟨48920, by rfl⟩ : syracuseStep 260909 = 97841) (by norm_num)
theorem B260981 : Blo 115785 260981 := bbase (se 5 (by rfl) ⟨12233, by rfl⟩ : syracuseStep 260981 = 24467) (by norm_num)
theorem B195493 : Blo 115785 195493 := bbase (se 4 (by rfl) ⟨18327, by rfl⟩ : syracuseStep 195493 = 36655) (by norm_num)
theorem B261053 : Blo 115785 261053 := bbase (se 3 (by rfl) ⟨48947, by rfl⟩ : syracuseStep 261053 = 97895) (by norm_num)
theorem B195581 : Blo 115785 195581 := bbase (se 3 (by rfl) ⟨36671, by rfl⟩ : syracuseStep 195581 = 73343) (by norm_num)
theorem B261125 : Blo 115785 261125 := bbase (se 4 (by rfl) ⟨24480, by rfl⟩ : syracuseStep 261125 = 48961) (by norm_num)
theorem B228413 : Blo 115785 228413 := bbase (se 3 (by rfl) ⟨42827, by rfl⟩ : syracuseStep 228413 = 85655) (by norm_num)
theorem B588869 : Blo 115785 588869 := bbase (se 4 (by rfl) ⟨55206, by rfl⟩ : syracuseStep 588869 = 110413) (by norm_num)
theorem B261197 : Blo 115785 261197 := bbase (se 3 (by rfl) ⟨48974, by rfl⟩ : syracuseStep 261197 = 97949) (by norm_num)
theorem B293989 : Blo 115785 293989 := bbase (se 4 (by rfl) ⟨27561, by rfl⟩ : syracuseStep 293989 = 55123) (by norm_num)
theorem B392309 : Blo 115785 392309 := bbase (se 5 (by rfl) ⟨18389, by rfl⟩ : syracuseStep 392309 = 36779) (by norm_num)
theorem B195709 : Blo 115785 195709 := bbase (se 3 (by rfl) ⟨36695, by rfl⟩ : syracuseStep 195709 = 73391) (by norm_num)
theorem B261269 : Blo 115785 261269 := bbase (se 6 (by rfl) ⟨6123, by rfl⟩ : syracuseStep 261269 = 12247) (by norm_num)
theorem B130261 : Blo 115785 130261 := bbase (se 7 (by rfl) ⟨1526, by rfl⟩ : syracuseStep 130261 = 3053) (by norm_num)
theorem B195797 : Blo 115785 195797 := bbase (se 7 (by rfl) ⟨2294, by rfl⟩ : syracuseStep 195797 = 4589) (by norm_num)
theorem B294101 : Blo 115785 294101 := bbase (se 7 (by rfl) ⟨3446, by rfl⟩ : syracuseStep 294101 = 6893) (by norm_num)
theorem B261341 : Blo 115785 261341 := bbase (se 3 (by rfl) ⟨49001, by rfl⟩ : syracuseStep 261341 = 98003) (by norm_num)
theorem B130297 : Blo 115785 130297 := bbase (se 2 (by rfl) ⟨48861, by rfl⟩ : syracuseStep 130297 = 97723) (by norm_num)
theorem B130333 : Blo 115785 130333 := bbase (se 3 (by rfl) ⟨24437, by rfl⟩ : syracuseStep 130333 = 48875) (by norm_num)
theorem B261413 : Blo 115785 261413 := bbase (se 4 (by rfl) ⟨24507, by rfl⟩ : syracuseStep 261413 = 49015) (by norm_num)
theorem B130369 : Blo 115785 130369 := bbase (se 2 (by rfl) ⟨48888, by rfl⟩ : syracuseStep 130369 = 97777) (by norm_num)
theorem B195925 : Blo 115785 195925 := bbase (se 11 (by rfl) ⟨143, by rfl⟩ : syracuseStep 195925 = 287) (by norm_num)
theorem B130405 : Blo 115785 130405 := bbase (se 4 (by rfl) ⟨12225, by rfl⟩ : syracuseStep 130405 = 24451) (by norm_num)
theorem B261485 : Blo 115785 261485 := bbase (se 3 (by rfl) ⟨49028, by rfl⟩ : syracuseStep 261485 = 98057) (by norm_num)
theorem B130441 : Blo 115785 130441 := bbase (se 2 (by rfl) ⟨48915, by rfl⟩ : syracuseStep 130441 = 97831) (by norm_num)
theorem B294293 : Blo 115785 294293 := bbase (se 6 (by rfl) ⟨6897, by rfl⟩ : syracuseStep 294293 = 13795) (by norm_num)
theorem B130477 : Blo 115785 130477 := bbase (se 3 (by rfl) ⟨24464, by rfl⟩ : syracuseStep 130477 = 48929) (by norm_num)
theorem B196013 : Blo 115785 196013 := bbase (se 3 (by rfl) ⟨36752, by rfl⟩ : syracuseStep 196013 = 73505) (by norm_num)
theorem B261557 : Blo 115785 261557 := bbase (se 5 (by rfl) ⟨12260, by rfl⟩ : syracuseStep 261557 = 24521) (by norm_num)
theorem B130513 : Blo 115785 130513 := bbase (se 2 (by rfl) ⟨48942, by rfl⟩ : syracuseStep 130513 = 97885) (by norm_num)
theorem B130549 : Blo 115785 130549 := bbase (se 5 (by rfl) ⟨6119, by rfl⟩ : syracuseStep 130549 = 12239) (by norm_num)
theorem B261629 : Blo 115785 261629 := bbase (se 3 (by rfl) ⟨49055, by rfl⟩ : syracuseStep 261629 = 98111) (by norm_num)
theorem B130585 : Blo 115785 130585 := bbase (se 2 (by rfl) ⟨48969, by rfl⟩ : syracuseStep 130585 = 97939) (by norm_num)
theorem B392741 : Blo 115785 392741 := bbase (se 4 (by rfl) ⟨36819, by rfl⟩ : syracuseStep 392741 = 73639) (by norm_num)
theorem B196141 : Blo 115785 196141 := bbase (se 3 (by rfl) ⟨36776, by rfl⟩ : syracuseStep 196141 = 73553) (by norm_num)
theorem B130621 : Blo 115785 130621 := bbase (se 3 (by rfl) ⟨24491, by rfl⟩ : syracuseStep 130621 = 48983) (by norm_num)
theorem B261701 : Blo 115785 261701 := bbase (se 4 (by rfl) ⟨24534, by rfl⟩ : syracuseStep 261701 = 49069) (by norm_num)
theorem B130657 : Blo 115785 130657 := bbase (se 2 (by rfl) ⟨48996, by rfl⟩ : syracuseStep 130657 = 97993) (by norm_num)
theorem B130693 : Blo 115785 130693 := bbase (se 4 (by rfl) ⟨12252, by rfl⟩ : syracuseStep 130693 = 24505) (by norm_num)
theorem B196229 : Blo 115785 196229 := bbase (se 4 (by rfl) ⟨18396, by rfl⟩ : syracuseStep 196229 = 36793) (by norm_num)
theorem B261773 : Blo 115785 261773 := bbase (se 3 (by rfl) ⟨49082, by rfl⟩ : syracuseStep 261773 = 98165) (by norm_num)
theorem B130729 : Blo 115785 130729 := bbase (se 2 (by rfl) ⟨49023, by rfl⟩ : syracuseStep 130729 = 98047) (by norm_num)
theorem B130765 : Blo 115785 130765 := bbase (se 3 (by rfl) ⟨24518, by rfl⟩ : syracuseStep 130765 = 49037) (by norm_num)
theorem B261845 : Blo 115785 261845 := bbase (se 7 (by rfl) ⟨3068, by rfl⟩ : syracuseStep 261845 = 6137) (by norm_num)
theorem B294637 : Blo 115785 294637 := bbase (se 3 (by rfl) ⟨55244, by rfl⟩ : syracuseStep 294637 = 110489) (by norm_num)
theorem B130801 : Blo 115785 130801 := bbase (se 2 (by rfl) ⟨49050, by rfl⟩ : syracuseStep 130801 = 98101) (by norm_num)
theorem B196357 : Blo 115785 196357 := bbase (se 4 (by rfl) ⟨18408, by rfl⟩ : syracuseStep 196357 = 36817) (by norm_num)
theorem B130837 : Blo 115785 130837 := bbase (se 6 (by rfl) ⟨3066, by rfl⟩ : syracuseStep 130837 = 6133) (by norm_num)
theorem B491285 : Blo 115785 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B261917 : Blo 115785 261917 := bbase (se 3 (by rfl) ⟨49109, by rfl⟩ : syracuseStep 261917 = 98219) (by norm_num)
theorem B130873 : Blo 115785 130873 := bbase (se 2 (by rfl) ⟨49077, by rfl⟩ : syracuseStep 130873 = 98155) (by norm_num)
theorem B130909 : Blo 115785 130909 := bbase (se 3 (by rfl) ⟨24545, by rfl⟩ : syracuseStep 130909 = 49091) (by norm_num)
theorem B196445 : Blo 115785 196445 := bbase (se 3 (by rfl) ⟨36833, by rfl⟩ : syracuseStep 196445 = 73667) (by norm_num)
theorem B294749 : Blo 115785 294749 := bbase (se 3 (by rfl) ⟨55265, by rfl⟩ : syracuseStep 294749 = 110531) (by norm_num)
theorem B261989 : Blo 115785 261989 := bbase (se 4 (by rfl) ⟨24561, by rfl⟩ : syracuseStep 261989 = 49123) (by norm_num)
theorem B130945 : Blo 115785 130945 := bbase (se 2 (by rfl) ⟨49104, by rfl⟩ : syracuseStep 130945 = 98209) (by norm_num)
theorem B130981 : Blo 115785 130981 := bbase (se 4 (by rfl) ⟨12279, by rfl⟩ : syracuseStep 130981 = 24559) (by norm_num)
theorem B262061 : Blo 115785 262061 := bbase (se 3 (by rfl) ⟨49136, by rfl⟩ : syracuseStep 262061 = 98273) (by norm_num)
theorem B360389 : Blo 115785 360389 := bbase (se 4 (by rfl) ⟨33786, by rfl⟩ : syracuseStep 360389 = 67573) (by norm_num)
theorem B131017 : Blo 115785 131017 := bbase (se 2 (by rfl) ⟨49131, by rfl⟩ : syracuseStep 131017 = 98263) (by norm_num)
theorem B393173 : Blo 115785 393173 := bbase (se 7 (by rfl) ⟨4607, by rfl⟩ : syracuseStep 393173 = 9215) (by norm_num)
theorem B196573 : Blo 115785 196573 := bbase (se 3 (by rfl) ⟨36857, by rfl⟩ : syracuseStep 196573 = 73715) (by norm_num)
theorem B131053 : Blo 115785 131053 := bbase (se 3 (by rfl) ⟨24572, by rfl⟩ : syracuseStep 131053 = 49145) (by norm_num)
theorem B262133 : Blo 115785 262133 := bbase (se 5 (by rfl) ⟨12287, by rfl⟩ : syracuseStep 262133 = 24575) (by norm_num)
theorem B163829 : Blo 115785 163829 := bbase (se 5 (by rfl) ⟨7679, by rfl⟩ : syracuseStep 163829 = 15359) (by norm_num)
theorem B196627 : Blo 115785 196627 := bstep (se 1 (by rfl) ⟨147470, by rfl⟩ : syracuseStep 196627 = 294941) B294941
theorem B131107 : Blo 115785 131107 := bstep (se 1 (by rfl) ⟨98330, by rfl⟩ : syracuseStep 131107 = 196661) B196661
theorem B294961 : Blo 115785 294961 := bstep (se 2 (by rfl) ⟨110610, by rfl⟩ : syracuseStep 294961 = 221221) B221221
theorem B196769 : Blo 115785 196769 := bstep (se 2 (by rfl) ⟨73788, by rfl⟩ : syracuseStep 196769 = 147577) B147577
theorem B393389 : Blo 115785 393389 := bstep (se 3 (by rfl) ⟨73760, by rfl⟩ : syracuseStep 393389 = 147521) B147521
theorem B131251 : Blo 115785 131251 := bstep (se 1 (by rfl) ⟨98438, by rfl⟩ : syracuseStep 131251 = 196877) B196877
theorem B393443 : Blo 115785 393443 := bstep (se 1 (by rfl) ⟨295082, by rfl⟩ : syracuseStep 393443 = 590165) B590165
theorem B327917 : Blo 115785 327917 := bstep (se 3 (by rfl) ⟨61484, by rfl⟩ : syracuseStep 327917 = 122969) B122969
theorem B262385 : Blo 115785 262385 := bstep (se 2 (by rfl) ⟨98394, by rfl⟩ : syracuseStep 262385 = 196789) B196789
theorem B262403 : Blo 115785 262403 := bstep (se 1 (by rfl) ⟨196802, by rfl⟩ : syracuseStep 262403 = 393605) B393605
theorem B885005 : Blo 115785 885005 := bstep (se 3 (by rfl) ⟨165938, by rfl⟩ : syracuseStep 885005 = 331877) B331877
theorem B196897 : Blo 115785 196897 := bstep (se 2 (by rfl) ⟨73836, by rfl⟩ : syracuseStep 196897 = 147673) B147673
theorem B295235 : Blo 115785 295235 := bstep (se 1 (by rfl) ⟨221426, by rfl⟩ : syracuseStep 295235 = 442853) B442853
theorem B196931 : Blo 115785 196931 := bstep (se 1 (by rfl) ⟨147698, by rfl⟩ : syracuseStep 196931 = 295397) B295397
theorem B131395 : Blo 115785 131395 := bstep (se 1 (by rfl) ⟨98546, by rfl⟩ : syracuseStep 131395 = 197093) B197093
theorem B197059 : Blo 115785 197059 := bstep (se 1 (by rfl) ⟨147794, by rfl⟩ : syracuseStep 197059 = 295589) B295589
theorem B131539 : Blo 115785 131539 := bstep (se 1 (by rfl) ⟨98654, by rfl⟩ : syracuseStep 131539 = 197309) B197309
theorem B393713 : Blo 115785 393713 := bstep (se 2 (by rfl) ⟨147642, by rfl⟩ : syracuseStep 393713 = 295285) B295285
theorem B295427 : Blo 115785 295427 := bstep (se 1 (by rfl) ⟨221570, by rfl⟩ : syracuseStep 295427 = 443141) B443141
theorem B262673 : Blo 115785 262673 := bstep (se 2 (by rfl) ⟨98502, by rfl⟩ : syracuseStep 262673 = 197005) B197005
theorem B262691 : Blo 115785 262691 := bstep (se 1 (by rfl) ⟨197018, by rfl⟩ : syracuseStep 262691 = 394037) B394037
theorem B197201 : Blo 115785 197201 := bstep (se 2 (by rfl) ⟨73950, by rfl⟩ : syracuseStep 197201 = 147901) B147901
theorem B131683 : Blo 115785 131683 := bstep (se 1 (by rfl) ⟨98762, by rfl⟩ : syracuseStep 131683 = 197525) B197525
theorem B3211973 : Blo 115785 3211973 := bstep (se 4 (by rfl) ⟨301122, by rfl⟩ : syracuseStep 3211973 = 602245) B602245
theorem B197329 : Blo 115785 197329 := bstep (se 2 (by rfl) ⟨73998, by rfl⟩ : syracuseStep 197329 = 147997) B147997
theorem B197363 : Blo 115785 197363 := bstep (se 1 (by rfl) ⟨148022, by rfl⟩ : syracuseStep 197363 = 296045) B296045
theorem B131827 : Blo 115785 131827 := bstep (se 1 (by rfl) ⟨98870, by rfl⟩ : syracuseStep 131827 = 197741) B197741
theorem B262961 : Blo 115785 262961 := bstep (se 2 (by rfl) ⟨98610, by rfl⟩ : syracuseStep 262961 = 197221) B197221
theorem B262979 : Blo 115785 262979 := bstep (se 1 (by rfl) ⟨197234, by rfl⟩ : syracuseStep 262979 = 394469) B394469
theorem B1016675 : Blo 115785 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B197491 : Blo 115785 197491 := bstep (se 1 (by rfl) ⟨148118, by rfl⟩ : syracuseStep 197491 = 296237) B296237
theorem B131971 : Blo 115785 131971 := bstep (se 1 (by rfl) ⟨98978, by rfl⟩ : syracuseStep 131971 = 197957) B197957
theorem B1868771 : Blo 115785 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B197633 : Blo 115785 197633 := bstep (se 2 (by rfl) ⟨74112, by rfl⟩ : syracuseStep 197633 = 148225) B148225
theorem B394253 : Blo 115785 394253 := bstep (se 3 (by rfl) ⟨73922, by rfl⟩ : syracuseStep 394253 = 147845) B147845
theorem B132115 : Blo 115785 132115 := bstep (se 1 (by rfl) ⟨99086, by rfl⟩ : syracuseStep 132115 = 198173) B198173
theorem B394307 : Blo 115785 394307 := bstep (se 1 (by rfl) ⟨295730, by rfl⟩ : syracuseStep 394307 = 591461) B591461
theorem B263249 : Blo 115785 263249 := bstep (se 2 (by rfl) ⟨98718, by rfl⟩ : syracuseStep 263249 = 197437) B197437
theorem B263267 : Blo 115785 263267 := bstep (se 1 (by rfl) ⟨197450, by rfl⟩ : syracuseStep 263267 = 394901) B394901
theorem B197761 : Blo 115785 197761 := bstep (se 2 (by rfl) ⟨74160, by rfl⟩ : syracuseStep 197761 = 148321) B148321
theorem B197795 : Blo 115785 197795 := bstep (se 1 (by rfl) ⟨148346, by rfl⟩ : syracuseStep 197795 = 296693) B296693
theorem B132259 : Blo 115785 132259 := bstep (se 1 (by rfl) ⟨99194, by rfl⟩ : syracuseStep 132259 = 198389) B198389
theorem B165073 : Blo 115785 165073 := bstep (se 2 (by rfl) ⟨61902, by rfl⟩ : syracuseStep 165073 = 123805) B123805
theorem B197923 : Blo 115785 197923 := bstep (se 1 (by rfl) ⟨148442, by rfl⟩ : syracuseStep 197923 = 296885) B296885
theorem B132403 : Blo 115785 132403 := bstep (se 1 (by rfl) ⟨99302, by rfl⟩ : syracuseStep 132403 = 198605) B198605
theorem B165187 : Blo 115785 165187 := bstep (se 1 (by rfl) ⟨123890, by rfl⟩ : syracuseStep 165187 = 247781) B247781
theorem B394577 : Blo 115785 394577 := bstep (se 2 (by rfl) ⟨147966, by rfl⟩ : syracuseStep 394577 = 295933) B295933
theorem B263537 : Blo 115785 263537 := bstep (se 2 (by rfl) ⟨98826, by rfl⟩ : syracuseStep 263537 = 197653) B197653
theorem B263555 : Blo 115785 263555 := bstep (se 1 (by rfl) ⟨197666, by rfl⟩ : syracuseStep 263555 = 395333) B395333
theorem B296369 : Blo 115785 296369 := bstep (se 2 (by rfl) ⟨111138, by rfl⟩ : syracuseStep 296369 = 222277) B222277
theorem B198065 : Blo 115785 198065 := bstep (se 2 (by rfl) ⟨74274, by rfl⟩ : syracuseStep 198065 = 148549) B148549
theorem B132547 : Blo 115785 132547 := bstep (se 1 (by rfl) ⟨99410, by rfl⟩ : syracuseStep 132547 = 198821) B198821
theorem B296419 : Blo 115785 296419 := bstep (se 1 (by rfl) ⟨222314, by rfl⟩ : syracuseStep 296419 = 444629) B444629
theorem B951821 : Blo 115785 951821 := bstep (se 3 (by rfl) ⟨178466, by rfl⟩ : syracuseStep 951821 = 356933) B356933
theorem B198193 : Blo 115785 198193 := bstep (se 2 (by rfl) ⟨74322, by rfl⟩ : syracuseStep 198193 = 148645) B148645
theorem B198227 : Blo 115785 198227 := bstep (se 1 (by rfl) ⟨148670, by rfl⟩ : syracuseStep 198227 = 297341) B297341
theorem B132691 : Blo 115785 132691 := bstep (se 1 (by rfl) ⟨99518, by rfl⟩ : syracuseStep 132691 = 199037) B199037
theorem B296561 : Blo 115785 296561 := bstep (se 2 (by rfl) ⟨111210, by rfl⟩ : syracuseStep 296561 = 222421) B222421
theorem B263825 : Blo 115785 263825 := bstep (se 2 (by rfl) ⟨98934, by rfl⟩ : syracuseStep 263825 = 197869) B197869
theorem B263843 : Blo 115785 263843 := bstep (se 1 (by rfl) ⟨197882, by rfl⟩ : syracuseStep 263843 = 395765) B395765
theorem B198355 : Blo 115785 198355 := bstep (se 1 (by rfl) ⟨148766, by rfl⟩ : syracuseStep 198355 = 297533) B297533
theorem B132835 : Blo 115785 132835 := bstep (se 1 (by rfl) ⟨99626, by rfl⟩ : syracuseStep 132835 = 199253) B199253
theorem B689905 : Blo 115785 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B198497 : Blo 115785 198497 := bstep (se 2 (by rfl) ⟨74436, by rfl⟩ : syracuseStep 198497 = 148873) B148873
theorem B395117 : Blo 115785 395117 := bstep (se 3 (by rfl) ⟨74084, by rfl⟩ : syracuseStep 395117 = 148169) B148169
theorem B132979 : Blo 115785 132979 := bstep (se 1 (by rfl) ⟨99734, by rfl⟩ : syracuseStep 132979 = 199469) B199469
theorem B395171 : Blo 115785 395171 := bstep (se 1 (by rfl) ⟨296378, by rfl⟩ : syracuseStep 395171 = 592757) B592757
theorem B264113 : Blo 115785 264113 := bstep (se 2 (by rfl) ⟨99042, by rfl⟩ : syracuseStep 264113 = 198085) B198085
theorem B264131 : Blo 115785 264131 := bstep (se 1 (by rfl) ⟨198098, by rfl⟩ : syracuseStep 264131 = 396197) B396197
theorem B198625 : Blo 115785 198625 := bstep (se 2 (by rfl) ⟨74484, by rfl⟩ : syracuseStep 198625 = 148969) B148969
theorem B198641 : Blo 115785 198641 := bstep (se 2 (by rfl) ⟨74490, by rfl⟩ : syracuseStep 198641 = 148981) B148981
theorem B198659 : Blo 115785 198659 := bstep (se 1 (by rfl) ⟨148994, by rfl⟩ : syracuseStep 198659 = 297989) B297989
theorem B133123 : Blo 115785 133123 := bstep (se 1 (by rfl) ⟨99842, by rfl⟩ : syracuseStep 133123 = 199685) B199685
theorem B329827 : Blo 115785 329827 := bstep (se 1 (by rfl) ⟨247370, by rfl⟩ : syracuseStep 329827 = 494741) B494741
theorem B198787 : Blo 115785 198787 := bstep (se 1 (by rfl) ⟨149090, by rfl⟩ : syracuseStep 198787 = 298181) B298181
theorem B133267 : Blo 115785 133267 := bstep (se 1 (by rfl) ⟨99950, by rfl⟩ : syracuseStep 133267 = 199901) B199901
theorem B395441 : Blo 115785 395441 := bstep (se 2 (by rfl) ⟨148290, by rfl⟩ : syracuseStep 395441 = 296581) B296581
theorem B1345733 : Blo 115785 1345733 := bstep (se 4 (by rfl) ⟨126162, by rfl⟩ : syracuseStep 1345733 = 252325) B252325
theorem B264401 : Blo 115785 264401 := bstep (se 2 (by rfl) ⟨99150, by rfl⟩ : syracuseStep 264401 = 198301) B198301
theorem B264419 : Blo 115785 264419 := bstep (se 1 (by rfl) ⟨198314, by rfl⟩ : syracuseStep 264419 = 396629) B396629
theorem B362723 : Blo 115785 362723 := bstep (se 1 (by rfl) ⟨272042, by rfl⟩ : syracuseStep 362723 = 544085) B544085
theorem B329987 : Blo 115785 329987 := bstep (se 1 (by rfl) ⟨247490, by rfl⟩ : syracuseStep 329987 = 494981) B494981
theorem B198929 : Blo 115785 198929 := bstep (se 2 (by rfl) ⟨74598, by rfl⟩ : syracuseStep 198929 = 149197) B149197
theorem B133411 : Blo 115785 133411 := bstep (se 1 (by rfl) ⟨100058, by rfl⟩ : syracuseStep 133411 = 200117) B200117
theorem B199057 : Blo 115785 199057 := bstep (se 2 (by rfl) ⟨74646, by rfl⟩ : syracuseStep 199057 = 149293) B149293
theorem B133555 : Blo 115785 133555 := bstep (se 1 (by rfl) ⟨100166, by rfl⟩ : syracuseStep 133555 = 200333) B200333
theorem B199091 : Blo 115785 199091 := bstep (se 1 (by rfl) ⟨149318, by rfl⟩ : syracuseStep 199091 = 298637) B298637
theorem B264689 : Blo 115785 264689 := bstep (se 2 (by rfl) ⟨99258, by rfl⟩ : syracuseStep 264689 = 198517) B198517
theorem B264707 : Blo 115785 264707 := bstep (se 1 (by rfl) ⟨198530, by rfl⟩ : syracuseStep 264707 = 397061) B397061
theorem B592433 : Blo 115785 592433 := bstep (se 2 (by rfl) ⟨222162, by rfl⟩ : syracuseStep 592433 = 444325) B444325
theorem B199219 : Blo 115785 199219 := bstep (se 1 (by rfl) ⟨149414, by rfl⟩ : syracuseStep 199219 = 298829) B298829
theorem B133699 : Blo 115785 133699 := bstep (se 1 (by rfl) ⟨100274, by rfl⟩ : syracuseStep 133699 = 200549) B200549
theorem B297553 : Blo 115785 297553 := bstep (se 2 (by rfl) ⟨111582, by rfl⟩ : syracuseStep 297553 = 223165) B223165
theorem B756337 : Blo 115785 756337 := bstep (se 2 (by rfl) ⟨283626, by rfl⟩ : syracuseStep 756337 = 567253) B567253
theorem B166531 : Blo 115785 166531 := bstep (se 1 (by rfl) ⟨124898, by rfl⟩ : syracuseStep 166531 = 249797) B249797
theorem B199361 : Blo 115785 199361 := bstep (se 2 (by rfl) ⟨74760, by rfl⟩ : syracuseStep 199361 = 149521) B149521
theorem B395981 : Blo 115785 395981 := bstep (se 3 (by rfl) ⟨74246, by rfl⟩ : syracuseStep 395981 = 148493) B148493
theorem B133843 : Blo 115785 133843 := bstep (se 1 (by rfl) ⟨100382, by rfl⟩ : syracuseStep 133843 = 200765) B200765
theorem B1018595 : Blo 115785 1018595 := bstep (se 1 (by rfl) ⟨763946, by rfl⟩ : syracuseStep 1018595 = 1527893) B1527893
theorem B396035 : Blo 115785 396035 := bstep (se 1 (by rfl) ⟨297026, by rfl⟩ : syracuseStep 396035 = 594053) B594053
theorem B264977 : Blo 115785 264977 := bstep (se 2 (by rfl) ⟨99366, by rfl⟩ : syracuseStep 264977 = 198733) B198733
theorem B264995 : Blo 115785 264995 := bstep (se 1 (by rfl) ⟨198746, by rfl⟩ : syracuseStep 264995 = 397493) B397493
theorem B1575733 : Blo 115785 1575733 := bstep (se 5 (by rfl) ⟨73862, by rfl⟩ : syracuseStep 1575733 = 147725) B147725
theorem B199489 : Blo 115785 199489 := bstep (se 2 (by rfl) ⟨74808, by rfl⟩ : syracuseStep 199489 = 149617) B149617
theorem B1084229 : Blo 115785 1084229 := bstep (se 4 (by rfl) ⟨101646, by rfl⟩ : syracuseStep 1084229 = 203293) B203293
theorem B297827 : Blo 115785 297827 := bstep (se 1 (by rfl) ⟨223370, by rfl⟩ : syracuseStep 297827 = 446741) B446741
theorem B199523 : Blo 115785 199523 := bstep (se 1 (by rfl) ⟨149642, by rfl⟩ : syracuseStep 199523 = 299285) B299285
theorem B133987 : Blo 115785 133987 := bstep (se 1 (by rfl) ⟨100490, by rfl⟩ : syracuseStep 133987 = 200981) B200981
theorem B199651 : Blo 115785 199651 := bstep (se 1 (by rfl) ⟨149738, by rfl⟩ : syracuseStep 199651 = 299477) B299477
theorem B134131 : Blo 115785 134131 := bstep (se 1 (by rfl) ⟨100598, by rfl⟩ : syracuseStep 134131 = 201197) B201197
theorem B396305 : Blo 115785 396305 := bstep (se 2 (by rfl) ⟨148614, by rfl⟩ : syracuseStep 396305 = 297229) B297229
theorem B298019 : Blo 115785 298019 := bstep (se 1 (by rfl) ⟨223514, by rfl⟩ : syracuseStep 298019 = 447029) B447029
theorem B265265 : Blo 115785 265265 := bstep (se 2 (by rfl) ⟨99474, by rfl⟩ : syracuseStep 265265 = 198949) B198949
theorem B265283 : Blo 115785 265283 := bstep (se 1 (by rfl) ⟨198962, by rfl⟩ : syracuseStep 265283 = 397925) B397925
theorem B887921 : Blo 115785 887921 := bstep (se 2 (by rfl) ⟨332970, by rfl⟩ : syracuseStep 887921 = 665941) B665941
theorem B199793 : Blo 115785 199793 := bstep (se 2 (by rfl) ⟨74922, by rfl⟩ : syracuseStep 199793 = 149845) B149845
theorem B134275 : Blo 115785 134275 := bstep (se 1 (by rfl) ⟨100706, by rfl⟩ : syracuseStep 134275 = 201413) B201413
theorem B199921 : Blo 115785 199921 := bstep (se 2 (by rfl) ⟨74970, by rfl⟩ : syracuseStep 199921 = 149941) B149941
theorem B199955 : Blo 115785 199955 := bstep (se 1 (by rfl) ⟨149966, by rfl⟩ : syracuseStep 199955 = 299933) B299933
theorem B134419 : Blo 115785 134419 := bstep (se 1 (by rfl) ⟨100814, by rfl⟩ : syracuseStep 134419 = 201629) B201629
theorem B331057 : Blo 115785 331057 := bstep (se 2 (by rfl) ⟨124146, by rfl⟩ : syracuseStep 331057 = 248293) B248293
theorem B265553 : Blo 115785 265553 := bstep (se 2 (by rfl) ⟨99582, by rfl⟩ : syracuseStep 265553 = 199165) B199165
theorem B265571 : Blo 115785 265571 := bstep (se 1 (by rfl) ⟨199178, by rfl⟩ : syracuseStep 265571 = 398357) B398357
theorem B200083 : Blo 115785 200083 := bstep (se 1 (by rfl) ⟨150062, by rfl⟩ : syracuseStep 200083 = 300125) B300125
theorem B134563 : Blo 115785 134563 := bstep (se 1 (by rfl) ⟨100922, by rfl⟩ : syracuseStep 134563 = 201845) B201845
theorem B200225 : Blo 115785 200225 := bstep (se 2 (by rfl) ⟨75084, by rfl⟩ : syracuseStep 200225 = 150169) B150169
theorem B396845 : Blo 115785 396845 := bstep (se 3 (by rfl) ⟨74408, by rfl⟩ : syracuseStep 396845 = 148817) B148817
theorem B134707 : Blo 115785 134707 := bstep (se 1 (by rfl) ⟨101030, by rfl⟩ : syracuseStep 134707 = 202061) B202061
theorem B396899 : Blo 115785 396899 := bstep (se 1 (by rfl) ⟨297674, by rfl⟩ : syracuseStep 396899 = 595349) B595349
theorem B265841 : Blo 115785 265841 := bstep (se 2 (by rfl) ⟨99690, by rfl⟩ : syracuseStep 265841 = 199381) B199381
theorem B265859 : Blo 115785 265859 := bstep (se 1 (by rfl) ⟨199394, by rfl⟩ : syracuseStep 265859 = 398789) B398789
theorem B200353 : Blo 115785 200353 := bstep (se 2 (by rfl) ⟨75132, by rfl⟩ : syracuseStep 200353 = 150265) B150265
theorem B200387 : Blo 115785 200387 := bstep (se 1 (by rfl) ⟨150290, by rfl⟩ : syracuseStep 200387 = 300581) B300581
theorem B626417 : Blo 115785 626417 := bstep (se 2 (by rfl) ⟨234906, by rfl⟩ : syracuseStep 626417 = 469813) B469813
theorem B167665 : Blo 115785 167665 := bstep (se 2 (by rfl) ⟨62874, by rfl⟩ : syracuseStep 167665 = 125749) B125749
theorem B200515 : Blo 115785 200515 := bstep (se 1 (by rfl) ⟨150386, by rfl⟩ : syracuseStep 200515 = 300773) B300773
theorem B167761 : Blo 115785 167761 := bstep (se 2 (by rfl) ⟨62910, by rfl⟩ : syracuseStep 167761 = 125821) B125821
theorem B397169 : Blo 115785 397169 := bstep (se 2 (by rfl) ⟨148938, by rfl⟩ : syracuseStep 397169 = 297877) B297877
theorem B266129 : Blo 115785 266129 := bstep (se 2 (by rfl) ⟨99798, by rfl⟩ : syracuseStep 266129 = 199597) B199597
theorem B266147 : Blo 115785 266147 := bstep (se 1 (by rfl) ⟨199610, by rfl⟩ : syracuseStep 266147 = 399221) B399221
theorem B135091 : Blo 115785 135091 := bstep (se 1 (by rfl) ⟨101318, by rfl⟩ : syracuseStep 135091 = 202637) B202637
theorem B298961 : Blo 115785 298961 := bstep (se 2 (by rfl) ⟨112110, by rfl⟩ : syracuseStep 298961 = 224221) B224221
theorem B200657 : Blo 115785 200657 := bstep (se 2 (by rfl) ⟨75246, by rfl⟩ : syracuseStep 200657 = 150493) B150493
theorem B593891 : Blo 115785 593891 := bstep (se 1 (by rfl) ⟨445418, by rfl⟩ : syracuseStep 593891 = 890837) B890837
theorem B299011 : Blo 115785 299011 := bstep (se 1 (by rfl) ⟨224258, by rfl⟩ : syracuseStep 299011 = 448517) B448517
theorem B495629 : Blo 115785 495629 := bstep (se 3 (by rfl) ⟨92930, by rfl⟩ : syracuseStep 495629 = 185861) B185861
theorem B331793 : Blo 115785 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B495665 : Blo 115785 495665 := bstep (se 2 (by rfl) ⟨185874, by rfl⟩ : syracuseStep 495665 = 371749) B371749
theorem B200785 : Blo 115785 200785 := bstep (se 2 (by rfl) ⟨75294, by rfl⟩ : syracuseStep 200785 = 150589) B150589
theorem B200819 : Blo 115785 200819 := bstep (se 1 (by rfl) ⟨150614, by rfl⟩ : syracuseStep 200819 = 301229) B301229
theorem B2330765 : Blo 115785 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B299153 : Blo 115785 299153 := bstep (se 2 (by rfl) ⟨112182, by rfl⟩ : syracuseStep 299153 = 224365) B224365
theorem B266417 : Blo 115785 266417 := bstep (se 2 (by rfl) ⟨99906, by rfl⟩ : syracuseStep 266417 = 199813) B199813
theorem B266435 : Blo 115785 266435 := bstep (se 1 (by rfl) ⟨199826, by rfl⟩ : syracuseStep 266435 = 399653) B399653
theorem B430285 : Blo 115785 430285 := bstep (se 3 (by rfl) ⟨80678, by rfl⟩ : syracuseStep 430285 = 161357) B161357
theorem B200947 : Blo 115785 200947 := bstep (se 1 (by rfl) ⟨150710, by rfl⟩ : syracuseStep 200947 = 301421) B301421
theorem B168257 : Blo 115785 168257 := bstep (se 2 (by rfl) ⟨63096, by rfl⟩ : syracuseStep 168257 = 126193) B126193
theorem B201089 : Blo 115785 201089 := bstep (se 2 (by rfl) ⟨75408, by rfl⟩ : syracuseStep 201089 = 150817) B150817
theorem B397709 : Blo 115785 397709 := bstep (se 3 (by rfl) ⟨74570, by rfl⟩ : syracuseStep 397709 = 149141) B149141
theorem B397763 : Blo 115785 397763 := bstep (se 1 (by rfl) ⟨298322, by rfl⟩ : syracuseStep 397763 = 596645) B596645
theorem B266705 : Blo 115785 266705 := bstep (se 2 (by rfl) ⟨100014, by rfl⟩ : syracuseStep 266705 = 200029) B200029
theorem B201187 : Blo 115785 201187 := bstep (se 1 (by rfl) ⟨150890, by rfl⟩ : syracuseStep 201187 = 301781) B301781
theorem B266723 : Blo 115785 266723 := bstep (se 1 (by rfl) ⟨200042, by rfl⟩ : syracuseStep 266723 = 400085) B400085
theorem B201217 : Blo 115785 201217 := bstep (se 2 (by rfl) ⟨75456, by rfl⟩ : syracuseStep 201217 = 150913) B150913
theorem B201251 : Blo 115785 201251 := bstep (se 1 (by rfl) ⟨150938, by rfl⟩ : syracuseStep 201251 = 301877) B301877
theorem B332333 : Blo 115785 332333 := bstep (se 3 (by rfl) ⟨62312, by rfl⟩ : syracuseStep 332333 = 124625) B124625
theorem B660109 : Blo 115785 660109 := bstep (se 3 (by rfl) ⟨123770, by rfl⟩ : syracuseStep 660109 = 247541) B247541
theorem B201379 : Blo 115785 201379 := bstep (se 1 (by rfl) ⟨151034, by rfl⟩ : syracuseStep 201379 = 302069) B302069
theorem B168643 : Blo 115785 168643 := bstep (se 1 (by rfl) ⟨126482, by rfl⟩ : syracuseStep 168643 = 252965) B252965
theorem B398033 : Blo 115785 398033 := bstep (se 2 (by rfl) ⟨149262, by rfl⟩ : syracuseStep 398033 = 298525) B298525
theorem B332515 : Blo 115785 332515 := bstep (se 1 (by rfl) ⟨249386, by rfl⟩ : syracuseStep 332515 = 498773) B498773
theorem B266993 : Blo 115785 266993 := bstep (se 2 (by rfl) ⟨100122, by rfl⟩ : syracuseStep 266993 = 200245) B200245
theorem B267011 : Blo 115785 267011 := bstep (se 1 (by rfl) ⟨200258, by rfl⟩ : syracuseStep 267011 = 400517) B400517
theorem B594701 : Blo 115785 594701 := bstep (se 3 (by rfl) ⟨111506, by rfl⟩ : syracuseStep 594701 = 223013) B223013
theorem B332561 : Blo 115785 332561 := bstep (se 2 (by rfl) ⟨124710, by rfl⟩ : syracuseStep 332561 = 249421) B249421
theorem B201521 : Blo 115785 201521 := bstep (se 2 (by rfl) ⟨75570, by rfl⟩ : syracuseStep 201521 = 151141) B151141
theorem B201649 : Blo 115785 201649 := bstep (se 2 (by rfl) ⟨75618, by rfl⟩ : syracuseStep 201649 = 151237) B151237
theorem B201683 : Blo 115785 201683 := bstep (se 1 (by rfl) ⟨151262, by rfl⟩ : syracuseStep 201683 = 302525) B302525
theorem B267281 : Blo 115785 267281 := bstep (se 2 (by rfl) ⟨100230, by rfl⟩ : syracuseStep 267281 = 200461) B200461
theorem B267299 : Blo 115785 267299 := bstep (se 1 (by rfl) ⟨200474, by rfl⟩ : syracuseStep 267299 = 400949) B400949
theorem B201811 : Blo 115785 201811 := bstep (se 1 (by rfl) ⟨151358, by rfl⟩ : syracuseStep 201811 = 302717) B302717
theorem B300145 : Blo 115785 300145 := bstep (se 2 (by rfl) ⟨112554, by rfl⟩ : syracuseStep 300145 = 225109) B225109
theorem B169123 : Blo 115785 169123 := bstep (se 1 (by rfl) ⟨126842, by rfl⟩ : syracuseStep 169123 = 253685) B253685
theorem B201953 : Blo 115785 201953 := bstep (se 2 (by rfl) ⟨75732, by rfl⟩ : syracuseStep 201953 = 151465) B151465
theorem B398573 : Blo 115785 398573 := bstep (se 3 (by rfl) ⟨74732, by rfl⟩ : syracuseStep 398573 = 149465) B149465
theorem B169219 : Blo 115785 169219 := bstep (se 1 (by rfl) ⟨126914, by rfl⟩ : syracuseStep 169219 = 253829) B253829
theorem B398627 : Blo 115785 398627 := bstep (se 1 (by rfl) ⟨298970, by rfl⟩ : syracuseStep 398627 = 597941) B597941
theorem B267569 : Blo 115785 267569 := bstep (se 2 (by rfl) ⟨100338, by rfl⟩ : syracuseStep 267569 = 200677) B200677
theorem B267587 : Blo 115785 267587 := bstep (se 1 (by rfl) ⟨200690, by rfl⟩ : syracuseStep 267587 = 401381) B401381
theorem B202081 : Blo 115785 202081 := bstep (se 2 (by rfl) ⟨75780, by rfl⟩ : syracuseStep 202081 = 151561) B151561
theorem B300419 : Blo 115785 300419 := bstep (se 1 (by rfl) ⟨225314, by rfl⟩ : syracuseStep 300419 = 450629) B450629
theorem B202115 : Blo 115785 202115 := bstep (se 1 (by rfl) ⟨151586, by rfl⟩ : syracuseStep 202115 = 303173) B303173
theorem B398897 : Blo 115785 398897 := bstep (se 2 (by rfl) ⟨149586, by rfl⟩ : syracuseStep 398897 = 299173) B299173
theorem B300611 : Blo 115785 300611 := bstep (se 1 (by rfl) ⟨225458, by rfl⟩ : syracuseStep 300611 = 450917) B450917
theorem B267857 : Blo 115785 267857 := bstep (se 2 (by rfl) ⟨100446, by rfl⟩ : syracuseStep 267857 = 200893) B200893
theorem B267875 : Blo 115785 267875 := bstep (se 1 (by rfl) ⟨200906, by rfl⟩ : syracuseStep 267875 = 401813) B401813
theorem B267985 : Blo 115785 267985 := bstep (se 2 (by rfl) ⟨100494, by rfl⟩ : syracuseStep 267985 = 200989) B200989
theorem B431843 : Blo 115785 431843 := bstep (se 1 (by rfl) ⟨323882, by rfl⟩ : syracuseStep 431843 = 647765) B647765
theorem B169715 : Blo 115785 169715 := bstep (se 1 (by rfl) ⟨127286, by rfl⟩ : syracuseStep 169715 = 254573) B254573
theorem B268145 : Blo 115785 268145 := bstep (se 2 (by rfl) ⟨100554, by rfl⟩ : syracuseStep 268145 = 201109) B201109
theorem B268163 : Blo 115785 268163 := bstep (se 1 (by rfl) ⟨201122, by rfl⟩ : syracuseStep 268163 = 402245) B402245
theorem B399437 : Blo 115785 399437 := bstep (se 3 (by rfl) ⟨74894, by rfl⟩ : syracuseStep 399437 = 149789) B149789
theorem B399491 : Blo 115785 399491 := bstep (se 1 (by rfl) ⟨299618, by rfl⟩ : syracuseStep 399491 = 599237) B599237
theorem B268433 : Blo 115785 268433 := bstep (se 2 (by rfl) ⟨100662, by rfl⟩ : syracuseStep 268433 = 201325) B201325
theorem B268451 : Blo 115785 268451 := bstep (se 1 (by rfl) ⟨201338, by rfl⟩ : syracuseStep 268451 = 402677) B402677
theorem B334019 : Blo 115785 334019 := bstep (se 1 (by rfl) ⟨250514, by rfl⟩ : syracuseStep 334019 = 501029) B501029
theorem B1808581 : Blo 115785 1808581 := bstep (se 4 (by rfl) ⟨169554, by rfl⟩ : syracuseStep 1808581 = 339109) B339109
theorem B5445845 : Blo 115785 5445845 := bstep (se 7 (by rfl) ⟨63818, by rfl⟩ : syracuseStep 5445845 = 127637) B127637
theorem B170353 : Blo 115785 170353 := bstep (se 2 (by rfl) ⟨63882, by rfl⟩ : syracuseStep 170353 = 127765) B127765
theorem B399761 : Blo 115785 399761 := bstep (se 2 (by rfl) ⟨149910, by rfl⟩ : syracuseStep 399761 = 299821) B299821
theorem B268721 : Blo 115785 268721 := bstep (se 2 (by rfl) ⟨100770, by rfl⟩ : syracuseStep 268721 = 201541) B201541
theorem B268739 : Blo 115785 268739 := bstep (se 1 (by rfl) ⟨201554, by rfl⟩ : syracuseStep 268739 = 403109) B403109
theorem B301553 : Blo 115785 301553 := bstep (se 2 (by rfl) ⟨113082, by rfl⟩ : syracuseStep 301553 = 226165) B226165
theorem B301603 : Blo 115785 301603 := bstep (se 1 (by rfl) ⟨226202, by rfl⟩ : syracuseStep 301603 = 452405) B452405
theorem B662093 : Blo 115785 662093 := bstep (se 3 (by rfl) ⟨124142, by rfl⟩ : syracuseStep 662093 = 248285) B248285
theorem B301745 : Blo 115785 301745 := bstep (se 2 (by rfl) ⟨113154, by rfl⟩ : syracuseStep 301745 = 226309) B226309
theorem B269009 : Blo 115785 269009 := bstep (se 2 (by rfl) ⟨100878, by rfl⟩ : syracuseStep 269009 = 201757) B201757
theorem B269027 : Blo 115785 269027 := bstep (se 1 (by rfl) ⟨201770, by rfl⟩ : syracuseStep 269027 = 403541) B403541
theorem B269123 : Blo 115785 269123 := bstep (se 1 (by rfl) ⟨201842, by rfl⟩ : syracuseStep 269123 = 403685) B403685
theorem B400301 : Blo 115785 400301 := bstep (se 3 (by rfl) ⟨75056, by rfl⟩ : syracuseStep 400301 = 150113) B150113
theorem B400355 : Blo 115785 400355 := bstep (se 1 (by rfl) ⟨300266, by rfl⟩ : syracuseStep 400355 = 600533) B600533
theorem B269297 : Blo 115785 269297 := bstep (se 2 (by rfl) ⟨100986, by rfl⟩ : syracuseStep 269297 = 201973) B201973
theorem B269315 : Blo 115785 269315 := bstep (se 1 (by rfl) ⟨201986, by rfl⟩ : syracuseStep 269315 = 403973) B403973
theorem B171217 : Blo 115785 171217 := bstep (se 2 (by rfl) ⟨64206, by rfl⟩ : syracuseStep 171217 = 128413) B128413
theorem B400625 : Blo 115785 400625 := bstep (se 2 (by rfl) ⟨150234, by rfl⟩ : syracuseStep 400625 = 300469) B300469
theorem B335117 : Blo 115785 335117 := bstep (se 3 (by rfl) ⟨62834, by rfl⟩ : syracuseStep 335117 = 125669) B125669
theorem B335249 : Blo 115785 335249 := bstep (se 2 (by rfl) ⟨125718, by rfl⟩ : syracuseStep 335249 = 251437) B251437
theorem B663025 : Blo 115785 663025 := bstep (se 2 (by rfl) ⟨248634, by rfl⟩ : syracuseStep 663025 = 497269) B497269
theorem B597617 : Blo 115785 597617 := bstep (se 2 (by rfl) ⟨224106, by rfl⟩ : syracuseStep 597617 = 448213) B448213
theorem B302737 : Blo 115785 302737 := bstep (se 2 (by rfl) ⟨113526, by rfl⟩ : syracuseStep 302737 = 227053) B227053
theorem B401165 : Blo 115785 401165 := bstep (se 3 (by rfl) ⟨75218, by rfl⟩ : syracuseStep 401165 = 150437) B150437
theorem B401219 : Blo 115785 401219 := bstep (se 1 (by rfl) ⟨300914, by rfl⟩ : syracuseStep 401219 = 601829) B601829
theorem B761669 : Blo 115785 761669 := bstep (se 4 (by rfl) ⟨71406, by rfl⟩ : syracuseStep 761669 = 142813) B142813
theorem B1351565 : Blo 115785 1351565 := bstep (se 3 (by rfl) ⟨253418, by rfl⟩ : syracuseStep 1351565 = 506837) B506837
theorem B303011 : Blo 115785 303011 := bstep (se 1 (by rfl) ⟨227258, by rfl⟩ : syracuseStep 303011 = 454517) B454517
theorem B139315 : Blo 115785 139315 := bstep (se 1 (by rfl) ⟨104486, by rfl⟩ : syracuseStep 139315 = 208973) B208973
theorem B237649 : Blo 115785 237649 := bstep (se 2 (by rfl) ⟨89118, by rfl⟩ : syracuseStep 237649 = 178237) B178237
theorem B401489 : Blo 115785 401489 := bstep (se 2 (by rfl) ⟨150558, by rfl⟩ : syracuseStep 401489 = 301117) B301117
theorem B303203 : Blo 115785 303203 := bstep (se 1 (by rfl) ⟨227402, by rfl⟩ : syracuseStep 303203 = 454805) B454805
theorem B500003 : Blo 115785 500003 := bstep (se 1 (by rfl) ⟨375002, by rfl⟩ : syracuseStep 500003 = 750005) B750005
theorem B991601 : Blo 115785 991601 := bstep (se 2 (by rfl) ⟨371850, by rfl⟩ : syracuseStep 991601 = 743701) B743701
theorem B402029 : Blo 115785 402029 := bstep (se 3 (by rfl) ⟨75380, by rfl⟩ : syracuseStep 402029 = 150761) B150761
theorem B2007665 : Blo 115785 2007665 := bstep (se 2 (by rfl) ⟨752874, by rfl⟩ : syracuseStep 2007665 = 1505749) B1505749
theorem B402083 : Blo 115785 402083 := bstep (se 1 (by rfl) ⟨301562, by rfl⟩ : syracuseStep 402083 = 603125) B603125
theorem B303875 : Blo 115785 303875 := bstep (se 1 (by rfl) ⟨227906, by rfl⟩ : syracuseStep 303875 = 455813) B455813
theorem B336707 : Blo 115785 336707 := bstep (se 1 (by rfl) ⟨252530, by rfl⟩ : syracuseStep 336707 = 505061) B505061
theorem B631651 : Blo 115785 631651 := bstep (se 1 (by rfl) ⟨473738, by rfl⟩ : syracuseStep 631651 = 947477) B947477
theorem B566129 : Blo 115785 566129 := bstep (se 2 (by rfl) ⟨212298, by rfl⟩ : syracuseStep 566129 = 424597) B424597
theorem B664483 : Blo 115785 664483 := bstep (se 1 (by rfl) ⟨498362, by rfl⟩ : syracuseStep 664483 = 996725) B996725
theorem B402353 : Blo 115785 402353 := bstep (se 2 (by rfl) ⟨150882, by rfl⟩ : syracuseStep 402353 = 301765) B301765
theorem B599075 : Blo 115785 599075 := bstep (se 1 (by rfl) ⟨449306, by rfl⟩ : syracuseStep 599075 = 898613) B898613
theorem B271459 : Blo 115785 271459 := bstep (se 1 (by rfl) ⟨203594, by rfl⟩ : syracuseStep 271459 = 407189) B407189
theorem B238993 : Blo 115785 238993 := bstep (se 2 (by rfl) ⟨89622, by rfl⟩ : syracuseStep 238993 = 179245) B179245
theorem B665009 : Blo 115785 665009 := bstep (se 2 (by rfl) ⟨249378, by rfl⟩ : syracuseStep 665009 = 498757) B498757
theorem B402893 : Blo 115785 402893 := bstep (se 3 (by rfl) ⟨75542, by rfl⟩ : syracuseStep 402893 = 151085) B151085
theorem B402947 : Blo 115785 402947 := bstep (se 1 (by rfl) ⟨302210, by rfl⟩ : syracuseStep 402947 = 604421) B604421
theorem B402961 : Blo 115785 402961 := bstep (se 2 (by rfl) ⟨151110, by rfl⟩ : syracuseStep 402961 = 302221) B302221
theorem B337517 : Blo 115785 337517 := bstep (se 3 (by rfl) ⟨63284, by rfl⟩ : syracuseStep 337517 = 126569) B126569
theorem B173681 : Blo 115785 173681 := bstep (se 2 (by rfl) ⟨65130, by rfl⟩ : syracuseStep 173681 = 130261) B130261
theorem B173699 : Blo 115785 173699 := bstep (se 1 (by rfl) ⟨130274, by rfl⟩ : syracuseStep 173699 = 260549) B260549
theorem B173729 : Blo 115785 173729 := bstep (se 2 (by rfl) ⟨65148, by rfl⟩ : syracuseStep 173729 = 130297) B130297
theorem B173747 : Blo 115785 173747 := bstep (se 1 (by rfl) ⟨130310, by rfl⟩ : syracuseStep 173747 = 260621) B260621
theorem B173777 : Blo 115785 173777 := bstep (se 2 (by rfl) ⟨65166, by rfl⟩ : syracuseStep 173777 = 130333) B130333
theorem B173795 : Blo 115785 173795 := bstep (se 1 (by rfl) ⟨130346, by rfl⟩ : syracuseStep 173795 = 260693) B260693
theorem B173825 : Blo 115785 173825 := bstep (se 2 (by rfl) ⟨65184, by rfl⟩ : syracuseStep 173825 = 130369) B130369
theorem B141059 : Blo 115785 141059 := bstep (se 1 (by rfl) ⟨105794, by rfl⟩ : syracuseStep 141059 = 211589) B211589
theorem B403217 : Blo 115785 403217 := bstep (se 2 (by rfl) ⟨151206, by rfl⟩ : syracuseStep 403217 = 302413) B302413
theorem B173843 : Blo 115785 173843 := bstep (se 1 (by rfl) ⟨130382, by rfl⟩ : syracuseStep 173843 = 260765) B260765
theorem B337709 : Blo 115785 337709 := bstep (se 3 (by rfl) ⟨63320, by rfl⟩ : syracuseStep 337709 = 126641) B126641
theorem B173873 : Blo 115785 173873 := bstep (se 2 (by rfl) ⟨65202, by rfl⟩ : syracuseStep 173873 = 130405) B130405
theorem B141107 : Blo 115785 141107 := bstep (se 1 (by rfl) ⟨105830, by rfl⟩ : syracuseStep 141107 = 211661) B211661
theorem B173891 : Blo 115785 173891 := bstep (se 1 (by rfl) ⟨130418, by rfl⟩ : syracuseStep 173891 = 260837) B260837
theorem B599885 : Blo 115785 599885 := bstep (se 3 (by rfl) ⟨112478, by rfl⟩ : syracuseStep 599885 = 224957) B224957
theorem B173921 : Blo 115785 173921 := bstep (se 2 (by rfl) ⟨65220, by rfl⟩ : syracuseStep 173921 = 130441) B130441
theorem B173939 : Blo 115785 173939 := bstep (se 1 (by rfl) ⟨130454, by rfl⟩ : syracuseStep 173939 = 260909) B260909
theorem B173969 : Blo 115785 173969 := bstep (se 2 (by rfl) ⟨65238, by rfl⟩ : syracuseStep 173969 = 130477) B130477
theorem B141203 : Blo 115785 141203 := bstep (se 1 (by rfl) ⟨105902, by rfl⟩ : syracuseStep 141203 = 211805) B211805
theorem B173987 : Blo 115785 173987 := bstep (se 1 (by rfl) ⟨130490, by rfl⟩ : syracuseStep 173987 = 260981) B260981
theorem B174017 : Blo 115785 174017 := bstep (se 2 (by rfl) ⟨65256, by rfl⟩ : syracuseStep 174017 = 130513) B130513
theorem B174035 : Blo 115785 174035 := bstep (se 1 (by rfl) ⟨130526, by rfl⟩ : syracuseStep 174035 = 261053) B261053
theorem B174065 : Blo 115785 174065 := bstep (se 2 (by rfl) ⟨65274, by rfl⟩ : syracuseStep 174065 = 130549) B130549
theorem B174083 : Blo 115785 174083 := bstep (se 1 (by rfl) ⟨130562, by rfl⟩ : syracuseStep 174083 = 261125) B261125
theorem B174113 : Blo 115785 174113 := bstep (se 2 (by rfl) ⟨65292, by rfl⟩ : syracuseStep 174113 = 130585) B130585
theorem B174131 : Blo 115785 174131 := bstep (se 1 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 174131 = 261197) B261197
theorem B174161 : Blo 115785 174161 := bstep (se 2 (by rfl) ⟨65310, by rfl⟩ : syracuseStep 174161 = 130621) B130621
theorem B174179 : Blo 115785 174179 := bstep (se 1 (by rfl) ⟨130634, by rfl⟩ : syracuseStep 174179 = 261269) B261269
theorem B174209 : Blo 115785 174209 := bstep (se 2 (by rfl) ⟨65328, by rfl⟩ : syracuseStep 174209 = 130657) B130657
theorem B174227 : Blo 115785 174227 := bstep (se 1 (by rfl) ⟨130670, by rfl⟩ : syracuseStep 174227 = 261341) B261341
theorem B174257 : Blo 115785 174257 := bstep (se 2 (by rfl) ⟨65346, by rfl⟩ : syracuseStep 174257 = 130693) B130693
theorem B174275 : Blo 115785 174275 := bstep (se 1 (by rfl) ⟨130706, by rfl⟩ : syracuseStep 174275 = 261413) B261413
theorem B2009285 : Blo 115785 2009285 := bstep (se 4 (by rfl) ⟨188370, by rfl⟩ : syracuseStep 2009285 = 376741) B376741
theorem B174305 : Blo 115785 174305 := bstep (se 2 (by rfl) ⟨65364, by rfl⟩ : syracuseStep 174305 = 130729) B130729
theorem B174323 : Blo 115785 174323 := bstep (se 1 (by rfl) ⟨130742, by rfl⟩ : syracuseStep 174323 = 261485) B261485
theorem B174353 : Blo 115785 174353 := bstep (se 2 (by rfl) ⟨65382, by rfl⟩ : syracuseStep 174353 = 130765) B130765
theorem B174371 : Blo 115785 174371 := bstep (se 1 (by rfl) ⟨130778, by rfl⟩ : syracuseStep 174371 = 261557) B261557
theorem B403757 : Blo 115785 403757 := bstep (se 3 (by rfl) ⟨75704, by rfl⟩ : syracuseStep 403757 = 151409) B151409
theorem B370993 : Blo 115785 370993 := bstep (se 2 (by rfl) ⟨139122, by rfl⟩ : syracuseStep 370993 = 278245) B278245
theorem B174401 : Blo 115785 174401 := bstep (se 2 (by rfl) ⟨65400, by rfl⟩ : syracuseStep 174401 = 130801) B130801
theorem B174419 : Blo 115785 174419 := bstep (se 1 (by rfl) ⟨130814, by rfl⟩ : syracuseStep 174419 = 261629) B261629
theorem B403811 : Blo 115785 403811 := bstep (se 1 (by rfl) ⟨302858, by rfl⟩ : syracuseStep 403811 = 605717) B605717
theorem B174449 : Blo 115785 174449 := bstep (se 2 (by rfl) ⟨65418, by rfl⟩ : syracuseStep 174449 = 130837) B130837
theorem B174467 : Blo 115785 174467 := bstep (se 1 (by rfl) ⟨130850, by rfl⟩ : syracuseStep 174467 = 261701) B261701
theorem B174497 : Blo 115785 174497 := bstep (se 2 (by rfl) ⟨65436, by rfl⟩ : syracuseStep 174497 = 130873) B130873
theorem B174515 : Blo 115785 174515 := bstep (se 1 (by rfl) ⟨130886, by rfl⟩ : syracuseStep 174515 = 261773) B261773
theorem B174545 : Blo 115785 174545 := bstep (se 2 (by rfl) ⟨65454, by rfl⟩ : syracuseStep 174545 = 130909) B130909
theorem B174563 : Blo 115785 174563 := bstep (se 1 (by rfl) ⟨130922, by rfl⟩ : syracuseStep 174563 = 261845) B261845
theorem B174593 : Blo 115785 174593 := bstep (se 2 (by rfl) ⟨65472, by rfl⟩ : syracuseStep 174593 = 130945) B130945
theorem B174611 : Blo 115785 174611 := bstep (se 1 (by rfl) ⟨130958, by rfl⟩ : syracuseStep 174611 = 261917) B261917
theorem B174641 : Blo 115785 174641 := bstep (se 2 (by rfl) ⟨65490, by rfl⟩ : syracuseStep 174641 = 130981) B130981
theorem B174659 : Blo 115785 174659 := bstep (se 1 (by rfl) ⟨130994, by rfl⟩ : syracuseStep 174659 = 261989) B261989
theorem B174689 : Blo 115785 174689 := bstep (se 2 (by rfl) ⟨65508, by rfl⟩ : syracuseStep 174689 = 131017) B131017
theorem B1288817 : Blo 115785 1288817 := bstep (se 2 (by rfl) ⟨483306, by rfl⟩ : syracuseStep 1288817 = 966613) B966613
theorem B404081 : Blo 115785 404081 := bstep (se 2 (by rfl) ⟨151530, by rfl⟩ : syracuseStep 404081 = 303061) B303061
theorem B174707 : Blo 115785 174707 := bstep (se 1 (by rfl) ⟨131030, by rfl⟩ : syracuseStep 174707 = 262061) B262061
theorem B240259 : Blo 115785 240259 := bstep (se 1 (by rfl) ⟨180194, by rfl⟩ : syracuseStep 240259 = 360389) B360389
theorem B436877 : Blo 115785 436877 := bstep (se 3 (by rfl) ⟨81914, by rfl⟩ : syracuseStep 436877 = 163829) B163829
theorem B174737 : Blo 115785 174737 := bstep (se 2 (by rfl) ⟨65526, by rfl⟩ : syracuseStep 174737 = 131053) B131053
theorem B174755 : Blo 115785 174755 := bstep (se 1 (by rfl) ⟨131066, by rfl⟩ : syracuseStep 174755 = 262133) B262133
theorem B174785 : Blo 115785 174785 := bstep (se 2 (by rfl) ⟨65544, by rfl⟩ : syracuseStep 174785 = 131089) B131089
theorem B174803 : Blo 115785 174803 := bstep (se 1 (by rfl) ⟨131102, by rfl⟩ : syracuseStep 174803 = 262205) B262205
theorem B371441 : Blo 115785 371441 := bstep (se 2 (by rfl) ⟨139290, by rfl⟩ : syracuseStep 371441 = 278581) B278581
theorem B174833 : Blo 115785 174833 := bstep (se 2 (by rfl) ⟨65562, by rfl⟩ : syracuseStep 174833 = 131125) B131125
theorem B1354481 : Blo 115785 1354481 := bstep (se 2 (by rfl) ⟨507930, by rfl⟩ : syracuseStep 1354481 = 1015861) B1015861
theorem B174851 : Blo 115785 174851 := bstep (se 1 (by rfl) ⟨131138, by rfl⟩ : syracuseStep 174851 = 262277) B262277
theorem B338701 : Blo 115785 338701 := bstep (se 3 (by rfl) ⟨63506, by rfl⟩ : syracuseStep 338701 = 127013) B127013
theorem B174881 : Blo 115785 174881 := bstep (se 2 (by rfl) ⟨65580, by rfl⟩ : syracuseStep 174881 = 131161) B131161
theorem B371491 : Blo 115785 371491 := bstep (se 1 (by rfl) ⟨278618, by rfl⟩ : syracuseStep 371491 = 557237) B557237
theorem B174899 : Blo 115785 174899 := bstep (se 1 (by rfl) ⟨131174, by rfl⟩ : syracuseStep 174899 = 262349) B262349
theorem B174929 : Blo 115785 174929 := bstep (se 2 (by rfl) ⟨65598, by rfl⟩ : syracuseStep 174929 = 131197) B131197
theorem B174947 : Blo 115785 174947 := bstep (se 1 (by rfl) ⟨131210, by rfl⟩ : syracuseStep 174947 = 262421) B262421
theorem B666467 : Blo 115785 666467 := bstep (se 1 (by rfl) ⟨499850, by rfl⟩ : syracuseStep 666467 = 999701) B999701
theorem B174977 : Blo 115785 174977 := bstep (se 2 (by rfl) ⟨65616, by rfl⟩ : syracuseStep 174977 = 131233) B131233
theorem B174995 : Blo 115785 174995 := bstep (se 1 (by rfl) ⟨131246, by rfl⟩ : syracuseStep 174995 = 262493) B262493
theorem B175025 : Blo 115785 175025 := bstep (se 2 (by rfl) ⟨65634, by rfl⟩ : syracuseStep 175025 = 131269) B131269
theorem B175043 : Blo 115785 175043 := bstep (se 1 (by rfl) ⟨131282, by rfl⟩ : syracuseStep 175043 = 262565) B262565
theorem B175073 : Blo 115785 175073 := bstep (se 2 (by rfl) ⟨65652, by rfl⟩ : syracuseStep 175073 = 131305) B131305
theorem B175091 : Blo 115785 175091 := bstep (se 1 (by rfl) ⟨131318, by rfl⟩ : syracuseStep 175091 = 262637) B262637
theorem B175121 : Blo 115785 175121 := bstep (se 2 (by rfl) ⟨65670, by rfl⟩ : syracuseStep 175121 = 131341) B131341
theorem B175139 : Blo 115785 175139 := bstep (se 1 (by rfl) ⟨131354, by rfl⟩ : syracuseStep 175139 = 262709) B262709
theorem B175169 : Blo 115785 175169 := bstep (se 2 (by rfl) ⟨65688, by rfl⟩ : syracuseStep 175169 = 131377) B131377
theorem B404561 : Blo 115785 404561 := bstep (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) B303421
theorem B175187 : Blo 115785 175187 := bstep (se 1 (by rfl) ⟨131390, by rfl⟩ : syracuseStep 175187 = 262781) B262781
theorem B175217 : Blo 115785 175217 := bstep (se 2 (by rfl) ⟨65706, by rfl⟩ : syracuseStep 175217 = 131413) B131413
theorem B175235 : Blo 115785 175235 := bstep (se 1 (by rfl) ⟨131426, by rfl⟩ : syracuseStep 175235 = 262853) B262853
theorem B273539 : Blo 115785 273539 := bstep (se 1 (by rfl) ⟨205154, by rfl⟩ : syracuseStep 273539 = 410309) B410309
theorem B535693 : Blo 115785 535693 := bstep (se 3 (by rfl) ⟨100442, by rfl⟩ : syracuseStep 535693 = 200885) B200885
theorem B175265 : Blo 115785 175265 := bstep (se 2 (by rfl) ⟨65724, by rfl⟩ : syracuseStep 175265 = 131449) B131449
theorem B175283 : Blo 115785 175283 := bstep (se 1 (by rfl) ⟨131462, by rfl⟩ : syracuseStep 175283 = 262925) B262925
theorem B175313 : Blo 115785 175313 := bstep (se 2 (by rfl) ⟨65742, by rfl⟩ : syracuseStep 175313 = 131485) B131485
theorem B175331 : Blo 115785 175331 := bstep (se 1 (by rfl) ⟨131498, by rfl⟩ : syracuseStep 175331 = 262997) B262997
theorem B175361 : Blo 115785 175361 := bstep (se 2 (by rfl) ⟨65760, by rfl⟩ : syracuseStep 175361 = 131521) B131521
theorem B175379 : Blo 115785 175379 := bstep (se 1 (by rfl) ⟨131534, by rfl⟩ : syracuseStep 175379 = 263069) B263069
theorem B175409 : Blo 115785 175409 := bstep (se 2 (by rfl) ⟨65778, by rfl⟩ : syracuseStep 175409 = 131557) B131557
theorem B175427 : Blo 115785 175427 := bstep (se 1 (by rfl) ⟨131570, by rfl⟩ : syracuseStep 175427 = 263141) B263141
theorem B175457 : Blo 115785 175457 := bstep (se 2 (by rfl) ⟨65796, by rfl⟩ : syracuseStep 175457 = 131593) B131593
theorem B175475 : Blo 115785 175475 := bstep (se 1 (by rfl) ⟨131606, by rfl⟩ : syracuseStep 175475 = 263213) B263213
theorem B175505 : Blo 115785 175505 := bstep (se 2 (by rfl) ⟨65814, by rfl⟩ : syracuseStep 175505 = 131629) B131629
theorem B175523 : Blo 115785 175523 := bstep (se 1 (by rfl) ⟨131642, by rfl⟩ : syracuseStep 175523 = 263285) B263285
theorem B175553 : Blo 115785 175553 := bstep (se 2 (by rfl) ⟨65832, by rfl⟩ : syracuseStep 175553 = 131665) B131665
theorem B175571 : Blo 115785 175571 := bstep (se 1 (by rfl) ⟨131678, by rfl⟩ : syracuseStep 175571 = 263357) B263357
theorem B175601 : Blo 115785 175601 := bstep (se 2 (by rfl) ⟨65850, by rfl⟩ : syracuseStep 175601 = 131701) B131701
theorem B175619 : Blo 115785 175619 := bstep (se 1 (by rfl) ⟨131714, by rfl⟩ : syracuseStep 175619 = 263429) B263429
theorem B175649 : Blo 115785 175649 := bstep (se 2 (by rfl) ⟨65868, by rfl⟩ : syracuseStep 175649 = 131737) B131737
theorem B175667 : Blo 115785 175667 := bstep (se 1 (by rfl) ⟨131750, by rfl⟩ : syracuseStep 175667 = 263501) B263501
theorem B175697 : Blo 115785 175697 := bstep (se 2 (by rfl) ⟨65886, by rfl⟩ : syracuseStep 175697 = 131773) B131773
theorem B175715 : Blo 115785 175715 := bstep (se 1 (by rfl) ⟨131786, by rfl⟩ : syracuseStep 175715 = 263573) B263573
theorem B241265 : Blo 115785 241265 := bstep (se 2 (by rfl) ⟨90474, by rfl⟩ : syracuseStep 241265 = 180949) B180949
theorem B175745 : Blo 115785 175745 := bstep (se 2 (by rfl) ⟨65904, by rfl⟩ : syracuseStep 175745 = 131809) B131809
theorem B175763 : Blo 115785 175763 := bstep (se 1 (by rfl) ⟨131822, by rfl⟩ : syracuseStep 175763 = 263645) B263645
theorem B175793 : Blo 115785 175793 := bstep (se 2 (by rfl) ⟨65922, by rfl⟩ : syracuseStep 175793 = 131845) B131845
theorem B175811 : Blo 115785 175811 := bstep (se 1 (by rfl) ⟨131858, by rfl⟩ : syracuseStep 175811 = 263717) B263717
theorem B175841 : Blo 115785 175841 := bstep (se 2 (by rfl) ⟨65940, by rfl⟩ : syracuseStep 175841 = 131881) B131881
theorem B175859 : Blo 115785 175859 := bstep (se 1 (by rfl) ⟨131894, by rfl⟩ : syracuseStep 175859 = 263789) B263789
theorem B175889 : Blo 115785 175889 := bstep (se 2 (by rfl) ⟨65958, by rfl⟩ : syracuseStep 175889 = 131917) B131917
theorem B175907 : Blo 115785 175907 := bstep (se 1 (by rfl) ⟨131930, by rfl⟩ : syracuseStep 175907 = 263861) B263861
theorem B175937 : Blo 115785 175937 := bstep (se 2 (by rfl) ⟨65976, by rfl⟩ : syracuseStep 175937 = 131953) B131953
theorem B175955 : Blo 115785 175955 := bstep (se 1 (by rfl) ⟨131966, by rfl⟩ : syracuseStep 175955 = 263933) B263933
theorem B175985 : Blo 115785 175985 := bstep (se 2 (by rfl) ⟨65994, by rfl⟩ : syracuseStep 175985 = 131989) B131989
theorem B176003 : Blo 115785 176003 := bstep (se 1 (by rfl) ⟨132002, by rfl⟩ : syracuseStep 176003 = 264005) B264005
theorem B176033 : Blo 115785 176033 := bstep (se 2 (by rfl) ⟨66012, by rfl⟩ : syracuseStep 176033 = 132025) B132025
theorem B503729 : Blo 115785 503729 := bstep (se 2 (by rfl) ⟨188898, by rfl⟩ : syracuseStep 503729 = 377797) B377797
theorem B176051 : Blo 115785 176051 := bstep (se 1 (by rfl) ⟨132038, by rfl⟩ : syracuseStep 176051 = 264077) B264077
theorem B176081 : Blo 115785 176081 := bstep (se 2 (by rfl) ⟨66030, by rfl⟩ : syracuseStep 176081 = 132061) B132061
theorem B176099 : Blo 115785 176099 := bstep (se 1 (by rfl) ⟨132074, by rfl⟩ : syracuseStep 176099 = 264149) B264149
theorem B176129 : Blo 115785 176129 := bstep (se 2 (by rfl) ⟨66048, by rfl⟩ : syracuseStep 176129 = 132097) B132097
theorem B176147 : Blo 115785 176147 := bstep (se 1 (by rfl) ⟨132110, by rfl⟩ : syracuseStep 176147 = 264221) B264221
theorem B176177 : Blo 115785 176177 := bstep (se 2 (by rfl) ⟨66066, by rfl⟩ : syracuseStep 176177 = 132133) B132133
theorem B176195 : Blo 115785 176195 := bstep (se 1 (by rfl) ⟨132146, by rfl⟩ : syracuseStep 176195 = 264293) B264293
theorem B634949 : Blo 115785 634949 := bstep (se 4 (by rfl) ⟨59526, by rfl⟩ : syracuseStep 634949 = 119053) B119053
theorem B176225 : Blo 115785 176225 := bstep (se 2 (by rfl) ⟨66084, by rfl⟩ : syracuseStep 176225 = 132169) B132169
theorem B176243 : Blo 115785 176243 := bstep (se 1 (by rfl) ⟨132182, by rfl⟩ : syracuseStep 176243 = 264365) B264365
theorem B176273 : Blo 115785 176273 := bstep (se 2 (by rfl) ⟨66102, by rfl⟩ : syracuseStep 176273 = 132205) B132205
theorem B176291 : Blo 115785 176291 := bstep (se 1 (by rfl) ⟨132218, by rfl⟩ : syracuseStep 176291 = 264437) B264437
theorem B176321 : Blo 115785 176321 := bstep (se 2 (by rfl) ⟨66120, by rfl⟩ : syracuseStep 176321 = 132241) B132241
theorem B176339 : Blo 115785 176339 := bstep (se 1 (by rfl) ⟨132254, by rfl⟩ : syracuseStep 176339 = 264509) B264509
theorem B176369 : Blo 115785 176369 := bstep (se 2 (by rfl) ⟨66138, by rfl⟩ : syracuseStep 176369 = 132277) B132277
theorem B176387 : Blo 115785 176387 := bstep (se 1 (by rfl) ⟨132290, by rfl⟩ : syracuseStep 176387 = 264581) B264581
theorem B176417 : Blo 115785 176417 := bstep (se 2 (by rfl) ⟨66156, by rfl⟩ : syracuseStep 176417 = 132313) B132313
theorem B176435 : Blo 115785 176435 := bstep (se 1 (by rfl) ⟨132326, by rfl⟩ : syracuseStep 176435 = 264653) B264653
theorem B176465 : Blo 115785 176465 := bstep (se 2 (by rfl) ⟨66174, by rfl⟩ : syracuseStep 176465 = 132349) B132349
theorem B176483 : Blo 115785 176483 := bstep (se 1 (by rfl) ⟨132362, by rfl⟩ : syracuseStep 176483 = 264725) B264725
theorem B176513 : Blo 115785 176513 := bstep (se 2 (by rfl) ⟨66192, by rfl⟩ : syracuseStep 176513 = 132385) B132385
theorem B176531 : Blo 115785 176531 := bstep (se 1 (by rfl) ⟨132398, by rfl⟩ : syracuseStep 176531 = 264797) B264797
theorem B176561 : Blo 115785 176561 := bstep (se 2 (by rfl) ⟨66210, by rfl⟩ : syracuseStep 176561 = 132421) B132421
theorem B176579 : Blo 115785 176579 := bstep (se 1 (by rfl) ⟨132434, by rfl⟩ : syracuseStep 176579 = 264869) B264869
theorem B340433 : Blo 115785 340433 := bstep (se 2 (by rfl) ⟨127662, by rfl⟩ : syracuseStep 340433 = 255325) B255325
theorem B176609 : Blo 115785 176609 := bstep (se 2 (by rfl) ⟨66228, by rfl⟩ : syracuseStep 176609 = 132457) B132457
theorem B176627 : Blo 115785 176627 := bstep (se 1 (by rfl) ⟨132470, by rfl⟩ : syracuseStep 176627 = 264941) B264941
theorem B176657 : Blo 115785 176657 := bstep (se 2 (by rfl) ⟨66246, by rfl⟩ : syracuseStep 176657 = 132493) B132493
theorem B176675 : Blo 115785 176675 := bstep (se 1 (by rfl) ⟨132506, by rfl⟩ : syracuseStep 176675 = 265013) B265013
theorem B176705 : Blo 115785 176705 := bstep (se 2 (by rfl) ⟨66264, by rfl⟩ : syracuseStep 176705 = 132529) B132529
theorem B176723 : Blo 115785 176723 := bstep (se 1 (by rfl) ⟨132542, by rfl⟩ : syracuseStep 176723 = 265085) B265085
theorem B176753 : Blo 115785 176753 := bstep (se 2 (by rfl) ⟨66282, by rfl⟩ : syracuseStep 176753 = 132565) B132565
theorem B176771 : Blo 115785 176771 := bstep (se 1 (by rfl) ⟨132578, by rfl⟩ : syracuseStep 176771 = 265157) B265157
theorem B340625 : Blo 115785 340625 := bstep (se 2 (by rfl) ⟨127734, by rfl⟩ : syracuseStep 340625 = 255469) B255469
theorem B176801 : Blo 115785 176801 := bstep (se 2 (by rfl) ⟨66300, by rfl⟩ : syracuseStep 176801 = 132601) B132601
theorem B602801 : Blo 115785 602801 := bstep (se 2 (by rfl) ⟨226050, by rfl⟩ : syracuseStep 602801 = 452101) B452101
theorem B176819 : Blo 115785 176819 := bstep (se 1 (by rfl) ⟨132614, by rfl⟩ : syracuseStep 176819 = 265229) B265229
theorem B668357 : Blo 115785 668357 := bstep (se 4 (by rfl) ⟨62658, by rfl⟩ : syracuseStep 668357 = 125317) B125317
theorem B176849 : Blo 115785 176849 := bstep (se 2 (by rfl) ⟨66318, by rfl⟩ : syracuseStep 176849 = 132637) B132637
theorem B176867 : Blo 115785 176867 := bstep (se 1 (by rfl) ⟨132650, by rfl⟩ : syracuseStep 176867 = 265301) B265301
theorem B635633 : Blo 115785 635633 := bstep (se 2 (by rfl) ⟨238362, by rfl⟩ : syracuseStep 635633 = 476725) B476725
theorem B176897 : Blo 115785 176897 := bstep (se 2 (by rfl) ⟨66336, by rfl⟩ : syracuseStep 176897 = 132673) B132673
theorem B373517 : Blo 115785 373517 := bstep (se 3 (by rfl) ⟨70034, by rfl⟩ : syracuseStep 373517 = 140069) B140069
theorem B176915 : Blo 115785 176915 := bstep (se 1 (by rfl) ⟨132686, by rfl⟩ : syracuseStep 176915 = 265373) B265373
theorem B176945 : Blo 115785 176945 := bstep (se 2 (by rfl) ⟨66354, by rfl⟩ : syracuseStep 176945 = 132709) B132709
theorem B176963 : Blo 115785 176963 := bstep (se 1 (by rfl) ⟨132722, by rfl⟩ : syracuseStep 176963 = 265445) B265445
theorem B176993 : Blo 115785 176993 := bstep (se 2 (by rfl) ⟨66372, by rfl⟩ : syracuseStep 176993 = 132745) B132745
theorem B177011 : Blo 115785 177011 := bstep (se 1 (by rfl) ⟨132758, by rfl⟩ : syracuseStep 177011 = 265517) B265517
theorem B177041 : Blo 115785 177041 := bstep (se 2 (by rfl) ⟨66390, by rfl⟩ : syracuseStep 177041 = 132781) B132781
theorem B177059 : Blo 115785 177059 := bstep (se 1 (by rfl) ⟨132794, by rfl⟩ : syracuseStep 177059 = 265589) B265589
theorem B177089 : Blo 115785 177089 := bstep (se 2 (by rfl) ⟨66408, by rfl⟩ : syracuseStep 177089 = 132817) B132817
theorem B209873 : Blo 115785 209873 := bstep (se 2 (by rfl) ⟨78702, by rfl⟩ : syracuseStep 209873 = 157405) B157405
theorem B177107 : Blo 115785 177107 := bstep (se 1 (by rfl) ⟨132830, by rfl⟩ : syracuseStep 177107 = 265661) B265661
theorem B177137 : Blo 115785 177137 := bstep (se 2 (by rfl) ⟨66426, by rfl⟩ : syracuseStep 177137 = 132853) B132853
theorem B177155 : Blo 115785 177155 := bstep (se 1 (by rfl) ⟨132866, by rfl⟩ : syracuseStep 177155 = 265733) B265733
theorem B177185 : Blo 115785 177185 := bstep (se 2 (by rfl) ⟨66444, by rfl⟩ : syracuseStep 177185 = 132889) B132889
theorem B177203 : Blo 115785 177203 := bstep (se 1 (by rfl) ⟨132902, by rfl⟩ : syracuseStep 177203 = 265805) B265805
theorem B144451 : Blo 115785 144451 := bstep (se 1 (by rfl) ⟨108338, by rfl⟩ : syracuseStep 144451 = 216677) B216677
theorem B177233 : Blo 115785 177233 := bstep (se 2 (by rfl) ⟨66462, by rfl⟩ : syracuseStep 177233 = 132925) B132925
theorem B177251 : Blo 115785 177251 := bstep (se 1 (by rfl) ⟨132938, by rfl⟩ : syracuseStep 177251 = 265877) B265877
theorem B177281 : Blo 115785 177281 := bstep (se 2 (by rfl) ⟨66480, by rfl⟩ : syracuseStep 177281 = 132961) B132961
theorem B177299 : Blo 115785 177299 := bstep (se 1 (by rfl) ⟨132974, by rfl⟩ : syracuseStep 177299 = 265949) B265949
theorem B177329 : Blo 115785 177329 := bstep (se 2 (by rfl) ⟨66498, by rfl⟩ : syracuseStep 177329 = 132997) B132997
theorem B177347 : Blo 115785 177347 := bstep (se 1 (by rfl) ⟨133010, by rfl⟩ : syracuseStep 177347 = 266021) B266021
theorem B177377 : Blo 115785 177377 := bstep (se 2 (by rfl) ⟨66516, by rfl⟩ : syracuseStep 177377 = 133033) B133033
theorem B177395 : Blo 115785 177395 := bstep (se 1 (by rfl) ⟨133046, by rfl⟩ : syracuseStep 177395 = 266093) B266093
theorem B177425 : Blo 115785 177425 := bstep (se 2 (by rfl) ⟨66534, by rfl⟩ : syracuseStep 177425 = 133069) B133069
theorem B177443 : Blo 115785 177443 := bstep (se 1 (by rfl) ⟨133082, by rfl⟩ : syracuseStep 177443 = 266165) B266165
theorem B177473 : Blo 115785 177473 := bstep (se 2 (by rfl) ⟨66552, by rfl⟩ : syracuseStep 177473 = 133105) B133105
theorem B177491 : Blo 115785 177491 := bstep (se 1 (by rfl) ⟨133118, by rfl⟩ : syracuseStep 177491 = 266237) B266237
theorem B177521 : Blo 115785 177521 := bstep (se 2 (by rfl) ⟨66570, by rfl⟩ : syracuseStep 177521 = 133141) B133141
theorem B177539 : Blo 115785 177539 := bstep (se 1 (by rfl) ⟨133154, by rfl⟩ : syracuseStep 177539 = 266309) B266309
theorem B177569 : Blo 115785 177569 := bstep (se 2 (by rfl) ⟨66588, by rfl⟩ : syracuseStep 177569 = 133177) B133177
theorem B177587 : Blo 115785 177587 := bstep (se 1 (by rfl) ⟨133190, by rfl⟩ : syracuseStep 177587 = 266381) B266381
theorem B177617 : Blo 115785 177617 := bstep (se 2 (by rfl) ⟨66606, by rfl⟩ : syracuseStep 177617 = 133213) B133213
theorem B177635 : Blo 115785 177635 := bstep (se 1 (by rfl) ⟨133226, by rfl⟩ : syracuseStep 177635 = 266453) B266453
theorem B341489 : Blo 115785 341489 := bstep (se 2 (by rfl) ⟨128058, by rfl⟩ : syracuseStep 341489 = 256117) B256117
theorem B177665 : Blo 115785 177665 := bstep (se 2 (by rfl) ⟨66624, by rfl⟩ : syracuseStep 177665 = 133249) B133249
theorem B177683 : Blo 115785 177683 := bstep (se 1 (by rfl) ⟨133262, by rfl⟩ : syracuseStep 177683 = 266525) B266525
theorem B177713 : Blo 115785 177713 := bstep (se 2 (by rfl) ⟨66642, by rfl⟩ : syracuseStep 177713 = 133285) B133285
theorem B177731 : Blo 115785 177731 := bstep (se 1 (by rfl) ⟨133298, by rfl⟩ : syracuseStep 177731 = 266597) B266597
theorem B177761 : Blo 115785 177761 := bstep (se 2 (by rfl) ⟨66660, by rfl⟩ : syracuseStep 177761 = 133321) B133321
theorem B177779 : Blo 115785 177779 := bstep (se 1 (by rfl) ⟨133334, by rfl⟩ : syracuseStep 177779 = 266669) B266669
theorem B177809 : Blo 115785 177809 := bstep (se 2 (by rfl) ⟨66678, by rfl⟩ : syracuseStep 177809 = 133357) B133357
theorem B177827 : Blo 115785 177827 := bstep (se 1 (by rfl) ⟨133370, by rfl⟩ : syracuseStep 177827 = 266741) B266741
theorem B177857 : Blo 115785 177857 := bstep (se 2 (by rfl) ⟨66696, by rfl⟩ : syracuseStep 177857 = 133393) B133393
theorem B177875 : Blo 115785 177875 := bstep (se 1 (by rfl) ⟨133406, by rfl⟩ : syracuseStep 177875 = 266813) B266813
theorem B177905 : Blo 115785 177905 := bstep (se 2 (by rfl) ⟨66714, by rfl⟩ : syracuseStep 177905 = 133429) B133429
theorem B177923 : Blo 115785 177923 := bstep (se 1 (by rfl) ⟨133442, by rfl⟩ : syracuseStep 177923 = 266885) B266885
theorem B177953 : Blo 115785 177953 := bstep (se 2 (by rfl) ⟨66732, by rfl⟩ : syracuseStep 177953 = 133465) B133465
theorem B177971 : Blo 115785 177971 := bstep (se 1 (by rfl) ⟨133478, by rfl⟩ : syracuseStep 177971 = 266957) B266957
theorem B178001 : Blo 115785 178001 := bstep (se 2 (by rfl) ⟨66750, by rfl⟩ : syracuseStep 178001 = 133501) B133501
theorem B178019 : Blo 115785 178019 := bstep (se 1 (by rfl) ⟨133514, by rfl⟩ : syracuseStep 178019 = 267029) B267029
theorem B178049 : Blo 115785 178049 := bstep (se 2 (by rfl) ⟨66768, by rfl⟩ : syracuseStep 178049 = 133537) B133537
theorem B1259405 : Blo 115785 1259405 := bstep (se 3 (by rfl) ⟨236138, by rfl⟩ : syracuseStep 1259405 = 472277) B472277
theorem B178067 : Blo 115785 178067 := bstep (se 1 (by rfl) ⟨133550, by rfl⟩ : syracuseStep 178067 = 267101) B267101
theorem B178097 : Blo 115785 178097 := bstep (se 2 (by rfl) ⟨66786, by rfl⟩ : syracuseStep 178097 = 133573) B133573
theorem B178115 : Blo 115785 178115 := bstep (se 1 (by rfl) ⟨133586, by rfl⟩ : syracuseStep 178115 = 267173) B267173
theorem B178145 : Blo 115785 178145 := bstep (se 2 (by rfl) ⟨66804, by rfl⟩ : syracuseStep 178145 = 133609) B133609
theorem B178163 : Blo 115785 178163 := bstep (se 1 (by rfl) ⟨133622, by rfl⟩ : syracuseStep 178163 = 267245) B267245
theorem B374797 : Blo 115785 374797 := bstep (se 3 (by rfl) ⟨70274, by rfl⟩ : syracuseStep 374797 = 140549) B140549
theorem B178193 : Blo 115785 178193 := bstep (se 2 (by rfl) ⟨66822, by rfl⟩ : syracuseStep 178193 = 133645) B133645
theorem B178211 : Blo 115785 178211 := bstep (se 1 (by rfl) ⟨133658, by rfl⟩ : syracuseStep 178211 = 267317) B267317
theorem B178241 : Blo 115785 178241 := bstep (se 2 (by rfl) ⟨66840, by rfl⟩ : syracuseStep 178241 = 133681) B133681
theorem B178259 : Blo 115785 178259 := bstep (se 1 (by rfl) ⟨133694, by rfl⟩ : syracuseStep 178259 = 267389) B267389
theorem B604259 : Blo 115785 604259 := bstep (se 1 (by rfl) ⟨453194, by rfl⟩ : syracuseStep 604259 = 906389) B906389
theorem B178289 : Blo 115785 178289 := bstep (se 2 (by rfl) ⟨66858, by rfl⟩ : syracuseStep 178289 = 133717) B133717
theorem B178307 : Blo 115785 178307 := bstep (se 1 (by rfl) ⟨133730, by rfl⟩ : syracuseStep 178307 = 267461) B267461
theorem B178337 : Blo 115785 178337 := bstep (se 2 (by rfl) ⟨66876, by rfl⟩ : syracuseStep 178337 = 133753) B133753
theorem B178355 : Blo 115785 178355 := bstep (se 1 (by rfl) ⟨133766, by rfl⟩ : syracuseStep 178355 = 267533) B267533
theorem B178385 : Blo 115785 178385 := bstep (se 2 (by rfl) ⟨66894, by rfl⟩ : syracuseStep 178385 = 133789) B133789
theorem B178403 : Blo 115785 178403 := bstep (se 1 (by rfl) ⟨133802, by rfl⟩ : syracuseStep 178403 = 267605) B267605
theorem B1620209 : Blo 115785 1620209 := bstep (se 2 (by rfl) ⟨607578, by rfl⟩ : syracuseStep 1620209 = 1215157) B1215157
theorem B178433 : Blo 115785 178433 := bstep (se 2 (by rfl) ⟨66912, by rfl⟩ : syracuseStep 178433 = 133825) B133825
theorem B178451 : Blo 115785 178451 := bstep (se 1 (by rfl) ⟨133838, by rfl⟩ : syracuseStep 178451 = 267677) B267677
theorem B178481 : Blo 115785 178481 := bstep (se 2 (by rfl) ⟨66930, by rfl⟩ : syracuseStep 178481 = 133861) B133861
theorem B178499 : Blo 115785 178499 := bstep (se 1 (by rfl) ⟨133874, by rfl⟩ : syracuseStep 178499 = 267749) B267749
theorem B506189 : Blo 115785 506189 := bstep (se 3 (by rfl) ⟨94910, by rfl⟩ : syracuseStep 506189 = 189821) B189821
theorem B178529 : Blo 115785 178529 := bstep (se 2 (by rfl) ⟨66948, by rfl⟩ : syracuseStep 178529 = 133897) B133897
theorem B178547 : Blo 115785 178547 := bstep (se 1 (by rfl) ⟨133910, by rfl⟩ : syracuseStep 178547 = 267821) B267821
theorem B178577 : Blo 115785 178577 := bstep (se 2 (by rfl) ⟨66966, by rfl⟩ : syracuseStep 178577 = 133933) B133933
theorem B178595 : Blo 115785 178595 := bstep (se 1 (by rfl) ⟨133946, by rfl⟩ : syracuseStep 178595 = 267893) B267893
theorem B178625 : Blo 115785 178625 := bstep (se 2 (by rfl) ⟨66984, by rfl⟩ : syracuseStep 178625 = 133969) B133969
theorem B178643 : Blo 115785 178643 := bstep (se 1 (by rfl) ⟨133982, by rfl⟩ : syracuseStep 178643 = 267965) B267965
theorem B178673 : Blo 115785 178673 := bstep (se 2 (by rfl) ⟨67002, by rfl⟩ : syracuseStep 178673 = 134005) B134005
theorem B375299 : Blo 115785 375299 := bstep (se 1 (by rfl) ⟨281474, by rfl⟩ : syracuseStep 375299 = 562949) B562949
theorem B178691 : Blo 115785 178691 := bstep (se 1 (by rfl) ⟨134018, by rfl⟩ : syracuseStep 178691 = 268037) B268037
theorem B178721 : Blo 115785 178721 := bstep (se 2 (by rfl) ⟨67020, by rfl⟩ : syracuseStep 178721 = 134041) B134041
theorem B178739 : Blo 115785 178739 := bstep (se 1 (by rfl) ⟨134054, by rfl⟩ : syracuseStep 178739 = 268109) B268109
theorem B440909 : Blo 115785 440909 := bstep (se 3 (by rfl) ⟨82670, by rfl⟩ : syracuseStep 440909 = 165341) B165341
theorem B178769 : Blo 115785 178769 := bstep (se 2 (by rfl) ⟨67038, by rfl⟩ : syracuseStep 178769 = 134077) B134077
theorem B178787 : Blo 115785 178787 := bstep (se 1 (by rfl) ⟨134090, by rfl⟩ : syracuseStep 178787 = 268181) B268181
theorem B178817 : Blo 115785 178817 := bstep (se 2 (by rfl) ⟨67056, by rfl⟩ : syracuseStep 178817 = 134113) B134113
theorem B178835 : Blo 115785 178835 := bstep (se 1 (by rfl) ⟨134126, by rfl⟩ : syracuseStep 178835 = 268253) B268253
theorem B178865 : Blo 115785 178865 := bstep (se 2 (by rfl) ⟨67074, by rfl⟩ : syracuseStep 178865 = 134149) B134149
theorem B178883 : Blo 115785 178883 := bstep (se 1 (by rfl) ⟨134162, by rfl⟩ : syracuseStep 178883 = 268325) B268325
theorem B178913 : Blo 115785 178913 := bstep (se 2 (by rfl) ⟨67092, by rfl⟩ : syracuseStep 178913 = 134185) B134185
theorem B178931 : Blo 115785 178931 := bstep (se 1 (by rfl) ⟨134198, by rfl⟩ : syracuseStep 178931 = 268397) B268397
theorem B178961 : Blo 115785 178961 := bstep (se 2 (by rfl) ⟨67110, by rfl⟩ : syracuseStep 178961 = 134221) B134221
theorem B178979 : Blo 115785 178979 := bstep (se 1 (by rfl) ⟨134234, by rfl⟩ : syracuseStep 178979 = 268469) B268469
theorem B179009 : Blo 115785 179009 := bstep (se 2 (by rfl) ⟨67128, by rfl⟩ : syracuseStep 179009 = 134257) B134257
theorem B179027 : Blo 115785 179027 := bstep (se 1 (by rfl) ⟨134270, by rfl⟩ : syracuseStep 179027 = 268541) B268541
theorem B1063793 : Blo 115785 1063793 := bstep (se 2 (by rfl) ⟨398922, by rfl⟩ : syracuseStep 1063793 = 797845) B797845
theorem B179057 : Blo 115785 179057 := bstep (se 2 (by rfl) ⟨67146, by rfl⟩ : syracuseStep 179057 = 134293) B134293
theorem B179075 : Blo 115785 179075 := bstep (se 1 (by rfl) ⟨134306, by rfl⟩ : syracuseStep 179075 = 268613) B268613
theorem B605069 : Blo 115785 605069 := bstep (se 3 (by rfl) ⟨113450, by rfl⟩ : syracuseStep 605069 = 226901) B226901
theorem B179105 : Blo 115785 179105 := bstep (se 2 (by rfl) ⟨67164, by rfl⟩ : syracuseStep 179105 = 134329) B134329
theorem B179123 : Blo 115785 179123 := bstep (se 1 (by rfl) ⟨134342, by rfl⟩ : syracuseStep 179123 = 268685) B268685
theorem B179153 : Blo 115785 179153 := bstep (se 2 (by rfl) ⟨67182, by rfl⟩ : syracuseStep 179153 = 134365) B134365
theorem B179171 : Blo 115785 179171 := bstep (se 1 (by rfl) ⟨134378, by rfl⟩ : syracuseStep 179171 = 268757) B268757
theorem B179201 : Blo 115785 179201 := bstep (se 2 (by rfl) ⟨67200, by rfl⟩ : syracuseStep 179201 = 134401) B134401
theorem B179219 : Blo 115785 179219 := bstep (se 1 (by rfl) ⟨134414, by rfl⟩ : syracuseStep 179219 = 268829) B268829
theorem B179249 : Blo 115785 179249 := bstep (se 2 (by rfl) ⟨67218, by rfl⟩ : syracuseStep 179249 = 134437) B134437
theorem B179267 : Blo 115785 179267 := bstep (se 1 (by rfl) ⟨134450, by rfl⟩ : syracuseStep 179267 = 268901) B268901
theorem B179297 : Blo 115785 179297 := bstep (se 2 (by rfl) ⟨67236, by rfl⟩ : syracuseStep 179297 = 134473) B134473
theorem B1129585 : Blo 115785 1129585 := bstep (se 2 (by rfl) ⟨423594, by rfl⟩ : syracuseStep 1129585 = 847189) B847189
theorem B179315 : Blo 115785 179315 := bstep (se 1 (by rfl) ⟨134486, by rfl⟩ : syracuseStep 179315 = 268973) B268973
theorem B179345 : Blo 115785 179345 := bstep (se 2 (by rfl) ⟨67254, by rfl⟩ : syracuseStep 179345 = 134509) B134509
theorem B179363 : Blo 115785 179363 := bstep (se 1 (by rfl) ⟨134522, by rfl⟩ : syracuseStep 179363 = 269045) B269045
theorem B179393 : Blo 115785 179393 := bstep (se 2 (by rfl) ⟨67272, by rfl⟩ : syracuseStep 179393 = 134545) B134545
theorem B179411 : Blo 115785 179411 := bstep (se 1 (by rfl) ⟨134558, by rfl⟩ : syracuseStep 179411 = 269117) B269117
theorem B179441 : Blo 115785 179441 := bstep (se 2 (by rfl) ⟨67290, by rfl⟩ : syracuseStep 179441 = 134581) B134581
theorem B179459 : Blo 115785 179459 := bstep (se 1 (by rfl) ⟨134594, by rfl⟩ : syracuseStep 179459 = 269189) B269189
theorem B179489 : Blo 115785 179489 := bstep (se 2 (by rfl) ⟨67308, by rfl⟩ : syracuseStep 179489 = 134617) B134617
theorem B179507 : Blo 115785 179507 := bstep (se 1 (by rfl) ⟨134630, by rfl⟩ : syracuseStep 179507 = 269261) B269261
theorem B179537 : Blo 115785 179537 := bstep (se 2 (by rfl) ⟨67326, by rfl⟩ : syracuseStep 179537 = 134653) B134653
theorem B179555 : Blo 115785 179555 := bstep (se 1 (by rfl) ⟨134666, by rfl⟩ : syracuseStep 179555 = 269333) B269333
theorem B441713 : Blo 115785 441713 := bstep (se 2 (by rfl) ⟨165642, by rfl⟩ : syracuseStep 441713 = 331285) B331285
theorem B179585 : Blo 115785 179585 := bstep (se 2 (by rfl) ⟨67344, by rfl⟩ : syracuseStep 179585 = 134689) B134689
theorem B179603 : Blo 115785 179603 := bstep (se 1 (by rfl) ⟨134702, by rfl⟩ : syracuseStep 179603 = 269405) B269405
theorem B408995 : Blo 115785 408995 := bstep (se 1 (by rfl) ⟨306746, by rfl⟩ : syracuseStep 408995 = 613493) B613493
theorem B179633 : Blo 115785 179633 := bstep (se 2 (by rfl) ⟨67362, by rfl⟩ : syracuseStep 179633 = 134725) B134725
theorem B179651 : Blo 115785 179651 := bstep (se 1 (by rfl) ⟨134738, by rfl⟩ : syracuseStep 179651 = 269477) B269477
theorem B507505 : Blo 115785 507505 := bstep (se 2 (by rfl) ⟨190314, by rfl⟩ : syracuseStep 507505 = 380629) B380629
theorem B147091 : Blo 115785 147091 := bstep (se 1 (by rfl) ⟨110318, by rfl⟩ : syracuseStep 147091 = 220637) B220637
theorem B573155 : Blo 115785 573155 := bstep (se 1 (by rfl) ⟨429866, by rfl⟩ : syracuseStep 573155 = 859733) B859733
theorem B147187 : Blo 115785 147187 := bstep (se 1 (by rfl) ⟨110390, by rfl⟩ : syracuseStep 147187 = 220781) B220781
theorem B376589 : Blo 115785 376589 := bstep (se 3 (by rfl) ⟨70610, by rfl⟩ : syracuseStep 376589 = 141221) B141221
theorem B376643 : Blo 115785 376643 := bstep (se 1 (by rfl) ⟨282482, by rfl⟩ : syracuseStep 376643 = 564965) B564965
theorem B180067 : Blo 115785 180067 := bstep (se 1 (by rfl) ⟨135050, by rfl⟩ : syracuseStep 180067 = 270101) B270101
theorem B2015117 : Blo 115785 2015117 := bstep (se 3 (by rfl) ⟨377834, by rfl⟩ : syracuseStep 2015117 = 755669) B755669
theorem B442381 : Blo 115785 442381 := bstep (se 3 (by rfl) ⟨82946, by rfl⟩ : syracuseStep 442381 = 165893) B165893
theorem B3031181 : Blo 115785 3031181 := bstep (se 3 (by rfl) ⟨568346, by rfl⟩ : syracuseStep 3031181 = 1136693) B1136693
theorem B147683 : Blo 115785 147683 := bstep (se 1 (by rfl) ⟨110762, by rfl⟩ : syracuseStep 147683 = 221525) B221525
theorem B1589557 : Blo 115785 1589557 := bstep (se 5 (by rfl) ⟨74510, by rfl⟩ : syracuseStep 1589557 = 149021) B149021
theorem B279139 : Blo 115785 279139 := bstep (se 1 (by rfl) ⟨209354, by rfl⟩ : syracuseStep 279139 = 418709) B418709
theorem B377617 : Blo 115785 377617 := bstep (se 2 (by rfl) ⟨141606, by rfl⟩ : syracuseStep 377617 = 283213) B283213
theorem B443171 : Blo 115785 443171 := bstep (se 1 (by rfl) ⟨332378, by rfl⟩ : syracuseStep 443171 = 664757) B664757
theorem B148387 : Blo 115785 148387 := bstep (se 1 (by rfl) ⟨111290, by rfl⟩ : syracuseStep 148387 = 222581) B222581
theorem B1360867 : Blo 115785 1360867 := bstep (se 1 (by rfl) ⟨1020650, by rfl⟩ : syracuseStep 1360867 = 2041301) B2041301
theorem B148483 : Blo 115785 148483 := bstep (se 1 (by rfl) ⟨111362, by rfl⟩ : syracuseStep 148483 = 222725) B222725
theorem B377873 : Blo 115785 377873 := bstep (se 2 (by rfl) ⟨141702, by rfl⟩ : syracuseStep 377873 = 283405) B283405
theorem B115795 : Blo 115785 115795 := bstep (se 1 (by rfl) ⟨86846, by rfl⟩ : syracuseStep 115795 = 173693) B173693
theorem B115811 : Blo 115785 115811 := bstep (se 1 (by rfl) ⟨86858, by rfl⟩ : syracuseStep 115811 = 173717) B173717
theorem B115827 : Blo 115785 115827 := bstep (se 1 (by rfl) ⟨86870, by rfl⟩ : syracuseStep 115827 = 173741) B173741
theorem B115843 : Blo 115785 115843 := bstep (se 1 (by rfl) ⟨86882, by rfl⟩ : syracuseStep 115843 = 173765) B173765
theorem B115859 : Blo 115785 115859 := bstep (se 1 (by rfl) ⟨86894, by rfl⟩ : syracuseStep 115859 = 173789) B173789
theorem B115875 : Blo 115785 115875 := bstep (se 1 (by rfl) ⟨86906, by rfl⟩ : syracuseStep 115875 = 173813) B173813
theorem B115891 : Blo 115785 115891 := bstep (se 1 (by rfl) ⟨86918, by rfl⟩ : syracuseStep 115891 = 173837) B173837
theorem B115907 : Blo 115785 115907 := bstep (se 1 (by rfl) ⟨86930, by rfl⟩ : syracuseStep 115907 = 173861) B173861
theorem B115923 : Blo 115785 115923 := bstep (se 1 (by rfl) ⟨86942, by rfl⟩ : syracuseStep 115923 = 173885) B173885
theorem B115939 : Blo 115785 115939 := bstep (se 1 (by rfl) ⟨86954, by rfl⟩ : syracuseStep 115939 = 173909) B173909
theorem B115955 : Blo 115785 115955 := bstep (se 1 (by rfl) ⟨86966, by rfl⟩ : syracuseStep 115955 = 173933) B173933
theorem B115971 : Blo 115785 115971 := bstep (se 1 (by rfl) ⟨86978, by rfl⟩ : syracuseStep 115971 = 173957) B173957
theorem B279811 : Blo 115785 279811 := bstep (se 1 (by rfl) ⟨209858, by rfl⟩ : syracuseStep 279811 = 419717) B419717
theorem B115987 : Blo 115785 115987 := bstep (se 1 (by rfl) ⟨86990, by rfl⟩ : syracuseStep 115987 = 173981) B173981
theorem B116003 : Blo 115785 116003 := bstep (se 1 (by rfl) ⟨87002, by rfl⟩ : syracuseStep 116003 = 174005) B174005
theorem B116019 : Blo 115785 116019 := bstep (se 1 (by rfl) ⟨87014, by rfl⟩ : syracuseStep 116019 = 174029) B174029
theorem B116035 : Blo 115785 116035 := bstep (se 1 (by rfl) ⟨87026, by rfl⟩ : syracuseStep 116035 = 174053) B174053
theorem B116051 : Blo 115785 116051 := bstep (se 1 (by rfl) ⟨87038, by rfl⟩ : syracuseStep 116051 = 174077) B174077
theorem B116067 : Blo 115785 116067 := bstep (se 1 (by rfl) ⟨87050, by rfl⟩ : syracuseStep 116067 = 174101) B174101
theorem B116083 : Blo 115785 116083 := bstep (se 1 (by rfl) ⟨87062, by rfl⟩ : syracuseStep 116083 = 174125) B174125
theorem B116099 : Blo 115785 116099 := bstep (se 1 (by rfl) ⟨87074, by rfl⟩ : syracuseStep 116099 = 174149) B174149
theorem B771461 : Blo 115785 771461 := bstep (se 4 (by rfl) ⟨72324, by rfl⟩ : syracuseStep 771461 = 144649) B144649
theorem B116115 : Blo 115785 116115 := bstep (se 1 (by rfl) ⟨87086, by rfl⟩ : syracuseStep 116115 = 174173) B174173
theorem B116131 : Blo 115785 116131 := bstep (se 1 (by rfl) ⟨87098, by rfl⟩ : syracuseStep 116131 = 174197) B174197
theorem B443825 : Blo 115785 443825 := bstep (se 2 (by rfl) ⟨166434, by rfl⟩ : syracuseStep 443825 = 332869) B332869
theorem B116147 : Blo 115785 116147 := bstep (se 1 (by rfl) ⟨87110, by rfl⟩ : syracuseStep 116147 = 174221) B174221
theorem B116163 : Blo 115785 116163 := bstep (se 1 (by rfl) ⟨87122, by rfl⟩ : syracuseStep 116163 = 174245) B174245
theorem B2278853 : Blo 115785 2278853 := bstep (se 4 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 2278853 = 427285) B427285
theorem B116179 : Blo 115785 116179 := bstep (se 1 (by rfl) ⟨87134, by rfl⟩ : syracuseStep 116179 = 174269) B174269
theorem B116195 : Blo 115785 116195 := bstep (se 1 (by rfl) ⟨87146, by rfl⟩ : syracuseStep 116195 = 174293) B174293
theorem B116211 : Blo 115785 116211 := bstep (se 1 (by rfl) ⟨87158, by rfl⟩ : syracuseStep 116211 = 174317) B174317
theorem B148979 : Blo 115785 148979 := bstep (se 1 (by rfl) ⟨111734, by rfl⟩ : syracuseStep 148979 = 223469) B223469
theorem B116227 : Blo 115785 116227 := bstep (se 1 (by rfl) ⟨87170, by rfl⟩ : syracuseStep 116227 = 174341) B174341
theorem B116243 : Blo 115785 116243 := bstep (se 1 (by rfl) ⟨87182, by rfl⟩ : syracuseStep 116243 = 174365) B174365
theorem B116259 : Blo 115785 116259 := bstep (se 1 (by rfl) ⟨87194, by rfl⟩ : syracuseStep 116259 = 174389) B174389
theorem B116275 : Blo 115785 116275 := bstep (se 1 (by rfl) ⟨87206, by rfl⟩ : syracuseStep 116275 = 174413) B174413
theorem B116291 : Blo 115785 116291 := bstep (se 1 (by rfl) ⟨87218, by rfl⟩ : syracuseStep 116291 = 174437) B174437
theorem B116307 : Blo 115785 116307 := bstep (se 1 (by rfl) ⟨87230, by rfl⟩ : syracuseStep 116307 = 174461) B174461
theorem B116323 : Blo 115785 116323 := bstep (se 1 (by rfl) ⟨87242, by rfl⟩ : syracuseStep 116323 = 174485) B174485
theorem B116339 : Blo 115785 116339 := bstep (se 1 (by rfl) ⟨87254, by rfl⟩ : syracuseStep 116339 = 174509) B174509
theorem B181889 : Blo 115785 181889 := bstep (se 2 (by rfl) ⟨68208, by rfl⟩ : syracuseStep 181889 = 136417) B136417
theorem B116355 : Blo 115785 116355 := bstep (se 1 (by rfl) ⟨87266, by rfl⟩ : syracuseStep 116355 = 174533) B174533
theorem B116371 : Blo 115785 116371 := bstep (se 1 (by rfl) ⟨87278, by rfl⟩ : syracuseStep 116371 = 174557) B174557
theorem B116387 : Blo 115785 116387 := bstep (se 1 (by rfl) ⟨87290, by rfl⟩ : syracuseStep 116387 = 174581) B174581
theorem B116403 : Blo 115785 116403 := bstep (se 1 (by rfl) ⟨87302, by rfl⟩ : syracuseStep 116403 = 174605) B174605
theorem B116419 : Blo 115785 116419 := bstep (se 1 (by rfl) ⟨87314, by rfl⟩ : syracuseStep 116419 = 174629) B174629
theorem B280273 : Blo 115785 280273 := bstep (se 2 (by rfl) ⟨105102, by rfl⟩ : syracuseStep 280273 = 210205) B210205
theorem B116435 : Blo 115785 116435 := bstep (se 1 (by rfl) ⟨87326, by rfl⟩ : syracuseStep 116435 = 174653) B174653
theorem B116451 : Blo 115785 116451 := bstep (se 1 (by rfl) ⟨87338, by rfl⟩ : syracuseStep 116451 = 174677) B174677
theorem B116467 : Blo 115785 116467 := bstep (se 1 (by rfl) ⟨87350, by rfl⟩ : syracuseStep 116467 = 174701) B174701
theorem B116483 : Blo 115785 116483 := bstep (se 1 (by rfl) ⟨87362, by rfl⟩ : syracuseStep 116483 = 174725) B174725
theorem B116499 : Blo 115785 116499 := bstep (se 1 (by rfl) ⟨87374, by rfl⟩ : syracuseStep 116499 = 174749) B174749
theorem B3786517 : Blo 115785 3786517 := bstep (se 6 (by rfl) ⟨88746, by rfl⟩ : syracuseStep 3786517 = 177493) B177493
theorem B116515 : Blo 115785 116515 := bstep (se 1 (by rfl) ⟨87386, by rfl⟩ : syracuseStep 116515 = 174773) B174773
theorem B116531 : Blo 115785 116531 := bstep (se 1 (by rfl) ⟨87398, by rfl⟩ : syracuseStep 116531 = 174797) B174797
theorem B116547 : Blo 115785 116547 := bstep (se 1 (by rfl) ⟨87410, by rfl⟩ : syracuseStep 116547 = 174821) B174821
theorem B116563 : Blo 115785 116563 := bstep (se 1 (by rfl) ⟨87422, by rfl⟩ : syracuseStep 116563 = 174845) B174845
theorem B116579 : Blo 115785 116579 := bstep (se 1 (by rfl) ⟨87434, by rfl⟩ : syracuseStep 116579 = 174869) B174869
theorem B116595 : Blo 115785 116595 := bstep (se 1 (by rfl) ⟨87446, by rfl⟩ : syracuseStep 116595 = 174893) B174893
theorem B116611 : Blo 115785 116611 := bstep (se 1 (by rfl) ⟨87458, by rfl⟩ : syracuseStep 116611 = 174917) B174917
theorem B116627 : Blo 115785 116627 := bstep (se 1 (by rfl) ⟨87470, by rfl⟩ : syracuseStep 116627 = 174941) B174941
theorem B116643 : Blo 115785 116643 := bstep (se 1 (by rfl) ⟨87482, by rfl⟩ : syracuseStep 116643 = 174965) B174965
theorem B116659 : Blo 115785 116659 := bstep (se 1 (by rfl) ⟨87494, by rfl⟩ : syracuseStep 116659 = 174989) B174989
theorem B116675 : Blo 115785 116675 := bstep (se 1 (by rfl) ⟨87506, by rfl⟩ : syracuseStep 116675 = 175013) B175013
theorem B116691 : Blo 115785 116691 := bstep (se 1 (by rfl) ⟨87518, by rfl⟩ : syracuseStep 116691 = 175037) B175037
theorem B116707 : Blo 115785 116707 := bstep (se 1 (by rfl) ⟨87530, by rfl⟩ : syracuseStep 116707 = 175061) B175061
theorem B116723 : Blo 115785 116723 := bstep (se 1 (by rfl) ⟨87542, by rfl⟩ : syracuseStep 116723 = 175085) B175085
theorem B116739 : Blo 115785 116739 := bstep (se 1 (by rfl) ⟨87554, by rfl⟩ : syracuseStep 116739 = 175109) B175109
theorem B116755 : Blo 115785 116755 := bstep (se 1 (by rfl) ⟨87566, by rfl⟩ : syracuseStep 116755 = 175133) B175133
theorem B116771 : Blo 115785 116771 := bstep (se 1 (by rfl) ⟨87578, by rfl⟩ : syracuseStep 116771 = 175157) B175157
theorem B116787 : Blo 115785 116787 := bstep (se 1 (by rfl) ⟨87590, by rfl⟩ : syracuseStep 116787 = 175181) B175181
theorem B116803 : Blo 115785 116803 := bstep (se 1 (by rfl) ⟨87602, by rfl⟩ : syracuseStep 116803 = 175205) B175205
theorem B116819 : Blo 115785 116819 := bstep (se 1 (by rfl) ⟨87614, by rfl⟩ : syracuseStep 116819 = 175229) B175229
theorem B116835 : Blo 115785 116835 := bstep (se 1 (by rfl) ⟨87626, by rfl⟩ : syracuseStep 116835 = 175253) B175253
theorem B378989 : Blo 115785 378989 := bstep (se 3 (by rfl) ⟨71060, by rfl⟩ : syracuseStep 378989 = 142121) B142121
theorem B116851 : Blo 115785 116851 := bstep (se 1 (by rfl) ⟨87638, by rfl⟩ : syracuseStep 116851 = 175277) B175277
theorem B116867 : Blo 115785 116867 := bstep (se 1 (by rfl) ⟨87650, by rfl⟩ : syracuseStep 116867 = 175301) B175301
theorem B116883 : Blo 115785 116883 := bstep (se 1 (by rfl) ⟨87662, by rfl⟩ : syracuseStep 116883 = 175325) B175325
theorem B116899 : Blo 115785 116899 := bstep (se 1 (by rfl) ⟨87674, by rfl⟩ : syracuseStep 116899 = 175349) B175349
theorem B116915 : Blo 115785 116915 := bstep (se 1 (by rfl) ⟨87686, by rfl⟩ : syracuseStep 116915 = 175373) B175373
theorem B149683 : Blo 115785 149683 := bstep (se 1 (by rfl) ⟨112262, by rfl⟩ : syracuseStep 149683 = 224525) B224525
theorem B116931 : Blo 115785 116931 := bstep (se 1 (by rfl) ⟨87698, by rfl⟩ : syracuseStep 116931 = 175397) B175397
theorem B706765 : Blo 115785 706765 := bstep (se 3 (by rfl) ⟨132518, by rfl⟩ : syracuseStep 706765 = 265037) B265037
theorem B116947 : Blo 115785 116947 := bstep (se 1 (by rfl) ⟨87710, by rfl⟩ : syracuseStep 116947 = 175421) B175421
theorem B116963 : Blo 115785 116963 := bstep (se 1 (by rfl) ⟨87722, by rfl⟩ : syracuseStep 116963 = 175445) B175445
theorem B116979 : Blo 115785 116979 := bstep (se 1 (by rfl) ⟨87734, by rfl⟩ : syracuseStep 116979 = 175469) B175469
theorem B116995 : Blo 115785 116995 := bstep (se 1 (by rfl) ⟨87746, by rfl⟩ : syracuseStep 116995 = 175493) B175493
theorem B117011 : Blo 115785 117011 := bstep (se 1 (by rfl) ⟨87758, by rfl⟩ : syracuseStep 117011 = 175517) B175517
theorem B149779 : Blo 115785 149779 := bstep (se 1 (by rfl) ⟨112334, by rfl⟩ : syracuseStep 149779 = 224669) B224669
theorem B117027 : Blo 115785 117027 := bstep (se 1 (by rfl) ⟨87770, by rfl⟩ : syracuseStep 117027 = 175541) B175541
theorem B117043 : Blo 115785 117043 := bstep (se 1 (by rfl) ⟨87782, by rfl⟩ : syracuseStep 117043 = 175565) B175565
theorem B117059 : Blo 115785 117059 := bstep (se 1 (by rfl) ⟨87794, by rfl⟩ : syracuseStep 117059 = 175589) B175589
theorem B149843 : Blo 115785 149843 := bstep (se 1 (by rfl) ⟨112382, by rfl⟩ : syracuseStep 149843 = 224765) B224765
theorem B117075 : Blo 115785 117075 := bstep (se 1 (by rfl) ⟨87806, by rfl⟩ : syracuseStep 117075 = 175613) B175613
theorem B117091 : Blo 115785 117091 := bstep (se 1 (by rfl) ⟨87818, by rfl⟩ : syracuseStep 117091 = 175637) B175637
theorem B117107 : Blo 115785 117107 := bstep (se 1 (by rfl) ⟨87830, by rfl⟩ : syracuseStep 117107 = 175661) B175661
theorem B117123 : Blo 115785 117123 := bstep (se 1 (by rfl) ⟨87842, by rfl⟩ : syracuseStep 117123 = 175685) B175685
theorem B674189 : Blo 115785 674189 := bstep (se 3 (by rfl) ⟨126410, by rfl⟩ : syracuseStep 674189 = 252821) B252821
theorem B117139 : Blo 115785 117139 := bstep (se 1 (by rfl) ⟨87854, by rfl⟩ : syracuseStep 117139 = 175709) B175709
theorem B117155 : Blo 115785 117155 := bstep (se 1 (by rfl) ⟨87866, by rfl⟩ : syracuseStep 117155 = 175733) B175733
theorem B117171 : Blo 115785 117171 := bstep (se 1 (by rfl) ⟨87878, by rfl⟩ : syracuseStep 117171 = 175757) B175757
theorem B117187 : Blo 115785 117187 := bstep (se 1 (by rfl) ⟨87890, by rfl⟩ : syracuseStep 117187 = 175781) B175781
theorem B117203 : Blo 115785 117203 := bstep (se 1 (by rfl) ⟨87902, by rfl⟩ : syracuseStep 117203 = 175805) B175805
theorem B117219 : Blo 115785 117219 := bstep (se 1 (by rfl) ⟨87914, by rfl⟩ : syracuseStep 117219 = 175829) B175829
theorem B117235 : Blo 115785 117235 := bstep (se 1 (by rfl) ⟨87926, by rfl⟩ : syracuseStep 117235 = 175853) B175853
theorem B117251 : Blo 115785 117251 := bstep (se 1 (by rfl) ⟨87938, by rfl⟩ : syracuseStep 117251 = 175877) B175877
theorem B117267 : Blo 115785 117267 := bstep (se 1 (by rfl) ⟨87950, by rfl⟩ : syracuseStep 117267 = 175901) B175901
theorem B117283 : Blo 115785 117283 := bstep (se 1 (by rfl) ⟨87962, by rfl⟩ : syracuseStep 117283 = 175925) B175925
theorem B117299 : Blo 115785 117299 := bstep (se 1 (by rfl) ⟨87974, by rfl⟩ : syracuseStep 117299 = 175949) B175949
theorem B117315 : Blo 115785 117315 := bstep (se 1 (by rfl) ⟨87986, by rfl⟩ : syracuseStep 117315 = 175973) B175973
theorem B117331 : Blo 115785 117331 := bstep (se 1 (by rfl) ⟨87998, by rfl⟩ : syracuseStep 117331 = 175997) B175997
theorem B117347 : Blo 115785 117347 := bstep (se 1 (by rfl) ⟨88010, by rfl⟩ : syracuseStep 117347 = 176021) B176021
theorem B510563 : Blo 115785 510563 := bstep (se 1 (by rfl) ⟨382922, by rfl⟩ : syracuseStep 510563 = 765845) B765845
theorem B117363 : Blo 115785 117363 := bstep (se 1 (by rfl) ⟨88022, by rfl⟩ : syracuseStep 117363 = 176045) B176045
theorem B117379 : Blo 115785 117379 := bstep (se 1 (by rfl) ⟨88034, by rfl⟩ : syracuseStep 117379 = 176069) B176069
theorem B117395 : Blo 115785 117395 := bstep (se 1 (by rfl) ⟨88046, by rfl⟩ : syracuseStep 117395 = 176093) B176093
theorem B117411 : Blo 115785 117411 := bstep (se 1 (by rfl) ⟨88058, by rfl⟩ : syracuseStep 117411 = 176117) B176117
theorem B117427 : Blo 115785 117427 := bstep (se 1 (by rfl) ⟨88070, by rfl⟩ : syracuseStep 117427 = 176141) B176141
theorem B117443 : Blo 115785 117443 := bstep (se 1 (by rfl) ⟨88082, by rfl⟩ : syracuseStep 117443 = 176165) B176165
theorem B117459 : Blo 115785 117459 := bstep (se 1 (by rfl) ⟨88094, by rfl⟩ : syracuseStep 117459 = 176189) B176189
theorem B117475 : Blo 115785 117475 := bstep (se 1 (by rfl) ⟨88106, by rfl⟩ : syracuseStep 117475 = 176213) B176213
theorem B117491 : Blo 115785 117491 := bstep (se 1 (by rfl) ⟨88118, by rfl⟩ : syracuseStep 117491 = 176237) B176237
theorem B117507 : Blo 115785 117507 := bstep (se 1 (by rfl) ⟨88130, by rfl⟩ : syracuseStep 117507 = 176261) B176261
theorem B150275 : Blo 115785 150275 := bstep (se 1 (by rfl) ⟨112706, by rfl⟩ : syracuseStep 150275 = 225413) B225413
theorem B117523 : Blo 115785 117523 := bstep (se 1 (by rfl) ⟨88142, by rfl⟩ : syracuseStep 117523 = 176285) B176285
theorem B117539 : Blo 115785 117539 := bstep (se 1 (by rfl) ⟨88154, by rfl⟩ : syracuseStep 117539 = 176309) B176309
theorem B609059 : Blo 115785 609059 := bstep (se 1 (by rfl) ⟨456794, by rfl⟩ : syracuseStep 609059 = 913589) B913589
theorem B117555 : Blo 115785 117555 := bstep (se 1 (by rfl) ⟨88166, by rfl⟩ : syracuseStep 117555 = 176333) B176333
theorem B117571 : Blo 115785 117571 := bstep (se 1 (by rfl) ⟨88178, by rfl⟩ : syracuseStep 117571 = 176357) B176357
theorem B117587 : Blo 115785 117587 := bstep (se 1 (by rfl) ⟨88190, by rfl⟩ : syracuseStep 117587 = 176381) B176381
theorem B445283 : Blo 115785 445283 := bstep (se 1 (by rfl) ⟨333962, by rfl⟩ : syracuseStep 445283 = 667925) B667925
theorem B117603 : Blo 115785 117603 := bstep (se 1 (by rfl) ⟨88202, by rfl⟩ : syracuseStep 117603 = 176405) B176405
theorem B445297 : Blo 115785 445297 := bstep (se 2 (by rfl) ⟨166986, by rfl⟩ : syracuseStep 445297 = 333973) B333973
theorem B117619 : Blo 115785 117619 := bstep (se 1 (by rfl) ⟨88214, by rfl⟩ : syracuseStep 117619 = 176429) B176429
theorem B117635 : Blo 115785 117635 := bstep (se 1 (by rfl) ⟨88226, by rfl⟩ : syracuseStep 117635 = 176453) B176453
theorem B117651 : Blo 115785 117651 := bstep (se 1 (by rfl) ⟨88238, by rfl⟩ : syracuseStep 117651 = 176477) B176477
theorem B117667 : Blo 115785 117667 := bstep (se 1 (by rfl) ⟨88250, by rfl⟩ : syracuseStep 117667 = 176501) B176501
theorem B117683 : Blo 115785 117683 := bstep (se 1 (by rfl) ⟨88262, by rfl⟩ : syracuseStep 117683 = 176525) B176525
theorem B117699 : Blo 115785 117699 := bstep (se 1 (by rfl) ⟨88274, by rfl⟩ : syracuseStep 117699 = 176549) B176549
theorem B117715 : Blo 115785 117715 := bstep (se 1 (by rfl) ⟨88286, by rfl⟩ : syracuseStep 117715 = 176573) B176573
theorem B117731 : Blo 115785 117731 := bstep (se 1 (by rfl) ⟨88298, by rfl⟩ : syracuseStep 117731 = 176597) B176597
theorem B117747 : Blo 115785 117747 := bstep (se 1 (by rfl) ⟨88310, by rfl⟩ : syracuseStep 117747 = 176621) B176621
theorem B117763 : Blo 115785 117763 := bstep (se 1 (by rfl) ⟨88322, by rfl⟩ : syracuseStep 117763 = 176645) B176645
theorem B117779 : Blo 115785 117779 := bstep (se 1 (by rfl) ⟨88334, by rfl⟩ : syracuseStep 117779 = 176669) B176669
theorem B117795 : Blo 115785 117795 := bstep (se 1 (by rfl) ⟨88346, by rfl⟩ : syracuseStep 117795 = 176693) B176693
theorem B117811 : Blo 115785 117811 := bstep (se 1 (by rfl) ⟨88358, by rfl⟩ : syracuseStep 117811 = 176717) B176717
theorem B117827 : Blo 115785 117827 := bstep (se 1 (by rfl) ⟨88370, by rfl⟩ : syracuseStep 117827 = 176741) B176741
theorem B674893 : Blo 115785 674893 := bstep (se 3 (by rfl) ⟨126542, by rfl⟩ : syracuseStep 674893 = 253085) B253085
theorem B117843 : Blo 115785 117843 := bstep (se 1 (by rfl) ⟨88382, by rfl⟩ : syracuseStep 117843 = 176765) B176765
theorem B117859 : Blo 115785 117859 := bstep (se 1 (by rfl) ⟨88394, by rfl⟩ : syracuseStep 117859 = 176789) B176789
theorem B117875 : Blo 115785 117875 := bstep (se 1 (by rfl) ⟨88406, by rfl⟩ : syracuseStep 117875 = 176813) B176813
theorem B117891 : Blo 115785 117891 := bstep (se 1 (by rfl) ⟨88418, by rfl⟩ : syracuseStep 117891 = 176837) B176837
theorem B117907 : Blo 115785 117907 := bstep (se 1 (by rfl) ⟨88430, by rfl⟩ : syracuseStep 117907 = 176861) B176861
theorem B117923 : Blo 115785 117923 := bstep (se 1 (by rfl) ⟨88442, by rfl⟩ : syracuseStep 117923 = 176885) B176885
theorem B117939 : Blo 115785 117939 := bstep (se 1 (by rfl) ⟨88454, by rfl⟩ : syracuseStep 117939 = 176909) B176909
theorem B117955 : Blo 115785 117955 := bstep (se 1 (by rfl) ⟨88466, by rfl⟩ : syracuseStep 117955 = 176933) B176933
theorem B117971 : Blo 115785 117971 := bstep (se 1 (by rfl) ⟨88478, by rfl⟩ : syracuseStep 117971 = 176957) B176957
theorem B117987 : Blo 115785 117987 := bstep (se 1 (by rfl) ⟨88490, by rfl⟩ : syracuseStep 117987 = 176981) B176981
theorem B118003 : Blo 115785 118003 := bstep (se 1 (by rfl) ⟨88502, by rfl⟩ : syracuseStep 118003 = 177005) B177005
theorem B118019 : Blo 115785 118019 := bstep (se 1 (by rfl) ⟨88514, by rfl⟩ : syracuseStep 118019 = 177029) B177029
theorem B544013 : Blo 115785 544013 := bstep (se 3 (by rfl) ⟨102002, by rfl⟩ : syracuseStep 544013 = 204005) B204005
theorem B118035 : Blo 115785 118035 := bstep (se 1 (by rfl) ⟨88526, by rfl⟩ : syracuseStep 118035 = 177053) B177053
theorem B118051 : Blo 115785 118051 := bstep (se 1 (by rfl) ⟨88538, by rfl⟩ : syracuseStep 118051 = 177077) B177077
theorem B118067 : Blo 115785 118067 := bstep (se 1 (by rfl) ⟨88550, by rfl⟩ : syracuseStep 118067 = 177101) B177101
theorem B118083 : Blo 115785 118083 := bstep (se 1 (by rfl) ⟨88562, by rfl⟩ : syracuseStep 118083 = 177125) B177125
theorem B118099 : Blo 115785 118099 := bstep (se 1 (by rfl) ⟨88574, by rfl⟩ : syracuseStep 118099 = 177149) B177149
theorem B314723 : Blo 115785 314723 := bstep (se 1 (by rfl) ⟨236042, by rfl⟩ : syracuseStep 314723 = 472085) B472085
theorem B118115 : Blo 115785 118115 := bstep (se 1 (by rfl) ⟨88586, by rfl⟩ : syracuseStep 118115 = 177173) B177173
theorem B118131 : Blo 115785 118131 := bstep (se 1 (by rfl) ⟨88598, by rfl⟩ : syracuseStep 118131 = 177197) B177197
theorem B118147 : Blo 115785 118147 := bstep (se 1 (by rfl) ⟨88610, by rfl⟩ : syracuseStep 118147 = 177221) B177221
theorem B118163 : Blo 115785 118163 := bstep (se 1 (by rfl) ⟨88622, by rfl⟩ : syracuseStep 118163 = 177245) B177245
theorem B118179 : Blo 115785 118179 := bstep (se 1 (by rfl) ⟨88634, by rfl⟩ : syracuseStep 118179 = 177269) B177269
theorem B380333 : Blo 115785 380333 := bstep (se 3 (by rfl) ⟨71312, by rfl⟩ : syracuseStep 380333 = 142625) B142625
theorem B118195 : Blo 115785 118195 := bstep (se 1 (by rfl) ⟨88646, by rfl⟩ : syracuseStep 118195 = 177293) B177293
theorem B118211 : Blo 115785 118211 := bstep (se 1 (by rfl) ⟨88658, by rfl⟩ : syracuseStep 118211 = 177317) B177317
theorem B150979 : Blo 115785 150979 := bstep (se 1 (by rfl) ⟨113234, by rfl⟩ : syracuseStep 150979 = 226469) B226469
theorem B118227 : Blo 115785 118227 := bstep (se 1 (by rfl) ⟨88670, by rfl⟩ : syracuseStep 118227 = 177341) B177341
theorem B118243 : Blo 115785 118243 := bstep (se 1 (by rfl) ⟨88682, by rfl⟩ : syracuseStep 118243 = 177365) B177365
theorem B118259 : Blo 115785 118259 := bstep (se 1 (by rfl) ⟨88694, by rfl⟩ : syracuseStep 118259 = 177389) B177389
theorem B118275 : Blo 115785 118275 := bstep (se 1 (by rfl) ⟨88706, by rfl⟩ : syracuseStep 118275 = 177413) B177413
theorem B118291 : Blo 115785 118291 := bstep (se 1 (by rfl) ⟨88718, by rfl⟩ : syracuseStep 118291 = 177437) B177437
theorem B118307 : Blo 115785 118307 := bstep (se 1 (by rfl) ⟨88730, by rfl⟩ : syracuseStep 118307 = 177461) B177461
theorem B151075 : Blo 115785 151075 := bstep (se 1 (by rfl) ⟨113306, by rfl⟩ : syracuseStep 151075 = 226613) B226613
theorem B118323 : Blo 115785 118323 := bstep (se 1 (by rfl) ⟨88742, by rfl⟩ : syracuseStep 118323 = 177485) B177485
theorem B118339 : Blo 115785 118339 := bstep (se 1 (by rfl) ⟨88754, by rfl⟩ : syracuseStep 118339 = 177509) B177509
theorem B118355 : Blo 115785 118355 := bstep (se 1 (by rfl) ⟨88766, by rfl⟩ : syracuseStep 118355 = 177533) B177533
theorem B118371 : Blo 115785 118371 := bstep (se 1 (by rfl) ⟨88778, by rfl⟩ : syracuseStep 118371 = 177557) B177557
theorem B118387 : Blo 115785 118387 := bstep (se 1 (by rfl) ⟨88790, by rfl⟩ : syracuseStep 118387 = 177581) B177581
theorem B118403 : Blo 115785 118403 := bstep (se 1 (by rfl) ⟨88802, by rfl⟩ : syracuseStep 118403 = 177605) B177605
theorem B118419 : Blo 115785 118419 := bstep (se 1 (by rfl) ⟨88814, by rfl⟩ : syracuseStep 118419 = 177629) B177629
theorem B118435 : Blo 115785 118435 := bstep (se 1 (by rfl) ⟨88826, by rfl⟩ : syracuseStep 118435 = 177653) B177653
theorem B118451 : Blo 115785 118451 := bstep (se 1 (by rfl) ⟨88838, by rfl⟩ : syracuseStep 118451 = 177677) B177677
theorem B118467 : Blo 115785 118467 := bstep (se 1 (by rfl) ⟨88850, by rfl⟩ : syracuseStep 118467 = 177701) B177701
theorem B118483 : Blo 115785 118483 := bstep (se 1 (by rfl) ⟨88862, by rfl⟩ : syracuseStep 118483 = 177725) B177725
theorem B118499 : Blo 115785 118499 := bstep (se 1 (by rfl) ⟨88874, by rfl⟩ : syracuseStep 118499 = 177749) B177749
theorem B904931 : Blo 115785 904931 := bstep (se 1 (by rfl) ⟨678698, by rfl⟩ : syracuseStep 904931 = 1357397) B1357397
theorem B118515 : Blo 115785 118515 := bstep (se 1 (by rfl) ⟨88886, by rfl⟩ : syracuseStep 118515 = 177773) B177773
theorem B118531 : Blo 115785 118531 := bstep (se 1 (by rfl) ⟨88898, by rfl⟩ : syracuseStep 118531 = 177797) B177797
theorem B118547 : Blo 115785 118547 := bstep (se 1 (by rfl) ⟨88910, by rfl⟩ : syracuseStep 118547 = 177821) B177821
theorem B118563 : Blo 115785 118563 := bstep (se 1 (by rfl) ⟨88922, by rfl⟩ : syracuseStep 118563 = 177845) B177845
theorem B118579 : Blo 115785 118579 := bstep (se 1 (by rfl) ⟨88934, by rfl⟩ : syracuseStep 118579 = 177869) B177869
theorem B118595 : Blo 115785 118595 := bstep (se 1 (by rfl) ⟨88946, by rfl⟩ : syracuseStep 118595 = 177893) B177893
theorem B118611 : Blo 115785 118611 := bstep (se 1 (by rfl) ⟨88958, by rfl⟩ : syracuseStep 118611 = 177917) B177917
theorem B118627 : Blo 115785 118627 := bstep (se 1 (by rfl) ⟨88970, by rfl⟩ : syracuseStep 118627 = 177941) B177941
theorem B380771 : Blo 115785 380771 := bstep (se 1 (by rfl) ⟨285578, by rfl⟩ : syracuseStep 380771 = 571157) B571157
theorem B118643 : Blo 115785 118643 := bstep (se 1 (by rfl) ⟨88982, by rfl⟩ : syracuseStep 118643 = 177965) B177965
theorem B118659 : Blo 115785 118659 := bstep (se 1 (by rfl) ⟨88994, by rfl⟩ : syracuseStep 118659 = 177989) B177989
theorem B118675 : Blo 115785 118675 := bstep (se 1 (by rfl) ⟨89006, by rfl⟩ : syracuseStep 118675 = 178013) B178013
theorem B249763 : Blo 115785 249763 := bstep (se 1 (by rfl) ⟨187322, by rfl⟩ : syracuseStep 249763 = 374645) B374645
theorem B118691 : Blo 115785 118691 := bstep (se 1 (by rfl) ⟨89018, by rfl⟩ : syracuseStep 118691 = 178037) B178037
theorem B118707 : Blo 115785 118707 := bstep (se 1 (by rfl) ⟨89030, by rfl⟩ : syracuseStep 118707 = 178061) B178061
theorem B118723 : Blo 115785 118723 := bstep (se 1 (by rfl) ⟨89042, by rfl⟩ : syracuseStep 118723 = 178085) B178085
theorem B118739 : Blo 115785 118739 := bstep (se 1 (by rfl) ⟨89054, by rfl⟩ : syracuseStep 118739 = 178109) B178109
theorem B446435 : Blo 115785 446435 := bstep (se 1 (by rfl) ⟨334826, by rfl⟩ : syracuseStep 446435 = 669653) B669653
theorem B118755 : Blo 115785 118755 := bstep (se 1 (by rfl) ⟨89066, by rfl⟩ : syracuseStep 118755 = 178133) B178133
theorem B118771 : Blo 115785 118771 := bstep (se 1 (by rfl) ⟨89078, by rfl⟩ : syracuseStep 118771 = 178157) B178157
theorem B118787 : Blo 115785 118787 := bstep (se 1 (by rfl) ⟨89090, by rfl⟩ : syracuseStep 118787 = 178181) B178181
theorem B118803 : Blo 115785 118803 := bstep (se 1 (by rfl) ⟨89102, by rfl⟩ : syracuseStep 118803 = 178205) B178205
theorem B151571 : Blo 115785 151571 := bstep (se 1 (by rfl) ⟨113678, by rfl⟩ : syracuseStep 151571 = 227357) B227357
theorem B118819 : Blo 115785 118819 := bstep (se 1 (by rfl) ⟨89114, by rfl⟩ : syracuseStep 118819 = 178229) B178229
theorem B118835 : Blo 115785 118835 := bstep (se 1 (by rfl) ⟨89126, by rfl⟩ : syracuseStep 118835 = 178253) B178253
theorem B118851 : Blo 115785 118851 := bstep (se 1 (by rfl) ⟨89138, by rfl⟩ : syracuseStep 118851 = 178277) B178277
theorem B118867 : Blo 115785 118867 := bstep (se 1 (by rfl) ⟨89150, by rfl⟩ : syracuseStep 118867 = 178301) B178301
theorem B118883 : Blo 115785 118883 := bstep (se 1 (by rfl) ⟨89162, by rfl⟩ : syracuseStep 118883 = 178325) B178325
theorem B118899 : Blo 115785 118899 := bstep (se 1 (by rfl) ⟨89174, by rfl⟩ : syracuseStep 118899 = 178349) B178349
theorem B118915 : Blo 115785 118915 := bstep (se 1 (by rfl) ⟨89186, by rfl⟩ : syracuseStep 118915 = 178373) B178373
theorem B118931 : Blo 115785 118931 := bstep (se 1 (by rfl) ⟨89198, by rfl⟩ : syracuseStep 118931 = 178397) B178397
theorem B118947 : Blo 115785 118947 := bstep (se 1 (by rfl) ⟨89210, by rfl⟩ : syracuseStep 118947 = 178421) B178421
theorem B118963 : Blo 115785 118963 := bstep (se 1 (by rfl) ⟨89222, by rfl⟩ : syracuseStep 118963 = 178445) B178445
theorem B118979 : Blo 115785 118979 := bstep (se 1 (by rfl) ⟨89234, by rfl⟩ : syracuseStep 118979 = 178469) B178469
theorem B118995 : Blo 115785 118995 := bstep (se 1 (by rfl) ⟨89246, by rfl⟩ : syracuseStep 118995 = 178493) B178493
theorem B119011 : Blo 115785 119011 := bstep (se 1 (by rfl) ⟨89258, by rfl⟩ : syracuseStep 119011 = 178517) B178517
theorem B119027 : Blo 115785 119027 := bstep (se 1 (by rfl) ⟨89270, by rfl⟩ : syracuseStep 119027 = 178541) B178541
theorem B119043 : Blo 115785 119043 := bstep (se 1 (by rfl) ⟨89282, by rfl⟩ : syracuseStep 119043 = 178565) B178565
theorem B119059 : Blo 115785 119059 := bstep (se 1 (by rfl) ⟨89294, by rfl⟩ : syracuseStep 119059 = 178589) B178589
theorem B446755 : Blo 115785 446755 := bstep (se 1 (by rfl) ⟨335066, by rfl⟩ : syracuseStep 446755 = 670133) B670133
theorem B119075 : Blo 115785 119075 := bstep (se 1 (by rfl) ⟨89306, by rfl⟩ : syracuseStep 119075 = 178613) B178613
theorem B119091 : Blo 115785 119091 := bstep (se 1 (by rfl) ⟨89318, by rfl⟩ : syracuseStep 119091 = 178637) B178637
theorem B119107 : Blo 115785 119107 := bstep (se 1 (by rfl) ⟨89330, by rfl⟩ : syracuseStep 119107 = 178661) B178661
theorem B119123 : Blo 115785 119123 := bstep (se 1 (by rfl) ⟨89342, by rfl⟩ : syracuseStep 119123 = 178685) B178685
theorem B119139 : Blo 115785 119139 := bstep (se 1 (by rfl) ⟨89354, by rfl⟩ : syracuseStep 119139 = 178709) B178709
theorem B119155 : Blo 115785 119155 := bstep (se 1 (by rfl) ⟨89366, by rfl⟩ : syracuseStep 119155 = 178733) B178733
theorem B119171 : Blo 115785 119171 := bstep (se 1 (by rfl) ⟨89378, by rfl⟩ : syracuseStep 119171 = 178757) B178757
theorem B119187 : Blo 115785 119187 := bstep (se 1 (by rfl) ⟨89390, by rfl⟩ : syracuseStep 119187 = 178781) B178781
theorem B119203 : Blo 115785 119203 := bstep (se 1 (by rfl) ⟨89402, by rfl⟩ : syracuseStep 119203 = 178805) B178805
theorem B119219 : Blo 115785 119219 := bstep (se 1 (by rfl) ⟨89414, by rfl⟩ : syracuseStep 119219 = 178829) B178829
theorem B119235 : Blo 115785 119235 := bstep (se 1 (by rfl) ⟨89426, by rfl⟩ : syracuseStep 119235 = 178853) B178853
theorem B119251 : Blo 115785 119251 := bstep (se 1 (by rfl) ⟨89438, by rfl⟩ : syracuseStep 119251 = 178877) B178877
theorem B119267 : Blo 115785 119267 := bstep (se 1 (by rfl) ⟨89450, by rfl⟩ : syracuseStep 119267 = 178901) B178901
theorem B119283 : Blo 115785 119283 := bstep (se 1 (by rfl) ⟨89462, by rfl⟩ : syracuseStep 119283 = 178925) B178925
theorem B119299 : Blo 115785 119299 := bstep (se 1 (by rfl) ⟨89474, by rfl⟩ : syracuseStep 119299 = 178949) B178949
theorem B119315 : Blo 115785 119315 := bstep (se 1 (by rfl) ⟨89486, by rfl⟩ : syracuseStep 119315 = 178973) B178973
theorem B119331 : Blo 115785 119331 := bstep (se 1 (by rfl) ⟨89498, by rfl⟩ : syracuseStep 119331 = 178997) B178997
theorem B119347 : Blo 115785 119347 := bstep (se 1 (by rfl) ⟨89510, by rfl⟩ : syracuseStep 119347 = 179021) B179021
theorem B119363 : Blo 115785 119363 := bstep (se 1 (by rfl) ⟨89522, by rfl⟩ : syracuseStep 119363 = 179045) B179045
theorem B676421 : Blo 115785 676421 := bstep (se 4 (by rfl) ⟨63414, by rfl⟩ : syracuseStep 676421 = 126829) B126829
theorem B119379 : Blo 115785 119379 := bstep (se 1 (by rfl) ⟨89534, by rfl⟩ : syracuseStep 119379 = 179069) B179069
theorem B119395 : Blo 115785 119395 := bstep (se 1 (by rfl) ⟨89546, by rfl⟩ : syracuseStep 119395 = 179093) B179093
theorem B643697 : Blo 115785 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B119411 : Blo 115785 119411 := bstep (se 1 (by rfl) ⟨89558, by rfl⟩ : syracuseStep 119411 = 179117) B179117
theorem B119427 : Blo 115785 119427 := bstep (se 1 (by rfl) ⟨89570, by rfl⟩ : syracuseStep 119427 = 179141) B179141
theorem B119443 : Blo 115785 119443 := bstep (se 1 (by rfl) ⟨89582, by rfl⟩ : syracuseStep 119443 = 179165) B179165
theorem B119459 : Blo 115785 119459 := bstep (se 1 (by rfl) ⟨89594, by rfl⟩ : syracuseStep 119459 = 179189) B179189
theorem B119475 : Blo 115785 119475 := bstep (se 1 (by rfl) ⟨89606, by rfl⟩ : syracuseStep 119475 = 179213) B179213
theorem B119491 : Blo 115785 119491 := bstep (se 1 (by rfl) ⟨89618, by rfl⟩ : syracuseStep 119491 = 179237) B179237
theorem B152275 : Blo 115785 152275 := bstep (se 1 (by rfl) ⟨114206, by rfl⟩ : syracuseStep 152275 = 228413) B228413
theorem B119507 : Blo 115785 119507 := bstep (se 1 (by rfl) ⟨89630, by rfl⟩ : syracuseStep 119507 = 179261) B179261
theorem B119523 : Blo 115785 119523 := bstep (se 1 (by rfl) ⟨89642, by rfl⟩ : syracuseStep 119523 = 179285) B179285
theorem B250609 : Blo 115785 250609 := bstep (se 2 (by rfl) ⟨93978, by rfl⟩ : syracuseStep 250609 = 187957) B187957
theorem B119539 : Blo 115785 119539 := bstep (se 1 (by rfl) ⟨89654, by rfl⟩ : syracuseStep 119539 = 179309) B179309
theorem B119555 : Blo 115785 119555 := bstep (se 1 (by rfl) ⟨89666, by rfl⟩ : syracuseStep 119555 = 179333) B179333
theorem B119571 : Blo 115785 119571 := bstep (se 1 (by rfl) ⟨89678, by rfl⟩ : syracuseStep 119571 = 179357) B179357
theorem B119587 : Blo 115785 119587 := bstep (se 1 (by rfl) ⟨89690, by rfl⟩ : syracuseStep 119587 = 179381) B179381
theorem B643889 : Blo 115785 643889 := bstep (se 2 (by rfl) ⟨241458, by rfl⟩ : syracuseStep 643889 = 482917) B482917
theorem B119603 : Blo 115785 119603 := bstep (se 1 (by rfl) ⟨89702, by rfl⟩ : syracuseStep 119603 = 179405) B179405
theorem B119619 : Blo 115785 119619 := bstep (se 1 (by rfl) ⟨89714, by rfl⟩ : syracuseStep 119619 = 179429) B179429
theorem B742213 : Blo 115785 742213 := bstep (se 4 (by rfl) ⟨69582, by rfl⟩ : syracuseStep 742213 = 139165) B139165
theorem B119635 : Blo 115785 119635 := bstep (se 1 (by rfl) ⟨89726, by rfl⟩ : syracuseStep 119635 = 179453) B179453
theorem B119651 : Blo 115785 119651 := bstep (se 1 (by rfl) ⟨89738, by rfl⟩ : syracuseStep 119651 = 179477) B179477
theorem B119667 : Blo 115785 119667 := bstep (se 1 (by rfl) ⟨89750, by rfl⟩ : syracuseStep 119667 = 179501) B179501
theorem B119683 : Blo 115785 119683 := bstep (se 1 (by rfl) ⟨89762, by rfl⟩ : syracuseStep 119683 = 179525) B179525
theorem B119699 : Blo 115785 119699 := bstep (se 1 (by rfl) ⟨89774, by rfl⟩ : syracuseStep 119699 = 179549) B179549
theorem B119715 : Blo 115785 119715 := bstep (se 1 (by rfl) ⟨89786, by rfl⟩ : syracuseStep 119715 = 179573) B179573
theorem B119731 : Blo 115785 119731 := bstep (se 1 (by rfl) ⟨89798, by rfl⟩ : syracuseStep 119731 = 179597) B179597
theorem B119747 : Blo 115785 119747 := bstep (se 1 (by rfl) ⟨89810, by rfl⟩ : syracuseStep 119747 = 179621) B179621
theorem B119763 : Blo 115785 119763 := bstep (se 1 (by rfl) ⟨89822, by rfl⟩ : syracuseStep 119763 = 179645) B179645
theorem B119779 : Blo 115785 119779 := bstep (se 1 (by rfl) ⟨89834, by rfl⟩ : syracuseStep 119779 = 179669) B179669
theorem B677105 : Blo 115785 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B284305 : Blo 115785 284305 := bstep (se 2 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 284305 = 213229) B213229
theorem B382691 : Blo 115785 382691 := bstep (se 1 (by rfl) ⟨287018, by rfl⟩ : syracuseStep 382691 = 574037) B574037
theorem B186131 : Blo 115785 186131 := bstep (se 1 (by rfl) ⟨139598, by rfl⟩ : syracuseStep 186131 = 279197) B279197
theorem B284579 : Blo 115785 284579 := bstep (se 1 (by rfl) ⟨213434, by rfl⟩ : syracuseStep 284579 = 426869) B426869
theorem B382915 : Blo 115785 382915 := bstep (se 1 (by rfl) ⟨287186, by rfl⟩ : syracuseStep 382915 = 574373) B574373
theorem B382925 : Blo 115785 382925 := bstep (se 3 (by rfl) ⟨71798, by rfl⟩ : syracuseStep 382925 = 143597) B143597
theorem B153619 : Blo 115785 153619 := bstep (se 1 (by rfl) ⟨115214, by rfl⟩ : syracuseStep 153619 = 230429) B230429
theorem B186419 : Blo 115785 186419 := bstep (se 1 (by rfl) ⟨139814, by rfl⟩ : syracuseStep 186419 = 279629) B279629
theorem B284867 : Blo 115785 284867 := bstep (se 1 (by rfl) ⟨213650, by rfl⟩ : syracuseStep 284867 = 427301) B427301
theorem B285059 : Blo 115785 285059 := bstep (se 1 (by rfl) ⟨213794, by rfl⟩ : syracuseStep 285059 = 427589) B427589
theorem B448973 : Blo 115785 448973 := bstep (se 3 (by rfl) ⟨84182, by rfl⟩ : syracuseStep 448973 = 168365) B168365
theorem B186835 : Blo 115785 186835 := bstep (se 1 (by rfl) ⟨140126, by rfl⟩ : syracuseStep 186835 = 280253) B280253
theorem B1530353 : Blo 115785 1530353 := bstep (se 2 (by rfl) ⟨573882, by rfl⟩ : syracuseStep 1530353 = 1147765) B1147765
theorem B252497 : Blo 115785 252497 := bstep (se 2 (by rfl) ⟨94686, by rfl⟩ : syracuseStep 252497 = 189373) B189373
theorem B678563 : Blo 115785 678563 := bstep (se 1 (by rfl) ⟨508922, by rfl⟩ : syracuseStep 678563 = 1017845) B1017845
theorem B187105 : Blo 115785 187105 := bstep (se 2 (by rfl) ⟨70164, by rfl⟩ : syracuseStep 187105 = 140329) B140329
theorem B1334069 : Blo 115785 1334069 := bstep (se 5 (by rfl) ⟨62534, by rfl⟩ : syracuseStep 1334069 = 125069) B125069
theorem B645965 : Blo 115785 645965 := bstep (se 3 (by rfl) ⟨121118, by rfl⟩ : syracuseStep 645965 = 242237) B242237
theorem B220067 : Blo 115785 220067 := bstep (se 1 (by rfl) ⟨165050, by rfl⟩ : syracuseStep 220067 = 330101) B330101
theorem B187361 : Blo 115785 187361 := bstep (se 2 (by rfl) ⟨70260, by rfl⟩ : syracuseStep 187361 = 140521) B140521
theorem B154675 : Blo 115785 154675 := bstep (se 1 (by rfl) ⟨116006, by rfl⟩ : syracuseStep 154675 = 232013) B232013
theorem B1956917 : Blo 115785 1956917 := bstep (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) B183461
theorem B318563 : Blo 115785 318563 := bstep (se 1 (by rfl) ⟨238922, by rfl⟩ : syracuseStep 318563 = 477845) B477845
theorem B285905 : Blo 115785 285905 := bstep (se 2 (by rfl) ⟨107214, by rfl⟩ : syracuseStep 285905 = 214429) B214429
theorem B286019 : Blo 115785 286019 := bstep (se 1 (by rfl) ⟨214514, by rfl⟩ : syracuseStep 286019 = 429029) B429029
theorem B286193 : Blo 115785 286193 := bstep (se 2 (by rfl) ⟨107322, by rfl⟩ : syracuseStep 286193 = 214645) B214645
theorem B188065 : Blo 115785 188065 := bstep (se 2 (by rfl) ⟨70524, by rfl⟩ : syracuseStep 188065 = 141049) B141049
theorem B220963 : Blo 115785 220963 := bstep (se 1 (by rfl) ⟨165722, by rfl⟩ : syracuseStep 220963 = 331445) B331445
theorem B548657 : Blo 115785 548657 := bstep (se 2 (by rfl) ⟨205746, by rfl⟩ : syracuseStep 548657 = 411493) B411493
theorem B253795 : Blo 115785 253795 := bstep (se 1 (by rfl) ⟨190346, by rfl⟩ : syracuseStep 253795 = 380693) B380693
theorem B319405 : Blo 115785 319405 := bstep (se 3 (by rfl) ⟨59888, by rfl⟩ : syracuseStep 319405 = 119777) B119777
theorem B221123 : Blo 115785 221123 := bstep (se 1 (by rfl) ⟨165842, by rfl⟩ : syracuseStep 221123 = 331685) B331685
theorem B745699 : Blo 115785 745699 := bstep (se 1 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 745699 = 1118549) B1118549
theorem B1532357 : Blo 115785 1532357 := bstep (se 4 (by rfl) ⟨143658, by rfl⟩ : syracuseStep 1532357 = 287317) B287317
theorem B188963 : Blo 115785 188963 := bstep (se 1 (by rfl) ⟨141722, by rfl⟩ : syracuseStep 188963 = 283445) B283445
theorem B189155 : Blo 115785 189155 := bstep (se 1 (by rfl) ⟨141866, by rfl⟩ : syracuseStep 189155 = 283733) B283733
theorem B156529 : Blo 115785 156529 := bstep (se 2 (by rfl) ⟨58698, by rfl⟩ : syracuseStep 156529 = 117397) B117397
theorem B320387 : Blo 115785 320387 := bstep (se 1 (by rfl) ⟨240290, by rfl⟩ : syracuseStep 320387 = 480581) B480581
theorem B3761093 : Blo 115785 3761093 := bstep (se 4 (by rfl) ⟨352602, by rfl⟩ : syracuseStep 3761093 = 705205) B705205
theorem B418765 : Blo 115785 418765 := bstep (se 3 (by rfl) ⟨78518, by rfl⟩ : syracuseStep 418765 = 157037) B157037
theorem B222193 : Blo 115785 222193 := bstep (se 2 (by rfl) ⟨83322, by rfl⟩ : syracuseStep 222193 = 166645) B166645
theorem B255025 : Blo 115785 255025 := bstep (se 2 (by rfl) ⟨95634, by rfl⟩ : syracuseStep 255025 = 191269) B191269
theorem B451889 : Blo 115785 451889 := bstep (se 2 (by rfl) ⟨169458, by rfl⟩ : syracuseStep 451889 = 338917) B338917
theorem B124211 : Blo 115785 124211 := bstep (se 1 (by rfl) ⟨93158, by rfl⟩ : syracuseStep 124211 = 186317) B186317
theorem B190129 : Blo 115785 190129 := bstep (se 2 (by rfl) ⟨71298, by rfl⟩ : syracuseStep 190129 = 142597) B142597
theorem B255811 : Blo 115785 255811 := bstep (se 1 (by rfl) ⟨191858, by rfl⟩ : syracuseStep 255811 = 383717) B383717
theorem B681797 : Blo 115785 681797 := bstep (se 4 (by rfl) ⟨63918, by rfl⟩ : syracuseStep 681797 = 127837) B127837
theorem B223249 : Blo 115785 223249 := bstep (se 2 (by rfl) ⟨83718, by rfl⟩ : syracuseStep 223249 = 167437) B167437
theorem B649315 : Blo 115785 649315 := bstep (se 1 (by rfl) ⟨486986, by rfl⟩ : syracuseStep 649315 = 973973) B973973
theorem B190577 : Blo 115785 190577 := bstep (se 2 (by rfl) ⟨71466, by rfl⟩ : syracuseStep 190577 = 142933) B142933
theorem B125155 : Blo 115785 125155 := bstep (se 1 (by rfl) ⟨93866, by rfl⟩ : syracuseStep 125155 = 187733) B187733
theorem B387395 : Blo 115785 387395 := bstep (se 1 (by rfl) ⟨290546, by rfl⟩ : syracuseStep 387395 = 581093) B581093
theorem B223651 : Blo 115785 223651 := bstep (se 1 (by rfl) ⟨167738, by rfl⟩ : syracuseStep 223651 = 335477) B335477
theorem B7301573 : Blo 115785 7301573 := bstep (se 4 (by rfl) ⟨684522, by rfl⟩ : syracuseStep 7301573 = 1369045) B1369045
theorem B223697 : Blo 115785 223697 := bstep (se 2 (by rfl) ⟨83886, by rfl⟩ : syracuseStep 223697 = 167773) B167773
theorem B289379 : Blo 115785 289379 := bstep (se 1 (by rfl) ⟨217034, by rfl⟩ : syracuseStep 289379 = 434069) B434069
theorem B191203 : Blo 115785 191203 := bstep (se 1 (by rfl) ⟨143402, by rfl⟩ : syracuseStep 191203 = 286805) B286805
theorem B453347 : Blo 115785 453347 := bstep (se 1 (by rfl) ⟨340010, by rfl⟩ : syracuseStep 453347 = 680021) B680021
theorem B223985 : Blo 115785 223985 := bstep (se 2 (by rfl) ⟨83994, by rfl⟩ : syracuseStep 223985 = 167989) B167989
theorem B420785 : Blo 115785 420785 := bstep (se 2 (by rfl) ⟨157794, by rfl⟩ : syracuseStep 420785 = 315589) B315589
theorem B322595 : Blo 115785 322595 := bstep (se 1 (by rfl) ⟨241946, by rfl⟩ : syracuseStep 322595 = 483893) B483893
theorem B224707 : Blo 115785 224707 := bstep (se 1 (by rfl) ⟨168530, by rfl⟩ : syracuseStep 224707 = 337061) B337061
theorem B126419 : Blo 115785 126419 := bstep (se 1 (by rfl) ⟨94814, by rfl⟩ : syracuseStep 126419 = 189629) B189629
theorem B454349 : Blo 115785 454349 := bstep (se 3 (by rfl) ⟨85190, by rfl⟩ : syracuseStep 454349 = 170381) B170381
theorem B323437 : Blo 115785 323437 := bstep (se 3 (by rfl) ⟨60644, by rfl⟩ : syracuseStep 323437 = 121289) B121289
theorem B225155 : Blo 115785 225155 := bstep (se 1 (by rfl) ⟨168866, by rfl⟩ : syracuseStep 225155 = 337733) B337733
theorem B749573 : Blo 115785 749573 := bstep (se 4 (by rfl) ⟨70272, by rfl⟩ : syracuseStep 749573 = 140545) B140545
theorem B225443 : Blo 115785 225443 := bstep (se 1 (by rfl) ⟨169082, by rfl⟩ : syracuseStep 225443 = 338165) B338165
theorem B127171 : Blo 115785 127171 := bstep (se 1 (by rfl) ⟨95378, by rfl⟩ : syracuseStep 127171 = 190757) B190757
theorem B127427 : Blo 115785 127427 := bstep (se 1 (by rfl) ⟨95570, by rfl⟩ : syracuseStep 127427 = 191141) B191141
theorem B848369 : Blo 115785 848369 := bstep (se 2 (by rfl) ⟨318138, by rfl⟩ : syracuseStep 848369 = 636277) B636277
theorem B422513 : Blo 115785 422513 := bstep (se 2 (by rfl) ⟨158442, by rfl⟩ : syracuseStep 422513 = 316885) B316885
theorem B226385 : Blo 115785 226385 := bstep (se 2 (by rfl) ⟨84894, by rfl⟩ : syracuseStep 226385 = 169789) B169789
theorem B193745 : Blo 115785 193745 := bstep (se 2 (by rfl) ⟨72654, by rfl⟩ : syracuseStep 193745 = 145309) B145309
theorem B587249 : Blo 115785 587249 := bstep (se 2 (by rfl) ⟨220218, by rfl⟩ : syracuseStep 587249 = 440437) B440437
theorem B390797 : Blo 115785 390797 := bstep (se 3 (by rfl) ⟨73274, by rfl⟩ : syracuseStep 390797 = 146549) B146549
theorem B390851 : Blo 115785 390851 := bstep (se 1 (by rfl) ⟨293138, by rfl⟩ : syracuseStep 390851 = 586277) B586277
theorem B718733 : Blo 115785 718733 := bstep (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) B269525
theorem B391121 : Blo 115785 391121 := bstep (se 2 (by rfl) ⟨146670, by rfl⟩ : syracuseStep 391121 = 293341) B293341
theorem B227281 : Blo 115785 227281 := bstep (se 2 (by rfl) ⟨85230, by rfl⟩ : syracuseStep 227281 = 170461) B170461
theorem B2291939 : Blo 115785 2291939 := bstep (se 1 (by rfl) ⟨1718954, by rfl⟩ : syracuseStep 2291939 = 3437909) B3437909
theorem B391661 : Blo 115785 391661 := bstep (se 3 (by rfl) ⟨73436, by rfl⟩ : syracuseStep 391661 = 146873) B146873
theorem B391715 : Blo 115785 391715 := bstep (se 1 (by rfl) ⟨293786, by rfl⟩ : syracuseStep 391715 = 587573) B587573
theorem B260657 : Blo 115785 260657 := bstep (se 2 (by rfl) ⟨97746, by rfl⟩ : syracuseStep 260657 = 195493) B195493
theorem B260675 : Blo 115785 260675 := bstep (se 1 (by rfl) ⟨195506, by rfl⟩ : syracuseStep 260675 = 391013) B391013
theorem B359075 : Blo 115785 359075 := bstep (se 1 (by rfl) ⟨269306, by rfl⟩ : syracuseStep 359075 = 538613) B538613
theorem B391985 : Blo 115785 391985 := bstep (se 2 (by rfl) ⟨146994, by rfl⟩ : syracuseStep 391985 = 293989) B293989
theorem B260945 : Blo 115785 260945 := bstep (se 2 (by rfl) ⟨97854, by rfl⟩ : syracuseStep 260945 = 195709) B195709
theorem B260963 : Blo 115785 260963 := bstep (se 1 (by rfl) ⟨195722, by rfl⟩ : syracuseStep 260963 = 391445) B391445
theorem B195473 : Blo 115785 195473 := bstep (se 2 (by rfl) ⟨73302, by rfl⟩ : syracuseStep 195473 = 146605) B146605
theorem B293777 : Blo 115785 293777 := bstep (se 2 (by rfl) ⟨110166, by rfl⟩ : syracuseStep 293777 = 220333) B220333
theorem B588707 : Blo 115785 588707 := bstep (se 1 (by rfl) ⟨441530, by rfl⟩ : syracuseStep 588707 = 883061) B883061
theorem B293827 : Blo 115785 293827 := bstep (se 1 (by rfl) ⟨220370, by rfl⟩ : syracuseStep 293827 = 440741) B440741
theorem B1702853 : Blo 115785 1702853 := bstep (se 4 (by rfl) ⟨159642, by rfl⟩ : syracuseStep 1702853 = 319285) B319285
theorem B195601 : Blo 115785 195601 := bstep (se 2 (by rfl) ⟨73350, by rfl⟩ : syracuseStep 195601 = 146701) B146701
theorem B195635 : Blo 115785 195635 := bstep (se 1 (by rfl) ⟨146726, by rfl⟩ : syracuseStep 195635 = 293453) B293453
theorem B293969 : Blo 115785 293969 := bstep (se 2 (by rfl) ⟨110238, by rfl⟩ : syracuseStep 293969 = 220477) B220477
theorem B261233 : Blo 115785 261233 := bstep (se 2 (by rfl) ⟨97962, by rfl⟩ : syracuseStep 261233 = 195925) B195925
theorem B261251 : Blo 115785 261251 := bstep (se 1 (by rfl) ⟨195938, by rfl⟩ : syracuseStep 261251 = 391877) B391877
theorem B752773 : Blo 115785 752773 := bstep (se 4 (by rfl) ⟨70572, by rfl⟩ : syracuseStep 752773 = 141145) B141145
theorem B195763 : Blo 115785 195763 := bstep (se 1 (by rfl) ⟨146822, by rfl⟩ : syracuseStep 195763 = 293645) B293645
theorem B195905 : Blo 115785 195905 := bstep (se 2 (by rfl) ⟨73464, by rfl⟩ : syracuseStep 195905 = 146929) B146929
theorem B392525 : Blo 115785 392525 := bstep (se 3 (by rfl) ⟨73598, by rfl⟩ : syracuseStep 392525 = 147197) B147197
theorem B130387 : Blo 115785 130387 := bstep (se 1 (by rfl) ⟨97790, by rfl⟩ : syracuseStep 130387 = 195581) B195581
theorem B392579 : Blo 115785 392579 := bstep (se 1 (by rfl) ⟨294434, by rfl⟩ : syracuseStep 392579 = 588869) B588869
theorem B1441165 : Blo 115785 1441165 := bstep (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) B540437
theorem B261521 : Blo 115785 261521 := bstep (se 2 (by rfl) ⟨98070, by rfl⟩ : syracuseStep 261521 = 196141) B196141
theorem B261539 : Blo 115785 261539 := bstep (se 1 (by rfl) ⟨196154, by rfl⟩ : syracuseStep 261539 = 392309) B392309
theorem B196033 : Blo 115785 196033 := bstep (se 2 (by rfl) ⟨73512, by rfl⟩ : syracuseStep 196033 = 147025) B147025
theorem B130531 : Blo 115785 130531 := bstep (se 1 (by rfl) ⟨97898, by rfl⟩ : syracuseStep 130531 = 195797) B195797
theorem B196067 : Blo 115785 196067 := bstep (se 1 (by rfl) ⟨147050, by rfl⟩ : syracuseStep 196067 = 294101) B294101
theorem B196195 : Blo 115785 196195 := bstep (se 1 (by rfl) ⟨147146, by rfl⟩ : syracuseStep 196195 = 294293) B294293
theorem B130675 : Blo 115785 130675 := bstep (se 1 (by rfl) ⟨98006, by rfl⟩ : syracuseStep 130675 = 196013) B196013
theorem B392849 : Blo 115785 392849 := bstep (se 2 (by rfl) ⟨147318, by rfl⟩ : syracuseStep 392849 = 294637) B294637
theorem B261809 : Blo 115785 261809 := bstep (se 2 (by rfl) ⟨98178, by rfl⟩ : syracuseStep 261809 = 196357) B196357
theorem B261827 : Blo 115785 261827 := bstep (se 1 (by rfl) ⟨196370, by rfl⟩ : syracuseStep 261827 = 392741) B392741
theorem B589517 : Blo 115785 589517 := bstep (se 3 (by rfl) ⟨110534, by rfl⟩ : syracuseStep 589517 = 221069) B221069
theorem B196337 : Blo 115785 196337 := bstep (se 2 (by rfl) ⟨73626, by rfl⟩ : syracuseStep 196337 = 147253) B147253
theorem B130819 : Blo 115785 130819 := bstep (se 1 (by rfl) ⟨98114, by rfl⟩ : syracuseStep 130819 = 196229) B196229
theorem B1507085 : Blo 115785 1507085 := bstep (se 3 (by rfl) ⟨282578, by rfl⟩ : syracuseStep 1507085 = 565157) B565157
theorem B327523 : Blo 115785 327523 := bstep (se 1 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 327523 = 491285) B491285
theorem B196465 : Blo 115785 196465 := bstep (se 2 (by rfl) ⟨73674, by rfl⟩ : syracuseStep 196465 = 147349) B147349
theorem B130963 : Blo 115785 130963 := bstep (se 1 (by rfl) ⟨98222, by rfl⟩ : syracuseStep 130963 = 196445) B196445
theorem B196499 : Blo 115785 196499 := bstep (se 1 (by rfl) ⟨147374, by rfl⟩ : syracuseStep 196499 = 294749) B294749
theorem B262097 : Blo 115785 262097 := bstep (se 2 (by rfl) ⟨98286, by rfl⟩ : syracuseStep 262097 = 196573) B196573
theorem B262115 : Blo 115785 262115 := bstep (se 1 (by rfl) ⟨196586, by rfl⟩ : syracuseStep 262115 = 393173) B393173
theorem B589841 : Blo 115785 589841 := bstep (se 2 (by rfl) ⟨221190, by rfl⟩ : syracuseStep 589841 = 442381) B442381
theorem B262169 : Blo 115785 262169 := bstep (se 2 (by rfl) ⟨98313, by rfl⟩ : syracuseStep 262169 = 196627) B196627
theorem B393281 : Blo 115785 393281 := bstep (se 2 (by rfl) ⟨147480, by rfl⟩ : syracuseStep 393281 = 294961) B294961
theorem B1998917 : Blo 115785 1998917 := bstep (se 4 (by rfl) ⟨187398, by rfl⟩ : syracuseStep 1998917 = 374797) B374797
theorem B131179 : Blo 115785 131179 := bstep (se 1 (by rfl) ⟨98384, by rfl⟩ : syracuseStep 131179 = 196769) B196769
theorem B262259 : Blo 115785 262259 := bstep (se 1 (by rfl) ⟨196694, by rfl⟩ : syracuseStep 262259 = 393389) B393389
theorem B262295 : Blo 115785 262295 := bstep (se 1 (by rfl) ⟨196721, by rfl⟩ : syracuseStep 262295 = 393443) B393443
theorem B590003 : Blo 115785 590003 := bstep (se 1 (by rfl) ⟨442502, by rfl⟩ : syracuseStep 590003 = 885005) B885005
theorem B196823 : Blo 115785 196823 := bstep (se 1 (by rfl) ⟨147617, by rfl⟩ : syracuseStep 196823 = 295235) B295235
theorem B131287 : Blo 115785 131287 := bstep (se 1 (by rfl) ⟨98465, by rfl⟩ : syracuseStep 131287 = 196931) B196931
theorem B262475 : Blo 115785 262475 := bstep (se 1 (by rfl) ⟨196856, by rfl⟩ : syracuseStep 262475 = 393713) B393713
theorem B196951 : Blo 115785 196951 := bstep (se 1 (by rfl) ⟨147713, by rfl⟩ : syracuseStep 196951 = 295427) B295427
theorem B262529 : Blo 115785 262529 := bstep (se 2 (by rfl) ⟨98448, by rfl⟩ : syracuseStep 262529 = 196897) B196897
theorem B131467 : Blo 115785 131467 := bstep (se 1 (by rfl) ⟨98600, by rfl⟩ : syracuseStep 131467 = 197201) B197201
theorem B3277205 : Blo 115785 3277205 := bstep (se 6 (by rfl) ⟨76809, by rfl⟩ : syracuseStep 3277205 = 153619) B153619
theorem B131575 : Blo 115785 131575 := bstep (se 1 (by rfl) ⟨98681, by rfl⟩ : syracuseStep 131575 = 197363) B197363
theorem B295447 : Blo 115785 295447 := bstep (se 1 (by rfl) ⟨221585, by rfl⟩ : syracuseStep 295447 = 443171) B443171
theorem B262745 : Blo 115785 262745 := bstep (se 2 (by rfl) ⟨98529, by rfl⟩ : syracuseStep 262745 = 197059) B197059
theorem B393821 : Blo 115785 393821 := bstep (se 3 (by rfl) ⟨73841, by rfl⟩ : syracuseStep 393821 = 147683) B147683
theorem B131755 : Blo 115785 131755 := bstep (se 1 (by rfl) ⟨98816, by rfl⟩ : syracuseStep 131755 = 197633) B197633
theorem B262835 : Blo 115785 262835 := bstep (se 1 (by rfl) ⟨197126, by rfl⟩ : syracuseStep 262835 = 394253) B394253
theorem B262871 : Blo 115785 262871 := bstep (se 1 (by rfl) ⟨197153, by rfl⟩ : syracuseStep 262871 = 394307) B394307
theorem B131863 : Blo 115785 131863 := bstep (se 1 (by rfl) ⟨98897, by rfl⟩ : syracuseStep 131863 = 197795) B197795
theorem B263051 : Blo 115785 263051 := bstep (se 1 (by rfl) ⟨197288, by rfl⟩ : syracuseStep 263051 = 394577) B394577
theorem B263105 : Blo 115785 263105 := bstep (se 2 (by rfl) ⟨98664, by rfl⟩ : syracuseStep 263105 = 197329) B197329
theorem B295883 : Blo 115785 295883 := bstep (se 1 (by rfl) ⟨221912, by rfl⟩ : syracuseStep 295883 = 443825) B443825
theorem B197579 : Blo 115785 197579 := bstep (se 1 (by rfl) ⟨148184, by rfl⟩ : syracuseStep 197579 = 296369) B296369
theorem B132043 : Blo 115785 132043 := bstep (se 1 (by rfl) ⟨99032, by rfl⟩ : syracuseStep 132043 = 198065) B198065
theorem B132151 : Blo 115785 132151 := bstep (se 1 (by rfl) ⟨99113, by rfl⟩ : syracuseStep 132151 = 198227) B198227
theorem B197707 : Blo 115785 197707 := bstep (se 1 (by rfl) ⟨148280, by rfl⟩ : syracuseStep 197707 = 296561) B296561
theorem B263321 : Blo 115785 263321 := bstep (se 2 (by rfl) ⟨98745, by rfl⟩ : syracuseStep 263321 = 197491) B197491
theorem B885977 : Blo 115785 885977 := bstep (se 2 (by rfl) ⟨332241, by rfl⟩ : syracuseStep 885977 = 664483) B664483
theorem B197849 : Blo 115785 197849 := bstep (se 2 (by rfl) ⟨74193, by rfl⟩ : syracuseStep 197849 = 148387) B148387
theorem B132331 : Blo 115785 132331 := bstep (se 1 (by rfl) ⟨99248, by rfl⟩ : syracuseStep 132331 = 198497) B198497
theorem B263411 : Blo 115785 263411 := bstep (se 1 (by rfl) ⟨197558, by rfl⟩ : syracuseStep 263411 = 395117) B395117
theorem B558353 : Blo 115785 558353 := bstep (se 2 (by rfl) ⟨209382, by rfl⟩ : syracuseStep 558353 = 418765) B418765
theorem B263447 : Blo 115785 263447 := bstep (se 1 (by rfl) ⟨197585, by rfl⟩ : syracuseStep 263447 = 395171) B395171
theorem B296257 : Blo 115785 296257 := bstep (se 2 (by rfl) ⟨111096, by rfl⟩ : syracuseStep 296257 = 222193) B222193
theorem B132427 : Blo 115785 132427 := bstep (se 1 (by rfl) ⟨99320, by rfl⟩ : syracuseStep 132427 = 198641) B198641
theorem B132439 : Blo 115785 132439 := bstep (se 1 (by rfl) ⟨99329, by rfl⟩ : syracuseStep 132439 = 198659) B198659
theorem B197977 : Blo 115785 197977 := bstep (se 2 (by rfl) ⟨74241, by rfl⟩ : syracuseStep 197977 = 148483) B148483
theorem B263627 : Blo 115785 263627 := bstep (se 1 (by rfl) ⟨197720, by rfl⟩ : syracuseStep 263627 = 395441) B395441
theorem B361945 : Blo 115785 361945 := bstep (se 2 (by rfl) ⟨135729, by rfl⟩ : syracuseStep 361945 = 271459) B271459
theorem B263681 : Blo 115785 263681 := bstep (se 2 (by rfl) ⟨98880, by rfl⟩ : syracuseStep 263681 = 197761) B197761
theorem B132619 : Blo 115785 132619 := bstep (se 1 (by rfl) ⟨99464, by rfl⟩ : syracuseStep 132619 = 198929) B198929
theorem B132727 : Blo 115785 132727 := bstep (se 1 (by rfl) ⟨99545, by rfl⟩ : syracuseStep 132727 = 199091) B199091
theorem B394955 : Blo 115785 394955 := bstep (se 1 (by rfl) ⟨296216, by rfl⟩ : syracuseStep 394955 = 592433) B592433
theorem B263897 : Blo 115785 263897 := bstep (se 2 (by rfl) ⟨98961, by rfl⟩ : syracuseStep 263897 = 197923) B197923
theorem B132907 : Blo 115785 132907 := bstep (se 1 (by rfl) ⟨99680, by rfl⟩ : syracuseStep 132907 = 199361) B199361
theorem B263987 : Blo 115785 263987 := bstep (se 1 (by rfl) ⟨197990, by rfl⟩ : syracuseStep 263987 = 395981) B395981
theorem B264023 : Blo 115785 264023 := bstep (se 1 (by rfl) ⟨198017, by rfl⟩ : syracuseStep 264023 = 396035) B396035
theorem B722819 : Blo 115785 722819 := bstep (se 1 (by rfl) ⟨542114, by rfl⟩ : syracuseStep 722819 = 1084229) B1084229
theorem B296855 : Blo 115785 296855 := bstep (se 1 (by rfl) ⟨222641, by rfl⟩ : syracuseStep 296855 = 445283) B445283
theorem B198551 : Blo 115785 198551 := bstep (se 1 (by rfl) ⟨148913, by rfl⟩ : syracuseStep 198551 = 297827) B297827
theorem B133015 : Blo 115785 133015 := bstep (se 1 (by rfl) ⟨99761, by rfl⟩ : syracuseStep 133015 = 199523) B199523
theorem B395225 : Blo 115785 395225 := bstep (se 2 (by rfl) ⟨148209, by rfl⟩ : syracuseStep 395225 = 296419) B296419
theorem B264203 : Blo 115785 264203 := bstep (se 1 (by rfl) ⟨198152, by rfl⟩ : syracuseStep 264203 = 396305) B396305
theorem B198679 : Blo 115785 198679 := bstep (se 1 (by rfl) ⟨149009, by rfl⟩ : syracuseStep 198679 = 298019) B298019
theorem B264257 : Blo 115785 264257 := bstep (se 2 (by rfl) ⟨99096, by rfl⟩ : syracuseStep 264257 = 198193) B198193
theorem B591947 : Blo 115785 591947 := bstep (se 1 (by rfl) ⟨443960, by rfl⟩ : syracuseStep 591947 = 887921) B887921
theorem B133195 : Blo 115785 133195 := bstep (se 1 (by rfl) ⟨99896, by rfl⟩ : syracuseStep 133195 = 199793) B199793
theorem B362675 : Blo 115785 362675 := bstep (se 1 (by rfl) ⟨272006, by rfl⟩ : syracuseStep 362675 = 544013) B544013
theorem B133303 : Blo 115785 133303 := bstep (se 1 (by rfl) ⟨99977, by rfl⟩ : syracuseStep 133303 = 199955) B199955
theorem B264473 : Blo 115785 264473 := bstep (se 2 (by rfl) ⟨99177, by rfl⟩ : syracuseStep 264473 = 198355) B198355
theorem B919873 : Blo 115785 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B133483 : Blo 115785 133483 := bstep (se 1 (by rfl) ⟨100112, by rfl⟩ : syracuseStep 133483 = 200225) B200225
theorem B5048689 : Blo 115785 5048689 := bstep (se 2 (by rfl) ⟨1893258, by rfl⟩ : syracuseStep 5048689 = 3786517) B3786517
theorem B264563 : Blo 115785 264563 := bstep (se 1 (by rfl) ⟨198422, by rfl⟩ : syracuseStep 264563 = 396845) B396845
theorem B3869045 : Blo 115785 3869045 := bstep (se 5 (by rfl) ⟨181361, by rfl⟩ : syracuseStep 3869045 = 362723) B362723
theorem B264599 : Blo 115785 264599 := bstep (se 1 (by rfl) ⟨198449, by rfl⟩ : syracuseStep 264599 = 396899) B396899
theorem B133591 : Blo 115785 133591 := bstep (se 1 (by rfl) ⟨100193, by rfl⟩ : syracuseStep 133591 = 200387) B200387
theorem B264779 : Blo 115785 264779 := bstep (se 1 (by rfl) ⟨198584, by rfl⟩ : syracuseStep 264779 = 397169) B397169
theorem B4983389 : Blo 115785 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B264833 : Blo 115785 264833 := bstep (se 2 (by rfl) ⟨99312, by rfl⟩ : syracuseStep 264833 = 198625) B198625
theorem B133771 : Blo 115785 133771 := bstep (se 1 (by rfl) ⟨100328, by rfl⟩ : syracuseStep 133771 = 200657) B200657
theorem B199307 : Blo 115785 199307 := bstep (se 1 (by rfl) ⟨149480, by rfl⟩ : syracuseStep 199307 = 298961) B298961
theorem B297623 : Blo 115785 297623 := bstep (se 1 (by rfl) ⟨223217, by rfl⟩ : syracuseStep 297623 = 446435) B446435
theorem B395927 : Blo 115785 395927 := bstep (se 1 (by rfl) ⟨296945, by rfl⟩ : syracuseStep 395927 = 593891) B593891
theorem B330419 : Blo 115785 330419 := bstep (se 1 (by rfl) ⟨247814, by rfl⟩ : syracuseStep 330419 = 495629) B495629
theorem B297665 : Blo 115785 297665 := bstep (se 2 (by rfl) ⟨111624, by rfl⟩ : syracuseStep 297665 = 223249) B223249
theorem B330443 : Blo 115785 330443 := bstep (se 1 (by rfl) ⟨247832, by rfl⟩ : syracuseStep 330443 = 495665) B495665
theorem B133879 : Blo 115785 133879 := bstep (se 1 (by rfl) ⟨100409, by rfl⟩ : syracuseStep 133879 = 200819) B200819
theorem B199435 : Blo 115785 199435 := bstep (se 1 (by rfl) ⟨149576, by rfl⟩ : syracuseStep 199435 = 299153) B299153
theorem B265049 : Blo 115785 265049 := bstep (se 2 (by rfl) ⟨99393, by rfl⟩ : syracuseStep 265049 = 198787) B198787
theorem B199577 : Blo 115785 199577 := bstep (se 2 (by rfl) ⟨74841, by rfl⟩ : syracuseStep 199577 = 149683) B149683
theorem B134059 : Blo 115785 134059 := bstep (se 1 (by rfl) ⟨100544, by rfl⟩ : syracuseStep 134059 = 201089) B201089
theorem B265139 : Blo 115785 265139 := bstep (se 1 (by rfl) ⟨198854, by rfl⟩ : syracuseStep 265139 = 397709) B397709
theorem B265175 : Blo 115785 265175 := bstep (se 1 (by rfl) ⟨198881, by rfl⟩ : syracuseStep 265175 = 397763) B397763
theorem B166873 : Blo 115785 166873 := bstep (se 2 (by rfl) ⟨62577, by rfl⟩ : syracuseStep 166873 = 125155) B125155
theorem B134167 : Blo 115785 134167 := bstep (se 1 (by rfl) ⟨100625, by rfl⟩ : syracuseStep 134167 = 201251) B201251
theorem B199705 : Blo 115785 199705 := bstep (se 2 (by rfl) ⟨74889, by rfl⟩ : syracuseStep 199705 = 149779) B149779
theorem B494657 : Blo 115785 494657 := bstep (se 2 (by rfl) ⟨185496, by rfl⟩ : syracuseStep 494657 = 370993) B370993
theorem B429131 : Blo 115785 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B265355 : Blo 115785 265355 := bstep (se 1 (by rfl) ⟨199016, by rfl⟩ : syracuseStep 265355 = 398033) B398033
theorem B396467 : Blo 115785 396467 := bstep (se 1 (by rfl) ⟨297350, by rfl⟩ : syracuseStep 396467 = 594701) B594701
theorem B265409 : Blo 115785 265409 := bstep (se 2 (by rfl) ⟨99528, by rfl⟩ : syracuseStep 265409 = 199057) B199057
theorem B134347 : Blo 115785 134347 := bstep (se 1 (by rfl) ⟨100760, by rfl⟩ : syracuseStep 134347 = 201521) B201521
theorem B298201 : Blo 115785 298201 := bstep (se 2 (by rfl) ⟨111825, by rfl⟩ : syracuseStep 298201 = 223651) B223651
theorem B134455 : Blo 115785 134455 := bstep (se 1 (by rfl) ⟨100841, by rfl⟩ : syracuseStep 134455 = 201683) B201683
theorem B265625 : Blo 115785 265625 := bstep (se 2 (by rfl) ⟨99609, by rfl⟩ : syracuseStep 265625 = 199219) B199219
theorem B396737 : Blo 115785 396737 := bstep (se 2 (by rfl) ⟨148776, by rfl⟩ : syracuseStep 396737 = 297553) B297553
theorem B331229 : Blo 115785 331229 := bstep (se 3 (by rfl) ⟨62105, by rfl⟩ : syracuseStep 331229 = 124211) B124211
theorem B134635 : Blo 115785 134635 := bstep (se 1 (by rfl) ⟨100976, by rfl⟩ : syracuseStep 134635 = 201953) B201953
theorem B265715 : Blo 115785 265715 := bstep (se 1 (by rfl) ⟨199286, by rfl⟩ : syracuseStep 265715 = 398573) B398573
theorem B265751 : Blo 115785 265751 := bstep (se 1 (by rfl) ⟨199313, by rfl⟩ : syracuseStep 265751 = 398627) B398627
theorem B200279 : Blo 115785 200279 := bstep (se 1 (by rfl) ⟨150209, by rfl⟩ : syracuseStep 200279 = 300419) B300419
theorem B134743 : Blo 115785 134743 := bstep (se 1 (by rfl) ⟨101057, by rfl⟩ : syracuseStep 134743 = 202115) B202115
theorem B265931 : Blo 115785 265931 := bstep (se 1 (by rfl) ⟨199448, by rfl⟩ : syracuseStep 265931 = 398897) B398897
theorem B200407 : Blo 115785 200407 := bstep (se 1 (by rfl) ⟨150305, by rfl⟩ : syracuseStep 200407 = 300611) B300611
theorem B2100977 : Blo 115785 2100977 := bstep (se 2 (by rfl) ⟨787866, by rfl⟩ : syracuseStep 2100977 = 1575733) B1575733
theorem B265985 : Blo 115785 265985 := bstep (se 2 (by rfl) ⟨99744, by rfl⟩ : syracuseStep 265985 = 199489) B199489
theorem B593729 : Blo 115785 593729 := bstep (se 2 (by rfl) ⟨222648, by rfl⟩ : syracuseStep 593729 = 445297) B445297
theorem B266201 : Blo 115785 266201 := bstep (se 2 (by rfl) ⟨99825, by rfl⟩ : syracuseStep 266201 = 199651) B199651
theorem B397277 : Blo 115785 397277 := bstep (se 3 (by rfl) ⟨74489, by rfl⟩ : syracuseStep 397277 = 148979) B148979
theorem B266291 : Blo 115785 266291 := bstep (se 1 (by rfl) ⟨199718, by rfl⟩ : syracuseStep 266291 = 399437) B399437
theorem B266327 : Blo 115785 266327 := bstep (se 1 (by rfl) ⟨199745, by rfl⟩ : syracuseStep 266327 = 399491) B399491
theorem B266507 : Blo 115785 266507 := bstep (se 1 (by rfl) ⟨199880, by rfl⟩ : syracuseStep 266507 = 399761) B399761
theorem B299315 : Blo 115785 299315 := bstep (se 1 (by rfl) ⟨224486, by rfl⟩ : syracuseStep 299315 = 448973) B448973
theorem B266561 : Blo 115785 266561 := bstep (se 2 (by rfl) ⟨99960, by rfl⟩ : syracuseStep 266561 = 199921) B199921
theorem B201035 : Blo 115785 201035 := bstep (se 1 (by rfl) ⟨150776, by rfl⟩ : syracuseStep 201035 = 301553) B301553
theorem B1020235 : Blo 115785 1020235 := bstep (se 1 (by rfl) ⟨765176, by rfl⟩ : syracuseStep 1020235 = 1530353) B1530353
theorem B168331 : Blo 115785 168331 := bstep (se 1 (by rfl) ⟨126248, by rfl⟩ : syracuseStep 168331 = 252497) B252497
theorem B201163 : Blo 115785 201163 := bstep (se 1 (by rfl) ⟨150872, by rfl⟩ : syracuseStep 201163 = 301745) B301745
theorem B266777 : Blo 115785 266777 := bstep (se 2 (by rfl) ⟨100041, by rfl⟩ : syracuseStep 266777 = 200083) B200083
theorem B889379 : Blo 115785 889379 := bstep (se 1 (by rfl) ⟨667034, by rfl⟩ : syracuseStep 889379 = 1334069) B1334069
theorem B430643 : Blo 115785 430643 := bstep (se 1 (by rfl) ⟨322982, by rfl⟩ : syracuseStep 430643 = 645965) B645965
theorem B299609 : Blo 115785 299609 := bstep (se 2 (by rfl) ⟨112353, by rfl⟩ : syracuseStep 299609 = 224707) B224707
theorem B201305 : Blo 115785 201305 := bstep (se 2 (by rfl) ⟨75489, by rfl⟩ : syracuseStep 201305 = 150979) B150979
theorem B1151581 : Blo 115785 1151581 := bstep (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) B431843
theorem B1020509 : Blo 115785 1020509 := bstep (se 3 (by rfl) ⟨191345, by rfl⟩ : syracuseStep 1020509 = 382691) B382691
theorem B266867 : Blo 115785 266867 := bstep (se 1 (by rfl) ⟨200150, by rfl⟩ : syracuseStep 266867 = 400301) B400301
theorem B266903 : Blo 115785 266903 := bstep (se 1 (by rfl) ⟨200177, by rfl⟩ : syracuseStep 266903 = 400355) B400355
theorem B201433 : Blo 115785 201433 := bstep (se 2 (by rfl) ⟨75537, by rfl⟩ : syracuseStep 201433 = 151075) B151075
theorem B267083 : Blo 115785 267083 := bstep (se 1 (by rfl) ⟨200312, by rfl⟩ : syracuseStep 267083 = 400625) B400625
theorem B267137 : Blo 115785 267137 := bstep (se 2 (by rfl) ⟨100176, by rfl⟩ : syracuseStep 267137 = 200353) B200353
theorem B398411 : Blo 115785 398411 := bstep (se 1 (by rfl) ⟨298808, by rfl⟩ : syracuseStep 398411 = 597617) B597617
theorem B267353 : Blo 115785 267353 := bstep (se 2 (by rfl) ⟨100257, by rfl⟩ : syracuseStep 267353 = 200515) B200515
theorem B431249 : Blo 115785 431249 := bstep (se 2 (by rfl) ⟨161718, by rfl⟩ : syracuseStep 431249 = 323437) B323437
theorem B267443 : Blo 115785 267443 := bstep (se 1 (by rfl) ⟨200582, by rfl⟩ : syracuseStep 267443 = 401165) B401165
theorem B365771 : Blo 115785 365771 := bstep (se 1 (by rfl) ⟨274328, by rfl⟩ : syracuseStep 365771 = 548657) B548657
theorem B1021133 : Blo 115785 1021133 := bstep (se 3 (by rfl) ⟨191462, by rfl⟩ : syracuseStep 1021133 = 382925) B382925
theorem B267479 : Blo 115785 267479 := bstep (se 1 (by rfl) ⟨200609, by rfl⟩ : syracuseStep 267479 = 401219) B401219
theorem B333017 : Blo 115785 333017 := bstep (se 2 (by rfl) ⟨124881, by rfl⟩ : syracuseStep 333017 = 249763) B249763
theorem B202007 : Blo 115785 202007 := bstep (se 1 (by rfl) ⟨151505, by rfl⟩ : syracuseStep 202007 = 303011) B303011
theorem B398681 : Blo 115785 398681 := bstep (se 2 (by rfl) ⟨149505, by rfl⟩ : syracuseStep 398681 = 299011) B299011
theorem B267659 : Blo 115785 267659 := bstep (se 1 (by rfl) ⟨200744, by rfl⟩ : syracuseStep 267659 = 401489) B401489
theorem B202135 : Blo 115785 202135 := bstep (se 1 (by rfl) ⟨151601, by rfl⟩ : syracuseStep 202135 = 303203) B303203
theorem B267713 : Blo 115785 267713 := bstep (se 2 (by rfl) ⟨100392, by rfl⟩ : syracuseStep 267713 = 200785) B200785
theorem B497117 : Blo 115785 497117 := bstep (se 3 (by rfl) ⟨93209, by rfl⟩ : syracuseStep 497117 = 186419) B186419
theorem B333335 : Blo 115785 333335 := bstep (se 1 (by rfl) ⟨250001, by rfl⟩ : syracuseStep 333335 = 500003) B500003
theorem B661067 : Blo 115785 661067 := bstep (se 1 (by rfl) ⟨495800, by rfl⟩ : syracuseStep 661067 = 991601) B991601
theorem B169561 : Blo 115785 169561 := bstep (se 2 (by rfl) ⟨63585, by rfl⟩ : syracuseStep 169561 = 127171) B127171
theorem B1021571 : Blo 115785 1021571 := bstep (se 1 (by rfl) ⟨766178, by rfl⟩ : syracuseStep 1021571 = 1532357) B1532357
theorem B267929 : Blo 115785 267929 := bstep (se 2 (by rfl) ⟨100473, by rfl⟩ : syracuseStep 267929 = 200947) B200947
theorem B595673 : Blo 115785 595673 := bstep (se 2 (by rfl) ⟨223377, by rfl⟩ : syracuseStep 595673 = 446755) B446755
theorem B268019 : Blo 115785 268019 := bstep (se 1 (by rfl) ⟨201014, by rfl⟩ : syracuseStep 268019 = 402029) B402029
theorem B268055 : Blo 115785 268055 := bstep (se 1 (by rfl) ⟨201041, by rfl⟩ : syracuseStep 268055 = 402083) B402083
theorem B202583 : Blo 115785 202583 := bstep (se 1 (by rfl) ⟨151937, by rfl⟩ : syracuseStep 202583 = 303875) B303875
theorem B268235 : Blo 115785 268235 := bstep (se 1 (by rfl) ⟨201176, by rfl⟩ : syracuseStep 268235 = 402353) B402353
theorem B268289 : Blo 115785 268289 := bstep (se 2 (by rfl) ⟨100608, by rfl⟩ : syracuseStep 268289 = 201217) B201217
theorem B399383 : Blo 115785 399383 := bstep (se 1 (by rfl) ⟨299537, by rfl⟩ : syracuseStep 399383 = 599075) B599075
theorem B301259 : Blo 115785 301259 := bstep (se 1 (by rfl) ⟨225944, by rfl⟩ : syracuseStep 301259 = 451889) B451889
theorem B268505 : Blo 115785 268505 := bstep (se 2 (by rfl) ⟨100689, by rfl⟩ : syracuseStep 268505 = 201379) B201379
theorem B399581 : Blo 115785 399581 := bstep (se 3 (by rfl) ⟨74921, by rfl⟩ : syracuseStep 399581 = 149843) B149843
theorem B203033 : Blo 115785 203033 := bstep (se 2 (by rfl) ⟨76137, by rfl⟩ : syracuseStep 203033 = 152275) B152275
theorem B268595 : Blo 115785 268595 := bstep (se 1 (by rfl) ⟨201446, by rfl⟩ : syracuseStep 268595 = 402893) B402893
theorem B334145 : Blo 115785 334145 := bstep (se 2 (by rfl) ⟨125304, by rfl⟩ : syracuseStep 334145 = 250609) B250609
theorem B268631 : Blo 115785 268631 := bstep (se 1 (by rfl) ⟨201473, by rfl⟩ : syracuseStep 268631 = 402947) B402947
theorem B989617 : Blo 115785 989617 := bstep (se 2 (by rfl) ⟨371106, by rfl⟩ : syracuseStep 989617 = 742213) B742213
theorem B268811 : Blo 115785 268811 := bstep (se 1 (by rfl) ⟨201608, by rfl⟩ : syracuseStep 268811 = 403217) B403217
theorem B399923 : Blo 115785 399923 := bstep (se 1 (by rfl) ⟨299942, by rfl⟩ : syracuseStep 399923 = 599885) B599885
theorem B268865 : Blo 115785 268865 := bstep (se 2 (by rfl) ⟨100824, by rfl⟩ : syracuseStep 268865 = 201649) B201649
theorem B269081 : Blo 115785 269081 := bstep (se 2 (by rfl) ⟨100905, by rfl⟩ : syracuseStep 269081 = 201811) B201811
theorem B400193 : Blo 115785 400193 := bstep (se 2 (by rfl) ⟨150072, by rfl⟩ : syracuseStep 400193 = 300145) B300145
theorem B269171 : Blo 115785 269171 := bstep (se 1 (by rfl) ⟨201878, by rfl⟩ : syracuseStep 269171 = 403757) B403757
theorem B269207 : Blo 115785 269207 := bstep (se 1 (by rfl) ⟨201905, by rfl⟩ : syracuseStep 269207 = 403811) B403811
theorem B859211 : Blo 115785 859211 := bstep (se 1 (by rfl) ⟨644408, by rfl⟩ : syracuseStep 859211 = 1288817) B1288817
theorem B269387 : Blo 115785 269387 := bstep (se 1 (by rfl) ⟨202040, by rfl⟩ : syracuseStep 269387 = 404081) B404081
theorem B466013 : Blo 115785 466013 := bstep (se 3 (by rfl) ⟨87377, by rfl⟩ : syracuseStep 466013 = 174755) B174755
theorem B269441 : Blo 115785 269441 := bstep (se 2 (by rfl) ⟨101040, by rfl⟩ : syracuseStep 269441 = 202081) B202081
theorem B302231 : Blo 115785 302231 := bstep (se 1 (by rfl) ⟨226673, by rfl⟩ : syracuseStep 302231 = 453347) B453347
theorem B597293 : Blo 115785 597293 := bstep (se 3 (by rfl) ⟨111992, by rfl⟩ : syracuseStep 597293 = 223985) B223985
theorem B400733 : Blo 115785 400733 := bstep (se 3 (by rfl) ⟨75137, by rfl⟩ : syracuseStep 400733 = 150275) B150275
theorem B302899 : Blo 115785 302899 := bstep (se 1 (by rfl) ⟨227174, by rfl⟩ : syracuseStep 302899 = 454349) B454349
theorem B303041 : Blo 115785 303041 := bstep (se 2 (by rfl) ⟨113640, by rfl⟩ : syracuseStep 303041 = 227281) B227281
theorem B335819 : Blo 115785 335819 := bstep (se 1 (by rfl) ⟨251864, by rfl⟩ : syracuseStep 335819 = 503729) B503729
theorem B499715 : Blo 115785 499715 := bstep (se 1 (by rfl) ⟨374786, by rfl⟩ : syracuseStep 499715 = 749573) B749573
theorem B5218445 : Blo 115785 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B565579 : Blo 115785 565579 := bstep (se 1 (by rfl) ⟨424184, by rfl⟩ : syracuseStep 565579 = 848369) B848369
theorem B401867 : Blo 115785 401867 := bstep (se 1 (by rfl) ⟨301400, by rfl⟩ : syracuseStep 401867 = 602801) B602801
theorem B139915 : Blo 115785 139915 := bstep (se 1 (by rfl) ⟨104936, by rfl⟩ : syracuseStep 139915 = 209873) B209873
theorem B402137 : Blo 115785 402137 := bstep (se 2 (by rfl) ⟨150801, by rfl⟩ : syracuseStep 402137 = 301603) B301603
theorem B337117 : Blo 115785 337117 := bstep (se 3 (by rfl) ⟨63209, by rfl⟩ : syracuseStep 337117 = 126419) B126419
theorem B763181 : Blo 115785 763181 := bstep (se 3 (by rfl) ⟨143096, by rfl⟩ : syracuseStep 763181 = 286193) B286193
theorem B3417461 : Blo 115785 3417461 := bstep (se 5 (by rfl) ⟨160193, by rfl⟩ : syracuseStep 3417461 = 320387) B320387
theorem B402839 : Blo 115785 402839 := bstep (se 1 (by rfl) ⟨302129, by rfl⟩ : syracuseStep 402839 = 604259) B604259
theorem B206233 : Blo 115785 206233 := bstep (se 2 (by rfl) ⟨77337, by rfl⟩ : syracuseStep 206233 = 154675) B154675
theorem B337459 : Blo 115785 337459 := bstep (se 1 (by rfl) ⟨253094, by rfl⟩ : syracuseStep 337459 = 506189) B506189
theorem B173771 : Blo 115785 173771 := bstep (se 1 (by rfl) ⟨130328, by rfl⟩ : syracuseStep 173771 = 260657) B260657
theorem B173783 : Blo 115785 173783 := bstep (se 1 (by rfl) ⟨130337, by rfl⟩ : syracuseStep 173783 = 260675) B260675
theorem B894725 : Blo 115785 894725 := bstep (se 4 (by rfl) ⟨83880, by rfl⟩ : syracuseStep 894725 = 167761) B167761
theorem B239383 : Blo 115785 239383 := bstep (se 1 (by rfl) ⟨179537, by rfl⟩ : syracuseStep 239383 = 359075) B359075
theorem B173849 : Blo 115785 173849 := bstep (se 2 (by rfl) ⟨65193, by rfl⟩ : syracuseStep 173849 = 130387) B130387
theorem B173963 : Blo 115785 173963 := bstep (se 1 (by rfl) ⟨130472, by rfl⟩ : syracuseStep 173963 = 260945) B260945
theorem B173975 : Blo 115785 173975 := bstep (se 1 (by rfl) ⟨130481, by rfl⟩ : syracuseStep 173975 = 260963) B260963
theorem B403379 : Blo 115785 403379 := bstep (se 1 (by rfl) ⟨302534, by rfl⟩ : syracuseStep 403379 = 605069) B605069
theorem B174041 : Blo 115785 174041 := bstep (se 2 (by rfl) ⟨65265, by rfl⟩ : syracuseStep 174041 = 130531) B130531
theorem B174155 : Blo 115785 174155 := bstep (se 1 (by rfl) ⟨130616, by rfl⟩ : syracuseStep 174155 = 261233) B261233
theorem B174167 : Blo 115785 174167 := bstep (se 1 (by rfl) ⟨130625, by rfl⟩ : syracuseStep 174167 = 261251) B261251
theorem B174233 : Blo 115785 174233 := bstep (se 2 (by rfl) ⟨65337, by rfl⟩ : syracuseStep 174233 = 130675) B130675
theorem B403649 : Blo 115785 403649 := bstep (se 2 (by rfl) ⟨151368, by rfl⟩ : syracuseStep 403649 = 302737) B302737
theorem B174347 : Blo 115785 174347 := bstep (se 1 (by rfl) ⟨130760, by rfl⟩ : syracuseStep 174347 = 261521) B261521
theorem B174359 : Blo 115785 174359 := bstep (se 1 (by rfl) ⟨130769, by rfl⟩ : syracuseStep 174359 = 261539) B261539
theorem B272663 : Blo 115785 272663 := bstep (se 1 (by rfl) ⟨204497, by rfl⟩ : syracuseStep 272663 = 408995) B408995
theorem B174425 : Blo 115785 174425 := bstep (se 2 (by rfl) ⟨65409, by rfl⟩ : syracuseStep 174425 = 130819) B130819
theorem B174539 : Blo 115785 174539 := bstep (se 1 (by rfl) ⟨130904, by rfl⟩ : syracuseStep 174539 = 261809) B261809
theorem B174551 : Blo 115785 174551 := bstep (se 1 (by rfl) ⟨130913, by rfl⟩ : syracuseStep 174551 = 261827) B261827
theorem B240089 : Blo 115785 240089 := bstep (se 2 (by rfl) ⟨90033, by rfl⟩ : syracuseStep 240089 = 180067) B180067
theorem B338393 : Blo 115785 338393 := bstep (se 2 (by rfl) ⟨126897, by rfl⟩ : syracuseStep 338393 = 253795) B253795
theorem B436697 : Blo 115785 436697 := bstep (se 2 (by rfl) ⟨163761, by rfl⟩ : syracuseStep 436697 = 327523) B327523
theorem B174617 : Blo 115785 174617 := bstep (se 2 (by rfl) ⟨65481, by rfl⟩ : syracuseStep 174617 = 130963) B130963
theorem B174731 : Blo 115785 174731 := bstep (se 1 (by rfl) ⟨131048, by rfl⟩ : syracuseStep 174731 = 262097) B262097
theorem B174743 : Blo 115785 174743 := bstep (se 1 (by rfl) ⟨131057, by rfl⟩ : syracuseStep 174743 = 262115) B262115
theorem B174809 : Blo 115785 174809 := bstep (se 2 (by rfl) ⟨65553, by rfl⟩ : syracuseStep 174809 = 131107) B131107
theorem B404189 : Blo 115785 404189 := bstep (se 3 (by rfl) ⟨75785, by rfl⟩ : syracuseStep 404189 = 151571) B151571
theorem B174923 : Blo 115785 174923 := bstep (se 1 (by rfl) ⟨131192, by rfl⟩ : syracuseStep 174923 = 262385) B262385
theorem B174935 : Blo 115785 174935 := bstep (se 1 (by rfl) ⟨131201, by rfl⟩ : syracuseStep 174935 = 262403) B262403
theorem B175001 : Blo 115785 175001 := bstep (se 2 (by rfl) ⟨65625, by rfl⟩ : syracuseStep 175001 = 131251) B131251
theorem B994265 : Blo 115785 994265 := bstep (se 2 (by rfl) ⟨372849, by rfl⟩ : syracuseStep 994265 = 745699) B745699
theorem B175115 : Blo 115785 175115 := bstep (se 1 (by rfl) ⟨131336, by rfl⟩ : syracuseStep 175115 = 262673) B262673
theorem B175127 : Blo 115785 175127 := bstep (se 1 (by rfl) ⟨131345, by rfl⟩ : syracuseStep 175127 = 262691) B262691
theorem B175193 : Blo 115785 175193 := bstep (se 2 (by rfl) ⟨65697, by rfl⟩ : syracuseStep 175193 = 131395) B131395
theorem B601181 : Blo 115785 601181 := bstep (se 3 (by rfl) ⟨112721, by rfl⟩ : syracuseStep 601181 = 225443) B225443
theorem B2141315 : Blo 115785 2141315 := bstep (se 1 (by rfl) ⟨1605986, by rfl⟩ : syracuseStep 2141315 = 3211973) B3211973
theorem B175307 : Blo 115785 175307 := bstep (se 1 (by rfl) ⟨131480, by rfl⟩ : syracuseStep 175307 = 262961) B262961
theorem B175319 : Blo 115785 175319 := bstep (se 1 (by rfl) ⟨131489, by rfl⟩ : syracuseStep 175319 = 262979) B262979
theorem B175385 : Blo 115785 175385 := bstep (se 2 (by rfl) ⟨65769, by rfl⟩ : syracuseStep 175385 = 131539) B131539
theorem B175499 : Blo 115785 175499 := bstep (se 1 (by rfl) ⟨131624, by rfl⟩ : syracuseStep 175499 = 263249) B263249
theorem B175511 : Blo 115785 175511 := bstep (se 1 (by rfl) ⟨131633, by rfl⟩ : syracuseStep 175511 = 263267) B263267
theorem B372185 : Blo 115785 372185 := bstep (se 2 (by rfl) ⟨139569, by rfl⟩ : syracuseStep 372185 = 279139) B279139
theorem B175577 : Blo 115785 175577 := bstep (se 2 (by rfl) ⟨65841, by rfl⟩ : syracuseStep 175577 = 131683) B131683
theorem B175691 : Blo 115785 175691 := bstep (se 1 (by rfl) ⟨131768, by rfl⟩ : syracuseStep 175691 = 263537) B263537
theorem B175703 : Blo 115785 175703 := bstep (se 1 (by rfl) ⟨131777, by rfl⟩ : syracuseStep 175703 = 263555) B263555
theorem B1519235 : Blo 115785 1519235 := bstep (se 1 (by rfl) ⟨1139426, by rfl⟩ : syracuseStep 1519235 = 2278853) B2278853
theorem B175769 : Blo 115785 175769 := bstep (se 2 (by rfl) ⟨65913, by rfl⟩ : syracuseStep 175769 = 131827) B131827
theorem B634547 : Blo 115785 634547 := bstep (se 1 (by rfl) ⟨475910, by rfl⟩ : syracuseStep 634547 = 951821) B951821
theorem B503489 : Blo 115785 503489 := bstep (se 2 (by rfl) ⟨188808, by rfl⟩ : syracuseStep 503489 = 377617) B377617
theorem B175883 : Blo 115785 175883 := bstep (se 1 (by rfl) ⟨131912, by rfl⟩ : syracuseStep 175883 = 263825) B263825
theorem B175895 : Blo 115785 175895 := bstep (se 1 (by rfl) ⟨131921, by rfl⟩ : syracuseStep 175895 = 263843) B263843
theorem B208705 : Blo 115785 208705 := bstep (se 2 (by rfl) ⟨78264, by rfl⟩ : syracuseStep 208705 = 156529) B156529
theorem B175961 : Blo 115785 175961 := bstep (se 2 (by rfl) ⟨65985, by rfl⟩ : syracuseStep 175961 = 131971) B131971
theorem B339805 : Blo 115785 339805 := bstep (se 3 (by rfl) ⟨63713, by rfl⟩ : syracuseStep 339805 = 127427) B127427
theorem B176075 : Blo 115785 176075 := bstep (se 1 (by rfl) ⟨132056, by rfl⟩ : syracuseStep 176075 = 264113) B264113
theorem B176087 : Blo 115785 176087 := bstep (se 1 (by rfl) ⟨132065, by rfl⟩ : syracuseStep 176087 = 264131) B264131
theorem B1814489 : Blo 115785 1814489 := bstep (se 2 (by rfl) ⟨680433, by rfl⟩ : syracuseStep 1814489 = 1360867) B1360867
theorem B176153 : Blo 115785 176153 := bstep (se 2 (by rfl) ⟨66057, by rfl⟩ : syracuseStep 176153 = 132115) B132115
theorem B340033 : Blo 115785 340033 := bstep (se 2 (by rfl) ⟨127512, by rfl⟩ : syracuseStep 340033 = 255025) B255025
theorem B897155 : Blo 115785 897155 := bstep (se 1 (by rfl) ⟨672866, by rfl⟩ : syracuseStep 897155 = 1345733) B1345733
theorem B176267 : Blo 115785 176267 := bstep (se 1 (by rfl) ⟨132200, by rfl⟩ : syracuseStep 176267 = 264401) B264401
theorem B176279 : Blo 115785 176279 := bstep (se 1 (by rfl) ⟨132209, by rfl⟩ : syracuseStep 176279 = 264419) B264419
theorem B176345 : Blo 115785 176345 := bstep (se 2 (by rfl) ⟨66129, by rfl⟩ : syracuseStep 176345 = 132259) B132259
theorem B176459 : Blo 115785 176459 := bstep (se 1 (by rfl) ⟨132344, by rfl⟩ : syracuseStep 176459 = 264689) B264689
theorem B176471 : Blo 115785 176471 := bstep (se 1 (by rfl) ⟨132353, by rfl⟩ : syracuseStep 176471 = 264707) B264707
theorem B373081 : Blo 115785 373081 := bstep (se 2 (by rfl) ⟨139905, by rfl⟩ : syracuseStep 373081 = 279811) B279811
theorem B340375 : Blo 115785 340375 := bstep (se 1 (by rfl) ⟨255281, by rfl⟩ : syracuseStep 340375 = 510563) B510563
theorem B176537 : Blo 115785 176537 := bstep (se 2 (by rfl) ⟨66201, by rfl⟩ : syracuseStep 176537 = 132403) B132403
theorem B176651 : Blo 115785 176651 := bstep (se 1 (by rfl) ⟨132488, by rfl⟩ : syracuseStep 176651 = 264977) B264977
theorem B176663 : Blo 115785 176663 := bstep (se 1 (by rfl) ⟨132497, by rfl⟩ : syracuseStep 176663 = 264995) B264995
theorem B176729 : Blo 115785 176729 := bstep (se 2 (by rfl) ⟨66273, by rfl⟩ : syracuseStep 176729 = 132547) B132547
theorem B504413 : Blo 115785 504413 := bstep (se 3 (by rfl) ⟨94577, by rfl⟩ : syracuseStep 504413 = 189155) B189155
theorem B537281 : Blo 115785 537281 := bstep (se 2 (by rfl) ⟨201480, by rfl⟩ : syracuseStep 537281 = 402961) B402961
theorem B176843 : Blo 115785 176843 := bstep (se 1 (by rfl) ⟨132632, by rfl⟩ : syracuseStep 176843 = 265265) B265265
theorem B176855 : Blo 115785 176855 := bstep (se 1 (by rfl) ⟨132641, by rfl⟩ : syracuseStep 176855 = 265283) B265283
theorem B176921 : Blo 115785 176921 := bstep (se 2 (by rfl) ⟨66345, by rfl⟩ : syracuseStep 176921 = 132691) B132691
theorem B1717037 : Blo 115785 1717037 := bstep (se 3 (by rfl) ⟨321944, by rfl⟩ : syracuseStep 1717037 = 643889) B643889
theorem B177035 : Blo 115785 177035 := bstep (se 1 (by rfl) ⟨132776, by rfl⟩ : syracuseStep 177035 = 265553) B265553
theorem B177047 : Blo 115785 177047 := bstep (se 1 (by rfl) ⟨132785, by rfl⟩ : syracuseStep 177047 = 265571) B265571
theorem B373697 : Blo 115785 373697 := bstep (se 2 (by rfl) ⟨140136, by rfl⟩ : syracuseStep 373697 = 280273) B280273
theorem B177113 : Blo 115785 177113 := bstep (se 2 (by rfl) ⟨66417, by rfl⟩ : syracuseStep 177113 = 132835) B132835
theorem B177227 : Blo 115785 177227 := bstep (se 1 (by rfl) ⟨132920, by rfl⟩ : syracuseStep 177227 = 265841) B265841
theorem B177239 : Blo 115785 177239 := bstep (se 1 (by rfl) ⟨132929, by rfl⟩ : syracuseStep 177239 = 265859) B265859
theorem B341081 : Blo 115785 341081 := bstep (se 2 (by rfl) ⟨127905, by rfl⟩ : syracuseStep 341081 = 255811) B255811
theorem B603287 : Blo 115785 603287 := bstep (se 1 (by rfl) ⟨452465, by rfl⟩ : syracuseStep 603287 = 904931) B904931
theorem B177305 : Blo 115785 177305 := bstep (se 2 (by rfl) ⟨66489, by rfl⟩ : syracuseStep 177305 = 132979) B132979
theorem B177419 : Blo 115785 177419 := bstep (se 1 (by rfl) ⟨133064, by rfl⟩ : syracuseStep 177419 = 266129) B266129
theorem B177431 : Blo 115785 177431 := bstep (se 1 (by rfl) ⟨133073, by rfl⟩ : syracuseStep 177431 = 266147) B266147
theorem B177497 : Blo 115785 177497 := bstep (se 2 (by rfl) ⟨66561, by rfl⟩ : syracuseStep 177497 = 133123) B133123
theorem B1553843 : Blo 115785 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B177611 : Blo 115785 177611 := bstep (se 1 (by rfl) ⟨133208, by rfl⟩ : syracuseStep 177611 = 266417) B266417
theorem B177623 : Blo 115785 177623 := bstep (se 1 (by rfl) ⟨133217, by rfl⟩ : syracuseStep 177623 = 266435) B266435
theorem B439769 : Blo 115785 439769 := bstep (se 2 (by rfl) ⟨164913, by rfl⟩ : syracuseStep 439769 = 329827) B329827
theorem B865753 : Blo 115785 865753 := bstep (se 2 (by rfl) ⟨324657, by rfl⟩ : syracuseStep 865753 = 649315) B649315
theorem B177689 : Blo 115785 177689 := bstep (se 2 (by rfl) ⟨66633, by rfl⟩ : syracuseStep 177689 = 133267) B133267
theorem B177803 : Blo 115785 177803 := bstep (se 1 (by rfl) ⟨133352, by rfl⟩ : syracuseStep 177803 = 266705) B266705
theorem B177815 : Blo 115785 177815 := bstep (se 1 (by rfl) ⟨133361, by rfl⟩ : syracuseStep 177815 = 266723) B266723
theorem B177881 : Blo 115785 177881 := bstep (se 2 (by rfl) ⟨66705, by rfl⟩ : syracuseStep 177881 = 133411) B133411
theorem B177995 : Blo 115785 177995 := bstep (se 1 (by rfl) ⟨133496, by rfl⟩ : syracuseStep 177995 = 266993) B266993
theorem B178007 : Blo 115785 178007 := bstep (se 1 (by rfl) ⟨133505, by rfl⟩ : syracuseStep 178007 = 267011) B267011
theorem B178073 : Blo 115785 178073 := bstep (se 2 (by rfl) ⟨66777, by rfl⟩ : syracuseStep 178073 = 133555) B133555
theorem B178187 : Blo 115785 178187 := bstep (se 1 (by rfl) ⟨133640, by rfl⟩ : syracuseStep 178187 = 267281) B267281
theorem B178199 : Blo 115785 178199 := bstep (se 1 (by rfl) ⟨133649, by rfl⟩ : syracuseStep 178199 = 267299) B267299
theorem B178265 : Blo 115785 178265 := bstep (se 2 (by rfl) ⟨66849, by rfl⟩ : syracuseStep 178265 = 133699) B133699
theorem B178379 : Blo 115785 178379 := bstep (se 1 (by rfl) ⟨133784, by rfl⟩ : syracuseStep 178379 = 267569) B267569
theorem B178391 : Blo 115785 178391 := bstep (se 1 (by rfl) ⟨133793, by rfl⟩ : syracuseStep 178391 = 267587) B267587
theorem B178457 : Blo 115785 178457 := bstep (se 2 (by rfl) ⟨66921, by rfl⟩ : syracuseStep 178457 = 133843) B133843
theorem B178571 : Blo 115785 178571 := bstep (se 1 (by rfl) ⟨133928, by rfl⟩ : syracuseStep 178571 = 267857) B267857
theorem B178583 : Blo 115785 178583 := bstep (se 1 (by rfl) ⟨133937, by rfl⟩ : syracuseStep 178583 = 267875) B267875
theorem B178649 : Blo 115785 178649 := bstep (se 2 (by rfl) ⟨66993, by rfl⟩ : syracuseStep 178649 = 133987) B133987
theorem B178763 : Blo 115785 178763 := bstep (se 1 (by rfl) ⟨134072, by rfl⟩ : syracuseStep 178763 = 268145) B268145
theorem B178775 : Blo 115785 178775 := bstep (se 1 (by rfl) ⟨134081, by rfl⟩ : syracuseStep 178775 = 268163) B268163
theorem B178841 : Blo 115785 178841 := bstep (se 2 (by rfl) ⟨67065, by rfl⟩ : syracuseStep 178841 = 134131) B134131
theorem B178955 : Blo 115785 178955 := bstep (se 1 (by rfl) ⟨134216, by rfl⟩ : syracuseStep 178955 = 268433) B268433
theorem B899857 : Blo 115785 899857 := bstep (se 2 (by rfl) ⟨337446, by rfl⟩ : syracuseStep 899857 = 674893) B674893
theorem B178967 : Blo 115785 178967 := bstep (se 1 (by rfl) ⟨134225, by rfl⟩ : syracuseStep 178967 = 268451) B268451
theorem B179033 : Blo 115785 179033 := bstep (se 2 (by rfl) ⟨67137, by rfl⟩ : syracuseStep 179033 = 134275) B134275
theorem B179147 : Blo 115785 179147 := bstep (se 1 (by rfl) ⟨134360, by rfl⟩ : syracuseStep 179147 = 268721) B268721
theorem B179159 : Blo 115785 179159 := bstep (se 1 (by rfl) ⟨134369, by rfl⟩ : syracuseStep 179159 = 268739) B268739
theorem B179225 : Blo 115785 179225 := bstep (se 2 (by rfl) ⟨67209, by rfl⟩ : syracuseStep 179225 = 134419) B134419
theorem B441395 : Blo 115785 441395 := bstep (se 1 (by rfl) ⟨331046, by rfl⟩ : syracuseStep 441395 = 662093) B662093
theorem B441409 : Blo 115785 441409 := bstep (se 2 (by rfl) ⟨165528, by rfl⟩ : syracuseStep 441409 = 331057) B331057
theorem B179339 : Blo 115785 179339 := bstep (se 1 (by rfl) ⟨134504, by rfl⟩ : syracuseStep 179339 = 269009) B269009
theorem B179351 : Blo 115785 179351 := bstep (se 1 (by rfl) ⟨134513, by rfl⟩ : syracuseStep 179351 = 269027) B269027
theorem B179417 : Blo 115785 179417 := bstep (se 2 (by rfl) ⟨67281, by rfl⟩ : syracuseStep 179417 = 134563) B134563
theorem B146711 : Blo 115785 146711 := bstep (se 1 (by rfl) ⟨110033, by rfl⟩ : syracuseStep 146711 = 220067) B220067
theorem B179531 : Blo 115785 179531 := bstep (se 1 (by rfl) ⟨134648, by rfl⟩ : syracuseStep 179531 = 269297) B269297
theorem B179543 : Blo 115785 179543 := bstep (se 1 (by rfl) ⟨134657, by rfl⟩ : syracuseStep 179543 = 269315) B269315
theorem B376157 : Blo 115785 376157 := bstep (se 3 (by rfl) ⟨70529, by rfl⟩ : syracuseStep 376157 = 141059) B141059
theorem B4078997 : Blo 115785 4078997 := bstep (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) B191203
theorem B212375 : Blo 115785 212375 := bstep (se 1 (by rfl) ⟨159281, by rfl⟩ : syracuseStep 212375 = 318563) B318563
theorem B179609 : Blo 115785 179609 := bstep (se 2 (by rfl) ⟨67353, by rfl⟩ : syracuseStep 179609 = 134707) B134707
theorem B900557 : Blo 115785 900557 := bstep (se 3 (by rfl) ⟨168854, by rfl⟩ : syracuseStep 900557 = 337709) B337709
theorem B376285 : Blo 115785 376285 := bstep (se 3 (by rfl) ⟨70553, by rfl⟩ : syracuseStep 376285 = 141107) B141107
theorem B376541 : Blo 115785 376541 := bstep (se 3 (by rfl) ⟨70601, by rfl⟩ : syracuseStep 376541 = 141203) B141203
theorem B507779 : Blo 115785 507779 := bstep (se 1 (by rfl) ⟨380834, by rfl⟩ : syracuseStep 507779 = 761669) B761669
theorem B901043 : Blo 115785 901043 := bstep (se 1 (by rfl) ⟨675782, by rfl⟩ : syracuseStep 901043 = 1351565) B1351565
theorem B147415 : Blo 115785 147415 := bstep (se 1 (by rfl) ⟨110561, by rfl⟩ : syracuseStep 147415 = 221123) B221123
theorem B573713 : Blo 115785 573713 := bstep (se 2 (by rfl) ⟨215142, by rfl⟩ : syracuseStep 573713 = 430285) B430285
theorem B377419 : Blo 115785 377419 := bstep (se 1 (by rfl) ⟨283064, by rfl⟩ : syracuseStep 377419 = 566129) B566129
theorem B2507395 : Blo 115785 2507395 := bstep (se 1 (by rfl) ⟨1880546, by rfl⟩ : syracuseStep 2507395 = 3761093) B3761093
theorem B443339 : Blo 115785 443339 := bstep (se 1 (by rfl) ⟨332504, by rfl⟩ : syracuseStep 443339 = 665009) B665009
theorem B443353 : Blo 115785 443353 := bstep (se 2 (by rfl) ⟨166257, by rfl⟩ : syracuseStep 443353 = 332515) B332515
theorem B115787 : Blo 115785 115787 := bstep (se 1 (by rfl) ⟨86840, by rfl⟩ : syracuseStep 115787 = 173681) B173681
theorem B115799 : Blo 115785 115799 := bstep (se 1 (by rfl) ⟨86849, by rfl⟩ : syracuseStep 115799 = 173699) B173699
theorem B115819 : Blo 115785 115819 := bstep (se 1 (by rfl) ⟨86864, by rfl⟩ : syracuseStep 115819 = 173729) B173729
theorem B115831 : Blo 115785 115831 := bstep (se 1 (by rfl) ⟨86873, by rfl⟩ : syracuseStep 115831 = 173747) B173747
theorem B115851 : Blo 115785 115851 := bstep (se 1 (by rfl) ⟨86888, by rfl⟩ : syracuseStep 115851 = 173777) B173777
theorem B115863 : Blo 115785 115863 := bstep (se 1 (by rfl) ⟨86897, by rfl⟩ : syracuseStep 115863 = 173795) B173795
theorem B115883 : Blo 115785 115883 := bstep (se 1 (by rfl) ⟨86912, by rfl⟩ : syracuseStep 115883 = 173825) B173825
theorem B115895 : Blo 115785 115895 := bstep (se 1 (by rfl) ⟨86921, by rfl⟩ : syracuseStep 115895 = 173843) B173843
theorem B115915 : Blo 115785 115915 := bstep (se 1 (by rfl) ⟨86936, by rfl⟩ : syracuseStep 115915 = 173873) B173873
theorem B115927 : Blo 115785 115927 := bstep (se 1 (by rfl) ⟨86945, by rfl⟩ : syracuseStep 115927 = 173891) B173891
theorem B115947 : Blo 115785 115947 := bstep (se 1 (by rfl) ⟨86960, by rfl⟩ : syracuseStep 115947 = 173921) B173921
theorem B115959 : Blo 115785 115959 := bstep (se 1 (by rfl) ⟨86969, by rfl⟩ : syracuseStep 115959 = 173939) B173939
theorem B115979 : Blo 115785 115979 := bstep (se 1 (by rfl) ⟨86984, by rfl⟩ : syracuseStep 115979 = 173969) B173969
theorem B115991 : Blo 115785 115991 := bstep (se 1 (by rfl) ⟨86993, by rfl⟩ : syracuseStep 115991 = 173987) B173987
theorem B116011 : Blo 115785 116011 := bstep (se 1 (by rfl) ⟨87008, by rfl⟩ : syracuseStep 116011 = 174017) B174017
theorem B116023 : Blo 115785 116023 := bstep (se 1 (by rfl) ⟨87017, by rfl⟩ : syracuseStep 116023 = 174035) B174035
theorem B116043 : Blo 115785 116043 := bstep (se 1 (by rfl) ⟨87032, by rfl⟩ : syracuseStep 116043 = 174065) B174065
theorem B116055 : Blo 115785 116055 := bstep (se 1 (by rfl) ⟨87041, by rfl⟩ : syracuseStep 116055 = 174083) B174083
theorem B902501 : Blo 115785 902501 := bstep (se 4 (by rfl) ⟨84609, by rfl⟩ : syracuseStep 902501 = 169219) B169219
theorem B116075 : Blo 115785 116075 := bstep (se 1 (by rfl) ⟨87056, by rfl⟩ : syracuseStep 116075 = 174113) B174113
theorem B116087 : Blo 115785 116087 := bstep (se 1 (by rfl) ⟨87065, by rfl⟩ : syracuseStep 116087 = 174131) B174131
theorem B116107 : Blo 115785 116107 := bstep (se 1 (by rfl) ⟨87080, by rfl⟩ : syracuseStep 116107 = 174161) B174161
theorem B116119 : Blo 115785 116119 := bstep (se 1 (by rfl) ⟨87089, by rfl⟩ : syracuseStep 116119 = 174179) B174179
theorem B116139 : Blo 115785 116139 := bstep (se 1 (by rfl) ⟨87104, by rfl⟩ : syracuseStep 116139 = 174209) B174209
theorem B116151 : Blo 115785 116151 := bstep (se 1 (by rfl) ⟨87113, by rfl⟩ : syracuseStep 116151 = 174227) B174227
theorem B116171 : Blo 115785 116171 := bstep (se 1 (by rfl) ⟨87128, by rfl⟩ : syracuseStep 116171 = 174257) B174257
theorem B116183 : Blo 115785 116183 := bstep (se 1 (by rfl) ⟨87137, by rfl⟩ : syracuseStep 116183 = 174275) B174275
theorem B116203 : Blo 115785 116203 := bstep (se 1 (by rfl) ⟨87152, by rfl⟩ : syracuseStep 116203 = 174305) B174305
theorem B116215 : Blo 115785 116215 := bstep (se 1 (by rfl) ⟨87161, by rfl⟩ : syracuseStep 116215 = 174323) B174323
theorem B116235 : Blo 115785 116235 := bstep (se 1 (by rfl) ⟨87176, by rfl⟩ : syracuseStep 116235 = 174353) B174353
theorem B116247 : Blo 115785 116247 := bstep (se 1 (by rfl) ⟨87185, by rfl⟩ : syracuseStep 116247 = 174371) B174371
theorem B116267 : Blo 115785 116267 := bstep (se 1 (by rfl) ⟨87200, by rfl⟩ : syracuseStep 116267 = 174401) B174401
theorem B116279 : Blo 115785 116279 := bstep (se 1 (by rfl) ⟨87209, by rfl⟩ : syracuseStep 116279 = 174419) B174419
theorem B116299 : Blo 115785 116299 := bstep (se 1 (by rfl) ⟨87224, by rfl⟩ : syracuseStep 116299 = 174449) B174449
theorem B116311 : Blo 115785 116311 := bstep (se 1 (by rfl) ⟨87233, by rfl⟩ : syracuseStep 116311 = 174467) B174467
theorem B771677 : Blo 115785 771677 := bstep (se 3 (by rfl) ⟨144689, by rfl⟩ : syracuseStep 771677 = 289379) B289379
theorem B116331 : Blo 115785 116331 := bstep (se 1 (by rfl) ⟨87248, by rfl⟩ : syracuseStep 116331 = 174497) B174497
theorem B116343 : Blo 115785 116343 := bstep (se 1 (by rfl) ⟨87257, by rfl⟩ : syracuseStep 116343 = 174515) B174515
theorem B4867715 : Blo 115785 4867715 := bstep (se 1 (by rfl) ⟨3650786, by rfl⟩ : syracuseStep 4867715 = 7301573) B7301573
theorem B116363 : Blo 115785 116363 := bstep (se 1 (by rfl) ⟨87272, by rfl⟩ : syracuseStep 116363 = 174545) B174545
theorem B149131 : Blo 115785 149131 := bstep (se 1 (by rfl) ⟨111848, by rfl⟩ : syracuseStep 149131 = 223697) B223697
theorem B116375 : Blo 115785 116375 := bstep (se 1 (by rfl) ⟨87281, by rfl⟩ : syracuseStep 116375 = 174563) B174563
theorem B116395 : Blo 115785 116395 := bstep (se 1 (by rfl) ⟨87296, by rfl⟩ : syracuseStep 116395 = 174593) B174593
theorem B116407 : Blo 115785 116407 := bstep (se 1 (by rfl) ⟨87305, by rfl⟩ : syracuseStep 116407 = 174611) B174611
theorem B116427 : Blo 115785 116427 := bstep (se 1 (by rfl) ⟨87320, by rfl⟩ : syracuseStep 116427 = 174641) B174641
theorem B116439 : Blo 115785 116439 := bstep (se 1 (by rfl) ⟨87329, by rfl⟩ : syracuseStep 116439 = 174659) B174659
theorem B116459 : Blo 115785 116459 := bstep (se 1 (by rfl) ⟨87344, by rfl⟩ : syracuseStep 116459 = 174689) B174689
theorem B116471 : Blo 115785 116471 := bstep (se 1 (by rfl) ⟨87353, by rfl⟩ : syracuseStep 116471 = 174707) B174707
theorem B116491 : Blo 115785 116491 := bstep (se 1 (by rfl) ⟨87368, by rfl⟩ : syracuseStep 116491 = 174737) B174737
theorem B116503 : Blo 115785 116503 := bstep (se 1 (by rfl) ⟨87377, by rfl⟩ : syracuseStep 116503 = 174755) B174755
theorem B116523 : Blo 115785 116523 := bstep (se 1 (by rfl) ⟨87392, by rfl⟩ : syracuseStep 116523 = 174785) B174785
theorem B116535 : Blo 115785 116535 := bstep (se 1 (by rfl) ⟨87401, by rfl⟩ : syracuseStep 116535 = 174803) B174803
theorem B247627 : Blo 115785 247627 := bstep (se 1 (by rfl) ⟨185720, by rfl⟩ : syracuseStep 247627 = 371441) B371441
theorem B116555 : Blo 115785 116555 := bstep (se 1 (by rfl) ⟨87416, by rfl⟩ : syracuseStep 116555 = 174833) B174833
theorem B902987 : Blo 115785 902987 := bstep (se 1 (by rfl) ⟨677240, by rfl⟩ : syracuseStep 902987 = 1354481) B1354481
theorem B116567 : Blo 115785 116567 := bstep (se 1 (by rfl) ⟨87425, by rfl⟩ : syracuseStep 116567 = 174851) B174851
theorem B116587 : Blo 115785 116587 := bstep (se 1 (by rfl) ⟨87440, by rfl⟩ : syracuseStep 116587 = 174881) B174881
theorem B116599 : Blo 115785 116599 := bstep (se 1 (by rfl) ⟨87449, by rfl⟩ : syracuseStep 116599 = 174899) B174899
theorem B116619 : Blo 115785 116619 := bstep (se 1 (by rfl) ⟨87464, by rfl⟩ : syracuseStep 116619 = 174929) B174929
theorem B116631 : Blo 115785 116631 := bstep (se 1 (by rfl) ⟨87473, by rfl⟩ : syracuseStep 116631 = 174947) B174947
theorem B444311 : Blo 115785 444311 := bstep (se 1 (by rfl) ⟨333233, by rfl⟩ : syracuseStep 444311 = 666467) B666467
theorem B116651 : Blo 115785 116651 := bstep (se 1 (by rfl) ⟨87488, by rfl⟩ : syracuseStep 116651 = 174977) B174977
theorem B116663 : Blo 115785 116663 := bstep (se 1 (by rfl) ⟨87497, by rfl⟩ : syracuseStep 116663 = 174995) B174995
theorem B280523 : Blo 115785 280523 := bstep (se 1 (by rfl) ⟨210392, by rfl⟩ : syracuseStep 280523 = 420785) B420785
theorem B116683 : Blo 115785 116683 := bstep (se 1 (by rfl) ⟨87512, by rfl⟩ : syracuseStep 116683 = 175025) B175025
theorem B116695 : Blo 115785 116695 := bstep (se 1 (by rfl) ⟨87521, by rfl⟩ : syracuseStep 116695 = 175043) B175043
theorem B116715 : Blo 115785 116715 := bstep (se 1 (by rfl) ⟨87536, by rfl⟩ : syracuseStep 116715 = 175073) B175073
theorem B116727 : Blo 115785 116727 := bstep (se 1 (by rfl) ⟨87545, by rfl⟩ : syracuseStep 116727 = 175091) B175091
theorem B116747 : Blo 115785 116747 := bstep (se 1 (by rfl) ⟨87560, by rfl⟩ : syracuseStep 116747 = 175121) B175121
theorem B116759 : Blo 115785 116759 := bstep (se 1 (by rfl) ⟨87569, by rfl⟩ : syracuseStep 116759 = 175139) B175139
theorem B215063 : Blo 115785 215063 := bstep (se 1 (by rfl) ⟨161297, by rfl⟩ : syracuseStep 215063 = 322595) B322595
theorem B116779 : Blo 115785 116779 := bstep (se 1 (by rfl) ⟨87584, by rfl⟩ : syracuseStep 116779 = 175169) B175169
theorem B116791 : Blo 115785 116791 := bstep (se 1 (by rfl) ⟨87593, by rfl⟩ : syracuseStep 116791 = 175187) B175187
theorem B116811 : Blo 115785 116811 := bstep (se 1 (by rfl) ⟨87608, by rfl⟩ : syracuseStep 116811 = 175217) B175217
theorem B116823 : Blo 115785 116823 := bstep (se 1 (by rfl) ⟨87617, by rfl⟩ : syracuseStep 116823 = 175235) B175235
theorem B182359 : Blo 115785 182359 := bstep (se 1 (by rfl) ⟨136769, by rfl⟩ : syracuseStep 182359 = 273539) B273539
theorem B1624157 : Blo 115785 1624157 := bstep (se 3 (by rfl) ⟨304529, by rfl⟩ : syracuseStep 1624157 = 609059) B609059
theorem B116843 : Blo 115785 116843 := bstep (se 1 (by rfl) ⟨87632, by rfl⟩ : syracuseStep 116843 = 175265) B175265
theorem B116855 : Blo 115785 116855 := bstep (se 1 (by rfl) ⟨87641, by rfl⟩ : syracuseStep 116855 = 175283) B175283
theorem B116875 : Blo 115785 116875 := bstep (se 1 (by rfl) ⟨87656, by rfl⟩ : syracuseStep 116875 = 175313) B175313
theorem B116887 : Blo 115785 116887 := bstep (se 1 (by rfl) ⟨87665, by rfl⟩ : syracuseStep 116887 = 175331) B175331
theorem B116907 : Blo 115785 116907 := bstep (se 1 (by rfl) ⟨87680, by rfl⟩ : syracuseStep 116907 = 175361) B175361
theorem B116919 : Blo 115785 116919 := bstep (se 1 (by rfl) ⟨87689, by rfl⟩ : syracuseStep 116919 = 175379) B175379
theorem B379073 : Blo 115785 379073 := bstep (se 2 (by rfl) ⟨142152, by rfl⟩ : syracuseStep 379073 = 284305) B284305
theorem B116939 : Blo 115785 116939 := bstep (se 1 (by rfl) ⟨87704, by rfl⟩ : syracuseStep 116939 = 175409) B175409
theorem B116951 : Blo 115785 116951 := bstep (se 1 (by rfl) ⟨87713, by rfl⟩ : syracuseStep 116951 = 175427) B175427
theorem B116971 : Blo 115785 116971 := bstep (se 1 (by rfl) ⟨87728, by rfl⟩ : syracuseStep 116971 = 175457) B175457
theorem B116983 : Blo 115785 116983 := bstep (se 1 (by rfl) ⟨87737, by rfl⟩ : syracuseStep 116983 = 175475) B175475
theorem B117003 : Blo 115785 117003 := bstep (se 1 (by rfl) ⟨87752, by rfl⟩ : syracuseStep 117003 = 175505) B175505
theorem B117015 : Blo 115785 117015 := bstep (se 1 (by rfl) ⟨87761, by rfl⟩ : syracuseStep 117015 = 175523) B175523
theorem B117035 : Blo 115785 117035 := bstep (se 1 (by rfl) ⟨87776, by rfl⟩ : syracuseStep 117035 = 175553) B175553
theorem B2836781 : Blo 115785 2836781 := bstep (se 3 (by rfl) ⟨531896, by rfl⟩ : syracuseStep 2836781 = 1063793) B1063793
theorem B117047 : Blo 115785 117047 := bstep (se 1 (by rfl) ⟨87785, by rfl⟩ : syracuseStep 117047 = 175571) B175571
theorem B117067 : Blo 115785 117067 := bstep (se 1 (by rfl) ⟨87800, by rfl⟩ : syracuseStep 117067 = 175601) B175601
theorem B117079 : Blo 115785 117079 := bstep (se 1 (by rfl) ⟨87809, by rfl⟩ : syracuseStep 117079 = 175619) B175619
theorem B117099 : Blo 115785 117099 := bstep (se 1 (by rfl) ⟨87824, by rfl⟩ : syracuseStep 117099 = 175649) B175649
theorem B117111 : Blo 115785 117111 := bstep (se 1 (by rfl) ⟨87833, by rfl⟩ : syracuseStep 117111 = 175667) B175667
theorem B117131 : Blo 115785 117131 := bstep (se 1 (by rfl) ⟨87848, by rfl⟩ : syracuseStep 117131 = 175697) B175697
theorem B117143 : Blo 115785 117143 := bstep (se 1 (by rfl) ⟨87857, by rfl⟩ : syracuseStep 117143 = 175715) B175715
theorem B117163 : Blo 115785 117163 := bstep (se 1 (by rfl) ⟨87872, by rfl⟩ : syracuseStep 117163 = 175745) B175745
theorem B117175 : Blo 115785 117175 := bstep (se 1 (by rfl) ⟨87881, by rfl⟩ : syracuseStep 117175 = 175763) B175763
theorem B117195 : Blo 115785 117195 := bstep (se 1 (by rfl) ⟨87896, by rfl⟩ : syracuseStep 117195 = 175793) B175793
theorem B117207 : Blo 115785 117207 := bstep (se 1 (by rfl) ⟨87905, by rfl⟩ : syracuseStep 117207 = 175811) B175811
theorem B117227 : Blo 115785 117227 := bstep (se 1 (by rfl) ⟨87920, by rfl⟩ : syracuseStep 117227 = 175841) B175841
theorem B117239 : Blo 115785 117239 := bstep (se 1 (by rfl) ⟨87929, by rfl⟩ : syracuseStep 117239 = 175859) B175859
theorem B117259 : Blo 115785 117259 := bstep (se 1 (by rfl) ⟨87944, by rfl⟩ : syracuseStep 117259 = 175889) B175889
theorem B117271 : Blo 115785 117271 := bstep (se 1 (by rfl) ⟨87953, by rfl⟩ : syracuseStep 117271 = 175907) B175907
theorem B117291 : Blo 115785 117291 := bstep (se 1 (by rfl) ⟨87968, by rfl⟩ : syracuseStep 117291 = 175937) B175937
theorem B117303 : Blo 115785 117303 := bstep (se 1 (by rfl) ⟨87977, by rfl⟩ : syracuseStep 117303 = 175955) B175955
theorem B117323 : Blo 115785 117323 := bstep (se 1 (by rfl) ⟨87992, by rfl⟩ : syracuseStep 117323 = 175985) B175985
theorem B117335 : Blo 115785 117335 := bstep (se 1 (by rfl) ⟨88001, by rfl⟩ : syracuseStep 117335 = 176003) B176003
theorem B150103 : Blo 115785 150103 := bstep (se 1 (by rfl) ⟨112577, by rfl⟩ : syracuseStep 150103 = 225155) B225155
theorem B510553 : Blo 115785 510553 := bstep (se 2 (by rfl) ⟨191457, by rfl⟩ : syracuseStep 510553 = 382915) B382915
theorem B117355 : Blo 115785 117355 := bstep (se 1 (by rfl) ⟨88016, by rfl⟩ : syracuseStep 117355 = 176033) B176033
theorem B117367 : Blo 115785 117367 := bstep (se 1 (by rfl) ⟨88025, by rfl⟩ : syracuseStep 117367 = 176051) B176051
theorem B117387 : Blo 115785 117387 := bstep (se 1 (by rfl) ⟨88040, by rfl⟩ : syracuseStep 117387 = 176081) B176081
theorem B117399 : Blo 115785 117399 := bstep (se 1 (by rfl) ⟨88049, by rfl⟩ : syracuseStep 117399 = 176099) B176099
theorem B117419 : Blo 115785 117419 := bstep (se 1 (by rfl) ⟨88064, by rfl⟩ : syracuseStep 117419 = 176129) B176129
theorem B117431 : Blo 115785 117431 := bstep (se 1 (by rfl) ⟨88073, by rfl⟩ : syracuseStep 117431 = 176147) B176147
theorem B117451 : Blo 115785 117451 := bstep (se 1 (by rfl) ⟨88088, by rfl⟩ : syracuseStep 117451 = 176177) B176177
theorem B117463 : Blo 115785 117463 := bstep (se 1 (by rfl) ⟨88097, by rfl⟩ : syracuseStep 117463 = 176195) B176195
theorem B117483 : Blo 115785 117483 := bstep (se 1 (by rfl) ⟨88112, by rfl⟩ : syracuseStep 117483 = 176225) B176225
theorem B117495 : Blo 115785 117495 := bstep (se 1 (by rfl) ⟨88121, by rfl⟩ : syracuseStep 117495 = 176243) B176243
theorem B117515 : Blo 115785 117515 := bstep (se 1 (by rfl) ⟨88136, by rfl⟩ : syracuseStep 117515 = 176273) B176273
theorem B117527 : Blo 115785 117527 := bstep (se 1 (by rfl) ⟨88145, by rfl⟩ : syracuseStep 117527 = 176291) B176291
theorem B117547 : Blo 115785 117547 := bstep (se 1 (by rfl) ⟨88160, by rfl⟩ : syracuseStep 117547 = 176321) B176321
theorem B117559 : Blo 115785 117559 := bstep (se 1 (by rfl) ⟨88169, by rfl⟩ : syracuseStep 117559 = 176339) B176339
theorem B117579 : Blo 115785 117579 := bstep (se 1 (by rfl) ⟨88184, by rfl⟩ : syracuseStep 117579 = 176369) B176369
theorem B117591 : Blo 115785 117591 := bstep (se 1 (by rfl) ⟨88193, by rfl⟩ : syracuseStep 117591 = 176387) B176387
theorem B117611 : Blo 115785 117611 := bstep (se 1 (by rfl) ⟨88208, by rfl⟩ : syracuseStep 117611 = 176417) B176417
theorem B117623 : Blo 115785 117623 := bstep (se 1 (by rfl) ⟨88217, by rfl⟩ : syracuseStep 117623 = 176435) B176435
theorem B117643 : Blo 115785 117643 := bstep (se 1 (by rfl) ⟨88232, by rfl⟩ : syracuseStep 117643 = 176465) B176465
theorem B117655 : Blo 115785 117655 := bstep (se 1 (by rfl) ⟨88241, by rfl⟩ : syracuseStep 117655 = 176483) B176483
theorem B117675 : Blo 115785 117675 := bstep (se 1 (by rfl) ⟨88256, by rfl⟩ : syracuseStep 117675 = 176513) B176513
theorem B2411441 : Blo 115785 2411441 := bstep (se 2 (by rfl) ⟨904290, by rfl⟩ : syracuseStep 2411441 = 1808581) B1808581
theorem B117687 : Blo 115785 117687 := bstep (se 1 (by rfl) ⟨88265, by rfl⟩ : syracuseStep 117687 = 176531) B176531
theorem B117707 : Blo 115785 117707 := bstep (se 1 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 117707 = 176561) B176561
theorem B117719 : Blo 115785 117719 := bstep (se 1 (by rfl) ⟨88289, by rfl⟩ : syracuseStep 117719 = 176579) B176579
theorem B117739 : Blo 115785 117739 := bstep (se 1 (by rfl) ⟨88304, by rfl⟩ : syracuseStep 117739 = 176609) B176609
theorem B117751 : Blo 115785 117751 := bstep (se 1 (by rfl) ⟨88313, by rfl⟩ : syracuseStep 117751 = 176627) B176627
theorem B117771 : Blo 115785 117771 := bstep (se 1 (by rfl) ⟨88328, by rfl⟩ : syracuseStep 117771 = 176657) B176657
theorem B117783 : Blo 115785 117783 := bstep (se 1 (by rfl) ⟨88337, by rfl⟩ : syracuseStep 117783 = 176675) B176675
theorem B117803 : Blo 115785 117803 := bstep (se 1 (by rfl) ⟨88352, by rfl⟩ : syracuseStep 117803 = 176705) B176705
theorem B117815 : Blo 115785 117815 := bstep (se 1 (by rfl) ⟨88361, by rfl⟩ : syracuseStep 117815 = 176723) B176723
theorem B281675 : Blo 115785 281675 := bstep (se 1 (by rfl) ⟨211256, by rfl⟩ : syracuseStep 281675 = 422513) B422513
theorem B117835 : Blo 115785 117835 := bstep (se 1 (by rfl) ⟨88376, by rfl⟩ : syracuseStep 117835 = 176753) B176753
theorem B117847 : Blo 115785 117847 := bstep (se 1 (by rfl) ⟨88385, by rfl⟩ : syracuseStep 117847 = 176771) B176771
theorem B117867 : Blo 115785 117867 := bstep (se 1 (by rfl) ⟨88400, by rfl⟩ : syracuseStep 117867 = 176801) B176801
theorem B117879 : Blo 115785 117879 := bstep (se 1 (by rfl) ⟨88409, by rfl⟩ : syracuseStep 117879 = 176819) B176819
theorem B445571 : Blo 115785 445571 := bstep (se 1 (by rfl) ⟨334178, by rfl⟩ : syracuseStep 445571 = 668357) B668357
theorem B117899 : Blo 115785 117899 := bstep (se 1 (by rfl) ⟨88424, by rfl⟩ : syracuseStep 117899 = 176849) B176849
theorem B117911 : Blo 115785 117911 := bstep (se 1 (by rfl) ⟨88433, by rfl⟩ : syracuseStep 117911 = 176867) B176867
theorem B117931 : Blo 115785 117931 := bstep (se 1 (by rfl) ⟨88448, by rfl⟩ : syracuseStep 117931 = 176897) B176897
theorem B249011 : Blo 115785 249011 := bstep (se 1 (by rfl) ⟨186758, by rfl⟩ : syracuseStep 249011 = 373517) B373517
theorem B117943 : Blo 115785 117943 := bstep (se 1 (by rfl) ⟨88457, by rfl⟩ : syracuseStep 117943 = 176915) B176915
theorem B117963 : Blo 115785 117963 := bstep (se 1 (by rfl) ⟨88472, by rfl⟩ : syracuseStep 117963 = 176945) B176945
theorem B117975 : Blo 115785 117975 := bstep (se 1 (by rfl) ⟨88481, by rfl⟩ : syracuseStep 117975 = 176963) B176963
theorem B117995 : Blo 115785 117995 := bstep (se 1 (by rfl) ⟨88496, by rfl⟩ : syracuseStep 117995 = 176993) B176993
theorem B118007 : Blo 115785 118007 := bstep (se 1 (by rfl) ⟨88505, by rfl⟩ : syracuseStep 118007 = 177011) B177011
theorem B118027 : Blo 115785 118027 := bstep (se 1 (by rfl) ⟨88520, by rfl⟩ : syracuseStep 118027 = 177041) B177041
theorem B118039 : Blo 115785 118039 := bstep (se 1 (by rfl) ⟨88529, by rfl⟩ : syracuseStep 118039 = 177059) B177059
theorem B249113 : Blo 115785 249113 := bstep (se 2 (by rfl) ⟨93417, by rfl⟩ : syracuseStep 249113 = 186835) B186835
theorem B118059 : Blo 115785 118059 := bstep (se 1 (by rfl) ⟨88544, by rfl⟩ : syracuseStep 118059 = 177089) B177089
theorem B118071 : Blo 115785 118071 := bstep (se 1 (by rfl) ⟨88553, by rfl⟩ : syracuseStep 118071 = 177107) B177107
theorem B118091 : Blo 115785 118091 := bstep (se 1 (by rfl) ⟨88568, by rfl⟩ : syracuseStep 118091 = 177137) B177137
theorem B118103 : Blo 115785 118103 := bstep (se 1 (by rfl) ⟨88577, by rfl⟩ : syracuseStep 118103 = 177155) B177155
theorem B118123 : Blo 115785 118123 := bstep (se 1 (by rfl) ⟨88592, by rfl⟩ : syracuseStep 118123 = 177185) B177185
theorem B118135 : Blo 115785 118135 := bstep (se 1 (by rfl) ⟨88601, by rfl⟩ : syracuseStep 118135 = 177203) B177203
theorem B118155 : Blo 115785 118155 := bstep (se 1 (by rfl) ⟨88616, by rfl⟩ : syracuseStep 118155 = 177233) B177233
theorem B150923 : Blo 115785 150923 := bstep (se 1 (by rfl) ⟨113192, by rfl⟩ : syracuseStep 150923 = 226385) B226385
theorem B118167 : Blo 115785 118167 := bstep (se 1 (by rfl) ⟨88625, by rfl⟩ : syracuseStep 118167 = 177251) B177251
theorem B118187 : Blo 115785 118187 := bstep (se 1 (by rfl) ⟨88640, by rfl⟩ : syracuseStep 118187 = 177281) B177281
theorem B118199 : Blo 115785 118199 := bstep (se 1 (by rfl) ⟨88649, by rfl⟩ : syracuseStep 118199 = 177299) B177299
theorem B118219 : Blo 115785 118219 := bstep (se 1 (by rfl) ⟨88664, by rfl⟩ : syracuseStep 118219 = 177329) B177329
theorem B118231 : Blo 115785 118231 := bstep (se 1 (by rfl) ⟨88673, by rfl⟩ : syracuseStep 118231 = 177347) B177347
theorem B118251 : Blo 115785 118251 := bstep (se 1 (by rfl) ⟨88688, by rfl⟩ : syracuseStep 118251 = 177377) B177377
theorem B118263 : Blo 115785 118263 := bstep (se 1 (by rfl) ⟨88697, by rfl⟩ : syracuseStep 118263 = 177395) B177395
theorem B1003013 : Blo 115785 1003013 := bstep (se 4 (by rfl) ⟨94032, by rfl⟩ : syracuseStep 1003013 = 188065) B188065
theorem B118283 : Blo 115785 118283 := bstep (se 1 (by rfl) ⟨88712, by rfl⟩ : syracuseStep 118283 = 177425) B177425
theorem B118295 : Blo 115785 118295 := bstep (se 1 (by rfl) ⟨88721, by rfl⟩ : syracuseStep 118295 = 177443) B177443
theorem B118315 : Blo 115785 118315 := bstep (se 1 (by rfl) ⟨88736, by rfl⟩ : syracuseStep 118315 = 177473) B177473
theorem B118327 : Blo 115785 118327 := bstep (se 1 (by rfl) ⟨88745, by rfl⟩ : syracuseStep 118327 = 177491) B177491
theorem B118347 : Blo 115785 118347 := bstep (se 1 (by rfl) ⟨88760, by rfl⟩ : syracuseStep 118347 = 177521) B177521
theorem B118359 : Blo 115785 118359 := bstep (se 1 (by rfl) ⟨88769, by rfl⟩ : syracuseStep 118359 = 177539) B177539
theorem B839261 : Blo 115785 839261 := bstep (se 3 (by rfl) ⟨157361, by rfl⟩ : syracuseStep 839261 = 314723) B314723
theorem B118379 : Blo 115785 118379 := bstep (se 1 (by rfl) ⟨88784, by rfl⟩ : syracuseStep 118379 = 177569) B177569
theorem B118391 : Blo 115785 118391 := bstep (se 1 (by rfl) ⟨88793, by rfl⟩ : syracuseStep 118391 = 177587) B177587
theorem B249473 : Blo 115785 249473 := bstep (se 2 (by rfl) ⟨93552, by rfl⟩ : syracuseStep 249473 = 187105) B187105
theorem B118411 : Blo 115785 118411 := bstep (se 1 (by rfl) ⟨88808, by rfl⟩ : syracuseStep 118411 = 177617) B177617
theorem B118423 : Blo 115785 118423 := bstep (se 1 (by rfl) ⟨88817, by rfl⟩ : syracuseStep 118423 = 177635) B177635
theorem B118443 : Blo 115785 118443 := bstep (se 1 (by rfl) ⟨88832, by rfl⟩ : syracuseStep 118443 = 177665) B177665
theorem B118455 : Blo 115785 118455 := bstep (se 1 (by rfl) ⟨88841, by rfl⟩ : syracuseStep 118455 = 177683) B177683
theorem B118475 : Blo 115785 118475 := bstep (se 1 (by rfl) ⟨88856, by rfl⟩ : syracuseStep 118475 = 177713) B177713
theorem B118487 : Blo 115785 118487 := bstep (se 1 (by rfl) ⟨88865, by rfl⟩ : syracuseStep 118487 = 177731) B177731
theorem B118507 : Blo 115785 118507 := bstep (se 1 (by rfl) ⟨88880, by rfl⟩ : syracuseStep 118507 = 177761) B177761
theorem B118519 : Blo 115785 118519 := bstep (se 1 (by rfl) ⟨88889, by rfl⟩ : syracuseStep 118519 = 177779) B177779
theorem B118539 : Blo 115785 118539 := bstep (se 1 (by rfl) ⟨88904, by rfl⟩ : syracuseStep 118539 = 177809) B177809
theorem B118551 : Blo 115785 118551 := bstep (se 1 (by rfl) ⟨88913, by rfl⟩ : syracuseStep 118551 = 177827) B177827
theorem B118571 : Blo 115785 118571 := bstep (se 1 (by rfl) ⟨88928, by rfl⟩ : syracuseStep 118571 = 177857) B177857
theorem B118583 : Blo 115785 118583 := bstep (se 1 (by rfl) ⟨88937, by rfl⟩ : syracuseStep 118583 = 177875) B177875
theorem B118603 : Blo 115785 118603 := bstep (se 1 (by rfl) ⟨88952, by rfl⟩ : syracuseStep 118603 = 177905) B177905
theorem B118615 : Blo 115785 118615 := bstep (se 1 (by rfl) ⟨88961, by rfl⟩ : syracuseStep 118615 = 177923) B177923
theorem B118635 : Blo 115785 118635 := bstep (se 1 (by rfl) ⟨88976, by rfl⟩ : syracuseStep 118635 = 177953) B177953
theorem B118647 : Blo 115785 118647 := bstep (se 1 (by rfl) ⟨88985, by rfl⟩ : syracuseStep 118647 = 177971) B177971
theorem B118667 : Blo 115785 118667 := bstep (se 1 (by rfl) ⟨89000, by rfl⟩ : syracuseStep 118667 = 178001) B178001
theorem B118679 : Blo 115785 118679 := bstep (se 1 (by rfl) ⟨89009, by rfl⟩ : syracuseStep 118679 = 178019) B178019
theorem B118699 : Blo 115785 118699 := bstep (se 1 (by rfl) ⟨89024, by rfl⟩ : syracuseStep 118699 = 178049) B178049
theorem B839603 : Blo 115785 839603 := bstep (se 1 (by rfl) ⟨629702, by rfl⟩ : syracuseStep 839603 = 1259405) B1259405
theorem B479155 : Blo 115785 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B118711 : Blo 115785 118711 := bstep (se 1 (by rfl) ⟨89033, by rfl⟩ : syracuseStep 118711 = 178067) B178067
theorem B118731 : Blo 115785 118731 := bstep (se 1 (by rfl) ⟨89048, by rfl⟩ : syracuseStep 118731 = 178097) B178097
theorem B118743 : Blo 115785 118743 := bstep (se 1 (by rfl) ⟨89057, by rfl⟩ : syracuseStep 118743 = 178115) B178115
theorem B118763 : Blo 115785 118763 := bstep (se 1 (by rfl) ⟨89072, by rfl⟩ : syracuseStep 118763 = 178145) B178145
theorem B118775 : Blo 115785 118775 := bstep (se 1 (by rfl) ⟨89081, by rfl⟩ : syracuseStep 118775 = 178163) B178163
theorem B118795 : Blo 115785 118795 := bstep (se 1 (by rfl) ⟨89096, by rfl⟩ : syracuseStep 118795 = 178193) B178193
theorem B118807 : Blo 115785 118807 := bstep (se 1 (by rfl) ⟨89105, by rfl⟩ : syracuseStep 118807 = 178211) B178211
theorem B118827 : Blo 115785 118827 := bstep (se 1 (by rfl) ⟨89120, by rfl⟩ : syracuseStep 118827 = 178241) B178241
theorem B118839 : Blo 115785 118839 := bstep (se 1 (by rfl) ⟨89129, by rfl⟩ : syracuseStep 118839 = 178259) B178259
theorem B118859 : Blo 115785 118859 := bstep (se 1 (by rfl) ⟨89144, by rfl⟩ : syracuseStep 118859 = 178289) B178289
theorem B118871 : Blo 115785 118871 := bstep (se 1 (by rfl) ⟨89153, by rfl⟩ : syracuseStep 118871 = 178307) B178307
theorem B118891 : Blo 115785 118891 := bstep (se 1 (by rfl) ⟨89168, by rfl⟩ : syracuseStep 118891 = 178337) B178337
theorem B118903 : Blo 115785 118903 := bstep (se 1 (by rfl) ⟨89177, by rfl⟩ : syracuseStep 118903 = 178355) B178355
theorem B118923 : Blo 115785 118923 := bstep (se 1 (by rfl) ⟨89192, by rfl⟩ : syracuseStep 118923 = 178385) B178385
theorem B1527959 : Blo 115785 1527959 := bstep (se 1 (by rfl) ⟨1145969, by rfl⟩ : syracuseStep 1527959 = 2291939) B2291939
theorem B118935 : Blo 115785 118935 := bstep (se 1 (by rfl) ⟨89201, by rfl⟩ : syracuseStep 118935 = 178403) B178403
theorem B118955 : Blo 115785 118955 := bstep (se 1 (by rfl) ⟨89216, by rfl⟩ : syracuseStep 118955 = 178433) B178433
theorem B1003697 : Blo 115785 1003697 := bstep (se 2 (by rfl) ⟨376386, by rfl⟩ : syracuseStep 1003697 = 752773) B752773
theorem B118967 : Blo 115785 118967 := bstep (se 1 (by rfl) ⟨89225, by rfl⟩ : syracuseStep 118967 = 178451) B178451
theorem B118987 : Blo 115785 118987 := bstep (se 1 (by rfl) ⟨89240, by rfl⟩ : syracuseStep 118987 = 178481) B178481
theorem B118999 : Blo 115785 118999 := bstep (se 1 (by rfl) ⟨89249, by rfl⟩ : syracuseStep 118999 = 178499) B178499
theorem B119019 : Blo 115785 119019 := bstep (se 1 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 119019 = 178529) B178529
theorem B119031 : Blo 115785 119031 := bstep (se 1 (by rfl) ⟨89273, by rfl⟩ : syracuseStep 119031 = 178547) B178547
theorem B119051 : Blo 115785 119051 := bstep (se 1 (by rfl) ⟨89288, by rfl⟩ : syracuseStep 119051 = 178577) B178577
theorem B119063 : Blo 115785 119063 := bstep (se 1 (by rfl) ⟨89297, by rfl⟩ : syracuseStep 119063 = 178595) B178595
theorem B119083 : Blo 115785 119083 := bstep (se 1 (by rfl) ⟨89312, by rfl⟩ : syracuseStep 119083 = 178625) B178625
theorem B643373 : Blo 115785 643373 := bstep (se 3 (by rfl) ⟨120632, by rfl⟩ : syracuseStep 643373 = 241265) B241265
theorem B119095 : Blo 115785 119095 := bstep (se 1 (by rfl) ⟨89321, by rfl⟩ : syracuseStep 119095 = 178643) B178643
theorem B119115 : Blo 115785 119115 := bstep (se 1 (by rfl) ⟨89336, by rfl⟩ : syracuseStep 119115 = 178673) B178673
theorem B250199 : Blo 115785 250199 := bstep (se 1 (by rfl) ⟨187649, by rfl⟩ : syracuseStep 250199 = 375299) B375299
theorem B119127 : Blo 115785 119127 := bstep (se 1 (by rfl) ⟨89345, by rfl⟩ : syracuseStep 119127 = 178691) B178691
theorem B119147 : Blo 115785 119147 := bstep (se 1 (by rfl) ⟨89360, by rfl⟩ : syracuseStep 119147 = 178721) B178721
theorem B119159 : Blo 115785 119159 := bstep (se 1 (by rfl) ⟨89369, by rfl⟩ : syracuseStep 119159 = 178739) B178739
theorem B119179 : Blo 115785 119179 := bstep (se 1 (by rfl) ⟨89384, by rfl⟩ : syracuseStep 119179 = 178769) B178769
theorem B119191 : Blo 115785 119191 := bstep (se 1 (by rfl) ⟨89393, by rfl⟩ : syracuseStep 119191 = 178787) B178787
theorem B119211 : Blo 115785 119211 := bstep (se 1 (by rfl) ⟨89408, by rfl⟩ : syracuseStep 119211 = 178817) B178817
theorem B119223 : Blo 115785 119223 := bstep (se 1 (by rfl) ⟨89417, by rfl⟩ : syracuseStep 119223 = 178835) B178835
theorem B119243 : Blo 115785 119243 := bstep (se 1 (by rfl) ⟨89432, by rfl⟩ : syracuseStep 119243 = 178865) B178865
theorem B119255 : Blo 115785 119255 := bstep (se 1 (by rfl) ⟨89441, by rfl⟩ : syracuseStep 119255 = 178883) B178883
theorem B119275 : Blo 115785 119275 := bstep (se 1 (by rfl) ⟨89456, by rfl⟩ : syracuseStep 119275 = 178913) B178913
theorem B119287 : Blo 115785 119287 := bstep (se 1 (by rfl) ⟨89465, by rfl⟩ : syracuseStep 119287 = 178931) B178931
theorem B119307 : Blo 115785 119307 := bstep (se 1 (by rfl) ⟨89480, by rfl⟩ : syracuseStep 119307 = 178961) B178961
theorem B1921553 : Blo 115785 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B119319 : Blo 115785 119319 := bstep (se 1 (by rfl) ⟨89489, by rfl⟩ : syracuseStep 119319 = 178979) B178979
theorem B119339 : Blo 115785 119339 := bstep (se 1 (by rfl) ⟨89504, by rfl⟩ : syracuseStep 119339 = 179009) B179009
theorem B119351 : Blo 115785 119351 := bstep (se 1 (by rfl) ⟨89513, by rfl⟩ : syracuseStep 119351 = 179027) B179027
theorem B119371 : Blo 115785 119371 := bstep (se 1 (by rfl) ⟨89528, by rfl⟩ : syracuseStep 119371 = 179057) B179057
theorem B119383 : Blo 115785 119383 := bstep (se 1 (by rfl) ⟨89537, by rfl⟩ : syracuseStep 119383 = 179075) B179075
theorem B119403 : Blo 115785 119403 := bstep (se 1 (by rfl) ⟨89552, by rfl⟩ : syracuseStep 119403 = 179105) B179105
theorem B119415 : Blo 115785 119415 := bstep (se 1 (by rfl) ⟨89561, by rfl⟩ : syracuseStep 119415 = 179123) B179123
theorem B1135235 : Blo 115785 1135235 := bstep (se 1 (by rfl) ⟨851426, by rfl⟩ : syracuseStep 1135235 = 1702853) B1702853
theorem B119435 : Blo 115785 119435 := bstep (se 1 (by rfl) ⟨89576, by rfl⟩ : syracuseStep 119435 = 179153) B179153
theorem B119447 : Blo 115785 119447 := bstep (se 1 (by rfl) ⟨89585, by rfl⟩ : syracuseStep 119447 = 179171) B179171
theorem B119467 : Blo 115785 119467 := bstep (se 1 (by rfl) ⟨89600, by rfl⟩ : syracuseStep 119467 = 179201) B179201
theorem B119479 : Blo 115785 119479 := bstep (se 1 (by rfl) ⟨89609, by rfl⟩ : syracuseStep 119479 = 179219) B179219
theorem B119499 : Blo 115785 119499 := bstep (se 1 (by rfl) ⟨89624, by rfl⟩ : syracuseStep 119499 = 179249) B179249
theorem B119511 : Blo 115785 119511 := bstep (se 1 (by rfl) ⟨89633, by rfl⟩ : syracuseStep 119511 = 179267) B179267
theorem B119531 : Blo 115785 119531 := bstep (se 1 (by rfl) ⟨89648, by rfl⟩ : syracuseStep 119531 = 179297) B179297
theorem B119543 : Blo 115785 119543 := bstep (se 1 (by rfl) ⟨89657, by rfl⟩ : syracuseStep 119543 = 179315) B179315
theorem B119563 : Blo 115785 119563 := bstep (se 1 (by rfl) ⟨89672, by rfl⟩ : syracuseStep 119563 = 179345) B179345
theorem B119575 : Blo 115785 119575 := bstep (se 1 (by rfl) ⟨89681, by rfl⟩ : syracuseStep 119575 = 179363) B179363
theorem B119595 : Blo 115785 119595 := bstep (se 1 (by rfl) ⟨89696, by rfl⟩ : syracuseStep 119595 = 179393) B179393
theorem B119607 : Blo 115785 119607 := bstep (se 1 (by rfl) ⟨89705, by rfl⟩ : syracuseStep 119607 = 179411) B179411
theorem B676673 : Blo 115785 676673 := bstep (se 2 (by rfl) ⟨253752, by rfl⟩ : syracuseStep 676673 = 507505) B507505
theorem B119627 : Blo 115785 119627 := bstep (se 1 (by rfl) ⟨89720, by rfl⟩ : syracuseStep 119627 = 179441) B179441
theorem B119639 : Blo 115785 119639 := bstep (se 1 (by rfl) ⟨89729, by rfl⟩ : syracuseStep 119639 = 179459) B179459
theorem B119659 : Blo 115785 119659 := bstep (se 1 (by rfl) ⟨89744, by rfl⟩ : syracuseStep 119659 = 179489) B179489
theorem B119671 : Blo 115785 119671 := bstep (se 1 (by rfl) ⟨89753, by rfl⟩ : syracuseStep 119671 = 179507) B179507
theorem B119691 : Blo 115785 119691 := bstep (se 1 (by rfl) ⟨89768, by rfl⟩ : syracuseStep 119691 = 179537) B179537
theorem B119703 : Blo 115785 119703 := bstep (se 1 (by rfl) ⟨89777, by rfl⟩ : syracuseStep 119703 = 179555) B179555
theorem B119723 : Blo 115785 119723 := bstep (se 1 (by rfl) ⟨89792, by rfl⟩ : syracuseStep 119723 = 179585) B179585
theorem B119735 : Blo 115785 119735 := bstep (se 1 (by rfl) ⟨89801, by rfl⟩ : syracuseStep 119735 = 179603) B179603
theorem B119755 : Blo 115785 119755 := bstep (se 1 (by rfl) ⟨89816, by rfl⟩ : syracuseStep 119755 = 179633) B179633
theorem B119767 : Blo 115785 119767 := bstep (se 1 (by rfl) ⟨89825, by rfl⟩ : syracuseStep 119767 = 179651) B179651
theorem B382103 : Blo 115785 382103 := bstep (se 1 (by rfl) ⟨286577, by rfl⟩ : syracuseStep 382103 = 573155) B573155
theorem B251059 : Blo 115785 251059 := bstep (se 1 (by rfl) ⟨188294, by rfl⟩ : syracuseStep 251059 = 376589) B376589
theorem B1004723 : Blo 115785 1004723 := bstep (se 1 (by rfl) ⟨753542, by rfl⟩ : syracuseStep 1004723 = 1507085) B1507085
theorem B251095 : Blo 115785 251095 := bstep (se 1 (by rfl) ⟨188321, by rfl⟩ : syracuseStep 251095 = 376643) B376643
theorem B185753 : Blo 115785 185753 := bstep (se 2 (by rfl) ⟨69657, by rfl⟩ : syracuseStep 185753 = 139315) B139315
theorem B2020787 : Blo 115785 2020787 := bstep (se 1 (by rfl) ⟨1515590, by rfl⟩ : syracuseStep 2020787 = 3031181) B3031181
theorem B316865 : Blo 115785 316865 := bstep (se 2 (by rfl) ⟨118824, by rfl⟩ : syracuseStep 316865 = 237649) B237649
theorem B218611 : Blo 115785 218611 := bstep (se 1 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 218611 = 327917) B327917
theorem B2119409 : Blo 115785 2119409 := bstep (se 2 (by rfl) ⟨794778, by rfl⟩ : syracuseStep 2119409 = 1589557) B1589557
theorem B677783 : Blo 115785 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B251915 : Blo 115785 251915 := bstep (se 1 (by rfl) ⟨188936, by rfl⟩ : syracuseStep 251915 = 377873) B377873
theorem B448685 : Blo 115785 448685 := bstep (se 3 (by rfl) ⟨84128, by rfl⟩ : syracuseStep 448685 = 168257) B168257
theorem B514307 : Blo 115785 514307 := bstep (se 1 (by rfl) ⟨385730, by rfl⟩ : syracuseStep 514307 = 771461) B771461
theorem B121259 : Blo 115785 121259 := bstep (se 1 (by rfl) ⟨90944, by rfl⟩ : syracuseStep 121259 = 181889) B181889
theorem B842201 : Blo 115785 842201 := bstep (se 2 (by rfl) ⟨315825, by rfl⟩ : syracuseStep 842201 = 631651) B631651
theorem B252659 : Blo 115785 252659 := bstep (se 1 (by rfl) ⟨189494, by rfl⟩ : syracuseStep 252659 = 378989) B378989
theorem B219991 : Blo 115785 219991 := bstep (se 1 (by rfl) ⟨164993, by rfl⟩ : syracuseStep 219991 = 329987) B329987
theorem B449459 : Blo 115785 449459 := bstep (se 1 (by rfl) ⟨337094, by rfl⟩ : syracuseStep 449459 = 674189) B674189
theorem B220097 : Blo 115785 220097 := bstep (se 2 (by rfl) ⟨82536, by rfl⟩ : syracuseStep 220097 = 165073) B165073
theorem B908333 : Blo 115785 908333 := bstep (se 3 (by rfl) ⟨170312, by rfl⟩ : syracuseStep 908333 = 340625) B340625
theorem B220249 : Blo 115785 220249 := bstep (se 2 (by rfl) ⟨82593, by rfl⟩ : syracuseStep 220249 = 165187) B165187
theorem B679063 : Blo 115785 679063 := bstep (se 1 (by rfl) ⟨509297, by rfl⟩ : syracuseStep 679063 = 1018595) B1018595
theorem B318941 : Blo 115785 318941 := bstep (se 3 (by rfl) ⟨59801, by rfl⟩ : syracuseStep 318941 = 119603) B119603
theorem B253505 : Blo 115785 253505 := bstep (se 2 (by rfl) ⟨95064, by rfl⟩ : syracuseStep 253505 = 190129) B190129
theorem B417611 : Blo 115785 417611 := bstep (se 1 (by rfl) ⟨313208, by rfl⟩ : syracuseStep 417611 = 626417) B626417
theorem B1072997 : Blo 115785 1072997 := bstep (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) B201187
theorem B253847 : Blo 115785 253847 := bstep (se 1 (by rfl) ⟨190385, by rfl⟩ : syracuseStep 253847 = 380771) B380771
theorem B221195 : Blo 115785 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B942353 : Blo 115785 942353 := bstep (se 2 (by rfl) ⟨353382, by rfl⟩ : syracuseStep 942353 = 706765) B706765
theorem B221555 : Blo 115785 221555 := bstep (se 1 (by rfl) ⟨166166, by rfl⟩ : syracuseStep 221555 = 332333) B332333
theorem B450947 : Blo 115785 450947 := bstep (se 1 (by rfl) ⟨338210, by rfl⟩ : syracuseStep 450947 = 676421) B676421
theorem B221707 : Blo 115785 221707 := bstep (se 1 (by rfl) ⟨166280, by rfl⟩ : syracuseStep 221707 = 332561) B332561
theorem B1008449 : Blo 115785 1008449 := bstep (se 2 (by rfl) ⟨378168, by rfl⟩ : syracuseStep 1008449 = 756337) B756337
theorem B451403 : Blo 115785 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B222041 : Blo 115785 222041 := bstep (se 2 (by rfl) ⟨83265, by rfl⟩ : syracuseStep 222041 = 166531) B166531
theorem B320345 : Blo 115785 320345 := bstep (se 2 (by rfl) ⟨120129, by rfl⟩ : syracuseStep 320345 = 240259) B240259
theorem B451601 : Blo 115785 451601 := bstep (se 2 (by rfl) ⟨169350, by rfl⟩ : syracuseStep 451601 = 338701) B338701
theorem B124087 : Blo 115785 124087 := bstep (se 1 (by rfl) ⟨93065, by rfl⟩ : syracuseStep 124087 = 186131) B186131
theorem B189719 : Blo 115785 189719 := bstep (se 1 (by rfl) ⟨142289, by rfl⟩ : syracuseStep 189719 = 284579) B284579
theorem B222679 : Blo 115785 222679 := bstep (se 1 (by rfl) ⟨167009, by rfl⟩ : syracuseStep 222679 = 334019) B334019
theorem B189911 : Blo 115785 189911 := bstep (se 1 (by rfl) ⟨142433, by rfl⟩ : syracuseStep 189911 = 284867) B284867
theorem B157145 : Blo 115785 157145 := bstep (se 2 (by rfl) ⟨58929, by rfl⟩ : syracuseStep 157145 = 117859) B117859
theorem B3630563 : Blo 115785 3630563 := bstep (se 1 (by rfl) ⟨2722922, by rfl⟩ : syracuseStep 3630563 = 5445845) B5445845
theorem B714257 : Blo 115785 714257 := bstep (se 2 (by rfl) ⟨267846, by rfl⟩ : syracuseStep 714257 = 535693) B535693
theorem B190039 : Blo 115785 190039 := bstep (se 1 (by rfl) ⟨142529, by rfl⟩ : syracuseStep 190039 = 285059) B285059
theorem B452375 : Blo 115785 452375 := bstep (se 1 (by rfl) ⟨339281, by rfl⟩ : syracuseStep 452375 = 678563) B678563
theorem B452573 : Blo 115785 452573 := bstep (se 3 (by rfl) ⟨84857, by rfl⟩ : syracuseStep 452573 = 169715) B169715
theorem B124907 : Blo 115785 124907 := bstep (se 1 (by rfl) ⟨93680, by rfl⟩ : syracuseStep 124907 = 187361) B187361
theorem B190603 : Blo 115785 190603 := bstep (se 1 (by rfl) ⟨142952, by rfl⟩ : syracuseStep 190603 = 285905) B285905
theorem B223411 : Blo 115785 223411 := bstep (se 1 (by rfl) ⟨167558, by rfl⟩ : syracuseStep 223411 = 335117) B335117
theorem B190679 : Blo 115785 190679 := bstep (se 1 (by rfl) ⟨143009, by rfl⟩ : syracuseStep 190679 = 286019) B286019
theorem B223499 : Blo 115785 223499 := bstep (se 1 (by rfl) ⟨167624, by rfl⟩ : syracuseStep 223499 = 335249) B335249
theorem B223553 : Blo 115785 223553 := bstep (se 2 (by rfl) ⟨83832, by rfl⟩ : syracuseStep 223553 = 167665) B167665
theorem B125975 : Blo 115785 125975 := bstep (se 1 (by rfl) ⟨94481, by rfl⟩ : syracuseStep 125975 = 188963) B188963
theorem B1338443 : Blo 115785 1338443 := bstep (se 1 (by rfl) ⟨1003832, by rfl⟩ : syracuseStep 1338443 = 2007665) B2007665
theorem B224471 : Blo 115785 224471 := bstep (se 1 (by rfl) ⟨168353, by rfl⟩ : syracuseStep 224471 = 336707) B336707
theorem B7925141 : Blo 115785 7925141 := bstep (se 6 (by rfl) ⟨185745, by rfl⟩ : syracuseStep 7925141 = 371491) B371491
theorem B880145 : Blo 115785 880145 := bstep (se 2 (by rfl) ⟨330054, by rfl⟩ : syracuseStep 880145 = 660109) B660109
theorem B224857 : Blo 115785 224857 := bstep (se 2 (by rfl) ⟨84321, by rfl⟩ : syracuseStep 224857 = 168643) B168643
theorem B225011 : Blo 115785 225011 := bstep (se 1 (by rfl) ⟨168758, by rfl⟩ : syracuseStep 225011 = 337517) B337517
theorem B913157 : Blo 115785 913157 := bstep (se 4 (by rfl) ⟨85608, by rfl⟩ : syracuseStep 913157 = 171217) B171217
theorem B454531 : Blo 115785 454531 := bstep (se 1 (by rfl) ⟨340898, by rfl⟩ : syracuseStep 454531 = 681797) B681797
theorem B127051 : Blo 115785 127051 := bstep (se 1 (by rfl) ⟨95288, by rfl⟩ : syracuseStep 127051 = 190577) B190577
theorem B192601 : Blo 115785 192601 := bstep (se 2 (by rfl) ⟨72225, by rfl⟩ : syracuseStep 192601 = 144451) B144451
theorem B1339523 : Blo 115785 1339523 := bstep (se 1 (by rfl) ⟨1004642, by rfl⟩ : syracuseStep 1339523 = 2009285) B2009285
theorem B258263 : Blo 115785 258263 := bstep (se 1 (by rfl) ⟨193697, by rfl⟩ : syracuseStep 258263 = 387395) B387395
theorem B225497 : Blo 115785 225497 := bstep (se 2 (by rfl) ⟨84561, by rfl⟩ : syracuseStep 225497 = 169123) B169123
theorem B291251 : Blo 115785 291251 := bstep (se 1 (by rfl) ⟨218438, by rfl⟩ : syracuseStep 291251 = 436877) B436877
theorem B1274629 : Blo 115785 1274629 := bstep (se 4 (by rfl) ⟨119496, by rfl⟩ : syracuseStep 1274629 = 238993) B238993
theorem B717661 : Blo 115785 717661 := bstep (se 3 (by rfl) ⟨134561, by rfl⟩ : syracuseStep 717661 = 269123) B269123
theorem B357313 : Blo 115785 357313 := bstep (se 2 (by rfl) ⟨133992, by rfl⟩ : syracuseStep 357313 = 267985) B267985
theorem B423299 : Blo 115785 423299 := bstep (se 1 (by rfl) ⟨317474, by rfl⟩ : syracuseStep 423299 = 634949) B634949
theorem B1078829 : Blo 115785 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B226955 : Blo 115785 226955 := bstep (se 1 (by rfl) ⟨170216, by rfl⟩ : syracuseStep 226955 = 340433) B340433
theorem B227137 : Blo 115785 227137 := bstep (se 2 (by rfl) ⟨85176, by rfl⟩ : syracuseStep 227137 = 170353) B170353
theorem B423755 : Blo 115785 423755 := bstep (se 1 (by rfl) ⟨317816, by rfl⟩ : syracuseStep 423755 = 635633) B635633
theorem B129163 : Blo 115785 129163 := bstep (se 1 (by rfl) ⟨96872, by rfl⟩ : syracuseStep 129163 = 193745) B193745
theorem B391499 : Blo 115785 391499 := bstep (se 1 (by rfl) ⟨293624, by rfl⟩ : syracuseStep 391499 = 587249) B587249
theorem B227659 : Blo 115785 227659 := bstep (se 1 (by rfl) ⟨170744, by rfl⟩ : syracuseStep 227659 = 341489) B341489
theorem B260531 : Blo 115785 260531 := bstep (se 1 (by rfl) ⟨195398, by rfl⟩ : syracuseStep 260531 = 390797) B390797
theorem B1014221 : Blo 115785 1014221 := bstep (se 3 (by rfl) ⟨190166, by rfl⟩ : syracuseStep 1014221 = 380333) B380333
theorem B260567 : Blo 115785 260567 := bstep (se 1 (by rfl) ⟨195425, by rfl⟩ : syracuseStep 260567 = 390851) B390851
theorem B391769 : Blo 115785 391769 := bstep (se 2 (by rfl) ⟨146913, by rfl⟩ : syracuseStep 391769 = 293827) B293827
theorem B260747 : Blo 115785 260747 := bstep (se 1 (by rfl) ⟨195560, by rfl⟩ : syracuseStep 260747 = 391121) B391121
theorem B260801 : Blo 115785 260801 := bstep (se 2 (by rfl) ⟨97800, by rfl⟩ : syracuseStep 260801 = 195601) B195601
theorem B1506113 : Blo 115785 1506113 := bstep (se 2 (by rfl) ⟨564792, by rfl⟩ : syracuseStep 1506113 = 1129585) B1129585
theorem B1080139 : Blo 115785 1080139 := bstep (se 1 (by rfl) ⟨810104, by rfl⟩ : syracuseStep 1080139 = 1620209) B1620209
theorem B261017 : Blo 115785 261017 := bstep (se 2 (by rfl) ⟨97881, by rfl⟩ : syracuseStep 261017 = 195763) B195763
theorem B261107 : Blo 115785 261107 := bstep (se 1 (by rfl) ⟨195830, by rfl⟩ : syracuseStep 261107 = 391661) B391661
theorem B261143 : Blo 115785 261143 := bstep (se 1 (by rfl) ⟨195857, by rfl⟩ : syracuseStep 261143 = 391715) B391715
theorem B293939 : Blo 115785 293939 := bstep (se 1 (by rfl) ⟨220454, by rfl⟩ : syracuseStep 293939 = 440909) B440909
theorem B261323 : Blo 115785 261323 := bstep (se 1 (by rfl) ⟨195992, by rfl⟩ : syracuseStep 261323 = 391985) B391985
theorem B261377 : Blo 115785 261377 := bstep (se 2 (by rfl) ⟨98016, by rfl⟩ : syracuseStep 261377 = 196033) B196033
theorem B130315 : Blo 115785 130315 := bstep (se 1 (by rfl) ⟨97736, by rfl⟩ : syracuseStep 130315 = 195473) B195473
theorem B195851 : Blo 115785 195851 := bstep (se 1 (by rfl) ⟨146888, by rfl⟩ : syracuseStep 195851 = 293777) B293777
theorem B392471 : Blo 115785 392471 := bstep (se 1 (by rfl) ⟨294353, by rfl⟩ : syracuseStep 392471 = 588707) B588707
theorem B884033 : Blo 115785 884033 := bstep (se 2 (by rfl) ⟨331512, by rfl⟩ : syracuseStep 884033 = 663025) B663025
theorem B130423 : Blo 115785 130423 := bstep (se 1 (by rfl) ⟨97817, by rfl⟩ : syracuseStep 130423 = 195635) B195635
theorem B195979 : Blo 115785 195979 := bstep (se 1 (by rfl) ⟨146984, by rfl⟩ : syracuseStep 195979 = 293969) B293969
theorem B261593 : Blo 115785 261593 := bstep (se 2 (by rfl) ⟨98097, by rfl⟩ : syracuseStep 261593 = 196195) B196195
theorem B196121 : Blo 115785 196121 := bstep (se 2 (by rfl) ⟨73545, by rfl⟩ : syracuseStep 196121 = 147091) B147091
theorem B130603 : Blo 115785 130603 := bstep (se 1 (by rfl) ⟨97952, by rfl⟩ : syracuseStep 130603 = 195905) B195905
theorem B261683 : Blo 115785 261683 := bstep (se 1 (by rfl) ⟨196262, by rfl⟩ : syracuseStep 261683 = 392525) B392525
theorem B294475 : Blo 115785 294475 := bstep (se 1 (by rfl) ⟨220856, by rfl⟩ : syracuseStep 294475 = 441713) B441713
theorem B261719 : Blo 115785 261719 := bstep (se 1 (by rfl) ⟨196289, by rfl⟩ : syracuseStep 261719 = 392579) B392579
theorem B720485 : Blo 115785 720485 := bstep (se 4 (by rfl) ⟨67545, by rfl⟩ : syracuseStep 720485 = 135091) B135091
theorem B130711 : Blo 115785 130711 := bstep (se 1 (by rfl) ⟨98033, by rfl⟩ : syracuseStep 130711 = 196067) B196067
theorem B196249 : Blo 115785 196249 := bstep (se 2 (by rfl) ⟨73593, by rfl⟩ : syracuseStep 196249 = 147187) B147187
theorem B294617 : Blo 115785 294617 := bstep (se 2 (by rfl) ⟨110481, by rfl⟩ : syracuseStep 294617 = 220963) B220963
theorem B261899 : Blo 115785 261899 := bstep (se 1 (by rfl) ⟨196424, by rfl⟩ : syracuseStep 261899 = 392849) B392849
theorem B393011 : Blo 115785 393011 := bstep (se 1 (by rfl) ⟨294758, by rfl⟩ : syracuseStep 393011 = 589517) B589517
theorem B261953 : Blo 115785 261953 := bstep (se 2 (by rfl) ⟨98232, by rfl⟩ : syracuseStep 261953 = 196465) B196465
theorem B130891 : Blo 115785 130891 := bstep (se 1 (by rfl) ⟨98168, by rfl⟩ : syracuseStep 130891 = 196337) B196337
theorem B425873 : Blo 115785 425873 := bstep (se 2 (by rfl) ⟨159702, by rfl⟩ : syracuseStep 425873 = 319405) B319405
theorem B1343411 : Blo 115785 1343411 := bstep (se 1 (by rfl) ⟨1007558, by rfl⟩ : syracuseStep 1343411 = 2015117) B2015117
theorem B130999 : Blo 115785 130999 := bstep (se 1 (by rfl) ⟨98249, by rfl⟩ : syracuseStep 130999 = 196499) B196499
theorem B393227 : Blo 115785 393227 := bstep (se 1 (by rfl) ⟨294920, by rfl⟩ : syracuseStep 393227 = 589841) B589841
theorem B589853 : Blo 115785 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B262187 : Blo 115785 262187 := bstep (se 1 (by rfl) ⟨196640, by rfl⟩ : syracuseStep 262187 = 393281) B393281
theorem B393335 : Blo 115785 393335 := bstep (se 1 (by rfl) ⟨295001, by rfl⟩ : syracuseStep 393335 = 590003) B590003
theorem B131215 : Blo 115785 131215 := bstep (se 1 (by rfl) ⟨98411, by rfl⟩ : syracuseStep 131215 = 196823) B196823
theorem B262547 : Blo 115785 262547 := bstep (se 1 (by rfl) ⟨196910, by rfl⟩ : syracuseStep 262547 = 393821) B393821
theorem B754105 : Blo 115785 754105 := bstep (se 2 (by rfl) ⟨282789, by rfl⟩ : syracuseStep 754105 = 565579) B565579
theorem B262601 : Blo 115785 262601 := bstep (se 2 (by rfl) ⟨98475, by rfl⟩ : syracuseStep 262601 = 196951) B196951
theorem B295559 : Blo 115785 295559 := bstep (se 1 (by rfl) ⟨221669, by rfl⟩ : syracuseStep 295559 = 443339) B443339
theorem B197255 : Blo 115785 197255 := bstep (se 1 (by rfl) ⟨147941, by rfl⟩ : syracuseStep 197255 = 295883) B295883
theorem B131719 : Blo 115785 131719 := bstep (se 1 (by rfl) ⟨98789, by rfl⟩ : syracuseStep 131719 = 197579) B197579
theorem B295609 : Blo 115785 295609 := bstep (se 2 (by rfl) ⟨110853, by rfl⟩ : syracuseStep 295609 = 221707) B221707
theorem B393929 : Blo 115785 393929 := bstep (se 2 (by rfl) ⟨147723, by rfl⟩ : syracuseStep 393929 = 295447) B295447
theorem B590651 : Blo 115785 590651 := bstep (se 1 (by rfl) ⟨442988, by rfl⟩ : syracuseStep 590651 = 885977) B885977
theorem B131899 : Blo 115785 131899 := bstep (se 1 (by rfl) ⟨98924, by rfl⟩ : syracuseStep 131899 = 197849) B197849
theorem B3343193 : Blo 115785 3343193 := bstep (se 2 (by rfl) ⟨1253697, by rfl⟩ : syracuseStep 3343193 = 2507395) B2507395
theorem B590813 : Blo 115785 590813 := bstep (se 3 (by rfl) ⟨110777, by rfl⟩ : syracuseStep 590813 = 221555) B221555
theorem B3245143 : Blo 115785 3245143 := bstep (se 1 (by rfl) ⟨2433857, by rfl⟩ : syracuseStep 3245143 = 4867715) B4867715
theorem B263303 : Blo 115785 263303 := bstep (se 1 (by rfl) ⟨197477, by rfl⟩ : syracuseStep 263303 = 394955) B394955
theorem B296207 : Blo 115785 296207 := bstep (se 1 (by rfl) ⟨222155, by rfl⟩ : syracuseStep 296207 = 444311) B444311
theorem B197903 : Blo 115785 197903 := bstep (se 1 (by rfl) ⟨148427, by rfl⟩ : syracuseStep 197903 = 296855) B296855
theorem B132367 : Blo 115785 132367 := bstep (se 1 (by rfl) ⟨99275, by rfl⟩ : syracuseStep 132367 = 198551) B198551
theorem B591137 : Blo 115785 591137 := bstep (se 2 (by rfl) ⟨221676, by rfl⟩ : syracuseStep 591137 = 443353) B443353
theorem B263483 : Blo 115785 263483 := bstep (se 1 (by rfl) ⟨197612, by rfl⟩ : syracuseStep 263483 = 395225) B395225
theorem B394631 : Blo 115785 394631 := bstep (se 1 (by rfl) ⟨295973, by rfl⟩ : syracuseStep 394631 = 591947) B591947
theorem B1082771 : Blo 115785 1082771 := bstep (se 1 (by rfl) ⟨812078, by rfl⟩ : syracuseStep 1082771 = 1624157) B1624157
theorem B263609 : Blo 115785 263609 := bstep (se 2 (by rfl) ⟨98853, by rfl⟩ : syracuseStep 263609 = 197707) B197707
theorem B1148381 : Blo 115785 1148381 := bstep (se 3 (by rfl) ⟨215321, by rfl⟩ : syracuseStep 1148381 = 430643) B430643
theorem B165449 : Blo 115785 165449 := bstep (se 2 (by rfl) ⟨62043, by rfl⟩ : syracuseStep 165449 = 124087) B124087
theorem B395009 : Blo 115785 395009 := bstep (se 2 (by rfl) ⟨148128, by rfl⟩ : syracuseStep 395009 = 296257) B296257
theorem B132871 : Blo 115785 132871 := bstep (se 1 (by rfl) ⟨99653, by rfl⟩ : syracuseStep 132871 = 199307) B199307
theorem B198415 : Blo 115785 198415 := bstep (se 1 (by rfl) ⟨148811, by rfl⟩ : syracuseStep 198415 = 297623) B297623
theorem B263951 : Blo 115785 263951 := bstep (se 1 (by rfl) ⟨197963, by rfl⟩ : syracuseStep 263951 = 395927) B395927
theorem B263969 : Blo 115785 263969 := bstep (se 2 (by rfl) ⟨98988, by rfl⟩ : syracuseStep 263969 = 197977) B197977
theorem B198443 : Blo 115785 198443 := bstep (se 1 (by rfl) ⟨148832, by rfl⟩ : syracuseStep 198443 = 297665) B297665
theorem B133051 : Blo 115785 133051 := bstep (se 1 (by rfl) ⟨99788, by rfl⟩ : syracuseStep 133051 = 199577) B199577
theorem B296905 : Blo 115785 296905 := bstep (se 2 (by rfl) ⟨111339, by rfl⟩ : syracuseStep 296905 = 222679) B222679
theorem B1607627 : Blo 115785 1607627 := bstep (se 1 (by rfl) ⟨1205720, by rfl⟩ : syracuseStep 1607627 = 2411441) B2411441
theorem B329771 : Blo 115785 329771 := bstep (se 1 (by rfl) ⟨247328, by rfl⟩ : syracuseStep 329771 = 494657) B494657
theorem B297047 : Blo 115785 297047 := bstep (se 1 (by rfl) ⟨222785, by rfl⟩ : syracuseStep 297047 = 445571) B445571
theorem B166007 : Blo 115785 166007 := bstep (se 1 (by rfl) ⟨124505, by rfl⟩ : syracuseStep 166007 = 249011) B249011
theorem B264311 : Blo 115785 264311 := bstep (se 1 (by rfl) ⟨198233, by rfl⟩ : syracuseStep 264311 = 396467) B396467
theorem B198841 : Blo 115785 198841 := bstep (se 2 (by rfl) ⟨74565, by rfl⟩ : syracuseStep 198841 = 149131) B149131
theorem B592109 : Blo 115785 592109 := bstep (se 3 (by rfl) ⟨111020, by rfl⟩ : syracuseStep 592109 = 222041) B222041
theorem B2033909 : Blo 115785 2033909 := bstep (se 5 (by rfl) ⟨95339, by rfl⟩ : syracuseStep 2033909 = 190679) B190679
theorem B264491 : Blo 115785 264491 := bstep (se 1 (by rfl) ⟨198368, by rfl⟩ : syracuseStep 264491 = 396737) B396737
theorem B133519 : Blo 115785 133519 := bstep (se 1 (by rfl) ⟨100139, by rfl⟩ : syracuseStep 133519 = 200279) B200279
theorem B559507 : Blo 115785 559507 := bstep (se 1 (by rfl) ⟨419630, by rfl⟩ : syracuseStep 559507 = 839261) B839261
theorem B166315 : Blo 115785 166315 := bstep (se 1 (by rfl) ⟨124736, by rfl⟩ : syracuseStep 166315 = 249473) B249473
theorem B330169 : Blo 115785 330169 := bstep (se 2 (by rfl) ⟨123813, by rfl⟩ : syracuseStep 330169 = 247627) B247627
theorem B395819 : Blo 115785 395819 := bstep (se 1 (by rfl) ⟨296864, by rfl⟩ : syracuseStep 395819 = 593729) B593729
theorem B264851 : Blo 115785 264851 := bstep (se 1 (by rfl) ⟨198638, by rfl⟩ : syracuseStep 264851 = 397277) B397277
theorem B264905 : Blo 115785 264905 := bstep (se 2 (by rfl) ⟨99339, by rfl⟩ : syracuseStep 264905 = 198679) B198679
theorem B1018639 : Blo 115785 1018639 := bstep (se 1 (by rfl) ⟨763979, by rfl⟩ : syracuseStep 1018639 = 1527959) B1527959
theorem B428915 : Blo 115785 428915 := bstep (se 1 (by rfl) ⟨321686, by rfl⟩ : syracuseStep 428915 = 643373) B643373
theorem B199543 : Blo 115785 199543 := bstep (se 1 (by rfl) ⟨149657, by rfl⟩ : syracuseStep 199543 = 299315) B299315
theorem B134023 : Blo 115785 134023 := bstep (se 1 (by rfl) ⟨100517, by rfl⟩ : syracuseStep 134023 = 201035) B201035
theorem B166799 : Blo 115785 166799 := bstep (se 1 (by rfl) ⟨125099, by rfl⟩ : syracuseStep 166799 = 250199) B250199
theorem B297881 : Blo 115785 297881 := bstep (se 2 (by rfl) ⟨111705, by rfl⟩ : syracuseStep 297881 = 223411) B223411
theorem B1281035 : Blo 115785 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B592919 : Blo 115785 592919 := bstep (se 1 (by rfl) ⟨444689, by rfl⟩ : syracuseStep 592919 = 889379) B889379
theorem B1149997 : Blo 115785 1149997 := bstep (se 3 (by rfl) ⟨215624, by rfl⟩ : syracuseStep 1149997 = 431249) B431249
theorem B199739 : Blo 115785 199739 := bstep (se 1 (by rfl) ⟨149804, by rfl⟩ : syracuseStep 199739 = 299609) B299609
theorem B134203 : Blo 115785 134203 := bstep (se 1 (by rfl) ⟨100652, by rfl⟩ : syracuseStep 134203 = 201305) B201305
theorem B756823 : Blo 115785 756823 := bstep (se 1 (by rfl) ⟨567617, by rfl⟩ : syracuseStep 756823 = 1135235) B1135235
theorem B265607 : Blo 115785 265607 := bstep (se 1 (by rfl) ⟨199205, by rfl⟩ : syracuseStep 265607 = 398411) B398411
theorem B200137 : Blo 115785 200137 := bstep (se 2 (by rfl) ⟨75051, by rfl⟩ : syracuseStep 200137 = 150103) B150103
theorem B134671 : Blo 115785 134671 := bstep (se 1 (by rfl) ⟨101003, by rfl⟩ : syracuseStep 134671 = 202007) B202007
theorem B265787 : Blo 115785 265787 := bstep (se 1 (by rfl) ⟨199340, by rfl⟩ : syracuseStep 265787 = 398681) B398681
theorem B1347191 : Blo 115785 1347191 := bstep (se 1 (by rfl) ⟨1010393, by rfl⟩ : syracuseStep 1347191 = 2020787) B2020787
theorem B331411 : Blo 115785 331411 := bstep (se 1 (by rfl) ⟨248558, by rfl⟩ : syracuseStep 331411 = 497117) B497117
theorem B265913 : Blo 115785 265913 := bstep (se 2 (by rfl) ⟨99717, by rfl⟩ : syracuseStep 265913 = 199435) B199435
theorem B495341 : Blo 115785 495341 := bstep (se 3 (by rfl) ⟨92876, by rfl⟩ : syracuseStep 495341 = 185753) B185753
theorem B397115 : Blo 115785 397115 := bstep (se 1 (by rfl) ⟨297836, by rfl⟩ : syracuseStep 397115 = 595673) B595673
theorem B1412939 : Blo 115785 1412939 := bstep (se 1 (by rfl) ⟨1059704, by rfl⟩ : syracuseStep 1412939 = 2119409) B2119409
theorem B135055 : Blo 115785 135055 := bstep (se 1 (by rfl) ⟨101291, by rfl⟩ : syracuseStep 135055 = 202583) B202583
theorem B266255 : Blo 115785 266255 := bstep (se 1 (by rfl) ⟨199691, by rfl⟩ : syracuseStep 266255 = 399383) B399383
theorem B266273 : Blo 115785 266273 := bstep (se 2 (by rfl) ⟨99852, by rfl⟩ : syracuseStep 266273 = 199705) B199705
theorem B888893 : Blo 115785 888893 := bstep (se 3 (by rfl) ⟨166667, by rfl⟩ : syracuseStep 888893 = 333335) B333335
theorem B299123 : Blo 115785 299123 := bstep (se 1 (by rfl) ⟨224342, by rfl⟩ : syracuseStep 299123 = 448685) B448685
theorem B200839 : Blo 115785 200839 := bstep (se 1 (by rfl) ⟨150629, by rfl⟩ : syracuseStep 200839 = 301259) B301259
theorem B266387 : Blo 115785 266387 := bstep (se 1 (by rfl) ⟨199790, by rfl⟩ : syracuseStep 266387 = 399581) B399581
theorem B135355 : Blo 115785 135355 := bstep (se 1 (by rfl) ⟨101516, by rfl⟩ : syracuseStep 135355 = 203033) B203033
theorem B397601 : Blo 115785 397601 := bstep (se 2 (by rfl) ⟨149100, by rfl⟩ : syracuseStep 397601 = 298201) B298201
theorem B561467 : Blo 115785 561467 := bstep (se 1 (by rfl) ⟨421100, by rfl⟩ : syracuseStep 561467 = 842201) B842201
theorem B266615 : Blo 115785 266615 := bstep (se 1 (by rfl) ⟨199961, by rfl⟩ : syracuseStep 266615 = 399923) B399923
theorem B266795 : Blo 115785 266795 := bstep (se 1 (by rfl) ⟨200096, by rfl⟩ : syracuseStep 266795 = 400193) B400193
theorem B299639 : Blo 115785 299639 := bstep (se 1 (by rfl) ⟨224729, by rfl⟩ : syracuseStep 299639 = 449459) B449459
theorem B201487 : Blo 115785 201487 := bstep (se 1 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 201487 = 302231) B302231
theorem B299809 : Blo 115785 299809 := bstep (se 2 (by rfl) ⟨112428, by rfl⟩ : syracuseStep 299809 = 224857) B224857
theorem B398195 : Blo 115785 398195 := bstep (se 1 (by rfl) ⟨298646, by rfl⟩ : syracuseStep 398195 = 597293) B597293
theorem B267155 : Blo 115785 267155 := bstep (se 1 (by rfl) ⟨200366, by rfl⟩ : syracuseStep 267155 = 400733) B400733
theorem B1676213 : Blo 115785 1676213 := bstep (se 5 (by rfl) ⟨78572, by rfl⟩ : syracuseStep 1676213 = 157145) B157145
theorem B267209 : Blo 115785 267209 := bstep (se 2 (by rfl) ⟨100203, by rfl⟩ : syracuseStep 267209 = 200407) B200407
theorem B169003 : Blo 115785 169003 := bstep (se 1 (by rfl) ⟨126752, by rfl⟩ : syracuseStep 169003 = 253505) B253505
theorem B169231 : Blo 115785 169231 := bstep (se 1 (by rfl) ⟨126923, by rfl⟩ : syracuseStep 169231 = 253847) B253847
theorem B333085 : Blo 115785 333085 := bstep (se 3 (by rfl) ⟨62453, by rfl⟩ : syracuseStep 333085 = 124907) B124907
theorem B202027 : Blo 115785 202027 := bstep (se 1 (by rfl) ⟨151520, by rfl⟩ : syracuseStep 202027 = 303041) B303041
theorem B333143 : Blo 115785 333143 := bstep (se 1 (by rfl) ⟨249857, by rfl⟩ : syracuseStep 333143 = 499715) B499715
theorem B3478963 : Blo 115785 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B628235 : Blo 115785 628235 := bstep (se 1 (by rfl) ⟨471176, by rfl⟩ : syracuseStep 628235 = 942353) B942353
theorem B300631 : Blo 115785 300631 := bstep (se 1 (by rfl) ⟨225473, by rfl⟩ : syracuseStep 300631 = 450947) B450947
theorem B267911 : Blo 115785 267911 := bstep (se 1 (by rfl) ⟨200933, by rfl⟩ : syracuseStep 267911 = 401867) B401867
theorem B497441 : Blo 115785 497441 := bstep (se 2 (by rfl) ⟨186540, by rfl⟩ : syracuseStep 497441 = 373081) B373081
theorem B268091 : Blo 115785 268091 := bstep (se 1 (by rfl) ⟨201068, by rfl⟩ : syracuseStep 268091 = 402137) B402137
theorem B300935 : Blo 115785 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B268217 : Blo 115785 268217 := bstep (se 2 (by rfl) ⟨100581, by rfl⟩ : syracuseStep 268217 = 201163) B201163
theorem B301067 : Blo 115785 301067 := bstep (se 1 (by rfl) ⟨225800, by rfl⟩ : syracuseStep 301067 = 451601) B451601
theorem B595997 : Blo 115785 595997 := bstep (se 3 (by rfl) ⟨111749, by rfl⟩ : syracuseStep 595997 = 223499) B223499
theorem B268559 : Blo 115785 268559 := bstep (se 1 (by rfl) ⟨201419, by rfl⟩ : syracuseStep 268559 = 402839) B402839
theorem B268577 : Blo 115785 268577 := bstep (se 2 (by rfl) ⟨100716, by rfl⟩ : syracuseStep 268577 = 201433) B201433
theorem B956881 : Blo 115785 956881 := bstep (se 2 (by rfl) ⟨358830, by rfl⟩ : syracuseStep 956881 = 717661) B717661
theorem B596483 : Blo 115785 596483 := bstep (se 1 (by rfl) ⟨447362, by rfl⟩ : syracuseStep 596483 = 894725) B894725
theorem B301583 : Blo 115785 301583 := bstep (se 1 (by rfl) ⟨226187, by rfl⟩ : syracuseStep 301583 = 452375) B452375
theorem B268919 : Blo 115785 268919 := bstep (se 1 (by rfl) ⟨201689, by rfl⟩ : syracuseStep 268919 = 403379) B403379
theorem B301715 : Blo 115785 301715 := bstep (se 1 (by rfl) ⟨226286, by rfl⟩ : syracuseStep 301715 = 452573) B452573
theorem B269099 : Blo 115785 269099 := bstep (se 1 (by rfl) ⟨201824, by rfl⟩ : syracuseStep 269099 = 403649) B403649
theorem B334745 : Blo 115785 334745 := bstep (se 2 (by rfl) ⟨125529, by rfl⟩ : syracuseStep 334745 = 251059) B251059
theorem B334793 : Blo 115785 334793 := bstep (se 2 (by rfl) ⟨125547, by rfl⟩ : syracuseStep 334793 = 251095) B251095
theorem B269459 : Blo 115785 269459 := bstep (se 1 (by rfl) ⟨202094, by rfl⟩ : syracuseStep 269459 = 404189) B404189
theorem B269513 : Blo 115785 269513 := bstep (se 2 (by rfl) ⟨101067, by rfl⟩ : syracuseStep 269513 = 202135) B202135
theorem B662843 : Blo 115785 662843 := bstep (se 1 (by rfl) ⟨497132, by rfl⟩ : syracuseStep 662843 = 994265) B994265
theorem B892295 : Blo 115785 892295 := bstep (se 1 (by rfl) ⟨669221, by rfl⟩ : syracuseStep 892295 = 1338443) B1338443
theorem B400787 : Blo 115785 400787 := bstep (se 1 (by rfl) ⟨300590, by rfl⟩ : syracuseStep 400787 = 601181) B601181
theorem B5283427 : Blo 115785 5283427 := bstep (se 1 (by rfl) ⟨3962570, by rfl⟩ : syracuseStep 5283427 = 7925141) B7925141
theorem B302849 : Blo 115785 302849 := bstep (se 2 (by rfl) ⟨113568, by rfl⟩ : syracuseStep 302849 = 227137) B227137
theorem B335659 : Blo 115785 335659 := bstep (se 1 (by rfl) ⟨251744, by rfl⟩ : syracuseStep 335659 = 503489) B503489
theorem B335933 : Blo 115785 335933 := bstep (se 3 (by rfl) ⟨62987, by rfl⟩ : syracuseStep 335933 = 125975) B125975
theorem B598103 : Blo 115785 598103 := bstep (se 1 (by rfl) ⟨448577, by rfl⟩ : syracuseStep 598103 = 897155) B897155
theorem B893015 : Blo 115785 893015 := bstep (se 1 (by rfl) ⟨669761, by rfl⟩ : syracuseStep 893015 = 1339523) B1339523
theorem B172175 : Blo 115785 172175 := bstep (se 1 (by rfl) ⟨129131, by rfl⟩ : syracuseStep 172175 = 258263) B258263
theorem B172217 : Blo 115785 172217 := bstep (se 2 (by rfl) ⟨64581, by rfl⟩ : syracuseStep 172217 = 129163) B129163
theorem B336275 : Blo 115785 336275 := bstep (se 1 (by rfl) ⟨252206, by rfl⟩ : syracuseStep 336275 = 504413) B504413
theorem B303545 : Blo 115785 303545 := bstep (se 2 (by rfl) ⟨113829, by rfl⟩ : syracuseStep 303545 = 227659) B227659
theorem B598589 : Blo 115785 598589 := bstep (se 3 (by rfl) ⟨112235, by rfl⟩ : syracuseStep 598589 = 224471) B224471
theorem B1319489 : Blo 115785 1319489 := bstep (se 2 (by rfl) ⟨494808, by rfl⟩ : syracuseStep 1319489 = 989617) B989617
theorem B664301 : Blo 115785 664301 := bstep (se 3 (by rfl) ⟨124556, by rfl⟩ : syracuseStep 664301 = 249113) B249113
theorem B402191 : Blo 115785 402191 := bstep (se 1 (by rfl) ⟨301643, by rfl⟩ : syracuseStep 402191 = 603287) B603287
theorem B402461 : Blo 115785 402461 := bstep (se 3 (by rfl) ⟨75461, by rfl⟩ : syracuseStep 402461 = 150923) B150923
theorem B173687 : Blo 115785 173687 := bstep (se 1 (by rfl) ⟨130265, by rfl⟩ : syracuseStep 173687 = 260531) B260531
theorem B173711 : Blo 115785 173711 := bstep (se 1 (by rfl) ⟨130283, by rfl⟩ : syracuseStep 173711 = 260567) B260567
theorem B173753 : Blo 115785 173753 := bstep (se 2 (by rfl) ⟨65157, by rfl⟩ : syracuseStep 173753 = 130315) B130315
theorem B173831 : Blo 115785 173831 := bstep (se 1 (by rfl) ⟨130373, by rfl⟩ : syracuseStep 173831 = 260747) B260747
theorem B173867 : Blo 115785 173867 := bstep (se 1 (by rfl) ⟨130400, by rfl⟩ : syracuseStep 173867 = 260801) B260801
theorem B173897 : Blo 115785 173897 := bstep (se 2 (by rfl) ⟨65211, by rfl⟩ : syracuseStep 173897 = 130423) B130423
theorem B174011 : Blo 115785 174011 := bstep (se 1 (by rfl) ⟨130508, by rfl⟩ : syracuseStep 174011 = 261017) B261017
theorem B501713 : Blo 115785 501713 := bstep (se 2 (by rfl) ⟨188142, by rfl⟩ : syracuseStep 501713 = 376285) B376285
theorem B174071 : Blo 115785 174071 := bstep (se 1 (by rfl) ⟨130553, by rfl⟩ : syracuseStep 174071 = 261107) B261107
theorem B174095 : Blo 115785 174095 := bstep (se 1 (by rfl) ⟨130571, by rfl⟩ : syracuseStep 174095 = 261143) B261143
theorem B174137 : Blo 115785 174137 := bstep (se 2 (by rfl) ⟨65301, by rfl⟩ : syracuseStep 174137 = 130603) B130603
theorem B174215 : Blo 115785 174215 := bstep (se 1 (by rfl) ⟨130661, by rfl⟩ : syracuseStep 174215 = 261323) B261323
theorem B174251 : Blo 115785 174251 := bstep (se 1 (by rfl) ⟨130688, by rfl⟩ : syracuseStep 174251 = 261377) B261377
theorem B174281 : Blo 115785 174281 := bstep (se 2 (by rfl) ⟨65355, by rfl⟩ : syracuseStep 174281 = 130711) B130711
theorem B141583 : Blo 115785 141583 := bstep (se 1 (by rfl) ⟨106187, by rfl⟩ : syracuseStep 141583 = 212375) B212375
theorem B600371 : Blo 115785 600371 := bstep (se 1 (by rfl) ⟨450278, by rfl⟩ : syracuseStep 600371 = 900557) B900557
theorem B174395 : Blo 115785 174395 := bstep (se 1 (by rfl) ⟨130796, by rfl⟩ : syracuseStep 174395 = 261593) B261593
theorem B174455 : Blo 115785 174455 := bstep (se 1 (by rfl) ⟨130841, by rfl⟩ : syracuseStep 174455 = 261683) B261683
theorem B174479 : Blo 115785 174479 := bstep (se 1 (by rfl) ⟨130859, by rfl⟩ : syracuseStep 174479 = 261719) B261719
theorem B403865 : Blo 115785 403865 := bstep (se 2 (by rfl) ⟨151449, by rfl⟩ : syracuseStep 403865 = 302899) B302899
theorem B174521 : Blo 115785 174521 := bstep (se 2 (by rfl) ⟨65445, by rfl⟩ : syracuseStep 174521 = 130891) B130891
theorem B2238941 : Blo 115785 2238941 := bstep (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) B839603
theorem B174599 : Blo 115785 174599 := bstep (se 1 (by rfl) ⟨130949, by rfl⟩ : syracuseStep 174599 = 261899) B261899
theorem B174635 : Blo 115785 174635 := bstep (se 1 (by rfl) ⟨130976, by rfl⟩ : syracuseStep 174635 = 261953) B261953
theorem B174665 : Blo 115785 174665 := bstep (se 2 (by rfl) ⟨65499, by rfl⟩ : syracuseStep 174665 = 130999) B130999
theorem B338519 : Blo 115785 338519 := bstep (se 1 (by rfl) ⟨253889, by rfl⟩ : syracuseStep 338519 = 507779) B507779
theorem B895607 : Blo 115785 895607 := bstep (se 1 (by rfl) ⟨671705, by rfl⟩ : syracuseStep 895607 = 1343411) B1343411
theorem B600695 : Blo 115785 600695 := bstep (se 1 (by rfl) ⟨450521, by rfl⟩ : syracuseStep 600695 = 901043) B901043
theorem B174779 : Blo 115785 174779 := bstep (se 1 (by rfl) ⟨131084, by rfl⟩ : syracuseStep 174779 = 262169) B262169
theorem B174839 : Blo 115785 174839 := bstep (se 1 (by rfl) ⟨131129, by rfl⟩ : syracuseStep 174839 = 262259) B262259
theorem B174863 : Blo 115785 174863 := bstep (se 1 (by rfl) ⟨131147, by rfl⟩ : syracuseStep 174863 = 262295) B262295
theorem B174905 : Blo 115785 174905 := bstep (se 2 (by rfl) ⟨65589, by rfl⟩ : syracuseStep 174905 = 131179) B131179
theorem B174983 : Blo 115785 174983 := bstep (se 1 (by rfl) ⟨131237, by rfl⟩ : syracuseStep 174983 = 262475) B262475
theorem B175019 : Blo 115785 175019 := bstep (se 1 (by rfl) ⟨131264, by rfl⟩ : syracuseStep 175019 = 262529) B262529
theorem B175049 : Blo 115785 175049 := bstep (se 2 (by rfl) ⟨65643, by rfl⟩ : syracuseStep 175049 = 131287) B131287
theorem B175163 : Blo 115785 175163 := bstep (se 1 (by rfl) ⟨131372, by rfl⟩ : syracuseStep 175163 = 262745) B262745
theorem B175223 : Blo 115785 175223 := bstep (se 1 (by rfl) ⟨131417, by rfl⟩ : syracuseStep 175223 = 262835) B262835
theorem B175247 : Blo 115785 175247 := bstep (se 1 (by rfl) ⟨131435, by rfl⟩ : syracuseStep 175247 = 262871) B262871
theorem B175289 : Blo 115785 175289 := bstep (se 2 (by rfl) ⟨65733, by rfl⟩ : syracuseStep 175289 = 131467) B131467
theorem B175367 : Blo 115785 175367 := bstep (se 1 (by rfl) ⟨131525, by rfl⟩ : syracuseStep 175367 = 263051) B263051
theorem B175403 : Blo 115785 175403 := bstep (se 1 (by rfl) ⟨131552, by rfl⟩ : syracuseStep 175403 = 263105) B263105
theorem B175433 : Blo 115785 175433 := bstep (se 2 (by rfl) ⟨65787, by rfl⟩ : syracuseStep 175433 = 131575) B131575
theorem B503225 : Blo 115785 503225 := bstep (se 2 (by rfl) ⟨188709, by rfl⟩ : syracuseStep 503225 = 377419) B377419
theorem B175547 : Blo 115785 175547 := bstep (se 1 (by rfl) ⟨131660, by rfl⟩ : syracuseStep 175547 = 263321) B263321
theorem B175607 : Blo 115785 175607 := bstep (se 1 (by rfl) ⟨131705, by rfl⟩ : syracuseStep 175607 = 263411) B263411
theorem B372235 : Blo 115785 372235 := bstep (se 1 (by rfl) ⟨279176, by rfl⟩ : syracuseStep 372235 = 558353) B558353
theorem B175631 : Blo 115785 175631 := bstep (se 1 (by rfl) ⟨131723, by rfl⟩ : syracuseStep 175631 = 263447) B263447
theorem B175673 : Blo 115785 175673 := bstep (se 2 (by rfl) ⟨65877, by rfl⟩ : syracuseStep 175673 = 131755) B131755
theorem B601667 : Blo 115785 601667 := bstep (se 1 (by rfl) ⟨451250, by rfl⟩ : syracuseStep 601667 = 902501) B902501
theorem B175751 : Blo 115785 175751 := bstep (se 1 (by rfl) ⟨131813, by rfl⟩ : syracuseStep 175751 = 263627) B263627
theorem B175787 : Blo 115785 175787 := bstep (se 1 (by rfl) ⟨131840, by rfl⟩ : syracuseStep 175787 = 263681) B263681
theorem B175817 : Blo 115785 175817 := bstep (se 2 (by rfl) ⟨65931, by rfl⟩ : syracuseStep 175817 = 131863) B131863
theorem B175931 : Blo 115785 175931 := bstep (se 1 (by rfl) ⟨131948, by rfl⟩ : syracuseStep 175931 = 263897) B263897
theorem B175991 : Blo 115785 175991 := bstep (se 1 (by rfl) ⟨131993, by rfl⟩ : syracuseStep 175991 = 263987) B263987
theorem B601991 : Blo 115785 601991 := bstep (se 1 (by rfl) ⟨451493, by rfl⟩ : syracuseStep 601991 = 902987) B902987
theorem B176015 : Blo 115785 176015 := bstep (se 1 (by rfl) ⟨132011, by rfl⟩ : syracuseStep 176015 = 264023) B264023
theorem B176057 : Blo 115785 176057 := bstep (se 2 (by rfl) ⟨66021, by rfl⟩ : syracuseStep 176057 = 132043) B132043
theorem B176135 : Blo 115785 176135 := bstep (se 1 (by rfl) ⟨132101, by rfl⟩ : syracuseStep 176135 = 264203) B264203
theorem B143375 : Blo 115785 143375 := bstep (se 1 (by rfl) ⟨107531, by rfl⟩ : syracuseStep 143375 = 215063) B215063
theorem B176171 : Blo 115785 176171 := bstep (se 1 (by rfl) ⟨132128, by rfl⟩ : syracuseStep 176171 = 264257) B264257
theorem B176201 : Blo 115785 176201 := bstep (se 2 (by rfl) ⟨66075, by rfl⟩ : syracuseStep 176201 = 132151) B132151
theorem B176315 : Blo 115785 176315 := bstep (se 1 (by rfl) ⟨132236, by rfl⟩ : syracuseStep 176315 = 264473) B264473
theorem B176375 : Blo 115785 176375 := bstep (se 1 (by rfl) ⟨132281, by rfl⟩ : syracuseStep 176375 = 264563) B264563
theorem B176399 : Blo 115785 176399 := bstep (se 1 (by rfl) ⟨132299, by rfl⟩ : syracuseStep 176399 = 264599) B264599
theorem B176441 : Blo 115785 176441 := bstep (se 2 (by rfl) ⟨66165, by rfl⟩ : syracuseStep 176441 = 132331) B132331
theorem B176519 : Blo 115785 176519 := bstep (se 1 (by rfl) ⟨132389, by rfl⟩ : syracuseStep 176519 = 264779) B264779
theorem B3322259 : Blo 115785 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B176555 : Blo 115785 176555 := bstep (se 1 (by rfl) ⟨132416, by rfl⟩ : syracuseStep 176555 = 264833) B264833
theorem B176569 : Blo 115785 176569 := bstep (se 2 (by rfl) ⟨66213, by rfl⟩ : syracuseStep 176569 = 132427) B132427
theorem B176585 : Blo 115785 176585 := bstep (se 2 (by rfl) ⟨66219, by rfl⟩ : syracuseStep 176585 = 132439) B132439
theorem B176699 : Blo 115785 176699 := bstep (se 1 (by rfl) ⟨132524, by rfl⟩ : syracuseStep 176699 = 265049) B265049
theorem B176759 : Blo 115785 176759 := bstep (se 1 (by rfl) ⟨132569, by rfl⟩ : syracuseStep 176759 = 265139) B265139
theorem B176783 : Blo 115785 176783 := bstep (se 1 (by rfl) ⟨132587, by rfl⟩ : syracuseStep 176783 = 265175) B265175
theorem B176825 : Blo 115785 176825 := bstep (se 2 (by rfl) ⟨66309, by rfl⟩ : syracuseStep 176825 = 132619) B132619
theorem B176903 : Blo 115785 176903 := bstep (se 1 (by rfl) ⟨132677, by rfl⟩ : syracuseStep 176903 = 265355) B265355
theorem B176939 : Blo 115785 176939 := bstep (se 1 (by rfl) ⟨132704, by rfl⟩ : syracuseStep 176939 = 265409) B265409
theorem B176969 : Blo 115785 176969 := bstep (se 2 (by rfl) ⟨66363, by rfl⟩ : syracuseStep 176969 = 132727) B132727
theorem B177083 : Blo 115785 177083 := bstep (se 1 (by rfl) ⟨132812, by rfl⟩ : syracuseStep 177083 = 265625) B265625
theorem B177143 : Blo 115785 177143 := bstep (se 1 (by rfl) ⟨132857, by rfl⟩ : syracuseStep 177143 = 265715) B265715
theorem B668675 : Blo 115785 668675 := bstep (se 1 (by rfl) ⟨501506, by rfl⟩ : syracuseStep 668675 = 1003013) B1003013
theorem B177167 : Blo 115785 177167 := bstep (se 1 (by rfl) ⟨132875, by rfl⟩ : syracuseStep 177167 = 265751) B265751
theorem B177209 : Blo 115785 177209 := bstep (se 2 (by rfl) ⟨66453, by rfl⟩ : syracuseStep 177209 = 132907) B132907
theorem B177287 : Blo 115785 177287 := bstep (se 1 (by rfl) ⟨132965, by rfl⟩ : syracuseStep 177287 = 265931) B265931
theorem B177323 : Blo 115785 177323 := bstep (se 1 (by rfl) ⟨132992, by rfl⟩ : syracuseStep 177323 = 265985) B265985
theorem B177353 : Blo 115785 177353 := bstep (se 2 (by rfl) ⟨66507, by rfl⟩ : syracuseStep 177353 = 133015) B133015
theorem B177467 : Blo 115785 177467 := bstep (se 1 (by rfl) ⟨133100, by rfl⟩ : syracuseStep 177467 = 266201) B266201
theorem B177527 : Blo 115785 177527 := bstep (se 1 (by rfl) ⟨133145, by rfl⟩ : syracuseStep 177527 = 266291) B266291
theorem B177551 : Blo 115785 177551 := bstep (se 1 (by rfl) ⟨133163, by rfl⟩ : syracuseStep 177551 = 266327) B266327
theorem B177593 : Blo 115785 177593 := bstep (se 2 (by rfl) ⟨66597, by rfl⟩ : syracuseStep 177593 = 133195) B133195
theorem B243145 : Blo 115785 243145 := bstep (se 2 (by rfl) ⟨91179, by rfl⟩ : syracuseStep 243145 = 182359) B182359
theorem B669131 : Blo 115785 669131 := bstep (se 1 (by rfl) ⟨501848, by rfl⟩ : syracuseStep 669131 = 1003697) B1003697
theorem B177671 : Blo 115785 177671 := bstep (se 1 (by rfl) ⟨133253, by rfl⟩ : syracuseStep 177671 = 266507) B266507
theorem B177707 : Blo 115785 177707 := bstep (se 1 (by rfl) ⟨133280, by rfl⟩ : syracuseStep 177707 = 266561) B266561
theorem B177737 : Blo 115785 177737 := bstep (se 2 (by rfl) ⟨66651, by rfl⟩ : syracuseStep 177737 = 133303) B133303
theorem B177851 : Blo 115785 177851 := bstep (se 1 (by rfl) ⟨133388, by rfl⟩ : syracuseStep 177851 = 266777) B266777
theorem B177911 : Blo 115785 177911 := bstep (se 1 (by rfl) ⟨133433, by rfl⟩ : syracuseStep 177911 = 266867) B266867
theorem B1226497 : Blo 115785 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B177935 : Blo 115785 177935 := bstep (se 1 (by rfl) ⟨133451, by rfl⟩ : syracuseStep 177935 = 266903) B266903
theorem B177977 : Blo 115785 177977 := bstep (se 2 (by rfl) ⟨66741, by rfl⟩ : syracuseStep 177977 = 133483) B133483
theorem B6731585 : Blo 115785 6731585 := bstep (se 2 (by rfl) ⟨2524344, by rfl⟩ : syracuseStep 6731585 = 5048689) B5048689
theorem B178055 : Blo 115785 178055 := bstep (se 1 (by rfl) ⟨133541, by rfl⟩ : syracuseStep 178055 = 267083) B267083
theorem B178091 : Blo 115785 178091 := bstep (se 1 (by rfl) ⟨133568, by rfl⟩ : syracuseStep 178091 = 267137) B267137
theorem B178121 : Blo 115785 178121 := bstep (se 2 (by rfl) ⟨66795, by rfl⟩ : syracuseStep 178121 = 133591) B133591
theorem B178235 : Blo 115785 178235 := bstep (se 1 (by rfl) ⟨133676, by rfl⟩ : syracuseStep 178235 = 267353) B267353
theorem B669815 : Blo 115785 669815 := bstep (se 1 (by rfl) ⟨502361, by rfl⟩ : syracuseStep 669815 = 1004723) B1004723
theorem B178295 : Blo 115785 178295 := bstep (se 1 (by rfl) ⟨133721, by rfl⟩ : syracuseStep 178295 = 267443) B267443
theorem B243847 : Blo 115785 243847 := bstep (se 1 (by rfl) ⟨182885, by rfl⟩ : syracuseStep 243847 = 365771) B365771
theorem B178319 : Blo 115785 178319 := bstep (se 1 (by rfl) ⟨133739, by rfl⟩ : syracuseStep 178319 = 267479) B267479
theorem B178361 : Blo 115785 178361 := bstep (se 2 (by rfl) ⟨66885, by rfl⟩ : syracuseStep 178361 = 133771) B133771
theorem B178439 : Blo 115785 178439 := bstep (se 1 (by rfl) ⟨133829, by rfl⟩ : syracuseStep 178439 = 267659) B267659
theorem B211243 : Blo 115785 211243 := bstep (se 1 (by rfl) ⟨158432, by rfl⟩ : syracuseStep 211243 = 316865) B316865
theorem B178475 : Blo 115785 178475 := bstep (se 1 (by rfl) ⟨133856, by rfl⟩ : syracuseStep 178475 = 267713) B267713
theorem B178505 : Blo 115785 178505 := bstep (se 2 (by rfl) ⟨66939, by rfl⟩ : syracuseStep 178505 = 133879) B133879
theorem B440711 : Blo 115785 440711 := bstep (se 1 (by rfl) ⟨330533, by rfl⟩ : syracuseStep 440711 = 661067) B661067
theorem B178619 : Blo 115785 178619 := bstep (se 1 (by rfl) ⟨133964, by rfl⟩ : syracuseStep 178619 = 267929) B267929
theorem B4143581 : Blo 115785 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B178679 : Blo 115785 178679 := bstep (se 1 (by rfl) ⟨134009, by rfl⟩ : syracuseStep 178679 = 268019) B268019
theorem B178703 : Blo 115785 178703 := bstep (se 1 (by rfl) ⟨134027, by rfl⟩ : syracuseStep 178703 = 268055) B268055
theorem B178745 : Blo 115785 178745 := bstep (se 2 (by rfl) ⟨67029, by rfl⟩ : syracuseStep 178745 = 134059) B134059
theorem B178823 : Blo 115785 178823 := bstep (se 1 (by rfl) ⟨134117, by rfl⟩ : syracuseStep 178823 = 268235) B268235
theorem B178859 : Blo 115785 178859 := bstep (se 1 (by rfl) ⟨134144, by rfl⟩ : syracuseStep 178859 = 268289) B268289
theorem B178889 : Blo 115785 178889 := bstep (se 2 (by rfl) ⟨67083, by rfl⟩ : syracuseStep 178889 = 134167) B134167
theorem B179003 : Blo 115785 179003 := bstep (se 1 (by rfl) ⟨134252, by rfl⟩ : syracuseStep 179003 = 268505) B268505
theorem B179063 : Blo 115785 179063 := bstep (se 1 (by rfl) ⟨134297, by rfl⟩ : syracuseStep 179063 = 268595) B268595
theorem B179087 : Blo 115785 179087 := bstep (se 1 (by rfl) ⟨134315, by rfl⟩ : syracuseStep 179087 = 268631) B268631
theorem B179129 : Blo 115785 179129 := bstep (se 2 (by rfl) ⟨67173, by rfl⟩ : syracuseStep 179129 = 134347) B134347
theorem B179207 : Blo 115785 179207 := bstep (se 1 (by rfl) ⟨134405, by rfl⟩ : syracuseStep 179207 = 268811) B268811
theorem B179243 : Blo 115785 179243 := bstep (se 1 (by rfl) ⟨134432, by rfl⟩ : syracuseStep 179243 = 268865) B268865
theorem B179273 : Blo 115785 179273 := bstep (se 2 (by rfl) ⟨67227, by rfl⟩ : syracuseStep 179273 = 134455) B134455
theorem B179387 : Blo 115785 179387 := bstep (se 1 (by rfl) ⟨134540, by rfl⟩ : syracuseStep 179387 = 269081) B269081
theorem B179447 : Blo 115785 179447 := bstep (se 1 (by rfl) ⟨134585, by rfl⟩ : syracuseStep 179447 = 269171) B269171
theorem B179471 : Blo 115785 179471 := bstep (se 1 (by rfl) ⟨134603, by rfl⟩ : syracuseStep 179471 = 269207) B269207
theorem B179513 : Blo 115785 179513 := bstep (se 2 (by rfl) ⟨67317, by rfl⟩ : syracuseStep 179513 = 134635) B134635
theorem B605555 : Blo 115785 605555 := bstep (se 1 (by rfl) ⟨454166, by rfl⟩ : syracuseStep 605555 = 908333) B908333
theorem B572807 : Blo 115785 572807 := bstep (se 1 (by rfl) ⟨429605, by rfl⟩ : syracuseStep 572807 = 859211) B859211
theorem B179591 : Blo 115785 179591 := bstep (se 1 (by rfl) ⟨134693, by rfl⟩ : syracuseStep 179591 = 269387) B269387
theorem B310675 : Blo 115785 310675 := bstep (se 1 (by rfl) ⟨233006, by rfl⟩ : syracuseStep 310675 = 466013) B466013
theorem B179627 : Blo 115785 179627 := bstep (se 1 (by rfl) ⟨134720, by rfl⟩ : syracuseStep 179627 = 269441) B269441
theorem B179657 : Blo 115785 179657 := bstep (se 2 (by rfl) ⟨67371, by rfl⟩ : syracuseStep 179657 = 134743) B134743
theorem B212627 : Blo 115785 212627 := bstep (se 1 (by rfl) ⟨159470, by rfl⟩ : syracuseStep 212627 = 318941) B318941
theorem B278273 : Blo 115785 278273 := bstep (se 2 (by rfl) ⟨104352, by rfl⟩ : syracuseStep 278273 = 208705) B208705
theorem B606041 : Blo 115785 606041 := bstep (se 2 (by rfl) ⟨227265, by rfl⟩ : syracuseStep 606041 = 454531) B454531
theorem B278407 : Blo 115785 278407 := bstep (se 1 (by rfl) ⟨208805, by rfl⟩ : syracuseStep 278407 = 417611) B417611
theorem B638873 : Blo 115785 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B671773 : Blo 115785 671773 := bstep (se 3 (by rfl) ⟨125957, by rfl⟩ : syracuseStep 671773 = 251915) B251915
theorem B1360313 : Blo 115785 1360313 := bstep (se 2 (by rfl) ⟨510117, by rfl⟩ : syracuseStep 1360313 = 1020235) B1020235
theorem B967133 : Blo 115785 967133 := bstep (se 3 (by rfl) ⟨181337, by rfl⟩ : syracuseStep 967133 = 362675) B362675
theorem B672299 : Blo 115785 672299 := bstep (se 1 (by rfl) ⟨504224, by rfl⟩ : syracuseStep 672299 = 1008449) B1008449
theorem B213563 : Blo 115785 213563 := bstep (se 1 (by rfl) ⟨160172, by rfl⟩ : syracuseStep 213563 = 320345) B320345
theorem B508787 : Blo 115785 508787 := bstep (se 1 (by rfl) ⟨381590, by rfl⟩ : syracuseStep 508787 = 763181) B763181
theorem B2278307 : Blo 115785 2278307 := bstep (se 1 (by rfl) ⟨1708730, by rfl⟩ : syracuseStep 2278307 = 3417461) B3417461
theorem B476171 : Blo 115785 476171 := bstep (se 1 (by rfl) ⟨357128, by rfl⟩ : syracuseStep 476171 = 714257) B714257
theorem B115847 : Blo 115785 115847 := bstep (se 1 (by rfl) ⟨86885, by rfl⟩ : syracuseStep 115847 = 173771) B173771
theorem B115855 : Blo 115785 115855 := bstep (se 1 (by rfl) ⟨86891, by rfl⟩ : syracuseStep 115855 = 173783) B173783
theorem B115899 : Blo 115785 115899 := bstep (se 1 (by rfl) ⟨86924, by rfl⟩ : syracuseStep 115899 = 173849) B173849
theorem B640237 : Blo 115785 640237 := bstep (se 3 (by rfl) ⟨120044, by rfl⟩ : syracuseStep 640237 = 240089) B240089
theorem B476417 : Blo 115785 476417 := bstep (se 2 (by rfl) ⟨178656, by rfl⟩ : syracuseStep 476417 = 357313) B357313
theorem B115975 : Blo 115785 115975 := bstep (se 1 (by rfl) ⟨86981, by rfl⟩ : syracuseStep 115975 = 173963) B173963
theorem B115983 : Blo 115785 115983 := bstep (se 1 (by rfl) ⟨86987, by rfl⟩ : syracuseStep 115983 = 173975) B173975
theorem B116027 : Blo 115785 116027 := bstep (se 1 (by rfl) ⟨87020, by rfl⟩ : syracuseStep 116027 = 174041) B174041
theorem B116103 : Blo 115785 116103 := bstep (se 1 (by rfl) ⟨87077, by rfl⟩ : syracuseStep 116103 = 174155) B174155
theorem B116111 : Blo 115785 116111 := bstep (se 1 (by rfl) ⟨87083, by rfl⟩ : syracuseStep 116111 = 174167) B174167
theorem B116155 : Blo 115785 116155 := bstep (se 1 (by rfl) ⟨87116, by rfl⟩ : syracuseStep 116155 = 174233) B174233
theorem B116231 : Blo 115785 116231 := bstep (se 1 (by rfl) ⟨87173, by rfl⟩ : syracuseStep 116231 = 174347) B174347
theorem B116239 : Blo 115785 116239 := bstep (se 1 (by rfl) ⟨87179, by rfl⟩ : syracuseStep 116239 = 174359) B174359
theorem B181775 : Blo 115785 181775 := bstep (se 1 (by rfl) ⟨136331, by rfl⟩ : syracuseStep 181775 = 272663) B272663
theorem B149035 : Blo 115785 149035 := bstep (se 1 (by rfl) ⟨111776, by rfl⟩ : syracuseStep 149035 = 223553) B223553
theorem B116283 : Blo 115785 116283 := bstep (se 1 (by rfl) ⟨87212, by rfl⟩ : syracuseStep 116283 = 174425) B174425
theorem B116359 : Blo 115785 116359 := bstep (se 1 (by rfl) ⟨87269, by rfl⟩ : syracuseStep 116359 = 174539) B174539
theorem B116367 : Blo 115785 116367 := bstep (se 1 (by rfl) ⟨87275, by rfl⟩ : syracuseStep 116367 = 174551) B174551
theorem B116411 : Blo 115785 116411 := bstep (se 1 (by rfl) ⟨87308, by rfl⟩ : syracuseStep 116411 = 174617) B174617
theorem B116487 : Blo 115785 116487 := bstep (se 1 (by rfl) ⟨87365, by rfl⟩ : syracuseStep 116487 = 174731) B174731
theorem B116495 : Blo 115785 116495 := bstep (se 1 (by rfl) ⟨87371, by rfl⟩ : syracuseStep 116495 = 174743) B174743
theorem B116539 : Blo 115785 116539 := bstep (se 1 (by rfl) ⟨87404, by rfl⟩ : syracuseStep 116539 = 174809) B174809
theorem B116615 : Blo 115785 116615 := bstep (se 1 (by rfl) ⟨87461, by rfl⟩ : syracuseStep 116615 = 174923) B174923
theorem B116623 : Blo 115785 116623 := bstep (se 1 (by rfl) ⟨87467, by rfl⟩ : syracuseStep 116623 = 174935) B174935
theorem B116667 : Blo 115785 116667 := bstep (se 1 (by rfl) ⟨87500, by rfl⟩ : syracuseStep 116667 = 175001) B175001
theorem B673757 : Blo 115785 673757 := bstep (se 3 (by rfl) ⟨126329, by rfl⟩ : syracuseStep 673757 = 252659) B252659
theorem B116743 : Blo 115785 116743 := bstep (se 1 (by rfl) ⟨87557, by rfl⟩ : syracuseStep 116743 = 175115) B175115
theorem B116751 : Blo 115785 116751 := bstep (se 1 (by rfl) ⟨87563, by rfl⟩ : syracuseStep 116751 = 175127) B175127
theorem B116795 : Blo 115785 116795 := bstep (se 1 (by rfl) ⟨87596, by rfl⟩ : syracuseStep 116795 = 175193) B175193
theorem B1427543 : Blo 115785 1427543 := bstep (se 1 (by rfl) ⟨1070657, by rfl⟩ : syracuseStep 1427543 = 2141315) B2141315
theorem B1099909 : Blo 115785 1099909 := bstep (se 4 (by rfl) ⟨103116, by rfl⟩ : syracuseStep 1099909 = 206233) B206233
theorem B116871 : Blo 115785 116871 := bstep (se 1 (by rfl) ⟨87653, by rfl⟩ : syracuseStep 116871 = 175307) B175307
theorem B116879 : Blo 115785 116879 := bstep (se 1 (by rfl) ⟨87659, by rfl⟩ : syracuseStep 116879 = 175319) B175319
theorem B116923 : Blo 115785 116923 := bstep (se 1 (by rfl) ⟨87692, by rfl⟩ : syracuseStep 116923 = 175385) B175385
theorem B116999 : Blo 115785 116999 := bstep (se 1 (by rfl) ⟨87749, by rfl⟩ : syracuseStep 116999 = 175499) B175499
theorem B117007 : Blo 115785 117007 := bstep (se 1 (by rfl) ⟨87755, by rfl⟩ : syracuseStep 117007 = 175511) B175511
theorem B248123 : Blo 115785 248123 := bstep (se 1 (by rfl) ⟨186092, by rfl⟩ : syracuseStep 248123 = 372185) B372185
theorem B117051 : Blo 115785 117051 := bstep (se 1 (by rfl) ⟨87788, by rfl⟩ : syracuseStep 117051 = 175577) B175577
theorem B117127 : Blo 115785 117127 := bstep (se 1 (by rfl) ⟨87845, by rfl⟩ : syracuseStep 117127 = 175691) B175691
theorem B117135 : Blo 115785 117135 := bstep (se 1 (by rfl) ⟨87851, by rfl⟩ : syracuseStep 117135 = 175703) B175703
theorem B117179 : Blo 115785 117179 := bstep (se 1 (by rfl) ⟨87884, by rfl⟩ : syracuseStep 117179 = 175769) B175769
theorem B150007 : Blo 115785 150007 := bstep (se 1 (by rfl) ⟨112505, by rfl⟩ : syracuseStep 150007 = 225011) B225011
theorem B608771 : Blo 115785 608771 := bstep (se 1 (by rfl) ⟨456578, by rfl⟩ : syracuseStep 608771 = 913157) B913157
theorem B117255 : Blo 115785 117255 := bstep (se 1 (by rfl) ⟨87941, by rfl⟩ : syracuseStep 117255 = 175883) B175883
theorem B117263 : Blo 115785 117263 := bstep (se 1 (by rfl) ⟨87947, by rfl⟩ : syracuseStep 117263 = 175895) B175895
theorem B117307 : Blo 115785 117307 := bstep (se 1 (by rfl) ⟨87980, by rfl⟩ : syracuseStep 117307 = 175961) B175961
theorem B117383 : Blo 115785 117383 := bstep (se 1 (by rfl) ⟨88037, by rfl⟩ : syracuseStep 117383 = 176075) B176075
theorem B117391 : Blo 115785 117391 := bstep (se 1 (by rfl) ⟨88043, by rfl⟩ : syracuseStep 117391 = 176087) B176087
theorem B117435 : Blo 115785 117435 := bstep (se 1 (by rfl) ⟨88076, by rfl⟩ : syracuseStep 117435 = 176153) B176153
theorem B117511 : Blo 115785 117511 := bstep (se 1 (by rfl) ⟨88133, by rfl⟩ : syracuseStep 117511 = 176267) B176267
theorem B117519 : Blo 115785 117519 := bstep (se 1 (by rfl) ⟨88139, by rfl⟩ : syracuseStep 117519 = 176279) B176279
theorem B117563 : Blo 115785 117563 := bstep (se 1 (by rfl) ⟨88172, by rfl⟩ : syracuseStep 117563 = 176345) B176345
theorem B150331 : Blo 115785 150331 := bstep (se 1 (by rfl) ⟨112748, by rfl⟩ : syracuseStep 150331 = 225497) B225497
theorem B117639 : Blo 115785 117639 := bstep (se 1 (by rfl) ⟨88229, by rfl⟩ : syracuseStep 117639 = 176459) B176459
theorem B117647 : Blo 115785 117647 := bstep (se 1 (by rfl) ⟨88235, by rfl⟩ : syracuseStep 117647 = 176471) B176471
theorem B117691 : Blo 115785 117691 := bstep (se 1 (by rfl) ⟨88268, by rfl⟩ : syracuseStep 117691 = 176537) B176537
theorem B117767 : Blo 115785 117767 := bstep (se 1 (by rfl) ⟨88325, by rfl⟩ : syracuseStep 117767 = 176651) B176651
theorem B117775 : Blo 115785 117775 := bstep (se 1 (by rfl) ⟨88331, by rfl⟩ : syracuseStep 117775 = 176663) B176663
theorem B117819 : Blo 115785 117819 := bstep (se 1 (by rfl) ⟨88364, by rfl⟩ : syracuseStep 117819 = 176729) B176729
theorem B805949 : Blo 115785 805949 := bstep (se 3 (by rfl) ⟨151115, by rfl⟩ : syracuseStep 805949 = 302231) B302231
theorem B117895 : Blo 115785 117895 := bstep (se 1 (by rfl) ⟨88421, by rfl⟩ : syracuseStep 117895 = 176843) B176843
theorem B117903 : Blo 115785 117903 := bstep (se 1 (by rfl) ⟨88427, by rfl⟩ : syracuseStep 117903 = 176855) B176855
theorem B117947 : Blo 115785 117947 := bstep (se 1 (by rfl) ⟨88460, by rfl⟩ : syracuseStep 117947 = 176921) B176921
theorem B118023 : Blo 115785 118023 := bstep (se 1 (by rfl) ⟨88517, by rfl⟩ : syracuseStep 118023 = 177035) B177035
theorem B118031 : Blo 115785 118031 := bstep (se 1 (by rfl) ⟨88523, by rfl⟩ : syracuseStep 118031 = 177047) B177047
theorem B249131 : Blo 115785 249131 := bstep (se 1 (by rfl) ⟨186848, by rfl⟩ : syracuseStep 249131 = 373697) B373697
theorem B118075 : Blo 115785 118075 := bstep (se 1 (by rfl) ⟨88556, by rfl⟩ : syracuseStep 118075 = 177113) B177113
theorem B118151 : Blo 115785 118151 := bstep (se 1 (by rfl) ⟨88613, by rfl⟩ : syracuseStep 118151 = 177227) B177227
theorem B118159 : Blo 115785 118159 := bstep (se 1 (by rfl) ⟨88619, by rfl⟩ : syracuseStep 118159 = 177239) B177239
theorem B118203 : Blo 115785 118203 := bstep (se 1 (by rfl) ⟨88652, by rfl⟩ : syracuseStep 118203 = 177305) B177305
theorem B118279 : Blo 115785 118279 := bstep (se 1 (by rfl) ⟨88709, by rfl⟩ : syracuseStep 118279 = 177419) B177419
theorem B118287 : Blo 115785 118287 := bstep (se 1 (by rfl) ⟨88715, by rfl⟩ : syracuseStep 118287 = 177431) B177431
theorem B118331 : Blo 115785 118331 := bstep (se 1 (by rfl) ⟨88748, by rfl⟩ : syracuseStep 118331 = 177497) B177497
theorem B282199 : Blo 115785 282199 := bstep (se 1 (by rfl) ⟨211649, by rfl⟩ : syracuseStep 282199 = 423299) B423299
theorem B118407 : Blo 115785 118407 := bstep (se 1 (by rfl) ⟨88805, by rfl⟩ : syracuseStep 118407 = 177611) B177611
theorem B118415 : Blo 115785 118415 := bstep (se 1 (by rfl) ⟨88811, by rfl⟩ : syracuseStep 118415 = 177623) B177623
theorem B118459 : Blo 115785 118459 := bstep (se 1 (by rfl) ⟨88844, by rfl⟩ : syracuseStep 118459 = 177689) B177689
theorem B1199809 : Blo 115785 1199809 := bstep (se 2 (by rfl) ⟨449928, by rfl⟩ : syracuseStep 1199809 = 899857) B899857
theorem B118535 : Blo 115785 118535 := bstep (se 1 (by rfl) ⟨88901, by rfl⟩ : syracuseStep 118535 = 177803) B177803
theorem B151303 : Blo 115785 151303 := bstep (se 1 (by rfl) ⟨113477, by rfl⟩ : syracuseStep 151303 = 226955) B226955
theorem B118543 : Blo 115785 118543 := bstep (se 1 (by rfl) ⟨88907, by rfl⟩ : syracuseStep 118543 = 177815) B177815
theorem B118587 : Blo 115785 118587 := bstep (se 1 (by rfl) ⟨88940, by rfl⟩ : syracuseStep 118587 = 177881) B177881
theorem B282503 : Blo 115785 282503 := bstep (se 1 (by rfl) ⟨211877, by rfl⟩ : syracuseStep 282503 = 423755) B423755
theorem B118663 : Blo 115785 118663 := bstep (se 1 (by rfl) ⟨88997, by rfl⟩ : syracuseStep 118663 = 177995) B177995
theorem B118671 : Blo 115785 118671 := bstep (se 1 (by rfl) ⟨89003, by rfl⟩ : syracuseStep 118671 = 178007) B178007
theorem B118715 : Blo 115785 118715 := bstep (se 1 (by rfl) ⟨89036, by rfl⟩ : syracuseStep 118715 = 178073) B178073
theorem B118791 : Blo 115785 118791 := bstep (se 1 (by rfl) ⟨89093, by rfl⟩ : syracuseStep 118791 = 178187) B178187
theorem B118799 : Blo 115785 118799 := bstep (se 1 (by rfl) ⟨89099, by rfl⟩ : syracuseStep 118799 = 178199) B178199
theorem B118843 : Blo 115785 118843 := bstep (se 1 (by rfl) ⟨89132, by rfl⟩ : syracuseStep 118843 = 178265) B178265
theorem B118919 : Blo 115785 118919 := bstep (se 1 (by rfl) ⟨89189, by rfl⟩ : syracuseStep 118919 = 178379) B178379
theorem B118927 : Blo 115785 118927 := bstep (se 1 (by rfl) ⟨89195, by rfl⟩ : syracuseStep 118927 = 178391) B178391
theorem B118971 : Blo 115785 118971 := bstep (se 1 (by rfl) ⟨89228, by rfl⟩ : syracuseStep 118971 = 178457) B178457
theorem B905417 : Blo 115785 905417 := bstep (se 2 (by rfl) ⟨339531, by rfl⟩ : syracuseStep 905417 = 679063) B679063
theorem B119047 : Blo 115785 119047 := bstep (se 1 (by rfl) ⟨89285, by rfl⟩ : syracuseStep 119047 = 178571) B178571
theorem B119055 : Blo 115785 119055 := bstep (se 1 (by rfl) ⟨89291, by rfl⟩ : syracuseStep 119055 = 178583) B178583
theorem B676147 : Blo 115785 676147 := bstep (se 1 (by rfl) ⟨507110, by rfl⟩ : syracuseStep 676147 = 1014221) B1014221
theorem B119099 : Blo 115785 119099 := bstep (se 1 (by rfl) ⟨89324, by rfl⟩ : syracuseStep 119099 = 178649) B178649
theorem B119175 : Blo 115785 119175 := bstep (se 1 (by rfl) ⟨89381, by rfl⟩ : syracuseStep 119175 = 178763) B178763
theorem B119183 : Blo 115785 119183 := bstep (se 1 (by rfl) ⟨89387, by rfl⟩ : syracuseStep 119183 = 178775) B178775
theorem B119227 : Blo 115785 119227 := bstep (se 1 (by rfl) ⟨89420, by rfl⟩ : syracuseStep 119227 = 178841) B178841
theorem B119303 : Blo 115785 119303 := bstep (se 1 (by rfl) ⟨89477, by rfl⟩ : syracuseStep 119303 = 178955) B178955
theorem B119311 : Blo 115785 119311 := bstep (se 1 (by rfl) ⟨89483, by rfl⟩ : syracuseStep 119311 = 178967) B178967
theorem B18469397 : Blo 115785 18469397 := bstep (se 6 (by rfl) ⟨432876, by rfl⟩ : syracuseStep 18469397 = 865753) B865753
theorem B1004075 : Blo 115785 1004075 := bstep (se 1 (by rfl) ⟨753056, by rfl⟩ : syracuseStep 1004075 = 1506113) B1506113
theorem B119355 : Blo 115785 119355 := bstep (se 1 (by rfl) ⟨89516, by rfl⟩ : syracuseStep 119355 = 179033) B179033
theorem B119431 : Blo 115785 119431 := bstep (se 1 (by rfl) ⟨89573, by rfl⟩ : syracuseStep 119431 = 179147) B179147
theorem B119439 : Blo 115785 119439 := bstep (se 1 (by rfl) ⟨89579, by rfl⟩ : syracuseStep 119439 = 179159) B179159
theorem B119483 : Blo 115785 119483 := bstep (se 1 (by rfl) ⟨89612, by rfl⟩ : syracuseStep 119483 = 179225) B179225
theorem B119559 : Blo 115785 119559 := bstep (se 1 (by rfl) ⟨89669, by rfl⟩ : syracuseStep 119559 = 179339) B179339
theorem B119567 : Blo 115785 119567 := bstep (se 1 (by rfl) ⟨89675, by rfl⟩ : syracuseStep 119567 = 179351) B179351
theorem B119611 : Blo 115785 119611 := bstep (se 1 (by rfl) ⟨89708, by rfl⟩ : syracuseStep 119611 = 179417) B179417
theorem B119687 : Blo 115785 119687 := bstep (se 1 (by rfl) ⟨89765, by rfl⟩ : syracuseStep 119687 = 179531) B179531
theorem B119695 : Blo 115785 119695 := bstep (se 1 (by rfl) ⟨89771, by rfl⟩ : syracuseStep 119695 = 179543) B179543
theorem B250771 : Blo 115785 250771 := bstep (se 1 (by rfl) ⟨188078, by rfl⟩ : syracuseStep 250771 = 376157) B376157
theorem B119739 : Blo 115785 119739 := bstep (se 1 (by rfl) ⟨89804, by rfl⟩ : syracuseStep 119739 = 179609) B179609
theorem B480323 : Blo 115785 480323 := bstep (se 1 (by rfl) ⟨360242, by rfl⟩ : syracuseStep 480323 = 720485) B720485
theorem B251027 : Blo 115785 251027 := bstep (se 1 (by rfl) ⟨188270, by rfl⟩ : syracuseStep 251027 = 376541) B376541
theorem B283915 : Blo 115785 283915 := bstep (se 1 (by rfl) ⟨212936, by rfl⟩ : syracuseStep 283915 = 425873) B425873
theorem B1332611 : Blo 115785 1332611 := bstep (se 1 (by rfl) ⟨999458, by rfl⟩ : syracuseStep 1332611 = 1998917) B1998917
theorem B382475 : Blo 115785 382475 := bstep (se 1 (by rfl) ⟨286856, by rfl⟩ : syracuseStep 382475 = 573713) B573713
theorem B2184803 : Blo 115785 2184803 := bstep (se 1 (by rfl) ⟨1638602, by rfl⟩ : syracuseStep 2184803 = 3277205) B3277205
theorem B677605 : Blo 115785 677605 := bstep (se 4 (by rfl) ⟨63525, by rfl⟩ : syracuseStep 677605 = 127051) B127051
theorem B186553 : Blo 115785 186553 := bstep (se 2 (by rfl) ⟨69957, by rfl⟩ : syracuseStep 186553 = 139915) B139915
theorem B514451 : Blo 115785 514451 := bstep (se 1 (by rfl) ⟨385838, by rfl⟩ : syracuseStep 514451 = 771677) B771677
theorem B481879 : Blo 115785 481879 := bstep (se 1 (by rfl) ⟨361409, by rfl⟩ : syracuseStep 481879 = 722819) B722819
theorem B252715 : Blo 115785 252715 := bstep (se 1 (by rfl) ⟨189536, by rfl⟩ : syracuseStep 252715 = 379073) B379073
theorem B318269 : Blo 115785 318269 := bstep (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) B119351
theorem B1891187 : Blo 115785 1891187 := bstep (se 1 (by rfl) ⟨1418390, by rfl⟩ : syracuseStep 1891187 = 2836781) B2836781
theorem B2579363 : Blo 115785 2579363 := bstep (se 1 (by rfl) ⟨1934522, by rfl⟩ : syracuseStep 2579363 = 3869045) B3869045
theorem B449489 : Blo 115785 449489 := bstep (se 2 (by rfl) ⟨168558, by rfl⟩ : syracuseStep 449489 = 337117) B337117
theorem B220295 : Blo 115785 220295 := bstep (se 1 (by rfl) ⟨165221, by rfl⟩ : syracuseStep 220295 = 330443) B330443
theorem B482593 : Blo 115785 482593 := bstep (se 2 (by rfl) ⟨180972, by rfl⟩ : syracuseStep 482593 = 361945) B361945
theorem B286087 : Blo 115785 286087 := bstep (se 1 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 286087 = 429131) B429131
theorem B449945 : Blo 115785 449945 := bstep (se 2 (by rfl) ⟨168729, by rfl⟩ : syracuseStep 449945 = 337459) B337459
theorem B253385 : Blo 115785 253385 := bstep (se 2 (by rfl) ⟨95019, by rfl⟩ : syracuseStep 253385 = 190039) B190039
theorem B220819 : Blo 115785 220819 := bstep (se 1 (by rfl) ⟨165614, by rfl⟩ : syracuseStep 220819 = 331229) B331229
theorem B319177 : Blo 115785 319177 := bstep (se 2 (by rfl) ⟨119691, by rfl⟩ : syracuseStep 319177 = 239383) B239383
theorem B1400651 : Blo 115785 1400651 := bstep (se 1 (by rfl) ⟨1050488, by rfl⟩ : syracuseStep 1400651 = 2100977) B2100977
theorem B254137 : Blo 115785 254137 := bstep (se 2 (by rfl) ⟨95301, by rfl⟩ : syracuseStep 254137 = 190603) B190603
theorem B680339 : Blo 115785 680339 := bstep (se 1 (by rfl) ⟨510254, by rfl⟩ : syracuseStep 680339 = 1020509) B1020509
theorem B451115 : Blo 115785 451115 := bstep (se 1 (by rfl) ⟨338336, by rfl⟩ : syracuseStep 451115 = 676673) B676673
theorem B254735 : Blo 115785 254735 := bstep (se 1 (by rfl) ⟨191051, by rfl⟩ : syracuseStep 254735 = 382103) B382103
theorem B680737 : Blo 115785 680737 := bstep (se 2 (by rfl) ⟨255276, by rfl⟩ : syracuseStep 680737 = 510553) B510553
theorem B680755 : Blo 115785 680755 := bstep (se 1 (by rfl) ⟨510566, by rfl⟩ : syracuseStep 680755 = 1021133) B1021133
theorem B222011 : Blo 115785 222011 := bstep (se 1 (by rfl) ⟨166508, by rfl⟩ : syracuseStep 222011 = 333017) B333017
theorem B681047 : Blo 115785 681047 := bstep (se 1 (by rfl) ⟨510785, by rfl⟩ : syracuseStep 681047 = 1021571) B1021571
theorem B451855 : Blo 115785 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B222497 : Blo 115785 222497 := bstep (se 2 (by rfl) ⟨83436, by rfl⟩ : syracuseStep 222497 = 166873) B166873
theorem B222763 : Blo 115785 222763 := bstep (se 1 (by rfl) ⟨167072, by rfl⟩ : syracuseStep 222763 = 334145) B334145
theorem B157897 : Blo 115785 157897 := bstep (se 2 (by rfl) ⟨59211, by rfl⟩ : syracuseStep 157897 = 118423) B118423
theorem B453073 : Blo 115785 453073 := bstep (se 2 (by rfl) ⟨169902, by rfl⟩ : syracuseStep 453073 = 339805) B339805
theorem B748061 : Blo 115785 748061 := bstep (se 3 (by rfl) ⟨140261, by rfl⟩ : syracuseStep 748061 = 280523) B280523
theorem B715331 : Blo 115785 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B223879 : Blo 115785 223879 := bstep (se 1 (by rfl) ⟨167909, by rfl⟩ : syracuseStep 223879 = 335819) B335819
theorem B453377 : Blo 115785 453377 := bstep (se 2 (by rfl) ⟨170016, by rfl⟩ : syracuseStep 453377 = 340033) B340033
theorem B256801 : Blo 115785 256801 := bstep (se 2 (by rfl) ⟨96300, by rfl⟩ : syracuseStep 256801 = 192601) B192601
theorem B224441 : Blo 115785 224441 := bstep (se 2 (by rfl) ⟨84165, by rfl⟩ : syracuseStep 224441 = 168331) B168331
theorem B453833 : Blo 115785 453833 := bstep (se 2 (by rfl) ⟨170187, by rfl⟩ : syracuseStep 453833 = 340375) B340375
theorem B1371485 : Blo 115785 1371485 := bstep (se 3 (by rfl) ⟨257153, by rfl⟩ : syracuseStep 1371485 = 514307) B514307
theorem B1535441 : Blo 115785 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B126479 : Blo 115785 126479 := bstep (se 1 (by rfl) ⟨94859, by rfl⟩ : syracuseStep 126479 = 189719) B189719
theorem B126607 : Blo 115785 126607 := bstep (se 1 (by rfl) ⟨94955, by rfl⟩ : syracuseStep 126607 = 189911) B189911
theorem B2420375 : Blo 115785 2420375 := bstep (se 1 (by rfl) ⟨1815281, by rfl⟩ : syracuseStep 2420375 = 3630563) B3630563
theorem B1699505 : Blo 115785 1699505 := bstep (se 2 (by rfl) ⟨637314, by rfl⟩ : syracuseStep 1699505 = 1274629) B1274629
theorem B323357 : Blo 115785 323357 := bstep (se 3 (by rfl) ⟨60629, by rfl⟩ : syracuseStep 323357 = 121259) B121259
theorem B225595 : Blo 115785 225595 := bstep (se 1 (by rfl) ⟨169196, by rfl⟩ : syracuseStep 225595 = 338393) B338393
theorem B291131 : Blo 115785 291131 := bstep (se 1 (by rfl) ⟨218348, by rfl⟩ : syracuseStep 291131 = 436697) B436697
theorem B881117 : Blo 115785 881117 := bstep (se 3 (by rfl) ⟨165209, by rfl⟩ : syracuseStep 881117 = 330419) B330419
theorem B291481 : Blo 115785 291481 := bstep (se 2 (by rfl) ⟨109305, by rfl⟩ : syracuseStep 291481 = 218611) B218611
theorem B226081 : Blo 115785 226081 := bstep (se 2 (by rfl) ⟨84780, by rfl⟩ : syracuseStep 226081 = 169561) B169561
theorem B586763 : Blo 115785 586763 := bstep (se 1 (by rfl) ⟨440072, by rfl⟩ : syracuseStep 586763 = 880145) B880145
theorem B1012823 : Blo 115785 1012823 := bstep (se 1 (by rfl) ⟨759617, by rfl⟩ : syracuseStep 1012823 = 1519235) B1519235
theorem B423031 : Blo 115785 423031 := bstep (se 1 (by rfl) ⟨317273, by rfl⟩ : syracuseStep 423031 = 634547) B634547
theorem B586925 : Blo 115785 586925 := bstep (se 3 (by rfl) ⟨110048, by rfl⟩ : syracuseStep 586925 = 220097) B220097
theorem B1209659 : Blo 115785 1209659 := bstep (se 1 (by rfl) ⟨907244, by rfl⟩ : syracuseStep 1209659 = 1814489) B1814489
theorem B751133 : Blo 115785 751133 := bstep (se 3 (by rfl) ⟨140837, by rfl⟩ : syracuseStep 751133 = 281675) B281675
theorem B194167 : Blo 115785 194167 := bstep (se 1 (by rfl) ⟨145625, by rfl⟩ : syracuseStep 194167 = 291251) B291251
theorem B358187 : Blo 115785 358187 := bstep (se 1 (by rfl) ⟨268640, by rfl⟩ : syracuseStep 358187 = 537281) B537281
theorem B1144691 : Blo 115785 1144691 := bstep (se 1 (by rfl) ⟨858518, by rfl⟩ : syracuseStep 1144691 = 1717037) B1717037
theorem B227387 : Blo 115785 227387 := bstep (se 1 (by rfl) ⟨170540, by rfl⟩ : syracuseStep 227387 = 341081) B341081
theorem B391229 : Blo 115785 391229 := bstep (se 3 (by rfl) ⟨73355, by rfl⟩ : syracuseStep 391229 = 146711) B146711
theorem B293179 : Blo 115785 293179 := bstep (se 1 (by rfl) ⟨219884, by rfl⟩ : syracuseStep 293179 = 439769) B439769
theorem B719219 : Blo 115785 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B1440185 : Blo 115785 1440185 := bstep (se 2 (by rfl) ⟨540069, by rfl⟩ : syracuseStep 1440185 = 1080139) B1080139
theorem B293321 : Blo 115785 293321 := bstep (se 2 (by rfl) ⟨109995, by rfl⟩ : syracuseStep 293321 = 219991) B219991
theorem B588545 : Blo 115785 588545 := bstep (se 2 (by rfl) ⟨220704, by rfl⟩ : syracuseStep 588545 = 441409) B441409
theorem B293665 : Blo 115785 293665 := bstep (se 2 (by rfl) ⟨110124, by rfl⟩ : syracuseStep 293665 = 220249) B220249
theorem B260999 : Blo 115785 260999 := bstep (se 1 (by rfl) ⟨195749, by rfl⟩ : syracuseStep 260999 = 391499) B391499
theorem B261179 : Blo 115785 261179 := bstep (se 1 (by rfl) ⟨195884, by rfl⟩ : syracuseStep 261179 = 391769) B391769
theorem B261305 : Blo 115785 261305 := bstep (se 2 (by rfl) ⟨97989, by rfl⟩ : syracuseStep 261305 = 195979) B195979
theorem B195959 : Blo 115785 195959 := bstep (se 1 (by rfl) ⟨146969, by rfl⟩ : syracuseStep 195959 = 293939) B293939
theorem B294263 : Blo 115785 294263 := bstep (se 1 (by rfl) ⟨220697, by rfl⟩ : syracuseStep 294263 = 441395) B441395
theorem B392633 : Blo 115785 392633 := bstep (se 2 (by rfl) ⟨147237, by rfl⟩ : syracuseStep 392633 = 294475) B294475
theorem B130567 : Blo 115785 130567 := bstep (se 1 (by rfl) ⟨97925, by rfl⟩ : syracuseStep 130567 = 195851) B195851
theorem B261647 : Blo 115785 261647 := bstep (se 1 (by rfl) ⟨196235, by rfl⟩ : syracuseStep 261647 = 392471) B392471
theorem B261665 : Blo 115785 261665 := bstep (se 2 (by rfl) ⟨98124, by rfl⟩ : syracuseStep 261665 = 196249) B196249
theorem B589355 : Blo 115785 589355 := bstep (se 1 (by rfl) ⟨442016, by rfl⟩ : syracuseStep 589355 = 884033) B884033
theorem B2719331 : Blo 115785 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B130747 : Blo 115785 130747 := bstep (se 1 (by rfl) ⟨98060, by rfl⟩ : syracuseStep 130747 = 196121) B196121
theorem B196411 : Blo 115785 196411 := bstep (se 1 (by rfl) ⟨147308, by rfl⟩ : syracuseStep 196411 = 294617) B294617
theorem B262007 : Blo 115785 262007 := bstep (se 1 (by rfl) ⟨196505, by rfl⟩ : syracuseStep 262007 = 393011) B393011
theorem B196553 : Blo 115785 196553 := bstep (se 2 (by rfl) ⟨73707, by rfl⟩ : syracuseStep 196553 = 147415) B147415
theorem B262151 : Blo 115785 262151 := bstep (se 1 (by rfl) ⟨196613, by rfl⟩ : syracuseStep 262151 = 393227) B393227
theorem B1572941 : Blo 115785 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B262223 : Blo 115785 262223 := bstep (se 1 (by rfl) ⟨196667, by rfl⟩ : syracuseStep 262223 = 393335) B393335
theorem B197039 : Blo 115785 197039 := bstep (se 1 (by rfl) ⟨147779, by rfl⟩ : syracuseStep 197039 = 295559) B295559
theorem B131503 : Blo 115785 131503 := bstep (se 1 (by rfl) ⟨98627, by rfl⟩ : syracuseStep 131503 = 197255) B197255
theorem B262619 : Blo 115785 262619 := bstep (se 1 (by rfl) ⟨196964, by rfl⟩ : syracuseStep 262619 = 393929) B393929
theorem B459245 : Blo 115785 459245 := bstep (se 3 (by rfl) ⟨86108, by rfl⟩ : syracuseStep 459245 = 172217) B172217
theorem B393767 : Blo 115785 393767 := bstep (se 1 (by rfl) ⟨295325, by rfl⟩ : syracuseStep 393767 = 590651) B590651
theorem B2228795 : Blo 115785 2228795 := bstep (se 1 (by rfl) ⟨1671596, by rfl⟩ : syracuseStep 2228795 = 3343193) B3343193
theorem B393875 : Blo 115785 393875 := bstep (se 1 (by rfl) ⟨295406, by rfl⟩ : syracuseStep 393875 = 590813) B590813
theorem B197471 : Blo 115785 197471 := bstep (se 1 (by rfl) ⟨148103, by rfl⟩ : syracuseStep 197471 = 296207) B296207
theorem B131935 : Blo 115785 131935 := bstep (se 1 (by rfl) ⟨98951, by rfl⟩ : syracuseStep 131935 = 197903) B197903
theorem B394091 : Blo 115785 394091 := bstep (se 1 (by rfl) ⟨295568, by rfl⟩ : syracuseStep 394091 = 591137) B591137
theorem B394145 : Blo 115785 394145 := bstep (se 2 (by rfl) ⟨147804, by rfl⟩ : syracuseStep 394145 = 295609) B295609
theorem B263087 : Blo 115785 263087 := bstep (se 1 (by rfl) ⟨197315, by rfl⟩ : syracuseStep 263087 = 394631) B394631
theorem B721847 : Blo 115785 721847 := bstep (se 1 (by rfl) ⟨541385, by rfl⟩ : syracuseStep 721847 = 1082771) B1082771
theorem B263339 : Blo 115785 263339 := bstep (se 1 (by rfl) ⟨197504, by rfl⟩ : syracuseStep 263339 = 395009) B395009
theorem B132295 : Blo 115785 132295 := bstep (se 1 (by rfl) ⟨99221, by rfl⟩ : syracuseStep 132295 = 198443) B198443
theorem B198031 : Blo 115785 198031 := bstep (se 1 (by rfl) ⟨148523, by rfl⟩ : syracuseStep 198031 = 297047) B297047
theorem B951695 : Blo 115785 951695 := bstep (se 1 (by rfl) ⟨713771, by rfl⟩ : syracuseStep 951695 = 1427543) B1427543
theorem B4326857 : Blo 115785 4326857 := bstep (se 2 (by rfl) ⟨1622571, by rfl⟩ : syracuseStep 4326857 = 3245143) B3245143
theorem B394739 : Blo 115785 394739 := bstep (se 1 (by rfl) ⟨296054, by rfl⟩ : syracuseStep 394739 = 592109) B592109
theorem B1836533 : Blo 115785 1836533 := bstep (se 5 (by rfl) ⟨86087, by rfl⟩ : syracuseStep 1836533 = 172175) B172175
theorem B165415 : Blo 115785 165415 := bstep (se 1 (by rfl) ⟨124061, by rfl⟩ : syracuseStep 165415 = 248123) B248123
theorem B853649 : Blo 115785 853649 := bstep (se 2 (by rfl) ⟨320118, by rfl⟩ : syracuseStep 853649 = 640237) B640237
theorem B263879 : Blo 115785 263879 := bstep (se 1 (by rfl) ⟨197909, by rfl⟩ : syracuseStep 263879 = 395819) B395819
theorem B198587 : Blo 115785 198587 := bstep (se 1 (by rfl) ⟨148940, by rfl⟩ : syracuseStep 198587 = 297881) B297881
theorem B854023 : Blo 115785 854023 := bstep (se 1 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 854023 = 1281035) B1281035
theorem B395279 : Blo 115785 395279 := bstep (se 1 (by rfl) ⟨296459, by rfl⟩ : syracuseStep 395279 = 592919) B592919
theorem B133159 : Blo 115785 133159 := bstep (se 1 (by rfl) ⟨99869, by rfl⟩ : syracuseStep 133159 = 199739) B199739
theorem B297017 : Blo 115785 297017 := bstep (se 2 (by rfl) ⟨111381, by rfl⟩ : syracuseStep 297017 = 222763) B222763
theorem B198713 : Blo 115785 198713 := bstep (se 2 (by rfl) ⟨74517, by rfl⟩ : syracuseStep 198713 = 149035) B149035
theorem B166087 : Blo 115785 166087 := bstep (se 1 (by rfl) ⟨124565, by rfl⟩ : syracuseStep 166087 = 249131) B249131
theorem B264553 : Blo 115785 264553 := bstep (se 2 (by rfl) ⟨99207, by rfl⟩ : syracuseStep 264553 = 198415) B198415
theorem B330227 : Blo 115785 330227 := bstep (se 1 (by rfl) ⟨247670, by rfl⟩ : syracuseStep 330227 = 495341) B495341
theorem B264743 : Blo 115785 264743 := bstep (se 1 (by rfl) ⟨198557, by rfl⟩ : syracuseStep 264743 = 397115) B397115
theorem B395873 : Blo 115785 395873 := bstep (se 2 (by rfl) ⟨148452, by rfl⟩ : syracuseStep 395873 = 296905) B296905
theorem B592595 : Blo 115785 592595 := bstep (se 1 (by rfl) ⟨444446, by rfl⟩ : syracuseStep 592595 = 888893) B888893
theorem B199415 : Blo 115785 199415 := bstep (se 1 (by rfl) ⟨149561, by rfl⟩ : syracuseStep 199415 = 299123) B299123
theorem B265067 : Blo 115785 265067 := bstep (se 1 (by rfl) ⟨198800, by rfl⟩ : syracuseStep 265067 = 397601) B397601
theorem B265121 : Blo 115785 265121 := bstep (se 2 (by rfl) ⟨99420, by rfl⟩ : syracuseStep 265121 = 198841) B198841
theorem B199759 : Blo 115785 199759 := bstep (se 1 (by rfl) ⟨149819, by rfl⟩ : syracuseStep 199759 = 299639) B299639
theorem B265463 : Blo 115785 265463 := bstep (se 1 (by rfl) ⟨199097, by rfl⟩ : syracuseStep 265463 = 398195) B398195
theorem B1117475 : Blo 115785 1117475 := bstep (se 1 (by rfl) ⟨838106, by rfl⟩ : syracuseStep 1117475 = 1676213) B1676213
theorem B200009 : Blo 115785 200009 := bstep (se 2 (by rfl) ⟨75003, by rfl⟩ : syracuseStep 200009 = 150007) B150007
theorem B167351 : Blo 115785 167351 := bstep (se 1 (by rfl) ⟨125513, by rfl⟩ : syracuseStep 167351 = 251027) B251027
theorem B298505 : Blo 115785 298505 := bstep (se 2 (by rfl) ⟨111939, by rfl⟩ : syracuseStep 298505 = 223879) B223879
theorem B888407 : Blo 115785 888407 := bstep (se 1 (by rfl) ⟨666305, by rfl⟩ : syracuseStep 888407 = 1332611) B1332611
theorem B200441 : Blo 115785 200441 := bstep (se 2 (by rfl) ⟨75165, by rfl⟩ : syracuseStep 200441 = 150331) B150331
theorem B266057 : Blo 115785 266057 := bstep (se 2 (by rfl) ⟨99771, by rfl⟩ : syracuseStep 266057 = 199543) B199543
theorem B331627 : Blo 115785 331627 := bstep (se 1 (by rfl) ⟨248720, by rfl⟩ : syracuseStep 331627 = 497441) B497441
theorem B200623 : Blo 115785 200623 := bstep (se 1 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 200623 = 300935) B300935
theorem B200711 : Blo 115785 200711 := bstep (se 1 (by rfl) ⟨150533, by rfl⟩ : syracuseStep 200711 = 301067) B301067
theorem B397331 : Blo 115785 397331 := bstep (se 1 (by rfl) ⟨297998, by rfl⟩ : syracuseStep 397331 = 595997) B595997
theorem B397655 : Blo 115785 397655 := bstep (se 1 (by rfl) ⟨298241, by rfl⟩ : syracuseStep 397655 = 596483) B596483
theorem B201055 : Blo 115785 201055 := bstep (se 1 (by rfl) ⟨150791, by rfl⟩ : syracuseStep 201055 = 301583) B301583
theorem B201143 : Blo 115785 201143 := bstep (se 1 (by rfl) ⟨150857, by rfl⟩ : syracuseStep 201143 = 301715) B301715
theorem B266849 : Blo 115785 266849 := bstep (se 2 (by rfl) ⟨100068, by rfl⟩ : syracuseStep 266849 = 200137) B200137
theorem B299659 : Blo 115785 299659 := bstep (se 1 (by rfl) ⟨224744, by rfl⟩ : syracuseStep 299659 = 449489) B449489
theorem B496313 : Blo 115785 496313 := bstep (se 2 (by rfl) ⟨186117, by rfl⟩ : syracuseStep 496313 = 372235) B372235
theorem B955165 : Blo 115785 955165 := bstep (se 3 (by rfl) ⟨179093, by rfl⟩ : syracuseStep 955165 = 358187) B358187
theorem B168809 : Blo 115785 168809 := bstep (se 2 (by rfl) ⟨63303, by rfl⟩ : syracuseStep 168809 = 126607) B126607
theorem B594863 : Blo 115785 594863 := bstep (se 1 (by rfl) ⟨446147, by rfl⟩ : syracuseStep 594863 = 892295) B892295
theorem B267191 : Blo 115785 267191 := bstep (se 1 (by rfl) ⟨200393, by rfl⟩ : syracuseStep 267191 = 400787) B400787
theorem B299963 : Blo 115785 299963 := bstep (se 1 (by rfl) ⟨224972, by rfl⟩ : syracuseStep 299963 = 449945) B449945
theorem B168923 : Blo 115785 168923 := bstep (se 1 (by rfl) ⟨126692, by rfl⟩ : syracuseStep 168923 = 253385) B253385
theorem B201737 : Blo 115785 201737 := bstep (se 2 (by rfl) ⟨75651, by rfl⟩ : syracuseStep 201737 = 151303) B151303
theorem B201899 : Blo 115785 201899 := bstep (se 1 (by rfl) ⟨151424, by rfl⟩ : syracuseStep 201899 = 302849) B302849
theorem B398735 : Blo 115785 398735 := bstep (se 1 (by rfl) ⟨299051, by rfl⟩ : syracuseStep 398735 = 598103) B598103
theorem B595343 : Blo 115785 595343 := bstep (se 1 (by rfl) ⟨446507, by rfl⟩ : syracuseStep 595343 = 893015) B893015
theorem B267785 : Blo 115785 267785 := bstep (se 2 (by rfl) ⟨100419, by rfl⟩ : syracuseStep 267785 = 200839) B200839
theorem B300743 : Blo 115785 300743 := bstep (se 1 (by rfl) ⟨225557, by rfl⟩ : syracuseStep 300743 = 451115) B451115
theorem B399059 : Blo 115785 399059 := bstep (se 1 (by rfl) ⟨299294, by rfl⟩ : syracuseStep 399059 = 598589) B598589
theorem B300793 : Blo 115785 300793 := bstep (se 2 (by rfl) ⟨112797, by rfl⟩ : syracuseStep 300793 = 225595) B225595
theorem B268127 : Blo 115785 268127 := bstep (se 1 (by rfl) ⟨201095, by rfl⟩ : syracuseStep 268127 = 402191) B402191
theorem B169823 : Blo 115785 169823 := bstep (se 1 (by rfl) ⟨127367, by rfl⟩ : syracuseStep 169823 = 254735) B254735
theorem B268307 : Blo 115785 268307 := bstep (se 1 (by rfl) ⟨201230, by rfl⟩ : syracuseStep 268307 = 402461) B402461
theorem B268649 : Blo 115785 268649 := bstep (se 2 (by rfl) ⟨100743, by rfl⟩ : syracuseStep 268649 = 201487) B201487
theorem B399745 : Blo 115785 399745 := bstep (se 2 (by rfl) ⟨149904, by rfl⟩ : syracuseStep 399745 = 299809) B299809
theorem B301441 : Blo 115785 301441 := bstep (se 2 (by rfl) ⟨113040, by rfl⟩ : syracuseStep 301441 = 226081) B226081
theorem B14522773 : Blo 115785 14522773 := bstep (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) B680755
theorem B3840493 : Blo 115785 3840493 := bstep (se 3 (by rfl) ⟨720092, by rfl⟩ : syracuseStep 3840493 = 1440185) B1440185
theorem B334361 : Blo 115785 334361 := bstep (se 2 (by rfl) ⟨125385, by rfl⟩ : syracuseStep 334361 = 250771) B250771
theorem B334475 : Blo 115785 334475 := bstep (se 1 (by rfl) ⟨250856, by rfl⟩ : syracuseStep 334475 = 501713) B501713
theorem B564041 : Blo 115785 564041 := bstep (se 2 (by rfl) ⟨211515, by rfl⟩ : syracuseStep 564041 = 423031) B423031
theorem B400247 : Blo 115785 400247 := bstep (se 1 (by rfl) ⟨300185, by rfl⟩ : syracuseStep 400247 = 600371) B600371
theorem B269243 : Blo 115785 269243 := bstep (se 1 (by rfl) ⟨201932, by rfl⟩ : syracuseStep 269243 = 403865) B403865
theorem B498707 : Blo 115785 498707 := bstep (se 1 (by rfl) ⟨374030, by rfl⟩ : syracuseStep 498707 = 748061) B748061
theorem B269369 : Blo 115785 269369 := bstep (se 2 (by rfl) ⟨101013, by rfl⟩ : syracuseStep 269369 = 202027) B202027
theorem B597071 : Blo 115785 597071 := bstep (se 1 (by rfl) ⟨447803, by rfl⟩ : syracuseStep 597071 = 895607) B895607
theorem B400463 : Blo 115785 400463 := bstep (se 1 (by rfl) ⟨300347, by rfl⟩ : syracuseStep 400463 = 600695) B600695
theorem B302251 : Blo 115785 302251 := bstep (se 1 (by rfl) ⟨226688, by rfl⟩ : syracuseStep 302251 = 453377) B453377
theorem B400841 : Blo 115785 400841 := bstep (se 2 (by rfl) ⟨150315, by rfl⟩ : syracuseStep 400841 = 300631) B300631
theorem B302555 : Blo 115785 302555 := bstep (se 1 (by rfl) ⟨226916, by rfl⟩ : syracuseStep 302555 = 453833) B453833
theorem B335483 : Blo 115785 335483 := bstep (se 1 (by rfl) ⟨251612, by rfl⟩ : syracuseStep 335483 = 503225) B503225
theorem B401111 : Blo 115785 401111 := bstep (se 1 (by rfl) ⟨300833, by rfl⟩ : syracuseStep 401111 = 601667) B601667
theorem B892781 : Blo 115785 892781 := bstep (se 3 (by rfl) ⟨167396, by rfl⟩ : syracuseStep 892781 = 334793) B334793
theorem B401327 : Blo 115785 401327 := bstep (se 1 (by rfl) ⟨300995, by rfl⟩ : syracuseStep 401327 = 601991) B601991
theorem B3449141 : Blo 115785 3449141 := bstep (se 5 (by rfl) ⟨161678, by rfl⟩ : syracuseStep 3449141 = 323357) B323357
theorem B500755 : Blo 115785 500755 := bstep (se 1 (by rfl) ⟨375566, by rfl⟩ : syracuseStep 500755 = 751133) B751133
theorem B336953 : Blo 115785 336953 := bstep (se 2 (by rfl) ⟨126357, by rfl⟩ : syracuseStep 336953 = 252715) B252715
theorem B763127 : Blo 115785 763127 := bstep (se 1 (by rfl) ⟨572345, by rfl⟩ : syracuseStep 763127 = 1144691) B1144691
theorem B337277 : Blo 115785 337277 := bstep (se 3 (by rfl) ⟨63239, by rfl⟩ : syracuseStep 337277 = 126479) B126479
theorem B2762387 : Blo 115785 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B173999 : Blo 115785 173999 := bstep (se 1 (by rfl) ⟨130499, by rfl⟩ : syracuseStep 173999 = 260999) B260999
theorem B174089 : Blo 115785 174089 := bstep (se 2 (by rfl) ⟨65283, by rfl⟩ : syracuseStep 174089 = 130567) B130567
theorem B1484837 : Blo 115785 1484837 := bstep (se 4 (by rfl) ⟨139203, by rfl⟩ : syracuseStep 1484837 = 278407) B278407
theorem B174119 : Blo 115785 174119 := bstep (se 1 (by rfl) ⟨130589, by rfl⟩ : syracuseStep 174119 = 261179) B261179
theorem B174203 : Blo 115785 174203 := bstep (se 1 (by rfl) ⟨130652, by rfl⟩ : syracuseStep 174203 = 261305) B261305
theorem B403703 : Blo 115785 403703 := bstep (se 1 (by rfl) ⟨302777, by rfl⟩ : syracuseStep 403703 = 605555) B605555
theorem B174329 : Blo 115785 174329 := bstep (se 2 (by rfl) ⟨65373, by rfl⟩ : syracuseStep 174329 = 130747) B130747
theorem B174431 : Blo 115785 174431 := bstep (se 1 (by rfl) ⟨130823, by rfl⟩ : syracuseStep 174431 = 261647) B261647
theorem B174443 : Blo 115785 174443 := bstep (se 1 (by rfl) ⟨130832, by rfl⟩ : syracuseStep 174443 = 261665) B261665
theorem B1812887 : Blo 115785 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B141751 : Blo 115785 141751 := bstep (se 1 (by rfl) ⟨106313, by rfl⟩ : syracuseStep 141751 = 212627) B212627
theorem B404027 : Blo 115785 404027 := bstep (se 1 (by rfl) ⟨303020, by rfl⟩ : syracuseStep 404027 = 606041) B606041
theorem B174671 : Blo 115785 174671 := bstep (se 1 (by rfl) ⟨131003, by rfl⟩ : syracuseStep 174671 = 262007) B262007
theorem B174791 : Blo 115785 174791 := bstep (se 1 (by rfl) ⟨131093, by rfl⟩ : syracuseStep 174791 = 262187) B262187
theorem B895697 : Blo 115785 895697 := bstep (se 2 (by rfl) ⟨335886, by rfl⟩ : syracuseStep 895697 = 671773) B671773
theorem B174953 : Blo 115785 174953 := bstep (se 2 (by rfl) ⟨65607, by rfl⟩ : syracuseStep 174953 = 131215) B131215
theorem B338849 : Blo 115785 338849 := bstep (se 2 (by rfl) ⟨127068, by rfl⟩ : syracuseStep 338849 = 254137) B254137
theorem B175031 : Blo 115785 175031 := bstep (se 1 (by rfl) ⟨131273, by rfl⟩ : syracuseStep 175031 = 262547) B262547
theorem B175067 : Blo 115785 175067 := bstep (se 1 (by rfl) ⟨131300, by rfl⟩ : syracuseStep 175067 = 262601) B262601
theorem B339191 : Blo 115785 339191 := bstep (se 1 (by rfl) ⟨254393, by rfl⟩ : syracuseStep 339191 = 508787) B508787
theorem B1518871 : Blo 115785 1518871 := bstep (se 1 (by rfl) ⟨1139153, by rfl⟩ : syracuseStep 1518871 = 2278307) B2278307
theorem B175535 : Blo 115785 175535 := bstep (se 1 (by rfl) ⟨131651, by rfl⟩ : syracuseStep 175535 = 263303) B263303
theorem B175625 : Blo 115785 175625 := bstep (se 2 (by rfl) ⟨65859, by rfl⟩ : syracuseStep 175625 = 131719) B131719
theorem B175655 : Blo 115785 175655 := bstep (se 1 (by rfl) ⟨131741, by rfl⟩ : syracuseStep 175655 = 263483) B263483
theorem B175739 : Blo 115785 175739 := bstep (se 1 (by rfl) ⟨131804, by rfl⟩ : syracuseStep 175739 = 263609) B263609
theorem B994949 : Blo 115785 994949 := bstep (se 4 (by rfl) ⟨93276, by rfl⟩ : syracuseStep 994949 = 186553) B186553
theorem B765587 : Blo 115785 765587 := bstep (se 1 (by rfl) ⟨574190, by rfl⟩ : syracuseStep 765587 = 1148381) B1148381
theorem B175865 : Blo 115785 175865 := bstep (se 2 (by rfl) ⟨65949, by rfl⟩ : syracuseStep 175865 = 131899) B131899
theorem B175967 : Blo 115785 175967 := bstep (se 1 (by rfl) ⟨131975, by rfl⟩ : syracuseStep 175967 = 263951) B263951
theorem B175979 : Blo 115785 175979 := bstep (se 1 (by rfl) ⟨131984, by rfl⟩ : syracuseStep 175979 = 263969) B263969
theorem B176207 : Blo 115785 176207 := bstep (se 1 (by rfl) ⟨132155, by rfl⟩ : syracuseStep 176207 = 264311) B264311
theorem B569501 : Blo 115785 569501 := bstep (se 3 (by rfl) ⟨106781, by rfl⟩ : syracuseStep 569501 = 213563) B213563
theorem B1355939 : Blo 115785 1355939 := bstep (se 1 (by rfl) ⟨1016954, by rfl⟩ : syracuseStep 1355939 = 2033909) B2033909
theorem B176327 : Blo 115785 176327 := bstep (se 1 (by rfl) ⟨132245, by rfl⟩ : syracuseStep 176327 = 264491) B264491
theorem B405847 : Blo 115785 405847 := bstep (se 1 (by rfl) ⟨304385, by rfl⟩ : syracuseStep 405847 = 608771) B608771
theorem B602473 : Blo 115785 602473 := bstep (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) B451855
theorem B176489 : Blo 115785 176489 := bstep (se 2 (by rfl) ⟨66183, by rfl⟩ : syracuseStep 176489 = 132367) B132367
theorem B176567 : Blo 115785 176567 := bstep (se 1 (by rfl) ⟨132425, by rfl⟩ : syracuseStep 176567 = 264851) B264851
theorem B176603 : Blo 115785 176603 := bstep (se 1 (by rfl) ⟨132452, by rfl⟩ : syracuseStep 176603 = 264905) B264905
theorem B537299 : Blo 115785 537299 := bstep (se 1 (by rfl) ⟨402974, by rfl⟩ : syracuseStep 537299 = 805949) B805949
theorem B177071 : Blo 115785 177071 := bstep (se 1 (by rfl) ⟨132803, by rfl⟩ : syracuseStep 177071 = 265607) B265607
theorem B177161 : Blo 115785 177161 := bstep (se 2 (by rfl) ⟨66435, by rfl⟩ : syracuseStep 177161 = 132871) B132871
theorem B177191 : Blo 115785 177191 := bstep (se 1 (by rfl) ⟨132893, by rfl⟩ : syracuseStep 177191 = 265787) B265787
theorem B898127 : Blo 115785 898127 := bstep (se 1 (by rfl) ⟨673595, by rfl⟩ : syracuseStep 898127 = 1347191) B1347191
theorem B177275 : Blo 115785 177275 := bstep (se 1 (by rfl) ⟨132956, by rfl⟩ : syracuseStep 177275 = 265913) B265913
theorem B177401 : Blo 115785 177401 := bstep (se 2 (by rfl) ⟨66525, by rfl⟩ : syracuseStep 177401 = 133051) B133051
theorem B177503 : Blo 115785 177503 := bstep (se 1 (by rfl) ⟨133127, by rfl⟩ : syracuseStep 177503 = 266255) B266255
theorem B177515 : Blo 115785 177515 := bstep (se 1 (by rfl) ⟨133136, by rfl⟩ : syracuseStep 177515 = 266273) B266273
theorem B603611 : Blo 115785 603611 := bstep (se 1 (by rfl) ⟨452708, by rfl⟩ : syracuseStep 603611 = 905417) B905417
theorem B374311 : Blo 115785 374311 := bstep (se 1 (by rfl) ⟨280733, by rfl⟩ : syracuseStep 374311 = 561467) B561467
theorem B177743 : Blo 115785 177743 := bstep (se 1 (by rfl) ⟨133307, by rfl⟩ : syracuseStep 177743 = 266615) B266615
theorem B210529 : Blo 115785 210529 := bstep (se 2 (by rfl) ⟨78948, by rfl⟩ : syracuseStep 210529 = 157897) B157897
theorem B669383 : Blo 115785 669383 := bstep (se 1 (by rfl) ⟨502037, by rfl⟩ : syracuseStep 669383 = 1004075) B1004075
theorem B177863 : Blo 115785 177863 := bstep (se 1 (by rfl) ⟨133397, by rfl⟩ : syracuseStep 177863 = 266795) B266795
theorem B178025 : Blo 115785 178025 := bstep (se 2 (by rfl) ⟨66759, by rfl⟩ : syracuseStep 178025 = 133519) B133519
theorem B440225 : Blo 115785 440225 := bstep (se 2 (by rfl) ⟨165084, by rfl⟩ : syracuseStep 440225 = 330169) B330169
theorem B178103 : Blo 115785 178103 := bstep (se 1 (by rfl) ⟨133577, by rfl⟩ : syracuseStep 178103 = 267155) B267155
theorem B604097 : Blo 115785 604097 := bstep (se 2 (by rfl) ⟨226536, by rfl⟩ : syracuseStep 604097 = 453073) B453073
theorem B178139 : Blo 115785 178139 := bstep (se 1 (by rfl) ⟨133604, by rfl⟩ : syracuseStep 178139 = 267209) B267209
theorem B1554565 : Blo 115785 1554565 := bstep (se 4 (by rfl) ⟨145740, by rfl⟩ : syracuseStep 1554565 = 291481) B291481
theorem B3225757 : Blo 115785 3225757 := bstep (se 3 (by rfl) ⟨604829, by rfl⟩ : syracuseStep 3225757 = 1209659) B1209659
theorem B342401 : Blo 115785 342401 := bstep (se 2 (by rfl) ⟨128400, by rfl⟩ : syracuseStep 342401 = 256801) B256801
theorem B1456535 : Blo 115785 1456535 := bstep (se 1 (by rfl) ⟨1092401, by rfl⟩ : syracuseStep 1456535 = 2184803) B2184803
theorem B178607 : Blo 115785 178607 := bstep (se 1 (by rfl) ⟨133955, by rfl⟩ : syracuseStep 178607 = 267911) B267911
theorem B178697 : Blo 115785 178697 := bstep (se 2 (by rfl) ⟨67011, by rfl⟩ : syracuseStep 178697 = 134023) B134023
theorem B178727 : Blo 115785 178727 := bstep (se 1 (by rfl) ⟨134045, by rfl⟩ : syracuseStep 178727 = 268091) B268091
theorem B178811 : Blo 115785 178811 := bstep (se 1 (by rfl) ⟨134108, by rfl⟩ : syracuseStep 178811 = 268217) B268217
theorem B178937 : Blo 115785 178937 := bstep (se 2 (by rfl) ⟨67101, by rfl⟩ : syracuseStep 178937 = 134203) B134203
theorem B179039 : Blo 115785 179039 := bstep (se 1 (by rfl) ⟨134279, by rfl⟩ : syracuseStep 179039 = 268559) B268559
theorem B179051 : Blo 115785 179051 := bstep (se 1 (by rfl) ⟨134288, by rfl⟩ : syracuseStep 179051 = 268577) B268577
theorem B441197 : Blo 115785 441197 := bstep (se 3 (by rfl) ⟨82724, by rfl⟩ : syracuseStep 441197 = 165449) B165449
theorem B342967 : Blo 115785 342967 := bstep (se 1 (by rfl) ⟨257225, by rfl⟩ : syracuseStep 342967 = 514451) B514451
theorem B179279 : Blo 115785 179279 := bstep (se 1 (by rfl) ⟨134459, by rfl⟩ : syracuseStep 179279 = 268919) B268919
theorem B179399 : Blo 115785 179399 := bstep (se 1 (by rfl) ⟨134549, by rfl⟩ : syracuseStep 179399 = 269099) B269099
theorem B1260791 : Blo 115785 1260791 := bstep (se 1 (by rfl) ⟨945593, by rfl⟩ : syracuseStep 1260791 = 1891187) B1891187
theorem B1719575 : Blo 115785 1719575 := bstep (se 1 (by rfl) ⟨1289681, by rfl⟩ : syracuseStep 1719575 = 2579363) B2579363
theorem B179561 : Blo 115785 179561 := bstep (se 2 (by rfl) ⟨67335, by rfl⟩ : syracuseStep 179561 = 134671) B134671
theorem B146863 : Blo 115785 146863 := bstep (se 1 (by rfl) ⟨110147, by rfl⟩ : syracuseStep 146863 = 220295) B220295
theorem B179639 : Blo 115785 179639 := bstep (se 1 (by rfl) ⟨134729, by rfl⟩ : syracuseStep 179639 = 269459) B269459
theorem B376265 : Blo 115785 376265 := bstep (se 2 (by rfl) ⟨141099, by rfl⟩ : syracuseStep 376265 = 282199) B282199
theorem B179675 : Blo 115785 179675 := bstep (se 1 (by rfl) ⟨134756, by rfl⟩ : syracuseStep 179675 = 269513) B269513
theorem B441881 : Blo 115785 441881 := bstep (se 2 (by rfl) ⟨165705, by rfl⟩ : syracuseStep 441881 = 331411) B331411
theorem B441895 : Blo 115785 441895 := bstep (se 1 (by rfl) ⟨331421, by rfl⟩ : syracuseStep 441895 = 662843) B662843
theorem B180073 : Blo 115785 180073 := bstep (se 2 (by rfl) ⟨67527, by rfl⟩ : syracuseStep 180073 = 135055) B135055
theorem B933767 : Blo 115785 933767 := bstep (se 1 (by rfl) ⟨700325, by rfl⟩ : syracuseStep 933767 = 1400651) B1400651
theorem B606365 : Blo 115785 606365 := bstep (se 3 (by rfl) ⟨113693, by rfl⟩ : syracuseStep 606365 = 227387) B227387
theorem B180473 : Blo 115785 180473 := bstep (se 2 (by rfl) ⟨67677, by rfl⟩ : syracuseStep 180473 = 135355) B135355
theorem B442685 : Blo 115785 442685 := bstep (se 3 (by rfl) ⟨83003, by rfl⟩ : syracuseStep 442685 = 166007) B166007
theorem B901529 : Blo 115785 901529 := bstep (se 2 (by rfl) ⟨338073, by rfl⟩ : syracuseStep 901529 = 676147) B676147
theorem B442867 : Blo 115785 442867 := bstep (se 1 (by rfl) ⟨332150, by rfl⟩ : syracuseStep 442867 = 664301) B664301
theorem B148007 : Blo 115785 148007 := bstep (se 1 (by rfl) ⟨111005, by rfl⟩ : syracuseStep 148007 = 222011) B222011
theorem B148331 : Blo 115785 148331 := bstep (se 1 (by rfl) ⟨111248, by rfl⟩ : syracuseStep 148331 = 222497) B222497
theorem B1917917 : Blo 115785 1917917 := bstep (se 3 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 1917917 = 719219) B719219
theorem B115791 : Blo 115785 115791 := bstep (se 1 (by rfl) ⟨86843, by rfl⟩ : syracuseStep 115791 = 173687) B173687
theorem B115807 : Blo 115785 115807 := bstep (se 1 (by rfl) ⟨86855, by rfl⟩ : syracuseStep 115807 = 173711) B173711
theorem B115835 : Blo 115785 115835 := bstep (se 1 (by rfl) ⟨86876, by rfl⟩ : syracuseStep 115835 = 173753) B173753
theorem B115887 : Blo 115785 115887 := bstep (se 1 (by rfl) ⟨86915, by rfl⟩ : syracuseStep 115887 = 173831) B173831
theorem B115911 : Blo 115785 115911 := bstep (se 1 (by rfl) ⟨86933, by rfl⟩ : syracuseStep 115911 = 173867) B173867
theorem B115931 : Blo 115785 115931 := bstep (se 1 (by rfl) ⟨86948, by rfl⟩ : syracuseStep 115931 = 173897) B173897
theorem B116007 : Blo 115785 116007 := bstep (se 1 (by rfl) ⟨87005, by rfl⟩ : syracuseStep 116007 = 174011) B174011
theorem B116047 : Blo 115785 116047 := bstep (se 1 (by rfl) ⟨87035, by rfl⟩ : syracuseStep 116047 = 174071) B174071
theorem B116063 : Blo 115785 116063 := bstep (se 1 (by rfl) ⟨87047, by rfl⟩ : syracuseStep 116063 = 174095) B174095
theorem B116091 : Blo 115785 116091 := bstep (se 1 (by rfl) ⟨87068, by rfl⟩ : syracuseStep 116091 = 174137) B174137
theorem B116143 : Blo 115785 116143 := bstep (se 1 (by rfl) ⟨87107, by rfl⟩ : syracuseStep 116143 = 174215) B174215
theorem B116167 : Blo 115785 116167 := bstep (se 1 (by rfl) ⟨87125, by rfl⟩ : syracuseStep 116167 = 174251) B174251
theorem B116187 : Blo 115785 116187 := bstep (se 1 (by rfl) ⟨87140, by rfl⟩ : syracuseStep 116187 = 174281) B174281
theorem B116263 : Blo 115785 116263 := bstep (se 1 (by rfl) ⟨87197, by rfl⟩ : syracuseStep 116263 = 174395) B174395
theorem B116303 : Blo 115785 116303 := bstep (se 1 (by rfl) ⟨87227, by rfl⟩ : syracuseStep 116303 = 174455) B174455
theorem B116319 : Blo 115785 116319 := bstep (se 1 (by rfl) ⟨87239, by rfl⟩ : syracuseStep 116319 = 174479) B174479
theorem B116347 : Blo 115785 116347 := bstep (se 1 (by rfl) ⟨87260, by rfl⟩ : syracuseStep 116347 = 174521) B174521
theorem B1492627 : Blo 115785 1492627 := bstep (se 1 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 1492627 = 2238941) B2238941
theorem B116399 : Blo 115785 116399 := bstep (se 1 (by rfl) ⟨87299, by rfl⟩ : syracuseStep 116399 = 174599) B174599
theorem B378553 : Blo 115785 378553 := bstep (se 2 (by rfl) ⟨141957, by rfl⟩ : syracuseStep 378553 = 283915) B283915
theorem B116423 : Blo 115785 116423 := bstep (se 1 (by rfl) ⟨87317, by rfl⟩ : syracuseStep 116423 = 174635) B174635
theorem B444113 : Blo 115785 444113 := bstep (se 2 (by rfl) ⟨166542, by rfl⟩ : syracuseStep 444113 = 333085) B333085
theorem B476887 : Blo 115785 476887 := bstep (se 1 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 476887 = 715331) B715331
theorem B116443 : Blo 115785 116443 := bstep (se 1 (by rfl) ⟨87332, by rfl⟩ : syracuseStep 116443 = 174665) B174665
theorem B116519 : Blo 115785 116519 := bstep (se 1 (by rfl) ⟨87389, by rfl⟩ : syracuseStep 116519 = 174779) B174779
theorem B116559 : Blo 115785 116559 := bstep (se 1 (by rfl) ⟨87419, by rfl⟩ : syracuseStep 116559 = 174839) B174839
theorem B116575 : Blo 115785 116575 := bstep (se 1 (by rfl) ⟨87431, by rfl⟩ : syracuseStep 116575 = 174863) B174863
theorem B116603 : Blo 115785 116603 := bstep (se 1 (by rfl) ⟨87452, by rfl⟩ : syracuseStep 116603 = 174905) B174905
theorem B4638617 : Blo 115785 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B116655 : Blo 115785 116655 := bstep (se 1 (by rfl) ⟨87491, by rfl⟩ : syracuseStep 116655 = 174983) B174983
theorem B116679 : Blo 115785 116679 := bstep (se 1 (by rfl) ⟨87509, by rfl⟩ : syracuseStep 116679 = 175019) B175019
theorem B116699 : Blo 115785 116699 := bstep (se 1 (by rfl) ⟨87524, by rfl⟩ : syracuseStep 116699 = 175049) B175049
theorem B116775 : Blo 115785 116775 := bstep (se 1 (by rfl) ⟨87581, by rfl⟩ : syracuseStep 116775 = 175163) B175163
theorem B116815 : Blo 115785 116815 := bstep (se 1 (by rfl) ⟨87611, by rfl⟩ : syracuseStep 116815 = 175223) B175223
theorem B116831 : Blo 115785 116831 := bstep (se 1 (by rfl) ⟨87623, by rfl⟩ : syracuseStep 116831 = 175247) B175247
theorem B116859 : Blo 115785 116859 := bstep (se 1 (by rfl) ⟨87644, by rfl⟩ : syracuseStep 116859 = 175289) B175289
theorem B149627 : Blo 115785 149627 := bstep (se 1 (by rfl) ⟨112220, by rfl⟩ : syracuseStep 149627 = 224441) B224441
theorem B116911 : Blo 115785 116911 := bstep (se 1 (by rfl) ⟨87683, by rfl⟩ : syracuseStep 116911 = 175367) B175367
theorem B116935 : Blo 115785 116935 := bstep (se 1 (by rfl) ⟨87701, by rfl⟩ : syracuseStep 116935 = 175403) B175403
theorem B116955 : Blo 115785 116955 := bstep (se 1 (by rfl) ⟨87716, by rfl⟩ : syracuseStep 116955 = 175433) B175433
theorem B117031 : Blo 115785 117031 := bstep (se 1 (by rfl) ⟨87773, by rfl⟩ : syracuseStep 117031 = 175547) B175547
theorem B903473 : Blo 115785 903473 := bstep (se 2 (by rfl) ⟨338802, by rfl⟩ : syracuseStep 903473 = 677605) B677605
theorem B117071 : Blo 115785 117071 := bstep (se 1 (by rfl) ⟨87803, by rfl⟩ : syracuseStep 117071 = 175607) B175607
theorem B117087 : Blo 115785 117087 := bstep (se 1 (by rfl) ⟨87815, by rfl⟩ : syracuseStep 117087 = 175631) B175631
theorem B117115 : Blo 115785 117115 := bstep (se 1 (by rfl) ⟨87836, by rfl⟩ : syracuseStep 117115 = 175673) B175673
theorem B444797 : Blo 115785 444797 := bstep (se 3 (by rfl) ⟨83399, by rfl⟩ : syracuseStep 444797 = 166799) B166799
theorem B1296773 : Blo 115785 1296773 := bstep (se 4 (by rfl) ⟨121572, by rfl⟩ : syracuseStep 1296773 = 243145) B243145
theorem B117167 : Blo 115785 117167 := bstep (se 1 (by rfl) ⟨87875, by rfl⟩ : syracuseStep 117167 = 175751) B175751
theorem B117191 : Blo 115785 117191 := bstep (se 1 (by rfl) ⟨87893, by rfl⟩ : syracuseStep 117191 = 175787) B175787
theorem B1133003 : Blo 115785 1133003 := bstep (se 1 (by rfl) ⟨849752, by rfl⟩ : syracuseStep 1133003 = 1699505) B1699505
theorem B117211 : Blo 115785 117211 := bstep (se 1 (by rfl) ⟨87908, by rfl⟩ : syracuseStep 117211 = 175817) B175817
theorem B117287 : Blo 115785 117287 := bstep (se 1 (by rfl) ⟨87965, by rfl⟩ : syracuseStep 117287 = 175931) B175931
theorem B117327 : Blo 115785 117327 := bstep (se 1 (by rfl) ⟨87995, by rfl⟩ : syracuseStep 117327 = 175991) B175991
theorem B117343 : Blo 115785 117343 := bstep (se 1 (by rfl) ⟨88007, by rfl⟩ : syracuseStep 117343 = 176015) B176015
theorem B117371 : Blo 115785 117371 := bstep (se 1 (by rfl) ⟨88028, by rfl⟩ : syracuseStep 117371 = 176057) B176057
theorem B117423 : Blo 115785 117423 := bstep (se 1 (by rfl) ⟨88067, by rfl⟩ : syracuseStep 117423 = 176135) B176135
theorem B117447 : Blo 115785 117447 := bstep (se 1 (by rfl) ⟨88085, by rfl⟩ : syracuseStep 117447 = 176171) B176171
theorem B117467 : Blo 115785 117467 := bstep (se 1 (by rfl) ⟨88100, by rfl⟩ : syracuseStep 117467 = 176201) B176201
theorem B117543 : Blo 115785 117543 := bstep (se 1 (by rfl) ⟨88157, by rfl⟩ : syracuseStep 117543 = 176315) B176315
theorem B117583 : Blo 115785 117583 := bstep (se 1 (by rfl) ⟨88187, by rfl⟩ : syracuseStep 117583 = 176375) B176375
theorem B117599 : Blo 115785 117599 := bstep (se 1 (by rfl) ⟨88199, by rfl⟩ : syracuseStep 117599 = 176399) B176399
theorem B117627 : Blo 115785 117627 := bstep (se 1 (by rfl) ⟨88220, by rfl⟩ : syracuseStep 117627 = 176441) B176441
theorem B117679 : Blo 115785 117679 := bstep (se 1 (by rfl) ⟨88259, by rfl⟩ : syracuseStep 117679 = 176519) B176519
theorem B2214839 : Blo 115785 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B117703 : Blo 115785 117703 := bstep (se 1 (by rfl) ⟨88277, by rfl⟩ : syracuseStep 117703 = 176555) B176555
theorem B117723 : Blo 115785 117723 := bstep (se 1 (by rfl) ⟨88292, by rfl⟩ : syracuseStep 117723 = 176585) B176585
theorem B117799 : Blo 115785 117799 := bstep (se 1 (by rfl) ⟨88349, by rfl⟩ : syracuseStep 117799 = 176699) B176699
theorem B281657 : Blo 115785 281657 := bstep (se 2 (by rfl) ⟨105621, by rfl⟩ : syracuseStep 281657 = 211243) B211243
theorem B117839 : Blo 115785 117839 := bstep (se 1 (by rfl) ⟨88379, by rfl⟩ : syracuseStep 117839 = 176759) B176759
theorem B117855 : Blo 115785 117855 := bstep (se 1 (by rfl) ⟨88391, by rfl⟩ : syracuseStep 117855 = 176783) B176783
theorem B117883 : Blo 115785 117883 := bstep (se 1 (by rfl) ⟨88412, by rfl⟩ : syracuseStep 117883 = 176825) B176825
theorem B117935 : Blo 115785 117935 := bstep (se 1 (by rfl) ⟨88451, by rfl⟩ : syracuseStep 117935 = 176903) B176903
theorem B117959 : Blo 115785 117959 := bstep (se 1 (by rfl) ⟨88469, by rfl⟩ : syracuseStep 117959 = 176939) B176939
theorem B117979 : Blo 115785 117979 := bstep (se 1 (by rfl) ⟨88484, by rfl⟩ : syracuseStep 117979 = 176969) B176969
theorem B118055 : Blo 115785 118055 := bstep (se 1 (by rfl) ⟨88541, by rfl⟩ : syracuseStep 118055 = 177083) B177083
theorem B118095 : Blo 115785 118095 := bstep (se 1 (by rfl) ⟨88571, by rfl⟩ : syracuseStep 118095 = 177143) B177143
theorem B445783 : Blo 115785 445783 := bstep (se 1 (by rfl) ⟨334337, by rfl⟩ : syracuseStep 445783 = 668675) B668675
theorem B118111 : Blo 115785 118111 := bstep (se 1 (by rfl) ⟨88583, by rfl⟩ : syracuseStep 118111 = 177167) B177167
theorem B118139 : Blo 115785 118139 := bstep (se 1 (by rfl) ⟨88604, by rfl⟩ : syracuseStep 118139 = 177209) B177209
theorem B675215 : Blo 115785 675215 := bstep (se 1 (by rfl) ⟨506411, by rfl⟩ : syracuseStep 675215 = 1012823) B1012823
theorem B118191 : Blo 115785 118191 := bstep (se 1 (by rfl) ⟨88643, by rfl⟩ : syracuseStep 118191 = 177287) B177287
theorem B118215 : Blo 115785 118215 := bstep (se 1 (by rfl) ⟨88661, by rfl⟩ : syracuseStep 118215 = 177323) B177323
theorem B642505 : Blo 115785 642505 := bstep (se 2 (by rfl) ⟨240939, by rfl⟩ : syracuseStep 642505 = 481879) B481879
theorem B118235 : Blo 115785 118235 := bstep (se 1 (by rfl) ⟨88676, by rfl⟩ : syracuseStep 118235 = 177353) B177353
theorem B118311 : Blo 115785 118311 := bstep (se 1 (by rfl) ⟨88733, by rfl⟩ : syracuseStep 118311 = 177467) B177467
theorem B118351 : Blo 115785 118351 := bstep (se 1 (by rfl) ⟨88763, by rfl⟩ : syracuseStep 118351 = 177527) B177527
theorem B118367 : Blo 115785 118367 := bstep (se 1 (by rfl) ⟨88775, by rfl⟩ : syracuseStep 118367 = 177551) B177551
theorem B118395 : Blo 115785 118395 := bstep (se 1 (by rfl) ⟨88796, by rfl⟩ : syracuseStep 118395 = 177593) B177593
theorem B446087 : Blo 115785 446087 := bstep (se 1 (by rfl) ⟨334565, by rfl⟩ : syracuseStep 446087 = 669131) B669131
theorem B118447 : Blo 115785 118447 := bstep (se 1 (by rfl) ⟨88835, by rfl⟩ : syracuseStep 118447 = 177671) B177671
theorem B118471 : Blo 115785 118471 := bstep (se 1 (by rfl) ⟨88853, by rfl⟩ : syracuseStep 118471 = 177707) B177707
theorem B118491 : Blo 115785 118491 := bstep (se 1 (by rfl) ⟨88868, by rfl⟩ : syracuseStep 118491 = 177737) B177737
theorem B118567 : Blo 115785 118567 := bstep (se 1 (by rfl) ⟨88925, by rfl⟩ : syracuseStep 118567 = 177851) B177851
theorem B118607 : Blo 115785 118607 := bstep (se 1 (by rfl) ⟨88955, by rfl⟩ : syracuseStep 118607 = 177911) B177911
theorem B118623 : Blo 115785 118623 := bstep (se 1 (by rfl) ⟨88967, by rfl⟩ : syracuseStep 118623 = 177935) B177935
theorem B118651 : Blo 115785 118651 := bstep (se 1 (by rfl) ⟨88988, by rfl⟩ : syracuseStep 118651 = 177977) B177977
theorem B118703 : Blo 115785 118703 := bstep (se 1 (by rfl) ⟨89027, by rfl⟩ : syracuseStep 118703 = 178055) B178055
theorem B118727 : Blo 115785 118727 := bstep (se 1 (by rfl) ⟨89045, by rfl⟩ : syracuseStep 118727 = 178091) B178091
theorem B118747 : Blo 115785 118747 := bstep (se 1 (by rfl) ⟨89060, by rfl⟩ : syracuseStep 118747 = 178121) B178121
theorem B118823 : Blo 115785 118823 := bstep (se 1 (by rfl) ⟨89117, by rfl⟩ : syracuseStep 118823 = 178235) B178235
theorem B446543 : Blo 115785 446543 := bstep (se 1 (by rfl) ⟨334907, by rfl⟩ : syracuseStep 446543 = 669815) B669815
theorem B118863 : Blo 115785 118863 := bstep (se 1 (by rfl) ⟨89147, by rfl⟩ : syracuseStep 118863 = 178295) B178295
theorem B118879 : Blo 115785 118879 := bstep (se 1 (by rfl) ⟨89159, by rfl⟩ : syracuseStep 118879 = 178319) B178319
theorem B118907 : Blo 115785 118907 := bstep (se 1 (by rfl) ⟨89180, by rfl⟩ : syracuseStep 118907 = 178361) B178361
theorem B118959 : Blo 115785 118959 := bstep (se 1 (by rfl) ⟨89219, by rfl⟩ : syracuseStep 118959 = 178439) B178439
theorem B118983 : Blo 115785 118983 := bstep (se 1 (by rfl) ⟨89237, by rfl⟩ : syracuseStep 118983 = 178475) B178475
theorem B119003 : Blo 115785 119003 := bstep (se 1 (by rfl) ⟨89252, by rfl⟩ : syracuseStep 119003 = 178505) B178505
theorem B119079 : Blo 115785 119079 := bstep (se 1 (by rfl) ⟨89309, by rfl⟩ : syracuseStep 119079 = 178619) B178619
theorem B119119 : Blo 115785 119119 := bstep (se 1 (by rfl) ⟨89339, by rfl⟩ : syracuseStep 119119 = 178679) B178679
theorem B119135 : Blo 115785 119135 := bstep (se 1 (by rfl) ⟨89351, by rfl⟩ : syracuseStep 119135 = 178703) B178703
theorem B119163 : Blo 115785 119163 := bstep (se 1 (by rfl) ⟨89372, by rfl⟩ : syracuseStep 119163 = 178745) B178745
theorem B643457 : Blo 115785 643457 := bstep (se 2 (by rfl) ⟨241296, by rfl⟩ : syracuseStep 643457 = 482593) B482593
theorem B119215 : Blo 115785 119215 := bstep (se 1 (by rfl) ⟨89411, by rfl⟩ : syracuseStep 119215 = 178823) B178823
theorem B119239 : Blo 115785 119239 := bstep (se 1 (by rfl) ⟨89429, by rfl⟩ : syracuseStep 119239 = 178859) B178859
theorem B119259 : Blo 115785 119259 := bstep (se 1 (by rfl) ⟨89444, by rfl⟩ : syracuseStep 119259 = 178889) B178889
theorem B381449 : Blo 115785 381449 := bstep (se 2 (by rfl) ⟨143043, by rfl⟩ : syracuseStep 381449 = 286087) B286087
theorem B414233 : Blo 115785 414233 := bstep (se 2 (by rfl) ⟨155337, by rfl⟩ : syracuseStep 414233 = 310675) B310675
theorem B119335 : Blo 115785 119335 := bstep (se 1 (by rfl) ⟨89501, by rfl⟩ : syracuseStep 119335 = 179003) B179003
theorem B119375 : Blo 115785 119375 := bstep (se 1 (by rfl) ⟨89531, by rfl⟩ : syracuseStep 119375 = 179063) B179063
theorem B119391 : Blo 115785 119391 := bstep (se 1 (by rfl) ⟨89543, by rfl⟩ : syracuseStep 119391 = 179087) B179087
theorem B119419 : Blo 115785 119419 := bstep (se 1 (by rfl) ⟨89564, by rfl⟩ : syracuseStep 119419 = 179129) B179129
theorem B742061 : Blo 115785 742061 := bstep (se 3 (by rfl) ⟨139136, by rfl⟩ : syracuseStep 742061 = 278273) B278273
theorem B119471 : Blo 115785 119471 := bstep (se 1 (by rfl) ⟨89603, by rfl⟩ : syracuseStep 119471 = 179207) B179207
theorem B119495 : Blo 115785 119495 := bstep (se 1 (by rfl) ⟨89621, by rfl⟩ : syracuseStep 119495 = 179243) B179243
theorem B119515 : Blo 115785 119515 := bstep (se 1 (by rfl) ⟨89636, by rfl⟩ : syracuseStep 119515 = 179273) B179273
theorem B119591 : Blo 115785 119591 := bstep (se 1 (by rfl) ⟨89693, by rfl⟩ : syracuseStep 119591 = 179387) B179387
theorem B119631 : Blo 115785 119631 := bstep (se 1 (by rfl) ⟨89723, by rfl⟩ : syracuseStep 119631 = 179447) B179447
theorem B119647 : Blo 115785 119647 := bstep (se 1 (by rfl) ⟨89735, by rfl⟩ : syracuseStep 119647 = 179471) B179471
theorem B119675 : Blo 115785 119675 := bstep (se 1 (by rfl) ⟨89756, by rfl⟩ : syracuseStep 119675 = 179513) B179513
theorem B381871 : Blo 115785 381871 := bstep (se 1 (by rfl) ⟨286403, by rfl⟩ : syracuseStep 381871 = 572807) B572807
theorem B119727 : Blo 115785 119727 := bstep (se 1 (by rfl) ⟨89795, by rfl⟩ : syracuseStep 119727 = 179591) B179591
theorem B119751 : Blo 115785 119751 := bstep (se 1 (by rfl) ⟨89813, by rfl⟩ : syracuseStep 119751 = 179627) B179627
theorem B119771 : Blo 115785 119771 := bstep (se 1 (by rfl) ⟨89828, by rfl⟩ : syracuseStep 119771 = 179657) B179657
theorem B447545 : Blo 115785 447545 := bstep (se 2 (by rfl) ⟨167829, by rfl⟩ : syracuseStep 447545 = 335659) B335659
theorem B382333 : Blo 115785 382333 := bstep (se 3 (by rfl) ⟨71687, by rfl⟩ : syracuseStep 382333 = 143375) B143375
theorem B906875 : Blo 115785 906875 := bstep (se 1 (by rfl) ⟨680156, by rfl⟩ : syracuseStep 906875 = 1360313) B1360313
theorem B644755 : Blo 115785 644755 := bstep (se 1 (by rfl) ⟨483566, by rfl⟩ : syracuseStep 644755 = 967133) B967133
theorem B448199 : Blo 115785 448199 := bstep (se 1 (by rfl) ⟨336149, by rfl⟩ : syracuseStep 448199 = 672299) B672299
theorem B710365 : Blo 115785 710365 := bstep (se 3 (by rfl) ⟨133193, by rfl⟩ : syracuseStep 710365 = 266387) B266387
theorem B1005473 : Blo 115785 1005473 := bstep (se 2 (by rfl) ⟨377052, by rfl⟩ : syracuseStep 1005473 = 754105) B754105
theorem B317447 : Blo 115785 317447 := bstep (se 1 (by rfl) ⟨238085, by rfl⟩ : syracuseStep 317447 = 476171) B476171
theorem B317611 : Blo 115785 317611 := bstep (se 1 (by rfl) ⟨238208, by rfl⟩ : syracuseStep 317611 = 476417) B476417
theorem B907649 : Blo 115785 907649 := bstep (se 2 (by rfl) ⟨340368, by rfl⟩ : syracuseStep 907649 = 680737) B680737
theorem B809453 : Blo 115785 809453 := bstep (se 3 (by rfl) ⟨151772, by rfl⟩ : syracuseStep 809453 = 303545) B303545
theorem B1071751 : Blo 115785 1071751 := bstep (se 1 (by rfl) ⟨803813, by rfl⟩ : syracuseStep 1071751 = 1607627) B1607627
theorem B449171 : Blo 115785 449171 := bstep (se 1 (by rfl) ⟨336878, by rfl⟩ : syracuseStep 449171 = 673757) B673757
theorem B219847 : Blo 115785 219847 := bstep (se 1 (by rfl) ⟨164885, by rfl⟩ : syracuseStep 219847 = 329771) B329771
theorem B285943 : Blo 115785 285943 := bstep (se 1 (by rfl) ⟨214457, by rfl⟩ : syracuseStep 285943 = 428915) B428915
theorem B941701 : Blo 115785 941701 := bstep (se 4 (by rfl) ⟨88284, by rfl⟩ : syracuseStep 941701 = 176569) B176569
theorem B941959 : Blo 115785 941959 := bstep (se 1 (by rfl) ⟨706469, by rfl⟩ : syracuseStep 941959 = 1412939) B1412939
theorem B188335 : Blo 115785 188335 := bstep (se 1 (by rfl) ⟨141251, by rfl⟩ : syracuseStep 188335 = 282503) B282503
theorem B1466545 : Blo 115785 1466545 := bstep (se 2 (by rfl) ⟨549954, by rfl⟩ : syracuseStep 1466545 = 1099909) B1099909
theorem B12312931 : Blo 115785 12312931 := bstep (se 1 (by rfl) ⟨9234698, by rfl⟩ : syracuseStep 12312931 = 18469397) B18469397
theorem B188777 : Blo 115785 188777 := bstep (se 2 (by rfl) ⟨70791, by rfl⟩ : syracuseStep 188777 = 141583) B141583
theorem B746009 : Blo 115785 746009 := bstep (se 2 (by rfl) ⟨279753, by rfl⟩ : syracuseStep 746009 = 559507) B559507
theorem B221753 : Blo 115785 221753 := bstep (se 2 (by rfl) ⟨83157, by rfl⟩ : syracuseStep 221753 = 166315) B166315
theorem B320215 : Blo 115785 320215 := bstep (se 1 (by rfl) ⟨240161, by rfl⟩ : syracuseStep 320215 = 480323) B480323
theorem B222095 : Blo 115785 222095 := bstep (se 1 (by rfl) ⟨166571, by rfl⟩ : syracuseStep 222095 = 333143) B333143
theorem B418823 : Blo 115785 418823 := bstep (se 1 (by rfl) ⟨314117, by rfl⟩ : syracuseStep 418823 = 628235) B628235
theorem B254983 : Blo 115785 254983 := bstep (se 1 (by rfl) ⟨191237, by rfl⟩ : syracuseStep 254983 = 382475) B382475
theorem B484733 : Blo 115785 484733 := bstep (se 3 (by rfl) ⟨90887, by rfl⟩ : syracuseStep 484733 = 181775) B181775
theorem B1533329 : Blo 115785 1533329 := bstep (se 2 (by rfl) ⟨574998, by rfl⟩ : syracuseStep 1533329 = 1149997) B1149997
theorem B5432741 : Blo 115785 5432741 := bstep (se 4 (by rfl) ⟨509319, by rfl⟩ : syracuseStep 5432741 = 1018639) B1018639
theorem B1009097 : Blo 115785 1009097 := bstep (se 2 (by rfl) ⟨378411, by rfl⟩ : syracuseStep 1009097 = 756823) B756823
theorem B223163 : Blo 115785 223163 := bstep (se 1 (by rfl) ⟨167372, by rfl⟩ : syracuseStep 223163 = 334745) B334745
theorem B157945 : Blo 115785 157945 := bstep (se 2 (by rfl) ⟨59229, by rfl⟩ : syracuseStep 157945 = 118459) B118459
theorem B1599745 : Blo 115785 1599745 := bstep (se 2 (by rfl) ⟨599904, by rfl⟩ : syracuseStep 1599745 = 1199809) B1199809
theorem B223955 : Blo 115785 223955 := bstep (se 1 (by rfl) ⟨167966, by rfl⟩ : syracuseStep 223955 = 335933) B335933
theorem B224183 : Blo 115785 224183 := bstep (se 1 (by rfl) ⟨168137, by rfl⟩ : syracuseStep 224183 = 336275) B336275
theorem B453559 : Blo 115785 453559 := bstep (se 1 (by rfl) ⟨340169, by rfl⟩ : syracuseStep 453559 = 680339) B680339
theorem B879659 : Blo 115785 879659 := bstep (se 1 (by rfl) ⟨659744, by rfl⟩ : syracuseStep 879659 = 1319489) B1319489
theorem B454031 : Blo 115785 454031 := bstep (se 1 (by rfl) ⟨340523, by rfl⟩ : syracuseStep 454031 = 681047) B681047
theorem B225337 : Blo 115785 225337 := bstep (se 2 (by rfl) ⟨84501, by rfl⟩ : syracuseStep 225337 = 169003) B169003
theorem B225641 : Blo 115785 225641 := bstep (se 2 (by rfl) ⟨84615, by rfl⟩ : syracuseStep 225641 = 169231) B169231
theorem B225679 : Blo 115785 225679 := bstep (se 1 (by rfl) ⟨169259, by rfl⟩ : syracuseStep 225679 = 338519) B338519
theorem B258889 : Blo 115785 258889 := bstep (se 2 (by rfl) ⟨97083, by rfl⟩ : syracuseStep 258889 = 194167) B194167
theorem B848717 : Blo 115785 848717 := bstep (se 3 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 848717 = 318269) B318269
theorem B914323 : Blo 115785 914323 := bstep (se 1 (by rfl) ⟨685742, by rfl⟩ : syracuseStep 914323 = 1371485) B1371485
theorem B1635329 : Blo 115785 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B325129 : Blo 115785 325129 := bstep (se 2 (by rfl) ⟨121923, by rfl⟩ : syracuseStep 325129 = 243847) B243847
theorem B194087 : Blo 115785 194087 := bstep (se 1 (by rfl) ⟨145565, by rfl⟩ : syracuseStep 194087 = 291131) B291131
theorem B587411 : Blo 115785 587411 := bstep (se 1 (by rfl) ⟨440558, by rfl⟩ : syracuseStep 587411 = 881117) B881117
theorem B390905 : Blo 115785 390905 := bstep (se 2 (by rfl) ⟨146589, by rfl⟩ : syracuseStep 390905 = 293179) B293179
theorem B1275841 : Blo 115785 1275841 := bstep (se 2 (by rfl) ⟨478440, by rfl⟩ : syracuseStep 1275841 = 956881) B956881
theorem B391175 : Blo 115785 391175 := bstep (se 1 (by rfl) ⟨293381, by rfl⟩ : syracuseStep 391175 = 586763) B586763
theorem B391283 : Blo 115785 391283 := bstep (se 1 (by rfl) ⟨293462, by rfl⟩ : syracuseStep 391283 = 586925) B586925
theorem B391553 : Blo 115785 391553 := bstep (se 2 (by rfl) ⟨146832, by rfl⟩ : syracuseStep 391553 = 293665) B293665
theorem B4487723 : Blo 115785 4487723 := bstep (se 1 (by rfl) ⟨3365792, by rfl⟩ : syracuseStep 4487723 = 6731585) B6731585
theorem B4094509 : Blo 115785 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B260819 : Blo 115785 260819 := bstep (se 1 (by rfl) ⟨195614, by rfl⟩ : syracuseStep 260819 = 391229) B391229
theorem B293807 : Blo 115785 293807 := bstep (se 1 (by rfl) ⟨220355, by rfl⟩ : syracuseStep 293807 = 440711) B440711
theorem B195547 : Blo 115785 195547 := bstep (se 1 (by rfl) ⟨146660, by rfl⟩ : syracuseStep 195547 = 293321) B293321
theorem B6454333 : Blo 115785 6454333 := bstep (se 3 (by rfl) ⟨1210187, by rfl⟩ : syracuseStep 6454333 = 2420375) B2420375
theorem B392363 : Blo 115785 392363 := bstep (se 1 (by rfl) ⟨294272, by rfl⟩ : syracuseStep 392363 = 588545) B588545
theorem B7044569 : Blo 115785 7044569 := bstep (se 2 (by rfl) ⟨2641713, by rfl⟩ : syracuseStep 7044569 = 5283427) B5283427
theorem B294425 : Blo 115785 294425 := bstep (se 2 (by rfl) ⟨110409, by rfl⟩ : syracuseStep 294425 = 220819) B220819
theorem B130639 : Blo 115785 130639 := bstep (se 1 (by rfl) ⟨97979, by rfl⟩ : syracuseStep 130639 = 195959) B195959
theorem B196175 : Blo 115785 196175 := bstep (se 1 (by rfl) ⟨147131, by rfl⟩ : syracuseStep 196175 = 294263) B294263
theorem B425569 : Blo 115785 425569 := bstep (se 2 (by rfl) ⟨159588, by rfl⟩ : syracuseStep 425569 = 319177) B319177
theorem B261755 : Blo 115785 261755 := bstep (se 1 (by rfl) ⟨196316, by rfl⟩ : syracuseStep 261755 = 392633) B392633
theorem B392903 : Blo 115785 392903 := bstep (se 1 (by rfl) ⟨294677, by rfl⟩ : syracuseStep 392903 = 589355) B589355
theorem B261881 : Blo 115785 261881 := bstep (se 2 (by rfl) ⟨98205, by rfl⟩ : syracuseStep 261881 = 196411) B196411
theorem B425915 : Blo 115785 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B131035 : Blo 115785 131035 := bstep (se 1 (by rfl) ⟨98276, by rfl⟩ : syracuseStep 131035 = 196553) B196553
theorem B1048627 : Blo 115785 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B295123 : Blo 115785 295123 := bstep (se 1 (by rfl) ⟨221342, by rfl⟩ : syracuseStep 295123 = 442685) B442685
theorem B131359 : Blo 115785 131359 := bstep (se 1 (by rfl) ⟨98519, by rfl⟩ : syracuseStep 131359 = 197039) B197039
theorem B262511 : Blo 115785 262511 := bstep (se 1 (by rfl) ⟨196883, by rfl⟩ : syracuseStep 262511 = 393767) B393767
theorem B262583 : Blo 115785 262583 := bstep (se 1 (by rfl) ⟨196937, by rfl⟩ : syracuseStep 262583 = 393875) B393875
theorem B16417241 : Blo 115785 16417241 := bstep (se 2 (by rfl) ⟨6156465, by rfl⟩ : syracuseStep 16417241 = 12312931) B12312931
theorem B131647 : Blo 115785 131647 := bstep (se 1 (by rfl) ⟨98735, by rfl⟩ : syracuseStep 131647 = 197471) B197471
theorem B262727 : Blo 115785 262727 := bstep (se 1 (by rfl) ⟨197045, by rfl⟩ : syracuseStep 262727 = 394091) B394091
theorem B262763 : Blo 115785 262763 := bstep (se 1 (by rfl) ⟨197072, by rfl⟩ : syracuseStep 262763 = 394145) B394145
theorem B1278611 : Blo 115785 1278611 := bstep (se 1 (by rfl) ⟨958958, by rfl⟩ : syracuseStep 1278611 = 1917917) B1917917
theorem B590489 : Blo 115785 590489 := bstep (se 2 (by rfl) ⟨221433, by rfl⟩ : syracuseStep 590489 = 442867) B442867
theorem B426953 : Blo 115785 426953 := bstep (se 2 (by rfl) ⟨160107, by rfl⟩ : syracuseStep 426953 = 320215) B320215
theorem B2884571 : Blo 115785 2884571 := bstep (se 1 (by rfl) ⟨2163428, by rfl⟩ : syracuseStep 2884571 = 4326857) B4326857
theorem B263159 : Blo 115785 263159 := bstep (se 1 (by rfl) ⟨197369, by rfl⟩ : syracuseStep 263159 = 394739) B394739
theorem B296075 : Blo 115785 296075 := bstep (se 1 (by rfl) ⟨222056, by rfl⟩ : syracuseStep 296075 = 444113) B444113
theorem B132391 : Blo 115785 132391 := bstep (se 1 (by rfl) ⟨99293, by rfl⟩ : syracuseStep 132391 = 198587) B198587
theorem B263519 : Blo 115785 263519 := bstep (se 1 (by rfl) ⟨197639, by rfl⟩ : syracuseStep 263519 = 395279) B395279
theorem B1017197 : Blo 115785 1017197 := bstep (se 3 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 1017197 = 381449) B381449
theorem B198011 : Blo 115785 198011 := bstep (se 1 (by rfl) ⟨148508, by rfl⟩ : syracuseStep 198011 = 297017) B297017
theorem B132475 : Blo 115785 132475 := bstep (se 1 (by rfl) ⟨99356, by rfl⟩ : syracuseStep 132475 = 198713) B198713
theorem B394685 : Blo 115785 394685 := bstep (se 3 (by rfl) ⟨74003, by rfl⟩ : syracuseStep 394685 = 148007) B148007
theorem B296531 : Blo 115785 296531 := bstep (se 1 (by rfl) ⟨222398, by rfl⟩ : syracuseStep 296531 = 444797) B444797
theorem B755335 : Blo 115785 755335 := bstep (se 1 (by rfl) ⟨566501, by rfl⟩ : syracuseStep 755335 = 1133003) B1133003
theorem B263915 : Blo 115785 263915 := bstep (se 1 (by rfl) ⟨197936, by rfl⟩ : syracuseStep 263915 = 395873) B395873
theorem B395063 : Blo 115785 395063 := bstep (se 1 (by rfl) ⟨296297, by rfl⟩ : syracuseStep 395063 = 592595) B592595
theorem B132943 : Blo 115785 132943 := bstep (se 1 (by rfl) ⟨99707, by rfl⟩ : syracuseStep 132943 = 199415) B199415
theorem B264041 : Blo 115785 264041 := bstep (se 2 (by rfl) ⟨99015, by rfl⟩ : syracuseStep 264041 = 198031) B198031
theorem B1410949 : Blo 115785 1410949 := bstep (se 4 (by rfl) ⟨132276, by rfl⟩ : syracuseStep 1410949 = 264553) B264553
theorem B1476559 : Blo 115785 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B133339 : Blo 115785 133339 := bstep (se 1 (by rfl) ⟨100004, by rfl⟩ : syracuseStep 133339 = 200009) B200009
theorem B395549 : Blo 115785 395549 := bstep (se 3 (by rfl) ⟨74165, by rfl⟩ : syracuseStep 395549 = 148331) B148331
theorem B199003 : Blo 115785 199003 := bstep (se 1 (by rfl) ⟨149252, by rfl⟩ : syracuseStep 199003 = 298505) B298505
theorem B592271 : Blo 115785 592271 := bstep (se 1 (by rfl) ⟨444203, by rfl⟩ : syracuseStep 592271 = 888407) B888407
theorem B297391 : Blo 115785 297391 := bstep (se 1 (by rfl) ⟨223043, by rfl⟩ : syracuseStep 297391 = 446087) B446087
theorem B133627 : Blo 115785 133627 := bstep (se 1 (by rfl) ⟨100220, by rfl⟩ : syracuseStep 133627 = 200441) B200441
theorem B133807 : Blo 115785 133807 := bstep (se 1 (by rfl) ⟨100355, by rfl⟩ : syracuseStep 133807 = 200711) B200711
theorem B264887 : Blo 115785 264887 := bstep (se 1 (by rfl) ⟨198665, by rfl⟩ : syracuseStep 264887 = 397331) B397331
theorem B297695 : Blo 115785 297695 := bstep (se 1 (by rfl) ⟨223271, by rfl⟩ : syracuseStep 297695 = 446543) B446543
theorem B265103 : Blo 115785 265103 := bstep (se 1 (by rfl) ⟨198827, by rfl⟩ : syracuseStep 265103 = 397655) B397655
theorem B428971 : Blo 115785 428971 := bstep (se 1 (by rfl) ⟨321728, by rfl⟩ : syracuseStep 428971 = 643457) B643457
theorem B134095 : Blo 115785 134095 := bstep (se 1 (by rfl) ⟨100571, by rfl⟩ : syracuseStep 134095 = 201143) B201143
theorem B2132993 : Blo 115785 2132993 := bstep (se 2 (by rfl) ⟨799872, by rfl⟩ : syracuseStep 2132993 = 1599745) B1599745
theorem B494707 : Blo 115785 494707 := bstep (se 1 (by rfl) ⟨371030, by rfl⟩ : syracuseStep 494707 = 742061) B742061
theorem B330875 : Blo 115785 330875 := bstep (se 1 (by rfl) ⟨248156, by rfl⟩ : syracuseStep 330875 = 496313) B496313
theorem B396575 : Blo 115785 396575 := bstep (se 1 (by rfl) ⟨297431, by rfl⟩ : syracuseStep 396575 = 594863) B594863
theorem B199975 : Blo 115785 199975 := bstep (se 1 (by rfl) ⟨149981, by rfl⟩ : syracuseStep 199975 = 299963) B299963
theorem B134491 : Blo 115785 134491 := bstep (se 1 (by rfl) ⟨100868, by rfl⟩ : syracuseStep 134491 = 201737) B201737
theorem B298363 : Blo 115785 298363 := bstep (se 1 (by rfl) ⟨223772, by rfl⟩ : syracuseStep 298363 = 447545) B447545
theorem B134599 : Blo 115785 134599 := bstep (se 1 (by rfl) ⟨100949, by rfl⟩ : syracuseStep 134599 = 201899) B201899
theorem B265823 : Blo 115785 265823 := bstep (se 1 (by rfl) ⟨199367, by rfl⟩ : syracuseStep 265823 = 398735) B398735
theorem B396895 : Blo 115785 396895 := bstep (se 1 (by rfl) ⟨297671, by rfl⟩ : syracuseStep 396895 = 595343) B595343
theorem B298799 : Blo 115785 298799 := bstep (se 1 (by rfl) ⟨224099, by rfl⟩ : syracuseStep 298799 = 448199) B448199
theorem B200495 : Blo 115785 200495 := bstep (se 1 (by rfl) ⟨150371, by rfl⟩ : syracuseStep 200495 = 300743) B300743
theorem B266039 : Blo 115785 266039 := bstep (se 1 (by rfl) ⟨199529, by rfl⟩ : syracuseStep 266039 = 399059) B399059
theorem B266345 : Blo 115785 266345 := bstep (se 2 (by rfl) ⟨99879, by rfl⟩ : syracuseStep 266345 = 199759) B199759
theorem B299447 : Blo 115785 299447 := bstep (se 1 (by rfl) ⟨224585, by rfl⟩ : syracuseStep 299447 = 449171) B449171
theorem B594377 : Blo 115785 594377 := bstep (se 2 (by rfl) ⟨222891, by rfl⟩ : syracuseStep 594377 = 445783) B445783
theorem B266831 : Blo 115785 266831 := bstep (se 1 (by rfl) ⟨200123, by rfl⟩ : syracuseStep 266831 = 400247) B400247
theorem B856673 : Blo 115785 856673 := bstep (se 2 (by rfl) ⟨321252, by rfl⟩ : syracuseStep 856673 = 642505) B642505
theorem B332471 : Blo 115785 332471 := bstep (se 1 (by rfl) ⟨249353, by rfl⟩ : syracuseStep 332471 = 498707) B498707
theorem B398047 : Blo 115785 398047 := bstep (se 1 (by rfl) ⟨298535, by rfl⟩ : syracuseStep 398047 = 597071) B597071
theorem B266975 : Blo 115785 266975 := bstep (se 1 (by rfl) ⟨200231, by rfl⟩ : syracuseStep 266975 = 400463) B400463
theorem B267227 : Blo 115785 267227 := bstep (se 1 (by rfl) ⟨200420, by rfl⟩ : syracuseStep 267227 = 400841) B400841
theorem B201703 : Blo 115785 201703 := bstep (se 1 (by rfl) ⟨151277, by rfl⟩ : syracuseStep 201703 = 302555) B302555
theorem B267407 : Blo 115785 267407 := bstep (se 1 (by rfl) ⟨200555, by rfl⟩ : syracuseStep 267407 = 401111) B401111
theorem B267497 : Blo 115785 267497 := bstep (se 2 (by rfl) ⟨100311, by rfl⟩ : syracuseStep 267497 = 200623) B200623
theorem B595187 : Blo 115785 595187 := bstep (se 1 (by rfl) ⟨446390, by rfl⟩ : syracuseStep 595187 = 892781) B892781
theorem B267551 : Blo 115785 267551 := bstep (se 1 (by rfl) ⟨200663, by rfl⟩ : syracuseStep 267551 = 401327) B401327
theorem B300449 : Blo 115785 300449 := bstep (se 2 (by rfl) ⟨112668, by rfl⟩ : syracuseStep 300449 = 225337) B225337
theorem B2299427 : Blo 115785 2299427 := bstep (se 1 (by rfl) ⟨1724570, by rfl⟩ : syracuseStep 2299427 = 3449141) B3449141
theorem B399005 : Blo 115785 399005 := bstep (se 3 (by rfl) ⟨74813, by rfl⟩ : syracuseStep 399005 = 149627) B149627
theorem B497339 : Blo 115785 497339 := bstep (se 1 (by rfl) ⟨373004, by rfl⟩ : syracuseStep 497339 = 746009) B746009
theorem B268073 : Blo 115785 268073 := bstep (se 2 (by rfl) ⟨100527, by rfl⟩ : syracuseStep 268073 = 201055) B201055
theorem B300905 : Blo 115785 300905 := bstep (se 2 (by rfl) ⟨112839, by rfl⟩ : syracuseStep 300905 = 225679) B225679
theorem B399545 : Blo 115785 399545 := bstep (se 2 (by rfl) ⟨149829, by rfl⟩ : syracuseStep 399545 = 299659) B299659
theorem B1022219 : Blo 115785 1022219 := bstep (se 1 (by rfl) ⟨766664, by rfl⟩ : syracuseStep 1022219 = 1533329) B1533329
theorem B1841591 : Blo 115785 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B1219097 : Blo 115785 1219097 := bstep (se 2 (by rfl) ⟨457161, by rfl⟩ : syracuseStep 1219097 = 914323) B914323
theorem B989891 : Blo 115785 989891 := bstep (se 1 (by rfl) ⟨742418, by rfl⟩ : syracuseStep 989891 = 1484837) B1484837
theorem B269135 : Blo 115785 269135 := bstep (se 1 (by rfl) ⟨201851, by rfl⟩ : syracuseStep 269135 = 403703) B403703
theorem B269351 : Blo 115785 269351 := bstep (se 1 (by rfl) ⟨202013, by rfl⟩ : syracuseStep 269351 = 404027) B404027
theorem B597131 : Blo 115785 597131 := bstep (se 1 (by rfl) ⟨447848, by rfl⟩ : syracuseStep 597131 = 895697) B895697
theorem B433505 : Blo 115785 433505 := bstep (se 2 (by rfl) ⟨162564, by rfl⟩ : syracuseStep 433505 = 325129) B325129
theorem B499081 : Blo 115785 499081 := bstep (se 2 (by rfl) ⟨187155, by rfl⟩ : syracuseStep 499081 = 374311) B374311
theorem B859673 : Blo 115785 859673 := bstep (se 2 (by rfl) ⟨322377, by rfl⟩ : syracuseStep 859673 = 644755) B644755
theorem B302687 : Blo 115785 302687 := bstep (se 1 (by rfl) ⟨227015, by rfl⟩ : syracuseStep 302687 = 454031) B454031
theorem B401057 : Blo 115785 401057 := bstep (se 2 (by rfl) ⟨150396, by rfl⟩ : syracuseStep 401057 = 300793) B300793
theorem B663299 : Blo 115785 663299 := bstep (se 1 (by rfl) ⟨497474, by rfl⟩ : syracuseStep 663299 = 994949) B994949
theorem B2072753 : Blo 115785 2072753 := bstep (se 2 (by rfl) ⟨777282, by rfl⟩ : syracuseStep 2072753 = 1554565) B1554565
theorem B4301009 : Blo 115785 4301009 := bstep (se 2 (by rfl) ⟨1612878, by rfl⟩ : syracuseStep 4301009 = 3225757) B3225757
theorem B532993 : Blo 115785 532993 := bstep (se 2 (by rfl) ⟨199872, by rfl⟩ : syracuseStep 532993 = 399745) B399745
theorem B401921 : Blo 115785 401921 := bstep (se 2 (by rfl) ⟨150720, by rfl⟩ : syracuseStep 401921 = 301441) B301441
theorem B1122821 : Blo 115785 1122821 := bstep (se 4 (by rfl) ⟨105264, by rfl⟩ : syracuseStep 1122821 = 210529) B210529
theorem B565811 : Blo 115785 565811 := bstep (se 1 (by rfl) ⟨424358, by rfl⟩ : syracuseStep 565811 = 848717) B848717
theorem B5120657 : Blo 115785 5120657 := bstep (se 2 (by rfl) ⟨1920246, by rfl⟩ : syracuseStep 5120657 = 3840493) B3840493
theorem B1090219 : Blo 115785 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B598751 : Blo 115785 598751 := bstep (se 1 (by rfl) ⟨449063, by rfl⟩ : syracuseStep 598751 = 898127) B898127
theorem B402407 : Blo 115785 402407 := bstep (se 1 (by rfl) ⟨301805, by rfl⟩ : syracuseStep 402407 = 603611) B603611
theorem B402731 : Blo 115785 402731 := bstep (se 1 (by rfl) ⟨302048, by rfl⟩ : syracuseStep 402731 = 604097) B604097
theorem B403001 : Blo 115785 403001 := bstep (se 2 (by rfl) ⟨151125, by rfl⟩ : syracuseStep 403001 = 302251) B302251
theorem B2991815 : Blo 115785 2991815 := bstep (se 1 (by rfl) ⟨2243861, by rfl⟩ : syracuseStep 2991815 = 4487723) B4487723
theorem B173879 : Blo 115785 173879 := bstep (se 1 (by rfl) ⟨130409, by rfl⟩ : syracuseStep 173879 = 260819) B260819
theorem B5023781 : Blo 115785 5023781 := bstep (se 4 (by rfl) ⟨470979, by rfl⟩ : syracuseStep 5023781 = 941959) B941959
theorem B174185 : Blo 115785 174185 := bstep (se 2 (by rfl) ⟨65319, by rfl⟩ : syracuseStep 174185 = 130639) B130639
theorem B567425 : Blo 115785 567425 := bstep (se 2 (by rfl) ⟨212784, by rfl⟩ : syracuseStep 567425 = 425569) B425569
theorem B1255601 : Blo 115785 1255601 := bstep (se 2 (by rfl) ⟨470850, by rfl⟩ : syracuseStep 1255601 = 941701) B941701
theorem B4696379 : Blo 115785 4696379 := bstep (se 1 (by rfl) ⟨3522284, by rfl⟩ : syracuseStep 4696379 = 7044569) B7044569
theorem B174503 : Blo 115785 174503 := bstep (se 1 (by rfl) ⟨130877, by rfl⟩ : syracuseStep 174503 = 261755) B261755
theorem B240097 : Blo 115785 240097 := bstep (se 2 (by rfl) ⟨90036, by rfl⟩ : syracuseStep 240097 = 180073) B180073
theorem B174587 : Blo 115785 174587 := bstep (se 1 (by rfl) ⟨130940, by rfl⟩ : syracuseStep 174587 = 261881) B261881
theorem B174713 : Blo 115785 174713 := bstep (se 2 (by rfl) ⟨65517, by rfl⟩ : syracuseStep 174713 = 131035) B131035
theorem B174767 : Blo 115785 174767 := bstep (se 1 (by rfl) ⟨131075, by rfl⟩ : syracuseStep 174767 = 262151) B262151
theorem B174815 : Blo 115785 174815 := bstep (se 1 (by rfl) ⟨131111, by rfl⟩ : syracuseStep 174815 = 262223) B262223
theorem B404243 : Blo 115785 404243 := bstep (se 1 (by rfl) ⟨303182, by rfl⟩ : syracuseStep 404243 = 606365) B606365
theorem B601019 : Blo 115785 601019 := bstep (se 1 (by rfl) ⟨450764, by rfl⟩ : syracuseStep 601019 = 901529) B901529
theorem B175079 : Blo 115785 175079 := bstep (se 1 (by rfl) ⟨131309, by rfl⟩ : syracuseStep 175079 = 262619) B262619
theorem B306163 : Blo 115785 306163 := bstep (se 1 (by rfl) ⟨229622, by rfl⟩ : syracuseStep 306163 = 459245) B459245
theorem B1485863 : Blo 115785 1485863 := bstep (se 1 (by rfl) ⟨1114397, by rfl⟩ : syracuseStep 1485863 = 2228795) B2228795
theorem B175337 : Blo 115785 175337 := bstep (se 2 (by rfl) ⟨65751, by rfl⟩ : syracuseStep 175337 = 131503) B131503
theorem B175391 : Blo 115785 175391 := bstep (se 1 (by rfl) ⟨131543, by rfl⟩ : syracuseStep 175391 = 263087) B263087
theorem B175559 : Blo 115785 175559 := bstep (se 1 (by rfl) ⟨131669, by rfl⟩ : syracuseStep 175559 = 263339) B263339
theorem B634463 : Blo 115785 634463 := bstep (se 1 (by rfl) ⟨475847, by rfl⟩ : syracuseStep 634463 = 951695) B951695
theorem B503405 : Blo 115785 503405 := bstep (se 3 (by rfl) ⟨94388, by rfl⟩ : syracuseStep 503405 = 188777) B188777
theorem B1224355 : Blo 115785 1224355 := bstep (se 1 (by rfl) ⟨918266, by rfl⟩ : syracuseStep 1224355 = 1836533) B1836533
theorem B569099 : Blo 115785 569099 := bstep (se 1 (by rfl) ⟨426824, by rfl⟩ : syracuseStep 569099 = 853649) B853649
theorem B175913 : Blo 115785 175913 := bstep (se 2 (by rfl) ⟨65967, by rfl⟩ : syracuseStep 175913 = 131935) B131935
theorem B175919 : Blo 115785 175919 := bstep (se 1 (by rfl) ⟨131939, by rfl⟩ : syracuseStep 175919 = 263879) B263879
theorem B3092411 : Blo 115785 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B339977 : Blo 115785 339977 := bstep (se 2 (by rfl) ⟨127491, by rfl⟩ : syracuseStep 339977 = 254983) B254983
theorem B667673 : Blo 115785 667673 := bstep (se 2 (by rfl) ⟨250377, by rfl⟩ : syracuseStep 667673 = 500755) B500755
theorem B602315 : Blo 115785 602315 := bstep (se 1 (by rfl) ⟨451736, by rfl⟩ : syracuseStep 602315 = 903473) B903473
theorem B864515 : Blo 115785 864515 := bstep (se 1 (by rfl) ⟨648386, by rfl⟩ : syracuseStep 864515 = 1296773) B1296773
theorem B176393 : Blo 115785 176393 := bstep (se 2 (by rfl) ⟨66147, by rfl⟩ : syracuseStep 176393 = 132295) B132295
theorem B176495 : Blo 115785 176495 := bstep (se 1 (by rfl) ⟨132371, by rfl⟩ : syracuseStep 176495 = 264743) B264743
theorem B176711 : Blo 115785 176711 := bstep (se 1 (by rfl) ⟨132533, by rfl⟩ : syracuseStep 176711 = 265067) B265067
theorem B176747 : Blo 115785 176747 := bstep (se 1 (by rfl) ⟨132560, by rfl⟩ : syracuseStep 176747 = 265121) B265121
theorem B176975 : Blo 115785 176975 := bstep (se 1 (by rfl) ⟨132731, by rfl⟩ : syracuseStep 176975 = 265463) B265463
theorem B504737 : Blo 115785 504737 := bstep (se 2 (by rfl) ⟨189276, by rfl⟩ : syracuseStep 504737 = 378553) B378553
theorem B635849 : Blo 115785 635849 := bstep (se 2 (by rfl) ⟨238443, by rfl⟩ : syracuseStep 635849 = 476887) B476887
theorem B177371 : Blo 115785 177371 := bstep (se 1 (by rfl) ⟨133028, by rfl⟩ : syracuseStep 177371 = 266057) B266057
theorem B177545 : Blo 115785 177545 := bstep (se 2 (by rfl) ⟨66579, by rfl⟩ : syracuseStep 177545 = 133159) B133159
theorem B210593 : Blo 115785 210593 := bstep (se 2 (by rfl) ⟨78972, by rfl⟩ : syracuseStep 210593 = 157945) B157945
theorem B276155 : Blo 115785 276155 := bstep (se 1 (by rfl) ⟨207116, by rfl⟩ : syracuseStep 276155 = 414233) B414233
theorem B177899 : Blo 115785 177899 := bstep (se 1 (by rfl) ⟨133424, by rfl⟩ : syracuseStep 177899 = 266849) B266849
theorem B178127 : Blo 115785 178127 := bstep (se 1 (by rfl) ⟨133595, by rfl⟩ : syracuseStep 178127 = 267191) B267191
theorem B178523 : Blo 115785 178523 := bstep (se 1 (by rfl) ⟨133892, by rfl⟩ : syracuseStep 178523 = 267785) B267785
theorem B604583 : Blo 115785 604583 := bstep (se 1 (by rfl) ⟨453437, by rfl⟩ : syracuseStep 604583 = 906875) B906875
theorem B178751 : Blo 115785 178751 := bstep (se 1 (by rfl) ⟨134063, by rfl⟩ : syracuseStep 178751 = 268127) B268127
theorem B604745 : Blo 115785 604745 := bstep (se 2 (by rfl) ⟨226779, by rfl⟩ : syracuseStep 604745 = 453559) B453559
theorem B670315 : Blo 115785 670315 := bstep (se 1 (by rfl) ⟨502736, by rfl⟩ : syracuseStep 670315 = 1005473) B1005473
theorem B211631 : Blo 115785 211631 := bstep (se 1 (by rfl) ⟨158723, by rfl⟩ : syracuseStep 211631 = 317447) B317447
theorem B178871 : Blo 115785 178871 := bstep (se 1 (by rfl) ⟨134153, by rfl⟩ : syracuseStep 178871 = 268307) B268307
theorem B179099 : Blo 115785 179099 := bstep (se 1 (by rfl) ⟨134324, by rfl⟩ : syracuseStep 179099 = 268649) B268649
theorem B605099 : Blo 115785 605099 := bstep (se 1 (by rfl) ⟨453824, by rfl⟩ : syracuseStep 605099 = 907649) B907649
theorem B539635 : Blo 115785 539635 := bstep (se 1 (by rfl) ⟨404726, by rfl⟩ : syracuseStep 539635 = 809453) B809453
theorem B179495 : Blo 115785 179495 := bstep (se 1 (by rfl) ⟨134621, by rfl⟩ : syracuseStep 179495 = 269243) B269243
theorem B179579 : Blo 115785 179579 := bstep (se 1 (by rfl) ⟨134684, by rfl⟩ : syracuseStep 179579 = 269369) B269369
theorem B442169 : Blo 115785 442169 := bstep (se 2 (by rfl) ⟨165813, by rfl⟩ : syracuseStep 442169 = 331627) B331627
theorem B147835 : Blo 115785 147835 := bstep (se 1 (by rfl) ⟨110876, by rfl⟩ : syracuseStep 147835 = 221753) B221753
theorem B541129 : Blo 115785 541129 := bstep (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) B405847
theorem B803297 : Blo 115785 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B148063 : Blo 115785 148063 := bstep (se 1 (by rfl) ⟨111047, by rfl⟩ : syracuseStep 148063 = 222095) B222095
theorem B279215 : Blo 115785 279215 := bstep (se 1 (by rfl) ⟨209411, by rfl⟩ : syracuseStep 279215 = 418823) B418823
theorem B508751 : Blo 115785 508751 := bstep (se 1 (by rfl) ⟨381563, by rfl⟩ : syracuseStep 508751 = 763127) B763127
theorem B3621827 : Blo 115785 3621827 := bstep (se 1 (by rfl) ⟨2716370, by rfl⟩ : syracuseStep 3621827 = 5432741) B5432741
theorem B672731 : Blo 115785 672731 := bstep (se 1 (by rfl) ⟨504548, by rfl⟩ : syracuseStep 672731 = 1009097) B1009097
theorem B345185 : Blo 115785 345185 := bstep (se 2 (by rfl) ⟨129444, by rfl⟩ : syracuseStep 345185 = 258889) B258889
theorem B509161 : Blo 115785 509161 := bstep (se 2 (by rfl) ⟨190935, by rfl⟩ : syracuseStep 509161 = 381871) B381871
theorem B115999 : Blo 115785 115999 := bstep (se 1 (by rfl) ⟨86999, by rfl⟩ : syracuseStep 115999 = 173999) B173999
theorem B148775 : Blo 115785 148775 := bstep (se 1 (by rfl) ⟨111581, by rfl⟩ : syracuseStep 148775 = 223163) B223163
theorem B116059 : Blo 115785 116059 := bstep (se 1 (by rfl) ⟨87044, by rfl⟩ : syracuseStep 116059 = 174089) B174089
theorem B116079 : Blo 115785 116079 := bstep (se 1 (by rfl) ⟨87059, by rfl⟩ : syracuseStep 116079 = 174119) B174119
theorem B116135 : Blo 115785 116135 := bstep (se 1 (by rfl) ⟨87101, by rfl⟩ : syracuseStep 116135 = 174203) B174203
theorem B116219 : Blo 115785 116219 := bstep (se 1 (by rfl) ⟨87164, by rfl⟩ : syracuseStep 116219 = 174329) B174329
theorem B116287 : Blo 115785 116287 := bstep (se 1 (by rfl) ⟨87215, by rfl⟩ : syracuseStep 116287 = 174431) B174431
theorem B116295 : Blo 115785 116295 := bstep (se 1 (by rfl) ⟨87221, by rfl⟩ : syracuseStep 116295 = 174443) B174443
theorem B116447 : Blo 115785 116447 := bstep (se 1 (by rfl) ⟨87335, by rfl⟩ : syracuseStep 116447 = 174671) B174671
theorem B116527 : Blo 115785 116527 := bstep (se 1 (by rfl) ⟨87395, by rfl⟩ : syracuseStep 116527 = 174791) B174791
theorem B149303 : Blo 115785 149303 := bstep (se 1 (by rfl) ⟨111977, by rfl⟩ : syracuseStep 149303 = 223955) B223955
theorem B509777 : Blo 115785 509777 := bstep (se 2 (by rfl) ⟨191166, by rfl⟩ : syracuseStep 509777 = 382333) B382333
theorem B116635 : Blo 115785 116635 := bstep (se 1 (by rfl) ⟨87476, by rfl⟩ : syracuseStep 116635 = 174953) B174953
theorem B116687 : Blo 115785 116687 := bstep (se 1 (by rfl) ⟨87515, by rfl⟩ : syracuseStep 116687 = 175031) B175031
theorem B149455 : Blo 115785 149455 := bstep (se 1 (by rfl) ⟨112091, by rfl⟩ : syracuseStep 149455 = 224183) B224183
theorem B116711 : Blo 115785 116711 := bstep (se 1 (by rfl) ⟨87533, by rfl⟩ : syracuseStep 116711 = 175067) B175067
theorem B117023 : Blo 115785 117023 := bstep (se 1 (by rfl) ⟨87767, by rfl⟩ : syracuseStep 117023 = 175535) B175535
theorem B117083 : Blo 115785 117083 := bstep (se 1 (by rfl) ⟨87812, by rfl⟩ : syracuseStep 117083 = 175625) B175625
theorem B117103 : Blo 115785 117103 := bstep (se 1 (by rfl) ⟨87827, by rfl⟩ : syracuseStep 117103 = 175655) B175655
theorem B117159 : Blo 115785 117159 := bstep (se 1 (by rfl) ⟨87869, by rfl⟩ : syracuseStep 117159 = 175739) B175739
theorem B510391 : Blo 115785 510391 := bstep (se 1 (by rfl) ⟨382793, by rfl⟩ : syracuseStep 510391 = 765587) B765587
theorem B117243 : Blo 115785 117243 := bstep (se 1 (by rfl) ⟨87932, by rfl⟩ : syracuseStep 117243 = 175865) B175865
theorem B117311 : Blo 115785 117311 := bstep (se 1 (by rfl) ⟨87983, by rfl⟩ : syracuseStep 117311 = 175967) B175967
theorem B117319 : Blo 115785 117319 := bstep (se 1 (by rfl) ⟨87989, by rfl⟩ : syracuseStep 117319 = 175979) B175979
theorem B117471 : Blo 115785 117471 := bstep (se 1 (by rfl) ⟨88103, by rfl⟩ : syracuseStep 117471 = 176207) B176207
theorem B379667 : Blo 115785 379667 := bstep (se 1 (by rfl) ⟨284750, by rfl⟩ : syracuseStep 379667 = 569501) B569501
theorem B903959 : Blo 115785 903959 := bstep (se 1 (by rfl) ⟨677969, by rfl⟩ : syracuseStep 903959 = 1355939) B1355939
theorem B117551 : Blo 115785 117551 := bstep (se 1 (by rfl) ⟨88163, by rfl⟩ : syracuseStep 117551 = 176327) B176327
theorem B117659 : Blo 115785 117659 := bstep (se 1 (by rfl) ⟨88244, by rfl⟩ : syracuseStep 117659 = 176489) B176489
theorem B150427 : Blo 115785 150427 := bstep (se 1 (by rfl) ⟨112820, by rfl⟩ : syracuseStep 150427 = 225641) B225641
theorem B117711 : Blo 115785 117711 := bstep (se 1 (by rfl) ⟨88283, by rfl⟩ : syracuseStep 117711 = 176567) B176567
theorem B117735 : Blo 115785 117735 := bstep (se 1 (by rfl) ⟨88301, by rfl⟩ : syracuseStep 117735 = 176603) B176603
theorem B118047 : Blo 115785 118047 := bstep (se 1 (by rfl) ⟨88535, by rfl⟩ : syracuseStep 118047 = 177071) B177071
theorem B118107 : Blo 115785 118107 := bstep (se 1 (by rfl) ⟨88580, by rfl⟩ : syracuseStep 118107 = 177161) B177161
theorem B118127 : Blo 115785 118127 := bstep (se 1 (by rfl) ⟨88595, by rfl⟩ : syracuseStep 118127 = 177191) B177191
theorem B5459345 : Blo 115785 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B118183 : Blo 115785 118183 := bstep (se 1 (by rfl) ⟨88637, by rfl⟩ : syracuseStep 118183 = 177275) B177275
theorem B118267 : Blo 115785 118267 := bstep (se 1 (by rfl) ⟨88700, by rfl⟩ : syracuseStep 118267 = 177401) B177401
theorem B1429001 : Blo 115785 1429001 := bstep (se 2 (by rfl) ⟨535875, by rfl⟩ : syracuseStep 1429001 = 1071751) B1071751
theorem B118335 : Blo 115785 118335 := bstep (se 1 (by rfl) ⟨88751, by rfl⟩ : syracuseStep 118335 = 177503) B177503
theorem B118343 : Blo 115785 118343 := bstep (se 1 (by rfl) ⟨88757, by rfl⟩ : syracuseStep 118343 = 177515) B177515
theorem B118495 : Blo 115785 118495 := bstep (se 1 (by rfl) ⟨88871, by rfl⟩ : syracuseStep 118495 = 177743) B177743
theorem B446255 : Blo 115785 446255 := bstep (se 1 (by rfl) ⟨334691, by rfl⟩ : syracuseStep 446255 = 669383) B669383
theorem B118575 : Blo 115785 118575 := bstep (se 1 (by rfl) ⟨88931, by rfl⟩ : syracuseStep 118575 = 177863) B177863
theorem B446269 : Blo 115785 446269 := bstep (se 3 (by rfl) ⟨83675, by rfl⟩ : syracuseStep 446269 = 167351) B167351
theorem B1003373 : Blo 115785 1003373 := bstep (se 3 (by rfl) ⟨188132, by rfl⟩ : syracuseStep 1003373 = 376265) B376265
theorem B118683 : Blo 115785 118683 := bstep (se 1 (by rfl) ⟨89012, by rfl⟩ : syracuseStep 118683 = 178025) B178025
theorem B118735 : Blo 115785 118735 := bstep (se 1 (by rfl) ⟨89051, by rfl⟩ : syracuseStep 118735 = 178103) B178103
theorem B118759 : Blo 115785 118759 := bstep (se 1 (by rfl) ⟨89069, by rfl⟩ : syracuseStep 118759 = 178139) B178139
theorem B8605777 : Blo 115785 8605777 := bstep (se 2 (by rfl) ⟨3227166, by rfl⟩ : syracuseStep 8605777 = 6454333) B6454333
theorem B971023 : Blo 115785 971023 := bstep (se 1 (by rfl) ⟨728267, by rfl⟩ : syracuseStep 971023 = 1456535) B1456535
theorem B119071 : Blo 115785 119071 := bstep (se 1 (by rfl) ⟨89303, by rfl⟩ : syracuseStep 119071 = 178607) B178607
theorem B381257 : Blo 115785 381257 := bstep (se 2 (by rfl) ⟨142971, by rfl⟩ : syracuseStep 381257 = 285943) B285943
theorem B119131 : Blo 115785 119131 := bstep (se 1 (by rfl) ⟨89348, by rfl⟩ : syracuseStep 119131 = 178697) B178697
theorem B119151 : Blo 115785 119151 := bstep (se 1 (by rfl) ⟨89363, by rfl⟩ : syracuseStep 119151 = 178727) B178727
theorem B119207 : Blo 115785 119207 := bstep (se 1 (by rfl) ⟨89405, by rfl⟩ : syracuseStep 119207 = 178811) B178811
theorem B119291 : Blo 115785 119291 := bstep (se 1 (by rfl) ⟨89468, by rfl⟩ : syracuseStep 119291 = 178937) B178937
theorem B119359 : Blo 115785 119359 := bstep (se 1 (by rfl) ⟨89519, by rfl⟩ : syracuseStep 119359 = 179039) B179039
theorem B119367 : Blo 115785 119367 := bstep (se 1 (by rfl) ⟨89525, by rfl⟩ : syracuseStep 119367 = 179051) B179051
theorem B119519 : Blo 115785 119519 := bstep (se 1 (by rfl) ⟨89639, by rfl⟩ : syracuseStep 119519 = 179279) B179279
theorem B119599 : Blo 115785 119599 := bstep (se 1 (by rfl) ⟨89699, by rfl⟩ : syracuseStep 119599 = 179399) B179399
theorem B840527 : Blo 115785 840527 := bstep (se 1 (by rfl) ⟨630395, by rfl⟩ : syracuseStep 840527 = 1260791) B1260791
theorem B119707 : Blo 115785 119707 := bstep (se 1 (by rfl) ⟨89780, by rfl⟩ : syracuseStep 119707 = 179561) B179561
theorem B119759 : Blo 115785 119759 := bstep (se 1 (by rfl) ⟨89819, by rfl⟩ : syracuseStep 119759 = 179639) B179639
theorem B119783 : Blo 115785 119783 := bstep (se 1 (by rfl) ⟨89837, by rfl⟩ : syracuseStep 119783 = 179675) B179675
theorem B251113 : Blo 115785 251113 := bstep (se 2 (by rfl) ⟨94167, by rfl⟩ : syracuseStep 251113 = 188335) B188335
theorem B283943 : Blo 115785 283943 := bstep (se 1 (by rfl) ⟨212957, by rfl⟩ : syracuseStep 283943 = 425915) B425915
theorem B1955393 : Blo 115785 1955393 := bstep (se 2 (by rfl) ⟨733272, by rfl⟩ : syracuseStep 1955393 = 1466545) B1466545
theorem B481231 : Blo 115785 481231 := bstep (se 1 (by rfl) ⟨360923, by rfl⟩ : syracuseStep 481231 = 721847) B721847
theorem B481261 : Blo 115785 481261 := bstep (se 3 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 481261 = 180473) B180473
theorem B220151 : Blo 115785 220151 := bstep (se 1 (by rfl) ⟨165113, by rfl⟩ : syracuseStep 220151 = 330227) B330227
theorem B187771 : Blo 115785 187771 := bstep (se 1 (by rfl) ⟨140828, by rfl⟩ : syracuseStep 187771 = 281657) B281657
theorem B220553 : Blo 115785 220553 := bstep (se 2 (by rfl) ⟨82707, by rfl⟩ : syracuseStep 220553 = 165415) B165415
theorem B744983 : Blo 115785 744983 := bstep (se 1 (by rfl) ⟨558737, by rfl⟩ : syracuseStep 744983 = 1117475) B1117475
theorem B1990169 : Blo 115785 1990169 := bstep (se 2 (by rfl) ⟨746313, by rfl⟩ : syracuseStep 1990169 = 1492627) B1492627
theorem B450143 : Blo 115785 450143 := bstep (se 1 (by rfl) ⟨337607, by rfl⟩ : syracuseStep 450143 = 675215) B675215
theorem B450157 : Blo 115785 450157 := bstep (se 3 (by rfl) ⟨84404, by rfl⟩ : syracuseStep 450157 = 168809) B168809
theorem B450461 : Blo 115785 450461 := bstep (se 3 (by rfl) ⟨84461, by rfl⟩ : syracuseStep 450461 = 168923) B168923
theorem B1138697 : Blo 115785 1138697 := bstep (se 2 (by rfl) ⟨427011, by rfl⟩ : syracuseStep 1138697 = 854023) B854023
theorem B221449 : Blo 115785 221449 := bstep (se 2 (by rfl) ⟨83043, by rfl⟩ : syracuseStep 221449 = 166087) B166087
theorem B189001 : Blo 115785 189001 := bstep (se 2 (by rfl) ⟨70875, by rfl⟩ : syracuseStep 189001 = 141751) B141751
theorem B517565 : Blo 115785 517565 := bstep (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) B194087
theorem B222907 : Blo 115785 222907 := bstep (se 1 (by rfl) ⟨167180, by rfl⟩ : syracuseStep 222907 = 334361) B334361
theorem B2025161 : Blo 115785 2025161 := bstep (se 2 (by rfl) ⟨759435, by rfl⟩ : syracuseStep 2025161 = 1518871) B1518871
theorem B222983 : Blo 115785 222983 := bstep (se 1 (by rfl) ⟨167237, by rfl⟩ : syracuseStep 222983 = 334475) B334475
theorem B452861 : Blo 115785 452861 := bstep (se 3 (by rfl) ⟨84911, by rfl⟩ : syracuseStep 452861 = 169823) B169823
theorem B223655 : Blo 115785 223655 := bstep (se 1 (by rfl) ⟨167741, by rfl⟩ : syracuseStep 223655 = 335483) B335483
theorem B224635 : Blo 115785 224635 := bstep (se 1 (by rfl) ⟨168476, by rfl⟩ : syracuseStep 224635 = 336953) B336953
theorem B224851 : Blo 115785 224851 := bstep (se 1 (by rfl) ⟨168638, by rfl⟩ : syracuseStep 224851 = 337277) B337277
theorem B323155 : Blo 115785 323155 := bstep (se 1 (by rfl) ⟨242366, by rfl⟩ : syracuseStep 323155 = 484733) B484733
theorem B913069 : Blo 115785 913069 := bstep (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) B342401
theorem B1273553 : Blo 115785 1273553 := bstep (se 2 (by rfl) ⟨477582, by rfl⟩ : syracuseStep 1273553 = 955165) B955165
theorem B1208591 : Blo 115785 1208591 := bstep (se 1 (by rfl) ⟨906443, by rfl⟩ : syracuseStep 1208591 = 1812887) B1812887
theorem B225899 : Blo 115785 225899 := bstep (se 1 (by rfl) ⟨169424, by rfl⟩ : syracuseStep 225899 = 338849) B338849
theorem B586439 : Blo 115785 586439 := bstep (se 1 (by rfl) ⟨439829, by rfl⟩ : syracuseStep 586439 = 879659) B879659
theorem B226127 : Blo 115785 226127 := bstep (se 1 (by rfl) ⟨169595, by rfl⟩ : syracuseStep 226127 = 339191) B339191
theorem B1504109 : Blo 115785 1504109 := bstep (se 3 (by rfl) ⟨282020, by rfl⟩ : syracuseStep 1504109 = 564041) B564041
theorem B947153 : Blo 115785 947153 := bstep (se 2 (by rfl) ⟨355182, by rfl⟩ : syracuseStep 947153 = 710365) B710365
theorem B1701121 : Blo 115785 1701121 := bstep (se 2 (by rfl) ⟨637920, by rfl⟩ : syracuseStep 1701121 = 1275841) B1275841
theorem B423481 : Blo 115785 423481 := bstep (se 2 (by rfl) ⟨158805, by rfl⟩ : syracuseStep 423481 = 317611) B317611
theorem B358199 : Blo 115785 358199 := bstep (se 1 (by rfl) ⟨268649, by rfl⟩ : syracuseStep 358199 = 537299) B537299
theorem B19363697 : Blo 115785 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B293129 : Blo 115785 293129 := bstep (se 2 (by rfl) ⟨109923, by rfl⟩ : syracuseStep 293129 = 219847) B219847
theorem B391607 : Blo 115785 391607 := bstep (se 1 (by rfl) ⟨293705, by rfl⟩ : syracuseStep 391607 = 587411) B587411
theorem B260603 : Blo 115785 260603 := bstep (se 1 (by rfl) ⟨195452, by rfl⟩ : syracuseStep 260603 = 390905) B390905
theorem B457289 : Blo 115785 457289 := bstep (se 2 (by rfl) ⟨171483, by rfl⟩ : syracuseStep 457289 = 342967) B342967
theorem B293483 : Blo 115785 293483 := bstep (se 1 (by rfl) ⟨220112, by rfl⟩ : syracuseStep 293483 = 440225) B440225
theorem B260729 : Blo 115785 260729 := bstep (se 2 (by rfl) ⟨97773, by rfl⟩ : syracuseStep 260729 = 195547) B195547
theorem B260783 : Blo 115785 260783 := bstep (se 1 (by rfl) ⟨195587, by rfl⟩ : syracuseStep 260783 = 391175) B391175
theorem B260855 : Blo 115785 260855 := bstep (se 1 (by rfl) ⟨195641, by rfl⟩ : syracuseStep 260855 = 391283) B391283
theorem B261035 : Blo 115785 261035 := bstep (se 1 (by rfl) ⟨195776, by rfl⟩ : syracuseStep 261035 = 391553) B391553
theorem B195817 : Blo 115785 195817 := bstep (se 2 (by rfl) ⟨73431, by rfl⟩ : syracuseStep 195817 = 146863) B146863
theorem B294131 : Blo 115785 294131 := bstep (se 1 (by rfl) ⟨220598, by rfl⟩ : syracuseStep 294131 = 441197) B441197
theorem B195871 : Blo 115785 195871 := bstep (se 1 (by rfl) ⟨146903, by rfl⟩ : syracuseStep 195871 = 293807) B293807
theorem B589193 : Blo 115785 589193 := bstep (se 2 (by rfl) ⟨220947, by rfl⟩ : syracuseStep 589193 = 441895) B441895
theorem B261575 : Blo 115785 261575 := bstep (se 1 (by rfl) ⟨196181, by rfl⟩ : syracuseStep 261575 = 392363) B392363
theorem B1146383 : Blo 115785 1146383 := bstep (se 1 (by rfl) ⟨859787, by rfl⟩ : syracuseStep 1146383 = 1719575) B1719575
theorem B196283 : Blo 115785 196283 := bstep (se 1 (by rfl) ⟨147212, by rfl⟩ : syracuseStep 196283 = 294425) B294425
theorem B294587 : Blo 115785 294587 := bstep (se 1 (by rfl) ⟨220940, by rfl⟩ : syracuseStep 294587 = 441881) B441881
theorem B130783 : Blo 115785 130783 := bstep (se 1 (by rfl) ⟨98087, by rfl⟩ : syracuseStep 130783 = 196175) B196175
theorem B261935 : Blo 115785 261935 := bstep (se 1 (by rfl) ⟨196451, by rfl⟩ : syracuseStep 261935 = 392903) B392903
theorem B622511 : Blo 115785 622511 := bstep (se 1 (by rfl) ⟨466883, by rfl⟩ : syracuseStep 622511 = 933767) B933767
theorem B393497 : Blo 115785 393497 := bstep (se 2 (by rfl) ⟨147561, by rfl⟩ : syracuseStep 393497 = 295123) B295123
theorem B10944827 : Blo 115785 10944827 := bstep (se 1 (by rfl) ⟨8208620, by rfl⟩ : syracuseStep 10944827 = 16417241) B16417241
theorem B295265 : Blo 115785 295265 := bstep (se 2 (by rfl) ⟨110724, by rfl⟩ : syracuseStep 295265 = 221449) B221449
theorem B852407 : Blo 115785 852407 := bstep (se 1 (by rfl) ⟨639305, by rfl⟩ : syracuseStep 852407 = 1278611) B1278611
theorem B393659 : Blo 115785 393659 := bstep (se 1 (by rfl) ⟨295244, by rfl⟩ : syracuseStep 393659 = 590489) B590489
theorem B197113 : Blo 115785 197113 := bstep (se 2 (by rfl) ⟨73917, by rfl⟩ : syracuseStep 197113 = 147835) B147835
theorem B721505 : Blo 115785 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B230123 : Blo 115785 230123 := bstep (se 1 (by rfl) ⟨172592, by rfl⟩ : syracuseStep 230123 = 345185) B345185
theorem B197383 : Blo 115785 197383 := bstep (se 1 (by rfl) ⟨148037, by rfl⟩ : syracuseStep 197383 = 296075) B296075
theorem B197417 : Blo 115785 197417 := bstep (se 2 (by rfl) ⟨74031, by rfl⟩ : syracuseStep 197417 = 148063) B148063
theorem B132007 : Blo 115785 132007 := bstep (se 1 (by rfl) ⟨99005, by rfl⟩ : syracuseStep 132007 = 198011) B198011
theorem B263123 : Blo 115785 263123 := bstep (se 1 (by rfl) ⟨197342, by rfl⟩ : syracuseStep 263123 = 394685) B394685
theorem B197687 : Blo 115785 197687 := bstep (se 1 (by rfl) ⟨148265, by rfl⟩ : syracuseStep 197687 = 296531) B296531
theorem B263375 : Blo 115785 263375 := bstep (se 1 (by rfl) ⟨197531, by rfl⟩ : syracuseStep 263375 = 395063) B395063
theorem B263699 : Blo 115785 263699 := bstep (se 1 (by rfl) ⟨197774, by rfl⟩ : syracuseStep 263699 = 395549) B395549
theorem B394847 : Blo 115785 394847 := bstep (se 1 (by rfl) ⟨296135, by rfl⟩ : syracuseStep 394847 = 592271) B592271
theorem B198463 : Blo 115785 198463 := bstep (se 1 (by rfl) ⟨148847, by rfl⟩ : syracuseStep 198463 = 297695) B297695
theorem B264383 : Blo 115785 264383 := bstep (se 1 (by rfl) ⟨198287, by rfl⟩ : syracuseStep 264383 = 396575) B396575
theorem B297209 : Blo 115785 297209 := bstep (se 2 (by rfl) ⟨111453, by rfl⟩ : syracuseStep 297209 = 222907) B222907
theorem B3639563 : Blo 115785 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B952667 : Blo 115785 952667 := bstep (se 1 (by rfl) ⟨714500, by rfl⟩ : syracuseStep 952667 = 1429001) B1429001
theorem B133663 : Blo 115785 133663 := bstep (se 1 (by rfl) ⟨100247, by rfl⟩ : syracuseStep 133663 = 200495) B200495
theorem B297503 : Blo 115785 297503 := bstep (se 1 (by rfl) ⟨223127, by rfl⟩ : syracuseStep 297503 = 446255) B446255
theorem B199199 : Blo 115785 199199 := bstep (se 1 (by rfl) ⟨149399, by rfl⟩ : syracuseStep 199199 = 298799) B298799
theorem B1968745 : Blo 115785 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B199273 : Blo 115785 199273 := bstep (se 2 (by rfl) ⟨74727, by rfl⟩ : syracuseStep 199273 = 149455) B149455
theorem B199631 : Blo 115785 199631 := bstep (se 1 (by rfl) ⟨149723, by rfl⟩ : syracuseStep 199631 = 299447) B299447
theorem B396251 : Blo 115785 396251 := bstep (se 1 (by rfl) ⟨297188, by rfl⟩ : syracuseStep 396251 = 594377) B594377
theorem B265337 : Blo 115785 265337 := bstep (se 2 (by rfl) ⟨99501, by rfl⟩ : syracuseStep 265337 = 199003) B199003
theorem B560351 : Blo 115785 560351 := bstep (se 1 (by rfl) ⟨420263, by rfl⟩ : syracuseStep 560351 = 840527) B840527
theorem B396521 : Blo 115785 396521 := bstep (se 2 (by rfl) ⟨148695, by rfl⟩ : syracuseStep 396521 = 297391) B297391
theorem B396733 : Blo 115785 396733 := bstep (se 3 (by rfl) ⟨74387, by rfl⟩ : syracuseStep 396733 = 148775) B148775
theorem B757181 : Blo 115785 757181 := bstep (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) B283943
theorem B396791 : Blo 115785 396791 := bstep (se 1 (by rfl) ⟨297593, by rfl⟩ : syracuseStep 396791 = 595187) B595187
theorem B200299 : Blo 115785 200299 := bstep (se 1 (by rfl) ⟨150224, by rfl⟩ : syracuseStep 200299 = 300449) B300449
theorem B266003 : Blo 115785 266003 := bstep (se 1 (by rfl) ⟨199502, by rfl⟩ : syracuseStep 266003 = 399005) B399005
theorem B331559 : Blo 115785 331559 := bstep (se 1 (by rfl) ⟨248669, by rfl⟩ : syracuseStep 331559 = 497339) B497339
theorem B200569 : Blo 115785 200569 := bstep (se 2 (by rfl) ⟨75213, by rfl⟩ : syracuseStep 200569 = 150427) B150427
theorem B200603 : Blo 115785 200603 := bstep (se 1 (by rfl) ⟨150452, by rfl⟩ : syracuseStep 200603 = 300905) B300905
theorem B266363 : Blo 115785 266363 := bstep (se 1 (by rfl) ⟨199772, by rfl⟩ : syracuseStep 266363 = 399545) B399545
theorem B659609 : Blo 115785 659609 := bstep (se 2 (by rfl) ⟨247353, by rfl⟩ : syracuseStep 659609 = 494707) B494707
theorem B266633 : Blo 115785 266633 := bstep (se 2 (by rfl) ⟨99987, by rfl⟩ : syracuseStep 266633 = 199975) B199975
theorem B561581 : Blo 115785 561581 := bstep (se 3 (by rfl) ⟨105296, by rfl⟩ : syracuseStep 561581 = 210593) B210593
theorem B659927 : Blo 115785 659927 := bstep (se 1 (by rfl) ⟨494945, by rfl⟩ : syracuseStep 659927 = 989891) B989891
theorem B299513 : Blo 115785 299513 := bstep (se 2 (by rfl) ⟨112317, by rfl⟩ : syracuseStep 299513 = 224635) B224635
theorem B397817 : Blo 115785 397817 := bstep (se 2 (by rfl) ⟨149181, by rfl⟩ : syracuseStep 397817 = 298363) B298363
theorem B398087 : Blo 115785 398087 := bstep (se 1 (by rfl) ⟨298565, by rfl⟩ : syracuseStep 398087 = 597131) B597131
theorem B299801 : Blo 115785 299801 := bstep (se 2 (by rfl) ⟨112425, by rfl⟩ : syracuseStep 299801 = 224851) B224851
theorem B529193 : Blo 115785 529193 := bstep (se 2 (by rfl) ⟨198447, by rfl⟩ : syracuseStep 529193 = 396895) B396895
theorem B398141 : Blo 115785 398141 := bstep (se 3 (by rfl) ⟨74651, by rfl⟩ : syracuseStep 398141 = 149303) B149303
theorem B1217425 : Blo 115785 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B496655 : Blo 115785 496655 := bstep (se 1 (by rfl) ⟨372491, by rfl⟩ : syracuseStep 496655 = 744983) B744983
theorem B300095 : Blo 115785 300095 := bstep (se 1 (by rfl) ⟨225071, by rfl⟩ : syracuseStep 300095 = 450143) B450143
theorem B201791 : Blo 115785 201791 := bstep (se 1 (by rfl) ⟨151343, by rfl⟩ : syracuseStep 201791 = 302687) B302687
theorem B595025 : Blo 115785 595025 := bstep (se 2 (by rfl) ⟨223134, by rfl⟩ : syracuseStep 595025 = 446269) B446269
theorem B267371 : Blo 115785 267371 := bstep (se 1 (by rfl) ⟨200528, by rfl⟩ : syracuseStep 267371 = 401057) B401057
theorem B300307 : Blo 115785 300307 := bstep (se 1 (by rfl) ⟨225230, by rfl⟩ : syracuseStep 300307 = 450461) B450461
theorem B759131 : Blo 115785 759131 := bstep (se 1 (by rfl) ⟨569348, by rfl⟩ : syracuseStep 759131 = 1138697) B1138697
theorem B11474369 : Blo 115785 11474369 := bstep (se 2 (by rfl) ⟨4302888, by rfl⟩ : syracuseStep 11474369 = 8605777) B8605777
theorem B1381835 : Blo 115785 1381835 := bstep (se 1 (by rfl) ⟨1036376, by rfl⟩ : syracuseStep 1381835 = 2072753) B2072753
theorem B267947 : Blo 115785 267947 := bstep (se 1 (by rfl) ⟨200960, by rfl⟩ : syracuseStep 267947 = 401921) B401921
theorem B3413771 : Blo 115785 3413771 := bstep (se 1 (by rfl) ⟨2560328, by rfl⟩ : syracuseStep 3413771 = 5120657) B5120657
theorem B399167 : Blo 115785 399167 := bstep (se 1 (by rfl) ⟨299375, by rfl⟩ : syracuseStep 399167 = 598751) B598751
theorem B268271 : Blo 115785 268271 := bstep (se 1 (by rfl) ⟨201203, by rfl⟩ : syracuseStep 268271 = 402407) B402407
theorem B268487 : Blo 115785 268487 := bstep (se 1 (by rfl) ⟨201365, by rfl⟩ : syracuseStep 268487 = 402731) B402731
theorem B530729 : Blo 115785 530729 := bstep (se 2 (by rfl) ⟨199023, by rfl⟩ : syracuseStep 530729 = 398047) B398047
theorem B268667 : Blo 115785 268667 := bstep (se 1 (by rfl) ⟨201500, by rfl⟩ : syracuseStep 268667 = 403001) B403001
theorem B596413 : Blo 115785 596413 := bstep (se 3 (by rfl) ⟨111827, by rfl⟩ : syracuseStep 596413 = 223655) B223655
theorem B1350107 : Blo 115785 1350107 := bstep (se 1 (by rfl) ⟨1012580, by rfl⟩ : syracuseStep 1350107 = 2025161) B2025161
theorem B268937 : Blo 115785 268937 := bstep (se 2 (by rfl) ⟨100851, by rfl⟩ : syracuseStep 268937 = 201703) B201703
theorem B3349187 : Blo 115785 3349187 := bstep (se 1 (by rfl) ⟨2511890, by rfl⟩ : syracuseStep 3349187 = 5023781) B5023781
theorem B3250925 : Blo 115785 3250925 := bstep (se 3 (by rfl) ⟨609548, by rfl⟩ : syracuseStep 3250925 = 1219097) B1219097
theorem B301907 : Blo 115785 301907 := bstep (se 1 (by rfl) ⟨226430, by rfl⟩ : syracuseStep 301907 = 452861) B452861
theorem B334817 : Blo 115785 334817 := bstep (se 2 (by rfl) ⟨125556, by rfl⟩ : syracuseStep 334817 = 251113) B251113
theorem B2268161 : Blo 115785 2268161 := bstep (se 2 (by rfl) ⟨850560, by rfl⟩ : syracuseStep 2268161 = 1701121) B1701121
theorem B564349 : Blo 115785 564349 := bstep (se 3 (by rfl) ⟨105815, by rfl⟩ : syracuseStep 564349 = 211631) B211631
theorem B269495 : Blo 115785 269495 := bstep (se 1 (by rfl) ⟨202121, by rfl⟩ : syracuseStep 269495 = 404243) B404243
theorem B400679 : Blo 115785 400679 := bstep (se 1 (by rfl) ⟨300509, by rfl⟩ : syracuseStep 400679 = 601019) B601019
theorem B990575 : Blo 115785 990575 := bstep (se 1 (by rfl) ⟨742931, by rfl⟩ : syracuseStep 990575 = 1485863) B1485863
theorem B564641 : Blo 115785 564641 := bstep (se 2 (by rfl) ⟨211740, by rfl⟩ : syracuseStep 564641 = 423481) B423481
theorem B335603 : Blo 115785 335603 := bstep (se 1 (by rfl) ⟨251702, by rfl⟩ : syracuseStep 335603 = 503405) B503405
theorem B401543 : Blo 115785 401543 := bstep (se 1 (by rfl) ⟨301157, by rfl⟩ : syracuseStep 401543 = 602315) B602315
theorem B336491 : Blo 115785 336491 := bstep (se 1 (by rfl) ⟨252368, by rfl⟩ : syracuseStep 336491 = 504737) B504737
theorem B631435 : Blo 115785 631435 := bstep (se 1 (by rfl) ⟨473576, by rfl⟩ : syracuseStep 631435 = 947153) B947153
theorem B893753 : Blo 115785 893753 := bstep (se 2 (by rfl) ⟨335157, by rfl⟩ : syracuseStep 893753 = 670315) B670315
theorem B238799 : Blo 115785 238799 := bstep (se 1 (by rfl) ⟨179099, by rfl⟩ : syracuseStep 238799 = 358199) B358199
theorem B403055 : Blo 115785 403055 := bstep (se 1 (by rfl) ⟨302291, by rfl⟩ : syracuseStep 403055 = 604583) B604583
theorem B173735 : Blo 115785 173735 := bstep (se 1 (by rfl) ⟨130301, by rfl⟩ : syracuseStep 173735 = 260603) B260603
theorem B304859 : Blo 115785 304859 := bstep (se 1 (by rfl) ⟨228644, by rfl⟩ : syracuseStep 304859 = 457289) B457289
theorem B403163 : Blo 115785 403163 := bstep (se 1 (by rfl) ⟨302372, by rfl⟩ : syracuseStep 403163 = 604745) B604745
theorem B173819 : Blo 115785 173819 := bstep (se 1 (by rfl) ⟨130364, by rfl⟩ : syracuseStep 173819 = 260729) B260729
theorem B173855 : Blo 115785 173855 := bstep (se 1 (by rfl) ⟨130391, by rfl⟩ : syracuseStep 173855 = 260783) B260783
theorem B173903 : Blo 115785 173903 := bstep (se 1 (by rfl) ⟨130427, by rfl⟩ : syracuseStep 173903 = 260855) B260855
theorem B665441 : Blo 115785 665441 := bstep (se 2 (by rfl) ⟨249540, by rfl⟩ : syracuseStep 665441 = 499081) B499081
theorem B174023 : Blo 115785 174023 := bstep (se 1 (by rfl) ⟨130517, by rfl⟩ : syracuseStep 174023 = 261035) B261035
theorem B403399 : Blo 115785 403399 := bstep (se 1 (by rfl) ⟨302549, by rfl⟩ : syracuseStep 403399 = 605099) B605099
theorem B600209 : Blo 115785 600209 := bstep (se 2 (by rfl) ⟨225078, by rfl⟩ : syracuseStep 600209 = 450157) B450157
theorem B174377 : Blo 115785 174377 := bstep (se 2 (by rfl) ⟨65391, by rfl⟩ : syracuseStep 174377 = 130783) B130783
theorem B174383 : Blo 115785 174383 := bstep (se 1 (by rfl) ⟨130787, by rfl⟩ : syracuseStep 174383 = 261575) B261575
theorem B764255 : Blo 115785 764255 := bstep (se 1 (by rfl) ⟨573191, by rfl⟩ : syracuseStep 764255 = 1146383) B1146383
theorem B174623 : Blo 115785 174623 := bstep (se 1 (by rfl) ⟨130967, by rfl⟩ : syracuseStep 174623 = 261935) B261935
theorem B175007 : Blo 115785 175007 := bstep (se 1 (by rfl) ⟨131255, by rfl⟩ : syracuseStep 175007 = 262511) B262511
theorem B175055 : Blo 115785 175055 := bstep (se 1 (by rfl) ⟨131291, by rfl⟩ : syracuseStep 175055 = 262583) B262583
theorem B535531 : Blo 115785 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B175145 : Blo 115785 175145 := bstep (se 2 (by rfl) ⟨65679, by rfl⟩ : syracuseStep 175145 = 131359) B131359
theorem B175151 : Blo 115785 175151 := bstep (se 1 (by rfl) ⟨131363, by rfl⟩ : syracuseStep 175151 = 262727) B262727
theorem B175175 : Blo 115785 175175 := bstep (se 1 (by rfl) ⟨131381, by rfl⟩ : syracuseStep 175175 = 262763) B262763
theorem B339167 : Blo 115785 339167 := bstep (se 1 (by rfl) ⟨254375, by rfl⟩ : syracuseStep 339167 = 508751) B508751
theorem B175439 : Blo 115785 175439 := bstep (se 1 (by rfl) ⟨131579, by rfl⟩ : syracuseStep 175439 = 263159) B263159
theorem B175529 : Blo 115785 175529 := bstep (se 2 (by rfl) ⟨65823, by rfl⟩ : syracuseStep 175529 = 131647) B131647
theorem B1453625 : Blo 115785 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B175679 : Blo 115785 175679 := bstep (se 1 (by rfl) ⟨131759, by rfl⟩ : syracuseStep 175679 = 263519) B263519
theorem B175943 : Blo 115785 175943 := bstep (se 1 (by rfl) ⟨131957, by rfl⟩ : syracuseStep 175943 = 263915) B263915
theorem B339851 : Blo 115785 339851 := bstep (se 1 (by rfl) ⟨254888, by rfl⟩ : syracuseStep 339851 = 509777) B509777
theorem B176027 : Blo 115785 176027 := bstep (se 1 (by rfl) ⟨132020, by rfl⟩ : syracuseStep 176027 = 264041) B264041
theorem B176521 : Blo 115785 176521 := bstep (se 2 (by rfl) ⟨66195, by rfl⟩ : syracuseStep 176521 = 132391) B132391
theorem B176591 : Blo 115785 176591 := bstep (se 1 (by rfl) ⟨132443, by rfl⟩ : syracuseStep 176591 = 264887) B264887
theorem B176633 : Blo 115785 176633 := bstep (se 2 (by rfl) ⟨66237, by rfl⟩ : syracuseStep 176633 = 132475) B132475
theorem B602639 : Blo 115785 602639 := bstep (se 1 (by rfl) ⟨451979, by rfl⟩ : syracuseStep 602639 = 903959) B903959
theorem B176735 : Blo 115785 176735 := bstep (se 1 (by rfl) ⟨132551, by rfl⟩ : syracuseStep 176735 = 265103) B265103
theorem B1421995 : Blo 115785 1421995 := bstep (se 1 (by rfl) ⟨1066496, by rfl⟩ : syracuseStep 1421995 = 2132993) B2132993
theorem B177215 : Blo 115785 177215 := bstep (se 1 (by rfl) ⟨132911, by rfl⟩ : syracuseStep 177215 = 265823) B265823
theorem B177257 : Blo 115785 177257 := bstep (se 2 (by rfl) ⟨66471, by rfl⟩ : syracuseStep 177257 = 132943) B132943
theorem B1881265 : Blo 115785 1881265 := bstep (se 2 (by rfl) ⟨705474, by rfl⟩ : syracuseStep 1881265 = 1410949) B1410949
theorem B177359 : Blo 115785 177359 := bstep (se 1 (by rfl) ⟨133019, by rfl⟩ : syracuseStep 177359 = 266039) B266039
theorem B668915 : Blo 115785 668915 := bstep (se 1 (by rfl) ⟨501686, by rfl⟩ : syracuseStep 668915 = 1003373) B1003373
theorem B177563 : Blo 115785 177563 := bstep (se 1 (by rfl) ⟨133172, by rfl⟩ : syracuseStep 177563 = 266345) B266345
theorem B177785 : Blo 115785 177785 := bstep (se 2 (by rfl) ⟨66669, by rfl⟩ : syracuseStep 177785 = 133339) B133339
theorem B177887 : Blo 115785 177887 := bstep (se 1 (by rfl) ⟨133415, by rfl⟩ : syracuseStep 177887 = 266831) B266831
theorem B571115 : Blo 115785 571115 := bstep (se 1 (by rfl) ⟨428336, by rfl⟩ : syracuseStep 571115 = 856673) B856673
theorem B177983 : Blo 115785 177983 := bstep (se 1 (by rfl) ⟨133487, by rfl⟩ : syracuseStep 177983 = 266975) B266975
theorem B178151 : Blo 115785 178151 := bstep (se 1 (by rfl) ⟨133613, by rfl⟩ : syracuseStep 178151 = 267227) B267227
theorem B178169 : Blo 115785 178169 := bstep (se 2 (by rfl) ⟨66813, by rfl⟩ : syracuseStep 178169 = 133627) B133627
theorem B178271 : Blo 115785 178271 := bstep (se 1 (by rfl) ⟨133703, by rfl⟩ : syracuseStep 178271 = 267407) B267407
theorem B178331 : Blo 115785 178331 := bstep (se 1 (by rfl) ⟨133748, by rfl⟩ : syracuseStep 178331 = 267497) B267497
theorem B178367 : Blo 115785 178367 := bstep (se 1 (by rfl) ⟨133775, by rfl⟩ : syracuseStep 178367 = 267551) B267551
theorem B178409 : Blo 115785 178409 := bstep (se 2 (by rfl) ⟨66903, by rfl⟩ : syracuseStep 178409 = 133807) B133807
theorem B178715 : Blo 115785 178715 := bstep (se 1 (by rfl) ⟨134036, by rfl⟩ : syracuseStep 178715 = 268073) B268073
theorem B571961 : Blo 115785 571961 := bstep (se 2 (by rfl) ⟨214485, by rfl⟩ : syracuseStep 571961 = 428971) B428971
theorem B178793 : Blo 115785 178793 := bstep (se 2 (by rfl) ⟨67047, by rfl⟩ : syracuseStep 178793 = 134095) B134095
theorem B1227727 : Blo 115785 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B179321 : Blo 115785 179321 := bstep (se 2 (by rfl) ⟨67245, by rfl⟩ : syracuseStep 179321 = 134491) B134491
theorem B179423 : Blo 115785 179423 := bstep (se 1 (by rfl) ⟨134567, by rfl⟩ : syracuseStep 179423 = 269135) B269135
theorem B179465 : Blo 115785 179465 := bstep (se 2 (by rfl) ⟨67299, by rfl⟩ : syracuseStep 179465 = 134599) B134599
theorem B146767 : Blo 115785 146767 := bstep (se 1 (by rfl) ⟨110075, by rfl⟩ : syracuseStep 146767 = 220151) B220151
theorem B179567 : Blo 115785 179567 := bstep (se 1 (by rfl) ⟨134675, by rfl⟩ : syracuseStep 179567 = 269351) B269351
theorem B147035 : Blo 115785 147035 := bstep (se 1 (by rfl) ⟨110276, by rfl⟩ : syracuseStep 147035 = 220553) B220553
theorem B1326779 : Blo 115785 1326779 := bstep (se 1 (by rfl) ⟨995084, by rfl⟩ : syracuseStep 1326779 = 1990169) B1990169
theorem B573115 : Blo 115785 573115 := bstep (se 1 (by rfl) ⟨429836, by rfl⟩ : syracuseStep 573115 = 859673) B859673
theorem B442199 : Blo 115785 442199 := bstep (se 1 (by rfl) ⟨331649, by rfl⟩ : syracuseStep 442199 = 663299) B663299
theorem B2867339 : Blo 115785 2867339 := bstep (se 1 (by rfl) ⟨2150504, by rfl⟩ : syracuseStep 2867339 = 4301009) B4301009
theorem B1294697 : Blo 115785 1294697 := bstep (se 2 (by rfl) ⟨485511, by rfl⟩ : syracuseStep 1294697 = 971023) B971023
theorem B377207 : Blo 115785 377207 := bstep (se 1 (by rfl) ⟨282905, by rfl⟩ : syracuseStep 377207 = 565811) B565811
theorem B345043 : Blo 115785 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B148655 : Blo 115785 148655 := bstep (se 1 (by rfl) ⟨111491, by rfl⟩ : syracuseStep 148655 = 222983) B222983
theorem B115919 : Blo 115785 115919 := bstep (se 1 (by rfl) ⟨86939, by rfl⟩ : syracuseStep 115919 = 173879) B173879
theorem B116123 : Blo 115785 116123 := bstep (se 1 (by rfl) ⟨87092, by rfl⟩ : syracuseStep 116123 = 174185) B174185
theorem B378283 : Blo 115785 378283 := bstep (se 1 (by rfl) ⟨283712, by rfl⟩ : syracuseStep 378283 = 567425) B567425
theorem B837067 : Blo 115785 837067 := bstep (se 1 (by rfl) ⟨627800, by rfl⟩ : syracuseStep 837067 = 1255601) B1255601
theorem B3130919 : Blo 115785 3130919 := bstep (se 1 (by rfl) ⟨2348189, by rfl⟩ : syracuseStep 3130919 = 4696379) B4696379
theorem B116335 : Blo 115785 116335 := bstep (se 1 (by rfl) ⟨87251, by rfl⟩ : syracuseStep 116335 = 174503) B174503
theorem B116391 : Blo 115785 116391 := bstep (se 1 (by rfl) ⟨87293, by rfl⟩ : syracuseStep 116391 = 174587) B174587
theorem B116475 : Blo 115785 116475 := bstep (se 1 (by rfl) ⟨87356, by rfl⟩ : syracuseStep 116475 = 174713) B174713
theorem B116511 : Blo 115785 116511 := bstep (se 1 (by rfl) ⟨87383, by rfl⟩ : syracuseStep 116511 = 174767) B174767
theorem B116543 : Blo 115785 116543 := bstep (se 1 (by rfl) ⟨87407, by rfl⟩ : syracuseStep 116543 = 174815) B174815
theorem B116719 : Blo 115785 116719 := bstep (se 1 (by rfl) ⟨87539, by rfl⟩ : syracuseStep 116719 = 175079) B175079
theorem B116891 : Blo 115785 116891 := bstep (se 1 (by rfl) ⟨87668, by rfl⟩ : syracuseStep 116891 = 175337) B175337
theorem B116927 : Blo 115785 116927 := bstep (se 1 (by rfl) ⟨87695, by rfl⟩ : syracuseStep 116927 = 175391) B175391
theorem B117039 : Blo 115785 117039 := bstep (se 1 (by rfl) ⟨87779, by rfl⟩ : syracuseStep 117039 = 175559) B175559
theorem B379399 : Blo 115785 379399 := bstep (se 1 (by rfl) ⟨284549, by rfl⟩ : syracuseStep 379399 = 569099) B569099
theorem B117275 : Blo 115785 117275 := bstep (se 1 (by rfl) ⟨87956, by rfl⟩ : syracuseStep 117275 = 175913) B175913
theorem B117279 : Blo 115785 117279 := bstep (se 1 (by rfl) ⟨87959, by rfl⟩ : syracuseStep 117279 = 175919) B175919
theorem B641641 : Blo 115785 641641 := bstep (se 2 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 641641 = 481231) B481231
theorem B641681 : Blo 115785 641681 := bstep (se 2 (by rfl) ⟨240630, by rfl⟩ : syracuseStep 641681 = 481261) B481261
theorem B445115 : Blo 115785 445115 := bstep (se 1 (by rfl) ⟨333836, by rfl⟩ : syracuseStep 445115 = 667673) B667673
theorem B576343 : Blo 115785 576343 := bstep (se 1 (by rfl) ⟨432257, by rfl⟩ : syracuseStep 576343 = 864515) B864515
theorem B117595 : Blo 115785 117595 := bstep (se 1 (by rfl) ⟨88196, by rfl⟩ : syracuseStep 117595 = 176393) B176393
theorem B805727 : Blo 115785 805727 := bstep (se 1 (by rfl) ⟨604295, by rfl⟩ : syracuseStep 805727 = 1208591) B1208591
theorem B117663 : Blo 115785 117663 := bstep (se 1 (by rfl) ⟨88247, by rfl⟩ : syracuseStep 117663 = 176495) B176495
theorem B117807 : Blo 115785 117807 := bstep (se 1 (by rfl) ⟨88355, by rfl⟩ : syracuseStep 117807 = 176711) B176711
theorem B117831 : Blo 115785 117831 := bstep (se 1 (by rfl) ⟨88373, by rfl⟩ : syracuseStep 117831 = 176747) B176747
theorem B150599 : Blo 115785 150599 := bstep (se 1 (by rfl) ⟨112949, by rfl⟩ : syracuseStep 150599 = 225899) B225899
theorem B1723493 : Blo 115785 1723493 := bstep (se 4 (by rfl) ⟨161577, by rfl⟩ : syracuseStep 1723493 = 323155) B323155
theorem B117983 : Blo 115785 117983 := bstep (se 1 (by rfl) ⟨88487, by rfl⟩ : syracuseStep 117983 = 176975) B176975
theorem B150751 : Blo 115785 150751 := bstep (se 1 (by rfl) ⟨113063, by rfl⟩ : syracuseStep 150751 = 226127) B226127
theorem B1002739 : Blo 115785 1002739 := bstep (se 1 (by rfl) ⟨752054, by rfl⟩ : syracuseStep 1002739 = 1504109) B1504109
theorem B118247 : Blo 115785 118247 := bstep (se 1 (by rfl) ⟨88685, by rfl⟩ : syracuseStep 118247 = 177371) B177371
theorem B118363 : Blo 115785 118363 := bstep (se 1 (by rfl) ⟨88772, by rfl⟩ : syracuseStep 118363 = 177545) B177545
theorem B184103 : Blo 115785 184103 := bstep (se 1 (by rfl) ⟨138077, by rfl⟩ : syracuseStep 184103 = 276155) B276155
theorem B118599 : Blo 115785 118599 := bstep (se 1 (by rfl) ⟨88949, by rfl⟩ : syracuseStep 118599 = 177899) B177899
theorem B118751 : Blo 115785 118751 := bstep (se 1 (by rfl) ⟨89063, by rfl⟩ : syracuseStep 118751 = 178127) B178127
theorem B119015 : Blo 115785 119015 := bstep (se 1 (by rfl) ⟨89261, by rfl⟩ : syracuseStep 119015 = 178523) B178523
theorem B119167 : Blo 115785 119167 := bstep (se 1 (by rfl) ⟨89375, by rfl⟩ : syracuseStep 119167 = 178751) B178751
theorem B119247 : Blo 115785 119247 := bstep (se 1 (by rfl) ⟨89435, by rfl⟩ : syracuseStep 119247 = 178871) B178871
theorem B250361 : Blo 115785 250361 := bstep (se 2 (by rfl) ⟨93885, by rfl⟩ : syracuseStep 250361 = 187771) B187771
theorem B119399 : Blo 115785 119399 := bstep (se 1 (by rfl) ⟨89549, by rfl⟩ : syracuseStep 119399 = 179099) B179099
theorem B119663 : Blo 115785 119663 := bstep (se 1 (by rfl) ⟨89747, by rfl⟩ : syracuseStep 119663 = 179495) B179495
theorem B119719 : Blo 115785 119719 := bstep (se 1 (by rfl) ⟨89789, by rfl⟩ : syracuseStep 119719 = 179579) B179579
theorem B415007 : Blo 115785 415007 := bstep (se 1 (by rfl) ⟨311255, by rfl⟩ : syracuseStep 415007 = 622511) B622511
theorem B1398169 : Blo 115785 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B186143 : Blo 115785 186143 := bstep (se 1 (by rfl) ⟨139607, by rfl⟩ : syracuseStep 186143 = 279215) B279215
theorem B2414551 : Blo 115785 2414551 := bstep (se 1 (by rfl) ⟨1810913, by rfl⟩ : syracuseStep 2414551 = 3621827) B3621827
theorem B284635 : Blo 115785 284635 := bstep (se 1 (by rfl) ⟨213476, by rfl⟩ : syracuseStep 284635 = 426953) B426953
theorem B1923047 : Blo 115785 1923047 := bstep (se 1 (by rfl) ⟨1442285, by rfl⟩ : syracuseStep 1923047 = 2884571) B2884571
theorem B448487 : Blo 115785 448487 := bstep (se 1 (by rfl) ⟨336365, by rfl⟩ : syracuseStep 448487 = 672731) B672731
theorem B710657 : Blo 115785 710657 := bstep (se 2 (by rfl) ⟨266496, by rfl⟩ : syracuseStep 710657 = 532993) B532993
theorem B252001 : Blo 115785 252001 := bstep (se 2 (by rfl) ⟨94500, by rfl⟩ : syracuseStep 252001 = 189001) B189001
theorem B678131 : Blo 115785 678131 := bstep (se 1 (by rfl) ⟨508598, by rfl⟩ : syracuseStep 678131 = 1017197) B1017197
theorem B678881 : Blo 115785 678881 := bstep (se 2 (by rfl) ⟨254580, by rfl⟩ : syracuseStep 678881 = 509161) B509161
theorem B220583 : Blo 115785 220583 := bstep (se 1 (by rfl) ⟨165437, by rfl⟩ : syracuseStep 220583 = 330875) B330875
theorem B1007113 : Blo 115785 1007113 := bstep (se 2 (by rfl) ⟨377667, by rfl⟩ : syracuseStep 1007113 = 755335) B755335
theorem B254171 : Blo 115785 254171 := bstep (se 1 (by rfl) ⟨190628, by rfl⟩ : syracuseStep 254171 = 381257) B381257
theorem B221647 : Blo 115785 221647 := bstep (se 1 (by rfl) ⟨166235, by rfl⟩ : syracuseStep 221647 = 332471) B332471
theorem B680521 : Blo 115785 680521 := bstep (se 2 (by rfl) ⟨255195, by rfl⟩ : syracuseStep 680521 = 510391) B510391
theorem B320129 : Blo 115785 320129 := bstep (se 2 (by rfl) ⟨120048, by rfl⟩ : syracuseStep 320129 = 240097) B240097
theorem B1532951 : Blo 115785 1532951 := bstep (se 1 (by rfl) ⟨1149713, by rfl⟩ : syracuseStep 1532951 = 2299427) B2299427
theorem B1303595 : Blo 115785 1303595 := bstep (se 1 (by rfl) ⟨977696, by rfl⟩ : syracuseStep 1303595 = 1955393) B1955393
theorem B681479 : Blo 115785 681479 := bstep (se 1 (by rfl) ⟨511109, by rfl⟩ : syracuseStep 681479 = 1022219) B1022219
theorem B1632473 : Blo 115785 1632473 := bstep (se 2 (by rfl) ⟨612177, by rfl⟩ : syracuseStep 1632473 = 1224355) B1224355
theorem B289003 : Blo 115785 289003 := bstep (se 1 (by rfl) ⟨216752, by rfl⟩ : syracuseStep 289003 = 433505) B433505
theorem B1632869 : Blo 115785 1632869 := bstep (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) B306163
theorem B748547 : Blo 115785 748547 := bstep (se 1 (by rfl) ⟨561410, by rfl⟩ : syracuseStep 748547 = 1122821) B1122821
theorem B1994543 : Blo 115785 1994543 := bstep (se 1 (by rfl) ⟨1495907, by rfl⟩ : syracuseStep 1994543 = 2991815) B2991815
theorem B1012445 : Blo 115785 1012445 := bstep (se 3 (by rfl) ⟨189833, by rfl⟩ : syracuseStep 1012445 = 379667) B379667
theorem B422975 : Blo 115785 422975 := bstep (se 1 (by rfl) ⟨317231, by rfl⟩ : syracuseStep 422975 = 634463) B634463
theorem B849035 : Blo 115785 849035 := bstep (se 1 (by rfl) ⟨636776, by rfl⟩ : syracuseStep 849035 = 1273553) B1273553
theorem B2061607 : Blo 115785 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B226651 : Blo 115785 226651 := bstep (se 1 (by rfl) ⟨169988, by rfl⟩ : syracuseStep 226651 = 339977) B339977
theorem B390959 : Blo 115785 390959 := bstep (se 1 (by rfl) ⟨293219, by rfl⟩ : syracuseStep 390959 = 586439) B586439
theorem B423899 : Blo 115785 423899 := bstep (se 1 (by rfl) ⟨317924, by rfl⟩ : syracuseStep 423899 = 635849) B635849
theorem B12909131 : Blo 115785 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B719513 : Blo 115785 719513 := bstep (se 2 (by rfl) ⟨269817, by rfl⟩ : syracuseStep 719513 = 539635) B539635
theorem B195419 : Blo 115785 195419 := bstep (se 1 (by rfl) ⟨146564, by rfl⟩ : syracuseStep 195419 = 293129) B293129
theorem B261071 : Blo 115785 261071 := bstep (se 1 (by rfl) ⟨195803, by rfl⟩ : syracuseStep 261071 = 391607) B391607
theorem B261089 : Blo 115785 261089 := bstep (se 2 (by rfl) ⟨97908, by rfl⟩ : syracuseStep 261089 = 195817) B195817
theorem B261161 : Blo 115785 261161 := bstep (se 2 (by rfl) ⟨97935, by rfl⟩ : syracuseStep 261161 = 195871) B195871
theorem B195655 : Blo 115785 195655 := bstep (se 1 (by rfl) ⟨146741, by rfl⟩ : syracuseStep 195655 = 293483) B293483
theorem B196087 : Blo 115785 196087 := bstep (se 1 (by rfl) ⟨147065, by rfl⟩ : syracuseStep 196087 = 294131) B294131
theorem B392795 : Blo 115785 392795 := bstep (se 1 (by rfl) ⟨294596, by rfl⟩ : syracuseStep 392795 = 589193) B589193
theorem B130855 : Blo 115785 130855 := bstep (se 1 (by rfl) ⟨98141, by rfl⟩ : syracuseStep 130855 = 196283) B196283
theorem B196391 : Blo 115785 196391 := bstep (se 1 (by rfl) ⟨147293, by rfl⟩ : syracuseStep 196391 = 294587) B294587
theorem B294779 : Blo 115785 294779 := bstep (se 1 (by rfl) ⟨221084, by rfl⟩ : syracuseStep 294779 = 442169) B442169
theorem B262331 : Blo 115785 262331 := bstep (se 1 (by rfl) ⟨196748, by rfl⟩ : syracuseStep 262331 = 393497) B393497
theorem B196843 : Blo 115785 196843 := bstep (se 1 (by rfl) ⟨147632, by rfl⟩ : syracuseStep 196843 = 295265) B295265
theorem B262439 : Blo 115785 262439 := bstep (se 1 (by rfl) ⟨196829, by rfl⟩ : syracuseStep 262439 = 393659) B393659
theorem B131611 : Blo 115785 131611 := bstep (se 1 (by rfl) ⟨98708, by rfl⟩ : syracuseStep 131611 = 197417) B197417
theorem B295529 : Blo 115785 295529 := bstep (se 2 (by rfl) ⟨110823, by rfl⟩ : syracuseStep 295529 = 221647) B221647
theorem B262817 : Blo 115785 262817 := bstep (se 2 (by rfl) ⟨98556, by rfl⟩ : syracuseStep 262817 = 197113) B197113
theorem B131791 : Blo 115785 131791 := bstep (se 1 (by rfl) ⟨98843, by rfl⟩ : syracuseStep 131791 = 197687) B197687
theorem B263177 : Blo 115785 263177 := bstep (se 2 (by rfl) ⟨98691, by rfl⟩ : syracuseStep 263177 = 197383) B197383
theorem B263231 : Blo 115785 263231 := bstep (se 1 (by rfl) ⟨197423, by rfl⟩ : syracuseStep 263231 = 394847) B394847
theorem B198139 : Blo 115785 198139 := bstep (se 1 (by rfl) ⟨148604, by rfl⟩ : syracuseStep 198139 = 297209) B297209
theorem B2426375 : Blo 115785 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B198335 : Blo 115785 198335 := bstep (se 1 (by rfl) ⟨148751, by rfl⟩ : syracuseStep 198335 = 297503) B297503
theorem B132799 : Blo 115785 132799 := bstep (se 1 (by rfl) ⟨99599, by rfl⟩ : syracuseStep 132799 = 199199) B199199
theorem B427787 : Blo 115785 427787 := bstep (se 1 (by rfl) ⟨320840, by rfl⟩ : syracuseStep 427787 = 641681) B641681
theorem B296743 : Blo 115785 296743 := bstep (se 1 (by rfl) ⟨222557, by rfl⟩ : syracuseStep 296743 = 445115) B445115
theorem B1116089 : Blo 115785 1116089 := bstep (se 2 (by rfl) ⟨418533, by rfl⟩ : syracuseStep 1116089 = 837067) B837067
theorem B133087 : Blo 115785 133087 := bstep (se 1 (by rfl) ⟨99815, by rfl⟩ : syracuseStep 133087 = 199631) B199631
theorem B264167 : Blo 115785 264167 := bstep (se 1 (by rfl) ⟨198125, by rfl⟩ : syracuseStep 264167 = 396251) B396251
theorem B1148995 : Blo 115785 1148995 := bstep (se 1 (by rfl) ⟨861746, by rfl⟩ : syracuseStep 1148995 = 1723493) B1723493
theorem B1411181 : Blo 115785 1411181 := bstep (se 3 (by rfl) ⟨264596, by rfl⟩ : syracuseStep 1411181 = 529193) B529193
theorem B264347 : Blo 115785 264347 := bstep (se 1 (by rfl) ⟨198260, by rfl⟩ : syracuseStep 264347 = 396521) B396521
theorem B3180869 : Blo 115785 3180869 := bstep (se 4 (by rfl) ⟨298206, by rfl⟩ : syracuseStep 3180869 = 596413) B596413
theorem B264527 : Blo 115785 264527 := bstep (se 1 (by rfl) ⟨198395, by rfl⟩ : syracuseStep 264527 = 396791) B396791
theorem B264617 : Blo 115785 264617 := bstep (se 2 (by rfl) ⟨99231, by rfl⟩ : syracuseStep 264617 = 198463) B198463
theorem B133735 : Blo 115785 133735 := bstep (se 1 (by rfl) ⟨100301, by rfl⟩ : syracuseStep 133735 = 200603) B200603
theorem B199675 : Blo 115785 199675 := bstep (se 1 (by rfl) ⟨149756, by rfl⟩ : syracuseStep 199675 = 299513) B299513
theorem B166907 : Blo 115785 166907 := bstep (se 1 (by rfl) ⟨125180, by rfl⟩ : syracuseStep 166907 = 250361) B250361
theorem B265211 : Blo 115785 265211 := bstep (se 1 (by rfl) ⟨198908, by rfl⟩ : syracuseStep 265211 = 397817) B397817
theorem B396413 : Blo 115785 396413 := bstep (se 3 (by rfl) ⟨74327, by rfl⟩ : syracuseStep 396413 = 148655) B148655
theorem B265391 : Blo 115785 265391 := bstep (se 1 (by rfl) ⟨199043, by rfl⟩ : syracuseStep 265391 = 398087) B398087
theorem B199867 : Blo 115785 199867 := bstep (se 1 (by rfl) ⟨149900, by rfl⟩ : syracuseStep 199867 = 299801) B299801
theorem B265427 : Blo 115785 265427 := bstep (se 1 (by rfl) ⟨199070, by rfl⟩ : syracuseStep 265427 = 398141) B398141
theorem B331103 : Blo 115785 331103 := bstep (se 1 (by rfl) ⟨248327, by rfl⟩ : syracuseStep 331103 = 496655) B496655
theorem B200063 : Blo 115785 200063 := bstep (se 1 (by rfl) ⟨150047, by rfl⟩ : syracuseStep 200063 = 300095) B300095
theorem B134527 : Blo 115785 134527 := bstep (se 1 (by rfl) ⟨100895, by rfl⟩ : syracuseStep 134527 = 201791) B201791
theorem B396683 : Blo 115785 396683 := bstep (se 1 (by rfl) ⟨297512, by rfl⟩ : syracuseStep 396683 = 595025) B595025
theorem B2624993 : Blo 115785 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B265697 : Blo 115785 265697 := bstep (se 2 (by rfl) ⟨99636, by rfl⟩ : syracuseStep 265697 = 199273) B199273
theorem B855521 : Blo 115785 855521 := bstep (se 2 (by rfl) ⟨320820, by rfl⟩ : syracuseStep 855521 = 641641) B641641
theorem B921223 : Blo 115785 921223 := bstep (se 1 (by rfl) ⟨690917, by rfl⟩ : syracuseStep 921223 = 1381835) B1381835
theorem B266111 : Blo 115785 266111 := bstep (se 1 (by rfl) ⟨199583, by rfl⟩ : syracuseStep 266111 = 399167) B399167
theorem B1282031 : Blo 115785 1282031 := bstep (se 1 (by rfl) ⟨961523, by rfl⟩ : syracuseStep 1282031 = 1923047) B1923047
theorem B298991 : Blo 115785 298991 := bstep (se 1 (by rfl) ⟨224243, by rfl⟩ : syracuseStep 298991 = 448487) B448487
theorem B201001 : Blo 115785 201001 := bstep (se 2 (by rfl) ⟨75375, by rfl⟩ : syracuseStep 201001 = 150751) B150751
theorem B2232791 : Blo 115785 2232791 := bstep (se 1 (by rfl) ⟨1674593, by rfl⟩ : syracuseStep 2232791 = 3349187) B3349187
theorem B2167283 : Blo 115785 2167283 := bstep (se 1 (by rfl) ⟨1625462, by rfl⟩ : syracuseStep 2167283 = 3250925) B3250925
theorem B201271 : Blo 115785 201271 := bstep (se 1 (by rfl) ⟨150953, by rfl⟩ : syracuseStep 201271 = 301907) B301907
theorem B528977 : Blo 115785 528977 := bstep (se 2 (by rfl) ⟨198366, by rfl⟩ : syracuseStep 528977 = 396733) B396733
theorem B1512107 : Blo 115785 1512107 := bstep (se 1 (by rfl) ⟨1134080, by rfl⟩ : syracuseStep 1512107 = 2268161) B2268161
theorem B496381 : Blo 115785 496381 := bstep (se 3 (by rfl) ⟨93071, by rfl⟩ : syracuseStep 496381 = 186143) B186143
theorem B267065 : Blo 115785 267065 := bstep (se 2 (by rfl) ⟨100149, by rfl⟩ : syracuseStep 267065 = 200299) B200299
theorem B267119 : Blo 115785 267119 := bstep (se 1 (by rfl) ⟨200339, by rfl⟩ : syracuseStep 267119 = 400679) B400679
theorem B660383 : Blo 115785 660383 := bstep (se 1 (by rfl) ⟨495287, by rfl⟩ : syracuseStep 660383 = 990575) B990575
theorem B1840229 : Blo 115785 1840229 := bstep (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) B345043
theorem B267425 : Blo 115785 267425 := bstep (se 2 (by rfl) ⟨100284, by rfl⟩ : syracuseStep 267425 = 200569) B200569
theorem B267695 : Blo 115785 267695 := bstep (se 1 (by rfl) ⟨200771, by rfl⟩ : syracuseStep 267695 = 401543) B401543
theorem B169447 : Blo 115785 169447 := bstep (se 1 (by rfl) ⟨127085, by rfl⟩ : syracuseStep 169447 = 254171) B254171
theorem B235361 : Blo 115785 235361 := bstep (se 2 (by rfl) ⟨88260, by rfl⟩ : syracuseStep 235361 = 176521) B176521
theorem B595835 : Blo 115785 595835 := bstep (se 1 (by rfl) ⟨446876, by rfl⟩ : syracuseStep 595835 = 893753) B893753
theorem B1021967 : Blo 115785 1021967 := bstep (se 1 (by rfl) ⟨766475, by rfl⟩ : syracuseStep 1021967 = 1532951) B1532951
theorem B268703 : Blo 115785 268703 := bstep (se 1 (by rfl) ⟨201527, by rfl⟩ : syracuseStep 268703 = 403055) B403055
theorem B203239 : Blo 115785 203239 := bstep (se 1 (by rfl) ⟨152429, by rfl⟩ : syracuseStep 203239 = 304859) B304859
theorem B268775 : Blo 115785 268775 := bstep (se 1 (by rfl) ⟨201581, by rfl⟩ : syracuseStep 268775 = 403163) B403163
theorem B400139 : Blo 115785 400139 := bstep (se 1 (by rfl) ⟨300104, by rfl⟩ : syracuseStep 400139 = 600209) B600209
theorem B1088315 : Blo 115785 1088315 := bstep (se 1 (by rfl) ⟨816236, by rfl⟩ : syracuseStep 1088315 = 1632473) B1632473
theorem B400409 : Blo 115785 400409 := bstep (se 2 (by rfl) ⟨150153, by rfl⟩ : syracuseStep 400409 = 300307) B300307
theorem B1088579 : Blo 115785 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B302201 : Blo 115785 302201 := bstep (se 2 (by rfl) ⟨113325, by rfl⟩ : syracuseStep 302201 = 226651) B226651
theorem B499031 : Blo 115785 499031 := bstep (se 1 (by rfl) ⟨374273, by rfl⟩ : syracuseStep 499031 = 748547) B748547
theorem B3219401 : Blo 115785 3219401 := bstep (se 2 (by rfl) ⟨1207275, by rfl⟩ : syracuseStep 3219401 = 2414551) B2414551
theorem B336001 : Blo 115785 336001 := bstep (se 2 (by rfl) ⟨126000, by rfl⟩ : syracuseStep 336001 = 252001) B252001
theorem B401597 : Blo 115785 401597 := bstep (se 3 (by rfl) ⟨75299, by rfl⟩ : syracuseStep 401597 = 150599) B150599
theorem B401759 : Blo 115785 401759 := bstep (se 1 (by rfl) ⟨301319, by rfl⟩ : syracuseStep 401759 = 602639) B602639
theorem B566023 : Blo 115785 566023 := bstep (se 1 (by rfl) ⟨424517, by rfl⟩ : syracuseStep 566023 = 849035) B849035
theorem B174047 : Blo 115785 174047 := bstep (se 1 (by rfl) ⟨130535, by rfl⟩ : syracuseStep 174047 = 261071) B261071
theorem B174059 : Blo 115785 174059 := bstep (se 1 (by rfl) ⟨130544, by rfl⟩ : syracuseStep 174059 = 261089) B261089
theorem B174107 : Blo 115785 174107 := bstep (se 1 (by rfl) ⟨130580, by rfl⟩ : syracuseStep 174107 = 261161) B261161
theorem B764153 : Blo 115785 764153 := bstep (se 2 (by rfl) ⟨286557, by rfl⟩ : syracuseStep 764153 = 573115) B573115
theorem B174473 : Blo 115785 174473 := bstep (se 2 (by rfl) ⟨65427, by rfl⟩ : syracuseStep 174473 = 130855) B130855
theorem B1911559 : Blo 115785 1911559 := bstep (se 1 (by rfl) ⟨1433669, by rfl⟩ : syracuseStep 1911559 = 2867339) B2867339
theorem B863131 : Blo 115785 863131 := bstep (se 1 (by rfl) ⟨647348, by rfl⟩ : syracuseStep 863131 = 1294697) B1294697
theorem B568271 : Blo 115785 568271 := bstep (se 1 (by rfl) ⟨426203, by rfl⟩ : syracuseStep 568271 = 852407) B852407
theorem B175415 : Blo 115785 175415 := bstep (se 1 (by rfl) ⟨131561, by rfl⟩ : syracuseStep 175415 = 263123) B263123
theorem B175583 : Blo 115785 175583 := bstep (se 1 (by rfl) ⟨131687, by rfl⟩ : syracuseStep 175583 = 263375) B263375
theorem B175799 : Blo 115785 175799 := bstep (se 1 (by rfl) ⟨131849, by rfl⟩ : syracuseStep 175799 = 263699) B263699
theorem B176009 : Blo 115785 176009 := bstep (se 2 (by rfl) ⟨66003, by rfl⟩ : syracuseStep 176009 = 132007) B132007
theorem B176255 : Blo 115785 176255 := bstep (se 1 (by rfl) ⟨132191, by rfl⟩ : syracuseStep 176255 = 264383) B264383
theorem B635111 : Blo 115785 635111 := bstep (se 1 (by rfl) ⟨476333, by rfl⟩ : syracuseStep 635111 = 952667) B952667
theorem B504377 : Blo 115785 504377 := bstep (se 2 (by rfl) ⟨189141, by rfl⟩ : syracuseStep 504377 = 378283) B378283
theorem B537151 : Blo 115785 537151 := bstep (se 1 (by rfl) ⟨402863, by rfl⟩ : syracuseStep 537151 = 805727) B805727
theorem B176891 : Blo 115785 176891 := bstep (se 1 (by rfl) ⟨132668, by rfl⟩ : syracuseStep 176891 = 265337) B265337
theorem B373567 : Blo 115785 373567 := bstep (se 1 (by rfl) ⟨280175, by rfl⟩ : syracuseStep 373567 = 560351) B560351
theorem B504787 : Blo 115785 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B177335 : Blo 115785 177335 := bstep (se 1 (by rfl) ⟨133001, by rfl⟩ : syracuseStep 177335 = 266003) B266003
theorem B177575 : Blo 115785 177575 := bstep (se 1 (by rfl) ⟨133181, by rfl⟩ : syracuseStep 177575 = 266363) B266363
theorem B439739 : Blo 115785 439739 := bstep (se 1 (by rfl) ⟨329804, by rfl⟩ : syracuseStep 439739 = 659609) B659609
theorem B177755 : Blo 115785 177755 := bstep (se 1 (by rfl) ⟨133316, by rfl⟩ : syracuseStep 177755 = 266633) B266633
theorem B374387 : Blo 115785 374387 := bstep (se 1 (by rfl) ⟨280790, by rfl⟩ : syracuseStep 374387 = 561581) B561581
theorem B439951 : Blo 115785 439951 := bstep (se 1 (by rfl) ⟨329963, by rfl⟩ : syracuseStep 439951 = 659927) B659927
theorem B636797 : Blo 115785 636797 := bstep (se 3 (by rfl) ⟨119399, by rfl⟩ : syracuseStep 636797 = 238799) B238799
theorem B505865 : Blo 115785 505865 := bstep (se 2 (by rfl) ⟨189699, by rfl⟩ : syracuseStep 505865 = 379399) B379399
theorem B178217 : Blo 115785 178217 := bstep (se 2 (by rfl) ⟨66831, by rfl⟩ : syracuseStep 178217 = 133663) B133663
theorem B178247 : Blo 115785 178247 := bstep (se 1 (by rfl) ⟨133685, by rfl⟩ : syracuseStep 178247 = 267371) B267371
theorem B276671 : Blo 115785 276671 := bstep (se 1 (by rfl) ⟨207503, by rfl⟩ : syracuseStep 276671 = 415007) B415007
theorem B506087 : Blo 115785 506087 := bstep (se 1 (by rfl) ⟨379565, by rfl⟩ : syracuseStep 506087 = 759131) B759131
theorem B7649579 : Blo 115785 7649579 := bstep (se 1 (by rfl) ⟨5737184, by rfl⟩ : syracuseStep 7649579 = 11474369) B11474369
theorem B178631 : Blo 115785 178631 := bstep (se 1 (by rfl) ⟨133973, by rfl⟩ : syracuseStep 178631 = 267947) B267947
theorem B768457 : Blo 115785 768457 := bstep (se 2 (by rfl) ⟨288171, by rfl⟩ : syracuseStep 768457 = 576343) B576343
theorem B2275847 : Blo 115785 2275847 := bstep (se 1 (by rfl) ⟨1706885, by rfl⟩ : syracuseStep 2275847 = 3413771) B3413771
theorem B178847 : Blo 115785 178847 := bstep (se 1 (by rfl) ⟨134135, by rfl⟩ : syracuseStep 178847 = 268271) B268271
theorem B473771 : Blo 115785 473771 := bstep (se 1 (by rfl) ⟨355328, by rfl⟩ : syracuseStep 473771 = 710657) B710657
theorem B178991 : Blo 115785 178991 := bstep (se 1 (by rfl) ⟨134243, by rfl⟩ : syracuseStep 178991 = 268487) B268487
theorem B179111 : Blo 115785 179111 := bstep (se 1 (by rfl) ⟨134333, by rfl⟩ : syracuseStep 179111 = 268667) B268667
theorem B900071 : Blo 115785 900071 := bstep (se 1 (by rfl) ⟨675053, by rfl⟩ : syracuseStep 900071 = 1350107) B1350107
theorem B179291 : Blo 115785 179291 := bstep (se 1 (by rfl) ⟨134468, by rfl⟩ : syracuseStep 179291 = 268937) B268937
theorem B179663 : Blo 115785 179663 := bstep (se 1 (by rfl) ⟨134747, by rfl⟩ : syracuseStep 179663 = 269495) B269495
theorem B376427 : Blo 115785 376427 := bstep (se 1 (by rfl) ⟨282320, by rfl⟩ : syracuseStep 376427 = 564641) B564641
theorem B213419 : Blo 115785 213419 := bstep (se 1 (by rfl) ⟨160064, by rfl⟩ : syracuseStep 213419 = 320129) B320129
theorem B869063 : Blo 115785 869063 := bstep (se 1 (by rfl) ⟨651797, by rfl⟩ : syracuseStep 869063 = 1303595) B1303595
theorem B115823 : Blo 115785 115823 := bstep (se 1 (by rfl) ⟨86867, by rfl⟩ : syracuseStep 115823 = 173735) B173735
theorem B115879 : Blo 115785 115879 := bstep (se 1 (by rfl) ⟨86909, by rfl⟩ : syracuseStep 115879 = 173819) B173819
theorem B115903 : Blo 115785 115903 := bstep (se 1 (by rfl) ⟨86927, by rfl⟩ : syracuseStep 115903 = 173855) B173855
theorem B1623233 : Blo 115785 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B115935 : Blo 115785 115935 := bstep (se 1 (by rfl) ⟨86951, by rfl⟩ : syracuseStep 115935 = 173903) B173903
theorem B443627 : Blo 115785 443627 := bstep (se 1 (by rfl) ⟨332720, by rfl⟩ : syracuseStep 443627 = 665441) B665441
theorem B116015 : Blo 115785 116015 := bstep (se 1 (by rfl) ⟨87011, by rfl⟩ : syracuseStep 116015 = 174023) B174023
theorem B1525229 : Blo 115785 1525229 := bstep (se 3 (by rfl) ⟨285980, by rfl⟩ : syracuseStep 1525229 = 571961) B571961
theorem B116251 : Blo 115785 116251 := bstep (se 1 (by rfl) ⟨87188, by rfl⟩ : syracuseStep 116251 = 174377) B174377
theorem B116255 : Blo 115785 116255 := bstep (se 1 (by rfl) ⟨87191, by rfl⟩ : syracuseStep 116255 = 174383) B174383
theorem B509503 : Blo 115785 509503 := bstep (se 1 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 509503 = 764255) B764255
theorem B2508353 : Blo 115785 2508353 := bstep (se 2 (by rfl) ⟨940632, by rfl⟩ : syracuseStep 2508353 = 1881265) B1881265
theorem B116415 : Blo 115785 116415 := bstep (se 1 (by rfl) ⟨87311, by rfl⟩ : syracuseStep 116415 = 174623) B174623
theorem B116671 : Blo 115785 116671 := bstep (se 1 (by rfl) ⟨87503, by rfl⟩ : syracuseStep 116671 = 175007) B175007
theorem B116703 : Blo 115785 116703 := bstep (se 1 (by rfl) ⟨87527, by rfl⟩ : syracuseStep 116703 = 175055) B175055
theorem B116763 : Blo 115785 116763 := bstep (se 1 (by rfl) ⟨87572, by rfl⟩ : syracuseStep 116763 = 175145) B175145
theorem B116767 : Blo 115785 116767 := bstep (se 1 (by rfl) ⟨87575, by rfl⟩ : syracuseStep 116767 = 175151) B175151
theorem B116783 : Blo 115785 116783 := bstep (se 1 (by rfl) ⟨87587, by rfl⟩ : syracuseStep 116783 = 175175) B175175
theorem B116959 : Blo 115785 116959 := bstep (se 1 (by rfl) ⟨87719, by rfl⟩ : syracuseStep 116959 = 175439) B175439
theorem B117019 : Blo 115785 117019 := bstep (se 1 (by rfl) ⟨87764, by rfl⟩ : syracuseStep 117019 = 175529) B175529
theorem B969083 : Blo 115785 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B117119 : Blo 115785 117119 := bstep (se 1 (by rfl) ⟨87839, by rfl⟩ : syracuseStep 117119 = 175679) B175679
theorem B1329695 : Blo 115785 1329695 := bstep (se 1 (by rfl) ⟨997271, by rfl⟩ : syracuseStep 1329695 = 1994543) B1994543
theorem B117295 : Blo 115785 117295 := bstep (se 1 (by rfl) ⟨87971, by rfl⟩ : syracuseStep 117295 = 175943) B175943
theorem B117351 : Blo 115785 117351 := bstep (se 1 (by rfl) ⟨88013, by rfl⟩ : syracuseStep 117351 = 176027) B176027
theorem B379513 : Blo 115785 379513 := bstep (se 2 (by rfl) ⟨142317, by rfl⟩ : syracuseStep 379513 = 284635) B284635
theorem B117727 : Blo 115785 117727 := bstep (se 1 (by rfl) ⟨88295, by rfl⟩ : syracuseStep 117727 = 176591) B176591
theorem B117755 : Blo 115785 117755 := bstep (se 1 (by rfl) ⟨88316, by rfl⟩ : syracuseStep 117755 = 176633) B176633
theorem B117823 : Blo 115785 117823 := bstep (se 1 (by rfl) ⟨88367, by rfl⟩ : syracuseStep 117823 = 176735) B176735
theorem B674963 : Blo 115785 674963 := bstep (se 1 (by rfl) ⟨506222, by rfl⟩ : syracuseStep 674963 = 1012445) B1012445
theorem B904445 : Blo 115785 904445 := bstep (se 3 (by rfl) ⟨169583, by rfl⟩ : syracuseStep 904445 = 339167) B339167
theorem B281983 : Blo 115785 281983 := bstep (se 1 (by rfl) ⟨211487, by rfl⟩ : syracuseStep 281983 = 422975) B422975
theorem B118143 : Blo 115785 118143 := bstep (se 1 (by rfl) ⟨88607, by rfl⟩ : syracuseStep 118143 = 177215) B177215
theorem B118171 : Blo 115785 118171 := bstep (se 1 (by rfl) ⟨88628, by rfl⟩ : syracuseStep 118171 = 177257) B177257
theorem B118239 : Blo 115785 118239 := bstep (se 1 (by rfl) ⟨88679, by rfl⟩ : syracuseStep 118239 = 177359) B177359
theorem B445943 : Blo 115785 445943 := bstep (se 1 (by rfl) ⟨334457, by rfl⟩ : syracuseStep 445943 = 668915) B668915
theorem B118375 : Blo 115785 118375 := bstep (se 1 (by rfl) ⟨88781, by rfl⟩ : syracuseStep 118375 = 177563) B177563
theorem B118523 : Blo 115785 118523 := bstep (se 1 (by rfl) ⟨88892, by rfl⟩ : syracuseStep 118523 = 177785) B177785
theorem B118591 : Blo 115785 118591 := bstep (se 1 (by rfl) ⟨88943, by rfl⟩ : syracuseStep 118591 = 177887) B177887
theorem B380743 : Blo 115785 380743 := bstep (se 1 (by rfl) ⟨285557, by rfl⟩ : syracuseStep 380743 = 571115) B571115
theorem B118655 : Blo 115785 118655 := bstep (se 1 (by rfl) ⟨88991, by rfl⟩ : syracuseStep 118655 = 177983) B177983
theorem B282599 : Blo 115785 282599 := bstep (se 1 (by rfl) ⟨211949, by rfl⟩ : syracuseStep 282599 = 423899) B423899
theorem B118767 : Blo 115785 118767 := bstep (se 1 (by rfl) ⟨89075, by rfl⟩ : syracuseStep 118767 = 178151) B178151
theorem B118779 : Blo 115785 118779 := bstep (se 1 (by rfl) ⟨89084, by rfl⟩ : syracuseStep 118779 = 178169) B178169
theorem B118847 : Blo 115785 118847 := bstep (se 1 (by rfl) ⟨89135, by rfl⟩ : syracuseStep 118847 = 178271) B178271
theorem B118887 : Blo 115785 118887 := bstep (se 1 (by rfl) ⟨89165, by rfl⟩ : syracuseStep 118887 = 178331) B178331
theorem B118911 : Blo 115785 118911 := bstep (se 1 (by rfl) ⟨89183, by rfl⟩ : syracuseStep 118911 = 178367) B178367
theorem B118939 : Blo 115785 118939 := bstep (se 1 (by rfl) ⟨89204, by rfl⟩ : syracuseStep 118939 = 178409) B178409
theorem B119143 : Blo 115785 119143 := bstep (se 1 (by rfl) ⟨89357, by rfl⟩ : syracuseStep 119143 = 178715) B178715
theorem B8606087 : Blo 115785 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B119195 : Blo 115785 119195 := bstep (se 1 (by rfl) ⟨89396, by rfl⟩ : syracuseStep 119195 = 178793) B178793
theorem B479675 : Blo 115785 479675 := bstep (se 1 (by rfl) ⟨359756, by rfl⟩ : syracuseStep 479675 = 719513) B719513
theorem B119547 : Blo 115785 119547 := bstep (se 1 (by rfl) ⟨89660, by rfl⟩ : syracuseStep 119547 = 179321) B179321
theorem B119615 : Blo 115785 119615 := bstep (se 1 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 119615 = 179423) B179423
theorem B119643 : Blo 115785 119643 := bstep (se 1 (by rfl) ⟨89732, by rfl⟩ : syracuseStep 119643 = 179465) B179465
theorem B119711 : Blo 115785 119711 := bstep (se 1 (by rfl) ⟨89783, by rfl⟩ : syracuseStep 119711 = 179567) B179567
theorem B2151461 : Blo 115785 2151461 := bstep (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) B403399
theorem B316669 : Blo 115785 316669 := bstep (se 3 (by rfl) ⟨59375, by rfl⟩ : syracuseStep 316669 = 118751) B118751
theorem B7296551 : Blo 115785 7296551 := bstep (se 1 (by rfl) ⟨5472413, by rfl⟩ : syracuseStep 7296551 = 10944827) B10944827
theorem B251471 : Blo 115785 251471 := bstep (se 1 (by rfl) ⟨188603, by rfl⟩ : syracuseStep 251471 = 377207) B377207
theorem B153415 : Blo 115785 153415 := bstep (se 1 (by rfl) ⟨115061, by rfl⟩ : syracuseStep 153415 = 230123) B230123
theorem B907361 : Blo 115785 907361 := bstep (se 2 (by rfl) ⟨340260, by rfl⟩ : syracuseStep 907361 = 680521) B680521
theorem B841913 : Blo 115785 841913 := bstep (se 2 (by rfl) ⟨315717, by rfl⟩ : syracuseStep 841913 = 631435) B631435
theorem B2087279 : Blo 115785 2087279 := bstep (se 1 (by rfl) ⟨1565459, by rfl⟩ : syracuseStep 2087279 = 3130919) B3130919
theorem B1924013 : Blo 115785 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B221039 : Blo 115785 221039 := bstep (se 1 (by rfl) ⟨165779, by rfl⟩ : syracuseStep 221039 = 331559) B331559
theorem B122735 : Blo 115785 122735 := bstep (se 1 (by rfl) ⟨92051, by rfl⟩ : syracuseStep 122735 = 184103) B184103
theorem B385337 : Blo 115785 385337 := bstep (se 2 (by rfl) ⟨144501, by rfl⟩ : syracuseStep 385337 = 289003) B289003
theorem B714041 : Blo 115785 714041 := bstep (se 2 (by rfl) ⟨267765, by rfl⟩ : syracuseStep 714041 = 535531) B535531
theorem B452087 : Blo 115785 452087 := bstep (se 1 (by rfl) ⟨339065, by rfl⟩ : syracuseStep 452087 = 678131) B678131
theorem B353819 : Blo 115785 353819 := bstep (se 1 (by rfl) ⟨265364, by rfl⟩ : syracuseStep 353819 = 530729) B530729
theorem B1336985 : Blo 115785 1336985 := bstep (se 2 (by rfl) ⟨501369, by rfl⟩ : syracuseStep 1336985 = 1002739) B1002739
theorem B223211 : Blo 115785 223211 := bstep (se 1 (by rfl) ⟨167408, by rfl⟩ : syracuseStep 223211 = 334817) B334817
theorem B452587 : Blo 115785 452587 := bstep (se 1 (by rfl) ⟨339440, by rfl⟩ : syracuseStep 452587 = 678881) B678881
theorem B6547877 : Blo 115785 6547877 := bstep (se 4 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 6547877 = 1227727) B1227727
theorem B223735 : Blo 115785 223735 := bstep (se 1 (by rfl) ⟨167801, by rfl⟩ : syracuseStep 223735 = 335603) B335603
theorem B224327 : Blo 115785 224327 := bstep (se 1 (by rfl) ⟨168245, by rfl⟩ : syracuseStep 224327 = 336491) B336491
theorem B1895993 : Blo 115785 1895993 := bstep (se 2 (by rfl) ⟨710997, by rfl⟩ : syracuseStep 1895993 = 1421995) B1421995
theorem B454319 : Blo 115785 454319 := bstep (se 1 (by rfl) ⟨340739, by rfl⟩ : syracuseStep 454319 = 681479) B681479
theorem B2748809 : Blo 115785 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B1864225 : Blo 115785 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B226567 : Blo 115785 226567 := bstep (se 1 (by rfl) ⟨169925, by rfl⟩ : syracuseStep 226567 = 339851) B339851
theorem B588221 : Blo 115785 588221 := bstep (se 3 (by rfl) ⟨110291, by rfl⟩ : syracuseStep 588221 = 220583) B220583
theorem B260639 : Blo 115785 260639 := bstep (se 1 (by rfl) ⟨195479, by rfl⟩ : syracuseStep 260639 = 390959) B390959
theorem B260873 : Blo 115785 260873 := bstep (se 2 (by rfl) ⟨97827, by rfl⟩ : syracuseStep 260873 = 195655) B195655
theorem B752465 : Blo 115785 752465 := bstep (se 2 (by rfl) ⟨282174, by rfl⟩ : syracuseStep 752465 = 564349) B564349
theorem B392093 : Blo 115785 392093 := bstep (se 3 (by rfl) ⟨73517, by rfl⟩ : syracuseStep 392093 = 147035) B147035
theorem B195689 : Blo 115785 195689 := bstep (se 2 (by rfl) ⟨73383, by rfl⟩ : syracuseStep 195689 = 146767) B146767
theorem B130279 : Blo 115785 130279 := bstep (se 1 (by rfl) ⟨97709, by rfl⟩ : syracuseStep 130279 = 195419) B195419
theorem B261449 : Blo 115785 261449 := bstep (se 2 (by rfl) ⟨98043, by rfl⟩ : syracuseStep 261449 = 196087) B196087
theorem B1342817 : Blo 115785 1342817 := bstep (se 2 (by rfl) ⟨503556, by rfl⟩ : syracuseStep 1342817 = 1007113) B1007113
theorem B261863 : Blo 115785 261863 := bstep (se 1 (by rfl) ⟨196397, by rfl⟩ : syracuseStep 261863 = 392795) B392795
theorem B884519 : Blo 115785 884519 := bstep (se 1 (by rfl) ⟨663389, by rfl⟩ : syracuseStep 884519 = 1326779) B1326779
theorem B130927 : Blo 115785 130927 := bstep (se 1 (by rfl) ⟨98195, by rfl⟩ : syracuseStep 130927 = 196391) B196391
theorem B294799 : Blo 115785 294799 := bstep (se 1 (by rfl) ⟨221099, by rfl⟩ : syracuseStep 294799 = 442199) B442199
theorem B196519 : Blo 115785 196519 := bstep (se 1 (by rfl) ⟨147389, by rfl⟩ : syracuseStep 196519 = 294779) B294779
theorem B262457 : Blo 115785 262457 := bstep (se 2 (by rfl) ⟨98421, by rfl⟩ : syracuseStep 262457 = 196843) B196843
theorem B1082155 : Blo 115785 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B295751 : Blo 115785 295751 := bstep (se 1 (by rfl) ⟨221813, by rfl⟩ : syracuseStep 295751 = 443627) B443627
theorem B1016819 : Blo 115785 1016819 := bstep (se 1 (by rfl) ⟨762614, by rfl⟩ : syracuseStep 1016819 = 1525229) B1525229
theorem B754697 : Blo 115785 754697 := bstep (se 2 (by rfl) ⟨283011, by rfl⟩ : syracuseStep 754697 = 566023) B566023
theorem B1672235 : Blo 115785 1672235 := bstep (se 1 (by rfl) ⟨1254176, by rfl⟩ : syracuseStep 1672235 = 2508353) B2508353
theorem B132223 : Blo 115785 132223 := bstep (se 1 (by rfl) ⟨99167, by rfl⟩ : syracuseStep 132223 = 198335) B198335
theorem B1410605 : Blo 115785 1410605 := bstep (se 3 (by rfl) ⟨264488, by rfl⟩ : syracuseStep 1410605 = 528977) B528977
theorem B788077 : Blo 115785 788077 := bstep (se 3 (by rfl) ⟨147764, by rfl⟩ : syracuseStep 788077 = 295529) B295529
theorem B886463 : Blo 115785 886463 := bstep (se 1 (by rfl) ⟨664847, by rfl⟩ : syracuseStep 886463 = 1329695) B1329695
theorem B264185 : Blo 115785 264185 := bstep (se 2 (by rfl) ⟨99069, by rfl⟩ : syracuseStep 264185 = 198139) B198139
theorem B264275 : Blo 115785 264275 := bstep (se 1 (by rfl) ⟨198206, by rfl⟩ : syracuseStep 264275 = 396413) B396413
theorem B133375 : Blo 115785 133375 := bstep (se 1 (by rfl) ⟨100031, by rfl⟩ : syracuseStep 133375 = 200063) B200063
theorem B264455 : Blo 115785 264455 := bstep (se 1 (by rfl) ⟨198341, by rfl⟩ : syracuseStep 264455 = 396683) B396683
theorem B395657 : Blo 115785 395657 := bstep (se 2 (by rfl) ⟨148371, by rfl⟩ : syracuseStep 395657 = 296743) B296743
theorem B1083941 : Blo 115785 1083941 := bstep (se 4 (by rfl) ⟨101619, by rfl⟩ : syracuseStep 1083941 = 203239) B203239
theorem B854687 : Blo 115785 854687 := bstep (se 1 (by rfl) ⟨641015, by rfl⟩ : syracuseStep 854687 = 1282031) B1282031
theorem B199327 : Blo 115785 199327 := bstep (se 1 (by rfl) ⟨149495, by rfl⟩ : syracuseStep 199327 = 298991) B298991
theorem B5737391 : Blo 115785 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B298313 : Blo 115785 298313 := bstep (se 2 (by rfl) ⟨111867, by rfl⟩ : syracuseStep 298313 = 223735) B223735
theorem B1150841 : Blo 115785 1150841 := bstep (se 2 (by rfl) ⟨431565, by rfl⟩ : syracuseStep 1150841 = 863131) B863131
theorem B397223 : Blo 115785 397223 := bstep (se 1 (by rfl) ⟨297917, by rfl⟩ : syracuseStep 397223 = 595835) B595835
theorem B561275 : Blo 115785 561275 := bstep (se 1 (by rfl) ⟨420956, by rfl⟩ : syracuseStep 561275 = 841913) B841913
theorem B266489 : Blo 115785 266489 := bstep (se 2 (by rfl) ⟨99933, by rfl⟩ : syracuseStep 266489 = 199867) B199867
theorem B266759 : Blo 115785 266759 := bstep (se 1 (by rfl) ⟨200069, by rfl⟩ : syracuseStep 266759 = 400139) B400139
theorem B725543 : Blo 115785 725543 := bstep (se 1 (by rfl) ⟨544157, by rfl⟩ : syracuseStep 725543 = 1088315) B1088315
theorem B266939 : Blo 115785 266939 := bstep (se 1 (by rfl) ⟨200204, by rfl⟩ : syracuseStep 266939 = 400409) B400409
theorem B725719 : Blo 115785 725719 := bstep (se 1 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 725719 = 1088579) B1088579
theorem B201467 : Blo 115785 201467 := bstep (se 1 (by rfl) ⟨151100, by rfl⟩ : syracuseStep 201467 = 302201) B302201
theorem B332687 : Blo 115785 332687 := bstep (se 1 (by rfl) ⟨249515, by rfl⟩ : syracuseStep 332687 = 499031) B499031
theorem B267731 : Blo 115785 267731 := bstep (se 1 (by rfl) ⟨200798, by rfl⟩ : syracuseStep 267731 = 401597) B401597
theorem B267839 : Blo 115785 267839 := bstep (se 1 (by rfl) ⟨200879, by rfl⟩ : syracuseStep 267839 = 401759) B401759
theorem B268001 : Blo 115785 268001 := bstep (se 2 (by rfl) ⟨100500, by rfl⟩ : syracuseStep 268001 = 201001) B201001
theorem B268361 : Blo 115785 268361 := bstep (se 2 (by rfl) ⟨100635, by rfl⟩ : syracuseStep 268361 = 201271) B201271
theorem B301391 : Blo 115785 301391 := bstep (se 1 (by rfl) ⟨226043, by rfl⟩ : syracuseStep 301391 = 452087) B452087
theorem B661841 : Blo 115785 661841 := bstep (se 2 (by rfl) ⟨248190, by rfl⟩ : syracuseStep 661841 = 496381) B496381
theorem B235879 : Blo 115785 235879 := bstep (se 1 (by rfl) ⟨176909, by rfl⟩ : syracuseStep 235879 = 353819) B353819
theorem B498089 : Blo 115785 498089 := bstep (se 2 (by rfl) ⟨186783, by rfl⟩ : syracuseStep 498089 = 373567) B373567
theorem B891323 : Blo 115785 891323 := bstep (se 1 (by rfl) ⟨668492, by rfl⟩ : syracuseStep 891323 = 1336985) B1336985
theorem B4365251 : Blo 115785 4365251 := bstep (se 1 (by rfl) ⟨3273938, by rfl⟩ : syracuseStep 4365251 = 6547877) B6547877
theorem B302089 : Blo 115785 302089 := bstep (se 2 (by rfl) ⟨113283, by rfl⟩ : syracuseStep 302089 = 226567) B226567
theorem B204553 : Blo 115785 204553 := bstep (se 2 (by rfl) ⟨76707, by rfl⟩ : syracuseStep 204553 = 153415) B153415
theorem B302879 : Blo 115785 302879 := bstep (se 1 (by rfl) ⟨227159, by rfl⟩ : syracuseStep 302879 = 454319) B454319
theorem B598205 : Blo 115785 598205 := bstep (se 3 (by rfl) ⟨112163, by rfl⟩ : syracuseStep 598205 = 224327) B224327
theorem B336251 : Blo 115785 336251 := bstep (se 1 (by rfl) ⟨252188, by rfl⟩ : syracuseStep 336251 = 504377) B504377
theorem B1024609 : Blo 115785 1024609 := bstep (se 2 (by rfl) ⟨384228, by rfl⟩ : syracuseStep 1024609 = 768457) B768457
theorem B1189181 : Blo 115785 1189181 := bstep (se 3 (by rfl) ⟨222971, by rfl⟩ : syracuseStep 1189181 = 445943) B445943
theorem B337243 : Blo 115785 337243 := bstep (se 1 (by rfl) ⟨252932, by rfl⟩ : syracuseStep 337243 = 505865) B505865
theorem B337391 : Blo 115785 337391 := bstep (se 1 (by rfl) ⟨253043, by rfl⟩ : syracuseStep 337391 = 506087) B506087
theorem B173705 : Blo 115785 173705 := bstep (se 2 (by rfl) ⟨65139, by rfl⟩ : syracuseStep 173705 = 130279) B130279
theorem B1517231 : Blo 115785 1517231 := bstep (se 1 (by rfl) ⟨1137923, by rfl⟩ : syracuseStep 1517231 = 2275847) B2275847
theorem B173759 : Blo 115785 173759 := bstep (se 1 (by rfl) ⟨130319, by rfl⟩ : syracuseStep 173759 = 260639) B260639
theorem B173915 : Blo 115785 173915 := bstep (se 1 (by rfl) ⟨130436, by rfl⟩ : syracuseStep 173915 = 260873) B260873
theorem B501643 : Blo 115785 501643 := bstep (se 1 (by rfl) ⟨376232, by rfl⟩ : syracuseStep 501643 = 752465) B752465
theorem B600047 : Blo 115785 600047 := bstep (se 1 (by rfl) ⟨450035, by rfl⟩ : syracuseStep 600047 = 900071) B900071
theorem B174299 : Blo 115785 174299 := bstep (se 1 (by rfl) ⟨130724, by rfl⟩ : syracuseStep 174299 = 261449) B261449
theorem B895211 : Blo 115785 895211 := bstep (se 1 (by rfl) ⟨671408, by rfl⟩ : syracuseStep 895211 = 1342817) B1342817
theorem B174569 : Blo 115785 174569 := bstep (se 2 (by rfl) ⟨65463, by rfl⟩ : syracuseStep 174569 = 130927) B130927
theorem B174575 : Blo 115785 174575 := bstep (se 1 (by rfl) ⟨130931, by rfl⟩ : syracuseStep 174575 = 261863) B261863
theorem B174887 : Blo 115785 174887 := bstep (se 1 (by rfl) ⟨131165, by rfl⟩ : syracuseStep 174887 = 262331) B262331
theorem B174959 : Blo 115785 174959 := bstep (se 1 (by rfl) ⟨131219, by rfl⟩ : syracuseStep 174959 = 262439) B262439
theorem B142279 : Blo 115785 142279 := bstep (se 1 (by rfl) ⟨106709, by rfl⟩ : syracuseStep 142279 = 213419) B213419
theorem B175211 : Blo 115785 175211 := bstep (se 1 (by rfl) ⟨131408, by rfl⟩ : syracuseStep 175211 = 262817) B262817
theorem B175451 : Blo 115785 175451 := bstep (se 1 (by rfl) ⟨131588, by rfl⟩ : syracuseStep 175451 = 263177) B263177
theorem B175481 : Blo 115785 175481 := bstep (se 2 (by rfl) ⟨65805, by rfl⟩ : syracuseStep 175481 = 131611) B131611
theorem B175487 : Blo 115785 175487 := bstep (se 1 (by rfl) ⟨131615, by rfl⟩ : syracuseStep 175487 = 263231) B263231
theorem B175721 : Blo 115785 175721 := bstep (se 2 (by rfl) ⟨65895, by rfl⟩ : syracuseStep 175721 = 131791) B131791
theorem B1617583 : Blo 115785 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B5779421 : Blo 115785 5779421 := bstep (se 3 (by rfl) ⟨1083641, by rfl⟩ : syracuseStep 5779421 = 2167283) B2167283
theorem B176111 : Blo 115785 176111 := bstep (se 1 (by rfl) ⟨132083, by rfl⟩ : syracuseStep 176111 = 264167) B264167
theorem B176231 : Blo 115785 176231 := bstep (se 1 (by rfl) ⟨132173, by rfl⟩ : syracuseStep 176231 = 264347) B264347
theorem B176351 : Blo 115785 176351 := bstep (se 1 (by rfl) ⟨132263, by rfl⟩ : syracuseStep 176351 = 264527) B264527
theorem B176411 : Blo 115785 176411 := bstep (se 1 (by rfl) ⟨132308, by rfl⟩ : syracuseStep 176411 = 264617) B264617
theorem B176807 : Blo 115785 176807 := bstep (se 1 (by rfl) ⟨132605, by rfl⟩ : syracuseStep 176807 = 265211) B265211
theorem B176927 : Blo 115785 176927 := bstep (se 1 (by rfl) ⟨132695, by rfl⟩ : syracuseStep 176927 = 265391) B265391
theorem B176951 : Blo 115785 176951 := bstep (se 1 (by rfl) ⟨132713, by rfl⟩ : syracuseStep 176951 = 265427) B265427
theorem B602963 : Blo 115785 602963 := bstep (se 1 (by rfl) ⟨452222, by rfl⟩ : syracuseStep 602963 = 904445) B904445
theorem B177065 : Blo 115785 177065 := bstep (se 2 (by rfl) ⟨66399, by rfl⟩ : syracuseStep 177065 = 132799) B132799
theorem B1749995 : Blo 115785 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B177131 : Blo 115785 177131 := bstep (se 1 (by rfl) ⟨132848, by rfl⟩ : syracuseStep 177131 = 265697) B265697
theorem B570347 : Blo 115785 570347 := bstep (se 1 (by rfl) ⟨427760, by rfl⟩ : syracuseStep 570347 = 855521) B855521
theorem B177407 : Blo 115785 177407 := bstep (se 1 (by rfl) ⟨133055, by rfl⟩ : syracuseStep 177407 = 266111) B266111
theorem B177449 : Blo 115785 177449 := bstep (se 2 (by rfl) ⟨66543, by rfl⟩ : syracuseStep 177449 = 133087) B133087
theorem B603449 : Blo 115785 603449 := bstep (se 2 (by rfl) ⟨226293, by rfl⟩ : syracuseStep 603449 = 452587) B452587
theorem B1488527 : Blo 115785 1488527 := bstep (se 1 (by rfl) ⟨1116395, by rfl⟩ : syracuseStep 1488527 = 2232791) B2232791
theorem B178043 : Blo 115785 178043 := bstep (se 1 (by rfl) ⟨133532, by rfl⟩ : syracuseStep 178043 = 267065) B267065
theorem B178079 : Blo 115785 178079 := bstep (se 1 (by rfl) ⟨133559, by rfl⟩ : syracuseStep 178079 = 267119) B267119
theorem B440255 : Blo 115785 440255 := bstep (se 1 (by rfl) ⟨330191, by rfl⟩ : syracuseStep 440255 = 660383) B660383
theorem B1226819 : Blo 115785 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B178283 : Blo 115785 178283 := bstep (se 1 (by rfl) ⟨133712, by rfl⟩ : syracuseStep 178283 = 267425) B267425
theorem B178313 : Blo 115785 178313 := bstep (se 2 (by rfl) ⟨66867, by rfl⟩ : syracuseStep 178313 = 133735) B133735
theorem B506017 : Blo 115785 506017 := bstep (se 2 (by rfl) ⟨189756, by rfl⟩ : syracuseStep 506017 = 379513) B379513
theorem B178463 : Blo 115785 178463 := bstep (se 1 (by rfl) ⟨133847, by rfl⟩ : syracuseStep 178463 = 267695) B267695
theorem B4864367 : Blo 115785 4864367 := bstep (se 1 (by rfl) ⟨3648275, by rfl⟩ : syracuseStep 4864367 = 7296551) B7296551
theorem B604907 : Blo 115785 604907 := bstep (se 1 (by rfl) ⟨453680, by rfl⟩ : syracuseStep 604907 = 907361) B907361
theorem B670589 : Blo 115785 670589 := bstep (se 3 (by rfl) ⟨125735, by rfl⟩ : syracuseStep 670589 = 251471) B251471
theorem B1391519 : Blo 115785 1391519 := bstep (se 1 (by rfl) ⟨1043639, by rfl⟩ : syracuseStep 1391519 = 2087279) B2087279
theorem B179135 : Blo 115785 179135 := bstep (se 1 (by rfl) ⟨134351, by rfl⟩ : syracuseStep 179135 = 268703) B268703
theorem B998365 : Blo 115785 998365 := bstep (se 3 (by rfl) ⟨187193, by rfl⟩ : syracuseStep 998365 = 374387) B374387
theorem B179183 : Blo 115785 179183 := bstep (se 1 (by rfl) ⟨134387, by rfl⟩ : syracuseStep 179183 = 268775) B268775
theorem B375977 : Blo 115785 375977 := bstep (se 2 (by rfl) ⟨140991, by rfl⟩ : syracuseStep 375977 = 281983) B281983
theorem B179369 : Blo 115785 179369 := bstep (se 2 (by rfl) ⟨67263, by rfl⟩ : syracuseStep 179369 = 134527) B134527
theorem B1228297 : Blo 115785 1228297 := bstep (se 2 (by rfl) ⟨460611, by rfl⟩ : syracuseStep 1228297 = 921223) B921223
theorem B147359 : Blo 115785 147359 := bstep (se 1 (by rfl) ⟨110519, by rfl⟩ : syracuseStep 147359 = 221039) B221039
theorem B2146267 : Blo 115785 2146267 := bstep (se 1 (by rfl) ⟨1609700, by rfl⟩ : syracuseStep 2146267 = 3219401) B3219401
theorem B1064933 : Blo 115785 1064933 := bstep (se 4 (by rfl) ⟨99837, by rfl⟩ : syracuseStep 1064933 = 199675) B199675
theorem B476027 : Blo 115785 476027 := bstep (se 1 (by rfl) ⟨357020, by rfl⟩ : syracuseStep 476027 = 714041) B714041
theorem B673049 : Blo 115785 673049 := bstep (se 2 (by rfl) ⟨252393, by rfl⟩ : syracuseStep 673049 = 504787) B504787
theorem B116031 : Blo 115785 116031 := bstep (se 1 (by rfl) ⟨87023, by rfl⟩ : syracuseStep 116031 = 174047) B174047
theorem B116039 : Blo 115785 116039 := bstep (se 1 (by rfl) ⟨87029, by rfl⟩ : syracuseStep 116039 = 174059) B174059
theorem B148807 : Blo 115785 148807 := bstep (se 1 (by rfl) ⟨111605, by rfl⟩ : syracuseStep 148807 = 223211) B223211
theorem B116071 : Blo 115785 116071 := bstep (se 1 (by rfl) ⟨87053, by rfl⟩ : syracuseStep 116071 = 174107) B174107
theorem B509435 : Blo 115785 509435 := bstep (se 1 (by rfl) ⟨382076, by rfl⟩ : syracuseStep 509435 = 764153) B764153
theorem B116315 : Blo 115785 116315 := bstep (se 1 (by rfl) ⟨87236, by rfl⟩ : syracuseStep 116315 = 174473) B174473
theorem B378847 : Blo 115785 378847 := bstep (se 1 (by rfl) ⟨284135, by rfl⟩ : syracuseStep 378847 = 568271) B568271
theorem B116943 : Blo 115785 116943 := bstep (se 1 (by rfl) ⟨87707, by rfl⟩ : syracuseStep 116943 = 175415) B175415
theorem B117055 : Blo 115785 117055 := bstep (se 1 (by rfl) ⟨87791, by rfl⟩ : syracuseStep 117055 = 175583) B175583
theorem B1263995 : Blo 115785 1263995 := bstep (se 1 (by rfl) ⟨947996, by rfl⟩ : syracuseStep 1263995 = 1895993) B1895993
theorem B5130701 : Blo 115785 5130701 := bstep (se 3 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 5130701 = 1924013) B1924013
theorem B117199 : Blo 115785 117199 := bstep (se 1 (by rfl) ⟨87899, by rfl⟩ : syracuseStep 117199 = 175799) B175799
theorem B117339 : Blo 115785 117339 := bstep (se 1 (by rfl) ⟨88004, by rfl⟩ : syracuseStep 117339 = 176009) B176009
theorem B445085 : Blo 115785 445085 := bstep (se 3 (by rfl) ⟨83453, by rfl⟩ : syracuseStep 445085 = 166907) B166907
theorem B117503 : Blo 115785 117503 := bstep (se 1 (by rfl) ⟨88127, by rfl⟩ : syracuseStep 117503 = 176255) B176255
theorem B117927 : Blo 115785 117927 := bstep (se 1 (by rfl) ⟨88445, by rfl⟩ : syracuseStep 117927 = 176891) B176891
theorem B118223 : Blo 115785 118223 := bstep (se 1 (by rfl) ⟨88667, by rfl⟩ : syracuseStep 118223 = 177335) B177335
theorem B118383 : Blo 115785 118383 := bstep (se 1 (by rfl) ⟨88787, by rfl⟩ : syracuseStep 118383 = 177575) B177575
theorem B118503 : Blo 115785 118503 := bstep (se 1 (by rfl) ⟨88877, by rfl⟩ : syracuseStep 118503 = 177755) B177755
theorem B118811 : Blo 115785 118811 := bstep (se 1 (by rfl) ⟨89108, by rfl⟩ : syracuseStep 118811 = 178217) B178217
theorem B118831 : Blo 115785 118831 := bstep (se 1 (by rfl) ⟨89123, by rfl⟩ : syracuseStep 118831 = 178247) B178247
theorem B184447 : Blo 115785 184447 := bstep (se 1 (by rfl) ⟨138335, by rfl⟩ : syracuseStep 184447 = 276671) B276671
theorem B5099719 : Blo 115785 5099719 := bstep (se 1 (by rfl) ⟨3824789, by rfl⟩ : syracuseStep 5099719 = 7649579) B7649579
theorem B119087 : Blo 115785 119087 := bstep (se 1 (by rfl) ⟨89315, by rfl⟩ : syracuseStep 119087 = 178631) B178631
theorem B119231 : Blo 115785 119231 := bstep (se 1 (by rfl) ⟨89423, by rfl⟩ : syracuseStep 119231 = 178847) B178847
theorem B315847 : Blo 115785 315847 := bstep (se 1 (by rfl) ⟨236885, by rfl⟩ : syracuseStep 315847 = 473771) B473771
theorem B119327 : Blo 115785 119327 := bstep (se 1 (by rfl) ⟨89495, by rfl⟩ : syracuseStep 119327 = 178991) B178991
theorem B119407 : Blo 115785 119407 := bstep (se 1 (by rfl) ⟨89555, by rfl⟩ : syracuseStep 119407 = 179111) B179111
theorem B119527 : Blo 115785 119527 := bstep (se 1 (by rfl) ⟨89645, by rfl⟩ : syracuseStep 119527 = 179291) B179291
theorem B119775 : Blo 115785 119775 := bstep (se 1 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 119775 = 179663) B179663
theorem B250951 : Blo 115785 250951 := bstep (se 1 (by rfl) ⟨188213, by rfl⟩ : syracuseStep 250951 = 376427) B376427
theorem B448001 : Blo 115785 448001 := bstep (se 2 (by rfl) ⟨168000, by rfl⟩ : syracuseStep 448001 = 336001) B336001
theorem B285191 : Blo 115785 285191 := bstep (se 1 (by rfl) ⟨213893, by rfl⟩ : syracuseStep 285191 = 427787) B427787
theorem B744059 : Blo 115785 744059 := bstep (se 1 (by rfl) ⟨558044, by rfl⟩ : syracuseStep 744059 = 1116089) B1116089
theorem B940787 : Blo 115785 940787 := bstep (se 1 (by rfl) ⟨705590, by rfl⟩ : syracuseStep 940787 = 1411181) B1411181
theorem B2120579 : Blo 115785 2120579 := bstep (se 1 (by rfl) ⟨1590434, by rfl⟩ : syracuseStep 2120579 = 3180869) B3180869
theorem B646055 : Blo 115785 646055 := bstep (se 1 (by rfl) ⟨484541, by rfl⟩ : syracuseStep 646055 = 969083) B969083
theorem B2317501 : Blo 115785 2317501 := bstep (se 3 (by rfl) ⟨434531, by rfl⟩ : syracuseStep 2317501 = 869063) B869063
theorem B679337 : Blo 115785 679337 := bstep (se 2 (by rfl) ⟨254751, by rfl⟩ : syracuseStep 679337 = 509503) B509503
theorem B449975 : Blo 115785 449975 := bstep (se 1 (by rfl) ⟨337481, by rfl⟩ : syracuseStep 449975 = 674963) B674963
theorem B220735 : Blo 115785 220735 := bstep (se 1 (by rfl) ⟨165551, by rfl⟩ : syracuseStep 220735 = 331103) B331103
theorem B188399 : Blo 115785 188399 := bstep (se 1 (by rfl) ⟨141299, by rfl⟩ : syracuseStep 188399 = 282599) B282599
theorem B1531993 : Blo 115785 1531993 := bstep (se 2 (by rfl) ⟨574497, by rfl⟩ : syracuseStep 1531993 = 1148995) B1148995
theorem B319783 : Blo 115785 319783 := bstep (se 1 (by rfl) ⟨239837, by rfl⟩ : syracuseStep 319783 = 479675) B479675
theorem B1008071 : Blo 115785 1008071 := bstep (se 1 (by rfl) ⟨756053, by rfl⟩ : syracuseStep 1008071 = 1512107) B1512107
theorem B1434307 : Blo 115785 1434307 := bstep (se 1 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 1434307 = 2151461) B2151461
theorem B2548745 : Blo 115785 2548745 := bstep (se 2 (by rfl) ⟨955779, by rfl⟩ : syracuseStep 2548745 = 1911559) B1911559
theorem B156907 : Blo 115785 156907 := bstep (se 1 (by rfl) ⟨117680, by rfl⟩ : syracuseStep 156907 = 235361) B235361
theorem B681311 : Blo 115785 681311 := bstep (se 1 (by rfl) ⟨510983, by rfl⟩ : syracuseStep 681311 = 1021967) B1021967
theorem B256891 : Blo 115785 256891 := bstep (se 1 (by rfl) ⟨192668, by rfl⟩ : syracuseStep 256891 = 385337) B385337
theorem B2485633 : Blo 115785 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B716201 : Blo 115785 716201 := bstep (se 2 (by rfl) ⟨268575, by rfl⟩ : syracuseStep 716201 = 537151) B537151
theorem B422225 : Blo 115785 422225 := bstep (se 2 (by rfl) ⟨158334, by rfl⟩ : syracuseStep 422225 = 316669) B316669
theorem B225929 : Blo 115785 225929 := bstep (se 2 (by rfl) ⟨84723, by rfl⟩ : syracuseStep 225929 = 169447) B169447
theorem B586601 : Blo 115785 586601 := bstep (se 2 (by rfl) ⟨219975, by rfl⟩ : syracuseStep 586601 = 439951) B439951
theorem B423407 : Blo 115785 423407 := bstep (se 1 (by rfl) ⟨317555, by rfl⟩ : syracuseStep 423407 = 635111) B635111
theorem B1832539 : Blo 115785 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B293159 : Blo 115785 293159 := bstep (se 1 (by rfl) ⟨219869, by rfl⟩ : syracuseStep 293159 = 439739) B439739
theorem B424531 : Blo 115785 424531 := bstep (se 1 (by rfl) ⟨318398, by rfl⟩ : syracuseStep 424531 = 636797) B636797
theorem B392147 : Blo 115785 392147 := bstep (se 1 (by rfl) ⟨294110, by rfl⟩ : syracuseStep 392147 = 588221) B588221
theorem B2030629 : Blo 115785 2030629 := bstep (se 4 (by rfl) ⟨190371, by rfl⟩ : syracuseStep 2030629 = 380743) B380743
theorem B261395 : Blo 115785 261395 := bstep (se 1 (by rfl) ⟨196046, by rfl⟩ : syracuseStep 261395 = 392093) B392093
theorem B130459 : Blo 115785 130459 := bstep (se 1 (by rfl) ⟨97844, by rfl⟩ : syracuseStep 130459 = 195689) B195689
theorem B327293 : Blo 115785 327293 := bstep (se 3 (by rfl) ⟨61367, by rfl⟩ : syracuseStep 327293 = 122735) B122735
theorem B393065 : Blo 115785 393065 := bstep (se 2 (by rfl) ⟨147399, by rfl⟩ : syracuseStep 393065 = 294799) B294799
theorem B589679 : Blo 115785 589679 := bstep (se 1 (by rfl) ⟨442259, by rfl⟩ : syracuseStep 589679 = 884519) B884519
theorem B262025 : Blo 115785 262025 := bstep (se 2 (by rfl) ⟨98259, by rfl⟩ : syracuseStep 262025 = 196519) B196519
theorem B426377 : Blo 115785 426377 := bstep (se 2 (by rfl) ⟨159891, by rfl⟩ : syracuseStep 426377 = 319783) B319783
theorem B197167 : Blo 115785 197167 := bstep (se 1 (by rfl) ⟨147875, by rfl⟩ : syracuseStep 197167 = 295751) B295751
theorem B1114823 : Blo 115785 1114823 := bstep (se 1 (by rfl) ⟨836117, by rfl⟩ : syracuseStep 1114823 = 1672235) B1672235
theorem B1442873 : Blo 115785 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B590975 : Blo 115785 590975 := bstep (se 1 (by rfl) ⟨443231, by rfl⟩ : syracuseStep 590975 = 886463) B886463
theorem B263771 : Blo 115785 263771 := bstep (se 1 (by rfl) ⟨197828, by rfl⟩ : syracuseStep 263771 = 395657) B395657
theorem B722627 : Blo 115785 722627 := bstep (se 1 (by rfl) ⟨541970, by rfl⟩ : syracuseStep 722627 = 1083941) B1083941
theorem B198409 : Blo 115785 198409 := bstep (se 2 (by rfl) ⟨74403, by rfl⟩ : syracuseStep 198409 = 148807) B148807
theorem B296723 : Blo 115785 296723 := bstep (se 1 (by rfl) ⟨222542, by rfl⟩ : syracuseStep 296723 = 445085) B445085
theorem B1050769 : Blo 115785 1050769 := bstep (se 2 (by rfl) ⟨394038, by rfl⟩ : syracuseStep 1050769 = 788077) B788077
theorem B198875 : Blo 115785 198875 := bstep (se 1 (by rfl) ⟨149156, by rfl⟩ : syracuseStep 198875 = 298313) B298313
theorem B264815 : Blo 115785 264815 := bstep (se 1 (by rfl) ⟨198611, by rfl⟩ : syracuseStep 264815 = 397223) B397223
theorem B134311 : Blo 115785 134311 := bstep (se 1 (by rfl) ⟨100733, by rfl⟩ : syracuseStep 134311 = 201467) B201467
theorem B265769 : Blo 115785 265769 := bstep (se 2 (by rfl) ⟨99663, by rfl⟩ : syracuseStep 265769 = 199327) B199327
theorem B298667 : Blo 115785 298667 := bstep (se 1 (by rfl) ⟨224000, by rfl⟩ : syracuseStep 298667 = 448001) B448001
theorem B200927 : Blo 115785 200927 := bstep (se 1 (by rfl) ⟨150695, by rfl⟩ : syracuseStep 200927 = 301391) B301391
theorem B594215 : Blo 115785 594215 := bstep (se 1 (by rfl) ⟨445661, by rfl⟩ : syracuseStep 594215 = 891323) B891323
theorem B496039 : Blo 115785 496039 := bstep (se 1 (by rfl) ⟨372029, by rfl⟩ : syracuseStep 496039 = 744059) B744059
theorem B627191 : Blo 115785 627191 := bstep (se 1 (by rfl) ⟨470393, by rfl⟩ : syracuseStep 627191 = 940787) B940787
theorem B3314177 : Blo 115785 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B1413719 : Blo 115785 1413719 := bstep (se 1 (by rfl) ⟨1060289, by rfl⟩ : syracuseStep 1413719 = 2120579) B2120579
theorem B430703 : Blo 115785 430703 := bstep (se 1 (by rfl) ⟨323027, by rfl⟩ : syracuseStep 430703 = 646055) B646055
theorem B299983 : Blo 115785 299983 := bstep (se 1 (by rfl) ⟨224987, by rfl⟩ : syracuseStep 299983 = 449975) B449975
theorem B758821 : Blo 115785 758821 := bstep (se 4 (by rfl) ⟨71139, by rfl⟩ : syracuseStep 758821 = 142279) B142279
theorem B201919 : Blo 115785 201919 := bstep (se 1 (by rfl) ⟨151439, by rfl⟩ : syracuseStep 201919 = 302879) B302879
theorem B400031 : Blo 115785 400031 := bstep (se 1 (by rfl) ⟨300023, by rfl⟩ : syracuseStep 400031 = 600047) B600047
theorem B334601 : Blo 115785 334601 := bstep (se 2 (by rfl) ⟨125475, by rfl⟩ : syracuseStep 334601 = 250951) B250951
theorem B596807 : Blo 115785 596807 := bstep (se 1 (by rfl) ⟨447605, by rfl⟩ : syracuseStep 596807 = 895211) B895211
theorem B401975 : Blo 115785 401975 := bstep (se 1 (by rfl) ⟨301481, by rfl⟩ : syracuseStep 401975 = 602963) B602963
theorem B566041 : Blo 115785 566041 := bstep (se 2 (by rfl) ⟨212265, by rfl⟩ : syracuseStep 566041 = 424531) B424531
theorem B402299 : Blo 115785 402299 := bstep (se 1 (by rfl) ⟨301724, by rfl⟩ : syracuseStep 402299 = 603449) B603449
theorem B992351 : Blo 115785 992351 := bstep (se 1 (by rfl) ⟨744263, by rfl⟩ : syracuseStep 992351 = 1488527) B1488527
theorem B402785 : Blo 115785 402785 := bstep (se 2 (by rfl) ⟨151044, by rfl⟩ : syracuseStep 402785 = 302089) B302089
theorem B3090001 : Blo 115785 3090001 := bstep (se 2 (by rfl) ⟨1158750, by rfl⟩ : syracuseStep 3090001 = 2317501) B2317501
theorem B403271 : Blo 115785 403271 := bstep (se 1 (by rfl) ⟨302453, by rfl⟩ : syracuseStep 403271 = 604907) B604907
theorem B173945 : Blo 115785 173945 := bstep (se 2 (by rfl) ⟨65229, by rfl⟩ : syracuseStep 173945 = 130459) B130459
theorem B927679 : Blo 115785 927679 := bstep (se 1 (by rfl) ⟨695759, by rfl⟩ : syracuseStep 927679 = 1391519) B1391519
theorem B174263 : Blo 115785 174263 := bstep (se 1 (by rfl) ⟨130697, by rfl⟩ : syracuseStep 174263 = 261395) B261395
theorem B272737 : Blo 115785 272737 := bstep (se 2 (by rfl) ⟨102276, by rfl⟩ : syracuseStep 272737 = 204553) B204553
theorem B174683 : Blo 115785 174683 := bstep (se 1 (by rfl) ⟨131012, by rfl⟩ : syracuseStep 174683 = 262025) B262025
theorem B2861689 : Blo 115785 2861689 := bstep (se 2 (by rfl) ⟨1073133, by rfl⟩ : syracuseStep 2861689 = 2146267) B2146267
theorem B2042657 : Blo 115785 2042657 := bstep (se 2 (by rfl) ⟨765996, by rfl⟩ : syracuseStep 2042657 = 1531993) B1531993
theorem B174971 : Blo 115785 174971 := bstep (se 1 (by rfl) ⟨131228, by rfl⟩ : syracuseStep 174971 = 262457) B262457
theorem B503131 : Blo 115785 503131 := bstep (se 1 (by rfl) ⟨377348, by rfl⟩ : syracuseStep 503131 = 754697) B754697
theorem B1912409 : Blo 115785 1912409 := bstep (se 2 (by rfl) ⟨717153, by rfl⟩ : syracuseStep 1912409 = 1434307) B1434307
theorem B896669 : Blo 115785 896669 := bstep (se 3 (by rfl) ⟨168125, by rfl⟩ : syracuseStep 896669 = 336251) B336251
theorem B339623 : Blo 115785 339623 := bstep (se 1 (by rfl) ⟨254717, by rfl⟩ : syracuseStep 339623 = 509435) B509435
theorem B176123 : Blo 115785 176123 := bstep (se 1 (by rfl) ⟨132092, by rfl⟩ : syracuseStep 176123 = 264185) B264185
theorem B176183 : Blo 115785 176183 := bstep (se 1 (by rfl) ⟨132137, by rfl⟩ : syracuseStep 176183 = 264275) B264275
theorem B176297 : Blo 115785 176297 := bstep (se 2 (by rfl) ⟨66111, by rfl⟩ : syracuseStep 176297 = 132223) B132223
theorem B176303 : Blo 115785 176303 := bstep (se 1 (by rfl) ⟨132227, by rfl⟩ : syracuseStep 176303 = 264455) B264455
theorem B3420467 : Blo 115785 3420467 := bstep (se 1 (by rfl) ⟨2565350, by rfl⟩ : syracuseStep 3420467 = 5130701) B5130701
theorem B602477 : Blo 115785 602477 := bstep (se 3 (by rfl) ⟨112964, by rfl⟩ : syracuseStep 602477 = 225929) B225929
theorem B569791 : Blo 115785 569791 := bstep (se 1 (by rfl) ⟨427343, by rfl⟩ : syracuseStep 569791 = 854687) B854687
theorem B1258021 : Blo 115785 1258021 := bstep (se 4 (by rfl) ⟨117939, by rfl⟩ : syracuseStep 1258021 = 235879) B235879
theorem B668857 : Blo 115785 668857 := bstep (se 2 (by rfl) ⟨250821, by rfl⟩ : syracuseStep 668857 = 501643) B501643
theorem B767227 : Blo 115785 767227 := bstep (se 1 (by rfl) ⟨575420, by rfl⟩ : syracuseStep 767227 = 1150841) B1150841
theorem B505129 : Blo 115785 505129 := bstep (se 2 (by rfl) ⟨189423, by rfl⟩ : syracuseStep 505129 = 378847) B378847
theorem B374183 : Blo 115785 374183 := bstep (se 1 (by rfl) ⟨280637, by rfl⟩ : syracuseStep 374183 = 561275) B561275
theorem B177659 : Blo 115785 177659 := bstep (se 1 (by rfl) ⟨133244, by rfl⟩ : syracuseStep 177659 = 266489) B266489
theorem B177833 : Blo 115785 177833 := bstep (se 2 (by rfl) ⟨66687, by rfl⟩ : syracuseStep 177833 = 133375) B133375
theorem B177839 : Blo 115785 177839 := bstep (se 1 (by rfl) ⟨133379, by rfl⟩ : syracuseStep 177839 = 266759) B266759
theorem B177959 : Blo 115785 177959 := bstep (se 1 (by rfl) ⟨133469, by rfl⟩ : syracuseStep 177959 = 266939) B266939
theorem B1816829 : Blo 115785 1816829 := bstep (se 3 (by rfl) ⟨340655, by rfl⟩ : syracuseStep 1816829 = 681311) B681311
theorem B178487 : Blo 115785 178487 := bstep (se 1 (by rfl) ⟨133865, by rfl⟩ : syracuseStep 178487 = 267731) B267731
theorem B178559 : Blo 115785 178559 := bstep (se 1 (by rfl) ⟨133919, by rfl⟩ : syracuseStep 178559 = 267839) B267839
theorem B178667 : Blo 115785 178667 := bstep (se 1 (by rfl) ⟨134000, by rfl⟩ : syracuseStep 178667 = 268001) B268001
theorem B342521 : Blo 115785 342521 := bstep (se 2 (by rfl) ⟨128445, by rfl⟩ : syracuseStep 342521 = 256891) B256891
theorem B1129085 : Blo 115785 1129085 := bstep (se 3 (by rfl) ⟨211703, by rfl⟩ : syracuseStep 1129085 = 423407) B423407
theorem B178907 : Blo 115785 178907 := bstep (se 1 (by rfl) ⟨134180, by rfl⟩ : syracuseStep 178907 = 268361) B268361
theorem B441227 : Blo 115785 441227 := bstep (se 1 (by rfl) ⟨330920, by rfl⟩ : syracuseStep 441227 = 661841) B661841
theorem B245929 : Blo 115785 245929 := bstep (se 2 (by rfl) ⟨92223, by rfl⟩ : syracuseStep 245929 = 184447) B184447
theorem B6799625 : Blo 115785 6799625 := bstep (se 2 (by rfl) ⟨2549859, by rfl⟩ : syracuseStep 6799625 = 5099719) B5099719
theorem B672047 : Blo 115785 672047 := bstep (se 1 (by rfl) ⟨504035, by rfl⟩ : syracuseStep 672047 = 1008071) B1008071
theorem B967625 : Blo 115785 967625 := bstep (se 2 (by rfl) ⟨362859, by rfl⟩ : syracuseStep 967625 = 725719) B725719
theorem B115803 : Blo 115785 115803 := bstep (se 1 (by rfl) ⟨86852, by rfl⟩ : syracuseStep 115803 = 173705) B173705
theorem B1328237 : Blo 115785 1328237 := bstep (se 3 (by rfl) ⟨249044, by rfl⟩ : syracuseStep 1328237 = 498089) B498089
theorem B115839 : Blo 115785 115839 := bstep (se 1 (by rfl) ⟨86879, by rfl⟩ : syracuseStep 115839 = 173759) B173759
theorem B836837 : Blo 115785 836837 := bstep (se 4 (by rfl) ⟨78453, by rfl⟩ : syracuseStep 836837 = 156907) B156907
theorem B115943 : Blo 115785 115943 := bstep (se 1 (by rfl) ⟨86957, by rfl⟩ : syracuseStep 115943 = 173915) B173915
theorem B116199 : Blo 115785 116199 := bstep (se 1 (by rfl) ⟨87149, by rfl⟩ : syracuseStep 116199 = 174299) B174299
theorem B116379 : Blo 115785 116379 := bstep (se 1 (by rfl) ⟨87284, by rfl⟩ : syracuseStep 116379 = 174569) B174569
theorem B116383 : Blo 115785 116383 := bstep (se 1 (by rfl) ⟨87287, by rfl⟩ : syracuseStep 116383 = 174575) B174575
theorem B116591 : Blo 115785 116591 := bstep (se 1 (by rfl) ⟨87443, by rfl⟩ : syracuseStep 116591 = 174887) B174887
theorem B116639 : Blo 115785 116639 := bstep (se 1 (by rfl) ⟨87479, by rfl⟩ : syracuseStep 116639 = 174959) B174959
theorem B116807 : Blo 115785 116807 := bstep (se 1 (by rfl) ⟨87605, by rfl⟩ : syracuseStep 116807 = 175211) B175211
theorem B2443385 : Blo 115785 2443385 := bstep (se 2 (by rfl) ⟨916269, by rfl⟩ : syracuseStep 2443385 = 1832539) B1832539
theorem B116967 : Blo 115785 116967 := bstep (se 1 (by rfl) ⟨87725, by rfl⟩ : syracuseStep 116967 = 175451) B175451
theorem B116987 : Blo 115785 116987 := bstep (se 1 (by rfl) ⟨87740, by rfl⟩ : syracuseStep 116987 = 175481) B175481
theorem B116991 : Blo 115785 116991 := bstep (se 1 (by rfl) ⟨87743, by rfl⟩ : syracuseStep 116991 = 175487) B175487
theorem B477467 : Blo 115785 477467 := bstep (se 1 (by rfl) ⟨358100, by rfl⟩ : syracuseStep 477467 = 716201) B716201
theorem B117147 : Blo 115785 117147 := bstep (se 1 (by rfl) ⟨87860, by rfl⟩ : syracuseStep 117147 = 175721) B175721
theorem B3852947 : Blo 115785 3852947 := bstep (se 1 (by rfl) ⟨2889710, by rfl⟩ : syracuseStep 3852947 = 5779421) B5779421
theorem B117407 : Blo 115785 117407 := bstep (se 1 (by rfl) ⟨88055, by rfl⟩ : syracuseStep 117407 = 176111) B176111
theorem B117487 : Blo 115785 117487 := bstep (se 1 (by rfl) ⟨88115, by rfl⟩ : syracuseStep 117487 = 176231) B176231
theorem B117567 : Blo 115785 117567 := bstep (se 1 (by rfl) ⟨88175, by rfl⟩ : syracuseStep 117567 = 176351) B176351
theorem B117607 : Blo 115785 117607 := bstep (se 1 (by rfl) ⟨88205, by rfl⟩ : syracuseStep 117607 = 176411) B176411
theorem B674689 : Blo 115785 674689 := bstep (se 2 (by rfl) ⟨253008, by rfl⟩ : syracuseStep 674689 = 506017) B506017
theorem B281483 : Blo 115785 281483 := bstep (se 1 (by rfl) ⟨211112, by rfl⟩ : syracuseStep 281483 = 422225) B422225
theorem B117871 : Blo 115785 117871 := bstep (se 1 (by rfl) ⟨88403, by rfl⟩ : syracuseStep 117871 = 176807) B176807
theorem B117951 : Blo 115785 117951 := bstep (se 1 (by rfl) ⟨88463, by rfl⟩ : syracuseStep 117951 = 176927) B176927
theorem B117967 : Blo 115785 117967 := bstep (se 1 (by rfl) ⟨88475, by rfl⟩ : syracuseStep 117967 = 176951) B176951
theorem B118043 : Blo 115785 118043 := bstep (se 1 (by rfl) ⟨88532, by rfl⟩ : syracuseStep 118043 = 177065) B177065
theorem B1166663 : Blo 115785 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B118087 : Blo 115785 118087 := bstep (se 1 (by rfl) ⟨88565, by rfl⟩ : syracuseStep 118087 = 177131) B177131
theorem B380231 : Blo 115785 380231 := bstep (se 1 (by rfl) ⟨285173, by rfl⟩ : syracuseStep 380231 = 570347) B570347
theorem B118271 : Blo 115785 118271 := bstep (se 1 (by rfl) ⟨88703, by rfl⟩ : syracuseStep 118271 = 177407) B177407
theorem B118299 : Blo 115785 118299 := bstep (se 1 (by rfl) ⟨88724, by rfl⟩ : syracuseStep 118299 = 177449) B177449
theorem B118695 : Blo 115785 118695 := bstep (se 1 (by rfl) ⟨89021, by rfl⟩ : syracuseStep 118695 = 178043) B178043
theorem B118719 : Blo 115785 118719 := bstep (se 1 (by rfl) ⟨89039, by rfl⟩ : syracuseStep 118719 = 178079) B178079
theorem B1331153 : Blo 115785 1331153 := bstep (se 2 (by rfl) ⟨499182, by rfl⟩ : syracuseStep 1331153 = 998365) B998365
theorem B2707505 : Blo 115785 2707505 := bstep (se 2 (by rfl) ⟨1015314, by rfl⟩ : syracuseStep 2707505 = 2030629) B2030629
theorem B118855 : Blo 115785 118855 := bstep (se 1 (by rfl) ⟨89141, by rfl⟩ : syracuseStep 118855 = 178283) B178283
theorem B118875 : Blo 115785 118875 := bstep (se 1 (by rfl) ⟨89156, by rfl⟩ : syracuseStep 118875 = 178313) B178313
theorem B118975 : Blo 115785 118975 := bstep (se 1 (by rfl) ⟨89231, by rfl⟩ : syracuseStep 118975 = 178463) B178463
theorem B447059 : Blo 115785 447059 := bstep (se 1 (by rfl) ⟨335294, by rfl⟩ : syracuseStep 447059 = 670589) B670589
theorem B119423 : Blo 115785 119423 := bstep (se 1 (by rfl) ⟨89567, by rfl⟩ : syracuseStep 119423 = 179135) B179135
theorem B119455 : Blo 115785 119455 := bstep (se 1 (by rfl) ⟨89591, by rfl⟩ : syracuseStep 119455 = 179183) B179183
theorem B250651 : Blo 115785 250651 := bstep (se 1 (by rfl) ⟨187988, by rfl⟩ : syracuseStep 250651 = 375977) B375977
theorem B119579 : Blo 115785 119579 := bstep (se 1 (by rfl) ⟨89684, by rfl⟩ : syracuseStep 119579 = 179369) B179369
theorem B218195 : Blo 115785 218195 := bstep (se 1 (by rfl) ⟨163646, by rfl⟩ : syracuseStep 218195 = 327293) B327293
theorem B709955 : Blo 115785 709955 := bstep (se 1 (by rfl) ⟨532466, by rfl⟩ : syracuseStep 709955 = 1064933) B1064933
theorem B1595213 : Blo 115785 1595213 := bstep (se 3 (by rfl) ⟨299102, by rfl⟩ : syracuseStep 1595213 = 598205) B598205
theorem B317351 : Blo 115785 317351 := bstep (se 1 (by rfl) ⟨238013, by rfl⟩ : syracuseStep 317351 = 476027) B476027
theorem B677879 : Blo 115785 677879 := bstep (se 1 (by rfl) ⟨508409, by rfl⟩ : syracuseStep 677879 = 1016819) B1016819
theorem B1366145 : Blo 115785 1366145 := bstep (se 2 (by rfl) ⟨512304, by rfl⟩ : syracuseStep 1366145 = 1024609) B1024609
theorem B448699 : Blo 115785 448699 := bstep (se 1 (by rfl) ⟨336524, by rfl⟩ : syracuseStep 448699 = 673049) B673049
theorem B940403 : Blo 115785 940403 := bstep (se 1 (by rfl) ⟨705302, by rfl⟩ : syracuseStep 940403 = 1410605) B1410605
theorem B842663 : Blo 115785 842663 := bstep (se 1 (by rfl) ⟨631997, by rfl⟩ : syracuseStep 842663 = 1263995) B1263995
theorem B449657 : Blo 115785 449657 := bstep (se 2 (by rfl) ⟨168621, by rfl⟩ : syracuseStep 449657 = 337243) B337243
theorem B3824927 : Blo 115785 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B483695 : Blo 115785 483695 := bstep (se 1 (by rfl) ⟨362771, by rfl⟩ : syracuseStep 483695 = 725543) B725543
theorem B221791 : Blo 115785 221791 := bstep (se 1 (by rfl) ⟨166343, by rfl⟩ : syracuseStep 221791 = 332687) B332687
theorem B3171149 : Blo 115785 3171149 := bstep (se 3 (by rfl) ⟨594590, by rfl⟩ : syracuseStep 3171149 = 1189181) B1189181
theorem B190127 : Blo 115785 190127 := bstep (se 1 (by rfl) ⟨142595, by rfl⟩ : syracuseStep 190127 = 285191) B285191
theorem B2910167 : Blo 115785 2910167 := bstep (se 1 (by rfl) ⟨2182625, by rfl⟩ : syracuseStep 2910167 = 4365251) B4365251
theorem B2156777 : Blo 115785 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B452891 : Blo 115785 452891 := bstep (se 1 (by rfl) ⟨339668, by rfl⟩ : syracuseStep 452891 = 679337) B679337
theorem B125599 : Blo 115785 125599 := bstep (se 1 (by rfl) ⟨94199, by rfl⟩ : syracuseStep 125599 = 188399) B188399
theorem B421129 : Blo 115785 421129 := bstep (se 2 (by rfl) ⟨157923, by rfl⟩ : syracuseStep 421129 = 315847) B315847
theorem B1699163 : Blo 115785 1699163 := bstep (se 1 (by rfl) ⟨1274372, by rfl⟩ : syracuseStep 1699163 = 2548745) B2548745
theorem B224927 : Blo 115785 224927 := bstep (se 1 (by rfl) ⟨168695, by rfl⟩ : syracuseStep 224927 = 337391) B337391
theorem B1011487 : Blo 115785 1011487 := bstep (se 1 (by rfl) ⟨758615, by rfl⟩ : syracuseStep 1011487 = 1517231) B1517231
theorem B391067 : Blo 115785 391067 := bstep (se 1 (by rfl) ⟨293300, by rfl⟩ : syracuseStep 391067 = 586601) B586601
theorem B293503 : Blo 115785 293503 := bstep (se 1 (by rfl) ⟨220127, by rfl⟩ : syracuseStep 293503 = 440255) B440255
theorem B817879 : Blo 115785 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B195439 : Blo 115785 195439 := bstep (se 1 (by rfl) ⟨146579, by rfl⟩ : syracuseStep 195439 = 293159) B293159
theorem B3242911 : Blo 115785 3242911 := bstep (se 1 (by rfl) ⟨2432183, by rfl⟩ : syracuseStep 3242911 = 4864367) B4864367
theorem B261431 : Blo 115785 261431 := bstep (se 1 (by rfl) ⟨196073, by rfl⟩ : syracuseStep 261431 = 392147) B392147
theorem B1637729 : Blo 115785 1637729 := bstep (se 2 (by rfl) ⟨614148, by rfl⟩ : syracuseStep 1637729 = 1228297) B1228297
theorem B294313 : Blo 115785 294313 := bstep (se 2 (by rfl) ⟨110367, by rfl⟩ : syracuseStep 294313 = 220735) B220735
theorem B392957 : Blo 115785 392957 := bstep (se 3 (by rfl) ⟨73679, by rfl⟩ : syracuseStep 392957 = 147359) B147359
theorem B262043 : Blo 115785 262043 := bstep (se 1 (by rfl) ⟨196532, by rfl⟩ : syracuseStep 262043 = 393065) B393065
theorem B393119 : Blo 115785 393119 := bstep (se 1 (by rfl) ⟨294839, by rfl⟩ : syracuseStep 393119 = 589679) B589679
theorem B327905 : Blo 115785 327905 := bstep (se 2 (by rfl) ⟨122964, by rfl⟩ : syracuseStep 327905 = 245929) B245929
theorem B262889 : Blo 115785 262889 := bstep (se 2 (by rfl) ⟨98583, by rfl⟩ : syracuseStep 262889 = 197167) B197167
theorem B885491 : Blo 115785 885491 := bstep (se 1 (by rfl) ⟨664118, by rfl⟩ : syracuseStep 885491 = 1328237) B1328237
theorem B393983 : Blo 115785 393983 := bstep (se 1 (by rfl) ⟨295487, by rfl⟩ : syracuseStep 393983 = 590975) B590975
theorem B295721 : Blo 115785 295721 := bstep (se 2 (by rfl) ⟨110895, by rfl⟩ : syracuseStep 295721 = 221791) B221791
theorem B557891 : Blo 115785 557891 := bstep (se 1 (by rfl) ⟨418418, by rfl⟩ : syracuseStep 557891 = 836837) B836837
theorem B2327413 : Blo 115785 2327413 := bstep (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) B218195
theorem B754721 : Blo 115785 754721 := bstep (se 2 (by rfl) ⟨283020, by rfl⟩ : syracuseStep 754721 = 566041) B566041
theorem B197815 : Blo 115785 197815 := bstep (se 1 (by rfl) ⟨148361, by rfl⟩ : syracuseStep 197815 = 296723) B296723
theorem B132583 : Blo 115785 132583 := bstep (se 1 (by rfl) ⟨99437, by rfl⟩ : syracuseStep 132583 = 198875) B198875
theorem B264545 : Blo 115785 264545 := bstep (se 2 (by rfl) ⟨99204, by rfl⟩ : syracuseStep 264545 = 198409) B198409
theorem B199111 : Blo 115785 199111 := bstep (se 1 (by rfl) ⟨149333, by rfl⟩ : syracuseStep 199111 = 298667) B298667
theorem B887435 : Blo 115785 887435 := bstep (se 1 (by rfl) ⟨665576, by rfl⟩ : syracuseStep 887435 = 1331153) B1331153
theorem B1805003 : Blo 115785 1805003 := bstep (se 1 (by rfl) ⟨1353752, by rfl⟩ : syracuseStep 1805003 = 2707505) B2707505
theorem B133951 : Blo 115785 133951 := bstep (se 1 (by rfl) ⟨100463, by rfl⟩ : syracuseStep 133951 = 200927) B200927
theorem B396143 : Blo 115785 396143 := bstep (se 1 (by rfl) ⟨297107, by rfl⟩ : syracuseStep 396143 = 594215) B594215
theorem B298039 : Blo 115785 298039 := bstep (se 1 (by rfl) ⟨223529, by rfl⟩ : syracuseStep 298039 = 447059) B447059
theorem B167465 : Blo 115785 167465 := bstep (se 2 (by rfl) ⟨62799, by rfl⟩ : syracuseStep 167465 = 125599) B125599
theorem B626935 : Blo 115785 626935 := bstep (se 1 (by rfl) ⟨470201, by rfl⟩ : syracuseStep 626935 = 940403) B940403
theorem B561505 : Blo 115785 561505 := bstep (se 2 (by rfl) ⟨210564, by rfl⟩ : syracuseStep 561505 = 421129) B421129
theorem B266687 : Blo 115785 266687 := bstep (se 1 (by rfl) ⟨200015, by rfl⟩ : syracuseStep 266687 = 400031) B400031
theorem B397871 : Blo 115785 397871 := bstep (se 1 (by rfl) ⟨298403, by rfl⟩ : syracuseStep 397871 = 596807) B596807
theorem B561775 : Blo 115785 561775 := bstep (se 1 (by rfl) ⟨421331, by rfl⟩ : syracuseStep 561775 = 842663) B842663
theorem B299771 : Blo 115785 299771 := bstep (se 1 (by rfl) ⟨224828, by rfl⟩ : syracuseStep 299771 = 449657) B449657
theorem B1348649 : Blo 115785 1348649 := bstep (se 2 (by rfl) ⟨505743, by rfl⟩ : syracuseStep 1348649 = 1011487) B1011487
theorem B267983 : Blo 115785 267983 := bstep (se 1 (by rfl) ⟨200987, by rfl⟩ : syracuseStep 267983 = 401975) B401975
theorem B661385 : Blo 115785 661385 := bstep (se 2 (by rfl) ⟨248019, by rfl⟩ : syracuseStep 661385 = 496039) B496039
theorem B268199 : Blo 115785 268199 := bstep (se 1 (by rfl) ⟨201149, by rfl⟩ : syracuseStep 268199 = 402299) B402299
theorem B759721 : Blo 115785 759721 := bstep (se 2 (by rfl) ⟨284895, by rfl⟩ : syracuseStep 759721 = 569791) B569791
theorem B1677361 : Blo 115785 1677361 := bstep (se 2 (by rfl) ⟨629010, by rfl⟩ : syracuseStep 1677361 = 1258021) B1258021
theorem B661567 : Blo 115785 661567 := bstep (se 1 (by rfl) ⟨496175, by rfl⟩ : syracuseStep 661567 = 992351) B992351
theorem B268523 : Blo 115785 268523 := bstep (se 1 (by rfl) ⟨201392, by rfl⟩ : syracuseStep 268523 = 402785) B402785
theorem B334201 : Blo 115785 334201 := bstep (se 2 (by rfl) ⟨125325, by rfl⟩ : syracuseStep 334201 = 250651) B250651
theorem B268847 : Blo 115785 268847 := bstep (se 1 (by rfl) ⟨201635, by rfl⟩ : syracuseStep 268847 = 403271) B403271
theorem B399977 : Blo 115785 399977 := bstep (se 2 (by rfl) ⟨149991, by rfl⟩ : syracuseStep 399977 = 299983) B299983
theorem B1940111 : Blo 115785 1940111 := bstep (se 1 (by rfl) ⟨1455083, by rfl⟩ : syracuseStep 1940111 = 2910167) B2910167
theorem B301927 : Blo 115785 301927 := bstep (se 1 (by rfl) ⟨226445, by rfl⟩ : syracuseStep 301927 = 452891) B452891
theorem B891809 : Blo 115785 891809 := bstep (se 2 (by rfl) ⟨334428, by rfl⟩ : syracuseStep 891809 = 668857) B668857
theorem B269225 : Blo 115785 269225 := bstep (se 2 (by rfl) ⟨100959, by rfl⟩ : syracuseStep 269225 = 201919) B201919
theorem B1022969 : Blo 115785 1022969 := bstep (se 2 (by rfl) ⟨383613, by rfl⟩ : syracuseStep 1022969 = 767227) B767227
theorem B597779 : Blo 115785 597779 := bstep (se 1 (by rfl) ⟨448334, by rfl⟩ : syracuseStep 597779 = 896669) B896669
theorem B401651 : Blo 115785 401651 := bstep (se 1 (by rfl) ⟨301238, by rfl⟩ : syracuseStep 401651 = 602477) B602477
theorem B598265 : Blo 115785 598265 := bstep (se 2 (by rfl) ⟨224349, by rfl⟩ : syracuseStep 598265 = 448699) B448699
theorem B1090505 : Blo 115785 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B174287 : Blo 115785 174287 := bstep (se 1 (by rfl) ⟨130715, by rfl⟩ : syracuseStep 174287 = 261431) B261431
theorem B1091819 : Blo 115785 1091819 := bstep (se 1 (by rfl) ⟨818864, by rfl⟩ : syracuseStep 1091819 = 1637729) B1637729
theorem B174695 : Blo 115785 174695 := bstep (se 1 (by rfl) ⟨131021, by rfl⟩ : syracuseStep 174695 = 262043) B262043
theorem B4533083 : Blo 115785 4533083 := bstep (se 1 (by rfl) ⟨3399812, by rfl⟩ : syracuseStep 4533083 = 6799625) B6799625
theorem B961915 : Blo 115785 961915 := bstep (se 1 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 961915 = 1442873) B1442873
theorem B175847 : Blo 115785 175847 := bstep (se 1 (by rfl) ⟨131885, by rfl⟩ : syracuseStep 175847 = 263771) B263771
theorem B176543 : Blo 115785 176543 := bstep (se 1 (by rfl) ⟨132407, by rfl⟩ : syracuseStep 176543 = 264815) B264815
theorem B1454597 : Blo 115785 1454597 := bstep (se 4 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 1454597 = 272737) B272737
theorem B177179 : Blo 115785 177179 := bstep (se 1 (by rfl) ⟨132884, by rfl⟩ : syracuseStep 177179 = 265769) B265769
theorem B2209451 : Blo 115785 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B3815585 : Blo 115785 3815585 := bstep (se 2 (by rfl) ⟨1430844, by rfl⟩ : syracuseStep 3815585 = 2861689) B2861689
theorem B473303 : Blo 115785 473303 := bstep (se 1 (by rfl) ⟨354977, by rfl⟩ : syracuseStep 473303 = 709955) B709955
theorem B899585 : Blo 115785 899585 := bstep (se 2 (by rfl) ⟨337344, by rfl⟩ : syracuseStep 899585 = 674689) B674689
theorem B1063475 : Blo 115785 1063475 := bstep (se 1 (by rfl) ⟨797606, by rfl⟩ : syracuseStep 1063475 = 1595213) B1595213
theorem B211567 : Blo 115785 211567 := bstep (se 1 (by rfl) ⟨158675, by rfl⟩ : syracuseStep 211567 = 317351) B317351
theorem B179081 : Blo 115785 179081 := bstep (se 2 (by rfl) ⟨67155, by rfl⟩ : syracuseStep 179081 = 134311) B134311
theorem B670841 : Blo 115785 670841 := bstep (se 2 (by rfl) ⟨251565, by rfl⟩ : syracuseStep 670841 = 503131) B503131
theorem B507005 : Blo 115785 507005 := bstep (se 3 (by rfl) ⟨95063, by rfl⟩ : syracuseStep 507005 = 190127) B190127
theorem B2114099 : Blo 115785 2114099 := bstep (se 1 (by rfl) ⟨1585574, by rfl⟩ : syracuseStep 2114099 = 3171149) B3171149
theorem B115963 : Blo 115785 115963 := bstep (se 1 (by rfl) ⟨86972, by rfl⟩ : syracuseStep 115963 = 173945) B173945
theorem B116175 : Blo 115785 116175 := bstep (se 1 (by rfl) ⟨87131, by rfl⟩ : syracuseStep 116175 = 174263) B174263
theorem B10274525 : Blo 115785 10274525 := bstep (se 3 (by rfl) ⟨1926473, by rfl⟩ : syracuseStep 10274525 = 3852947) B3852947
theorem B673505 : Blo 115785 673505 := bstep (se 2 (by rfl) ⟨252564, by rfl⟩ : syracuseStep 673505 = 505129) B505129
theorem B116455 : Blo 115785 116455 := bstep (se 1 (by rfl) ⟨87341, by rfl⟩ : syracuseStep 116455 = 174683) B174683
theorem B1361771 : Blo 115785 1361771 := bstep (se 1 (by rfl) ⟨1021328, by rfl⟩ : syracuseStep 1361771 = 2042657) B2042657
theorem B116647 : Blo 115785 116647 := bstep (se 1 (by rfl) ⟨87485, by rfl⟩ : syracuseStep 116647 = 174971) B174971
theorem B1132775 : Blo 115785 1132775 := bstep (se 1 (by rfl) ⟨849581, by rfl⟩ : syracuseStep 1132775 = 1699163) B1699163
theorem B149951 : Blo 115785 149951 := bstep (se 1 (by rfl) ⟨112463, by rfl⟩ : syracuseStep 149951 = 224927) B224927
theorem B117415 : Blo 115785 117415 := bstep (se 1 (by rfl) ⟨88061, by rfl⟩ : syracuseStep 117415 = 176123) B176123
theorem B117455 : Blo 115785 117455 := bstep (se 1 (by rfl) ⟨88091, by rfl⟩ : syracuseStep 117455 = 176183) B176183
theorem B117531 : Blo 115785 117531 := bstep (se 1 (by rfl) ⟨88148, by rfl⟩ : syracuseStep 117531 = 176297) B176297
theorem B117535 : Blo 115785 117535 := bstep (se 1 (by rfl) ⟨88151, by rfl⟩ : syracuseStep 117535 = 176303) B176303
theorem B2280311 : Blo 115785 2280311 := bstep (se 1 (by rfl) ⟨1710233, by rfl⟩ : syracuseStep 2280311 = 3420467) B3420467
theorem B249455 : Blo 115785 249455 := bstep (se 1 (by rfl) ⟨187091, by rfl⟩ : syracuseStep 249455 = 374183) B374183
theorem B118439 : Blo 115785 118439 := bstep (se 1 (by rfl) ⟨88829, by rfl⟩ : syracuseStep 118439 = 177659) B177659
theorem B118555 : Blo 115785 118555 := bstep (se 1 (by rfl) ⟨88916, by rfl⟩ : syracuseStep 118555 = 177833) B177833
theorem B118559 : Blo 115785 118559 := bstep (se 1 (by rfl) ⟨88919, by rfl⟩ : syracuseStep 118559 = 177839) B177839
theorem B118639 : Blo 115785 118639 := bstep (se 1 (by rfl) ⟨88979, by rfl⟩ : syracuseStep 118639 = 177959) B177959
theorem B118991 : Blo 115785 118991 := bstep (se 1 (by rfl) ⟨89243, by rfl⟩ : syracuseStep 118991 = 178487) B178487
theorem B119039 : Blo 115785 119039 := bstep (se 1 (by rfl) ⟨89279, by rfl⟩ : syracuseStep 119039 = 178559) B178559
theorem B119111 : Blo 115785 119111 := bstep (se 1 (by rfl) ⟨89333, by rfl⟩ : syracuseStep 119111 = 178667) B178667
theorem B119271 : Blo 115785 119271 := bstep (se 1 (by rfl) ⟨89453, by rfl⟩ : syracuseStep 119271 = 178907) B178907
theorem B448031 : Blo 115785 448031 := bstep (se 1 (by rfl) ⟨336023, by rfl⟩ : syracuseStep 448031 = 672047) B672047
theorem B284251 : Blo 115785 284251 := bstep (se 1 (by rfl) ⟨213188, by rfl⟩ : syracuseStep 284251 = 426377) B426377
theorem B743215 : Blo 115785 743215 := bstep (se 1 (by rfl) ⟨557411, by rfl⟩ : syracuseStep 743215 = 1114823) B1114823
theorem B645083 : Blo 115785 645083 := bstep (se 1 (by rfl) ⟨483812, by rfl⟩ : syracuseStep 645083 = 967625) B967625
theorem B481751 : Blo 115785 481751 := bstep (se 1 (by rfl) ⟨361313, by rfl⟩ : syracuseStep 481751 = 722627) B722627
theorem B1628923 : Blo 115785 1628923 := bstep (se 1 (by rfl) ⟨1221692, by rfl⟩ : syracuseStep 1628923 = 2443385) B2443385
theorem B318311 : Blo 115785 318311 := bstep (se 1 (by rfl) ⟨238733, by rfl⟩ : syracuseStep 318311 = 477467) B477467
theorem B187655 : Blo 115785 187655 := bstep (se 1 (by rfl) ⟨140741, by rfl⟩ : syracuseStep 187655 = 281483) B281483
theorem B4120001 : Blo 115785 4120001 := bstep (se 2 (by rfl) ⟨1545000, by rfl⟩ : syracuseStep 4120001 = 3090001) B3090001
theorem B777775 : Blo 115785 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B253487 : Blo 115785 253487 := bstep (se 1 (by rfl) ⟨190115, by rfl⟩ : syracuseStep 253487 = 380231) B380231
theorem B1236905 : Blo 115785 1236905 := bstep (se 2 (by rfl) ⟨463839, by rfl⟩ : syracuseStep 1236905 = 927679) B927679
theorem B1401025 : Blo 115785 1401025 := bstep (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) B1050769
theorem B418127 : Blo 115785 418127 := bstep (se 1 (by rfl) ⟨313595, by rfl⟩ : syracuseStep 418127 = 627191) B627191
theorem B942479 : Blo 115785 942479 := bstep (se 1 (by rfl) ⟨706859, by rfl⟩ : syracuseStep 942479 = 1413719) B1413719
theorem B287135 : Blo 115785 287135 := bstep (se 1 (by rfl) ⟨215351, by rfl⟩ : syracuseStep 287135 = 430703) B430703
theorem B451919 : Blo 115785 451919 := bstep (se 1 (by rfl) ⟨338939, by rfl⟩ : syracuseStep 451919 = 677879) B677879
theorem B910763 : Blo 115785 910763 := bstep (se 1 (by rfl) ⟨683072, by rfl⟩ : syracuseStep 910763 = 1366145) B1366145
theorem B223067 : Blo 115785 223067 := bstep (se 1 (by rfl) ⟨167300, by rfl⟩ : syracuseStep 223067 = 334601) B334601
theorem B2549951 : Blo 115785 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B322463 : Blo 115785 322463 := bstep (se 1 (by rfl) ⟨241847, by rfl⟩ : syracuseStep 322463 = 483695) B483695
theorem B1011761 : Blo 115785 1011761 := bstep (se 2 (by rfl) ⟨379410, by rfl⟩ : syracuseStep 1011761 = 758821) B758821
theorem B1437851 : Blo 115785 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B1274939 : Blo 115785 1274939 := bstep (se 1 (by rfl) ⟨956204, by rfl⟩ : syracuseStep 1274939 = 1912409) B1912409
theorem B226415 : Blo 115785 226415 := bstep (se 1 (by rfl) ⟨169811, by rfl⟩ : syracuseStep 226415 = 339623) B339623
theorem B391337 : Blo 115785 391337 := bstep (se 2 (by rfl) ⟨146751, by rfl⟩ : syracuseStep 391337 = 293503) B293503
theorem B260585 : Blo 115785 260585 := bstep (se 2 (by rfl) ⟨97719, by rfl⟩ : syracuseStep 260585 = 195439) B195439
theorem B4323881 : Blo 115785 4323881 := bstep (se 2 (by rfl) ⟨1621455, by rfl⟩ : syracuseStep 4323881 = 3242911) B3242911
theorem B260711 : Blo 115785 260711 := bstep (se 1 (by rfl) ⟨195533, by rfl⟩ : syracuseStep 260711 = 391067) B391067
theorem B1211219 : Blo 115785 1211219 := bstep (se 1 (by rfl) ⟨908414, by rfl⟩ : syracuseStep 1211219 = 1816829) B1816829
theorem B228347 : Blo 115785 228347 := bstep (se 1 (by rfl) ⟨171260, by rfl⟩ : syracuseStep 228347 = 342521) B342521
theorem B752723 : Blo 115785 752723 := bstep (se 1 (by rfl) ⟨564542, by rfl⟩ : syracuseStep 752723 = 1129085) B1129085
theorem B392417 : Blo 115785 392417 := bstep (se 2 (by rfl) ⟨147156, by rfl⟩ : syracuseStep 392417 = 294313) B294313
theorem B294151 : Blo 115785 294151 := bstep (se 1 (by rfl) ⟨220613, by rfl⟩ : syracuseStep 294151 = 441227) B441227
theorem B261971 : Blo 115785 261971 := bstep (se 1 (by rfl) ⟨196478, by rfl⟩ : syracuseStep 261971 = 392957) B392957
theorem B262079 : Blo 115785 262079 := bstep (se 1 (by rfl) ⟨196559, by rfl⟩ : syracuseStep 262079 = 393119) B393119
theorem B1868033 : Blo 115785 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B1409399 : Blo 115785 1409399 := bstep (se 1 (by rfl) ⟨1057049, by rfl⟩ : syracuseStep 1409399 = 2114099) B2114099
theorem B590327 : Blo 115785 590327 := bstep (se 1 (by rfl) ⟨442745, by rfl⟩ : syracuseStep 590327 = 885491) B885491
theorem B262655 : Blo 115785 262655 := bstep (se 1 (by rfl) ⟨196991, by rfl⟩ : syracuseStep 262655 = 393983) B393983
theorem B197147 : Blo 115785 197147 := bstep (se 1 (by rfl) ⟨147860, by rfl⟩ : syracuseStep 197147 = 295721) B295721
theorem B1115005 : Blo 115785 1115005 := bstep (se 3 (by rfl) ⟨209063, by rfl⟩ : syracuseStep 1115005 = 418127) B418127
theorem B6849683 : Blo 115785 6849683 := bstep (se 1 (by rfl) ⟨5137262, by rfl⟩ : syracuseStep 6849683 = 10274525) B10274525
theorem B755183 : Blo 115785 755183 := bstep (se 1 (by rfl) ⟨566387, by rfl⟩ : syracuseStep 755183 = 1132775) B1132775
theorem B263753 : Blo 115785 263753 := bstep (se 2 (by rfl) ⟨98907, by rfl⟩ : syracuseStep 263753 = 197815) B197815
theorem B591623 : Blo 115785 591623 := bstep (se 1 (by rfl) ⟨443717, by rfl⟩ : syracuseStep 591623 = 887435) B887435
theorem B264095 : Blo 115785 264095 := bstep (se 1 (by rfl) ⟨198071, by rfl⟩ : syracuseStep 264095 = 396143) B396143
theorem B166303 : Blo 115785 166303 := bstep (se 1 (by rfl) ⟨124727, by rfl⟩ : syracuseStep 166303 = 249455) B249455
theorem B265247 : Blo 115785 265247 := bstep (se 1 (by rfl) ⟨198935, by rfl⟩ : syracuseStep 265247 = 397871) B397871
theorem B199847 : Blo 115785 199847 := bstep (se 1 (by rfl) ⟨149885, by rfl⟩ : syracuseStep 199847 = 299771) B299771
theorem B265481 : Blo 115785 265481 := bstep (se 2 (by rfl) ⟨99555, by rfl⟩ : syracuseStep 265481 = 199111) B199111
theorem B298687 : Blo 115785 298687 := bstep (se 1 (by rfl) ⟨224015, by rfl⟩ : syracuseStep 298687 = 448031) B448031
theorem B430055 : Blo 115785 430055 := bstep (se 1 (by rfl) ⟨322541, by rfl⟩ : syracuseStep 430055 = 645083) B645083
theorem B397385 : Blo 115785 397385 := bstep (se 2 (by rfl) ⟨149019, by rfl⟩ : syracuseStep 397385 = 298039) B298039
theorem B266651 : Blo 115785 266651 := bstep (se 1 (by rfl) ⟨199988, by rfl⟩ : syracuseStep 266651 = 399977) B399977
theorem B1282553 : Blo 115785 1282553 := bstep (se 2 (by rfl) ⟨480957, by rfl⟩ : syracuseStep 1282553 = 961915) B961915
theorem B594539 : Blo 115785 594539 := bstep (se 1 (by rfl) ⟨445904, by rfl⟩ : syracuseStep 594539 = 891809) B891809
theorem B398519 : Blo 115785 398519 := bstep (se 1 (by rfl) ⟨298889, by rfl⟩ : syracuseStep 398519 = 597779) B597779
theorem B824603 : Blo 115785 824603 := bstep (se 1 (by rfl) ⟨618452, by rfl⟩ : syracuseStep 824603 = 1236905) B1236905
theorem B267767 : Blo 115785 267767 := bstep (se 1 (by rfl) ⟨200825, by rfl⟩ : syracuseStep 267767 = 401651) B401651
theorem B398843 : Blo 115785 398843 := bstep (se 1 (by rfl) ⟨299132, by rfl⟩ : syracuseStep 398843 = 598265) B598265
theorem B628319 : Blo 115785 628319 := bstep (se 1 (by rfl) ⟨471239, by rfl⟩ : syracuseStep 628319 = 942479) B942479
theorem B727003 : Blo 115785 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B301279 : Blo 115785 301279 := bstep (se 1 (by rfl) ⟨225959, by rfl⟩ : syracuseStep 301279 = 451919) B451919
theorem B399869 : Blo 115785 399869 := bstep (se 3 (by rfl) ⟨74975, by rfl⟩ : syracuseStep 399869 = 149951) B149951
theorem B727879 : Blo 115785 727879 := bstep (se 1 (by rfl) ⟨545909, by rfl⟩ : syracuseStep 727879 = 1091819) B1091819
theorem B3022055 : Blo 115785 3022055 := bstep (se 1 (by rfl) ⟨2266541, by rfl⟩ : syracuseStep 3022055 = 4533083) B4533083
theorem B990953 : Blo 115785 990953 := bstep (se 2 (by rfl) ⟨371607, by rfl⟩ : syracuseStep 990953 = 743215) B743215
theorem B859901 : Blo 115785 859901 := bstep (se 3 (by rfl) ⟨161231, by rfl⟩ : syracuseStep 859901 = 322463) B322463
theorem B2236481 : Blo 115785 2236481 := bstep (se 2 (by rfl) ⟨838680, by rfl⟩ : syracuseStep 2236481 = 1677361) B1677361
theorem B958567 : Blo 115785 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B500413 : Blo 115785 500413 := bstep (se 3 (by rfl) ⟨93827, by rfl⟩ : syracuseStep 500413 = 187655) B187655
theorem B2171897 : Blo 115785 2171897 := bstep (se 2 (by rfl) ⟨814461, by rfl⟩ : syracuseStep 2171897 = 1628923) B1628923
theorem B402569 : Blo 115785 402569 := bstep (se 2 (by rfl) ⟨150963, by rfl⟩ : syracuseStep 402569 = 301927) B301927
theorem B173723 : Blo 115785 173723 := bstep (se 1 (by rfl) ⟨130292, by rfl⟩ : syracuseStep 173723 = 260585) B260585
theorem B599723 : Blo 115785 599723 := bstep (se 1 (by rfl) ⟨449792, by rfl⟩ : syracuseStep 599723 = 899585) B899585
theorem B173807 : Blo 115785 173807 := bstep (se 1 (by rfl) ⟨130355, by rfl⟩ : syracuseStep 173807 = 260711) B260711
theorem B501815 : Blo 115785 501815 := bstep (se 1 (by rfl) ⟨376361, by rfl⟩ : syracuseStep 501815 = 752723) B752723
theorem B338003 : Blo 115785 338003 := bstep (se 1 (by rfl) ⟨253502, by rfl⟩ : syracuseStep 338003 = 507005) B507005
theorem B174647 : Blo 115785 174647 := bstep (se 1 (by rfl) ⟨130985, by rfl⟩ : syracuseStep 174647 = 261971) B261971
theorem B174719 : Blo 115785 174719 := bstep (se 1 (by rfl) ⟨131039, by rfl⟩ : syracuseStep 174719 = 262079) B262079
theorem B175259 : Blo 115785 175259 := bstep (se 1 (by rfl) ⟨131444, by rfl⟩ : syracuseStep 175259 = 262889) B262889
theorem B371927 : Blo 115785 371927 := bstep (se 1 (by rfl) ⟨278945, by rfl⟩ : syracuseStep 371927 = 557891) B557891
theorem B503147 : Blo 115785 503147 := bstep (se 1 (by rfl) ⟨377360, by rfl⟩ : syracuseStep 503147 = 754721) B754721
theorem B176363 : Blo 115785 176363 := bstep (se 1 (by rfl) ⟨132272, by rfl⟩ : syracuseStep 176363 = 264545) B264545
theorem B1520207 : Blo 115785 1520207 := bstep (se 1 (by rfl) ⟨1140155, by rfl⟩ : syracuseStep 1520207 = 2280311) B2280311
theorem B176777 : Blo 115785 176777 := bstep (se 2 (by rfl) ⟨66291, by rfl⟩ : syracuseStep 176777 = 132583) B132583
theorem B603773 : Blo 115785 603773 := bstep (se 3 (by rfl) ⟨113207, by rfl⟩ : syracuseStep 603773 = 226415) B226415
theorem B177791 : Blo 115785 177791 := bstep (se 1 (by rfl) ⟨133343, by rfl⟩ : syracuseStep 177791 = 266687) B266687
theorem B899099 : Blo 115785 899099 := bstep (se 1 (by rfl) ⟨674324, by rfl⟩ : syracuseStep 899099 = 1348649) B1348649
theorem B178601 : Blo 115785 178601 := bstep (se 2 (by rfl) ⟨66975, by rfl⟩ : syracuseStep 178601 = 133951) B133951
theorem B178655 : Blo 115785 178655 := bstep (se 1 (by rfl) ⟨133991, by rfl⟩ : syracuseStep 178655 = 267983) B267983
theorem B440923 : Blo 115785 440923 := bstep (se 1 (by rfl) ⟨330692, by rfl⟩ : syracuseStep 440923 = 661385) B661385
theorem B178799 : Blo 115785 178799 := bstep (se 1 (by rfl) ⟨134099, by rfl⟩ : syracuseStep 178799 = 268199) B268199
theorem B179015 : Blo 115785 179015 := bstep (se 1 (by rfl) ⟨134261, by rfl⟩ : syracuseStep 179015 = 268523) B268523
theorem B179231 : Blo 115785 179231 := bstep (se 1 (by rfl) ⟨134423, by rfl⟩ : syracuseStep 179231 = 268847) B268847
theorem B1293407 : Blo 115785 1293407 := bstep (se 1 (by rfl) ⟨970055, by rfl⟩ : syracuseStep 1293407 = 1940111) B1940111
theorem B179483 : Blo 115785 179483 := bstep (se 1 (by rfl) ⟨134612, by rfl⟩ : syracuseStep 179483 = 269225) B269225
theorem B835913 : Blo 115785 835913 := bstep (se 2 (by rfl) ⟨313467, by rfl⟩ : syracuseStep 835913 = 626935) B626935
theorem B1262141 : Blo 115785 1262141 := bstep (se 3 (by rfl) ⟨236651, by rfl⟩ : syracuseStep 1262141 = 473303) B473303
theorem B607175 : Blo 115785 607175 := bstep (se 1 (by rfl) ⟨455381, by rfl⟩ : syracuseStep 607175 = 910763) B910763
theorem B148711 : Blo 115785 148711 := bstep (se 1 (by rfl) ⟨111533, by rfl⟩ : syracuseStep 148711 = 223067) B223067
theorem B116191 : Blo 115785 116191 := bstep (se 1 (by rfl) ⟨87143, by rfl⟩ : syracuseStep 116191 = 174287) B174287
theorem B116463 : Blo 115785 116463 := bstep (se 1 (by rfl) ⟨87347, by rfl⟩ : syracuseStep 116463 = 174695) B174695
theorem B379001 : Blo 115785 379001 := bstep (se 2 (by rfl) ⟨142125, by rfl⟩ : syracuseStep 379001 = 284251) B284251
theorem B117231 : Blo 115785 117231 := bstep (se 1 (by rfl) ⟨87923, by rfl⟩ : syracuseStep 117231 = 175847) B175847
theorem B674507 : Blo 115785 674507 := bstep (se 1 (by rfl) ⟨505880, by rfl⟩ : syracuseStep 674507 = 1011761) B1011761
theorem B117695 : Blo 115785 117695 := bstep (se 1 (by rfl) ⟨88271, by rfl⟩ : syracuseStep 117695 = 176543) B176543
theorem B969731 : Blo 115785 969731 := bstep (se 1 (by rfl) ⟨727298, by rfl⟩ : syracuseStep 969731 = 1454597) B1454597
theorem B445601 : Blo 115785 445601 := bstep (se 2 (by rfl) ⟨167100, by rfl⟩ : syracuseStep 445601 = 334201) B334201
theorem B118119 : Blo 115785 118119 := bstep (se 1 (by rfl) ⟨88589, by rfl⟩ : syracuseStep 118119 = 177179) B177179
theorem B282089 : Blo 115785 282089 := bstep (se 2 (by rfl) ⟨105783, by rfl⟩ : syracuseStep 282089 = 211567) B211567
theorem B3395317 : Blo 115785 3395317 := bstep (se 5 (by rfl) ⟨159155, by rfl⟩ : syracuseStep 3395317 = 318311) B318311
theorem B2543723 : Blo 115785 2543723 := bstep (se 1 (by rfl) ⟨1907792, by rfl⟩ : syracuseStep 2543723 = 3815585) B3815585
theorem B446573 : Blo 115785 446573 := bstep (se 3 (by rfl) ⟨83732, by rfl⟩ : syracuseStep 446573 = 167465) B167465
theorem B675965 : Blo 115785 675965 := bstep (se 3 (by rfl) ⟨126743, by rfl⟩ : syracuseStep 675965 = 253487) B253487
theorem B708983 : Blo 115785 708983 := bstep (se 1 (by rfl) ⟨531737, by rfl⟩ : syracuseStep 708983 = 1063475) B1063475
theorem B807479 : Blo 115785 807479 := bstep (se 1 (by rfl) ⟨605609, by rfl⟩ : syracuseStep 807479 = 1211219) B1211219
theorem B119387 : Blo 115785 119387 := bstep (se 1 (by rfl) ⟨89540, by rfl⟩ : syracuseStep 119387 = 179081) B179081
theorem B152231 : Blo 115785 152231 := bstep (se 1 (by rfl) ⟨114173, by rfl⟩ : syracuseStep 152231 = 228347) B228347
theorem B1037033 : Blo 115785 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B447227 : Blo 115785 447227 := bstep (se 1 (by rfl) ⟨335420, by rfl⟩ : syracuseStep 447227 = 670841) B670841
theorem B218603 : Blo 115785 218603 := bstep (se 1 (by rfl) ⟨163952, by rfl⟩ : syracuseStep 218603 = 327905) B327905
theorem B449003 : Blo 115785 449003 := bstep (se 1 (by rfl) ⟨336752, by rfl⟩ : syracuseStep 449003 = 673505) B673505
theorem B3103217 : Blo 115785 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B907847 : Blo 115785 907847 := bstep (se 1 (by rfl) ⟨680885, by rfl⟩ : syracuseStep 907847 = 1361771) B1361771
theorem B1203335 : Blo 115785 1203335 := bstep (se 1 (by rfl) ⟨902501, by rfl⟩ : syracuseStep 1203335 = 1805003) B1805003
theorem B321167 : Blo 115785 321167 := bstep (se 1 (by rfl) ⟨240875, by rfl⟩ : syracuseStep 321167 = 481751) B481751
theorem B5891869 : Blo 115785 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B681979 : Blo 115785 681979 := bstep (se 1 (by rfl) ⟨511484, by rfl⟩ : syracuseStep 681979 = 1022969) B1022969
theorem B2746667 : Blo 115785 2746667 := bstep (se 1 (by rfl) ⟨2060000, by rfl⟩ : syracuseStep 2746667 = 4120001) B4120001
theorem B191423 : Blo 115785 191423 := bstep (se 1 (by rfl) ⟨143567, by rfl⟩ : syracuseStep 191423 = 287135) B287135
theorem B748673 : Blo 115785 748673 := bstep (se 2 (by rfl) ⟨280752, by rfl⟩ : syracuseStep 748673 = 561505) B561505
theorem B749033 : Blo 115785 749033 := bstep (se 2 (by rfl) ⟨280887, by rfl⟩ : syracuseStep 749033 = 561775) B561775
theorem B1699967 : Blo 115785 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B1012961 : Blo 115785 1012961 := bstep (se 2 (by rfl) ⟨379860, by rfl⟩ : syracuseStep 1012961 = 759721) B759721
theorem B882089 : Blo 115785 882089 := bstep (se 2 (by rfl) ⟨330783, by rfl⟩ : syracuseStep 882089 = 661567) B661567
theorem B849959 : Blo 115785 849959 := bstep (se 1 (by rfl) ⟨637469, by rfl⟩ : syracuseStep 849959 = 1274939) B1274939
theorem B260891 : Blo 115785 260891 := bstep (se 1 (by rfl) ⟨195668, by rfl⟩ : syracuseStep 260891 = 391337) B391337
theorem B392201 : Blo 115785 392201 := bstep (se 2 (by rfl) ⟨147075, by rfl⟩ : syracuseStep 392201 = 294151) B294151
theorem B2882587 : Blo 115785 2882587 := bstep (se 1 (by rfl) ⟨2161940, by rfl⟩ : syracuseStep 2882587 = 4323881) B4323881
theorem B261611 : Blo 115785 261611 := bstep (se 1 (by rfl) ⟨196208, by rfl⟩ : syracuseStep 261611 = 392417) B392417
theorem B1278089 : Blo 115785 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B557275 : Blo 115785 557275 := bstep (se 1 (by rfl) ⟨417956, by rfl⟩ : syracuseStep 557275 = 835913) B835913
theorem B393551 : Blo 115785 393551 := bstep (se 1 (by rfl) ⟨295163, by rfl⟩ : syracuseStep 393551 = 590327) B590327
theorem B131431 : Blo 115785 131431 := bstep (se 1 (by rfl) ⟨98573, by rfl⟩ : syracuseStep 131431 = 197147) B197147
theorem B4981421 : Blo 115785 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B394415 : Blo 115785 394415 := bstep (se 1 (by rfl) ⟨295811, by rfl⟩ : syracuseStep 394415 = 591623) B591623
theorem B198281 : Blo 115785 198281 := bstep (se 2 (by rfl) ⟨74355, by rfl⟩ : syracuseStep 198281 = 148711) B148711
theorem B297067 : Blo 115785 297067 := bstep (se 1 (by rfl) ⟨222800, by rfl⟩ : syracuseStep 297067 = 445601) B445601
theorem B133231 : Blo 115785 133231 := bstep (se 1 (by rfl) ⟨99923, by rfl⟩ : syracuseStep 133231 = 199847) B199847
theorem B886949 : Blo 115785 886949 := bstep (se 4 (by rfl) ⟨83151, by rfl⟩ : syracuseStep 886949 = 166303) B166303
theorem B264923 : Blo 115785 264923 := bstep (se 1 (by rfl) ⟨198692, by rfl⟩ : syracuseStep 264923 = 397385) B397385
theorem B297715 : Blo 115785 297715 := bstep (se 1 (by rfl) ⟨223286, by rfl⟩ : syracuseStep 297715 = 446573) B446573
theorem B855035 : Blo 115785 855035 := bstep (se 1 (by rfl) ⟨641276, by rfl⟩ : syracuseStep 855035 = 1282553) B1282553
theorem B396359 : Blo 115785 396359 := bstep (se 1 (by rfl) ⟨297269, by rfl⟩ : syracuseStep 396359 = 594539) B594539
theorem B691355 : Blo 115785 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B298151 : Blo 115785 298151 := bstep (se 1 (by rfl) ⟨223613, by rfl⟩ : syracuseStep 298151 = 447227) B447227
theorem B265679 : Blo 115785 265679 := bstep (se 1 (by rfl) ⟨199259, by rfl⟩ : syracuseStep 265679 = 398519) B398519
theorem B265895 : Blo 115785 265895 := bstep (se 1 (by rfl) ⟨199421, by rfl⟩ : syracuseStep 265895 = 398843) B398843
theorem B299335 : Blo 115785 299335 := bstep (se 1 (by rfl) ⟨224501, by rfl⟩ : syracuseStep 299335 = 449003) B449003
theorem B2068811 : Blo 115785 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B266579 : Blo 115785 266579 := bstep (se 1 (by rfl) ⟨199934, by rfl⟩ : syracuseStep 266579 = 399869) B399869
theorem B398249 : Blo 115785 398249 := bstep (se 2 (by rfl) ⟨149343, by rfl⟩ : syracuseStep 398249 = 298687) B298687
theorem B4527089 : Blo 115785 4527089 := bstep (se 2 (by rfl) ⟨1697658, by rfl⟩ : syracuseStep 4527089 = 3395317) B3395317
theorem B660635 : Blo 115785 660635 := bstep (se 1 (by rfl) ⟨495476, by rfl⟩ : syracuseStep 660635 = 990953) B990953
theorem B1447931 : Blo 115785 1447931 := bstep (se 1 (by rfl) ⟨1085948, by rfl⟩ : syracuseStep 1447931 = 2171897) B2171897
theorem B268379 : Blo 115785 268379 := bstep (se 1 (by rfl) ⟨201284, by rfl⟩ : syracuseStep 268379 = 402569) B402569
theorem B399815 : Blo 115785 399815 := bstep (se 1 (by rfl) ⟨299861, by rfl⟩ : syracuseStep 399815 = 599723) B599723
theorem B334543 : Blo 115785 334543 := bstep (se 1 (by rfl) ⟨250907, by rfl⟩ : syracuseStep 334543 = 501815) B501815
theorem B499115 : Blo 115785 499115 := bstep (se 1 (by rfl) ⟨374336, by rfl⟩ : syracuseStep 499115 = 748673) B748673
theorem B335431 : Blo 115785 335431 := bstep (se 1 (by rfl) ⟨251573, by rfl⟩ : syracuseStep 335431 = 503147) B503147
theorem B499355 : Blo 115785 499355 := bstep (se 1 (by rfl) ⟨374516, by rfl⟩ : syracuseStep 499355 = 749033) B749033
theorem B401705 : Blo 115785 401705 := bstep (se 2 (by rfl) ⟨150639, by rfl⟩ : syracuseStep 401705 = 301279) B301279
theorem B402515 : Blo 115785 402515 := bstep (se 1 (by rfl) ⟨301886, by rfl⟩ : syracuseStep 402515 = 603773) B603773
theorem B599399 : Blo 115785 599399 := bstep (se 1 (by rfl) ⟨449549, by rfl⟩ : syracuseStep 599399 = 899099) B899099
theorem B566639 : Blo 115785 566639 := bstep (se 1 (by rfl) ⟨424979, by rfl⟩ : syracuseStep 566639 = 849959) B849959
theorem B3843449 : Blo 115785 3843449 := bstep (se 2 (by rfl) ⟨1441293, by rfl⟩ : syracuseStep 3843449 = 2882587) B2882587
theorem B173927 : Blo 115785 173927 := bstep (se 1 (by rfl) ⟨130445, by rfl⟩ : syracuseStep 173927 = 260891) B260891
theorem B862271 : Blo 115785 862271 := bstep (se 1 (by rfl) ⟨646703, by rfl⟩ : syracuseStep 862271 = 1293407) B1293407
theorem B174407 : Blo 115785 174407 := bstep (se 1 (by rfl) ⟨130805, by rfl⟩ : syracuseStep 174407 = 261611) B261611
theorem B175103 : Blo 115785 175103 := bstep (se 1 (by rfl) ⟨131327, by rfl⟩ : syracuseStep 175103 = 262655) B262655
theorem B404783 : Blo 115785 404783 := bstep (se 1 (by rfl) ⟨303587, by rfl⟩ : syracuseStep 404783 = 607175) B607175
theorem B4566455 : Blo 115785 4566455 := bstep (se 1 (by rfl) ⟨3424841, by rfl⟩ : syracuseStep 4566455 = 6849683) B6849683
theorem B667217 : Blo 115785 667217 := bstep (se 2 (by rfl) ⟨250206, by rfl⟩ : syracuseStep 667217 = 500413) B500413
theorem B503455 : Blo 115785 503455 := bstep (se 1 (by rfl) ⟨377591, by rfl⟩ : syracuseStep 503455 = 755183) B755183
theorem B175835 : Blo 115785 175835 := bstep (se 1 (by rfl) ⟨131876, by rfl⟩ : syracuseStep 175835 = 263753) B263753
theorem B1486673 : Blo 115785 1486673 := bstep (se 2 (by rfl) ⟨557502, by rfl⟩ : syracuseStep 1486673 = 1115005) B1115005
theorem B176063 : Blo 115785 176063 := bstep (se 1 (by rfl) ⟨132047, by rfl⟩ : syracuseStep 176063 = 264095) B264095
theorem B176831 : Blo 115785 176831 := bstep (se 1 (by rfl) ⟨132623, by rfl⟩ : syracuseStep 176831 = 265247) B265247
theorem B176987 : Blo 115785 176987 := bstep (se 1 (by rfl) ⟨132740, by rfl⟩ : syracuseStep 176987 = 265481) B265481
theorem B472655 : Blo 115785 472655 := bstep (se 1 (by rfl) ⟨354491, by rfl⟩ : syracuseStep 472655 = 708983) B708983
theorem B177767 : Blo 115785 177767 := bstep (se 1 (by rfl) ⟨133325, by rfl⟩ : syracuseStep 177767 = 266651) B266651
theorem B8795765 : Blo 115785 8795765 := bstep (se 5 (by rfl) ⟨412301, by rfl⟩ : syracuseStep 8795765 = 824603) B824603
theorem B538319 : Blo 115785 538319 := bstep (se 1 (by rfl) ⟨403739, by rfl⟩ : syracuseStep 538319 = 807479) B807479
theorem B178511 : Blo 115785 178511 := bstep (se 1 (by rfl) ⟨133883, by rfl⟩ : syracuseStep 178511 = 267767) B267767
theorem B605231 : Blo 115785 605231 := bstep (se 1 (by rfl) ⟨453923, by rfl⟩ : syracuseStep 605231 = 907847) B907847
theorem B802223 : Blo 115785 802223 := bstep (se 1 (by rfl) ⟨601667, by rfl⟩ : syracuseStep 802223 = 1203335) B1203335
theorem B2014703 : Blo 115785 2014703 := bstep (se 1 (by rfl) ⟨1511027, by rfl⟩ : syracuseStep 2014703 = 3022055) B3022055
theorem B1490987 : Blo 115785 1490987 := bstep (se 1 (by rfl) ⟨1118240, by rfl⟩ : syracuseStep 1490987 = 2236481) B2236481
theorem B7324445 : Blo 115785 7324445 := bstep (se 3 (by rfl) ⟨1373333, by rfl⟩ : syracuseStep 7324445 = 2746667) B2746667
theorem B214111 : Blo 115785 214111 := bstep (se 1 (by rfl) ⟨160583, by rfl⟩ : syracuseStep 214111 = 321167) B321167
theorem B115815 : Blo 115785 115815 := bstep (se 1 (by rfl) ⟨86861, by rfl⟩ : syracuseStep 115815 = 173723) B173723
theorem B115871 : Blo 115785 115871 := bstep (se 1 (by rfl) ⟨86903, by rfl⟩ : syracuseStep 115871 = 173807) B173807
theorem B116431 : Blo 115785 116431 := bstep (se 1 (by rfl) ⟨87323, by rfl⟩ : syracuseStep 116431 = 174647) B174647
theorem B1623797 : Blo 115785 1623797 := bstep (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) B152231
theorem B116479 : Blo 115785 116479 := bstep (se 1 (by rfl) ⟨87359, by rfl⟩ : syracuseStep 116479 = 174719) B174719
theorem B116839 : Blo 115785 116839 := bstep (se 1 (by rfl) ⟨87629, by rfl⟩ : syracuseStep 116839 = 175259) B175259
theorem B247951 : Blo 115785 247951 := bstep (se 1 (by rfl) ⟨185963, by rfl⟩ : syracuseStep 247951 = 371927) B371927
theorem B510461 : Blo 115785 510461 := bstep (se 3 (by rfl) ⟨95711, by rfl⟩ : syracuseStep 510461 = 191423) B191423
theorem B969337 : Blo 115785 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B1133311 : Blo 115785 1133311 := bstep (se 1 (by rfl) ⟨849983, by rfl⟩ : syracuseStep 1133311 = 1699967) B1699967
theorem B117575 : Blo 115785 117575 := bstep (se 1 (by rfl) ⟨88181, by rfl⟩ : syracuseStep 117575 = 176363) B176363
theorem B117851 : Blo 115785 117851 := bstep (se 1 (by rfl) ⟨88388, by rfl⟩ : syracuseStep 117851 = 176777) B176777
theorem B675307 : Blo 115785 675307 := bstep (se 1 (by rfl) ⟨506480, by rfl⟩ : syracuseStep 675307 = 1012961) B1012961
theorem B118527 : Blo 115785 118527 := bstep (se 1 (by rfl) ⟨88895, by rfl⟩ : syracuseStep 118527 = 177791) B177791
theorem B970505 : Blo 115785 970505 := bstep (se 2 (by rfl) ⟨363939, by rfl⟩ : syracuseStep 970505 = 727879) B727879
theorem B119067 : Blo 115785 119067 := bstep (se 1 (by rfl) ⟨89300, by rfl⟩ : syracuseStep 119067 = 178601) B178601
theorem B119103 : Blo 115785 119103 := bstep (se 1 (by rfl) ⟨89327, by rfl⟩ : syracuseStep 119103 = 178655) B178655
theorem B119199 : Blo 115785 119199 := bstep (se 1 (by rfl) ⟨89399, by rfl⟩ : syracuseStep 119199 = 178799) B178799
theorem B119343 : Blo 115785 119343 := bstep (se 1 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 119343 = 179015) B179015
theorem B119487 : Blo 115785 119487 := bstep (se 1 (by rfl) ⟨89615, by rfl⟩ : syracuseStep 119487 = 179231) B179231
theorem B119655 : Blo 115785 119655 := bstep (se 1 (by rfl) ⟨89741, by rfl⟩ : syracuseStep 119655 = 179483) B179483
theorem B939599 : Blo 115785 939599 := bstep (se 1 (by rfl) ⟨704699, by rfl⟩ : syracuseStep 939599 = 1409399) B1409399
theorem B841427 : Blo 115785 841427 := bstep (se 1 (by rfl) ⟨631070, by rfl⟩ : syracuseStep 841427 = 1262141) B1262141
theorem B252667 : Blo 115785 252667 := bstep (se 1 (by rfl) ⟨189500, by rfl⟩ : syracuseStep 252667 = 379001) B379001
theorem B449671 : Blo 115785 449671 := bstep (se 1 (by rfl) ⟨337253, by rfl⟩ : syracuseStep 449671 = 674507) B674507
theorem B646487 : Blo 115785 646487 := bstep (se 1 (by rfl) ⟨484865, by rfl⟩ : syracuseStep 646487 = 969731) B969731
theorem B7855825 : Blo 115785 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B286703 : Blo 115785 286703 := bstep (se 1 (by rfl) ⟨215027, by rfl⟩ : syracuseStep 286703 = 430055) B430055
theorem B909305 : Blo 115785 909305 := bstep (se 2 (by rfl) ⟨340989, by rfl⟩ : syracuseStep 909305 = 681979) B681979
theorem B1695815 : Blo 115785 1695815 := bstep (se 1 (by rfl) ⟨1271861, by rfl⟩ : syracuseStep 1695815 = 2543723) B2543723
theorem B450643 : Blo 115785 450643 := bstep (se 1 (by rfl) ⟨337982, by rfl⟩ : syracuseStep 450643 = 675965) B675965
theorem B418879 : Blo 115785 418879 := bstep (se 1 (by rfl) ⟨314159, by rfl⟩ : syracuseStep 418879 = 628319) B628319
theorem B582941 : Blo 115785 582941 := bstep (se 3 (by rfl) ⟨109301, by rfl⟩ : syracuseStep 582941 = 218603) B218603
theorem B225335 : Blo 115785 225335 := bstep (se 1 (by rfl) ⟨169001, by rfl⟩ : syracuseStep 225335 = 338003) B338003
theorem B1013471 : Blo 115785 1013471 := bstep (se 1 (by rfl) ⟨760103, by rfl⟩ : syracuseStep 1013471 = 1520207) B1520207
theorem B587897 : Blo 115785 587897 := bstep (se 2 (by rfl) ⟨220461, by rfl⟩ : syracuseStep 587897 = 440923) B440923
theorem B588059 : Blo 115785 588059 := bstep (se 1 (by rfl) ⟨441044, by rfl⟩ : syracuseStep 588059 = 882089) B882089
theorem B752237 : Blo 115785 752237 := bstep (se 3 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 752237 = 282089) B282089
theorem B2293069 : Blo 115785 2293069 := bstep (se 3 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 2293069 = 859901) B859901
theorem B261467 : Blo 115785 261467 := bstep (se 1 (by rfl) ⟨196100, by rfl⟩ : syracuseStep 261467 = 392201) B392201
theorem B852059 : Blo 115785 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B262367 : Blo 115785 262367 := bstep (se 1 (by rfl) ⟨196775, by rfl⟩ : syracuseStep 262367 = 393551) B393551
theorem B4882963 : Blo 115785 4882963 := bstep (se 1 (by rfl) ⟨3662222, by rfl⟩ : syracuseStep 4882963 = 7324445) B7324445
theorem B262943 : Blo 115785 262943 := bstep (se 1 (by rfl) ⟨197207, by rfl⟩ : syracuseStep 262943 = 394415) B394415
theorem B132187 : Blo 115785 132187 := bstep (se 1 (by rfl) ⟨99140, by rfl⟩ : syracuseStep 132187 = 198281) B198281
theorem B1082531 : Blo 115785 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B558505 : Blo 115785 558505 := bstep (se 2 (by rfl) ⟨209439, by rfl⟩ : syracuseStep 558505 = 418879) B418879
theorem B591299 : Blo 115785 591299 := bstep (se 1 (by rfl) ⟨443474, by rfl⟩ : syracuseStep 591299 = 886949) B886949
theorem B264239 : Blo 115785 264239 := bstep (se 1 (by rfl) ⟨198179, by rfl⟩ : syracuseStep 264239 = 396359) B396359
theorem B460903 : Blo 115785 460903 := bstep (se 1 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 460903 = 691355) B691355
theorem B198767 : Blo 115785 198767 := bstep (se 1 (by rfl) ⟨149075, by rfl⟩ : syracuseStep 198767 = 298151) B298151
theorem B396089 : Blo 115785 396089 := bstep (se 2 (by rfl) ⟨148533, by rfl⟩ : syracuseStep 396089 = 297067) B297067
theorem B1379207 : Blo 115785 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B265499 : Blo 115785 265499 := bstep (se 1 (by rfl) ⟨199124, by rfl⟩ : syracuseStep 265499 = 398249) B398249
theorem B3018059 : Blo 115785 3018059 := bstep (se 1 (by rfl) ⟨2263544, by rfl⟩ : syracuseStep 3018059 = 4527089) B4527089
theorem B396953 : Blo 115785 396953 := bstep (se 2 (by rfl) ⟨148857, by rfl⟩ : syracuseStep 396953 = 297715) B297715
theorem B1511081 : Blo 115785 1511081 := bstep (se 2 (by rfl) ⟨566655, by rfl⟩ : syracuseStep 1511081 = 1133311) B1133311
theorem B626399 : Blo 115785 626399 := bstep (se 1 (by rfl) ⟨469799, by rfl⟩ : syracuseStep 626399 = 939599) B939599
theorem B560951 : Blo 115785 560951 := bstep (se 1 (by rfl) ⟨420713, by rfl⟩ : syracuseStep 560951 = 841427) B841427
theorem B266543 : Blo 115785 266543 := bstep (se 1 (by rfl) ⟨199907, by rfl⟩ : syracuseStep 266543 = 399815) B399815
theorem B430991 : Blo 115785 430991 := bstep (se 1 (by rfl) ⟨323243, by rfl⟩ : syracuseStep 430991 = 646487) B646487
theorem B332743 : Blo 115785 332743 := bstep (se 1 (by rfl) ⟨249557, by rfl⟩ : syracuseStep 332743 = 499115) B499115
theorem B332903 : Blo 115785 332903 := bstep (se 1 (by rfl) ⟨249677, by rfl⟩ : syracuseStep 332903 = 499355) B499355
theorem B267803 : Blo 115785 267803 := bstep (se 1 (by rfl) ⟨200852, by rfl⟩ : syracuseStep 267803 = 401705) B401705
theorem B399113 : Blo 115785 399113 := bstep (se 2 (by rfl) ⟨149667, by rfl⟩ : syracuseStep 399113 = 299335) B299335
theorem B268343 : Blo 115785 268343 := bstep (se 1 (by rfl) ⟨201257, by rfl⟩ : syracuseStep 268343 = 402515) B402515
theorem B399599 : Blo 115785 399599 := bstep (se 1 (by rfl) ⟨299699, by rfl⟩ : syracuseStep 399599 = 599399) B599399
theorem B2562299 : Blo 115785 2562299 := bstep (se 1 (by rfl) ⟨1921724, by rfl⟩ : syracuseStep 2562299 = 3843449) B3843449
theorem B269855 : Blo 115785 269855 := bstep (se 1 (by rfl) ⟨202391, by rfl⟩ : syracuseStep 269855 = 404783) B404783
theorem B991115 : Blo 115785 991115 := bstep (se 1 (by rfl) ⟨743336, by rfl⟩ : syracuseStep 991115 = 1486673) B1486673
theorem B336889 : Blo 115785 336889 := bstep (se 2 (by rfl) ⟨126333, by rfl⟩ : syracuseStep 336889 = 252667) B252667
theorem B599561 : Blo 115785 599561 := bstep (se 2 (by rfl) ⟨224835, by rfl⟩ : syracuseStep 599561 = 449671) B449671
theorem B501491 : Blo 115785 501491 := bstep (se 1 (by rfl) ⟨376118, by rfl⟩ : syracuseStep 501491 = 752237) B752237
theorem B3057425 : Blo 115785 3057425 := bstep (se 2 (by rfl) ⟨1146534, by rfl⟩ : syracuseStep 3057425 = 2293069) B2293069
theorem B403487 : Blo 115785 403487 := bstep (se 1 (by rfl) ⟨302615, by rfl⟩ : syracuseStep 403487 = 605231) B605231
theorem B174311 : Blo 115785 174311 := bstep (se 1 (by rfl) ⟨130733, by rfl⟩ : syracuseStep 174311 = 261467) B261467
theorem B534815 : Blo 115785 534815 := bstep (se 1 (by rfl) ⟨401111, by rfl⟩ : syracuseStep 534815 = 802223) B802223
theorem B993991 : Blo 115785 993991 := bstep (se 1 (by rfl) ⟨745493, by rfl⟩ : syracuseStep 993991 = 1490987) B1490987
theorem B600857 : Blo 115785 600857 := bstep (se 2 (by rfl) ⟨225321, by rfl⟩ : syracuseStep 600857 = 450643) B450643
theorem B3320947 : Blo 115785 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B175241 : Blo 115785 175241 := bstep (se 2 (by rfl) ⟨65715, by rfl⟩ : syracuseStep 175241 = 131431) B131431
theorem B1322405 : Blo 115785 1322405 := bstep (se 4 (by rfl) ⟨123975, by rfl⟩ : syracuseStep 1322405 = 247951) B247951
theorem B340307 : Blo 115785 340307 := bstep (se 1 (by rfl) ⟨255230, by rfl⟩ : syracuseStep 340307 = 510461) B510461
theorem B176615 : Blo 115785 176615 := bstep (se 1 (by rfl) ⟨132461, by rfl⟩ : syracuseStep 176615 = 264923) B264923
theorem B570023 : Blo 115785 570023 := bstep (se 1 (by rfl) ⟨427517, by rfl⟩ : syracuseStep 570023 = 855035) B855035
theorem B177119 : Blo 115785 177119 := bstep (se 1 (by rfl) ⟨132839, by rfl⟩ : syracuseStep 177119 = 265679) B265679
theorem B177263 : Blo 115785 177263 := bstep (se 1 (by rfl) ⟨132947, by rfl⟩ : syracuseStep 177263 = 265895) B265895
theorem B177641 : Blo 115785 177641 := bstep (se 2 (by rfl) ⟨66615, by rfl⟩ : syracuseStep 177641 = 133231) B133231
theorem B177719 : Blo 115785 177719 := bstep (se 1 (by rfl) ⟨133289, by rfl⟩ : syracuseStep 177719 = 266579) B266579
theorem B1554509 : Blo 115785 1554509 := bstep (se 3 (by rfl) ⟨291470, by rfl⟩ : syracuseStep 1554509 = 582941) B582941
theorem B440423 : Blo 115785 440423 := bstep (se 1 (by rfl) ⟨330317, by rfl⟩ : syracuseStep 440423 = 660635) B660635
theorem B1292449 : Blo 115785 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B965287 : Blo 115785 965287 := bstep (se 1 (by rfl) ⟨723965, by rfl⟩ : syracuseStep 965287 = 1447931) B1447931
theorem B178919 : Blo 115785 178919 := bstep (se 1 (by rfl) ⟨134189, by rfl⟩ : syracuseStep 178919 = 268379) B268379
theorem B900409 : Blo 115785 900409 := bstep (se 2 (by rfl) ⟨337653, by rfl⟩ : syracuseStep 900409 = 675307) B675307
theorem B671273 : Blo 115785 671273 := bstep (se 2 (by rfl) ⟨251727, by rfl⟩ : syracuseStep 671273 = 503455) B503455
theorem B606203 : Blo 115785 606203 := bstep (se 1 (by rfl) ⟨454652, by rfl⟩ : syracuseStep 606203 = 909305) B909305
theorem B1130543 : Blo 115785 1130543 := bstep (se 1 (by rfl) ⟨847907, by rfl⟩ : syracuseStep 1130543 = 1695815) B1695815
theorem B377759 : Blo 115785 377759 := bstep (se 1 (by rfl) ⟨283319, by rfl⟩ : syracuseStep 377759 = 566639) B566639
theorem B115951 : Blo 115785 115951 := bstep (se 1 (by rfl) ⟨86963, by rfl⟩ : syracuseStep 115951 = 173927) B173927
theorem B574847 : Blo 115785 574847 := bstep (se 1 (by rfl) ⟨431135, by rfl⟩ : syracuseStep 574847 = 862271) B862271
theorem B116271 : Blo 115785 116271 := bstep (se 1 (by rfl) ⟨87203, by rfl⟩ : syracuseStep 116271 = 174407) B174407
theorem B116735 : Blo 115785 116735 := bstep (se 1 (by rfl) ⟨87551, by rfl⟩ : syracuseStep 116735 = 175103) B175103
theorem B444811 : Blo 115785 444811 := bstep (se 1 (by rfl) ⟨333608, by rfl⟩ : syracuseStep 444811 = 667217) B667217
theorem B117223 : Blo 115785 117223 := bstep (se 1 (by rfl) ⟨87917, by rfl⟩ : syracuseStep 117223 = 175835) B175835
theorem B117375 : Blo 115785 117375 := bstep (se 1 (by rfl) ⟨88031, by rfl⟩ : syracuseStep 117375 = 176063) B176063
theorem B150223 : Blo 115785 150223 := bstep (se 1 (by rfl) ⟨112667, by rfl⟩ : syracuseStep 150223 = 225335) B225335
theorem B117887 : Blo 115785 117887 := bstep (se 1 (by rfl) ⟨88415, by rfl⟩ : syracuseStep 117887 = 176831) B176831
theorem B117991 : Blo 115785 117991 := bstep (se 1 (by rfl) ⟨88493, by rfl⟩ : syracuseStep 117991 = 176987) B176987
theorem B446057 : Blo 115785 446057 := bstep (se 2 (by rfl) ⟨167271, by rfl⟩ : syracuseStep 446057 = 334543) B334543
theorem B315103 : Blo 115785 315103 := bstep (se 1 (by rfl) ⟨236327, by rfl⟩ : syracuseStep 315103 = 472655) B472655
theorem B118511 : Blo 115785 118511 := bstep (se 1 (by rfl) ⟨88883, by rfl⟩ : syracuseStep 118511 = 177767) B177767
theorem B675647 : Blo 115785 675647 := bstep (se 1 (by rfl) ⟨506735, by rfl⟩ : syracuseStep 675647 = 1013471) B1013471
theorem B119007 : Blo 115785 119007 := bstep (se 1 (by rfl) ⟨89255, by rfl⟩ : syracuseStep 119007 = 178511) B178511
theorem B447241 : Blo 115785 447241 := bstep (se 2 (by rfl) ⟨167715, by rfl⟩ : syracuseStep 447241 = 335431) B335431
theorem B10474433 : Blo 115785 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B743033 : Blo 115785 743033 := bstep (se 2 (by rfl) ⟨278637, by rfl⟩ : syracuseStep 743033 = 557275) B557275
theorem B285481 : Blo 115785 285481 := bstep (se 2 (by rfl) ⟨107055, by rfl⟩ : syracuseStep 285481 = 214111) B214111
theorem B647003 : Blo 115785 647003 := bstep (se 1 (by rfl) ⟨485252, by rfl⟩ : syracuseStep 647003 = 970505) B970505
theorem B191135 : Blo 115785 191135 := bstep (se 1 (by rfl) ⟨143351, by rfl⟩ : syracuseStep 191135 = 286703) B286703
theorem B3044303 : Blo 115785 3044303 := bstep (se 1 (by rfl) ⟨2283227, by rfl⟩ : syracuseStep 3044303 = 4566455) B4566455
theorem B5863843 : Blo 115785 5863843 := bstep (se 1 (by rfl) ⟨4397882, by rfl⟩ : syracuseStep 5863843 = 8795765) B8795765
theorem B358879 : Blo 115785 358879 := bstep (se 1 (by rfl) ⟨269159, by rfl⟩ : syracuseStep 358879 = 538319) B538319
theorem B391931 : Blo 115785 391931 := bstep (se 1 (by rfl) ⟨293948, by rfl⟩ : syracuseStep 391931 = 587897) B587897
theorem B392039 : Blo 115785 392039 := bstep (se 1 (by rfl) ⟨294029, by rfl⟩ : syracuseStep 392039 = 588059) B588059
theorem B1343135 : Blo 115785 1343135 := bstep (se 1 (by rfl) ⟨1007351, by rfl⟩ : syracuseStep 1343135 = 2014703) B2014703
theorem B753695 : Blo 115785 753695 := bstep (se 1 (by rfl) ⟨565271, by rfl⟩ : syracuseStep 753695 = 1130543) B1130543
theorem B394199 : Blo 115785 394199 := bstep (se 1 (by rfl) ⟨295649, by rfl⟩ : syracuseStep 394199 = 591299) B591299
theorem B132511 : Blo 115785 132511 := bstep (se 1 (by rfl) ⟨99383, by rfl⟩ : syracuseStep 132511 = 198767) B198767
theorem B264059 : Blo 115785 264059 := bstep (se 1 (by rfl) ⟨198044, by rfl⟩ : syracuseStep 264059 = 396089) B396089
theorem B919471 : Blo 115785 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B297371 : Blo 115785 297371 := bstep (se 1 (by rfl) ⟨223028, by rfl⟩ : syracuseStep 297371 = 446057) B446057
theorem B264635 : Blo 115785 264635 := bstep (se 1 (by rfl) ⟨198476, by rfl⟩ : syracuseStep 264635 = 396953) B396953
theorem B2886749 : Blo 115785 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B593081 : Blo 115785 593081 := bstep (se 2 (by rfl) ⟨222405, by rfl⟩ : syracuseStep 593081 = 444811) B444811
theorem B6982955 : Blo 115785 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B200297 : Blo 115785 200297 := bstep (se 2 (by rfl) ⟨75111, by rfl⟩ : syracuseStep 200297 = 150223) B150223
theorem B266075 : Blo 115785 266075 := bstep (se 1 (by rfl) ⟨199556, by rfl⟩ : syracuseStep 266075 = 399113) B399113
theorem B4427929 : Blo 115785 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B266399 : Blo 115785 266399 := bstep (se 1 (by rfl) ⟨199799, by rfl⟩ : syracuseStep 266399 = 399599) B399599
theorem B1708199 : Blo 115785 1708199 := bstep (se 1 (by rfl) ⟨1281149, by rfl⟩ : syracuseStep 1708199 = 2562299) B2562299
theorem B431335 : Blo 115785 431335 := bstep (se 1 (by rfl) ⟨323501, by rfl⟩ : syracuseStep 431335 = 647003) B647003
theorem B660743 : Blo 115785 660743 := bstep (se 1 (by rfl) ⟨495557, by rfl⟩ : syracuseStep 660743 = 991115) B991115
theorem B399707 : Blo 115785 399707 := bstep (se 1 (by rfl) ⟨299780, by rfl⟩ : syracuseStep 399707 = 599561) B599561
theorem B596321 : Blo 115785 596321 := bstep (se 2 (by rfl) ⟨223620, by rfl⟩ : syracuseStep 596321 = 447241) B447241
theorem B334327 : Blo 115785 334327 := bstep (se 1 (by rfl) ⟨250745, by rfl⟩ : syracuseStep 334327 = 501491) B501491
theorem B2038283 : Blo 115785 2038283 := bstep (se 1 (by rfl) ⟨1528712, by rfl⟩ : syracuseStep 2038283 = 3057425) B3057425
theorem B268991 : Blo 115785 268991 := bstep (se 1 (by rfl) ⟨201743, by rfl⟩ : syracuseStep 268991 = 403487) B403487
theorem B400571 : Blo 115785 400571 := bstep (se 1 (by rfl) ⟨300428, by rfl⟩ : syracuseStep 400571 = 600857) B600857
theorem B1287049 : Blo 115785 1287049 := bstep (se 2 (by rfl) ⟨482643, by rfl⟩ : syracuseStep 1287049 = 965287) B965287
theorem B895423 : Blo 115785 895423 := bstep (se 1 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 895423 = 1343135) B1343135
theorem B404135 : Blo 115785 404135 := bstep (se 1 (by rfl) ⟨303101, by rfl⟩ : syracuseStep 404135 = 606203) B606203
theorem B174911 : Blo 115785 174911 := bstep (se 1 (by rfl) ⟨131183, by rfl⟩ : syracuseStep 174911 = 262367) B262367
theorem B2272157 : Blo 115785 2272157 := bstep (se 3 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 2272157 = 852059) B852059
theorem B175295 : Blo 115785 175295 := bstep (se 1 (by rfl) ⟨131471, by rfl⟩ : syracuseStep 175295 = 262943) B262943
theorem B176159 : Blo 115785 176159 := bstep (se 1 (by rfl) ⟨132119, by rfl⟩ : syracuseStep 176159 = 264239) B264239
theorem B176249 : Blo 115785 176249 := bstep (se 2 (by rfl) ⟨66093, by rfl⟩ : syracuseStep 176249 = 132187) B132187
theorem B176999 : Blo 115785 176999 := bstep (se 1 (by rfl) ⟨132749, by rfl⟩ : syracuseStep 176999 = 265499) B265499
theorem B2012039 : Blo 115785 2012039 := bstep (se 1 (by rfl) ⟨1509029, by rfl⟩ : syracuseStep 2012039 = 3018059) B3018059
theorem B373967 : Blo 115785 373967 := bstep (se 1 (by rfl) ⟨280475, by rfl⟩ : syracuseStep 373967 = 560951) B560951
theorem B177695 : Blo 115785 177695 := bstep (se 1 (by rfl) ⟨133271, by rfl⟩ : syracuseStep 177695 = 266543) B266543
theorem B1325321 : Blo 115785 1325321 := bstep (se 2 (by rfl) ⟨496995, by rfl⟩ : syracuseStep 1325321 = 993991) B993991
theorem B178535 : Blo 115785 178535 := bstep (se 1 (by rfl) ⟨133901, by rfl⟩ : syracuseStep 178535 = 267803) B267803
theorem B178895 : Blo 115785 178895 := bstep (se 1 (by rfl) ⟨134171, by rfl⟩ : syracuseStep 178895 = 268343) B268343
theorem B1981421 : Blo 115785 1981421 := bstep (se 3 (by rfl) ⟨371516, by rfl⟩ : syracuseStep 1981421 = 743033) B743033
theorem B179903 : Blo 115785 179903 := bstep (se 1 (by rfl) ⟨134927, by rfl⟩ : syracuseStep 179903 = 269855) B269855
theorem B4145357 : Blo 115785 4145357 := bstep (se 3 (by rfl) ⟨777254, by rfl⟩ : syracuseStep 4145357 = 1554509) B1554509
theorem B443657 : Blo 115785 443657 := bstep (se 2 (by rfl) ⟨166371, by rfl⟩ : syracuseStep 443657 = 332743) B332743
theorem B116207 : Blo 115785 116207 := bstep (se 1 (by rfl) ⟨87155, by rfl⟩ : syracuseStep 116207 = 174311) B174311
theorem B116827 : Blo 115785 116827 := bstep (se 1 (by rfl) ⟨87620, by rfl⟩ : syracuseStep 116827 = 175241) B175241
theorem B1723265 : Blo 115785 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B117743 : Blo 115785 117743 := bstep (se 1 (by rfl) ⟨88307, by rfl⟩ : syracuseStep 117743 = 176615) B176615
theorem B380015 : Blo 115785 380015 := bstep (se 1 (by rfl) ⟨285011, by rfl⟩ : syracuseStep 380015 = 570023) B570023
theorem B7818457 : Blo 115785 7818457 := bstep (se 2 (by rfl) ⟨2931921, by rfl⟩ : syracuseStep 7818457 = 5863843) B5863843
theorem B478505 : Blo 115785 478505 := bstep (se 2 (by rfl) ⟨179439, by rfl⟩ : syracuseStep 478505 = 358879) B358879
theorem B118079 : Blo 115785 118079 := bstep (se 1 (by rfl) ⟨88559, by rfl⟩ : syracuseStep 118079 = 177119) B177119
theorem B118175 : Blo 115785 118175 := bstep (se 1 (by rfl) ⟨88631, by rfl⟩ : syracuseStep 118175 = 177263) B177263
theorem B118427 : Blo 115785 118427 := bstep (se 1 (by rfl) ⟨88820, by rfl⟩ : syracuseStep 118427 = 177641) B177641
theorem B118479 : Blo 115785 118479 := bstep (se 1 (by rfl) ⟨88859, by rfl⟩ : syracuseStep 118479 = 177719) B177719
theorem B380641 : Blo 115785 380641 := bstep (se 2 (by rfl) ⟨142740, by rfl⟩ : syracuseStep 380641 = 285481) B285481
theorem B1200545 : Blo 115785 1200545 := bstep (se 2 (by rfl) ⟨450204, by rfl⟩ : syracuseStep 1200545 = 900409) B900409
theorem B119279 : Blo 115785 119279 := bstep (se 1 (by rfl) ⟨89459, by rfl⟩ : syracuseStep 119279 = 178919) B178919
theorem B447515 : Blo 115785 447515 := bstep (se 1 (by rfl) ⟨335636, by rfl⟩ : syracuseStep 447515 = 671273) B671273
theorem B251839 : Blo 115785 251839 := bstep (se 1 (by rfl) ⟨188879, by rfl⟩ : syracuseStep 251839 = 377759) B377759
theorem B6510617 : Blo 115785 6510617 := bstep (se 2 (by rfl) ⟨2441481, by rfl⟩ : syracuseStep 6510617 = 4882963) B4882963
theorem B383231 : Blo 115785 383231 := bstep (se 1 (by rfl) ⟨287423, by rfl⟩ : syracuseStep 383231 = 574847) B574847
theorem B449185 : Blo 115785 449185 := bstep (se 2 (by rfl) ⟨168444, by rfl⟩ : syracuseStep 449185 = 336889) B336889
theorem B1007387 : Blo 115785 1007387 := bstep (se 1 (by rfl) ⟨755540, by rfl⟩ : syracuseStep 1007387 = 1511081) B1511081
theorem B417599 : Blo 115785 417599 := bstep (se 1 (by rfl) ⟨313199, by rfl⟩ : syracuseStep 417599 = 626399) B626399
theorem B450431 : Blo 115785 450431 := bstep (se 1 (by rfl) ⟨337823, by rfl⟩ : syracuseStep 450431 = 675647) B675647
theorem B614537 : Blo 115785 614537 := bstep (se 2 (by rfl) ⟨230451, by rfl⟩ : syracuseStep 614537 = 460903) B460903
theorem B287327 : Blo 115785 287327 := bstep (se 1 (by rfl) ⟨215495, by rfl⟩ : syracuseStep 287327 = 430991) B430991
theorem B221935 : Blo 115785 221935 := bstep (se 1 (by rfl) ⟨166451, by rfl⟩ : syracuseStep 221935 = 332903) B332903
theorem B420137 : Blo 115785 420137 := bstep (se 2 (by rfl) ⟨157551, by rfl⟩ : syracuseStep 420137 = 315103) B315103
theorem B356543 : Blo 115785 356543 := bstep (se 1 (by rfl) ⟨267407, by rfl⟩ : syracuseStep 356543 = 534815) B534815
theorem B127423 : Blo 115785 127423 := bstep (se 1 (by rfl) ⟨95567, by rfl⟩ : syracuseStep 127423 = 191135) B191135
theorem B2978693 : Blo 115785 2978693 := bstep (se 4 (by rfl) ⟨279252, by rfl⟩ : syracuseStep 2978693 = 558505) B558505
theorem B881603 : Blo 115785 881603 := bstep (se 1 (by rfl) ⟨661202, by rfl⟩ : syracuseStep 881603 = 1322405) B1322405
theorem B226871 : Blo 115785 226871 := bstep (se 1 (by rfl) ⟨170153, by rfl⟩ : syracuseStep 226871 = 340307) B340307
theorem B2029535 : Blo 115785 2029535 := bstep (se 1 (by rfl) ⟨1522151, by rfl⟩ : syracuseStep 2029535 = 3044303) B3044303
theorem B293615 : Blo 115785 293615 := bstep (se 1 (by rfl) ⟨220211, by rfl⟩ : syracuseStep 293615 = 440423) B440423
theorem B261287 : Blo 115785 261287 := bstep (se 1 (by rfl) ⟨195965, by rfl⟩ : syracuseStep 261287 = 391931) B391931
theorem B261359 : Blo 115785 261359 := bstep (se 1 (by rfl) ⟨196019, by rfl⟩ : syracuseStep 261359 = 392039) B392039
theorem B262799 : Blo 115785 262799 := bstep (se 1 (by rfl) ⟨197099, by rfl⟩ : syracuseStep 262799 = 394199) B394199
theorem B295771 : Blo 115785 295771 := bstep (se 1 (by rfl) ⟨221828, by rfl⟩ : syracuseStep 295771 = 443657) B443657
theorem B295913 : Blo 115785 295913 := bstep (se 2 (by rfl) ⟨110967, by rfl⟩ : syracuseStep 295913 = 221935) B221935
theorem B198247 : Blo 115785 198247 := bstep (se 1 (by rfl) ⟨148685, by rfl⟩ : syracuseStep 198247 = 297371) B297371
theorem B1148843 : Blo 115785 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B3803125 : Blo 115785 3803125 := bstep (se 5 (by rfl) ⟨178271, by rfl⟩ : syracuseStep 3803125 = 356543) B356543
theorem B395387 : Blo 115785 395387 := bstep (se 1 (by rfl) ⟨296540, by rfl⟩ : syracuseStep 395387 = 593081) B593081
theorem B4655303 : Blo 115785 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B133531 : Blo 115785 133531 := bstep (se 1 (by rfl) ⟨100148, by rfl⟩ : syracuseStep 133531 = 200297) B200297
theorem B298343 : Blo 115785 298343 := bstep (se 1 (by rfl) ⟨223757, by rfl⟩ : syracuseStep 298343 = 447515) B447515
theorem B266471 : Blo 115785 266471 := bstep (se 1 (by rfl) ⟨199853, by rfl⟩ : syracuseStep 266471 = 399707) B399707
theorem B397547 : Blo 115785 397547 := bstep (se 1 (by rfl) ⟨298160, by rfl⟩ : syracuseStep 397547 = 596321) B596321
theorem B10424609 : Blo 115785 10424609 := bstep (se 2 (by rfl) ⟨3909228, by rfl⟩ : syracuseStep 10424609 = 7818457) B7818457
theorem B267047 : Blo 115785 267047 := bstep (se 1 (by rfl) ⟨200285, by rfl⟩ : syracuseStep 267047 = 400571) B400571
theorem B300287 : Blo 115785 300287 := bstep (se 1 (by rfl) ⟨225215, by rfl⟩ : syracuseStep 300287 = 450431) B450431
theorem B269423 : Blo 115785 269423 := bstep (se 1 (by rfl) ⟨202067, by rfl⟩ : syracuseStep 269423 = 404135) B404135
theorem B1514771 : Blo 115785 1514771 := bstep (se 1 (by rfl) ⟨1136078, by rfl⟩ : syracuseStep 1514771 = 2272157) B2272157
theorem B335785 : Blo 115785 335785 := bstep (se 2 (by rfl) ⟨125919, by rfl⟩ : syracuseStep 335785 = 251839) B251839
theorem B598913 : Blo 115785 598913 := bstep (se 2 (by rfl) ⟨224592, by rfl⟩ : syracuseStep 598913 = 449185) B449185
theorem B1353023 : Blo 115785 1353023 := bstep (se 1 (by rfl) ⟨1014767, by rfl⟩ : syracuseStep 1353023 = 2029535) B2029535
theorem B1320947 : Blo 115785 1320947 := bstep (se 1 (by rfl) ⟨990710, by rfl⟩ : syracuseStep 1320947 = 1981421) B1981421
theorem B174191 : Blo 115785 174191 := bstep (se 1 (by rfl) ⟨130643, by rfl⟩ : syracuseStep 174191 = 261287) B261287
theorem B174239 : Blo 115785 174239 := bstep (se 1 (by rfl) ⟨130679, by rfl⟩ : syracuseStep 174239 = 261359) B261359
theorem B502463 : Blo 115785 502463 := bstep (se 1 (by rfl) ⟨376847, by rfl⟩ : syracuseStep 502463 = 753695) B753695
theorem B2763571 : Blo 115785 2763571 := bstep (se 1 (by rfl) ⟨2072678, by rfl⟩ : syracuseStep 2763571 = 4145357) B4145357
theorem B1716065 : Blo 115785 1716065 := bstep (se 2 (by rfl) ⟨643524, by rfl⟩ : syracuseStep 1716065 = 1287049) B1287049
theorem B176039 : Blo 115785 176039 := bstep (se 1 (by rfl) ⟨132029, by rfl⟩ : syracuseStep 176039 = 264059) B264059
theorem B176423 : Blo 115785 176423 := bstep (se 1 (by rfl) ⟨132317, by rfl⟩ : syracuseStep 176423 = 264635) B264635
theorem B176681 : Blo 115785 176681 := bstep (se 2 (by rfl) ⟨66255, by rfl⟩ : syracuseStep 176681 = 132511) B132511
theorem B177383 : Blo 115785 177383 := bstep (se 1 (by rfl) ⟨133037, by rfl⟩ : syracuseStep 177383 = 266075) B266075
theorem B1225961 : Blo 115785 1225961 := bstep (se 2 (by rfl) ⟨459735, by rfl⟩ : syracuseStep 1225961 = 919471) B919471
theorem B177599 : Blo 115785 177599 := bstep (se 1 (by rfl) ⟨133199, by rfl⟩ : syracuseStep 177599 = 266399) B266399
theorem B800363 : Blo 115785 800363 := bstep (se 1 (by rfl) ⟨600272, by rfl⟩ : syracuseStep 800363 = 1200545) B1200545
theorem B1193897 : Blo 115785 1193897 := bstep (se 2 (by rfl) ⟨447711, by rfl⟩ : syracuseStep 1193897 = 895423) B895423
theorem B440495 : Blo 115785 440495 := bstep (se 1 (by rfl) ⟨330371, by rfl⟩ : syracuseStep 440495 = 660743) B660743
theorem B4340411 : Blo 115785 4340411 := bstep (se 1 (by rfl) ⟨3255308, by rfl⟩ : syracuseStep 4340411 = 6510617) B6510617
theorem B1358855 : Blo 115785 1358855 := bstep (se 1 (by rfl) ⟨1019141, by rfl⟩ : syracuseStep 1358855 = 2038283) B2038283
theorem B179327 : Blo 115785 179327 := bstep (se 1 (by rfl) ⟨134495, by rfl⟩ : syracuseStep 179327 = 268991) B268991
theorem B507521 : Blo 115785 507521 := bstep (se 2 (by rfl) ⟨190320, by rfl⟩ : syracuseStep 507521 = 380641) B380641
theorem B671591 : Blo 115785 671591 := bstep (se 1 (by rfl) ⟨503693, by rfl⟩ : syracuseStep 671591 = 1007387) B1007387
theorem B278399 : Blo 115785 278399 := bstep (se 1 (by rfl) ⟨208799, by rfl⟩ : syracuseStep 278399 = 417599) B417599
theorem B409691 : Blo 115785 409691 := bstep (se 1 (by rfl) ⟨307268, by rfl⟩ : syracuseStep 409691 = 614537) B614537
theorem B280091 : Blo 115785 280091 := bstep (se 1 (by rfl) ⟨210068, by rfl⟩ : syracuseStep 280091 = 420137) B420137
theorem B575113 : Blo 115785 575113 := bstep (se 2 (by rfl) ⟨215667, by rfl⟩ : syracuseStep 575113 = 431335) B431335
theorem B116607 : Blo 115785 116607 := bstep (se 1 (by rfl) ⟨87455, by rfl⟩ : syracuseStep 116607 = 174911) B174911
theorem B116863 : Blo 115785 116863 := bstep (se 1 (by rfl) ⟨87647, by rfl⟩ : syracuseStep 116863 = 175295) B175295
theorem B117439 : Blo 115785 117439 := bstep (se 1 (by rfl) ⟨88079, by rfl⟩ : syracuseStep 117439 = 176159) B176159
theorem B117499 : Blo 115785 117499 := bstep (se 1 (by rfl) ⟨88124, by rfl⟩ : syracuseStep 117499 = 176249) B176249
theorem B117999 : Blo 115785 117999 := bstep (se 1 (by rfl) ⟨88499, by rfl⟩ : syracuseStep 117999 = 176999) B176999
theorem B1985795 : Blo 115785 1985795 := bstep (se 1 (by rfl) ⟨1489346, by rfl⟩ : syracuseStep 1985795 = 2978693) B2978693
theorem B445769 : Blo 115785 445769 := bstep (se 2 (by rfl) ⟨167163, by rfl⟩ : syracuseStep 445769 = 334327) B334327
theorem B249311 : Blo 115785 249311 := bstep (se 1 (by rfl) ⟨186983, by rfl⟩ : syracuseStep 249311 = 373967) B373967
theorem B118463 : Blo 115785 118463 := bstep (se 1 (by rfl) ⟨88847, by rfl⟩ : syracuseStep 118463 = 177695) B177695
theorem B151247 : Blo 115785 151247 := bstep (se 1 (by rfl) ⟨113435, by rfl⟩ : syracuseStep 151247 = 226871) B226871
theorem B315133 : Blo 115785 315133 := bstep (se 3 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 315133 = 118175) B118175
theorem B119023 : Blo 115785 119023 := bstep (se 1 (by rfl) ⟨89267, by rfl⟩ : syracuseStep 119023 = 178535) B178535
theorem B119263 : Blo 115785 119263 := bstep (se 1 (by rfl) ⟨89447, by rfl⟩ : syracuseStep 119263 = 178895) B178895
theorem B119935 : Blo 115785 119935 := bstep (se 1 (by rfl) ⟨89951, by rfl⟩ : syracuseStep 119935 = 179903) B179903
theorem B23615621 : Blo 115785 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B318077 : Blo 115785 318077 := bstep (se 3 (by rfl) ⟨59639, by rfl⟩ : syracuseStep 318077 = 119279) B119279
theorem B1924499 : Blo 115785 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B253343 : Blo 115785 253343 := bstep (se 1 (by rfl) ⟨190007, by rfl⟩ : syracuseStep 253343 = 380015) B380015
theorem B679589 : Blo 115785 679589 := bstep (se 4 (by rfl) ⟨63711, by rfl⟩ : syracuseStep 679589 = 127423) B127423
theorem B1138799 : Blo 115785 1138799 := bstep (se 1 (by rfl) ⟨854099, by rfl⟩ : syracuseStep 1138799 = 1708199) B1708199
theorem B255487 : Blo 115785 255487 := bstep (se 1 (by rfl) ⟨191615, by rfl⟩ : syracuseStep 255487 = 383231) B383231
theorem B191551 : Blo 115785 191551 := bstep (se 1 (by rfl) ⟨143663, by rfl⟩ : syracuseStep 191551 = 287327) B287327
theorem B1341359 : Blo 115785 1341359 := bstep (se 1 (by rfl) ⟨1006019, by rfl⟩ : syracuseStep 1341359 = 2012039) B2012039
theorem B587735 : Blo 115785 587735 := bstep (se 1 (by rfl) ⟨440801, by rfl⟩ : syracuseStep 587735 = 881603) B881603
theorem B1276013 : Blo 115785 1276013 := bstep (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) B478505
theorem B883547 : Blo 115785 883547 := bstep (se 1 (by rfl) ⟨662660, by rfl⟩ : syracuseStep 883547 = 1325321) B1325321
theorem B195743 : Blo 115785 195743 := bstep (se 1 (by rfl) ⟨146807, by rfl⟩ : syracuseStep 195743 = 293615) B293615
theorem B197275 : Blo 115785 197275 := bstep (se 1 (by rfl) ⟨147956, by rfl⟩ : syracuseStep 197275 = 295913) B295913
theorem B394361 : Blo 115785 394361 := bstep (se 2 (by rfl) ⟨147885, by rfl⟩ : syracuseStep 394361 = 295771) B295771
theorem B263591 : Blo 115785 263591 := bstep (se 1 (by rfl) ⟨197693, by rfl⟩ : syracuseStep 263591 = 395387) B395387
theorem B264329 : Blo 115785 264329 := bstep (se 2 (by rfl) ⟨99123, by rfl⟩ : syracuseStep 264329 = 198247) B198247
theorem B297179 : Blo 115785 297179 := bstep (se 1 (by rfl) ⟨222884, by rfl⟩ : syracuseStep 297179 = 445769) B445769
theorem B198895 : Blo 115785 198895 := bstep (se 1 (by rfl) ⟨149171, by rfl⟩ : syracuseStep 198895 = 298343) B298343
theorem B166207 : Blo 115785 166207 := bstep (se 1 (by rfl) ⟨124655, by rfl⟩ : syracuseStep 166207 = 249311) B249311
theorem B265031 : Blo 115785 265031 := bstep (se 1 (by rfl) ⟨198773, by rfl⟩ : syracuseStep 265031 = 397547) B397547
theorem B6949739 : Blo 115785 6949739 := bstep (se 1 (by rfl) ⟨5212304, by rfl⟩ : syracuseStep 6949739 = 10424609) B10424609
theorem B200191 : Blo 115785 200191 := bstep (se 1 (by rfl) ⟨150143, by rfl⟩ : syracuseStep 200191 = 300287) B300287
theorem B1282999 : Blo 115785 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B168895 : Blo 115785 168895 := bstep (se 1 (by rfl) ⟨126671, by rfl⟩ : syracuseStep 168895 = 253343) B253343
theorem B3183725 : Blo 115785 3183725 := bstep (se 3 (by rfl) ⟨596948, by rfl⟩ : syracuseStep 3183725 = 1193897) B1193897
theorem B399275 : Blo 115785 399275 := bstep (se 1 (by rfl) ⟨299456, by rfl⟩ : syracuseStep 399275 = 598913) B598913
theorem B533575 : Blo 115785 533575 := bstep (se 1 (by rfl) ⟨400181, by rfl⟩ : syracuseStep 533575 = 800363) B800363
theorem B894239 : Blo 115785 894239 := bstep (se 1 (by rfl) ⟨670679, by rfl⟩ : syracuseStep 894239 = 1341359) B1341359
theorem B1680709 : Blo 115785 1680709 := bstep (se 4 (by rfl) ⟨157566, by rfl⟩ : syracuseStep 1680709 = 315133) B315133
theorem B2893607 : Blo 115785 2893607 := bstep (se 1 (by rfl) ⟨2170205, by rfl⟩ : syracuseStep 2893607 = 4340411) B4340411
theorem B403325 : Blo 115785 403325 := bstep (se 3 (by rfl) ⟨75623, by rfl⟩ : syracuseStep 403325 = 151247) B151247
theorem B338347 : Blo 115785 338347 := bstep (se 1 (by rfl) ⟨253760, by rfl⟩ : syracuseStep 338347 = 507521) B507521
theorem B1092509 : Blo 115785 1092509 := bstep (se 3 (by rfl) ⟨204845, by rfl⟩ : syracuseStep 1092509 = 409691) B409691
theorem B175199 : Blo 115785 175199 := bstep (se 1 (by rfl) ⟨131399, by rfl⟩ : syracuseStep 175199 = 262799) B262799
theorem B765895 : Blo 115785 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B340649 : Blo 115785 340649 := bstep (se 2 (by rfl) ⟨127743, by rfl⟩ : syracuseStep 340649 = 255487) B255487
theorem B1323863 : Blo 115785 1323863 := bstep (se 1 (by rfl) ⟨992897, by rfl⟩ : syracuseStep 1323863 = 1985795) B1985795
theorem B766817 : Blo 115785 766817 := bstep (se 2 (by rfl) ⟨287556, by rfl⟩ : syracuseStep 766817 = 575113) B575113
theorem B177647 : Blo 115785 177647 := bstep (se 1 (by rfl) ⟨133235, by rfl⟩ : syracuseStep 177647 = 266471) B266471
theorem B178031 : Blo 115785 178031 := bstep (se 1 (by rfl) ⟨133523, by rfl⟩ : syracuseStep 178031 = 267047) B267047
theorem B3684761 : Blo 115785 3684761 := bstep (se 2 (by rfl) ⟨1381785, by rfl⟩ : syracuseStep 3684761 = 2763571) B2763571
theorem B15743747 : Blo 115785 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B212051 : Blo 115785 212051 := bstep (se 1 (by rfl) ⟨159038, by rfl⟩ : syracuseStep 212051 = 318077) B318077
theorem B179615 : Blo 115785 179615 := bstep (se 1 (by rfl) ⟨134711, by rfl⟩ : syracuseStep 179615 = 269423) B269423
theorem B902015 : Blo 115785 902015 := bstep (se 1 (by rfl) ⟨676511, by rfl⟩ : syracuseStep 902015 = 1353023) B1353023
theorem B116127 : Blo 115785 116127 := bstep (se 1 (by rfl) ⟨87095, by rfl⟩ : syracuseStep 116127 = 174191) B174191
theorem B116159 : Blo 115785 116159 := bstep (se 1 (by rfl) ⟨87119, by rfl⟩ : syracuseStep 116159 = 174239) B174239
theorem B117359 : Blo 115785 117359 := bstep (se 1 (by rfl) ⟨88019, by rfl⟩ : syracuseStep 117359 = 176039) B176039
theorem B117615 : Blo 115785 117615 := bstep (se 1 (by rfl) ⟨88211, by rfl⟩ : syracuseStep 117615 = 176423) B176423
theorem B117787 : Blo 115785 117787 := bstep (se 1 (by rfl) ⟨88340, by rfl⟩ : syracuseStep 117787 = 176681) B176681
theorem B118255 : Blo 115785 118255 := bstep (se 1 (by rfl) ⟨88691, by rfl⟩ : syracuseStep 118255 = 177383) B177383
theorem B118399 : Blo 115785 118399 := bstep (se 1 (by rfl) ⟨88799, by rfl⟩ : syracuseStep 118399 = 177599) B177599
theorem B905903 : Blo 115785 905903 := bstep (se 1 (by rfl) ⟨679427, by rfl⟩ : syracuseStep 905903 = 1358855) B1358855
theorem B119551 : Blo 115785 119551 := bstep (se 1 (by rfl) ⟨89663, by rfl⟩ : syracuseStep 119551 = 179327) B179327
theorem B447713 : Blo 115785 447713 := bstep (se 2 (by rfl) ⟨167892, by rfl⟩ : syracuseStep 447713 = 335785) B335785
theorem B447727 : Blo 115785 447727 := bstep (se 1 (by rfl) ⟨335795, by rfl⟩ : syracuseStep 447727 = 671591) B671591
theorem B185599 : Blo 115785 185599 := bstep (se 1 (by rfl) ⟨139199, by rfl⟩ : syracuseStep 185599 = 278399) B278399
theorem B3036797 : Blo 115785 3036797 := bstep (se 3 (by rfl) ⟨569399, by rfl⟩ : syracuseStep 3036797 = 1138799) B1138799
theorem B186727 : Blo 115785 186727 := bstep (se 1 (by rfl) ⟨140045, by rfl⟩ : syracuseStep 186727 = 280091) B280091
theorem B3103535 : Blo 115785 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B712165 : Blo 115785 712165 := bstep (se 4 (by rfl) ⟨66765, by rfl⟩ : syracuseStep 712165 = 133531) B133531
theorem B5070833 : Blo 115785 5070833 := bstep (se 2 (by rfl) ⟨1901562, by rfl⟩ : syracuseStep 5070833 = 3803125) B3803125
theorem B255401 : Blo 115785 255401 := bstep (se 2 (by rfl) ⟨95775, by rfl⟩ : syracuseStep 255401 = 191551) B191551
theorem B1009847 : Blo 115785 1009847 := bstep (se 1 (by rfl) ⟨757385, by rfl⟩ : syracuseStep 1009847 = 1514771) B1514771
theorem B453059 : Blo 115785 453059 := bstep (se 1 (by rfl) ⟨339794, by rfl⟩ : syracuseStep 453059 = 679589) B679589
theorem B880631 : Blo 115785 880631 := bstep (se 1 (by rfl) ⟨660473, by rfl⟩ : syracuseStep 880631 = 1320947) B1320947
theorem B159913 : Blo 115785 159913 := bstep (se 2 (by rfl) ⟨59967, by rfl⟩ : syracuseStep 159913 = 119935) B119935
theorem B1339901 : Blo 115785 1339901 := bstep (se 3 (by rfl) ⟨251231, by rfl⟩ : syracuseStep 1339901 = 502463) B502463
theorem B1144043 : Blo 115785 1144043 := bstep (se 1 (by rfl) ⟨858032, by rfl⟩ : syracuseStep 1144043 = 1716065) B1716065
theorem B817307 : Blo 115785 817307 := bstep (se 1 (by rfl) ⟨612980, by rfl⟩ : syracuseStep 817307 = 1225961) B1225961
theorem B391823 : Blo 115785 391823 := bstep (se 1 (by rfl) ⟨293867, by rfl⟩ : syracuseStep 391823 = 587735) B587735
theorem B850675 : Blo 115785 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B293663 : Blo 115785 293663 := bstep (se 1 (by rfl) ⟨220247, by rfl⟩ : syracuseStep 293663 = 440495) B440495
theorem B589031 : Blo 115785 589031 := bstep (se 1 (by rfl) ⟨441773, by rfl⟩ : syracuseStep 589031 = 883547) B883547
theorem B130495 : Blo 115785 130495 := bstep (se 1 (by rfl) ⟨97871, by rfl⟩ : syracuseStep 130495 = 195743) B195743
theorem B262907 : Blo 115785 262907 := bstep (se 1 (by rfl) ⟨197180, by rfl⟩ : syracuseStep 262907 = 394361) B394361
theorem B263033 : Blo 115785 263033 := bstep (se 2 (by rfl) ⟨98637, by rfl⟩ : syracuseStep 263033 = 197275) B197275
theorem B852869 : Blo 115785 852869 := bstep (se 4 (by rfl) ⟨79956, by rfl⟩ : syracuseStep 852869 = 159913) B159913
theorem B198119 : Blo 115785 198119 := bstep (se 1 (by rfl) ⟨148589, by rfl⟩ : syracuseStep 198119 = 297179) B297179
theorem B1804517 : Blo 115785 1804517 := bstep (se 4 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 1804517 = 338347) B338347
theorem B265193 : Blo 115785 265193 := bstep (se 2 (by rfl) ⟨99447, by rfl⟩ : syracuseStep 265193 = 198895) B198895
theorem B298475 : Blo 115785 298475 := bstep (se 1 (by rfl) ⟨223856, by rfl⟩ : syracuseStep 298475 = 447713) B447713
theorem B266183 : Blo 115785 266183 := bstep (se 1 (by rfl) ⟨199637, by rfl⟩ : syracuseStep 266183 = 399275) B399275
theorem B2069023 : Blo 115785 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B266921 : Blo 115785 266921 := bstep (se 2 (by rfl) ⟨100095, by rfl⟩ : syracuseStep 266921 = 200191) B200191
theorem B1021193 : Blo 115785 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B3380555 : Blo 115785 3380555 := bstep (se 1 (by rfl) ⟨2535416, by rfl⟩ : syracuseStep 3380555 = 5070833) B5070833
theorem B596159 : Blo 115785 596159 := bstep (se 1 (by rfl) ⟨447119, by rfl⟩ : syracuseStep 596159 = 894239) B894239
theorem B170267 : Blo 115785 170267 := bstep (se 1 (by rfl) ⟨127700, by rfl⟩ : syracuseStep 170267 = 255401) B255401
theorem B1710665 : Blo 115785 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B268883 : Blo 115785 268883 := bstep (se 1 (by rfl) ⟨201662, by rfl⟩ : syracuseStep 268883 = 403325) B403325
theorem B302039 : Blo 115785 302039 := bstep (se 1 (by rfl) ⟨226529, by rfl⟩ : syracuseStep 302039 = 453059) B453059
theorem B596969 : Blo 115785 596969 := bstep (se 2 (by rfl) ⟨223863, by rfl⟩ : syracuseStep 596969 = 447727) B447727
theorem B893267 : Blo 115785 893267 := bstep (se 1 (by rfl) ⟨669950, by rfl⟩ : syracuseStep 893267 = 1339901) B1339901
theorem B762695 : Blo 115785 762695 := bstep (se 1 (by rfl) ⟨572021, by rfl⟩ : syracuseStep 762695 = 1144043) B1144043
theorem B10495831 : Blo 115785 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B173993 : Blo 115785 173993 := bstep (se 2 (by rfl) ⟨65247, by rfl⟩ : syracuseStep 173993 = 130495) B130495
theorem B141367 : Blo 115785 141367 := bstep (se 1 (by rfl) ⟨106025, by rfl⟩ : syracuseStep 141367 = 212051) B212051
theorem B601343 : Blo 115785 601343 := bstep (se 1 (by rfl) ⟨451007, by rfl⟩ : syracuseStep 601343 = 902015) B902015
theorem B175727 : Blo 115785 175727 := bstep (se 1 (by rfl) ⟨131795, by rfl⟩ : syracuseStep 175727 = 263591) B263591
theorem B176219 : Blo 115785 176219 := bstep (se 1 (by rfl) ⟨132164, by rfl⟩ : syracuseStep 176219 = 264329) B264329
theorem B2240945 : Blo 115785 2240945 := bstep (se 2 (by rfl) ⟨840354, by rfl⟩ : syracuseStep 2240945 = 1680709) B1680709
theorem B176687 : Blo 115785 176687 := bstep (se 1 (by rfl) ⟨132515, by rfl⟩ : syracuseStep 176687 = 265031) B265031
theorem B4633159 : Blo 115785 4633159 := bstep (se 1 (by rfl) ⟨3474869, by rfl⟩ : syracuseStep 4633159 = 6949739) B6949739
theorem B603935 : Blo 115785 603935 := bstep (se 1 (by rfl) ⟨452951, by rfl⟩ : syracuseStep 603935 = 905903) B905903
theorem B46613717 : Blo 115785 46613717 := bstep (se 7 (by rfl) ⟨546254, by rfl⟩ : syracuseStep 46613717 = 1092509) B1092509
theorem B673231 : Blo 115785 673231 := bstep (se 1 (by rfl) ⟨504923, by rfl⟩ : syracuseStep 673231 = 1009847) B1009847
theorem B247465 : Blo 115785 247465 := bstep (se 2 (by rfl) ⟨92799, by rfl⟩ : syracuseStep 247465 = 185599) B185599
theorem B116799 : Blo 115785 116799 := bstep (se 1 (by rfl) ⟨87599, by rfl⟩ : syracuseStep 116799 = 175199) B175199
theorem B248969 : Blo 115785 248969 := bstep (se 2 (by rfl) ⟨93363, by rfl⟩ : syracuseStep 248969 = 186727) B186727
theorem B511211 : Blo 115785 511211 := bstep (se 1 (by rfl) ⟨383408, by rfl⟩ : syracuseStep 511211 = 766817) B766817
theorem B1134233 : Blo 115785 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B118431 : Blo 115785 118431 := bstep (se 1 (by rfl) ⟨88823, by rfl⟩ : syracuseStep 118431 = 177647) B177647
theorem B118687 : Blo 115785 118687 := bstep (se 1 (by rfl) ⟨89015, by rfl⟩ : syracuseStep 118687 = 178031) B178031
theorem B544871 : Blo 115785 544871 := bstep (se 1 (by rfl) ⟨408653, by rfl⟩ : syracuseStep 544871 = 817307) B817307
theorem B119743 : Blo 115785 119743 := bstep (se 1 (by rfl) ⟨89807, by rfl⟩ : syracuseStep 119743 = 179615) B179615
theorem B711433 : Blo 115785 711433 := bstep (se 2 (by rfl) ⟨266787, by rfl⟩ : syracuseStep 711433 = 533575) B533575
theorem B221609 : Blo 115785 221609 := bstep (se 2 (by rfl) ⟨83103, by rfl⟩ : syracuseStep 221609 = 166207) B166207
theorem B451129 : Blo 115785 451129 := bstep (se 2 (by rfl) ⟨169173, by rfl⟩ : syracuseStep 451129 = 338347) B338347
theorem B2122483 : Blo 115785 2122483 := bstep (se 1 (by rfl) ⟨1591862, by rfl⟩ : syracuseStep 2122483 = 3183725) B3183725
theorem B2024531 : Blo 115785 2024531 := bstep (se 1 (by rfl) ⟨1518398, by rfl⟩ : syracuseStep 2024531 = 3036797) B3036797
theorem B1929071 : Blo 115785 1929071 := bstep (se 1 (by rfl) ⟨1446803, by rfl⟩ : syracuseStep 1929071 = 2893607) B2893607
theorem B225193 : Blo 115785 225193 := bstep (se 2 (by rfl) ⟨84447, by rfl⟩ : syracuseStep 225193 = 168895) B168895
theorem B783101 : Blo 115785 783101 := bstep (se 3 (by rfl) ⟨146831, by rfl⟩ : syracuseStep 783101 = 293663) B293663
theorem B587087 : Blo 115785 587087 := bstep (se 1 (by rfl) ⟨440315, by rfl⟩ : syracuseStep 587087 = 880631) B880631
theorem B227099 : Blo 115785 227099 := bstep (se 1 (by rfl) ⟨170324, by rfl⟩ : syracuseStep 227099 = 340649) B340649
theorem B882575 : Blo 115785 882575 := bstep (se 1 (by rfl) ⟨661931, by rfl⟩ : syracuseStep 882575 = 1323863) B1323863
theorem B2456507 : Blo 115785 2456507 := bstep (se 1 (by rfl) ⟨1842380, by rfl⟩ : syracuseStep 2456507 = 3684761) B3684761
theorem B261215 : Blo 115785 261215 := bstep (se 1 (by rfl) ⟨195911, by rfl⟩ : syracuseStep 261215 = 391823) B391823
theorem B949553 : Blo 115785 949553 := bstep (se 2 (by rfl) ⟨356082, by rfl⟩ : syracuseStep 949553 = 712165) B712165
theorem B392687 : Blo 115785 392687 := bstep (se 1 (by rfl) ⟨294515, by rfl⟩ : syracuseStep 392687 = 589031) B589031
theorem B132079 : Blo 115785 132079 := bstep (se 1 (by rfl) ⟨99059, by rfl⟩ : syracuseStep 132079 = 198119) B198119
theorem B165979 : Blo 115785 165979 := bstep (se 1 (by rfl) ⟨124484, by rfl⟩ : syracuseStep 165979 = 248969) B248969
theorem B329953 : Blo 115785 329953 := bstep (se 2 (by rfl) ⟨123732, by rfl⟩ : syracuseStep 329953 = 247465) B247465
theorem B198983 : Blo 115785 198983 := bstep (se 1 (by rfl) ⟨149237, by rfl⟩ : syracuseStep 198983 = 298475) B298475
theorem B756155 : Blo 115785 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B13994441 : Blo 115785 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B363247 : Blo 115785 363247 := bstep (se 1 (by rfl) ⟨272435, by rfl⟩ : syracuseStep 363247 = 544871) B544871
theorem B397439 : Blo 115785 397439 := bstep (se 1 (by rfl) ⟨298079, by rfl⟩ : syracuseStep 397439 = 596159) B596159
theorem B201359 : Blo 115785 201359 := bstep (se 1 (by rfl) ⟨151019, by rfl⟩ : syracuseStep 201359 = 302039) B302039
theorem B397979 : Blo 115785 397979 := bstep (se 1 (by rfl) ⟨298484, by rfl⟩ : syracuseStep 397979 = 596969) B596969
theorem B300257 : Blo 115785 300257 := bstep (se 2 (by rfl) ⟨112596, by rfl⟩ : syracuseStep 300257 = 225193) B225193
theorem B595511 : Blo 115785 595511 := bstep (se 1 (by rfl) ⟨446633, by rfl⟩ : syracuseStep 595511 = 893267) B893267
theorem B2758697 : Blo 115785 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B1349687 : Blo 115785 1349687 := bstep (se 1 (by rfl) ⟨1012265, by rfl⟩ : syracuseStep 1349687 = 2024531) B2024531
theorem B400895 : Blo 115785 400895 := bstep (se 1 (by rfl) ⟨300671, by rfl⟩ : syracuseStep 400895 = 601343) B601343
theorem B1286047 : Blo 115785 1286047 := bstep (se 1 (by rfl) ⟨964535, by rfl⟩ : syracuseStep 1286047 = 1929071) B1929071
theorem B402623 : Blo 115785 402623 := bstep (se 1 (by rfl) ⟨301967, by rfl⟩ : syracuseStep 402623 = 603935) B603935
theorem B174143 : Blo 115785 174143 := bstep (se 1 (by rfl) ⟨130607, by rfl⟩ : syracuseStep 174143 = 261215) B261215
theorem B633035 : Blo 115785 633035 := bstep (se 1 (by rfl) ⟨474776, by rfl⟩ : syracuseStep 633035 = 949553) B949553
theorem B175271 : Blo 115785 175271 := bstep (se 1 (by rfl) ⟨131453, by rfl⟩ : syracuseStep 175271 = 262907) B262907
theorem B175355 : Blo 115785 175355 := bstep (se 1 (by rfl) ⟨131516, by rfl⟩ : syracuseStep 175355 = 263033) B263033
theorem B568579 : Blo 115785 568579 := bstep (se 1 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 568579 = 852869) B852869
theorem B601505 : Blo 115785 601505 := bstep (se 2 (by rfl) ⟨225564, by rfl⟩ : syracuseStep 601505 = 451129) B451129
theorem B31075811 : Blo 115785 31075811 := bstep (se 1 (by rfl) ⟨23306858, by rfl⟩ : syracuseStep 31075811 = 46613717) B46613717
theorem B2829977 : Blo 115785 2829977 := bstep (se 2 (by rfl) ⟨1061241, by rfl⟩ : syracuseStep 2829977 = 2122483) B2122483
theorem B897641 : Blo 115785 897641 := bstep (se 2 (by rfl) ⟨336615, by rfl⟩ : syracuseStep 897641 = 673231) B673231
theorem B176795 : Blo 115785 176795 := bstep (se 1 (by rfl) ⟨132596, by rfl⟩ : syracuseStep 176795 = 265193) B265193
theorem B177455 : Blo 115785 177455 := bstep (se 1 (by rfl) ⟨133091, by rfl⟩ : syracuseStep 177455 = 266183) B266183
theorem B177947 : Blo 115785 177947 := bstep (se 1 (by rfl) ⟨133460, by rfl⟩ : syracuseStep 177947 = 266921) B266921
theorem B179255 : Blo 115785 179255 := bstep (se 1 (by rfl) ⟨134441, by rfl⟩ : syracuseStep 179255 = 268883) B268883
theorem B147739 : Blo 115785 147739 := bstep (se 1 (by rfl) ⟨110804, by rfl⟩ : syracuseStep 147739 = 221609) B221609
theorem B508463 : Blo 115785 508463 := bstep (se 1 (by rfl) ⟨381347, by rfl⟩ : syracuseStep 508463 = 762695) B762695
theorem B6177545 : Blo 115785 6177545 := bstep (se 2 (by rfl) ⟨2316579, by rfl⟩ : syracuseStep 6177545 = 4633159) B4633159
theorem B115995 : Blo 115785 115995 := bstep (se 1 (by rfl) ⟨86996, by rfl⟩ : syracuseStep 115995 = 173993) B173993
theorem B117151 : Blo 115785 117151 := bstep (se 1 (by rfl) ⟨87863, by rfl⟩ : syracuseStep 117151 = 175727) B175727
theorem B117479 : Blo 115785 117479 := bstep (se 1 (by rfl) ⟨88109, by rfl⟩ : syracuseStep 117479 = 176219) B176219
theorem B1493963 : Blo 115785 1493963 := bstep (se 1 (by rfl) ⟨1120472, by rfl⟩ : syracuseStep 1493963 = 2240945) B2240945
theorem B117791 : Blo 115785 117791 := bstep (se 1 (by rfl) ⟨88343, by rfl⟩ : syracuseStep 117791 = 176687) B176687
theorem B1363229 : Blo 115785 1363229 := bstep (se 3 (by rfl) ⟨255605, by rfl⟩ : syracuseStep 1363229 = 511211) B511211
theorem B151399 : Blo 115785 151399 := bstep (se 1 (by rfl) ⟨113549, by rfl⟩ : syracuseStep 151399 = 227099) B227099
theorem B1203011 : Blo 115785 1203011 := bstep (se 1 (by rfl) ⟨902258, by rfl⟩ : syracuseStep 1203011 = 1804517) B1804517
theorem B188489 : Blo 115785 188489 := bstep (se 2 (by rfl) ⟨70683, by rfl⟩ : syracuseStep 188489 = 141367) B141367
theorem B680795 : Blo 115785 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B2253703 : Blo 115785 2253703 := bstep (se 1 (by rfl) ⟨1690277, by rfl⟩ : syracuseStep 2253703 = 3380555) B3380555
theorem B3794309 : Blo 115785 3794309 := bstep (se 4 (by rfl) ⟨355716, by rfl⟩ : syracuseStep 3794309 = 711433) B711433
theorem B1140443 : Blo 115785 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B454045 : Blo 115785 454045 := bstep (se 3 (by rfl) ⟨85133, by rfl⟩ : syracuseStep 454045 = 170267) B170267
theorem B522067 : Blo 115785 522067 := bstep (se 1 (by rfl) ⟨391550, by rfl⟩ : syracuseStep 522067 = 783101) B783101
theorem B391391 : Blo 115785 391391 := bstep (se 1 (by rfl) ⟨293543, by rfl⟩ : syracuseStep 391391 = 587087) B587087
theorem B588383 : Blo 115785 588383 := bstep (se 1 (by rfl) ⟨441287, by rfl⟩ : syracuseStep 588383 = 882575) B882575
theorem B1637671 : Blo 115785 1637671 := bstep (se 1 (by rfl) ⟨1228253, by rfl⟩ : syracuseStep 1637671 = 2456507) B2456507
theorem B261791 : Blo 115785 261791 := bstep (se 1 (by rfl) ⟨196343, by rfl⟩ : syracuseStep 261791 = 392687) B392687
theorem B196985 : Blo 115785 196985 := bstep (se 2 (by rfl) ⟨73869, by rfl⟩ : syracuseStep 196985 = 147739) B147739
theorem B132655 : Blo 115785 132655 := bstep (se 1 (by rfl) ⟨99491, by rfl⟩ : syracuseStep 132655 = 198983) B198983
theorem B264959 : Blo 115785 264959 := bstep (se 1 (by rfl) ⟨198719, by rfl⟩ : syracuseStep 264959 = 397439) B397439
theorem B134239 : Blo 115785 134239 := bstep (se 1 (by rfl) ⟨100679, by rfl⟩ : syracuseStep 134239 = 201359) B201359
theorem B265319 : Blo 115785 265319 := bstep (se 1 (by rfl) ⟨198989, by rfl⟩ : syracuseStep 265319 = 397979) B397979
theorem B200171 : Blo 115785 200171 := bstep (se 1 (by rfl) ⟨150128, by rfl⟩ : syracuseStep 200171 = 300257) B300257
theorem B397007 : Blo 115785 397007 := bstep (se 1 (by rfl) ⟨297755, by rfl⟩ : syracuseStep 397007 = 595511) B595511
theorem B1937317 : Blo 115785 1937317 := bstep (se 4 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 1937317 = 363247) B363247
theorem B1839131 : Blo 115785 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B758105 : Blo 115785 758105 := bstep (se 2 (by rfl) ⟨284289, by rfl⟩ : syracuseStep 758105 = 568579) B568579
theorem B267263 : Blo 115785 267263 := bstep (se 1 (by rfl) ⟨200447, by rfl⟩ : syracuseStep 267263 = 400895) B400895
theorem B201865 : Blo 115785 201865 := bstep (se 2 (by rfl) ⟨75699, by rfl⟩ : syracuseStep 201865 = 151399) B151399
theorem B268415 : Blo 115785 268415 := bstep (se 1 (by rfl) ⟨201311, by rfl⟩ : syracuseStep 268415 = 402623) B402623
theorem B2529539 : Blo 115785 2529539 := bstep (se 1 (by rfl) ⟨1897154, by rfl⟩ : syracuseStep 2529539 = 3794309) B3794309
theorem B760295 : Blo 115785 760295 := bstep (se 1 (by rfl) ⟨570221, by rfl⟩ : syracuseStep 760295 = 1140443) B1140443
theorem B401003 : Blo 115785 401003 := bstep (se 1 (by rfl) ⟨300752, by rfl⟩ : syracuseStep 401003 = 601505) B601505
theorem B20717207 : Blo 115785 20717207 := bstep (se 1 (by rfl) ⟨15537905, by rfl⟩ : syracuseStep 20717207 = 31075811) B31075811
theorem B696089 : Blo 115785 696089 := bstep (se 2 (by rfl) ⟨261033, by rfl⟩ : syracuseStep 696089 = 522067) B522067
theorem B598427 : Blo 115785 598427 := bstep (se 1 (by rfl) ⟨448820, by rfl⟩ : syracuseStep 598427 = 897641) B897641
theorem B174527 : Blo 115785 174527 := bstep (se 1 (by rfl) ⟨130895, by rfl⟩ : syracuseStep 174527 = 261791) B261791
theorem B1714729 : Blo 115785 1714729 := bstep (se 2 (by rfl) ⟨643023, by rfl⟩ : syracuseStep 1714729 = 1286047) B1286047
theorem B338975 : Blo 115785 338975 := bstep (se 1 (by rfl) ⟨254231, by rfl⟩ : syracuseStep 338975 = 508463) B508463
theorem B176105 : Blo 115785 176105 := bstep (se 2 (by rfl) ⟨66039, by rfl⟩ : syracuseStep 176105 = 132079) B132079
theorem B995975 : Blo 115785 995975 := bstep (se 1 (by rfl) ⟨746981, by rfl⟩ : syracuseStep 995975 = 1493963) B1493963
theorem B439937 : Blo 115785 439937 := bstep (se 2 (by rfl) ⟨164976, by rfl⟩ : syracuseStep 439937 = 329953) B329953
theorem B899791 : Blo 115785 899791 := bstep (se 1 (by rfl) ⟨674843, by rfl⟩ : syracuseStep 899791 = 1349687) B1349687
theorem B605393 : Blo 115785 605393 := bstep (se 2 (by rfl) ⟨227022, by rfl⟩ : syracuseStep 605393 = 454045) B454045
theorem B802007 : Blo 115785 802007 := bstep (se 1 (by rfl) ⟨601505, by rfl⟩ : syracuseStep 802007 = 1203011) B1203011
theorem B2016413 : Blo 115785 2016413 := bstep (se 3 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 2016413 = 756155) B756155
theorem B116095 : Blo 115785 116095 := bstep (se 1 (by rfl) ⟨87071, by rfl⟩ : syracuseStep 116095 = 174143) B174143
theorem B116847 : Blo 115785 116847 := bstep (se 1 (by rfl) ⟨87635, by rfl⟩ : syracuseStep 116847 = 175271) B175271
theorem B116903 : Blo 115785 116903 := bstep (se 1 (by rfl) ⟨87677, by rfl⟩ : syracuseStep 116903 = 175355) B175355
theorem B1886651 : Blo 115785 1886651 := bstep (se 1 (by rfl) ⟨1414988, by rfl⟩ : syracuseStep 1886651 = 2829977) B2829977
theorem B117863 : Blo 115785 117863 := bstep (se 1 (by rfl) ⟨88397, by rfl⟩ : syracuseStep 117863 = 176795) B176795
theorem B118303 : Blo 115785 118303 := bstep (se 1 (by rfl) ⟨88727, by rfl⟩ : syracuseStep 118303 = 177455) B177455
theorem B118631 : Blo 115785 118631 := bstep (se 1 (by rfl) ⟨88973, by rfl⟩ : syracuseStep 118631 = 177947) B177947
theorem B2183561 : Blo 115785 2183561 := bstep (se 2 (by rfl) ⟨818835, by rfl⟩ : syracuseStep 2183561 = 1637671) B1637671
theorem B119503 : Blo 115785 119503 := bstep (se 1 (by rfl) ⟨89627, by rfl⟩ : syracuseStep 119503 = 179255) B179255
theorem B4118363 : Blo 115785 4118363 := bstep (se 1 (by rfl) ⟨3088772, by rfl⟩ : syracuseStep 4118363 = 6177545) B6177545
theorem B3004937 : Blo 115785 3004937 := bstep (se 2 (by rfl) ⟨1126851, by rfl⟩ : syracuseStep 3004937 = 2253703) B2253703
theorem B9329627 : Blo 115785 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B908819 : Blo 115785 908819 := bstep (se 1 (by rfl) ⟨681614, by rfl⟩ : syracuseStep 908819 = 1363229) B1363229
theorem B221305 : Blo 115785 221305 := bstep (se 2 (by rfl) ⟨82989, by rfl⟩ : syracuseStep 221305 = 165979) B165979
theorem B125659 : Blo 115785 125659 := bstep (se 1 (by rfl) ⟨94244, by rfl⟩ : syracuseStep 125659 = 188489) B188489
theorem B453863 : Blo 115785 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B422023 : Blo 115785 422023 := bstep (se 1 (by rfl) ⟨316517, by rfl⟩ : syracuseStep 422023 = 633035) B633035
theorem B260927 : Blo 115785 260927 := bstep (se 1 (by rfl) ⟨195695, by rfl⟩ : syracuseStep 260927 = 391391) B391391
theorem B392255 : Blo 115785 392255 := bstep (se 1 (by rfl) ⟨294191, by rfl⟩ : syracuseStep 392255 = 588383) B588383
theorem B295073 : Blo 115785 295073 := bstep (se 2 (by rfl) ⟨110652, by rfl⟩ : syracuseStep 295073 = 221305) B221305
theorem B131323 : Blo 115785 131323 := bstep (se 1 (by rfl) ⟨98492, by rfl⟩ : syracuseStep 131323 = 196985) B196985
theorem B1344275 : Blo 115785 1344275 := bstep (se 1 (by rfl) ⟨1008206, by rfl⟩ : syracuseStep 1344275 = 2016413) B2016413
theorem B133447 : Blo 115785 133447 := bstep (se 1 (by rfl) ⟨100085, by rfl⟩ : syracuseStep 133447 = 200171) B200171
theorem B264671 : Blo 115785 264671 := bstep (se 1 (by rfl) ⟨198503, by rfl⟩ : syracuseStep 264671 = 397007) B397007
theorem B167545 : Blo 115785 167545 := bstep (se 2 (by rfl) ⟨62829, by rfl⟩ : syracuseStep 167545 = 125659) B125659
theorem B2003291 : Blo 115785 2003291 := bstep (se 1 (by rfl) ⟨1502468, by rfl⟩ : syracuseStep 2003291 = 3004937) B3004937
theorem B267335 : Blo 115785 267335 := bstep (se 1 (by rfl) ⟨200501, by rfl⟩ : syracuseStep 267335 = 401003) B401003
theorem B464059 : Blo 115785 464059 := bstep (se 1 (by rfl) ⟨348044, by rfl⟩ : syracuseStep 464059 = 696089) B696089
theorem B562697 : Blo 115785 562697 := bstep (se 2 (by rfl) ⟨211011, by rfl⟩ : syracuseStep 562697 = 422023) B422023
theorem B398951 : Blo 115785 398951 := bstep (se 1 (by rfl) ⟨299213, by rfl⟩ : syracuseStep 398951 = 598427) B598427
theorem B269153 : Blo 115785 269153 := bstep (se 2 (by rfl) ⟨100932, by rfl⟩ : syracuseStep 269153 = 201865) B201865
theorem B302575 : Blo 115785 302575 := bstep (se 1 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 302575 = 453863) B453863
theorem B24879005 : Blo 115785 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B663983 : Blo 115785 663983 := bstep (se 1 (by rfl) ⟨497987, by rfl⟩ : syracuseStep 663983 = 995975) B995975
theorem B173951 : Blo 115785 173951 := bstep (se 1 (by rfl) ⟨130463, by rfl⟩ : syracuseStep 173951 = 260927) B260927
theorem B403595 : Blo 115785 403595 := bstep (se 1 (by rfl) ⟨302696, by rfl⟩ : syracuseStep 403595 = 605393) B605393
theorem B534671 : Blo 115785 534671 := bstep (se 1 (by rfl) ⟨401003, by rfl⟩ : syracuseStep 534671 = 802007) B802007
theorem B1257767 : Blo 115785 1257767 := bstep (se 1 (by rfl) ⟨943325, by rfl⟩ : syracuseStep 1257767 = 1886651) B1886651
theorem B176639 : Blo 115785 176639 := bstep (se 1 (by rfl) ⟨132479, by rfl⟩ : syracuseStep 176639 = 264959) B264959
theorem B176873 : Blo 115785 176873 := bstep (se 2 (by rfl) ⟨66327, by rfl⟩ : syracuseStep 176873 = 132655) B132655
theorem B176879 : Blo 115785 176879 := bstep (se 1 (by rfl) ⟨132659, by rfl⟩ : syracuseStep 176879 = 265319) B265319
theorem B1226087 : Blo 115785 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B505403 : Blo 115785 505403 := bstep (se 1 (by rfl) ⟨379052, by rfl⟩ : syracuseStep 505403 = 758105) B758105
theorem B1455707 : Blo 115785 1455707 := bstep (se 1 (by rfl) ⟨1091780, by rfl⟩ : syracuseStep 1455707 = 2183561) B2183561
theorem B178175 : Blo 115785 178175 := bstep (se 1 (by rfl) ⟨133631, by rfl⟩ : syracuseStep 178175 = 267263) B267263
theorem B178943 : Blo 115785 178943 := bstep (se 1 (by rfl) ⟨134207, by rfl⟩ : syracuseStep 178943 = 268415) B268415
theorem B178985 : Blo 115785 178985 := bstep (se 2 (by rfl) ⟨67119, by rfl⟩ : syracuseStep 178985 = 134239) B134239
theorem B1686359 : Blo 115785 1686359 := bstep (se 1 (by rfl) ⟨1264769, by rfl⟩ : syracuseStep 1686359 = 2529539) B2529539
theorem B506863 : Blo 115785 506863 := bstep (se 1 (by rfl) ⟨380147, by rfl⟩ : syracuseStep 506863 = 760295) B760295
theorem B605879 : Blo 115785 605879 := bstep (se 1 (by rfl) ⟨454409, by rfl⟩ : syracuseStep 605879 = 908819) B908819
theorem B13811471 : Blo 115785 13811471 := bstep (se 1 (by rfl) ⟨10358603, by rfl⟩ : syracuseStep 13811471 = 20717207) B20717207
theorem B116351 : Blo 115785 116351 := bstep (se 1 (by rfl) ⟨87263, by rfl⟩ : syracuseStep 116351 = 174527) B174527
theorem B117403 : Blo 115785 117403 := bstep (se 1 (by rfl) ⟨88052, by rfl⟩ : syracuseStep 117403 = 176105) B176105
theorem B2286305 : Blo 115785 2286305 := bstep (se 2 (by rfl) ⟨857364, by rfl⟩ : syracuseStep 2286305 = 1714729) B1714729
theorem B2745575 : Blo 115785 2745575 := bstep (se 1 (by rfl) ⟨2059181, by rfl⟩ : syracuseStep 2745575 = 4118363) B4118363
theorem B19195541 : Blo 115785 19195541 := bstep (se 6 (by rfl) ⟨449895, by rfl⟩ : syracuseStep 19195541 = 899791) B899791
theorem B2583089 : Blo 115785 2583089 := bstep (se 2 (by rfl) ⟨968658, by rfl⟩ : syracuseStep 2583089 = 1937317) B1937317
theorem B225983 : Blo 115785 225983 := bstep (se 1 (by rfl) ⟨169487, by rfl⟩ : syracuseStep 225983 = 338975) B338975
theorem B293291 : Blo 115785 293291 := bstep (se 1 (by rfl) ⟨219968, by rfl⟩ : syracuseStep 293291 = 439937) B439937
theorem B261503 : Blo 115785 261503 := bstep (se 1 (by rfl) ⟨196127, by rfl⟩ : syracuseStep 261503 = 392255) B392255
theorem B196715 : Blo 115785 196715 := bstep (se 1 (by rfl) ⟨147536, by rfl⟩ : syracuseStep 196715 = 295073) B295073
theorem B265967 : Blo 115785 265967 := bstep (se 1 (by rfl) ⟨199475, by rfl⟩ : syracuseStep 265967 = 398951) B398951
theorem B16586003 : Blo 115785 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B269063 : Blo 115785 269063 := bstep (se 1 (by rfl) ⟨201797, by rfl⟩ : syracuseStep 269063 = 403595) B403595
theorem B336935 : Blo 115785 336935 := bstep (se 1 (by rfl) ⟨252701, by rfl⟩ : syracuseStep 336935 = 505403) B505403
theorem B1124239 : Blo 115785 1124239 := bstep (se 1 (by rfl) ⟨843179, by rfl⟩ : syracuseStep 1124239 = 1686359) B1686359
theorem B403433 : Blo 115785 403433 := bstep (se 2 (by rfl) ⟨151287, by rfl⟩ : syracuseStep 403433 = 302575) B302575
theorem B174335 : Blo 115785 174335 := bstep (se 1 (by rfl) ⟨130751, by rfl⟩ : syracuseStep 174335 = 261503) B261503
theorem B403919 : Blo 115785 403919 := bstep (se 1 (by rfl) ⟨302939, by rfl⟩ : syracuseStep 403919 = 605879) B605879
theorem B175097 : Blo 115785 175097 := bstep (se 2 (by rfl) ⟨65661, by rfl⟩ : syracuseStep 175097 = 131323) B131323
theorem B896183 : Blo 115785 896183 := bstep (se 1 (by rfl) ⟨672137, by rfl⟩ : syracuseStep 896183 = 1344275) B1344275
theorem B176447 : Blo 115785 176447 := bstep (se 1 (by rfl) ⟨132335, by rfl⟩ : syracuseStep 176447 = 264671) B264671
theorem B177929 : Blo 115785 177929 := bstep (se 2 (by rfl) ⟨66723, by rfl⟩ : syracuseStep 177929 = 133447) B133447
theorem B178223 : Blo 115785 178223 := bstep (se 1 (by rfl) ⟨133667, by rfl⟩ : syracuseStep 178223 = 267335) B267335
theorem B375131 : Blo 115785 375131 := bstep (se 1 (by rfl) ⟨281348, by rfl⟩ : syracuseStep 375131 = 562697) B562697
theorem B179435 : Blo 115785 179435 := bstep (se 1 (by rfl) ⟨134576, by rfl⟩ : syracuseStep 179435 = 269153) B269153
theorem B2703269 : Blo 115785 2703269 := bstep (se 4 (by rfl) ⟨253431, by rfl⟩ : syracuseStep 2703269 = 506863) B506863
theorem B442655 : Blo 115785 442655 := bstep (se 1 (by rfl) ⟨331991, by rfl⟩ : syracuseStep 442655 = 663983) B663983
theorem B1524203 : Blo 115785 1524203 := bstep (se 1 (by rfl) ⟨1143152, by rfl⟩ : syracuseStep 1524203 = 2286305) B2286305
theorem B12797027 : Blo 115785 12797027 := bstep (se 1 (by rfl) ⟨9597770, by rfl⟩ : syracuseStep 12797027 = 19195541) B19195541
theorem B115967 : Blo 115785 115967 := bstep (se 1 (by rfl) ⟨86975, by rfl⟩ : syracuseStep 115967 = 173951) B173951
theorem B1722059 : Blo 115785 1722059 := bstep (se 1 (by rfl) ⟨1291544, by rfl⟩ : syracuseStep 1722059 = 2583089) B2583089
theorem B838511 : Blo 115785 838511 := bstep (se 1 (by rfl) ⟨628883, by rfl⟩ : syracuseStep 838511 = 1257767) B1257767
theorem B117759 : Blo 115785 117759 := bstep (se 1 (by rfl) ⟨88319, by rfl⟩ : syracuseStep 117759 = 176639) B176639
theorem B150655 : Blo 115785 150655 := bstep (se 1 (by rfl) ⟨112991, by rfl⟩ : syracuseStep 150655 = 225983) B225983
theorem B117915 : Blo 115785 117915 := bstep (se 1 (by rfl) ⟨88436, by rfl⟩ : syracuseStep 117915 = 176873) B176873
theorem B117919 : Blo 115785 117919 := bstep (se 1 (by rfl) ⟨88439, by rfl⟩ : syracuseStep 117919 = 176879) B176879
theorem B970471 : Blo 115785 970471 := bstep (se 1 (by rfl) ⟨727853, by rfl⟩ : syracuseStep 970471 = 1455707) B1455707
theorem B118783 : Blo 115785 118783 := bstep (se 1 (by rfl) ⟨89087, by rfl⟩ : syracuseStep 118783 = 178175) B178175
theorem B119295 : Blo 115785 119295 := bstep (se 1 (by rfl) ⟨89471, by rfl⟩ : syracuseStep 119295 = 178943) B178943
theorem B119323 : Blo 115785 119323 := bstep (se 1 (by rfl) ⟨89492, by rfl⟩ : syracuseStep 119323 = 178985) B178985
theorem B1335527 : Blo 115785 1335527 := bstep (se 1 (by rfl) ⟨1001645, by rfl⟩ : syracuseStep 1335527 = 2003291) B2003291
theorem B223393 : Blo 115785 223393 := bstep (se 2 (by rfl) ⟨83772, by rfl⟩ : syracuseStep 223393 = 167545) B167545
theorem B1830383 : Blo 115785 1830383 := bstep (se 1 (by rfl) ⟨1372787, by rfl⟩ : syracuseStep 1830383 = 2745575) B2745575
theorem B356447 : Blo 115785 356447 := bstep (se 1 (by rfl) ⟨267335, by rfl⟩ : syracuseStep 356447 = 534671) B534671
theorem B618745 : Blo 115785 618745 := bstep (se 2 (by rfl) ⟨232029, by rfl⟩ : syracuseStep 618745 = 464059) B464059
theorem B817391 : Blo 115785 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B195527 : Blo 115785 195527 := bstep (se 1 (by rfl) ⟨146645, by rfl⟩ : syracuseStep 195527 = 293291) B293291
theorem B9207647 : Blo 115785 9207647 := bstep (se 1 (by rfl) ⟨6905735, by rfl⟩ : syracuseStep 9207647 = 13811471) B13811471
theorem B131143 : Blo 115785 131143 := bstep (se 1 (by rfl) ⟨98357, by rfl⟩ : syracuseStep 131143 = 196715) B196715
theorem B295103 : Blo 115785 295103 := bstep (se 1 (by rfl) ⟨221327, by rfl⟩ : syracuseStep 295103 = 442655) B442655
theorem B950525 : Blo 115785 950525 := bstep (se 3 (by rfl) ⟨178223, by rfl⟩ : syracuseStep 950525 = 356447) B356447
theorem B1016135 : Blo 115785 1016135 := bstep (se 1 (by rfl) ⟨762101, by rfl⟩ : syracuseStep 1016135 = 1524203) B1524203
theorem B1148039 : Blo 115785 1148039 := bstep (se 1 (by rfl) ⟨861029, by rfl⟩ : syracuseStep 1148039 = 1722059) B1722059
theorem B559007 : Blo 115785 559007 := bstep (se 1 (by rfl) ⟨419255, by rfl⟩ : syracuseStep 559007 = 838511) B838511
theorem B297857 : Blo 115785 297857 := bstep (se 2 (by rfl) ⟨111696, by rfl⟩ : syracuseStep 297857 = 223393) B223393
theorem B200873 : Blo 115785 200873 := bstep (se 2 (by rfl) ⟨75327, by rfl⟩ : syracuseStep 200873 = 150655) B150655
theorem B890351 : Blo 115785 890351 := bstep (se 1 (by rfl) ⟨667763, by rfl⟩ : syracuseStep 890351 = 1335527) B1335527
theorem B824993 : Blo 115785 824993 := bstep (se 2 (by rfl) ⟨309372, by rfl⟩ : syracuseStep 824993 = 618745) B618745
theorem B268955 : Blo 115785 268955 := bstep (se 1 (by rfl) ⟨201716, by rfl⟩ : syracuseStep 268955 = 403433) B403433
theorem B269279 : Blo 115785 269279 := bstep (se 1 (by rfl) ⟨201959, by rfl⟩ : syracuseStep 269279 = 403919) B403919
theorem B597455 : Blo 115785 597455 := bstep (se 1 (by rfl) ⟨448091, by rfl⟩ : syracuseStep 597455 = 896183) B896183
theorem B1220255 : Blo 115785 1220255 := bstep (se 1 (by rfl) ⟨915191, by rfl⟩ : syracuseStep 1220255 = 1830383) B1830383
theorem B6138431 : Blo 115785 6138431 := bstep (se 1 (by rfl) ⟨4603823, by rfl⟩ : syracuseStep 6138431 = 9207647) B9207647
theorem B633509 : Blo 115785 633509 := bstep (se 4 (by rfl) ⟨59391, by rfl⟩ : syracuseStep 633509 = 118783) B118783
theorem B8531351 : Blo 115785 8531351 := bstep (se 1 (by rfl) ⟨6398513, by rfl⟩ : syracuseStep 8531351 = 12797027) B12797027
theorem B177311 : Blo 115785 177311 := bstep (se 1 (by rfl) ⟨132983, by rfl⟩ : syracuseStep 177311 = 265967) B265967
theorem B179375 : Blo 115785 179375 := bstep (se 1 (by rfl) ⟨134531, by rfl⟩ : syracuseStep 179375 = 269063) B269063
theorem B2179709 : Blo 115785 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B1000349 : Blo 115785 1000349 := bstep (se 3 (by rfl) ⟨187565, by rfl⟩ : syracuseStep 1000349 = 375131) B375131
theorem B116223 : Blo 115785 116223 := bstep (se 1 (by rfl) ⟨87167, by rfl⟩ : syracuseStep 116223 = 174335) B174335
theorem B116731 : Blo 115785 116731 := bstep (se 1 (by rfl) ⟨87548, by rfl⟩ : syracuseStep 116731 = 175097) B175097
theorem B117631 : Blo 115785 117631 := bstep (se 1 (by rfl) ⟨88223, by rfl⟩ : syracuseStep 117631 = 176447) B176447
theorem B478493 : Blo 115785 478493 := bstep (se 3 (by rfl) ⟨89717, by rfl⟩ : syracuseStep 478493 = 179435) B179435
theorem B118619 : Blo 115785 118619 := bstep (se 1 (by rfl) ⟨88964, by rfl⟩ : syracuseStep 118619 = 177929) B177929
theorem B118815 : Blo 115785 118815 := bstep (se 1 (by rfl) ⟨89111, by rfl⟩ : syracuseStep 118815 = 178223) B178223
theorem B119623 : Blo 115785 119623 := bstep (se 1 (by rfl) ⟨89717, by rfl⟩ : syracuseStep 119623 = 179435) B179435
theorem B1498985 : Blo 115785 1498985 := bstep (se 2 (by rfl) ⟨562119, by rfl⟩ : syracuseStep 1498985 = 1124239) B1124239
theorem B44229341 : Blo 115785 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B224623 : Blo 115785 224623 := bstep (se 1 (by rfl) ⟨168467, by rfl⟩ : syracuseStep 224623 = 336935) B336935
theorem B5175845 : Blo 115785 5175845 := bstep (se 4 (by rfl) ⟨485235, by rfl⟩ : syracuseStep 5175845 = 970471) B970471
theorem B130351 : Blo 115785 130351 := bstep (se 1 (by rfl) ⟨97763, by rfl⟩ : syracuseStep 130351 = 195527) B195527
theorem B1802179 : Blo 115785 1802179 := bstep (se 1 (by rfl) ⟨1351634, by rfl⟩ : syracuseStep 1802179 = 2703269) B2703269
theorem B196735 : Blo 115785 196735 := bstep (se 1 (by rfl) ⟨147551, by rfl⟩ : syracuseStep 196735 = 295103) B295103
theorem B198571 : Blo 115785 198571 := bstep (se 1 (by rfl) ⟨148928, by rfl⟩ : syracuseStep 198571 = 297857) B297857
theorem B133915 : Blo 115785 133915 := bstep (se 1 (by rfl) ⟨100436, by rfl⟩ : syracuseStep 133915 = 200873) B200873
theorem B593567 : Blo 115785 593567 := bstep (se 1 (by rfl) ⟨445175, by rfl⟩ : syracuseStep 593567 = 890351) B890351
theorem B299497 : Blo 115785 299497 := bstep (se 2 (by rfl) ⟨112311, by rfl⟩ : syracuseStep 299497 = 224623) B224623
theorem B398303 : Blo 115785 398303 := bstep (se 1 (by rfl) ⟨298727, by rfl⟩ : syracuseStep 398303 = 597455) B597455
theorem B3450563 : Blo 115785 3450563 := bstep (se 1 (by rfl) ⟨2587922, by rfl⟩ : syracuseStep 3450563 = 5175845) B5175845
theorem B173801 : Blo 115785 173801 := bstep (se 2 (by rfl) ⟨65175, by rfl⟩ : syracuseStep 173801 = 130351) B130351
theorem B2402905 : Blo 115785 2402905 := bstep (se 2 (by rfl) ⟨901089, by rfl⟩ : syracuseStep 2402905 = 1802179) B1802179
theorem B174857 : Blo 115785 174857 := bstep (se 2 (by rfl) ⟨65571, by rfl⟩ : syracuseStep 174857 = 131143) B131143
theorem B633683 : Blo 115785 633683 := bstep (se 1 (by rfl) ⟨475262, by rfl⟩ : syracuseStep 633683 = 950525) B950525
theorem B1453139 : Blo 115785 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B666899 : Blo 115785 666899 := bstep (se 1 (by rfl) ⟨500174, by rfl⟩ : syracuseStep 666899 = 1000349) B1000349
theorem B765359 : Blo 115785 765359 := bstep (se 1 (by rfl) ⟨574019, by rfl⟩ : syracuseStep 765359 = 1148039) B1148039
theorem B372671 : Blo 115785 372671 := bstep (se 1 (by rfl) ⟨279503, by rfl⟩ : syracuseStep 372671 = 559007) B559007
theorem B179303 : Blo 115785 179303 := bstep (se 1 (by rfl) ⟨134477, by rfl⟩ : syracuseStep 179303 = 268955) B268955
theorem B179519 : Blo 115785 179519 := bstep (se 1 (by rfl) ⟨134639, by rfl⟩ : syracuseStep 179519 = 269279) B269279
theorem B999323 : Blo 115785 999323 := bstep (se 1 (by rfl) ⟨749492, by rfl⟩ : syracuseStep 999323 = 1498985) B1498985
theorem B5687567 : Blo 115785 5687567 := bstep (se 1 (by rfl) ⟨4265675, by rfl⟩ : syracuseStep 5687567 = 8531351) B8531351
theorem B118207 : Blo 115785 118207 := bstep (se 1 (by rfl) ⟨88655, by rfl⟩ : syracuseStep 118207 = 177311) B177311
theorem B119583 : Blo 115785 119583 := bstep (se 1 (by rfl) ⟨89687, by rfl⟩ : syracuseStep 119583 = 179375) B179375
theorem B677423 : Blo 115785 677423 := bstep (se 1 (by rfl) ⟨508067, by rfl⟩ : syracuseStep 677423 = 1016135) B1016135
theorem B318995 : Blo 115785 318995 := bstep (se 1 (by rfl) ⟨239246, by rfl⟩ : syracuseStep 318995 = 478493) B478493
theorem B549995 : Blo 115785 549995 := bstep (se 1 (by rfl) ⟨412496, by rfl⟩ : syracuseStep 549995 = 824993) B824993
theorem B813503 : Blo 115785 813503 := bstep (se 1 (by rfl) ⟨610127, by rfl⟩ : syracuseStep 813503 = 1220255) B1220255
theorem B29486227 : Blo 115785 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B4092287 : Blo 115785 4092287 := bstep (se 1 (by rfl) ⟨3069215, by rfl⟩ : syracuseStep 4092287 = 6138431) B6138431
theorem B422339 : Blo 115785 422339 := bstep (se 1 (by rfl) ⟨316754, by rfl⟩ : syracuseStep 422339 = 633509) B633509
theorem B262313 : Blo 115785 262313 := bstep (se 2 (by rfl) ⟨98367, by rfl⟩ : syracuseStep 262313 = 196735) B196735
theorem B10912765 : Blo 115785 10912765 := bstep (se 3 (by rfl) ⟨2046143, by rfl⟩ : syracuseStep 10912765 = 4092287) B4092287
theorem B5866613 : Blo 115785 5866613 := bstep (se 5 (by rfl) ⟨274997, by rfl⟩ : syracuseStep 5866613 = 549995) B549995
theorem B395711 : Blo 115785 395711 := bstep (se 1 (by rfl) ⟨296783, by rfl⟩ : syracuseStep 395711 = 593567) B593567
theorem B264761 : Blo 115785 264761 := bstep (se 2 (by rfl) ⟨99285, by rfl⟩ : syracuseStep 264761 = 198571) B198571
theorem B265535 : Blo 115785 265535 := bstep (se 1 (by rfl) ⟨199151, by rfl⟩ : syracuseStep 265535 = 398303) B398303
theorem B399329 : Blo 115785 399329 := bstep (se 2 (by rfl) ⟨149748, by rfl⟩ : syracuseStep 399329 = 299497) B299497
theorem B2300375 : Blo 115785 2300375 := bstep (se 1 (by rfl) ⟨1725281, by rfl⟩ : syracuseStep 2300375 = 3450563) B3450563
theorem B666215 : Blo 115785 666215 := bstep (se 1 (by rfl) ⟨499661, by rfl⟩ : syracuseStep 666215 = 999323) B999323
theorem B1126237 : Blo 115785 1126237 := bstep (se 3 (by rfl) ⟨211169, by rfl⟩ : syracuseStep 1126237 = 422339) B422339
theorem B178553 : Blo 115785 178553 := bstep (se 2 (by rfl) ⟨66957, by rfl⟩ : syracuseStep 178553 = 133915) B133915
theorem B212663 : Blo 115785 212663 := bstep (se 1 (by rfl) ⟨159497, by rfl⟩ : syracuseStep 212663 = 318995) B318995
theorem B115867 : Blo 115785 115867 := bstep (se 1 (by rfl) ⟨86900, by rfl⟩ : syracuseStep 115867 = 173801) B173801
theorem B542335 : Blo 115785 542335 := bstep (se 1 (by rfl) ⟨406751, by rfl⟩ : syracuseStep 542335 = 813503) B813503
theorem B116571 : Blo 115785 116571 := bstep (se 1 (by rfl) ⟨87428, by rfl⟩ : syracuseStep 116571 = 174857) B174857
theorem B968759 : Blo 115785 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B444599 : Blo 115785 444599 := bstep (se 1 (by rfl) ⟨333449, by rfl⟩ : syracuseStep 444599 = 666899) B666899
theorem B1689821 : Blo 115785 1689821 := bstep (se 3 (by rfl) ⟨316841, by rfl⟩ : syracuseStep 1689821 = 633683) B633683
theorem B510239 : Blo 115785 510239 := bstep (se 1 (by rfl) ⟨382679, by rfl⟩ : syracuseStep 510239 = 765359) B765359
theorem B248447 : Blo 115785 248447 := bstep (se 1 (by rfl) ⟨186335, by rfl⟩ : syracuseStep 248447 = 372671) B372671
theorem B119535 : Blo 115785 119535 := bstep (se 1 (by rfl) ⟨89651, by rfl⟩ : syracuseStep 119535 = 179303) B179303
theorem B119679 : Blo 115785 119679 := bstep (se 1 (by rfl) ⟨89759, by rfl⟩ : syracuseStep 119679 = 179519) B179519
theorem B3791711 : Blo 115785 3791711 := bstep (se 1 (by rfl) ⟨2843783, by rfl⟩ : syracuseStep 3791711 = 5687567) B5687567
theorem B3203873 : Blo 115785 3203873 := bstep (se 2 (by rfl) ⟨1201452, by rfl⟩ : syracuseStep 3203873 = 2402905) B2402905
theorem B451615 : Blo 115785 451615 := bstep (se 1 (by rfl) ⟨338711, by rfl⟩ : syracuseStep 451615 = 677423) B677423
theorem B39314969 : Blo 115785 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B14550353 : Blo 115785 14550353 := bstep (se 2 (by rfl) ⟨5456382, by rfl⟩ : syracuseStep 14550353 = 10912765) B10912765
theorem B296399 : Blo 115785 296399 := bstep (se 1 (by rfl) ⟨222299, by rfl⟩ : syracuseStep 296399 = 444599) B444599
theorem B263807 : Blo 115785 263807 := bstep (se 1 (by rfl) ⟨197855, by rfl⟩ : syracuseStep 263807 = 395711) B395711
theorem B723113 : Blo 115785 723113 := bstep (se 2 (by rfl) ⟨271167, by rfl⟩ : syracuseStep 723113 = 542335) B542335
theorem B266219 : Blo 115785 266219 := bstep (se 1 (by rfl) ⟨199664, by rfl⟩ : syracuseStep 266219 = 399329) B399329
theorem B2527807 : Blo 115785 2527807 := bstep (se 1 (by rfl) ⟨1895855, by rfl⟩ : syracuseStep 2527807 = 3791711) B3791711
theorem B2135915 : Blo 115785 2135915 := bstep (se 1 (by rfl) ⟨1601936, by rfl⟩ : syracuseStep 2135915 = 3203873) B3203873
theorem B662525 : Blo 115785 662525 := bstep (se 3 (by rfl) ⟨124223, by rfl⟩ : syracuseStep 662525 = 248447) B248447
theorem B567101 : Blo 115785 567101 := bstep (se 3 (by rfl) ⟨106331, by rfl⟩ : syracuseStep 567101 = 212663) B212663
theorem B174875 : Blo 115785 174875 := bstep (se 1 (by rfl) ⟨131156, by rfl⟩ : syracuseStep 174875 = 262313) B262313
theorem B3911075 : Blo 115785 3911075 := bstep (se 1 (by rfl) ⟨2933306, by rfl⟩ : syracuseStep 3911075 = 5866613) B5866613
theorem B602153 : Blo 115785 602153 := bstep (se 2 (by rfl) ⟨225807, by rfl⟩ : syracuseStep 602153 = 451615) B451615
theorem B1126547 : Blo 115785 1126547 := bstep (se 1 (by rfl) ⟨844910, by rfl⟩ : syracuseStep 1126547 = 1689821) B1689821
theorem B340159 : Blo 115785 340159 := bstep (se 1 (by rfl) ⟨255119, by rfl⟩ : syracuseStep 340159 = 510239) B510239
theorem B176507 : Blo 115785 176507 := bstep (se 1 (by rfl) ⟨132380, by rfl⟩ : syracuseStep 176507 = 264761) B264761
theorem B177023 : Blo 115785 177023 := bstep (se 1 (by rfl) ⟨132767, by rfl⟩ : syracuseStep 177023 = 265535) B265535
theorem B444143 : Blo 115785 444143 := bstep (se 1 (by rfl) ⟨333107, by rfl⟩ : syracuseStep 444143 = 666215) B666215
theorem B119035 : Blo 115785 119035 := bstep (se 1 (by rfl) ⟨89276, by rfl⟩ : syracuseStep 119035 = 178553) B178553
theorem B645839 : Blo 115785 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B1533583 : Blo 115785 1533583 := bstep (se 1 (by rfl) ⟨1150187, by rfl⟩ : syracuseStep 1533583 = 2300375) B2300375
theorem B1501649 : Blo 115785 1501649 := bstep (se 2 (by rfl) ⟨563118, by rfl⟩ : syracuseStep 1501649 = 1126237) B1126237
theorem B26209979 : Blo 115785 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B9700235 : Blo 115785 9700235 := bstep (se 1 (by rfl) ⟨7275176, by rfl⟩ : syracuseStep 9700235 = 14550353) B14550353
theorem B197599 : Blo 115785 197599 := bstep (se 1 (by rfl) ⟨148199, by rfl⟩ : syracuseStep 197599 = 296399) B296399
theorem B296095 : Blo 115785 296095 := bstep (se 1 (by rfl) ⟨222071, by rfl⟩ : syracuseStep 296095 = 444143) B444143
theorem B430559 : Blo 115785 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B17473319 : Blo 115785 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B401435 : Blo 115785 401435 := bstep (se 1 (by rfl) ⟨301076, by rfl⟩ : syracuseStep 401435 = 602153) B602153
theorem B175871 : Blo 115785 175871 := bstep (se 1 (by rfl) ⟨131903, by rfl⟩ : syracuseStep 175871 = 263807) B263807
theorem B2044777 : Blo 115785 2044777 := bstep (se 2 (by rfl) ⟨766791, by rfl⟩ : syracuseStep 2044777 = 1533583) B1533583
theorem B177479 : Blo 115785 177479 := bstep (se 1 (by rfl) ⟨133109, by rfl⟩ : syracuseStep 177479 = 266219) B266219
theorem B1423943 : Blo 115785 1423943 := bstep (se 1 (by rfl) ⟨1067957, by rfl⟩ : syracuseStep 1423943 = 2135915) B2135915
theorem B441683 : Blo 115785 441683 := bstep (se 1 (by rfl) ⟨331262, by rfl⟩ : syracuseStep 441683 = 662525) B662525
theorem B378067 : Blo 115785 378067 := bstep (se 1 (by rfl) ⟨283550, by rfl⟩ : syracuseStep 378067 = 567101) B567101
theorem B1001099 : Blo 115785 1001099 := bstep (se 1 (by rfl) ⟨750824, by rfl⟩ : syracuseStep 1001099 = 1501649) B1501649
theorem B116583 : Blo 115785 116583 := bstep (se 1 (by rfl) ⟨87437, by rfl⟩ : syracuseStep 116583 = 174875) B174875
theorem B2607383 : Blo 115785 2607383 := bstep (se 1 (by rfl) ⟨1955537, by rfl⟩ : syracuseStep 2607383 = 3911075) B3911075
theorem B117671 : Blo 115785 117671 := bstep (se 1 (by rfl) ⟨88253, by rfl⟩ : syracuseStep 117671 = 176507) B176507
theorem B118015 : Blo 115785 118015 := bstep (se 1 (by rfl) ⟨88511, by rfl⟩ : syracuseStep 118015 = 177023) B177023
theorem B482075 : Blo 115785 482075 := bstep (se 1 (by rfl) ⟨361556, by rfl⟩ : syracuseStep 482075 = 723113) B723113
theorem B453545 : Blo 115785 453545 := bstep (se 2 (by rfl) ⟨170079, by rfl⟩ : syracuseStep 453545 = 340159) B340159
theorem B3370409 : Blo 115785 3370409 := bstep (se 2 (by rfl) ⟨1263903, by rfl⟩ : syracuseStep 3370409 = 2527807) B2527807
theorem B751031 : Blo 115785 751031 := bstep (se 1 (by rfl) ⟨563273, by rfl⟩ : syracuseStep 751031 = 1126547) B1126547
theorem B263465 : Blo 115785 263465 := bstep (se 2 (by rfl) ⟨98799, by rfl⟩ : syracuseStep 263465 = 197599) B197599
theorem B1738255 : Blo 115785 1738255 := bstep (se 1 (by rfl) ⟨1303691, by rfl⟩ : syracuseStep 1738255 = 2607383) B2607383
theorem B394793 : Blo 115785 394793 := bstep (se 2 (by rfl) ⟨148047, by rfl⟩ : syracuseStep 394793 = 296095) B296095
theorem B267623 : Blo 115785 267623 := bstep (se 1 (by rfl) ⟨200717, by rfl⟩ : syracuseStep 267623 = 401435) B401435
theorem B2726369 : Blo 115785 2726369 := bstep (se 2 (by rfl) ⟨1022388, by rfl⟩ : syracuseStep 2726369 = 2044777) B2044777
theorem B302363 : Blo 115785 302363 := bstep (se 1 (by rfl) ⟨226772, by rfl⟩ : syracuseStep 302363 = 453545) B453545
theorem B500687 : Blo 115785 500687 := bstep (se 1 (by rfl) ⟨375515, by rfl⟩ : syracuseStep 500687 = 751031) B751031
theorem B6466823 : Blo 115785 6466823 := bstep (se 1 (by rfl) ⟨4850117, by rfl⟩ : syracuseStep 6466823 = 9700235) B9700235
theorem B667399 : Blo 115785 667399 := bstep (se 1 (by rfl) ⟨500549, by rfl⟩ : syracuseStep 667399 = 1001099) B1001099
theorem B504089 : Blo 115785 504089 := bstep (se 2 (by rfl) ⟨189033, by rfl⟩ : syracuseStep 504089 = 378067) B378067
theorem B11648879 : Blo 115785 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B2246939 : Blo 115785 2246939 := bstep (se 1 (by rfl) ⟨1685204, by rfl⟩ : syracuseStep 2246939 = 3370409) B3370409
theorem B117247 : Blo 115785 117247 := bstep (se 1 (by rfl) ⟨87935, by rfl⟩ : syracuseStep 117247 = 175871) B175871
theorem B118319 : Blo 115785 118319 := bstep (se 1 (by rfl) ⟨88739, by rfl⟩ : syracuseStep 118319 = 177479) B177479
theorem B287039 : Blo 115785 287039 := bstep (se 1 (by rfl) ⟨215279, by rfl⟩ : syracuseStep 287039 = 430559) B430559
theorem B321383 : Blo 115785 321383 := bstep (se 1 (by rfl) ⟨241037, by rfl⟩ : syracuseStep 321383 = 482075) B482075
theorem B949295 : Blo 115785 949295 := bstep (se 1 (by rfl) ⟨711971, by rfl⟩ : syracuseStep 949295 = 1423943) B1423943
theorem B294455 : Blo 115785 294455 := bstep (se 1 (by rfl) ⟨220841, by rfl⟩ : syracuseStep 294455 = 441683) B441683
theorem B263195 : Blo 115785 263195 := bstep (se 1 (by rfl) ⟨197396, by rfl⟩ : syracuseStep 263195 = 394793) B394793
theorem B201575 : Blo 115785 201575 := bstep (se 1 (by rfl) ⟨151181, by rfl⟩ : syracuseStep 201575 = 302363) B302363
theorem B889865 : Blo 115785 889865 := bstep (se 2 (by rfl) ⟨333699, by rfl⟩ : syracuseStep 889865 = 667399) B667399
theorem B333791 : Blo 115785 333791 := bstep (se 1 (by rfl) ⟨250343, by rfl⟩ : syracuseStep 333791 = 500687) B500687
theorem B336059 : Blo 115785 336059 := bstep (se 1 (by rfl) ⟨252044, by rfl⟩ : syracuseStep 336059 = 504089) B504089
theorem B632863 : Blo 115785 632863 := bstep (se 1 (by rfl) ⟨474647, by rfl⟩ : syracuseStep 632863 = 949295) B949295
theorem B175643 : Blo 115785 175643 := bstep (se 1 (by rfl) ⟨131732, by rfl⟩ : syracuseStep 175643 = 263465) B263465
theorem B178415 : Blo 115785 178415 := bstep (se 1 (by rfl) ⟨133811, by rfl⟩ : syracuseStep 178415 = 267623) B267623
theorem B1817579 : Blo 115785 1817579 := bstep (se 1 (by rfl) ⟨1363184, by rfl⟩ : syracuseStep 1817579 = 2726369) B2726369
theorem B214255 : Blo 115785 214255 := bstep (se 1 (by rfl) ⟨160691, by rfl⟩ : syracuseStep 214255 = 321383) B321383
theorem B4311215 : Blo 115785 4311215 := bstep (se 1 (by rfl) ⟨3233411, by rfl⟩ : syracuseStep 4311215 = 6466823) B6466823
theorem B1497959 : Blo 115785 1497959 := bstep (se 1 (by rfl) ⟨1123469, by rfl⟩ : syracuseStep 1497959 = 2246939) B2246939
theorem B2317673 : Blo 115785 2317673 := bstep (se 2 (by rfl) ⟨869127, by rfl⟩ : syracuseStep 2317673 = 1738255) B1738255
theorem B191359 : Blo 115785 191359 := bstep (se 1 (by rfl) ⟨143519, by rfl⟩ : syracuseStep 191359 = 287039) B287039
theorem B196303 : Blo 115785 196303 := bstep (se 1 (by rfl) ⟨147227, by rfl⟩ : syracuseStep 196303 = 294455) B294455
theorem B7765919 : Blo 115785 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B134383 : Blo 115785 134383 := bstep (se 1 (by rfl) ⟨100787, by rfl⟩ : syracuseStep 134383 = 201575) B201575
theorem B593243 : Blo 115785 593243 := bstep (se 1 (by rfl) ⟨444932, by rfl⟩ : syracuseStep 593243 = 889865) B889865
theorem B175463 : Blo 115785 175463 := bstep (se 1 (by rfl) ⟨131597, by rfl⟩ : syracuseStep 175463 = 263195) B263195
theorem B998639 : Blo 115785 998639 := bstep (se 1 (by rfl) ⟨748979, by rfl⟩ : syracuseStep 998639 = 1497959) B1497959
theorem B117095 : Blo 115785 117095 := bstep (se 1 (by rfl) ⟨87821, by rfl⟩ : syracuseStep 117095 = 175643) B175643
theorem B6180461 : Blo 115785 6180461 := bstep (se 3 (by rfl) ⟨1158836, by rfl⟩ : syracuseStep 6180461 = 2317673) B2317673
theorem B118943 : Blo 115785 118943 := bstep (se 1 (by rfl) ⟨89207, by rfl⟩ : syracuseStep 118943 = 178415) B178415
theorem B2874143 : Blo 115785 2874143 := bstep (se 1 (by rfl) ⟨2155607, by rfl⟩ : syracuseStep 2874143 = 4311215) B4311215
theorem B843817 : Blo 115785 843817 := bstep (se 2 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 843817 = 632863) B632863
theorem B255145 : Blo 115785 255145 := bstep (se 2 (by rfl) ⟨95679, by rfl⟩ : syracuseStep 255145 = 191359) B191359
theorem B222527 : Blo 115785 222527 := bstep (se 1 (by rfl) ⟨166895, by rfl⟩ : syracuseStep 222527 = 333791) B333791
theorem B224039 : Blo 115785 224039 := bstep (se 1 (by rfl) ⟨168029, by rfl⟩ : syracuseStep 224039 = 336059) B336059
theorem B1142693 : Blo 115785 1142693 := bstep (se 4 (by rfl) ⟨107127, by rfl⟩ : syracuseStep 1142693 = 214255) B214255
theorem B1211719 : Blo 115785 1211719 := bstep (se 1 (by rfl) ⟨908789, by rfl⟩ : syracuseStep 1211719 = 1817579) B1817579
theorem B261737 : Blo 115785 261737 := bstep (se 2 (by rfl) ⟨98151, by rfl⟩ : syracuseStep 261737 = 196303) B196303
theorem B5177279 : Blo 115785 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B395495 : Blo 115785 395495 := bstep (se 1 (by rfl) ⟨296621, by rfl⟩ : syracuseStep 395495 = 593243) B593243
theorem B593405 : Blo 115785 593405 := bstep (se 3 (by rfl) ⟨111263, by rfl⟩ : syracuseStep 593405 = 222527) B222527
theorem B761795 : Blo 115785 761795 := bstep (se 1 (by rfl) ⟨571346, by rfl⟩ : syracuseStep 761795 = 1142693) B1142693
theorem B1615625 : Blo 115785 1615625 := bstep (se 2 (by rfl) ⟨605859, by rfl⟩ : syracuseStep 1615625 = 1211719) B1211719
theorem B665759 : Blo 115785 665759 := bstep (se 1 (by rfl) ⟨499319, by rfl⟩ : syracuseStep 665759 = 998639) B998639
theorem B174491 : Blo 115785 174491 := bstep (se 1 (by rfl) ⟨130868, by rfl⟩ : syracuseStep 174491 = 261737) B261737
theorem B13806077 : Blo 115785 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B1125089 : Blo 115785 1125089 := bstep (se 2 (by rfl) ⟨421908, by rfl⟩ : syracuseStep 1125089 = 843817) B843817
theorem B340193 : Blo 115785 340193 := bstep (se 2 (by rfl) ⟨127572, by rfl⟩ : syracuseStep 340193 = 255145) B255145
theorem B179177 : Blo 115785 179177 := bstep (se 2 (by rfl) ⟨67191, by rfl⟩ : syracuseStep 179177 = 134383) B134383
theorem B1916095 : Blo 115785 1916095 := bstep (se 1 (by rfl) ⟨1437071, by rfl⟩ : syracuseStep 1916095 = 2874143) B2874143
theorem B149359 : Blo 115785 149359 := bstep (se 1 (by rfl) ⟨112019, by rfl⟩ : syracuseStep 149359 = 224039) B224039
theorem B116975 : Blo 115785 116975 := bstep (se 1 (by rfl) ⟨87731, by rfl⟩ : syracuseStep 116975 = 175463) B175463
theorem B4120307 : Blo 115785 4120307 := bstep (se 1 (by rfl) ⟨3090230, by rfl⟩ : syracuseStep 4120307 = 6180461) B6180461
theorem B263663 : Blo 115785 263663 := bstep (se 1 (by rfl) ⟨197747, by rfl⟩ : syracuseStep 263663 = 395495) B395495
theorem B395603 : Blo 115785 395603 := bstep (se 1 (by rfl) ⟨296702, by rfl⟩ : syracuseStep 395603 = 593405) B593405
theorem B199145 : Blo 115785 199145 := bstep (se 2 (by rfl) ⟨74679, by rfl⟩ : syracuseStep 199145 = 149359) B149359
theorem B507863 : Blo 115785 507863 := bstep (se 1 (by rfl) ⟨380897, by rfl⟩ : syracuseStep 507863 = 761795) B761795
theorem B36816205 : Blo 115785 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B443839 : Blo 115785 443839 := bstep (se 1 (by rfl) ⟨332879, by rfl⟩ : syracuseStep 443839 = 665759) B665759
theorem B116327 : Blo 115785 116327 := bstep (se 1 (by rfl) ⟨87245, by rfl⟩ : syracuseStep 116327 = 174491) B174491
theorem B119451 : Blo 115785 119451 := bstep (se 1 (by rfl) ⟨89588, by rfl⟩ : syracuseStep 119451 = 179177) B179177
theorem B2746871 : Blo 115785 2746871 := bstep (se 1 (by rfl) ⟨2060153, by rfl⟩ : syracuseStep 2746871 = 4120307) B4120307
theorem B1077083 : Blo 115785 1077083 := bstep (se 1 (by rfl) ⟨807812, by rfl⟩ : syracuseStep 1077083 = 1615625) B1615625
theorem B750059 : Blo 115785 750059 := bstep (se 1 (by rfl) ⟨562544, by rfl⟩ : syracuseStep 750059 = 1125089) B1125089
theorem B226795 : Blo 115785 226795 := bstep (se 1 (by rfl) ⟨170096, by rfl⟩ : syracuseStep 226795 = 340193) B340193
theorem B2554793 : Blo 115785 2554793 := bstep (se 2 (by rfl) ⟨958047, by rfl⟩ : syracuseStep 2554793 = 1916095) B1916095
theorem B263735 : Blo 115785 263735 := bstep (se 1 (by rfl) ⟨197801, by rfl⟩ : syracuseStep 263735 = 395603) B395603
theorem B132763 : Blo 115785 132763 := bstep (se 1 (by rfl) ⟨99572, by rfl⟩ : syracuseStep 132763 = 199145) B199145
theorem B49088273 : Blo 115785 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B591785 : Blo 115785 591785 := bstep (se 2 (by rfl) ⟨221919, by rfl⟩ : syracuseStep 591785 = 443839) B443839
theorem B302393 : Blo 115785 302393 := bstep (se 2 (by rfl) ⟨113397, by rfl⟩ : syracuseStep 302393 = 226795) B226795
theorem B500039 : Blo 115785 500039 := bstep (se 1 (by rfl) ⟨375029, by rfl⟩ : syracuseStep 500039 = 750059) B750059
theorem B338575 : Blo 115785 338575 := bstep (se 1 (by rfl) ⟨253931, by rfl⟩ : syracuseStep 338575 = 507863) B507863
theorem B175775 : Blo 115785 175775 := bstep (se 1 (by rfl) ⟨131831, by rfl⟩ : syracuseStep 175775 = 263663) B263663
theorem B1831247 : Blo 115785 1831247 := bstep (se 1 (by rfl) ⟨1373435, by rfl⟩ : syracuseStep 1831247 = 2746871) B2746871
theorem B718055 : Blo 115785 718055 := bstep (se 1 (by rfl) ⟨538541, by rfl⟩ : syracuseStep 718055 = 1077083) B1077083
theorem B1703195 : Blo 115785 1703195 := bstep (se 1 (by rfl) ⟨1277396, by rfl⟩ : syracuseStep 1703195 = 2554793) B2554793
theorem B394523 : Blo 115785 394523 := bstep (se 1 (by rfl) ⟨295892, by rfl⟩ : syracuseStep 394523 = 591785) B591785
theorem B201595 : Blo 115785 201595 := bstep (se 1 (by rfl) ⟨151196, by rfl⟩ : syracuseStep 201595 = 302393) B302393
theorem B333359 : Blo 115785 333359 := bstep (se 1 (by rfl) ⟨250019, by rfl⟩ : syracuseStep 333359 = 500039) B500039
theorem B523608245 : Blo 115785 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B1220831 : Blo 115785 1220831 := bstep (se 1 (by rfl) ⟨915623, by rfl⟩ : syracuseStep 1220831 = 1831247) B1831247
theorem B175823 : Blo 115785 175823 := bstep (se 1 (by rfl) ⟨131867, by rfl⟩ : syracuseStep 175823 = 263735) B263735
theorem B177017 : Blo 115785 177017 := bstep (se 2 (by rfl) ⟨66381, by rfl⟩ : syracuseStep 177017 = 132763) B132763
theorem B117183 : Blo 115785 117183 := bstep (se 1 (by rfl) ⟨87887, by rfl⟩ : syracuseStep 117183 = 175775) B175775
theorem B478703 : Blo 115785 478703 := bstep (se 1 (by rfl) ⟨359027, by rfl⟩ : syracuseStep 478703 = 718055) B718055
theorem B1135463 : Blo 115785 1135463 := bstep (se 1 (by rfl) ⟨851597, by rfl⟩ : syracuseStep 1135463 = 1703195) B1703195
theorem B451433 : Blo 115785 451433 := bstep (se 2 (by rfl) ⟨169287, by rfl⟩ : syracuseStep 451433 = 338575) B338575
theorem B263015 : Blo 115785 263015 := bstep (se 1 (by rfl) ⟨197261, by rfl⟩ : syracuseStep 263015 = 394523) B394523
theorem B300955 : Blo 115785 300955 := bstep (se 1 (by rfl) ⟨225716, by rfl⟩ : syracuseStep 300955 = 451433) B451433
theorem B268793 : Blo 115785 268793 := bstep (se 2 (by rfl) ⟨100797, by rfl⟩ : syracuseStep 268793 = 201595) B201595
theorem B3027901 : Blo 115785 3027901 := bstep (se 3 (by rfl) ⟨567731, by rfl⟩ : syracuseStep 3027901 = 1135463) B1135463
theorem B117215 : Blo 115785 117215 := bstep (se 1 (by rfl) ⟨87911, by rfl⟩ : syracuseStep 117215 = 175823) B175823
theorem B118011 : Blo 115785 118011 := bstep (se 1 (by rfl) ⟨88508, by rfl⟩ : syracuseStep 118011 = 177017) B177017
theorem B319135 : Blo 115785 319135 := bstep (se 1 (by rfl) ⟨239351, by rfl⟩ : syracuseStep 319135 = 478703) B478703
theorem B222239 : Blo 115785 222239 := bstep (se 1 (by rfl) ⟨166679, by rfl⟩ : syracuseStep 222239 = 333359) B333359
theorem B349072163 : Blo 115785 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B813887 : Blo 115785 813887 := bstep (se 1 (by rfl) ⟨610415, by rfl⟩ : syracuseStep 813887 = 1220831) B1220831
theorem B4037201 : Blo 115785 4037201 := bstep (se 2 (by rfl) ⟨1513950, by rfl⟩ : syracuseStep 4037201 = 3027901) B3027901
theorem B401273 : Blo 115785 401273 := bstep (se 2 (by rfl) ⟨150477, by rfl⟩ : syracuseStep 401273 = 300955) B300955
theorem B175343 : Blo 115785 175343 := bstep (se 1 (by rfl) ⟨131507, by rfl⟩ : syracuseStep 175343 = 263015) B263015
theorem B179195 : Blo 115785 179195 := bstep (se 1 (by rfl) ⟨134396, by rfl⟩ : syracuseStep 179195 = 268793) B268793
theorem B148159 : Blo 115785 148159 := bstep (se 1 (by rfl) ⟨111119, by rfl⟩ : syracuseStep 148159 = 222239) B222239
theorem B542591 : Blo 115785 542591 := bstep (se 1 (by rfl) ⟨406943, by rfl⟩ : syracuseStep 542591 = 813887) B813887
theorem B232714775 : Blo 115785 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B425513 : Blo 115785 425513 := bstep (se 2 (by rfl) ⟨159567, by rfl⟩ : syracuseStep 425513 = 319135) B319135
theorem B197545 : Blo 115785 197545 := bstep (se 2 (by rfl) ⟨74079, by rfl⟩ : syracuseStep 197545 = 148159) B148159
theorem B361727 : Blo 115785 361727 := bstep (se 1 (by rfl) ⟨271295, by rfl⟩ : syracuseStep 361727 = 542591) B542591
theorem B2691467 : Blo 115785 2691467 := bstep (se 1 (by rfl) ⟨2018600, by rfl⟩ : syracuseStep 2691467 = 4037201) B4037201
theorem B267515 : Blo 115785 267515 := bstep (se 1 (by rfl) ⟨200636, by rfl⟩ : syracuseStep 267515 = 401273) B401273
theorem B116895 : Blo 115785 116895 := bstep (se 1 (by rfl) ⟨87671, by rfl⟩ : syracuseStep 116895 = 175343) B175343
theorem B155143183 : Blo 115785 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B119463 : Blo 115785 119463 := bstep (se 1 (by rfl) ⟨89597, by rfl⟩ : syracuseStep 119463 = 179195) B179195
theorem B283675 : Blo 115785 283675 := bstep (se 1 (by rfl) ⟨212756, by rfl⟩ : syracuseStep 283675 = 425513) B425513
theorem B263393 : Blo 115785 263393 := bstep (se 2 (by rfl) ⟨98772, by rfl⟩ : syracuseStep 263393 = 197545) B197545
theorem B241151 : Blo 115785 241151 := bstep (se 1 (by rfl) ⟨180863, by rfl⟩ : syracuseStep 241151 = 361727) B361727
theorem B178343 : Blo 115785 178343 := bstep (se 1 (by rfl) ⟨133757, by rfl⟩ : syracuseStep 178343 = 267515) B267515
theorem B378233 : Blo 115785 378233 := bstep (se 2 (by rfl) ⟨141837, by rfl⟩ : syracuseStep 378233 = 283675) B283675
theorem B1794311 : Blo 115785 1794311 := bstep (se 1 (by rfl) ⟨1345733, by rfl⟩ : syracuseStep 1794311 = 2691467) B2691467
theorem B206857577 : Blo 115785 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B175595 : Blo 115785 175595 := bstep (se 1 (by rfl) ⟨131696, by rfl⟩ : syracuseStep 175595 = 263393) B263393
theorem B1196207 : Blo 115785 1196207 := bstep (se 1 (by rfl) ⟨897155, by rfl⟩ : syracuseStep 1196207 = 1794311) B1794311
theorem B137905051 : Blo 115785 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B643069 : Blo 115785 643069 := bstep (se 3 (by rfl) ⟨120575, by rfl⟩ : syracuseStep 643069 = 241151) B241151
theorem B118895 : Blo 115785 118895 := bstep (se 1 (by rfl) ⟨89171, by rfl⟩ : syracuseStep 118895 = 178343) B178343
theorem B252155 : Blo 115785 252155 := bstep (se 1 (by rfl) ⟨189116, by rfl⟩ : syracuseStep 252155 = 378233) B378233
theorem B168103 : Blo 115785 168103 := bstep (se 1 (by rfl) ⟨126077, by rfl⟩ : syracuseStep 168103 = 252155) B252155
theorem B857425 : Blo 115785 857425 := bstep (se 2 (by rfl) ⟨321534, by rfl⟩ : syracuseStep 857425 = 643069) B643069
theorem B797471 : Blo 115785 797471 := bstep (se 1 (by rfl) ⟨598103, by rfl⟩ : syracuseStep 797471 = 1196207) B1196207
theorem B183873401 : Blo 115785 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B117063 : Blo 115785 117063 := bstep (se 1 (by rfl) ⟨87797, by rfl⟩ : syracuseStep 117063 = 175595) B175595
theorem B531647 : Blo 115785 531647 := bstep (se 1 (by rfl) ⟨398735, by rfl⟩ : syracuseStep 531647 = 797471) B797471
theorem B224137 : Blo 115785 224137 := bstep (se 2 (by rfl) ⟨84051, by rfl⟩ : syracuseStep 224137 = 168103) B168103
theorem B1143233 : Blo 115785 1143233 := bstep (se 2 (by rfl) ⟨428712, by rfl⟩ : syracuseStep 1143233 = 857425) B857425
theorem B122582267 : Blo 115785 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B298849 : Blo 115785 298849 := bstep (se 2 (by rfl) ⟨112068, by rfl⟩ : syracuseStep 298849 = 224137) B224137
theorem B762155 : Blo 115785 762155 := bstep (se 1 (by rfl) ⟨571616, by rfl⟩ : syracuseStep 762155 = 1143233) B1143233
theorem B354431 : Blo 115785 354431 := bstep (se 1 (by rfl) ⟨265823, by rfl⟩ : syracuseStep 354431 = 531647) B531647
theorem B81721511 : Blo 115785 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B398465 : Blo 115785 398465 := bstep (se 2 (by rfl) ⟨149424, by rfl⟩ : syracuseStep 398465 = 298849) B298849
theorem B236287 : Blo 115785 236287 := bstep (se 1 (by rfl) ⟨177215, by rfl⟩ : syracuseStep 236287 = 354431) B354431
theorem B508103 : Blo 115785 508103 := bstep (se 1 (by rfl) ⟨381077, by rfl⟩ : syracuseStep 508103 = 762155) B762155
theorem B54481007 : Blo 115785 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B265643 : Blo 115785 265643 := bstep (se 1 (by rfl) ⟨199232, by rfl⟩ : syracuseStep 265643 = 398465) B398465
theorem B338735 : Blo 115785 338735 := bstep (se 1 (by rfl) ⟨254051, by rfl⟩ : syracuseStep 338735 = 508103) B508103
theorem B36320671 : Blo 115785 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B315049 : Blo 115785 315049 := bstep (se 2 (by rfl) ⟨118143, by rfl⟩ : syracuseStep 315049 = 236287) B236287
theorem B177095 : Blo 115785 177095 := bstep (se 1 (by rfl) ⟨132821, by rfl⟩ : syracuseStep 177095 = 265643) B265643
theorem B420065 : Blo 115785 420065 := bstep (se 2 (by rfl) ⟨157524, by rfl⟩ : syracuseStep 420065 = 315049) B315049
theorem B225823 : Blo 115785 225823 := bstep (se 1 (by rfl) ⟨169367, by rfl⟩ : syracuseStep 225823 = 338735) B338735
theorem B48427561 : Blo 115785 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B301097 : Blo 115785 301097 := bstep (se 2 (by rfl) ⟨112911, by rfl⟩ : syracuseStep 301097 = 225823) B225823
theorem B64570081 : Blo 115785 64570081 := bstep (se 2 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 64570081 = 48427561) B48427561
theorem B280043 : Blo 115785 280043 := bstep (se 1 (by rfl) ⟨210032, by rfl⟩ : syracuseStep 280043 = 420065) B420065
theorem B118063 : Blo 115785 118063 := bstep (se 1 (by rfl) ⟨88547, by rfl⟩ : syracuseStep 118063 = 177095) B177095
theorem B200731 : Blo 115785 200731 := bstep (se 1 (by rfl) ⟨150548, by rfl⟩ : syracuseStep 200731 = 301097) B301097
theorem B86093441 : Blo 115785 86093441 := bstep (se 2 (by rfl) ⟨32285040, by rfl⟩ : syracuseStep 86093441 = 64570081) B64570081
theorem B186695 : Blo 115785 186695 := bstep (se 1 (by rfl) ⟨140021, by rfl⟩ : syracuseStep 186695 = 280043) B280043
theorem B267641 : Blo 115785 267641 := bstep (se 2 (by rfl) ⟨100365, by rfl⟩ : syracuseStep 267641 = 200731) B200731
theorem B57395627 : Blo 115785 57395627 := bstep (se 1 (by rfl) ⟨43046720, by rfl⟩ : syracuseStep 57395627 = 86093441) B86093441
theorem B124463 : Blo 115785 124463 := bstep (se 1 (by rfl) ⟨93347, by rfl⟩ : syracuseStep 124463 = 186695) B186695
theorem B331901 : Blo 115785 331901 := bstep (se 3 (by rfl) ⟨62231, by rfl⟩ : syracuseStep 331901 = 124463) B124463
theorem B178427 : Blo 115785 178427 := bstep (se 1 (by rfl) ⟨133820, by rfl⟩ : syracuseStep 178427 = 267641) B267641
theorem B38263751 : Blo 115785 38263751 := bstep (se 1 (by rfl) ⟨28697813, by rfl⟩ : syracuseStep 38263751 = 57395627) B57395627
theorem B25509167 : Blo 115785 25509167 := bstep (se 1 (by rfl) ⟨19131875, by rfl⟩ : syracuseStep 25509167 = 38263751) B38263751
theorem B118951 : Blo 115785 118951 := bstep (se 1 (by rfl) ⟨89213, by rfl⟩ : syracuseStep 118951 = 178427) B178427
theorem B221267 : Blo 115785 221267 := bstep (se 1 (by rfl) ⟨165950, by rfl⟩ : syracuseStep 221267 = 331901) B331901
theorem B147511 : Blo 115785 147511 := bstep (se 1 (by rfl) ⟨110633, by rfl⟩ : syracuseStep 147511 = 221267) B221267
theorem B17006111 : Blo 115785 17006111 := bstep (se 1 (by rfl) ⟨12754583, by rfl⟩ : syracuseStep 17006111 = 25509167) B25509167
theorem B196681 : Blo 115785 196681 := bstep (se 2 (by rfl) ⟨73755, by rfl⟩ : syracuseStep 196681 = 147511) B147511
theorem B11337407 : Blo 115785 11337407 := bstep (se 1 (by rfl) ⟨8503055, by rfl⟩ : syracuseStep 11337407 = 17006111) B17006111
theorem B262241 : Blo 115785 262241 := bstep (se 2 (by rfl) ⟨98340, by rfl⟩ : syracuseStep 262241 = 196681) B196681
theorem B7558271 : Blo 115785 7558271 := bstep (se 1 (by rfl) ⟨5668703, by rfl⟩ : syracuseStep 7558271 = 11337407) B11337407
theorem B174827 : Blo 115785 174827 := bstep (se 1 (by rfl) ⟨131120, by rfl⟩ : syracuseStep 174827 = 262241) B262241
theorem B5038847 : Blo 115785 5038847 := bstep (se 1 (by rfl) ⟨3779135, by rfl⟩ : syracuseStep 5038847 = 7558271) B7558271
theorem B3359231 : Blo 115785 3359231 := bstep (se 1 (by rfl) ⟨2519423, by rfl⟩ : syracuseStep 3359231 = 5038847) B5038847
theorem B116551 : Blo 115785 116551 := bstep (se 1 (by rfl) ⟨87413, by rfl⟩ : syracuseStep 116551 = 174827) B174827
theorem B2239487 : Blo 115785 2239487 := bstep (se 1 (by rfl) ⟨1679615, by rfl⟩ : syracuseStep 2239487 = 3359231) B3359231
theorem B1492991 : Blo 115785 1492991 := bstep (se 1 (by rfl) ⟨1119743, by rfl⟩ : syracuseStep 1492991 = 2239487) B2239487
theorem B995327 : Blo 115785 995327 := bstep (se 1 (by rfl) ⟨746495, by rfl⟩ : syracuseStep 995327 = 1492991) B1492991
theorem B663551 : Blo 115785 663551 := bstep (se 1 (by rfl) ⟨497663, by rfl⟩ : syracuseStep 663551 = 995327) B995327
theorem B442367 : Blo 115785 442367 := bstep (se 1 (by rfl) ⟨331775, by rfl⟩ : syracuseStep 442367 = 663551) B663551
theorem B294911 : Blo 115785 294911 := bstep (se 1 (by rfl) ⟨221183, by rfl⟩ : syracuseStep 294911 = 442367) B442367
theorem B196607 : Blo 115785 196607 := bstep (se 1 (by rfl) ⟨147455, by rfl⟩ : syracuseStep 196607 = 294911) B294911
theorem B131071 : Blo 115785 131071 := bstep (se 1 (by rfl) ⟨98303, by rfl⟩ : syracuseStep 131071 = 196607) B196607
theorem B174761 : Blo 115785 174761 := bstep (se 2 (by rfl) ⟨65535, by rfl⟩ : syracuseStep 174761 = 131071) B131071
theorem B116507 : Blo 115785 116507 := bstep (se 1 (by rfl) ⟨87380, by rfl⟩ : syracuseStep 116507 = 174761) B174761

theorem C0 (j : ℕ) (h1 : 28946 ≤ j) (h2 : j ≤ 29645) : Blo 115785 (4 * j + 3) := by
  interval_cases j
  · exact B115787
  · exact B115791
  · exact B115795
  · exact B115799
  · exact B115803
  · exact B115807
  · exact B115811
  · exact B115815
  · exact B115819
  · exact B115823
  · exact B115827
  · exact B115831
  · exact B115835
  · exact B115839
  · exact B115843
  · exact B115847
  · exact B115851
  · exact B115855
  · exact B115859
  · exact B115863
  · exact B115867
  · exact B115871
  · exact B115875
  · exact B115879
  · exact B115883
  · exact B115887
  · exact B115891
  · exact B115895
  · exact B115899
  · exact B115903
  · exact B115907
  · exact B115911
  · exact B115915
  · exact B115919
  · exact B115923
  · exact B115927
  · exact B115931
  · exact B115935
  · exact B115939
  · exact B115943
  · exact B115947
  · exact B115951
  · exact B115955
  · exact B115959
  · exact B115963
  · exact B115967
  · exact B115971
  · exact B115975
  · exact B115979
  · exact B115983
  · exact B115987
  · exact B115991
  · exact B115995
  · exact B115999
  · exact B116003
  · exact B116007
  · exact B116011
  · exact B116015
  · exact B116019
  · exact B116023
  · exact B116027
  · exact B116031
  · exact B116035
  · exact B116039
  · exact B116043
  · exact B116047
  · exact B116051
  · exact B116055
  · exact B116059
  · exact B116063
  · exact B116067
  · exact B116071
  · exact B116075
  · exact B116079
  · exact B116083
  · exact B116087
  · exact B116091
  · exact B116095
  · exact B116099
  · exact B116103
  · exact B116107
  · exact B116111
  · exact B116115
  · exact B116119
  · exact B116123
  · exact B116127
  · exact B116131
  · exact B116135
  · exact B116139
  · exact B116143
  · exact B116147
  · exact B116151
  · exact B116155
  · exact B116159
  · exact B116163
  · exact B116167
  · exact B116171
  · exact B116175
  · exact B116179
  · exact B116183
  · exact B116187
  · exact B116191
  · exact B116195
  · exact B116199
  · exact B116203
  · exact B116207
  · exact B116211
  · exact B116215
  · exact B116219
  · exact B116223
  · exact B116227
  · exact B116231
  · exact B116235
  · exact B116239
  · exact B116243
  · exact B116247
  · exact B116251
  · exact B116255
  · exact B116259
  · exact B116263
  · exact B116267
  · exact B116271
  · exact B116275
  · exact B116279
  · exact B116283
  · exact B116287
  · exact B116291
  · exact B116295
  · exact B116299
  · exact B116303
  · exact B116307
  · exact B116311
  · exact B116315
  · exact B116319
  · exact B116323
  · exact B116327
  · exact B116331
  · exact B116335
  · exact B116339
  · exact B116343
  · exact B116347
  · exact B116351
  · exact B116355
  · exact B116359
  · exact B116363
  · exact B116367
  · exact B116371
  · exact B116375
  · exact B116379
  · exact B116383
  · exact B116387
  · exact B116391
  · exact B116395
  · exact B116399
  · exact B116403
  · exact B116407
  · exact B116411
  · exact B116415
  · exact B116419
  · exact B116423
  · exact B116427
  · exact B116431
  · exact B116435
  · exact B116439
  · exact B116443
  · exact B116447
  · exact B116451
  · exact B116455
  · exact B116459
  · exact B116463
  · exact B116467
  · exact B116471
  · exact B116475
  · exact B116479
  · exact B116483
  · exact B116487
  · exact B116491
  · exact B116495
  · exact B116499
  · exact B116503
  · exact B116507
  · exact B116511
  · exact B116515
  · exact B116519
  · exact B116523
  · exact B116527
  · exact B116531
  · exact B116535
  · exact B116539
  · exact B116543
  · exact B116547
  · exact B116551
  · exact B116555
  · exact B116559
  · exact B116563
  · exact B116567
  · exact B116571
  · exact B116575
  · exact B116579
  · exact B116583
  · exact B116587
  · exact B116591
  · exact B116595
  · exact B116599
  · exact B116603
  · exact B116607
  · exact B116611
  · exact B116615
  · exact B116619
  · exact B116623
  · exact B116627
  · exact B116631
  · exact B116635
  · exact B116639
  · exact B116643
  · exact B116647
  · exact B116651
  · exact B116655
  · exact B116659
  · exact B116663
  · exact B116667
  · exact B116671
  · exact B116675
  · exact B116679
  · exact B116683
  · exact B116687
  · exact B116691
  · exact B116695
  · exact B116699
  · exact B116703
  · exact B116707
  · exact B116711
  · exact B116715
  · exact B116719
  · exact B116723
  · exact B116727
  · exact B116731
  · exact B116735
  · exact B116739
  · exact B116743
  · exact B116747
  · exact B116751
  · exact B116755
  · exact B116759
  · exact B116763
  · exact B116767
  · exact B116771
  · exact B116775
  · exact B116779
  · exact B116783
  · exact B116787
  · exact B116791
  · exact B116795
  · exact B116799
  · exact B116803
  · exact B116807
  · exact B116811
  · exact B116815
  · exact B116819
  · exact B116823
  · exact B116827
  · exact B116831
  · exact B116835
  · exact B116839
  · exact B116843
  · exact B116847
  · exact B116851
  · exact B116855
  · exact B116859
  · exact B116863
  · exact B116867
  · exact B116871
  · exact B116875
  · exact B116879
  · exact B116883
  · exact B116887
  · exact B116891
  · exact B116895
  · exact B116899
  · exact B116903
  · exact B116907
  · exact B116911
  · exact B116915
  · exact B116919
  · exact B116923
  · exact B116927
  · exact B116931
  · exact B116935
  · exact B116939
  · exact B116943
  · exact B116947
  · exact B116951
  · exact B116955
  · exact B116959
  · exact B116963
  · exact B116967
  · exact B116971
  · exact B116975
  · exact B116979
  · exact B116983
  · exact B116987
  · exact B116991
  · exact B116995
  · exact B116999
  · exact B117003
  · exact B117007
  · exact B117011
  · exact B117015
  · exact B117019
  · exact B117023
  · exact B117027
  · exact B117031
  · exact B117035
  · exact B117039
  · exact B117043
  · exact B117047
  · exact B117051
  · exact B117055
  · exact B117059
  · exact B117063
  · exact B117067
  · exact B117071
  · exact B117075
  · exact B117079
  · exact B117083
  · exact B117087
  · exact B117091
  · exact B117095
  · exact B117099
  · exact B117103
  · exact B117107
  · exact B117111
  · exact B117115
  · exact B117119
  · exact B117123
  · exact B117127
  · exact B117131
  · exact B117135
  · exact B117139
  · exact B117143
  · exact B117147
  · exact B117151
  · exact B117155
  · exact B117159
  · exact B117163
  · exact B117167
  · exact B117171
  · exact B117175
  · exact B117179
  · exact B117183
  · exact B117187
  · exact B117191
  · exact B117195
  · exact B117199
  · exact B117203
  · exact B117207
  · exact B117211
  · exact B117215
  · exact B117219
  · exact B117223
  · exact B117227
  · exact B117231
  · exact B117235
  · exact B117239
  · exact B117243
  · exact B117247
  · exact B117251
  · exact B117255
  · exact B117259
  · exact B117263
  · exact B117267
  · exact B117271
  · exact B117275
  · exact B117279
  · exact B117283
  · exact B117287
  · exact B117291
  · exact B117295
  · exact B117299
  · exact B117303
  · exact B117307
  · exact B117311
  · exact B117315
  · exact B117319
  · exact B117323
  · exact B117327
  · exact B117331
  · exact B117335
  · exact B117339
  · exact B117343
  · exact B117347
  · exact B117351
  · exact B117355
  · exact B117359
  · exact B117363
  · exact B117367
  · exact B117371
  · exact B117375
  · exact B117379
  · exact B117383
  · exact B117387
  · exact B117391
  · exact B117395
  · exact B117399
  · exact B117403
  · exact B117407
  · exact B117411
  · exact B117415
  · exact B117419
  · exact B117423
  · exact B117427
  · exact B117431
  · exact B117435
  · exact B117439
  · exact B117443
  · exact B117447
  · exact B117451
  · exact B117455
  · exact B117459
  · exact B117463
  · exact B117467
  · exact B117471
  · exact B117475
  · exact B117479
  · exact B117483
  · exact B117487
  · exact B117491
  · exact B117495
  · exact B117499
  · exact B117503
  · exact B117507
  · exact B117511
  · exact B117515
  · exact B117519
  · exact B117523
  · exact B117527
  · exact B117531
  · exact B117535
  · exact B117539
  · exact B117543
  · exact B117547
  · exact B117551
  · exact B117555
  · exact B117559
  · exact B117563
  · exact B117567
  · exact B117571
  · exact B117575
  · exact B117579
  · exact B117583
  · exact B117587
  · exact B117591
  · exact B117595
  · exact B117599
  · exact B117603
  · exact B117607
  · exact B117611
  · exact B117615
  · exact B117619
  · exact B117623
  · exact B117627
  · exact B117631
  · exact B117635
  · exact B117639
  · exact B117643
  · exact B117647
  · exact B117651
  · exact B117655
  · exact B117659
  · exact B117663
  · exact B117667
  · exact B117671
  · exact B117675
  · exact B117679
  · exact B117683
  · exact B117687
  · exact B117691
  · exact B117695
  · exact B117699
  · exact B117703
  · exact B117707
  · exact B117711
  · exact B117715
  · exact B117719
  · exact B117723
  · exact B117727
  · exact B117731
  · exact B117735
  · exact B117739
  · exact B117743
  · exact B117747
  · exact B117751
  · exact B117755
  · exact B117759
  · exact B117763
  · exact B117767
  · exact B117771
  · exact B117775
  · exact B117779
  · exact B117783
  · exact B117787
  · exact B117791
  · exact B117795
  · exact B117799
  · exact B117803
  · exact B117807
  · exact B117811
  · exact B117815
  · exact B117819
  · exact B117823
  · exact B117827
  · exact B117831
  · exact B117835
  · exact B117839
  · exact B117843
  · exact B117847
  · exact B117851
  · exact B117855
  · exact B117859
  · exact B117863
  · exact B117867
  · exact B117871
  · exact B117875
  · exact B117879
  · exact B117883
  · exact B117887
  · exact B117891
  · exact B117895
  · exact B117899
  · exact B117903
  · exact B117907
  · exact B117911
  · exact B117915
  · exact B117919
  · exact B117923
  · exact B117927
  · exact B117931
  · exact B117935
  · exact B117939
  · exact B117943
  · exact B117947
  · exact B117951
  · exact B117955
  · exact B117959
  · exact B117963
  · exact B117967
  · exact B117971
  · exact B117975
  · exact B117979
  · exact B117983
  · exact B117987
  · exact B117991
  · exact B117995
  · exact B117999
  · exact B118003
  · exact B118007
  · exact B118011
  · exact B118015
  · exact B118019
  · exact B118023
  · exact B118027
  · exact B118031
  · exact B118035
  · exact B118039
  · exact B118043
  · exact B118047
  · exact B118051
  · exact B118055
  · exact B118059
  · exact B118063
  · exact B118067
  · exact B118071
  · exact B118075
  · exact B118079
  · exact B118083
  · exact B118087
  · exact B118091
  · exact B118095
  · exact B118099
  · exact B118103
  · exact B118107
  · exact B118111
  · exact B118115
  · exact B118119
  · exact B118123
  · exact B118127
  · exact B118131
  · exact B118135
  · exact B118139
  · exact B118143
  · exact B118147
  · exact B118151
  · exact B118155
  · exact B118159
  · exact B118163
  · exact B118167
  · exact B118171
  · exact B118175
  · exact B118179
  · exact B118183
  · exact B118187
  · exact B118191
  · exact B118195
  · exact B118199
  · exact B118203
  · exact B118207
  · exact B118211
  · exact B118215
  · exact B118219
  · exact B118223
  · exact B118227
  · exact B118231
  · exact B118235
  · exact B118239
  · exact B118243
  · exact B118247
  · exact B118251
  · exact B118255
  · exact B118259
  · exact B118263
  · exact B118267
  · exact B118271
  · exact B118275
  · exact B118279
  · exact B118283
  · exact B118287
  · exact B118291
  · exact B118295
  · exact B118299
  · exact B118303
  · exact B118307
  · exact B118311
  · exact B118315
  · exact B118319
  · exact B118323
  · exact B118327
  · exact B118331
  · exact B118335
  · exact B118339
  · exact B118343
  · exact B118347
  · exact B118351
  · exact B118355
  · exact B118359
  · exact B118363
  · exact B118367
  · exact B118371
  · exact B118375
  · exact B118379
  · exact B118383
  · exact B118387
  · exact B118391
  · exact B118395
  · exact B118399
  · exact B118403
  · exact B118407
  · exact B118411
  · exact B118415
  · exact B118419
  · exact B118423
  · exact B118427
  · exact B118431
  · exact B118435
  · exact B118439
  · exact B118443
  · exact B118447
  · exact B118451
  · exact B118455
  · exact B118459
  · exact B118463
  · exact B118467
  · exact B118471
  · exact B118475
  · exact B118479
  · exact B118483
  · exact B118487
  · exact B118491
  · exact B118495
  · exact B118499
  · exact B118503
  · exact B118507
  · exact B118511
  · exact B118515
  · exact B118519
  · exact B118523
  · exact B118527
  · exact B118531
  · exact B118535
  · exact B118539
  · exact B118543
  · exact B118547
  · exact B118551
  · exact B118555
  · exact B118559
  · exact B118563
  · exact B118567
  · exact B118571
  · exact B118575
  · exact B118579
  · exact B118583

theorem C1 (j : ℕ) (h1 : 29646 ≤ j) (h2 : j ≤ 29945) : Blo 115785 (4 * j + 3) := by
  interval_cases j
  · exact B118587
  · exact B118591
  · exact B118595
  · exact B118599
  · exact B118603
  · exact B118607
  · exact B118611
  · exact B118615
  · exact B118619
  · exact B118623
  · exact B118627
  · exact B118631
  · exact B118635
  · exact B118639
  · exact B118643
  · exact B118647
  · exact B118651
  · exact B118655
  · exact B118659
  · exact B118663
  · exact B118667
  · exact B118671
  · exact B118675
  · exact B118679
  · exact B118683
  · exact B118687
  · exact B118691
  · exact B118695
  · exact B118699
  · exact B118703
  · exact B118707
  · exact B118711
  · exact B118715
  · exact B118719
  · exact B118723
  · exact B118727
  · exact B118731
  · exact B118735
  · exact B118739
  · exact B118743
  · exact B118747
  · exact B118751
  · exact B118755
  · exact B118759
  · exact B118763
  · exact B118767
  · exact B118771
  · exact B118775
  · exact B118779
  · exact B118783
  · exact B118787
  · exact B118791
  · exact B118795
  · exact B118799
  · exact B118803
  · exact B118807
  · exact B118811
  · exact B118815
  · exact B118819
  · exact B118823
  · exact B118827
  · exact B118831
  · exact B118835
  · exact B118839
  · exact B118843
  · exact B118847
  · exact B118851
  · exact B118855
  · exact B118859
  · exact B118863
  · exact B118867
  · exact B118871
  · exact B118875
  · exact B118879
  · exact B118883
  · exact B118887
  · exact B118891
  · exact B118895
  · exact B118899
  · exact B118903
  · exact B118907
  · exact B118911
  · exact B118915
  · exact B118919
  · exact B118923
  · exact B118927
  · exact B118931
  · exact B118935
  · exact B118939
  · exact B118943
  · exact B118947
  · exact B118951
  · exact B118955
  · exact B118959
  · exact B118963
  · exact B118967
  · exact B118971
  · exact B118975
  · exact B118979
  · exact B118983
  · exact B118987
  · exact B118991
  · exact B118995
  · exact B118999
  · exact B119003
  · exact B119007
  · exact B119011
  · exact B119015
  · exact B119019
  · exact B119023
  · exact B119027
  · exact B119031
  · exact B119035
  · exact B119039
  · exact B119043
  · exact B119047
  · exact B119051
  · exact B119055
  · exact B119059
  · exact B119063
  · exact B119067
  · exact B119071
  · exact B119075
  · exact B119079
  · exact B119083
  · exact B119087
  · exact B119091
  · exact B119095
  · exact B119099
  · exact B119103
  · exact B119107
  · exact B119111
  · exact B119115
  · exact B119119
  · exact B119123
  · exact B119127
  · exact B119131
  · exact B119135
  · exact B119139
  · exact B119143
  · exact B119147
  · exact B119151
  · exact B119155
  · exact B119159
  · exact B119163
  · exact B119167
  · exact B119171
  · exact B119175
  · exact B119179
  · exact B119183
  · exact B119187
  · exact B119191
  · exact B119195
  · exact B119199
  · exact B119203
  · exact B119207
  · exact B119211
  · exact B119215
  · exact B119219
  · exact B119223
  · exact B119227
  · exact B119231
  · exact B119235
  · exact B119239
  · exact B119243
  · exact B119247
  · exact B119251
  · exact B119255
  · exact B119259
  · exact B119263
  · exact B119267
  · exact B119271
  · exact B119275
  · exact B119279
  · exact B119283
  · exact B119287
  · exact B119291
  · exact B119295
  · exact B119299
  · exact B119303
  · exact B119307
  · exact B119311
  · exact B119315
  · exact B119319
  · exact B119323
  · exact B119327
  · exact B119331
  · exact B119335
  · exact B119339
  · exact B119343
  · exact B119347
  · exact B119351
  · exact B119355
  · exact B119359
  · exact B119363
  · exact B119367
  · exact B119371
  · exact B119375
  · exact B119379
  · exact B119383
  · exact B119387
  · exact B119391
  · exact B119395
  · exact B119399
  · exact B119403
  · exact B119407
  · exact B119411
  · exact B119415
  · exact B119419
  · exact B119423
  · exact B119427
  · exact B119431
  · exact B119435
  · exact B119439
  · exact B119443
  · exact B119447
  · exact B119451
  · exact B119455
  · exact B119459
  · exact B119463
  · exact B119467
  · exact B119471
  · exact B119475
  · exact B119479
  · exact B119483
  · exact B119487
  · exact B119491
  · exact B119495
  · exact B119499
  · exact B119503
  · exact B119507
  · exact B119511
  · exact B119515
  · exact B119519
  · exact B119523
  · exact B119527
  · exact B119531
  · exact B119535
  · exact B119539
  · exact B119543
  · exact B119547
  · exact B119551
  · exact B119555
  · exact B119559
  · exact B119563
  · exact B119567
  · exact B119571
  · exact B119575
  · exact B119579
  · exact B119583
  · exact B119587
  · exact B119591
  · exact B119595
  · exact B119599
  · exact B119603
  · exact B119607
  · exact B119611
  · exact B119615
  · exact B119619
  · exact B119623
  · exact B119627
  · exact B119631
  · exact B119635
  · exact B119639
  · exact B119643
  · exact B119647
  · exact B119651
  · exact B119655
  · exact B119659
  · exact B119663
  · exact B119667
  · exact B119671
  · exact B119675
  · exact B119679
  · exact B119683
  · exact B119687
  · exact B119691
  · exact B119695
  · exact B119699
  · exact B119703
  · exact B119707
  · exact B119711
  · exact B119715
  · exact B119719
  · exact B119723
  · exact B119727
  · exact B119731
  · exact B119735
  · exact B119739
  · exact B119743
  · exact B119747
  · exact B119751
  · exact B119755
  · exact B119759
  · exact B119763
  · exact B119767
  · exact B119771
  · exact B119775
  · exact B119779
  · exact B119783

theorem solution (m : ℕ) (hlo : 115785 ≤ m) (hhi : m ≤ 119785) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 28946 ≤ j := by omega
    have hj2 : j ≤ 29945 := by omega
    have hb : Blo 115785 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 29646 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
