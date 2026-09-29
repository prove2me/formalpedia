-- Prove2me | solution 1 for syracuse_descends_range_542804_546804
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:33.336746+00:00
-- url     : https://prove2.me/submissions/7c0bb94e-8c61-44e7-8e53-22bd25a8f610

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


theorem B1376261 : Blo 542804 1376261 := bbase (se 4 (by rfl) ⟨129024, by rfl⟩ : syracuseStep 1376261 = 258049) (by norm_num)
theorem B819221 : Blo 542804 819221 := bbase (se 6 (by rfl) ⟨19200, by rfl⟩ : syracuseStep 819221 = 38401) (by norm_num)
theorem B589853 : Blo 542804 589853 := bbase (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) (by norm_num)
theorem B819245 : Blo 542804 819245 := bbase (se 3 (by rfl) ⟨153608, by rfl⟩ : syracuseStep 819245 = 307217) (by norm_num)
theorem B2064437 : Blo 542804 2064437 := bbase (se 5 (by rfl) ⟨96770, by rfl⟩ : syracuseStep 2064437 = 193541) (by norm_num)
theorem B819269 : Blo 542804 819269 := bbase (se 4 (by rfl) ⟨76806, by rfl⟩ : syracuseStep 819269 = 153613) (by norm_num)
theorem B917581 : Blo 542804 917581 := bbase (se 3 (by rfl) ⟨172046, by rfl⟩ : syracuseStep 917581 = 344093) (by norm_num)
theorem B983125 : Blo 542804 983125 := bbase (se 8 (by rfl) ⟨5760, by rfl⟩ : syracuseStep 983125 = 11521) (by norm_num)
theorem B819293 : Blo 542804 819293 := bbase (se 3 (by rfl) ⟨153617, by rfl⟩ : syracuseStep 819293 = 307235) (by norm_num)
theorem B819317 : Blo 542804 819317 := bbase (se 5 (by rfl) ⟨38405, by rfl⟩ : syracuseStep 819317 = 76811) (by norm_num)
theorem B819341 : Blo 542804 819341 := bbase (se 3 (by rfl) ⟨153626, by rfl⟩ : syracuseStep 819341 = 307253) (by norm_num)
theorem B688277 : Blo 542804 688277 := bbase (se 6 (by rfl) ⟨16131, by rfl⟩ : syracuseStep 688277 = 32263) (by norm_num)
theorem B917669 : Blo 542804 917669 := bbase (se 4 (by rfl) ⟨86031, by rfl⟩ : syracuseStep 917669 = 172063) (by norm_num)
theorem B819365 : Blo 542804 819365 := bbase (se 4 (by rfl) ⟨76815, by rfl⟩ : syracuseStep 819365 = 153631) (by norm_num)
theorem B1835189 : Blo 542804 1835189 := bbase (se 5 (by rfl) ⟨86024, by rfl⟩ : syracuseStep 1835189 = 172049) (by norm_num)
theorem B819389 : Blo 542804 819389 := bbase (se 3 (by rfl) ⟨153635, by rfl⟩ : syracuseStep 819389 = 307271) (by norm_num)
theorem B1376453 : Blo 542804 1376453 := bbase (se 4 (by rfl) ⟨129042, by rfl⟩ : syracuseStep 1376453 = 258085) (by norm_num)
theorem B688333 : Blo 542804 688333 := bbase (se 3 (by rfl) ⟨129062, by rfl⟩ : syracuseStep 688333 = 258125) (by norm_num)
theorem B819413 : Blo 542804 819413 := bbase (se 7 (by rfl) ⟨9602, by rfl⟩ : syracuseStep 819413 = 19205) (by norm_num)
theorem B819437 : Blo 542804 819437 := bbase (se 3 (by rfl) ⟨153644, by rfl⟩ : syracuseStep 819437 = 307289) (by norm_num)
theorem B819461 : Blo 542804 819461 := bbase (se 4 (by rfl) ⟨76824, by rfl⟩ : syracuseStep 819461 = 153649) (by norm_num)
theorem B819485 : Blo 542804 819485 := bbase (se 3 (by rfl) ⟨153653, by rfl⟩ : syracuseStep 819485 = 307307) (by norm_num)
theorem B917797 : Blo 542804 917797 := bbase (se 4 (by rfl) ⟨86043, by rfl⟩ : syracuseStep 917797 = 172087) (by norm_num)
theorem B688429 : Blo 542804 688429 := bbase (se 3 (by rfl) ⟨129080, by rfl⟩ : syracuseStep 688429 = 258161) (by norm_num)
theorem B819509 : Blo 542804 819509 := bbase (se 5 (by rfl) ⟨38414, by rfl⟩ : syracuseStep 819509 = 76829) (by norm_num)
theorem B819533 : Blo 542804 819533 := bbase (se 3 (by rfl) ⟨153662, by rfl⟩ : syracuseStep 819533 = 307325) (by norm_num)
theorem B819557 : Blo 542804 819557 := bbase (se 4 (by rfl) ⟨76833, by rfl⟩ : syracuseStep 819557 = 153667) (by norm_num)
theorem B917885 : Blo 542804 917885 := bbase (se 3 (by rfl) ⟨172103, by rfl⟩ : syracuseStep 917885 = 344207) (by norm_num)
theorem B819581 : Blo 542804 819581 := bbase (se 3 (by rfl) ⟨153671, by rfl⟩ : syracuseStep 819581 = 307343) (by norm_num)
theorem B819605 : Blo 542804 819605 := bbase (se 6 (by rfl) ⟨19209, by rfl⟩ : syracuseStep 819605 = 38419) (by norm_num)
theorem B819629 : Blo 542804 819629 := bbase (se 3 (by rfl) ⟨153680, by rfl⟩ : syracuseStep 819629 = 307361) (by norm_num)
theorem B819653 : Blo 542804 819653 := bbase (se 4 (by rfl) ⟨76842, by rfl⟩ : syracuseStep 819653 = 153685) (by norm_num)
theorem B655825 : Blo 542804 655825 := bbase (se 2 (by rfl) ⟨245934, by rfl⟩ : syracuseStep 655825 = 491869) (by norm_num)
theorem B688601 : Blo 542804 688601 := bbase (se 2 (by rfl) ⟨258225, by rfl⟩ : syracuseStep 688601 = 516451) (by norm_num)
theorem B819677 : Blo 542804 819677 := bbase (se 3 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 819677 = 307379) (by norm_num)
theorem B819701 : Blo 542804 819701 := bbase (se 5 (by rfl) ⟨38423, by rfl⟩ : syracuseStep 819701 = 76847) (by norm_num)
theorem B918013 : Blo 542804 918013 := bbase (se 3 (by rfl) ⟨172127, by rfl⟩ : syracuseStep 918013 = 344255) (by norm_num)
theorem B819725 : Blo 542804 819725 := bbase (se 3 (by rfl) ⟨153698, by rfl⟩ : syracuseStep 819725 = 307397) (by norm_num)
theorem B688657 : Blo 542804 688657 := bbase (se 2 (by rfl) ⟨258246, by rfl⟩ : syracuseStep 688657 = 516493) (by norm_num)
theorem B1376797 : Blo 542804 1376797 := bbase (se 3 (by rfl) ⟨258149, by rfl⟩ : syracuseStep 1376797 = 516299) (by norm_num)
theorem B819749 : Blo 542804 819749 := bbase (se 4 (by rfl) ⟨76851, by rfl⟩ : syracuseStep 819749 = 153703) (by norm_num)
theorem B655921 : Blo 542804 655921 := bbase (se 2 (by rfl) ⟨245970, by rfl⟩ : syracuseStep 655921 = 491941) (by norm_num)
theorem B819773 : Blo 542804 819773 := bbase (se 3 (by rfl) ⟨153707, by rfl⟩ : syracuseStep 819773 = 307415) (by norm_num)
theorem B918101 : Blo 542804 918101 := bbase (se 8 (by rfl) ⟨5379, by rfl⟩ : syracuseStep 918101 = 10759) (by norm_num)
theorem B819797 : Blo 542804 819797 := bbase (se 8 (by rfl) ⟨4803, by rfl⟩ : syracuseStep 819797 = 9607) (by norm_num)
theorem B1835621 : Blo 542804 1835621 := bbase (se 4 (by rfl) ⟨172089, by rfl⟩ : syracuseStep 1835621 = 344179) (by norm_num)
theorem B819821 : Blo 542804 819821 := bbase (se 3 (by rfl) ⟨153716, by rfl⟩ : syracuseStep 819821 = 307433) (by norm_num)
theorem B688753 : Blo 542804 688753 := bbase (se 2 (by rfl) ⟨258282, by rfl⟩ : syracuseStep 688753 = 516565) (by norm_num)
theorem B819845 : Blo 542804 819845 := bbase (se 4 (by rfl) ⟨76860, by rfl⟩ : syracuseStep 819845 = 153721) (by norm_num)
theorem B1376909 : Blo 542804 1376909 := bbase (se 3 (by rfl) ⟨258170, by rfl⟩ : syracuseStep 1376909 = 516341) (by norm_num)
theorem B819869 : Blo 542804 819869 := bbase (se 3 (by rfl) ⟨153725, by rfl⟩ : syracuseStep 819869 = 307451) (by norm_num)
theorem B2753189 : Blo 542804 2753189 := bbase (se 4 (by rfl) ⟨258111, by rfl⟩ : syracuseStep 2753189 = 516223) (by norm_num)
theorem B819893 : Blo 542804 819893 := bbase (se 5 (by rfl) ⟨38432, by rfl⟩ : syracuseStep 819893 = 76865) (by norm_num)
theorem B819917 : Blo 542804 819917 := bbase (se 3 (by rfl) ⟨153734, by rfl⟩ : syracuseStep 819917 = 307469) (by norm_num)
theorem B918229 : Blo 542804 918229 := bbase (se 7 (by rfl) ⟨10760, by rfl⟩ : syracuseStep 918229 = 21521) (by norm_num)
theorem B819941 : Blo 542804 819941 := bbase (se 4 (by rfl) ⟨76869, by rfl⟩ : syracuseStep 819941 = 153739) (by norm_num)
theorem B819965 : Blo 542804 819965 := bbase (se 3 (by rfl) ⟨153743, by rfl⟩ : syracuseStep 819965 = 307487) (by norm_num)
theorem B819989 : Blo 542804 819989 := bbase (se 6 (by rfl) ⟨19218, by rfl⟩ : syracuseStep 819989 = 38437) (by norm_num)
theorem B688925 : Blo 542804 688925 := bbase (se 3 (by rfl) ⟨129173, by rfl⟩ : syracuseStep 688925 = 258347) (by norm_num)
theorem B918317 : Blo 542804 918317 := bbase (se 3 (by rfl) ⟨172184, by rfl⟩ : syracuseStep 918317 = 344369) (by norm_num)
theorem B820013 : Blo 542804 820013 := bbase (se 3 (by rfl) ⟨153752, by rfl⟩ : syracuseStep 820013 = 307505) (by norm_num)
theorem B820037 : Blo 542804 820037 := bbase (se 4 (by rfl) ⟨76878, by rfl⟩ : syracuseStep 820037 = 153757) (by norm_num)
theorem B1377101 : Blo 542804 1377101 := bbase (se 3 (by rfl) ⟨258206, by rfl⟩ : syracuseStep 1377101 = 516413) (by norm_num)
theorem B688981 : Blo 542804 688981 := bbase (se 9 (by rfl) ⟨2018, by rfl⟩ : syracuseStep 688981 = 4037) (by norm_num)
theorem B820061 : Blo 542804 820061 := bbase (se 3 (by rfl) ⟨153761, by rfl⟩ : syracuseStep 820061 = 307523) (by norm_num)
theorem B2327413 : Blo 542804 2327413 := bbase (se 5 (by rfl) ⟨109097, by rfl⟩ : syracuseStep 2327413 = 218195) (by norm_num)
theorem B820085 : Blo 542804 820085 := bbase (se 5 (by rfl) ⟨38441, by rfl⟩ : syracuseStep 820085 = 76883) (by norm_num)
theorem B820109 : Blo 542804 820109 := bbase (se 3 (by rfl) ⟨153770, by rfl⟩ : syracuseStep 820109 = 307541) (by norm_num)
theorem B820133 : Blo 542804 820133 := bbase (se 4 (by rfl) ⟨76887, by rfl⟩ : syracuseStep 820133 = 153775) (by norm_num)
theorem B918445 : Blo 542804 918445 := bbase (se 3 (by rfl) ⟨172208, by rfl⟩ : syracuseStep 918445 = 344417) (by norm_num)
theorem B656305 : Blo 542804 656305 := bbase (se 2 (by rfl) ⟨246114, by rfl⟩ : syracuseStep 656305 = 492229) (by norm_num)
theorem B689077 : Blo 542804 689077 := bbase (se 5 (by rfl) ⟨32300, by rfl⟩ : syracuseStep 689077 = 64601) (by norm_num)
theorem B820157 : Blo 542804 820157 := bbase (se 3 (by rfl) ⟨153779, by rfl⟩ : syracuseStep 820157 = 307559) (by norm_num)
theorem B820181 : Blo 542804 820181 := bbase (se 7 (by rfl) ⟨9611, by rfl⟩ : syracuseStep 820181 = 19223) (by norm_num)
theorem B820205 : Blo 542804 820205 := bbase (se 3 (by rfl) ⟨153788, by rfl⟩ : syracuseStep 820205 = 307577) (by norm_num)
theorem B1180669 : Blo 542804 1180669 := bbase (se 3 (by rfl) ⟨221375, by rfl⟩ : syracuseStep 1180669 = 442751) (by norm_num)
theorem B918533 : Blo 542804 918533 := bbase (se 4 (by rfl) ⟨86112, by rfl⟩ : syracuseStep 918533 = 172225) (by norm_num)
theorem B1836053 : Blo 542804 1836053 := bbase (se 6 (by rfl) ⟨43032, by rfl⟩ : syracuseStep 1836053 = 86065) (by norm_num)
theorem B689249 : Blo 542804 689249 := bbase (se 2 (by rfl) ⟨258468, by rfl⟩ : syracuseStep 689249 = 516937) (by norm_num)
theorem B918661 : Blo 542804 918661 := bbase (se 4 (by rfl) ⟨86124, by rfl⟩ : syracuseStep 918661 = 172249) (by norm_num)
theorem B689305 : Blo 542804 689305 := bbase (se 2 (by rfl) ⟨258489, by rfl⟩ : syracuseStep 689305 = 516979) (by norm_num)
theorem B1377445 : Blo 542804 1377445 := bbase (se 4 (by rfl) ⟨129135, by rfl⟩ : syracuseStep 1377445 = 258271) (by norm_num)
theorem B2065621 : Blo 542804 2065621 := bbase (se 7 (by rfl) ⟨24206, by rfl⟩ : syracuseStep 2065621 = 48413) (by norm_num)
theorem B3114197 : Blo 542804 3114197 := bbase (se 7 (by rfl) ⟨36494, by rfl⟩ : syracuseStep 3114197 = 72989) (by norm_num)
theorem B918749 : Blo 542804 918749 := bbase (se 3 (by rfl) ⟨172265, by rfl⟩ : syracuseStep 918749 = 344531) (by norm_num)
theorem B689401 : Blo 542804 689401 := bbase (se 2 (by rfl) ⟨258525, by rfl⟩ : syracuseStep 689401 = 517051) (by norm_num)
theorem B1049861 : Blo 542804 1049861 := bbase (se 4 (by rfl) ⟨98424, by rfl⟩ : syracuseStep 1049861 = 196849) (by norm_num)
theorem B1377557 : Blo 542804 1377557 := bbase (se 6 (by rfl) ⟨32286, by rfl⟩ : syracuseStep 1377557 = 64573) (by norm_num)
theorem B918877 : Blo 542804 918877 := bbase (se 3 (by rfl) ⟨172289, by rfl⟩ : syracuseStep 918877 = 344579) (by norm_num)
theorem B689573 : Blo 542804 689573 := bbase (se 4 (by rfl) ⟨64647, by rfl⟩ : syracuseStep 689573 = 129295) (by norm_num)
theorem B918965 : Blo 542804 918965 := bbase (se 5 (by rfl) ⟨43076, by rfl⟩ : syracuseStep 918965 = 86153) (by norm_num)
theorem B1836485 : Blo 542804 1836485 := bbase (se 4 (by rfl) ⟨172170, by rfl⟩ : syracuseStep 1836485 = 344341) (by norm_num)
theorem B1377749 : Blo 542804 1377749 := bbase (se 7 (by rfl) ⟨16145, by rfl⟩ : syracuseStep 1377749 = 32291) (by norm_num)
theorem B13469141 : Blo 542804 13469141 := bbase (se 7 (by rfl) ⟨157841, by rfl⟩ : syracuseStep 13469141 = 315683) (by norm_num)
theorem B689629 : Blo 542804 689629 := bbase (se 3 (by rfl) ⟨129305, by rfl⟩ : syracuseStep 689629 = 258611) (by norm_num)
theorem B2065925 : Blo 542804 2065925 := bbase (se 4 (by rfl) ⟨193680, by rfl⟩ : syracuseStep 2065925 = 387361) (by norm_num)
theorem B919093 : Blo 542804 919093 := bbase (se 5 (by rfl) ⟨43082, by rfl⟩ : syracuseStep 919093 = 86165) (by norm_num)
theorem B689725 : Blo 542804 689725 := bbase (se 3 (by rfl) ⟨129323, by rfl⟩ : syracuseStep 689725 = 258647) (by norm_num)
theorem B591481 : Blo 542804 591481 := bbase (se 2 (by rfl) ⟨221805, by rfl⟩ : syracuseStep 591481 = 443611) (by norm_num)
theorem B919181 : Blo 542804 919181 := bbase (se 3 (by rfl) ⟨172346, by rfl⟩ : syracuseStep 919181 = 344693) (by norm_num)
theorem B2623205 : Blo 542804 2623205 := bbase (se 4 (by rfl) ⟨245925, by rfl⟩ : syracuseStep 2623205 = 491851) (by norm_num)
theorem B689897 : Blo 542804 689897 := bbase (se 2 (by rfl) ⟨258711, by rfl⟩ : syracuseStep 689897 = 517423) (by norm_num)
theorem B919309 : Blo 542804 919309 := bbase (se 3 (by rfl) ⟨172370, by rfl⟩ : syracuseStep 919309 = 344741) (by norm_num)
theorem B558881 : Blo 542804 558881 := bbase (se 2 (by rfl) ⟨209580, by rfl⟩ : syracuseStep 558881 = 419161) (by norm_num)
theorem B689953 : Blo 542804 689953 := bbase (se 2 (by rfl) ⟨258732, by rfl⟩ : syracuseStep 689953 = 517465) (by norm_num)
theorem B1378093 : Blo 542804 1378093 := bbase (se 3 (by rfl) ⟨258392, by rfl⟩ : syracuseStep 1378093 = 516785) (by norm_num)
theorem B919397 : Blo 542804 919397 := bbase (se 4 (by rfl) ⟨86193, by rfl⟩ : syracuseStep 919397 = 172387) (by norm_num)
theorem B1836917 : Blo 542804 1836917 := bbase (se 5 (by rfl) ⟨86105, by rfl⟩ : syracuseStep 1836917 = 172211) (by norm_num)
theorem B690049 : Blo 542804 690049 := bbase (se 2 (by rfl) ⟨258768, by rfl⟩ : syracuseStep 690049 = 517537) (by norm_num)
theorem B1378205 : Blo 542804 1378205 := bbase (se 3 (by rfl) ⟨258413, by rfl⟩ : syracuseStep 1378205 = 516827) (by norm_num)
theorem B2754485 : Blo 542804 2754485 := bbase (se 5 (by rfl) ⟨129116, by rfl⟩ : syracuseStep 2754485 = 258233) (by norm_num)
theorem B4655029 : Blo 542804 4655029 := bbase (se 5 (by rfl) ⟨218204, by rfl⟩ : syracuseStep 4655029 = 436409) (by norm_num)
theorem B919525 : Blo 542804 919525 := bbase (se 4 (by rfl) ⟨86205, by rfl⟩ : syracuseStep 919525 = 172411) (by norm_num)
theorem B690221 : Blo 542804 690221 := bbase (se 3 (by rfl) ⟨129416, by rfl⟩ : syracuseStep 690221 = 258833) (by norm_num)
theorem B919613 : Blo 542804 919613 := bbase (se 3 (by rfl) ⟨172427, by rfl⟩ : syracuseStep 919613 = 344855) (by norm_num)
theorem B1378397 : Blo 542804 1378397 := bbase (se 3 (by rfl) ⟨258449, by rfl⟩ : syracuseStep 1378397 = 516899) (by norm_num)
theorem B1312861 : Blo 542804 1312861 := bbase (se 3 (by rfl) ⟨246161, by rfl⟩ : syracuseStep 1312861 = 492323) (by norm_num)
theorem B690277 : Blo 542804 690277 := bbase (se 4 (by rfl) ⟨64713, by rfl⟩ : syracuseStep 690277 = 129427) (by norm_num)
theorem B919741 : Blo 542804 919741 := bbase (se 3 (by rfl) ⟨172451, by rfl⟩ : syracuseStep 919741 = 344903) (by norm_num)
theorem B690373 : Blo 542804 690373 := bbase (se 4 (by rfl) ⟨64722, by rfl⟩ : syracuseStep 690373 = 129445) (by norm_num)
theorem B919829 : Blo 542804 919829 := bbase (se 6 (by rfl) ⟨21558, by rfl⟩ : syracuseStep 919829 = 43117) (by norm_num)
theorem B1837349 : Blo 542804 1837349 := bbase (se 4 (by rfl) ⟨172251, by rfl⟩ : syracuseStep 1837349 = 344503) (by norm_num)
theorem B690545 : Blo 542804 690545 := bbase (se 2 (by rfl) ⟨258954, by rfl⟩ : syracuseStep 690545 = 517909) (by norm_num)
theorem B2623877 : Blo 542804 2623877 := bbase (se 4 (by rfl) ⟨245988, by rfl⟩ : syracuseStep 2623877 = 491977) (by norm_num)
theorem B919957 : Blo 542804 919957 := bbase (se 6 (by rfl) ⟨21561, by rfl⟩ : syracuseStep 919957 = 43123) (by norm_num)
theorem B690601 : Blo 542804 690601 := bbase (se 2 (by rfl) ⟨258975, by rfl⟩ : syracuseStep 690601 = 517951) (by norm_num)
theorem B1378741 : Blo 542804 1378741 := bbase (se 5 (by rfl) ⟨64628, by rfl⟩ : syracuseStep 1378741 = 129257) (by norm_num)
theorem B920045 : Blo 542804 920045 := bbase (se 3 (by rfl) ⟨172508, by rfl⟩ : syracuseStep 920045 = 345017) (by norm_num)
theorem B690697 : Blo 542804 690697 := bbase (se 2 (by rfl) ⟨259011, by rfl⟩ : syracuseStep 690697 = 518023) (by norm_num)
theorem B1378853 : Blo 542804 1378853 := bbase (se 4 (by rfl) ⟨129267, by rfl⟩ : syracuseStep 1378853 = 258535) (by norm_num)
theorem B1739333 : Blo 542804 1739333 := bbase (se 4 (by rfl) ⟨163062, by rfl⟩ : syracuseStep 1739333 = 326125) (by norm_num)
theorem B920173 : Blo 542804 920173 := bbase (se 3 (by rfl) ⟨172532, by rfl⟩ : syracuseStep 920173 = 345065) (by norm_num)
theorem B690869 : Blo 542804 690869 := bbase (se 5 (by rfl) ⟨32384, by rfl⟩ : syracuseStep 690869 = 64769) (by norm_num)
theorem B920261 : Blo 542804 920261 := bbase (se 4 (by rfl) ⟨86274, by rfl⟩ : syracuseStep 920261 = 172549) (by norm_num)
theorem B1837781 : Blo 542804 1837781 := bbase (se 7 (by rfl) ⟨21536, by rfl⟩ : syracuseStep 1837781 = 43073) (by norm_num)
theorem B1379045 : Blo 542804 1379045 := bbase (se 4 (by rfl) ⟨129285, by rfl⟩ : syracuseStep 1379045 = 258571) (by norm_num)
theorem B690925 : Blo 542804 690925 := bbase (se 3 (by rfl) ⟨129548, by rfl⟩ : syracuseStep 690925 = 259097) (by norm_num)
theorem B1313533 : Blo 542804 1313533 := bbase (se 3 (by rfl) ⟨246287, by rfl⟩ : syracuseStep 1313533 = 492575) (by norm_num)
theorem B559909 : Blo 542804 559909 := bbase (se 4 (by rfl) ⟨52491, by rfl⟩ : syracuseStep 559909 = 104983) (by norm_num)
theorem B920389 : Blo 542804 920389 := bbase (se 4 (by rfl) ⟨86286, by rfl⟩ : syracuseStep 920389 = 172573) (by norm_num)
theorem B691021 : Blo 542804 691021 := bbase (se 3 (by rfl) ⟨129566, by rfl⟩ : syracuseStep 691021 = 259133) (by norm_num)
theorem B920477 : Blo 542804 920477 := bbase (se 3 (by rfl) ⟨172589, by rfl⟩ : syracuseStep 920477 = 345179) (by norm_num)
theorem B1313765 : Blo 542804 1313765 := bbase (se 4 (by rfl) ⟨123165, by rfl⟩ : syracuseStep 1313765 = 246331) (by norm_num)
theorem B691193 : Blo 542804 691193 := bbase (se 2 (by rfl) ⟨259197, by rfl⟩ : syracuseStep 691193 = 518395) (by norm_num)
theorem B920605 : Blo 542804 920605 := bbase (se 3 (by rfl) ⟨172613, by rfl⟩ : syracuseStep 920605 = 345227) (by norm_num)
theorem B691249 : Blo 542804 691249 := bbase (se 2 (by rfl) ⟨259218, by rfl⟩ : syracuseStep 691249 = 518437) (by norm_num)
theorem B1379389 : Blo 542804 1379389 := bbase (se 3 (by rfl) ⟨258635, by rfl⟩ : syracuseStep 1379389 = 517271) (by norm_num)
theorem B920693 : Blo 542804 920693 := bbase (se 5 (by rfl) ⟨43157, by rfl⟩ : syracuseStep 920693 = 86315) (by norm_num)
theorem B1838213 : Blo 542804 1838213 := bbase (se 4 (by rfl) ⟨172332, by rfl⟩ : syracuseStep 1838213 = 344665) (by norm_num)
theorem B691345 : Blo 542804 691345 := bbase (se 2 (by rfl) ⟨259254, by rfl⟩ : syracuseStep 691345 = 518509) (by norm_num)
theorem B1379501 : Blo 542804 1379501 := bbase (se 3 (by rfl) ⟨258656, by rfl⟩ : syracuseStep 1379501 = 517313) (by norm_num)
theorem B2755781 : Blo 542804 2755781 := bbase (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) (by norm_num)
theorem B920821 : Blo 542804 920821 := bbase (se 5 (by rfl) ⟨43163, by rfl⟩ : syracuseStep 920821 = 86327) (by norm_num)
theorem B691517 : Blo 542804 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B920909 : Blo 542804 920909 := bbase (se 3 (by rfl) ⟨172670, by rfl⟩ : syracuseStep 920909 = 345341) (by norm_num)
theorem B1379693 : Blo 542804 1379693 := bbase (se 3 (by rfl) ⟨258692, by rfl⟩ : syracuseStep 1379693 = 517385) (by norm_num)
theorem B691573 : Blo 542804 691573 := bbase (se 5 (by rfl) ⟨32417, by rfl⟩ : syracuseStep 691573 = 64835) (by norm_num)
theorem B921037 : Blo 542804 921037 := bbase (se 3 (by rfl) ⟨172694, by rfl⟩ : syracuseStep 921037 = 345389) (by norm_num)
theorem B691669 : Blo 542804 691669 := bbase (se 7 (by rfl) ⟨8105, by rfl⟩ : syracuseStep 691669 = 16211) (by norm_num)
theorem B921125 : Blo 542804 921125 := bbase (se 4 (by rfl) ⟨86355, by rfl⟩ : syracuseStep 921125 = 172711) (by norm_num)
theorem B1838645 : Blo 542804 1838645 := bbase (se 5 (by rfl) ⟨86186, by rfl⟩ : syracuseStep 1838645 = 172373) (by norm_num)
theorem B2068037 : Blo 542804 2068037 := bbase (se 4 (by rfl) ⟨193878, by rfl⟩ : syracuseStep 2068037 = 387757) (by norm_num)
theorem B691841 : Blo 542804 691841 := bbase (se 2 (by rfl) ⟨259440, by rfl⟩ : syracuseStep 691841 = 518881) (by norm_num)
theorem B921253 : Blo 542804 921253 := bbase (se 4 (by rfl) ⟨86367, by rfl⟩ : syracuseStep 921253 = 172735) (by norm_num)
theorem B691897 : Blo 542804 691897 := bbase (se 2 (by rfl) ⟨259461, by rfl⟩ : syracuseStep 691897 = 518923) (by norm_num)
theorem B1380037 : Blo 542804 1380037 := bbase (se 4 (by rfl) ⟨129378, by rfl⟩ : syracuseStep 1380037 = 258757) (by norm_num)
theorem B921341 : Blo 542804 921341 := bbase (se 3 (by rfl) ⟨172751, by rfl⟩ : syracuseStep 921341 = 345503) (by norm_num)
theorem B691993 : Blo 542804 691993 := bbase (se 2 (by rfl) ⟨259497, by rfl⟩ : syracuseStep 691993 = 518995) (by norm_num)
theorem B1380149 : Blo 542804 1380149 := bbase (se 5 (by rfl) ⟨64694, by rfl⟩ : syracuseStep 1380149 = 129389) (by norm_num)
theorem B2068325 : Blo 542804 2068325 := bbase (se 4 (by rfl) ⟨193905, by rfl⟩ : syracuseStep 2068325 = 387811) (by norm_num)
theorem B4657013 : Blo 542804 4657013 := bbase (se 5 (by rfl) ⟨218297, by rfl⟩ : syracuseStep 4657013 = 436595) (by norm_num)
theorem B921469 : Blo 542804 921469 := bbase (se 3 (by rfl) ⟨172775, by rfl⟩ : syracuseStep 921469 = 345551) (by norm_num)
theorem B921557 : Blo 542804 921557 := bbase (se 7 (by rfl) ⟨10799, by rfl⟩ : syracuseStep 921557 = 21599) (by norm_num)
theorem B1839077 : Blo 542804 1839077 := bbase (se 4 (by rfl) ⟨172413, by rfl⟩ : syracuseStep 1839077 = 344827) (by norm_num)
theorem B1380341 : Blo 542804 1380341 := bbase (se 5 (by rfl) ⟨64703, by rfl⟩ : syracuseStep 1380341 = 129407) (by norm_num)
theorem B5050421 : Blo 542804 5050421 := bbase (se 5 (by rfl) ⟨236738, by rfl⟩ : syracuseStep 5050421 = 473477) (by norm_num)
theorem B921685 : Blo 542804 921685 := bbase (se 8 (by rfl) ⟨5400, by rfl⟩ : syracuseStep 921685 = 10801) (by norm_num)
theorem B4198517 : Blo 542804 4198517 := bbase (se 5 (by rfl) ⟨196805, by rfl⟩ : syracuseStep 4198517 = 393611) (by norm_num)
theorem B921773 : Blo 542804 921773 := bbase (se 3 (by rfl) ⟨172832, by rfl⟩ : syracuseStep 921773 = 345665) (by norm_num)
theorem B921901 : Blo 542804 921901 := bbase (se 3 (by rfl) ⟨172856, by rfl⟩ : syracuseStep 921901 = 345713) (by norm_num)
theorem B1380685 : Blo 542804 1380685 := bbase (se 3 (by rfl) ⟨258878, by rfl⟩ : syracuseStep 1380685 = 517757) (by norm_num)
theorem B921989 : Blo 542804 921989 := bbase (se 4 (by rfl) ⟨86436, by rfl⟩ : syracuseStep 921989 = 172873) (by norm_num)
theorem B1839509 : Blo 542804 1839509 := bbase (se 6 (by rfl) ⟨43113, by rfl⟩ : syracuseStep 1839509 = 86227) (by norm_num)
theorem B1380797 : Blo 542804 1380797 := bbase (se 3 (by rfl) ⟨258899, by rfl⟩ : syracuseStep 1380797 = 517799) (by norm_num)
theorem B2757077 : Blo 542804 2757077 := bbase (se 7 (by rfl) ⟨32309, by rfl⟩ : syracuseStep 2757077 = 64619) (by norm_num)
theorem B922117 : Blo 542804 922117 := bbase (se 4 (by rfl) ⟨86448, by rfl⟩ : syracuseStep 922117 = 172897) (by norm_num)
theorem B4133429 : Blo 542804 4133429 := bbase (se 5 (by rfl) ⟨193754, by rfl⟩ : syracuseStep 4133429 = 387509) (by norm_num)
theorem B922205 : Blo 542804 922205 := bbase (se 3 (by rfl) ⟨172913, by rfl⟩ : syracuseStep 922205 = 345827) (by norm_num)
theorem B1380989 : Blo 542804 1380989 := bbase (se 3 (by rfl) ⟨258935, by rfl⟩ : syracuseStep 1380989 = 517871) (by norm_num)
theorem B922333 : Blo 542804 922333 := bbase (se 3 (by rfl) ⟨172937, by rfl⟩ : syracuseStep 922333 = 345875) (by norm_num)
theorem B922421 : Blo 542804 922421 := bbase (se 5 (by rfl) ⟨43238, by rfl⟩ : syracuseStep 922421 = 86477) (by norm_num)
theorem B1839941 : Blo 542804 1839941 := bbase (se 4 (by rfl) ⟨172494, by rfl⟩ : syracuseStep 1839941 = 344989) (by norm_num)
theorem B922549 : Blo 542804 922549 := bbase (se 5 (by rfl) ⟨43244, by rfl⟩ : syracuseStep 922549 = 86489) (by norm_num)
theorem B1381333 : Blo 542804 1381333 := bbase (se 7 (by rfl) ⟨16187, by rfl⟩ : syracuseStep 1381333 = 32375) (by norm_num)
theorem B2069509 : Blo 542804 2069509 := bbase (se 4 (by rfl) ⟨194016, by rfl⟩ : syracuseStep 2069509 = 388033) (by norm_num)
theorem B922637 : Blo 542804 922637 := bbase (se 3 (by rfl) ⟨172994, by rfl⟩ : syracuseStep 922637 = 345989) (by norm_num)
theorem B1381445 : Blo 542804 1381445 := bbase (se 4 (by rfl) ⟨129510, by rfl⟩ : syracuseStep 1381445 = 259021) (by norm_num)
theorem B8983637 : Blo 542804 8983637 := bbase (se 8 (by rfl) ⟨52638, by rfl⟩ : syracuseStep 8983637 = 105277) (by norm_num)
theorem B1840373 : Blo 542804 1840373 := bbase (se 5 (by rfl) ⟨86267, by rfl⟩ : syracuseStep 1840373 = 172535) (by norm_num)
theorem B1381637 : Blo 542804 1381637 := bbase (se 4 (by rfl) ⟨129528, by rfl⟩ : syracuseStep 1381637 = 259057) (by norm_num)
theorem B2069813 : Blo 542804 2069813 := bbase (se 5 (by rfl) ⟨97022, by rfl⟩ : syracuseStep 2069813 = 194045) (by norm_num)
theorem B1381981 : Blo 542804 1381981 := bbase (se 3 (by rfl) ⟨259121, by rfl⟩ : syracuseStep 1381981 = 518243) (by norm_num)
theorem B1742485 : Blo 542804 1742485 := bbase (se 6 (by rfl) ⟨40839, by rfl⟩ : syracuseStep 1742485 = 81679) (by norm_num)
theorem B1840805 : Blo 542804 1840805 := bbase (se 4 (by rfl) ⟨172575, by rfl⟩ : syracuseStep 1840805 = 345151) (by norm_num)
theorem B1545925 : Blo 542804 1545925 := bbase (se 4 (by rfl) ⟨144930, by rfl⟩ : syracuseStep 1545925 = 289861) (by norm_num)
theorem B1382093 : Blo 542804 1382093 := bbase (se 3 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 1382093 = 518285) (by norm_num)
theorem B2758373 : Blo 542804 2758373 := bbase (se 4 (by rfl) ⟨258597, by rfl⟩ : syracuseStep 2758373 = 517195) (by norm_num)
theorem B2332421 : Blo 542804 2332421 := bbase (se 4 (by rfl) ⟨218664, by rfl⟩ : syracuseStep 2332421 = 437329) (by norm_num)
theorem B3479381 : Blo 542804 3479381 := bbase (se 9 (by rfl) ⟨10193, by rfl⟩ : syracuseStep 3479381 = 20387) (by norm_num)
theorem B1382285 : Blo 542804 1382285 := bbase (se 3 (by rfl) ⟨259178, by rfl⟩ : syracuseStep 1382285 = 518357) (by norm_num)
theorem B2201525 : Blo 542804 2201525 := bbase (se 5 (by rfl) ⟨103196, by rfl⟩ : syracuseStep 2201525 = 206393) (by norm_num)
theorem B2332709 : Blo 542804 2332709 := bbase (se 4 (by rfl) ⟨218691, by rfl⟩ : syracuseStep 2332709 = 437383) (by norm_num)
theorem B1841237 : Blo 542804 1841237 := bbase (se 8 (by rfl) ⟨10788, by rfl⟩ : syracuseStep 1841237 = 21577) (by norm_num)
theorem B1382629 : Blo 542804 1382629 := bbase (se 4 (by rfl) ⟨129621, by rfl⟩ : syracuseStep 1382629 = 259243) (by norm_num)
theorem B1382741 : Blo 542804 1382741 := bbase (se 10 (by rfl) ⟨2025, by rfl⟩ : syracuseStep 1382741 = 4051) (by norm_num)
theorem B1841669 : Blo 542804 1841669 := bbase (se 4 (by rfl) ⟨172656, by rfl⟩ : syracuseStep 1841669 = 345313) (by norm_num)
theorem B825869 : Blo 542804 825869 := bbase (se 3 (by rfl) ⟨154850, by rfl⟩ : syracuseStep 825869 = 309701) (by norm_num)
theorem B1382933 : Blo 542804 1382933 := bbase (se 6 (by rfl) ⟨32412, by rfl⟩ : syracuseStep 1382933 = 64825) (by norm_num)
theorem B2955797 : Blo 542804 2955797 := bbase (se 6 (by rfl) ⟨69276, by rfl⟩ : syracuseStep 2955797 = 138553) (by norm_num)
theorem B629305 : Blo 542804 629305 := bbase (se 2 (by rfl) ⟨235989, by rfl⟩ : syracuseStep 629305 = 471979) (by norm_num)
theorem B5216885 : Blo 542804 5216885 := bbase (se 5 (by rfl) ⟨244541, by rfl⟩ : syracuseStep 5216885 = 489083) (by norm_num)
theorem B662177 : Blo 542804 662177 := bbase (se 2 (by rfl) ⟨248316, by rfl⟩ : syracuseStep 662177 = 496633) (by norm_num)
theorem B1547029 : Blo 542804 1547029 := bbase (se 6 (by rfl) ⟨36258, by rfl⟩ : syracuseStep 1547029 = 72517) (by norm_num)
theorem B2333461 : Blo 542804 2333461 := bbase (se 6 (by rfl) ⟨54690, by rfl⟩ : syracuseStep 2333461 = 109381) (by norm_num)
theorem B629537 : Blo 542804 629537 := bbase (se 2 (by rfl) ⟨236076, by rfl⟩ : syracuseStep 629537 = 472153) (by norm_num)
theorem B1383277 : Blo 542804 1383277 := bbase (se 3 (by rfl) ⟨259364, by rfl⟩ : syracuseStep 1383277 = 518729) (by norm_num)
theorem B6986645 : Blo 542804 6986645 := bbase (se 6 (by rfl) ⟨163749, by rfl⟩ : syracuseStep 6986645 = 327499) (by norm_num)
theorem B1842101 : Blo 542804 1842101 := bbase (se 5 (by rfl) ⟨86348, by rfl⟩ : syracuseStep 1842101 = 172697) (by norm_num)
theorem B1383389 : Blo 542804 1383389 := bbase (se 3 (by rfl) ⟨259385, by rfl⟩ : syracuseStep 1383389 = 518771) (by norm_num)
theorem B2759669 : Blo 542804 2759669 := bbase (se 5 (by rfl) ⟨129359, by rfl⟩ : syracuseStep 2759669 = 258719) (by norm_num)
theorem B662581 : Blo 542804 662581 := bbase (se 5 (by rfl) ⟨31058, by rfl⟩ : syracuseStep 662581 = 62117) (by norm_num)
theorem B826453 : Blo 542804 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B1383581 : Blo 542804 1383581 := bbase (se 3 (by rfl) ⟨259421, by rfl⟩ : syracuseStep 1383581 = 518843) (by norm_num)
theorem B1023205 : Blo 542804 1023205 := bbase (se 4 (by rfl) ⟨95925, by rfl⟩ : syracuseStep 1023205 = 191851) (by norm_num)
theorem B23928149 : Blo 542804 23928149 := bbase (se 11 (by rfl) ⟨17525, by rfl⟩ : syracuseStep 23928149 = 35051) (by norm_num)
theorem B1842533 : Blo 542804 1842533 := bbase (se 4 (by rfl) ⟨172737, by rfl⟩ : syracuseStep 1842533 = 345475) (by norm_num)
theorem B2071925 : Blo 542804 2071925 := bbase (se 5 (by rfl) ⟨97121, by rfl⟩ : syracuseStep 2071925 = 194243) (by norm_num)
theorem B2334197 : Blo 542804 2334197 := bbase (se 5 (by rfl) ⟨109415, by rfl⟩ : syracuseStep 2334197 = 218831) (by norm_num)
theorem B1383925 : Blo 542804 1383925 := bbase (se 5 (by rfl) ⟨64871, by rfl⟩ : syracuseStep 1383925 = 129743) (by norm_num)
theorem B3317269 : Blo 542804 3317269 := bbase (se 6 (by rfl) ⟨77748, by rfl⟩ : syracuseStep 3317269 = 155497) (by norm_num)
theorem B663113 : Blo 542804 663113 := bbase (se 2 (by rfl) ⟨248667, by rfl⟩ : syracuseStep 663113 = 497335) (by norm_num)
theorem B1384037 : Blo 542804 1384037 := bbase (se 4 (by rfl) ⟨129753, by rfl⟩ : syracuseStep 1384037 = 259507) (by norm_num)
theorem B2072213 : Blo 542804 2072213 := bbase (se 6 (by rfl) ⟨48567, by rfl⟩ : syracuseStep 2072213 = 97135) (by norm_num)
theorem B1842965 : Blo 542804 1842965 := bbase (se 6 (by rfl) ⟨43194, by rfl⟩ : syracuseStep 1842965 = 86389) (by norm_num)
theorem B4202389 : Blo 542804 4202389 := bbase (se 6 (by rfl) ⟨98493, by rfl⟩ : syracuseStep 4202389 = 196987) (by norm_num)
theorem B696457 : Blo 542804 696457 := bbase (se 2 (by rfl) ⟨261171, by rfl⟩ : syracuseStep 696457 = 522343) (by norm_num)
theorem B663697 : Blo 542804 663697 := bbase (se 2 (by rfl) ⟨248886, by rfl⟩ : syracuseStep 663697 = 497773) (by norm_num)
theorem B1843397 : Blo 542804 1843397 := bbase (se 4 (by rfl) ⟨172818, by rfl⟩ : syracuseStep 1843397 = 345637) (by norm_num)
theorem B1548533 : Blo 542804 1548533 := bbase (se 5 (by rfl) ⟨72587, by rfl⟩ : syracuseStep 1548533 = 145175) (by norm_num)
theorem B2760965 : Blo 542804 2760965 := bbase (se 4 (by rfl) ⟨258840, by rfl⟩ : syracuseStep 2760965 = 517681) (by norm_num)
theorem B1745317 : Blo 542804 1745317 := bbase (se 4 (by rfl) ⟨163623, by rfl⟩ : syracuseStep 1745317 = 327247) (by norm_num)
theorem B1745381 : Blo 542804 1745381 := bbase (se 4 (by rfl) ⟨163629, by rfl⟩ : syracuseStep 1745381 = 327259) (by norm_num)
theorem B1843829 : Blo 542804 1843829 := bbase (se 5 (by rfl) ⟨86429, by rfl⟩ : syracuseStep 1843829 = 172859) (by norm_num)
theorem B4956821 : Blo 542804 4956821 := bbase (se 6 (by rfl) ⟨116175, by rfl⟩ : syracuseStep 4956821 = 232351) (by norm_num)
theorem B1221317 : Blo 542804 1221317 := bbase (se 4 (by rfl) ⟨114498, by rfl⟩ : syracuseStep 1221317 = 228997) (by norm_num)
theorem B1221389 : Blo 542804 1221389 := bbase (se 3 (by rfl) ⟨229010, by rfl⟩ : syracuseStep 1221389 = 458021) (by norm_num)
theorem B2073397 : Blo 542804 2073397 := bbase (se 5 (by rfl) ⟨97190, by rfl⟩ : syracuseStep 2073397 = 194381) (by norm_num)
theorem B1221461 : Blo 542804 1221461 := bbase (se 9 (by rfl) ⟨3578, by rfl⟩ : syracuseStep 1221461 = 7157) (by norm_num)
theorem B1221533 : Blo 542804 1221533 := bbase (se 3 (by rfl) ⟨229037, by rfl⟩ : syracuseStep 1221533 = 458075) (by norm_num)
theorem B1221605 : Blo 542804 1221605 := bbase (se 4 (by rfl) ⟨114525, by rfl⟩ : syracuseStep 1221605 = 229051) (by norm_num)
theorem B1844261 : Blo 542804 1844261 := bbase (se 4 (by rfl) ⟨172899, by rfl⟩ : syracuseStep 1844261 = 345799) (by norm_num)
theorem B1221677 : Blo 542804 1221677 := bbase (se 3 (by rfl) ⟨229064, by rfl⟩ : syracuseStep 1221677 = 458129) (by norm_num)
theorem B4432981 : Blo 542804 4432981 := bbase (se 8 (by rfl) ⟨25974, by rfl⟩ : syracuseStep 4432981 = 51949) (by norm_num)
theorem B2073701 : Blo 542804 2073701 := bbase (se 4 (by rfl) ⟨194409, by rfl⟩ : syracuseStep 2073701 = 388819) (by norm_num)
theorem B1221749 : Blo 542804 1221749 := bbase (se 5 (by rfl) ⟨57269, by rfl⟩ : syracuseStep 1221749 = 114539) (by norm_num)
theorem B599161 : Blo 542804 599161 := bbase (se 2 (by rfl) ⟨224685, by rfl⟩ : syracuseStep 599161 = 449371) (by norm_num)
theorem B1221821 : Blo 542804 1221821 := bbase (se 3 (by rfl) ⟨229091, by rfl⟩ : syracuseStep 1221821 = 458183) (by norm_num)
theorem B1221893 : Blo 542804 1221893 := bbase (se 4 (by rfl) ⟨114552, by rfl⟩ : syracuseStep 1221893 = 229105) (by norm_num)
theorem B1221965 : Blo 542804 1221965 := bbase (se 3 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 1221965 = 458237) (by norm_num)
theorem B664949 : Blo 542804 664949 := bbase (se 5 (by rfl) ⟨31169, by rfl⟩ : syracuseStep 664949 = 62339) (by norm_num)
theorem B1222037 : Blo 542804 1222037 := bbase (se 6 (by rfl) ⟨28641, by rfl⟩ : syracuseStep 1222037 = 57283) (by norm_num)
theorem B1844693 : Blo 542804 1844693 := bbase (se 7 (by rfl) ⟨21617, by rfl⟩ : syracuseStep 1844693 = 43235) (by norm_num)
theorem B1222109 : Blo 542804 1222109 := bbase (se 3 (by rfl) ⟨229145, by rfl⟩ : syracuseStep 1222109 = 458291) (by norm_num)
theorem B2762261 : Blo 542804 2762261 := bbase (se 6 (by rfl) ⟨64740, by rfl⟩ : syracuseStep 2762261 = 129481) (by norm_num)
theorem B1222181 : Blo 542804 1222181 := bbase (se 4 (by rfl) ⟨114579, by rfl⟩ : syracuseStep 1222181 = 229159) (by norm_num)
theorem B1222253 : Blo 542804 1222253 := bbase (se 3 (by rfl) ⟨229172, by rfl⟩ : syracuseStep 1222253 = 458345) (by norm_num)
theorem B1222325 : Blo 542804 1222325 := bbase (se 5 (by rfl) ⟨57296, by rfl⟩ : syracuseStep 1222325 = 114593) (by norm_num)
theorem B1222397 : Blo 542804 1222397 := bbase (se 3 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 1222397 = 458399) (by norm_num)
theorem B1550117 : Blo 542804 1550117 := bbase (se 4 (by rfl) ⟨145323, by rfl⟩ : syracuseStep 1550117 = 290647) (by norm_num)
theorem B1222469 : Blo 542804 1222469 := bbase (se 4 (by rfl) ⟨114606, by rfl⟩ : syracuseStep 1222469 = 229213) (by norm_num)
theorem B1845125 : Blo 542804 1845125 := bbase (se 4 (by rfl) ⟨172980, by rfl⟩ : syracuseStep 1845125 = 345961) (by norm_num)
theorem B1222541 : Blo 542804 1222541 := bbase (se 3 (by rfl) ⟨229226, by rfl⟩ : syracuseStep 1222541 = 458453) (by norm_num)
theorem B1222613 : Blo 542804 1222613 := bbase (se 7 (by rfl) ⟨14327, by rfl⟩ : syracuseStep 1222613 = 28655) (by norm_num)
theorem B829397 : Blo 542804 829397 := bbase (se 7 (by rfl) ⟨9719, by rfl⟩ : syracuseStep 829397 = 19439) (by norm_num)
theorem B1222685 : Blo 542804 1222685 := bbase (se 3 (by rfl) ⟨229253, by rfl⟩ : syracuseStep 1222685 = 458507) (by norm_num)
theorem B829469 : Blo 542804 829469 := bbase (se 3 (by rfl) ⟨155525, by rfl⟩ : syracuseStep 829469 = 311051) (by norm_num)
theorem B1222757 : Blo 542804 1222757 := bbase (se 4 (by rfl) ⟨114633, by rfl⟩ : syracuseStep 1222757 = 229267) (by norm_num)
theorem B6629525 : Blo 542804 6629525 := bbase (se 6 (by rfl) ⟨155379, by rfl⟩ : syracuseStep 6629525 = 310759) (by norm_num)
theorem B1222829 : Blo 542804 1222829 := bbase (se 3 (by rfl) ⟨229280, by rfl⟩ : syracuseStep 1222829 = 458561) (by norm_num)
theorem B698593 : Blo 542804 698593 := bbase (se 2 (by rfl) ⟨261972, by rfl⟩ : syracuseStep 698593 = 523945) (by norm_num)
theorem B1222901 : Blo 542804 1222901 := bbase (se 5 (by rfl) ⟨57323, by rfl⟩ : syracuseStep 1222901 = 114647) (by norm_num)
theorem B1222973 : Blo 542804 1222973 := bbase (se 3 (by rfl) ⟨229307, by rfl⟩ : syracuseStep 1222973 = 458615) (by norm_num)
theorem B1223045 : Blo 542804 1223045 := bbase (se 4 (by rfl) ⟨114660, by rfl⟩ : syracuseStep 1223045 = 229321) (by norm_num)
theorem B1550789 : Blo 542804 1550789 := bbase (se 4 (by rfl) ⟨145386, by rfl⟩ : syracuseStep 1550789 = 290773) (by norm_num)
theorem B1223117 : Blo 542804 1223117 := bbase (se 3 (by rfl) ⟨229334, by rfl⟩ : syracuseStep 1223117 = 458669) (by norm_num)
theorem B1223189 : Blo 542804 1223189 := bbase (se 6 (by rfl) ⟨28668, by rfl⟩ : syracuseStep 1223189 = 57337) (by norm_num)
theorem B1223261 : Blo 542804 1223261 := bbase (se 3 (by rfl) ⟨229361, by rfl⟩ : syracuseStep 1223261 = 458723) (by norm_num)
theorem B1223333 : Blo 542804 1223333 := bbase (se 4 (by rfl) ⟨114687, by rfl⟩ : syracuseStep 1223333 = 229375) (by norm_num)
theorem B1223405 : Blo 542804 1223405 := bbase (se 3 (by rfl) ⟨229388, by rfl⟩ : syracuseStep 1223405 = 458777) (by norm_num)
theorem B2763557 : Blo 542804 2763557 := bbase (se 4 (by rfl) ⟨259083, by rfl⟩ : syracuseStep 2763557 = 518167) (by norm_num)
theorem B1223477 : Blo 542804 1223477 := bbase (se 5 (by rfl) ⟨57350, by rfl⟩ : syracuseStep 1223477 = 114701) (by norm_num)
theorem B1551221 : Blo 542804 1551221 := bbase (se 5 (by rfl) ⟨72713, by rfl⟩ : syracuseStep 1551221 = 145427) (by norm_num)
theorem B1223549 : Blo 542804 1223549 := bbase (se 3 (by rfl) ⟨229415, by rfl⟩ : syracuseStep 1223549 = 458831) (by norm_num)
theorem B1223621 : Blo 542804 1223621 := bbase (se 4 (by rfl) ⟨114714, by rfl⟩ : syracuseStep 1223621 = 229429) (by norm_num)
theorem B1223693 : Blo 542804 1223693 := bbase (se 3 (by rfl) ⟨229442, by rfl⟩ : syracuseStep 1223693 = 458885) (by norm_num)
theorem B1223765 : Blo 542804 1223765 := bbase (se 8 (by rfl) ⟨7170, by rfl⟩ : syracuseStep 1223765 = 14341) (by norm_num)
theorem B1223837 : Blo 542804 1223837 := bbase (se 3 (by rfl) ⟨229469, by rfl⟩ : syracuseStep 1223837 = 458939) (by norm_num)
theorem B2075813 : Blo 542804 2075813 := bbase (se 4 (by rfl) ⟨194607, by rfl⟩ : syracuseStep 2075813 = 389215) (by norm_num)
theorem B1223909 : Blo 542804 1223909 := bbase (se 4 (by rfl) ⟨114741, by rfl⟩ : syracuseStep 1223909 = 229483) (by norm_num)
theorem B1223981 : Blo 542804 1223981 := bbase (se 3 (by rfl) ⟨229496, by rfl⟩ : syracuseStep 1223981 = 458993) (by norm_num)
theorem B5680469 : Blo 542804 5680469 := bbase (se 11 (by rfl) ⟨4160, by rfl⟩ : syracuseStep 5680469 = 8321) (by norm_num)
theorem B1224053 : Blo 542804 1224053 := bbase (se 5 (by rfl) ⟨57377, by rfl⟩ : syracuseStep 1224053 = 114755) (by norm_num)
theorem B1748405 : Blo 542804 1748405 := bbase (se 5 (by rfl) ⟨81956, by rfl⟩ : syracuseStep 1748405 = 163913) (by norm_num)
theorem B1224125 : Blo 542804 1224125 := bbase (se 3 (by rfl) ⟨229523, by rfl⟩ : syracuseStep 1224125 = 459047) (by norm_num)
theorem B2076101 : Blo 542804 2076101 := bbase (se 4 (by rfl) ⟨194634, by rfl⟩ : syracuseStep 2076101 = 389269) (by norm_num)
theorem B1224197 : Blo 542804 1224197 := bbase (se 4 (by rfl) ⟨114768, by rfl⟩ : syracuseStep 1224197 = 229537) (by norm_num)
theorem B1224269 : Blo 542804 1224269 := bbase (se 3 (by rfl) ⟨229550, by rfl⟩ : syracuseStep 1224269 = 459101) (by norm_num)
theorem B3092053 : Blo 542804 3092053 := bbase (se 8 (by rfl) ⟨18117, by rfl⟩ : syracuseStep 3092053 = 36235) (by norm_num)
theorem B1551973 : Blo 542804 1551973 := bbase (se 4 (by rfl) ⟨145497, by rfl⟩ : syracuseStep 1551973 = 290995) (by norm_num)
theorem B1224341 : Blo 542804 1224341 := bbase (se 6 (by rfl) ⟨28695, by rfl⟩ : syracuseStep 1224341 = 57391) (by norm_num)
theorem B1224413 : Blo 542804 1224413 := bbase (se 3 (by rfl) ⟨229577, by rfl⟩ : syracuseStep 1224413 = 459155) (by norm_num)
theorem B1191677 : Blo 542804 1191677 := bbase (se 3 (by rfl) ⟨223439, by rfl⟩ : syracuseStep 1191677 = 446879) (by norm_num)
theorem B1224485 : Blo 542804 1224485 := bbase (se 4 (by rfl) ⟨114795, by rfl⟩ : syracuseStep 1224485 = 229591) (by norm_num)
theorem B1224557 : Blo 542804 1224557 := bbase (se 3 (by rfl) ⟨229604, by rfl⟩ : syracuseStep 1224557 = 459209) (by norm_num)
theorem B1224629 : Blo 542804 1224629 := bbase (se 5 (by rfl) ⟨57404, by rfl⟩ : syracuseStep 1224629 = 114809) (by norm_num)
theorem B1224701 : Blo 542804 1224701 := bbase (se 3 (by rfl) ⟨229631, by rfl⟩ : syracuseStep 1224701 = 459263) (by norm_num)
theorem B2764853 : Blo 542804 2764853 := bbase (se 5 (by rfl) ⟨129602, by rfl⟩ : syracuseStep 2764853 = 259205) (by norm_num)
theorem B1224773 : Blo 542804 1224773 := bbase (se 4 (by rfl) ⟨114822, by rfl⟩ : syracuseStep 1224773 = 229645) (by norm_num)
theorem B1224845 : Blo 542804 1224845 := bbase (se 3 (by rfl) ⟨229658, by rfl⟩ : syracuseStep 1224845 = 459317) (by norm_num)
theorem B4141205 : Blo 542804 4141205 := bbase (se 6 (by rfl) ⟨97059, by rfl⟩ : syracuseStep 4141205 = 194119) (by norm_num)
theorem B1224917 : Blo 542804 1224917 := bbase (se 7 (by rfl) ⟨14354, by rfl⟩ : syracuseStep 1224917 = 28709) (by norm_num)
theorem B1061093 : Blo 542804 1061093 := bbase (se 4 (by rfl) ⟨99477, by rfl⟩ : syracuseStep 1061093 = 198955) (by norm_num)
theorem B1224989 : Blo 542804 1224989 := bbase (se 3 (by rfl) ⟨229685, by rfl⟩ : syracuseStep 1224989 = 459371) (by norm_num)
theorem B1225061 : Blo 542804 1225061 := bbase (se 4 (by rfl) ⟨114849, by rfl⟩ : syracuseStep 1225061 = 229699) (by norm_num)
theorem B1159589 : Blo 542804 1159589 := bbase (se 4 (by rfl) ⟨108711, by rfl⟩ : syracuseStep 1159589 = 217423) (by norm_num)
theorem B1225133 : Blo 542804 1225133 := bbase (se 3 (by rfl) ⟨229712, by rfl⟩ : syracuseStep 1225133 = 459425) (by norm_num)
theorem B1225205 : Blo 542804 1225205 := bbase (se 5 (by rfl) ⟨57431, by rfl⟩ : syracuseStep 1225205 = 114863) (by norm_num)
theorem B1225277 : Blo 542804 1225277 := bbase (se 3 (by rfl) ⟨229739, by rfl⟩ : syracuseStep 1225277 = 459479) (by norm_num)
theorem B1487477 : Blo 542804 1487477 := bbase (se 5 (by rfl) ⟨69725, by rfl⟩ : syracuseStep 1487477 = 139451) (by norm_num)
theorem B1225349 : Blo 542804 1225349 := bbase (se 4 (by rfl) ⟨114876, by rfl⟩ : syracuseStep 1225349 = 229753) (by norm_num)
theorem B4207285 : Blo 542804 4207285 := bbase (se 5 (by rfl) ⟨197216, by rfl⟩ : syracuseStep 4207285 = 394433) (by norm_num)
theorem B1225421 : Blo 542804 1225421 := bbase (se 3 (by rfl) ⟨229766, by rfl⟩ : syracuseStep 1225421 = 459533) (by norm_num)
theorem B1225493 : Blo 542804 1225493 := bbase (se 6 (by rfl) ⟨28722, by rfl⟩ : syracuseStep 1225493 = 57445) (by norm_num)
theorem B1225565 : Blo 542804 1225565 := bbase (se 3 (by rfl) ⟨229793, by rfl⟩ : syracuseStep 1225565 = 459587) (by norm_num)
theorem B1225637 : Blo 542804 1225637 := bbase (se 4 (by rfl) ⟨114903, by rfl⟩ : syracuseStep 1225637 = 229807) (by norm_num)
theorem B1225709 : Blo 542804 1225709 := bbase (se 3 (by rfl) ⟨229820, by rfl⟩ : syracuseStep 1225709 = 459641) (by norm_num)
theorem B1225781 : Blo 542804 1225781 := bbase (se 5 (by rfl) ⟨57458, by rfl⟩ : syracuseStep 1225781 = 114917) (by norm_num)
theorem B1225853 : Blo 542804 1225853 := bbase (se 3 (by rfl) ⟨229847, by rfl⟩ : syracuseStep 1225853 = 459695) (by norm_num)
theorem B1225925 : Blo 542804 1225925 := bbase (se 4 (by rfl) ⟨114930, by rfl⟩ : syracuseStep 1225925 = 229861) (by norm_num)
theorem B1225997 : Blo 542804 1225997 := bbase (se 3 (by rfl) ⟨229874, by rfl⟩ : syracuseStep 1225997 = 459749) (by norm_num)
theorem B2766149 : Blo 542804 2766149 := bbase (se 4 (by rfl) ⟨259326, by rfl⟩ : syracuseStep 2766149 = 518653) (by norm_num)
theorem B1226069 : Blo 542804 1226069 := bbase (se 13 (by rfl) ⟨224, by rfl⟩ : syracuseStep 1226069 = 449) (by norm_num)
theorem B1226141 : Blo 542804 1226141 := bbase (se 3 (by rfl) ⟨229901, by rfl⟩ : syracuseStep 1226141 = 459803) (by norm_num)
theorem B1226213 : Blo 542804 1226213 := bbase (se 4 (by rfl) ⟨114957, by rfl⟩ : syracuseStep 1226213 = 229915) (by norm_num)
theorem B3094037 : Blo 542804 3094037 := bbase (se 6 (by rfl) ⟨72516, by rfl⟩ : syracuseStep 3094037 = 145033) (by norm_num)
theorem B1226285 : Blo 542804 1226285 := bbase (se 3 (by rfl) ⟨229928, by rfl⟩ : syracuseStep 1226285 = 459857) (by norm_num)
theorem B734797 : Blo 542804 734797 := bbase (se 3 (by rfl) ⟨137774, by rfl⟩ : syracuseStep 734797 = 275549) (by norm_num)
theorem B1226357 : Blo 542804 1226357 := bbase (se 5 (by rfl) ⟨57485, by rfl⟩ : syracuseStep 1226357 = 114971) (by norm_num)
theorem B1226429 : Blo 542804 1226429 := bbase (se 3 (by rfl) ⟨229955, by rfl⟩ : syracuseStep 1226429 = 459911) (by norm_num)
theorem B1226501 : Blo 542804 1226501 := bbase (se 4 (by rfl) ⟨114984, by rfl⟩ : syracuseStep 1226501 = 229969) (by norm_num)
theorem B1226573 : Blo 542804 1226573 := bbase (se 3 (by rfl) ⟨229982, by rfl⟩ : syracuseStep 1226573 = 459965) (by norm_num)
theorem B1226645 : Blo 542804 1226645 := bbase (se 6 (by rfl) ⟨28749, by rfl⟩ : syracuseStep 1226645 = 57499) (by norm_num)
theorem B1226717 : Blo 542804 1226717 := bbase (se 3 (by rfl) ⟨230009, by rfl⟩ : syracuseStep 1226717 = 460019) (by norm_num)
theorem B1161229 : Blo 542804 1161229 := bbase (se 3 (by rfl) ⟨217730, by rfl⟩ : syracuseStep 1161229 = 435461) (by norm_num)
theorem B1226789 : Blo 542804 1226789 := bbase (se 4 (by rfl) ⟨115011, by rfl⟩ : syracuseStep 1226789 = 230023) (by norm_num)
theorem B1226861 : Blo 542804 1226861 := bbase (se 3 (by rfl) ⟨230036, by rfl⟩ : syracuseStep 1226861 = 460073) (by norm_num)
theorem B1226933 : Blo 542804 1226933 := bbase (se 5 (by rfl) ⟨57512, by rfl⟩ : syracuseStep 1226933 = 115025) (by norm_num)
theorem B1227005 : Blo 542804 1227005 := bbase (se 3 (by rfl) ⟨230063, by rfl⟩ : syracuseStep 1227005 = 460127) (by norm_num)
theorem B1227077 : Blo 542804 1227077 := bbase (se 4 (by rfl) ⟨115038, by rfl⟩ : syracuseStep 1227077 = 230077) (by norm_num)
theorem B2242885 : Blo 542804 2242885 := bbase (se 4 (by rfl) ⟨210270, by rfl⟩ : syracuseStep 2242885 = 420541) (by norm_num)
theorem B1554821 : Blo 542804 1554821 := bbase (se 4 (by rfl) ⟨145764, by rfl⟩ : syracuseStep 1554821 = 291529) (by norm_num)
theorem B1227149 : Blo 542804 1227149 := bbase (se 3 (by rfl) ⟨230090, by rfl⟩ : syracuseStep 1227149 = 460181) (by norm_num)
theorem B1227221 : Blo 542804 1227221 := bbase (se 7 (by rfl) ⟨14381, by rfl⟩ : syracuseStep 1227221 = 28763) (by norm_num)
theorem B1227293 : Blo 542804 1227293 := bbase (se 3 (by rfl) ⟨230117, by rfl⟩ : syracuseStep 1227293 = 460235) (by norm_num)
theorem B1325605 : Blo 542804 1325605 := bbase (se 4 (by rfl) ⟨124275, by rfl⟩ : syracuseStep 1325605 = 248551) (by norm_num)
theorem B2767445 : Blo 542804 2767445 := bbase (se 8 (by rfl) ⟨16215, by rfl⟩ : syracuseStep 2767445 = 32431) (by norm_num)
theorem B1227365 : Blo 542804 1227365 := bbase (se 4 (by rfl) ⟨115065, by rfl⟩ : syracuseStep 1227365 = 230131) (by norm_num)
theorem B1227437 : Blo 542804 1227437 := bbase (se 3 (by rfl) ⟨230144, by rfl⟩ : syracuseStep 1227437 = 460289) (by norm_num)
theorem B2243285 : Blo 542804 2243285 := bbase (se 7 (by rfl) ⟨26288, by rfl⟩ : syracuseStep 2243285 = 52577) (by norm_num)
theorem B1227509 : Blo 542804 1227509 := bbase (se 5 (by rfl) ⟨57539, by rfl⟩ : syracuseStep 1227509 = 115079) (by norm_num)
theorem B1227581 : Blo 542804 1227581 := bbase (se 3 (by rfl) ⟨230171, by rfl⟩ : syracuseStep 1227581 = 460343) (by norm_num)
theorem B1030981 : Blo 542804 1030981 := bbase (se 4 (by rfl) ⟨96654, by rfl⟩ : syracuseStep 1030981 = 193309) (by norm_num)
theorem B1162117 : Blo 542804 1162117 := bbase (se 4 (by rfl) ⟨108948, by rfl⟩ : syracuseStep 1162117 = 217897) (by norm_num)
theorem B1227653 : Blo 542804 1227653 := bbase (se 4 (by rfl) ⟨115092, by rfl⟩ : syracuseStep 1227653 = 230185) (by norm_num)
theorem B1227725 : Blo 542804 1227725 := bbase (se 3 (by rfl) ⟨230198, by rfl⟩ : syracuseStep 1227725 = 460397) (by norm_num)
theorem B1031125 : Blo 542804 1031125 := bbase (se 7 (by rfl) ⟨12083, by rfl⟩ : syracuseStep 1031125 = 24167) (by norm_num)
theorem B998357 : Blo 542804 998357 := bbase (se 7 (by rfl) ⟨11699, by rfl⟩ : syracuseStep 998357 = 23399) (by norm_num)
theorem B1260533 : Blo 542804 1260533 := bbase (se 5 (by rfl) ⟨59087, by rfl⟩ : syracuseStep 1260533 = 118175) (by norm_num)
theorem B1227797 : Blo 542804 1227797 := bbase (se 6 (by rfl) ⟨28776, by rfl⟩ : syracuseStep 1227797 = 57553) (by norm_num)
theorem B1227869 : Blo 542804 1227869 := bbase (se 3 (by rfl) ⟨230225, by rfl⟩ : syracuseStep 1227869 = 460451) (by norm_num)
theorem B1031285 : Blo 542804 1031285 := bbase (se 5 (by rfl) ⟨48341, by rfl⟩ : syracuseStep 1031285 = 96683) (by norm_num)
theorem B1653877 : Blo 542804 1653877 := bbase (se 5 (by rfl) ⟨77525, by rfl⟩ : syracuseStep 1653877 = 155051) (by norm_num)
theorem B1227941 : Blo 542804 1227941 := bbase (se 4 (by rfl) ⟨115119, by rfl⟩ : syracuseStep 1227941 = 230239) (by norm_num)
theorem B1228013 : Blo 542804 1228013 := bbase (se 3 (by rfl) ⟨230252, by rfl⟩ : syracuseStep 1228013 = 460505) (by norm_num)
theorem B1031429 : Blo 542804 1031429 := bbase (se 4 (by rfl) ⟨96696, by rfl⟩ : syracuseStep 1031429 = 193393) (by norm_num)
theorem B1228085 : Blo 542804 1228085 := bbase (se 5 (by rfl) ⟨57566, by rfl⟩ : syracuseStep 1228085 = 115133) (by norm_num)
theorem B1162613 : Blo 542804 1162613 := bbase (se 5 (by rfl) ⟨54497, by rfl⟩ : syracuseStep 1162613 = 108995) (by norm_num)
theorem B1228157 : Blo 542804 1228157 := bbase (se 3 (by rfl) ⟨230279, by rfl⟩ : syracuseStep 1228157 = 460559) (by norm_num)
theorem B933277 : Blo 542804 933277 := bbase (se 3 (by rfl) ⟨174989, by rfl⟩ : syracuseStep 933277 = 349979) (by norm_num)
theorem B1228229 : Blo 542804 1228229 := bbase (se 4 (by rfl) ⟨115146, by rfl⟩ : syracuseStep 1228229 = 230293) (by norm_num)
theorem B1228301 : Blo 542804 1228301 := bbase (se 3 (by rfl) ⟨230306, by rfl⟩ : syracuseStep 1228301 = 460613) (by norm_num)
theorem B4439573 : Blo 542804 4439573 := bbase (se 6 (by rfl) ⟨104052, by rfl⟩ : syracuseStep 4439573 = 208105) (by norm_num)
theorem B1031717 : Blo 542804 1031717 := bbase (se 4 (by rfl) ⟨96723, by rfl⟩ : syracuseStep 1031717 = 193447) (by norm_num)
theorem B1556005 : Blo 542804 1556005 := bbase (se 4 (by rfl) ⟨145875, by rfl⟩ : syracuseStep 1556005 = 291751) (by norm_num)
theorem B1228373 : Blo 542804 1228373 := bbase (se 8 (by rfl) ⟨7197, by rfl⟩ : syracuseStep 1228373 = 14395) (by norm_num)
theorem B1228445 : Blo 542804 1228445 := bbase (se 3 (by rfl) ⟨230333, by rfl⟩ : syracuseStep 1228445 = 460667) (by norm_num)
theorem B3096245 : Blo 542804 3096245 := bbase (se 5 (by rfl) ⟨145136, by rfl⟩ : syracuseStep 3096245 = 290273) (by norm_num)
theorem B4669109 : Blo 542804 4669109 := bbase (se 5 (by rfl) ⟨218864, by rfl⟩ : syracuseStep 4669109 = 437729) (by norm_num)
theorem B605881 : Blo 542804 605881 := bbase (se 2 (by rfl) ⟨227205, by rfl⟩ : syracuseStep 605881 = 454411) (by norm_num)
theorem B1031869 : Blo 542804 1031869 := bbase (se 3 (by rfl) ⟨193475, by rfl⟩ : syracuseStep 1031869 = 386951) (by norm_num)
theorem B1556165 : Blo 542804 1556165 := bbase (se 4 (by rfl) ⟨145890, by rfl⟩ : syracuseStep 1556165 = 291781) (by norm_num)
theorem B1228517 : Blo 542804 1228517 := bbase (se 4 (by rfl) ⟨115173, by rfl⟩ : syracuseStep 1228517 = 230347) (by norm_num)
theorem B2801429 : Blo 542804 2801429 := bbase (se 6 (by rfl) ⟨65658, by rfl⟩ : syracuseStep 2801429 = 131317) (by norm_num)
theorem B1228589 : Blo 542804 1228589 := bbase (se 3 (by rfl) ⟨230360, by rfl⟩ : syracuseStep 1228589 = 460721) (by norm_num)
theorem B1228661 : Blo 542804 1228661 := bbase (se 5 (by rfl) ⟨57593, by rfl⟩ : syracuseStep 1228661 = 115187) (by norm_num)
theorem B638857 : Blo 542804 638857 := bbase (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) (by norm_num)
theorem B1556405 : Blo 542804 1556405 := bbase (se 5 (by rfl) ⟨72956, by rfl⟩ : syracuseStep 1556405 = 145913) (by norm_num)
theorem B1228733 : Blo 542804 1228733 := bbase (se 3 (by rfl) ⟨230387, by rfl⟩ : syracuseStep 1228733 = 460775) (by norm_num)
theorem B1032173 : Blo 542804 1032173 := bbase (se 3 (by rfl) ⟨193532, by rfl⟩ : syracuseStep 1032173 = 387065) (by norm_num)
theorem B1228805 : Blo 542804 1228805 := bbase (se 4 (by rfl) ⟨115200, by rfl⟩ : syracuseStep 1228805 = 230401) (by norm_num)
theorem B1228877 : Blo 542804 1228877 := bbase (se 3 (by rfl) ⟨230414, by rfl⟩ : syracuseStep 1228877 = 460829) (by norm_num)
theorem B6209621 : Blo 542804 6209621 := bbase (se 8 (by rfl) ⟨36384, by rfl⟩ : syracuseStep 6209621 = 72769) (by norm_num)
theorem B1556597 : Blo 542804 1556597 := bbase (se 5 (by rfl) ⟨72965, by rfl⟩ : syracuseStep 1556597 = 145931) (by norm_num)
theorem B1228949 : Blo 542804 1228949 := bbase (se 6 (by rfl) ⟨28803, by rfl⟩ : syracuseStep 1228949 = 57607) (by norm_num)
theorem B1654997 : Blo 542804 1654997 := bbase (se 7 (by rfl) ⟨19394, by rfl⟩ : syracuseStep 1654997 = 38789) (by norm_num)
theorem B1163477 : Blo 542804 1163477 := bbase (se 7 (by rfl) ⟨13634, by rfl⟩ : syracuseStep 1163477 = 27269) (by norm_num)
theorem B1229021 : Blo 542804 1229021 := bbase (se 3 (by rfl) ⟨230441, by rfl⟩ : syracuseStep 1229021 = 460883) (by norm_num)
theorem B1229093 : Blo 542804 1229093 := bbase (se 4 (by rfl) ⟨115227, by rfl⟩ : syracuseStep 1229093 = 230455) (by norm_num)
theorem B1163621 : Blo 542804 1163621 := bbase (se 4 (by rfl) ⟨109089, by rfl⟩ : syracuseStep 1163621 = 218179) (by norm_num)
theorem B1229165 : Blo 542804 1229165 := bbase (se 3 (by rfl) ⟨230468, by rfl⟩ : syracuseStep 1229165 = 460937) (by norm_num)
theorem B1229237 : Blo 542804 1229237 := bbase (se 5 (by rfl) ⟨57620, by rfl⟩ : syracuseStep 1229237 = 115241) (by norm_num)
theorem B934357 : Blo 542804 934357 := bbase (se 7 (by rfl) ⟨10949, by rfl⟩ : syracuseStep 934357 = 21899) (by norm_num)
theorem B1229309 : Blo 542804 1229309 := bbase (se 3 (by rfl) ⟨230495, by rfl⟩ : syracuseStep 1229309 = 460991) (by norm_num)
theorem B1229381 : Blo 542804 1229381 := bbase (se 4 (by rfl) ⟨115254, by rfl⟩ : syracuseStep 1229381 = 230509) (by norm_num)
theorem B1229453 : Blo 542804 1229453 := bbase (se 3 (by rfl) ⟨230522, by rfl⟩ : syracuseStep 1229453 = 461045) (by norm_num)
theorem B1229525 : Blo 542804 1229525 := bbase (se 7 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 1229525 = 28817) (by norm_num)
theorem B1032925 : Blo 542804 1032925 := bbase (se 3 (by rfl) ⟨193673, by rfl⟩ : syracuseStep 1032925 = 387347) (by norm_num)
theorem B1229597 : Blo 542804 1229597 := bbase (se 3 (by rfl) ⟨230549, by rfl⟩ : syracuseStep 1229597 = 461099) (by norm_num)
theorem B1229669 : Blo 542804 1229669 := bbase (se 4 (by rfl) ⟨115281, by rfl⟩ : syracuseStep 1229669 = 230563) (by norm_num)
theorem B1033069 : Blo 542804 1033069 := bbase (se 3 (by rfl) ⟨193700, by rfl⟩ : syracuseStep 1033069 = 387401) (by norm_num)
theorem B1229741 : Blo 542804 1229741 := bbase (se 3 (by rfl) ⟨230576, by rfl⟩ : syracuseStep 1229741 = 461153) (by norm_num)
theorem B1229813 : Blo 542804 1229813 := bbase (se 5 (by rfl) ⟨57647, by rfl⟩ : syracuseStep 1229813 = 115295) (by norm_num)
theorem B738301 : Blo 542804 738301 := bbase (se 3 (by rfl) ⟨138431, by rfl⟩ : syracuseStep 738301 = 276863) (by norm_num)
theorem B1033229 : Blo 542804 1033229 := bbase (se 3 (by rfl) ⟨193730, by rfl⟩ : syracuseStep 1033229 = 387461) (by norm_num)
theorem B1229885 : Blo 542804 1229885 := bbase (se 3 (by rfl) ⟨230603, by rfl⟩ : syracuseStep 1229885 = 461207) (by norm_num)
theorem B1164365 : Blo 542804 1164365 := bbase (se 3 (by rfl) ⟨218318, by rfl⟩ : syracuseStep 1164365 = 436637) (by norm_num)
theorem B1229957 : Blo 542804 1229957 := bbase (se 4 (by rfl) ⟨115308, by rfl⟩ : syracuseStep 1229957 = 230617) (by norm_num)
theorem B1033373 : Blo 542804 1033373 := bbase (se 3 (by rfl) ⟨193757, by rfl⟩ : syracuseStep 1033373 = 387515) (by norm_num)
theorem B1230029 : Blo 542804 1230029 := bbase (se 3 (by rfl) ⟨230630, by rfl⟩ : syracuseStep 1230029 = 461261) (by norm_num)
theorem B6964501 : Blo 542804 6964501 := bbase (se 6 (by rfl) ⟨163230, by rfl⟩ : syracuseStep 6964501 = 326461) (by norm_num)
theorem B1230101 : Blo 542804 1230101 := bbase (se 6 (by rfl) ⟨28830, by rfl⟩ : syracuseStep 1230101 = 57661) (by norm_num)
theorem B1230173 : Blo 542804 1230173 := bbase (se 3 (by rfl) ⟨230657, by rfl⟩ : syracuseStep 1230173 = 461315) (by norm_num)
theorem B1230245 : Blo 542804 1230245 := bbase (se 4 (by rfl) ⟨115335, by rfl⟩ : syracuseStep 1230245 = 230671) (by norm_num)
theorem B1033661 : Blo 542804 1033661 := bbase (se 3 (by rfl) ⟨193811, by rfl⟩ : syracuseStep 1033661 = 387623) (by norm_num)
theorem B2803157 : Blo 542804 2803157 := bbase (se 7 (by rfl) ⟨32849, by rfl⟩ : syracuseStep 2803157 = 65699) (by norm_num)
theorem B574993 : Blo 542804 574993 := bbase (se 2 (by rfl) ⟨215622, by rfl⟩ : syracuseStep 574993 = 431245) (by norm_num)
theorem B1033813 : Blo 542804 1033813 := bbase (se 8 (by rfl) ⟨6057, by rfl⟩ : syracuseStep 1033813 = 12115) (by norm_num)
theorem B870077 : Blo 542804 870077 := bbase (se 3 (by rfl) ⟨163139, by rfl⟩ : syracuseStep 870077 = 326279) (by norm_num)
theorem B1165117 : Blo 542804 1165117 := bbase (se 3 (by rfl) ⟨218459, by rfl⟩ : syracuseStep 1165117 = 436919) (by norm_num)
theorem B1034117 : Blo 542804 1034117 := bbase (se 4 (by rfl) ⟨96948, by rfl⟩ : syracuseStep 1034117 = 193897) (by norm_num)
theorem B870301 : Blo 542804 870301 := bbase (se 3 (by rfl) ⟨163181, by rfl⟩ : syracuseStep 870301 = 326363) (by norm_num)
theorem B1165261 : Blo 542804 1165261 := bbase (se 3 (by rfl) ⟨218486, by rfl⟩ : syracuseStep 1165261 = 436973) (by norm_num)
theorem B4638869 : Blo 542804 4638869 := bbase (se 6 (by rfl) ⟨108723, by rfl⟩ : syracuseStep 4638869 = 217447) (by norm_num)
theorem B1165637 : Blo 542804 1165637 := bbase (se 4 (by rfl) ⟨109278, by rfl⟩ : syracuseStep 1165637 = 218557) (by norm_num)
theorem B1034869 : Blo 542804 1034869 := bbase (se 5 (by rfl) ⟨48509, by rfl⟩ : syracuseStep 1034869 = 97019) (by norm_num)
theorem B1100461 : Blo 542804 1100461 := bbase (se 3 (by rfl) ⟨206336, by rfl⟩ : syracuseStep 1100461 = 412673) (by norm_num)
theorem B1166005 : Blo 542804 1166005 := bbase (se 5 (by rfl) ⟨54656, by rfl⟩ : syracuseStep 1166005 = 109313) (by norm_num)
theorem B1100477 : Blo 542804 1100477 := bbase (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) (by norm_num)
theorem B1035013 : Blo 542804 1035013 := bbase (se 4 (by rfl) ⟨97032, by rfl⟩ : syracuseStep 1035013 = 194065) (by norm_num)
theorem B1395533 : Blo 542804 1395533 := bbase (se 3 (by rfl) ⟨261662, by rfl⟩ : syracuseStep 1395533 = 523325) (by norm_num)
theorem B1395541 : Blo 542804 1395541 := bbase (se 9 (by rfl) ⟨4088, by rfl⟩ : syracuseStep 1395541 = 8177) (by norm_num)
theorem B1035173 : Blo 542804 1035173 := bbase (se 4 (by rfl) ⟨97047, by rfl⟩ : syracuseStep 1035173 = 194095) (by norm_num)
theorem B773173 : Blo 542804 773173 := bbase (se 5 (by rfl) ⟨36242, by rfl⟩ : syracuseStep 773173 = 72485) (by norm_num)
theorem B1035317 : Blo 542804 1035317 := bbase (se 5 (by rfl) ⟨48530, by rfl⟩ : syracuseStep 1035317 = 97061) (by norm_num)
theorem B871717 : Blo 542804 871717 := bbase (se 4 (by rfl) ⟨81723, by rfl⟩ : syracuseStep 871717 = 163447) (by norm_num)
theorem B1035605 : Blo 542804 1035605 := bbase (se 11 (by rfl) ⟨758, by rfl⟩ : syracuseStep 1035605 = 1517) (by norm_num)
theorem B2477461 : Blo 542804 2477461 := bbase (se 6 (by rfl) ⟨58065, by rfl⟩ : syracuseStep 2477461 = 116131) (by norm_num)
theorem B2608613 : Blo 542804 2608613 := bbase (se 4 (by rfl) ⟨244557, by rfl⟩ : syracuseStep 2608613 = 489115) (by norm_num)
theorem B1035757 : Blo 542804 1035757 := bbase (se 3 (by rfl) ⟨194204, by rfl⟩ : syracuseStep 1035757 = 388409) (by norm_num)
theorem B871973 : Blo 542804 871973 := bbase (se 4 (by rfl) ⟨81747, by rfl⟩ : syracuseStep 871973 = 163495) (by norm_num)
theorem B1658549 : Blo 542804 1658549 := bbase (se 5 (by rfl) ⟨77744, by rfl⟩ : syracuseStep 1658549 = 155489) (by norm_num)
theorem B1396445 : Blo 542804 1396445 := bbase (se 3 (by rfl) ⟨261833, by rfl⟩ : syracuseStep 1396445 = 523667) (by norm_num)
theorem B872165 : Blo 542804 872165 := bbase (se 4 (by rfl) ⟨81765, by rfl⟩ : syracuseStep 872165 = 163531) (by norm_num)
theorem B4148981 : Blo 542804 4148981 := bbase (se 5 (by rfl) ⟨194483, by rfl⟩ : syracuseStep 4148981 = 388967) (by norm_num)
theorem B1036061 : Blo 542804 1036061 := bbase (se 3 (by rfl) ⟨194261, by rfl⟩ : syracuseStep 1036061 = 388523) (by norm_num)
theorem B1101613 : Blo 542804 1101613 := bbase (se 3 (by rfl) ⟨206552, by rfl⟩ : syracuseStep 1101613 = 413105) (by norm_num)
theorem B773965 : Blo 542804 773965 := bbase (se 3 (by rfl) ⟨145118, by rfl⟩ : syracuseStep 773965 = 290237) (by norm_num)
theorem B2215973 : Blo 542804 2215973 := bbase (se 4 (by rfl) ⟨207747, by rfl⟩ : syracuseStep 2215973 = 415495) (by norm_num)
theorem B3723413 : Blo 542804 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B1167509 : Blo 542804 1167509 := bbase (se 6 (by rfl) ⟨27363, by rfl⟩ : syracuseStep 1167509 = 54727) (by norm_num)
theorem B774301 : Blo 542804 774301 := bbase (se 3 (by rfl) ⟨145181, by rfl⟩ : syracuseStep 774301 = 290363) (by norm_num)
theorem B1167653 : Blo 542804 1167653 := bbase (se 4 (by rfl) ⟨109467, by rfl⟩ : syracuseStep 1167653 = 218935) (by norm_num)
theorem B774517 : Blo 542804 774517 := bbase (se 5 (by rfl) ⟨36305, by rfl⟩ : syracuseStep 774517 = 72611) (by norm_num)
theorem B610681 : Blo 542804 610681 := bbase (se 2 (by rfl) ⟨229005, by rfl⟩ : syracuseStep 610681 = 458011) (by norm_num)
theorem B610717 : Blo 542804 610717 := bbase (se 3 (by rfl) ⟨114509, by rfl⟩ : syracuseStep 610717 = 229019) (by norm_num)
theorem B610753 : Blo 542804 610753 := bbase (se 2 (by rfl) ⟨229032, by rfl⟩ : syracuseStep 610753 = 458065) (by norm_num)
theorem B610789 : Blo 542804 610789 := bbase (se 4 (by rfl) ⟨57261, by rfl⟩ : syracuseStep 610789 = 114523) (by norm_num)
theorem B1102325 : Blo 542804 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B610825 : Blo 542804 610825 := bbase (se 2 (by rfl) ⟨229059, by rfl⟩ : syracuseStep 610825 = 458119) (by norm_num)
theorem B1036813 : Blo 542804 1036813 := bbase (se 3 (by rfl) ⟨194402, by rfl⟩ : syracuseStep 1036813 = 388805) (by norm_num)
theorem B610861 : Blo 542804 610861 := bbase (se 3 (by rfl) ⟨114536, by rfl⟩ : syracuseStep 610861 = 229073) (by norm_num)
theorem B610897 : Blo 542804 610897 := bbase (se 2 (by rfl) ⟨229086, by rfl⟩ : syracuseStep 610897 = 458173) (by norm_num)
theorem B610933 : Blo 542804 610933 := bbase (se 5 (by rfl) ⟨28637, by rfl⟩ : syracuseStep 610933 = 57275) (by norm_num)
theorem B873101 : Blo 542804 873101 := bbase (se 3 (by rfl) ⟨163706, by rfl⟩ : syracuseStep 873101 = 327413) (by norm_num)
theorem B610969 : Blo 542804 610969 := bbase (se 2 (by rfl) ⟨229113, by rfl⟩ : syracuseStep 610969 = 458227) (by norm_num)
theorem B1036957 : Blo 542804 1036957 := bbase (se 3 (by rfl) ⟨194429, by rfl⟩ : syracuseStep 1036957 = 388859) (by norm_num)
theorem B611005 : Blo 542804 611005 := bbase (se 3 (by rfl) ⟨114563, by rfl⟩ : syracuseStep 611005 = 229127) (by norm_num)
theorem B611041 : Blo 542804 611041 := bbase (se 2 (by rfl) ⟨229140, by rfl⟩ : syracuseStep 611041 = 458281) (by norm_num)
theorem B774893 : Blo 542804 774893 := bbase (se 3 (by rfl) ⟨145292, by rfl⟩ : syracuseStep 774893 = 290585) (by norm_num)
theorem B611077 : Blo 542804 611077 := bbase (se 4 (by rfl) ⟨57288, by rfl⟩ : syracuseStep 611077 = 114577) (by norm_num)
theorem B611113 : Blo 542804 611113 := bbase (se 2 (by rfl) ⟨229167, by rfl⟩ : syracuseStep 611113 = 458335) (by norm_num)
theorem B1037117 : Blo 542804 1037117 := bbase (se 3 (by rfl) ⟨194459, by rfl⟩ : syracuseStep 1037117 = 388919) (by norm_num)
theorem B611149 : Blo 542804 611149 := bbase (se 3 (by rfl) ⟨114590, by rfl⟩ : syracuseStep 611149 = 229181) (by norm_num)
theorem B611185 : Blo 542804 611185 := bbase (se 2 (by rfl) ⟨229194, by rfl⟩ : syracuseStep 611185 = 458389) (by norm_num)
theorem B611221 : Blo 542804 611221 := bbase (se 6 (by rfl) ⟨14325, by rfl⟩ : syracuseStep 611221 = 28651) (by norm_num)
theorem B611257 : Blo 542804 611257 := bbase (se 2 (by rfl) ⟨229221, by rfl⟩ : syracuseStep 611257 = 458443) (by norm_num)
theorem B1037261 : Blo 542804 1037261 := bbase (se 3 (by rfl) ⟨194486, by rfl⟩ : syracuseStep 1037261 = 388973) (by norm_num)
theorem B611293 : Blo 542804 611293 := bbase (se 3 (by rfl) ⟨114617, by rfl⟩ : syracuseStep 611293 = 229235) (by norm_num)
theorem B611329 : Blo 542804 611329 := bbase (se 2 (by rfl) ⟨229248, by rfl⟩ : syracuseStep 611329 = 458497) (by norm_num)
theorem B873485 : Blo 542804 873485 := bbase (se 3 (by rfl) ⟨163778, by rfl⟩ : syracuseStep 873485 = 327557) (by norm_num)
theorem B611365 : Blo 542804 611365 := bbase (se 4 (by rfl) ⟨57315, by rfl⟩ : syracuseStep 611365 = 114631) (by norm_num)
theorem B611401 : Blo 542804 611401 := bbase (se 2 (by rfl) ⟨229275, by rfl⟩ : syracuseStep 611401 = 458551) (by norm_num)
theorem B611437 : Blo 542804 611437 := bbase (se 3 (by rfl) ⟨114644, by rfl⟩ : syracuseStep 611437 = 229289) (by norm_num)
theorem B873613 : Blo 542804 873613 := bbase (se 3 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 873613 = 327605) (by norm_num)
theorem B611473 : Blo 542804 611473 := bbase (se 2 (by rfl) ⟨229302, by rfl⟩ : syracuseStep 611473 = 458605) (by norm_num)
theorem B611509 : Blo 542804 611509 := bbase (se 5 (by rfl) ⟨28664, by rfl⟩ : syracuseStep 611509 = 57329) (by norm_num)
theorem B611545 : Blo 542804 611545 := bbase (se 2 (by rfl) ⟨229329, by rfl⟩ : syracuseStep 611545 = 458659) (by norm_num)
theorem B1037549 : Blo 542804 1037549 := bbase (se 3 (by rfl) ⟨194540, by rfl⟩ : syracuseStep 1037549 = 389081) (by norm_num)
theorem B611581 : Blo 542804 611581 := bbase (se 3 (by rfl) ⟨114671, by rfl⟩ : syracuseStep 611581 = 229343) (by norm_num)
theorem B2938133 : Blo 542804 2938133 := bbase (se 6 (by rfl) ⟨68862, by rfl⟩ : syracuseStep 2938133 = 137725) (by norm_num)
theorem B611617 : Blo 542804 611617 := bbase (se 2 (by rfl) ⟨229356, by rfl⟩ : syracuseStep 611617 = 458713) (by norm_num)
theorem B3495221 : Blo 542804 3495221 := bbase (se 5 (by rfl) ⟨163838, by rfl⟩ : syracuseStep 3495221 = 327677) (by norm_num)
theorem B611653 : Blo 542804 611653 := bbase (se 4 (by rfl) ⟨57342, by rfl⟩ : syracuseStep 611653 = 114685) (by norm_num)
theorem B611689 : Blo 542804 611689 := bbase (se 2 (by rfl) ⟨229383, by rfl⟩ : syracuseStep 611689 = 458767) (by norm_num)
theorem B1037701 : Blo 542804 1037701 := bbase (se 4 (by rfl) ⟨97284, by rfl⟩ : syracuseStep 1037701 = 194569) (by norm_num)
theorem B611725 : Blo 542804 611725 := bbase (se 3 (by rfl) ⟨114698, by rfl⟩ : syracuseStep 611725 = 229397) (by norm_num)
theorem B611761 : Blo 542804 611761 := bbase (se 2 (by rfl) ⟨229410, by rfl⟩ : syracuseStep 611761 = 458821) (by norm_num)
theorem B611797 : Blo 542804 611797 := bbase (se 7 (by rfl) ⟨7169, by rfl⟩ : syracuseStep 611797 = 14339) (by norm_num)
theorem B611833 : Blo 542804 611833 := bbase (se 2 (by rfl) ⟨229437, by rfl⟩ : syracuseStep 611833 = 458875) (by norm_num)
theorem B611869 : Blo 542804 611869 := bbase (se 3 (by rfl) ⟨114725, by rfl⟩ : syracuseStep 611869 = 229451) (by norm_num)
theorem B611905 : Blo 542804 611905 := bbase (se 2 (by rfl) ⟨229464, by rfl⟩ : syracuseStep 611905 = 458929) (by norm_num)
theorem B1103429 : Blo 542804 1103429 := bbase (se 4 (by rfl) ⟨103446, by rfl⟩ : syracuseStep 1103429 = 206893) (by norm_num)
theorem B611941 : Blo 542804 611941 := bbase (se 4 (by rfl) ⟨57369, by rfl⟩ : syracuseStep 611941 = 114739) (by norm_num)
theorem B611977 : Blo 542804 611977 := bbase (se 2 (by rfl) ⟨229491, by rfl⟩ : syracuseStep 611977 = 458983) (by norm_num)
theorem B612013 : Blo 542804 612013 := bbase (se 3 (by rfl) ⟨114752, by rfl⟩ : syracuseStep 612013 = 229505) (by norm_num)
theorem B1038005 : Blo 542804 1038005 := bbase (se 5 (by rfl) ⟨48656, by rfl⟩ : syracuseStep 1038005 = 97313) (by norm_num)
theorem B612049 : Blo 542804 612049 := bbase (se 2 (by rfl) ⟨229518, by rfl⟩ : syracuseStep 612049 = 459037) (by norm_num)
theorem B612085 : Blo 542804 612085 := bbase (se 5 (by rfl) ⟨28691, by rfl⟩ : syracuseStep 612085 = 57383) (by norm_num)
theorem B612121 : Blo 542804 612121 := bbase (se 2 (by rfl) ⟨229545, by rfl⟩ : syracuseStep 612121 = 459091) (by norm_num)
theorem B612157 : Blo 542804 612157 := bbase (se 3 (by rfl) ⟨114779, by rfl⟩ : syracuseStep 612157 = 229559) (by norm_num)
theorem B612193 : Blo 542804 612193 := bbase (se 2 (by rfl) ⟨229572, by rfl⟩ : syracuseStep 612193 = 459145) (by norm_num)
theorem B612229 : Blo 542804 612229 := bbase (se 4 (by rfl) ⟨57396, by rfl⟩ : syracuseStep 612229 = 114793) (by norm_num)
theorem B612265 : Blo 542804 612265 := bbase (se 2 (by rfl) ⟨229599, by rfl⟩ : syracuseStep 612265 = 459199) (by norm_num)
theorem B612301 : Blo 542804 612301 := bbase (se 3 (by rfl) ⟨114806, by rfl⟩ : syracuseStep 612301 = 229613) (by norm_num)
theorem B612337 : Blo 542804 612337 := bbase (se 2 (by rfl) ⟨229626, by rfl⟩ : syracuseStep 612337 = 459253) (by norm_num)
theorem B612373 : Blo 542804 612373 := bbase (se 6 (by rfl) ⟨14352, by rfl⟩ : syracuseStep 612373 = 28705) (by norm_num)
theorem B612409 : Blo 542804 612409 := bbase (se 2 (by rfl) ⟨229653, by rfl⟩ : syracuseStep 612409 = 459307) (by norm_num)
theorem B612445 : Blo 542804 612445 := bbase (se 3 (by rfl) ⟨114833, by rfl⟩ : syracuseStep 612445 = 229667) (by norm_num)
theorem B874613 : Blo 542804 874613 := bbase (se 5 (by rfl) ⟨40997, by rfl⟩ : syracuseStep 874613 = 81995) (by norm_num)
theorem B776317 : Blo 542804 776317 := bbase (se 3 (by rfl) ⟨145559, by rfl⟩ : syracuseStep 776317 = 291119) (by norm_num)
theorem B612481 : Blo 542804 612481 := bbase (se 2 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 612481 = 459361) (by norm_num)
theorem B612517 : Blo 542804 612517 := bbase (se 4 (by rfl) ⟨57423, by rfl⟩ : syracuseStep 612517 = 114847) (by norm_num)
theorem B2611381 : Blo 542804 2611381 := bbase (se 5 (by rfl) ⟨122408, by rfl⟩ : syracuseStep 2611381 = 244817) (by norm_num)
theorem B612553 : Blo 542804 612553 := bbase (se 2 (by rfl) ⟨229707, by rfl⟩ : syracuseStep 612553 = 459415) (by norm_num)
theorem B612589 : Blo 542804 612589 := bbase (se 3 (by rfl) ⟨114860, by rfl⟩ : syracuseStep 612589 = 229721) (by norm_num)
theorem B874741 : Blo 542804 874741 := bbase (se 5 (by rfl) ⟨41003, by rfl⟩ : syracuseStep 874741 = 82007) (by norm_num)
theorem B612625 : Blo 542804 612625 := bbase (se 2 (by rfl) ⟨229734, by rfl⟩ : syracuseStep 612625 = 459469) (by norm_num)
theorem B612661 : Blo 542804 612661 := bbase (se 5 (by rfl) ⟨28718, by rfl⟩ : syracuseStep 612661 = 57437) (by norm_num)
theorem B612697 : Blo 542804 612697 := bbase (se 2 (by rfl) ⟨229761, by rfl⟩ : syracuseStep 612697 = 459523) (by norm_num)
theorem B579965 : Blo 542804 579965 := bbase (se 3 (by rfl) ⟨108743, by rfl⟩ : syracuseStep 579965 = 217487) (by norm_num)
theorem B612733 : Blo 542804 612733 := bbase (se 3 (by rfl) ⟨114887, by rfl⟩ : syracuseStep 612733 = 229775) (by norm_num)
theorem B4413845 : Blo 542804 4413845 := bbase (se 6 (by rfl) ⟨103449, by rfl⟩ : syracuseStep 4413845 = 206899) (by norm_num)
theorem B612769 : Blo 542804 612769 := bbase (se 2 (by rfl) ⟨229788, by rfl⟩ : syracuseStep 612769 = 459577) (by norm_num)
theorem B612805 : Blo 542804 612805 := bbase (se 4 (by rfl) ⟨57450, by rfl⟩ : syracuseStep 612805 = 114901) (by norm_num)
theorem B612841 : Blo 542804 612841 := bbase (se 2 (by rfl) ⟨229815, by rfl⟩ : syracuseStep 612841 = 459631) (by norm_num)
theorem B4708853 : Blo 542804 4708853 := bbase (se 5 (by rfl) ⟨220727, by rfl⟩ : syracuseStep 4708853 = 441455) (by norm_num)
theorem B612877 : Blo 542804 612877 := bbase (se 3 (by rfl) ⟨114914, by rfl⟩ : syracuseStep 612877 = 229829) (by norm_num)
theorem B1858085 : Blo 542804 1858085 := bbase (se 4 (by rfl) ⟨174195, by rfl⟩ : syracuseStep 1858085 = 348391) (by norm_num)
theorem B612913 : Blo 542804 612913 := bbase (se 2 (by rfl) ⟨229842, by rfl⟩ : syracuseStep 612913 = 459685) (by norm_num)
theorem B612949 : Blo 542804 612949 := bbase (se 8 (by rfl) ⟨3591, by rfl⟩ : syracuseStep 612949 = 7183) (by norm_num)
theorem B580213 : Blo 542804 580213 := bbase (se 5 (by rfl) ⟨27197, by rfl⟩ : syracuseStep 580213 = 54395) (by norm_num)
theorem B875125 : Blo 542804 875125 := bbase (se 5 (by rfl) ⟨41021, by rfl⟩ : syracuseStep 875125 = 82043) (by norm_num)
theorem B612985 : Blo 542804 612985 := bbase (se 2 (by rfl) ⟨229869, by rfl⟩ : syracuseStep 612985 = 459739) (by norm_num)
theorem B613021 : Blo 542804 613021 := bbase (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) (by norm_num)
theorem B613057 : Blo 542804 613057 := bbase (se 2 (by rfl) ⟨229896, by rfl⟩ : syracuseStep 613057 = 459793) (by norm_num)
theorem B776909 : Blo 542804 776909 := bbase (se 3 (by rfl) ⟨145670, by rfl⟩ : syracuseStep 776909 = 291341) (by norm_num)
theorem B613093 : Blo 542804 613093 := bbase (se 4 (by rfl) ⟨57477, by rfl⟩ : syracuseStep 613093 = 114955) (by norm_num)
theorem B613129 : Blo 542804 613129 := bbase (se 2 (by rfl) ⟨229923, by rfl⟩ : syracuseStep 613129 = 459847) (by norm_num)
theorem B776989 : Blo 542804 776989 := bbase (se 3 (by rfl) ⟨145685, by rfl⟩ : syracuseStep 776989 = 291371) (by norm_num)
theorem B613165 : Blo 542804 613165 := bbase (se 3 (by rfl) ⟨114968, by rfl⟩ : syracuseStep 613165 = 229937) (by norm_num)
theorem B613201 : Blo 542804 613201 := bbase (se 2 (by rfl) ⟨229950, by rfl⟩ : syracuseStep 613201 = 459901) (by norm_num)
theorem B613237 : Blo 542804 613237 := bbase (se 5 (by rfl) ⟨28745, by rfl⟩ : syracuseStep 613237 = 57491) (by norm_num)
theorem B875381 : Blo 542804 875381 := bbase (se 5 (by rfl) ⟨41033, by rfl⟩ : syracuseStep 875381 = 82067) (by norm_num)
theorem B777109 : Blo 542804 777109 := bbase (se 6 (by rfl) ⟨18213, by rfl⟩ : syracuseStep 777109 = 36427) (by norm_num)
theorem B613273 : Blo 542804 613273 := bbase (se 2 (by rfl) ⟨229977, by rfl⟩ : syracuseStep 613273 = 459955) (by norm_num)
theorem B613309 : Blo 542804 613309 := bbase (se 3 (by rfl) ⟨114995, by rfl⟩ : syracuseStep 613309 = 229991) (by norm_num)
theorem B613345 : Blo 542804 613345 := bbase (se 2 (by rfl) ⟨230004, by rfl⟩ : syracuseStep 613345 = 460009) (by norm_num)
theorem B777205 : Blo 542804 777205 := bbase (se 5 (by rfl) ⟨36431, by rfl⟩ : syracuseStep 777205 = 72863) (by norm_num)
theorem B613381 : Blo 542804 613381 := bbase (se 4 (by rfl) ⟨57504, by rfl⟩ : syracuseStep 613381 = 115009) (by norm_num)
theorem B580645 : Blo 542804 580645 := bbase (se 4 (by rfl) ⟨54435, by rfl⟩ : syracuseStep 580645 = 108871) (by norm_num)
theorem B613417 : Blo 542804 613417 := bbase (se 2 (by rfl) ⟨230031, by rfl⟩ : syracuseStep 613417 = 460063) (by norm_num)
theorem B613453 : Blo 542804 613453 := bbase (se 3 (by rfl) ⟨115022, by rfl⟩ : syracuseStep 613453 = 230045) (by norm_num)
theorem B580717 : Blo 542804 580717 := bbase (se 3 (by rfl) ⟨108884, by rfl⟩ : syracuseStep 580717 = 217769) (by norm_num)
theorem B613489 : Blo 542804 613489 := bbase (se 2 (by rfl) ⟨230058, by rfl⟩ : syracuseStep 613489 = 460117) (by norm_num)
theorem B613525 : Blo 542804 613525 := bbase (se 6 (by rfl) ⟨14379, by rfl⟩ : syracuseStep 613525 = 28759) (by norm_num)
theorem B613561 : Blo 542804 613561 := bbase (se 2 (by rfl) ⟨230085, by rfl⟩ : syracuseStep 613561 = 460171) (by norm_num)
theorem B1399997 : Blo 542804 1399997 := bbase (se 3 (by rfl) ⟨262499, by rfl⟩ : syracuseStep 1399997 = 524999) (by norm_num)
theorem B613597 : Blo 542804 613597 := bbase (se 3 (by rfl) ⟨115049, by rfl⟩ : syracuseStep 613597 = 230099) (by norm_num)
theorem B613633 : Blo 542804 613633 := bbase (se 2 (by rfl) ⟨230112, by rfl⟩ : syracuseStep 613633 = 460225) (by norm_num)
theorem B613669 : Blo 542804 613669 := bbase (se 4 (by rfl) ⟨57531, by rfl⟩ : syracuseStep 613669 = 115063) (by norm_num)
theorem B613705 : Blo 542804 613705 := bbase (se 2 (by rfl) ⟨230139, by rfl⟩ : syracuseStep 613705 = 460279) (by norm_num)
theorem B613741 : Blo 542804 613741 := bbase (se 3 (by rfl) ⟨115076, by rfl⟩ : syracuseStep 613741 = 230153) (by norm_num)
theorem B613777 : Blo 542804 613777 := bbase (se 2 (by rfl) ⟨230166, by rfl⟩ : syracuseStep 613777 = 460333) (by norm_num)
theorem B613813 : Blo 542804 613813 := bbase (se 5 (by rfl) ⟨28772, by rfl⟩ : syracuseStep 613813 = 57545) (by norm_num)
theorem B613849 : Blo 542804 613849 := bbase (se 2 (by rfl) ⟨230193, by rfl⟩ : syracuseStep 613849 = 460387) (by norm_num)
theorem B581089 : Blo 542804 581089 := bbase (se 2 (by rfl) ⟨217908, by rfl⟩ : syracuseStep 581089 = 435817) (by norm_num)
theorem B777701 : Blo 542804 777701 := bbase (se 4 (by rfl) ⟨72909, by rfl⟩ : syracuseStep 777701 = 145819) (by norm_num)
theorem B613885 : Blo 542804 613885 := bbase (se 3 (by rfl) ⟨115103, by rfl⟩ : syracuseStep 613885 = 230207) (by norm_num)
theorem B613921 : Blo 542804 613921 := bbase (se 2 (by rfl) ⟨230220, by rfl⟩ : syracuseStep 613921 = 460441) (by norm_num)
theorem B613957 : Blo 542804 613957 := bbase (se 4 (by rfl) ⟨57558, by rfl⟩ : syracuseStep 613957 = 115117) (by norm_num)
theorem B1662565 : Blo 542804 1662565 := bbase (se 4 (by rfl) ⟨155865, by rfl⟩ : syracuseStep 1662565 = 311731) (by norm_num)
theorem B613993 : Blo 542804 613993 := bbase (se 2 (by rfl) ⟨230247, by rfl⟩ : syracuseStep 613993 = 460495) (by norm_num)
theorem B614029 : Blo 542804 614029 := bbase (se 3 (by rfl) ⟨115130, by rfl⟩ : syracuseStep 614029 = 230261) (by norm_num)
theorem B614065 : Blo 542804 614065 := bbase (se 2 (by rfl) ⟨230274, by rfl⟩ : syracuseStep 614065 = 460549) (by norm_num)
theorem B614101 : Blo 542804 614101 := bbase (se 7 (by rfl) ⟨7196, by rfl⟩ : syracuseStep 614101 = 14393) (by norm_num)
theorem B679657 : Blo 542804 679657 := bbase (se 2 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 679657 = 509743) (by norm_num)
theorem B614137 : Blo 542804 614137 := bbase (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) (by norm_num)
theorem B614173 : Blo 542804 614173 := bbase (se 3 (by rfl) ⟨115157, by rfl⟩ : syracuseStep 614173 = 230315) (by norm_num)
theorem B614209 : Blo 542804 614209 := bbase (se 2 (by rfl) ⟨230328, by rfl⟩ : syracuseStep 614209 = 460657) (by norm_num)
theorem B581465 : Blo 542804 581465 := bbase (se 2 (by rfl) ⟨218049, by rfl⟩ : syracuseStep 581465 = 436099) (by norm_num)
theorem B614245 : Blo 542804 614245 := bbase (se 4 (by rfl) ⟨57585, by rfl⟩ : syracuseStep 614245 = 115171) (by norm_num)
theorem B614281 : Blo 542804 614281 := bbase (se 2 (by rfl) ⟨230355, by rfl⟩ : syracuseStep 614281 = 460711) (by norm_num)
theorem B581537 : Blo 542804 581537 := bbase (se 2 (by rfl) ⟨218076, by rfl⟩ : syracuseStep 581537 = 436153) (by norm_num)
theorem B1105829 : Blo 542804 1105829 := bbase (se 4 (by rfl) ⟨103671, by rfl⟩ : syracuseStep 1105829 = 207343) (by norm_num)
theorem B614317 : Blo 542804 614317 := bbase (se 3 (by rfl) ⟨115184, by rfl⟩ : syracuseStep 614317 = 230369) (by norm_num)
theorem B614353 : Blo 542804 614353 := bbase (se 2 (by rfl) ⟨230382, by rfl⟩ : syracuseStep 614353 = 460765) (by norm_num)
theorem B614389 : Blo 542804 614389 := bbase (se 5 (by rfl) ⟨28799, by rfl⟩ : syracuseStep 614389 = 57599) (by norm_num)
theorem B778253 : Blo 542804 778253 := bbase (se 3 (by rfl) ⟨145922, by rfl⟩ : syracuseStep 778253 = 291845) (by norm_num)
theorem B614425 : Blo 542804 614425 := bbase (se 2 (by rfl) ⟨230409, by rfl⟩ : syracuseStep 614425 = 460819) (by norm_num)
theorem B614461 : Blo 542804 614461 := bbase (se 3 (by rfl) ⟨115211, by rfl⟩ : syracuseStep 614461 = 230423) (by norm_num)
theorem B581725 : Blo 542804 581725 := bbase (se 3 (by rfl) ⟨109073, by rfl⟩ : syracuseStep 581725 = 218147) (by norm_num)
theorem B614497 : Blo 542804 614497 := bbase (se 2 (by rfl) ⟨230436, by rfl⟩ : syracuseStep 614497 = 460873) (by norm_num)
theorem B614533 : Blo 542804 614533 := bbase (se 4 (by rfl) ⟨57612, by rfl⟩ : syracuseStep 614533 = 115225) (by norm_num)
theorem B614569 : Blo 542804 614569 := bbase (se 2 (by rfl) ⟨230463, by rfl⟩ : syracuseStep 614569 = 460927) (by norm_num)
theorem B614605 : Blo 542804 614605 := bbase (se 3 (by rfl) ⟨115238, by rfl⟩ : syracuseStep 614605 = 230477) (by norm_num)
theorem B614641 : Blo 542804 614641 := bbase (se 2 (by rfl) ⟨230490, by rfl⟩ : syracuseStep 614641 = 460981) (by norm_num)
theorem B581909 : Blo 542804 581909 := bbase (se 6 (by rfl) ⟨13638, by rfl⟩ : syracuseStep 581909 = 27277) (by norm_num)
theorem B614677 : Blo 542804 614677 := bbase (se 6 (by rfl) ⟨14406, by rfl⟩ : syracuseStep 614677 = 28813) (by norm_num)
theorem B614713 : Blo 542804 614713 := bbase (se 2 (by rfl) ⟨230517, by rfl⟩ : syracuseStep 614713 = 461035) (by norm_num)
theorem B614749 : Blo 542804 614749 := bbase (se 3 (by rfl) ⟨115265, by rfl⟩ : syracuseStep 614749 = 230531) (by norm_num)
theorem B614785 : Blo 542804 614785 := bbase (se 2 (by rfl) ⟨230544, by rfl⟩ : syracuseStep 614785 = 461089) (by norm_num)
theorem B1401229 : Blo 542804 1401229 := bbase (se 3 (by rfl) ⟨262730, by rfl⟩ : syracuseStep 1401229 = 525461) (by norm_num)
theorem B614821 : Blo 542804 614821 := bbase (se 4 (by rfl) ⟨57639, by rfl⟩ : syracuseStep 614821 = 115279) (by norm_num)
theorem B614857 : Blo 542804 614857 := bbase (se 2 (by rfl) ⟨230571, by rfl⟩ : syracuseStep 614857 = 461143) (by norm_num)
theorem B614893 : Blo 542804 614893 := bbase (se 3 (by rfl) ⟨115292, by rfl⟩ : syracuseStep 614893 = 230585) (by norm_num)
theorem B614929 : Blo 542804 614929 := bbase (se 2 (by rfl) ⟨230598, by rfl⟩ : syracuseStep 614929 = 461197) (by norm_num)
theorem B614965 : Blo 542804 614965 := bbase (se 5 (by rfl) ⟨28826, by rfl⟩ : syracuseStep 614965 = 57653) (by norm_num)
theorem B615001 : Blo 542804 615001 := bbase (se 2 (by rfl) ⟨230625, by rfl⟩ : syracuseStep 615001 = 461251) (by norm_num)
theorem B615037 : Blo 542804 615037 := bbase (se 3 (by rfl) ⟨115319, by rfl⟩ : syracuseStep 615037 = 230639) (by norm_num)
theorem B615073 : Blo 542804 615073 := bbase (se 2 (by rfl) ⟨230652, by rfl⟩ : syracuseStep 615073 = 461305) (by norm_num)
theorem B615109 : Blo 542804 615109 := bbase (se 4 (by rfl) ⟨57666, by rfl⟩ : syracuseStep 615109 = 115333) (by norm_num)
theorem B615145 : Blo 542804 615145 := bbase (se 2 (by rfl) ⟨230679, by rfl⟩ : syracuseStep 615145 = 461359) (by norm_num)
theorem B2614133 : Blo 542804 2614133 := bbase (se 5 (by rfl) ⟨122537, by rfl⟩ : syracuseStep 2614133 = 245075) (by norm_num)
theorem B4416373 : Blo 542804 4416373 := bbase (se 5 (by rfl) ⟨207017, by rfl⟩ : syracuseStep 4416373 = 414035) (by norm_num)
theorem B582661 : Blo 542804 582661 := bbase (se 4 (by rfl) ⟨54624, by rfl⟩ : syracuseStep 582661 = 109249) (by norm_num)
theorem B582733 : Blo 542804 582733 := bbase (se 3 (by rfl) ⟨109262, by rfl⟩ : syracuseStep 582733 = 218525) (by norm_num)
theorem B1959029 : Blo 542804 1959029 := bbase (se 5 (by rfl) ⟨91829, by rfl⟩ : syracuseStep 1959029 = 183659) (by norm_num)
theorem B582913 : Blo 542804 582913 := bbase (se 2 (by rfl) ⟨218592, by rfl⟩ : syracuseStep 582913 = 437185) (by norm_num)
theorem B1959173 : Blo 542804 1959173 := bbase (se 4 (by rfl) ⟨183672, by rfl⟩ : syracuseStep 1959173 = 367345) (by norm_num)
theorem B3106133 : Blo 542804 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B550361 : Blo 542804 550361 := bbase (se 2 (by rfl) ⟨206385, by rfl⟩ : syracuseStep 550361 = 412771) (by norm_num)
theorem B1467973 : Blo 542804 1467973 := bbase (se 4 (by rfl) ⟨137622, by rfl⟩ : syracuseStep 1467973 = 275245) (by norm_num)
theorem B1893989 : Blo 542804 1893989 := bbase (se 4 (by rfl) ⟨177561, by rfl⟩ : syracuseStep 1893989 = 355123) (by norm_num)
theorem B1107613 : Blo 542804 1107613 := bbase (se 3 (by rfl) ⟨207677, by rfl⟩ : syracuseStep 1107613 = 415355) (by norm_num)
theorem B583357 : Blo 542804 583357 := bbase (se 3 (by rfl) ⟨109379, by rfl⟩ : syracuseStep 583357 = 218759) (by norm_num)
theorem B4187861 : Blo 542804 4187861 := bbase (se 7 (by rfl) ⟨49076, by rfl⟩ : syracuseStep 4187861 = 98153) (by norm_num)
theorem B1402645 : Blo 542804 1402645 := bbase (se 6 (by rfl) ⟨32874, by rfl⟩ : syracuseStep 1402645 = 65749) (by norm_num)
theorem B583481 : Blo 542804 583481 := bbase (se 2 (by rfl) ⟨218805, by rfl⟩ : syracuseStep 583481 = 437611) (by norm_num)
theorem B7858133 : Blo 542804 7858133 := bbase (se 7 (by rfl) ⟨92087, by rfl⟩ : syracuseStep 7858133 = 184175) (by norm_num)
theorem B5236757 : Blo 542804 5236757 := bbase (se 6 (by rfl) ⟨122736, by rfl⟩ : syracuseStep 5236757 = 245473) (by norm_num)
theorem B3926069 : Blo 542804 3926069 := bbase (se 5 (by rfl) ⟨184034, by rfl⟩ : syracuseStep 3926069 = 368069) (by norm_num)
theorem B583733 : Blo 542804 583733 := bbase (se 5 (by rfl) ⟨27362, by rfl⟩ : syracuseStep 583733 = 54725) (by norm_num)
theorem B551009 : Blo 542804 551009 := bbase (se 2 (by rfl) ⟨206628, by rfl⟩ : syracuseStep 551009 = 413257) (by norm_num)
theorem B2091221 : Blo 542804 2091221 := bbase (se 7 (by rfl) ⟨24506, by rfl⟩ : syracuseStep 2091221 = 49013) (by norm_num)
theorem B2320613 : Blo 542804 2320613 := bbase (se 4 (by rfl) ⟨217557, by rfl⟩ : syracuseStep 2320613 = 435115) (by norm_num)
theorem B1010053 : Blo 542804 1010053 := bbase (se 4 (by rfl) ⟨94692, by rfl⟩ : syracuseStep 1010053 = 189385) (by norm_num)
theorem B747949 : Blo 542804 747949 := bbase (se 3 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 747949 = 280481) (by norm_num)
theorem B1272349 : Blo 542804 1272349 := bbase (se 3 (by rfl) ⟨238565, by rfl⟩ : syracuseStep 1272349 = 477131) (by norm_num)
theorem B1305173 : Blo 542804 1305173 := bbase (se 8 (by rfl) ⟨7647, by rfl⟩ : syracuseStep 1305173 = 15295) (by norm_num)
theorem B2091653 : Blo 542804 2091653 := bbase (se 4 (by rfl) ⟨196092, by rfl⟩ : syracuseStep 2091653 = 392185) (by norm_num)
theorem B1305605 : Blo 542804 1305605 := bbase (se 4 (by rfl) ⟨122400, by rfl⟩ : syracuseStep 1305605 = 244801) (by norm_num)
theorem B551941 : Blo 542804 551941 := bbase (se 4 (by rfl) ⟨51744, by rfl⟩ : syracuseStep 551941 = 103489) (by norm_num)
theorem B814229 : Blo 542804 814229 := bbase (se 6 (by rfl) ⟨19083, by rfl⟩ : syracuseStep 814229 = 38167) (by norm_num)
theorem B1272989 : Blo 542804 1272989 := bbase (se 3 (by rfl) ⟨238685, by rfl⟩ : syracuseStep 1272989 = 477371) (by norm_num)
theorem B814253 : Blo 542804 814253 := bbase (se 3 (by rfl) ⟨152672, by rfl⟩ : syracuseStep 814253 = 305345) (by norm_num)
theorem B814277 : Blo 542804 814277 := bbase (se 4 (by rfl) ⟨76338, by rfl⟩ : syracuseStep 814277 = 152677) (by norm_num)
theorem B2616533 : Blo 542804 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B814301 : Blo 542804 814301 := bbase (se 3 (by rfl) ⟨152681, by rfl⟩ : syracuseStep 814301 = 305363) (by norm_num)
theorem B1961189 : Blo 542804 1961189 := bbase (se 4 (by rfl) ⟨183861, by rfl⟩ : syracuseStep 1961189 = 367723) (by norm_num)
theorem B814325 : Blo 542804 814325 := bbase (se 5 (by rfl) ⟨38171, by rfl⟩ : syracuseStep 814325 = 76343) (by norm_num)
theorem B945413 : Blo 542804 945413 := bbase (se 4 (by rfl) ⟨88632, by rfl⟩ : syracuseStep 945413 = 177265) (by norm_num)
theorem B814349 : Blo 542804 814349 := bbase (se 3 (by rfl) ⟨152690, by rfl⟩ : syracuseStep 814349 = 305381) (by norm_num)
theorem B814373 : Blo 542804 814373 := bbase (se 4 (by rfl) ⟨76347, by rfl⟩ : syracuseStep 814373 = 152695) (by norm_num)
theorem B1240373 : Blo 542804 1240373 := bbase (se 5 (by rfl) ⟨58142, by rfl⟩ : syracuseStep 1240373 = 116285) (by norm_num)
theorem B814397 : Blo 542804 814397 := bbase (se 3 (by rfl) ⟨152699, by rfl⟩ : syracuseStep 814397 = 305399) (by norm_num)
theorem B814421 : Blo 542804 814421 := bbase (se 11 (by rfl) ⟨596, by rfl⟩ : syracuseStep 814421 = 1193) (by norm_num)
theorem B814445 : Blo 542804 814445 := bbase (se 3 (by rfl) ⟨152708, by rfl⟩ : syracuseStep 814445 = 305417) (by norm_num)
theorem B814469 : Blo 542804 814469 := bbase (se 4 (by rfl) ⟨76356, by rfl⟩ : syracuseStep 814469 = 152713) (by norm_num)
theorem B814493 : Blo 542804 814493 := bbase (se 3 (by rfl) ⟨152717, by rfl⟩ : syracuseStep 814493 = 305435) (by norm_num)
theorem B814517 : Blo 542804 814517 := bbase (se 5 (by rfl) ⟨38180, by rfl⟩ : syracuseStep 814517 = 76361) (by norm_num)
theorem B814541 : Blo 542804 814541 := bbase (se 3 (by rfl) ⟨152726, by rfl⟩ : syracuseStep 814541 = 305453) (by norm_num)
theorem B814565 : Blo 542804 814565 := bbase (se 4 (by rfl) ⟨76365, by rfl⟩ : syracuseStep 814565 = 152731) (by norm_num)
theorem B814589 : Blo 542804 814589 := bbase (se 3 (by rfl) ⟨152735, by rfl⟩ : syracuseStep 814589 = 305471) (by norm_num)
theorem B814613 : Blo 542804 814613 := bbase (se 6 (by rfl) ⟨19092, by rfl⟩ : syracuseStep 814613 = 38185) (by norm_num)
theorem B978461 : Blo 542804 978461 := bbase (se 3 (by rfl) ⟨183461, by rfl⟩ : syracuseStep 978461 = 366923) (by norm_num)
theorem B814637 : Blo 542804 814637 := bbase (se 3 (by rfl) ⟨152744, by rfl⟩ : syracuseStep 814637 = 305489) (by norm_num)
theorem B814661 : Blo 542804 814661 := bbase (se 4 (by rfl) ⟨76374, by rfl⟩ : syracuseStep 814661 = 152749) (by norm_num)
theorem B814685 : Blo 542804 814685 := bbase (se 3 (by rfl) ⟨152753, by rfl⟩ : syracuseStep 814685 = 305507) (by norm_num)
theorem B2748005 : Blo 542804 2748005 := bbase (se 4 (by rfl) ⟨257625, by rfl⟩ : syracuseStep 2748005 = 515251) (by norm_num)
theorem B814709 : Blo 542804 814709 := bbase (se 5 (by rfl) ⟨38189, by rfl⟩ : syracuseStep 814709 = 76379) (by norm_num)
theorem B814733 : Blo 542804 814733 := bbase (se 3 (by rfl) ⟨152762, by rfl⟩ : syracuseStep 814733 = 305525) (by norm_num)
theorem B814757 : Blo 542804 814757 := bbase (se 4 (by rfl) ⟨76383, by rfl⟩ : syracuseStep 814757 = 152767) (by norm_num)
theorem B814781 : Blo 542804 814781 := bbase (se 3 (by rfl) ⟨152771, by rfl⟩ : syracuseStep 814781 = 305543) (by norm_num)
theorem B814805 : Blo 542804 814805 := bbase (se 7 (by rfl) ⟨9548, by rfl⟩ : syracuseStep 814805 = 19097) (by norm_num)
theorem B814829 : Blo 542804 814829 := bbase (se 3 (by rfl) ⟨152780, by rfl⟩ : syracuseStep 814829 = 305561) (by norm_num)
theorem B814853 : Blo 542804 814853 := bbase (se 4 (by rfl) ⟨76392, by rfl⟩ : syracuseStep 814853 = 152785) (by norm_num)
theorem B814877 : Blo 542804 814877 := bbase (se 3 (by rfl) ⟨152789, by rfl⟩ : syracuseStep 814877 = 305579) (by norm_num)
theorem B1863461 : Blo 542804 1863461 := bbase (se 4 (by rfl) ⟨174699, by rfl⟩ : syracuseStep 1863461 = 349399) (by norm_num)
theorem B552749 : Blo 542804 552749 := bbase (se 3 (by rfl) ⟨103640, by rfl⟩ : syracuseStep 552749 = 207281) (by norm_num)
theorem B814901 : Blo 542804 814901 := bbase (se 5 (by rfl) ⟨38198, by rfl⟩ : syracuseStep 814901 = 76397) (by norm_num)
theorem B814925 : Blo 542804 814925 := bbase (se 3 (by rfl) ⟨152798, by rfl⟩ : syracuseStep 814925 = 305597) (by norm_num)
theorem B814949 : Blo 542804 814949 := bbase (se 4 (by rfl) ⟨76401, by rfl⟩ : syracuseStep 814949 = 152803) (by norm_num)
theorem B814973 : Blo 542804 814973 := bbase (se 3 (by rfl) ⟨152807, by rfl⟩ : syracuseStep 814973 = 305615) (by norm_num)
theorem B1699717 : Blo 542804 1699717 := bbase (se 4 (by rfl) ⟨159348, by rfl⟩ : syracuseStep 1699717 = 318697) (by norm_num)
theorem B814997 : Blo 542804 814997 := bbase (se 6 (by rfl) ⟨19101, by rfl⟩ : syracuseStep 814997 = 38203) (by norm_num)
theorem B815021 : Blo 542804 815021 := bbase (se 3 (by rfl) ⟨152816, by rfl⟩ : syracuseStep 815021 = 305633) (by norm_num)
theorem B815045 : Blo 542804 815045 := bbase (se 4 (by rfl) ⟨76410, by rfl⟩ : syracuseStep 815045 = 152821) (by norm_num)
theorem B815069 : Blo 542804 815069 := bbase (se 3 (by rfl) ⟨152825, by rfl⟩ : syracuseStep 815069 = 305651) (by norm_num)
theorem B815093 : Blo 542804 815093 := bbase (se 5 (by rfl) ⟨38207, by rfl⟩ : syracuseStep 815093 = 76415) (by norm_num)
theorem B815117 : Blo 542804 815117 := bbase (se 3 (by rfl) ⟨152834, by rfl⟩ : syracuseStep 815117 = 305669) (by norm_num)
theorem B815141 : Blo 542804 815141 := bbase (se 4 (by rfl) ⟨76419, by rfl⟩ : syracuseStep 815141 = 152839) (by norm_num)
theorem B815165 : Blo 542804 815165 := bbase (se 3 (by rfl) ⟨152843, by rfl⟩ : syracuseStep 815165 = 305687) (by norm_num)
theorem B815189 : Blo 542804 815189 := bbase (se 8 (by rfl) ⟨4776, by rfl⟩ : syracuseStep 815189 = 9553) (by norm_num)
theorem B815213 : Blo 542804 815213 := bbase (se 3 (by rfl) ⟨152852, by rfl⟩ : syracuseStep 815213 = 305705) (by norm_num)
theorem B815237 : Blo 542804 815237 := bbase (se 4 (by rfl) ⟨76428, by rfl⟩ : syracuseStep 815237 = 152857) (by norm_num)
theorem B553109 : Blo 542804 553109 := bbase (se 6 (by rfl) ⟨12963, by rfl⟩ : syracuseStep 553109 = 25927) (by norm_num)
theorem B815261 : Blo 542804 815261 := bbase (se 3 (by rfl) ⟨152861, by rfl⟩ : syracuseStep 815261 = 305723) (by norm_num)
theorem B815285 : Blo 542804 815285 := bbase (se 5 (by rfl) ⟨38216, by rfl⟩ : syracuseStep 815285 = 76433) (by norm_num)
theorem B815309 : Blo 542804 815309 := bbase (se 3 (by rfl) ⟨152870, by rfl⟩ : syracuseStep 815309 = 305741) (by norm_num)
theorem B815333 : Blo 542804 815333 := bbase (se 4 (by rfl) ⟨76437, by rfl⟩ : syracuseStep 815333 = 152875) (by norm_num)
theorem B815357 : Blo 542804 815357 := bbase (se 3 (by rfl) ⟨152879, by rfl⟩ : syracuseStep 815357 = 305759) (by norm_num)
theorem B815381 : Blo 542804 815381 := bbase (se 6 (by rfl) ⟨19110, by rfl⟩ : syracuseStep 815381 = 38221) (by norm_num)
theorem B815405 : Blo 542804 815405 := bbase (se 3 (by rfl) ⟨152888, by rfl⟩ : syracuseStep 815405 = 305777) (by norm_num)
theorem B4714805 : Blo 542804 4714805 := bbase (se 5 (by rfl) ⟨221006, by rfl⟩ : syracuseStep 4714805 = 442013) (by norm_num)
theorem B815429 : Blo 542804 815429 := bbase (se 4 (by rfl) ⟨76446, by rfl⟩ : syracuseStep 815429 = 152893) (by norm_num)
theorem B815453 : Blo 542804 815453 := bbase (se 3 (by rfl) ⟨152897, by rfl⟩ : syracuseStep 815453 = 305795) (by norm_num)
theorem B815477 : Blo 542804 815477 := bbase (se 5 (by rfl) ⟨38225, by rfl⟩ : syracuseStep 815477 = 76451) (by norm_num)
theorem B815501 : Blo 542804 815501 := bbase (se 3 (by rfl) ⟨152906, by rfl⟩ : syracuseStep 815501 = 305813) (by norm_num)
theorem B2355605 : Blo 542804 2355605 := bbase (se 6 (by rfl) ⟨55209, by rfl⟩ : syracuseStep 2355605 = 110419) (by norm_num)
theorem B815525 : Blo 542804 815525 := bbase (se 4 (by rfl) ⟨76455, by rfl⟩ : syracuseStep 815525 = 152911) (by norm_num)
theorem B815549 : Blo 542804 815549 := bbase (se 3 (by rfl) ⟨152915, by rfl⟩ : syracuseStep 815549 = 305831) (by norm_num)
theorem B815573 : Blo 542804 815573 := bbase (se 7 (by rfl) ⟨9557, by rfl⟩ : syracuseStep 815573 = 19115) (by norm_num)
theorem B815597 : Blo 542804 815597 := bbase (se 3 (by rfl) ⟨152924, by rfl⟩ : syracuseStep 815597 = 305849) (by norm_num)
theorem B815621 : Blo 542804 815621 := bbase (se 4 (by rfl) ⟨76464, by rfl⟩ : syracuseStep 815621 = 152929) (by norm_num)
theorem B815645 : Blo 542804 815645 := bbase (se 3 (by rfl) ⟨152933, by rfl⟩ : syracuseStep 815645 = 305867) (by norm_num)
theorem B815669 : Blo 542804 815669 := bbase (se 5 (by rfl) ⟨38234, by rfl⟩ : syracuseStep 815669 = 76469) (by norm_num)
theorem B815693 : Blo 542804 815693 := bbase (se 3 (by rfl) ⟨152942, by rfl⟩ : syracuseStep 815693 = 305885) (by norm_num)
theorem B815717 : Blo 542804 815717 := bbase (se 4 (by rfl) ⟨76473, by rfl⟩ : syracuseStep 815717 = 152947) (by norm_num)
theorem B815741 : Blo 542804 815741 := bbase (se 3 (by rfl) ⟨152951, by rfl⟩ : syracuseStep 815741 = 305903) (by norm_num)
theorem B815765 : Blo 542804 815765 := bbase (se 6 (by rfl) ⟨19119, by rfl⟩ : syracuseStep 815765 = 38239) (by norm_num)
theorem B815789 : Blo 542804 815789 := bbase (se 3 (by rfl) ⟨152960, by rfl⟩ : syracuseStep 815789 = 305921) (by norm_num)
theorem B815813 : Blo 542804 815813 := bbase (se 4 (by rfl) ⟨76482, by rfl⟩ : syracuseStep 815813 = 152965) (by norm_num)
theorem B815837 : Blo 542804 815837 := bbase (se 3 (by rfl) ⟨152969, by rfl⟩ : syracuseStep 815837 = 305939) (by norm_num)
theorem B815861 : Blo 542804 815861 := bbase (se 5 (by rfl) ⟨38243, by rfl⟩ : syracuseStep 815861 = 76487) (by norm_num)
theorem B815885 : Blo 542804 815885 := bbase (se 3 (by rfl) ⟨152978, by rfl⟩ : syracuseStep 815885 = 305957) (by norm_num)
theorem B815909 : Blo 542804 815909 := bbase (se 4 (by rfl) ⟨76491, by rfl⟩ : syracuseStep 815909 = 152983) (by norm_num)
theorem B815933 : Blo 542804 815933 := bbase (se 3 (by rfl) ⟨152987, by rfl⟩ : syracuseStep 815933 = 305975) (by norm_num)
theorem B1045333 : Blo 542804 1045333 := bbase (se 9 (by rfl) ⟨3062, by rfl⟩ : syracuseStep 1045333 = 6125) (by norm_num)
theorem B815957 : Blo 542804 815957 := bbase (se 9 (by rfl) ⟨2390, by rfl⟩ : syracuseStep 815957 = 4781) (by norm_num)
theorem B5665621 : Blo 542804 5665621 := bbase (se 9 (by rfl) ⟨16598, by rfl⟩ : syracuseStep 5665621 = 33197) (by norm_num)
theorem B815981 : Blo 542804 815981 := bbase (se 3 (by rfl) ⟨152996, by rfl⟩ : syracuseStep 815981 = 305993) (by norm_num)
theorem B2749301 : Blo 542804 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B816005 : Blo 542804 816005 := bbase (se 4 (by rfl) ⟨76500, by rfl⟩ : syracuseStep 816005 = 153001) (by norm_num)
theorem B816029 : Blo 542804 816029 := bbase (se 3 (by rfl) ⟨153005, by rfl⟩ : syracuseStep 816029 = 306011) (by norm_num)
theorem B816053 : Blo 542804 816053 := bbase (se 5 (by rfl) ⟨38252, by rfl⟩ : syracuseStep 816053 = 76505) (by norm_num)
theorem B816077 : Blo 542804 816077 := bbase (se 3 (by rfl) ⟨153014, by rfl⟩ : syracuseStep 816077 = 306029) (by norm_num)
theorem B4125653 : Blo 542804 4125653 := bbase (se 7 (by rfl) ⟨48347, by rfl⟩ : syracuseStep 4125653 = 96695) (by norm_num)
theorem B816101 : Blo 542804 816101 := bbase (se 4 (by rfl) ⟨76509, by rfl⟩ : syracuseStep 816101 = 153019) (by norm_num)
theorem B553969 : Blo 542804 553969 := bbase (se 2 (by rfl) ⟨207738, by rfl⟩ : syracuseStep 553969 = 415477) (by norm_num)
theorem B816125 : Blo 542804 816125 := bbase (se 3 (by rfl) ⟨153023, by rfl⟩ : syracuseStep 816125 = 306047) (by norm_num)
theorem B816149 : Blo 542804 816149 := bbase (se 6 (by rfl) ⟨19128, by rfl⟩ : syracuseStep 816149 = 38257) (by norm_num)
theorem B816173 : Blo 542804 816173 := bbase (se 3 (by rfl) ⟨153032, by rfl⟩ : syracuseStep 816173 = 306065) (by norm_num)
theorem B816197 : Blo 542804 816197 := bbase (se 4 (by rfl) ⟨76518, by rfl⟩ : syracuseStep 816197 = 153037) (by norm_num)
theorem B816221 : Blo 542804 816221 := bbase (se 3 (by rfl) ⟨153041, by rfl⟩ : syracuseStep 816221 = 306083) (by norm_num)
theorem B816245 : Blo 542804 816245 := bbase (se 5 (by rfl) ⟨38261, by rfl⟩ : syracuseStep 816245 = 76523) (by norm_num)
theorem B816269 : Blo 542804 816269 := bbase (se 3 (by rfl) ⟨153050, by rfl⟩ : syracuseStep 816269 = 306101) (by norm_num)
theorem B816293 : Blo 542804 816293 := bbase (se 4 (by rfl) ⟨76527, by rfl⟩ : syracuseStep 816293 = 153055) (by norm_num)
theorem B816317 : Blo 542804 816317 := bbase (se 3 (by rfl) ⟨153059, by rfl⟩ : syracuseStep 816317 = 306119) (by norm_num)
theorem B816341 : Blo 542804 816341 := bbase (se 7 (by rfl) ⟨9566, by rfl⟩ : syracuseStep 816341 = 19133) (by norm_num)
theorem B1832165 : Blo 542804 1832165 := bbase (se 4 (by rfl) ⟨171765, by rfl⟩ : syracuseStep 1832165 = 343531) (by norm_num)
theorem B816365 : Blo 542804 816365 := bbase (se 3 (by rfl) ⟨153068, by rfl⟩ : syracuseStep 816365 = 306137) (by norm_num)
theorem B980221 : Blo 542804 980221 := bbase (se 3 (by rfl) ⟨183791, by rfl⟩ : syracuseStep 980221 = 367583) (by norm_num)
theorem B816389 : Blo 542804 816389 := bbase (se 4 (by rfl) ⟨76536, by rfl⟩ : syracuseStep 816389 = 153073) (by norm_num)
theorem B816413 : Blo 542804 816413 := bbase (se 3 (by rfl) ⟨153077, by rfl⟩ : syracuseStep 816413 = 306155) (by norm_num)
theorem B816437 : Blo 542804 816437 := bbase (se 5 (by rfl) ⟨38270, by rfl⟩ : syracuseStep 816437 = 76541) (by norm_num)
theorem B816461 : Blo 542804 816461 := bbase (se 3 (by rfl) ⟨153086, by rfl⟩ : syracuseStep 816461 = 306173) (by norm_num)
theorem B816485 : Blo 542804 816485 := bbase (se 4 (by rfl) ⟨76545, by rfl⟩ : syracuseStep 816485 = 153091) (by norm_num)
theorem B816509 : Blo 542804 816509 := bbase (se 3 (by rfl) ⟨153095, by rfl⟩ : syracuseStep 816509 = 306191) (by norm_num)
theorem B980357 : Blo 542804 980357 := bbase (se 4 (by rfl) ⟨91908, by rfl⟩ : syracuseStep 980357 = 183817) (by norm_num)
theorem B816533 : Blo 542804 816533 := bbase (se 6 (by rfl) ⟨19137, by rfl⟩ : syracuseStep 816533 = 38275) (by norm_num)
theorem B2061733 : Blo 542804 2061733 := bbase (se 4 (by rfl) ⟨193287, by rfl⟩ : syracuseStep 2061733 = 386575) (by norm_num)
theorem B816557 : Blo 542804 816557 := bbase (se 3 (by rfl) ⟨153104, by rfl⟩ : syracuseStep 816557 = 306209) (by norm_num)
theorem B816581 : Blo 542804 816581 := bbase (se 4 (by rfl) ⟨76554, by rfl⟩ : syracuseStep 816581 = 153109) (by norm_num)
theorem B980437 : Blo 542804 980437 := bbase (se 7 (by rfl) ⟨11489, by rfl⟩ : syracuseStep 980437 = 22979) (by norm_num)
theorem B816605 : Blo 542804 816605 := bbase (se 3 (by rfl) ⟨153113, by rfl⟩ : syracuseStep 816605 = 306227) (by norm_num)
theorem B816629 : Blo 542804 816629 := bbase (se 5 (by rfl) ⟨38279, by rfl⟩ : syracuseStep 816629 = 76559) (by norm_num)
theorem B816653 : Blo 542804 816653 := bbase (se 3 (by rfl) ⟨153122, by rfl⟩ : syracuseStep 816653 = 306245) (by norm_num)
theorem B652817 : Blo 542804 652817 := bbase (se 2 (by rfl) ⟨244806, by rfl⟩ : syracuseStep 652817 = 489613) (by norm_num)
theorem B1177109 : Blo 542804 1177109 := bbase (se 6 (by rfl) ⟨27588, by rfl⟩ : syracuseStep 1177109 = 55177) (by norm_num)
theorem B816677 : Blo 542804 816677 := bbase (se 4 (by rfl) ⟨76563, by rfl⟩ : syracuseStep 816677 = 153127) (by norm_num)
theorem B816701 : Blo 542804 816701 := bbase (se 3 (by rfl) ⟨153131, by rfl⟩ : syracuseStep 816701 = 306263) (by norm_num)
theorem B652865 : Blo 542804 652865 := bbase (se 2 (by rfl) ⟨244824, by rfl⟩ : syracuseStep 652865 = 489649) (by norm_num)
theorem B816725 : Blo 542804 816725 := bbase (se 8 (by rfl) ⟨4785, by rfl⟩ : syracuseStep 816725 = 9571) (by norm_num)
theorem B816749 : Blo 542804 816749 := bbase (se 3 (by rfl) ⟨153140, by rfl⟩ : syracuseStep 816749 = 306281) (by norm_num)
theorem B816773 : Blo 542804 816773 := bbase (se 4 (by rfl) ⟨76572, by rfl⟩ : syracuseStep 816773 = 153145) (by norm_num)
theorem B620177 : Blo 542804 620177 := bbase (se 2 (by rfl) ⟨232566, by rfl⟩ : syracuseStep 620177 = 465133) (by norm_num)
theorem B1832597 : Blo 542804 1832597 := bbase (se 6 (by rfl) ⟨42951, by rfl⟩ : syracuseStep 1832597 = 85903) (by norm_num)
theorem B816797 : Blo 542804 816797 := bbase (se 3 (by rfl) ⟨153149, by rfl⟩ : syracuseStep 816797 = 306299) (by norm_num)
theorem B652961 : Blo 542804 652961 := bbase (se 2 (by rfl) ⟨244860, by rfl⟩ : syracuseStep 652961 = 489721) (by norm_num)
theorem B816821 : Blo 542804 816821 := bbase (se 5 (by rfl) ⟨38288, by rfl⟩ : syracuseStep 816821 = 76577) (by norm_num)
theorem B816845 : Blo 542804 816845 := bbase (se 3 (by rfl) ⟨153158, by rfl⟩ : syracuseStep 816845 = 306317) (by norm_num)
theorem B2062037 : Blo 542804 2062037 := bbase (se 7 (by rfl) ⟨24164, by rfl⟩ : syracuseStep 2062037 = 48329) (by norm_num)
theorem B816869 : Blo 542804 816869 := bbase (se 4 (by rfl) ⟨76581, by rfl⟩ : syracuseStep 816869 = 153163) (by norm_num)
theorem B816893 : Blo 542804 816893 := bbase (se 3 (by rfl) ⟨153167, by rfl⟩ : syracuseStep 816893 = 306335) (by norm_num)
theorem B816917 : Blo 542804 816917 := bbase (se 6 (by rfl) ⟨19146, by rfl⟩ : syracuseStep 816917 = 38293) (by norm_num)
theorem B1275685 : Blo 542804 1275685 := bbase (se 4 (by rfl) ⟨119595, by rfl⟩ : syracuseStep 1275685 = 239191) (by norm_num)
theorem B816941 : Blo 542804 816941 := bbase (se 3 (by rfl) ⟨153176, by rfl⟩ : syracuseStep 816941 = 306353) (by norm_num)
theorem B653125 : Blo 542804 653125 := bbase (se 4 (by rfl) ⟨61230, by rfl⟩ : syracuseStep 653125 = 122461) (by norm_num)
theorem B816965 : Blo 542804 816965 := bbase (se 4 (by rfl) ⟨76590, by rfl⟩ : syracuseStep 816965 = 153181) (by norm_num)
theorem B1242965 : Blo 542804 1242965 := bbase (se 9 (by rfl) ⟨3641, by rfl⟩ : syracuseStep 1242965 = 7283) (by norm_num)
theorem B816989 : Blo 542804 816989 := bbase (se 3 (by rfl) ⟨153185, by rfl⟩ : syracuseStep 816989 = 306371) (by norm_num)
theorem B817013 : Blo 542804 817013 := bbase (se 5 (by rfl) ⟨38297, by rfl⟩ : syracuseStep 817013 = 76595) (by norm_num)
theorem B817037 : Blo 542804 817037 := bbase (se 3 (by rfl) ⟨153194, by rfl⟩ : syracuseStep 817037 = 306389) (by norm_num)
theorem B817061 : Blo 542804 817061 := bbase (se 4 (by rfl) ⟨76599, by rfl⟩ : syracuseStep 817061 = 153199) (by norm_num)
theorem B817085 : Blo 542804 817085 := bbase (se 3 (by rfl) ⟨153203, by rfl⟩ : syracuseStep 817085 = 306407) (by norm_num)
theorem B817109 : Blo 542804 817109 := bbase (se 7 (by rfl) ⟨9575, by rfl⟩ : syracuseStep 817109 = 19151) (by norm_num)
theorem B817133 : Blo 542804 817133 := bbase (se 3 (by rfl) ⟨153212, by rfl⟩ : syracuseStep 817133 = 306425) (by norm_num)
theorem B1374205 : Blo 542804 1374205 := bbase (se 3 (by rfl) ⟨257663, by rfl⟩ : syracuseStep 1374205 = 515327) (by norm_num)
theorem B817157 : Blo 542804 817157 := bbase (se 4 (by rfl) ⟨76608, by rfl⟩ : syracuseStep 817157 = 153217) (by norm_num)
theorem B653341 : Blo 542804 653341 := bbase (se 3 (by rfl) ⟨122501, by rfl⟩ : syracuseStep 653341 = 245003) (by norm_num)
theorem B817181 : Blo 542804 817181 := bbase (se 3 (by rfl) ⟨153221, by rfl⟩ : syracuseStep 817181 = 306443) (by norm_num)
theorem B817205 : Blo 542804 817205 := bbase (se 5 (by rfl) ⟨38306, by rfl⟩ : syracuseStep 817205 = 76613) (by norm_num)
theorem B1833029 : Blo 542804 1833029 := bbase (se 4 (by rfl) ⟨171846, by rfl⟩ : syracuseStep 1833029 = 343693) (by norm_num)
theorem B817229 : Blo 542804 817229 := bbase (se 3 (by rfl) ⟨153230, by rfl⟩ : syracuseStep 817229 = 306461) (by norm_num)
theorem B817253 : Blo 542804 817253 := bbase (se 4 (by rfl) ⟨76617, by rfl⟩ : syracuseStep 817253 = 153235) (by norm_num)
theorem B1374317 : Blo 542804 1374317 := bbase (se 3 (by rfl) ⟨257684, by rfl⟩ : syracuseStep 1374317 = 515369) (by norm_num)
theorem B817277 : Blo 542804 817277 := bbase (se 3 (by rfl) ⟨153239, by rfl⟩ : syracuseStep 817277 = 306479) (by norm_num)
theorem B2750597 : Blo 542804 2750597 := bbase (se 4 (by rfl) ⟨257868, by rfl⟩ : syracuseStep 2750597 = 515737) (by norm_num)
theorem B817301 : Blo 542804 817301 := bbase (se 6 (by rfl) ⟨19155, by rfl⟩ : syracuseStep 817301 = 38311) (by norm_num)
theorem B2324645 : Blo 542804 2324645 := bbase (se 4 (by rfl) ⟨217935, by rfl⟩ : syracuseStep 2324645 = 435871) (by norm_num)
theorem B817325 : Blo 542804 817325 := bbase (se 3 (by rfl) ⟨153248, by rfl⟩ : syracuseStep 817325 = 306497) (by norm_num)
theorem B653509 : Blo 542804 653509 := bbase (se 4 (by rfl) ⟨61266, by rfl⟩ : syracuseStep 653509 = 122533) (by norm_num)
theorem B817349 : Blo 542804 817349 := bbase (se 4 (by rfl) ⟨76626, by rfl⟩ : syracuseStep 817349 = 153253) (by norm_num)
theorem B1964245 : Blo 542804 1964245 := bbase (se 7 (by rfl) ⟨23018, by rfl⟩ : syracuseStep 1964245 = 46037) (by norm_num)
theorem B817373 : Blo 542804 817373 := bbase (se 3 (by rfl) ⟨153257, by rfl⟩ : syracuseStep 817373 = 306515) (by norm_num)
theorem B817397 : Blo 542804 817397 := bbase (se 5 (by rfl) ⟨38315, by rfl⟩ : syracuseStep 817397 = 76631) (by norm_num)
theorem B817421 : Blo 542804 817421 := bbase (se 3 (by rfl) ⟨153266, by rfl⟩ : syracuseStep 817421 = 306533) (by norm_num)
theorem B620821 : Blo 542804 620821 := bbase (se 6 (by rfl) ⟨14550, by rfl⟩ : syracuseStep 620821 = 29101) (by norm_num)
theorem B817445 : Blo 542804 817445 := bbase (se 4 (by rfl) ⟨76635, by rfl⟩ : syracuseStep 817445 = 153271) (by norm_num)
theorem B1374509 : Blo 542804 1374509 := bbase (se 3 (by rfl) ⟨257720, by rfl⟩ : syracuseStep 1374509 = 515441) (by norm_num)
theorem B817469 : Blo 542804 817469 := bbase (se 3 (by rfl) ⟨153275, by rfl⟩ : syracuseStep 817469 = 306551) (by norm_num)
theorem B1308997 : Blo 542804 1308997 := bbase (se 4 (by rfl) ⟨122718, by rfl⟩ : syracuseStep 1308997 = 245437) (by norm_num)
theorem B817493 : Blo 542804 817493 := bbase (se 10 (by rfl) ⟨1197, by rfl⟩ : syracuseStep 817493 = 2395) (by norm_num)
theorem B817517 : Blo 542804 817517 := bbase (se 3 (by rfl) ⟨153284, by rfl⟩ : syracuseStep 817517 = 306569) (by norm_num)
theorem B1964405 : Blo 542804 1964405 := bbase (se 5 (by rfl) ⟨92081, by rfl⟩ : syracuseStep 1964405 = 184163) (by norm_num)
theorem B817541 : Blo 542804 817541 := bbase (se 4 (by rfl) ⟨76644, by rfl⟩ : syracuseStep 817541 = 153289) (by norm_num)
theorem B817565 : Blo 542804 817565 := bbase (se 3 (by rfl) ⟨153293, by rfl⟩ : syracuseStep 817565 = 306587) (by norm_num)
theorem B817589 : Blo 542804 817589 := bbase (se 5 (by rfl) ⟨38324, by rfl⟩ : syracuseStep 817589 = 76649) (by norm_num)
theorem B817613 : Blo 542804 817613 := bbase (se 3 (by rfl) ⟨153302, by rfl⟩ : syracuseStep 817613 = 306605) (by norm_num)
theorem B817637 : Blo 542804 817637 := bbase (se 4 (by rfl) ⟨76653, by rfl⟩ : syracuseStep 817637 = 153307) (by norm_num)
theorem B588269 : Blo 542804 588269 := bbase (se 3 (by rfl) ⟨110300, by rfl⟩ : syracuseStep 588269 = 220601) (by norm_num)
theorem B1833461 : Blo 542804 1833461 := bbase (se 5 (by rfl) ⟨85943, by rfl⟩ : syracuseStep 1833461 = 171887) (by norm_num)
theorem B817661 : Blo 542804 817661 := bbase (se 3 (by rfl) ⟨153311, by rfl⟩ : syracuseStep 817661 = 306623) (by norm_num)
theorem B817685 : Blo 542804 817685 := bbase (se 6 (by rfl) ⟨19164, by rfl⟩ : syracuseStep 817685 = 38329) (by norm_num)
theorem B981533 : Blo 542804 981533 := bbase (se 3 (by rfl) ⟨184037, by rfl⟩ : syracuseStep 981533 = 368075) (by norm_num)
theorem B817709 : Blo 542804 817709 := bbase (se 3 (by rfl) ⟨153320, by rfl⟩ : syracuseStep 817709 = 306641) (by norm_num)
theorem B817733 : Blo 542804 817733 := bbase (se 4 (by rfl) ⟨76662, by rfl⟩ : syracuseStep 817733 = 153325) (by norm_num)
theorem B1342037 : Blo 542804 1342037 := bbase (se 8 (by rfl) ⟨7863, by rfl⟩ : syracuseStep 1342037 = 15727) (by norm_num)
theorem B817757 : Blo 542804 817757 := bbase (se 3 (by rfl) ⟨153329, by rfl⟩ : syracuseStep 817757 = 306659) (by norm_num)
theorem B916069 : Blo 542804 916069 := bbase (se 4 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 916069 = 171763) (by norm_num)
theorem B817781 : Blo 542804 817781 := bbase (se 5 (by rfl) ⟨38333, by rfl⟩ : syracuseStep 817781 = 76667) (by norm_num)
theorem B1374853 : Blo 542804 1374853 := bbase (se 4 (by rfl) ⟨128892, by rfl⟩ : syracuseStep 1374853 = 257785) (by norm_num)
theorem B817805 : Blo 542804 817805 := bbase (se 3 (by rfl) ⟨153338, by rfl⟩ : syracuseStep 817805 = 306677) (by norm_num)
theorem B817829 : Blo 542804 817829 := bbase (se 4 (by rfl) ⟨76671, by rfl⟩ : syracuseStep 817829 = 153343) (by norm_num)
theorem B916157 : Blo 542804 916157 := bbase (se 3 (by rfl) ⟨171779, by rfl⟩ : syracuseStep 916157 = 343559) (by norm_num)
theorem B817853 : Blo 542804 817853 := bbase (se 3 (by rfl) ⟨153347, by rfl⟩ : syracuseStep 817853 = 306695) (by norm_num)
theorem B654037 : Blo 542804 654037 := bbase (se 7 (by rfl) ⟨7664, by rfl⟩ : syracuseStep 654037 = 15329) (by norm_num)
theorem B817877 : Blo 542804 817877 := bbase (se 7 (by rfl) ⟨9584, by rfl⟩ : syracuseStep 817877 = 19169) (by norm_num)
theorem B1571557 : Blo 542804 1571557 := bbase (se 4 (by rfl) ⟨147333, by rfl⟩ : syracuseStep 1571557 = 294667) (by norm_num)
theorem B1309421 : Blo 542804 1309421 := bbase (se 3 (by rfl) ⟨245516, by rfl⟩ : syracuseStep 1309421 = 491033) (by norm_num)
theorem B817901 : Blo 542804 817901 := bbase (se 3 (by rfl) ⟨153356, by rfl⟩ : syracuseStep 817901 = 306713) (by norm_num)
theorem B1374965 : Blo 542804 1374965 := bbase (se 5 (by rfl) ⟨64451, by rfl⟩ : syracuseStep 1374965 = 128903) (by norm_num)
theorem B817925 : Blo 542804 817925 := bbase (se 4 (by rfl) ⟨76680, by rfl⟩ : syracuseStep 817925 = 153361) (by norm_num)
theorem B817949 : Blo 542804 817949 := bbase (se 3 (by rfl) ⟨153365, by rfl⟩ : syracuseStep 817949 = 306731) (by norm_num)
theorem B817973 : Blo 542804 817973 := bbase (se 5 (by rfl) ⟨38342, by rfl⟩ : syracuseStep 817973 = 76685) (by norm_num)
theorem B916285 : Blo 542804 916285 := bbase (se 3 (by rfl) ⟨171803, by rfl⟩ : syracuseStep 916285 = 343607) (by norm_num)
theorem B981821 : Blo 542804 981821 := bbase (se 3 (by rfl) ⟨184091, by rfl⟩ : syracuseStep 981821 = 368183) (by norm_num)
theorem B817997 : Blo 542804 817997 := bbase (se 3 (by rfl) ⟨153374, by rfl⟩ : syracuseStep 817997 = 306749) (by norm_num)
theorem B818021 : Blo 542804 818021 := bbase (se 4 (by rfl) ⟨76689, by rfl⟩ : syracuseStep 818021 = 153379) (by norm_num)
theorem B818045 : Blo 542804 818045 := bbase (se 3 (by rfl) ⟨153383, by rfl⟩ : syracuseStep 818045 = 306767) (by norm_num)
theorem B916373 : Blo 542804 916373 := bbase (se 6 (by rfl) ⟨21477, by rfl⟩ : syracuseStep 916373 = 42955) (by norm_num)
theorem B818069 : Blo 542804 818069 := bbase (se 6 (by rfl) ⟨19173, by rfl⟩ : syracuseStep 818069 = 38347) (by norm_num)
theorem B1833893 : Blo 542804 1833893 := bbase (se 4 (by rfl) ⟨171927, by rfl⟩ : syracuseStep 1833893 = 343855) (by norm_num)
theorem B818093 : Blo 542804 818093 := bbase (se 3 (by rfl) ⟨153392, by rfl⟩ : syracuseStep 818093 = 306785) (by norm_num)
theorem B1375157 : Blo 542804 1375157 := bbase (se 5 (by rfl) ⟨64460, by rfl⟩ : syracuseStep 1375157 = 128921) (by norm_num)
theorem B687037 : Blo 542804 687037 := bbase (se 3 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 687037 = 257639) (by norm_num)
theorem B818117 : Blo 542804 818117 := bbase (se 4 (by rfl) ⟨76698, by rfl⟩ : syracuseStep 818117 = 153397) (by norm_num)
theorem B818141 : Blo 542804 818141 := bbase (se 3 (by rfl) ⟨153401, by rfl⟩ : syracuseStep 818141 = 306803) (by norm_num)
theorem B818165 : Blo 542804 818165 := bbase (se 5 (by rfl) ⟨38351, by rfl⟩ : syracuseStep 818165 = 76703) (by norm_num)
theorem B1309709 : Blo 542804 1309709 := bbase (se 3 (by rfl) ⟨245570, by rfl⟩ : syracuseStep 1309709 = 491141) (by norm_num)
theorem B818189 : Blo 542804 818189 := bbase (se 3 (by rfl) ⟨153410, by rfl⟩ : syracuseStep 818189 = 306821) (by norm_num)
theorem B916501 : Blo 542804 916501 := bbase (se 6 (by rfl) ⟨21480, by rfl⟩ : syracuseStep 916501 = 42961) (by norm_num)
theorem B982037 : Blo 542804 982037 := bbase (se 6 (by rfl) ⟨23016, by rfl⟩ : syracuseStep 982037 = 46033) (by norm_num)
theorem B687133 : Blo 542804 687133 := bbase (se 3 (by rfl) ⟨128837, by rfl⟩ : syracuseStep 687133 = 257675) (by norm_num)
theorem B818213 : Blo 542804 818213 := bbase (se 4 (by rfl) ⟨76707, by rfl⟩ : syracuseStep 818213 = 153415) (by norm_num)
theorem B818237 : Blo 542804 818237 := bbase (se 3 (by rfl) ⟨153419, by rfl⟩ : syracuseStep 818237 = 306839) (by norm_num)
theorem B818261 : Blo 542804 818261 := bbase (se 8 (by rfl) ⟨4794, by rfl⟩ : syracuseStep 818261 = 9589) (by norm_num)
theorem B916589 : Blo 542804 916589 := bbase (se 3 (by rfl) ⟨171860, by rfl⟩ : syracuseStep 916589 = 343721) (by norm_num)
theorem B818285 : Blo 542804 818285 := bbase (se 3 (by rfl) ⟨153428, by rfl⟩ : syracuseStep 818285 = 306857) (by norm_num)
theorem B818309 : Blo 542804 818309 := bbase (se 4 (by rfl) ⟨76716, by rfl⟩ : syracuseStep 818309 = 153433) (by norm_num)
theorem B818333 : Blo 542804 818333 := bbase (se 3 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 818333 = 306875) (by norm_num)
theorem B818357 : Blo 542804 818357 := bbase (se 5 (by rfl) ⟨38360, by rfl⟩ : syracuseStep 818357 = 76721) (by norm_num)
theorem B687305 : Blo 542804 687305 := bbase (se 2 (by rfl) ⟨257739, by rfl⟩ : syracuseStep 687305 = 515479) (by norm_num)
theorem B818381 : Blo 542804 818381 := bbase (se 3 (by rfl) ⟨153446, by rfl⟩ : syracuseStep 818381 = 306893) (by norm_num)
theorem B818405 : Blo 542804 818405 := bbase (se 4 (by rfl) ⟨76725, by rfl⟩ : syracuseStep 818405 = 153451) (by norm_num)
theorem B2489573 : Blo 542804 2489573 := bbase (se 4 (by rfl) ⟨233397, by rfl⟩ : syracuseStep 2489573 = 466795) (by norm_num)
theorem B916717 : Blo 542804 916717 := bbase (se 3 (by rfl) ⟨171884, by rfl⟩ : syracuseStep 916717 = 343769) (by norm_num)
theorem B818429 : Blo 542804 818429 := bbase (se 3 (by rfl) ⟨153455, by rfl⟩ : syracuseStep 818429 = 306911) (by norm_num)
theorem B687361 : Blo 542804 687361 := bbase (se 2 (by rfl) ⟨257760, by rfl⟩ : syracuseStep 687361 = 515521) (by norm_num)
theorem B1375501 : Blo 542804 1375501 := bbase (se 3 (by rfl) ⟨257906, by rfl⟩ : syracuseStep 1375501 = 515813) (by norm_num)
theorem B818453 : Blo 542804 818453 := bbase (se 6 (by rfl) ⟨19182, by rfl⟩ : syracuseStep 818453 = 38365) (by norm_num)
theorem B818477 : Blo 542804 818477 := bbase (se 3 (by rfl) ⟨153464, by rfl⟩ : syracuseStep 818477 = 306929) (by norm_num)
theorem B916805 : Blo 542804 916805 := bbase (se 4 (by rfl) ⟨85950, by rfl⟩ : syracuseStep 916805 = 171901) (by norm_num)
theorem B818501 : Blo 542804 818501 := bbase (se 4 (by rfl) ⟨76734, by rfl⟩ : syracuseStep 818501 = 153469) (by norm_num)
theorem B1834325 : Blo 542804 1834325 := bbase (se 11 (by rfl) ⟨1343, by rfl⟩ : syracuseStep 1834325 = 2687) (by norm_num)
theorem B818525 : Blo 542804 818525 := bbase (se 3 (by rfl) ⟨153473, by rfl⟩ : syracuseStep 818525 = 306947) (by norm_num)
theorem B687457 : Blo 542804 687457 := bbase (se 2 (by rfl) ⟨257796, by rfl⟩ : syracuseStep 687457 = 515593) (by norm_num)
theorem B818549 : Blo 542804 818549 := bbase (se 5 (by rfl) ⟨38369, by rfl⟩ : syracuseStep 818549 = 76739) (by norm_num)
theorem B1375613 : Blo 542804 1375613 := bbase (se 3 (by rfl) ⟨257927, by rfl⟩ : syracuseStep 1375613 = 515855) (by norm_num)
theorem B818573 : Blo 542804 818573 := bbase (se 3 (by rfl) ⟨153482, by rfl⟩ : syracuseStep 818573 = 306965) (by norm_num)
theorem B2751893 : Blo 542804 2751893 := bbase (se 6 (by rfl) ⟨64497, by rfl⟩ : syracuseStep 2751893 = 128995) (by norm_num)
theorem B818597 : Blo 542804 818597 := bbase (se 4 (by rfl) ⟨76743, by rfl⟩ : syracuseStep 818597 = 153487) (by norm_num)
theorem B818621 : Blo 542804 818621 := bbase (se 3 (by rfl) ⟨153491, by rfl⟩ : syracuseStep 818621 = 306983) (by norm_num)
theorem B916933 : Blo 542804 916933 := bbase (se 4 (by rfl) ⟨85962, by rfl⟩ : syracuseStep 916933 = 171925) (by norm_num)
theorem B818645 : Blo 542804 818645 := bbase (se 7 (by rfl) ⟨9593, by rfl⟩ : syracuseStep 818645 = 19187) (by norm_num)
theorem B818669 : Blo 542804 818669 := bbase (se 3 (by rfl) ⟨153500, by rfl⟩ : syracuseStep 818669 = 307001) (by norm_num)
theorem B818693 : Blo 542804 818693 := bbase (se 4 (by rfl) ⟨76752, by rfl⟩ : syracuseStep 818693 = 153505) (by norm_num)
theorem B687629 : Blo 542804 687629 := bbase (se 3 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 687629 = 257861) (by norm_num)
theorem B917021 : Blo 542804 917021 := bbase (se 3 (by rfl) ⟨171941, by rfl⟩ : syracuseStep 917021 = 343883) (by norm_num)
theorem B818717 : Blo 542804 818717 := bbase (se 3 (by rfl) ⟨153509, by rfl⟩ : syracuseStep 818717 = 307019) (by norm_num)
theorem B818741 : Blo 542804 818741 := bbase (se 5 (by rfl) ⟨38378, by rfl⟩ : syracuseStep 818741 = 76757) (by norm_num)
theorem B1375805 : Blo 542804 1375805 := bbase (se 3 (by rfl) ⟨257963, by rfl⟩ : syracuseStep 1375805 = 515927) (by norm_num)
theorem B687685 : Blo 542804 687685 := bbase (se 4 (by rfl) ⟨64470, by rfl⟩ : syracuseStep 687685 = 128941) (by norm_num)
theorem B818765 : Blo 542804 818765 := bbase (se 3 (by rfl) ⟨153518, by rfl⟩ : syracuseStep 818765 = 307037) (by norm_num)
theorem B1867349 : Blo 542804 1867349 := bbase (se 8 (by rfl) ⟨10941, by rfl⟩ : syracuseStep 1867349 = 21883) (by norm_num)
theorem B818789 : Blo 542804 818789 := bbase (se 4 (by rfl) ⟨76761, by rfl⟩ : syracuseStep 818789 = 153523) (by norm_num)
theorem B1638005 : Blo 542804 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B818813 : Blo 542804 818813 := bbase (se 3 (by rfl) ⟨153527, by rfl⟩ : syracuseStep 818813 = 307055) (by norm_num)
theorem B818837 : Blo 542804 818837 := bbase (se 6 (by rfl) ⟨19191, by rfl⟩ : syracuseStep 818837 = 38383) (by norm_num)
theorem B917149 : Blo 542804 917149 := bbase (se 3 (by rfl) ⟨171965, by rfl⟩ : syracuseStep 917149 = 343931) (by norm_num)
theorem B687781 : Blo 542804 687781 := bbase (se 4 (by rfl) ⟨64479, by rfl⟩ : syracuseStep 687781 = 128959) (by norm_num)
theorem B818861 : Blo 542804 818861 := bbase (se 3 (by rfl) ⟨153536, by rfl⟩ : syracuseStep 818861 = 307073) (by norm_num)
theorem B818885 : Blo 542804 818885 := bbase (se 4 (by rfl) ⟨76770, by rfl⟩ : syracuseStep 818885 = 153541) (by norm_num)
theorem B818909 : Blo 542804 818909 := bbase (se 3 (by rfl) ⟨153545, by rfl⟩ : syracuseStep 818909 = 307091) (by norm_num)
theorem B917237 : Blo 542804 917237 := bbase (se 5 (by rfl) ⟨42995, by rfl⟩ : syracuseStep 917237 = 85991) (by norm_num)
theorem B818933 : Blo 542804 818933 := bbase (se 5 (by rfl) ⟨38387, by rfl⟩ : syracuseStep 818933 = 76775) (by norm_num)
theorem B1834757 : Blo 542804 1834757 := bbase (se 4 (by rfl) ⟨172008, by rfl⟩ : syracuseStep 1834757 = 344017) (by norm_num)
theorem B818957 : Blo 542804 818957 := bbase (se 3 (by rfl) ⟨153554, by rfl⟩ : syracuseStep 818957 = 307109) (by norm_num)
theorem B2064149 : Blo 542804 2064149 := bbase (se 6 (by rfl) ⟨48378, by rfl⟩ : syracuseStep 2064149 = 96757) (by norm_num)
theorem B655133 : Blo 542804 655133 := bbase (se 3 (by rfl) ⟨122837, by rfl⟩ : syracuseStep 655133 = 245675) (by norm_num)
theorem B1703717 : Blo 542804 1703717 := bbase (se 4 (by rfl) ⟨159723, by rfl⟩ : syracuseStep 1703717 = 319447) (by norm_num)
theorem B818981 : Blo 542804 818981 := bbase (se 4 (by rfl) ⟨76779, by rfl⟩ : syracuseStep 818981 = 153559) (by norm_num)
theorem B819005 : Blo 542804 819005 := bbase (se 3 (by rfl) ⟨153563, by rfl⟩ : syracuseStep 819005 = 307127) (by norm_num)
theorem B687953 : Blo 542804 687953 := bbase (se 2 (by rfl) ⟨257982, by rfl⟩ : syracuseStep 687953 = 515965) (by norm_num)
theorem B819029 : Blo 542804 819029 := bbase (se 9 (by rfl) ⟨2399, by rfl⟩ : syracuseStep 819029 = 4799) (by norm_num)
theorem B819053 : Blo 542804 819053 := bbase (se 3 (by rfl) ⟨153572, by rfl⟩ : syracuseStep 819053 = 307145) (by norm_num)
theorem B917365 : Blo 542804 917365 := bbase (se 5 (by rfl) ⟨43001, by rfl⟩ : syracuseStep 917365 = 86003) (by norm_num)
theorem B982901 : Blo 542804 982901 := bbase (se 5 (by rfl) ⟨46073, by rfl⟩ : syracuseStep 982901 = 92147) (by norm_num)
theorem B819077 : Blo 542804 819077 := bbase (se 4 (by rfl) ⟨76788, by rfl⟩ : syracuseStep 819077 = 153577) (by norm_num)
theorem B688009 : Blo 542804 688009 := bbase (se 2 (by rfl) ⟨258003, by rfl⟩ : syracuseStep 688009 = 516007) (by norm_num)
theorem B1376149 : Blo 542804 1376149 := bbase (se 6 (by rfl) ⟨32253, by rfl⟩ : syracuseStep 1376149 = 64507) (by norm_num)
theorem B2326421 : Blo 542804 2326421 := bbase (se 6 (by rfl) ⟨54525, by rfl⟩ : syracuseStep 2326421 = 109051) (by norm_num)
theorem B819101 : Blo 542804 819101 := bbase (se 3 (by rfl) ⟨153581, by rfl⟩ : syracuseStep 819101 = 307163) (by norm_num)
theorem B622513 : Blo 542804 622513 := bbase (se 2 (by rfl) ⟨233442, by rfl⟩ : syracuseStep 622513 = 466885) (by norm_num)
theorem B819125 : Blo 542804 819125 := bbase (se 5 (by rfl) ⟨38396, by rfl⟩ : syracuseStep 819125 = 76793) (by norm_num)
theorem B917453 : Blo 542804 917453 := bbase (se 3 (by rfl) ⟨172022, by rfl⟩ : syracuseStep 917453 = 344045) (by norm_num)
theorem B819149 : Blo 542804 819149 := bbase (se 3 (by rfl) ⟨153590, by rfl⟩ : syracuseStep 819149 = 307181) (by norm_num)
theorem B819173 : Blo 542804 819173 := bbase (se 4 (by rfl) ⟨76797, by rfl⟩ : syracuseStep 819173 = 153595) (by norm_num)
theorem B688105 : Blo 542804 688105 := bbase (se 2 (by rfl) ⟨258039, by rfl⟩ : syracuseStep 688105 = 516079) (by norm_num)
theorem B819197 : Blo 542804 819197 := bbase (se 3 (by rfl) ⟨153599, by rfl⟩ : syracuseStep 819197 = 307199) (by norm_num)
theorem B917507 : Blo 542804 917507 := bstep (se 1 (by rfl) ⟨688130, by rfl⟩ : syracuseStep 917507 = 1376261) B1376261
theorem B819203 : Blo 542804 819203 := bstep (se 1 (by rfl) ⟨614402, by rfl⟩ : syracuseStep 819203 = 1228805) B1228805
theorem B819233 : Blo 542804 819233 := bstep (se 2 (by rfl) ⟨307212, by rfl⟩ : syracuseStep 819233 = 614425) B614425
theorem B1376291 : Blo 542804 1376291 := bstep (se 1 (by rfl) ⟨1032218, by rfl⟩ : syracuseStep 1376291 = 2064437) B2064437
theorem B819251 : Blo 542804 819251 := bstep (se 1 (by rfl) ⟨614438, by rfl⟩ : syracuseStep 819251 = 1228877) B1228877
theorem B1572941 : Blo 542804 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B819281 : Blo 542804 819281 := bstep (se 2 (by rfl) ⟨307230, by rfl⟩ : syracuseStep 819281 = 614461) B614461
theorem B819299 : Blo 542804 819299 := bstep (se 1 (by rfl) ⟨614474, by rfl⟩ : syracuseStep 819299 = 1228949) B1228949
theorem B1310833 : Blo 542804 1310833 := bstep (se 2 (by rfl) ⟨491562, by rfl⟩ : syracuseStep 1310833 = 983125) B983125
theorem B819329 : Blo 542804 819329 := bstep (se 2 (by rfl) ⟨307248, by rfl⟩ : syracuseStep 819329 = 614497) B614497
theorem B917635 : Blo 542804 917635 := bstep (se 1 (by rfl) ⟨688226, by rfl⟩ : syracuseStep 917635 = 1376453) B1376453
theorem B819347 : Blo 542804 819347 := bstep (se 1 (by rfl) ⟨614510, by rfl⟩ : syracuseStep 819347 = 1229021) B1229021
theorem B819377 : Blo 542804 819377 := bstep (se 2 (by rfl) ⟨307266, by rfl⟩ : syracuseStep 819377 = 614533) B614533
theorem B819395 : Blo 542804 819395 := bstep (se 1 (by rfl) ⟨614546, by rfl⟩ : syracuseStep 819395 = 1229093) B1229093
theorem B819425 : Blo 542804 819425 := bstep (se 2 (by rfl) ⟨307284, by rfl⟩ : syracuseStep 819425 = 614569) B614569
theorem B819443 : Blo 542804 819443 := bstep (se 1 (by rfl) ⟨614582, by rfl⟩ : syracuseStep 819443 = 1229165) B1229165
theorem B917777 : Blo 542804 917777 := bstep (se 2 (by rfl) ⟨344166, by rfl⟩ : syracuseStep 917777 = 688333) B688333
theorem B819473 : Blo 542804 819473 := bstep (se 2 (by rfl) ⟨307302, by rfl⟩ : syracuseStep 819473 = 614605) B614605
theorem B819491 : Blo 542804 819491 := bstep (se 1 (by rfl) ⟨614618, by rfl⟩ : syracuseStep 819491 = 1229237) B1229237
theorem B819521 : Blo 542804 819521 := bstep (se 2 (by rfl) ⟨307320, by rfl⟩ : syracuseStep 819521 = 614641) B614641
theorem B819539 : Blo 542804 819539 := bstep (se 1 (by rfl) ⟨614654, by rfl⟩ : syracuseStep 819539 = 1229309) B1229309
theorem B819569 : Blo 542804 819569 := bstep (se 2 (by rfl) ⟨307338, by rfl⟩ : syracuseStep 819569 = 614677) B614677
theorem B819587 : Blo 542804 819587 := bstep (se 1 (by rfl) ⟨614690, by rfl⟩ : syracuseStep 819587 = 1229381) B1229381
theorem B1835405 : Blo 542804 1835405 := bstep (se 3 (by rfl) ⟨344138, by rfl⟩ : syracuseStep 1835405 = 688277) B688277
theorem B9929101 : Blo 542804 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B1474957 : Blo 542804 1474957 := bstep (se 3 (by rfl) ⟨276554, by rfl⟩ : syracuseStep 1474957 = 553109) B553109
theorem B917905 : Blo 542804 917905 := bstep (se 2 (by rfl) ⟨344214, by rfl⟩ : syracuseStep 917905 = 688429) B688429
theorem B819617 : Blo 542804 819617 := bstep (se 2 (by rfl) ⟨307356, by rfl⟩ : syracuseStep 819617 = 614713) B614713
theorem B917939 : Blo 542804 917939 := bstep (se 1 (by rfl) ⟨688454, by rfl⟩ : syracuseStep 917939 = 1376909) B1376909
theorem B819635 : Blo 542804 819635 := bstep (se 1 (by rfl) ⟨614726, by rfl⟩ : syracuseStep 819635 = 1229453) B1229453
theorem B1835459 : Blo 542804 1835459 := bstep (se 1 (by rfl) ⟨1376594, by rfl⟩ : syracuseStep 1835459 = 2753189) B2753189
theorem B819665 : Blo 542804 819665 := bstep (se 2 (by rfl) ⟨307374, by rfl⟩ : syracuseStep 819665 = 614749) B614749
theorem B819683 : Blo 542804 819683 := bstep (se 1 (by rfl) ⟨614762, by rfl⟩ : syracuseStep 819683 = 1229525) B1229525
theorem B819713 : Blo 542804 819713 := bstep (se 2 (by rfl) ⟨307392, by rfl⟩ : syracuseStep 819713 = 614785) B614785
theorem B819731 : Blo 542804 819731 := bstep (se 1 (by rfl) ⟨614798, by rfl⟩ : syracuseStep 819731 = 1229597) B1229597
theorem B2327089 : Blo 542804 2327089 := bstep (se 2 (by rfl) ⟨872658, by rfl⟩ : syracuseStep 2327089 = 1745317) B1745317
theorem B918067 : Blo 542804 918067 := bstep (se 1 (by rfl) ⟨688550, by rfl⟩ : syracuseStep 918067 = 1377101) B1377101
theorem B819761 : Blo 542804 819761 := bstep (se 2 (by rfl) ⟨307410, by rfl⟩ : syracuseStep 819761 = 614821) B614821
theorem B819779 : Blo 542804 819779 := bstep (se 1 (by rfl) ⟨614834, by rfl⟩ : syracuseStep 819779 = 1229669) B1229669
theorem B819809 : Blo 542804 819809 := bstep (se 2 (by rfl) ⟨307428, by rfl⟩ : syracuseStep 819809 = 614857) B614857
theorem B1245809 : Blo 542804 1245809 := bstep (se 2 (by rfl) ⟨467178, by rfl⟩ : syracuseStep 1245809 = 934357) B934357
theorem B819827 : Blo 542804 819827 := bstep (se 1 (by rfl) ⟨614870, by rfl⟩ : syracuseStep 819827 = 1229741) B1229741
theorem B819857 : Blo 542804 819857 := bstep (se 2 (by rfl) ⟨307446, by rfl⟩ : syracuseStep 819857 = 614893) B614893
theorem B819875 : Blo 542804 819875 := bstep (se 1 (by rfl) ⟨614906, by rfl⟩ : syracuseStep 819875 = 1229813) B1229813
theorem B688819 : Blo 542804 688819 := bstep (se 1 (by rfl) ⟨516614, by rfl⟩ : syracuseStep 688819 = 1033229) B1033229
theorem B918209 : Blo 542804 918209 := bstep (se 2 (by rfl) ⟨344328, by rfl⟩ : syracuseStep 918209 = 688657) B688657
theorem B819905 : Blo 542804 819905 := bstep (se 2 (by rfl) ⟨307464, by rfl⟩ : syracuseStep 819905 = 614929) B614929
theorem B1835729 : Blo 542804 1835729 := bstep (se 2 (by rfl) ⟨688398, by rfl⟩ : syracuseStep 1835729 = 1376797) B1376797
theorem B819923 : Blo 542804 819923 := bstep (se 1 (by rfl) ⟨614942, by rfl⟩ : syracuseStep 819923 = 1229885) B1229885
theorem B819953 : Blo 542804 819953 := bstep (se 2 (by rfl) ⟨307482, by rfl⟩ : syracuseStep 819953 = 614965) B614965
theorem B819971 : Blo 542804 819971 := bstep (se 1 (by rfl) ⟨614978, by rfl⟩ : syracuseStep 819971 = 1229957) B1229957
theorem B3539717 : Blo 542804 3539717 := bstep (se 4 (by rfl) ⟨331848, by rfl⟩ : syracuseStep 3539717 = 663697) B663697
theorem B3113741 : Blo 542804 3113741 := bstep (se 3 (by rfl) ⟨583826, by rfl⟩ : syracuseStep 3113741 = 1167653) B1167653
theorem B688915 : Blo 542804 688915 := bstep (se 1 (by rfl) ⟨516686, by rfl⟩ : syracuseStep 688915 = 1033373) B1033373
theorem B820001 : Blo 542804 820001 := bstep (se 2 (by rfl) ⟨307500, by rfl⟩ : syracuseStep 820001 = 615001) B615001
theorem B820019 : Blo 542804 820019 := bstep (se 1 (by rfl) ⟨615014, by rfl⟩ : syracuseStep 820019 = 1230029) B1230029
theorem B918337 : Blo 542804 918337 := bstep (se 2 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 918337 = 688753) B688753
theorem B820049 : Blo 542804 820049 := bstep (se 2 (by rfl) ⟨307518, by rfl⟩ : syracuseStep 820049 = 615037) B615037
theorem B918371 : Blo 542804 918371 := bstep (se 1 (by rfl) ⟨688778, by rfl⟩ : syracuseStep 918371 = 1377557) B1377557
theorem B820067 : Blo 542804 820067 := bstep (se 1 (by rfl) ⟨615050, by rfl⟩ : syracuseStep 820067 = 1230101) B1230101
theorem B820097 : Blo 542804 820097 := bstep (se 2 (by rfl) ⟨307536, by rfl⟩ : syracuseStep 820097 = 615073) B615073
theorem B820115 : Blo 542804 820115 := bstep (se 1 (by rfl) ⟨615086, by rfl⟩ : syracuseStep 820115 = 1230173) B1230173
theorem B820145 : Blo 542804 820145 := bstep (se 2 (by rfl) ⟨307554, by rfl⟩ : syracuseStep 820145 = 615109) B615109
theorem B820163 : Blo 542804 820163 := bstep (se 1 (by rfl) ⟨615122, by rfl⟩ : syracuseStep 820163 = 1230245) B1230245
theorem B1377233 : Blo 542804 1377233 := bstep (se 2 (by rfl) ⟨516462, by rfl⟩ : syracuseStep 1377233 = 1032925) B1032925
theorem B820193 : Blo 542804 820193 := bstep (se 2 (by rfl) ⟨307572, by rfl⟩ : syracuseStep 820193 = 615145) B615145
theorem B918499 : Blo 542804 918499 := bstep (se 1 (by rfl) ⟨688874, by rfl⟩ : syracuseStep 918499 = 1377749) B1377749
theorem B8979427 : Blo 542804 8979427 := bstep (se 1 (by rfl) ⟨6734570, by rfl⟩ : syracuseStep 8979427 = 13469141) B13469141
theorem B1868771 : Blo 542804 1868771 := bstep (se 1 (by rfl) ⟨1401578, by rfl⟩ : syracuseStep 1868771 = 2803157) B2803157
theorem B1377283 : Blo 542804 1377283 := bstep (se 1 (by rfl) ⟨1032962, by rfl⟩ : syracuseStep 1377283 = 2065925) B2065925
theorem B918641 : Blo 542804 918641 := bstep (se 2 (by rfl) ⟨344490, by rfl⟩ : syracuseStep 918641 = 688981) B688981
theorem B1377425 : Blo 542804 1377425 := bstep (se 2 (by rfl) ⟨516534, by rfl⟩ : syracuseStep 1377425 = 1033069) B1033069
theorem B1836269 : Blo 542804 1836269 := bstep (se 3 (by rfl) ⟨344300, by rfl⟩ : syracuseStep 1836269 = 688601) B688601
theorem B918769 : Blo 542804 918769 := bstep (se 2 (by rfl) ⟨344538, by rfl⟩ : syracuseStep 918769 = 689077) B689077
theorem B689411 : Blo 542804 689411 := bstep (se 1 (by rfl) ⟨517058, by rfl⟩ : syracuseStep 689411 = 1034117) B1034117
theorem B918803 : Blo 542804 918803 := bstep (se 1 (by rfl) ⟨689102, by rfl⟩ : syracuseStep 918803 = 1378205) B1378205
theorem B1836323 : Blo 542804 1836323 := bstep (se 1 (by rfl) ⟨1377242, by rfl⟩ : syracuseStep 1836323 = 2754485) B2754485
theorem B1574225 : Blo 542804 1574225 := bstep (se 2 (by rfl) ⟨590334, by rfl⟩ : syracuseStep 1574225 = 1180669) B1180669
theorem B984401 : Blo 542804 984401 := bstep (se 2 (by rfl) ⟨369150, by rfl⟩ : syracuseStep 984401 = 738301) B738301
theorem B918931 : Blo 542804 918931 := bstep (se 1 (by rfl) ⟨689198, by rfl⟩ : syracuseStep 918931 = 1378397) B1378397
theorem B919073 : Blo 542804 919073 := bstep (se 2 (by rfl) ⟨344652, by rfl⟩ : syracuseStep 919073 = 689305) B689305
theorem B1836593 : Blo 542804 1836593 := bstep (se 2 (by rfl) ⟨688722, by rfl⟩ : syracuseStep 1836593 = 1377445) B1377445
theorem B2754161 : Blo 542804 2754161 := bstep (se 2 (by rfl) ⟨1032810, by rfl⟩ : syracuseStep 2754161 = 2065621) B2065621
theorem B919201 : Blo 542804 919201 := bstep (se 2 (by rfl) ⟨344700, by rfl⟩ : syracuseStep 919201 = 689401) B689401
theorem B919235 : Blo 542804 919235 := bstep (se 1 (by rfl) ⟨689426, by rfl⟩ : syracuseStep 919235 = 1378853) B1378853
theorem B919363 : Blo 542804 919363 := bstep (se 1 (by rfl) ⟨689522, by rfl⟩ : syracuseStep 919363 = 1379045) B1379045
theorem B690115 : Blo 542804 690115 := bstep (se 1 (by rfl) ⟨517586, by rfl⟩ : syracuseStep 690115 = 1035173) B1035173
theorem B2066381 : Blo 542804 2066381 := bstep (se 3 (by rfl) ⟨387446, by rfl⟩ : syracuseStep 2066381 = 774893) B774893
theorem B919505 : Blo 542804 919505 := bstep (se 2 (by rfl) ⟨344814, by rfl⟩ : syracuseStep 919505 = 689629) B689629
theorem B690211 : Blo 542804 690211 := bstep (se 1 (by rfl) ⟨517658, by rfl⟩ : syracuseStep 690211 = 1035317) B1035317
theorem B7473221 : Blo 542804 7473221 := bstep (se 4 (by rfl) ⟨700614, by rfl⟩ : syracuseStep 7473221 = 1401229) B1401229
theorem B1837133 : Blo 542804 1837133 := bstep (se 3 (by rfl) ⟨344462, by rfl⟩ : syracuseStep 1837133 = 688925) B688925
theorem B919633 : Blo 542804 919633 := bstep (se 2 (by rfl) ⟨344862, by rfl⟩ : syracuseStep 919633 = 689725) B689725
theorem B1378417 : Blo 542804 1378417 := bstep (se 2 (by rfl) ⟨516906, by rfl⟩ : syracuseStep 1378417 = 1033813) B1033813
theorem B919667 : Blo 542804 919667 := bstep (se 1 (by rfl) ⟨689750, by rfl⟩ : syracuseStep 919667 = 1379501) B1379501
theorem B1837187 : Blo 542804 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B919795 : Blo 542804 919795 := bstep (se 1 (by rfl) ⟨689846, by rfl⟩ : syracuseStep 919795 = 1379693) B1379693
theorem B1739075 : Blo 542804 1739075 := bstep (se 1 (by rfl) ⟨1304306, by rfl⟩ : syracuseStep 1739075 = 2608613) B2608613
theorem B1870193 : Blo 542804 1870193 := bstep (se 2 (by rfl) ⟨701322, by rfl⟩ : syracuseStep 1870193 = 1402645) B1402645
theorem B919937 : Blo 542804 919937 := bstep (se 2 (by rfl) ⟨344976, by rfl⟩ : syracuseStep 919937 = 689953) B689953
theorem B1378691 : Blo 542804 1378691 := bstep (se 1 (by rfl) ⟨1034018, by rfl⟩ : syracuseStep 1378691 = 2068037) B2068037
theorem B1837457 : Blo 542804 1837457 := bstep (se 2 (by rfl) ⟨689046, by rfl⟩ : syracuseStep 1837457 = 1378093) B1378093
theorem B920065 : Blo 542804 920065 := bstep (se 2 (by rfl) ⟨345024, by rfl⟩ : syracuseStep 920065 = 690049) B690049
theorem B690707 : Blo 542804 690707 := bstep (se 1 (by rfl) ⟨518030, by rfl⟩ : syracuseStep 690707 = 1036061) B1036061
theorem B920099 : Blo 542804 920099 := bstep (se 1 (by rfl) ⟨690074, by rfl⟩ : syracuseStep 920099 = 1380149) B1380149
theorem B1378883 : Blo 542804 1378883 := bstep (se 1 (by rfl) ⟨1034162, by rfl⟩ : syracuseStep 1378883 = 2068325) B2068325
theorem B920227 : Blo 542804 920227 := bstep (se 1 (by rfl) ⟨690170, by rfl⟩ : syracuseStep 920227 = 1380341) B1380341
theorem B1477315 : Blo 542804 1477315 := bstep (se 1 (by rfl) ⟨1107986, by rfl⟩ : syracuseStep 1477315 = 2215973) B2215973
theorem B920369 : Blo 542804 920369 := bstep (se 2 (by rfl) ⟨345138, by rfl⟩ : syracuseStep 920369 = 690277) B690277
theorem B1837997 : Blo 542804 1837997 := bstep (se 3 (by rfl) ⟨344624, by rfl⟩ : syracuseStep 1837997 = 689249) B689249
theorem B920497 : Blo 542804 920497 := bstep (se 2 (by rfl) ⟨345186, by rfl⟩ : syracuseStep 920497 = 690373) B690373
theorem B920531 : Blo 542804 920531 := bstep (se 1 (by rfl) ⟨690398, by rfl⟩ : syracuseStep 920531 = 1380797) B1380797
theorem B1838051 : Blo 542804 1838051 := bstep (se 1 (by rfl) ⟨1378538, by rfl⟩ : syracuseStep 1838051 = 2757077) B2757077
theorem B2755619 : Blo 542804 2755619 := bstep (se 1 (by rfl) ⟨2066714, by rfl⟩ : syracuseStep 2755619 = 4133429) B4133429
theorem B920659 : Blo 542804 920659 := bstep (se 1 (by rfl) ⟨690494, by rfl⟩ : syracuseStep 920659 = 1380989) B1380989
theorem B1346737 : Blo 542804 1346737 := bstep (se 2 (by rfl) ⟨505026, by rfl⟩ : syracuseStep 1346737 = 1010053) B1010053
theorem B691411 : Blo 542804 691411 := bstep (se 1 (by rfl) ⟨518558, by rfl⟩ : syracuseStep 691411 = 1037117) B1037117
theorem B920801 : Blo 542804 920801 := bstep (se 2 (by rfl) ⟨345300, by rfl⟩ : syracuseStep 920801 = 690601) B690601
theorem B1838321 : Blo 542804 1838321 := bstep (se 2 (by rfl) ⟨689370, by rfl⟩ : syracuseStep 1838321 = 1378741) B1378741
theorem B691507 : Blo 542804 691507 := bstep (se 1 (by rfl) ⟨518630, by rfl⟩ : syracuseStep 691507 = 1037261) B1037261
theorem B920929 : Blo 542804 920929 := bstep (se 2 (by rfl) ⟨345348, by rfl⟩ : syracuseStep 920929 = 690697) B690697
theorem B920963 : Blo 542804 920963 := bstep (se 1 (by rfl) ⟨690722, by rfl⟩ : syracuseStep 920963 = 1381445) B1381445
theorem B1379825 : Blo 542804 1379825 := bstep (se 2 (by rfl) ⟨517434, by rfl⟩ : syracuseStep 1379825 = 1034869) B1034869
theorem B921091 : Blo 542804 921091 := bstep (se 1 (by rfl) ⟨690818, by rfl⟩ : syracuseStep 921091 = 1381637) B1381637
theorem B2330147 : Blo 542804 2330147 := bstep (se 1 (by rfl) ⟨1747610, by rfl⟩ : syracuseStep 2330147 = 3495221) B3495221
theorem B1379875 : Blo 542804 1379875 := bstep (se 1 (by rfl) ⟨1034906, by rfl⟩ : syracuseStep 1379875 = 2069813) B2069813
theorem B1773197 : Blo 542804 1773197 := bstep (se 3 (by rfl) ⟨332474, by rfl⟩ : syracuseStep 1773197 = 664949) B664949
theorem B921233 : Blo 542804 921233 := bstep (se 2 (by rfl) ⟨345462, by rfl⟩ : syracuseStep 921233 = 690925) B690925
theorem B1380017 : Blo 542804 1380017 := bstep (se 2 (by rfl) ⟨517506, by rfl⟩ : syracuseStep 1380017 = 1035013) B1035013
theorem B1838861 : Blo 542804 1838861 := bstep (se 3 (by rfl) ⟨344786, by rfl⟩ : syracuseStep 1838861 = 689573) B689573
theorem B921361 : Blo 542804 921361 := bstep (se 2 (by rfl) ⟨345510, by rfl⟩ : syracuseStep 921361 = 691021) B691021
theorem B692003 : Blo 542804 692003 := bstep (se 1 (by rfl) ⟨519002, by rfl⟩ : syracuseStep 692003 = 1038005) B1038005
theorem B921395 : Blo 542804 921395 := bstep (se 1 (by rfl) ⟨691046, by rfl⟩ : syracuseStep 921395 = 1382093) B1382093
theorem B1838915 : Blo 542804 1838915 := bstep (se 1 (by rfl) ⟨1379186, by rfl⟩ : syracuseStep 1838915 = 2758373) B2758373
theorem B2756429 : Blo 542804 2756429 := bstep (se 3 (by rfl) ⟨516830, by rfl⟩ : syracuseStep 2756429 = 1033661) B1033661
theorem B921523 : Blo 542804 921523 := bstep (se 1 (by rfl) ⟨691142, by rfl⟩ : syracuseStep 921523 = 1382285) B1382285
theorem B1740845 : Blo 542804 1740845 := bstep (se 3 (by rfl) ⟨326408, by rfl⟩ : syracuseStep 1740845 = 652817) B652817
theorem B921665 : Blo 542804 921665 := bstep (se 2 (by rfl) ⟨345624, by rfl⟩ : syracuseStep 921665 = 691249) B691249
theorem B1839185 : Blo 542804 1839185 := bstep (se 2 (by rfl) ⟨689694, by rfl⟩ : syracuseStep 1839185 = 1379389) B1379389
theorem B1740973 : Blo 542804 1740973 := bstep (se 3 (by rfl) ⟨326432, by rfl⟩ : syracuseStep 1740973 = 652865) B652865
theorem B921793 : Blo 542804 921793 := bstep (se 2 (by rfl) ⟨345672, by rfl⟩ : syracuseStep 921793 = 691345) B691345
theorem B921827 : Blo 542804 921827 := bstep (se 1 (by rfl) ⟨691370, by rfl⟩ : syracuseStep 921827 = 1382741) B1382741
theorem B921955 : Blo 542804 921955 := bstep (se 1 (by rfl) ⟨691466, by rfl⟩ : syracuseStep 921955 = 1382933) B1382933
theorem B1970531 : Blo 542804 1970531 := bstep (se 1 (by rfl) ⟨1477898, by rfl⟩ : syracuseStep 1970531 = 2955797) B2955797
theorem B3477923 : Blo 542804 3477923 := bstep (se 1 (by rfl) ⟨2608442, by rfl⟩ : syracuseStep 3477923 = 5216885) B5216885
theorem B1741229 : Blo 542804 1741229 := bstep (se 3 (by rfl) ⟨326480, by rfl⟩ : syracuseStep 1741229 = 652961) B652961
theorem B7442885 : Blo 542804 7442885 := bstep (se 4 (by rfl) ⟨697770, by rfl⟩ : syracuseStep 7442885 = 1395541) B1395541
theorem B922097 : Blo 542804 922097 := bstep (se 2 (by rfl) ⟨345786, by rfl⟩ : syracuseStep 922097 = 691573) B691573
theorem B4657763 : Blo 542804 4657763 := bstep (se 1 (by rfl) ⟨3493322, by rfl⟩ : syracuseStep 4657763 = 6986645) B6986645
theorem B1839725 : Blo 542804 1839725 := bstep (se 3 (by rfl) ⟨344948, by rfl⟩ : syracuseStep 1839725 = 689897) B689897
theorem B922225 : Blo 542804 922225 := bstep (se 2 (by rfl) ⟨345834, by rfl⟩ : syracuseStep 922225 = 691669) B691669
theorem B1381009 : Blo 542804 1381009 := bstep (se 2 (by rfl) ⟨517878, by rfl⟩ : syracuseStep 1381009 = 1035757) B1035757
theorem B922259 : Blo 542804 922259 := bstep (se 1 (by rfl) ⟨691694, by rfl⟩ : syracuseStep 922259 = 1383389) B1383389
theorem B1839779 : Blo 542804 1839779 := bstep (se 1 (by rfl) ⟨1379834, by rfl⟩ : syracuseStep 1839779 = 2759669) B2759669
theorem B6197957 : Blo 542804 6197957 := bstep (se 4 (by rfl) ⟨581058, by rfl⟩ : syracuseStep 6197957 = 1162117) B1162117
theorem B922387 : Blo 542804 922387 := bstep (se 1 (by rfl) ⟨691790, by rfl⟩ : syracuseStep 922387 = 1383581) B1383581
theorem B2069297 : Blo 542804 2069297 := bstep (se 2 (by rfl) ⟨775986, by rfl⟩ : syracuseStep 2069297 = 1551973) B1551973
theorem B922529 : Blo 542804 922529 := bstep (se 2 (by rfl) ⟨345948, by rfl⟩ : syracuseStep 922529 = 691897) B691897
theorem B1381283 : Blo 542804 1381283 := bstep (se 1 (by rfl) ⟨1035962, by rfl⟩ : syracuseStep 1381283 = 2071925) B2071925
theorem B1840049 : Blo 542804 1840049 := bstep (se 2 (by rfl) ⟨690018, by rfl⟩ : syracuseStep 1840049 = 1380037) B1380037
theorem B922657 : Blo 542804 922657 := bstep (se 2 (by rfl) ⟨345996, by rfl⟩ : syracuseStep 922657 = 691993) B691993
theorem B922691 : Blo 542804 922691 := bstep (se 1 (by rfl) ⟨692018, by rfl⟩ : syracuseStep 922691 = 1384037) B1384037
theorem B1381475 : Blo 542804 1381475 := bstep (se 1 (by rfl) ⟨1036106, by rfl⟩ : syracuseStep 1381475 = 2072213) B2072213
theorem B2266289 : Blo 542804 2266289 := bstep (se 2 (by rfl) ⟨849858, by rfl⟩ : syracuseStep 2266289 = 1699717) B1699717
theorem B2954501 : Blo 542804 2954501 := bstep (se 4 (by rfl) ⟨276984, by rfl⟩ : syracuseStep 2954501 = 553969) B553969
theorem B1840589 : Blo 542804 1840589 := bstep (se 3 (by rfl) ⟨345110, by rfl⟩ : syracuseStep 1840589 = 690221) B690221
theorem B1840643 : Blo 542804 1840643 := bstep (se 1 (by rfl) ⟨1380482, by rfl⟩ : syracuseStep 1840643 = 2760965) B2760965
theorem B1840913 : Blo 542804 1840913 := bstep (se 2 (by rfl) ⟨690342, by rfl⟩ : syracuseStep 1840913 = 1380685) B1380685
theorem B1742755 : Blo 542804 1742755 := bstep (se 1 (by rfl) ⟨1307066, by rfl⟩ : syracuseStep 1742755 = 2614133) B2614133
theorem B8820677 : Blo 542804 8820677 := bstep (se 4 (by rfl) ⟨826938, by rfl⟩ : syracuseStep 8820677 = 1653877) B1653877
theorem B1382417 : Blo 542804 1382417 := bstep (se 2 (by rfl) ⟨518406, by rfl⟩ : syracuseStep 1382417 = 1036813) B1036813
theorem B1382467 : Blo 542804 1382467 := bstep (se 1 (by rfl) ⟨1036850, by rfl⟩ : syracuseStep 1382467 = 2073701) B2073701
theorem B1382609 : Blo 542804 1382609 := bstep (se 2 (by rfl) ⟨518478, by rfl⟩ : syracuseStep 1382609 = 1036957) B1036957
theorem B2070755 : Blo 542804 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B1841453 : Blo 542804 1841453 := bstep (se 3 (by rfl) ⟨345272, by rfl⟩ : syracuseStep 1841453 = 690545) B690545
theorem B1841507 : Blo 542804 1841507 := bstep (se 1 (by rfl) ⟨1381130, by rfl⟩ : syracuseStep 1841507 = 2762261) B2762261
theorem B2791907 : Blo 542804 2791907 := bstep (se 1 (by rfl) ⟨2093930, by rfl⟩ : syracuseStep 2791907 = 4187861) B4187861
theorem B1841777 : Blo 542804 1841777 := bstep (se 2 (by rfl) ⟨690666, by rfl⟩ : syracuseStep 1841777 = 1381333) B1381333
theorem B2759345 : Blo 542804 2759345 := bstep (se 2 (by rfl) ⟨1034754, by rfl⟩ : syracuseStep 2759345 = 2069509) B2069509
theorem B1547075 : Blo 542804 1547075 := bstep (se 1 (by rfl) ⟨1160306, by rfl⟩ : syracuseStep 1547075 = 2320613) B2320613
theorem B1842317 : Blo 542804 1842317 := bstep (se 3 (by rfl) ⟨345434, by rfl⟩ : syracuseStep 1842317 = 690869) B690869
theorem B1383601 : Blo 542804 1383601 := bstep (se 2 (by rfl) ⟨518850, by rfl⟩ : syracuseStep 1383601 = 1037701) B1037701
theorem B1842371 : Blo 542804 1842371 := bstep (se 1 (by rfl) ⟨1381778, by rfl⟩ : syracuseStep 1842371 = 2763557) B2763557
theorem B2071757 : Blo 542804 2071757 := bstep (se 3 (by rfl) ⟨388454, by rfl⟩ : syracuseStep 2071757 = 776909) B776909
theorem B1383875 : Blo 542804 1383875 := bstep (se 1 (by rfl) ⟨1037906, by rfl⟩ : syracuseStep 1383875 = 2075813) B2075813
theorem B1842641 : Blo 542804 1842641 := bstep (se 2 (by rfl) ⟨690990, by rfl⟩ : syracuseStep 1842641 = 1381981) B1381981
theorem B1744355 : Blo 542804 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B630275 : Blo 542804 630275 := bstep (se 1 (by rfl) ⟨472706, by rfl⟩ : syracuseStep 630275 = 945413) B945413
theorem B1384067 : Blo 542804 1384067 := bstep (se 1 (by rfl) ⟨1038050, by rfl⟩ : syracuseStep 1384067 = 2076101) B2076101
theorem B2334349 : Blo 542804 2334349 := bstep (se 3 (by rfl) ⟨437690, by rfl⟩ : syracuseStep 2334349 = 875381) B875381
theorem B1843181 : Blo 542804 1843181 := bstep (se 3 (by rfl) ⟨345596, by rfl⟩ : syracuseStep 1843181 = 691193) B691193
theorem B3481613 : Blo 542804 3481613 := bstep (se 3 (by rfl) ⟨652802, by rfl⟩ : syracuseStep 3481613 = 1305605) B1305605
theorem B1548305 : Blo 542804 1548305 := bstep (se 2 (by rfl) ⟨580614, by rfl⟩ : syracuseStep 1548305 = 1161229) B1161229
theorem B1843235 : Blo 542804 1843235 := bstep (se 1 (by rfl) ⟨1382426, by rfl⟩ : syracuseStep 1843235 = 2764853) B2764853
theorem B2760803 : Blo 542804 2760803 := bstep (se 1 (by rfl) ⟨2070602, by rfl⟩ : syracuseStep 2760803 = 4141205) B4141205
theorem B3481841 : Blo 542804 3481841 := bstep (se 2 (by rfl) ⟨1305690, by rfl⟩ : syracuseStep 3481841 = 2611381) B2611381
theorem B1843505 : Blo 542804 1843505 := bstep (se 2 (by rfl) ⟨691314, by rfl⟩ : syracuseStep 1843505 = 1382629) B1382629
theorem B827761 : Blo 542804 827761 := bstep (se 2 (by rfl) ⟨310410, by rfl⟩ : syracuseStep 827761 = 620821) B620821
theorem B991651 : Blo 542804 991651 := bstep (se 1 (by rfl) ⟨743738, by rfl⟩ : syracuseStep 991651 = 1487477) B1487477
theorem B1745329 : Blo 542804 1745329 := bstep (se 2 (by rfl) ⟨654498, by rfl⟩ : syracuseStep 1745329 = 1308997) B1308997
theorem B2990513 : Blo 542804 2990513 := bstep (se 2 (by rfl) ⟨1121442, by rfl⟩ : syracuseStep 2990513 = 2242885) B2242885
theorem B3154565 : Blo 542804 3154565 := bstep (se 4 (by rfl) ⟨295740, by rfl⟩ : syracuseStep 3154565 = 591481) B591481
theorem B1221425 : Blo 542804 1221425 := bstep (se 2 (by rfl) ⟨458034, by rfl⟩ : syracuseStep 1221425 = 916069) B916069
theorem B1221443 : Blo 542804 1221443 := bstep (se 1 (by rfl) ⟨916082, by rfl⟩ : syracuseStep 1221443 = 1832165) B1832165
theorem B5907269 : Blo 542804 5907269 := bstep (se 4 (by rfl) ⟨553806, by rfl⟩ : syracuseStep 5907269 = 1107613) B1107613
theorem B1844045 : Blo 542804 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B1844099 : Blo 542804 1844099 := bstep (se 1 (by rfl) ⟨1383074, by rfl⟩ : syracuseStep 1844099 = 2766149) B2766149
theorem B2761613 : Blo 542804 2761613 := bstep (se 3 (by rfl) ⟨517802, by rfl⟩ : syracuseStep 2761613 = 1035605) B1035605
theorem B14001173 : Blo 542804 14001173 := bstep (se 6 (by rfl) ⟨328152, by rfl⟩ : syracuseStep 14001173 = 656305) B656305
theorem B1221713 : Blo 542804 1221713 := bstep (se 2 (by rfl) ⟨458142, by rfl⟩ : syracuseStep 1221713 = 916285) B916285
theorem B1221731 : Blo 542804 1221731 := bstep (se 1 (by rfl) ⟨916298, by rfl⟩ : syracuseStep 1221731 = 1832597) B1832597
theorem B1844369 : Blo 542804 1844369 := bstep (se 2 (by rfl) ⟨691638, by rfl⟩ : syracuseStep 1844369 = 1383277) B1383277
theorem B828643 : Blo 542804 828643 := bstep (se 1 (by rfl) ⟨621482, by rfl⟩ : syracuseStep 828643 = 1242965) B1242965
theorem B2073869 : Blo 542804 2073869 := bstep (se 3 (by rfl) ⟨388850, by rfl⟩ : syracuseStep 2073869 = 777701) B777701
theorem B1222001 : Blo 542804 1222001 := bstep (se 2 (by rfl) ⟨458250, by rfl⟩ : syracuseStep 1222001 = 916501) B916501
theorem B1222019 : Blo 542804 1222019 := bstep (se 1 (by rfl) ⟨916514, by rfl⟩ : syracuseStep 1222019 = 1833029) B1833029
theorem B1549763 : Blo 542804 1549763 := bstep (se 1 (by rfl) ⟨1162322, by rfl⟩ : syracuseStep 1549763 = 2324645) B2324645
theorem B4368013 : Blo 542804 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B1222289 : Blo 542804 1222289 := bstep (se 2 (by rfl) ⟨458358, by rfl⟩ : syracuseStep 1222289 = 916717) B916717
theorem B1222307 : Blo 542804 1222307 := bstep (se 1 (by rfl) ⟨916730, by rfl⟩ : syracuseStep 1222307 = 1833461) B1833461
theorem B1844909 : Blo 542804 1844909 := bstep (se 3 (by rfl) ⟨345920, by rfl⟩ : syracuseStep 1844909 = 691841) B691841
theorem B894691 : Blo 542804 894691 := bstep (se 1 (by rfl) ⟨671018, by rfl⟩ : syracuseStep 894691 = 1342037) B1342037
theorem B1844963 : Blo 542804 1844963 := bstep (se 1 (by rfl) ⟨1383722, by rfl⟩ : syracuseStep 1844963 = 2767445) B2767445
theorem B1222577 : Blo 542804 1222577 := bstep (se 2 (by rfl) ⟨458466, by rfl⟩ : syracuseStep 1222577 = 916933) B916933
theorem B1222595 : Blo 542804 1222595 := bstep (se 1 (by rfl) ⟨916946, by rfl⟩ : syracuseStep 1222595 = 1833893) B1833893
theorem B1845233 : Blo 542804 1845233 := bstep (se 2 (by rfl) ⟨691962, by rfl⟩ : syracuseStep 1845233 = 1383925) B1383925
theorem B2074673 : Blo 542804 2074673 := bstep (se 2 (by rfl) ⟨778002, by rfl⟩ : syracuseStep 2074673 = 1556005) B1556005
theorem B1747021 : Blo 542804 1747021 := bstep (se 3 (by rfl) ⟨327566, by rfl⟩ : syracuseStep 1747021 = 655133) B655133
theorem B1222865 : Blo 542804 1222865 := bstep (se 2 (by rfl) ⟨458574, by rfl⟩ : syracuseStep 1222865 = 917149) B917149
theorem B1222883 : Blo 542804 1222883 := bstep (se 1 (by rfl) ⟨917162, by rfl⟩ : syracuseStep 1222883 = 1834325) B1834325
theorem B1550573 : Blo 542804 1550573 := bstep (se 3 (by rfl) ⟨290732, by rfl⟩ : syracuseStep 1550573 = 581465) B581465
theorem B2959715 : Blo 542804 2959715 := bstep (se 1 (by rfl) ⟨2219786, by rfl⟩ : syracuseStep 2959715 = 4439573) B4439573
theorem B6203789 : Blo 542804 6203789 := bstep (se 3 (by rfl) ⟨1163210, by rfl⟩ : syracuseStep 6203789 = 2326421) B2326421
theorem B1550765 : Blo 542804 1550765 := bstep (se 3 (by rfl) ⟨290768, by rfl⟩ : syracuseStep 1550765 = 581537) B581537
theorem B1223153 : Blo 542804 1223153 := bstep (se 2 (by rfl) ⟨458682, by rfl⟩ : syracuseStep 1223153 = 917365) B917365
theorem B1223171 : Blo 542804 1223171 := bstep (se 1 (by rfl) ⟨917378, by rfl⟩ : syracuseStep 1223171 = 1834757) B1834757
theorem B830017 : Blo 542804 830017 := bstep (se 2 (by rfl) ⟨311256, by rfl⟩ : syracuseStep 830017 = 622513) B622513
theorem B2075341 : Blo 542804 2075341 := bstep (se 3 (by rfl) ⟨389126, by rfl⟩ : syracuseStep 2075341 = 778253) B778253
theorem B4139747 : Blo 542804 4139747 := bstep (se 1 (by rfl) ⟨3104810, by rfl⟩ : syracuseStep 4139747 = 6209621) B6209621
theorem B1223441 : Blo 542804 1223441 := bstep (se 2 (by rfl) ⟨458790, by rfl⟩ : syracuseStep 1223441 = 917581) B917581
theorem B1223459 : Blo 542804 1223459 := bstep (se 1 (by rfl) ⟨917594, by rfl⟩ : syracuseStep 1223459 = 1835189) B1835189
theorem B928609 : Blo 542804 928609 := bstep (se 2 (by rfl) ⟨348228, by rfl⟩ : syracuseStep 928609 = 696457) B696457
theorem B1223729 : Blo 542804 1223729 := bstep (se 2 (by rfl) ⟨458898, by rfl⟩ : syracuseStep 1223729 = 917797) B917797
theorem B1223747 : Blo 542804 1223747 := bstep (se 1 (by rfl) ⟨917810, by rfl⟩ : syracuseStep 1223747 = 1835621) B1835621
theorem B1224017 : Blo 542804 1224017 := bstep (se 2 (by rfl) ⟨459006, by rfl⟩ : syracuseStep 1224017 = 918013) B918013
theorem B1224035 : Blo 542804 1224035 := bstep (se 1 (by rfl) ⟨918026, by rfl⟩ : syracuseStep 1224035 = 1836053) B1836053
theorem B1551757 : Blo 542804 1551757 := bstep (se 3 (by rfl) ⟨290954, by rfl⟩ : syracuseStep 1551757 = 581909) B581909
theorem B2076131 : Blo 542804 2076131 := bstep (se 1 (by rfl) ⟨1557098, by rfl⟩ : syracuseStep 2076131 = 3114197) B3114197
theorem B699907 : Blo 542804 699907 := bstep (se 1 (by rfl) ⟨524930, by rfl⟩ : syracuseStep 699907 = 1049861) B1049861
theorem B1224305 : Blo 542804 1224305 := bstep (se 2 (by rfl) ⟨459114, by rfl⟩ : syracuseStep 1224305 = 918229) B918229
theorem B1224323 : Blo 542804 1224323 := bstep (se 1 (by rfl) ⟨918242, by rfl⟩ : syracuseStep 1224323 = 1836485) B1836485
theorem B2764529 : Blo 542804 2764529 := bstep (se 2 (by rfl) ⟨1036698, by rfl⟩ : syracuseStep 2764529 = 2073397) B2073397
theorem B1748803 : Blo 542804 1748803 := bstep (se 1 (by rfl) ⟨1311602, by rfl⟩ : syracuseStep 1748803 = 2623205) B2623205
theorem B1224593 : Blo 542804 1224593 := bstep (se 2 (by rfl) ⟨459222, by rfl⟩ : syracuseStep 1224593 = 918445) B918445
theorem B1224611 : Blo 542804 1224611 := bstep (se 1 (by rfl) ⟨918458, by rfl⟩ : syracuseStep 1224611 = 1836917) B1836917
theorem B3092579 : Blo 542804 3092579 := bstep (se 1 (by rfl) ⟨2319434, by rfl⟩ : syracuseStep 3092579 = 4638869) B4638869
theorem B5910641 : Blo 542804 5910641 := bstep (se 2 (by rfl) ⟨2216490, by rfl⟩ : syracuseStep 5910641 = 4432981) B4432981
theorem B798881 : Blo 542804 798881 := bstep (se 2 (by rfl) ⟨299580, by rfl⟩ : syracuseStep 798881 = 599161) B599161
theorem B1224881 : Blo 542804 1224881 := bstep (se 2 (by rfl) ⟨459330, by rfl⟩ : syracuseStep 1224881 = 918661) B918661
theorem B1224899 : Blo 542804 1224899 := bstep (se 1 (by rfl) ⟨918674, by rfl⟩ : syracuseStep 1224899 = 1837349) B1837349
theorem B1749251 : Blo 542804 1749251 := bstep (se 1 (by rfl) ⟨1311938, by rfl⟩ : syracuseStep 1749251 = 2623877) B2623877
theorem B9286001 : Blo 542804 9286001 := bstep (se 2 (by rfl) ⟨3482250, by rfl⟩ : syracuseStep 9286001 = 6964501) B6964501
theorem B1159555 : Blo 542804 1159555 := bstep (se 1 (by rfl) ⟨869666, by rfl⟩ : syracuseStep 1159555 = 1739333) B1739333
theorem B1225169 : Blo 542804 1225169 := bstep (se 2 (by rfl) ⟨459438, by rfl⟩ : syracuseStep 1225169 = 918877) B918877
theorem B1225187 : Blo 542804 1225187 := bstep (se 1 (by rfl) ⟨918890, by rfl⟩ : syracuseStep 1225187 = 1837781) B1837781
theorem B930355 : Blo 542804 930355 := bstep (se 1 (by rfl) ⟨697766, by rfl⟩ : syracuseStep 930355 = 1395533) B1395533
theorem B766657 : Blo 542804 766657 := bstep (se 2 (by rfl) ⟨287496, by rfl⟩ : syracuseStep 766657 = 574993) B574993
theorem B1225457 : Blo 542804 1225457 := bstep (se 2 (by rfl) ⟨459546, by rfl⟩ : syracuseStep 1225457 = 919093) B919093
theorem B1225475 : Blo 542804 1225475 := bstep (se 1 (by rfl) ⟨919106, by rfl⟩ : syracuseStep 1225475 = 1838213) B1838213
theorem B1225745 : Blo 542804 1225745 := bstep (se 2 (by rfl) ⟨459654, by rfl⟩ : syracuseStep 1225745 = 919309) B919309
theorem B1225763 : Blo 542804 1225763 := bstep (se 1 (by rfl) ⟨919322, by rfl⟩ : syracuseStep 1225763 = 1838645) B1838645
theorem B1553489 : Blo 542804 1553489 := bstep (se 2 (by rfl) ⟨582558, by rfl⟩ : syracuseStep 1553489 = 1165117) B1165117
theorem B2765987 : Blo 542804 2765987 := bstep (se 1 (by rfl) ⟨2074490, by rfl⟩ : syracuseStep 2765987 = 4148981) B4148981
theorem B1160401 : Blo 542804 1160401 := bstep (se 2 (by rfl) ⟨435150, by rfl⟩ : syracuseStep 1160401 = 870301) B870301
theorem B6206705 : Blo 542804 6206705 := bstep (se 2 (by rfl) ⟨2327514, by rfl⟩ : syracuseStep 6206705 = 4655029) B4655029
theorem B1553681 : Blo 542804 1553681 := bstep (se 2 (by rfl) ⟨582630, by rfl⟩ : syracuseStep 1553681 = 1165261) B1165261
theorem B1226033 : Blo 542804 1226033 := bstep (se 2 (by rfl) ⟨459762, by rfl⟩ : syracuseStep 1226033 = 919525) B919525
theorem B1226051 : Blo 542804 1226051 := bstep (se 1 (by rfl) ⟨919538, by rfl⟩ : syracuseStep 1226051 = 1839077) B1839077
theorem B2799011 : Blo 542804 2799011 := bstep (se 1 (by rfl) ⟨2099258, by rfl⟩ : syracuseStep 2799011 = 4198517) B4198517
theorem B1750481 : Blo 542804 1750481 := bstep (se 2 (by rfl) ⟨656430, by rfl⟩ : syracuseStep 1750481 = 1312861) B1312861
theorem B1226321 : Blo 542804 1226321 := bstep (se 2 (by rfl) ⟨459870, by rfl⟩ : syracuseStep 1226321 = 919741) B919741
theorem B1226339 : Blo 542804 1226339 := bstep (se 1 (by rfl) ⟨919754, by rfl⟩ : syracuseStep 1226339 = 1839509) B1839509
theorem B931457 : Blo 542804 931457 := bstep (se 2 (by rfl) ⟨349296, by rfl⟩ : syracuseStep 931457 = 698593) B698593
theorem B3356293 : Blo 542804 3356293 := bstep (se 4 (by rfl) ⟨314652, by rfl⟩ : syracuseStep 3356293 = 629305) B629305
theorem B1226609 : Blo 542804 1226609 := bstep (se 2 (by rfl) ⟨459978, by rfl⟩ : syracuseStep 1226609 = 919957) B919957
theorem B1226627 : Blo 542804 1226627 := bstep (se 1 (by rfl) ⟨919970, by rfl⟩ : syracuseStep 1226627 = 1839941) B1839941
theorem B997265 : Blo 542804 997265 := bstep (se 2 (by rfl) ⟨373974, by rfl⟩ : syracuseStep 997265 = 747949) B747949
theorem B3094469 : Blo 542804 3094469 := bstep (se 4 (by rfl) ⟨290106, by rfl⟩ : syracuseStep 3094469 = 580213) B580213
theorem B2766797 : Blo 542804 2766797 := bstep (se 3 (by rfl) ⟨518774, by rfl⟩ : syracuseStep 2766797 = 1037549) B1037549
theorem B1226897 : Blo 542804 1226897 := bstep (se 2 (by rfl) ⟨460086, by rfl⟩ : syracuseStep 1226897 = 920173) B920173
theorem B1226915 : Blo 542804 1226915 := bstep (se 1 (by rfl) ⟨920186, by rfl⟩ : syracuseStep 1226915 = 1840373) B1840373
theorem B1554673 : Blo 542804 1554673 := bstep (se 2 (by rfl) ⟨583002, by rfl⟩ : syracuseStep 1554673 = 1166005) B1166005
theorem B1751377 : Blo 542804 1751377 := bstep (se 2 (by rfl) ⟨656766, by rfl⟩ : syracuseStep 1751377 = 1313533) B1313533
theorem B1227185 : Blo 542804 1227185 := bstep (se 2 (by rfl) ⟨460194, by rfl⟩ : syracuseStep 1227185 = 920389) B920389
theorem B1227203 : Blo 542804 1227203 := bstep (se 1 (by rfl) ⟨920402, by rfl⟩ : syracuseStep 1227203 = 1840805) B1840805
theorem B3488197 : Blo 542804 3488197 := bstep (se 4 (by rfl) ⟨327018, by rfl⟩ : syracuseStep 3488197 = 654037) B654037
theorem B1554947 : Blo 542804 1554947 := bstep (se 1 (by rfl) ⟨1166210, by rfl⟩ : syracuseStep 1554947 = 2332421) B2332421
theorem B1555139 : Blo 542804 1555139 := bstep (se 1 (by rfl) ⟨1166354, by rfl⟩ : syracuseStep 1555139 = 2332709) B2332709
theorem B1227473 : Blo 542804 1227473 := bstep (se 2 (by rfl) ⟨460302, by rfl⟩ : syracuseStep 1227473 = 920605) B920605
theorem B1227491 : Blo 542804 1227491 := bstep (se 1 (by rfl) ⟨920618, by rfl⟩ : syracuseStep 1227491 = 1841237) B1841237
theorem B1030897 : Blo 542804 1030897 := bstep (se 2 (by rfl) ⟨386586, by rfl⟩ : syracuseStep 1030897 = 773173) B773173
theorem B1227761 : Blo 542804 1227761 := bstep (se 2 (by rfl) ⟨460410, by rfl⟩ : syracuseStep 1227761 = 920821) B920821
theorem B1227779 : Blo 542804 1227779 := bstep (se 1 (by rfl) ⟨920834, by rfl⟩ : syracuseStep 1227779 = 1841669) B1841669
theorem B1653805 : Blo 542804 1653805 := bstep (se 3 (by rfl) ⟨310088, by rfl⟩ : syracuseStep 1653805 = 620177) B620177
theorem B1162289 : Blo 542804 1162289 := bstep (se 2 (by rfl) ⟨435858, by rfl⟩ : syracuseStep 1162289 = 871717) B871717
theorem B1228049 : Blo 542804 1228049 := bstep (se 2 (by rfl) ⟨460518, by rfl⟩ : syracuseStep 1228049 = 921037) B921037
theorem B1228067 : Blo 542804 1228067 := bstep (se 1 (by rfl) ⟨921050, by rfl⟩ : syracuseStep 1228067 = 1842101) B1842101
theorem B933331 : Blo 542804 933331 := bstep (se 1 (by rfl) ⟨699998, by rfl⟩ : syracuseStep 933331 = 1399997) B1399997
theorem B1555949 : Blo 542804 1555949 := bstep (se 3 (by rfl) ⟨291740, by rfl⟩ : syracuseStep 1555949 = 583481) B583481
theorem B1228337 : Blo 542804 1228337 := bstep (se 2 (by rfl) ⟨460626, by rfl⟩ : syracuseStep 1228337 = 921253) B921253
theorem B1228355 : Blo 542804 1228355 := bstep (se 1 (by rfl) ⟨921266, by rfl⟩ : syracuseStep 1228355 = 1842533) B1842533
theorem B1556131 : Blo 542804 1556131 := bstep (se 1 (by rfl) ⟨1167098, by rfl⟩ : syracuseStep 1556131 = 2334197) B2334197
theorem B1031953 : Blo 542804 1031953 := bstep (se 2 (by rfl) ⟨386982, by rfl⟩ : syracuseStep 1031953 = 773965) B773965
theorem B1228625 : Blo 542804 1228625 := bstep (se 2 (by rfl) ⟨460734, by rfl⟩ : syracuseStep 1228625 = 921469) B921469
theorem B1228643 : Blo 542804 1228643 := bstep (se 1 (by rfl) ⟨921482, by rfl⟩ : syracuseStep 1228643 = 1842965) B1842965
theorem B2211725 : Blo 542804 2211725 := bstep (se 3 (by rfl) ⟨414698, by rfl⟩ : syracuseStep 2211725 = 829397) B829397
theorem B737219 : Blo 542804 737219 := bstep (se 1 (by rfl) ⟨552914, by rfl⟩ : syracuseStep 737219 = 1105829) B1105829
theorem B4145093 : Blo 542804 4145093 := bstep (se 4 (by rfl) ⟨388602, by rfl⟩ : syracuseStep 4145093 = 777205) B777205
theorem B1228913 : Blo 542804 1228913 := bstep (se 2 (by rfl) ⟨460842, by rfl⟩ : syracuseStep 1228913 = 921685) B921685
theorem B1228931 : Blo 542804 1228931 := bstep (se 1 (by rfl) ⟨921698, by rfl⟩ : syracuseStep 1228931 = 1843397) B1843397
theorem B1556621 : Blo 542804 1556621 := bstep (se 3 (by rfl) ⟨291866, by rfl⟩ : syracuseStep 1556621 = 583733) B583733
theorem B1032355 : Blo 542804 1032355 := bstep (se 1 (by rfl) ⟨774266, by rfl⟩ : syracuseStep 1032355 = 1548533) B1548533
theorem B1032401 : Blo 542804 1032401 := bstep (se 2 (by rfl) ⟨387150, by rfl⟩ : syracuseStep 1032401 = 774301) B774301
theorem B1163587 : Blo 542804 1163587 := bstep (se 1 (by rfl) ⟨872690, by rfl⟩ : syracuseStep 1163587 = 1745381) B1745381
theorem B1229201 : Blo 542804 1229201 := bstep (se 2 (by rfl) ⟨460950, by rfl⟩ : syracuseStep 1229201 = 921901) B921901
theorem B1229219 : Blo 542804 1229219 := bstep (se 1 (by rfl) ⟨921914, by rfl⟩ : syracuseStep 1229219 = 1843829) B1843829
theorem B1032689 : Blo 542804 1032689 := bstep (se 2 (by rfl) ⟨387258, by rfl⟩ : syracuseStep 1032689 = 774517) B774517
theorem B1229489 : Blo 542804 1229489 := bstep (se 2 (by rfl) ⟨461058, by rfl⟩ : syracuseStep 1229489 = 922117) B922117
theorem B1229507 : Blo 542804 1229507 := bstep (se 1 (by rfl) ⟨922130, by rfl⟩ : syracuseStep 1229507 = 1844261) B1844261
theorem B27214613 : Blo 542804 27214613 := bstep (se 6 (by rfl) ⟨637842, by rfl⟩ : syracuseStep 27214613 = 1275685) B1275685
theorem B1229777 : Blo 542804 1229777 := bstep (se 2 (by rfl) ⟨461166, by rfl⟩ : syracuseStep 1229777 = 922333) B922333
theorem B1229795 : Blo 542804 1229795 := bstep (se 1 (by rfl) ⟨922346, by rfl⟩ : syracuseStep 1229795 = 1844693) B1844693
theorem B1262659 : Blo 542804 1262659 := bstep (se 1 (by rfl) ⟨946994, by rfl⟩ : syracuseStep 1262659 = 1893989) B1893989
theorem B1393777 : Blo 542804 1393777 := bstep (se 2 (by rfl) ⟨522666, by rfl⟩ : syracuseStep 1393777 = 1045333) B1045333
theorem B7554161 : Blo 542804 7554161 := bstep (se 2 (by rfl) ⟨2832810, by rfl⟩ : syracuseStep 7554161 = 5665621) B5665621
theorem B1033411 : Blo 542804 1033411 := bstep (se 1 (by rfl) ⟨775058, by rfl⟩ : syracuseStep 1033411 = 1550117) B1550117
theorem B1230065 : Blo 542804 1230065 := bstep (se 2 (by rfl) ⟨461274, by rfl⟩ : syracuseStep 1230065 = 922549) B922549
theorem B1230083 : Blo 542804 1230083 := bstep (se 1 (by rfl) ⟨922562, by rfl⟩ : syracuseStep 1230083 = 1845125) B1845125
theorem B3491171 : Blo 542804 3491171 := bstep (se 1 (by rfl) ⟨2618378, by rfl⟩ : syracuseStep 3491171 = 5236757) B5236757
theorem B1394147 : Blo 542804 1394147 := bstep (se 1 (by rfl) ⟨1045610, by rfl⟩ : syracuseStep 1394147 = 2091221) B2091221
theorem B1164817 : Blo 542804 1164817 := bstep (se 2 (by rfl) ⟨436806, by rfl⟩ : syracuseStep 1164817 = 873613) B873613
theorem B1033859 : Blo 542804 1033859 := bstep (se 1 (by rfl) ⟨775394, by rfl⟩ : syracuseStep 1033859 = 1550789) B1550789
theorem B870115 : Blo 542804 870115 := bstep (se 1 (by rfl) ⟨652586, by rfl⟩ : syracuseStep 870115 = 1305173) B1305173
theorem B1394435 : Blo 542804 1394435 := bstep (se 1 (by rfl) ⟨1045826, by rfl⟩ : syracuseStep 1394435 = 2091653) B2091653
theorem B2934605 : Blo 542804 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B1034147 : Blo 542804 1034147 := bstep (se 1 (by rfl) ⟨775610, by rfl⟩ : syracuseStep 1034147 = 1551221) B1551221
theorem B542819 : Blo 542804 542819 := bstep (se 1 (by rfl) ⟨407114, by rfl⟩ : syracuseStep 542819 = 814229) B814229
theorem B542835 : Blo 542804 542835 := bstep (se 1 (by rfl) ⟨407126, by rfl⟩ : syracuseStep 542835 = 814253) B814253
theorem B542851 : Blo 542804 542851 := bstep (se 1 (by rfl) ⟨407138, by rfl⟩ : syracuseStep 542851 = 814277) B814277
theorem B542867 : Blo 542804 542867 := bstep (se 1 (by rfl) ⟨407150, by rfl⟩ : syracuseStep 542867 = 814301) B814301
theorem B542883 : Blo 542804 542883 := bstep (se 1 (by rfl) ⟨407162, by rfl⟩ : syracuseStep 542883 = 814325) B814325
theorem B542899 : Blo 542804 542899 := bstep (se 1 (by rfl) ⟨407174, by rfl⟩ : syracuseStep 542899 = 814349) B814349
theorem B542915 : Blo 542804 542915 := bstep (se 1 (by rfl) ⟨407186, by rfl⟩ : syracuseStep 542915 = 814373) B814373
theorem B542931 : Blo 542804 542931 := bstep (se 1 (by rfl) ⟨407198, by rfl⟩ : syracuseStep 542931 = 814397) B814397
theorem B542947 : Blo 542804 542947 := bstep (se 1 (by rfl) ⟨407210, by rfl⟩ : syracuseStep 542947 = 814421) B814421
theorem B3786979 : Blo 542804 3786979 := bstep (se 1 (by rfl) ⟨2840234, by rfl⟩ : syracuseStep 3786979 = 5680469) B5680469
theorem B542963 : Blo 542804 542963 := bstep (se 1 (by rfl) ⟨407222, by rfl⟩ : syracuseStep 542963 = 814445) B814445
theorem B542979 : Blo 542804 542979 := bstep (se 1 (by rfl) ⟨407234, by rfl⟩ : syracuseStep 542979 = 814469) B814469
theorem B542995 : Blo 542804 542995 := bstep (se 1 (by rfl) ⟨407246, by rfl⟩ : syracuseStep 542995 = 814493) B814493
theorem B543011 : Blo 542804 543011 := bstep (se 1 (by rfl) ⟨407258, by rfl⟩ : syracuseStep 543011 = 814517) B814517
theorem B1165603 : Blo 542804 1165603 := bstep (se 1 (by rfl) ⟨874202, by rfl⟩ : syracuseStep 1165603 = 1748405) B1748405
theorem B543027 : Blo 542804 543027 := bstep (se 1 (by rfl) ⟨407270, by rfl⟩ : syracuseStep 543027 = 814541) B814541
theorem B543043 : Blo 542804 543043 := bstep (se 1 (by rfl) ⟨407282, by rfl⟩ : syracuseStep 543043 = 814565) B814565
theorem B543059 : Blo 542804 543059 := bstep (se 1 (by rfl) ⟨407294, by rfl⟩ : syracuseStep 543059 = 814589) B814589
theorem B543075 : Blo 542804 543075 := bstep (se 1 (by rfl) ⟨407306, by rfl⟩ : syracuseStep 543075 = 814613) B814613
theorem B543091 : Blo 542804 543091 := bstep (se 1 (by rfl) ⟨407318, by rfl⟩ : syracuseStep 543091 = 814637) B814637
theorem B543107 : Blo 542804 543107 := bstep (se 1 (by rfl) ⟨407330, by rfl⟩ : syracuseStep 543107 = 814661) B814661
theorem B543123 : Blo 542804 543123 := bstep (se 1 (by rfl) ⟨407342, by rfl⟩ : syracuseStep 543123 = 814685) B814685
theorem B543139 : Blo 542804 543139 := bstep (se 1 (by rfl) ⟨407354, by rfl⟩ : syracuseStep 543139 = 814709) B814709
theorem B870833 : Blo 542804 870833 := bstep (se 2 (by rfl) ⟨326562, by rfl⟩ : syracuseStep 870833 = 653125) B653125
theorem B543155 : Blo 542804 543155 := bstep (se 1 (by rfl) ⟨407366, by rfl⟩ : syracuseStep 543155 = 814733) B814733
theorem B543171 : Blo 542804 543171 := bstep (se 1 (by rfl) ⟨407378, by rfl⟩ : syracuseStep 543171 = 814757) B814757
theorem B543187 : Blo 542804 543187 := bstep (se 1 (by rfl) ⟨407390, by rfl⟩ : syracuseStep 543187 = 814781) B814781
theorem B543203 : Blo 542804 543203 := bstep (se 1 (by rfl) ⟨407402, by rfl⟩ : syracuseStep 543203 = 814805) B814805
theorem B543219 : Blo 542804 543219 := bstep (se 1 (by rfl) ⟨407414, by rfl⟩ : syracuseStep 543219 = 814829) B814829
theorem B543235 : Blo 542804 543235 := bstep (se 1 (by rfl) ⟨407426, by rfl⟩ : syracuseStep 543235 = 814853) B814853
theorem B543251 : Blo 542804 543251 := bstep (se 1 (by rfl) ⟨407438, by rfl⟩ : syracuseStep 543251 = 814877) B814877
theorem B543267 : Blo 542804 543267 := bstep (se 1 (by rfl) ⟨407450, by rfl⟩ : syracuseStep 543267 = 814901) B814901
theorem B543283 : Blo 542804 543283 := bstep (se 1 (by rfl) ⟨407462, by rfl⟩ : syracuseStep 543283 = 814925) B814925
theorem B543299 : Blo 542804 543299 := bstep (se 1 (by rfl) ⟨407474, by rfl⟩ : syracuseStep 543299 = 814949) B814949
theorem B543315 : Blo 542804 543315 := bstep (se 1 (by rfl) ⟨407486, by rfl⟩ : syracuseStep 543315 = 814973) B814973
theorem B543331 : Blo 542804 543331 := bstep (se 1 (by rfl) ⟨407498, by rfl⟩ : syracuseStep 543331 = 814997) B814997
theorem B543347 : Blo 542804 543347 := bstep (se 1 (by rfl) ⟨407510, by rfl⟩ : syracuseStep 543347 = 815021) B815021
theorem B543363 : Blo 542804 543363 := bstep (se 1 (by rfl) ⟨407522, by rfl⟩ : syracuseStep 543363 = 815045) B815045
theorem B3361421 : Blo 542804 3361421 := bstep (se 3 (by rfl) ⟨630266, by rfl⟩ : syracuseStep 3361421 = 1260533) B1260533
theorem B543379 : Blo 542804 543379 := bstep (se 1 (by rfl) ⟨407534, by rfl⟩ : syracuseStep 543379 = 815069) B815069
theorem B543395 : Blo 542804 543395 := bstep (se 1 (by rfl) ⟨407546, by rfl⟩ : syracuseStep 543395 = 815093) B815093
theorem B543411 : Blo 542804 543411 := bstep (se 1 (by rfl) ⟨407558, by rfl⟩ : syracuseStep 543411 = 815117) B815117
theorem B543427 : Blo 542804 543427 := bstep (se 1 (by rfl) ⟨407570, by rfl⟩ : syracuseStep 543427 = 815141) B815141
theorem B3492557 : Blo 542804 3492557 := bstep (se 3 (by rfl) ⟨654854, by rfl⟩ : syracuseStep 3492557 = 1309709) B1309709
theorem B871121 : Blo 542804 871121 := bstep (se 2 (by rfl) ⟨326670, by rfl⟩ : syracuseStep 871121 = 653341) B653341
theorem B543443 : Blo 542804 543443 := bstep (se 1 (by rfl) ⟨407582, by rfl⟩ : syracuseStep 543443 = 815165) B815165
theorem B543459 : Blo 542804 543459 := bstep (se 1 (by rfl) ⟨407594, by rfl⟩ : syracuseStep 543459 = 815189) B815189
theorem B543475 : Blo 542804 543475 := bstep (se 1 (by rfl) ⟨407606, by rfl⟩ : syracuseStep 543475 = 815213) B815213
theorem B543491 : Blo 542804 543491 := bstep (se 1 (by rfl) ⟨407618, by rfl⟩ : syracuseStep 543491 = 815237) B815237
theorem B543507 : Blo 542804 543507 := bstep (se 1 (by rfl) ⟨407630, by rfl⟩ : syracuseStep 543507 = 815261) B815261
theorem B543523 : Blo 542804 543523 := bstep (se 1 (by rfl) ⟨407642, by rfl⟩ : syracuseStep 543523 = 815285) B815285
theorem B543539 : Blo 542804 543539 := bstep (se 1 (by rfl) ⟨407654, by rfl⟩ : syracuseStep 543539 = 815309) B815309
theorem B543555 : Blo 542804 543555 := bstep (se 1 (by rfl) ⟨407666, by rfl⟩ : syracuseStep 543555 = 815333) B815333
theorem B707395 : Blo 542804 707395 := bstep (se 1 (by rfl) ⟨530546, by rfl⟩ : syracuseStep 707395 = 1061093) B1061093
theorem B1035089 : Blo 542804 1035089 := bstep (se 2 (by rfl) ⟨388158, by rfl⟩ : syracuseStep 1035089 = 776317) B776317
theorem B543571 : Blo 542804 543571 := bstep (se 1 (by rfl) ⟨407678, by rfl⟩ : syracuseStep 543571 = 815357) B815357
theorem B543587 : Blo 542804 543587 := bstep (se 1 (by rfl) ⟨407690, by rfl⟩ : syracuseStep 543587 = 815381) B815381
theorem B543603 : Blo 542804 543603 := bstep (se 1 (by rfl) ⟨407702, by rfl⟩ : syracuseStep 543603 = 815405) B815405
theorem B543619 : Blo 542804 543619 := bstep (se 1 (by rfl) ⟨407714, by rfl⟩ : syracuseStep 543619 = 815429) B815429
theorem B543635 : Blo 542804 543635 := bstep (se 1 (by rfl) ⟨407726, by rfl⟩ : syracuseStep 543635 = 815453) B815453
theorem B543651 : Blo 542804 543651 := bstep (se 1 (by rfl) ⟨407738, by rfl⟩ : syracuseStep 543651 = 815477) B815477
theorem B871345 : Blo 542804 871345 := bstep (se 2 (by rfl) ⟨326754, by rfl⟩ : syracuseStep 871345 = 653509) B653509
theorem B543667 : Blo 542804 543667 := bstep (se 1 (by rfl) ⟨407750, by rfl⟩ : syracuseStep 543667 = 815501) B815501
theorem B773059 : Blo 542804 773059 := bstep (se 1 (by rfl) ⟨579794, by rfl⟩ : syracuseStep 773059 = 1159589) B1159589
theorem B543683 : Blo 542804 543683 := bstep (se 1 (by rfl) ⟨407762, by rfl⟩ : syracuseStep 543683 = 815525) B815525
theorem B543699 : Blo 542804 543699 := bstep (se 1 (by rfl) ⟨407774, by rfl⟩ : syracuseStep 543699 = 815549) B815549
theorem B543715 : Blo 542804 543715 := bstep (se 1 (by rfl) ⟨407786, by rfl⟩ : syracuseStep 543715 = 815573) B815573
theorem B1166321 : Blo 542804 1166321 := bstep (se 2 (by rfl) ⟨437370, by rfl⟩ : syracuseStep 1166321 = 874741) B874741
theorem B543731 : Blo 542804 543731 := bstep (se 1 (by rfl) ⟨407798, by rfl⟩ : syracuseStep 543731 = 815597) B815597
theorem B543747 : Blo 542804 543747 := bstep (se 1 (by rfl) ⟨407810, by rfl⟩ : syracuseStep 543747 = 815621) B815621
theorem B543763 : Blo 542804 543763 := bstep (se 1 (by rfl) ⟨407822, by rfl⟩ : syracuseStep 543763 = 815645) B815645
theorem B543779 : Blo 542804 543779 := bstep (se 1 (by rfl) ⟨407834, by rfl⟩ : syracuseStep 543779 = 815669) B815669
theorem B543795 : Blo 542804 543795 := bstep (se 1 (by rfl) ⟨407846, by rfl⟩ : syracuseStep 543795 = 815693) B815693
theorem B543811 : Blo 542804 543811 := bstep (se 1 (by rfl) ⟨407858, by rfl⟩ : syracuseStep 543811 = 815717) B815717
theorem B3918917 : Blo 542804 3918917 := bstep (se 4 (by rfl) ⟨367398, by rfl⟩ : syracuseStep 3918917 = 734797) B734797
theorem B543827 : Blo 542804 543827 := bstep (se 1 (by rfl) ⟨407870, by rfl⟩ : syracuseStep 543827 = 815741) B815741
theorem B543843 : Blo 542804 543843 := bstep (se 1 (by rfl) ⟨407882, by rfl⟩ : syracuseStep 543843 = 815765) B815765
theorem B543859 : Blo 542804 543859 := bstep (se 1 (by rfl) ⟨407894, by rfl⟩ : syracuseStep 543859 = 815789) B815789
theorem B543875 : Blo 542804 543875 := bstep (se 1 (by rfl) ⟨407906, by rfl⟩ : syracuseStep 543875 = 815813) B815813
theorem B543891 : Blo 542804 543891 := bstep (se 1 (by rfl) ⟨407918, by rfl⟩ : syracuseStep 543891 = 815837) B815837
theorem B543907 : Blo 542804 543907 := bstep (se 1 (by rfl) ⟨407930, by rfl⟩ : syracuseStep 543907 = 815861) B815861
theorem B543923 : Blo 542804 543923 := bstep (se 1 (by rfl) ⟨407942, by rfl⟩ : syracuseStep 543923 = 815885) B815885
theorem B543939 : Blo 542804 543939 := bstep (se 1 (by rfl) ⟨407954, by rfl⟩ : syracuseStep 543939 = 815909) B815909
theorem B543955 : Blo 542804 543955 := bstep (se 1 (by rfl) ⟨407966, by rfl⟩ : syracuseStep 543955 = 815933) B815933
theorem B543971 : Blo 542804 543971 := bstep (se 1 (by rfl) ⟨407978, by rfl⟩ : syracuseStep 543971 = 815957) B815957
theorem B543987 : Blo 542804 543987 := bstep (se 1 (by rfl) ⟨407990, by rfl⟩ : syracuseStep 543987 = 815981) B815981
theorem B544003 : Blo 542804 544003 := bstep (se 1 (by rfl) ⟨408002, by rfl⟩ : syracuseStep 544003 = 816005) B816005
theorem B6638861 : Blo 542804 6638861 := bstep (se 3 (by rfl) ⟨1244786, by rfl⟩ : syracuseStep 6638861 = 2489573) B2489573
theorem B544019 : Blo 542804 544019 := bstep (se 1 (by rfl) ⟨408014, by rfl⟩ : syracuseStep 544019 = 816029) B816029
theorem B544035 : Blo 542804 544035 := bstep (se 1 (by rfl) ⟨408026, by rfl⟩ : syracuseStep 544035 = 816053) B816053
theorem B544051 : Blo 542804 544051 := bstep (se 1 (by rfl) ⟨408038, by rfl⟩ : syracuseStep 544051 = 816077) B816077
theorem B544067 : Blo 542804 544067 := bstep (se 1 (by rfl) ⟨408050, by rfl⟩ : syracuseStep 544067 = 816101) B816101
theorem B544083 : Blo 542804 544083 := bstep (se 1 (by rfl) ⟨408062, by rfl⟩ : syracuseStep 544083 = 816125) B816125
theorem B544099 : Blo 542804 544099 := bstep (se 1 (by rfl) ⟨408074, by rfl⟩ : syracuseStep 544099 = 816149) B816149
theorem B544115 : Blo 542804 544115 := bstep (se 1 (by rfl) ⟨408086, by rfl⟩ : syracuseStep 544115 = 816173) B816173
theorem B544131 : Blo 542804 544131 := bstep (se 1 (by rfl) ⟨408098, by rfl⟩ : syracuseStep 544131 = 816197) B816197
theorem B544147 : Blo 542804 544147 := bstep (se 1 (by rfl) ⟨408110, by rfl⟩ : syracuseStep 544147 = 816221) B816221
theorem B544163 : Blo 542804 544163 := bstep (se 1 (by rfl) ⟨408122, by rfl⟩ : syracuseStep 544163 = 816245) B816245
theorem B544179 : Blo 542804 544179 := bstep (se 1 (by rfl) ⟨408134, by rfl⟩ : syracuseStep 544179 = 816269) B816269
theorem B544195 : Blo 542804 544195 := bstep (se 1 (by rfl) ⟨408146, by rfl⟩ : syracuseStep 544195 = 816293) B816293
theorem B544211 : Blo 542804 544211 := bstep (se 1 (by rfl) ⟨408158, by rfl⟩ : syracuseStep 544211 = 816317) B816317
theorem B544227 : Blo 542804 544227 := bstep (se 1 (by rfl) ⟨408170, by rfl⟩ : syracuseStep 544227 = 816341) B816341
theorem B1166833 : Blo 542804 1166833 := bstep (se 2 (by rfl) ⟨437562, by rfl⟩ : syracuseStep 1166833 = 875125) B875125
theorem B544243 : Blo 542804 544243 := bstep (se 1 (by rfl) ⟨408182, by rfl⟩ : syracuseStep 544243 = 816365) B816365
theorem B544259 : Blo 542804 544259 := bstep (se 1 (by rfl) ⟨408194, by rfl⟩ : syracuseStep 544259 = 816389) B816389
theorem B544275 : Blo 542804 544275 := bstep (se 1 (by rfl) ⟨408206, by rfl⟩ : syracuseStep 544275 = 816413) B816413
theorem B544291 : Blo 542804 544291 := bstep (se 1 (by rfl) ⟨408218, by rfl⟩ : syracuseStep 544291 = 816437) B816437
theorem B544307 : Blo 542804 544307 := bstep (se 1 (by rfl) ⟨408230, by rfl⟩ : syracuseStep 544307 = 816461) B816461
theorem B544323 : Blo 542804 544323 := bstep (se 1 (by rfl) ⟨408242, by rfl⟩ : syracuseStep 544323 = 816485) B816485
theorem B544339 : Blo 542804 544339 := bstep (se 1 (by rfl) ⟨408254, by rfl⟩ : syracuseStep 544339 = 816509) B816509
theorem B544355 : Blo 542804 544355 := bstep (se 1 (by rfl) ⟨408266, by rfl⟩ : syracuseStep 544355 = 816533) B816533
theorem B544371 : Blo 542804 544371 := bstep (se 1 (by rfl) ⟨408278, by rfl⟩ : syracuseStep 544371 = 816557) B816557
theorem B544387 : Blo 542804 544387 := bstep (se 1 (by rfl) ⟨408290, by rfl⟩ : syracuseStep 544387 = 816581) B816581
theorem B3100301 : Blo 542804 3100301 := bstep (se 3 (by rfl) ⟨581306, by rfl⟩ : syracuseStep 3100301 = 1162613) B1162613
theorem B544403 : Blo 542804 544403 := bstep (se 1 (by rfl) ⟨408302, by rfl⟩ : syracuseStep 544403 = 816605) B816605
theorem B544419 : Blo 542804 544419 := bstep (se 1 (by rfl) ⟨408314, by rfl⟩ : syracuseStep 544419 = 816629) B816629
theorem B544435 : Blo 542804 544435 := bstep (se 1 (by rfl) ⟨408326, by rfl⟩ : syracuseStep 544435 = 816653) B816653
theorem B544451 : Blo 542804 544451 := bstep (se 1 (by rfl) ⟨408338, by rfl⟩ : syracuseStep 544451 = 816677) B816677
theorem B1035985 : Blo 542804 1035985 := bstep (se 2 (by rfl) ⟨388494, by rfl⟩ : syracuseStep 1035985 = 776989) B776989
theorem B544467 : Blo 542804 544467 := bstep (se 1 (by rfl) ⟨408350, by rfl⟩ : syracuseStep 544467 = 816701) B816701
theorem B544483 : Blo 542804 544483 := bstep (se 1 (by rfl) ⟨408362, by rfl⟩ : syracuseStep 544483 = 816725) B816725
theorem B544499 : Blo 542804 544499 := bstep (se 1 (by rfl) ⟨408374, by rfl⟩ : syracuseStep 544499 = 816749) B816749
theorem B544515 : Blo 542804 544515 := bstep (se 1 (by rfl) ⟨408386, by rfl⟩ : syracuseStep 544515 = 816773) B816773
theorem B544531 : Blo 542804 544531 := bstep (se 1 (by rfl) ⟨408398, by rfl⟩ : syracuseStep 544531 = 816797) B816797
theorem B544547 : Blo 542804 544547 := bstep (se 1 (by rfl) ⟨408410, by rfl⟩ : syracuseStep 544547 = 816821) B816821
theorem B544563 : Blo 542804 544563 := bstep (se 1 (by rfl) ⟨408422, by rfl⟩ : syracuseStep 544563 = 816845) B816845
theorem B544579 : Blo 542804 544579 := bstep (se 1 (by rfl) ⟨408434, by rfl⟩ : syracuseStep 544579 = 816869) B816869
theorem B544595 : Blo 542804 544595 := bstep (se 1 (by rfl) ⟨408446, by rfl⟩ : syracuseStep 544595 = 816893) B816893
theorem B544611 : Blo 542804 544611 := bstep (se 1 (by rfl) ⟨408458, by rfl⟩ : syracuseStep 544611 = 816917) B816917
theorem B1036145 : Blo 542804 1036145 := bstep (se 2 (by rfl) ⟨388554, by rfl⟩ : syracuseStep 1036145 = 777109) B777109
theorem B544627 : Blo 542804 544627 := bstep (se 1 (by rfl) ⟨408470, by rfl⟩ : syracuseStep 544627 = 816941) B816941
theorem B544643 : Blo 542804 544643 := bstep (se 1 (by rfl) ⟨408482, by rfl⟩ : syracuseStep 544643 = 816965) B816965
theorem B544659 : Blo 542804 544659 := bstep (se 1 (by rfl) ⟨408494, by rfl⟩ : syracuseStep 544659 = 816989) B816989
theorem B544675 : Blo 542804 544675 := bstep (se 1 (by rfl) ⟨408506, by rfl⟩ : syracuseStep 544675 = 817013) B817013
theorem B544691 : Blo 542804 544691 := bstep (se 1 (by rfl) ⟨408518, by rfl⟩ : syracuseStep 544691 = 817037) B817037
theorem B544707 : Blo 542804 544707 := bstep (se 1 (by rfl) ⟨408530, by rfl⟩ : syracuseStep 544707 = 817061) B817061
theorem B544723 : Blo 542804 544723 := bstep (se 1 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 544723 = 817085) B817085
theorem B544739 : Blo 542804 544739 := bstep (se 1 (by rfl) ⟨408554, by rfl⟩ : syracuseStep 544739 = 817109) B817109
theorem B544755 : Blo 542804 544755 := bstep (se 1 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 544755 = 817133) B817133
theorem B544771 : Blo 542804 544771 := bstep (se 1 (by rfl) ⟨408578, by rfl⟩ : syracuseStep 544771 = 817157) B817157
theorem B544787 : Blo 542804 544787 := bstep (se 1 (by rfl) ⟨408590, by rfl⟩ : syracuseStep 544787 = 817181) B817181
theorem B544803 : Blo 542804 544803 := bstep (se 1 (by rfl) ⟨408602, by rfl⟩ : syracuseStep 544803 = 817205) B817205
theorem B774193 : Blo 542804 774193 := bstep (se 2 (by rfl) ⟨290322, by rfl⟩ : syracuseStep 774193 = 580645) B580645
theorem B544819 : Blo 542804 544819 := bstep (se 1 (by rfl) ⟨408614, by rfl⟩ : syracuseStep 544819 = 817229) B817229
theorem B544835 : Blo 542804 544835 := bstep (se 1 (by rfl) ⟨408626, by rfl⟩ : syracuseStep 544835 = 817253) B817253
theorem B544851 : Blo 542804 544851 := bstep (se 1 (by rfl) ⟨408638, by rfl⟩ : syracuseStep 544851 = 817277) B817277
theorem B544867 : Blo 542804 544867 := bstep (se 1 (by rfl) ⟨408650, by rfl⟩ : syracuseStep 544867 = 817301) B817301
theorem B1101937 : Blo 542804 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B544883 : Blo 542804 544883 := bstep (se 1 (by rfl) ⟨408662, by rfl⟩ : syracuseStep 544883 = 817325) B817325
theorem B544899 : Blo 542804 544899 := bstep (se 1 (by rfl) ⟨408674, by rfl⟩ : syracuseStep 544899 = 817349) B817349
theorem B774289 : Blo 542804 774289 := bstep (se 2 (by rfl) ⟨290358, by rfl⟩ : syracuseStep 774289 = 580717) B580717
theorem B544915 : Blo 542804 544915 := bstep (se 1 (by rfl) ⟨408686, by rfl⟩ : syracuseStep 544915 = 817373) B817373
theorem B544931 : Blo 542804 544931 := bstep (se 1 (by rfl) ⟨408698, by rfl⟩ : syracuseStep 544931 = 817397) B817397
theorem B544947 : Blo 542804 544947 := bstep (se 1 (by rfl) ⟨408710, by rfl⟩ : syracuseStep 544947 = 817421) B817421
theorem B544963 : Blo 542804 544963 := bstep (se 1 (by rfl) ⟨408722, by rfl⟩ : syracuseStep 544963 = 817445) B817445
theorem B544979 : Blo 542804 544979 := bstep (se 1 (by rfl) ⟨408734, by rfl⟩ : syracuseStep 544979 = 817469) B817469
theorem B544995 : Blo 542804 544995 := bstep (se 1 (by rfl) ⟨408746, by rfl⟩ : syracuseStep 544995 = 817493) B817493
theorem B545011 : Blo 542804 545011 := bstep (se 1 (by rfl) ⟨408758, by rfl⟩ : syracuseStep 545011 = 817517) B817517
theorem B545027 : Blo 542804 545027 := bstep (se 1 (by rfl) ⟨408770, by rfl⟩ : syracuseStep 545027 = 817541) B817541
theorem B1036547 : Blo 542804 1036547 := bstep (se 1 (by rfl) ⟨777410, by rfl⟩ : syracuseStep 1036547 = 1554821) B1554821
theorem B545043 : Blo 542804 545043 := bstep (se 1 (by rfl) ⟨408782, by rfl⟩ : syracuseStep 545043 = 817565) B817565
theorem B545059 : Blo 542804 545059 := bstep (se 1 (by rfl) ⟨408794, by rfl⟩ : syracuseStep 545059 = 817589) B817589
theorem B1364273 : Blo 542804 1364273 := bstep (se 2 (by rfl) ⟨511602, by rfl⟩ : syracuseStep 1364273 = 1023205) B1023205
theorem B545075 : Blo 542804 545075 := bstep (se 1 (by rfl) ⟨408806, by rfl⟩ : syracuseStep 545075 = 817613) B817613
theorem B545091 : Blo 542804 545091 := bstep (se 1 (by rfl) ⟨408818, by rfl⟩ : syracuseStep 545091 = 817637) B817637
theorem B545107 : Blo 542804 545107 := bstep (se 1 (by rfl) ⟨408830, by rfl⟩ : syracuseStep 545107 = 817661) B817661
theorem B545123 : Blo 542804 545123 := bstep (se 1 (by rfl) ⟨408842, by rfl⟩ : syracuseStep 545123 = 817685) B817685
theorem B545139 : Blo 542804 545139 := bstep (se 1 (by rfl) ⟨408854, by rfl⟩ : syracuseStep 545139 = 817709) B817709
theorem B545155 : Blo 542804 545155 := bstep (se 1 (by rfl) ⟨408866, by rfl⟩ : syracuseStep 545155 = 817733) B817733
theorem B545171 : Blo 542804 545171 := bstep (se 1 (by rfl) ⟨408878, by rfl⟩ : syracuseStep 545171 = 817757) B817757
theorem B545187 : Blo 542804 545187 := bstep (se 1 (by rfl) ⟨408890, by rfl⟩ : syracuseStep 545187 = 817781) B817781
theorem B545203 : Blo 542804 545203 := bstep (se 1 (by rfl) ⟨408902, by rfl⟩ : syracuseStep 545203 = 817805) B817805
theorem B545219 : Blo 542804 545219 := bstep (se 1 (by rfl) ⟨408914, by rfl⟩ : syracuseStep 545219 = 817829) B817829
theorem B610771 : Blo 542804 610771 := bstep (se 1 (by rfl) ⟨458078, by rfl⟩ : syracuseStep 610771 = 916157) B916157
theorem B545235 : Blo 542804 545235 := bstep (se 1 (by rfl) ⟨408926, by rfl⟩ : syracuseStep 545235 = 817853) B817853
theorem B545251 : Blo 542804 545251 := bstep (se 1 (by rfl) ⟨408938, by rfl⟩ : syracuseStep 545251 = 817877) B817877
theorem B1495523 : Blo 542804 1495523 := bstep (se 1 (by rfl) ⟨1121642, by rfl⟩ : syracuseStep 1495523 = 2243285) B2243285
theorem B872947 : Blo 542804 872947 := bstep (se 1 (by rfl) ⟨654710, by rfl⟩ : syracuseStep 872947 = 1309421) B1309421
theorem B545267 : Blo 542804 545267 := bstep (se 1 (by rfl) ⟨408950, by rfl⟩ : syracuseStep 545267 = 817901) B817901
theorem B545283 : Blo 542804 545283 := bstep (se 1 (by rfl) ⟨408962, by rfl⟩ : syracuseStep 545283 = 817925) B817925
theorem B545299 : Blo 542804 545299 := bstep (se 1 (by rfl) ⟨408974, by rfl⟩ : syracuseStep 545299 = 817949) B817949
theorem B545315 : Blo 542804 545315 := bstep (se 1 (by rfl) ⟨408986, by rfl⟩ : syracuseStep 545315 = 817973) B817973
theorem B545331 : Blo 542804 545331 := bstep (se 1 (by rfl) ⟨408998, by rfl⟩ : syracuseStep 545331 = 817997) B817997
theorem B545347 : Blo 542804 545347 := bstep (se 1 (by rfl) ⟨409010, by rfl⟩ : syracuseStep 545347 = 818021) B818021
theorem B3723853 : Blo 542804 3723853 := bstep (se 3 (by rfl) ⟨698222, by rfl⟩ : syracuseStep 3723853 = 1396445) B1396445
theorem B545363 : Blo 542804 545363 := bstep (se 1 (by rfl) ⟨409022, by rfl⟩ : syracuseStep 545363 = 818045) B818045
theorem B610915 : Blo 542804 610915 := bstep (se 1 (by rfl) ⟨458186, by rfl⟩ : syracuseStep 610915 = 916373) B916373
theorem B545379 : Blo 542804 545379 := bstep (se 1 (by rfl) ⟨409034, by rfl⟩ : syracuseStep 545379 = 818069) B818069
theorem B545395 : Blo 542804 545395 := bstep (se 1 (by rfl) ⟨409046, by rfl⟩ : syracuseStep 545395 = 818093) B818093
theorem B774785 : Blo 542804 774785 := bstep (se 2 (by rfl) ⟨290544, by rfl⟩ : syracuseStep 774785 = 581089) B581089
theorem B545411 : Blo 542804 545411 := bstep (se 1 (by rfl) ⟨409058, by rfl⟩ : syracuseStep 545411 = 818117) B818117
theorem B545427 : Blo 542804 545427 := bstep (se 1 (by rfl) ⟨409070, by rfl⟩ : syracuseStep 545427 = 818141) B818141
theorem B545443 : Blo 542804 545443 := bstep (se 1 (by rfl) ⟨409082, by rfl⟩ : syracuseStep 545443 = 818165) B818165
theorem B545459 : Blo 542804 545459 := bstep (se 1 (by rfl) ⟨409094, by rfl⟩ : syracuseStep 545459 = 818189) B818189
theorem B545475 : Blo 542804 545475 := bstep (se 1 (by rfl) ⟨409106, by rfl⟩ : syracuseStep 545475 = 818213) B818213
theorem B545491 : Blo 542804 545491 := bstep (se 1 (by rfl) ⟨409118, by rfl⟩ : syracuseStep 545491 = 818237) B818237
theorem B545507 : Blo 542804 545507 := bstep (se 1 (by rfl) ⟨409130, by rfl⟩ : syracuseStep 545507 = 818261) B818261
theorem B611059 : Blo 542804 611059 := bstep (se 1 (by rfl) ⟨458294, by rfl⟩ : syracuseStep 611059 = 916589) B916589
theorem B545523 : Blo 542804 545523 := bstep (se 1 (by rfl) ⟨409142, by rfl⟩ : syracuseStep 545523 = 818285) B818285
theorem B545539 : Blo 542804 545539 := bstep (se 1 (by rfl) ⟨409154, by rfl⟩ : syracuseStep 545539 = 818309) B818309
theorem B545555 : Blo 542804 545555 := bstep (se 1 (by rfl) ⟨409166, by rfl⟩ : syracuseStep 545555 = 818333) B818333
theorem B545571 : Blo 542804 545571 := bstep (se 1 (by rfl) ⟨409178, by rfl⟩ : syracuseStep 545571 = 818357) B818357
theorem B2216753 : Blo 542804 2216753 := bstep (se 2 (by rfl) ⟨831282, by rfl⟩ : syracuseStep 2216753 = 1662565) B1662565
theorem B545587 : Blo 542804 545587 := bstep (se 1 (by rfl) ⟨409190, by rfl⟩ : syracuseStep 545587 = 818381) B818381
theorem B545603 : Blo 542804 545603 := bstep (se 1 (by rfl) ⟨409202, by rfl⟩ : syracuseStep 545603 = 818405) B818405
theorem B545619 : Blo 542804 545619 := bstep (se 1 (by rfl) ⟨409214, by rfl⟩ : syracuseStep 545619 = 818429) B818429
theorem B545635 : Blo 542804 545635 := bstep (se 1 (by rfl) ⟨409226, by rfl⟩ : syracuseStep 545635 = 818453) B818453
theorem B545651 : Blo 542804 545651 := bstep (se 1 (by rfl) ⟨409238, by rfl⟩ : syracuseStep 545651 = 818477) B818477
theorem B611203 : Blo 542804 611203 := bstep (se 1 (by rfl) ⟨458402, by rfl⟩ : syracuseStep 611203 = 916805) B916805
theorem B545667 : Blo 542804 545667 := bstep (se 1 (by rfl) ⟨409250, by rfl⟩ : syracuseStep 545667 = 818501) B818501
theorem B545683 : Blo 542804 545683 := bstep (se 1 (by rfl) ⟨409262, by rfl⟩ : syracuseStep 545683 = 818525) B818525
theorem B807841 : Blo 542804 807841 := bstep (se 2 (by rfl) ⟨302940, by rfl⟩ : syracuseStep 807841 = 605881) B605881
theorem B545699 : Blo 542804 545699 := bstep (se 1 (by rfl) ⟨409274, by rfl⟩ : syracuseStep 545699 = 818549) B818549
theorem B545715 : Blo 542804 545715 := bstep (se 1 (by rfl) ⟨409286, by rfl⟩ : syracuseStep 545715 = 818573) B818573
theorem B545731 : Blo 542804 545731 := bstep (se 1 (by rfl) ⟨409298, by rfl⟩ : syracuseStep 545731 = 818597) B818597
theorem B545747 : Blo 542804 545747 := bstep (se 1 (by rfl) ⟨409310, by rfl⟩ : syracuseStep 545747 = 818621) B818621
theorem B906209 : Blo 542804 906209 := bstep (se 2 (by rfl) ⟨339828, by rfl⟩ : syracuseStep 906209 = 679657) B679657
theorem B545763 : Blo 542804 545763 := bstep (se 1 (by rfl) ⟨409322, by rfl⟩ : syracuseStep 545763 = 818645) B818645
theorem B545779 : Blo 542804 545779 := bstep (se 1 (by rfl) ⟨409334, by rfl⟩ : syracuseStep 545779 = 818669) B818669
theorem B545795 : Blo 542804 545795 := bstep (se 1 (by rfl) ⟨409346, by rfl⟩ : syracuseStep 545795 = 818693) B818693
theorem B611347 : Blo 542804 611347 := bstep (se 1 (by rfl) ⟨458510, by rfl⟩ : syracuseStep 611347 = 917021) B917021
theorem B545811 : Blo 542804 545811 := bstep (se 1 (by rfl) ⟨409358, by rfl⟩ : syracuseStep 545811 = 818717) B818717
theorem B545827 : Blo 542804 545827 := bstep (se 1 (by rfl) ⟨409370, by rfl⟩ : syracuseStep 545827 = 818741) B818741
theorem B545843 : Blo 542804 545843 := bstep (se 1 (by rfl) ⟨409382, by rfl⟩ : syracuseStep 545843 = 818765) B818765
theorem B545859 : Blo 542804 545859 := bstep (se 1 (by rfl) ⟨409394, by rfl⟩ : syracuseStep 545859 = 818789) B818789
theorem B545875 : Blo 542804 545875 := bstep (se 1 (by rfl) ⟨409406, by rfl⟩ : syracuseStep 545875 = 818813) B818813
theorem B545891 : Blo 542804 545891 := bstep (se 1 (by rfl) ⟨409418, by rfl⟩ : syracuseStep 545891 = 818837) B818837
theorem B545907 : Blo 542804 545907 := bstep (se 1 (by rfl) ⟨409430, by rfl⟩ : syracuseStep 545907 = 818861) B818861
theorem B545923 : Blo 542804 545923 := bstep (se 1 (by rfl) ⟨409442, by rfl⟩ : syracuseStep 545923 = 818885) B818885
theorem B1037443 : Blo 542804 1037443 := bstep (se 1 (by rfl) ⟨778082, by rfl⟩ : syracuseStep 1037443 = 1556165) B1556165
theorem B545939 : Blo 542804 545939 := bstep (se 1 (by rfl) ⟨409454, by rfl⟩ : syracuseStep 545939 = 818909) B818909
theorem B611491 : Blo 542804 611491 := bstep (se 1 (by rfl) ⟨458618, by rfl⟩ : syracuseStep 611491 = 917237) B917237
theorem B545955 : Blo 542804 545955 := bstep (se 1 (by rfl) ⟨409466, by rfl⟩ : syracuseStep 545955 = 818933) B818933
theorem B545971 : Blo 542804 545971 := bstep (se 1 (by rfl) ⟨409478, by rfl⟩ : syracuseStep 545971 = 818957) B818957
theorem B1135811 : Blo 542804 1135811 := bstep (se 1 (by rfl) ⟨851858, by rfl⟩ : syracuseStep 1135811 = 1703717) B1703717
theorem B545987 : Blo 542804 545987 := bstep (se 1 (by rfl) ⟨409490, by rfl⟩ : syracuseStep 545987 = 818981) B818981
theorem B546003 : Blo 542804 546003 := bstep (se 1 (by rfl) ⟨409502, by rfl⟩ : syracuseStep 546003 = 819005) B819005
theorem B546019 : Blo 542804 546019 := bstep (se 1 (by rfl) ⟨409514, by rfl⟩ : syracuseStep 546019 = 819029) B819029
theorem B546035 : Blo 542804 546035 := bstep (se 1 (by rfl) ⟨409526, by rfl⟩ : syracuseStep 546035 = 819053) B819053
theorem B546051 : Blo 542804 546051 := bstep (se 1 (by rfl) ⟨409538, by rfl⟩ : syracuseStep 546051 = 819077) B819077
theorem B546067 : Blo 542804 546067 := bstep (se 1 (by rfl) ⟨409550, by rfl⟩ : syracuseStep 546067 = 819101) B819101
theorem B546083 : Blo 542804 546083 := bstep (se 1 (by rfl) ⟨409562, by rfl⟩ : syracuseStep 546083 = 819125) B819125
theorem B1037603 : Blo 542804 1037603 := bstep (se 1 (by rfl) ⟨778202, by rfl⟩ : syracuseStep 1037603 = 1556405) B1556405
theorem B611635 : Blo 542804 611635 := bstep (se 1 (by rfl) ⟨458726, by rfl⟩ : syracuseStep 611635 = 917453) B917453
theorem B546099 : Blo 542804 546099 := bstep (se 1 (by rfl) ⟨409574, by rfl⟩ : syracuseStep 546099 = 819149) B819149
theorem B546115 : Blo 542804 546115 := bstep (se 1 (by rfl) ⟨409586, by rfl⟩ : syracuseStep 546115 = 819173) B819173
theorem B546131 : Blo 542804 546131 := bstep (se 1 (by rfl) ⟨409598, by rfl⟩ : syracuseStep 546131 = 819197) B819197
theorem B546147 : Blo 542804 546147 := bstep (se 1 (by rfl) ⟨409610, by rfl⟩ : syracuseStep 546147 = 819221) B819221
theorem B546163 : Blo 542804 546163 := bstep (se 1 (by rfl) ⟨409622, by rfl⟩ : syracuseStep 546163 = 819245) B819245
theorem B546179 : Blo 542804 546179 := bstep (se 1 (by rfl) ⟨409634, by rfl⟩ : syracuseStep 546179 = 819269) B819269
theorem B546195 : Blo 542804 546195 := bstep (se 1 (by rfl) ⟨409646, by rfl⟩ : syracuseStep 546195 = 819293) B819293
theorem B546211 : Blo 542804 546211 := bstep (se 1 (by rfl) ⟨409658, by rfl⟩ : syracuseStep 546211 = 819317) B819317
theorem B546227 : Blo 542804 546227 := bstep (se 1 (by rfl) ⟨409670, by rfl⟩ : syracuseStep 546227 = 819341) B819341
theorem B611779 : Blo 542804 611779 := bstep (se 1 (by rfl) ⟨458834, by rfl⟩ : syracuseStep 611779 = 917669) B917669
theorem B546243 : Blo 542804 546243 := bstep (se 1 (by rfl) ⟨409682, by rfl⟩ : syracuseStep 546243 = 819365) B819365
theorem B546259 : Blo 542804 546259 := bstep (se 1 (by rfl) ⟨409694, by rfl⟩ : syracuseStep 546259 = 819389) B819389
theorem B775651 : Blo 542804 775651 := bstep (se 1 (by rfl) ⟨581738, by rfl⟩ : syracuseStep 775651 = 1163477) B1163477
theorem B546275 : Blo 542804 546275 := bstep (se 1 (by rfl) ⟨409706, by rfl⟩ : syracuseStep 546275 = 819413) B819413
theorem B546291 : Blo 542804 546291 := bstep (se 1 (by rfl) ⟨409718, by rfl⟩ : syracuseStep 546291 = 819437) B819437
theorem B546307 : Blo 542804 546307 := bstep (se 1 (by rfl) ⟨409730, by rfl⟩ : syracuseStep 546307 = 819461) B819461
theorem B546323 : Blo 542804 546323 := bstep (se 1 (by rfl) ⟨409742, by rfl⟩ : syracuseStep 546323 = 819485) B819485
theorem B546339 : Blo 542804 546339 := bstep (se 1 (by rfl) ⟨409754, by rfl⟩ : syracuseStep 546339 = 819509) B819509
theorem B546355 : Blo 542804 546355 := bstep (se 1 (by rfl) ⟨409766, by rfl⟩ : syracuseStep 546355 = 819533) B819533
theorem B775747 : Blo 542804 775747 := bstep (se 1 (by rfl) ⟨581810, by rfl⟩ : syracuseStep 775747 = 1163621) B1163621
theorem B546371 : Blo 542804 546371 := bstep (se 1 (by rfl) ⟨409778, by rfl⟩ : syracuseStep 546371 = 819557) B819557
theorem B611923 : Blo 542804 611923 := bstep (se 1 (by rfl) ⟨458942, by rfl⟩ : syracuseStep 611923 = 917885) B917885
theorem B546387 : Blo 542804 546387 := bstep (se 1 (by rfl) ⟨409790, by rfl⟩ : syracuseStep 546387 = 819581) B819581
theorem B546403 : Blo 542804 546403 := bstep (se 1 (by rfl) ⟨409802, by rfl⟩ : syracuseStep 546403 = 819605) B819605
theorem B546419 : Blo 542804 546419 := bstep (se 1 (by rfl) ⟨409814, by rfl⟩ : syracuseStep 546419 = 819629) B819629
theorem B546435 : Blo 542804 546435 := bstep (se 1 (by rfl) ⟨409826, by rfl⟩ : syracuseStep 546435 = 819653) B819653
theorem B4150925 : Blo 542804 4150925 := bstep (se 3 (by rfl) ⟨778298, by rfl⟩ : syracuseStep 4150925 = 1556597) B1556597
theorem B546451 : Blo 542804 546451 := bstep (se 1 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 546451 = 819677) B819677
theorem B546467 : Blo 542804 546467 := bstep (se 1 (by rfl) ⟨409850, by rfl⟩ : syracuseStep 546467 = 819701) B819701
theorem B546483 : Blo 542804 546483 := bstep (se 1 (by rfl) ⟨409862, by rfl⟩ : syracuseStep 546483 = 819725) B819725
theorem B546499 : Blo 542804 546499 := bstep (se 1 (by rfl) ⟨409874, by rfl⟩ : syracuseStep 546499 = 819749) B819749
theorem B546515 : Blo 542804 546515 := bstep (se 1 (by rfl) ⟨409886, by rfl⟩ : syracuseStep 546515 = 819773) B819773
theorem B612067 : Blo 542804 612067 := bstep (se 1 (by rfl) ⟨459050, by rfl⟩ : syracuseStep 612067 = 918101) B918101
theorem B546531 : Blo 542804 546531 := bstep (se 1 (by rfl) ⟨409898, by rfl⟩ : syracuseStep 546531 = 819797) B819797
theorem B546547 : Blo 542804 546547 := bstep (se 1 (by rfl) ⟨409910, by rfl⟩ : syracuseStep 546547 = 819821) B819821
theorem B546563 : Blo 542804 546563 := bstep (se 1 (by rfl) ⟨409922, by rfl⟩ : syracuseStep 546563 = 819845) B819845
theorem B546579 : Blo 542804 546579 := bstep (se 1 (by rfl) ⟨409934, by rfl⟩ : syracuseStep 546579 = 819869) B819869
theorem B546595 : Blo 542804 546595 := bstep (se 1 (by rfl) ⟨409946, by rfl⟩ : syracuseStep 546595 = 819893) B819893
theorem B546611 : Blo 542804 546611 := bstep (se 1 (by rfl) ⟨409958, by rfl⟩ : syracuseStep 546611 = 819917) B819917
theorem B546627 : Blo 542804 546627 := bstep (se 1 (by rfl) ⟨409970, by rfl⟩ : syracuseStep 546627 = 819941) B819941
theorem B3102533 : Blo 542804 3102533 := bstep (se 4 (by rfl) ⟨290862, by rfl⟩ : syracuseStep 3102533 = 581725) B581725
theorem B546643 : Blo 542804 546643 := bstep (se 1 (by rfl) ⟨409982, by rfl⟩ : syracuseStep 546643 = 819965) B819965
theorem B546659 : Blo 542804 546659 := bstep (se 1 (by rfl) ⟨409994, by rfl⟩ : syracuseStep 546659 = 819989) B819989
theorem B612211 : Blo 542804 612211 := bstep (se 1 (by rfl) ⟨459158, by rfl⟩ : syracuseStep 612211 = 918317) B918317
theorem B546675 : Blo 542804 546675 := bstep (se 1 (by rfl) ⟨410006, by rfl⟩ : syracuseStep 546675 = 820013) B820013
theorem B546691 : Blo 542804 546691 := bstep (se 1 (by rfl) ⟨410018, by rfl⟩ : syracuseStep 546691 = 820037) B820037
theorem B4413325 : Blo 542804 4413325 := bstep (se 3 (by rfl) ⟨827498, by rfl⟩ : syracuseStep 4413325 = 1654997) B1654997
theorem B546707 : Blo 542804 546707 := bstep (se 1 (by rfl) ⟨410030, by rfl⟩ : syracuseStep 546707 = 820061) B820061
theorem B546723 : Blo 542804 546723 := bstep (se 1 (by rfl) ⟨410042, by rfl⟩ : syracuseStep 546723 = 820085) B820085
theorem B546739 : Blo 542804 546739 := bstep (se 1 (by rfl) ⟨410054, by rfl⟩ : syracuseStep 546739 = 820109) B820109
theorem B874433 : Blo 542804 874433 := bstep (se 2 (by rfl) ⟨327912, by rfl⟩ : syracuseStep 874433 = 655825) B655825
theorem B546755 : Blo 542804 546755 := bstep (se 1 (by rfl) ⟨410066, by rfl⟩ : syracuseStep 546755 = 820133) B820133
theorem B546771 : Blo 542804 546771 := bstep (se 1 (by rfl) ⟨410078, by rfl⟩ : syracuseStep 546771 = 820157) B820157
theorem B546787 : Blo 542804 546787 := bstep (se 1 (by rfl) ⟨410090, by rfl⟩ : syracuseStep 546787 = 820181) B820181
theorem B546803 : Blo 542804 546803 := bstep (se 1 (by rfl) ⟨410102, by rfl⟩ : syracuseStep 546803 = 820205) B820205
theorem B612355 : Blo 542804 612355 := bstep (se 1 (by rfl) ⟨459266, by rfl⟩ : syracuseStep 612355 = 918533) B918533
theorem B776243 : Blo 542804 776243 := bstep (se 1 (by rfl) ⟨582182, by rfl⟩ : syracuseStep 776243 = 1164365) B1164365
theorem B874561 : Blo 542804 874561 := bstep (se 2 (by rfl) ⟨327960, by rfl⟩ : syracuseStep 874561 = 655921) B655921
theorem B12572813 : Blo 542804 12572813 := bstep (se 3 (by rfl) ⟨2357402, by rfl⟩ : syracuseStep 12572813 = 4714805) B4714805
theorem B612499 : Blo 542804 612499 := bstep (se 1 (by rfl) ⟨459374, by rfl⟩ : syracuseStep 612499 = 918749) B918749
theorem B612643 : Blo 542804 612643 := bstep (se 1 (by rfl) ⟨459482, by rfl⟩ : syracuseStep 612643 = 918965) B918965
theorem B612787 : Blo 542804 612787 := bstep (se 1 (by rfl) ⟨459590, by rfl⟩ : syracuseStep 612787 = 919181) B919181
theorem B580051 : Blo 542804 580051 := bstep (se 1 (by rfl) ⟨435038, by rfl⟩ : syracuseStep 580051 = 870077) B870077
theorem B3103217 : Blo 542804 3103217 := bstep (se 2 (by rfl) ⟨1163706, by rfl⟩ : syracuseStep 3103217 = 2327413) B2327413
theorem B612931 : Blo 542804 612931 := bstep (se 1 (by rfl) ⟨459698, by rfl⟩ : syracuseStep 612931 = 919397) B919397
theorem B2939533 : Blo 542804 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B776881 : Blo 542804 776881 := bstep (se 2 (by rfl) ⟨291330, by rfl⟩ : syracuseStep 776881 = 582661) B582661
theorem B613075 : Blo 542804 613075 := bstep (se 1 (by rfl) ⟨459806, by rfl⟩ : syracuseStep 613075 = 919613) B919613
theorem B613219 : Blo 542804 613219 := bstep (se 1 (by rfl) ⟨459914, by rfl⟩ : syracuseStep 613219 = 919829) B919829
theorem B613363 : Blo 542804 613363 := bstep (se 1 (by rfl) ⟨460022, by rfl⟩ : syracuseStep 613363 = 920045) B920045
theorem B777217 : Blo 542804 777217 := bstep (se 2 (by rfl) ⟨291456, by rfl⟩ : syracuseStep 777217 = 582913) B582913
theorem B613507 : Blo 542804 613507 := bstep (se 1 (by rfl) ⟨460130, by rfl⟩ : syracuseStep 613507 = 920261) B920261
theorem B613651 : Blo 542804 613651 := bstep (se 1 (by rfl) ⟨460238, by rfl⟩ : syracuseStep 613651 = 920477) B920477
theorem B875843 : Blo 542804 875843 := bstep (se 1 (by rfl) ⟨656882, by rfl⟩ : syracuseStep 875843 = 1313765) B1313765
theorem B613795 : Blo 542804 613795 := bstep (se 1 (by rfl) ⟨460346, by rfl⟩ : syracuseStep 613795 = 920693) B920693
theorem B1957297 : Blo 542804 1957297 := bstep (se 2 (by rfl) ⟨733986, by rfl⟩ : syracuseStep 1957297 = 1467973) B1467973
theorem B613939 : Blo 542804 613939 := bstep (se 1 (by rfl) ⟨460454, by rfl⟩ : syracuseStep 613939 = 920909) B920909
theorem B777809 : Blo 542804 777809 := bstep (se 2 (by rfl) ⟨291678, by rfl⟩ : syracuseStep 777809 = 583357) B583357
theorem B581315 : Blo 542804 581315 := bstep (se 1 (by rfl) ⟨435986, by rfl⟩ : syracuseStep 581315 = 871973) B871973
theorem B614083 : Blo 542804 614083 := bstep (se 1 (by rfl) ⟨460562, by rfl⟩ : syracuseStep 614083 = 921125) B921125
theorem B1105699 : Blo 542804 1105699 := bstep (se 1 (by rfl) ⟨829274, by rfl⟩ : syracuseStep 1105699 = 1658549) B1658549
theorem B614227 : Blo 542804 614227 := bstep (se 1 (by rfl) ⟨460670, by rfl⟩ : syracuseStep 614227 = 921341) B921341
theorem B3104675 : Blo 542804 3104675 := bstep (se 1 (by rfl) ⟨2328506, by rfl⟩ : syracuseStep 3104675 = 4657013) B4657013
theorem B614371 : Blo 542804 614371 := bstep (se 1 (by rfl) ⟨460778, by rfl⟩ : syracuseStep 614371 = 921557) B921557
theorem B3366947 : Blo 542804 3366947 := bstep (se 1 (by rfl) ⟨2525210, by rfl⟩ : syracuseStep 3366947 = 5050421) B5050421
theorem B778339 : Blo 542804 778339 := bstep (se 1 (by rfl) ⟨583754, by rfl⟩ : syracuseStep 778339 = 1167509) B1167509
theorem B614515 : Blo 542804 614515 := bstep (se 1 (by rfl) ⟨460886, by rfl⟩ : syracuseStep 614515 = 921773) B921773
theorem B614659 : Blo 542804 614659 := bstep (se 1 (by rfl) ⟨460994, by rfl⟩ : syracuseStep 614659 = 921989) B921989
theorem B614803 : Blo 542804 614803 := bstep (se 1 (by rfl) ⟨461102, by rfl⟩ : syracuseStep 614803 = 922205) B922205
theorem B582067 : Blo 542804 582067 := bstep (se 1 (by rfl) ⟨436550, by rfl⟩ : syracuseStep 582067 = 873101) B873101
theorem B614947 : Blo 542804 614947 := bstep (se 1 (by rfl) ⟨461210, by rfl⟩ : syracuseStep 614947 = 922421) B922421
theorem B582323 : Blo 542804 582323 := bstep (se 1 (by rfl) ⟨436742, by rfl⟩ : syracuseStep 582323 = 873485) B873485
theorem B615091 : Blo 542804 615091 := bstep (se 1 (by rfl) ⟨461318, by rfl⟩ : syracuseStep 615091 = 922637) B922637
theorem B1696465 : Blo 542804 1696465 := bstep (se 2 (by rfl) ⟨636174, by rfl⟩ : syracuseStep 1696465 = 1272349) B1272349
theorem B5989091 : Blo 542804 5989091 := bstep (se 1 (by rfl) ⟨4491818, by rfl⟩ : syracuseStep 5989091 = 8983637) B8983637
theorem B1958755 : Blo 542804 1958755 := bstep (se 1 (by rfl) ⟨1469066, by rfl⟩ : syracuseStep 1958755 = 2938133) B2938133
theorem B1467281 : Blo 542804 1467281 := bstep (se 2 (by rfl) ⟨550230, by rfl⟩ : syracuseStep 1467281 = 1100461) B1100461
theorem B22438853 : Blo 542804 22438853 := bstep (se 4 (by rfl) ⟨2103642, by rfl⟩ : syracuseStep 22438853 = 4207285) B4207285
theorem B2614285 : Blo 542804 2614285 := bstep (se 3 (by rfl) ⟨490178, by rfl⟩ : syracuseStep 2614285 = 980357) B980357
theorem B746545 : Blo 542804 746545 := bstep (se 2 (by rfl) ⟨279954, by rfl⟩ : syracuseStep 746545 = 559909) B559909
theorem B2319587 : Blo 542804 2319587 := bstep (se 1 (by rfl) ⟨1739690, by rfl⟩ : syracuseStep 2319587 = 3479381) B3479381
theorem B1467629 : Blo 542804 1467629 := bstep (se 3 (by rfl) ⟨275180, by rfl⟩ : syracuseStep 1467629 = 550361) B550361
theorem B1467683 : Blo 542804 1467683 := bstep (se 1 (by rfl) ⟨1100762, by rfl⟩ : syracuseStep 1467683 = 2201525) B2201525
theorem B6186293 : Blo 542804 6186293 := bstep (se 5 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 6186293 = 579965) B579965
theorem B583075 : Blo 542804 583075 := bstep (se 1 (by rfl) ⟨437306, by rfl⟩ : syracuseStep 583075 = 874613) B874613
theorem B2942477 : Blo 542804 2942477 := bstep (se 3 (by rfl) ⟨551714, by rfl⟩ : syracuseStep 2942477 = 1103429) B1103429
theorem B2942563 : Blo 542804 2942563 := bstep (se 1 (by rfl) ⟨2206922, by rfl⟩ : syracuseStep 2942563 = 4413845) B4413845
theorem B3139235 : Blo 542804 3139235 := bstep (se 1 (by rfl) ⟨2354426, by rfl⟩ : syracuseStep 3139235 = 4708853) B4708853
theorem B550579 : Blo 542804 550579 := bstep (se 1 (by rfl) ⟨412934, by rfl⟩ : syracuseStep 550579 = 825869) B825869
theorem B1238723 : Blo 542804 1238723 := bstep (se 1 (by rfl) ⟨929042, by rfl⟩ : syracuseStep 1238723 = 1858085) B1858085
theorem B3303281 : Blo 542804 3303281 := bstep (se 2 (by rfl) ⟨1238730, by rfl⟩ : syracuseStep 3303281 = 2477461) B2477461
theorem B23553989 : Blo 542804 23553989 := bstep (se 4 (by rfl) ⟨2208186, by rfl⟩ : syracuseStep 23553989 = 4416373) B4416373
theorem B4122737 : Blo 542804 4122737 := bstep (se 2 (by rfl) ⟨1546026, by rfl⟩ : syracuseStep 4122737 = 3092053) B3092053
theorem B15952099 : Blo 542804 15952099 := bstep (se 1 (by rfl) ⟨11964074, by rfl⟩ : syracuseStep 15952099 = 23928149) B23928149
theorem B1468817 : Blo 542804 1468817 := bstep (se 2 (by rfl) ⟨550806, by rfl⟩ : syracuseStep 1468817 = 1101613) B1101613
theorem B2943685 : Blo 542804 2943685 := bstep (se 4 (by rfl) ⟨275970, by rfl⟩ : syracuseStep 2943685 = 551941) B551941
theorem B1469357 : Blo 542804 1469357 := bstep (se 3 (by rfl) ⟨275504, by rfl⟩ : syracuseStep 1469357 = 551009) B551009
theorem B3533765 : Blo 542804 3533765 := bstep (se 4 (by rfl) ⟨331290, by rfl⟩ : syracuseStep 3533765 = 662581) B662581
theorem B3107909 : Blo 542804 3107909 := bstep (se 4 (by rfl) ⟨291366, by rfl⟩ : syracuseStep 3107909 = 582733) B582733
theorem B3304547 : Blo 542804 3304547 := bstep (se 1 (by rfl) ⟨2478410, by rfl⟩ : syracuseStep 3304547 = 4956821) B4956821
theorem B814211 : Blo 542804 814211 := bstep (se 1 (by rfl) ⟨610658, by rfl⟩ : syracuseStep 814211 = 1221317) B1221317
theorem B814241 : Blo 542804 814241 := bstep (se 2 (by rfl) ⟨305340, by rfl⟩ : syracuseStep 814241 = 610681) B610681
theorem B814259 : Blo 542804 814259 := bstep (se 1 (by rfl) ⟨610694, by rfl⟩ : syracuseStep 814259 = 1221389) B1221389
theorem B814289 : Blo 542804 814289 := bstep (se 2 (by rfl) ⟨305358, by rfl⟩ : syracuseStep 814289 = 610717) B610717
theorem B814307 : Blo 542804 814307 := bstep (se 1 (by rfl) ⟨610730, by rfl⟩ : syracuseStep 814307 = 1221461) B1221461
theorem B814337 : Blo 542804 814337 := bstep (se 2 (by rfl) ⟨305376, by rfl⟩ : syracuseStep 814337 = 610753) B610753
theorem B814355 : Blo 542804 814355 := bstep (se 1 (by rfl) ⟨610766, by rfl⟩ : syracuseStep 814355 = 1221533) B1221533
theorem B814385 : Blo 542804 814385 := bstep (se 2 (by rfl) ⟨305394, by rfl⟩ : syracuseStep 814385 = 610789) B610789
theorem B814403 : Blo 542804 814403 := bstep (se 1 (by rfl) ⟨610802, by rfl⟩ : syracuseStep 814403 = 1221605) B1221605
theorem B814433 : Blo 542804 814433 := bstep (se 2 (by rfl) ⟨305412, by rfl⟩ : syracuseStep 814433 = 610825) B610825
theorem B814451 : Blo 542804 814451 := bstep (se 1 (by rfl) ⟨610838, by rfl⟩ : syracuseStep 814451 = 1221677) B1221677
theorem B814481 : Blo 542804 814481 := bstep (se 2 (by rfl) ⟨305430, by rfl⟩ : syracuseStep 814481 = 610861) B610861
theorem B814499 : Blo 542804 814499 := bstep (se 1 (by rfl) ⟨610874, by rfl⟩ : syracuseStep 814499 = 1221749) B1221749
theorem B1306019 : Blo 542804 1306019 := bstep (se 1 (by rfl) ⟨979514, by rfl⟩ : syracuseStep 1306019 = 1959029) B1959029
theorem B814529 : Blo 542804 814529 := bstep (se 2 (by rfl) ⟨305448, by rfl⟩ : syracuseStep 814529 = 610897) B610897
theorem B814547 : Blo 542804 814547 := bstep (se 1 (by rfl) ⟨610910, by rfl⟩ : syracuseStep 814547 = 1221821) B1221821
theorem B814577 : Blo 542804 814577 := bstep (se 2 (by rfl) ⟨305466, by rfl⟩ : syracuseStep 814577 = 610933) B610933
theorem B814595 : Blo 542804 814595 := bstep (se 1 (by rfl) ⟨610946, by rfl⟩ : syracuseStep 814595 = 1221893) B1221893
theorem B1306115 : Blo 542804 1306115 := bstep (se 1 (by rfl) ⟨979586, by rfl⟩ : syracuseStep 1306115 = 1959173) B1959173
theorem B3108365 : Blo 542804 3108365 := bstep (se 3 (by rfl) ⟨582818, by rfl⟩ : syracuseStep 3108365 = 1165637) B1165637
theorem B814625 : Blo 542804 814625 := bstep (se 2 (by rfl) ⟨305484, by rfl⟩ : syracuseStep 814625 = 610969) B610969
theorem B814643 : Blo 542804 814643 := bstep (se 1 (by rfl) ⟨610982, by rfl⟩ : syracuseStep 814643 = 1221965) B1221965
theorem B814673 : Blo 542804 814673 := bstep (se 2 (by rfl) ⟨305502, by rfl⟩ : syracuseStep 814673 = 611005) B611005
theorem B814691 : Blo 542804 814691 := bstep (se 1 (by rfl) ⟨611018, by rfl⟩ : syracuseStep 814691 = 1222037) B1222037
theorem B814721 : Blo 542804 814721 := bstep (se 2 (by rfl) ⟨305520, by rfl⟩ : syracuseStep 814721 = 611041) B611041
theorem B814739 : Blo 542804 814739 := bstep (se 1 (by rfl) ⟨611054, by rfl⟩ : syracuseStep 814739 = 1222109) B1222109
theorem B814769 : Blo 542804 814769 := bstep (se 2 (by rfl) ⟨305538, by rfl⟩ : syracuseStep 814769 = 611077) B611077
theorem B814787 : Blo 542804 814787 := bstep (se 1 (by rfl) ⟨611090, by rfl⟩ : syracuseStep 814787 = 1222181) B1222181
theorem B814817 : Blo 542804 814817 := bstep (se 2 (by rfl) ⟨305556, by rfl⟩ : syracuseStep 814817 = 611113) B611113
theorem B814835 : Blo 542804 814835 := bstep (se 1 (by rfl) ⟨611126, by rfl⟩ : syracuseStep 814835 = 1222253) B1222253
theorem B814865 : Blo 542804 814865 := bstep (se 2 (by rfl) ⟨305574, by rfl⟩ : syracuseStep 814865 = 611149) B611149
theorem B814883 : Blo 542804 814883 := bstep (se 1 (by rfl) ⟨611162, by rfl⟩ : syracuseStep 814883 = 1222325) B1222325
theorem B814913 : Blo 542804 814913 := bstep (se 2 (by rfl) ⟨305592, by rfl⟩ : syracuseStep 814913 = 611185) B611185
theorem B814931 : Blo 542804 814931 := bstep (se 1 (by rfl) ⟨611198, by rfl⟩ : syracuseStep 814931 = 1222397) B1222397
theorem B814961 : Blo 542804 814961 := bstep (se 2 (by rfl) ⟨305610, by rfl⟩ : syracuseStep 814961 = 611221) B611221
theorem B814979 : Blo 542804 814979 := bstep (se 1 (by rfl) ⟨611234, by rfl⟩ : syracuseStep 814979 = 1222469) B1222469
theorem B815009 : Blo 542804 815009 := bstep (se 2 (by rfl) ⟨305628, by rfl⟩ : syracuseStep 815009 = 611257) B611257
theorem B815027 : Blo 542804 815027 := bstep (se 1 (by rfl) ⟨611270, by rfl⟩ : syracuseStep 815027 = 1222541) B1222541
theorem B1568717 : Blo 542804 1568717 := bstep (se 3 (by rfl) ⟨294134, by rfl⟩ : syracuseStep 1568717 = 588269) B588269
theorem B815057 : Blo 542804 815057 := bstep (se 2 (by rfl) ⟨305646, by rfl⟩ : syracuseStep 815057 = 611293) B611293
theorem B815075 : Blo 542804 815075 := bstep (se 1 (by rfl) ⟨611306, by rfl⟩ : syracuseStep 815075 = 1222613) B1222613
theorem B5238755 : Blo 542804 5238755 := bstep (se 1 (by rfl) ⟨3929066, by rfl⟩ : syracuseStep 5238755 = 7858133) B7858133
theorem B815105 : Blo 542804 815105 := bstep (se 2 (by rfl) ⟨305664, by rfl⟩ : syracuseStep 815105 = 611329) B611329
theorem B815123 : Blo 542804 815123 := bstep (se 1 (by rfl) ⟨611342, by rfl⟩ : syracuseStep 815123 = 1222685) B1222685
theorem B552979 : Blo 542804 552979 := bstep (se 1 (by rfl) ⟨414734, by rfl⟩ : syracuseStep 552979 = 829469) B829469
theorem B2617379 : Blo 542804 2617379 := bstep (se 1 (by rfl) ⟨1963034, by rfl⟩ : syracuseStep 2617379 = 3926069) B3926069
theorem B815153 : Blo 542804 815153 := bstep (se 2 (by rfl) ⟨305682, by rfl⟩ : syracuseStep 815153 = 611365) B611365
theorem B815171 : Blo 542804 815171 := bstep (se 1 (by rfl) ⟨611378, by rfl⟩ : syracuseStep 815171 = 1222757) B1222757
theorem B815201 : Blo 542804 815201 := bstep (se 2 (by rfl) ⟨305700, by rfl⟩ : syracuseStep 815201 = 611401) B611401
theorem B4419683 : Blo 542804 4419683 := bstep (se 1 (by rfl) ⟨3314762, by rfl⟩ : syracuseStep 4419683 = 6629525) B6629525
theorem B815219 : Blo 542804 815219 := bstep (se 1 (by rfl) ⟨611414, by rfl⟩ : syracuseStep 815219 = 1222829) B1222829
theorem B815249 : Blo 542804 815249 := bstep (se 2 (by rfl) ⟨305718, by rfl⟩ : syracuseStep 815249 = 611437) B611437
theorem B815267 : Blo 542804 815267 := bstep (se 1 (by rfl) ⟨611450, by rfl⟩ : syracuseStep 815267 = 1222901) B1222901
theorem B815297 : Blo 542804 815297 := bstep (se 2 (by rfl) ⟨305736, by rfl⟩ : syracuseStep 815297 = 611473) B611473
theorem B815315 : Blo 542804 815315 := bstep (se 1 (by rfl) ⟨611486, by rfl⟩ : syracuseStep 815315 = 1222973) B1222973
theorem B815345 : Blo 542804 815345 := bstep (se 2 (by rfl) ⟨305754, by rfl⟩ : syracuseStep 815345 = 611509) B611509
theorem B815363 : Blo 542804 815363 := bstep (se 1 (by rfl) ⟨611522, by rfl⟩ : syracuseStep 815363 = 1223045) B1223045
theorem B815393 : Blo 542804 815393 := bstep (se 2 (by rfl) ⟨305772, by rfl⟩ : syracuseStep 815393 = 611545) B611545
theorem B815411 : Blo 542804 815411 := bstep (se 1 (by rfl) ⟨611558, by rfl⟩ : syracuseStep 815411 = 1223117) B1223117
theorem B815441 : Blo 542804 815441 := bstep (se 2 (by rfl) ⟨305790, by rfl⟩ : syracuseStep 815441 = 611581) B611581
theorem B1306961 : Blo 542804 1306961 := bstep (se 2 (by rfl) ⟨490110, by rfl⟩ : syracuseStep 1306961 = 980221) B980221
theorem B815459 : Blo 542804 815459 := bstep (se 1 (by rfl) ⟨611594, by rfl⟩ : syracuseStep 815459 = 1223189) B1223189
theorem B815489 : Blo 542804 815489 := bstep (se 2 (by rfl) ⟨305808, by rfl⟩ : syracuseStep 815489 = 611617) B611617
theorem B815507 : Blo 542804 815507 := bstep (se 1 (by rfl) ⟨611630, by rfl⟩ : syracuseStep 815507 = 1223261) B1223261
theorem B1765805 : Blo 542804 1765805 := bstep (se 3 (by rfl) ⟨331088, by rfl⟩ : syracuseStep 1765805 = 662177) B662177
theorem B815537 : Blo 542804 815537 := bstep (se 2 (by rfl) ⟨305826, by rfl⟩ : syracuseStep 815537 = 611653) B611653
theorem B815555 : Blo 542804 815555 := bstep (se 1 (by rfl) ⟨611666, by rfl⟩ : syracuseStep 815555 = 1223333) B1223333
theorem B815585 : Blo 542804 815585 := bstep (se 2 (by rfl) ⟨305844, by rfl⟩ : syracuseStep 815585 = 611689) B611689
theorem B815603 : Blo 542804 815603 := bstep (se 1 (by rfl) ⟨611702, by rfl⟩ : syracuseStep 815603 = 1223405) B1223405
theorem B815633 : Blo 542804 815633 := bstep (se 2 (by rfl) ⟨305862, by rfl⟩ : syracuseStep 815633 = 611725) B611725
theorem B815651 : Blo 542804 815651 := bstep (se 1 (by rfl) ⟨611738, by rfl⟩ : syracuseStep 815651 = 1223477) B1223477
theorem B2748977 : Blo 542804 2748977 := bstep (se 2 (by rfl) ⟨1030866, by rfl⟩ : syracuseStep 2748977 = 2061733) B2061733
theorem B815681 : Blo 542804 815681 := bstep (se 2 (by rfl) ⟨305880, by rfl⟩ : syracuseStep 815681 = 611761) B611761
theorem B815699 : Blo 542804 815699 := bstep (se 1 (by rfl) ⟨611774, by rfl⟩ : syracuseStep 815699 = 1223549) B1223549
theorem B815729 : Blo 542804 815729 := bstep (se 2 (by rfl) ⟨305898, by rfl⟩ : syracuseStep 815729 = 611797) B611797
theorem B1307249 : Blo 542804 1307249 := bstep (se 2 (by rfl) ⟨490218, by rfl⟩ : syracuseStep 1307249 = 980437) B980437
theorem B815747 : Blo 542804 815747 := bstep (se 1 (by rfl) ⟨611810, by rfl⟩ : syracuseStep 815747 = 1223621) B1223621
theorem B815777 : Blo 542804 815777 := bstep (se 2 (by rfl) ⟨305916, by rfl⟩ : syracuseStep 815777 = 611833) B611833
theorem B815795 : Blo 542804 815795 := bstep (se 1 (by rfl) ⟨611846, by rfl⟩ : syracuseStep 815795 = 1223693) B1223693
theorem B815825 : Blo 542804 815825 := bstep (se 2 (by rfl) ⟨305934, by rfl⟩ : syracuseStep 815825 = 611869) B611869
theorem B815843 : Blo 542804 815843 := bstep (se 1 (by rfl) ⟨611882, by rfl⟩ : syracuseStep 815843 = 1223765) B1223765
theorem B815873 : Blo 542804 815873 := bstep (se 2 (by rfl) ⟨305952, by rfl⟩ : syracuseStep 815873 = 611905) B611905
theorem B848659 : Blo 542804 848659 := bstep (se 1 (by rfl) ⟨636494, by rfl⟩ : syracuseStep 848659 = 1272989) B1272989
theorem B815891 : Blo 542804 815891 := bstep (se 1 (by rfl) ⟨611918, by rfl⟩ : syracuseStep 815891 = 1223837) B1223837
theorem B815921 : Blo 542804 815921 := bstep (se 2 (by rfl) ⟨305970, by rfl⟩ : syracuseStep 815921 = 611941) B611941
theorem B815939 : Blo 542804 815939 := bstep (se 1 (by rfl) ⟨611954, by rfl⟩ : syracuseStep 815939 = 1223909) B1223909
theorem B1307459 : Blo 542804 1307459 := bstep (se 1 (by rfl) ⟨980594, by rfl⟩ : syracuseStep 1307459 = 1961189) B1961189
theorem B2618189 : Blo 542804 2618189 := bstep (se 3 (by rfl) ⟨490910, by rfl⟩ : syracuseStep 2618189 = 981821) B981821
theorem B815969 : Blo 542804 815969 := bstep (se 2 (by rfl) ⟨305988, by rfl⟩ : syracuseStep 815969 = 611977) B611977
theorem B2323313 : Blo 542804 2323313 := bstep (se 2 (by rfl) ⟨871242, by rfl⟩ : syracuseStep 2323313 = 1742485) B1742485
theorem B815987 : Blo 542804 815987 := bstep (se 1 (by rfl) ⟨611990, by rfl⟩ : syracuseStep 815987 = 1223981) B1223981
theorem B816017 : Blo 542804 816017 := bstep (se 2 (by rfl) ⟨306006, by rfl⟩ : syracuseStep 816017 = 612013) B612013
theorem B816035 : Blo 542804 816035 := bstep (se 1 (by rfl) ⟨612026, by rfl⟩ : syracuseStep 816035 = 1224053) B1224053
theorem B2061233 : Blo 542804 2061233 := bstep (se 2 (by rfl) ⟨772962, by rfl⟩ : syracuseStep 2061233 = 1545925) B1545925
theorem B816065 : Blo 542804 816065 := bstep (se 2 (by rfl) ⟨306024, by rfl⟩ : syracuseStep 816065 = 612049) B612049
theorem B816083 : Blo 542804 816083 := bstep (se 1 (by rfl) ⟨612062, by rfl⟩ : syracuseStep 816083 = 1224125) B1224125
theorem B816113 : Blo 542804 816113 := bstep (se 2 (by rfl) ⟨306042, by rfl⟩ : syracuseStep 816113 = 612085) B612085
theorem B816131 : Blo 542804 816131 := bstep (se 1 (by rfl) ⟨612098, by rfl⟩ : syracuseStep 816131 = 1224197) B1224197
theorem B652307 : Blo 542804 652307 := bstep (se 1 (by rfl) ⟨489230, by rfl⟩ : syracuseStep 652307 = 978461) B978461
theorem B816161 : Blo 542804 816161 := bstep (se 2 (by rfl) ⟨306060, by rfl⟩ : syracuseStep 816161 = 612121) B612121
theorem B816179 : Blo 542804 816179 := bstep (se 1 (by rfl) ⟨612134, by rfl⟩ : syracuseStep 816179 = 1224269) B1224269
theorem B1832003 : Blo 542804 1832003 := bstep (se 1 (by rfl) ⟨1374002, by rfl⟩ : syracuseStep 1832003 = 2748005) B2748005
theorem B816209 : Blo 542804 816209 := bstep (se 2 (by rfl) ⟨306078, by rfl⟩ : syracuseStep 816209 = 612157) B612157
theorem B816227 : Blo 542804 816227 := bstep (se 1 (by rfl) ⟨612170, by rfl⟩ : syracuseStep 816227 = 1224341) B1224341
theorem B816257 : Blo 542804 816257 := bstep (se 2 (by rfl) ⟨306096, by rfl⟩ : syracuseStep 816257 = 612193) B612193
theorem B816275 : Blo 542804 816275 := bstep (se 1 (by rfl) ⟨612206, by rfl⟩ : syracuseStep 816275 = 1224413) B1224413
theorem B816305 : Blo 542804 816305 := bstep (se 2 (by rfl) ⟨306114, by rfl⟩ : syracuseStep 816305 = 612229) B612229
theorem B816323 : Blo 542804 816323 := bstep (se 1 (by rfl) ⟨612242, by rfl⟩ : syracuseStep 816323 = 1224485) B1224485
theorem B1242307 : Blo 542804 1242307 := bstep (se 1 (by rfl) ⟨931730, by rfl⟩ : syracuseStep 1242307 = 1863461) B1863461
theorem B816353 : Blo 542804 816353 := bstep (se 2 (by rfl) ⟨306132, by rfl⟩ : syracuseStep 816353 = 612265) B612265
theorem B816371 : Blo 542804 816371 := bstep (se 1 (by rfl) ⟨612278, by rfl⟩ : syracuseStep 816371 = 1224557) B1224557
theorem B816401 : Blo 542804 816401 := bstep (se 2 (by rfl) ⟨306150, by rfl⟩ : syracuseStep 816401 = 612301) B612301
theorem B816419 : Blo 542804 816419 := bstep (se 1 (by rfl) ⟨612314, by rfl⟩ : syracuseStep 816419 = 1224629) B1224629
theorem B12711221 : Blo 542804 12711221 := bstep (se 5 (by rfl) ⟨595838, by rfl⟩ : syracuseStep 12711221 = 1191677) B1191677
theorem B816449 : Blo 542804 816449 := bstep (se 2 (by rfl) ⟨306168, by rfl⟩ : syracuseStep 816449 = 612337) B612337
theorem B1832273 : Blo 542804 1832273 := bstep (se 2 (by rfl) ⟨687102, by rfl⟩ : syracuseStep 1832273 = 1374205) B1374205
theorem B816467 : Blo 542804 816467 := bstep (se 1 (by rfl) ⟨612350, by rfl⟩ : syracuseStep 816467 = 1224701) B1224701
theorem B816497 : Blo 542804 816497 := bstep (se 2 (by rfl) ⟨306186, by rfl⟩ : syracuseStep 816497 = 612373) B612373
theorem B816515 : Blo 542804 816515 := bstep (se 1 (by rfl) ⟨612386, by rfl⟩ : syracuseStep 816515 = 1224773) B1224773
theorem B816545 : Blo 542804 816545 := bstep (se 2 (by rfl) ⟨306204, by rfl⟩ : syracuseStep 816545 = 612409) B612409
theorem B816563 : Blo 542804 816563 := bstep (se 1 (by rfl) ⟨612422, by rfl⟩ : syracuseStep 816563 = 1224845) B1224845
theorem B816593 : Blo 542804 816593 := bstep (se 2 (by rfl) ⟨306222, by rfl⟩ : syracuseStep 816593 = 612445) B612445
theorem B816611 : Blo 542804 816611 := bstep (se 1 (by rfl) ⟨612458, by rfl⟩ : syracuseStep 816611 = 1224917) B1224917
theorem B816641 : Blo 542804 816641 := bstep (se 2 (by rfl) ⟨306240, by rfl⟩ : syracuseStep 816641 = 612481) B612481
theorem B816659 : Blo 542804 816659 := bstep (se 1 (by rfl) ⟨612494, by rfl⟩ : syracuseStep 816659 = 1224989) B1224989
theorem B816689 : Blo 542804 816689 := bstep (se 2 (by rfl) ⟨306258, by rfl⟩ : syracuseStep 816689 = 612517) B612517
theorem B816707 : Blo 542804 816707 := bstep (se 1 (by rfl) ⟨612530, by rfl⟩ : syracuseStep 816707 = 1225061) B1225061
theorem B816737 : Blo 542804 816737 := bstep (se 2 (by rfl) ⟨306276, by rfl⟩ : syracuseStep 816737 = 612553) B612553
theorem B1570403 : Blo 542804 1570403 := bstep (se 1 (by rfl) ⟨1177802, by rfl⟩ : syracuseStep 1570403 = 2355605) B2355605
theorem B2618993 : Blo 542804 2618993 := bstep (se 2 (by rfl) ⟨982122, by rfl⟩ : syracuseStep 2618993 = 1964245) B1964245
theorem B816755 : Blo 542804 816755 := bstep (se 1 (by rfl) ⟨612566, by rfl⟩ : syracuseStep 816755 = 1225133) B1225133
theorem B816785 : Blo 542804 816785 := bstep (se 2 (by rfl) ⟨306294, by rfl⟩ : syracuseStep 816785 = 612589) B612589
theorem B816803 : Blo 542804 816803 := bstep (se 1 (by rfl) ⟨612602, by rfl⟩ : syracuseStep 816803 = 1225205) B1225205
theorem B5961397 : Blo 542804 5961397 := bstep (se 5 (by rfl) ⟨279440, by rfl⟩ : syracuseStep 5961397 = 558881) B558881
theorem B6715061 : Blo 542804 6715061 := bstep (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) B629537
theorem B816833 : Blo 542804 816833 := bstep (se 2 (by rfl) ⟨306312, by rfl⟩ : syracuseStep 816833 = 612625) B612625
theorem B816851 : Blo 542804 816851 := bstep (se 1 (by rfl) ⟨612638, by rfl⟩ : syracuseStep 816851 = 1225277) B1225277
theorem B816881 : Blo 542804 816881 := bstep (se 2 (by rfl) ⟨306330, by rfl⟩ : syracuseStep 816881 = 612661) B612661
theorem B816899 : Blo 542804 816899 := bstep (se 1 (by rfl) ⟨612674, by rfl⟩ : syracuseStep 816899 = 1225349) B1225349
theorem B816929 : Blo 542804 816929 := bstep (se 2 (by rfl) ⟨306348, by rfl⟩ : syracuseStep 816929 = 612697) B612697
theorem B816947 : Blo 542804 816947 := bstep (se 1 (by rfl) ⟨612710, by rfl⟩ : syracuseStep 816947 = 1225421) B1225421
theorem B816977 : Blo 542804 816977 := bstep (se 2 (by rfl) ⟨306366, by rfl⟩ : syracuseStep 816977 = 612733) B612733
theorem B816995 : Blo 542804 816995 := bstep (se 1 (by rfl) ⟨612746, by rfl⟩ : syracuseStep 816995 = 1225493) B1225493
theorem B1832813 : Blo 542804 1832813 := bstep (se 3 (by rfl) ⟨343652, by rfl⟩ : syracuseStep 1832813 = 687305) B687305
theorem B817025 : Blo 542804 817025 := bstep (se 2 (by rfl) ⟨306384, by rfl⟩ : syracuseStep 817025 = 612769) B612769
theorem B817043 : Blo 542804 817043 := bstep (se 1 (by rfl) ⟨612782, by rfl⟩ : syracuseStep 817043 = 1225565) B1225565
theorem B1832867 : Blo 542804 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B817073 : Blo 542804 817073 := bstep (se 2 (by rfl) ⟨306402, by rfl⟩ : syracuseStep 817073 = 612805) B612805
theorem B817091 : Blo 542804 817091 := bstep (se 1 (by rfl) ⟨612818, by rfl⟩ : syracuseStep 817091 = 1225637) B1225637
theorem B817121 : Blo 542804 817121 := bstep (se 2 (by rfl) ⟨306420, by rfl⟩ : syracuseStep 817121 = 612841) B612841
theorem B2750435 : Blo 542804 2750435 := bstep (se 1 (by rfl) ⟨2062826, by rfl⟩ : syracuseStep 2750435 = 4125653) B4125653
theorem B817139 : Blo 542804 817139 := bstep (se 1 (by rfl) ⟨612854, by rfl⟩ : syracuseStep 817139 = 1225709) B1225709
theorem B817169 : Blo 542804 817169 := bstep (se 2 (by rfl) ⟨306438, by rfl⟩ : syracuseStep 817169 = 612877) B612877
theorem B817187 : Blo 542804 817187 := bstep (se 1 (by rfl) ⟨612890, by rfl⟩ : syracuseStep 817187 = 1225781) B1225781
theorem B1767473 : Blo 542804 1767473 := bstep (se 2 (by rfl) ⟨662802, by rfl⟩ : syracuseStep 1767473 = 1325605) B1325605
theorem B817217 : Blo 542804 817217 := bstep (se 2 (by rfl) ⟨306456, by rfl⟩ : syracuseStep 817217 = 612913) B612913
theorem B817235 : Blo 542804 817235 := bstep (se 1 (by rfl) ⟨612926, by rfl⟩ : syracuseStep 817235 = 1225853) B1225853
theorem B817265 : Blo 542804 817265 := bstep (se 2 (by rfl) ⟨306474, by rfl⟩ : syracuseStep 817265 = 612949) B612949
theorem B817283 : Blo 542804 817283 := bstep (se 1 (by rfl) ⟨612962, by rfl⟩ : syracuseStep 817283 = 1225925) B1225925
theorem B3307661 : Blo 542804 3307661 := bstep (se 3 (by rfl) ⟨620186, by rfl⟩ : syracuseStep 3307661 = 1240373) B1240373
theorem B817313 : Blo 542804 817313 := bstep (se 2 (by rfl) ⟨306492, by rfl⟩ : syracuseStep 817313 = 612985) B612985
theorem B1833137 : Blo 542804 1833137 := bstep (se 2 (by rfl) ⟨687426, by rfl⟩ : syracuseStep 1833137 = 1374853) B1374853
theorem B817331 : Blo 542804 817331 := bstep (se 1 (by rfl) ⟨612998, by rfl⟩ : syracuseStep 817331 = 1225997) B1225997
theorem B817361 : Blo 542804 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B817379 : Blo 542804 817379 := bstep (se 1 (by rfl) ⟨613034, by rfl⟩ : syracuseStep 817379 = 1226069) B1226069
theorem B817409 : Blo 542804 817409 := bstep (se 2 (by rfl) ⟨306528, by rfl⟩ : syracuseStep 817409 = 613057) B613057
theorem B817427 : Blo 542804 817427 := bstep (se 1 (by rfl) ⟨613070, by rfl⟩ : syracuseStep 817427 = 1226141) B1226141
theorem B2095409 : Blo 542804 2095409 := bstep (se 2 (by rfl) ⟨785778, by rfl⟩ : syracuseStep 2095409 = 1571557) B1571557
theorem B817457 : Blo 542804 817457 := bstep (se 2 (by rfl) ⟨306546, by rfl⟩ : syracuseStep 817457 = 613093) B613093
theorem B817475 : Blo 542804 817475 := bstep (se 1 (by rfl) ⟨613106, by rfl⟩ : syracuseStep 817475 = 1226213) B1226213
theorem B817505 : Blo 542804 817505 := bstep (se 2 (by rfl) ⟨306564, by rfl⟩ : syracuseStep 817505 = 613129) B613129
theorem B2062691 : Blo 542804 2062691 := bstep (se 1 (by rfl) ⟨1547018, by rfl⟩ : syracuseStep 2062691 = 3094037) B3094037
theorem B784739 : Blo 542804 784739 := bstep (se 1 (by rfl) ⟨588554, by rfl⟩ : syracuseStep 784739 = 1177109) B1177109
theorem B2062705 : Blo 542804 2062705 := bstep (se 2 (by rfl) ⟨773514, by rfl⟩ : syracuseStep 2062705 = 1547029) B1547029
theorem B3111281 : Blo 542804 3111281 := bstep (se 2 (by rfl) ⟨1166730, by rfl⟩ : syracuseStep 3111281 = 2333461) B2333461
theorem B817523 : Blo 542804 817523 := bstep (se 1 (by rfl) ⟨613142, by rfl⟩ : syracuseStep 817523 = 1226285) B1226285
theorem B817553 : Blo 542804 817553 := bstep (se 2 (by rfl) ⟨306582, by rfl⟩ : syracuseStep 817553 = 613165) B613165
theorem B817571 : Blo 542804 817571 := bstep (se 1 (by rfl) ⟨613178, by rfl⟩ : syracuseStep 817571 = 1226357) B1226357
theorem B1374641 : Blo 542804 1374641 := bstep (se 2 (by rfl) ⟨515490, by rfl⟩ : syracuseStep 1374641 = 1030981) B1030981
theorem B817601 : Blo 542804 817601 := bstep (se 2 (by rfl) ⟨306600, by rfl⟩ : syracuseStep 817601 = 613201) B613201
theorem B817619 : Blo 542804 817619 := bstep (se 1 (by rfl) ⟨613214, by rfl⟩ : syracuseStep 817619 = 1226429) B1226429
theorem B1374691 : Blo 542804 1374691 := bstep (se 1 (by rfl) ⟨1031018, by rfl⟩ : syracuseStep 1374691 = 2062037) B2062037
theorem B817649 : Blo 542804 817649 := bstep (se 2 (by rfl) ⟨306618, by rfl⟩ : syracuseStep 817649 = 613237) B613237
theorem B817667 : Blo 542804 817667 := bstep (se 1 (by rfl) ⟨613250, by rfl⟩ : syracuseStep 817667 = 1226501) B1226501
theorem B817697 : Blo 542804 817697 := bstep (se 2 (by rfl) ⟨306636, by rfl⟩ : syracuseStep 817697 = 613273) B613273
theorem B817715 : Blo 542804 817715 := bstep (se 1 (by rfl) ⟨613286, by rfl⟩ : syracuseStep 817715 = 1226573) B1226573
theorem B916049 : Blo 542804 916049 := bstep (se 2 (by rfl) ⟨343518, by rfl⟩ : syracuseStep 916049 = 687037) B687037
theorem B817745 : Blo 542804 817745 := bstep (se 2 (by rfl) ⟨306654, by rfl⟩ : syracuseStep 817745 = 613309) B613309
theorem B817763 : Blo 542804 817763 := bstep (se 1 (by rfl) ⟨613322, by rfl⟩ : syracuseStep 817763 = 1226645) B1226645
theorem B1374833 : Blo 542804 1374833 := bstep (se 2 (by rfl) ⟨515562, by rfl⟩ : syracuseStep 1374833 = 1031125) B1031125
theorem B817793 : Blo 542804 817793 := bstep (se 2 (by rfl) ⟨306672, by rfl⟩ : syracuseStep 817793 = 613345) B613345
theorem B817811 : Blo 542804 817811 := bstep (se 1 (by rfl) ⟨613358, by rfl⟩ : syracuseStep 817811 = 1226717) B1226717
theorem B817841 : Blo 542804 817841 := bstep (se 2 (by rfl) ⟨306690, by rfl⟩ : syracuseStep 817841 = 613381) B613381
theorem B817859 : Blo 542804 817859 := bstep (se 1 (by rfl) ⟨613394, by rfl⟩ : syracuseStep 817859 = 1226789) B1226789
theorem B1833677 : Blo 542804 1833677 := bstep (se 3 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 1833677 = 687629) B687629
theorem B916177 : Blo 542804 916177 := bstep (se 2 (by rfl) ⟨343566, by rfl⟩ : syracuseStep 916177 = 687133) B687133
theorem B817889 : Blo 542804 817889 := bstep (se 2 (by rfl) ⟨306708, by rfl⟩ : syracuseStep 817889 = 613417) B613417
theorem B916211 : Blo 542804 916211 := bstep (se 1 (by rfl) ⟨687158, by rfl⟩ : syracuseStep 916211 = 1374317) B1374317
theorem B817907 : Blo 542804 817907 := bstep (se 1 (by rfl) ⟨613430, by rfl⟩ : syracuseStep 817907 = 1226861) B1226861
theorem B1833731 : Blo 542804 1833731 := bstep (se 1 (by rfl) ⟨1375298, by rfl⟩ : syracuseStep 1833731 = 2750597) B2750597
theorem B2751245 : Blo 542804 2751245 := bstep (se 3 (by rfl) ⟨515858, by rfl⟩ : syracuseStep 2751245 = 1031717) B1031717
theorem B817937 : Blo 542804 817937 := bstep (se 2 (by rfl) ⟨306726, by rfl⟩ : syracuseStep 817937 = 613453) B613453
theorem B817955 : Blo 542804 817955 := bstep (se 1 (by rfl) ⟨613466, by rfl⟩ : syracuseStep 817955 = 1226933) B1226933
theorem B817985 : Blo 542804 817985 := bstep (se 2 (by rfl) ⟨306744, by rfl⟩ : syracuseStep 817985 = 613489) B613489
theorem B818003 : Blo 542804 818003 := bstep (se 1 (by rfl) ⟨613502, by rfl⟩ : syracuseStep 818003 = 1227005) B1227005
theorem B1768301 : Blo 542804 1768301 := bstep (se 3 (by rfl) ⟨331556, by rfl⟩ : syracuseStep 1768301 = 663113) B663113
theorem B818033 : Blo 542804 818033 := bstep (se 2 (by rfl) ⟨306762, by rfl⟩ : syracuseStep 818033 = 613525) B613525
theorem B916339 : Blo 542804 916339 := bstep (se 1 (by rfl) ⟨687254, by rfl⟩ : syracuseStep 916339 = 1374509) B1374509
theorem B818051 : Blo 542804 818051 := bstep (se 1 (by rfl) ⟨613538, by rfl⟩ : syracuseStep 818051 = 1227077) B1227077
theorem B818081 : Blo 542804 818081 := bstep (se 2 (by rfl) ⟨306780, by rfl⟩ : syracuseStep 818081 = 613561) B613561
theorem B1309603 : Blo 542804 1309603 := bstep (se 1 (by rfl) ⟨982202, by rfl⟩ : syracuseStep 1309603 = 1964405) B1964405
theorem B818099 : Blo 542804 818099 := bstep (se 1 (by rfl) ⟨613574, by rfl⟩ : syracuseStep 818099 = 1227149) B1227149
theorem B818129 : Blo 542804 818129 := bstep (se 2 (by rfl) ⟨306798, by rfl⟩ : syracuseStep 818129 = 613597) B613597
theorem B818147 : Blo 542804 818147 := bstep (se 1 (by rfl) ⟨613610, by rfl⟩ : syracuseStep 818147 = 1227221) B1227221
theorem B916481 : Blo 542804 916481 := bstep (se 2 (by rfl) ⟨343680, by rfl⟩ : syracuseStep 916481 = 687361) B687361
theorem B818177 : Blo 542804 818177 := bstep (se 2 (by rfl) ⟨306816, by rfl⟩ : syracuseStep 818177 = 613633) B613633
theorem B1834001 : Blo 542804 1834001 := bstep (se 2 (by rfl) ⟨687750, by rfl⟩ : syracuseStep 1834001 = 1375501) B1375501
theorem B654355 : Blo 542804 654355 := bstep (se 1 (by rfl) ⟨490766, by rfl⟩ : syracuseStep 654355 = 981533) B981533
theorem B818195 : Blo 542804 818195 := bstep (se 1 (by rfl) ⟨613646, by rfl⟩ : syracuseStep 818195 = 1227293) B1227293
theorem B818225 : Blo 542804 818225 := bstep (se 2 (by rfl) ⟨306834, by rfl⟩ : syracuseStep 818225 = 613669) B613669
theorem B818243 : Blo 542804 818243 := bstep (se 1 (by rfl) ⟨613682, by rfl⟩ : syracuseStep 818243 = 1227365) B1227365
theorem B818273 : Blo 542804 818273 := bstep (se 2 (by rfl) ⟨306852, by rfl⟩ : syracuseStep 818273 = 613705) B613705
theorem B818291 : Blo 542804 818291 := bstep (se 1 (by rfl) ⟨613718, by rfl⟩ : syracuseStep 818291 = 1227437) B1227437
theorem B916609 : Blo 542804 916609 := bstep (se 2 (by rfl) ⟨343728, by rfl⟩ : syracuseStep 916609 = 687457) B687457
theorem B818321 : Blo 542804 818321 := bstep (se 2 (by rfl) ⟨306870, by rfl⟩ : syracuseStep 818321 = 613741) B613741
theorem B916643 : Blo 542804 916643 := bstep (se 1 (by rfl) ⟨687482, by rfl⟩ : syracuseStep 916643 = 1374965) B1374965
theorem B818339 : Blo 542804 818339 := bstep (se 1 (by rfl) ⟨613754, by rfl⟩ : syracuseStep 818339 = 1227509) B1227509
theorem B818369 : Blo 542804 818369 := bstep (se 2 (by rfl) ⟨306888, by rfl⟩ : syracuseStep 818369 = 613777) B613777
theorem B1244369 : Blo 542804 1244369 := bstep (se 2 (by rfl) ⟨466638, by rfl⟩ : syracuseStep 1244369 = 933277) B933277
theorem B818387 : Blo 542804 818387 := bstep (se 1 (by rfl) ⟨613790, by rfl⟩ : syracuseStep 818387 = 1227581) B1227581
theorem B818417 : Blo 542804 818417 := bstep (se 2 (by rfl) ⟨306906, by rfl⟩ : syracuseStep 818417 = 613813) B613813
theorem B818435 : Blo 542804 818435 := bstep (se 1 (by rfl) ⟨613826, by rfl⟩ : syracuseStep 818435 = 1227653) B1227653
theorem B2325773 : Blo 542804 2325773 := bstep (se 3 (by rfl) ⟨436082, by rfl⟩ : syracuseStep 2325773 = 872165) B872165
theorem B818465 : Blo 542804 818465 := bstep (se 2 (by rfl) ⟨306924, by rfl⟩ : syracuseStep 818465 = 613849) B613849
theorem B916771 : Blo 542804 916771 := bstep (se 1 (by rfl) ⟨687578, by rfl⟩ : syracuseStep 916771 = 1375157) B1375157
theorem B818483 : Blo 542804 818483 := bstep (se 1 (by rfl) ⟨613862, by rfl⟩ : syracuseStep 818483 = 1227725) B1227725
theorem B818513 : Blo 542804 818513 := bstep (se 2 (by rfl) ⟨306942, by rfl⟩ : syracuseStep 818513 = 613885) B613885
theorem B654691 : Blo 542804 654691 := bstep (se 1 (by rfl) ⟨491018, by rfl⟩ : syracuseStep 654691 = 982037) B982037
theorem B818531 : Blo 542804 818531 := bstep (se 1 (by rfl) ⟨613898, by rfl⟩ : syracuseStep 818531 = 1227797) B1227797
theorem B4423025 : Blo 542804 4423025 := bstep (se 2 (by rfl) ⟨1658634, by rfl⟩ : syracuseStep 4423025 = 3317269) B3317269
theorem B818561 : Blo 542804 818561 := bstep (se 2 (by rfl) ⟨306960, by rfl⟩ : syracuseStep 818561 = 613921) B613921
theorem B818579 : Blo 542804 818579 := bstep (se 1 (by rfl) ⟨613934, by rfl⟩ : syracuseStep 818579 = 1227869) B1227869
theorem B687523 : Blo 542804 687523 := bstep (se 1 (by rfl) ⟨515642, by rfl⟩ : syracuseStep 687523 = 1031285) B1031285
theorem B916913 : Blo 542804 916913 := bstep (se 2 (by rfl) ⟨343842, by rfl⟩ : syracuseStep 916913 = 687685) B687685
theorem B818609 : Blo 542804 818609 := bstep (se 2 (by rfl) ⟨306978, by rfl⟩ : syracuseStep 818609 = 613957) B613957
theorem B818627 : Blo 542804 818627 := bstep (se 1 (by rfl) ⟨613970, by rfl⟩ : syracuseStep 818627 = 1227941) B1227941
theorem B1473997 : Blo 542804 1473997 := bstep (se 3 (by rfl) ⟨276374, by rfl⟩ : syracuseStep 1473997 = 552749) B552749
theorem B818657 : Blo 542804 818657 := bstep (se 2 (by rfl) ⟨306996, by rfl⟩ : syracuseStep 818657 = 613993) B613993
theorem B818675 : Blo 542804 818675 := bstep (se 1 (by rfl) ⟨614006, by rfl⟩ : syracuseStep 818675 = 1228013) B1228013
theorem B687619 : Blo 542804 687619 := bstep (se 1 (by rfl) ⟨515714, by rfl⟩ : syracuseStep 687619 = 1031429) B1031429
theorem B818705 : Blo 542804 818705 := bstep (se 2 (by rfl) ⟨307014, by rfl⟩ : syracuseStep 818705 = 614029) B614029
theorem B818723 : Blo 542804 818723 := bstep (se 1 (by rfl) ⟨614042, by rfl⟩ : syracuseStep 818723 = 1228085) B1228085
theorem B1834541 : Blo 542804 1834541 := bstep (se 3 (by rfl) ⟨343976, by rfl⟩ : syracuseStep 1834541 = 687953) B687953
theorem B917041 : Blo 542804 917041 := bstep (se 2 (by rfl) ⟨343890, by rfl⟩ : syracuseStep 917041 = 687781) B687781
theorem B10649141 : Blo 542804 10649141 := bstep (se 5 (by rfl) ⟨499178, by rfl⟩ : syracuseStep 10649141 = 998357) B998357
theorem B818753 : Blo 542804 818753 := bstep (se 2 (by rfl) ⟨307032, by rfl⟩ : syracuseStep 818753 = 614065) B614065
theorem B1375825 : Blo 542804 1375825 := bstep (se 2 (by rfl) ⟨515934, by rfl⟩ : syracuseStep 1375825 = 1031869) B1031869
theorem B917075 : Blo 542804 917075 := bstep (se 1 (by rfl) ⟨687806, by rfl⟩ : syracuseStep 917075 = 1375613) B1375613
theorem B818771 : Blo 542804 818771 := bstep (se 1 (by rfl) ⟨614078, by rfl⟩ : syracuseStep 818771 = 1228157) B1228157
theorem B1834595 : Blo 542804 1834595 := bstep (se 1 (by rfl) ⟨1375946, by rfl⟩ : syracuseStep 1834595 = 2751893) B2751893
theorem B818801 : Blo 542804 818801 := bstep (se 2 (by rfl) ⟨307050, by rfl⟩ : syracuseStep 818801 = 614101) B614101
theorem B818819 : Blo 542804 818819 := bstep (se 1 (by rfl) ⟨614114, by rfl⟩ : syracuseStep 818819 = 1228229) B1228229
theorem B2621069 : Blo 542804 2621069 := bstep (se 3 (by rfl) ⟨491450, by rfl⟩ : syracuseStep 2621069 = 982901) B982901
theorem B818849 : Blo 542804 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B818867 : Blo 542804 818867 := bstep (se 1 (by rfl) ⟨614150, by rfl⟩ : syracuseStep 818867 = 1228301) B1228301
theorem B818897 : Blo 542804 818897 := bstep (se 2 (by rfl) ⟨307086, by rfl⟩ : syracuseStep 818897 = 614173) B614173
theorem B917203 : Blo 542804 917203 := bstep (se 1 (by rfl) ⟨687902, by rfl⟩ : syracuseStep 917203 = 1375805) B1375805
theorem B1244899 : Blo 542804 1244899 := bstep (se 1 (by rfl) ⟨933674, by rfl⟩ : syracuseStep 1244899 = 1867349) B1867349
theorem B818915 : Blo 542804 818915 := bstep (se 1 (by rfl) ⟨614186, by rfl⟩ : syracuseStep 818915 = 1228373) B1228373
theorem B818945 : Blo 542804 818945 := bstep (se 2 (by rfl) ⟨307104, by rfl⟩ : syracuseStep 818945 = 614209) B614209
theorem B818963 : Blo 542804 818963 := bstep (se 1 (by rfl) ⟨614222, by rfl⟩ : syracuseStep 818963 = 1228445) B1228445
theorem B2064163 : Blo 542804 2064163 := bstep (se 1 (by rfl) ⟨1548122, by rfl⟩ : syracuseStep 2064163 = 3096245) B3096245
theorem B3112739 : Blo 542804 3112739 := bstep (se 1 (by rfl) ⟨2334554, by rfl⟩ : syracuseStep 3112739 = 4669109) B4669109
theorem B818993 : Blo 542804 818993 := bstep (se 2 (by rfl) ⟨307122, by rfl⟩ : syracuseStep 818993 = 614245) B614245
theorem B819011 : Blo 542804 819011 := bstep (se 1 (by rfl) ⟨614258, by rfl⟩ : syracuseStep 819011 = 1228517) B1228517
theorem B917345 : Blo 542804 917345 := bstep (se 2 (by rfl) ⟨344004, by rfl⟩ : syracuseStep 917345 = 688009) B688009
theorem B851809 : Blo 542804 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B1376099 : Blo 542804 1376099 := bstep (se 1 (by rfl) ⟨1032074, by rfl⟩ : syracuseStep 1376099 = 2064149) B2064149
theorem B1867619 : Blo 542804 1867619 := bstep (se 1 (by rfl) ⟨1400714, by rfl⟩ : syracuseStep 1867619 = 2801429) B2801429
theorem B819041 : Blo 542804 819041 := bstep (se 2 (by rfl) ⟨307140, by rfl⟩ : syracuseStep 819041 = 614281) B614281
theorem B1834865 : Blo 542804 1834865 := bstep (se 2 (by rfl) ⟨688074, by rfl⟩ : syracuseStep 1834865 = 1376149) B1376149
theorem B5603185 : Blo 542804 5603185 := bstep (se 2 (by rfl) ⟨2101194, by rfl⟩ : syracuseStep 5603185 = 4202389) B4202389
theorem B819059 : Blo 542804 819059 := bstep (se 1 (by rfl) ⟨614294, by rfl⟩ : syracuseStep 819059 = 1228589) B1228589
theorem B819089 : Blo 542804 819089 := bstep (se 2 (by rfl) ⟨307158, by rfl⟩ : syracuseStep 819089 = 614317) B614317
theorem B819107 : Blo 542804 819107 := bstep (se 1 (by rfl) ⟨614330, by rfl⟩ : syracuseStep 819107 = 1228661) B1228661
theorem B819137 : Blo 542804 819137 := bstep (se 2 (by rfl) ⟨307176, by rfl⟩ : syracuseStep 819137 = 614353) B614353
theorem B819155 : Blo 542804 819155 := bstep (se 1 (by rfl) ⟨614366, by rfl⟩ : syracuseStep 819155 = 1228733) B1228733
theorem B917473 : Blo 542804 917473 := bstep (se 2 (by rfl) ⟨344052, by rfl⟩ : syracuseStep 917473 = 688105) B688105
theorem B819185 : Blo 542804 819185 := bstep (se 2 (by rfl) ⟨307194, by rfl⟩ : syracuseStep 819185 = 614389) B614389
theorem B688115 : Blo 542804 688115 := bstep (se 1 (by rfl) ⟨516086, by rfl⟩ : syracuseStep 688115 = 1032173) B1032173
theorem B917527 : Blo 542804 917527 := bstep (se 1 (by rfl) ⟨688145, by rfl⟩ : syracuseStep 917527 = 1376291) B1376291
theorem B1048627 : Blo 542804 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B819275 : Blo 542804 819275 := bstep (se 1 (by rfl) ⟨614456, by rfl⟩ : syracuseStep 819275 = 1228913) B1228913
theorem B819287 : Blo 542804 819287 := bstep (se 1 (by rfl) ⟨614465, by rfl⟩ : syracuseStep 819287 = 1228931) B1228931
theorem B8978525 : Blo 542804 8978525 := bstep (se 3 (by rfl) ⟨1683473, by rfl⟩ : syracuseStep 8978525 = 3366947) B3366947
theorem B2949221 : Blo 542804 2949221 := bstep (se 4 (by rfl) ⟨276489, by rfl⟩ : syracuseStep 2949221 = 552979) B552979
theorem B688267 : Blo 542804 688267 := bstep (se 1 (by rfl) ⟨516200, by rfl⟩ : syracuseStep 688267 = 1032401) B1032401
theorem B819353 : Blo 542804 819353 := bstep (se 2 (by rfl) ⟨307257, by rfl⟩ : syracuseStep 819353 = 614515) B614515
theorem B1376473 : Blo 542804 1376473 := bstep (se 2 (by rfl) ⟨516177, by rfl⟩ : syracuseStep 1376473 = 1032355) B1032355
theorem B819467 : Blo 542804 819467 := bstep (se 1 (by rfl) ⟨614600, by rfl⟩ : syracuseStep 819467 = 1229201) B1229201
theorem B819479 : Blo 542804 819479 := bstep (se 1 (by rfl) ⟨614609, by rfl⟩ : syracuseStep 819479 = 1229219) B1229219
theorem B819545 : Blo 542804 819545 := bstep (se 2 (by rfl) ⟨307329, by rfl⟩ : syracuseStep 819545 = 614659) B614659
theorem B2130349 : Blo 542804 2130349 := bstep (se 3 (by rfl) ⟨399440, by rfl⟩ : syracuseStep 2130349 = 798881) B798881
theorem B819659 : Blo 542804 819659 := bstep (se 1 (by rfl) ⟨614744, by rfl⟩ : syracuseStep 819659 = 1229489) B1229489
theorem B819671 : Blo 542804 819671 := bstep (se 1 (by rfl) ⟨614753, by rfl⟩ : syracuseStep 819671 = 1229507) B1229507
theorem B2359811 : Blo 542804 2359811 := bstep (se 1 (by rfl) ⟨1769858, by rfl⟩ : syracuseStep 2359811 = 3539717) B3539717
theorem B13238801 : Blo 542804 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B1966609 : Blo 542804 1966609 := bstep (se 2 (by rfl) ⟨737478, by rfl⟩ : syracuseStep 1966609 = 1474957) B1474957
theorem B819737 : Blo 542804 819737 := bstep (se 2 (by rfl) ⟨307401, by rfl⟩ : syracuseStep 819737 = 614803) B614803
theorem B2327105 : Blo 542804 2327105 := bstep (se 2 (by rfl) ⟨872664, by rfl⟩ : syracuseStep 2327105 = 1745329) B1745329
theorem B918155 : Blo 542804 918155 := bstep (se 1 (by rfl) ⟨688616, by rfl⟩ : syracuseStep 918155 = 1377233) B1377233
theorem B819851 : Blo 542804 819851 := bstep (se 1 (by rfl) ⟨614888, by rfl⟩ : syracuseStep 819851 = 1229777) B1229777
theorem B819863 : Blo 542804 819863 := bstep (se 1 (by rfl) ⟨614897, by rfl⟩ : syracuseStep 819863 = 1229795) B1229795
theorem B819929 : Blo 542804 819929 := bstep (se 2 (by rfl) ⟨307473, by rfl⟩ : syracuseStep 819929 = 614947) B614947
theorem B4129541 : Blo 542804 4129541 := bstep (se 4 (by rfl) ⟨387144, by rfl⟩ : syracuseStep 4129541 = 774289) B774289
theorem B918283 : Blo 542804 918283 := bstep (se 1 (by rfl) ⟨688712, by rfl⟩ : syracuseStep 918283 = 1377425) B1377425
theorem B820043 : Blo 542804 820043 := bstep (se 1 (by rfl) ⟨615032, by rfl⟩ : syracuseStep 820043 = 1230065) B1230065
theorem B820055 : Blo 542804 820055 := bstep (se 1 (by rfl) ⟨615041, by rfl⟩ : syracuseStep 820055 = 1230083) B1230083
theorem B1049483 : Blo 542804 1049483 := bstep (se 1 (by rfl) ⟨787112, by rfl⟩ : syracuseStep 1049483 = 1574225) B1574225
theorem B656267 : Blo 542804 656267 := bstep (se 1 (by rfl) ⟨492200, by rfl⟩ : syracuseStep 656267 = 984401) B984401
theorem B2327447 : Blo 542804 2327447 := bstep (se 1 (by rfl) ⟨1745585, by rfl⟩ : syracuseStep 2327447 = 3491171) B3491171
theorem B918425 : Blo 542804 918425 := bstep (se 2 (by rfl) ⟨344409, by rfl⟩ : syracuseStep 918425 = 688819) B688819
theorem B820121 : Blo 542804 820121 := bstep (se 2 (by rfl) ⟨307545, by rfl⟩ : syracuseStep 820121 = 615091) B615091
theorem B2261953 : Blo 542804 2261953 := bstep (se 2 (by rfl) ⟨848232, by rfl⟩ : syracuseStep 2261953 = 1696465) B1696465
theorem B918553 : Blo 542804 918553 := bstep (se 2 (by rfl) ⟨344457, by rfl⟩ : syracuseStep 918553 = 688915) B688915
theorem B1836107 : Blo 542804 1836107 := bstep (se 1 (by rfl) ⟨1377080, by rfl⟩ : syracuseStep 1836107 = 2754161) B2754161
theorem B689239 : Blo 542804 689239 := bstep (se 1 (by rfl) ⟨516929, by rfl⟩ : syracuseStep 689239 = 1033859) B1033859
theorem B2753837 : Blo 542804 2753837 := bstep (se 3 (by rfl) ⟨516344, by rfl⟩ : syracuseStep 2753837 = 1032689) B1032689
theorem B1377587 : Blo 542804 1377587 := bstep (se 1 (by rfl) ⟨1033190, by rfl⟩ : syracuseStep 1377587 = 2066381) B2066381
theorem B1836377 : Blo 542804 1836377 := bstep (se 2 (by rfl) ⟨688641, by rfl⟩ : syracuseStep 1836377 = 1377283) B1377283
theorem B4982147 : Blo 542804 4982147 := bstep (se 1 (by rfl) ⟨3736610, by rfl⟩ : syracuseStep 4982147 = 7473221) B7473221
theorem B26936725 : Blo 542804 26936725 := bstep (se 6 (by rfl) ⟨631329, by rfl⟩ : syracuseStep 26936725 = 1262659) B1262659
theorem B1246795 : Blo 542804 1246795 := bstep (se 1 (by rfl) ⟨935096, by rfl⟩ : syracuseStep 1246795 = 1870193) B1870193
theorem B919127 : Blo 542804 919127 := bstep (se 1 (by rfl) ⟨689345, by rfl⟩ : syracuseStep 919127 = 1378691) B1378691
theorem B1377881 : Blo 542804 1377881 := bstep (se 2 (by rfl) ⟨516705, by rfl⟩ : syracuseStep 1377881 = 1033411) B1033411
theorem B2066093 : Blo 542804 2066093 := bstep (se 3 (by rfl) ⟨387392, by rfl⟩ : syracuseStep 2066093 = 774785) B774785
theorem B919255 : Blo 542804 919255 := bstep (se 1 (by rfl) ⟨689441, by rfl⟩ : syracuseStep 919255 = 1378883) B1378883
theorem B2328371 : Blo 542804 2328371 := bstep (se 1 (by rfl) ⟨1746278, by rfl⟩ : syracuseStep 2328371 = 3492557) B3492557
theorem B690059 : Blo 542804 690059 := bstep (se 1 (by rfl) ⟨517544, by rfl⟩ : syracuseStep 690059 = 1035089) B1035089
theorem B1837079 : Blo 542804 1837079 := bstep (se 1 (by rfl) ⟨1377809, by rfl⟩ : syracuseStep 1837079 = 2755619) B2755619
theorem B919883 : Blo 542804 919883 := bstep (se 1 (by rfl) ⟨689912, by rfl⟩ : syracuseStep 919883 = 1379825) B1379825
theorem B2066867 : Blo 542804 2066867 := bstep (se 1 (by rfl) ⟨1550150, by rfl⟩ : syracuseStep 2066867 = 3100301) B3100301
theorem B1182131 : Blo 542804 1182131 := bstep (se 1 (by rfl) ⟨886598, by rfl⟩ : syracuseStep 1182131 = 1773197) B1773197
theorem B920011 : Blo 542804 920011 := bstep (se 1 (by rfl) ⟨690008, by rfl⟩ : syracuseStep 920011 = 1380017) B1380017
theorem B1837619 : Blo 542804 1837619 := bstep (se 1 (by rfl) ⟨1378214, by rfl⟩ : syracuseStep 1837619 = 2756429) B2756429
theorem B690763 : Blo 542804 690763 := bstep (se 1 (by rfl) ⟨518072, by rfl⟩ : syracuseStep 690763 = 1036145) B1036145
theorem B920153 : Blo 542804 920153 := bstep (se 2 (by rfl) ⟨345057, by rfl⟩ : syracuseStep 920153 = 690115) B690115
theorem B4983389 : Blo 542804 4983389 := bstep (se 3 (by rfl) ⟨934385, by rfl⟩ : syracuseStep 4983389 = 1868771) B1868771
theorem B920281 : Blo 542804 920281 := bstep (se 2 (by rfl) ⟨345105, by rfl⟩ : syracuseStep 920281 = 690211) B690211
theorem B1739485 : Blo 542804 1739485 := bstep (se 3 (by rfl) ⟨326153, by rfl⟩ : syracuseStep 1739485 = 652307) B652307
theorem B2329361 : Blo 542804 2329361 := bstep (se 2 (by rfl) ⟨873510, by rfl⟩ : syracuseStep 2329361 = 1747021) B1747021
theorem B1837889 : Blo 542804 1837889 := bstep (se 2 (by rfl) ⟨689208, by rfl⟩ : syracuseStep 1837889 = 1378417) B1378417
theorem B691031 : Blo 542804 691031 := bstep (se 1 (by rfl) ⟨518273, by rfl⟩ : syracuseStep 691031 = 1036547) B1036547
theorem B1313687 : Blo 542804 1313687 := bstep (se 1 (by rfl) ⟨985265, by rfl⟩ : syracuseStep 1313687 = 1970531) B1970531
theorem B21269465 : Blo 542804 21269465 := bstep (se 2 (by rfl) ⟨7976049, by rfl⟩ : syracuseStep 21269465 = 15952099) B15952099
theorem B5049305 : Blo 542804 5049305 := bstep (se 2 (by rfl) ⟨1893489, by rfl⟩ : syracuseStep 5049305 = 3786979) B3786979
theorem B4131971 : Blo 542804 4131971 := bstep (se 1 (by rfl) ⟨3098978, by rfl⟩ : syracuseStep 4131971 = 6197957) B6197957
theorem B1379531 : Blo 542804 1379531 := bstep (se 1 (by rfl) ⟨1034648, by rfl⟩ : syracuseStep 1379531 = 2069297) B2069297
theorem B1477835 : Blo 542804 1477835 := bstep (se 1 (by rfl) ⟨1108376, by rfl⟩ : syracuseStep 1477835 = 2216753) B2216753
theorem B920855 : Blo 542804 920855 := bstep (se 1 (by rfl) ⟨690641, by rfl⟩ : syracuseStep 920855 = 1381283) B1381283
theorem B1838429 : Blo 542804 1838429 := bstep (se 3 (by rfl) ⟨344705, by rfl⟩ : syracuseStep 1838429 = 689411) B689411
theorem B920983 : Blo 542804 920983 := bstep (se 1 (by rfl) ⟨690737, by rfl⟩ : syracuseStep 920983 = 1381475) B1381475
theorem B1510859 : Blo 542804 1510859 := bstep (se 1 (by rfl) ⟨1133144, by rfl⟩ : syracuseStep 1510859 = 2266289) B2266289
theorem B757207 : Blo 542804 757207 := bstep (se 1 (by rfl) ⟨567905, by rfl⟩ : syracuseStep 757207 = 1135811) B1135811
theorem B1969667 : Blo 542804 1969667 := bstep (se 1 (by rfl) ⟨1477250, by rfl⟩ : syracuseStep 1969667 = 2954501) B2954501
theorem B691735 : Blo 542804 691735 := bstep (se 1 (by rfl) ⟨518801, by rfl⟩ : syracuseStep 691735 = 1037603) B1037603
theorem B1969753 : Blo 542804 1969753 := bstep (se 2 (by rfl) ⟨738657, by rfl⟩ : syracuseStep 1969753 = 1477315) B1477315
theorem B15699653 : Blo 542804 15699653 := bstep (se 4 (by rfl) ⟨1471842, by rfl⟩ : syracuseStep 15699653 = 2943685) B2943685
theorem B2068355 : Blo 542804 2068355 := bstep (se 1 (by rfl) ⟨1551266, by rfl⟩ : syracuseStep 2068355 = 3102533) B3102533
theorem B921611 : Blo 542804 921611 := bstep (se 1 (by rfl) ⟨691208, by rfl⟩ : syracuseStep 921611 = 1382417) B1382417
theorem B921739 : Blo 542804 921739 := bstep (se 1 (by rfl) ⟨691304, by rfl⟩ : syracuseStep 921739 = 1382609) B1382609
theorem B1380503 : Blo 542804 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B921881 : Blo 542804 921881 := bstep (se 2 (by rfl) ⟨345705, by rfl⟩ : syracuseStep 921881 = 691411) B691411
theorem B6983981 : Blo 542804 6983981 := bstep (se 3 (by rfl) ⟨1309496, by rfl⟩ : syracuseStep 6983981 = 2618993) B2618993
theorem B2068811 : Blo 542804 2068811 := bstep (se 1 (by rfl) ⟨1551608, by rfl⟩ : syracuseStep 2068811 = 3103217) B3103217
theorem B922009 : Blo 542804 922009 := bstep (se 2 (by rfl) ⟨345753, by rfl⟩ : syracuseStep 922009 = 691507) B691507
theorem B1839563 : Blo 542804 1839563 := bstep (se 1 (by rfl) ⟨1379672, by rfl⟩ : syracuseStep 1839563 = 2759345) B2759345
theorem B2069009 : Blo 542804 2069009 := bstep (se 2 (by rfl) ⟨775878, by rfl⟩ : syracuseStep 2069009 = 1551757) B1551757
theorem B1839833 : Blo 542804 1839833 := bstep (se 2 (by rfl) ⟨689937, by rfl⟩ : syracuseStep 1839833 = 1379875) B1379875
theorem B1381171 : Blo 542804 1381171 := bstep (se 1 (by rfl) ⟨1035878, by rfl⟩ : syracuseStep 1381171 = 2071757) B2071757
theorem B1381313 : Blo 542804 1381313 := bstep (se 2 (by rfl) ⟨517992, by rfl⟩ : syracuseStep 1381313 = 1035985) B1035985
theorem B922583 : Blo 542804 922583 := bstep (se 1 (by rfl) ⟨691937, by rfl⟩ : syracuseStep 922583 = 1383875) B1383875
theorem B922711 : Blo 542804 922711 := bstep (se 1 (by rfl) ⟨692033, by rfl⟩ : syracuseStep 922711 = 1384067) B1384067
theorem B2331737 : Blo 542804 2331737 := bstep (se 2 (by rfl) ⟨874401, by rfl⟩ : syracuseStep 2331737 = 1748803) B1748803
theorem B2757725 : Blo 542804 2757725 := bstep (se 3 (by rfl) ⟨517073, by rfl⟩ : syracuseStep 2757725 = 1034147) B1034147
theorem B2331821 : Blo 542804 2331821 := bstep (se 3 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 2331821 = 874433) B874433
theorem B2069783 : Blo 542804 2069783 := bstep (se 1 (by rfl) ⟨1552337, by rfl⟩ : syracuseStep 2069783 = 3104675) B3104675
theorem B1840535 : Blo 542804 1840535 := bstep (se 1 (by rfl) ⟨1380401, by rfl⟩ : syracuseStep 1840535 = 2760803) B2760803
theorem B2069981 : Blo 542804 2069981 := bstep (se 3 (by rfl) ⟨388121, by rfl⟩ : syracuseStep 2069981 = 776243) B776243
theorem B2103043 : Blo 542804 2103043 := bstep (se 1 (by rfl) ⟨1577282, by rfl⟩ : syracuseStep 2103043 = 3154565) B3154565
theorem B1546073 : Blo 542804 1546073 := bstep (se 2 (by rfl) ⟨579777, by rfl⟩ : syracuseStep 1546073 = 1159555) B1159555
theorem B3938179 : Blo 542804 3938179 := bstep (se 1 (by rfl) ⟨2953634, by rfl⟩ : syracuseStep 3938179 = 5907269) B5907269
theorem B1841075 : Blo 542804 1841075 := bstep (se 1 (by rfl) ⟨1380806, by rfl⟩ : syracuseStep 1841075 = 2761613) B2761613
theorem B1546391 : Blo 542804 1546391 := bstep (se 1 (by rfl) ⟨1159793, by rfl⟩ : syracuseStep 1546391 = 2319587) B2319587
theorem B1382579 : Blo 542804 1382579 := bstep (se 1 (by rfl) ⟨1036934, by rfl⟩ : syracuseStep 1382579 = 2073869) B2073869
theorem B1841345 : Blo 542804 1841345 := bstep (se 2 (by rfl) ⟨690504, by rfl⟩ : syracuseStep 1841345 = 1381009) B1381009
theorem B1022209 : Blo 542804 1022209 := bstep (se 2 (by rfl) ⟨383328, by rfl⟩ : syracuseStep 1022209 = 766657) B766657
theorem B4135373 : Blo 542804 4135373 := bstep (se 3 (by rfl) ⟨775382, by rfl⟩ : syracuseStep 4135373 = 1550765) B1550765
theorem B825815 : Blo 542804 825815 := bstep (se 1 (by rfl) ⟨619361, by rfl⟩ : syracuseStep 825815 = 1238723) B1238723
theorem B2202187 : Blo 542804 2202187 := bstep (se 1 (by rfl) ⟨1651640, by rfl⟩ : syracuseStep 2202187 = 3303281) B3303281
theorem B15702659 : Blo 542804 15702659 := bstep (se 1 (by rfl) ⟨11776994, by rfl⟩ : syracuseStep 15702659 = 23553989) B23553989
theorem B1383115 : Blo 542804 1383115 := bstep (se 1 (by rfl) ⟨1037336, by rfl⟩ : syracuseStep 1383115 = 2074673) B2074673
theorem B1841885 : Blo 542804 1841885 := bstep (se 3 (by rfl) ⟨345353, by rfl⟩ : syracuseStep 1841885 = 690707) B690707
theorem B1383257 : Blo 542804 1383257 := bstep (se 2 (by rfl) ⟨518721, by rfl⟩ : syracuseStep 1383257 = 1037443) B1037443
theorem B1973143 : Blo 542804 1973143 := bstep (se 1 (by rfl) ⟨1479857, by rfl⟩ : syracuseStep 1973143 = 2959715) B2959715
theorem B4135859 : Blo 542804 4135859 := bstep (se 1 (by rfl) ⟨3101894, by rfl⟩ : syracuseStep 4135859 = 6203789) B6203789
theorem B1547201 : Blo 542804 1547201 := bstep (se 2 (by rfl) ⟨580200, by rfl⟩ : syracuseStep 1547201 = 1160401) B1160401
theorem B2759831 : Blo 542804 2759831 := bstep (se 1 (by rfl) ⟨2069873, by rfl⟩ : syracuseStep 2759831 = 4139747) B4139747
theorem B2071939 : Blo 542804 2071939 := bstep (se 1 (by rfl) ⟨1553954, by rfl⟩ : syracuseStep 2071939 = 3107909) B3107909
theorem B2203031 : Blo 542804 2203031 := bstep (se 1 (by rfl) ⟨1652273, by rfl⟩ : syracuseStep 2203031 = 3304547) B3304547
theorem B1384087 : Blo 542804 1384087 := bstep (se 1 (by rfl) ⟨1038065, by rfl⟩ : syracuseStep 1384087 = 2076131) B2076131
theorem B2072243 : Blo 542804 2072243 := bstep (se 1 (by rfl) ⟨1554182, by rfl⟩ : syracuseStep 2072243 = 3108365) B3108365
theorem B1843019 : Blo 542804 1843019 := bstep (se 1 (by rfl) ⟨1382264, by rfl⟩ : syracuseStep 1843019 = 2764529) B2764529
theorem B1744919 : Blo 542804 1744919 := bstep (se 1 (by rfl) ⟨1308689, by rfl⟩ : syracuseStep 1744919 = 2617379) B2617379
theorem B3940427 : Blo 542804 3940427 := bstep (se 1 (by rfl) ⟨2955320, by rfl⟩ : syracuseStep 3940427 = 5910641) B5910641
theorem B1843289 : Blo 542804 1843289 := bstep (se 2 (by rfl) ⟨691233, by rfl⟩ : syracuseStep 1843289 = 1382467) B1382467
theorem B2072897 : Blo 542804 2072897 := bstep (se 2 (by rfl) ⟨777336, by rfl⟩ : syracuseStep 2072897 = 1554673) B1554673
theorem B4137317 : Blo 542804 4137317 := bstep (se 4 (by rfl) ⟨387873, by rfl⟩ : syracuseStep 4137317 = 775747) B775747
theorem B2335169 : Blo 542804 2335169 := bstep (se 2 (by rfl) ⟨875688, by rfl⟩ : syracuseStep 2335169 = 1751377) B1751377
theorem B3318317 : Blo 542804 3318317 := bstep (se 3 (by rfl) ⟨622184, by rfl⟩ : syracuseStep 3318317 = 1244369) B1244369
theorem B1745459 : Blo 542804 1745459 := bstep (se 1 (by rfl) ⟨1309094, by rfl⟩ : syracuseStep 1745459 = 2618189) B2618189
theorem B1548875 : Blo 542804 1548875 := bstep (se 1 (by rfl) ⟨1161656, by rfl⟩ : syracuseStep 1548875 = 2323313) B2323313
theorem B17703629 : Blo 542804 17703629 := bstep (se 3 (by rfl) ⟨3319430, by rfl⟩ : syracuseStep 17703629 = 6638861) B6638861
theorem B1221335 : Blo 542804 1221335 := bstep (se 1 (by rfl) ⟨916001, by rfl⟩ : syracuseStep 1221335 = 1832003) B1832003
theorem B1843991 : Blo 542804 1843991 := bstep (se 1 (by rfl) ⟨1382993, by rfl⟩ : syracuseStep 1843991 = 2765987) B2765987
theorem B4137803 : Blo 542804 4137803 := bstep (se 1 (by rfl) ⟨3103352, by rfl⟩ : syracuseStep 4137803 = 6206705) B6206705
theorem B1221515 : Blo 542804 1221515 := bstep (se 1 (by rfl) ⟨916136, by rfl⟩ : syracuseStep 1221515 = 1832273) B1832273
theorem B1221569 : Blo 542804 1221569 := bstep (se 2 (by rfl) ⟨458088, by rfl⟩ : syracuseStep 1221569 = 916177) B916177
theorem B1221785 : Blo 542804 1221785 := bstep (se 2 (by rfl) ⟨458169, by rfl⟩ : syracuseStep 1221785 = 916339) B916339
theorem B1746137 : Blo 542804 1746137 := bstep (se 2 (by rfl) ⟨654801, by rfl⟩ : syracuseStep 1746137 = 1309603) B1309603
theorem B1221875 : Blo 542804 1221875 := bstep (se 1 (by rfl) ⟨916406, by rfl⟩ : syracuseStep 1221875 = 1832813) B1832813
theorem B664843 : Blo 542804 664843 := bstep (se 1 (by rfl) ⟨498632, by rfl⟩ : syracuseStep 664843 = 997265) B997265
theorem B1221911 : Blo 542804 1221911 := bstep (se 1 (by rfl) ⟨916433, by rfl⟩ : syracuseStep 1221911 = 1832867) B1832867
theorem B1844531 : Blo 542804 1844531 := bstep (se 1 (by rfl) ⟨1383398, by rfl⟩ : syracuseStep 1844531 = 2766797) B2766797
theorem B1680733 : Blo 542804 1680733 := bstep (se 3 (by rfl) ⟨315137, by rfl⟩ : syracuseStep 1680733 = 630275) B630275
theorem B2205073 : Blo 542804 2205073 := bstep (se 2 (by rfl) ⟨826902, by rfl⟩ : syracuseStep 2205073 = 1653805) B1653805
theorem B2205107 : Blo 542804 2205107 := bstep (se 1 (by rfl) ⟨1653830, by rfl⟩ : syracuseStep 2205107 = 3307661) B3307661
theorem B1222091 : Blo 542804 1222091 := bstep (se 1 (by rfl) ⟨916568, by rfl⟩ : syracuseStep 1222091 = 1833137) B1833137
theorem B1222145 : Blo 542804 1222145 := bstep (se 2 (by rfl) ⟨458304, by rfl⟩ : syracuseStep 1222145 = 916609) B916609
theorem B2074157 : Blo 542804 2074157 := bstep (se 3 (by rfl) ⟨388904, by rfl⟩ : syracuseStep 2074157 = 777809) B777809
theorem B1844801 : Blo 542804 1844801 := bstep (se 2 (by rfl) ⟨691800, by rfl⟩ : syracuseStep 1844801 = 1383601) B1383601
theorem B2074187 : Blo 542804 2074187 := bstep (se 1 (by rfl) ⟨1555640, by rfl⟩ : syracuseStep 2074187 = 3111281) B3111281
theorem B1222361 : Blo 542804 1222361 := bstep (se 2 (by rfl) ⟨458385, by rfl⟩ : syracuseStep 1222361 = 916771) B916771
theorem B1222451 : Blo 542804 1222451 := bstep (se 1 (by rfl) ⟨916838, by rfl⟩ : syracuseStep 1222451 = 1833677) B1833677
theorem B1222487 : Blo 542804 1222487 := bstep (se 1 (by rfl) ⟨916865, by rfl⟩ : syracuseStep 1222487 = 1833731) B1833731
theorem B1550173 : Blo 542804 1550173 := bstep (se 3 (by rfl) ⟨290657, by rfl⟩ : syracuseStep 1550173 = 581315) B581315
theorem B1222667 : Blo 542804 1222667 := bstep (se 1 (by rfl) ⟨917000, by rfl⟩ : syracuseStep 1222667 = 1834001) B1834001
theorem B1222721 : Blo 542804 1222721 := bstep (se 2 (by rfl) ⟨458520, by rfl⟩ : syracuseStep 1222721 = 917041) B917041
theorem B1845341 : Blo 542804 1845341 := bstep (se 3 (by rfl) ⟨346001, by rfl⟩ : syracuseStep 1845341 = 692003) B692003
theorem B1550515 : Blo 542804 1550515 := bstep (se 1 (by rfl) ⟨1162886, by rfl⟩ : syracuseStep 1550515 = 2325773) B2325773
theorem B2074841 : Blo 542804 2074841 := bstep (se 2 (by rfl) ⟨778065, by rfl⟩ : syracuseStep 2074841 = 1556131) B1556131
theorem B1222937 : Blo 542804 1222937 := bstep (se 2 (by rfl) ⟨458601, by rfl⟩ : syracuseStep 1222937 = 917203) B917203
theorem B1223027 : Blo 542804 1223027 := bstep (se 1 (by rfl) ⟨917270, by rfl⟩ : syracuseStep 1223027 = 1834541) B1834541
theorem B1223063 : Blo 542804 1223063 := bstep (se 1 (by rfl) ⟨917297, by rfl⟩ : syracuseStep 1223063 = 1834595) B1834595
theorem B1747379 : Blo 542804 1747379 := bstep (se 1 (by rfl) ⟨1310534, by rfl⟩ : syracuseStep 1747379 = 2621069) B2621069
theorem B2075159 : Blo 542804 2075159 := bstep (se 1 (by rfl) ⟨1556369, by rfl⟩ : syracuseStep 2075159 = 3112739) B3112739
theorem B1223243 : Blo 542804 1223243 := bstep (se 1 (by rfl) ⟨917432, by rfl⟩ : syracuseStep 1223243 = 1834865) B1834865
theorem B1223297 : Blo 542804 1223297 := bstep (se 2 (by rfl) ⟨458736, by rfl⟩ : syracuseStep 1223297 = 917473) B917473
theorem B2763395 : Blo 542804 2763395 := bstep (se 1 (by rfl) ⟨2072546, by rfl⟩ : syracuseStep 2763395 = 4145093) B4145093
theorem B1223513 : Blo 542804 1223513 := bstep (se 2 (by rfl) ⟨458817, by rfl⟩ : syracuseStep 1223513 = 917635) B917635
theorem B1223603 : Blo 542804 1223603 := bstep (se 1 (by rfl) ⟨917702, by rfl⟩ : syracuseStep 1223603 = 1835405) B1835405
theorem B1223639 : Blo 542804 1223639 := bstep (se 1 (by rfl) ⟨917729, by rfl⟩ : syracuseStep 1223639 = 1835459) B1835459
theorem B830539 : Blo 542804 830539 := bstep (se 1 (by rfl) ⟨622904, by rfl⟩ : syracuseStep 830539 = 1245809) B1245809
theorem B1551449 : Blo 542804 1551449 := bstep (se 2 (by rfl) ⟨581793, by rfl⟩ : syracuseStep 1551449 = 1163587) B1163587
theorem B1223819 : Blo 542804 1223819 := bstep (se 1 (by rfl) ⟨917864, by rfl⟩ : syracuseStep 1223819 = 1835729) B1835729
theorem B2075827 : Blo 542804 2075827 := bstep (se 1 (by rfl) ⟨1556870, by rfl⟩ : syracuseStep 2075827 = 3113741) B3113741
theorem B1223873 : Blo 542804 1223873 := bstep (se 2 (by rfl) ⟨458952, by rfl⟩ : syracuseStep 1223873 = 917905) B917905
theorem B1322201 : Blo 542804 1322201 := bstep (se 2 (by rfl) ⟨495825, by rfl⟩ : syracuseStep 1322201 = 991651) B991651
theorem B6991109 : Blo 542804 6991109 := bstep (se 4 (by rfl) ⟨655416, by rfl⟩ : syracuseStep 6991109 = 1310833) B1310833
theorem B1224089 : Blo 542804 1224089 := bstep (se 2 (by rfl) ⟨459033, by rfl⟩ : syracuseStep 1224089 = 918067) B918067
theorem B1224179 : Blo 542804 1224179 := bstep (se 1 (by rfl) ⟨918134, by rfl⟩ : syracuseStep 1224179 = 1836269) B1836269
theorem B1224215 : Blo 542804 1224215 := bstep (se 1 (by rfl) ⟨918161, by rfl⟩ : syracuseStep 1224215 = 1836323) B1836323
theorem B929431 : Blo 542804 929431 := bstep (se 1 (by rfl) ⟨697073, by rfl⟩ : syracuseStep 929431 = 1394147) B1394147
theorem B1224395 : Blo 542804 1224395 := bstep (se 1 (by rfl) ⟨918296, by rfl⟩ : syracuseStep 1224395 = 1836593) B1836593
theorem B1224449 : Blo 542804 1224449 := bstep (se 2 (by rfl) ⟨459168, by rfl⟩ : syracuseStep 1224449 = 918337) B918337
theorem B1224665 : Blo 542804 1224665 := bstep (se 2 (by rfl) ⟨459249, by rfl⟩ : syracuseStep 1224665 = 918499) B918499
theorem B11972569 : Blo 542804 11972569 := bstep (se 2 (by rfl) ⟨4489713, by rfl⟩ : syracuseStep 11972569 = 8979427) B8979427
theorem B3485713 : Blo 542804 3485713 := bstep (se 2 (by rfl) ⟨1307142, by rfl⟩ : syracuseStep 3485713 = 2614285) B2614285
theorem B1224755 : Blo 542804 1224755 := bstep (se 1 (by rfl) ⟨918566, by rfl⟩ : syracuseStep 1224755 = 1837133) B1837133
theorem B995393 : Blo 542804 995393 := bstep (se 2 (by rfl) ⟨373272, by rfl⟩ : syracuseStep 995393 = 746545) B746545
theorem B1224791 : Blo 542804 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B1224971 : Blo 542804 1224971 := bstep (se 1 (by rfl) ⟨918728, by rfl⟩ : syracuseStep 1224971 = 1837457) B1837457
theorem B1225025 : Blo 542804 1225025 := bstep (se 2 (by rfl) ⟨459384, by rfl⟩ : syracuseStep 1225025 = 918769) B918769
theorem B2240947 : Blo 542804 2240947 := bstep (se 1 (by rfl) ⟨1680710, by rfl⟩ : syracuseStep 2240947 = 3361421) B3361421
theorem B1552861 : Blo 542804 1552861 := bstep (se 3 (by rfl) ⟨291161, by rfl⟩ : syracuseStep 1552861 = 582323) B582323
theorem B1225241 : Blo 542804 1225241 := bstep (se 2 (by rfl) ⟨459465, by rfl⟩ : syracuseStep 1225241 = 918931) B918931
theorem B1225331 : Blo 542804 1225331 := bstep (se 1 (by rfl) ⟨918998, by rfl⟩ : syracuseStep 1225331 = 1837997) B1837997
theorem B1225367 : Blo 542804 1225367 := bstep (se 1 (by rfl) ⟨919025, by rfl⟩ : syracuseStep 1225367 = 1838051) B1838051
theorem B1553089 : Blo 542804 1553089 := bstep (se 2 (by rfl) ⟨582408, by rfl⟩ : syracuseStep 1553089 = 1164817) B1164817
theorem B1225547 : Blo 542804 1225547 := bstep (se 1 (by rfl) ⟨919160, by rfl⟩ : syracuseStep 1225547 = 1838321) B1838321
theorem B3486557 : Blo 542804 3486557 := bstep (se 3 (by rfl) ⟨653729, by rfl⟩ : syracuseStep 3486557 = 1307459) B1307459
theorem B1225601 : Blo 542804 1225601 := bstep (se 2 (by rfl) ⟨459600, by rfl⟩ : syracuseStep 1225601 = 919201) B919201
theorem B734105 : Blo 542804 734105 := bstep (se 2 (by rfl) ⟨275289, by rfl⟩ : syracuseStep 734105 = 550579) B550579
theorem B1160153 : Blo 542804 1160153 := bstep (se 2 (by rfl) ⟨435057, by rfl⟩ : syracuseStep 1160153 = 870115) B870115
theorem B1553431 : Blo 542804 1553431 := bstep (se 1 (by rfl) ⟨1165073, by rfl⟩ : syracuseStep 1553431 = 2330147) B2330147
theorem B3912749 : Blo 542804 3912749 := bstep (se 3 (by rfl) ⟨733640, by rfl⟩ : syracuseStep 3912749 = 1467281) B1467281
theorem B1225817 : Blo 542804 1225817 := bstep (se 2 (by rfl) ⟨459681, by rfl⟩ : syracuseStep 1225817 = 919363) B919363
theorem B1225907 : Blo 542804 1225907 := bstep (se 1 (by rfl) ⟨919430, by rfl⟩ : syracuseStep 1225907 = 1838861) B1838861
theorem B1225943 : Blo 542804 1225943 := bstep (se 1 (by rfl) ⟨919457, by rfl⟩ : syracuseStep 1225943 = 1838915) B1838915
theorem B1160563 : Blo 542804 1160563 := bstep (se 1 (by rfl) ⟨870422, by rfl⟩ : syracuseStep 1160563 = 1740845) B1740845
theorem B1226123 : Blo 542804 1226123 := bstep (se 1 (by rfl) ⟨919592, by rfl⟩ : syracuseStep 1226123 = 1839185) B1839185
theorem B1226177 : Blo 542804 1226177 := bstep (se 2 (by rfl) ⟨459816, by rfl⟩ : syracuseStep 1226177 = 919633) B919633
theorem B4961893 : Blo 542804 4961893 := bstep (se 4 (by rfl) ⟨465177, by rfl⟩ : syracuseStep 4961893 = 930355) B930355
theorem B1160819 : Blo 542804 1160819 := bstep (se 1 (by rfl) ⟨870614, by rfl⟩ : syracuseStep 1160819 = 1741229) B1741229
theorem B997015 : Blo 542804 997015 := bstep (se 1 (by rfl) ⟨747761, by rfl⟩ : syracuseStep 997015 = 1495523) B1495523
theorem B1226393 : Blo 542804 1226393 := bstep (se 2 (by rfl) ⟨459897, by rfl⟩ : syracuseStep 1226393 = 919795) B919795
theorem B1554137 : Blo 542804 1554137 := bstep (se 2 (by rfl) ⟨582801, by rfl⟩ : syracuseStep 1554137 = 1165603) B1165603
theorem B1226483 : Blo 542804 1226483 := bstep (se 1 (by rfl) ⟨919862, by rfl⟩ : syracuseStep 1226483 = 1839725) B1839725
theorem B1226519 : Blo 542804 1226519 := bstep (se 1 (by rfl) ⟨919889, by rfl⟩ : syracuseStep 1226519 = 1839779) B1839779
theorem B1226699 : Blo 542804 1226699 := bstep (se 1 (by rfl) ⟨920024, by rfl⟩ : syracuseStep 1226699 = 1840049) B1840049
theorem B604139 : Blo 542804 604139 := bstep (se 1 (by rfl) ⟨453104, by rfl⟩ : syracuseStep 604139 = 906209) B906209
theorem B1226753 : Blo 542804 1226753 := bstep (se 2 (by rfl) ⟨460032, by rfl⟩ : syracuseStep 1226753 = 920065) B920065
theorem B4143149 : Blo 542804 4143149 := bstep (se 3 (by rfl) ⟨776840, by rfl⟩ : syracuseStep 4143149 = 1553681) B1553681
theorem B15677509 : Blo 542804 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B1226969 : Blo 542804 1226969 := bstep (se 2 (by rfl) ⟨460113, by rfl⟩ : syracuseStep 1226969 = 920227) B920227
theorem B2767121 : Blo 542804 2767121 := bstep (se 2 (by rfl) ⟨1037670, by rfl⟩ : syracuseStep 2767121 = 2075341) B2075341
theorem B1227059 : Blo 542804 1227059 := bstep (se 1 (by rfl) ⟨920294, by rfl⟩ : syracuseStep 1227059 = 1840589) B1840589
theorem B1227095 : Blo 542804 1227095 := bstep (se 1 (by rfl) ⟨920321, by rfl⟩ : syracuseStep 1227095 = 1840643) B1840643
theorem B2767283 : Blo 542804 2767283 := bstep (se 1 (by rfl) ⟨2075462, by rfl⟩ : syracuseStep 2767283 = 4150925) B4150925
theorem B1227275 : Blo 542804 1227275 := bstep (se 1 (by rfl) ⟨920456, by rfl⟩ : syracuseStep 1227275 = 1840913) B1840913
theorem B1161793 : Blo 542804 1161793 := bstep (se 2 (by rfl) ⟨435672, by rfl⟩ : syracuseStep 1161793 = 871345) B871345
theorem B1227329 : Blo 542804 1227329 := bstep (se 2 (by rfl) ⟨460248, by rfl⟩ : syracuseStep 1227329 = 920497) B920497
theorem B1030745 : Blo 542804 1030745 := bstep (se 2 (by rfl) ⟨386529, by rfl⟩ : syracuseStep 1030745 = 773059) B773059
theorem B5880451 : Blo 542804 5880451 := bstep (se 1 (by rfl) ⟨4410338, by rfl⟩ : syracuseStep 5880451 = 8820677) B8820677
theorem B1227545 : Blo 542804 1227545 := bstep (se 2 (by rfl) ⟨460329, by rfl⟩ : syracuseStep 1227545 = 920659) B920659
theorem B1227635 : Blo 542804 1227635 := bstep (se 1 (by rfl) ⟨920726, by rfl⟩ : syracuseStep 1227635 = 1841453) B1841453
theorem B1227671 : Blo 542804 1227671 := bstep (se 1 (by rfl) ⟨920753, by rfl⟩ : syracuseStep 1227671 = 1841507) B1841507
theorem B1227851 : Blo 542804 1227851 := bstep (se 1 (by rfl) ⟨920888, by rfl⟩ : syracuseStep 1227851 = 1841777) B1841777
theorem B1227905 : Blo 542804 1227905 := bstep (se 2 (by rfl) ⟨460464, by rfl⟩ : syracuseStep 1227905 = 920929) B920929
theorem B1031383 : Blo 542804 1031383 := bstep (se 1 (by rfl) ⟨773537, by rfl⟩ : syracuseStep 1031383 = 1547075) B1547075
theorem B1555777 : Blo 542804 1555777 := bstep (se 2 (by rfl) ⟨583416, by rfl⟩ : syracuseStep 1555777 = 1166833) B1166833
theorem B933209 : Blo 542804 933209 := bstep (se 2 (by rfl) ⟨349953, by rfl⟩ : syracuseStep 933209 = 699907) B699907
theorem B1228121 : Blo 542804 1228121 := bstep (se 2 (by rfl) ⟨460545, by rfl⟩ : syracuseStep 1228121 = 921091) B921091
theorem B3718493 : Blo 542804 3718493 := bstep (se 3 (by rfl) ⟨697217, by rfl⟩ : syracuseStep 3718493 = 1394435) B1394435
theorem B1228211 : Blo 542804 1228211 := bstep (se 1 (by rfl) ⟨921158, by rfl⟩ : syracuseStep 1228211 = 1842317) B1842317
theorem B1228247 : Blo 542804 1228247 := bstep (se 1 (by rfl) ⟨921185, by rfl⟩ : syracuseStep 1228247 = 1842371) B1842371
theorem B1228427 : Blo 542804 1228427 := bstep (se 1 (by rfl) ⟨921320, by rfl⟩ : syracuseStep 1228427 = 1842641) B1842641
theorem B1228481 : Blo 542804 1228481 := bstep (se 2 (by rfl) ⟨460680, by rfl⟩ : syracuseStep 1228481 = 921361) B921361
theorem B1228697 : Blo 542804 1228697 := bstep (se 2 (by rfl) ⟨460761, by rfl⟩ : syracuseStep 1228697 = 921523) B921523
theorem B1228787 : Blo 542804 1228787 := bstep (se 1 (by rfl) ⟨921590, by rfl⟩ : syracuseStep 1228787 = 1843181) B1843181
theorem B1032203 : Blo 542804 1032203 := bstep (se 1 (by rfl) ⟨774152, by rfl⟩ : syracuseStep 1032203 = 1548305) B1548305
theorem B1228823 : Blo 542804 1228823 := bstep (se 1 (by rfl) ⟨921617, by rfl⟩ : syracuseStep 1228823 = 1843235) B1843235
theorem B1032257 : Blo 542804 1032257 := bstep (se 2 (by rfl) ⟨387096, by rfl⟩ : syracuseStep 1032257 = 774193) B774193
theorem B1229003 : Blo 542804 1229003 := bstep (se 1 (by rfl) ⟨921752, by rfl⟩ : syracuseStep 1229003 = 1843505) B1843505
theorem B1229057 : Blo 542804 1229057 := bstep (se 2 (by rfl) ⟨460896, by rfl⟩ : syracuseStep 1229057 = 921793) B921793
theorem B1229273 : Blo 542804 1229273 := bstep (se 2 (by rfl) ⟨460977, by rfl⟩ : syracuseStep 1229273 = 921955) B921955
theorem B1229363 : Blo 542804 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B1229399 : Blo 542804 1229399 := bstep (se 1 (by rfl) ⟨922049, by rfl⟩ : syracuseStep 1229399 = 1844099) B1844099
theorem B14959235 : Blo 542804 14959235 := bstep (se 1 (by rfl) ⟨11219426, by rfl⟩ : syracuseStep 14959235 = 22438853) B22438853
theorem B1163929 : Blo 542804 1163929 := bstep (se 2 (by rfl) ⟨436473, by rfl⟩ : syracuseStep 1163929 = 872947) B872947
theorem B1229579 : Blo 542804 1229579 := bstep (se 1 (by rfl) ⟨922184, by rfl⟩ : syracuseStep 1229579 = 1844369) B1844369
theorem B4965137 : Blo 542804 4965137 := bstep (se 2 (by rfl) ⟨1861926, by rfl⟩ : syracuseStep 4965137 = 3723853) B3723853
theorem B1229633 : Blo 542804 1229633 := bstep (se 2 (by rfl) ⟨461112, by rfl⟩ : syracuseStep 1229633 = 922225) B922225
theorem B4637533 : Blo 542804 4637533 := bstep (se 3 (by rfl) ⟨869537, by rfl⟩ : syracuseStep 4637533 = 1739075) B1739075
theorem B1033175 : Blo 542804 1033175 := bstep (se 1 (by rfl) ⟨774881, by rfl⟩ : syracuseStep 1033175 = 1549763) B1549763
theorem B1131545 : Blo 542804 1131545 := bstep (se 2 (by rfl) ⟨424329, by rfl⟩ : syracuseStep 1131545 = 848659) B848659
theorem B1229849 : Blo 542804 1229849 := bstep (se 2 (by rfl) ⟨461193, by rfl⟩ : syracuseStep 1229849 = 922387) B922387
theorem B1229939 : Blo 542804 1229939 := bstep (se 1 (by rfl) ⟨922454, by rfl⟩ : syracuseStep 1229939 = 1844909) B1844909
theorem B1229975 : Blo 542804 1229975 := bstep (se 1 (by rfl) ⟨922481, by rfl⟩ : syracuseStep 1229975 = 1844963) B1844963
theorem B1230155 : Blo 542804 1230155 := bstep (se 1 (by rfl) ⟨922616, by rfl⟩ : syracuseStep 1230155 = 1845233) B1845233
theorem B1230209 : Blo 542804 1230209 := bstep (se 2 (by rfl) ⟨461328, by rfl⟩ : syracuseStep 1230209 = 922657) B922657
theorem B1033715 : Blo 542804 1033715 := bstep (se 1 (by rfl) ⟨775286, by rfl⟩ : syracuseStep 1033715 = 1550573) B1550573
theorem B1656409 : Blo 542804 1656409 := bstep (se 2 (by rfl) ⟨621153, by rfl⟩ : syracuseStep 1656409 = 1242307) B1242307
theorem B4147037 : Blo 542804 4147037 := bstep (se 3 (by rfl) ⟨777569, by rfl⟩ : syracuseStep 4147037 = 1555139) B1555139
theorem B1034201 : Blo 542804 1034201 := bstep (se 2 (by rfl) ⟨387825, by rfl⟩ : syracuseStep 1034201 = 775651) B775651
theorem B19810325 : Blo 542804 19810325 := bstep (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) B928609
theorem B542807 : Blo 542804 542807 := bstep (se 1 (by rfl) ⟨407105, by rfl⟩ : syracuseStep 542807 = 814211) B814211
theorem B542827 : Blo 542804 542827 := bstep (se 1 (by rfl) ⟨407120, by rfl⟩ : syracuseStep 542827 = 814241) B814241
theorem B542839 : Blo 542804 542839 := bstep (se 1 (by rfl) ⟨407129, by rfl⟩ : syracuseStep 542839 = 814259) B814259
theorem B542859 : Blo 542804 542859 := bstep (se 1 (by rfl) ⟨407144, by rfl⟩ : syracuseStep 542859 = 814289) B814289
theorem B542871 : Blo 542804 542871 := bstep (se 1 (by rfl) ⟨407153, by rfl⟩ : syracuseStep 542871 = 814307) B814307
theorem B542891 : Blo 542804 542891 := bstep (se 1 (by rfl) ⟨407168, by rfl⟩ : syracuseStep 542891 = 814337) B814337
theorem B4475057 : Blo 542804 4475057 := bstep (se 2 (by rfl) ⟨1678146, by rfl⟩ : syracuseStep 4475057 = 3356293) B3356293
theorem B542903 : Blo 542804 542903 := bstep (se 1 (by rfl) ⟨407177, by rfl⟩ : syracuseStep 542903 = 814355) B814355
theorem B542923 : Blo 542804 542923 := bstep (se 1 (by rfl) ⟨407192, by rfl⟩ : syracuseStep 542923 = 814385) B814385
theorem B542935 : Blo 542804 542935 := bstep (se 1 (by rfl) ⟨407201, by rfl⟩ : syracuseStep 542935 = 814403) B814403
theorem B542955 : Blo 542804 542955 := bstep (se 1 (by rfl) ⟨407216, by rfl⟩ : syracuseStep 542955 = 814433) B814433
theorem B7948529 : Blo 542804 7948529 := bstep (se 2 (by rfl) ⟨2980698, by rfl⟩ : syracuseStep 7948529 = 5961397) B5961397
theorem B542967 : Blo 542804 542967 := bstep (se 1 (by rfl) ⟨407225, by rfl⟩ : syracuseStep 542967 = 814451) B814451
theorem B542987 : Blo 542804 542987 := bstep (se 1 (by rfl) ⟨407240, by rfl⟩ : syracuseStep 542987 = 814481) B814481
theorem B542999 : Blo 542804 542999 := bstep (se 1 (by rfl) ⟨407249, by rfl⟩ : syracuseStep 542999 = 814499) B814499
theorem B870679 : Blo 542804 870679 := bstep (se 1 (by rfl) ⟨653009, by rfl⟩ : syracuseStep 870679 = 1306019) B1306019
theorem B543019 : Blo 542804 543019 := bstep (se 1 (by rfl) ⟨407264, by rfl⟩ : syracuseStep 543019 = 814529) B814529
theorem B543031 : Blo 542804 543031 := bstep (se 1 (by rfl) ⟨407273, by rfl⟩ : syracuseStep 543031 = 814547) B814547
theorem B543051 : Blo 542804 543051 := bstep (se 1 (by rfl) ⟨407288, by rfl⟩ : syracuseStep 543051 = 814577) B814577
theorem B543063 : Blo 542804 543063 := bstep (se 1 (by rfl) ⟨407297, by rfl⟩ : syracuseStep 543063 = 814595) B814595
theorem B870743 : Blo 542804 870743 := bstep (se 1 (by rfl) ⟨653057, by rfl⟩ : syracuseStep 870743 = 1306115) B1306115
theorem B543083 : Blo 542804 543083 := bstep (se 1 (by rfl) ⟨407312, by rfl⟩ : syracuseStep 543083 = 814625) B814625
theorem B63883637 : Blo 542804 63883637 := bstep (se 5 (by rfl) ⟨2994545, by rfl⟩ : syracuseStep 63883637 = 5989091) B5989091
theorem B543095 : Blo 542804 543095 := bstep (se 1 (by rfl) ⟨407321, by rfl⟩ : syracuseStep 543095 = 814643) B814643
theorem B543115 : Blo 542804 543115 := bstep (se 1 (by rfl) ⟨407336, by rfl⟩ : syracuseStep 543115 = 814673) B814673
theorem B543127 : Blo 542804 543127 := bstep (se 1 (by rfl) ⟨407345, by rfl⟩ : syracuseStep 543127 = 814691) B814691
theorem B543147 : Blo 542804 543147 := bstep (se 1 (by rfl) ⟨407360, by rfl⟩ : syracuseStep 543147 = 814721) B814721
theorem B543159 : Blo 542804 543159 := bstep (se 1 (by rfl) ⟨407369, by rfl⟩ : syracuseStep 543159 = 814739) B814739
theorem B543179 : Blo 542804 543179 := bstep (se 1 (by rfl) ⟨407384, by rfl⟩ : syracuseStep 543179 = 814769) B814769
theorem B543191 : Blo 542804 543191 := bstep (se 1 (by rfl) ⟨407393, by rfl⟩ : syracuseStep 543191 = 814787) B814787
theorem B543211 : Blo 542804 543211 := bstep (se 1 (by rfl) ⟨407408, by rfl⟩ : syracuseStep 543211 = 814817) B814817
theorem B543223 : Blo 542804 543223 := bstep (se 1 (by rfl) ⟨407417, by rfl⟩ : syracuseStep 543223 = 814835) B814835
theorem B543243 : Blo 542804 543243 := bstep (se 1 (by rfl) ⟨407432, by rfl⟩ : syracuseStep 543243 = 814865) B814865
theorem B9423373 : Blo 542804 9423373 := bstep (se 3 (by rfl) ⟨1766882, by rfl⟩ : syracuseStep 9423373 = 3533765) B3533765
theorem B5884433 : Blo 542804 5884433 := bstep (se 2 (by rfl) ⟨2206662, by rfl⟩ : syracuseStep 5884433 = 4413325) B4413325
theorem B543255 : Blo 542804 543255 := bstep (se 1 (by rfl) ⟨407441, by rfl⟩ : syracuseStep 543255 = 814883) B814883
theorem B543275 : Blo 542804 543275 := bstep (se 1 (by rfl) ⟨407456, by rfl⟩ : syracuseStep 543275 = 814913) B814913
theorem B543287 : Blo 542804 543287 := bstep (se 1 (by rfl) ⟨407465, by rfl⟩ : syracuseStep 543287 = 814931) B814931
theorem B543307 : Blo 542804 543307 := bstep (se 1 (by rfl) ⟨407480, by rfl⟩ : syracuseStep 543307 = 814961) B814961
theorem B543319 : Blo 542804 543319 := bstep (se 1 (by rfl) ⟨407489, by rfl⟩ : syracuseStep 543319 = 814979) B814979
theorem B543339 : Blo 542804 543339 := bstep (se 1 (by rfl) ⟨407504, by rfl⟩ : syracuseStep 543339 = 815009) B815009
theorem B543351 : Blo 542804 543351 := bstep (se 1 (by rfl) ⟨407513, by rfl⟩ : syracuseStep 543351 = 815027) B815027
theorem B543371 : Blo 542804 543371 := bstep (se 1 (by rfl) ⟨407528, by rfl⟩ : syracuseStep 543371 = 815057) B815057
theorem B543383 : Blo 542804 543383 := bstep (se 1 (by rfl) ⟨407537, by rfl⟩ : syracuseStep 543383 = 815075) B815075
theorem B3492503 : Blo 542804 3492503 := bstep (se 1 (by rfl) ⟨2619377, by rfl⟩ : syracuseStep 3492503 = 5238755) B5238755
theorem B543403 : Blo 542804 543403 := bstep (se 1 (by rfl) ⟨407552, by rfl⟩ : syracuseStep 543403 = 815105) B815105
theorem B543415 : Blo 542804 543415 := bstep (se 1 (by rfl) ⟨407561, by rfl⟩ : syracuseStep 543415 = 815123) B815123
theorem B543435 : Blo 542804 543435 := bstep (se 1 (by rfl) ⟨407576, by rfl⟩ : syracuseStep 543435 = 815153) B815153
theorem B543447 : Blo 542804 543447 := bstep (se 1 (by rfl) ⟨407585, by rfl⟩ : syracuseStep 543447 = 815171) B815171
theorem B543467 : Blo 542804 543467 := bstep (se 1 (by rfl) ⟨407600, by rfl⟩ : syracuseStep 543467 = 815201) B815201
theorem B543479 : Blo 542804 543479 := bstep (se 1 (by rfl) ⟨407609, by rfl⟩ : syracuseStep 543479 = 815219) B815219
theorem B1166081 : Blo 542804 1166081 := bstep (se 2 (by rfl) ⟨437280, by rfl⟩ : syracuseStep 1166081 = 874561) B874561
theorem B543499 : Blo 542804 543499 := bstep (se 1 (by rfl) ⟨407624, by rfl⟩ : syracuseStep 543499 = 815249) B815249
theorem B543511 : Blo 542804 543511 := bstep (se 1 (by rfl) ⟨407633, by rfl⟩ : syracuseStep 543511 = 815267) B815267
theorem B543531 : Blo 542804 543531 := bstep (se 1 (by rfl) ⟨407648, by rfl⟩ : syracuseStep 543531 = 815297) B815297
theorem B543543 : Blo 542804 543543 := bstep (se 1 (by rfl) ⟨407657, by rfl⟩ : syracuseStep 543543 = 815315) B815315
theorem B543563 : Blo 542804 543563 := bstep (se 1 (by rfl) ⟨407672, by rfl⟩ : syracuseStep 543563 = 815345) B815345
theorem B543575 : Blo 542804 543575 := bstep (se 1 (by rfl) ⟨407681, by rfl⟩ : syracuseStep 543575 = 815363) B815363
theorem B1166167 : Blo 542804 1166167 := bstep (se 1 (by rfl) ⟨874625, by rfl⟩ : syracuseStep 1166167 = 1749251) B1749251
theorem B543595 : Blo 542804 543595 := bstep (se 1 (by rfl) ⟨407696, by rfl⟩ : syracuseStep 543595 = 815393) B815393
theorem B543607 : Blo 542804 543607 := bstep (se 1 (by rfl) ⟨407705, by rfl⟩ : syracuseStep 543607 = 815411) B815411
theorem B543627 : Blo 542804 543627 := bstep (se 1 (by rfl) ⟨407720, by rfl⟩ : syracuseStep 543627 = 815441) B815441
theorem B871307 : Blo 542804 871307 := bstep (se 1 (by rfl) ⟨653480, by rfl⟩ : syracuseStep 871307 = 1306961) B1306961
theorem B543639 : Blo 542804 543639 := bstep (se 1 (by rfl) ⟨407729, by rfl⟩ : syracuseStep 543639 = 815459) B815459
theorem B543659 : Blo 542804 543659 := bstep (se 1 (by rfl) ⟨407744, by rfl⟩ : syracuseStep 543659 = 815489) B815489
theorem B543671 : Blo 542804 543671 := bstep (se 1 (by rfl) ⟨407753, by rfl⟩ : syracuseStep 543671 = 815507) B815507
theorem B543691 : Blo 542804 543691 := bstep (se 1 (by rfl) ⟨407768, by rfl⟩ : syracuseStep 543691 = 815537) B815537
theorem B543703 : Blo 542804 543703 := bstep (se 1 (by rfl) ⟨407777, by rfl⟩ : syracuseStep 543703 = 815555) B815555
theorem B543723 : Blo 542804 543723 := bstep (se 1 (by rfl) ⟨407792, by rfl⟩ : syracuseStep 543723 = 815585) B815585
theorem B543735 : Blo 542804 543735 := bstep (se 1 (by rfl) ⟨407801, by rfl⟩ : syracuseStep 543735 = 815603) B815603
theorem B543755 : Blo 542804 543755 := bstep (se 1 (by rfl) ⟨407816, by rfl⟩ : syracuseStep 543755 = 815633) B815633
theorem B543767 : Blo 542804 543767 := bstep (se 1 (by rfl) ⟨407825, by rfl⟩ : syracuseStep 543767 = 815651) B815651
theorem B543787 : Blo 542804 543787 := bstep (se 1 (by rfl) ⟨407840, by rfl⟩ : syracuseStep 543787 = 815681) B815681
theorem B543799 : Blo 542804 543799 := bstep (se 1 (by rfl) ⟨407849, by rfl⟩ : syracuseStep 543799 = 815699) B815699
theorem B543819 : Blo 542804 543819 := bstep (se 1 (by rfl) ⟨407864, by rfl⟩ : syracuseStep 543819 = 815729) B815729
theorem B871499 : Blo 542804 871499 := bstep (se 1 (by rfl) ⟨653624, by rfl⟩ : syracuseStep 871499 = 1307249) B1307249
theorem B543831 : Blo 542804 543831 := bstep (se 1 (by rfl) ⟨407873, by rfl⟩ : syracuseStep 543831 = 815747) B815747
theorem B543851 : Blo 542804 543851 := bstep (se 1 (by rfl) ⟨407888, by rfl⟩ : syracuseStep 543851 = 815777) B815777
theorem B543863 : Blo 542804 543863 := bstep (se 1 (by rfl) ⟨407897, by rfl⟩ : syracuseStep 543863 = 815795) B815795
theorem B543883 : Blo 542804 543883 := bstep (se 1 (by rfl) ⟨407912, by rfl⟩ : syracuseStep 543883 = 815825) B815825
theorem B543895 : Blo 542804 543895 := bstep (se 1 (by rfl) ⟨407921, by rfl⟩ : syracuseStep 543895 = 815843) B815843
theorem B543915 : Blo 542804 543915 := bstep (se 1 (by rfl) ⟨407936, by rfl⟩ : syracuseStep 543915 = 815873) B815873
theorem B543927 : Blo 542804 543927 := bstep (se 1 (by rfl) ⟨407945, by rfl⟩ : syracuseStep 543927 = 815891) B815891
theorem B543947 : Blo 542804 543947 := bstep (se 1 (by rfl) ⟨407960, by rfl⟩ : syracuseStep 543947 = 815921) B815921
theorem B543959 : Blo 542804 543959 := bstep (se 1 (by rfl) ⟨407969, by rfl⟩ : syracuseStep 543959 = 815939) B815939
theorem B543979 : Blo 542804 543979 := bstep (se 1 (by rfl) ⟨407984, by rfl⟩ : syracuseStep 543979 = 815969) B815969
theorem B543991 : Blo 542804 543991 := bstep (se 1 (by rfl) ⟨407993, by rfl⟩ : syracuseStep 543991 = 815987) B815987
theorem B544011 : Blo 542804 544011 := bstep (se 1 (by rfl) ⟨408008, by rfl⟩ : syracuseStep 544011 = 816017) B816017
theorem B544023 : Blo 542804 544023 := bstep (se 1 (by rfl) ⟨408017, by rfl⟩ : syracuseStep 544023 = 816035) B816035
theorem B773401 : Blo 542804 773401 := bstep (se 2 (by rfl) ⟨290025, by rfl⟩ : syracuseStep 773401 = 580051) B580051
theorem B544043 : Blo 542804 544043 := bstep (se 1 (by rfl) ⟨408032, by rfl⟩ : syracuseStep 544043 = 816065) B816065
theorem B544055 : Blo 542804 544055 := bstep (se 1 (by rfl) ⟨408041, by rfl⟩ : syracuseStep 544055 = 816083) B816083
theorem B544075 : Blo 542804 544075 := bstep (se 1 (by rfl) ⟨408056, by rfl⟩ : syracuseStep 544075 = 816113) B816113
theorem B544087 : Blo 542804 544087 := bstep (se 1 (by rfl) ⟨408065, by rfl⟩ : syracuseStep 544087 = 816131) B816131
theorem B544107 : Blo 542804 544107 := bstep (se 1 (by rfl) ⟨408080, by rfl⟩ : syracuseStep 544107 = 816161) B816161
theorem B544119 : Blo 542804 544119 := bstep (se 1 (by rfl) ⟨408089, by rfl⟩ : syracuseStep 544119 = 816179) B816179
theorem B544139 : Blo 542804 544139 := bstep (se 1 (by rfl) ⟨408104, by rfl⟩ : syracuseStep 544139 = 816209) B816209
theorem B1035659 : Blo 542804 1035659 := bstep (se 1 (by rfl) ⟨776744, by rfl⟩ : syracuseStep 1035659 = 1553489) B1553489
theorem B544151 : Blo 542804 544151 := bstep (se 1 (by rfl) ⟨408113, by rfl⟩ : syracuseStep 544151 = 816227) B816227
theorem B544171 : Blo 542804 544171 := bstep (se 1 (by rfl) ⟨408128, by rfl⟩ : syracuseStep 544171 = 816257) B816257
theorem B544183 : Blo 542804 544183 := bstep (se 1 (by rfl) ⟨408137, by rfl⟩ : syracuseStep 544183 = 816275) B816275
theorem B544203 : Blo 542804 544203 := bstep (se 1 (by rfl) ⟨408152, by rfl⟩ : syracuseStep 544203 = 816305) B816305
theorem B544215 : Blo 542804 544215 := bstep (se 1 (by rfl) ⟨408161, by rfl⟩ : syracuseStep 544215 = 816323) B816323
theorem B544235 : Blo 542804 544235 := bstep (se 1 (by rfl) ⟨408176, by rfl⟩ : syracuseStep 544235 = 816353) B816353
theorem B544247 : Blo 542804 544247 := bstep (se 1 (by rfl) ⟨408185, by rfl⟩ : syracuseStep 544247 = 816371) B816371
theorem B544267 : Blo 542804 544267 := bstep (se 1 (by rfl) ⟨408200, by rfl⟩ : syracuseStep 544267 = 816401) B816401
theorem B544279 : Blo 542804 544279 := bstep (se 1 (by rfl) ⟨408209, by rfl⟩ : syracuseStep 544279 = 816419) B816419
theorem B8474147 : Blo 542804 8474147 := bstep (se 1 (by rfl) ⟨6355610, by rfl⟩ : syracuseStep 8474147 = 12711221) B12711221
theorem B544299 : Blo 542804 544299 := bstep (se 1 (by rfl) ⟨408224, by rfl⟩ : syracuseStep 544299 = 816449) B816449
theorem B544311 : Blo 542804 544311 := bstep (se 1 (by rfl) ⟨408233, by rfl⟩ : syracuseStep 544311 = 816467) B816467
theorem B1035841 : Blo 542804 1035841 := bstep (se 2 (by rfl) ⟨388440, by rfl⟩ : syracuseStep 1035841 = 776881) B776881
theorem B544331 : Blo 542804 544331 := bstep (se 1 (by rfl) ⟨408248, by rfl⟩ : syracuseStep 544331 = 816497) B816497
theorem B544343 : Blo 542804 544343 := bstep (se 1 (by rfl) ⟨408257, by rfl⟩ : syracuseStep 544343 = 816515) B816515
theorem B544363 : Blo 542804 544363 := bstep (se 1 (by rfl) ⟨408272, by rfl⟩ : syracuseStep 544363 = 816545) B816545
theorem B544375 : Blo 542804 544375 := bstep (se 1 (by rfl) ⟨408281, by rfl⟩ : syracuseStep 544375 = 816563) B816563
theorem B544395 : Blo 542804 544395 := bstep (se 1 (by rfl) ⟨408296, by rfl⟩ : syracuseStep 544395 = 816593) B816593
theorem B1166987 : Blo 542804 1166987 := bstep (se 1 (by rfl) ⟨875240, by rfl⟩ : syracuseStep 1166987 = 1750481) B1750481
theorem B544407 : Blo 542804 544407 := bstep (se 1 (by rfl) ⟨408305, by rfl⟩ : syracuseStep 544407 = 816611) B816611
theorem B544427 : Blo 542804 544427 := bstep (se 1 (by rfl) ⟨408320, by rfl⟩ : syracuseStep 544427 = 816641) B816641
theorem B544439 : Blo 542804 544439 := bstep (se 1 (by rfl) ⟨408329, by rfl⟩ : syracuseStep 544439 = 816659) B816659
theorem B544459 : Blo 542804 544459 := bstep (se 1 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 544459 = 816689) B816689
theorem B544471 : Blo 542804 544471 := bstep (se 1 (by rfl) ⟨408353, by rfl⟩ : syracuseStep 544471 = 816707) B816707
theorem B544491 : Blo 542804 544491 := bstep (se 1 (by rfl) ⟨408368, by rfl⟩ : syracuseStep 544491 = 816737) B816737
theorem B544503 : Blo 542804 544503 := bstep (se 1 (by rfl) ⟨408377, by rfl⟩ : syracuseStep 544503 = 816755) B816755
theorem B544523 : Blo 542804 544523 := bstep (se 1 (by rfl) ⟨408392, by rfl⟩ : syracuseStep 544523 = 816785) B816785
theorem B544535 : Blo 542804 544535 := bstep (se 1 (by rfl) ⟨408401, by rfl⟩ : syracuseStep 544535 = 816803) B816803
theorem B4476707 : Blo 542804 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B544555 : Blo 542804 544555 := bstep (se 1 (by rfl) ⟨408416, by rfl⟩ : syracuseStep 544555 = 816833) B816833
theorem B544567 : Blo 542804 544567 := bstep (se 1 (by rfl) ⟨408425, by rfl⟩ : syracuseStep 544567 = 816851) B816851
theorem B544587 : Blo 542804 544587 := bstep (se 1 (by rfl) ⟨408440, by rfl⟩ : syracuseStep 544587 = 816881) B816881
theorem B544599 : Blo 542804 544599 := bstep (se 1 (by rfl) ⟨408449, by rfl⟩ : syracuseStep 544599 = 816899) B816899
theorem B4771685 : Blo 542804 4771685 := bstep (se 4 (by rfl) ⟨447345, by rfl⟩ : syracuseStep 4771685 = 894691) B894691
theorem B544619 : Blo 542804 544619 := bstep (se 1 (by rfl) ⟨408464, by rfl⟩ : syracuseStep 544619 = 816929) B816929
theorem B544631 : Blo 542804 544631 := bstep (se 1 (by rfl) ⟨408473, by rfl⟩ : syracuseStep 544631 = 816947) B816947
theorem B544651 : Blo 542804 544651 := bstep (se 1 (by rfl) ⟨408488, by rfl⟩ : syracuseStep 544651 = 816977) B816977
theorem B544663 : Blo 542804 544663 := bstep (se 1 (by rfl) ⟨408497, by rfl⟩ : syracuseStep 544663 = 816995) B816995
theorem B544683 : Blo 542804 544683 := bstep (se 1 (by rfl) ⟨408512, by rfl⟩ : syracuseStep 544683 = 817025) B817025
theorem B544695 : Blo 542804 544695 := bstep (se 1 (by rfl) ⟨408521, by rfl⟩ : syracuseStep 544695 = 817043) B817043
theorem B544715 : Blo 542804 544715 := bstep (se 1 (by rfl) ⟨408536, by rfl⟩ : syracuseStep 544715 = 817073) B817073
theorem B544727 : Blo 542804 544727 := bstep (se 1 (by rfl) ⟨408545, by rfl⟩ : syracuseStep 544727 = 817091) B817091
theorem B544747 : Blo 542804 544747 := bstep (se 1 (by rfl) ⟨408560, by rfl⟩ : syracuseStep 544747 = 817121) B817121
theorem B544759 : Blo 542804 544759 := bstep (se 1 (by rfl) ⟨408569, by rfl⟩ : syracuseStep 544759 = 817139) B817139
theorem B1036289 : Blo 542804 1036289 := bstep (se 2 (by rfl) ⟨388608, by rfl⟩ : syracuseStep 1036289 = 777217) B777217
theorem B544779 : Blo 542804 544779 := bstep (se 1 (by rfl) ⟨408584, by rfl⟩ : syracuseStep 544779 = 817169) B817169
theorem B544791 : Blo 542804 544791 := bstep (se 1 (by rfl) ⟨408593, by rfl⟩ : syracuseStep 544791 = 817187) B817187
theorem B872473 : Blo 542804 872473 := bstep (se 2 (by rfl) ⟨327177, by rfl⟩ : syracuseStep 872473 = 654355) B654355
theorem B544811 : Blo 542804 544811 := bstep (se 1 (by rfl) ⟨408608, by rfl⟩ : syracuseStep 544811 = 817217) B817217
theorem B544823 : Blo 542804 544823 := bstep (se 1 (by rfl) ⟨408617, by rfl⟩ : syracuseStep 544823 = 817235) B817235
theorem B544843 : Blo 542804 544843 := bstep (se 1 (by rfl) ⟨408632, by rfl⟩ : syracuseStep 544843 = 817265) B817265
theorem B544855 : Blo 542804 544855 := bstep (se 1 (by rfl) ⟨408641, by rfl⟩ : syracuseStep 544855 = 817283) B817283
theorem B544875 : Blo 542804 544875 := bstep (se 1 (by rfl) ⟨408656, by rfl⟩ : syracuseStep 544875 = 817313) B817313
theorem B544887 : Blo 542804 544887 := bstep (se 1 (by rfl) ⟨408665, by rfl⟩ : syracuseStep 544887 = 817331) B817331
theorem B544907 : Blo 542804 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B544919 : Blo 542804 544919 := bstep (se 1 (by rfl) ⟨408689, by rfl⟩ : syracuseStep 544919 = 817379) B817379
theorem B544939 : Blo 542804 544939 := bstep (se 1 (by rfl) ⟨408704, by rfl⟩ : syracuseStep 544939 = 817409) B817409
theorem B544951 : Blo 542804 544951 := bstep (se 1 (by rfl) ⟨408713, by rfl⟩ : syracuseStep 544951 = 817427) B817427
theorem B1396939 : Blo 542804 1396939 := bstep (se 1 (by rfl) ⟨1047704, by rfl⟩ : syracuseStep 1396939 = 2095409) B2095409
theorem B544971 : Blo 542804 544971 := bstep (se 1 (by rfl) ⟨408728, by rfl⟩ : syracuseStep 544971 = 817457) B817457
theorem B544983 : Blo 542804 544983 := bstep (se 1 (by rfl) ⟨408737, by rfl⟩ : syracuseStep 544983 = 817475) B817475
theorem B545003 : Blo 542804 545003 := bstep (se 1 (by rfl) ⟨408752, by rfl⟩ : syracuseStep 545003 = 817505) B817505
theorem B545015 : Blo 542804 545015 := bstep (se 1 (by rfl) ⟨408761, by rfl⟩ : syracuseStep 545015 = 817523) B817523
theorem B545035 : Blo 542804 545035 := bstep (se 1 (by rfl) ⟨408776, by rfl⟩ : syracuseStep 545035 = 817553) B817553
theorem B545047 : Blo 542804 545047 := bstep (se 1 (by rfl) ⟨408785, by rfl⟩ : syracuseStep 545047 = 817571) B817571
theorem B545067 : Blo 542804 545067 := bstep (se 1 (by rfl) ⟨408800, by rfl⟩ : syracuseStep 545067 = 817601) B817601
theorem B545079 : Blo 542804 545079 := bstep (se 1 (by rfl) ⟨408809, by rfl⟩ : syracuseStep 545079 = 817619) B817619
theorem B545099 : Blo 542804 545099 := bstep (se 1 (by rfl) ⟨408824, by rfl⟩ : syracuseStep 545099 = 817649) B817649
theorem B545111 : Blo 542804 545111 := bstep (se 1 (by rfl) ⟨408833, by rfl⟩ : syracuseStep 545111 = 817667) B817667
theorem B1036631 : Blo 542804 1036631 := bstep (se 1 (by rfl) ⟨777473, by rfl⟩ : syracuseStep 1036631 = 1554947) B1554947
theorem B545131 : Blo 542804 545131 := bstep (se 1 (by rfl) ⟨408848, by rfl⟩ : syracuseStep 545131 = 817697) B817697
theorem B545143 : Blo 542804 545143 := bstep (se 1 (by rfl) ⟨408857, by rfl⟩ : syracuseStep 545143 = 817715) B817715
theorem B610699 : Blo 542804 610699 := bstep (se 1 (by rfl) ⟨458024, by rfl⟩ : syracuseStep 610699 = 916049) B916049
theorem B545163 : Blo 542804 545163 := bstep (se 1 (by rfl) ⟨408872, by rfl⟩ : syracuseStep 545163 = 817745) B817745
theorem B545175 : Blo 542804 545175 := bstep (se 1 (by rfl) ⟨408881, by rfl⟩ : syracuseStep 545175 = 817763) B817763
theorem B545195 : Blo 542804 545195 := bstep (se 1 (by rfl) ⟨408896, by rfl⟩ : syracuseStep 545195 = 817793) B817793
theorem B545207 : Blo 542804 545207 := bstep (se 1 (by rfl) ⟨408905, by rfl⟩ : syracuseStep 545207 = 817811) B817811
theorem B545227 : Blo 542804 545227 := bstep (se 1 (by rfl) ⟨408920, by rfl⟩ : syracuseStep 545227 = 817841) B817841
theorem B545239 : Blo 542804 545239 := bstep (se 1 (by rfl) ⟨408929, by rfl⟩ : syracuseStep 545239 = 817859) B817859
theorem B872921 : Blo 542804 872921 := bstep (se 2 (by rfl) ⟨327345, by rfl⟩ : syracuseStep 872921 = 654691) B654691
theorem B545259 : Blo 542804 545259 := bstep (se 1 (by rfl) ⟨408944, by rfl⟩ : syracuseStep 545259 = 817889) B817889
theorem B610807 : Blo 542804 610807 := bstep (se 1 (by rfl) ⟨458105, by rfl⟩ : syracuseStep 610807 = 916211) B916211
theorem B545271 : Blo 542804 545271 := bstep (se 1 (by rfl) ⟨408953, by rfl⟩ : syracuseStep 545271 = 817907) B817907
theorem B545291 : Blo 542804 545291 := bstep (se 1 (by rfl) ⟨408968, by rfl⟩ : syracuseStep 545291 = 817937) B817937
theorem B545303 : Blo 542804 545303 := bstep (se 1 (by rfl) ⟨408977, by rfl⟩ : syracuseStep 545303 = 817955) B817955
theorem B545323 : Blo 542804 545323 := bstep (se 1 (by rfl) ⟨408992, by rfl⟩ : syracuseStep 545323 = 817985) B817985
theorem B545335 : Blo 542804 545335 := bstep (se 1 (by rfl) ⟨409001, by rfl⟩ : syracuseStep 545335 = 818003) B818003
theorem B2609729 : Blo 542804 2609729 := bstep (se 2 (by rfl) ⟨978648, by rfl⟩ : syracuseStep 2609729 = 1957297) B1957297
theorem B545355 : Blo 542804 545355 := bstep (se 1 (by rfl) ⟨409016, by rfl⟩ : syracuseStep 545355 = 818033) B818033
theorem B545367 : Blo 542804 545367 := bstep (se 1 (by rfl) ⟨409025, by rfl⟩ : syracuseStep 545367 = 818051) B818051
theorem B545387 : Blo 542804 545387 := bstep (se 1 (by rfl) ⟨409040, by rfl⟩ : syracuseStep 545387 = 818081) B818081
theorem B545399 : Blo 542804 545399 := bstep (se 1 (by rfl) ⟨409049, by rfl⟩ : syracuseStep 545399 = 818099) B818099
theorem B545419 : Blo 542804 545419 := bstep (se 1 (by rfl) ⟨409064, by rfl⟩ : syracuseStep 545419 = 818129) B818129
theorem B545431 : Blo 542804 545431 := bstep (se 1 (by rfl) ⟨409073, by rfl⟩ : syracuseStep 545431 = 818147) B818147
theorem B610987 : Blo 542804 610987 := bstep (se 1 (by rfl) ⟨458240, by rfl⟩ : syracuseStep 610987 = 916481) B916481
theorem B545451 : Blo 542804 545451 := bstep (se 1 (by rfl) ⟨409088, by rfl⟩ : syracuseStep 545451 = 818177) B818177
theorem B545463 : Blo 542804 545463 := bstep (se 1 (by rfl) ⟨409097, by rfl⟩ : syracuseStep 545463 = 818195) B818195
theorem B774859 : Blo 542804 774859 := bstep (se 1 (by rfl) ⟨581144, by rfl⟩ : syracuseStep 774859 = 1162289) B1162289
theorem B545483 : Blo 542804 545483 := bstep (se 1 (by rfl) ⟨409112, by rfl⟩ : syracuseStep 545483 = 818225) B818225
theorem B545495 : Blo 542804 545495 := bstep (se 1 (by rfl) ⟨409121, by rfl⟩ : syracuseStep 545495 = 818243) B818243
theorem B545515 : Blo 542804 545515 := bstep (se 1 (by rfl) ⟨409136, by rfl⟩ : syracuseStep 545515 = 818273) B818273
theorem B545527 : Blo 542804 545527 := bstep (se 1 (by rfl) ⟨409145, by rfl⟩ : syracuseStep 545527 = 818291) B818291
theorem B545547 : Blo 542804 545547 := bstep (se 1 (by rfl) ⟨409160, by rfl⟩ : syracuseStep 545547 = 818321) B818321
theorem B611095 : Blo 542804 611095 := bstep (se 1 (by rfl) ⟨458321, by rfl⟩ : syracuseStep 611095 = 916643) B916643
theorem B545559 : Blo 542804 545559 := bstep (se 1 (by rfl) ⟨409169, by rfl⟩ : syracuseStep 545559 = 818339) B818339
theorem B545579 : Blo 542804 545579 := bstep (se 1 (by rfl) ⟨409184, by rfl⟩ : syracuseStep 545579 = 818369) B818369
theorem B545591 : Blo 542804 545591 := bstep (se 1 (by rfl) ⟨409193, by rfl⟩ : syracuseStep 545591 = 818387) B818387
theorem B545611 : Blo 542804 545611 := bstep (se 1 (by rfl) ⟨409208, by rfl⟩ : syracuseStep 545611 = 818417) B818417
theorem B545623 : Blo 542804 545623 := bstep (se 1 (by rfl) ⟨409217, by rfl⟩ : syracuseStep 545623 = 818435) B818435
theorem B545643 : Blo 542804 545643 := bstep (se 1 (by rfl) ⟨409232, by rfl⟩ : syracuseStep 545643 = 818465) B818465
theorem B545655 : Blo 542804 545655 := bstep (se 1 (by rfl) ⟨409241, by rfl⟩ : syracuseStep 545655 = 818483) B818483
theorem B545675 : Blo 542804 545675 := bstep (se 1 (by rfl) ⟨409256, by rfl⟩ : syracuseStep 545675 = 818513) B818513
theorem B545687 : Blo 542804 545687 := bstep (se 1 (by rfl) ⟨409265, by rfl⟩ : syracuseStep 545687 = 818531) B818531
theorem B545707 : Blo 542804 545707 := bstep (se 1 (by rfl) ⟨409280, by rfl⟩ : syracuseStep 545707 = 818561) B818561
theorem B545719 : Blo 542804 545719 := bstep (se 1 (by rfl) ⟨409289, by rfl⟩ : syracuseStep 545719 = 818579) B818579
theorem B611275 : Blo 542804 611275 := bstep (se 1 (by rfl) ⟨458456, by rfl⟩ : syracuseStep 611275 = 916913) B916913
theorem B545739 : Blo 542804 545739 := bstep (se 1 (by rfl) ⟨409304, by rfl⟩ : syracuseStep 545739 = 818609) B818609
theorem B545751 : Blo 542804 545751 := bstep (se 1 (by rfl) ⟨409313, by rfl⟩ : syracuseStep 545751 = 818627) B818627
theorem B1659865 : Blo 542804 1659865 := bstep (se 2 (by rfl) ⟨622449, by rfl⟩ : syracuseStep 1659865 = 1244899) B1244899
theorem B545771 : Blo 542804 545771 := bstep (se 1 (by rfl) ⟨409328, by rfl⟩ : syracuseStep 545771 = 818657) B818657
theorem B1037299 : Blo 542804 1037299 := bstep (se 1 (by rfl) ⟨777974, by rfl⟩ : syracuseStep 1037299 = 1555949) B1555949
theorem B545783 : Blo 542804 545783 := bstep (se 1 (by rfl) ⟨409337, by rfl⟩ : syracuseStep 545783 = 818675) B818675
theorem B545803 : Blo 542804 545803 := bstep (se 1 (by rfl) ⟨409352, by rfl⟩ : syracuseStep 545803 = 818705) B818705
theorem B545815 : Blo 542804 545815 := bstep (se 1 (by rfl) ⟨409361, by rfl⟩ : syracuseStep 545815 = 818723) B818723
theorem B7099427 : Blo 542804 7099427 := bstep (se 1 (by rfl) ⟨5324570, by rfl⟩ : syracuseStep 7099427 = 10649141) B10649141
theorem B545835 : Blo 542804 545835 := bstep (se 1 (by rfl) ⟨409376, by rfl⟩ : syracuseStep 545835 = 818753) B818753
theorem B611383 : Blo 542804 611383 := bstep (se 1 (by rfl) ⟨458537, by rfl⟩ : syracuseStep 611383 = 917075) B917075
theorem B545847 : Blo 542804 545847 := bstep (se 1 (by rfl) ⟨409385, by rfl⟩ : syracuseStep 545847 = 818771) B818771
theorem B545867 : Blo 542804 545867 := bstep (se 1 (by rfl) ⟨409400, by rfl⟩ : syracuseStep 545867 = 818801) B818801
theorem B545879 : Blo 542804 545879 := bstep (se 1 (by rfl) ⟨409409, by rfl⟩ : syracuseStep 545879 = 818819) B818819
theorem B545899 : Blo 542804 545899 := bstep (se 1 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 545899 = 818849) B818849
theorem B545911 : Blo 542804 545911 := bstep (se 1 (by rfl) ⟨409433, by rfl⟩ : syracuseStep 545911 = 818867) B818867
theorem B1135745 : Blo 542804 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B545931 : Blo 542804 545931 := bstep (se 1 (by rfl) ⟨409448, by rfl⟩ : syracuseStep 545931 = 818897) B818897
theorem B545943 : Blo 542804 545943 := bstep (se 1 (by rfl) ⟨409457, by rfl⟩ : syracuseStep 545943 = 818915) B818915
theorem B545963 : Blo 542804 545963 := bstep (se 1 (by rfl) ⟨409472, by rfl⟩ : syracuseStep 545963 = 818945) B818945
theorem B545975 : Blo 542804 545975 := bstep (se 1 (by rfl) ⟨409481, by rfl⟩ : syracuseStep 545975 = 818963) B818963
theorem B545995 : Blo 542804 545995 := bstep (se 1 (by rfl) ⟨409496, by rfl⟩ : syracuseStep 545995 = 818993) B818993
theorem B546007 : Blo 542804 546007 := bstep (se 1 (by rfl) ⟨409505, by rfl⟩ : syracuseStep 546007 = 819011) B819011
theorem B611563 : Blo 542804 611563 := bstep (se 1 (by rfl) ⟨458672, by rfl⟩ : syracuseStep 611563 = 917345) B917345
theorem B546027 : Blo 542804 546027 := bstep (se 1 (by rfl) ⟨409520, by rfl⟩ : syracuseStep 546027 = 819041) B819041
theorem B546039 : Blo 542804 546039 := bstep (se 1 (by rfl) ⟨409529, by rfl⟩ : syracuseStep 546039 = 819059) B819059
theorem B546059 : Blo 542804 546059 := bstep (se 1 (by rfl) ⟨409544, by rfl⟩ : syracuseStep 546059 = 819089) B819089
theorem B546071 : Blo 542804 546071 := bstep (se 1 (by rfl) ⟨409553, by rfl⟩ : syracuseStep 546071 = 819107) B819107
theorem B546091 : Blo 542804 546091 := bstep (se 1 (by rfl) ⟨409568, by rfl⟩ : syracuseStep 546091 = 819137) B819137
theorem B546103 : Blo 542804 546103 := bstep (se 1 (by rfl) ⟨409577, by rfl⟩ : syracuseStep 546103 = 819155) B819155
theorem B546123 : Blo 542804 546123 := bstep (se 1 (by rfl) ⟨409592, by rfl⟩ : syracuseStep 546123 = 819185) B819185
theorem B611671 : Blo 542804 611671 := bstep (se 1 (by rfl) ⟨458753, by rfl⟩ : syracuseStep 611671 = 917507) B917507
theorem B546135 : Blo 542804 546135 := bstep (se 1 (by rfl) ⟨409601, by rfl⟩ : syracuseStep 546135 = 819203) B819203
theorem B546155 : Blo 542804 546155 := bstep (se 1 (by rfl) ⟨409616, by rfl⟩ : syracuseStep 546155 = 819233) B819233
theorem B546167 : Blo 542804 546167 := bstep (se 1 (by rfl) ⟨409625, by rfl⟩ : syracuseStep 546167 = 819251) B819251
theorem B546187 : Blo 542804 546187 := bstep (se 1 (by rfl) ⟨409640, by rfl⟩ : syracuseStep 546187 = 819281) B819281
theorem B546199 : Blo 542804 546199 := bstep (se 1 (by rfl) ⟨409649, by rfl⟩ : syracuseStep 546199 = 819299) B819299
theorem B546219 : Blo 542804 546219 := bstep (se 1 (by rfl) ⟨409664, by rfl⟩ : syracuseStep 546219 = 819329) B819329
theorem B1037747 : Blo 542804 1037747 := bstep (se 1 (by rfl) ⟨778310, by rfl⟩ : syracuseStep 1037747 = 1556621) B1556621
theorem B546231 : Blo 542804 546231 := bstep (se 1 (by rfl) ⟨409673, by rfl⟩ : syracuseStep 546231 = 819347) B819347
theorem B546251 : Blo 542804 546251 := bstep (se 1 (by rfl) ⟨409688, by rfl⟩ : syracuseStep 546251 = 819377) B819377
theorem B546263 : Blo 542804 546263 := bstep (se 1 (by rfl) ⟨409697, by rfl⟩ : syracuseStep 546263 = 819395) B819395
theorem B1037785 : Blo 542804 1037785 := bstep (se 2 (by rfl) ⟨389169, by rfl⟩ : syracuseStep 1037785 = 778339) B778339
theorem B546283 : Blo 542804 546283 := bstep (se 1 (by rfl) ⟨409712, by rfl⟩ : syracuseStep 546283 = 819425) B819425
theorem B546295 : Blo 542804 546295 := bstep (se 1 (by rfl) ⟨409721, by rfl⟩ : syracuseStep 546295 = 819443) B819443
theorem B611851 : Blo 542804 611851 := bstep (se 1 (by rfl) ⟨458888, by rfl⟩ : syracuseStep 611851 = 917777) B917777
theorem B546315 : Blo 542804 546315 := bstep (se 1 (by rfl) ⟨409736, by rfl⟩ : syracuseStep 546315 = 819473) B819473
theorem B546327 : Blo 542804 546327 := bstep (se 1 (by rfl) ⟨409745, by rfl⟩ : syracuseStep 546327 = 819491) B819491
theorem B546347 : Blo 542804 546347 := bstep (se 1 (by rfl) ⟨409760, by rfl⟩ : syracuseStep 546347 = 819521) B819521
theorem B546359 : Blo 542804 546359 := bstep (se 1 (by rfl) ⟨409769, by rfl⟩ : syracuseStep 546359 = 819539) B819539
theorem B546379 : Blo 542804 546379 := bstep (se 1 (by rfl) ⟨409784, by rfl⟩ : syracuseStep 546379 = 819569) B819569
theorem B546391 : Blo 542804 546391 := bstep (se 1 (by rfl) ⟨409793, by rfl⟩ : syracuseStep 546391 = 819587) B819587
theorem B546411 : Blo 542804 546411 := bstep (se 1 (by rfl) ⟨409808, by rfl⟩ : syracuseStep 546411 = 819617) B819617
theorem B611959 : Blo 542804 611959 := bstep (se 1 (by rfl) ⟨458969, by rfl⟩ : syracuseStep 611959 = 917939) B917939
theorem B546423 : Blo 542804 546423 := bstep (se 1 (by rfl) ⟨409817, by rfl⟩ : syracuseStep 546423 = 819635) B819635
theorem B546443 : Blo 542804 546443 := bstep (se 1 (by rfl) ⟨409832, by rfl⟩ : syracuseStep 546443 = 819665) B819665
theorem B546455 : Blo 542804 546455 := bstep (se 1 (by rfl) ⟨409841, by rfl⟩ : syracuseStep 546455 = 819683) B819683
theorem B546475 : Blo 542804 546475 := bstep (se 1 (by rfl) ⟨409856, by rfl⟩ : syracuseStep 546475 = 819713) B819713
theorem B546487 : Blo 542804 546487 := bstep (se 1 (by rfl) ⟨409865, by rfl⟩ : syracuseStep 546487 = 819731) B819731
theorem B546507 : Blo 542804 546507 := bstep (se 1 (by rfl) ⟨409880, by rfl⟩ : syracuseStep 546507 = 819761) B819761
theorem B546519 : Blo 542804 546519 := bstep (se 1 (by rfl) ⟨409889, by rfl⟩ : syracuseStep 546519 = 819779) B819779
theorem B546539 : Blo 542804 546539 := bstep (se 1 (by rfl) ⟨409904, by rfl⟩ : syracuseStep 546539 = 819809) B819809
theorem B546551 : Blo 542804 546551 := bstep (se 1 (by rfl) ⟨409913, by rfl⟩ : syracuseStep 546551 = 819827) B819827
theorem B546571 : Blo 542804 546571 := bstep (se 1 (by rfl) ⟨409928, by rfl⟩ : syracuseStep 546571 = 819857) B819857
theorem B546583 : Blo 542804 546583 := bstep (se 1 (by rfl) ⟨409937, by rfl⟩ : syracuseStep 546583 = 819875) B819875
theorem B612139 : Blo 542804 612139 := bstep (se 1 (by rfl) ⟨459104, by rfl⟩ : syracuseStep 612139 = 918209) B918209
theorem B546603 : Blo 542804 546603 := bstep (se 1 (by rfl) ⟨409952, by rfl⟩ : syracuseStep 546603 = 819905) B819905
theorem B546615 : Blo 542804 546615 := bstep (se 1 (by rfl) ⟨409961, by rfl⟩ : syracuseStep 546615 = 819923) B819923
theorem B1103681 : Blo 542804 1103681 := bstep (se 2 (by rfl) ⟨413880, by rfl⟩ : syracuseStep 1103681 = 827761) B827761
theorem B546635 : Blo 542804 546635 := bstep (se 1 (by rfl) ⟨409976, by rfl⟩ : syracuseStep 546635 = 819953) B819953
theorem B546647 : Blo 542804 546647 := bstep (se 1 (by rfl) ⟨409985, by rfl⟩ : syracuseStep 546647 = 819971) B819971
theorem B18143075 : Blo 542804 18143075 := bstep (se 1 (by rfl) ⟨13607306, by rfl⟩ : syracuseStep 18143075 = 27214613) B27214613
theorem B546667 : Blo 542804 546667 := bstep (se 1 (by rfl) ⟨410000, by rfl⟩ : syracuseStep 546667 = 820001) B820001
theorem B546679 : Blo 542804 546679 := bstep (se 1 (by rfl) ⟨410009, by rfl⟩ : syracuseStep 546679 = 820019) B820019
theorem B546699 : Blo 542804 546699 := bstep (se 1 (by rfl) ⟨410024, by rfl⟩ : syracuseStep 546699 = 820049) B820049
theorem B612247 : Blo 542804 612247 := bstep (se 1 (by rfl) ⟨459185, by rfl⟩ : syracuseStep 612247 = 918371) B918371
theorem B546711 : Blo 542804 546711 := bstep (se 1 (by rfl) ⟨410033, by rfl⟩ : syracuseStep 546711 = 820067) B820067
theorem B776089 : Blo 542804 776089 := bstep (se 2 (by rfl) ⟨291033, by rfl⟩ : syracuseStep 776089 = 582067) B582067
theorem B546731 : Blo 542804 546731 := bstep (se 1 (by rfl) ⟨410048, by rfl⟩ : syracuseStep 546731 = 820097) B820097
theorem B546743 : Blo 542804 546743 := bstep (se 1 (by rfl) ⟨410057, by rfl⟩ : syracuseStep 546743 = 820115) B820115
theorem B546763 : Blo 542804 546763 := bstep (se 1 (by rfl) ⟨410072, by rfl⟩ : syracuseStep 546763 = 820145) B820145
theorem B546775 : Blo 542804 546775 := bstep (se 1 (by rfl) ⟨410081, by rfl⟩ : syracuseStep 546775 = 820163) B820163
theorem B546795 : Blo 542804 546795 := bstep (se 1 (by rfl) ⟨410096, by rfl⟩ : syracuseStep 546795 = 820193) B820193
theorem B3102785 : Blo 542804 3102785 := bstep (se 2 (by rfl) ⟨1163544, by rfl⟩ : syracuseStep 3102785 = 2327089) B2327089
theorem B612427 : Blo 542804 612427 := bstep (se 1 (by rfl) ⟨459320, by rfl⟩ : syracuseStep 612427 = 918641) B918641
theorem B5036107 : Blo 542804 5036107 := bstep (se 1 (by rfl) ⟨3777080, by rfl⟩ : syracuseStep 5036107 = 7554161) B7554161
theorem B612535 : Blo 542804 612535 := bstep (se 1 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 612535 = 918803) B918803
theorem B612715 : Blo 542804 612715 := bstep (se 1 (by rfl) ⟨459536, by rfl⟩ : syracuseStep 612715 = 919073) B919073
theorem B4708813 : Blo 542804 4708813 := bstep (se 3 (by rfl) ⟨882902, by rfl⟩ : syracuseStep 4708813 = 1765805) B1765805
theorem B612823 : Blo 542804 612823 := bstep (se 1 (by rfl) ⟨459617, by rfl⟩ : syracuseStep 612823 = 919235) B919235
theorem B2611673 : Blo 542804 2611673 := bstep (se 2 (by rfl) ⟨979377, by rfl⟩ : syracuseStep 2611673 = 1958755) B1958755
theorem B19847693 : Blo 542804 19847693 := bstep (se 3 (by rfl) ⟨3721442, by rfl⟩ : syracuseStep 19847693 = 7442885) B7442885
theorem B1956403 : Blo 542804 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B613003 : Blo 542804 613003 := bstep (se 1 (by rfl) ⟨459752, by rfl⟩ : syracuseStep 613003 = 919505) B919505
theorem B613111 : Blo 542804 613111 := bstep (se 1 (by rfl) ⟨459833, by rfl⟩ : syracuseStep 613111 = 919667) B919667
theorem B613291 : Blo 542804 613291 := bstep (se 1 (by rfl) ⟨459968, by rfl⟩ : syracuseStep 613291 = 919937) B919937
theorem B580555 : Blo 542804 580555 := bstep (se 1 (by rfl) ⟨435416, by rfl⟩ : syracuseStep 580555 = 870833) B870833
theorem B1104857 : Blo 542804 1104857 := bstep (se 2 (by rfl) ⟨414321, by rfl⟩ : syracuseStep 1104857 = 828643) B828643
theorem B613399 : Blo 542804 613399 := bstep (se 1 (by rfl) ⟨460049, by rfl⟩ : syracuseStep 613399 = 920099) B920099
theorem B613579 : Blo 542804 613579 := bstep (se 1 (by rfl) ⟨460184, by rfl⟩ : syracuseStep 613579 = 920369) B920369
theorem B777433 : Blo 542804 777433 := bstep (se 2 (by rfl) ⟨291537, by rfl⟩ : syracuseStep 777433 = 583075) B583075
theorem B613687 : Blo 542804 613687 := bstep (se 1 (by rfl) ⟨460265, by rfl⟩ : syracuseStep 613687 = 920531) B920531
theorem B777547 : Blo 542804 777547 := bstep (se 1 (by rfl) ⟨583160, by rfl⟩ : syracuseStep 777547 = 1166321) B1166321
theorem B2612611 : Blo 542804 2612611 := bstep (se 1 (by rfl) ⟨1959458, by rfl⟩ : syracuseStep 2612611 = 3918917) B3918917
theorem B3923417 : Blo 542804 3923417 := bstep (se 2 (by rfl) ⟨1471281, by rfl⟩ : syracuseStep 3923417 = 2942563) B2942563
theorem B613867 : Blo 542804 613867 := bstep (se 1 (by rfl) ⟨460400, by rfl⟩ : syracuseStep 613867 = 920801) B920801
theorem B613975 : Blo 542804 613975 := bstep (se 1 (by rfl) ⟨460481, by rfl⟩ : syracuseStep 613975 = 920963) B920963
theorem B614155 : Blo 542804 614155 := bstep (se 1 (by rfl) ⟨460616, by rfl⟩ : syracuseStep 614155 = 921233) B921233
theorem B614263 : Blo 542804 614263 := bstep (se 1 (by rfl) ⟨460697, by rfl⟩ : syracuseStep 614263 = 921395) B921395
theorem B614443 : Blo 542804 614443 := bstep (se 1 (by rfl) ⟨460832, by rfl⟩ : syracuseStep 614443 = 921665) B921665
theorem B614551 : Blo 542804 614551 := bstep (se 1 (by rfl) ⟨460913, by rfl⟩ : syracuseStep 614551 = 921827) B921827
theorem B909515 : Blo 542804 909515 := bstep (se 1 (by rfl) ⟨682136, by rfl⟩ : syracuseStep 909515 = 1364273) B1364273
theorem B93184277 : Blo 542804 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B2318615 : Blo 542804 2318615 := bstep (se 1 (by rfl) ⟨1738961, by rfl⟩ : syracuseStep 2318615 = 3477923) B3477923
theorem B614731 : Blo 542804 614731 := bstep (se 1 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 614731 = 922097) B922097
theorem B3105175 : Blo 542804 3105175 := bstep (se 1 (by rfl) ⟨2328881, by rfl⟩ : syracuseStep 3105175 = 4657763) B4657763
theorem B614839 : Blo 542804 614839 := bstep (se 1 (by rfl) ⟨461129, by rfl⟩ : syracuseStep 614839 = 922259) B922259
theorem B615019 : Blo 542804 615019 := bstep (se 1 (by rfl) ⟨461264, by rfl⟩ : syracuseStep 615019 = 922529) B922529
theorem B615127 : Blo 542804 615127 := bstep (se 1 (by rfl) ⟨461345, by rfl⟩ : syracuseStep 615127 = 922691) B922691
theorem B1106689 : Blo 542804 1106689 := bstep (se 2 (by rfl) ⟨415008, by rfl⟩ : syracuseStep 1106689 = 830017) B830017
theorem B943193 : Blo 542804 943193 := bstep (se 2 (by rfl) ⟨353697, by rfl⟩ : syracuseStep 943193 = 707395) B707395
theorem B8381875 : Blo 542804 8381875 := bstep (se 1 (by rfl) ⟨6286406, by rfl⟩ : syracuseStep 8381875 = 12572813) B12572813
theorem B1795649 : Blo 542804 1795649 := bstep (se 2 (by rfl) ⟨673368, by rfl⟩ : syracuseStep 1795649 = 1346737) B1346737
theorem B1861271 : Blo 542804 1861271 := bstep (se 1 (by rfl) ⟨1395953, by rfl⟩ : syracuseStep 1861271 = 2791907) B2791907
theorem B2483885 : Blo 542804 2483885 := bstep (se 3 (by rfl) ⟨465728, by rfl⟩ : syracuseStep 2483885 = 931457) B931457
theorem B583895 : Blo 542804 583895 := bstep (se 1 (by rfl) ⟨437921, by rfl⟩ : syracuseStep 583895 = 875843) B875843
theorem B2321075 : Blo 542804 2321075 := bstep (se 1 (by rfl) ⟨1740806, by rfl⟩ : syracuseStep 2321075 = 3481613) B3481613
theorem B1469249 : Blo 542804 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B2321227 : Blo 542804 2321227 := bstep (se 1 (by rfl) ⟨1740920, by rfl⟩ : syracuseStep 2321227 = 3481841) B3481841
theorem B2321297 : Blo 542804 2321297 := bstep (se 2 (by rfl) ⟨870486, by rfl⟩ : syracuseStep 2321297 = 1740973) B1740973
theorem B1993675 : Blo 542804 1993675 := bstep (se 1 (by rfl) ⟨1495256, by rfl⟩ : syracuseStep 1993675 = 2990513) B2990513
theorem B814283 : Blo 542804 814283 := bstep (se 1 (by rfl) ⟨610712, by rfl⟩ : syracuseStep 814283 = 1221425) B1221425
theorem B814295 : Blo 542804 814295 := bstep (se 1 (by rfl) ⟨610721, by rfl⟩ : syracuseStep 814295 = 1221443) B1221443
theorem B7433477 : Blo 542804 7433477 := bstep (se 4 (by rfl) ⟨696888, by rfl⟩ : syracuseStep 7433477 = 1393777) B1393777
theorem B814361 : Blo 542804 814361 := bstep (se 2 (by rfl) ⟨305385, by rfl⟩ : syracuseStep 814361 = 610771) B610771
theorem B9334115 : Blo 542804 9334115 := bstep (se 1 (by rfl) ⟨7000586, by rfl⟩ : syracuseStep 9334115 = 14001173) B14001173
theorem B814475 : Blo 542804 814475 := bstep (se 1 (by rfl) ⟨610856, by rfl⟩ : syracuseStep 814475 = 1221713) B1221713
theorem B814487 : Blo 542804 814487 := bstep (se 1 (by rfl) ⟨610865, by rfl⟩ : syracuseStep 814487 = 1221731) B1221731
theorem B814553 : Blo 542804 814553 := bstep (se 2 (by rfl) ⟨305457, by rfl⟩ : syracuseStep 814553 = 610915) B610915
theorem B978419 : Blo 542804 978419 := bstep (se 1 (by rfl) ⟨733814, by rfl⟩ : syracuseStep 978419 = 1467629) B1467629
theorem B978455 : Blo 542804 978455 := bstep (se 1 (by rfl) ⟨733841, by rfl⟩ : syracuseStep 978455 = 1467683) B1467683
theorem B4124195 : Blo 542804 4124195 := bstep (se 1 (by rfl) ⟨3093146, by rfl⟩ : syracuseStep 4124195 = 6186293) B6186293
theorem B814667 : Blo 542804 814667 := bstep (se 1 (by rfl) ⟨611000, by rfl⟩ : syracuseStep 814667 = 1222001) B1222001
theorem B814679 : Blo 542804 814679 := bstep (se 1 (by rfl) ⟨611009, by rfl⟩ : syracuseStep 814679 = 1222019) B1222019
theorem B2092637 : Blo 542804 2092637 := bstep (se 3 (by rfl) ⟨392369, by rfl⟩ : syracuseStep 2092637 = 784739) B784739
theorem B814745 : Blo 542804 814745 := bstep (se 2 (by rfl) ⟨305529, by rfl⟩ : syracuseStep 814745 = 611059) B611059
theorem B1961651 : Blo 542804 1961651 := bstep (se 1 (by rfl) ⟨1471238, by rfl⟩ : syracuseStep 1961651 = 2942477) B2942477
theorem B814859 : Blo 542804 814859 := bstep (se 1 (by rfl) ⟨611144, by rfl⟩ : syracuseStep 814859 = 1222289) B1222289
theorem B814871 : Blo 542804 814871 := bstep (se 1 (by rfl) ⟨611153, by rfl⟩ : syracuseStep 814871 = 1222307) B1222307
theorem B2092823 : Blo 542804 2092823 := bstep (se 1 (by rfl) ⟨1569617, by rfl⟩ : syracuseStep 2092823 = 3139235) B3139235
theorem B814937 : Blo 542804 814937 := bstep (se 2 (by rfl) ⟨305601, by rfl⟩ : syracuseStep 814937 = 611203) B611203
theorem B1077121 : Blo 542804 1077121 := bstep (se 2 (by rfl) ⟨403920, by rfl⟩ : syracuseStep 1077121 = 807841) B807841
theorem B815051 : Blo 542804 815051 := bstep (se 1 (by rfl) ⟨611288, by rfl⟩ : syracuseStep 815051 = 1222577) B1222577
theorem B815063 : Blo 542804 815063 := bstep (se 1 (by rfl) ⟨611297, by rfl⟩ : syracuseStep 815063 = 1222595) B1222595
theorem B815129 : Blo 542804 815129 := bstep (se 2 (by rfl) ⟨305673, by rfl⟩ : syracuseStep 815129 = 611347) B611347
theorem B2748491 : Blo 542804 2748491 := bstep (se 1 (by rfl) ⟨2061368, by rfl⟩ : syracuseStep 2748491 = 4122737) B4122737
theorem B815243 : Blo 542804 815243 := bstep (se 1 (by rfl) ⟨611432, by rfl⟩ : syracuseStep 815243 = 1222865) B1222865
theorem B815255 : Blo 542804 815255 := bstep (se 1 (by rfl) ⟨611441, by rfl⟩ : syracuseStep 815255 = 1222883) B1222883
theorem B815321 : Blo 542804 815321 := bstep (se 2 (by rfl) ⟨305745, by rfl⟩ : syracuseStep 815321 = 611491) B611491
theorem B979211 : Blo 542804 979211 := bstep (se 1 (by rfl) ⟨734408, by rfl⟩ : syracuseStep 979211 = 1468817) B1468817
theorem B815435 : Blo 542804 815435 := bstep (se 1 (by rfl) ⟨611576, by rfl⟩ : syracuseStep 815435 = 1223153) B1223153
theorem B815447 : Blo 542804 815447 := bstep (se 1 (by rfl) ⟨611585, by rfl⟩ : syracuseStep 815447 = 1223171) B1223171
theorem B815513 : Blo 542804 815513 := bstep (se 2 (by rfl) ⟨305817, by rfl⟩ : syracuseStep 815513 = 611635) B611635
theorem B815627 : Blo 542804 815627 := bstep (se 1 (by rfl) ⟨611720, by rfl⟩ : syracuseStep 815627 = 1223441) B1223441
theorem B815639 : Blo 542804 815639 := bstep (se 1 (by rfl) ⟨611729, by rfl⟩ : syracuseStep 815639 = 1223459) B1223459
theorem B2322989 : Blo 542804 2322989 := bstep (se 3 (by rfl) ⟨435560, by rfl⟩ : syracuseStep 2322989 = 871121) B871121
theorem B815705 : Blo 542804 815705 := bstep (se 2 (by rfl) ⟨305889, by rfl⟩ : syracuseStep 815705 = 611779) B611779
theorem B979571 : Blo 542804 979571 := bstep (se 1 (by rfl) ⟨734678, by rfl⟩ : syracuseStep 979571 = 1469357) B1469357
theorem B815819 : Blo 542804 815819 := bstep (se 1 (by rfl) ⟨611864, by rfl⟩ : syracuseStep 815819 = 1223729) B1223729
theorem B815831 : Blo 542804 815831 := bstep (se 1 (by rfl) ⟨611873, by rfl⟩ : syracuseStep 815831 = 1223747) B1223747
theorem B815897 : Blo 542804 815897 := bstep (se 2 (by rfl) ⟨305961, by rfl⟩ : syracuseStep 815897 = 611923) B611923
theorem B816011 : Blo 542804 816011 := bstep (se 1 (by rfl) ⟨612008, by rfl⟩ : syracuseStep 816011 = 1224017) B1224017
theorem B816023 : Blo 542804 816023 := bstep (se 1 (by rfl) ⟨612017, by rfl⟩ : syracuseStep 816023 = 1224035) B1224035
theorem B816089 : Blo 542804 816089 := bstep (se 2 (by rfl) ⟨306033, by rfl⟩ : syracuseStep 816089 = 612067) B612067
theorem B816203 : Blo 542804 816203 := bstep (se 1 (by rfl) ⟨612152, by rfl⟩ : syracuseStep 816203 = 1224305) B1224305
theorem B816215 : Blo 542804 816215 := bstep (se 1 (by rfl) ⟨612161, by rfl⟩ : syracuseStep 816215 = 1224323) B1224323
theorem B816281 : Blo 542804 816281 := bstep (se 2 (by rfl) ⟨306105, by rfl⟩ : syracuseStep 816281 = 612211) B612211
theorem B2323673 : Blo 542804 2323673 := bstep (se 2 (by rfl) ⟨871377, by rfl⟩ : syracuseStep 2323673 = 1742755) B1742755
theorem B816395 : Blo 542804 816395 := bstep (se 1 (by rfl) ⟨612296, by rfl⟩ : syracuseStep 816395 = 1224593) B1224593
theorem B816407 : Blo 542804 816407 := bstep (se 1 (by rfl) ⟨612305, by rfl⟩ : syracuseStep 816407 = 1224611) B1224611
theorem B1045811 : Blo 542804 1045811 := bstep (se 1 (by rfl) ⟨784358, by rfl⟩ : syracuseStep 1045811 = 1568717) B1568717
theorem B816473 : Blo 542804 816473 := bstep (se 2 (by rfl) ⟨306177, by rfl⟩ : syracuseStep 816473 = 612355) B612355
theorem B2061719 : Blo 542804 2061719 := bstep (se 1 (by rfl) ⟨1546289, by rfl⟩ : syracuseStep 2061719 = 3092579) B3092579
theorem B2946455 : Blo 542804 2946455 := bstep (se 1 (by rfl) ⟨2209841, by rfl⟩ : syracuseStep 2946455 = 4419683) B4419683
theorem B816587 : Blo 542804 816587 := bstep (se 1 (by rfl) ⟨612440, by rfl⟩ : syracuseStep 816587 = 1224881) B1224881
theorem B816599 : Blo 542804 816599 := bstep (se 1 (by rfl) ⟨612449, by rfl⟩ : syracuseStep 816599 = 1224899) B1224899
theorem B816665 : Blo 542804 816665 := bstep (se 2 (by rfl) ⟨306249, by rfl⟩ : syracuseStep 816665 = 612499) B612499
theorem B6190667 : Blo 542804 6190667 := bstep (se 1 (by rfl) ⟨4643000, by rfl⟩ : syracuseStep 6190667 = 9286001) B9286001
theorem B816779 : Blo 542804 816779 := bstep (se 1 (by rfl) ⟨612584, by rfl⟩ : syracuseStep 816779 = 1225169) B1225169
theorem B816791 : Blo 542804 816791 := bstep (se 1 (by rfl) ⟨612593, by rfl⟩ : syracuseStep 816791 = 1225187) B1225187
theorem B1832651 : Blo 542804 1832651 := bstep (se 1 (by rfl) ⟨1374488, by rfl⟩ : syracuseStep 1832651 = 2748977) B2748977
theorem B816857 : Blo 542804 816857 := bstep (se 2 (by rfl) ⟨306321, by rfl⟩ : syracuseStep 816857 = 612643) B612643
theorem B2750273 : Blo 542804 2750273 := bstep (se 2 (by rfl) ⟨1031352, by rfl⟩ : syracuseStep 2750273 = 2062705) B2062705
theorem B816971 : Blo 542804 816971 := bstep (se 1 (by rfl) ⟨612728, by rfl⟩ : syracuseStep 816971 = 1225457) B1225457
theorem B816983 : Blo 542804 816983 := bstep (se 1 (by rfl) ⟨612737, by rfl⟩ : syracuseStep 816983 = 1225475) B1225475
theorem B817049 : Blo 542804 817049 := bstep (se 2 (by rfl) ⟨306393, by rfl⟩ : syracuseStep 817049 = 612787) B612787
theorem B4650929 : Blo 542804 4650929 := bstep (se 2 (by rfl) ⟨1744098, by rfl⟩ : syracuseStep 4650929 = 3488197) B3488197
theorem B1374155 : Blo 542804 1374155 := bstep (se 1 (by rfl) ⟨1030616, by rfl⟩ : syracuseStep 1374155 = 2061233) B2061233
theorem B1832921 : Blo 542804 1832921 := bstep (se 2 (by rfl) ⟨687345, by rfl⟩ : syracuseStep 1832921 = 1374691) B1374691
theorem B817163 : Blo 542804 817163 := bstep (se 1 (by rfl) ⟨612872, by rfl⟩ : syracuseStep 817163 = 1225745) B1225745
theorem B817175 : Blo 542804 817175 := bstep (se 1 (by rfl) ⟨612881, by rfl⟩ : syracuseStep 817175 = 1225763) B1225763
theorem B817241 : Blo 542804 817241 := bstep (se 2 (by rfl) ⟨306465, by rfl⟩ : syracuseStep 817241 = 612931) B612931
theorem B817355 : Blo 542804 817355 := bstep (se 1 (by rfl) ⟨613016, by rfl⟩ : syracuseStep 817355 = 1226033) B1226033
theorem B817367 : Blo 542804 817367 := bstep (se 1 (by rfl) ⟨613025, by rfl⟩ : syracuseStep 817367 = 1226051) B1226051
theorem B1866007 : Blo 542804 1866007 := bstep (se 1 (by rfl) ⟨1399505, by rfl⟩ : syracuseStep 1866007 = 2799011) B2799011
theorem B817433 : Blo 542804 817433 := bstep (se 2 (by rfl) ⟨306537, by rfl⟩ : syracuseStep 817433 = 613075) B613075
theorem B11794733 : Blo 542804 11794733 := bstep (se 3 (by rfl) ⟨2211512, by rfl⟩ : syracuseStep 11794733 = 4423025) B4423025
theorem B1374529 : Blo 542804 1374529 := bstep (se 2 (by rfl) ⟨515448, by rfl⟩ : syracuseStep 1374529 = 1030897) B1030897
theorem B817547 : Blo 542804 817547 := bstep (se 1 (by rfl) ⟨613160, by rfl⟩ : syracuseStep 817547 = 1226321) B1226321
theorem B1046935 : Blo 542804 1046935 := bstep (se 1 (by rfl) ⟨785201, by rfl⟩ : syracuseStep 1046935 = 1570403) B1570403
theorem B817559 : Blo 542804 817559 := bstep (se 1 (by rfl) ⟨613169, by rfl⟩ : syracuseStep 817559 = 1226339) B1226339
theorem B817625 : Blo 542804 817625 := bstep (se 2 (by rfl) ⟨306609, by rfl⟩ : syracuseStep 817625 = 613219) B613219
theorem B817739 : Blo 542804 817739 := bstep (se 1 (by rfl) ⟨613304, by rfl⟩ : syracuseStep 817739 = 1226609) B1226609
theorem B817751 : Blo 542804 817751 := bstep (se 1 (by rfl) ⟨613313, by rfl⟩ : syracuseStep 817751 = 1226627) B1226627
theorem B4651613 : Blo 542804 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B2062979 : Blo 542804 2062979 := bstep (se 1 (by rfl) ⟨1547234, by rfl⟩ : syracuseStep 2062979 = 3094469) B3094469
theorem B1833623 : Blo 542804 1833623 := bstep (se 1 (by rfl) ⟨1375217, by rfl⟩ : syracuseStep 1833623 = 2750435) B2750435
theorem B817817 : Blo 542804 817817 := bstep (se 2 (by rfl) ⟨306681, by rfl⟩ : syracuseStep 817817 = 613363) B613363
theorem B1178315 : Blo 542804 1178315 := bstep (se 1 (by rfl) ⟨883736, by rfl⟩ : syracuseStep 1178315 = 1767473) B1767473
theorem B817931 : Blo 542804 817931 := bstep (se 1 (by rfl) ⟨613448, by rfl⟩ : syracuseStep 817931 = 1226897) B1226897
theorem B817943 : Blo 542804 817943 := bstep (se 1 (by rfl) ⟨613457, by rfl⟩ : syracuseStep 817943 = 1226915) B1226915
theorem B818009 : Blo 542804 818009 := bstep (se 2 (by rfl) ⟨306753, by rfl⟩ : syracuseStep 818009 = 613507) B613507
theorem B1375127 : Blo 542804 1375127 := bstep (se 1 (by rfl) ⟨1031345, by rfl⟩ : syracuseStep 1375127 = 2062691) B2062691
theorem B916427 : Blo 542804 916427 := bstep (se 1 (by rfl) ⟨687320, by rfl⟩ : syracuseStep 916427 = 1374641) B1374641
theorem B818123 : Blo 542804 818123 := bstep (se 1 (by rfl) ⟨613592, by rfl⟩ : syracuseStep 818123 = 1227185) B1227185
theorem B818135 : Blo 542804 818135 := bstep (se 1 (by rfl) ⟨613601, by rfl⟩ : syracuseStep 818135 = 1227203) B1227203
theorem B818201 : Blo 542804 818201 := bstep (se 2 (by rfl) ⟨306825, by rfl⟩ : syracuseStep 818201 = 613651) B613651
theorem B916555 : Blo 542804 916555 := bstep (se 1 (by rfl) ⟨687416, by rfl⟩ : syracuseStep 916555 = 1374833) B1374833
theorem B818315 : Blo 542804 818315 := bstep (se 1 (by rfl) ⟨613736, by rfl⟩ : syracuseStep 818315 = 1227473) B1227473
theorem B818327 : Blo 542804 818327 := bstep (se 1 (by rfl) ⟨613745, by rfl⟩ : syracuseStep 818327 = 1227491) B1227491
theorem B1834163 : Blo 542804 1834163 := bstep (se 1 (by rfl) ⟨1375622, by rfl⟩ : syracuseStep 1834163 = 2751245) B2751245
theorem B916697 : Blo 542804 916697 := bstep (se 2 (by rfl) ⟨343761, by rfl⟩ : syracuseStep 916697 = 687523) B687523
theorem B818393 : Blo 542804 818393 := bstep (se 2 (by rfl) ⟨306897, by rfl⟩ : syracuseStep 818393 = 613795) B613795
theorem B1178867 : Blo 542804 1178867 := bstep (se 1 (by rfl) ⟨884150, by rfl⟩ : syracuseStep 1178867 = 1768301) B1768301
theorem B1965329 : Blo 542804 1965329 := bstep (se 2 (by rfl) ⟨736998, by rfl⟩ : syracuseStep 1965329 = 1473997) B1473997
theorem B1244441 : Blo 542804 1244441 := bstep (se 2 (by rfl) ⟨466665, by rfl⟩ : syracuseStep 1244441 = 933331) B933331
theorem B818507 : Blo 542804 818507 := bstep (se 1 (by rfl) ⟨613880, by rfl⟩ : syracuseStep 818507 = 1227761) B1227761
theorem B818519 : Blo 542804 818519 := bstep (se 1 (by rfl) ⟨613889, by rfl⟩ : syracuseStep 818519 = 1227779) B1227779
theorem B916825 : Blo 542804 916825 := bstep (se 2 (by rfl) ⟨343809, by rfl⟩ : syracuseStep 916825 = 687619) B687619
theorem B818585 : Blo 542804 818585 := bstep (se 2 (by rfl) ⟨306969, by rfl⟩ : syracuseStep 818585 = 613939) B613939
theorem B1834433 : Blo 542804 1834433 := bstep (se 2 (by rfl) ⟨687912, by rfl⟩ : syracuseStep 1834433 = 1375825) B1375825
theorem B818699 : Blo 542804 818699 := bstep (se 1 (by rfl) ⟨614024, by rfl⟩ : syracuseStep 818699 = 1228049) B1228049
theorem B3112465 : Blo 542804 3112465 := bstep (se 2 (by rfl) ⟨1167174, by rfl⟩ : syracuseStep 3112465 = 2334349) B2334349
theorem B818711 : Blo 542804 818711 := bstep (se 1 (by rfl) ⟨614033, by rfl⟩ : syracuseStep 818711 = 1228067) B1228067
theorem B818777 : Blo 542804 818777 := bstep (se 2 (by rfl) ⟨307041, by rfl⟩ : syracuseStep 818777 = 614083) B614083
theorem B1375937 : Blo 542804 1375937 := bstep (se 2 (by rfl) ⟨515976, by rfl⟩ : syracuseStep 1375937 = 1031953) B1031953
theorem B818891 : Blo 542804 818891 := bstep (se 1 (by rfl) ⟨614168, by rfl⟩ : syracuseStep 818891 = 1228337) B1228337
theorem B818903 : Blo 542804 818903 := bstep (se 1 (by rfl) ⟨614177, by rfl⟩ : syracuseStep 818903 = 1228355) B1228355
theorem B2752217 : Blo 542804 2752217 := bstep (se 2 (by rfl) ⟨1032081, by rfl⟩ : syracuseStep 2752217 = 2064163) B2064163
theorem B1474265 : Blo 542804 1474265 := bstep (se 2 (by rfl) ⟨552849, by rfl⟩ : syracuseStep 1474265 = 1105699) B1105699
theorem B818969 : Blo 542804 818969 := bstep (se 2 (by rfl) ⟨307113, by rfl⟩ : syracuseStep 818969 = 614227) B614227
theorem B7470913 : Blo 542804 7470913 := bstep (se 2 (by rfl) ⟨2801592, by rfl⟩ : syracuseStep 7470913 = 5603185) B5603185
theorem B1965917 : Blo 542804 1965917 := bstep (se 3 (by rfl) ⟨368609, by rfl⟩ : syracuseStep 1965917 = 737219) B737219
theorem B819083 : Blo 542804 819083 := bstep (se 1 (by rfl) ⟨614312, by rfl⟩ : syracuseStep 819083 = 1228625) B1228625
theorem B917399 : Blo 542804 917399 := bstep (se 1 (by rfl) ⟨688049, by rfl⟩ : syracuseStep 917399 = 1376099) B1376099
theorem B1245079 : Blo 542804 1245079 := bstep (se 1 (by rfl) ⟨933809, by rfl⟩ : syracuseStep 1245079 = 1867619) B1867619
theorem B819095 : Blo 542804 819095 := bstep (se 1 (by rfl) ⟨614321, by rfl⟩ : syracuseStep 819095 = 1228643) B1228643
theorem B1474483 : Blo 542804 1474483 := bstep (se 1 (by rfl) ⟨1105862, by rfl⟩ : syracuseStep 1474483 = 2211725) B2211725
theorem B819161 : Blo 542804 819161 := bstep (se 2 (by rfl) ⟨307185, by rfl⟩ : syracuseStep 819161 = 614371) B614371
theorem B1834973 : Blo 542804 1834973 := bstep (se 3 (by rfl) ⟨344057, by rfl⟩ : syracuseStep 1834973 = 688115) B688115
theorem B819215 : Blo 542804 819215 := bstep (se 1 (by rfl) ⟨614411, by rfl⟩ : syracuseStep 819215 = 1228823) B1228823
theorem B2752541 : Blo 542804 2752541 := bstep (se 3 (by rfl) ⟨516101, by rfl⟩ : syracuseStep 2752541 = 1032203) B1032203
theorem B688171 : Blo 542804 688171 := bstep (se 1 (by rfl) ⟨516128, by rfl⟩ : syracuseStep 688171 = 1032257) B1032257
theorem B819257 : Blo 542804 819257 := bstep (se 2 (by rfl) ⟨307221, by rfl⟩ : syracuseStep 819257 = 614443) B614443
theorem B819335 : Blo 542804 819335 := bstep (se 1 (by rfl) ⟨614501, by rfl⟩ : syracuseStep 819335 = 1229003) B1229003
theorem B819371 : Blo 542804 819371 := bstep (se 1 (by rfl) ⟨614528, by rfl⟩ : syracuseStep 819371 = 1229057) B1229057
theorem B917689 : Blo 542804 917689 := bstep (se 2 (by rfl) ⟨344133, by rfl⟩ : syracuseStep 917689 = 688267) B688267
theorem B819401 : Blo 542804 819401 := bstep (se 2 (by rfl) ⟨307275, by rfl⟩ : syracuseStep 819401 = 614551) B614551
theorem B7864589 : Blo 542804 7864589 := bstep (se 3 (by rfl) ⟨1474610, by rfl⟩ : syracuseStep 7864589 = 2949221) B2949221
theorem B1835297 : Blo 542804 1835297 := bstep (se 2 (by rfl) ⟨688236, by rfl⟩ : syracuseStep 1835297 = 1376473) B1376473
theorem B819515 : Blo 542804 819515 := bstep (se 1 (by rfl) ⟨614636, by rfl⟩ : syracuseStep 819515 = 1229273) B1229273
theorem B819575 : Blo 542804 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B819599 : Blo 542804 819599 := bstep (se 1 (by rfl) ⟨614699, by rfl⟩ : syracuseStep 819599 = 1229399) B1229399
theorem B819641 : Blo 542804 819641 := bstep (se 2 (by rfl) ⟨307365, by rfl⟩ : syracuseStep 819641 = 614731) B614731
theorem B2753027 : Blo 542804 2753027 := bstep (se 1 (by rfl) ⟨2064770, by rfl⟩ : syracuseStep 2753027 = 4129541) B4129541
theorem B819719 : Blo 542804 819719 := bstep (se 1 (by rfl) ⟨614789, by rfl⟩ : syracuseStep 819719 = 1229579) B1229579
theorem B3310091 : Blo 542804 3310091 := bstep (se 1 (by rfl) ⟨2482568, by rfl⟩ : syracuseStep 3310091 = 4965137) B4965137
theorem B2425373 : Blo 542804 2425373 := bstep (se 3 (by rfl) ⟨454757, by rfl⟩ : syracuseStep 2425373 = 909515) B909515
theorem B819755 : Blo 542804 819755 := bstep (se 1 (by rfl) ⟨614816, by rfl⟩ : syracuseStep 819755 = 1229633) B1229633
theorem B819785 : Blo 542804 819785 := bstep (se 2 (by rfl) ⟨307419, by rfl⟩ : syracuseStep 819785 = 614839) B614839
theorem B754363 : Blo 542804 754363 := bstep (se 1 (by rfl) ⟨565772, by rfl⟩ : syracuseStep 754363 = 1131545) B1131545
theorem B819899 : Blo 542804 819899 := bstep (se 1 (by rfl) ⟨614924, by rfl⟩ : syracuseStep 819899 = 1229849) B1229849
theorem B2622145 : Blo 542804 2622145 := bstep (se 2 (by rfl) ⟨983304, by rfl⟩ : syracuseStep 2622145 = 1966609) B1966609
theorem B819959 : Blo 542804 819959 := bstep (se 1 (by rfl) ⟨614969, by rfl⟩ : syracuseStep 819959 = 1229939) B1229939
theorem B819983 : Blo 542804 819983 := bstep (se 1 (by rfl) ⟨614987, by rfl⟩ : syracuseStep 819983 = 1229975) B1229975
theorem B820025 : Blo 542804 820025 := bstep (se 2 (by rfl) ⟨307509, by rfl⟩ : syracuseStep 820025 = 615019) B615019
theorem B1835891 : Blo 542804 1835891 := bstep (se 1 (by rfl) ⟨1376918, by rfl⟩ : syracuseStep 1835891 = 2753837) B2753837
theorem B918391 : Blo 542804 918391 := bstep (se 1 (by rfl) ⟨688793, by rfl⟩ : syracuseStep 918391 = 1377587) B1377587
theorem B820103 : Blo 542804 820103 := bstep (se 1 (by rfl) ⟨615077, by rfl⟩ : syracuseStep 820103 = 1230155) B1230155
theorem B820139 : Blo 542804 820139 := bstep (se 1 (by rfl) ⟨615104, by rfl⟩ : syracuseStep 820139 = 1230209) B1230209
theorem B820169 : Blo 542804 820169 := bstep (se 2 (by rfl) ⟨307563, by rfl⟩ : syracuseStep 820169 = 615127) B615127
theorem B689143 : Blo 542804 689143 := bstep (se 1 (by rfl) ⟨516857, by rfl⟩ : syracuseStep 689143 = 1033715) B1033715
theorem B1475585 : Blo 542804 1475585 := bstep (se 2 (by rfl) ⟨553344, by rfl⟩ : syracuseStep 1475585 = 1106689) B1106689
theorem B918587 : Blo 542804 918587 := bstep (se 1 (by rfl) ⟨688940, by rfl⟩ : syracuseStep 918587 = 1377881) B1377881
theorem B1377395 : Blo 542804 1377395 := bstep (se 1 (by rfl) ⟨1033046, by rfl⟩ : syracuseStep 1377395 = 2066093) B2066093
theorem B6227117 : Blo 542804 6227117 := bstep (se 3 (by rfl) ⟨1167584, by rfl⟩ : syracuseStep 6227117 = 2335169) B2335169
theorem B3015937 : Blo 542804 3015937 := bstep (se 2 (by rfl) ⟨1130976, by rfl⟩ : syracuseStep 3015937 = 2261953) B2261953
theorem B689467 : Blo 542804 689467 := bstep (se 1 (by rfl) ⟨517100, by rfl⟩ : syracuseStep 689467 = 1034201) B1034201
theorem B6292829 : Blo 542804 6292829 := bstep (se 3 (by rfl) ⟨1179905, by rfl⟩ : syracuseStep 6292829 = 2359811) B2359811
theorem B13206883 : Blo 542804 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B918985 : Blo 542804 918985 := bstep (se 2 (by rfl) ⟨344619, by rfl⟩ : syracuseStep 918985 = 689239) B689239
theorem B1377911 : Blo 542804 1377911 := bstep (se 1 (by rfl) ⟨1033433, by rfl⟩ : syracuseStep 1377911 = 2066867) B2066867
theorem B788087 : Blo 542804 788087 := bstep (se 1 (by rfl) ⟨591065, by rfl⟩ : syracuseStep 788087 = 1182131) B1182131
theorem B886457 : Blo 542804 886457 := bstep (se 2 (by rfl) ⟨332421, by rfl⟩ : syracuseStep 886457 = 664843) B664843
theorem B2328335 : Blo 542804 2328335 := bstep (se 1 (by rfl) ⟨1746251, by rfl⟩ : syracuseStep 2328335 = 3492503) B3492503
theorem B35915633 : Blo 542804 35915633 := bstep (se 2 (by rfl) ⟨13468362, by rfl⟩ : syracuseStep 35915633 = 26936725) B26936725
theorem B11175833 : Blo 542804 11175833 := bstep (se 2 (by rfl) ⟨4190937, by rfl⟩ : syracuseStep 11175833 = 8381875) B8381875
theorem B2754647 : Blo 542804 2754647 := bstep (se 1 (by rfl) ⟨2065985, by rfl⟩ : syracuseStep 2754647 = 4131971) B4131971
theorem B919687 : Blo 542804 919687 := bstep (se 1 (by rfl) ⟨689765, by rfl⟩ : syracuseStep 919687 = 1379531) B1379531
theorem B985223 : Blo 542804 985223 := bstep (se 1 (by rfl) ⟨738917, by rfl⟩ : syracuseStep 985223 = 1477835) B1477835
theorem B690439 : Blo 542804 690439 := bstep (se 1 (by rfl) ⟨517829, by rfl⟩ : syracuseStep 690439 = 1035659) B1035659
theorem B1313111 : Blo 542804 1313111 := bstep (se 1 (by rfl) ⟨984833, by rfl⟩ : syracuseStep 1313111 = 1969667) B1969667
theorem B2066897 : Blo 542804 2066897 := bstep (se 2 (by rfl) ⟨775086, by rfl⟩ : syracuseStep 2066897 = 1550173) B1550173
theorem B2984471 : Blo 542804 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B2755133 : Blo 542804 2755133 := bstep (se 3 (by rfl) ⟨516587, by rfl⟩ : syracuseStep 2755133 = 1033175) B1033175
theorem B3181123 : Blo 542804 3181123 := bstep (se 1 (by rfl) ⟨2385842, by rfl⟩ : syracuseStep 3181123 = 4771685) B4771685
theorem B1378903 : Blo 542804 1378903 := bstep (se 1 (by rfl) ⟨1034177, by rfl⟩ : syracuseStep 1378903 = 2068355) B2068355
theorem B690859 : Blo 542804 690859 := bstep (se 1 (by rfl) ⟨518144, by rfl⟩ : syracuseStep 690859 = 1036289) B1036289
theorem B920335 : Blo 542804 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B4655987 : Blo 542804 4655987 := bstep (se 1 (by rfl) ⟨3491990, by rfl⟩ : syracuseStep 4655987 = 6983981) B6983981
theorem B1379207 : Blo 542804 1379207 := bstep (se 1 (by rfl) ⟨1034405, by rfl⟩ : syracuseStep 1379207 = 2068811) B2068811
theorem B691087 : Blo 542804 691087 := bstep (se 1 (by rfl) ⟨518315, by rfl⟩ : syracuseStep 691087 = 1036631) B1036631
theorem B2067353 : Blo 542804 2067353 := bstep (se 2 (by rfl) ⟨775257, by rfl⟩ : syracuseStep 2067353 = 1550515) B1550515
theorem B1379339 : Blo 542804 1379339 := bstep (se 1 (by rfl) ⟨1034504, by rfl⟩ : syracuseStep 1379339 = 2069009) B2069009
theorem B1739819 : Blo 542804 1739819 := bstep (se 1 (by rfl) ⟨1304864, by rfl⟩ : syracuseStep 1739819 = 2609729) B2609729
theorem B4656365 : Blo 542804 4656365 := bstep (se 3 (by rfl) ⟨873068, by rfl⟩ : syracuseStep 4656365 = 1746137) B1746137
theorem B920875 : Blo 542804 920875 := bstep (se 1 (by rfl) ⟨690656, by rfl⟩ : syracuseStep 920875 = 1381313) B1381313
theorem B1838483 : Blo 542804 1838483 := bstep (se 1 (by rfl) ⟨1378862, by rfl⟩ : syracuseStep 1838483 = 2757725) B2757725
theorem B921017 : Blo 542804 921017 := bstep (se 2 (by rfl) ⟨345381, by rfl⟩ : syracuseStep 921017 = 690763) B690763
theorem B2788829 : Blo 542804 2788829 := bstep (se 3 (by rfl) ⟨522905, by rfl⟩ : syracuseStep 2788829 = 1045811) B1045811
theorem B1379855 : Blo 542804 1379855 := bstep (se 1 (by rfl) ⟨1034891, by rfl⟩ : syracuseStep 1379855 = 2069783) B2069783
theorem B691831 : Blo 542804 691831 := bstep (se 1 (by rfl) ⟨518873, by rfl⟩ : syracuseStep 691831 = 1037747) B1037747
theorem B1379987 : Blo 542804 1379987 := bstep (se 1 (by rfl) ⟨1034990, by rfl⟩ : syracuseStep 1379987 = 2069981) B2069981
theorem B9277253 : Blo 542804 9277253 := bstep (se 4 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 9277253 = 1739485) B1739485
theorem B2658233 : Blo 542804 2658233 := bstep (se 2 (by rfl) ⟨996837, by rfl⟩ : syracuseStep 2658233 = 1993675) B1993675
theorem B2068523 : Blo 542804 2068523 := bstep (se 1 (by rfl) ⟨1551392, by rfl⟩ : syracuseStep 2068523 = 3102785) B3102785
theorem B921719 : Blo 542804 921719 := bstep (se 1 (by rfl) ⟨691289, by rfl⟩ : syracuseStep 921719 = 1382579) B1382579
theorem B4788397 : Blo 542804 4788397 := bstep (se 3 (by rfl) ⟨897824, by rfl⟩ : syracuseStep 4788397 = 1795649) B1795649
theorem B2756915 : Blo 542804 2756915 := bstep (se 1 (by rfl) ⟨2067686, by rfl⟩ : syracuseStep 2756915 = 4135373) B4135373
theorem B1741115 : Blo 542804 1741115 := bstep (se 1 (by rfl) ⟨1305836, by rfl⟩ : syracuseStep 1741115 = 2611673) B2611673
theorem B6623693 : Blo 542804 6623693 := bstep (se 3 (by rfl) ⟨1241942, by rfl⟩ : syracuseStep 6623693 = 2483885) B2483885
theorem B922171 : Blo 542804 922171 := bstep (se 1 (by rfl) ⟨691628, by rfl⟩ : syracuseStep 922171 = 1383257) B1383257
theorem B2757239 : Blo 542804 2757239 := bstep (se 1 (by rfl) ⟨2067929, by rfl⟩ : syracuseStep 2757239 = 4135859) B4135859
theorem B922313 : Blo 542804 922313 := bstep (se 2 (by rfl) ⟨345867, by rfl⟩ : syracuseStep 922313 = 691735) B691735
theorem B1381121 : Blo 542804 1381121 := bstep (se 2 (by rfl) ⟨517920, by rfl⟩ : syracuseStep 1381121 = 1035841) B1035841
theorem B1839887 : Blo 542804 1839887 := bstep (se 1 (by rfl) ⟨1379915, by rfl⟩ : syracuseStep 1839887 = 2759831) B2759831
theorem B2626337 : Blo 542804 2626337 := bstep (se 2 (by rfl) ⟨984876, by rfl⟩ : syracuseStep 2626337 = 1969753) B1969753
theorem B10523429 : Blo 542804 10523429 := bstep (se 4 (by rfl) ⟨986571, by rfl⟩ : syracuseStep 10523429 = 1973143) B1973143
theorem B1840157 : Blo 542804 1840157 := bstep (se 3 (by rfl) ⟨345029, by rfl⟩ : syracuseStep 1840157 = 690059) B690059
theorem B1381495 : Blo 542804 1381495 := bstep (se 1 (by rfl) ⟨1036121, by rfl⟩ : syracuseStep 1381495 = 2072243) B2072243
theorem B1611037 : Blo 542804 1611037 := bstep (se 3 (by rfl) ⟨302069, by rfl⟩ : syracuseStep 1611037 = 604139) B604139
theorem B15963425 : Blo 542804 15963425 := bstep (se 2 (by rfl) ⟨5986284, by rfl⟩ : syracuseStep 15963425 = 11972569) B11972569
theorem B1545743 : Blo 542804 1545743 := bstep (se 1 (by rfl) ⟨1159307, by rfl⟩ : syracuseStep 1545743 = 2318615) B2318615
theorem B1381931 : Blo 542804 1381931 := bstep (se 1 (by rfl) ⟨1036448, by rfl⟩ : syracuseStep 1381931 = 2072897) B2072897
theorem B2758211 : Blo 542804 2758211 := bstep (se 1 (by rfl) ⟨2068658, by rfl⟩ : syracuseStep 2758211 = 4137317) B4137317
theorem B4429541 : Blo 542804 4429541 := bstep (se 4 (by rfl) ⟨415269, by rfl⟩ : syracuseStep 4429541 = 830539) B830539
theorem B11802419 : Blo 542804 11802419 := bstep (se 1 (by rfl) ⟨8851814, by rfl⟩ : syracuseStep 11802419 = 17703629) B17703629
theorem B2758535 : Blo 542804 2758535 := bstep (se 1 (by rfl) ⟨2068901, by rfl⟩ : syracuseStep 2758535 = 4137803) B4137803
theorem B2987929 : Blo 542804 2987929 := bstep (se 2 (by rfl) ⟨1120473, by rfl⟩ : syracuseStep 2987929 = 2240947) B2240947
theorem B2070481 : Blo 542804 2070481 := bstep (se 2 (by rfl) ⟨776430, by rfl⟩ : syracuseStep 2070481 = 1552861) B1552861
theorem B2070785 : Blo 542804 2070785 := bstep (se 2 (by rfl) ⟨776544, by rfl⟩ : syracuseStep 2070785 = 1553089) B1553089
theorem B1382771 : Blo 542804 1382771 := bstep (se 1 (by rfl) ⟨1037078, by rfl⟩ : syracuseStep 1382771 = 2074157) B2074157
theorem B1382791 : Blo 542804 1382791 := bstep (se 1 (by rfl) ⟨1037093, by rfl⟩ : syracuseStep 1382791 = 2074187) B2074187
theorem B1841561 : Blo 542804 1841561 := bstep (se 2 (by rfl) ⟨690585, by rfl⟩ : syracuseStep 1841561 = 1381171) B1381171
theorem B4659677 : Blo 542804 4659677 := bstep (se 3 (by rfl) ⟨873689, by rfl⟩ : syracuseStep 4659677 = 1747379) B1747379
theorem B2202173 : Blo 542804 2202173 := bstep (se 3 (by rfl) ⟨412907, by rfl⟩ : syracuseStep 2202173 = 825815) B825815
theorem B1383065 : Blo 542804 1383065 := bstep (se 2 (by rfl) ⟨518649, by rfl⟩ : syracuseStep 1383065 = 1037299) B1037299
theorem B2071241 : Blo 542804 2071241 := bstep (se 2 (by rfl) ⟨776715, by rfl⟩ : syracuseStep 2071241 = 1553431) B1553431
theorem B1383227 : Blo 542804 1383227 := bstep (se 1 (by rfl) ⟨1037420, by rfl⟩ : syracuseStep 1383227 = 2074841) B2074841
theorem B1383439 : Blo 542804 1383439 := bstep (se 1 (by rfl) ⟨1037579, by rfl⟩ : syracuseStep 1383439 = 2075159) B2075159
theorem B1842263 : Blo 542804 1842263 := bstep (se 1 (by rfl) ⟨1381697, by rfl⟩ : syracuseStep 1842263 = 2763395) B2763395
theorem B1547383 : Blo 542804 1547383 := bstep (se 1 (by rfl) ⟨1160537, by rfl⟩ : syracuseStep 1547383 = 2321075) B2321075
theorem B1547417 : Blo 542804 1547417 := bstep (se 2 (by rfl) ⟨580281, by rfl⟩ : syracuseStep 1547417 = 1160563) B1160563
theorem B1547531 : Blo 542804 1547531 := bstep (se 1 (by rfl) ⟨1160648, by rfl⟩ : syracuseStep 1547531 = 2321297) B2321297
theorem B1383713 : Blo 542804 1383713 := bstep (se 2 (by rfl) ⟨518892, by rfl⟩ : syracuseStep 1383713 = 1037785) B1037785
theorem B4955651 : Blo 542804 4955651 := bstep (se 1 (by rfl) ⟨3716738, by rfl⟩ : syracuseStep 4955651 = 7433477) B7433477
theorem B4660739 : Blo 542804 4660739 := bstep (se 1 (by rfl) ⟨3495554, by rfl⟩ : syracuseStep 4660739 = 6991109) B6991109
theorem B1842749 : Blo 542804 1842749 := bstep (se 3 (by rfl) ⟨345515, by rfl⟩ : syracuseStep 1842749 = 691031) B691031
theorem B4038437 : Blo 542804 4038437 := bstep (se 4 (by rfl) ⟨378603, by rfl⟩ : syracuseStep 4038437 = 757207) B757207
theorem B5250905 : Blo 542804 5250905 := bstep (se 2 (by rfl) ⟨1969089, by rfl⟩ : syracuseStep 5250905 = 3938179) B3938179
theorem B663595 : Blo 542804 663595 := bstep (se 1 (by rfl) ⟨497696, by rfl⟩ : syracuseStep 663595 = 995393) B995393
theorem B1548659 : Blo 542804 1548659 := bstep (se 1 (by rfl) ⟨1161494, by rfl⟩ : syracuseStep 1548659 = 2322989) B2322989
theorem B3318509 : Blo 542804 3318509 := bstep (se 3 (by rfl) ⟨622220, by rfl⟩ : syracuseStep 3318509 = 1244441) B1244441
theorem B1549057 : Blo 542804 1549057 := bstep (se 2 (by rfl) ⟨580896, by rfl⟩ : syracuseStep 1549057 = 1161793) B1161793
theorem B1549115 : Blo 542804 1549115 := bstep (se 1 (by rfl) ⟨1161836, by rfl⟩ : syracuseStep 1549115 = 2323673) B2323673
theorem B7840601 : Blo 542804 7840601 := bstep (se 2 (by rfl) ⟨2940225, by rfl⟩ : syracuseStep 7840601 = 5880451) B5880451
theorem B1844153 : Blo 542804 1844153 := bstep (se 2 (by rfl) ⟨691557, by rfl⟩ : syracuseStep 1844153 = 1383115) B1383115
theorem B1221767 : Blo 542804 1221767 := bstep (se 1 (by rfl) ⟨916325, by rfl⟩ : syracuseStep 1221767 = 1832651) B1832651
theorem B1221947 : Blo 542804 1221947 := bstep (se 1 (by rfl) ⟨916460, by rfl⟩ : syracuseStep 1221947 = 1832921) B1832921
theorem B2762099 : Blo 542804 2762099 := bstep (se 1 (by rfl) ⟨2071574, by rfl⟩ : syracuseStep 2762099 = 4143149) B4143149
theorem B1222073 : Blo 542804 1222073 := bstep (se 2 (by rfl) ⟨458277, by rfl⟩ : syracuseStep 1222073 = 916555) B916555
theorem B1844747 : Blo 542804 1844747 := bstep (se 1 (by rfl) ⟨1383560, by rfl⟩ : syracuseStep 1844747 = 2767121) B2767121
theorem B1844855 : Blo 542804 1844855 := bstep (se 1 (by rfl) ⟨1383641, by rfl⟩ : syracuseStep 1844855 = 2767283) B2767283
theorem B2074369 : Blo 542804 2074369 := bstep (se 2 (by rfl) ⟨777888, by rfl⟩ : syracuseStep 2074369 = 1555777) B1555777
theorem B1222415 : Blo 542804 1222415 := bstep (se 1 (by rfl) ⟨916811, by rfl⟩ : syracuseStep 1222415 = 1833623) B1833623
theorem B1222433 : Blo 542804 1222433 := bstep (se 2 (by rfl) ⟨458412, by rfl⟩ : syracuseStep 1222433 = 916825) B916825
theorem B3483481 : Blo 542804 3483481 := bstep (se 2 (by rfl) ⟨1306305, by rfl⟩ : syracuseStep 3483481 = 2612611) B2612611
theorem B2762585 : Blo 542804 2762585 := bstep (se 2 (by rfl) ⟨1035969, by rfl⟩ : syracuseStep 2762585 = 2071939) B2071939
theorem B1222775 : Blo 542804 1222775 := bstep (se 1 (by rfl) ⟨917081, by rfl⟩ : syracuseStep 1222775 = 1834163) B1834163
theorem B1845449 : Blo 542804 1845449 := bstep (se 2 (by rfl) ⟨692043, by rfl⟩ : syracuseStep 1845449 = 1384087) B1384087
theorem B1222955 : Blo 542804 1222955 := bstep (se 1 (by rfl) ⟨917216, by rfl⟩ : syracuseStep 1222955 = 1834433) B1834433
theorem B1223315 : Blo 542804 1223315 := bstep (se 1 (by rfl) ⟨917486, by rfl⟩ : syracuseStep 1223315 = 1834973) B1834973
theorem B1223369 : Blo 542804 1223369 := bstep (se 2 (by rfl) ⟨458763, by rfl⟩ : syracuseStep 1223369 = 917527) B917527
theorem B8825867 : Blo 542804 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B1551403 : Blo 542804 1551403 := bstep (se 1 (by rfl) ⟨1163552, by rfl⟩ : syracuseStep 1551403 = 2327105) B2327105
theorem B9972823 : Blo 542804 9972823 := bstep (se 1 (by rfl) ⟨7479617, by rfl⟩ : syracuseStep 9972823 = 14959235) B14959235
theorem B4140233 : Blo 542804 4140233 := bstep (se 2 (by rfl) ⟨1552587, by rfl⟩ : syracuseStep 4140233 = 3105175) B3105175
theorem B1551631 : Blo 542804 1551631 := bstep (se 1 (by rfl) ⟨1163723, by rfl⟩ : syracuseStep 1551631 = 2327447) B2327447
theorem B1224071 : Blo 542804 1224071 := bstep (se 1 (by rfl) ⟨918053, by rfl⟩ : syracuseStep 1224071 = 1836107) B1836107
theorem B248491405 : Blo 542804 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B1551905 : Blo 542804 1551905 := bstep (se 2 (by rfl) ⟨581964, by rfl⟩ : syracuseStep 1551905 = 1163929) B1163929
theorem B1224251 : Blo 542804 1224251 := bstep (se 1 (by rfl) ⟨918188, by rfl⟩ : syracuseStep 1224251 = 1836377) B1836377
theorem B3321431 : Blo 542804 3321431 := bstep (se 1 (by rfl) ⟨2491073, by rfl⟩ : syracuseStep 3321431 = 4982147) B4982147
theorem B1224377 : Blo 542804 1224377 := bstep (se 2 (by rfl) ⟨459141, by rfl⟩ : syracuseStep 1224377 = 918283) B918283
theorem B1552247 : Blo 542804 1552247 := bstep (se 1 (by rfl) ⟨1164185, by rfl⟩ : syracuseStep 1552247 = 2328371) B2328371
theorem B2764691 : Blo 542804 2764691 := bstep (se 1 (by rfl) ⟨2073518, by rfl⟩ : syracuseStep 2764691 = 4147037) B4147037
theorem B5451781 : Blo 542804 5451781 := bstep (se 4 (by rfl) ⟨511104, by rfl⟩ : syracuseStep 5451781 = 1022209) B1022209
theorem B1224719 : Blo 542804 1224719 := bstep (se 1 (by rfl) ⟨918539, by rfl⟩ : syracuseStep 1224719 = 1837079) B1837079
theorem B1224737 : Blo 542804 1224737 := bstep (se 2 (by rfl) ⟨459276, by rfl⟩ : syracuseStep 1224737 = 918553) B918553
theorem B1225079 : Blo 542804 1225079 := bstep (se 1 (by rfl) ⟨918809, by rfl⟩ : syracuseStep 1225079 = 1837619) B1837619
theorem B3322259 : Blo 542804 3322259 := bstep (se 1 (by rfl) ⟨2491694, by rfl⟩ : syracuseStep 3322259 = 4983389) B4983389
theorem B1552907 : Blo 542804 1552907 := bstep (se 1 (by rfl) ⟨1164680, by rfl⟩ : syracuseStep 1552907 = 2329361) B2329361
theorem B1225259 : Blo 542804 1225259 := bstep (se 1 (by rfl) ⟨918944, by rfl⟩ : syracuseStep 1225259 = 1837889) B1837889
theorem B2208545 : Blo 542804 2208545 := bstep (se 2 (by rfl) ⟨828204, by rfl⟩ : syracuseStep 2208545 = 1656409) B1656409
theorem B5583653 : Blo 542804 5583653 := bstep (se 4 (by rfl) ⟨523467, by rfl⟩ : syracuseStep 5583653 = 1046935) B1046935
theorem B1225619 : Blo 542804 1225619 := bstep (se 1 (by rfl) ⟨919214, by rfl⟩ : syracuseStep 1225619 = 1838429) B1838429
theorem B1225673 : Blo 542804 1225673 := bstep (se 2 (by rfl) ⟨459627, by rfl⟩ : syracuseStep 1225673 = 919255) B919255
theorem B5649431 : Blo 542804 5649431 := bstep (se 1 (by rfl) ⟨4237073, by rfl⟩ : syracuseStep 5649431 = 8474147) B8474147
theorem B2798621 : Blo 542804 2798621 := bstep (se 3 (by rfl) ⟨524741, by rfl⟩ : syracuseStep 2798621 = 1049483) B1049483
theorem B1750045 : Blo 542804 1750045 := bstep (se 3 (by rfl) ⟨328133, by rfl⟩ : syracuseStep 1750045 = 656267) B656267
theorem B10466435 : Blo 542804 10466435 := bstep (se 1 (by rfl) ⟨7849826, by rfl⟩ : syracuseStep 10466435 = 15699653) B15699653
theorem B1226375 : Blo 542804 1226375 := bstep (se 1 (by rfl) ⟨919781, by rfl⟩ : syracuseStep 1226375 = 1839563) B1839563
theorem B1160905 : Blo 542804 1160905 := bstep (se 2 (by rfl) ⟨435339, by rfl⟩ : syracuseStep 1160905 = 870679) B870679
theorem B1226555 : Blo 542804 1226555 := bstep (se 1 (by rfl) ⟨919916, by rfl⟩ : syracuseStep 1226555 = 1839833) B1839833
theorem B1226681 : Blo 542804 1226681 := bstep (se 2 (by rfl) ⟨460005, by rfl⟩ : syracuseStep 1226681 = 920011) B920011
theorem B12564497 : Blo 542804 12564497 := bstep (se 2 (by rfl) ⟨4711686, by rfl⟩ : syracuseStep 12564497 = 9423373) B9423373
theorem B4732951 : Blo 542804 4732951 := bstep (se 1 (by rfl) ⟨3549713, by rfl⟩ : syracuseStep 4732951 = 7099427) B7099427
theorem B1554491 : Blo 542804 1554491 := bstep (se 1 (by rfl) ⟨1165868, by rfl⟩ : syracuseStep 1554491 = 2331737) B2331737
theorem B1554547 : Blo 542804 1554547 := bstep (se 1 (by rfl) ⟨1165910, by rfl⟩ : syracuseStep 1554547 = 2331821) B2331821
theorem B1227023 : Blo 542804 1227023 := bstep (se 1 (by rfl) ⟨920267, by rfl⟩ : syracuseStep 1227023 = 1840535) B1840535
theorem B1227041 : Blo 542804 1227041 := bstep (se 2 (by rfl) ⟨460140, by rfl⟩ : syracuseStep 1227041 = 920281) B920281
theorem B3094969 : Blo 542804 3094969 := bstep (se 2 (by rfl) ⟨1160613, by rfl⟩ : syracuseStep 3094969 = 2321227) B2321227
theorem B1554889 : Blo 542804 1554889 := bstep (se 2 (by rfl) ⟨583083, by rfl⟩ : syracuseStep 1554889 = 1166167) B1166167
theorem B735787 : Blo 542804 735787 := bstep (se 1 (by rfl) ⟨551840, by rfl⟩ : syracuseStep 735787 = 1103681) B1103681
theorem B1030715 : Blo 542804 1030715 := bstep (se 1 (by rfl) ⟨773036, by rfl⟩ : syracuseStep 1030715 = 1546073) B1546073
theorem B1227383 : Blo 542804 1227383 := bstep (se 1 (by rfl) ⟨920537, by rfl⟩ : syracuseStep 1227383 = 1841075) B1841075
theorem B1227563 : Blo 542804 1227563 := bstep (se 1 (by rfl) ⟨920672, by rfl⟩ : syracuseStep 1227563 = 1841345) B1841345
theorem B2767769 : Blo 542804 2767769 := bstep (se 2 (by rfl) ⟨1037913, by rfl⟩ : syracuseStep 2767769 = 2075827) B2075827
theorem B1031201 : Blo 542804 1031201 := bstep (se 2 (by rfl) ⟨386700, by rfl⟩ : syracuseStep 1031201 = 773401) B773401
theorem B10468439 : Blo 542804 10468439 := bstep (se 1 (by rfl) ⟨7851329, by rfl⟩ : syracuseStep 10468439 = 15702659) B15702659
theorem B1227923 : Blo 542804 1227923 := bstep (se 1 (by rfl) ⟨920942, by rfl⟩ : syracuseStep 1227923 = 1841885) B1841885
theorem B1227977 : Blo 542804 1227977 := bstep (se 2 (by rfl) ⟨460491, by rfl⟩ : syracuseStep 1227977 = 920983) B920983
theorem B1031467 : Blo 542804 1031467 := bstep (se 1 (by rfl) ⟨773600, by rfl⟩ : syracuseStep 1031467 = 1547201) B1547201
theorem B736571 : Blo 542804 736571 := bstep (se 1 (by rfl) ⟨552428, by rfl⟩ : syracuseStep 736571 = 1104857) B1104857
theorem B48381533 : Blo 542804 48381533 := bstep (se 3 (by rfl) ⟨9071537, by rfl⟩ : syracuseStep 48381533 = 18143075) B18143075
theorem B1228679 : Blo 542804 1228679 := bstep (se 1 (by rfl) ⟨921509, by rfl⟩ : syracuseStep 1228679 = 1843019) B1843019
theorem B1163279 : Blo 542804 1163279 := bstep (se 1 (by rfl) ⟨872459, by rfl⟩ : syracuseStep 1163279 = 1744919) B1744919
theorem B1163297 : Blo 542804 1163297 := bstep (se 2 (by rfl) ⟨436236, by rfl⟩ : syracuseStep 1163297 = 872473) B872473
theorem B1228859 : Blo 542804 1228859 := bstep (se 1 (by rfl) ⟨921644, by rfl⟩ : syracuseStep 1228859 = 1843289) B1843289
theorem B1228985 : Blo 542804 1228985 := bstep (se 2 (by rfl) ⟨460869, by rfl⟩ : syracuseStep 1228985 = 921739) B921739
theorem B2212211 : Blo 542804 2212211 := bstep (se 1 (by rfl) ⟨1659158, by rfl⟩ : syracuseStep 2212211 = 3318317) B3318317
theorem B1163639 : Blo 542804 1163639 := bstep (se 1 (by rfl) ⟨872729, by rfl⟩ : syracuseStep 1163639 = 1745459) B1745459
theorem B1032583 : Blo 542804 1032583 := bstep (se 1 (by rfl) ⟨774437, by rfl⟩ : syracuseStep 1032583 = 1548875) B1548875
theorem B1229327 : Blo 542804 1229327 := bstep (se 1 (by rfl) ⟨921995, by rfl⟩ : syracuseStep 1229327 = 1843991) B1843991
theorem B1229345 : Blo 542804 1229345 := bstep (se 2 (by rfl) ⟨461004, by rfl⟩ : syracuseStep 1229345 = 922009) B922009
theorem B1557053 : Blo 542804 1557053 := bstep (se 3 (by rfl) ⟨291947, by rfl⟩ : syracuseStep 1557053 = 583895) B583895
theorem B1229687 : Blo 542804 1229687 := bstep (se 1 (by rfl) ⟨922265, by rfl⟩ : syracuseStep 1229687 = 1844531) B1844531
theorem B1033145 : Blo 542804 1033145 := bstep (se 2 (by rfl) ⟨387429, by rfl⟩ : syracuseStep 1033145 = 774859) B774859
theorem B1229867 : Blo 542804 1229867 := bstep (se 1 (by rfl) ⟨922400, by rfl⟩ : syracuseStep 1229867 = 1844801) B1844801
theorem B2213153 : Blo 542804 2213153 := bstep (se 2 (by rfl) ⟨829932, by rfl⟩ : syracuseStep 2213153 = 1659865) B1659865
theorem B1230227 : Blo 542804 1230227 := bstep (se 1 (by rfl) ⟨922670, by rfl⟩ : syracuseStep 1230227 = 1845341) B1845341
theorem B1230281 : Blo 542804 1230281 := bstep (se 2 (by rfl) ⟨461355, by rfl⟩ : syracuseStep 1230281 = 922711) B922711
theorem B8963909 : Blo 542804 8963909 := bstep (se 4 (by rfl) ⟨840366, by rfl⟩ : syracuseStep 8963909 = 1680733) B1680733
theorem B1034299 : Blo 542804 1034299 := bstep (se 1 (by rfl) ⟨775724, by rfl⟩ : syracuseStep 1034299 = 1551449) B1551449
theorem B542855 : Blo 542804 542855 := bstep (se 1 (by rfl) ⟨407141, by rfl⟩ : syracuseStep 542855 = 814283) B814283
theorem B542863 : Blo 542804 542863 := bstep (se 1 (by rfl) ⟨407147, by rfl⟩ : syracuseStep 542863 = 814295) B814295
theorem B542907 : Blo 542804 542907 := bstep (se 1 (by rfl) ⟨407180, by rfl⟩ : syracuseStep 542907 = 814361) B814361
theorem B1329353 : Blo 542804 1329353 := bstep (se 2 (by rfl) ⟨498507, by rfl⟩ : syracuseStep 1329353 = 997015) B997015
theorem B542983 : Blo 542804 542983 := bstep (se 1 (by rfl) ⟨407237, by rfl⟩ : syracuseStep 542983 = 814475) B814475
theorem B542991 : Blo 542804 542991 := bstep (se 1 (by rfl) ⟨407243, by rfl⟩ : syracuseStep 542991 = 814487) B814487
theorem B543035 : Blo 542804 543035 := bstep (se 1 (by rfl) ⟨407276, by rfl⟩ : syracuseStep 543035 = 814553) B814553
theorem B2804057 : Blo 542804 2804057 := bstep (se 2 (by rfl) ⟨1051521, by rfl⟩ : syracuseStep 2804057 = 2103043) B2103043
theorem B543111 : Blo 542804 543111 := bstep (se 1 (by rfl) ⟨407333, by rfl⟩ : syracuseStep 543111 = 814667) B814667
theorem B543119 : Blo 542804 543119 := bstep (se 1 (by rfl) ⟨407339, by rfl⟩ : syracuseStep 543119 = 814679) B814679
theorem B1395091 : Blo 542804 1395091 := bstep (se 1 (by rfl) ⟨1046318, by rfl⟩ : syracuseStep 1395091 = 2092637) B2092637
theorem B543163 : Blo 542804 543163 := bstep (se 1 (by rfl) ⟨407372, by rfl⟩ : syracuseStep 543163 = 814745) B814745
theorem B543239 : Blo 542804 543239 := bstep (se 1 (by rfl) ⟨407429, by rfl⟩ : syracuseStep 543239 = 814859) B814859
theorem B543247 : Blo 542804 543247 := bstep (se 1 (by rfl) ⟨407435, by rfl⟩ : syracuseStep 543247 = 814871) B814871
theorem B1395215 : Blo 542804 1395215 := bstep (se 1 (by rfl) ⟨1046411, by rfl⟩ : syracuseStep 1395215 = 2092823) B2092823
theorem B1034785 : Blo 542804 1034785 := bstep (se 2 (by rfl) ⟨388044, by rfl⟩ : syracuseStep 1034785 = 776089) B776089
theorem B543291 : Blo 542804 543291 := bstep (se 1 (by rfl) ⟨407468, by rfl⟩ : syracuseStep 543291 = 814937) B814937
theorem B543367 : Blo 542804 543367 := bstep (se 1 (by rfl) ⟨407525, by rfl⟩ : syracuseStep 543367 = 815051) B815051
theorem B543375 : Blo 542804 543375 := bstep (se 1 (by rfl) ⟨407531, by rfl⟩ : syracuseStep 543375 = 815063) B815063
theorem B543419 : Blo 542804 543419 := bstep (se 1 (by rfl) ⟨407564, by rfl⟩ : syracuseStep 543419 = 815129) B815129
theorem B543495 : Blo 542804 543495 := bstep (se 1 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 543495 = 815243) B815243
theorem B543503 : Blo 542804 543503 := bstep (se 1 (by rfl) ⟨407627, by rfl⟩ : syracuseStep 543503 = 815255) B815255
theorem B543547 : Blo 542804 543547 := bstep (se 1 (by rfl) ⟨407660, by rfl⟩ : syracuseStep 543547 = 815321) B815321
theorem B543623 : Blo 542804 543623 := bstep (se 1 (by rfl) ⟨407717, by rfl⟩ : syracuseStep 543623 = 815435) B815435
theorem B543631 : Blo 542804 543631 := bstep (se 1 (by rfl) ⟨407723, by rfl⟩ : syracuseStep 543631 = 815447) B815447
theorem B543675 : Blo 542804 543675 := bstep (se 1 (by rfl) ⟨407756, by rfl⟩ : syracuseStep 543675 = 815513) B815513
theorem B543751 : Blo 542804 543751 := bstep (se 1 (by rfl) ⟨407813, by rfl⟩ : syracuseStep 543751 = 815627) B815627
theorem B543759 : Blo 542804 543759 := bstep (se 1 (by rfl) ⟨407819, by rfl⟩ : syracuseStep 543759 = 815639) B815639
theorem B543803 : Blo 542804 543803 := bstep (se 1 (by rfl) ⟨407852, by rfl⟩ : syracuseStep 543803 = 815705) B815705
theorem B543879 : Blo 542804 543879 := bstep (se 1 (by rfl) ⟨407909, by rfl⟩ : syracuseStep 543879 = 815819) B815819
theorem B543887 : Blo 542804 543887 := bstep (se 1 (by rfl) ⟨407915, by rfl⟩ : syracuseStep 543887 = 815831) B815831
theorem B543931 : Blo 542804 543931 := bstep (se 1 (by rfl) ⟨407948, by rfl⟩ : syracuseStep 543931 = 815897) B815897
theorem B3525869 : Blo 542804 3525869 := bstep (se 3 (by rfl) ⟨661100, by rfl⟩ : syracuseStep 3525869 = 1322201) B1322201
theorem B544007 : Blo 542804 544007 := bstep (se 1 (by rfl) ⟨408005, by rfl⟩ : syracuseStep 544007 = 816011) B816011
theorem B544015 : Blo 542804 544015 := bstep (se 1 (by rfl) ⟨408011, by rfl⟩ : syracuseStep 544015 = 816023) B816023
theorem B6278417 : Blo 542804 6278417 := bstep (se 2 (by rfl) ⟨2354406, by rfl⟩ : syracuseStep 6278417 = 4708813) B4708813
theorem B773435 : Blo 542804 773435 := bstep (se 1 (by rfl) ⟨580076, by rfl⟩ : syracuseStep 773435 = 1160153) B1160153
theorem B544059 : Blo 542804 544059 := bstep (se 1 (by rfl) ⟨408044, by rfl⟩ : syracuseStep 544059 = 816089) B816089
theorem B2608499 : Blo 542804 2608499 := bstep (se 1 (by rfl) ⟨1956374, by rfl⟩ : syracuseStep 2608499 = 3912749) B3912749
theorem B544135 : Blo 542804 544135 := bstep (se 1 (by rfl) ⟨408101, by rfl⟩ : syracuseStep 544135 = 816203) B816203
theorem B544143 : Blo 542804 544143 := bstep (se 1 (by rfl) ⟨408107, by rfl⟩ : syracuseStep 544143 = 816215) B816215
theorem B2608537 : Blo 542804 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B2936249 : Blo 542804 2936249 := bstep (se 2 (by rfl) ⟨1101093, by rfl⟩ : syracuseStep 2936249 = 2202187) B2202187
theorem B544187 : Blo 542804 544187 := bstep (se 1 (by rfl) ⟨408140, by rfl⟩ : syracuseStep 544187 = 816281) B816281
theorem B544263 : Blo 542804 544263 := bstep (se 1 (by rfl) ⟨408197, by rfl⟩ : syracuseStep 544263 = 816395) B816395
theorem B544271 : Blo 542804 544271 := bstep (se 1 (by rfl) ⟨408203, by rfl⟩ : syracuseStep 544271 = 816407) B816407
theorem B544315 : Blo 542804 544315 := bstep (se 1 (by rfl) ⟨408236, by rfl⟩ : syracuseStep 544315 = 816473) B816473
theorem B544391 : Blo 542804 544391 := bstep (se 1 (by rfl) ⟨408293, by rfl⟩ : syracuseStep 544391 = 816587) B816587
theorem B544399 : Blo 542804 544399 := bstep (se 1 (by rfl) ⟨408299, by rfl⟩ : syracuseStep 544399 = 816599) B816599
theorem B544443 : Blo 542804 544443 := bstep (se 1 (by rfl) ⟨408332, by rfl⟩ : syracuseStep 544443 = 816665) B816665
theorem B773879 : Blo 542804 773879 := bstep (se 1 (by rfl) ⟨580409, by rfl⟩ : syracuseStep 773879 = 1160819) B1160819
theorem B544519 : Blo 542804 544519 := bstep (se 1 (by rfl) ⟨408389, by rfl⟩ : syracuseStep 544519 = 816779) B816779
theorem B544527 : Blo 542804 544527 := bstep (se 1 (by rfl) ⟨408395, by rfl⟩ : syracuseStep 544527 = 816791) B816791
theorem B544571 : Blo 542804 544571 := bstep (se 1 (by rfl) ⟨408428, by rfl⟩ : syracuseStep 544571 = 816857) B816857
theorem B1036091 : Blo 542804 1036091 := bstep (se 1 (by rfl) ⟨777068, by rfl⟩ : syracuseStep 1036091 = 1554137) B1554137
theorem B544647 : Blo 542804 544647 := bstep (se 1 (by rfl) ⟨408485, by rfl⟩ : syracuseStep 544647 = 816971) B816971
theorem B544655 : Blo 542804 544655 := bstep (se 1 (by rfl) ⟨408491, by rfl⟩ : syracuseStep 544655 = 816983) B816983
theorem B774073 : Blo 542804 774073 := bstep (se 2 (by rfl) ⟨290277, by rfl⟩ : syracuseStep 774073 = 580555) B580555
theorem B544699 : Blo 542804 544699 := bstep (se 1 (by rfl) ⟨408524, by rfl⟩ : syracuseStep 544699 = 817049) B817049
theorem B3100619 : Blo 542804 3100619 := bstep (se 1 (by rfl) ⟨2325464, by rfl⟩ : syracuseStep 3100619 = 4650929) B4650929
theorem B544775 : Blo 542804 544775 := bstep (se 1 (by rfl) ⟨408581, by rfl⟩ : syracuseStep 544775 = 817163) B817163
theorem B544783 : Blo 542804 544783 := bstep (se 1 (by rfl) ⟨408587, by rfl⟩ : syracuseStep 544783 = 817175) B817175
theorem B544827 : Blo 542804 544827 := bstep (se 1 (by rfl) ⟨408620, by rfl⟩ : syracuseStep 544827 = 817241) B817241
theorem B544903 : Blo 542804 544903 := bstep (se 1 (by rfl) ⟨408677, by rfl⟩ : syracuseStep 544903 = 817355) B817355
theorem B544911 : Blo 542804 544911 := bstep (se 1 (by rfl) ⟨408683, by rfl⟩ : syracuseStep 544911 = 817367) B817367
theorem B544955 : Blo 542804 544955 := bstep (se 1 (by rfl) ⟨408716, by rfl⟩ : syracuseStep 544955 = 817433) B817433
theorem B545031 : Blo 542804 545031 := bstep (se 1 (by rfl) ⟨408773, by rfl⟩ : syracuseStep 545031 = 817547) B817547
theorem B545039 : Blo 542804 545039 := bstep (se 1 (by rfl) ⟨408779, by rfl⟩ : syracuseStep 545039 = 817559) B817559
theorem B1036577 : Blo 542804 1036577 := bstep (se 2 (by rfl) ⟨388716, by rfl⟩ : syracuseStep 1036577 = 777433) B777433
theorem B545083 : Blo 542804 545083 := bstep (se 1 (by rfl) ⟨408812, by rfl⟩ : syracuseStep 545083 = 817625) B817625
theorem B545159 : Blo 542804 545159 := bstep (se 1 (by rfl) ⟨408869, by rfl⟩ : syracuseStep 545159 = 817739) B817739
theorem B545167 : Blo 542804 545167 := bstep (se 1 (by rfl) ⟨408875, by rfl⟩ : syracuseStep 545167 = 817751) B817751
theorem B3101075 : Blo 542804 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B1036729 : Blo 542804 1036729 := bstep (se 2 (by rfl) ⟨388773, by rfl⟩ : syracuseStep 1036729 = 777547) B777547
theorem B545211 : Blo 542804 545211 := bstep (se 1 (by rfl) ⟨408908, by rfl⟩ : syracuseStep 545211 = 817817) B817817
theorem B545287 : Blo 542804 545287 := bstep (se 1 (by rfl) ⟨408965, by rfl⟩ : syracuseStep 545287 = 817931) B817931
theorem B545295 : Blo 542804 545295 := bstep (se 1 (by rfl) ⟨408971, by rfl⟩ : syracuseStep 545295 = 817943) B817943
theorem B545339 : Blo 542804 545339 := bstep (se 1 (by rfl) ⟨409004, by rfl⟩ : syracuseStep 545339 = 818009) B818009
theorem B610951 : Blo 542804 610951 := bstep (se 1 (by rfl) ⟨458213, by rfl⟩ : syracuseStep 610951 = 916427) B916427
theorem B545415 : Blo 542804 545415 := bstep (se 1 (by rfl) ⟨409061, by rfl⟩ : syracuseStep 545415 = 818123) B818123
theorem B545423 : Blo 542804 545423 := bstep (se 1 (by rfl) ⟨409067, by rfl⟩ : syracuseStep 545423 = 818135) B818135
theorem B545467 : Blo 542804 545467 := bstep (se 1 (by rfl) ⟨409100, by rfl⟩ : syracuseStep 545467 = 818201) B818201
theorem B4149953 : Blo 542804 4149953 := bstep (se 2 (by rfl) ⟨1556232, by rfl⟩ : syracuseStep 4149953 = 3112465) B3112465
theorem B545543 : Blo 542804 545543 := bstep (se 1 (by rfl) ⟨409157, by rfl⟩ : syracuseStep 545543 = 818315) B818315
theorem B545551 : Blo 542804 545551 := bstep (se 1 (by rfl) ⟨409163, by rfl⟩ : syracuseStep 545551 = 818327) B818327
theorem B611131 : Blo 542804 611131 := bstep (se 1 (by rfl) ⟨458348, by rfl⟩ : syracuseStep 611131 = 916697) B916697
theorem B545595 : Blo 542804 545595 := bstep (se 1 (by rfl) ⟨409196, by rfl⟩ : syracuseStep 545595 = 818393) B818393
theorem B545671 : Blo 542804 545671 := bstep (se 1 (by rfl) ⟨409253, by rfl⟩ : syracuseStep 545671 = 818507) B818507
theorem B545679 : Blo 542804 545679 := bstep (se 1 (by rfl) ⟨409259, by rfl⟩ : syracuseStep 545679 = 818519) B818519
theorem B2478995 : Blo 542804 2478995 := bstep (se 1 (by rfl) ⟨1859246, by rfl⟩ : syracuseStep 2478995 = 3718493) B3718493
theorem B545723 : Blo 542804 545723 := bstep (se 1 (by rfl) ⟨409292, by rfl⟩ : syracuseStep 545723 = 818585) B818585
theorem B545799 : Blo 542804 545799 := bstep (se 1 (by rfl) ⟨409349, by rfl⟩ : syracuseStep 545799 = 818699) B818699
theorem B545807 : Blo 542804 545807 := bstep (se 1 (by rfl) ⟨409355, by rfl⟩ : syracuseStep 545807 = 818711) B818711
theorem B545851 : Blo 542804 545851 := bstep (se 1 (by rfl) ⟨409388, by rfl⟩ : syracuseStep 545851 = 818777) B818777
theorem B545927 : Blo 542804 545927 := bstep (se 1 (by rfl) ⟨409445, by rfl⟩ : syracuseStep 545927 = 818891) B818891
theorem B545935 : Blo 542804 545935 := bstep (se 1 (by rfl) ⟨409451, by rfl⟩ : syracuseStep 545935 = 818903) B818903
theorem B545979 : Blo 542804 545979 := bstep (se 1 (by rfl) ⟨409484, by rfl⟩ : syracuseStep 545979 = 818969) B818969
theorem B1660105 : Blo 542804 1660105 := bstep (se 2 (by rfl) ⟨622539, by rfl⟩ : syracuseStep 1660105 = 1245079) B1245079
theorem B546055 : Blo 542804 546055 := bstep (se 1 (by rfl) ⟨409541, by rfl⟩ : syracuseStep 546055 = 819083) B819083
theorem B611599 : Blo 542804 611599 := bstep (se 1 (by rfl) ⟨458699, by rfl⟩ : syracuseStep 611599 = 917399) B917399
theorem B546063 : Blo 542804 546063 := bstep (se 1 (by rfl) ⟨409547, by rfl⟩ : syracuseStep 546063 = 819095) B819095
theorem B546107 : Blo 542804 546107 := bstep (se 1 (by rfl) ⟨409580, by rfl⟩ : syracuseStep 546107 = 819161) B819161
theorem B546183 : Blo 542804 546183 := bstep (se 1 (by rfl) ⟨409637, by rfl⟩ : syracuseStep 546183 = 819275) B819275
theorem B546191 : Blo 542804 546191 := bstep (se 1 (by rfl) ⟨409643, by rfl⟩ : syracuseStep 546191 = 819287) B819287
theorem B5985683 : Blo 542804 5985683 := bstep (se 1 (by rfl) ⟨4489262, by rfl⟩ : syracuseStep 5985683 = 8978525) B8978525
theorem B1398169 : Blo 542804 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B546235 : Blo 542804 546235 := bstep (se 1 (by rfl) ⟨409676, by rfl⟩ : syracuseStep 546235 = 819353) B819353
theorem B546311 : Blo 542804 546311 := bstep (se 1 (by rfl) ⟨409733, by rfl⟩ : syracuseStep 546311 = 819467) B819467
theorem B546319 : Blo 542804 546319 := bstep (se 1 (by rfl) ⟨409739, by rfl⟩ : syracuseStep 546319 = 819479) B819479
theorem B10507805 : Blo 542804 10507805 := bstep (se 3 (by rfl) ⟨1970213, by rfl⟩ : syracuseStep 10507805 = 3940427) B3940427
theorem B546363 : Blo 542804 546363 := bstep (se 1 (by rfl) ⟨409772, by rfl⟩ : syracuseStep 546363 = 819545) B819545
theorem B546439 : Blo 542804 546439 := bstep (se 1 (by rfl) ⟨409829, by rfl⟩ : syracuseStep 546439 = 819659) B819659
theorem B546447 : Blo 542804 546447 := bstep (se 1 (by rfl) ⟨409835, by rfl⟩ : syracuseStep 546447 = 819671) B819671
theorem B546491 : Blo 542804 546491 := bstep (se 1 (by rfl) ⟨409868, by rfl⟩ : syracuseStep 546491 = 819737) B819737
theorem B612103 : Blo 542804 612103 := bstep (se 1 (by rfl) ⟨459077, by rfl⟩ : syracuseStep 612103 = 918155) B918155
theorem B546567 : Blo 542804 546567 := bstep (se 1 (by rfl) ⟨409925, by rfl⟩ : syracuseStep 546567 = 819851) B819851
theorem B546575 : Blo 542804 546575 := bstep (se 1 (by rfl) ⟨409931, by rfl⟩ : syracuseStep 546575 = 819863) B819863
theorem B546619 : Blo 542804 546619 := bstep (se 1 (by rfl) ⟨409964, by rfl⟩ : syracuseStep 546619 = 819929) B819929
theorem B546695 : Blo 542804 546695 := bstep (se 1 (by rfl) ⟨410021, by rfl⟩ : syracuseStep 546695 = 820043) B820043
theorem B546703 : Blo 542804 546703 := bstep (se 1 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 546703 = 820055) B820055
theorem B2840465 : Blo 542804 2840465 := bstep (se 2 (by rfl) ⟨1065174, by rfl⟩ : syracuseStep 2840465 = 2130349) B2130349
theorem B612283 : Blo 542804 612283 := bstep (se 1 (by rfl) ⟨459212, by rfl⟩ : syracuseStep 612283 = 918425) B918425
theorem B546747 : Blo 542804 546747 := bstep (se 1 (by rfl) ⟨410060, by rfl⟩ : syracuseStep 546747 = 820121) B820121
theorem B612751 : Blo 542804 612751 := bstep (se 1 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 612751 = 919127) B919127
theorem B6183377 : Blo 542804 6183377 := bstep (se 2 (by rfl) ⟨2318766, by rfl⟩ : syracuseStep 6183377 = 4637533) B4637533
theorem B12114613 : Blo 542804 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B5299019 : Blo 542804 5299019 := bstep (se 1 (by rfl) ⟨3974264, by rfl⟩ : syracuseStep 5299019 = 7948529) B7948529
theorem B613255 : Blo 542804 613255 := bstep (se 1 (by rfl) ⟨459941, by rfl⟩ : syracuseStep 613255 = 919883) B919883
theorem B580495 : Blo 542804 580495 := bstep (se 1 (by rfl) ⟨435371, by rfl⟩ : syracuseStep 580495 = 870743) B870743
theorem B42589091 : Blo 542804 42589091 := bstep (se 1 (by rfl) ⟨31941818, by rfl⟩ : syracuseStep 42589091 = 63883637) B63883637
theorem B2612189 : Blo 542804 2612189 := bstep (se 3 (by rfl) ⟨489785, by rfl⟩ : syracuseStep 2612189 = 979571) B979571
theorem B3922955 : Blo 542804 3922955 := bstep (se 1 (by rfl) ⟨2942216, by rfl⟩ : syracuseStep 3922955 = 5884433) B5884433
theorem B613435 : Blo 542804 613435 := bstep (se 1 (by rfl) ⟨460076, by rfl⟩ : syracuseStep 613435 = 920153) B920153
theorem B47733941 : Blo 542804 47733941 := bstep (se 5 (by rfl) ⟨2237528, by rfl⟩ : syracuseStep 47733941 = 4475057) B4475057
theorem B580871 : Blo 542804 580871 := bstep (se 1 (by rfl) ⟨435653, by rfl⟩ : syracuseStep 580871 = 871307) B871307
theorem B875791 : Blo 542804 875791 := bstep (se 1 (by rfl) ⟨656843, by rfl⟩ : syracuseStep 875791 = 1313687) B1313687
theorem B14179643 : Blo 542804 14179643 := bstep (se 1 (by rfl) ⟨10634732, by rfl⟩ : syracuseStep 14179643 = 21269465) B21269465
theorem B3366203 : Blo 542804 3366203 := bstep (se 1 (by rfl) ⟨2524652, by rfl⟩ : syracuseStep 3366203 = 5049305) B5049305
theorem B613903 : Blo 542804 613903 := bstep (se 1 (by rfl) ⟨460427, by rfl⟩ : syracuseStep 613903 = 920855) B920855
theorem B1007239 : Blo 542804 1007239 := bstep (se 1 (by rfl) ⟨755429, by rfl⟩ : syracuseStep 1007239 = 1510859) B1510859
theorem B1957613 : Blo 542804 1957613 := bstep (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) B734105
theorem B614407 : Blo 542804 614407 := bstep (se 1 (by rfl) ⟨460805, by rfl⟩ : syracuseStep 614407 = 921611) B921611
theorem B614587 : Blo 542804 614587 := bstep (se 1 (by rfl) ⟨460940, by rfl⟩ : syracuseStep 614587 = 921881) B921881
theorem B2515181 : Blo 542804 2515181 := bstep (se 3 (by rfl) ⟨471596, by rfl⟩ : syracuseStep 2515181 = 943193) B943193
theorem B581947 : Blo 542804 581947 := bstep (se 1 (by rfl) ⟨436460, by rfl⟩ : syracuseStep 581947 = 872921) B872921
theorem B615055 : Blo 542804 615055 := bstep (se 1 (by rfl) ⟨461291, by rfl⟩ : syracuseStep 615055 = 922583) B922583
theorem B13231795 : Blo 542804 13231795 := bstep (se 1 (by rfl) ⟨9923846, by rfl⟩ : syracuseStep 13231795 = 19847693) B19847693
theorem B1239241 : Blo 542804 1239241 := bstep (se 2 (by rfl) ⟨464715, by rfl⟩ : syracuseStep 1239241 = 929431) B929431
theorem B1468687 : Blo 542804 1468687 := bstep (se 1 (by rfl) ⟨1101515, by rfl⟩ : syracuseStep 1468687 = 2203031) B2203031
theorem B2615611 : Blo 542804 2615611 := bstep (se 1 (by rfl) ⟨1961708, by rfl⟩ : syracuseStep 2615611 = 3923417) B3923417
theorem B1436161 : Blo 542804 1436161 := bstep (se 2 (by rfl) ⟨538560, by rfl⟩ : syracuseStep 1436161 = 1077121) B1077121
theorem B4647617 : Blo 542804 4647617 := bstep (se 2 (by rfl) ⟨1742856, by rfl⟩ : syracuseStep 4647617 = 3485713) B3485713
theorem B1862585 : Blo 542804 1862585 := bstep (se 2 (by rfl) ⟨698469, by rfl⟩ : syracuseStep 1862585 = 1396939) B1396939
theorem B4123709 : Blo 542804 4123709 := bstep (se 3 (by rfl) ⟨773195, by rfl⟩ : syracuseStep 4123709 = 1546391) B1546391
theorem B814223 : Blo 542804 814223 := bstep (se 1 (by rfl) ⟨610667, by rfl⟩ : syracuseStep 814223 = 1221335) B1221335
theorem B814265 : Blo 542804 814265 := bstep (se 2 (by rfl) ⟨305349, by rfl⟩ : syracuseStep 814265 = 610699) B610699
theorem B814343 : Blo 542804 814343 := bstep (se 1 (by rfl) ⟨610757, by rfl⟩ : syracuseStep 814343 = 1221515) B1221515
theorem B814379 : Blo 542804 814379 := bstep (se 1 (by rfl) ⟨610784, by rfl⟩ : syracuseStep 814379 = 1221569) B1221569
theorem B814409 : Blo 542804 814409 := bstep (se 2 (by rfl) ⟨305403, by rfl⟩ : syracuseStep 814409 = 610807) B610807
theorem B814523 : Blo 542804 814523 := bstep (se 1 (by rfl) ⟨610892, by rfl⟩ : syracuseStep 814523 = 1221785) B1221785
theorem B814583 : Blo 542804 814583 := bstep (se 1 (by rfl) ⟨610937, by rfl⟩ : syracuseStep 814583 = 1221875) B1221875
theorem B814607 : Blo 542804 814607 := bstep (se 1 (by rfl) ⟨610955, by rfl⟩ : syracuseStep 814607 = 1221911) B1221911
theorem B814649 : Blo 542804 814649 := bstep (se 2 (by rfl) ⟨305493, by rfl⟩ : syracuseStep 814649 = 610987) B610987
theorem B1470071 : Blo 542804 1470071 := bstep (se 1 (by rfl) ⟨1102553, by rfl⟩ : syracuseStep 1470071 = 2205107) B2205107
theorem B814727 : Blo 542804 814727 := bstep (se 1 (by rfl) ⟨611045, by rfl⟩ : syracuseStep 814727 = 1222091) B1222091
theorem B814763 : Blo 542804 814763 := bstep (se 1 (by rfl) ⟨611072, by rfl⟩ : syracuseStep 814763 = 1222145) B1222145
theorem B814793 : Blo 542804 814793 := bstep (se 2 (by rfl) ⟨305547, by rfl⟩ : syracuseStep 814793 = 611095) B611095
theorem B1240847 : Blo 542804 1240847 := bstep (se 1 (by rfl) ⟨930635, by rfl⟩ : syracuseStep 1240847 = 1861271) B1861271
theorem B814907 : Blo 542804 814907 := bstep (se 1 (by rfl) ⟨611180, by rfl⟩ : syracuseStep 814907 = 1222361) B1222361
theorem B814967 : Blo 542804 814967 := bstep (se 1 (by rfl) ⟨611225, by rfl⟩ : syracuseStep 814967 = 1222451) B1222451
theorem B814991 : Blo 542804 814991 := bstep (se 1 (by rfl) ⟨611243, by rfl⟩ : syracuseStep 814991 = 1222487) B1222487
theorem B815033 : Blo 542804 815033 := bstep (se 2 (by rfl) ⟨305637, by rfl⟩ : syracuseStep 815033 = 611275) B611275
theorem B815111 : Blo 542804 815111 := bstep (se 1 (by rfl) ⟨611333, by rfl⟩ : syracuseStep 815111 = 1222667) B1222667
theorem B815147 : Blo 542804 815147 := bstep (se 1 (by rfl) ⟨611360, by rfl⟩ : syracuseStep 815147 = 1222721) B1222721
theorem B815177 : Blo 542804 815177 := bstep (se 2 (by rfl) ⟨305691, by rfl⟩ : syracuseStep 815177 = 611383) B611383
theorem B815291 : Blo 542804 815291 := bstep (se 1 (by rfl) ⟨611468, by rfl⟩ : syracuseStep 815291 = 1222937) B1222937
theorem B2748653 : Blo 542804 2748653 := bstep (se 3 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 2748653 = 1030745) B1030745
theorem B815351 : Blo 542804 815351 := bstep (se 1 (by rfl) ⟨611513, by rfl⟩ : syracuseStep 815351 = 1223027) B1223027
theorem B815375 : Blo 542804 815375 := bstep (se 1 (by rfl) ⟨611531, by rfl⟩ : syracuseStep 815375 = 1223063) B1223063
theorem B815417 : Blo 542804 815417 := bstep (se 2 (by rfl) ⟨305781, by rfl⟩ : syracuseStep 815417 = 611563) B611563
theorem B815495 : Blo 542804 815495 := bstep (se 1 (by rfl) ⟨611621, by rfl⟩ : syracuseStep 815495 = 1223243) B1223243
theorem B815531 : Blo 542804 815531 := bstep (se 1 (by rfl) ⟨611648, by rfl⟩ : syracuseStep 815531 = 1223297) B1223297
theorem B815561 : Blo 542804 815561 := bstep (se 2 (by rfl) ⟨305835, by rfl⟩ : syracuseStep 815561 = 611671) B611671
theorem B979499 : Blo 542804 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B815675 : Blo 542804 815675 := bstep (se 1 (by rfl) ⟨611756, by rfl⟩ : syracuseStep 815675 = 1223513) B1223513
theorem B815735 : Blo 542804 815735 := bstep (se 1 (by rfl) ⟨611801, by rfl⟩ : syracuseStep 815735 = 1223603) B1223603
theorem B815759 : Blo 542804 815759 := bstep (se 1 (by rfl) ⟨611819, by rfl⟩ : syracuseStep 815759 = 1223639) B1223639
theorem B3109549 : Blo 542804 3109549 := bstep (se 3 (by rfl) ⟨583040, by rfl⟩ : syracuseStep 3109549 = 1166081) B1166081
theorem B815801 : Blo 542804 815801 := bstep (se 2 (by rfl) ⟨305925, by rfl⟩ : syracuseStep 815801 = 611851) B611851
theorem B11760389 : Blo 542804 11760389 := bstep (se 4 (by rfl) ⟨1102536, by rfl⟩ : syracuseStep 11760389 = 2205073) B2205073
theorem B815879 : Blo 542804 815879 := bstep (se 1 (by rfl) ⟨611909, by rfl⟩ : syracuseStep 815879 = 1223819) B1223819
theorem B815915 : Blo 542804 815915 := bstep (se 1 (by rfl) ⟨611936, by rfl⟩ : syracuseStep 815915 = 1223873) B1223873
theorem B6615857 : Blo 542804 6615857 := bstep (se 2 (by rfl) ⟨2480946, by rfl⟩ : syracuseStep 6615857 = 4961893) B4961893
theorem B815945 : Blo 542804 815945 := bstep (se 2 (by rfl) ⟨305979, by rfl⟩ : syracuseStep 815945 = 611959) B611959
theorem B6222743 : Blo 542804 6222743 := bstep (se 1 (by rfl) ⟨4667057, by rfl⟩ : syracuseStep 6222743 = 9334115) B9334115
theorem B816059 : Blo 542804 816059 := bstep (se 1 (by rfl) ⟨612044, by rfl⟩ : syracuseStep 816059 = 1224089) B1224089
theorem B652279 : Blo 542804 652279 := bstep (se 1 (by rfl) ⟨489209, by rfl⟩ : syracuseStep 652279 = 978419) B978419
theorem B816119 : Blo 542804 816119 := bstep (se 1 (by rfl) ⟨612089, by rfl⟩ : syracuseStep 816119 = 1224179) B1224179
theorem B652303 : Blo 542804 652303 := bstep (se 1 (by rfl) ⟨489227, by rfl⟩ : syracuseStep 652303 = 978455) B978455
theorem B816143 : Blo 542804 816143 := bstep (se 1 (by rfl) ⟨612107, by rfl⟩ : syracuseStep 816143 = 1224215) B1224215
theorem B2749463 : Blo 542804 2749463 := bstep (se 1 (by rfl) ⟨2062097, by rfl⟩ : syracuseStep 2749463 = 4124195) B4124195
theorem B816185 : Blo 542804 816185 := bstep (se 2 (by rfl) ⟨306069, by rfl⟩ : syracuseStep 816185 = 612139) B612139
theorem B1307767 : Blo 542804 1307767 := bstep (se 1 (by rfl) ⟨980825, by rfl⟩ : syracuseStep 1307767 = 1961651) B1961651
theorem B816263 : Blo 542804 816263 := bstep (se 1 (by rfl) ⟨612197, by rfl⟩ : syracuseStep 816263 = 1224395) B1224395
theorem B816299 : Blo 542804 816299 := bstep (se 1 (by rfl) ⟨612224, by rfl⟩ : syracuseStep 816299 = 1224449) B1224449
theorem B816329 : Blo 542804 816329 := bstep (se 2 (by rfl) ⟨306123, by rfl⟩ : syracuseStep 816329 = 612247) B612247
theorem B816443 : Blo 542804 816443 := bstep (se 1 (by rfl) ⟨612332, by rfl⟩ : syracuseStep 816443 = 1224665) B1224665
theorem B816503 : Blo 542804 816503 := bstep (se 1 (by rfl) ⟨612377, by rfl⟩ : syracuseStep 816503 = 1224755) B1224755
theorem B1832327 : Blo 542804 1832327 := bstep (se 1 (by rfl) ⟨1374245, by rfl⟩ : syracuseStep 1832327 = 2748491) B2748491
theorem B816527 : Blo 542804 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B20903345 : Blo 542804 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B816569 : Blo 542804 816569 := bstep (se 2 (by rfl) ⟨306213, by rfl⟩ : syracuseStep 816569 = 612427) B612427
theorem B6714809 : Blo 542804 6714809 := bstep (se 2 (by rfl) ⟨2518053, by rfl⟩ : syracuseStep 6714809 = 5036107) B5036107
theorem B652807 : Blo 542804 652807 := bstep (se 1 (by rfl) ⟨489605, by rfl⟩ : syracuseStep 652807 = 979211) B979211
theorem B816647 : Blo 542804 816647 := bstep (se 1 (by rfl) ⟨612485, by rfl⟩ : syracuseStep 816647 = 1224971) B1224971
theorem B2323997 : Blo 542804 2323997 := bstep (se 3 (by rfl) ⟨435749, by rfl⟩ : syracuseStep 2323997 = 871499) B871499
theorem B816683 : Blo 542804 816683 := bstep (se 1 (by rfl) ⟨612512, by rfl⟩ : syracuseStep 816683 = 1225025) B1225025
theorem B816713 : Blo 542804 816713 := bstep (se 2 (by rfl) ⟨306267, by rfl⟩ : syracuseStep 816713 = 612535) B612535
theorem B816827 : Blo 542804 816827 := bstep (se 1 (by rfl) ⟨612620, by rfl⟩ : syracuseStep 816827 = 1225241) B1225241
theorem B2488009 : Blo 542804 2488009 := bstep (se 2 (by rfl) ⟨933003, by rfl⟩ : syracuseStep 2488009 = 1866007) B1866007
theorem B6649573 : Blo 542804 6649573 := bstep (se 4 (by rfl) ⟨623397, by rfl⟩ : syracuseStep 6649573 = 1246795) B1246795
theorem B816887 : Blo 542804 816887 := bstep (se 1 (by rfl) ⟨612665, by rfl⟩ : syracuseStep 816887 = 1225331) B1225331
theorem B1832705 : Blo 542804 1832705 := bstep (se 2 (by rfl) ⟨687264, by rfl⟩ : syracuseStep 1832705 = 1374529) B1374529
theorem B816911 : Blo 542804 816911 := bstep (se 1 (by rfl) ⟨612683, by rfl⟩ : syracuseStep 816911 = 1225367) B1225367
theorem B816953 : Blo 542804 816953 := bstep (se 2 (by rfl) ⟨306357, by rfl⟩ : syracuseStep 816953 = 612715) B612715
theorem B817031 : Blo 542804 817031 := bstep (se 1 (by rfl) ⟨612773, by rfl⟩ : syracuseStep 817031 = 1225547) B1225547
theorem B2324371 : Blo 542804 2324371 := bstep (se 1 (by rfl) ⟨1743278, by rfl⟩ : syracuseStep 2324371 = 3486557) B3486557
theorem B817067 : Blo 542804 817067 := bstep (se 1 (by rfl) ⟨612800, by rfl⟩ : syracuseStep 817067 = 1225601) B1225601
theorem B817097 : Blo 542804 817097 := bstep (se 2 (by rfl) ⟨306411, by rfl⟩ : syracuseStep 817097 = 612823) B612823
theorem B817211 : Blo 542804 817211 := bstep (se 1 (by rfl) ⟨612908, by rfl⟩ : syracuseStep 817211 = 1225817) B1225817
theorem B817271 : Blo 542804 817271 := bstep (se 1 (by rfl) ⟨612953, by rfl⟩ : syracuseStep 817271 = 1225907) B1225907
theorem B817295 : Blo 542804 817295 := bstep (se 1 (by rfl) ⟨612971, by rfl⟩ : syracuseStep 817295 = 1225943) B1225943
theorem B817337 : Blo 542804 817337 := bstep (se 2 (by rfl) ⟨306501, by rfl⟩ : syracuseStep 817337 = 613003) B613003
theorem B817415 : Blo 542804 817415 := bstep (se 1 (by rfl) ⟨613061, by rfl⟩ : syracuseStep 817415 = 1226123) B1226123
theorem B1374479 : Blo 542804 1374479 := bstep (se 1 (by rfl) ⟨1030859, by rfl⟩ : syracuseStep 1374479 = 2061719) B2061719
theorem B1964303 : Blo 542804 1964303 := bstep (se 1 (by rfl) ⟨1473227, by rfl⟩ : syracuseStep 1964303 = 2946455) B2946455
theorem B817451 : Blo 542804 817451 := bstep (se 1 (by rfl) ⟨613088, by rfl⟩ : syracuseStep 817451 = 1226177) B1226177
theorem B817481 : Blo 542804 817481 := bstep (se 2 (by rfl) ⟨306555, by rfl⟩ : syracuseStep 817481 = 613111) B613111
theorem B4127111 : Blo 542804 4127111 := bstep (se 1 (by rfl) ⟨3095333, by rfl⟩ : syracuseStep 4127111 = 6190667) B6190667
theorem B817595 : Blo 542804 817595 := bstep (se 1 (by rfl) ⟨613196, by rfl⟩ : syracuseStep 817595 = 1226393) B1226393
theorem B817655 : Blo 542804 817655 := bstep (se 1 (by rfl) ⟨613241, by rfl⟩ : syracuseStep 817655 = 1226483) B1226483
theorem B817679 : Blo 542804 817679 := bstep (se 1 (by rfl) ⟨613259, by rfl⟩ : syracuseStep 817679 = 1226519) B1226519
theorem B1833515 : Blo 542804 1833515 := bstep (se 1 (by rfl) ⟨1375136, by rfl⟩ : syracuseStep 1833515 = 2750273) B2750273
theorem B817721 : Blo 542804 817721 := bstep (se 2 (by rfl) ⟨306645, by rfl⟩ : syracuseStep 817721 = 613291) B613291
theorem B916103 : Blo 542804 916103 := bstep (se 1 (by rfl) ⟨687077, by rfl⟩ : syracuseStep 916103 = 1374155) B1374155
theorem B817799 : Blo 542804 817799 := bstep (se 1 (by rfl) ⟨613349, by rfl⟩ : syracuseStep 817799 = 1226699) B1226699
theorem B817835 : Blo 542804 817835 := bstep (se 1 (by rfl) ⟨613376, by rfl⟩ : syracuseStep 817835 = 1226753) B1226753
theorem B817865 : Blo 542804 817865 := bstep (se 2 (by rfl) ⟨306699, by rfl⟩ : syracuseStep 817865 = 613399) B613399
theorem B817979 : Blo 542804 817979 := bstep (se 1 (by rfl) ⟨613484, by rfl⟩ : syracuseStep 817979 = 1226969) B1226969
theorem B7863155 : Blo 542804 7863155 := bstep (se 1 (by rfl) ⟨5897366, by rfl⟩ : syracuseStep 7863155 = 11794733) B11794733
theorem B818039 : Blo 542804 818039 := bstep (se 1 (by rfl) ⟨613529, by rfl⟩ : syracuseStep 818039 = 1227059) B1227059
theorem B818063 : Blo 542804 818063 := bstep (se 1 (by rfl) ⟨613547, by rfl⟩ : syracuseStep 818063 = 1227095) B1227095
theorem B818105 : Blo 542804 818105 := bstep (se 2 (by rfl) ⟨306789, by rfl⟩ : syracuseStep 818105 = 613579) B613579
theorem B1375177 : Blo 542804 1375177 := bstep (se 2 (by rfl) ⟨515691, by rfl⟩ : syracuseStep 1375177 = 1031383) B1031383
theorem B818183 : Blo 542804 818183 := bstep (se 1 (by rfl) ⟨613637, by rfl⟩ : syracuseStep 818183 = 1227275) B1227275
theorem B3111965 : Blo 542804 3111965 := bstep (se 3 (by rfl) ⟨583493, by rfl⟩ : syracuseStep 3111965 = 1166987) B1166987
theorem B818219 : Blo 542804 818219 := bstep (se 1 (by rfl) ⟨613664, by rfl⟩ : syracuseStep 818219 = 1227329) B1227329
theorem B818249 : Blo 542804 818249 := bstep (se 2 (by rfl) ⟨306843, by rfl⟩ : syracuseStep 818249 = 613687) B613687
theorem B1375319 : Blo 542804 1375319 := bstep (se 1 (by rfl) ⟨1031489, by rfl⟩ : syracuseStep 1375319 = 2062979) B2062979
theorem B785543 : Blo 542804 785543 := bstep (se 1 (by rfl) ⟨589157, by rfl⟩ : syracuseStep 785543 = 1178315) B1178315
theorem B818363 : Blo 542804 818363 := bstep (se 1 (by rfl) ⟨613772, by rfl⟩ : syracuseStep 818363 = 1227545) B1227545
theorem B818423 : Blo 542804 818423 := bstep (se 1 (by rfl) ⟨613817, by rfl⟩ : syracuseStep 818423 = 1227635) B1227635
theorem B916751 : Blo 542804 916751 := bstep (se 1 (by rfl) ⟨687563, by rfl⟩ : syracuseStep 916751 = 1375127) B1375127
theorem B818447 : Blo 542804 818447 := bstep (se 1 (by rfl) ⟨613835, by rfl⟩ : syracuseStep 818447 = 1227671) B1227671
theorem B818489 : Blo 542804 818489 := bstep (se 2 (by rfl) ⟨306933, by rfl⟩ : syracuseStep 818489 = 613867) B613867
theorem B818567 : Blo 542804 818567 := bstep (se 1 (by rfl) ⟨613925, by rfl⟩ : syracuseStep 818567 = 1227851) B1227851
theorem B818603 : Blo 542804 818603 := bstep (se 1 (by rfl) ⟨613952, by rfl⟩ : syracuseStep 818603 = 1227905) B1227905
theorem B818633 : Blo 542804 818633 := bstep (se 2 (by rfl) ⟨306987, by rfl⟩ : syracuseStep 818633 = 613975) B613975
theorem B785911 : Blo 542804 785911 := bstep (se 1 (by rfl) ⟨589433, by rfl⟩ : syracuseStep 785911 = 1178867) B1178867
theorem B1310219 : Blo 542804 1310219 := bstep (se 1 (by rfl) ⟨982664, by rfl⟩ : syracuseStep 1310219 = 1965329) B1965329
theorem B622139 : Blo 542804 622139 := bstep (se 1 (by rfl) ⟨466604, by rfl⟩ : syracuseStep 622139 = 933209) B933209
theorem B818747 : Blo 542804 818747 := bstep (se 1 (by rfl) ⟨614060, by rfl⟩ : syracuseStep 818747 = 1228121) B1228121
theorem B5242445 : Blo 542804 5242445 := bstep (se 3 (by rfl) ⟨982958, by rfl⟩ : syracuseStep 5242445 = 1965917) B1965917
theorem B818807 : Blo 542804 818807 := bstep (se 1 (by rfl) ⟨614105, by rfl⟩ : syracuseStep 818807 = 1228211) B1228211
theorem B818831 : Blo 542804 818831 := bstep (se 1 (by rfl) ⟨614123, by rfl⟩ : syracuseStep 818831 = 1228247) B1228247
theorem B818873 : Blo 542804 818873 := bstep (se 2 (by rfl) ⟨307077, by rfl⟩ : syracuseStep 818873 = 614155) B614155
theorem B9961217 : Blo 542804 9961217 := bstep (se 2 (by rfl) ⟨3735456, by rfl⟩ : syracuseStep 9961217 = 7470913) B7470913
theorem B818951 : Blo 542804 818951 := bstep (se 1 (by rfl) ⟨614213, by rfl⟩ : syracuseStep 818951 = 1228427) B1228427
theorem B917291 : Blo 542804 917291 := bstep (se 1 (by rfl) ⟨687968, by rfl⟩ : syracuseStep 917291 = 1375937) B1375937
theorem B818987 : Blo 542804 818987 := bstep (se 1 (by rfl) ⟨614240, by rfl⟩ : syracuseStep 818987 = 1228481) B1228481
theorem B1834811 : Blo 542804 1834811 := bstep (se 1 (by rfl) ⟨1376108, by rfl⟩ : syracuseStep 1834811 = 2752217) B2752217
theorem B982843 : Blo 542804 982843 := bstep (se 1 (by rfl) ⟨737132, by rfl⟩ : syracuseStep 982843 = 1474265) B1474265
theorem B819017 : Blo 542804 819017 := bstep (se 2 (by rfl) ⟨307131, by rfl⟩ : syracuseStep 819017 = 614263) B614263
theorem B1965977 : Blo 542804 1965977 := bstep (se 2 (by rfl) ⟨737241, by rfl⟩ : syracuseStep 1965977 = 1474483) B1474483
theorem B819131 : Blo 542804 819131 := bstep (se 1 (by rfl) ⟨614348, by rfl⟩ : syracuseStep 819131 = 1228697) B1228697
theorem B819191 : Blo 542804 819191 := bstep (se 1 (by rfl) ⟨614393, by rfl⟩ : syracuseStep 819191 = 1228787) B1228787
theorem B819209 : Blo 542804 819209 := bstep (se 2 (by rfl) ⟨307203, by rfl⟩ : syracuseStep 819209 = 614407) B614407
theorem B1835027 : Blo 542804 1835027 := bstep (se 1 (by rfl) ⟨1376270, by rfl⟩ : syracuseStep 1835027 = 2752541) B2752541
theorem B819239 : Blo 542804 819239 := bstep (se 1 (by rfl) ⟨614429, by rfl⟩ : syracuseStep 819239 = 1228859) B1228859
theorem B917561 : Blo 542804 917561 := bstep (se 2 (by rfl) ⟨344085, by rfl⟩ : syracuseStep 917561 = 688171) B688171
theorem B819323 : Blo 542804 819323 := bstep (se 1 (by rfl) ⟨614492, by rfl⟩ : syracuseStep 819323 = 1228985) B1228985
theorem B5243059 : Blo 542804 5243059 := bstep (se 1 (by rfl) ⟨3932294, by rfl⟩ : syracuseStep 5243059 = 7864589) B7864589
theorem B819449 : Blo 542804 819449 := bstep (se 2 (by rfl) ⟨307293, by rfl⟩ : syracuseStep 819449 = 614587) B614587
theorem B1835351 : Blo 542804 1835351 := bstep (se 1 (by rfl) ⟨1376513, by rfl⟩ : syracuseStep 1835351 = 2753027) B2753027
theorem B819551 : Blo 542804 819551 := bstep (se 1 (by rfl) ⟨614663, by rfl⟩ : syracuseStep 819551 = 1229327) B1229327
theorem B819563 : Blo 542804 819563 := bstep (se 1 (by rfl) ⟨614672, by rfl⟩ : syracuseStep 819563 = 1229345) B1229345
theorem B1376777 : Blo 542804 1376777 := bstep (se 2 (by rfl) ⟨516291, by rfl⟩ : syracuseStep 1376777 = 1032583) B1032583
theorem B819791 : Blo 542804 819791 := bstep (se 1 (by rfl) ⟨614843, by rfl⟩ : syracuseStep 819791 = 1229687) B1229687
theorem B688763 : Blo 542804 688763 := bstep (se 1 (by rfl) ⟨516572, by rfl⟩ : syracuseStep 688763 = 1033145) B1033145
theorem B983723 : Blo 542804 983723 := bstep (se 1 (by rfl) ⟨737792, by rfl⟩ : syracuseStep 983723 = 1475585) B1475585
theorem B819911 : Blo 542804 819911 := bstep (se 1 (by rfl) ⟨614933, by rfl⟩ : syracuseStep 819911 = 1229867) B1229867
theorem B918263 : Blo 542804 918263 := bstep (se 1 (by rfl) ⟨688697, by rfl⟩ : syracuseStep 918263 = 1377395) B1377395
theorem B820073 : Blo 542804 820073 := bstep (se 2 (by rfl) ⟨307527, by rfl⟩ : syracuseStep 820073 = 615055) B615055
theorem B1475435 : Blo 542804 1475435 := bstep (se 1 (by rfl) ⟨1106576, by rfl⟩ : syracuseStep 1475435 = 2213153) B2213153
theorem B4195219 : Blo 542804 4195219 := bstep (se 1 (by rfl) ⟨3146414, by rfl⟩ : syracuseStep 4195219 = 6292829) B6292829
theorem B14156693 : Blo 542804 14156693 := bstep (se 6 (by rfl) ⟨331797, by rfl⟩ : syracuseStep 14156693 = 663595) B663595
theorem B820151 : Blo 542804 820151 := bstep (se 1 (by rfl) ⟨615113, by rfl⟩ : syracuseStep 820151 = 1230227) B1230227
theorem B820187 : Blo 542804 820187 := bstep (se 1 (by rfl) ⟨615140, by rfl⟩ : syracuseStep 820187 = 1230281) B1230281
theorem B5899229 : Blo 542804 5899229 := bstep (se 3 (by rfl) ⟨1106105, by rfl⟩ : syracuseStep 5899229 = 2212211) B2212211
theorem B2065409 : Blo 542804 2065409 := bstep (se 2 (by rfl) ⟨774528, by rfl⟩ : syracuseStep 2065409 = 1549057) B1549057
theorem B918607 : Blo 542804 918607 := bstep (se 1 (by rfl) ⟨688955, by rfl⟩ : syracuseStep 918607 = 1377911) B1377911
theorem B590971 : Blo 542804 590971 := bstep (se 1 (by rfl) ⟨443228, by rfl⟩ : syracuseStep 590971 = 886457) B886457
theorem B918857 : Blo 542804 918857 := bstep (se 2 (by rfl) ⟨344571, by rfl⟩ : syracuseStep 918857 = 689143) B689143
theorem B1836431 : Blo 542804 1836431 := bstep (se 1 (by rfl) ⟨1377323, by rfl⟩ : syracuseStep 1836431 = 2754647) B2754647
theorem B886235 : Blo 542804 886235 := bstep (se 1 (by rfl) ⟨664676, by rfl⟩ : syracuseStep 886235 = 1329353) B1329353
theorem B1869371 : Blo 542804 1869371 := bstep (se 1 (by rfl) ⟨1402028, by rfl⟩ : syracuseStep 1869371 = 2804057) B2804057
theorem B1377931 : Blo 542804 1377931 := bstep (se 1 (by rfl) ⟨1033448, by rfl⟩ : syracuseStep 1377931 = 2066897) B2066897
theorem B1836755 : Blo 542804 1836755 := bstep (se 1 (by rfl) ⟨1377566, by rfl⟩ : syracuseStep 1836755 = 2755133) B2755133
theorem B919289 : Blo 542804 919289 := bstep (se 2 (by rfl) ⟨344733, by rfl⟩ : syracuseStep 919289 = 689467) B689467
theorem B919471 : Blo 542804 919471 := bstep (se 1 (by rfl) ⟨689603, by rfl⟩ : syracuseStep 919471 = 1379207) B1379207
theorem B1378235 : Blo 542804 1378235 := bstep (se 1 (by rfl) ⟨1033676, by rfl⟩ : syracuseStep 1378235 = 2067353) B2067353
theorem B919559 : Blo 542804 919559 := bstep (se 1 (by rfl) ⟨689669, by rfl⟩ : syracuseStep 919559 = 1379339) B1379339
theorem B1738999 : Blo 542804 1738999 := bstep (se 1 (by rfl) ⟨1304249, by rfl⟩ : syracuseStep 1738999 = 2608499) B2608499
theorem B919903 : Blo 542804 919903 := bstep (se 1 (by rfl) ⟨689927, by rfl⟩ : syracuseStep 919903 = 1379855) B1379855
theorem B919991 : Blo 542804 919991 := bstep (se 1 (by rfl) ⟨689993, by rfl⟩ : syracuseStep 919991 = 1379987) B1379987
theorem B1772155 : Blo 542804 1772155 := bstep (se 1 (by rfl) ⟨1329116, by rfl⟩ : syracuseStep 1772155 = 2658233) B2658233
theorem B2067079 : Blo 542804 2067079 := bstep (se 1 (by rfl) ⟨1550309, by rfl⟩ : syracuseStep 2067079 = 3100619) B3100619
theorem B1379015 : Blo 542804 1379015 := bstep (se 1 (by rfl) ⟨1034261, by rfl⟩ : syracuseStep 1379015 = 2068523) B2068523
theorem B1379065 : Blo 542804 1379065 := bstep (se 2 (by rfl) ⟨517149, by rfl⟩ : syracuseStep 1379065 = 1034299) B1034299
theorem B1837943 : Blo 542804 1837943 := bstep (se 1 (by rfl) ⟨1378457, by rfl⟩ : syracuseStep 1837943 = 2756915) B2756915
theorem B2067383 : Blo 542804 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B920585 : Blo 542804 920585 := bstep (se 2 (by rfl) ⟨345219, by rfl⟩ : syracuseStep 920585 = 690439) B690439
theorem B1838159 : Blo 542804 1838159 := bstep (se 1 (by rfl) ⟨1378619, by rfl⟩ : syracuseStep 1838159 = 2757239) B2757239
theorem B920747 : Blo 542804 920747 := bstep (se 1 (by rfl) ⟨690560, by rfl⟩ : syracuseStep 920747 = 1381121) B1381121
theorem B7015619 : Blo 542804 7015619 := bstep (se 1 (by rfl) ⟨5261714, by rfl⟩ : syracuseStep 7015619 = 10523429) B10523429
theorem B1379713 : Blo 542804 1379713 := bstep (se 2 (by rfl) ⟨517392, by rfl⟩ : syracuseStep 1379713 = 1034785) B1034785
theorem B1838537 : Blo 542804 1838537 := bstep (se 2 (by rfl) ⟨689451, by rfl⟩ : syracuseStep 1838537 = 1378903) B1378903
theorem B921145 : Blo 542804 921145 := bstep (se 2 (by rfl) ⟨345429, by rfl⟩ : syracuseStep 921145 = 690859) B690859
theorem B921287 : Blo 542804 921287 := bstep (se 1 (by rfl) ⟨690965, by rfl⟩ : syracuseStep 921287 = 1381931) B1381931
theorem B1838807 : Blo 542804 1838807 := bstep (se 1 (by rfl) ⟨1379105, by rfl⟩ : syracuseStep 1838807 = 2758211) B2758211
theorem B2953027 : Blo 542804 2953027 := bstep (se 1 (by rfl) ⟨2214770, by rfl⟩ : syracuseStep 2953027 = 4429541) B4429541
theorem B921449 : Blo 542804 921449 := bstep (se 2 (by rfl) ⟨345543, by rfl⟩ : syracuseStep 921449 = 691087) B691087
theorem B7868279 : Blo 542804 7868279 := bstep (se 1 (by rfl) ⟨5901209, by rfl⟩ : syracuseStep 7868279 = 11802419) B11802419
theorem B1839023 : Blo 542804 1839023 := bstep (se 1 (by rfl) ⟨1379267, by rfl⟩ : syracuseStep 1839023 = 2758535) B2758535
theorem B2068537 : Blo 542804 2068537 := bstep (se 2 (by rfl) ⟨775701, by rfl⟩ : syracuseStep 2068537 = 1551403) B1551403
theorem B1380523 : Blo 542804 1380523 := bstep (se 1 (by rfl) ⟨1035392, by rfl⟩ : syracuseStep 1380523 = 2070785) B2070785
theorem B921847 : Blo 542804 921847 := bstep (se 1 (by rfl) ⟨691385, by rfl⟩ : syracuseStep 921847 = 1382771) B1382771
theorem B2101565 : Blo 542804 2101565 := bstep (se 3 (by rfl) ⟨394043, by rfl⟩ : syracuseStep 2101565 = 788087) B788087
theorem B2068841 : Blo 542804 2068841 := bstep (se 2 (by rfl) ⟨775815, by rfl⟩ : syracuseStep 2068841 = 1551631) B1551631
theorem B922043 : Blo 542804 922043 := bstep (se 1 (by rfl) ⟨691532, by rfl⟩ : syracuseStep 922043 = 1383065) B1383065
theorem B1380827 : Blo 542804 1380827 := bstep (se 1 (by rfl) ⟨1035620, by rfl⟩ : syracuseStep 1380827 = 2071241) B2071241
theorem B331321873 : Blo 542804 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B3478049 : Blo 542804 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B922151 : Blo 542804 922151 := bstep (se 1 (by rfl) ⟨691613, by rfl⟩ : syracuseStep 922151 = 1383227) B1383227
theorem B31822627 : Blo 542804 31822627 := bstep (se 1 (by rfl) ⟨23866970, by rfl⟩ : syracuseStep 31822627 = 47733941) B47733941
theorem B922441 : Blo 542804 922441 := bstep (se 2 (by rfl) ⟨345915, by rfl⟩ : syracuseStep 922441 = 691831) B691831
theorem B922475 : Blo 542804 922475 := bstep (se 1 (by rfl) ⟨691856, by rfl⟩ : syracuseStep 922475 = 1383713) B1383713
theorem B7574573 : Blo 542804 7574573 := bstep (se 3 (by rfl) ⟨1420232, by rfl⟩ : syracuseStep 7574573 = 2840465) B2840465
theorem B3478949 : Blo 542804 3478949 := bstep (se 4 (by rfl) ⟨326151, by rfl⟩ : syracuseStep 3478949 = 652303) B652303
theorem B2627261 : Blo 542804 2627261 := bstep (se 3 (by rfl) ⟨492611, by rfl⟩ : syracuseStep 2627261 = 985223) B985223
theorem B1382305 : Blo 542804 1382305 := bstep (se 2 (by rfl) ⟨518364, by rfl⟩ : syracuseStep 1382305 = 1036729) B1036729
theorem B1841399 : Blo 542804 1841399 := bstep (se 1 (by rfl) ⟨1381049, by rfl⟩ : syracuseStep 1841399 = 2762099) B2762099
theorem B8853893 : Blo 542804 8853893 := bstep (se 4 (by rfl) ⟨830052, by rfl⟩ : syracuseStep 8853893 = 1660105) B1660105
theorem B1841723 : Blo 542804 1841723 := bstep (se 1 (by rfl) ⟨1381292, by rfl⟩ : syracuseStep 1841723 = 2762585) B2762585
theorem B2333393 : Blo 542804 2333393 := bstep (se 2 (by rfl) ⟨875022, by rfl⟩ : syracuseStep 2333393 = 1750045) B1750045
theorem B1743689 : Blo 542804 1743689 := bstep (se 2 (by rfl) ⟨653883, by rfl⟩ : syracuseStep 1743689 = 1307767) B1307767
theorem B1841993 : Blo 542804 1841993 := bstep (se 2 (by rfl) ⟨690747, by rfl⟩ : syracuseStep 1841993 = 1381495) B1381495
theorem B2760155 : Blo 542804 2760155 := bstep (se 1 (by rfl) ⟨2070116, by rfl⟩ : syracuseStep 2760155 = 4140233) B4140233
theorem B1547873 : Blo 542804 1547873 := bstep (se 2 (by rfl) ⟨580452, by rfl⟩ : syracuseStep 1547873 = 1160905) B1160905
theorem B3317345 : Blo 542804 3317345 := bstep (se 2 (by rfl) ⟨1244004, by rfl⟩ : syracuseStep 3317345 = 2488009) B2488009
theorem B827231 : Blo 542804 827231 := bstep (se 1 (by rfl) ⟨620423, by rfl⟩ : syracuseStep 827231 = 1240847) B1240847
theorem B1843127 : Blo 542804 1843127 := bstep (se 1 (by rfl) ⟨1382345, by rfl⟩ : syracuseStep 1843127 = 2764691) B2764691
theorem B2760641 : Blo 542804 2760641 := bstep (se 2 (by rfl) ⟨1035240, by rfl⟩ : syracuseStep 2760641 = 2070481) B2070481
theorem B2072729 : Blo 542804 2072729 := bstep (se 2 (by rfl) ⟨777273, by rfl⟩ : syracuseStep 2072729 = 1554547) B1554547
theorem B7840259 : Blo 542804 7840259 := bstep (se 1 (by rfl) ⟨5880194, by rfl⟩ : syracuseStep 7840259 = 11760389) B11760389
theorem B1843721 : Blo 542804 1843721 := bstep (se 2 (by rfl) ⟨691395, by rfl⟩ : syracuseStep 1843721 = 1382791) B1382791
theorem B2073185 : Blo 542804 2073185 := bstep (se 2 (by rfl) ⟨777444, by rfl⟩ : syracuseStep 2073185 = 1554889) B1554889
theorem B1548989 : Blo 542804 1548989 := bstep (se 3 (by rfl) ⟨290435, by rfl⟩ : syracuseStep 1548989 = 580871) B580871
theorem B1221551 : Blo 542804 1221551 := bstep (se 1 (by rfl) ⟨916163, by rfl⟩ : syracuseStep 1221551 = 1832327) B1832327
theorem B13935563 : Blo 542804 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B1549331 : Blo 542804 1549331 := bstep (se 1 (by rfl) ⟨1161998, by rfl⟩ : syracuseStep 1549331 = 2323997) B2323997
theorem B1221803 : Blo 542804 1221803 := bstep (se 1 (by rfl) ⟨916352, by rfl⟩ : syracuseStep 1221803 = 1832705) B1832705
theorem B1844585 : Blo 542804 1844585 := bstep (se 2 (by rfl) ⟨691719, by rfl⟩ : syracuseStep 1844585 = 1383439) B1383439
theorem B1222343 : Blo 542804 1222343 := bstep (se 1 (by rfl) ⟨916757, by rfl⟩ : syracuseStep 1222343 = 1833515) B1833515
theorem B1845179 : Blo 542804 1845179 := bstep (se 1 (by rfl) ⟨1383884, by rfl⟩ : syracuseStep 1845179 = 2767769) B2767769
theorem B5220301 : Blo 542804 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B2074643 : Blo 542804 2074643 := bstep (se 1 (by rfl) ⟨1555982, by rfl⟩ : syracuseStep 2074643 = 3111965) B3111965
theorem B2762909 : Blo 542804 2762909 := bstep (se 3 (by rfl) ⟨518045, by rfl⟩ : syracuseStep 2762909 = 1036091) B1036091
theorem B32254355 : Blo 542804 32254355 := bstep (se 1 (by rfl) ⟨24190766, by rfl⟩ : syracuseStep 32254355 = 48381533) B48381533
theorem B1223207 : Blo 542804 1223207 := bstep (se 1 (by rfl) ⟨917405, by rfl⟩ : syracuseStep 1223207 = 1834811) B1834811
theorem B1223531 : Blo 542804 1223531 := bstep (se 1 (by rfl) ⟨917648, by rfl⟩ : syracuseStep 1223531 = 1835297) B1835297
theorem B1223585 : Blo 542804 1223585 := bstep (se 2 (by rfl) ⟨458844, by rfl⟩ : syracuseStep 1223585 = 917689) B917689
theorem B2206727 : Blo 542804 2206727 := bstep (se 1 (by rfl) ⟨1655045, by rfl⟩ : syracuseStep 2206727 = 3310091) B3310091
theorem B1616915 : Blo 542804 1616915 := bstep (se 1 (by rfl) ⟨1212686, by rfl⟩ : syracuseStep 1616915 = 2425373) B2425373
theorem B1223927 : Blo 542804 1223927 := bstep (se 1 (by rfl) ⟨917945, by rfl⟩ : syracuseStep 1223927 = 1835891) B1835891
theorem B2764205 : Blo 542804 2764205 := bstep (se 3 (by rfl) ⟨518288, by rfl⟩ : syracuseStep 2764205 = 1036577) B1036577
theorem B1224521 : Blo 542804 1224521 := bstep (se 2 (by rfl) ⟨459195, by rfl⟩ : syracuseStep 1224521 = 918391) B918391
theorem B1552223 : Blo 542804 1552223 := bstep (se 1 (by rfl) ⟨1164167, by rfl⟩ : syracuseStep 1552223 = 2328335) B2328335
theorem B5975939 : Blo 542804 5975939 := bstep (se 1 (by rfl) ⟨4481954, by rfl⟩ : syracuseStep 5975939 = 8963909) B8963909
theorem B7450555 : Blo 542804 7450555 := bstep (se 1 (by rfl) ⟨5587916, by rfl⟩ : syracuseStep 7450555 = 11175833) B11175833
theorem B930143 : Blo 542804 930143 := bstep (se 1 (by rfl) ⟨697607, by rfl⟩ : syracuseStep 930143 = 1395215) B1395215
theorem B17609177 : Blo 542804 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B1225313 : Blo 542804 1225313 := bstep (se 2 (by rfl) ⟨459492, by rfl⟩ : syracuseStep 1225313 = 918985) B918985
theorem B17642393 : Blo 542804 17642393 := bstep (se 2 (by rfl) ⟨6615897, by rfl⟩ : syracuseStep 17642393 = 13231795) B13231795
theorem B1225655 : Blo 542804 1225655 := bstep (se 1 (by rfl) ⟨919241, by rfl⟩ : syracuseStep 1225655 = 1838483) B1838483
theorem B2765825 : Blo 542804 2765825 := bstep (se 2 (by rfl) ⟨1037184, by rfl⟩ : syracuseStep 2765825 = 2074369) B2074369
theorem B1226249 : Blo 542804 1226249 := bstep (se 2 (by rfl) ⟨459843, by rfl⟩ : syracuseStep 1226249 = 919687) B919687
theorem B1160743 : Blo 542804 1160743 := bstep (se 1 (by rfl) ⟨870557, by rfl⟩ : syracuseStep 1160743 = 1741115) B1741115
theorem B1652321 : Blo 542804 1652321 := bstep (se 2 (by rfl) ⟨619620, by rfl⟩ : syracuseStep 1652321 = 1239241) B1239241
theorem B3487481 : Blo 542804 3487481 := bstep (se 2 (by rfl) ⟨1307805, by rfl⟩ : syracuseStep 3487481 = 2615611) B2615611
theorem B2766635 : Blo 542804 2766635 := bstep (se 1 (by rfl) ⟨2074976, by rfl⟩ : syracuseStep 2766635 = 4149953) B4149953
theorem B1226591 : Blo 542804 1226591 := bstep (se 1 (by rfl) ⟨919943, by rfl⟩ : syracuseStep 1226591 = 1839887) B1839887
theorem B1750891 : Blo 542804 1750891 := bstep (se 1 (by rfl) ⟨1313168, by rfl⟩ : syracuseStep 1750891 = 2626337) B2626337
theorem B1652663 : Blo 542804 1652663 := bstep (se 1 (by rfl) ⟨1239497, by rfl⟩ : syracuseStep 1652663 = 2478995) B2478995
theorem B1914881 : Blo 542804 1914881 := bstep (se 2 (by rfl) ⟨718080, by rfl⟩ : syracuseStep 1914881 = 1436161) B1436161
theorem B1226771 : Blo 542804 1226771 := bstep (se 1 (by rfl) ⟨920078, by rfl⟩ : syracuseStep 1226771 = 1840157) B1840157
theorem B4241497 : Blo 542804 4241497 := bstep (se 2 (by rfl) ⟨1590561, by rfl⟩ : syracuseStep 4241497 = 3181123) B3181123
theorem B1030495 : Blo 542804 1030495 := bstep (se 1 (by rfl) ⟨772871, by rfl⟩ : syracuseStep 1030495 = 1545743) B1545743
theorem B1227113 : Blo 542804 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B1227707 : Blo 542804 1227707 := bstep (se 1 (by rfl) ⟨920780, by rfl⟩ : syracuseStep 1227707 = 1841561) B1841561
theorem B1227833 : Blo 542804 1227833 := bstep (se 2 (by rfl) ⟨460437, by rfl⟩ : syracuseStep 1227833 = 920875) B920875
theorem B28392727 : Blo 542804 28392727 := bstep (se 1 (by rfl) ⟨21294545, by rfl⟩ : syracuseStep 28392727 = 42589091) B42589091
theorem B1228175 : Blo 542804 1228175 := bstep (se 1 (by rfl) ⟨921131, by rfl⟩ : syracuseStep 1228175 = 1842263) B1842263
theorem B1031611 : Blo 542804 1031611 := bstep (se 1 (by rfl) ⟨773708, by rfl⟩ : syracuseStep 1031611 = 1547417) B1547417
theorem B1031687 : Blo 542804 1031687 := bstep (se 1 (by rfl) ⟨773765, by rfl⟩ : syracuseStep 1031687 = 1547531) B1547531
theorem B9453095 : Blo 542804 9453095 := bstep (se 1 (by rfl) ⟨7089821, by rfl⟩ : syracuseStep 9453095 = 14179643) B14179643
theorem B1228499 : Blo 542804 1228499 := bstep (se 1 (by rfl) ⟨921374, by rfl⟩ : syracuseStep 1228499 = 1842749) B1842749
theorem B1032097 : Blo 542804 1032097 := bstep (se 2 (by rfl) ⟨387036, by rfl⟩ : syracuseStep 1032097 = 774073) B774073
theorem B1032439 : Blo 542804 1032439 := bstep (se 1 (by rfl) ⟨774329, by rfl⟩ : syracuseStep 1032439 = 1548659) B1548659
theorem B2212339 : Blo 542804 2212339 := bstep (se 1 (by rfl) ⟨1659254, by rfl⟩ : syracuseStep 2212339 = 3318509) B3318509
theorem B1032743 : Blo 542804 1032743 := bstep (se 1 (by rfl) ⟨774557, by rfl⟩ : syracuseStep 1032743 = 1549115) B1549115
theorem B5227067 : Blo 542804 5227067 := bstep (se 1 (by rfl) ⟨3920300, by rfl⟩ : syracuseStep 5227067 = 7840601) B7840601
theorem B1229435 : Blo 542804 1229435 := bstep (se 1 (by rfl) ⟨922076, by rfl⟩ : syracuseStep 1229435 = 1844153) B1844153
theorem B1229561 : Blo 542804 1229561 := bstep (se 2 (by rfl) ⟨461085, by rfl⟩ : syracuseStep 1229561 = 922171) B922171
theorem B4146065 : Blo 542804 4146065 := bstep (se 2 (by rfl) ⟨1554774, by rfl⟩ : syracuseStep 4146065 = 3109549) B3109549
theorem B1229831 : Blo 542804 1229831 := bstep (se 1 (by rfl) ⟨922373, by rfl⟩ : syracuseStep 1229831 = 1844747) B1844747
theorem B1229903 : Blo 542804 1229903 := bstep (se 1 (by rfl) ⟨922427, by rfl⟩ : syracuseStep 1229903 = 1844855) B1844855
theorem B869705 : Blo 542804 869705 := bstep (se 2 (by rfl) ⟨326139, by rfl⟩ : syracuseStep 869705 = 652279) B652279
theorem B4670885 : Blo 542804 4670885 := bstep (se 4 (by rfl) ⟨437895, by rfl⟩ : syracuseStep 4670885 = 875791) B875791
theorem B1230299 : Blo 542804 1230299 := bstep (se 1 (by rfl) ⟨922724, by rfl⟩ : syracuseStep 1230299 = 1845449) B1845449
theorem B2148049 : Blo 542804 2148049 := bstep (se 2 (by rfl) ⟨805518, by rfl⟩ : syracuseStep 2148049 = 1611037) B1611037
theorem B3098411 : Blo 542804 3098411 := bstep (se 1 (by rfl) ⟨2323808, by rfl⟩ : syracuseStep 3098411 = 4647617) B4647617
theorem B5883911 : Blo 542804 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B870409 : Blo 542804 870409 := bstep (se 2 (by rfl) ⟨326403, by rfl⟩ : syracuseStep 870409 = 652807) B652807
theorem B542815 : Blo 542804 542815 := bstep (se 1 (by rfl) ⟨407111, by rfl⟩ : syracuseStep 542815 = 814223) B814223
theorem B542843 : Blo 542804 542843 := bstep (se 1 (by rfl) ⟨407132, by rfl⟩ : syracuseStep 542843 = 814265) B814265
theorem B542895 : Blo 542804 542895 := bstep (se 1 (by rfl) ⟨407171, by rfl⟩ : syracuseStep 542895 = 814343) B814343
theorem B542919 : Blo 542804 542919 := bstep (se 1 (by rfl) ⟨407189, by rfl⟩ : syracuseStep 542919 = 814379) B814379
theorem B542939 : Blo 542804 542939 := bstep (se 1 (by rfl) ⟨407204, by rfl⟩ : syracuseStep 542939 = 814409) B814409
theorem B543015 : Blo 542804 543015 := bstep (se 1 (by rfl) ⟨407261, by rfl⟩ : syracuseStep 543015 = 814523) B814523
theorem B8866097 : Blo 542804 8866097 := bstep (se 2 (by rfl) ⟨3324786, by rfl⟩ : syracuseStep 8866097 = 6649573) B6649573
theorem B543055 : Blo 542804 543055 := bstep (se 1 (by rfl) ⟨407291, by rfl⟩ : syracuseStep 543055 = 814583) B814583
theorem B543071 : Blo 542804 543071 := bstep (se 1 (by rfl) ⟨407303, by rfl⟩ : syracuseStep 543071 = 814607) B814607
theorem B1034603 : Blo 542804 1034603 := bstep (se 1 (by rfl) ⟨775952, by rfl⟩ : syracuseStep 1034603 = 1551905) B1551905
theorem B543099 : Blo 542804 543099 := bstep (se 1 (by rfl) ⟨407324, by rfl⟩ : syracuseStep 543099 = 814649) B814649
theorem B2214287 : Blo 542804 2214287 := bstep (se 1 (by rfl) ⟨1660715, by rfl⟩ : syracuseStep 2214287 = 3321431) B3321431
theorem B543151 : Blo 542804 543151 := bstep (se 1 (by rfl) ⟨407363, by rfl⟩ : syracuseStep 543151 = 814727) B814727
theorem B543175 : Blo 542804 543175 := bstep (se 1 (by rfl) ⟨407381, by rfl⟩ : syracuseStep 543175 = 814763) B814763
theorem B543195 : Blo 542804 543195 := bstep (se 1 (by rfl) ⟨407396, by rfl⟩ : syracuseStep 543195 = 814793) B814793
theorem B3099161 : Blo 542804 3099161 := bstep (se 2 (by rfl) ⟨1162185, by rfl⟩ : syracuseStep 3099161 = 2324371) B2324371
theorem B3983905 : Blo 542804 3983905 := bstep (se 2 (by rfl) ⟨1493964, by rfl⟩ : syracuseStep 3983905 = 2987929) B2987929
theorem B543271 : Blo 542804 543271 := bstep (se 1 (by rfl) ⟨407453, by rfl⟩ : syracuseStep 543271 = 814907) B814907
theorem B6965837 : Blo 542804 6965837 := bstep (se 3 (by rfl) ⟨1306094, by rfl⟩ : syracuseStep 6965837 = 2612189) B2612189
theorem B543311 : Blo 542804 543311 := bstep (se 1 (by rfl) ⟨407483, by rfl⟩ : syracuseStep 543311 = 814967) B814967
theorem B1034831 : Blo 542804 1034831 := bstep (se 1 (by rfl) ⟨776123, by rfl⟩ : syracuseStep 1034831 = 1552247) B1552247
theorem B543327 : Blo 542804 543327 := bstep (se 1 (by rfl) ⟨407495, by rfl⟩ : syracuseStep 543327 = 814991) B814991
theorem B543355 : Blo 542804 543355 := bstep (se 1 (by rfl) ⟨407516, by rfl⟩ : syracuseStep 543355 = 815033) B815033
theorem B543407 : Blo 542804 543407 := bstep (se 1 (by rfl) ⟨407555, by rfl⟩ : syracuseStep 543407 = 815111) B815111
theorem B543431 : Blo 542804 543431 := bstep (se 1 (by rfl) ⟨407573, by rfl⟩ : syracuseStep 543431 = 815147) B815147
theorem B6310601 : Blo 542804 6310601 := bstep (se 2 (by rfl) ⟨2366475, by rfl⟩ : syracuseStep 6310601 = 4732951) B4732951
theorem B543451 : Blo 542804 543451 := bstep (se 1 (by rfl) ⟨407588, by rfl⟩ : syracuseStep 543451 = 815177) B815177
theorem B4639517 : Blo 542804 4639517 := bstep (se 3 (by rfl) ⟨869909, by rfl⟩ : syracuseStep 4639517 = 1739819) B1739819
theorem B543527 : Blo 542804 543527 := bstep (se 1 (by rfl) ⟨407645, by rfl⟩ : syracuseStep 543527 = 815291) B815291
theorem B543567 : Blo 542804 543567 := bstep (se 1 (by rfl) ⟨407675, by rfl⟩ : syracuseStep 543567 = 815351) B815351
theorem B543583 : Blo 542804 543583 := bstep (se 1 (by rfl) ⟨407687, by rfl⟩ : syracuseStep 543583 = 815375) B815375
theorem B543611 : Blo 542804 543611 := bstep (se 1 (by rfl) ⟨407708, by rfl⟩ : syracuseStep 543611 = 815417) B815417
theorem B543663 : Blo 542804 543663 := bstep (se 1 (by rfl) ⟨407747, by rfl⟩ : syracuseStep 543663 = 815495) B815495
theorem B2214839 : Blo 542804 2214839 := bstep (se 1 (by rfl) ⟨1661129, by rfl⟩ : syracuseStep 2214839 = 3322259) B3322259
theorem B543687 : Blo 542804 543687 := bstep (se 1 (by rfl) ⟨407765, by rfl⟩ : syracuseStep 543687 = 815531) B815531
theorem B543707 : Blo 542804 543707 := bstep (se 1 (by rfl) ⟨407780, by rfl⟩ : syracuseStep 543707 = 815561) B815561
theorem B1035271 : Blo 542804 1035271 := bstep (se 1 (by rfl) ⟨776453, by rfl⟩ : syracuseStep 1035271 = 1552907) B1552907
theorem B543783 : Blo 542804 543783 := bstep (se 1 (by rfl) ⟨407837, by rfl⟩ : syracuseStep 543783 = 815675) B815675
theorem B543823 : Blo 542804 543823 := bstep (se 1 (by rfl) ⟨407867, by rfl⟩ : syracuseStep 543823 = 815735) B815735
theorem B543839 : Blo 542804 543839 := bstep (se 1 (by rfl) ⟨407879, by rfl⟩ : syracuseStep 543839 = 815759) B815759
theorem B543867 : Blo 542804 543867 := bstep (se 1 (by rfl) ⟨407900, by rfl⟩ : syracuseStep 543867 = 815801) B815801
theorem B543919 : Blo 542804 543919 := bstep (se 1 (by rfl) ⟨407939, by rfl⟩ : syracuseStep 543919 = 815879) B815879
theorem B3722435 : Blo 542804 3722435 := bstep (se 1 (by rfl) ⟨2791826, by rfl⟩ : syracuseStep 3722435 = 5583653) B5583653
theorem B543943 : Blo 542804 543943 := bstep (se 1 (by rfl) ⟨407957, by rfl⟩ : syracuseStep 543943 = 815915) B815915
theorem B4410571 : Blo 542804 4410571 := bstep (se 1 (by rfl) ⟨3307928, by rfl⟩ : syracuseStep 4410571 = 6615857) B6615857
theorem B543963 : Blo 542804 543963 := bstep (se 1 (by rfl) ⟨407972, by rfl⟩ : syracuseStep 543963 = 815945) B815945
theorem B4148495 : Blo 542804 4148495 := bstep (se 1 (by rfl) ⟨3111371, by rfl⟩ : syracuseStep 4148495 = 6222743) B6222743
theorem B544039 : Blo 542804 544039 := bstep (se 1 (by rfl) ⟨408029, by rfl⟩ : syracuseStep 544039 = 816059) B816059
theorem B544079 : Blo 542804 544079 := bstep (se 1 (by rfl) ⟨408059, by rfl⟩ : syracuseStep 544079 = 816119) B816119
theorem B544095 : Blo 542804 544095 := bstep (se 1 (by rfl) ⟨408071, by rfl⟩ : syracuseStep 544095 = 816143) B816143
theorem B544123 : Blo 542804 544123 := bstep (se 1 (by rfl) ⟨408092, by rfl⟩ : syracuseStep 544123 = 816185) B816185
theorem B544175 : Blo 542804 544175 := bstep (se 1 (by rfl) ⟨408131, by rfl⟩ : syracuseStep 544175 = 816263) B816263
theorem B544199 : Blo 542804 544199 := bstep (se 1 (by rfl) ⟨408149, by rfl⟩ : syracuseStep 544199 = 816299) B816299
theorem B544219 : Blo 542804 544219 := bstep (se 1 (by rfl) ⟨408164, by rfl⟩ : syracuseStep 544219 = 816329) B816329
theorem B544295 : Blo 542804 544295 := bstep (se 1 (by rfl) ⟨408221, by rfl⟩ : syracuseStep 544295 = 816443) B816443
theorem B544335 : Blo 542804 544335 := bstep (se 1 (by rfl) ⟨408251, by rfl⟩ : syracuseStep 544335 = 816503) B816503
theorem B544351 : Blo 542804 544351 := bstep (se 1 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 544351 = 816527) B816527
theorem B544379 : Blo 542804 544379 := bstep (se 1 (by rfl) ⟨408284, by rfl⟩ : syracuseStep 544379 = 816569) B816569
theorem B4476539 : Blo 542804 4476539 := bstep (se 1 (by rfl) ⟨3357404, by rfl⟩ : syracuseStep 4476539 = 6714809) B6714809
theorem B544431 : Blo 542804 544431 := bstep (se 1 (by rfl) ⟨408323, by rfl⟩ : syracuseStep 544431 = 816647) B816647
theorem B544455 : Blo 542804 544455 := bstep (se 1 (by rfl) ⟨408341, by rfl⟩ : syracuseStep 544455 = 816683) B816683
theorem B544475 : Blo 542804 544475 := bstep (se 1 (by rfl) ⟨408356, by rfl⟩ : syracuseStep 544475 = 816713) B816713
theorem B544551 : Blo 542804 544551 := bstep (se 1 (by rfl) ⟨408413, by rfl⟩ : syracuseStep 544551 = 816827) B816827
theorem B544591 : Blo 542804 544591 := bstep (se 1 (by rfl) ⟨408443, by rfl⟩ : syracuseStep 544591 = 816887) B816887
theorem B544607 : Blo 542804 544607 := bstep (se 1 (by rfl) ⟨408455, by rfl⟩ : syracuseStep 544607 = 816911) B816911
theorem B773993 : Blo 542804 773993 := bstep (se 2 (by rfl) ⟨290247, by rfl⟩ : syracuseStep 773993 = 580495) B580495
theorem B544635 : Blo 542804 544635 := bstep (se 1 (by rfl) ⟨408476, by rfl⟩ : syracuseStep 544635 = 816953) B816953
theorem B544687 : Blo 542804 544687 := bstep (se 1 (by rfl) ⟨408515, by rfl⟩ : syracuseStep 544687 = 817031) B817031
theorem B544711 : Blo 542804 544711 := bstep (se 1 (by rfl) ⟨408533, by rfl⟩ : syracuseStep 544711 = 817067) B817067
theorem B544731 : Blo 542804 544731 := bstep (se 1 (by rfl) ⟨408548, by rfl⟩ : syracuseStep 544731 = 817097) B817097
theorem B8376331 : Blo 542804 8376331 := bstep (se 1 (by rfl) ⟨6282248, by rfl⟩ : syracuseStep 8376331 = 12564497) B12564497
theorem B544807 : Blo 542804 544807 := bstep (se 1 (by rfl) ⟨408605, by rfl⟩ : syracuseStep 544807 = 817211) B817211
theorem B1036327 : Blo 542804 1036327 := bstep (se 1 (by rfl) ⟨777245, by rfl⟩ : syracuseStep 1036327 = 1554491) B1554491
theorem B544847 : Blo 542804 544847 := bstep (se 1 (by rfl) ⟨408635, by rfl⟩ : syracuseStep 544847 = 817271) B817271
theorem B544863 : Blo 542804 544863 := bstep (se 1 (by rfl) ⟨408647, by rfl⟩ : syracuseStep 544863 = 817295) B817295
theorem B544891 : Blo 542804 544891 := bstep (se 1 (by rfl) ⟨408668, by rfl⟩ : syracuseStep 544891 = 817337) B817337
theorem B1659037 : Blo 542804 1659037 := bstep (se 3 (by rfl) ⟨311069, by rfl⟩ : syracuseStep 1659037 = 622139) B622139
theorem B544943 : Blo 542804 544943 := bstep (se 1 (by rfl) ⟨408707, by rfl⟩ : syracuseStep 544943 = 817415) B817415
theorem B544967 : Blo 542804 544967 := bstep (se 1 (by rfl) ⟨408725, by rfl⟩ : syracuseStep 544967 = 817451) B817451
theorem B544987 : Blo 542804 544987 := bstep (se 1 (by rfl) ⟨408740, by rfl⟩ : syracuseStep 544987 = 817481) B817481
theorem B545063 : Blo 542804 545063 := bstep (se 1 (by rfl) ⟨408797, by rfl⟩ : syracuseStep 545063 = 817595) B817595
theorem B545103 : Blo 542804 545103 := bstep (se 1 (by rfl) ⟨408827, by rfl⟩ : syracuseStep 545103 = 817655) B817655
theorem B545119 : Blo 542804 545119 := bstep (se 1 (by rfl) ⟨408839, by rfl⟩ : syracuseStep 545119 = 817679) B817679
theorem B545147 : Blo 542804 545147 := bstep (se 1 (by rfl) ⟨408860, by rfl⟩ : syracuseStep 545147 = 817721) B817721
theorem B610735 : Blo 542804 610735 := bstep (se 1 (by rfl) ⟨458051, by rfl⟩ : syracuseStep 610735 = 916103) B916103
theorem B545199 : Blo 542804 545199 := bstep (se 1 (by rfl) ⟨408899, by rfl⟩ : syracuseStep 545199 = 817799) B817799
theorem B545223 : Blo 542804 545223 := bstep (se 1 (by rfl) ⟨408917, by rfl⟩ : syracuseStep 545223 = 817835) B817835
theorem B545243 : Blo 542804 545243 := bstep (se 1 (by rfl) ⟨408932, by rfl⟩ : syracuseStep 545243 = 817865) B817865
theorem B545319 : Blo 542804 545319 := bstep (se 1 (by rfl) ⟨408989, by rfl⟩ : syracuseStep 545319 = 817979) B817979
theorem B545359 : Blo 542804 545359 := bstep (se 1 (by rfl) ⟨409019, by rfl⟩ : syracuseStep 545359 = 818039) B818039
theorem B545375 : Blo 542804 545375 := bstep (se 1 (by rfl) ⟨409031, by rfl⟩ : syracuseStep 545375 = 818063) B818063
theorem B545403 : Blo 542804 545403 := bstep (se 1 (by rfl) ⟨409052, by rfl⟩ : syracuseStep 545403 = 818105) B818105
theorem B545455 : Blo 542804 545455 := bstep (se 1 (by rfl) ⟨409091, by rfl⟩ : syracuseStep 545455 = 818183) B818183
theorem B545479 : Blo 542804 545479 := bstep (se 1 (by rfl) ⟨409109, by rfl⟩ : syracuseStep 545479 = 818219) B818219
theorem B545499 : Blo 542804 545499 := bstep (se 1 (by rfl) ⟨409124, by rfl⟩ : syracuseStep 545499 = 818249) B818249
theorem B10769165 : Blo 542804 10769165 := bstep (se 3 (by rfl) ⟨2019218, by rfl⟩ : syracuseStep 10769165 = 4038437) B4038437
theorem B545575 : Blo 542804 545575 := bstep (se 1 (by rfl) ⟨409181, by rfl⟩ : syracuseStep 545575 = 818363) B818363
theorem B545615 : Blo 542804 545615 := bstep (se 1 (by rfl) ⟨409211, by rfl⟩ : syracuseStep 545615 = 818423) B818423
theorem B611167 : Blo 542804 611167 := bstep (se 1 (by rfl) ⟨458375, by rfl⟩ : syracuseStep 611167 = 916751) B916751
theorem B545631 : Blo 542804 545631 := bstep (se 1 (by rfl) ⟨409223, by rfl⟩ : syracuseStep 545631 = 818447) B818447
theorem B545659 : Blo 542804 545659 := bstep (se 1 (by rfl) ⟨409244, by rfl⟩ : syracuseStep 545659 = 818489) B818489
theorem B545711 : Blo 542804 545711 := bstep (se 1 (by rfl) ⟨409283, by rfl⟩ : syracuseStep 545711 = 818567) B818567
theorem B545735 : Blo 542804 545735 := bstep (se 1 (by rfl) ⟨409301, by rfl⟩ : syracuseStep 545735 = 818603) B818603
theorem B545755 : Blo 542804 545755 := bstep (se 1 (by rfl) ⟨409316, by rfl⟩ : syracuseStep 545755 = 818633) B818633
theorem B873479 : Blo 542804 873479 := bstep (se 1 (by rfl) ⟨655109, by rfl⟩ : syracuseStep 873479 = 1310219) B1310219
theorem B545831 : Blo 542804 545831 := bstep (se 1 (by rfl) ⟨409373, by rfl⟩ : syracuseStep 545831 = 818747) B818747
theorem B3494963 : Blo 542804 3494963 := bstep (se 1 (by rfl) ⟨2621222, by rfl⟩ : syracuseStep 3494963 = 5242445) B5242445
theorem B545871 : Blo 542804 545871 := bstep (se 1 (by rfl) ⟨409403, by rfl⟩ : syracuseStep 545871 = 818807) B818807
theorem B545887 : Blo 542804 545887 := bstep (se 1 (by rfl) ⟨409415, by rfl⟩ : syracuseStep 545887 = 818831) B818831
theorem B545915 : Blo 542804 545915 := bstep (se 1 (by rfl) ⟨409436, by rfl⟩ : syracuseStep 545915 = 818873) B818873
theorem B6640811 : Blo 542804 6640811 := bstep (se 1 (by rfl) ⟨4980608, by rfl⟩ : syracuseStep 6640811 = 9961217) B9961217
theorem B545967 : Blo 542804 545967 := bstep (se 1 (by rfl) ⟨409475, by rfl⟩ : syracuseStep 545967 = 818951) B818951
theorem B611527 : Blo 542804 611527 := bstep (se 1 (by rfl) ⟨458645, by rfl⟩ : syracuseStep 611527 = 917291) B917291
theorem B545991 : Blo 542804 545991 := bstep (se 1 (by rfl) ⟨409493, by rfl⟩ : syracuseStep 545991 = 818987) B818987
theorem B546011 : Blo 542804 546011 := bstep (se 1 (by rfl) ⟨409508, by rfl⟩ : syracuseStep 546011 = 819017) B819017
theorem B546087 : Blo 542804 546087 := bstep (se 1 (by rfl) ⟨409565, by rfl⟩ : syracuseStep 546087 = 819131) B819131
theorem B546127 : Blo 542804 546127 := bstep (se 1 (by rfl) ⟨409595, by rfl⟩ : syracuseStep 546127 = 819191) B819191
theorem B546143 : Blo 542804 546143 := bstep (se 1 (by rfl) ⟨409607, by rfl⟩ : syracuseStep 546143 = 819215) B819215
theorem B775531 : Blo 542804 775531 := bstep (se 1 (by rfl) ⟨581648, by rfl⟩ : syracuseStep 775531 = 1163297) B1163297
theorem B546171 : Blo 542804 546171 := bstep (se 1 (by rfl) ⟨409628, by rfl⟩ : syracuseStep 546171 = 819257) B819257
theorem B3102077 : Blo 542804 3102077 := bstep (se 3 (by rfl) ⟨581639, by rfl⟩ : syracuseStep 3102077 = 1163279) B1163279
theorem B546223 : Blo 542804 546223 := bstep (se 1 (by rfl) ⟨409667, by rfl⟩ : syracuseStep 546223 = 819335) B819335
theorem B546247 : Blo 542804 546247 := bstep (se 1 (by rfl) ⟨409685, by rfl⟩ : syracuseStep 546247 = 819371) B819371
theorem B546267 : Blo 542804 546267 := bstep (se 1 (by rfl) ⟨409700, by rfl⟩ : syracuseStep 546267 = 819401) B819401
theorem B546343 : Blo 542804 546343 := bstep (se 1 (by rfl) ⟨409757, by rfl⟩ : syracuseStep 546343 = 819515) B819515
theorem B775759 : Blo 542804 775759 := bstep (se 1 (by rfl) ⟨581819, by rfl⟩ : syracuseStep 775759 = 1163639) B1163639
theorem B546383 : Blo 542804 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B546399 : Blo 542804 546399 := bstep (se 1 (by rfl) ⟨409799, by rfl⟩ : syracuseStep 546399 = 819599) B819599
theorem B546427 : Blo 542804 546427 := bstep (se 1 (by rfl) ⟨409820, by rfl⟩ : syracuseStep 546427 = 819641) B819641
theorem B546479 : Blo 542804 546479 := bstep (se 1 (by rfl) ⟨409859, by rfl⟩ : syracuseStep 546479 = 819719) B819719
theorem B546503 : Blo 542804 546503 := bstep (se 1 (by rfl) ⟨409877, by rfl⟩ : syracuseStep 546503 = 819755) B819755
theorem B1038035 : Blo 542804 1038035 := bstep (se 1 (by rfl) ⟨778526, by rfl⟩ : syracuseStep 1038035 = 1557053) B1557053
theorem B546523 : Blo 542804 546523 := bstep (se 1 (by rfl) ⟨409892, by rfl⟩ : syracuseStep 546523 = 819785) B819785
theorem B546599 : Blo 542804 546599 := bstep (se 1 (by rfl) ⟨409949, by rfl⟩ : syracuseStep 546599 = 819899) B819899
theorem B546639 : Blo 542804 546639 := bstep (se 1 (by rfl) ⟨409979, by rfl⟩ : syracuseStep 546639 = 819959) B819959
theorem B546655 : Blo 542804 546655 := bstep (se 1 (by rfl) ⟨409991, by rfl⟩ : syracuseStep 546655 = 819983) B819983
theorem B546683 : Blo 542804 546683 := bstep (se 1 (by rfl) ⟨410012, by rfl⟩ : syracuseStep 546683 = 820025) B820025
theorem B546735 : Blo 542804 546735 := bstep (se 1 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 546735 = 820103) B820103
theorem B546759 : Blo 542804 546759 := bstep (se 1 (by rfl) ⟨410069, by rfl⟩ : syracuseStep 546759 = 820139) B820139
theorem B546779 : Blo 542804 546779 := bstep (se 1 (by rfl) ⟨410084, by rfl⟩ : syracuseStep 546779 = 820169) B820169
theorem B612391 : Blo 542804 612391 := bstep (se 1 (by rfl) ⟨459293, by rfl⟩ : syracuseStep 612391 = 918587) B918587
theorem B4151411 : Blo 542804 4151411 := bstep (se 1 (by rfl) ⟨3113558, by rfl⟩ : syracuseStep 4151411 = 6227117) B6227117
theorem B3496193 : Blo 542804 3496193 := bstep (se 2 (by rfl) ⟨1311072, by rfl⟩ : syracuseStep 3496193 = 2622145) B2622145
theorem B23943755 : Blo 542804 23943755 := bstep (se 1 (by rfl) ⟨17957816, by rfl⟩ : syracuseStep 23943755 = 35915633) B35915633
theorem B2611997 : Blo 542804 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B3103717 : Blo 542804 3103717 := bstep (se 4 (by rfl) ⟨290973, by rfl⟩ : syracuseStep 3103717 = 581947) B581947
theorem B4021249 : Blo 542804 4021249 := bstep (se 2 (by rfl) ⟨1507968, by rfl⟩ : syracuseStep 4021249 = 3015937) B3015937
theorem B1989647 : Blo 542804 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B3103991 : Blo 542804 3103991 := bstep (se 1 (by rfl) ⟨2327993, by rfl⟩ : syracuseStep 3103991 = 4655987) B4655987
theorem B3104243 : Blo 542804 3104243 := bstep (se 1 (by rfl) ⟨2328182, by rfl⟩ : syracuseStep 3104243 = 4656365) B4656365
theorem B4185611 : Blo 542804 4185611 := bstep (se 1 (by rfl) ⟨3139208, by rfl⟩ : syracuseStep 4185611 = 6278417) B6278417
theorem B1957499 : Blo 542804 1957499 := bstep (se 1 (by rfl) ⟨1468124, by rfl⟩ : syracuseStep 1957499 = 2936249) B2936249
theorem B614011 : Blo 542804 614011 := bstep (se 1 (by rfl) ⟨460508, by rfl⟩ : syracuseStep 614011 = 921017) B921017
theorem B1859219 : Blo 542804 1859219 := bstep (se 1 (by rfl) ⟨1394414, by rfl⟩ : syracuseStep 1859219 = 2788829) B2788829
theorem B4644641 : Blo 542804 4644641 := bstep (se 2 (by rfl) ⟨1741740, by rfl⟩ : syracuseStep 4644641 = 3483481) B3483481
theorem B26828597 : Blo 542804 26828597 := bstep (se 5 (by rfl) ⟨1257590, by rfl⟩ : syracuseStep 26828597 = 2515181) B2515181
theorem B6184835 : Blo 542804 6184835 := bstep (se 1 (by rfl) ⟨4638626, by rfl⟩ : syracuseStep 6184835 = 9277253) B9277253
theorem B15065149 : Blo 542804 15065149 := bstep (se 3 (by rfl) ⟨2824715, by rfl⟩ : syracuseStep 15065149 = 5649431) B5649431
theorem B614479 : Blo 542804 614479 := bstep (se 1 (by rfl) ⟨460859, by rfl⟩ : syracuseStep 614479 = 921719) B921719
theorem B3924197 : Blo 542804 3924197 := bstep (se 4 (by rfl) ⟨367893, by rfl⟩ : syracuseStep 3924197 = 735787) B735787
theorem B4415795 : Blo 542804 4415795 := bstep (se 1 (by rfl) ⟨3311846, by rfl⟩ : syracuseStep 4415795 = 6623693) B6623693
theorem B1958249 : Blo 542804 1958249 := bstep (se 2 (by rfl) ⟨734343, by rfl⟩ : syracuseStep 1958249 = 1468687) B1468687
theorem B614875 : Blo 542804 614875 := bstep (se 1 (by rfl) ⟨461156, by rfl⟩ : syracuseStep 614875 = 922313) B922313
theorem B1860121 : Blo 542804 1860121 := bstep (se 2 (by rfl) ⟨697545, by rfl⟩ : syracuseStep 1860121 = 1395091) B1395091
theorem B10642283 : Blo 542804 10642283 := bstep (se 1 (by rfl) ⟨7981712, by rfl⟩ : syracuseStep 10642283 = 15963425) B15963425
theorem B3990455 : Blo 542804 3990455 := bstep (se 1 (by rfl) ⟨2992841, by rfl⟩ : syracuseStep 3990455 = 5985683) B5985683
theorem B4023269 : Blo 542804 4023269 := bstep (se 4 (by rfl) ⟨377181, by rfl⟩ : syracuseStep 4023269 = 754363) B754363
theorem B7005203 : Blo 542804 7005203 := bstep (se 1 (by rfl) ⟨5253902, by rfl⟩ : syracuseStep 7005203 = 10507805) B10507805
theorem B13297097 : Blo 542804 13297097 := bstep (se 2 (by rfl) ⟨4986411, by rfl⟩ : syracuseStep 13297097 = 9972823) B9972823
theorem B4122251 : Blo 542804 4122251 := bstep (se 1 (by rfl) ⟨3091688, by rfl⟩ : syracuseStep 4122251 = 6183377) B6183377
theorem B3106451 : Blo 542804 3106451 := bstep (se 1 (by rfl) ⟨2329838, by rfl⟩ : syracuseStep 3106451 = 4659677) B4659677
theorem B1468115 : Blo 542804 1468115 := bstep (se 1 (by rfl) ⟨1101086, by rfl⟩ : syracuseStep 1468115 = 2202173) B2202173
theorem B3532679 : Blo 542804 3532679 := bstep (se 1 (by rfl) ⟨2649509, by rfl⟩ : syracuseStep 3532679 = 5299019) B5299019
theorem B2615303 : Blo 542804 2615303 := bstep (se 1 (by rfl) ⟨1961477, by rfl⟩ : syracuseStep 2615303 = 3922955) B3922955
theorem B3303767 : Blo 542804 3303767 := bstep (se 1 (by rfl) ⟨2477825, by rfl⟩ : syracuseStep 3303767 = 4955651) B4955651
theorem B3107159 : Blo 542804 3107159 := bstep (se 1 (by rfl) ⟨2330369, by rfl⟩ : syracuseStep 3107159 = 4660739) B4660739
theorem B3500603 : Blo 542804 3500603 := bstep (se 1 (by rfl) ⟨2625452, by rfl⟩ : syracuseStep 3500603 = 5250905) B5250905
theorem B7269041 : Blo 542804 7269041 := bstep (se 2 (by rfl) ⟨2725890, by rfl⟩ : syracuseStep 7269041 = 5451781) B5451781
theorem B6384529 : Blo 542804 6384529 := bstep (se 2 (by rfl) ⟨2394198, by rfl⟩ : syracuseStep 6384529 = 4788397) B4788397
theorem B814511 : Blo 542804 814511 := bstep (se 1 (by rfl) ⟨610883, by rfl⟩ : syracuseStep 814511 = 1221767) B1221767
theorem B814601 : Blo 542804 814601 := bstep (se 2 (by rfl) ⟨305475, by rfl⟩ : syracuseStep 814601 = 610951) B610951
theorem B814631 : Blo 542804 814631 := bstep (se 1 (by rfl) ⟨610973, by rfl⟩ : syracuseStep 814631 = 1221947) B1221947
theorem B3501629 : Blo 542804 3501629 := bstep (se 3 (by rfl) ⟨656555, by rfl⟩ : syracuseStep 3501629 = 1313111) B1313111
theorem B814715 : Blo 542804 814715 := bstep (se 1 (by rfl) ⟨611036, by rfl⟩ : syracuseStep 814715 = 1222073) B1222073
theorem B814841 : Blo 542804 814841 := bstep (se 2 (by rfl) ⟨305565, by rfl⟩ : syracuseStep 814841 = 611131) B611131
theorem B814943 : Blo 542804 814943 := bstep (se 1 (by rfl) ⟨611207, by rfl⟩ : syracuseStep 814943 = 1222415) B1222415
theorem B814955 : Blo 542804 814955 := bstep (se 1 (by rfl) ⟨611216, by rfl⟩ : syracuseStep 814955 = 1222433) B1222433
theorem B815183 : Blo 542804 815183 := bstep (se 1 (by rfl) ⟨611387, by rfl⟩ : syracuseStep 815183 = 1222775) B1222775
theorem B815303 : Blo 542804 815303 := bstep (se 1 (by rfl) ⟨611477, by rfl⟩ : syracuseStep 815303 = 1222955) B1222955
theorem B815465 : Blo 542804 815465 := bstep (se 2 (by rfl) ⟨305799, by rfl⟩ : syracuseStep 815465 = 611599) B611599
theorem B815543 : Blo 542804 815543 := bstep (se 1 (by rfl) ⟨611657, by rfl⟩ : syracuseStep 815543 = 1223315) B1223315
theorem B815579 : Blo 542804 815579 := bstep (se 1 (by rfl) ⟨611684, by rfl⟩ : syracuseStep 815579 = 1223369) B1223369
theorem B1864225 : Blo 542804 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B1241723 : Blo 542804 1241723 := bstep (se 1 (by rfl) ⟨931292, by rfl⟩ : syracuseStep 1241723 = 1862585) B1862585
theorem B2749139 : Blo 542804 2749139 := bstep (se 1 (by rfl) ⟨2061854, by rfl⟩ : syracuseStep 2749139 = 4123709) B4123709
theorem B816047 : Blo 542804 816047 := bstep (se 1 (by rfl) ⟨612035, by rfl⟩ : syracuseStep 816047 = 1224071) B1224071
theorem B816137 : Blo 542804 816137 := bstep (se 2 (by rfl) ⟨306051, by rfl⟩ : syracuseStep 816137 = 612103) B612103
theorem B816167 : Blo 542804 816167 := bstep (se 1 (by rfl) ⟨612125, by rfl⟩ : syracuseStep 816167 = 1224251) B1224251
theorem B980047 : Blo 542804 980047 := bstep (se 1 (by rfl) ⟨735035, by rfl⟩ : syracuseStep 980047 = 1470071) B1470071
theorem B816251 : Blo 542804 816251 := bstep (se 1 (by rfl) ⟨612188, by rfl⟩ : syracuseStep 816251 = 1224377) B1224377
theorem B816377 : Blo 542804 816377 := bstep (se 2 (by rfl) ⟨306141, by rfl⟩ : syracuseStep 816377 = 612283) B612283
theorem B816479 : Blo 542804 816479 := bstep (se 1 (by rfl) ⟨612359, by rfl⟩ : syracuseStep 816479 = 1224719) B1224719
theorem B816491 : Blo 542804 816491 := bstep (se 1 (by rfl) ⟨612368, by rfl⟩ : syracuseStep 816491 = 1224737) B1224737
theorem B1832435 : Blo 542804 1832435 := bstep (se 1 (by rfl) ⟨1374326, by rfl⟩ : syracuseStep 1832435 = 2748653) B2748653
theorem B816719 : Blo 542804 816719 := bstep (se 1 (by rfl) ⟨612539, by rfl⟩ : syracuseStep 816719 = 1225079) B1225079
theorem B2094781 : Blo 542804 2094781 := bstep (se 3 (by rfl) ⟨392771, by rfl⟩ : syracuseStep 2094781 = 785543) B785543
theorem B816839 : Blo 542804 816839 := bstep (se 1 (by rfl) ⟨612629, by rfl⟩ : syracuseStep 816839 = 1225259) B1225259
theorem B817001 : Blo 542804 817001 := bstep (se 2 (by rfl) ⟨306375, by rfl⟩ : syracuseStep 817001 = 612751) B612751
theorem B1472363 : Blo 542804 1472363 := bstep (se 1 (by rfl) ⟨1104272, by rfl⟩ : syracuseStep 1472363 = 2208545) B2208545
theorem B4126625 : Blo 542804 4126625 := bstep (se 2 (by rfl) ⟨1547484, by rfl⟩ : syracuseStep 4126625 = 3094969) B3094969
theorem B817079 : Blo 542804 817079 := bstep (se 1 (by rfl) ⟨612809, by rfl⟩ : syracuseStep 817079 = 1225619) B1225619
theorem B9402317 : Blo 542804 9402317 := bstep (se 3 (by rfl) ⟨1762934, by rfl⟩ : syracuseStep 9402317 = 3525869) B3525869
theorem B817115 : Blo 542804 817115 := bstep (se 1 (by rfl) ⟨612836, by rfl⟩ : syracuseStep 817115 = 1225673) B1225673
theorem B1832975 : Blo 542804 1832975 := bstep (se 1 (by rfl) ⟨1374731, by rfl⟩ : syracuseStep 1832975 = 2749463) B2749463
theorem B1865747 : Blo 542804 1865747 := bstep (se 1 (by rfl) ⟨1399310, by rfl⟩ : syracuseStep 1865747 = 2798621) B2798621
theorem B6977623 : Blo 542804 6977623 := bstep (se 1 (by rfl) ⟨5233217, by rfl⟩ : syracuseStep 6977623 = 10466435) B10466435
theorem B2062493 : Blo 542804 2062493 := bstep (se 3 (by rfl) ⟨386717, by rfl⟩ : syracuseStep 2062493 = 773435) B773435
theorem B1964189 : Blo 542804 1964189 := bstep (se 3 (by rfl) ⟨368285, by rfl⟩ : syracuseStep 1964189 = 736571) B736571
theorem B8976541 : Blo 542804 8976541 := bstep (se 3 (by rfl) ⟨1683101, by rfl⟩ : syracuseStep 8976541 = 3366203) B3366203
theorem B16152817 : Blo 542804 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B817583 : Blo 542804 817583 := bstep (se 1 (by rfl) ⟨613187, by rfl⟩ : syracuseStep 817583 = 1226375) B1226375
theorem B817673 : Blo 542804 817673 := bstep (se 2 (by rfl) ⟨306627, by rfl⟩ : syracuseStep 817673 = 613255) B613255
theorem B817703 : Blo 542804 817703 := bstep (se 1 (by rfl) ⟨613277, by rfl⟩ : syracuseStep 817703 = 1226555) B1226555
theorem B1833569 : Blo 542804 1833569 := bstep (se 2 (by rfl) ⟨687588, by rfl⟩ : syracuseStep 1833569 = 1375177) B1375177
theorem B817787 : Blo 542804 817787 := bstep (se 1 (by rfl) ⟨613340, by rfl⟩ : syracuseStep 817787 = 1226681) B1226681
theorem B817913 : Blo 542804 817913 := bstep (se 2 (by rfl) ⟨306717, by rfl⟩ : syracuseStep 817913 = 613435) B613435
theorem B2063177 : Blo 542804 2063177 := bstep (se 2 (by rfl) ⟨773691, by rfl⟩ : syracuseStep 2063177 = 1547383) B1547383
theorem B916319 : Blo 542804 916319 := bstep (se 1 (by rfl) ⟨687239, by rfl⟩ : syracuseStep 916319 = 1374479) B1374479
theorem B1309535 : Blo 542804 1309535 := bstep (se 1 (by rfl) ⟨982151, by rfl⟩ : syracuseStep 1309535 = 1964303) B1964303
theorem B818015 : Blo 542804 818015 := bstep (se 1 (by rfl) ⟨613511, by rfl⟩ : syracuseStep 818015 = 1227023) B1227023
theorem B818027 : Blo 542804 818027 := bstep (se 1 (by rfl) ⟨613520, by rfl⟩ : syracuseStep 818027 = 1227041) B1227041
theorem B2751407 : Blo 542804 2751407 := bstep (se 1 (by rfl) ⟨2063555, by rfl⟩ : syracuseStep 2751407 = 4127111) B4127111
theorem B5241829 : Blo 542804 5241829 := bstep (se 4 (by rfl) ⟨491421, by rfl⟩ : syracuseStep 5241829 = 982843) B982843
theorem B687143 : Blo 542804 687143 := bstep (se 1 (by rfl) ⟨515357, by rfl⟩ : syracuseStep 687143 = 1030715) B1030715
theorem B1375289 : Blo 542804 1375289 := bstep (se 2 (by rfl) ⟨515733, by rfl⟩ : syracuseStep 1375289 = 1031467) B1031467
theorem B818255 : Blo 542804 818255 := bstep (se 1 (by rfl) ⟨613691, by rfl⟩ : syracuseStep 818255 = 1227383) B1227383
theorem B818375 : Blo 542804 818375 := bstep (se 1 (by rfl) ⟨613781, by rfl⟩ : syracuseStep 818375 = 1227563) B1227563
theorem B5242103 : Blo 542804 5242103 := bstep (se 1 (by rfl) ⟨3931577, by rfl⟩ : syracuseStep 5242103 = 7863155) B7863155
theorem B2063677 : Blo 542804 2063677 := bstep (se 3 (by rfl) ⟨386939, by rfl⟩ : syracuseStep 2063677 = 773879) B773879
theorem B1047881 : Blo 542804 1047881 := bstep (se 2 (by rfl) ⟨392955, by rfl⟩ : syracuseStep 1047881 = 785911) B785911
theorem B818537 : Blo 542804 818537 := bstep (se 2 (by rfl) ⟨306951, by rfl⟩ : syracuseStep 818537 = 613903) B613903
theorem B687467 : Blo 542804 687467 := bstep (se 1 (by rfl) ⟨515600, by rfl⟩ : syracuseStep 687467 = 1031201) B1031201
theorem B916879 : Blo 542804 916879 := bstep (se 1 (by rfl) ⟨687659, by rfl⟩ : syracuseStep 916879 = 1375319) B1375319
theorem B6978959 : Blo 542804 6978959 := bstep (se 1 (by rfl) ⟨5234219, by rfl⟩ : syracuseStep 6978959 = 10468439) B10468439
theorem B818615 : Blo 542804 818615 := bstep (se 1 (by rfl) ⟨613961, by rfl⟩ : syracuseStep 818615 = 1227923) B1227923
theorem B818651 : Blo 542804 818651 := bstep (se 1 (by rfl) ⟨613988, by rfl⟩ : syracuseStep 818651 = 1227977) B1227977
theorem B1342985 : Blo 542804 1342985 := bstep (se 2 (by rfl) ⟨503619, by rfl⟩ : syracuseStep 1342985 = 1007239) B1007239
theorem B819119 : Blo 542804 819119 := bstep (se 1 (by rfl) ⟨614339, by rfl⟩ : syracuseStep 819119 = 1228679) B1228679
theorem B1310651 : Blo 542804 1310651 := bstep (se 1 (by rfl) ⟨982988, by rfl⟩ : syracuseStep 1310651 = 1965977) B1965977
theorem B20086865 : Blo 542804 20086865 := bstep (se 2 (by rfl) ⟨7532574, by rfl⟩ : syracuseStep 20086865 = 15065149) B15065149
theorem B819305 : Blo 542804 819305 := bstep (se 2 (by rfl) ⟨307239, by rfl⟩ : syracuseStep 819305 = 614479) B614479
theorem B1376585 : Blo 542804 1376585 := bstep (se 2 (by rfl) ⟨516219, by rfl⟩ : syracuseStep 1376585 = 1032439) B1032439
theorem B917851 : Blo 542804 917851 := bstep (se 1 (by rfl) ⟨688388, by rfl⟩ : syracuseStep 917851 = 1376777) B1376777
theorem B688495 : Blo 542804 688495 := bstep (se 1 (by rfl) ⟨516371, by rfl⟩ : syracuseStep 688495 = 1032743) B1032743
theorem B819623 : Blo 542804 819623 := bstep (se 1 (by rfl) ⟨614717, by rfl⟩ : syracuseStep 819623 = 1229435) B1229435
theorem B819707 : Blo 542804 819707 := bstep (se 1 (by rfl) ⟨614780, by rfl⟩ : syracuseStep 819707 = 1229561) B1229561
theorem B983623 : Blo 542804 983623 := bstep (se 1 (by rfl) ⟨737717, by rfl⟩ : syracuseStep 983623 = 1475435) B1475435
theorem B9437795 : Blo 542804 9437795 := bstep (se 1 (by rfl) ⟨7078346, by rfl⟩ : syracuseStep 9437795 = 14156693) B14156693
theorem B819833 : Blo 542804 819833 := bstep (se 2 (by rfl) ⟨307437, by rfl⟩ : syracuseStep 819833 = 614875) B614875
theorem B3932819 : Blo 542804 3932819 := bstep (se 1 (by rfl) ⟨2949614, by rfl⟩ : syracuseStep 3932819 = 5899229) B5899229
theorem B2949785 : Blo 542804 2949785 := bstep (se 2 (by rfl) ⟨1106169, by rfl⟩ : syracuseStep 2949785 = 2212339) B2212339
theorem B1376939 : Blo 542804 1376939 := bstep (se 1 (by rfl) ⟨1032704, by rfl⟩ : syracuseStep 1376939 = 2065409) B2065409
theorem B819887 : Blo 542804 819887 := bstep (se 1 (by rfl) ⟨614915, by rfl⟩ : syracuseStep 819887 = 1229831) B1229831
theorem B819935 : Blo 542804 819935 := bstep (se 1 (by rfl) ⟨614951, by rfl⟩ : syracuseStep 819935 = 1229903) B1229903
theorem B5604173 : Blo 542804 5604173 := bstep (se 3 (by rfl) ⟨1050782, by rfl⟩ : syracuseStep 5604173 = 2101565) B2101565
theorem B3113923 : Blo 542804 3113923 := bstep (se 1 (by rfl) ⟨2335442, by rfl⟩ : syracuseStep 3113923 = 4670885) B4670885
theorem B820199 : Blo 542804 820199 := bstep (se 1 (by rfl) ⟨615149, by rfl⟩ : syracuseStep 820199 = 1230299) B1230299
theorem B1246247 : Blo 542804 1246247 := bstep (se 1 (by rfl) ⟨934685, by rfl⟩ : syracuseStep 1246247 = 1869371) B1869371
theorem B2065607 : Blo 542804 2065607 := bstep (se 1 (by rfl) ⟨1549205, by rfl⟩ : syracuseStep 2065607 = 3098411) B3098411
theorem B918823 : Blo 542804 918823 := bstep (se 1 (by rfl) ⟨689117, by rfl⟩ : syracuseStep 918823 = 1378235) B1378235
theorem B787961 : Blo 542804 787961 := bstep (se 2 (by rfl) ⟨295485, by rfl⟩ : syracuseStep 787961 = 590971) B590971
theorem B689735 : Blo 542804 689735 := bstep (se 1 (by rfl) ⟨517301, by rfl⟩ : syracuseStep 689735 = 1034603) B1034603
theorem B1476191 : Blo 542804 1476191 := bstep (se 1 (by rfl) ⟨1107143, by rfl⟩ : syracuseStep 1476191 = 2214287) B2214287
theorem B1836701 : Blo 542804 1836701 := bstep (se 3 (by rfl) ⟨344381, by rfl⟩ : syracuseStep 1836701 = 688763) B688763
theorem B2066107 : Blo 542804 2066107 := bstep (se 1 (by rfl) ⟨1549580, by rfl⟩ : syracuseStep 2066107 = 3099161) B3099161
theorem B689887 : Blo 542804 689887 := bstep (se 1 (by rfl) ⟨517415, by rfl⟩ : syracuseStep 689887 = 1034831) B1034831
theorem B2623261 : Blo 542804 2623261 := bstep (se 3 (by rfl) ⟨491861, by rfl⟩ : syracuseStep 2623261 = 983723) B983723
theorem B919343 : Blo 542804 919343 := bstep (se 1 (by rfl) ⟨689507, by rfl⟩ : syracuseStep 919343 = 1379015) B1379015
theorem B1378255 : Blo 542804 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B1476559 : Blo 542804 1476559 := bstep (se 1 (by rfl) ⟨1107419, by rfl⟩ : syracuseStep 1476559 = 2214839) B2214839
theorem B1837241 : Blo 542804 1837241 := bstep (se 2 (by rfl) ⟨688965, by rfl⟩ : syracuseStep 1837241 = 1377931) B1377931
theorem B2984359 : Blo 542804 2984359 := bstep (se 1 (by rfl) ⟨2238269, by rfl⟩ : syracuseStep 2984359 = 4476539) B4476539
theorem B1379227 : Blo 542804 1379227 := bstep (se 1 (by rfl) ⟨1034420, by rfl⟩ : syracuseStep 1379227 = 2068841) B2068841
theorem B920551 : Blo 542804 920551 := bstep (se 1 (by rfl) ⟨690413, by rfl⟩ : syracuseStep 920551 = 1380827) B1380827
theorem B7179443 : Blo 542804 7179443 := bstep (se 1 (by rfl) ⟨5384582, by rfl⟩ : syracuseStep 7179443 = 10769165) B10769165
theorem B5049715 : Blo 542804 5049715 := bstep (se 1 (by rfl) ⟨3787286, by rfl⟩ : syracuseStep 5049715 = 7574573) B7574573
theorem B2329975 : Blo 542804 2329975 := bstep (se 1 (by rfl) ⟨1747481, by rfl⟩ : syracuseStep 2329975 = 3494963) B3494963
theorem B5311873 : Blo 542804 5311873 := bstep (se 2 (by rfl) ⟨1991952, by rfl⟩ : syracuseStep 5311873 = 3983905) B3983905
theorem B4427207 : Blo 542804 4427207 := bstep (se 1 (by rfl) ⟨3320405, by rfl⟩ : syracuseStep 4427207 = 6640811) B6640811
theorem B2756105 : Blo 542804 2756105 := bstep (se 2 (by rfl) ⟨1033539, by rfl⟩ : syracuseStep 2756105 = 2067079) B2067079
theorem B2068051 : Blo 542804 2068051 := bstep (se 1 (by rfl) ⟨1551038, by rfl⟩ : syracuseStep 2068051 = 3102077) B3102077
theorem B1838753 : Blo 542804 1838753 := bstep (se 2 (by rfl) ⟨689532, by rfl⟩ : syracuseStep 1838753 = 1379065) B1379065
theorem B2363293 : Blo 542804 2363293 := bstep (se 3 (by rfl) ⟨443117, by rfl⟩ : syracuseStep 2363293 = 886235) B886235
theorem B1380361 : Blo 542804 1380361 := bstep (se 2 (by rfl) ⟨517635, by rfl⟩ : syracuseStep 1380361 = 1035271) B1035271
theorem B2330795 : Blo 542804 2330795 := bstep (se 1 (by rfl) ⟨1748096, by rfl⟩ : syracuseStep 2330795 = 3496193) B3496193
theorem B5902595 : Blo 542804 5902595 := bstep (se 1 (by rfl) ⟨4426946, by rfl⟩ : syracuseStep 5902595 = 8853893) B8853893
theorem B15962503 : Blo 542804 15962503 := bstep (se 1 (by rfl) ⟨11971877, by rfl⟩ : syracuseStep 15962503 = 23943755) B23943755
theorem B1839617 : Blo 542804 1839617 := bstep (se 2 (by rfl) ⟨689856, by rfl⟩ : syracuseStep 1839617 = 1379713) B1379713
theorem B1741331 : Blo 542804 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B2069327 : Blo 542804 2069327 := bstep (se 1 (by rfl) ⟨1551995, by rfl⟩ : syracuseStep 2069327 = 3103991) B3103991
theorem B1840103 : Blo 542804 1840103 := bstep (se 1 (by rfl) ⟨1380077, by rfl⟩ : syracuseStep 1840103 = 2760155) B2760155
theorem B2069495 : Blo 542804 2069495 := bstep (se 1 (by rfl) ⟨1552121, by rfl⟩ : syracuseStep 2069495 = 3104243) B3104243
theorem B2790407 : Blo 542804 2790407 := bstep (se 1 (by rfl) ⟨2092805, by rfl⟩ : syracuseStep 2790407 = 4185611) B4185611
theorem B9934073 : Blo 542804 9934073 := bstep (se 2 (by rfl) ⟨3725277, by rfl⟩ : syracuseStep 9934073 = 7450555) B7450555
theorem B1840427 : Blo 542804 1840427 := bstep (se 1 (by rfl) ⟨1380320, by rfl⟩ : syracuseStep 1840427 = 2760641) B2760641
theorem B1381769 : Blo 542804 1381769 := bstep (se 2 (by rfl) ⟨518163, by rfl⟩ : syracuseStep 1381769 = 1036327) B1036327
theorem B2758049 : Blo 542804 2758049 := bstep (se 2 (by rfl) ⟨1034268, by rfl⟩ : syracuseStep 2758049 = 2068537) B2068537
theorem B1381819 : Blo 542804 1381819 := bstep (se 1 (by rfl) ⟨1036364, by rfl⟩ : syracuseStep 1381819 = 2072729) B2072729
theorem B1840697 : Blo 542804 1840697 := bstep (se 2 (by rfl) ⟨690261, by rfl⟩ : syracuseStep 1840697 = 1380523) B1380523
theorem B1382123 : Blo 542804 1382123 := bstep (se 1 (by rfl) ⟨1036592, by rfl⟩ : syracuseStep 1382123 = 2073185) B2073185
theorem B2660303 : Blo 542804 2660303 := bstep (se 1 (by rfl) ⟨1995227, by rfl⟩ : syracuseStep 2660303 = 3990455) B3990455
theorem B2070967 : Blo 542804 2070967 := bstep (se 1 (by rfl) ⟨1553225, by rfl⟩ : syracuseStep 2070967 = 3106451) B3106451
theorem B1743535 : Blo 542804 1743535 := bstep (se 1 (by rfl) ⟨1307651, by rfl⟩ : syracuseStep 1743535 = 2615303) B2615303
theorem B1383095 : Blo 542804 1383095 := bstep (se 1 (by rfl) ⟨1037321, by rfl⟩ : syracuseStep 1383095 = 2074643) B2074643
theorem B1841939 : Blo 542804 1841939 := bstep (se 1 (by rfl) ⟨1381454, by rfl⟩ : syracuseStep 1841939 = 2762909) B2762909
theorem B2202511 : Blo 542804 2202511 := bstep (se 1 (by rfl) ⟨1651883, by rfl⟩ : syracuseStep 2202511 = 3303767) B3303767
theorem B2071439 : Blo 542804 2071439 := bstep (se 1 (by rfl) ⟨1553579, by rfl⟩ : syracuseStep 2071439 = 3107159) B3107159
theorem B21502903 : Blo 542804 21502903 := bstep (se 1 (by rfl) ⟨16127177, by rfl⟩ : syracuseStep 21502903 = 32254355) B32254355
theorem B2333735 : Blo 542804 2333735 := bstep (se 1 (by rfl) ⟨1750301, by rfl⟩ : syracuseStep 2333735 = 3500603) B3500603
theorem B1547657 : Blo 542804 1547657 := bstep (se 2 (by rfl) ⟨580371, by rfl⟩ : syracuseStep 1547657 = 1160743) B1160743
theorem B2793041 : Blo 542804 2793041 := bstep (se 2 (by rfl) ⟨1047390, by rfl⟩ : syracuseStep 2793041 = 2094781) B2094781
theorem B1842803 : Blo 542804 1842803 := bstep (se 1 (by rfl) ⟨1382102, by rfl⟩ : syracuseStep 1842803 = 2764205) B2764205
theorem B2334419 : Blo 542804 2334419 := bstep (se 1 (by rfl) ⟨1750814, by rfl⟩ : syracuseStep 2334419 = 3501629) B3501629
theorem B2334521 : Blo 542804 2334521 := bstep (se 2 (by rfl) ⟨875445, by rfl⟩ : syracuseStep 2334521 = 1750891) B1750891
theorem B1843073 : Blo 542804 1843073 := bstep (se 2 (by rfl) ⟨691152, by rfl⟩ : syracuseStep 1843073 = 1382305) B1382305
theorem B11968721 : Blo 542804 11968721 := bstep (se 2 (by rfl) ⟨4488270, by rfl⟩ : syracuseStep 11968721 = 8976541) B8976541
theorem B11739451 : Blo 542804 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B21537089 : Blo 542804 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B827815 : Blo 542804 827815 := bstep (se 1 (by rfl) ⟨620861, by rfl⟩ : syracuseStep 827815 = 1241723) B1241723
theorem B1843883 : Blo 542804 1843883 := bstep (se 1 (by rfl) ⟨1382912, by rfl⟩ : syracuseStep 1843883 = 2765825) B2765825
theorem B1221623 : Blo 542804 1221623 := bstep (se 1 (by rfl) ⟨916217, by rfl⟩ : syracuseStep 1221623 = 1832435) B1832435
theorem B1844423 : Blo 542804 1844423 := bstep (se 1 (by rfl) ⟨1383317, by rfl⟩ : syracuseStep 1844423 = 2766635) B2766635
theorem B4138289 : Blo 542804 4138289 := bstep (se 2 (by rfl) ⟨1551858, by rfl⟩ : syracuseStep 4138289 = 3103717) B3103717
theorem B6989105 : Blo 542804 6989105 := bstep (se 2 (by rfl) ⟨2620914, by rfl⟩ : syracuseStep 6989105 = 5241829) B5241829
theorem B6268211 : Blo 542804 6268211 := bstep (se 1 (by rfl) ⟨4701158, by rfl⟩ : syracuseStep 6268211 = 9402317) B9402317
theorem B1221983 : Blo 542804 1221983 := bstep (se 1 (by rfl) ⟨916487, by rfl⟩ : syracuseStep 1221983 = 1832975) B1832975
theorem B3581293 : Blo 542804 3581293 := bstep (se 3 (by rfl) ⟨671492, by rfl⟩ : syracuseStep 3581293 = 1342985) B1342985
theorem B37856969 : Blo 542804 37856969 := bstep (se 2 (by rfl) ⟨14196363, by rfl⟩ : syracuseStep 37856969 = 28392727) B28392727
theorem B1222379 : Blo 542804 1222379 := bstep (se 1 (by rfl) ⟨916784, by rfl⟩ : syracuseStep 1222379 = 1833569) B1833569
theorem B1222505 : Blo 542804 1222505 := bstep (se 2 (by rfl) ⟨458439, by rfl⟩ : syracuseStep 1222505 = 916879) B916879
theorem B698587 : Blo 542804 698587 := bstep (se 1 (by rfl) ⟨523940, by rfl⟩ : syracuseStep 698587 = 1047881) B1047881
theorem B2205949 : Blo 542804 2205949 := bstep (se 3 (by rfl) ⟨413615, by rfl⟩ : syracuseStep 2205949 = 827231) B827231
theorem B4139261 : Blo 542804 4139261 := bstep (se 3 (by rfl) ⟨776111, by rfl⟩ : syracuseStep 4139261 = 1552223) B1552223
theorem B20982077 : Blo 542804 20982077 := bstep (se 3 (by rfl) ⟨3934139, by rfl⟩ : syracuseStep 20982077 = 7868279) B7868279
theorem B6302063 : Blo 542804 6302063 := bstep (se 1 (by rfl) ⟨4726547, by rfl⟩ : syracuseStep 6302063 = 9453095) B9453095
theorem B1223351 : Blo 542804 1223351 := bstep (se 1 (by rfl) ⟨917513, by rfl⟩ : syracuseStep 1223351 = 1835027) B1835027
theorem B1223567 : Blo 542804 1223567 := bstep (se 1 (by rfl) ⟨917675, by rfl⟩ : syracuseStep 1223567 = 1835351) B1835351
theorem B6990745 : Blo 542804 6990745 := bstep (se 2 (by rfl) ⟨2621529, by rfl⟩ : syracuseStep 6990745 = 5243059) B5243059
theorem B3484711 : Blo 542804 3484711 := bstep (se 1 (by rfl) ⟨2613533, by rfl⟩ : syracuseStep 3484711 = 5227067) B5227067
theorem B2764043 : Blo 542804 2764043 := bstep (se 1 (by rfl) ⟨2073032, by rfl⟩ : syracuseStep 2764043 = 4146065) B4146065
theorem B1224287 : Blo 542804 1224287 := bstep (se 1 (by rfl) ⟨918215, by rfl⟩ : syracuseStep 1224287 = 1836431) B1836431
theorem B1224503 : Blo 542804 1224503 := bstep (se 1 (by rfl) ⟨918377, by rfl⟩ : syracuseStep 1224503 = 1836755) B1836755
theorem B1224809 : Blo 542804 1224809 := bstep (se 2 (by rfl) ⟨459303, by rfl⟩ : syracuseStep 1224809 = 918607) B918607
theorem B5910731 : Blo 542804 5910731 := bstep (se 1 (by rfl) ⟨4433048, by rfl⟩ : syracuseStep 5910731 = 8866097) B8866097
theorem B4207067 : Blo 542804 4207067 := bstep (se 1 (by rfl) ⟨3155300, by rfl⟩ : syracuseStep 4207067 = 6310601) B6310601
theorem B3093011 : Blo 542804 3093011 := bstep (se 1 (by rfl) ⟨2319758, by rfl⟩ : syracuseStep 3093011 = 4639517) B4639517
theorem B1225295 : Blo 542804 1225295 := bstep (se 1 (by rfl) ⟨918971, by rfl⟩ : syracuseStep 1225295 = 1837943) B1837943
theorem B1225439 : Blo 542804 1225439 := bstep (se 1 (by rfl) ⟨919079, by rfl⟩ : syracuseStep 1225439 = 1838159) B1838159
theorem B2765663 : Blo 542804 2765663 := bstep (se 1 (by rfl) ⟨2074247, by rfl⟩ : syracuseStep 2765663 = 4148495) B4148495
theorem B2864065 : Blo 542804 2864065 := bstep (se 2 (by rfl) ⟨1074024, by rfl⟩ : syracuseStep 2864065 = 2148049) B2148049
theorem B1225691 : Blo 542804 1225691 := bstep (se 1 (by rfl) ⟨919268, by rfl⟩ : syracuseStep 1225691 = 1838537) B1838537
theorem B1225871 : Blo 542804 1225871 := bstep (se 1 (by rfl) ⟨919403, by rfl⟩ : syracuseStep 1225871 = 1838807) B1838807
theorem B1225961 : Blo 542804 1225961 := bstep (se 2 (by rfl) ⟨459735, by rfl⟩ : syracuseStep 1225961 = 919471) B919471
theorem B6960401 : Blo 542804 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B1226015 : Blo 542804 1226015 := bstep (se 1 (by rfl) ⟨919511, by rfl⟩ : syracuseStep 1226015 = 1839023) B1839023
theorem B1226537 : Blo 542804 1226537 := bstep (se 2 (by rfl) ⟨459951, by rfl⟩ : syracuseStep 1226537 = 919903) B919903
theorem B9451493 : Blo 542804 9451493 := bstep (se 4 (by rfl) ⟨886077, by rfl⟩ : syracuseStep 9451493 = 1772155) B1772155
theorem B1751507 : Blo 542804 1751507 := bstep (se 1 (by rfl) ⟨1313630, by rfl⟩ : syracuseStep 1751507 = 2627261) B2627261
theorem B2767607 : Blo 542804 2767607 := bstep (se 1 (by rfl) ⟨2075705, by rfl⟩ : syracuseStep 2767607 = 4151411) B4151411
theorem B1227599 : Blo 542804 1227599 := bstep (se 1 (by rfl) ⟨920699, by rfl⟩ : syracuseStep 1227599 = 1841399) B1841399
theorem B5880761 : Blo 542804 5880761 := bstep (se 2 (by rfl) ⟨2205285, by rfl⟩ : syracuseStep 5880761 = 4410571) B4410571
theorem B1227815 : Blo 542804 1227815 := bstep (se 1 (by rfl) ⟨920861, by rfl⟩ : syracuseStep 1227815 = 1841723) B1841723
theorem B1555595 : Blo 542804 1555595 := bstep (se 1 (by rfl) ⟨1166696, by rfl⟩ : syracuseStep 1555595 = 2333393) B2333393
theorem B1162459 : Blo 542804 1162459 := bstep (se 1 (by rfl) ⟨871844, by rfl⟩ : syracuseStep 1162459 = 1743689) B1743689
theorem B1227995 : Blo 542804 1227995 := bstep (se 1 (by rfl) ⟨920996, by rfl⟩ : syracuseStep 1227995 = 1841993) B1841993
theorem B2768093 : Blo 542804 2768093 := bstep (se 3 (by rfl) ⟨519017, by rfl⟩ : syracuseStep 2768093 = 1038035) B1038035
theorem B1326431 : Blo 542804 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B1228193 : Blo 542804 1228193 := bstep (se 2 (by rfl) ⟨460572, by rfl⟩ : syracuseStep 1228193 = 921145) B921145
theorem B1031915 : Blo 542804 1031915 := bstep (se 1 (by rfl) ⟨773936, by rfl⟩ : syracuseStep 1031915 = 1547873) B1547873
theorem B2211563 : Blo 542804 2211563 := bstep (se 1 (by rfl) ⟨1658672, by rfl⟩ : syracuseStep 2211563 = 3317345) B3317345
theorem B3096427 : Blo 542804 3096427 := bstep (se 1 (by rfl) ⟨2322320, by rfl⟩ : syracuseStep 3096427 = 4644641) B4644641
theorem B1228751 : Blo 542804 1228751 := bstep (se 1 (by rfl) ⟨921563, by rfl⟩ : syracuseStep 1228751 = 1843127) B1843127
theorem B2212049 : Blo 542804 2212049 := bstep (se 2 (by rfl) ⟨829518, by rfl⟩ : syracuseStep 2212049 = 1659037) B1659037
theorem B1229129 : Blo 542804 1229129 := bstep (se 2 (by rfl) ⟨460923, by rfl⟩ : syracuseStep 1229129 = 921847) B921847
theorem B5226839 : Blo 542804 5226839 := bstep (se 1 (by rfl) ⟨3920129, by rfl⟩ : syracuseStep 5226839 = 7840259) B7840259
theorem B1229147 : Blo 542804 1229147 := bstep (se 1 (by rfl) ⟨921860, by rfl⟩ : syracuseStep 1229147 = 1843721) B1843721
theorem B1032659 : Blo 542804 1032659 := bstep (se 1 (by rfl) ⟨774494, by rfl⟩ : syracuseStep 1032659 = 1548989) B1548989
theorem B7094855 : Blo 542804 7094855 := bstep (se 1 (by rfl) ⟨5321141, by rfl⟩ : syracuseStep 7094855 = 10642283) B10642283
theorem B9290375 : Blo 542804 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B1032887 : Blo 542804 1032887 := bstep (se 1 (by rfl) ⟨774665, by rfl⟩ : syracuseStep 1032887 = 1549331) B1549331
theorem B4670135 : Blo 542804 4670135 := bstep (se 1 (by rfl) ⟨3502601, by rfl⟩ : syracuseStep 4670135 = 7005203) B7005203
theorem B441762497 : Blo 542804 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B1229723 : Blo 542804 1229723 := bstep (se 1 (by rfl) ⟨922292, by rfl⟩ : syracuseStep 1229723 = 1844585) B1844585
theorem B8864731 : Blo 542804 8864731 := bstep (se 1 (by rfl) ⟨6648548, by rfl⟩ : syracuseStep 8864731 = 13297097) B13297097
theorem B1229921 : Blo 542804 1229921 := bstep (se 2 (by rfl) ⟨461220, by rfl⟩ : syracuseStep 1229921 = 922441) B922441
theorem B1230119 : Blo 542804 1230119 := bstep (se 1 (by rfl) ⟨922589, by rfl⟩ : syracuseStep 1230119 = 1845179) B1845179
theorem B19384109 : Blo 542804 19384109 := bstep (se 3 (by rfl) ⟨3634520, by rfl⟩ : syracuseStep 19384109 = 7269041) B7269041
theorem B1034041 : Blo 542804 1034041 := bstep (se 2 (by rfl) ⟨387765, by rfl⟩ : syracuseStep 1034041 = 775531) B775531
theorem B1034345 : Blo 542804 1034345 := bstep (se 2 (by rfl) ⟨387879, by rfl⟩ : syracuseStep 1034345 = 775759) B775759
theorem B543007 : Blo 542804 543007 := bstep (se 1 (by rfl) ⟨407255, by rfl⟩ : syracuseStep 543007 = 814511) B814511
theorem B543067 : Blo 542804 543067 := bstep (se 1 (by rfl) ⟨407300, by rfl⟩ : syracuseStep 543067 = 814601) B814601
theorem B543087 : Blo 542804 543087 := bstep (se 1 (by rfl) ⟨407315, by rfl⟩ : syracuseStep 543087 = 814631) B814631
theorem B543143 : Blo 542804 543143 := bstep (se 1 (by rfl) ⟨407357, by rfl⟩ : syracuseStep 543143 = 814715) B814715
theorem B543227 : Blo 542804 543227 := bstep (se 1 (by rfl) ⟨407420, by rfl⟩ : syracuseStep 543227 = 814841) B814841
theorem B543295 : Blo 542804 543295 := bstep (se 1 (by rfl) ⟨407471, by rfl⟩ : syracuseStep 543295 = 814943) B814943
theorem B543303 : Blo 542804 543303 := bstep (se 1 (by rfl) ⟨407477, by rfl⟩ : syracuseStep 543303 = 814955) B814955
theorem B3983959 : Blo 542804 3983959 := bstep (se 1 (by rfl) ⟨2987969, by rfl⟩ : syracuseStep 3983959 = 5975939) B5975939
theorem B543455 : Blo 542804 543455 := bstep (se 1 (by rfl) ⟨407591, by rfl⟩ : syracuseStep 543455 = 815183) B815183
theorem B5655329 : Blo 542804 5655329 := bstep (se 2 (by rfl) ⟨2120748, by rfl⟩ : syracuseStep 5655329 = 4241497) B4241497
theorem B543535 : Blo 542804 543535 := bstep (se 1 (by rfl) ⟨407651, by rfl⟩ : syracuseStep 543535 = 815303) B815303
theorem B543643 : Blo 542804 543643 := bstep (se 1 (by rfl) ⟨407732, by rfl⟩ : syracuseStep 543643 = 815465) B815465
theorem B543695 : Blo 542804 543695 := bstep (se 1 (by rfl) ⟨407771, by rfl⟩ : syracuseStep 543695 = 815543) B815543
theorem B543719 : Blo 542804 543719 := bstep (se 1 (by rfl) ⟨407789, by rfl⟩ : syracuseStep 543719 = 815579) B815579
theorem B544031 : Blo 542804 544031 := bstep (se 1 (by rfl) ⟨408023, by rfl⟩ : syracuseStep 544031 = 816047) B816047
theorem B544091 : Blo 542804 544091 := bstep (se 1 (by rfl) ⟨408068, by rfl⟩ : syracuseStep 544091 = 816137) B816137
theorem B544111 : Blo 542804 544111 := bstep (se 1 (by rfl) ⟨408083, by rfl⟩ : syracuseStep 544111 = 816167) B816167
theorem B544167 : Blo 542804 544167 := bstep (se 1 (by rfl) ⟨408125, by rfl⟩ : syracuseStep 544167 = 816251) B816251
theorem B544251 : Blo 542804 544251 := bstep (se 1 (by rfl) ⟨408188, by rfl⟩ : syracuseStep 544251 = 816377) B816377
theorem B544319 : Blo 542804 544319 := bstep (se 1 (by rfl) ⟨408239, by rfl⟩ : syracuseStep 544319 = 816479) B816479
theorem B544327 : Blo 542804 544327 := bstep (se 1 (by rfl) ⟨408245, by rfl⟩ : syracuseStep 544327 = 816491) B816491
theorem B544479 : Blo 542804 544479 := bstep (se 1 (by rfl) ⟨408359, by rfl⟩ : syracuseStep 544479 = 816719) B816719
theorem B1101547 : Blo 542804 1101547 := bstep (se 1 (by rfl) ⟨826160, by rfl⟩ : syracuseStep 1101547 = 1652321) B1652321
theorem B544559 : Blo 542804 544559 := bstep (se 1 (by rfl) ⟨408419, by rfl⟩ : syracuseStep 544559 = 816839) B816839
theorem B544667 : Blo 542804 544667 := bstep (se 1 (by rfl) ⟨408500, by rfl⟩ : syracuseStep 544667 = 817001) B817001
theorem B1101775 : Blo 542804 1101775 := bstep (se 1 (by rfl) ⟨826331, by rfl⟩ : syracuseStep 1101775 = 1652663) B1652663
theorem B544719 : Blo 542804 544719 := bstep (se 1 (by rfl) ⟨408539, by rfl⟩ : syracuseStep 544719 = 817079) B817079
theorem B544743 : Blo 542804 544743 := bstep (se 1 (by rfl) ⟨408557, by rfl⟩ : syracuseStep 544743 = 817115) B817115
theorem B5361665 : Blo 542804 5361665 := bstep (se 2 (by rfl) ⟨2010624, by rfl⟩ : syracuseStep 5361665 = 4021249) B4021249
theorem B545055 : Blo 542804 545055 := bstep (se 1 (by rfl) ⟨408791, by rfl⟩ : syracuseStep 545055 = 817583) B817583
theorem B545115 : Blo 542804 545115 := bstep (se 1 (by rfl) ⟨408836, by rfl⟩ : syracuseStep 545115 = 817673) B817673
theorem B15749477 : Blo 542804 15749477 := bstep (se 4 (by rfl) ⟨1476513, by rfl⟩ : syracuseStep 15749477 = 2953027) B2953027
theorem B545135 : Blo 542804 545135 := bstep (se 1 (by rfl) ⟨408851, by rfl⟩ : syracuseStep 545135 = 817703) B817703
theorem B545191 : Blo 542804 545191 := bstep (se 1 (by rfl) ⟨408893, by rfl⟩ : syracuseStep 545191 = 817787) B817787
theorem B545275 : Blo 542804 545275 := bstep (se 1 (by rfl) ⟨408956, by rfl⟩ : syracuseStep 545275 = 817913) B817913
theorem B610879 : Blo 542804 610879 := bstep (se 1 (by rfl) ⟨458159, by rfl⟩ : syracuseStep 610879 = 916319) B916319
theorem B873023 : Blo 542804 873023 := bstep (se 1 (by rfl) ⟨654767, by rfl⟩ : syracuseStep 873023 = 1309535) B1309535
theorem B545343 : Blo 542804 545343 := bstep (se 1 (by rfl) ⟨409007, by rfl⟩ : syracuseStep 545343 = 818015) B818015
theorem B545351 : Blo 542804 545351 := bstep (se 1 (by rfl) ⟨409013, by rfl⟩ : syracuseStep 545351 = 818027) B818027
theorem B545503 : Blo 542804 545503 := bstep (se 1 (by rfl) ⟨409127, by rfl⟩ : syracuseStep 545503 = 818255) B818255
theorem B545583 : Blo 542804 545583 := bstep (se 1 (by rfl) ⟨409187, by rfl⟩ : syracuseStep 545583 = 818375) B818375
theorem B3494735 : Blo 542804 3494735 := bstep (se 1 (by rfl) ⟨2621051, by rfl⟩ : syracuseStep 3494735 = 5242103) B5242103
theorem B545691 : Blo 542804 545691 := bstep (se 1 (by rfl) ⟨409268, by rfl⟩ : syracuseStep 545691 = 818537) B818537
theorem B545743 : Blo 542804 545743 := bstep (se 1 (by rfl) ⟨409307, by rfl⟩ : syracuseStep 545743 = 818615) B818615
theorem B545767 : Blo 542804 545767 := bstep (se 1 (by rfl) ⟨409325, by rfl⟩ : syracuseStep 545767 = 818651) B818651
theorem B546079 : Blo 542804 546079 := bstep (se 1 (by rfl) ⟨409559, by rfl⟩ : syracuseStep 546079 = 819119) B819119
theorem B873767 : Blo 542804 873767 := bstep (se 1 (by rfl) ⟨655325, by rfl⟩ : syracuseStep 873767 = 1310651) B1310651
theorem B546139 : Blo 542804 546139 := bstep (se 1 (by rfl) ⟨409604, by rfl⟩ : syracuseStep 546139 = 819209) B819209
theorem B546159 : Blo 542804 546159 := bstep (se 1 (by rfl) ⟨409619, by rfl⟩ : syracuseStep 546159 = 819239) B819239
theorem B611707 : Blo 542804 611707 := bstep (se 1 (by rfl) ⟨458780, by rfl⟩ : syracuseStep 611707 = 917561) B917561
theorem B4642181 : Blo 542804 4642181 := bstep (se 4 (by rfl) ⟨435204, by rfl⟩ : syracuseStep 4642181 = 870409) B870409
theorem B546215 : Blo 542804 546215 := bstep (se 1 (by rfl) ⟨409661, by rfl⟩ : syracuseStep 546215 = 819323) B819323
theorem B546299 : Blo 542804 546299 := bstep (se 1 (by rfl) ⟨409724, by rfl⟩ : syracuseStep 546299 = 819449) B819449
theorem B546367 : Blo 542804 546367 := bstep (se 1 (by rfl) ⟨409775, by rfl⟩ : syracuseStep 546367 = 819551) B819551
theorem B546375 : Blo 542804 546375 := bstep (se 1 (by rfl) ⟨409781, by rfl⟩ : syracuseStep 546375 = 819563) B819563
theorem B546527 : Blo 542804 546527 := bstep (se 1 (by rfl) ⟨409895, by rfl⟩ : syracuseStep 546527 = 819791) B819791
theorem B546607 : Blo 542804 546607 := bstep (se 1 (by rfl) ⟨409955, by rfl⟩ : syracuseStep 546607 = 819911) B819911
theorem B612175 : Blo 542804 612175 := bstep (se 1 (by rfl) ⟨459131, by rfl⟩ : syracuseStep 612175 = 918263) B918263
theorem B546715 : Blo 542804 546715 := bstep (se 1 (by rfl) ⟨410036, by rfl⟩ : syracuseStep 546715 = 820073) B820073
theorem B546767 : Blo 542804 546767 := bstep (se 1 (by rfl) ⟨410075, by rfl⟩ : syracuseStep 546767 = 820151) B820151
theorem B546791 : Blo 542804 546791 := bstep (se 1 (by rfl) ⟨410093, by rfl⟩ : syracuseStep 546791 = 820187) B820187
theorem B2480161 : Blo 542804 2480161 := bstep (se 2 (by rfl) ⟨930060, by rfl⟩ : syracuseStep 2480161 = 1860121) B1860121
theorem B579803 : Blo 542804 579803 := bstep (se 1 (by rfl) ⟨434852, by rfl⟩ : syracuseStep 579803 = 869705) B869705
theorem B612571 : Blo 542804 612571 := bstep (se 1 (by rfl) ⟨459428, by rfl⟩ : syracuseStep 612571 = 918857) B918857
theorem B2480381 : Blo 542804 2480381 := bstep (se 3 (by rfl) ⟨465071, by rfl⟩ : syracuseStep 2480381 = 930143) B930143
theorem B612859 : Blo 542804 612859 := bstep (se 1 (by rfl) ⟨459644, by rfl⟩ : syracuseStep 612859 = 919289) B919289
theorem B5593625 : Blo 542804 5593625 := bstep (se 2 (by rfl) ⟨2097609, by rfl⟩ : syracuseStep 5593625 = 4195219) B4195219
theorem B3922607 : Blo 542804 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B613039 : Blo 542804 613039 := bstep (se 1 (by rfl) ⟨459779, by rfl⟩ : syracuseStep 613039 = 919559) B919559
theorem B613327 : Blo 542804 613327 := bstep (se 1 (by rfl) ⟨459995, by rfl⟩ : syracuseStep 613327 = 919991) B919991
theorem B4643891 : Blo 542804 4643891 := bstep (se 1 (by rfl) ⟨3482918, by rfl⟩ : syracuseStep 4643891 = 6965837) B6965837
theorem B613723 : Blo 542804 613723 := bstep (se 1 (by rfl) ⟨460292, by rfl⟩ : syracuseStep 613723 = 920585) B920585
theorem B613831 : Blo 542804 613831 := bstep (se 1 (by rfl) ⟨460373, by rfl⟩ : syracuseStep 613831 = 920747) B920747
theorem B2481623 : Blo 542804 2481623 := bstep (se 1 (by rfl) ⟨1861217, by rfl⟩ : syracuseStep 2481623 = 3722435) B3722435
theorem B614191 : Blo 542804 614191 := bstep (se 1 (by rfl) ⟨460643, by rfl⟩ : syracuseStep 614191 = 921287) B921287
theorem B614299 : Blo 542804 614299 := bstep (se 1 (by rfl) ⟨460724, by rfl⟩ : syracuseStep 614299 = 921449) B921449
theorem B614695 : Blo 542804 614695 := bstep (se 1 (by rfl) ⟨461021, by rfl⟩ : syracuseStep 614695 = 922043) B922043
theorem B2318665 : Blo 542804 2318665 := bstep (se 2 (by rfl) ⟨869499, by rfl⟩ : syracuseStep 2318665 = 1738999) B1738999
theorem B2318699 : Blo 542804 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B614767 : Blo 542804 614767 := bstep (se 1 (by rfl) ⟨461075, by rfl⟩ : syracuseStep 614767 = 922151) B922151
theorem B614983 : Blo 542804 614983 := bstep (se 1 (by rfl) ⟨461237, by rfl⟩ : syracuseStep 614983 = 922475) B922475
theorem B582319 : Blo 542804 582319 := bstep (se 1 (by rfl) ⟨436739, by rfl⟩ : syracuseStep 582319 = 873479) B873479
theorem B2319299 : Blo 542804 2319299 := bstep (se 1 (by rfl) ⟨1739474, by rfl⟩ : syracuseStep 2319299 = 3478949) B3478949
theorem B8512705 : Blo 542804 8512705 := bstep (se 2 (by rfl) ⟨3192264, by rfl⟩ : syracuseStep 8512705 = 6384529) B6384529
theorem B1304999 : Blo 542804 1304999 := bstep (se 1 (by rfl) ⟨978749, by rfl⟩ : syracuseStep 1304999 = 1957499) B1957499
theorem B1239479 : Blo 542804 1239479 := bstep (se 1 (by rfl) ⟨929609, by rfl⟩ : syracuseStep 1239479 = 1859219) B1859219
theorem B17885731 : Blo 542804 17885731 := bstep (se 1 (by rfl) ⟨13414298, by rfl⟩ : syracuseStep 17885731 = 26828597) B26828597
theorem B4123223 : Blo 542804 4123223 := bstep (se 1 (by rfl) ⟨3092417, by rfl⟩ : syracuseStep 4123223 = 6184835) B6184835
theorem B5106349 : Blo 542804 5106349 := bstep (se 3 (by rfl) ⟨957440, by rfl⟩ : syracuseStep 5106349 = 1914881) B1914881
theorem B11168441 : Blo 542804 11168441 := bstep (se 2 (by rfl) ⟨4188165, by rfl⟩ : syracuseStep 11168441 = 8376331) B8376331
theorem B2616131 : Blo 542804 2616131 := bstep (se 1 (by rfl) ⟨1962098, by rfl⟩ : syracuseStep 2616131 = 3924197) B3924197
theorem B2943863 : Blo 542804 2943863 := bstep (se 1 (by rfl) ⟨2207897, by rfl⟩ : syracuseStep 2943863 = 4415795) B4415795
theorem B1305499 : Blo 542804 1305499 := bstep (se 1 (by rfl) ⟨979124, by rfl⟩ : syracuseStep 1305499 = 1958249) B1958249
theorem B814313 : Blo 542804 814313 := bstep (se 2 (by rfl) ⟨305367, by rfl⟩ : syracuseStep 814313 = 610735) B610735
theorem B814367 : Blo 542804 814367 := bstep (se 1 (by rfl) ⟨610775, by rfl⟩ : syracuseStep 814367 = 1221551) B1221551
theorem B2682179 : Blo 542804 2682179 := bstep (se 1 (by rfl) ⟨2011634, by rfl⟩ : syracuseStep 2682179 = 4023269) B4023269
theorem B2485633 : Blo 542804 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B814535 : Blo 542804 814535 := bstep (se 1 (by rfl) ⟨610901, by rfl⟩ : syracuseStep 814535 = 1221803) B1221803
theorem B42430169 : Blo 542804 42430169 := bstep (se 2 (by rfl) ⟨15911313, by rfl⟩ : syracuseStep 42430169 = 31822627) B31822627
theorem B2748167 : Blo 542804 2748167 := bstep (se 1 (by rfl) ⟨2061125, by rfl⟩ : syracuseStep 2748167 = 4122251) B4122251
theorem B814889 : Blo 542804 814889 := bstep (se 2 (by rfl) ⟨305583, by rfl⟩ : syracuseStep 814889 = 611167) B611167
theorem B814895 : Blo 542804 814895 := bstep (se 1 (by rfl) ⟨611171, by rfl⟩ : syracuseStep 814895 = 1222343) B1222343
theorem B978743 : Blo 542804 978743 := bstep (se 1 (by rfl) ⟨734057, by rfl⟩ : syracuseStep 978743 = 1468115) B1468115
theorem B2355119 : Blo 542804 2355119 := bstep (se 1 (by rfl) ⟨1766339, by rfl⟩ : syracuseStep 2355119 = 3532679) B3532679
theorem B1306729 : Blo 542804 1306729 := bstep (se 2 (by rfl) ⟨490023, by rfl⟩ : syracuseStep 1306729 = 980047) B980047
theorem B815369 : Blo 542804 815369 := bstep (se 2 (by rfl) ⟨305763, by rfl⟩ : syracuseStep 815369 = 611527) B611527
theorem B815471 : Blo 542804 815471 := bstep (se 1 (by rfl) ⟨611603, by rfl⟩ : syracuseStep 815471 = 1223207) B1223207
theorem B815687 : Blo 542804 815687 := bstep (se 1 (by rfl) ⟨611765, by rfl⟩ : syracuseStep 815687 = 1223531) B1223531
theorem B815723 : Blo 542804 815723 := bstep (se 1 (by rfl) ⟨611792, by rfl⟩ : syracuseStep 815723 = 1223585) B1223585
theorem B1471151 : Blo 542804 1471151 := bstep (se 1 (by rfl) ⟨1103363, by rfl⟩ : syracuseStep 1471151 = 2206727) B2206727
theorem B1077943 : Blo 542804 1077943 := bstep (se 1 (by rfl) ⟨808457, by rfl⟩ : syracuseStep 1077943 = 1616915) B1616915
theorem B815951 : Blo 542804 815951 := bstep (se 1 (by rfl) ⟨611963, by rfl⟩ : syracuseStep 815951 = 1223927) B1223927
theorem B816347 : Blo 542804 816347 := bstep (se 1 (by rfl) ⟨612260, by rfl⟩ : syracuseStep 816347 = 1224521) B1224521
theorem B816521 : Blo 542804 816521 := bstep (se 2 (by rfl) ⟨306195, by rfl⟩ : syracuseStep 816521 = 612391) B612391
theorem B1832381 : Blo 542804 1832381 := bstep (se 3 (by rfl) ⟨343571, by rfl⟩ : syracuseStep 1832381 = 687143) B687143
theorem B9303497 : Blo 542804 9303497 := bstep (se 2 (by rfl) ⟨3488811, by rfl⟩ : syracuseStep 9303497 = 6977623) B6977623
theorem B816875 : Blo 542804 816875 := bstep (se 1 (by rfl) ⟨612656, by rfl⟩ : syracuseStep 816875 = 1225313) B1225313
theorem B1373993 : Blo 542804 1373993 := bstep (se 2 (by rfl) ⟨515247, by rfl⟩ : syracuseStep 1373993 = 1030495) B1030495
theorem B1832759 : Blo 542804 1832759 := bstep (se 1 (by rfl) ⟨1374569, by rfl⟩ : syracuseStep 1832759 = 2749139) B2749139
theorem B18708317 : Blo 542804 18708317 := bstep (se 3 (by rfl) ⟨3507809, by rfl⟩ : syracuseStep 18708317 = 7015619) B7015619
theorem B11761595 : Blo 542804 11761595 := bstep (se 1 (by rfl) ⟨8821196, by rfl⟩ : syracuseStep 11761595 = 17642393) B17642393
theorem B817103 : Blo 542804 817103 := bstep (se 1 (by rfl) ⟨612827, by rfl⟩ : syracuseStep 817103 = 1225655) B1225655
theorem B1833245 : Blo 542804 1833245 := bstep (se 3 (by rfl) ⟨343733, by rfl⟩ : syracuseStep 1833245 = 687467) B687467
theorem B817499 : Blo 542804 817499 := bstep (se 1 (by rfl) ⟨613124, by rfl⟩ : syracuseStep 817499 = 1226249) B1226249
theorem B2324987 : Blo 542804 2324987 := bstep (se 1 (by rfl) ⟨1743740, by rfl⟩ : syracuseStep 2324987 = 3487481) B3487481
theorem B817727 : Blo 542804 817727 := bstep (se 1 (by rfl) ⟨613295, by rfl⟩ : syracuseStep 817727 = 1226591) B1226591
theorem B981575 : Blo 542804 981575 := bstep (se 1 (by rfl) ⟨736181, by rfl⟩ : syracuseStep 981575 = 1472363) B1472363
theorem B2751083 : Blo 542804 2751083 := bstep (se 1 (by rfl) ⟨2063312, by rfl⟩ : syracuseStep 2751083 = 4126625) B4126625
theorem B817847 : Blo 542804 817847 := bstep (se 1 (by rfl) ⟨613385, by rfl⟩ : syracuseStep 817847 = 1226771) B1226771
theorem B1243831 : Blo 542804 1243831 := bstep (se 1 (by rfl) ⟨932873, by rfl⟩ : syracuseStep 1243831 = 1865747) B1865747
theorem B1374995 : Blo 542804 1374995 := bstep (se 1 (by rfl) ⟨1031246, by rfl⟩ : syracuseStep 1374995 = 2062493) B2062493
theorem B1309459 : Blo 542804 1309459 := bstep (se 1 (by rfl) ⟨982094, by rfl⟩ : syracuseStep 1309459 = 1964189) B1964189
theorem B818075 : Blo 542804 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B2751569 : Blo 542804 2751569 := bstep (se 2 (by rfl) ⟨1031838, by rfl⟩ : syracuseStep 2751569 = 2063677) B2063677
theorem B1375451 : Blo 542804 1375451 := bstep (se 1 (by rfl) ⟨1031588, by rfl⟩ : syracuseStep 1375451 = 2063177) B2063177
theorem B1375481 : Blo 542804 1375481 := bstep (se 2 (by rfl) ⟨515805, by rfl⟩ : syracuseStep 1375481 = 1031611) B1031611
theorem B1834271 : Blo 542804 1834271 := bstep (se 1 (by rfl) ⟨1375703, by rfl⟩ : syracuseStep 1834271 = 2751407) B2751407
theorem B818471 : Blo 542804 818471 := bstep (se 1 (by rfl) ⟨613853, by rfl⟩ : syracuseStep 818471 = 1227707) B1227707
theorem B916859 : Blo 542804 916859 := bstep (se 1 (by rfl) ⟨687644, by rfl⟩ : syracuseStep 916859 = 1375289) B1375289
theorem B818555 : Blo 542804 818555 := bstep (se 1 (by rfl) ⟨613916, by rfl⟩ : syracuseStep 818555 = 1227833) B1227833
theorem B818681 : Blo 542804 818681 := bstep (se 2 (by rfl) ⟨307005, by rfl⟩ : syracuseStep 818681 = 614011) B614011
theorem B4652639 : Blo 542804 4652639 := bstep (se 1 (by rfl) ⟨3489479, by rfl⟩ : syracuseStep 4652639 = 6978959) B6978959
theorem B818783 : Blo 542804 818783 := bstep (se 1 (by rfl) ⟨614087, by rfl⟩ : syracuseStep 818783 = 1228175) B1228175
theorem B2063981 : Blo 542804 2063981 := bstep (se 3 (by rfl) ⟨386996, by rfl⟩ : syracuseStep 2063981 = 773993) B773993
theorem B687791 : Blo 542804 687791 := bstep (se 1 (by rfl) ⟨515843, by rfl⟩ : syracuseStep 687791 = 1031687) B1031687
theorem B818999 : Blo 542804 818999 := bstep (se 1 (by rfl) ⟨614249, by rfl⟩ : syracuseStep 818999 = 1228499) B1228499
theorem B1376129 : Blo 542804 1376129 := bstep (se 2 (by rfl) ⟨516048, by rfl⟩ : syracuseStep 1376129 = 1032097) B1032097
theorem B1474699 : Blo 542804 1474699 := bstep (se 1 (by rfl) ⟨1106024, by rfl⟩ : syracuseStep 1474699 = 2212049) B2212049
theorem B917723 : Blo 542804 917723 := bstep (se 1 (by rfl) ⟨688292, by rfl⟩ : syracuseStep 917723 = 1376585) B1376585
theorem B819419 : Blo 542804 819419 := bstep (se 1 (by rfl) ⟨614564, by rfl⟩ : syracuseStep 819419 = 1229129) B1229129
theorem B819431 : Blo 542804 819431 := bstep (se 1 (by rfl) ⟨614573, by rfl⟩ : syracuseStep 819431 = 1229147) B1229147
theorem B688439 : Blo 542804 688439 := bstep (se 1 (by rfl) ⟨516329, by rfl⟩ : syracuseStep 688439 = 1032659) B1032659
theorem B819593 : Blo 542804 819593 := bstep (se 2 (by rfl) ⟨307347, by rfl⟩ : syracuseStep 819593 = 614695) B614695
theorem B6291863 : Blo 542804 6291863 := bstep (se 1 (by rfl) ⟨4718897, by rfl⟩ : syracuseStep 6291863 = 9437795) B9437795
theorem B6193583 : Blo 542804 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B2621879 : Blo 542804 2621879 := bstep (se 1 (by rfl) ⟨1966409, by rfl⟩ : syracuseStep 2621879 = 3932819) B3932819
theorem B1966523 : Blo 542804 1966523 := bstep (se 1 (by rfl) ⟨1474892, by rfl⟩ : syracuseStep 1966523 = 2949785) B2949785
theorem B917959 : Blo 542804 917959 := bstep (se 1 (by rfl) ⟨688469, by rfl⟩ : syracuseStep 917959 = 1376939) B1376939
theorem B688591 : Blo 542804 688591 := bstep (se 1 (by rfl) ⟨516443, by rfl⟩ : syracuseStep 688591 = 1032887) B1032887
theorem B3113423 : Blo 542804 3113423 := bstep (se 1 (by rfl) ⟨2335067, by rfl⟩ : syracuseStep 3113423 = 4670135) B4670135
theorem B917993 : Blo 542804 917993 := bstep (se 2 (by rfl) ⟨344247, by rfl⟩ : syracuseStep 917993 = 688495) B688495
theorem B819689 : Blo 542804 819689 := bstep (se 2 (by rfl) ⟨307383, by rfl⟩ : syracuseStep 819689 = 614767) B614767
theorem B3736115 : Blo 542804 3736115 := bstep (se 1 (by rfl) ⟨2802086, by rfl⟩ : syracuseStep 3736115 = 5604173) B5604173
theorem B819815 : Blo 542804 819815 := bstep (se 1 (by rfl) ⟨614861, by rfl⟩ : syracuseStep 819815 = 1229723) B1229723
theorem B819947 : Blo 542804 819947 := bstep (se 1 (by rfl) ⟨614960, by rfl⟩ : syracuseStep 819947 = 1229921) B1229921
theorem B1311497 : Blo 542804 1311497 := bstep (se 2 (by rfl) ⟨491811, by rfl⟩ : syracuseStep 1311497 = 983623) B983623
theorem B819977 : Blo 542804 819977 := bstep (se 2 (by rfl) ⟨307491, by rfl⟩ : syracuseStep 819977 = 614983) B614983
theorem B1377071 : Blo 542804 1377071 := bstep (se 1 (by rfl) ⟨1032803, by rfl⟩ : syracuseStep 1377071 = 2065607) B2065607
theorem B820079 : Blo 542804 820079 := bstep (se 1 (by rfl) ⟨615059, by rfl⟩ : syracuseStep 820079 = 1230119) B1230119
theorem B689563 : Blo 542804 689563 := bstep (se 1 (by rfl) ⟨517172, by rfl⟩ : syracuseStep 689563 = 1034345) B1034345
theorem B3770219 : Blo 542804 3770219 := bstep (se 1 (by rfl) ⟨2827664, by rfl⟩ : syracuseStep 3770219 = 5655329) B5655329
theorem B4786295 : Blo 542804 4786295 := bstep (se 1 (by rfl) ⟨3589721, by rfl⟩ : syracuseStep 4786295 = 7179443) B7179443
theorem B2754809 : Blo 542804 2754809 := bstep (se 2 (by rfl) ⟨1033053, by rfl⟩ : syracuseStep 2754809 = 2066107) B2066107
theorem B919849 : Blo 542804 919849 := bstep (se 2 (by rfl) ⟨344943, by rfl⟩ : syracuseStep 919849 = 689887) B689887
theorem B2951471 : Blo 542804 2951471 := bstep (se 1 (by rfl) ⟨2213603, by rfl⟩ : syracuseStep 2951471 = 4427207) B4427207
theorem B1837403 : Blo 542804 1837403 := bstep (se 1 (by rfl) ⟨1378052, by rfl⟩ : syracuseStep 1837403 = 2756105) B2756105
theorem B1378721 : Blo 542804 1378721 := bstep (se 2 (by rfl) ⟨517020, by rfl⟩ : syracuseStep 1378721 = 1034041) B1034041
theorem B1837673 : Blo 542804 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B1968745 : Blo 542804 1968745 := bstep (se 2 (by rfl) ⟨738279, by rfl⟩ : syracuseStep 1968745 = 1476559) B1476559
theorem B7441085 : Blo 542804 7441085 := bstep (se 3 (by rfl) ⟨1395203, by rfl⟩ : syracuseStep 7441085 = 2790407) B2790407
theorem B3935063 : Blo 542804 3935063 := bstep (se 1 (by rfl) ⟨2951297, by rfl⟩ : syracuseStep 3935063 = 5902595) B5902595
theorem B1379551 : Blo 542804 1379551 := bstep (se 1 (by rfl) ⟨1034663, by rfl⟩ : syracuseStep 1379551 = 2069327) B2069327
theorem B2329823 : Blo 542804 2329823 := bstep (se 1 (by rfl) ⟨1747367, by rfl⟩ : syracuseStep 2329823 = 3494735) B3494735
theorem B1379663 : Blo 542804 1379663 := bstep (se 1 (by rfl) ⟨1034747, by rfl⟩ : syracuseStep 1379663 = 2069495) B2069495
theorem B2330045 : Blo 542804 2330045 := bstep (se 3 (by rfl) ⟨436883, by rfl⟩ : syracuseStep 2330045 = 873767) B873767
theorem B5311945 : Blo 542804 5311945 := bstep (se 2 (by rfl) ⟨1991979, by rfl⟩ : syracuseStep 5311945 = 3983959) B3983959
theorem B6622715 : Blo 542804 6622715 := bstep (se 1 (by rfl) ⟨4967036, by rfl⟩ : syracuseStep 6622715 = 9934073) B9934073
theorem B921179 : Blo 542804 921179 := bstep (se 1 (by rfl) ⟨690884, by rfl⟩ : syracuseStep 921179 = 1381769) B1381769
theorem B1838699 : Blo 542804 1838699 := bstep (se 1 (by rfl) ⟨1379024, by rfl⟩ : syracuseStep 1838699 = 2758049) B2758049
theorem B921415 : Blo 542804 921415 := bstep (se 1 (by rfl) ⟨691061, by rfl⟩ : syracuseStep 921415 = 1382123) B1382123
theorem B1740665 : Blo 542804 1740665 := bstep (se 2 (by rfl) ⟨652749, by rfl⟩ : syracuseStep 1740665 = 1305499) B1305499
theorem B1838969 : Blo 542804 1838969 := bstep (se 2 (by rfl) ⟨689613, by rfl⟩ : syracuseStep 1838969 = 1379227) B1379227
theorem B1773535 : Blo 542804 1773535 := bstep (se 1 (by rfl) ⟨1330151, by rfl⟩ : syracuseStep 1773535 = 2660303) B2660303
theorem B2101229 : Blo 542804 2101229 := bstep (se 3 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 2101229 = 787961) B787961
theorem B1839293 : Blo 542804 1839293 := bstep (se 3 (by rfl) ⟨344867, by rfl⟩ : syracuseStep 1839293 = 689735) B689735
theorem B3936509 : Blo 542804 3936509 := bstep (se 3 (by rfl) ⟨738095, by rfl⟩ : syracuseStep 3936509 = 1476191) B1476191
theorem B922063 : Blo 542804 922063 := bstep (se 1 (by rfl) ⟨691547, by rfl⟩ : syracuseStep 922063 = 1383095) B1383095
theorem B3314177 : Blo 542804 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B7082497 : Blo 542804 7082497 := bstep (se 2 (by rfl) ⟨2655936, by rfl⟩ : syracuseStep 7082497 = 5311873) B5311873
theorem B1380959 : Blo 542804 1380959 := bstep (se 1 (by rfl) ⟨1035719, by rfl⟩ : syracuseStep 1380959 = 2071439) B2071439
theorem B2757401 : Blo 542804 2757401 := bstep (se 2 (by rfl) ⟨1034025, by rfl⟩ : syracuseStep 2757401 = 2068051) B2068051
theorem B3151057 : Blo 542804 3151057 := bstep (se 2 (by rfl) ⟨1181646, by rfl⟩ : syracuseStep 3151057 = 2363293) B2363293
theorem B1840481 : Blo 542804 1840481 := bstep (se 2 (by rfl) ⟨690180, by rfl⟩ : syracuseStep 1840481 = 1380361) B1380361
theorem B1742305 : Blo 542804 1742305 := bstep (se 2 (by rfl) ⟨653364, by rfl⟩ : syracuseStep 1742305 = 1306729) B1306729
theorem B14358059 : Blo 542804 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B1545799 : Blo 542804 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B1546141 : Blo 542804 1546141 := bstep (se 3 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 1546141 = 579803) B579803
theorem B1546199 : Blo 542804 1546199 := bstep (se 1 (by rfl) ⟨1159649, by rfl⟩ : syracuseStep 1546199 = 2319299) B2319299
theorem B9312245 : Blo 542804 9312245 := bstep (se 5 (by rfl) ⟨436511, by rfl⟩ : syracuseStep 9312245 = 873023) B873023
theorem B2758859 : Blo 542804 2758859 := bstep (se 1 (by rfl) ⟨2069144, by rfl⟩ : syracuseStep 2758859 = 4138289) B4138289
theorem B4659403 : Blo 542804 4659403 := bstep (se 1 (by rfl) ⟨3494552, by rfl⟩ : syracuseStep 4659403 = 6989105) B6989105
theorem B25237979 : Blo 542804 25237979 := bstep (se 1 (by rfl) ⟨18928484, by rfl⟩ : syracuseStep 25237979 = 37856969) B37856969
theorem B2759507 : Blo 542804 2759507 := bstep (se 1 (by rfl) ⟨2069630, by rfl⟩ : syracuseStep 2759507 = 4139261) B4139261
theorem B826319 : Blo 542804 826319 := bstep (se 1 (by rfl) ⟨619739, by rfl⟩ : syracuseStep 826319 = 1239479) B1239479
theorem B7445627 : Blo 542804 7445627 := bstep (se 1 (by rfl) ⟨5584220, by rfl⟩ : syracuseStep 7445627 = 11168441) B11168441
theorem B10460285 : Blo 542804 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B1744087 : Blo 542804 1744087 := bstep (se 1 (by rfl) ⟨1308065, by rfl⟩ : syracuseStep 1744087 = 2616131) B2616131
theorem B1842425 : Blo 542804 1842425 := bstep (se 2 (by rfl) ⟨690909, by rfl⟩ : syracuseStep 1842425 = 1381819) B1381819
theorem B1842695 : Blo 542804 1842695 := bstep (se 1 (by rfl) ⟨1382021, by rfl⟩ : syracuseStep 1842695 = 2764043) B2764043
theorem B28286779 : Blo 542804 28286779 := bstep (se 1 (by rfl) ⟨21215084, by rfl⟩ : syracuseStep 28286779 = 42430169) B42430169
theorem B3940487 : Blo 542804 3940487 := bstep (se 1 (by rfl) ⟨2955365, by rfl⟩ : syracuseStep 3940487 = 5910731) B5910731
theorem B1843775 : Blo 542804 1843775 := bstep (se 1 (by rfl) ⟨1382831, by rfl⟩ : syracuseStep 1843775 = 2765663) B2765663
theorem B2761289 : Blo 542804 2761289 := bstep (se 2 (by rfl) ⟨1035483, by rfl⟩ : syracuseStep 2761289 = 2070967) B2070967
theorem B1221587 : Blo 542804 1221587 := bstep (se 1 (by rfl) ⟨916190, by rfl⟩ : syracuseStep 1221587 = 1832381) B1832381
theorem B6202331 : Blo 542804 6202331 := bstep (se 1 (by rfl) ⟨4651748, by rfl⟩ : syracuseStep 6202331 = 9303497) B9303497
theorem B1745945 : Blo 542804 1745945 := bstep (se 2 (by rfl) ⟨654729, by rfl⟩ : syracuseStep 1745945 = 1309459) B1309459
theorem B1221839 : Blo 542804 1221839 := bstep (se 1 (by rfl) ⟨916379, by rfl⟩ : syracuseStep 1221839 = 1832759) B1832759
theorem B7841063 : Blo 542804 7841063 := bstep (se 1 (by rfl) ⟨5880797, by rfl⟩ : syracuseStep 7841063 = 11761595) B11761595
theorem B6300995 : Blo 542804 6300995 := bstep (se 1 (by rfl) ⟨4725746, by rfl⟩ : syracuseStep 6300995 = 9451493) B9451493
theorem B1222163 : Blo 542804 1222163 := bstep (se 1 (by rfl) ⟨916622, by rfl⟩ : syracuseStep 1222163 = 1833245) B1833245
theorem B1549945 : Blo 542804 1549945 := bstep (se 2 (by rfl) ⟨581229, by rfl⟩ : syracuseStep 1549945 = 1162459) B1162459
theorem B1549991 : Blo 542804 1549991 := bstep (se 1 (by rfl) ⟨1162493, by rfl⟩ : syracuseStep 1549991 = 2324987) B2324987
theorem B1845071 : Blo 542804 1845071 := bstep (se 1 (by rfl) ⟨1383803, by rfl⟩ : syracuseStep 1845071 = 2767607) B2767607
theorem B1845395 : Blo 542804 1845395 := bstep (se 1 (by rfl) ⟨1384046, by rfl⟩ : syracuseStep 1845395 = 2768093) B2768093
theorem B1222847 : Blo 542804 1222847 := bstep (se 1 (by rfl) ⟨917135, by rfl⟩ : syracuseStep 1222847 = 1834271) B1834271
theorem B57191093 : Blo 542804 57191093 := bstep (se 5 (by rfl) ⟨2680832, by rfl⟩ : syracuseStep 57191093 = 5361665) B5361665
theorem B3484559 : Blo 542804 3484559 := bstep (se 1 (by rfl) ⟨2613419, by rfl⟩ : syracuseStep 3484559 = 5226839) B5226839
theorem B4729903 : Blo 542804 4729903 := bstep (se 1 (by rfl) ⟨3547427, by rfl⟩ : syracuseStep 4729903 = 7094855) B7094855
theorem B3091553 : Blo 542804 3091553 := bstep (se 2 (by rfl) ⟨1159332, by rfl⟩ : syracuseStep 3091553 = 2318665) B2318665
theorem B1223801 : Blo 542804 1223801 := bstep (se 2 (by rfl) ⟨458925, by rfl⟩ : syracuseStep 1223801 = 917851) B917851
theorem B830831 : Blo 542804 830831 := bstep (se 1 (by rfl) ⟨623123, by rfl⟩ : syracuseStep 830831 = 1246247) B1246247
theorem B1224467 : Blo 542804 1224467 := bstep (se 1 (by rfl) ⟨918350, by rfl⟩ : syracuseStep 1224467 = 1836701) B1836701
theorem B12922739 : Blo 542804 12922739 := bstep (se 1 (by rfl) ⟨9692054, by rfl⟩ : syracuseStep 12922739 = 19384109) B19384109
theorem B1224827 : Blo 542804 1224827 := bstep (se 1 (by rfl) ⟨918620, by rfl⟩ : syracuseStep 1224827 = 1837241) B1837241
theorem B11350273 : Blo 542804 11350273 := bstep (se 2 (by rfl) ⟨4256352, by rfl⟩ : syracuseStep 11350273 = 8512705) B8512705
theorem B1225097 : Blo 542804 1225097 := bstep (se 2 (by rfl) ⟨459411, by rfl⟩ : syracuseStep 1225097 = 918823) B918823
theorem B1225835 : Blo 542804 1225835 := bstep (se 1 (by rfl) ⟨919376, by rfl⟩ : syracuseStep 1225835 = 1838753) B1838753
theorem B10499651 : Blo 542804 10499651 := bstep (se 1 (by rfl) ⟨7874738, by rfl⟩ : syracuseStep 10499651 = 15749477) B15749477
theorem B1226411 : Blo 542804 1226411 := bstep (se 1 (by rfl) ⟨919808, by rfl⟩ : syracuseStep 1226411 = 1839617) B1839617
theorem B1160887 : Blo 542804 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B3979145 : Blo 542804 3979145 := bstep (se 2 (by rfl) ⟨1492179, by rfl⟩ : syracuseStep 3979145 = 2984359) B2984359
theorem B1226735 : Blo 542804 1226735 := bstep (se 1 (by rfl) ⟨920051, by rfl⟩ : syracuseStep 1226735 = 1840103) B1840103
theorem B1226951 : Blo 542804 1226951 := bstep (se 1 (by rfl) ⟨920213, by rfl⟩ : syracuseStep 1226951 = 1840427) B1840427
theorem B3094787 : Blo 542804 3094787 := bstep (se 1 (by rfl) ⟨2321090, by rfl⟩ : syracuseStep 3094787 = 4642181) B4642181
theorem B1227131 : Blo 542804 1227131 := bstep (se 1 (by rfl) ⟨920348, by rfl⟩ : syracuseStep 1227131 = 1840697) B1840697
theorem B9320993 : Blo 542804 9320993 := bstep (se 2 (by rfl) ⟨3495372, by rfl⟩ : syracuseStep 9320993 = 6990745) B6990745
theorem B1227401 : Blo 542804 1227401 := bstep (se 2 (by rfl) ⟨460275, by rfl⟩ : syracuseStep 1227401 = 920551) B920551
theorem B1653587 : Blo 542804 1653587 := bstep (se 1 (by rfl) ⟨1240190, by rfl⟩ : syracuseStep 1653587 = 2480381) B2480381
theorem B6732953 : Blo 542804 6732953 := bstep (se 2 (by rfl) ⟨2524857, by rfl⟩ : syracuseStep 6732953 = 5049715) B5049715
theorem B1227959 : Blo 542804 1227959 := bstep (se 1 (by rfl) ⟨920969, by rfl⟩ : syracuseStep 1227959 = 1841939) B1841939
theorem B1555823 : Blo 542804 1555823 := bstep (se 1 (by rfl) ⟨1166867, by rfl⟩ : syracuseStep 1555823 = 2333735) B2333735
theorem B3095927 : Blo 542804 3095927 := bstep (se 1 (by rfl) ⟨2321945, by rfl⟩ : syracuseStep 3095927 = 4643891) B4643891
theorem B1031771 : Blo 542804 1031771 := bstep (se 1 (by rfl) ⟨773828, by rfl⟩ : syracuseStep 1031771 = 1547657) B1547657
theorem B1654415 : Blo 542804 1654415 := bstep (se 1 (by rfl) ⟨1240811, by rfl⟩ : syracuseStep 1654415 = 2481623) B2481623
theorem B1228535 : Blo 542804 1228535 := bstep (se 1 (by rfl) ⟨921401, by rfl⟩ : syracuseStep 1228535 = 1842803) B1842803
theorem B1556279 : Blo 542804 1556279 := bstep (se 1 (by rfl) ⟨1167209, by rfl⟩ : syracuseStep 1556279 = 2334419) B2334419
theorem B1556347 : Blo 542804 1556347 := bstep (se 1 (by rfl) ⟨1167260, by rfl⟩ : syracuseStep 1556347 = 2334521) B2334521
theorem B1228715 : Blo 542804 1228715 := bstep (se 1 (by rfl) ⟨921536, by rfl⟩ : syracuseStep 1228715 = 1843073) B1843073
theorem B7979147 : Blo 542804 7979147 := bstep (se 1 (by rfl) ⟨5984360, by rfl⟩ : syracuseStep 7979147 = 11968721) B11968721
theorem B1229255 : Blo 542804 1229255 := bstep (se 1 (by rfl) ⟨921941, by rfl⟩ : syracuseStep 1229255 = 1843883) B1843883
theorem B21283337 : Blo 542804 21283337 := bstep (se 2 (by rfl) ⟨7981251, by rfl⟩ : syracuseStep 21283337 = 15962503) B15962503
theorem B1229615 : Blo 542804 1229615 := bstep (se 1 (by rfl) ⟨922211, by rfl⟩ : syracuseStep 1229615 = 1844423) B1844423
theorem B4178807 : Blo 542804 4178807 := bstep (se 1 (by rfl) ⟨3134105, by rfl⟩ : syracuseStep 4178807 = 6268211) B6268211
theorem B3818753 : Blo 542804 3818753 := bstep (se 2 (by rfl) ⟨1432032, by rfl⟩ : syracuseStep 3818753 = 2864065) B2864065
theorem B869999 : Blo 542804 869999 := bstep (se 1 (by rfl) ⟨652499, by rfl⟩ : syracuseStep 869999 = 1304999) B1304999
theorem B542875 : Blo 542804 542875 := bstep (se 1 (by rfl) ⟨407156, by rfl⟩ : syracuseStep 542875 = 814313) B814313
theorem B542911 : Blo 542804 542911 := bstep (se 1 (by rfl) ⟨407183, by rfl⟩ : syracuseStep 542911 = 814367) B814367
theorem B1788119 : Blo 542804 1788119 := bstep (se 1 (by rfl) ⟨1341089, by rfl⟩ : syracuseStep 1788119 = 2682179) B2682179
theorem B543023 : Blo 542804 543023 := bstep (se 1 (by rfl) ⟨407267, by rfl⟩ : syracuseStep 543023 = 814535) B814535
theorem B543259 : Blo 542804 543259 := bstep (se 1 (by rfl) ⟨407444, by rfl⟩ : syracuseStep 543259 = 814889) B814889
theorem B543263 : Blo 542804 543263 := bstep (se 1 (by rfl) ⟨407447, by rfl⟩ : syracuseStep 543263 = 814895) B814895
theorem B543579 : Blo 542804 543579 := bstep (se 1 (by rfl) ⟨407684, by rfl⟩ : syracuseStep 543579 = 815369) B815369
theorem B543647 : Blo 542804 543647 := bstep (se 1 (by rfl) ⟨407735, by rfl⟩ : syracuseStep 543647 = 815471) B815471
theorem B2804711 : Blo 542804 2804711 := bstep (se 1 (by rfl) ⟨2103533, by rfl⟩ : syracuseStep 2804711 = 4207067) B4207067
theorem B543791 : Blo 542804 543791 := bstep (se 1 (by rfl) ⟨407843, by rfl⟩ : syracuseStep 543791 = 815687) B815687
theorem B543815 : Blo 542804 543815 := bstep (se 1 (by rfl) ⟨407861, by rfl⟩ : syracuseStep 543815 = 815723) B815723
theorem B543967 : Blo 542804 543967 := bstep (se 1 (by rfl) ⟨407975, by rfl⟩ : syracuseStep 543967 = 815951) B815951
theorem B544231 : Blo 542804 544231 := bstep (se 1 (by rfl) ⟨408173, by rfl⟩ : syracuseStep 544231 = 816347) B816347
theorem B4640267 : Blo 542804 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B1658441 : Blo 542804 1658441 := bstep (se 2 (by rfl) ⟨621915, by rfl⟩ : syracuseStep 1658441 = 1243831) B1243831
theorem B544347 : Blo 542804 544347 := bstep (se 1 (by rfl) ⟨408260, by rfl⟩ : syracuseStep 544347 = 816521) B816521
theorem B544583 : Blo 542804 544583 := bstep (se 1 (by rfl) ⟨408437, by rfl⟩ : syracuseStep 544583 = 816875) B816875
theorem B2936681 : Blo 542804 2936681 := bstep (se 2 (by rfl) ⟨1101255, by rfl⟩ : syracuseStep 2936681 = 2202511) B2202511
theorem B12472211 : Blo 542804 12472211 := bstep (se 1 (by rfl) ⟨9354158, by rfl⟩ : syracuseStep 12472211 = 18708317) B18708317
theorem B544735 : Blo 542804 544735 := bstep (se 1 (by rfl) ⟨408551, by rfl⟩ : syracuseStep 544735 = 817103) B817103
theorem B544999 : Blo 542804 544999 := bstep (se 1 (by rfl) ⟨408749, by rfl⟩ : syracuseStep 544999 = 817499) B817499
theorem B1167671 : Blo 542804 1167671 := bstep (se 1 (by rfl) ⟨875753, by rfl⟩ : syracuseStep 1167671 = 1751507) B1751507
theorem B545151 : Blo 542804 545151 := bstep (se 1 (by rfl) ⟨408863, by rfl⟩ : syracuseStep 545151 = 817727) B817727
theorem B545231 : Blo 542804 545231 := bstep (se 1 (by rfl) ⟨408923, by rfl⟩ : syracuseStep 545231 = 817847) B817847
theorem B545383 : Blo 542804 545383 := bstep (se 1 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 545383 = 818075) B818075
theorem B3920507 : Blo 542804 3920507 := bstep (se 1 (by rfl) ⟨2940380, by rfl⟩ : syracuseStep 3920507 = 5880761) B5880761
theorem B1037063 : Blo 542804 1037063 := bstep (se 1 (by rfl) ⟨777797, by rfl⟩ : syracuseStep 1037063 = 1555595) B1555595
theorem B2609981 : Blo 542804 2609981 := bstep (se 3 (by rfl) ⟨489371, by rfl⟩ : syracuseStep 2609981 = 978743) B978743
theorem B545647 : Blo 542804 545647 := bstep (se 1 (by rfl) ⟨409235, by rfl⟩ : syracuseStep 545647 = 818471) B818471
theorem B611239 : Blo 542804 611239 := bstep (se 1 (by rfl) ⟨458429, by rfl⟩ : syracuseStep 611239 = 916859) B916859
theorem B545703 : Blo 542804 545703 := bstep (se 1 (by rfl) ⟨409277, by rfl⟩ : syracuseStep 545703 = 818555) B818555
theorem B545787 : Blo 542804 545787 := bstep (se 1 (by rfl) ⟨409340, by rfl⟩ : syracuseStep 545787 = 818681) B818681
theorem B3101759 : Blo 542804 3101759 := bstep (se 1 (by rfl) ⟨2326319, by rfl⟩ : syracuseStep 3101759 = 4652639) B4652639
theorem B545855 : Blo 542804 545855 := bstep (se 1 (by rfl) ⟨409391, by rfl⟩ : syracuseStep 545855 = 818783) B818783
theorem B545999 : Blo 542804 545999 := bstep (se 1 (by rfl) ⟨409499, by rfl⟩ : syracuseStep 545999 = 818999) B818999
theorem B13391243 : Blo 542804 13391243 := bstep (se 1 (by rfl) ⟨10043432, by rfl⟩ : syracuseStep 13391243 = 20086865) B20086865
theorem B546203 : Blo 542804 546203 := bstep (se 1 (by rfl) ⟨409652, by rfl⟩ : syracuseStep 546203 = 819305) B819305
theorem B546415 : Blo 542804 546415 := bstep (se 1 (by rfl) ⟨409811, by rfl⟩ : syracuseStep 546415 = 819623) B819623
theorem B546471 : Blo 542804 546471 := bstep (se 1 (by rfl) ⟨409853, by rfl⟩ : syracuseStep 546471 = 819707) B819707
theorem B15652601 : Blo 542804 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B546555 : Blo 542804 546555 := bstep (se 1 (by rfl) ⟨409916, by rfl⟩ : syracuseStep 546555 = 819833) B819833
theorem B6215453 : Blo 542804 6215453 := bstep (se 3 (by rfl) ⟨1165397, by rfl⟩ : syracuseStep 6215453 = 2330795) B2330795
theorem B546591 : Blo 542804 546591 := bstep (se 1 (by rfl) ⟨409943, by rfl⟩ : syracuseStep 546591 = 819887) B819887
theorem B294508331 : Blo 542804 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B546623 : Blo 542804 546623 := bstep (se 1 (by rfl) ⟨409967, by rfl⟩ : syracuseStep 546623 = 819935) B819935
theorem B1103753 : Blo 542804 1103753 := bstep (se 2 (by rfl) ⟨413907, by rfl⟩ : syracuseStep 1103753 = 827815) B827815
theorem B546799 : Blo 542804 546799 := bstep (se 1 (by rfl) ⟨410099, by rfl⟩ : syracuseStep 546799 = 820199) B820199
theorem B612895 : Blo 542804 612895 := bstep (se 1 (by rfl) ⟨459671, by rfl⟩ : syracuseStep 612895 = 919343) B919343
theorem B4151897 : Blo 542804 4151897 := bstep (se 2 (by rfl) ⟨1556961, by rfl⟩ : syracuseStep 4151897 = 3113923) B3113923
theorem B11819641 : Blo 542804 11819641 := bstep (se 2 (by rfl) ⟨4432365, by rfl⟩ : syracuseStep 11819641 = 8864731) B8864731
theorem B4775057 : Blo 542804 4775057 := bstep (se 2 (by rfl) ⟨1790646, by rfl⟩ : syracuseStep 4775057 = 3581293) B3581293
theorem B3497681 : Blo 542804 3497681 := bstep (se 2 (by rfl) ⟨1311630, by rfl⟩ : syracuseStep 3497681 = 2623261) B2623261
theorem B2941265 : Blo 542804 2941265 := bstep (se 2 (by rfl) ⟨1102974, by rfl⟩ : syracuseStep 2941265 = 2205949) B2205949
theorem B23847641 : Blo 542804 23847641 := bstep (se 2 (by rfl) ⟨8942865, by rfl⟩ : syracuseStep 23847641 = 17885731) B17885731
theorem B6808465 : Blo 542804 6808465 := bstep (se 2 (by rfl) ⟨2553174, by rfl⟩ : syracuseStep 6808465 = 5106349) B5106349
theorem B3105701 : Blo 542804 3105701 := bstep (se 4 (by rfl) ⟨291159, by rfl⟩ : syracuseStep 3105701 = 582319) B582319
theorem B4646281 : Blo 542804 4646281 := bstep (se 2 (by rfl) ⟨1742355, by rfl⟩ : syracuseStep 4646281 = 3484711) B3484711
theorem B3729083 : Blo 542804 3729083 := bstep (se 1 (by rfl) ⟨2796812, by rfl⟩ : syracuseStep 3729083 = 5593625) B5593625
theorem B3106633 : Blo 542804 3106633 := bstep (se 2 (by rfl) ⟨1164987, by rfl⟩ : syracuseStep 3106633 = 2329975) B2329975
theorem B14903189 : Blo 542804 14903189 := bstep (se 6 (by rfl) ⟨349293, by rfl⟩ : syracuseStep 14903189 = 698587) B698587
theorem B1468729 : Blo 542804 1468729 := bstep (se 2 (by rfl) ⟨550773, by rfl⟩ : syracuseStep 1468729 = 1101547) B1101547
theorem B1862027 : Blo 542804 1862027 := bstep (se 1 (by rfl) ⟨1396520, by rfl⟩ : syracuseStep 1862027 = 2793041) B2793041
theorem B1469033 : Blo 542804 1469033 := bstep (se 2 (by rfl) ⟨550887, by rfl⟩ : syracuseStep 1469033 = 1101775) B1101775
theorem B814415 : Blo 542804 814415 := bstep (se 1 (by rfl) ⟨610811, by rfl⟩ : syracuseStep 814415 = 1221623) B1221623
theorem B814505 : Blo 542804 814505 := bstep (se 2 (by rfl) ⟨305439, by rfl⟩ : syracuseStep 814505 = 610879) B610879
theorem B814655 : Blo 542804 814655 := bstep (se 1 (by rfl) ⟨610991, by rfl⟩ : syracuseStep 814655 = 1221983) B1221983
theorem B1437257 : Blo 542804 1437257 := bstep (se 2 (by rfl) ⟨538971, by rfl⟩ : syracuseStep 1437257 = 1077943) B1077943
theorem B16805501 : Blo 542804 16805501 := bstep (se 3 (by rfl) ⟨3151031, by rfl⟩ : syracuseStep 16805501 = 6302063) B6302063
theorem B814919 : Blo 542804 814919 := bstep (se 1 (by rfl) ⟨611189, by rfl⟩ : syracuseStep 814919 = 1222379) B1222379
theorem B815003 : Blo 542804 815003 := bstep (se 1 (by rfl) ⟨611252, by rfl⟩ : syracuseStep 815003 = 1222505) B1222505
theorem B13988051 : Blo 542804 13988051 := bstep (se 1 (by rfl) ⟨10491038, by rfl⟩ : syracuseStep 13988051 = 20982077) B20982077
theorem B2748815 : Blo 542804 2748815 := bstep (se 1 (by rfl) ⟨2061611, by rfl⟩ : syracuseStep 2748815 = 4123223) B4123223
theorem B815567 : Blo 542804 815567 := bstep (se 1 (by rfl) ⟨611675, by rfl⟩ : syracuseStep 815567 = 1223351) B1223351
theorem B815609 : Blo 542804 815609 := bstep (se 2 (by rfl) ⟨305853, by rfl⟩ : syracuseStep 815609 = 611707) B611707
theorem B1962575 : Blo 542804 1962575 := bstep (se 1 (by rfl) ⟨1471931, by rfl⟩ : syracuseStep 1962575 = 2943863) B2943863
theorem B815711 : Blo 542804 815711 := bstep (se 1 (by rfl) ⟨611783, by rfl⟩ : syracuseStep 815711 = 1223567) B1223567
theorem B816191 : Blo 542804 816191 := bstep (se 1 (by rfl) ⟨612143, by rfl⟩ : syracuseStep 816191 = 1224287) B1224287
theorem B816233 : Blo 542804 816233 := bstep (se 2 (by rfl) ⟨306087, by rfl⟩ : syracuseStep 816233 = 612175) B612175
theorem B1832111 : Blo 542804 1832111 := bstep (se 1 (by rfl) ⟨1374083, by rfl⟩ : syracuseStep 1832111 = 2748167) B2748167
theorem B816335 : Blo 542804 816335 := bstep (se 1 (by rfl) ⟨612251, by rfl⟩ : syracuseStep 816335 = 1224503) B1224503
theorem B1570079 : Blo 542804 1570079 := bstep (se 1 (by rfl) ⟨1177559, by rfl⟩ : syracuseStep 1570079 = 2355119) B2355119
theorem B3306881 : Blo 542804 3306881 := bstep (se 2 (by rfl) ⟨1240080, by rfl⟩ : syracuseStep 3306881 = 2480161) B2480161
theorem B816539 : Blo 542804 816539 := bstep (se 1 (by rfl) ⟨612404, by rfl⟩ : syracuseStep 816539 = 1224809) B1224809
theorem B816761 : Blo 542804 816761 := bstep (se 2 (by rfl) ⟨306285, by rfl⟩ : syracuseStep 816761 = 612571) B612571
theorem B2062007 : Blo 542804 2062007 := bstep (se 1 (by rfl) ⟨1546505, by rfl⟩ : syracuseStep 2062007 = 3093011) B3093011
theorem B816863 : Blo 542804 816863 := bstep (se 1 (by rfl) ⟨612647, by rfl⟩ : syracuseStep 816863 = 1225295) B1225295
theorem B980767 : Blo 542804 980767 := bstep (se 1 (by rfl) ⟨735575, by rfl⟩ : syracuseStep 980767 = 1471151) B1471151
theorem B816959 : Blo 542804 816959 := bstep (se 1 (by rfl) ⟨612719, by rfl⟩ : syracuseStep 816959 = 1225439) B1225439
theorem B817127 : Blo 542804 817127 := bstep (se 1 (by rfl) ⟨612845, by rfl⟩ : syracuseStep 817127 = 1225691) B1225691
theorem B817145 : Blo 542804 817145 := bstep (se 2 (by rfl) ⟨306429, by rfl⟩ : syracuseStep 817145 = 612859) B612859
theorem B817247 : Blo 542804 817247 := bstep (se 1 (by rfl) ⟨612935, by rfl⟩ : syracuseStep 817247 = 1225871) B1225871
theorem B817307 : Blo 542804 817307 := bstep (se 1 (by rfl) ⟨612980, by rfl⟩ : syracuseStep 817307 = 1225961) B1225961
theorem B817343 : Blo 542804 817343 := bstep (se 1 (by rfl) ⟨613007, by rfl⟩ : syracuseStep 817343 = 1226015) B1226015
theorem B2324713 : Blo 542804 2324713 := bstep (se 2 (by rfl) ⟨871767, by rfl⟩ : syracuseStep 2324713 = 1743535) B1743535
theorem B817385 : Blo 542804 817385 := bstep (se 2 (by rfl) ⟨306519, by rfl⟩ : syracuseStep 817385 = 613039) B613039
theorem B915995 : Blo 542804 915995 := bstep (se 1 (by rfl) ⟨686996, by rfl⟩ : syracuseStep 915995 = 1373993) B1373993
theorem B817691 : Blo 542804 817691 := bstep (se 1 (by rfl) ⟨613268, by rfl⟩ : syracuseStep 817691 = 1226537) B1226537
theorem B28670537 : Blo 542804 28670537 := bstep (se 2 (by rfl) ⟨10751451, by rfl⟩ : syracuseStep 28670537 = 21502903) B21502903
theorem B817769 : Blo 542804 817769 := bstep (se 2 (by rfl) ⟨306663, by rfl⟩ : syracuseStep 817769 = 613327) B613327
theorem B654383 : Blo 542804 654383 := bstep (se 1 (by rfl) ⟨490787, by rfl⟩ : syracuseStep 654383 = 981575) B981575
theorem B1834055 : Blo 542804 1834055 := bstep (se 1 (by rfl) ⟨1375541, by rfl⟩ : syracuseStep 1834055 = 2751083) B2751083
theorem B818297 : Blo 542804 818297 := bstep (se 2 (by rfl) ⟨306861, by rfl⟩ : syracuseStep 818297 = 613723) B613723
theorem B1834109 : Blo 542804 1834109 := bstep (se 3 (by rfl) ⟨343895, by rfl⟩ : syracuseStep 1834109 = 687791) B687791
theorem B916663 : Blo 542804 916663 := bstep (se 1 (by rfl) ⟨687497, by rfl⟩ : syracuseStep 916663 = 1374995) B1374995
theorem B818399 : Blo 542804 818399 := bstep (se 1 (by rfl) ⟨613799, by rfl⟩ : syracuseStep 818399 = 1227599) B1227599
theorem B818441 : Blo 542804 818441 := bstep (se 2 (by rfl) ⟨306915, by rfl⟩ : syracuseStep 818441 = 613831) B613831
theorem B818543 : Blo 542804 818543 := bstep (se 1 (by rfl) ⟨613907, by rfl⟩ : syracuseStep 818543 = 1227815) B1227815
theorem B1834379 : Blo 542804 1834379 := bstep (se 1 (by rfl) ⟨1375784, by rfl⟩ : syracuseStep 1834379 = 2751569) B2751569
theorem B916967 : Blo 542804 916967 := bstep (se 1 (by rfl) ⟨687725, by rfl⟩ : syracuseStep 916967 = 1375451) B1375451
theorem B818663 : Blo 542804 818663 := bstep (se 1 (by rfl) ⟨613997, by rfl⟩ : syracuseStep 818663 = 1227995) B1227995
theorem B916987 : Blo 542804 916987 := bstep (se 1 (by rfl) ⟨687740, by rfl⟩ : syracuseStep 916987 = 1375481) B1375481
theorem B884287 : Blo 542804 884287 := bstep (se 1 (by rfl) ⟨663215, by rfl⟩ : syracuseStep 884287 = 1326431) B1326431
theorem B818795 : Blo 542804 818795 := bstep (se 1 (by rfl) ⟨614096, by rfl⟩ : syracuseStep 818795 = 1228193) B1228193
theorem B818921 : Blo 542804 818921 := bstep (se 2 (by rfl) ⟨307095, by rfl⟩ : syracuseStep 818921 = 614191) B614191
theorem B1375987 : Blo 542804 1375987 := bstep (se 1 (by rfl) ⟨1031990, by rfl⟩ : syracuseStep 1375987 = 2063981) B2063981
theorem B4128569 : Blo 542804 4128569 := bstep (se 2 (by rfl) ⟨1548213, by rfl⟩ : syracuseStep 4128569 = 3096427) B3096427
theorem B687943 : Blo 542804 687943 := bstep (se 1 (by rfl) ⟨515957, by rfl⟩ : syracuseStep 687943 = 1031915) B1031915
theorem B1474375 : Blo 542804 1474375 := bstep (se 1 (by rfl) ⟨1105781, by rfl⟩ : syracuseStep 1474375 = 2211563) B2211563
theorem B819065 : Blo 542804 819065 := bstep (se 2 (by rfl) ⟨307149, by rfl⟩ : syracuseStep 819065 = 614299) B614299
theorem B917419 : Blo 542804 917419 := bstep (se 1 (by rfl) ⟨688064, by rfl⟩ : syracuseStep 917419 = 1376129) B1376129
theorem B819167 : Blo 542804 819167 := bstep (se 1 (by rfl) ⟨614375, by rfl⟩ : syracuseStep 819167 = 1228751) B1228751
theorem B1966265 : Blo 542804 1966265 := bstep (se 2 (by rfl) ⟨737349, by rfl⟩ : syracuseStep 1966265 = 1474699) B1474699
theorem B4194575 : Blo 542804 4194575 := bstep (se 1 (by rfl) ⟨3145931, by rfl⟩ : syracuseStep 4194575 = 6291863) B6291863
theorem B4129055 : Blo 542804 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B819503 : Blo 542804 819503 := bstep (se 1 (by rfl) ⟨614627, by rfl⟩ : syracuseStep 819503 = 1229255) B1229255
theorem B14188891 : Blo 542804 14188891 := bstep (se 1 (by rfl) ⟨10641668, by rfl⟩ : syracuseStep 14188891 = 21283337) B21283337
theorem B2490743 : Blo 542804 2490743 := bstep (se 1 (by rfl) ⟨1868057, by rfl⟩ : syracuseStep 2490743 = 3736115) B3736115
theorem B918047 : Blo 542804 918047 := bstep (se 1 (by rfl) ⟨688535, by rfl⟩ : syracuseStep 918047 = 1377071) B1377071
theorem B819743 : Blo 542804 819743 := bstep (se 1 (by rfl) ⟨614807, by rfl⟩ : syracuseStep 819743 = 1229615) B1229615
theorem B2785871 : Blo 542804 2785871 := bstep (se 1 (by rfl) ⟨2089403, by rfl⟩ : syracuseStep 2785871 = 4178807) B4178807
theorem B918121 : Blo 542804 918121 := bstep (se 2 (by rfl) ⟨344295, by rfl⟩ : syracuseStep 918121 = 688591) B688591
theorem B1835837 : Blo 542804 1835837 := bstep (se 3 (by rfl) ⟨344219, by rfl⟩ : syracuseStep 1835837 = 688439) B688439
theorem B5244061 : Blo 542804 5244061 := bstep (se 3 (by rfl) ⟨983261, by rfl⟩ : syracuseStep 5244061 = 1966523) B1966523
theorem B9077953 : Blo 542804 9077953 := bstep (se 2 (by rfl) ⟨3404232, by rfl⟩ : syracuseStep 9077953 = 6808465) B6808465
theorem B1836539 : Blo 542804 1836539 := bstep (se 1 (by rfl) ⟨1377404, by rfl⟩ : syracuseStep 1836539 = 2754809) B2754809
theorem B1967647 : Blo 542804 1967647 := bstep (se 1 (by rfl) ⟨1475735, by rfl⟩ : syracuseStep 1967647 = 2951471) B2951471
theorem B919147 : Blo 542804 919147 := bstep (se 1 (by rfl) ⟨689360, by rfl⟩ : syracuseStep 919147 = 1378721) B1378721
theorem B6195041 : Blo 542804 6195041 := bstep (se 2 (by rfl) ⟨2323140, by rfl⟩ : syracuseStep 6195041 = 4646281) B4646281
theorem B919417 : Blo 542804 919417 := bstep (se 2 (by rfl) ⟨344781, by rfl⟩ : syracuseStep 919417 = 689563) B689563
theorem B2623375 : Blo 542804 2623375 := bstep (se 1 (by rfl) ⟨1967531, by rfl⟩ : syracuseStep 2623375 = 3935063) B3935063
theorem B2066593 : Blo 542804 2066593 := bstep (se 2 (by rfl) ⟨774972, by rfl⟩ : syracuseStep 2066593 = 1549945) B1549945
theorem B919775 : Blo 542804 919775 := bstep (se 1 (by rfl) ⟨689831, by rfl⟩ : syracuseStep 919775 = 1379663) B1379663
theorem B2624339 : Blo 542804 2624339 := bstep (se 1 (by rfl) ⟨1968254, by rfl⟩ : syracuseStep 2624339 = 3936509) B3936509
theorem B920639 : Blo 542804 920639 := bstep (se 1 (by rfl) ⟨690479, by rfl⟩ : syracuseStep 920639 = 1380959) B1380959
theorem B1838267 : Blo 542804 1838267 := bstep (se 1 (by rfl) ⟨1378700, by rfl⟩ : syracuseStep 1838267 = 2757401) B2757401
theorem B1739987 : Blo 542804 1739987 := bstep (se 1 (by rfl) ⟨1304990, by rfl⟩ : syracuseStep 1739987 = 2609981) B2609981
theorem B2067839 : Blo 542804 2067839 := bstep (se 1 (by rfl) ⟨1550879, by rfl⟩ : syracuseStep 2067839 = 3101759) B3101759
theorem B2624993 : Blo 542804 2624993 := bstep (se 2 (by rfl) ⟨984372, by rfl⟩ : syracuseStep 2624993 = 1968745) B1968745
theorem B9572039 : Blo 542804 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B1839239 : Blo 542804 1839239 := bstep (se 1 (by rfl) ⟨1379429, by rfl⟩ : syracuseStep 1839239 = 2758859) B2758859
theorem B1839401 : Blo 542804 1839401 := bstep (se 2 (by rfl) ⟨689775, by rfl⟩ : syracuseStep 1839401 = 1379551) B1379551
theorem B1839671 : Blo 542804 1839671 := bstep (se 1 (by rfl) ⟨1379753, by rfl⟩ : syracuseStep 1839671 = 2759507) B2759507
theorem B3183371 : Blo 542804 3183371 := bstep (se 1 (by rfl) ⟨2387528, by rfl⟩ : syracuseStep 3183371 = 4775057) B4775057
theorem B2331787 : Blo 542804 2331787 := bstep (se 1 (by rfl) ⟨1748840, by rfl⟩ : syracuseStep 2331787 = 3497681) B3497681
theorem B2364713 : Blo 542804 2364713 := bstep (se 2 (by rfl) ⟨886767, by rfl⟩ : syracuseStep 2364713 = 1773535) B1773535
theorem B2626991 : Blo 542804 2626991 := bstep (se 1 (by rfl) ⟨1970243, by rfl⟩ : syracuseStep 2626991 = 3940487) B3940487
theorem B1840859 : Blo 542804 1840859 := bstep (se 1 (by rfl) ⟨1380644, by rfl⟩ : syracuseStep 1840859 = 2761289) B2761289
theorem B15898427 : Blo 542804 15898427 := bstep (se 1 (by rfl) ⟨11923820, by rfl⟩ : syracuseStep 15898427 = 23847641) B23847641
theorem B2070467 : Blo 542804 2070467 := bstep (se 1 (by rfl) ⟨1552850, by rfl⟩ : syracuseStep 2070467 = 3105701) B3105701
theorem B4134887 : Blo 542804 4134887 := bstep (se 1 (by rfl) ⟨3101165, by rfl⟩ : syracuseStep 4134887 = 6202331) B6202331
theorem B9935459 : Blo 542804 9935459 := bstep (se 1 (by rfl) ⟨7451594, by rfl⟩ : syracuseStep 9935459 = 14903189) B14903189
theorem B76454765 : Blo 542804 76454765 := bstep (se 3 (by rfl) ⟨14335268, by rfl⟩ : syracuseStep 76454765 = 28670537) B28670537
theorem B4201409 : Blo 542804 4201409 := bstep (se 2 (by rfl) ⟨1575528, by rfl⟩ : syracuseStep 4201409 = 3151057) B3151057
theorem B1547849 : Blo 542804 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B958171 : Blo 542804 958171 := bstep (se 1 (by rfl) ⟨718628, by rfl⟩ : syracuseStep 958171 = 1437257) B1437257
theorem B2203517 : Blo 542804 2203517 := bstep (se 3 (by rfl) ⟨413159, by rfl⟩ : syracuseStep 2203517 = 826319) B826319
theorem B7479229 : Blo 542804 7479229 := bstep (se 3 (by rfl) ⟨1402355, by rfl⟩ : syracuseStep 7479229 = 2804711) B2804711
theorem B1745021 : Blo 542804 1745021 := bstep (se 3 (by rfl) ⟨327191, by rfl⟩ : syracuseStep 1745021 = 654383) B654383
theorem B1221407 : Blo 542804 1221407 := bstep (se 1 (by rfl) ⟨916055, by rfl⟩ : syracuseStep 1221407 = 1832111) B1832111
theorem B2204587 : Blo 542804 2204587 := bstep (se 1 (by rfl) ⟨1653440, by rfl⟩ : syracuseStep 2204587 = 3306881) B3306881
theorem B1222217 : Blo 542804 1222217 := bstep (se 2 (by rfl) ⟨458331, by rfl⟩ : syracuseStep 1222217 = 916663) B916663
theorem B1222649 : Blo 542804 1222649 := bstep (se 2 (by rfl) ⟨458493, by rfl⟩ : syracuseStep 1222649 = 916987) B916987
theorem B1222703 : Blo 542804 1222703 := bstep (se 1 (by rfl) ⟨917027, by rfl⟩ : syracuseStep 1222703 = 1834055) B1834055
theorem B1222739 : Blo 542804 1222739 := bstep (se 1 (by rfl) ⟨917054, by rfl⟩ : syracuseStep 1222739 = 1834109) B1834109
theorem B1222919 : Blo 542804 1222919 := bstep (se 1 (by rfl) ⟨917189, by rfl⟩ : syracuseStep 1222919 = 1834379) B1834379
theorem B2075129 : Blo 542804 2075129 := bstep (se 2 (by rfl) ⟨778173, by rfl⟩ : syracuseStep 2075129 = 1556347) B1556347
theorem B1223225 : Blo 542804 1223225 := bstep (se 2 (by rfl) ⟨458709, by rfl⟩ : syracuseStep 1223225 = 917419) B917419
theorem B5319431 : Blo 542804 5319431 := bstep (se 1 (by rfl) ⟨3989573, by rfl⟩ : syracuseStep 5319431 = 7979147) B7979147
theorem B1747919 : Blo 542804 1747919 := bstep (se 1 (by rfl) ⟨1310939, by rfl⟩ : syracuseStep 1747919 = 2621879) B2621879
theorem B2075615 : Blo 542804 2075615 := bstep (se 1 (by rfl) ⟨1556711, by rfl⟩ : syracuseStep 2075615 = 3113423) B3113423
theorem B1223945 : Blo 542804 1223945 := bstep (se 2 (by rfl) ⟨458979, by rfl⟩ : syracuseStep 1223945 = 917959) B917959
theorem B1192079 : Blo 542804 1192079 := bstep (se 1 (by rfl) ⟨894059, by rfl⟩ : syracuseStep 1192079 = 1788119) B1788119
theorem B1224935 : Blo 542804 1224935 := bstep (se 1 (by rfl) ⟨918701, by rfl⟩ : syracuseStep 1224935 = 1837403) B1837403
theorem B1225115 : Blo 542804 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B2765501 : Blo 542804 2765501 := bstep (se 3 (by rfl) ⟨518531, by rfl⟩ : syracuseStep 2765501 = 1037063) B1037063
theorem B1553215 : Blo 542804 1553215 := bstep (se 1 (by rfl) ⟨1164911, by rfl⟩ : syracuseStep 1553215 = 2329823) B2329823
theorem B1553363 : Blo 542804 1553363 := bstep (se 1 (by rfl) ⟨1165022, by rfl⟩ : syracuseStep 1553363 = 2330045) B2330045
theorem B3093511 : Blo 542804 3093511 := bstep (se 1 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 3093511 = 4640267) B4640267
theorem B1225799 : Blo 542804 1225799 := bstep (se 1 (by rfl) ⟨919349, by rfl⟩ : syracuseStep 1225799 = 1838699) B1838699
theorem B4142177 : Blo 542804 4142177 := bstep (se 2 (by rfl) ⟨1553316, by rfl⟩ : syracuseStep 4142177 = 3106633) B3106633
theorem B1160443 : Blo 542804 1160443 := bstep (se 1 (by rfl) ⟨870332, by rfl⟩ : syracuseStep 1160443 = 1740665) B1740665
theorem B1225979 : Blo 542804 1225979 := bstep (se 1 (by rfl) ⟨919484, by rfl⟩ : syracuseStep 1225979 = 1838969) B1838969
theorem B1226195 : Blo 542804 1226195 := bstep (se 1 (by rfl) ⟨919646, by rfl⟩ : syracuseStep 1226195 = 1839293) B1839293
theorem B2209451 : Blo 542804 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B1226465 : Blo 542804 1226465 := bstep (se 2 (by rfl) ⟨459924, by rfl⟩ : syracuseStep 1226465 = 919849) B919849
theorem B1226987 : Blo 542804 1226987 := bstep (se 1 (by rfl) ⟨920240, by rfl⟩ : syracuseStep 1226987 = 1840481) B1840481
theorem B8927495 : Blo 542804 8927495 := bstep (se 1 (by rfl) ⟨6695621, by rfl⟩ : syracuseStep 8927495 = 13391243) B13391243
theorem B10435067 : Blo 542804 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B4143635 : Blo 542804 4143635 := bstep (se 1 (by rfl) ⟨3107726, by rfl⟩ : syracuseStep 4143635 = 6215453) B6215453
theorem B1030799 : Blo 542804 1030799 := bstep (se 1 (by rfl) ⟨773099, by rfl⟩ : syracuseStep 1030799 = 1546199) B1546199
theorem B6208163 : Blo 542804 6208163 := bstep (se 1 (by rfl) ⟨4656122, by rfl⟩ : syracuseStep 6208163 = 9312245) B9312245
theorem B16825319 : Blo 542804 16825319 := bstep (se 1 (by rfl) ⟨12618989, by rfl⟩ : syracuseStep 16825319 = 25237979) B25237979
theorem B2767931 : Blo 542804 2767931 := bstep (se 1 (by rfl) ⟨2075948, by rfl⟩ : syracuseStep 2767931 = 4151897) B4151897
theorem B9944221 : Blo 542804 9944221 := bstep (se 3 (by rfl) ⟨1864541, by rfl⟩ : syracuseStep 9944221 = 3729083) B3729083
theorem B4963751 : Blo 542804 4963751 := bstep (se 1 (by rfl) ⟨3722813, by rfl⟩ : syracuseStep 4963751 = 7445627) B7445627
theorem B1228283 : Blo 542804 1228283 := bstep (se 1 (by rfl) ⟨921212, by rfl⟩ : syracuseStep 1228283 = 1842425) B1842425
theorem B1228463 : Blo 542804 1228463 := bstep (se 1 (by rfl) ⟨921347, by rfl⟩ : syracuseStep 1228463 = 1842695) B1842695
theorem B1228553 : Blo 542804 1228553 := bstep (se 2 (by rfl) ⟨460707, by rfl⟩ : syracuseStep 1228553 = 921415) B921415
theorem B12763453 : Blo 542804 12763453 := bstep (se 3 (by rfl) ⟨2393147, by rfl⟩ : syracuseStep 12763453 = 4786295) B4786295
theorem B1229183 : Blo 542804 1229183 := bstep (se 1 (by rfl) ⟨921887, by rfl⟩ : syracuseStep 1229183 = 1843775) B1843775
theorem B1229417 : Blo 542804 1229417 := bstep (se 2 (by rfl) ⟨461031, by rfl⟩ : syracuseStep 1229417 = 922063) B922063
theorem B1163963 : Blo 542804 1163963 := bstep (se 1 (by rfl) ⟨872972, by rfl⟩ : syracuseStep 1163963 = 1745945) B1745945
theorem B5227375 : Blo 542804 5227375 := bstep (se 1 (by rfl) ⟨3920531, by rfl⟩ : syracuseStep 5227375 = 7841063) B7841063
theorem B1033327 : Blo 542804 1033327 := bstep (se 1 (by rfl) ⟨774995, by rfl⟩ : syracuseStep 1033327 = 1549991) B1549991
theorem B1230047 : Blo 542804 1230047 := bstep (se 1 (by rfl) ⟨922535, by rfl⟩ : syracuseStep 1230047 = 1845071) B1845071
theorem B1230263 : Blo 542804 1230263 := bstep (se 1 (by rfl) ⟨922697, by rfl⟩ : syracuseStep 1230263 = 1845395) B1845395
theorem B38127395 : Blo 542804 38127395 := bstep (se 1 (by rfl) ⟨28595546, by rfl⟩ : syracuseStep 38127395 = 57191093) B57191093
theorem B19842893 : Blo 542804 19842893 := bstep (se 3 (by rfl) ⟨3720542, by rfl⟩ : syracuseStep 19842893 = 7441085) B7441085
theorem B542943 : Blo 542804 542943 := bstep (se 1 (by rfl) ⟨407207, by rfl⟩ : syracuseStep 542943 = 814415) B814415
theorem B543003 : Blo 542804 543003 := bstep (se 1 (by rfl) ⟨407252, by rfl⟩ : syracuseStep 543003 = 814505) B814505
theorem B543103 : Blo 542804 543103 := bstep (se 1 (by rfl) ⟨407327, by rfl⟩ : syracuseStep 543103 = 814655) B814655
theorem B28330373 : Blo 542804 28330373 := bstep (se 4 (by rfl) ⟨2655972, by rfl⟩ : syracuseStep 28330373 = 5311945) B5311945
theorem B543279 : Blo 542804 543279 := bstep (se 1 (by rfl) ⟨407459, by rfl⟩ : syracuseStep 543279 = 814919) B814919
theorem B543335 : Blo 542804 543335 := bstep (se 1 (by rfl) ⟨407501, by rfl⟩ : syracuseStep 543335 = 815003) B815003
theorem B9325367 : Blo 542804 9325367 := bstep (se 1 (by rfl) ⟨6994025, by rfl⟩ : syracuseStep 9325367 = 13988051) B13988051
theorem B6212537 : Blo 542804 6212537 := bstep (se 2 (by rfl) ⟨2329701, by rfl⟩ : syracuseStep 6212537 = 4659403) B4659403
theorem B543711 : Blo 542804 543711 := bstep (se 1 (by rfl) ⟨407783, by rfl⟩ : syracuseStep 543711 = 815567) B815567
theorem B3099617 : Blo 542804 3099617 := bstep (se 2 (by rfl) ⟨1162356, by rfl⟩ : syracuseStep 3099617 = 2324713) B2324713
theorem B543739 : Blo 542804 543739 := bstep (se 1 (by rfl) ⟨407804, by rfl⟩ : syracuseStep 543739 = 815609) B815609
theorem B543807 : Blo 542804 543807 := bstep (se 1 (by rfl) ⟨407855, by rfl⟩ : syracuseStep 543807 = 815711) B815711
theorem B544127 : Blo 542804 544127 := bstep (se 1 (by rfl) ⟨408095, by rfl⟩ : syracuseStep 544127 = 816191) B816191
theorem B544155 : Blo 542804 544155 := bstep (se 1 (by rfl) ⟨408116, by rfl⟩ : syracuseStep 544155 = 816233) B816233
theorem B544223 : Blo 542804 544223 := bstep (se 1 (by rfl) ⟨408167, by rfl⟩ : syracuseStep 544223 = 816335) B816335
theorem B544359 : Blo 542804 544359 := bstep (se 1 (by rfl) ⟨408269, by rfl⟩ : syracuseStep 544359 = 816539) B816539
theorem B2215549 : Blo 542804 2215549 := bstep (se 3 (by rfl) ⟨415415, by rfl⟩ : syracuseStep 2215549 = 830831) B830831
theorem B6999767 : Blo 542804 6999767 := bstep (se 1 (by rfl) ⟨5249825, by rfl⟩ : syracuseStep 6999767 = 10499651) B10499651
theorem B544507 : Blo 542804 544507 := bstep (se 1 (by rfl) ⟨408380, by rfl⟩ : syracuseStep 544507 = 816761) B816761
theorem B544575 : Blo 542804 544575 := bstep (se 1 (by rfl) ⟨408431, by rfl⟩ : syracuseStep 544575 = 816863) B816863
theorem B544639 : Blo 542804 544639 := bstep (se 1 (by rfl) ⟨408479, by rfl⟩ : syracuseStep 544639 = 816959) B816959
theorem B544751 : Blo 542804 544751 := bstep (se 1 (by rfl) ⟨408563, by rfl⟩ : syracuseStep 544751 = 817127) B817127
theorem B544763 : Blo 542804 544763 := bstep (se 1 (by rfl) ⟨408572, by rfl⟩ : syracuseStep 544763 = 817145) B817145
theorem B544831 : Blo 542804 544831 := bstep (se 1 (by rfl) ⟨408623, by rfl⟩ : syracuseStep 544831 = 817247) B817247
theorem B544871 : Blo 542804 544871 := bstep (se 1 (by rfl) ⟨408653, by rfl⟩ : syracuseStep 544871 = 817307) B817307
theorem B544895 : Blo 542804 544895 := bstep (se 1 (by rfl) ⟨408671, by rfl⟩ : syracuseStep 544895 = 817343) B817343
theorem B544923 : Blo 542804 544923 := bstep (se 1 (by rfl) ⟨408692, by rfl⟩ : syracuseStep 544923 = 817385) B817385
theorem B5230757 : Blo 542804 5230757 := bstep (se 4 (by rfl) ⟨490383, by rfl⟩ : syracuseStep 5230757 = 980767) B980767
theorem B610663 : Blo 542804 610663 := bstep (se 1 (by rfl) ⟨457997, by rfl⟩ : syracuseStep 610663 = 915995) B915995
theorem B545127 : Blo 542804 545127 := bstep (se 1 (by rfl) ⟨408845, by rfl⟩ : syracuseStep 545127 = 817691) B817691
theorem B6213995 : Blo 542804 6213995 := bstep (se 1 (by rfl) ⟨4660496, by rfl⟩ : syracuseStep 6213995 = 9320993) B9320993
theorem B545179 : Blo 542804 545179 := bstep (se 1 (by rfl) ⟨408884, by rfl⟩ : syracuseStep 545179 = 817769) B817769
theorem B1102391 : Blo 542804 1102391 := bstep (se 1 (by rfl) ⟨826793, by rfl⟩ : syracuseStep 1102391 = 1653587) B1653587
theorem B545531 : Blo 542804 545531 := bstep (se 1 (by rfl) ⟨409148, by rfl⟩ : syracuseStep 545531 = 818297) B818297
theorem B545599 : Blo 542804 545599 := bstep (se 1 (by rfl) ⟨409199, by rfl⟩ : syracuseStep 545599 = 818399) B818399
theorem B545627 : Blo 542804 545627 := bstep (se 1 (by rfl) ⟨409220, by rfl⟩ : syracuseStep 545627 = 818441) B818441
theorem B545695 : Blo 542804 545695 := bstep (se 1 (by rfl) ⟨409271, by rfl⟩ : syracuseStep 545695 = 818543) B818543
theorem B1037215 : Blo 542804 1037215 := bstep (se 1 (by rfl) ⟨777911, by rfl⟩ : syracuseStep 1037215 = 1555823) B1555823
theorem B611311 : Blo 542804 611311 := bstep (se 1 (by rfl) ⟨458483, by rfl⟩ : syracuseStep 611311 = 916967) B916967
theorem B545775 : Blo 542804 545775 := bstep (se 1 (by rfl) ⟨409331, by rfl⟩ : syracuseStep 545775 = 818663) B818663
theorem B545863 : Blo 542804 545863 := bstep (se 1 (by rfl) ⟨409397, by rfl⟩ : syracuseStep 545863 = 818795) B818795
theorem B1102943 : Blo 542804 1102943 := bstep (se 1 (by rfl) ⟨827207, by rfl⟩ : syracuseStep 1102943 = 1654415) B1654415
theorem B545947 : Blo 542804 545947 := bstep (se 1 (by rfl) ⟨409460, by rfl⟩ : syracuseStep 545947 = 818921) B818921
theorem B1037519 : Blo 542804 1037519 := bstep (se 1 (by rfl) ⟨778139, by rfl⟩ : syracuseStep 1037519 = 1556279) B1556279
theorem B546043 : Blo 542804 546043 := bstep (se 1 (by rfl) ⟨409532, by rfl⟩ : syracuseStep 546043 = 819065) B819065
theorem B546111 : Blo 542804 546111 := bstep (se 1 (by rfl) ⟨409583, by rfl⟩ : syracuseStep 546111 = 819167) B819167
theorem B611815 : Blo 542804 611815 := bstep (se 1 (by rfl) ⟨458861, by rfl⟩ : syracuseStep 611815 = 917723) B917723
theorem B546279 : Blo 542804 546279 := bstep (se 1 (by rfl) ⟨409709, by rfl⟩ : syracuseStep 546279 = 819419) B819419
theorem B546287 : Blo 542804 546287 := bstep (se 1 (by rfl) ⟨409715, by rfl⟩ : syracuseStep 546287 = 819431) B819431
theorem B546395 : Blo 542804 546395 := bstep (se 1 (by rfl) ⟨409796, by rfl⟩ : syracuseStep 546395 = 819593) B819593
theorem B611995 : Blo 542804 611995 := bstep (se 1 (by rfl) ⟨458996, by rfl⟩ : syracuseStep 611995 = 917993) B917993
theorem B546459 : Blo 542804 546459 := bstep (se 1 (by rfl) ⟨409844, by rfl⟩ : syracuseStep 546459 = 819689) B819689
theorem B546543 : Blo 542804 546543 := bstep (se 1 (by rfl) ⟨409907, by rfl⟩ : syracuseStep 546543 = 819815) B819815
theorem B546631 : Blo 542804 546631 := bstep (se 1 (by rfl) ⟨409973, by rfl⟩ : syracuseStep 546631 = 819947) B819947
theorem B874331 : Blo 542804 874331 := bstep (se 1 (by rfl) ⟨655748, by rfl⟩ : syracuseStep 874331 = 1311497) B1311497
theorem B546651 : Blo 542804 546651 := bstep (se 1 (by rfl) ⟨409988, by rfl⟩ : syracuseStep 546651 = 819977) B819977
theorem B546719 : Blo 542804 546719 := bstep (se 1 (by rfl) ⟨410039, by rfl⟩ : syracuseStep 546719 = 820079) B820079
theorem B2545835 : Blo 542804 2545835 := bstep (se 1 (by rfl) ⟨1909376, by rfl⟩ : syracuseStep 2545835 = 3818753) B3818753
theorem B2513479 : Blo 542804 2513479 := bstep (se 1 (by rfl) ⟨1885109, by rfl⟩ : syracuseStep 2513479 = 3770219) B3770219
theorem B4415143 : Blo 542804 4415143 := bstep (se 1 (by rfl) ⟨3311357, by rfl⟩ : syracuseStep 4415143 = 6622715) B6622715
theorem B614119 : Blo 542804 614119 := bstep (se 1 (by rfl) ⟨460589, by rfl⟩ : syracuseStep 614119 = 921179) B921179
theorem B1957787 : Blo 542804 1957787 := bstep (se 1 (by rfl) ⟨1468340, by rfl⟩ : syracuseStep 1957787 = 2936681) B2936681
theorem B8314807 : Blo 542804 8314807 := bstep (se 1 (by rfl) ⟨6236105, by rfl⟩ : syracuseStep 8314807 = 12472211) B12472211
theorem B1400819 : Blo 542804 1400819 := bstep (se 1 (by rfl) ⟨1050614, by rfl⟩ : syracuseStep 1400819 = 2101229) B2101229
theorem B37773317 : Blo 542804 37773317 := bstep (se 4 (by rfl) ⟨3541248, by rfl⟩ : syracuseStep 37773317 = 7082497) B7082497
theorem B778447 : Blo 542804 778447 := bstep (se 1 (by rfl) ⟨583835, by rfl⟩ : syracuseStep 778447 = 1167671) B1167671
theorem B1958305 : Blo 542804 1958305 := bstep (se 2 (by rfl) ⟨734364, by rfl⟩ : syracuseStep 1958305 = 1468729) B1468729
theorem B2613671 : Blo 542804 2613671 := bstep (se 1 (by rfl) ⟨1960253, by rfl⟩ : syracuseStep 2613671 = 3920507) B3920507
theorem B16802653 : Blo 542804 16802653 := bstep (se 3 (by rfl) ⟨3150497, by rfl⟩ : syracuseStep 16802653 = 6300995) B6300995
theorem B196338887 : Blo 542804 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B2319997 : Blo 542804 2319997 := bstep (se 3 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 2319997 = 869999) B869999
theorem B6973523 : Blo 542804 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B2943341 : Blo 542804 2943341 := bstep (se 3 (by rfl) ⟨551876, by rfl⟩ : syracuseStep 2943341 = 1103753) B1103753
theorem B1960843 : Blo 542804 1960843 := bstep (se 1 (by rfl) ⟨1470632, by rfl⟩ : syracuseStep 1960843 = 2941265) B2941265
theorem B25226149 : Blo 542804 25226149 := bstep (se 4 (by rfl) ⟨2364951, by rfl⟩ : syracuseStep 25226149 = 4729903) B4729903
theorem B15133697 : Blo 542804 15133697 := bstep (se 2 (by rfl) ⟨5675136, by rfl⟩ : syracuseStep 15133697 = 11350273) B11350273
theorem B814391 : Blo 542804 814391 := bstep (se 1 (by rfl) ⟨610793, by rfl⟩ : syracuseStep 814391 = 1221587) B1221587
theorem B814559 : Blo 542804 814559 := bstep (se 1 (by rfl) ⟨610919, by rfl⟩ : syracuseStep 814559 = 1221839) B1221839
theorem B814775 : Blo 542804 814775 := bstep (se 1 (by rfl) ⟨611081, by rfl⟩ : syracuseStep 814775 = 1222163) B1222163
theorem B814985 : Blo 542804 814985 := bstep (se 2 (by rfl) ⟨305619, by rfl⟩ : syracuseStep 814985 = 611239) B611239
theorem B815231 : Blo 542804 815231 := bstep (se 1 (by rfl) ⟨611423, by rfl⟩ : syracuseStep 815231 = 1222847) B1222847
theorem B1241351 : Blo 542804 1241351 := bstep (se 1 (by rfl) ⟨931013, by rfl⟩ : syracuseStep 1241351 = 1862027) B1862027
theorem B979355 : Blo 542804 979355 := bstep (se 1 (by rfl) ⟨734516, by rfl⟩ : syracuseStep 979355 = 1469033) B1469033
theorem B2323039 : Blo 542804 2323039 := bstep (se 1 (by rfl) ⟨1742279, by rfl⟩ : syracuseStep 2323039 = 3484559) B3484559
theorem B2323073 : Blo 542804 2323073 := bstep (se 2 (by rfl) ⟨871152, by rfl⟩ : syracuseStep 2323073 = 1742305) B1742305
theorem B2061035 : Blo 542804 2061035 := bstep (se 1 (by rfl) ⟨1545776, by rfl⟩ : syracuseStep 2061035 = 3091553) B3091553
theorem B815867 : Blo 542804 815867 := bstep (se 1 (by rfl) ⟨611900, by rfl⟩ : syracuseStep 815867 = 1223801) B1223801
theorem B2061065 : Blo 542804 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B11203667 : Blo 542804 11203667 := bstep (se 1 (by rfl) ⟨8402750, by rfl⟩ : syracuseStep 11203667 = 16805501) B16805501
theorem B816311 : Blo 542804 816311 := bstep (se 1 (by rfl) ⟨612233, by rfl⟩ : syracuseStep 816311 = 1224467) B1224467
theorem B2061521 : Blo 542804 2061521 := bstep (se 2 (by rfl) ⟨773070, by rfl⟩ : syracuseStep 2061521 = 1546141) B1546141
theorem B8615159 : Blo 542804 8615159 := bstep (se 1 (by rfl) ⟨6461369, by rfl⟩ : syracuseStep 8615159 = 12922739) B12922739
theorem B816551 : Blo 542804 816551 := bstep (se 1 (by rfl) ⟨612413, by rfl⟩ : syracuseStep 816551 = 1224827) B1224827
theorem B816731 : Blo 542804 816731 := bstep (se 1 (by rfl) ⟨612548, by rfl⟩ : syracuseStep 816731 = 1225097) B1225097
theorem B1832543 : Blo 542804 1832543 := bstep (se 1 (by rfl) ⟨1374407, by rfl⟩ : syracuseStep 1832543 = 2748815) B2748815
theorem B1308383 : Blo 542804 1308383 := bstep (se 1 (by rfl) ⟨981287, by rfl⟩ : syracuseStep 1308383 = 1962575) B1962575
theorem B817193 : Blo 542804 817193 := bstep (se 2 (by rfl) ⟨306447, by rfl⟩ : syracuseStep 817193 = 612895) B612895
theorem B817223 : Blo 542804 817223 := bstep (se 1 (by rfl) ⟨612917, by rfl⟩ : syracuseStep 817223 = 1225835) B1225835
theorem B15759521 : Blo 542804 15759521 := bstep (se 2 (by rfl) ⟨5909820, by rfl⟩ : syracuseStep 15759521 = 11819641) B11819641
theorem B1046719 : Blo 542804 1046719 := bstep (se 1 (by rfl) ⟨785039, by rfl⟩ : syracuseStep 1046719 = 1570079) B1570079
theorem B817607 : Blo 542804 817607 := bstep (se 1 (by rfl) ⟨613205, by rfl⟩ : syracuseStep 817607 = 1226411) B1226411
theorem B1374671 : Blo 542804 1374671 := bstep (se 1 (by rfl) ⟨1031003, by rfl⟩ : syracuseStep 1374671 = 2062007) B2062007
theorem B2652763 : Blo 542804 2652763 := bstep (se 1 (by rfl) ⟨1989572, by rfl⟩ : syracuseStep 2652763 = 3979145) B3979145
theorem B817823 : Blo 542804 817823 := bstep (se 1 (by rfl) ⟨613367, by rfl⟩ : syracuseStep 817823 = 1226735) B1226735
theorem B817967 : Blo 542804 817967 := bstep (se 1 (by rfl) ⟨613475, by rfl⟩ : syracuseStep 817967 = 1226951) B1226951
theorem B2063191 : Blo 542804 2063191 := bstep (se 1 (by rfl) ⟨1547393, by rfl⟩ : syracuseStep 2063191 = 3094787) B3094787
theorem B4422509 : Blo 542804 4422509 := bstep (se 3 (by rfl) ⟨829220, by rfl⟩ : syracuseStep 4422509 = 1658441) B1658441
theorem B818087 : Blo 542804 818087 := bstep (se 1 (by rfl) ⟨613565, by rfl⟩ : syracuseStep 818087 = 1227131) B1227131
theorem B2325449 : Blo 542804 2325449 := bstep (se 2 (by rfl) ⟨872043, by rfl⟩ : syracuseStep 2325449 = 1744087) B1744087
theorem B818267 : Blo 542804 818267 := bstep (se 1 (by rfl) ⟨613700, by rfl⟩ : syracuseStep 818267 = 1227401) B1227401
theorem B1179049 : Blo 542804 1179049 := bstep (se 2 (by rfl) ⟨442143, by rfl⟩ : syracuseStep 1179049 = 884287) B884287
theorem B4488635 : Blo 542804 4488635 := bstep (se 1 (by rfl) ⟨3366476, by rfl⟩ : syracuseStep 4488635 = 6732953) B6732953
theorem B818639 : Blo 542804 818639 := bstep (se 1 (by rfl) ⟨613979, by rfl⟩ : syracuseStep 818639 = 1227959) B1227959
theorem B2063951 : Blo 542804 2063951 := bstep (se 1 (by rfl) ⟨1547963, by rfl⟩ : syracuseStep 2063951 = 3095927) B3095927
theorem B1834649 : Blo 542804 1834649 := bstep (se 2 (by rfl) ⟨687993, by rfl⟩ : syracuseStep 1834649 = 1375987) B1375987
theorem B687847 : Blo 542804 687847 := bstep (se 1 (by rfl) ⟨515885, by rfl⟩ : syracuseStep 687847 = 1031771) B1031771
theorem B37715705 : Blo 542804 37715705 := bstep (se 2 (by rfl) ⟨14143389, by rfl⟩ : syracuseStep 37715705 = 28286779) B28286779
theorem B917257 : Blo 542804 917257 := bstep (se 2 (by rfl) ⟨343971, by rfl⟩ : syracuseStep 917257 = 687943) B687943
theorem B1965833 : Blo 542804 1965833 := bstep (se 2 (by rfl) ⟨737187, by rfl⟩ : syracuseStep 1965833 = 1474375) B1474375
theorem B819023 : Blo 542804 819023 := bstep (se 1 (by rfl) ⟨614267, by rfl⟩ : syracuseStep 819023 = 1228535) B1228535
theorem B2752379 : Blo 542804 2752379 := bstep (se 1 (by rfl) ⟨2064284, by rfl⟩ : syracuseStep 2752379 = 4128569) B4128569
theorem B819143 : Blo 542804 819143 := bstep (se 1 (by rfl) ⟨614357, by rfl⟩ : syracuseStep 819143 = 1228715) B1228715
theorem B1310843 : Blo 542804 1310843 := bstep (se 1 (by rfl) ⟨983132, by rfl⟩ : syracuseStep 1310843 = 1966265) B1966265
theorem B2752703 : Blo 542804 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B819455 : Blo 542804 819455 := bstep (se 1 (by rfl) ⟨614591, by rfl⟩ : syracuseStep 819455 = 1229183) B1229183
theorem B4653389 : Blo 542804 4653389 := bstep (se 3 (by rfl) ⟨872510, by rfl⟩ : syracuseStep 4653389 = 1745021) B1745021
theorem B819611 : Blo 542804 819611 := bstep (se 1 (by rfl) ⟨614708, by rfl⟩ : syracuseStep 819611 = 1229417) B1229417
theorem B820031 : Blo 542804 820031 := bstep (se 1 (by rfl) ⟨615023, by rfl⟩ : syracuseStep 820031 = 1230047) B1230047
theorem B820175 : Blo 542804 820175 := bstep (se 1 (by rfl) ⟨615131, by rfl⟩ : syracuseStep 820175 = 1230263) B1230263
theorem B4130027 : Blo 542804 4130027 := bstep (se 1 (by rfl) ⟨3097520, by rfl⟩ : syracuseStep 4130027 = 6195041) B6195041
theorem B1377769 : Blo 542804 1377769 := bstep (se 2 (by rfl) ⟨516663, by rfl⟩ : syracuseStep 1377769 = 1033327) B1033327
theorem B2066411 : Blo 542804 2066411 := bstep (se 1 (by rfl) ⟨1549808, by rfl⟩ : syracuseStep 2066411 = 3099617) B3099617
theorem B2623529 : Blo 542804 2623529 := bstep (se 2 (by rfl) ⟨983823, by rfl⟩ : syracuseStep 2623529 = 1967647) B1967647
theorem B1378559 : Blo 542804 1378559 := bstep (se 1 (by rfl) ⟨1033919, by rfl⟩ : syracuseStep 1378559 = 2067839) B2067839
theorem B2755457 : Blo 542804 2755457 := bstep (se 2 (by rfl) ⟨1033296, by rfl⟩ : syracuseStep 2755457 = 2066593) B2066593
theorem B691679 : Blo 542804 691679 := bstep (se 1 (by rfl) ⟨518759, by rfl⟩ : syracuseStep 691679 = 1037519) B1037519
theorem B1576475 : Blo 542804 1576475 := bstep (se 1 (by rfl) ⟨1182356, by rfl⟩ : syracuseStep 1576475 = 2364713) B2364713
theorem B1380311 : Blo 542804 1380311 := bstep (se 1 (by rfl) ⟨1035233, by rfl⟩ : syracuseStep 1380311 = 2070467) B2070467
theorem B2756591 : Blo 542804 2756591 := bstep (se 1 (by rfl) ⟨2067443, by rfl⟩ : syracuseStep 2756591 = 4134887) B4134887
theorem B6623639 : Blo 542804 6623639 := bstep (se 1 (by rfl) ⟨4967729, by rfl⟩ : syracuseStep 6623639 = 9935459) B9935459
theorem B2954065 : Blo 542804 2954065 := bstep (se 2 (by rfl) ⟨1107774, by rfl⟩ : syracuseStep 2954065 = 2215549) B2215549
theorem B1742447 : Blo 542804 1742447 := bstep (se 1 (by rfl) ⟨1306835, by rfl⟩ : syracuseStep 1742447 = 2613671) B2613671
theorem B6788893 : Blo 542804 6788893 := bstep (se 3 (by rfl) ⟨1272917, by rfl⟩ : syracuseStep 6788893 = 2545835) B2545835
theorem B2070953 : Blo 542804 2070953 := bstep (se 2 (by rfl) ⟨776607, by rfl⟩ : syracuseStep 2070953 = 1553215) B1553215
theorem B1382953 : Blo 542804 1382953 := bstep (se 2 (by rfl) ⟨518607, by rfl⟩ : syracuseStep 1382953 = 1037215) B1037215
theorem B1547257 : Blo 542804 1547257 := bstep (se 2 (by rfl) ⟨580221, by rfl⟩ : syracuseStep 1547257 = 1160443) B1160443
theorem B1383419 : Blo 542804 1383419 := bstep (se 1 (by rfl) ⟨1037564, by rfl⟩ : syracuseStep 1383419 = 2075129) B2075129
theorem B3546287 : Blo 542804 3546287 := bstep (se 1 (by rfl) ⟨2659715, by rfl⟩ : syracuseStep 3546287 = 5319431) B5319431
theorem B1383743 : Blo 542804 1383743 := bstep (se 1 (by rfl) ⟨1037807, by rfl⟩ : syracuseStep 1383743 = 2075615) B2075615
theorem B794719 : Blo 542804 794719 := bstep (se 1 (by rfl) ⟨596039, by rfl⟩ : syracuseStep 794719 = 1192079) B1192079
theorem B827567 : Blo 542804 827567 := bstep (se 1 (by rfl) ⟨620675, by rfl⟩ : syracuseStep 827567 = 1241351) B1241351
theorem B1548715 : Blo 542804 1548715 := bstep (se 1 (by rfl) ⟨1161536, by rfl⟩ : syracuseStep 1548715 = 2323073) B2323073
theorem B1843667 : Blo 542804 1843667 := bstep (se 1 (by rfl) ⟨1382750, by rfl⟩ : syracuseStep 1843667 = 2765501) B2765501
theorem B2761451 : Blo 542804 2761451 := bstep (se 1 (by rfl) ⟨2071088, by rfl⟩ : syracuseStep 2761451 = 4142177) B4142177
theorem B3351305 : Blo 542804 3351305 := bstep (se 2 (by rfl) ⟨1256739, by rfl⟩ : syracuseStep 3351305 = 2513479) B2513479
theorem B5743439 : Blo 542804 5743439 := bstep (se 1 (by rfl) ⟨4307579, by rfl⟩ : syracuseStep 5743439 = 8615159) B8615159
theorem B1221695 : Blo 542804 1221695 := bstep (se 1 (by rfl) ⟨916271, by rfl⟩ : syracuseStep 1221695 = 1832543) B1832543
theorem B11969693 : Blo 542804 11969693 := bstep (se 3 (by rfl) ⟨2244317, by rfl⟩ : syracuseStep 11969693 = 4488635) B4488635
theorem B6956711 : Blo 542804 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B2762423 : Blo 542804 2762423 := bstep (se 1 (by rfl) ⟨2071817, by rfl⟩ : syracuseStep 2762423 = 4143635) B4143635
theorem B4138775 : Blo 542804 4138775 := bstep (se 1 (by rfl) ⟨3104081, by rfl⟩ : syracuseStep 4138775 = 6208163) B6208163
theorem B1550299 : Blo 542804 1550299 := bstep (se 1 (by rfl) ⟨1162724, by rfl⟩ : syracuseStep 1550299 = 2325449) B2325449
theorem B11216879 : Blo 542804 11216879 := bstep (se 1 (by rfl) ⟨8412659, by rfl⟩ : syracuseStep 11216879 = 16825319) B16825319
theorem B1845287 : Blo 542804 1845287 := bstep (se 1 (by rfl) ⟨1383965, by rfl⟩ : syracuseStep 1845287 = 2767931) B2767931
theorem B1223009 : Blo 542804 1223009 := bstep (se 2 (by rfl) ⟨458628, by rfl⟩ : syracuseStep 1223009 = 917257) B917257
theorem B1223099 : Blo 542804 1223099 := bstep (se 1 (by rfl) ⟨917324, by rfl⟩ : syracuseStep 1223099 = 1834649) B1834649
theorem B25143803 : Blo 542804 25143803 := bstep (se 1 (by rfl) ⟨18857852, by rfl⟩ : syracuseStep 25143803 = 37715705) B37715705
theorem B11086409 : Blo 542804 11086409 := bstep (se 2 (by rfl) ⟨4157403, by rfl⟩ : syracuseStep 11086409 = 8314807) B8314807
theorem B9972305 : Blo 542804 9972305 := bstep (se 2 (by rfl) ⟨3739614, by rfl⟩ : syracuseStep 9972305 = 7479229) B7479229
theorem B2796383 : Blo 542804 2796383 := bstep (se 1 (by rfl) ⟨2097287, by rfl⟩ : syracuseStep 2796383 = 4194575) B4194575
theorem B17017937 : Blo 542804 17017937 := bstep (se 2 (by rfl) ⟨6381726, by rfl⟩ : syracuseStep 17017937 = 12763453) B12763453
theorem B18918521 : Blo 542804 18918521 := bstep (se 2 (by rfl) ⟨7094445, by rfl⟩ : syracuseStep 18918521 = 14188891) B14188891
theorem B1223891 : Blo 542804 1223891 := bstep (se 1 (by rfl) ⟨917918, by rfl⟩ : syracuseStep 1223891 = 1835837) B1835837
theorem B1224161 : Blo 542804 1224161 := bstep (se 2 (by rfl) ⟨459060, by rfl⟩ : syracuseStep 1224161 = 918121) B918121
theorem B1224359 : Blo 542804 1224359 := bstep (se 1 (by rfl) ⟨918269, by rfl⟩ : syracuseStep 1224359 = 1836539) B1836539
theorem B6992081 : Blo 542804 6992081 := bstep (se 2 (by rfl) ⟨2622030, by rfl⟩ : syracuseStep 6992081 = 5244061) B5244061
theorem B12103937 : Blo 542804 12103937 := bstep (se 2 (by rfl) ⟨4538976, by rfl⟩ : syracuseStep 12103937 = 9077953) B9077953
theorem B18886915 : Blo 542804 18886915 := bstep (se 1 (by rfl) ⟨14165186, by rfl⟩ : syracuseStep 18886915 = 28330373) B28330373
theorem B1749559 : Blo 542804 1749559 := bstep (se 1 (by rfl) ⟨1312169, by rfl⟩ : syracuseStep 1749559 = 2624339) B2624339
theorem B4141691 : Blo 542804 4141691 := bstep (se 1 (by rfl) ⟨3106268, by rfl⟩ : syracuseStep 4141691 = 6212537) B6212537
theorem B1225511 : Blo 542804 1225511 := bstep (se 1 (by rfl) ⟨919133, by rfl⟩ : syracuseStep 1225511 = 1838267) B1838267
theorem B1159991 : Blo 542804 1159991 := bstep (se 1 (by rfl) ⟨869993, by rfl⟩ : syracuseStep 1159991 = 1739987) B1739987
theorem B1225529 : Blo 542804 1225529 := bstep (se 2 (by rfl) ⟨459573, by rfl⟩ : syracuseStep 1225529 = 919147) B919147
theorem B3093329 : Blo 542804 3093329 := bstep (se 2 (by rfl) ⟨1159998, by rfl⟩ : syracuseStep 3093329 = 2319997) B2319997
theorem B1749995 : Blo 542804 1749995 := bstep (se 1 (by rfl) ⟨1312496, by rfl⟩ : syracuseStep 1749995 = 2624993) B2624993
theorem B4666511 : Blo 542804 4666511 := bstep (se 1 (by rfl) ⟨3499883, by rfl⟩ : syracuseStep 4666511 = 6999767) B6999767
theorem B1225889 : Blo 542804 1225889 := bstep (se 2 (by rfl) ⟨459708, by rfl⟩ : syracuseStep 1225889 = 919417) B919417
theorem B1226159 : Blo 542804 1226159 := bstep (se 1 (by rfl) ⟨919619, by rfl⟩ : syracuseStep 1226159 = 1839239) B1839239
theorem B1226267 : Blo 542804 1226267 := bstep (se 1 (by rfl) ⟨919700, by rfl⟩ : syracuseStep 1226267 = 1839401) B1839401
theorem B4142663 : Blo 542804 4142663 := bstep (se 1 (by rfl) ⟨3106997, by rfl⟩ : syracuseStep 4142663 = 6213995) B6213995
theorem B734927 : Blo 542804 734927 := bstep (se 1 (by rfl) ⟨551195, by rfl⟩ : syracuseStep 734927 = 1102391) B1102391
theorem B1226447 : Blo 542804 1226447 := bstep (se 1 (by rfl) ⟨919835, by rfl⟩ : syracuseStep 1226447 = 1839671) B1839671
theorem B1751327 : Blo 542804 1751327 := bstep (se 1 (by rfl) ⟨1313495, by rfl⟩ : syracuseStep 1751327 = 2626991) B2626991
theorem B1227239 : Blo 542804 1227239 := bstep (se 1 (by rfl) ⟨920429, by rfl⟩ : syracuseStep 1227239 = 1840859) B1840859
theorem B10598951 : Blo 542804 10598951 := bstep (se 1 (by rfl) ⟨7949213, by rfl⟩ : syracuseStep 10598951 = 15898427) B15898427
theorem B33634865 : Blo 542804 33634865 := bstep (se 2 (by rfl) ⟨12613074, by rfl⟩ : syracuseStep 33634865 = 25226149) B25226149
theorem B50969843 : Blo 542804 50969843 := bstep (se 1 (by rfl) ⟨38227382, by rfl⟩ : syracuseStep 50969843 = 76454765) B76454765
theorem B2800939 : Blo 542804 2800939 := bstep (se 1 (by rfl) ⟨2100704, by rfl⟩ : syracuseStep 2800939 = 4201409) B4201409
theorem B25182211 : Blo 542804 25182211 := bstep (se 1 (by rfl) ⟨18886658, by rfl⟩ : syracuseStep 25182211 = 37773317) B37773317
theorem B3097385 : Blo 542804 3097385 := bstep (se 2 (by rfl) ⟨1161519, by rfl⟩ : syracuseStep 3097385 = 2323039) B2323039
theorem B130892591 : Blo 542804 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B1165279 : Blo 542804 1165279 := bstep (se 1 (by rfl) ⟨873959, by rfl⟩ : syracuseStep 1165279 = 1747919) B1747919
theorem B542927 : Blo 542804 542927 := bstep (se 1 (by rfl) ⟨407195, by rfl⟩ : syracuseStep 542927 = 814391) B814391
theorem B543039 : Blo 542804 543039 := bstep (se 1 (by rfl) ⟨407279, by rfl⟩ : syracuseStep 543039 = 814559) B814559
theorem B543183 : Blo 542804 543183 := bstep (se 1 (by rfl) ⟨407387, by rfl⟩ : syracuseStep 543183 = 814775) B814775
theorem B543323 : Blo 542804 543323 := bstep (se 1 (by rfl) ⟨407492, by rfl⟩ : syracuseStep 543323 = 814985) B814985
theorem B543487 : Blo 542804 543487 := bstep (se 1 (by rfl) ⟨407615, by rfl⟩ : syracuseStep 543487 = 815231) B815231
theorem B1395625 : Blo 542804 1395625 := bstep (se 2 (by rfl) ⟨523359, by rfl⟩ : syracuseStep 1395625 = 1046719) B1046719
theorem B543911 : Blo 542804 543911 := bstep (se 1 (by rfl) ⟨407933, by rfl⟩ : syracuseStep 543911 = 815867) B815867
theorem B1035575 : Blo 542804 1035575 := bstep (se 1 (by rfl) ⟨776681, by rfl⟩ : syracuseStep 1035575 = 1553363) B1553363
theorem B544207 : Blo 542804 544207 := bstep (se 1 (by rfl) ⟨408155, by rfl⟩ : syracuseStep 544207 = 816311) B816311
theorem B544367 : Blo 542804 544367 := bstep (se 1 (by rfl) ⟨408275, by rfl⟩ : syracuseStep 544367 = 816551) B816551
theorem B544487 : Blo 542804 544487 := bstep (se 1 (by rfl) ⟨408365, by rfl⟩ : syracuseStep 544487 = 816731) B816731
theorem B872255 : Blo 542804 872255 := bstep (se 1 (by rfl) ⟨654191, by rfl⟩ : syracuseStep 872255 = 1308383) B1308383
theorem B544795 : Blo 542804 544795 := bstep (se 1 (by rfl) ⟨408596, by rfl⟩ : syracuseStep 544795 = 817193) B817193
theorem B544815 : Blo 542804 544815 := bstep (se 1 (by rfl) ⟨408611, by rfl⟩ : syracuseStep 544815 = 817223) B817223
theorem B10506347 : Blo 542804 10506347 := bstep (se 1 (by rfl) ⟨7879760, by rfl⟩ : syracuseStep 10506347 = 15759521) B15759521
theorem B5951663 : Blo 542804 5951663 := bstep (se 1 (by rfl) ⟨4463747, by rfl⟩ : syracuseStep 5951663 = 8927495) B8927495
theorem B13258961 : Blo 542804 13258961 := bstep (se 2 (by rfl) ⟨4972110, by rfl⟩ : syracuseStep 13258961 = 9944221) B9944221
theorem B545071 : Blo 542804 545071 := bstep (se 1 (by rfl) ⟨408803, by rfl⟩ : syracuseStep 545071 = 817607) B817607
theorem B545215 : Blo 542804 545215 := bstep (se 1 (by rfl) ⟨408911, by rfl⟩ : syracuseStep 545215 = 817823) B817823
theorem B545311 : Blo 542804 545311 := bstep (se 1 (by rfl) ⟨408983, by rfl⟩ : syracuseStep 545311 = 817967) B817967
theorem B545391 : Blo 542804 545391 := bstep (se 1 (by rfl) ⟨409043, by rfl⟩ : syracuseStep 545391 = 818087) B818087
theorem B545511 : Blo 542804 545511 := bstep (se 1 (by rfl) ⟨409133, by rfl⟩ : syracuseStep 545511 = 818267) B818267
theorem B5886857 : Blo 542804 5886857 := bstep (se 2 (by rfl) ⟨2207571, by rfl⟩ : syracuseStep 5886857 = 4415143) B4415143
theorem B545759 : Blo 542804 545759 := bstep (se 1 (by rfl) ⟨409319, by rfl⟩ : syracuseStep 545759 = 818639) B818639
theorem B546015 : Blo 542804 546015 := bstep (se 1 (by rfl) ⟨409511, by rfl⟩ : syracuseStep 546015 = 819023) B819023
theorem B546095 : Blo 542804 546095 := bstep (se 1 (by rfl) ⟨409571, by rfl⟩ : syracuseStep 546095 = 819143) B819143
theorem B546335 : Blo 542804 546335 := bstep (se 1 (by rfl) ⟨409751, by rfl⟩ : syracuseStep 546335 = 819503) B819503
theorem B1660495 : Blo 542804 1660495 := bstep (se 1 (by rfl) ⟨1245371, by rfl⟩ : syracuseStep 1660495 = 2490743) B2490743
theorem B1037929 : Blo 542804 1037929 := bstep (se 2 (by rfl) ⟨389223, by rfl⟩ : syracuseStep 1037929 = 778447) B778447
theorem B612031 : Blo 542804 612031 := bstep (se 1 (by rfl) ⟨459023, by rfl⟩ : syracuseStep 612031 = 918047) B918047
theorem B546495 : Blo 542804 546495 := bstep (se 1 (by rfl) ⟨409871, by rfl⟩ : syracuseStep 546495 = 819743) B819743
theorem B13948685 : Blo 542804 13948685 := bstep (se 3 (by rfl) ⟨2615378, by rfl⟩ : syracuseStep 13948685 = 5230757) B5230757
theorem B775975 : Blo 542804 775975 := bstep (se 1 (by rfl) ⟨581981, by rfl⟩ : syracuseStep 775975 = 1163963) B1163963
theorem B2611073 : Blo 542804 2611073 := bstep (se 2 (by rfl) ⟨979152, by rfl⟩ : syracuseStep 2611073 = 1958305) B1958305
theorem B22403537 : Blo 542804 22403537 := bstep (se 2 (by rfl) ⟨8401326, by rfl⟩ : syracuseStep 22403537 = 16802653) B16802653
theorem B6969833 : Blo 542804 6969833 := bstep (se 2 (by rfl) ⟨2613687, by rfl⟩ : syracuseStep 6969833 = 5227375) B5227375
theorem B13228595 : Blo 542804 13228595 := bstep (se 1 (by rfl) ⟨9921446, by rfl⟩ : syracuseStep 13228595 = 19842893) B19842893
theorem B2939449 : Blo 542804 2939449 := bstep (se 2 (by rfl) ⟨1102293, by rfl⟩ : syracuseStep 2939449 = 2204587) B2204587
theorem B613183 : Blo 542804 613183 := bstep (se 1 (by rfl) ⟨459887, by rfl⟩ : syracuseStep 613183 = 919775) B919775
theorem B7428989 : Blo 542804 7428989 := bstep (se 3 (by rfl) ⟨1392935, by rfl⟩ : syracuseStep 7428989 = 2785871) B2785871
theorem B6216911 : Blo 542804 6216911 := bstep (se 1 (by rfl) ⟨4662683, by rfl⟩ : syracuseStep 6216911 = 9325367) B9325367
theorem B613759 : Blo 542804 613759 := bstep (se 1 (by rfl) ⟨460319, by rfl⟩ : syracuseStep 613759 = 920639) B920639
theorem B6381359 : Blo 542804 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B3497833 : Blo 542804 3497833 := bstep (se 2 (by rfl) ⟨1311687, by rfl⟩ : syracuseStep 3497833 = 2623375) B2623375
theorem B2941181 : Blo 542804 2941181 := bstep (se 3 (by rfl) ⟨551471, by rfl⟩ : syracuseStep 2941181 = 1102943) B1102943
theorem B2122247 : Blo 542804 2122247 := bstep (se 1 (by rfl) ⟨1591685, by rfl⟩ : syracuseStep 2122247 = 3183371) B3183371
theorem B2614457 : Blo 542804 2614457 := bstep (se 2 (by rfl) ⟨980421, by rfl⟩ : syracuseStep 2614457 = 1960843) B1960843
theorem B582887 : Blo 542804 582887 := bstep (se 1 (by rfl) ⟨437165, by rfl⟩ : syracuseStep 582887 = 874331) B874331
theorem B5891869 : Blo 542804 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B101673053 : Blo 542804 101673053 := bstep (se 3 (by rfl) ⟨19063697, by rfl⟩ : syracuseStep 101673053 = 38127395) B38127395
theorem B1469011 : Blo 542804 1469011 := bstep (se 1 (by rfl) ⟨1101758, by rfl⟩ : syracuseStep 1469011 = 2203517) B2203517
theorem B1305191 : Blo 542804 1305191 := bstep (se 1 (by rfl) ⟨978893, by rfl⟩ : syracuseStep 1305191 = 1957787) B1957787
theorem B814217 : Blo 542804 814217 := bstep (se 2 (by rfl) ⟨305331, by rfl⟩ : syracuseStep 814217 = 610663) B610663
theorem B814271 : Blo 542804 814271 := bstep (se 1 (by rfl) ⟨610703, by rfl⟩ : syracuseStep 814271 = 1221407) B1221407
theorem B814811 : Blo 542804 814811 := bstep (se 1 (by rfl) ⟨611108, by rfl⟩ : syracuseStep 814811 = 1222217) B1222217
theorem B815081 : Blo 542804 815081 := bstep (se 2 (by rfl) ⟨305655, by rfl⟩ : syracuseStep 815081 = 611311) B611311
theorem B815099 : Blo 542804 815099 := bstep (se 1 (by rfl) ⟨611324, by rfl⟩ : syracuseStep 815099 = 1222649) B1222649
theorem B4124681 : Blo 542804 4124681 := bstep (se 2 (by rfl) ⟨1546755, by rfl⟩ : syracuseStep 4124681 = 3093511) B3093511
theorem B815135 : Blo 542804 815135 := bstep (se 1 (by rfl) ⟨611351, by rfl⟩ : syracuseStep 815135 = 1222703) B1222703
theorem B815159 : Blo 542804 815159 := bstep (se 1 (by rfl) ⟨611369, by rfl⟩ : syracuseStep 815159 = 1222739) B1222739
theorem B4649015 : Blo 542804 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B815279 : Blo 542804 815279 := bstep (se 1 (by rfl) ⟨611459, by rfl⟩ : syracuseStep 815279 = 1222919) B1222919
theorem B3109049 : Blo 542804 3109049 := bstep (se 2 (by rfl) ⟨1165893, by rfl⟩ : syracuseStep 3109049 = 2331787) B2331787
theorem B1962227 : Blo 542804 1962227 := bstep (se 1 (by rfl) ⟨1471670, by rfl⟩ : syracuseStep 1962227 = 2943341) B2943341
theorem B815483 : Blo 542804 815483 := bstep (se 1 (by rfl) ⟨611612, by rfl⟩ : syracuseStep 815483 = 1223225) B1223225
theorem B815753 : Blo 542804 815753 := bstep (se 2 (by rfl) ⟨305907, by rfl⟩ : syracuseStep 815753 = 611815) B611815
theorem B10089131 : Blo 542804 10089131 := bstep (se 1 (by rfl) ⟨7566848, by rfl⟩ : syracuseStep 10089131 = 15133697) B15133697
theorem B815963 : Blo 542804 815963 := bstep (se 1 (by rfl) ⟨611972, by rfl⟩ : syracuseStep 815963 = 1223945) B1223945
theorem B815993 : Blo 542804 815993 := bstep (se 2 (by rfl) ⟨305997, by rfl⟩ : syracuseStep 815993 = 611995) B611995
theorem B816623 : Blo 542804 816623 := bstep (se 1 (by rfl) ⟨612467, by rfl⟩ : syracuseStep 816623 = 1224935) B1224935
theorem B652903 : Blo 542804 652903 := bstep (se 1 (by rfl) ⟨489677, by rfl⟩ : syracuseStep 652903 = 979355) B979355
theorem B816743 : Blo 542804 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B1374023 : Blo 542804 1374023 := bstep (se 1 (by rfl) ⟨1030517, by rfl⟩ : syracuseStep 1374023 = 2061035) B2061035
theorem B1374043 : Blo 542804 1374043 := bstep (se 1 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 1374043 = 2061065) B2061065
theorem B817199 : Blo 542804 817199 := bstep (se 1 (by rfl) ⟨612899, by rfl⟩ : syracuseStep 817199 = 1225799) B1225799
theorem B7469111 : Blo 542804 7469111 := bstep (se 1 (by rfl) ⟨5601833, by rfl⟩ : syracuseStep 7469111 = 11203667) B11203667
theorem B3537017 : Blo 542804 3537017 := bstep (se 2 (by rfl) ⟨1326381, by rfl⟩ : syracuseStep 3537017 = 2652763) B2652763
theorem B1374347 : Blo 542804 1374347 := bstep (se 1 (by rfl) ⟨1030760, by rfl⟩ : syracuseStep 1374347 = 2061521) B2061521
theorem B817319 : Blo 542804 817319 := bstep (se 1 (by rfl) ⟨612989, by rfl⟩ : syracuseStep 817319 = 1225979) B1225979
theorem B817463 : Blo 542804 817463 := bstep (se 1 (by rfl) ⟨613097, by rfl⟩ : syracuseStep 817463 = 1226195) B1226195
theorem B2750921 : Blo 542804 2750921 := bstep (se 2 (by rfl) ⟨1031595, by rfl⟩ : syracuseStep 2750921 = 2063191) B2063191
theorem B817643 : Blo 542804 817643 := bstep (se 1 (by rfl) ⟨613232, by rfl⟩ : syracuseStep 817643 = 1226465) B1226465
theorem B817991 : Blo 542804 817991 := bstep (se 1 (by rfl) ⟨613493, by rfl⟩ : syracuseStep 817991 = 1226987) B1226987
theorem B4127597 : Blo 542804 4127597 := bstep (se 3 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 4127597 = 1547849) B1547849
theorem B916447 : Blo 542804 916447 := bstep (se 1 (by rfl) ⟨687335, by rfl⟩ : syracuseStep 916447 = 1374671) B1374671
theorem B687199 : Blo 542804 687199 := bstep (se 1 (by rfl) ⟨515399, by rfl⟩ : syracuseStep 687199 = 1030799) B1030799
theorem B1572065 : Blo 542804 1572065 := bstep (se 2 (by rfl) ⟨589524, by rfl⟩ : syracuseStep 1572065 = 1179049) B1179049
theorem B2948339 : Blo 542804 2948339 := bstep (se 1 (by rfl) ⟨2211254, by rfl⟩ : syracuseStep 2948339 = 4422509) B4422509
theorem B3309167 : Blo 542804 3309167 := bstep (se 1 (by rfl) ⟨2481875, by rfl⟩ : syracuseStep 3309167 = 4963751) B4963751
theorem B1277561 : Blo 542804 1277561 := bstep (se 2 (by rfl) ⟨479085, by rfl⟩ : syracuseStep 1277561 = 958171) B958171
theorem B917129 : Blo 542804 917129 := bstep (se 2 (by rfl) ⟨343923, by rfl⟩ : syracuseStep 917129 = 687847) B687847
theorem B818825 : Blo 542804 818825 := bstep (se 2 (by rfl) ⟨307059, by rfl⟩ : syracuseStep 818825 = 614119) B614119
theorem B818855 : Blo 542804 818855 := bstep (se 1 (by rfl) ⟨614141, by rfl⟩ : syracuseStep 818855 = 1228283) B1228283
theorem B1375967 : Blo 542804 1375967 := bstep (se 1 (by rfl) ⟨1031975, by rfl⟩ : syracuseStep 1375967 = 2063951) B2063951
theorem B818975 : Blo 542804 818975 := bstep (se 1 (by rfl) ⟨614231, by rfl⟩ : syracuseStep 818975 = 1228463) B1228463
theorem B1310555 : Blo 542804 1310555 := bstep (se 1 (by rfl) ⟨982916, by rfl⟩ : syracuseStep 1310555 = 1965833) B1965833
theorem B819035 : Blo 542804 819035 := bstep (se 1 (by rfl) ⟨614276, by rfl⟩ : syracuseStep 819035 = 1228553) B1228553
theorem B1834919 : Blo 542804 1834919 := bstep (se 1 (by rfl) ⟨1376189, by rfl⟩ : syracuseStep 1834919 = 2752379) B2752379
theorem B3735517 : Blo 542804 3735517 := bstep (se 3 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 3735517 = 1400819) B1400819
theorem B1835135 : Blo 542804 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B2064923 : Blo 542804 2064923 := bstep (se 1 (by rfl) ⟨1548692, by rfl⟩ : syracuseStep 2064923 = 3097385) B3097385
theorem B2064953 : Blo 542804 2064953 := bstep (se 2 (by rfl) ⟨774357, by rfl⟩ : syracuseStep 2064953 = 1548715) B1548715
theorem B2753351 : Blo 542804 2753351 := bstep (se 1 (by rfl) ⟨2065013, by rfl⟩ : syracuseStep 2753351 = 4130027) B4130027
theorem B1377607 : Blo 542804 1377607 := bstep (se 1 (by rfl) ⟨1033205, by rfl⟩ : syracuseStep 1377607 = 2066411) B2066411
theorem B100730213 : Blo 542804 100730213 := bstep (se 4 (by rfl) ⟨9443457, by rfl⟩ : syracuseStep 100730213 = 18886915) B18886915
theorem B919039 : Blo 542804 919039 := bstep (se 1 (by rfl) ⟨689279, by rfl⟩ : syracuseStep 919039 = 1378559) B1378559
theorem B26904349 : Blo 542804 26904349 := bstep (se 3 (by rfl) ⟨5044565, by rfl⟩ : syracuseStep 26904349 = 10089131) B10089131
theorem B1836971 : Blo 542804 1836971 := bstep (se 1 (by rfl) ⟨1377728, by rfl⟩ : syracuseStep 1836971 = 2755457) B2755457
theorem B1837025 : Blo 542804 1837025 := bstep (se 2 (by rfl) ⟨688884, by rfl⟩ : syracuseStep 1837025 = 1377769) B1377769
theorem B349046909 : Blo 542804 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B690383 : Blo 542804 690383 := bstep (se 1 (by rfl) ⟨517787, by rfl⟩ : syracuseStep 690383 = 1035575) B1035575
theorem B1050983 : Blo 542804 1050983 := bstep (se 1 (by rfl) ⟨788237, by rfl⟩ : syracuseStep 1050983 = 1576475) B1576475
theorem B2067065 : Blo 542804 2067065 := bstep (se 2 (by rfl) ⟨775149, by rfl⟩ : syracuseStep 2067065 = 1550299) B1550299
theorem B920207 : Blo 542804 920207 := bstep (se 1 (by rfl) ⟨690155, by rfl⟩ : syracuseStep 920207 = 1380311) B1380311
theorem B1837727 : Blo 542804 1837727 := bstep (se 1 (by rfl) ⟨1378295, by rfl⟩ : syracuseStep 1837727 = 2756591) B2756591
theorem B3967775 : Blo 542804 3967775 := bstep (se 1 (by rfl) ⟨2975831, by rfl⟩ : syracuseStep 3967775 = 5951663) B5951663
theorem B1380635 : Blo 542804 1380635 := bstep (se 1 (by rfl) ⟨1035476, by rfl⟩ : syracuseStep 1380635 = 2070953) B2070953
theorem B8819063 : Blo 542804 8819063 := bstep (se 1 (by rfl) ⟨6614297, by rfl⟩ : syracuseStep 8819063 = 13228595) B13228595
theorem B4952659 : Blo 542804 4952659 := bstep (se 1 (by rfl) ⟨3714494, by rfl⟩ : syracuseStep 4952659 = 7428989) B7428989
theorem B922279 : Blo 542804 922279 := bstep (se 1 (by rfl) ⟨691709, by rfl⟩ : syracuseStep 922279 = 1383419) B1383419
theorem B2364191 : Blo 542804 2364191 := bstep (se 1 (by rfl) ⟨1773143, by rfl⟩ : syracuseStep 2364191 = 3546287) B3546287
theorem B922495 : Blo 542804 922495 := bstep (se 1 (by rfl) ⟨691871, by rfl⟩ : syracuseStep 922495 = 1383743) B1383743
theorem B1414831 : Blo 542804 1414831 := bstep (se 1 (by rfl) ⟨1061123, by rfl⟩ : syracuseStep 1414831 = 2122247) B2122247
theorem B1840967 : Blo 542804 1840967 := bstep (se 1 (by rfl) ⟨1380725, by rfl⟩ : syracuseStep 1840967 = 2761451) B2761451
theorem B2332745 : Blo 542804 2332745 := bstep (se 2 (by rfl) ⟨874779, by rfl⟩ : syracuseStep 2332745 = 1749559) B1749559
theorem B1742971 : Blo 542804 1742971 := bstep (se 1 (by rfl) ⟨1307228, by rfl⟩ : syracuseStep 1742971 = 2614457) B2614457
theorem B3938753 : Blo 542804 3938753 := bstep (se 2 (by rfl) ⟨1477032, by rfl⟩ : syracuseStep 3938753 = 2954065) B2954065
theorem B1841615 : Blo 542804 1841615 := bstep (se 1 (by rfl) ⟨1381211, by rfl⟩ : syracuseStep 1841615 = 2762423) B2762423
theorem B2759183 : Blo 542804 2759183 := bstep (se 1 (by rfl) ⟨2069387, by rfl⟩ : syracuseStep 2759183 = 4138775) B4138775
theorem B7477919 : Blo 542804 7477919 := bstep (se 1 (by rfl) ⟨5608439, by rfl⟩ : syracuseStep 7477919 = 11216879) B11216879
theorem B3480509 : Blo 542804 3480509 := bstep (se 3 (by rfl) ⟨652595, by rfl⟩ : syracuseStep 3480509 = 1305191) B1305191
theorem B11345291 : Blo 542804 11345291 := bstep (se 1 (by rfl) ⟨8508968, by rfl⟩ : syracuseStep 11345291 = 17017937) B17017937
theorem B1383905 : Blo 542804 1383905 := bstep (se 2 (by rfl) ⟨518964, by rfl⟩ : syracuseStep 1383905 = 1037929) B1037929
theorem B9051857 : Blo 542804 9051857 := bstep (se 2 (by rfl) ⟨3394446, by rfl⟩ : syracuseStep 9051857 = 6788893) B6788893
theorem B2072699 : Blo 542804 2072699 := bstep (se 1 (by rfl) ⟨1554524, by rfl⟩ : syracuseStep 2072699 = 3109049) B3109049
theorem B4661387 : Blo 542804 4661387 := bstep (se 1 (by rfl) ⟨3496040, by rfl⟩ : syracuseStep 4661387 = 6992081) B6992081
theorem B8069291 : Blo 542804 8069291 := bstep (se 1 (by rfl) ⟨6051968, by rfl⟩ : syracuseStep 8069291 = 12103937) B12103937
theorem B2761127 : Blo 542804 2761127 := bstep (se 1 (by rfl) ⟨2070845, by rfl⟩ : syracuseStep 2761127 = 4141691) B4141691
theorem B3482149 : Blo 542804 3482149 := bstep (se 4 (by rfl) ⟨326451, by rfl⟩ : syracuseStep 3482149 = 652903) B652903
theorem B1843937 : Blo 542804 1843937 := bstep (se 2 (by rfl) ⟨691476, by rfl⟩ : syracuseStep 1843937 = 1382953) B1382953
theorem B2761775 : Blo 542804 2761775 := bstep (se 1 (by rfl) ⟨2071331, by rfl⟩ : syracuseStep 2761775 = 4142663) B4142663
theorem B1844477 : Blo 542804 1844477 := bstep (se 3 (by rfl) ⟨345839, by rfl⟩ : syracuseStep 1844477 = 691679) B691679
theorem B1221929 : Blo 542804 1221929 := bstep (se 2 (by rfl) ⟨458223, by rfl⟩ : syracuseStep 1221929 = 916447) B916447
theorem B22423243 : Blo 542804 22423243 := bstep (se 1 (by rfl) ⟨16817432, by rfl⟩ : syracuseStep 22423243 = 33634865) B33634865
theorem B2206111 : Blo 542804 2206111 := bstep (se 1 (by rfl) ⟨1654583, by rfl⟩ : syracuseStep 2206111 = 3309167) B3309167
theorem B4663777 : Blo 542804 4663777 := bstep (se 2 (by rfl) ⟨1748916, by rfl⟩ : syracuseStep 4663777 = 3497833) B3497833
theorem B1223279 : Blo 542804 1223279 := bstep (se 1 (by rfl) ⟨917459, by rfl⟩ : syracuseStep 1223279 = 1834919) B1834919
theorem B1059625 : Blo 542804 1059625 := bstep (se 2 (by rfl) ⟨397359, by rfl⟩ : syracuseStep 1059625 = 794719) B794719
theorem B1553705 : Blo 542804 1553705 := bstep (se 2 (by rfl) ⟨582639, by rfl⟩ : syracuseStep 1553705 = 1165279) B1165279
theorem B1554365 : Blo 542804 1554365 := bstep (se 3 (by rfl) ⟨291443, by rfl⟩ : syracuseStep 1554365 = 582887) B582887
theorem B1161631 : Blo 542804 1161631 := bstep (se 1 (by rfl) ⟨871223, by rfl⟩ : syracuseStep 1161631 = 1742447) B1742447
theorem B4144607 : Blo 542804 4144607 := bstep (se 1 (by rfl) ⟨3108455, by rfl⟩ : syracuseStep 4144607 = 6216911) B6216911
theorem B6962861 : Blo 542804 6962861 := bstep (se 3 (by rfl) ⟨1305536, by rfl⟩ : syracuseStep 6962861 = 2611073) B2611073
theorem B6996077 : Blo 542804 6996077 := bstep (se 3 (by rfl) ⟨1311764, by rfl⟩ : syracuseStep 6996077 = 2623529) B2623529
theorem B1229111 : Blo 542804 1229111 := bstep (se 1 (by rfl) ⟨921833, by rfl⟩ : syracuseStep 1229111 = 1843667) B1843667
theorem B7979795 : Blo 542804 7979795 := bstep (se 1 (by rfl) ⟨5984846, by rfl⟩ : syracuseStep 7979795 = 11969693) B11969693
theorem B4637807 : Blo 542804 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B1230191 : Blo 542804 1230191 := bstep (se 1 (by rfl) ⟨922643, by rfl⟩ : syracuseStep 1230191 = 1845287) B1845287
theorem B67782035 : Blo 542804 67782035 := bstep (se 1 (by rfl) ⟨50836526, by rfl⟩ : syracuseStep 67782035 = 101673053) B101673053
theorem B16762535 : Blo 542804 16762535 := bstep (se 1 (by rfl) ⟨12571901, by rfl⟩ : syracuseStep 16762535 = 25143803) B25143803
theorem B7390939 : Blo 542804 7390939 := bstep (se 1 (by rfl) ⟨5543204, by rfl⟩ : syracuseStep 7390939 = 11086409) B11086409
theorem B542811 : Blo 542804 542811 := bstep (se 1 (by rfl) ⟨407108, by rfl⟩ : syracuseStep 542811 = 814217) B814217
theorem B2213993 : Blo 542804 2213993 := bstep (se 2 (by rfl) ⟨830247, by rfl⟩ : syracuseStep 2213993 = 1660495) B1660495
theorem B542847 : Blo 542804 542847 := bstep (se 1 (by rfl) ⟨407135, by rfl⟩ : syracuseStep 542847 = 814271) B814271
theorem B1034633 : Blo 542804 1034633 := bstep (se 2 (by rfl) ⟨387987, by rfl⟩ : syracuseStep 1034633 = 775975) B775975
theorem B543207 : Blo 542804 543207 := bstep (se 1 (by rfl) ⟨407405, by rfl⟩ : syracuseStep 543207 = 814811) B814811
theorem B543387 : Blo 542804 543387 := bstep (se 1 (by rfl) ⟨407540, by rfl⟩ : syracuseStep 543387 = 815081) B815081
theorem B543399 : Blo 542804 543399 := bstep (se 1 (by rfl) ⟨407549, by rfl⟩ : syracuseStep 543399 = 815099) B815099
theorem B543423 : Blo 542804 543423 := bstep (se 1 (by rfl) ⟨407567, by rfl⟩ : syracuseStep 543423 = 815135) B815135
theorem B543439 : Blo 542804 543439 := bstep (se 1 (by rfl) ⟨407579, by rfl⟩ : syracuseStep 543439 = 815159) B815159
theorem B3099343 : Blo 542804 3099343 := bstep (se 1 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 3099343 = 4649015) B4649015
theorem B543519 : Blo 542804 543519 := bstep (se 1 (by rfl) ⟨407639, by rfl⟩ : syracuseStep 543519 = 815279) B815279
theorem B543655 : Blo 542804 543655 := bstep (se 1 (by rfl) ⟨407741, by rfl⟩ : syracuseStep 543655 = 815483) B815483
theorem B543835 : Blo 542804 543835 := bstep (se 1 (by rfl) ⟨407876, by rfl⟩ : syracuseStep 543835 = 815753) B815753
theorem B773327 : Blo 542804 773327 := bstep (se 1 (by rfl) ⟨579995, by rfl⟩ : syracuseStep 773327 = 1159991) B1159991
theorem B543975 : Blo 542804 543975 := bstep (se 1 (by rfl) ⟨407981, by rfl⟩ : syracuseStep 543975 = 815963) B815963
theorem B543995 : Blo 542804 543995 := bstep (se 1 (by rfl) ⟨407996, by rfl⟩ : syracuseStep 543995 = 815993) B815993
theorem B1166663 : Blo 542804 1166663 := bstep (se 1 (by rfl) ⟨874997, by rfl⟩ : syracuseStep 1166663 = 1749995) B1749995
theorem B3919265 : Blo 542804 3919265 := bstep (se 2 (by rfl) ⟨1469724, by rfl⟩ : syracuseStep 3919265 = 2939449) B2939449
theorem B544415 : Blo 542804 544415 := bstep (se 1 (by rfl) ⟨408311, by rfl⟩ : syracuseStep 544415 = 816623) B816623
theorem B544495 : Blo 542804 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B544799 : Blo 542804 544799 := bstep (se 1 (by rfl) ⟨408599, by rfl⟩ : syracuseStep 544799 = 817199) B817199
theorem B544879 : Blo 542804 544879 := bstep (se 1 (by rfl) ⟨408659, by rfl⟩ : syracuseStep 544879 = 817319) B817319
theorem B1167551 : Blo 542804 1167551 := bstep (se 1 (by rfl) ⟨875663, by rfl⟩ : syracuseStep 1167551 = 1751327) B1751327
theorem B544975 : Blo 542804 544975 := bstep (se 1 (by rfl) ⟨408731, by rfl⟩ : syracuseStep 544975 = 817463) B817463
theorem B545095 : Blo 542804 545095 := bstep (se 1 (by rfl) ⟨408821, by rfl⟩ : syracuseStep 545095 = 817643) B817643
theorem B7065967 : Blo 542804 7065967 := bstep (se 1 (by rfl) ⟨5299475, by rfl⟩ : syracuseStep 7065967 = 10598951) B10598951
theorem B545327 : Blo 542804 545327 := bstep (se 1 (by rfl) ⟨408995, by rfl⟩ : syracuseStep 545327 = 817991) B817991
theorem B611419 : Blo 542804 611419 := bstep (se 1 (by rfl) ⟨458564, by rfl⟩ : syracuseStep 611419 = 917129) B917129
theorem B545883 : Blo 542804 545883 := bstep (se 1 (by rfl) ⟨409412, by rfl⟩ : syracuseStep 545883 = 818825) B818825
theorem B545903 : Blo 542804 545903 := bstep (se 1 (by rfl) ⟨409427, by rfl⟩ : syracuseStep 545903 = 818855) B818855
theorem B545983 : Blo 542804 545983 := bstep (se 1 (by rfl) ⟨409487, by rfl⟩ : syracuseStep 545983 = 818975) B818975
theorem B873703 : Blo 542804 873703 := bstep (se 1 (by rfl) ⟨655277, by rfl⟩ : syracuseStep 873703 = 1310555) B1310555
theorem B546023 : Blo 542804 546023 := bstep (se 1 (by rfl) ⟨409517, by rfl⟩ : syracuseStep 546023 = 819035) B819035
theorem B33576281 : Blo 542804 33576281 := bstep (se 2 (by rfl) ⟨12591105, by rfl⟩ : syracuseStep 33576281 = 25182211) B25182211
theorem B873895 : Blo 542804 873895 := bstep (se 1 (by rfl) ⟨655421, by rfl⟩ : syracuseStep 873895 = 1310843) B1310843
theorem B546303 : Blo 542804 546303 := bstep (se 1 (by rfl) ⟨409727, by rfl⟩ : syracuseStep 546303 = 819455) B819455
theorem B3102259 : Blo 542804 3102259 := bstep (se 1 (by rfl) ⟨2326694, by rfl⟩ : syracuseStep 3102259 = 4653389) B4653389
theorem B546407 : Blo 542804 546407 := bstep (se 1 (by rfl) ⟨409805, by rfl⟩ : syracuseStep 546407 = 819611) B819611
theorem B546687 : Blo 542804 546687 := bstep (se 1 (by rfl) ⟨410015, by rfl⟩ : syracuseStep 546687 = 820031) B820031
theorem B546783 : Blo 542804 546783 := bstep (se 1 (by rfl) ⟨410087, by rfl⟩ : syracuseStep 546783 = 820175) B820175
theorem B8936813 : Blo 542804 8936813 := bstep (se 3 (by rfl) ⟨1675652, by rfl⟩ : syracuseStep 8936813 = 3351305) B3351305
theorem B7855825 : Blo 542804 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B581503 : Blo 542804 581503 := bstep (se 1 (by rfl) ⟨436127, by rfl⟩ : syracuseStep 581503 = 872255) B872255
theorem B7004231 : Blo 542804 7004231 := bstep (se 1 (by rfl) ⟨5253173, by rfl⟩ : syracuseStep 7004231 = 10506347) B10506347
theorem B8839307 : Blo 542804 8839307 := bstep (se 1 (by rfl) ⟨6629480, by rfl⟩ : syracuseStep 8839307 = 13258961) B13258961
theorem B4415759 : Blo 542804 4415759 := bstep (se 1 (by rfl) ⟨3311819, by rfl⟩ : syracuseStep 4415759 = 6623639) B6623639
theorem B3924571 : Blo 542804 3924571 := bstep (se 1 (by rfl) ⟨2943428, by rfl⟩ : syracuseStep 3924571 = 5886857) B5886857
theorem B1958681 : Blo 542804 1958681 := bstep (se 2 (by rfl) ⟨734505, by rfl⟩ : syracuseStep 1958681 = 1469011) B1469011
theorem B9299123 : Blo 542804 9299123 := bstep (se 1 (by rfl) ⟨6974342, by rfl⟩ : syracuseStep 9299123 = 13948685) B13948685
theorem B1860833 : Blo 542804 1860833 := bstep (se 2 (by rfl) ⟨697812, by rfl⟩ : syracuseStep 1860833 = 1395625) B1395625
theorem B14935691 : Blo 542804 14935691 := bstep (se 1 (by rfl) ⟨11201768, by rfl⟩ : syracuseStep 14935691 = 22403537) B22403537
theorem B4646555 : Blo 542804 4646555 := bstep (se 1 (by rfl) ⟨3484916, by rfl⟩ : syracuseStep 4646555 = 6969833) B6969833
theorem B1959805 : Blo 542804 1959805 := bstep (se 3 (by rfl) ⟨367463, by rfl⟩ : syracuseStep 1959805 = 734927) B734927
theorem B4254239 : Blo 542804 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B551711 : Blo 542804 551711 := bstep (se 1 (by rfl) ⟨413783, by rfl⟩ : syracuseStep 551711 = 827567) B827567
theorem B1960787 : Blo 542804 1960787 := bstep (se 1 (by rfl) ⟨1470590, by rfl⟩ : syracuseStep 1960787 = 2941181) B2941181
theorem B3828959 : Blo 542804 3828959 := bstep (se 1 (by rfl) ⟨2871719, by rfl⟩ : syracuseStep 3828959 = 5743439) B5743439
theorem B814463 : Blo 542804 814463 := bstep (se 1 (by rfl) ⟨610847, by rfl⟩ : syracuseStep 814463 = 1221695) B1221695
theorem B815339 : Blo 542804 815339 := bstep (se 1 (by rfl) ⟨611504, by rfl⟩ : syracuseStep 815339 = 1223009) B1223009
theorem B815399 : Blo 542804 815399 := bstep (se 1 (by rfl) ⟨611549, by rfl⟩ : syracuseStep 815399 = 1223099) B1223099
theorem B6648203 : Blo 542804 6648203 := bstep (se 1 (by rfl) ⟨4986152, by rfl⟩ : syracuseStep 6648203 = 9972305) B9972305
theorem B1864255 : Blo 542804 1864255 := bstep (se 1 (by rfl) ⟨1398191, by rfl⟩ : syracuseStep 1864255 = 2796383) B2796383
theorem B12612347 : Blo 542804 12612347 := bstep (se 1 (by rfl) ⟨9459260, by rfl⟩ : syracuseStep 12612347 = 18918521) B18918521
theorem B815927 : Blo 542804 815927 := bstep (se 1 (by rfl) ⟨611945, by rfl⟩ : syracuseStep 815927 = 1223891) B1223891
theorem B816041 : Blo 542804 816041 := bstep (se 2 (by rfl) ⟨306015, by rfl⟩ : syracuseStep 816041 = 612031) B612031
theorem B816107 : Blo 542804 816107 := bstep (se 1 (by rfl) ⟨612080, by rfl⟩ : syracuseStep 816107 = 1224161) B1224161
theorem B816239 : Blo 542804 816239 := bstep (se 1 (by rfl) ⟨612179, by rfl⟩ : syracuseStep 816239 = 1224359) B1224359
theorem B1832057 : Blo 542804 1832057 := bstep (se 2 (by rfl) ⟨687021, by rfl⟩ : syracuseStep 1832057 = 1374043) B1374043
theorem B2749787 : Blo 542804 2749787 := bstep (se 1 (by rfl) ⟨2062340, by rfl⟩ : syracuseStep 2749787 = 4124681) B4124681
theorem B1308151 : Blo 542804 1308151 := bstep (se 1 (by rfl) ⟨981113, by rfl⟩ : syracuseStep 1308151 = 1962227) B1962227
theorem B817007 : Blo 542804 817007 := bstep (se 1 (by rfl) ⟨612755, by rfl⟩ : syracuseStep 817007 = 1225511) B1225511
theorem B817019 : Blo 542804 817019 := bstep (se 1 (by rfl) ⟨612764, by rfl⟩ : syracuseStep 817019 = 1225529) B1225529
theorem B2062219 : Blo 542804 2062219 := bstep (se 1 (by rfl) ⟨1546664, by rfl⟩ : syracuseStep 2062219 = 3093329) B3093329
theorem B3111007 : Blo 542804 3111007 := bstep (se 1 (by rfl) ⟨2333255, by rfl⟩ : syracuseStep 3111007 = 4666511) B4666511
theorem B817259 : Blo 542804 817259 := bstep (se 1 (by rfl) ⟨612944, by rfl⟩ : syracuseStep 817259 = 1225889) B1225889
theorem B817439 : Blo 542804 817439 := bstep (se 1 (by rfl) ⟨613079, by rfl⟩ : syracuseStep 817439 = 1226159) B1226159
theorem B817511 : Blo 542804 817511 := bstep (se 1 (by rfl) ⟨613133, by rfl⟩ : syracuseStep 817511 = 1226267) B1226267
theorem B817577 : Blo 542804 817577 := bstep (se 2 (by rfl) ⟨306591, by rfl⟩ : syracuseStep 817577 = 613183) B613183
theorem B817631 : Blo 542804 817631 := bstep (se 1 (by rfl) ⟨613223, by rfl⟩ : syracuseStep 817631 = 1226447) B1226447
theorem B916015 : Blo 542804 916015 := bstep (se 1 (by rfl) ⟨687011, by rfl⟩ : syracuseStep 916015 = 1374023) B1374023
theorem B2063009 : Blo 542804 2063009 := bstep (se 2 (by rfl) ⟨773628, by rfl⟩ : syracuseStep 2063009 = 1547257) B1547257
theorem B4979407 : Blo 542804 4979407 := bstep (se 1 (by rfl) ⟨3734555, by rfl⟩ : syracuseStep 4979407 = 7469111) B7469111
theorem B2358011 : Blo 542804 2358011 := bstep (se 1 (by rfl) ⟨1768508, by rfl⟩ : syracuseStep 2358011 = 3537017) B3537017
theorem B916231 : Blo 542804 916231 := bstep (se 1 (by rfl) ⟨687173, by rfl⟩ : syracuseStep 916231 = 1374347) B1374347
theorem B916265 : Blo 542804 916265 := bstep (se 2 (by rfl) ⟨343599, by rfl⟩ : syracuseStep 916265 = 687199) B687199
theorem B1833947 : Blo 542804 1833947 := bstep (se 1 (by rfl) ⟨1375460, by rfl⟩ : syracuseStep 1833947 = 2750921) B2750921
theorem B818159 : Blo 542804 818159 := bstep (se 1 (by rfl) ⟨613619, by rfl⟩ : syracuseStep 818159 = 1227239) B1227239
theorem B3734585 : Blo 542804 3734585 := bstep (se 2 (by rfl) ⟨1400469, by rfl⟩ : syracuseStep 3734585 = 2800939) B2800939
theorem B818345 : Blo 542804 818345 := bstep (se 2 (by rfl) ⟨306879, by rfl⟩ : syracuseStep 818345 = 613759) B613759
theorem B2751731 : Blo 542804 2751731 := bstep (se 1 (by rfl) ⟨2063798, by rfl⟩ : syracuseStep 2751731 = 4127597) B4127597
theorem B1048043 : Blo 542804 1048043 := bstep (se 1 (by rfl) ⟨786032, by rfl⟩ : syracuseStep 1048043 = 1572065) B1572065
theorem B33979895 : Blo 542804 33979895 := bstep (se 1 (by rfl) ⟨25484921, by rfl⟩ : syracuseStep 33979895 = 50969843) B50969843
theorem B1965559 : Blo 542804 1965559 := bstep (se 1 (by rfl) ⟨1474169, by rfl⟩ : syracuseStep 1965559 = 2948339) B2948339
theorem B851707 : Blo 542804 851707 := bstep (se 1 (by rfl) ⟨638780, by rfl⟩ : syracuseStep 851707 = 1277561) B1277561
theorem B917311 : Blo 542804 917311 := bstep (se 1 (by rfl) ⟨687983, by rfl⟩ : syracuseStep 917311 = 1375967) B1375967
theorem B4980689 : Blo 542804 4980689 := bstep (se 2 (by rfl) ⟨1867758, by rfl⟩ : syracuseStep 4980689 = 3735517) B3735517
theorem B819407 : Blo 542804 819407 := bstep (se 1 (by rfl) ⟨614555, by rfl⟩ : syracuseStep 819407 = 1229111) B1229111
theorem B1376615 : Blo 542804 1376615 := bstep (se 1 (by rfl) ⟨1032461, by rfl⟩ : syracuseStep 1376615 = 2064923) B2064923
theorem B1376635 : Blo 542804 1376635 := bstep (se 1 (by rfl) ⟨1032476, by rfl⟩ : syracuseStep 1376635 = 2064953) B2064953
theorem B1835567 : Blo 542804 1835567 := bstep (se 1 (by rfl) ⟨1376675, by rfl⟩ : syracuseStep 1835567 = 2753351) B2753351
theorem B820127 : Blo 542804 820127 := bstep (se 1 (by rfl) ⟨615095, by rfl⟩ : syracuseStep 820127 = 1230191) B1230191
theorem B45188023 : Blo 542804 45188023 := bstep (se 1 (by rfl) ⟨33891017, by rfl⟩ : syracuseStep 45188023 = 67782035) B67782035
theorem B17728541 : Blo 542804 17728541 := bstep (se 3 (by rfl) ⟨3324101, by rfl⟩ : syracuseStep 17728541 = 6648203) B6648203
theorem B11175023 : Blo 542804 11175023 := bstep (se 1 (by rfl) ⟨8381267, by rfl⟩ : syracuseStep 11175023 = 16762535) B16762535
theorem B1475995 : Blo 542804 1475995 := bstep (se 1 (by rfl) ⟨1106996, by rfl⟩ : syracuseStep 1475995 = 2213993) B2213993
theorem B1378043 : Blo 542804 1378043 := bstep (se 1 (by rfl) ⟨1033532, by rfl⟩ : syracuseStep 1378043 = 2067065) B2067065
theorem B1836809 : Blo 542804 1836809 := bstep (se 2 (by rfl) ⟨688803, by rfl⟩ : syracuseStep 1836809 = 1377607) B1377607
theorem B920423 : Blo 542804 920423 := bstep (se 1 (by rfl) ⟨690317, by rfl⟩ : syracuseStep 920423 = 1380635) B1380635
theorem B1576127 : Blo 542804 1576127 := bstep (se 1 (by rfl) ⟨1182095, by rfl⟩ : syracuseStep 1576127 = 2364191) B2364191
theorem B22384187 : Blo 542804 22384187 := bstep (se 1 (by rfl) ⟨16788140, by rfl⟩ : syracuseStep 22384187 = 33576281) B33576281
theorem B4132457 : Blo 542804 4132457 := bstep (se 2 (by rfl) ⟨1549671, by rfl⟩ : syracuseStep 4132457 = 3099343) B3099343
theorem B1839455 : Blo 542804 1839455 := bstep (se 1 (by rfl) ⟨1379591, by rfl⟩ : syracuseStep 1839455 = 2759183) B2759183
theorem B4985279 : Blo 542804 4985279 := bstep (se 1 (by rfl) ⟨3738959, by rfl⟩ : syracuseStep 4985279 = 7477919) B7477919
theorem B922603 : Blo 542804 922603 := bstep (se 1 (by rfl) ⟨691952, by rfl⟩ : syracuseStep 922603 = 1383905) B1383905
theorem B6034571 : Blo 542804 6034571 := bstep (se 1 (by rfl) ⟨4525928, by rfl⟩ : syracuseStep 6034571 = 9051857) B9051857
theorem B1381799 : Blo 542804 1381799 := bstep (se 1 (by rfl) ⟨1036349, by rfl⟩ : syracuseStep 1381799 = 2072699) B2072699
theorem B5379527 : Blo 542804 5379527 := bstep (se 1 (by rfl) ⟨4034645, by rfl⟩ : syracuseStep 5379527 = 8069291) B8069291
theorem B1840751 : Blo 542804 1840751 := bstep (se 1 (by rfl) ⟨1380563, by rfl⟩ : syracuseStep 1840751 = 2761127) B2761127
theorem B1841021 : Blo 542804 1841021 := bstep (se 3 (by rfl) ⟨345191, by rfl⟩ : syracuseStep 1841021 = 690383) B690383
theorem B1841183 : Blo 542804 1841183 := bstep (se 1 (by rfl) ⟨1380887, by rfl⟩ : syracuseStep 1841183 = 2761775) B2761775
theorem B6199415 : Blo 542804 6199415 := bstep (se 1 (by rfl) ⟨4649561, by rfl⟩ : syracuseStep 6199415 = 9299123) B9299123
theorem B2759021 : Blo 542804 2759021 := bstep (se 3 (by rfl) ⟨517316, by rfl⟩ : syracuseStep 2759021 = 1034633) B1034633
theorem B11344637 : Blo 542804 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B1744201 : Blo 542804 1744201 := bstep (se 2 (by rfl) ⟨654075, by rfl⟩ : syracuseStep 1744201 = 1308151) B1308151
theorem B4136345 : Blo 542804 4136345 := bstep (se 2 (by rfl) ⟨1551129, by rfl⟩ : syracuseStep 4136345 = 3102259) B3102259
theorem B1548841 : Blo 542804 1548841 := bstep (se 2 (by rfl) ⟨580815, by rfl⟩ : syracuseStep 1548841 = 1161631) B1161631
theorem B1221353 : Blo 542804 1221353 := bstep (se 2 (by rfl) ⟨458007, by rfl⟩ : syracuseStep 1221353 = 916015) B916015
theorem B1221371 : Blo 542804 1221371 := bstep (se 1 (by rfl) ⟨916028, by rfl⟩ : syracuseStep 1221371 = 1832057) B1832057
theorem B1221641 : Blo 542804 1221641 := bstep (se 2 (by rfl) ⟨458115, by rfl⟩ : syracuseStep 1221641 = 916231) B916231
theorem B2794781 : Blo 542804 2794781 := bstep (se 3 (by rfl) ⟨524021, by rfl⟩ : syracuseStep 2794781 = 1048043) B1048043
theorem B1222631 : Blo 542804 1222631 := bstep (se 1 (by rfl) ⟨916973, by rfl⟩ : syracuseStep 1222631 = 1833947) B1833947
theorem B2763071 : Blo 542804 2763071 := bstep (se 1 (by rfl) ⟨2072303, by rfl⟩ : syracuseStep 2763071 = 4144607) B4144607
theorem B22653263 : Blo 542804 22653263 := bstep (se 1 (by rfl) ⟨16989947, by rfl⟩ : syracuseStep 22653263 = 33979895) B33979895
theorem B1223081 : Blo 542804 1223081 := bstep (se 2 (by rfl) ⟨458655, by rfl⟩ : syracuseStep 1223081 = 917311) B917311
theorem B3320459 : Blo 542804 3320459 := bstep (se 1 (by rfl) ⟨2490344, by rfl⟩ : syracuseStep 3320459 = 4980689) B4980689
theorem B4664051 : Blo 542804 4664051 := bstep (se 1 (by rfl) ⟨3498038, by rfl⟩ : syracuseStep 4664051 = 6996077) B6996077
theorem B1223423 : Blo 542804 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B5319863 : Blo 542804 5319863 := bstep (se 1 (by rfl) ⟨3989897, by rfl⟩ : syracuseStep 5319863 = 7979795) B7979795
theorem B3091871 : Blo 542804 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B67153475 : Blo 542804 67153475 := bstep (se 1 (by rfl) ⟨50365106, by rfl⟩ : syracuseStep 67153475 = 100730213) B100730213
theorem B1224647 : Blo 542804 1224647 := bstep (se 1 (by rfl) ⟨918485, by rfl⟩ : syracuseStep 1224647 = 1836971) B1836971
theorem B1224683 : Blo 542804 1224683 := bstep (se 1 (by rfl) ⟨918512, by rfl⟩ : syracuseStep 1224683 = 1837025) B1837025
theorem B232697939 : Blo 542804 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B700655 : Blo 542804 700655 := bstep (se 1 (by rfl) ⟨525491, by rfl⟩ : syracuseStep 700655 = 1050983) B1050983
theorem B1225151 : Blo 542804 1225151 := bstep (se 1 (by rfl) ⟨918863, by rfl⟩ : syracuseStep 1225151 = 1837727) B1837727
theorem B1225385 : Blo 542804 1225385 := bstep (se 2 (by rfl) ⟨459519, by rfl⟩ : syracuseStep 1225385 = 919039) B919039
theorem B5223149 : Blo 542804 5223149 := bstep (se 3 (by rfl) ⟨979340, by rfl⟩ : syracuseStep 5223149 = 1958681) B1958681
theorem B29897657 : Blo 542804 29897657 := bstep (se 2 (by rfl) ⟨11211621, by rfl⟩ : syracuseStep 29897657 = 22423243) B22423243
theorem B5879375 : Blo 542804 5879375 := bstep (se 1 (by rfl) ⟨4409531, by rfl⟩ : syracuseStep 5879375 = 8819063) B8819063
theorem B4962221 : Blo 542804 4962221 := bstep (se 3 (by rfl) ⟨930416, by rfl⟩ : syracuseStep 4962221 = 1860833) B1860833
theorem B1227311 : Blo 542804 1227311 := bstep (se 1 (by rfl) ⟨920483, by rfl⟩ : syracuseStep 1227311 = 1840967) B1840967
theorem B1555163 : Blo 542804 1555163 := bstep (se 1 (by rfl) ⟨1166372, by rfl⟩ : syracuseStep 1555163 = 2332745) B2332745
theorem B5651333 : Blo 542804 5651333 := bstep (se 4 (by rfl) ⟨529812, by rfl⟩ : syracuseStep 5651333 = 1059625) B1059625
theorem B1227743 : Blo 542804 1227743 := bstep (se 1 (by rfl) ⟨920807, by rfl⟩ : syracuseStep 1227743 = 1841615) B1841615
theorem B4669487 : Blo 542804 4669487 := bstep (se 1 (by rfl) ⟨3502115, by rfl⟩ : syracuseStep 4669487 = 7004231) B7004231
theorem B9421289 : Blo 542804 9421289 := bstep (se 2 (by rfl) ⟨3532983, by rfl⟩ : syracuseStep 9421289 = 7065967) B7065967
theorem B1229291 : Blo 542804 1229291 := bstep (se 1 (by rfl) ⟨921968, by rfl⟩ : syracuseStep 1229291 = 1843937) B1843937
theorem B6603545 : Blo 542804 6603545 := bstep (se 2 (by rfl) ⟨2476329, by rfl⟩ : syracuseStep 6603545 = 4952659) B4952659
theorem B1229651 : Blo 542804 1229651 := bstep (se 1 (by rfl) ⟨922238, by rfl⟩ : syracuseStep 1229651 = 1844477) B1844477
theorem B1229705 : Blo 542804 1229705 := bstep (se 2 (by rfl) ⟨461139, by rfl⟩ : syracuseStep 1229705 = 922279) B922279
theorem B3097703 : Blo 542804 3097703 := bstep (se 1 (by rfl) ⟨2323277, by rfl⟩ : syracuseStep 3097703 = 4646555) B4646555
theorem B1229993 : Blo 542804 1229993 := bstep (se 2 (by rfl) ⟨461247, by rfl⟩ : syracuseStep 1229993 = 922495) B922495
theorem B10503341 : Blo 542804 10503341 := bstep (se 3 (by rfl) ⟨1969376, by rfl⟩ : syracuseStep 10503341 = 3938753) B3938753
theorem B1164937 : Blo 542804 1164937 := bstep (se 2 (by rfl) ⟨436851, by rfl⟩ : syracuseStep 1164937 = 873703) B873703
theorem B1165193 : Blo 542804 1165193 := bstep (se 2 (by rfl) ⟨436947, by rfl⟩ : syracuseStep 1165193 = 873895) B873895
theorem B1886441 : Blo 542804 1886441 := bstep (se 2 (by rfl) ⟨707415, by rfl⟩ : syracuseStep 1886441 = 1414831) B1414831
theorem B542975 : Blo 542804 542975 := bstep (se 1 (by rfl) ⟨407231, by rfl⟩ : syracuseStep 542975 = 814463) B814463
theorem B4148009 : Blo 542804 4148009 := bstep (se 2 (by rfl) ⟨1555503, by rfl⟩ : syracuseStep 4148009 = 3111007) B3111007
theorem B543559 : Blo 542804 543559 := bstep (se 1 (by rfl) ⟨407669, by rfl⟩ : syracuseStep 543559 = 815339) B815339
theorem B543599 : Blo 542804 543599 := bstep (se 1 (by rfl) ⟨407699, by rfl⟩ : syracuseStep 543599 = 815399) B815399
theorem B8408231 : Blo 542804 8408231 := bstep (se 1 (by rfl) ⟨6306173, by rfl⟩ : syracuseStep 8408231 = 12612347) B12612347
theorem B543951 : Blo 542804 543951 := bstep (se 1 (by rfl) ⟨407963, by rfl⟩ : syracuseStep 543951 = 815927) B815927
theorem B544027 : Blo 542804 544027 := bstep (se 1 (by rfl) ⟨408020, by rfl⟩ : syracuseStep 544027 = 816041) B816041
theorem B544071 : Blo 542804 544071 := bstep (se 1 (by rfl) ⟨408053, by rfl⟩ : syracuseStep 544071 = 816107) B816107
theorem B544159 : Blo 542804 544159 := bstep (se 1 (by rfl) ⟨408119, by rfl⟩ : syracuseStep 544159 = 816239) B816239
theorem B1035803 : Blo 542804 1035803 := bstep (se 1 (by rfl) ⟨776852, by rfl⟩ : syracuseStep 1035803 = 1553705) B1553705
theorem B6639209 : Blo 542804 6639209 := bstep (se 2 (by rfl) ⟨2489703, by rfl⟩ : syracuseStep 6639209 = 4979407) B4979407
theorem B544671 : Blo 542804 544671 := bstep (se 1 (by rfl) ⟨408503, by rfl⟩ : syracuseStep 544671 = 817007) B817007
theorem B544679 : Blo 542804 544679 := bstep (se 1 (by rfl) ⟨408509, by rfl⟩ : syracuseStep 544679 = 817019) B817019
theorem B1036243 : Blo 542804 1036243 := bstep (se 1 (by rfl) ⟨777182, by rfl⟩ : syracuseStep 1036243 = 1554365) B1554365
theorem B4542437 : Blo 542804 4542437 := bstep (se 4 (by rfl) ⟨425853, by rfl⟩ : syracuseStep 4542437 = 851707) B851707
theorem B544839 : Blo 542804 544839 := bstep (se 1 (by rfl) ⟨408629, by rfl⟩ : syracuseStep 544839 = 817259) B817259
theorem B544959 : Blo 542804 544959 := bstep (se 1 (by rfl) ⟨408719, by rfl⟩ : syracuseStep 544959 = 817439) B817439
theorem B545007 : Blo 542804 545007 := bstep (se 1 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 545007 = 817511) B817511
theorem B545051 : Blo 542804 545051 := bstep (se 1 (by rfl) ⟨408788, by rfl⟩ : syracuseStep 545051 = 817577) B817577
theorem B545087 : Blo 542804 545087 := bstep (se 1 (by rfl) ⟨408815, by rfl⟩ : syracuseStep 545087 = 817631) B817631
theorem B610843 : Blo 542804 610843 := bstep (se 1 (by rfl) ⟨458132, by rfl⟩ : syracuseStep 610843 = 916265) B916265
theorem B545439 : Blo 542804 545439 := bstep (se 1 (by rfl) ⟨409079, by rfl⟩ : syracuseStep 545439 = 818159) B818159
theorem B545563 : Blo 542804 545563 := bstep (se 1 (by rfl) ⟨409172, by rfl⟩ : syracuseStep 545563 = 818345) B818345
theorem B10474433 : Blo 542804 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B4641907 : Blo 542804 4641907 := bstep (se 1 (by rfl) ⟨3481430, by rfl⟩ : syracuseStep 4641907 = 6962861) B6962861
theorem B775337 : Blo 542804 775337 := bstep (se 2 (by rfl) ⟨290751, by rfl⟩ : syracuseStep 775337 = 581503) B581503
theorem B4642865 : Blo 542804 4642865 := bstep (se 2 (by rfl) ⟨1741074, by rfl⟩ : syracuseStep 4642865 = 3482149) B3482149
theorem B5232761 : Blo 542804 5232761 := bstep (se 2 (by rfl) ⟨1962285, by rfl⟩ : syracuseStep 5232761 = 3924571) B3924571
theorem B613471 : Blo 542804 613471 := bstep (se 1 (by rfl) ⟨460103, by rfl⟩ : syracuseStep 613471 = 920207) B920207
theorem B2645183 : Blo 542804 2645183 := bstep (se 1 (by rfl) ⟨1983887, by rfl⟩ : syracuseStep 2645183 = 3967775) B3967775
theorem B777775 : Blo 542804 777775 := bstep (se 1 (by rfl) ⟨583331, by rfl⟩ : syracuseStep 777775 = 1166663) B1166663
theorem B2612843 : Blo 542804 2612843 := bstep (se 1 (by rfl) ⟨1959632, by rfl⟩ : syracuseStep 2612843 = 3919265) B3919265
theorem B9854585 : Blo 542804 9854585 := bstep (se 2 (by rfl) ⟨3695469, by rfl⟩ : syracuseStep 9854585 = 7390939) B7390939
theorem B35872465 : Blo 542804 35872465 := bstep (se 2 (by rfl) ⟨13452174, by rfl⟩ : syracuseStep 35872465 = 26904349) B26904349
theorem B2613073 : Blo 542804 2613073 := bstep (se 2 (by rfl) ⟨979902, by rfl⟩ : syracuseStep 2613073 = 1959805) B1959805
theorem B778367 : Blo 542804 778367 := bstep (se 1 (by rfl) ⟨583775, by rfl⟩ : syracuseStep 778367 = 1167551) B1167551
theorem B2941481 : Blo 542804 2941481 := bstep (se 2 (by rfl) ⟨1103055, by rfl⟩ : syracuseStep 2941481 = 2206111) B2206111
theorem B6218369 : Blo 542804 6218369 := bstep (se 2 (by rfl) ⟨2331888, by rfl⟩ : syracuseStep 6218369 = 4663777) B4663777
theorem B2320339 : Blo 542804 2320339 := bstep (se 1 (by rfl) ⟨1740254, by rfl⟩ : syracuseStep 2320339 = 3480509) B3480509
theorem B5957875 : Blo 542804 5957875 := bstep (se 1 (by rfl) ⟨4468406, by rfl⟩ : syracuseStep 5957875 = 8936813) B8936813
theorem B7563527 : Blo 542804 7563527 := bstep (se 1 (by rfl) ⟨5672645, by rfl⟩ : syracuseStep 7563527 = 11345291) B11345291
theorem B5892871 : Blo 542804 5892871 := bstep (se 1 (by rfl) ⟨4419653, by rfl⟩ : syracuseStep 5892871 = 8839307) B8839307
theorem B3107591 : Blo 542804 3107591 := bstep (se 1 (by rfl) ⟨2330693, by rfl⟩ : syracuseStep 3107591 = 4661387) B4661387
theorem B2943839 : Blo 542804 2943839 := bstep (se 1 (by rfl) ⟨2207879, by rfl⟩ : syracuseStep 2943839 = 4415759) B4415759
theorem B2485673 : Blo 542804 2485673 := bstep (se 2 (by rfl) ⟨932127, by rfl⟩ : syracuseStep 2485673 = 1864255) B1864255
theorem B814619 : Blo 542804 814619 := bstep (se 1 (by rfl) ⟨610964, by rfl⟩ : syracuseStep 814619 = 1221929) B1221929
theorem B9957127 : Blo 542804 9957127 := bstep (se 1 (by rfl) ⟨7467845, by rfl⟩ : syracuseStep 9957127 = 14935691) B14935691
theorem B815225 : Blo 542804 815225 := bstep (se 2 (by rfl) ⟨305709, by rfl⟩ : syracuseStep 815225 = 611419) B611419
theorem B815519 : Blo 542804 815519 := bstep (se 1 (by rfl) ⟨611639, by rfl⟩ : syracuseStep 815519 = 1223279) B1223279
theorem B1307191 : Blo 542804 1307191 := bstep (se 1 (by rfl) ⟨980393, by rfl⟩ : syracuseStep 1307191 = 1960787) B1960787
theorem B6288029 : Blo 542804 6288029 := bstep (se 3 (by rfl) ⟨1179005, by rfl⟩ : syracuseStep 6288029 = 2358011) B2358011
theorem B1471229 : Blo 542804 1471229 := bstep (se 3 (by rfl) ⟨275855, by rfl⟩ : syracuseStep 1471229 = 551711) B551711
theorem B2552639 : Blo 542804 2552639 := bstep (se 1 (by rfl) ⟨1914479, by rfl⟩ : syracuseStep 2552639 = 3828959) B3828959
theorem B2749625 : Blo 542804 2749625 := bstep (se 2 (by rfl) ⟨1031109, by rfl⟩ : syracuseStep 2749625 = 2062219) B2062219
theorem B2323961 : Blo 542804 2323961 := bstep (se 2 (by rfl) ⟨871485, by rfl⟩ : syracuseStep 2323961 = 1742971) B1742971
theorem B2062205 : Blo 542804 2062205 := bstep (se 3 (by rfl) ⟨386663, by rfl⟩ : syracuseStep 2062205 = 773327) B773327
theorem B1833191 : Blo 542804 1833191 := bstep (se 1 (by rfl) ⟨1374893, by rfl⟩ : syracuseStep 1833191 = 2749787) B2749787
theorem B1375339 : Blo 542804 1375339 := bstep (se 1 (by rfl) ⟨1031504, by rfl⟩ : syracuseStep 1375339 = 2063009) B2063009
theorem B2620745 : Blo 542804 2620745 := bstep (se 2 (by rfl) ⟨982779, by rfl⟩ : syracuseStep 2620745 = 1965559) B1965559
theorem B2489723 : Blo 542804 2489723 := bstep (se 1 (by rfl) ⟨1867292, by rfl⟩ : syracuseStep 2489723 = 3734585) B3734585
theorem B1834487 : Blo 542804 1834487 := bstep (se 1 (by rfl) ⟨1375865, by rfl⟩ : syracuseStep 1834487 = 2751731) B2751731
theorem B3112991 : Blo 542804 3112991 := bstep (se 1 (by rfl) ⟨2334743, by rfl⟩ : syracuseStep 3112991 = 4669487) B4669487
theorem B620527837 : Blo 542804 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B917743 : Blo 542804 917743 := bstep (se 1 (by rfl) ⟨688307, by rfl⟩ : syracuseStep 917743 = 1376615) B1376615
theorem B819527 : Blo 542804 819527 := bstep (se 1 (by rfl) ⟨614645, by rfl⟩ : syracuseStep 819527 = 1229291) B1229291
theorem B1835513 : Blo 542804 1835513 := bstep (se 2 (by rfl) ⟨688317, by rfl⟩ : syracuseStep 1835513 = 1376635) B1376635
theorem B819767 : Blo 542804 819767 := bstep (se 1 (by rfl) ⟨614825, by rfl⟩ : syracuseStep 819767 = 1229651) B1229651
theorem B819803 : Blo 542804 819803 := bstep (se 1 (by rfl) ⟨614852, by rfl⟩ : syracuseStep 819803 = 1229705) B1229705
theorem B2065121 : Blo 542804 2065121 := bstep (se 2 (by rfl) ⟨774420, by rfl⟩ : syracuseStep 2065121 = 1548841) B1548841
theorem B2065135 : Blo 542804 2065135 := bstep (se 1 (by rfl) ⟨1548851, by rfl⟩ : syracuseStep 2065135 = 3097703) B3097703
theorem B819995 : Blo 542804 819995 := bstep (se 1 (by rfl) ⟨614996, by rfl⟩ : syracuseStep 819995 = 1229993) B1229993
theorem B918695 : Blo 542804 918695 := bstep (se 1 (by rfl) ⟨689021, by rfl⟩ : syracuseStep 918695 = 1378043) B1378043
theorem B1967993 : Blo 542804 1967993 := bstep (se 2 (by rfl) ⟨737997, by rfl⟩ : syracuseStep 1967993 = 1475995) B1475995
theorem B5605487 : Blo 542804 5605487 := bstep (se 1 (by rfl) ⟨4204115, by rfl⟩ : syracuseStep 5605487 = 8408231) B8408231
theorem B1050751 : Blo 542804 1050751 := bstep (se 1 (by rfl) ⟨788063, by rfl⟩ : syracuseStep 1050751 = 1576127) B1576127
theorem B690535 : Blo 542804 690535 := bstep (se 1 (by rfl) ⟨517901, by rfl⟩ : syracuseStep 690535 = 1035803) B1035803
theorem B2754971 : Blo 542804 2754971 := bstep (se 1 (by rfl) ⟨2066228, by rfl⟩ : syracuseStep 2754971 = 4132457) B4132457
theorem B4426139 : Blo 542804 4426139 := bstep (se 1 (by rfl) ⟨3319604, by rfl⟩ : syracuseStep 4426139 = 6639209) B6639209
theorem B20122037 : Blo 542804 20122037 := bstep (se 5 (by rfl) ⟨943220, by rfl⟩ : syracuseStep 20122037 = 1886441) B1886441
theorem B7473653 : Blo 542804 7473653 := bstep (se 5 (by rfl) ⟨350327, by rfl⟩ : syracuseStep 7473653 = 700655) B700655
theorem B2067565 : Blo 542804 2067565 := bstep (se 3 (by rfl) ⟨387668, by rfl⟩ : syracuseStep 2067565 = 775337) B775337
theorem B6982955 : Blo 542804 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B921199 : Blo 542804 921199 := bstep (se 1 (by rfl) ⟨690899, by rfl⟩ : syracuseStep 921199 = 1381799) B1381799
theorem B4132943 : Blo 542804 4132943 := bstep (se 1 (by rfl) ⟨3099707, by rfl⟩ : syracuseStep 4132943 = 6199415) B6199415
theorem B1839347 : Blo 542804 1839347 := bstep (se 1 (by rfl) ⟨1379510, by rfl⟩ : syracuseStep 1839347 = 2759021) B2759021
theorem B2757563 : Blo 542804 2757563 := bstep (se 1 (by rfl) ⟨2068172, by rfl⟩ : syracuseStep 2757563 = 4136345) B4136345
theorem B13276169 : Blo 542804 13276169 := bstep (se 2 (by rfl) ⟨4978563, by rfl⟩ : syracuseStep 13276169 = 9957127) B9957127
theorem B1741895 : Blo 542804 1741895 := bstep (se 1 (by rfl) ⟨1306421, by rfl⟩ : syracuseStep 1741895 = 2612843) B2612843
theorem B1381657 : Blo 542804 1381657 := bstep (se 2 (by rfl) ⟨518121, by rfl⟩ : syracuseStep 1381657 = 1036243) B1036243
theorem B1742921 : Blo 542804 1742921 := bstep (se 2 (by rfl) ⟨653595, by rfl⟩ : syracuseStep 1742921 = 1307191) B1307191
theorem B1842047 : Blo 542804 1842047 := bstep (se 1 (by rfl) ⟨1381535, by rfl⟩ : syracuseStep 1842047 = 2763071) B2763071
theorem B2071727 : Blo 542804 2071727 := bstep (se 1 (by rfl) ⟨1553795, by rfl⟩ : syracuseStep 2071727 = 3107591) B3107591
theorem B3546575 : Blo 542804 3546575 := bstep (se 1 (by rfl) ⟨2659931, by rfl⟩ : syracuseStep 3546575 = 5319863) B5319863
theorem B44768983 : Blo 542804 44768983 := bstep (se 1 (by rfl) ⟨33576737, by rfl⟩ : syracuseStep 44768983 = 67153475) B67153475
theorem B3482099 : Blo 542804 3482099 := bstep (se 1 (by rfl) ⟨2611574, by rfl⟩ : syracuseStep 3482099 = 5223149) B5223149
theorem B19931771 : Blo 542804 19931771 := bstep (se 1 (by rfl) ⟨14948828, by rfl⟩ : syracuseStep 19931771 = 29897657) B29897657
theorem B1549307 : Blo 542804 1549307 := bstep (se 1 (by rfl) ⟨1161980, by rfl⟩ : syracuseStep 1549307 = 2323961) B2323961
theorem B1222127 : Blo 542804 1222127 := bstep (se 1 (by rfl) ⟨916595, by rfl⟩ : syracuseStep 1222127 = 1833191) B1833191
theorem B1747163 : Blo 542804 1747163 := bstep (se 1 (by rfl) ⟨1310372, by rfl⟩ : syracuseStep 1747163 = 2620745) B2620745
theorem B1222991 : Blo 542804 1222991 := bstep (se 1 (by rfl) ⟨917243, by rfl⟩ : syracuseStep 1222991 = 1834487) B1834487
theorem B3484097 : Blo 542804 3484097 := bstep (se 2 (by rfl) ⟨1306536, by rfl⟩ : syracuseStep 3484097 = 2613073) B2613073
theorem B2075645 : Blo 542804 2075645 := bstep (se 3 (by rfl) ⟨389183, by rfl⟩ : syracuseStep 2075645 = 778367) B778367
theorem B1223711 : Blo 542804 1223711 := bstep (se 1 (by rfl) ⟨917783, by rfl⟩ : syracuseStep 1223711 = 1835567) B1835567
theorem B4402363 : Blo 542804 4402363 := bstep (se 1 (by rfl) ⟨3301772, by rfl⟩ : syracuseStep 4402363 = 6603545) B6603545
theorem B7450015 : Blo 542804 7450015 := bstep (se 1 (by rfl) ⟨5587511, by rfl⟩ : syracuseStep 7450015 = 11175023) B11175023
theorem B1224539 : Blo 542804 1224539 := bstep (se 1 (by rfl) ⟨918404, by rfl⟩ : syracuseStep 1224539 = 1836809) B1836809
theorem B7843949 : Blo 542804 7843949 := bstep (se 3 (by rfl) ⟨1470740, by rfl⟩ : syracuseStep 7843949 = 2941481) B2941481
theorem B2765339 : Blo 542804 2765339 := bstep (se 1 (by rfl) ⟨2074004, by rfl⟩ : syracuseStep 2765339 = 4148009) B4148009
theorem B1553249 : Blo 542804 1553249 := bstep (se 2 (by rfl) ⟨582468, by rfl⟩ : syracuseStep 1553249 = 1164937) B1164937
theorem B14922791 : Blo 542804 14922791 := bstep (se 1 (by rfl) ⟨11192093, by rfl⟩ : syracuseStep 14922791 = 22384187) B22384187
theorem B3093785 : Blo 542804 3093785 := bstep (se 2 (by rfl) ⟨1160169, by rfl⟩ : syracuseStep 3093785 = 2320339) B2320339
theorem B3028291 : Blo 542804 3028291 := bstep (se 1 (by rfl) ⟨2271218, by rfl⟩ : syracuseStep 3028291 = 4542437) B4542437
theorem B1226303 : Blo 542804 1226303 := bstep (se 1 (by rfl) ⟨919727, by rfl⟩ : syracuseStep 1226303 = 1839455) B1839455
theorem B3323519 : Blo 542804 3323519 := bstep (se 1 (by rfl) ⟨2492639, by rfl⟩ : syracuseStep 3323519 = 4985279) B4985279
theorem B7452749 : Blo 542804 7452749 := bstep (se 3 (by rfl) ⟨1397390, by rfl⟩ : syracuseStep 7452749 = 2794781) B2794781
theorem B1227167 : Blo 542804 1227167 := bstep (se 1 (by rfl) ⟨920375, by rfl⟩ : syracuseStep 1227167 = 1840751) B1840751
theorem B1227347 : Blo 542804 1227347 := bstep (se 1 (by rfl) ⟨920510, by rfl⟩ : syracuseStep 1227347 = 1841021) B1841021
theorem B1227455 : Blo 542804 1227455 := bstep (se 1 (by rfl) ⟨920591, by rfl⟩ : syracuseStep 1227455 = 1841183) B1841183
theorem B3095243 : Blo 542804 3095243 := bstep (se 1 (by rfl) ⟨2321432, by rfl⟩ : syracuseStep 3095243 = 4642865) B4642865
theorem B3488507 : Blo 542804 3488507 := bstep (se 1 (by rfl) ⟨2616380, by rfl⟩ : syracuseStep 3488507 = 5232761) B5232761
theorem B6569723 : Blo 542804 6569723 := bstep (se 1 (by rfl) ⟨4927292, by rfl⟩ : syracuseStep 6569723 = 9854585) B9854585
theorem B4145579 : Blo 542804 4145579 := bstep (se 1 (by rfl) ⟨3109184, by rfl⟩ : syracuseStep 4145579 = 6218369) B6218369
theorem B1230137 : Blo 542804 1230137 := bstep (se 2 (by rfl) ⟨461301, by rfl⟩ : syracuseStep 1230137 = 922603) B922603
theorem B2213639 : Blo 542804 2213639 := bstep (se 1 (by rfl) ⟨1660229, by rfl⟩ : syracuseStep 2213639 = 3320459) B3320459
theorem B1657115 : Blo 542804 1657115 := bstep (se 1 (by rfl) ⟨1242836, by rfl⟩ : syracuseStep 1657115 = 2485673) B2485673
theorem B543079 : Blo 542804 543079 := bstep (se 1 (by rfl) ⟨407309, by rfl⟩ : syracuseStep 543079 = 814619) B814619
theorem B543483 : Blo 542804 543483 := bstep (se 1 (by rfl) ⟨407612, by rfl⟩ : syracuseStep 543483 = 815225) B815225
theorem B543679 : Blo 542804 543679 := bstep (se 1 (by rfl) ⟨407759, by rfl⟩ : syracuseStep 543679 = 815519) B815519
theorem B3919583 : Blo 542804 3919583 := bstep (se 1 (by rfl) ⟨2939687, by rfl⟩ : syracuseStep 3919583 = 5879375) B5879375
theorem B1036775 : Blo 542804 1036775 := bstep (se 1 (by rfl) ⟨777581, by rfl⟩ : syracuseStep 1036775 = 1555163) B1555163
theorem B1037033 : Blo 542804 1037033 := bstep (se 2 (by rfl) ⟨388887, by rfl⟩ : syracuseStep 1037033 = 777775) B777775
theorem B1659815 : Blo 542804 1659815 := bstep (se 1 (by rfl) ⟨1244861, by rfl⟩ : syracuseStep 1659815 = 2489723) B2489723
theorem B47829953 : Blo 542804 47829953 := bstep (se 2 (by rfl) ⟨17936232, by rfl⟩ : syracuseStep 47829953 = 35872465) B35872465
theorem B546271 : Blo 542804 546271 := bstep (se 1 (by rfl) ⟨409703, by rfl⟩ : syracuseStep 546271 = 819407) B819407
theorem B6280859 : Blo 542804 6280859 := bstep (se 1 (by rfl) ⟨4710644, by rfl⟩ : syracuseStep 6280859 = 9421289) B9421289
theorem B546751 : Blo 542804 546751 := bstep (se 1 (by rfl) ⟨410063, by rfl⟩ : syracuseStep 546751 = 820127) B820127
theorem B11819027 : Blo 542804 11819027 := bstep (se 1 (by rfl) ⟨8864270, by rfl⟩ : syracuseStep 11819027 = 17728541) B17728541
theorem B7002227 : Blo 542804 7002227 := bstep (se 1 (by rfl) ⟨5251670, by rfl⟩ : syracuseStep 7002227 = 10503341) B10503341
theorem B60250697 : Blo 542804 60250697 := bstep (se 2 (by rfl) ⟨22594011, by rfl⟩ : syracuseStep 60250697 = 45188023) B45188023
theorem B776795 : Blo 542804 776795 := bstep (se 1 (by rfl) ⟨582596, by rfl⟩ : syracuseStep 776795 = 1165193) B1165193
theorem B31775333 : Blo 542804 31775333 := bstep (se 4 (by rfl) ⟨2978937, by rfl⟩ : syracuseStep 31775333 = 5957875) B5957875
theorem B613615 : Blo 542804 613615 := bstep (se 1 (by rfl) ⟨460211, by rfl⟩ : syracuseStep 613615 = 920423) B920423
theorem B4023047 : Blo 542804 4023047 := bstep (se 1 (by rfl) ⟨3017285, by rfl⟩ : syracuseStep 4023047 = 6034571) B6034571
theorem B7857161 : Blo 542804 7857161 := bstep (se 2 (by rfl) ⟨2946435, by rfl⟩ : syracuseStep 7857161 = 5892871) B5892871
theorem B14345405 : Blo 542804 14345405 := bstep (se 3 (by rfl) ⟨2689763, by rfl⟩ : syracuseStep 14345405 = 5379527) B5379527
theorem B7563091 : Blo 542804 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B1763455 : Blo 542804 1763455 := bstep (se 1 (by rfl) ⟨1322591, by rfl⟩ : syracuseStep 1763455 = 2645183) B2645183
theorem B814235 : Blo 542804 814235 := bstep (se 1 (by rfl) ⟨610676, by rfl⟩ : syracuseStep 814235 = 1221353) B1221353
theorem B814247 : Blo 542804 814247 := bstep (se 1 (by rfl) ⟨610685, by rfl⟩ : syracuseStep 814247 = 1221371) B1221371
theorem B814427 : Blo 542804 814427 := bstep (se 1 (by rfl) ⟨610820, by rfl⟩ : syracuseStep 814427 = 1221641) B1221641
theorem B814457 : Blo 542804 814457 := bstep (se 2 (by rfl) ⟨305421, by rfl⟩ : syracuseStep 814457 = 610843) B610843
theorem B815087 : Blo 542804 815087 := bstep (se 1 (by rfl) ⟨611315, by rfl⟩ : syracuseStep 815087 = 1222631) B1222631
theorem B6189209 : Blo 542804 6189209 := bstep (se 2 (by rfl) ⟨2320953, by rfl⟩ : syracuseStep 6189209 = 4641907) B4641907
theorem B5042351 : Blo 542804 5042351 := bstep (se 1 (by rfl) ⟨3781763, by rfl⟩ : syracuseStep 5042351 = 7563527) B7563527
theorem B15102175 : Blo 542804 15102175 := bstep (se 1 (by rfl) ⟨11326631, by rfl⟩ : syracuseStep 15102175 = 22653263) B22653263
theorem B815387 : Blo 542804 815387 := bstep (se 1 (by rfl) ⟨611540, by rfl⟩ : syracuseStep 815387 = 1223081) B1223081
theorem B3109367 : Blo 542804 3109367 := bstep (se 1 (by rfl) ⟨2332025, by rfl⟩ : syracuseStep 3109367 = 4664051) B4664051
theorem B815615 : Blo 542804 815615 := bstep (se 1 (by rfl) ⟨611711, by rfl⟩ : syracuseStep 815615 = 1223423) B1223423
theorem B1962559 : Blo 542804 1962559 := bstep (se 1 (by rfl) ⟨1471919, by rfl⟩ : syracuseStep 1962559 = 2943839) B2943839
theorem B2061247 : Blo 542804 2061247 := bstep (se 1 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 2061247 = 3091871) B3091871
theorem B816431 : Blo 542804 816431 := bstep (se 1 (by rfl) ⟨612323, by rfl⟩ : syracuseStep 816431 = 1224647) B1224647
theorem B816455 : Blo 542804 816455 := bstep (se 1 (by rfl) ⟨612341, by rfl⟩ : syracuseStep 816455 = 1224683) B1224683
theorem B816767 : Blo 542804 816767 := bstep (se 1 (by rfl) ⟨612575, by rfl⟩ : syracuseStep 816767 = 1225151) B1225151
theorem B4192019 : Blo 542804 4192019 := bstep (se 1 (by rfl) ⟨3144014, by rfl⟩ : syracuseStep 4192019 = 6288029) B6288029
theorem B816923 : Blo 542804 816923 := bstep (se 1 (by rfl) ⟨612692, by rfl⟩ : syracuseStep 816923 = 1225385) B1225385
theorem B980819 : Blo 542804 980819 := bstep (se 1 (by rfl) ⟨735614, by rfl⟩ : syracuseStep 980819 = 1471229) B1471229
theorem B27228149 : Blo 542804 27228149 := bstep (se 5 (by rfl) ⟨1276319, by rfl⟩ : syracuseStep 27228149 = 2552639) B2552639
theorem B1833083 : Blo 542804 1833083 := bstep (se 1 (by rfl) ⟨1374812, by rfl⟩ : syracuseStep 1833083 = 2749625) B2749625
theorem B1374803 : Blo 542804 1374803 := bstep (se 1 (by rfl) ⟨1031102, by rfl⟩ : syracuseStep 1374803 = 2062205) B2062205
theorem B3308147 : Blo 542804 3308147 := bstep (se 1 (by rfl) ⟨2481110, by rfl⟩ : syracuseStep 3308147 = 4962221) B4962221
theorem B817961 : Blo 542804 817961 := bstep (se 2 (by rfl) ⟨306735, by rfl⟩ : syracuseStep 817961 = 613471) B613471
theorem B1833785 : Blo 542804 1833785 := bstep (se 2 (by rfl) ⟨687669, by rfl⟩ : syracuseStep 1833785 = 1375339) B1375339
theorem B818207 : Blo 542804 818207 := bstep (se 1 (by rfl) ⟨613655, by rfl⟩ : syracuseStep 818207 = 1227311) B1227311
theorem B2325601 : Blo 542804 2325601 := bstep (se 2 (by rfl) ⟨872100, by rfl⟩ : syracuseStep 2325601 = 1744201) B1744201
theorem B3767555 : Blo 542804 3767555 := bstep (se 1 (by rfl) ⟨2825666, by rfl⟩ : syracuseStep 3767555 = 5651333) B5651333
theorem B818495 : Blo 542804 818495 := bstep (se 1 (by rfl) ⟨613871, by rfl⟩ : syracuseStep 818495 = 1227743) B1227743
theorem B1376747 : Blo 542804 1376747 := bstep (se 1 (by rfl) ⟨1032560, by rfl⟩ : syracuseStep 1376747 = 2065121) B2065121
theorem B820091 : Blo 542804 820091 := bstep (se 1 (by rfl) ⟨615068, by rfl⟩ : syracuseStep 820091 = 1230137) B1230137
theorem B2753513 : Blo 542804 2753513 := bstep (se 2 (by rfl) ⟨1032567, by rfl⟩ : syracuseStep 2753513 = 2065135) B2065135
theorem B1475759 : Blo 542804 1475759 := bstep (se 1 (by rfl) ⟨1106819, by rfl⟩ : syracuseStep 1475759 = 2213639) B2213639
theorem B1311995 : Blo 542804 1311995 := bstep (se 1 (by rfl) ⟨983996, by rfl⟩ : syracuseStep 1311995 = 1967993) B1967993
theorem B3736991 : Blo 542804 3736991 := bstep (se 1 (by rfl) ⟨2802743, by rfl⟩ : syracuseStep 3736991 = 5605487) B5605487
theorem B1836647 : Blo 542804 1836647 := bstep (se 1 (by rfl) ⟨1377485, by rfl⟩ : syracuseStep 1836647 = 2754971) B2754971
theorem B2950759 : Blo 542804 2950759 := bstep (se 1 (by rfl) ⟨2213069, by rfl⟩ : syracuseStep 2950759 = 4426139) B4426139
theorem B4982435 : Blo 542804 4982435 := bstep (se 1 (by rfl) ⟨3736826, by rfl⟩ : syracuseStep 4982435 = 7473653) B7473653
theorem B4655303 : Blo 542804 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B4131485 : Blo 542804 4131485 := bstep (se 3 (by rfl) ⟨774653, by rfl⟩ : syracuseStep 4131485 = 1549307) B1549307
theorem B2755295 : Blo 542804 2755295 := bstep (se 1 (by rfl) ⟨2066471, by rfl⟩ : syracuseStep 2755295 = 4132943) B4132943
theorem B691183 : Blo 542804 691183 := bstep (se 1 (by rfl) ⟨518387, by rfl⟩ : syracuseStep 691183 = 1036775) B1036775
theorem B920713 : Blo 542804 920713 := bstep (se 2 (by rfl) ⟨345267, by rfl⟩ : syracuseStep 920713 = 690535) B690535
theorem B691355 : Blo 542804 691355 := bstep (se 1 (by rfl) ⟨518516, by rfl⟩ : syracuseStep 691355 = 1037033) B1037033
theorem B1838375 : Blo 542804 1838375 := bstep (se 1 (by rfl) ⟨1378781, by rfl⟩ : syracuseStep 1838375 = 2757563) B2757563
theorem B31886635 : Blo 542804 31886635 := bstep (se 1 (by rfl) ⟨23914976, by rfl⟩ : syracuseStep 31886635 = 47829953) B47829953
theorem B8850779 : Blo 542804 8850779 := bstep (se 1 (by rfl) ⟨6638084, by rfl⟩ : syracuseStep 8850779 = 13276169) B13276169
theorem B2756753 : Blo 542804 2756753 := bstep (se 2 (by rfl) ⟨1033782, by rfl⟩ : syracuseStep 2756753 = 2067565) B2067565
theorem B5869817 : Blo 542804 5869817 := bstep (se 2 (by rfl) ⟨2201181, by rfl⟩ : syracuseStep 5869817 = 4402363) B4402363
theorem B16748957 : Blo 542804 16748957 := bstep (se 3 (by rfl) ⟨3140429, by rfl⟩ : syracuseStep 16748957 = 6280859) B6280859
theorem B9933353 : Blo 542804 9933353 := bstep (se 2 (by rfl) ⟨3725007, by rfl⟩ : syracuseStep 9933353 = 7450015) B7450015
theorem B1381151 : Blo 542804 1381151 := bstep (se 1 (by rfl) ⟨1035863, by rfl⟩ : syracuseStep 1381151 = 2071727) B2071727
theorem B2364383 : Blo 542804 2364383 := bstep (se 1 (by rfl) ⟨1773287, by rfl⟩ : syracuseStep 2364383 = 3546575) B3546575
theorem B2071453 : Blo 542804 2071453 := bstep (se 3 (by rfl) ⟨388397, by rfl⟩ : syracuseStep 2071453 = 776795) B776795
theorem B1842209 : Blo 542804 1842209 := bstep (se 2 (by rfl) ⟨690828, by rfl⟩ : syracuseStep 1842209 = 1381657) B1381657
theorem B1383763 : Blo 542804 1383763 := bstep (se 1 (by rfl) ⟨1037822, by rfl⟩ : syracuseStep 1383763 = 2075645) B2075645
theorem B2072911 : Blo 542804 2072911 := bstep (se 1 (by rfl) ⟨1554683, by rfl⟩ : syracuseStep 2072911 = 3109367) B3109367
theorem B1843559 : Blo 542804 1843559 := bstep (se 1 (by rfl) ⟨1382669, by rfl⟩ : syracuseStep 1843559 = 2765339) B2765339
theorem B2794679 : Blo 542804 2794679 := bstep (se 1 (by rfl) ⟨2096009, by rfl⟩ : syracuseStep 2794679 = 4192019) B4192019
theorem B1222055 : Blo 542804 1222055 := bstep (se 1 (by rfl) ⟨916541, by rfl⟩ : syracuseStep 1222055 = 1833083) B1833083
theorem B2205431 : Blo 542804 2205431 := bstep (se 1 (by rfl) ⟨1654073, by rfl⟩ : syracuseStep 2205431 = 3308147) B3308147
theorem B1222523 : Blo 542804 1222523 := bstep (se 1 (by rfl) ⟨916892, by rfl⟩ : syracuseStep 1222523 = 1833785) B1833785
theorem B2075327 : Blo 542804 2075327 := bstep (se 1 (by rfl) ⟨1556495, by rfl⟩ : syracuseStep 2075327 = 3112991) B3112991
theorem B2763719 : Blo 542804 2763719 := bstep (se 1 (by rfl) ⟨2072789, by rfl⟩ : syracuseStep 2763719 = 4145579) B4145579
theorem B827370449 : Blo 542804 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B1223657 : Blo 542804 1223657 := bstep (se 2 (by rfl) ⟨458871, by rfl⟩ : syracuseStep 1223657 = 917743) B917743
theorem B1223675 : Blo 542804 1223675 := bstep (se 1 (by rfl) ⟨917756, by rfl⟩ : syracuseStep 1223675 = 1835513) B1835513
theorem B13446269 : Blo 542804 13446269 := bstep (se 3 (by rfl) ⟨2521175, by rfl⟩ : syracuseStep 13446269 = 5042351) B5042351
theorem B13414691 : Blo 542804 13414691 := bstep (se 1 (by rfl) ⟨10061018, by rfl⟩ : syracuseStep 13414691 = 20122037) B20122037
theorem B10728125 : Blo 542804 10728125 := bstep (se 3 (by rfl) ⟨2011523, by rfl⟩ : syracuseStep 10728125 = 4023047) B4023047
theorem B1226231 : Blo 542804 1226231 := bstep (se 1 (by rfl) ⟨919673, by rfl⟩ : syracuseStep 1226231 = 1839347) B1839347
theorem B10466981 : Blo 542804 10466981 := bstep (se 4 (by rfl) ⟨981279, by rfl⟩ : syracuseStep 10466981 = 1962559) B1962559
theorem B1161263 : Blo 542804 1161263 := bstep (se 1 (by rfl) ⟨870947, by rfl⟩ : syracuseStep 1161263 = 1741895) B1741895
theorem B7879351 : Blo 542804 7879351 := bstep (se 1 (by rfl) ⟨5909513, by rfl⟩ : syracuseStep 7879351 = 11819027) B11819027
theorem B1161947 : Blo 542804 1161947 := bstep (se 1 (by rfl) ⟨871460, by rfl⟩ : syracuseStep 1161947 = 1742921) B1742921
theorem B4668151 : Blo 542804 4668151 := bstep (se 1 (by rfl) ⟨3501113, by rfl⟩ : syracuseStep 4668151 = 7002227) B7002227
theorem B1228031 : Blo 542804 1228031 := bstep (se 1 (by rfl) ⟨921023, by rfl⟩ : syracuseStep 1228031 = 1842047) B1842047
theorem B1228265 : Blo 542804 1228265 := bstep (se 2 (by rfl) ⟨460599, by rfl⟩ : syracuseStep 1228265 = 921199) B921199
theorem B20136233 : Blo 542804 20136233 := bstep (se 2 (by rfl) ⟨7551087, by rfl⟩ : syracuseStep 20136233 = 15102175) B15102175
theorem B13287847 : Blo 542804 13287847 := bstep (se 1 (by rfl) ⟨9965885, by rfl⟩ : syracuseStep 13287847 = 19931771) B19931771
theorem B338936885 : Blo 542804 338936885 := bstep (se 5 (by rfl) ⟨15887666, by rfl⟩ : syracuseStep 338936885 = 31775333) B31775333
theorem B64603541 : Blo 542804 64603541 := bstep (se 6 (by rfl) ⟨1514145, by rfl⟩ : syracuseStep 64603541 = 3028291) B3028291
theorem B1164775 : Blo 542804 1164775 := bstep (se 1 (by rfl) ⟨873581, by rfl⟩ : syracuseStep 1164775 = 1747163) B1747163
theorem B542823 : Blo 542804 542823 := bstep (se 1 (by rfl) ⟨407117, by rfl⟩ : syracuseStep 542823 = 814235) B814235
theorem B542831 : Blo 542804 542831 := bstep (se 1 (by rfl) ⟨407123, by rfl⟩ : syracuseStep 542831 = 814247) B814247
theorem B542951 : Blo 542804 542951 := bstep (se 1 (by rfl) ⟨407213, by rfl⟩ : syracuseStep 542951 = 814427) B814427
theorem B542971 : Blo 542804 542971 := bstep (se 1 (by rfl) ⟨407228, by rfl⟩ : syracuseStep 542971 = 814457) B814457
theorem B543391 : Blo 542804 543391 := bstep (se 1 (by rfl) ⟨407543, by rfl⟩ : syracuseStep 543391 = 815087) B815087
theorem B5229299 : Blo 542804 5229299 := bstep (se 1 (by rfl) ⟨3921974, by rfl⟩ : syracuseStep 5229299 = 7843949) B7843949
theorem B543591 : Blo 542804 543591 := bstep (se 1 (by rfl) ⟨407693, by rfl⟩ : syracuseStep 543591 = 815387) B815387
theorem B543743 : Blo 542804 543743 := bstep (se 1 (by rfl) ⟨407807, by rfl⟩ : syracuseStep 543743 = 815615) B815615
theorem B1035499 : Blo 542804 1035499 := bstep (se 1 (by rfl) ⟨776624, by rfl⟩ : syracuseStep 1035499 = 1553249) B1553249
theorem B9948527 : Blo 542804 9948527 := bstep (se 1 (by rfl) ⟨7461395, by rfl⟩ : syracuseStep 9948527 = 14922791) B14922791
theorem B544287 : Blo 542804 544287 := bstep (se 1 (by rfl) ⟨408215, by rfl⟩ : syracuseStep 544287 = 816431) B816431
theorem B544303 : Blo 542804 544303 := bstep (se 1 (by rfl) ⟨408227, by rfl⟩ : syracuseStep 544303 = 816455) B816455
theorem B544511 : Blo 542804 544511 := bstep (se 1 (by rfl) ⟨408383, by rfl⟩ : syracuseStep 544511 = 816767) B816767
theorem B2215679 : Blo 542804 2215679 := bstep (se 1 (by rfl) ⟨1661759, by rfl⟩ : syracuseStep 2215679 = 3323519) B3323519
theorem B544615 : Blo 542804 544615 := bstep (se 1 (by rfl) ⟨408461, by rfl⟩ : syracuseStep 544615 = 816923) B816923
theorem B4968499 : Blo 542804 4968499 := bstep (se 1 (by rfl) ⟨3726374, by rfl⟩ : syracuseStep 4968499 = 7452749) B7452749
theorem B3100801 : Blo 542804 3100801 := bstep (se 2 (by rfl) ⟨1162800, by rfl⟩ : syracuseStep 3100801 = 2325601) B2325601
theorem B545307 : Blo 542804 545307 := bstep (se 1 (by rfl) ⟨408980, by rfl⟩ : syracuseStep 545307 = 817961) B817961
theorem B545471 : Blo 542804 545471 := bstep (se 1 (by rfl) ⟨409103, by rfl⟩ : syracuseStep 545471 = 818207) B818207
theorem B2511703 : Blo 542804 2511703 := bstep (se 1 (by rfl) ⟨1883777, by rfl⟩ : syracuseStep 2511703 = 3767555) B3767555
theorem B545663 : Blo 542804 545663 := bstep (se 1 (by rfl) ⟨409247, by rfl⟩ : syracuseStep 545663 = 818495) B818495
theorem B59691977 : Blo 542804 59691977 := bstep (se 2 (by rfl) ⟨22384491, by rfl⟩ : syracuseStep 59691977 = 44768983) B44768983
theorem B4379815 : Blo 542804 4379815 := bstep (se 1 (by rfl) ⟨3284861, by rfl⟩ : syracuseStep 4379815 = 6569723) B6569723
theorem B546351 : Blo 542804 546351 := bstep (se 1 (by rfl) ⟨409763, by rfl⟩ : syracuseStep 546351 = 819527) B819527
theorem B546511 : Blo 542804 546511 := bstep (se 1 (by rfl) ⟨409883, by rfl⟩ : syracuseStep 546511 = 819767) B819767
theorem B546535 : Blo 542804 546535 := bstep (se 1 (by rfl) ⟨409901, by rfl⟩ : syracuseStep 546535 = 819803) B819803
theorem B546663 : Blo 542804 546663 := bstep (se 1 (by rfl) ⟨409997, by rfl⟩ : syracuseStep 546663 = 819995) B819995
theorem B612463 : Blo 542804 612463 := bstep (se 1 (by rfl) ⟨459347, by rfl⟩ : syracuseStep 612463 = 918695) B918695
theorem B1104743 : Blo 542804 1104743 := bstep (se 1 (by rfl) ⟨828557, by rfl⟩ : syracuseStep 1104743 = 1657115) B1657115
theorem B10084121 : Blo 542804 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B2613055 : Blo 542804 2613055 := bstep (se 1 (by rfl) ⟨1959791, by rfl⟩ : syracuseStep 2613055 = 3919583) B3919583
theorem B2351273 : Blo 542804 2351273 := bstep (se 2 (by rfl) ⟨881727, by rfl⟩ : syracuseStep 2351273 = 1763455) B1763455
theorem B1401001 : Blo 542804 1401001 := bstep (se 2 (by rfl) ⟨525375, by rfl⟩ : syracuseStep 1401001 = 1050751) B1050751
theorem B1106543 : Blo 542804 1106543 := bstep (se 1 (by rfl) ⟨829907, by rfl⟩ : syracuseStep 1106543 = 1659815) B1659815
theorem B40167131 : Blo 542804 40167131 := bstep (se 1 (by rfl) ⟨30125348, by rfl⟩ : syracuseStep 40167131 = 60250697) B60250697
theorem B2321399 : Blo 542804 2321399 := bstep (se 1 (by rfl) ⟨1741049, by rfl⟩ : syracuseStep 2321399 = 3482099) B3482099
theorem B5238107 : Blo 542804 5238107 := bstep (se 1 (by rfl) ⟨3928580, by rfl⟩ : syracuseStep 5238107 = 7857161) B7857161
theorem B9563603 : Blo 542804 9563603 := bstep (se 1 (by rfl) ⟨7172702, by rfl⟩ : syracuseStep 9563603 = 14345405) B14345405
theorem B814751 : Blo 542804 814751 := bstep (se 1 (by rfl) ⟨611063, by rfl⟩ : syracuseStep 814751 = 1222127) B1222127
theorem B2748329 : Blo 542804 2748329 := bstep (se 2 (by rfl) ⟨1030623, by rfl⟩ : syracuseStep 2748329 = 2061247) B2061247
theorem B815327 : Blo 542804 815327 := bstep (se 1 (by rfl) ⟨611495, by rfl⟩ : syracuseStep 815327 = 1222991) B1222991
theorem B2322731 : Blo 542804 2322731 := bstep (se 1 (by rfl) ⟨1742048, by rfl⟩ : syracuseStep 2322731 = 3484097) B3484097
theorem B815807 : Blo 542804 815807 := bstep (se 1 (by rfl) ⟨611855, by rfl⟩ : syracuseStep 815807 = 1223711) B1223711
theorem B816359 : Blo 542804 816359 := bstep (se 1 (by rfl) ⟨612269, by rfl⟩ : syracuseStep 816359 = 1224539) B1224539
theorem B4126139 : Blo 542804 4126139 := bstep (se 1 (by rfl) ⟨3094604, by rfl⟩ : syracuseStep 4126139 = 6189209) B6189209
theorem B2062523 : Blo 542804 2062523 := bstep (se 1 (by rfl) ⟨1546892, by rfl⟩ : syracuseStep 2062523 = 3093785) B3093785
theorem B817535 : Blo 542804 817535 := bstep (se 1 (by rfl) ⟨613151, by rfl⟩ : syracuseStep 817535 = 1226303) B1226303
theorem B653879 : Blo 542804 653879 := bstep (se 1 (by rfl) ⟨490409, by rfl⟩ : syracuseStep 653879 = 980819) B980819
theorem B18152099 : Blo 542804 18152099 := bstep (se 1 (by rfl) ⟨13614074, by rfl⟩ : syracuseStep 18152099 = 27228149) B27228149
theorem B818111 : Blo 542804 818111 := bstep (se 1 (by rfl) ⟨613583, by rfl⟩ : syracuseStep 818111 = 1227167) B1227167
theorem B818153 : Blo 542804 818153 := bstep (se 2 (by rfl) ⟨306807, by rfl⟩ : syracuseStep 818153 = 613615) B613615
theorem B916535 : Blo 542804 916535 := bstep (se 1 (by rfl) ⟨687401, by rfl⟩ : syracuseStep 916535 = 1374803) B1374803
theorem B818231 : Blo 542804 818231 := bstep (se 1 (by rfl) ⟨613673, by rfl⟩ : syracuseStep 818231 = 1227347) B1227347
theorem B818303 : Blo 542804 818303 := bstep (se 1 (by rfl) ⟨613727, by rfl⟩ : syracuseStep 818303 = 1227455) B1227455
theorem B2063495 : Blo 542804 2063495 := bstep (se 1 (by rfl) ⟨1547621, by rfl⟩ : syracuseStep 2063495 = 3095243) B3095243
theorem B2325671 : Blo 542804 2325671 := bstep (se 1 (by rfl) ⟨1744253, by rfl⟩ : syracuseStep 2325671 = 3488507) B3488507
theorem B917831 : Blo 542804 917831 := bstep (se 1 (by rfl) ⟨688373, by rfl⟩ : syracuseStep 917831 = 1376747) B1376747
theorem B1835675 : Blo 542804 1835675 := bstep (se 1 (by rfl) ⟨1376756, by rfl⟩ : syracuseStep 1835675 = 2753513) B2753513
theorem B983839 : Blo 542804 983839 := bstep (se 1 (by rfl) ⟨737879, by rfl⟩ : syracuseStep 983839 = 1475759) B1475759
theorem B2491327 : Blo 542804 2491327 := bstep (se 1 (by rfl) ⟨1868495, by rfl⟩ : syracuseStep 2491327 = 3736991) B3736991
theorem B44663885 : Blo 542804 44663885 := bstep (se 3 (by rfl) ⟨8374478, by rfl⟩ : syracuseStep 44663885 = 16748957) B16748957
theorem B2754323 : Blo 542804 2754323 := bstep (se 1 (by rfl) ⟨2065742, by rfl⟩ : syracuseStep 2754323 = 4131485) B4131485
theorem B1836863 : Blo 542804 1836863 := bstep (se 1 (by rfl) ⟨1377647, by rfl⟩ : syracuseStep 1836863 = 2755295) B2755295
theorem B3934345 : Blo 542804 3934345 := bstep (se 2 (by rfl) ⟨1475379, by rfl⟩ : syracuseStep 3934345 = 2950759) B2950759
theorem B5900519 : Blo 542804 5900519 := bstep (se 1 (by rfl) ⟨4425389, by rfl⟩ : syracuseStep 5900519 = 8850779) B8850779
theorem B1837835 : Blo 542804 1837835 := bstep (se 1 (by rfl) ⟨1378376, by rfl⟩ : syracuseStep 1837835 = 2756753) B2756753
theorem B6622235 : Blo 542804 6622235 := bstep (se 1 (by rfl) ⟨4966676, by rfl⟩ : syracuseStep 6622235 = 9933353) B9933353
theorem B920767 : Blo 542804 920767 := bstep (se 1 (by rfl) ⟨690575, by rfl⟩ : syracuseStep 920767 = 1381151) B1381151
theorem B1576255 : Blo 542804 1576255 := bstep (se 1 (by rfl) ⟨1182191, by rfl⟩ : syracuseStep 1576255 = 2364383) B2364383
theorem B29888021 : Blo 542804 29888021 := bstep (se 6 (by rfl) ⟨700500, by rfl⟩ : syracuseStep 29888021 = 1401001) B1401001
theorem B921577 : Blo 542804 921577 := bstep (se 2 (by rfl) ⟨345591, by rfl⟩ : syracuseStep 921577 = 691183) B691183
theorem B1380665 : Blo 542804 1380665 := bstep (se 2 (by rfl) ⟨517749, by rfl⟩ : syracuseStep 1380665 = 1035499) B1035499
theorem B6722747 : Blo 542804 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B6624665 : Blo 542804 6624665 := bstep (se 2 (by rfl) ⟨2484249, by rfl⟩ : syracuseStep 6624665 = 4968499) B4968499
theorem B4134401 : Blo 542804 4134401 := bstep (se 2 (by rfl) ⟨1550400, by rfl⟩ : syracuseStep 4134401 = 3100801) B3100801
theorem B3348937 : Blo 542804 3348937 := bstep (se 2 (by rfl) ⟨1255851, by rfl⟩ : syracuseStep 3348937 = 2511703) B2511703
theorem B1743677 : Blo 542804 1743677 := bstep (se 3 (by rfl) ⟨326939, by rfl⟩ : syracuseStep 1743677 = 653879) B653879
theorem B1383551 : Blo 542804 1383551 := bstep (se 1 (by rfl) ⟨1037663, by rfl⟩ : syracuseStep 1383551 = 2075327) B2075327
theorem B1842479 : Blo 542804 1842479 := bstep (se 1 (by rfl) ⟨1381859, by rfl⟩ : syracuseStep 1842479 = 2763719) B2763719
theorem B1547599 : Blo 542804 1547599 := bstep (se 1 (by rfl) ⟨1160699, by rfl⟩ : syracuseStep 1547599 = 2321399) B2321399
theorem B1548487 : Blo 542804 1548487 := bstep (se 1 (by rfl) ⟨1161365, by rfl⟩ : syracuseStep 1548487 = 2322731) B2322731
theorem B1843613 : Blo 542804 1843613 := bstep (se 3 (by rfl) ⟨345677, by rfl⟩ : syracuseStep 1843613 = 691355) B691355
theorem B7152083 : Blo 542804 7152083 := bstep (se 1 (by rfl) ⟨5364062, by rfl⟩ : syracuseStep 7152083 = 10728125) B10728125
theorem B2761937 : Blo 542804 2761937 := bstep (se 2 (by rfl) ⟨1035726, by rfl⟩ : syracuseStep 2761937 = 2071453) B2071453
theorem B25502941 : Blo 542804 25502941 := bstep (se 3 (by rfl) ⟨4781801, by rfl⟩ : syracuseStep 25502941 = 9563603) B9563603
theorem B12101399 : Blo 542804 12101399 := bstep (se 1 (by rfl) ⟨9076049, by rfl⟩ : syracuseStep 12101399 = 18152099) B18152099
theorem B1845017 : Blo 542804 1845017 := bstep (se 2 (by rfl) ⟨691881, by rfl⟩ : syracuseStep 1845017 = 1383763) B1383763
theorem B5908477 : Blo 542804 5908477 := bstep (se 3 (by rfl) ⟨1107839, by rfl⟩ : syracuseStep 5908477 = 2215679) B2215679
theorem B1550447 : Blo 542804 1550447 := bstep (se 1 (by rfl) ⟨1162835, by rfl⟩ : syracuseStep 1550447 = 2325671) B2325671
theorem B3484073 : Blo 542804 3484073 := bstep (se 2 (by rfl) ⟨1306527, by rfl⟩ : syracuseStep 3484073 = 2613055) B2613055
theorem B2763881 : Blo 542804 2763881 := bstep (se 2 (by rfl) ⟨1036455, by rfl⟩ : syracuseStep 2763881 = 2072911) B2072911
theorem B6270061 : Blo 542804 6270061 := bstep (se 3 (by rfl) ⟨1175636, by rfl⟩ : syracuseStep 6270061 = 2351273) B2351273
theorem B43069027 : Blo 542804 43069027 := bstep (se 1 (by rfl) ⟨32301770, by rfl⟩ : syracuseStep 43069027 = 64603541) B64603541
theorem B1224431 : Blo 542804 1224431 := bstep (se 1 (by rfl) ⟨918323, by rfl⟩ : syracuseStep 1224431 = 1836647) B1836647
theorem B3321623 : Blo 542804 3321623 := bstep (se 1 (by rfl) ⟨2491217, by rfl⟩ : syracuseStep 3321623 = 4982435) B4982435
theorem B3486199 : Blo 542804 3486199 := bstep (se 1 (by rfl) ⟨2614649, by rfl⟩ : syracuseStep 3486199 = 5229299) B5229299
theorem B1553033 : Blo 542804 1553033 := bstep (se 2 (by rfl) ⟨582387, by rfl⟩ : syracuseStep 1553033 = 1164775) B1164775
theorem B1225583 : Blo 542804 1225583 := bstep (se 1 (by rfl) ⟨919187, by rfl⟩ : syracuseStep 1225583 = 1838375) B1838375
theorem B6632351 : Blo 542804 6632351 := bstep (se 1 (by rfl) ⟨4974263, by rfl⟩ : syracuseStep 6632351 = 9948527) B9948527
theorem B3913211 : Blo 542804 3913211 := bstep (se 1 (by rfl) ⟨2934908, by rfl⟩ : syracuseStep 3913211 = 5869817) B5869817
theorem B39794651 : Blo 542804 39794651 := bstep (se 1 (by rfl) ⟨29845988, by rfl⟩ : syracuseStep 39794651 = 59691977) B59691977
theorem B1227617 : Blo 542804 1227617 := bstep (se 2 (by rfl) ⟨460356, by rfl⟩ : syracuseStep 1227617 = 920713) B920713
theorem B42515513 : Blo 542804 42515513 := bstep (se 2 (by rfl) ⟨15943317, by rfl⟩ : syracuseStep 42515513 = 31886635) B31886635
theorem B736495 : Blo 542804 736495 := bstep (se 1 (by rfl) ⟨552371, by rfl⟩ : syracuseStep 736495 = 1104743) B1104743
theorem B1228139 : Blo 542804 1228139 := bstep (se 1 (by rfl) ⟨921104, by rfl⟩ : syracuseStep 1228139 = 1842209) B1842209
theorem B3096701 : Blo 542804 3096701 := bstep (se 3 (by rfl) ⟨580631, by rfl⟩ : syracuseStep 3096701 = 1161263) B1161263
theorem B1229039 : Blo 542804 1229039 := bstep (se 1 (by rfl) ⟨921779, by rfl⟩ : syracuseStep 1229039 = 1843559) B1843559
theorem B737695 : Blo 542804 737695 := bstep (se 1 (by rfl) ⟨553271, by rfl⟩ : syracuseStep 737695 = 1106543) B1106543
theorem B8964179 : Blo 542804 8964179 := bstep (se 1 (by rfl) ⟨6723134, by rfl⟩ : syracuseStep 8964179 = 13446269) B13446269
theorem B3492071 : Blo 542804 3492071 := bstep (se 1 (by rfl) ⟨2619053, by rfl⟩ : syracuseStep 3492071 = 5238107) B5238107
theorem B543167 : Blo 542804 543167 := bstep (se 1 (by rfl) ⟨407375, by rfl⟩ : syracuseStep 543167 = 814751) B814751
theorem B543551 : Blo 542804 543551 := bstep (se 1 (by rfl) ⟨407663, by rfl⟩ : syracuseStep 543551 = 815327) B815327
theorem B543871 : Blo 542804 543871 := bstep (se 1 (by rfl) ⟨407903, by rfl⟩ : syracuseStep 543871 = 815807) B815807
theorem B544239 : Blo 542804 544239 := bstep (se 1 (by rfl) ⟨408179, by rfl⟩ : syracuseStep 544239 = 816359) B816359
theorem B10505801 : Blo 542804 10505801 := bstep (se 2 (by rfl) ⟨3939675, by rfl⟩ : syracuseStep 10505801 = 7879351) B7879351
theorem B545023 : Blo 542804 545023 := bstep (se 1 (by rfl) ⟨408767, by rfl⟩ : syracuseStep 545023 = 817535) B817535
theorem B774631 : Blo 542804 774631 := bstep (se 1 (by rfl) ⟨580973, by rfl⟩ : syracuseStep 774631 = 1161947) B1161947
theorem B545407 : Blo 542804 545407 := bstep (se 1 (by rfl) ⟨409055, by rfl⟩ : syracuseStep 545407 = 818111) B818111
theorem B545435 : Blo 542804 545435 := bstep (se 1 (by rfl) ⟨409076, by rfl⟩ : syracuseStep 545435 = 818153) B818153
theorem B611023 : Blo 542804 611023 := bstep (se 1 (by rfl) ⟨458267, by rfl⟩ : syracuseStep 611023 = 916535) B916535
theorem B545487 : Blo 542804 545487 := bstep (se 1 (by rfl) ⟨409115, by rfl⟩ : syracuseStep 545487 = 818231) B818231
theorem B545535 : Blo 542804 545535 := bstep (se 1 (by rfl) ⟨409151, by rfl⟩ : syracuseStep 545535 = 818303) B818303
theorem B17717129 : Blo 542804 17717129 := bstep (se 2 (by rfl) ⟨6643923, by rfl⟩ : syracuseStep 17717129 = 13287847) B13287847
theorem B546727 : Blo 542804 546727 := bstep (se 1 (by rfl) ⟨410045, by rfl⟩ : syracuseStep 546727 = 820091) B820091
theorem B225957923 : Blo 542804 225957923 := bstep (se 1 (by rfl) ⟨169468442, by rfl⟩ : syracuseStep 225957923 = 338936885) B338936885
theorem B35772509 : Blo 542804 35772509 := bstep (se 3 (by rfl) ⟨6707345, by rfl⟩ : syracuseStep 35772509 = 13414691) B13414691
theorem B53696621 : Blo 542804 53696621 := bstep (se 3 (by rfl) ⟨10068116, by rfl⟩ : syracuseStep 53696621 = 20136233) B20136233
theorem B3103535 : Blo 542804 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B3498653 : Blo 542804 3498653 := bstep (se 3 (by rfl) ⟨655997, by rfl⟩ : syracuseStep 3498653 = 1311995) B1311995
theorem B107112349 : Blo 542804 107112349 := bstep (se 3 (by rfl) ⟨20083565, by rfl⟩ : syracuseStep 107112349 = 40167131) B40167131
theorem B1863119 : Blo 542804 1863119 := bstep (se 1 (by rfl) ⟨1397339, by rfl⟩ : syracuseStep 1863119 = 2794679) B2794679
theorem B23359013 : Blo 542804 23359013 := bstep (se 4 (by rfl) ⟨2189907, by rfl⟩ : syracuseStep 23359013 = 4379815) B4379815
theorem B814703 : Blo 542804 814703 := bstep (se 1 (by rfl) ⟨611027, by rfl⟩ : syracuseStep 814703 = 1222055) B1222055
theorem B1470287 : Blo 542804 1470287 := bstep (se 1 (by rfl) ⟨1102715, by rfl⟩ : syracuseStep 1470287 = 2205431) B2205431
theorem B815015 : Blo 542804 815015 := bstep (se 1 (by rfl) ⟨611261, by rfl⟩ : syracuseStep 815015 = 1222523) B1222523
theorem B551580299 : Blo 542804 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B815771 : Blo 542804 815771 := bstep (se 1 (by rfl) ⟨611828, by rfl⟩ : syracuseStep 815771 = 1223657) B1223657
theorem B815783 : Blo 542804 815783 := bstep (se 1 (by rfl) ⟨611837, by rfl⟩ : syracuseStep 815783 = 1223675) B1223675
theorem B1832219 : Blo 542804 1832219 := bstep (se 1 (by rfl) ⟨1374164, by rfl⟩ : syracuseStep 1832219 = 2748329) B2748329
theorem B816617 : Blo 542804 816617 := bstep (se 2 (by rfl) ⟨306231, by rfl⟩ : syracuseStep 816617 = 612463) B612463
theorem B2750759 : Blo 542804 2750759 := bstep (se 1 (by rfl) ⟨2063069, by rfl⟩ : syracuseStep 2750759 = 4126139) B4126139
theorem B6224201 : Blo 542804 6224201 := bstep (se 2 (by rfl) ⟨2334075, by rfl⟩ : syracuseStep 6224201 = 4668151) B4668151
theorem B817487 : Blo 542804 817487 := bstep (se 1 (by rfl) ⟨613115, by rfl⟩ : syracuseStep 817487 = 1226231) B1226231
theorem B6977987 : Blo 542804 6977987 := bstep (se 1 (by rfl) ⟨5233490, by rfl⟩ : syracuseStep 6977987 = 10466981) B10466981
theorem B1375015 : Blo 542804 1375015 := bstep (se 1 (by rfl) ⟨1031261, by rfl⟩ : syracuseStep 1375015 = 2062523) B2062523
theorem B1375663 : Blo 542804 1375663 := bstep (se 1 (by rfl) ⟨1031747, by rfl⟩ : syracuseStep 1375663 = 2063495) B2063495
theorem B818687 : Blo 542804 818687 := bstep (se 1 (by rfl) ⟨614015, by rfl⟩ : syracuseStep 818687 = 1228031) B1228031
theorem B818843 : Blo 542804 818843 := bstep (se 1 (by rfl) ⟨614132, by rfl⟩ : syracuseStep 818843 = 1228265) B1228265
theorem B2064467 : Blo 542804 2064467 := bstep (se 1 (by rfl) ⟨1548350, by rfl⟩ : syracuseStep 2064467 = 3096701) B3096701
theorem B819359 : Blo 542804 819359 := bstep (se 1 (by rfl) ⟨614519, by rfl⟩ : syracuseStep 819359 = 1229039) B1229039
theorem B2064649 : Blo 542804 2064649 := bstep (se 2 (by rfl) ⟨774243, by rfl⟩ : syracuseStep 2064649 = 1548487) B1548487
theorem B983593 : Blo 542804 983593 := bstep (se 2 (by rfl) ⟨368847, by rfl⟩ : syracuseStep 983593 = 737695) B737695
theorem B1311785 : Blo 542804 1311785 := bstep (se 2 (by rfl) ⟨491919, by rfl⟩ : syracuseStep 1311785 = 983839) B983839
theorem B1836215 : Blo 542804 1836215 := bstep (se 1 (by rfl) ⟨1377161, by rfl⟩ : syracuseStep 1836215 = 2754323) B2754323
theorem B2328047 : Blo 542804 2328047 := bstep (se 1 (by rfl) ⟨1746035, by rfl⟩ : syracuseStep 2328047 = 3492071) B3492071
theorem B3933679 : Blo 542804 3933679 := bstep (se 1 (by rfl) ⟨2950259, by rfl⟩ : syracuseStep 3933679 = 5900519) B5900519
theorem B19925347 : Blo 542804 19925347 := bstep (se 1 (by rfl) ⟨14944010, by rfl⟩ : syracuseStep 19925347 = 29888021) B29888021
theorem B5245793 : Blo 542804 5245793 := bstep (se 2 (by rfl) ⟨1967172, by rfl⟩ : syracuseStep 5245793 = 3934345) B3934345
theorem B920443 : Blo 542804 920443 := bstep (se 1 (by rfl) ⟨690332, by rfl⟩ : syracuseStep 920443 = 1380665) B1380665
theorem B2756267 : Blo 542804 2756267 := bstep (se 1 (by rfl) ⟨2067200, by rfl⟩ : syracuseStep 2756267 = 4134401) B4134401
theorem B150638615 : Blo 542804 150638615 := bstep (se 1 (by rfl) ⟨112978961, by rfl⟩ : syracuseStep 150638615 = 225957923) B225957923
theorem B8360081 : Blo 542804 8360081 := bstep (se 2 (by rfl) ⟨3135030, by rfl⟩ : syracuseStep 8360081 = 6270061) B6270061
theorem B2101673 : Blo 542804 2101673 := bstep (se 2 (by rfl) ⟨788127, by rfl⟩ : syracuseStep 2101673 = 1576255) B1576255
theorem B2069023 : Blo 542804 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B922367 : Blo 542804 922367 := bstep (se 1 (by rfl) ⟨691775, by rfl⟩ : syracuseStep 922367 = 1383551) B1383551
theorem B1841291 : Blo 542804 1841291 := bstep (se 1 (by rfl) ⟨1380968, by rfl⟩ : syracuseStep 1841291 = 2761937) B2761937
theorem B8067599 : Blo 542804 8067599 := bstep (se 1 (by rfl) ⟨6050699, by rfl⟩ : syracuseStep 8067599 = 12101399) B12101399
theorem B1842587 : Blo 542804 1842587 := bstep (se 1 (by rfl) ⟨1381940, by rfl⟩ : syracuseStep 1842587 = 2763881) B2763881
theorem B15572675 : Blo 542804 15572675 := bstep (se 1 (by rfl) ⟨11679506, by rfl⟩ : syracuseStep 15572675 = 23359013) B23359013
theorem B4465249 : Blo 542804 4465249 := bstep (se 2 (by rfl) ⟨1674468, by rfl⟩ : syracuseStep 4465249 = 3348937) B3348937
theorem B1221479 : Blo 542804 1221479 := bstep (se 1 (by rfl) ⟨916109, by rfl⟩ : syracuseStep 1221479 = 1832219) B1832219
theorem B1223783 : Blo 542804 1223783 := bstep (se 1 (by rfl) ⟨917837, by rfl⟩ : syracuseStep 1223783 = 1835675) B1835675
theorem B1224575 : Blo 542804 1224575 := bstep (se 1 (by rfl) ⟨918431, by rfl⟩ : syracuseStep 1224575 = 1836863) B1836863
theorem B3321769 : Blo 542804 3321769 := bstep (se 2 (by rfl) ⟨1245663, by rfl⟩ : syracuseStep 3321769 = 2491327) B2491327
theorem B5976119 : Blo 542804 5976119 := bstep (se 1 (by rfl) ⟨4482089, by rfl⟩ : syracuseStep 5976119 = 8964179) B8964179
theorem B1225223 : Blo 542804 1225223 := bstep (se 1 (by rfl) ⟨918917, by rfl⟩ : syracuseStep 1225223 = 1837835) B1837835
theorem B142816465 : Blo 542804 142816465 := bstep (se 2 (by rfl) ⟨53556174, by rfl⟩ : syracuseStep 142816465 = 107112349) B107112349
theorem B7877969 : Blo 542804 7877969 := bstep (se 2 (by rfl) ⟨2954238, by rfl⟩ : syracuseStep 7877969 = 5908477) B5908477
theorem B11811419 : Blo 542804 11811419 := bstep (se 1 (by rfl) ⟨8858564, by rfl⟩ : syracuseStep 11811419 = 17717129) B17717129
theorem B35797747 : Blo 542804 35797747 := bstep (se 1 (by rfl) ⟨26848310, by rfl⟩ : syracuseStep 35797747 = 53696621) B53696621
theorem B1227689 : Blo 542804 1227689 := bstep (se 2 (by rfl) ⟨460383, by rfl⟩ : syracuseStep 1227689 = 920767) B920767
theorem B1162451 : Blo 542804 1162451 := bstep (se 1 (by rfl) ⟨871838, by rfl⟩ : syracuseStep 1162451 = 1743677) B1743677
theorem B57425369 : Blo 542804 57425369 := bstep (se 2 (by rfl) ⟨21534513, by rfl⟩ : syracuseStep 57425369 = 43069027) B43069027
theorem B1228319 : Blo 542804 1228319 := bstep (se 1 (by rfl) ⟨921239, by rfl⟩ : syracuseStep 1228319 = 1842479) B1842479
theorem B1228769 : Blo 542804 1228769 := bstep (se 2 (by rfl) ⟨460788, by rfl⟩ : syracuseStep 1228769 = 921577) B921577
theorem B1229075 : Blo 542804 1229075 := bstep (se 1 (by rfl) ⟨921806, by rfl⟩ : syracuseStep 1229075 = 1843613) B1843613
theorem B4768055 : Blo 542804 4768055 := bstep (se 1 (by rfl) ⟨3576041, by rfl⟩ : syracuseStep 4768055 = 7152083) B7152083
theorem B1032841 : Blo 542804 1032841 := bstep (se 2 (by rfl) ⟨387315, by rfl⟩ : syracuseStep 1032841 = 774631) B774631
theorem B1230011 : Blo 542804 1230011 := bstep (se 1 (by rfl) ⟨922508, by rfl⟩ : syracuseStep 1230011 = 1845017) B1845017
theorem B1033631 : Blo 542804 1033631 := bstep (se 1 (by rfl) ⟨775223, by rfl⟩ : syracuseStep 1033631 = 1550447) B1550447
theorem B543135 : Blo 542804 543135 := bstep (se 1 (by rfl) ⟨407351, by rfl⟩ : syracuseStep 543135 = 814703) B814703
theorem B2214415 : Blo 542804 2214415 := bstep (se 1 (by rfl) ⟨1660811, by rfl⟩ : syracuseStep 2214415 = 3321623) B3321623
theorem B543343 : Blo 542804 543343 := bstep (se 1 (by rfl) ⟨407507, by rfl⟩ : syracuseStep 543343 = 815015) B815015
theorem B1035355 : Blo 542804 1035355 := bstep (se 1 (by rfl) ⟨776516, by rfl⟩ : syracuseStep 1035355 = 1553033) B1553033
theorem B543847 : Blo 542804 543847 := bstep (se 1 (by rfl) ⟨407885, by rfl⟩ : syracuseStep 543847 = 815771) B815771
theorem B543855 : Blo 542804 543855 := bstep (se 1 (by rfl) ⟨407891, by rfl⟩ : syracuseStep 543855 = 815783) B815783
theorem B544411 : Blo 542804 544411 := bstep (se 1 (by rfl) ⟨408308, by rfl⟩ : syracuseStep 544411 = 816617) B816617
theorem B2608807 : Blo 542804 2608807 := bstep (se 1 (by rfl) ⟨1956605, by rfl⟩ : syracuseStep 2608807 = 3913211) B3913211
theorem B4968317 : Blo 542804 4968317 := bstep (se 3 (by rfl) ⟨931559, by rfl⟩ : syracuseStep 4968317 = 1863119) B1863119
theorem B26529767 : Blo 542804 26529767 := bstep (se 1 (by rfl) ⟨19897325, by rfl⟩ : syracuseStep 26529767 = 39794651) B39794651
theorem B4149467 : Blo 542804 4149467 := bstep (se 1 (by rfl) ⟨3112100, by rfl⟩ : syracuseStep 4149467 = 6224201) B6224201
theorem B544991 : Blo 542804 544991 := bstep (se 1 (by rfl) ⟨408743, by rfl⟩ : syracuseStep 544991 = 817487) B817487
theorem B545791 : Blo 542804 545791 := bstep (se 1 (by rfl) ⟨409343, by rfl⟩ : syracuseStep 545791 = 818687) B818687
theorem B545895 : Blo 542804 545895 := bstep (se 1 (by rfl) ⟨409421, by rfl⟩ : syracuseStep 545895 = 818843) B818843
theorem B611887 : Blo 542804 611887 := bstep (se 1 (by rfl) ⟨458915, by rfl⟩ : syracuseStep 611887 = 917831) B917831
theorem B29775923 : Blo 542804 29775923 := bstep (se 1 (by rfl) ⟨22331942, by rfl⟩ : syracuseStep 29775923 = 44663885) B44663885
theorem B34003921 : Blo 542804 34003921 := bstep (se 2 (by rfl) ⟨12751470, by rfl⟩ : syracuseStep 34003921 = 25502941) B25502941
theorem B9329741 : Blo 542804 9329741 := bstep (se 3 (by rfl) ⟨1749326, by rfl⟩ : syracuseStep 9329741 = 3498653) B3498653
theorem B4414823 : Blo 542804 4414823 := bstep (se 1 (by rfl) ⟨3311117, by rfl⟩ : syracuseStep 4414823 = 6622235) B6622235
theorem B7003867 : Blo 542804 7003867 := bstep (se 1 (by rfl) ⟨5252900, by rfl⟩ : syracuseStep 7003867 = 10505801) B10505801
theorem B4481831 : Blo 542804 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B4416443 : Blo 542804 4416443 := bstep (se 1 (by rfl) ⟨3312332, by rfl⟩ : syracuseStep 4416443 = 6624665) B6624665
theorem B23848339 : Blo 542804 23848339 := bstep (se 1 (by rfl) ⟨17886254, by rfl⟩ : syracuseStep 23848339 = 35772509) B35772509
theorem B4648265 : Blo 542804 4648265 := bstep (se 2 (by rfl) ⟨1743099, by rfl⟩ : syracuseStep 4648265 = 3486199) B3486199
theorem B814697 : Blo 542804 814697 := bstep (se 2 (by rfl) ⟨305511, by rfl⟩ : syracuseStep 814697 = 611023) B611023
theorem B3927973 : Blo 542804 3927973 := bstep (se 4 (by rfl) ⟨368247, by rfl⟩ : syracuseStep 3927973 = 736495) B736495
theorem B2322715 : Blo 542804 2322715 := bstep (se 1 (by rfl) ⟨1742036, by rfl⟩ : syracuseStep 2322715 = 3484073) B3484073
theorem B816287 : Blo 542804 816287 := bstep (se 1 (by rfl) ⟨612215, by rfl⟩ : syracuseStep 816287 = 1224431) B1224431
theorem B980191 : Blo 542804 980191 := bstep (se 1 (by rfl) ⟨735143, by rfl⟩ : syracuseStep 980191 = 1470287) B1470287
theorem B367720199 : Blo 542804 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B817055 : Blo 542804 817055 := bstep (se 1 (by rfl) ⟨612791, by rfl⟩ : syracuseStep 817055 = 1225583) B1225583
theorem B4421567 : Blo 542804 4421567 := bstep (se 1 (by rfl) ⟨3316175, by rfl⟩ : syracuseStep 4421567 = 6632351) B6632351
theorem B1833353 : Blo 542804 1833353 := bstep (se 2 (by rfl) ⟨687507, by rfl⟩ : syracuseStep 1833353 = 1375015) B1375015
theorem B1833839 : Blo 542804 1833839 := bstep (se 1 (by rfl) ⟨1375379, by rfl⟩ : syracuseStep 1833839 = 2750759) B2750759
theorem B4651991 : Blo 542804 4651991 := bstep (se 1 (by rfl) ⟨3488993, by rfl⟩ : syracuseStep 4651991 = 6977987) B6977987
theorem B2063465 : Blo 542804 2063465 := bstep (se 2 (by rfl) ⟨773799, by rfl⟩ : syracuseStep 2063465 = 1547599) B1547599
theorem B1834217 : Blo 542804 1834217 := bstep (se 2 (by rfl) ⟨687831, by rfl⟩ : syracuseStep 1834217 = 1375663) B1375663
theorem B818411 : Blo 542804 818411 := bstep (se 1 (by rfl) ⟨613808, by rfl⟩ : syracuseStep 818411 = 1227617) B1227617
theorem B28343675 : Blo 542804 28343675 := bstep (se 1 (by rfl) ⟨21257756, by rfl⟩ : syracuseStep 28343675 = 42515513) B42515513
theorem B818759 : Blo 542804 818759 := bstep (se 1 (by rfl) ⟨614069, by rfl⟩ : syracuseStep 818759 = 1228139) B1228139
theorem B1376311 : Blo 542804 1376311 := bstep (se 1 (by rfl) ⟨1032233, by rfl⟩ : syracuseStep 1376311 = 2064467) B2064467
theorem B819383 : Blo 542804 819383 := bstep (se 1 (by rfl) ⟨614537, by rfl⟩ : syracuseStep 819383 = 1229075) B1229075
theorem B3178703 : Blo 542804 3178703 := bstep (se 1 (by rfl) ⟨2384027, by rfl⟩ : syracuseStep 3178703 = 4768055) B4768055
theorem B2752865 : Blo 542804 2752865 := bstep (se 2 (by rfl) ⟨1032324, by rfl⟩ : syracuseStep 2752865 = 2064649) B2064649
theorem B820007 : Blo 542804 820007 := bstep (se 1 (by rfl) ⟨615005, by rfl⟩ : syracuseStep 820007 = 1230011) B1230011
theorem B1377121 : Blo 542804 1377121 := bstep (se 2 (by rfl) ⟨516420, by rfl⟩ : syracuseStep 1377121 = 1032841) B1032841
theorem B689087 : Blo 542804 689087 := bstep (se 1 (by rfl) ⟨516815, by rfl⟩ : syracuseStep 689087 = 1033631) B1033631
theorem B5604461 : Blo 542804 5604461 := bstep (se 3 (by rfl) ⟨1050836, by rfl⟩ : syracuseStep 5604461 = 2101673) B2101673
theorem B5244905 : Blo 542804 5244905 := bstep (se 2 (by rfl) ⟨1966839, by rfl⟩ : syracuseStep 5244905 = 3933679) B3933679
theorem B1837511 : Blo 542804 1837511 := bstep (se 1 (by rfl) ⟨1378133, by rfl⟩ : syracuseStep 1837511 = 2756267) B2756267
theorem B5573387 : Blo 542804 5573387 := bstep (se 1 (by rfl) ⟨4180040, by rfl⟩ : syracuseStep 5573387 = 8360081) B8360081
theorem B5245829 : Blo 542804 5245829 := bstep (se 4 (by rfl) ⟨491796, by rfl⟩ : syracuseStep 5245829 = 983593) B983593
theorem B2952553 : Blo 542804 2952553 := bstep (se 2 (by rfl) ⟨1107207, by rfl⟩ : syracuseStep 2952553 = 2214415) B2214415
theorem B1380473 : Blo 542804 1380473 := bstep (se 2 (by rfl) ⟨517677, by rfl⟩ : syracuseStep 1380473 = 1035355) B1035355
theorem B5378399 : Blo 542804 5378399 := bstep (se 1 (by rfl) ⟨4033799, by rfl⟩ : syracuseStep 5378399 = 8067599) B8067599
theorem B3478409 : Blo 542804 3478409 := bstep (se 2 (by rfl) ⟨1304403, by rfl⟩ : syracuseStep 3478409 = 2608807) B2608807
theorem B4429025 : Blo 542804 4429025 := bstep (se 2 (by rfl) ⟨1660884, by rfl⟩ : syracuseStep 4429025 = 3321769) B3321769
theorem B2987887 : Blo 542804 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B2758697 : Blo 542804 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B5251979 : Blo 542804 5251979 := bstep (se 1 (by rfl) ⟨3938984, by rfl⟩ : syracuseStep 5251979 = 7877969) B7877969
theorem B245146799 : Blo 542804 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B153134317 : Blo 542804 153134317 := bstep (se 3 (by rfl) ⟨28712684, by rfl⟩ : syracuseStep 153134317 = 57425369) B57425369
theorem B1222235 : Blo 542804 1222235 := bstep (se 1 (by rfl) ⟨916676, by rfl⟩ : syracuseStep 1222235 = 1833353) B1833353
theorem B7874279 : Blo 542804 7874279 := bstep (se 1 (by rfl) ⟨5905709, by rfl⟩ : syracuseStep 7874279 = 11811419) B11811419
theorem B41527133 : Blo 542804 41527133 := bstep (se 3 (by rfl) ⟨7786337, by rfl⟩ : syracuseStep 41527133 = 15572675) B15572675
theorem B1222559 : Blo 542804 1222559 := bstep (se 1 (by rfl) ⟨916919, by rfl⟩ : syracuseStep 1222559 = 1833839) B1833839
theorem B1222811 : Blo 542804 1222811 := bstep (se 1 (by rfl) ⟨917108, by rfl⟩ : syracuseStep 1222811 = 1834217) B1834217
theorem B13248845 : Blo 542804 13248845 := bstep (se 3 (by rfl) ⟨2484158, by rfl⟩ : syracuseStep 13248845 = 4968317) B4968317
theorem B1224143 : Blo 542804 1224143 := bstep (se 1 (by rfl) ⟨918107, by rfl⟩ : syracuseStep 1224143 = 1836215) B1836215
theorem B1552031 : Blo 542804 1552031 := bstep (se 1 (by rfl) ⟨1164023, by rfl⟩ : syracuseStep 1552031 = 2328047) B2328047
theorem B31797785 : Blo 542804 31797785 := bstep (se 2 (by rfl) ⟨11924169, by rfl⟩ : syracuseStep 31797785 = 23848339) B23848339
theorem B2766311 : Blo 542804 2766311 := bstep (se 1 (by rfl) ⟨2074733, by rfl⟩ : syracuseStep 2766311 = 4149467) B4149467
theorem B1227257 : Blo 542804 1227257 := bstep (se 2 (by rfl) ⟨460221, by rfl⟩ : syracuseStep 1227257 = 920443) B920443
theorem B1227527 : Blo 542804 1227527 := bstep (se 1 (by rfl) ⟨920645, by rfl⟩ : syracuseStep 1227527 = 1841291) B1841291
theorem B1228391 : Blo 542804 1228391 := bstep (se 1 (by rfl) ⟨921293, by rfl⟩ : syracuseStep 1228391 = 1842587) B1842587
theorem B3096953 : Blo 542804 3096953 := bstep (se 2 (by rfl) ⟨1161357, by rfl⟩ : syracuseStep 3096953 = 2322715) B2322715
theorem B3098843 : Blo 542804 3098843 := bstep (se 1 (by rfl) ⟨2324132, by rfl⟩ : syracuseStep 3098843 = 4648265) B4648265
theorem B543131 : Blo 542804 543131 := bstep (se 1 (by rfl) ⟨407348, by rfl⟩ : syracuseStep 543131 = 814697) B814697
theorem B3984079 : Blo 542804 3984079 := bstep (se 1 (by rfl) ⟨2988059, by rfl⟩ : syracuseStep 3984079 = 5976119) B5976119
theorem B3099869 : Blo 542804 3099869 := bstep (se 3 (by rfl) ⟨581225, by rfl⟩ : syracuseStep 3099869 = 1162451) B1162451
theorem B544191 : Blo 542804 544191 := bstep (se 1 (by rfl) ⟨408143, by rfl⟩ : syracuseStep 544191 = 816287) B816287
theorem B47730329 : Blo 542804 47730329 := bstep (se 2 (by rfl) ⟨17898873, by rfl⟩ : syracuseStep 47730329 = 35797747) B35797747
theorem B544703 : Blo 542804 544703 := bstep (se 1 (by rfl) ⟨408527, by rfl⟩ : syracuseStep 544703 = 817055) B817055
theorem B45338561 : Blo 542804 45338561 := bstep (se 2 (by rfl) ⟨17001960, by rfl⟩ : syracuseStep 45338561 = 34003921) B34003921
theorem B3101327 : Blo 542804 3101327 := bstep (se 1 (by rfl) ⟨2325995, by rfl⟩ : syracuseStep 3101327 = 4651991) B4651991
theorem B545607 : Blo 542804 545607 := bstep (se 1 (by rfl) ⟨409205, by rfl⟩ : syracuseStep 545607 = 818411) B818411
theorem B18895783 : Blo 542804 18895783 := bstep (se 1 (by rfl) ⟨14171837, by rfl⟩ : syracuseStep 18895783 = 28343675) B28343675
theorem B545839 : Blo 542804 545839 := bstep (se 1 (by rfl) ⟨409379, by rfl⟩ : syracuseStep 545839 = 818759) B818759
theorem B546239 : Blo 542804 546239 := bstep (se 1 (by rfl) ⟨409679, by rfl⟩ : syracuseStep 546239 = 819359) B819359
theorem B874523 : Blo 542804 874523 := bstep (se 1 (by rfl) ⟨655892, by rfl⟩ : syracuseStep 874523 = 1311785) B1311785
theorem B3497195 : Blo 542804 3497195 := bstep (se 1 (by rfl) ⟨2622896, by rfl⟩ : syracuseStep 3497195 = 5245793) B5245793
theorem B17686511 : Blo 542804 17686511 := bstep (se 1 (by rfl) ⟨13264883, by rfl⟩ : syracuseStep 17686511 = 26529767) B26529767
theorem B100425743 : Blo 542804 100425743 := bstep (se 1 (by rfl) ⟨75319307, by rfl⟩ : syracuseStep 100425743 = 150638615) B150638615
theorem B26567129 : Blo 542804 26567129 := bstep (se 2 (by rfl) ⟨9962673, by rfl⟩ : syracuseStep 26567129 = 19925347) B19925347
theorem B614911 : Blo 542804 614911 := bstep (se 1 (by rfl) ⟨461183, by rfl⟩ : syracuseStep 614911 = 922367) B922367
theorem B23814661 : Blo 542804 23814661 := bstep (se 4 (by rfl) ⟨2232624, by rfl⟩ : syracuseStep 23814661 = 4465249) B4465249
theorem B19850615 : Blo 542804 19850615 := bstep (se 1 (by rfl) ⟨14887961, by rfl⟩ : syracuseStep 19850615 = 29775923) B29775923
theorem B6219827 : Blo 542804 6219827 := bstep (se 1 (by rfl) ⟨4664870, by rfl⟩ : syracuseStep 6219827 = 9329741) B9329741
theorem B2943215 : Blo 542804 2943215 := bstep (se 1 (by rfl) ⟨2207411, by rfl⟩ : syracuseStep 2943215 = 4414823) B4414823
theorem B5237297 : Blo 542804 5237297 := bstep (se 2 (by rfl) ⟨1963986, by rfl⟩ : syracuseStep 5237297 = 3927973) B3927973
theorem B814319 : Blo 542804 814319 := bstep (se 1 (by rfl) ⟨610739, by rfl⟩ : syracuseStep 814319 = 1221479) B1221479
theorem B2944295 : Blo 542804 2944295 := bstep (se 1 (by rfl) ⟨2208221, by rfl⟩ : syracuseStep 2944295 = 4416443) B4416443
theorem B761687813 : Blo 542804 761687813 := bstep (se 4 (by rfl) ⟨71408232, by rfl⟩ : syracuseStep 761687813 = 142816465) B142816465
theorem B1306921 : Blo 542804 1306921 := bstep (se 2 (by rfl) ⟨490095, by rfl⟩ : syracuseStep 1306921 = 980191) B980191
theorem B815849 : Blo 542804 815849 := bstep (se 2 (by rfl) ⟨305943, by rfl⟩ : syracuseStep 815849 = 611887) B611887
theorem B815855 : Blo 542804 815855 := bstep (se 1 (by rfl) ⟨611891, by rfl⟩ : syracuseStep 815855 = 1223783) B1223783
theorem B816383 : Blo 542804 816383 := bstep (se 1 (by rfl) ⟨612287, by rfl⟩ : syracuseStep 816383 = 1224575) B1224575
theorem B816815 : Blo 542804 816815 := bstep (se 1 (by rfl) ⟨612611, by rfl⟩ : syracuseStep 816815 = 1225223) B1225223
theorem B2947711 : Blo 542804 2947711 := bstep (se 1 (by rfl) ⟨2210783, by rfl⟩ : syracuseStep 2947711 = 4421567) B4421567
theorem B818459 : Blo 542804 818459 := bstep (se 1 (by rfl) ⟨613844, by rfl⟩ : syracuseStep 818459 = 1227689) B1227689
theorem B1375643 : Blo 542804 1375643 := bstep (se 1 (by rfl) ⟨1031732, by rfl⟩ : syracuseStep 1375643 = 2063465) B2063465
theorem B9338489 : Blo 542804 9338489 := bstep (se 2 (by rfl) ⟨3501933, by rfl⟩ : syracuseStep 9338489 = 7003867) B7003867
theorem B818879 : Blo 542804 818879 := bstep (se 1 (by rfl) ⟨614159, by rfl⟩ : syracuseStep 818879 = 1228319) B1228319
theorem B819179 : Blo 542804 819179 := bstep (se 1 (by rfl) ⟨614384, by rfl⟩ : syracuseStep 819179 = 1228769) B1228769
theorem B1835081 : Blo 542804 1835081 := bstep (se 2 (by rfl) ⟨688155, by rfl⟩ : syracuseStep 1835081 = 1376311) B1376311
theorem B1835243 : Blo 542804 1835243 := bstep (se 1 (by rfl) ⟨1376432, by rfl⟩ : syracuseStep 1835243 = 2752865) B2752865
theorem B2064635 : Blo 542804 2064635 := bstep (se 1 (by rfl) ⟨1548476, by rfl⟩ : syracuseStep 2064635 = 3096953) B3096953
theorem B819881 : Blo 542804 819881 := bstep (se 2 (by rfl) ⟨307455, by rfl⟩ : syracuseStep 819881 = 614911) B614911
theorem B31752881 : Blo 542804 31752881 := bstep (se 2 (by rfl) ⟨11907330, by rfl⟩ : syracuseStep 31752881 = 23814661) B23814661
theorem B3736307 : Blo 542804 3736307 := bstep (se 1 (by rfl) ⟨2802230, by rfl⟩ : syracuseStep 3736307 = 5604461) B5604461
theorem B1836161 : Blo 542804 1836161 := bstep (se 2 (by rfl) ⟨688560, by rfl⟩ : syracuseStep 1836161 = 1377121) B1377121
theorem B2065895 : Blo 542804 2065895 := bstep (se 1 (by rfl) ⟨1549421, by rfl⟩ : syracuseStep 2065895 = 3098843) B3098843
theorem B2066579 : Blo 542804 2066579 := bstep (se 1 (by rfl) ⟨1549934, by rfl⟩ : syracuseStep 2066579 = 3099869) B3099869
theorem B31820219 : Blo 542804 31820219 := bstep (se 1 (by rfl) ⟨23865164, by rfl⟩ : syracuseStep 31820219 = 47730329) B47730329
theorem B1837565 : Blo 542804 1837565 := bstep (se 3 (by rfl) ⟨344543, by rfl⟩ : syracuseStep 1837565 = 689087) B689087
theorem B920315 : Blo 542804 920315 := bstep (se 1 (by rfl) ⟨690236, by rfl⟩ : syracuseStep 920315 = 1380473) B1380473
theorem B2067551 : Blo 542804 2067551 := bstep (se 1 (by rfl) ⟨1550663, by rfl⟩ : syracuseStep 2067551 = 3101327) B3101327
theorem B2952683 : Blo 542804 2952683 := bstep (se 1 (by rfl) ⟨2214512, by rfl⟩ : syracuseStep 2952683 = 4429025) B4429025
theorem B5312105 : Blo 542804 5312105 := bstep (se 2 (by rfl) ⟨1992039, by rfl⟩ : syracuseStep 5312105 = 3984079) B3984079
theorem B1839131 : Blo 542804 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B3936737 : Blo 542804 3936737 := bstep (se 2 (by rfl) ⟨1476276, by rfl⟩ : syracuseStep 3936737 = 2952553) B2952553
theorem B2331463 : Blo 542804 2331463 := bstep (se 1 (by rfl) ⟨1748597, by rfl⟩ : syracuseStep 2331463 = 3497195) B3497195
theorem B66950495 : Blo 542804 66950495 := bstep (se 1 (by rfl) ⟨50212871, by rfl⟩ : syracuseStep 66950495 = 100425743) B100425743
theorem B2332061 : Blo 542804 2332061 := bstep (se 3 (by rfl) ⟨437261, by rfl⟩ : syracuseStep 2332061 = 874523) B874523
theorem B1742561 : Blo 542804 1742561 := bstep (se 2 (by rfl) ⟨653460, by rfl⟩ : syracuseStep 1742561 = 1306921) B1306921
theorem B5249519 : Blo 542804 5249519 := bstep (se 1 (by rfl) ⟨3937139, by rfl⟩ : syracuseStep 5249519 = 7874279) B7874279
theorem B816716357 : Blo 542804 816716357 := bstep (se 4 (by rfl) ⟨76567158, by rfl⟩ : syracuseStep 816716357 = 153134317) B153134317
theorem B1844207 : Blo 542804 1844207 := bstep (se 1 (by rfl) ⟨1383155, by rfl⟩ : syracuseStep 1844207 = 2766311) B2766311
theorem B1225007 : Blo 542804 1225007 := bstep (se 1 (by rfl) ⟨918755, by rfl⟩ : syracuseStep 1225007 = 1837511) B1837511
theorem B3715591 : Blo 542804 3715591 := bstep (se 1 (by rfl) ⟨2786693, by rfl⟩ : syracuseStep 3715591 = 5573387) B5573387
theorem B30225707 : Blo 542804 30225707 := bstep (se 1 (by rfl) ⟨22669280, by rfl⟩ : syracuseStep 30225707 = 45338561) B45338561
theorem B3585599 : Blo 542804 3585599 := bstep (se 1 (by rfl) ⟨2689199, by rfl⟩ : syracuseStep 3585599 = 5378399) B5378399
theorem B17711419 : Blo 542804 17711419 := bstep (se 1 (by rfl) ⟨13283564, by rfl⟩ : syracuseStep 17711419 = 26567129) B26567129
theorem B163431199 : Blo 542804 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B4146551 : Blo 542804 4146551 := bstep (se 1 (by rfl) ⟨3109913, by rfl⟩ : syracuseStep 4146551 = 6219827) B6219827
theorem B8832563 : Blo 542804 8832563 := bstep (se 1 (by rfl) ⟨6624422, by rfl⟩ : syracuseStep 8832563 = 13248845) B13248845
theorem B3491531 : Blo 542804 3491531 := bstep (se 1 (by rfl) ⟨2618648, by rfl⟩ : syracuseStep 3491531 = 5237297) B5237297
theorem B542879 : Blo 542804 542879 := bstep (se 1 (by rfl) ⟨407159, by rfl⟩ : syracuseStep 542879 = 814319) B814319
theorem B1034687 : Blo 542804 1034687 := bstep (se 1 (by rfl) ⟨776015, by rfl⟩ : syracuseStep 1034687 = 1552031) B1552031
theorem B3983849 : Blo 542804 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B507791875 : Blo 542804 507791875 := bstep (se 1 (by rfl) ⟨380843906, by rfl⟩ : syracuseStep 507791875 = 761687813) B761687813
theorem B543899 : Blo 542804 543899 := bstep (se 1 (by rfl) ⟨407924, by rfl⟩ : syracuseStep 543899 = 815849) B815849
theorem B543903 : Blo 542804 543903 := bstep (se 1 (by rfl) ⟨407927, by rfl⟩ : syracuseStep 543903 = 815855) B815855
theorem B544255 : Blo 542804 544255 := bstep (se 1 (by rfl) ⟨408191, by rfl⟩ : syracuseStep 544255 = 816383) B816383
theorem B544543 : Blo 542804 544543 := bstep (se 1 (by rfl) ⟨408407, by rfl⟩ : syracuseStep 544543 = 816815) B816815
theorem B545639 : Blo 542804 545639 := bstep (se 1 (by rfl) ⟨409229, by rfl⟩ : syracuseStep 545639 = 818459) B818459
theorem B545919 : Blo 542804 545919 := bstep (se 1 (by rfl) ⟨409439, by rfl⟩ : syracuseStep 545919 = 818879) B818879
theorem B546119 : Blo 542804 546119 := bstep (se 1 (by rfl) ⟨409589, by rfl⟩ : syracuseStep 546119 = 819179) B819179
theorem B546255 : Blo 542804 546255 := bstep (se 1 (by rfl) ⟨409691, by rfl⟩ : syracuseStep 546255 = 819383) B819383
theorem B2119135 : Blo 542804 2119135 := bstep (se 1 (by rfl) ⟨1589351, by rfl⟩ : syracuseStep 2119135 = 3178703) B3178703
theorem B546671 : Blo 542804 546671 := bstep (se 1 (by rfl) ⟨410003, by rfl⟩ : syracuseStep 546671 = 820007) B820007
theorem B3496603 : Blo 542804 3496603 := bstep (se 1 (by rfl) ⟨2622452, by rfl⟩ : syracuseStep 3496603 = 5244905) B5244905
theorem B3497219 : Blo 542804 3497219 := bstep (se 1 (by rfl) ⟨2622914, by rfl⟩ : syracuseStep 3497219 = 5245829) B5245829
theorem B2318939 : Blo 542804 2318939 := bstep (se 1 (by rfl) ⟨1739204, by rfl⟩ : syracuseStep 2318939 = 3478409) B3478409
theorem B11791007 : Blo 542804 11791007 := bstep (se 1 (by rfl) ⟨8843255, by rfl⟩ : syracuseStep 11791007 = 17686511) B17686511
theorem B3501319 : Blo 542804 3501319 := bstep (se 1 (by rfl) ⟨2625989, by rfl⟩ : syracuseStep 3501319 = 5251979) B5251979
theorem B13233743 : Blo 542804 13233743 := bstep (se 1 (by rfl) ⟨9925307, by rfl⟩ : syracuseStep 13233743 = 19850615) B19850615
theorem B814823 : Blo 542804 814823 := bstep (se 1 (by rfl) ⟨611117, by rfl⟩ : syracuseStep 814823 = 1222235) B1222235
theorem B25194377 : Blo 542804 25194377 := bstep (se 2 (by rfl) ⟨9447891, by rfl⟩ : syracuseStep 25194377 = 18895783) B18895783
theorem B27684755 : Blo 542804 27684755 := bstep (se 1 (by rfl) ⟨20763566, by rfl⟩ : syracuseStep 27684755 = 41527133) B41527133
theorem B815039 : Blo 542804 815039 := bstep (se 1 (by rfl) ⟨611279, by rfl⟩ : syracuseStep 815039 = 1222559) B1222559
theorem B815207 : Blo 542804 815207 := bstep (se 1 (by rfl) ⟨611405, by rfl⟩ : syracuseStep 815207 = 1222811) B1222811
theorem B1962143 : Blo 542804 1962143 := bstep (se 1 (by rfl) ⟨1471607, by rfl⟩ : syracuseStep 1962143 = 2943215) B2943215
theorem B1962863 : Blo 542804 1962863 := bstep (se 1 (by rfl) ⟨1472147, by rfl⟩ : syracuseStep 1962863 = 2944295) B2944295
theorem B816095 : Blo 542804 816095 := bstep (se 1 (by rfl) ⟨612071, by rfl⟩ : syracuseStep 816095 = 1224143) B1224143
theorem B21198523 : Blo 542804 21198523 := bstep (se 1 (by rfl) ⟨15898892, by rfl⟩ : syracuseStep 21198523 = 31797785) B31797785
theorem B3930281 : Blo 542804 3930281 := bstep (se 2 (by rfl) ⟨1473855, by rfl⟩ : syracuseStep 3930281 = 2947711) B2947711
theorem B818171 : Blo 542804 818171 := bstep (se 1 (by rfl) ⟨613628, by rfl⟩ : syracuseStep 818171 = 1227257) B1227257
theorem B818351 : Blo 542804 818351 := bstep (se 1 (by rfl) ⟨613763, by rfl⟩ : syracuseStep 818351 = 1227527) B1227527
theorem B917095 : Blo 542804 917095 := bstep (se 1 (by rfl) ⟨687821, by rfl⟩ : syracuseStep 917095 = 1375643) B1375643
theorem B818927 : Blo 542804 818927 := bstep (se 1 (by rfl) ⟨614195, by rfl⟩ : syracuseStep 818927 = 1228391) B1228391
theorem B6225659 : Blo 542804 6225659 := bstep (se 1 (by rfl) ⟨4669244, by rfl⟩ : syracuseStep 6225659 = 9338489) B9338489
theorem B1376423 : Blo 542804 1376423 := bstep (se 1 (by rfl) ⟨1032317, by rfl⟩ : syracuseStep 1376423 = 2064635) B2064635
theorem B21168587 : Blo 542804 21168587 := bstep (se 1 (by rfl) ⟨15876440, by rfl⟩ : syracuseStep 21168587 = 31752881) B31752881
theorem B1377263 : Blo 542804 1377263 := bstep (se 1 (by rfl) ⟨1032947, by rfl⟩ : syracuseStep 1377263 = 2065895) B2065895
theorem B217908265 : Blo 542804 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B2327687 : Blo 542804 2327687 := bstep (se 1 (by rfl) ⟨1745765, by rfl⟩ : syracuseStep 2327687 = 3491531) B3491531
theorem B1377719 : Blo 542804 1377719 := bstep (se 1 (by rfl) ⟨1033289, by rfl⟩ : syracuseStep 1377719 = 2066579) B2066579
theorem B689791 : Blo 542804 689791 := bstep (se 1 (by rfl) ⟨517343, by rfl⟩ : syracuseStep 689791 = 1034687) B1034687
theorem B2655899 : Blo 542804 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B9963485 : Blo 542804 9963485 := bstep (se 3 (by rfl) ⟨1868153, by rfl⟩ : syracuseStep 9963485 = 3736307) B3736307
theorem B1378367 : Blo 542804 1378367 := bstep (se 1 (by rfl) ⟨1033775, by rfl⟩ : syracuseStep 1378367 = 2067551) B2067551
theorem B1968455 : Blo 542804 1968455 := bstep (se 1 (by rfl) ⟨1476341, by rfl⟩ : syracuseStep 1968455 = 2952683) B2952683
theorem B3541403 : Blo 542804 3541403 := bstep (se 1 (by rfl) ⟨2656052, by rfl⟩ : syracuseStep 3541403 = 5312105) B5312105
theorem B2624491 : Blo 542804 2624491 := bstep (se 1 (by rfl) ⟨1968368, by rfl⟩ : syracuseStep 2624491 = 3936737) B3936737
theorem B677055833 : Blo 542804 677055833 := bstep (se 2 (by rfl) ⟨253895937, by rfl⟩ : syracuseStep 677055833 = 507791875) B507791875
theorem B44633663 : Blo 542804 44633663 := bstep (se 1 (by rfl) ⟨33475247, by rfl⟩ : syracuseStep 44633663 = 66950495) B66950495
theorem B544477571 : Blo 542804 544477571 := bstep (se 1 (by rfl) ⟨408358178, by rfl⟩ : syracuseStep 544477571 = 816716357) B816716357
theorem B2331479 : Blo 542804 2331479 := bstep (se 1 (by rfl) ⟨1748609, by rfl⟩ : syracuseStep 2331479 = 3497219) B3497219
theorem B1545959 : Blo 542804 1545959 := bstep (se 1 (by rfl) ⟨1159469, by rfl⟩ : syracuseStep 1545959 = 2318939) B2318939
theorem B4954121 : Blo 542804 4954121 := bstep (se 2 (by rfl) ⟨1857795, by rfl⟩ : syracuseStep 4954121 = 3715591) B3715591
theorem B2825513 : Blo 542804 2825513 := bstep (se 2 (by rfl) ⟨1059567, by rfl⟩ : syracuseStep 2825513 = 2119135) B2119135
theorem B8822495 : Blo 542804 8822495 := bstep (se 1 (by rfl) ⟨6616871, by rfl⟩ : syracuseStep 8822495 = 13233743) B13233743
theorem B18456503 : Blo 542804 18456503 := bstep (se 1 (by rfl) ⟨13842377, by rfl⟩ : syracuseStep 18456503 = 27684755) B27684755
theorem B4662137 : Blo 542804 4662137 := bstep (se 2 (by rfl) ⟨1748301, by rfl⟩ : syracuseStep 4662137 = 3496603) B3496603
theorem B1222793 : Blo 542804 1222793 := bstep (se 2 (by rfl) ⟨458547, by rfl⟩ : syracuseStep 1222793 = 917095) B917095
theorem B1223387 : Blo 542804 1223387 := bstep (se 1 (by rfl) ⟨917540, by rfl⟩ : syracuseStep 1223387 = 1835081) B1835081
theorem B1223495 : Blo 542804 1223495 := bstep (se 1 (by rfl) ⟨917621, by rfl⟩ : syracuseStep 1223495 = 1835243) B1835243
theorem B1224107 : Blo 542804 1224107 := bstep (se 1 (by rfl) ⟨918080, by rfl⟩ : syracuseStep 1224107 = 1836161) B1836161
theorem B2764367 : Blo 542804 2764367 := bstep (se 1 (by rfl) ⟨2073275, by rfl⟩ : syracuseStep 2764367 = 4146551) B4146551
theorem B21213479 : Blo 542804 21213479 := bstep (se 1 (by rfl) ⟨15910109, by rfl⟩ : syracuseStep 21213479 = 31820219) B31820219
theorem B1225043 : Blo 542804 1225043 := bstep (se 1 (by rfl) ⟨918782, by rfl⟩ : syracuseStep 1225043 = 1837565) B1837565
theorem B1226087 : Blo 542804 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B1554707 : Blo 542804 1554707 := bstep (se 1 (by rfl) ⟨1166030, by rfl⟩ : syracuseStep 1554707 = 2332061) B2332061
theorem B1161707 : Blo 542804 1161707 := bstep (se 1 (by rfl) ⟨871280, by rfl⟩ : syracuseStep 1161707 = 1742561) B1742561
theorem B4668425 : Blo 542804 4668425 := bstep (se 2 (by rfl) ⟨1750659, by rfl⟩ : syracuseStep 4668425 = 3501319) B3501319
theorem B1229471 : Blo 542804 1229471 := bstep (se 1 (by rfl) ⟨922103, by rfl⟩ : syracuseStep 1229471 = 1844207) B1844207
theorem B28264697 : Blo 542804 28264697 := bstep (se 2 (by rfl) ⟨10599261, by rfl⟩ : syracuseStep 28264697 = 21198523) B21198523
theorem B543215 : Blo 542804 543215 := bstep (se 1 (by rfl) ⟨407411, by rfl⟩ : syracuseStep 543215 = 814823) B814823
theorem B16796251 : Blo 542804 16796251 := bstep (se 1 (by rfl) ⟨12597188, by rfl⟩ : syracuseStep 16796251 = 25194377) B25194377
theorem B543359 : Blo 542804 543359 := bstep (se 1 (by rfl) ⟨407519, by rfl⟩ : syracuseStep 543359 = 815039) B815039
theorem B543471 : Blo 542804 543471 := bstep (se 1 (by rfl) ⟨407603, by rfl⟩ : syracuseStep 543471 = 815207) B815207
theorem B544063 : Blo 542804 544063 := bstep (se 1 (by rfl) ⟨408047, by rfl⟩ : syracuseStep 544063 = 816095) B816095
theorem B545447 : Blo 542804 545447 := bstep (se 1 (by rfl) ⟨409085, by rfl⟩ : syracuseStep 545447 = 818171) B818171
theorem B545567 : Blo 542804 545567 := bstep (se 1 (by rfl) ⟨409175, by rfl⟩ : syracuseStep 545567 = 818351) B818351
theorem B545951 : Blo 542804 545951 := bstep (se 1 (by rfl) ⟨409463, by rfl⟩ : syracuseStep 545951 = 818927) B818927
theorem B4150439 : Blo 542804 4150439 := bstep (se 1 (by rfl) ⟨3112829, by rfl⟩ : syracuseStep 4150439 = 6225659) B6225659
theorem B23615225 : Blo 542804 23615225 := bstep (se 2 (by rfl) ⟨8855709, by rfl⟩ : syracuseStep 23615225 = 17711419) B17711419
theorem B546587 : Blo 542804 546587 := bstep (se 1 (by rfl) ⟨409940, by rfl⟩ : syracuseStep 546587 = 819881) B819881
theorem B5888375 : Blo 542804 5888375 := bstep (se 1 (by rfl) ⟨4416281, by rfl⟩ : syracuseStep 5888375 = 8832563) B8832563
theorem B613543 : Blo 542804 613543 := bstep (se 1 (by rfl) ⟨460157, by rfl⟩ : syracuseStep 613543 = 920315) B920315
theorem B3499679 : Blo 542804 3499679 := bstep (se 1 (by rfl) ⟨2624759, by rfl⟩ : syracuseStep 3499679 = 5249519) B5249519
theorem B3108617 : Blo 542804 3108617 := bstep (se 2 (by rfl) ⟨1165731, by rfl⟩ : syracuseStep 3108617 = 2331463) B2331463
theorem B7860671 : Blo 542804 7860671 := bstep (se 1 (by rfl) ⟨5895503, by rfl⟩ : syracuseStep 7860671 = 11791007) B11791007
theorem B1308095 : Blo 542804 1308095 := bstep (se 1 (by rfl) ⟨981071, by rfl⟩ : syracuseStep 1308095 = 1962143) B1962143
theorem B816671 : Blo 542804 816671 := bstep (se 1 (by rfl) ⟨612503, by rfl⟩ : syracuseStep 816671 = 1225007) B1225007
theorem B1308575 : Blo 542804 1308575 := bstep (se 1 (by rfl) ⟨981431, by rfl⟩ : syracuseStep 1308575 = 1962863) B1962863
theorem B20150471 : Blo 542804 20150471 := bstep (se 1 (by rfl) ⟨15112853, by rfl⟩ : syracuseStep 20150471 = 30225707) B30225707
theorem B2390399 : Blo 542804 2390399 := bstep (se 1 (by rfl) ⟨1792799, by rfl⟩ : syracuseStep 2390399 = 3585599) B3585599
theorem B2620187 : Blo 542804 2620187 := bstep (se 1 (by rfl) ⟨1965140, by rfl⟩ : syracuseStep 2620187 = 3930281) B3930281
theorem B917615 : Blo 542804 917615 := bstep (se 1 (by rfl) ⟨688211, by rfl⟩ : syracuseStep 917615 = 1376423) B1376423
theorem B819647 : Blo 542804 819647 := bstep (se 1 (by rfl) ⟨614735, by rfl⟩ : syracuseStep 819647 = 1229471) B1229471
theorem B918175 : Blo 542804 918175 := bstep (se 1 (by rfl) ⟨688631, by rfl⟩ : syracuseStep 918175 = 1377263) B1377263
theorem B918479 : Blo 542804 918479 := bstep (se 1 (by rfl) ⟨688859, by rfl⟩ : syracuseStep 918479 = 1377719) B1377719
theorem B1770599 : Blo 542804 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B918911 : Blo 542804 918911 := bstep (se 1 (by rfl) ⟨689183, by rfl⟩ : syracuseStep 918911 = 1378367) B1378367
theorem B18843131 : Blo 542804 18843131 := bstep (se 1 (by rfl) ⟨14132348, by rfl⟩ : syracuseStep 18843131 = 28264697) B28264697
theorem B1312303 : Blo 542804 1312303 := bstep (se 1 (by rfl) ⟨984227, by rfl⟩ : syracuseStep 1312303 = 1968455) B1968455
theorem B2360935 : Blo 542804 2360935 := bstep (se 1 (by rfl) ⟨1770701, by rfl⟩ : syracuseStep 2360935 = 3541403) B3541403
theorem B919721 : Blo 542804 919721 := bstep (se 2 (by rfl) ⟨344895, by rfl⟩ : syracuseStep 919721 = 689791) B689791
theorem B29755775 : Blo 542804 29755775 := bstep (se 1 (by rfl) ⟨22316831, by rfl⟩ : syracuseStep 29755775 = 44633663) B44633663
theorem B2333119 : Blo 542804 2333119 := bstep (se 1 (by rfl) ⟨1749839, by rfl⟩ : syracuseStep 2333119 = 3499679) B3499679
theorem B1842911 : Blo 542804 1842911 := bstep (se 1 (by rfl) ⟨1382183, by rfl⟩ : syracuseStep 1842911 = 2764367) B2764367
theorem B2072411 : Blo 542804 2072411 := bstep (se 1 (by rfl) ⟨1554308, by rfl⟩ : syracuseStep 2072411 = 3108617) B3108617
theorem B1746791 : Blo 542804 1746791 := bstep (se 1 (by rfl) ⟨1310093, by rfl⟩ : syracuseStep 1746791 = 2620187) B2620187
theorem B1551791 : Blo 542804 1551791 := bstep (se 1 (by rfl) ⟨1163843, by rfl⟩ : syracuseStep 1551791 = 2327687) B2327687
theorem B362985047 : Blo 542804 362985047 := bstep (se 1 (by rfl) ⟨272238785, by rfl⟩ : syracuseStep 362985047 = 544477571) B544477571
theorem B1554319 : Blo 542804 1554319 := bstep (se 1 (by rfl) ⟨1165739, by rfl⟩ : syracuseStep 1554319 = 2331479) B2331479
theorem B2766959 : Blo 542804 2766959 := bstep (se 1 (by rfl) ⟨2075219, by rfl⟩ : syracuseStep 2766959 = 4150439) B4150439
theorem B22395001 : Blo 542804 22395001 := bstep (se 2 (by rfl) ⟨8398125, by rfl⟩ : syracuseStep 22395001 = 16796251) B16796251
theorem B1030639 : Blo 542804 1030639 := bstep (se 1 (by rfl) ⟨772979, by rfl⟩ : syracuseStep 1030639 = 1545959) B1545959
theorem B15743483 : Blo 542804 15743483 := bstep (se 1 (by rfl) ⟨11807612, by rfl⟩ : syracuseStep 15743483 = 23615225) B23615225
theorem B1883675 : Blo 542804 1883675 := bstep (se 1 (by rfl) ⟨1412756, by rfl⟩ : syracuseStep 1883675 = 2825513) B2825513
theorem B5881663 : Blo 542804 5881663 := bstep (se 1 (by rfl) ⟨4411247, by rfl⟩ : syracuseStep 5881663 = 8822495) B8822495
theorem B3097885 : Blo 542804 3097885 := bstep (se 3 (by rfl) ⟨580853, by rfl⟩ : syracuseStep 3097885 = 1161707) B1161707
theorem B14142319 : Blo 542804 14142319 := bstep (se 1 (by rfl) ⟨10606739, by rfl⟩ : syracuseStep 14142319 = 21213479) B21213479
theorem B872063 : Blo 542804 872063 := bstep (se 1 (by rfl) ⟨654047, by rfl⟩ : syracuseStep 872063 = 1308095) B1308095
theorem B544447 : Blo 542804 544447 := bstep (se 1 (by rfl) ⟨408335, by rfl⟩ : syracuseStep 544447 = 816671) B816671
theorem B872383 : Blo 542804 872383 := bstep (se 1 (by rfl) ⟨654287, by rfl⟩ : syracuseStep 872383 = 1308575) B1308575
theorem B1036471 : Blo 542804 1036471 := bstep (se 1 (by rfl) ⟨777353, by rfl⟩ : syracuseStep 1036471 = 1554707) B1554707
theorem B1593599 : Blo 542804 1593599 := bstep (se 1 (by rfl) ⟨1195199, by rfl⟩ : syracuseStep 1593599 = 2390399) B2390399
theorem B14112391 : Blo 542804 14112391 := bstep (se 1 (by rfl) ⟨10584293, by rfl⟩ : syracuseStep 14112391 = 21168587) B21168587
theorem B6642323 : Blo 542804 6642323 := bstep (se 1 (by rfl) ⟨4981742, by rfl⟩ : syracuseStep 6642323 = 9963485) B9963485
theorem B290544353 : Blo 542804 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B451370555 : Blo 542804 451370555 := bstep (se 1 (by rfl) ⟨338527916, by rfl⟩ : syracuseStep 451370555 = 677055833) B677055833
theorem B3499321 : Blo 542804 3499321 := bstep (se 2 (by rfl) ⟨1312245, by rfl⟩ : syracuseStep 3499321 = 2624491) B2624491
theorem B3302747 : Blo 542804 3302747 := bstep (se 1 (by rfl) ⟨2477060, by rfl⟩ : syracuseStep 3302747 = 4954121) B4954121
theorem B3925583 : Blo 542804 3925583 := bstep (se 1 (by rfl) ⟨2944187, by rfl⟩ : syracuseStep 3925583 = 5888375) B5888375
theorem B3108091 : Blo 542804 3108091 := bstep (se 1 (by rfl) ⟨2331068, by rfl⟩ : syracuseStep 3108091 = 4662137) B4662137
theorem B815195 : Blo 542804 815195 := bstep (se 1 (by rfl) ⟨611396, by rfl⟩ : syracuseStep 815195 = 1222793) B1222793
theorem B815591 : Blo 542804 815591 := bstep (se 1 (by rfl) ⟨611693, by rfl⟩ : syracuseStep 815591 = 1223387) B1223387
theorem B815663 : Blo 542804 815663 := bstep (se 1 (by rfl) ⟨611747, by rfl⟩ : syracuseStep 815663 = 1223495) B1223495
theorem B816071 : Blo 542804 816071 := bstep (se 1 (by rfl) ⟨612053, by rfl⟩ : syracuseStep 816071 = 1224107) B1224107
theorem B816695 : Blo 542804 816695 := bstep (se 1 (by rfl) ⟨612521, by rfl⟩ : syracuseStep 816695 = 1225043) B1225043
theorem B5240447 : Blo 542804 5240447 := bstep (se 1 (by rfl) ⟨3930335, by rfl⟩ : syracuseStep 5240447 = 7860671) B7860671
theorem B817391 : Blo 542804 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B13433647 : Blo 542804 13433647 := bstep (se 1 (by rfl) ⟨10075235, by rfl⟩ : syracuseStep 13433647 = 20150471) B20150471
theorem B818057 : Blo 542804 818057 := bstep (se 2 (by rfl) ⟨306771, by rfl⟩ : syracuseStep 818057 = 613543) B613543
theorem B3112283 : Blo 542804 3112283 := bstep (se 1 (by rfl) ⟨2334212, by rfl⟩ : syracuseStep 3112283 = 4668425) B4668425
theorem B49217341 : Blo 542804 49217341 := bstep (se 3 (by rfl) ⟨9228251, by rfl⟩ : syracuseStep 49217341 = 18456503) B18456503
theorem B4130513 : Blo 542804 4130513 := bstep (se 2 (by rfl) ⟨1548942, by rfl⟩ : syracuseStep 4130513 = 3097885) B3097885
theorem B3147913 : Blo 542804 3147913 := bstep (se 2 (by rfl) ⟨1180467, by rfl⟩ : syracuseStep 3147913 = 2360935) B2360935
theorem B4721597 : Blo 542804 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B4428215 : Blo 542804 4428215 := bstep (se 1 (by rfl) ⟨3321161, by rfl⟩ : syracuseStep 4428215 = 6642323) B6642323
theorem B193696235 : Blo 542804 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B300913703 : Blo 542804 300913703 := bstep (se 1 (by rfl) ⟨225685277, by rfl⟩ : syracuseStep 300913703 = 451370555) B451370555
theorem B1381607 : Blo 542804 1381607 := bstep (se 1 (by rfl) ⟨1036205, by rfl⟩ : syracuseStep 1381607 = 2072411) B2072411
theorem B1381961 : Blo 542804 1381961 := bstep (se 2 (by rfl) ⟨518235, by rfl⟩ : syracuseStep 1381961 = 1036471) B1036471
theorem B2201831 : Blo 542804 2201831 := bstep (se 1 (by rfl) ⟨1651373, by rfl⟩ : syracuseStep 2201831 = 3302747) B3302747
theorem B18816521 : Blo 542804 18816521 := bstep (se 2 (by rfl) ⟨7056195, by rfl⟩ : syracuseStep 18816521 = 14112391) B14112391
theorem B2072425 : Blo 542804 2072425 := bstep (se 2 (by rfl) ⟨777159, by rfl⟩ : syracuseStep 2072425 = 1554319) B1554319
theorem B29860001 : Blo 542804 29860001 := bstep (se 2 (by rfl) ⟨11197500, by rfl⟩ : syracuseStep 29860001 = 22395001) B22395001
theorem B1844639 : Blo 542804 1844639 := bstep (se 1 (by rfl) ⟨1383479, by rfl⟩ : syracuseStep 1844639 = 2766959) B2766959
theorem B10495655 : Blo 542804 10495655 := bstep (se 1 (by rfl) ⟨7871741, by rfl⟩ : syracuseStep 10495655 = 15743483) B15743483
theorem B2074855 : Blo 542804 2074855 := bstep (se 1 (by rfl) ⟨1556141, by rfl⟩ : syracuseStep 2074855 = 3112283) B3112283
theorem B1255783 : Blo 542804 1255783 := bstep (se 1 (by rfl) ⟨941837, by rfl⟩ : syracuseStep 1255783 = 1883675) B1883675
theorem B7842217 : Blo 542804 7842217 := bstep (se 2 (by rfl) ⟨2940831, by rfl⟩ : syracuseStep 7842217 = 5881663) B5881663
theorem B1224233 : Blo 542804 1224233 := bstep (se 2 (by rfl) ⟨459087, by rfl⟩ : syracuseStep 1224233 = 918175) B918175
theorem B12562087 : Blo 542804 12562087 := bstep (se 1 (by rfl) ⟨9421565, by rfl⟩ : syracuseStep 12562087 = 18843131) B18843131
theorem B19837183 : Blo 542804 19837183 := bstep (se 1 (by rfl) ⟨14877887, by rfl⟩ : syracuseStep 19837183 = 29755775) B29755775
theorem B4665761 : Blo 542804 4665761 := bstep (se 2 (by rfl) ⟨1749660, by rfl⟩ : syracuseStep 4665761 = 3499321) B3499321
theorem B1749737 : Blo 542804 1749737 := bstep (se 2 (by rfl) ⟨656151, by rfl⟩ : syracuseStep 1749737 = 1312303) B1312303
theorem B4144121 : Blo 542804 4144121 := bstep (se 2 (by rfl) ⟨1554045, by rfl⟩ : syracuseStep 4144121 = 3108091) B3108091
theorem B1228607 : Blo 542804 1228607 := bstep (se 1 (by rfl) ⟨921455, by rfl⟩ : syracuseStep 1228607 = 1842911) B1842911
theorem B1163177 : Blo 542804 1163177 := bstep (se 2 (by rfl) ⟨436191, by rfl⟩ : syracuseStep 1163177 = 872383) B872383
theorem B1164527 : Blo 542804 1164527 := bstep (se 1 (by rfl) ⟨873395, by rfl⟩ : syracuseStep 1164527 = 1746791) B1746791
theorem B1034527 : Blo 542804 1034527 := bstep (se 1 (by rfl) ⟨775895, by rfl⟩ : syracuseStep 1034527 = 1551791) B1551791
theorem B543463 : Blo 542804 543463 := bstep (se 1 (by rfl) ⟨407597, by rfl⟩ : syracuseStep 543463 = 815195) B815195
theorem B543727 : Blo 542804 543727 := bstep (se 1 (by rfl) ⟨407795, by rfl⟩ : syracuseStep 543727 = 815591) B815591
theorem B543775 : Blo 542804 543775 := bstep (se 1 (by rfl) ⟨407831, by rfl⟩ : syracuseStep 543775 = 815663) B815663
theorem B544047 : Blo 542804 544047 := bstep (se 1 (by rfl) ⟨408035, by rfl⟩ : syracuseStep 544047 = 816071) B816071
theorem B544463 : Blo 542804 544463 := bstep (se 1 (by rfl) ⟨408347, by rfl⟩ : syracuseStep 544463 = 816695) B816695
theorem B17911529 : Blo 542804 17911529 := bstep (se 2 (by rfl) ⟨6716823, by rfl⟩ : syracuseStep 17911529 = 13433647) B13433647
theorem B3493631 : Blo 542804 3493631 := bstep (se 1 (by rfl) ⟨2620223, by rfl⟩ : syracuseStep 3493631 = 5240447) B5240447
theorem B544927 : Blo 542804 544927 := bstep (se 1 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 544927 = 817391) B817391
theorem B545371 : Blo 542804 545371 := bstep (se 1 (by rfl) ⟨409028, by rfl⟩ : syracuseStep 545371 = 818057) B818057
theorem B65623121 : Blo 542804 65623121 := bstep (se 2 (by rfl) ⟨24608670, by rfl⟩ : syracuseStep 65623121 = 49217341) B49217341
theorem B611743 : Blo 542804 611743 := bstep (se 1 (by rfl) ⟨458807, by rfl⟩ : syracuseStep 611743 = 917615) B917615
theorem B546431 : Blo 542804 546431 := bstep (se 1 (by rfl) ⟨409823, by rfl⟩ : syracuseStep 546431 = 819647) B819647
theorem B612319 : Blo 542804 612319 := bstep (se 1 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 612319 = 918479) B918479
theorem B4249597 : Blo 542804 4249597 := bstep (se 3 (by rfl) ⟨796799, by rfl⟩ : syracuseStep 4249597 = 1593599) B1593599
theorem B612607 : Blo 542804 612607 := bstep (se 1 (by rfl) ⟨459455, by rfl⟩ : syracuseStep 612607 = 918911) B918911
theorem B613147 : Blo 542804 613147 := bstep (se 1 (by rfl) ⟨459860, by rfl⟩ : syracuseStep 613147 = 919721) B919721
theorem B581375 : Blo 542804 581375 := bstep (se 1 (by rfl) ⟨436031, by rfl⟩ : syracuseStep 581375 = 872063) B872063
theorem B75425701 : Blo 542804 75425701 := bstep (se 4 (by rfl) ⟨7071159, by rfl⟩ : syracuseStep 75425701 = 14142319) B14142319
theorem B2617055 : Blo 542804 2617055 := bstep (se 1 (by rfl) ⟨1962791, by rfl⟩ : syracuseStep 2617055 = 3925583) B3925583
theorem B3110825 : Blo 542804 3110825 := bstep (se 2 (by rfl) ⟨1166559, by rfl⟩ : syracuseStep 3110825 = 2333119) B2333119
theorem B1374185 : Blo 542804 1374185 := bstep (se 2 (by rfl) ⟨515319, by rfl⟩ : syracuseStep 1374185 = 1030639) B1030639
theorem B241990031 : Blo 542804 241990031 := bstep (se 1 (by rfl) ⟨181492523, by rfl⟩ : syracuseStep 241990031 = 362985047) B362985047
theorem B2753675 : Blo 542804 2753675 := bstep (se 1 (by rfl) ⟨2065256, by rfl⟩ : syracuseStep 2753675 = 4130513) B4130513
theorem B3147731 : Blo 542804 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B2329087 : Blo 542804 2329087 := bstep (se 1 (by rfl) ⟨1746815, by rfl⟩ : syracuseStep 2329087 = 3493631) B3493631
theorem B100567601 : Blo 542804 100567601 := bstep (se 2 (by rfl) ⟨37712850, by rfl⟩ : syracuseStep 100567601 = 75425701) B75425701
theorem B4197217 : Blo 542804 4197217 := bstep (se 2 (by rfl) ⟨1573956, by rfl⟩ : syracuseStep 4197217 = 3147913) B3147913
theorem B2952143 : Blo 542804 2952143 := bstep (se 1 (by rfl) ⟨2214107, by rfl⟩ : syracuseStep 2952143 = 4428215) B4428215
theorem B1379369 : Blo 542804 1379369 := bstep (se 2 (by rfl) ⟨517263, by rfl⟩ : syracuseStep 1379369 = 1034527) B1034527
theorem B1674377 : Blo 542804 1674377 := bstep (se 2 (by rfl) ⟨627891, by rfl⟩ : syracuseStep 1674377 = 1255783) B1255783
theorem B10456289 : Blo 542804 10456289 := bstep (se 2 (by rfl) ⟨3921108, by rfl⟩ : syracuseStep 10456289 = 7842217) B7842217
theorem B200609135 : Blo 542804 200609135 := bstep (se 1 (by rfl) ⟨150456851, by rfl⟩ : syracuseStep 200609135 = 300913703) B300913703
theorem B43748747 : Blo 542804 43748747 := bstep (se 1 (by rfl) ⟨32811560, by rfl⟩ : syracuseStep 43748747 = 65623121) B65623121
theorem B921071 : Blo 542804 921071 := bstep (se 1 (by rfl) ⟨690803, by rfl⟩ : syracuseStep 921071 = 1381607) B1381607
theorem B921307 : Blo 542804 921307 := bstep (se 1 (by rfl) ⟨690980, by rfl⟩ : syracuseStep 921307 = 1381961) B1381961
theorem B16749449 : Blo 542804 16749449 := bstep (se 2 (by rfl) ⟨6281043, by rfl⟩ : syracuseStep 16749449 = 12562087) B12562087
theorem B26449577 : Blo 542804 26449577 := bstep (se 2 (by rfl) ⟨9918591, by rfl⟩ : syracuseStep 26449577 = 19837183) B19837183
theorem B1744703 : Blo 542804 1744703 := bstep (se 1 (by rfl) ⟨1308527, by rfl⟩ : syracuseStep 1744703 = 2617055) B2617055
theorem B2073883 : Blo 542804 2073883 := bstep (se 1 (by rfl) ⟨1555412, by rfl⟩ : syracuseStep 2073883 = 3110825) B3110825
theorem B50177389 : Blo 542804 50177389 := bstep (se 3 (by rfl) ⟨9408260, by rfl⟩ : syracuseStep 50177389 = 18816521) B18816521
theorem B161326687 : Blo 542804 161326687 := bstep (se 1 (by rfl) ⟨120995015, by rfl⟩ : syracuseStep 161326687 = 241990031) B241990031
theorem B2762747 : Blo 542804 2762747 := bstep (se 1 (by rfl) ⟨2072060, by rfl⟩ : syracuseStep 2762747 = 4144121) B4144121
theorem B1550333 : Blo 542804 1550333 := bstep (se 3 (by rfl) ⟨290687, by rfl⟩ : syracuseStep 1550333 = 581375) B581375
theorem B2763233 : Blo 542804 2763233 := bstep (se 2 (by rfl) ⟨1036212, by rfl⟩ : syracuseStep 2763233 = 2072425) B2072425
theorem B11941019 : Blo 542804 11941019 := bstep (se 1 (by rfl) ⟨8955764, by rfl⟩ : syracuseStep 11941019 = 17911529) B17911529
theorem B2766473 : Blo 542804 2766473 := bstep (se 2 (by rfl) ⟨1037427, by rfl⟩ : syracuseStep 2766473 = 2074855) B2074855
theorem B19906667 : Blo 542804 19906667 := bstep (se 1 (by rfl) ⟨14930000, by rfl⟩ : syracuseStep 19906667 = 29860001) B29860001
theorem B1229759 : Blo 542804 1229759 := bstep (se 1 (by rfl) ⟨922319, by rfl⟩ : syracuseStep 1229759 = 1844639) B1844639
theorem B6997103 : Blo 542804 6997103 := bstep (se 1 (by rfl) ⟨5247827, by rfl⟩ : syracuseStep 6997103 = 10495655) B10495655
theorem B1166491 : Blo 542804 1166491 := bstep (se 1 (by rfl) ⟨874868, by rfl⟩ : syracuseStep 1166491 = 1749737) B1749737
theorem B775451 : Blo 542804 775451 := bstep (se 1 (by rfl) ⟨581588, by rfl⟩ : syracuseStep 775451 = 1163177) B1163177
theorem B776351 : Blo 542804 776351 := bstep (se 1 (by rfl) ⟨582263, by rfl⟩ : syracuseStep 776351 = 1164527) B1164527
theorem B129130823 : Blo 542804 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B1467887 : Blo 542804 1467887 := bstep (se 1 (by rfl) ⟨1100915, by rfl⟩ : syracuseStep 1467887 = 2201831) B2201831
theorem B815657 : Blo 542804 815657 := bstep (se 2 (by rfl) ⟨305871, by rfl⟩ : syracuseStep 815657 = 611743) B611743
theorem B816155 : Blo 542804 816155 := bstep (se 1 (by rfl) ⟨612116, by rfl⟩ : syracuseStep 816155 = 1224233) B1224233
theorem B816425 : Blo 542804 816425 := bstep (se 2 (by rfl) ⟨306159, by rfl⟩ : syracuseStep 816425 = 612319) B612319
theorem B5666129 : Blo 542804 5666129 := bstep (se 2 (by rfl) ⟨2124798, by rfl⟩ : syracuseStep 5666129 = 4249597) B4249597
theorem B3110507 : Blo 542804 3110507 := bstep (se 1 (by rfl) ⟨2332880, by rfl⟩ : syracuseStep 3110507 = 4665761) B4665761
theorem B816809 : Blo 542804 816809 := bstep (se 2 (by rfl) ⟨306303, by rfl⟩ : syracuseStep 816809 = 612607) B612607
theorem B817529 : Blo 542804 817529 := bstep (se 2 (by rfl) ⟨306573, by rfl⟩ : syracuseStep 817529 = 613147) B613147
theorem B916123 : Blo 542804 916123 := bstep (se 1 (by rfl) ⟨687092, by rfl⟩ : syracuseStep 916123 = 1374185) B1374185
theorem B819071 : Blo 542804 819071 := bstep (se 1 (by rfl) ⟨614303, by rfl⟩ : syracuseStep 819071 = 1228607) B1228607
theorem B13271111 : Blo 542804 13271111 := bstep (se 1 (by rfl) ⟨9953333, by rfl⟩ : syracuseStep 13271111 = 19906667) B19906667
theorem B819839 : Blo 542804 819839 := bstep (se 1 (by rfl) ⟨614879, by rfl⟩ : syracuseStep 819839 = 1229759) B1229759
theorem B1835783 : Blo 542804 1835783 := bstep (se 1 (by rfl) ⟨1376837, by rfl⟩ : syracuseStep 1835783 = 2753675) B2753675
theorem B2098487 : Blo 542804 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B67045067 : Blo 542804 67045067 := bstep (se 1 (by rfl) ⟨50283800, by rfl⟩ : syracuseStep 67045067 = 100567601) B100567601
theorem B1968095 : Blo 542804 1968095 := bstep (se 1 (by rfl) ⟨1476071, by rfl⟩ : syracuseStep 1968095 = 2952143) B2952143
theorem B919579 : Blo 542804 919579 := bstep (se 1 (by rfl) ⟨689684, by rfl⟩ : syracuseStep 919579 = 1379369) B1379369
theorem B1116251 : Blo 542804 1116251 := bstep (se 1 (by rfl) ⟨837188, by rfl⟩ : syracuseStep 1116251 = 1674377) B1674377
theorem B29165831 : Blo 542804 29165831 := bstep (se 1 (by rfl) ⟨21874373, by rfl⟩ : syracuseStep 29165831 = 43748747) B43748747
theorem B2067869 : Blo 542804 2067869 := bstep (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) B775451
theorem B17633051 : Blo 542804 17633051 := bstep (se 1 (by rfl) ⟨13224788, by rfl⟩ : syracuseStep 17633051 = 26449577) B26449577
theorem B86087215 : Blo 542804 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B2070269 : Blo 542804 2070269 := bstep (se 3 (by rfl) ⟨388175, by rfl⟩ : syracuseStep 2070269 = 776351) B776351
theorem B1841831 : Blo 542804 1841831 := bstep (se 1 (by rfl) ⟨1381373, by rfl⟩ : syracuseStep 1841831 = 2762747) B2762747
theorem B1842155 : Blo 542804 1842155 := bstep (se 1 (by rfl) ⟨1381616, by rfl⟩ : syracuseStep 1842155 = 2763233) B2763233
theorem B1221497 : Blo 542804 1221497 := bstep (se 2 (by rfl) ⟨458061, by rfl⟩ : syracuseStep 1221497 = 916123) B916123
theorem B3777419 : Blo 542804 3777419 := bstep (se 1 (by rfl) ⟨2833064, by rfl⟩ : syracuseStep 3777419 = 5666129) B5666129
theorem B2073671 : Blo 542804 2073671 := bstep (se 1 (by rfl) ⟨1555253, by rfl⟩ : syracuseStep 2073671 = 3110507) B3110507
theorem B1844315 : Blo 542804 1844315 := bstep (se 1 (by rfl) ⟨1383236, by rfl⟩ : syracuseStep 1844315 = 2766473) B2766473
theorem B4664735 : Blo 542804 4664735 := bstep (se 1 (by rfl) ⟨3498551, by rfl⟩ : syracuseStep 4664735 = 6997103) B6997103
theorem B2765177 : Blo 542804 2765177 := bstep (se 2 (by rfl) ⟨1036941, by rfl⟩ : syracuseStep 2765177 = 2073883) B2073883
theorem B215102249 : Blo 542804 215102249 := bstep (se 2 (by rfl) ⟨80663343, by rfl⟩ : syracuseStep 215102249 = 161326687) B161326687
theorem B133739423 : Blo 542804 133739423 := bstep (se 1 (by rfl) ⟨100304567, by rfl⟩ : syracuseStep 133739423 = 200609135) B200609135
theorem B3914365 : Blo 542804 3914365 := bstep (se 3 (by rfl) ⟨733943, by rfl⟩ : syracuseStep 3914365 = 1467887) B1467887
theorem B1228409 : Blo 542804 1228409 := bstep (se 2 (by rfl) ⟨460653, by rfl⟩ : syracuseStep 1228409 = 921307) B921307
theorem B1163135 : Blo 542804 1163135 := bstep (se 1 (by rfl) ⟨872351, by rfl⟩ : syracuseStep 1163135 = 1744703) B1744703
theorem B1033555 : Blo 542804 1033555 := bstep (se 1 (by rfl) ⟨775166, by rfl⟩ : syracuseStep 1033555 = 1550333) B1550333
theorem B543771 : Blo 542804 543771 := bstep (se 1 (by rfl) ⟨407828, by rfl⟩ : syracuseStep 543771 = 815657) B815657
theorem B544103 : Blo 542804 544103 := bstep (se 1 (by rfl) ⟨408077, by rfl⟩ : syracuseStep 544103 = 816155) B816155
theorem B544283 : Blo 542804 544283 := bstep (se 1 (by rfl) ⟨408212, by rfl⟩ : syracuseStep 544283 = 816425) B816425
theorem B544539 : Blo 542804 544539 := bstep (se 1 (by rfl) ⟨408404, by rfl⟩ : syracuseStep 544539 = 816809) B816809
theorem B545019 : Blo 542804 545019 := bstep (se 1 (by rfl) ⟨408764, by rfl⟩ : syracuseStep 545019 = 817529) B817529
theorem B546047 : Blo 542804 546047 := bstep (se 1 (by rfl) ⟨409535, by rfl⟩ : syracuseStep 546047 = 819071) B819071
theorem B66903185 : Blo 542804 66903185 := bstep (se 2 (by rfl) ⟨25088694, by rfl⟩ : syracuseStep 66903185 = 50177389) B50177389
theorem B6970859 : Blo 542804 6970859 := bstep (se 1 (by rfl) ⟨5228144, by rfl⟩ : syracuseStep 6970859 = 10456289) B10456289
theorem B614047 : Blo 542804 614047 := bstep (se 1 (by rfl) ⟨460535, by rfl⟩ : syracuseStep 614047 = 921071) B921071
theorem B11166299 : Blo 542804 11166299 := bstep (se 1 (by rfl) ⟨8374724, by rfl⟩ : syracuseStep 11166299 = 16749449) B16749449
theorem B3105449 : Blo 542804 3105449 := bstep (se 2 (by rfl) ⟨1164543, by rfl⟩ : syracuseStep 3105449 = 2329087) B2329087
theorem B5596289 : Blo 542804 5596289 := bstep (se 2 (by rfl) ⟨2098608, by rfl⟩ : syracuseStep 5596289 = 4197217) B4197217
theorem B6221285 : Blo 542804 6221285 := bstep (se 4 (by rfl) ⟨583245, by rfl⟩ : syracuseStep 6221285 = 1166491) B1166491
theorem B7960679 : Blo 542804 7960679 := bstep (se 1 (by rfl) ⟨5970509, by rfl⟩ : syracuseStep 7960679 = 11941019) B11941019
theorem B8847407 : Blo 542804 8847407 := bstep (se 1 (by rfl) ⟨6635555, by rfl⟩ : syracuseStep 8847407 = 13271111) B13271111
theorem B44696711 : Blo 542804 44696711 := bstep (se 1 (by rfl) ⟨33522533, by rfl⟩ : syracuseStep 44696711 = 67045067) B67045067
theorem B1378073 : Blo 542804 1378073 := bstep (se 2 (by rfl) ⟨516777, by rfl⟩ : syracuseStep 1378073 = 1033555) B1033555
theorem B1378579 : Blo 542804 1378579 := bstep (se 1 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 1378579 = 2067869) B2067869
theorem B1380179 : Blo 542804 1380179 := bstep (se 1 (by rfl) ⟨1035134, by rfl⟩ : syracuseStep 1380179 = 2070269) B2070269
theorem B44602123 : Blo 542804 44602123 := bstep (se 1 (by rfl) ⟨33451592, by rfl⟩ : syracuseStep 44602123 = 66903185) B66903185
theorem B5248253 : Blo 542804 5248253 := bstep (se 3 (by rfl) ⟨984047, by rfl⟩ : syracuseStep 5248253 = 1968095) B1968095
theorem B7444199 : Blo 542804 7444199 := bstep (se 1 (by rfl) ⟨5583149, by rfl⟩ : syracuseStep 7444199 = 11166299) B11166299
theorem B2070299 : Blo 542804 2070299 := bstep (se 1 (by rfl) ⟨1552724, by rfl⟩ : syracuseStep 2070299 = 3105449) B3105449
theorem B1382447 : Blo 542804 1382447 := bstep (se 1 (by rfl) ⟨1036835, by rfl⟩ : syracuseStep 1382447 = 2073671) B2073671
theorem B1843451 : Blo 542804 1843451 := bstep (se 1 (by rfl) ⟨1382588, by rfl⟩ : syracuseStep 1843451 = 2765177) B2765177
theorem B143401499 : Blo 542804 143401499 := bstep (se 1 (by rfl) ⟨107551124, by rfl⟩ : syracuseStep 143401499 = 215102249) B215102249
theorem B5219153 : Blo 542804 5219153 := bstep (se 2 (by rfl) ⟨1957182, by rfl⟩ : syracuseStep 5219153 = 3914365) B3914365
theorem B1223855 : Blo 542804 1223855 := bstep (se 1 (by rfl) ⟨917891, by rfl⟩ : syracuseStep 1223855 = 1835783) B1835783
theorem B19443887 : Blo 542804 19443887 := bstep (se 1 (by rfl) ⟨14582915, by rfl⟩ : syracuseStep 19443887 = 29165831) B29165831
theorem B10073117 : Blo 542804 10073117 := bstep (se 3 (by rfl) ⟨1888709, by rfl⟩ : syracuseStep 10073117 = 3777419) B3777419
theorem B1226105 : Blo 542804 1226105 := bstep (se 2 (by rfl) ⟨459789, by rfl⟩ : syracuseStep 1226105 = 919579) B919579
theorem B1227887 : Blo 542804 1227887 := bstep (se 1 (by rfl) ⟨920915, by rfl⟩ : syracuseStep 1227887 = 1841831) B1841831
theorem B1228103 : Blo 542804 1228103 := bstep (se 1 (by rfl) ⟨921077, by rfl⟩ : syracuseStep 1228103 = 1842155) B1842155
theorem B1229543 : Blo 542804 1229543 := bstep (se 1 (by rfl) ⟨922157, by rfl⟩ : syracuseStep 1229543 = 1844315) B1844315
theorem B4147523 : Blo 542804 4147523 := bstep (se 1 (by rfl) ⟨3110642, by rfl⟩ : syracuseStep 4147523 = 6221285) B6221285
theorem B775423 : Blo 542804 775423 := bstep (se 1 (by rfl) ⟨581567, by rfl⟩ : syracuseStep 775423 = 1163135) B1163135
theorem B546559 : Blo 542804 546559 := bstep (se 1 (by rfl) ⟨409919, by rfl⟩ : syracuseStep 546559 = 819839) B819839
theorem B744167 : Blo 542804 744167 := bstep (se 1 (by rfl) ⟨558125, by rfl⟩ : syracuseStep 744167 = 1116251) B1116251
theorem B11755367 : Blo 542804 11755367 := bstep (se 1 (by rfl) ⟨8816525, by rfl⟩ : syracuseStep 11755367 = 17633051) B17633051
theorem B5595965 : Blo 542804 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B4647239 : Blo 542804 4647239 := bstep (se 1 (by rfl) ⟨3485429, by rfl⟩ : syracuseStep 4647239 = 6970859) B6970859
theorem B814331 : Blo 542804 814331 := bstep (se 1 (by rfl) ⟨610748, by rfl⟩ : syracuseStep 814331 = 1221497) B1221497
theorem B3730859 : Blo 542804 3730859 := bstep (se 1 (by rfl) ⟨2798144, by rfl⟩ : syracuseStep 3730859 = 5596289) B5596289
theorem B114782953 : Blo 542804 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B3109823 : Blo 542804 3109823 := bstep (se 1 (by rfl) ⟨2332367, by rfl⟩ : syracuseStep 3109823 = 4664735) B4664735
theorem B89159615 : Blo 542804 89159615 := bstep (se 1 (by rfl) ⟨66869711, by rfl⟩ : syracuseStep 89159615 = 133739423) B133739423
theorem B5307119 : Blo 542804 5307119 := bstep (se 1 (by rfl) ⟨3980339, by rfl⟩ : syracuseStep 5307119 = 7960679) B7960679
theorem B818729 : Blo 542804 818729 := bstep (se 2 (by rfl) ⟨307023, by rfl⟩ : syracuseStep 818729 = 614047) B614047
theorem B818939 : Blo 542804 818939 := bstep (se 1 (by rfl) ⟨614204, by rfl⟩ : syracuseStep 818939 = 1228409) B1228409
theorem B5898271 : Blo 542804 5898271 := bstep (se 1 (by rfl) ⟨4423703, by rfl⟩ : syracuseStep 5898271 = 8847407) B8847407
theorem B819695 : Blo 542804 819695 := bstep (se 1 (by rfl) ⟨614771, by rfl⟩ : syracuseStep 819695 = 1229543) B1229543
theorem B918715 : Blo 542804 918715 := bstep (se 1 (by rfl) ⟨689036, by rfl⟩ : syracuseStep 918715 = 1378073) B1378073
theorem B920119 : Blo 542804 920119 := bstep (se 1 (by rfl) ⟨690089, by rfl⟩ : syracuseStep 920119 = 1380179) B1380179
theorem B1838105 : Blo 542804 1838105 := bstep (se 2 (by rfl) ⟨689289, by rfl⟩ : syracuseStep 1838105 = 1378579) B1378579
theorem B1380199 : Blo 542804 1380199 := bstep (se 1 (by rfl) ⟨1035149, by rfl⟩ : syracuseStep 1380199 = 2070299) B2070299
theorem B921631 : Blo 542804 921631 := bstep (se 1 (by rfl) ⟨691223, by rfl⟩ : syracuseStep 921631 = 1382447) B1382447
theorem B7836911 : Blo 542804 7836911 := bstep (se 1 (by rfl) ⟨5877683, by rfl⟩ : syracuseStep 7836911 = 11755367) B11755367
theorem B3479435 : Blo 542804 3479435 := bstep (se 1 (by rfl) ⟨2609576, by rfl⟩ : syracuseStep 3479435 = 5219153) B5219153
theorem B2073215 : Blo 542804 2073215 := bstep (se 1 (by rfl) ⟨1554911, by rfl⟩ : syracuseStep 2073215 = 3109823) B3109823
theorem B29797807 : Blo 542804 29797807 := bstep (se 1 (by rfl) ⟨22348355, by rfl⟩ : syracuseStep 29797807 = 44696711) B44696711
theorem B2765015 : Blo 542804 2765015 := bstep (se 1 (by rfl) ⟨2073761, by rfl⟩ : syracuseStep 2765015 = 4147523) B4147523
theorem B4962799 : Blo 542804 4962799 := bstep (se 1 (by rfl) ⟨3722099, by rfl⟩ : syracuseStep 4962799 = 7444199) B7444199
theorem B1228967 : Blo 542804 1228967 := bstep (se 1 (by rfl) ⟨921725, by rfl⟩ : syracuseStep 1228967 = 1843451) B1843451
theorem B95600999 : Blo 542804 95600999 := bstep (se 1 (by rfl) ⟨71700749, by rfl⟩ : syracuseStep 95600999 = 143401499) B143401499
theorem B153043937 : Blo 542804 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B3098159 : Blo 542804 3098159 := bstep (se 1 (by rfl) ⟨2323619, by rfl⟩ : syracuseStep 3098159 = 4647239) B4647239
theorem B1033897 : Blo 542804 1033897 := bstep (se 2 (by rfl) ⟨387711, by rfl⟩ : syracuseStep 1033897 = 775423) B775423
theorem B1984445 : Blo 542804 1984445 := bstep (se 3 (by rfl) ⟨372083, by rfl⟩ : syracuseStep 1984445 = 744167) B744167
theorem B542887 : Blo 542804 542887 := bstep (se 1 (by rfl) ⟨407165, by rfl⟩ : syracuseStep 542887 = 814331) B814331
theorem B12962591 : Blo 542804 12962591 := bstep (se 1 (by rfl) ⟨9721943, by rfl⟩ : syracuseStep 12962591 = 19443887) B19443887
theorem B545819 : Blo 542804 545819 := bstep (se 1 (by rfl) ⟨409364, by rfl⟩ : syracuseStep 545819 = 818729) B818729
theorem B545959 : Blo 542804 545959 := bstep (se 1 (by rfl) ⟨409469, by rfl⟩ : syracuseStep 545959 = 818939) B818939
theorem B26861645 : Blo 542804 26861645 := bstep (se 3 (by rfl) ⟨5036558, by rfl⟩ : syracuseStep 26861645 = 10073117) B10073117
theorem B3498835 : Blo 542804 3498835 := bstep (se 1 (by rfl) ⟨2624126, by rfl⟩ : syracuseStep 3498835 = 5248253) B5248253
theorem B3730643 : Blo 542804 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B59469497 : Blo 542804 59469497 := bstep (se 2 (by rfl) ⟨22301061, by rfl⟩ : syracuseStep 59469497 = 44602123) B44602123
theorem B815903 : Blo 542804 815903 := bstep (se 1 (by rfl) ⟨611927, by rfl⟩ : syracuseStep 815903 = 1223855) B1223855
theorem B2487239 : Blo 542804 2487239 := bstep (se 1 (by rfl) ⟨1865429, by rfl⟩ : syracuseStep 2487239 = 3730859) B3730859
theorem B817403 : Blo 542804 817403 := bstep (se 1 (by rfl) ⟨613052, by rfl⟩ : syracuseStep 817403 = 1226105) B1226105
theorem B59439743 : Blo 542804 59439743 := bstep (se 1 (by rfl) ⟨44579807, by rfl⟩ : syracuseStep 59439743 = 89159615) B89159615
theorem B3538079 : Blo 542804 3538079 := bstep (se 1 (by rfl) ⟨2653559, by rfl⟩ : syracuseStep 3538079 = 5307119) B5307119
theorem B818591 : Blo 542804 818591 := bstep (se 1 (by rfl) ⟨613943, by rfl⟩ : syracuseStep 818591 = 1227887) B1227887
theorem B818735 : Blo 542804 818735 := bstep (se 1 (by rfl) ⟨614051, by rfl⟩ : syracuseStep 818735 = 1228103) B1228103
theorem B7864361 : Blo 542804 7864361 := bstep (se 2 (by rfl) ⟨2949135, by rfl⟩ : syracuseStep 7864361 = 5898271) B5898271
theorem B819311 : Blo 542804 819311 := bstep (se 1 (by rfl) ⟨614483, by rfl⟩ : syracuseStep 819311 = 1228967) B1228967
theorem B71631053 : Blo 542804 71631053 := bstep (se 3 (by rfl) ⟨13430822, by rfl⟩ : syracuseStep 71631053 = 26861645) B26861645
theorem B63733999 : Blo 542804 63733999 := bstep (se 1 (by rfl) ⟨47800499, by rfl⟩ : syracuseStep 63733999 = 95600999) B95600999
theorem B2065439 : Blo 542804 2065439 := bstep (se 1 (by rfl) ⟨1549079, by rfl⟩ : syracuseStep 2065439 = 3098159) B3098159
theorem B1378529 : Blo 542804 1378529 := bstep (se 2 (by rfl) ⟨516948, by rfl⟩ : syracuseStep 1378529 = 1033897) B1033897
theorem B1840265 : Blo 542804 1840265 := bstep (se 2 (by rfl) ⟨690099, by rfl⟩ : syracuseStep 1840265 = 1380199) B1380199
theorem B1382143 : Blo 542804 1382143 := bstep (se 1 (by rfl) ⟨1036607, by rfl⟩ : syracuseStep 1382143 = 2073215) B2073215
theorem B1843343 : Blo 542804 1843343 := bstep (se 1 (by rfl) ⟨1382507, by rfl⟩ : syracuseStep 1843343 = 2765015) B2765015
theorem B39626495 : Blo 542804 39626495 := bstep (se 1 (by rfl) ⟨29719871, by rfl⟩ : syracuseStep 39626495 = 59439743) B59439743
theorem B4665113 : Blo 542804 4665113 := bstep (se 2 (by rfl) ⟨1749417, by rfl⟩ : syracuseStep 4665113 = 3498835) B3498835
theorem B1322963 : Blo 542804 1322963 := bstep (se 1 (by rfl) ⟨992222, by rfl⟩ : syracuseStep 1322963 = 1984445) B1984445
theorem B1224953 : Blo 542804 1224953 := bstep (se 2 (by rfl) ⟨459357, by rfl⟩ : syracuseStep 1224953 = 918715) B918715
theorem B1225403 : Blo 542804 1225403 := bstep (se 1 (by rfl) ⟨919052, by rfl⟩ : syracuseStep 1225403 = 1838105) B1838105
theorem B1226825 : Blo 542804 1226825 := bstep (se 2 (by rfl) ⟨460059, by rfl⟩ : syracuseStep 1226825 = 920119) B920119
theorem B5224607 : Blo 542804 5224607 := bstep (se 1 (by rfl) ⟨3918455, by rfl⟩ : syracuseStep 5224607 = 7836911) B7836911
theorem B39730409 : Blo 542804 39730409 := bstep (se 2 (by rfl) ⟨14898903, by rfl⟩ : syracuseStep 39730409 = 29797807) B29797807
theorem B1228841 : Blo 542804 1228841 := bstep (se 2 (by rfl) ⟨460815, by rfl⟩ : syracuseStep 1228841 = 921631) B921631
theorem B543935 : Blo 542804 543935 := bstep (se 1 (by rfl) ⟨407951, by rfl⟩ : syracuseStep 543935 = 815903) B815903
theorem B1658159 : Blo 542804 1658159 := bstep (se 1 (by rfl) ⟨1243619, by rfl⟩ : syracuseStep 1658159 = 2487239) B2487239
theorem B544935 : Blo 542804 544935 := bstep (se 1 (by rfl) ⟨408701, by rfl⟩ : syracuseStep 544935 = 817403) B817403
theorem B545727 : Blo 542804 545727 := bstep (se 1 (by rfl) ⟨409295, by rfl⟩ : syracuseStep 545727 = 818591) B818591
theorem B545823 : Blo 542804 545823 := bstep (se 1 (by rfl) ⟨409367, by rfl⟩ : syracuseStep 545823 = 818735) B818735
theorem B546463 : Blo 542804 546463 := bstep (se 1 (by rfl) ⟨409847, by rfl⟩ : syracuseStep 546463 = 819695) B819695
theorem B102029291 : Blo 542804 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B8641727 : Blo 542804 8641727 := bstep (se 1 (by rfl) ⟨6481295, by rfl⟩ : syracuseStep 8641727 = 12962591) B12962591
theorem B2319623 : Blo 542804 2319623 := bstep (se 1 (by rfl) ⟨1739717, by rfl⟩ : syracuseStep 2319623 = 3479435) B3479435
theorem B2487095 : Blo 542804 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B39646331 : Blo 542804 39646331 := bstep (se 1 (by rfl) ⟨29734748, by rfl⟩ : syracuseStep 39646331 = 59469497) B59469497
theorem B6617065 : Blo 542804 6617065 := bstep (se 2 (by rfl) ⟨2481399, by rfl⟩ : syracuseStep 6617065 = 4962799) B4962799
theorem B2358719 : Blo 542804 2358719 := bstep (se 1 (by rfl) ⟨1769039, by rfl⟩ : syracuseStep 2358719 = 3538079) B3538079
theorem B5242907 : Blo 542804 5242907 := bstep (se 1 (by rfl) ⟨3932180, by rfl⟩ : syracuseStep 5242907 = 7864361) B7864361
theorem B819227 : Blo 542804 819227 := bstep (se 1 (by rfl) ⟨614420, by rfl⟩ : syracuseStep 819227 = 1228841) B1228841
theorem B1376959 : Blo 542804 1376959 := bstep (se 1 (by rfl) ⟨1032719, by rfl⟩ : syracuseStep 1376959 = 2065439) B2065439
theorem B919019 : Blo 542804 919019 := bstep (se 1 (by rfl) ⟨689264, by rfl⟩ : syracuseStep 919019 = 1378529) B1378529
theorem B1546415 : Blo 542804 1546415 := bstep (se 1 (by rfl) ⟨1159811, by rfl⟩ : syracuseStep 1546415 = 2319623) B2319623
theorem B26417663 : Blo 542804 26417663 := bstep (se 1 (by rfl) ⟨19813247, by rfl⟩ : syracuseStep 26417663 = 39626495) B39626495
theorem B1842857 : Blo 542804 1842857 := bstep (se 2 (by rfl) ⟨691071, by rfl⟩ : syracuseStep 1842857 = 1382143) B1382143
theorem B8822753 : Blo 542804 8822753 := bstep (se 2 (by rfl) ⟨3308532, by rfl⟩ : syracuseStep 8822753 = 6617065) B6617065
theorem B3483071 : Blo 542804 3483071 := bstep (se 1 (by rfl) ⟨2612303, by rfl⟩ : syracuseStep 3483071 = 5224607) B5224607
theorem B26486939 : Blo 542804 26486939 := bstep (se 1 (by rfl) ⟨19865204, by rfl⟩ : syracuseStep 26486939 = 39730409) B39730409
theorem B47754035 : Blo 542804 47754035 := bstep (se 1 (by rfl) ⟨35815526, by rfl⟩ : syracuseStep 47754035 = 71631053) B71631053
theorem B84978665 : Blo 542804 84978665 := bstep (se 2 (by rfl) ⟨31866999, by rfl⟩ : syracuseStep 84978665 = 63733999) B63733999
theorem B1226843 : Blo 542804 1226843 := bstep (se 1 (by rfl) ⟨920132, by rfl⟩ : syracuseStep 1226843 = 1840265) B1840265
theorem B1228895 : Blo 542804 1228895 := bstep (se 1 (by rfl) ⟨921671, by rfl⟩ : syracuseStep 1228895 = 1843343) B1843343
theorem B1658063 : Blo 542804 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B26430887 : Blo 542804 26430887 := bstep (se 1 (by rfl) ⟨19823165, by rfl⟩ : syracuseStep 26430887 = 39646331) B39646331
theorem B546207 : Blo 542804 546207 := bstep (se 1 (by rfl) ⟨409655, by rfl⟩ : syracuseStep 546207 = 819311) B819311
theorem B1105439 : Blo 542804 1105439 := bstep (se 1 (by rfl) ⟨829079, by rfl⟩ : syracuseStep 1105439 = 1658159) B1658159
theorem B68019527 : Blo 542804 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B5761151 : Blo 542804 5761151 := bstep (se 1 (by rfl) ⟨4320863, by rfl⟩ : syracuseStep 5761151 = 8641727) B8641727
theorem B3110075 : Blo 542804 3110075 := bstep (se 1 (by rfl) ⟨2332556, by rfl⟩ : syracuseStep 3110075 = 4665113) B4665113
theorem B881975 : Blo 542804 881975 := bstep (se 1 (by rfl) ⟨661481, by rfl⟩ : syracuseStep 881975 = 1322963) B1322963
theorem B816635 : Blo 542804 816635 := bstep (se 1 (by rfl) ⟨612476, by rfl⟩ : syracuseStep 816635 = 1224953) B1224953
theorem B816935 : Blo 542804 816935 := bstep (se 1 (by rfl) ⟨612701, by rfl⟩ : syracuseStep 816935 = 1225403) B1225403
theorem B817883 : Blo 542804 817883 := bstep (se 1 (by rfl) ⟨613412, by rfl⟩ : syracuseStep 817883 = 1226825) B1226825
theorem B1572479 : Blo 542804 1572479 := bstep (se 1 (by rfl) ⟨1179359, by rfl⟩ : syracuseStep 1572479 = 2358719) B2358719
theorem B819263 : Blo 542804 819263 := bstep (se 1 (by rfl) ⟨614447, by rfl⟩ : syracuseStep 819263 = 1228895) B1228895
theorem B1835945 : Blo 542804 1835945 := bstep (se 2 (by rfl) ⟨688479, by rfl⟩ : syracuseStep 1835945 = 1376959) B1376959
theorem B3840767 : Blo 542804 3840767 := bstep (se 1 (by rfl) ⟨2880575, by rfl⟩ : syracuseStep 3840767 = 5761151) B5761151
theorem B2073383 : Blo 542804 2073383 := bstep (se 1 (by rfl) ⟨1555037, by rfl⟩ : syracuseStep 2073383 = 3110075) B3110075
theorem B1030943 : Blo 542804 1030943 := bstep (se 1 (by rfl) ⟨773207, by rfl⟩ : syracuseStep 1030943 = 1546415) B1546415
theorem B17611775 : Blo 542804 17611775 := bstep (se 1 (by rfl) ⟨13208831, by rfl⟩ : syracuseStep 17611775 = 26417663) B26417663
theorem B1228571 : Blo 542804 1228571 := bstep (se 1 (by rfl) ⟨921428, by rfl⟩ : syracuseStep 1228571 = 1842857) B1842857
theorem B5881835 : Blo 542804 5881835 := bstep (se 1 (by rfl) ⟨4411376, by rfl⟩ : syracuseStep 5881835 = 8822753) B8822753
theorem B31836023 : Blo 542804 31836023 := bstep (se 1 (by rfl) ⟨23877017, by rfl⟩ : syracuseStep 31836023 = 47754035) B47754035
theorem B544423 : Blo 542804 544423 := bstep (se 1 (by rfl) ⟨408317, by rfl⟩ : syracuseStep 544423 = 816635) B816635
theorem B544623 : Blo 542804 544623 := bstep (se 1 (by rfl) ⟨408467, by rfl⟩ : syracuseStep 544623 = 816935) B816935
theorem B545255 : Blo 542804 545255 := bstep (se 1 (by rfl) ⟨408941, by rfl⟩ : syracuseStep 545255 = 817883) B817883
theorem B3495271 : Blo 542804 3495271 := bstep (se 1 (by rfl) ⟨2621453, by rfl⟩ : syracuseStep 3495271 = 5242907) B5242907
theorem B546151 : Blo 542804 546151 := bstep (se 1 (by rfl) ⟨409613, by rfl⟩ : syracuseStep 546151 = 819227) B819227
theorem B612679 : Blo 542804 612679 := bstep (se 1 (by rfl) ⟨459509, by rfl⟩ : syracuseStep 612679 = 919019) B919019
theorem B1105375 : Blo 542804 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B17620591 : Blo 542804 17620591 := bstep (se 1 (by rfl) ⟨13215443, by rfl⟩ : syracuseStep 17620591 = 26430887) B26430887
theorem B45346351 : Blo 542804 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B2322047 : Blo 542804 2322047 := bstep (se 1 (by rfl) ⟨1741535, by rfl⟩ : syracuseStep 2322047 = 3483071) B3483071
theorem B17657959 : Blo 542804 17657959 := bstep (se 1 (by rfl) ⟨13243469, by rfl⟩ : syracuseStep 17657959 = 26486939) B26486939
theorem B56652443 : Blo 542804 56652443 := bstep (se 1 (by rfl) ⟨42489332, by rfl⟩ : syracuseStep 56652443 = 84978665) B84978665
theorem B587983 : Blo 542804 587983 := bstep (se 1 (by rfl) ⟨440987, by rfl⟩ : syracuseStep 587983 = 881975) B881975
theorem B817895 : Blo 542804 817895 := bstep (se 1 (by rfl) ⟨613421, by rfl⟩ : syracuseStep 817895 = 1226843) B1226843
theorem B2947837 : Blo 542804 2947837 := bstep (se 3 (by rfl) ⟨552719, by rfl⟩ : syracuseStep 2947837 = 1105439) B1105439
theorem B1048319 : Blo 542804 1048319 := bstep (se 1 (by rfl) ⟨786239, by rfl⟩ : syracuseStep 1048319 = 1572479) B1572479
theorem B2560511 : Blo 542804 2560511 := bstep (se 1 (by rfl) ⟨1920383, by rfl⟩ : syracuseStep 2560511 = 3840767) B3840767
theorem B60461801 : Blo 542804 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B1382255 : Blo 542804 1382255 := bstep (se 1 (by rfl) ⟨1036691, by rfl⟩ : syracuseStep 1382255 = 2073383) B2073383
theorem B4660361 : Blo 542804 4660361 := bstep (se 2 (by rfl) ⟨1747635, by rfl⟩ : syracuseStep 4660361 = 3495271) B3495271
theorem B11741183 : Blo 542804 11741183 := bstep (se 1 (by rfl) ⟨8805887, by rfl⟩ : syracuseStep 11741183 = 17611775) B17611775
theorem B698879 : Blo 542804 698879 := bstep (se 1 (by rfl) ⟨524159, by rfl⟩ : syracuseStep 698879 = 1048319) B1048319
theorem B1223963 : Blo 542804 1223963 := bstep (se 1 (by rfl) ⟨917972, by rfl⟩ : syracuseStep 1223963 = 1835945) B1835945
theorem B23543945 : Blo 542804 23543945 := bstep (se 2 (by rfl) ⟨8828979, by rfl⟩ : syracuseStep 23543945 = 17657959) B17657959
theorem B37768295 : Blo 542804 37768295 := bstep (se 1 (by rfl) ⟨28326221, by rfl⟩ : syracuseStep 37768295 = 56652443) B56652443
theorem B545263 : Blo 542804 545263 := bstep (se 1 (by rfl) ⟨408947, by rfl⟩ : syracuseStep 545263 = 817895) B817895
theorem B3921223 : Blo 542804 3921223 := bstep (se 1 (by rfl) ⟨2940917, by rfl⟩ : syracuseStep 3921223 = 5881835) B5881835
theorem B546175 : Blo 542804 546175 := bstep (se 1 (by rfl) ⟨409631, by rfl⟩ : syracuseStep 546175 = 819263) B819263
theorem B21224015 : Blo 542804 21224015 := bstep (se 1 (by rfl) ⟨15918011, by rfl⟩ : syracuseStep 21224015 = 31836023) B31836023
theorem B783977 : Blo 542804 783977 := bstep (se 2 (by rfl) ⟨293991, by rfl⟩ : syracuseStep 783977 = 587983) B587983
theorem B816905 : Blo 542804 816905 := bstep (se 2 (by rfl) ⟨306339, by rfl⟩ : syracuseStep 816905 = 612679) B612679
theorem B3930449 : Blo 542804 3930449 := bstep (se 2 (by rfl) ⟨1473918, by rfl⟩ : syracuseStep 3930449 = 2947837) B2947837
theorem B6192125 : Blo 542804 6192125 := bstep (se 3 (by rfl) ⟨1161023, by rfl⟩ : syracuseStep 6192125 = 2322047) B2322047
theorem B687295 : Blo 542804 687295 := bstep (se 1 (by rfl) ⟨515471, by rfl⟩ : syracuseStep 687295 = 1030943) B1030943
theorem B1473833 : Blo 542804 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B23494121 : Blo 542804 23494121 := bstep (se 2 (by rfl) ⟨8810295, by rfl⟩ : syracuseStep 23494121 = 17620591) B17620591
theorem B819047 : Blo 542804 819047 := bstep (se 1 (by rfl) ⟨614285, by rfl⟩ : syracuseStep 819047 = 1228571) B1228571
theorem B15695963 : Blo 542804 15695963 := bstep (se 1 (by rfl) ⟨11771972, by rfl⟩ : syracuseStep 15695963 = 23543945) B23543945
theorem B1707007 : Blo 542804 1707007 := bstep (se 1 (by rfl) ⟨1280255, by rfl⟩ : syracuseStep 1707007 = 2560511) B2560511
theorem B40307867 : Blo 542804 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B921503 : Blo 542804 921503 := bstep (se 1 (by rfl) ⟨691127, by rfl⟩ : syracuseStep 921503 = 1382255) B1382255
theorem B25178863 : Blo 542804 25178863 := bstep (se 1 (by rfl) ⟨18884147, by rfl⟩ : syracuseStep 25178863 = 37768295) B37768295
theorem B5228297 : Blo 542804 5228297 := bstep (se 2 (by rfl) ⟨1960611, by rfl⟩ : syracuseStep 5228297 = 3921223) B3921223
theorem B544603 : Blo 542804 544603 := bstep (se 1 (by rfl) ⟨408452, by rfl⟩ : syracuseStep 544603 = 816905) B816905
theorem B546031 : Blo 542804 546031 := bstep (se 1 (by rfl) ⟨409523, by rfl⟩ : syracuseStep 546031 = 819047) B819047
theorem B2090605 : Blo 542804 2090605 := bstep (se 3 (by rfl) ⟨391988, by rfl⟩ : syracuseStep 2090605 = 783977) B783977
theorem B14149343 : Blo 542804 14149343 := bstep (se 1 (by rfl) ⟨10612007, by rfl⟩ : syracuseStep 14149343 = 21224015) B21224015
theorem B3106907 : Blo 542804 3106907 := bstep (se 1 (by rfl) ⟨2330180, by rfl⟩ : syracuseStep 3106907 = 4660361) B4660361
theorem B10481197 : Blo 542804 10481197 := bstep (se 3 (by rfl) ⟨1965224, by rfl⟩ : syracuseStep 10481197 = 3930449) B3930449
theorem B1863677 : Blo 542804 1863677 := bstep (se 3 (by rfl) ⟨349439, by rfl⟩ : syracuseStep 1863677 = 698879) B698879
theorem B7827455 : Blo 542804 7827455 := bstep (se 1 (by rfl) ⟨5870591, by rfl⟩ : syracuseStep 7827455 = 11741183) B11741183
theorem B815975 : Blo 542804 815975 := bstep (se 1 (by rfl) ⟨611981, by rfl⟩ : syracuseStep 815975 = 1223963) B1223963
theorem B3930221 : Blo 542804 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B916393 : Blo 542804 916393 := bstep (se 2 (by rfl) ⟨343647, by rfl⟩ : syracuseStep 916393 = 687295) B687295
theorem B4128083 : Blo 542804 4128083 := bstep (se 1 (by rfl) ⟨3096062, by rfl⟩ : syracuseStep 4128083 = 6192125) B6192125
theorem B15662747 : Blo 542804 15662747 := bstep (se 1 (by rfl) ⟨11747060, by rfl⟩ : syracuseStep 15662747 = 23494121) B23494121
theorem B26871911 : Blo 542804 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B2787473 : Blo 542804 2787473 := bstep (se 2 (by rfl) ⟨1045302, by rfl⟩ : syracuseStep 2787473 = 2090605) B2090605
theorem B2071271 : Blo 542804 2071271 := bstep (se 1 (by rfl) ⟨1553453, by rfl⟩ : syracuseStep 2071271 = 3106907) B3106907
theorem B5218303 : Blo 542804 5218303 := bstep (se 1 (by rfl) ⟨3913727, by rfl⟩ : syracuseStep 5218303 = 7827455) B7827455
theorem B1221857 : Blo 542804 1221857 := bstep (se 2 (by rfl) ⟨458196, by rfl⟩ : syracuseStep 1221857 = 916393) B916393
theorem B10463975 : Blo 542804 10463975 := bstep (se 1 (by rfl) ⟨7847981, by rfl⟩ : syracuseStep 10463975 = 15695963) B15695963
theorem B3485531 : Blo 542804 3485531 := bstep (se 1 (by rfl) ⟨2614148, by rfl⟩ : syracuseStep 3485531 = 5228297) B5228297
theorem B2276009 : Blo 542804 2276009 := bstep (se 2 (by rfl) ⟨853503, by rfl⟩ : syracuseStep 2276009 = 1707007) B1707007
theorem B13974929 : Blo 542804 13974929 := bstep (se 2 (by rfl) ⟨5240598, by rfl⟩ : syracuseStep 13974929 = 10481197) B10481197
theorem B33571817 : Blo 542804 33571817 := bstep (se 2 (by rfl) ⟨12589431, by rfl⟩ : syracuseStep 33571817 = 25178863) B25178863
theorem B543983 : Blo 542804 543983 := bstep (se 1 (by rfl) ⟨407987, by rfl⟩ : syracuseStep 543983 = 815975) B815975
theorem B10441831 : Blo 542804 10441831 := bstep (se 1 (by rfl) ⟨7831373, by rfl⟩ : syracuseStep 10441831 = 15662747) B15662747
theorem B614335 : Blo 542804 614335 := bstep (se 1 (by rfl) ⟨460751, by rfl⟩ : syracuseStep 614335 = 921503) B921503
theorem B9432895 : Blo 542804 9432895 := bstep (se 1 (by rfl) ⟨7074671, by rfl⟩ : syracuseStep 9432895 = 14149343) B14149343
theorem B1242451 : Blo 542804 1242451 := bstep (se 1 (by rfl) ⟨931838, by rfl⟩ : syracuseStep 1242451 = 1863677) B1863677
theorem B2620147 : Blo 542804 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B2752055 : Blo 542804 2752055 := bstep (se 1 (by rfl) ⟨2064041, by rfl⟩ : syracuseStep 2752055 = 4128083) B4128083
theorem B22381211 : Blo 542804 22381211 := bstep (se 1 (by rfl) ⟨16785908, by rfl⟩ : syracuseStep 22381211 = 33571817) B33571817
theorem B1380847 : Blo 542804 1380847 := bstep (se 1 (by rfl) ⟨1035635, by rfl⟩ : syracuseStep 1380847 = 2071271) B2071271
theorem B6626405 : Blo 542804 6626405 := bstep (se 4 (by rfl) ⟨621225, by rfl⟩ : syracuseStep 6626405 = 1242451) B1242451
theorem B1517339 : Blo 542804 1517339 := bstep (se 1 (by rfl) ⟨1138004, by rfl⟩ : syracuseStep 1517339 = 2276009) B2276009
theorem B9316619 : Blo 542804 9316619 := bstep (se 1 (by rfl) ⟨6987464, by rfl⟩ : syracuseStep 9316619 = 13974929) B13974929
theorem B6957737 : Blo 542804 6957737 := bstep (se 2 (by rfl) ⟨2609151, by rfl⟩ : syracuseStep 6957737 = 5218303) B5218303
theorem B3493529 : Blo 542804 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B9294749 : Blo 542804 9294749 := bstep (se 3 (by rfl) ⟨1742765, by rfl⟩ : syracuseStep 9294749 = 3485531) B3485531
theorem B17914607 : Blo 542804 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B1858315 : Blo 542804 1858315 := bstep (se 1 (by rfl) ⟨1393736, by rfl⟩ : syracuseStep 1858315 = 2787473) B2787473
theorem B12577193 : Blo 542804 12577193 := bstep (se 2 (by rfl) ⟨4716447, by rfl⟩ : syracuseStep 12577193 = 9432895) B9432895
theorem B814571 : Blo 542804 814571 := bstep (se 1 (by rfl) ⟨610928, by rfl⟩ : syracuseStep 814571 = 1221857) B1221857
theorem B13922441 : Blo 542804 13922441 := bstep (se 2 (by rfl) ⟨5220915, by rfl⟩ : syracuseStep 13922441 = 10441831) B10441831
theorem B6975983 : Blo 542804 6975983 := bstep (se 1 (by rfl) ⟨5231987, by rfl⟩ : syracuseStep 6975983 = 10463975) B10463975
theorem B1834703 : Blo 542804 1834703 := bstep (se 1 (by rfl) ⟨1376027, by rfl⟩ : syracuseStep 1834703 = 2752055) B2752055
theorem B819113 : Blo 542804 819113 := bstep (se 2 (by rfl) ⟨307167, by rfl⟩ : syracuseStep 819113 = 614335) B614335
theorem B2329019 : Blo 542804 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B6196499 : Blo 542804 6196499 := bstep (se 1 (by rfl) ⟨4647374, by rfl⟩ : syracuseStep 6196499 = 9294749) B9294749
theorem B1841129 : Blo 542804 1841129 := bstep (se 2 (by rfl) ⟨690423, by rfl⟩ : syracuseStep 1841129 = 1380847) B1380847
theorem B9281627 : Blo 542804 9281627 := bstep (se 1 (by rfl) ⟨6961220, by rfl⟩ : syracuseStep 9281627 = 13922441) B13922441
theorem B17670413 : Blo 542804 17670413 := bstep (se 3 (by rfl) ⟨3313202, by rfl⟩ : syracuseStep 17670413 = 6626405) B6626405
theorem B1223135 : Blo 542804 1223135 := bstep (se 1 (by rfl) ⟨917351, by rfl⟩ : syracuseStep 1223135 = 1834703) B1834703
theorem B14920807 : Blo 542804 14920807 := bstep (se 1 (by rfl) ⟨11190605, by rfl⟩ : syracuseStep 14920807 = 22381211) B22381211
theorem B11943071 : Blo 542804 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B6211079 : Blo 542804 6211079 := bstep (se 1 (by rfl) ⟨4658309, by rfl⟩ : syracuseStep 6211079 = 9316619) B9316619
theorem B4638491 : Blo 542804 4638491 := bstep (se 1 (by rfl) ⟨3478868, by rfl⟩ : syracuseStep 4638491 = 6957737) B6957737
theorem B543047 : Blo 542804 543047 := bstep (se 1 (by rfl) ⟨407285, by rfl⟩ : syracuseStep 543047 = 814571) B814571
theorem B2477753 : Blo 542804 2477753 := bstep (se 2 (by rfl) ⟨929157, by rfl⟩ : syracuseStep 2477753 = 1858315) B1858315
theorem B546075 : Blo 542804 546075 := bstep (se 1 (by rfl) ⟨409556, by rfl⟩ : syracuseStep 546075 = 819113) B819113
theorem B1011559 : Blo 542804 1011559 := bstep (se 1 (by rfl) ⟨758669, by rfl⟩ : syracuseStep 1011559 = 1517339) B1517339
theorem B8384795 : Blo 542804 8384795 := bstep (se 1 (by rfl) ⟨6288596, by rfl⟩ : syracuseStep 8384795 = 12577193) B12577193
theorem B4650655 : Blo 542804 4650655 := bstep (se 1 (by rfl) ⟨3487991, by rfl⟩ : syracuseStep 4650655 = 6975983) B6975983
theorem B47121101 : Blo 542804 47121101 := bstep (se 3 (by rfl) ⟨8835206, by rfl⟩ : syracuseStep 47121101 = 17670413) B17670413
theorem B4130999 : Blo 542804 4130999 := bstep (se 1 (by rfl) ⟨3098249, by rfl⟩ : syracuseStep 4130999 = 6196499) B6196499
theorem B19894409 : Blo 542804 19894409 := bstep (se 2 (by rfl) ⟨7460403, by rfl⟩ : syracuseStep 19894409 = 14920807) B14920807
theorem B1348745 : Blo 542804 1348745 := bstep (se 2 (by rfl) ⟨505779, by rfl⟩ : syracuseStep 1348745 = 1011559) B1011559
theorem B6200873 : Blo 542804 6200873 := bstep (se 2 (by rfl) ⟨2325327, by rfl⟩ : syracuseStep 6200873 = 4650655) B4650655
theorem B4140719 : Blo 542804 4140719 := bstep (se 1 (by rfl) ⟨3105539, by rfl⟩ : syracuseStep 4140719 = 6211079) B6211079
theorem B3092327 : Blo 542804 3092327 := bstep (se 1 (by rfl) ⟨2319245, by rfl⟩ : syracuseStep 3092327 = 4638491) B4638491
theorem B1552679 : Blo 542804 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B1651835 : Blo 542804 1651835 := bstep (se 1 (by rfl) ⟨1238876, by rfl⟩ : syracuseStep 1651835 = 2477753) B2477753
theorem B1227419 : Blo 542804 1227419 := bstep (se 1 (by rfl) ⟨920564, by rfl⟩ : syracuseStep 1227419 = 1841129) B1841129
theorem B5589863 : Blo 542804 5589863 := bstep (se 1 (by rfl) ⟨4192397, by rfl⟩ : syracuseStep 5589863 = 8384795) B8384795
theorem B6187751 : Blo 542804 6187751 := bstep (se 1 (by rfl) ⟨4640813, by rfl⟩ : syracuseStep 6187751 = 9281627) B9281627
theorem B815423 : Blo 542804 815423 := bstep (se 1 (by rfl) ⟨611567, by rfl⟩ : syracuseStep 815423 = 1223135) B1223135
theorem B7962047 : Blo 542804 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B2753999 : Blo 542804 2753999 := bstep (se 1 (by rfl) ⟨2065499, by rfl⟩ : syracuseStep 2753999 = 4130999) B4130999
theorem B4133915 : Blo 542804 4133915 := bstep (se 1 (by rfl) ⟨3100436, by rfl⟩ : syracuseStep 4133915 = 6200873) B6200873
theorem B2760479 : Blo 542804 2760479 := bstep (se 1 (by rfl) ⟨2070359, by rfl⟩ : syracuseStep 2760479 = 4140719) B4140719
theorem B1035119 : Blo 542804 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B543615 : Blo 542804 543615 := bstep (se 1 (by rfl) ⟨407711, by rfl⟩ : syracuseStep 543615 = 815423) B815423
theorem B1101223 : Blo 542804 1101223 := bstep (se 1 (by rfl) ⟨825917, by rfl⟩ : syracuseStep 1101223 = 1651835) B1651835
theorem B31414067 : Blo 542804 31414067 := bstep (se 1 (by rfl) ⟨23560550, by rfl⟩ : syracuseStep 31414067 = 47121101) B47121101
theorem B3726575 : Blo 542804 3726575 := bstep (se 1 (by rfl) ⟨2794931, by rfl⟩ : syracuseStep 3726575 = 5589863) B5589863
theorem B13262939 : Blo 542804 13262939 := bstep (se 1 (by rfl) ⟨9947204, by rfl⟩ : syracuseStep 13262939 = 19894409) B19894409
theorem B3596653 : Blo 542804 3596653 := bstep (se 3 (by rfl) ⟨674372, by rfl⟩ : syracuseStep 3596653 = 1348745) B1348745
theorem B4125167 : Blo 542804 4125167 := bstep (se 1 (by rfl) ⟨3093875, by rfl⟩ : syracuseStep 4125167 = 6187751) B6187751
theorem B2061551 : Blo 542804 2061551 := bstep (se 1 (by rfl) ⟨1546163, by rfl⟩ : syracuseStep 2061551 = 3092327) B3092327
theorem B818279 : Blo 542804 818279 := bstep (se 1 (by rfl) ⟨613709, by rfl⟩ : syracuseStep 818279 = 1227419) B1227419
theorem B5308031 : Blo 542804 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B1835999 : Blo 542804 1835999 := bstep (se 1 (by rfl) ⟨1376999, by rfl⟩ : syracuseStep 1835999 = 2753999) B2753999
theorem B2755943 : Blo 542804 2755943 := bstep (se 1 (by rfl) ⟨2066957, by rfl⟩ : syracuseStep 2755943 = 4133915) B4133915
theorem B20942711 : Blo 542804 20942711 := bstep (se 1 (by rfl) ⟨15707033, by rfl⟩ : syracuseStep 20942711 = 31414067) B31414067
theorem B1840319 : Blo 542804 1840319 := bstep (se 1 (by rfl) ⟨1380239, by rfl⟩ : syracuseStep 1840319 = 2760479) B2760479
theorem B2760317 : Blo 542804 2760317 := bstep (se 3 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 2760317 = 1035119) B1035119
theorem B4795537 : Blo 542804 4795537 := bstep (se 2 (by rfl) ⟨1798326, by rfl⟩ : syracuseStep 4795537 = 3596653) B3596653
theorem B545519 : Blo 542804 545519 := bstep (se 1 (by rfl) ⟨409139, by rfl⟩ : syracuseStep 545519 = 818279) B818279
theorem B1468297 : Blo 542804 1468297 := bstep (se 2 (by rfl) ⟨550611, by rfl⟩ : syracuseStep 1468297 = 1101223) B1101223
theorem B2484383 : Blo 542804 2484383 := bstep (se 1 (by rfl) ⟨1863287, by rfl⟩ : syracuseStep 2484383 = 3726575) B3726575
theorem B8841959 : Blo 542804 8841959 := bstep (se 1 (by rfl) ⟨6631469, by rfl⟩ : syracuseStep 8841959 = 13262939) B13262939
theorem B2750111 : Blo 542804 2750111 := bstep (se 1 (by rfl) ⟨2062583, by rfl⟩ : syracuseStep 2750111 = 4125167) B4125167
theorem B1374367 : Blo 542804 1374367 := bstep (se 1 (by rfl) ⟨1030775, by rfl⟩ : syracuseStep 1374367 = 2061551) B2061551
theorem B3538687 : Blo 542804 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B1837295 : Blo 542804 1837295 := bstep (se 1 (by rfl) ⟨1377971, by rfl⟩ : syracuseStep 1837295 = 2755943) B2755943
theorem B13961807 : Blo 542804 13961807 := bstep (se 1 (by rfl) ⟨10471355, by rfl⟩ : syracuseStep 13961807 = 20942711) B20942711
theorem B6394049 : Blo 542804 6394049 := bstep (se 2 (by rfl) ⟨2397768, by rfl⟩ : syracuseStep 6394049 = 4795537) B4795537
theorem B1840211 : Blo 542804 1840211 := bstep (se 1 (by rfl) ⟨1380158, by rfl⟩ : syracuseStep 1840211 = 2760317) B2760317
theorem B6625021 : Blo 542804 6625021 := bstep (se 3 (by rfl) ⟨1242191, by rfl⟩ : syracuseStep 6625021 = 2484383) B2484383
theorem B1223999 : Blo 542804 1223999 := bstep (se 1 (by rfl) ⟨917999, by rfl⟩ : syracuseStep 1223999 = 1835999) B1835999
theorem B1226879 : Blo 542804 1226879 := bstep (se 1 (by rfl) ⟨920159, by rfl⟩ : syracuseStep 1226879 = 1840319) B1840319
theorem B5894639 : Blo 542804 5894639 := bstep (se 1 (by rfl) ⟨4420979, by rfl⟩ : syracuseStep 5894639 = 8841959) B8841959
theorem B1832489 : Blo 542804 1832489 := bstep (se 2 (by rfl) ⟨687183, by rfl⟩ : syracuseStep 1832489 = 1374367) B1374367
theorem B1833407 : Blo 542804 1833407 := bstep (se 1 (by rfl) ⟨1375055, by rfl⟩ : syracuseStep 1833407 = 2750111) B2750111
theorem B7830917 : Blo 542804 7830917 := bstep (se 4 (by rfl) ⟨734148, by rfl⟩ : syracuseStep 7830917 = 1468297) B1468297
theorem B4718249 : Blo 542804 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B9307871 : Blo 542804 9307871 := bstep (se 1 (by rfl) ⟨6980903, by rfl⟩ : syracuseStep 9307871 = 13961807) B13961807
theorem B4262699 : Blo 542804 4262699 := bstep (se 1 (by rfl) ⟨3197024, by rfl⟩ : syracuseStep 4262699 = 6394049) B6394049
theorem B141333781 : Blo 542804 141333781 := bstep (se 6 (by rfl) ⟨3312510, by rfl⟩ : syracuseStep 141333781 = 6625021) B6625021
theorem B1221659 : Blo 542804 1221659 := bstep (se 1 (by rfl) ⟨916244, by rfl⟩ : syracuseStep 1221659 = 1832489) B1832489
theorem B1222271 : Blo 542804 1222271 := bstep (se 1 (by rfl) ⟨916703, by rfl⟩ : syracuseStep 1222271 = 1833407) B1833407
theorem B5220611 : Blo 542804 5220611 := bstep (se 1 (by rfl) ⟨3915458, by rfl⟩ : syracuseStep 5220611 = 7830917) B7830917
theorem B1224863 : Blo 542804 1224863 := bstep (se 1 (by rfl) ⟨918647, by rfl⟩ : syracuseStep 1224863 = 1837295) B1837295
theorem B1226807 : Blo 542804 1226807 := bstep (se 1 (by rfl) ⟨920105, by rfl⟩ : syracuseStep 1226807 = 1840211) B1840211
theorem B815999 : Blo 542804 815999 := bstep (se 1 (by rfl) ⟨611999, by rfl⟩ : syracuseStep 815999 = 1223999) B1223999
theorem B3929759 : Blo 542804 3929759 := bstep (se 1 (by rfl) ⟨2947319, by rfl⟩ : syracuseStep 3929759 = 5894639) B5894639
theorem B817919 : Blo 542804 817919 := bstep (se 1 (by rfl) ⟨613439, by rfl⟩ : syracuseStep 817919 = 1226879) B1226879
theorem B3145499 : Blo 542804 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B3480407 : Blo 542804 3480407 := bstep (se 1 (by rfl) ⟨2610305, by rfl⟩ : syracuseStep 3480407 = 5220611) B5220611
theorem B6205247 : Blo 542804 6205247 := bstep (se 1 (by rfl) ⟨4653935, by rfl⟩ : syracuseStep 6205247 = 9307871) B9307871
theorem B543999 : Blo 542804 543999 := bstep (se 1 (by rfl) ⟨407999, by rfl⟩ : syracuseStep 543999 = 815999) B815999
theorem B545279 : Blo 542804 545279 := bstep (se 1 (by rfl) ⟨408959, by rfl⟩ : syracuseStep 545279 = 817919) B817919
theorem B2841799 : Blo 542804 2841799 := bstep (se 1 (by rfl) ⟨2131349, by rfl⟩ : syracuseStep 2841799 = 4262699) B4262699
theorem B814439 : Blo 542804 814439 := bstep (se 1 (by rfl) ⟨610829, by rfl⟩ : syracuseStep 814439 = 1221659) B1221659
theorem B814847 : Blo 542804 814847 := bstep (se 1 (by rfl) ⟨611135, by rfl⟩ : syracuseStep 814847 = 1222271) B1222271
theorem B188445041 : Blo 542804 188445041 := bstep (se 2 (by rfl) ⟨70666890, by rfl⟩ : syracuseStep 188445041 = 141333781) B141333781
theorem B816575 : Blo 542804 816575 := bstep (se 1 (by rfl) ⟨612431, by rfl⟩ : syracuseStep 816575 = 1224863) B1224863
theorem B2619839 : Blo 542804 2619839 := bstep (se 1 (by rfl) ⟨1964879, by rfl⟩ : syracuseStep 2619839 = 3929759) B3929759
theorem B817871 : Blo 542804 817871 := bstep (se 1 (by rfl) ⟨613403, by rfl⟩ : syracuseStep 817871 = 1226807) B1226807
theorem B2096999 : Blo 542804 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B4136831 : Blo 542804 4136831 := bstep (se 1 (by rfl) ⟨3102623, by rfl⟩ : syracuseStep 4136831 = 6205247) B6205247
theorem B1746559 : Blo 542804 1746559 := bstep (se 1 (by rfl) ⟨1309919, by rfl⟩ : syracuseStep 1746559 = 2619839) B2619839
theorem B542959 : Blo 542804 542959 := bstep (se 1 (by rfl) ⟨407219, by rfl⟩ : syracuseStep 542959 = 814439) B814439
theorem B543231 : Blo 542804 543231 := bstep (se 1 (by rfl) ⟨407423, by rfl⟩ : syracuseStep 543231 = 814847) B814847
theorem B544383 : Blo 542804 544383 := bstep (se 1 (by rfl) ⟨408287, by rfl⟩ : syracuseStep 544383 = 816575) B816575
theorem B3789065 : Blo 542804 3789065 := bstep (se 2 (by rfl) ⟨1420899, by rfl⟩ : syracuseStep 3789065 = 2841799) B2841799
theorem B545247 : Blo 542804 545247 := bstep (se 1 (by rfl) ⟨408935, by rfl⟩ : syracuseStep 545247 = 817871) B817871
theorem B1397999 : Blo 542804 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B2320271 : Blo 542804 2320271 := bstep (se 1 (by rfl) ⟨1740203, by rfl⟩ : syracuseStep 2320271 = 3480407) B3480407
theorem B125630027 : Blo 542804 125630027 := bstep (se 1 (by rfl) ⟨94222520, by rfl⟩ : syracuseStep 125630027 = 188445041) B188445041
theorem B2328745 : Blo 542804 2328745 := bstep (se 2 (by rfl) ⟨873279, by rfl⟩ : syracuseStep 2328745 = 1746559) B1746559
theorem B2757887 : Blo 542804 2757887 := bstep (se 1 (by rfl) ⟨2068415, by rfl⟩ : syracuseStep 2757887 = 4136831) B4136831
theorem B1546847 : Blo 542804 1546847 := bstep (se 1 (by rfl) ⟨1160135, by rfl⟩ : syracuseStep 1546847 = 2320271) B2320271
theorem B10104173 : Blo 542804 10104173 := bstep (se 3 (by rfl) ⟨1894532, by rfl⟩ : syracuseStep 10104173 = 3789065) B3789065
theorem B931999 : Blo 542804 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B83753351 : Blo 542804 83753351 := bstep (se 1 (by rfl) ⟨62815013, by rfl⟩ : syracuseStep 83753351 = 125630027) B125630027
theorem B1838591 : Blo 542804 1838591 := bstep (se 1 (by rfl) ⟨1378943, by rfl⟩ : syracuseStep 1838591 = 2757887) B2757887
theorem B1031231 : Blo 542804 1031231 := bstep (se 1 (by rfl) ⟨773423, by rfl⟩ : syracuseStep 1031231 = 1546847) B1546847
theorem B6736115 : Blo 542804 6736115 := bstep (se 1 (by rfl) ⟨5052086, by rfl⟩ : syracuseStep 6736115 = 10104173) B10104173
theorem B3104993 : Blo 542804 3104993 := bstep (se 2 (by rfl) ⟨1164372, by rfl⟩ : syracuseStep 3104993 = 2328745) B2328745
theorem B1242665 : Blo 542804 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B55835567 : Blo 542804 55835567 := bstep (se 1 (by rfl) ⟨41876675, by rfl⟩ : syracuseStep 55835567 = 83753351) B83753351
theorem B4490743 : Blo 542804 4490743 := bstep (se 1 (by rfl) ⟨3368057, by rfl⟩ : syracuseStep 4490743 = 6736115) B6736115
theorem B2069995 : Blo 542804 2069995 := bstep (se 1 (by rfl) ⟨1552496, by rfl⟩ : syracuseStep 2069995 = 3104993) B3104993
theorem B828443 : Blo 542804 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B1225727 : Blo 542804 1225727 := bstep (se 1 (by rfl) ⟨919295, by rfl⟩ : syracuseStep 1225727 = 1838591) B1838591
theorem B2749949 : Blo 542804 2749949 := bstep (se 3 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 2749949 = 1031231) B1031231
theorem B37223711 : Blo 542804 37223711 := bstep (se 1 (by rfl) ⟨27917783, by rfl⟩ : syracuseStep 37223711 = 55835567) B55835567
theorem B2759993 : Blo 542804 2759993 := bstep (se 2 (by rfl) ⟨1034997, by rfl⟩ : syracuseStep 2759993 = 2069995) B2069995
theorem B24815807 : Blo 542804 24815807 := bstep (se 1 (by rfl) ⟨18611855, by rfl⟩ : syracuseStep 24815807 = 37223711) B37223711
theorem B5987657 : Blo 542804 5987657 := bstep (se 2 (by rfl) ⟨2245371, by rfl⟩ : syracuseStep 5987657 = 4490743) B4490743
theorem B552295 : Blo 542804 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B817151 : Blo 542804 817151 := bstep (se 1 (by rfl) ⟨612863, by rfl⟩ : syracuseStep 817151 = 1225727) B1225727
theorem B1833299 : Blo 542804 1833299 := bstep (se 1 (by rfl) ⟨1374974, by rfl⟩ : syracuseStep 1833299 = 2749949) B2749949
theorem B1839995 : Blo 542804 1839995 := bstep (se 1 (by rfl) ⟨1379996, by rfl⟩ : syracuseStep 1839995 = 2759993) B2759993
theorem B1222199 : Blo 542804 1222199 := bstep (se 1 (by rfl) ⟨916649, by rfl⟩ : syracuseStep 1222199 = 1833299) B1833299
theorem B736393 : Blo 542804 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B544767 : Blo 542804 544767 := bstep (se 1 (by rfl) ⟨408575, by rfl⟩ : syracuseStep 544767 = 817151) B817151
theorem B3991771 : Blo 542804 3991771 := bstep (se 1 (by rfl) ⟨2993828, by rfl⟩ : syracuseStep 3991771 = 5987657) B5987657
theorem B16543871 : Blo 542804 16543871 := bstep (se 1 (by rfl) ⟨12407903, by rfl⟩ : syracuseStep 16543871 = 24815807) B24815807
theorem B5322361 : Blo 542804 5322361 := bstep (se 2 (by rfl) ⟨1995885, by rfl⟩ : syracuseStep 5322361 = 3991771) B3991771
theorem B1226663 : Blo 542804 1226663 := bstep (se 1 (by rfl) ⟨919997, by rfl⟩ : syracuseStep 1226663 = 1839995) B1839995
theorem B11029247 : Blo 542804 11029247 := bstep (se 1 (by rfl) ⟨8271935, by rfl⟩ : syracuseStep 11029247 = 16543871) B16543871
theorem B814799 : Blo 542804 814799 := bstep (se 1 (by rfl) ⟨611099, by rfl⟩ : syracuseStep 814799 = 1222199) B1222199
theorem B981857 : Blo 542804 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B7352831 : Blo 542804 7352831 := bstep (se 1 (by rfl) ⟨5514623, by rfl⟩ : syracuseStep 7352831 = 11029247) B11029247
theorem B7096481 : Blo 542804 7096481 := bstep (se 2 (by rfl) ⟨2661180, by rfl⟩ : syracuseStep 7096481 = 5322361) B5322361
theorem B543199 : Blo 542804 543199 := bstep (se 1 (by rfl) ⟨407399, by rfl⟩ : syracuseStep 543199 = 814799) B814799
theorem B817775 : Blo 542804 817775 := bstep (se 1 (by rfl) ⟨613331, by rfl⟩ : syracuseStep 817775 = 1226663) B1226663
theorem B654571 : Blo 542804 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B4730987 : Blo 542804 4730987 := bstep (se 1 (by rfl) ⟨3548240, by rfl⟩ : syracuseStep 4730987 = 7096481) B7096481
theorem B3491045 : Blo 542804 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B4901887 : Blo 542804 4901887 := bstep (se 1 (by rfl) ⟨3676415, by rfl⟩ : syracuseStep 4901887 = 7352831) B7352831
theorem B545183 : Blo 542804 545183 := bstep (se 1 (by rfl) ⟨408887, by rfl⟩ : syracuseStep 545183 = 817775) B817775
theorem B2327363 : Blo 542804 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B3153991 : Blo 542804 3153991 := bstep (se 1 (by rfl) ⟨2365493, by rfl⟩ : syracuseStep 3153991 = 4730987) B4730987
theorem B6535849 : Blo 542804 6535849 := bstep (se 2 (by rfl) ⟨2450943, by rfl⟩ : syracuseStep 6535849 = 4901887) B4901887
theorem B4205321 : Blo 542804 4205321 := bstep (se 2 (by rfl) ⟨1576995, by rfl⟩ : syracuseStep 4205321 = 3153991) B3153991
theorem B1551575 : Blo 542804 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B8714465 : Blo 542804 8714465 := bstep (se 2 (by rfl) ⟨3267924, by rfl⟩ : syracuseStep 8714465 = 6535849) B6535849
theorem B5809643 : Blo 542804 5809643 := bstep (se 1 (by rfl) ⟨4357232, by rfl⟩ : syracuseStep 5809643 = 8714465) B8714465
theorem B2803547 : Blo 542804 2803547 := bstep (se 1 (by rfl) ⟨2102660, by rfl⟩ : syracuseStep 2803547 = 4205321) B4205321
theorem B1034383 : Blo 542804 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B1869031 : Blo 542804 1869031 := bstep (se 1 (by rfl) ⟨1401773, by rfl⟩ : syracuseStep 1869031 = 2803547) B2803547
theorem B1379177 : Blo 542804 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B3873095 : Blo 542804 3873095 := bstep (se 1 (by rfl) ⟨2904821, by rfl⟩ : syracuseStep 3873095 = 5809643) B5809643
theorem B2492041 : Blo 542804 2492041 := bstep (se 2 (by rfl) ⟨934515, by rfl⟩ : syracuseStep 2492041 = 1869031) B1869031
theorem B919451 : Blo 542804 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B2582063 : Blo 542804 2582063 := bstep (se 1 (by rfl) ⟨1936547, by rfl⟩ : syracuseStep 2582063 = 3873095) B3873095
theorem B3322721 : Blo 542804 3322721 := bstep (se 2 (by rfl) ⟨1246020, by rfl⟩ : syracuseStep 3322721 = 2492041) B2492041
theorem B1721375 : Blo 542804 1721375 := bstep (se 1 (by rfl) ⟨1291031, by rfl⟩ : syracuseStep 1721375 = 2582063) B2582063
theorem B612967 : Blo 542804 612967 := bstep (se 1 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 612967 = 919451) B919451
theorem B1147583 : Blo 542804 1147583 := bstep (se 1 (by rfl) ⟨860687, by rfl⟩ : syracuseStep 1147583 = 1721375) B1721375
theorem B2215147 : Blo 542804 2215147 := bstep (se 1 (by rfl) ⟨1661360, by rfl⟩ : syracuseStep 2215147 = 3322721) B3322721
theorem B817289 : Blo 542804 817289 := bstep (se 2 (by rfl) ⟨306483, by rfl⟩ : syracuseStep 817289 = 612967) B612967
theorem B2953529 : Blo 542804 2953529 := bstep (se 2 (by rfl) ⟨1107573, by rfl⟩ : syracuseStep 2953529 = 2215147) B2215147
theorem B765055 : Blo 542804 765055 := bstep (se 1 (by rfl) ⟨573791, by rfl⟩ : syracuseStep 765055 = 1147583) B1147583
theorem B544859 : Blo 542804 544859 := bstep (se 1 (by rfl) ⟨408644, by rfl⟩ : syracuseStep 544859 = 817289) B817289
theorem B1969019 : Blo 542804 1969019 := bstep (se 1 (by rfl) ⟨1476764, by rfl⟩ : syracuseStep 1969019 = 2953529) B2953529
theorem B4080293 : Blo 542804 4080293 := bstep (se 4 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 4080293 = 765055) B765055
theorem B2720195 : Blo 542804 2720195 := bstep (se 1 (by rfl) ⟨2040146, by rfl⟩ : syracuseStep 2720195 = 4080293) B4080293
theorem B1312679 : Blo 542804 1312679 := bstep (se 1 (by rfl) ⟨984509, by rfl⟩ : syracuseStep 1312679 = 1969019) B1969019
theorem B1813463 : Blo 542804 1813463 := bstep (se 1 (by rfl) ⟨1360097, by rfl⟩ : syracuseStep 1813463 = 2720195) B2720195
theorem B875119 : Blo 542804 875119 := bstep (se 1 (by rfl) ⟨656339, by rfl⟩ : syracuseStep 875119 = 1312679) B1312679
theorem B1166825 : Blo 542804 1166825 := bstep (se 2 (by rfl) ⟨437559, by rfl⟩ : syracuseStep 1166825 = 875119) B875119
theorem B1208975 : Blo 542804 1208975 := bstep (se 1 (by rfl) ⟨906731, by rfl⟩ : syracuseStep 1208975 = 1813463) B1813463
theorem B12895733 : Blo 542804 12895733 := bstep (se 5 (by rfl) ⟨604487, by rfl⟩ : syracuseStep 12895733 = 1208975) B1208975
theorem B3111533 : Blo 542804 3111533 := bstep (se 3 (by rfl) ⟨583412, by rfl⟩ : syracuseStep 3111533 = 1166825) B1166825
theorem B2074355 : Blo 542804 2074355 := bstep (se 1 (by rfl) ⟨1555766, by rfl⟩ : syracuseStep 2074355 = 3111533) B3111533
theorem B34388621 : Blo 542804 34388621 := bstep (se 3 (by rfl) ⟨6447866, by rfl⟩ : syracuseStep 34388621 = 12895733) B12895733
theorem B1382903 : Blo 542804 1382903 := bstep (se 1 (by rfl) ⟨1037177, by rfl⟩ : syracuseStep 1382903 = 2074355) B2074355
theorem B22925747 : Blo 542804 22925747 := bstep (se 1 (by rfl) ⟨17194310, by rfl⟩ : syracuseStep 22925747 = 34388621) B34388621
theorem B921935 : Blo 542804 921935 := bstep (se 1 (by rfl) ⟨691451, by rfl⟩ : syracuseStep 921935 = 1382903) B1382903
theorem B15283831 : Blo 542804 15283831 := bstep (se 1 (by rfl) ⟨11462873, by rfl⟩ : syracuseStep 15283831 = 22925747) B22925747
theorem B614623 : Blo 542804 614623 := bstep (se 1 (by rfl) ⟨460967, by rfl⟩ : syracuseStep 614623 = 921935) B921935
theorem B20378441 : Blo 542804 20378441 := bstep (se 2 (by rfl) ⟨7641915, by rfl⟩ : syracuseStep 20378441 = 15283831) B15283831
theorem B819497 : Blo 542804 819497 := bstep (se 2 (by rfl) ⟨307311, by rfl⟩ : syracuseStep 819497 = 614623) B614623
theorem B13585627 : Blo 542804 13585627 := bstep (se 1 (by rfl) ⟨10189220, by rfl⟩ : syracuseStep 13585627 = 20378441) B20378441
theorem B72456677 : Blo 542804 72456677 := bstep (se 4 (by rfl) ⟨6792813, by rfl⟩ : syracuseStep 72456677 = 13585627) B13585627
theorem B546331 : Blo 542804 546331 := bstep (se 1 (by rfl) ⟨409748, by rfl⟩ : syracuseStep 546331 = 819497) B819497
theorem B48304451 : Blo 542804 48304451 := bstep (se 1 (by rfl) ⟨36228338, by rfl⟩ : syracuseStep 48304451 = 72456677) B72456677
theorem B32202967 : Blo 542804 32202967 := bstep (se 1 (by rfl) ⟨24152225, by rfl⟩ : syracuseStep 32202967 = 48304451) B48304451
theorem B42937289 : Blo 542804 42937289 := bstep (se 2 (by rfl) ⟨16101483, by rfl⟩ : syracuseStep 42937289 = 32202967) B32202967
theorem B28624859 : Blo 542804 28624859 := bstep (se 1 (by rfl) ⟨21468644, by rfl⟩ : syracuseStep 28624859 = 42937289) B42937289
theorem B19083239 : Blo 542804 19083239 := bstep (se 1 (by rfl) ⟨14312429, by rfl⟩ : syracuseStep 19083239 = 28624859) B28624859
theorem B12722159 : Blo 542804 12722159 := bstep (se 1 (by rfl) ⟨9541619, by rfl⟩ : syracuseStep 12722159 = 19083239) B19083239
theorem B8481439 : Blo 542804 8481439 := bstep (se 1 (by rfl) ⟨6361079, by rfl⟩ : syracuseStep 8481439 = 12722159) B12722159
theorem B11308585 : Blo 542804 11308585 := bstep (se 2 (by rfl) ⟨4240719, by rfl⟩ : syracuseStep 11308585 = 8481439) B8481439
theorem B15078113 : Blo 542804 15078113 := bstep (se 2 (by rfl) ⟨5654292, by rfl⟩ : syracuseStep 15078113 = 11308585) B11308585
theorem B10052075 : Blo 542804 10052075 := bstep (se 1 (by rfl) ⟨7539056, by rfl⟩ : syracuseStep 10052075 = 15078113) B15078113
theorem B6701383 : Blo 542804 6701383 := bstep (se 1 (by rfl) ⟨5026037, by rfl⟩ : syracuseStep 6701383 = 10052075) B10052075
theorem B8935177 : Blo 542804 8935177 := bstep (se 2 (by rfl) ⟨3350691, by rfl⟩ : syracuseStep 8935177 = 6701383) B6701383
theorem B11913569 : Blo 542804 11913569 := bstep (se 2 (by rfl) ⟨4467588, by rfl⟩ : syracuseStep 11913569 = 8935177) B8935177
theorem B7942379 : Blo 542804 7942379 := bstep (se 1 (by rfl) ⟨5956784, by rfl⟩ : syracuseStep 7942379 = 11913569) B11913569
theorem B84718709 : Blo 542804 84718709 := bstep (se 5 (by rfl) ⟨3971189, by rfl⟩ : syracuseStep 84718709 = 7942379) B7942379
theorem B56479139 : Blo 542804 56479139 := bstep (se 1 (by rfl) ⟨42359354, by rfl⟩ : syracuseStep 56479139 = 84718709) B84718709
theorem B37652759 : Blo 542804 37652759 := bstep (se 1 (by rfl) ⟨28239569, by rfl⟩ : syracuseStep 37652759 = 56479139) B56479139
theorem B25101839 : Blo 542804 25101839 := bstep (se 1 (by rfl) ⟨18826379, by rfl⟩ : syracuseStep 25101839 = 37652759) B37652759
theorem B16734559 : Blo 542804 16734559 := bstep (se 1 (by rfl) ⟨12550919, by rfl⟩ : syracuseStep 16734559 = 25101839) B25101839
theorem B22312745 : Blo 542804 22312745 := bstep (se 2 (by rfl) ⟨8367279, by rfl⟩ : syracuseStep 22312745 = 16734559) B16734559
theorem B14875163 : Blo 542804 14875163 := bstep (se 1 (by rfl) ⟨11156372, by rfl⟩ : syracuseStep 14875163 = 22312745) B22312745
theorem B9916775 : Blo 542804 9916775 := bstep (se 1 (by rfl) ⟨7437581, by rfl⟩ : syracuseStep 9916775 = 14875163) B14875163
theorem B6611183 : Blo 542804 6611183 := bstep (se 1 (by rfl) ⟨4958387, by rfl⟩ : syracuseStep 6611183 = 9916775) B9916775
theorem B4407455 : Blo 542804 4407455 := bstep (se 1 (by rfl) ⟨3305591, by rfl⟩ : syracuseStep 4407455 = 6611183) B6611183
theorem B2938303 : Blo 542804 2938303 := bstep (se 1 (by rfl) ⟨2203727, by rfl⟩ : syracuseStep 2938303 = 4407455) B4407455
theorem B3917737 : Blo 542804 3917737 := bstep (se 2 (by rfl) ⟨1469151, by rfl⟩ : syracuseStep 3917737 = 2938303) B2938303
theorem B5223649 : Blo 542804 5223649 := bstep (se 2 (by rfl) ⟨1958868, by rfl⟩ : syracuseStep 5223649 = 3917737) B3917737
theorem B6964865 : Blo 542804 6964865 := bstep (se 2 (by rfl) ⟨2611824, by rfl⟩ : syracuseStep 6964865 = 5223649) B5223649
theorem B4643243 : Blo 542804 4643243 := bstep (se 1 (by rfl) ⟨3482432, by rfl⟩ : syracuseStep 4643243 = 6964865) B6964865
theorem B3095495 : Blo 542804 3095495 := bstep (se 1 (by rfl) ⟨2321621, by rfl⟩ : syracuseStep 3095495 = 4643243) B4643243
theorem B2063663 : Blo 542804 2063663 := bstep (se 1 (by rfl) ⟨1547747, by rfl⟩ : syracuseStep 2063663 = 3095495) B3095495
theorem B1375775 : Blo 542804 1375775 := bstep (se 1 (by rfl) ⟨1031831, by rfl⟩ : syracuseStep 1375775 = 2063663) B2063663
theorem B917183 : Blo 542804 917183 := bstep (se 1 (by rfl) ⟨687887, by rfl⟩ : syracuseStep 917183 = 1375775) B1375775
theorem B611455 : Blo 542804 611455 := bstep (se 1 (by rfl) ⟨458591, by rfl⟩ : syracuseStep 611455 = 917183) B917183
theorem B815273 : Blo 542804 815273 := bstep (se 2 (by rfl) ⟨305727, by rfl⟩ : syracuseStep 815273 = 611455) B611455
theorem B543515 : Blo 542804 543515 := bstep (se 1 (by rfl) ⟨407636, by rfl⟩ : syracuseStep 543515 = 815273) B815273

theorem C0 (j : ℕ) (h1 : 135701 ≤ j) (h2 : j ≤ 136400) : Blo 542804 (4 * j + 3) := by
  interval_cases j
  · exact B542807
  · exact B542811
  · exact B542815
  · exact B542819
  · exact B542823
  · exact B542827
  · exact B542831
  · exact B542835
  · exact B542839
  · exact B542843
  · exact B542847
  · exact B542851
  · exact B542855
  · exact B542859
  · exact B542863
  · exact B542867
  · exact B542871
  · exact B542875
  · exact B542879
  · exact B542883
  · exact B542887
  · exact B542891
  · exact B542895
  · exact B542899
  · exact B542903
  · exact B542907
  · exact B542911
  · exact B542915
  · exact B542919
  · exact B542923
  · exact B542927
  · exact B542931
  · exact B542935
  · exact B542939
  · exact B542943
  · exact B542947
  · exact B542951
  · exact B542955
  · exact B542959
  · exact B542963
  · exact B542967
  · exact B542971
  · exact B542975
  · exact B542979
  · exact B542983
  · exact B542987
  · exact B542991
  · exact B542995
  · exact B542999
  · exact B543003
  · exact B543007
  · exact B543011
  · exact B543015
  · exact B543019
  · exact B543023
  · exact B543027
  · exact B543031
  · exact B543035
  · exact B543039
  · exact B543043
  · exact B543047
  · exact B543051
  · exact B543055
  · exact B543059
  · exact B543063
  · exact B543067
  · exact B543071
  · exact B543075
  · exact B543079
  · exact B543083
  · exact B543087
  · exact B543091
  · exact B543095
  · exact B543099
  · exact B543103
  · exact B543107
  · exact B543111
  · exact B543115
  · exact B543119
  · exact B543123
  · exact B543127
  · exact B543131
  · exact B543135
  · exact B543139
  · exact B543143
  · exact B543147
  · exact B543151
  · exact B543155
  · exact B543159
  · exact B543163
  · exact B543167
  · exact B543171
  · exact B543175
  · exact B543179
  · exact B543183
  · exact B543187
  · exact B543191
  · exact B543195
  · exact B543199
  · exact B543203
  · exact B543207
  · exact B543211
  · exact B543215
  · exact B543219
  · exact B543223
  · exact B543227
  · exact B543231
  · exact B543235
  · exact B543239
  · exact B543243
  · exact B543247
  · exact B543251
  · exact B543255
  · exact B543259
  · exact B543263
  · exact B543267
  · exact B543271
  · exact B543275
  · exact B543279
  · exact B543283
  · exact B543287
  · exact B543291
  · exact B543295
  · exact B543299
  · exact B543303
  · exact B543307
  · exact B543311
  · exact B543315
  · exact B543319
  · exact B543323
  · exact B543327
  · exact B543331
  · exact B543335
  · exact B543339
  · exact B543343
  · exact B543347
  · exact B543351
  · exact B543355
  · exact B543359
  · exact B543363
  · exact B543367
  · exact B543371
  · exact B543375
  · exact B543379
  · exact B543383
  · exact B543387
  · exact B543391
  · exact B543395
  · exact B543399
  · exact B543403
  · exact B543407
  · exact B543411
  · exact B543415
  · exact B543419
  · exact B543423
  · exact B543427
  · exact B543431
  · exact B543435
  · exact B543439
  · exact B543443
  · exact B543447
  · exact B543451
  · exact B543455
  · exact B543459
  · exact B543463
  · exact B543467
  · exact B543471
  · exact B543475
  · exact B543479
  · exact B543483
  · exact B543487
  · exact B543491
  · exact B543495
  · exact B543499
  · exact B543503
  · exact B543507
  · exact B543511
  · exact B543515
  · exact B543519
  · exact B543523
  · exact B543527
  · exact B543531
  · exact B543535
  · exact B543539
  · exact B543543
  · exact B543547
  · exact B543551
  · exact B543555
  · exact B543559
  · exact B543563
  · exact B543567
  · exact B543571
  · exact B543575
  · exact B543579
  · exact B543583
  · exact B543587
  · exact B543591
  · exact B543595
  · exact B543599
  · exact B543603
  · exact B543607
  · exact B543611
  · exact B543615
  · exact B543619
  · exact B543623
  · exact B543627
  · exact B543631
  · exact B543635
  · exact B543639
  · exact B543643
  · exact B543647
  · exact B543651
  · exact B543655
  · exact B543659
  · exact B543663
  · exact B543667
  · exact B543671
  · exact B543675
  · exact B543679
  · exact B543683
  · exact B543687
  · exact B543691
  · exact B543695
  · exact B543699
  · exact B543703
  · exact B543707
  · exact B543711
  · exact B543715
  · exact B543719
  · exact B543723
  · exact B543727
  · exact B543731
  · exact B543735
  · exact B543739
  · exact B543743
  · exact B543747
  · exact B543751
  · exact B543755
  · exact B543759
  · exact B543763
  · exact B543767
  · exact B543771
  · exact B543775
  · exact B543779
  · exact B543783
  · exact B543787
  · exact B543791
  · exact B543795
  · exact B543799
  · exact B543803
  · exact B543807
  · exact B543811
  · exact B543815
  · exact B543819
  · exact B543823
  · exact B543827
  · exact B543831
  · exact B543835
  · exact B543839
  · exact B543843
  · exact B543847
  · exact B543851
  · exact B543855
  · exact B543859
  · exact B543863
  · exact B543867
  · exact B543871
  · exact B543875
  · exact B543879
  · exact B543883
  · exact B543887
  · exact B543891
  · exact B543895
  · exact B543899
  · exact B543903
  · exact B543907
  · exact B543911
  · exact B543915
  · exact B543919
  · exact B543923
  · exact B543927
  · exact B543931
  · exact B543935
  · exact B543939
  · exact B543943
  · exact B543947
  · exact B543951
  · exact B543955
  · exact B543959
  · exact B543963
  · exact B543967
  · exact B543971
  · exact B543975
  · exact B543979
  · exact B543983
  · exact B543987
  · exact B543991
  · exact B543995
  · exact B543999
  · exact B544003
  · exact B544007
  · exact B544011
  · exact B544015
  · exact B544019
  · exact B544023
  · exact B544027
  · exact B544031
  · exact B544035
  · exact B544039
  · exact B544043
  · exact B544047
  · exact B544051
  · exact B544055
  · exact B544059
  · exact B544063
  · exact B544067
  · exact B544071
  · exact B544075
  · exact B544079
  · exact B544083
  · exact B544087
  · exact B544091
  · exact B544095
  · exact B544099
  · exact B544103
  · exact B544107
  · exact B544111
  · exact B544115
  · exact B544119
  · exact B544123
  · exact B544127
  · exact B544131
  · exact B544135
  · exact B544139
  · exact B544143
  · exact B544147
  · exact B544151
  · exact B544155
  · exact B544159
  · exact B544163
  · exact B544167
  · exact B544171
  · exact B544175
  · exact B544179
  · exact B544183
  · exact B544187
  · exact B544191
  · exact B544195
  · exact B544199
  · exact B544203
  · exact B544207
  · exact B544211
  · exact B544215
  · exact B544219
  · exact B544223
  · exact B544227
  · exact B544231
  · exact B544235
  · exact B544239
  · exact B544243
  · exact B544247
  · exact B544251
  · exact B544255
  · exact B544259
  · exact B544263
  · exact B544267
  · exact B544271
  · exact B544275
  · exact B544279
  · exact B544283
  · exact B544287
  · exact B544291
  · exact B544295
  · exact B544299
  · exact B544303
  · exact B544307
  · exact B544311
  · exact B544315
  · exact B544319
  · exact B544323
  · exact B544327
  · exact B544331
  · exact B544335
  · exact B544339
  · exact B544343
  · exact B544347
  · exact B544351
  · exact B544355
  · exact B544359
  · exact B544363
  · exact B544367
  · exact B544371
  · exact B544375
  · exact B544379
  · exact B544383
  · exact B544387
  · exact B544391
  · exact B544395
  · exact B544399
  · exact B544403
  · exact B544407
  · exact B544411
  · exact B544415
  · exact B544419
  · exact B544423
  · exact B544427
  · exact B544431
  · exact B544435
  · exact B544439
  · exact B544443
  · exact B544447
  · exact B544451
  · exact B544455
  · exact B544459
  · exact B544463
  · exact B544467
  · exact B544471
  · exact B544475
  · exact B544479
  · exact B544483
  · exact B544487
  · exact B544491
  · exact B544495
  · exact B544499
  · exact B544503
  · exact B544507
  · exact B544511
  · exact B544515
  · exact B544519
  · exact B544523
  · exact B544527
  · exact B544531
  · exact B544535
  · exact B544539
  · exact B544543
  · exact B544547
  · exact B544551
  · exact B544555
  · exact B544559
  · exact B544563
  · exact B544567
  · exact B544571
  · exact B544575
  · exact B544579
  · exact B544583
  · exact B544587
  · exact B544591
  · exact B544595
  · exact B544599
  · exact B544603
  · exact B544607
  · exact B544611
  · exact B544615
  · exact B544619
  · exact B544623
  · exact B544627
  · exact B544631
  · exact B544635
  · exact B544639
  · exact B544643
  · exact B544647
  · exact B544651
  · exact B544655
  · exact B544659
  · exact B544663
  · exact B544667
  · exact B544671
  · exact B544675
  · exact B544679
  · exact B544683
  · exact B544687
  · exact B544691
  · exact B544695
  · exact B544699
  · exact B544703
  · exact B544707
  · exact B544711
  · exact B544715
  · exact B544719
  · exact B544723
  · exact B544727
  · exact B544731
  · exact B544735
  · exact B544739
  · exact B544743
  · exact B544747
  · exact B544751
  · exact B544755
  · exact B544759
  · exact B544763
  · exact B544767
  · exact B544771
  · exact B544775
  · exact B544779
  · exact B544783
  · exact B544787
  · exact B544791
  · exact B544795
  · exact B544799
  · exact B544803
  · exact B544807
  · exact B544811
  · exact B544815
  · exact B544819
  · exact B544823
  · exact B544827
  · exact B544831
  · exact B544835
  · exact B544839
  · exact B544843
  · exact B544847
  · exact B544851
  · exact B544855
  · exact B544859
  · exact B544863
  · exact B544867
  · exact B544871
  · exact B544875
  · exact B544879
  · exact B544883
  · exact B544887
  · exact B544891
  · exact B544895
  · exact B544899
  · exact B544903
  · exact B544907
  · exact B544911
  · exact B544915
  · exact B544919
  · exact B544923
  · exact B544927
  · exact B544931
  · exact B544935
  · exact B544939
  · exact B544943
  · exact B544947
  · exact B544951
  · exact B544955
  · exact B544959
  · exact B544963
  · exact B544967
  · exact B544971
  · exact B544975
  · exact B544979
  · exact B544983
  · exact B544987
  · exact B544991
  · exact B544995
  · exact B544999
  · exact B545003
  · exact B545007
  · exact B545011
  · exact B545015
  · exact B545019
  · exact B545023
  · exact B545027
  · exact B545031
  · exact B545035
  · exact B545039
  · exact B545043
  · exact B545047
  · exact B545051
  · exact B545055
  · exact B545059
  · exact B545063
  · exact B545067
  · exact B545071
  · exact B545075
  · exact B545079
  · exact B545083
  · exact B545087
  · exact B545091
  · exact B545095
  · exact B545099
  · exact B545103
  · exact B545107
  · exact B545111
  · exact B545115
  · exact B545119
  · exact B545123
  · exact B545127
  · exact B545131
  · exact B545135
  · exact B545139
  · exact B545143
  · exact B545147
  · exact B545151
  · exact B545155
  · exact B545159
  · exact B545163
  · exact B545167
  · exact B545171
  · exact B545175
  · exact B545179
  · exact B545183
  · exact B545187
  · exact B545191
  · exact B545195
  · exact B545199
  · exact B545203
  · exact B545207
  · exact B545211
  · exact B545215
  · exact B545219
  · exact B545223
  · exact B545227
  · exact B545231
  · exact B545235
  · exact B545239
  · exact B545243
  · exact B545247
  · exact B545251
  · exact B545255
  · exact B545259
  · exact B545263
  · exact B545267
  · exact B545271
  · exact B545275
  · exact B545279
  · exact B545283
  · exact B545287
  · exact B545291
  · exact B545295
  · exact B545299
  · exact B545303
  · exact B545307
  · exact B545311
  · exact B545315
  · exact B545319
  · exact B545323
  · exact B545327
  · exact B545331
  · exact B545335
  · exact B545339
  · exact B545343
  · exact B545347
  · exact B545351
  · exact B545355
  · exact B545359
  · exact B545363
  · exact B545367
  · exact B545371
  · exact B545375
  · exact B545379
  · exact B545383
  · exact B545387
  · exact B545391
  · exact B545395
  · exact B545399
  · exact B545403
  · exact B545407
  · exact B545411
  · exact B545415
  · exact B545419
  · exact B545423
  · exact B545427
  · exact B545431
  · exact B545435
  · exact B545439
  · exact B545443
  · exact B545447
  · exact B545451
  · exact B545455
  · exact B545459
  · exact B545463
  · exact B545467
  · exact B545471
  · exact B545475
  · exact B545479
  · exact B545483
  · exact B545487
  · exact B545491
  · exact B545495
  · exact B545499
  · exact B545503
  · exact B545507
  · exact B545511
  · exact B545515
  · exact B545519
  · exact B545523
  · exact B545527
  · exact B545531
  · exact B545535
  · exact B545539
  · exact B545543
  · exact B545547
  · exact B545551
  · exact B545555
  · exact B545559
  · exact B545563
  · exact B545567
  · exact B545571
  · exact B545575
  · exact B545579
  · exact B545583
  · exact B545587
  · exact B545591
  · exact B545595
  · exact B545599
  · exact B545603

theorem C1 (j : ℕ) (h1 : 136401 ≤ j) (h2 : j ≤ 136700) : Blo 542804 (4 * j + 3) := by
  interval_cases j
  · exact B545607
  · exact B545611
  · exact B545615
  · exact B545619
  · exact B545623
  · exact B545627
  · exact B545631
  · exact B545635
  · exact B545639
  · exact B545643
  · exact B545647
  · exact B545651
  · exact B545655
  · exact B545659
  · exact B545663
  · exact B545667
  · exact B545671
  · exact B545675
  · exact B545679
  · exact B545683
  · exact B545687
  · exact B545691
  · exact B545695
  · exact B545699
  · exact B545703
  · exact B545707
  · exact B545711
  · exact B545715
  · exact B545719
  · exact B545723
  · exact B545727
  · exact B545731
  · exact B545735
  · exact B545739
  · exact B545743
  · exact B545747
  · exact B545751
  · exact B545755
  · exact B545759
  · exact B545763
  · exact B545767
  · exact B545771
  · exact B545775
  · exact B545779
  · exact B545783
  · exact B545787
  · exact B545791
  · exact B545795
  · exact B545799
  · exact B545803
  · exact B545807
  · exact B545811
  · exact B545815
  · exact B545819
  · exact B545823
  · exact B545827
  · exact B545831
  · exact B545835
  · exact B545839
  · exact B545843
  · exact B545847
  · exact B545851
  · exact B545855
  · exact B545859
  · exact B545863
  · exact B545867
  · exact B545871
  · exact B545875
  · exact B545879
  · exact B545883
  · exact B545887
  · exact B545891
  · exact B545895
  · exact B545899
  · exact B545903
  · exact B545907
  · exact B545911
  · exact B545915
  · exact B545919
  · exact B545923
  · exact B545927
  · exact B545931
  · exact B545935
  · exact B545939
  · exact B545943
  · exact B545947
  · exact B545951
  · exact B545955
  · exact B545959
  · exact B545963
  · exact B545967
  · exact B545971
  · exact B545975
  · exact B545979
  · exact B545983
  · exact B545987
  · exact B545991
  · exact B545995
  · exact B545999
  · exact B546003
  · exact B546007
  · exact B546011
  · exact B546015
  · exact B546019
  · exact B546023
  · exact B546027
  · exact B546031
  · exact B546035
  · exact B546039
  · exact B546043
  · exact B546047
  · exact B546051
  · exact B546055
  · exact B546059
  · exact B546063
  · exact B546067
  · exact B546071
  · exact B546075
  · exact B546079
  · exact B546083
  · exact B546087
  · exact B546091
  · exact B546095
  · exact B546099
  · exact B546103
  · exact B546107
  · exact B546111
  · exact B546115
  · exact B546119
  · exact B546123
  · exact B546127
  · exact B546131
  · exact B546135
  · exact B546139
  · exact B546143
  · exact B546147
  · exact B546151
  · exact B546155
  · exact B546159
  · exact B546163
  · exact B546167
  · exact B546171
  · exact B546175
  · exact B546179
  · exact B546183
  · exact B546187
  · exact B546191
  · exact B546195
  · exact B546199
  · exact B546203
  · exact B546207
  · exact B546211
  · exact B546215
  · exact B546219
  · exact B546223
  · exact B546227
  · exact B546231
  · exact B546235
  · exact B546239
  · exact B546243
  · exact B546247
  · exact B546251
  · exact B546255
  · exact B546259
  · exact B546263
  · exact B546267
  · exact B546271
  · exact B546275
  · exact B546279
  · exact B546283
  · exact B546287
  · exact B546291
  · exact B546295
  · exact B546299
  · exact B546303
  · exact B546307
  · exact B546311
  · exact B546315
  · exact B546319
  · exact B546323
  · exact B546327
  · exact B546331
  · exact B546335
  · exact B546339
  · exact B546343
  · exact B546347
  · exact B546351
  · exact B546355
  · exact B546359
  · exact B546363
  · exact B546367
  · exact B546371
  · exact B546375
  · exact B546379
  · exact B546383
  · exact B546387
  · exact B546391
  · exact B546395
  · exact B546399
  · exact B546403
  · exact B546407
  · exact B546411
  · exact B546415
  · exact B546419
  · exact B546423
  · exact B546427
  · exact B546431
  · exact B546435
  · exact B546439
  · exact B546443
  · exact B546447
  · exact B546451
  · exact B546455
  · exact B546459
  · exact B546463
  · exact B546467
  · exact B546471
  · exact B546475
  · exact B546479
  · exact B546483
  · exact B546487
  · exact B546491
  · exact B546495
  · exact B546499
  · exact B546503
  · exact B546507
  · exact B546511
  · exact B546515
  · exact B546519
  · exact B546523
  · exact B546527
  · exact B546531
  · exact B546535
  · exact B546539
  · exact B546543
  · exact B546547
  · exact B546551
  · exact B546555
  · exact B546559
  · exact B546563
  · exact B546567
  · exact B546571
  · exact B546575
  · exact B546579
  · exact B546583
  · exact B546587
  · exact B546591
  · exact B546595
  · exact B546599
  · exact B546603
  · exact B546607
  · exact B546611
  · exact B546615
  · exact B546619
  · exact B546623
  · exact B546627
  · exact B546631
  · exact B546635
  · exact B546639
  · exact B546643
  · exact B546647
  · exact B546651
  · exact B546655
  · exact B546659
  · exact B546663
  · exact B546667
  · exact B546671
  · exact B546675
  · exact B546679
  · exact B546683
  · exact B546687
  · exact B546691
  · exact B546695
  · exact B546699
  · exact B546703
  · exact B546707
  · exact B546711
  · exact B546715
  · exact B546719
  · exact B546723
  · exact B546727
  · exact B546731
  · exact B546735
  · exact B546739
  · exact B546743
  · exact B546747
  · exact B546751
  · exact B546755
  · exact B546759
  · exact B546763
  · exact B546767
  · exact B546771
  · exact B546775
  · exact B546779
  · exact B546783
  · exact B546787
  · exact B546791
  · exact B546795
  · exact B546799
  · exact B546803

theorem solution (m : ℕ) (hlo : 542804 ≤ m) (hhi : m ≤ 546804) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 135701 ≤ j := by omega
    have hj2 : j ≤ 136700 := by omega
    have hb : Blo 542804 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 136401 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
