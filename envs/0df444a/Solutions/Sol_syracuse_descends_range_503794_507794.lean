-- Prove2me | solution 1 for syracuse_descends_range_503794_507794
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:15.34592+00:00
-- url     : https://prove2.me/submissions/cf0208e0-c5b6-4ee6-bd55-175092eb20b2

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


theorem B1277957 : Blo 503794 1277957 := bbase (se 4 (by rfl) ⟨119808, by rfl⟩ : syracuseStep 1277957 = 239617) (by norm_num)
theorem B852005 : Blo 503794 852005 := bbase (se 4 (by rfl) ⟨79875, by rfl⟩ : syracuseStep 852005 = 159751) (by norm_num)
theorem B1081421 : Blo 503794 1081421 := bbase (se 3 (by rfl) ⟨202766, by rfl⟩ : syracuseStep 1081421 = 405533) (by norm_num)
theorem B852133 : Blo 503794 852133 := bbase (se 4 (by rfl) ⟨79887, by rfl⟩ : syracuseStep 852133 = 159775) (by norm_num)
theorem B1310957 : Blo 503794 1310957 := bbase (se 3 (by rfl) ⟨245804, by rfl⟩ : syracuseStep 1310957 = 491609) (by norm_num)
theorem B852221 : Blo 503794 852221 := bbase (se 3 (by rfl) ⟨159791, by rfl⟩ : syracuseStep 852221 = 319583) (by norm_num)
theorem B1442053 : Blo 503794 1442053 := bbase (se 4 (by rfl) ⟨135192, by rfl⟩ : syracuseStep 1442053 = 270385) (by norm_num)
theorem B2556197 : Blo 503794 2556197 := bbase (se 4 (by rfl) ⟨239643, by rfl⟩ : syracuseStep 2556197 = 479287) (by norm_num)
theorem B1081669 : Blo 503794 1081669 := bbase (se 4 (by rfl) ⟨101406, by rfl⟩ : syracuseStep 1081669 = 202813) (by norm_num)
theorem B1278301 : Blo 503794 1278301 := bbase (se 3 (by rfl) ⟨239681, by rfl⟩ : syracuseStep 1278301 = 479363) (by norm_num)
theorem B1704293 : Blo 503794 1704293 := bbase (se 4 (by rfl) ⟨159777, by rfl⟩ : syracuseStep 1704293 = 319555) (by norm_num)
theorem B852349 : Blo 503794 852349 := bbase (se 3 (by rfl) ⟨159815, by rfl⟩ : syracuseStep 852349 = 319631) (by norm_num)
theorem B1278413 : Blo 503794 1278413 := bbase (se 3 (by rfl) ⟨239702, by rfl⟩ : syracuseStep 1278413 = 479405) (by norm_num)
theorem B852437 : Blo 503794 852437 := bbase (se 7 (by rfl) ⟨9989, by rfl⟩ : syracuseStep 852437 = 19979) (by norm_num)
theorem B819677 : Blo 503794 819677 := bbase (se 3 (by rfl) ⟨153689, by rfl⟩ : syracuseStep 819677 = 307379) (by norm_num)
theorem B2884085 : Blo 503794 2884085 := bbase (se 5 (by rfl) ⟨135191, by rfl⟩ : syracuseStep 2884085 = 270383) (by norm_num)
theorem B721477 : Blo 503794 721477 := bbase (se 4 (by rfl) ⟨67638, by rfl⟩ : syracuseStep 721477 = 135277) (by norm_num)
theorem B852565 : Blo 503794 852565 := bbase (se 8 (by rfl) ⟨4995, by rfl⟩ : syracuseStep 852565 = 9991) (by norm_num)
theorem B21955157 : Blo 503794 21955157 := bbase (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) (by norm_num)
theorem B1278605 : Blo 503794 1278605 := bbase (se 3 (by rfl) ⟨239738, by rfl⟩ : syracuseStep 1278605 = 479477) (by norm_num)
theorem B852653 : Blo 503794 852653 := bbase (se 3 (by rfl) ⟨159872, by rfl⟩ : syracuseStep 852653 = 319745) (by norm_num)
theorem B3637973 : Blo 503794 3637973 := bbase (se 7 (by rfl) ⟨42632, by rfl⟩ : syracuseStep 3637973 = 85265) (by norm_num)
theorem B1704725 : Blo 503794 1704725 := bbase (se 6 (by rfl) ⟨39954, by rfl⟩ : syracuseStep 1704725 = 79909) (by norm_num)
theorem B852781 : Blo 503794 852781 := bbase (se 3 (by rfl) ⟨159896, by rfl⟩ : syracuseStep 852781 = 319793) (by norm_num)
theorem B1082173 : Blo 503794 1082173 := bbase (se 3 (by rfl) ⟨202907, by rfl⟩ : syracuseStep 1082173 = 405815) (by norm_num)
theorem B2196341 : Blo 503794 2196341 := bbase (se 5 (by rfl) ⟨102953, by rfl⟩ : syracuseStep 2196341 = 205907) (by norm_num)
theorem B852869 : Blo 503794 852869 := bbase (se 4 (by rfl) ⟨79956, by rfl⟩ : syracuseStep 852869 = 159913) (by norm_num)
theorem B721813 : Blo 503794 721813 := bbase (se 6 (by rfl) ⟨16917, by rfl⟩ : syracuseStep 721813 = 33835) (by norm_num)
theorem B1278949 : Blo 503794 1278949 := bbase (se 4 (by rfl) ⟨119901, by rfl⟩ : syracuseStep 1278949 = 239803) (by norm_num)
theorem B852997 : Blo 503794 852997 := bbase (se 4 (by rfl) ⟨79968, by rfl⟩ : syracuseStep 852997 = 159937) (by norm_num)
theorem B1279061 : Blo 503794 1279061 := bbase (se 8 (by rfl) ⟨7494, by rfl⟩ : syracuseStep 1279061 = 14989) (by norm_num)
theorem B853085 : Blo 503794 853085 := bbase (se 3 (by rfl) ⟨159953, by rfl⟩ : syracuseStep 853085 = 319907) (by norm_num)
theorem B722029 : Blo 503794 722029 := bbase (se 3 (by rfl) ⟨135380, by rfl⟩ : syracuseStep 722029 = 270761) (by norm_num)
theorem B1705157 : Blo 503794 1705157 := bbase (se 4 (by rfl) ⟨159858, by rfl⟩ : syracuseStep 1705157 = 319717) (by norm_num)
theorem B853213 : Blo 503794 853213 := bbase (se 3 (by rfl) ⟨159977, by rfl⟩ : syracuseStep 853213 = 319955) (by norm_num)
theorem B1279253 : Blo 503794 1279253 := bbase (se 6 (by rfl) ⟨29982, by rfl⟩ : syracuseStep 1279253 = 59965) (by norm_num)
theorem B853301 : Blo 503794 853301 := bbase (se 5 (by rfl) ⟨39998, by rfl⟩ : syracuseStep 853301 = 79997) (by norm_num)
theorem B656785 : Blo 503794 656785 := bbase (se 2 (by rfl) ⟨246294, by rfl⟩ : syracuseStep 656785 = 492589) (by norm_num)
theorem B853429 : Blo 503794 853429 := bbase (se 5 (by rfl) ⟨40004, by rfl⟩ : syracuseStep 853429 = 80009) (by norm_num)
theorem B722405 : Blo 503794 722405 := bbase (se 4 (by rfl) ⟨67725, by rfl⟩ : syracuseStep 722405 = 135451) (by norm_num)
theorem B853517 : Blo 503794 853517 := bbase (se 3 (by rfl) ⟨160034, by rfl⟩ : syracuseStep 853517 = 320069) (by norm_num)
theorem B2557493 : Blo 503794 2557493 := bbase (se 5 (by rfl) ⟨119882, by rfl⟩ : syracuseStep 2557493 = 239765) (by norm_num)
theorem B1279597 : Blo 503794 1279597 := bbase (se 3 (by rfl) ⟨239924, by rfl⟩ : syracuseStep 1279597 = 479849) (by norm_num)
theorem B1705589 : Blo 503794 1705589 := bbase (se 5 (by rfl) ⟨79949, by rfl⟩ : syracuseStep 1705589 = 159899) (by norm_num)
theorem B853645 : Blo 503794 853645 := bbase (se 3 (by rfl) ⟨160058, by rfl⟩ : syracuseStep 853645 = 320117) (by norm_num)
theorem B1083061 : Blo 503794 1083061 := bbase (se 5 (by rfl) ⟨50768, by rfl⟩ : syracuseStep 1083061 = 101537) (by norm_num)
theorem B820925 : Blo 503794 820925 := bbase (se 3 (by rfl) ⟨153923, by rfl⟩ : syracuseStep 820925 = 307847) (by norm_num)
theorem B1279709 : Blo 503794 1279709 := bbase (se 3 (by rfl) ⟨239945, by rfl⟩ : syracuseStep 1279709 = 479891) (by norm_num)
theorem B853733 : Blo 503794 853733 := bbase (se 4 (by rfl) ⟨80037, by rfl⟩ : syracuseStep 853733 = 160075) (by norm_num)
theorem B1443557 : Blo 503794 1443557 := bbase (se 4 (by rfl) ⟨135333, by rfl⟩ : syracuseStep 1443557 = 270667) (by norm_num)
theorem B4327253 : Blo 503794 4327253 := bbase (se 9 (by rfl) ⟨12677, by rfl⟩ : syracuseStep 4327253 = 25355) (by norm_num)
theorem B853861 : Blo 503794 853861 := bbase (se 4 (by rfl) ⟨80049, by rfl⟩ : syracuseStep 853861 = 160099) (by norm_num)
theorem B1279901 : Blo 503794 1279901 := bbase (se 3 (by rfl) ⟨239981, by rfl⟩ : syracuseStep 1279901 = 479963) (by norm_num)
theorem B853949 : Blo 503794 853949 := bbase (se 3 (by rfl) ⟨160115, by rfl⟩ : syracuseStep 853949 = 320231) (by norm_num)
theorem B755693 : Blo 503794 755693 := bbase (se 3 (by rfl) ⟨141692, by rfl⟩ : syracuseStep 755693 = 283385) (by norm_num)
theorem B755717 : Blo 503794 755717 := bbase (se 4 (by rfl) ⟨70848, by rfl⟩ : syracuseStep 755717 = 141697) (by norm_num)
theorem B755741 : Blo 503794 755741 := bbase (se 3 (by rfl) ⟨141701, by rfl⟩ : syracuseStep 755741 = 283403) (by norm_num)
theorem B1706021 : Blo 503794 1706021 := bbase (se 4 (by rfl) ⟨159939, by rfl⟩ : syracuseStep 1706021 = 319879) (by norm_num)
theorem B755765 : Blo 503794 755765 := bbase (se 5 (by rfl) ⟨35426, by rfl⟩ : syracuseStep 755765 = 70853) (by norm_num)
theorem B854077 : Blo 503794 854077 := bbase (se 3 (by rfl) ⟨160139, by rfl⟩ : syracuseStep 854077 = 320279) (by norm_num)
theorem B755789 : Blo 503794 755789 := bbase (se 3 (by rfl) ⟨141710, by rfl⟩ : syracuseStep 755789 = 283421) (by norm_num)
theorem B755813 : Blo 503794 755813 := bbase (se 4 (by rfl) ⟨70857, by rfl⟩ : syracuseStep 755813 = 141715) (by norm_num)
theorem B755837 : Blo 503794 755837 := bbase (se 3 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 755837 = 283439) (by norm_num)
theorem B755861 : Blo 503794 755861 := bbase (se 6 (by rfl) ⟨17715, by rfl⟩ : syracuseStep 755861 = 35431) (by norm_num)
theorem B854165 : Blo 503794 854165 := bbase (se 6 (by rfl) ⟨20019, by rfl⟩ : syracuseStep 854165 = 40039) (by norm_num)
theorem B1083557 : Blo 503794 1083557 := bbase (se 4 (by rfl) ⟨101583, by rfl⟩ : syracuseStep 1083557 = 203167) (by norm_num)
theorem B755885 : Blo 503794 755885 := bbase (se 3 (by rfl) ⟨141728, by rfl⟩ : syracuseStep 755885 = 283457) (by norm_num)
theorem B755909 : Blo 503794 755909 := bbase (se 4 (by rfl) ⟨70866, by rfl⟩ : syracuseStep 755909 = 141733) (by norm_num)
theorem B755933 : Blo 503794 755933 := bbase (se 3 (by rfl) ⟨141737, by rfl⟩ : syracuseStep 755933 = 283475) (by norm_num)
theorem B755957 : Blo 503794 755957 := bbase (se 5 (by rfl) ⟨35435, by rfl⟩ : syracuseStep 755957 = 70871) (by norm_num)
theorem B1280245 : Blo 503794 1280245 := bbase (se 5 (by rfl) ⟨60011, by rfl⟩ : syracuseStep 1280245 = 120023) (by norm_num)
theorem B755981 : Blo 503794 755981 := bbase (se 3 (by rfl) ⟨141746, by rfl⟩ : syracuseStep 755981 = 283493) (by norm_num)
theorem B854293 : Blo 503794 854293 := bbase (se 6 (by rfl) ⟨20022, by rfl⟩ : syracuseStep 854293 = 40045) (by norm_num)
theorem B756005 : Blo 503794 756005 := bbase (se 4 (by rfl) ⟨70875, by rfl⟩ : syracuseStep 756005 = 141751) (by norm_num)
theorem B756029 : Blo 503794 756029 := bbase (se 3 (by rfl) ⟨141755, by rfl⟩ : syracuseStep 756029 = 283511) (by norm_num)
theorem B756053 : Blo 503794 756053 := bbase (se 10 (by rfl) ⟨1107, by rfl⟩ : syracuseStep 756053 = 2215) (by norm_num)
theorem B1280357 : Blo 503794 1280357 := bbase (se 4 (by rfl) ⟨120033, by rfl⟩ : syracuseStep 1280357 = 240067) (by norm_num)
theorem B756077 : Blo 503794 756077 := bbase (se 3 (by rfl) ⟨141764, by rfl⟩ : syracuseStep 756077 = 283529) (by norm_num)
theorem B854381 : Blo 503794 854381 := bbase (se 3 (by rfl) ⟨160196, by rfl⟩ : syracuseStep 854381 = 320393) (by norm_num)
theorem B756101 : Blo 503794 756101 := bbase (se 4 (by rfl) ⟨70884, by rfl⟩ : syracuseStep 756101 = 141769) (by norm_num)
theorem B756125 : Blo 503794 756125 := bbase (se 3 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 756125 = 283547) (by norm_num)
theorem B756149 : Blo 503794 756149 := bbase (se 5 (by rfl) ⟨35444, by rfl⟩ : syracuseStep 756149 = 70889) (by norm_num)
theorem B756173 : Blo 503794 756173 := bbase (se 3 (by rfl) ⟨141782, by rfl⟩ : syracuseStep 756173 = 283565) (by norm_num)
theorem B1706453 : Blo 503794 1706453 := bbase (se 7 (by rfl) ⟨19997, by rfl⟩ : syracuseStep 1706453 = 39995) (by norm_num)
theorem B756197 : Blo 503794 756197 := bbase (se 4 (by rfl) ⟨70893, by rfl⟩ : syracuseStep 756197 = 141787) (by norm_num)
theorem B854509 : Blo 503794 854509 := bbase (se 3 (by rfl) ⟨160220, by rfl⟩ : syracuseStep 854509 = 320441) (by norm_num)
theorem B756221 : Blo 503794 756221 := bbase (se 3 (by rfl) ⟨141791, by rfl⟩ : syracuseStep 756221 = 283583) (by norm_num)
theorem B756245 : Blo 503794 756245 := bbase (se 6 (by rfl) ⟨17724, by rfl⟩ : syracuseStep 756245 = 35449) (by norm_num)
theorem B1280549 : Blo 503794 1280549 := bbase (se 4 (by rfl) ⟨120051, by rfl⟩ : syracuseStep 1280549 = 240103) (by norm_num)
theorem B756269 : Blo 503794 756269 := bbase (se 3 (by rfl) ⟨141800, by rfl⟩ : syracuseStep 756269 = 283601) (by norm_num)
theorem B756293 : Blo 503794 756293 := bbase (se 4 (by rfl) ⟨70902, by rfl⟩ : syracuseStep 756293 = 141805) (by norm_num)
theorem B854597 : Blo 503794 854597 := bbase (se 4 (by rfl) ⟨80118, by rfl⟩ : syracuseStep 854597 = 160237) (by norm_num)
theorem B756317 : Blo 503794 756317 := bbase (se 3 (by rfl) ⟨141809, by rfl⟩ : syracuseStep 756317 = 283619) (by norm_num)
theorem B756341 : Blo 503794 756341 := bbase (se 5 (by rfl) ⟨35453, by rfl⟩ : syracuseStep 756341 = 70907) (by norm_num)
theorem B2427509 : Blo 503794 2427509 := bbase (se 5 (by rfl) ⟨113789, by rfl⟩ : syracuseStep 2427509 = 227579) (by norm_num)
theorem B756365 : Blo 503794 756365 := bbase (se 3 (by rfl) ⟨141818, by rfl⟩ : syracuseStep 756365 = 283637) (by norm_num)
theorem B2886293 : Blo 503794 2886293 := bbase (se 6 (by rfl) ⟨67647, by rfl⟩ : syracuseStep 2886293 = 135295) (by norm_num)
theorem B756389 : Blo 503794 756389 := bbase (se 4 (by rfl) ⟨70911, by rfl⟩ : syracuseStep 756389 = 141823) (by norm_num)
theorem B756413 : Blo 503794 756413 := bbase (se 3 (by rfl) ⟨141827, by rfl⟩ : syracuseStep 756413 = 283655) (by norm_num)
theorem B854725 : Blo 503794 854725 := bbase (se 4 (by rfl) ⟨80130, by rfl⟩ : syracuseStep 854725 = 160261) (by norm_num)
theorem B756437 : Blo 503794 756437 := bbase (se 7 (by rfl) ⟨8864, by rfl⟩ : syracuseStep 756437 = 17729) (by norm_num)
theorem B756461 : Blo 503794 756461 := bbase (se 3 (by rfl) ⟨141836, by rfl⟩ : syracuseStep 756461 = 283673) (by norm_num)
theorem B756485 : Blo 503794 756485 := bbase (se 4 (by rfl) ⟨70920, by rfl⟩ : syracuseStep 756485 = 141841) (by norm_num)
theorem B2165525 : Blo 503794 2165525 := bbase (se 6 (by rfl) ⟨50754, by rfl⟩ : syracuseStep 2165525 = 101509) (by norm_num)
theorem B756509 : Blo 503794 756509 := bbase (se 3 (by rfl) ⟨141845, by rfl⟩ : syracuseStep 756509 = 283691) (by norm_num)
theorem B854813 : Blo 503794 854813 := bbase (se 3 (by rfl) ⟨160277, by rfl⟩ : syracuseStep 854813 = 320555) (by norm_num)
theorem B756533 : Blo 503794 756533 := bbase (se 5 (by rfl) ⟨35462, by rfl⟩ : syracuseStep 756533 = 70925) (by norm_num)
theorem B2558789 : Blo 503794 2558789 := bbase (se 4 (by rfl) ⟨239886, by rfl⟩ : syracuseStep 2558789 = 479773) (by norm_num)
theorem B756557 : Blo 503794 756557 := bbase (se 3 (by rfl) ⟨141854, by rfl⟩ : syracuseStep 756557 = 283709) (by norm_num)
theorem B756581 : Blo 503794 756581 := bbase (se 4 (by rfl) ⟨70929, by rfl⟩ : syracuseStep 756581 = 141859) (by norm_num)
theorem B756605 : Blo 503794 756605 := bbase (se 3 (by rfl) ⟨141863, by rfl⟩ : syracuseStep 756605 = 283727) (by norm_num)
theorem B1280893 : Blo 503794 1280893 := bbase (se 3 (by rfl) ⟨240167, by rfl⟩ : syracuseStep 1280893 = 480335) (by norm_num)
theorem B1706885 : Blo 503794 1706885 := bbase (se 4 (by rfl) ⟨160020, by rfl⟩ : syracuseStep 1706885 = 320041) (by norm_num)
theorem B756629 : Blo 503794 756629 := bbase (se 6 (by rfl) ⟨17733, by rfl⟩ : syracuseStep 756629 = 35467) (by norm_num)
theorem B854941 : Blo 503794 854941 := bbase (se 3 (by rfl) ⟨160301, by rfl⟩ : syracuseStep 854941 = 320603) (by norm_num)
theorem B756653 : Blo 503794 756653 := bbase (se 3 (by rfl) ⟨141872, by rfl⟩ : syracuseStep 756653 = 283745) (by norm_num)
theorem B756677 : Blo 503794 756677 := bbase (se 4 (by rfl) ⟨70938, by rfl⟩ : syracuseStep 756677 = 141877) (by norm_num)
theorem B756701 : Blo 503794 756701 := bbase (se 3 (by rfl) ⟨141881, by rfl⟩ : syracuseStep 756701 = 283763) (by norm_num)
theorem B1281005 : Blo 503794 1281005 := bbase (se 3 (by rfl) ⟨240188, by rfl⟩ : syracuseStep 1281005 = 480377) (by norm_num)
theorem B756725 : Blo 503794 756725 := bbase (se 5 (by rfl) ⟨35471, by rfl⟩ : syracuseStep 756725 = 70943) (by norm_num)
theorem B855029 : Blo 503794 855029 := bbase (se 5 (by rfl) ⟨40079, by rfl⟩ : syracuseStep 855029 = 80159) (by norm_num)
theorem B756749 : Blo 503794 756749 := bbase (se 3 (by rfl) ⟨141890, by rfl⟩ : syracuseStep 756749 = 283781) (by norm_num)
theorem B1084445 : Blo 503794 1084445 := bbase (se 3 (by rfl) ⟨203333, by rfl⟩ : syracuseStep 1084445 = 406667) (by norm_num)
theorem B756773 : Blo 503794 756773 := bbase (se 4 (by rfl) ⟨70947, by rfl⟩ : syracuseStep 756773 = 141895) (by norm_num)
theorem B756797 : Blo 503794 756797 := bbase (se 3 (by rfl) ⟨141899, by rfl⟩ : syracuseStep 756797 = 283799) (by norm_num)
theorem B2591813 : Blo 503794 2591813 := bbase (se 4 (by rfl) ⟨242982, by rfl⟩ : syracuseStep 2591813 = 485965) (by norm_num)
theorem B756821 : Blo 503794 756821 := bbase (se 8 (by rfl) ⟨4434, by rfl⟩ : syracuseStep 756821 = 8869) (by norm_num)
theorem B756845 : Blo 503794 756845 := bbase (se 3 (by rfl) ⟨141908, by rfl⟩ : syracuseStep 756845 = 283817) (by norm_num)
theorem B855157 : Blo 503794 855157 := bbase (se 5 (by rfl) ⟨40085, by rfl⟩ : syracuseStep 855157 = 80171) (by norm_num)
theorem B756869 : Blo 503794 756869 := bbase (se 4 (by rfl) ⟨70956, by rfl⟩ : syracuseStep 756869 = 141913) (by norm_num)
theorem B756893 : Blo 503794 756893 := bbase (se 3 (by rfl) ⟨141917, by rfl⟩ : syracuseStep 756893 = 283835) (by norm_num)
theorem B1281197 : Blo 503794 1281197 := bbase (se 3 (by rfl) ⟨240224, by rfl⟩ : syracuseStep 1281197 = 480449) (by norm_num)
theorem B756917 : Blo 503794 756917 := bbase (se 5 (by rfl) ⟨35480, by rfl⟩ : syracuseStep 756917 = 70961) (by norm_num)
theorem B3247285 : Blo 503794 3247285 := bbase (se 5 (by rfl) ⟨152216, by rfl⟩ : syracuseStep 3247285 = 304433) (by norm_num)
theorem B756941 : Blo 503794 756941 := bbase (se 3 (by rfl) ⟨141926, by rfl⟩ : syracuseStep 756941 = 283853) (by norm_num)
theorem B855245 : Blo 503794 855245 := bbase (se 3 (by rfl) ⟨160358, by rfl⟩ : syracuseStep 855245 = 320717) (by norm_num)
theorem B756965 : Blo 503794 756965 := bbase (se 4 (by rfl) ⟨70965, by rfl⟩ : syracuseStep 756965 = 141931) (by norm_num)
theorem B1215733 : Blo 503794 1215733 := bbase (se 5 (by rfl) ⟨56987, by rfl⟩ : syracuseStep 1215733 = 113975) (by norm_num)
theorem B756989 : Blo 503794 756989 := bbase (se 3 (by rfl) ⟨141935, by rfl⟩ : syracuseStep 756989 = 283871) (by norm_num)
theorem B757013 : Blo 503794 757013 := bbase (se 6 (by rfl) ⟨17742, by rfl⟩ : syracuseStep 757013 = 35485) (by norm_num)
theorem B1445141 : Blo 503794 1445141 := bbase (se 6 (by rfl) ⟨33870, by rfl⟩ : syracuseStep 1445141 = 67741) (by norm_num)
theorem B757037 : Blo 503794 757037 := bbase (se 3 (by rfl) ⟨141944, by rfl⟩ : syracuseStep 757037 = 283889) (by norm_num)
theorem B1707317 : Blo 503794 1707317 := bbase (se 5 (by rfl) ⟨80030, by rfl⟩ : syracuseStep 1707317 = 160061) (by norm_num)
theorem B691517 : Blo 503794 691517 := bbase (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) (by norm_num)
theorem B757061 : Blo 503794 757061 := bbase (se 4 (by rfl) ⟨70974, by rfl⟩ : syracuseStep 757061 = 141949) (by norm_num)
theorem B855373 : Blo 503794 855373 := bbase (se 3 (by rfl) ⟨160382, by rfl⟩ : syracuseStep 855373 = 320765) (by norm_num)
theorem B757085 : Blo 503794 757085 := bbase (se 3 (by rfl) ⟨141953, by rfl⟩ : syracuseStep 757085 = 283907) (by norm_num)
theorem B757109 : Blo 503794 757109 := bbase (se 5 (by rfl) ⟨35489, by rfl⟩ : syracuseStep 757109 = 70979) (by norm_num)
theorem B757133 : Blo 503794 757133 := bbase (se 3 (by rfl) ⟨141962, by rfl⟩ : syracuseStep 757133 = 283925) (by norm_num)
theorem B757157 : Blo 503794 757157 := bbase (se 4 (by rfl) ⟨70983, by rfl⟩ : syracuseStep 757157 = 141967) (by norm_num)
theorem B855461 : Blo 503794 855461 := bbase (se 4 (by rfl) ⟨80199, by rfl⟩ : syracuseStep 855461 = 160399) (by norm_num)
theorem B757181 : Blo 503794 757181 := bbase (se 3 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 757181 = 283943) (by norm_num)
theorem B757205 : Blo 503794 757205 := bbase (se 7 (by rfl) ⟨8873, by rfl⟩ : syracuseStep 757205 = 17747) (by norm_num)
theorem B1641941 : Blo 503794 1641941 := bbase (se 7 (by rfl) ⟨19241, by rfl⟩ : syracuseStep 1641941 = 38483) (by norm_num)
theorem B1215965 : Blo 503794 1215965 := bbase (se 3 (by rfl) ⟨227993, by rfl⟩ : syracuseStep 1215965 = 455987) (by norm_num)
theorem B757229 : Blo 503794 757229 := bbase (se 3 (by rfl) ⟨141980, by rfl⟩ : syracuseStep 757229 = 283961) (by norm_num)
theorem B757253 : Blo 503794 757253 := bbase (se 4 (by rfl) ⟨70992, by rfl⟩ : syracuseStep 757253 = 141985) (by norm_num)
theorem B1281541 : Blo 503794 1281541 := bbase (se 4 (by rfl) ⟨120144, by rfl⟩ : syracuseStep 1281541 = 240289) (by norm_num)
theorem B757277 : Blo 503794 757277 := bbase (se 3 (by rfl) ⟨141989, by rfl⟩ : syracuseStep 757277 = 283979) (by norm_num)
theorem B855589 : Blo 503794 855589 := bbase (se 4 (by rfl) ⟨80211, by rfl⟩ : syracuseStep 855589 = 160423) (by norm_num)
theorem B757301 : Blo 503794 757301 := bbase (se 5 (by rfl) ⟨35498, by rfl⟩ : syracuseStep 757301 = 70997) (by norm_num)
theorem B1248821 : Blo 503794 1248821 := bbase (se 5 (by rfl) ⟨58538, by rfl⟩ : syracuseStep 1248821 = 117077) (by norm_num)
theorem B757325 : Blo 503794 757325 := bbase (se 3 (by rfl) ⟨141998, by rfl⟩ : syracuseStep 757325 = 283997) (by norm_num)
theorem B757349 : Blo 503794 757349 := bbase (se 4 (by rfl) ⟨71001, by rfl⟩ : syracuseStep 757349 = 142003) (by norm_num)
theorem B1216109 : Blo 503794 1216109 := bbase (se 3 (by rfl) ⟨228020, by rfl⟩ : syracuseStep 1216109 = 456041) (by norm_num)
theorem B1281653 : Blo 503794 1281653 := bbase (se 5 (by rfl) ⟨60077, by rfl⟩ : syracuseStep 1281653 = 120155) (by norm_num)
theorem B757373 : Blo 503794 757373 := bbase (se 3 (by rfl) ⟨142007, by rfl⟩ : syracuseStep 757373 = 284015) (by norm_num)
theorem B855677 : Blo 503794 855677 := bbase (se 3 (by rfl) ⟨160439, by rfl⟩ : syracuseStep 855677 = 320879) (by norm_num)
theorem B757397 : Blo 503794 757397 := bbase (se 6 (by rfl) ⟨17751, by rfl⟩ : syracuseStep 757397 = 35503) (by norm_num)
theorem B757421 : Blo 503794 757421 := bbase (se 3 (by rfl) ⟨142016, by rfl⟩ : syracuseStep 757421 = 284033) (by norm_num)
theorem B757445 : Blo 503794 757445 := bbase (se 4 (by rfl) ⟨71010, by rfl⟩ : syracuseStep 757445 = 142021) (by norm_num)
theorem B757469 : Blo 503794 757469 := bbase (se 3 (by rfl) ⟨142025, by rfl⟩ : syracuseStep 757469 = 284051) (by norm_num)
theorem B1707749 : Blo 503794 1707749 := bbase (se 4 (by rfl) ⟨160101, by rfl⟩ : syracuseStep 1707749 = 320203) (by norm_num)
theorem B757493 : Blo 503794 757493 := bbase (se 5 (by rfl) ⟨35507, by rfl⟩ : syracuseStep 757493 = 71015) (by norm_num)
theorem B855805 : Blo 503794 855805 := bbase (se 3 (by rfl) ⟨160463, by rfl⟩ : syracuseStep 855805 = 320927) (by norm_num)
theorem B2166533 : Blo 503794 2166533 := bbase (se 4 (by rfl) ⟨203112, by rfl⟩ : syracuseStep 2166533 = 406225) (by norm_num)
theorem B757517 : Blo 503794 757517 := bbase (se 3 (by rfl) ⟨142034, by rfl⟩ : syracuseStep 757517 = 284069) (by norm_num)
theorem B757541 : Blo 503794 757541 := bbase (se 4 (by rfl) ⟨71019, by rfl⟩ : syracuseStep 757541 = 142039) (by norm_num)
theorem B1281845 : Blo 503794 1281845 := bbase (se 5 (by rfl) ⟨60086, by rfl⟩ : syracuseStep 1281845 = 120173) (by norm_num)
theorem B757565 : Blo 503794 757565 := bbase (se 3 (by rfl) ⟨142043, by rfl⟩ : syracuseStep 757565 = 284087) (by norm_num)
theorem B986941 : Blo 503794 986941 := bbase (se 3 (by rfl) ⟨185051, by rfl⟩ : syracuseStep 986941 = 370103) (by norm_num)
theorem B757589 : Blo 503794 757589 := bbase (se 9 (by rfl) ⟨2219, by rfl⟩ : syracuseStep 757589 = 4439) (by norm_num)
theorem B855893 : Blo 503794 855893 := bbase (se 9 (by rfl) ⟨2507, by rfl⟩ : syracuseStep 855893 = 5015) (by norm_num)
theorem B1216349 : Blo 503794 1216349 := bbase (se 3 (by rfl) ⟨228065, by rfl⟩ : syracuseStep 1216349 = 456131) (by norm_num)
theorem B757613 : Blo 503794 757613 := bbase (se 3 (by rfl) ⟨142052, by rfl⟩ : syracuseStep 757613 = 284105) (by norm_num)
theorem B757637 : Blo 503794 757637 := bbase (se 4 (by rfl) ⟨71028, by rfl⟩ : syracuseStep 757637 = 142057) (by norm_num)
theorem B757661 : Blo 503794 757661 := bbase (se 3 (by rfl) ⟨142061, by rfl⟩ : syracuseStep 757661 = 284123) (by norm_num)
theorem B757685 : Blo 503794 757685 := bbase (se 5 (by rfl) ⟨35516, by rfl⟩ : syracuseStep 757685 = 71033) (by norm_num)
theorem B1445813 : Blo 503794 1445813 := bbase (se 5 (by rfl) ⟨67772, by rfl⟩ : syracuseStep 1445813 = 135545) (by norm_num)
theorem B757709 : Blo 503794 757709 := bbase (se 3 (by rfl) ⟨142070, by rfl⟩ : syracuseStep 757709 = 284141) (by norm_num)
theorem B692173 : Blo 503794 692173 := bbase (se 3 (by rfl) ⟨129782, by rfl⟩ : syracuseStep 692173 = 259565) (by norm_num)
theorem B856021 : Blo 503794 856021 := bbase (se 7 (by rfl) ⟨10031, by rfl⟩ : syracuseStep 856021 = 20063) (by norm_num)
theorem B757733 : Blo 503794 757733 := bbase (se 4 (by rfl) ⟨71037, by rfl⟩ : syracuseStep 757733 = 142075) (by norm_num)
theorem B3837941 : Blo 503794 3837941 := bbase (se 5 (by rfl) ⟨179903, by rfl⟩ : syracuseStep 3837941 = 359807) (by norm_num)
theorem B757757 : Blo 503794 757757 := bbase (se 3 (by rfl) ⟨142079, by rfl⟩ : syracuseStep 757757 = 284159) (by norm_num)
theorem B757781 : Blo 503794 757781 := bbase (se 6 (by rfl) ⟨17760, by rfl⟩ : syracuseStep 757781 = 35521) (by norm_num)
theorem B757805 : Blo 503794 757805 := bbase (se 3 (by rfl) ⟨142088, by rfl⟩ : syracuseStep 757805 = 284177) (by norm_num)
theorem B856109 : Blo 503794 856109 := bbase (se 3 (by rfl) ⟨160520, by rfl⟩ : syracuseStep 856109 = 321041) (by norm_num)
theorem B757829 : Blo 503794 757829 := bbase (se 4 (by rfl) ⟨71046, by rfl⟩ : syracuseStep 757829 = 142093) (by norm_num)
theorem B2560085 : Blo 503794 2560085 := bbase (se 8 (by rfl) ⟨15000, by rfl⟩ : syracuseStep 2560085 = 30001) (by norm_num)
theorem B757853 : Blo 503794 757853 := bbase (se 3 (by rfl) ⟨142097, by rfl⟩ : syracuseStep 757853 = 284195) (by norm_num)
theorem B757877 : Blo 503794 757877 := bbase (se 5 (by rfl) ⟨35525, by rfl⟩ : syracuseStep 757877 = 71051) (by norm_num)
theorem B757901 : Blo 503794 757901 := bbase (se 3 (by rfl) ⟨142106, by rfl⟩ : syracuseStep 757901 = 284213) (by norm_num)
theorem B1282189 : Blo 503794 1282189 := bbase (se 3 (by rfl) ⟨240410, by rfl⟩ : syracuseStep 1282189 = 480821) (by norm_num)
theorem B1708181 : Blo 503794 1708181 := bbase (se 6 (by rfl) ⟨40035, by rfl⟩ : syracuseStep 1708181 = 80071) (by norm_num)
theorem B757925 : Blo 503794 757925 := bbase (se 4 (by rfl) ⟨71055, by rfl⟩ : syracuseStep 757925 = 142111) (by norm_num)
theorem B856237 : Blo 503794 856237 := bbase (se 3 (by rfl) ⟨160544, by rfl⟩ : syracuseStep 856237 = 321089) (by norm_num)
theorem B757949 : Blo 503794 757949 := bbase (se 3 (by rfl) ⟨142115, by rfl⟩ : syracuseStep 757949 = 284231) (by norm_num)
theorem B757973 : Blo 503794 757973 := bbase (se 7 (by rfl) ⟨8882, by rfl⟩ : syracuseStep 757973 = 17765) (by norm_num)
theorem B757997 : Blo 503794 757997 := bbase (se 3 (by rfl) ⟨142124, by rfl⟩ : syracuseStep 757997 = 284249) (by norm_num)
theorem B1282301 : Blo 503794 1282301 := bbase (se 3 (by rfl) ⟨240431, by rfl⟩ : syracuseStep 1282301 = 480863) (by norm_num)
theorem B758021 : Blo 503794 758021 := bbase (se 4 (by rfl) ⟨71064, by rfl⟩ : syracuseStep 758021 = 142129) (by norm_num)
theorem B856325 : Blo 503794 856325 := bbase (se 4 (by rfl) ⟨80280, by rfl⟩ : syracuseStep 856325 = 160561) (by norm_num)
theorem B758045 : Blo 503794 758045 := bbase (se 3 (by rfl) ⟨142133, by rfl⟩ : syracuseStep 758045 = 284267) (by norm_num)
theorem B758069 : Blo 503794 758069 := bbase (se 5 (by rfl) ⟨35534, by rfl⟩ : syracuseStep 758069 = 71069) (by norm_num)
theorem B758093 : Blo 503794 758093 := bbase (se 3 (by rfl) ⟨142142, by rfl⟩ : syracuseStep 758093 = 284285) (by norm_num)
theorem B758117 : Blo 503794 758117 := bbase (se 4 (by rfl) ⟨71073, by rfl⟩ : syracuseStep 758117 = 142147) (by norm_num)
theorem B758141 : Blo 503794 758141 := bbase (se 3 (by rfl) ⟨142151, by rfl⟩ : syracuseStep 758141 = 284303) (by norm_num)
theorem B856453 : Blo 503794 856453 := bbase (se 4 (by rfl) ⟨80292, by rfl⟩ : syracuseStep 856453 = 160585) (by norm_num)
theorem B758165 : Blo 503794 758165 := bbase (se 6 (by rfl) ⟨17769, by rfl⟩ : syracuseStep 758165 = 35539) (by norm_num)
theorem B758189 : Blo 503794 758189 := bbase (se 3 (by rfl) ⟨142160, by rfl⟩ : syracuseStep 758189 = 284321) (by norm_num)
theorem B1282493 : Blo 503794 1282493 := bbase (se 3 (by rfl) ⟨240467, by rfl⟩ : syracuseStep 1282493 = 480935) (by norm_num)
theorem B758213 : Blo 503794 758213 := bbase (se 4 (by rfl) ⟨71082, by rfl⟩ : syracuseStep 758213 = 142165) (by norm_num)
theorem B758237 : Blo 503794 758237 := bbase (se 3 (by rfl) ⟨142169, by rfl⟩ : syracuseStep 758237 = 284339) (by norm_num)
theorem B856541 : Blo 503794 856541 := bbase (se 3 (by rfl) ⟨160601, by rfl⟩ : syracuseStep 856541 = 321203) (by norm_num)
theorem B758261 : Blo 503794 758261 := bbase (se 5 (by rfl) ⟨35543, by rfl⟩ : syracuseStep 758261 = 71087) (by norm_num)
theorem B758285 : Blo 503794 758285 := bbase (se 3 (by rfl) ⟨142178, by rfl⟩ : syracuseStep 758285 = 284357) (by norm_num)
theorem B758309 : Blo 503794 758309 := bbase (se 4 (by rfl) ⟨71091, by rfl⟩ : syracuseStep 758309 = 142183) (by norm_num)
theorem B758333 : Blo 503794 758333 := bbase (se 3 (by rfl) ⟨142187, by rfl⟩ : syracuseStep 758333 = 284375) (by norm_num)
theorem B1708613 : Blo 503794 1708613 := bbase (se 4 (by rfl) ⟨160182, by rfl⟩ : syracuseStep 1708613 = 320365) (by norm_num)
theorem B758357 : Blo 503794 758357 := bbase (se 8 (by rfl) ⟨4443, by rfl⟩ : syracuseStep 758357 = 8887) (by norm_num)
theorem B1151581 : Blo 503794 1151581 := bbase (se 3 (by rfl) ⟨215921, by rfl⟩ : syracuseStep 1151581 = 431843) (by norm_num)
theorem B1217117 : Blo 503794 1217117 := bbase (se 3 (by rfl) ⟨228209, by rfl⟩ : syracuseStep 1217117 = 456419) (by norm_num)
theorem B856669 : Blo 503794 856669 := bbase (se 3 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 856669 = 321251) (by norm_num)
theorem B758381 : Blo 503794 758381 := bbase (se 3 (by rfl) ⟨142196, by rfl⟩ : syracuseStep 758381 = 284393) (by norm_num)
theorem B758405 : Blo 503794 758405 := bbase (se 4 (by rfl) ⟨71100, by rfl⟩ : syracuseStep 758405 = 142201) (by norm_num)
theorem B758429 : Blo 503794 758429 := bbase (se 3 (by rfl) ⟨142205, by rfl⟩ : syracuseStep 758429 = 284411) (by norm_num)
theorem B758453 : Blo 503794 758453 := bbase (se 5 (by rfl) ⟨35552, by rfl⟩ : syracuseStep 758453 = 71105) (by norm_num)
theorem B856757 : Blo 503794 856757 := bbase (se 5 (by rfl) ⟨40160, by rfl⟩ : syracuseStep 856757 = 80321) (by norm_num)
theorem B758477 : Blo 503794 758477 := bbase (se 3 (by rfl) ⟨142214, by rfl⟩ : syracuseStep 758477 = 284429) (by norm_num)
theorem B2298581 : Blo 503794 2298581 := bbase (se 7 (by rfl) ⟨26936, by rfl⟩ : syracuseStep 2298581 = 53873) (by norm_num)
theorem B758501 : Blo 503794 758501 := bbase (se 4 (by rfl) ⟨71109, by rfl⟩ : syracuseStep 758501 = 142219) (by norm_num)
theorem B758525 : Blo 503794 758525 := bbase (se 3 (by rfl) ⟨142223, by rfl⟩ : syracuseStep 758525 = 284447) (by norm_num)
theorem B758549 : Blo 503794 758549 := bbase (se 6 (by rfl) ⟨17778, by rfl⟩ : syracuseStep 758549 = 35557) (by norm_num)
theorem B1282837 : Blo 503794 1282837 := bbase (se 6 (by rfl) ⟨30066, by rfl⟩ : syracuseStep 1282837 = 60133) (by norm_num)
theorem B758573 : Blo 503794 758573 := bbase (se 3 (by rfl) ⟨142232, by rfl⟩ : syracuseStep 758573 = 284465) (by norm_num)
theorem B856885 : Blo 503794 856885 := bbase (se 5 (by rfl) ⟨40166, by rfl⟩ : syracuseStep 856885 = 80333) (by norm_num)
theorem B758597 : Blo 503794 758597 := bbase (se 4 (by rfl) ⟨71118, by rfl⟩ : syracuseStep 758597 = 142237) (by norm_num)
theorem B758621 : Blo 503794 758621 := bbase (se 3 (by rfl) ⟨142241, by rfl⟩ : syracuseStep 758621 = 284483) (by norm_num)
theorem B758645 : Blo 503794 758645 := bbase (se 5 (by rfl) ⟨35561, by rfl⟩ : syracuseStep 758645 = 71123) (by norm_num)
theorem B1282949 : Blo 503794 1282949 := bbase (se 4 (by rfl) ⟨120276, by rfl⟩ : syracuseStep 1282949 = 240553) (by norm_num)
theorem B758669 : Blo 503794 758669 := bbase (se 3 (by rfl) ⟨142250, by rfl⟩ : syracuseStep 758669 = 284501) (by norm_num)
theorem B758693 : Blo 503794 758693 := bbase (se 4 (by rfl) ⟨71127, by rfl⟩ : syracuseStep 758693 = 142255) (by norm_num)
theorem B758717 : Blo 503794 758717 := bbase (se 3 (by rfl) ⟨142259, by rfl⟩ : syracuseStep 758717 = 284519) (by norm_num)
theorem B758741 : Blo 503794 758741 := bbase (se 7 (by rfl) ⟨8891, by rfl⟩ : syracuseStep 758741 = 17783) (by norm_num)
theorem B758765 : Blo 503794 758765 := bbase (se 3 (by rfl) ⟨142268, by rfl⟩ : syracuseStep 758765 = 284537) (by norm_num)
theorem B1709045 : Blo 503794 1709045 := bbase (se 5 (by rfl) ⟨80111, by rfl⟩ : syracuseStep 1709045 = 160223) (by norm_num)
theorem B758789 : Blo 503794 758789 := bbase (se 4 (by rfl) ⟨71136, by rfl⟩ : syracuseStep 758789 = 142273) (by norm_num)
theorem B758813 : Blo 503794 758813 := bbase (se 3 (by rfl) ⟨142277, by rfl⟩ : syracuseStep 758813 = 284555) (by norm_num)
theorem B758837 : Blo 503794 758837 := bbase (se 5 (by rfl) ⟨35570, by rfl⟩ : syracuseStep 758837 = 71141) (by norm_num)
theorem B1283141 : Blo 503794 1283141 := bbase (se 4 (by rfl) ⟨120294, by rfl⟩ : syracuseStep 1283141 = 240589) (by norm_num)
theorem B758861 : Blo 503794 758861 := bbase (se 3 (by rfl) ⟨142286, by rfl⟩ : syracuseStep 758861 = 284573) (by norm_num)
theorem B758885 : Blo 503794 758885 := bbase (se 4 (by rfl) ⟨71145, by rfl⟩ : syracuseStep 758885 = 142291) (by norm_num)
theorem B758909 : Blo 503794 758909 := bbase (se 3 (by rfl) ⟨142295, by rfl⟩ : syracuseStep 758909 = 284591) (by norm_num)
theorem B758933 : Blo 503794 758933 := bbase (se 6 (by rfl) ⟨17787, by rfl⟩ : syracuseStep 758933 = 35575) (by norm_num)
theorem B758957 : Blo 503794 758957 := bbase (se 3 (by rfl) ⟨142304, by rfl⟩ : syracuseStep 758957 = 284609) (by norm_num)
theorem B758981 : Blo 503794 758981 := bbase (se 4 (by rfl) ⟨71154, by rfl⟩ : syracuseStep 758981 = 142309) (by norm_num)
theorem B759005 : Blo 503794 759005 := bbase (se 3 (by rfl) ⟨142313, by rfl⟩ : syracuseStep 759005 = 284627) (by norm_num)
theorem B759029 : Blo 503794 759029 := bbase (se 5 (by rfl) ⟨35579, by rfl⟩ : syracuseStep 759029 = 71159) (by norm_num)
theorem B759053 : Blo 503794 759053 := bbase (se 3 (by rfl) ⟨142322, by rfl⟩ : syracuseStep 759053 = 284645) (by norm_num)
theorem B759077 : Blo 503794 759077 := bbase (se 4 (by rfl) ⟨71163, by rfl⟩ : syracuseStep 759077 = 142327) (by norm_num)
theorem B759101 : Blo 503794 759101 := bbase (se 3 (by rfl) ⟨142331, by rfl⟩ : syracuseStep 759101 = 284663) (by norm_num)
theorem B759125 : Blo 503794 759125 := bbase (se 14 (by rfl) ⟨69, by rfl⟩ : syracuseStep 759125 = 139) (by norm_num)
theorem B2561381 : Blo 503794 2561381 := bbase (se 4 (by rfl) ⟨240129, by rfl⟩ : syracuseStep 2561381 = 480259) (by norm_num)
theorem B759149 : Blo 503794 759149 := bbase (se 3 (by rfl) ⟨142340, by rfl⟩ : syracuseStep 759149 = 284681) (by norm_num)
theorem B759173 : Blo 503794 759173 := bbase (se 4 (by rfl) ⟨71172, by rfl⟩ : syracuseStep 759173 = 142345) (by norm_num)
theorem B759197 : Blo 503794 759197 := bbase (se 3 (by rfl) ⟨142349, by rfl⟩ : syracuseStep 759197 = 284699) (by norm_num)
theorem B1283485 : Blo 503794 1283485 := bbase (se 3 (by rfl) ⟨240653, by rfl⟩ : syracuseStep 1283485 = 481307) (by norm_num)
theorem B1709477 : Blo 503794 1709477 := bbase (se 4 (by rfl) ⟨160263, by rfl⟩ : syracuseStep 1709477 = 320527) (by norm_num)
theorem B759221 : Blo 503794 759221 := bbase (se 5 (by rfl) ⟨35588, by rfl⟩ : syracuseStep 759221 = 71177) (by norm_num)
theorem B759245 : Blo 503794 759245 := bbase (se 3 (by rfl) ⟨142358, by rfl⟩ : syracuseStep 759245 = 284717) (by norm_num)
theorem B759269 : Blo 503794 759269 := bbase (se 4 (by rfl) ⟨71181, by rfl⟩ : syracuseStep 759269 = 142363) (by norm_num)
theorem B2168309 : Blo 503794 2168309 := bbase (se 5 (by rfl) ⟨101639, by rfl⟩ : syracuseStep 2168309 = 203279) (by norm_num)
theorem B759293 : Blo 503794 759293 := bbase (se 3 (by rfl) ⟨142367, by rfl⟩ : syracuseStep 759293 = 284735) (by norm_num)
theorem B1283597 : Blo 503794 1283597 := bbase (se 3 (by rfl) ⟨240674, by rfl⟩ : syracuseStep 1283597 = 481349) (by norm_num)
theorem B759317 : Blo 503794 759317 := bbase (se 6 (by rfl) ⟨17796, by rfl⟩ : syracuseStep 759317 = 35593) (by norm_num)
theorem B759341 : Blo 503794 759341 := bbase (se 3 (by rfl) ⟨142376, by rfl⟩ : syracuseStep 759341 = 284753) (by norm_num)
theorem B759365 : Blo 503794 759365 := bbase (se 4 (by rfl) ⟨71190, by rfl⟩ : syracuseStep 759365 = 142381) (by norm_num)
theorem B759389 : Blo 503794 759389 := bbase (se 3 (by rfl) ⟨142385, by rfl⟩ : syracuseStep 759389 = 284771) (by norm_num)
theorem B759413 : Blo 503794 759413 := bbase (se 5 (by rfl) ⟨35597, by rfl⟩ : syracuseStep 759413 = 71195) (by norm_num)
theorem B759437 : Blo 503794 759437 := bbase (se 3 (by rfl) ⟨142394, by rfl⟩ : syracuseStep 759437 = 284789) (by norm_num)
theorem B759461 : Blo 503794 759461 := bbase (se 4 (by rfl) ⟨71199, by rfl⟩ : syracuseStep 759461 = 142399) (by norm_num)
theorem B759485 : Blo 503794 759485 := bbase (se 3 (by rfl) ⟨142403, by rfl⟩ : syracuseStep 759485 = 284807) (by norm_num)
theorem B1283789 : Blo 503794 1283789 := bbase (se 3 (by rfl) ⟨240710, by rfl⟩ : syracuseStep 1283789 = 481421) (by norm_num)
theorem B759509 : Blo 503794 759509 := bbase (se 7 (by rfl) ⟨8900, by rfl⟩ : syracuseStep 759509 = 17801) (by norm_num)
theorem B759533 : Blo 503794 759533 := bbase (se 3 (by rfl) ⟨142412, by rfl⟩ : syracuseStep 759533 = 284825) (by norm_num)
theorem B759557 : Blo 503794 759557 := bbase (se 4 (by rfl) ⟨71208, by rfl⟩ : syracuseStep 759557 = 142417) (by norm_num)
theorem B759581 : Blo 503794 759581 := bbase (se 3 (by rfl) ⟨142421, by rfl⟩ : syracuseStep 759581 = 284843) (by norm_num)
theorem B759605 : Blo 503794 759605 := bbase (se 5 (by rfl) ⟨35606, by rfl⟩ : syracuseStep 759605 = 71213) (by norm_num)
theorem B759629 : Blo 503794 759629 := bbase (se 3 (by rfl) ⟨142430, by rfl⟩ : syracuseStep 759629 = 284861) (by norm_num)
theorem B1709909 : Blo 503794 1709909 := bbase (se 9 (by rfl) ⟨5009, by rfl⟩ : syracuseStep 1709909 = 10019) (by norm_num)
theorem B759653 : Blo 503794 759653 := bbase (se 4 (by rfl) ⟨71217, by rfl⟩ : syracuseStep 759653 = 142435) (by norm_num)
theorem B759677 : Blo 503794 759677 := bbase (se 3 (by rfl) ⟨142439, by rfl⟩ : syracuseStep 759677 = 284879) (by norm_num)
theorem B759701 : Blo 503794 759701 := bbase (se 6 (by rfl) ⟨17805, by rfl⟩ : syracuseStep 759701 = 35611) (by norm_num)
theorem B759725 : Blo 503794 759725 := bbase (se 3 (by rfl) ⟨142448, by rfl⟩ : syracuseStep 759725 = 284897) (by norm_num)
theorem B1218493 : Blo 503794 1218493 := bbase (se 3 (by rfl) ⟨228467, by rfl⟩ : syracuseStep 1218493 = 456935) (by norm_num)
theorem B759749 : Blo 503794 759749 := bbase (se 4 (by rfl) ⟨71226, by rfl⟩ : syracuseStep 759749 = 142453) (by norm_num)
theorem B759773 : Blo 503794 759773 := bbase (se 3 (by rfl) ⟨142457, by rfl⟩ : syracuseStep 759773 = 284915) (by norm_num)
theorem B759797 : Blo 503794 759797 := bbase (se 5 (by rfl) ⟨35615, by rfl⟩ : syracuseStep 759797 = 71231) (by norm_num)
theorem B759821 : Blo 503794 759821 := bbase (se 3 (by rfl) ⟨142466, by rfl⟩ : syracuseStep 759821 = 284933) (by norm_num)
theorem B759845 : Blo 503794 759845 := bbase (se 4 (by rfl) ⟨71235, by rfl⟩ : syracuseStep 759845 = 142471) (by norm_num)
theorem B1284133 : Blo 503794 1284133 := bbase (se 4 (by rfl) ⟨120387, by rfl⟩ : syracuseStep 1284133 = 240775) (by norm_num)
theorem B759869 : Blo 503794 759869 := bbase (se 3 (by rfl) ⟨142475, by rfl⟩ : syracuseStep 759869 = 284951) (by norm_num)
theorem B759893 : Blo 503794 759893 := bbase (se 8 (by rfl) ⟨4452, by rfl⟩ : syracuseStep 759893 = 8905) (by norm_num)
theorem B759917 : Blo 503794 759917 := bbase (se 3 (by rfl) ⟨142484, by rfl⟩ : syracuseStep 759917 = 284969) (by norm_num)
theorem B759941 : Blo 503794 759941 := bbase (se 4 (by rfl) ⟨71244, by rfl⟩ : syracuseStep 759941 = 142489) (by norm_num)
theorem B1284245 : Blo 503794 1284245 := bbase (se 6 (by rfl) ⟨30099, by rfl⟩ : syracuseStep 1284245 = 60199) (by norm_num)
theorem B759965 : Blo 503794 759965 := bbase (se 3 (by rfl) ⟨142493, by rfl⟩ : syracuseStep 759965 = 284987) (by norm_num)
theorem B4102325 : Blo 503794 4102325 := bbase (se 5 (by rfl) ⟨192296, by rfl⟩ : syracuseStep 4102325 = 384593) (by norm_num)
theorem B759989 : Blo 503794 759989 := bbase (se 5 (by rfl) ⟨35624, by rfl⟩ : syracuseStep 759989 = 71249) (by norm_num)
theorem B760013 : Blo 503794 760013 := bbase (se 3 (by rfl) ⟨142502, by rfl⟩ : syracuseStep 760013 = 285005) (by norm_num)
theorem B760037 : Blo 503794 760037 := bbase (se 4 (by rfl) ⟨71253, by rfl⟩ : syracuseStep 760037 = 142507) (by norm_num)
theorem B760061 : Blo 503794 760061 := bbase (se 3 (by rfl) ⟨142511, by rfl⟩ : syracuseStep 760061 = 285023) (by norm_num)
theorem B1710341 : Blo 503794 1710341 := bbase (se 4 (by rfl) ⟨160344, by rfl⟩ : syracuseStep 1710341 = 320689) (by norm_num)
theorem B760085 : Blo 503794 760085 := bbase (se 6 (by rfl) ⟨17814, by rfl⟩ : syracuseStep 760085 = 35629) (by norm_num)
theorem B760109 : Blo 503794 760109 := bbase (se 3 (by rfl) ⟨142520, by rfl⟩ : syracuseStep 760109 = 285041) (by norm_num)
theorem B760133 : Blo 503794 760133 := bbase (se 4 (by rfl) ⟨71262, by rfl⟩ : syracuseStep 760133 = 142525) (by norm_num)
theorem B989525 : Blo 503794 989525 := bbase (se 10 (by rfl) ⟨1449, by rfl⟩ : syracuseStep 989525 = 2899) (by norm_num)
theorem B1284437 : Blo 503794 1284437 := bbase (se 10 (by rfl) ⟨1881, by rfl⟩ : syracuseStep 1284437 = 3763) (by norm_num)
theorem B760157 : Blo 503794 760157 := bbase (se 3 (by rfl) ⟨142529, by rfl⟩ : syracuseStep 760157 = 285059) (by norm_num)
theorem B760181 : Blo 503794 760181 := bbase (se 5 (by rfl) ⟨35633, by rfl⟩ : syracuseStep 760181 = 71267) (by norm_num)
theorem B760205 : Blo 503794 760205 := bbase (se 3 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 760205 = 285077) (by norm_num)
theorem B760229 : Blo 503794 760229 := bbase (se 4 (by rfl) ⟨71271, by rfl⟩ : syracuseStep 760229 = 142543) (by norm_num)
theorem B760253 : Blo 503794 760253 := bbase (se 3 (by rfl) ⟨142547, by rfl⟩ : syracuseStep 760253 = 285095) (by norm_num)
theorem B760277 : Blo 503794 760277 := bbase (se 7 (by rfl) ⟨8909, by rfl⟩ : syracuseStep 760277 = 17819) (by norm_num)
theorem B760301 : Blo 503794 760301 := bbase (se 3 (by rfl) ⟨142556, by rfl⟩ : syracuseStep 760301 = 285113) (by norm_num)
theorem B760325 : Blo 503794 760325 := bbase (se 4 (by rfl) ⟨71280, by rfl⟩ : syracuseStep 760325 = 142561) (by norm_num)
theorem B760349 : Blo 503794 760349 := bbase (se 3 (by rfl) ⟨142565, by rfl⟩ : syracuseStep 760349 = 285131) (by norm_num)
theorem B1055285 : Blo 503794 1055285 := bbase (se 5 (by rfl) ⟨49466, by rfl⟩ : syracuseStep 1055285 = 98933) (by norm_num)
theorem B760373 : Blo 503794 760373 := bbase (se 5 (by rfl) ⟨35642, by rfl⟩ : syracuseStep 760373 = 71285) (by norm_num)
theorem B760397 : Blo 503794 760397 := bbase (se 3 (by rfl) ⟨142574, by rfl⟩ : syracuseStep 760397 = 285149) (by norm_num)
theorem B760421 : Blo 503794 760421 := bbase (se 4 (by rfl) ⟨71289, by rfl⟩ : syracuseStep 760421 = 142579) (by norm_num)
theorem B2562677 : Blo 503794 2562677 := bbase (se 5 (by rfl) ⟨120125, by rfl⟩ : syracuseStep 2562677 = 240251) (by norm_num)
theorem B760445 : Blo 503794 760445 := bbase (se 3 (by rfl) ⟨142583, by rfl⟩ : syracuseStep 760445 = 285167) (by norm_num)
theorem B760469 : Blo 503794 760469 := bbase (se 6 (by rfl) ⟨17823, by rfl⟩ : syracuseStep 760469 = 35647) (by norm_num)
theorem B760493 : Blo 503794 760493 := bbase (se 3 (by rfl) ⟨142592, by rfl⟩ : syracuseStep 760493 = 285185) (by norm_num)
theorem B1284781 : Blo 503794 1284781 := bbase (se 3 (by rfl) ⟨240896, by rfl⟩ : syracuseStep 1284781 = 481793) (by norm_num)
theorem B957109 : Blo 503794 957109 := bbase (se 5 (by rfl) ⟨44864, by rfl⟩ : syracuseStep 957109 = 89729) (by norm_num)
theorem B1710773 : Blo 503794 1710773 := bbase (se 5 (by rfl) ⟨80192, by rfl⟩ : syracuseStep 1710773 = 160385) (by norm_num)
theorem B760517 : Blo 503794 760517 := bbase (se 4 (by rfl) ⟨71298, by rfl⟩ : syracuseStep 760517 = 142597) (by norm_num)
theorem B760541 : Blo 503794 760541 := bbase (se 3 (by rfl) ⟨142601, by rfl⟩ : syracuseStep 760541 = 285203) (by norm_num)
theorem B760565 : Blo 503794 760565 := bbase (se 5 (by rfl) ⟨35651, by rfl⟩ : syracuseStep 760565 = 71303) (by norm_num)
theorem B760589 : Blo 503794 760589 := bbase (se 3 (by rfl) ⟨142610, by rfl⟩ : syracuseStep 760589 = 285221) (by norm_num)
theorem B1284893 : Blo 503794 1284893 := bbase (se 3 (by rfl) ⟨240917, by rfl⟩ : syracuseStep 1284893 = 481835) (by norm_num)
theorem B760613 : Blo 503794 760613 := bbase (se 4 (by rfl) ⟨71307, by rfl⟩ : syracuseStep 760613 = 142615) (by norm_num)
theorem B760637 : Blo 503794 760637 := bbase (se 3 (by rfl) ⟨142619, by rfl⟩ : syracuseStep 760637 = 285239) (by norm_num)
theorem B957253 : Blo 503794 957253 := bbase (se 4 (by rfl) ⟨89742, by rfl⟩ : syracuseStep 957253 = 179485) (by norm_num)
theorem B760661 : Blo 503794 760661 := bbase (se 9 (by rfl) ⟨2228, by rfl⟩ : syracuseStep 760661 = 4457) (by norm_num)
theorem B760685 : Blo 503794 760685 := bbase (se 3 (by rfl) ⟨142628, by rfl⟩ : syracuseStep 760685 = 285257) (by norm_num)
theorem B760709 : Blo 503794 760709 := bbase (se 4 (by rfl) ⟨71316, by rfl⟩ : syracuseStep 760709 = 142633) (by norm_num)
theorem B760733 : Blo 503794 760733 := bbase (se 3 (by rfl) ⟨142637, by rfl⟩ : syracuseStep 760733 = 285275) (by norm_num)
theorem B760757 : Blo 503794 760757 := bbase (se 5 (by rfl) ⟨35660, by rfl⟩ : syracuseStep 760757 = 71321) (by norm_num)
theorem B760781 : Blo 503794 760781 := bbase (se 3 (by rfl) ⟨142646, by rfl⟩ : syracuseStep 760781 = 285293) (by norm_num)
theorem B1285085 : Blo 503794 1285085 := bbase (se 3 (by rfl) ⟨240953, by rfl⟩ : syracuseStep 1285085 = 481907) (by norm_num)
theorem B957413 : Blo 503794 957413 := bbase (se 4 (by rfl) ⟨89757, by rfl⟩ : syracuseStep 957413 = 179515) (by norm_num)
theorem B760805 : Blo 503794 760805 := bbase (se 4 (by rfl) ⟨71325, by rfl⟩ : syracuseStep 760805 = 142651) (by norm_num)
theorem B760829 : Blo 503794 760829 := bbase (se 3 (by rfl) ⟨142655, by rfl⟩ : syracuseStep 760829 = 285311) (by norm_num)
theorem B760853 : Blo 503794 760853 := bbase (se 6 (by rfl) ⟨17832, by rfl⟩ : syracuseStep 760853 = 35665) (by norm_num)
theorem B760877 : Blo 503794 760877 := bbase (se 3 (by rfl) ⟨142664, by rfl⟩ : syracuseStep 760877 = 285329) (by norm_num)
theorem B760901 : Blo 503794 760901 := bbase (se 4 (by rfl) ⟨71334, by rfl⟩ : syracuseStep 760901 = 142669) (by norm_num)
theorem B3251285 : Blo 503794 3251285 := bbase (se 8 (by rfl) ⟨19050, by rfl⟩ : syracuseStep 3251285 = 38101) (by norm_num)
theorem B760925 : Blo 503794 760925 := bbase (se 3 (by rfl) ⟨142673, by rfl⟩ : syracuseStep 760925 = 285347) (by norm_num)
theorem B1711205 : Blo 503794 1711205 := bbase (se 4 (by rfl) ⟨160425, by rfl⟩ : syracuseStep 1711205 = 320851) (by norm_num)
theorem B1219693 : Blo 503794 1219693 := bbase (se 3 (by rfl) ⟨228692, by rfl⟩ : syracuseStep 1219693 = 457385) (by norm_num)
theorem B957557 : Blo 503794 957557 := bbase (se 5 (by rfl) ⟨44885, by rfl⟩ : syracuseStep 957557 = 89771) (by norm_num)
theorem B760949 : Blo 503794 760949 := bbase (se 5 (by rfl) ⟨35669, by rfl⟩ : syracuseStep 760949 = 71339) (by norm_num)
theorem B760973 : Blo 503794 760973 := bbase (se 3 (by rfl) ⟨142682, by rfl⟩ : syracuseStep 760973 = 285365) (by norm_num)
theorem B760997 : Blo 503794 760997 := bbase (se 4 (by rfl) ⟨71343, by rfl⟩ : syracuseStep 760997 = 142687) (by norm_num)
theorem B1875125 : Blo 503794 1875125 := bbase (se 5 (by rfl) ⟨87896, by rfl⟩ : syracuseStep 1875125 = 175793) (by norm_num)
theorem B761021 : Blo 503794 761021 := bbase (se 3 (by rfl) ⟨142691, by rfl⟩ : syracuseStep 761021 = 285383) (by norm_num)
theorem B761045 : Blo 503794 761045 := bbase (se 7 (by rfl) ⟨8918, by rfl⟩ : syracuseStep 761045 = 17837) (by norm_num)
theorem B761069 : Blo 503794 761069 := bbase (se 3 (by rfl) ⟨142700, by rfl⟩ : syracuseStep 761069 = 285401) (by norm_num)
theorem B761093 : Blo 503794 761093 := bbase (se 4 (by rfl) ⟨71352, by rfl⟩ : syracuseStep 761093 = 142705) (by norm_num)
theorem B1187093 : Blo 503794 1187093 := bbase (se 6 (by rfl) ⟨27822, by rfl⟩ : syracuseStep 1187093 = 55645) (by norm_num)
theorem B761117 : Blo 503794 761117 := bbase (se 3 (by rfl) ⟨142709, by rfl⟩ : syracuseStep 761117 = 285419) (by norm_num)
theorem B761141 : Blo 503794 761141 := bbase (se 5 (by rfl) ⟨35678, by rfl⟩ : syracuseStep 761141 = 71357) (by norm_num)
theorem B761165 : Blo 503794 761165 := bbase (se 3 (by rfl) ⟨142718, by rfl⟩ : syracuseStep 761165 = 285437) (by norm_num)
theorem B761189 : Blo 503794 761189 := bbase (se 4 (by rfl) ⟨71361, by rfl⟩ : syracuseStep 761189 = 142723) (by norm_num)
theorem B761213 : Blo 503794 761213 := bbase (se 3 (by rfl) ⟨142727, by rfl⟩ : syracuseStep 761213 = 285455) (by norm_num)
theorem B2432389 : Blo 503794 2432389 := bbase (se 4 (by rfl) ⟨228036, by rfl⟩ : syracuseStep 2432389 = 456073) (by norm_num)
theorem B957845 : Blo 503794 957845 := bbase (se 6 (by rfl) ⟨22449, by rfl⟩ : syracuseStep 957845 = 44899) (by norm_num)
theorem B761237 : Blo 503794 761237 := bbase (se 6 (by rfl) ⟨17841, by rfl⟩ : syracuseStep 761237 = 35683) (by norm_num)
theorem B761261 : Blo 503794 761261 := bbase (se 3 (by rfl) ⟨142736, by rfl⟩ : syracuseStep 761261 = 285473) (by norm_num)
theorem B761285 : Blo 503794 761285 := bbase (se 4 (by rfl) ⟨71370, by rfl⟩ : syracuseStep 761285 = 142741) (by norm_num)
theorem B761309 : Blo 503794 761309 := bbase (se 3 (by rfl) ⟨142745, by rfl⟩ : syracuseStep 761309 = 285491) (by norm_num)
theorem B761333 : Blo 503794 761333 := bbase (se 5 (by rfl) ⟨35687, by rfl⟩ : syracuseStep 761333 = 71375) (by norm_num)
theorem B3907061 : Blo 503794 3907061 := bbase (se 5 (by rfl) ⟨183143, by rfl⟩ : syracuseStep 3907061 = 366287) (by norm_num)
theorem B761357 : Blo 503794 761357 := bbase (se 3 (by rfl) ⟨142754, by rfl⟩ : syracuseStep 761357 = 285509) (by norm_num)
theorem B1711637 : Blo 503794 1711637 := bbase (se 6 (by rfl) ⟨40116, by rfl⟩ : syracuseStep 1711637 = 80233) (by norm_num)
theorem B761381 : Blo 503794 761381 := bbase (se 4 (by rfl) ⟨71379, by rfl⟩ : syracuseStep 761381 = 142759) (by norm_num)
theorem B957997 : Blo 503794 957997 := bbase (se 3 (by rfl) ⟨179624, by rfl⟩ : syracuseStep 957997 = 359249) (by norm_num)
theorem B761405 : Blo 503794 761405 := bbase (se 3 (by rfl) ⟨142763, by rfl⟩ : syracuseStep 761405 = 285527) (by norm_num)
theorem B761429 : Blo 503794 761429 := bbase (se 8 (by rfl) ⟨4461, by rfl⟩ : syracuseStep 761429 = 8923) (by norm_num)
theorem B761453 : Blo 503794 761453 := bbase (se 3 (by rfl) ⟨142772, by rfl⟩ : syracuseStep 761453 = 285545) (by norm_num)
theorem B761477 : Blo 503794 761477 := bbase (se 4 (by rfl) ⟨71388, by rfl⟩ : syracuseStep 761477 = 142777) (by norm_num)
theorem B761501 : Blo 503794 761501 := bbase (se 3 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 761501 = 285563) (by norm_num)
theorem B761525 : Blo 503794 761525 := bbase (se 5 (by rfl) ⟨35696, by rfl⟩ : syracuseStep 761525 = 71393) (by norm_num)
theorem B761549 : Blo 503794 761549 := bbase (se 3 (by rfl) ⟨142790, by rfl⟩ : syracuseStep 761549 = 285581) (by norm_num)
theorem B761573 : Blo 503794 761573 := bbase (se 4 (by rfl) ⟨71397, by rfl⟩ : syracuseStep 761573 = 142795) (by norm_num)
theorem B761597 : Blo 503794 761597 := bbase (se 3 (by rfl) ⟨142799, by rfl⟩ : syracuseStep 761597 = 285599) (by norm_num)
theorem B1154837 : Blo 503794 1154837 := bbase (se 6 (by rfl) ⟨27066, by rfl⟩ : syracuseStep 1154837 = 54133) (by norm_num)
theorem B761621 : Blo 503794 761621 := bbase (se 6 (by rfl) ⟨17850, by rfl⟩ : syracuseStep 761621 = 35701) (by norm_num)
theorem B761645 : Blo 503794 761645 := bbase (se 3 (by rfl) ⟨142808, by rfl⟩ : syracuseStep 761645 = 285617) (by norm_num)
theorem B761669 : Blo 503794 761669 := bbase (se 4 (by rfl) ⟨71406, by rfl⟩ : syracuseStep 761669 = 142813) (by norm_num)
theorem B958301 : Blo 503794 958301 := bbase (se 3 (by rfl) ⟨179681, by rfl⟩ : syracuseStep 958301 = 359363) (by norm_num)
theorem B2563973 : Blo 503794 2563973 := bbase (se 4 (by rfl) ⟨240372, by rfl⟩ : syracuseStep 2563973 = 480745) (by norm_num)
theorem B1712069 : Blo 503794 1712069 := bbase (se 4 (by rfl) ⟨160506, by rfl⟩ : syracuseStep 1712069 = 321013) (by norm_num)
theorem B39297109 : Blo 503794 39297109 := bbase (se 8 (by rfl) ⟨230256, by rfl⟩ : syracuseStep 39297109 = 460513) (by norm_num)
theorem B2728181 : Blo 503794 2728181 := bbase (se 5 (by rfl) ⟨127883, by rfl⟩ : syracuseStep 2728181 = 255767) (by norm_num)
theorem B1155421 : Blo 503794 1155421 := bbase (se 3 (by rfl) ⟨216641, by rfl⟩ : syracuseStep 1155421 = 433283) (by norm_num)
theorem B1712501 : Blo 503794 1712501 := bbase (se 5 (by rfl) ⟨80273, by rfl⟩ : syracuseStep 1712501 = 160547) (by norm_num)
theorem B5743061 : Blo 503794 5743061 := bbase (se 7 (by rfl) ⟨67301, by rfl⟩ : syracuseStep 5743061 = 134603) (by norm_num)
theorem B959053 : Blo 503794 959053 := bbase (se 3 (by rfl) ⟨179822, by rfl⟩ : syracuseStep 959053 = 359645) (by norm_num)
theorem B12264149 : Blo 503794 12264149 := bbase (se 7 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 12264149 = 287441) (by norm_num)
theorem B959197 : Blo 503794 959197 := bbase (se 3 (by rfl) ⟨179849, by rfl⟩ : syracuseStep 959197 = 359699) (by norm_num)
theorem B1712933 : Blo 503794 1712933 := bbase (se 4 (by rfl) ⟨160587, by rfl⟩ : syracuseStep 1712933 = 321175) (by norm_num)
theorem B959357 : Blo 503794 959357 := bbase (se 3 (by rfl) ⟨179879, by rfl⟩ : syracuseStep 959357 = 359759) (by norm_num)
theorem B1614725 : Blo 503794 1614725 := bbase (se 4 (by rfl) ⟨151380, by rfl⟩ : syracuseStep 1614725 = 302761) (by norm_num)
theorem B1024949 : Blo 503794 1024949 := bbase (se 5 (by rfl) ⟨48044, by rfl⟩ : syracuseStep 1024949 = 96089) (by norm_num)
theorem B959501 : Blo 503794 959501 := bbase (se 3 (by rfl) ⟨179906, by rfl⟩ : syracuseStep 959501 = 359813) (by norm_num)
theorem B1614917 : Blo 503794 1614917 := bbase (se 4 (by rfl) ⟨151398, by rfl⟩ : syracuseStep 1614917 = 302797) (by norm_num)
theorem B1156189 : Blo 503794 1156189 := bbase (se 3 (by rfl) ⟨216785, by rfl⟩ : syracuseStep 1156189 = 433571) (by norm_num)
theorem B1090685 : Blo 503794 1090685 := bbase (se 3 (by rfl) ⟨204503, by rfl⟩ : syracuseStep 1090685 = 409007) (by norm_num)
theorem B2565269 : Blo 503794 2565269 := bbase (se 6 (by rfl) ⟨60123, by rfl⟩ : syracuseStep 2565269 = 120247) (by norm_num)
theorem B1713365 : Blo 503794 1713365 := bbase (se 7 (by rfl) ⟨20078, by rfl⟩ : syracuseStep 1713365 = 40157) (by norm_num)
theorem B4695317 : Blo 503794 4695317 := bbase (se 6 (by rfl) ⟨110046, by rfl⟩ : syracuseStep 4695317 = 220093) (by norm_num)
theorem B959789 : Blo 503794 959789 := bbase (se 3 (by rfl) ⟨179960, by rfl⟩ : syracuseStep 959789 = 359921) (by norm_num)
theorem B1025453 : Blo 503794 1025453 := bbase (se 3 (by rfl) ⟨192272, by rfl⟩ : syracuseStep 1025453 = 384545) (by norm_num)
theorem B959941 : Blo 503794 959941 := bbase (se 4 (by rfl) ⟨89994, by rfl⟩ : syracuseStep 959941 = 179989) (by norm_num)
theorem B1156589 : Blo 503794 1156589 := bbase (se 3 (by rfl) ⟨216860, by rfl⟩ : syracuseStep 1156589 = 433721) (by norm_num)
theorem B566797 : Blo 503794 566797 := bbase (se 3 (by rfl) ⟨106274, by rfl⟩ : syracuseStep 566797 = 212549) (by norm_num)
theorem B566833 : Blo 503794 566833 := bbase (se 2 (by rfl) ⟨212562, by rfl⟩ : syracuseStep 566833 = 425125) (by norm_num)
theorem B566869 : Blo 503794 566869 := bbase (se 8 (by rfl) ⟨3321, by rfl⟩ : syracuseStep 566869 = 6643) (by norm_num)
theorem B566905 : Blo 503794 566905 := bbase (se 2 (by rfl) ⟨212589, by rfl⟩ : syracuseStep 566905 = 425179) (by norm_num)
theorem B1713797 : Blo 503794 1713797 := bbase (se 4 (by rfl) ⟨160668, by rfl⟩ : syracuseStep 1713797 = 321337) (by norm_num)
theorem B566941 : Blo 503794 566941 := bbase (se 3 (by rfl) ⟨106301, by rfl⟩ : syracuseStep 566941 = 212603) (by norm_num)
theorem B566977 : Blo 503794 566977 := bbase (se 2 (by rfl) ⟨212616, by rfl⟩ : syracuseStep 566977 = 425233) (by norm_num)
theorem B567013 : Blo 503794 567013 := bbase (se 4 (by rfl) ⟨53157, by rfl⟩ : syracuseStep 567013 = 106315) (by norm_num)
theorem B960245 : Blo 503794 960245 := bbase (se 5 (by rfl) ⟨45011, by rfl⟩ : syracuseStep 960245 = 90023) (by norm_num)
theorem B567049 : Blo 503794 567049 := bbase (se 2 (by rfl) ⟨212643, by rfl⟩ : syracuseStep 567049 = 425287) (by norm_num)
theorem B567085 : Blo 503794 567085 := bbase (se 3 (by rfl) ⟨106328, by rfl⟩ : syracuseStep 567085 = 212657) (by norm_num)
theorem B567121 : Blo 503794 567121 := bbase (se 2 (by rfl) ⟨212670, by rfl⟩ : syracuseStep 567121 = 425341) (by norm_num)
theorem B567157 : Blo 503794 567157 := bbase (se 5 (by rfl) ⟨26585, by rfl⟩ : syracuseStep 567157 = 53171) (by norm_num)
theorem B567193 : Blo 503794 567193 := bbase (se 2 (by rfl) ⟨212697, by rfl⟩ : syracuseStep 567193 = 425395) (by norm_num)
theorem B731045 : Blo 503794 731045 := bbase (se 4 (by rfl) ⟨68535, by rfl⟩ : syracuseStep 731045 = 137071) (by norm_num)
theorem B567229 : Blo 503794 567229 := bbase (se 3 (by rfl) ⟨106355, by rfl⟩ : syracuseStep 567229 = 212711) (by norm_num)
theorem B567265 : Blo 503794 567265 := bbase (se 2 (by rfl) ⟨212724, by rfl⟩ : syracuseStep 567265 = 425449) (by norm_num)
theorem B567301 : Blo 503794 567301 := bbase (se 4 (by rfl) ⟨53184, by rfl⟩ : syracuseStep 567301 = 106369) (by norm_num)
theorem B567337 : Blo 503794 567337 := bbase (se 2 (by rfl) ⟨212751, by rfl⟩ : syracuseStep 567337 = 425503) (by norm_num)
theorem B2730037 : Blo 503794 2730037 := bbase (se 5 (by rfl) ⟨127970, by rfl⟩ : syracuseStep 2730037 = 255941) (by norm_num)
theorem B567373 : Blo 503794 567373 := bbase (se 3 (by rfl) ⟨106382, by rfl⟩ : syracuseStep 567373 = 212765) (by norm_num)
theorem B567409 : Blo 503794 567409 := bbase (se 2 (by rfl) ⟨212778, by rfl⟩ : syracuseStep 567409 = 425557) (by norm_num)
theorem B567445 : Blo 503794 567445 := bbase (se 6 (by rfl) ⟨13299, by rfl⟩ : syracuseStep 567445 = 26599) (by norm_num)
theorem B567481 : Blo 503794 567481 := bbase (se 2 (by rfl) ⟨212805, by rfl⟩ : syracuseStep 567481 = 425611) (by norm_num)
theorem B8726741 : Blo 503794 8726741 := bbase (se 7 (by rfl) ⟨102266, by rfl⟩ : syracuseStep 8726741 = 204533) (by norm_num)
theorem B567517 : Blo 503794 567517 := bbase (se 3 (by rfl) ⟨106409, by rfl⟩ : syracuseStep 567517 = 212819) (by norm_num)
theorem B567553 : Blo 503794 567553 := bbase (se 2 (by rfl) ⟨212832, by rfl⟩ : syracuseStep 567553 = 425665) (by norm_num)
theorem B567589 : Blo 503794 567589 := bbase (se 4 (by rfl) ⟨53211, by rfl⟩ : syracuseStep 567589 = 106423) (by norm_num)
theorem B567625 : Blo 503794 567625 := bbase (se 2 (by rfl) ⟨212859, by rfl⟩ : syracuseStep 567625 = 425719) (by norm_num)
theorem B567661 : Blo 503794 567661 := bbase (se 3 (by rfl) ⟨106436, by rfl⟩ : syracuseStep 567661 = 212873) (by norm_num)
theorem B567697 : Blo 503794 567697 := bbase (se 2 (by rfl) ⟨212886, by rfl⟩ : syracuseStep 567697 = 425773) (by norm_num)
theorem B2566565 : Blo 503794 2566565 := bbase (se 4 (by rfl) ⟨240615, by rfl⟩ : syracuseStep 2566565 = 481231) (by norm_num)
theorem B567733 : Blo 503794 567733 := bbase (se 5 (by rfl) ⟨26612, by rfl⟩ : syracuseStep 567733 = 53225) (by norm_num)
theorem B731605 : Blo 503794 731605 := bbase (se 7 (by rfl) ⟨8573, by rfl⟩ : syracuseStep 731605 = 17147) (by norm_num)
theorem B567769 : Blo 503794 567769 := bbase (se 2 (by rfl) ⟨212913, by rfl⟩ : syracuseStep 567769 = 425827) (by norm_num)
theorem B960997 : Blo 503794 960997 := bbase (se 4 (by rfl) ⟨90093, by rfl⟩ : syracuseStep 960997 = 180187) (by norm_num)
theorem B567805 : Blo 503794 567805 := bbase (se 3 (by rfl) ⟨106463, by rfl⟩ : syracuseStep 567805 = 212927) (by norm_num)
theorem B567841 : Blo 503794 567841 := bbase (se 2 (by rfl) ⟨212940, by rfl⟩ : syracuseStep 567841 = 425881) (by norm_num)
theorem B1092133 : Blo 503794 1092133 := bbase (se 4 (by rfl) ⟨102387, by rfl⟩ : syracuseStep 1092133 = 204775) (by norm_num)
theorem B1878565 : Blo 503794 1878565 := bbase (se 4 (by rfl) ⟨176115, by rfl⟩ : syracuseStep 1878565 = 352231) (by norm_num)
theorem B567877 : Blo 503794 567877 := bbase (se 4 (by rfl) ⟨53238, by rfl⟩ : syracuseStep 567877 = 106477) (by norm_num)
theorem B567913 : Blo 503794 567913 := bbase (se 2 (by rfl) ⟨212967, by rfl⟩ : syracuseStep 567913 = 425935) (by norm_num)
theorem B961141 : Blo 503794 961141 := bbase (se 5 (by rfl) ⟨45053, by rfl⟩ : syracuseStep 961141 = 90107) (by norm_num)
theorem B567949 : Blo 503794 567949 := bbase (se 3 (by rfl) ⟨106490, by rfl⟩ : syracuseStep 567949 = 212981) (by norm_num)
theorem B567985 : Blo 503794 567985 := bbase (se 2 (by rfl) ⟨212994, by rfl⟩ : syracuseStep 567985 = 425989) (by norm_num)
theorem B568021 : Blo 503794 568021 := bbase (se 7 (by rfl) ⟨6656, by rfl⟩ : syracuseStep 568021 = 13313) (by norm_num)
theorem B2730709 : Blo 503794 2730709 := bbase (se 7 (by rfl) ⟨32000, by rfl⟩ : syracuseStep 2730709 = 64001) (by norm_num)
theorem B568057 : Blo 503794 568057 := bbase (se 2 (by rfl) ⟨213021, by rfl⟩ : syracuseStep 568057 = 426043) (by norm_num)
theorem B961301 : Blo 503794 961301 := bbase (se 6 (by rfl) ⟨22530, by rfl⟩ : syracuseStep 961301 = 45061) (by norm_num)
theorem B568093 : Blo 503794 568093 := bbase (se 3 (by rfl) ⟨106517, by rfl⟩ : syracuseStep 568093 = 213035) (by norm_num)
theorem B568129 : Blo 503794 568129 := bbase (se 2 (by rfl) ⟨213048, by rfl⟩ : syracuseStep 568129 = 426097) (by norm_num)
theorem B7875413 : Blo 503794 7875413 := bbase (se 9 (by rfl) ⟨23072, by rfl⟩ : syracuseStep 7875413 = 46145) (by norm_num)
theorem B568165 : Blo 503794 568165 := bbase (se 4 (by rfl) ⟨53265, by rfl⟩ : syracuseStep 568165 = 106531) (by norm_num)
theorem B4107125 : Blo 503794 4107125 := bbase (se 5 (by rfl) ⟨192521, by rfl⟩ : syracuseStep 4107125 = 385043) (by norm_num)
theorem B568201 : Blo 503794 568201 := bbase (se 2 (by rfl) ⟨213075, by rfl⟩ : syracuseStep 568201 = 426151) (by norm_num)
theorem B961445 : Blo 503794 961445 := bbase (se 4 (by rfl) ⟨90135, by rfl⟩ : syracuseStep 961445 = 180271) (by norm_num)
theorem B568237 : Blo 503794 568237 := bbase (se 3 (by rfl) ⟨106544, by rfl⟩ : syracuseStep 568237 = 213089) (by norm_num)
theorem B1158085 : Blo 503794 1158085 := bbase (se 4 (by rfl) ⟨108570, by rfl⟩ : syracuseStep 1158085 = 217141) (by norm_num)
theorem B568273 : Blo 503794 568273 := bbase (se 2 (by rfl) ⟨213102, by rfl⟩ : syracuseStep 568273 = 426205) (by norm_num)
theorem B568309 : Blo 503794 568309 := bbase (se 5 (by rfl) ⟨26639, by rfl⟩ : syracuseStep 568309 = 53279) (by norm_num)
theorem B568345 : Blo 503794 568345 := bbase (se 2 (by rfl) ⟨213129, by rfl⟩ : syracuseStep 568345 = 426259) (by norm_num)
theorem B568381 : Blo 503794 568381 := bbase (se 3 (by rfl) ⟨106571, by rfl⟩ : syracuseStep 568381 = 213143) (by norm_num)
theorem B1944661 : Blo 503794 1944661 := bbase (se 8 (by rfl) ⟨11394, by rfl⟩ : syracuseStep 1944661 = 22789) (by norm_num)
theorem B568417 : Blo 503794 568417 := bbase (se 2 (by rfl) ⟨213156, by rfl⟩ : syracuseStep 568417 = 426313) (by norm_num)
theorem B568453 : Blo 503794 568453 := bbase (se 4 (by rfl) ⟨53292, by rfl⟩ : syracuseStep 568453 = 106585) (by norm_num)
theorem B568489 : Blo 503794 568489 := bbase (se 2 (by rfl) ⟨213183, by rfl⟩ : syracuseStep 568489 = 426367) (by norm_num)
theorem B961733 : Blo 503794 961733 := bbase (se 4 (by rfl) ⟨90162, by rfl⟩ : syracuseStep 961733 = 180325) (by norm_num)
theorem B568525 : Blo 503794 568525 := bbase (se 3 (by rfl) ⟨106598, by rfl⟩ : syracuseStep 568525 = 213197) (by norm_num)
theorem B568561 : Blo 503794 568561 := bbase (se 2 (by rfl) ⟨213210, by rfl⟩ : syracuseStep 568561 = 426421) (by norm_num)
theorem B568597 : Blo 503794 568597 := bbase (se 6 (by rfl) ⟨13326, by rfl⟩ : syracuseStep 568597 = 26653) (by norm_num)
theorem B568633 : Blo 503794 568633 := bbase (se 2 (by rfl) ⟨213237, by rfl⟩ : syracuseStep 568633 = 426475) (by norm_num)
theorem B568669 : Blo 503794 568669 := bbase (se 3 (by rfl) ⟨106625, by rfl⟩ : syracuseStep 568669 = 213251) (by norm_num)
theorem B961885 : Blo 503794 961885 := bbase (se 3 (by rfl) ⟨180353, by rfl⟩ : syracuseStep 961885 = 360707) (by norm_num)
theorem B1092973 : Blo 503794 1092973 := bbase (se 3 (by rfl) ⟨204932, by rfl⟩ : syracuseStep 1092973 = 409865) (by norm_num)
theorem B568705 : Blo 503794 568705 := bbase (se 2 (by rfl) ⟨213264, by rfl⟩ : syracuseStep 568705 = 426529) (by norm_num)
theorem B568741 : Blo 503794 568741 := bbase (se 4 (by rfl) ⟨53319, by rfl⟩ : syracuseStep 568741 = 106639) (by norm_num)
theorem B568777 : Blo 503794 568777 := bbase (se 2 (by rfl) ⟨213291, by rfl⟩ : syracuseStep 568777 = 426583) (by norm_num)
theorem B2436581 : Blo 503794 2436581 := bbase (se 4 (by rfl) ⟨228429, by rfl⟩ : syracuseStep 2436581 = 456859) (by norm_num)
theorem B568813 : Blo 503794 568813 := bbase (se 3 (by rfl) ⟨106652, by rfl⟩ : syracuseStep 568813 = 213305) (by norm_num)
theorem B568849 : Blo 503794 568849 := bbase (se 2 (by rfl) ⟨213318, by rfl⟩ : syracuseStep 568849 = 426637) (by norm_num)
theorem B568885 : Blo 503794 568885 := bbase (se 5 (by rfl) ⟨26666, by rfl⟩ : syracuseStep 568885 = 53333) (by norm_num)
theorem B3845717 : Blo 503794 3845717 := bbase (se 8 (by rfl) ⟨22533, by rfl⟩ : syracuseStep 3845717 = 45067) (by norm_num)
theorem B568921 : Blo 503794 568921 := bbase (se 2 (by rfl) ⟨213345, by rfl⟩ : syracuseStep 568921 = 426691) (by norm_num)
theorem B568957 : Blo 503794 568957 := bbase (se 3 (by rfl) ⟨106679, by rfl⟩ : syracuseStep 568957 = 213359) (by norm_num)
theorem B962189 : Blo 503794 962189 := bbase (se 3 (by rfl) ⟨180410, by rfl⟩ : syracuseStep 962189 = 360821) (by norm_num)
theorem B568993 : Blo 503794 568993 := bbase (se 2 (by rfl) ⟨213372, by rfl⟩ : syracuseStep 568993 = 426745) (by norm_num)
theorem B2567861 : Blo 503794 2567861 := bbase (se 5 (by rfl) ⟨120368, by rfl⟩ : syracuseStep 2567861 = 240737) (by norm_num)
theorem B569029 : Blo 503794 569029 := bbase (se 4 (by rfl) ⟨53346, by rfl⟩ : syracuseStep 569029 = 106693) (by norm_num)
theorem B569065 : Blo 503794 569065 := bbase (se 2 (by rfl) ⟨213399, by rfl⟩ : syracuseStep 569065 = 426799) (by norm_num)
theorem B569101 : Blo 503794 569101 := bbase (se 3 (by rfl) ⟨106706, by rfl⟩ : syracuseStep 569101 = 213413) (by norm_num)
theorem B569137 : Blo 503794 569137 := bbase (se 2 (by rfl) ⟨213426, by rfl⟩ : syracuseStep 569137 = 426853) (by norm_num)
theorem B2043701 : Blo 503794 2043701 := bbase (se 5 (by rfl) ⟨95798, by rfl⟩ : syracuseStep 2043701 = 191597) (by norm_num)
theorem B569173 : Blo 503794 569173 := bbase (se 9 (by rfl) ⟨1667, by rfl⟩ : syracuseStep 569173 = 3335) (by norm_num)
theorem B569209 : Blo 503794 569209 := bbase (se 2 (by rfl) ⟨213453, by rfl⟩ : syracuseStep 569209 = 426907) (by norm_num)
theorem B1027981 : Blo 503794 1027981 := bbase (se 3 (by rfl) ⟨192746, by rfl⟩ : syracuseStep 1027981 = 385493) (by norm_num)
theorem B569245 : Blo 503794 569245 := bbase (se 3 (by rfl) ⟨106733, by rfl⟩ : syracuseStep 569245 = 213467) (by norm_num)
theorem B569281 : Blo 503794 569281 := bbase (se 2 (by rfl) ⟨213480, by rfl⟩ : syracuseStep 569281 = 426961) (by norm_num)
theorem B569317 : Blo 503794 569317 := bbase (se 4 (by rfl) ⟨53373, by rfl⟩ : syracuseStep 569317 = 106747) (by norm_num)
theorem B569353 : Blo 503794 569353 := bbase (se 2 (by rfl) ⟨213507, by rfl⟩ : syracuseStep 569353 = 427015) (by norm_num)
theorem B569389 : Blo 503794 569389 := bbase (se 3 (by rfl) ⟨106760, by rfl⟩ : syracuseStep 569389 = 213521) (by norm_num)
theorem B569425 : Blo 503794 569425 := bbase (se 2 (by rfl) ⟨213534, by rfl⟩ : syracuseStep 569425 = 427069) (by norm_num)
theorem B3518549 : Blo 503794 3518549 := bbase (se 8 (by rfl) ⟨20616, by rfl⟩ : syracuseStep 3518549 = 41233) (by norm_num)
theorem B569461 : Blo 503794 569461 := bbase (se 5 (by rfl) ⟨26693, by rfl⟩ : syracuseStep 569461 = 53387) (by norm_num)
theorem B569497 : Blo 503794 569497 := bbase (se 2 (by rfl) ⟨213561, by rfl⟩ : syracuseStep 569497 = 427123) (by norm_num)
theorem B569533 : Blo 503794 569533 := bbase (se 3 (by rfl) ⟨106787, by rfl⟩ : syracuseStep 569533 = 213575) (by norm_num)
theorem B4305109 : Blo 503794 4305109 := bbase (se 7 (by rfl) ⟨50450, by rfl⟩ : syracuseStep 4305109 = 100901) (by norm_num)
theorem B569569 : Blo 503794 569569 := bbase (se 2 (by rfl) ⟨213588, by rfl⟩ : syracuseStep 569569 = 427177) (by norm_num)
theorem B569605 : Blo 503794 569605 := bbase (se 4 (by rfl) ⟨53400, by rfl⟩ : syracuseStep 569605 = 106801) (by norm_num)
theorem B569641 : Blo 503794 569641 := bbase (se 2 (by rfl) ⟨213615, by rfl⟩ : syracuseStep 569641 = 427231) (by norm_num)
theorem B569677 : Blo 503794 569677 := bbase (se 3 (by rfl) ⟨106814, by rfl⟩ : syracuseStep 569677 = 213629) (by norm_num)
theorem B569713 : Blo 503794 569713 := bbase (se 2 (by rfl) ⟨213642, by rfl⟩ : syracuseStep 569713 = 427285) (by norm_num)
theorem B962941 : Blo 503794 962941 := bbase (se 3 (by rfl) ⟨180551, by rfl⟩ : syracuseStep 962941 = 361103) (by norm_num)
theorem B569749 : Blo 503794 569749 := bbase (se 6 (by rfl) ⟨13353, by rfl⟩ : syracuseStep 569749 = 26707) (by norm_num)
theorem B569785 : Blo 503794 569785 := bbase (se 2 (by rfl) ⟨213669, by rfl⟩ : syracuseStep 569785 = 427339) (by norm_num)
theorem B569821 : Blo 503794 569821 := bbase (se 3 (by rfl) ⟨106841, by rfl⟩ : syracuseStep 569821 = 213683) (by norm_num)
theorem B569857 : Blo 503794 569857 := bbase (se 2 (by rfl) ⟨213696, by rfl⟩ : syracuseStep 569857 = 427393) (by norm_num)
theorem B963085 : Blo 503794 963085 := bbase (se 3 (by rfl) ⟨180578, by rfl⟩ : syracuseStep 963085 = 361157) (by norm_num)
theorem B569893 : Blo 503794 569893 := bbase (se 4 (by rfl) ⟨53427, by rfl⟩ : syracuseStep 569893 = 106855) (by norm_num)
theorem B569929 : Blo 503794 569929 := bbase (se 2 (by rfl) ⟨213723, by rfl⟩ : syracuseStep 569929 = 427447) (by norm_num)
theorem B1618517 : Blo 503794 1618517 := bbase (se 8 (by rfl) ⟨9483, by rfl⟩ : syracuseStep 1618517 = 18967) (by norm_num)
theorem B569965 : Blo 503794 569965 := bbase (se 3 (by rfl) ⟨106868, by rfl⟩ : syracuseStep 569965 = 213737) (by norm_num)
theorem B570001 : Blo 503794 570001 := bbase (se 2 (by rfl) ⟨213750, by rfl⟩ : syracuseStep 570001 = 427501) (by norm_num)
theorem B963245 : Blo 503794 963245 := bbase (se 3 (by rfl) ⟨180608, by rfl⟩ : syracuseStep 963245 = 361217) (by norm_num)
theorem B570037 : Blo 503794 570037 := bbase (se 5 (by rfl) ⟨26720, by rfl⟩ : syracuseStep 570037 = 53441) (by norm_num)
theorem B1094357 : Blo 503794 1094357 := bbase (se 7 (by rfl) ⟨12824, by rfl⟩ : syracuseStep 1094357 = 25649) (by norm_num)
theorem B570073 : Blo 503794 570073 := bbase (se 2 (by rfl) ⟨213777, by rfl⟩ : syracuseStep 570073 = 427555) (by norm_num)
theorem B570109 : Blo 503794 570109 := bbase (se 3 (by rfl) ⟨106895, by rfl⟩ : syracuseStep 570109 = 213791) (by norm_num)
theorem B1946389 : Blo 503794 1946389 := bbase (se 6 (by rfl) ⟨45618, by rfl⟩ : syracuseStep 1946389 = 91237) (by norm_num)
theorem B570145 : Blo 503794 570145 := bbase (se 2 (by rfl) ⟨213804, by rfl⟩ : syracuseStep 570145 = 427609) (by norm_num)
theorem B2044709 : Blo 503794 2044709 := bbase (se 4 (by rfl) ⟨191691, by rfl⟩ : syracuseStep 2044709 = 383383) (by norm_num)
theorem B963389 : Blo 503794 963389 := bbase (se 3 (by rfl) ⟨180635, by rfl⟩ : syracuseStep 963389 = 361271) (by norm_num)
theorem B570181 : Blo 503794 570181 := bbase (se 4 (by rfl) ⟨53454, by rfl⟩ : syracuseStep 570181 = 106909) (by norm_num)
theorem B570217 : Blo 503794 570217 := bbase (se 2 (by rfl) ⟨213831, by rfl⟩ : syracuseStep 570217 = 427663) (by norm_num)
theorem B570253 : Blo 503794 570253 := bbase (se 3 (by rfl) ⟨106922, by rfl⟩ : syracuseStep 570253 = 213845) (by norm_num)
theorem B570289 : Blo 503794 570289 := bbase (se 2 (by rfl) ⟨213858, by rfl⟩ : syracuseStep 570289 = 427717) (by norm_num)
theorem B2569157 : Blo 503794 2569157 := bbase (se 4 (by rfl) ⟨240858, by rfl⟩ : syracuseStep 2569157 = 481717) (by norm_num)
theorem B570325 : Blo 503794 570325 := bbase (se 7 (by rfl) ⟨6683, by rfl⟩ : syracuseStep 570325 = 13367) (by norm_num)
theorem B570361 : Blo 503794 570361 := bbase (se 2 (by rfl) ⟨213885, by rfl⟩ : syracuseStep 570361 = 427771) (by norm_num)
theorem B570397 : Blo 503794 570397 := bbase (se 3 (by rfl) ⟨106949, by rfl⟩ : syracuseStep 570397 = 213899) (by norm_num)
theorem B570433 : Blo 503794 570433 := bbase (se 2 (by rfl) ⟨213912, by rfl⟩ : syracuseStep 570433 = 427825) (by norm_num)
theorem B963677 : Blo 503794 963677 := bbase (se 3 (by rfl) ⟨180689, by rfl⟩ : syracuseStep 963677 = 361379) (by norm_num)
theorem B570469 : Blo 503794 570469 := bbase (se 4 (by rfl) ⟨53481, by rfl⟩ : syracuseStep 570469 = 106963) (by norm_num)
theorem B1913989 : Blo 503794 1913989 := bbase (se 4 (by rfl) ⟨179436, by rfl⟩ : syracuseStep 1913989 = 358873) (by norm_num)
theorem B570505 : Blo 503794 570505 := bbase (se 2 (by rfl) ⟨213939, by rfl⟩ : syracuseStep 570505 = 427879) (by norm_num)
theorem B570541 : Blo 503794 570541 := bbase (se 3 (by rfl) ⟨106976, by rfl⟩ : syracuseStep 570541 = 213953) (by norm_num)
theorem B570577 : Blo 503794 570577 := bbase (se 2 (by rfl) ⟨213966, by rfl⟩ : syracuseStep 570577 = 427933) (by norm_num)
theorem B570613 : Blo 503794 570613 := bbase (se 5 (by rfl) ⟨26747, by rfl⟩ : syracuseStep 570613 = 53495) (by norm_num)
theorem B963829 : Blo 503794 963829 := bbase (se 5 (by rfl) ⟨45179, by rfl⟩ : syracuseStep 963829 = 90359) (by norm_num)
theorem B570649 : Blo 503794 570649 := bbase (se 2 (by rfl) ⟨213993, by rfl⟩ : syracuseStep 570649 = 427987) (by norm_num)
theorem B570685 : Blo 503794 570685 := bbase (se 3 (by rfl) ⟨107003, by rfl⟩ : syracuseStep 570685 = 214007) (by norm_num)
theorem B570721 : Blo 503794 570721 := bbase (se 2 (by rfl) ⟨214020, by rfl⟩ : syracuseStep 570721 = 428041) (by norm_num)
theorem B865637 : Blo 503794 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B570757 : Blo 503794 570757 := bbase (se 4 (by rfl) ⟨53508, by rfl⟩ : syracuseStep 570757 = 107017) (by norm_num)
theorem B2602405 : Blo 503794 2602405 := bbase (se 4 (by rfl) ⟨243975, by rfl⟩ : syracuseStep 2602405 = 487951) (by norm_num)
theorem B570793 : Blo 503794 570793 := bbase (se 2 (by rfl) ⟨214047, by rfl⟩ : syracuseStep 570793 = 428095) (by norm_num)
theorem B1914293 : Blo 503794 1914293 := bbase (se 5 (by rfl) ⟨89732, by rfl⟩ : syracuseStep 1914293 = 179465) (by norm_num)
theorem B570829 : Blo 503794 570829 := bbase (se 3 (by rfl) ⟨107030, by rfl⟩ : syracuseStep 570829 = 214061) (by norm_num)
theorem B570865 : Blo 503794 570865 := bbase (se 2 (by rfl) ⟨214074, by rfl⟩ : syracuseStep 570865 = 428149) (by norm_num)
theorem B570901 : Blo 503794 570901 := bbase (se 6 (by rfl) ⟨13380, by rfl⟩ : syracuseStep 570901 = 26761) (by norm_num)
theorem B538169 : Blo 503794 538169 := bbase (se 2 (by rfl) ⟨201813, by rfl⟩ : syracuseStep 538169 = 403627) (by norm_num)
theorem B570937 : Blo 503794 570937 := bbase (se 2 (by rfl) ⟨214101, by rfl⟩ : syracuseStep 570937 = 428203) (by norm_num)
theorem B570973 : Blo 503794 570973 := bbase (se 3 (by rfl) ⟨107057, by rfl⟩ : syracuseStep 570973 = 214115) (by norm_num)
theorem B571009 : Blo 503794 571009 := bbase (se 2 (by rfl) ⟨214128, by rfl⟩ : syracuseStep 571009 = 428257) (by norm_num)
theorem B571045 : Blo 503794 571045 := bbase (se 4 (by rfl) ⟨53535, by rfl⟩ : syracuseStep 571045 = 107071) (by norm_num)
theorem B571081 : Blo 503794 571081 := bbase (se 2 (by rfl) ⟨214155, by rfl⟩ : syracuseStep 571081 = 428311) (by norm_num)
theorem B571117 : Blo 503794 571117 := bbase (se 3 (by rfl) ⟨107084, by rfl⟩ : syracuseStep 571117 = 214169) (by norm_num)
theorem B571153 : Blo 503794 571153 := bbase (se 2 (by rfl) ⟨214182, by rfl⟩ : syracuseStep 571153 = 428365) (by norm_num)
theorem B3127061 : Blo 503794 3127061 := bbase (se 6 (by rfl) ⟨73290, by rfl⟩ : syracuseStep 3127061 = 146581) (by norm_num)
theorem B571189 : Blo 503794 571189 := bbase (se 5 (by rfl) ⟨26774, by rfl⟩ : syracuseStep 571189 = 53549) (by norm_num)
theorem B571225 : Blo 503794 571225 := bbase (se 2 (by rfl) ⟨214209, by rfl⟩ : syracuseStep 571225 = 428419) (by norm_num)
theorem B1947493 : Blo 503794 1947493 := bbase (se 4 (by rfl) ⟨182577, by rfl⟩ : syracuseStep 1947493 = 365155) (by norm_num)
theorem B571261 : Blo 503794 571261 := bbase (se 3 (by rfl) ⟨107111, by rfl⟩ : syracuseStep 571261 = 214223) (by norm_num)
theorem B4307093 : Blo 503794 4307093 := bbase (se 6 (by rfl) ⟨100947, by rfl⟩ : syracuseStep 4307093 = 201895) (by norm_num)
theorem B2570453 : Blo 503794 2570453 := bbase (se 7 (by rfl) ⟨30122, by rfl⟩ : syracuseStep 2570453 = 60245) (by norm_num)
theorem B538921 : Blo 503794 538921 := bbase (se 2 (by rfl) ⟨202095, by rfl⟩ : syracuseStep 538921 = 404191) (by norm_num)
theorem B538993 : Blo 503794 538993 := bbase (se 2 (by rfl) ⟨202122, by rfl⟩ : syracuseStep 538993 = 404245) (by norm_num)
theorem B5257685 : Blo 503794 5257685 := bbase (se 7 (by rfl) ⟨61613, by rfl⟩ : syracuseStep 5257685 = 123227) (by norm_num)
theorem B539173 : Blo 503794 539173 := bbase (se 4 (by rfl) ⟨50547, by rfl⟩ : syracuseStep 539173 = 101095) (by norm_num)
theorem B637733 : Blo 503794 637733 := bbase (se 4 (by rfl) ⟨59787, by rfl⟩ : syracuseStep 637733 = 119575) (by norm_num)
theorem B1620773 : Blo 503794 1620773 := bbase (se 4 (by rfl) ⟨151947, by rfl⟩ : syracuseStep 1620773 = 303895) (by norm_num)
theorem B637789 : Blo 503794 637789 := bbase (se 3 (by rfl) ⟨119585, by rfl⟩ : syracuseStep 637789 = 239171) (by norm_num)
theorem B1620901 : Blo 503794 1620901 := bbase (se 4 (by rfl) ⟨151959, by rfl⟩ : syracuseStep 1620901 = 303919) (by norm_num)
theorem B637885 : Blo 503794 637885 := bbase (se 3 (by rfl) ⟨119603, by rfl⟩ : syracuseStep 637885 = 239207) (by norm_num)
theorem B539617 : Blo 503794 539617 := bbase (se 2 (by rfl) ⟨202356, by rfl⟩ : syracuseStep 539617 = 404713) (by norm_num)
theorem B539741 : Blo 503794 539741 := bbase (se 3 (by rfl) ⟨101201, by rfl⟩ : syracuseStep 539741 = 202403) (by norm_num)
theorem B638057 : Blo 503794 638057 := bbase (se 2 (by rfl) ⟨239271, by rfl⟩ : syracuseStep 638057 = 478543) (by norm_num)
theorem B4602997 : Blo 503794 4602997 := bbase (se 5 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 4602997 = 431531) (by norm_num)
theorem B638113 : Blo 503794 638113 := bbase (se 2 (by rfl) ⟨239292, by rfl⟩ : syracuseStep 638113 = 478585) (by norm_num)
theorem B1293509 : Blo 503794 1293509 := bbase (se 4 (by rfl) ⟨121266, by rfl⟩ : syracuseStep 1293509 = 242533) (by norm_num)
theorem B638209 : Blo 503794 638209 := bbase (se 2 (by rfl) ⟨239328, by rfl⟩ : syracuseStep 638209 = 478657) (by norm_num)
theorem B11124053 : Blo 503794 11124053 := bbase (se 11 (by rfl) ⟨8147, by rfl⟩ : syracuseStep 11124053 = 16295) (by norm_num)
theorem B539993 : Blo 503794 539993 := bbase (se 2 (by rfl) ⟨202497, by rfl⟩ : syracuseStep 539993 = 404995) (by norm_num)
theorem B638381 : Blo 503794 638381 := bbase (se 3 (by rfl) ⟨119696, by rfl⟩ : syracuseStep 638381 = 239393) (by norm_num)
theorem B638437 : Blo 503794 638437 := bbase (se 4 (by rfl) ⟨59853, by rfl⟩ : syracuseStep 638437 = 119707) (by norm_num)
theorem B1916405 : Blo 503794 1916405 := bbase (se 5 (by rfl) ⟨89831, by rfl⟩ : syracuseStep 1916405 = 179663) (by norm_num)
theorem B638533 : Blo 503794 638533 := bbase (se 4 (by rfl) ⟨59862, by rfl⟩ : syracuseStep 638533 = 119725) (by norm_num)
theorem B2637413 : Blo 503794 2637413 := bbase (se 4 (by rfl) ⟨247257, by rfl⟩ : syracuseStep 2637413 = 494515) (by norm_num)
theorem B769765 : Blo 503794 769765 := bbase (se 4 (by rfl) ⟨72165, by rfl⟩ : syracuseStep 769765 = 144331) (by norm_num)
theorem B638705 : Blo 503794 638705 := bbase (se 2 (by rfl) ⟨239514, by rfl⟩ : syracuseStep 638705 = 479029) (by norm_num)
theorem B1916693 : Blo 503794 1916693 := bbase (se 6 (by rfl) ⟨44922, by rfl⟩ : syracuseStep 1916693 = 89845) (by norm_num)
theorem B540437 : Blo 503794 540437 := bbase (se 6 (by rfl) ⟨12666, by rfl⟩ : syracuseStep 540437 = 25333) (by norm_num)
theorem B638761 : Blo 503794 638761 := bbase (se 2 (by rfl) ⟨239535, by rfl⟩ : syracuseStep 638761 = 479071) (by norm_num)
theorem B638857 : Blo 503794 638857 := bbase (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) (by norm_num)
theorem B606209 : Blo 503794 606209 := bbase (se 2 (by rfl) ⟨227328, by rfl⟩ : syracuseStep 606209 = 454657) (by norm_num)
theorem B540685 : Blo 503794 540685 := bbase (se 3 (by rfl) ⟨101378, by rfl⟩ : syracuseStep 540685 = 202757) (by norm_num)
theorem B639029 : Blo 503794 639029 := bbase (se 5 (by rfl) ⟨29954, by rfl⟩ : syracuseStep 639029 = 59909) (by norm_num)
theorem B639085 : Blo 503794 639085 := bbase (se 3 (by rfl) ⟨119828, by rfl⟩ : syracuseStep 639085 = 239657) (by norm_num)
theorem B639181 : Blo 503794 639181 := bbase (se 3 (by rfl) ⟨119846, by rfl⟩ : syracuseStep 639181 = 239693) (by norm_num)
theorem B606541 : Blo 503794 606541 := bbase (se 3 (by rfl) ⟨113726, by rfl⟩ : syracuseStep 606541 = 227453) (by norm_num)
theorem B3457397 : Blo 503794 3457397 := bbase (se 5 (by rfl) ⟨162065, by rfl⟩ : syracuseStep 3457397 = 324131) (by norm_num)
theorem B639353 : Blo 503794 639353 := bbase (se 2 (by rfl) ⟨239757, by rfl⟩ : syracuseStep 639353 = 479515) (by norm_num)
theorem B639409 : Blo 503794 639409 := bbase (se 2 (by rfl) ⟨239778, by rfl⟩ : syracuseStep 639409 = 479557) (by norm_num)
theorem B541129 : Blo 503794 541129 := bbase (se 2 (by rfl) ⟨202923, by rfl⟩ : syracuseStep 541129 = 405847) (by norm_num)
theorem B606685 : Blo 503794 606685 := bbase (se 3 (by rfl) ⟨113753, by rfl⟩ : syracuseStep 606685 = 227507) (by norm_num)
theorem B541189 : Blo 503794 541189 := bbase (se 4 (by rfl) ⟨50736, by rfl⟩ : syracuseStep 541189 = 101473) (by norm_num)
theorem B639505 : Blo 503794 639505 := bbase (se 2 (by rfl) ⟨239814, by rfl⟩ : syracuseStep 639505 = 479629) (by norm_num)
theorem B2310805 : Blo 503794 2310805 := bbase (se 6 (by rfl) ⟨54159, by rfl⟩ : syracuseStep 2310805 = 108319) (by norm_num)
theorem B639677 : Blo 503794 639677 := bbase (se 3 (by rfl) ⟨119939, by rfl⟩ : syracuseStep 639677 = 239879) (by norm_num)
theorem B639733 : Blo 503794 639733 := bbase (se 5 (by rfl) ⟨29987, by rfl⟩ : syracuseStep 639733 = 59975) (by norm_num)
theorem B541505 : Blo 503794 541505 := bbase (se 2 (by rfl) ⟨203064, by rfl⟩ : syracuseStep 541505 = 406129) (by norm_num)
theorem B639829 : Blo 503794 639829 := bbase (se 9 (by rfl) ⟨1874, by rfl⟩ : syracuseStep 639829 = 3749) (by norm_num)
theorem B770933 : Blo 503794 770933 := bbase (se 5 (by rfl) ⟨36137, by rfl⟩ : syracuseStep 770933 = 72275) (by norm_num)
theorem B1917877 : Blo 503794 1917877 := bbase (se 5 (by rfl) ⟨89900, by rfl⟩ : syracuseStep 1917877 = 179801) (by norm_num)
theorem B640001 : Blo 503794 640001 := bbase (se 2 (by rfl) ⟨240000, by rfl⟩ : syracuseStep 640001 = 480001) (by norm_num)
theorem B1295365 : Blo 503794 1295365 := bbase (se 4 (by rfl) ⟨121440, by rfl⟩ : syracuseStep 1295365 = 242881) (by norm_num)
theorem B640057 : Blo 503794 640057 := bbase (se 2 (by rfl) ⟨240021, by rfl⟩ : syracuseStep 640057 = 480043) (by norm_num)
theorem B771157 : Blo 503794 771157 := bbase (se 8 (by rfl) ⟨4518, by rfl⟩ : syracuseStep 771157 = 9037) (by norm_num)
theorem B640153 : Blo 503794 640153 := bbase (se 2 (by rfl) ⟨240057, by rfl⟩ : syracuseStep 640153 = 480115) (by norm_num)
theorem B1918181 : Blo 503794 1918181 := bbase (se 4 (by rfl) ⟨179829, by rfl⟩ : syracuseStep 1918181 = 359659) (by norm_num)
theorem B541949 : Blo 503794 541949 := bbase (se 3 (by rfl) ⟨101615, by rfl⟩ : syracuseStep 541949 = 203231) (by norm_num)
theorem B1819909 : Blo 503794 1819909 := bbase (se 4 (by rfl) ⟨170616, by rfl⟩ : syracuseStep 1819909 = 341233) (by norm_num)
theorem B542009 : Blo 503794 542009 := bbase (se 2 (by rfl) ⟨203253, by rfl⟩ : syracuseStep 542009 = 406507) (by norm_num)
theorem B640325 : Blo 503794 640325 := bbase (se 4 (by rfl) ⟨60030, by rfl⟩ : syracuseStep 640325 = 120061) (by norm_num)
theorem B640381 : Blo 503794 640381 := bbase (se 3 (by rfl) ⟨120071, by rfl⟩ : syracuseStep 640381 = 240143) (by norm_num)
theorem B542137 : Blo 503794 542137 := bbase (se 2 (by rfl) ⟨203301, by rfl⟩ : syracuseStep 542137 = 406603) (by norm_num)
theorem B607709 : Blo 503794 607709 := bbase (se 3 (by rfl) ⟨113945, by rfl⟩ : syracuseStep 607709 = 227891) (by norm_num)
theorem B640477 : Blo 503794 640477 := bbase (se 3 (by rfl) ⟨120089, by rfl⟩ : syracuseStep 640477 = 240179) (by norm_num)
theorem B1951253 : Blo 503794 1951253 := bbase (se 6 (by rfl) ⟨45732, by rfl⟩ : syracuseStep 1951253 = 91465) (by norm_num)
theorem B640649 : Blo 503794 640649 := bbase (se 2 (by rfl) ⟨240243, by rfl⟩ : syracuseStep 640649 = 480487) (by norm_num)
theorem B640705 : Blo 503794 640705 := bbase (se 2 (by rfl) ⟨240264, by rfl⟩ : syracuseStep 640705 = 480529) (by norm_num)
theorem B1623797 : Blo 503794 1623797 := bbase (se 5 (by rfl) ⟨76115, by rfl⟩ : syracuseStep 1623797 = 152231) (by norm_num)
theorem B640801 : Blo 503794 640801 := bbase (se 2 (by rfl) ⟨240300, by rfl⟩ : syracuseStep 640801 = 480601) (by norm_num)
theorem B640973 : Blo 503794 640973 := bbase (se 3 (by rfl) ⟨120182, by rfl⟩ : syracuseStep 640973 = 240365) (by norm_num)
theorem B641029 : Blo 503794 641029 := bbase (se 4 (by rfl) ⟨60096, by rfl⟩ : syracuseStep 641029 = 120193) (by norm_num)
theorem B641125 : Blo 503794 641125 := bbase (se 4 (by rfl) ⟨60105, by rfl⟩ : syracuseStep 641125 = 120211) (by norm_num)
theorem B641297 : Blo 503794 641297 := bbase (se 2 (by rfl) ⟨240486, by rfl⟩ : syracuseStep 641297 = 480973) (by norm_num)
theorem B641353 : Blo 503794 641353 := bbase (se 2 (by rfl) ⟨240507, by rfl⟩ : syracuseStep 641353 = 481015) (by norm_num)
theorem B575905 : Blo 503794 575905 := bbase (se 2 (by rfl) ⟨215964, by rfl⟩ : syracuseStep 575905 = 431929) (by norm_num)
theorem B641449 : Blo 503794 641449 := bbase (se 2 (by rfl) ⟨240543, by rfl⟩ : syracuseStep 641449 = 481087) (by norm_num)
theorem B641621 : Blo 503794 641621 := bbase (se 8 (by rfl) ⟨3759, by rfl⟩ : syracuseStep 641621 = 7519) (by norm_num)
theorem B608905 : Blo 503794 608905 := bbase (se 2 (by rfl) ⟨228339, by rfl⟩ : syracuseStep 608905 = 456679) (by norm_num)
theorem B641677 : Blo 503794 641677 := bbase (se 3 (by rfl) ⟨120314, by rfl⟩ : syracuseStep 641677 = 240629) (by norm_num)
theorem B608977 : Blo 503794 608977 := bbase (se 2 (by rfl) ⟨228366, by rfl⟩ : syracuseStep 608977 = 456733) (by norm_num)
theorem B7785173 : Blo 503794 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B641773 : Blo 503794 641773 := bbase (se 3 (by rfl) ⟨120332, by rfl⟩ : syracuseStep 641773 = 240665) (by norm_num)
theorem B641945 : Blo 503794 641945 := bbase (se 2 (by rfl) ⟨240729, by rfl⟩ : syracuseStep 641945 = 481459) (by norm_num)
theorem B510877 : Blo 503794 510877 := bbase (se 3 (by rfl) ⟨95789, by rfl⟩ : syracuseStep 510877 = 191579) (by norm_num)
theorem B642001 : Blo 503794 642001 := bbase (se 2 (by rfl) ⟨240750, by rfl⟩ : syracuseStep 642001 = 481501) (by norm_num)
theorem B1133549 : Blo 503794 1133549 := bbase (se 3 (by rfl) ⟨212540, by rfl⟩ : syracuseStep 1133549 = 425081) (by norm_num)
theorem B642097 : Blo 503794 642097 := bbase (se 2 (by rfl) ⟨240786, by rfl⟩ : syracuseStep 642097 = 481573) (by norm_num)
theorem B1133621 : Blo 503794 1133621 := bbase (se 5 (by rfl) ⟨53138, by rfl⟩ : syracuseStep 1133621 = 106277) (by norm_num)
theorem B1133693 : Blo 503794 1133693 := bbase (se 3 (by rfl) ⟨212567, by rfl⟩ : syracuseStep 1133693 = 425135) (by norm_num)
theorem B2182277 : Blo 503794 2182277 := bbase (se 4 (by rfl) ⟨204588, by rfl⟩ : syracuseStep 2182277 = 409177) (by norm_num)
theorem B3853493 : Blo 503794 3853493 := bbase (se 5 (by rfl) ⟨180632, by rfl⟩ : syracuseStep 3853493 = 361265) (by norm_num)
theorem B1133765 : Blo 503794 1133765 := bbase (se 4 (by rfl) ⟨106290, by rfl⟩ : syracuseStep 1133765 = 212581) (by norm_num)
theorem B8735957 : Blo 503794 8735957 := bbase (se 7 (by rfl) ⟨102374, by rfl⟩ : syracuseStep 8735957 = 204749) (by norm_num)
theorem B642269 : Blo 503794 642269 := bbase (se 3 (by rfl) ⟨120425, by rfl⟩ : syracuseStep 642269 = 240851) (by norm_num)
theorem B511201 : Blo 503794 511201 := bbase (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) (by norm_num)
theorem B1133837 : Blo 503794 1133837 := bbase (se 3 (by rfl) ⟨212594, by rfl⟩ : syracuseStep 1133837 = 425189) (by norm_num)
theorem B642325 : Blo 503794 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B1920293 : Blo 503794 1920293 := bbase (se 4 (by rfl) ⟨180027, by rfl⟩ : syracuseStep 1920293 = 360055) (by norm_num)
theorem B1133909 : Blo 503794 1133909 := bbase (se 11 (by rfl) ⟨830, by rfl⟩ : syracuseStep 1133909 = 1661) (by norm_num)
theorem B642421 : Blo 503794 642421 := bbase (se 5 (by rfl) ⟨30113, by rfl⟩ : syracuseStep 642421 = 60227) (by norm_num)
theorem B1363333 : Blo 503794 1363333 := bbase (se 4 (by rfl) ⟨127812, by rfl⟩ : syracuseStep 1363333 = 255625) (by norm_num)
theorem B1133981 : Blo 503794 1133981 := bbase (se 3 (by rfl) ⟨212621, by rfl⟩ : syracuseStep 1133981 = 425243) (by norm_num)
theorem B1134053 : Blo 503794 1134053 := bbase (se 4 (by rfl) ⟨106317, by rfl⟩ : syracuseStep 1134053 = 212635) (by norm_num)
theorem B642593 : Blo 503794 642593 := bbase (se 2 (by rfl) ⟨240972, by rfl⟩ : syracuseStep 642593 = 481945) (by norm_num)
theorem B1134125 : Blo 503794 1134125 := bbase (se 3 (by rfl) ⟨212648, by rfl⟩ : syracuseStep 1134125 = 425297) (by norm_num)
theorem B1920581 : Blo 503794 1920581 := bbase (se 4 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 1920581 = 360109) (by norm_num)
theorem B642649 : Blo 503794 642649 := bbase (se 2 (by rfl) ⟨240993, by rfl⟩ : syracuseStep 642649 = 481987) (by norm_num)
theorem B1134197 : Blo 503794 1134197 := bbase (se 5 (by rfl) ⟨53165, by rfl⟩ : syracuseStep 1134197 = 106331) (by norm_num)
theorem B577145 : Blo 503794 577145 := bbase (se 2 (by rfl) ⟨216429, by rfl⟩ : syracuseStep 577145 = 432859) (by norm_num)
theorem B1298045 : Blo 503794 1298045 := bbase (se 3 (by rfl) ⟨243383, by rfl⟩ : syracuseStep 1298045 = 486767) (by norm_num)
theorem B609977 : Blo 503794 609977 := bbase (se 2 (by rfl) ⟨228741, by rfl⟩ : syracuseStep 609977 = 457483) (by norm_num)
theorem B1134269 : Blo 503794 1134269 := bbase (se 3 (by rfl) ⟨212675, by rfl⟩ : syracuseStep 1134269 = 425351) (by norm_num)
theorem B1134341 : Blo 503794 1134341 := bbase (se 4 (by rfl) ⟨106344, by rfl⟩ : syracuseStep 1134341 = 212689) (by norm_num)
theorem B1134413 : Blo 503794 1134413 := bbase (se 3 (by rfl) ⟨212702, by rfl⟩ : syracuseStep 1134413 = 425405) (by norm_num)
theorem B1625989 : Blo 503794 1625989 := bbase (se 4 (by rfl) ⟨152436, by rfl⟩ : syracuseStep 1625989 = 304873) (by norm_num)
theorem B1134485 : Blo 503794 1134485 := bbase (se 6 (by rfl) ⟨26589, by rfl⟩ : syracuseStep 1134485 = 53179) (by norm_num)
theorem B1134557 : Blo 503794 1134557 := bbase (se 3 (by rfl) ⟨212729, by rfl⟩ : syracuseStep 1134557 = 425459) (by norm_num)
theorem B512029 : Blo 503794 512029 := bbase (se 3 (by rfl) ⟨96005, by rfl⟩ : syracuseStep 512029 = 192011) (by norm_num)
theorem B1134629 : Blo 503794 1134629 := bbase (se 4 (by rfl) ⟨106371, by rfl⟩ : syracuseStep 1134629 = 212743) (by norm_num)
theorem B1134701 : Blo 503794 1134701 := bbase (se 3 (by rfl) ⟨212756, by rfl⟩ : syracuseStep 1134701 = 425513) (by norm_num)
theorem B1134773 : Blo 503794 1134773 := bbase (se 5 (by rfl) ⟨53192, by rfl⟩ : syracuseStep 1134773 = 106385) (by norm_num)
theorem B577729 : Blo 503794 577729 := bbase (se 2 (by rfl) ⟨216648, by rfl⟩ : syracuseStep 577729 = 433297) (by norm_num)
theorem B1462469 : Blo 503794 1462469 := bbase (se 4 (by rfl) ⟨137106, by rfl⟩ : syracuseStep 1462469 = 274213) (by norm_num)
theorem B1134845 : Blo 503794 1134845 := bbase (se 3 (by rfl) ⟨212783, by rfl⟩ : syracuseStep 1134845 = 425567) (by norm_num)
theorem B1134917 : Blo 503794 1134917 := bbase (se 4 (by rfl) ⟨106398, by rfl⟩ : syracuseStep 1134917 = 212797) (by norm_num)
theorem B2314565 : Blo 503794 2314565 := bbase (se 4 (by rfl) ⟨216990, by rfl⟩ : syracuseStep 2314565 = 433981) (by norm_num)
theorem B512345 : Blo 503794 512345 := bbase (se 2 (by rfl) ⟨192129, by rfl⟩ : syracuseStep 512345 = 384259) (by norm_num)
theorem B1134989 : Blo 503794 1134989 := bbase (se 3 (by rfl) ⟨212810, by rfl⟩ : syracuseStep 1134989 = 425621) (by norm_num)
theorem B1135061 : Blo 503794 1135061 := bbase (se 7 (by rfl) ⟨13301, by rfl⟩ : syracuseStep 1135061 = 26603) (by norm_num)
theorem B807413 : Blo 503794 807413 := bbase (se 5 (by rfl) ⟨37847, by rfl⟩ : syracuseStep 807413 = 75695) (by norm_num)
theorem B1364501 : Blo 503794 1364501 := bbase (se 6 (by rfl) ⟨31980, by rfl⟩ : syracuseStep 1364501 = 63961) (by norm_num)
theorem B1135133 : Blo 503794 1135133 := bbase (se 3 (by rfl) ⟨212837, by rfl⟩ : syracuseStep 1135133 = 425675) (by norm_num)
theorem B1135205 : Blo 503794 1135205 := bbase (se 4 (by rfl) ⟨106425, by rfl⟩ : syracuseStep 1135205 = 212851) (by norm_num)
theorem B1135277 : Blo 503794 1135277 := bbase (se 3 (by rfl) ⟨212864, by rfl⟩ : syracuseStep 1135277 = 425729) (by norm_num)
theorem B1921765 : Blo 503794 1921765 := bbase (se 4 (by rfl) ⟨180165, by rfl⟩ : syracuseStep 1921765 = 360331) (by norm_num)
theorem B1135349 : Blo 503794 1135349 := bbase (se 5 (by rfl) ⟨53219, by rfl⟩ : syracuseStep 1135349 = 106439) (by norm_num)
theorem B578345 : Blo 503794 578345 := bbase (se 2 (by rfl) ⟨216879, by rfl⟩ : syracuseStep 578345 = 433759) (by norm_num)
theorem B1135421 : Blo 503794 1135421 := bbase (se 3 (by rfl) ⟨212891, by rfl⟩ : syracuseStep 1135421 = 425783) (by norm_num)
theorem B1135493 : Blo 503794 1135493 := bbase (se 4 (by rfl) ⟨106452, by rfl⟩ : syracuseStep 1135493 = 212905) (by norm_num)
theorem B971669 : Blo 503794 971669 := bbase (se 6 (by rfl) ⟨22773, by rfl⟩ : syracuseStep 971669 = 45547) (by norm_num)
theorem B512929 : Blo 503794 512929 := bbase (se 2 (by rfl) ⟨192348, by rfl⟩ : syracuseStep 512929 = 384697) (by norm_num)
theorem B807869 : Blo 503794 807869 := bbase (se 3 (by rfl) ⟨151475, by rfl⟩ : syracuseStep 807869 = 302951) (by norm_num)
theorem B1135565 : Blo 503794 1135565 := bbase (se 3 (by rfl) ⟨212918, by rfl⟩ : syracuseStep 1135565 = 425837) (by norm_num)
theorem B1135637 : Blo 503794 1135637 := bbase (se 6 (by rfl) ⟨26616, by rfl⟩ : syracuseStep 1135637 = 53233) (by norm_num)
theorem B1922069 : Blo 503794 1922069 := bbase (se 6 (by rfl) ⟨45048, by rfl⟩ : syracuseStep 1922069 = 90097) (by norm_num)
theorem B1135709 : Blo 503794 1135709 := bbase (se 3 (by rfl) ⟨212945, by rfl⟩ : syracuseStep 1135709 = 425891) (by norm_num)
theorem B808093 : Blo 503794 808093 := bbase (se 3 (by rfl) ⟨151517, by rfl⟩ : syracuseStep 808093 = 303035) (by norm_num)
theorem B1135781 : Blo 503794 1135781 := bbase (se 4 (by rfl) ⟨106479, by rfl⟩ : syracuseStep 1135781 = 212959) (by norm_num)
theorem B808157 : Blo 503794 808157 := bbase (se 3 (by rfl) ⟨151529, by rfl⟩ : syracuseStep 808157 = 303059) (by norm_num)
theorem B2184421 : Blo 503794 2184421 := bbase (se 4 (by rfl) ⟨204789, by rfl⟩ : syracuseStep 2184421 = 409579) (by norm_num)
theorem B1135853 : Blo 503794 1135853 := bbase (se 3 (by rfl) ⟨212972, by rfl⟩ : syracuseStep 1135853 = 425945) (by norm_num)
theorem B1135925 : Blo 503794 1135925 := bbase (se 5 (by rfl) ⟨53246, by rfl⟩ : syracuseStep 1135925 = 106493) (by norm_num)
theorem B808285 : Blo 503794 808285 := bbase (se 3 (by rfl) ⟨151553, by rfl⟩ : syracuseStep 808285 = 303107) (by norm_num)
theorem B1135997 : Blo 503794 1135997 := bbase (se 3 (by rfl) ⟨212999, by rfl⟩ : syracuseStep 1135997 = 425999) (by norm_num)
theorem B1136069 : Blo 503794 1136069 := bbase (se 4 (by rfl) ⟨106506, by rfl⟩ : syracuseStep 1136069 = 213013) (by norm_num)
theorem B1136141 : Blo 503794 1136141 := bbase (se 3 (by rfl) ⟨213026, by rfl⟩ : syracuseStep 1136141 = 426053) (by norm_num)
theorem B2872853 : Blo 503794 2872853 := bbase (se 6 (by rfl) ⟨67332, by rfl⟩ : syracuseStep 2872853 = 134665) (by norm_num)
theorem B1136213 : Blo 503794 1136213 := bbase (se 8 (by rfl) ⟨6657, by rfl⟩ : syracuseStep 1136213 = 13315) (by norm_num)
theorem B1136285 : Blo 503794 1136285 := bbase (se 3 (by rfl) ⟨213053, by rfl⟩ : syracuseStep 1136285 = 426107) (by norm_num)
theorem B1824437 : Blo 503794 1824437 := bbase (se 5 (by rfl) ⟨85520, by rfl⟩ : syracuseStep 1824437 = 171041) (by norm_num)
theorem B1136357 : Blo 503794 1136357 := bbase (se 4 (by rfl) ⟨106533, by rfl⟩ : syracuseStep 1136357 = 213067) (by norm_num)
theorem B513793 : Blo 503794 513793 := bbase (se 2 (by rfl) ⟨192672, by rfl⟩ : syracuseStep 513793 = 385345) (by norm_num)
theorem B1136429 : Blo 503794 1136429 := bbase (se 3 (by rfl) ⟨213080, by rfl⟩ : syracuseStep 1136429 = 426161) (by norm_num)
theorem B1136501 : Blo 503794 1136501 := bbase (se 5 (by rfl) ⟨53273, by rfl⟩ : syracuseStep 1136501 = 106547) (by norm_num)
theorem B1136573 : Blo 503794 1136573 := bbase (se 3 (by rfl) ⟨213107, by rfl⟩ : syracuseStep 1136573 = 426215) (by norm_num)
theorem B2152453 : Blo 503794 2152453 := bbase (se 4 (by rfl) ⟨201792, by rfl⟩ : syracuseStep 2152453 = 403585) (by norm_num)
theorem B1136645 : Blo 503794 1136645 := bbase (se 4 (by rfl) ⟨106560, by rfl⟩ : syracuseStep 1136645 = 213121) (by norm_num)
theorem B1136717 : Blo 503794 1136717 := bbase (se 3 (by rfl) ⟨213134, by rfl⟩ : syracuseStep 1136717 = 426269) (by norm_num)
theorem B1824869 : Blo 503794 1824869 := bbase (se 4 (by rfl) ⟨171081, by rfl⟩ : syracuseStep 1824869 = 342163) (by norm_num)
theorem B1136789 : Blo 503794 1136789 := bbase (se 6 (by rfl) ⟨26643, by rfl⟩ : syracuseStep 1136789 = 53287) (by norm_num)
theorem B1136861 : Blo 503794 1136861 := bbase (se 3 (by rfl) ⟨213161, by rfl⟩ : syracuseStep 1136861 = 426323) (by norm_num)
theorem B1136933 : Blo 503794 1136933 := bbase (se 4 (by rfl) ⟨106587, by rfl⟩ : syracuseStep 1136933 = 213175) (by norm_num)
theorem B1137005 : Blo 503794 1137005 := bbase (se 3 (by rfl) ⟨213188, by rfl⟩ : syracuseStep 1137005 = 426377) (by norm_num)
theorem B514477 : Blo 503794 514477 := bbase (se 3 (by rfl) ⟨96464, by rfl⟩ : syracuseStep 514477 = 192929) (by norm_num)
theorem B1137077 : Blo 503794 1137077 := bbase (se 5 (by rfl) ⟨53300, by rfl⟩ : syracuseStep 1137077 = 106601) (by norm_num)
theorem B1137149 : Blo 503794 1137149 := bbase (se 3 (by rfl) ⟨213215, by rfl⟩ : syracuseStep 1137149 = 426431) (by norm_num)
theorem B809509 : Blo 503794 809509 := bbase (se 4 (by rfl) ⟨75891, by rfl⟩ : syracuseStep 809509 = 151783) (by norm_num)
theorem B1137221 : Blo 503794 1137221 := bbase (se 4 (by rfl) ⟨106614, by rfl⟩ : syracuseStep 1137221 = 213229) (by norm_num)
theorem B547465 : Blo 503794 547465 := bbase (se 2 (by rfl) ⟨205299, by rfl⟩ : syracuseStep 547465 = 410599) (by norm_num)
theorem B1137293 : Blo 503794 1137293 := bbase (se 3 (by rfl) ⟨213242, by rfl⟩ : syracuseStep 1137293 = 426485) (by norm_num)
theorem B1825445 : Blo 503794 1825445 := bbase (se 4 (by rfl) ⟨171135, by rfl⟩ : syracuseStep 1825445 = 342271) (by norm_num)
theorem B1137365 : Blo 503794 1137365 := bbase (se 7 (by rfl) ⟨13328, by rfl⟩ : syracuseStep 1137365 = 26657) (by norm_num)
theorem B1137437 : Blo 503794 1137437 := bbase (se 3 (by rfl) ⟨213269, by rfl⟩ : syracuseStep 1137437 = 426539) (by norm_num)
theorem B1137509 : Blo 503794 1137509 := bbase (se 4 (by rfl) ⟨106641, by rfl⟩ : syracuseStep 1137509 = 213283) (by norm_num)
theorem B1137581 : Blo 503794 1137581 := bbase (se 3 (by rfl) ⟨213296, by rfl⟩ : syracuseStep 1137581 = 426593) (by norm_num)
theorem B1137653 : Blo 503794 1137653 := bbase (se 5 (by rfl) ⟨53327, by rfl⟩ : syracuseStep 1137653 = 106655) (by norm_num)
theorem B1137725 : Blo 503794 1137725 := bbase (se 3 (by rfl) ⟨213323, by rfl⟩ : syracuseStep 1137725 = 426647) (by norm_num)
theorem B973901 : Blo 503794 973901 := bbase (se 3 (by rfl) ⟨182606, by rfl⟩ : syracuseStep 973901 = 365213) (by norm_num)
theorem B1924181 : Blo 503794 1924181 := bbase (se 8 (by rfl) ⟨11274, by rfl⟩ : syracuseStep 1924181 = 22549) (by norm_num)
theorem B1236061 : Blo 503794 1236061 := bbase (se 3 (by rfl) ⟨231761, by rfl⟩ : syracuseStep 1236061 = 463523) (by norm_num)
theorem B1137797 : Blo 503794 1137797 := bbase (se 4 (by rfl) ⟨106668, by rfl⟩ : syracuseStep 1137797 = 213337) (by norm_num)
theorem B810181 : Blo 503794 810181 := bbase (se 4 (by rfl) ⟨75954, by rfl⟩ : syracuseStep 810181 = 151909) (by norm_num)
theorem B1137869 : Blo 503794 1137869 := bbase (se 3 (by rfl) ⟨213350, by rfl⟩ : syracuseStep 1137869 = 426701) (by norm_num)
theorem B1137941 : Blo 503794 1137941 := bbase (se 6 (by rfl) ⟨26670, by rfl⟩ : syracuseStep 1137941 = 53341) (by norm_num)
theorem B1138013 : Blo 503794 1138013 := bbase (se 3 (by rfl) ⟨213377, by rfl⟩ : syracuseStep 1138013 = 426755) (by norm_num)
theorem B1924469 : Blo 503794 1924469 := bbase (se 5 (by rfl) ⟨90209, by rfl⟩ : syracuseStep 1924469 = 180419) (by norm_num)
theorem B1138085 : Blo 503794 1138085 := bbase (se 4 (by rfl) ⟨106695, by rfl⟩ : syracuseStep 1138085 = 213391) (by norm_num)
theorem B1564085 : Blo 503794 1564085 := bbase (se 5 (by rfl) ⟨73316, by rfl⟩ : syracuseStep 1564085 = 146633) (by norm_num)
theorem B1138157 : Blo 503794 1138157 := bbase (se 3 (by rfl) ⟨213404, by rfl⟩ : syracuseStep 1138157 = 426809) (by norm_num)
theorem B1138229 : Blo 503794 1138229 := bbase (se 5 (by rfl) ⟨53354, by rfl⟩ : syracuseStep 1138229 = 106709) (by norm_num)
theorem B2252405 : Blo 503794 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B1138301 : Blo 503794 1138301 := bbase (se 3 (by rfl) ⟨213431, by rfl⟩ : syracuseStep 1138301 = 426863) (by norm_num)
theorem B1138373 : Blo 503794 1138373 := bbase (se 4 (by rfl) ⟨106722, by rfl⟩ : syracuseStep 1138373 = 213445) (by norm_num)
theorem B1138445 : Blo 503794 1138445 := bbase (se 3 (by rfl) ⟨213458, by rfl⟩ : syracuseStep 1138445 = 426917) (by norm_num)
theorem B646969 : Blo 503794 646969 := bbase (se 2 (by rfl) ⟨242613, by rfl⟩ : syracuseStep 646969 = 485227) (by norm_num)
theorem B1138517 : Blo 503794 1138517 := bbase (se 9 (by rfl) ⟨3335, by rfl⟩ : syracuseStep 1138517 = 6671) (by norm_num)
theorem B1138589 : Blo 503794 1138589 := bbase (se 3 (by rfl) ⟨213485, by rfl⟩ : syracuseStep 1138589 = 426971) (by norm_num)
theorem B974749 : Blo 503794 974749 := bbase (se 3 (by rfl) ⟨182765, by rfl⟩ : syracuseStep 974749 = 365531) (by norm_num)
theorem B1138661 : Blo 503794 1138661 := bbase (se 4 (by rfl) ⟨106749, by rfl⟩ : syracuseStep 1138661 = 213499) (by norm_num)
theorem B1368037 : Blo 503794 1368037 := bbase (se 4 (by rfl) ⟨128253, by rfl⟩ : syracuseStep 1368037 = 256507) (by norm_num)
theorem B1138733 : Blo 503794 1138733 := bbase (se 3 (by rfl) ⟨213512, by rfl⟩ : syracuseStep 1138733 = 427025) (by norm_num)
theorem B1302589 : Blo 503794 1302589 := bbase (se 3 (by rfl) ⟨244235, by rfl⟩ : syracuseStep 1302589 = 488471) (by norm_num)
theorem B1138805 : Blo 503794 1138805 := bbase (se 5 (by rfl) ⟨53381, by rfl⟩ : syracuseStep 1138805 = 106763) (by norm_num)
theorem B647317 : Blo 503794 647317 := bbase (se 6 (by rfl) ⟨15171, by rfl⟩ : syracuseStep 647317 = 30343) (by norm_num)
theorem B811181 : Blo 503794 811181 := bbase (se 3 (by rfl) ⟨152096, by rfl⟩ : syracuseStep 811181 = 304193) (by norm_num)
theorem B1401013 : Blo 503794 1401013 := bbase (se 5 (by rfl) ⟨65672, by rfl⟩ : syracuseStep 1401013 = 131345) (by norm_num)
theorem B1138877 : Blo 503794 1138877 := bbase (se 3 (by rfl) ⟨213539, by rfl⟩ : syracuseStep 1138877 = 427079) (by norm_num)
theorem B1138949 : Blo 503794 1138949 := bbase (se 4 (by rfl) ⟨106776, by rfl⟩ : syracuseStep 1138949 = 213553) (by norm_num)
theorem B1139021 : Blo 503794 1139021 := bbase (se 3 (by rfl) ⟨213566, by rfl⟩ : syracuseStep 1139021 = 427133) (by norm_num)
theorem B3236213 : Blo 503794 3236213 := bbase (se 5 (by rfl) ⟨151697, by rfl⟩ : syracuseStep 3236213 = 303395) (by norm_num)
theorem B1139093 : Blo 503794 1139093 := bbase (se 6 (by rfl) ⟨26697, by rfl⟩ : syracuseStep 1139093 = 53395) (by norm_num)
theorem B1139165 : Blo 503794 1139165 := bbase (se 3 (by rfl) ⟨213593, by rfl⟩ : syracuseStep 1139165 = 427187) (by norm_num)
theorem B1925653 : Blo 503794 1925653 := bbase (se 6 (by rfl) ⟨45132, by rfl⟩ : syracuseStep 1925653 = 90265) (by norm_num)
theorem B1139237 : Blo 503794 1139237 := bbase (se 4 (by rfl) ⟨106803, by rfl⟩ : syracuseStep 1139237 = 213607) (by norm_num)
theorem B1139309 : Blo 503794 1139309 := bbase (se 3 (by rfl) ⟨213620, by rfl⟩ : syracuseStep 1139309 = 427241) (by norm_num)
theorem B1139381 : Blo 503794 1139381 := bbase (se 5 (by rfl) ⟨53408, by rfl⟩ : syracuseStep 1139381 = 106817) (by norm_num)
theorem B1139453 : Blo 503794 1139453 := bbase (se 3 (by rfl) ⟨213647, by rfl⟩ : syracuseStep 1139453 = 427295) (by norm_num)
theorem B1139525 : Blo 503794 1139525 := bbase (se 4 (by rfl) ⟨106830, by rfl⟩ : syracuseStep 1139525 = 213661) (by norm_num)
theorem B1925957 : Blo 503794 1925957 := bbase (se 4 (by rfl) ⟨180558, by rfl⟩ : syracuseStep 1925957 = 361117) (by norm_num)
theorem B1139597 : Blo 503794 1139597 := bbase (se 3 (by rfl) ⟨213674, by rfl⟩ : syracuseStep 1139597 = 427349) (by norm_num)
theorem B615325 : Blo 503794 615325 := bbase (se 3 (by rfl) ⟨115373, by rfl⟩ : syracuseStep 615325 = 230747) (by norm_num)
theorem B1041349 : Blo 503794 1041349 := bbase (se 4 (by rfl) ⟨97626, by rfl⟩ : syracuseStep 1041349 = 195253) (by norm_num)
theorem B1139669 : Blo 503794 1139669 := bbase (se 7 (by rfl) ⟨13355, by rfl⟩ : syracuseStep 1139669 = 26711) (by norm_num)
theorem B1139741 : Blo 503794 1139741 := bbase (se 3 (by rfl) ⟨213701, by rfl⟩ : syracuseStep 1139741 = 427403) (by norm_num)
theorem B910373 : Blo 503794 910373 := bbase (se 4 (by rfl) ⟨85347, by rfl⟩ : syracuseStep 910373 = 170695) (by norm_num)
theorem B1139813 : Blo 503794 1139813 := bbase (se 4 (by rfl) ⟨106857, by rfl⟩ : syracuseStep 1139813 = 213715) (by norm_num)
theorem B1139885 : Blo 503794 1139885 := bbase (se 3 (by rfl) ⟨213728, by rfl⟩ : syracuseStep 1139885 = 427457) (by norm_num)
theorem B1139957 : Blo 503794 1139957 := bbase (se 5 (by rfl) ⟨53435, by rfl⟩ : syracuseStep 1139957 = 106871) (by norm_num)
theorem B5203253 : Blo 503794 5203253 := bbase (se 5 (by rfl) ⟨243902, by rfl⟩ : syracuseStep 5203253 = 487805) (by norm_num)
theorem B1140029 : Blo 503794 1140029 := bbase (se 3 (by rfl) ⟨213755, by rfl⟩ : syracuseStep 1140029 = 427511) (by norm_num)
theorem B1140101 : Blo 503794 1140101 := bbase (se 4 (by rfl) ⟨106884, by rfl⟩ : syracuseStep 1140101 = 213769) (by norm_num)
theorem B1140173 : Blo 503794 1140173 := bbase (se 3 (by rfl) ⟨213782, by rfl⟩ : syracuseStep 1140173 = 427565) (by norm_num)
theorem B779773 : Blo 503794 779773 := bbase (se 3 (by rfl) ⟨146207, by rfl⟩ : syracuseStep 779773 = 292415) (by norm_num)
theorem B1730069 : Blo 503794 1730069 := bbase (se 6 (by rfl) ⟨40548, by rfl⟩ : syracuseStep 1730069 = 81097) (by norm_num)
theorem B1140245 : Blo 503794 1140245 := bbase (se 6 (by rfl) ⟨26724, by rfl⟩ : syracuseStep 1140245 = 53449) (by norm_num)
theorem B910877 : Blo 503794 910877 := bbase (se 3 (by rfl) ⟨170789, by rfl⟩ : syracuseStep 910877 = 341579) (by norm_num)
theorem B517685 : Blo 503794 517685 := bbase (se 5 (by rfl) ⟨24266, by rfl⟩ : syracuseStep 517685 = 48533) (by norm_num)
theorem B1140317 : Blo 503794 1140317 := bbase (se 3 (by rfl) ⟨213809, by rfl⟩ : syracuseStep 1140317 = 427619) (by norm_num)
theorem B812693 : Blo 503794 812693 := bbase (se 6 (by rfl) ⟨19047, by rfl⟩ : syracuseStep 812693 = 38095) (by norm_num)
theorem B1140389 : Blo 503794 1140389 := bbase (se 4 (by rfl) ⟨106911, by rfl⟩ : syracuseStep 1140389 = 213823) (by norm_num)
theorem B1435333 : Blo 503794 1435333 := bbase (se 4 (by rfl) ⟨134562, by rfl⟩ : syracuseStep 1435333 = 269125) (by norm_num)
theorem B1140461 : Blo 503794 1140461 := bbase (se 3 (by rfl) ⟨213836, by rfl⟩ : syracuseStep 1140461 = 427673) (by norm_num)
theorem B1140533 : Blo 503794 1140533 := bbase (se 5 (by rfl) ⟨53462, by rfl⟩ : syracuseStep 1140533 = 106925) (by norm_num)
theorem B1140605 : Blo 503794 1140605 := bbase (se 3 (by rfl) ⟨213863, by rfl⟩ : syracuseStep 1140605 = 427727) (by norm_num)
theorem B1140677 : Blo 503794 1140677 := bbase (se 4 (by rfl) ⟨106938, by rfl⟩ : syracuseStep 1140677 = 213877) (by norm_num)
theorem B4319189 : Blo 503794 4319189 := bbase (se 7 (by rfl) ⟨50615, by rfl⟩ : syracuseStep 4319189 = 101231) (by norm_num)
theorem B616405 : Blo 503794 616405 := bbase (se 7 (by rfl) ⟨7223, by rfl⟩ : syracuseStep 616405 = 14447) (by norm_num)
theorem B1140749 : Blo 503794 1140749 := bbase (se 3 (by rfl) ⟨213890, by rfl⟩ : syracuseStep 1140749 = 427781) (by norm_num)
theorem B1140821 : Blo 503794 1140821 := bbase (se 8 (by rfl) ⟨6684, by rfl⟩ : syracuseStep 1140821 = 13369) (by norm_num)
theorem B813149 : Blo 503794 813149 := bbase (se 3 (by rfl) ⟨152465, by rfl⟩ : syracuseStep 813149 = 304931) (by norm_num)
theorem B4843637 : Blo 503794 4843637 := bbase (se 5 (by rfl) ⟨227045, by rfl⟩ : syracuseStep 4843637 = 454091) (by norm_num)
theorem B1140893 : Blo 503794 1140893 := bbase (se 3 (by rfl) ⟨213917, by rfl⟩ : syracuseStep 1140893 = 427835) (by norm_num)
theorem B1140965 : Blo 503794 1140965 := bbase (se 4 (by rfl) ⟨106965, by rfl⟩ : syracuseStep 1140965 = 213931) (by norm_num)
theorem B911621 : Blo 503794 911621 := bbase (se 4 (by rfl) ⟨85464, by rfl⟩ : syracuseStep 911621 = 170929) (by norm_num)
theorem B1141037 : Blo 503794 1141037 := bbase (se 3 (by rfl) ⟨213944, by rfl⟩ : syracuseStep 1141037 = 427889) (by norm_num)
theorem B1141109 : Blo 503794 1141109 := bbase (se 5 (by rfl) ⟨53489, by rfl⟩ : syracuseStep 1141109 = 106979) (by norm_num)
theorem B1141181 : Blo 503794 1141181 := bbase (se 3 (by rfl) ⟨213971, by rfl⟩ : syracuseStep 1141181 = 427943) (by norm_num)
theorem B682445 : Blo 503794 682445 := bbase (se 3 (by rfl) ⟨127958, by rfl⟩ : syracuseStep 682445 = 255917) (by norm_num)
theorem B1141253 : Blo 503794 1141253 := bbase (se 4 (by rfl) ⟨106992, by rfl⟩ : syracuseStep 1141253 = 213985) (by norm_num)
theorem B1141325 : Blo 503794 1141325 := bbase (se 3 (by rfl) ⟨213998, by rfl⟩ : syracuseStep 1141325 = 427997) (by norm_num)
theorem B682597 : Blo 503794 682597 := bbase (se 4 (by rfl) ⟨63993, by rfl⟩ : syracuseStep 682597 = 127987) (by norm_num)
theorem B1141397 : Blo 503794 1141397 := bbase (se 6 (by rfl) ⟨26751, by rfl⟩ : syracuseStep 1141397 = 53503) (by norm_num)
theorem B1141469 : Blo 503794 1141469 := bbase (se 3 (by rfl) ⟨214025, by rfl⟩ : syracuseStep 1141469 = 428051) (by norm_num)
theorem B1075997 : Blo 503794 1075997 := bbase (se 3 (by rfl) ⟨201749, by rfl⟩ : syracuseStep 1075997 = 403499) (by norm_num)
theorem B1141541 : Blo 503794 1141541 := bbase (se 4 (by rfl) ⟨107019, by rfl⟩ : syracuseStep 1141541 = 214039) (by norm_num)
theorem B1141613 : Blo 503794 1141613 := bbase (se 3 (by rfl) ⟨214052, by rfl⟩ : syracuseStep 1141613 = 428105) (by norm_num)
theorem B2157461 : Blo 503794 2157461 := bbase (se 6 (by rfl) ⟨50565, by rfl⟩ : syracuseStep 2157461 = 101131) (by norm_num)
theorem B1076141 : Blo 503794 1076141 := bbase (se 3 (by rfl) ⟨201776, by rfl⟩ : syracuseStep 1076141 = 403553) (by norm_num)
theorem B1141685 : Blo 503794 1141685 := bbase (se 5 (by rfl) ⟨53516, by rfl⟩ : syracuseStep 1141685 = 107033) (by norm_num)
theorem B1141757 : Blo 503794 1141757 := bbase (se 3 (by rfl) ⟨214079, by rfl⟩ : syracuseStep 1141757 = 428159) (by norm_num)
theorem B683029 : Blo 503794 683029 := bbase (se 6 (by rfl) ⟨16008, by rfl⟩ : syracuseStep 683029 = 32017) (by norm_num)
theorem B650273 : Blo 503794 650273 := bbase (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) (by norm_num)
theorem B519229 : Blo 503794 519229 := bbase (se 3 (by rfl) ⟨97355, by rfl⟩ : syracuseStep 519229 = 194711) (by norm_num)
theorem B1141829 : Blo 503794 1141829 := bbase (se 4 (by rfl) ⟨107046, by rfl⟩ : syracuseStep 1141829 = 214093) (by norm_num)
theorem B1141901 : Blo 503794 1141901 := bbase (se 3 (by rfl) ⟨214106, by rfl⟩ : syracuseStep 1141901 = 428213) (by norm_num)
theorem B4942997 : Blo 503794 4942997 := bbase (se 6 (by rfl) ⟨115851, by rfl⟩ : syracuseStep 4942997 = 231703) (by norm_num)
theorem B2157749 : Blo 503794 2157749 := bbase (se 5 (by rfl) ⟨101144, by rfl⟩ : syracuseStep 2157749 = 202289) (by norm_num)
theorem B1141973 : Blo 503794 1141973 := bbase (se 7 (by rfl) ⟨13382, by rfl⟩ : syracuseStep 1141973 = 26765) (by norm_num)
theorem B2551013 : Blo 503794 2551013 := bbase (se 4 (by rfl) ⟨239157, by rfl⟩ : syracuseStep 2551013 = 478315) (by norm_num)
theorem B683245 : Blo 503794 683245 := bbase (se 3 (by rfl) ⟨128108, by rfl⟩ : syracuseStep 683245 = 256217) (by norm_num)
theorem B3239189 : Blo 503794 3239189 := bbase (se 6 (by rfl) ⟨75918, by rfl⟩ : syracuseStep 3239189 = 151837) (by norm_num)
theorem B1142045 : Blo 503794 1142045 := bbase (se 3 (by rfl) ⟨214133, by rfl⟩ : syracuseStep 1142045 = 428267) (by norm_num)
theorem B1142117 : Blo 503794 1142117 := bbase (se 4 (by rfl) ⟨107073, by rfl⟩ : syracuseStep 1142117 = 214147) (by norm_num)
theorem B1142189 : Blo 503794 1142189 := bbase (se 3 (by rfl) ⟨214160, by rfl⟩ : syracuseStep 1142189 = 428321) (by norm_num)
theorem B1142261 : Blo 503794 1142261 := bbase (se 5 (by rfl) ⟨53543, by rfl⟩ : syracuseStep 1142261 = 107087) (by norm_num)
theorem B1142333 : Blo 503794 1142333 := bbase (se 3 (by rfl) ⟨214187, by rfl⟩ : syracuseStep 1142333 = 428375) (by norm_num)
theorem B1142405 : Blo 503794 1142405 := bbase (se 4 (by rfl) ⟨107100, by rfl⟩ : syracuseStep 1142405 = 214201) (by norm_num)
theorem B1076885 : Blo 503794 1076885 := bbase (se 6 (by rfl) ⟨25239, by rfl⟩ : syracuseStep 1076885 = 50479) (by norm_num)
theorem B913069 : Blo 503794 913069 := bbase (se 3 (by rfl) ⟨171200, by rfl⟩ : syracuseStep 913069 = 342401) (by norm_num)
theorem B1142477 : Blo 503794 1142477 := bbase (se 3 (by rfl) ⟨214214, by rfl⟩ : syracuseStep 1142477 = 428429) (by norm_num)
theorem B913141 : Blo 503794 913141 := bbase (se 5 (by rfl) ⟨42803, by rfl⟩ : syracuseStep 913141 = 85607) (by norm_num)
theorem B2158501 : Blo 503794 2158501 := bbase (se 4 (by rfl) ⟨202359, by rfl⟩ : syracuseStep 2158501 = 404719) (by norm_num)
theorem B1372069 : Blo 503794 1372069 := bbase (se 4 (by rfl) ⟨128631, by rfl⟩ : syracuseStep 1372069 = 257263) (by norm_num)
theorem B1372373 : Blo 503794 1372373 := bbase (se 7 (by rfl) ⟨16082, by rfl⟩ : syracuseStep 1372373 = 32165) (by norm_num)
theorem B913645 : Blo 503794 913645 := bbase (se 3 (by rfl) ⟨171308, by rfl⟩ : syracuseStep 913645 = 342617) (by norm_num)
theorem B1077637 : Blo 503794 1077637 := bbase (se 4 (by rfl) ⟨101028, by rfl⟩ : syracuseStep 1077637 = 202057) (by norm_num)
theorem B3830165 : Blo 503794 3830165 := bbase (se 6 (by rfl) ⟨89769, by rfl⟩ : syracuseStep 3830165 = 179539) (by norm_num)
theorem B1438181 : Blo 503794 1438181 := bbase (se 4 (by rfl) ⟨134829, by rfl⟩ : syracuseStep 1438181 = 269659) (by norm_num)
theorem B2552309 : Blo 503794 2552309 := bbase (se 5 (by rfl) ⟨119639, by rfl⟩ : syracuseStep 2552309 = 239279) (by norm_num)
theorem B1077781 : Blo 503794 1077781 := bbase (se 6 (by rfl) ⟨25260, by rfl⟩ : syracuseStep 1077781 = 50521) (by norm_num)
theorem B1700405 : Blo 503794 1700405 := bbase (se 5 (by rfl) ⟨79706, by rfl⟩ : syracuseStep 1700405 = 159413) (by norm_num)
theorem B2159237 : Blo 503794 2159237 := bbase (se 4 (by rfl) ⟨202428, by rfl⟩ : syracuseStep 2159237 = 404857) (by norm_num)
theorem B914309 : Blo 503794 914309 := bbase (se 4 (by rfl) ⟨85716, by rfl⟩ : syracuseStep 914309 = 171433) (by norm_num)
theorem B1078157 : Blo 503794 1078157 := bbase (se 3 (by rfl) ⟨202154, by rfl⟩ : syracuseStep 1078157 = 404309) (by norm_num)
theorem B1700837 : Blo 503794 1700837 := bbase (se 4 (by rfl) ⟨159453, by rfl⟩ : syracuseStep 1700837 = 318907) (by norm_num)
theorem B717997 : Blo 503794 717997 := bbase (se 3 (by rfl) ⟨134624, by rfl⟩ : syracuseStep 717997 = 269249) (by norm_num)
theorem B1078525 : Blo 503794 1078525 := bbase (se 3 (by rfl) ⟨202223, by rfl⟩ : syracuseStep 1078525 = 404447) (by norm_num)
theorem B1701269 : Blo 503794 1701269 := bbase (se 6 (by rfl) ⟨39873, by rfl⟩ : syracuseStep 1701269 = 79747) (by norm_num)
theorem B2880917 : Blo 503794 2880917 := bbase (se 6 (by rfl) ⟨67521, by rfl⟩ : syracuseStep 2880917 = 135043) (by norm_num)
theorem B1275365 : Blo 503794 1275365 := bbase (se 4 (by rfl) ⟨119565, by rfl⟩ : syracuseStep 1275365 = 239131) (by norm_num)
theorem B1439365 : Blo 503794 1439365 := bbase (se 4 (by rfl) ⟨134940, by rfl⟩ : syracuseStep 1439365 = 269881) (by norm_num)
theorem B718589 : Blo 503794 718589 := bbase (se 3 (by rfl) ⟨134735, by rfl⟩ : syracuseStep 718589 = 269471) (by norm_num)
theorem B2553605 : Blo 503794 2553605 := bbase (se 4 (by rfl) ⟨239400, by rfl⟩ : syracuseStep 2553605 = 478801) (by norm_num)
theorem B1439525 : Blo 503794 1439525 := bbase (se 4 (by rfl) ⟨134955, by rfl⟩ : syracuseStep 1439525 = 269911) (by norm_num)
theorem B1275709 : Blo 503794 1275709 := bbase (se 3 (by rfl) ⟨239195, by rfl⟩ : syracuseStep 1275709 = 478391) (by norm_num)
theorem B1701701 : Blo 503794 1701701 := bbase (se 4 (by rfl) ⟨159534, by rfl⟩ : syracuseStep 1701701 = 319069) (by norm_num)
theorem B718669 : Blo 503794 718669 := bbase (se 3 (by rfl) ⟨134750, by rfl⟩ : syracuseStep 718669 = 269501) (by norm_num)
theorem B1275821 : Blo 503794 1275821 := bbase (se 3 (by rfl) ⟨239216, by rfl⟩ : syracuseStep 1275821 = 478433) (by norm_num)
theorem B718789 : Blo 503794 718789 := bbase (se 4 (by rfl) ⟨67386, by rfl⟩ : syracuseStep 718789 = 134773) (by norm_num)
theorem B1439765 : Blo 503794 1439765 := bbase (se 6 (by rfl) ⟨33744, by rfl⟩ : syracuseStep 1439765 = 67489) (by norm_num)
theorem B718885 : Blo 503794 718885 := bbase (se 4 (by rfl) ⟨67395, by rfl⟩ : syracuseStep 718885 = 134791) (by norm_num)
theorem B1276013 : Blo 503794 1276013 := bbase (se 3 (by rfl) ⟨239252, by rfl⟩ : syracuseStep 1276013 = 478505) (by norm_num)
theorem B1210573 : Blo 503794 1210573 := bbase (se 3 (by rfl) ⟨226982, by rfl⟩ : syracuseStep 1210573 = 453965) (by norm_num)
theorem B1439957 : Blo 503794 1439957 := bbase (se 7 (by rfl) ⟨16874, by rfl⟩ : syracuseStep 1439957 = 33749) (by norm_num)
theorem B1702133 : Blo 503794 1702133 := bbase (se 5 (by rfl) ⟨79787, by rfl⟩ : syracuseStep 1702133 = 159575) (by norm_num)
theorem B1210621 : Blo 503794 1210621 := bbase (se 3 (by rfl) ⟨226991, by rfl⟩ : syracuseStep 1210621 = 453983) (by norm_num)
theorem B850189 : Blo 503794 850189 := bbase (se 3 (by rfl) ⟨159410, by rfl⟩ : syracuseStep 850189 = 318821) (by norm_num)
theorem B2193685 : Blo 503794 2193685 := bbase (se 6 (by rfl) ⟨51414, by rfl⟩ : syracuseStep 2193685 = 102829) (by norm_num)
theorem B850277 : Blo 503794 850277 := bbase (se 4 (by rfl) ⟨79713, by rfl⟩ : syracuseStep 850277 = 159427) (by norm_num)
theorem B1276357 : Blo 503794 1276357 := bbase (se 4 (by rfl) ⟨119658, by rfl⟩ : syracuseStep 1276357 = 239317) (by norm_num)
theorem B850405 : Blo 503794 850405 := bbase (se 4 (by rfl) ⟨79725, by rfl⟩ : syracuseStep 850405 = 159451) (by norm_num)
theorem B1735157 : Blo 503794 1735157 := bbase (se 5 (by rfl) ⟨81335, by rfl⟩ : syracuseStep 1735157 = 162671) (by norm_num)
theorem B2423317 : Blo 503794 2423317 := bbase (se 6 (by rfl) ⟨56796, by rfl⟩ : syracuseStep 2423317 = 113593) (by norm_num)
theorem B719381 : Blo 503794 719381 := bbase (se 6 (by rfl) ⟨16860, by rfl⟩ : syracuseStep 719381 = 33721) (by norm_num)
theorem B1276469 : Blo 503794 1276469 := bbase (se 5 (by rfl) ⟨59834, by rfl⟩ : syracuseStep 1276469 = 119669) (by norm_num)
theorem B2882101 : Blo 503794 2882101 := bbase (se 5 (by rfl) ⟨135098, by rfl⟩ : syracuseStep 2882101 = 270197) (by norm_num)
theorem B850493 : Blo 503794 850493 := bbase (se 3 (by rfl) ⟨159467, by rfl⟩ : syracuseStep 850493 = 318935) (by norm_num)
theorem B1702565 : Blo 503794 1702565 := bbase (se 4 (by rfl) ⟨159615, by rfl⟩ : syracuseStep 1702565 = 319231) (by norm_num)
theorem B850621 : Blo 503794 850621 := bbase (se 3 (by rfl) ⟨159491, by rfl⟩ : syracuseStep 850621 = 318983) (by norm_num)
theorem B555709 : Blo 503794 555709 := bbase (se 3 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 555709 = 208391) (by norm_num)
theorem B1080029 : Blo 503794 1080029 := bbase (se 3 (by rfl) ⟨202505, by rfl⟩ : syracuseStep 1080029 = 405011) (by norm_num)
theorem B1276661 : Blo 503794 1276661 := bbase (se 5 (by rfl) ⟨59843, by rfl⟩ : syracuseStep 1276661 = 119687) (by norm_num)
theorem B850709 : Blo 503794 850709 := bbase (se 6 (by rfl) ⟨19938, by rfl⟩ : syracuseStep 850709 = 39877) (by norm_num)
theorem B1211237 : Blo 503794 1211237 := bbase (se 4 (by rfl) ⟨113553, by rfl⟩ : syracuseStep 1211237 = 227107) (by norm_num)
theorem B1080173 : Blo 503794 1080173 := bbase (se 3 (by rfl) ⟨202532, by rfl⟩ : syracuseStep 1080173 = 405065) (by norm_num)
theorem B850837 : Blo 503794 850837 := bbase (se 6 (by rfl) ⟨19941, by rfl⟩ : syracuseStep 850837 = 39883) (by norm_num)
theorem B850925 : Blo 503794 850925 := bbase (se 3 (by rfl) ⟨159548, by rfl⟩ : syracuseStep 850925 = 319097) (by norm_num)
theorem B818165 : Blo 503794 818165 := bbase (se 5 (by rfl) ⟨38351, by rfl⟩ : syracuseStep 818165 = 76703) (by norm_num)
theorem B2554901 : Blo 503794 2554901 := bbase (se 6 (by rfl) ⟨59880, by rfl⟩ : syracuseStep 2554901 = 119761) (by norm_num)
theorem B719933 : Blo 503794 719933 := bbase (se 3 (by rfl) ⟨134987, by rfl⟩ : syracuseStep 719933 = 269975) (by norm_num)
theorem B1277005 : Blo 503794 1277005 := bbase (se 3 (by rfl) ⟨239438, by rfl⟩ : syracuseStep 1277005 = 478877) (by norm_num)
theorem B1702997 : Blo 503794 1702997 := bbase (se 8 (by rfl) ⟨9978, by rfl⟩ : syracuseStep 1702997 = 19957) (by norm_num)
theorem B851053 : Blo 503794 851053 := bbase (se 3 (by rfl) ⟨159572, by rfl⟩ : syracuseStep 851053 = 319145) (by norm_num)
theorem B1440949 : Blo 503794 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B1211581 : Blo 503794 1211581 := bbase (se 3 (by rfl) ⟨227171, by rfl⟩ : syracuseStep 1211581 = 454343) (by norm_num)
theorem B1277117 : Blo 503794 1277117 := bbase (se 3 (by rfl) ⟨239459, by rfl⟩ : syracuseStep 1277117 = 478919) (by norm_num)
theorem B851141 : Blo 503794 851141 := bbase (se 4 (by rfl) ⟨79794, by rfl⟩ : syracuseStep 851141 = 159589) (by norm_num)
theorem B1080533 : Blo 503794 1080533 := bbase (se 7 (by rfl) ⟨12662, by rfl⟩ : syracuseStep 1080533 = 25325) (by norm_num)
theorem B851269 : Blo 503794 851269 := bbase (se 4 (by rfl) ⟨79806, by rfl⟩ : syracuseStep 851269 = 159613) (by norm_num)
theorem B1277309 : Blo 503794 1277309 := bbase (se 3 (by rfl) ⟨239495, by rfl⟩ : syracuseStep 1277309 = 478991) (by norm_num)
theorem B851357 : Blo 503794 851357 := bbase (se 3 (by rfl) ⟨159629, by rfl⟩ : syracuseStep 851357 = 319259) (by norm_num)
theorem B1211813 : Blo 503794 1211813 := bbase (se 4 (by rfl) ⟨113607, by rfl⟩ : syracuseStep 1211813 = 227215) (by norm_num)
theorem B1703429 : Blo 503794 1703429 := bbase (se 4 (by rfl) ⟨159696, by rfl⟩ : syracuseStep 1703429 = 319393) (by norm_num)
theorem B851485 : Blo 503794 851485 := bbase (se 3 (by rfl) ⟨159653, by rfl⟩ : syracuseStep 851485 = 319307) (by norm_num)
theorem B1212005 : Blo 503794 1212005 := bbase (se 4 (by rfl) ⟨113625, by rfl⟩ : syracuseStep 1212005 = 227251) (by norm_num)
theorem B851573 : Blo 503794 851573 := bbase (se 5 (by rfl) ⟨39917, by rfl⟩ : syracuseStep 851573 = 79835) (by norm_num)
theorem B1277653 : Blo 503794 1277653 := bbase (se 7 (by rfl) ⟨14972, by rfl⟩ : syracuseStep 1277653 = 29945) (by norm_num)
theorem B2457317 : Blo 503794 2457317 := bbase (se 4 (by rfl) ⟨230373, by rfl⟩ : syracuseStep 2457317 = 460747) (by norm_num)
theorem B851701 : Blo 503794 851701 := bbase (se 5 (by rfl) ⟨39923, by rfl⟩ : syracuseStep 851701 = 79847) (by norm_num)
theorem B720685 : Blo 503794 720685 := bbase (se 3 (by rfl) ⟨135128, by rfl⟩ : syracuseStep 720685 = 270257) (by norm_num)
theorem B1277765 : Blo 503794 1277765 := bbase (se 4 (by rfl) ⟨119790, by rfl⟩ : syracuseStep 1277765 = 239581) (by norm_num)
theorem B851789 : Blo 503794 851789 := bbase (se 3 (by rfl) ⟨159710, by rfl⟩ : syracuseStep 851789 = 319421) (by norm_num)
theorem B2162533 : Blo 503794 2162533 := bbase (se 4 (by rfl) ⟨202737, by rfl⟩ : syracuseStep 2162533 = 405475) (by norm_num)
theorem B1212293 : Blo 503794 1212293 := bbase (se 4 (by rfl) ⟨113652, by rfl⟩ : syracuseStep 1212293 = 227305) (by norm_num)
theorem B1703861 : Blo 503794 1703861 := bbase (se 5 (by rfl) ⟨79868, by rfl⟩ : syracuseStep 1703861 = 159737) (by norm_num)
theorem B851917 : Blo 503794 851917 := bbase (se 3 (by rfl) ⟨159734, by rfl⟩ : syracuseStep 851917 = 319469) (by norm_num)
theorem B1310717 : Blo 503794 1310717 := bbase (se 3 (by rfl) ⟨245759, by rfl⟩ : syracuseStep 1310717 = 491519) (by norm_num)
theorem B851971 : Blo 503794 851971 := bstep (se 1 (by rfl) ⟨638978, by rfl⟩ : syracuseStep 851971 = 1277957) B1277957
theorem B720913 : Blo 503794 720913 := bstep (se 2 (by rfl) ⟨270342, by rfl⟩ : syracuseStep 720913 = 540685) B540685
theorem B720947 : Blo 503794 720947 := bstep (se 1 (by rfl) ⟨540710, by rfl⟩ : syracuseStep 720947 = 1081421) B1081421
theorem B1736785 : Blo 503794 1736785 := bstep (se 2 (by rfl) ⟨651294, by rfl⟩ : syracuseStep 1736785 = 1302589) B1302589
theorem B52396145 : Blo 503794 52396145 := bstep (se 2 (by rfl) ⟨19648554, by rfl⟩ : syracuseStep 52396145 = 39297109) B39297109
theorem B1704077 : Blo 503794 1704077 := bstep (se 3 (by rfl) ⟨319514, by rfl⟩ : syracuseStep 1704077 = 639029) B639029
theorem B852113 : Blo 503794 852113 := bstep (se 2 (by rfl) ⟨319542, by rfl⟩ : syracuseStep 852113 = 639085) B639085
theorem B1704131 : Blo 503794 1704131 := bstep (se 1 (by rfl) ⟨1278098, by rfl⟩ : syracuseStep 1704131 = 2556197) B2556197
theorem B3834053 : Blo 503794 3834053 := bstep (se 4 (by rfl) ⟨359442, by rfl⟩ : syracuseStep 3834053 = 718885) B718885
theorem B1868017 : Blo 503794 1868017 := bstep (se 2 (by rfl) ⟨700506, by rfl⟩ : syracuseStep 1868017 = 1401013) B1401013
theorem B852241 : Blo 503794 852241 := bstep (se 2 (by rfl) ⟨319590, by rfl⟩ : syracuseStep 852241 = 639181) B639181
theorem B852275 : Blo 503794 852275 := bstep (se 1 (by rfl) ⟨639206, by rfl⟩ : syracuseStep 852275 = 1278413) B1278413
theorem B1442225 : Blo 503794 1442225 := bstep (se 2 (by rfl) ⟨540834, by rfl⟩ : syracuseStep 1442225 = 1081669) B1081669
theorem B852403 : Blo 503794 852403 := bstep (se 1 (by rfl) ⟨639302, by rfl⟩ : syracuseStep 852403 = 1278605) B1278605
theorem B2163149 : Blo 503794 2163149 := bstep (se 3 (by rfl) ⟨405590, by rfl⟩ : syracuseStep 2163149 = 811181) B811181
theorem B1704401 : Blo 503794 1704401 := bstep (se 2 (by rfl) ⟨639150, by rfl⟩ : syracuseStep 1704401 = 1278301) B1278301
theorem B1540561 : Blo 503794 1540561 := bstep (se 2 (by rfl) ⟨577710, by rfl⟩ : syracuseStep 1540561 = 1155421) B1155421
theorem B2425315 : Blo 503794 2425315 := bstep (se 1 (by rfl) ⟨1818986, by rfl⟩ : syracuseStep 2425315 = 3637973) B3637973
theorem B3899917 : Blo 503794 3899917 := bstep (se 3 (by rfl) ⟨731234, by rfl⟩ : syracuseStep 3899917 = 1462469) B1462469
theorem B852545 : Blo 503794 852545 := bstep (se 2 (by rfl) ⟨319704, by rfl⟩ : syracuseStep 852545 = 639409) B639409
theorem B721505 : Blo 503794 721505 := bstep (se 2 (by rfl) ⟨270564, by rfl⟩ : syracuseStep 721505 = 541129) B541129
theorem B721585 : Blo 503794 721585 := bstep (se 2 (by rfl) ⟨270594, by rfl⟩ : syracuseStep 721585 = 541189) B541189
theorem B852673 : Blo 503794 852673 := bstep (se 2 (by rfl) ⟨319752, by rfl⟩ : syracuseStep 852673 = 639505) B639505
theorem B852707 : Blo 503794 852707 := bstep (se 1 (by rfl) ⟨639530, by rfl⟩ : syracuseStep 852707 = 1279061) B1279061
theorem B1278737 : Blo 503794 1278737 := bstep (se 2 (by rfl) ⟨479526, by rfl⟩ : syracuseStep 1278737 = 959053) B959053
theorem B1278787 : Blo 503794 1278787 := bstep (se 1 (by rfl) ⟨959090, by rfl⟩ : syracuseStep 1278787 = 1918181) B1918181
theorem B852835 : Blo 503794 852835 := bstep (se 1 (by rfl) ⟨639626, by rfl⟩ : syracuseStep 852835 = 1279253) B1279253
theorem B3081073 : Blo 503794 3081073 := bstep (se 2 (by rfl) ⟨1155402, by rfl⟩ : syracuseStep 3081073 = 2310805) B2310805
theorem B1278929 : Blo 503794 1278929 := bstep (se 2 (by rfl) ⟨479598, by rfl⟩ : syracuseStep 1278929 = 959197) B959197
theorem B1704941 : Blo 503794 1704941 := bstep (se 3 (by rfl) ⟨319676, by rfl⟩ : syracuseStep 1704941 = 639353) B639353
theorem B852977 : Blo 503794 852977 := bstep (se 2 (by rfl) ⟨319866, by rfl⟩ : syracuseStep 852977 = 639733) B639733
theorem B1704995 : Blo 503794 1704995 := bstep (se 1 (by rfl) ⟨1278746, by rfl⟩ : syracuseStep 1704995 = 2557493) B2557493
theorem B1442897 : Blo 503794 1442897 := bstep (se 2 (by rfl) ⟨541086, by rfl⟩ : syracuseStep 1442897 = 1082173) B1082173
theorem B853105 : Blo 503794 853105 := bstep (se 2 (by rfl) ⟨319914, by rfl⟩ : syracuseStep 853105 = 639829) B639829
theorem B853139 : Blo 503794 853139 := bstep (se 1 (by rfl) ⟨639854, by rfl⟩ : syracuseStep 853139 = 1279709) B1279709
theorem B1082531 : Blo 503794 1082531 := bstep (se 1 (by rfl) ⟨811898, by rfl⟩ : syracuseStep 1082531 = 1623797) B1623797
theorem B820433 : Blo 503794 820433 := bstep (se 2 (by rfl) ⟨307662, by rfl⟩ : syracuseStep 820433 = 615325) B615325
theorem B2884835 : Blo 503794 2884835 := bstep (se 1 (by rfl) ⟨2163626, by rfl⟩ : syracuseStep 2884835 = 4327253) B4327253
theorem B2557169 : Blo 503794 2557169 := bstep (se 2 (by rfl) ⟨958938, by rfl⟩ : syracuseStep 2557169 = 1917877) B1917877
theorem B853267 : Blo 503794 853267 := bstep (se 1 (by rfl) ⟨639950, by rfl⟩ : syracuseStep 853267 = 1279901) B1279901
theorem B1705265 : Blo 503794 1705265 := bstep (se 2 (by rfl) ⟨639474, by rfl⟩ : syracuseStep 1705265 = 1278949) B1278949
theorem B853409 : Blo 503794 853409 := bstep (se 2 (by rfl) ⟨320028, by rfl⟩ : syracuseStep 853409 = 640057) B640057
theorem B722371 : Blo 503794 722371 := bstep (se 1 (by rfl) ⟨541778, by rfl⟩ : syracuseStep 722371 = 1083557) B1083557
theorem B11699653 : Blo 503794 11699653 := bstep (se 4 (by rfl) ⟨1096842, by rfl⟩ : syracuseStep 11699653 = 2193685) B2193685
theorem B1541585 : Blo 503794 1541585 := bstep (se 2 (by rfl) ⟨578094, by rfl⟩ : syracuseStep 1541585 = 1156189) B1156189
theorem B853537 : Blo 503794 853537 := bstep (se 2 (by rfl) ⟨320076, by rfl⟩ : syracuseStep 853537 = 640153) B640153
theorem B853571 : Blo 503794 853571 := bstep (se 1 (by rfl) ⟨640178, by rfl⟩ : syracuseStep 853571 = 1280357) B1280357
theorem B3245645 : Blo 503794 3245645 := bstep (se 3 (by rfl) ⟨608558, by rfl⟩ : syracuseStep 3245645 = 1217117) B1217117
theorem B2426545 : Blo 503794 2426545 := bstep (se 2 (by rfl) ⟨909954, by rfl⟩ : syracuseStep 2426545 = 1819909) B1819909
theorem B853699 : Blo 503794 853699 := bstep (se 1 (by rfl) ⟨640274, by rfl⟩ : syracuseStep 853699 = 1280549) B1280549
theorem B1705805 : Blo 503794 1705805 := bstep (se 3 (by rfl) ⟨319838, by rfl⟩ : syracuseStep 1705805 = 639677) B639677
theorem B853841 : Blo 503794 853841 := bstep (se 2 (by rfl) ⟨320190, by rfl⟩ : syracuseStep 853841 = 640381) B640381
theorem B1443683 : Blo 503794 1443683 := bstep (se 1 (by rfl) ⟨1082762, by rfl⟩ : syracuseStep 1443683 = 2165525) B2165525
theorem B1705859 : Blo 503794 1705859 := bstep (se 1 (by rfl) ⟨1279394, by rfl⟩ : syracuseStep 1705859 = 2558789) B2558789
theorem B2918285 : Blo 503794 2918285 := bstep (se 3 (by rfl) ⟨547178, by rfl⟩ : syracuseStep 2918285 = 1094357) B1094357
theorem B722849 : Blo 503794 722849 := bstep (se 2 (by rfl) ⟨271068, by rfl⟩ : syracuseStep 722849 = 542137) B542137
theorem B1279921 : Blo 503794 1279921 := bstep (se 2 (by rfl) ⟨479970, by rfl⟩ : syracuseStep 1279921 = 959941) B959941
theorem B853969 : Blo 503794 853969 := bstep (se 2 (by rfl) ⟨320238, by rfl⟩ : syracuseStep 853969 = 640477) B640477
theorem B755699 : Blo 503794 755699 := bstep (se 1 (by rfl) ⟨566774, by rfl⟩ : syracuseStep 755699 = 1133549) B1133549
theorem B854003 : Blo 503794 854003 := bstep (se 1 (by rfl) ⟨640502, by rfl⟩ : syracuseStep 854003 = 1281005) B1281005
theorem B755729 : Blo 503794 755729 := bstep (se 2 (by rfl) ⟨283398, by rfl⟩ : syracuseStep 755729 = 566797) B566797
theorem B722963 : Blo 503794 722963 := bstep (se 1 (by rfl) ⟨542222, by rfl⟩ : syracuseStep 722963 = 1084445) B1084445
theorem B755747 : Blo 503794 755747 := bstep (se 1 (by rfl) ⟨566810, by rfl⟩ : syracuseStep 755747 = 1133621) B1133621
theorem B755777 : Blo 503794 755777 := bstep (se 2 (by rfl) ⟨283416, by rfl⟩ : syracuseStep 755777 = 566833) B566833
theorem B755795 : Blo 503794 755795 := bstep (se 1 (by rfl) ⟨566846, by rfl⟩ : syracuseStep 755795 = 1133693) B1133693
theorem B1542253 : Blo 503794 1542253 := bstep (se 3 (by rfl) ⟨289172, by rfl⟩ : syracuseStep 1542253 = 578345) B578345
theorem B755825 : Blo 503794 755825 := bstep (se 2 (by rfl) ⟨283434, by rfl⟩ : syracuseStep 755825 = 566869) B566869
theorem B854131 : Blo 503794 854131 := bstep (se 1 (by rfl) ⟨640598, by rfl⟩ : syracuseStep 854131 = 1281197) B1281197
theorem B755843 : Blo 503794 755843 := bstep (se 1 (by rfl) ⟨566882, by rfl⟩ : syracuseStep 755843 = 1133765) B1133765
theorem B1706129 : Blo 503794 1706129 := bstep (se 2 (by rfl) ⟨639798, by rfl⟩ : syracuseStep 1706129 = 1279597) B1279597
theorem B755873 : Blo 503794 755873 := bstep (se 2 (by rfl) ⟨283452, by rfl⟩ : syracuseStep 755873 = 566905) B566905
theorem B1444013 : Blo 503794 1444013 := bstep (se 3 (by rfl) ⟨270752, by rfl⟩ : syracuseStep 1444013 = 541505) B541505
theorem B755891 : Blo 503794 755891 := bstep (se 1 (by rfl) ⟨566918, by rfl⟩ : syracuseStep 755891 = 1133837) B1133837
theorem B1280195 : Blo 503794 1280195 := bstep (se 1 (by rfl) ⟨960146, by rfl⟩ : syracuseStep 1280195 = 1920293) B1920293
theorem B755921 : Blo 503794 755921 := bstep (se 2 (by rfl) ⟨283470, by rfl⟩ : syracuseStep 755921 = 566941) B566941
theorem B755939 : Blo 503794 755939 := bstep (se 1 (by rfl) ⟨566954, by rfl⟩ : syracuseStep 755939 = 1133909) B1133909
theorem B1444081 : Blo 503794 1444081 := bstep (se 2 (by rfl) ⟨541530, by rfl⟩ : syracuseStep 1444081 = 1083061) B1083061
theorem B755969 : Blo 503794 755969 := bstep (se 2 (by rfl) ⟨283488, by rfl⟩ : syracuseStep 755969 = 566977) B566977
theorem B854273 : Blo 503794 854273 := bstep (se 2 (by rfl) ⟨320352, by rfl⟩ : syracuseStep 854273 = 640705) B640705
theorem B755987 : Blo 503794 755987 := bstep (se 1 (by rfl) ⟨566990, by rfl⟩ : syracuseStep 755987 = 1133981) B1133981
theorem B756017 : Blo 503794 756017 := bstep (se 2 (by rfl) ⟨283506, by rfl⟩ : syracuseStep 756017 = 567013) B567013
theorem B756035 : Blo 503794 756035 := bstep (se 1 (by rfl) ⟨567026, by rfl⟩ : syracuseStep 756035 = 1134053) B1134053
theorem B756065 : Blo 503794 756065 := bstep (se 2 (by rfl) ⟨283524, by rfl⟩ : syracuseStep 756065 = 567049) B567049
theorem B756083 : Blo 503794 756083 := bstep (se 1 (by rfl) ⟨567062, by rfl⟩ : syracuseStep 756083 = 1134125) B1134125
theorem B854401 : Blo 503794 854401 := bstep (se 2 (by rfl) ⟨320400, by rfl⟩ : syracuseStep 854401 = 640801) B640801
theorem B1280387 : Blo 503794 1280387 := bstep (se 1 (by rfl) ⟨960290, by rfl⟩ : syracuseStep 1280387 = 1920581) B1920581
theorem B2591117 : Blo 503794 2591117 := bstep (se 3 (by rfl) ⟨485834, by rfl⟩ : syracuseStep 2591117 = 971669) B971669
theorem B756113 : Blo 503794 756113 := bstep (se 2 (by rfl) ⟨283542, by rfl⟩ : syracuseStep 756113 = 567085) B567085
theorem B756131 : Blo 503794 756131 := bstep (se 1 (by rfl) ⟨567098, by rfl⟩ : syracuseStep 756131 = 1134197) B1134197
theorem B854435 : Blo 503794 854435 := bstep (se 1 (by rfl) ⟨640826, by rfl⟩ : syracuseStep 854435 = 1281653) B1281653
theorem B756161 : Blo 503794 756161 := bstep (se 2 (by rfl) ⟨283560, by rfl⟩ : syracuseStep 756161 = 567121) B567121
theorem B756179 : Blo 503794 756179 := bstep (se 1 (by rfl) ⟨567134, by rfl⟩ : syracuseStep 756179 = 1134269) B1134269
theorem B756209 : Blo 503794 756209 := bstep (se 2 (by rfl) ⟨283578, by rfl⟩ : syracuseStep 756209 = 567157) B567157
theorem B756227 : Blo 503794 756227 := bstep (se 1 (by rfl) ⟨567170, by rfl⟩ : syracuseStep 756227 = 1134341) B1134341
theorem B1444355 : Blo 503794 1444355 := bstep (se 1 (by rfl) ⟨1083266, by rfl⟩ : syracuseStep 1444355 = 2166533) B2166533
theorem B756257 : Blo 503794 756257 := bstep (se 2 (by rfl) ⟨283596, by rfl⟩ : syracuseStep 756257 = 567193) B567193
theorem B854563 : Blo 503794 854563 := bstep (se 1 (by rfl) ⟨640922, by rfl⟩ : syracuseStep 854563 = 1281845) B1281845
theorem B756275 : Blo 503794 756275 := bstep (se 1 (by rfl) ⟨567206, by rfl⟩ : syracuseStep 756275 = 1134413) B1134413
theorem B756305 : Blo 503794 756305 := bstep (se 2 (by rfl) ⟨283614, by rfl⟩ : syracuseStep 756305 = 567229) B567229
theorem B756323 : Blo 503794 756323 := bstep (se 1 (by rfl) ⟨567242, by rfl⟩ : syracuseStep 756323 = 1134485) B1134485
theorem B821873 : Blo 503794 821873 := bstep (se 2 (by rfl) ⟨308202, by rfl⟩ : syracuseStep 821873 = 616405) B616405
theorem B756353 : Blo 503794 756353 := bstep (se 2 (by rfl) ⟨283632, by rfl⟩ : syracuseStep 756353 = 567265) B567265
theorem B756371 : Blo 503794 756371 := bstep (se 1 (by rfl) ⟨567278, by rfl⟩ : syracuseStep 756371 = 1134557) B1134557
theorem B2558627 : Blo 503794 2558627 := bstep (se 1 (by rfl) ⟨1918970, by rfl⟩ : syracuseStep 2558627 = 3837941) B3837941
theorem B1706669 : Blo 503794 1706669 := bstep (se 3 (by rfl) ⟨320000, by rfl⟩ : syracuseStep 1706669 = 640001) B640001
theorem B756401 : Blo 503794 756401 := bstep (se 2 (by rfl) ⟨283650, by rfl⟩ : syracuseStep 756401 = 567301) B567301
theorem B854705 : Blo 503794 854705 := bstep (se 2 (by rfl) ⟨320514, by rfl⟩ : syracuseStep 854705 = 641029) B641029
theorem B756419 : Blo 503794 756419 := bstep (se 1 (by rfl) ⟨567314, by rfl⟩ : syracuseStep 756419 = 1134629) B1134629
theorem B756449 : Blo 503794 756449 := bstep (se 2 (by rfl) ⟨283668, by rfl⟩ : syracuseStep 756449 = 567337) B567337
theorem B1706723 : Blo 503794 1706723 := bstep (se 1 (by rfl) ⟨1280042, by rfl⟩ : syracuseStep 1706723 = 2560085) B2560085
theorem B3640049 : Blo 503794 3640049 := bstep (se 2 (by rfl) ⟨1365018, by rfl⟩ : syracuseStep 3640049 = 2730037) B2730037
theorem B756467 : Blo 503794 756467 := bstep (se 1 (by rfl) ⟨567350, by rfl⟩ : syracuseStep 756467 = 1134701) B1134701
theorem B2427661 : Blo 503794 2427661 := bstep (se 3 (by rfl) ⟨455186, by rfl⟩ : syracuseStep 2427661 = 910373) B910373
theorem B756497 : Blo 503794 756497 := bstep (se 2 (by rfl) ⟨283686, by rfl⟩ : syracuseStep 756497 = 567373) B567373
theorem B756515 : Blo 503794 756515 := bstep (se 1 (by rfl) ⟨567386, by rfl⟩ : syracuseStep 756515 = 1134773) B1134773
theorem B854833 : Blo 503794 854833 := bstep (se 2 (by rfl) ⟨320562, by rfl⟩ : syracuseStep 854833 = 641125) B641125
theorem B756545 : Blo 503794 756545 := bstep (se 2 (by rfl) ⟨283704, by rfl⟩ : syracuseStep 756545 = 567409) B567409
theorem B756563 : Blo 503794 756563 := bstep (se 1 (by rfl) ⟨567422, by rfl⟩ : syracuseStep 756563 = 1134845) B1134845
theorem B854867 : Blo 503794 854867 := bstep (se 1 (by rfl) ⟨641150, by rfl⟩ : syracuseStep 854867 = 1282301) B1282301
theorem B756593 : Blo 503794 756593 := bstep (se 2 (by rfl) ⟨283722, by rfl⟩ : syracuseStep 756593 = 567445) B567445
theorem B756611 : Blo 503794 756611 := bstep (se 1 (by rfl) ⟨567458, by rfl⟩ : syracuseStep 756611 = 1134917) B1134917
theorem B1543043 : Blo 503794 1543043 := bstep (se 1 (by rfl) ⟨1157282, by rfl⟩ : syracuseStep 1543043 = 2314565) B2314565
theorem B756641 : Blo 503794 756641 := bstep (se 2 (by rfl) ⟨283740, by rfl⟩ : syracuseStep 756641 = 567481) B567481
theorem B756659 : Blo 503794 756659 := bstep (se 1 (by rfl) ⟨567494, by rfl⟩ : syracuseStep 756659 = 1134989) B1134989
theorem B756689 : Blo 503794 756689 := bstep (se 2 (by rfl) ⟨283758, by rfl⟩ : syracuseStep 756689 = 567517) B567517
theorem B854995 : Blo 503794 854995 := bstep (se 1 (by rfl) ⟨641246, by rfl⟩ : syracuseStep 854995 = 1282493) B1282493
theorem B756707 : Blo 503794 756707 := bstep (se 1 (by rfl) ⟨567530, by rfl⟩ : syracuseStep 756707 = 1135061) B1135061
theorem B1706993 : Blo 503794 1706993 := bstep (se 2 (by rfl) ⟨640122, by rfl⟩ : syracuseStep 1706993 = 1280245) B1280245
theorem B756737 : Blo 503794 756737 := bstep (se 2 (by rfl) ⟨283776, by rfl⟩ : syracuseStep 756737 = 567553) B567553
theorem B756755 : Blo 503794 756755 := bstep (se 1 (by rfl) ⟨567566, by rfl⟩ : syracuseStep 756755 = 1135133) B1135133
theorem B756785 : Blo 503794 756785 := bstep (se 2 (by rfl) ⟨283794, by rfl⟩ : syracuseStep 756785 = 567589) B567589
theorem B756803 : Blo 503794 756803 := bstep (se 1 (by rfl) ⟨567602, by rfl⟩ : syracuseStep 756803 = 1135205) B1135205
theorem B756833 : Blo 503794 756833 := bstep (se 2 (by rfl) ⟨283812, by rfl⟩ : syracuseStep 756833 = 567625) B567625
theorem B855137 : Blo 503794 855137 := bstep (se 2 (by rfl) ⟨320676, by rfl⟩ : syracuseStep 855137 = 641353) B641353
theorem B756851 : Blo 503794 756851 := bstep (se 1 (by rfl) ⟨567638, by rfl⟩ : syracuseStep 756851 = 1135277) B1135277
theorem B756881 : Blo 503794 756881 := bstep (se 2 (by rfl) ⟨283830, by rfl⟩ : syracuseStep 756881 = 567661) B567661
theorem B756899 : Blo 503794 756899 := bstep (se 1 (by rfl) ⟨567674, by rfl⟩ : syracuseStep 756899 = 1135349) B1135349
theorem B756929 : Blo 503794 756929 := bstep (se 2 (by rfl) ⟨283848, by rfl⟩ : syracuseStep 756929 = 567697) B567697
theorem B756947 : Blo 503794 756947 := bstep (se 1 (by rfl) ⟨567710, by rfl⟩ : syracuseStep 756947 = 1135421) B1135421
theorem B855265 : Blo 503794 855265 := bstep (se 2 (by rfl) ⟨320724, by rfl⟩ : syracuseStep 855265 = 641449) B641449
theorem B756977 : Blo 503794 756977 := bstep (se 2 (by rfl) ⟨283866, by rfl⟩ : syracuseStep 756977 = 567733) B567733
theorem B756995 : Blo 503794 756995 := bstep (se 1 (by rfl) ⟨567746, by rfl⟩ : syracuseStep 756995 = 1135493) B1135493
theorem B855299 : Blo 503794 855299 := bstep (se 1 (by rfl) ⟨641474, by rfl⟩ : syracuseStep 855299 = 1282949) B1282949
theorem B757025 : Blo 503794 757025 := bstep (se 2 (by rfl) ⟨283884, by rfl⟩ : syracuseStep 757025 = 567769) B567769
theorem B1281329 : Blo 503794 1281329 := bstep (se 2 (by rfl) ⟨480498, by rfl⟩ : syracuseStep 1281329 = 960997) B960997
theorem B757043 : Blo 503794 757043 := bstep (se 1 (by rfl) ⟨567782, by rfl⟩ : syracuseStep 757043 = 1135565) B1135565
theorem B1445197 : Blo 503794 1445197 := bstep (se 3 (by rfl) ⟨270974, by rfl⟩ : syracuseStep 1445197 = 541949) B541949
theorem B757073 : Blo 503794 757073 := bstep (se 2 (by rfl) ⟨283902, by rfl⟩ : syracuseStep 757073 = 567805) B567805
theorem B757091 : Blo 503794 757091 := bstep (se 1 (by rfl) ⟨567818, by rfl⟩ : syracuseStep 757091 = 1135637) B1135637
theorem B1281379 : Blo 503794 1281379 := bstep (se 1 (by rfl) ⟨961034, by rfl⟩ : syracuseStep 1281379 = 1922069) B1922069
theorem B757121 : Blo 503794 757121 := bstep (se 2 (by rfl) ⟨283920, by rfl⟩ : syracuseStep 757121 = 567841) B567841
theorem B855427 : Blo 503794 855427 := bstep (se 1 (by rfl) ⟨641570, by rfl⟩ : syracuseStep 855427 = 1283141) B1283141
theorem B757139 : Blo 503794 757139 := bstep (se 1 (by rfl) ⟨567854, by rfl⟩ : syracuseStep 757139 = 1135709) B1135709
theorem B757169 : Blo 503794 757169 := bstep (se 2 (by rfl) ⟨283938, by rfl⟩ : syracuseStep 757169 = 567877) B567877
theorem B757187 : Blo 503794 757187 := bstep (se 1 (by rfl) ⟨567890, by rfl⟩ : syracuseStep 757187 = 1135781) B1135781
theorem B2559437 : Blo 503794 2559437 := bstep (se 3 (by rfl) ⟨479894, by rfl⟩ : syracuseStep 2559437 = 959789) B959789
theorem B757217 : Blo 503794 757217 := bstep (se 2 (by rfl) ⟨283956, by rfl⟩ : syracuseStep 757217 = 567913) B567913
theorem B1445357 : Blo 503794 1445357 := bstep (se 3 (by rfl) ⟨271004, by rfl⟩ : syracuseStep 1445357 = 542009) B542009
theorem B1281521 : Blo 503794 1281521 := bstep (se 2 (by rfl) ⟨480570, by rfl⟩ : syracuseStep 1281521 = 961141) B961141
theorem B757235 : Blo 503794 757235 := bstep (se 1 (by rfl) ⟨567926, by rfl⟩ : syracuseStep 757235 = 1135853) B1135853
theorem B1707533 : Blo 503794 1707533 := bstep (se 3 (by rfl) ⟨320162, by rfl⟩ : syracuseStep 1707533 = 640325) B640325
theorem B757265 : Blo 503794 757265 := bstep (se 2 (by rfl) ⟨283974, by rfl⟩ : syracuseStep 757265 = 567949) B567949
theorem B855569 : Blo 503794 855569 := bstep (se 2 (by rfl) ⟨320838, by rfl⟩ : syracuseStep 855569 = 641677) B641677
theorem B757283 : Blo 503794 757283 := bstep (se 1 (by rfl) ⟨567962, by rfl⟩ : syracuseStep 757283 = 1135925) B1135925
theorem B757313 : Blo 503794 757313 := bstep (se 2 (by rfl) ⟨283992, by rfl⟩ : syracuseStep 757313 = 567985) B567985
theorem B1707587 : Blo 503794 1707587 := bstep (se 1 (by rfl) ⟨1280690, by rfl⟩ : syracuseStep 1707587 = 2561381) B2561381
theorem B757331 : Blo 503794 757331 := bstep (se 1 (by rfl) ⟨567998, by rfl⟩ : syracuseStep 757331 = 1135997) B1135997
theorem B757361 : Blo 503794 757361 := bstep (se 2 (by rfl) ⟨284010, by rfl⟩ : syracuseStep 757361 = 568021) B568021
theorem B3640945 : Blo 503794 3640945 := bstep (se 2 (by rfl) ⟨1365354, by rfl⟩ : syracuseStep 3640945 = 2730709) B2730709
theorem B757379 : Blo 503794 757379 := bstep (se 1 (by rfl) ⟨568034, by rfl⟩ : syracuseStep 757379 = 1136069) B1136069
theorem B855697 : Blo 503794 855697 := bstep (se 2 (by rfl) ⟨320886, by rfl⟩ : syracuseStep 855697 = 641773) B641773
theorem B757409 : Blo 503794 757409 := bstep (se 2 (by rfl) ⟨284028, by rfl⟩ : syracuseStep 757409 = 568057) B568057
theorem B1445539 : Blo 503794 1445539 := bstep (se 1 (by rfl) ⟨1084154, by rfl⟩ : syracuseStep 1445539 = 2168309) B2168309
theorem B757427 : Blo 503794 757427 := bstep (se 1 (by rfl) ⟨568070, by rfl⟩ : syracuseStep 757427 = 1136141) B1136141
theorem B855731 : Blo 503794 855731 := bstep (se 1 (by rfl) ⟨641798, by rfl⟩ : syracuseStep 855731 = 1283597) B1283597
theorem B757457 : Blo 503794 757457 := bstep (se 2 (by rfl) ⟨284046, by rfl⟩ : syracuseStep 757457 = 568093) B568093
theorem B757475 : Blo 503794 757475 := bstep (se 1 (by rfl) ⟨568106, by rfl⟩ : syracuseStep 757475 = 1136213) B1136213
theorem B757505 : Blo 503794 757505 := bstep (se 2 (by rfl) ⟨284064, by rfl⟩ : syracuseStep 757505 = 568129) B568129
theorem B3247877 : Blo 503794 3247877 := bstep (se 4 (by rfl) ⟨304488, by rfl⟩ : syracuseStep 3247877 = 608977) B608977
theorem B757523 : Blo 503794 757523 := bstep (se 1 (by rfl) ⟨568142, by rfl⟩ : syracuseStep 757523 = 1136285) B1136285
theorem B1216291 : Blo 503794 1216291 := bstep (se 1 (by rfl) ⟨912218, by rfl⟩ : syracuseStep 1216291 = 1824437) B1824437
theorem B757553 : Blo 503794 757553 := bstep (se 2 (by rfl) ⟨284082, by rfl⟩ : syracuseStep 757553 = 568165) B568165
theorem B855859 : Blo 503794 855859 := bstep (se 1 (by rfl) ⟨641894, by rfl⟩ : syracuseStep 855859 = 1283789) B1283789
theorem B757571 : Blo 503794 757571 := bstep (se 1 (by rfl) ⟨568178, by rfl⟩ : syracuseStep 757571 = 1136357) B1136357
theorem B1707857 : Blo 503794 1707857 := bstep (se 2 (by rfl) ⟨640446, by rfl⟩ : syracuseStep 1707857 = 1280893) B1280893
theorem B757601 : Blo 503794 757601 := bstep (se 2 (by rfl) ⟨284100, by rfl⟩ : syracuseStep 757601 = 568201) B568201
theorem B757619 : Blo 503794 757619 := bstep (se 1 (by rfl) ⟨568214, by rfl⟩ : syracuseStep 757619 = 1136429) B1136429
theorem B757649 : Blo 503794 757649 := bstep (se 2 (by rfl) ⟨284118, by rfl⟩ : syracuseStep 757649 = 568237) B568237
theorem B757667 : Blo 503794 757667 := bstep (se 1 (by rfl) ⟨568250, by rfl⟩ : syracuseStep 757667 = 1136501) B1136501
theorem B1544113 : Blo 503794 1544113 := bstep (se 2 (by rfl) ⟨579042, by rfl⟩ : syracuseStep 1544113 = 1158085) B1158085
theorem B757697 : Blo 503794 757697 := bstep (se 2 (by rfl) ⟨284136, by rfl⟩ : syracuseStep 757697 = 568273) B568273
theorem B856001 : Blo 503794 856001 := bstep (se 2 (by rfl) ⟨321000, by rfl⟩ : syracuseStep 856001 = 642001) B642001
theorem B757715 : Blo 503794 757715 := bstep (se 1 (by rfl) ⟨568286, by rfl⟩ : syracuseStep 757715 = 1136573) B1136573
theorem B757745 : Blo 503794 757745 := bstep (se 2 (by rfl) ⟨284154, by rfl⟩ : syracuseStep 757745 = 568309) B568309
theorem B757763 : Blo 503794 757763 := bstep (se 1 (by rfl) ⟨568322, by rfl⟩ : syracuseStep 757763 = 1136645) B1136645
theorem B757793 : Blo 503794 757793 := bstep (se 2 (by rfl) ⟨284172, by rfl⟩ : syracuseStep 757793 = 568345) B568345
theorem B757811 : Blo 503794 757811 := bstep (se 1 (by rfl) ⟨568358, by rfl⟩ : syracuseStep 757811 = 1136717) B1136717
theorem B856129 : Blo 503794 856129 := bstep (se 2 (by rfl) ⟨321048, by rfl⟩ : syracuseStep 856129 = 642097) B642097
theorem B757841 : Blo 503794 757841 := bstep (se 2 (by rfl) ⟨284190, by rfl⟩ : syracuseStep 757841 = 568381) B568381
theorem B757859 : Blo 503794 757859 := bstep (se 1 (by rfl) ⟨568394, by rfl⟩ : syracuseStep 757859 = 1136789) B1136789
theorem B856163 : Blo 503794 856163 := bstep (se 1 (by rfl) ⟨642122, by rfl⟩ : syracuseStep 856163 = 1284245) B1284245
theorem B2592881 : Blo 503794 2592881 := bstep (se 2 (by rfl) ⟨972330, by rfl⟩ : syracuseStep 2592881 = 1944661) B1944661
theorem B757889 : Blo 503794 757889 := bstep (se 2 (by rfl) ⟨284208, by rfl⟩ : syracuseStep 757889 = 568417) B568417
theorem B1380493 : Blo 503794 1380493 := bstep (se 3 (by rfl) ⟨258842, by rfl⟩ : syracuseStep 1380493 = 517685) B517685
theorem B757907 : Blo 503794 757907 := bstep (se 1 (by rfl) ⟨568430, by rfl⟩ : syracuseStep 757907 = 1136861) B1136861
theorem B757937 : Blo 503794 757937 := bstep (se 2 (by rfl) ⟨284226, by rfl⟩ : syracuseStep 757937 = 568453) B568453
theorem B757955 : Blo 503794 757955 := bstep (se 1 (by rfl) ⟨568466, by rfl⟩ : syracuseStep 757955 = 1136933) B1136933
theorem B757985 : Blo 503794 757985 := bstep (se 2 (by rfl) ⟨284244, by rfl⟩ : syracuseStep 757985 = 568489) B568489
theorem B659683 : Blo 503794 659683 := bstep (se 1 (by rfl) ⟨494762, by rfl⟩ : syracuseStep 659683 = 989525) B989525
theorem B856291 : Blo 503794 856291 := bstep (se 1 (by rfl) ⟨642218, by rfl⟩ : syracuseStep 856291 = 1284437) B1284437
theorem B4329713 : Blo 503794 4329713 := bstep (se 2 (by rfl) ⟨1623642, by rfl⟩ : syracuseStep 4329713 = 3247285) B3247285
theorem B758003 : Blo 503794 758003 := bstep (se 1 (by rfl) ⟨568502, by rfl⟩ : syracuseStep 758003 = 1137005) B1137005
theorem B758033 : Blo 503794 758033 := bstep (se 2 (by rfl) ⟨284262, by rfl⟩ : syracuseStep 758033 = 568525) B568525
theorem B758051 : Blo 503794 758051 := bstep (se 1 (by rfl) ⟨568538, by rfl⟩ : syracuseStep 758051 = 1137077) B1137077
theorem B758081 : Blo 503794 758081 := bstep (se 2 (by rfl) ⟨284280, by rfl⟩ : syracuseStep 758081 = 568561) B568561
theorem B758099 : Blo 503794 758099 := bstep (se 1 (by rfl) ⟨568574, by rfl⟩ : syracuseStep 758099 = 1137149) B1137149
theorem B1708397 : Blo 503794 1708397 := bstep (se 3 (by rfl) ⟨320324, by rfl⟩ : syracuseStep 1708397 = 640649) B640649
theorem B758129 : Blo 503794 758129 := bstep (se 2 (by rfl) ⟨284298, by rfl⟩ : syracuseStep 758129 = 568597) B568597
theorem B856433 : Blo 503794 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B758147 : Blo 503794 758147 := bstep (se 1 (by rfl) ⟨568610, by rfl⟩ : syracuseStep 758147 = 1137221) B1137221
theorem B2167181 : Blo 503794 2167181 := bstep (se 3 (by rfl) ⟨406346, by rfl⟩ : syracuseStep 2167181 = 812693) B812693
theorem B758177 : Blo 503794 758177 := bstep (se 2 (by rfl) ⟨284316, by rfl⟩ : syracuseStep 758177 = 568633) B568633
theorem B1708451 : Blo 503794 1708451 := bstep (se 1 (by rfl) ⟨1281338, by rfl⟩ : syracuseStep 1708451 = 2562677) B2562677
theorem B758195 : Blo 503794 758195 := bstep (se 1 (by rfl) ⟨568646, by rfl⟩ : syracuseStep 758195 = 1137293) B1137293
theorem B1216963 : Blo 503794 1216963 := bstep (se 1 (by rfl) ⟨912722, by rfl⟩ : syracuseStep 1216963 = 1825445) B1825445
theorem B758225 : Blo 503794 758225 := bstep (se 2 (by rfl) ⟨284334, by rfl⟩ : syracuseStep 758225 = 568669) B568669
theorem B1282513 : Blo 503794 1282513 := bstep (se 2 (by rfl) ⟨480942, by rfl⟩ : syracuseStep 1282513 = 961885) B961885
theorem B758243 : Blo 503794 758243 := bstep (se 1 (by rfl) ⟨568682, by rfl⟩ : syracuseStep 758243 = 1137365) B1137365
theorem B856561 : Blo 503794 856561 := bstep (se 2 (by rfl) ⟨321210, by rfl⟩ : syracuseStep 856561 = 642421) B642421
theorem B758273 : Blo 503794 758273 := bstep (se 2 (by rfl) ⟨284352, by rfl⟩ : syracuseStep 758273 = 568705) B568705
theorem B758291 : Blo 503794 758291 := bstep (se 1 (by rfl) ⟨568718, by rfl⟩ : syracuseStep 758291 = 1137437) B1137437
theorem B856595 : Blo 503794 856595 := bstep (se 1 (by rfl) ⟨642446, by rfl⟩ : syracuseStep 856595 = 1284893) B1284893
theorem B758321 : Blo 503794 758321 := bstep (se 2 (by rfl) ⟨284370, by rfl⟩ : syracuseStep 758321 = 568741) B568741
theorem B758339 : Blo 503794 758339 := bstep (se 1 (by rfl) ⟨568754, by rfl⟩ : syracuseStep 758339 = 1137509) B1137509
theorem B758369 : Blo 503794 758369 := bstep (se 2 (by rfl) ⟨284388, by rfl⟩ : syracuseStep 758369 = 568777) B568777
theorem B758387 : Blo 503794 758387 := bstep (se 1 (by rfl) ⟨568790, by rfl⟩ : syracuseStep 758387 = 1137581) B1137581
theorem B758417 : Blo 503794 758417 := bstep (se 2 (by rfl) ⟨284406, by rfl⟩ : syracuseStep 758417 = 568813) B568813
theorem B856723 : Blo 503794 856723 := bstep (se 1 (by rfl) ⟨642542, by rfl⟩ : syracuseStep 856723 = 1285085) B1285085
theorem B758435 : Blo 503794 758435 := bstep (se 1 (by rfl) ⟨568826, by rfl⟩ : syracuseStep 758435 = 1137653) B1137653
theorem B1708721 : Blo 503794 1708721 := bstep (se 2 (by rfl) ⟨640770, by rfl⟩ : syracuseStep 1708721 = 1281541) B1281541
theorem B758465 : Blo 503794 758465 := bstep (se 2 (by rfl) ⟨284424, by rfl⟩ : syracuseStep 758465 = 568849) B568849
theorem B758483 : Blo 503794 758483 := bstep (se 1 (by rfl) ⟨568862, by rfl⟩ : syracuseStep 758483 = 1137725) B1137725
theorem B1282787 : Blo 503794 1282787 := bstep (se 1 (by rfl) ⟨962090, by rfl⟩ : syracuseStep 1282787 = 1924181) B1924181
theorem B2167523 : Blo 503794 2167523 := bstep (se 1 (by rfl) ⟨1625642, by rfl⟩ : syracuseStep 2167523 = 3251285) B3251285
theorem B758513 : Blo 503794 758513 := bstep (se 2 (by rfl) ⟨284442, by rfl⟩ : syracuseStep 758513 = 568885) B568885
theorem B758531 : Blo 503794 758531 := bstep (se 1 (by rfl) ⟨568898, by rfl⟩ : syracuseStep 758531 = 1137797) B1137797
theorem B758561 : Blo 503794 758561 := bstep (se 2 (by rfl) ⟨284460, by rfl⟩ : syracuseStep 758561 = 568921) B568921
theorem B856865 : Blo 503794 856865 := bstep (se 2 (by rfl) ⟨321324, by rfl⟩ : syracuseStep 856865 = 642649) B642649
theorem B1250083 : Blo 503794 1250083 := bstep (se 1 (by rfl) ⟨937562, by rfl⟩ : syracuseStep 1250083 = 1875125) B1875125
theorem B758579 : Blo 503794 758579 := bstep (se 1 (by rfl) ⟨568934, by rfl⟩ : syracuseStep 758579 = 1137869) B1137869
theorem B2724677 : Blo 503794 2724677 := bstep (se 4 (by rfl) ⟨255438, by rfl⟩ : syracuseStep 2724677 = 510877) B510877
theorem B758609 : Blo 503794 758609 := bstep (se 2 (by rfl) ⟨284478, by rfl⟩ : syracuseStep 758609 = 568957) B568957
theorem B758627 : Blo 503794 758627 := bstep (se 1 (by rfl) ⟨568970, by rfl⟩ : syracuseStep 758627 = 1137941) B1137941
theorem B758657 : Blo 503794 758657 := bstep (se 2 (by rfl) ⟨284496, by rfl⟩ : syracuseStep 758657 = 568993) B568993
theorem B1217425 : Blo 503794 1217425 := bstep (se 2 (by rfl) ⟨456534, by rfl⟩ : syracuseStep 1217425 = 913069) B913069
theorem B758675 : Blo 503794 758675 := bstep (se 1 (by rfl) ⟨569006, by rfl⟩ : syracuseStep 758675 = 1138013) B1138013
theorem B1282979 : Blo 503794 1282979 := bstep (se 1 (by rfl) ⟨962234, by rfl⟩ : syracuseStep 1282979 = 1924469) B1924469
theorem B758705 : Blo 503794 758705 := bstep (se 2 (by rfl) ⟨284514, by rfl⟩ : syracuseStep 758705 = 569029) B569029
theorem B758723 : Blo 503794 758723 := bstep (se 1 (by rfl) ⟨569042, by rfl⟩ : syracuseStep 758723 = 1138085) B1138085
theorem B758753 : Blo 503794 758753 := bstep (se 2 (by rfl) ⟨284532, by rfl⟩ : syracuseStep 758753 = 569065) B569065
theorem B1217521 : Blo 503794 1217521 := bstep (se 2 (by rfl) ⟨456570, by rfl⟩ : syracuseStep 1217521 = 913141) B913141
theorem B758771 : Blo 503794 758771 := bstep (se 1 (by rfl) ⟨569078, by rfl⟩ : syracuseStep 758771 = 1138157) B1138157
theorem B758801 : Blo 503794 758801 := bstep (se 2 (by rfl) ⟨284550, by rfl⟩ : syracuseStep 758801 = 569101) B569101
theorem B758819 : Blo 503794 758819 := bstep (se 1 (by rfl) ⟨569114, by rfl⟩ : syracuseStep 758819 = 1138229) B1138229
theorem B758849 : Blo 503794 758849 := bstep (se 2 (by rfl) ⟨284568, by rfl⟩ : syracuseStep 758849 = 569137) B569137
theorem B1315921 : Blo 503794 1315921 := bstep (se 2 (by rfl) ⟨493470, by rfl⟩ : syracuseStep 1315921 = 986941) B986941
theorem B758867 : Blo 503794 758867 := bstep (se 1 (by rfl) ⟨569150, by rfl⟩ : syracuseStep 758867 = 1138301) B1138301
theorem B758897 : Blo 503794 758897 := bstep (se 2 (by rfl) ⟨284586, by rfl⟩ : syracuseStep 758897 = 569173) B569173
theorem B758915 : Blo 503794 758915 := bstep (se 1 (by rfl) ⟨569186, by rfl⟩ : syracuseStep 758915 = 1138373) B1138373
theorem B758945 : Blo 503794 758945 := bstep (se 2 (by rfl) ⟨284604, by rfl⟩ : syracuseStep 758945 = 569209) B569209
theorem B2167985 : Blo 503794 2167985 := bstep (se 2 (by rfl) ⟨812994, by rfl⟩ : syracuseStep 2167985 = 1625989) B1625989
theorem B758963 : Blo 503794 758963 := bstep (se 1 (by rfl) ⟨569222, by rfl⟩ : syracuseStep 758963 = 1138445) B1138445
theorem B1709261 : Blo 503794 1709261 := bstep (se 3 (by rfl) ⟨320486, by rfl⟩ : syracuseStep 1709261 = 640973) B640973
theorem B758993 : Blo 503794 758993 := bstep (se 2 (by rfl) ⟨284622, by rfl⟩ : syracuseStep 758993 = 569245) B569245
theorem B759011 : Blo 503794 759011 := bstep (se 1 (by rfl) ⟨569258, by rfl⟩ : syracuseStep 759011 = 1138517) B1138517
theorem B759041 : Blo 503794 759041 := bstep (se 2 (by rfl) ⟨284640, by rfl⟩ : syracuseStep 759041 = 569281) B569281
theorem B1709315 : Blo 503794 1709315 := bstep (se 1 (by rfl) ⟨1281986, by rfl⟩ : syracuseStep 1709315 = 2563973) B2563973
theorem B922897 : Blo 503794 922897 := bstep (se 2 (by rfl) ⟨346086, by rfl⟩ : syracuseStep 922897 = 692173) B692173
theorem B759059 : Blo 503794 759059 := bstep (se 1 (by rfl) ⟨569294, by rfl⟩ : syracuseStep 759059 = 1138589) B1138589
theorem B759089 : Blo 503794 759089 := bstep (se 2 (by rfl) ⟨284658, by rfl⟩ : syracuseStep 759089 = 569317) B569317
theorem B759107 : Blo 503794 759107 := bstep (se 1 (by rfl) ⟨569330, by rfl⟩ : syracuseStep 759107 = 1138661) B1138661
theorem B759137 : Blo 503794 759137 := bstep (se 2 (by rfl) ⟨284676, by rfl⟩ : syracuseStep 759137 = 569353) B569353
theorem B759155 : Blo 503794 759155 := bstep (se 1 (by rfl) ⟨569366, by rfl⟩ : syracuseStep 759155 = 1138733) B1138733
theorem B759185 : Blo 503794 759185 := bstep (se 2 (by rfl) ⟨284694, by rfl⟩ : syracuseStep 759185 = 569389) B569389
theorem B759203 : Blo 503794 759203 := bstep (se 1 (by rfl) ⟨569402, by rfl⟩ : syracuseStep 759203 = 1138805) B1138805
theorem B759233 : Blo 503794 759233 := bstep (se 2 (by rfl) ⟨284712, by rfl⟩ : syracuseStep 759233 = 569425) B569425
theorem B759251 : Blo 503794 759251 := bstep (se 1 (by rfl) ⟨569438, by rfl⟩ : syracuseStep 759251 = 1138877) B1138877
theorem B759281 : Blo 503794 759281 := bstep (se 2 (by rfl) ⟨284730, by rfl⟩ : syracuseStep 759281 = 569461) B569461
theorem B759299 : Blo 503794 759299 := bstep (se 1 (by rfl) ⟨569474, by rfl⟩ : syracuseStep 759299 = 1138949) B1138949
theorem B1709585 : Blo 503794 1709585 := bstep (se 2 (by rfl) ⟨641094, by rfl⟩ : syracuseStep 1709585 = 1282189) B1282189
theorem B759329 : Blo 503794 759329 := bstep (se 2 (by rfl) ⟨284748, by rfl⟩ : syracuseStep 759329 = 569497) B569497
theorem B759347 : Blo 503794 759347 := bstep (se 1 (by rfl) ⟨569510, by rfl⟩ : syracuseStep 759347 = 1139021) B1139021
theorem B759377 : Blo 503794 759377 := bstep (se 2 (by rfl) ⟨284766, by rfl⟩ : syracuseStep 759377 = 569533) B569533
theorem B759395 : Blo 503794 759395 := bstep (se 1 (by rfl) ⟨569546, by rfl⟩ : syracuseStep 759395 = 1139093) B1139093
theorem B5740145 : Blo 503794 5740145 := bstep (se 2 (by rfl) ⟨2152554, by rfl⟩ : syracuseStep 5740145 = 4305109) B4305109
theorem B759425 : Blo 503794 759425 := bstep (se 2 (by rfl) ⟨284784, by rfl⟩ : syracuseStep 759425 = 569569) B569569
theorem B759443 : Blo 503794 759443 := bstep (se 1 (by rfl) ⟨569582, by rfl⟩ : syracuseStep 759443 = 1139165) B1139165
theorem B759473 : Blo 503794 759473 := bstep (se 2 (by rfl) ⟨284802, by rfl⟩ : syracuseStep 759473 = 569605) B569605
theorem B759491 : Blo 503794 759491 := bstep (se 1 (by rfl) ⟨569618, by rfl⟩ : syracuseStep 759491 = 1139237) B1139237
theorem B759521 : Blo 503794 759521 := bstep (se 2 (by rfl) ⟨284820, by rfl⟩ : syracuseStep 759521 = 569641) B569641
theorem B759539 : Blo 503794 759539 := bstep (se 1 (by rfl) ⟨569654, by rfl⟩ : syracuseStep 759539 = 1139309) B1139309
theorem B759569 : Blo 503794 759569 := bstep (se 2 (by rfl) ⟨284838, by rfl⟩ : syracuseStep 759569 = 569677) B569677
theorem B759587 : Blo 503794 759587 := bstep (se 1 (by rfl) ⟨569690, by rfl⟩ : syracuseStep 759587 = 1139381) B1139381
theorem B759617 : Blo 503794 759617 := bstep (se 2 (by rfl) ⟨284856, by rfl⟩ : syracuseStep 759617 = 569713) B569713
theorem B1283921 : Blo 503794 1283921 := bstep (se 2 (by rfl) ⟨481470, by rfl⟩ : syracuseStep 1283921 = 962941) B962941
theorem B759635 : Blo 503794 759635 := bstep (se 1 (by rfl) ⟨569726, by rfl⟩ : syracuseStep 759635 = 1139453) B1139453
theorem B759665 : Blo 503794 759665 := bstep (se 2 (by rfl) ⟨284874, by rfl⟩ : syracuseStep 759665 = 569749) B569749
theorem B759683 : Blo 503794 759683 := bstep (se 1 (by rfl) ⟨569762, by rfl⟩ : syracuseStep 759683 = 1139525) B1139525
theorem B1283971 : Blo 503794 1283971 := bstep (se 1 (by rfl) ⟨962978, by rfl⟩ : syracuseStep 1283971 = 1925957) B1925957
theorem B3839885 : Blo 503794 3839885 := bstep (se 3 (by rfl) ⟨719978, by rfl⟩ : syracuseStep 3839885 = 1439957) B1439957
theorem B759713 : Blo 503794 759713 := bstep (se 2 (by rfl) ⟨284892, by rfl⟩ : syracuseStep 759713 = 569785) B569785
theorem B759731 : Blo 503794 759731 := bstep (se 1 (by rfl) ⟨569798, by rfl⟩ : syracuseStep 759731 = 1139597) B1139597
theorem B24549317 : Blo 503794 24549317 := bstep (se 4 (by rfl) ⟨2301498, by rfl⟩ : syracuseStep 24549317 = 4602997) B4602997
theorem B759761 : Blo 503794 759761 := bstep (se 2 (by rfl) ⟨284910, by rfl⟩ : syracuseStep 759761 = 569821) B569821
theorem B759779 : Blo 503794 759779 := bstep (se 1 (by rfl) ⟨569834, by rfl⟩ : syracuseStep 759779 = 1139669) B1139669
theorem B759809 : Blo 503794 759809 := bstep (se 2 (by rfl) ⟨284928, by rfl⟩ : syracuseStep 759809 = 569857) B569857
theorem B1284113 : Blo 503794 1284113 := bstep (se 2 (by rfl) ⟨481542, by rfl⟩ : syracuseStep 1284113 = 963085) B963085
theorem B759827 : Blo 503794 759827 := bstep (se 1 (by rfl) ⟨569870, by rfl⟩ : syracuseStep 759827 = 1139741) B1139741
theorem B1710125 : Blo 503794 1710125 := bstep (se 3 (by rfl) ⟨320648, by rfl⟩ : syracuseStep 1710125 = 641297) B641297
theorem B759857 : Blo 503794 759857 := bstep (se 2 (by rfl) ⟨284946, by rfl⟩ : syracuseStep 759857 = 569893) B569893
theorem B759875 : Blo 503794 759875 := bstep (se 1 (by rfl) ⟨569906, by rfl⟩ : syracuseStep 759875 = 1139813) B1139813
theorem B759905 : Blo 503794 759905 := bstep (se 2 (by rfl) ⟨284964, by rfl⟩ : syracuseStep 759905 = 569929) B569929
theorem B1710179 : Blo 503794 1710179 := bstep (se 1 (by rfl) ⟨1282634, by rfl⟩ : syracuseStep 1710179 = 2565269) B2565269
theorem B759923 : Blo 503794 759923 := bstep (se 1 (by rfl) ⟨569942, by rfl⟩ : syracuseStep 759923 = 1139885) B1139885
theorem B759953 : Blo 503794 759953 := bstep (se 2 (by rfl) ⟨284982, by rfl⟩ : syracuseStep 759953 = 569965) B569965
theorem B759971 : Blo 503794 759971 := bstep (se 1 (by rfl) ⟨569978, by rfl⟩ : syracuseStep 759971 = 1139957) B1139957
theorem B760001 : Blo 503794 760001 := bstep (se 2 (by rfl) ⟨285000, by rfl⟩ : syracuseStep 760001 = 570001) B570001
theorem B760019 : Blo 503794 760019 := bstep (se 1 (by rfl) ⟨570014, by rfl⟩ : syracuseStep 760019 = 1140029) B1140029
theorem B760049 : Blo 503794 760049 := bstep (se 2 (by rfl) ⟨285018, by rfl⟩ : syracuseStep 760049 = 570037) B570037
theorem B760067 : Blo 503794 760067 := bstep (se 1 (by rfl) ⟨570050, by rfl⟩ : syracuseStep 760067 = 1140101) B1140101
theorem B760097 : Blo 503794 760097 := bstep (se 2 (by rfl) ⟨285036, by rfl⟩ : syracuseStep 760097 = 570073) B570073
theorem B2562353 : Blo 503794 2562353 := bstep (se 2 (by rfl) ⟨960882, by rfl⟩ : syracuseStep 2562353 = 1921765) B1921765
theorem B760115 : Blo 503794 760115 := bstep (se 1 (by rfl) ⟨570086, by rfl⟩ : syracuseStep 760115 = 1140173) B1140173
theorem B6461765 : Blo 503794 6461765 := bstep (se 4 (by rfl) ⟨605790, by rfl⟩ : syracuseStep 6461765 = 1211581) B1211581
theorem B760145 : Blo 503794 760145 := bstep (se 2 (by rfl) ⟨285054, by rfl⟩ : syracuseStep 760145 = 570109) B570109
theorem B1153379 : Blo 503794 1153379 := bstep (se 1 (by rfl) ⟨865034, by rfl⟩ : syracuseStep 1153379 = 1730069) B1730069
theorem B760163 : Blo 503794 760163 := bstep (se 1 (by rfl) ⟨570122, by rfl⟩ : syracuseStep 760163 = 1140245) B1140245
theorem B1710449 : Blo 503794 1710449 := bstep (se 2 (by rfl) ⟨641418, by rfl⟩ : syracuseStep 1710449 = 1282837) B1282837
theorem B2595185 : Blo 503794 2595185 := bstep (se 2 (by rfl) ⟨973194, by rfl⟩ : syracuseStep 2595185 = 1946389) B1946389
theorem B760193 : Blo 503794 760193 := bstep (se 2 (by rfl) ⟨285072, by rfl⟩ : syracuseStep 760193 = 570145) B570145
theorem B760211 : Blo 503794 760211 := bstep (se 1 (by rfl) ⟨570158, by rfl⟩ : syracuseStep 760211 = 1140317) B1140317
theorem B760241 : Blo 503794 760241 := bstep (se 2 (by rfl) ⟨285090, by rfl⟩ : syracuseStep 760241 = 570181) B570181
theorem B760259 : Blo 503794 760259 := bstep (se 1 (by rfl) ⟨570194, by rfl⟩ : syracuseStep 760259 = 1140389) B1140389
theorem B760289 : Blo 503794 760289 := bstep (se 2 (by rfl) ⟨285108, by rfl⟩ : syracuseStep 760289 = 570217) B570217
theorem B760307 : Blo 503794 760307 := bstep (se 1 (by rfl) ⟨570230, by rfl⟩ : syracuseStep 760307 = 1140461) B1140461
theorem B760337 : Blo 503794 760337 := bstep (se 2 (by rfl) ⟨285126, by rfl⟩ : syracuseStep 760337 = 570253) B570253
theorem B760355 : Blo 503794 760355 := bstep (se 1 (by rfl) ⟨570266, by rfl⟩ : syracuseStep 760355 = 1140533) B1140533
theorem B760385 : Blo 503794 760385 := bstep (se 2 (by rfl) ⟨285144, by rfl⟩ : syracuseStep 760385 = 570289) B570289
theorem B760403 : Blo 503794 760403 := bstep (se 1 (by rfl) ⟨570302, by rfl⟩ : syracuseStep 760403 = 1140605) B1140605
theorem B760433 : Blo 503794 760433 := bstep (se 2 (by rfl) ⟨285162, by rfl⟩ : syracuseStep 760433 = 570325) B570325
theorem B760451 : Blo 503794 760451 := bstep (se 1 (by rfl) ⟨570338, by rfl⟩ : syracuseStep 760451 = 1140677) B1140677
theorem B760481 : Blo 503794 760481 := bstep (se 2 (by rfl) ⟨285180, by rfl⟩ : syracuseStep 760481 = 570361) B570361
theorem B760499 : Blo 503794 760499 := bstep (se 1 (by rfl) ⟨570374, by rfl⟩ : syracuseStep 760499 = 1140749) B1140749
theorem B760529 : Blo 503794 760529 := bstep (se 2 (by rfl) ⟨285198, by rfl⟩ : syracuseStep 760529 = 570397) B570397
theorem B760547 : Blo 503794 760547 := bstep (se 1 (by rfl) ⟨570410, by rfl⟩ : syracuseStep 760547 = 1140821) B1140821
theorem B760577 : Blo 503794 760577 := bstep (se 2 (by rfl) ⟨285216, by rfl⟩ : syracuseStep 760577 = 570433) B570433
theorem B760595 : Blo 503794 760595 := bstep (se 1 (by rfl) ⟨570446, by rfl⟩ : syracuseStep 760595 = 1140893) B1140893
theorem B760625 : Blo 503794 760625 := bstep (se 2 (by rfl) ⟨285234, by rfl⟩ : syracuseStep 760625 = 570469) B570469
theorem B760643 : Blo 503794 760643 := bstep (se 1 (by rfl) ⟨570482, by rfl⟩ : syracuseStep 760643 = 1140965) B1140965
theorem B760673 : Blo 503794 760673 := bstep (se 2 (by rfl) ⟨285252, by rfl⟩ : syracuseStep 760673 = 570505) B570505
theorem B760691 : Blo 503794 760691 := bstep (se 1 (by rfl) ⟨570518, by rfl⟩ : syracuseStep 760691 = 1141037) B1141037
theorem B1710989 : Blo 503794 1710989 := bstep (se 3 (by rfl) ⟨320810, by rfl⟩ : syracuseStep 1710989 = 641621) B641621
theorem B957329 : Blo 503794 957329 := bstep (se 2 (by rfl) ⟨358998, by rfl⟩ : syracuseStep 957329 = 717997) B717997
theorem B760721 : Blo 503794 760721 := bstep (se 2 (by rfl) ⟨285270, by rfl⟩ : syracuseStep 760721 = 570541) B570541
theorem B760739 : Blo 503794 760739 := bstep (se 1 (by rfl) ⟨570554, by rfl⟩ : syracuseStep 760739 = 1141109) B1141109
theorem B760769 : Blo 503794 760769 := bstep (se 2 (by rfl) ⟨285288, by rfl⟩ : syracuseStep 760769 = 570577) B570577
theorem B1711043 : Blo 503794 1711043 := bstep (se 1 (by rfl) ⟨1283282, by rfl⟩ : syracuseStep 1711043 = 2566565) B2566565
theorem B760787 : Blo 503794 760787 := bstep (se 1 (by rfl) ⟨570590, by rfl⟩ : syracuseStep 760787 = 1141181) B1141181
theorem B760817 : Blo 503794 760817 := bstep (se 2 (by rfl) ⟨285306, by rfl⟩ : syracuseStep 760817 = 570613) B570613
theorem B1285105 : Blo 503794 1285105 := bstep (se 2 (by rfl) ⟨481914, by rfl⟩ : syracuseStep 1285105 = 963829) B963829
theorem B760835 : Blo 503794 760835 := bstep (se 1 (by rfl) ⟨570626, by rfl⟩ : syracuseStep 760835 = 1141253) B1141253
theorem B760865 : Blo 503794 760865 := bstep (se 2 (by rfl) ⟨285324, by rfl⟩ : syracuseStep 760865 = 570649) B570649
theorem B760883 : Blo 503794 760883 := bstep (se 1 (by rfl) ⟨570662, by rfl⟩ : syracuseStep 760883 = 1141325) B1141325
theorem B760913 : Blo 503794 760913 := bstep (se 2 (by rfl) ⟨285342, by rfl⟩ : syracuseStep 760913 = 570685) B570685
theorem B760931 : Blo 503794 760931 := bstep (se 1 (by rfl) ⟨570698, by rfl⟩ : syracuseStep 760931 = 1141397) B1141397
theorem B760961 : Blo 503794 760961 := bstep (se 2 (by rfl) ⟨285360, by rfl⟩ : syracuseStep 760961 = 570721) B570721
theorem B760979 : Blo 503794 760979 := bstep (se 1 (by rfl) ⟨570734, by rfl⟩ : syracuseStep 760979 = 1141469) B1141469
theorem B761009 : Blo 503794 761009 := bstep (se 2 (by rfl) ⟨285378, by rfl⟩ : syracuseStep 761009 = 570757) B570757
theorem B761027 : Blo 503794 761027 := bstep (se 1 (by rfl) ⟨570770, by rfl⟩ : syracuseStep 761027 = 1141541) B1141541
theorem B1711313 : Blo 503794 1711313 := bstep (se 2 (by rfl) ⟨641742, by rfl⟩ : syracuseStep 1711313 = 1283485) B1283485
theorem B761057 : Blo 503794 761057 := bstep (se 2 (by rfl) ⟨285396, by rfl⟩ : syracuseStep 761057 = 570793) B570793
theorem B5250275 : Blo 503794 5250275 := bstep (se 1 (by rfl) ⟨3937706, by rfl⟩ : syracuseStep 5250275 = 7875413) B7875413
theorem B761075 : Blo 503794 761075 := bstep (se 1 (by rfl) ⟨570806, by rfl⟩ : syracuseStep 761075 = 1141613) B1141613
theorem B761105 : Blo 503794 761105 := bstep (se 2 (by rfl) ⟨285414, by rfl⟩ : syracuseStep 761105 = 570829) B570829
theorem B761123 : Blo 503794 761123 := bstep (se 1 (by rfl) ⟨570842, by rfl⟩ : syracuseStep 761123 = 1141685) B1141685
theorem B761153 : Blo 503794 761153 := bstep (se 2 (by rfl) ⟨285432, by rfl⟩ : syracuseStep 761153 = 570865) B570865
theorem B761171 : Blo 503794 761171 := bstep (se 1 (by rfl) ⟨570878, by rfl⟩ : syracuseStep 761171 = 1141757) B1141757
theorem B761201 : Blo 503794 761201 := bstep (se 2 (by rfl) ⟨285450, by rfl⟩ : syracuseStep 761201 = 570901) B570901
theorem B761219 : Blo 503794 761219 := bstep (se 1 (by rfl) ⟨570914, by rfl⟩ : syracuseStep 761219 = 1141829) B1141829
theorem B761249 : Blo 503794 761249 := bstep (se 2 (by rfl) ⟨285468, by rfl⟩ : syracuseStep 761249 = 570937) B570937
theorem B761267 : Blo 503794 761267 := bstep (se 1 (by rfl) ⟨570950, by rfl⟩ : syracuseStep 761267 = 1141901) B1141901
theorem B761297 : Blo 503794 761297 := bstep (se 2 (by rfl) ⟨285486, by rfl⟩ : syracuseStep 761297 = 570973) B570973
theorem B761315 : Blo 503794 761315 := bstep (se 1 (by rfl) ⟨570986, by rfl⟩ : syracuseStep 761315 = 1141973) B1141973
theorem B761345 : Blo 503794 761345 := bstep (se 2 (by rfl) ⟨285504, by rfl⟩ : syracuseStep 761345 = 571009) B571009
theorem B761363 : Blo 503794 761363 := bstep (se 1 (by rfl) ⟨571022, by rfl⟩ : syracuseStep 761363 = 1142045) B1142045
theorem B761393 : Blo 503794 761393 := bstep (se 2 (by rfl) ⟨285522, by rfl⟩ : syracuseStep 761393 = 571045) B571045
theorem B761411 : Blo 503794 761411 := bstep (se 1 (by rfl) ⟨571058, by rfl⟩ : syracuseStep 761411 = 1142117) B1142117
theorem B761441 : Blo 503794 761441 := bstep (se 2 (by rfl) ⟨285540, by rfl⟩ : syracuseStep 761441 = 571081) B571081
theorem B761459 : Blo 503794 761459 := bstep (se 1 (by rfl) ⟨571094, by rfl⟩ : syracuseStep 761459 = 1142189) B1142189
theorem B761489 : Blo 503794 761489 := bstep (se 2 (by rfl) ⟨285558, by rfl⟩ : syracuseStep 761489 = 571117) B571117
theorem B761507 : Blo 503794 761507 := bstep (se 1 (by rfl) ⟨571130, by rfl⟩ : syracuseStep 761507 = 1142261) B1142261
theorem B761537 : Blo 503794 761537 := bstep (se 2 (by rfl) ⟨285576, by rfl⟩ : syracuseStep 761537 = 571153) B571153
theorem B761555 : Blo 503794 761555 := bstep (se 1 (by rfl) ⟨571166, by rfl⟩ : syracuseStep 761555 = 1142333) B1142333
theorem B2563811 : Blo 503794 2563811 := bstep (se 1 (by rfl) ⟨1922858, by rfl⟩ : syracuseStep 2563811 = 3845717) B3845717
theorem B1711853 : Blo 503794 1711853 := bstep (se 3 (by rfl) ⟨320972, by rfl⟩ : syracuseStep 1711853 = 641945) B641945
theorem B761585 : Blo 503794 761585 := bstep (se 2 (by rfl) ⟨285594, by rfl⟩ : syracuseStep 761585 = 571189) B571189
theorem B761603 : Blo 503794 761603 := bstep (se 1 (by rfl) ⟨571202, by rfl⟩ : syracuseStep 761603 = 1142405) B1142405
theorem B958225 : Blo 503794 958225 := bstep (se 2 (by rfl) ⟨359334, by rfl⟩ : syracuseStep 958225 = 718669) B718669
theorem B1711907 : Blo 503794 1711907 := bstep (se 1 (by rfl) ⟨1283930, by rfl⟩ : syracuseStep 1711907 = 2567861) B2567861
theorem B761633 : Blo 503794 761633 := bstep (se 2 (by rfl) ⟨285612, by rfl⟩ : syracuseStep 761633 = 571225) B571225
theorem B761651 : Blo 503794 761651 := bstep (se 1 (by rfl) ⟨571238, by rfl⟩ : syracuseStep 761651 = 1142477) B1142477
theorem B761681 : Blo 503794 761681 := bstep (se 2 (by rfl) ⟨285630, by rfl⟩ : syracuseStep 761681 = 571261) B571261
theorem B958385 : Blo 503794 958385 := bstep (se 2 (by rfl) ⟨359394, by rfl⟩ : syracuseStep 958385 = 718789) B718789
theorem B1712177 : Blo 503794 1712177 := bstep (se 2 (by rfl) ⟨642066, by rfl⟩ : syracuseStep 1712177 = 1284133) B1284133
theorem B2597069 : Blo 503794 2597069 := bstep (se 3 (by rfl) ⟨486950, by rfl⟩ : syracuseStep 2597069 = 973901) B973901
theorem B1614097 : Blo 503794 1614097 := bstep (se 2 (by rfl) ⟨605286, by rfl⟩ : syracuseStep 1614097 = 1210573) B1210573
theorem B958787 : Blo 503794 958787 := bstep (se 1 (by rfl) ⟨719090, by rfl⟩ : syracuseStep 958787 = 1438181) B1438181
theorem B1614161 : Blo 503794 1614161 := bstep (se 2 (by rfl) ⟨605310, by rfl⟩ : syracuseStep 1614161 = 1210621) B1210621
theorem B2564621 : Blo 503794 2564621 := bstep (se 3 (by rfl) ⟨480866, by rfl⟩ : syracuseStep 2564621 = 961733) B961733
theorem B1712717 : Blo 503794 1712717 := bstep (se 3 (by rfl) ⟨321134, by rfl⟩ : syracuseStep 1712717 = 642269) B642269
theorem B1712771 : Blo 503794 1712771 := bstep (se 1 (by rfl) ⟨1284578, by rfl⟩ : syracuseStep 1712771 = 2569157) B2569157
theorem B3842801 : Blo 503794 3842801 := bstep (se 2 (by rfl) ⟨1441050, by rfl⟩ : syracuseStep 3842801 = 2882101) B2882101
theorem B1844045 : Blo 503794 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B729953 : Blo 503794 729953 := bstep (se 2 (by rfl) ⟨273732, by rfl⟩ : syracuseStep 729953 = 547465) B547465
theorem B1713041 : Blo 503794 1713041 := bstep (se 2 (by rfl) ⟨642390, by rfl⟩ : syracuseStep 1713041 = 1284781) B1284781
theorem B959683 : Blo 503794 959683 := bstep (se 1 (by rfl) ⟨719762, by rfl⟩ : syracuseStep 959683 = 1439525) B1439525
theorem B959843 : Blo 503794 959843 := bstep (se 1 (by rfl) ⟨719882, by rfl⟩ : syracuseStep 959843 = 1439765) B1439765
theorem B1713581 : Blo 503794 1713581 := bstep (se 3 (by rfl) ⟨321296, by rfl⟩ : syracuseStep 1713581 = 642593) B642593
theorem B1648081 : Blo 503794 1648081 := bstep (se 2 (by rfl) ⟨618030, by rfl⟩ : syracuseStep 1648081 = 1236061) B1236061
theorem B1713635 : Blo 503794 1713635 := bstep (se 1 (by rfl) ⟨1285226, by rfl⟩ : syracuseStep 1713635 = 2570453) B2570453
theorem B566851 : Blo 503794 566851 := bstep (se 1 (by rfl) ⟨425138, by rfl⟩ : syracuseStep 566851 = 850277) B850277
theorem B6006413 : Blo 503794 6006413 := bstep (se 3 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 6006413 = 2252405) B2252405
theorem B1156771 : Blo 503794 1156771 := bstep (se 1 (by rfl) ⟨867578, by rfl⟩ : syracuseStep 1156771 = 1735157) B1735157
theorem B566995 : Blo 503794 566995 := bstep (se 1 (by rfl) ⟨425246, by rfl⟩ : syracuseStep 566995 = 850493) B850493
theorem B567139 : Blo 503794 567139 := bstep (se 1 (by rfl) ⟨425354, by rfl⟩ : syracuseStep 567139 = 850709) B850709
theorem B567283 : Blo 503794 567283 := bstep (se 1 (by rfl) ⟨425462, by rfl⟩ : syracuseStep 567283 = 850925) B850925
theorem B5482565 : Blo 503794 5482565 := bstep (se 4 (by rfl) ⟨513990, by rfl⟩ : syracuseStep 5482565 = 1027981) B1027981
theorem B862339 : Blo 503794 862339 := bstep (se 1 (by rfl) ⟨646754, by rfl⟩ : syracuseStep 862339 = 1293509) B1293509
theorem B567427 : Blo 503794 567427 := bstep (se 1 (by rfl) ⟨425570, by rfl⟩ : syracuseStep 567427 = 851141) B851141
theorem B7317701 : Blo 503794 7317701 := bstep (se 4 (by rfl) ⟨686034, by rfl⟩ : syracuseStep 7317701 = 1372069) B1372069
theorem B7416035 : Blo 503794 7416035 := bstep (se 1 (by rfl) ⟨5562026, by rfl⟩ : syracuseStep 7416035 = 11124053) B11124053
theorem B567571 : Blo 503794 567571 := bstep (se 1 (by rfl) ⟨425678, by rfl⟩ : syracuseStep 567571 = 851357) B851357
theorem B1026353 : Blo 503794 1026353 := bstep (se 2 (by rfl) ⟨384882, by rfl⟩ : syracuseStep 1026353 = 769765) B769765
theorem B960913 : Blo 503794 960913 := bstep (se 2 (by rfl) ⟨360342, by rfl⟩ : syracuseStep 960913 = 720685) B720685
theorem B862625 : Blo 503794 862625 := bstep (se 2 (by rfl) ⟨323484, by rfl⟩ : syracuseStep 862625 = 646969) B646969
theorem B567715 : Blo 503794 567715 := bstep (se 1 (by rfl) ⟨425786, by rfl⟩ : syracuseStep 567715 = 851573) B851573
theorem B567859 : Blo 503794 567859 := bstep (se 1 (by rfl) ⟨425894, by rfl⟩ : syracuseStep 567859 = 851789) B851789
theorem B6466229 : Blo 503794 6466229 := bstep (se 5 (by rfl) ⟨303104, by rfl⟩ : syracuseStep 6466229 = 606209) B606209
theorem B568003 : Blo 503794 568003 := bstep (se 1 (by rfl) ⟨426002, by rfl⟩ : syracuseStep 568003 = 852005) B852005
theorem B568147 : Blo 503794 568147 := bstep (se 1 (by rfl) ⟨426110, by rfl⟩ : syracuseStep 568147 = 852221) B852221
theorem B2304931 : Blo 503794 2304931 := bstep (se 1 (by rfl) ⟨1728698, by rfl⟩ : syracuseStep 2304931 = 3457397) B3457397
theorem B568291 : Blo 503794 568291 := bstep (se 1 (by rfl) ⟨426218, by rfl⟩ : syracuseStep 568291 = 852437) B852437
theorem B568435 : Blo 503794 568435 := bstep (se 1 (by rfl) ⟨426326, by rfl⟩ : syracuseStep 568435 = 852653) B852653
theorem B568579 : Blo 503794 568579 := bstep (se 1 (by rfl) ⟨426434, by rfl⟩ : syracuseStep 568579 = 852869) B852869
theorem B2567537 : Blo 503794 2567537 := bstep (se 2 (by rfl) ⟨962826, by rfl⟩ : syracuseStep 2567537 = 1925653) B1925653
theorem B568723 : Blo 503794 568723 := bstep (se 1 (by rfl) ⟨426542, by rfl⟩ : syracuseStep 568723 = 853085) B853085
theorem B961969 : Blo 503794 961969 := bstep (se 2 (by rfl) ⟨360738, by rfl⟩ : syracuseStep 961969 = 721477) B721477
theorem B3452357 : Blo 503794 3452357 := bstep (se 4 (by rfl) ⟨323658, by rfl⟩ : syracuseStep 3452357 = 647317) B647317
theorem B568867 : Blo 503794 568867 := bstep (se 1 (by rfl) ⟨426650, by rfl⟩ : syracuseStep 568867 = 853301) B853301
theorem B8629901 : Blo 503794 8629901 := bstep (se 3 (by rfl) ⟨1618106, by rfl⟩ : syracuseStep 8629901 = 3236213) B3236213
theorem B569011 : Blo 503794 569011 := bstep (se 1 (by rfl) ⟨426758, by rfl⟩ : syracuseStep 569011 = 853517) B853517
theorem B569155 : Blo 503794 569155 := bstep (se 1 (by rfl) ⟨426866, by rfl⟩ : syracuseStep 569155 = 853733) B853733
theorem B962371 : Blo 503794 962371 := bstep (se 1 (by rfl) ⟨721778, by rfl⟩ : syracuseStep 962371 = 1443557) B1443557
theorem B962417 : Blo 503794 962417 := bstep (se 2 (by rfl) ⟨360906, by rfl⟩ : syracuseStep 962417 = 721813) B721813
theorem B1388465 : Blo 503794 1388465 := bstep (se 2 (by rfl) ⟨520674, by rfl⟩ : syracuseStep 1388465 = 1041349) B1041349
theorem B569299 : Blo 503794 569299 := bstep (se 1 (by rfl) ⟨426974, by rfl⟩ : syracuseStep 569299 = 853949) B853949
theorem B503795 : Blo 503794 503795 := bstep (se 1 (by rfl) ⟨377846, by rfl⟩ : syracuseStep 503795 = 755693) B755693
theorem B503811 : Blo 503794 503811 := bstep (se 1 (by rfl) ⟨377858, by rfl⟩ : syracuseStep 503811 = 755717) B755717
theorem B503827 : Blo 503794 503827 := bstep (se 1 (by rfl) ⟨377870, by rfl⟩ : syracuseStep 503827 = 755741) B755741
theorem B503843 : Blo 503794 503843 := bstep (se 1 (by rfl) ⟨377882, by rfl⟩ : syracuseStep 503843 = 755765) B755765
theorem B503859 : Blo 503794 503859 := bstep (se 1 (by rfl) ⟨377894, by rfl⟩ : syracuseStep 503859 = 755789) B755789
theorem B503875 : Blo 503794 503875 := bstep (se 1 (by rfl) ⟨377906, by rfl⟩ : syracuseStep 503875 = 755813) B755813
theorem B503891 : Blo 503794 503891 := bstep (se 1 (by rfl) ⟨377918, by rfl⟩ : syracuseStep 503891 = 755837) B755837
theorem B503907 : Blo 503794 503907 := bstep (se 1 (by rfl) ⟨377930, by rfl⟩ : syracuseStep 503907 = 755861) B755861
theorem B569443 : Blo 503794 569443 := bstep (se 1 (by rfl) ⟨427082, by rfl⟩ : syracuseStep 569443 = 854165) B854165
theorem B1028209 : Blo 503794 1028209 := bstep (se 2 (by rfl) ⟨385578, by rfl⟩ : syracuseStep 1028209 = 771157) B771157
theorem B503923 : Blo 503794 503923 := bstep (se 1 (by rfl) ⟨377942, by rfl⟩ : syracuseStep 503923 = 755885) B755885
theorem B503939 : Blo 503794 503939 := bstep (se 1 (by rfl) ⟨377954, by rfl⟩ : syracuseStep 503939 = 755909) B755909
theorem B962705 : Blo 503794 962705 := bstep (se 2 (by rfl) ⟨361014, by rfl⟩ : syracuseStep 962705 = 722029) B722029
theorem B503955 : Blo 503794 503955 := bstep (se 1 (by rfl) ⟨377966, by rfl⟩ : syracuseStep 503955 = 755933) B755933
theorem B503971 : Blo 503794 503971 := bstep (se 1 (by rfl) ⟨377978, by rfl⟩ : syracuseStep 503971 = 755957) B755957
theorem B503987 : Blo 503794 503987 := bstep (se 1 (by rfl) ⟨377990, by rfl⟩ : syracuseStep 503987 = 755981) B755981
theorem B504003 : Blo 503794 504003 := bstep (se 1 (by rfl) ⟨378002, by rfl⟩ : syracuseStep 504003 = 756005) B756005
theorem B504019 : Blo 503794 504019 := bstep (se 1 (by rfl) ⟨378014, by rfl⟩ : syracuseStep 504019 = 756029) B756029
theorem B504035 : Blo 503794 504035 := bstep (se 1 (by rfl) ⟨378026, by rfl⟩ : syracuseStep 504035 = 756053) B756053
theorem B504051 : Blo 503794 504051 := bstep (se 1 (by rfl) ⟨378038, by rfl⟩ : syracuseStep 504051 = 756077) B756077
theorem B569587 : Blo 503794 569587 := bstep (se 1 (by rfl) ⟨427190, by rfl⟩ : syracuseStep 569587 = 854381) B854381
theorem B504067 : Blo 503794 504067 := bstep (se 1 (by rfl) ⟨378050, by rfl⟩ : syracuseStep 504067 = 756101) B756101
theorem B504083 : Blo 503794 504083 := bstep (se 1 (by rfl) ⟨378062, by rfl⟩ : syracuseStep 504083 = 756125) B756125
theorem B504099 : Blo 503794 504099 := bstep (se 1 (by rfl) ⟨378074, by rfl⟩ : syracuseStep 504099 = 756149) B756149
theorem B504115 : Blo 503794 504115 := bstep (se 1 (by rfl) ⟨378086, by rfl⟩ : syracuseStep 504115 = 756173) B756173
theorem B504131 : Blo 503794 504131 := bstep (se 1 (by rfl) ⟨378098, by rfl⟩ : syracuseStep 504131 = 756197) B756197
theorem B504147 : Blo 503794 504147 := bstep (se 1 (by rfl) ⟨378110, by rfl⟩ : syracuseStep 504147 = 756221) B756221
theorem B504163 : Blo 503794 504163 := bstep (se 1 (by rfl) ⟨378122, by rfl⟩ : syracuseStep 504163 = 756245) B756245
theorem B504179 : Blo 503794 504179 := bstep (se 1 (by rfl) ⟨378134, by rfl⟩ : syracuseStep 504179 = 756269) B756269
theorem B504195 : Blo 503794 504195 := bstep (se 1 (by rfl) ⟨378146, by rfl⟩ : syracuseStep 504195 = 756293) B756293
theorem B569731 : Blo 503794 569731 := bstep (se 1 (by rfl) ⟨427298, by rfl⟩ : syracuseStep 569731 = 854597) B854597
theorem B504211 : Blo 503794 504211 := bstep (se 1 (by rfl) ⟨378158, by rfl⟩ : syracuseStep 504211 = 756317) B756317
theorem B504227 : Blo 503794 504227 := bstep (se 1 (by rfl) ⟨378170, by rfl⟩ : syracuseStep 504227 = 756341) B756341
theorem B1618339 : Blo 503794 1618339 := bstep (se 1 (by rfl) ⟨1213754, by rfl⟩ : syracuseStep 1618339 = 2427509) B2427509
theorem B504243 : Blo 503794 504243 := bstep (se 1 (by rfl) ⟨378182, by rfl⟩ : syracuseStep 504243 = 756365) B756365
theorem B504259 : Blo 503794 504259 := bstep (se 1 (by rfl) ⟨378194, by rfl⟩ : syracuseStep 504259 = 756389) B756389
theorem B504275 : Blo 503794 504275 := bstep (se 1 (by rfl) ⟨378206, by rfl⟩ : syracuseStep 504275 = 756413) B756413
theorem B504291 : Blo 503794 504291 := bstep (se 1 (by rfl) ⟨378218, by rfl⟩ : syracuseStep 504291 = 756437) B756437
theorem B504307 : Blo 503794 504307 := bstep (se 1 (by rfl) ⟨378230, by rfl⟩ : syracuseStep 504307 = 756461) B756461
theorem B504323 : Blo 503794 504323 := bstep (se 1 (by rfl) ⟨378242, by rfl⟩ : syracuseStep 504323 = 756485) B756485
theorem B504339 : Blo 503794 504339 := bstep (se 1 (by rfl) ⟨378254, by rfl⟩ : syracuseStep 504339 = 756509) B756509
theorem B569875 : Blo 503794 569875 := bstep (se 1 (by rfl) ⟨427406, by rfl⟩ : syracuseStep 569875 = 854813) B854813
theorem B504355 : Blo 503794 504355 := bstep (se 1 (by rfl) ⟨378266, by rfl⟩ : syracuseStep 504355 = 756533) B756533
theorem B504371 : Blo 503794 504371 := bstep (se 1 (by rfl) ⟨378278, by rfl⟩ : syracuseStep 504371 = 756557) B756557
theorem B504387 : Blo 503794 504387 := bstep (se 1 (by rfl) ⟨378290, by rfl⟩ : syracuseStep 504387 = 756581) B756581
theorem B504403 : Blo 503794 504403 := bstep (se 1 (by rfl) ⟨378302, by rfl⟩ : syracuseStep 504403 = 756605) B756605
theorem B504419 : Blo 503794 504419 := bstep (se 1 (by rfl) ⟨378314, by rfl⟩ : syracuseStep 504419 = 756629) B756629
theorem B504435 : Blo 503794 504435 := bstep (se 1 (by rfl) ⟨378326, by rfl⟩ : syracuseStep 504435 = 756653) B756653
theorem B504451 : Blo 503794 504451 := bstep (se 1 (by rfl) ⟨378338, by rfl⟩ : syracuseStep 504451 = 756677) B756677
theorem B504467 : Blo 503794 504467 := bstep (se 1 (by rfl) ⟨378350, by rfl⟩ : syracuseStep 504467 = 756701) B756701
theorem B504483 : Blo 503794 504483 := bstep (se 1 (by rfl) ⟨378362, by rfl⟩ : syracuseStep 504483 = 756725) B756725
theorem B570019 : Blo 503794 570019 := bstep (se 1 (by rfl) ⟨427514, by rfl⟩ : syracuseStep 570019 = 855029) B855029
theorem B504499 : Blo 503794 504499 := bstep (se 1 (by rfl) ⟨378374, by rfl⟩ : syracuseStep 504499 = 756749) B756749
theorem B504515 : Blo 503794 504515 := bstep (se 1 (by rfl) ⟨378386, by rfl⟩ : syracuseStep 504515 = 756773) B756773
theorem B504531 : Blo 503794 504531 := bstep (se 1 (by rfl) ⟨378398, by rfl⟩ : syracuseStep 504531 = 756797) B756797
theorem B504547 : Blo 503794 504547 := bstep (se 1 (by rfl) ⟨378410, by rfl⟩ : syracuseStep 504547 = 756821) B756821
theorem B504563 : Blo 503794 504563 := bstep (se 1 (by rfl) ⟨378422, by rfl⟩ : syracuseStep 504563 = 756845) B756845
theorem B1454851 : Blo 503794 1454851 := bstep (se 1 (by rfl) ⟨1091138, by rfl⟩ : syracuseStep 1454851 = 2182277) B2182277
theorem B504579 : Blo 503794 504579 := bstep (se 1 (by rfl) ⟨378434, by rfl⟩ : syracuseStep 504579 = 756869) B756869
theorem B504595 : Blo 503794 504595 := bstep (se 1 (by rfl) ⟨378446, by rfl⟩ : syracuseStep 504595 = 756893) B756893
theorem B504611 : Blo 503794 504611 := bstep (se 1 (by rfl) ⟨378458, by rfl⟩ : syracuseStep 504611 = 756917) B756917
theorem B2568995 : Blo 503794 2568995 := bstep (se 1 (by rfl) ⟨1926746, by rfl⟩ : syracuseStep 2568995 = 3853493) B3853493
theorem B504627 : Blo 503794 504627 := bstep (se 1 (by rfl) ⟨378470, by rfl⟩ : syracuseStep 504627 = 756941) B756941
theorem B570163 : Blo 503794 570163 := bstep (se 1 (by rfl) ⟨427622, by rfl⟩ : syracuseStep 570163 = 855245) B855245
theorem B504643 : Blo 503794 504643 := bstep (se 1 (by rfl) ⟨378482, by rfl⟩ : syracuseStep 504643 = 756965) B756965
theorem B504659 : Blo 503794 504659 := bstep (se 1 (by rfl) ⟨378494, by rfl⟩ : syracuseStep 504659 = 756989) B756989
theorem B504675 : Blo 503794 504675 := bstep (se 1 (by rfl) ⟨378506, by rfl⟩ : syracuseStep 504675 = 757013) B757013
theorem B963427 : Blo 503794 963427 := bstep (se 1 (by rfl) ⟨722570, by rfl⟩ : syracuseStep 963427 = 1445141) B1445141
theorem B504691 : Blo 503794 504691 := bstep (se 1 (by rfl) ⟨378518, by rfl⟩ : syracuseStep 504691 = 757037) B757037
theorem B504707 : Blo 503794 504707 := bstep (se 1 (by rfl) ⟨378530, by rfl⟩ : syracuseStep 504707 = 757061) B757061
theorem B504723 : Blo 503794 504723 := bstep (se 1 (by rfl) ⟨378542, by rfl⟩ : syracuseStep 504723 = 757085) B757085
theorem B504739 : Blo 503794 504739 := bstep (se 1 (by rfl) ⟨378554, by rfl⟩ : syracuseStep 504739 = 757109) B757109
theorem B1913777 : Blo 503794 1913777 := bstep (se 2 (by rfl) ⟨717666, by rfl⟩ : syracuseStep 1913777 = 1435333) B1435333
theorem B504755 : Blo 503794 504755 := bstep (se 1 (by rfl) ⟨378566, by rfl⟩ : syracuseStep 504755 = 757133) B757133
theorem B504771 : Blo 503794 504771 := bstep (se 1 (by rfl) ⟨378578, by rfl⟩ : syracuseStep 504771 = 757157) B757157
theorem B570307 : Blo 503794 570307 := bstep (se 1 (by rfl) ⟨427730, by rfl⟩ : syracuseStep 570307 = 855461) B855461
theorem B504787 : Blo 503794 504787 := bstep (se 1 (by rfl) ⟨378590, by rfl⟩ : syracuseStep 504787 = 757181) B757181
theorem B504803 : Blo 503794 504803 := bstep (se 1 (by rfl) ⟨378602, by rfl⟩ : syracuseStep 504803 = 757205) B757205
theorem B1094627 : Blo 503794 1094627 := bstep (se 1 (by rfl) ⟨820970, by rfl⟩ : syracuseStep 1094627 = 1641941) B1641941
theorem B504819 : Blo 503794 504819 := bstep (se 1 (by rfl) ⟨378614, by rfl⟩ : syracuseStep 504819 = 757229) B757229
theorem B504835 : Blo 503794 504835 := bstep (se 1 (by rfl) ⟨378626, by rfl⟩ : syracuseStep 504835 = 757253) B757253
theorem B504851 : Blo 503794 504851 := bstep (se 1 (by rfl) ⟨378638, by rfl⟩ : syracuseStep 504851 = 757277) B757277
theorem B504867 : Blo 503794 504867 := bstep (se 1 (by rfl) ⟨378650, by rfl⟩ : syracuseStep 504867 = 757301) B757301
theorem B832547 : Blo 503794 832547 := bstep (se 1 (by rfl) ⟨624410, by rfl⟩ : syracuseStep 832547 = 1248821) B1248821
theorem B504883 : Blo 503794 504883 := bstep (se 1 (by rfl) ⟨378662, by rfl⟩ : syracuseStep 504883 = 757325) B757325
theorem B504899 : Blo 503794 504899 := bstep (se 1 (by rfl) ⟨378674, by rfl⟩ : syracuseStep 504899 = 757349) B757349
theorem B504915 : Blo 503794 504915 := bstep (se 1 (by rfl) ⟨378686, by rfl⟩ : syracuseStep 504915 = 757373) B757373
theorem B570451 : Blo 503794 570451 := bstep (se 1 (by rfl) ⟨427838, by rfl⟩ : syracuseStep 570451 = 855677) B855677
theorem B504931 : Blo 503794 504931 := bstep (se 1 (by rfl) ⟨378698, by rfl⟩ : syracuseStep 504931 = 757397) B757397
theorem B504947 : Blo 503794 504947 := bstep (se 1 (by rfl) ⟨378710, by rfl⟩ : syracuseStep 504947 = 757421) B757421
theorem B504963 : Blo 503794 504963 := bstep (se 1 (by rfl) ⟨378722, by rfl⟩ : syracuseStep 504963 = 757445) B757445
theorem B504979 : Blo 503794 504979 := bstep (se 1 (by rfl) ⟨378734, by rfl⟩ : syracuseStep 504979 = 757469) B757469
theorem B504995 : Blo 503794 504995 := bstep (se 1 (by rfl) ⟨378746, by rfl⟩ : syracuseStep 504995 = 757493) B757493
theorem B505011 : Blo 503794 505011 := bstep (se 1 (by rfl) ⟨378758, by rfl⟩ : syracuseStep 505011 = 757517) B757517
theorem B505027 : Blo 503794 505027 := bstep (se 1 (by rfl) ⟨378770, by rfl⟩ : syracuseStep 505027 = 757541) B757541
theorem B505043 : Blo 503794 505043 := bstep (se 1 (by rfl) ⟨378782, by rfl⟩ : syracuseStep 505043 = 757565) B757565
theorem B505059 : Blo 503794 505059 := bstep (se 1 (by rfl) ⟨378794, by rfl⟩ : syracuseStep 505059 = 757589) B757589
theorem B570595 : Blo 503794 570595 := bstep (se 1 (by rfl) ⟨427946, by rfl⟩ : syracuseStep 570595 = 855893) B855893
theorem B505075 : Blo 503794 505075 := bstep (se 1 (by rfl) ⟨378806, by rfl⟩ : syracuseStep 505075 = 757613) B757613
theorem B505091 : Blo 503794 505091 := bstep (se 1 (by rfl) ⟨378818, by rfl⟩ : syracuseStep 505091 = 757637) B757637
theorem B505107 : Blo 503794 505107 := bstep (se 1 (by rfl) ⟨378830, by rfl⟩ : syracuseStep 505107 = 757661) B757661
theorem B505123 : Blo 503794 505123 := bstep (se 1 (by rfl) ⟨378842, by rfl⟩ : syracuseStep 505123 = 757685) B757685
theorem B963875 : Blo 503794 963875 := bstep (se 1 (by rfl) ⟨722906, by rfl⟩ : syracuseStep 963875 = 1445813) B1445813
theorem B505139 : Blo 503794 505139 := bstep (se 1 (by rfl) ⟨378854, by rfl⟩ : syracuseStep 505139 = 757709) B757709
theorem B505155 : Blo 503794 505155 := bstep (se 1 (by rfl) ⟨378866, by rfl⟩ : syracuseStep 505155 = 757733) B757733
theorem B505171 : Blo 503794 505171 := bstep (se 1 (by rfl) ⟨378878, by rfl⟩ : syracuseStep 505171 = 757757) B757757
theorem B505187 : Blo 503794 505187 := bstep (se 1 (by rfl) ⟨378890, by rfl⟩ : syracuseStep 505187 = 757781) B757781
theorem B505203 : Blo 503794 505203 := bstep (se 1 (by rfl) ⟨378902, by rfl⟩ : syracuseStep 505203 = 757805) B757805
theorem B570739 : Blo 503794 570739 := bstep (se 1 (by rfl) ⟨428054, by rfl⟩ : syracuseStep 570739 = 856109) B856109
theorem B505219 : Blo 503794 505219 := bstep (se 1 (by rfl) ⟨378914, by rfl⟩ : syracuseStep 505219 = 757829) B757829
theorem B505235 : Blo 503794 505235 := bstep (se 1 (by rfl) ⟨378926, by rfl⟩ : syracuseStep 505235 = 757853) B757853
theorem B505251 : Blo 503794 505251 := bstep (se 1 (by rfl) ⟨378938, by rfl⟩ : syracuseStep 505251 = 757877) B757877
theorem B505267 : Blo 503794 505267 := bstep (se 1 (by rfl) ⟨378950, by rfl⟩ : syracuseStep 505267 = 757901) B757901
theorem B505283 : Blo 503794 505283 := bstep (se 1 (by rfl) ⟨378962, by rfl⟩ : syracuseStep 505283 = 757925) B757925
theorem B505299 : Blo 503794 505299 := bstep (se 1 (by rfl) ⟨378974, by rfl⟩ : syracuseStep 505299 = 757949) B757949
theorem B505315 : Blo 503794 505315 := bstep (se 1 (by rfl) ⟨378986, by rfl⟩ : syracuseStep 505315 = 757973) B757973
theorem B505331 : Blo 503794 505331 := bstep (se 1 (by rfl) ⟨378998, by rfl⟩ : syracuseStep 505331 = 757997) B757997
theorem B505347 : Blo 503794 505347 := bstep (se 1 (by rfl) ⟨379010, by rfl⟩ : syracuseStep 505347 = 758021) B758021
theorem B570883 : Blo 503794 570883 := bstep (se 1 (by rfl) ⟨428162, by rfl⟩ : syracuseStep 570883 = 856325) B856325
theorem B4306445 : Blo 503794 4306445 := bstep (se 3 (by rfl) ⟨807458, by rfl⟩ : syracuseStep 4306445 = 1614917) B1614917
theorem B505363 : Blo 503794 505363 := bstep (se 1 (by rfl) ⟨379022, by rfl⟩ : syracuseStep 505363 = 758045) B758045
theorem B505379 : Blo 503794 505379 := bstep (se 1 (by rfl) ⟨379034, by rfl⟩ : syracuseStep 505379 = 758069) B758069
theorem B505395 : Blo 503794 505395 := bstep (se 1 (by rfl) ⟨379046, by rfl⟩ : syracuseStep 505395 = 758093) B758093
theorem B505411 : Blo 503794 505411 := bstep (se 1 (by rfl) ⟨379058, by rfl⟩ : syracuseStep 505411 = 758117) B758117
theorem B2569805 : Blo 503794 2569805 := bstep (se 3 (by rfl) ⟨481838, by rfl⟩ : syracuseStep 2569805 = 963677) B963677
theorem B505427 : Blo 503794 505427 := bstep (se 1 (by rfl) ⟨379070, by rfl⟩ : syracuseStep 505427 = 758141) B758141
theorem B505443 : Blo 503794 505443 := bstep (se 1 (by rfl) ⟨379082, by rfl⟩ : syracuseStep 505443 = 758165) B758165
theorem B505459 : Blo 503794 505459 := bstep (se 1 (by rfl) ⟨379094, by rfl⟩ : syracuseStep 505459 = 758189) B758189
theorem B505475 : Blo 503794 505475 := bstep (se 1 (by rfl) ⟨379106, by rfl⟩ : syracuseStep 505475 = 758213) B758213
theorem B505491 : Blo 503794 505491 := bstep (se 1 (by rfl) ⟨379118, by rfl⟩ : syracuseStep 505491 = 758237) B758237
theorem B571027 : Blo 503794 571027 := bstep (se 1 (by rfl) ⟨428270, by rfl⟩ : syracuseStep 571027 = 856541) B856541
theorem B505507 : Blo 503794 505507 := bstep (se 1 (by rfl) ⟨379130, by rfl⟩ : syracuseStep 505507 = 758261) B758261
theorem B505523 : Blo 503794 505523 := bstep (se 1 (by rfl) ⟨379142, by rfl⟩ : syracuseStep 505523 = 758285) B758285
theorem B505539 : Blo 503794 505539 := bstep (se 1 (by rfl) ⟨379154, by rfl⟩ : syracuseStep 505539 = 758309) B758309
theorem B505555 : Blo 503794 505555 := bstep (se 1 (by rfl) ⟨379166, by rfl⟩ : syracuseStep 505555 = 758333) B758333
theorem B505571 : Blo 503794 505571 := bstep (se 1 (by rfl) ⟨379178, by rfl⟩ : syracuseStep 505571 = 758357) B758357
theorem B505587 : Blo 503794 505587 := bstep (se 1 (by rfl) ⟨379190, by rfl⟩ : syracuseStep 505587 = 758381) B758381
theorem B505603 : Blo 503794 505603 := bstep (se 1 (by rfl) ⟨379202, by rfl⟩ : syracuseStep 505603 = 758405) B758405
theorem B505619 : Blo 503794 505619 := bstep (se 1 (by rfl) ⟨379214, by rfl⟩ : syracuseStep 505619 = 758429) B758429
theorem B505635 : Blo 503794 505635 := bstep (se 1 (by rfl) ⟨379226, by rfl⟩ : syracuseStep 505635 = 758453) B758453
theorem B571171 : Blo 503794 571171 := bstep (se 1 (by rfl) ⟨428378, by rfl⟩ : syracuseStep 571171 = 856757) B856757
theorem B505651 : Blo 503794 505651 := bstep (se 1 (by rfl) ⟨379238, by rfl⟩ : syracuseStep 505651 = 758477) B758477
theorem B505667 : Blo 503794 505667 := bstep (se 1 (by rfl) ⟨379250, by rfl⟩ : syracuseStep 505667 = 758501) B758501
theorem B505683 : Blo 503794 505683 := bstep (se 1 (by rfl) ⟨379262, by rfl⟩ : syracuseStep 505683 = 758525) B758525
theorem B505699 : Blo 503794 505699 := bstep (se 1 (by rfl) ⟨379274, by rfl⟩ : syracuseStep 505699 = 758549) B758549
theorem B505715 : Blo 503794 505715 := bstep (se 1 (by rfl) ⟨379286, by rfl⟩ : syracuseStep 505715 = 758573) B758573
theorem B767873 : Blo 503794 767873 := bstep (se 2 (by rfl) ⟨287952, by rfl⟩ : syracuseStep 767873 = 575905) B575905
theorem B505731 : Blo 503794 505731 := bstep (se 1 (by rfl) ⟨379298, by rfl⟩ : syracuseStep 505731 = 758597) B758597
theorem B505747 : Blo 503794 505747 := bstep (se 1 (by rfl) ⟨379310, by rfl⟩ : syracuseStep 505747 = 758621) B758621
theorem B505763 : Blo 503794 505763 := bstep (se 1 (by rfl) ⟨379322, by rfl⟩ : syracuseStep 505763 = 758645) B758645
theorem B505779 : Blo 503794 505779 := bstep (se 1 (by rfl) ⟨379334, by rfl⟩ : syracuseStep 505779 = 758669) B758669
theorem B505795 : Blo 503794 505795 := bstep (se 1 (by rfl) ⟨379346, by rfl⟩ : syracuseStep 505795 = 758693) B758693
theorem B538579 : Blo 503794 538579 := bstep (se 1 (by rfl) ⟨403934, by rfl⟩ : syracuseStep 538579 = 807869) B807869
theorem B505811 : Blo 503794 505811 := bstep (se 1 (by rfl) ⟨379358, by rfl⟩ : syracuseStep 505811 = 758717) B758717
theorem B505827 : Blo 503794 505827 := bstep (se 1 (by rfl) ⟨379370, by rfl⟩ : syracuseStep 505827 = 758741) B758741
theorem B505843 : Blo 503794 505843 := bstep (se 1 (by rfl) ⟨379382, by rfl⟩ : syracuseStep 505843 = 758765) B758765
theorem B505859 : Blo 503794 505859 := bstep (se 1 (by rfl) ⟨379394, by rfl⟩ : syracuseStep 505859 = 758789) B758789
theorem B505875 : Blo 503794 505875 := bstep (se 1 (by rfl) ⟨379406, by rfl⟩ : syracuseStep 505875 = 758813) B758813
theorem B505891 : Blo 503794 505891 := bstep (se 1 (by rfl) ⟨379418, by rfl⟩ : syracuseStep 505891 = 758837) B758837
theorem B2504753 : Blo 503794 2504753 := bstep (se 2 (by rfl) ⟨939282, by rfl⟩ : syracuseStep 2504753 = 1878565) B1878565
theorem B505907 : Blo 503794 505907 := bstep (se 1 (by rfl) ⟨379430, by rfl⟩ : syracuseStep 505907 = 758861) B758861
theorem B505923 : Blo 503794 505923 := bstep (se 1 (by rfl) ⟨379442, by rfl⟩ : syracuseStep 505923 = 758885) B758885
theorem B505939 : Blo 503794 505939 := bstep (se 1 (by rfl) ⟨379454, by rfl⟩ : syracuseStep 505939 = 758909) B758909
theorem B505955 : Blo 503794 505955 := bstep (se 1 (by rfl) ⟨379466, by rfl⟩ : syracuseStep 505955 = 758933) B758933
theorem B505971 : Blo 503794 505971 := bstep (se 1 (by rfl) ⟨379478, by rfl⟩ : syracuseStep 505971 = 758957) B758957
theorem B505987 : Blo 503794 505987 := bstep (se 1 (by rfl) ⟨379490, by rfl⟩ : syracuseStep 505987 = 758981) B758981
theorem B506003 : Blo 503794 506003 := bstep (se 1 (by rfl) ⟨379502, by rfl⟩ : syracuseStep 506003 = 759005) B759005
theorem B506019 : Blo 503794 506019 := bstep (se 1 (by rfl) ⟨379514, by rfl⟩ : syracuseStep 506019 = 759029) B759029
theorem B506035 : Blo 503794 506035 := bstep (se 1 (by rfl) ⟨379526, by rfl⟩ : syracuseStep 506035 = 759053) B759053
theorem B506051 : Blo 503794 506051 := bstep (se 1 (by rfl) ⟨379538, by rfl⟩ : syracuseStep 506051 = 759077) B759077
theorem B506067 : Blo 503794 506067 := bstep (se 1 (by rfl) ⟨379550, by rfl⟩ : syracuseStep 506067 = 759101) B759101
theorem B506083 : Blo 503794 506083 := bstep (se 1 (by rfl) ⟨379562, by rfl⟩ : syracuseStep 506083 = 759125) B759125
theorem B506099 : Blo 503794 506099 := bstep (se 1 (by rfl) ⟨379574, by rfl⟩ : syracuseStep 506099 = 759149) B759149
theorem B506115 : Blo 503794 506115 := bstep (se 1 (by rfl) ⟨379586, by rfl⟩ : syracuseStep 506115 = 759173) B759173
theorem B506131 : Blo 503794 506131 := bstep (se 1 (by rfl) ⟨379598, by rfl⟩ : syracuseStep 506131 = 759197) B759197
theorem B506147 : Blo 503794 506147 := bstep (se 1 (by rfl) ⟨379610, by rfl⟩ : syracuseStep 506147 = 759221) B759221
theorem B506163 : Blo 503794 506163 := bstep (se 1 (by rfl) ⟨379622, by rfl⟩ : syracuseStep 506163 = 759245) B759245
theorem B506179 : Blo 503794 506179 := bstep (se 1 (by rfl) ⟨379634, by rfl⟩ : syracuseStep 506179 = 759269) B759269
theorem B506195 : Blo 503794 506195 := bstep (se 1 (by rfl) ⟨379646, by rfl⟩ : syracuseStep 506195 = 759293) B759293
theorem B1915235 : Blo 503794 1915235 := bstep (se 1 (by rfl) ⟨1436426, by rfl⟩ : syracuseStep 1915235 = 2872853) B2872853
theorem B506211 : Blo 503794 506211 := bstep (se 1 (by rfl) ⟨379658, by rfl⟩ : syracuseStep 506211 = 759317) B759317
theorem B506227 : Blo 503794 506227 := bstep (se 1 (by rfl) ⟨379670, by rfl⟩ : syracuseStep 506227 = 759341) B759341
theorem B506243 : Blo 503794 506243 := bstep (se 1 (by rfl) ⟨379682, by rfl⟩ : syracuseStep 506243 = 759365) B759365
theorem B506259 : Blo 503794 506259 := bstep (se 1 (by rfl) ⟨379694, by rfl⟩ : syracuseStep 506259 = 759389) B759389
theorem B506275 : Blo 503794 506275 := bstep (se 1 (by rfl) ⟨379706, by rfl⟩ : syracuseStep 506275 = 759413) B759413
theorem B506291 : Blo 503794 506291 := bstep (se 1 (by rfl) ⟨379718, by rfl⟩ : syracuseStep 506291 = 759437) B759437
theorem B506307 : Blo 503794 506307 := bstep (se 1 (by rfl) ⟨379730, by rfl⟩ : syracuseStep 506307 = 759461) B759461
theorem B506323 : Blo 503794 506323 := bstep (se 1 (by rfl) ⟨379742, by rfl⟩ : syracuseStep 506323 = 759485) B759485
theorem B506339 : Blo 503794 506339 := bstep (se 1 (by rfl) ⟨379754, by rfl⟩ : syracuseStep 506339 = 759509) B759509
theorem B506355 : Blo 503794 506355 := bstep (se 1 (by rfl) ⟨379766, by rfl⟩ : syracuseStep 506355 = 759533) B759533
theorem B506371 : Blo 503794 506371 := bstep (se 1 (by rfl) ⟨379778, by rfl⟩ : syracuseStep 506371 = 759557) B759557
theorem B506387 : Blo 503794 506387 := bstep (se 1 (by rfl) ⟨379790, by rfl⟩ : syracuseStep 506387 = 759581) B759581
theorem B506403 : Blo 503794 506403 := bstep (se 1 (by rfl) ⟨379802, by rfl⟩ : syracuseStep 506403 = 759605) B759605
theorem B506419 : Blo 503794 506419 := bstep (se 1 (by rfl) ⟨379814, by rfl⟩ : syracuseStep 506419 = 759629) B759629
theorem B506435 : Blo 503794 506435 := bstep (se 1 (by rfl) ⟨379826, by rfl⟩ : syracuseStep 506435 = 759653) B759653
theorem B1620557 : Blo 503794 1620557 := bstep (se 3 (by rfl) ⟨303854, by rfl⟩ : syracuseStep 1620557 = 607709) B607709
theorem B506451 : Blo 503794 506451 := bstep (se 1 (by rfl) ⟨379838, by rfl⟩ : syracuseStep 506451 = 759677) B759677
theorem B506467 : Blo 503794 506467 := bstep (se 1 (by rfl) ⟨379850, by rfl⟩ : syracuseStep 506467 = 759701) B759701
theorem B506483 : Blo 503794 506483 := bstep (se 1 (by rfl) ⟨379862, by rfl⟩ : syracuseStep 506483 = 759725) B759725
theorem B506499 : Blo 503794 506499 := bstep (se 1 (by rfl) ⟨379874, by rfl⟩ : syracuseStep 506499 = 759749) B759749
theorem B506515 : Blo 503794 506515 := bstep (se 1 (by rfl) ⟨379886, by rfl⟩ : syracuseStep 506515 = 759773) B759773
theorem B506531 : Blo 503794 506531 := bstep (se 1 (by rfl) ⟨379898, by rfl⟩ : syracuseStep 506531 = 759797) B759797
theorem B506547 : Blo 503794 506547 := bstep (se 1 (by rfl) ⟨379910, by rfl⟩ : syracuseStep 506547 = 759821) B759821
theorem B506563 : Blo 503794 506563 := bstep (se 1 (by rfl) ⟨379922, by rfl⟩ : syracuseStep 506563 = 759845) B759845
theorem B506579 : Blo 503794 506579 := bstep (se 1 (by rfl) ⟨379934, by rfl⟩ : syracuseStep 506579 = 759869) B759869
theorem B506595 : Blo 503794 506595 := bstep (se 1 (by rfl) ⟨379946, by rfl⟩ : syracuseStep 506595 = 759893) B759893
theorem B506611 : Blo 503794 506611 := bstep (se 1 (by rfl) ⟨379958, by rfl⟩ : syracuseStep 506611 = 759917) B759917
theorem B506627 : Blo 503794 506627 := bstep (se 1 (by rfl) ⟨379970, by rfl⟩ : syracuseStep 506627 = 759941) B759941
theorem B506643 : Blo 503794 506643 := bstep (se 1 (by rfl) ⟨379982, by rfl⟩ : syracuseStep 506643 = 759965) B759965
theorem B2734883 : Blo 503794 2734883 := bstep (se 1 (by rfl) ⟨2051162, by rfl⟩ : syracuseStep 2734883 = 4102325) B4102325
theorem B506659 : Blo 503794 506659 := bstep (se 1 (by rfl) ⟨379994, by rfl⟩ : syracuseStep 506659 = 759989) B759989
theorem B506675 : Blo 503794 506675 := bstep (se 1 (by rfl) ⟨380006, by rfl⟩ : syracuseStep 506675 = 760013) B760013
theorem B506691 : Blo 503794 506691 := bstep (se 1 (by rfl) ⟨380018, by rfl⟩ : syracuseStep 506691 = 760037) B760037
theorem B506707 : Blo 503794 506707 := bstep (se 1 (by rfl) ⟨380030, by rfl⟩ : syracuseStep 506707 = 760061) B760061
theorem B506723 : Blo 503794 506723 := bstep (se 1 (by rfl) ⟨380042, by rfl⟩ : syracuseStep 506723 = 760085) B760085
theorem B506739 : Blo 503794 506739 := bstep (se 1 (by rfl) ⟨380054, by rfl⟩ : syracuseStep 506739 = 760109) B760109
theorem B506755 : Blo 503794 506755 := bstep (se 1 (by rfl) ⟨380066, by rfl⟩ : syracuseStep 506755 = 760133) B760133
theorem B506771 : Blo 503794 506771 := bstep (se 1 (by rfl) ⟨380078, by rfl⟩ : syracuseStep 506771 = 760157) B760157
theorem B506787 : Blo 503794 506787 := bstep (se 1 (by rfl) ⟨380090, by rfl⟩ : syracuseStep 506787 = 760181) B760181
theorem B506803 : Blo 503794 506803 := bstep (se 1 (by rfl) ⟨380102, by rfl⟩ : syracuseStep 506803 = 760205) B760205
theorem B506819 : Blo 503794 506819 := bstep (se 1 (by rfl) ⟨380114, by rfl⟩ : syracuseStep 506819 = 760229) B760229
theorem B506835 : Blo 503794 506835 := bstep (se 1 (by rfl) ⟨380126, by rfl⟩ : syracuseStep 506835 = 760253) B760253
theorem B506851 : Blo 503794 506851 := bstep (se 1 (by rfl) ⟨380138, by rfl⟩ : syracuseStep 506851 = 760277) B760277
theorem B1620977 : Blo 503794 1620977 := bstep (se 2 (by rfl) ⟨607866, by rfl⟩ : syracuseStep 1620977 = 1215733) B1215733
theorem B506867 : Blo 503794 506867 := bstep (se 1 (by rfl) ⟨380150, by rfl⟩ : syracuseStep 506867 = 760301) B760301
theorem B506883 : Blo 503794 506883 := bstep (se 1 (by rfl) ⟨380162, by rfl⟩ : syracuseStep 506883 = 760325) B760325
theorem B506899 : Blo 503794 506899 := bstep (se 1 (by rfl) ⟨380174, by rfl⟩ : syracuseStep 506899 = 760349) B760349
theorem B703523 : Blo 503794 703523 := bstep (se 1 (by rfl) ⟨527642, by rfl⟩ : syracuseStep 703523 = 1055285) B1055285
theorem B506915 : Blo 503794 506915 := bstep (se 1 (by rfl) ⟨380186, by rfl⟩ : syracuseStep 506915 = 760373) B760373
theorem B506931 : Blo 503794 506931 := bstep (se 1 (by rfl) ⟨380198, by rfl⟩ : syracuseStep 506931 = 760397) B760397
theorem B506947 : Blo 503794 506947 := bstep (se 1 (by rfl) ⟨380210, by rfl⟩ : syracuseStep 506947 = 760421) B760421
theorem B506963 : Blo 503794 506963 := bstep (se 1 (by rfl) ⟨380222, by rfl⟩ : syracuseStep 506963 = 760445) B760445
theorem B506979 : Blo 503794 506979 := bstep (se 1 (by rfl) ⟨380234, by rfl⟩ : syracuseStep 506979 = 760469) B760469
theorem B506995 : Blo 503794 506995 := bstep (se 1 (by rfl) ⟨380246, by rfl⟩ : syracuseStep 506995 = 760493) B760493
theorem B507011 : Blo 503794 507011 := bstep (se 1 (by rfl) ⟨380258, by rfl⟩ : syracuseStep 507011 = 760517) B760517
theorem B1457297 : Blo 503794 1457297 := bstep (se 2 (by rfl) ⟨546486, by rfl⟩ : syracuseStep 1457297 = 1092973) B1092973
theorem B507027 : Blo 503794 507027 := bstep (se 1 (by rfl) ⟨380270, by rfl⟩ : syracuseStep 507027 = 760541) B760541
theorem B507043 : Blo 503794 507043 := bstep (se 1 (by rfl) ⟨380282, by rfl⟩ : syracuseStep 507043 = 760565) B760565
theorem B1817777 : Blo 503794 1817777 := bstep (se 2 (by rfl) ⟨681666, by rfl⟩ : syracuseStep 1817777 = 1363333) B1363333
theorem B507059 : Blo 503794 507059 := bstep (se 1 (by rfl) ⟨380294, by rfl⟩ : syracuseStep 507059 = 760589) B760589
theorem B507075 : Blo 503794 507075 := bstep (se 1 (by rfl) ⟨380306, by rfl⟩ : syracuseStep 507075 = 760613) B760613
theorem B507091 : Blo 503794 507091 := bstep (se 1 (by rfl) ⟨380318, by rfl⟩ : syracuseStep 507091 = 760637) B760637
theorem B507107 : Blo 503794 507107 := bstep (se 1 (by rfl) ⟨380330, by rfl⟩ : syracuseStep 507107 = 760661) B760661
theorem B507123 : Blo 503794 507123 := bstep (se 1 (by rfl) ⟨380342, by rfl⟩ : syracuseStep 507123 = 760685) B760685
theorem B507139 : Blo 503794 507139 := bstep (se 1 (by rfl) ⟨380354, by rfl⟩ : syracuseStep 507139 = 760709) B760709
theorem B507155 : Blo 503794 507155 := bstep (se 1 (by rfl) ⟨380366, by rfl⟩ : syracuseStep 507155 = 760733) B760733
theorem B507171 : Blo 503794 507171 := bstep (se 1 (by rfl) ⟨380378, by rfl⟩ : syracuseStep 507171 = 760757) B760757
theorem B507187 : Blo 503794 507187 := bstep (se 1 (by rfl) ⟨380390, by rfl⟩ : syracuseStep 507187 = 760781) B760781
theorem B638275 : Blo 503794 638275 := bstep (se 1 (by rfl) ⟨478706, by rfl⟩ : syracuseStep 638275 = 957413) B957413
theorem B507203 : Blo 503794 507203 := bstep (se 1 (by rfl) ⟨380402, by rfl⟩ : syracuseStep 507203 = 760805) B760805
theorem B1916237 : Blo 503794 1916237 := bstep (se 3 (by rfl) ⟨359294, by rfl⟩ : syracuseStep 1916237 = 718589) B718589
theorem B507219 : Blo 503794 507219 := bstep (se 1 (by rfl) ⟨380414, by rfl⟩ : syracuseStep 507219 = 760829) B760829
theorem B507235 : Blo 503794 507235 := bstep (se 1 (by rfl) ⟨380426, by rfl⟩ : syracuseStep 507235 = 760853) B760853
theorem B507251 : Blo 503794 507251 := bstep (se 1 (by rfl) ⟨380438, by rfl⟩ : syracuseStep 507251 = 760877) B760877
theorem B507267 : Blo 503794 507267 := bstep (se 1 (by rfl) ⟨380450, by rfl⟩ : syracuseStep 507267 = 760901) B760901
theorem B507283 : Blo 503794 507283 := bstep (se 1 (by rfl) ⟨380462, by rfl⟩ : syracuseStep 507283 = 760925) B760925
theorem B638371 : Blo 503794 638371 := bstep (se 1 (by rfl) ⟨478778, by rfl⟩ : syracuseStep 638371 = 957557) B957557
theorem B507299 : Blo 503794 507299 := bstep (se 1 (by rfl) ⟨380474, by rfl⟩ : syracuseStep 507299 = 760949) B760949
theorem B507315 : Blo 503794 507315 := bstep (se 1 (by rfl) ⟨380486, by rfl⟩ : syracuseStep 507315 = 760973) B760973
theorem B507331 : Blo 503794 507331 := bstep (se 1 (by rfl) ⟨380498, by rfl⟩ : syracuseStep 507331 = 760997) B760997
theorem B507347 : Blo 503794 507347 := bstep (se 1 (by rfl) ⟨380510, by rfl⟩ : syracuseStep 507347 = 761021) B761021
theorem B507363 : Blo 503794 507363 := bstep (se 1 (by rfl) ⟨380522, by rfl⟩ : syracuseStep 507363 = 761045) B761045
theorem B507379 : Blo 503794 507379 := bstep (se 1 (by rfl) ⟨380534, by rfl⟩ : syracuseStep 507379 = 761069) B761069
theorem B507395 : Blo 503794 507395 := bstep (se 1 (by rfl) ⟨380546, by rfl⟩ : syracuseStep 507395 = 761093) B761093
theorem B507411 : Blo 503794 507411 := bstep (se 1 (by rfl) ⟨380558, by rfl⟩ : syracuseStep 507411 = 761117) B761117
theorem B507427 : Blo 503794 507427 := bstep (se 1 (by rfl) ⟨380570, by rfl⟩ : syracuseStep 507427 = 761141) B761141
theorem B507443 : Blo 503794 507443 := bstep (se 1 (by rfl) ⟨380582, by rfl⟩ : syracuseStep 507443 = 761165) B761165
theorem B507459 : Blo 503794 507459 := bstep (se 1 (by rfl) ⟨380594, by rfl⟩ : syracuseStep 507459 = 761189) B761189
theorem B507475 : Blo 503794 507475 := bstep (se 1 (by rfl) ⟨380606, by rfl⟩ : syracuseStep 507475 = 761213) B761213
theorem B507491 : Blo 503794 507491 := bstep (se 1 (by rfl) ⟨380618, by rfl⟩ : syracuseStep 507491 = 761237) B761237
theorem B507507 : Blo 503794 507507 := bstep (se 1 (by rfl) ⟨380630, by rfl⟩ : syracuseStep 507507 = 761261) B761261
theorem B507523 : Blo 503794 507523 := bstep (se 1 (by rfl) ⟨380642, by rfl⟩ : syracuseStep 507523 = 761285) B761285
theorem B507539 : Blo 503794 507539 := bstep (se 1 (by rfl) ⟨380654, by rfl⟩ : syracuseStep 507539 = 761309) B761309
theorem B507555 : Blo 503794 507555 := bstep (se 1 (by rfl) ⟨380666, by rfl⟩ : syracuseStep 507555 = 761333) B761333
theorem B2604707 : Blo 503794 2604707 := bstep (se 1 (by rfl) ⟨1953530, by rfl⟩ : syracuseStep 2604707 = 3907061) B3907061
theorem B507571 : Blo 503794 507571 := bstep (se 1 (by rfl) ⟨380678, by rfl⟩ : syracuseStep 507571 = 761357) B761357
theorem B507587 : Blo 503794 507587 := bstep (se 1 (by rfl) ⟨380690, by rfl⟩ : syracuseStep 507587 = 761381) B761381
theorem B507603 : Blo 503794 507603 := bstep (se 1 (by rfl) ⟨380702, by rfl⟩ : syracuseStep 507603 = 761405) B761405
theorem B507619 : Blo 503794 507619 := bstep (se 1 (by rfl) ⟨380714, by rfl⟩ : syracuseStep 507619 = 761429) B761429
theorem B507635 : Blo 503794 507635 := bstep (se 1 (by rfl) ⟨380726, by rfl⟩ : syracuseStep 507635 = 761453) B761453
theorem B507651 : Blo 503794 507651 := bstep (se 1 (by rfl) ⟨380738, by rfl⟩ : syracuseStep 507651 = 761477) B761477
theorem B1949453 : Blo 503794 1949453 := bstep (se 3 (by rfl) ⟨365522, by rfl⟩ : syracuseStep 1949453 = 731045) B731045
theorem B507667 : Blo 503794 507667 := bstep (se 1 (by rfl) ⟨380750, by rfl⟩ : syracuseStep 507667 = 761501) B761501
theorem B507683 : Blo 503794 507683 := bstep (se 1 (by rfl) ⟨380762, by rfl⟩ : syracuseStep 507683 = 761525) B761525
theorem B507699 : Blo 503794 507699 := bstep (se 1 (by rfl) ⟨380774, by rfl⟩ : syracuseStep 507699 = 761549) B761549
theorem B507715 : Blo 503794 507715 := bstep (se 1 (by rfl) ⟨380786, by rfl⟩ : syracuseStep 507715 = 761573) B761573
theorem B507731 : Blo 503794 507731 := bstep (se 1 (by rfl) ⟨380798, by rfl⟩ : syracuseStep 507731 = 761597) B761597
theorem B507747 : Blo 503794 507747 := bstep (se 1 (by rfl) ⟨380810, by rfl⟩ : syracuseStep 507747 = 761621) B761621
theorem B507763 : Blo 503794 507763 := bstep (se 1 (by rfl) ⟨380822, by rfl⟩ : syracuseStep 507763 = 761645) B761645
theorem B507779 : Blo 503794 507779 := bstep (se 1 (by rfl) ⟨380834, by rfl⟩ : syracuseStep 507779 = 761669) B761669
theorem B638867 : Blo 503794 638867 := bstep (se 1 (by rfl) ⟨479150, by rfl⟩ : syracuseStep 638867 = 958301) B958301
theorem B1818787 : Blo 503794 1818787 := bstep (se 1 (by rfl) ⟨1364090, by rfl⟩ : syracuseStep 1818787 = 2728181) B2728181
theorem B770305 : Blo 503794 770305 := bstep (se 2 (by rfl) ⟨288864, by rfl⟩ : syracuseStep 770305 = 577729) B577729
theorem B4866317 : Blo 503794 4866317 := bstep (se 3 (by rfl) ⟨912434, by rfl⟩ : syracuseStep 4866317 = 1824869) B1824869
theorem B9716021 : Blo 503794 9716021 := bstep (se 5 (by rfl) ⟨455438, by rfl⟩ : syracuseStep 9716021 = 910877) B910877
theorem B2769221 : Blo 503794 2769221 := bstep (se 4 (by rfl) ⟨259614, by rfl⟩ : syracuseStep 2769221 = 519229) B519229
theorem B8176099 : Blo 503794 8176099 := bstep (se 1 (by rfl) ⟨6132074, by rfl⟩ : syracuseStep 8176099 = 12264149) B12264149
theorem B639571 : Blo 503794 639571 := bstep (se 1 (by rfl) ⟨479678, by rfl⟩ : syracuseStep 639571 = 959357) B959357
theorem B639667 : Blo 503794 639667 := bstep (se 1 (by rfl) ⟨479750, by rfl⟩ : syracuseStep 639667 = 959501) B959501
theorem B3130211 : Blo 503794 3130211 := bstep (se 1 (by rfl) ⟨2347658, by rfl⟩ : syracuseStep 3130211 = 4695317) B4695317
theorem B771059 : Blo 503794 771059 := bstep (se 1 (by rfl) ⟨578294, by rfl⟩ : syracuseStep 771059 = 1156589) B1156589
theorem B640163 : Blo 503794 640163 := bstep (se 1 (by rfl) ⟨480122, by rfl⟩ : syracuseStep 640163 = 960245) B960245
theorem B1819853 : Blo 503794 1819853 := bstep (se 3 (by rfl) ⟨341222, by rfl⟩ : syracuseStep 1819853 = 682445) B682445
theorem B1918349 : Blo 503794 1918349 := bstep (se 3 (by rfl) ⟨359690, by rfl⟩ : syracuseStep 1918349 = 719381) B719381
theorem B542099 : Blo 503794 542099 := bstep (se 1 (by rfl) ⟨406574, by rfl⟩ : syracuseStep 542099 = 813149) B813149
theorem B3229091 : Blo 503794 3229091 := bstep (se 1 (by rfl) ⟨2421818, by rfl⟩ : syracuseStep 3229091 = 4843637) B4843637
theorem B5817827 : Blo 503794 5817827 := bstep (se 1 (by rfl) ⟨4363370, by rfl⟩ : syracuseStep 5817827 = 8726741) B8726741
theorem B607747 : Blo 503794 607747 := bstep (se 1 (by rfl) ⟨455810, by rfl⟩ : syracuseStep 607747 = 911621) B911621
theorem B640867 : Blo 503794 640867 := bstep (se 1 (by rfl) ⟨480650, by rfl⟩ : syracuseStep 640867 = 961301) B961301
theorem B20760461 : Blo 503794 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B2738083 : Blo 503794 2738083 := bstep (se 1 (by rfl) ⟨2053562, by rfl⟩ : syracuseStep 2738083 = 4107125) B4107125
theorem B640963 : Blo 503794 640963 := bstep (se 1 (by rfl) ⟨480722, by rfl⟩ : syracuseStep 640963 = 961445) B961445
theorem B3295331 : Blo 503794 3295331 := bstep (se 1 (by rfl) ⟨2471498, by rfl⟩ : syracuseStep 3295331 = 4942997) B4942997
theorem B1919153 : Blo 503794 1919153 := bstep (se 2 (by rfl) ⟨719682, by rfl⟩ : syracuseStep 1919153 = 1439365) B1439365
theorem B1624387 : Blo 503794 1624387 := bstep (se 1 (by rfl) ⟨1218290, by rfl⟩ : syracuseStep 1624387 = 2436581) B2436581
theorem B641459 : Blo 503794 641459 := bstep (se 1 (by rfl) ⟨481094, by rfl⟩ : syracuseStep 641459 = 962189) B962189
theorem B1362467 : Blo 503794 1362467 := bstep (se 1 (by rfl) ⟨1021850, by rfl⟩ : syracuseStep 1362467 = 2043701) B2043701
theorem B1624657 : Blo 503794 1624657 := bstep (se 2 (by rfl) ⟨609246, by rfl⟩ : syracuseStep 1624657 = 1218493) B1218493
theorem B2869937 : Blo 503794 2869937 := bstep (se 2 (by rfl) ⟨1076226, by rfl⟩ : syracuseStep 2869937 = 2152453) B2152453
theorem B2345699 : Blo 503794 2345699 := bstep (se 1 (by rfl) ⟨1759274, by rfl⟩ : syracuseStep 2345699 = 3518549) B3518549
theorem B1919821 : Blo 503794 1919821 := bstep (se 3 (by rfl) ⟨359966, by rfl⟩ : syracuseStep 1919821 = 719933) B719933
theorem B1133585 : Blo 503794 1133585 := bstep (se 2 (by rfl) ⟨425094, by rfl⟩ : syracuseStep 1133585 = 850189) B850189
theorem B1133603 : Blo 503794 1133603 := bstep (se 1 (by rfl) ⟨850202, by rfl⟩ : syracuseStep 1133603 = 1700405) B1700405
theorem B642163 : Blo 503794 642163 := bstep (se 1 (by rfl) ⟨481622, by rfl⟩ : syracuseStep 642163 = 963245) B963245
theorem B1363139 : Blo 503794 1363139 := bstep (se 1 (by rfl) ⟨1022354, by rfl⟩ : syracuseStep 1363139 = 2044709) B2044709
theorem B642259 : Blo 503794 642259 := bstep (se 1 (by rfl) ⟨481694, by rfl⟩ : syracuseStep 642259 = 963389) B963389
theorem B609539 : Blo 503794 609539 := bstep (se 1 (by rfl) ⟨457154, by rfl⟩ : syracuseStep 609539 = 914309) B914309
theorem B1133873 : Blo 503794 1133873 := bstep (se 2 (by rfl) ⟨425202, by rfl⟩ : syracuseStep 1133873 = 850405) B850405
theorem B1133891 : Blo 503794 1133891 := bstep (se 1 (by rfl) ⟨850418, by rfl⟩ : syracuseStep 1133891 = 1700837) B1700837
theorem B3231089 : Blo 503794 3231089 := bstep (se 2 (by rfl) ⟨1211658, by rfl⟩ : syracuseStep 3231089 = 2423317) B2423317
theorem B3165581 : Blo 503794 3165581 := bstep (se 3 (by rfl) ⟨593546, by rfl⟩ : syracuseStep 3165581 = 1187093) B1187093
theorem B577091 : Blo 503794 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B1134161 : Blo 503794 1134161 := bstep (se 2 (by rfl) ⟨425310, by rfl⟩ : syracuseStep 1134161 = 850621) B850621
theorem B740945 : Blo 503794 740945 := bstep (se 2 (by rfl) ⟨277854, by rfl⟩ : syracuseStep 740945 = 555709) B555709
theorem B1134179 : Blo 503794 1134179 := bstep (se 1 (by rfl) ⟨850634, by rfl⟩ : syracuseStep 1134179 = 1701269) B1701269
theorem B1920611 : Blo 503794 1920611 := bstep (se 1 (by rfl) ⟨1440458, by rfl⟩ : syracuseStep 1920611 = 2880917) B2880917
theorem B2084707 : Blo 503794 2084707 := bstep (se 1 (by rfl) ⟨1563530, by rfl⟩ : syracuseStep 2084707 = 3127061) B3127061
theorem B1134449 : Blo 503794 1134449 := bstep (se 2 (by rfl) ⟨425418, by rfl⟩ : syracuseStep 1134449 = 850837) B850837
theorem B1134467 : Blo 503794 1134467 := bstep (se 1 (by rfl) ⟨850850, by rfl⟩ : syracuseStep 1134467 = 1701701) B1701701
theorem B2740229 : Blo 503794 2740229 := bstep (se 4 (by rfl) ⟨256896, by rfl⟩ : syracuseStep 2740229 = 513793) B513793
theorem B2871395 : Blo 503794 2871395 := bstep (se 1 (by rfl) ⟨2153546, by rfl⟩ : syracuseStep 2871395 = 4307093) B4307093
theorem B1134737 : Blo 503794 1134737 := bstep (se 2 (by rfl) ⟨425526, by rfl⟩ : syracuseStep 1134737 = 851053) B851053
theorem B1626257 : Blo 503794 1626257 := bstep (se 2 (by rfl) ⟨609846, by rfl⟩ : syracuseStep 1626257 = 1219693) B1219693
theorem B1134755 : Blo 503794 1134755 := bstep (se 1 (by rfl) ⟨851066, by rfl⟩ : syracuseStep 1134755 = 1702133) B1702133
theorem B1921265 : Blo 503794 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B3461453 : Blo 503794 3461453 := bstep (se 3 (by rfl) ⟨649022, by rfl⟩ : syracuseStep 3461453 = 1298045) B1298045
theorem B1135025 : Blo 503794 1135025 := bstep (se 2 (by rfl) ⟨425634, by rfl⟩ : syracuseStep 1135025 = 851269) B851269
theorem B1135043 : Blo 503794 1135043 := bstep (se 1 (by rfl) ⟨851282, by rfl⟩ : syracuseStep 1135043 = 1702565) B1702565
theorem B1626605 : Blo 503794 1626605 := bstep (se 3 (by rfl) ⟨304988, by rfl⟩ : syracuseStep 1626605 = 609977) B609977
theorem B807491 : Blo 503794 807491 := bstep (se 1 (by rfl) ⟨605618, by rfl⟩ : syracuseStep 807491 = 1211237) B1211237
theorem B545443 : Blo 503794 545443 := bstep (se 1 (by rfl) ⟨409082, by rfl⟩ : syracuseStep 545443 = 818165) B818165
theorem B1135313 : Blo 503794 1135313 := bstep (se 2 (by rfl) ⟨425742, by rfl⟩ : syracuseStep 1135313 = 851485) B851485
theorem B1135331 : Blo 503794 1135331 := bstep (se 1 (by rfl) ⟨851498, by rfl⟩ : syracuseStep 1135331 = 1702997) B1702997
theorem B807875 : Blo 503794 807875 := bstep (se 1 (by rfl) ⟨605906, by rfl⟩ : syracuseStep 807875 = 1211813) B1211813
theorem B1135601 : Blo 503794 1135601 := bstep (se 2 (by rfl) ⟨425850, by rfl⟩ : syracuseStep 1135601 = 851701) B851701
theorem B1135619 : Blo 503794 1135619 := bstep (se 1 (by rfl) ⟨851714, by rfl⟩ : syracuseStep 1135619 = 1703429) B1703429
theorem B3232781 : Blo 503794 3232781 := bstep (se 3 (by rfl) ⟨606146, by rfl⟩ : syracuseStep 3232781 = 1212293) B1212293
theorem B808003 : Blo 503794 808003 := bstep (se 1 (by rfl) ⟨606002, by rfl⟩ : syracuseStep 808003 = 1212005) B1212005
theorem B1758275 : Blo 503794 1758275 := bstep (se 1 (by rfl) ⟨1318706, by rfl⟩ : syracuseStep 1758275 = 2637413) B2637413
theorem B1299665 : Blo 503794 1299665 := bstep (se 2 (by rfl) ⟨487374, by rfl⟩ : syracuseStep 1299665 = 974749) B974749
theorem B1135889 : Blo 503794 1135889 := bstep (se 2 (by rfl) ⟨425958, by rfl⟩ : syracuseStep 1135889 = 851917) B851917
theorem B1135907 : Blo 503794 1135907 := bstep (se 1 (by rfl) ⟨851930, by rfl⟩ : syracuseStep 1135907 = 1703861) B1703861
theorem B1824049 : Blo 503794 1824049 := bstep (se 2 (by rfl) ⟨684018, by rfl⟩ : syracuseStep 1824049 = 1368037) B1368037
theorem B873811 : Blo 503794 873811 := bstep (se 1 (by rfl) ⟨655358, by rfl⟩ : syracuseStep 873811 = 1310717) B1310717
theorem B1136177 : Blo 503794 1136177 := bstep (se 2 (by rfl) ⟨426066, by rfl⟩ : syracuseStep 1136177 = 852133) B852133
theorem B1136195 : Blo 503794 1136195 := bstep (se 1 (by rfl) ⟨852146, by rfl⟩ : syracuseStep 1136195 = 1704293) B1704293
theorem B1922723 : Blo 503794 1922723 := bstep (se 1 (by rfl) ⟨1442042, by rfl⟩ : syracuseStep 1922723 = 2884085) B2884085
theorem B1922737 : Blo 503794 1922737 := bstep (se 2 (by rfl) ⟨721026, by rfl⟩ : syracuseStep 1922737 = 1442053) B1442053
theorem B14636771 : Blo 503794 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B808721 : Blo 503794 808721 := bstep (se 2 (by rfl) ⟨303270, by rfl⟩ : syracuseStep 808721 = 606541) B606541
theorem B1136465 : Blo 503794 1136465 := bstep (se 2 (by rfl) ⟨426174, by rfl⟩ : syracuseStep 1136465 = 852349) B852349
theorem B1136483 : Blo 503794 1136483 := bstep (se 1 (by rfl) ⟨852362, by rfl⟩ : syracuseStep 1136483 = 1704725) B1704725
theorem B513955 : Blo 503794 513955 := bstep (se 1 (by rfl) ⟨385466, by rfl⟩ : syracuseStep 513955 = 770933) B770933
theorem B1464227 : Blo 503794 1464227 := bstep (se 1 (by rfl) ⟨1098170, by rfl⟩ : syracuseStep 1464227 = 2196341) B2196341
theorem B808913 : Blo 503794 808913 := bstep (se 2 (by rfl) ⟨303342, by rfl⟩ : syracuseStep 808913 = 606685) B606685
theorem B1136753 : Blo 503794 1136753 := bstep (se 2 (by rfl) ⟨426282, by rfl⟩ : syracuseStep 1136753 = 852565) B852565
theorem B1136771 : Blo 503794 1136771 := bstep (se 1 (by rfl) ⟨852578, by rfl⟩ : syracuseStep 1136771 = 1705157) B1705157
theorem B1366253 : Blo 503794 1366253 := bstep (se 3 (by rfl) ⟨256172, by rfl⟩ : syracuseStep 1366253 = 512345) B512345
theorem B1300835 : Blo 503794 1300835 := bstep (se 1 (by rfl) ⟨975626, by rfl⟩ : syracuseStep 1300835 = 1951253) B1951253
theorem B1137041 : Blo 503794 1137041 := bstep (se 2 (by rfl) ⟨426390, by rfl⟩ : syracuseStep 1137041 = 852781) B852781
theorem B1137059 : Blo 503794 1137059 := bstep (se 1 (by rfl) ⟨852794, by rfl⟩ : syracuseStep 1137059 = 1705589) B1705589
theorem B547283 : Blo 503794 547283 := bstep (se 1 (by rfl) ⟨410462, by rfl⟩ : syracuseStep 547283 = 820925) B820925
theorem B4872773 : Blo 503794 4872773 := bstep (se 4 (by rfl) ⟨456822, by rfl⟩ : syracuseStep 4872773 = 913645) B913645
theorem B2185805 : Blo 503794 2185805 := bstep (se 3 (by rfl) ⟨409838, by rfl⟩ : syracuseStep 2185805 = 819677) B819677
theorem B1727153 : Blo 503794 1727153 := bstep (se 2 (by rfl) ⟨647682, by rfl⟩ : syracuseStep 1727153 = 1295365) B1295365
theorem B1137329 : Blo 503794 1137329 := bstep (se 2 (by rfl) ⟨426498, by rfl⟩ : syracuseStep 1137329 = 852997) B852997
theorem B1137347 : Blo 503794 1137347 := bstep (se 1 (by rfl) ⟨853010, by rfl⟩ : syracuseStep 1137347 = 1706021) B1706021
theorem B1137617 : Blo 503794 1137617 := bstep (se 2 (by rfl) ⟨426606, by rfl⟩ : syracuseStep 1137617 = 853213) B853213
theorem B1137635 : Blo 503794 1137635 := bstep (se 1 (by rfl) ⟨853226, by rfl⟩ : syracuseStep 1137635 = 1706453) B1706453
theorem B1924195 : Blo 503794 1924195 := bstep (se 1 (by rfl) ⟨1443146, by rfl⟩ : syracuseStep 1924195 = 2886293) B2886293
theorem B875713 : Blo 503794 875713 := bstep (se 2 (by rfl) ⟨328392, by rfl⟩ : syracuseStep 875713 = 656785) B656785
theorem B1137905 : Blo 503794 1137905 := bstep (se 2 (by rfl) ⟨426714, by rfl⟩ : syracuseStep 1137905 = 853429) B853429
theorem B1137923 : Blo 503794 1137923 := bstep (se 1 (by rfl) ⟨853442, by rfl⟩ : syracuseStep 1137923 = 1706885) B1706885
theorem B2874629 : Blo 503794 2874629 := bstep (se 4 (by rfl) ⟨269496, by rfl⟩ : syracuseStep 2874629 = 538993) B538993
theorem B1039697 : Blo 503794 1039697 := bstep (se 2 (by rfl) ⟨389886, by rfl⟩ : syracuseStep 1039697 = 779773) B779773
theorem B5823971 : Blo 503794 5823971 := bstep (se 1 (by rfl) ⟨4367978, by rfl⟩ : syracuseStep 5823971 = 8735957) B8735957
theorem B1138193 : Blo 503794 1138193 := bstep (se 2 (by rfl) ⟨426822, by rfl⟩ : syracuseStep 1138193 = 853645) B853645
theorem B1138211 : Blo 503794 1138211 := bstep (se 1 (by rfl) ⟨853658, by rfl⟩ : syracuseStep 1138211 = 1707317) B1707317
theorem B2743877 : Blo 503794 2743877 := bstep (se 4 (by rfl) ⟨257238, by rfl⟩ : syracuseStep 2743877 = 514477) B514477
theorem B810643 : Blo 503794 810643 := bstep (se 1 (by rfl) ⟨607982, by rfl⟩ : syracuseStep 810643 = 1215965) B1215965
theorem B2875085 : Blo 503794 2875085 := bstep (se 3 (by rfl) ⟨539078, by rfl⟩ : syracuseStep 2875085 = 1078157) B1078157
theorem B810739 : Blo 503794 810739 := bstep (se 1 (by rfl) ⟨608054, by rfl⟩ : syracuseStep 810739 = 1216109) B1216109
theorem B1138481 : Blo 503794 1138481 := bstep (se 2 (by rfl) ⟨426930, by rfl⟩ : syracuseStep 1138481 = 853861) B853861
theorem B1138499 : Blo 503794 1138499 := bstep (se 1 (by rfl) ⟨853874, by rfl⟩ : syracuseStep 1138499 = 1707749) B1707749
theorem B810899 : Blo 503794 810899 := bstep (se 1 (by rfl) ⟨608174, by rfl⟩ : syracuseStep 810899 = 1216349) B1216349
theorem B1138769 : Blo 503794 1138769 := bstep (se 2 (by rfl) ⟨427038, by rfl⟩ : syracuseStep 1138769 = 854077) B854077
theorem B1138787 : Blo 503794 1138787 := bstep (se 1 (by rfl) ⟨854090, by rfl⟩ : syracuseStep 1138787 = 1708181) B1708181
theorem B5824709 : Blo 503794 5824709 := bstep (se 4 (by rfl) ⟨546066, by rfl⟩ : syracuseStep 5824709 = 1092133) B1092133
theorem B2908493 : Blo 503794 2908493 := bstep (se 3 (by rfl) ⟨545342, by rfl⟩ : syracuseStep 2908493 = 1090685) B1090685
theorem B909667 : Blo 503794 909667 := bstep (se 1 (by rfl) ⟨682250, by rfl⟩ : syracuseStep 909667 = 1364501) B1364501
theorem B1139057 : Blo 503794 1139057 := bstep (se 2 (by rfl) ⟨427146, by rfl⟩ : syracuseStep 1139057 = 854293) B854293
theorem B1139075 : Blo 503794 1139075 := bstep (se 1 (by rfl) ⟨854306, by rfl⟩ : syracuseStep 1139075 = 1708613) B1708613
theorem B1532387 : Blo 503794 1532387 := bstep (se 1 (by rfl) ⟨1149290, by rfl⟩ : syracuseStep 1532387 = 2298581) B2298581
theorem B2155085 : Blo 503794 2155085 := bstep (se 3 (by rfl) ⟨404078, by rfl⟩ : syracuseStep 2155085 = 808157) B808157
theorem B975473 : Blo 503794 975473 := bstep (se 2 (by rfl) ⟨365802, by rfl⟩ : syracuseStep 975473 = 731605) B731605
theorem B1139345 : Blo 503794 1139345 := bstep (se 2 (by rfl) ⟨427254, by rfl⟩ : syracuseStep 1139345 = 854509) B854509
theorem B1139363 : Blo 503794 1139363 := bstep (se 1 (by rfl) ⟨854522, by rfl⟩ : syracuseStep 1139363 = 1709045) B1709045
theorem B910129 : Blo 503794 910129 := bstep (se 2 (by rfl) ⟨341298, by rfl⟩ : syracuseStep 910129 = 682597) B682597
theorem B811873 : Blo 503794 811873 := bstep (se 2 (by rfl) ⟨304452, by rfl⟩ : syracuseStep 811873 = 608905) B608905
theorem B1139633 : Blo 503794 1139633 := bstep (se 2 (by rfl) ⟨427362, by rfl⟩ : syracuseStep 1139633 = 854725) B854725
theorem B1139651 : Blo 503794 1139651 := bstep (se 1 (by rfl) ⟨854738, by rfl⟩ : syracuseStep 1139651 = 1709477) B1709477
theorem B1139921 : Blo 503794 1139921 := bstep (se 2 (by rfl) ⟨427470, by rfl⟩ : syracuseStep 1139921 = 854941) B854941
theorem B1139939 : Blo 503794 1139939 := bstep (se 1 (by rfl) ⟨854954, by rfl⟩ : syracuseStep 1139939 = 1709909) B1709909
theorem B1926413 : Blo 503794 1926413 := bstep (se 3 (by rfl) ⟨361202, by rfl⟩ : syracuseStep 1926413 = 722405) B722405
theorem B910705 : Blo 503794 910705 := bstep (se 2 (by rfl) ⟨341514, by rfl⟩ : syracuseStep 910705 = 683029) B683029
theorem B1435117 : Blo 503794 1435117 := bstep (se 3 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 1435117 = 538169) B538169
theorem B1140209 : Blo 503794 1140209 := bstep (se 2 (by rfl) ⟨427578, by rfl⟩ : syracuseStep 1140209 = 855157) B855157
theorem B1140227 : Blo 503794 1140227 := bstep (se 1 (by rfl) ⟨855170, by rfl⟩ : syracuseStep 1140227 = 1710341) B1710341
theorem B681601 : Blo 503794 681601 := bstep (se 2 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 681601 = 511201) B511201
theorem B910993 : Blo 503794 910993 := bstep (se 2 (by rfl) ⟨341622, by rfl⟩ : syracuseStep 910993 = 683245) B683245
theorem B1140497 : Blo 503794 1140497 := bstep (se 2 (by rfl) ⟨427686, by rfl⟩ : syracuseStep 1140497 = 855373) B855373
theorem B1140515 : Blo 503794 1140515 := bstep (se 1 (by rfl) ⟨855386, by rfl⟩ : syracuseStep 1140515 = 1710773) B1710773
theorem B1140785 : Blo 503794 1140785 := bstep (se 2 (by rfl) ⟨427794, by rfl⟩ : syracuseStep 1140785 = 855589) B855589
theorem B1140803 : Blo 503794 1140803 := bstep (se 1 (by rfl) ⟨855602, by rfl⟩ : syracuseStep 1140803 = 1711205) B1711205
theorem B1042723 : Blo 503794 1042723 := bstep (se 1 (by rfl) ⟨782042, by rfl⟩ : syracuseStep 1042723 = 1564085) B1564085
theorem B1141073 : Blo 503794 1141073 := bstep (se 2 (by rfl) ⟨427902, by rfl⟩ : syracuseStep 1141073 = 855805) B855805
theorem B1141091 : Blo 503794 1141091 := bstep (se 1 (by rfl) ⟨855818, by rfl⟩ : syracuseStep 1141091 = 1711637) B1711637
theorem B2878001 : Blo 503794 2878001 := bstep (se 2 (by rfl) ⟨1079250, by rfl⟩ : syracuseStep 2878001 = 2158501) B2158501
theorem B8612405 : Blo 503794 8612405 := bstep (se 5 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 8612405 = 807413) B807413
theorem B1141361 : Blo 503794 1141361 := bstep (se 2 (by rfl) ⟨428010, by rfl⟩ : syracuseStep 1141361 = 856021) B856021
theorem B1141379 : Blo 503794 1141379 := bstep (se 1 (by rfl) ⟨856034, by rfl⟩ : syracuseStep 1141379 = 1712069) B1712069
theorem B682705 : Blo 503794 682705 := bstep (se 2 (by rfl) ⟨256014, by rfl⟩ : syracuseStep 682705 = 512029) B512029
theorem B1141649 : Blo 503794 1141649 := bstep (se 2 (by rfl) ⟨428118, by rfl⟩ : syracuseStep 1141649 = 856237) B856237
theorem B1141667 : Blo 503794 1141667 := bstep (se 1 (by rfl) ⟨856250, by rfl⟩ : syracuseStep 1141667 = 1712501) B1712501
theorem B3828707 : Blo 503794 3828707 := bstep (se 1 (by rfl) ⟨2871530, by rfl⟩ : syracuseStep 3828707 = 5743061) B5743061
theorem B1436849 : Blo 503794 1436849 := bstep (se 2 (by rfl) ⟨538818, by rfl⟩ : syracuseStep 1436849 = 1077637) B1077637
theorem B1141937 : Blo 503794 1141937 := bstep (se 2 (by rfl) ⟨428226, by rfl⟩ : syracuseStep 1141937 = 856453) B856453
theorem B1141955 : Blo 503794 1141955 := bstep (se 1 (by rfl) ⟨856466, by rfl⟩ : syracuseStep 1141955 = 1712933) B1712933
theorem B1076483 : Blo 503794 1076483 := bstep (se 1 (by rfl) ⟨807362, by rfl⟩ : syracuseStep 1076483 = 1614725) B1614725
theorem B683299 : Blo 503794 683299 := bstep (se 1 (by rfl) ⟨512474, by rfl⟩ : syracuseStep 683299 = 1024949) B1024949
theorem B1437041 : Blo 503794 1437041 := bstep (se 2 (by rfl) ⟨538890, by rfl⟩ : syracuseStep 1437041 = 1077781) B1077781
theorem B1535441 : Blo 503794 1535441 := bstep (se 2 (by rfl) ⟨575790, by rfl⟩ : syracuseStep 1535441 = 1151581) B1151581
theorem B1142225 : Blo 503794 1142225 := bstep (se 2 (by rfl) ⟨428334, by rfl⟩ : syracuseStep 1142225 = 856669) B856669
theorem B1142243 : Blo 503794 1142243 := bstep (se 1 (by rfl) ⟨856682, by rfl⟩ : syracuseStep 1142243 = 1713365) B1713365
theorem B3468835 : Blo 503794 3468835 := bstep (se 1 (by rfl) ⟨2601626, by rfl⟩ : syracuseStep 3468835 = 5203253) B5203253
theorem B683635 : Blo 503794 683635 := bstep (se 1 (by rfl) ⟨512726, by rfl⟩ : syracuseStep 683635 = 1025453) B1025453
theorem B4320965 : Blo 503794 4320965 := bstep (se 4 (by rfl) ⟨405090, by rfl⟩ : syracuseStep 4320965 = 810181) B810181
theorem B1142513 : Blo 503794 1142513 := bstep (se 2 (by rfl) ⟨428442, by rfl⟩ : syracuseStep 1142513 = 856885) B856885
theorem B1142531 : Blo 503794 1142531 := bstep (se 1 (by rfl) ⟨856898, by rfl⟩ : syracuseStep 1142531 = 1713797) B1713797
theorem B683905 : Blo 503794 683905 := bstep (se 2 (by rfl) ⟨256464, by rfl⟩ : syracuseStep 683905 = 512929) B512929
theorem B2879459 : Blo 503794 2879459 := bstep (se 1 (by rfl) ⟨2159594, by rfl⟩ : syracuseStep 2879459 = 4319189) B4319189
theorem B2551985 : Blo 503794 2551985 := bstep (se 2 (by rfl) ⟨956994, by rfl⟩ : syracuseStep 2551985 = 1913989) B1913989
theorem B1077457 : Blo 503794 1077457 := bstep (se 2 (by rfl) ⟨404046, by rfl⟩ : syracuseStep 1077457 = 808093) B808093
theorem B2912561 : Blo 503794 2912561 := bstep (se 2 (by rfl) ⟨1092210, by rfl⟩ : syracuseStep 2912561 = 2184421) B2184421
theorem B1438033 : Blo 503794 1438033 := bstep (se 2 (by rfl) ⟨539262, by rfl⟩ : syracuseStep 1438033 = 1078525) B1078525
theorem B1077713 : Blo 503794 1077713 := bstep (se 2 (by rfl) ⟨404142, by rfl⟩ : syracuseStep 1077713 = 808285) B808285
theorem B717331 : Blo 503794 717331 := bstep (se 1 (by rfl) ⟨537998, by rfl⟩ : syracuseStep 717331 = 1075997) B1075997
theorem B3469873 : Blo 503794 3469873 := bstep (se 2 (by rfl) ⟨1301202, by rfl⟩ : syracuseStep 3469873 = 2602405) B2602405
theorem B1438307 : Blo 503794 1438307 := bstep (se 1 (by rfl) ⟨1078730, by rfl⟩ : syracuseStep 1438307 = 2157461) B2157461
theorem B717427 : Blo 503794 717427 := bstep (se 1 (by rfl) ⟨538070, by rfl⟩ : syracuseStep 717427 = 1076141) B1076141
theorem B1700621 : Blo 503794 1700621 := bstep (se 3 (by rfl) ⟨318866, by rfl⟩ : syracuseStep 1700621 = 637733) B637733
theorem B1438499 : Blo 503794 1438499 := bstep (se 1 (by rfl) ⟨1078874, by rfl⟩ : syracuseStep 1438499 = 2157749) B2157749
theorem B1700675 : Blo 503794 1700675 := bstep (se 1 (by rfl) ⟨1275506, by rfl⟩ : syracuseStep 1700675 = 2551013) B2551013
theorem B2159459 : Blo 503794 2159459 := bstep (se 1 (by rfl) ⟨1619594, by rfl⟩ : syracuseStep 2159459 = 3239189) B3239189
theorem B2880461 : Blo 503794 2880461 := bstep (se 3 (by rfl) ⟨540086, by rfl⟩ : syracuseStep 2880461 = 1080173) B1080173
theorem B1700945 : Blo 503794 1700945 := bstep (se 2 (by rfl) ⟨637854, by rfl⟩ : syracuseStep 1700945 = 1275709) B1275709
theorem B717923 : Blo 503794 717923 := bstep (se 1 (by rfl) ⟨538442, by rfl⟩ : syracuseStep 717923 = 1076885) B1076885
theorem B1734061 : Blo 503794 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B914915 : Blo 503794 914915 := bstep (se 1 (by rfl) ⟨686186, by rfl⟩ : syracuseStep 914915 = 1372373) B1372373
theorem B6911501 : Blo 503794 6911501 := bstep (se 3 (by rfl) ⟨1295906, by rfl⟩ : syracuseStep 6911501 = 2591813) B2591813
theorem B1439309 : Blo 503794 1439309 := bstep (se 3 (by rfl) ⟨269870, by rfl⟩ : syracuseStep 1439309 = 539741) B539741
theorem B2553443 : Blo 503794 2553443 := bstep (se 1 (by rfl) ⟨1915082, by rfl⟩ : syracuseStep 2553443 = 3830165) B3830165
theorem B1701485 : Blo 503794 1701485 := bstep (se 3 (by rfl) ⟨319028, by rfl⟩ : syracuseStep 1701485 = 638057) B638057
theorem B1701539 : Blo 503794 1701539 := bstep (se 1 (by rfl) ⟨1276154, by rfl⟩ : syracuseStep 1701539 = 2552309) B2552309
theorem B718561 : Blo 503794 718561 := bstep (se 2 (by rfl) ⟨269460, by rfl⟩ : syracuseStep 718561 = 538921) B538921
theorem B1079011 : Blo 503794 1079011 := bstep (se 1 (by rfl) ⟨809258, by rfl⟩ : syracuseStep 1079011 = 1618517) B1618517
theorem B1439491 : Blo 503794 1439491 := bstep (se 1 (by rfl) ⟨1079618, by rfl⟩ : syracuseStep 1439491 = 2159237) B2159237
theorem B1701809 : Blo 503794 1701809 := bstep (se 2 (by rfl) ⟨638178, by rfl⟩ : syracuseStep 1701809 = 1276357) B1276357
theorem B718897 : Blo 503794 718897 := bstep (se 2 (by rfl) ⟨269586, by rfl⟩ : syracuseStep 718897 = 539173) B539173
theorem B1079345 : Blo 503794 1079345 := bstep (se 2 (by rfl) ⟨404754, by rfl⟩ : syracuseStep 1079345 = 809509) B809509
theorem B1439981 : Blo 503794 1439981 := bstep (se 3 (by rfl) ⟨269996, by rfl⟩ : syracuseStep 1439981 = 539993) B539993
theorem B1276145 : Blo 503794 1276145 := bstep (se 2 (by rfl) ⟨478554, by rfl⟩ : syracuseStep 1276145 = 957109) B957109
theorem B1276195 : Blo 503794 1276195 := bstep (se 1 (by rfl) ⟨957146, by rfl⟩ : syracuseStep 1276195 = 1914293) B1914293
theorem B850243 : Blo 503794 850243 := bstep (se 1 (by rfl) ⟨637682, by rfl⟩ : syracuseStep 850243 = 1275365) B1275365
theorem B2554253 : Blo 503794 2554253 := bstep (se 3 (by rfl) ⟨478922, by rfl⟩ : syracuseStep 2554253 = 957845) B957845
theorem B1276337 : Blo 503794 1276337 := bstep (se 2 (by rfl) ⟨478626, by rfl⟩ : syracuseStep 1276337 = 957253) B957253
theorem B1702349 : Blo 503794 1702349 := bstep (se 3 (by rfl) ⟨319190, by rfl⟩ : syracuseStep 1702349 = 638381) B638381
theorem B850385 : Blo 503794 850385 := bstep (se 2 (by rfl) ⟨318894, by rfl⟩ : syracuseStep 850385 = 637789) B637789
theorem B1702403 : Blo 503794 1702403 := bstep (se 1 (by rfl) ⟨1276802, by rfl⟩ : syracuseStep 1702403 = 2553605) B2553605
theorem B2161201 : Blo 503794 2161201 := bstep (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) B1620901
theorem B850513 : Blo 503794 850513 := bstep (se 2 (by rfl) ⟨318942, by rfl⟩ : syracuseStep 850513 = 637885) B637885
theorem B850547 : Blo 503794 850547 := bstep (se 1 (by rfl) ⟨637910, by rfl⟩ : syracuseStep 850547 = 1275821) B1275821
theorem B719489 : Blo 503794 719489 := bstep (se 2 (by rfl) ⟨269808, by rfl⟩ : syracuseStep 719489 = 539617) B539617
theorem B850675 : Blo 503794 850675 := bstep (se 1 (by rfl) ⟨638006, by rfl⟩ : syracuseStep 850675 = 1276013) B1276013
theorem B1702673 : Blo 503794 1702673 := bstep (se 2 (by rfl) ⟨638502, by rfl⟩ : syracuseStep 1702673 = 1277005) B1277005
theorem B850817 : Blo 503794 850817 := bstep (se 2 (by rfl) ⟨319056, by rfl⟩ : syracuseStep 850817 = 638113) B638113
theorem B3505123 : Blo 503794 3505123 := bstep (se 1 (by rfl) ⟨2628842, by rfl⟩ : syracuseStep 3505123 = 5257685) B5257685
theorem B1539053 : Blo 503794 1539053 := bstep (se 3 (by rfl) ⟨288572, by rfl⟩ : syracuseStep 1539053 = 577145) B577145
theorem B850945 : Blo 503794 850945 := bstep (se 2 (by rfl) ⟨319104, by rfl⟩ : syracuseStep 850945 = 638209) B638209
theorem B850979 : Blo 503794 850979 := bstep (se 1 (by rfl) ⟨638234, by rfl⟩ : syracuseStep 850979 = 1276469) B1276469
theorem B720019 : Blo 503794 720019 := bstep (se 1 (by rfl) ⟨540014, by rfl⟩ : syracuseStep 720019 = 1080029) B1080029
theorem B851107 : Blo 503794 851107 := bstep (se 1 (by rfl) ⟨638330, by rfl⟩ : syracuseStep 851107 = 1276661) B1276661
theorem B3243185 : Blo 503794 3243185 := bstep (se 2 (by rfl) ⟨1216194, by rfl⟩ : syracuseStep 3243185 = 2432389) B2432389
theorem B1080515 : Blo 503794 1080515 := bstep (se 1 (by rfl) ⟨810386, by rfl⟩ : syracuseStep 1080515 = 1620773) B1620773
theorem B10386629 : Blo 503794 10386629 := bstep (se 4 (by rfl) ⟨973746, by rfl⟩ : syracuseStep 10386629 = 1947493) B1947493
theorem B55934165 : Blo 503794 55934165 := bstep (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) B1310957
theorem B6552845 : Blo 503794 6552845 := bstep (se 3 (by rfl) ⟨1228658, by rfl⟩ : syracuseStep 6552845 = 2457317) B2457317
theorem B1703213 : Blo 503794 1703213 := bstep (se 3 (by rfl) ⟨319352, by rfl⟩ : syracuseStep 1703213 = 638705) B638705
theorem B851249 : Blo 503794 851249 := bstep (se 2 (by rfl) ⟨319218, by rfl⟩ : syracuseStep 851249 = 638437) B638437
theorem B1703267 : Blo 503794 1703267 := bstep (se 1 (by rfl) ⟨1277450, by rfl⟩ : syracuseStep 1703267 = 2554901) B2554901
theorem B1441165 : Blo 503794 1441165 := bstep (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) B540437
theorem B3079565 : Blo 503794 3079565 := bstep (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) B1154837
theorem B1277329 : Blo 503794 1277329 := bstep (se 2 (by rfl) ⟨478998, by rfl⟩ : syracuseStep 1277329 = 957997) B957997
theorem B851377 : Blo 503794 851377 := bstep (se 2 (by rfl) ⟨319266, by rfl⟩ : syracuseStep 851377 = 638533) B638533
theorem B851411 : Blo 503794 851411 := bstep (se 1 (by rfl) ⟨638558, by rfl⟩ : syracuseStep 851411 = 1277117) B1277117
theorem B720355 : Blo 503794 720355 := bstep (se 1 (by rfl) ⟨540266, by rfl⟩ : syracuseStep 720355 = 1080533) B1080533
theorem B851539 : Blo 503794 851539 := bstep (se 1 (by rfl) ⟨638654, by rfl⟩ : syracuseStep 851539 = 1277309) B1277309
theorem B1703537 : Blo 503794 1703537 := bstep (se 2 (by rfl) ⟨638826, by rfl⟩ : syracuseStep 1703537 = 1277653) B1277653
theorem B1277603 : Blo 503794 1277603 := bstep (se 1 (by rfl) ⟨958202, by rfl⟩ : syracuseStep 1277603 = 1916405) B1916405
theorem B851681 : Blo 503794 851681 := bstep (se 2 (by rfl) ⟨319380, by rfl⟩ : syracuseStep 851681 = 638761) B638761
theorem B2883377 : Blo 503794 2883377 := bstep (se 2 (by rfl) ⟨1081266, by rfl⟩ : syracuseStep 2883377 = 2162533) B2162533
theorem B851809 : Blo 503794 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B1277795 : Blo 503794 1277795 := bstep (se 1 (by rfl) ⟨958346, by rfl⟩ : syracuseStep 1277795 = 1916693) B1916693
theorem B851843 : Blo 503794 851843 := bstep (se 1 (by rfl) ⟨638882, by rfl⟩ : syracuseStep 851843 = 1277765) B1277765
theorem B34930763 : Blo 503794 34930763 := bstep (se 1 (by rfl) ⟨26198072, by rfl⟩ : syracuseStep 34930763 = 52396145) B52396145
theorem B2556035 : Blo 503794 2556035 := bstep (se 1 (by rfl) ⟨1917026, by rfl⟩ : syracuseStep 2556035 = 3834053) B3834053
theorem B3244211 : Blo 503794 3244211 := bstep (se 1 (by rfl) ⟨2433158, by rfl⟩ : syracuseStep 3244211 = 4866317) B4866317
theorem B2425049 : Blo 503794 2425049 := bstep (se 2 (by rfl) ⟨909393, by rfl⟩ : syracuseStep 2425049 = 1818787) B1818787
theorem B1442099 : Blo 503794 1442099 := bstep (se 1 (by rfl) ⟨1081574, by rfl⟩ : syracuseStep 1442099 = 2163149) B2163149
theorem B2490689 : Blo 503794 2490689 := bstep (se 2 (by rfl) ⟨934008, by rfl⟩ : syracuseStep 2490689 = 1868017) B1868017
theorem B1212889 : Blo 503794 1212889 := bstep (se 2 (by rfl) ⟨454833, by rfl⟩ : syracuseStep 1212889 = 909667) B909667
theorem B852491 : Blo 503794 852491 := bstep (se 1 (by rfl) ⟨639368, by rfl⟩ : syracuseStep 852491 = 1278737) B1278737
theorem B852619 : Blo 503794 852619 := bstep (se 1 (by rfl) ⟨639464, by rfl⟩ : syracuseStep 852619 = 1278929) B1278929
theorem B852761 : Blo 503794 852761 := bstep (se 2 (by rfl) ⟨319785, by rfl⟩ : syracuseStep 852761 = 639571) B639571
theorem B1213235 : Blo 503794 1213235 := bstep (se 1 (by rfl) ⟨909926, by rfl⟩ : syracuseStep 1213235 = 1819853) B1819853
theorem B1704779 : Blo 503794 1704779 := bstep (se 1 (by rfl) ⟨1278584, by rfl⟩ : syracuseStep 1704779 = 2557169) B2557169
theorem B852889 : Blo 503794 852889 := bstep (se 2 (by rfl) ⟨319833, by rfl⟩ : syracuseStep 852889 = 639667) B639667
theorem B1278899 : Blo 503794 1278899 := bstep (se 1 (by rfl) ⟨959174, by rfl⟩ : syracuseStep 1278899 = 1918349) B1918349
theorem B2163763 : Blo 503794 2163763 := bstep (se 1 (by rfl) ⟨1622822, by rfl⟩ : syracuseStep 2163763 = 3245645) B3245645
theorem B1213505 : Blo 503794 1213505 := bstep (se 2 (by rfl) ⟨455064, by rfl⟩ : syracuseStep 1213505 = 910129) B910129
theorem B1705049 : Blo 503794 1705049 := bstep (se 2 (by rfl) ⟨639393, by rfl⟩ : syracuseStep 1705049 = 1278787) B1278787
theorem B1082497 : Blo 503794 1082497 := bstep (se 2 (by rfl) ⟨405936, by rfl⟩ : syracuseStep 1082497 = 811873) B811873
theorem B2196887 : Blo 503794 2196887 := bstep (se 1 (by rfl) ⟨1647665, by rfl⟩ : syracuseStep 2196887 = 3295331) B3295331
theorem B1279435 : Blo 503794 1279435 := bstep (se 1 (by rfl) ⟨959576, by rfl⟩ : syracuseStep 1279435 = 1919153) B1919153
theorem B853463 : Blo 503794 853463 := bstep (se 1 (by rfl) ⟨640097, by rfl⟩ : syracuseStep 853463 = 1280195) B1280195
theorem B853591 : Blo 503794 853591 := bstep (se 1 (by rfl) ⟨640193, by rfl⟩ : syracuseStep 853591 = 1280387) B1280387
theorem B1279577 : Blo 503794 1279577 := bstep (se 2 (by rfl) ⟨479841, by rfl⟩ : syracuseStep 1279577 = 959683) B959683
theorem B1705751 : Blo 503794 1705751 := bstep (se 1 (by rfl) ⟨1279313, by rfl⟩ : syracuseStep 1705751 = 2558627) B2558627
theorem B1214273 : Blo 503794 1214273 := bstep (se 2 (by rfl) ⟨455352, by rfl⟩ : syracuseStep 1214273 = 910705) B910705
theorem B2426699 : Blo 503794 2426699 := bstep (se 1 (by rfl) ⟨1820024, by rfl⟩ : syracuseStep 2426699 = 3640049) B3640049
theorem B15599537 : Blo 503794 15599537 := bstep (se 2 (by rfl) ⟨5849826, by rfl⟩ : syracuseStep 15599537 = 11699653) B11699653
theorem B2197441 : Blo 503794 2197441 := bstep (se 2 (by rfl) ⟨824040, by rfl⟩ : syracuseStep 2197441 = 1648081) B1648081
theorem B755723 : Blo 503794 755723 := bstep (se 1 (by rfl) ⟨566792, by rfl⟩ : syracuseStep 755723 = 1133585) B1133585
theorem B755735 : Blo 503794 755735 := bstep (se 1 (by rfl) ⟨566801, by rfl⟩ : syracuseStep 755735 = 1133603) B1133603
theorem B755801 : Blo 503794 755801 := bstep (se 2 (by rfl) ⟨283425, by rfl⟩ : syracuseStep 755801 = 566851) B566851
theorem B3835997 : Blo 503794 3835997 := bstep (se 3 (by rfl) ⟨719249, by rfl⟩ : syracuseStep 3835997 = 1438499) B1438499
theorem B1214657 : Blo 503794 1214657 := bstep (se 2 (by rfl) ⟨455496, by rfl⟩ : syracuseStep 1214657 = 910993) B910993
theorem B755915 : Blo 503794 755915 := bstep (se 1 (by rfl) ⟨566936, by rfl⟩ : syracuseStep 755915 = 1133873) B1133873
theorem B854219 : Blo 503794 854219 := bstep (se 1 (by rfl) ⟨640664, by rfl⟩ : syracuseStep 854219 = 1281329) B1281329
theorem B755927 : Blo 503794 755927 := bstep (se 1 (by rfl) ⟨566945, by rfl⟩ : syracuseStep 755927 = 1133891) B1133891
theorem B755993 : Blo 503794 755993 := bstep (se 2 (by rfl) ⟨283497, by rfl⟩ : syracuseStep 755993 = 566995) B566995
theorem B1706291 : Blo 503794 1706291 := bstep (se 1 (by rfl) ⟨1279718, by rfl⟩ : syracuseStep 1706291 = 2559437) B2559437
theorem B854347 : Blo 503794 854347 := bstep (se 1 (by rfl) ⟨640760, by rfl⟩ : syracuseStep 854347 = 1281521) B1281521
theorem B6490469 : Blo 503794 6490469 := bstep (se 4 (by rfl) ⟨608481, by rfl⟩ : syracuseStep 6490469 = 1216963) B1216963
theorem B756107 : Blo 503794 756107 := bstep (se 1 (by rfl) ⟨567080, by rfl⟩ : syracuseStep 756107 = 1134161) B1134161
theorem B756119 : Blo 503794 756119 := bstep (se 1 (by rfl) ⟨567089, by rfl⟩ : syracuseStep 756119 = 1134179) B1134179
theorem B1280407 : Blo 503794 1280407 := bstep (se 1 (by rfl) ⟨960305, by rfl⟩ : syracuseStep 1280407 = 1920611) B1920611
theorem B756185 : Blo 503794 756185 := bstep (se 2 (by rfl) ⟨283569, by rfl⟩ : syracuseStep 756185 = 567139) B567139
theorem B854489 : Blo 503794 854489 := bstep (se 2 (by rfl) ⟨320433, by rfl⟩ : syracuseStep 854489 = 640867) B640867
theorem B2165251 : Blo 503794 2165251 := bstep (se 1 (by rfl) ⟨1623938, by rfl⟩ : syracuseStep 2165251 = 3247877) B3247877
theorem B1706561 : Blo 503794 1706561 := bstep (se 2 (by rfl) ⟨639960, by rfl⟩ : syracuseStep 1706561 = 1279921) B1279921
theorem B756299 : Blo 503794 756299 := bstep (se 1 (by rfl) ⟨567224, by rfl⟩ : syracuseStep 756299 = 1134449) B1134449
theorem B756311 : Blo 503794 756311 := bstep (se 1 (by rfl) ⟨567233, by rfl⟩ : syracuseStep 756311 = 1134467) B1134467
theorem B854617 : Blo 503794 854617 := bstep (se 2 (by rfl) ⟨320481, by rfl⟩ : syracuseStep 854617 = 640963) B640963
theorem B756377 : Blo 503794 756377 := bstep (se 2 (by rfl) ⟨283641, by rfl⟩ : syracuseStep 756377 = 567283) B567283
theorem B756491 : Blo 503794 756491 := bstep (se 1 (by rfl) ⟨567368, by rfl⟩ : syracuseStep 756491 = 1134737) B1134737
theorem B756503 : Blo 503794 756503 := bstep (se 1 (by rfl) ⟨567377, by rfl⟩ : syracuseStep 756503 = 1134755) B1134755
theorem B1280843 : Blo 503794 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B2886475 : Blo 503794 2886475 := bstep (se 1 (by rfl) ⟨2164856, by rfl⟩ : syracuseStep 2886475 = 4329713) B4329713
theorem B1149785 : Blo 503794 1149785 := bstep (se 2 (by rfl) ⟨431169, by rfl⟩ : syracuseStep 1149785 = 862339) B862339
theorem B756569 : Blo 503794 756569 := bstep (se 2 (by rfl) ⟨283713, by rfl⟩ : syracuseStep 756569 = 567427) B567427
theorem B1444787 : Blo 503794 1444787 := bstep (se 1 (by rfl) ⟨1083590, by rfl⟩ : syracuseStep 1444787 = 2167181) B2167181
theorem B756683 : Blo 503794 756683 := bstep (se 1 (by rfl) ⟨567512, by rfl⟩ : syracuseStep 756683 = 1135025) B1135025
theorem B756695 : Blo 503794 756695 := bstep (se 1 (by rfl) ⟨567521, by rfl⟩ : syracuseStep 756695 = 1135043) B1135043
theorem B1084403 : Blo 503794 1084403 := bstep (se 1 (by rfl) ⟨813302, by rfl⟩ : syracuseStep 1084403 = 1626605) B1626605
theorem B756761 : Blo 503794 756761 := bstep (se 2 (by rfl) ⟨283785, by rfl⟩ : syracuseStep 756761 = 567571) B567571
theorem B2165849 : Blo 503794 2165849 := bstep (se 2 (by rfl) ⟨812193, by rfl⟩ : syracuseStep 2165849 = 1624387) B1624387
theorem B1707101 : Blo 503794 1707101 := bstep (se 3 (by rfl) ⟨320081, by rfl⟩ : syracuseStep 1707101 = 640163) B640163
theorem B2886749 : Blo 503794 2886749 := bstep (se 3 (by rfl) ⟨541265, by rfl⟩ : syracuseStep 2886749 = 1082531) B1082531
theorem B756875 : Blo 503794 756875 := bstep (se 1 (by rfl) ⟨567656, by rfl⟩ : syracuseStep 756875 = 1135313) B1135313
theorem B756887 : Blo 503794 756887 := bstep (se 1 (by rfl) ⟨567665, by rfl⟩ : syracuseStep 756887 = 1135331) B1135331
theorem B855191 : Blo 503794 855191 := bstep (se 1 (by rfl) ⟨641393, by rfl⟩ : syracuseStep 855191 = 1282787) B1282787
theorem B1445015 : Blo 503794 1445015 := bstep (se 1 (by rfl) ⟨1083761, by rfl⟩ : syracuseStep 1445015 = 2167523) B2167523
theorem B1281217 : Blo 503794 1281217 := bstep (se 2 (by rfl) ⟨480456, by rfl⟩ : syracuseStep 1281217 = 960913) B960913
theorem B756953 : Blo 503794 756953 := bstep (se 2 (by rfl) ⟨283857, by rfl⟩ : syracuseStep 756953 = 567715) B567715
theorem B855319 : Blo 503794 855319 := bstep (se 1 (by rfl) ⟨641489, by rfl⟩ : syracuseStep 855319 = 1282979) B1282979
theorem B757067 : Blo 503794 757067 := bstep (se 1 (by rfl) ⟨567800, by rfl⟩ : syracuseStep 757067 = 1135601) B1135601
theorem B757079 : Blo 503794 757079 := bstep (se 1 (by rfl) ⟨567809, by rfl⟩ : syracuseStep 757079 = 1135619) B1135619
theorem B757145 : Blo 503794 757145 := bstep (se 2 (by rfl) ⟨283929, by rfl⟩ : syracuseStep 757145 = 567859) B567859
theorem B2166209 : Blo 503794 2166209 := bstep (se 2 (by rfl) ⟨812328, by rfl⟩ : syracuseStep 2166209 = 1624657) B1624657
theorem B1445323 : Blo 503794 1445323 := bstep (se 1 (by rfl) ⟨1083992, by rfl⟩ : syracuseStep 1445323 = 2167985) B2167985
theorem B757259 : Blo 503794 757259 := bstep (se 1 (by rfl) ⟨567944, by rfl⟩ : syracuseStep 757259 = 1135889) B1135889
theorem B757271 : Blo 503794 757271 := bstep (se 1 (by rfl) ⟨567953, by rfl⟩ : syracuseStep 757271 = 1135907) B1135907
theorem B757337 : Blo 503794 757337 := bstep (se 2 (by rfl) ⟨284001, by rfl⟩ : syracuseStep 757337 = 568003) B568003
theorem B757451 : Blo 503794 757451 := bstep (se 1 (by rfl) ⟨568088, by rfl⟩ : syracuseStep 757451 = 1136177) B1136177
theorem B757463 : Blo 503794 757463 := bstep (se 1 (by rfl) ⟨568097, by rfl⟩ : syracuseStep 757463 = 1136195) B1136195
theorem B1445597 : Blo 503794 1445597 := bstep (se 3 (by rfl) ⟨271049, by rfl⟩ : syracuseStep 1445597 = 542099) B542099
theorem B2559761 : Blo 503794 2559761 := bstep (se 2 (by rfl) ⟨959910, by rfl⟩ : syracuseStep 2559761 = 1919821) B1919821
theorem B1281815 : Blo 503794 1281815 := bstep (se 1 (by rfl) ⟨961361, by rfl⟩ : syracuseStep 1281815 = 1922723) B1922723
theorem B757529 : Blo 503794 757529 := bstep (se 2 (by rfl) ⟨284073, by rfl⟩ : syracuseStep 757529 = 568147) B568147
theorem B757643 : Blo 503794 757643 := bstep (se 1 (by rfl) ⟨568232, by rfl⟩ : syracuseStep 757643 = 1136465) B1136465
theorem B855947 : Blo 503794 855947 := bstep (se 1 (by rfl) ⟨641960, by rfl⟩ : syracuseStep 855947 = 1283921) B1283921
theorem B757655 : Blo 503794 757655 := bstep (se 1 (by rfl) ⟨568241, by rfl⟩ : syracuseStep 757655 = 1136483) B1136483
theorem B2559923 : Blo 503794 2559923 := bstep (se 1 (by rfl) ⟨1919942, by rfl⟩ : syracuseStep 2559923 = 3839885) B3839885
theorem B757721 : Blo 503794 757721 := bstep (se 2 (by rfl) ⟨284145, by rfl⟩ : syracuseStep 757721 = 568291) B568291
theorem B856075 : Blo 503794 856075 := bstep (se 1 (by rfl) ⟨642056, by rfl⟩ : syracuseStep 856075 = 1284113) B1284113
theorem B757835 : Blo 503794 757835 := bstep (se 1 (by rfl) ⟨568376, by rfl⟩ : syracuseStep 757835 = 1136753) B1136753
theorem B757847 : Blo 503794 757847 := bstep (se 1 (by rfl) ⟨568385, by rfl⟩ : syracuseStep 757847 = 1136771) B1136771
theorem B757913 : Blo 503794 757913 := bstep (se 2 (by rfl) ⟨284217, by rfl⟩ : syracuseStep 757913 = 568435) B568435
theorem B856217 : Blo 503794 856217 := bstep (se 2 (by rfl) ⟨321081, by rfl⟩ : syracuseStep 856217 = 642163) B642163
theorem B1708235 : Blo 503794 1708235 := bstep (se 1 (by rfl) ⟨1281176, by rfl⟩ : syracuseStep 1708235 = 2562353) B2562353
theorem B758027 : Blo 503794 758027 := bstep (se 1 (by rfl) ⟨568520, by rfl⟩ : syracuseStep 758027 = 1137041) B1137041
theorem B758039 : Blo 503794 758039 := bstep (se 1 (by rfl) ⟨568529, by rfl⟩ : syracuseStep 758039 = 1137059) B1137059
theorem B856345 : Blo 503794 856345 := bstep (se 2 (by rfl) ⟨321129, by rfl⟩ : syracuseStep 856345 = 642259) B642259
theorem B758105 : Blo 503794 758105 := bstep (se 2 (by rfl) ⟨284289, by rfl⟩ : syracuseStep 758105 = 568579) B568579
theorem B3248515 : Blo 503794 3248515 := bstep (se 1 (by rfl) ⟨2436386, by rfl⟩ : syracuseStep 3248515 = 4872773) B4872773
theorem B1151435 : Blo 503794 1151435 := bstep (se 1 (by rfl) ⟨863576, by rfl⟩ : syracuseStep 1151435 = 1727153) B1727153
theorem B758219 : Blo 503794 758219 := bstep (se 1 (by rfl) ⟨568664, by rfl⟩ : syracuseStep 758219 = 1137329) B1137329
theorem B758231 : Blo 503794 758231 := bstep (se 1 (by rfl) ⟨568673, by rfl⟩ : syracuseStep 758231 = 1137347) B1137347
theorem B1708505 : Blo 503794 1708505 := bstep (se 2 (by rfl) ⟨640689, by rfl⟩ : syracuseStep 1708505 = 1281379) B1281379
theorem B758297 : Blo 503794 758297 := bstep (se 2 (by rfl) ⟨284361, by rfl⟩ : syracuseStep 758297 = 568723) B568723
theorem B1282625 : Blo 503794 1282625 := bstep (se 2 (by rfl) ⟨480984, by rfl⟩ : syracuseStep 1282625 = 961969) B961969
theorem B758411 : Blo 503794 758411 := bstep (se 1 (by rfl) ⟨568808, by rfl⟩ : syracuseStep 758411 = 1137617) B1137617
theorem B758423 : Blo 503794 758423 := bstep (se 1 (by rfl) ⟨568817, by rfl⟩ : syracuseStep 758423 = 1137635) B1137635
theorem B4625113 : Blo 503794 4625113 := bstep (se 2 (by rfl) ⟨1734417, by rfl⟩ : syracuseStep 4625113 = 3468835) B3468835
theorem B758489 : Blo 503794 758489 := bstep (se 2 (by rfl) ⟨284433, by rfl⟩ : syracuseStep 758489 = 568867) B568867
theorem B4854593 : Blo 503794 4854593 := bstep (se 2 (by rfl) ⟨1820472, by rfl⟩ : syracuseStep 4854593 = 3640945) B3640945
theorem B758603 : Blo 503794 758603 := bstep (se 1 (by rfl) ⟨568952, by rfl⟩ : syracuseStep 758603 = 1137905) B1137905
theorem B758615 : Blo 503794 758615 := bstep (se 1 (by rfl) ⟨568961, by rfl⟩ : syracuseStep 758615 = 1137923) B1137923
theorem B758681 : Blo 503794 758681 := bstep (se 2 (by rfl) ⟨284505, by rfl⟩ : syracuseStep 758681 = 569011) B569011
theorem B758795 : Blo 503794 758795 := bstep (se 1 (by rfl) ⟨569096, by rfl⟩ : syracuseStep 758795 = 1138193) B1138193
theorem B758807 : Blo 503794 758807 := bstep (se 1 (by rfl) ⟨569105, by rfl⟩ : syracuseStep 758807 = 1138211) B1138211
theorem B758873 : Blo 503794 758873 := bstep (se 2 (by rfl) ⟨284577, by rfl⟩ : syracuseStep 758873 = 569155) B569155
theorem B1283161 : Blo 503794 1283161 := bstep (se 2 (by rfl) ⟨481185, by rfl⟩ : syracuseStep 1283161 = 962371) B962371
theorem B1709207 : Blo 503794 1709207 := bstep (se 1 (by rfl) ⟨1281905, by rfl⟩ : syracuseStep 1709207 = 2563811) B2563811
theorem B758987 : Blo 503794 758987 := bstep (se 1 (by rfl) ⟨569240, by rfl⟩ : syracuseStep 758987 = 1138481) B1138481
theorem B758999 : Blo 503794 758999 := bstep (se 1 (by rfl) ⟨569249, by rfl⟩ : syracuseStep 758999 = 1138499) B1138499
theorem B6493445 : Blo 503794 6493445 := bstep (se 4 (by rfl) ⟨608760, by rfl⟩ : syracuseStep 6493445 = 1217521) B1217521
theorem B759065 : Blo 503794 759065 := bstep (se 2 (by rfl) ⟨284649, by rfl⟩ : syracuseStep 759065 = 569299) B569299
theorem B759179 : Blo 503794 759179 := bstep (se 1 (by rfl) ⟨569384, by rfl⟩ : syracuseStep 759179 = 1138769) B1138769
theorem B759191 : Blo 503794 759191 := bstep (se 1 (by rfl) ⟨569393, by rfl⟩ : syracuseStep 759191 = 1138787) B1138787
theorem B759257 : Blo 503794 759257 := bstep (se 2 (by rfl) ⟨284721, by rfl⟩ : syracuseStep 759257 = 569443) B569443
theorem B1840657 : Blo 503794 1840657 := bstep (se 2 (by rfl) ⟨690246, by rfl⟩ : syracuseStep 1840657 = 1380493) B1380493
theorem B1938995 : Blo 503794 1938995 := bstep (se 1 (by rfl) ⟨1454246, by rfl⟩ : syracuseStep 1938995 = 2908493) B2908493
theorem B759371 : Blo 503794 759371 := bstep (se 1 (by rfl) ⟨569528, by rfl⟩ : syracuseStep 759371 = 1139057) B1139057
theorem B759383 : Blo 503794 759383 := bstep (se 1 (by rfl) ⟨569537, by rfl⟩ : syracuseStep 759383 = 1139075) B1139075
theorem B1021591 : Blo 503794 1021591 := bstep (se 1 (by rfl) ⟨766193, by rfl⟩ : syracuseStep 1021591 = 1532387) B1532387
theorem B759449 : Blo 503794 759449 := bstep (se 2 (by rfl) ⟨284793, by rfl⟩ : syracuseStep 759449 = 569587) B569587
theorem B1709747 : Blo 503794 1709747 := bstep (se 1 (by rfl) ⟨1282310, by rfl⟩ : syracuseStep 1709747 = 2564621) B2564621
theorem B759563 : Blo 503794 759563 := bstep (se 1 (by rfl) ⟨569672, by rfl⟩ : syracuseStep 759563 = 1139345) B1139345
theorem B759575 : Blo 503794 759575 := bstep (se 1 (by rfl) ⟨569681, by rfl⟩ : syracuseStep 759575 = 1139363) B1139363
theorem B2561867 : Blo 503794 2561867 := bstep (se 1 (by rfl) ⟨1921400, by rfl⟩ : syracuseStep 2561867 = 3842801) B3842801
theorem B759641 : Blo 503794 759641 := bstep (se 2 (by rfl) ⟨284865, by rfl⟩ : syracuseStep 759641 = 569731) B569731
theorem B1710017 : Blo 503794 1710017 := bstep (se 2 (by rfl) ⟨641256, by rfl⟩ : syracuseStep 1710017 = 1282513) B1282513
theorem B759755 : Blo 503794 759755 := bstep (se 1 (by rfl) ⟨569816, by rfl⟩ : syracuseStep 759755 = 1139633) B1139633
theorem B759767 : Blo 503794 759767 := bstep (se 1 (by rfl) ⟨569825, by rfl⟩ : syracuseStep 759767 = 1139651) B1139651
theorem B956441 : Blo 503794 956441 := bstep (se 2 (by rfl) ⟨358665, by rfl⟩ : syracuseStep 956441 = 717331) B717331
theorem B759833 : Blo 503794 759833 := bstep (se 2 (by rfl) ⟨284937, by rfl⟩ : syracuseStep 759833 = 569875) B569875
theorem B4626497 : Blo 503794 4626497 := bstep (se 2 (by rfl) ⟨1734936, by rfl⟩ : syracuseStep 4626497 = 3469873) B3469873
theorem B759947 : Blo 503794 759947 := bstep (se 1 (by rfl) ⟨569960, by rfl⟩ : syracuseStep 759947 = 1139921) B1139921
theorem B759959 : Blo 503794 759959 := bstep (se 1 (by rfl) ⟨569969, by rfl⟩ : syracuseStep 759959 = 1139939) B1139939
theorem B1284275 : Blo 503794 1284275 := bstep (se 1 (by rfl) ⟨963206, by rfl⟩ : syracuseStep 1284275 = 1926413) B1926413
theorem B760025 : Blo 503794 760025 := bstep (se 2 (by rfl) ⟨285009, by rfl⟩ : syracuseStep 760025 = 570019) B570019
theorem B760139 : Blo 503794 760139 := bstep (se 1 (by rfl) ⟨570104, by rfl⟩ : syracuseStep 760139 = 1140209) B1140209
theorem B760151 : Blo 503794 760151 := bstep (se 1 (by rfl) ⟨570113, by rfl⟩ : syracuseStep 760151 = 1140227) B1140227
theorem B1939801 : Blo 503794 1939801 := bstep (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) B1454851
theorem B760217 : Blo 503794 760217 := bstep (se 2 (by rfl) ⟨285081, by rfl⟩ : syracuseStep 760217 = 570163) B570163
theorem B4004275 : Blo 503794 4004275 := bstep (se 1 (by rfl) ⟨3003206, by rfl⟩ : syracuseStep 4004275 = 6006413) B6006413
theorem B1284569 : Blo 503794 1284569 := bstep (se 2 (by rfl) ⟨481713, by rfl⟩ : syracuseStep 1284569 = 963427) B963427
theorem B1710557 : Blo 503794 1710557 := bstep (se 3 (by rfl) ⟨320729, by rfl⟩ : syracuseStep 1710557 = 641459) B641459
theorem B760331 : Blo 503794 760331 := bstep (se 1 (by rfl) ⟨570248, by rfl⟩ : syracuseStep 760331 = 1140497) B1140497
theorem B760343 : Blo 503794 760343 := bstep (se 1 (by rfl) ⟨570257, by rfl⟩ : syracuseStep 760343 = 1140515) B1140515
theorem B760409 : Blo 503794 760409 := bstep (se 2 (by rfl) ⟨285153, by rfl⟩ : syracuseStep 760409 = 570307) B570307
theorem B760523 : Blo 503794 760523 := bstep (se 1 (by rfl) ⟨570392, by rfl⟩ : syracuseStep 760523 = 1140785) B1140785
theorem B760535 : Blo 503794 760535 := bstep (se 1 (by rfl) ⟨570401, by rfl⟩ : syracuseStep 760535 = 1140803) B1140803
theorem B4922117 : Blo 503794 4922117 := bstep (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) B922897
theorem B760601 : Blo 503794 760601 := bstep (se 2 (by rfl) ⟨285225, by rfl⟩ : syracuseStep 760601 = 570451) B570451
theorem B3644261 : Blo 503794 3644261 := bstep (se 4 (by rfl) ⟨341649, by rfl⟩ : syracuseStep 3644261 = 683299) B683299
theorem B760715 : Blo 503794 760715 := bstep (se 1 (by rfl) ⟨570536, by rfl⟩ : syracuseStep 760715 = 1141073) B1141073
theorem B760727 : Blo 503794 760727 := bstep (se 1 (by rfl) ⟨570545, by rfl⟩ : syracuseStep 760727 = 1141091) B1141091
theorem B760793 : Blo 503794 760793 := bstep (se 2 (by rfl) ⟨285297, by rfl⟩ : syracuseStep 760793 = 570595) B570595
theorem B5741603 : Blo 503794 5741603 := bstep (se 1 (by rfl) ⟨4306202, by rfl⟩ : syracuseStep 5741603 = 8612405) B8612405
theorem B2432065 : Blo 503794 2432065 := bstep (se 2 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 2432065 = 1824049) B1824049
theorem B760907 : Blo 503794 760907 := bstep (se 1 (by rfl) ⟨570680, by rfl⟩ : syracuseStep 760907 = 1141361) B1141361
theorem B760919 : Blo 503794 760919 := bstep (se 1 (by rfl) ⟨570689, by rfl⟩ : syracuseStep 760919 = 1141379) B1141379
theorem B4660325 : Blo 503794 4660325 := bstep (se 4 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 4660325 = 873811) B873811
theorem B760985 : Blo 503794 760985 := bstep (se 2 (by rfl) ⟨285369, by rfl⟩ : syracuseStep 760985 = 570739) B570739
theorem B761099 : Blo 503794 761099 := bstep (se 1 (by rfl) ⟨570824, by rfl⟩ : syracuseStep 761099 = 1141649) B1141649
theorem B761111 : Blo 503794 761111 := bstep (se 1 (by rfl) ⟨570833, by rfl⟩ : syracuseStep 761111 = 1141667) B1141667
theorem B761177 : Blo 503794 761177 := bstep (se 2 (by rfl) ⟨285441, by rfl⟩ : syracuseStep 761177 = 570883) B570883
theorem B957899 : Blo 503794 957899 := bstep (se 1 (by rfl) ⟨718424, by rfl⟩ : syracuseStep 957899 = 1436849) B1436849
theorem B761291 : Blo 503794 761291 := bstep (se 1 (by rfl) ⟨570968, by rfl⟩ : syracuseStep 761291 = 1141937) B1141937
theorem B761303 : Blo 503794 761303 := bstep (se 1 (by rfl) ⟨570977, by rfl⟩ : syracuseStep 761303 = 1141955) B1141955
theorem B761369 : Blo 503794 761369 := bstep (se 2 (by rfl) ⟨285513, by rfl⟩ : syracuseStep 761369 = 571027) B571027
theorem B2563649 : Blo 503794 2563649 := bstep (se 2 (by rfl) ⟨961368, by rfl⟩ : syracuseStep 2563649 = 1922737) B1922737
theorem B1711691 : Blo 503794 1711691 := bstep (se 1 (by rfl) ⟨1283768, by rfl⟩ : syracuseStep 1711691 = 2567537) B2567537
theorem B958081 : Blo 503794 958081 := bstep (se 2 (by rfl) ⟨359280, by rfl⟩ : syracuseStep 958081 = 718561) B718561
theorem B2301571 : Blo 503794 2301571 := bstep (se 1 (by rfl) ⟨1726178, by rfl⟩ : syracuseStep 2301571 = 3452357) B3452357
theorem B761483 : Blo 503794 761483 := bstep (se 1 (by rfl) ⟨571112, by rfl⟩ : syracuseStep 761483 = 1142225) B1142225
theorem B761495 : Blo 503794 761495 := bstep (se 1 (by rfl) ⟨571121, by rfl⟩ : syracuseStep 761495 = 1142243) B1142243
theorem B761561 : Blo 503794 761561 := bstep (se 2 (by rfl) ⟨285585, by rfl⟩ : syracuseStep 761561 = 571171) B571171
theorem B761675 : Blo 503794 761675 := bstep (se 1 (by rfl) ⟨571256, by rfl⟩ : syracuseStep 761675 = 1142513) B1142513
theorem B761687 : Blo 503794 761687 := bstep (se 1 (by rfl) ⟨571265, by rfl⟩ : syracuseStep 761687 = 1142531) B1142531
theorem B1711961 : Blo 503794 1711961 := bstep (se 2 (by rfl) ⟨641985, by rfl⟩ : syracuseStep 1711961 = 1283971) B1283971
theorem B925643 : Blo 503794 925643 := bstep (se 1 (by rfl) ⟨694232, by rfl⟩ : syracuseStep 925643 = 1388465) B1388465
theorem B958529 : Blo 503794 958529 := bstep (se 2 (by rfl) ⟨359448, by rfl⟩ : syracuseStep 958529 = 718897) B718897
theorem B1876061 : Blo 503794 1876061 := bstep (se 3 (by rfl) ⟨351761, by rfl⟩ : syracuseStep 1876061 = 703523) B703523
theorem B1941707 : Blo 503794 1941707 := bstep (se 1 (by rfl) ⟨1456280, by rfl⟩ : syracuseStep 1941707 = 2912561) B2912561
theorem B958871 : Blo 503794 958871 := bstep (se 1 (by rfl) ⟨719153, by rfl⟩ : syracuseStep 958871 = 1438307) B1438307
theorem B1712663 : Blo 503794 1712663 := bstep (se 1 (by rfl) ⟨1284497, by rfl⟩ : syracuseStep 1712663 = 2568995) B2568995
theorem B729751 : Blo 503794 729751 := bstep (se 1 (by rfl) ⟨547313, by rfl⟩ : syracuseStep 729751 = 1094627) B1094627
theorem B6169445 : Blo 503794 6169445 := bstep (se 4 (by rfl) ⟨578385, by rfl⟩ : syracuseStep 6169445 = 1156771) B1156771
theorem B959539 : Blo 503794 959539 := bstep (se 1 (by rfl) ⟨719654, by rfl⟩ : syracuseStep 959539 = 1439309) B1439309
theorem B1713203 : Blo 503794 1713203 := bstep (se 1 (by rfl) ⟨1284902, by rfl⟩ : syracuseStep 1713203 = 2569805) B2569805
theorem B1713473 : Blo 503794 1713473 := bstep (se 2 (by rfl) ⟨642552, by rfl⟩ : syracuseStep 1713473 = 1285105) B1285105
theorem B2565593 : Blo 503794 2565593 := bstep (se 2 (by rfl) ⟨962097, by rfl⟩ : syracuseStep 2565593 = 1924195) B1924195
theorem B959987 : Blo 503794 959987 := bstep (se 1 (by rfl) ⟨719990, by rfl⟩ : syracuseStep 959987 = 1439981) B1439981
theorem B960025 : Blo 503794 960025 := bstep (se 2 (by rfl) ⟨360009, by rfl⟩ : syracuseStep 960025 = 720019) B720019
theorem B1975853 : Blo 503794 1975853 := bstep (se 3 (by rfl) ⟨370472, by rfl⟩ : syracuseStep 1975853 = 740945) B740945
theorem B566923 : Blo 503794 566923 := bstep (se 1 (by rfl) ⟨425192, by rfl⟩ : syracuseStep 566923 = 850385) B850385
theorem B567031 : Blo 503794 567031 := bstep (se 1 (by rfl) ⟨425273, by rfl⟩ : syracuseStep 567031 = 850547) B850547
theorem B567211 : Blo 503794 567211 := bstep (se 1 (by rfl) ⟨425408, by rfl⟩ : syracuseStep 567211 = 850817) B850817
theorem B960473 : Blo 503794 960473 := bstep (se 2 (by rfl) ⟨360177, by rfl⟩ : syracuseStep 960473 = 720355) B720355
theorem B1026035 : Blo 503794 1026035 := bstep (se 1 (by rfl) ⟨769526, by rfl⟩ : syracuseStep 1026035 = 1539053) B1539053
theorem B567319 : Blo 503794 567319 := bstep (se 1 (by rfl) ⟨425489, by rfl⟩ : syracuseStep 567319 = 850979) B850979
theorem B6924419 : Blo 503794 6924419 := bstep (se 1 (by rfl) ⟨5193314, by rfl⟩ : syracuseStep 6924419 = 10386629) B10386629
theorem B4368563 : Blo 503794 4368563 := bstep (se 1 (by rfl) ⟨3276422, by rfl⟩ : syracuseStep 4368563 = 6552845) B6552845
theorem B567499 : Blo 503794 567499 := bstep (se 1 (by rfl) ⟨425624, by rfl⟩ : syracuseStep 567499 = 851249) B851249
theorem B567607 : Blo 503794 567607 := bstep (se 1 (by rfl) ⟨425705, by rfl⟩ : syracuseStep 567607 = 851411) B851411
theorem B567787 : Blo 503794 567787 := bstep (se 1 (by rfl) ⟨425840, by rfl⟩ : syracuseStep 567787 = 851681) B851681
theorem B567895 : Blo 503794 567895 := bstep (se 1 (by rfl) ⟨425921, by rfl⟩ : syracuseStep 567895 = 851843) B851843
theorem B961217 : Blo 503794 961217 := bstep (se 2 (by rfl) ⟨360456, by rfl⟩ : syracuseStep 961217 = 720913) B720913
theorem B568075 : Blo 503794 568075 := bstep (se 1 (by rfl) ⟨426056, by rfl⟩ : syracuseStep 568075 = 852113) B852113
theorem B568183 : Blo 503794 568183 := bstep (se 1 (by rfl) ⟨426137, by rfl⟩ : syracuseStep 568183 = 852275) B852275
theorem B1846147 : Blo 503794 1846147 := bstep (se 1 (by rfl) ⟨1384610, by rfl⟩ : syracuseStep 1846147 = 2769221) B2769221
theorem B961483 : Blo 503794 961483 := bstep (se 1 (by rfl) ⟨721112, by rfl⟩ : syracuseStep 961483 = 1442225) B1442225
theorem B1027073 : Blo 503794 1027073 := bstep (se 2 (by rfl) ⟨385152, by rfl⟩ : syracuseStep 1027073 = 770305) B770305
theorem B568363 : Blo 503794 568363 := bstep (se 1 (by rfl) ⟨426272, by rfl⟩ : syracuseStep 568363 = 852545) B852545
theorem B2567213 : Blo 503794 2567213 := bstep (se 3 (by rfl) ⟨481352, by rfl⟩ : syracuseStep 2567213 = 962705) B962705
theorem B4336685 : Blo 503794 4336685 := bstep (se 3 (by rfl) ⟨813128, by rfl⟩ : syracuseStep 4336685 = 1626257) B1626257
theorem B568471 : Blo 503794 568471 := bstep (se 1 (by rfl) ⟨426353, by rfl⟩ : syracuseStep 568471 = 852707) B852707
theorem B568651 : Blo 503794 568651 := bstep (se 1 (by rfl) ⟨426488, by rfl⟩ : syracuseStep 568651 = 852977) B852977
theorem B961931 : Blo 503794 961931 := bstep (se 1 (by rfl) ⟨721448, by rfl⟩ : syracuseStep 961931 = 1442897) B1442897
theorem B568759 : Blo 503794 568759 := bstep (se 1 (by rfl) ⟨426569, by rfl⟩ : syracuseStep 568759 = 853139) B853139
theorem B962113 : Blo 503794 962113 := bstep (se 2 (by rfl) ⟨360792, by rfl⟩ : syracuseStep 962113 = 721585) B721585
theorem B568939 : Blo 503794 568939 := bstep (se 1 (by rfl) ⟨426704, by rfl⟩ : syracuseStep 568939 = 853409) B853409
theorem B1027723 : Blo 503794 1027723 := bstep (se 1 (by rfl) ⟨770792, by rfl⟩ : syracuseStep 1027723 = 1541585) B1541585
theorem B3878551 : Blo 503794 3878551 := bstep (se 1 (by rfl) ⟨2908913, by rfl⟩ : syracuseStep 3878551 = 5817827) B5817827
theorem B569047 : Blo 503794 569047 := bstep (se 1 (by rfl) ⟨426785, by rfl⟩ : syracuseStep 569047 = 853571) B853571
theorem B4108097 : Blo 503794 4108097 := bstep (se 2 (by rfl) ⟨1540536, by rfl⟩ : syracuseStep 4108097 = 3081073) B3081073
theorem B3518309 : Blo 503794 3518309 := bstep (se 4 (by rfl) ⟨329841, by rfl⟩ : syracuseStep 3518309 = 659683) B659683
theorem B569227 : Blo 503794 569227 := bstep (se 1 (by rfl) ⟨426920, by rfl⟩ : syracuseStep 569227 = 853841) B853841
theorem B962455 : Blo 503794 962455 := bstep (se 1 (by rfl) ⟨721841, by rfl⟩ : syracuseStep 962455 = 1443683) B1443683
theorem B1945523 : Blo 503794 1945523 := bstep (se 1 (by rfl) ⟨1459142, by rfl⟩ : syracuseStep 1945523 = 2918285) B2918285
theorem B13840307 : Blo 503794 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B503799 : Blo 503794 503799 := bstep (se 1 (by rfl) ⟨377849, by rfl⟩ : syracuseStep 503799 = 755699) B755699
theorem B569335 : Blo 503794 569335 := bstep (se 1 (by rfl) ⟨427001, by rfl⟩ : syracuseStep 569335 = 854003) B854003
theorem B503819 : Blo 503794 503819 := bstep (se 1 (by rfl) ⟨377864, by rfl⟩ : syracuseStep 503819 = 755729) B755729
theorem B503831 : Blo 503794 503831 := bstep (se 1 (by rfl) ⟨377873, by rfl⟩ : syracuseStep 503831 = 755747) B755747
theorem B503851 : Blo 503794 503851 := bstep (se 1 (by rfl) ⟨377888, by rfl⟩ : syracuseStep 503851 = 755777) B755777
theorem B503863 : Blo 503794 503863 := bstep (se 1 (by rfl) ⟨377897, by rfl⟩ : syracuseStep 503863 = 755795) B755795
theorem B503883 : Blo 503794 503883 := bstep (se 1 (by rfl) ⟨377912, by rfl⟩ : syracuseStep 503883 = 755825) B755825
theorem B503895 : Blo 503794 503895 := bstep (se 1 (by rfl) ⟨377921, by rfl⟩ : syracuseStep 503895 = 755843) B755843
theorem B503915 : Blo 503794 503915 := bstep (se 1 (by rfl) ⟨377936, by rfl⟩ : syracuseStep 503915 = 755873) B755873
theorem B962675 : Blo 503794 962675 := bstep (se 1 (by rfl) ⟨722006, by rfl⟩ : syracuseStep 962675 = 1444013) B1444013
theorem B503927 : Blo 503794 503927 := bstep (se 1 (by rfl) ⟨377945, by rfl⟩ : syracuseStep 503927 = 755891) B755891
theorem B503947 : Blo 503794 503947 := bstep (se 1 (by rfl) ⟨377960, by rfl⟩ : syracuseStep 503947 = 755921) B755921
theorem B503959 : Blo 503794 503959 := bstep (se 1 (by rfl) ⟨377969, by rfl⟩ : syracuseStep 503959 = 755939) B755939
theorem B503979 : Blo 503794 503979 := bstep (se 1 (by rfl) ⟨377984, by rfl⟩ : syracuseStep 503979 = 755969) B755969
theorem B569515 : Blo 503794 569515 := bstep (se 1 (by rfl) ⟨427136, by rfl⟩ : syracuseStep 569515 = 854273) B854273
theorem B503991 : Blo 503794 503991 := bstep (se 1 (by rfl) ⟨377993, by rfl⟩ : syracuseStep 503991 = 755987) B755987
theorem B504011 : Blo 503794 504011 := bstep (se 1 (by rfl) ⟨378008, by rfl⟩ : syracuseStep 504011 = 756017) B756017
theorem B504023 : Blo 503794 504023 := bstep (se 1 (by rfl) ⟨378017, by rfl⟩ : syracuseStep 504023 = 756035) B756035
theorem B504043 : Blo 503794 504043 := bstep (se 1 (by rfl) ⟨378032, by rfl⟩ : syracuseStep 504043 = 756065) B756065
theorem B504055 : Blo 503794 504055 := bstep (se 1 (by rfl) ⟨378041, by rfl⟩ : syracuseStep 504055 = 756083) B756083
theorem B504075 : Blo 503794 504075 := bstep (se 1 (by rfl) ⟨378056, by rfl⟩ : syracuseStep 504075 = 756113) B756113
theorem B504087 : Blo 503794 504087 := bstep (se 1 (by rfl) ⟨378065, by rfl⟩ : syracuseStep 504087 = 756131) B756131
theorem B569623 : Blo 503794 569623 := bstep (se 1 (by rfl) ⟨427217, by rfl⟩ : syracuseStep 569623 = 854435) B854435
theorem B504107 : Blo 503794 504107 := bstep (se 1 (by rfl) ⟨378080, by rfl⟩ : syracuseStep 504107 = 756161) B756161
theorem B504119 : Blo 503794 504119 := bstep (se 1 (by rfl) ⟨378089, by rfl⟩ : syracuseStep 504119 = 756179) B756179
theorem B504139 : Blo 503794 504139 := bstep (se 1 (by rfl) ⟨378104, by rfl⟩ : syracuseStep 504139 = 756209) B756209
theorem B504151 : Blo 503794 504151 := bstep (se 1 (by rfl) ⟨378113, by rfl⟩ : syracuseStep 504151 = 756227) B756227
theorem B962903 : Blo 503794 962903 := bstep (se 1 (by rfl) ⟨722177, by rfl⟩ : syracuseStep 962903 = 1444355) B1444355
theorem B504171 : Blo 503794 504171 := bstep (se 1 (by rfl) ⟨378128, by rfl⟩ : syracuseStep 504171 = 756257) B756257
theorem B504183 : Blo 503794 504183 := bstep (se 1 (by rfl) ⟨378137, by rfl⟩ : syracuseStep 504183 = 756275) B756275
theorem B504203 : Blo 503794 504203 := bstep (se 1 (by rfl) ⟨378152, by rfl⟩ : syracuseStep 504203 = 756305) B756305
theorem B504215 : Blo 503794 504215 := bstep (se 1 (by rfl) ⟨378161, by rfl⟩ : syracuseStep 504215 = 756323) B756323
theorem B504235 : Blo 503794 504235 := bstep (se 1 (by rfl) ⟨378176, by rfl⟩ : syracuseStep 504235 = 756353) B756353
theorem B504247 : Blo 503794 504247 := bstep (se 1 (by rfl) ⟨378185, by rfl⟩ : syracuseStep 504247 = 756371) B756371
theorem B1913291 : Blo 503794 1913291 := bstep (se 1 (by rfl) ⟨1434968, by rfl⟩ : syracuseStep 1913291 = 2869937) B2869937
theorem B504267 : Blo 503794 504267 := bstep (se 1 (by rfl) ⟨378200, by rfl⟩ : syracuseStep 504267 = 756401) B756401
theorem B569803 : Blo 503794 569803 := bstep (se 1 (by rfl) ⟨427352, by rfl⟩ : syracuseStep 569803 = 854705) B854705
theorem B504279 : Blo 503794 504279 := bstep (se 1 (by rfl) ⟨378209, by rfl⟩ : syracuseStep 504279 = 756419) B756419
theorem B504299 : Blo 503794 504299 := bstep (se 1 (by rfl) ⟨378224, by rfl⟩ : syracuseStep 504299 = 756449) B756449
theorem B504311 : Blo 503794 504311 := bstep (se 1 (by rfl) ⟨378233, by rfl⟩ : syracuseStep 504311 = 756467) B756467
theorem B504331 : Blo 503794 504331 := bstep (se 1 (by rfl) ⟨378248, by rfl⟩ : syracuseStep 504331 = 756497) B756497
theorem B504343 : Blo 503794 504343 := bstep (se 1 (by rfl) ⟨378257, by rfl⟩ : syracuseStep 504343 = 756515) B756515
theorem B504363 : Blo 503794 504363 := bstep (se 1 (by rfl) ⟨378272, by rfl⟩ : syracuseStep 504363 = 756545) B756545
theorem B504375 : Blo 503794 504375 := bstep (se 1 (by rfl) ⟨378281, by rfl⟩ : syracuseStep 504375 = 756563) B756563
theorem B569911 : Blo 503794 569911 := bstep (se 1 (by rfl) ⟨427433, by rfl⟩ : syracuseStep 569911 = 854867) B854867
theorem B504395 : Blo 503794 504395 := bstep (se 1 (by rfl) ⟨378296, by rfl⟩ : syracuseStep 504395 = 756593) B756593
theorem B504407 : Blo 503794 504407 := bstep (se 1 (by rfl) ⟨378305, by rfl⟩ : syracuseStep 504407 = 756611) B756611
theorem B1028695 : Blo 503794 1028695 := bstep (se 1 (by rfl) ⟨771521, by rfl⟩ : syracuseStep 1028695 = 1543043) B1543043
theorem B963161 : Blo 503794 963161 := bstep (se 2 (by rfl) ⟨361185, by rfl⟩ : syracuseStep 963161 = 722371) B722371
theorem B504427 : Blo 503794 504427 := bstep (se 1 (by rfl) ⟨378320, by rfl⟩ : syracuseStep 504427 = 756641) B756641
theorem B504439 : Blo 503794 504439 := bstep (se 1 (by rfl) ⟨378329, by rfl⟩ : syracuseStep 504439 = 756659) B756659
theorem B504459 : Blo 503794 504459 := bstep (se 1 (by rfl) ⟨378344, by rfl⟩ : syracuseStep 504459 = 756689) B756689
theorem B1913489 : Blo 503794 1913489 := bstep (se 2 (by rfl) ⟨717558, by rfl⟩ : syracuseStep 1913489 = 1435117) B1435117
theorem B504471 : Blo 503794 504471 := bstep (se 1 (by rfl) ⟨378353, by rfl⟩ : syracuseStep 504471 = 756707) B756707
theorem B504491 : Blo 503794 504491 := bstep (se 1 (by rfl) ⟨378368, by rfl⟩ : syracuseStep 504491 = 756737) B756737
theorem B504503 : Blo 503794 504503 := bstep (se 1 (by rfl) ⟨378377, by rfl⟩ : syracuseStep 504503 = 756755) B756755
theorem B504523 : Blo 503794 504523 := bstep (se 1 (by rfl) ⟨378392, by rfl⟩ : syracuseStep 504523 = 756785) B756785
theorem B504535 : Blo 503794 504535 := bstep (se 1 (by rfl) ⟨378401, by rfl⟩ : syracuseStep 504535 = 756803) B756803
theorem B504555 : Blo 503794 504555 := bstep (se 1 (by rfl) ⟨378416, by rfl⟩ : syracuseStep 504555 = 756833) B756833
theorem B570091 : Blo 503794 570091 := bstep (se 1 (by rfl) ⟨427568, by rfl⟩ : syracuseStep 570091 = 855137) B855137
theorem B504567 : Blo 503794 504567 := bstep (se 1 (by rfl) ⟨378425, by rfl⟩ : syracuseStep 504567 = 756851) B756851
theorem B504587 : Blo 503794 504587 := bstep (se 1 (by rfl) ⟨378440, by rfl⟩ : syracuseStep 504587 = 756881) B756881
theorem B504599 : Blo 503794 504599 := bstep (se 1 (by rfl) ⟨378449, by rfl⟩ : syracuseStep 504599 = 756899) B756899
theorem B504619 : Blo 503794 504619 := bstep (se 1 (by rfl) ⟨378464, by rfl⟩ : syracuseStep 504619 = 756929) B756929
theorem B504631 : Blo 503794 504631 := bstep (se 1 (by rfl) ⟨378473, by rfl⟩ : syracuseStep 504631 = 756947) B756947
theorem B504651 : Blo 503794 504651 := bstep (se 1 (by rfl) ⟨378488, by rfl⟩ : syracuseStep 504651 = 756977) B756977
theorem B504663 : Blo 503794 504663 := bstep (se 1 (by rfl) ⟨378497, by rfl⟩ : syracuseStep 504663 = 756995) B756995
theorem B570199 : Blo 503794 570199 := bstep (se 1 (by rfl) ⟨427649, by rfl⟩ : syracuseStep 570199 = 855299) B855299
theorem B504683 : Blo 503794 504683 := bstep (se 1 (by rfl) ⟨378512, by rfl⟩ : syracuseStep 504683 = 757025) B757025
theorem B504695 : Blo 503794 504695 := bstep (se 1 (by rfl) ⟨378521, by rfl⟩ : syracuseStep 504695 = 757043) B757043
theorem B504715 : Blo 503794 504715 := bstep (se 1 (by rfl) ⟨378536, by rfl⟩ : syracuseStep 504715 = 757073) B757073
theorem B504727 : Blo 503794 504727 := bstep (se 1 (by rfl) ⟨378545, by rfl⟩ : syracuseStep 504727 = 757091) B757091
theorem B504747 : Blo 503794 504747 := bstep (se 1 (by rfl) ⟨378560, by rfl⟩ : syracuseStep 504747 = 757121) B757121
theorem B2110387 : Blo 503794 2110387 := bstep (se 1 (by rfl) ⟨1582790, by rfl⟩ : syracuseStep 2110387 = 3165581) B3165581
theorem B504759 : Blo 503794 504759 := bstep (se 1 (by rfl) ⟨378569, by rfl⟩ : syracuseStep 504759 = 757139) B757139
theorem B504779 : Blo 503794 504779 := bstep (se 1 (by rfl) ⟨378584, by rfl⟩ : syracuseStep 504779 = 757169) B757169
theorem B504791 : Blo 503794 504791 := bstep (se 1 (by rfl) ⟨378593, by rfl⟩ : syracuseStep 504791 = 757187) B757187
theorem B504811 : Blo 503794 504811 := bstep (se 1 (by rfl) ⟨378608, by rfl⟩ : syracuseStep 504811 = 757217) B757217
theorem B963571 : Blo 503794 963571 := bstep (se 1 (by rfl) ⟨722678, by rfl⟩ : syracuseStep 963571 = 1445357) B1445357
theorem B504823 : Blo 503794 504823 := bstep (se 1 (by rfl) ⟨378617, by rfl⟩ : syracuseStep 504823 = 757235) B757235
theorem B504843 : Blo 503794 504843 := bstep (se 1 (by rfl) ⟨378632, by rfl⟩ : syracuseStep 504843 = 757265) B757265
theorem B570379 : Blo 503794 570379 := bstep (se 1 (by rfl) ⟨427784, by rfl⟩ : syracuseStep 570379 = 855569) B855569
theorem B504855 : Blo 503794 504855 := bstep (se 1 (by rfl) ⟨378641, by rfl⟩ : syracuseStep 504855 = 757283) B757283
theorem B504875 : Blo 503794 504875 := bstep (se 1 (by rfl) ⟨378656, by rfl⟩ : syracuseStep 504875 = 757313) B757313
theorem B504887 : Blo 503794 504887 := bstep (se 1 (by rfl) ⟨378665, by rfl⟩ : syracuseStep 504887 = 757331) B757331
theorem B504907 : Blo 503794 504907 := bstep (se 1 (by rfl) ⟨378680, by rfl⟩ : syracuseStep 504907 = 757361) B757361
theorem B504919 : Blo 503794 504919 := bstep (se 1 (by rfl) ⟨378689, by rfl⟩ : syracuseStep 504919 = 757379) B757379
theorem B504939 : Blo 503794 504939 := bstep (se 1 (by rfl) ⟨378704, by rfl⟩ : syracuseStep 504939 = 757409) B757409
theorem B504951 : Blo 503794 504951 := bstep (se 1 (by rfl) ⟨378713, by rfl⟩ : syracuseStep 504951 = 757427) B757427
theorem B570487 : Blo 503794 570487 := bstep (se 1 (by rfl) ⟨427865, by rfl⟩ : syracuseStep 570487 = 855731) B855731
theorem B504971 : Blo 503794 504971 := bstep (se 1 (by rfl) ⟨378728, by rfl⟩ : syracuseStep 504971 = 757457) B757457
theorem B504983 : Blo 503794 504983 := bstep (se 1 (by rfl) ⟨378737, by rfl⟩ : syracuseStep 504983 = 757475) B757475
theorem B505003 : Blo 503794 505003 := bstep (se 1 (by rfl) ⟨378752, by rfl⟩ : syracuseStep 505003 = 757505) B757505
theorem B505015 : Blo 503794 505015 := bstep (se 1 (by rfl) ⟨378761, by rfl⟩ : syracuseStep 505015 = 757523) B757523
theorem B505035 : Blo 503794 505035 := bstep (se 1 (by rfl) ⟨378776, by rfl⟩ : syracuseStep 505035 = 757553) B757553
theorem B505047 : Blo 503794 505047 := bstep (se 1 (by rfl) ⟨378785, by rfl⟩ : syracuseStep 505047 = 757571) B757571
theorem B3650777 : Blo 503794 3650777 := bstep (se 2 (by rfl) ⟨1369041, by rfl⟩ : syracuseStep 3650777 = 2738083) B2738083
theorem B505067 : Blo 503794 505067 := bstep (se 1 (by rfl) ⟨378800, by rfl⟩ : syracuseStep 505067 = 757601) B757601
theorem B505079 : Blo 503794 505079 := bstep (se 1 (by rfl) ⟨378809, by rfl⟩ : syracuseStep 505079 = 757619) B757619
theorem B505099 : Blo 503794 505099 := bstep (se 1 (by rfl) ⟨378824, by rfl⟩ : syracuseStep 505099 = 757649) B757649
theorem B505111 : Blo 503794 505111 := bstep (se 1 (by rfl) ⟨378833, by rfl⟩ : syracuseStep 505111 = 757667) B757667
theorem B505131 : Blo 503794 505131 := bstep (se 1 (by rfl) ⟨378848, by rfl⟩ : syracuseStep 505131 = 757697) B757697
theorem B570667 : Blo 503794 570667 := bstep (se 1 (by rfl) ⟨428000, by rfl⟩ : syracuseStep 570667 = 856001) B856001
theorem B505143 : Blo 503794 505143 := bstep (se 1 (by rfl) ⟨378857, by rfl⟩ : syracuseStep 505143 = 757715) B757715
theorem B505163 : Blo 503794 505163 := bstep (se 1 (by rfl) ⟨378872, by rfl⟩ : syracuseStep 505163 = 757745) B757745
theorem B505175 : Blo 503794 505175 := bstep (se 1 (by rfl) ⟨378881, by rfl⟩ : syracuseStep 505175 = 757763) B757763
theorem B505195 : Blo 503794 505195 := bstep (se 1 (by rfl) ⟨378896, by rfl⟩ : syracuseStep 505195 = 757793) B757793
theorem B505207 : Blo 503794 505207 := bstep (se 1 (by rfl) ⟨378905, by rfl⟩ : syracuseStep 505207 = 757811) B757811
theorem B505227 : Blo 503794 505227 := bstep (se 1 (by rfl) ⟨378920, by rfl⟩ : syracuseStep 505227 = 757841) B757841
theorem B1914263 : Blo 503794 1914263 := bstep (se 1 (by rfl) ⟨1435697, by rfl⟩ : syracuseStep 1914263 = 2871395) B2871395
theorem B505239 : Blo 503794 505239 := bstep (se 1 (by rfl) ⟨378929, by rfl⟩ : syracuseStep 505239 = 757859) B757859
theorem B570775 : Blo 503794 570775 := bstep (se 1 (by rfl) ⟨428081, by rfl⟩ : syracuseStep 570775 = 856163) B856163
theorem B505259 : Blo 503794 505259 := bstep (se 1 (by rfl) ⟨378944, by rfl⟩ : syracuseStep 505259 = 757889) B757889
theorem B505271 : Blo 503794 505271 := bstep (se 1 (by rfl) ⟨378953, by rfl⟩ : syracuseStep 505271 = 757907) B757907
theorem B505291 : Blo 503794 505291 := bstep (se 1 (by rfl) ⟨378968, by rfl⟩ : syracuseStep 505291 = 757937) B757937
theorem B505303 : Blo 503794 505303 := bstep (se 1 (by rfl) ⟨378977, by rfl⟩ : syracuseStep 505303 = 757955) B757955
theorem B505323 : Blo 503794 505323 := bstep (se 1 (by rfl) ⟨378992, by rfl⟩ : syracuseStep 505323 = 757985) B757985
theorem B505335 : Blo 503794 505335 := bstep (se 1 (by rfl) ⟨379001, by rfl⟩ : syracuseStep 505335 = 758003) B758003
theorem B505355 : Blo 503794 505355 := bstep (se 1 (by rfl) ⟨379016, by rfl⟩ : syracuseStep 505355 = 758033) B758033
theorem B505367 : Blo 503794 505367 := bstep (se 1 (by rfl) ⟨379025, by rfl⟩ : syracuseStep 505367 = 758051) B758051
theorem B505387 : Blo 503794 505387 := bstep (se 1 (by rfl) ⟨379040, by rfl⟩ : syracuseStep 505387 = 758081) B758081
theorem B2307635 : Blo 503794 2307635 := bstep (se 1 (by rfl) ⟨1730726, by rfl⟩ : syracuseStep 2307635 = 3461453) B3461453
theorem B505399 : Blo 503794 505399 := bstep (se 1 (by rfl) ⟨379049, by rfl⟩ : syracuseStep 505399 = 758099) B758099
theorem B505419 : Blo 503794 505419 := bstep (se 1 (by rfl) ⟨379064, by rfl⟩ : syracuseStep 505419 = 758129) B758129
theorem B570955 : Blo 503794 570955 := bstep (se 1 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 570955 = 856433) B856433
theorem B505431 : Blo 503794 505431 := bstep (se 1 (by rfl) ⟨379073, by rfl⟩ : syracuseStep 505431 = 758147) B758147
theorem B1914461 : Blo 503794 1914461 := bstep (se 3 (by rfl) ⟨358961, by rfl⟩ : syracuseStep 1914461 = 717923) B717923
theorem B505451 : Blo 503794 505451 := bstep (se 1 (by rfl) ⟨379088, by rfl⟩ : syracuseStep 505451 = 758177) B758177
theorem B505463 : Blo 503794 505463 := bstep (se 1 (by rfl) ⟨379097, by rfl⟩ : syracuseStep 505463 = 758195) B758195
theorem B505483 : Blo 503794 505483 := bstep (se 1 (by rfl) ⟨379112, by rfl⟩ : syracuseStep 505483 = 758225) B758225
theorem B505495 : Blo 503794 505495 := bstep (se 1 (by rfl) ⟨379121, by rfl⟩ : syracuseStep 505495 = 758243) B758243
theorem B505515 : Blo 503794 505515 := bstep (se 1 (by rfl) ⟨379136, by rfl⟩ : syracuseStep 505515 = 758273) B758273
theorem B505527 : Blo 503794 505527 := bstep (se 1 (by rfl) ⟨379145, by rfl⟩ : syracuseStep 505527 = 758291) B758291
theorem B571063 : Blo 503794 571063 := bstep (se 1 (by rfl) ⟨428297, by rfl⟩ : syracuseStep 571063 = 856595) B856595
theorem B505547 : Blo 503794 505547 := bstep (se 1 (by rfl) ⟨379160, by rfl⟩ : syracuseStep 505547 = 758321) B758321
theorem B538327 : Blo 503794 538327 := bstep (se 1 (by rfl) ⟨403745, by rfl⟩ : syracuseStep 538327 = 807491) B807491
theorem B505559 : Blo 503794 505559 := bstep (se 1 (by rfl) ⟨379169, by rfl⟩ : syracuseStep 505559 = 758339) B758339
theorem B505579 : Blo 503794 505579 := bstep (se 1 (by rfl) ⟨379184, by rfl⟩ : syracuseStep 505579 = 758369) B758369
theorem B505591 : Blo 503794 505591 := bstep (se 1 (by rfl) ⟨379193, by rfl⟩ : syracuseStep 505591 = 758387) B758387
theorem B505611 : Blo 503794 505611 := bstep (se 1 (by rfl) ⟨379208, by rfl⟩ : syracuseStep 505611 = 758417) B758417
theorem B505623 : Blo 503794 505623 := bstep (se 1 (by rfl) ⟨379217, by rfl⟩ : syracuseStep 505623 = 758435) B758435
theorem B505643 : Blo 503794 505643 := bstep (se 1 (by rfl) ⟨379232, by rfl⟩ : syracuseStep 505643 = 758465) B758465
theorem B505655 : Blo 503794 505655 := bstep (se 1 (by rfl) ⟨379241, by rfl⟩ : syracuseStep 505655 = 758483) B758483
theorem B505675 : Blo 503794 505675 := bstep (se 1 (by rfl) ⟨379256, by rfl⟩ : syracuseStep 505675 = 758513) B758513
theorem B505687 : Blo 503794 505687 := bstep (se 1 (by rfl) ⟨379265, by rfl⟩ : syracuseStep 505687 = 758531) B758531
theorem B505707 : Blo 503794 505707 := bstep (se 1 (by rfl) ⟨379280, by rfl⟩ : syracuseStep 505707 = 758561) B758561
theorem B571243 : Blo 503794 571243 := bstep (se 1 (by rfl) ⟨428432, by rfl⟩ : syracuseStep 571243 = 856865) B856865
theorem B505719 : Blo 503794 505719 := bstep (se 1 (by rfl) ⟨379289, by rfl⟩ : syracuseStep 505719 = 758579) B758579
theorem B1816451 : Blo 503794 1816451 := bstep (se 1 (by rfl) ⟨1362338, by rfl⟩ : syracuseStep 1816451 = 2724677) B2724677
theorem B505739 : Blo 503794 505739 := bstep (se 1 (by rfl) ⟨379304, by rfl⟩ : syracuseStep 505739 = 758609) B758609
theorem B505751 : Blo 503794 505751 := bstep (se 1 (by rfl) ⟨379313, by rfl⟩ : syracuseStep 505751 = 758627) B758627
theorem B505771 : Blo 503794 505771 := bstep (se 1 (by rfl) ⟨379328, by rfl⟩ : syracuseStep 505771 = 758657) B758657
theorem B505783 : Blo 503794 505783 := bstep (se 1 (by rfl) ⟨379337, by rfl⟩ : syracuseStep 505783 = 758675) B758675
theorem B505803 : Blo 503794 505803 := bstep (se 1 (by rfl) ⟨379352, by rfl⟩ : syracuseStep 505803 = 758705) B758705
theorem B538583 : Blo 503794 538583 := bstep (se 1 (by rfl) ⟨403937, by rfl⟩ : syracuseStep 538583 = 807875) B807875
theorem B505815 : Blo 503794 505815 := bstep (se 1 (by rfl) ⟨379361, by rfl⟩ : syracuseStep 505815 = 758723) B758723
theorem B505835 : Blo 503794 505835 := bstep (se 1 (by rfl) ⟨379376, by rfl⟩ : syracuseStep 505835 = 758753) B758753
theorem B505847 : Blo 503794 505847 := bstep (se 1 (by rfl) ⟨379385, by rfl⟩ : syracuseStep 505847 = 758771) B758771
theorem B505867 : Blo 503794 505867 := bstep (se 1 (by rfl) ⟨379400, by rfl⟩ : syracuseStep 505867 = 758801) B758801
theorem B505879 : Blo 503794 505879 := bstep (se 1 (by rfl) ⟨379409, by rfl⟩ : syracuseStep 505879 = 758819) B758819
theorem B505899 : Blo 503794 505899 := bstep (se 1 (by rfl) ⟨379424, by rfl⟩ : syracuseStep 505899 = 758849) B758849
theorem B505911 : Blo 503794 505911 := bstep (se 1 (by rfl) ⟨379433, by rfl⟩ : syracuseStep 505911 = 758867) B758867
theorem B505931 : Blo 503794 505931 := bstep (se 1 (by rfl) ⟨379448, by rfl⟩ : syracuseStep 505931 = 758897) B758897
theorem B505943 : Blo 503794 505943 := bstep (se 1 (by rfl) ⟨379457, by rfl⟩ : syracuseStep 505943 = 758915) B758915
theorem B505963 : Blo 503794 505963 := bstep (se 1 (by rfl) ⟨379472, by rfl⟩ : syracuseStep 505963 = 758945) B758945
theorem B505975 : Blo 503794 505975 := bstep (se 1 (by rfl) ⟨379481, by rfl⟩ : syracuseStep 505975 = 758963) B758963
theorem B505995 : Blo 503794 505995 := bstep (se 1 (by rfl) ⟨379496, by rfl⟩ : syracuseStep 505995 = 758993) B758993
theorem B506007 : Blo 503794 506007 := bstep (se 1 (by rfl) ⟨379505, by rfl⟩ : syracuseStep 506007 = 759011) B759011
theorem B506027 : Blo 503794 506027 := bstep (se 1 (by rfl) ⟨379520, by rfl⟩ : syracuseStep 506027 = 759041) B759041
theorem B506039 : Blo 503794 506039 := bstep (se 1 (by rfl) ⟨379529, by rfl⟩ : syracuseStep 506039 = 759059) B759059
theorem B506059 : Blo 503794 506059 := bstep (se 1 (by rfl) ⟨379544, by rfl⟩ : syracuseStep 506059 = 759089) B759089
theorem B506071 : Blo 503794 506071 := bstep (se 1 (by rfl) ⟨379553, by rfl⟩ : syracuseStep 506071 = 759107) B759107
theorem B506091 : Blo 503794 506091 := bstep (se 1 (by rfl) ⟨379568, by rfl⟩ : syracuseStep 506091 = 759137) B759137
theorem B506103 : Blo 503794 506103 := bstep (se 1 (by rfl) ⟨379577, by rfl⟩ : syracuseStep 506103 = 759155) B759155
theorem B506123 : Blo 503794 506123 := bstep (se 1 (by rfl) ⟨379592, by rfl⟩ : syracuseStep 506123 = 759185) B759185
theorem B506135 : Blo 503794 506135 := bstep (se 1 (by rfl) ⟨379601, by rfl⟩ : syracuseStep 506135 = 759203) B759203
theorem B506155 : Blo 503794 506155 := bstep (se 1 (by rfl) ⟨379616, by rfl⟩ : syracuseStep 506155 = 759233) B759233
theorem B506167 : Blo 503794 506167 := bstep (se 1 (by rfl) ⟨379625, by rfl⟩ : syracuseStep 506167 = 759251) B759251
theorem B506187 : Blo 503794 506187 := bstep (se 1 (by rfl) ⟨379640, by rfl⟩ : syracuseStep 506187 = 759281) B759281
theorem B506199 : Blo 503794 506199 := bstep (se 1 (by rfl) ⟨379649, by rfl⟩ : syracuseStep 506199 = 759299) B759299
theorem B506219 : Blo 503794 506219 := bstep (se 1 (by rfl) ⟨379664, by rfl⟩ : syracuseStep 506219 = 759329) B759329
theorem B506231 : Blo 503794 506231 := bstep (se 1 (by rfl) ⟨379673, by rfl⟩ : syracuseStep 506231 = 759347) B759347
theorem B506251 : Blo 503794 506251 := bstep (se 1 (by rfl) ⟨379688, by rfl⟩ : syracuseStep 506251 = 759377) B759377
theorem B506263 : Blo 503794 506263 := bstep (se 1 (by rfl) ⟨379697, by rfl⟩ : syracuseStep 506263 = 759395) B759395
theorem B506283 : Blo 503794 506283 := bstep (se 1 (by rfl) ⟨379712, by rfl⟩ : syracuseStep 506283 = 759425) B759425
theorem B506295 : Blo 503794 506295 := bstep (se 1 (by rfl) ⟨379721, by rfl⟩ : syracuseStep 506295 = 759443) B759443
theorem B506315 : Blo 503794 506315 := bstep (se 1 (by rfl) ⟨379736, by rfl⟩ : syracuseStep 506315 = 759473) B759473
theorem B506327 : Blo 503794 506327 := bstep (se 1 (by rfl) ⟨379745, by rfl⟩ : syracuseStep 506327 = 759491) B759491
theorem B506347 : Blo 503794 506347 := bstep (se 1 (by rfl) ⟨379760, by rfl⟩ : syracuseStep 506347 = 759521) B759521
theorem B506359 : Blo 503794 506359 := bstep (se 1 (by rfl) ⟨379769, by rfl⟩ : syracuseStep 506359 = 759539) B759539
theorem B539147 : Blo 503794 539147 := bstep (se 1 (by rfl) ⟨404360, by rfl⟩ : syracuseStep 539147 = 808721) B808721
theorem B506379 : Blo 503794 506379 := bstep (se 1 (by rfl) ⟨379784, by rfl⟩ : syracuseStep 506379 = 759569) B759569
theorem B506391 : Blo 503794 506391 := bstep (se 1 (by rfl) ⟨379793, by rfl⟩ : syracuseStep 506391 = 759587) B759587
theorem B506411 : Blo 503794 506411 := bstep (se 1 (by rfl) ⟨379808, by rfl⟩ : syracuseStep 506411 = 759617) B759617
theorem B506423 : Blo 503794 506423 := bstep (se 1 (by rfl) ⟨379817, by rfl⟩ : syracuseStep 506423 = 759635) B759635
theorem B506443 : Blo 503794 506443 := bstep (se 1 (by rfl) ⟨379832, by rfl⟩ : syracuseStep 506443 = 759665) B759665
theorem B506455 : Blo 503794 506455 := bstep (se 1 (by rfl) ⟨379841, by rfl⟩ : syracuseStep 506455 = 759683) B759683
theorem B506475 : Blo 503794 506475 := bstep (se 1 (by rfl) ⟨379856, by rfl⟩ : syracuseStep 506475 = 759713) B759713
theorem B506487 : Blo 503794 506487 := bstep (se 1 (by rfl) ⟨379865, by rfl⟩ : syracuseStep 506487 = 759731) B759731
theorem B16366211 : Blo 503794 16366211 := bstep (se 1 (by rfl) ⟨12274658, by rfl⟩ : syracuseStep 16366211 = 24549317) B24549317
theorem B506507 : Blo 503794 506507 := bstep (se 1 (by rfl) ⟨379880, by rfl⟩ : syracuseStep 506507 = 759761) B759761
theorem B506519 : Blo 503794 506519 := bstep (se 1 (by rfl) ⟨379889, by rfl⟩ : syracuseStep 506519 = 759779) B759779
theorem B506539 : Blo 503794 506539 := bstep (se 1 (by rfl) ⟨379904, by rfl⟩ : syracuseStep 506539 = 759809) B759809
theorem B506551 : Blo 503794 506551 := bstep (se 1 (by rfl) ⟨379913, by rfl⟩ : syracuseStep 506551 = 759827) B759827
theorem B506571 : Blo 503794 506571 := bstep (se 1 (by rfl) ⟨379928, by rfl⟩ : syracuseStep 506571 = 759857) B759857
theorem B18430669 : Blo 503794 18430669 := bstep (se 3 (by rfl) ⟨3455750, by rfl⟩ : syracuseStep 18430669 = 6911501) B6911501
theorem B506583 : Blo 503794 506583 := bstep (se 1 (by rfl) ⟨379937, by rfl⟩ : syracuseStep 506583 = 759875) B759875
theorem B506603 : Blo 503794 506603 := bstep (se 1 (by rfl) ⟨379952, by rfl⟩ : syracuseStep 506603 = 759905) B759905
theorem B506615 : Blo 503794 506615 := bstep (se 1 (by rfl) ⟨379961, by rfl⟩ : syracuseStep 506615 = 759923) B759923
theorem B506635 : Blo 503794 506635 := bstep (se 1 (by rfl) ⟨379976, by rfl⟩ : syracuseStep 506635 = 759953) B759953
theorem B506647 : Blo 503794 506647 := bstep (se 1 (by rfl) ⟨379985, by rfl⟩ : syracuseStep 506647 = 759971) B759971
theorem B506667 : Blo 503794 506667 := bstep (se 1 (by rfl) ⟨380000, by rfl⟩ : syracuseStep 506667 = 760001) B760001
theorem B506679 : Blo 503794 506679 := bstep (se 1 (by rfl) ⟨380009, by rfl⟩ : syracuseStep 506679 = 760019) B760019
theorem B506699 : Blo 503794 506699 := bstep (se 1 (by rfl) ⟨380024, by rfl⟩ : syracuseStep 506699 = 760049) B760049
theorem B506711 : Blo 503794 506711 := bstep (se 1 (by rfl) ⟨380033, by rfl⟩ : syracuseStep 506711 = 760067) B760067
theorem B506731 : Blo 503794 506731 := bstep (se 1 (by rfl) ⟨380048, by rfl⟩ : syracuseStep 506731 = 760097) B760097
theorem B506743 : Blo 503794 506743 := bstep (se 1 (by rfl) ⟨380057, by rfl⟩ : syracuseStep 506743 = 760115) B760115
theorem B4307843 : Blo 503794 4307843 := bstep (se 1 (by rfl) ⟨3230882, by rfl⟩ : syracuseStep 4307843 = 6461765) B6461765
theorem B506763 : Blo 503794 506763 := bstep (se 1 (by rfl) ⟨380072, by rfl⟩ : syracuseStep 506763 = 760145) B760145
theorem B768919 : Blo 503794 768919 := bstep (se 1 (by rfl) ⟨576689, by rfl⟩ : syracuseStep 768919 = 1153379) B1153379
theorem B506775 : Blo 503794 506775 := bstep (se 1 (by rfl) ⟨380081, by rfl⟩ : syracuseStep 506775 = 760163) B760163
theorem B867223 : Blo 503794 867223 := bstep (se 1 (by rfl) ⟨650417, by rfl⟩ : syracuseStep 867223 = 1300835) B1300835
theorem B506795 : Blo 503794 506795 := bstep (se 1 (by rfl) ⟨380096, by rfl⟩ : syracuseStep 506795 = 760193) B760193
theorem B506807 : Blo 503794 506807 := bstep (se 1 (by rfl) ⟨380105, by rfl⟩ : syracuseStep 506807 = 760211) B760211
theorem B506827 : Blo 503794 506827 := bstep (se 1 (by rfl) ⟨380120, by rfl⟩ : syracuseStep 506827 = 760241) B760241
theorem B506839 : Blo 503794 506839 := bstep (se 1 (by rfl) ⟨380129, by rfl⟩ : syracuseStep 506839 = 760259) B760259
theorem B506859 : Blo 503794 506859 := bstep (se 1 (by rfl) ⟨380144, by rfl⟩ : syracuseStep 506859 = 760289) B760289
theorem B506871 : Blo 503794 506871 := bstep (se 1 (by rfl) ⟨380153, by rfl⟩ : syracuseStep 506871 = 760307) B760307
theorem B506891 : Blo 503794 506891 := bstep (se 1 (by rfl) ⟨380168, by rfl⟩ : syracuseStep 506891 = 760337) B760337
theorem B506903 : Blo 503794 506903 := bstep (se 1 (by rfl) ⟨380177, by rfl⟩ : syracuseStep 506903 = 760355) B760355
theorem B506923 : Blo 503794 506923 := bstep (se 1 (by rfl) ⟨380192, by rfl⟩ : syracuseStep 506923 = 760385) B760385
theorem B1457203 : Blo 503794 1457203 := bstep (se 1 (by rfl) ⟨1092902, by rfl⟩ : syracuseStep 1457203 = 2185805) B2185805
theorem B506935 : Blo 503794 506935 := bstep (se 1 (by rfl) ⟨380201, by rfl⟩ : syracuseStep 506935 = 760403) B760403
theorem B506955 : Blo 503794 506955 := bstep (se 1 (by rfl) ⟨380216, by rfl⟩ : syracuseStep 506955 = 760433) B760433
theorem B506967 : Blo 503794 506967 := bstep (se 1 (by rfl) ⟨380225, by rfl⟩ : syracuseStep 506967 = 760451) B760451
theorem B506987 : Blo 503794 506987 := bstep (se 1 (by rfl) ⟨380240, by rfl⟩ : syracuseStep 506987 = 760481) B760481
theorem B506999 : Blo 503794 506999 := bstep (se 1 (by rfl) ⟨380249, by rfl⟩ : syracuseStep 506999 = 760499) B760499
theorem B507019 : Blo 503794 507019 := bstep (se 1 (by rfl) ⟨380264, by rfl⟩ : syracuseStep 507019 = 760529) B760529
theorem B507031 : Blo 503794 507031 := bstep (se 1 (by rfl) ⟨380273, by rfl⟩ : syracuseStep 507031 = 760547) B760547
theorem B507051 : Blo 503794 507051 := bstep (se 1 (by rfl) ⟨380288, by rfl⟩ : syracuseStep 507051 = 760577) B760577
theorem B507063 : Blo 503794 507063 := bstep (se 1 (by rfl) ⟨380297, by rfl⟩ : syracuseStep 507063 = 760595) B760595
theorem B507083 : Blo 503794 507083 := bstep (se 1 (by rfl) ⟨380312, by rfl⟩ : syracuseStep 507083 = 760625) B760625
theorem B507095 : Blo 503794 507095 := bstep (se 1 (by rfl) ⟨380321, by rfl⟩ : syracuseStep 507095 = 760643) B760643
theorem B507115 : Blo 503794 507115 := bstep (se 1 (by rfl) ⟨380336, by rfl⟩ : syracuseStep 507115 = 760673) B760673
theorem B507127 : Blo 503794 507127 := bstep (se 1 (by rfl) ⟨380345, by rfl⟩ : syracuseStep 507127 = 760691) B760691
theorem B638219 : Blo 503794 638219 := bstep (se 1 (by rfl) ⟨478664, by rfl⟩ : syracuseStep 638219 = 957329) B957329
theorem B507147 : Blo 503794 507147 := bstep (se 1 (by rfl) ⟨380360, by rfl⟩ : syracuseStep 507147 = 760721) B760721
theorem B507159 : Blo 503794 507159 := bstep (se 1 (by rfl) ⟨380369, by rfl⟩ : syracuseStep 507159 = 760739) B760739
theorem B507179 : Blo 503794 507179 := bstep (se 1 (by rfl) ⟨380384, by rfl⟩ : syracuseStep 507179 = 760769) B760769
theorem B507191 : Blo 503794 507191 := bstep (se 1 (by rfl) ⟨380393, by rfl⟩ : syracuseStep 507191 = 760787) B760787
theorem B507211 : Blo 503794 507211 := bstep (se 1 (by rfl) ⟨380408, by rfl⟩ : syracuseStep 507211 = 760817) B760817
theorem B507223 : Blo 503794 507223 := bstep (se 1 (by rfl) ⟨380417, by rfl⟩ : syracuseStep 507223 = 760835) B760835
theorem B507243 : Blo 503794 507243 := bstep (se 1 (by rfl) ⟨380432, by rfl⟩ : syracuseStep 507243 = 760865) B760865
theorem B507255 : Blo 503794 507255 := bstep (se 1 (by rfl) ⟨380441, by rfl⟩ : syracuseStep 507255 = 760883) B760883
theorem B507275 : Blo 503794 507275 := bstep (se 1 (by rfl) ⟨380456, by rfl⟩ : syracuseStep 507275 = 760913) B760913
theorem B507287 : Blo 503794 507287 := bstep (se 1 (by rfl) ⟨380465, by rfl⟩ : syracuseStep 507287 = 760931) B760931
theorem B507307 : Blo 503794 507307 := bstep (se 1 (by rfl) ⟨380480, by rfl⟩ : syracuseStep 507307 = 760961) B760961
theorem B507319 : Blo 503794 507319 := bstep (se 1 (by rfl) ⟨380489, by rfl⟩ : syracuseStep 507319 = 760979) B760979
theorem B507339 : Blo 503794 507339 := bstep (se 1 (by rfl) ⟨380504, by rfl⟩ : syracuseStep 507339 = 761009) B761009
theorem B507351 : Blo 503794 507351 := bstep (se 1 (by rfl) ⟨380513, by rfl⟩ : syracuseStep 507351 = 761027) B761027
theorem B507371 : Blo 503794 507371 := bstep (se 1 (by rfl) ⟨380528, by rfl⟩ : syracuseStep 507371 = 761057) B761057
theorem B507383 : Blo 503794 507383 := bstep (se 1 (by rfl) ⟨380537, by rfl⟩ : syracuseStep 507383 = 761075) B761075
theorem B1916419 : Blo 503794 1916419 := bstep (se 1 (by rfl) ⟨1437314, by rfl⟩ : syracuseStep 1916419 = 2874629) B2874629
theorem B507403 : Blo 503794 507403 := bstep (se 1 (by rfl) ⟨380552, by rfl⟩ : syracuseStep 507403 = 761105) B761105
theorem B507415 : Blo 503794 507415 := bstep (se 1 (by rfl) ⟨380561, by rfl⟩ : syracuseStep 507415 = 761123) B761123
theorem B507435 : Blo 503794 507435 := bstep (se 1 (by rfl) ⟨380576, by rfl⟩ : syracuseStep 507435 = 761153) B761153
theorem B507447 : Blo 503794 507447 := bstep (se 1 (by rfl) ⟨380585, by rfl⟩ : syracuseStep 507447 = 761171) B761171
theorem B507467 : Blo 503794 507467 := bstep (se 1 (by rfl) ⟨380600, by rfl⟩ : syracuseStep 507467 = 761201) B761201
theorem B507479 : Blo 503794 507479 := bstep (se 1 (by rfl) ⟨380609, by rfl⟩ : syracuseStep 507479 = 761219) B761219
theorem B507499 : Blo 503794 507499 := bstep (se 1 (by rfl) ⟨380624, by rfl⟩ : syracuseStep 507499 = 761249) B761249
theorem B507511 : Blo 503794 507511 := bstep (se 1 (by rfl) ⟨380633, by rfl⟩ : syracuseStep 507511 = 761267) B761267
theorem B507531 : Blo 503794 507531 := bstep (se 1 (by rfl) ⟨380648, by rfl⟩ : syracuseStep 507531 = 761297) B761297
theorem B3882647 : Blo 503794 3882647 := bstep (se 1 (by rfl) ⟨2911985, by rfl⟩ : syracuseStep 3882647 = 5823971) B5823971
theorem B507543 : Blo 503794 507543 := bstep (se 1 (by rfl) ⟨380657, by rfl⟩ : syracuseStep 507543 = 761315) B761315
theorem B507563 : Blo 503794 507563 := bstep (se 1 (by rfl) ⟨380672, by rfl⟩ : syracuseStep 507563 = 761345) B761345
theorem B507575 : Blo 503794 507575 := bstep (se 1 (by rfl) ⟨380681, by rfl⟩ : syracuseStep 507575 = 761363) B761363
theorem B507595 : Blo 503794 507595 := bstep (se 1 (by rfl) ⟨380696, by rfl⟩ : syracuseStep 507595 = 761393) B761393
theorem B507607 : Blo 503794 507607 := bstep (se 1 (by rfl) ⟨380705, by rfl⟩ : syracuseStep 507607 = 761411) B761411
theorem B1621721 : Blo 503794 1621721 := bstep (se 2 (by rfl) ⟨608145, by rfl⟩ : syracuseStep 1621721 = 1216291) B1216291
theorem B507627 : Blo 503794 507627 := bstep (se 1 (by rfl) ⟨380720, by rfl⟩ : syracuseStep 507627 = 761441) B761441
theorem B507639 : Blo 503794 507639 := bstep (se 1 (by rfl) ⟨380729, by rfl⟩ : syracuseStep 507639 = 761459) B761459
theorem B507659 : Blo 503794 507659 := bstep (se 1 (by rfl) ⟨380744, by rfl⟩ : syracuseStep 507659 = 761489) B761489
theorem B507671 : Blo 503794 507671 := bstep (se 1 (by rfl) ⟨380753, by rfl⟩ : syracuseStep 507671 = 761507) B761507
theorem B507691 : Blo 503794 507691 := bstep (se 1 (by rfl) ⟨380768, by rfl⟩ : syracuseStep 507691 = 761537) B761537
theorem B1916723 : Blo 503794 1916723 := bstep (se 1 (by rfl) ⟨1437542, by rfl⟩ : syracuseStep 1916723 = 2875085) B2875085
theorem B507703 : Blo 503794 507703 := bstep (se 1 (by rfl) ⟨380777, by rfl⟩ : syracuseStep 507703 = 761555) B761555
theorem B507723 : Blo 503794 507723 := bstep (se 1 (by rfl) ⟨380792, by rfl⟩ : syracuseStep 507723 = 761585) B761585
theorem B507735 : Blo 503794 507735 := bstep (se 1 (by rfl) ⟨380801, by rfl⟩ : syracuseStep 507735 = 761603) B761603
theorem B18693989 : Blo 503794 18693989 := bstep (se 4 (by rfl) ⟨1752561, by rfl⟩ : syracuseStep 18693989 = 3505123) B3505123
theorem B507755 : Blo 503794 507755 := bstep (se 1 (by rfl) ⟨380816, by rfl⟩ : syracuseStep 507755 = 761633) B761633
theorem B507767 : Blo 503794 507767 := bstep (se 1 (by rfl) ⟨380825, by rfl⟩ : syracuseStep 507767 = 761651) B761651
theorem B507787 : Blo 503794 507787 := bstep (se 1 (by rfl) ⟨380840, by rfl⟩ : syracuseStep 507787 = 761681) B761681
theorem B540599 : Blo 503794 540599 := bstep (se 1 (by rfl) ⟨405449, by rfl⟩ : syracuseStep 540599 = 810899) B810899
theorem B638923 : Blo 503794 638923 := bstep (se 1 (by rfl) ⟨479192, by rfl⟩ : syracuseStep 638923 = 958385) B958385
theorem B3883139 : Blo 503794 3883139 := bstep (se 1 (by rfl) ⟨2912354, by rfl⟩ : syracuseStep 3883139 = 5824709) B5824709
theorem B639191 : Blo 503794 639191 := bstep (se 1 (by rfl) ⟨479393, by rfl⟩ : syracuseStep 639191 = 958787) B958787
theorem B1917377 : Blo 503794 1917377 := bstep (se 2 (by rfl) ⟨719016, by rfl⟩ : syracuseStep 1917377 = 1438033) B1438033
theorem B1229363 : Blo 503794 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B639895 : Blo 503794 639895 := bstep (se 1 (by rfl) ⟨479921, by rfl⟩ : syracuseStep 639895 = 959843) B959843
theorem B1623233 : Blo 503794 1623233 := bstep (se 2 (by rfl) ⟨608712, by rfl⟩ : syracuseStep 1623233 = 1217425) B1217425
theorem B1459421 : Blo 503794 1459421 := bstep (se 3 (by rfl) ⟨273641, by rfl⟩ : syracuseStep 1459421 = 547283) B547283
theorem B3655043 : Blo 503794 3655043 := bstep (se 1 (by rfl) ⟨2741282, by rfl⟩ : syracuseStep 3655043 = 5482565) B5482565
theorem B1754561 : Blo 503794 1754561 := bstep (se 2 (by rfl) ⟨657960, by rfl⟩ : syracuseStep 1754561 = 1315921) B1315921
theorem B575083 : Blo 503794 575083 := bstep (se 1 (by rfl) ⟨431312, by rfl⟩ : syracuseStep 575083 = 862625) B862625
theorem B1918637 : Blo 503794 1918637 := bstep (se 3 (by rfl) ⟨359744, by rfl⟩ : syracuseStep 1918637 = 719489) B719489
theorem B1918667 : Blo 503794 1918667 := bstep (se 1 (by rfl) ⟨1439000, by rfl⟩ : syracuseStep 1918667 = 2878001) B2878001
theorem B4310819 : Blo 503794 4310819 := bstep (se 1 (by rfl) ⟨3233114, by rfl⟩ : syracuseStep 4310819 = 6466229) B6466229
theorem B2312081 : Blo 503794 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B1919321 : Blo 503794 1919321 := bstep (se 2 (by rfl) ⟨719745, by rfl⟩ : syracuseStep 1919321 = 1439491) B1439491
theorem B5753267 : Blo 503794 5753267 := bstep (se 1 (by rfl) ⟨4314950, by rfl⟩ : syracuseStep 5753267 = 8629901) B8629901
theorem B641611 : Blo 503794 641611 := bstep (se 1 (by rfl) ⟨481208, by rfl⟩ : syracuseStep 641611 = 962417) B962417
theorem B1919639 : Blo 503794 1919639 := bstep (se 1 (by rfl) ⟨1439729, by rfl⟩ : syracuseStep 1919639 = 2879459) B2879459
theorem B1133657 : Blo 503794 1133657 := bstep (se 2 (by rfl) ⟨425121, by rfl⟩ : syracuseStep 1133657 = 850243) B850243
theorem B1133747 : Blo 503794 1133747 := bstep (se 1 (by rfl) ⟨850310, by rfl⟩ : syracuseStep 1133747 = 1700621) B1700621
theorem B1133783 : Blo 503794 1133783 := bstep (se 1 (by rfl) ⟨850337, by rfl⟩ : syracuseStep 1133783 = 1700675) B1700675
theorem B1920307 : Blo 503794 1920307 := bstep (se 1 (by rfl) ⟨1440230, by rfl⟩ : syracuseStep 1920307 = 2880461) B2880461
theorem B1625437 : Blo 503794 1625437 := bstep (se 3 (by rfl) ⟨304769, by rfl⟩ : syracuseStep 1625437 = 609539) B609539
theorem B1133963 : Blo 503794 1133963 := bstep (se 1 (by rfl) ⟨850472, by rfl⟩ : syracuseStep 1133963 = 1700945) B1700945
theorem B1134017 : Blo 503794 1134017 := bstep (se 2 (by rfl) ⟨425256, by rfl⟩ : syracuseStep 1134017 = 850513) B850513
theorem B642583 : Blo 503794 642583 := bstep (se 1 (by rfl) ⟨481937, by rfl⟩ : syracuseStep 642583 = 963875) B963875
theorem B609943 : Blo 503794 609943 := bstep (se 1 (by rfl) ⟨457457, by rfl⟩ : syracuseStep 609943 = 914915) B914915
theorem B1134233 : Blo 503794 1134233 := bstep (se 2 (by rfl) ⟨425337, by rfl⟩ : syracuseStep 1134233 = 850675) B850675
theorem B2870963 : Blo 503794 2870963 := bstep (se 1 (by rfl) ⟨2153222, by rfl⟩ : syracuseStep 2870963 = 4306445) B4306445
theorem B7786165 : Blo 503794 7786165 := bstep (se 5 (by rfl) ⟨364976, by rfl⟩ : syracuseStep 7786165 = 729953) B729953
theorem B1134323 : Blo 503794 1134323 := bstep (se 1 (by rfl) ⟨850742, by rfl⟩ : syracuseStep 1134323 = 1701485) B1701485
theorem B1134359 : Blo 503794 1134359 := bstep (se 1 (by rfl) ⟨850769, by rfl⟩ : syracuseStep 1134359 = 1701539) B1701539
theorem B5754725 : Blo 503794 5754725 := bstep (se 4 (by rfl) ⟨539505, by rfl⟩ : syracuseStep 5754725 = 1079011) B1079011
theorem B511915 : Blo 503794 511915 := bstep (se 1 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 511915 = 767873) B767873
theorem B1134539 : Blo 503794 1134539 := bstep (se 1 (by rfl) ⟨850904, by rfl⟩ : syracuseStep 1134539 = 1701809) B1701809
theorem B1134593 : Blo 503794 1134593 := bstep (se 2 (by rfl) ⟨425472, by rfl⟩ : syracuseStep 1134593 = 850945) B850945
theorem B1134809 : Blo 503794 1134809 := bstep (se 2 (by rfl) ⟨425553, by rfl⟩ : syracuseStep 1134809 = 851107) B851107
theorem B1167617 : Blo 503794 1167617 := bstep (se 2 (by rfl) ⟨437856, by rfl⟩ : syracuseStep 1167617 = 875713) B875713
theorem B1134899 : Blo 503794 1134899 := bstep (se 1 (by rfl) ⟨851174, by rfl⟩ : syracuseStep 1134899 = 1702349) B1702349
theorem B1134935 : Blo 503794 1134935 := bstep (se 1 (by rfl) ⟨851201, by rfl⟩ : syracuseStep 1134935 = 1702403) B1702403
theorem B1135115 : Blo 503794 1135115 := bstep (se 1 (by rfl) ⟨851336, by rfl⟩ : syracuseStep 1135115 = 1702673) B1702673
theorem B1921553 : Blo 503794 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B1823255 : Blo 503794 1823255 := bstep (se 1 (by rfl) ⟨1367441, by rfl⟩ : syracuseStep 1823255 = 2734883) B2734883
theorem B1135169 : Blo 503794 1135169 := bstep (se 2 (by rfl) ⟨425688, by rfl⟩ : syracuseStep 1135169 = 851377) B851377
theorem B971531 : Blo 503794 971531 := bstep (se 1 (by rfl) ⟨728648, by rfl⟩ : syracuseStep 971531 = 1457297) B1457297
theorem B1135385 : Blo 503794 1135385 := bstep (se 2 (by rfl) ⟨425769, by rfl⟩ : syracuseStep 1135385 = 851539) B851539
theorem B1135475 : Blo 503794 1135475 := bstep (se 1 (by rfl) ⟨851606, by rfl⟩ : syracuseStep 1135475 = 1703213) B1703213
theorem B1135511 : Blo 503794 1135511 := bstep (se 1 (by rfl) ⟨851633, by rfl⟩ : syracuseStep 1135511 = 1703267) B1703267
theorem B2053043 : Blo 503794 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B1135691 : Blo 503794 1135691 := bstep (se 1 (by rfl) ⟨851768, by rfl⟩ : syracuseStep 1135691 = 1703537) B1703537
theorem B2872421 : Blo 503794 2872421 := bstep (se 4 (by rfl) ⟨269289, by rfl⟩ : syracuseStep 2872421 = 538579) B538579
theorem B1135745 : Blo 503794 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B1299635 : Blo 503794 1299635 := bstep (se 1 (by rfl) ⟨974726, by rfl⟩ : syracuseStep 1299635 = 1949453) B1949453
theorem B1922251 : Blo 503794 1922251 := bstep (se 1 (by rfl) ⟨1441688, by rfl⟩ : syracuseStep 1922251 = 2883377) B2883377
theorem B1135961 : Blo 503794 1135961 := bstep (se 2 (by rfl) ⟨425985, by rfl⟩ : syracuseStep 1135961 = 851971) B851971
theorem B1136051 : Blo 503794 1136051 := bstep (se 1 (by rfl) ⟨852038, by rfl⟩ : syracuseStep 1136051 = 1704077) B1704077
theorem B2315713 : Blo 503794 2315713 := bstep (se 2 (by rfl) ⟨868392, by rfl⟩ : syracuseStep 2315713 = 1736785) B1736785
theorem B1136087 : Blo 503794 1136087 := bstep (se 1 (by rfl) ⟨852065, by rfl⟩ : syracuseStep 1136087 = 1704131) B1704131
theorem B1922525 : Blo 503794 1922525 := bstep (se 3 (by rfl) ⟨360473, by rfl⟩ : syracuseStep 1922525 = 720947) B720947
theorem B6477347 : Blo 503794 6477347 := bstep (se 1 (by rfl) ⟨4858010, by rfl⟩ : syracuseStep 6477347 = 9716021) B9716021
theorem B1136267 : Blo 503794 1136267 := bstep (se 1 (by rfl) ⟨852200, by rfl⟩ : syracuseStep 1136267 = 1704401) B1704401
theorem B2152129 : Blo 503794 2152129 := bstep (se 2 (by rfl) ⟨807048, by rfl⟩ : syracuseStep 2152129 = 1614097) B1614097
theorem B1136321 : Blo 503794 1136321 := bstep (se 2 (by rfl) ⟨426120, by rfl⟩ : syracuseStep 1136321 = 852241) B852241
theorem B1136537 : Blo 503794 1136537 := bstep (se 2 (by rfl) ⟨426201, by rfl⟩ : syracuseStep 1136537 = 852403) B852403
theorem B2054081 : Blo 503794 2054081 := bstep (se 2 (by rfl) ⟨770280, by rfl⟩ : syracuseStep 2054081 = 1540561) B1540561
theorem B10901465 : Blo 503794 10901465 := bstep (se 2 (by rfl) ⟨4088049, by rfl⟩ : syracuseStep 10901465 = 8176099) B8176099
theorem B3233753 : Blo 503794 3233753 := bstep (se 2 (by rfl) ⟨1212657, by rfl⟩ : syracuseStep 3233753 = 2425315) B2425315
theorem B1136627 : Blo 503794 1136627 := bstep (se 1 (by rfl) ⟨852470, by rfl⟩ : syracuseStep 1136627 = 1704941) B1704941
theorem B5199889 : Blo 503794 5199889 := bstep (se 2 (by rfl) ⟨1949958, by rfl⟩ : syracuseStep 5199889 = 3899917) B3899917
theorem B1136663 : Blo 503794 1136663 := bstep (se 1 (by rfl) ⟨852497, by rfl⟩ : syracuseStep 1136663 = 1704995) B1704995
theorem B546955 : Blo 503794 546955 := bstep (se 1 (by rfl) ⟨410216, by rfl⟩ : syracuseStep 546955 = 820433) B820433
theorem B1923223 : Blo 503794 1923223 := bstep (se 1 (by rfl) ⟨1442417, by rfl⟩ : syracuseStep 1923223 = 2884835) B2884835
theorem B1136843 : Blo 503794 1136843 := bstep (se 1 (by rfl) ⟨852632, by rfl⟩ : syracuseStep 1136843 = 1705265) B1705265
theorem B1136897 : Blo 503794 1136897 := bstep (se 2 (by rfl) ⟨426336, by rfl⟩ : syracuseStep 1136897 = 852673) B852673
theorem B2152727 : Blo 503794 2152727 := bstep (se 1 (by rfl) ⟨1614545, by rfl⟩ : syracuseStep 2152727 = 3229091) B3229091
theorem B1137113 : Blo 503794 1137113 := bstep (se 2 (by rfl) ⟨426417, by rfl⟩ : syracuseStep 1137113 = 852835) B852835
theorem B1137203 : Blo 503794 1137203 := bstep (se 1 (by rfl) ⟨852902, by rfl⟩ : syracuseStep 1137203 = 1705805) B1705805
theorem B1137239 : Blo 503794 1137239 := bstep (se 1 (by rfl) ⟨852929, by rfl⟩ : syracuseStep 1137239 = 1705859) B1705859
theorem B1137419 : Blo 503794 1137419 := bstep (se 1 (by rfl) ⟨853064, by rfl⟩ : syracuseStep 1137419 = 1706129) B1706129
theorem B1137473 : Blo 503794 1137473 := bstep (se 2 (by rfl) ⟨426552, by rfl⟩ : syracuseStep 1137473 = 853105) B853105
theorem B5561189 : Blo 503794 5561189 := bstep (se 4 (by rfl) ⟨521361, by rfl⟩ : syracuseStep 5561189 = 1042723) B1042723
theorem B1924013 : Blo 503794 1924013 := bstep (se 3 (by rfl) ⟨360752, by rfl⟩ : syracuseStep 1924013 = 721505) B721505
theorem B1727411 : Blo 503794 1727411 := bstep (se 1 (by rfl) ⟨1295558, by rfl⟩ : syracuseStep 1727411 = 2591117) B2591117
theorem B1137689 : Blo 503794 1137689 := bstep (se 2 (by rfl) ⟨426633, by rfl⟩ : syracuseStep 1137689 = 853267) B853267
theorem B1137779 : Blo 503794 1137779 := bstep (se 1 (by rfl) ⟨853334, by rfl⟩ : syracuseStep 1137779 = 1706669) B1706669
theorem B1137815 : Blo 503794 1137815 := bstep (se 1 (by rfl) ⟨853361, by rfl⟩ : syracuseStep 1137815 = 1706723) B1706723
theorem B1137995 : Blo 503794 1137995 := bstep (se 1 (by rfl) ⟨853496, by rfl⟩ : syracuseStep 1137995 = 1706993) B1706993
theorem B810329 : Blo 503794 810329 := bstep (se 2 (by rfl) ⟨303873, by rfl⟩ : syracuseStep 810329 = 607747) B607747
theorem B1138049 : Blo 503794 1138049 := bstep (se 2 (by rfl) ⟨426768, by rfl⟩ : syracuseStep 1138049 = 853537) B853537
theorem B908759 : Blo 503794 908759 := bstep (se 1 (by rfl) ⟨681569, by rfl⟩ : syracuseStep 908759 = 1363139) B1363139
theorem B908801 : Blo 503794 908801 := bstep (se 2 (by rfl) ⟨340800, by rfl⟩ : syracuseStep 908801 = 681601) B681601
theorem B3235393 : Blo 503794 3235393 := bstep (se 2 (by rfl) ⟨1213272, by rfl⟩ : syracuseStep 3235393 = 2426545) B2426545
theorem B2154059 : Blo 503794 2154059 := bstep (se 1 (by rfl) ⟨1615544, by rfl⟩ : syracuseStep 2154059 = 3231089) B3231089
theorem B1138265 : Blo 503794 1138265 := bstep (se 2 (by rfl) ⟨426849, by rfl⟩ : syracuseStep 1138265 = 853699) B853699
theorem B8347229 : Blo 503794 8347229 := bstep (se 3 (by rfl) ⟨1565105, by rfl⟩ : syracuseStep 8347229 = 3130211) B3130211
theorem B1138355 : Blo 503794 1138355 := bstep (se 1 (by rfl) ⟨853766, by rfl⟩ : syracuseStep 1138355 = 1707533) B1707533
theorem B1138391 : Blo 503794 1138391 := bstep (se 1 (by rfl) ⟨853793, by rfl⟩ : syracuseStep 1138391 = 1707587) B1707587
theorem B1138571 : Blo 503794 1138571 := bstep (se 1 (by rfl) ⟨853928, by rfl⟩ : syracuseStep 1138571 = 1707857) B1707857
theorem B1138625 : Blo 503794 1138625 := bstep (se 2 (by rfl) ⟨426984, by rfl⟩ : syracuseStep 1138625 = 853969) B853969
theorem B2056157 : Blo 503794 2056157 := bstep (se 3 (by rfl) ⟨385529, by rfl⟩ : syracuseStep 2056157 = 771059) B771059
theorem B1826819 : Blo 503794 1826819 := bstep (se 1 (by rfl) ⟨1370114, by rfl⟩ : syracuseStep 1826819 = 2740229) B2740229
theorem B1728587 : Blo 503794 1728587 := bstep (se 1 (by rfl) ⟨1296440, by rfl⟩ : syracuseStep 1728587 = 2592881) B2592881
theorem B2056337 : Blo 503794 2056337 := bstep (se 2 (by rfl) ⟨771126, by rfl⟩ : syracuseStep 2056337 = 1542253) B1542253
theorem B1138841 : Blo 503794 1138841 := bstep (se 2 (by rfl) ⟨427065, by rfl⟩ : syracuseStep 1138841 = 854131) B854131
theorem B1138931 : Blo 503794 1138931 := bstep (se 1 (by rfl) ⟨854198, by rfl⟩ : syracuseStep 1138931 = 1708397) B1708397
theorem B1138967 : Blo 503794 1138967 := bstep (se 1 (by rfl) ⟨854225, by rfl⟩ : syracuseStep 1138967 = 1708451) B1708451
theorem B1925441 : Blo 503794 1925441 := bstep (se 2 (by rfl) ⟨722040, by rfl⟩ : syracuseStep 1925441 = 1444081) B1444081
theorem B1139147 : Blo 503794 1139147 := bstep (se 1 (by rfl) ⟨854360, by rfl⟩ : syracuseStep 1139147 = 1708721) B1708721
theorem B1139201 : Blo 503794 1139201 := bstep (se 2 (by rfl) ⟨427200, by rfl⟩ : syracuseStep 1139201 = 854401) B854401
theorem B3465773 : Blo 503794 3465773 := bstep (se 3 (by rfl) ⟨649832, by rfl⟩ : syracuseStep 3465773 = 1299665) B1299665
theorem B3826277 : Blo 503794 3826277 := bstep (se 4 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 3826277 = 717427) B717427
theorem B2155187 : Blo 503794 2155187 := bstep (se 1 (by rfl) ⟨1616390, by rfl⟩ : syracuseStep 2155187 = 3232781) B3232781
theorem B44360405 : Blo 503794 44360405 := bstep (se 7 (by rfl) ⟨519848, by rfl⟩ : syracuseStep 44360405 = 1039697) B1039697
theorem B1172183 : Blo 503794 1172183 := bstep (se 1 (by rfl) ⟨879137, by rfl⟩ : syracuseStep 1172183 = 1758275) B1758275
theorem B1139417 : Blo 503794 1139417 := bstep (se 2 (by rfl) ⟨427281, by rfl⟩ : syracuseStep 1139417 = 854563) B854563
theorem B1139507 : Blo 503794 1139507 := bstep (se 1 (by rfl) ⟨854630, by rfl⟩ : syracuseStep 1139507 = 1709261) B1709261
theorem B1139543 : Blo 503794 1139543 := bstep (se 1 (by rfl) ⟨854657, by rfl⟩ : syracuseStep 1139543 = 1709315) B1709315
theorem B2909029 : Blo 503794 2909029 := bstep (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) B545443
theorem B910273 : Blo 503794 910273 := bstep (se 2 (by rfl) ⟨341352, by rfl⟩ : syracuseStep 910273 = 682705) B682705
theorem B1139723 : Blo 503794 1139723 := bstep (se 1 (by rfl) ⟨854792, by rfl⟩ : syracuseStep 1139723 = 1709585) B1709585
theorem B3236881 : Blo 503794 3236881 := bstep (se 2 (by rfl) ⟨1213830, by rfl⟩ : syracuseStep 3236881 = 2427661) B2427661
theorem B1139777 : Blo 503794 1139777 := bstep (se 2 (by rfl) ⟨427416, by rfl⟩ : syracuseStep 1139777 = 854833) B854833
theorem B3826763 : Blo 503794 3826763 := bstep (se 1 (by rfl) ⟨2870072, by rfl⟩ : syracuseStep 3826763 = 5740145) B5740145
theorem B9757847 : Blo 503794 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B3073241 : Blo 503794 3073241 := bstep (se 2 (by rfl) ⟨1152465, by rfl⟩ : syracuseStep 3073241 = 2304931) B2304931
theorem B976151 : Blo 503794 976151 := bstep (se 1 (by rfl) ⟨732113, by rfl⟩ : syracuseStep 976151 = 1464227) B1464227
theorem B1139993 : Blo 503794 1139993 := bstep (se 2 (by rfl) ⟨427497, by rfl⟩ : syracuseStep 1139993 = 854995) B854995
theorem B1140083 : Blo 503794 1140083 := bstep (se 1 (by rfl) ⟨855062, by rfl⟩ : syracuseStep 1140083 = 1710125) B1710125
theorem B1140119 : Blo 503794 1140119 := bstep (se 1 (by rfl) ⟨855089, by rfl⟩ : syracuseStep 1140119 = 1710179) B1710179
theorem B910835 : Blo 503794 910835 := bstep (se 1 (by rfl) ⟨683126, by rfl⟩ : syracuseStep 910835 = 1366253) B1366253
theorem B1730123 : Blo 503794 1730123 := bstep (se 1 (by rfl) ⟨1297592, by rfl⟩ : syracuseStep 1730123 = 2595185) B2595185
theorem B1140299 : Blo 503794 1140299 := bstep (se 1 (by rfl) ⟨855224, by rfl⟩ : syracuseStep 1140299 = 1710449) B1710449
theorem B1140353 : Blo 503794 1140353 := bstep (se 2 (by rfl) ⟨427632, by rfl⟩ : syracuseStep 1140353 = 855265) B855265
theorem B1926929 : Blo 503794 1926929 := bstep (se 2 (by rfl) ⟨722598, by rfl⟩ : syracuseStep 1926929 = 1445197) B1445197
theorem B1140569 : Blo 503794 1140569 := bstep (se 2 (by rfl) ⟨427713, by rfl⟩ : syracuseStep 1140569 = 855427) B855427
theorem B1140659 : Blo 503794 1140659 := bstep (se 1 (by rfl) ⟨855494, by rfl⟩ : syracuseStep 1140659 = 1710989) B1710989
theorem B1140695 : Blo 503794 1140695 := bstep (se 1 (by rfl) ⟨855521, by rfl⟩ : syracuseStep 1140695 = 1711043) B1711043
theorem B1140875 : Blo 503794 1140875 := bstep (se 1 (by rfl) ⟨855656, by rfl⟩ : syracuseStep 1140875 = 1711313) B1711313
theorem B3500183 : Blo 503794 3500183 := bstep (se 1 (by rfl) ⟨2625137, by rfl⟩ : syracuseStep 3500183 = 5250275) B5250275
theorem B911513 : Blo 503794 911513 := bstep (se 2 (by rfl) ⟨341817, by rfl⟩ : syracuseStep 911513 = 683635) B683635
theorem B1140929 : Blo 503794 1140929 := bstep (se 2 (by rfl) ⟨427848, by rfl⟩ : syracuseStep 1140929 = 855697) B855697
theorem B1927385 : Blo 503794 1927385 := bstep (se 2 (by rfl) ⟨722769, by rfl⟩ : syracuseStep 1927385 = 1445539) B1445539
theorem B1829251 : Blo 503794 1829251 := bstep (se 1 (by rfl) ⟨1371938, by rfl⟩ : syracuseStep 1829251 = 2743877) B2743877
theorem B1141145 : Blo 503794 1141145 := bstep (se 2 (by rfl) ⟨427929, by rfl⟩ : syracuseStep 1141145 = 855859) B855859
theorem B1927597 : Blo 503794 1927597 := bstep (se 3 (by rfl) ⟨361424, by rfl⟩ : syracuseStep 1927597 = 722849) B722849
theorem B2779609 : Blo 503794 2779609 := bstep (se 2 (by rfl) ⟨1042353, by rfl⟩ : syracuseStep 2779609 = 2084707) B2084707
theorem B1141235 : Blo 503794 1141235 := bstep (se 1 (by rfl) ⟨855926, by rfl⟩ : syracuseStep 1141235 = 1711853) B1711853
theorem B911873 : Blo 503794 911873 := bstep (se 2 (by rfl) ⟨341952, by rfl⟩ : syracuseStep 911873 = 683905) B683905
theorem B1141271 : Blo 503794 1141271 := bstep (se 1 (by rfl) ⟨855953, by rfl⟩ : syracuseStep 1141271 = 1711907) B1711907
theorem B2157101 : Blo 503794 2157101 := bstep (se 3 (by rfl) ⟨404456, by rfl⟩ : syracuseStep 2157101 = 808913) B808913
theorem B2058817 : Blo 503794 2058817 := bstep (se 2 (by rfl) ⟨772056, by rfl⟩ : syracuseStep 2058817 = 1544113) B1544113
theorem B1141451 : Blo 503794 1141451 := bstep (se 1 (by rfl) ⟨856088, by rfl⟩ : syracuseStep 1141451 = 1712177) B1712177
theorem B1927901 : Blo 503794 1927901 := bstep (se 3 (by rfl) ⟨361481, by rfl⟩ : syracuseStep 1927901 = 722963) B722963
theorem B1141505 : Blo 503794 1141505 := bstep (se 2 (by rfl) ⟨428064, by rfl⟩ : syracuseStep 1141505 = 856129) B856129
theorem B2878253 : Blo 503794 2878253 := bstep (se 3 (by rfl) ⟨539672, by rfl⟩ : syracuseStep 2878253 = 1079345) B1079345
theorem B1731379 : Blo 503794 1731379 := bstep (se 1 (by rfl) ⟨1298534, by rfl⟩ : syracuseStep 1731379 = 2597069) B2597069
theorem B1370945 : Blo 503794 1370945 := bstep (se 2 (by rfl) ⟨514104, by rfl⟩ : syracuseStep 1370945 = 1028209) B1028209
theorem B1076107 : Blo 503794 1076107 := bstep (se 1 (by rfl) ⟨807080, by rfl⟩ : syracuseStep 1076107 = 1614161) B1614161
theorem B1436609 : Blo 503794 1436609 := bstep (se 2 (by rfl) ⟨538728, by rfl⟩ : syracuseStep 1436609 = 1077457) B1077457
theorem B1141721 : Blo 503794 1141721 := bstep (se 2 (by rfl) ⟨428145, by rfl⟩ : syracuseStep 1141721 = 856291) B856291
theorem B1436723 : Blo 503794 1436723 := bstep (se 1 (by rfl) ⟨1077542, by rfl⟩ : syracuseStep 1436723 = 2155085) B2155085
theorem B1141811 : Blo 503794 1141811 := bstep (se 1 (by rfl) ⟨856358, by rfl⟩ : syracuseStep 1141811 = 1712717) B1712717
theorem B650315 : Blo 503794 650315 := bstep (se 1 (by rfl) ⟨487736, by rfl⟩ : syracuseStep 650315 = 975473) B975473
theorem B1141847 : Blo 503794 1141847 := bstep (se 1 (by rfl) ⟨856385, by rfl⟩ : syracuseStep 1141847 = 1712771) B1712771
theorem B2157785 : Blo 503794 2157785 := bstep (se 2 (by rfl) ⟨809169, by rfl⟩ : syracuseStep 2157785 = 1618339) B1618339
theorem B1142027 : Blo 503794 1142027 := bstep (se 1 (by rfl) ⟨856520, by rfl⟩ : syracuseStep 1142027 = 1713041) B1713041
theorem B1142081 : Blo 503794 1142081 := bstep (se 2 (by rfl) ⟨428280, by rfl⟩ : syracuseStep 1142081 = 856561) B856561
theorem B1142297 : Blo 503794 1142297 := bstep (se 2 (by rfl) ⟨428361, by rfl⟩ : syracuseStep 1142297 = 856723) B856723
theorem B1142387 : Blo 503794 1142387 := bstep (se 1 (by rfl) ⟨856790, by rfl⟩ : syracuseStep 1142387 = 1713581) B1713581
theorem B1142423 : Blo 503794 1142423 := bstep (se 1 (by rfl) ⟨856817, by rfl⟩ : syracuseStep 1142423 = 1713635) B1713635
theorem B1666777 : Blo 503794 1666777 := bstep (se 2 (by rfl) ⟨625041, by rfl⟩ : syracuseStep 1666777 = 1250083) B1250083
theorem B1077337 : Blo 503794 1077337 := bstep (se 2 (by rfl) ⟨404001, by rfl⟩ : syracuseStep 1077337 = 808003) B808003
theorem B3633245 : Blo 503794 3633245 := bstep (se 3 (by rfl) ⟨681233, by rfl⟩ : syracuseStep 3633245 = 1362467) B1362467
theorem B4878467 : Blo 503794 4878467 := bstep (se 1 (by rfl) ⟨3658850, by rfl⟩ : syracuseStep 4878467 = 7317701) B7317701
theorem B4944023 : Blo 503794 4944023 := bstep (se 1 (by rfl) ⟨3708017, by rfl⟩ : syracuseStep 4944023 = 7416035) B7416035
theorem B684235 : Blo 503794 684235 := bstep (se 1 (by rfl) ⟨513176, by rfl⟩ : syracuseStep 684235 = 1026353) B1026353
theorem B2191661 : Blo 503794 2191661 := bstep (se 3 (by rfl) ⟨410936, by rfl⟩ : syracuseStep 2191661 = 821873) B821873
theorem B6255197 : Blo 503794 6255197 := bstep (se 3 (by rfl) ⟨1172849, by rfl⟩ : syracuseStep 6255197 = 2345699) B2345699
theorem B2552471 : Blo 503794 2552471 := bstep (se 1 (by rfl) ⟨1914353, by rfl⟩ : syracuseStep 2552471 = 3828707) B3828707
theorem B717655 : Blo 503794 717655 := bstep (se 1 (by rfl) ⟨538241, by rfl⟩ : syracuseStep 717655 = 1076483) B1076483
theorem B2880643 : Blo 503794 2880643 := bstep (se 1 (by rfl) ⟨2160482, by rfl⟩ : syracuseStep 2880643 = 4320965) B4320965
theorem B685273 : Blo 503794 685273 := bstep (se 2 (by rfl) ⟨256977, by rfl⟩ : syracuseStep 685273 = 513955) B513955
theorem B4322605 : Blo 503794 4322605 := bstep (se 3 (by rfl) ⟨810488, by rfl⟩ : syracuseStep 4322605 = 1620977) B1620977
theorem B1701323 : Blo 503794 1701323 := bstep (se 1 (by rfl) ⟨1275992, by rfl⟩ : syracuseStep 1701323 = 2551985) B2551985
theorem B718475 : Blo 503794 718475 := bstep (se 1 (by rfl) ⟨538856, by rfl⟩ : syracuseStep 718475 = 1077713) B1077713
theorem B1701593 : Blo 503794 1701593 := bstep (se 2 (by rfl) ⟨638097, by rfl⟩ : syracuseStep 1701593 = 1276195) B1276195
theorem B149157773 : Blo 503794 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B1439639 : Blo 503794 1439639 := bstep (se 1 (by rfl) ⟨1079729, by rfl⟩ : syracuseStep 1439639 = 2159459) B2159459
theorem B1275851 : Blo 503794 1275851 := bstep (se 1 (by rfl) ⟨956888, by rfl⟩ : syracuseStep 1275851 = 1913777) B1913777
theorem B555031 : Blo 503794 555031 := bstep (se 1 (by rfl) ⟨416273, by rfl⟩ : syracuseStep 555031 = 832547) B832547
theorem B2881601 : Blo 503794 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B3832109 : Blo 503794 3832109 := bstep (se 3 (by rfl) ⟨718520, by rfl⟩ : syracuseStep 3832109 = 1437041) B1437041
theorem B1702295 : Blo 503794 1702295 := bstep (se 1 (by rfl) ⟨1276721, by rfl⟩ : syracuseStep 1702295 = 2553443) B2553443
theorem B4094509 : Blo 503794 4094509 := bstep (se 3 (by rfl) ⟨767720, by rfl⟩ : syracuseStep 4094509 = 1535441) B1535441
theorem B4323941 : Blo 503794 4323941 := bstep (se 4 (by rfl) ⟨405369, by rfl⟩ : syracuseStep 4323941 = 810739) B810739
theorem B1669835 : Blo 503794 1669835 := bstep (se 1 (by rfl) ⟨1252376, by rfl⟩ : syracuseStep 1669835 = 2504753) B2504753
theorem B850763 : Blo 503794 850763 := bstep (se 1 (by rfl) ⟨638072, by rfl⟩ : syracuseStep 850763 = 1276145) B1276145
theorem B1538909 : Blo 503794 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B1276823 : Blo 503794 1276823 := bstep (se 1 (by rfl) ⟨957617, by rfl⟩ : syracuseStep 1276823 = 1915235) B1915235
theorem B1702835 : Blo 503794 1702835 := bstep (se 1 (by rfl) ⟨1277126, by rfl⟩ : syracuseStep 1702835 = 2554253) B2554253
theorem B850891 : Blo 503794 850891 := bstep (se 1 (by rfl) ⟨638168, by rfl⟩ : syracuseStep 850891 = 1276337) B1276337
theorem B1080371 : Blo 503794 1080371 := bstep (se 1 (by rfl) ⟨810278, by rfl⟩ : syracuseStep 1080371 = 1620557) B1620557
theorem B851033 : Blo 503794 851033 := bstep (se 2 (by rfl) ⟨319137, by rfl⟩ : syracuseStep 851033 = 638275) B638275
theorem B1703105 : Blo 503794 1703105 := bstep (se 2 (by rfl) ⟨638664, by rfl⟩ : syracuseStep 1703105 = 1277329) B1277329
theorem B851161 : Blo 503794 851161 := bstep (se 2 (by rfl) ⟨319185, by rfl⟩ : syracuseStep 851161 = 638371) B638371
theorem B1211851 : Blo 503794 1211851 := bstep (se 1 (by rfl) ⟨908888, by rfl⟩ : syracuseStep 1211851 = 1817777) B1817777
theorem B2162123 : Blo 503794 2162123 := bstep (se 1 (by rfl) ⟨1621592, by rfl⟩ : syracuseStep 2162123 = 3243185) B3243185
theorem B720343 : Blo 503794 720343 := bstep (se 1 (by rfl) ⟨540257, by rfl⟩ : syracuseStep 720343 = 1080515) B1080515
theorem B1080857 : Blo 503794 1080857 := bstep (se 2 (by rfl) ⟨405321, by rfl⟩ : syracuseStep 1080857 = 810643) B810643
theorem B1277491 : Blo 503794 1277491 := bstep (se 1 (by rfl) ⟨958118, by rfl⟩ : syracuseStep 1277491 = 1916237) B1916237
theorem B1277633 : Blo 503794 1277633 := bstep (se 2 (by rfl) ⟨479112, by rfl⟩ : syracuseStep 1277633 = 958225) B958225
theorem B1703645 : Blo 503794 1703645 := bstep (se 3 (by rfl) ⟨319433, by rfl⟩ : syracuseStep 1703645 = 638867) B638867
theorem B851735 : Blo 503794 851735 := bstep (se 1 (by rfl) ⟨638801, by rfl⟩ : syracuseStep 851735 = 1277603) B1277603
theorem B1736471 : Blo 503794 1736471 := bstep (se 1 (by rfl) ⟨1302353, by rfl⟩ : syracuseStep 1736471 = 2604707) B2604707
theorem B851863 : Blo 503794 851863 := bstep (se 1 (by rfl) ⟨638897, by rfl⟩ : syracuseStep 851863 = 1277795) B1277795
theorem B2588759 : Blo 503794 2588759 := bstep (se 1 (by rfl) ⟨1941569, by rfl⟩ : syracuseStep 2588759 = 3883139) B3883139
theorem B1704023 : Blo 503794 1704023 := bstep (se 1 (by rfl) ⟨1278017, by rfl⟩ : syracuseStep 1704023 = 2556035) B2556035
theorem B2162807 : Blo 503794 2162807 := bstep (se 1 (by rfl) ⟨1622105, by rfl⟩ : syracuseStep 2162807 = 3244211) B3244211
theorem B1278251 : Blo 503794 1278251 := bstep (se 1 (by rfl) ⟨958688, by rfl⟩ : syracuseStep 1278251 = 1917377) B1917377
theorem B819575 : Blo 503794 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B1704509 : Blo 503794 1704509 := bstep (se 3 (by rfl) ⟨319595, by rfl⟩ : syracuseStep 1704509 = 639191) B639191
theorem B852599 : Blo 503794 852599 := bstep (se 1 (by rfl) ⟨639449, by rfl⟩ : syracuseStep 852599 = 1278899) B1278899
theorem B2917093 : Blo 503794 2917093 := bstep (se 4 (by rfl) ⟨273477, by rfl⟩ : syracuseStep 2917093 = 546955) B546955
theorem B1082155 : Blo 503794 1082155 := bstep (se 1 (by rfl) ⟨811616, by rfl⟩ : syracuseStep 1082155 = 1623233) B1623233
theorem B853051 : Blo 503794 853051 := bstep (se 1 (by rfl) ⟨639788, by rfl⟩ : syracuseStep 853051 = 1279577) B1279577
theorem B1279091 : Blo 503794 1279091 := bstep (se 1 (by rfl) ⟨959318, by rfl⟩ : syracuseStep 1279091 = 1918637) B1918637
theorem B1279111 : Blo 503794 1279111 := bstep (se 1 (by rfl) ⟨959333, by rfl⟩ : syracuseStep 1279111 = 1918667) B1918667
theorem B853193 : Blo 503794 853193 := bstep (se 2 (by rfl) ⟨319947, by rfl⟩ : syracuseStep 853193 = 639895) B639895
theorem B1213697 : Blo 503794 1213697 := bstep (se 2 (by rfl) ⟨455136, by rfl⟩ : syracuseStep 1213697 = 910273) B910273
theorem B1541387 : Blo 503794 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B2557331 : Blo 503794 2557331 := bstep (se 1 (by rfl) ⟨1917998, by rfl⟩ : syracuseStep 2557331 = 3835997) B3835997
theorem B1279385 : Blo 503794 1279385 := bstep (se 2 (by rfl) ⟨479769, by rfl⟩ : syracuseStep 1279385 = 959539) B959539
theorem B2885017 : Blo 503794 2885017 := bstep (se 2 (by rfl) ⟨1081881, by rfl⟩ : syracuseStep 2885017 = 2163763) B2163763
theorem B1443329 : Blo 503794 1443329 := bstep (se 2 (by rfl) ⟨541248, by rfl⟩ : syracuseStep 1443329 = 1082497) B1082497
theorem B1279547 : Blo 503794 1279547 := bstep (se 1 (by rfl) ⟨959660, by rfl⟩ : syracuseStep 1279547 = 1919321) B1919321
theorem B4326979 : Blo 503794 4326979 := bstep (se 1 (by rfl) ⟨3245234, by rfl⟩ : syracuseStep 4326979 = 6490469) B6490469
theorem B3835511 : Blo 503794 3835511 := bstep (se 1 (by rfl) ⟨2876633, by rfl⟩ : syracuseStep 3835511 = 5753267) B5753267
theorem B1279759 : Blo 503794 1279759 := bstep (se 1 (by rfl) ⟨959819, by rfl⟩ : syracuseStep 1279759 = 1919639) B1919639
theorem B853895 : Blo 503794 853895 := bstep (se 1 (by rfl) ⟨640421, by rfl⟩ : syracuseStep 853895 = 1280843) B1280843
theorem B1705913 : Blo 503794 1705913 := bstep (se 2 (by rfl) ⟨639717, by rfl⟩ : syracuseStep 1705913 = 1279435) B1279435
theorem B722935 : Blo 503794 722935 := bstep (se 1 (by rfl) ⟨542201, by rfl⟩ : syracuseStep 722935 = 1084403) B1084403
theorem B1280033 : Blo 503794 1280033 := bstep (se 2 (by rfl) ⟨480012, by rfl⟩ : syracuseStep 1280033 = 960025) B960025
theorem B755771 : Blo 503794 755771 := bstep (se 1 (by rfl) ⟨566828, by rfl⟩ : syracuseStep 755771 = 1133657) B1133657
theorem B1443899 : Blo 503794 1443899 := bstep (se 1 (by rfl) ⟨1082924, by rfl⟩ : syracuseStep 1443899 = 2165849) B2165849
theorem B755831 : Blo 503794 755831 := bstep (se 1 (by rfl) ⟨566873, by rfl⟩ : syracuseStep 755831 = 1133747) B1133747
theorem B755855 : Blo 503794 755855 := bstep (se 1 (by rfl) ⟨566891, by rfl⟩ : syracuseStep 755855 = 1133783) B1133783
theorem B755897 : Blo 503794 755897 := bstep (se 2 (by rfl) ⟨283461, by rfl⟩ : syracuseStep 755897 = 566923) B566923
theorem B755975 : Blo 503794 755975 := bstep (se 1 (by rfl) ⟨566981, by rfl⟩ : syracuseStep 755975 = 1133963) B1133963
theorem B756011 : Blo 503794 756011 := bstep (se 1 (by rfl) ⟨567008, by rfl⟩ : syracuseStep 756011 = 1134017) B1134017
theorem B1444139 : Blo 503794 1444139 := bstep (se 1 (by rfl) ⟨1083104, by rfl⟩ : syracuseStep 1444139 = 2166209) B2166209
theorem B756041 : Blo 503794 756041 := bstep (se 2 (by rfl) ⟨283515, by rfl⟩ : syracuseStep 756041 = 567031) B567031
theorem B756155 : Blo 503794 756155 := bstep (se 1 (by rfl) ⟨567116, by rfl⟩ : syracuseStep 756155 = 1134233) B1134233
theorem B756215 : Blo 503794 756215 := bstep (se 1 (by rfl) ⟨567161, by rfl⟩ : syracuseStep 756215 = 1134323) B1134323
theorem B1706507 : Blo 503794 1706507 := bstep (se 1 (by rfl) ⟨1279880, by rfl⟩ : syracuseStep 1706507 = 2559761) B2559761
theorem B756239 : Blo 503794 756239 := bstep (se 1 (by rfl) ⟨567179, by rfl⟩ : syracuseStep 756239 = 1134359) B1134359
theorem B854543 : Blo 503794 854543 := bstep (se 1 (by rfl) ⟨640907, by rfl⟩ : syracuseStep 854543 = 1281815) B1281815
theorem B756281 : Blo 503794 756281 := bstep (se 2 (by rfl) ⟨283605, by rfl⟩ : syracuseStep 756281 = 567211) B567211
theorem B3836483 : Blo 503794 3836483 := bstep (se 1 (by rfl) ⟨2877362, by rfl⟩ : syracuseStep 3836483 = 5754725) B5754725
theorem B1706615 : Blo 503794 1706615 := bstep (se 1 (by rfl) ⟨1279961, by rfl⟩ : syracuseStep 1706615 = 2559923) B2559923
theorem B756359 : Blo 503794 756359 := bstep (se 1 (by rfl) ⟨567269, by rfl⟩ : syracuseStep 756359 = 1134539) B1134539
theorem B756395 : Blo 503794 756395 := bstep (se 1 (by rfl) ⟨567296, by rfl⟩ : syracuseStep 756395 = 1134593) B1134593
theorem B756425 : Blo 503794 756425 := bstep (se 2 (by rfl) ⟨283659, by rfl⟩ : syracuseStep 756425 = 567319) B567319
theorem B756539 : Blo 503794 756539 := bstep (se 1 (by rfl) ⟨567404, by rfl⟩ : syracuseStep 756539 = 1134809) B1134809
theorem B756599 : Blo 503794 756599 := bstep (se 1 (by rfl) ⟨567449, by rfl⟩ : syracuseStep 756599 = 1134899) B1134899
theorem B756623 : Blo 503794 756623 := bstep (se 1 (by rfl) ⟨567467, by rfl⟩ : syracuseStep 756623 = 1134935) B1134935
theorem B756665 : Blo 503794 756665 := bstep (se 2 (by rfl) ⟨283749, by rfl⟩ : syracuseStep 756665 = 567499) B567499
theorem B756743 : Blo 503794 756743 := bstep (se 1 (by rfl) ⟨567557, by rfl⟩ : syracuseStep 756743 = 1135115) B1135115
theorem B1281035 : Blo 503794 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B1215503 : Blo 503794 1215503 := bstep (se 1 (by rfl) ⟨911627, by rfl⟩ : syracuseStep 1215503 = 1823255) B1823255
theorem B756779 : Blo 503794 756779 := bstep (se 1 (by rfl) ⟨567584, by rfl⟩ : syracuseStep 756779 = 1135169) B1135169
theorem B855083 : Blo 503794 855083 := bstep (se 1 (by rfl) ⟨641312, by rfl⟩ : syracuseStep 855083 = 1282625) B1282625
theorem B756809 : Blo 503794 756809 := bstep (se 2 (by rfl) ⟨283803, by rfl⟩ : syracuseStep 756809 = 567607) B567607
theorem B756923 : Blo 503794 756923 := bstep (se 1 (by rfl) ⟨567692, by rfl⟩ : syracuseStep 756923 = 1135385) B1135385
theorem B1707209 : Blo 503794 1707209 := bstep (se 2 (by rfl) ⟨640203, by rfl⟩ : syracuseStep 1707209 = 1280407) B1280407
theorem B756983 : Blo 503794 756983 := bstep (se 1 (by rfl) ⟨567737, by rfl⟩ : syracuseStep 756983 = 1135475) B1135475
theorem B757007 : Blo 503794 757007 := bstep (se 1 (by rfl) ⟨567755, by rfl⟩ : syracuseStep 757007 = 1135511) B1135511
theorem B3706145 : Blo 503794 3706145 := bstep (se 2 (by rfl) ⟨1389804, by rfl⟩ : syracuseStep 3706145 = 2779609) B2779609
theorem B757049 : Blo 503794 757049 := bstep (se 2 (by rfl) ⟨283893, by rfl⟩ : syracuseStep 757049 = 567787) B567787
theorem B2887001 : Blo 503794 2887001 := bstep (se 2 (by rfl) ⟨1082625, by rfl⟩ : syracuseStep 2887001 = 2165251) B2165251
theorem B757127 : Blo 503794 757127 := bstep (se 1 (by rfl) ⟨567845, by rfl⟩ : syracuseStep 757127 = 1135691) B1135691
theorem B757163 : Blo 503794 757163 := bstep (se 1 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 757163 = 1135745) B1135745
theorem B855481 : Blo 503794 855481 := bstep (se 2 (by rfl) ⟨320805, by rfl⟩ : syracuseStep 855481 = 641611) B641611
theorem B757193 : Blo 503794 757193 := bstep (se 2 (by rfl) ⟨283947, by rfl⟩ : syracuseStep 757193 = 567895) B567895
theorem B4328963 : Blo 503794 4328963 := bstep (se 1 (by rfl) ⟨3246722, by rfl⟩ : syracuseStep 4328963 = 6493445) B6493445
theorem B757307 : Blo 503794 757307 := bstep (se 1 (by rfl) ⟨567980, by rfl⟩ : syracuseStep 757307 = 1135961) B1135961
theorem B757367 : Blo 503794 757367 := bstep (se 1 (by rfl) ⟨568025, by rfl⟩ : syracuseStep 757367 = 1136051) B1136051
theorem B757391 : Blo 503794 757391 := bstep (se 1 (by rfl) ⟨568043, by rfl⟩ : syracuseStep 757391 = 1136087) B1136087
theorem B1281683 : Blo 503794 1281683 := bstep (se 1 (by rfl) ⟨961262, by rfl⟩ : syracuseStep 1281683 = 1922525) B1922525
theorem B757433 : Blo 503794 757433 := bstep (se 2 (by rfl) ⟨284037, by rfl⟩ : syracuseStep 757433 = 568075) B568075
theorem B757511 : Blo 503794 757511 := bstep (se 1 (by rfl) ⟨568133, by rfl⟩ : syracuseStep 757511 = 1136267) B1136267
theorem B757547 : Blo 503794 757547 := bstep (se 1 (by rfl) ⟨568160, by rfl⟩ : syracuseStep 757547 = 1136321) B1136321
theorem B757577 : Blo 503794 757577 := bstep (se 2 (by rfl) ⟨284091, by rfl⟩ : syracuseStep 757577 = 568183) B568183
theorem B2461529 : Blo 503794 2461529 := bstep (se 2 (by rfl) ⟨923073, by rfl⟩ : syracuseStep 2461529 = 1846147) B1846147
theorem B1707911 : Blo 503794 1707911 := bstep (se 1 (by rfl) ⟨1280933, by rfl⟩ : syracuseStep 1707911 = 2561867) B2561867
theorem B1281977 : Blo 503794 1281977 := bstep (se 2 (by rfl) ⟨480741, by rfl⟩ : syracuseStep 1281977 = 961483) B961483
theorem B757691 : Blo 503794 757691 := bstep (se 1 (by rfl) ⟨568268, by rfl⟩ : syracuseStep 757691 = 1136537) B1136537
theorem B757751 : Blo 503794 757751 := bstep (se 1 (by rfl) ⟨568313, by rfl⟩ : syracuseStep 757751 = 1136627) B1136627
theorem B757775 : Blo 503794 757775 := bstep (se 1 (by rfl) ⟨568331, by rfl⟩ : syracuseStep 757775 = 1136663) B1136663
theorem B3084331 : Blo 503794 3084331 := bstep (se 1 (by rfl) ⟨2313248, by rfl⟩ : syracuseStep 3084331 = 4626497) B4626497
theorem B757817 : Blo 503794 757817 := bstep (se 2 (by rfl) ⟨284181, by rfl⟩ : syracuseStep 757817 = 568363) B568363
theorem B856183 : Blo 503794 856183 := bstep (se 1 (by rfl) ⟨642137, by rfl⟩ : syracuseStep 856183 = 1284275) B1284275
theorem B757895 : Blo 503794 757895 := bstep (se 1 (by rfl) ⟨568421, by rfl⟩ : syracuseStep 757895 = 1136843) B1136843
theorem B757931 : Blo 503794 757931 := bstep (se 1 (by rfl) ⟨568448, by rfl⟩ : syracuseStep 757931 = 1136897) B1136897
theorem B757961 : Blo 503794 757961 := bstep (se 2 (by rfl) ⟨284235, by rfl⟩ : syracuseStep 757961 = 568471) B568471
theorem B23433461 : Blo 503794 23433461 := bstep (se 5 (by rfl) ⟨1098443, by rfl⟩ : syracuseStep 23433461 = 2196887) B2196887
theorem B1708289 : Blo 503794 1708289 := bstep (se 2 (by rfl) ⟨640608, by rfl⟩ : syracuseStep 1708289 = 1281217) B1281217
theorem B758075 : Blo 503794 758075 := bstep (se 1 (by rfl) ⟨568556, by rfl⟩ : syracuseStep 758075 = 1137113) B1137113
theorem B856379 : Blo 503794 856379 := bstep (se 1 (by rfl) ⟨642284, by rfl⟩ : syracuseStep 856379 = 1284569) B1284569
theorem B758135 : Blo 503794 758135 := bstep (se 1 (by rfl) ⟨568601, by rfl⟩ : syracuseStep 758135 = 1137203) B1137203
theorem B758159 : Blo 503794 758159 := bstep (se 1 (by rfl) ⟨568619, by rfl⟩ : syracuseStep 758159 = 1137239) B1137239
theorem B2560409 : Blo 503794 2560409 := bstep (se 2 (by rfl) ⟨960153, by rfl⟩ : syracuseStep 2560409 = 1920307) B1920307
theorem B758201 : Blo 503794 758201 := bstep (se 2 (by rfl) ⟨284325, by rfl⟩ : syracuseStep 758201 = 568651) B568651
theorem B2167249 : Blo 503794 2167249 := bstep (se 2 (by rfl) ⟨812718, by rfl⟩ : syracuseStep 2167249 = 1625437) B1625437
theorem B3281411 : Blo 503794 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B758279 : Blo 503794 758279 := bstep (se 1 (by rfl) ⟨568709, by rfl⟩ : syracuseStep 758279 = 1137419) B1137419
theorem B758315 : Blo 503794 758315 := bstep (se 1 (by rfl) ⟨568736, by rfl⟩ : syracuseStep 758315 = 1137473) B1137473
theorem B2429507 : Blo 503794 2429507 := bstep (se 1 (by rfl) ⟨1822130, by rfl⟩ : syracuseStep 2429507 = 3644261) B3644261
theorem B3707459 : Blo 503794 3707459 := bstep (se 1 (by rfl) ⟨2780594, by rfl⟩ : syracuseStep 3707459 = 5561189) B5561189
theorem B758345 : Blo 503794 758345 := bstep (se 2 (by rfl) ⟨284379, by rfl⟩ : syracuseStep 758345 = 568759) B568759
theorem B1282675 : Blo 503794 1282675 := bstep (se 1 (by rfl) ⟨962006, by rfl⟩ : syracuseStep 1282675 = 1924013) B1924013
theorem B758459 : Blo 503794 758459 := bstep (se 1 (by rfl) ⟨568844, by rfl⟩ : syracuseStep 758459 = 1137689) B1137689
theorem B856777 : Blo 503794 856777 := bstep (se 2 (by rfl) ⟨321291, by rfl⟩ : syracuseStep 856777 = 642583) B642583
theorem B758519 : Blo 503794 758519 := bstep (se 1 (by rfl) ⟨568889, by rfl⟩ : syracuseStep 758519 = 1137779) B1137779
theorem B1282817 : Blo 503794 1282817 := bstep (se 2 (by rfl) ⟨481056, by rfl⟩ : syracuseStep 1282817 = 962113) B962113
theorem B758543 : Blo 503794 758543 := bstep (se 1 (by rfl) ⟨568907, by rfl⟩ : syracuseStep 758543 = 1137815) B1137815
theorem B758585 : Blo 503794 758585 := bstep (se 2 (by rfl) ⟨284469, by rfl⟩ : syracuseStep 758585 = 568939) B568939
theorem B758663 : Blo 503794 758663 := bstep (se 1 (by rfl) ⟨568997, by rfl⟩ : syracuseStep 758663 = 1137995) B1137995
theorem B758699 : Blo 503794 758699 := bstep (se 1 (by rfl) ⟨569024, by rfl⟩ : syracuseStep 758699 = 1138049) B1138049
theorem B758729 : Blo 503794 758729 := bstep (se 2 (by rfl) ⟨284523, by rfl⟩ : syracuseStep 758729 = 569047) B569047
theorem B1709099 : Blo 503794 1709099 := bstep (se 1 (by rfl) ⟨1281824, by rfl⟩ : syracuseStep 1709099 = 2563649) B2563649
theorem B758843 : Blo 503794 758843 := bstep (se 1 (by rfl) ⟨569132, by rfl⟩ : syracuseStep 758843 = 1138265) B1138265
theorem B758903 : Blo 503794 758903 := bstep (se 1 (by rfl) ⟨569177, by rfl⟩ : syracuseStep 758903 = 1138355) B1138355
theorem B758927 : Blo 503794 758927 := bstep (se 1 (by rfl) ⟨569195, by rfl⟩ : syracuseStep 758927 = 1138391) B1138391
theorem B758969 : Blo 503794 758969 := bstep (se 2 (by rfl) ⟨284613, by rfl⟩ : syracuseStep 758969 = 569227) B569227
theorem B1283273 : Blo 503794 1283273 := bstep (se 2 (by rfl) ⟨481227, by rfl⟩ : syracuseStep 1283273 = 962455) B962455
theorem B759047 : Blo 503794 759047 := bstep (se 1 (by rfl) ⟨569285, by rfl⟩ : syracuseStep 759047 = 1138571) B1138571
theorem B759083 : Blo 503794 759083 := bstep (se 1 (by rfl) ⟨569312, by rfl⟩ : syracuseStep 759083 = 1138625) B1138625
theorem B759113 : Blo 503794 759113 := bstep (se 2 (by rfl) ⟨284667, by rfl⟩ : syracuseStep 759113 = 569335) B569335
theorem B1217879 : Blo 503794 1217879 := bstep (se 1 (by rfl) ⟨913409, by rfl⟩ : syracuseStep 1217879 = 1826819) B1826819
theorem B1250707 : Blo 503794 1250707 := bstep (se 1 (by rfl) ⟨938030, by rfl⟩ : syracuseStep 1250707 = 1876061) B1876061
theorem B759227 : Blo 503794 759227 := bstep (se 1 (by rfl) ⟨569420, by rfl⟩ : syracuseStep 759227 = 1138841) B1138841
theorem B759287 : Blo 503794 759287 := bstep (se 1 (by rfl) ⟨569465, by rfl⟩ : syracuseStep 759287 = 1138931) B1138931
theorem B759311 : Blo 503794 759311 := bstep (se 1 (by rfl) ⟨569483, by rfl⟩ : syracuseStep 759311 = 1138967) B1138967
theorem B1283627 : Blo 503794 1283627 := bstep (se 1 (by rfl) ⟨962720, by rfl⟩ : syracuseStep 1283627 = 1925441) B1925441
theorem B759353 : Blo 503794 759353 := bstep (se 2 (by rfl) ⟨284757, by rfl⟩ : syracuseStep 759353 = 569515) B569515
theorem B759431 : Blo 503794 759431 := bstep (se 1 (by rfl) ⟨569573, by rfl⟩ : syracuseStep 759431 = 1139147) B1139147
theorem B759467 : Blo 503794 759467 := bstep (se 1 (by rfl) ⟨569600, by rfl⟩ : syracuseStep 759467 = 1139201) B1139201
theorem B759497 : Blo 503794 759497 := bstep (se 2 (by rfl) ⟨284811, by rfl⟩ : syracuseStep 759497 = 569623) B569623
theorem B759611 : Blo 503794 759611 := bstep (se 1 (by rfl) ⟨569708, by rfl⟩ : syracuseStep 759611 = 1139417) B1139417
theorem B4331353 : Blo 503794 4331353 := bstep (se 2 (by rfl) ⟨1624257, by rfl⟩ : syracuseStep 4331353 = 3248515) B3248515
theorem B759671 : Blo 503794 759671 := bstep (se 1 (by rfl) ⟨569753, by rfl⟩ : syracuseStep 759671 = 1139507) B1139507
theorem B759695 : Blo 503794 759695 := bstep (se 1 (by rfl) ⟨569771, by rfl⟩ : syracuseStep 759695 = 1139543) B1139543
theorem B759737 : Blo 503794 759737 := bstep (se 2 (by rfl) ⟨284901, by rfl⟩ : syracuseStep 759737 = 569803) B569803
theorem B759815 : Blo 503794 759815 := bstep (se 1 (by rfl) ⟨569861, by rfl⟩ : syracuseStep 759815 = 1139723) B1139723
theorem B759851 : Blo 503794 759851 := bstep (se 1 (by rfl) ⟨569888, by rfl⟩ : syracuseStep 759851 = 1139777) B1139777
theorem B759881 : Blo 503794 759881 := bstep (se 2 (by rfl) ⟨284955, by rfl⟩ : syracuseStep 759881 = 569911) B569911
theorem B759995 : Blo 503794 759995 := bstep (se 1 (by rfl) ⟨569996, by rfl⟩ : syracuseStep 759995 = 1139993) B1139993
theorem B760055 : Blo 503794 760055 := bstep (se 1 (by rfl) ⟨570041, by rfl⟩ : syracuseStep 760055 = 1140083) B1140083
theorem B760079 : Blo 503794 760079 := bstep (se 1 (by rfl) ⟨570059, by rfl⟩ : syracuseStep 760079 = 1140119) B1140119
theorem B6166817 : Blo 503794 6166817 := bstep (se 2 (by rfl) ⟨2312556, by rfl⟩ : syracuseStep 6166817 = 4625113) B4625113
theorem B760121 : Blo 503794 760121 := bstep (se 2 (by rfl) ⟨285045, by rfl⟩ : syracuseStep 760121 = 570091) B570091
theorem B1710395 : Blo 503794 1710395 := bstep (se 1 (by rfl) ⟨1282796, by rfl⟩ : syracuseStep 1710395 = 2565593) B2565593
theorem B1317235 : Blo 503794 1317235 := bstep (se 1 (by rfl) ⟨987926, by rfl⟩ : syracuseStep 1317235 = 1975853) B1975853
theorem B1153415 : Blo 503794 1153415 := bstep (se 1 (by rfl) ⟨865061, by rfl⟩ : syracuseStep 1153415 = 1730123) B1730123
theorem B760199 : Blo 503794 760199 := bstep (se 1 (by rfl) ⟨570149, by rfl⟩ : syracuseStep 760199 = 1140299) B1140299
theorem B760235 : Blo 503794 760235 := bstep (se 1 (by rfl) ⟨570176, by rfl⟩ : syracuseStep 760235 = 1140353) B1140353
theorem B956873 : Blo 503794 956873 := bstep (se 2 (by rfl) ⟨358827, by rfl⟩ : syracuseStep 956873 = 717655) B717655
theorem B760265 : Blo 503794 760265 := bstep (se 2 (by rfl) ⟨285099, by rfl⟩ : syracuseStep 760265 = 570199) B570199
theorem B1284619 : Blo 503794 1284619 := bstep (se 1 (by rfl) ⟨963464, by rfl⟩ : syracuseStep 1284619 = 1926929) B1926929
theorem B760379 : Blo 503794 760379 := bstep (se 1 (by rfl) ⟨570284, by rfl⟩ : syracuseStep 760379 = 1140569) B1140569
theorem B760439 : Blo 503794 760439 := bstep (se 1 (by rfl) ⟨570329, by rfl⟩ : syracuseStep 760439 = 1140659) B1140659
theorem B760463 : Blo 503794 760463 := bstep (se 1 (by rfl) ⟨570347, by rfl⟩ : syracuseStep 760463 = 1140695) B1140695
theorem B1284761 : Blo 503794 1284761 := bstep (se 2 (by rfl) ⟨481785, by rfl⟩ : syracuseStep 1284761 = 963571) B963571
theorem B760505 : Blo 503794 760505 := bstep (se 2 (by rfl) ⟨285189, by rfl⟩ : syracuseStep 760505 = 570379) B570379
theorem B760583 : Blo 503794 760583 := bstep (se 1 (by rfl) ⟨570437, by rfl⟩ : syracuseStep 760583 = 1140875) B1140875
theorem B2333455 : Blo 503794 2333455 := bstep (se 1 (by rfl) ⟨1750091, by rfl⟩ : syracuseStep 2333455 = 3500183) B3500183
theorem B1710881 : Blo 503794 1710881 := bstep (se 2 (by rfl) ⟨641580, by rfl⟩ : syracuseStep 1710881 = 1283161) B1283161
theorem B760619 : Blo 503794 760619 := bstep (se 1 (by rfl) ⟨570464, by rfl⟩ : syracuseStep 760619 = 1140929) B1140929
theorem B1284923 : Blo 503794 1284923 := bstep (se 1 (by rfl) ⟨963692, by rfl⟩ : syracuseStep 1284923 = 1927385) B1927385
theorem B760649 : Blo 503794 760649 := bstep (se 2 (by rfl) ⟨285243, by rfl⟩ : syracuseStep 760649 = 570487) B570487
theorem B3840857 : Blo 503794 3840857 := bstep (se 2 (by rfl) ⟨1440321, by rfl⟩ : syracuseStep 3840857 = 2880643) B2880643
theorem B2563001 : Blo 503794 2563001 := bstep (se 2 (by rfl) ⟨961125, by rfl⟩ : syracuseStep 2563001 = 1922251) B1922251
theorem B760763 : Blo 503794 760763 := bstep (se 1 (by rfl) ⟨570572, by rfl⟩ : syracuseStep 760763 = 1141145) B1141145
theorem B760823 : Blo 503794 760823 := bstep (se 1 (by rfl) ⟨570617, by rfl⟩ : syracuseStep 760823 = 1141235) B1141235
theorem B760847 : Blo 503794 760847 := bstep (se 1 (by rfl) ⟨570635, by rfl⟩ : syracuseStep 760847 = 1141271) B1141271
theorem B760889 : Blo 503794 760889 := bstep (se 2 (by rfl) ⟨285333, by rfl⟩ : syracuseStep 760889 = 570667) B570667
theorem B760967 : Blo 503794 760967 := bstep (se 1 (by rfl) ⟨570725, by rfl⟩ : syracuseStep 760967 = 1141451) B1141451
theorem B1285267 : Blo 503794 1285267 := bstep (se 1 (by rfl) ⟨963950, by rfl⟩ : syracuseStep 1285267 = 1927901) B1927901
theorem B761003 : Blo 503794 761003 := bstep (se 1 (by rfl) ⟨570752, by rfl⟩ : syracuseStep 761003 = 1141505) B1141505
theorem B761033 : Blo 503794 761033 := bstep (se 2 (by rfl) ⟨285387, by rfl⟩ : syracuseStep 761033 = 570775) B570775
theorem B3087617 : Blo 503794 3087617 := bstep (se 2 (by rfl) ⟨1157856, by rfl⟩ : syracuseStep 3087617 = 2315713) B2315713
theorem B957739 : Blo 503794 957739 := bstep (se 1 (by rfl) ⟨718304, by rfl⟩ : syracuseStep 957739 = 1436609) B1436609
theorem B761147 : Blo 503794 761147 := bstep (se 1 (by rfl) ⟨570860, by rfl⟩ : syracuseStep 761147 = 1141721) B1141721
theorem B1711475 : Blo 503794 1711475 := bstep (se 1 (by rfl) ⟨1283606, by rfl⟩ : syracuseStep 1711475 = 2567213) B2567213
theorem B2891123 : Blo 503794 2891123 := bstep (se 1 (by rfl) ⟨2168342, by rfl⟩ : syracuseStep 2891123 = 4336685) B4336685
theorem B957815 : Blo 503794 957815 := bstep (se 1 (by rfl) ⟨718361, by rfl⟩ : syracuseStep 957815 = 1436723) B1436723
theorem B761207 : Blo 503794 761207 := bstep (se 1 (by rfl) ⟨570905, by rfl⟩ : syracuseStep 761207 = 1141811) B1141811
theorem B761231 : Blo 503794 761231 := bstep (se 1 (by rfl) ⟨570923, by rfl⟩ : syracuseStep 761231 = 1141847) B1141847
theorem B761273 : Blo 503794 761273 := bstep (se 2 (by rfl) ⟨285477, by rfl⟩ : syracuseStep 761273 = 570955) B570955
theorem B761351 : Blo 503794 761351 := bstep (se 1 (by rfl) ⟨571013, by rfl⟩ : syracuseStep 761351 = 1142027) B1142027
theorem B761387 : Blo 503794 761387 := bstep (se 1 (by rfl) ⟨571040, by rfl⟩ : syracuseStep 761387 = 1142081) B1142081
theorem B761417 : Blo 503794 761417 := bstep (se 2 (by rfl) ⟨285531, by rfl⟩ : syracuseStep 761417 = 571063) B571063
theorem B761531 : Blo 503794 761531 := bstep (se 1 (by rfl) ⟨571148, by rfl⟩ : syracuseStep 761531 = 1142297) B1142297
theorem B761591 : Blo 503794 761591 := bstep (se 1 (by rfl) ⟨571193, by rfl⟩ : syracuseStep 761591 = 1142387) B1142387
theorem B761615 : Blo 503794 761615 := bstep (se 1 (by rfl) ⟨571211, by rfl⟩ : syracuseStep 761615 = 1142423) B1142423
theorem B3841829 : Blo 503794 3841829 := bstep (se 4 (by rfl) ⟨360171, by rfl⟩ : syracuseStep 3841829 = 720343) B720343
theorem B761657 : Blo 503794 761657 := bstep (se 2 (by rfl) ⟨285621, by rfl⟩ : syracuseStep 761657 = 571243) B571243
theorem B3252311 : Blo 503794 3252311 := bstep (se 1 (by rfl) ⟨2439233, by rfl⟩ : syracuseStep 3252311 = 4878467) B4878467
theorem B2564297 : Blo 503794 2564297 := bstep (se 2 (by rfl) ⟨961611, by rfl⟩ : syracuseStep 2564297 = 1923223) B1923223
theorem B4170131 : Blo 503794 4170131 := bstep (se 1 (by rfl) ⟨3127598, by rfl⟩ : syracuseStep 4170131 = 6255197) B6255197
theorem B5448485 : Blo 503794 5448485 := bstep (se 4 (by rfl) ⟨510795, by rfl⟩ : syracuseStep 5448485 = 1021591) B1021591
theorem B2433851 : Blo 503794 2433851 := bstep (se 1 (by rfl) ⟨1825388, by rfl⟩ : syracuseStep 2433851 = 3650777) B3650777
theorem B1025225 : Blo 503794 1025225 := bstep (se 2 (by rfl) ⟨384459, by rfl⟩ : syracuseStep 1025225 = 768919) B768919
theorem B1156297 : Blo 503794 1156297 := bstep (se 2 (by rfl) ⟨433611, by rfl⟩ : syracuseStep 1156297 = 867223) B867223
theorem B959759 : Blo 503794 959759 := bstep (se 1 (by rfl) ⟨719819, by rfl⟩ : syracuseStep 959759 = 1439639) B1439639
theorem B1942937 : Blo 503794 1942937 := bstep (se 2 (by rfl) ⟨728601, by rfl⟩ : syracuseStep 1942937 = 1457203) B1457203
theorem B18425717 : Blo 503794 18425717 := bstep (se 5 (by rfl) ⟨863705, by rfl⟩ : syracuseStep 18425717 = 1727411) B1727411
theorem B567175 : Blo 503794 567175 := bstep (se 1 (by rfl) ⟨425381, by rfl⟩ : syracuseStep 567175 = 850763) B850763
theorem B1025939 : Blo 503794 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B1615801 : Blo 503794 1615801 := bstep (se 2 (by rfl) ⟨605925, by rfl⟩ : syracuseStep 1615801 = 1211851) B1211851
theorem B567355 : Blo 503794 567355 := bstep (se 1 (by rfl) ⟨425516, by rfl⟩ : syracuseStep 567355 = 851033) B851033
theorem B10954925 : Blo 503794 10954925 := bstep (se 3 (by rfl) ⟨2054048, by rfl⟩ : syracuseStep 10954925 = 4108097) B4108097
theorem B567823 : Blo 503794 567823 := bstep (se 1 (by rfl) ⟨425867, by rfl⟩ : syracuseStep 567823 = 851735) B851735
theorem B1157647 : Blo 503794 1157647 := bstep (se 1 (by rfl) ⟨868235, by rfl⟩ : syracuseStep 1157647 = 1736471) B1736471
theorem B2468381 : Blo 503794 2468381 := bstep (se 3 (by rfl) ⟨462821, by rfl⟩ : syracuseStep 2468381 = 925643) B925643
theorem B12462659 : Blo 503794 12462659 := bstep (se 1 (by rfl) ⟨9346994, by rfl⟩ : syracuseStep 12462659 = 18693989) B18693989
theorem B2960165 : Blo 503794 2960165 := bstep (se 4 (by rfl) ⟨277515, by rfl⟩ : syracuseStep 2960165 = 555031) B555031
theorem B1616699 : Blo 503794 1616699 := bstep (se 1 (by rfl) ⟨1212524, by rfl⟩ : syracuseStep 1616699 = 2425049) B2425049
theorem B961399 : Blo 503794 961399 := bstep (se 1 (by rfl) ⟨721049, by rfl⟩ : syracuseStep 961399 = 1442099) B1442099
theorem B568327 : Blo 503794 568327 := bstep (se 1 (by rfl) ⟨426245, by rfl⟩ : syracuseStep 568327 = 852491) B852491
theorem B568507 : Blo 503794 568507 := bstep (se 1 (by rfl) ⟨426380, by rfl⟩ : syracuseStep 568507 = 852761) B852761
theorem B1617185 : Blo 503794 1617185 := bstep (se 2 (by rfl) ⟨606444, by rfl⟩ : syracuseStep 1617185 = 1212889) B1212889
theorem B2436695 : Blo 503794 2436695 := bstep (se 1 (by rfl) ⟨1827521, by rfl⟩ : syracuseStep 2436695 = 3655043) B3655043
theorem B568975 : Blo 503794 568975 := bstep (se 1 (by rfl) ⟨426731, by rfl⟩ : syracuseStep 568975 = 853463) B853463
theorem B3878705 : Blo 503794 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B10399691 : Blo 503794 10399691 := bstep (se 1 (by rfl) ⟨7799768, by rfl⟩ : syracuseStep 10399691 = 15599537) B15599537
theorem B503815 : Blo 503794 503815 := bstep (se 1 (by rfl) ⟨377861, by rfl⟩ : syracuseStep 503815 = 755723) B755723
theorem B503823 : Blo 503794 503823 := bstep (se 1 (by rfl) ⟨377867, by rfl⟩ : syracuseStep 503823 = 755735) B755735
theorem B503867 : Blo 503794 503867 := bstep (se 1 (by rfl) ⟨377900, by rfl⟩ : syracuseStep 503867 = 755801) B755801
theorem B503943 : Blo 503794 503943 := bstep (se 1 (by rfl) ⟨377957, by rfl⟩ : syracuseStep 503943 = 755915) B755915
theorem B569479 : Blo 503794 569479 := bstep (se 1 (by rfl) ⟨427109, by rfl⟩ : syracuseStep 569479 = 854219) B854219
theorem B503951 : Blo 503794 503951 := bstep (se 1 (by rfl) ⟨377963, by rfl⟩ : syracuseStep 503951 = 755927) B755927
theorem B503995 : Blo 503794 503995 := bstep (se 1 (by rfl) ⟨377996, by rfl⟩ : syracuseStep 503995 = 755993) B755993
theorem B504071 : Blo 503794 504071 := bstep (se 1 (by rfl) ⟨378053, by rfl⟩ : syracuseStep 504071 = 756107) B756107
theorem B504079 : Blo 503794 504079 := bstep (se 1 (by rfl) ⟨378059, by rfl⟩ : syracuseStep 504079 = 756119) B756119
theorem B504123 : Blo 503794 504123 := bstep (se 1 (by rfl) ⟨378092, by rfl⟩ : syracuseStep 504123 = 756185) B756185
theorem B569659 : Blo 503794 569659 := bstep (se 1 (by rfl) ⟨427244, by rfl⟩ : syracuseStep 569659 = 854489) B854489
theorem B504199 : Blo 503794 504199 := bstep (se 1 (by rfl) ⟨378149, by rfl⟩ : syracuseStep 504199 = 756299) B756299
theorem B504207 : Blo 503794 504207 := bstep (se 1 (by rfl) ⟨378155, by rfl⟩ : syracuseStep 504207 = 756311) B756311
theorem B504251 : Blo 503794 504251 := bstep (se 1 (by rfl) ⟨378188, by rfl⟩ : syracuseStep 504251 = 756377) B756377
theorem B504327 : Blo 503794 504327 := bstep (se 1 (by rfl) ⟨378245, by rfl⟩ : syracuseStep 504327 = 756491) B756491
theorem B504335 : Blo 503794 504335 := bstep (se 1 (by rfl) ⟨378251, by rfl⟩ : syracuseStep 504335 = 756503) B756503
theorem B766523 : Blo 503794 766523 := bstep (se 1 (by rfl) ⟨574892, by rfl⟩ : syracuseStep 766523 = 1149785) B1149785
theorem B504379 : Blo 503794 504379 := bstep (se 1 (by rfl) ⟨378284, by rfl⟩ : syracuseStep 504379 = 756569) B756569
theorem B963191 : Blo 503794 963191 := bstep (se 1 (by rfl) ⟨722393, by rfl⟩ : syracuseStep 963191 = 1444787) B1444787
theorem B504455 : Blo 503794 504455 := bstep (se 1 (by rfl) ⟨378341, by rfl⟩ : syracuseStep 504455 = 756683) B756683
theorem B504463 : Blo 503794 504463 := bstep (se 1 (by rfl) ⟨378347, by rfl⟩ : syracuseStep 504463 = 756695) B756695
theorem B504507 : Blo 503794 504507 := bstep (se 1 (by rfl) ⟨378380, by rfl⟩ : syracuseStep 504507 = 756761) B756761
theorem B504583 : Blo 503794 504583 := bstep (se 1 (by rfl) ⟨378437, by rfl⟩ : syracuseStep 504583 = 756875) B756875
theorem B504591 : Blo 503794 504591 := bstep (se 1 (by rfl) ⟨378443, by rfl⟩ : syracuseStep 504591 = 756887) B756887
theorem B570127 : Blo 503794 570127 := bstep (se 1 (by rfl) ⟨427595, by rfl⟩ : syracuseStep 570127 = 855191) B855191
theorem B963343 : Blo 503794 963343 := bstep (se 1 (by rfl) ⟨722507, by rfl⟩ : syracuseStep 963343 = 1445015) B1445015
theorem B504635 : Blo 503794 504635 := bstep (se 1 (by rfl) ⟨378476, by rfl⟩ : syracuseStep 504635 = 756953) B756953
theorem B504711 : Blo 503794 504711 := bstep (se 1 (by rfl) ⟨378533, by rfl⟩ : syracuseStep 504711 = 757067) B757067
theorem B504719 : Blo 503794 504719 := bstep (se 1 (by rfl) ⟨378539, by rfl⟩ : syracuseStep 504719 = 757079) B757079
theorem B504763 : Blo 503794 504763 := bstep (se 1 (by rfl) ⟨378572, by rfl⟩ : syracuseStep 504763 = 757145) B757145
theorem B504839 : Blo 503794 504839 := bstep (se 1 (by rfl) ⟨378629, by rfl⟩ : syracuseStep 504839 = 757259) B757259
theorem B504847 : Blo 503794 504847 := bstep (se 1 (by rfl) ⟨378635, by rfl⟩ : syracuseStep 504847 = 757271) B757271
theorem B504891 : Blo 503794 504891 := bstep (se 1 (by rfl) ⟨378668, by rfl⟩ : syracuseStep 504891 = 757337) B757337
theorem B1913975 : Blo 503794 1913975 := bstep (se 1 (by rfl) ⟨1435481, by rfl⟩ : syracuseStep 1913975 = 2870963) B2870963
theorem B504967 : Blo 503794 504967 := bstep (se 1 (by rfl) ⟨378725, by rfl⟩ : syracuseStep 504967 = 757451) B757451
theorem B504975 : Blo 503794 504975 := bstep (se 1 (by rfl) ⟨378731, by rfl⟩ : syracuseStep 504975 = 757463) B757463
theorem B963731 : Blo 503794 963731 := bstep (se 1 (by rfl) ⟨722798, by rfl⟩ : syracuseStep 963731 = 1445597) B1445597
theorem B505019 : Blo 503794 505019 := bstep (se 1 (by rfl) ⟨378764, by rfl⟩ : syracuseStep 505019 = 757529) B757529
theorem B505095 : Blo 503794 505095 := bstep (se 1 (by rfl) ⟨378821, by rfl⟩ : syracuseStep 505095 = 757643) B757643
theorem B570631 : Blo 503794 570631 := bstep (se 1 (by rfl) ⟨427973, by rfl⟩ : syracuseStep 570631 = 855947) B855947
theorem B505103 : Blo 503794 505103 := bstep (se 1 (by rfl) ⟨378827, by rfl⟩ : syracuseStep 505103 = 757655) B757655
theorem B505147 : Blo 503794 505147 := bstep (se 1 (by rfl) ⟨378860, by rfl⟩ : syracuseStep 505147 = 757721) B757721
theorem B505223 : Blo 503794 505223 := bstep (se 1 (by rfl) ⟨378917, by rfl⟩ : syracuseStep 505223 = 757835) B757835
theorem B505231 : Blo 503794 505231 := bstep (se 1 (by rfl) ⟨378923, by rfl⟩ : syracuseStep 505231 = 757847) B757847
theorem B505275 : Blo 503794 505275 := bstep (se 1 (by rfl) ⟨378956, by rfl⟩ : syracuseStep 505275 = 757913) B757913
theorem B570811 : Blo 503794 570811 := bstep (se 1 (by rfl) ⟨428108, by rfl⟩ : syracuseStep 570811 = 856217) B856217
theorem B505351 : Blo 503794 505351 := bstep (se 1 (by rfl) ⟨379013, by rfl⟩ : syracuseStep 505351 = 758027) B758027
theorem B505359 : Blo 503794 505359 := bstep (se 1 (by rfl) ⟨379019, by rfl⟩ : syracuseStep 505359 = 758039) B758039
theorem B505403 : Blo 503794 505403 := bstep (se 1 (by rfl) ⟨379052, by rfl⟩ : syracuseStep 505403 = 758105) B758105
theorem B505479 : Blo 503794 505479 := bstep (se 1 (by rfl) ⟨379109, by rfl⟩ : syracuseStep 505479 = 758219) B758219
theorem B505487 : Blo 503794 505487 := bstep (se 1 (by rfl) ⟨379115, by rfl⟩ : syracuseStep 505487 = 758231) B758231
theorem B505531 : Blo 503794 505531 := bstep (se 1 (by rfl) ⟨379148, by rfl⟩ : syracuseStep 505531 = 758297) B758297
theorem B505607 : Blo 503794 505607 := bstep (se 1 (by rfl) ⟨379205, by rfl⟩ : syracuseStep 505607 = 758411) B758411
theorem B505615 : Blo 503794 505615 := bstep (se 1 (by rfl) ⟨379211, by rfl⟩ : syracuseStep 505615 = 758423) B758423
theorem B505659 : Blo 503794 505659 := bstep (se 1 (by rfl) ⟨379244, by rfl⟩ : syracuseStep 505659 = 758489) B758489
theorem B2439001 : Blo 503794 2439001 := bstep (se 2 (by rfl) ⟨914625, by rfl⟩ : syracuseStep 2439001 = 1829251) B1829251
theorem B505735 : Blo 503794 505735 := bstep (se 1 (by rfl) ⟨379301, by rfl⟩ : syracuseStep 505735 = 758603) B758603
theorem B505743 : Blo 503794 505743 := bstep (se 1 (by rfl) ⟨379307, by rfl⟩ : syracuseStep 505743 = 758615) B758615
theorem B2570129 : Blo 503794 2570129 := bstep (se 2 (by rfl) ⟨963798, by rfl⟩ : syracuseStep 2570129 = 1927597) B1927597
theorem B505787 : Blo 503794 505787 := bstep (se 1 (by rfl) ⟨379340, by rfl⟩ : syracuseStep 505787 = 758681) B758681
theorem B505863 : Blo 503794 505863 := bstep (se 1 (by rfl) ⟨379397, by rfl⟩ : syracuseStep 505863 = 758795) B758795
theorem B505871 : Blo 503794 505871 := bstep (se 1 (by rfl) ⟨379403, by rfl⟩ : syracuseStep 505871 = 758807) B758807
theorem B505915 : Blo 503794 505915 := bstep (se 1 (by rfl) ⟨379436, by rfl⟩ : syracuseStep 505915 = 758873) B758873
theorem B1914947 : Blo 503794 1914947 := bstep (se 1 (by rfl) ⟨1436210, by rfl⟩ : syracuseStep 1914947 = 2872421) B2872421
theorem B866423 : Blo 503794 866423 := bstep (se 1 (by rfl) ⟨649817, by rfl⟩ : syracuseStep 866423 = 1299635) B1299635
theorem B505991 : Blo 503794 505991 := bstep (se 1 (by rfl) ⟨379493, by rfl⟩ : syracuseStep 505991 = 758987) B758987
theorem B505999 : Blo 503794 505999 := bstep (se 1 (by rfl) ⟨379499, by rfl⟩ : syracuseStep 505999 = 758999) B758999
theorem B506043 : Blo 503794 506043 := bstep (se 1 (by rfl) ⟨379532, by rfl⟩ : syracuseStep 506043 = 759065) B759065
theorem B506119 : Blo 503794 506119 := bstep (se 1 (by rfl) ⟨379589, by rfl⟩ : syracuseStep 506119 = 759179) B759179
theorem B506127 : Blo 503794 506127 := bstep (se 1 (by rfl) ⟨379595, by rfl⟩ : syracuseStep 506127 = 759191) B759191
theorem B506171 : Blo 503794 506171 := bstep (se 1 (by rfl) ⟨379628, by rfl⟩ : syracuseStep 506171 = 759257) B759257
theorem B1292663 : Blo 503794 1292663 := bstep (se 1 (by rfl) ⟨969497, by rfl⟩ : syracuseStep 1292663 = 1938995) B1938995
theorem B506247 : Blo 503794 506247 := bstep (se 1 (by rfl) ⟨379685, by rfl⟩ : syracuseStep 506247 = 759371) B759371
theorem B506255 : Blo 503794 506255 := bstep (se 1 (by rfl) ⟨379691, by rfl⟩ : syracuseStep 506255 = 759383) B759383
theorem B2308505 : Blo 503794 2308505 := bstep (se 2 (by rfl) ⟨865689, by rfl⟩ : syracuseStep 2308505 = 1731379) B1731379
theorem B3848633 : Blo 503794 3848633 := bstep (se 2 (by rfl) ⟨1443237, by rfl⟩ : syracuseStep 3848633 = 2886475) B2886475
theorem B506299 : Blo 503794 506299 := bstep (se 1 (by rfl) ⟨379724, by rfl⟩ : syracuseStep 506299 = 759449) B759449
theorem B506375 : Blo 503794 506375 := bstep (se 1 (by rfl) ⟨379781, by rfl⟩ : syracuseStep 506375 = 759563) B759563
theorem B506383 : Blo 503794 506383 := bstep (se 1 (by rfl) ⟨379787, by rfl⟩ : syracuseStep 506383 = 759575) B759575
theorem B506427 : Blo 503794 506427 := bstep (se 1 (by rfl) ⟨379820, by rfl⟩ : syracuseStep 506427 = 759641) B759641
theorem B506503 : Blo 503794 506503 := bstep (se 1 (by rfl) ⟨379877, by rfl⟩ : syracuseStep 506503 = 759755) B759755
theorem B506511 : Blo 503794 506511 := bstep (se 1 (by rfl) ⟨379883, by rfl⟩ : syracuseStep 506511 = 759767) B759767
theorem B637627 : Blo 503794 637627 := bstep (se 1 (by rfl) ⟨478220, by rfl⟩ : syracuseStep 637627 = 956441) B956441
theorem B506555 : Blo 503794 506555 := bstep (se 1 (by rfl) ⟨379916, by rfl⟩ : syracuseStep 506555 = 759833) B759833
theorem B506631 : Blo 503794 506631 := bstep (se 1 (by rfl) ⟨379973, by rfl⟩ : syracuseStep 506631 = 759947) B759947
theorem B506639 : Blo 503794 506639 := bstep (se 1 (by rfl) ⟨379979, by rfl⟩ : syracuseStep 506639 = 759959) B759959
theorem B506683 : Blo 503794 506683 := bstep (se 1 (by rfl) ⟨380012, by rfl⟩ : syracuseStep 506683 = 760025) B760025
theorem B506759 : Blo 503794 506759 := bstep (se 1 (by rfl) ⟨380069, by rfl⟩ : syracuseStep 506759 = 760139) B760139
theorem B506767 : Blo 503794 506767 := bstep (se 1 (by rfl) ⟨380075, by rfl⟩ : syracuseStep 506767 = 760151) B760151
theorem B506811 : Blo 503794 506811 := bstep (se 1 (by rfl) ⟨380108, by rfl⟩ : syracuseStep 506811 = 760217) B760217
theorem B506887 : Blo 503794 506887 := bstep (se 1 (by rfl) ⟨380165, by rfl⟩ : syracuseStep 506887 = 760331) B760331
theorem B506895 : Blo 503794 506895 := bstep (se 1 (by rfl) ⟨380171, by rfl⟩ : syracuseStep 506895 = 760343) B760343
theorem B1915933 : Blo 503794 1915933 := bstep (se 3 (by rfl) ⟨359237, by rfl⟩ : syracuseStep 1915933 = 718475) B718475
theorem B506939 : Blo 503794 506939 := bstep (se 1 (by rfl) ⟨380204, by rfl⟩ : syracuseStep 506939 = 760409) B760409
theorem B507015 : Blo 503794 507015 := bstep (se 1 (by rfl) ⟨380261, by rfl⟩ : syracuseStep 507015 = 760523) B760523
theorem B507023 : Blo 503794 507023 := bstep (se 1 (by rfl) ⟨380267, by rfl⟩ : syracuseStep 507023 = 760535) B760535
theorem B507067 : Blo 503794 507067 := bstep (se 1 (by rfl) ⟨380300, by rfl⟩ : syracuseStep 507067 = 760601) B760601
theorem B507143 : Blo 503794 507143 := bstep (se 1 (by rfl) ⟨380357, by rfl⟩ : syracuseStep 507143 = 760715) B760715
theorem B507151 : Blo 503794 507151 := bstep (se 1 (by rfl) ⟨380363, by rfl⟩ : syracuseStep 507151 = 760727) B760727
theorem B507195 : Blo 503794 507195 := bstep (se 1 (by rfl) ⟨380396, by rfl⟩ : syracuseStep 507195 = 760793) B760793
theorem B507271 : Blo 503794 507271 := bstep (se 1 (by rfl) ⟨380453, by rfl⟩ : syracuseStep 507271 = 760907) B760907
theorem B507279 : Blo 503794 507279 := bstep (se 1 (by rfl) ⟨380459, by rfl⟩ : syracuseStep 507279 = 760919) B760919
theorem B507323 : Blo 503794 507323 := bstep (se 1 (by rfl) ⟨380492, by rfl⟩ : syracuseStep 507323 = 760985) B760985
theorem B507399 : Blo 503794 507399 := bstep (se 1 (by rfl) ⟨380549, by rfl⟩ : syracuseStep 507399 = 761099) B761099
theorem B507407 : Blo 503794 507407 := bstep (se 1 (by rfl) ⟨380555, by rfl⟩ : syracuseStep 507407 = 761111) B761111
theorem B6471197 : Blo 503794 6471197 := bstep (se 3 (by rfl) ⟨1213349, by rfl⟩ : syracuseStep 6471197 = 2426699) B2426699
theorem B507451 : Blo 503794 507451 := bstep (se 1 (by rfl) ⟨380588, by rfl⟩ : syracuseStep 507451 = 761177) B761177
theorem B638599 : Blo 503794 638599 := bstep (se 1 (by rfl) ⟨478949, by rfl⟩ : syracuseStep 638599 = 957899) B957899
theorem B507527 : Blo 503794 507527 := bstep (se 1 (by rfl) ⟨380645, by rfl⟩ : syracuseStep 507527 = 761291) B761291
theorem B507535 : Blo 503794 507535 := bstep (se 1 (by rfl) ⟨380651, by rfl⟩ : syracuseStep 507535 = 761303) B761303
theorem B507579 : Blo 503794 507579 := bstep (se 1 (by rfl) ⟨380684, by rfl⟩ : syracuseStep 507579 = 761369) B761369
theorem B507655 : Blo 503794 507655 := bstep (se 1 (by rfl) ⟨380741, by rfl⟩ : syracuseStep 507655 = 761483) B761483
theorem B507663 : Blo 503794 507663 := bstep (se 1 (by rfl) ⟨380747, by rfl⟩ : syracuseStep 507663 = 761495) B761495
theorem B507707 : Blo 503794 507707 := bstep (se 1 (by rfl) ⟨380780, by rfl⟩ : syracuseStep 507707 = 761561) B761561
theorem B507783 : Blo 503794 507783 := bstep (se 1 (by rfl) ⟨380837, by rfl⟩ : syracuseStep 507783 = 761675) B761675
theorem B507791 : Blo 503794 507791 := bstep (se 1 (by rfl) ⟨380843, by rfl⟩ : syracuseStep 507791 = 761687) B761687
theorem B639019 : Blo 503794 639019 := bstep (se 1 (by rfl) ⟨479264, by rfl⟩ : syracuseStep 639019 = 958529) B958529
theorem B1294471 : Blo 503794 1294471 := bstep (se 1 (by rfl) ⟨970853, by rfl⟩ : syracuseStep 1294471 = 1941707) B1941707
theorem B639247 : Blo 503794 639247 := bstep (se 1 (by rfl) ⟨479435, by rfl⟩ : syracuseStep 639247 = 958871) B958871
theorem B2310515 : Blo 503794 2310515 := bstep (se 1 (by rfl) ⟨1732886, by rfl⟩ : syracuseStep 2310515 = 3465773) B3465773
theorem B29573603 : Blo 503794 29573603 := bstep (se 1 (by rfl) ⟨22180202, by rfl⟩ : syracuseStep 29573603 = 44360405) B44360405
theorem B4112963 : Blo 503794 4112963 := bstep (se 1 (by rfl) ⟨3084722, by rfl⟩ : syracuseStep 4112963 = 6169445) B6169445
theorem B6505231 : Blo 503794 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B2048827 : Blo 503794 2048827 := bstep (se 1 (by rfl) ⟨1536620, by rfl⟩ : syracuseStep 2048827 = 3073241) B3073241
theorem B607223 : Blo 503794 607223 := bstep (se 1 (by rfl) ⟨455417, by rfl⟩ : syracuseStep 607223 = 910835) B910835
theorem B639991 : Blo 503794 639991 := bstep (se 1 (by rfl) ⟨479993, by rfl⟩ : syracuseStep 639991 = 959987) B959987
theorem B640315 : Blo 503794 640315 := bstep (se 1 (by rfl) ⟨480236, by rfl⟩ : syracuseStep 640315 = 960473) B960473
theorem B607675 : Blo 503794 607675 := bstep (se 1 (by rfl) ⟨455756, by rfl⟩ : syracuseStep 607675 = 911513) B911513
theorem B607915 : Blo 503794 607915 := bstep (se 1 (by rfl) ⟨455936, by rfl⟩ : syracuseStep 607915 = 911873) B911873
theorem B640811 : Blo 503794 640811 := bstep (se 1 (by rfl) ⟨480608, by rfl⟩ : syracuseStep 640811 = 961217) B961217
theorem B1918835 : Blo 503794 1918835 := bstep (se 1 (by rfl) ⟨1439126, by rfl⟩ : syracuseStep 1918835 = 2878253) B2878253
theorem B3655853 : Blo 503794 3655853 := bstep (se 3 (by rfl) ⟨685472, by rfl⟩ : syracuseStep 3655853 = 1370945) B1370945
theorem B12503285 : Blo 503794 12503285 := bstep (se 5 (by rfl) ⟨586091, by rfl⟩ : syracuseStep 12503285 = 1172183) B1172183
theorem B2869505 : Blo 503794 2869505 := bstep (se 2 (by rfl) ⟨1076064, by rfl⟩ : syracuseStep 2869505 = 2152129) B2152129
theorem B641287 : Blo 503794 641287 := bstep (se 1 (by rfl) ⟨480965, by rfl⟩ : syracuseStep 641287 = 961931) B961931
theorem B2345539 : Blo 503794 2345539 := bstep (se 1 (by rfl) ⟨1759154, by rfl⟩ : syracuseStep 2345539 = 3518309) B3518309
theorem B1297015 : Blo 503794 1297015 := bstep (se 1 (by rfl) ⟨972761, by rfl⟩ : syracuseStep 1297015 = 1945523) B1945523
theorem B9226871 : Blo 503794 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B6933185 : Blo 503794 6933185 := bstep (se 2 (by rfl) ⟨2599944, by rfl⟩ : syracuseStep 6933185 = 5199889) B5199889
theorem B641783 : Blo 503794 641783 := bstep (se 1 (by rfl) ⟨481337, by rfl⟩ : syracuseStep 641783 = 962675) B962675
theorem B3296015 : Blo 503794 3296015 := bstep (se 1 (by rfl) ⟨2472011, by rfl⟩ : syracuseStep 3296015 = 4944023) B4944023
theorem B1461107 : Blo 503794 1461107 := bstep (se 1 (by rfl) ⟨1095830, by rfl⟩ : syracuseStep 1461107 = 2191661) B2191661
theorem B641935 : Blo 503794 641935 := bstep (se 1 (by rfl) ⟨481451, by rfl⟩ : syracuseStep 641935 = 962903) B962903
theorem B642107 : Blo 503794 642107 := bstep (se 1 (by rfl) ⟨481580, by rfl⟩ : syracuseStep 642107 = 963161) B963161
theorem B3067109 : Blo 503794 3067109 := bstep (se 4 (by rfl) ⟨287541, by rfl⟩ : syracuseStep 3067109 = 575083) B575083
theorem B5459345 : Blo 503794 5459345 := bstep (se 2 (by rfl) ⟨2047254, by rfl⟩ : syracuseStep 5459345 = 4094509) B4094509
theorem B1134215 : Blo 503794 1134215 := bstep (se 1 (by rfl) ⟨850661, by rfl⟩ : syracuseStep 1134215 = 1701323) B1701323
theorem B1134395 : Blo 503794 1134395 := bstep (se 1 (by rfl) ⟨850796, by rfl⟩ : syracuseStep 1134395 = 1701593) B1701593
theorem B99438515 : Blo 503794 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B1134521 : Blo 503794 1134521 := bstep (se 2 (by rfl) ⟨425445, by rfl⟩ : syracuseStep 1134521 = 850891) B850891
theorem B1921067 : Blo 503794 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B1134863 : Blo 503794 1134863 := bstep (se 1 (by rfl) ⟨851147, by rfl⟩ : syracuseStep 1134863 = 1702295) B1702295
theorem B1134881 : Blo 503794 1134881 := bstep (se 2 (by rfl) ⟨425580, by rfl⟩ : syracuseStep 1134881 = 851161) B851161
theorem B2871895 : Blo 503794 2871895 := bstep (se 1 (by rfl) ⟨2153921, by rfl⟩ : syracuseStep 2871895 = 4307843) B4307843
theorem B1135223 : Blo 503794 1135223 := bstep (se 1 (by rfl) ⟨851417, by rfl⟩ : syracuseStep 1135223 = 1702835) B1702835
theorem B4313857 : Blo 503794 4313857 := bstep (se 2 (by rfl) ⟨1617696, by rfl⟩ : syracuseStep 4313857 = 3235393) B3235393
theorem B1135403 : Blo 503794 1135403 := bstep (se 1 (by rfl) ⟨851552, by rfl⟩ : syracuseStep 1135403 = 1703105) B1703105
theorem B3068761 : Blo 503794 3068761 := bstep (se 2 (by rfl) ⟨1150785, by rfl⟩ : syracuseStep 3068761 = 2301571) B2301571
theorem B11719685 : Blo 503794 11719685 := bstep (se 4 (by rfl) ⟨1098720, by rfl⟩ : syracuseStep 11719685 = 2197441) B2197441
theorem B1135763 : Blo 503794 1135763 := bstep (se 1 (by rfl) ⟨851822, by rfl⟩ : syracuseStep 1135763 = 1703645) B1703645
theorem B1135817 : Blo 503794 1135817 := bstep (se 2 (by rfl) ⟨425931, by rfl⟩ : syracuseStep 1135817 = 851863) B851863
theorem B23287175 : Blo 503794 23287175 := bstep (se 1 (by rfl) ⟨17465381, by rfl⟩ : syracuseStep 23287175 = 34930763) B34930763
theorem B4609565 : Blo 503794 4609565 := bstep (se 3 (by rfl) ⟨864293, by rfl⟩ : syracuseStep 4609565 = 1728587) B1728587
theorem B808823 : Blo 503794 808823 := bstep (se 1 (by rfl) ⟨606617, by rfl⟩ : syracuseStep 808823 = 1213235) B1213235
theorem B1136519 : Blo 503794 1136519 := bstep (se 1 (by rfl) ⟨852389, by rfl⟩ : syracuseStep 1136519 = 1704779) B1704779
theorem B809003 : Blo 503794 809003 := bstep (se 1 (by rfl) ⟨606752, by rfl⟩ : syracuseStep 809003 = 1213505) B1213505
theorem B1136699 : Blo 503794 1136699 := bstep (se 1 (by rfl) ⟨852524, by rfl⟩ : syracuseStep 1136699 = 1705049) B1705049
theorem B972947 : Blo 503794 972947 := bstep (se 1 (by rfl) ⟨729710, by rfl⟩ : syracuseStep 972947 = 1459421) B1459421
theorem B6641837 : Blo 503794 6641837 := bstep (se 3 (by rfl) ⟨1245344, by rfl⟩ : syracuseStep 6641837 = 2490689) B2490689
theorem B1136825 : Blo 503794 1136825 := bstep (se 2 (by rfl) ⟨426309, by rfl⟩ : syracuseStep 1136825 = 852619) B852619
theorem B973001 : Blo 503794 973001 := bstep (se 2 (by rfl) ⟨364875, by rfl⟩ : syracuseStep 973001 = 729751) B729751
theorem B1137167 : Blo 503794 1137167 := bstep (se 1 (by rfl) ⟨852875, by rfl⟩ : syracuseStep 1137167 = 1705751) B1705751
theorem B2873879 : Blo 503794 2873879 := bstep (se 1 (by rfl) ⟨2155409, by rfl⟩ : syracuseStep 2873879 = 4310819) B4310819
theorem B3070493 : Blo 503794 3070493 := bstep (se 3 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 3070493 = 1151435) B1151435
theorem B1137185 : Blo 503794 1137185 := bstep (se 2 (by rfl) ⟨426444, by rfl⟩ : syracuseStep 1137185 = 852889) B852889
theorem B809515 : Blo 503794 809515 := bstep (se 1 (by rfl) ⟨607136, by rfl⟩ : syracuseStep 809515 = 1214273) B1214273
theorem B4315841 : Blo 503794 4315841 := bstep (se 2 (by rfl) ⟨1618440, by rfl⟩ : syracuseStep 4315841 = 3236881) B3236881
theorem B809771 : Blo 503794 809771 := bstep (se 1 (by rfl) ⟨607328, by rfl⟩ : syracuseStep 809771 = 1214657) B1214657
theorem B1137527 : Blo 503794 1137527 := bstep (se 1 (by rfl) ⟨853145, by rfl⟩ : syracuseStep 1137527 = 1706291) B1706291
theorem B1137707 : Blo 503794 1137707 := bstep (se 1 (by rfl) ⟨853280, by rfl⟩ : syracuseStep 1137707 = 1706561) B1706561
theorem B1138067 : Blo 503794 1138067 := bstep (se 1 (by rfl) ⟨853550, by rfl⟩ : syracuseStep 1138067 = 1707101) B1707101
theorem B1924499 : Blo 503794 1924499 := bstep (se 1 (by rfl) ⟨1443374, by rfl⟩ : syracuseStep 1924499 = 2886749) B2886749
theorem B1138121 : Blo 503794 1138121 := bstep (se 2 (by rfl) ⟨426795, by rfl⟩ : syracuseStep 1138121 = 853591) B853591
theorem B1138823 : Blo 503794 1138823 := bstep (se 1 (by rfl) ⟨854117, by rfl⟩ : syracuseStep 1138823 = 1708235) B1708235
theorem B778411 : Blo 503794 778411 := bstep (se 1 (by rfl) ⟨583808, by rfl⟩ : syracuseStep 778411 = 1167617) B1167617
theorem B1139003 : Blo 503794 1139003 := bstep (se 1 (by rfl) ⟨854252, by rfl⟩ : syracuseStep 1139003 = 1708505) B1708505
theorem B1139129 : Blo 503794 1139129 := bstep (se 2 (by rfl) ⟨427173, by rfl⟩ : syracuseStep 1139129 = 854347) B854347
theorem B647687 : Blo 503794 647687 := bstep (se 1 (by rfl) ⟨485765, by rfl⟩ : syracuseStep 647687 = 971531) B971531
theorem B3236395 : Blo 503794 3236395 := bstep (se 1 (by rfl) ⟨2427296, by rfl⟩ : syracuseStep 3236395 = 4854593) B4854593
theorem B1368695 : Blo 503794 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B2745089 : Blo 503794 2745089 := bstep (se 2 (by rfl) ⟨1029408, by rfl⟩ : syracuseStep 2745089 = 2058817) B2058817
theorem B1139471 : Blo 503794 1139471 := bstep (se 1 (by rfl) ⟨854603, by rfl⟩ : syracuseStep 1139471 = 1709207) B1709207
theorem B1139489 : Blo 503794 1139489 := bstep (se 2 (by rfl) ⟨427308, by rfl⟩ : syracuseStep 1139489 = 854617) B854617
theorem B4318231 : Blo 503794 4318231 := bstep (se 1 (by rfl) ⟨3238673, by rfl⟩ : syracuseStep 4318231 = 6477347) B6477347
theorem B1139831 : Blo 503794 1139831 := bstep (se 1 (by rfl) ⟨854873, by rfl⟩ : syracuseStep 1139831 = 1709747) B1709747
theorem B4678829 : Blo 503794 4678829 := bstep (se 3 (by rfl) ⟨877280, by rfl⟩ : syracuseStep 4678829 = 1754561) B1754561
theorem B1434809 : Blo 503794 1434809 := bstep (se 2 (by rfl) ⟨538053, by rfl⟩ : syracuseStep 1434809 = 1076107) B1076107
theorem B1369387 : Blo 503794 1369387 := bstep (se 1 (by rfl) ⟨1027040, by rfl⟩ : syracuseStep 1369387 = 2054081) B2054081
theorem B1140011 : Blo 503794 1140011 := bstep (se 1 (by rfl) ⟨855008, by rfl⟩ : syracuseStep 1140011 = 1710017) B1710017
theorem B7267643 : Blo 503794 7267643 := bstep (se 1 (by rfl) ⟨5450732, by rfl⟩ : syracuseStep 7267643 = 10901465) B10901465
theorem B2155835 : Blo 503794 2155835 := bstep (se 1 (by rfl) ⟨1616876, by rfl⟩ : syracuseStep 2155835 = 3233753) B3233753
theorem B1435151 : Blo 503794 1435151 := bstep (se 1 (by rfl) ⟨1076363, by rfl⟩ : syracuseStep 1435151 = 2152727) B2152727
theorem B1140371 : Blo 503794 1140371 := bstep (se 1 (by rfl) ⟨855278, by rfl⟩ : syracuseStep 1140371 = 1710557) B1710557
theorem B1140425 : Blo 503794 1140425 := bstep (se 2 (by rfl) ⟨427659, by rfl⟩ : syracuseStep 1140425 = 855319) B855319
theorem B1927097 : Blo 503794 1927097 := bstep (se 2 (by rfl) ⟨722661, by rfl⟩ : syracuseStep 1927097 = 1445323) B1445323
theorem B3827735 : Blo 503794 3827735 := bstep (se 1 (by rfl) ⟨2870801, by rfl⟩ : syracuseStep 3827735 = 5741603) B5741603
theorem B3106883 : Blo 503794 3106883 := bstep (se 1 (by rfl) ⟨2330162, by rfl⟩ : syracuseStep 3106883 = 4660325) B4660325
theorem B1370297 : Blo 503794 1370297 := bstep (se 2 (by rfl) ⟨513861, by rfl⟩ : syracuseStep 1370297 = 1027723) B1027723
theorem B5171401 : Blo 503794 5171401 := bstep (se 2 (by rfl) ⟨1939275, by rfl⟩ : syracuseStep 5171401 = 3878551) B3878551
theorem B813257 : Blo 503794 813257 := bstep (se 2 (by rfl) ⟨304971, by rfl⟩ : syracuseStep 813257 = 609943) B609943
theorem B10381553 : Blo 503794 10381553 := bstep (se 2 (by rfl) ⟨3893082, by rfl⟩ : syracuseStep 10381553 = 7786165) B7786165
theorem B2222369 : Blo 503794 2222369 := bstep (se 2 (by rfl) ⟨833388, by rfl⟩ : syracuseStep 2222369 = 1666777) B1666777
theorem B1436039 : Blo 503794 1436039 := bstep (se 1 (by rfl) ⟨1077029, by rfl⟩ : syracuseStep 1436039 = 2154059) B2154059
theorem B1141127 : Blo 503794 1141127 := bstep (se 1 (by rfl) ⟨855845, by rfl⟩ : syracuseStep 1141127 = 1711691) B1711691
theorem B5564819 : Blo 503794 5564819 := bstep (se 1 (by rfl) ⟨4173614, by rfl⟩ : syracuseStep 5564819 = 8347229) B8347229
theorem B682553 : Blo 503794 682553 := bstep (se 2 (by rfl) ⟨255957, by rfl⟩ : syracuseStep 682553 = 511915) B511915
theorem B1141307 : Blo 503794 1141307 := bstep (se 1 (by rfl) ⟨855980, by rfl⟩ : syracuseStep 1141307 = 1711961) B1711961
theorem B1436221 : Blo 503794 1436221 := bstep (se 3 (by rfl) ⟨269291, by rfl⟩ : syracuseStep 1436221 = 538583) B538583
theorem B1370771 : Blo 503794 1370771 := bstep (se 1 (by rfl) ⟨1028078, by rfl⟩ : syracuseStep 1370771 = 2056157) B2056157
theorem B9693877 : Blo 503794 9693877 := bstep (se 5 (by rfl) ⟨454400, by rfl⟩ : syracuseStep 9693877 = 908801) B908801
theorem B1141433 : Blo 503794 1141433 := bstep (se 2 (by rfl) ⟨428037, by rfl⟩ : syracuseStep 1141433 = 856075) B856075
theorem B1370891 : Blo 503794 1370891 := bstep (se 1 (by rfl) ⟨1028168, by rfl⟩ : syracuseStep 1370891 = 2056337) B2056337
theorem B1436449 : Blo 503794 1436449 := bstep (se 2 (by rfl) ⟨538668, by rfl⟩ : syracuseStep 1436449 = 1077337) B1077337
theorem B912313 : Blo 503794 912313 := bstep (se 2 (by rfl) ⟨342117, by rfl⟩ : syracuseStep 912313 = 684235) B684235
theorem B1141775 : Blo 503794 1141775 := bstep (se 1 (by rfl) ⟨856331, by rfl⟩ : syracuseStep 1141775 = 1712663) B1712663
theorem B1141793 : Blo 503794 1141793 := bstep (se 2 (by rfl) ⟨428172, by rfl⟩ : syracuseStep 1141793 = 856345) B856345
theorem B2550851 : Blo 503794 2550851 := bstep (se 1 (by rfl) ⟨1913138, by rfl⟩ : syracuseStep 2550851 = 3826277) B3826277
theorem B1436791 : Blo 503794 1436791 := bstep (se 1 (by rfl) ⟨1077593, by rfl⟩ : syracuseStep 1436791 = 2155187) B2155187
theorem B1142135 : Blo 503794 1142135 := bstep (se 1 (by rfl) ⟨856601, by rfl⟩ : syracuseStep 1142135 = 1713203) B1713203
theorem B2551175 : Blo 503794 2551175 := bstep (se 1 (by rfl) ⟨1913381, by rfl⟩ : syracuseStep 2551175 = 3826763) B3826763
theorem B1371593 : Blo 503794 1371593 := bstep (se 2 (by rfl) ⟨514347, by rfl⟩ : syracuseStep 1371593 = 1028695) B1028695
theorem B650767 : Blo 503794 650767 := bstep (se 1 (by rfl) ⟨488075, by rfl⟩ : syracuseStep 650767 = 976151) B976151
theorem B1142315 : Blo 503794 1142315 := bstep (se 1 (by rfl) ⟨856736, by rfl⟩ : syracuseStep 1142315 = 1713473) B1713473
theorem B2813849 : Blo 503794 2813849 := bstep (se 2 (by rfl) ⟨1055193, by rfl⟩ : syracuseStep 2813849 = 2110387) B2110387
theorem B684023 : Blo 503794 684023 := bstep (se 1 (by rfl) ⟨513017, by rfl⟩ : syracuseStep 684023 = 1026035) B1026035
theorem B1437725 : Blo 503794 1437725 := bstep (se 3 (by rfl) ⟨269573, by rfl⟩ : syracuseStep 1437725 = 539147) B539147
theorem B4616279 : Blo 503794 4616279 := bstep (se 1 (by rfl) ⟨3462209, by rfl⟩ : syracuseStep 4616279 = 6924419) B6924419
theorem B2912375 : Blo 503794 2912375 := bstep (se 1 (by rfl) ⟨2184281, by rfl⟩ : syracuseStep 2912375 = 4368563) B4368563
theorem B913697 : Blo 503794 913697 := bstep (se 2 (by rfl) ⟨342636, by rfl⟩ : syracuseStep 913697 = 685273) B685273
theorem B1438067 : Blo 503794 1438067 := bstep (se 1 (by rfl) ⟨1078550, by rfl⟩ : syracuseStep 1438067 = 2157101) B2157101
theorem B5763473 : Blo 503794 5763473 := bstep (se 2 (by rfl) ⟨2161302, by rfl⟩ : syracuseStep 5763473 = 4322605) B4322605
theorem B4452893 : Blo 503794 4452893 := bstep (se 3 (by rfl) ⟨834917, by rfl⟩ : syracuseStep 4452893 = 1669835) B1669835
theorem B684715 : Blo 503794 684715 := bstep (se 1 (by rfl) ⟨513536, by rfl⟩ : syracuseStep 684715 = 1027073) B1027073
theorem B2454209 : Blo 503794 2454209 := bstep (se 2 (by rfl) ⟨920328, by rfl⟩ : syracuseStep 2454209 = 1840657) B1840657
theorem B1438523 : Blo 503794 1438523 := bstep (se 1 (by rfl) ⟨1078892, by rfl⟩ : syracuseStep 1438523 = 2157785) B2157785
theorem B717769 : Blo 503794 717769 := bstep (se 2 (by rfl) ⟨269163, by rfl⟩ : syracuseStep 717769 = 538327) B538327
theorem B2422163 : Blo 503794 2422163 := bstep (se 1 (by rfl) ⟨1816622, by rfl⟩ : syracuseStep 2422163 = 3633245) B3633245
theorem B1734173 : Blo 503794 1734173 := bstep (se 3 (by rfl) ⟨325157, by rfl⟩ : syracuseStep 1734173 = 650315) B650315
theorem B1275527 : Blo 503794 1275527 := bstep (se 1 (by rfl) ⟨956645, by rfl⟩ : syracuseStep 1275527 = 1913291) B1913291
theorem B1275659 : Blo 503794 1275659 := bstep (se 1 (by rfl) ⟨956744, by rfl⟩ : syracuseStep 1275659 = 1913489) B1913489
theorem B1701647 : Blo 503794 1701647 := bstep (se 1 (by rfl) ⟨1276235, by rfl⟩ : syracuseStep 1701647 = 2552471) B2552471
theorem B2586401 : Blo 503794 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B5339033 : Blo 503794 5339033 := bstep (se 2 (by rfl) ⟨2002137, by rfl⟩ : syracuseStep 5339033 = 4004275) B4004275
theorem B1701917 : Blo 503794 1701917 := bstep (se 3 (by rfl) ⟨319109, by rfl⟩ : syracuseStep 1701917 = 638219) B638219
theorem B2160877 : Blo 503794 2160877 := bstep (se 3 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 2160877 = 810329) B810329
theorem B1276175 : Blo 503794 1276175 := bstep (se 1 (by rfl) ⟨957131, by rfl⟩ : syracuseStep 1276175 = 1914263) B1914263
theorem B24574225 : Blo 503794 24574225 := bstep (se 2 (by rfl) ⟨9215334, by rfl⟩ : syracuseStep 24574225 = 18430669) B18430669
theorem B1538423 : Blo 503794 1538423 := bstep (se 1 (by rfl) ⟨1153817, by rfl⟩ : syracuseStep 1538423 = 2307635) B2307635
theorem B1276307 : Blo 503794 1276307 := bstep (se 1 (by rfl) ⟨957230, by rfl⟩ : syracuseStep 1276307 = 1914461) B1914461
theorem B2423357 : Blo 503794 2423357 := bstep (se 3 (by rfl) ⟨454379, by rfl⟩ : syracuseStep 2423357 = 908759) B908759
theorem B1210967 : Blo 503794 1210967 := bstep (se 1 (by rfl) ⟨908225, by rfl⟩ : syracuseStep 1210967 = 1816451) B1816451
theorem B850567 : Blo 503794 850567 := bstep (se 1 (by rfl) ⟨637925, by rfl⟩ : syracuseStep 850567 = 1275851) B1275851
theorem B3242753 : Blo 503794 3242753 := bstep (se 2 (by rfl) ⟨1216032, by rfl⟩ : syracuseStep 3242753 = 2432065) B2432065
theorem B2554739 : Blo 503794 2554739 := bstep (se 1 (by rfl) ⟨1916054, by rfl⟩ : syracuseStep 2554739 = 3832109) B3832109
theorem B2882627 : Blo 503794 2882627 := bstep (se 1 (by rfl) ⟨2161970, by rfl⟩ : syracuseStep 2882627 = 4323941) B4323941
theorem B10910807 : Blo 503794 10910807 := bstep (se 1 (by rfl) ⟨8183105, by rfl⟩ : syracuseStep 10910807 = 16366211) B16366211
theorem B4324589 : Blo 503794 4324589 := bstep (se 3 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 4324589 = 1621721) B1621721
theorem B5766389 : Blo 503794 5766389 := bstep (se 5 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 5766389 = 540599) B540599
theorem B851215 : Blo 503794 851215 := bstep (se 1 (by rfl) ⟨638411, by rfl⟩ : syracuseStep 851215 = 1276823) B1276823
theorem B2555225 : Blo 503794 2555225 := bstep (se 2 (by rfl) ⟨958209, by rfl⟩ : syracuseStep 2555225 = 1916419) B1916419
theorem B720247 : Blo 503794 720247 := bstep (se 1 (by rfl) ⟨540185, by rfl⟩ : syracuseStep 720247 = 1080371) B1080371
theorem B1703321 : Blo 503794 1703321 := bstep (se 2 (by rfl) ⟨638745, by rfl⟩ : syracuseStep 1703321 = 1277491) B1277491
theorem B1277441 : Blo 503794 1277441 := bstep (se 2 (by rfl) ⟨479040, by rfl⟩ : syracuseStep 1277441 = 958081) B958081
theorem B1441415 : Blo 503794 1441415 := bstep (se 1 (by rfl) ⟨1081061, by rfl⟩ : syracuseStep 1441415 = 2162123) B2162123
theorem B720571 : Blo 503794 720571 := bstep (se 1 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 720571 = 1080857) B1080857
theorem B2588431 : Blo 503794 2588431 := bstep (se 1 (by rfl) ⟨1941323, by rfl⟩ : syracuseStep 2588431 = 3882647) B3882647
theorem B851755 : Blo 503794 851755 := bstep (se 1 (by rfl) ⟨638816, by rfl⟩ : syracuseStep 851755 = 1277633) B1277633
theorem B1277815 : Blo 503794 1277815 := bstep (se 1 (by rfl) ⟨958361, by rfl⟩ : syracuseStep 1277815 = 1916723) B1916723
theorem B851897 : Blo 503794 851897 := bstep (se 2 (by rfl) ⟨319461, by rfl⟩ : syracuseStep 851897 = 638923) B638923
theorem B852025 : Blo 503794 852025 := bstep (se 2 (by rfl) ⟨319509, by rfl⟩ : syracuseStep 852025 = 639019) B639019
theorem B1441871 : Blo 503794 1441871 := bstep (se 1 (by rfl) ⟨1081403, by rfl⟩ : syracuseStep 1441871 = 2162807) B2162807
theorem B852167 : Blo 503794 852167 := bstep (se 1 (by rfl) ⟨639125, by rfl⟩ : syracuseStep 852167 = 1278251) B1278251
theorem B1540343 : Blo 503794 1540343 := bstep (se 1 (by rfl) ⟨1155257, by rfl⟩ : syracuseStep 1540343 = 2310515) B2310515
theorem B852329 : Blo 503794 852329 := bstep (se 2 (by rfl) ⟨319623, by rfl⟩ : syracuseStep 852329 = 639247) B639247
theorem B852727 : Blo 503794 852727 := bstep (se 1 (by rfl) ⟨639545, by rfl⟩ : syracuseStep 852727 = 1279091) B1279091
theorem B1704887 : Blo 503794 1704887 := bstep (se 1 (by rfl) ⟨1278665, by rfl⟩ : syracuseStep 1704887 = 2557331) B2557331
theorem B852923 : Blo 503794 852923 := bstep (se 1 (by rfl) ⟨639692, by rfl⟩ : syracuseStep 852923 = 1279385) B1279385
theorem B853031 : Blo 503794 853031 := bstep (se 1 (by rfl) ⟨639773, by rfl⟩ : syracuseStep 853031 = 1279547) B1279547
theorem B1442873 : Blo 503794 1442873 := bstep (se 2 (by rfl) ⟨541077, by rfl⟩ : syracuseStep 1442873 = 1082155) B1082155
theorem B2557007 : Blo 503794 2557007 := bstep (se 1 (by rfl) ⟨1917755, by rfl⟩ : syracuseStep 2557007 = 3835511) B3835511
theorem B1279223 : Blo 503794 1279223 := bstep (se 1 (by rfl) ⟨959417, by rfl⟩ : syracuseStep 1279223 = 1918835) B1918835
theorem B853321 : Blo 503794 853321 := bstep (se 2 (by rfl) ⟨319995, by rfl⟩ : syracuseStep 853321 = 639991) B639991
theorem B8750429 : Blo 503794 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B853355 : Blo 503794 853355 := bstep (se 1 (by rfl) ⟨640016, by rfl⟩ : syracuseStep 853355 = 1280033) B1280033
theorem B1705481 : Blo 503794 1705481 := bstep (se 2 (by rfl) ⟨639555, by rfl⟩ : syracuseStep 1705481 = 1279111) B1279111
theorem B1541729 : Blo 503794 1541729 := bstep (se 2 (by rfl) ⟨578148, by rfl⟩ : syracuseStep 1541729 = 1156297) B1156297
theorem B2557655 : Blo 503794 2557655 := bstep (se 1 (by rfl) ⟨1918241, by rfl⟩ : syracuseStep 2557655 = 3836483) B3836483
theorem B853753 : Blo 503794 853753 := bstep (se 2 (by rfl) ⟨320157, by rfl⟩ : syracuseStep 853753 = 640315) B640315
theorem B4622123 : Blo 503794 4622123 := bstep (se 1 (by rfl) ⟨3466592, by rfl⟩ : syracuseStep 4622123 = 6933185) B6933185
theorem B2197343 : Blo 503794 2197343 := bstep (se 1 (by rfl) ⟨1648007, by rfl⟩ : syracuseStep 2197343 = 3296015) B3296015
theorem B854023 : Blo 503794 854023 := bstep (se 1 (by rfl) ⟨640517, by rfl⟩ : syracuseStep 854023 = 1281035) B1281035
theorem B5769305 : Blo 503794 5769305 := bstep (se 2 (by rfl) ⟨2163489, by rfl⟩ : syracuseStep 5769305 = 4326979) B4326979
theorem B3639563 : Blo 503794 3639563 := bstep (se 1 (by rfl) ⟨2729672, by rfl⟩ : syracuseStep 3639563 = 5459345) B5459345
theorem B2885975 : Blo 503794 2885975 := bstep (se 1 (by rfl) ⟨2164481, by rfl⟩ : syracuseStep 2885975 = 4328963) B4328963
theorem B1706345 : Blo 503794 1706345 := bstep (se 2 (by rfl) ⟨639879, by rfl⟩ : syracuseStep 1706345 = 1279759) B1279759
theorem B756143 : Blo 503794 756143 := bstep (se 1 (by rfl) ⟨567107, by rfl⟩ : syracuseStep 756143 = 1134215) B1134215
theorem B854455 : Blo 503794 854455 := bstep (se 1 (by rfl) ⟨640841, by rfl⟩ : syracuseStep 854455 = 1281683) B1281683
theorem B756233 : Blo 503794 756233 := bstep (se 2 (by rfl) ⟨283587, by rfl⟩ : syracuseStep 756233 = 567175) B567175
theorem B756263 : Blo 503794 756263 := bstep (se 1 (by rfl) ⟨567197, by rfl⟩ : syracuseStep 756263 = 1134395) B1134395
theorem B66292343 : Blo 503794 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B756347 : Blo 503794 756347 := bstep (se 1 (by rfl) ⟨567260, by rfl⟩ : syracuseStep 756347 = 1134521) B1134521
theorem B854651 : Blo 503794 854651 := bstep (se 1 (by rfl) ⟨640988, by rfl⟩ : syracuseStep 854651 = 1281977) B1281977
theorem B1280711 : Blo 503794 1280711 := bstep (se 1 (by rfl) ⟨960533, by rfl⟩ : syracuseStep 1280711 = 1921067) B1921067
theorem B756473 : Blo 503794 756473 := bstep (se 2 (by rfl) ⟨283677, by rfl⟩ : syracuseStep 756473 = 567355) B567355
theorem B756575 : Blo 503794 756575 := bstep (se 1 (by rfl) ⟨567431, by rfl⟩ : syracuseStep 756575 = 1134863) B1134863
theorem B756587 : Blo 503794 756587 := bstep (se 1 (by rfl) ⟨567440, by rfl⟩ : syracuseStep 756587 = 1134881) B1134881
theorem B1706939 : Blo 503794 1706939 := bstep (se 1 (by rfl) ⟨1280204, by rfl⟩ : syracuseStep 1706939 = 2560409) B2560409
theorem B855049 : Blo 503794 855049 := bstep (se 2 (by rfl) ⟨320643, by rfl⟩ : syracuseStep 855049 = 641287) B641287
theorem B756815 : Blo 503794 756815 := bstep (se 1 (by rfl) ⟨567611, by rfl⟩ : syracuseStep 756815 = 1135223) B1135223
theorem B855211 : Blo 503794 855211 := bstep (se 1 (by rfl) ⟨641408, by rfl⟩ : syracuseStep 855211 = 1282817) B1282817
theorem B756935 : Blo 503794 756935 := bstep (se 1 (by rfl) ⟨567701, by rfl⟩ : syracuseStep 756935 = 1135403) B1135403
theorem B6917413 : Blo 503794 6917413 := bstep (se 4 (by rfl) ⟨648507, by rfl⟩ : syracuseStep 6917413 = 1297015) B1297015
theorem B757097 : Blo 503794 757097 := bstep (se 2 (by rfl) ⟨283911, by rfl⟩ : syracuseStep 757097 = 567823) B567823
theorem B1543529 : Blo 503794 1543529 := bstep (se 2 (by rfl) ⟨578823, by rfl⟩ : syracuseStep 1543529 = 1157647) B1157647
theorem B757175 : Blo 503794 757175 := bstep (se 1 (by rfl) ⟨567881, by rfl⟩ : syracuseStep 757175 = 1135763) B1135763
theorem B757211 : Blo 503794 757211 := bstep (se 1 (by rfl) ⟨567908, by rfl⟩ : syracuseStep 757211 = 1135817) B1135817
theorem B855515 : Blo 503794 855515 := bstep (se 1 (by rfl) ⟨641636, by rfl⟩ : syracuseStep 855515 = 1283273) B1283273
theorem B855751 : Blo 503794 855751 := bstep (se 1 (by rfl) ⟨641813, by rfl⟩ : syracuseStep 855751 = 1283627) B1283627
theorem B6459101 : Blo 503794 6459101 := bstep (se 3 (by rfl) ⟨1211081, by rfl⟩ : syracuseStep 6459101 = 2422163) B2422163
theorem B1281865 : Blo 503794 1281865 := bstep (se 2 (by rfl) ⟨480699, by rfl⟩ : syracuseStep 1281865 = 961399) B961399
theorem B855913 : Blo 503794 855913 := bstep (se 2 (by rfl) ⟨320967, by rfl⟩ : syracuseStep 855913 = 641935) B641935
theorem B1216417 : Blo 503794 1216417 := bstep (se 2 (by rfl) ⟨456156, by rfl⟩ : syracuseStep 1216417 = 912313) B912313
theorem B757679 : Blo 503794 757679 := bstep (se 1 (by rfl) ⟨568259, by rfl⟩ : syracuseStep 757679 = 1136519) B1136519
theorem B757769 : Blo 503794 757769 := bstep (se 2 (by rfl) ⟨284163, by rfl⟩ : syracuseStep 757769 = 568327) B568327
theorem B757799 : Blo 503794 757799 := bstep (se 1 (by rfl) ⟨568349, by rfl⟩ : syracuseStep 757799 = 1136699) B1136699
theorem B4427891 : Blo 503794 4427891 := bstep (se 1 (by rfl) ⟨3320918, by rfl⟩ : syracuseStep 4427891 = 6641837) B6641837
theorem B757883 : Blo 503794 757883 := bstep (se 1 (by rfl) ⟨568412, by rfl⟩ : syracuseStep 757883 = 1136825) B1136825
theorem B758009 : Blo 503794 758009 := bstep (se 2 (by rfl) ⟨284253, by rfl⟩ : syracuseStep 758009 = 568507) B568507
theorem B758111 : Blo 503794 758111 := bstep (se 1 (by rfl) ⟨568583, by rfl⟩ : syracuseStep 758111 = 1137167) B1137167
theorem B758123 : Blo 503794 758123 := bstep (se 1 (by rfl) ⟨568592, by rfl⟩ : syracuseStep 758123 = 1137185) B1137185
theorem B856507 : Blo 503794 856507 := bstep (se 1 (by rfl) ⟨642380, by rfl⟩ : syracuseStep 856507 = 1284761) B1284761
theorem B856615 : Blo 503794 856615 := bstep (se 1 (by rfl) ⟨642461, by rfl⟩ : syracuseStep 856615 = 1284923) B1284923
theorem B2560571 : Blo 503794 2560571 := bstep (se 1 (by rfl) ⟨1920428, by rfl⟩ : syracuseStep 2560571 = 3840857) B3840857
theorem B758351 : Blo 503794 758351 := bstep (se 1 (by rfl) ⟨568763, by rfl⟩ : syracuseStep 758351 = 1137527) B1137527
theorem B1708667 : Blo 503794 1708667 := bstep (se 1 (by rfl) ⟨1281500, by rfl⟩ : syracuseStep 1708667 = 2563001) B2563001
theorem B758471 : Blo 503794 758471 := bstep (se 1 (by rfl) ⟨568853, by rfl⟩ : syracuseStep 758471 = 1137707) B1137707
theorem B1708829 : Blo 503794 1708829 := bstep (se 3 (by rfl) ⟨320405, by rfl⟩ : syracuseStep 1708829 = 640811) B640811
theorem B758633 : Blo 503794 758633 := bstep (se 2 (by rfl) ⟨284487, by rfl⟩ : syracuseStep 758633 = 568975) B568975
theorem B758711 : Blo 503794 758711 := bstep (se 1 (by rfl) ⟨569033, by rfl⟩ : syracuseStep 758711 = 1138067) B1138067
theorem B1282999 : Blo 503794 1282999 := bstep (se 1 (by rfl) ⟨962249, by rfl⟩ : syracuseStep 1282999 = 1924499) B1924499
theorem B758747 : Blo 503794 758747 := bstep (se 1 (by rfl) ⟨569060, by rfl⟩ : syracuseStep 758747 = 1138121) B1138121
theorem B2561219 : Blo 503794 2561219 := bstep (se 1 (by rfl) ⟨1920914, by rfl⟩ : syracuseStep 2561219 = 3841829) B3841829
theorem B2168207 : Blo 503794 2168207 := bstep (se 1 (by rfl) ⟨1626155, by rfl⟩ : syracuseStep 2168207 = 3252311) B3252311
theorem B759215 : Blo 503794 759215 := bstep (se 1 (by rfl) ⟨569411, by rfl⟩ : syracuseStep 759215 = 1138823) B1138823
theorem B1709531 : Blo 503794 1709531 := bstep (se 1 (by rfl) ⟨1282148, by rfl⟩ : syracuseStep 1709531 = 2564297) B2564297
theorem B759305 : Blo 503794 759305 := bstep (se 2 (by rfl) ⟨284739, by rfl⟩ : syracuseStep 759305 = 569479) B569479
theorem B759335 : Blo 503794 759335 := bstep (se 1 (by rfl) ⟨569501, by rfl⟩ : syracuseStep 759335 = 1139003) B1139003
theorem B759419 : Blo 503794 759419 := bstep (se 1 (by rfl) ⟨569564, by rfl⟩ : syracuseStep 759419 = 1139129) B1139129
theorem B759545 : Blo 503794 759545 := bstep (se 2 (by rfl) ⟨284829, by rfl⟩ : syracuseStep 759545 = 569659) B569659
theorem B759647 : Blo 503794 759647 := bstep (se 1 (by rfl) ⟨569735, by rfl⟩ : syracuseStep 759647 = 1139471) B1139471
theorem B759659 : Blo 503794 759659 := bstep (se 1 (by rfl) ⟨569744, by rfl⟩ : syracuseStep 759659 = 1139489) B1139489
theorem B2889665 : Blo 503794 2889665 := bstep (se 2 (by rfl) ⟨1083624, by rfl⟩ : syracuseStep 2889665 = 2167249) B2167249
theorem B759887 : Blo 503794 759887 := bstep (se 1 (by rfl) ⟨569915, by rfl⟩ : syracuseStep 759887 = 1139831) B1139831
theorem B3119219 : Blo 503794 3119219 := bstep (se 1 (by rfl) ⟨2339414, by rfl⟩ : syracuseStep 3119219 = 4678829) B4678829
theorem B956539 : Blo 503794 956539 := bstep (se 1 (by rfl) ⟨717404, by rfl⟩ : syracuseStep 956539 = 1434809) B1434809
theorem B1710233 : Blo 503794 1710233 := bstep (se 2 (by rfl) ⟨641337, by rfl⟩ : syracuseStep 1710233 = 1282675) B1282675
theorem B760007 : Blo 503794 760007 := bstep (se 1 (by rfl) ⟨570005, by rfl⟩ : syracuseStep 760007 = 1140011) B1140011
theorem B3447101 : Blo 503794 3447101 := bstep (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) B1292663
theorem B956767 : Blo 503794 956767 := bstep (se 1 (by rfl) ⟨717575, by rfl⟩ : syracuseStep 956767 = 1435151) B1435151
theorem B760169 : Blo 503794 760169 := bstep (se 2 (by rfl) ⟨285063, by rfl⟩ : syracuseStep 760169 = 570127) B570127
theorem B1284457 : Blo 503794 1284457 := bstep (se 2 (by rfl) ⟨481671, by rfl⟩ : syracuseStep 1284457 = 963343) B963343
theorem B760247 : Blo 503794 760247 := bstep (se 1 (by rfl) ⟨570185, by rfl⟩ : syracuseStep 760247 = 1140371) B1140371
theorem B760283 : Blo 503794 760283 := bstep (se 1 (by rfl) ⟨570212, by rfl⟩ : syracuseStep 760283 = 1140425) B1140425
theorem B957025 : Blo 503794 957025 := bstep (se 2 (by rfl) ⟨358884, by rfl⟩ : syracuseStep 957025 = 717769) B717769
theorem B1284731 : Blo 503794 1284731 := bstep (se 1 (by rfl) ⟨963548, by rfl⟩ : syracuseStep 1284731 = 1927097) B1927097
theorem B2071255 : Blo 503794 2071255 := bstep (se 1 (by rfl) ⟨1553441, by rfl⟩ : syracuseStep 2071255 = 3106883) B3106883
theorem B6921035 : Blo 503794 6921035 := bstep (se 1 (by rfl) ⟨5190776, by rfl⟩ : syracuseStep 6921035 = 10381553) B10381553
theorem B1481579 : Blo 503794 1481579 := bstep (se 1 (by rfl) ⟨1111184, by rfl⟩ : syracuseStep 1481579 = 2222369) B2222369
theorem B957359 : Blo 503794 957359 := bstep (se 1 (by rfl) ⟨718019, by rfl⟩ : syracuseStep 957359 = 1436039) B1436039
theorem B760751 : Blo 503794 760751 := bstep (se 1 (by rfl) ⟨570563, by rfl⟩ : syracuseStep 760751 = 1141127) B1141127
theorem B760841 : Blo 503794 760841 := bstep (se 2 (by rfl) ⟨285315, by rfl⟩ : syracuseStep 760841 = 570631) B570631
theorem B760871 : Blo 503794 760871 := bstep (se 1 (by rfl) ⟨570653, by rfl⟩ : syracuseStep 760871 = 1141307) B1141307
theorem B760955 : Blo 503794 760955 := bstep (se 1 (by rfl) ⟨570716, by rfl⟩ : syracuseStep 760955 = 1141433) B1141433
theorem B1973443 : Blo 503794 1973443 := bstep (se 1 (by rfl) ⟨1480082, by rfl⟩ : syracuseStep 1973443 = 2960165) B2960165
theorem B761081 : Blo 503794 761081 := bstep (se 2 (by rfl) ⟨285405, by rfl⟩ : syracuseStep 761081 = 570811) B570811
theorem B1711421 : Blo 503794 1711421 := bstep (se 3 (by rfl) ⟨320891, by rfl⟩ : syracuseStep 1711421 = 641783) B641783
theorem B761183 : Blo 503794 761183 := bstep (se 1 (by rfl) ⟨570887, by rfl⟩ : syracuseStep 761183 = 1141775) B1141775
theorem B761195 : Blo 503794 761195 := bstep (se 1 (by rfl) ⟨570896, by rfl⟩ : syracuseStep 761195 = 1141793) B1141793
theorem B761423 : Blo 503794 761423 := bstep (se 1 (by rfl) ⟨571067, by rfl⟩ : syracuseStep 761423 = 1142135) B1142135
theorem B761543 : Blo 503794 761543 := bstep (se 1 (by rfl) ⟨571157, by rfl⟩ : syracuseStep 761543 = 1142315) B1142315
theorem B5775137 : Blo 503794 5775137 := bstep (se 2 (by rfl) ⟨2165676, by rfl⟩ : syracuseStep 5775137 = 4331353) B4331353
theorem B3252001 : Blo 503794 3252001 := bstep (se 2 (by rfl) ⟨1219500, by rfl⟩ : syracuseStep 3252001 = 2439001) B2439001
theorem B1875899 : Blo 503794 1875899 := bstep (se 1 (by rfl) ⟨1406924, by rfl⟩ : syracuseStep 1875899 = 2813849) B2813849
theorem B958483 : Blo 503794 958483 := bstep (se 1 (by rfl) ⟨718862, by rfl⟩ : syracuseStep 958483 = 1437725) B1437725
theorem B1941583 : Blo 503794 1941583 := bstep (se 1 (by rfl) ⟨1456187, by rfl⟩ : syracuseStep 1941583 = 2912375) B2912375
theorem B1712285 : Blo 503794 1712285 := bstep (se 3 (by rfl) ⟨321053, by rfl⟩ : syracuseStep 1712285 = 642107) B642107
theorem B958711 : Blo 503794 958711 := bstep (se 1 (by rfl) ⟨719033, by rfl⟩ : syracuseStep 958711 = 1438067) B1438067
theorem B3842315 : Blo 503794 3842315 := bstep (se 1 (by rfl) ⟨2881736, by rfl⟩ : syracuseStep 3842315 = 5763473) B5763473
theorem B959015 : Blo 503794 959015 := bstep (se 1 (by rfl) ⟨719261, by rfl⟩ : syracuseStep 959015 = 1438523) B1438523
theorem B8233645 : Blo 503794 8233645 := bstep (se 3 (by rfl) ⟨1543808, by rfl⟩ : syracuseStep 8233645 = 3087617) B3087617
theorem B1712825 : Blo 503794 1712825 := bstep (se 2 (by rfl) ⟨642309, by rfl⟩ : syracuseStep 1712825 = 1284619) B1284619
theorem B1156115 : Blo 503794 1156115 := bstep (se 1 (by rfl) ⟨867086, by rfl⟩ : syracuseStep 1156115 = 1734173) B1734173
theorem B1713419 : Blo 503794 1713419 := bstep (se 1 (by rfl) ⟨1285064, by rfl⟩ : syracuseStep 1713419 = 2570129) B2570129
theorem B1713689 : Blo 503794 1713689 := bstep (se 2 (by rfl) ⟨642633, by rfl⟩ : syracuseStep 1713689 = 1285267) B1285267
theorem B1025615 : Blo 503794 1025615 := bstep (se 1 (by rfl) ⟨769211, by rfl⟩ : syracuseStep 1025615 = 1538423) B1538423
theorem B2565755 : Blo 503794 2565755 := bstep (se 1 (by rfl) ⟨1924316, by rfl⟩ : syracuseStep 2565755 = 3848633) B3848633
theorem B3843773 : Blo 503794 3843773 := bstep (se 3 (by rfl) ⟨720707, by rfl⟩ : syracuseStep 3843773 = 1441415) B1441415
theorem B1615571 : Blo 503794 1615571 := bstep (se 1 (by rfl) ⟨1211678, by rfl⟩ : syracuseStep 1615571 = 2423357) B2423357
theorem B960329 : Blo 503794 960329 := bstep (se 2 (by rfl) ⟨360123, by rfl⟩ : syracuseStep 960329 = 720247) B720247
theorem B3844259 : Blo 503794 3844259 := bstep (se 1 (by rfl) ⟨2883194, by rfl⟩ : syracuseStep 3844259 = 5766389) B5766389
theorem B6564077 : Blo 503794 6564077 := bstep (se 3 (by rfl) ⟨1230764, by rfl⟩ : syracuseStep 6564077 = 2461529) B2461529
theorem B960761 : Blo 503794 960761 := bstep (se 2 (by rfl) ⟨360285, by rfl⟩ : syracuseStep 960761 = 720571) B720571
theorem B3451241 : Blo 503794 3451241 := bstep (se 2 (by rfl) ⟨1294215, by rfl⟩ : syracuseStep 3451241 = 2588431) B2588431
theorem B567931 : Blo 503794 567931 := bstep (se 1 (by rfl) ⟨425948, by rfl⟩ : syracuseStep 567931 = 851897) B851897
theorem B568399 : Blo 503794 568399 := bstep (se 1 (by rfl) ⟨426299, by rfl⟩ : syracuseStep 568399 = 852599) B852599
theorem B568795 : Blo 503794 568795 := bstep (se 1 (by rfl) ⟨426596, by rfl⟩ : syracuseStep 568795 = 853193) B853193
theorem B1027591 : Blo 503794 1027591 := bstep (se 1 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 1027591 = 1541387) B1541387
theorem B962219 : Blo 503794 962219 := bstep (se 1 (by rfl) ⟨721664, by rfl⟩ : syracuseStep 962219 = 1443329) B1443329
theorem B2731769 : Blo 503794 2731769 := bstep (se 2 (by rfl) ⟨1024413, by rfl⟩ : syracuseStep 2731769 = 2048827) B2048827
theorem B569263 : Blo 503794 569263 := bstep (se 1 (by rfl) ⟨426947, by rfl⟩ : syracuseStep 569263 = 853895) B853895
theorem B503847 : Blo 503794 503847 := bstep (se 1 (by rfl) ⟨377885, by rfl⟩ : syracuseStep 503847 = 755771) B755771
theorem B962599 : Blo 503794 962599 := bstep (se 1 (by rfl) ⟨721949, by rfl⟩ : syracuseStep 962599 = 1443899) B1443899
theorem B503887 : Blo 503794 503887 := bstep (se 1 (by rfl) ⟨377915, by rfl⟩ : syracuseStep 503887 = 755831) B755831
theorem B503903 : Blo 503794 503903 := bstep (se 1 (by rfl) ⟨377927, by rfl⟩ : syracuseStep 503903 = 755855) B755855
theorem B2437235 : Blo 503794 2437235 := bstep (se 1 (by rfl) ⟨1827926, by rfl⟩ : syracuseStep 2437235 = 3655853) B3655853
theorem B503931 : Blo 503794 503931 := bstep (se 1 (by rfl) ⟨377948, by rfl⟩ : syracuseStep 503931 = 755897) B755897
theorem B2044061 : Blo 503794 2044061 := bstep (se 3 (by rfl) ⟨383261, by rfl⟩ : syracuseStep 2044061 = 766523) B766523
theorem B8335523 : Blo 503794 8335523 := bstep (se 1 (by rfl) ⟨6251642, by rfl⟩ : syracuseStep 8335523 = 12503285) B12503285
theorem B1913003 : Blo 503794 1913003 := bstep (se 1 (by rfl) ⟨1434752, by rfl⟩ : syracuseStep 1913003 = 2869505) B2869505
theorem B503983 : Blo 503794 503983 := bstep (se 1 (by rfl) ⟨377987, by rfl⟩ : syracuseStep 503983 = 755975) B755975
theorem B504007 : Blo 503794 504007 := bstep (se 1 (by rfl) ⟨378005, by rfl⟩ : syracuseStep 504007 = 756011) B756011
theorem B962759 : Blo 503794 962759 := bstep (se 1 (by rfl) ⟨722069, by rfl⟩ : syracuseStep 962759 = 1444139) B1444139
theorem B504027 : Blo 503794 504027 := bstep (se 1 (by rfl) ⟨378020, by rfl⟩ : syracuseStep 504027 = 756041) B756041
theorem B504103 : Blo 503794 504103 := bstep (se 1 (by rfl) ⟨378077, by rfl⟩ : syracuseStep 504103 = 756155) B756155
theorem B3649853 : Blo 503794 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B2568509 : Blo 503794 2568509 := bstep (se 3 (by rfl) ⟨481595, by rfl⟩ : syracuseStep 2568509 = 963191) B963191
theorem B504143 : Blo 503794 504143 := bstep (se 1 (by rfl) ⟨378107, by rfl⟩ : syracuseStep 504143 = 756215) B756215
theorem B504159 : Blo 503794 504159 := bstep (se 1 (by rfl) ⟨378119, by rfl⟩ : syracuseStep 504159 = 756239) B756239
theorem B569695 : Blo 503794 569695 := bstep (se 1 (by rfl) ⟨427271, by rfl⟩ : syracuseStep 569695 = 854543) B854543
theorem B504187 : Blo 503794 504187 := bstep (se 1 (by rfl) ⟨378140, by rfl⟩ : syracuseStep 504187 = 756281) B756281
theorem B504239 : Blo 503794 504239 := bstep (se 1 (by rfl) ⟨378179, by rfl⟩ : syracuseStep 504239 = 756359) B756359
theorem B504263 : Blo 503794 504263 := bstep (se 1 (by rfl) ⟨378197, by rfl⟩ : syracuseStep 504263 = 756395) B756395
theorem B504283 : Blo 503794 504283 := bstep (se 1 (by rfl) ⟨378212, by rfl⟩ : syracuseStep 504283 = 756425) B756425
theorem B3846689 : Blo 503794 3846689 := bstep (se 2 (by rfl) ⟨1442508, by rfl⟩ : syracuseStep 3846689 = 2885017) B2885017
theorem B504359 : Blo 503794 504359 := bstep (se 1 (by rfl) ⟨378269, by rfl⟩ : syracuseStep 504359 = 756539) B756539
theorem B504399 : Blo 503794 504399 := bstep (se 1 (by rfl) ⟨378299, by rfl⟩ : syracuseStep 504399 = 756599) B756599
theorem B504415 : Blo 503794 504415 := bstep (se 1 (by rfl) ⟨378311, by rfl⟩ : syracuseStep 504415 = 756623) B756623
theorem B504443 : Blo 503794 504443 := bstep (se 1 (by rfl) ⟨378332, by rfl⟩ : syracuseStep 504443 = 756665) B756665
theorem B504495 : Blo 503794 504495 := bstep (se 1 (by rfl) ⟨378371, by rfl⟩ : syracuseStep 504495 = 756743) B756743
theorem B504519 : Blo 503794 504519 := bstep (se 1 (by rfl) ⟨378389, by rfl⟩ : syracuseStep 504519 = 756779) B756779
theorem B570055 : Blo 503794 570055 := bstep (se 1 (by rfl) ⟨427541, by rfl⟩ : syracuseStep 570055 = 855083) B855083
theorem B504539 : Blo 503794 504539 := bstep (se 1 (by rfl) ⟨378404, by rfl⟩ : syracuseStep 504539 = 756809) B756809
theorem B504615 : Blo 503794 504615 := bstep (se 1 (by rfl) ⟨378461, by rfl⟩ : syracuseStep 504615 = 756923) B756923
theorem B2044739 : Blo 503794 2044739 := bstep (se 1 (by rfl) ⟨1533554, by rfl⟩ : syracuseStep 2044739 = 3067109) B3067109
theorem B504655 : Blo 503794 504655 := bstep (se 1 (by rfl) ⟨378491, by rfl⟩ : syracuseStep 504655 = 756983) B756983
theorem B504671 : Blo 503794 504671 := bstep (se 1 (by rfl) ⟨378503, by rfl⟩ : syracuseStep 504671 = 757007) B757007
theorem B2470763 : Blo 503794 2470763 := bstep (se 1 (by rfl) ⟨1853072, by rfl⟩ : syracuseStep 2470763 = 3706145) B3706145
theorem B504699 : Blo 503794 504699 := bstep (se 1 (by rfl) ⟨378524, by rfl⟩ : syracuseStep 504699 = 757049) B757049
theorem B504751 : Blo 503794 504751 := bstep (se 1 (by rfl) ⟨378563, by rfl⟩ : syracuseStep 504751 = 757127) B757127
theorem B504775 : Blo 503794 504775 := bstep (se 1 (by rfl) ⟨378581, by rfl⟩ : syracuseStep 504775 = 757163) B757163
theorem B504795 : Blo 503794 504795 := bstep (se 1 (by rfl) ⟨378596, by rfl⟩ : syracuseStep 504795 = 757193) B757193
theorem B504871 : Blo 503794 504871 := bstep (se 1 (by rfl) ⟨378653, by rfl⟩ : syracuseStep 504871 = 757307) B757307
theorem B504911 : Blo 503794 504911 := bstep (se 1 (by rfl) ⟨378683, by rfl⟩ : syracuseStep 504911 = 757367) B757367
theorem B504927 : Blo 503794 504927 := bstep (se 1 (by rfl) ⟨378695, by rfl⟩ : syracuseStep 504927 = 757391) B757391
theorem B504955 : Blo 503794 504955 := bstep (se 1 (by rfl) ⟨378716, by rfl⟩ : syracuseStep 504955 = 757433) B757433
theorem B505007 : Blo 503794 505007 := bstep (se 1 (by rfl) ⟨378755, by rfl⟩ : syracuseStep 505007 = 757511) B757511
theorem B505031 : Blo 503794 505031 := bstep (se 1 (by rfl) ⟨378773, by rfl⟩ : syracuseStep 505031 = 757547) B757547
theorem B505051 : Blo 503794 505051 := bstep (se 1 (by rfl) ⟨378788, by rfl⟩ : syracuseStep 505051 = 757577) B757577
theorem B505127 : Blo 503794 505127 := bstep (se 1 (by rfl) ⟨378845, by rfl⟩ : syracuseStep 505127 = 757691) B757691
theorem B1619261 : Blo 503794 1619261 := bstep (se 3 (by rfl) ⟨303611, by rfl⟩ : syracuseStep 1619261 = 607223) B607223
theorem B963913 : Blo 503794 963913 := bstep (se 2 (by rfl) ⟨361467, by rfl⟩ : syracuseStep 963913 = 722935) B722935
theorem B505167 : Blo 503794 505167 := bstep (se 1 (by rfl) ⟨378875, by rfl⟩ : syracuseStep 505167 = 757751) B757751
theorem B505183 : Blo 503794 505183 := bstep (se 1 (by rfl) ⟨378887, by rfl⟩ : syracuseStep 505183 = 757775) B757775
theorem B505211 : Blo 503794 505211 := bstep (se 1 (by rfl) ⟨378908, by rfl⟩ : syracuseStep 505211 = 757817) B757817
theorem B505263 : Blo 503794 505263 := bstep (se 1 (by rfl) ⟨378947, by rfl⟩ : syracuseStep 505263 = 757895) B757895
theorem B505287 : Blo 503794 505287 := bstep (se 1 (by rfl) ⟨378965, by rfl⟩ : syracuseStep 505287 = 757931) B757931
theorem B505307 : Blo 503794 505307 := bstep (se 1 (by rfl) ⟨378980, by rfl⟩ : syracuseStep 505307 = 757961) B757961
theorem B505383 : Blo 503794 505383 := bstep (se 1 (by rfl) ⟨379037, by rfl⟩ : syracuseStep 505383 = 758075) B758075
theorem B570919 : Blo 503794 570919 := bstep (se 1 (by rfl) ⟨428189, by rfl⟩ : syracuseStep 570919 = 856379) B856379
theorem B505423 : Blo 503794 505423 := bstep (se 1 (by rfl) ⟨379067, by rfl⟩ : syracuseStep 505423 = 758135) B758135
theorem B505439 : Blo 503794 505439 := bstep (se 1 (by rfl) ⟨379079, by rfl⟩ : syracuseStep 505439 = 758159) B758159
theorem B6895201 : Blo 503794 6895201 := bstep (se 2 (by rfl) ⟨2585700, by rfl⟩ : syracuseStep 6895201 = 5171401) B5171401
theorem B505467 : Blo 503794 505467 := bstep (se 1 (by rfl) ⟨379100, by rfl⟩ : syracuseStep 505467 = 758201) B758201
theorem B505519 : Blo 503794 505519 := bstep (se 1 (by rfl) ⟨379139, by rfl⟩ : syracuseStep 505519 = 758279) B758279
theorem B505543 : Blo 503794 505543 := bstep (se 1 (by rfl) ⟨379157, by rfl⟩ : syracuseStep 505543 = 758315) B758315
theorem B1619671 : Blo 503794 1619671 := bstep (se 1 (by rfl) ⟨1214753, by rfl⟩ : syracuseStep 1619671 = 2429507) B2429507
theorem B2471639 : Blo 503794 2471639 := bstep (se 1 (by rfl) ⟨1853729, by rfl⟩ : syracuseStep 2471639 = 3707459) B3707459
theorem B505563 : Blo 503794 505563 := bstep (se 1 (by rfl) ⟨379172, by rfl⟩ : syracuseStep 505563 = 758345) B758345
theorem B505639 : Blo 503794 505639 := bstep (se 1 (by rfl) ⟨379229, by rfl⟩ : syracuseStep 505639 = 758459) B758459
theorem B505679 : Blo 503794 505679 := bstep (se 1 (by rfl) ⟨379259, by rfl⟩ : syracuseStep 505679 = 758519) B758519
theorem B505695 : Blo 503794 505695 := bstep (se 1 (by rfl) ⟨379271, by rfl⟩ : syracuseStep 505695 = 758543) B758543
theorem B505723 : Blo 503794 505723 := bstep (se 1 (by rfl) ⟨379292, by rfl⟩ : syracuseStep 505723 = 758585) B758585
theorem B505775 : Blo 503794 505775 := bstep (se 1 (by rfl) ⟨379331, by rfl⟩ : syracuseStep 505775 = 758663) B758663
theorem B505799 : Blo 503794 505799 := bstep (se 1 (by rfl) ⟨379349, by rfl⟩ : syracuseStep 505799 = 758699) B758699
theorem B505819 : Blo 503794 505819 := bstep (se 1 (by rfl) ⟨379364, by rfl⟩ : syracuseStep 505819 = 758729) B758729
theorem B505895 : Blo 503794 505895 := bstep (se 1 (by rfl) ⟨379421, by rfl⟩ : syracuseStep 505895 = 758843) B758843
theorem B505935 : Blo 503794 505935 := bstep (se 1 (by rfl) ⟨379451, by rfl⟩ : syracuseStep 505935 = 758903) B758903
theorem B1914961 : Blo 503794 1914961 := bstep (se 2 (by rfl) ⟨718110, by rfl⟩ : syracuseStep 1914961 = 1436221) B1436221
theorem B3127385 : Blo 503794 3127385 := bstep (se 2 (by rfl) ⟨1172769, by rfl⟩ : syracuseStep 3127385 = 2345539) B2345539
theorem B505951 : Blo 503794 505951 := bstep (se 1 (by rfl) ⟨379463, by rfl⟩ : syracuseStep 505951 = 758927) B758927
theorem B505979 : Blo 503794 505979 := bstep (se 1 (by rfl) ⟨379484, by rfl⟩ : syracuseStep 505979 = 758969) B758969
theorem B5748893 : Blo 503794 5748893 := bstep (se 3 (by rfl) ⟨1077917, by rfl⟩ : syracuseStep 5748893 = 2155835) B2155835
theorem B506031 : Blo 503794 506031 := bstep (se 1 (by rfl) ⟨379523, by rfl⟩ : syracuseStep 506031 = 759047) B759047
theorem B506055 : Blo 503794 506055 := bstep (se 1 (by rfl) ⟨379541, by rfl⟩ : syracuseStep 506055 = 759083) B759083
theorem B506075 : Blo 503794 506075 := bstep (se 1 (by rfl) ⟨379556, by rfl⟩ : syracuseStep 506075 = 759113) B759113
theorem B12925169 : Blo 503794 12925169 := bstep (se 2 (by rfl) ⟨4846938, by rfl⟩ : syracuseStep 12925169 = 9693877) B9693877
theorem B506151 : Blo 503794 506151 := bstep (se 1 (by rfl) ⟨379613, by rfl⟩ : syracuseStep 506151 = 759227) B759227
theorem B506191 : Blo 503794 506191 := bstep (se 1 (by rfl) ⟨379643, by rfl⟩ : syracuseStep 506191 = 759287) B759287
theorem B506207 : Blo 503794 506207 := bstep (se 1 (by rfl) ⟨379655, by rfl⟩ : syracuseStep 506207 = 759311) B759311
theorem B506235 : Blo 503794 506235 := bstep (se 1 (by rfl) ⟨379676, by rfl⟩ : syracuseStep 506235 = 759353) B759353
theorem B1915265 : Blo 503794 1915265 := bstep (se 2 (by rfl) ⟨718224, by rfl⟩ : syracuseStep 1915265 = 1436449) B1436449
theorem B506287 : Blo 503794 506287 := bstep (se 1 (by rfl) ⟨379715, by rfl⟩ : syracuseStep 506287 = 759431) B759431
theorem B506311 : Blo 503794 506311 := bstep (se 1 (by rfl) ⟨379733, by rfl⟩ : syracuseStep 506311 = 759467) B759467
theorem B506331 : Blo 503794 506331 := bstep (se 1 (by rfl) ⟨379748, by rfl⟩ : syracuseStep 506331 = 759497) B759497
theorem B506407 : Blo 503794 506407 := bstep (se 1 (by rfl) ⟨379805, by rfl⟩ : syracuseStep 506407 = 759611) B759611
theorem B506447 : Blo 503794 506447 := bstep (se 1 (by rfl) ⟨379835, by rfl⟩ : syracuseStep 506447 = 759671) B759671
theorem B506463 : Blo 503794 506463 := bstep (se 1 (by rfl) ⟨379847, by rfl⟩ : syracuseStep 506463 = 759695) B759695
theorem B506491 : Blo 503794 506491 := bstep (se 1 (by rfl) ⟨379868, by rfl⟩ : syracuseStep 506491 = 759737) B759737
theorem B506543 : Blo 503794 506543 := bstep (se 1 (by rfl) ⟨379907, by rfl⟩ : syracuseStep 506543 = 759815) B759815
theorem B539335 : Blo 503794 539335 := bstep (se 1 (by rfl) ⟨404501, by rfl⟩ : syracuseStep 539335 = 809003) B809003
theorem B506567 : Blo 503794 506567 := bstep (se 1 (by rfl) ⟨379925, by rfl⟩ : syracuseStep 506567 = 759851) B759851
theorem B506587 : Blo 503794 506587 := bstep (se 1 (by rfl) ⟨379940, by rfl⟩ : syracuseStep 506587 = 759881) B759881
theorem B506663 : Blo 503794 506663 := bstep (se 1 (by rfl) ⟨379997, by rfl⟩ : syracuseStep 506663 = 759995) B759995
theorem B1915721 : Blo 503794 1915721 := bstep (se 2 (by rfl) ⟨718395, by rfl⟩ : syracuseStep 1915721 = 1436791) B1436791
theorem B506703 : Blo 503794 506703 := bstep (se 1 (by rfl) ⟨380027, by rfl⟩ : syracuseStep 506703 = 760055) B760055
theorem B506719 : Blo 503794 506719 := bstep (se 1 (by rfl) ⟨380039, by rfl⟩ : syracuseStep 506719 = 760079) B760079
theorem B4111211 : Blo 503794 4111211 := bstep (se 1 (by rfl) ⟨3083408, by rfl⟩ : syracuseStep 4111211 = 6166817) B6166817
theorem B506747 : Blo 503794 506747 := bstep (se 1 (by rfl) ⟨380060, by rfl⟩ : syracuseStep 506747 = 760121) B760121
theorem B768943 : Blo 503794 768943 := bstep (se 1 (by rfl) ⟨576707, by rfl⟩ : syracuseStep 768943 = 1153415) B1153415
theorem B506799 : Blo 503794 506799 := bstep (se 1 (by rfl) ⟨380099, by rfl⟩ : syracuseStep 506799 = 760199) B760199
theorem B506823 : Blo 503794 506823 := bstep (se 1 (by rfl) ⟨380117, by rfl⟩ : syracuseStep 506823 = 760235) B760235
theorem B506843 : Blo 503794 506843 := bstep (se 1 (by rfl) ⟨380132, by rfl⟩ : syracuseStep 506843 = 760265) B760265
theorem B1915919 : Blo 503794 1915919 := bstep (se 1 (by rfl) ⟨1436939, by rfl⟩ : syracuseStep 1915919 = 2873879) B2873879
theorem B2046995 : Blo 503794 2046995 := bstep (se 1 (by rfl) ⟨1535246, by rfl⟩ : syracuseStep 2046995 = 3070493) B3070493
theorem B506919 : Blo 503794 506919 := bstep (se 1 (by rfl) ⟨380189, by rfl⟩ : syracuseStep 506919 = 760379) B760379
theorem B506959 : Blo 503794 506959 := bstep (se 1 (by rfl) ⟨380219, by rfl⟩ : syracuseStep 506959 = 760439) B760439
theorem B506975 : Blo 503794 506975 := bstep (se 1 (by rfl) ⟨380231, by rfl⟩ : syracuseStep 506975 = 760463) B760463
theorem B507003 : Blo 503794 507003 := bstep (se 1 (by rfl) ⟨380252, by rfl⟩ : syracuseStep 507003 = 760505) B760505
theorem B507055 : Blo 503794 507055 := bstep (se 1 (by rfl) ⟨380291, by rfl⟩ : syracuseStep 507055 = 760583) B760583
theorem B507079 : Blo 503794 507079 := bstep (se 1 (by rfl) ⟨380309, by rfl⟩ : syracuseStep 507079 = 760619) B760619
theorem B507099 : Blo 503794 507099 := bstep (se 1 (by rfl) ⟨380324, by rfl⟩ : syracuseStep 507099 = 760649) B760649
theorem B507175 : Blo 503794 507175 := bstep (se 1 (by rfl) ⟨380381, by rfl⟩ : syracuseStep 507175 = 760763) B760763
theorem B507215 : Blo 503794 507215 := bstep (se 1 (by rfl) ⟨380411, by rfl⟩ : syracuseStep 507215 = 760823) B760823
theorem B507231 : Blo 503794 507231 := bstep (se 1 (by rfl) ⟨380423, by rfl⟩ : syracuseStep 507231 = 760847) B760847
theorem B867689 : Blo 503794 867689 := bstep (se 2 (by rfl) ⟨325383, by rfl⟩ : syracuseStep 867689 = 650767) B650767
theorem B507259 : Blo 503794 507259 := bstep (se 1 (by rfl) ⟨380444, by rfl⟩ : syracuseStep 507259 = 760889) B760889
theorem B507311 : Blo 503794 507311 := bstep (se 1 (by rfl) ⟨380483, by rfl⟩ : syracuseStep 507311 = 760967) B760967
theorem B507335 : Blo 503794 507335 := bstep (se 1 (by rfl) ⟨380501, by rfl⟩ : syracuseStep 507335 = 761003) B761003
theorem B507355 : Blo 503794 507355 := bstep (se 1 (by rfl) ⟨380516, by rfl⟩ : syracuseStep 507355 = 761033) B761033
theorem B507431 : Blo 503794 507431 := bstep (se 1 (by rfl) ⟨380573, by rfl⟩ : syracuseStep 507431 = 761147) B761147
theorem B638543 : Blo 503794 638543 := bstep (se 1 (by rfl) ⟨478907, by rfl⟩ : syracuseStep 638543 = 957815) B957815
theorem B507471 : Blo 503794 507471 := bstep (se 1 (by rfl) ⟨380603, by rfl⟩ : syracuseStep 507471 = 761207) B761207
theorem B507487 : Blo 503794 507487 := bstep (se 1 (by rfl) ⟨380615, by rfl⟩ : syracuseStep 507487 = 761231) B761231
theorem B507515 : Blo 503794 507515 := bstep (se 1 (by rfl) ⟨380636, by rfl⟩ : syracuseStep 507515 = 761273) B761273
theorem B507567 : Blo 503794 507567 := bstep (se 1 (by rfl) ⟨380675, by rfl⟩ : syracuseStep 507567 = 761351) B761351
theorem B507591 : Blo 503794 507591 := bstep (se 1 (by rfl) ⟨380693, by rfl⟩ : syracuseStep 507591 = 761387) B761387
theorem B507611 : Blo 503794 507611 := bstep (se 1 (by rfl) ⟨380708, by rfl⟩ : syracuseStep 507611 = 761417) B761417
theorem B507687 : Blo 503794 507687 := bstep (se 1 (by rfl) ⟨380765, by rfl⟩ : syracuseStep 507687 = 761531) B761531
theorem B507727 : Blo 503794 507727 := bstep (se 1 (by rfl) ⟨380795, by rfl⟩ : syracuseStep 507727 = 761591) B761591
theorem B507743 : Blo 503794 507743 := bstep (se 1 (by rfl) ⟨380807, by rfl⟩ : syracuseStep 507743 = 761615) B761615
theorem B507771 : Blo 503794 507771 := bstep (se 1 (by rfl) ⟨380828, by rfl⟩ : syracuseStep 507771 = 761657) B761657
theorem B4112441 : Blo 503794 4112441 := bstep (se 2 (by rfl) ⟨1542165, by rfl⟩ : syracuseStep 4112441 = 3084331) B3084331
theorem B1622567 : Blo 503794 1622567 := bstep (se 1 (by rfl) ⟨1216925, by rfl⟩ : syracuseStep 1622567 = 2433851) B2433851
theorem B639839 : Blo 503794 639839 := bstep (se 1 (by rfl) ⟨479879, by rfl⟩ : syracuseStep 639839 = 959759) B959759
theorem B1295291 : Blo 503794 1295291 := bstep (se 1 (by rfl) ⟨971468, by rfl⟩ : syracuseStep 1295291 = 1942937) B1942937
theorem B5751809 : Blo 503794 5751809 := bstep (se 2 (by rfl) ⟨2156928, by rfl⟩ : syracuseStep 5751809 = 4313857) B4313857
theorem B542171 : Blo 503794 542171 := bstep (se 1 (by rfl) ⟨406628, by rfl⟩ : syracuseStep 542171 = 813257) B813257
theorem B1820141 : Blo 503794 1820141 := bstep (se 3 (by rfl) ⟨341276, by rfl⟩ : syracuseStep 1820141 = 682553) B682553
theorem B8308439 : Blo 503794 8308439 := bstep (se 1 (by rfl) ⟨6231329, by rfl⟩ : syracuseStep 8308439 = 12462659) B12462659
theorem B1624463 : Blo 503794 1624463 := bstep (se 1 (by rfl) ⟨1218347, by rfl⟩ : syracuseStep 1624463 = 2436695) B2436695
theorem B6933127 : Blo 503794 6933127 := bstep (se 1 (by rfl) ⟨5199845, by rfl⟩ : syracuseStep 6933127 = 10399691) B10399691
theorem B609131 : Blo 503794 609131 := bstep (se 1 (by rfl) ⟨456848, by rfl⟩ : syracuseStep 609131 = 913697) B913697
theorem B2968595 : Blo 503794 2968595 := bstep (se 1 (by rfl) ⟨2226446, by rfl⟩ : syracuseStep 2968595 = 4452893) B4452893
theorem B1756313 : Blo 503794 1756313 := bstep (se 2 (by rfl) ⟨658617, by rfl⟩ : syracuseStep 1756313 = 1317235) B1317235
theorem B642487 : Blo 503794 642487 := bstep (se 1 (by rfl) ⟨481865, by rfl⟩ : syracuseStep 642487 = 963731) B963731
theorem B1134089 : Blo 503794 1134089 := bstep (se 2 (by rfl) ⟨425283, by rfl⟩ : syracuseStep 1134089 = 850567) B850567
theorem B1134431 : Blo 503794 1134431 := bstep (se 1 (by rfl) ⟨850823, by rfl⟩ : syracuseStep 1134431 = 1701647) B1701647
theorem B1724267 : Blo 503794 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B3657581 : Blo 503794 3657581 := bstep (se 3 (by rfl) ⟨685796, by rfl⟩ : syracuseStep 3657581 = 1371593) B1371593
theorem B3559355 : Blo 503794 3559355 := bstep (se 1 (by rfl) ⟨2669516, by rfl⟩ : syracuseStep 3559355 = 5339033) B5339033
theorem B1134611 : Blo 503794 1134611 := bstep (se 1 (by rfl) ⟨850958, by rfl⟩ : syracuseStep 1134611 = 1701917) B1701917
theorem B577615 : Blo 503794 577615 := bstep (se 1 (by rfl) ⟨433211, by rfl⟩ : syracuseStep 577615 = 866423) B866423
theorem B1134953 : Blo 503794 1134953 := bstep (se 2 (by rfl) ⟨425607, by rfl⟩ : syracuseStep 1134953 = 851215) B851215
theorem B807311 : Blo 503794 807311 := bstep (se 1 (by rfl) ⟨605483, by rfl⟩ : syracuseStep 807311 = 1210967) B1210967
theorem B1921751 : Blo 503794 1921751 := bstep (se 1 (by rfl) ⟨1441313, by rfl⟩ : syracuseStep 1921751 = 2882627) B2882627
theorem B10343213 : Blo 503794 10343213 := bstep (se 3 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 10343213 = 3878705) B3878705
theorem B1135547 : Blo 503794 1135547 := bstep (se 1 (by rfl) ⟨851660, by rfl⟩ : syracuseStep 1135547 = 1703321) B1703321
theorem B4314131 : Blo 503794 4314131 := bstep (se 1 (by rfl) ⟨3235598, by rfl⟩ : syracuseStep 4314131 = 6471197) B6471197
theorem B1135673 : Blo 503794 1135673 := bstep (se 2 (by rfl) ⟨425877, by rfl⟩ : syracuseStep 1135673 = 851755) B851755
theorem B1824061 : Blo 503794 1824061 := bstep (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) B684023
theorem B1725839 : Blo 503794 1725839 := bstep (se 1 (by rfl) ⟨1294379, by rfl⟩ : syracuseStep 1725839 = 2588759) B2588759
theorem B1136015 : Blo 503794 1136015 := bstep (se 1 (by rfl) ⟨852011, by rfl⟩ : syracuseStep 1136015 = 1704023) B1704023
theorem B1725961 : Blo 503794 1725961 := bstep (se 2 (by rfl) ⟨647235, by rfl⟩ : syracuseStep 1725961 = 1294471) B1294471
theorem B1037881 : Blo 503794 1037881 := bstep (se 2 (by rfl) ⟨389205, by rfl⟩ : syracuseStep 1037881 = 778411) B778411
theorem B546383 : Blo 503794 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B19715735 : Blo 503794 19715735 := bstep (se 1 (by rfl) ⟨14786801, by rfl⟩ : syracuseStep 19715735 = 29573603) B29573603
theorem B1136339 : Blo 503794 1136339 := bstep (se 1 (by rfl) ⟨852254, by rfl⟩ : syracuseStep 1136339 = 1704509) B1704509
theorem B2741975 : Blo 503794 2741975 := bstep (se 1 (by rfl) ⟨2056481, by rfl⟩ : syracuseStep 2741975 = 4112963) B4112963
theorem B4315193 : Blo 503794 4315193 := bstep (se 2 (by rfl) ⟨1618197, by rfl⟩ : syracuseStep 4315193 = 3236395) B3236395
theorem B809131 : Blo 503794 809131 := bstep (se 1 (by rfl) ⟨606848, by rfl⟩ : syracuseStep 809131 = 1213697) B1213697
theorem B3889457 : Blo 503794 3889457 := bstep (se 2 (by rfl) ⟨1458546, by rfl⟩ : syracuseStep 3889457 = 2917093) B2917093
theorem B8673641 : Blo 503794 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B1137275 : Blo 503794 1137275 := bstep (se 1 (by rfl) ⟨852956, by rfl⟩ : syracuseStep 1137275 = 1705913) B1705913
theorem B1727165 : Blo 503794 1727165 := bstep (se 3 (by rfl) ⟨323843, by rfl⟩ : syracuseStep 1727165 = 647687) B647687
theorem B5757641 : Blo 503794 5757641 := bstep (se 2 (by rfl) ⟨2159115, by rfl⟩ : syracuseStep 5757641 = 4318231) B4318231
theorem B1137401 : Blo 503794 1137401 := bstep (se 2 (by rfl) ⟨426525, by rfl⟩ : syracuseStep 1137401 = 853051) B853051
theorem B1137671 : Blo 503794 1137671 := bstep (se 1 (by rfl) ⟨853253, by rfl⟩ : syracuseStep 1137671 = 1706507) B1706507
theorem B1825849 : Blo 503794 1825849 := bstep (se 2 (by rfl) ⟨684693, by rfl⟩ : syracuseStep 1825849 = 1369387) B1369387
theorem B1137743 : Blo 503794 1137743 := bstep (se 1 (by rfl) ⟨853307, by rfl⟩ : syracuseStep 1137743 = 1706615) B1706615
theorem B6151247 : Blo 503794 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B974071 : Blo 503794 974071 := bstep (se 1 (by rfl) ⟨730553, by rfl⟩ : syracuseStep 974071 = 1461107) B1461107
theorem B810233 : Blo 503794 810233 := bstep (se 2 (by rfl) ⟨303837, by rfl⟩ : syracuseStep 810233 = 607675) B607675
theorem B810335 : Blo 503794 810335 := bstep (se 1 (by rfl) ⟨607751, by rfl⟩ : syracuseStep 810335 = 1215503) B1215503
theorem B1138139 : Blo 503794 1138139 := bstep (se 1 (by rfl) ⟨853604, by rfl⟩ : syracuseStep 1138139 = 1707209) B1707209
theorem B1924667 : Blo 503794 1924667 := bstep (se 1 (by rfl) ⟨1443500, by rfl⟩ : syracuseStep 1924667 = 2887001) B2887001
theorem B2154401 : Blo 503794 2154401 := bstep (se 2 (by rfl) ⟨807900, by rfl⟩ : syracuseStep 2154401 = 1615801) B1615801
theorem B1138607 : Blo 503794 1138607 := bstep (se 1 (by rfl) ⟨853955, by rfl⟩ : syracuseStep 1138607 = 1707911) B1707911
theorem B31252493 : Blo 503794 31252493 := bstep (se 3 (by rfl) ⟨5859842, by rfl⟩ : syracuseStep 31252493 = 11719685) B11719685
theorem B15622307 : Blo 503794 15622307 := bstep (se 1 (by rfl) ⟨11716730, by rfl⟩ : syracuseStep 15622307 = 23433461) B23433461
theorem B1138859 : Blo 503794 1138859 := bstep (se 1 (by rfl) ⟨854144, by rfl⟩ : syracuseStep 1138859 = 1708289) B1708289
theorem B1139399 : Blo 503794 1139399 := bstep (se 1 (by rfl) ⟨854549, by rfl⟩ : syracuseStep 1139399 = 1709099) B1709099
theorem B811919 : Blo 503794 811919 := bstep (se 1 (by rfl) ⟨608939, by rfl⟩ : syracuseStep 811919 = 1217879) B1217879
theorem B15524783 : Blo 503794 15524783 := bstep (se 1 (by rfl) ⟨11643587, by rfl⟩ : syracuseStep 15524783 = 23287175) B23287175
theorem B3073043 : Blo 503794 3073043 := bstep (se 1 (by rfl) ⟨2304782, by rfl⟩ : syracuseStep 3073043 = 4609565) B4609565
theorem B12445093 : Blo 503794 12445093 := bstep (se 4 (by rfl) ⟨1166727, by rfl⟩ : syracuseStep 12445093 = 2333455) B2333455
theorem B648631 : Blo 503794 648631 := bstep (se 1 (by rfl) ⟨486473, by rfl⟩ : syracuseStep 648631 = 972947) B972947
theorem B648667 : Blo 503794 648667 := bstep (se 1 (by rfl) ⟨486500, by rfl⟩ : syracuseStep 648667 = 973001) B973001
theorem B1140263 : Blo 503794 1140263 := bstep (se 1 (by rfl) ⟨855197, by rfl⟩ : syracuseStep 1140263 = 1710395) B1710395
theorem B2877227 : Blo 503794 2877227 := bstep (se 1 (by rfl) ⟨2157920, by rfl⟩ : syracuseStep 2877227 = 4315841) B4315841
theorem B1140587 : Blo 503794 1140587 := bstep (se 1 (by rfl) ⟨855440, by rfl⟩ : syracuseStep 1140587 = 1710881) B1710881
theorem B1140641 : Blo 503794 1140641 := bstep (se 2 (by rfl) ⟨427740, by rfl⟩ : syracuseStep 1140641 = 855481) B855481
theorem B1140983 : Blo 503794 1140983 := bstep (se 1 (by rfl) ⟨855737, by rfl⟩ : syracuseStep 1140983 = 1711475) B1711475
theorem B1927415 : Blo 503794 1927415 := bstep (se 1 (by rfl) ⟨1445561, by rfl⟩ : syracuseStep 1927415 = 2891123) B2891123
theorem B2156861 : Blo 503794 2156861 := bstep (se 3 (by rfl) ⟨404411, by rfl⟩ : syracuseStep 2156861 = 808823) B808823
theorem B1141577 : Blo 503794 1141577 := bstep (se 2 (by rfl) ⟨428091, by rfl⟩ : syracuseStep 1141577 = 856183) B856183
theorem B2780087 : Blo 503794 2780087 := bstep (se 1 (by rfl) ⟨2085065, by rfl⟩ : syracuseStep 2780087 = 4170131) B4170131
theorem B1830059 : Blo 503794 1830059 := bstep (se 1 (by rfl) ⟨1372544, by rfl⟩ : syracuseStep 1830059 = 2745089) B2745089
theorem B3632323 : Blo 503794 3632323 := bstep (se 1 (by rfl) ⟨2724242, by rfl⟩ : syracuseStep 3632323 = 5448485) B5448485
theorem B3829193 : Blo 503794 3829193 := bstep (se 2 (by rfl) ⟨1435947, by rfl⟩ : syracuseStep 3829193 = 2871895) B2871895
theorem B683483 : Blo 503794 683483 := bstep (se 1 (by rfl) ⟨512612, by rfl⟩ : syracuseStep 683483 = 1025225) B1025225
theorem B4845095 : Blo 503794 4845095 := bstep (se 1 (by rfl) ⟨3633821, by rfl⟩ : syracuseStep 4845095 = 7267643) B7267643
theorem B912953 : Blo 503794 912953 := bstep (se 2 (by rfl) ⟨342357, by rfl⟩ : syracuseStep 912953 = 684715) B684715
theorem B1142369 : Blo 503794 1142369 := bstep (se 2 (by rfl) ⟨428388, by rfl⟩ : syracuseStep 1142369 = 856777) B856777
theorem B14839517 : Blo 503794 14839517 := bstep (se 3 (by rfl) ⟨2782409, by rfl⟩ : syracuseStep 14839517 = 5564819) B5564819
theorem B6156013 : Blo 503794 6156013 := bstep (se 3 (by rfl) ⟨1154252, by rfl⟩ : syracuseStep 6156013 = 2308505) B2308505
theorem B4091681 : Blo 503794 4091681 := bstep (se 2 (by rfl) ⟨1534380, by rfl⟩ : syracuseStep 4091681 = 3068761) B3068761
theorem B2551661 : Blo 503794 2551661 := bstep (se 3 (by rfl) ⟨478436, by rfl⟩ : syracuseStep 2551661 = 956873) B956873
theorem B12283811 : Blo 503794 12283811 := bstep (se 1 (by rfl) ⟨9212858, by rfl⟩ : syracuseStep 12283811 = 18425717) B18425717
theorem B683959 : Blo 503794 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B2551823 : Blo 503794 2551823 := bstep (se 1 (by rfl) ⟨1913867, by rfl⟩ : syracuseStep 2551823 = 3827735) B3827735
theorem B6582349 : Blo 503794 6582349 := bstep (se 3 (by rfl) ⟨1234190, by rfl⟩ : syracuseStep 6582349 = 2468381) B2468381
theorem B7303283 : Blo 503794 7303283 := bstep (se 1 (by rfl) ⟨5477462, by rfl⟩ : syracuseStep 7303283 = 10954925) B10954925
theorem B913531 : Blo 503794 913531 := bstep (se 1 (by rfl) ⟨685148, by rfl⟩ : syracuseStep 913531 = 1370297) B1370297
theorem B913847 : Blo 503794 913847 := bstep (se 1 (by rfl) ⟨685385, by rfl⟩ : syracuseStep 913847 = 1370771) B1370771
theorem B913927 : Blo 503794 913927 := bstep (se 1 (by rfl) ⟨685445, by rfl⟩ : syracuseStep 913927 = 1370891) B1370891
theorem B1667609 : Blo 503794 1667609 := bstep (se 2 (by rfl) ⟨625353, by rfl⟩ : syracuseStep 1667609 = 1250707) B1250707
theorem B1077799 : Blo 503794 1077799 := bstep (se 1 (by rfl) ⟨808349, by rfl⟩ : syracuseStep 1077799 = 1616699) B1616699
theorem B1700567 : Blo 503794 1700567 := bstep (se 1 (by rfl) ⟨1275425, by rfl⟩ : syracuseStep 1700567 = 2550851) B2550851
theorem B2159389 : Blo 503794 2159389 := bstep (se 3 (by rfl) ⟨404885, by rfl⟩ : syracuseStep 2159389 = 809771) B809771
theorem B1078123 : Blo 503794 1078123 := bstep (se 1 (by rfl) ⟨808592, by rfl⟩ : syracuseStep 1078123 = 1617185) B1617185
theorem B1700783 : Blo 503794 1700783 := bstep (se 1 (by rfl) ⟨1275587, by rfl⟩ : syracuseStep 1700783 = 2551175) B2551175
theorem B3077519 : Blo 503794 3077519 := bstep (se 1 (by rfl) ⟨2308139, by rfl⟩ : syracuseStep 3077519 = 4616279) B4616279
theorem B2881169 : Blo 503794 2881169 := bstep (se 2 (by rfl) ⟨1080438, by rfl⟩ : syracuseStep 2881169 = 2160877) B2160877
theorem B32765633 : Blo 503794 32765633 := bstep (se 2 (by rfl) ⟨12287112, by rfl⟩ : syracuseStep 32765633 = 24574225) B24574225
theorem B1636139 : Blo 503794 1636139 := bstep (se 1 (by rfl) ⟨1227104, by rfl⟩ : syracuseStep 1636139 = 2454209) B2454209
theorem B1079353 : Blo 503794 1079353 := bstep (se 2 (by rfl) ⟨404757, by rfl⟩ : syracuseStep 1079353 = 809515) B809515
theorem B1275983 : Blo 503794 1275983 := bstep (se 1 (by rfl) ⟨956987, by rfl⟩ : syracuseStep 1275983 = 1913975) B1913975
theorem B3242213 : Blo 503794 3242213 := bstep (se 4 (by rfl) ⟨303957, by rfl⟩ : syracuseStep 3242213 = 607915) B607915
theorem B850169 : Blo 503794 850169 := bstep (se 2 (by rfl) ⟨318813, by rfl⟩ : syracuseStep 850169 = 637627) B637627
theorem B850351 : Blo 503794 850351 := bstep (se 1 (by rfl) ⟨637763, by rfl⟩ : syracuseStep 850351 = 1275527) B1275527
theorem B850439 : Blo 503794 850439 := bstep (se 1 (by rfl) ⟨637829, by rfl⟩ : syracuseStep 850439 = 1275659) B1275659
theorem B2554577 : Blo 503794 2554577 := bstep (se 2 (by rfl) ⟨957966, by rfl⟩ : syracuseStep 2554577 = 1915933) B1915933
theorem B1276631 : Blo 503794 1276631 := bstep (se 1 (by rfl) ⟨957473, by rfl⟩ : syracuseStep 1276631 = 1914947) B1914947
theorem B850783 : Blo 503794 850783 := bstep (se 1 (by rfl) ⟨638087, by rfl⟩ : syracuseStep 850783 = 1276175) B1276175
theorem B850871 : Blo 503794 850871 := bstep (se 1 (by rfl) ⟨638153, by rfl⟩ : syracuseStep 850871 = 1276307) B1276307
theorem B1276985 : Blo 503794 1276985 := bstep (se 2 (by rfl) ⟨478869, by rfl⟩ : syracuseStep 1276985 = 957739) B957739
theorem B2161835 : Blo 503794 2161835 := bstep (se 1 (by rfl) ⟨1621376, by rfl⟩ : syracuseStep 2161835 = 3242753) B3242753
theorem B1703159 : Blo 503794 1703159 := bstep (se 1 (by rfl) ⟨1277369, by rfl⟩ : syracuseStep 1703159 = 2554739) B2554739
theorem B7273871 : Blo 503794 7273871 := bstep (se 1 (by rfl) ⟨5455403, by rfl⟩ : syracuseStep 7273871 = 10910807) B10910807
theorem B2883059 : Blo 503794 2883059 := bstep (se 1 (by rfl) ⟨2162294, by rfl⟩ : syracuseStep 2883059 = 4324589) B4324589
theorem B851465 : Blo 503794 851465 := bstep (se 2 (by rfl) ⟨319299, by rfl⟩ : syracuseStep 851465 = 638599) B638599
theorem B1703483 : Blo 503794 1703483 := bstep (se 1 (by rfl) ⟨1277612, by rfl⟩ : syracuseStep 1703483 = 2555225) B2555225
theorem B851627 : Blo 503794 851627 := bstep (se 1 (by rfl) ⟨638720, by rfl⟩ : syracuseStep 851627 = 1277441) B1277441
theorem B1703753 : Blo 503794 1703753 := bstep (se 2 (by rfl) ⟨638907, by rfl⟩ : syracuseStep 1703753 = 1277815) B1277815
theorem B1277977 : Blo 503794 1277977 := bstep (se 2 (by rfl) ⟨479241, by rfl⟩ : syracuseStep 1277977 = 958483) B958483
theorem B2588777 : Blo 503794 2588777 := bstep (se 2 (by rfl) ⟨970791, by rfl⟩ : syracuseStep 2588777 = 1941583) B1941583
theorem B21921941 : Blo 503794 21921941 := bstep (se 6 (by rfl) ⟨513795, by rfl⟩ : syracuseStep 21921941 = 1027591) B1027591
theorem B1278281 : Blo 503794 1278281 := bstep (se 2 (by rfl) ⟨479355, by rfl⟩ : syracuseStep 1278281 = 958711) B958711
theorem B1081711 : Blo 503794 1081711 := bstep (se 1 (by rfl) ⟨811283, by rfl⟩ : syracuseStep 1081711 = 1622567) B1622567
theorem B3834539 : Blo 503794 3834539 := bstep (se 1 (by rfl) ⟨2875904, by rfl⟩ : syracuseStep 3834539 = 5751809) B5751809
theorem B1704671 : Blo 503794 1704671 := bstep (se 1 (by rfl) ⟨1278503, by rfl⟩ : syracuseStep 1704671 = 2557007) B2557007
theorem B852815 : Blo 503794 852815 := bstep (se 1 (by rfl) ⟨639611, by rfl⟩ : syracuseStep 852815 = 1279223) B1279223
theorem B10978193 : Blo 503794 10978193 := bstep (se 2 (by rfl) ⟨4116822, by rfl⟩ : syracuseStep 10978193 = 8233645) B8233645
theorem B5833619 : Blo 503794 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B1213427 : Blo 503794 1213427 := bstep (se 1 (by rfl) ⟨910070, by rfl⟩ : syracuseStep 1213427 = 1820141) B1820141
theorem B1705103 : Blo 503794 1705103 := bstep (se 1 (by rfl) ⟨1278827, by rfl⟩ : syracuseStep 1705103 = 2557655) B2557655
theorem B5538959 : Blo 503794 5538959 := bstep (se 1 (by rfl) ⟨4154219, by rfl⟩ : syracuseStep 5538959 = 8308439) B8308439
theorem B3081415 : Blo 503794 3081415 := bstep (se 1 (by rfl) ⟨2311061, by rfl⟩ : syracuseStep 3081415 = 4622123) B4622123
theorem B2426375 : Blo 503794 2426375 := bstep (se 1 (by rfl) ⟨1819781, by rfl⟩ : syracuseStep 2426375 = 3639563) B3639563
theorem B1082975 : Blo 503794 1082975 := bstep (se 1 (by rfl) ⟨812231, by rfl⟩ : syracuseStep 1082975 = 1624463) B1624463
theorem B853807 : Blo 503794 853807 := bstep (se 1 (by rfl) ⟨640355, by rfl⟩ : syracuseStep 853807 = 1280711) B1280711
theorem B1706237 : Blo 503794 1706237 := bstep (se 3 (by rfl) ⟨319919, by rfl⟩ : syracuseStep 1706237 = 639839) B639839
theorem B756059 : Blo 503794 756059 := bstep (se 1 (by rfl) ⟨567044, by rfl⟩ : syracuseStep 756059 = 1134089) B1134089
theorem B756287 : Blo 503794 756287 := bstep (se 1 (by rfl) ⟨567215, by rfl⟩ : syracuseStep 756287 = 1134431) B1134431
theorem B756407 : Blo 503794 756407 := bstep (se 1 (by rfl) ⟨567305, by rfl⟩ : syracuseStep 756407 = 1134611) B1134611
theorem B2951927 : Blo 503794 2951927 := bstep (se 1 (by rfl) ⟨2213945, by rfl⟩ : syracuseStep 2951927 = 4427891) B4427891
theorem B756635 : Blo 503794 756635 := bstep (se 1 (by rfl) ⟨567476, by rfl⟩ : syracuseStep 756635 = 1134953) B1134953
theorem B1707047 : Blo 503794 1707047 := bstep (se 1 (by rfl) ⟨1280285, by rfl⟩ : syracuseStep 1707047 = 2560571) B2560571
theorem B1281167 : Blo 503794 1281167 := bstep (se 1 (by rfl) ⟨960875, by rfl⟩ : syracuseStep 1281167 = 1921751) B1921751
theorem B757031 : Blo 503794 757031 := bstep (se 1 (by rfl) ⟨567773, by rfl⟩ : syracuseStep 757031 = 1135547) B1135547
theorem B757115 : Blo 503794 757115 := bstep (se 1 (by rfl) ⟨567836, by rfl⟩ : syracuseStep 757115 = 1135673) B1135673
theorem B1707479 : Blo 503794 1707479 := bstep (se 1 (by rfl) ⟨1280609, by rfl⟩ : syracuseStep 1707479 = 2561219) B2561219
theorem B757241 : Blo 503794 757241 := bstep (se 2 (by rfl) ⟨283965, by rfl⟩ : syracuseStep 757241 = 567931) B567931
theorem B9244169 : Blo 503794 9244169 := bstep (se 2 (by rfl) ⟨3466563, by rfl⟩ : syracuseStep 9244169 = 6933127) B6933127
theorem B1150559 : Blo 503794 1150559 := bstep (se 1 (by rfl) ⟨862919, by rfl⟩ : syracuseStep 1150559 = 1725839) B1725839
theorem B757343 : Blo 503794 757343 := bstep (se 1 (by rfl) ⟨568007, by rfl⟩ : syracuseStep 757343 = 1136015) B1136015
theorem B1445471 : Blo 503794 1445471 := bstep (se 1 (by rfl) ⟨1084103, by rfl⟩ : syracuseStep 1445471 = 2168207) B2168207
theorem B757559 : Blo 503794 757559 := bstep (se 1 (by rfl) ⟨568169, by rfl⟩ : syracuseStep 757559 = 1136339) B1136339
theorem B1445789 : Blo 503794 1445789 := bstep (se 3 (by rfl) ⟨271085, by rfl⟩ : syracuseStep 1445789 = 542171) B542171
theorem B757865 : Blo 503794 757865 := bstep (se 2 (by rfl) ⟨284199, by rfl⟩ : syracuseStep 757865 = 568399) B568399
theorem B2592971 : Blo 503794 2592971 := bstep (se 1 (by rfl) ⟨1944728, by rfl⟩ : syracuseStep 2592971 = 3889457) B3889457
theorem B758183 : Blo 503794 758183 := bstep (se 1 (by rfl) ⟨568637, by rfl⟩ : syracuseStep 758183 = 1137275) B1137275
theorem B856487 : Blo 503794 856487 := bstep (se 1 (by rfl) ⟨642365, by rfl⟩ : syracuseStep 856487 = 1284731) B1284731
theorem B1151443 : Blo 503794 1151443 := bstep (se 1 (by rfl) ⟨863582, by rfl⟩ : syracuseStep 1151443 = 1727165) B1727165
theorem B3838427 : Blo 503794 3838427 := bstep (se 1 (by rfl) ⟨2878820, by rfl⟩ : syracuseStep 3838427 = 5757641) B5757641
theorem B758267 : Blo 503794 758267 := bstep (se 1 (by rfl) ⟨568700, by rfl⟩ : syracuseStep 758267 = 1137401) B1137401
theorem B987719 : Blo 503794 987719 := bstep (se 1 (by rfl) ⟨740789, by rfl⟩ : syracuseStep 987719 = 1481579) B1481579
theorem B856649 : Blo 503794 856649 := bstep (se 2 (by rfl) ⟨321243, by rfl⟩ : syracuseStep 856649 = 642487) B642487
theorem B758393 : Blo 503794 758393 := bstep (se 2 (by rfl) ⟨284397, by rfl⟩ : syracuseStep 758393 = 568795) B568795
theorem B758447 : Blo 503794 758447 := bstep (se 1 (by rfl) ⟨568835, by rfl⟩ : syracuseStep 758447 = 1137671) B1137671
theorem B758495 : Blo 503794 758495 := bstep (se 1 (by rfl) ⟨568871, by rfl⟩ : syracuseStep 758495 = 1137743) B1137743
theorem B4100831 : Blo 503794 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B758759 : Blo 503794 758759 := bstep (se 1 (by rfl) ⟨569069, by rfl⟩ : syracuseStep 758759 = 1138139) B1138139
theorem B1283111 : Blo 503794 1283111 := bstep (se 1 (by rfl) ⟨962333, by rfl⟩ : syracuseStep 1283111 = 1924667) B1924667
theorem B1709153 : Blo 503794 1709153 := bstep (se 2 (by rfl) ⟨640932, by rfl⟩ : syracuseStep 1709153 = 1281865) B1281865
theorem B759017 : Blo 503794 759017 := bstep (se 2 (by rfl) ⟨284631, by rfl⟩ : syracuseStep 759017 = 569263) B569263
theorem B759071 : Blo 503794 759071 := bstep (se 1 (by rfl) ⟨569303, by rfl⟩ : syracuseStep 759071 = 1138607) B1138607
theorem B1283465 : Blo 503794 1283465 := bstep (se 2 (by rfl) ⟨481299, by rfl⟩ : syracuseStep 1283465 = 962599) B962599
theorem B759239 : Blo 503794 759239 := bstep (se 1 (by rfl) ⟨569429, by rfl⟩ : syracuseStep 759239 = 1138859) B1138859
theorem B1218041 : Blo 503794 1218041 := bstep (se 2 (by rfl) ⟨456765, by rfl⟩ : syracuseStep 1218041 = 913531) B913531
theorem B2561543 : Blo 503794 2561543 := bstep (se 1 (by rfl) ⟨1921157, by rfl⟩ : syracuseStep 2561543 = 3842315) B3842315
theorem B759593 : Blo 503794 759593 := bstep (se 2 (by rfl) ⟨284847, by rfl⟩ : syracuseStep 759593 = 569695) B569695
theorem B759599 : Blo 503794 759599 := bstep (se 1 (by rfl) ⟨569699, by rfl⟩ : syracuseStep 759599 = 1139399) B1139399
theorem B2562029 : Blo 503794 2562029 := bstep (se 3 (by rfl) ⟨480380, by rfl⟩ : syracuseStep 2562029 = 960761) B960761
theorem B1218569 : Blo 503794 1218569 := bstep (se 2 (by rfl) ⟨456963, by rfl⟩ : syracuseStep 1218569 = 913927) B913927
theorem B760073 : Blo 503794 760073 := bstep (se 2 (by rfl) ⟨285027, by rfl⟩ : syracuseStep 760073 = 570055) B570055
theorem B760175 : Blo 503794 760175 := bstep (se 1 (by rfl) ⟨570131, by rfl⟩ : syracuseStep 760175 = 1140263) B1140263
theorem B1710503 : Blo 503794 1710503 := bstep (se 1 (by rfl) ⟨1282877, by rfl⟩ : syracuseStep 1710503 = 2565755) B2565755
theorem B2562515 : Blo 503794 2562515 := bstep (se 1 (by rfl) ⟨1921886, by rfl⟩ : syracuseStep 2562515 = 3843773) B3843773
theorem B760391 : Blo 503794 760391 := bstep (se 1 (by rfl) ⟨570293, by rfl⟩ : syracuseStep 760391 = 1140587) B1140587
theorem B1710665 : Blo 503794 1710665 := bstep (se 2 (by rfl) ⟨641499, by rfl⟩ : syracuseStep 1710665 = 1282999) B1282999
theorem B760427 : Blo 503794 760427 := bstep (se 1 (by rfl) ⟨570320, by rfl⟩ : syracuseStep 760427 = 1140641) B1140641
theorem B2562839 : Blo 503794 2562839 := bstep (se 1 (by rfl) ⟨1922129, by rfl⟩ : syracuseStep 2562839 = 3844259) B3844259
theorem B760655 : Blo 503794 760655 := bstep (se 1 (by rfl) ⟨570491, by rfl⟩ : syracuseStep 760655 = 1140983) B1140983
theorem B1284943 : Blo 503794 1284943 := bstep (se 1 (by rfl) ⟨963707, by rfl⟩ : syracuseStep 1284943 = 1927415) B1927415
theorem B2300827 : Blo 503794 2300827 := bstep (se 1 (by rfl) ⟨1725620, by rfl⟩ : syracuseStep 2300827 = 3451241) B3451241
theorem B2432081 : Blo 503794 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B1285217 : Blo 503794 1285217 := bstep (se 2 (by rfl) ⟨481956, by rfl⟩ : syracuseStep 1285217 = 963913) B963913
theorem B761051 : Blo 503794 761051 := bstep (se 1 (by rfl) ⟨570788, by rfl⟩ : syracuseStep 761051 = 1141577) B1141577
theorem B2301281 : Blo 503794 2301281 := bstep (se 2 (by rfl) ⟨862980, by rfl⟩ : syracuseStep 2301281 = 1725961) B1725961
theorem B761225 : Blo 503794 761225 := bstep (se 2 (by rfl) ⟨285459, by rfl⟩ : syracuseStep 761225 = 570919) B570919
theorem B1383841 : Blo 503794 1383841 := bstep (se 2 (by rfl) ⟨518940, by rfl⟩ : syracuseStep 1383841 = 1037881) B1037881
theorem B1220039 : Blo 503794 1220039 := bstep (se 1 (by rfl) ⟨915029, by rfl⟩ : syracuseStep 1220039 = 1830059) B1830059
theorem B761579 : Blo 503794 761579 := bstep (se 1 (by rfl) ⟨571184, by rfl⟩ : syracuseStep 761579 = 1142369) B1142369
theorem B7413565 : Blo 503794 7413565 := bstep (se 3 (by rfl) ⟨1390043, by rfl⟩ : syracuseStep 7413565 = 2780087) B2780087
theorem B2433235 : Blo 503794 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B1712339 : Blo 503794 1712339 := bstep (se 1 (by rfl) ⟨1284254, by rfl⟩ : syracuseStep 1712339 = 2568509) B2568509
theorem B2564459 : Blo 503794 2564459 := bstep (se 1 (by rfl) ⟨1923344, by rfl⟩ : syracuseStep 2564459 = 3846689) B3846689
theorem B1712609 : Blo 503794 1712609 := bstep (se 2 (by rfl) ⟨642228, by rfl⟩ : syracuseStep 1712609 = 1284457) B1284457
theorem B1647175 : Blo 503794 1647175 := bstep (se 1 (by rfl) ⟨1235381, by rfl⟩ : syracuseStep 1647175 = 2470763) B2470763
theorem B2761673 : Blo 503794 2761673 := bstep (se 2 (by rfl) ⟨1035627, by rfl⟩ : syracuseStep 2761673 = 2071255) B2071255
theorem B1090759 : Blo 503794 1090759 := bstep (se 1 (by rfl) ⟨818069, by rfl⟩ : syracuseStep 1090759 = 1636139) B1636139
theorem B1025257 : Blo 503794 1025257 := bstep (se 2 (by rfl) ⟨384471, by rfl⟩ : syracuseStep 1025257 = 768943) B768943
theorem B2434465 : Blo 503794 2434465 := bstep (se 2 (by rfl) ⟨912924, by rfl⟩ : syracuseStep 2434465 = 1825849) B1825849
theorem B2434541 : Blo 503794 2434541 := bstep (se 3 (by rfl) ⟨456476, by rfl⟩ : syracuseStep 2434541 = 912953) B912953
theorem B566779 : Blo 503794 566779 := bstep (se 1 (by rfl) ⟨425084, by rfl⟩ : syracuseStep 566779 = 850169) B850169
theorem B2631257 : Blo 503794 2631257 := bstep (se 2 (by rfl) ⟨986721, by rfl⟩ : syracuseStep 2631257 = 1973443) B1973443
theorem B566959 : Blo 503794 566959 := bstep (se 1 (by rfl) ⟨425219, by rfl⟩ : syracuseStep 566959 = 850439) B850439
theorem B2565917 : Blo 503794 2565917 := bstep (se 3 (by rfl) ⟨481109, by rfl⟩ : syracuseStep 2565917 = 962219) B962219
theorem B567247 : Blo 503794 567247 := bstep (se 1 (by rfl) ⟨425435, by rfl⟩ : syracuseStep 567247 = 850871) B850871
theorem B4598045 : Blo 503794 4598045 := bstep (se 3 (by rfl) ⟨862133, by rfl⟩ : syracuseStep 4598045 = 1724267) B1724267
theorem B567643 : Blo 503794 567643 := bstep (se 1 (by rfl) ⟨425732, by rfl⟩ : syracuseStep 567643 = 851465) B851465
theorem B4336001 : Blo 503794 4336001 := bstep (se 2 (by rfl) ⟨1626000, by rfl⟩ : syracuseStep 4336001 = 3252001) B3252001
theorem B567751 : Blo 503794 567751 := bstep (se 1 (by rfl) ⟨425813, by rfl⟩ : syracuseStep 567751 = 851627) B851627
theorem B961247 : Blo 503794 961247 := bstep (se 1 (by rfl) ⟨720935, by rfl⟩ : syracuseStep 961247 = 1441871) B1441871
theorem B568111 : Blo 503794 568111 := bstep (se 1 (by rfl) ⟨426083, by rfl⟩ : syracuseStep 568111 = 852167) B852167
theorem B568219 : Blo 503794 568219 := bstep (se 1 (by rfl) ⟨426164, by rfl⟩ : syracuseStep 568219 = 852329) B852329
theorem B35105861 : Blo 503794 35105861 := bstep (se 4 (by rfl) ⟨3291174, by rfl⟩ : syracuseStep 35105861 = 6582349) B6582349
theorem B568615 : Blo 503794 568615 := bstep (se 1 (by rfl) ⟨426461, by rfl⟩ : syracuseStep 568615 = 852923) B852923
theorem B4107581 : Blo 503794 4107581 := bstep (se 3 (by rfl) ⟨770171, by rfl⟩ : syracuseStep 4107581 = 1540343) B1540343
theorem B568687 : Blo 503794 568687 := bstep (se 1 (by rfl) ⟨426515, by rfl⟩ : syracuseStep 568687 = 853031) B853031
theorem B568903 : Blo 503794 568903 := bstep (se 1 (by rfl) ⟨426677, by rfl⟩ : syracuseStep 568903 = 853355) B853355
theorem B1027819 : Blo 503794 1027819 := bstep (se 1 (by rfl) ⟨770864, by rfl⟩ : syracuseStep 1027819 = 1541729) B1541729
theorem B3846203 : Blo 503794 3846203 := bstep (se 1 (by rfl) ⟨2884652, by rfl⟩ : syracuseStep 3846203 = 5769305) B5769305
theorem B504095 : Blo 503794 504095 := bstep (se 1 (by rfl) ⟨378071, by rfl⟩ : syracuseStep 504095 = 756143) B756143
theorem B504155 : Blo 503794 504155 := bstep (se 1 (by rfl) ⟨378116, by rfl⟩ : syracuseStep 504155 = 756233) B756233
theorem B504175 : Blo 503794 504175 := bstep (se 1 (by rfl) ⟨378131, by rfl⟩ : syracuseStep 504175 = 756263) B756263
theorem B504231 : Blo 503794 504231 := bstep (se 1 (by rfl) ⟨378173, by rfl⟩ : syracuseStep 504231 = 756347) B756347
theorem B569767 : Blo 503794 569767 := bstep (se 1 (by rfl) ⟨427325, by rfl⟩ : syracuseStep 569767 = 854651) B854651
theorem B504315 : Blo 503794 504315 := bstep (se 1 (by rfl) ⟨378236, by rfl⟩ : syracuseStep 504315 = 756473) B756473
theorem B16593457 : Blo 503794 16593457 := bstep (se 2 (by rfl) ⟨6222546, by rfl⟩ : syracuseStep 16593457 = 12445093) B12445093
theorem B504383 : Blo 503794 504383 := bstep (se 1 (by rfl) ⟨378287, by rfl⟩ : syracuseStep 504383 = 756575) B756575
theorem B504391 : Blo 503794 504391 := bstep (se 1 (by rfl) ⟨378293, by rfl⟩ : syracuseStep 504391 = 756587) B756587
theorem B864841 : Blo 503794 864841 := bstep (se 2 (by rfl) ⟨324315, by rfl⟩ : syracuseStep 864841 = 648631) B648631
theorem B1979063 : Blo 503794 1979063 := bstep (se 1 (by rfl) ⟨1484297, by rfl⟩ : syracuseStep 1979063 = 2968595) B2968595
theorem B504543 : Blo 503794 504543 := bstep (se 1 (by rfl) ⟨378407, by rfl⟩ : syracuseStep 504543 = 756815) B756815
theorem B504623 : Blo 503794 504623 := bstep (se 1 (by rfl) ⟨378467, by rfl⟩ : syracuseStep 504623 = 756935) B756935
theorem B504731 : Blo 503794 504731 := bstep (se 1 (by rfl) ⟨378548, by rfl⟩ : syracuseStep 504731 = 757097) B757097
theorem B1029019 : Blo 503794 1029019 := bstep (se 1 (by rfl) ⟨771764, by rfl⟩ : syracuseStep 1029019 = 1543529) B1543529
theorem B504783 : Blo 503794 504783 := bstep (se 1 (by rfl) ⟨378587, by rfl⟩ : syracuseStep 504783 = 757175) B757175
theorem B504807 : Blo 503794 504807 := bstep (se 1 (by rfl) ⟨378605, by rfl⟩ : syracuseStep 504807 = 757211) B757211
theorem B570343 : Blo 503794 570343 := bstep (se 1 (by rfl) ⟨427757, by rfl⟩ : syracuseStep 570343 = 855515) B855515
theorem B4306067 : Blo 503794 4306067 := bstep (se 1 (by rfl) ⟨3229550, by rfl⟩ : syracuseStep 4306067 = 6459101) B6459101
theorem B3454109 : Blo 503794 3454109 := bstep (se 3 (by rfl) ⟨647645, by rfl⟩ : syracuseStep 3454109 = 1295291) B1295291
theorem B2438387 : Blo 503794 2438387 := bstep (se 1 (by rfl) ⟨1828790, by rfl⟩ : syracuseStep 2438387 = 3657581) B3657581
theorem B505119 : Blo 503794 505119 := bstep (se 1 (by rfl) ⟨378839, by rfl⟩ : syracuseStep 505119 = 757679) B757679
theorem B2372903 : Blo 503794 2372903 := bstep (se 1 (by rfl) ⟨1779677, by rfl⟩ : syracuseStep 2372903 = 3559355) B3559355
theorem B505179 : Blo 503794 505179 := bstep (se 1 (by rfl) ⟨378884, by rfl⟩ : syracuseStep 505179 = 757769) B757769
theorem B505199 : Blo 503794 505199 := bstep (se 1 (by rfl) ⟨378899, by rfl⟩ : syracuseStep 505199 = 757799) B757799
theorem B505255 : Blo 503794 505255 := bstep (se 1 (by rfl) ⟨378941, by rfl⟩ : syracuseStep 505255 = 757883) B757883
theorem B3847661 : Blo 503794 3847661 := bstep (se 3 (by rfl) ⟨721436, by rfl⟩ : syracuseStep 3847661 = 1442873) B1442873
theorem B505339 : Blo 503794 505339 := bstep (se 1 (by rfl) ⟨379004, by rfl⟩ : syracuseStep 505339 = 758009) B758009
theorem B505407 : Blo 503794 505407 := bstep (se 1 (by rfl) ⟨379055, by rfl⟩ : syracuseStep 505407 = 758111) B758111
theorem B505415 : Blo 503794 505415 := bstep (se 1 (by rfl) ⟨379061, by rfl⟩ : syracuseStep 505415 = 758123) B758123
theorem B538207 : Blo 503794 538207 := bstep (se 1 (by rfl) ⟨403655, by rfl⟩ : syracuseStep 538207 = 807311) B807311
theorem B505567 : Blo 503794 505567 := bstep (se 1 (by rfl) ⟨379175, by rfl⟩ : syracuseStep 505567 = 758351) B758351
theorem B505647 : Blo 503794 505647 := bstep (se 1 (by rfl) ⟨379235, by rfl⟩ : syracuseStep 505647 = 758471) B758471
theorem B6895475 : Blo 503794 6895475 := bstep (se 1 (by rfl) ⟨5171606, by rfl⟩ : syracuseStep 6895475 = 10343213) B10343213
theorem B505755 : Blo 503794 505755 := bstep (se 1 (by rfl) ⟨379316, by rfl⟩ : syracuseStep 505755 = 758633) B758633
theorem B505807 : Blo 503794 505807 := bstep (se 1 (by rfl) ⟨379355, by rfl⟩ : syracuseStep 505807 = 758711) B758711
theorem B505831 : Blo 503794 505831 := bstep (se 1 (by rfl) ⟨379373, by rfl⟩ : syracuseStep 505831 = 758747) B758747
theorem B506143 : Blo 503794 506143 := bstep (se 1 (by rfl) ⟨379607, by rfl⟩ : syracuseStep 506143 = 759215) B759215
theorem B506203 : Blo 503794 506203 := bstep (se 1 (by rfl) ⟨379652, by rfl⟩ : syracuseStep 506203 = 759305) B759305
theorem B506223 : Blo 503794 506223 := bstep (se 1 (by rfl) ⟨379667, by rfl⟩ : syracuseStep 506223 = 759335) B759335
theorem B506279 : Blo 503794 506279 := bstep (se 1 (by rfl) ⟨379709, by rfl⟩ : syracuseStep 506279 = 759419) B759419
theorem B506363 : Blo 503794 506363 := bstep (se 1 (by rfl) ⟨379772, by rfl⟩ : syracuseStep 506363 = 759545) B759545
theorem B506431 : Blo 503794 506431 := bstep (se 1 (by rfl) ⟨379823, by rfl⟩ : syracuseStep 506431 = 759647) B759647
theorem B506439 : Blo 503794 506439 := bstep (se 1 (by rfl) ⟨379829, by rfl⟩ : syracuseStep 506439 = 759659) B759659
theorem B506591 : Blo 503794 506591 := bstep (se 1 (by rfl) ⟨379943, by rfl⟩ : syracuseStep 506591 = 759887) B759887
theorem B2079479 : Blo 503794 2079479 := bstep (se 1 (by rfl) ⟨1559609, by rfl⟩ : syracuseStep 2079479 = 3119219) B3119219
theorem B506671 : Blo 503794 506671 := bstep (se 1 (by rfl) ⟨380003, by rfl⟩ : syracuseStep 506671 = 760007) B760007
theorem B1457021 : Blo 503794 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B506779 : Blo 503794 506779 := bstep (se 1 (by rfl) ⟨380084, by rfl⟩ : syracuseStep 506779 = 760169) B760169
theorem B5782427 : Blo 503794 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B506831 : Blo 503794 506831 := bstep (se 1 (by rfl) ⟨380123, by rfl⟩ : syracuseStep 506831 = 760247) B760247
theorem B506855 : Blo 503794 506855 := bstep (se 1 (by rfl) ⟨380141, by rfl⟩ : syracuseStep 506855 = 760283) B760283
theorem B9223217 : Blo 503794 9223217 := bstep (se 2 (by rfl) ⟨3458706, by rfl⟩ : syracuseStep 9223217 = 6917413) B6917413
theorem B52575293 : Blo 503794 52575293 := bstep (se 3 (by rfl) ⟨9857867, by rfl⟩ : syracuseStep 52575293 = 19715735) B19715735
theorem B9747701 : Blo 503794 9747701 := bstep (se 5 (by rfl) ⟨456923, by rfl⟩ : syracuseStep 9747701 = 913847) B913847
theorem B507167 : Blo 503794 507167 := bstep (se 1 (by rfl) ⟨380375, by rfl⟩ : syracuseStep 507167 = 760751) B760751
theorem B507227 : Blo 503794 507227 := bstep (se 1 (by rfl) ⟨380420, by rfl⟩ : syracuseStep 507227 = 760841) B760841
theorem B507247 : Blo 503794 507247 := bstep (se 1 (by rfl) ⟨380435, by rfl⟩ : syracuseStep 507247 = 760871) B760871
theorem B507303 : Blo 503794 507303 := bstep (se 1 (by rfl) ⟨380477, by rfl⟩ : syracuseStep 507303 = 760955) B760955
theorem B540155 : Blo 503794 540155 := bstep (se 1 (by rfl) ⟨405116, by rfl⟩ : syracuseStep 540155 = 810233) B810233
theorem B507387 : Blo 503794 507387 := bstep (se 1 (by rfl) ⟨380540, by rfl⟩ : syracuseStep 507387 = 761081) B761081
theorem B507455 : Blo 503794 507455 := bstep (se 1 (by rfl) ⟨380591, by rfl⟩ : syracuseStep 507455 = 761183) B761183
theorem B507463 : Blo 503794 507463 := bstep (se 1 (by rfl) ⟨380597, by rfl⟩ : syracuseStep 507463 = 761195) B761195
theorem B8208017 : Blo 503794 8208017 := bstep (se 2 (by rfl) ⟨3078006, by rfl⟩ : syracuseStep 8208017 = 6156013) B6156013
theorem B507615 : Blo 503794 507615 := bstep (se 1 (by rfl) ⟨380711, by rfl⟩ : syracuseStep 507615 = 761423) B761423
theorem B507695 : Blo 503794 507695 := bstep (se 1 (by rfl) ⟨380771, by rfl⟩ : syracuseStep 507695 = 761543) B761543
theorem B3850091 : Blo 503794 3850091 := bstep (se 1 (by rfl) ⟨2887568, by rfl⟩ : syracuseStep 3850091 = 5775137) B5775137
theorem B1621889 : Blo 503794 1621889 := bstep (se 2 (by rfl) ⟨608208, by rfl⟩ : syracuseStep 1621889 = 1216417) B1216417
theorem B770153 : Blo 503794 770153 := bstep (se 2 (by rfl) ⟨288807, by rfl⟩ : syracuseStep 770153 = 577615) B577615
theorem B639343 : Blo 503794 639343 := bstep (se 1 (by rfl) ⟨479507, by rfl⟩ : syracuseStep 639343 = 959015) B959015
theorem B541279 : Blo 503794 541279 := bstep (se 1 (by rfl) ⟨405959, by rfl⟩ : syracuseStep 541279 = 811919) B811919
theorem B2048695 : Blo 503794 2048695 := bstep (se 1 (by rfl) ⟨1536521, by rfl⟩ : syracuseStep 2048695 = 3073043) B3073043
theorem B770743 : Blo 503794 770743 := bstep (se 1 (by rfl) ⟨578057, by rfl⟩ : syracuseStep 770743 = 1156115) B1156115
theorem B9192269 : Blo 503794 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B1918151 : Blo 503794 1918151 := bstep (se 1 (by rfl) ⟨1438613, by rfl⟩ : syracuseStep 1918151 = 2877227) B2877227
theorem B640219 : Blo 503794 640219 := bstep (se 1 (by rfl) ⟨480164, by rfl⟩ : syracuseStep 640219 = 960329) B960329
theorem B4376051 : Blo 503794 4376051 := bstep (se 1 (by rfl) ⟨3282038, by rfl⟩ : syracuseStep 4376051 = 6564077) B6564077
theorem B9193601 : Blo 503794 9193601 := bstep (se 2 (by rfl) ⟨3447600, by rfl⟩ : syracuseStep 9193601 = 6895201) B6895201
theorem B26364149 : Blo 503794 26364149 := bstep (se 5 (by rfl) ⟨1235819, by rfl⟩ : syracuseStep 26364149 = 2471639) B2471639
theorem B1624349 : Blo 503794 1624349 := bstep (se 3 (by rfl) ⟨304565, by rfl⟩ : syracuseStep 1624349 = 609131) B609131
theorem B3230063 : Blo 503794 3230063 := bstep (se 1 (by rfl) ⟨2422547, by rfl⟩ : syracuseStep 3230063 = 4845095) B4845095
theorem B3459557 : Blo 503794 3459557 := bstep (se 4 (by rfl) ⟨324333, by rfl⟩ : syracuseStep 3459557 = 648667) B648667
theorem B1821179 : Blo 503794 1821179 := bstep (se 1 (by rfl) ⟨1365884, by rfl⟩ : syracuseStep 1821179 = 2731769) B2731769
theorem B4868855 : Blo 503794 4868855 := bstep (se 1 (by rfl) ⟨3651641, by rfl⟩ : syracuseStep 4868855 = 7303283) B7303283
theorem B1624823 : Blo 503794 1624823 := bstep (se 1 (by rfl) ⟨1218617, by rfl⟩ : syracuseStep 1624823 = 2437235) B2437235
theorem B1362707 : Blo 503794 1362707 := bstep (se 1 (by rfl) ⟨1022030, by rfl⟩ : syracuseStep 1362707 = 2044061) B2044061
theorem B5557015 : Blo 503794 5557015 := bstep (se 1 (by rfl) ⟨4167761, by rfl⟩ : syracuseStep 5557015 = 8335523) B8335523
theorem B641839 : Blo 503794 641839 := bstep (se 1 (by rfl) ⟨481379, by rfl⟩ : syracuseStep 641839 = 962759) B962759
theorem B1133711 : Blo 503794 1133711 := bstep (se 1 (by rfl) ⟨850283, by rfl⟩ : syracuseStep 1133711 = 1700567) B1700567
theorem B1363159 : Blo 503794 1363159 := bstep (se 1 (by rfl) ⟨1022369, by rfl⟩ : syracuseStep 1363159 = 2044739) B2044739
theorem B1133801 : Blo 503794 1133801 := bstep (se 2 (by rfl) ⟨425175, by rfl⟩ : syracuseStep 1133801 = 850351) B850351
theorem B1133855 : Blo 503794 1133855 := bstep (se 1 (by rfl) ⟨850391, by rfl⟩ : syracuseStep 1133855 = 1700783) B1700783
theorem B1920779 : Blo 503794 1920779 := bstep (se 1 (by rfl) ⟨1440584, by rfl⟩ : syracuseStep 1920779 = 2881169) B2881169
theorem B1134377 : Blo 503794 1134377 := bstep (se 2 (by rfl) ⟨425391, by rfl⟩ : syracuseStep 1134377 = 850783) B850783
theorem B21843755 : Blo 503794 21843755 := bstep (se 1 (by rfl) ⟨16382816, by rfl⟩ : syracuseStep 21843755 = 32765633) B32765633
theorem B1822621 : Blo 503794 1822621 := bstep (se 3 (by rfl) ⟨341741, by rfl⟩ : syracuseStep 1822621 = 683483) B683483
theorem B2084923 : Blo 503794 2084923 := bstep (se 1 (by rfl) ⟨1563692, by rfl⟩ : syracuseStep 2084923 = 3127385) B3127385
theorem B1298761 : Blo 503794 1298761 := bstep (se 2 (by rfl) ⟨487035, by rfl⟩ : syracuseStep 1298761 = 974071) B974071
theorem B2740807 : Blo 503794 2740807 := bstep (se 1 (by rfl) ⟨2055605, by rfl⟩ : syracuseStep 2740807 = 4111211) B4111211
theorem B1364663 : Blo 503794 1364663 := bstep (se 1 (by rfl) ⟨1023497, by rfl⟩ : syracuseStep 1364663 = 2046995) B2046995
theorem B1135439 : Blo 503794 1135439 := bstep (se 1 (by rfl) ⟨851579, by rfl⟩ : syracuseStep 1135439 = 1703159) B1703159
theorem B578459 : Blo 503794 578459 := bstep (se 1 (by rfl) ⟨433844, by rfl⟩ : syracuseStep 578459 = 867689) B867689
theorem B1922039 : Blo 503794 1922039 := bstep (se 1 (by rfl) ⟨1441529, by rfl⟩ : syracuseStep 1922039 = 2883059) B2883059
theorem B1135655 : Blo 503794 1135655 := bstep (se 1 (by rfl) ⟨851741, by rfl⟩ : syracuseStep 1135655 = 1703483) B1703483
theorem B5002397 : Blo 503794 5002397 := bstep (se 3 (by rfl) ⟨937949, by rfl⟩ : syracuseStep 5002397 = 1875899) B1875899
theorem B1135835 : Blo 503794 1135835 := bstep (se 1 (by rfl) ⟨851876, by rfl⟩ : syracuseStep 1135835 = 1703753) B1703753
theorem B2741627 : Blo 503794 2741627 := bstep (se 1 (by rfl) ⟨2056220, by rfl⟩ : syracuseStep 2741627 = 4112441) B4112441
theorem B1136033 : Blo 503794 1136033 := bstep (se 2 (by rfl) ⟨426012, by rfl⟩ : syracuseStep 1136033 = 852025) B852025
theorem B1136591 : Blo 503794 1136591 := bstep (se 1 (by rfl) ⟨852443, by rfl⟩ : syracuseStep 1136591 = 1704887) B1704887
theorem B1136969 : Blo 503794 1136969 := bstep (se 2 (by rfl) ⟨426363, by rfl⟩ : syracuseStep 1136969 = 852727) B852727
theorem B1136987 : Blo 503794 1136987 := bstep (se 1 (by rfl) ⟨852740, by rfl⟩ : syracuseStep 1136987 = 1705481) B1705481
theorem B1464895 : Blo 503794 1464895 := bstep (se 1 (by rfl) ⟨1098671, by rfl⟩ : syracuseStep 1464895 = 2197343) B2197343
theorem B1923983 : Blo 503794 1923983 := bstep (se 1 (by rfl) ⟨1442987, by rfl⟩ : syracuseStep 1923983 = 2885975) B2885975
theorem B1137563 : Blo 503794 1137563 := bstep (se 1 (by rfl) ⟨853172, by rfl⟩ : syracuseStep 1137563 = 1706345) B1706345
theorem B44194895 : Blo 503794 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B1137761 : Blo 503794 1137761 := bstep (se 2 (by rfl) ⟨426660, by rfl⟩ : syracuseStep 1137761 = 853321) B853321
theorem B1137959 : Blo 503794 1137959 := bstep (se 1 (by rfl) ⟨853469, by rfl⟩ : syracuseStep 1137959 = 1706939) B1706939
theorem B1170875 : Blo 503794 1170875 := bstep (se 1 (by rfl) ⟨878156, by rfl⟩ : syracuseStep 1170875 = 1756313) B1756313
theorem B1138337 : Blo 503794 1138337 := bstep (se 2 (by rfl) ⟨426876, by rfl⟩ : syracuseStep 1138337 = 853753) B853753
theorem B1138697 : Blo 503794 1138697 := bstep (se 2 (by rfl) ⟨427011, by rfl⟩ : syracuseStep 1138697 = 854023) B854023
theorem B1139111 : Blo 503794 1139111 := bstep (se 1 (by rfl) ⟨854333, by rfl⟩ : syracuseStep 1139111 = 1708667) B1708667
theorem B1139219 : Blo 503794 1139219 := bstep (se 1 (by rfl) ⟨854414, by rfl⟩ : syracuseStep 1139219 = 1708829) B1708829
theorem B1139273 : Blo 503794 1139273 := bstep (se 2 (by rfl) ⟨427227, by rfl⟩ : syracuseStep 1139273 = 854455) B854455
theorem B2876087 : Blo 503794 2876087 := bstep (se 1 (by rfl) ⟨2157065, by rfl⟩ : syracuseStep 2876087 = 4314131) B4314131
theorem B1139687 : Blo 503794 1139687 := bstep (se 1 (by rfl) ⟨854765, by rfl⟩ : syracuseStep 1139687 = 1709531) B1709531
theorem B1827983 : Blo 503794 1827983 := bstep (se 1 (by rfl) ⟨1370987, by rfl⟩ : syracuseStep 1827983 = 2741975) B2741975
theorem B1926443 : Blo 503794 1926443 := bstep (se 1 (by rfl) ⟨1444832, by rfl⟩ : syracuseStep 1926443 = 2889665) B2889665
theorem B1140065 : Blo 503794 1140065 := bstep (se 2 (by rfl) ⟨427524, by rfl⟩ : syracuseStep 1140065 = 855049) B855049
theorem B2876795 : Blo 503794 2876795 := bstep (se 1 (by rfl) ⟨2157596, by rfl⟩ : syracuseStep 2876795 = 4315193) B4315193
theorem B1140155 : Blo 503794 1140155 := bstep (se 1 (by rfl) ⟨855116, by rfl⟩ : syracuseStep 1140155 = 1710233) B1710233
theorem B32826869 : Blo 503794 32826869 := bstep (se 5 (by rfl) ⟨1538759, by rfl⟩ : syracuseStep 32826869 = 3077519) B3077519
theorem B1140281 : Blo 503794 1140281 := bstep (se 2 (by rfl) ⟨427605, by rfl⟩ : syracuseStep 1140281 = 855211) B855211
theorem B4843097 : Blo 503794 4843097 := bstep (se 2 (by rfl) ⟨1816161, by rfl⟩ : syracuseStep 4843097 = 3632323) B3632323
theorem B4614023 : Blo 503794 4614023 := bstep (se 1 (by rfl) ⟨3460517, by rfl⟩ : syracuseStep 4614023 = 6921035) B6921035
theorem B1140947 : Blo 503794 1140947 := bstep (se 1 (by rfl) ⟨855710, by rfl⟩ : syracuseStep 1140947 = 1711421) B1711421
theorem B1141001 : Blo 503794 1141001 := bstep (se 2 (by rfl) ⟨427875, by rfl⟩ : syracuseStep 1141001 = 855751) B855751
theorem B1141217 : Blo 503794 1141217 := bstep (se 2 (by rfl) ⟨427956, by rfl⟩ : syracuseStep 1141217 = 855913) B855913
theorem B911945 : Blo 503794 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B1436267 : Blo 503794 1436267 := bstep (se 1 (by rfl) ⟨1077200, by rfl⟩ : syracuseStep 1436267 = 2154401) B2154401
theorem B20834995 : Blo 503794 20834995 := bstep (se 1 (by rfl) ⟨15626246, by rfl⟩ : syracuseStep 20834995 = 31252493) B31252493
theorem B1141523 : Blo 503794 1141523 := bstep (se 1 (by rfl) ⟨856142, by rfl⟩ : syracuseStep 1141523 = 1712285) B1712285
theorem B10414871 : Blo 503794 10414871 := bstep (se 1 (by rfl) ⟨7811153, by rfl⟩ : syracuseStep 10414871 = 15622307) B15622307
theorem B1141883 : Blo 503794 1141883 := bstep (se 1 (by rfl) ⟨856412, by rfl⟩ : syracuseStep 1141883 = 1712825) B1712825
theorem B1142009 : Blo 503794 1142009 := bstep (se 2 (by rfl) ⟨428253, by rfl⟩ : syracuseStep 1142009 = 856507) B856507
theorem B10349855 : Blo 503794 10349855 := bstep (se 1 (by rfl) ⟨7762391, by rfl⟩ : syracuseStep 10349855 = 15524783) B15524783
theorem B1437065 : Blo 503794 1437065 := bstep (se 2 (by rfl) ⟨538899, by rfl⟩ : syracuseStep 1437065 = 1077799) B1077799
theorem B1142153 : Blo 503794 1142153 := bstep (se 2 (by rfl) ⟨428307, by rfl⟩ : syracuseStep 1142153 = 856615) B856615
theorem B1142279 : Blo 503794 1142279 := bstep (se 1 (by rfl) ⟨856709, by rfl⟩ : syracuseStep 1142279 = 1713419) B1713419
theorem B1142459 : Blo 503794 1142459 := bstep (se 1 (by rfl) ⟨856844, by rfl⟩ : syracuseStep 1142459 = 1713689) B1713689
theorem B2879185 : Blo 503794 2879185 := bstep (se 2 (by rfl) ⟨1079694, by rfl⟩ : syracuseStep 2879185 = 2159389) B2159389
theorem B683743 : Blo 503794 683743 := bstep (se 1 (by rfl) ⟨512807, by rfl⟩ : syracuseStep 683743 = 1025615) B1025615
theorem B1077047 : Blo 503794 1077047 := bstep (se 1 (by rfl) ⟨807785, by rfl⟩ : syracuseStep 1077047 = 1615571) B1615571
theorem B1437497 : Blo 503794 1437497 := bstep (se 2 (by rfl) ⟨539061, by rfl⟩ : syracuseStep 1437497 = 1078123) B1078123
theorem B1437907 : Blo 503794 1437907 := bstep (se 1 (by rfl) ⟨1078430, by rfl⟩ : syracuseStep 1437907 = 2156861) B2156861
theorem B2159561 : Blo 503794 2159561 := bstep (se 2 (by rfl) ⟨809835, by rfl⟩ : syracuseStep 2159561 = 1619671) B1619671
theorem B2552795 : Blo 503794 2552795 := bstep (se 1 (by rfl) ⟨1914596, by rfl⟩ : syracuseStep 2552795 = 3829193) B3829193
theorem B2552957 : Blo 503794 2552957 := bstep (se 3 (by rfl) ⟨478679, by rfl⟩ : syracuseStep 2552957 = 957359) B957359
theorem B9893011 : Blo 503794 9893011 := bstep (se 1 (by rfl) ⟨7419758, by rfl⟩ : syracuseStep 9893011 = 14839517) B14839517
theorem B1701107 : Blo 503794 1701107 := bstep (se 1 (by rfl) ⟨1275830, by rfl⟩ : syracuseStep 1701107 = 2551661) B2551661
theorem B8189207 : Blo 503794 8189207 := bstep (se 1 (by rfl) ⟨6141905, by rfl⟩ : syracuseStep 8189207 = 12283811) B12283811
theorem B1701215 : Blo 503794 1701215 := bstep (se 1 (by rfl) ⟨1275911, by rfl⟩ : syracuseStep 1701215 = 2551823) B2551823
theorem B1439137 : Blo 503794 1439137 := bstep (se 2 (by rfl) ⟨539676, by rfl⟩ : syracuseStep 1439137 = 1079353) B1079353
theorem B2553281 : Blo 503794 2553281 := bstep (se 2 (by rfl) ⟨957480, by rfl⟩ : syracuseStep 2553281 = 1914961) B1914961
theorem B1275335 : Blo 503794 1275335 := bstep (se 1 (by rfl) ⟨956501, by rfl⟩ : syracuseStep 1275335 = 1913003) B1913003
theorem B1275385 : Blo 503794 1275385 := bstep (se 2 (by rfl) ⟨478269, by rfl⟩ : syracuseStep 1275385 = 956539) B956539
theorem B1078841 : Blo 503794 1078841 := bstep (se 2 (by rfl) ⟨404565, by rfl⟩ : syracuseStep 1078841 = 809131) B809131
theorem B1111739 : Blo 503794 1111739 := bstep (se 1 (by rfl) ⟨833804, by rfl⟩ : syracuseStep 1111739 = 1667609) B1667609
theorem B1275689 : Blo 503794 1275689 := bstep (se 2 (by rfl) ⟨478383, by rfl⟩ : syracuseStep 1275689 = 956767) B956767
theorem B1276033 : Blo 503794 1276033 := bstep (se 2 (by rfl) ⟨478512, by rfl⟩ : syracuseStep 1276033 = 957025) B957025
theorem B1079507 : Blo 503794 1079507 := bstep (se 1 (by rfl) ⟨809630, by rfl⟩ : syracuseStep 1079507 = 1619261) B1619261
theorem B2160893 : Blo 503794 2160893 := bstep (se 3 (by rfl) ⟨405167, by rfl⟩ : syracuseStep 2160893 = 810335) B810335
theorem B719113 : Blo 503794 719113 := bstep (se 2 (by rfl) ⟨269667, by rfl⟩ : syracuseStep 719113 = 539335) B539335
theorem B850655 : Blo 503794 850655 := bstep (se 1 (by rfl) ⟨637991, by rfl⟩ : syracuseStep 850655 = 1275983) B1275983
theorem B3832595 : Blo 503794 3832595 := bstep (se 1 (by rfl) ⟨2874446, by rfl⟩ : syracuseStep 3832595 = 5748893) B5748893
theorem B2161475 : Blo 503794 2161475 := bstep (se 1 (by rfl) ⟨1621106, by rfl⟩ : syracuseStep 2161475 = 3242213) B3242213
theorem B8616779 : Blo 503794 8616779 := bstep (se 1 (by rfl) ⟨6462584, by rfl⟩ : syracuseStep 8616779 = 12925169) B12925169
theorem B1702781 : Blo 503794 1702781 := bstep (se 3 (by rfl) ⟨319271, by rfl⟩ : syracuseStep 1702781 = 638543) B638543
theorem B1276843 : Blo 503794 1276843 := bstep (se 1 (by rfl) ⟨957632, by rfl⟩ : syracuseStep 1276843 = 1915265) B1915265
theorem B1703051 : Blo 503794 1703051 := bstep (se 1 (by rfl) ⟨1277288, by rfl⟩ : syracuseStep 1703051 = 2554577) B2554577
theorem B851087 : Blo 503794 851087 := bstep (se 1 (by rfl) ⟨638315, by rfl⟩ : syracuseStep 851087 = 1276631) B1276631
theorem B1277147 : Blo 503794 1277147 := bstep (se 1 (by rfl) ⟨957860, by rfl⟩ : syracuseStep 1277147 = 1915721) B1915721
theorem B1277279 : Blo 503794 1277279 := bstep (se 1 (by rfl) ⟨957959, by rfl⟩ : syracuseStep 1277279 = 1915919) B1915919
theorem B851323 : Blo 503794 851323 := bstep (se 1 (by rfl) ⟨638492, by rfl⟩ : syracuseStep 851323 = 1276985) B1276985
theorem B10911149 : Blo 503794 10911149 := bstep (se 3 (by rfl) ⟨2045840, by rfl⟩ : syracuseStep 10911149 = 4091681) B4091681
theorem B1441223 : Blo 503794 1441223 := bstep (se 1 (by rfl) ⟨1080917, by rfl⟩ : syracuseStep 1441223 = 2161835) B2161835
theorem B4849247 : Blo 503794 4849247 := bstep (se 1 (by rfl) ⟨3636935, by rfl⟩ : syracuseStep 4849247 = 7273871) B7273871
theorem B1703969 : Blo 503794 1703969 := bstep (se 2 (by rfl) ⟨638988, by rfl⟩ : syracuseStep 1703969 = 1277977) B1277977
theorem B14614627 : Blo 503794 14614627 := bstep (se 1 (by rfl) ⟨10960970, by rfl⟩ : syracuseStep 14614627 = 21921941) B21921941
theorem B852187 : Blo 503794 852187 := bstep (se 1 (by rfl) ⟨639140, by rfl⟩ : syracuseStep 852187 = 1278281) B1278281
theorem B3244313 : Blo 503794 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B2556359 : Blo 503794 2556359 := bstep (se 1 (by rfl) ⟨1917269, by rfl⟩ : syracuseStep 2556359 = 3834539) B3834539
theorem B852457 : Blo 503794 852457 := bstep (se 2 (by rfl) ⟨319671, by rfl⟩ : syracuseStep 852457 = 639343) B639343
theorem B1442281 : Blo 503794 1442281 := bstep (se 2 (by rfl) ⟨540855, by rfl⟩ : syracuseStep 1442281 = 1081711) B1081711
theorem B6128179 : Blo 503794 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B2196233 : Blo 503794 2196233 := bstep (se 2 (by rfl) ⟨823587, by rfl⟩ : syracuseStep 2196233 = 1647175) B1647175
theorem B721705 : Blo 503794 721705 := bstep (se 2 (by rfl) ⟨270639, by rfl⟩ : syracuseStep 721705 = 541279) B541279
theorem B1278767 : Blo 503794 1278767 := bstep (se 1 (by rfl) ⟨959075, by rfl⟩ : syracuseStep 1278767 = 1918151) B1918151
theorem B2917367 : Blo 503794 2917367 := bstep (se 1 (by rfl) ⟨2188025, by rfl⟩ : syracuseStep 2917367 = 4376051) B4376051
theorem B6129067 : Blo 503794 6129067 := bstep (se 1 (by rfl) ⟨4596800, by rfl⟩ : syracuseStep 6129067 = 9193601) B9193601
theorem B1082899 : Blo 503794 1082899 := bstep (se 1 (by rfl) ⟨812174, by rfl⟩ : syracuseStep 1082899 = 1624349) B1624349
theorem B853625 : Blo 503794 853625 := bstep (se 2 (by rfl) ⟨320109, by rfl⟩ : syracuseStep 853625 = 640219) B640219
theorem B1214119 : Blo 503794 1214119 := bstep (se 1 (by rfl) ⟨910589, by rfl⟩ : syracuseStep 1214119 = 1821179) B1821179
theorem B1967951 : Blo 503794 1967951 := bstep (se 1 (by rfl) ⟨1475963, by rfl⟩ : syracuseStep 1967951 = 2951927) B2951927
theorem B3245903 : Blo 503794 3245903 := bstep (se 1 (by rfl) ⟨2434427, by rfl⟩ : syracuseStep 3245903 = 4868855) B4868855
theorem B1083215 : Blo 503794 1083215 := bstep (se 1 (by rfl) ⟨812411, by rfl⟩ : syracuseStep 1083215 = 1624823) B1624823
theorem B3245953 : Blo 503794 3245953 := bstep (se 2 (by rfl) ⟨1217232, by rfl⟩ : syracuseStep 3245953 = 2434465) B2434465
theorem B755705 : Blo 503794 755705 := bstep (se 2 (by rfl) ⟨283389, by rfl⟩ : syracuseStep 755705 = 566779) B566779
theorem B755807 : Blo 503794 755807 := bstep (se 1 (by rfl) ⟨566855, by rfl⟩ : syracuseStep 755807 = 1133711) B1133711
theorem B854111 : Blo 503794 854111 := bstep (se 1 (by rfl) ⟨640583, by rfl⟩ : syracuseStep 854111 = 1281167) B1281167
theorem B755867 : Blo 503794 755867 := bstep (se 1 (by rfl) ⟨566900, by rfl⟩ : syracuseStep 755867 = 1133801) B1133801
theorem B755903 : Blo 503794 755903 := bstep (se 1 (by rfl) ⟨566927, by rfl⟩ : syracuseStep 755903 = 1133855) B1133855
theorem B755945 : Blo 503794 755945 := bstep (se 2 (by rfl) ⟨283479, by rfl⟩ : syracuseStep 755945 = 566959) B566959
theorem B6162779 : Blo 503794 6162779 := bstep (se 1 (by rfl) ⟨4622084, by rfl⟩ : syracuseStep 6162779 = 9244169) B9244169
theorem B1542557 : Blo 503794 1542557 := bstep (se 3 (by rfl) ⟨289229, by rfl⟩ : syracuseStep 1542557 = 578459) B578459
theorem B1280519 : Blo 503794 1280519 := bstep (se 1 (by rfl) ⟨960389, by rfl⟩ : syracuseStep 1280519 = 1920779) B1920779
theorem B756251 : Blo 503794 756251 := bstep (se 1 (by rfl) ⟨567188, by rfl⟩ : syracuseStep 756251 = 1134377) B1134377
theorem B756329 : Blo 503794 756329 := bstep (se 2 (by rfl) ⟨283623, by rfl⟩ : syracuseStep 756329 = 567247) B567247
theorem B2558951 : Blo 503794 2558951 := bstep (se 1 (by rfl) ⟨1919213, by rfl⟩ : syracuseStep 2558951 = 3838427) B3838427
theorem B756857 : Blo 503794 756857 := bstep (se 2 (by rfl) ⟨283821, by rfl⟩ : syracuseStep 756857 = 567643) B567643
theorem B756959 : Blo 503794 756959 := bstep (se 1 (by rfl) ⟨567719, by rfl⟩ : syracuseStep 756959 = 1135439) B1135439
theorem B757001 : Blo 503794 757001 := bstep (se 2 (by rfl) ⟨283875, by rfl⟩ : syracuseStep 757001 = 567751) B567751
theorem B1281359 : Blo 503794 1281359 := bstep (se 1 (by rfl) ⟨961019, by rfl⟩ : syracuseStep 1281359 = 1922039) B1922039
theorem B757103 : Blo 503794 757103 := bstep (se 1 (by rfl) ⟨567827, by rfl⟩ : syracuseStep 757103 = 1135655) B1135655
theorem B855407 : Blo 503794 855407 := bstep (se 1 (by rfl) ⟨641555, by rfl⟩ : syracuseStep 855407 = 1283111) B1283111
theorem B757223 : Blo 503794 757223 := bstep (se 1 (by rfl) ⟨567917, by rfl⟩ : syracuseStep 757223 = 1135835) B1135835
theorem B855643 : Blo 503794 855643 := bstep (se 1 (by rfl) ⟨641732, by rfl⟩ : syracuseStep 855643 = 1283465) B1283465
theorem B757355 : Blo 503794 757355 := bstep (se 1 (by rfl) ⟨568016, by rfl⟩ : syracuseStep 757355 = 1136033) B1136033
theorem B7311005 : Blo 503794 7311005 := bstep (se 3 (by rfl) ⟨1370813, by rfl⟩ : syracuseStep 7311005 = 2741627) B2741627
theorem B1707695 : Blo 503794 1707695 := bstep (se 1 (by rfl) ⟨1280771, by rfl⟩ : syracuseStep 1707695 = 2561543) B2561543
theorem B757481 : Blo 503794 757481 := bstep (se 2 (by rfl) ⟨284055, by rfl⟩ : syracuseStep 757481 = 568111) B568111
theorem B855785 : Blo 503794 855785 := bstep (se 2 (by rfl) ⟨320919, by rfl⟩ : syracuseStep 855785 = 641839) B641839
theorem B757625 : Blo 503794 757625 := bstep (se 2 (by rfl) ⟨284109, by rfl⟩ : syracuseStep 757625 = 568219) B568219
theorem B6492109 : Blo 503794 6492109 := bstep (se 3 (by rfl) ⟨1217270, by rfl⟩ : syracuseStep 6492109 = 2434541) B2434541
theorem B757727 : Blo 503794 757727 := bstep (se 1 (by rfl) ⟨568295, by rfl⟩ : syracuseStep 757727 = 1136591) B1136591
theorem B1708019 : Blo 503794 1708019 := bstep (se 1 (by rfl) ⟨1281014, by rfl⟩ : syracuseStep 1708019 = 2562029) B2562029
theorem B757979 : Blo 503794 757979 := bstep (se 1 (by rfl) ⟨568484, by rfl⟩ : syracuseStep 757979 = 1136969) B1136969
theorem B757991 : Blo 503794 757991 := bstep (se 1 (by rfl) ⟨568493, by rfl⟩ : syracuseStep 757991 = 1136987) B1136987
theorem B2887933 : Blo 503794 2887933 := bstep (se 3 (by rfl) ⟨541487, by rfl⟩ : syracuseStep 2887933 = 1082975) B1082975
theorem B1708343 : Blo 503794 1708343 := bstep (se 1 (by rfl) ⟨1281257, by rfl⟩ : syracuseStep 1708343 = 2562515) B2562515
theorem B758153 : Blo 503794 758153 := bstep (se 2 (by rfl) ⟨284307, by rfl⟩ : syracuseStep 758153 = 568615) B568615
theorem B758249 : Blo 503794 758249 := bstep (se 2 (by rfl) ⟨284343, by rfl⟩ : syracuseStep 758249 = 568687) B568687
theorem B1708559 : Blo 503794 1708559 := bstep (se 1 (by rfl) ⟨1281419, by rfl⟩ : syracuseStep 1708559 = 2562839) B2562839
theorem B1282655 : Blo 503794 1282655 := bstep (se 1 (by rfl) ⟨961991, by rfl⟩ : syracuseStep 1282655 = 1923983) B1923983
theorem B758375 : Blo 503794 758375 := bstep (se 1 (by rfl) ⟨568781, by rfl⟩ : syracuseStep 758375 = 1137563) B1137563
theorem B29463263 : Blo 503794 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B758507 : Blo 503794 758507 := bstep (se 1 (by rfl) ⟨568880, by rfl⟩ : syracuseStep 758507 = 1137761) B1137761
theorem B856811 : Blo 503794 856811 := bstep (se 1 (by rfl) ⟨642608, by rfl⟩ : syracuseStep 856811 = 1285217) B1285217
theorem B758537 : Blo 503794 758537 := bstep (se 2 (by rfl) ⟨284451, by rfl⟩ : syracuseStep 758537 = 568903) B568903
theorem B758639 : Blo 503794 758639 := bstep (se 1 (by rfl) ⟨568979, by rfl⟩ : syracuseStep 758639 = 1137959) B1137959
theorem B3838913 : Blo 503794 3838913 := bstep (se 2 (by rfl) ⟨1439592, by rfl⟩ : syracuseStep 3838913 = 2879185) B2879185
theorem B758891 : Blo 503794 758891 := bstep (se 1 (by rfl) ⟨569168, by rfl⟩ : syracuseStep 758891 = 1138337) B1138337
theorem B2430161 : Blo 503794 2430161 := bstep (se 2 (by rfl) ⟨911310, by rfl⟩ : syracuseStep 2430161 = 1822621) B1822621
theorem B759131 : Blo 503794 759131 := bstep (se 1 (by rfl) ⟨569348, by rfl⟩ : syracuseStep 759131 = 1138697) B1138697
theorem B3249517 : Blo 503794 3249517 := bstep (se 3 (by rfl) ⟨609284, by rfl⟩ : syracuseStep 3249517 = 1218569) B1218569
theorem B1709639 : Blo 503794 1709639 := bstep (se 1 (by rfl) ⟨1282229, by rfl⟩ : syracuseStep 1709639 = 2564459) B2564459
theorem B759407 : Blo 503794 759407 := bstep (se 1 (by rfl) ⟨569555, by rfl⟩ : syracuseStep 759407 = 1139111) B1139111
theorem B759479 : Blo 503794 759479 := bstep (se 1 (by rfl) ⟨569609, by rfl⟩ : syracuseStep 759479 = 1139219) B1139219
theorem B759515 : Blo 503794 759515 := bstep (se 1 (by rfl) ⟨569636, by rfl⟩ : syracuseStep 759515 = 1139273) B1139273
theorem B759689 : Blo 503794 759689 := bstep (se 2 (by rfl) ⟨284883, by rfl⟩ : syracuseStep 759689 = 569767) B569767
theorem B759791 : Blo 503794 759791 := bstep (se 1 (by rfl) ⟨569843, by rfl⟩ : syracuseStep 759791 = 1139687) B1139687
theorem B22124609 : Blo 503794 22124609 := bstep (se 2 (by rfl) ⟨8296728, by rfl⟩ : syracuseStep 22124609 = 16593457) B16593457
theorem B1218655 : Blo 503794 1218655 := bstep (se 1 (by rfl) ⟨913991, by rfl⟩ : syracuseStep 1218655 = 1827983) B1827983
theorem B1153121 : Blo 503794 1153121 := bstep (se 2 (by rfl) ⟨432420, by rfl⟩ : syracuseStep 1153121 = 864841) B864841
theorem B1284295 : Blo 503794 1284295 := bstep (se 1 (by rfl) ⟨963221, by rfl⟩ : syracuseStep 1284295 = 1926443) B1926443
theorem B760043 : Blo 503794 760043 := bstep (se 1 (by rfl) ⟨570032, by rfl⟩ : syracuseStep 760043 = 1140065) B1140065
theorem B760103 : Blo 503794 760103 := bstep (se 1 (by rfl) ⟨570077, by rfl⟩ : syracuseStep 760103 = 1140155) B1140155
theorem B760187 : Blo 503794 760187 := bstep (se 1 (by rfl) ⟨570140, by rfl⟩ : syracuseStep 760187 = 1140281) B1140281
theorem B1710611 : Blo 503794 1710611 := bstep (se 1 (by rfl) ⟨1282958, by rfl⟩ : syracuseStep 1710611 = 2565917) B2565917
theorem B760457 : Blo 503794 760457 := bstep (se 2 (by rfl) ⟨285171, by rfl⟩ : syracuseStep 760457 = 570343) B570343
theorem B760631 : Blo 503794 760631 := bstep (se 1 (by rfl) ⟨570473, by rfl⟩ : syracuseStep 760631 = 1140947) B1140947
theorem B760667 : Blo 503794 760667 := bstep (se 1 (by rfl) ⟨570500, by rfl⟩ : syracuseStep 760667 = 1141001) B1141001
theorem B2431853 : Blo 503794 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B2890667 : Blo 503794 2890667 := bstep (se 1 (by rfl) ⟨2168000, by rfl⟩ : syracuseStep 2890667 = 4336001) B4336001
theorem B760811 : Blo 503794 760811 := bstep (se 1 (by rfl) ⟨570608, by rfl⟩ : syracuseStep 760811 = 1141217) B1141217
theorem B957511 : Blo 503794 957511 := bstep (se 1 (by rfl) ⟨718133, by rfl⟩ : syracuseStep 957511 = 1436267) B1436267
theorem B761015 : Blo 503794 761015 := bstep (se 1 (by rfl) ⟨570761, by rfl⟩ : syracuseStep 761015 = 1141523) B1141523
theorem B2563325 : Blo 503794 2563325 := bstep (se 3 (by rfl) ⟨480623, by rfl⟩ : syracuseStep 2563325 = 961247) B961247
theorem B23403907 : Blo 503794 23403907 := bstep (se 1 (by rfl) ⟨17552930, by rfl⟩ : syracuseStep 23403907 = 35105861) B35105861
theorem B761255 : Blo 503794 761255 := bstep (se 1 (by rfl) ⟨570941, by rfl⟩ : syracuseStep 761255 = 1141883) B1141883
theorem B761339 : Blo 503794 761339 := bstep (se 1 (by rfl) ⟨571004, by rfl⟩ : syracuseStep 761339 = 1142009) B1142009
theorem B7380485 : Blo 503794 7380485 := bstep (se 4 (by rfl) ⟨691920, by rfl⟩ : syracuseStep 7380485 = 1383841) B1383841
theorem B958043 : Blo 503794 958043 := bstep (se 1 (by rfl) ⟨718532, by rfl⟩ : syracuseStep 958043 = 1437065) B1437065
theorem B761435 : Blo 503794 761435 := bstep (se 1 (by rfl) ⟨571076, by rfl⟩ : syracuseStep 761435 = 1142153) B1142153
theorem B761519 : Blo 503794 761519 := bstep (se 1 (by rfl) ⟨571139, by rfl⟩ : syracuseStep 761519 = 1142279) B1142279
theorem B761639 : Blo 503794 761639 := bstep (se 1 (by rfl) ⟨571229, by rfl⟩ : syracuseStep 761639 = 1142459) B1142459
theorem B958331 : Blo 503794 958331 := bstep (se 1 (by rfl) ⟨718748, by rfl⟩ : syracuseStep 958331 = 1437497) B1437497
theorem B2564135 : Blo 503794 2564135 := bstep (se 1 (by rfl) ⟨1923101, by rfl⟩ : syracuseStep 2564135 = 3846203) B3846203
theorem B958817 : Blo 503794 958817 := bstep (se 2 (by rfl) ⟨359556, by rfl⟩ : syracuseStep 958817 = 719113) B719113
theorem B1319375 : Blo 503794 1319375 := bstep (se 1 (by rfl) ⟨989531, by rfl⟩ : syracuseStep 1319375 = 1979063) B1979063
theorem B2302739 : Blo 503794 2302739 := bstep (se 1 (by rfl) ⟨1727054, by rfl⟩ : syracuseStep 2302739 = 3454109) B3454109
theorem B1581935 : Blo 503794 1581935 := bstep (se 1 (by rfl) ⟨1186451, by rfl⟩ : syracuseStep 1581935 = 2372903) B2372903
theorem B2565107 : Blo 503794 2565107 := bstep (se 1 (by rfl) ⟨1923830, by rfl⟩ : syracuseStep 2565107 = 3847661) B3847661
theorem B1713257 : Blo 503794 1713257 := bstep (se 2 (by rfl) ⟨642471, by rfl⟩ : syracuseStep 1713257 = 1284943) B1284943
theorem B3122333 : Blo 503794 3122333 := bstep (se 3 (by rfl) ⟨585437, by rfl⟩ : syracuseStep 3122333 = 1170875) B1170875
theorem B5481701 : Blo 503794 5481701 := bstep (se 4 (by rfl) ⟨513909, by rfl⟩ : syracuseStep 5481701 = 1027819) B1027819
theorem B4596983 : Blo 503794 4596983 := bstep (se 1 (by rfl) ⟨3447737, by rfl⟩ : syracuseStep 4596983 = 6895475) B6895475
theorem B567103 : Blo 503794 567103 := bstep (se 1 (by rfl) ⟨425327, by rfl⟩ : syracuseStep 567103 = 850655) B850655
theorem B1386319 : Blo 503794 1386319 := bstep (se 1 (by rfl) ⟨1039739, by rfl⟩ : syracuseStep 1386319 = 2079479) B2079479
theorem B5744519 : Blo 503794 5744519 := bstep (se 1 (by rfl) ⟨4308389, by rfl⟩ : syracuseStep 5744519 = 8616779) B8616779
theorem B567391 : Blo 503794 567391 := bstep (se 1 (by rfl) ⟨425543, by rfl⟩ : syracuseStep 567391 = 851087) B851087
theorem B6498467 : Blo 503794 6498467 := bstep (se 1 (by rfl) ⟨4873850, by rfl⟩ : syracuseStep 6498467 = 9747701) B9747701
theorem B960815 : Blo 503794 960815 := bstep (se 1 (by rfl) ⟨720611, by rfl⟩ : syracuseStep 960815 = 1441223) B1441223
theorem B2566727 : Blo 503794 2566727 := bstep (se 1 (by rfl) ⟨1925045, by rfl⟩ : syracuseStep 2566727 = 3850091) B3850091
theorem B11119589 : Blo 503794 11119589 := bstep (se 4 (by rfl) ⟨1042461, by rfl⟩ : syracuseStep 11119589 = 2084923) B2084923
theorem B568543 : Blo 503794 568543 := bstep (se 1 (by rfl) ⟨426407, by rfl⟩ : syracuseStep 568543 = 852815) B852815
theorem B7318795 : Blo 503794 7318795 := bstep (se 1 (by rfl) ⟨5489096, by rfl⟩ : syracuseStep 7318795 = 10978193) B10978193
theorem B1027657 : Blo 503794 1027657 := bstep (se 2 (by rfl) ⟨385371, by rfl⟩ : syracuseStep 1027657 = 770743) B770743
theorem B1617583 : Blo 503794 1617583 := bstep (se 1 (by rfl) ⟨1213187, by rfl⟩ : syracuseStep 1617583 = 2426375) B2426375
theorem B17576099 : Blo 503794 17576099 := bstep (se 1 (by rfl) ⟨13182074, by rfl⟩ : syracuseStep 17576099 = 26364149) B26364149
theorem B504039 : Blo 503794 504039 := bstep (se 1 (by rfl) ⟨378029, by rfl⟩ : syracuseStep 504039 = 756059) B756059
theorem B1454345 : Blo 503794 1454345 := bstep (se 2 (by rfl) ⟨545379, by rfl⟩ : syracuseStep 1454345 = 1090759) B1090759
theorem B4108553 : Blo 503794 4108553 := bstep (se 2 (by rfl) ⟨1540707, by rfl⟩ : syracuseStep 4108553 = 3081415) B3081415
theorem B504191 : Blo 503794 504191 := bstep (se 1 (by rfl) ⟨378143, by rfl⟩ : syracuseStep 504191 = 756287) B756287
theorem B6926725 : Blo 503794 6926725 := bstep (se 4 (by rfl) ⟨649380, by rfl⟩ : syracuseStep 6926725 = 1298761) B1298761
theorem B504271 : Blo 503794 504271 := bstep (se 1 (by rfl) ⟨378203, by rfl⟩ : syracuseStep 504271 = 756407) B756407
theorem B504423 : Blo 503794 504423 := bstep (se 1 (by rfl) ⟨378317, by rfl⟩ : syracuseStep 504423 = 756635) B756635
theorem B504687 : Blo 503794 504687 := bstep (se 1 (by rfl) ⟨378515, by rfl⟩ : syracuseStep 504687 = 757031) B757031
theorem B504743 : Blo 503794 504743 := bstep (se 1 (by rfl) ⟨378557, by rfl⟩ : syracuseStep 504743 = 757115) B757115
theorem B504827 : Blo 503794 504827 := bstep (se 1 (by rfl) ⟨378620, by rfl⟩ : syracuseStep 504827 = 757241) B757241
theorem B767039 : Blo 503794 767039 := bstep (se 1 (by rfl) ⟨575279, by rfl⟩ : syracuseStep 767039 = 1150559) B1150559
theorem B504895 : Blo 503794 504895 := bstep (se 1 (by rfl) ⟨378671, by rfl⟩ : syracuseStep 504895 = 757343) B757343
theorem B963647 : Blo 503794 963647 := bstep (se 1 (by rfl) ⟨722735, by rfl⟩ : syracuseStep 963647 = 1445471) B1445471
theorem B14562503 : Blo 503794 14562503 := bstep (se 1 (by rfl) ⟨10921877, by rfl⟩ : syracuseStep 14562503 = 21843755) B21843755
theorem B505039 : Blo 503794 505039 := bstep (se 1 (by rfl) ⟨378779, by rfl⟩ : syracuseStep 505039 = 757559) B757559
theorem B505243 : Blo 503794 505243 := bstep (se 1 (by rfl) ⟨378932, by rfl⟩ : syracuseStep 505243 = 757865) B757865
theorem B505455 : Blo 503794 505455 := bstep (se 1 (by rfl) ⟨379091, by rfl⟩ : syracuseStep 505455 = 758183) B758183
theorem B570991 : Blo 503794 570991 := bstep (se 1 (by rfl) ⟨428243, by rfl⟩ : syracuseStep 570991 = 856487) B856487
theorem B505511 : Blo 503794 505511 := bstep (se 1 (by rfl) ⟨379133, by rfl⟩ : syracuseStep 505511 = 758267) B758267
theorem B571099 : Blo 503794 571099 := bstep (se 1 (by rfl) ⟨428324, by rfl⟩ : syracuseStep 571099 = 856649) B856649
theorem B505595 : Blo 503794 505595 := bstep (se 1 (by rfl) ⟨379196, by rfl⟩ : syracuseStep 505595 = 758393) B758393
theorem B505631 : Blo 503794 505631 := bstep (se 1 (by rfl) ⟨379223, by rfl⟩ : syracuseStep 505631 = 758447) B758447
theorem B505663 : Blo 503794 505663 := bstep (se 1 (by rfl) ⟨379247, by rfl⟩ : syracuseStep 505663 = 758495) B758495
theorem B2733887 : Blo 503794 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B505839 : Blo 503794 505839 := bstep (se 1 (by rfl) ⟨379379, by rfl⟩ : syracuseStep 505839 = 758759) B758759
theorem B506011 : Blo 503794 506011 := bstep (se 1 (by rfl) ⟨379508, by rfl⟩ : syracuseStep 506011 = 759017) B759017
theorem B506047 : Blo 503794 506047 := bstep (se 1 (by rfl) ⟨379535, by rfl⟩ : syracuseStep 506047 = 759071) B759071
theorem B10926373 : Blo 503794 10926373 := bstep (se 4 (by rfl) ⟨1024347, by rfl⟩ : syracuseStep 10926373 = 2048695) B2048695
theorem B506159 : Blo 503794 506159 := bstep (se 1 (by rfl) ⟨379619, by rfl⟩ : syracuseStep 506159 = 759239) B759239
theorem B506395 : Blo 503794 506395 := bstep (se 1 (by rfl) ⟨379796, by rfl⟩ : syracuseStep 506395 = 759593) B759593
theorem B506399 : Blo 503794 506399 := bstep (se 1 (by rfl) ⟨379799, by rfl⟩ : syracuseStep 506399 = 759599) B759599
theorem B29637413 : Blo 503794 29637413 := bstep (se 4 (by rfl) ⟨2778507, by rfl⟩ : syracuseStep 29637413 = 5557015) B5557015
theorem B506715 : Blo 503794 506715 := bstep (se 1 (by rfl) ⟨380036, by rfl⟩ : syracuseStep 506715 = 760073) B760073
theorem B506783 : Blo 503794 506783 := bstep (se 1 (by rfl) ⟨380087, by rfl⟩ : syracuseStep 506783 = 760175) B760175
theorem B506927 : Blo 503794 506927 := bstep (se 1 (by rfl) ⟨380195, by rfl⟩ : syracuseStep 506927 = 760391) B760391
theorem B506951 : Blo 503794 506951 := bstep (se 1 (by rfl) ⟨380213, by rfl⟩ : syracuseStep 506951 = 760427) B760427
theorem B2964637 : Blo 503794 2964637 := bstep (se 3 (by rfl) ⟨555869, by rfl⟩ : syracuseStep 2964637 = 1111739) B1111739
theorem B507103 : Blo 503794 507103 := bstep (se 1 (by rfl) ⟨380327, by rfl⟩ : syracuseStep 507103 = 760655) B760655
theorem B1621387 : Blo 503794 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B507367 : Blo 503794 507367 := bstep (se 1 (by rfl) ⟨380525, by rfl⟩ : syracuseStep 507367 = 761051) B761051
theorem B507483 : Blo 503794 507483 := bstep (se 1 (by rfl) ⟨380612, by rfl⟩ : syracuseStep 507483 = 761225) B761225
theorem B12304061 : Blo 503794 12304061 := bstep (se 3 (by rfl) ⟨2307011, by rfl⟩ : syracuseStep 12304061 = 4614023) B4614023
theorem B507719 : Blo 503794 507719 := bstep (se 1 (by rfl) ⟨380789, by rfl⟩ : syracuseStep 507719 = 761579) B761579
theorem B1917209 : Blo 503794 1917209 := bstep (se 2 (by rfl) ⟨718953, by rfl⟩ : syracuseStep 1917209 = 1437907) B1437907
theorem B1917391 : Blo 503794 1917391 := bstep (se 1 (by rfl) ⟨1438043, by rfl⟩ : syracuseStep 1917391 = 2876087) B2876087
theorem B10535669 : Blo 503794 10535669 := bstep (se 5 (by rfl) ⟨493859, by rfl⟩ : syracuseStep 10535669 = 987719) B987719
theorem B3654409 : Blo 503794 3654409 := bstep (se 2 (by rfl) ⟨1370403, by rfl⟩ : syracuseStep 3654409 = 2740807) B2740807
theorem B1917863 : Blo 503794 1917863 := bstep (se 1 (by rfl) ⟨1438397, by rfl⟩ : syracuseStep 1917863 = 2876795) B2876795
theorem B3228731 : Blo 503794 3228731 := bstep (se 1 (by rfl) ⟨2421548, by rfl⟩ : syracuseStep 3228731 = 4843097) B4843097
theorem B1754171 : Blo 503794 1754171 := bstep (se 1 (by rfl) ⟨1315628, by rfl⟩ : syracuseStep 1754171 = 2631257) B2631257
theorem B9225485 : Blo 503794 9225485 := bstep (se 3 (by rfl) ⟨1729778, by rfl⟩ : syracuseStep 9225485 = 3459557) B3459557
theorem B3065363 : Blo 503794 3065363 := bstep (se 1 (by rfl) ⟨2299022, by rfl⟩ : syracuseStep 3065363 = 4598045) B4598045
theorem B13190681 : Blo 503794 13190681 := bstep (se 2 (by rfl) ⟨4946505, by rfl⟩ : syracuseStep 13190681 = 9893011) B9893011
theorem B1918849 : Blo 503794 1918849 := bstep (se 2 (by rfl) ⟨719568, by rfl⟩ : syracuseStep 1918849 = 1439137) B1439137
theorem B6899903 : Blo 503794 6899903 := bstep (se 1 (by rfl) ⟨5174927, by rfl⟩ : syracuseStep 6899903 = 10349855) B10349855
theorem B2738387 : Blo 503794 2738387 := bstep (se 1 (by rfl) ⟨2053790, by rfl⟩ : syracuseStep 2738387 = 4107581) B4107581
theorem B2870437 : Blo 503794 2870437 := bstep (se 4 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 2870437 = 538207) B538207
theorem B1953193 : Blo 503794 1953193 := bstep (se 2 (by rfl) ⟨732447, by rfl⟩ : syracuseStep 1953193 = 1464895) B1464895
theorem B2870711 : Blo 503794 2870711 := bstep (se 1 (by rfl) ⟨2153033, by rfl⟩ : syracuseStep 2870711 = 4306067) B4306067
theorem B1134071 : Blo 503794 1134071 := bstep (se 1 (by rfl) ⟨850553, by rfl⟩ : syracuseStep 1134071 = 1701107) B1701107
theorem B1625591 : Blo 503794 1625591 := bstep (se 1 (by rfl) ⟨1219193, by rfl⟩ : syracuseStep 1625591 = 2438387) B2438387
theorem B5459471 : Blo 503794 5459471 := bstep (se 1 (by rfl) ⟨4094603, by rfl⟩ : syracuseStep 5459471 = 8189207) B8189207
theorem B1134143 : Blo 503794 1134143 := bstep (se 1 (by rfl) ⟨850607, by rfl⟩ : syracuseStep 1134143 = 1701215) B1701215
theorem B3067769 : Blo 503794 3067769 := bstep (se 2 (by rfl) ⟨1150413, by rfl⟩ : syracuseStep 3067769 = 2300827) B2300827
theorem B1135097 : Blo 503794 1135097 := bstep (se 2 (by rfl) ⟨425661, by rfl⟩ : syracuseStep 1135097 = 851323) B851323
theorem B1135187 : Blo 503794 1135187 := bstep (se 1 (by rfl) ⟨851390, by rfl⟩ : syracuseStep 1135187 = 1702781) B1702781
theorem B971347 : Blo 503794 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B3854951 : Blo 503794 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B6148811 : Blo 503794 6148811 := bstep (se 1 (by rfl) ⟨4611608, by rfl⟩ : syracuseStep 6148811 = 9223217) B9223217
theorem B35050195 : Blo 503794 35050195 := bstep (se 1 (by rfl) ⟨26287646, by rfl⟩ : syracuseStep 35050195 = 52575293) B52575293
theorem B1135367 : Blo 503794 1135367 := bstep (se 1 (by rfl) ⟨851525, by rfl⟩ : syracuseStep 1135367 = 1703051) B1703051
theorem B3232831 : Blo 503794 3232831 := bstep (se 1 (by rfl) ⟨2424623, by rfl⟩ : syracuseStep 3232831 = 4849247) B4849247
theorem B3855437 : Blo 503794 3855437 := bstep (se 3 (by rfl) ⟨722894, by rfl⟩ : syracuseStep 3855437 = 1445789) B1445789
theorem B9884753 : Blo 503794 9884753 := bstep (se 2 (by rfl) ⟨3706782, by rfl⟩ : syracuseStep 9884753 = 7413565) B7413565
theorem B1725851 : Blo 503794 1725851 := bstep (se 1 (by rfl) ⟨1294388, by rfl⟩ : syracuseStep 1725851 = 2588777) B2588777
theorem B1136447 : Blo 503794 1136447 := bstep (se 1 (by rfl) ⟨852335, by rfl⟩ : syracuseStep 1136447 = 1704671) B1704671
theorem B3889079 : Blo 503794 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B808951 : Blo 503794 808951 := bstep (se 1 (by rfl) ⟨606713, by rfl⟩ : syracuseStep 808951 = 1213427) B1213427
theorem B1136735 : Blo 503794 1136735 := bstep (se 1 (by rfl) ⟨852551, by rfl⟩ : syracuseStep 1136735 = 1705103) B1705103
theorem B3692639 : Blo 503794 3692639 := bstep (se 1 (by rfl) ⟨2769479, by rfl⟩ : syracuseStep 3692639 = 5538959) B5538959
theorem B8214965 : Blo 503794 8214965 := bstep (se 5 (by rfl) ⟨385076, by rfl⟩ : syracuseStep 8214965 = 770153) B770153
theorem B1137491 : Blo 503794 1137491 := bstep (se 1 (by rfl) ⟨853118, by rfl⟩ : syracuseStep 1137491 = 1706237) B1706237
theorem B2153375 : Blo 503794 2153375 := bstep (se 1 (by rfl) ⟨1615031, by rfl⟩ : syracuseStep 2153375 = 3230063) B3230063
theorem B1367009 : Blo 503794 1367009 := bstep (se 2 (by rfl) ⟨512628, by rfl⟩ : syracuseStep 1367009 = 1025257) B1025257
theorem B908471 : Blo 503794 908471 := bstep (se 1 (by rfl) ⟨681353, by rfl⟩ : syracuseStep 908471 = 1362707) B1362707
theorem B1138031 : Blo 503794 1138031 := bstep (se 1 (by rfl) ⟨853523, by rfl⟩ : syracuseStep 1138031 = 1707047) B1707047
theorem B1138319 : Blo 503794 1138319 := bstep (se 1 (by rfl) ⟨853739, by rfl⟩ : syracuseStep 1138319 = 1707479) B1707479
theorem B1138409 : Blo 503794 1138409 := bstep (se 2 (by rfl) ⟨426903, by rfl⟩ : syracuseStep 1138409 = 853807) B853807
theorem B7364461 : Blo 503794 7364461 := bstep (se 3 (by rfl) ⟨1380836, by rfl⟩ : syracuseStep 7364461 = 2761673) B2761673
theorem B1728647 : Blo 503794 1728647 := bstep (se 1 (by rfl) ⟨1296485, by rfl⟩ : syracuseStep 1728647 = 2592971) B2592971
theorem B909775 : Blo 503794 909775 := bstep (se 1 (by rfl) ⟨682331, by rfl⟩ : syracuseStep 909775 = 1364663) B1364663
theorem B1139435 : Blo 503794 1139435 := bstep (se 1 (by rfl) ⟨854576, by rfl⟩ : syracuseStep 1139435 = 1709153) B1709153
theorem B3334931 : Blo 503794 3334931 := bstep (se 1 (by rfl) ⟨2501198, by rfl⟩ : syracuseStep 3334931 = 5002397) B5002397
theorem B27779993 : Blo 503794 27779993 := bstep (se 2 (by rfl) ⟨10417497, by rfl⟩ : syracuseStep 27779993 = 20834995) B20834995
theorem B812027 : Blo 503794 812027 := bstep (se 1 (by rfl) ⟨609020, by rfl⟩ : syracuseStep 812027 = 1218041) B1218041
theorem B1140335 : Blo 503794 1140335 := bstep (se 1 (by rfl) ⟨855251, by rfl⟩ : syracuseStep 1140335 = 1710503) B1710503
theorem B1140443 : Blo 503794 1140443 := bstep (se 1 (by rfl) ⟨855332, by rfl⟩ : syracuseStep 1140443 = 1710665) B1710665
theorem B1534187 : Blo 503794 1534187 := bstep (se 1 (by rfl) ⟨1150640, by rfl⟩ : syracuseStep 1534187 = 2301281) B2301281
theorem B911657 : Blo 503794 911657 := bstep (se 2 (by rfl) ⟨341871, by rfl⟩ : syracuseStep 911657 = 683743) B683743
theorem B813359 : Blo 503794 813359 := bstep (se 1 (by rfl) ⟨610019, by rfl⟩ : syracuseStep 813359 = 1220039) B1220039
theorem B1141559 : Blo 503794 1141559 := bstep (se 1 (by rfl) ⟨856169, by rfl⟩ : syracuseStep 1141559 = 1712339) B1712339
theorem B1141739 : Blo 503794 1141739 := bstep (se 1 (by rfl) ⟨856304, by rfl⟩ : syracuseStep 1141739 = 1712609) B1712609
theorem B2878685 : Blo 503794 2878685 := bstep (se 3 (by rfl) ⟨539753, by rfl⟩ : syracuseStep 2878685 = 1079507) B1079507
theorem B1535257 : Blo 503794 1535257 := bstep (se 2 (by rfl) ⟨575721, by rfl⟩ : syracuseStep 1535257 = 1151443) B1151443
theorem B21884579 : Blo 503794 21884579 := bstep (se 1 (by rfl) ⟨16413434, by rfl⟩ : syracuseStep 21884579 = 32826869) B32826869
theorem B7270181 : Blo 503794 7270181 := bstep (se 4 (by rfl) ⟨681579, by rfl⟩ : syracuseStep 7270181 = 1363159) B1363159
theorem B1372025 : Blo 503794 1372025 := bstep (se 2 (by rfl) ⟨514509, by rfl⟩ : syracuseStep 1372025 = 1029019) B1029019
theorem B6943247 : Blo 503794 6943247 := bstep (se 1 (by rfl) ⟨5207435, by rfl⟩ : syracuseStep 6943247 = 10414871) B10414871
theorem B1700513 : Blo 503794 1700513 := bstep (se 2 (by rfl) ⟨637692, by rfl⟩ : syracuseStep 1700513 = 1275385) B1275385
theorem B718031 : Blo 503794 718031 := bstep (se 1 (by rfl) ⟨538523, by rfl⟩ : syracuseStep 718031 = 1077047) B1077047
theorem B1701377 : Blo 503794 1701377 := bstep (se 2 (by rfl) ⟨638016, by rfl⟩ : syracuseStep 1701377 = 1276033) B1276033
theorem B1439707 : Blo 503794 1439707 := bstep (se 1 (by rfl) ⟨1079780, by rfl⟩ : syracuseStep 1439707 = 2159561) B2159561
theorem B1701863 : Blo 503794 1701863 := bstep (se 1 (by rfl) ⟨1276397, by rfl⟩ : syracuseStep 1701863 = 2552795) B2552795
theorem B1701971 : Blo 503794 1701971 := bstep (se 1 (by rfl) ⟨1276478, by rfl⟩ : syracuseStep 1701971 = 2552957) B2552957
theorem B1702187 : Blo 503794 1702187 := bstep (se 1 (by rfl) ⟨1276640, by rfl⟩ : syracuseStep 1702187 = 2553281) B2553281
theorem B850223 : Blo 503794 850223 := bstep (se 1 (by rfl) ⟨637667, by rfl⟩ : syracuseStep 850223 = 1275335) B1275335
theorem B719227 : Blo 503794 719227 := bstep (se 1 (by rfl) ⟨539420, by rfl⟩ : syracuseStep 719227 = 1078841) B1078841
theorem B850459 : Blo 503794 850459 := bstep (se 1 (by rfl) ⟨637844, by rfl⟩ : syracuseStep 850459 = 1275689) B1275689
theorem B1702457 : Blo 503794 1702457 := bstep (se 2 (by rfl) ⟨638421, by rfl⟩ : syracuseStep 1702457 = 1276843) B1276843
theorem B1440413 : Blo 503794 1440413 := bstep (se 3 (by rfl) ⟨270077, by rfl⟩ : syracuseStep 1440413 = 540155) B540155
theorem B1440595 : Blo 503794 1440595 := bstep (se 1 (by rfl) ⟨1080446, by rfl⟩ : syracuseStep 1440595 = 2160893) B2160893
theorem B2555063 : Blo 503794 2555063 := bstep (se 1 (by rfl) ⟨1916297, by rfl⟩ : syracuseStep 2555063 = 3832595) B3832595
theorem B1440983 : Blo 503794 1440983 := bstep (se 1 (by rfl) ⟨1080737, by rfl⟩ : syracuseStep 1440983 = 2161475) B2161475
theorem B851431 : Blo 503794 851431 := bstep (se 1 (by rfl) ⟨638573, by rfl⟩ : syracuseStep 851431 = 1277147) B1277147
theorem B851519 : Blo 503794 851519 := bstep (se 1 (by rfl) ⟨638639, by rfl⟩ : syracuseStep 851519 = 1277279) B1277279
theorem B7274099 : Blo 503794 7274099 := bstep (se 1 (by rfl) ⟨5455574, by rfl⟩ : syracuseStep 7274099 = 10911149) B10911149
theorem B5472011 : Blo 503794 5472011 := bstep (se 1 (by rfl) ⟨4104008, by rfl⟩ : syracuseStep 5472011 = 8208017) B8208017
theorem B1081259 : Blo 503794 1081259 := bstep (se 1 (by rfl) ⟨810944, by rfl⟩ : syracuseStep 1081259 = 1621889) B1621889
theorem B1278139 : Blo 503794 1278139 := bstep (se 1 (by rfl) ⟨958604, by rfl⟩ : syracuseStep 1278139 = 1917209) B1917209
theorem B2162875 : Blo 503794 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B1704239 : Blo 503794 1704239 := bstep (se 1 (by rfl) ⟨1278179, by rfl⟩ : syracuseStep 1704239 = 2556359) B2556359
theorem B852511 : Blo 503794 852511 := bstep (se 1 (by rfl) ⟨639383, by rfl⟩ : syracuseStep 852511 = 1278767) B1278767
theorem B2556521 : Blo 503794 2556521 := bstep (se 2 (by rfl) ⟨958695, by rfl⟩ : syracuseStep 2556521 = 1917391) B1917391
theorem B1278575 : Blo 503794 1278575 := bstep (se 1 (by rfl) ⟨958931, by rfl⟩ : syracuseStep 1278575 = 1917863) B1917863
theorem B2556845 : Blo 503794 2556845 := bstep (se 3 (by rfl) ⟨479408, by rfl⟩ : syracuseStep 2556845 = 958817) B958817
theorem B1311967 : Blo 503794 1311967 := bstep (se 1 (by rfl) ⟨983975, by rfl⟩ : syracuseStep 1311967 = 1967951) B1967951
theorem B2163935 : Blo 503794 2163935 := bstep (se 1 (by rfl) ⟨1622951, by rfl⟩ : syracuseStep 2163935 = 3245903) B3245903
theorem B722143 : Blo 503794 722143 := bstep (se 1 (by rfl) ⟨541607, by rfl⟩ : syracuseStep 722143 = 1083215) B1083215
theorem B853679 : Blo 503794 853679 := bstep (se 1 (by rfl) ⟨640259, by rfl⟩ : syracuseStep 853679 = 1280519) B1280519
theorem B1705967 : Blo 503794 1705967 := bstep (se 1 (by rfl) ⟨1279475, by rfl⟩ : syracuseStep 1705967 = 2558951) B2558951
theorem B1443865 : Blo 503794 1443865 := bstep (se 2 (by rfl) ⟨541449, by rfl⟩ : syracuseStep 1443865 = 1082899) B1082899
theorem B854239 : Blo 503794 854239 := bstep (se 1 (by rfl) ⟨640679, by rfl⟩ : syracuseStep 854239 = 1281359) B1281359
theorem B756047 : Blo 503794 756047 := bstep (se 1 (by rfl) ⟨567035, by rfl⟩ : syracuseStep 756047 = 1134071) B1134071
theorem B1083727 : Blo 503794 1083727 := bstep (se 1 (by rfl) ⟨812795, by rfl⟩ : syracuseStep 1083727 = 1625591) B1625591
theorem B3639647 : Blo 503794 3639647 := bstep (se 1 (by rfl) ⟨2729735, by rfl⟩ : syracuseStep 3639647 = 5459471) B5459471
theorem B756095 : Blo 503794 756095 := bstep (se 1 (by rfl) ⟨567071, by rfl⟩ : syracuseStep 756095 = 1134143) B1134143
theorem B4852133 : Blo 503794 4852133 := bstep (se 4 (by rfl) ⟨454887, by rfl⟩ : syracuseStep 4852133 = 909775) B909775
theorem B756137 : Blo 503794 756137 := bstep (se 2 (by rfl) ⟨283551, by rfl⟩ : syracuseStep 756137 = 567103) B567103
theorem B2558465 : Blo 503794 2558465 := bstep (se 2 (by rfl) ⟨959424, by rfl⟩ : syracuseStep 2558465 = 1918849) B1918849
theorem B4327937 : Blo 503794 4327937 := bstep (se 2 (by rfl) ⟨1622976, by rfl⟩ : syracuseStep 4327937 = 3245953) B3245953
theorem B756521 : Blo 503794 756521 := bstep (se 2 (by rfl) ⟨283695, by rfl⟩ : syracuseStep 756521 = 567391) B567391
theorem B756731 : Blo 503794 756731 := bstep (se 1 (by rfl) ⟨567548, by rfl⟩ : syracuseStep 756731 = 1135097) B1135097
theorem B756791 : Blo 503794 756791 := bstep (se 1 (by rfl) ⟨567593, by rfl⟩ : syracuseStep 756791 = 1135187) B1135187
theorem B855103 : Blo 503794 855103 := bstep (se 1 (by rfl) ⟨641327, by rfl⟩ : syracuseStep 855103 = 1282655) B1282655
theorem B756911 : Blo 503794 756911 := bstep (se 1 (by rfl) ⟨567683, by rfl⟩ : syracuseStep 756911 = 1135367) B1135367
theorem B2559275 : Blo 503794 2559275 := bstep (se 1 (by rfl) ⟨1919456, by rfl⟩ : syracuseStep 2559275 = 3838913) B3838913
theorem B6589835 : Blo 503794 6589835 := bstep (se 1 (by rfl) ⟨4942376, by rfl⟩ : syracuseStep 6589835 = 9884753) B9884753
theorem B1150567 : Blo 503794 1150567 := bstep (se 1 (by rfl) ⟨862925, by rfl⟩ : syracuseStep 1150567 = 1725851) B1725851
theorem B757631 : Blo 503794 757631 := bstep (se 1 (by rfl) ⟨568223, by rfl⟩ : syracuseStep 757631 = 1136447) B1136447
theorem B2592719 : Blo 503794 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B14749739 : Blo 503794 14749739 := bstep (se 1 (by rfl) ⟨11062304, by rfl⟩ : syracuseStep 14749739 = 22124609) B22124609
theorem B757823 : Blo 503794 757823 := bstep (se 1 (by rfl) ⟨568367, by rfl⟩ : syracuseStep 757823 = 1136735) B1136735
theorem B2461759 : Blo 503794 2461759 := bstep (se 1 (by rfl) ⟨1846319, by rfl⟩ : syracuseStep 2461759 = 3692639) B3692639
theorem B5476643 : Blo 503794 5476643 := bstep (se 1 (by rfl) ⟨4107482, by rfl⟩ : syracuseStep 5476643 = 8214965) B8214965
theorem B758057 : Blo 503794 758057 := bstep (se 2 (by rfl) ⟨284271, by rfl⟩ : syracuseStep 758057 = 568543) B568543
theorem B758327 : Blo 503794 758327 := bstep (se 1 (by rfl) ⟨568745, by rfl⟩ : syracuseStep 758327 = 1137491) B1137491
theorem B1708883 : Blo 503794 1708883 := bstep (se 1 (by rfl) ⟨1281662, by rfl⟩ : syracuseStep 1708883 = 2563325) B2563325
theorem B758687 : Blo 503794 758687 := bstep (se 1 (by rfl) ⟨569015, by rfl⟩ : syracuseStep 758687 = 1138031) B1138031
theorem B4920323 : Blo 503794 4920323 := bstep (se 1 (by rfl) ⟨3690242, by rfl⟩ : syracuseStep 4920323 = 7380485) B7380485
theorem B758879 : Blo 503794 758879 := bstep (se 1 (by rfl) ⟨569159, by rfl⟩ : syracuseStep 758879 = 1138319) B1138319
theorem B758939 : Blo 503794 758939 := bstep (se 1 (by rfl) ⟨569204, by rfl⟩ : syracuseStep 758939 = 1138409) B1138409
theorem B8656145 : Blo 503794 8656145 := bstep (se 2 (by rfl) ⟨3246054, by rfl⟩ : syracuseStep 8656145 = 6492109) B6492109
theorem B1709423 : Blo 503794 1709423 := bstep (se 1 (by rfl) ⟨1282067, by rfl⟩ : syracuseStep 1709423 = 2564135) B2564135
theorem B1152431 : Blo 503794 1152431 := bstep (se 1 (by rfl) ⟨864323, by rfl⟩ : syracuseStep 1152431 = 1728647) B1728647
theorem B759623 : Blo 503794 759623 := bstep (se 1 (by rfl) ⟨569717, by rfl⟩ : syracuseStep 759623 = 1139435) B1139435
theorem B18519995 : Blo 503794 18519995 := bstep (se 1 (by rfl) ⟨13889996, by rfl⟩ : syracuseStep 18519995 = 27779993) B27779993
theorem B1710071 : Blo 503794 1710071 := bstep (se 1 (by rfl) ⟨1282553, by rfl⟩ : syracuseStep 1710071 = 2565107) B2565107
theorem B2168957 : Blo 503794 2168957 := bstep (se 3 (by rfl) ⟨406679, by rfl⟩ : syracuseStep 2168957 = 813359) B813359
theorem B46733593 : Blo 503794 46733593 := bstep (se 2 (by rfl) ⟨17525097, by rfl⟩ : syracuseStep 46733593 = 35050195) B35050195
theorem B760223 : Blo 503794 760223 := bstep (se 1 (by rfl) ⟨570167, by rfl⟩ : syracuseStep 760223 = 1140335) B1140335
theorem B760295 : Blo 503794 760295 := bstep (se 1 (by rfl) ⟨570221, by rfl⟩ : syracuseStep 760295 = 1140443) B1140443
theorem B4332311 : Blo 503794 4332311 := bstep (se 1 (by rfl) ⟨3249233, by rfl⟩ : syracuseStep 4332311 = 6498467) B6498467
theorem B1022791 : Blo 503794 1022791 := bstep (se 1 (by rfl) ⟨767093, by rfl⟩ : syracuseStep 1022791 = 1534187) B1534187
theorem B1711151 : Blo 503794 1711151 := bstep (se 1 (by rfl) ⟨1283363, by rfl⟩ : syracuseStep 1711151 = 2566727) B2566727
theorem B4332689 : Blo 503794 4332689 := bstep (se 2 (by rfl) ⟨1624758, by rfl⟩ : syracuseStep 4332689 = 3249517) B3249517
theorem B761039 : Blo 503794 761039 := bstep (se 1 (by rfl) ⟨570779, by rfl⟩ : syracuseStep 761039 = 1141559) B1141559
theorem B7413059 : Blo 503794 7413059 := bstep (se 1 (by rfl) ⟨5559794, by rfl⟩ : syracuseStep 7413059 = 11119589) B11119589
theorem B761159 : Blo 503794 761159 := bstep (se 1 (by rfl) ⟨570869, by rfl⟩ : syracuseStep 761159 = 1141739) B1141739
theorem B761321 : Blo 503794 761321 := bstep (se 2 (by rfl) ⟨285495, by rfl⟩ : syracuseStep 761321 = 570991) B570991
theorem B761465 : Blo 503794 761465 := bstep (se 2 (by rfl) ⟨285549, by rfl⟩ : syracuseStep 761465 = 571099) B571099
theorem B14589719 : Blo 503794 14589719 := bstep (se 1 (by rfl) ⟨10942289, by rfl⟩ : syracuseStep 14589719 = 21884579) B21884579
theorem B1712393 : Blo 503794 1712393 := bstep (se 2 (by rfl) ⟨642147, by rfl⟩ : syracuseStep 1712393 = 1284295) B1284295
theorem B4628831 : Blo 503794 4628831 := bstep (se 1 (by rfl) ⟨3471623, by rfl⟩ : syracuseStep 4628831 = 6943247) B6943247
theorem B958969 : Blo 503794 958969 := bstep (se 2 (by rfl) ⟨359613, by rfl⟩ : syracuseStep 958969 = 719227) B719227
theorem B9708335 : Blo 503794 9708335 := bstep (se 1 (by rfl) ⟨7281251, by rfl⟩ : syracuseStep 9708335 = 14562503) B14562503
theorem B566815 : Blo 503794 566815 := bstep (se 1 (by rfl) ⟨425111, by rfl⟩ : syracuseStep 566815 = 850223) B850223
theorem B960275 : Blo 503794 960275 := bstep (se 1 (by rfl) ⟨720206, by rfl⟩ : syracuseStep 960275 = 1440413) B1440413
theorem B31205209 : Blo 503794 31205209 := bstep (se 2 (by rfl) ⟨11701953, by rfl⟩ : syracuseStep 31205209 = 23403907) B23403907
theorem B960655 : Blo 503794 960655 := bstep (se 1 (by rfl) ⟨720491, by rfl⟩ : syracuseStep 960655 = 1440983) B1440983
theorem B567679 : Blo 503794 567679 := bstep (se 1 (by rfl) ⟨425759, by rfl⟩ : syracuseStep 567679 = 851519) B851519
theorem B8202707 : Blo 503794 8202707 := bstep (se 1 (by rfl) ⟨6152030, by rfl⟩ : syracuseStep 8202707 = 12304061) B12304061
theorem B3648007 : Blo 503794 3648007 := bstep (se 1 (by rfl) ⟨2736005, by rfl⟩ : syracuseStep 3648007 = 5472011) B5472011
theorem B7023779 : Blo 503794 7023779 := bstep (se 1 (by rfl) ⟨5267834, by rfl⟩ : syracuseStep 7023779 = 10535669) B10535669
theorem B1944911 : Blo 503794 1944911 := bstep (se 1 (by rfl) ⟨1458683, by rfl⟩ : syracuseStep 1944911 = 2917367) B2917367
theorem B2043575 : Blo 503794 2043575 := bstep (se 1 (by rfl) ⟨1532681, by rfl⟩ : syracuseStep 2043575 = 3065363) B3065363
theorem B8793787 : Blo 503794 8793787 := bstep (se 1 (by rfl) ⟨6595340, by rfl⟩ : syracuseStep 8793787 = 13190681) B13190681
theorem B962273 : Blo 503794 962273 := bstep (se 2 (by rfl) ⟨360852, by rfl⟩ : syracuseStep 962273 = 721705) B721705
theorem B569083 : Blo 503794 569083 := bstep (se 1 (by rfl) ⟨426812, by rfl⟩ : syracuseStep 569083 = 853625) B853625
theorem B3518333 : Blo 503794 3518333 := bstep (se 3 (by rfl) ⟨659687, by rfl⟩ : syracuseStep 3518333 = 1319375) B1319375
theorem B503803 : Blo 503794 503803 := bstep (se 1 (by rfl) ⟨377852, by rfl⟩ : syracuseStep 503803 = 755705) B755705
theorem B503871 : Blo 503794 503871 := bstep (se 1 (by rfl) ⟨377903, by rfl⟩ : syracuseStep 503871 = 755807) B755807
theorem B569407 : Blo 503794 569407 := bstep (se 1 (by rfl) ⟨427055, by rfl⟩ : syracuseStep 569407 = 854111) B854111
theorem B503911 : Blo 503794 503911 := bstep (se 1 (by rfl) ⟨377933, by rfl⟩ : syracuseStep 503911 = 755867) B755867
theorem B503935 : Blo 503794 503935 := bstep (se 1 (by rfl) ⟨377951, by rfl⟩ : syracuseStep 503935 = 755903) B755903
theorem B4599935 : Blo 503794 4599935 := bstep (se 1 (by rfl) ⟨3449951, by rfl⟩ : syracuseStep 4599935 = 6899903) B6899903
theorem B503963 : Blo 503794 503963 := bstep (se 1 (by rfl) ⟨377972, by rfl⟩ : syracuseStep 503963 = 755945) B755945
theorem B4108519 : Blo 503794 4108519 := bstep (se 1 (by rfl) ⟨3081389, by rfl⟩ : syracuseStep 4108519 = 6162779) B6162779
theorem B1028371 : Blo 503794 1028371 := bstep (se 1 (by rfl) ⟨771278, by rfl⟩ : syracuseStep 1028371 = 1542557) B1542557
theorem B504167 : Blo 503794 504167 := bstep (se 1 (by rfl) ⟨378125, by rfl⟩ : syracuseStep 504167 = 756251) B756251
theorem B504219 : Blo 503794 504219 := bstep (se 1 (by rfl) ⟨378164, by rfl⟩ : syracuseStep 504219 = 756329) B756329
theorem B16396829 : Blo 503794 16396829 := bstep (se 3 (by rfl) ⟨3074405, by rfl⟩ : syracuseStep 16396829 = 6148811) B6148811
theorem B8172089 : Blo 503794 8172089 := bstep (se 2 (by rfl) ⟨3064533, by rfl⟩ : syracuseStep 8172089 = 6129067) B6129067
theorem B504571 : Blo 503794 504571 := bstep (se 1 (by rfl) ⟨378428, by rfl⟩ : syracuseStep 504571 = 756857) B756857
theorem B504639 : Blo 503794 504639 := bstep (se 1 (by rfl) ⟨378479, by rfl⟩ : syracuseStep 504639 = 756959) B756959
theorem B504667 : Blo 503794 504667 := bstep (se 1 (by rfl) ⟨378500, by rfl⟩ : syracuseStep 504667 = 757001) B757001
theorem B1618825 : Blo 503794 1618825 := bstep (se 2 (by rfl) ⟨607059, by rfl⟩ : syracuseStep 1618825 = 1214119) B1214119
theorem B504735 : Blo 503794 504735 := bstep (se 1 (by rfl) ⟨378551, by rfl⟩ : syracuseStep 504735 = 757103) B757103
theorem B570271 : Blo 503794 570271 := bstep (se 1 (by rfl) ⟨427703, by rfl⟩ : syracuseStep 570271 = 855407) B855407
theorem B1913807 : Blo 503794 1913807 := bstep (se 1 (by rfl) ⟨1435355, by rfl⟩ : syracuseStep 1913807 = 2870711) B2870711
theorem B504815 : Blo 503794 504815 := bstep (se 1 (by rfl) ⟨378611, by rfl⟩ : syracuseStep 504815 = 757223) B757223
theorem B504903 : Blo 503794 504903 := bstep (se 1 (by rfl) ⟨378677, by rfl⟩ : syracuseStep 504903 = 757355) B757355
theorem B1848425 : Blo 503794 1848425 := bstep (se 2 (by rfl) ⟨693159, by rfl⟩ : syracuseStep 1848425 = 1386319) B1386319
theorem B504987 : Blo 503794 504987 := bstep (se 1 (by rfl) ⟨378740, by rfl⟩ : syracuseStep 504987 = 757481) B757481
theorem B570523 : Blo 503794 570523 := bstep (se 1 (by rfl) ⟨427892, by rfl⟩ : syracuseStep 570523 = 855785) B855785
theorem B2045179 : Blo 503794 2045179 := bstep (se 1 (by rfl) ⟨1533884, by rfl⟩ : syracuseStep 2045179 = 3067769) B3067769
theorem B505083 : Blo 503794 505083 := bstep (se 1 (by rfl) ⟨378812, by rfl⟩ : syracuseStep 505083 = 757625) B757625
theorem B505151 : Blo 503794 505151 := bstep (se 1 (by rfl) ⟨378863, by rfl⟩ : syracuseStep 505151 = 757727) B757727
theorem B505319 : Blo 503794 505319 := bstep (se 1 (by rfl) ⟨378989, by rfl⟩ : syracuseStep 505319 = 757979) B757979
theorem B505327 : Blo 503794 505327 := bstep (se 1 (by rfl) ⟨378995, by rfl⟩ : syracuseStep 505327 = 757991) B757991
theorem B505435 : Blo 503794 505435 := bstep (se 1 (by rfl) ⟨379076, by rfl⟩ : syracuseStep 505435 = 758153) B758153
theorem B32683621 : Blo 503794 32683621 := bstep (se 4 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 32683621 = 6128179) B6128179
theorem B505499 : Blo 503794 505499 := bstep (se 1 (by rfl) ⟨379124, by rfl⟩ : syracuseStep 505499 = 758249) B758249
theorem B505583 : Blo 503794 505583 := bstep (se 1 (by rfl) ⟨379187, by rfl⟩ : syracuseStep 505583 = 758375) B758375
theorem B2569967 : Blo 503794 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B19642175 : Blo 503794 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B505671 : Blo 503794 505671 := bstep (se 1 (by rfl) ⟨379253, by rfl⟩ : syracuseStep 505671 = 758507) B758507
theorem B571207 : Blo 503794 571207 := bstep (se 1 (by rfl) ⟨428405, by rfl⟩ : syracuseStep 571207 = 856811) B856811
theorem B505691 : Blo 503794 505691 := bstep (se 1 (by rfl) ⟨379268, by rfl⟩ : syracuseStep 505691 = 758537) B758537
theorem B1914749 : Blo 503794 1914749 := bstep (se 3 (by rfl) ⟨359015, by rfl⟩ : syracuseStep 1914749 = 718031) B718031
theorem B505759 : Blo 503794 505759 := bstep (se 1 (by rfl) ⟨379319, by rfl⟩ : syracuseStep 505759 = 758639) B758639
theorem B2570291 : Blo 503794 2570291 := bstep (se 1 (by rfl) ⟨1927718, by rfl⟩ : syracuseStep 2570291 = 3855437) B3855437
theorem B505927 : Blo 503794 505927 := bstep (se 1 (by rfl) ⟨379445, by rfl⟩ : syracuseStep 505927 = 758891) B758891
theorem B1620107 : Blo 503794 1620107 := bstep (se 1 (by rfl) ⟨1215080, by rfl⟩ : syracuseStep 1620107 = 2430161) B2430161
theorem B506087 : Blo 503794 506087 := bstep (se 1 (by rfl) ⟨379565, by rfl⟩ : syracuseStep 506087 = 759131) B759131
theorem B506271 : Blo 503794 506271 := bstep (se 1 (by rfl) ⟨379703, by rfl⟩ : syracuseStep 506271 = 759407) B759407
theorem B506319 : Blo 503794 506319 := bstep (se 1 (by rfl) ⟨379739, by rfl⟩ : syracuseStep 506319 = 759479) B759479
theorem B506343 : Blo 503794 506343 := bstep (se 1 (by rfl) ⟨379757, by rfl⟩ : syracuseStep 506343 = 759515) B759515
theorem B506459 : Blo 503794 506459 := bstep (se 1 (by rfl) ⟨379844, by rfl⟩ : syracuseStep 506459 = 759689) B759689
theorem B506527 : Blo 503794 506527 := bstep (se 1 (by rfl) ⟨379895, by rfl⟩ : syracuseStep 506527 = 759791) B759791
theorem B506695 : Blo 503794 506695 := bstep (se 1 (by rfl) ⟨380021, by rfl⟩ : syracuseStep 506695 = 760043) B760043
theorem B506735 : Blo 503794 506735 := bstep (se 1 (by rfl) ⟨380051, by rfl⟩ : syracuseStep 506735 = 760103) B760103
theorem B506791 : Blo 503794 506791 := bstep (se 1 (by rfl) ⟨380093, by rfl⟩ : syracuseStep 506791 = 760187) B760187
theorem B506971 : Blo 503794 506971 := bstep (se 1 (by rfl) ⟨380228, by rfl⟩ : syracuseStep 506971 = 760457) B760457
theorem B507087 : Blo 503794 507087 := bstep (se 1 (by rfl) ⟨380315, by rfl⟩ : syracuseStep 507087 = 760631) B760631
theorem B2604257 : Blo 503794 2604257 := bstep (se 2 (by rfl) ⟨976596, by rfl⟩ : syracuseStep 2604257 = 1953193) B1953193
theorem B507111 : Blo 503794 507111 := bstep (se 1 (by rfl) ⟨380333, by rfl⟩ : syracuseStep 507111 = 760667) B760667
theorem B1621235 : Blo 503794 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B507207 : Blo 503794 507207 := bstep (se 1 (by rfl) ⟨380405, by rfl⟩ : syracuseStep 507207 = 760811) B760811
theorem B605647 : Blo 503794 605647 := bstep (se 1 (by rfl) ⟨454235, by rfl⟩ : syracuseStep 605647 = 908471) B908471
theorem B507343 : Blo 503794 507343 := bstep (se 1 (by rfl) ⟨380507, by rfl⟩ : syracuseStep 507343 = 761015) B761015
theorem B507503 : Blo 503794 507503 := bstep (se 1 (by rfl) ⟨380627, by rfl⟩ : syracuseStep 507503 = 761255) B761255
theorem B507559 : Blo 503794 507559 := bstep (se 1 (by rfl) ⟨380669, by rfl⟩ : syracuseStep 507559 = 761339) B761339
theorem B638695 : Blo 503794 638695 := bstep (se 1 (by rfl) ⟨479021, by rfl⟩ : syracuseStep 638695 = 958043) B958043
theorem B507623 : Blo 503794 507623 := bstep (se 1 (by rfl) ⟨380717, by rfl⟩ : syracuseStep 507623 = 761435) B761435
theorem B507679 : Blo 503794 507679 := bstep (se 1 (by rfl) ⟨380759, by rfl⟩ : syracuseStep 507679 = 761519) B761519
theorem B507759 : Blo 503794 507759 := bstep (se 1 (by rfl) ⟨380819, by rfl⟩ : syracuseStep 507759 = 761639) B761639
theorem B3850577 : Blo 503794 3850577 := bstep (se 2 (by rfl) ⟨1443966, by rfl⟩ : syracuseStep 3850577 = 2887933) B2887933
theorem B541351 : Blo 503794 541351 := bstep (se 1 (by rfl) ⟨406013, by rfl⟩ : syracuseStep 541351 = 812027) B812027
theorem B2081555 : Blo 503794 2081555 := bstep (se 1 (by rfl) ⟨1561166, by rfl⟩ : syracuseStep 2081555 = 3122333) B3122333
theorem B1295129 : Blo 503794 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B3654467 : Blo 503794 3654467 := bstep (se 1 (by rfl) ⟨2740850, by rfl⟩ : syracuseStep 3654467 = 5481701) B5481701
theorem B3064655 : Blo 503794 3064655 := bstep (se 1 (by rfl) ⟨2298491, by rfl⟩ : syracuseStep 3064655 = 4596983) B4596983
theorem B4310441 : Blo 503794 4310441 := bstep (se 2 (by rfl) ⟨1616415, by rfl⟩ : syracuseStep 4310441 = 3232831) B3232831
theorem B607771 : Blo 503794 607771 := bstep (se 1 (by rfl) ⟨455828, by rfl⟩ : syracuseStep 607771 = 911657) B911657
theorem B640543 : Blo 503794 640543 := bstep (se 1 (by rfl) ⟨480407, by rfl⟩ : syracuseStep 640543 = 960815) B960815
theorem B1919123 : Blo 503794 1919123 := bstep (se 1 (by rfl) ⟨1439342, by rfl⟩ : syracuseStep 1919123 = 2878685) B2878685
theorem B1919609 : Blo 503794 1919609 := bstep (se 2 (by rfl) ⟨719853, by rfl⟩ : syracuseStep 1919609 = 1439707) B1439707
theorem B11717399 : Blo 503794 11717399 := bstep (se 1 (by rfl) ⟨8788049, by rfl⟩ : syracuseStep 11717399 = 17576099) B17576099
theorem B1624873 : Blo 503794 1624873 := bstep (se 2 (by rfl) ⟨609327, by rfl⟩ : syracuseStep 1624873 = 1218655) B1218655
theorem B969563 : Blo 503794 969563 := bstep (se 1 (by rfl) ⟨727172, by rfl⟩ : syracuseStep 969563 = 1454345) B1454345
theorem B2739035 : Blo 503794 2739035 := bstep (se 1 (by rfl) ⟨2054276, by rfl⟩ : syracuseStep 2739035 = 4108553) B4108553
theorem B14568497 : Blo 503794 14568497 := bstep (se 2 (by rfl) ⟨5463186, by rfl⟩ : syracuseStep 14568497 = 10926373) B10926373
theorem B1133675 : Blo 503794 1133675 := bstep (se 1 (by rfl) ⟨850256, by rfl⟩ : syracuseStep 1133675 = 1700513) B1700513
theorem B1133945 : Blo 503794 1133945 := bstep (se 2 (by rfl) ⟨425229, by rfl⟩ : syracuseStep 1133945 = 850459) B850459
theorem B642431 : Blo 503794 642431 := bstep (se 1 (by rfl) ⟨481823, by rfl⟩ : syracuseStep 642431 = 963647) B963647
theorem B1134251 : Blo 503794 1134251 := bstep (se 1 (by rfl) ⟨850688, by rfl⟩ : syracuseStep 1134251 = 1701377) B1701377
theorem B1920793 : Blo 503794 1920793 := bstep (se 2 (by rfl) ⟨720297, by rfl⟩ : syracuseStep 1920793 = 1440595) B1440595
theorem B1822591 : Blo 503794 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B1134575 : Blo 503794 1134575 := bstep (se 1 (by rfl) ⟨850931, by rfl⟩ : syracuseStep 1134575 = 1701863) B1701863
theorem B1134647 : Blo 503794 1134647 := bstep (se 1 (by rfl) ⟨850985, by rfl⟩ : syracuseStep 1134647 = 1701971) B1701971
theorem B1134791 : Blo 503794 1134791 := bstep (se 1 (by rfl) ⟨851093, by rfl⟩ : syracuseStep 1134791 = 1702187) B1702187
theorem B3952849 : Blo 503794 3952849 := bstep (se 2 (by rfl) ⟨1482318, by rfl⟩ : syracuseStep 3952849 = 2964637) B2964637
theorem B1134971 : Blo 503794 1134971 := bstep (se 1 (by rfl) ⟨851228, by rfl⟩ : syracuseStep 1134971 = 1702457) B1702457
theorem B1135241 : Blo 503794 1135241 := bstep (se 2 (by rfl) ⟨425715, by rfl⟩ : syracuseStep 1135241 = 851431) B851431
theorem B3658733 : Blo 503794 3658733 := bstep (se 3 (by rfl) ⟨686012, by rfl⟩ : syracuseStep 3658733 = 1372025) B1372025
theorem B9819281 : Blo 503794 9819281 := bstep (se 2 (by rfl) ⟨3682230, by rfl⟩ : syracuseStep 9819281 = 7364461) B7364461
theorem B1135979 : Blo 503794 1135979 := bstep (se 1 (by rfl) ⟨851984, by rfl⟩ : syracuseStep 1135979 = 1703969) B1703969
theorem B19486169 : Blo 503794 19486169 := bstep (se 2 (by rfl) ⟨7307313, by rfl⟩ : syracuseStep 19486169 = 14614627) B14614627
theorem B1136249 : Blo 503794 1136249 := bstep (se 2 (by rfl) ⟨426093, by rfl⟩ : syracuseStep 1136249 = 852187) B852187
theorem B1464155 : Blo 503794 1464155 := bstep (se 1 (by rfl) ⟨1098116, by rfl⟩ : syracuseStep 1464155 = 2196233) B2196233
theorem B1136609 : Blo 503794 1136609 := bstep (se 2 (by rfl) ⟨426228, by rfl⟩ : syracuseStep 1136609 = 852457) B852457
theorem B1923041 : Blo 503794 1923041 := bstep (se 2 (by rfl) ⟨721140, by rfl⟩ : syracuseStep 1923041 = 1442281) B1442281
theorem B8181749 : Blo 503794 8181749 := bstep (se 5 (by rfl) ⟨383519, by rfl⟩ : syracuseStep 8181749 = 767039) B767039
theorem B2152487 : Blo 503794 2152487 := bstep (se 1 (by rfl) ⟨1614365, by rfl⟩ : syracuseStep 2152487 = 3228731) B3228731
theorem B1169447 : Blo 503794 1169447 := bstep (se 1 (by rfl) ⟨877085, by rfl⟩ : syracuseStep 1169447 = 1754171) B1754171
theorem B6150323 : Blo 503794 6150323 := bstep (se 1 (by rfl) ⟨4612742, by rfl⟩ : syracuseStep 6150323 = 9225485) B9225485
theorem B4872545 : Blo 503794 4872545 := bstep (se 2 (by rfl) ⟨1827204, by rfl⟩ : syracuseStep 4872545 = 3654409) B3654409
theorem B1825591 : Blo 503794 1825591 := bstep (se 1 (by rfl) ⟨1369193, by rfl⟩ : syracuseStep 1825591 = 2738387) B2738387
theorem B4218493 : Blo 503794 4218493 := bstep (se 3 (by rfl) ⟨790967, by rfl⟩ : syracuseStep 4218493 = 1581935) B1581935
theorem B4874003 : Blo 503794 4874003 := bstep (se 1 (by rfl) ⟨3655502, by rfl⟩ : syracuseStep 4874003 = 7311005) B7311005
theorem B1138463 : Blo 503794 1138463 := bstep (se 1 (by rfl) ⟨853847, by rfl⟩ : syracuseStep 1138463 = 1707695) B1707695
theorem B1138679 : Blo 503794 1138679 := bstep (se 1 (by rfl) ⟨854009, by rfl⟩ : syracuseStep 1138679 = 1708019) B1708019
theorem B1138895 : Blo 503794 1138895 := bstep (se 1 (by rfl) ⟨854171, by rfl⟩ : syracuseStep 1138895 = 1708343) B1708343
theorem B1139039 : Blo 503794 1139039 := bstep (se 1 (by rfl) ⟨854279, by rfl⟩ : syracuseStep 1139039 = 1708559) B1708559
theorem B1139759 : Blo 503794 1139759 := bstep (se 1 (by rfl) ⟨854819, by rfl⟩ : syracuseStep 1139759 = 1709639) B1709639
theorem B3827249 : Blo 503794 3827249 := bstep (se 2 (by rfl) ⟨1435218, by rfl⟩ : syracuseStep 3827249 = 2870437) B2870437
theorem B1140407 : Blo 503794 1140407 := bstep (se 1 (by rfl) ⟨855305, by rfl⟩ : syracuseStep 1140407 = 1710611) B1710611
theorem B9758393 : Blo 503794 9758393 := bstep (se 2 (by rfl) ⟨3659397, by rfl⟩ : syracuseStep 9758393 = 7318795) B7318795
theorem B1435583 : Blo 503794 1435583 := bstep (se 1 (by rfl) ⟨1076687, by rfl⟩ : syracuseStep 1435583 = 2153375) B2153375
theorem B1927111 : Blo 503794 1927111 := bstep (se 1 (by rfl) ⟨1445333, by rfl⟩ : syracuseStep 1927111 = 2890667) B2890667
theorem B911339 : Blo 503794 911339 := bstep (se 1 (by rfl) ⟨683504, by rfl⟩ : syracuseStep 911339 = 1367009) B1367009
theorem B1370209 : Blo 503794 1370209 := bstep (se 2 (by rfl) ⟨513828, by rfl⟩ : syracuseStep 1370209 = 1027657) B1027657
theorem B1140857 : Blo 503794 1140857 := bstep (se 2 (by rfl) ⟨427821, by rfl⟩ : syracuseStep 1140857 = 855643) B855643
theorem B2156777 : Blo 503794 2156777 := bstep (se 2 (by rfl) ⟨808791, by rfl⟩ : syracuseStep 2156777 = 1617583) B1617583
theorem B3074989 : Blo 503794 3074989 := bstep (se 3 (by rfl) ⟨576560, by rfl⟩ : syracuseStep 3074989 = 1153121) B1153121
theorem B9235633 : Blo 503794 9235633 := bstep (se 2 (by rfl) ⟨3463362, by rfl⟩ : syracuseStep 9235633 = 6926725) B6926725
theorem B1535159 : Blo 503794 1535159 := bstep (se 1 (by rfl) ⟨1151369, by rfl⟩ : syracuseStep 1535159 = 2302739) B2302739
theorem B2223287 : Blo 503794 2223287 := bstep (se 1 (by rfl) ⟨1667465, by rfl⟩ : syracuseStep 2223287 = 3334931) B3334931
theorem B1142171 : Blo 503794 1142171 := bstep (se 1 (by rfl) ⟨856628, by rfl⟩ : syracuseStep 1142171 = 1713257) B1713257
theorem B3829679 : Blo 503794 3829679 := bstep (se 1 (by rfl) ⟨2872259, by rfl⟩ : syracuseStep 3829679 = 5744519) B5744519
theorem B8188037 : Blo 503794 8188037 := bstep (se 4 (by rfl) ⟨767628, by rfl⟩ : syracuseStep 8188037 = 1535257) B1535257
theorem B8647397 : Blo 503794 8647397 := bstep (se 4 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 8647397 = 1621387) B1621387
theorem B4846787 : Blo 503794 4846787 := bstep (se 1 (by rfl) ⟨3635090, by rfl⟩ : syracuseStep 4846787 = 7270181) B7270181
theorem B1078601 : Blo 503794 1078601 := bstep (se 2 (by rfl) ⟨404475, by rfl⟩ : syracuseStep 1078601 = 808951) B808951
theorem B1276681 : Blo 503794 1276681 := bstep (se 2 (by rfl) ⟨478755, by rfl⟩ : syracuseStep 1276681 = 957511) B957511
theorem B19758275 : Blo 503794 19758275 := bstep (se 1 (by rfl) ⟨14818706, by rfl⟩ : syracuseStep 19758275 = 29637413) B29637413
theorem B1703375 : Blo 503794 1703375 := bstep (se 1 (by rfl) ⟨1277531, by rfl⟩ : syracuseStep 1703375 = 2555063) B2555063
theorem B2555549 : Blo 503794 2555549 := bstep (se 3 (by rfl) ⟨479165, by rfl⟩ : syracuseStep 2555549 = 958331) B958331
theorem B4849399 : Blo 503794 4849399 := bstep (se 1 (by rfl) ⟨3637049, by rfl⟩ : syracuseStep 4849399 = 7274099) B7274099
theorem B720839 : Blo 503794 720839 := bstep (se 1 (by rfl) ⟨540629, by rfl⟩ : syracuseStep 720839 = 1081259) B1081259
theorem B1704185 : Blo 503794 1704185 := bstep (se 2 (by rfl) ⟨639069, by rfl⟩ : syracuseStep 1704185 = 1278139) B1278139
theorem B2883833 : Blo 503794 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1704347 : Blo 503794 1704347 := bstep (se 1 (by rfl) ⟨1278260, by rfl⟩ : syracuseStep 1704347 = 2556521) B2556521
theorem B852383 : Blo 503794 852383 := bstep (se 1 (by rfl) ⟨639287, by rfl⟩ : syracuseStep 852383 = 1278575) B1278575
theorem B1704563 : Blo 503794 1704563 := bstep (se 1 (by rfl) ⟨1278422, by rfl⟩ : syracuseStep 1704563 = 2556845) B2556845
theorem B1278625 : Blo 503794 1278625 := bstep (se 2 (by rfl) ⟨479484, by rfl⟩ : syracuseStep 1278625 = 958969) B958969
theorem B1442623 : Blo 503794 1442623 := bstep (se 1 (by rfl) ⟨1081967, by rfl⟩ : syracuseStep 1442623 = 2163935) B2163935
theorem B721801 : Blo 503794 721801 := bstep (se 2 (by rfl) ⟨270675, by rfl⟩ : syracuseStep 721801 = 541351) B541351
theorem B1279415 : Blo 503794 1279415 := bstep (se 1 (by rfl) ⟨959561, by rfl⟩ : syracuseStep 1279415 = 1919123) B1919123
theorem B2426431 : Blo 503794 2426431 := bstep (se 1 (by rfl) ⟨1819823, by rfl⟩ : syracuseStep 2426431 = 3639647) B3639647
theorem B1705643 : Blo 503794 1705643 := bstep (se 1 (by rfl) ⟨1279232, by rfl⟩ : syracuseStep 1705643 = 2558465) B2558465
theorem B2885291 : Blo 503794 2885291 := bstep (se 1 (by rfl) ⟨2163968, by rfl⟩ : syracuseStep 2885291 = 4327937) B4327937
theorem B1279739 : Blo 503794 1279739 := bstep (se 1 (by rfl) ⟨959804, by rfl⟩ : syracuseStep 1279739 = 1919609) B1919609
theorem B755753 : Blo 503794 755753 := bstep (se 2 (by rfl) ⟨283407, by rfl⟩ : syracuseStep 755753 = 566815) B566815
theorem B854057 : Blo 503794 854057 := bstep (se 2 (by rfl) ⟨320271, by rfl⟩ : syracuseStep 854057 = 640543) B640543
theorem B755783 : Blo 503794 755783 := bstep (se 1 (by rfl) ⟨566837, by rfl⟩ : syracuseStep 755783 = 1133675) B1133675
theorem B1706183 : Blo 503794 1706183 := bstep (se 1 (by rfl) ⟨1279637, by rfl⟩ : syracuseStep 1706183 = 2559275) B2559275
theorem B755963 : Blo 503794 755963 := bstep (se 1 (by rfl) ⟨566972, by rfl⟩ : syracuseStep 755963 = 1133945) B1133945
theorem B4393223 : Blo 503794 4393223 := bstep (se 1 (by rfl) ⟨3294917, by rfl⟩ : syracuseStep 4393223 = 6589835) B6589835
theorem B756167 : Blo 503794 756167 := bstep (se 1 (by rfl) ⟨567125, by rfl⟩ : syracuseStep 756167 = 1134251) B1134251
theorem B756383 : Blo 503794 756383 := bstep (se 1 (by rfl) ⟨567287, by rfl⟩ : syracuseStep 756383 = 1134575) B1134575
theorem B9833159 : Blo 503794 9833159 := bstep (se 1 (by rfl) ⟨7374869, by rfl⟩ : syracuseStep 9833159 = 14749739) B14749739
theorem B756431 : Blo 503794 756431 := bstep (se 1 (by rfl) ⟨567323, by rfl⟩ : syracuseStep 756431 = 1134647) B1134647
theorem B756527 : Blo 503794 756527 := bstep (se 1 (by rfl) ⟨567395, by rfl⟩ : syracuseStep 756527 = 1134791) B1134791
theorem B1280873 : Blo 503794 1280873 := bstep (se 2 (by rfl) ⟨480327, by rfl⟩ : syracuseStep 1280873 = 960655) B960655
theorem B756647 : Blo 503794 756647 := bstep (se 1 (by rfl) ⟨567485, by rfl⟩ : syracuseStep 756647 = 1134971) B1134971
theorem B756827 : Blo 503794 756827 := bstep (se 1 (by rfl) ⟨567620, by rfl⟩ : syracuseStep 756827 = 1135241) B1135241
theorem B1444969 : Blo 503794 1444969 := bstep (se 2 (by rfl) ⟨541863, by rfl⟩ : syracuseStep 1444969 = 1083727) B1083727
theorem B756905 : Blo 503794 756905 := bstep (se 2 (by rfl) ⟨283839, by rfl⟩ : syracuseStep 756905 = 567679) B567679
theorem B5770763 : Blo 503794 5770763 := bstep (se 1 (by rfl) ⟨4328072, by rfl⟩ : syracuseStep 5770763 = 8656145) B8656145
theorem B757319 : Blo 503794 757319 := bstep (se 1 (by rfl) ⟨567989, by rfl⟩ : syracuseStep 757319 = 1135979) B1135979
theorem B2166497 : Blo 503794 2166497 := bstep (se 2 (by rfl) ⟨812436, by rfl⟩ : syracuseStep 2166497 = 1624873) B1624873
theorem B757499 : Blo 503794 757499 := bstep (se 1 (by rfl) ⟨568124, by rfl⟩ : syracuseStep 757499 = 1136249) B1136249
theorem B4099985 : Blo 503794 4099985 := bstep (se 2 (by rfl) ⟨1537494, by rfl⟩ : syracuseStep 4099985 = 3074989) B3074989
theorem B757739 : Blo 503794 757739 := bstep (se 1 (by rfl) ⟨568304, by rfl⟩ : syracuseStep 757739 = 1136609) B1136609
theorem B1282027 : Blo 503794 1282027 := bstep (se 1 (by rfl) ⟨961520, by rfl⟩ : syracuseStep 1282027 = 1923041) B1923041
theorem B4100215 : Blo 503794 4100215 := bstep (se 1 (by rfl) ⟨3075161, by rfl⟩ : syracuseStep 4100215 = 6150323) B6150323
theorem B3248363 : Blo 503794 3248363 := bstep (se 1 (by rfl) ⟨2436272, by rfl⟩ : syracuseStep 3248363 = 4872545) B4872545
theorem B2888207 : Blo 503794 2888207 := bstep (se 1 (by rfl) ⟨2166155, by rfl⟩ : syracuseStep 2888207 = 4332311) B4332311
theorem B2560733 : Blo 503794 2560733 := bstep (se 3 (by rfl) ⟨480137, by rfl⟩ : syracuseStep 2560733 = 960275) B960275
theorem B2888459 : Blo 503794 2888459 := bstep (se 1 (by rfl) ⟨2166344, by rfl⟩ : syracuseStep 2888459 = 4332689) B4332689
theorem B758777 : Blo 503794 758777 := bstep (se 2 (by rfl) ⟨284541, by rfl⟩ : syracuseStep 758777 = 569083) B569083
theorem B2561057 : Blo 503794 2561057 := bstep (se 2 (by rfl) ⟨960396, by rfl⟩ : syracuseStep 2561057 = 1920793) B1920793
theorem B3249335 : Blo 503794 3249335 := bstep (se 1 (by rfl) ⟨2437001, by rfl⟩ : syracuseStep 3249335 = 4874003) B4874003
theorem B758975 : Blo 503794 758975 := bstep (se 1 (by rfl) ⟨569231, by rfl⟩ : syracuseStep 758975 = 1138463) B1138463
theorem B759119 : Blo 503794 759119 := bstep (se 1 (by rfl) ⟨569339, by rfl⟩ : syracuseStep 759119 = 1138679) B1138679
theorem B759209 : Blo 503794 759209 := bstep (se 2 (by rfl) ⟨284703, by rfl⟩ : syracuseStep 759209 = 569407) B569407
theorem B759263 : Blo 503794 759263 := bstep (se 1 (by rfl) ⟨569447, by rfl⟩ : syracuseStep 759263 = 1138895) B1138895
theorem B759359 : Blo 503794 759359 := bstep (se 1 (by rfl) ⟨569519, by rfl⟩ : syracuseStep 759359 = 1139039) B1139039
theorem B5478025 : Blo 503794 5478025 := bstep (se 2 (by rfl) ⟨2054259, by rfl⟩ : syracuseStep 5478025 = 4108519) B4108519
theorem B759839 : Blo 503794 759839 := bstep (se 1 (by rfl) ⟨569879, by rfl⟩ : syracuseStep 759839 = 1139759) B1139759
theorem B760271 : Blo 503794 760271 := bstep (se 1 (by rfl) ⟨570203, by rfl⟩ : syracuseStep 760271 = 1140407) B1140407
theorem B760361 : Blo 503794 760361 := bstep (se 2 (by rfl) ⟨285135, by rfl⟩ : syracuseStep 760361 = 570271) B570271
theorem B760571 : Blo 503794 760571 := bstep (se 1 (by rfl) ⟨570428, by rfl⟩ : syracuseStep 760571 = 1140857) B1140857
theorem B760697 : Blo 503794 760697 := bstep (se 2 (by rfl) ⟨285261, by rfl⟩ : syracuseStep 760697 = 570523) B570523
theorem B2726905 : Blo 503794 2726905 := bstep (se 2 (by rfl) ⟨1022589, by rfl⟩ : syracuseStep 2726905 = 2045179) B2045179
theorem B1482191 : Blo 503794 1482191 := bstep (se 1 (by rfl) ⟨1111643, by rfl⟩ : syracuseStep 1482191 = 2223287) B2223287
theorem B761447 : Blo 503794 761447 := bstep (se 1 (by rfl) ⟨571085, by rfl⟩ : syracuseStep 761447 = 1142171) B1142171
theorem B761609 : Blo 503794 761609 := bstep (se 2 (by rfl) ⟨285603, by rfl⟩ : syracuseStep 761609 = 571207) B571207
theorem B5448059 : Blo 503794 5448059 := bstep (se 1 (by rfl) ⟨4086044, by rfl⟩ : syracuseStep 5448059 = 8172089) B8172089
theorem B6136357 : Blo 503794 6136357 := bstep (se 4 (by rfl) ⟨575283, by rfl⟩ : syracuseStep 6136357 = 1150567) B1150567
theorem B19768157 : Blo 503794 19768157 := bstep (se 3 (by rfl) ⟨3706529, by rfl⟩ : syracuseStep 19768157 = 7413059) B7413059
theorem B1713149 : Blo 503794 1713149 := bstep (se 3 (by rfl) ⟨321215, by rfl⟩ : syracuseStep 1713149 = 642431) B642431
theorem B2434121 : Blo 503794 2434121 := bstep (se 2 (by rfl) ⟨912795, by rfl⟩ : syracuseStep 2434121 = 1825591) B1825591
theorem B1713311 : Blo 503794 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B1713527 : Blo 503794 1713527 := bstep (se 1 (by rfl) ⟨1285145, by rfl⟩ : syracuseStep 1713527 = 2570291) B2570291
theorem B6465865 : Blo 503794 6465865 := bstep (se 2 (by rfl) ⟨2424699, by rfl⟩ : syracuseStep 6465865 = 4849399) B4849399
theorem B2567051 : Blo 503794 2567051 := bstep (se 1 (by rfl) ⟨1925288, by rfl⟩ : syracuseStep 2567051 = 3850577) B3850577
theorem B1387703 : Blo 503794 1387703 := bstep (se 1 (by rfl) ⟨1040777, by rfl⟩ : syracuseStep 1387703 = 2081555) B2081555
theorem B863419 : Blo 503794 863419 := bstep (se 1 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 863419 = 1295129) B1295129
theorem B2436311 : Blo 503794 2436311 := bstep (se 1 (by rfl) ⟨1827233, by rfl⟩ : syracuseStep 2436311 = 3654467) B3654467
theorem B2043103 : Blo 503794 2043103 := bstep (se 1 (by rfl) ⟨1532327, by rfl⟩ : syracuseStep 2043103 = 3064655) B3064655
theorem B569119 : Blo 503794 569119 := bstep (se 1 (by rfl) ⟨426839, by rfl⟩ : syracuseStep 569119 = 853679) B853679
theorem B504031 : Blo 503794 504031 := bstep (se 1 (by rfl) ⟨378023, by rfl⟩ : syracuseStep 504031 = 756047) B756047
theorem B504063 : Blo 503794 504063 := bstep (se 1 (by rfl) ⟨378047, by rfl⟩ : syracuseStep 504063 = 756095) B756095
theorem B504091 : Blo 503794 504091 := bstep (se 1 (by rfl) ⟨378068, by rfl⟩ : syracuseStep 504091 = 756137) B756137
theorem B1749289 : Blo 503794 1749289 := bstep (se 2 (by rfl) ⟨655983, by rfl⟩ : syracuseStep 1749289 = 1311967) B1311967
theorem B962857 : Blo 503794 962857 := bstep (se 2 (by rfl) ⟨361071, by rfl⟩ : syracuseStep 962857 = 722143) B722143
theorem B7811599 : Blo 503794 7811599 := bstep (se 1 (by rfl) ⟨5858699, by rfl⟩ : syracuseStep 7811599 = 11717399) B11717399
theorem B504347 : Blo 503794 504347 := bstep (se 1 (by rfl) ⟨378260, by rfl⟩ : syracuseStep 504347 = 756521) B756521
theorem B504487 : Blo 503794 504487 := bstep (se 1 (by rfl) ⟨378365, by rfl⟩ : syracuseStep 504487 = 756731) B756731
theorem B9712331 : Blo 503794 9712331 := bstep (se 1 (by rfl) ⟨7284248, by rfl⟩ : syracuseStep 9712331 = 14568497) B14568497
theorem B504527 : Blo 503794 504527 := bstep (se 1 (by rfl) ⟨378395, by rfl⟩ : syracuseStep 504527 = 756791) B756791
theorem B504607 : Blo 503794 504607 := bstep (se 1 (by rfl) ⟨378455, by rfl⟩ : syracuseStep 504607 = 756911) B756911
theorem B505087 : Blo 503794 505087 := bstep (se 1 (by rfl) ⟨378815, by rfl⟩ : syracuseStep 505087 = 757631) B757631
theorem B2569481 : Blo 503794 2569481 := bstep (se 2 (by rfl) ⟨963555, by rfl⟩ : syracuseStep 2569481 = 1927111) B1927111
theorem B13120861 : Blo 503794 13120861 := bstep (se 3 (by rfl) ⟨2460161, by rfl⟩ : syracuseStep 13120861 = 4920323) B4920323
theorem B505215 : Blo 503794 505215 := bstep (se 1 (by rfl) ⟨378911, by rfl⟩ : syracuseStep 505215 = 757823) B757823
theorem B3651095 : Blo 503794 3651095 := bstep (se 1 (by rfl) ⟨2738321, by rfl⟩ : syracuseStep 3651095 = 5476643) B5476643
theorem B505371 : Blo 503794 505371 := bstep (se 1 (by rfl) ⟨379028, by rfl⟩ : syracuseStep 505371 = 758057) B758057
theorem B4929133 : Blo 503794 4929133 := bstep (se 3 (by rfl) ⟨924212, by rfl⟩ : syracuseStep 4929133 = 1848425) B1848425
theorem B505551 : Blo 503794 505551 := bstep (se 1 (by rfl) ⟨379163, by rfl⟩ : syracuseStep 505551 = 758327) B758327
theorem B505791 : Blo 503794 505791 := bstep (se 1 (by rfl) ⟨379343, by rfl⟩ : syracuseStep 505791 = 758687) B758687
theorem B2439155 : Blo 503794 2439155 := bstep (se 1 (by rfl) ⟨1829366, by rfl⟩ : syracuseStep 2439155 = 3658733) B3658733
theorem B4864009 : Blo 503794 4864009 := bstep (se 2 (by rfl) ⟨1824003, by rfl⟩ : syracuseStep 4864009 = 3648007) B3648007
theorem B505919 : Blo 503794 505919 := bstep (se 1 (by rfl) ⟨379439, by rfl⟩ : syracuseStep 505919 = 758879) B758879
theorem B505959 : Blo 503794 505959 := bstep (se 1 (by rfl) ⟨379469, by rfl⟩ : syracuseStep 505959 = 758939) B758939
theorem B768287 : Blo 503794 768287 := bstep (se 1 (by rfl) ⟨576215, by rfl⟩ : syracuseStep 768287 = 1152431) B1152431
theorem B12990779 : Blo 503794 12990779 := bstep (se 1 (by rfl) ⟨9743084, by rfl⟩ : syracuseStep 12990779 = 19486169) B19486169
theorem B506415 : Blo 503794 506415 := bstep (se 1 (by rfl) ⟨379811, by rfl⟩ : syracuseStep 506415 = 759623) B759623
theorem B5454499 : Blo 503794 5454499 := bstep (se 1 (by rfl) ⟨4090874, by rfl⟩ : syracuseStep 5454499 = 8181749) B8181749
theorem B506815 : Blo 503794 506815 := bstep (se 1 (by rfl) ⟨380111, by rfl⟩ : syracuseStep 506815 = 760223) B760223
theorem B506863 : Blo 503794 506863 := bstep (se 1 (by rfl) ⟨380147, by rfl⟩ : syracuseStep 506863 = 760295) B760295
theorem B507359 : Blo 503794 507359 := bstep (se 1 (by rfl) ⟨380519, by rfl⟩ : syracuseStep 507359 = 761039) B761039
theorem B507439 : Blo 503794 507439 := bstep (se 1 (by rfl) ⟨380579, by rfl⟩ : syracuseStep 507439 = 761159) B761159
theorem B507547 : Blo 503794 507547 := bstep (se 1 (by rfl) ⟨380660, by rfl⟩ : syracuseStep 507547 = 761321) B761321
theorem B507643 : Blo 503794 507643 := bstep (se 1 (by rfl) ⟨380732, by rfl⟩ : syracuseStep 507643 = 761465) B761465
theorem B5783885 : Blo 503794 5783885 := bstep (se 3 (by rfl) ⟨1084478, by rfl⟩ : syracuseStep 5783885 = 2168957) B2168957
theorem B6472223 : Blo 503794 6472223 := bstep (se 1 (by rfl) ⟨4854167, by rfl⟩ : syracuseStep 6472223 = 9708335) B9708335
theorem B6505595 : Blo 503794 6505595 := bstep (se 1 (by rfl) ⟨4879196, by rfl⟩ : syracuseStep 6505595 = 9758393) B9758393
theorem B607559 : Blo 503794 607559 := bstep (se 1 (by rfl) ⟨455669, by rfl⟩ : syracuseStep 607559 = 911339) B911339
theorem B1296607 : Blo 503794 1296607 := bstep (se 1 (by rfl) ⟨972455, by rfl⟩ : syracuseStep 1296607 = 1944911) B1944911
theorem B3230117 : Blo 503794 3230117 := bstep (se 4 (by rfl) ⟨302823, by rfl⟩ : syracuseStep 3230117 = 605647) B605647
theorem B1362383 : Blo 503794 1362383 := bstep (se 1 (by rfl) ⟨1021787, by rfl⟩ : syracuseStep 1362383 = 2043575) B2043575
theorem B641515 : Blo 503794 641515 := bstep (se 1 (by rfl) ⟨481136, by rfl⟩ : syracuseStep 641515 = 962273) B962273
theorem B2345555 : Blo 503794 2345555 := bstep (se 1 (by rfl) ⟨1759166, by rfl⟩ : syracuseStep 2345555 = 3518333) B3518333
theorem B3066623 : Blo 503794 3066623 := bstep (se 1 (by rfl) ⟨2299967, by rfl⟩ : syracuseStep 3066623 = 4599935) B4599935
theorem B5458691 : Blo 503794 5458691 := bstep (se 1 (by rfl) ⟨4094018, by rfl⟩ : syracuseStep 5458691 = 8188037) B8188037
theorem B10931219 : Blo 503794 10931219 := bstep (se 1 (by rfl) ⟨8198414, by rfl⟩ : syracuseStep 10931219 = 16396829) B16396829
theorem B62311457 : Blo 503794 62311457 := bstep (se 2 (by rfl) ⟨23366796, by rfl⟩ : syracuseStep 62311457 = 46733593) B46733593
theorem B3231191 : Blo 503794 3231191 := bstep (se 1 (by rfl) ⟨2423393, by rfl⟩ : syracuseStep 3231191 = 4846787) B4846787
theorem B1363721 : Blo 503794 1363721 := bstep (se 2 (by rfl) ⟨511395, by rfl⟩ : syracuseStep 1363721 = 1022791) B1022791
theorem B13094783 : Blo 503794 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B9720485 : Blo 503794 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B5624657 : Blo 503794 5624657 := bstep (se 2 (by rfl) ⟨2109246, by rfl⟩ : syracuseStep 5624657 = 4218493) B4218493
theorem B1135583 : Blo 503794 1135583 := bstep (se 1 (by rfl) ⟨851687, by rfl⟩ : syracuseStep 1135583 = 1703375) B1703375
theorem B1922237 : Blo 503794 1922237 := bstep (se 3 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 1922237 = 720839) B720839
theorem B1136159 : Blo 503794 1136159 := bstep (se 1 (by rfl) ⟨852119, by rfl⟩ : syracuseStep 1136159 = 1704239) B1704239
theorem B13129381 : Blo 503794 13129381 := bstep (se 4 (by rfl) ⟨1230879, by rfl⟩ : syracuseStep 13129381 = 2461759) B2461759
theorem B12474101 : Blo 503794 12474101 := bstep (se 5 (by rfl) ⟨584723, by rfl⟩ : syracuseStep 12474101 = 1169447) B1169447
theorem B1136681 : Blo 503794 1136681 := bstep (se 2 (by rfl) ⟨426255, by rfl⟩ : syracuseStep 1136681 = 852511) B852511
theorem B12343549 : Blo 503794 12343549 := bstep (se 3 (by rfl) ⟨2314415, by rfl⟩ : syracuseStep 12343549 = 4628831) B4628831
theorem B2873627 : Blo 503794 2873627 := bstep (se 1 (by rfl) ⟨2155220, by rfl⟩ : syracuseStep 2873627 = 4310441) B4310441
theorem B1137311 : Blo 503794 1137311 := bstep (se 1 (by rfl) ⟨852983, by rfl⟩ : syracuseStep 1137311 = 1705967) B1705967
theorem B3234755 : Blo 503794 3234755 := bstep (se 1 (by rfl) ⟨2426066, by rfl⟩ : syracuseStep 3234755 = 4852133) B4852133
theorem B646375 : Blo 503794 646375 := bstep (se 1 (by rfl) ⟨484781, by rfl⟩ : syracuseStep 646375 = 969563) B969563
theorem B1826023 : Blo 503794 1826023 := bstep (se 1 (by rfl) ⟨1369517, by rfl⟩ : syracuseStep 1826023 = 2739035) B2739035
theorem B810361 : Blo 503794 810361 := bstep (se 2 (by rfl) ⟨303885, by rfl⟩ : syracuseStep 810361 = 607771) B607771
theorem B41606945 : Blo 503794 41606945 := bstep (se 2 (by rfl) ⟨15602604, by rfl⟩ : syracuseStep 41606945 = 31205209) B31205209
theorem B1728479 : Blo 503794 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B1925153 : Blo 503794 1925153 := bstep (se 2 (by rfl) ⟨721932, by rfl⟩ : syracuseStep 1925153 = 1443865) B1443865
theorem B1826945 : Blo 503794 1826945 := bstep (se 2 (by rfl) ⟨685104, by rfl⟩ : syracuseStep 1826945 = 1370209) B1370209
theorem B1138985 : Blo 503794 1138985 := bstep (se 2 (by rfl) ⟨427119, by rfl⟩ : syracuseStep 1138985 = 854239) B854239
theorem B1139255 : Blo 503794 1139255 := bstep (se 1 (by rfl) ⟨854441, by rfl⟩ : syracuseStep 1139255 = 1708883) B1708883
theorem B6546187 : Blo 503794 6546187 := bstep (se 1 (by rfl) ⟨4909640, by rfl⟩ : syracuseStep 6546187 = 9819281) B9819281
theorem B2876269 : Blo 503794 2876269 := bstep (se 3 (by rfl) ⟨539300, by rfl⟩ : syracuseStep 2876269 = 1078601) B1078601
theorem B1139615 : Blo 503794 1139615 := bstep (se 1 (by rfl) ⟨854711, by rfl⟩ : syracuseStep 1139615 = 1709423) B1709423
theorem B976103 : Blo 503794 976103 := bstep (se 1 (by rfl) ⟨732077, by rfl⟩ : syracuseStep 976103 = 1464155) B1464155
theorem B12346663 : Blo 503794 12346663 := bstep (se 1 (by rfl) ⟨9259997, by rfl⟩ : syracuseStep 12346663 = 18519995) B18519995
theorem B1140047 : Blo 503794 1140047 := bstep (se 1 (by rfl) ⟨855035, by rfl⟩ : syracuseStep 1140047 = 1710071) B1710071
theorem B1434991 : Blo 503794 1434991 := bstep (se 1 (by rfl) ⟨1076243, by rfl⟩ : syracuseStep 1434991 = 2152487) B2152487
theorem B1140137 : Blo 503794 1140137 := bstep (se 2 (by rfl) ⟨427551, by rfl⟩ : syracuseStep 1140137 = 855103) B855103
theorem B12314177 : Blo 503794 12314177 := bstep (se 2 (by rfl) ⟨4617816, by rfl⟩ : syracuseStep 12314177 = 9235633) B9235633
theorem B1140767 : Blo 503794 1140767 := bstep (se 1 (by rfl) ⟨855575, by rfl⟩ : syracuseStep 1140767 = 1711151) B1711151
theorem B11725049 : Blo 503794 11725049 := bstep (se 2 (by rfl) ⟨4396893, by rfl⟩ : syracuseStep 11725049 = 8793787) B8793787
theorem B3828221 : Blo 503794 3828221 := bstep (se 3 (by rfl) ⟨717791, by rfl⟩ : syracuseStep 3828221 = 1435583) B1435583
theorem B9726479 : Blo 503794 9726479 := bstep (se 1 (by rfl) ⟨7294859, by rfl⟩ : syracuseStep 9726479 = 14589719) B14589719
theorem B1141595 : Blo 503794 1141595 := bstep (se 1 (by rfl) ⟨856196, by rfl⟩ : syracuseStep 1141595 = 1712393) B1712393
theorem B5270465 : Blo 503794 5270465 := bstep (se 2 (by rfl) ⟨1976424, by rfl⟩ : syracuseStep 5270465 = 3952849) B3952849
theorem B1371161 : Blo 503794 1371161 := bstep (se 2 (by rfl) ⟨514185, by rfl⟩ : syracuseStep 1371161 = 1028371) B1028371
theorem B2551499 : Blo 503794 2551499 := bstep (se 1 (by rfl) ⟨1913624, by rfl⟩ : syracuseStep 2551499 = 3827249) B3827249
theorem B2158433 : Blo 503794 2158433 := bstep (se 2 (by rfl) ⟨809412, by rfl⟩ : syracuseStep 2158433 = 1618825) B1618825
theorem B1437851 : Blo 503794 1437851 := bstep (se 1 (by rfl) ⟨1078388, by rfl⟩ : syracuseStep 1437851 = 2156777) B2156777
theorem B5468471 : Blo 503794 5468471 := bstep (se 1 (by rfl) ⟨4101353, by rfl⟩ : syracuseStep 5468471 = 8202707) B8202707
theorem B4682519 : Blo 503794 4682519 := bstep (se 1 (by rfl) ⟨3511889, by rfl⟩ : syracuseStep 4682519 = 7023779) B7023779
theorem B43578161 : Blo 503794 43578161 := bstep (se 2 (by rfl) ⟨16341810, by rfl⟩ : syracuseStep 43578161 = 32683621) B32683621
theorem B2553119 : Blo 503794 2553119 := bstep (se 1 (by rfl) ⟨1914839, by rfl⟩ : syracuseStep 2553119 = 3829679) B3829679
theorem B4093757 : Blo 503794 4093757 := bstep (se 3 (by rfl) ⟨767579, by rfl⟩ : syracuseStep 4093757 = 1535159) B1535159
theorem B5764931 : Blo 503794 5764931 := bstep (se 1 (by rfl) ⟨4323698, by rfl⟩ : syracuseStep 5764931 = 8647397) B8647397
theorem B1275871 : Blo 503794 1275871 := bstep (se 1 (by rfl) ⟨956903, by rfl⟩ : syracuseStep 1275871 = 1913807) B1913807
theorem B1702241 : Blo 503794 1702241 := bstep (se 2 (by rfl) ⟨638340, by rfl⟩ : syracuseStep 1702241 = 1276681) B1276681
theorem B1276499 : Blo 503794 1276499 := bstep (se 1 (by rfl) ⟨957374, by rfl⟩ : syracuseStep 1276499 = 1914749) B1914749
theorem B1080071 : Blo 503794 1080071 := bstep (se 1 (by rfl) ⟨810053, by rfl⟩ : syracuseStep 1080071 = 1620107) B1620107
theorem B13172183 : Blo 503794 13172183 := bstep (se 1 (by rfl) ⟨9879137, by rfl⟩ : syracuseStep 13172183 = 19758275) B19758275
theorem B1736171 : Blo 503794 1736171 := bstep (se 1 (by rfl) ⟨1302128, by rfl⟩ : syracuseStep 1736171 = 2604257) B2604257
theorem B1080823 : Blo 503794 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B851593 : Blo 503794 851593 := bstep (se 2 (by rfl) ⟨319347, by rfl⟩ : syracuseStep 851593 = 638695) B638695
theorem B1703699 : Blo 503794 1703699 := bstep (se 1 (by rfl) ⟨1277774, by rfl⟩ : syracuseStep 1703699 = 2555549) B2555549
theorem B1704833 : Blo 503794 1704833 := bstep (se 2 (by rfl) ⟨639312, by rfl⟩ : syracuseStep 1704833 = 1278625) B1278625
theorem B852943 : Blo 503794 852943 := bstep (se 1 (by rfl) ⟨639707, by rfl⟩ : syracuseStep 852943 = 1279415) B1279415
theorem B3835025 : Blo 503794 3835025 := bstep (se 2 (by rfl) ⟨1438134, by rfl⟩ : syracuseStep 3835025 = 2876269) B2876269
theorem B853159 : Blo 503794 853159 := bstep (se 1 (by rfl) ⟨639869, by rfl⟩ : syracuseStep 853159 = 1279739) B1279739
theorem B6555439 : Blo 503794 6555439 := bstep (se 1 (by rfl) ⟨4916579, by rfl⟩ : syracuseStep 6555439 = 9833159) B9833159
theorem B3639127 : Blo 503794 3639127 := bstep (se 1 (by rfl) ⟨2729345, by rfl⟩ : syracuseStep 3639127 = 5458691) B5458691
theorem B853915 : Blo 503794 853915 := bstep (se 1 (by rfl) ⟨640436, by rfl⟩ : syracuseStep 853915 = 1280873) B1280873
theorem B1444331 : Blo 503794 1444331 := bstep (se 1 (by rfl) ⟨1083248, by rfl⟩ : syracuseStep 1444331 = 2166497) B2166497
theorem B2165575 : Blo 503794 2165575 := bstep (se 1 (by rfl) ⟨1624181, by rfl⟩ : syracuseStep 2165575 = 3248363) B3248363
theorem B8621153 : Blo 503794 8621153 := bstep (se 2 (by rfl) ⟨3232932, by rfl⟩ : syracuseStep 8621153 = 6465865) B6465865
theorem B1707155 : Blo 503794 1707155 := bstep (se 1 (by rfl) ⟨1280366, by rfl⟩ : syracuseStep 1707155 = 2560733) B2560733
theorem B855353 : Blo 503794 855353 := bstep (se 2 (by rfl) ⟨320757, by rfl⟩ : syracuseStep 855353 = 641515) B641515
theorem B757055 : Blo 503794 757055 := bstep (se 1 (by rfl) ⟨567791, by rfl⟩ : syracuseStep 757055 = 1135583) B1135583
theorem B1707371 : Blo 503794 1707371 := bstep (se 1 (by rfl) ⟨1280528, by rfl⟩ : syracuseStep 1707371 = 2561057) B2561057
theorem B1281491 : Blo 503794 1281491 := bstep (se 1 (by rfl) ⟨961118, by rfl⟩ : syracuseStep 1281491 = 1922237) B1922237
theorem B757439 : Blo 503794 757439 := bstep (se 1 (by rfl) ⟨568079, by rfl⟩ : syracuseStep 757439 = 1136159) B1136159
theorem B757787 : Blo 503794 757787 := bstep (se 1 (by rfl) ⟨568340, by rfl⟩ : syracuseStep 757787 = 1136681) B1136681
theorem B1151225 : Blo 503794 1151225 := bstep (se 2 (by rfl) ⟨431709, by rfl⟩ : syracuseStep 1151225 = 863419) B863419
theorem B2724137 : Blo 503794 2724137 := bstep (se 2 (by rfl) ⟨1021551, by rfl⟩ : syracuseStep 2724137 = 2043103) B2043103
theorem B758207 : Blo 503794 758207 := bstep (se 1 (by rfl) ⟨568655, by rfl⟩ : syracuseStep 758207 = 1137311) B1137311
theorem B988127 : Blo 503794 988127 := bstep (se 1 (by rfl) ⟨741095, by rfl⟩ : syracuseStep 988127 = 1482191) B1482191
theorem B758825 : Blo 503794 758825 := bstep (se 2 (by rfl) ⟨284559, by rfl⟩ : syracuseStep 758825 = 569119) B569119
theorem B1709369 : Blo 503794 1709369 := bstep (se 2 (by rfl) ⟨641013, by rfl⟩ : syracuseStep 1709369 = 1282027) B1282027
theorem B1152319 : Blo 503794 1152319 := bstep (se 1 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 1152319 = 1728479) B1728479
theorem B1283435 : Blo 503794 1283435 := bstep (se 1 (by rfl) ⟨962576, by rfl⟩ : syracuseStep 1283435 = 1925153) B1925153
theorem B1217963 : Blo 503794 1217963 := bstep (se 1 (by rfl) ⟨913472, by rfl⟩ : syracuseStep 1217963 = 1826945) B1826945
theorem B759323 : Blo 503794 759323 := bstep (se 1 (by rfl) ⟨569492, by rfl⟩ : syracuseStep 759323 = 1138985) B1138985
theorem B759503 : Blo 503794 759503 := bstep (se 1 (by rfl) ⟨569627, by rfl⟩ : syracuseStep 759503 = 1139255) B1139255
theorem B2332385 : Blo 503794 2332385 := bstep (se 2 (by rfl) ⟨874644, by rfl⟩ : syracuseStep 2332385 = 1749289) B1749289
theorem B1283809 : Blo 503794 1283809 := bstep (se 2 (by rfl) ⟨481428, by rfl⟩ : syracuseStep 1283809 = 962857) B962857
theorem B13178771 : Blo 503794 13178771 := bstep (se 1 (by rfl) ⟨9884078, by rfl⟩ : syracuseStep 13178771 = 19768157) B19768157
theorem B759743 : Blo 503794 759743 := bstep (se 1 (by rfl) ⟨569807, by rfl⟩ : syracuseStep 759743 = 1139615) B1139615
theorem B760031 : Blo 503794 760031 := bstep (se 1 (by rfl) ⟨570023, by rfl⟩ : syracuseStep 760031 = 1140047) B1140047
theorem B760091 : Blo 503794 760091 := bstep (se 1 (by rfl) ⟨570068, by rfl⟩ : syracuseStep 760091 = 1140137) B1140137
theorem B760511 : Blo 503794 760511 := bstep (se 1 (by rfl) ⟨570383, by rfl⟩ : syracuseStep 760511 = 1140767) B1140767
theorem B761063 : Blo 503794 761063 := bstep (se 1 (by rfl) ⟨570797, by rfl⟩ : syracuseStep 761063 = 1141595) B1141595
theorem B1711367 : Blo 503794 1711367 := bstep (se 1 (by rfl) ⟨1283525, by rfl⟩ : syracuseStep 1711367 = 2567051) B2567051
theorem B17505841 : Blo 503794 17505841 := bstep (se 2 (by rfl) ⟨6564690, by rfl⟩ : syracuseStep 17505841 = 13129381) B13129381
theorem B958567 : Blo 503794 958567 := bstep (se 1 (by rfl) ⟨718925, by rfl⟩ : syracuseStep 958567 = 1437851) B1437851
theorem B3645647 : Blo 503794 3645647 := bstep (se 1 (by rfl) ⟨2734235, by rfl⟩ : syracuseStep 3645647 = 5468471) B5468471
theorem B16458065 : Blo 503794 16458065 := bstep (se 2 (by rfl) ⟨6171774, by rfl⟩ : syracuseStep 16458065 = 12343549) B12343549
theorem B3121679 : Blo 503794 3121679 := bstep (se 1 (by rfl) ⟨2341259, by rfl⟩ : syracuseStep 3121679 = 4682519) B4682519
theorem B1712987 : Blo 503794 1712987 := bstep (se 1 (by rfl) ⟨1284740, by rfl⟩ : syracuseStep 1712987 = 2569481) B2569481
theorem B2434063 : Blo 503794 2434063 := bstep (se 1 (by rfl) ⟨1825547, by rfl⟩ : syracuseStep 2434063 = 3651095) B3651095
theorem B2729171 : Blo 503794 2729171 := bstep (se 1 (by rfl) ⟨2046878, by rfl⟩ : syracuseStep 2729171 = 4093757) B4093757
theorem B3843287 : Blo 503794 3843287 := bstep (se 1 (by rfl) ⟨2882465, by rfl⟩ : syracuseStep 3843287 = 5764931) B5764931
theorem B8660519 : Blo 503794 8660519 := bstep (se 1 (by rfl) ⟨6495389, by rfl⟩ : syracuseStep 8660519 = 12990779) B12990779
theorem B861833 : Blo 503794 861833 := bstep (se 2 (by rfl) ⟨323187, by rfl⟩ : syracuseStep 861833 = 646375) B646375
theorem B2434697 : Blo 503794 2434697 := bstep (se 2 (by rfl) ⟨913011, by rfl⟩ : syracuseStep 2434697 = 1826023) B1826023
theorem B1157447 : Blo 503794 1157447 := bstep (se 1 (by rfl) ⟨868085, by rfl⟩ : syracuseStep 1157447 = 1736171) B1736171
theorem B568255 : Blo 503794 568255 := bstep (se 1 (by rfl) ⟨426191, by rfl⟩ : syracuseStep 568255 = 852383) B852383
theorem B4337063 : Blo 503794 4337063 := bstep (se 1 (by rfl) ⟨3252797, by rfl⟩ : syracuseStep 4337063 = 6505595) B6505595
theorem B8728249 : Blo 503794 8728249 := bstep (se 2 (by rfl) ⟨3273093, by rfl⟩ : syracuseStep 8728249 = 6546187) B6546187
theorem B503835 : Blo 503794 503835 := bstep (se 1 (by rfl) ⟨377876, by rfl⟩ : syracuseStep 503835 = 755753) B755753
theorem B569371 : Blo 503794 569371 := bstep (se 1 (by rfl) ⟨427028, by rfl⟩ : syracuseStep 569371 = 854057) B854057
theorem B503855 : Blo 503794 503855 := bstep (se 1 (by rfl) ⟨377891, by rfl⟩ : syracuseStep 503855 = 755783) B755783
theorem B503975 : Blo 503794 503975 := bstep (se 1 (by rfl) ⟨377981, by rfl⟩ : syracuseStep 503975 = 755963) B755963
theorem B2928815 : Blo 503794 2928815 := bstep (se 1 (by rfl) ⟨2196611, by rfl⟩ : syracuseStep 2928815 = 4393223) B4393223
theorem B504111 : Blo 503794 504111 := bstep (se 1 (by rfl) ⟨378083, by rfl⟩ : syracuseStep 504111 = 756167) B756167
theorem B16462217 : Blo 503794 16462217 := bstep (se 2 (by rfl) ⟨6173331, by rfl⟩ : syracuseStep 16462217 = 12346663) B12346663
theorem B504255 : Blo 503794 504255 := bstep (se 1 (by rfl) ⟨378191, by rfl⟩ : syracuseStep 504255 = 756383) B756383
theorem B504287 : Blo 503794 504287 := bstep (se 1 (by rfl) ⟨378215, by rfl⟩ : syracuseStep 504287 = 756431) B756431
theorem B1913321 : Blo 503794 1913321 := bstep (se 2 (by rfl) ⟨717495, by rfl⟩ : syracuseStep 1913321 = 1434991) B1434991
theorem B2044415 : Blo 503794 2044415 := bstep (se 1 (by rfl) ⟨1533311, by rfl⟩ : syracuseStep 2044415 = 3066623) B3066623
theorem B504351 : Blo 503794 504351 := bstep (se 1 (by rfl) ⟨378263, by rfl⟩ : syracuseStep 504351 = 756527) B756527
theorem B504431 : Blo 503794 504431 := bstep (se 1 (by rfl) ⟨378323, by rfl⟩ : syracuseStep 504431 = 756647) B756647
theorem B7287479 : Blo 503794 7287479 := bstep (se 1 (by rfl) ⟨5465609, by rfl⟩ : syracuseStep 7287479 = 10931219) B10931219
theorem B504551 : Blo 503794 504551 := bstep (se 1 (by rfl) ⟨378413, by rfl⟩ : syracuseStep 504551 = 756827) B756827
theorem B504603 : Blo 503794 504603 := bstep (se 1 (by rfl) ⟨378452, by rfl⟩ : syracuseStep 504603 = 756905) B756905
theorem B3847175 : Blo 503794 3847175 := bstep (se 1 (by rfl) ⟨2885381, by rfl⟩ : syracuseStep 3847175 = 5770763) B5770763
theorem B504879 : Blo 503794 504879 := bstep (se 1 (by rfl) ⟨378659, by rfl⟩ : syracuseStep 504879 = 757319) B757319
theorem B504999 : Blo 503794 504999 := bstep (se 1 (by rfl) ⟨378749, by rfl⟩ : syracuseStep 504999 = 757499) B757499
theorem B8729855 : Blo 503794 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B2733323 : Blo 503794 2733323 := bstep (se 1 (by rfl) ⟨2049992, by rfl⟩ : syracuseStep 2733323 = 4099985) B4099985
theorem B505159 : Blo 503794 505159 := bstep (se 1 (by rfl) ⟨378869, by rfl⟩ : syracuseStep 505159 = 757739) B757739
theorem B8664893 : Blo 503794 8664893 := bstep (se 3 (by rfl) ⟨1624667, by rfl⟩ : syracuseStep 8664893 = 3249335) B3249335
theorem B3749771 : Blo 503794 3749771 := bstep (se 1 (by rfl) ⟨2812328, by rfl⟩ : syracuseStep 3749771 = 5624657) B5624657
theorem B505851 : Blo 503794 505851 := bstep (se 1 (by rfl) ⟨379388, by rfl⟩ : syracuseStep 505851 = 758777) B758777
theorem B505983 : Blo 503794 505983 := bstep (se 1 (by rfl) ⟨379487, by rfl⟩ : syracuseStep 505983 = 758975) B758975
theorem B1620157 : Blo 503794 1620157 := bstep (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) B607559
theorem B506079 : Blo 503794 506079 := bstep (se 1 (by rfl) ⟨379559, by rfl⟩ : syracuseStep 506079 = 759119) B759119
theorem B506139 : Blo 503794 506139 := bstep (se 1 (by rfl) ⟨379604, by rfl⟩ : syracuseStep 506139 = 759209) B759209
theorem B506175 : Blo 503794 506175 := bstep (se 1 (by rfl) ⟨379631, by rfl⟩ : syracuseStep 506175 = 759263) B759263
theorem B506239 : Blo 503794 506239 := bstep (se 1 (by rfl) ⟨379679, by rfl⟩ : syracuseStep 506239 = 759359) B759359
theorem B506559 : Blo 503794 506559 := bstep (se 1 (by rfl) ⟨379919, by rfl⟩ : syracuseStep 506559 = 759839) B759839
theorem B1915751 : Blo 503794 1915751 := bstep (se 1 (by rfl) ⟨1436813, by rfl⟩ : syracuseStep 1915751 = 2873627) B2873627
theorem B506847 : Blo 503794 506847 := bstep (se 1 (by rfl) ⟨380135, by rfl⟩ : syracuseStep 506847 = 760271) B760271
theorem B506907 : Blo 503794 506907 := bstep (se 1 (by rfl) ⟨380180, by rfl⟩ : syracuseStep 506907 = 760361) B760361
theorem B507047 : Blo 503794 507047 := bstep (se 1 (by rfl) ⟨380285, by rfl⟩ : syracuseStep 507047 = 760571) B760571
theorem B507131 : Blo 503794 507131 := bstep (se 1 (by rfl) ⟨380348, by rfl⟩ : syracuseStep 507131 = 760697) B760697
theorem B3849605 : Blo 503794 3849605 := bstep (se 4 (by rfl) ⟨360900, by rfl⟩ : syracuseStep 3849605 = 721801) B721801
theorem B507631 : Blo 503794 507631 := bstep (se 1 (by rfl) ⟨380723, by rfl⟩ : syracuseStep 507631 = 761447) B761447
theorem B507739 : Blo 503794 507739 := bstep (se 1 (by rfl) ⟨380804, by rfl⟩ : syracuseStep 507739 = 761609) B761609
theorem B27737963 : Blo 503794 27737963 := bstep (se 1 (by rfl) ⟨20803472, by rfl⟩ : syracuseStep 27737963 = 41606945) B41606945
theorem B1622747 : Blo 503794 1622747 := bstep (se 1 (by rfl) ⟨1217060, by rfl⟩ : syracuseStep 1622747 = 2434121) B2434121
theorem B8209451 : Blo 503794 8209451 := bstep (se 1 (by rfl) ⟨6157088, by rfl⟩ : syracuseStep 8209451 = 12314177) B12314177
theorem B7816699 : Blo 503794 7816699 := bstep (se 1 (by rfl) ⟨5862524, by rfl⟩ : syracuseStep 7816699 = 11725049) B11725049
theorem B1624207 : Blo 503794 1624207 := bstep (se 1 (by rfl) ⟨1218155, by rfl⟩ : syracuseStep 1624207 = 2436311) B2436311
theorem B6572177 : Blo 503794 6572177 := bstep (se 2 (by rfl) ⟨2464566, by rfl⟩ : syracuseStep 6572177 = 4929133) B4929133
theorem B6474887 : Blo 503794 6474887 := bstep (se 1 (by rfl) ⟨4856165, by rfl⟩ : syracuseStep 6474887 = 9712331) B9712331
theorem B29052107 : Blo 503794 29052107 := bstep (se 1 (by rfl) ⟨21789080, by rfl⟩ : syracuseStep 29052107 = 43578161) B43578161
theorem B1626103 : Blo 503794 1626103 := bstep (se 1 (by rfl) ⟨1219577, by rfl⟩ : syracuseStep 1626103 = 2439155) B2439155
theorem B512191 : Blo 503794 512191 := bstep (se 1 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 512191 = 768287) B768287
theorem B1134827 : Blo 503794 1134827 := bstep (se 1 (by rfl) ⟨851120, by rfl⟩ : syracuseStep 1134827 = 1702241) B1702241
theorem B1135457 : Blo 503794 1135457 := bstep (se 2 (by rfl) ⟨425796, by rfl⟩ : syracuseStep 1135457 = 851593) B851593
theorem B1135799 : Blo 503794 1135799 := bstep (se 1 (by rfl) ⟨851849, by rfl⟩ : syracuseStep 1135799 = 1703699) B1703699
theorem B1136123 : Blo 503794 1136123 := bstep (se 1 (by rfl) ⟨852092, by rfl⟩ : syracuseStep 1136123 = 1704185) B1704185
theorem B1922555 : Blo 503794 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B3855923 : Blo 503794 3855923 := bstep (se 1 (by rfl) ⟨2891942, by rfl⟩ : syracuseStep 3855923 = 5783885) B5783885
theorem B1136231 : Blo 503794 1136231 := bstep (se 1 (by rfl) ⟨852173, by rfl⟩ : syracuseStep 1136231 = 1704347) B1704347
theorem B4314815 : Blo 503794 4314815 := bstep (se 1 (by rfl) ⟨3236111, by rfl⟩ : syracuseStep 4314815 = 6472223) B6472223
theorem B1136375 : Blo 503794 1136375 := bstep (se 1 (by rfl) ⟨852281, by rfl⟩ : syracuseStep 1136375 = 1704563) B1704563
theorem B8181809 : Blo 503794 8181809 := bstep (se 2 (by rfl) ⟨3068178, by rfl⟩ : syracuseStep 8181809 = 6136357) B6136357
theorem B1923497 : Blo 503794 1923497 := bstep (se 2 (by rfl) ⟨721311, by rfl⟩ : syracuseStep 1923497 = 1442623) B1442623
theorem B1137095 : Blo 503794 1137095 := bstep (se 1 (by rfl) ⟨852821, by rfl⟩ : syracuseStep 1137095 = 1705643) B1705643
theorem B1923527 : Blo 503794 1923527 := bstep (se 1 (by rfl) ⟨1442645, by rfl⟩ : syracuseStep 1923527 = 2885291) B2885291
theorem B1137455 : Blo 503794 1137455 := bstep (se 1 (by rfl) ⟨853091, by rfl⟩ : syracuseStep 1137455 = 1706183) B1706183
theorem B2153411 : Blo 503794 2153411 := bstep (se 1 (by rfl) ⟨1615058, by rfl⟩ : syracuseStep 2153411 = 3230117) B3230117
theorem B908255 : Blo 503794 908255 := bstep (se 1 (by rfl) ⟨681191, by rfl⟩ : syracuseStep 908255 = 1362383) B1362383
theorem B41540971 : Blo 503794 41540971 := bstep (se 1 (by rfl) ⟨31155728, by rfl⟩ : syracuseStep 41540971 = 62311457) B62311457
theorem B3235241 : Blo 503794 3235241 := bstep (se 2 (by rfl) ⟨1213215, by rfl⟩ : syracuseStep 3235241 = 2426431) B2426431
theorem B2154127 : Blo 503794 2154127 := bstep (se 1 (by rfl) ⟨1615595, by rfl⟩ : syracuseStep 2154127 = 3231191) B3231191
theorem B1728809 : Blo 503794 1728809 := bstep (se 2 (by rfl) ⟨648303, by rfl⟩ : syracuseStep 1728809 = 1296607) B1296607
theorem B1925471 : Blo 503794 1925471 := bstep (se 1 (by rfl) ⟨1444103, by rfl⟩ : syracuseStep 1925471 = 2888207) B2888207
theorem B6480323 : Blo 503794 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B1925639 : Blo 503794 1925639 := bstep (se 1 (by rfl) ⟨1444229, by rfl⟩ : syracuseStep 1925639 = 2888459) B2888459
theorem B8316067 : Blo 503794 8316067 := bstep (se 1 (by rfl) ⟨6237050, by rfl⟩ : syracuseStep 8316067 = 12474101) B12474101
theorem B1926625 : Blo 503794 1926625 := bstep (se 2 (by rfl) ⟨722484, by rfl⟩ : syracuseStep 1926625 = 1444969) B1444969
theorem B2156503 : Blo 503794 2156503 := bstep (se 1 (by rfl) ⟨1617377, by rfl⟩ : syracuseStep 2156503 = 3234755) B3234755
theorem B5466953 : Blo 503794 5466953 := bstep (se 2 (by rfl) ⟨2050107, by rfl⟩ : syracuseStep 5466953 = 4100215) B4100215
theorem B3632039 : Blo 503794 3632039 := bstep (se 1 (by rfl) ⟨2724029, by rfl⟩ : syracuseStep 3632039 = 5448059) B5448059
theorem B1142099 : Blo 503794 1142099 := bstep (se 1 (by rfl) ⟨856574, by rfl⟩ : syracuseStep 1142099 = 1713149) B1713149
theorem B10415465 : Blo 503794 10415465 := bstep (se 2 (by rfl) ⟨3905799, by rfl⟩ : syracuseStep 10415465 = 7811599) B7811599
theorem B1142207 : Blo 503794 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B650735 : Blo 503794 650735 := bstep (se 1 (by rfl) ⟨488051, by rfl⟩ : syracuseStep 650735 = 976103) B976103
theorem B1142351 : Blo 503794 1142351 := bstep (se 1 (by rfl) ⟨856763, by rfl⟩ : syracuseStep 1142351 = 1713527) B1713527
theorem B6254813 : Blo 503794 6254813 := bstep (se 3 (by rfl) ⟨1172777, by rfl⟩ : syracuseStep 6254813 = 2345555) B2345555
theorem B2552147 : Blo 503794 2552147 := bstep (se 1 (by rfl) ⟨1914110, by rfl⟩ : syracuseStep 2552147 = 3828221) B3828221
theorem B6484319 : Blo 503794 6484319 := bstep (se 1 (by rfl) ⟨4863239, by rfl⟩ : syracuseStep 6484319 = 9726479) B9726479
theorem B17494481 : Blo 503794 17494481 := bstep (se 2 (by rfl) ⟨6560430, by rfl⟩ : syracuseStep 17494481 = 13120861) B13120861
theorem B914107 : Blo 503794 914107 := bstep (se 1 (by rfl) ⟨685580, by rfl⟩ : syracuseStep 914107 = 1371161) B1371161
theorem B7304033 : Blo 503794 7304033 := bstep (se 2 (by rfl) ⟨2739012, by rfl⟩ : syracuseStep 7304033 = 5478025) B5478025
theorem B1700999 : Blo 503794 1700999 := bstep (se 1 (by rfl) ⟨1275749, by rfl⟩ : syracuseStep 1700999 = 2551499) B2551499
theorem B14054573 : Blo 503794 14054573 := bstep (se 3 (by rfl) ⟨2635232, by rfl⟩ : syracuseStep 14054573 = 5270465) B5270465
theorem B1438955 : Blo 503794 1438955 := bstep (se 1 (by rfl) ⟨1079216, by rfl⟩ : syracuseStep 1438955 = 2158433) B2158433
theorem B1701161 : Blo 503794 1701161 := bstep (se 2 (by rfl) ⟨637935, by rfl⟩ : syracuseStep 1701161 = 1275871) B1275871
theorem B6485345 : Blo 503794 6485345 := bstep (se 2 (by rfl) ⟨2432004, by rfl⟩ : syracuseStep 6485345 = 4864009) B4864009
theorem B3700541 : Blo 503794 3700541 := bstep (se 3 (by rfl) ⟨693851, by rfl⟩ : syracuseStep 3700541 = 1387703) B1387703
theorem B1702079 : Blo 503794 1702079 := bstep (se 1 (by rfl) ⟨1276559, by rfl⟩ : syracuseStep 1702079 = 2553119) B2553119
theorem B7272665 : Blo 503794 7272665 := bstep (se 2 (by rfl) ⟨2727249, by rfl⟩ : syracuseStep 7272665 = 5454499) B5454499
theorem B3635873 : Blo 503794 3635873 := bstep (se 2 (by rfl) ⟨1363452, by rfl⟩ : syracuseStep 3635873 = 2726905) B2726905
theorem B850999 : Blo 503794 850999 := bstep (se 1 (by rfl) ⟨638249, by rfl⟩ : syracuseStep 850999 = 1276499) B1276499
theorem B1080481 : Blo 503794 1080481 := bstep (se 2 (by rfl) ⟨405180, by rfl⟩ : syracuseStep 1080481 = 810361) B810361
theorem B720047 : Blo 503794 720047 := bstep (se 1 (by rfl) ⟨540035, by rfl⟩ : syracuseStep 720047 = 1080071) B1080071
theorem B1441097 : Blo 503794 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B3636589 : Blo 503794 3636589 := bstep (se 3 (by rfl) ⟨681860, by rfl⟩ : syracuseStep 3636589 = 1363721) B1363721
theorem B8781455 : Blo 503794 8781455 := bstep (se 1 (by rfl) ⟨6586091, by rfl⟩ : syracuseStep 8781455 = 13172183) B13172183
theorem B1278089 : Blo 503794 1278089 := bstep (se 2 (by rfl) ⟨479283, by rfl⟩ : syracuseStep 1278089 = 958567) B958567
theorem B1081831 : Blo 503794 1081831 := bstep (se 1 (by rfl) ⟨811373, by rfl⟩ : syracuseStep 1081831 = 1622747) B1622747
theorem B5472967 : Blo 503794 5472967 := bstep (se 1 (by rfl) ⟨4104725, by rfl⟩ : syracuseStep 5472967 = 8209451) B8209451
theorem B2556683 : Blo 503794 2556683 := bstep (se 1 (by rfl) ⟨1917512, by rfl⟩ : syracuseStep 2556683 = 3835025) B3835025
theorem B3245417 : Blo 503794 3245417 := bstep (se 2 (by rfl) ⟨1217031, by rfl⟩ : syracuseStep 3245417 = 2434063) B2434063
theorem B10422265 : Blo 503794 10422265 := bstep (se 2 (by rfl) ⟨3908349, by rfl⟩ : syracuseStep 10422265 = 7816699) B7816699
theorem B19368071 : Blo 503794 19368071 := bstep (se 1 (by rfl) ⟨14526053, by rfl⟩ : syracuseStep 19368071 = 29052107) B29052107
theorem B854327 : Blo 503794 854327 := bstep (se 1 (by rfl) ⟨640745, by rfl⟩ : syracuseStep 854327 = 1281491) B1281491
theorem B4852169 : Blo 503794 4852169 := bstep (se 2 (by rfl) ⟨1819563, by rfl⟩ : syracuseStep 4852169 = 3639127) B3639127
theorem B756551 : Blo 503794 756551 := bstep (se 1 (by rfl) ⟨567413, by rfl⟩ : syracuseStep 756551 = 1134827) B1134827
theorem B2165609 : Blo 503794 2165609 := bstep (se 2 (by rfl) ⟨812103, by rfl⟩ : syracuseStep 2165609 = 1624207) B1624207
theorem B7277789 : Blo 503794 7277789 := bstep (se 3 (by rfl) ⟨1364585, by rfl⟩ : syracuseStep 7277789 = 2729171) B2729171
theorem B756971 : Blo 503794 756971 := bstep (se 1 (by rfl) ⟨567728, by rfl⟩ : syracuseStep 756971 = 1135457) B1135457
theorem B658751 : Blo 503794 658751 := bstep (se 1 (by rfl) ⟨494063, by rfl⟩ : syracuseStep 658751 = 988127) B988127
theorem B757199 : Blo 503794 757199 := bstep (se 1 (by rfl) ⟨567899, by rfl⟩ : syracuseStep 757199 = 1135799) B1135799
theorem B855623 : Blo 503794 855623 := bstep (se 1 (by rfl) ⟨641717, by rfl⟩ : syracuseStep 855623 = 1283435) B1283435
theorem B757415 : Blo 503794 757415 := bstep (se 1 (by rfl) ⟨568061, by rfl⟩ : syracuseStep 757415 = 1136123) B1136123
theorem B1281703 : Blo 503794 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B757487 : Blo 503794 757487 := bstep (se 1 (by rfl) ⟨568115, by rfl⟩ : syracuseStep 757487 = 1136231) B1136231
theorem B2887433 : Blo 503794 2887433 := bstep (se 2 (by rfl) ⟨1082787, by rfl⟩ : syracuseStep 2887433 = 2165575) B2165575
theorem B3247901 : Blo 503794 3247901 := bstep (se 3 (by rfl) ⟨608981, by rfl⟩ : syracuseStep 3247901 = 1217963) B1217963
theorem B757583 : Blo 503794 757583 := bstep (se 1 (by rfl) ⟨568187, by rfl⟩ : syracuseStep 757583 = 1136375) B1136375
theorem B757673 : Blo 503794 757673 := bstep (se 2 (by rfl) ⟨284127, by rfl⟩ : syracuseStep 757673 = 568255) B568255
theorem B8785847 : Blo 503794 8785847 := bstep (se 1 (by rfl) ⟨6589385, by rfl⟩ : syracuseStep 8785847 = 13178771) B13178771
theorem B1282331 : Blo 503794 1282331 := bstep (se 1 (by rfl) ⟨961748, by rfl⟩ : syracuseStep 1282331 = 1923497) B1923497
theorem B758063 : Blo 503794 758063 := bstep (se 1 (by rfl) ⟨568547, by rfl⟩ : syracuseStep 758063 = 1137095) B1137095
theorem B1282351 : Blo 503794 1282351 := bstep (se 1 (by rfl) ⟨961763, by rfl⟩ : syracuseStep 1282351 = 1923527) B1923527
theorem B758303 : Blo 503794 758303 := bstep (se 1 (by rfl) ⟨568727, by rfl⟩ : syracuseStep 758303 = 1137455) B1137455
theorem B11637665 : Blo 503794 11637665 := bstep (se 2 (by rfl) ⟨4364124, by rfl⟩ : syracuseStep 11637665 = 8728249) B8728249
theorem B9999389 : Blo 503794 9999389 := bstep (se 3 (by rfl) ⟨1874885, by rfl⟩ : syracuseStep 9999389 = 3749771) B3749771
theorem B2168137 : Blo 503794 2168137 := bstep (se 2 (by rfl) ⟨813051, by rfl⟩ : syracuseStep 2168137 = 1626103) B1626103
theorem B759161 : Blo 503794 759161 := bstep (se 2 (by rfl) ⟨284685, by rfl⟩ : syracuseStep 759161 = 569371) B569371
theorem B2430431 : Blo 503794 2430431 := bstep (se 1 (by rfl) ⟨1822823, by rfl⟩ : syracuseStep 2430431 = 3645647) B3645647
theorem B1152539 : Blo 503794 1152539 := bstep (se 1 (by rfl) ⟨864404, by rfl⟩ : syracuseStep 1152539 = 1728809) B1728809
theorem B1283647 : Blo 503794 1283647 := bstep (se 1 (by rfl) ⟨962735, by rfl⟩ : syracuseStep 1283647 = 1925471) B1925471
theorem B1283759 : Blo 503794 1283759 := bstep (se 1 (by rfl) ⟨962819, by rfl⟩ : syracuseStep 1283759 = 1925639) B1925639
theorem B2562191 : Blo 503794 2562191 := bstep (se 1 (by rfl) ⟨1921643, by rfl⟩ : syracuseStep 2562191 = 3843287) B3843287
theorem B3086525 : Blo 503794 3086525 := bstep (se 3 (by rfl) ⟨578723, by rfl⟩ : syracuseStep 3086525 = 1157447) B1157447
theorem B1218809 : Blo 503794 1218809 := bstep (se 2 (by rfl) ⟨457053, by rfl⟩ : syracuseStep 1218809 = 914107) B914107
theorem B5773679 : Blo 503794 5773679 := bstep (se 1 (by rfl) ⟨4330259, by rfl⟩ : syracuseStep 5773679 = 8660519) B8660519
theorem B761399 : Blo 503794 761399 := bstep (se 1 (by rfl) ⟨571049, by rfl⟩ : syracuseStep 761399 = 1142099) B1142099
theorem B2891375 : Blo 503794 2891375 := bstep (se 1 (by rfl) ⟨2168531, by rfl⟩ : syracuseStep 2891375 = 4337063) B4337063
theorem B761471 : Blo 503794 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B1711745 : Blo 503794 1711745 := bstep (se 2 (by rfl) ⟨641904, by rfl⟩ : syracuseStep 1711745 = 1283809) B1283809
theorem B761567 : Blo 503794 761567 := bstep (se 1 (by rfl) ⟨571175, by rfl⟩ : syracuseStep 761567 = 1142351) B1142351
theorem B4169875 : Blo 503794 4169875 := bstep (se 1 (by rfl) ⟨3127406, by rfl⟩ : syracuseStep 4169875 = 6254813) B6254813
theorem B4858319 : Blo 503794 4858319 := bstep (se 1 (by rfl) ⟨3643739, by rfl⟩ : syracuseStep 4858319 = 7287479) B7287479
theorem B2564783 : Blo 503794 2564783 := bstep (se 1 (by rfl) ⟨1923587, by rfl⟩ : syracuseStep 2564783 = 3847175) B3847175
theorem B959303 : Blo 503794 959303 := bstep (se 1 (by rfl) ⟨719477, by rfl⟩ : syracuseStep 959303 = 1438955) B1438955
theorem B2467027 : Blo 503794 2467027 := bstep (se 1 (by rfl) ⟨1850270, by rfl⟩ : syracuseStep 2467027 = 3700541) B3700541
theorem B5776595 : Blo 503794 5776595 := bstep (se 1 (by rfl) ⟨4332446, by rfl⟩ : syracuseStep 5776595 = 8664893) B8664893
theorem B55387961 : Blo 503794 55387961 := bstep (se 2 (by rfl) ⟨20770485, by rfl⟩ : syracuseStep 55387961 = 41540971) B41540971
theorem B23341121 : Blo 503794 23341121 := bstep (se 2 (by rfl) ⟨8752920, by rfl⟩ : syracuseStep 23341121 = 17505841) B17505841
theorem B960731 : Blo 503794 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B2566403 : Blo 503794 2566403 := bstep (se 1 (by rfl) ⟨1924802, by rfl⟩ : syracuseStep 2566403 = 3849605) B3849605
theorem B18491975 : Blo 503794 18491975 := bstep (se 1 (by rfl) ⟨13868981, by rfl⟩ : syracuseStep 18491975 = 27737963) B27737963
theorem B11088089 : Blo 503794 11088089 := bstep (se 2 (by rfl) ⟨4158033, by rfl⟩ : syracuseStep 11088089 = 8316067) B8316067
theorem B2568833 : Blo 503794 2568833 := bstep (se 2 (by rfl) ⟨963312, by rfl⟩ : syracuseStep 2568833 = 1926625) B1926625
theorem B5747435 : Blo 503794 5747435 := bstep (se 1 (by rfl) ⟨4310576, by rfl⟩ : syracuseStep 5747435 = 8621153) B8621153
theorem B570235 : Blo 503794 570235 := bstep (se 1 (by rfl) ⟨427676, by rfl⟩ : syracuseStep 570235 = 855353) B855353
theorem B504703 : Blo 503794 504703 := bstep (se 1 (by rfl) ⟨378527, by rfl⟩ : syracuseStep 504703 = 757055) B757055
theorem B504959 : Blo 503794 504959 := bstep (se 1 (by rfl) ⟨378719, by rfl⟩ : syracuseStep 504959 = 757439) B757439
theorem B505191 : Blo 503794 505191 := bstep (se 1 (by rfl) ⟨378893, by rfl⟩ : syracuseStep 505191 = 757787) B757787
theorem B767483 : Blo 503794 767483 := bstep (se 1 (by rfl) ⟨575612, by rfl⟩ : syracuseStep 767483 = 1151225) B1151225
theorem B1816091 : Blo 503794 1816091 := bstep (se 1 (by rfl) ⟨1362068, by rfl⟩ : syracuseStep 1816091 = 2724137) B2724137
theorem B505471 : Blo 503794 505471 := bstep (se 1 (by rfl) ⟨379103, by rfl⟩ : syracuseStep 505471 = 758207) B758207
theorem B505883 : Blo 503794 505883 := bstep (se 1 (by rfl) ⟨379412, by rfl⟩ : syracuseStep 505883 = 758825) B758825
theorem B7288861 : Blo 503794 7288861 := bstep (se 3 (by rfl) ⟨1366661, by rfl⟩ : syracuseStep 7288861 = 2733323) B2733323
theorem B506215 : Blo 503794 506215 := bstep (se 1 (by rfl) ⟨379661, by rfl⟩ : syracuseStep 506215 = 759323) B759323
theorem B2570615 : Blo 503794 2570615 := bstep (se 1 (by rfl) ⟨1927961, by rfl⟩ : syracuseStep 2570615 = 3855923) B3855923
theorem B506335 : Blo 503794 506335 := bstep (se 1 (by rfl) ⟨379751, by rfl⟩ : syracuseStep 506335 = 759503) B759503
theorem B1554923 : Blo 503794 1554923 := bstep (se 1 (by rfl) ⟨1166192, by rfl⟩ : syracuseStep 1554923 = 2332385) B2332385
theorem B506495 : Blo 503794 506495 := bstep (se 1 (by rfl) ⟨379871, by rfl⟩ : syracuseStep 506495 = 759743) B759743
theorem B5454539 : Blo 503794 5454539 := bstep (se 1 (by rfl) ⟨4090904, by rfl⟩ : syracuseStep 5454539 = 8181809) B8181809
theorem B506687 : Blo 503794 506687 := bstep (se 1 (by rfl) ⟨380015, by rfl⟩ : syracuseStep 506687 = 760031) B760031
theorem B506727 : Blo 503794 506727 := bstep (se 1 (by rfl) ⟨380045, by rfl⟩ : syracuseStep 506727 = 760091) B760091
theorem B507007 : Blo 503794 507007 := bstep (se 1 (by rfl) ⟨380255, by rfl⟩ : syracuseStep 507007 = 760511) B760511
theorem B605503 : Blo 503794 605503 := bstep (se 1 (by rfl) ⟨454127, by rfl⟩ : syracuseStep 605503 = 908255) B908255
theorem B507375 : Blo 503794 507375 := bstep (se 1 (by rfl) ⟨380531, by rfl⟩ : syracuseStep 507375 = 761063) B761063
theorem B2081119 : Blo 503794 2081119 := bstep (se 1 (by rfl) ⟨1560839, by rfl⟩ : syracuseStep 2081119 = 3121679) B3121679
theorem B574555 : Blo 503794 574555 := bstep (se 1 (by rfl) ⟨430916, by rfl⟩ : syracuseStep 574555 = 861833) B861833
theorem B1623131 : Blo 503794 1623131 := bstep (se 1 (by rfl) ⟨1217348, by rfl⟩ : syracuseStep 1623131 = 2434697) B2434697
theorem B3851549 : Blo 503794 3851549 := bstep (se 3 (by rfl) ⟨722165, by rfl⟩ : syracuseStep 3851549 = 1444331) B1444331
theorem B1952543 : Blo 503794 1952543 := bstep (se 1 (by rfl) ⟨1464407, by rfl⟩ : syracuseStep 1952543 = 2928815) B2928815
theorem B1362943 : Blo 503794 1362943 := bstep (se 1 (by rfl) ⟨1022207, by rfl⟩ : syracuseStep 1362943 = 2044415) B2044415
theorem B1920125 : Blo 503794 1920125 := bstep (se 3 (by rfl) ⟨360023, by rfl⟩ : syracuseStep 1920125 = 720047) B720047
theorem B4869355 : Blo 503794 4869355 := bstep (se 1 (by rfl) ⟨3652016, by rfl⟩ : syracuseStep 4869355 = 7304033) B7304033
theorem B1133999 : Blo 503794 1133999 := bstep (se 1 (by rfl) ⟨850499, by rfl⟩ : syracuseStep 1133999 = 1700999) B1700999
theorem B5819903 : Blo 503794 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B1134107 : Blo 503794 1134107 := bstep (se 1 (by rfl) ⟨850580, by rfl⟩ : syracuseStep 1134107 = 1701161) B1701161
theorem B1134665 : Blo 503794 1134665 := bstep (se 2 (by rfl) ⟨425499, by rfl⟩ : syracuseStep 1134665 = 850999) B850999
theorem B1134719 : Blo 503794 1134719 := bstep (se 1 (by rfl) ⟨851039, by rfl⟩ : syracuseStep 1134719 = 1702079) B1702079
theorem B2872169 : Blo 503794 2872169 := bstep (se 2 (by rfl) ⟨1077063, by rfl⟩ : syracuseStep 2872169 = 2154127) B2154127
theorem B5854303 : Blo 503794 5854303 := bstep (se 1 (by rfl) ⟨4390727, by rfl⟩ : syracuseStep 5854303 = 8781455) B8781455
theorem B1136555 : Blo 503794 1136555 := bstep (se 1 (by rfl) ⟨852416, by rfl⟩ : syracuseStep 1136555 = 1704833) B1704833
theorem B1137257 : Blo 503794 1137257 := bstep (se 2 (by rfl) ⟨426471, by rfl⟩ : syracuseStep 1137257 = 852943) B852943
theorem B4381451 : Blo 503794 4381451 := bstep (se 1 (by rfl) ⟨3286088, by rfl⟩ : syracuseStep 4381451 = 6572177) B6572177
theorem B1137545 : Blo 503794 1137545 := bstep (se 2 (by rfl) ⟨426579, by rfl⟩ : syracuseStep 1137545 = 853159) B853159
theorem B4316591 : Blo 503794 4316591 := bstep (se 1 (by rfl) ⟨3237443, by rfl⟩ : syracuseStep 4316591 = 6474887) B6474887
theorem B1138103 : Blo 503794 1138103 := bstep (se 1 (by rfl) ⟨853577, by rfl⟩ : syracuseStep 1138103 = 1707155) B1707155
theorem B1138247 : Blo 503794 1138247 := bstep (se 1 (by rfl) ⟨853685, by rfl⟩ : syracuseStep 1138247 = 1707371) B1707371
theorem B8740585 : Blo 503794 8740585 := bstep (se 2 (by rfl) ⟨3277719, by rfl⟩ : syracuseStep 8740585 = 6555439) B6555439
theorem B1138553 : Blo 503794 1138553 := bstep (se 2 (by rfl) ⟨426957, by rfl⟩ : syracuseStep 1138553 = 853915) B853915
theorem B2875337 : Blo 503794 2875337 := bstep (se 2 (by rfl) ⟨1078251, by rfl⟩ : syracuseStep 2875337 = 2156503) B2156503
theorem B37478861 : Blo 503794 37478861 := bstep (se 3 (by rfl) ⟨7027286, by rfl⟩ : syracuseStep 37478861 = 14054573) B14054573
theorem B1139579 : Blo 503794 1139579 := bstep (se 1 (by rfl) ⟨854684, by rfl⟩ : syracuseStep 1139579 = 1709369) B1709369
theorem B2876543 : Blo 503794 2876543 := bstep (se 1 (by rfl) ⟨2157407, by rfl⟩ : syracuseStep 2876543 = 4314815) B4314815
theorem B1435607 : Blo 503794 1435607 := bstep (se 1 (by rfl) ⟨1076705, by rfl⟩ : syracuseStep 1435607 = 2153411) B2153411
theorem B1140911 : Blo 503794 1140911 := bstep (se 1 (by rfl) ⟨855683, by rfl⟩ : syracuseStep 1140911 = 1711367) B1711367
theorem B2156827 : Blo 503794 2156827 := bstep (se 1 (by rfl) ⟨1617620, by rfl⟩ : syracuseStep 2156827 = 3235241) B3235241
theorem B6941173 : Blo 503794 6941173 := bstep (se 5 (by rfl) ⟨325367, by rfl⟩ : syracuseStep 6941173 = 650735) B650735
theorem B10972043 : Blo 503794 10972043 := bstep (se 1 (by rfl) ⟨8229032, by rfl⟩ : syracuseStep 10972043 = 16458065) B16458065
theorem B682921 : Blo 503794 682921 := bstep (se 2 (by rfl) ⟨256095, by rfl⟩ : syracuseStep 682921 = 512191) B512191
theorem B4320215 : Blo 503794 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B1141991 : Blo 503794 1141991 := bstep (se 1 (by rfl) ⟨856493, by rfl⟩ : syracuseStep 1141991 = 1712987) B1712987
theorem B1536425 : Blo 503794 1536425 := bstep (se 2 (by rfl) ⟨576159, by rfl⟩ : syracuseStep 1536425 = 1152319) B1152319
theorem B2421359 : Blo 503794 2421359 := bstep (se 1 (by rfl) ⟨1816019, by rfl⟩ : syracuseStep 2421359 = 3632039) B3632039
theorem B14578541 : Blo 503794 14578541 := bstep (se 3 (by rfl) ⟨2733476, by rfl⟩ : syracuseStep 14578541 = 5466953) B5466953
theorem B6943643 : Blo 503794 6943643 := bstep (se 1 (by rfl) ⟨5207732, by rfl⟩ : syracuseStep 6943643 = 10415465) B10415465
theorem B1701431 : Blo 503794 1701431 := bstep (se 1 (by rfl) ⟨1276073, by rfl⟩ : syracuseStep 1701431 = 2552147) B2552147
theorem B4322879 : Blo 503794 4322879 := bstep (se 1 (by rfl) ⟨3242159, by rfl⟩ : syracuseStep 4322879 = 6484319) B6484319
theorem B2160209 : Blo 503794 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B10974811 : Blo 503794 10974811 := bstep (se 1 (by rfl) ⟨8231108, by rfl⟩ : syracuseStep 10974811 = 16462217) B16462217
theorem B11662987 : Blo 503794 11662987 := bstep (se 1 (by rfl) ⟨8747240, by rfl⟩ : syracuseStep 11662987 = 17494481) B17494481
theorem B1275547 : Blo 503794 1275547 := bstep (se 1 (by rfl) ⟨956660, by rfl⟩ : syracuseStep 1275547 = 1913321) B1913321
theorem B4323563 : Blo 503794 4323563 := bstep (se 1 (by rfl) ⟨3242672, by rfl⟩ : syracuseStep 4323563 = 6485345) B6485345
theorem B4848443 : Blo 503794 4848443 := bstep (se 1 (by rfl) ⟨3636332, by rfl⟩ : syracuseStep 4848443 = 7272665) B7272665
theorem B1440641 : Blo 503794 1440641 := bstep (se 2 (by rfl) ⟨540240, by rfl⟩ : syracuseStep 1440641 = 1080481) B1080481
theorem B2423915 : Blo 503794 2423915 := bstep (se 1 (by rfl) ⟨1817936, by rfl⟩ : syracuseStep 2423915 = 3635873) B3635873
theorem B4848785 : Blo 503794 4848785 := bstep (se 2 (by rfl) ⟨1818294, by rfl⟩ : syracuseStep 4848785 = 3636589) B3636589
theorem B1277167 : Blo 503794 1277167 := bstep (se 1 (by rfl) ⟨957875, by rfl⟩ : syracuseStep 1277167 = 1915751) B1915751
theorem B852059 : Blo 503794 852059 := bstep (se 1 (by rfl) ⟨639044, by rfl⟩ : syracuseStep 852059 = 1278089) B1278089
theorem B1704455 : Blo 503794 1704455 := bstep (se 1 (by rfl) ⟨1278341, by rfl⟩ : syracuseStep 1704455 = 2556683) B2556683
theorem B1442441 : Blo 503794 1442441 := bstep (se 2 (by rfl) ⟨540915, by rfl⟩ : syracuseStep 1442441 = 1081831) B1081831
theorem B1082087 : Blo 503794 1082087 := bstep (se 1 (by rfl) ⟨811565, by rfl⟩ : syracuseStep 1082087 = 1623131) B1623131
theorem B2163611 : Blo 503794 2163611 := bstep (se 1 (by rfl) ⟨1622708, by rfl⟩ : syracuseStep 2163611 = 3245417) B3245417
theorem B12912047 : Blo 503794 12912047 := bstep (se 1 (by rfl) ⟨9684035, by rfl⟩ : syracuseStep 12912047 = 19368071) B19368071
theorem B1443739 : Blo 503794 1443739 := bstep (se 1 (by rfl) ⟨1082804, by rfl⟩ : syracuseStep 1443739 = 2165609) B2165609
theorem B1280083 : Blo 503794 1280083 := bstep (se 1 (by rfl) ⟨960062, by rfl⟩ : syracuseStep 1280083 = 1920125) B1920125
theorem B2558141 : Blo 503794 2558141 := bstep (se 3 (by rfl) ⟨479651, by rfl⟩ : syracuseStep 2558141 = 959303) B959303
theorem B755999 : Blo 503794 755999 := bstep (se 1 (by rfl) ⟨566999, by rfl⟩ : syracuseStep 755999 = 1133999) B1133999
theorem B756071 : Blo 503794 756071 := bstep (se 1 (by rfl) ⟨567053, by rfl⟩ : syracuseStep 756071 = 1134107) B1134107
theorem B2165267 : Blo 503794 2165267 := bstep (se 1 (by rfl) ⟨1623950, by rfl⟩ : syracuseStep 2165267 = 3247901) B3247901
theorem B13896353 : Blo 503794 13896353 := bstep (se 2 (by rfl) ⟨5211132, by rfl⟩ : syracuseStep 13896353 = 10422265) B10422265
theorem B756443 : Blo 503794 756443 := bstep (se 1 (by rfl) ⟨567332, by rfl⟩ : syracuseStep 756443 = 1134665) B1134665
theorem B756479 : Blo 503794 756479 := bstep (se 1 (by rfl) ⟨567359, by rfl⟩ : syracuseStep 756479 = 1134719) B1134719
theorem B854887 : Blo 503794 854887 := bstep (se 1 (by rfl) ⟨641165, by rfl⟩ : syracuseStep 854887 = 1282331) B1282331
theorem B855839 : Blo 503794 855839 := bstep (se 1 (by rfl) ⟨641879, by rfl⟩ : syracuseStep 855839 = 1283759) B1283759
theorem B757703 : Blo 503794 757703 := bstep (se 1 (by rfl) ⟨568277, by rfl⟩ : syracuseStep 757703 = 1136555) B1136555
theorem B1708127 : Blo 503794 1708127 := bstep (se 1 (by rfl) ⟨1281095, by rfl⟩ : syracuseStep 1708127 = 2562191) B2562191
theorem B6492473 : Blo 503794 6492473 := bstep (se 2 (by rfl) ⟨2434677, by rfl⟩ : syracuseStep 6492473 = 4869355) B4869355
theorem B758171 : Blo 503794 758171 := bstep (se 1 (by rfl) ⟨568628, by rfl⟩ : syracuseStep 758171 = 1137257) B1137257
theorem B2920967 : Blo 503794 2920967 := bstep (se 1 (by rfl) ⟨2190725, by rfl⟩ : syracuseStep 2920967 = 4381451) B4381451
theorem B758363 : Blo 503794 758363 := bstep (se 1 (by rfl) ⟨568772, by rfl⟩ : syracuseStep 758363 = 1137545) B1137545
theorem B3642245 : Blo 503794 3642245 := bstep (se 4 (by rfl) ⟨341460, by rfl⟩ : syracuseStep 3642245 = 682921) B682921
theorem B1708937 : Blo 503794 1708937 := bstep (se 2 (by rfl) ⟨640851, by rfl⟩ : syracuseStep 1708937 = 1281703) B1281703
theorem B758735 : Blo 503794 758735 := bstep (se 1 (by rfl) ⟨569051, by rfl⟩ : syracuseStep 758735 = 1138103) B1138103
theorem B758831 : Blo 503794 758831 := bstep (se 1 (by rfl) ⟨569123, by rfl⟩ : syracuseStep 758831 = 1138247) B1138247
theorem B759035 : Blo 503794 759035 := bstep (se 1 (by rfl) ⟨569276, by rfl⟩ : syracuseStep 759035 = 1138553) B1138553
theorem B1709801 : Blo 503794 1709801 := bstep (se 2 (by rfl) ⟨641175, by rfl⟩ : syracuseStep 1709801 = 1282351) B1282351
theorem B1709855 : Blo 503794 1709855 := bstep (se 1 (by rfl) ⟨1282391, by rfl⟩ : syracuseStep 1709855 = 2564783) B2564783
theorem B759719 : Blo 503794 759719 := bstep (se 1 (by rfl) ⟨569789, by rfl⟩ : syracuseStep 759719 = 1139579) B1139579
theorem B760313 : Blo 503794 760313 := bstep (se 2 (by rfl) ⟨285117, by rfl⟩ : syracuseStep 760313 = 570235) B570235
theorem B957071 : Blo 503794 957071 := bstep (se 1 (by rfl) ⟨717803, by rfl⟩ : syracuseStep 957071 = 1435607) B1435607
theorem B760607 : Blo 503794 760607 := bstep (se 1 (by rfl) ⟨570455, by rfl⟩ : syracuseStep 760607 = 1140911) B1140911
theorem B7805737 : Blo 503794 7805737 := bstep (se 2 (by rfl) ⟨2927151, by rfl⟩ : syracuseStep 7805737 = 5854303) B5854303
theorem B1710935 : Blo 503794 1710935 := bstep (se 1 (by rfl) ⟨1283201, by rfl⟩ : syracuseStep 1710935 = 2566403) B2566403
theorem B12327983 : Blo 503794 12327983 := bstep (se 1 (by rfl) ⟨9245987, by rfl⟩ : syracuseStep 12327983 = 18491975) B18491975
theorem B2890849 : Blo 503794 2890849 := bstep (se 2 (by rfl) ⟨1084068, by rfl⟩ : syracuseStep 2890849 = 2168137) B2168137
theorem B7314695 : Blo 503794 7314695 := bstep (se 1 (by rfl) ⟨5486021, by rfl⟩ : syracuseStep 7314695 = 10972043) B10972043
theorem B1711529 : Blo 503794 1711529 := bstep (se 2 (by rfl) ⟨641823, by rfl⟩ : syracuseStep 1711529 = 1283647) B1283647
theorem B761327 : Blo 503794 761327 := bstep (se 1 (by rfl) ⟨570995, by rfl⟩ : syracuseStep 761327 = 1141991) B1141991
theorem B1024283 : Blo 503794 1024283 := bstep (se 1 (by rfl) ⟨768212, by rfl⟩ : syracuseStep 1024283 = 1536425) B1536425
theorem B1614239 : Blo 503794 1614239 := bstep (se 1 (by rfl) ⟨1210679, by rfl⟩ : syracuseStep 1614239 = 2421359) B2421359
theorem B1712555 : Blo 503794 1712555 := bstep (se 1 (by rfl) ⟨1284416, by rfl⟩ : syracuseStep 1712555 = 2568833) B2568833
theorem B19407437 : Blo 503794 19407437 := bstep (se 3 (by rfl) ⟨3638894, by rfl⟩ : syracuseStep 19407437 = 7277789) B7277789
theorem B4629095 : Blo 503794 4629095 := bstep (se 1 (by rfl) ⟨3471821, by rfl⟩ : syracuseStep 4629095 = 6943643) B6943643
theorem B1713743 : Blo 503794 1713743 := bstep (se 1 (by rfl) ⟨1285307, by rfl⟩ : syracuseStep 1713743 = 2570615) B2570615
theorem B960427 : Blo 503794 960427 := bstep (se 1 (by rfl) ⟨720320, by rfl⟩ : syracuseStep 960427 = 1440641) B1440641
theorem B1615943 : Blo 503794 1615943 := bstep (se 1 (by rfl) ⟨1211957, by rfl⟩ : syracuseStep 1615943 = 2423915) B2423915
theorem B2567699 : Blo 503794 2567699 := bstep (se 1 (by rfl) ⟨1925774, by rfl⟩ : syracuseStep 2567699 = 3851549) B3851549
theorem B766073 : Blo 503794 766073 := bstep (se 2 (by rfl) ⟨287277, by rfl⟩ : syracuseStep 766073 = 574555) B574555
theorem B569551 : Blo 503794 569551 := bstep (se 1 (by rfl) ⟨427163, by rfl⟩ : syracuseStep 569551 = 854327) B854327
theorem B3289369 : Blo 503794 3289369 := bstep (se 2 (by rfl) ⟨1233513, by rfl⟩ : syracuseStep 3289369 = 2467027) B2467027
theorem B504367 : Blo 503794 504367 := bstep (se 1 (by rfl) ⟨378275, by rfl⟩ : syracuseStep 504367 = 756551) B756551
theorem B504647 : Blo 503794 504647 := bstep (se 1 (by rfl) ⟨378485, by rfl⟩ : syracuseStep 504647 = 756971) B756971
theorem B504799 : Blo 503794 504799 := bstep (se 1 (by rfl) ⟨378599, by rfl⟩ : syracuseStep 504799 = 757199) B757199
theorem B3879935 : Blo 503794 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B570415 : Blo 503794 570415 := bstep (se 1 (by rfl) ⟨427811, by rfl⟩ : syracuseStep 570415 = 855623) B855623
theorem B504943 : Blo 503794 504943 := bstep (se 1 (by rfl) ⟨378707, by rfl⟩ : syracuseStep 504943 = 757415) B757415
theorem B504991 : Blo 503794 504991 := bstep (se 1 (by rfl) ⟨378743, by rfl⟩ : syracuseStep 504991 = 757487) B757487
theorem B505055 : Blo 503794 505055 := bstep (se 1 (by rfl) ⟨378791, by rfl⟩ : syracuseStep 505055 = 757583) B757583
theorem B505115 : Blo 503794 505115 := bstep (se 1 (by rfl) ⟨378836, by rfl⟩ : syracuseStep 505115 = 757673) B757673
theorem B505375 : Blo 503794 505375 := bstep (se 1 (by rfl) ⟨379031, by rfl⟩ : syracuseStep 505375 = 758063) B758063
theorem B505535 : Blo 503794 505535 := bstep (se 1 (by rfl) ⟨379151, by rfl⟩ : syracuseStep 505535 = 758303) B758303
theorem B1914779 : Blo 503794 1914779 := bstep (se 1 (by rfl) ⟨1436084, by rfl⟩ : syracuseStep 1914779 = 2872169) B2872169
theorem B9254897 : Blo 503794 9254897 := bstep (se 2 (by rfl) ⟨3470586, by rfl⟩ : syracuseStep 9254897 = 6941173) B6941173
theorem B6666259 : Blo 503794 6666259 := bstep (se 1 (by rfl) ⟨4999694, by rfl⟩ : syracuseStep 6666259 = 9999389) B9999389
theorem B506107 : Blo 503794 506107 := bstep (se 1 (by rfl) ⟨379580, by rfl⟩ : syracuseStep 506107 = 759161) B759161
theorem B1620287 : Blo 503794 1620287 := bstep (se 1 (by rfl) ⟨1215215, by rfl⟩ : syracuseStep 1620287 = 2430431) B2430431
theorem B768359 : Blo 503794 768359 := bstep (se 1 (by rfl) ⟨576269, by rfl⟩ : syracuseStep 768359 = 1152539) B1152539
theorem B1817257 : Blo 503794 1817257 := bstep (se 2 (by rfl) ⟨681471, by rfl⟩ : syracuseStep 1817257 = 1362943) B1362943
theorem B3849119 : Blo 503794 3849119 := bstep (se 1 (by rfl) ⟨2886839, by rfl⟩ : syracuseStep 3849119 = 5773679) B5773679
theorem B507599 : Blo 503794 507599 := bstep (se 1 (by rfl) ⟨380699, by rfl⟩ : syracuseStep 507599 = 761399) B761399
theorem B507647 : Blo 503794 507647 := bstep (se 1 (by rfl) ⟨380735, by rfl⟩ : syracuseStep 507647 = 761471) B761471
theorem B507711 : Blo 503794 507711 := bstep (se 1 (by rfl) ⟨380783, by rfl⟩ : syracuseStep 507711 = 761567) B761567
theorem B1916891 : Blo 503794 1916891 := bstep (se 1 (by rfl) ⟨1437668, by rfl⟩ : syracuseStep 1916891 = 2875337) B2875337
theorem B24985907 : Blo 503794 24985907 := bstep (se 1 (by rfl) ⟨18739430, by rfl⟩ : syracuseStep 24985907 = 37478861) B37478861
theorem B1917695 : Blo 503794 1917695 := bstep (se 1 (by rfl) ⟨1438271, by rfl⟩ : syracuseStep 1917695 = 2876543) B2876543
theorem B3851063 : Blo 503794 3851063 := bstep (se 1 (by rfl) ⟨2888297, by rfl⟩ : syracuseStep 3851063 = 5776595) B5776595
theorem B4146461 : Blo 503794 4146461 := bstep (se 3 (by rfl) ⟨777461, by rfl⟩ : syracuseStep 4146461 = 1554923) B1554923
theorem B640487 : Blo 503794 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B14633081 : Blo 503794 14633081 := bstep (se 2 (by rfl) ⟨5487405, by rfl⟩ : syracuseStep 14633081 = 10974811) B10974811
theorem B15550649 : Blo 503794 15550649 := bstep (se 2 (by rfl) ⟨5831493, by rfl⟩ : syracuseStep 15550649 = 11662987) B11662987
theorem B9718481 : Blo 503794 9718481 := bstep (se 2 (by rfl) ⟨3644430, by rfl⟩ : syracuseStep 9718481 = 7288861) B7288861
theorem B7392059 : Blo 503794 7392059 := bstep (se 1 (by rfl) ⟨5544044, by rfl⟩ : syracuseStep 7392059 = 11088089) B11088089
theorem B9719027 : Blo 503794 9719027 := bstep (se 1 (by rfl) ⟨7289270, by rfl⟩ : syracuseStep 9719027 = 14578541) B14578541
theorem B1756669 : Blo 503794 1756669 := bstep (se 3 (by rfl) ⟨329375, by rfl⟩ : syracuseStep 1756669 = 658751) B658751
theorem B511655 : Blo 503794 511655 := bstep (se 1 (by rfl) ⟨383741, by rfl⟩ : syracuseStep 511655 = 767483) B767483
theorem B1134287 : Blo 503794 1134287 := bstep (se 1 (by rfl) ⟨850715, by rfl⟩ : syracuseStep 1134287 = 1701431) B1701431
theorem B807337 : Blo 503794 807337 := bstep (se 2 (by rfl) ⟨302751, by rfl⟩ : syracuseStep 807337 = 605503) B605503
theorem B3232295 : Blo 503794 3232295 := bstep (se 1 (by rfl) ⟨2424221, by rfl⟩ : syracuseStep 3232295 = 4848443) B4848443
theorem B3232523 : Blo 503794 3232523 := bstep (se 1 (by rfl) ⟨2424392, by rfl⟩ : syracuseStep 3232523 = 4848785) B4848785
theorem B11654113 : Blo 503794 11654113 := bstep (se 2 (by rfl) ⟨4370292, by rfl⟩ : syracuseStep 11654113 = 8740585) B8740585
theorem B5559833 : Blo 503794 5559833 := bstep (se 2 (by rfl) ⟨2084937, by rfl⟩ : syracuseStep 5559833 = 4169875) B4169875
theorem B2774825 : Blo 503794 2774825 := bstep (se 2 (by rfl) ⟨1040559, by rfl⟩ : syracuseStep 2774825 = 2081119) B2081119
theorem B7297289 : Blo 503794 7297289 := bstep (se 2 (by rfl) ⟨2736483, by rfl⟩ : syracuseStep 7297289 = 5472967) B5472967
theorem B3234779 : Blo 503794 3234779 := bstep (se 1 (by rfl) ⟨2426084, by rfl⟩ : syracuseStep 3234779 = 4852169) B4852169
theorem B1924955 : Blo 503794 1924955 := bstep (se 1 (by rfl) ⟨1443716, by rfl⟩ : syracuseStep 1924955 = 2887433) B2887433
theorem B5857231 : Blo 503794 5857231 := bstep (se 1 (by rfl) ⟨4392923, by rfl⟩ : syracuseStep 5857231 = 8785847) B8785847
theorem B2875769 : Blo 503794 2875769 := bstep (se 2 (by rfl) ⟨1078413, by rfl⟩ : syracuseStep 2875769 = 2156827) B2156827
theorem B7758443 : Blo 503794 7758443 := bstep (se 1 (by rfl) ⟨5818832, by rfl⟩ : syracuseStep 7758443 = 11637665) B11637665
theorem B2057683 : Blo 503794 2057683 := bstep (se 1 (by rfl) ⟨1543262, by rfl⟩ : syracuseStep 2057683 = 3086525) B3086525
theorem B812539 : Blo 503794 812539 := bstep (se 1 (by rfl) ⟨609404, by rfl⟩ : syracuseStep 812539 = 1218809) B1218809
theorem B5760557 : Blo 503794 5760557 := bstep (se 3 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 5760557 = 2160209) B2160209
theorem B2877727 : Blo 503794 2877727 := bstep (se 1 (by rfl) ⟨2158295, by rfl⟩ : syracuseStep 2877727 = 4316591) B4316591
theorem B1927583 : Blo 503794 1927583 := bstep (se 1 (by rfl) ⟨1445687, by rfl⟩ : syracuseStep 1927583 = 2891375) B2891375
theorem B1141163 : Blo 503794 1141163 := bstep (se 1 (by rfl) ⟨855872, by rfl⟩ : syracuseStep 1141163 = 1711745) B1711745
theorem B3238879 : Blo 503794 3238879 := bstep (se 1 (by rfl) ⟨2429159, by rfl⟩ : syracuseStep 3238879 = 4858319) B4858319
theorem B36925307 : Blo 503794 36925307 := bstep (se 1 (by rfl) ⟨27693980, by rfl⟩ : syracuseStep 36925307 = 55387961) B55387961
theorem B15560747 : Blo 503794 15560747 := bstep (se 1 (by rfl) ⟨11670560, by rfl⟩ : syracuseStep 15560747 = 23341121) B23341121
theorem B2880143 : Blo 503794 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B5206781 : Blo 503794 5206781 := bstep (se 3 (by rfl) ⟨976271, by rfl⟩ : syracuseStep 5206781 = 1952543) B1952543
theorem B1700729 : Blo 503794 1700729 := bstep (se 2 (by rfl) ⟨637773, by rfl⟩ : syracuseStep 1700729 = 1275547) B1275547
theorem B3831623 : Blo 503794 3831623 := bstep (se 1 (by rfl) ⟨2873717, by rfl⟩ : syracuseStep 3831623 = 5747435) B5747435
theorem B1210727 : Blo 503794 1210727 := bstep (se 1 (by rfl) ⟨908045, by rfl⟩ : syracuseStep 1210727 = 1816091) B1816091
theorem B2881919 : Blo 503794 2881919 := bstep (se 1 (by rfl) ⟨2161439, by rfl⟩ : syracuseStep 2881919 = 4322879) B4322879
theorem B2882375 : Blo 503794 2882375 := bstep (se 1 (by rfl) ⟨2161781, by rfl⟩ : syracuseStep 2882375 = 4323563) B4323563
theorem B1702889 : Blo 503794 1702889 := bstep (se 2 (by rfl) ⟨638583, by rfl⟩ : syracuseStep 1702889 = 1277167) B1277167
theorem B3636359 : Blo 503794 3636359 := bstep (se 1 (by rfl) ⟨2727269, by rfl⟩ : syracuseStep 3636359 = 5454539) B5454539
theorem B721391 : Blo 503794 721391 := bstep (se 1 (by rfl) ⟨541043, by rfl⟩ : syracuseStep 721391 = 1082087) B1082087
theorem B1278463 : Blo 503794 1278463 := bstep (se 1 (by rfl) ⟨958847, by rfl⟩ : syracuseStep 1278463 = 1917695) B1917695
theorem B1442407 : Blo 503794 1442407 := bstep (se 1 (by rfl) ⟨1081805, by rfl⟩ : syracuseStep 1442407 = 2163611) B2163611
theorem B1705427 : Blo 503794 1705427 := bstep (se 1 (by rfl) ⟨1279070, by rfl⟩ : syracuseStep 1705427 = 2558141) B2558141
theorem B1443511 : Blo 503794 1443511 := bstep (se 1 (by rfl) ⟨1082633, by rfl⟩ : syracuseStep 1443511 = 2165267) B2165267
theorem B1083385 : Blo 503794 1083385 := bstep (se 2 (by rfl) ⟨406269, by rfl⟩ : syracuseStep 1083385 = 812539) B812539
theorem B756191 : Blo 503794 756191 := bstep (se 1 (by rfl) ⟨567143, by rfl⟩ : syracuseStep 756191 = 1134287) B1134287
theorem B1280569 : Blo 503794 1280569 := bstep (se 2 (by rfl) ⟨480213, by rfl⟩ : syracuseStep 1280569 = 960427) B960427
theorem B1706777 : Blo 503794 1706777 := bstep (se 2 (by rfl) ⟨640041, by rfl⟩ : syracuseStep 1706777 = 1280083) B1280083
theorem B4328315 : Blo 503794 4328315 := bstep (se 1 (by rfl) ⟨3246236, by rfl⟩ : syracuseStep 4328315 = 6492473) B6492473
theorem B3836969 : Blo 503794 3836969 := bstep (se 2 (by rfl) ⟨1438863, by rfl⟩ : syracuseStep 3836969 = 2877727) B2877727
theorem B2428163 : Blo 503794 2428163 := bstep (se 1 (by rfl) ⟨1821122, by rfl⟩ : syracuseStep 2428163 = 3642245) B3642245
theorem B3706555 : Blo 503794 3706555 := bstep (se 1 (by rfl) ⟨2779916, by rfl⟩ : syracuseStep 3706555 = 5559833) B5559833
theorem B1707965 : Blo 503794 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B1283303 : Blo 503794 1283303 := bstep (se 1 (by rfl) ⟨962477, by rfl⟩ : syracuseStep 1283303 = 1924955) B1924955
theorem B759401 : Blo 503794 759401 := bstep (se 2 (by rfl) ⟨284775, by rfl⟩ : syracuseStep 759401 = 569551) B569551
theorem B3086063 : Blo 503794 3086063 := bstep (se 1 (by rfl) ⟨2314547, by rfl⟩ : syracuseStep 3086063 = 4629095) B4629095
theorem B3840371 : Blo 503794 3840371 := bstep (se 1 (by rfl) ⟨2880278, by rfl⟩ : syracuseStep 3840371 = 5760557) B5760557
theorem B15538817 : Blo 503794 15538817 := bstep (se 2 (by rfl) ⟨5827056, by rfl⟩ : syracuseStep 15538817 = 11654113) B11654113
theorem B760553 : Blo 503794 760553 := bstep (se 2 (by rfl) ⟨285207, by rfl⟩ : syracuseStep 760553 = 570415) B570415
theorem B1285055 : Blo 503794 1285055 := bstep (se 1 (by rfl) ⟨963791, by rfl⟩ : syracuseStep 1285055 = 1927583) B1927583
theorem B760775 : Blo 503794 760775 := bstep (se 1 (by rfl) ⟨570581, by rfl⟩ : syracuseStep 760775 = 1141163) B1141163
theorem B1711799 : Blo 503794 1711799 := bstep (se 1 (by rfl) ⟨1283849, by rfl⟩ : syracuseStep 1711799 = 2567699) B2567699
theorem B24616871 : Blo 503794 24616871 := bstep (se 1 (by rfl) ⟨18462653, by rfl⟩ : syracuseStep 24616871 = 36925307) B36925307
theorem B8888345 : Blo 503794 8888345 := bstep (se 2 (by rfl) ⟨3333129, by rfl⟩ : syracuseStep 8888345 = 6666259) B6666259
theorem B6169931 : Blo 503794 6169931 := bstep (se 1 (by rfl) ⟨4627448, by rfl⟩ : syracuseStep 6169931 = 9254897) B9254897
theorem B2566079 : Blo 503794 2566079 := bstep (se 1 (by rfl) ⟨1924559, by rfl⟩ : syracuseStep 2566079 = 3849119) B3849119
theorem B7809641 : Blo 503794 7809641 := bstep (se 2 (by rfl) ⟨2928615, by rfl⟩ : syracuseStep 7809641 = 5857231) B5857231
theorem B568039 : Blo 503794 568039 := bstep (se 1 (by rfl) ⟨426029, by rfl⟩ : syracuseStep 568039 = 852059) B852059
theorem B16657271 : Blo 503794 16657271 := bstep (se 1 (by rfl) ⟨12492953, by rfl⟩ : syracuseStep 16657271 = 24985907) B24985907
theorem B961627 : Blo 503794 961627 := bstep (se 1 (by rfl) ⟨721220, by rfl⟩ : syracuseStep 961627 = 1442441) B1442441
theorem B2567375 : Blo 503794 2567375 := bstep (se 1 (by rfl) ⟨1925531, by rfl⟩ : syracuseStep 2567375 = 3851063) B3851063
theorem B2731421 : Blo 503794 2731421 := bstep (se 3 (by rfl) ⟨512141, by rfl⟩ : syracuseStep 2731421 = 1024283) B1024283
theorem B2764307 : Blo 503794 2764307 := bstep (se 1 (by rfl) ⟨2073230, by rfl⟩ : syracuseStep 2764307 = 4146461) B4146461
theorem B10367099 : Blo 503794 10367099 := bstep (se 1 (by rfl) ⟨7775324, by rfl⟩ : syracuseStep 10367099 = 15550649) B15550649
theorem B503999 : Blo 503794 503999 := bstep (se 1 (by rfl) ⟨377999, by rfl⟩ : syracuseStep 503999 = 755999) B755999
theorem B504047 : Blo 503794 504047 := bstep (se 1 (by rfl) ⟨378035, by rfl⟩ : syracuseStep 504047 = 756071) B756071
theorem B20689181 : Blo 503794 20689181 := bstep (se 3 (by rfl) ⟨3879221, by rfl⟩ : syracuseStep 20689181 = 7758443) B7758443
theorem B504295 : Blo 503794 504295 := bstep (se 1 (by rfl) ⟨378221, by rfl⟩ : syracuseStep 504295 = 756443) B756443
theorem B504319 : Blo 503794 504319 := bstep (se 1 (by rfl) ⟨378239, by rfl⟩ : syracuseStep 504319 = 756479) B756479
theorem B4928039 : Blo 503794 4928039 := bstep (se 1 (by rfl) ⟨3696029, by rfl⟩ : syracuseStep 4928039 = 7392059) B7392059
theorem B570559 : Blo 503794 570559 := bstep (se 1 (by rfl) ⟨427919, by rfl⟩ : syracuseStep 570559 = 855839) B855839
theorem B505135 : Blo 503794 505135 := bstep (se 1 (by rfl) ⟨378851, by rfl⟩ : syracuseStep 505135 = 757703) B757703
theorem B505447 : Blo 503794 505447 := bstep (se 1 (by rfl) ⟨379085, by rfl⟩ : syracuseStep 505447 = 758171) B758171
theorem B1947311 : Blo 503794 1947311 := bstep (se 1 (by rfl) ⟨1460483, by rfl⟩ : syracuseStep 1947311 = 2920967) B2920967
theorem B505575 : Blo 503794 505575 := bstep (se 1 (by rfl) ⟨379181, by rfl⟩ : syracuseStep 505575 = 758363) B758363
theorem B505823 : Blo 503794 505823 := bstep (se 1 (by rfl) ⟨379367, by rfl⟩ : syracuseStep 505823 = 758735) B758735
theorem B505887 : Blo 503794 505887 := bstep (se 1 (by rfl) ⟨379415, by rfl⟩ : syracuseStep 505887 = 758831) B758831
theorem B506023 : Blo 503794 506023 := bstep (se 1 (by rfl) ⟨379517, by rfl⟩ : syracuseStep 506023 = 759035) B759035
theorem B1849883 : Blo 503794 1849883 := bstep (se 1 (by rfl) ⟨1387412, by rfl⟩ : syracuseStep 1849883 = 2774825) B2774825
theorem B506479 : Blo 503794 506479 := bstep (se 1 (by rfl) ⟨379859, by rfl⟩ : syracuseStep 506479 = 759719) B759719
theorem B4864859 : Blo 503794 4864859 := bstep (se 1 (by rfl) ⟨3648644, by rfl⟩ : syracuseStep 4864859 = 7297289) B7297289
theorem B506875 : Blo 503794 506875 := bstep (se 1 (by rfl) ⟨380156, by rfl⟩ : syracuseStep 506875 = 760313) B760313
theorem B638047 : Blo 503794 638047 := bstep (se 1 (by rfl) ⟨478535, by rfl⟩ : syracuseStep 638047 = 957071) B957071
theorem B507071 : Blo 503794 507071 := bstep (se 1 (by rfl) ⟨380303, by rfl⟩ : syracuseStep 507071 = 760607) B760607
theorem B2342225 : Blo 503794 2342225 := bstep (se 2 (by rfl) ⟨878334, by rfl⟩ : syracuseStep 2342225 = 1756669) B1756669
theorem B507551 : Blo 503794 507551 := bstep (se 1 (by rfl) ⟨380663, by rfl⟩ : syracuseStep 507551 = 761327) B761327
theorem B1917179 : Blo 503794 1917179 := bstep (se 1 (by rfl) ⟨1437884, by rfl⟩ : syracuseStep 1917179 = 2875769) B2875769
theorem B3228605 : Blo 503794 3228605 := bstep (se 3 (by rfl) ⟨605363, by rfl⟩ : syracuseStep 3228605 = 1210727) B1210727
theorem B10373831 : Blo 503794 10373831 := bstep (se 1 (by rfl) ⟨7780373, by rfl⟩ : syracuseStep 10373831 = 15560747) B15560747
theorem B510715 : Blo 503794 510715 := bstep (se 1 (by rfl) ⟨383036, by rfl⟩ : syracuseStep 510715 = 766073) B766073
theorem B1920095 : Blo 503794 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B1133819 : Blo 503794 1133819 := bstep (se 1 (by rfl) ⟨850364, by rfl⟩ : syracuseStep 1133819 = 1700729) B1700729
theorem B10407649 : Blo 503794 10407649 := bstep (se 2 (by rfl) ⟨3902868, by rfl⟩ : syracuseStep 10407649 = 7805737) B7805737
theorem B3854465 : Blo 503794 3854465 := bstep (se 2 (by rfl) ⟨1445424, by rfl⟩ : syracuseStep 3854465 = 2890849) B2890849
theorem B512239 : Blo 503794 512239 := bstep (se 1 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 512239 = 768359) B768359
theorem B1921279 : Blo 503794 1921279 := bstep (se 1 (by rfl) ⟨1440959, by rfl⟩ : syracuseStep 1921279 = 2881919) B2881919
theorem B1364413 : Blo 503794 1364413 := bstep (se 3 (by rfl) ⟨255827, by rfl⟩ : syracuseStep 1364413 = 511655) B511655
theorem B1921583 : Blo 503794 1921583 := bstep (se 1 (by rfl) ⟨1441187, by rfl⟩ : syracuseStep 1921583 = 2882375) B2882375
theorem B1135259 : Blo 503794 1135259 := bstep (se 1 (by rfl) ⟨851444, by rfl⟩ : syracuseStep 1135259 = 1702889) B1702889
theorem B1136303 : Blo 503794 1136303 := bstep (se 1 (by rfl) ⟨852227, by rfl⟩ : syracuseStep 1136303 = 1704455) B1704455
theorem B8608031 : Blo 503794 8608031 := bstep (se 1 (by rfl) ⟨6456023, by rfl⟩ : syracuseStep 8608031 = 12912047) B12912047
theorem B9755387 : Blo 503794 9755387 := bstep (se 1 (by rfl) ⟨7316540, by rfl⟩ : syracuseStep 9755387 = 14633081) B14633081
theorem B9264235 : Blo 503794 9264235 := bstep (se 1 (by rfl) ⟨6948176, by rfl⟩ : syracuseStep 9264235 = 13896353) B13896353
theorem B6478987 : Blo 503794 6478987 := bstep (se 1 (by rfl) ⟨4859240, by rfl⟩ : syracuseStep 6478987 = 9718481) B9718481
theorem B2743577 : Blo 503794 2743577 := bstep (se 2 (by rfl) ⟨1028841, by rfl⟩ : syracuseStep 2743577 = 2057683) B2057683
theorem B6479351 : Blo 503794 6479351 := bstep (se 1 (by rfl) ⟨4859513, by rfl⟩ : syracuseStep 6479351 = 9719027) B9719027
theorem B1924985 : Blo 503794 1924985 := bstep (se 2 (by rfl) ⟨721869, by rfl⟩ : syracuseStep 1924985 = 1443739) B1443739
theorem B1138751 : Blo 503794 1138751 := bstep (se 1 (by rfl) ⟨854063, by rfl⟩ : syracuseStep 1138751 = 1708127) B1708127
theorem B2154863 : Blo 503794 2154863 := bstep (se 1 (by rfl) ⟨1616147, by rfl⟩ : syracuseStep 2154863 = 3232295) B3232295
theorem B2155015 : Blo 503794 2155015 := bstep (se 1 (by rfl) ⟨1616261, by rfl⟩ : syracuseStep 2155015 = 3232523) B3232523
theorem B1139291 : Blo 503794 1139291 := bstep (se 1 (by rfl) ⟨854468, by rfl⟩ : syracuseStep 1139291 = 1708937) B1708937
theorem B1139849 : Blo 503794 1139849 := bstep (se 2 (by rfl) ⟨427443, by rfl⟩ : syracuseStep 1139849 = 854887) B854887
theorem B1139867 : Blo 503794 1139867 := bstep (se 1 (by rfl) ⟨854900, by rfl⟩ : syracuseStep 1139867 = 1709801) B1709801
theorem B1139903 : Blo 503794 1139903 := bstep (se 1 (by rfl) ⟨854927, by rfl⟩ : syracuseStep 1139903 = 1709855) B1709855
theorem B4318505 : Blo 503794 4318505 := bstep (se 2 (by rfl) ⟨1619439, by rfl⟩ : syracuseStep 4318505 = 3238879) B3238879
theorem B1140623 : Blo 503794 1140623 := bstep (se 1 (by rfl) ⟨855467, by rfl⟩ : syracuseStep 1140623 = 1710935) B1710935
theorem B2156519 : Blo 503794 2156519 := bstep (se 1 (by rfl) ⟨1617389, by rfl⟩ : syracuseStep 2156519 = 3234779) B3234779
theorem B8218655 : Blo 503794 8218655 := bstep (se 1 (by rfl) ⟨6163991, by rfl⟩ : syracuseStep 8218655 = 12327983) B12327983
theorem B4876463 : Blo 503794 4876463 := bstep (se 1 (by rfl) ⟨3657347, by rfl⟩ : syracuseStep 4876463 = 7314695) B7314695
theorem B1141019 : Blo 503794 1141019 := bstep (se 1 (by rfl) ⟨855764, by rfl⟩ : syracuseStep 1141019 = 1711529) B1711529
theorem B1076159 : Blo 503794 1076159 := bstep (se 1 (by rfl) ⟨807119, by rfl⟩ : syracuseStep 1076159 = 1614239) B1614239
theorem B1141703 : Blo 503794 1141703 := bstep (se 1 (by rfl) ⟨856277, by rfl⟩ : syracuseStep 1141703 = 1712555) B1712555
theorem B4385825 : Blo 503794 4385825 := bstep (se 2 (by rfl) ⟨1644684, by rfl⟩ : syracuseStep 4385825 = 3289369) B3289369
theorem B12938291 : Blo 503794 12938291 := bstep (se 1 (by rfl) ⟨9703718, by rfl⟩ : syracuseStep 12938291 = 19407437) B19407437
theorem B1076449 : Blo 503794 1076449 := bstep (se 2 (by rfl) ⟨403668, by rfl⟩ : syracuseStep 1076449 = 807337) B807337
theorem B1142495 : Blo 503794 1142495 := bstep (se 1 (by rfl) ⟨856871, by rfl⟩ : syracuseStep 1142495 = 1713743) B1713743
theorem B1077295 : Blo 503794 1077295 := bstep (se 1 (by rfl) ⟨807971, by rfl⟩ : syracuseStep 1077295 = 1615943) B1615943
theorem B3471187 : Blo 503794 3471187 := bstep (se 1 (by rfl) ⟨2603390, by rfl⟩ : syracuseStep 3471187 = 5206781) B5206781
theorem B2586623 : Blo 503794 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B2423009 : Blo 503794 2423009 := bstep (se 2 (by rfl) ⟨908628, by rfl⟩ : syracuseStep 2423009 = 1817257) B1817257
theorem B2554415 : Blo 503794 2554415 := bstep (se 1 (by rfl) ⟨1915811, by rfl⟩ : syracuseStep 2554415 = 3831623) B3831623
theorem B1276519 : Blo 503794 1276519 := bstep (se 1 (by rfl) ⟨957389, by rfl⟩ : syracuseStep 1276519 = 1914779) B1914779
theorem B1080191 : Blo 503794 1080191 := bstep (se 1 (by rfl) ⟨810143, by rfl⟩ : syracuseStep 1080191 = 1620287) B1620287
theorem B2424239 : Blo 503794 2424239 := bstep (se 1 (by rfl) ⟨1818179, by rfl⟩ : syracuseStep 2424239 = 3636359) B3636359
theorem B1277927 : Blo 503794 1277927 := bstep (se 1 (by rfl) ⟨958445, by rfl⟩ : syracuseStep 1277927 = 1916891) B1916891
theorem B1278119 : Blo 503794 1278119 := bstep (se 1 (by rfl) ⟨958589, by rfl⟩ : syracuseStep 1278119 = 1917179) B1917179
theorem B1704617 : Blo 503794 1704617 := bstep (se 2 (by rfl) ⟨639231, by rfl⟩ : syracuseStep 1704617 = 1278463) B1278463
theorem B6915887 : Blo 503794 6915887 := bstep (se 1 (by rfl) ⟨5186915, by rfl⟩ : syracuseStep 6915887 = 10373831) B10373831
theorem B2885543 : Blo 503794 2885543 := bstep (se 1 (by rfl) ⟨2164157, by rfl⟩ : syracuseStep 2885543 = 4328315) B4328315
theorem B2557979 : Blo 503794 2557979 := bstep (se 1 (by rfl) ⟨1918484, by rfl⟩ : syracuseStep 2557979 = 3836969) B3836969
theorem B1280063 : Blo 503794 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B755879 : Blo 503794 755879 := bstep (se 1 (by rfl) ⟨566909, by rfl⟩ : syracuseStep 755879 = 1133819) B1133819
theorem B1281055 : Blo 503794 1281055 := bstep (se 1 (by rfl) ⟨960791, by rfl⟩ : syracuseStep 1281055 = 1921583) B1921583
theorem B756839 : Blo 503794 756839 := bstep (se 1 (by rfl) ⟨567629, by rfl⟩ : syracuseStep 756839 = 1135259) B1135259
theorem B1707425 : Blo 503794 1707425 := bstep (se 2 (by rfl) ⟨640284, by rfl⟩ : syracuseStep 1707425 = 1280569) B1280569
theorem B855535 : Blo 503794 855535 := bstep (se 1 (by rfl) ⟨641651, by rfl⟩ : syracuseStep 855535 = 1283303) B1283303
theorem B757385 : Blo 503794 757385 := bstep (se 2 (by rfl) ⟨284019, by rfl⟩ : syracuseStep 757385 = 568039) B568039
theorem B757535 : Blo 503794 757535 := bstep (se 1 (by rfl) ⟨568151, by rfl⟩ : syracuseStep 757535 = 1136303) B1136303
theorem B1282169 : Blo 503794 1282169 := bstep (se 2 (by rfl) ⟨480813, by rfl⟩ : syracuseStep 1282169 = 961627) B961627
theorem B5738687 : Blo 503794 5738687 := bstep (se 1 (by rfl) ⟨4304015, by rfl⟩ : syracuseStep 5738687 = 8608031) B8608031
theorem B2560247 : Blo 503794 2560247 := bstep (se 1 (by rfl) ⟨1920185, by rfl⟩ : syracuseStep 2560247 = 3840371) B3840371
theorem B10359211 : Blo 503794 10359211 := bstep (se 1 (by rfl) ⟨7769408, by rfl⟩ : syracuseStep 10359211 = 15538817) B15538817
theorem B856703 : Blo 503794 856703 := bstep (se 1 (by rfl) ⟨642527, by rfl⟩ : syracuseStep 856703 = 1285055) B1285055
theorem B1283323 : Blo 503794 1283323 := bstep (se 1 (by rfl) ⟨962492, by rfl⟩ : syracuseStep 1283323 = 1924985) B1924985
theorem B759167 : Blo 503794 759167 := bstep (se 1 (by rfl) ⟨569375, by rfl⟩ : syracuseStep 759167 = 1138751) B1138751
theorem B19732085 : Blo 503794 19732085 := bstep (se 5 (by rfl) ⟨924941, by rfl⟩ : syracuseStep 19732085 = 1849883) B1849883
theorem B2561705 : Blo 503794 2561705 := bstep (se 2 (by rfl) ⟨960639, by rfl⟩ : syracuseStep 2561705 = 1921279) B1921279
theorem B759527 : Blo 503794 759527 := bstep (se 1 (by rfl) ⟨569645, by rfl⟩ : syracuseStep 759527 = 1139291) B1139291
theorem B759899 : Blo 503794 759899 := bstep (se 1 (by rfl) ⟨569924, by rfl⟩ : syracuseStep 759899 = 1139849) B1139849
theorem B759911 : Blo 503794 759911 := bstep (se 1 (by rfl) ⟨569933, by rfl⟩ : syracuseStep 759911 = 1139867) B1139867
theorem B759935 : Blo 503794 759935 := bstep (se 1 (by rfl) ⟨569951, by rfl⟩ : syracuseStep 759935 = 1139903) B1139903
theorem B760415 : Blo 503794 760415 := bstep (se 1 (by rfl) ⟨570311, by rfl⟩ : syracuseStep 760415 = 1140623) B1140623
theorem B1710719 : Blo 503794 1710719 := bstep (se 1 (by rfl) ⟨1283039, by rfl⟩ : syracuseStep 1710719 = 2566079) B2566079
theorem B5479103 : Blo 503794 5479103 := bstep (se 1 (by rfl) ⟨4109327, by rfl⟩ : syracuseStep 5479103 = 8218655) B8218655
theorem B760679 : Blo 503794 760679 := bstep (se 1 (by rfl) ⟨570509, by rfl⟩ : syracuseStep 760679 = 1141019) B1141019
theorem B760745 : Blo 503794 760745 := bstep (se 2 (by rfl) ⟨285279, by rfl⟩ : syracuseStep 760745 = 570559) B570559
theorem B761135 : Blo 503794 761135 := bstep (se 1 (by rfl) ⟨570851, by rfl⟩ : syracuseStep 761135 = 1141703) B1141703
theorem B2923883 : Blo 503794 2923883 := bstep (se 1 (by rfl) ⟨2192912, by rfl⟩ : syracuseStep 2923883 = 4385825) B4385825
theorem B8625527 : Blo 503794 8625527 := bstep (se 1 (by rfl) ⟨6469145, by rfl⟩ : syracuseStep 8625527 = 12938291) B12938291
theorem B1711583 : Blo 503794 1711583 := bstep (se 1 (by rfl) ⟨1283687, by rfl⟩ : syracuseStep 1711583 = 2567375) B2567375
theorem B1842871 : Blo 503794 1842871 := bstep (se 1 (by rfl) ⟨1382153, by rfl⟩ : syracuseStep 1842871 = 2764307) B2764307
theorem B4628249 : Blo 503794 4628249 := bstep (se 2 (by rfl) ⟨1735593, by rfl⟩ : syracuseStep 4628249 = 3471187) B3471187
theorem B761663 : Blo 503794 761663 := bstep (se 1 (by rfl) ⟨571247, by rfl⟩ : syracuseStep 761663 = 1142495) B1142495
theorem B3285359 : Blo 503794 3285359 := bstep (se 1 (by rfl) ⟨2464019, by rfl⟩ : syracuseStep 3285359 = 4928039) B4928039
theorem B7283789 : Blo 503794 7283789 := bstep (se 3 (by rfl) ⟨1365710, by rfl⟩ : syracuseStep 7283789 = 2731421) B2731421
theorem B1615339 : Blo 503794 1615339 := bstep (se 1 (by rfl) ⟨1211504, by rfl⟩ : syracuseStep 1615339 = 2423009) B2423009
theorem B1616159 : Blo 503794 1616159 := bstep (se 1 (by rfl) ⟨1212119, by rfl⟩ : syracuseStep 1616159 = 2424239) B2424239
theorem B5778053 : Blo 503794 5778053 := bstep (se 4 (by rfl) ⟨541692, by rfl⟩ : syracuseStep 5778053 = 1083385) B1083385
theorem B504127 : Blo 503794 504127 := bstep (se 1 (by rfl) ⟨378095, by rfl⟩ : syracuseStep 504127 = 756191) B756191
theorem B1618775 : Blo 503794 1618775 := bstep (se 1 (by rfl) ⟨1214081, by rfl⟩ : syracuseStep 1618775 = 2428163) B2428163
theorem B2569643 : Blo 503794 2569643 := bstep (se 1 (by rfl) ⟨1927232, by rfl⟩ : syracuseStep 2569643 = 3854465) B3854465
theorem B506267 : Blo 503794 506267 := bstep (se 1 (by rfl) ⟨379700, by rfl⟩ : syracuseStep 506267 = 759401) B759401
theorem B507035 : Blo 503794 507035 := bstep (se 1 (by rfl) ⟨380276, by rfl⟩ : syracuseStep 507035 = 760553) B760553
theorem B6503591 : Blo 503794 6503591 := bstep (se 1 (by rfl) ⟨4877693, by rfl⟩ : syracuseStep 6503591 = 9755387) B9755387
theorem B507183 : Blo 503794 507183 := bstep (se 1 (by rfl) ⟨380387, by rfl⟩ : syracuseStep 507183 = 760775) B760775
theorem B13876865 : Blo 503794 13876865 := bstep (se 2 (by rfl) ⟨5203824, by rfl⟩ : syracuseStep 13876865 = 10407649) B10407649
theorem B1819217 : Blo 503794 1819217 := bstep (se 2 (by rfl) ⟨682206, by rfl⟩ : syracuseStep 1819217 = 1364413) B1364413
theorem B4113287 : Blo 503794 4113287 := bstep (se 1 (by rfl) ⟨3084965, by rfl⟩ : syracuseStep 4113287 = 6169931) B6169931
theorem B1298207 : Blo 503794 1298207 := bstep (se 1 (by rfl) ⟨973655, by rfl⟩ : syracuseStep 1298207 = 1947311) B1947311
theorem B8638649 : Blo 503794 8638649 := bstep (se 2 (by rfl) ⟨3239493, by rfl⟩ : syracuseStep 8638649 = 6478987) B6478987
theorem B1561483 : Blo 503794 1561483 := bstep (se 1 (by rfl) ⟨1171112, by rfl⟩ : syracuseStep 1561483 = 2342225) B2342225
theorem B2152403 : Blo 503794 2152403 := bstep (se 1 (by rfl) ⟨1614302, by rfl⟩ : syracuseStep 2152403 = 3228605) B3228605
theorem B2873353 : Blo 503794 2873353 := bstep (se 2 (by rfl) ⟨1077507, by rfl⟩ : syracuseStep 2873353 = 2155015) B2155015
theorem B1923209 : Blo 503794 1923209 := bstep (se 2 (by rfl) ⟨721203, by rfl⟩ : syracuseStep 1923209 = 1442407) B1442407
theorem B1136951 : Blo 503794 1136951 := bstep (se 1 (by rfl) ⟨852713, by rfl⟩ : syracuseStep 1136951 = 1705427) B1705427
theorem B1923709 : Blo 503794 1923709 := bstep (se 3 (by rfl) ⟨360695, by rfl⟩ : syracuseStep 1923709 = 721391) B721391
theorem B1137851 : Blo 503794 1137851 := bstep (se 1 (by rfl) ⟨853388, by rfl⟩ : syracuseStep 1137851 = 1706777) B1706777
theorem B1924681 : Blo 503794 1924681 := bstep (se 2 (by rfl) ⟨721755, by rfl⟩ : syracuseStep 1924681 = 1443511) B1443511
theorem B1138643 : Blo 503794 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B680953 : Blo 503794 680953 := bstep (se 2 (by rfl) ⟨255357, by rfl⟩ : syracuseStep 680953 = 510715) B510715
theorem B2057375 : Blo 503794 2057375 := bstep (se 1 (by rfl) ⟨1543031, by rfl⟩ : syracuseStep 2057375 = 3086063) B3086063
theorem B1435265 : Blo 503794 1435265 := bstep (se 2 (by rfl) ⟨538224, by rfl⟩ : syracuseStep 1435265 = 1076449) B1076449
theorem B1829051 : Blo 503794 1829051 := bstep (se 1 (by rfl) ⟨1371788, by rfl⟩ : syracuseStep 1829051 = 2743577) B2743577
theorem B4942073 : Blo 503794 4942073 := bstep (se 2 (by rfl) ⟨1853277, by rfl⟩ : syracuseStep 4942073 = 3706555) B3706555
theorem B4319567 : Blo 503794 4319567 := bstep (se 1 (by rfl) ⟨3239675, by rfl⟩ : syracuseStep 4319567 = 6479351) B6479351
theorem B1141199 : Blo 503794 1141199 := bstep (se 1 (by rfl) ⟨855899, by rfl⟩ : syracuseStep 1141199 = 1711799) B1711799
theorem B16411247 : Blo 503794 16411247 := bstep (se 1 (by rfl) ⟨12308435, by rfl⟩ : syracuseStep 16411247 = 24616871) B24616871
theorem B5925563 : Blo 503794 5925563 := bstep (se 1 (by rfl) ⟨4444172, by rfl⟩ : syracuseStep 5925563 = 8888345) B8888345
theorem B1436393 : Blo 503794 1436393 := bstep (se 2 (by rfl) ⟨538647, by rfl⟩ : syracuseStep 1436393 = 1077295) B1077295
theorem B1436575 : Blo 503794 1436575 := bstep (se 1 (by rfl) ⟨1077431, by rfl⟩ : syracuseStep 1436575 = 2154863) B2154863
theorem B682985 : Blo 503794 682985 := bstep (se 2 (by rfl) ⟨256119, by rfl⟩ : syracuseStep 682985 = 512239) B512239
theorem B13003901 : Blo 503794 13003901 := bstep (se 3 (by rfl) ⟨2438231, by rfl⟩ : syracuseStep 13003901 = 4876463) B4876463
theorem B2879003 : Blo 503794 2879003 := bstep (se 1 (by rfl) ⟨2159252, by rfl⟩ : syracuseStep 2879003 = 4318505) B4318505
theorem B1437679 : Blo 503794 1437679 := bstep (se 1 (by rfl) ⟨1078259, by rfl⟩ : syracuseStep 1437679 = 2156519) B2156519
theorem B5206427 : Blo 503794 5206427 := bstep (se 1 (by rfl) ⟨3904820, by rfl⟩ : syracuseStep 5206427 = 7809641) B7809641
theorem B11104847 : Blo 503794 11104847 := bstep (se 1 (by rfl) ⟨8328635, by rfl⟩ : syracuseStep 11104847 = 16657271) B16657271
theorem B717439 : Blo 503794 717439 := bstep (se 1 (by rfl) ⟨538079, by rfl⟩ : syracuseStep 717439 = 1076159) B1076159
theorem B6911399 : Blo 503794 6911399 := bstep (se 1 (by rfl) ⟨5183549, by rfl⟩ : syracuseStep 6911399 = 10367099) B10367099
theorem B13792787 : Blo 503794 13792787 := bstep (se 1 (by rfl) ⟨10344590, by rfl⟩ : syracuseStep 13792787 = 20689181) B20689181
theorem B1702025 : Blo 503794 1702025 := bstep (se 2 (by rfl) ⟨638259, by rfl⟩ : syracuseStep 1702025 = 1276519) B1276519
theorem B850729 : Blo 503794 850729 := bstep (se 2 (by rfl) ⟨319023, by rfl⟩ : syracuseStep 850729 = 638047) B638047
theorem B12352313 : Blo 503794 12352313 := bstep (se 2 (by rfl) ⟨4632117, by rfl⟩ : syracuseStep 12352313 = 9264235) B9264235
theorem B1702943 : Blo 503794 1702943 := bstep (se 1 (by rfl) ⟨1277207, by rfl⟩ : syracuseStep 1702943 = 2554415) B2554415
theorem B3243239 : Blo 503794 3243239 := bstep (se 1 (by rfl) ⟨2432429, by rfl⟩ : syracuseStep 3243239 = 4864859) B4864859
theorem B720127 : Blo 503794 720127 := bstep (se 1 (by rfl) ⟨540095, by rfl⟩ : syracuseStep 720127 = 1080191) B1080191
theorem B851951 : Blo 503794 851951 := bstep (se 1 (by rfl) ⟨638963, by rfl⟩ : syracuseStep 851951 = 1277927) B1277927
theorem B27590645 : Blo 503794 27590645 := bstep (se 5 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 27590645 = 2586623) B2586623
theorem B852079 : Blo 503794 852079 := bstep (se 1 (by rfl) ⟨639059, by rfl⟩ : syracuseStep 852079 = 1278119) B1278119
theorem B1705319 : Blo 503794 1705319 := bstep (se 1 (by rfl) ⟨1278989, by rfl⟩ : syracuseStep 1705319 = 2557979) B2557979
theorem B853375 : Blo 503794 853375 := bstep (se 1 (by rfl) ⟨640031, by rfl⟩ : syracuseStep 853375 = 1280063) B1280063
theorem B4851245 : Blo 503794 4851245 := bstep (se 3 (by rfl) ⟨909608, by rfl⟩ : syracuseStep 4851245 = 1819217) B1819217
theorem B854779 : Blo 503794 854779 := bstep (se 1 (by rfl) ⟨641084, by rfl⟩ : syracuseStep 854779 = 1282169) B1282169
theorem B1706831 : Blo 503794 1706831 := bstep (se 1 (by rfl) ⟨1280123, by rfl⟩ : syracuseStep 1706831 = 2560247) B2560247
theorem B1707803 : Blo 503794 1707803 := bstep (se 1 (by rfl) ⟨1280852, by rfl⟩ : syracuseStep 1707803 = 2561705) B2561705
theorem B1708073 : Blo 503794 1708073 := bstep (se 2 (by rfl) ⟨640527, by rfl⟩ : syracuseStep 1708073 = 1281055) B1281055
theorem B1282139 : Blo 503794 1282139 := bstep (se 1 (by rfl) ⟨961604, by rfl⟩ : syracuseStep 1282139 = 1923209) B1923209
theorem B757967 : Blo 503794 757967 := bstep (se 1 (by rfl) ⟨568475, by rfl⟩ : syracuseStep 757967 = 1136951) B1136951
theorem B8327909 : Blo 503794 8327909 := bstep (se 4 (by rfl) ⟨780741, by rfl⟩ : syracuseStep 8327909 = 1561483) B1561483
theorem B758567 : Blo 503794 758567 := bstep (se 1 (by rfl) ⟨568925, by rfl⟩ : syracuseStep 758567 = 1137851) B1137851
theorem B3085499 : Blo 503794 3085499 := bstep (se 1 (by rfl) ⟨2314124, by rfl⟩ : syracuseStep 3085499 = 4628249) B4628249
theorem B759095 : Blo 503794 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B4855859 : Blo 503794 4855859 := bstep (se 1 (by rfl) ⟨3641894, by rfl⟩ : syracuseStep 4855859 = 7283789) B7283789
theorem B956585 : Blo 503794 956585 := bstep (se 2 (by rfl) ⟨358719, by rfl⟩ : syracuseStep 956585 = 717439) B717439
theorem B956843 : Blo 503794 956843 := bstep (se 1 (by rfl) ⟨717632, by rfl⟩ : syracuseStep 956843 = 1435265) B1435265
theorem B1219367 : Blo 503794 1219367 := bstep (se 1 (by rfl) ⟨914525, by rfl⟩ : syracuseStep 1219367 = 1829051) B1829051
theorem B760799 : Blo 503794 760799 := bstep (se 1 (by rfl) ⟨570599, by rfl⟩ : syracuseStep 760799 = 1141199) B1141199
theorem B1711097 : Blo 503794 1711097 := bstep (se 2 (by rfl) ⟨641661, by rfl⟩ : syracuseStep 1711097 = 1283323) B1283323
theorem B957595 : Blo 503794 957595 := bstep (se 1 (by rfl) ⟨718196, by rfl⟩ : syracuseStep 957595 = 1436393) B1436393
theorem B2564945 : Blo 503794 2564945 := bstep (se 2 (by rfl) ⟨961854, by rfl⟩ : syracuseStep 2564945 = 1923709) B1923709
theorem B1713095 : Blo 503794 1713095 := bstep (se 1 (by rfl) ⟨1284821, by rfl⟩ : syracuseStep 1713095 = 2569643) B2569643
theorem B960169 : Blo 503794 960169 := bstep (se 2 (by rfl) ⟨360063, by rfl⟩ : syracuseStep 960169 = 720127) B720127
theorem B8234875 : Blo 503794 8234875 := bstep (se 1 (by rfl) ⟨6176156, by rfl⟩ : syracuseStep 8234875 = 12352313) B12352313
theorem B2566241 : Blo 503794 2566241 := bstep (se 2 (by rfl) ⟨962340, by rfl⟩ : syracuseStep 2566241 = 1924681) B1924681
theorem B4335727 : Blo 503794 4335727 := bstep (se 1 (by rfl) ⟨3251795, by rfl⟩ : syracuseStep 4335727 = 6503591) B6503591
theorem B9251243 : Blo 503794 9251243 := bstep (se 1 (by rfl) ⟨6938432, by rfl⟩ : syracuseStep 9251243 = 13876865) B13876865
theorem B567967 : Blo 503794 567967 := bstep (se 1 (by rfl) ⟨425975, by rfl⟩ : syracuseStep 567967 = 851951) B851951
theorem B18393763 : Blo 503794 18393763 := bstep (se 1 (by rfl) ⟨13795322, by rfl⟩ : syracuseStep 18393763 = 27590645) B27590645
theorem B503919 : Blo 503794 503919 := bstep (se 1 (by rfl) ⟨377939, by rfl⟩ : syracuseStep 503919 = 755879) B755879
theorem B504559 : Blo 503794 504559 := bstep (se 1 (by rfl) ⟨378419, by rfl⟩ : syracuseStep 504559 = 756839) B756839
theorem B504923 : Blo 503794 504923 := bstep (se 1 (by rfl) ⟨378692, by rfl⟩ : syracuseStep 504923 = 757385) B757385
theorem B505023 : Blo 503794 505023 := bstep (se 1 (by rfl) ⟨378767, by rfl⟩ : syracuseStep 505023 = 757535) B757535
theorem B571135 : Blo 503794 571135 := bstep (se 1 (by rfl) ⟨428351, by rfl⟩ : syracuseStep 571135 = 856703) B856703
theorem B506111 : Blo 503794 506111 := bstep (se 1 (by rfl) ⟨379583, by rfl⟩ : syracuseStep 506111 = 759167) B759167
theorem B13154723 : Blo 503794 13154723 := bstep (se 1 (by rfl) ⟨9866042, by rfl⟩ : syracuseStep 13154723 = 19732085) B19732085
theorem B506351 : Blo 503794 506351 := bstep (se 1 (by rfl) ⟨379763, by rfl⟩ : syracuseStep 506351 = 759527) B759527
theorem B1915433 : Blo 503794 1915433 := bstep (se 2 (by rfl) ⟨718287, by rfl⟩ : syracuseStep 1915433 = 1436575) B1436575
theorem B506599 : Blo 503794 506599 := bstep (se 1 (by rfl) ⟨379949, by rfl⟩ : syracuseStep 506599 = 759899) B759899
theorem B506607 : Blo 503794 506607 := bstep (se 1 (by rfl) ⟨379955, by rfl⟩ : syracuseStep 506607 = 759911) B759911
theorem B506623 : Blo 503794 506623 := bstep (se 1 (by rfl) ⟨379967, by rfl⟩ : syracuseStep 506623 = 759935) B759935
theorem B506943 : Blo 503794 506943 := bstep (se 1 (by rfl) ⟨380207, by rfl⟩ : syracuseStep 506943 = 760415) B760415
theorem B3652735 : Blo 503794 3652735 := bstep (se 1 (by rfl) ⟨2739551, by rfl⟩ : syracuseStep 3652735 = 5479103) B5479103
theorem B507119 : Blo 503794 507119 := bstep (se 1 (by rfl) ⟨380339, by rfl⟩ : syracuseStep 507119 = 760679) B760679
theorem B507163 : Blo 503794 507163 := bstep (se 1 (by rfl) ⟨380372, by rfl⟩ : syracuseStep 507163 = 760745) B760745
theorem B507423 : Blo 503794 507423 := bstep (se 1 (by rfl) ⟨380567, by rfl⟩ : syracuseStep 507423 = 761135) B761135
theorem B1949255 : Blo 503794 1949255 := bstep (se 1 (by rfl) ⟨1461941, by rfl⟩ : syracuseStep 1949255 = 2923883) B2923883
theorem B5750351 : Blo 503794 5750351 := bstep (se 1 (by rfl) ⟨4312763, by rfl⟩ : syracuseStep 5750351 = 8625527) B8625527
theorem B507775 : Blo 503794 507775 := bstep (se 1 (by rfl) ⟨380831, by rfl⟩ : syracuseStep 507775 = 761663) B761663
theorem B1916905 : Blo 503794 1916905 := bstep (se 2 (by rfl) ⟨718839, by rfl⟩ : syracuseStep 1916905 = 1437679) B1437679
theorem B13812281 : Blo 503794 13812281 := bstep (se 2 (by rfl) ⟨5179605, by rfl⟩ : syracuseStep 13812281 = 10359211) B10359211
theorem B4309757 : Blo 503794 4309757 := bstep (se 3 (by rfl) ⟨808079, by rfl⟩ : syracuseStep 4309757 = 1616159) B1616159
theorem B3294715 : Blo 503794 3294715 := bstep (se 1 (by rfl) ⟨2471036, by rfl⟩ : syracuseStep 3294715 = 4942073) B4942073
theorem B3852035 : Blo 503794 3852035 := bstep (se 1 (by rfl) ⟨2889026, by rfl⟩ : syracuseStep 3852035 = 5778053) B5778053
theorem B3950375 : Blo 503794 3950375 := bstep (se 1 (by rfl) ⟨2962781, by rfl⟩ : syracuseStep 3950375 = 5925563) B5925563
theorem B8669267 : Blo 503794 8669267 := bstep (se 1 (by rfl) ⟨6501950, by rfl⟩ : syracuseStep 8669267 = 13003901) B13003901
theorem B1919335 : Blo 503794 1919335 := bstep (se 1 (by rfl) ⟨1439501, by rfl⟩ : syracuseStep 1919335 = 2879003) B2879003
theorem B1821293 : Blo 503794 1821293 := bstep (se 3 (by rfl) ⟨341492, by rfl⟩ : syracuseStep 1821293 = 682985) B682985
theorem B4607599 : Blo 503794 4607599 := bstep (se 1 (by rfl) ⟨3455699, by rfl⟩ : syracuseStep 4607599 = 6911399) B6911399
theorem B9195191 : Blo 503794 9195191 := bstep (se 1 (by rfl) ⟨6896393, by rfl⟩ : syracuseStep 9195191 = 13792787) B13792787
theorem B1134305 : Blo 503794 1134305 := bstep (se 2 (by rfl) ⟨425364, by rfl⟩ : syracuseStep 1134305 = 850729) B850729
theorem B1134683 : Blo 503794 1134683 := bstep (se 1 (by rfl) ⟨851012, by rfl⟩ : syracuseStep 1134683 = 1702025) B1702025
theorem B1135295 : Blo 503794 1135295 := bstep (se 1 (by rfl) ⟨851471, by rfl⟩ : syracuseStep 1135295 = 1702943) B1702943
theorem B3461885 : Blo 503794 3461885 := bstep (se 3 (by rfl) ⟨649103, by rfl⟩ : syracuseStep 3461885 = 1298207) B1298207
theorem B1136411 : Blo 503794 1136411 := bstep (se 1 (by rfl) ⟨852308, by rfl⟩ : syracuseStep 1136411 = 1704617) B1704617
theorem B2742191 : Blo 503794 2742191 := bstep (se 1 (by rfl) ⟨2056643, by rfl⟩ : syracuseStep 2742191 = 4113287) B4113287
theorem B4610591 : Blo 503794 4610591 := bstep (se 1 (by rfl) ⟨3457943, by rfl⟩ : syracuseStep 4610591 = 6915887) B6915887
theorem B1923695 : Blo 503794 1923695 := bstep (se 1 (by rfl) ⟨1442771, by rfl⟩ : syracuseStep 1923695 = 2885543) B2885543
theorem B907937 : Blo 503794 907937 := bstep (se 2 (by rfl) ⟨340476, by rfl⟩ : syracuseStep 907937 = 680953) B680953
theorem B2153785 : Blo 503794 2153785 := bstep (se 2 (by rfl) ⟨807669, by rfl⟩ : syracuseStep 2153785 = 1615339) B1615339
theorem B1138283 : Blo 503794 1138283 := bstep (se 1 (by rfl) ⟨853712, by rfl⟩ : syracuseStep 1138283 = 1707425) B1707425
theorem B5759099 : Blo 503794 5759099 := bstep (se 1 (by rfl) ⟨4319324, by rfl⟩ : syracuseStep 5759099 = 8638649) B8638649
theorem B3825791 : Blo 503794 3825791 := bstep (se 1 (by rfl) ⟨2869343, by rfl⟩ : syracuseStep 3825791 = 5738687) B5738687
theorem B1434935 : Blo 503794 1434935 := bstep (se 1 (by rfl) ⟨1076201, by rfl⟩ : syracuseStep 1434935 = 2152403) B2152403
theorem B1140479 : Blo 503794 1140479 := bstep (se 1 (by rfl) ⟨855359, by rfl⟩ : syracuseStep 1140479 = 1710719) B1710719
theorem B1140713 : Blo 503794 1140713 := bstep (se 2 (by rfl) ⟨427767, by rfl⟩ : syracuseStep 1140713 = 855535) B855535
theorem B1141055 : Blo 503794 1141055 := bstep (se 1 (by rfl) ⟨855791, by rfl⟩ : syracuseStep 1141055 = 1711583) B1711583
theorem B2190239 : Blo 503794 2190239 := bstep (se 1 (by rfl) ⟨1642679, by rfl⟩ : syracuseStep 2190239 = 3285359) B3285359
theorem B1371583 : Blo 503794 1371583 := bstep (se 1 (by rfl) ⟨1028687, by rfl⟩ : syracuseStep 1371583 = 2057375) B2057375
theorem B2879711 : Blo 503794 2879711 := bstep (se 1 (by rfl) ⟨2159783, by rfl⟩ : syracuseStep 2879711 = 4319567) B4319567
theorem B10940831 : Blo 503794 10940831 := bstep (se 1 (by rfl) ⟨8205623, by rfl⟩ : syracuseStep 10940831 = 16411247) B16411247
theorem B3831137 : Blo 503794 3831137 := bstep (se 2 (by rfl) ⟨1436676, by rfl⟩ : syracuseStep 3831137 = 2873353) B2873353
theorem B3470951 : Blo 503794 3470951 := bstep (se 1 (by rfl) ⟨2603213, by rfl⟩ : syracuseStep 3470951 = 5206427) B5206427
theorem B7403231 : Blo 503794 7403231 := bstep (se 1 (by rfl) ⟨5552423, by rfl⟩ : syracuseStep 7403231 = 11104847) B11104847
theorem B1079183 : Blo 503794 1079183 := bstep (se 1 (by rfl) ⟨809387, by rfl⟩ : syracuseStep 1079183 = 1618775) B1618775
theorem B2162159 : Blo 503794 2162159 := bstep (se 1 (by rfl) ⟨1621619, by rfl⟩ : syracuseStep 2162159 = 3243239) B3243239
theorem B2457161 : Blo 503794 2457161 := bstep (se 2 (by rfl) ⟨921435, by rfl⟩ : syracuseStep 2457161 = 1842871) B1842871
theorem B9208187 : Blo 503794 9208187 := bstep (se 1 (by rfl) ⟨6906140, by rfl⟩ : syracuseStep 9208187 = 13812281) B13812281
theorem B1214195 : Blo 503794 1214195 := bstep (se 1 (by rfl) ⟨910646, by rfl⟩ : syracuseStep 1214195 = 1821293) B1821293
theorem B4392953 : Blo 503794 4392953 := bstep (se 2 (by rfl) ⟨1647357, by rfl⟩ : syracuseStep 4392953 = 3294715) B3294715
theorem B1280225 : Blo 503794 1280225 := bstep (se 2 (by rfl) ⟨480084, by rfl⟩ : syracuseStep 1280225 = 960169) B960169
theorem B6130127 : Blo 503794 6130127 := bstep (se 1 (by rfl) ⟨4597595, by rfl⟩ : syracuseStep 6130127 = 9195191) B9195191
theorem B756203 : Blo 503794 756203 := bstep (se 1 (by rfl) ⟨567152, by rfl⟩ : syracuseStep 756203 = 1134305) B1134305
theorem B10979833 : Blo 503794 10979833 := bstep (se 2 (by rfl) ⟨4117437, by rfl⟩ : syracuseStep 10979833 = 8234875) B8234875
theorem B756455 : Blo 503794 756455 := bstep (se 1 (by rfl) ⟨567341, by rfl⟩ : syracuseStep 756455 = 1134683) B1134683
theorem B854759 : Blo 503794 854759 := bstep (se 1 (by rfl) ⟨641069, by rfl⟩ : syracuseStep 854759 = 1282139) B1282139
theorem B756863 : Blo 503794 756863 := bstep (se 1 (by rfl) ⟨567647, by rfl⟩ : syracuseStep 756863 = 1135295) B1135295
theorem B2559113 : Blo 503794 2559113 := bstep (se 2 (by rfl) ⟨959667, by rfl⟩ : syracuseStep 2559113 = 1919335) B1919335
theorem B757289 : Blo 503794 757289 := bstep (se 2 (by rfl) ⟨283983, by rfl⟩ : syracuseStep 757289 = 567967) B567967
theorem B757607 : Blo 503794 757607 := bstep (se 1 (by rfl) ⟨568205, by rfl⟩ : syracuseStep 757607 = 1136411) B1136411
theorem B1282463 : Blo 503794 1282463 := bstep (se 1 (by rfl) ⟨961847, by rfl⟩ : syracuseStep 1282463 = 1923695) B1923695
theorem B758855 : Blo 503794 758855 := bstep (se 1 (by rfl) ⟨569141, by rfl⟩ : syracuseStep 758855 = 1138283) B1138283
theorem B3839399 : Blo 503794 3839399 := bstep (se 1 (by rfl) ⟨2879549, by rfl⟩ : syracuseStep 3839399 = 5759099) B5759099
theorem B1709963 : Blo 503794 1709963 := bstep (se 1 (by rfl) ⟨1282472, by rfl⟩ : syracuseStep 1709963 = 2564945) B2564945
theorem B956623 : Blo 503794 956623 := bstep (se 1 (by rfl) ⟨717467, by rfl⟩ : syracuseStep 956623 = 1434935) B1434935
theorem B760319 : Blo 503794 760319 := bstep (se 1 (by rfl) ⟨570239, by rfl⟩ : syracuseStep 760319 = 1140479) B1140479
theorem B760475 : Blo 503794 760475 := bstep (se 1 (by rfl) ⟨570356, by rfl⟩ : syracuseStep 760475 = 1140713) B1140713
theorem B1710827 : Blo 503794 1710827 := bstep (se 1 (by rfl) ⟨1283120, by rfl⟩ : syracuseStep 1710827 = 2566241) B2566241
theorem B760703 : Blo 503794 760703 := bstep (se 1 (by rfl) ⟨570527, by rfl⟩ : syracuseStep 760703 = 1141055) B1141055
theorem B6167495 : Blo 503794 6167495 := bstep (se 1 (by rfl) ⟨4625621, by rfl⟩ : syracuseStep 6167495 = 9251243) B9251243
theorem B761513 : Blo 503794 761513 := bstep (se 2 (by rfl) ⟨285567, by rfl⟩ : syracuseStep 761513 = 571135) B571135
theorem B2568023 : Blo 503794 2568023 := bstep (se 1 (by rfl) ⟨1926017, by rfl⟩ : syracuseStep 2568023 = 3852035) B3852035
theorem B5779511 : Blo 503794 5779511 := bstep (se 1 (by rfl) ⟨4334633, by rfl⟩ : syracuseStep 5779511 = 8669267) B8669267
theorem B505311 : Blo 503794 505311 := bstep (se 1 (by rfl) ⟨378983, by rfl⟩ : syracuseStep 505311 = 757967) B757967
theorem B5780969 : Blo 503794 5780969 := bstep (se 2 (by rfl) ⟨2167863, by rfl⟩ : syracuseStep 5780969 = 4335727) B4335727
theorem B5551939 : Blo 503794 5551939 := bstep (se 1 (by rfl) ⟨4163954, by rfl⟩ : syracuseStep 5551939 = 8327909) B8327909
theorem B2307923 : Blo 503794 2307923 := bstep (se 1 (by rfl) ⟨1730942, by rfl⟩ : syracuseStep 2307923 = 3461885) B3461885
theorem B505711 : Blo 503794 505711 := bstep (se 1 (by rfl) ⟨379283, by rfl⟩ : syracuseStep 505711 = 758567) B758567
theorem B506063 : Blo 503794 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B24525017 : Blo 503794 24525017 := bstep (se 2 (by rfl) ⟨9196881, by rfl⟩ : syracuseStep 24525017 = 18393763) B18393763
theorem B637723 : Blo 503794 637723 := bstep (se 1 (by rfl) ⟨478292, by rfl⟩ : syracuseStep 637723 = 956585) B956585
theorem B637895 : Blo 503794 637895 := bstep (se 1 (by rfl) ⟨478421, by rfl⟩ : syracuseStep 637895 = 956843) B956843
theorem B605291 : Blo 503794 605291 := bstep (se 1 (by rfl) ⟨453968, by rfl⟩ : syracuseStep 605291 = 907937) B907937
theorem B507199 : Blo 503794 507199 := bstep (se 1 (by rfl) ⟨380399, by rfl⟩ : syracuseStep 507199 = 760799) B760799
theorem B6143465 : Blo 503794 6143465 := bstep (se 2 (by rfl) ⟨2303799, by rfl⟩ : syracuseStep 6143465 = 4607599) B4607599
theorem B1460159 : Blo 503794 1460159 := bstep (se 1 (by rfl) ⟨1095119, by rfl⟩ : syracuseStep 1460159 = 2190239) B2190239
theorem B1919807 : Blo 503794 1919807 := bstep (se 1 (by rfl) ⟨1439855, by rfl⟩ : syracuseStep 1919807 = 2879711) B2879711
theorem B7293887 : Blo 503794 7293887 := bstep (se 1 (by rfl) ⟨5470415, by rfl⟩ : syracuseStep 7293887 = 10940831) B10940831
theorem B2313967 : Blo 503794 2313967 := bstep (se 1 (by rfl) ⟨1735475, by rfl⟩ : syracuseStep 2313967 = 3470951) B3470951
theorem B4935487 : Blo 503794 4935487 := bstep (se 1 (by rfl) ⟨3701615, by rfl⟩ : syracuseStep 4935487 = 7403231) B7403231
theorem B4870313 : Blo 503794 4870313 := bstep (se 2 (by rfl) ⟨1826367, by rfl⟩ : syracuseStep 4870313 = 3652735) B3652735
theorem B8769815 : Blo 503794 8769815 := bstep (se 1 (by rfl) ⟨6577361, by rfl⟩ : syracuseStep 8769815 = 13154723) B13154723
theorem B2871713 : Blo 503794 2871713 := bstep (se 2 (by rfl) ⟨1076892, by rfl⟩ : syracuseStep 2871713 = 2153785) B2153785
theorem B1299503 : Blo 503794 1299503 := bstep (se 1 (by rfl) ⟨974627, by rfl⟩ : syracuseStep 1299503 = 1949255) B1949255
theorem B1136105 : Blo 503794 1136105 := bstep (se 2 (by rfl) ⟨426039, by rfl⟩ : syracuseStep 1136105 = 852079) B852079
theorem B2873171 : Blo 503794 2873171 := bstep (se 1 (by rfl) ⟨2154878, by rfl⟩ : syracuseStep 2873171 = 4309757) B4309757
theorem B1136879 : Blo 503794 1136879 := bstep (se 1 (by rfl) ⟨852659, by rfl⟩ : syracuseStep 1136879 = 1705319) B1705319
theorem B3234163 : Blo 503794 3234163 := bstep (se 1 (by rfl) ⟨2425622, by rfl⟩ : syracuseStep 3234163 = 4851245) B4851245
theorem B1137833 : Blo 503794 1137833 := bstep (se 2 (by rfl) ⟨426687, by rfl⟩ : syracuseStep 1137833 = 853375) B853375
theorem B1137887 : Blo 503794 1137887 := bstep (se 1 (by rfl) ⟨853415, by rfl⟩ : syracuseStep 1137887 = 1706831) B1706831
theorem B1138535 : Blo 503794 1138535 := bstep (se 1 (by rfl) ⟨853901, by rfl⟩ : syracuseStep 1138535 = 1707803) B1707803
theorem B1138715 : Blo 503794 1138715 := bstep (se 1 (by rfl) ⟨854036, by rfl⟩ : syracuseStep 1138715 = 1708073) B1708073
theorem B2056999 : Blo 503794 2056999 := bstep (se 1 (by rfl) ⟨1542749, by rfl⟩ : syracuseStep 2056999 = 3085499) B3085499
theorem B1139705 : Blo 503794 1139705 := bstep (se 2 (by rfl) ⟨427389, by rfl⟩ : syracuseStep 1139705 = 854779) B854779
theorem B1828127 : Blo 503794 1828127 := bstep (se 1 (by rfl) ⟨1371095, by rfl⟩ : syracuseStep 1828127 = 2742191) B2742191
theorem B3237239 : Blo 503794 3237239 := bstep (se 1 (by rfl) ⟨2427929, by rfl⟩ : syracuseStep 3237239 = 4855859) B4855859
theorem B3073727 : Blo 503794 3073727 := bstep (se 1 (by rfl) ⟨2305295, by rfl⟩ : syracuseStep 3073727 = 4610591) B4610591
theorem B812911 : Blo 503794 812911 := bstep (se 1 (by rfl) ⟨609683, by rfl⟩ : syracuseStep 812911 = 1219367) B1219367
theorem B1828777 : Blo 503794 1828777 := bstep (se 2 (by rfl) ⟨685791, by rfl⟩ : syracuseStep 1828777 = 1371583) B1371583
theorem B1140731 : Blo 503794 1140731 := bstep (se 1 (by rfl) ⟨855548, by rfl⟩ : syracuseStep 1140731 = 1711097) B1711097
theorem B2550527 : Blo 503794 2550527 := bstep (se 1 (by rfl) ⟨1912895, by rfl⟩ : syracuseStep 2550527 = 3825791) B3825791
theorem B1142063 : Blo 503794 1142063 := bstep (se 1 (by rfl) ⟨856547, by rfl⟩ : syracuseStep 1142063 = 1713095) B1713095
theorem B42137333 : Blo 503794 42137333 := bstep (se 5 (by rfl) ⟨1975187, by rfl⟩ : syracuseStep 42137333 = 3950375) B3950375
theorem B2554091 : Blo 503794 2554091 := bstep (se 1 (by rfl) ⟨1915568, by rfl⟩ : syracuseStep 2554091 = 3831137) B3831137
theorem B719455 : Blo 503794 719455 := bstep (se 1 (by rfl) ⟨539591, by rfl⟩ : syracuseStep 719455 = 1079183) B1079183
theorem B1276793 : Blo 503794 1276793 := bstep (se 2 (by rfl) ⟨478797, by rfl⟩ : syracuseStep 1276793 = 957595) B957595
theorem B1276955 : Blo 503794 1276955 := bstep (se 1 (by rfl) ⟨957716, by rfl⟩ : syracuseStep 1276955 = 1915433) B1915433
theorem B1441439 : Blo 503794 1441439 := bstep (se 1 (by rfl) ⟨1081079, by rfl⟩ : syracuseStep 1441439 = 2162159) B2162159
theorem B1638107 : Blo 503794 1638107 := bstep (se 1 (by rfl) ⟨1228580, by rfl⟩ : syracuseStep 1638107 = 2457161) B2457161
theorem B3833567 : Blo 503794 3833567 := bstep (se 1 (by rfl) ⟨2875175, by rfl⟩ : syracuseStep 3833567 = 5750351) B5750351
theorem B2555873 : Blo 503794 2555873 := bstep (se 2 (by rfl) ⟨958452, by rfl⟩ : syracuseStep 2555873 = 1916905) B1916905
theorem B853483 : Blo 503794 853483 := bstep (se 1 (by rfl) ⟨640112, by rfl⟩ : syracuseStep 853483 = 1280225) B1280225
theorem B1279871 : Blo 503794 1279871 := bstep (se 1 (by rfl) ⟨959903, by rfl⟩ : syracuseStep 1279871 = 1919807) B1919807
theorem B1706075 : Blo 503794 1706075 := bstep (se 1 (by rfl) ⟨1279556, by rfl⟩ : syracuseStep 1706075 = 2559113) B2559113
theorem B1083881 : Blo 503794 1083881 := bstep (se 2 (by rfl) ⟨406455, by rfl⟩ : syracuseStep 1083881 = 812911) B812911
theorem B3246875 : Blo 503794 3246875 := bstep (se 1 (by rfl) ⟨2435156, by rfl⟩ : syracuseStep 3246875 = 4870313) B4870313
theorem B854975 : Blo 503794 854975 := bstep (se 1 (by rfl) ⟨641231, by rfl⟩ : syracuseStep 854975 = 1282463) B1282463
theorem B2559599 : Blo 503794 2559599 := bstep (se 1 (by rfl) ⟨1919699, by rfl⟩ : syracuseStep 2559599 = 3839399) B3839399
theorem B757403 : Blo 503794 757403 := bstep (se 1 (by rfl) ⟨568052, by rfl⟩ : syracuseStep 757403 = 1136105) B1136105
theorem B757919 : Blo 503794 757919 := bstep (se 1 (by rfl) ⟨568439, by rfl⟩ : syracuseStep 757919 = 1136879) B1136879
theorem B758555 : Blo 503794 758555 := bstep (se 1 (by rfl) ⟨568916, by rfl⟩ : syracuseStep 758555 = 1137833) B1137833
theorem B758591 : Blo 503794 758591 := bstep (se 1 (by rfl) ⟨568943, by rfl⟩ : syracuseStep 758591 = 1137887) B1137887
theorem B3085289 : Blo 503794 3085289 := bstep (se 2 (by rfl) ⟨1156983, by rfl⟩ : syracuseStep 3085289 = 2313967) B2313967
theorem B759023 : Blo 503794 759023 := bstep (se 1 (by rfl) ⟨569267, by rfl⟩ : syracuseStep 759023 = 1138535) B1138535
theorem B759143 : Blo 503794 759143 := bstep (se 1 (by rfl) ⟨569357, by rfl⟩ : syracuseStep 759143 = 1138715) B1138715
theorem B759803 : Blo 503794 759803 := bstep (se 1 (by rfl) ⟨569852, by rfl⟩ : syracuseStep 759803 = 1139705) B1139705
theorem B760487 : Blo 503794 760487 := bstep (se 1 (by rfl) ⟨570365, by rfl⟩ : syracuseStep 760487 = 1140731) B1140731
theorem B761375 : Blo 503794 761375 := bstep (se 1 (by rfl) ⟨571031, by rfl⟩ : syracuseStep 761375 = 1142063) B1142063
theorem B12951413 : Blo 503794 12951413 := bstep (se 5 (by rfl) ⟨607097, by rfl⟩ : syracuseStep 12951413 = 1214195) B1214195
theorem B1712015 : Blo 503794 1712015 := bstep (se 1 (by rfl) ⟨1284011, by rfl⟩ : syracuseStep 1712015 = 2568023) B2568023
theorem B1614109 : Blo 503794 1614109 := bstep (se 3 (by rfl) ⟨302645, by rfl⟩ : syracuseStep 1614109 = 605291) B605291
theorem B959273 : Blo 503794 959273 := bstep (se 2 (by rfl) ⟨359727, by rfl⟩ : syracuseStep 959273 = 719455) B719455
theorem B28091555 : Blo 503794 28091555 := bstep (se 1 (by rfl) ⟨21068666, by rfl⟩ : syracuseStep 28091555 = 42137333) B42137333
theorem B960959 : Blo 503794 960959 := bstep (se 1 (by rfl) ⟨720719, by rfl⟩ : syracuseStep 960959 = 1441439) B1441439
theorem B1092071 : Blo 503794 1092071 := bstep (se 1 (by rfl) ⟨819053, by rfl⟩ : syracuseStep 1092071 = 1638107) B1638107
theorem B6138791 : Blo 503794 6138791 := bstep (se 1 (by rfl) ⟨4604093, by rfl⟩ : syracuseStep 6138791 = 9208187) B9208187
theorem B2928635 : Blo 503794 2928635 := bstep (se 1 (by rfl) ⟨2196476, by rfl⟩ : syracuseStep 2928635 = 4392953) B4392953
theorem B504135 : Blo 503794 504135 := bstep (se 1 (by rfl) ⟨378101, by rfl⟩ : syracuseStep 504135 = 756203) B756203
theorem B504303 : Blo 503794 504303 := bstep (se 1 (by rfl) ⟨378227, by rfl⟩ : syracuseStep 504303 = 756455) B756455
theorem B569839 : Blo 503794 569839 := bstep (se 1 (by rfl) ⟨427379, by rfl⟩ : syracuseStep 569839 = 854759) B854759
theorem B4862591 : Blo 503794 4862591 := bstep (se 1 (by rfl) ⟨3646943, by rfl⟩ : syracuseStep 4862591 = 7293887) B7293887
theorem B504575 : Blo 503794 504575 := bstep (se 1 (by rfl) ⟨378431, by rfl⟩ : syracuseStep 504575 = 756863) B756863
theorem B504859 : Blo 503794 504859 := bstep (se 1 (by rfl) ⟨378644, by rfl⟩ : syracuseStep 504859 = 757289) B757289
theorem B2438369 : Blo 503794 2438369 := bstep (se 2 (by rfl) ⟨914388, by rfl⟩ : syracuseStep 2438369 = 1828777) B1828777
theorem B505071 : Blo 503794 505071 := bstep (se 1 (by rfl) ⟨378803, by rfl⟩ : syracuseStep 505071 = 757607) B757607
theorem B5846543 : Blo 503794 5846543 := bstep (se 1 (by rfl) ⟨4384907, by rfl⟩ : syracuseStep 5846543 = 8769815) B8769815
theorem B1914475 : Blo 503794 1914475 := bstep (se 1 (by rfl) ⟨1435856, by rfl⟩ : syracuseStep 1914475 = 2871713) B2871713
theorem B866335 : Blo 503794 866335 := bstep (se 1 (by rfl) ⟨649751, by rfl⟩ : syracuseStep 866335 = 1299503) B1299503
theorem B505903 : Blo 503794 505903 := bstep (se 1 (by rfl) ⟨379427, by rfl⟩ : syracuseStep 505903 = 758855) B758855
theorem B1915447 : Blo 503794 1915447 := bstep (se 1 (by rfl) ⟨1436585, by rfl⟩ : syracuseStep 1915447 = 2873171) B2873171
theorem B506879 : Blo 503794 506879 := bstep (se 1 (by rfl) ⟨380159, by rfl⟩ : syracuseStep 506879 = 760319) B760319
theorem B506983 : Blo 503794 506983 := bstep (se 1 (by rfl) ⟨380237, by rfl⟩ : syracuseStep 506983 = 760475) B760475
theorem B507135 : Blo 503794 507135 := bstep (se 1 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 507135 = 760703) B760703
theorem B4111663 : Blo 503794 4111663 := bstep (se 1 (by rfl) ⟨3083747, by rfl⟩ : syracuseStep 4111663 = 6167495) B6167495
theorem B507675 : Blo 503794 507675 := bstep (se 1 (by rfl) ⟨380756, by rfl⟩ : syracuseStep 507675 = 761513) B761513
theorem B2049151 : Blo 503794 2049151 := bstep (se 1 (by rfl) ⟨1536863, by rfl⟩ : syracuseStep 2049151 = 3073727) B3073727
theorem B3853007 : Blo 503794 3853007 := bstep (se 1 (by rfl) ⟨2889755, by rfl⟩ : syracuseStep 3853007 = 5779511) B5779511
theorem B4312217 : Blo 503794 4312217 := bstep (se 2 (by rfl) ⟨1617081, by rfl⟩ : syracuseStep 4312217 = 3234163) B3234163
theorem B3853979 : Blo 503794 3853979 := bstep (se 1 (by rfl) ⟨2890484, by rfl⟩ : syracuseStep 3853979 = 5780969) B5780969
theorem B2742665 : Blo 503794 2742665 := bstep (se 2 (by rfl) ⟨1028499, by rfl⟩ : syracuseStep 2742665 = 2056999) B2056999
theorem B973439 : Blo 503794 973439 := bstep (se 1 (by rfl) ⟨730079, by rfl⟩ : syracuseStep 973439 = 1460159) B1460159
theorem B14639777 : Blo 503794 14639777 := bstep (se 2 (by rfl) ⟨5489916, by rfl⟩ : syracuseStep 14639777 = 10979833) B10979833
theorem B4875005 : Blo 503794 4875005 := bstep (se 3 (by rfl) ⟨914063, by rfl⟩ : syracuseStep 4875005 = 1828127) B1828127
theorem B1139975 : Blo 503794 1139975 := bstep (se 1 (by rfl) ⟨854981, by rfl⟩ : syracuseStep 1139975 = 1709963) B1709963
theorem B1140551 : Blo 503794 1140551 := bstep (se 1 (by rfl) ⟨855413, by rfl⟩ : syracuseStep 1140551 = 1710827) B1710827
theorem B6580649 : Blo 503794 6580649 := bstep (se 2 (by rfl) ⟨2467743, by rfl⟩ : syracuseStep 6580649 = 4935487) B4935487
theorem B2158159 : Blo 503794 2158159 := bstep (se 1 (by rfl) ⟨1618619, by rfl⟩ : syracuseStep 2158159 = 3237239) B3237239
theorem B16347005 : Blo 503794 16347005 := bstep (se 3 (by rfl) ⟨3065063, by rfl⟩ : syracuseStep 16347005 = 6130127) B6130127
theorem B1700351 : Blo 503794 1700351 := bstep (se 1 (by rfl) ⟨1275263, by rfl⟩ : syracuseStep 1700351 = 2550527) B2550527
theorem B7402585 : Blo 503794 7402585 := bstep (se 2 (by rfl) ⟨2775969, by rfl⟩ : syracuseStep 7402585 = 5551939) B5551939
theorem B1701053 : Blo 503794 1701053 := bstep (se 3 (by rfl) ⟨318947, by rfl⟩ : syracuseStep 1701053 = 637895) B637895
theorem B1275497 : Blo 503794 1275497 := bstep (se 2 (by rfl) ⟨478311, by rfl⟩ : syracuseStep 1275497 = 956623) B956623
theorem B850297 : Blo 503794 850297 := bstep (se 2 (by rfl) ⟨318861, by rfl⟩ : syracuseStep 850297 = 637723) B637723
theorem B1538615 : Blo 503794 1538615 := bstep (se 1 (by rfl) ⟨1153961, by rfl⟩ : syracuseStep 1538615 = 2307923) B2307923
theorem B16350011 : Blo 503794 16350011 := bstep (se 1 (by rfl) ⟨12262508, by rfl⟩ : syracuseStep 16350011 = 24525017) B24525017
theorem B1702727 : Blo 503794 1702727 := bstep (se 1 (by rfl) ⟨1277045, by rfl⟩ : syracuseStep 1702727 = 2554091) B2554091
theorem B851195 : Blo 503794 851195 := bstep (se 1 (by rfl) ⟨638396, by rfl⟩ : syracuseStep 851195 = 1276793) B1276793
theorem B851303 : Blo 503794 851303 := bstep (se 1 (by rfl) ⟨638477, by rfl⟩ : syracuseStep 851303 = 1276955) B1276955
theorem B4095643 : Blo 503794 4095643 := bstep (se 1 (by rfl) ⟨3071732, by rfl⟩ : syracuseStep 4095643 = 6143465) B6143465
theorem B2555711 : Blo 503794 2555711 := bstep (se 1 (by rfl) ⟨1916783, by rfl⟩ : syracuseStep 2555711 = 3833567) B3833567
theorem B1703915 : Blo 503794 1703915 := bstep (se 1 (by rfl) ⟨1277936, by rfl⟩ : syracuseStep 1703915 = 2555873) B2555873
theorem B853247 : Blo 503794 853247 := bstep (se 1 (by rfl) ⟨639935, by rfl⟩ : syracuseStep 853247 = 1279871) B1279871
theorem B2164583 : Blo 503794 2164583 := bstep (se 1 (by rfl) ⟨1623437, by rfl⟩ : syracuseStep 2164583 = 3246875) B3246875
theorem B1706399 : Blo 503794 1706399 := bstep (se 1 (by rfl) ⟨1279799, by rfl⟩ : syracuseStep 1706399 = 2559599) B2559599
theorem B3250003 : Blo 503794 3250003 := bstep (se 1 (by rfl) ⟨2437502, by rfl⟩ : syracuseStep 3250003 = 4875005) B4875005
theorem B759785 : Blo 503794 759785 := bstep (se 2 (by rfl) ⟨284919, by rfl⟩ : syracuseStep 759785 = 569839) B569839
theorem B759983 : Blo 503794 759983 := bstep (se 1 (by rfl) ⟨569987, by rfl⟩ : syracuseStep 759983 = 1139975) B1139975
theorem B7313773 : Blo 503794 7313773 := bstep (se 3 (by rfl) ⟨1371332, by rfl⟩ : syracuseStep 7313773 = 2742665) B2742665
theorem B760367 : Blo 503794 760367 := bstep (se 1 (by rfl) ⟨570275, by rfl⟩ : syracuseStep 760367 = 1140551) B1140551
theorem B2890349 : Blo 503794 2890349 := bstep (se 3 (by rfl) ⟨541940, by rfl⟩ : syracuseStep 2890349 = 1083881) B1083881
theorem B9870113 : Blo 503794 9870113 := bstep (se 2 (by rfl) ⟨3701292, by rfl⟩ : syracuseStep 9870113 = 7402585) B7402585
theorem B4102973 : Blo 503794 4102973 := bstep (se 3 (by rfl) ⟨769307, by rfl⟩ : syracuseStep 4102973 = 1538615) B1538615
theorem B728047 : Blo 503794 728047 := bstep (se 1 (by rfl) ⟨546035, by rfl⟩ : syracuseStep 728047 = 1092071) B1092071
theorem B1155113 : Blo 503794 1155113 := bstep (se 2 (by rfl) ⟨433167, by rfl⟩ : syracuseStep 1155113 = 866335) B866335
theorem B5482217 : Blo 503794 5482217 := bstep (se 2 (by rfl) ⟨2055831, by rfl⟩ : syracuseStep 5482217 = 4111663) B4111663
theorem B567463 : Blo 503794 567463 := bstep (se 1 (by rfl) ⟨425597, by rfl⟩ : syracuseStep 567463 = 851195) B851195
theorem B567535 : Blo 503794 567535 := bstep (se 1 (by rfl) ⟨425651, by rfl⟩ : syracuseStep 567535 = 851303) B851303
theorem B2732201 : Blo 503794 2732201 := bstep (se 2 (by rfl) ⟨1024575, by rfl⟩ : syracuseStep 2732201 = 2049151) B2049151
theorem B2568671 : Blo 503794 2568671 := bstep (se 1 (by rfl) ⟨1926503, by rfl⟩ : syracuseStep 2568671 = 3853007) B3853007
theorem B569983 : Blo 503794 569983 := bstep (se 1 (by rfl) ⟨427487, by rfl⟩ : syracuseStep 569983 = 854975) B854975
theorem B504935 : Blo 503794 504935 := bstep (se 1 (by rfl) ⟨378701, by rfl⟩ : syracuseStep 504935 = 757403) B757403
theorem B2569319 : Blo 503794 2569319 := bstep (se 1 (by rfl) ⟨1926989, by rfl⟩ : syracuseStep 2569319 = 3853979) B3853979
theorem B505279 : Blo 503794 505279 := bstep (se 1 (by rfl) ⟨378959, by rfl⟩ : syracuseStep 505279 = 757919) B757919
theorem B505703 : Blo 503794 505703 := bstep (se 1 (by rfl) ⟨379277, by rfl⟩ : syracuseStep 505703 = 758555) B758555
theorem B505727 : Blo 503794 505727 := bstep (se 1 (by rfl) ⟨379295, by rfl⟩ : syracuseStep 505727 = 758591) B758591
theorem B506015 : Blo 503794 506015 := bstep (se 1 (by rfl) ⟨379511, by rfl⟩ : syracuseStep 506015 = 759023) B759023
theorem B506095 : Blo 503794 506095 := bstep (se 1 (by rfl) ⟨379571, by rfl⟩ : syracuseStep 506095 = 759143) B759143
theorem B506535 : Blo 503794 506535 := bstep (se 1 (by rfl) ⟨379901, by rfl⟩ : syracuseStep 506535 = 759803) B759803
theorem B506991 : Blo 503794 506991 := bstep (se 1 (by rfl) ⟨380243, by rfl⟩ : syracuseStep 506991 = 760487) B760487
theorem B507583 : Blo 503794 507583 := bstep (se 1 (by rfl) ⟨380687, by rfl⟩ : syracuseStep 507583 = 761375) B761375
theorem B8634275 : Blo 503794 8634275 := bstep (se 1 (by rfl) ⟨6475706, by rfl⟩ : syracuseStep 8634275 = 12951413) B12951413
theorem B639515 : Blo 503794 639515 := bstep (se 1 (by rfl) ⟨479636, by rfl⟩ : syracuseStep 639515 = 959273) B959273
theorem B18727703 : Blo 503794 18727703 := bstep (se 1 (by rfl) ⟨14045777, by rfl⟩ : syracuseStep 18727703 = 28091555) B28091555
theorem B17548397 : Blo 503794 17548397 := bstep (se 3 (by rfl) ⟨3290324, by rfl⟩ : syracuseStep 17548397 = 6580649) B6580649
theorem B640639 : Blo 503794 640639 := bstep (se 1 (by rfl) ⟨480479, by rfl⟩ : syracuseStep 640639 = 960959) B960959
theorem B10898003 : Blo 503794 10898003 := bstep (se 1 (by rfl) ⟨8173502, by rfl⟩ : syracuseStep 10898003 = 16347005) B16347005
theorem B1952423 : Blo 503794 1952423 := bstep (se 1 (by rfl) ⟨1464317, by rfl⟩ : syracuseStep 1952423 = 2928635) B2928635
theorem B1133567 : Blo 503794 1133567 := bstep (se 1 (by rfl) ⟨850175, by rfl⟩ : syracuseStep 1133567 = 1700351) B1700351
theorem B1133729 : Blo 503794 1133729 := bstep (se 2 (by rfl) ⟨425148, by rfl⟩ : syracuseStep 1133729 = 850297) B850297
theorem B1134035 : Blo 503794 1134035 := bstep (se 1 (by rfl) ⟨850526, by rfl⟩ : syracuseStep 1134035 = 1701053) B1701053
theorem B1625579 : Blo 503794 1625579 := bstep (se 1 (by rfl) ⟨1219184, by rfl⟩ : syracuseStep 1625579 = 2438369) B2438369
theorem B10900007 : Blo 503794 10900007 := bstep (se 1 (by rfl) ⟨8175005, by rfl⟩ : syracuseStep 10900007 = 16350011) B16350011
theorem B1135151 : Blo 503794 1135151 := bstep (se 1 (by rfl) ⟨851363, by rfl⟩ : syracuseStep 1135151 = 1702727) B1702727
theorem B5460857 : Blo 503794 5460857 := bstep (se 2 (by rfl) ⟨2047821, by rfl⟩ : syracuseStep 5460857 = 4095643) B4095643
theorem B1135943 : Blo 503794 1135943 := bstep (se 1 (by rfl) ⟨851957, by rfl⟩ : syracuseStep 1135943 = 1703915) B1703915
theorem B2152145 : Blo 503794 2152145 := bstep (se 2 (by rfl) ⟨807054, by rfl⟩ : syracuseStep 2152145 = 1614109) B1614109
theorem B1137383 : Blo 503794 1137383 := bstep (se 1 (by rfl) ⟨853037, by rfl⟩ : syracuseStep 1137383 = 1706075) B1706075
theorem B1137977 : Blo 503794 1137977 := bstep (se 2 (by rfl) ⟨426741, by rfl⟩ : syracuseStep 1137977 = 853483) B853483
theorem B2874811 : Blo 503794 2874811 := bstep (se 1 (by rfl) ⟨2156108, by rfl⟩ : syracuseStep 2874811 = 4312217) B4312217
theorem B2056859 : Blo 503794 2056859 := bstep (se 1 (by rfl) ⟨1542644, by rfl⟩ : syracuseStep 2056859 = 3085289) B3085289
theorem B648959 : Blo 503794 648959 := bstep (se 1 (by rfl) ⟨486719, by rfl⟩ : syracuseStep 648959 = 973439) B973439
theorem B2877545 : Blo 503794 2877545 := bstep (se 2 (by rfl) ⟨1079079, by rfl⟩ : syracuseStep 2877545 = 2158159) B2158159
theorem B1141343 : Blo 503794 1141343 := bstep (se 1 (by rfl) ⟨856007, by rfl⟩ : syracuseStep 1141343 = 1712015) B1712015
theorem B9759851 : Blo 503794 9759851 := bstep (se 1 (by rfl) ⟨7319888, by rfl⟩ : syracuseStep 9759851 = 14639777) B14639777
theorem B4092527 : Blo 503794 4092527 := bstep (se 1 (by rfl) ⟨3069395, by rfl⟩ : syracuseStep 4092527 = 6138791) B6138791
theorem B2552633 : Blo 503794 2552633 := bstep (se 2 (by rfl) ⟨957237, by rfl⟩ : syracuseStep 2552633 = 1914475) B1914475
theorem B3241727 : Blo 503794 3241727 := bstep (se 1 (by rfl) ⟨2431295, by rfl⟩ : syracuseStep 3241727 = 4862591) B4862591
theorem B2553929 : Blo 503794 2553929 := bstep (se 2 (by rfl) ⟨957723, by rfl⟩ : syracuseStep 2553929 = 1915447) B1915447
theorem B3897695 : Blo 503794 3897695 := bstep (se 1 (by rfl) ⟨2923271, by rfl⟩ : syracuseStep 3897695 = 5846543) B5846543
theorem B850331 : Blo 503794 850331 := bstep (se 1 (by rfl) ⟨637748, by rfl⟩ : syracuseStep 850331 = 1275497) B1275497
theorem B1703807 : Blo 503794 1703807 := bstep (se 1 (by rfl) ⟨1277855, by rfl⟩ : syracuseStep 1703807 = 2555711) B2555711
theorem B12485135 : Blo 503794 12485135 := bstep (se 1 (by rfl) ⟨9363851, by rfl⟩ : syracuseStep 12485135 = 18727703) B18727703
theorem B11698931 : Blo 503794 11698931 := bstep (se 1 (by rfl) ⟨8774198, by rfl⟩ : syracuseStep 11698931 = 17548397) B17548397
theorem B1705373 : Blo 503794 1705373 := bstep (se 3 (by rfl) ⟨319757, by rfl⟩ : syracuseStep 1705373 = 639515) B639515
theorem B755711 : Blo 503794 755711 := bstep (se 1 (by rfl) ⟨566783, by rfl⟩ : syracuseStep 755711 = 1133567) B1133567
theorem B755819 : Blo 503794 755819 := bstep (se 1 (by rfl) ⟨566864, by rfl⟩ : syracuseStep 755819 = 1133729) B1133729
theorem B854185 : Blo 503794 854185 := bstep (se 2 (by rfl) ⟨320319, by rfl⟩ : syracuseStep 854185 = 640639) B640639
theorem B756023 : Blo 503794 756023 := bstep (se 1 (by rfl) ⟨567017, by rfl⟩ : syracuseStep 756023 = 1134035) B1134035
theorem B1083719 : Blo 503794 1083719 := bstep (se 1 (by rfl) ⟨812789, by rfl⟩ : syracuseStep 1083719 = 1625579) B1625579
theorem B756617 : Blo 503794 756617 := bstep (se 2 (by rfl) ⟨283731, by rfl⟩ : syracuseStep 756617 = 567463) B567463
theorem B756713 : Blo 503794 756713 := bstep (se 2 (by rfl) ⟨283767, by rfl⟩ : syracuseStep 756713 = 567535) B567535
theorem B756767 : Blo 503794 756767 := bstep (se 1 (by rfl) ⟨567575, by rfl⟩ : syracuseStep 756767 = 1135151) B1135151
theorem B3640571 : Blo 503794 3640571 := bstep (se 1 (by rfl) ⟨2730428, by rfl⟩ : syracuseStep 3640571 = 5460857) B5460857
theorem B757295 : Blo 503794 757295 := bstep (se 1 (by rfl) ⟨567971, by rfl⟩ : syracuseStep 757295 = 1135943) B1135943
theorem B758255 : Blo 503794 758255 := bstep (se 1 (by rfl) ⟨568691, by rfl⟩ : syracuseStep 758255 = 1137383) B1137383
theorem B758651 : Blo 503794 758651 := bstep (se 1 (by rfl) ⟨568988, by rfl⟩ : syracuseStep 758651 = 1137977) B1137977
theorem B5772221 : Blo 503794 5772221 := bstep (se 3 (by rfl) ⟨1082291, by rfl⟩ : syracuseStep 5772221 = 2164583) B2164583
theorem B759977 : Blo 503794 759977 := bstep (se 2 (by rfl) ⟨284991, by rfl⟩ : syracuseStep 759977 = 569983) B569983
theorem B760895 : Blo 503794 760895 := bstep (se 1 (by rfl) ⟨570671, by rfl⟩ : syracuseStep 760895 = 1141343) B1141343
theorem B4333337 : Blo 503794 4333337 := bstep (se 2 (by rfl) ⟨1625001, by rfl⟩ : syracuseStep 4333337 = 3250003) B3250003
theorem B1712447 : Blo 503794 1712447 := bstep (se 1 (by rfl) ⟨1284335, by rfl⟩ : syracuseStep 1712447 = 2568671) B2568671
theorem B2728351 : Blo 503794 2728351 := bstep (se 1 (by rfl) ⟨2046263, by rfl⟩ : syracuseStep 2728351 = 4092527) B4092527
theorem B1712879 : Blo 503794 1712879 := bstep (se 1 (by rfl) ⟨1284659, by rfl⟩ : syracuseStep 1712879 = 2569319) B2569319
theorem B2598463 : Blo 503794 2598463 := bstep (se 1 (by rfl) ⟨1948847, by rfl⟩ : syracuseStep 2598463 = 3897695) B3897695
theorem B566887 : Blo 503794 566887 := bstep (se 1 (by rfl) ⟨425165, by rfl⟩ : syracuseStep 566887 = 850331) B850331
theorem B568831 : Blo 503794 568831 := bstep (se 1 (by rfl) ⟨426623, by rfl⟩ : syracuseStep 568831 = 853247) B853247
theorem B506523 : Blo 503794 506523 := bstep (se 1 (by rfl) ⟨379892, by rfl⟩ : syracuseStep 506523 = 759785) B759785
theorem B506655 : Blo 503794 506655 := bstep (se 1 (by rfl) ⟨379991, by rfl⟩ : syracuseStep 506655 = 759983) B759983
theorem B506911 : Blo 503794 506911 := bstep (se 1 (by rfl) ⟨380183, by rfl⟩ : syracuseStep 506911 = 760367) B760367
theorem B2735315 : Blo 503794 2735315 := bstep (se 1 (by rfl) ⟨2051486, by rfl⟩ : syracuseStep 2735315 = 4102973) B4102973
theorem B770075 : Blo 503794 770075 := bstep (se 1 (by rfl) ⟨577556, by rfl⟩ : syracuseStep 770075 = 1155113) B1155113
theorem B3654811 : Blo 503794 3654811 := bstep (se 1 (by rfl) ⟨2741108, by rfl⟩ : syracuseStep 3654811 = 5482217) B5482217
theorem B1918363 : Blo 503794 1918363 := bstep (se 1 (by rfl) ⟨1438772, by rfl⟩ : syracuseStep 1918363 = 2877545) B2877545
theorem B6506567 : Blo 503794 6506567 := bstep (se 1 (by rfl) ⟨4879925, by rfl⟩ : syracuseStep 6506567 = 9759851) B9759851
theorem B1821467 : Blo 503794 1821467 := bstep (se 1 (by rfl) ⟨1366100, by rfl⟩ : syracuseStep 1821467 = 2732201) B2732201
theorem B9751697 : Blo 503794 9751697 := bstep (se 2 (by rfl) ⟨3656886, by rfl⟩ : syracuseStep 9751697 = 7313773) B7313773
theorem B970729 : Blo 503794 970729 := bstep (se 2 (by rfl) ⟨364023, by rfl⟩ : syracuseStep 970729 = 728047) B728047
theorem B1135871 : Blo 503794 1135871 := bstep (se 1 (by rfl) ⟨851903, by rfl⟩ : syracuseStep 1135871 = 1703807) B1703807
theorem B5756183 : Blo 503794 5756183 := bstep (se 1 (by rfl) ⟨4317137, by rfl⟩ : syracuseStep 5756183 = 8634275) B8634275
theorem B1137599 : Blo 503794 1137599 := bstep (se 1 (by rfl) ⟨853199, by rfl⟩ : syracuseStep 1137599 = 1706399) B1706399
theorem B7265335 : Blo 503794 7265335 := bstep (se 1 (by rfl) ⟨5449001, by rfl⟩ : syracuseStep 7265335 = 10898003) B10898003
theorem B1301615 : Blo 503794 1301615 := bstep (se 1 (by rfl) ⟨976211, by rfl⟩ : syracuseStep 1301615 = 1952423) B1952423
theorem B7266671 : Blo 503794 7266671 := bstep (se 1 (by rfl) ⟨5450003, by rfl⟩ : syracuseStep 7266671 = 10900007) B10900007
theorem B1434763 : Blo 503794 1434763 := bstep (se 1 (by rfl) ⟨1076072, by rfl⟩ : syracuseStep 1434763 = 2152145) B2152145
theorem B1926899 : Blo 503794 1926899 := bstep (se 1 (by rfl) ⟨1445174, by rfl⟩ : syracuseStep 1926899 = 2890349) B2890349
theorem B6580075 : Blo 503794 6580075 := bstep (se 1 (by rfl) ⟨4935056, by rfl⟩ : syracuseStep 6580075 = 9870113) B9870113
theorem B1730557 : Blo 503794 1730557 := bstep (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) B648959
theorem B1371239 : Blo 503794 1371239 := bstep (se 1 (by rfl) ⟨1028429, by rfl⟩ : syracuseStep 1371239 = 2056859) B2056859
theorem B1701755 : Blo 503794 1701755 := bstep (se 1 (by rfl) ⟨1276316, by rfl⟩ : syracuseStep 1701755 = 2552633) B2552633
theorem B2161151 : Blo 503794 2161151 := bstep (se 1 (by rfl) ⟨1620863, by rfl⟩ : syracuseStep 2161151 = 3241727) B3241727
theorem B1702619 : Blo 503794 1702619 := bstep (se 1 (by rfl) ⟨1276964, by rfl⟩ : syracuseStep 1702619 = 2553929) B2553929
theorem B3833081 : Blo 503794 3833081 := bstep (se 2 (by rfl) ⟨1437405, by rfl⟩ : syracuseStep 3833081 = 2874811) B2874811
theorem B7799287 : Blo 503794 7799287 := bstep (se 1 (by rfl) ⟨5849465, by rfl⟩ : syracuseStep 7799287 = 11698931) B11698931
theorem B3637801 : Blo 503794 3637801 := bstep (se 2 (by rfl) ⟨1364175, by rfl⟩ : syracuseStep 3637801 = 2728351) B2728351
theorem B33293693 : Blo 503794 33293693 := bstep (se 3 (by rfl) ⟨6242567, by rfl⟩ : syracuseStep 33293693 = 12485135) B12485135
theorem B2557817 : Blo 503794 2557817 := bstep (se 2 (by rfl) ⟨959181, by rfl⟩ : syracuseStep 2557817 = 1918363) B1918363
theorem B755849 : Blo 503794 755849 := bstep (se 2 (by rfl) ⟨283443, by rfl⟩ : syracuseStep 755849 = 566887) B566887
theorem B2427047 : Blo 503794 2427047 := bstep (se 1 (by rfl) ⟨1820285, by rfl⟩ : syracuseStep 2427047 = 3640571) B3640571
theorem B757247 : Blo 503794 757247 := bstep (se 1 (by rfl) ⟨567935, by rfl⟩ : syracuseStep 757247 = 1135871) B1135871
theorem B3837455 : Blo 503794 3837455 := bstep (se 1 (by rfl) ⟨2878091, by rfl⟩ : syracuseStep 3837455 = 5756183) B5756183
theorem B758399 : Blo 503794 758399 := bstep (se 1 (by rfl) ⟨568799, by rfl⟩ : syracuseStep 758399 = 1137599) B1137599
theorem B758441 : Blo 503794 758441 := bstep (se 2 (by rfl) ⟨284415, by rfl⟩ : syracuseStep 758441 = 568831) B568831
theorem B2888891 : Blo 503794 2888891 := bstep (se 1 (by rfl) ⟨2166668, by rfl⟩ : syracuseStep 2888891 = 4333337) B4333337
theorem B2889917 : Blo 503794 2889917 := bstep (se 3 (by rfl) ⟨541859, by rfl⟩ : syracuseStep 2889917 = 1083719) B1083719
theorem B1284599 : Blo 503794 1284599 := bstep (se 1 (by rfl) ⟨963449, by rfl⟩ : syracuseStep 1284599 = 1926899) B1926899
theorem B4857245 : Blo 503794 4857245 := bstep (se 3 (by rfl) ⟨910733, by rfl⟩ : syracuseStep 4857245 = 1821467) B1821467
theorem B503807 : Blo 503794 503807 := bstep (se 1 (by rfl) ⟨377855, by rfl⟩ : syracuseStep 503807 = 755711) B755711
theorem B4337711 : Blo 503794 4337711 := bstep (se 1 (by rfl) ⟨3253283, by rfl⟩ : syracuseStep 4337711 = 6506567) B6506567
theorem B503879 : Blo 503794 503879 := bstep (se 1 (by rfl) ⟨377909, by rfl⟩ : syracuseStep 503879 = 755819) B755819
theorem B1913017 : Blo 503794 1913017 := bstep (se 2 (by rfl) ⟨717381, by rfl⟩ : syracuseStep 1913017 = 1434763) B1434763
theorem B504015 : Blo 503794 504015 := bstep (se 1 (by rfl) ⟨378011, by rfl⟩ : syracuseStep 504015 = 756023) B756023
theorem B504411 : Blo 503794 504411 := bstep (se 1 (by rfl) ⟨378308, by rfl⟩ : syracuseStep 504411 = 756617) B756617
theorem B504475 : Blo 503794 504475 := bstep (se 1 (by rfl) ⟨378356, by rfl⟩ : syracuseStep 504475 = 756713) B756713
theorem B504511 : Blo 503794 504511 := bstep (se 1 (by rfl) ⟨378383, by rfl⟩ : syracuseStep 504511 = 756767) B756767
theorem B6501131 : Blo 503794 6501131 := bstep (se 1 (by rfl) ⟨4875848, by rfl⟩ : syracuseStep 6501131 = 9751697) B9751697
theorem B504863 : Blo 503794 504863 := bstep (se 1 (by rfl) ⟨378647, by rfl⟩ : syracuseStep 504863 = 757295) B757295
theorem B2307409 : Blo 503794 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B505503 : Blo 503794 505503 := bstep (se 1 (by rfl) ⟨379127, by rfl⟩ : syracuseStep 505503 = 758255) B758255
theorem B505767 : Blo 503794 505767 := bstep (se 1 (by rfl) ⟨379325, by rfl⟩ : syracuseStep 505767 = 758651) B758651
theorem B3848147 : Blo 503794 3848147 := bstep (se 1 (by rfl) ⟨2886110, by rfl⟩ : syracuseStep 3848147 = 5772221) B5772221
theorem B506651 : Blo 503794 506651 := bstep (se 1 (by rfl) ⟨379988, by rfl⟩ : syracuseStep 506651 = 759977) B759977
theorem B507263 : Blo 503794 507263 := bstep (se 1 (by rfl) ⟨380447, by rfl⟩ : syracuseStep 507263 = 760895) B760895
theorem B867743 : Blo 503794 867743 := bstep (se 1 (by rfl) ⟨650807, by rfl⟩ : syracuseStep 867743 = 1301615) B1301615
theorem B1134503 : Blo 503794 1134503 := bstep (se 1 (by rfl) ⟨850877, by rfl⟩ : syracuseStep 1134503 = 1701755) B1701755
theorem B9687113 : Blo 503794 9687113 := bstep (se 2 (by rfl) ⟨3632667, by rfl⟩ : syracuseStep 9687113 = 7265335) B7265335
theorem B1135079 : Blo 503794 1135079 := bstep (se 1 (by rfl) ⟨851309, by rfl⟩ : syracuseStep 1135079 = 1702619) B1702619
theorem B1823543 : Blo 503794 1823543 := bstep (se 1 (by rfl) ⟨1367657, by rfl⟩ : syracuseStep 1823543 = 2735315) B2735315
theorem B513383 : Blo 503794 513383 := bstep (se 1 (by rfl) ⟨385037, by rfl⟩ : syracuseStep 513383 = 770075) B770075
theorem B1136915 : Blo 503794 1136915 := bstep (se 1 (by rfl) ⟨852686, by rfl⟩ : syracuseStep 1136915 = 1705373) B1705373
theorem B4873081 : Blo 503794 4873081 := bstep (se 2 (by rfl) ⟨1827405, by rfl⟩ : syracuseStep 4873081 = 3654811) B3654811
theorem B3464617 : Blo 503794 3464617 := bstep (se 2 (by rfl) ⟨1299231, by rfl⟩ : syracuseStep 3464617 = 2598463) B2598463
theorem B8773433 : Blo 503794 8773433 := bstep (se 2 (by rfl) ⟨3290037, by rfl⟩ : syracuseStep 8773433 = 6580075) B6580075
theorem B1138913 : Blo 503794 1138913 := bstep (se 2 (by rfl) ⟨427092, by rfl⟩ : syracuseStep 1138913 = 854185) B854185
theorem B1141631 : Blo 503794 1141631 := bstep (se 1 (by rfl) ⟨856223, by rfl⟩ : syracuseStep 1141631 = 1712447) B1712447
theorem B4844447 : Blo 503794 4844447 := bstep (se 1 (by rfl) ⟨3633335, by rfl⟩ : syracuseStep 4844447 = 7266671) B7266671
theorem B1141919 : Blo 503794 1141919 := bstep (se 1 (by rfl) ⟨856439, by rfl⟩ : syracuseStep 1141919 = 1712879) B1712879
theorem B914159 : Blo 503794 914159 := bstep (se 1 (by rfl) ⟨685619, by rfl⟩ : syracuseStep 914159 = 1371239) B1371239
theorem B1440767 : Blo 503794 1440767 := bstep (se 1 (by rfl) ⟨1080575, by rfl⟩ : syracuseStep 1440767 = 2161151) B2161151
theorem B2555387 : Blo 503794 2555387 := bstep (se 1 (by rfl) ⟨1916540, by rfl⟩ : syracuseStep 2555387 = 3833081) B3833081
theorem B20708885 : Blo 503794 20708885 := bstep (se 6 (by rfl) ⟨485364, by rfl⟩ : syracuseStep 20708885 = 970729) B970729
theorem B4850401 : Blo 503794 4850401 := bstep (se 2 (by rfl) ⟨1818900, by rfl⟩ : syracuseStep 4850401 = 3637801) B3637801
theorem B1705211 : Blo 503794 1705211 := bstep (se 1 (by rfl) ⟨1278908, by rfl⟩ : syracuseStep 1705211 = 2557817) B2557817
theorem B2558303 : Blo 503794 2558303 := bstep (se 1 (by rfl) ⟨1918727, by rfl⟩ : syracuseStep 2558303 = 3837455) B3837455
theorem B756335 : Blo 503794 756335 := bstep (se 1 (by rfl) ⟨567251, by rfl⟩ : syracuseStep 756335 = 1134503) B1134503
theorem B6458075 : Blo 503794 6458075 := bstep (se 1 (by rfl) ⟨4843556, by rfl⟩ : syracuseStep 6458075 = 9687113) B9687113
theorem B756719 : Blo 503794 756719 := bstep (se 1 (by rfl) ⟨567539, by rfl⟩ : syracuseStep 756719 = 1135079) B1135079
theorem B1215695 : Blo 503794 1215695 := bstep (se 1 (by rfl) ⟨911771, by rfl⟩ : syracuseStep 1215695 = 1823543) B1823543
theorem B757943 : Blo 503794 757943 := bstep (se 1 (by rfl) ⟨568457, by rfl⟩ : syracuseStep 757943 = 1136915) B1136915
theorem B856399 : Blo 503794 856399 := bstep (se 1 (by rfl) ⟨642299, by rfl⟩ : syracuseStep 856399 = 1284599) B1284599
theorem B759275 : Blo 503794 759275 := bstep (se 1 (by rfl) ⟨569456, by rfl⟩ : syracuseStep 759275 = 1138913) B1138913
theorem B761087 : Blo 503794 761087 := bstep (se 1 (by rfl) ⟨570815, by rfl⟩ : syracuseStep 761087 = 1141631) B1141631
theorem B761279 : Blo 503794 761279 := bstep (se 1 (by rfl) ⟨570959, by rfl⟩ : syracuseStep 761279 = 1141919) B1141919
theorem B2891807 : Blo 503794 2891807 := bstep (se 1 (by rfl) ⟨2168855, by rfl⟩ : syracuseStep 2891807 = 4337711) B4337711
theorem B4334087 : Blo 503794 4334087 := bstep (se 1 (by rfl) ⟨3250565, by rfl⟩ : syracuseStep 4334087 = 6501131) B6501131
theorem B6497441 : Blo 503794 6497441 := bstep (se 2 (by rfl) ⟨2436540, by rfl⟩ : syracuseStep 6497441 = 4873081) B4873081
theorem B2565431 : Blo 503794 2565431 := bstep (se 1 (by rfl) ⟨1924073, by rfl⟩ : syracuseStep 2565431 = 3848147) B3848147
theorem B960511 : Blo 503794 960511 := bstep (se 1 (by rfl) ⟨720383, by rfl⟩ : syracuseStep 960511 = 1440767) B1440767
theorem B13805923 : Blo 503794 13805923 := bstep (se 1 (by rfl) ⟨10354442, by rfl⟩ : syracuseStep 13805923 = 20708885) B20708885
theorem B10399049 : Blo 503794 10399049 := bstep (se 2 (by rfl) ⟨3899643, by rfl⟩ : syracuseStep 10399049 = 7799287) B7799287
theorem B22195795 : Blo 503794 22195795 := bstep (se 1 (by rfl) ⟨16646846, by rfl⟩ : syracuseStep 22195795 = 33293693) B33293693
theorem B503899 : Blo 503794 503899 := bstep (se 1 (by rfl) ⟨377924, by rfl⟩ : syracuseStep 503899 = 755849) B755849
theorem B1618031 : Blo 503794 1618031 := bstep (se 1 (by rfl) ⟨1213523, by rfl⟩ : syracuseStep 1618031 = 2427047) B2427047
theorem B504831 : Blo 503794 504831 := bstep (se 1 (by rfl) ⟨378623, by rfl⟩ : syracuseStep 504831 = 757247) B757247
theorem B505599 : Blo 503794 505599 := bstep (se 1 (by rfl) ⟨379199, by rfl⟩ : syracuseStep 505599 = 758399) B758399
theorem B505627 : Blo 503794 505627 := bstep (se 1 (by rfl) ⟨379220, by rfl⟩ : syracuseStep 505627 = 758441) B758441
theorem B5848955 : Blo 503794 5848955 := bstep (se 1 (by rfl) ⟨4386716, by rfl⟩ : syracuseStep 5848955 = 8773433) B8773433
theorem B12306181 : Blo 503794 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B3229631 : Blo 503794 3229631 := bstep (se 1 (by rfl) ⟨2422223, by rfl⟩ : syracuseStep 3229631 = 4844447) B4844447
theorem B609439 : Blo 503794 609439 := bstep (se 1 (by rfl) ⟨457079, by rfl⟩ : syracuseStep 609439 = 914159) B914159
theorem B578495 : Blo 503794 578495 := bstep (se 1 (by rfl) ⟨433871, by rfl⟩ : syracuseStep 578495 = 867743) B867743
theorem B1925927 : Blo 503794 1925927 := bstep (se 1 (by rfl) ⟨1444445, by rfl⟩ : syracuseStep 1925927 = 2888891) B2888891
theorem B1369021 : Blo 503794 1369021 := bstep (se 3 (by rfl) ⟨256691, by rfl⟩ : syracuseStep 1369021 = 513383) B513383
theorem B1926611 : Blo 503794 1926611 := bstep (se 1 (by rfl) ⟨1444958, by rfl⟩ : syracuseStep 1926611 = 2889917) B2889917
theorem B3238163 : Blo 503794 3238163 := bstep (se 1 (by rfl) ⟨2428622, by rfl⟩ : syracuseStep 3238163 = 4857245) B4857245
theorem B2550689 : Blo 503794 2550689 := bstep (se 2 (by rfl) ⟨956508, by rfl⟩ : syracuseStep 2550689 = 1913017) B1913017
theorem B4619489 : Blo 503794 4619489 := bstep (se 2 (by rfl) ⟨1732308, by rfl⟩ : syracuseStep 4619489 = 3464617) B3464617
theorem B1703591 : Blo 503794 1703591 := bstep (se 1 (by rfl) ⟨1277693, by rfl⟩ : syracuseStep 1703591 = 2555387) B2555387
theorem B1705535 : Blo 503794 1705535 := bstep (se 1 (by rfl) ⟨1279151, by rfl⟩ : syracuseStep 1705535 = 2558303) B2558303
theorem B1542653 : Blo 503794 1542653 := bstep (se 3 (by rfl) ⟨289247, by rfl⟩ : syracuseStep 1542653 = 578495) B578495
theorem B1280681 : Blo 503794 1280681 := bstep (se 2 (by rfl) ⟨480255, by rfl⟩ : syracuseStep 1280681 = 960511) B960511
theorem B29594393 : Blo 503794 29594393 := bstep (se 2 (by rfl) ⟨11097897, by rfl⟩ : syracuseStep 29594393 = 22195795) B22195795
theorem B2889391 : Blo 503794 2889391 := bstep (se 1 (by rfl) ⟨2167043, by rfl⟩ : syracuseStep 2889391 = 4334087) B4334087
theorem B1283951 : Blo 503794 1283951 := bstep (se 1 (by rfl) ⟨962963, by rfl⟩ : syracuseStep 1283951 = 1925927) B1925927
theorem B4331627 : Blo 503794 4331627 := bstep (se 1 (by rfl) ⟨3248720, by rfl⟩ : syracuseStep 4331627 = 6497441) B6497441
theorem B1710287 : Blo 503794 1710287 := bstep (se 1 (by rfl) ⟨1282715, by rfl⟩ : syracuseStep 1710287 = 2565431) B2565431
theorem B1284407 : Blo 503794 1284407 := bstep (se 1 (by rfl) ⟨963305, by rfl⟩ : syracuseStep 1284407 = 1926611) B1926611
theorem B6467201 : Blo 503794 6467201 := bstep (se 2 (by rfl) ⟨2425200, by rfl⟩ : syracuseStep 6467201 = 4850401) B4850401
theorem B504223 : Blo 503794 504223 := bstep (se 1 (by rfl) ⟨378167, by rfl⟩ : syracuseStep 504223 = 756335) B756335
theorem B4305383 : Blo 503794 4305383 := bstep (se 1 (by rfl) ⟨3229037, by rfl⟩ : syracuseStep 4305383 = 6458075) B6458075
theorem B504479 : Blo 503794 504479 := bstep (se 1 (by rfl) ⟨378359, by rfl⟩ : syracuseStep 504479 = 756719) B756719
theorem B505295 : Blo 503794 505295 := bstep (se 1 (by rfl) ⟨378971, by rfl⟩ : syracuseStep 505295 = 757943) B757943
theorem B506183 : Blo 503794 506183 := bstep (se 1 (by rfl) ⟨379637, by rfl⟩ : syracuseStep 506183 = 759275) B759275
theorem B507391 : Blo 503794 507391 := bstep (se 1 (by rfl) ⟨380543, by rfl⟩ : syracuseStep 507391 = 761087) B761087
theorem B507519 : Blo 503794 507519 := bstep (se 1 (by rfl) ⟨380639, by rfl⟩ : syracuseStep 507519 = 761279) B761279
theorem B6932699 : Blo 503794 6932699 := bstep (se 1 (by rfl) ⟨5199524, by rfl⟩ : syracuseStep 6932699 = 10399049) B10399049
theorem B1135727 : Blo 503794 1135727 := bstep (se 1 (by rfl) ⟨851795, by rfl⟩ : syracuseStep 1135727 = 1703591) B1703591
theorem B1136807 : Blo 503794 1136807 := bstep (se 1 (by rfl) ⟨852605, by rfl⟩ : syracuseStep 1136807 = 1705211) B1705211
theorem B1825361 : Blo 503794 1825361 := bstep (se 2 (by rfl) ⟨684510, by rfl⟩ : syracuseStep 1825361 = 1369021) B1369021
theorem B2153087 : Blo 503794 2153087 := bstep (se 1 (by rfl) ⟨1614815, by rfl⟩ : syracuseStep 2153087 = 3229631) B3229631
theorem B16408241 : Blo 503794 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B18407897 : Blo 503794 18407897 := bstep (se 2 (by rfl) ⟨6902961, by rfl⟩ : syracuseStep 18407897 = 13805923) B13805923
theorem B812585 : Blo 503794 812585 := bstep (se 2 (by rfl) ⟨304719, by rfl⟩ : syracuseStep 812585 = 609439) B609439
theorem B1927871 : Blo 503794 1927871 := bstep (se 1 (by rfl) ⟨1445903, by rfl⟩ : syracuseStep 1927871 = 2891807) B2891807
theorem B1141865 : Blo 503794 1141865 := bstep (se 2 (by rfl) ⟨428199, by rfl⟩ : syracuseStep 1141865 = 856399) B856399
theorem B2158775 : Blo 503794 2158775 := bstep (se 1 (by rfl) ⟨1619081, by rfl⟩ : syracuseStep 2158775 = 3238163) B3238163
theorem B1700459 : Blo 503794 1700459 := bstep (se 1 (by rfl) ⟨1275344, by rfl⟩ : syracuseStep 1700459 = 2550689) B2550689
theorem B1078687 : Blo 503794 1078687 := bstep (se 1 (by rfl) ⟨809015, by rfl⟩ : syracuseStep 1078687 = 1618031) B1618031
theorem B3241853 : Blo 503794 3241853 := bstep (se 3 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 3241853 = 1215695) B1215695
theorem B12318637 : Blo 503794 12318637 := bstep (se 3 (by rfl) ⟨2309744, by rfl⟩ : syracuseStep 12318637 = 4619489) B4619489
theorem B3899303 : Blo 503794 3899303 := bstep (se 1 (by rfl) ⟨2924477, by rfl⟩ : syracuseStep 3899303 = 5848955) B5848955
theorem B4621799 : Blo 503794 4621799 := bstep (se 1 (by rfl) ⟨3466349, by rfl⟩ : syracuseStep 4621799 = 6932699) B6932699
theorem B853787 : Blo 503794 853787 := bstep (se 1 (by rfl) ⟨640340, by rfl⟩ : syracuseStep 853787 = 1280681) B1280681
theorem B19729595 : Blo 503794 19729595 := bstep (se 1 (by rfl) ⟨14797196, by rfl⟩ : syracuseStep 19729595 = 29594393) B29594393
theorem B757151 : Blo 503794 757151 := bstep (se 1 (by rfl) ⟨567863, by rfl⟩ : syracuseStep 757151 = 1135727) B1135727
theorem B855967 : Blo 503794 855967 := bstep (se 1 (by rfl) ⟨641975, by rfl⟩ : syracuseStep 855967 = 1283951) B1283951
theorem B2887751 : Blo 503794 2887751 := bstep (se 1 (by rfl) ⟨2165813, by rfl⟩ : syracuseStep 2887751 = 4331627) B4331627
theorem B757871 : Blo 503794 757871 := bstep (se 1 (by rfl) ⟨568403, by rfl⟩ : syracuseStep 757871 = 1136807) B1136807
theorem B856271 : Blo 503794 856271 := bstep (se 1 (by rfl) ⟨642203, by rfl⟩ : syracuseStep 856271 = 1284407) B1284407
theorem B1216907 : Blo 503794 1216907 := bstep (se 1 (by rfl) ⟨912680, by rfl⟩ : syracuseStep 1216907 = 1825361) B1825361
theorem B1285247 : Blo 503794 1285247 := bstep (se 1 (by rfl) ⟨963935, by rfl⟩ : syracuseStep 1285247 = 1927871) B1927871
theorem B761243 : Blo 503794 761243 := bstep (se 1 (by rfl) ⟨570932, by rfl⟩ : syracuseStep 761243 = 1141865) B1141865
theorem B16424849 : Blo 503794 16424849 := bstep (se 2 (by rfl) ⟨6159318, by rfl⟩ : syracuseStep 16424849 = 12318637) B12318637
theorem B2599535 : Blo 503794 2599535 := bstep (se 1 (by rfl) ⟨1949651, by rfl⟩ : syracuseStep 2599535 = 3899303) B3899303
theorem B1028435 : Blo 503794 1028435 := bstep (se 1 (by rfl) ⟨771326, by rfl⟩ : syracuseStep 1028435 = 1542653) B1542653
theorem B12271931 : Blo 503794 12271931 := bstep (se 1 (by rfl) ⟨9203948, by rfl⟩ : syracuseStep 12271931 = 18407897) B18407897
theorem B541723 : Blo 503794 541723 := bstep (se 1 (by rfl) ⟨406292, by rfl⟩ : syracuseStep 541723 = 812585) B812585
theorem B3852521 : Blo 503794 3852521 := bstep (se 2 (by rfl) ⟨1444695, by rfl⟩ : syracuseStep 3852521 = 2889391) B2889391
theorem B4311467 : Blo 503794 4311467 := bstep (se 1 (by rfl) ⟨3233600, by rfl⟩ : syracuseStep 4311467 = 6467201) B6467201
theorem B2870255 : Blo 503794 2870255 := bstep (se 1 (by rfl) ⟨2152691, by rfl⟩ : syracuseStep 2870255 = 4305383) B4305383
theorem B1133639 : Blo 503794 1133639 := bstep (se 1 (by rfl) ⟨850229, by rfl⟩ : syracuseStep 1133639 = 1700459) B1700459
theorem B1137023 : Blo 503794 1137023 := bstep (se 1 (by rfl) ⟨852767, by rfl⟩ : syracuseStep 1137023 = 1705535) B1705535
theorem B1140191 : Blo 503794 1140191 := bstep (se 1 (by rfl) ⟨855143, by rfl⟩ : syracuseStep 1140191 = 1710287) B1710287
theorem B1435391 : Blo 503794 1435391 := bstep (se 1 (by rfl) ⟨1076543, by rfl⟩ : syracuseStep 1435391 = 2153087) B2153087
theorem B10938827 : Blo 503794 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B1438249 : Blo 503794 1438249 := bstep (se 2 (by rfl) ⟨539343, by rfl⟩ : syracuseStep 1438249 = 1078687) B1078687
theorem B1439183 : Blo 503794 1439183 := bstep (se 1 (by rfl) ⟨1079387, by rfl⟩ : syracuseStep 1439183 = 2158775) B2158775
theorem B2161235 : Blo 503794 2161235 := bstep (se 1 (by rfl) ⟨1620926, by rfl⟩ : syracuseStep 2161235 = 3241853) B3241853
theorem B3081199 : Blo 503794 3081199 := bstep (se 1 (by rfl) ⟨2310899, by rfl⟩ : syracuseStep 3081199 = 4621799) B4621799
theorem B722297 : Blo 503794 722297 := bstep (se 2 (by rfl) ⟨270861, by rfl⟩ : syracuseStep 722297 = 541723) B541723
theorem B755759 : Blo 503794 755759 := bstep (se 1 (by rfl) ⟨566819, by rfl⟩ : syracuseStep 755759 = 1133639) B1133639
theorem B758015 : Blo 503794 758015 := bstep (se 1 (by rfl) ⟨568511, by rfl⟩ : syracuseStep 758015 = 1137023) B1137023
theorem B856831 : Blo 503794 856831 := bstep (se 1 (by rfl) ⟨642623, by rfl⟩ : syracuseStep 856831 = 1285247) B1285247
theorem B10949899 : Blo 503794 10949899 := bstep (se 1 (by rfl) ⟨8212424, by rfl⟩ : syracuseStep 10949899 = 16424849) B16424849
theorem B760127 : Blo 503794 760127 := bstep (se 1 (by rfl) ⟨570095, by rfl⟩ : syracuseStep 760127 = 1140191) B1140191
theorem B956927 : Blo 503794 956927 := bstep (se 1 (by rfl) ⟨717695, by rfl⟩ : syracuseStep 956927 = 1435391) B1435391
theorem B29170205 : Blo 503794 29170205 := bstep (se 3 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 29170205 = 10938827) B10938827
theorem B959455 : Blo 503794 959455 := bstep (se 1 (by rfl) ⟨719591, by rfl⟩ : syracuseStep 959455 = 1439183) B1439183
theorem B569191 : Blo 503794 569191 := bstep (se 1 (by rfl) ⟨426893, by rfl⟩ : syracuseStep 569191 = 853787) B853787
theorem B2568347 : Blo 503794 2568347 := bstep (se 1 (by rfl) ⟨1926260, by rfl⟩ : syracuseStep 2568347 = 3852521) B3852521
theorem B1913503 : Blo 503794 1913503 := bstep (se 1 (by rfl) ⟨1435127, by rfl⟩ : syracuseStep 1913503 = 2870255) B2870255
theorem B13153063 : Blo 503794 13153063 := bstep (se 1 (by rfl) ⟨9864797, by rfl⟩ : syracuseStep 13153063 = 19729595) B19729595
theorem B504767 : Blo 503794 504767 := bstep (se 1 (by rfl) ⟨378575, by rfl⟩ : syracuseStep 504767 = 757151) B757151
theorem B505247 : Blo 503794 505247 := bstep (se 1 (by rfl) ⟨378935, by rfl⟩ : syracuseStep 505247 = 757871) B757871
theorem B570847 : Blo 503794 570847 := bstep (se 1 (by rfl) ⟨428135, by rfl⟩ : syracuseStep 570847 = 856271) B856271
theorem B507495 : Blo 503794 507495 := bstep (se 1 (by rfl) ⟨380621, by rfl⟩ : syracuseStep 507495 = 761243) B761243
theorem B1917665 : Blo 503794 1917665 := bstep (se 2 (by rfl) ⟨719124, by rfl⟩ : syracuseStep 1917665 = 1438249) B1438249
theorem B8181287 : Blo 503794 8181287 := bstep (se 1 (by rfl) ⟨6135965, by rfl⟩ : syracuseStep 8181287 = 12271931) B12271931
theorem B2742493 : Blo 503794 2742493 := bstep (se 3 (by rfl) ⟨514217, by rfl⟩ : syracuseStep 2742493 = 1028435) B1028435
theorem B2874311 : Blo 503794 2874311 := bstep (se 1 (by rfl) ⟨2155733, by rfl⟩ : syracuseStep 2874311 = 4311467) B4311467
theorem B1925167 : Blo 503794 1925167 := bstep (se 1 (by rfl) ⟨1443875, by rfl⟩ : syracuseStep 1925167 = 2887751) B2887751
theorem B811271 : Blo 503794 811271 := bstep (se 1 (by rfl) ⟨608453, by rfl⟩ : syracuseStep 811271 = 1216907) B1216907
theorem B1141289 : Blo 503794 1141289 := bstep (se 2 (by rfl) ⟨427983, by rfl⟩ : syracuseStep 1141289 = 855967) B855967
theorem B1733023 : Blo 503794 1733023 := bstep (se 1 (by rfl) ⟨1299767, by rfl⟩ : syracuseStep 1733023 = 2599535) B2599535
theorem B1440823 : Blo 503794 1440823 := bstep (se 1 (by rfl) ⟨1080617, by rfl⟩ : syracuseStep 1440823 = 2161235) B2161235
theorem B1278443 : Blo 503794 1278443 := bstep (se 1 (by rfl) ⟨958832, by rfl⟩ : syracuseStep 1278443 = 1917665) B1917665
theorem B1279273 : Blo 503794 1279273 := bstep (se 2 (by rfl) ⟨479727, by rfl⟩ : syracuseStep 1279273 = 959455) B959455
theorem B758921 : Blo 503794 758921 := bstep (se 2 (by rfl) ⟨284595, by rfl⟩ : syracuseStep 758921 = 569191) B569191
theorem B17537417 : Blo 503794 17537417 := bstep (se 2 (by rfl) ⟨6576531, by rfl⟩ : syracuseStep 17537417 = 13153063) B13153063
theorem B760859 : Blo 503794 760859 := bstep (se 1 (by rfl) ⟨570644, by rfl⟩ : syracuseStep 760859 = 1141289) B1141289
theorem B761129 : Blo 503794 761129 := bstep (se 2 (by rfl) ⟨285423, by rfl⟩ : syracuseStep 761129 = 570847) B570847
theorem B1712231 : Blo 503794 1712231 := bstep (se 1 (by rfl) ⟨1284173, by rfl⟩ : syracuseStep 1712231 = 2568347) B2568347
theorem B2566889 : Blo 503794 2566889 := bstep (se 2 (by rfl) ⟨962583, by rfl⟩ : syracuseStep 2566889 = 1925167) B1925167
theorem B4108265 : Blo 503794 4108265 := bstep (se 2 (by rfl) ⟨1540599, by rfl⟩ : syracuseStep 4108265 = 3081199) B3081199
theorem B503839 : Blo 503794 503839 := bstep (se 1 (by rfl) ⟨377879, by rfl⟩ : syracuseStep 503839 = 755759) B755759
theorem B505343 : Blo 503794 505343 := bstep (se 1 (by rfl) ⟨379007, by rfl⟩ : syracuseStep 505343 = 758015) B758015
theorem B5454191 : Blo 503794 5454191 := bstep (se 1 (by rfl) ⟨4090643, by rfl⟩ : syracuseStep 5454191 = 8181287) B8181287
theorem B506751 : Blo 503794 506751 := bstep (se 1 (by rfl) ⟨380063, by rfl⟩ : syracuseStep 506751 = 760127) B760127
theorem B637951 : Blo 503794 637951 := bstep (se 1 (by rfl) ⟨478463, by rfl⟩ : syracuseStep 637951 = 956927) B956927
theorem B19446803 : Blo 503794 19446803 := bstep (se 1 (by rfl) ⟨14585102, by rfl⟩ : syracuseStep 19446803 = 29170205) B29170205
theorem B1916207 : Blo 503794 1916207 := bstep (se 1 (by rfl) ⟨1437155, by rfl⟩ : syracuseStep 1916207 = 2874311) B2874311
theorem B540847 : Blo 503794 540847 := bstep (se 1 (by rfl) ⟨405635, by rfl⟩ : syracuseStep 540847 = 811271) B811271
theorem B2310697 : Blo 503794 2310697 := bstep (se 2 (by rfl) ⟨866511, by rfl⟩ : syracuseStep 2310697 = 1733023) B1733023
theorem B14599865 : Blo 503794 14599865 := bstep (se 2 (by rfl) ⟨5474949, by rfl⟩ : syracuseStep 14599865 = 10949899) B10949899
theorem B3656657 : Blo 503794 3656657 := bstep (se 2 (by rfl) ⟨1371246, by rfl⟩ : syracuseStep 3656657 = 2742493) B2742493
theorem B1921097 : Blo 503794 1921097 := bstep (se 2 (by rfl) ⟨720411, by rfl⟩ : syracuseStep 1921097 = 1440823) B1440823
theorem B1926125 : Blo 503794 1926125 := bstep (se 3 (by rfl) ⟨361148, by rfl⟩ : syracuseStep 1926125 = 722297) B722297
theorem B2551337 : Blo 503794 2551337 := bstep (se 2 (by rfl) ⟨956751, by rfl⟩ : syracuseStep 2551337 = 1913503) B1913503
theorem B1142441 : Blo 503794 1142441 := bstep (se 2 (by rfl) ⟨428415, by rfl⟩ : syracuseStep 1142441 = 856831) B856831
theorem B852295 : Blo 503794 852295 := bstep (se 1 (by rfl) ⟨639221, by rfl⟩ : syracuseStep 852295 = 1278443) B1278443
theorem B3080929 : Blo 503794 3080929 := bstep (se 2 (by rfl) ⟨1155348, by rfl⟩ : syracuseStep 3080929 = 2310697) B2310697
theorem B2884517 : Blo 503794 2884517 := bstep (se 4 (by rfl) ⟨270423, by rfl⟩ : syracuseStep 2884517 = 540847) B540847
theorem B9733243 : Blo 503794 9733243 := bstep (se 1 (by rfl) ⟨7299932, by rfl⟩ : syracuseStep 9733243 = 14599865) B14599865
theorem B1705697 : Blo 503794 1705697 := bstep (se 2 (by rfl) ⟨639636, by rfl⟩ : syracuseStep 1705697 = 1279273) B1279273
theorem B1280731 : Blo 503794 1280731 := bstep (se 1 (by rfl) ⟨960548, by rfl⟩ : syracuseStep 1280731 = 1921097) B1921097
theorem B1284083 : Blo 503794 1284083 := bstep (se 1 (by rfl) ⟨963062, by rfl⟩ : syracuseStep 1284083 = 1926125) B1926125
theorem B1711259 : Blo 503794 1711259 := bstep (se 1 (by rfl) ⟨1283444, by rfl⟩ : syracuseStep 1711259 = 2566889) B2566889
theorem B761627 : Blo 503794 761627 := bstep (se 1 (by rfl) ⟨571220, by rfl⟩ : syracuseStep 761627 = 1142441) B1142441
theorem B2437771 : Blo 503794 2437771 := bstep (se 1 (by rfl) ⟨1828328, by rfl⟩ : syracuseStep 2437771 = 3656657) B3656657
theorem B505947 : Blo 503794 505947 := bstep (se 1 (by rfl) ⟨379460, by rfl⟩ : syracuseStep 505947 = 758921) B758921
theorem B507239 : Blo 503794 507239 := bstep (se 1 (by rfl) ⟨380429, by rfl⟩ : syracuseStep 507239 = 760859) B760859
theorem B507419 : Blo 503794 507419 := bstep (se 1 (by rfl) ⟨380564, by rfl⟩ : syracuseStep 507419 = 761129) B761129
theorem B2738843 : Blo 503794 2738843 := bstep (se 1 (by rfl) ⟨2054132, by rfl⟩ : syracuseStep 2738843 = 4108265) B4108265
theorem B12964535 : Blo 503794 12964535 := bstep (se 1 (by rfl) ⟨9723401, by rfl⟩ : syracuseStep 12964535 = 19446803) B19446803
theorem B11691611 : Blo 503794 11691611 := bstep (se 1 (by rfl) ⟨8768708, by rfl⟩ : syracuseStep 11691611 = 17537417) B17537417
theorem B1141487 : Blo 503794 1141487 := bstep (se 1 (by rfl) ⟨856115, by rfl⟩ : syracuseStep 1141487 = 1712231) B1712231
theorem B1700891 : Blo 503794 1700891 := bstep (se 1 (by rfl) ⟨1275668, by rfl⟩ : syracuseStep 1700891 = 2551337) B2551337
theorem B850601 : Blo 503794 850601 := bstep (se 2 (by rfl) ⟨318975, by rfl⟩ : syracuseStep 850601 = 637951) B637951
theorem B3636127 : Blo 503794 3636127 := bstep (se 1 (by rfl) ⟨2727095, by rfl⟩ : syracuseStep 3636127 = 5454191) B5454191
theorem B1277471 : Blo 503794 1277471 := bstep (se 1 (by rfl) ⟨958103, by rfl⟩ : syracuseStep 1277471 = 1916207) B1916207
theorem B12977657 : Blo 503794 12977657 := bstep (se 2 (by rfl) ⟨4866621, by rfl⟩ : syracuseStep 12977657 = 9733243) B9733243
theorem B1707641 : Blo 503794 1707641 := bstep (se 2 (by rfl) ⟨640365, by rfl⟩ : syracuseStep 1707641 = 1280731) B1280731
theorem B856055 : Blo 503794 856055 := bstep (se 1 (by rfl) ⟨642041, by rfl⟩ : syracuseStep 856055 = 1284083) B1284083
theorem B3250361 : Blo 503794 3250361 := bstep (se 2 (by rfl) ⟨1218885, by rfl⟩ : syracuseStep 3250361 = 2437771) B2437771
theorem B760991 : Blo 503794 760991 := bstep (se 1 (by rfl) ⟨570743, by rfl⟩ : syracuseStep 760991 = 1141487) B1141487
theorem B567067 : Blo 503794 567067 := bstep (se 1 (by rfl) ⟨425300, by rfl⟩ : syracuseStep 567067 = 850601) B850601
theorem B4107905 : Blo 503794 4107905 := bstep (se 2 (by rfl) ⟨1540464, by rfl⟩ : syracuseStep 4107905 = 3080929) B3080929
theorem B507751 : Blo 503794 507751 := bstep (se 1 (by rfl) ⟨380813, by rfl⟩ : syracuseStep 507751 = 761627) B761627
theorem B1133927 : Blo 503794 1133927 := bstep (se 1 (by rfl) ⟨850445, by rfl⟩ : syracuseStep 1133927 = 1700891) B1700891
theorem B1136393 : Blo 503794 1136393 := bstep (se 2 (by rfl) ⟨426147, by rfl⟩ : syracuseStep 1136393 = 852295) B852295
theorem B1923011 : Blo 503794 1923011 := bstep (se 1 (by rfl) ⟨1442258, by rfl⟩ : syracuseStep 1923011 = 2884517) B2884517
theorem B1137131 : Blo 503794 1137131 := bstep (se 1 (by rfl) ⟨852848, by rfl⟩ : syracuseStep 1137131 = 1705697) B1705697
theorem B1825895 : Blo 503794 1825895 := bstep (se 1 (by rfl) ⟨1369421, by rfl⟩ : syracuseStep 1825895 = 2738843) B2738843
theorem B8643023 : Blo 503794 8643023 := bstep (se 1 (by rfl) ⟨6482267, by rfl⟩ : syracuseStep 8643023 = 12964535) B12964535
theorem B1140839 : Blo 503794 1140839 := bstep (se 1 (by rfl) ⟨855629, by rfl⟩ : syracuseStep 1140839 = 1711259) B1711259
theorem B7794407 : Blo 503794 7794407 := bstep (se 1 (by rfl) ⟨5845805, by rfl⟩ : syracuseStep 7794407 = 11691611) B11691611
theorem B4848169 : Blo 503794 4848169 := bstep (se 2 (by rfl) ⟨1818063, by rfl⟩ : syracuseStep 4848169 = 3636127) B3636127
theorem B851647 : Blo 503794 851647 := bstep (se 1 (by rfl) ⟨638735, by rfl⟩ : syracuseStep 851647 = 1277471) B1277471
theorem B8651771 : Blo 503794 8651771 := bstep (se 1 (by rfl) ⟨6488828, by rfl⟩ : syracuseStep 8651771 = 12977657) B12977657
theorem B755951 : Blo 503794 755951 := bstep (se 1 (by rfl) ⟨566963, by rfl⟩ : syracuseStep 755951 = 1133927) B1133927
theorem B756089 : Blo 503794 756089 := bstep (se 2 (by rfl) ⟨283533, by rfl⟩ : syracuseStep 756089 = 567067) B567067
theorem B757595 : Blo 503794 757595 := bstep (se 1 (by rfl) ⟨568196, by rfl⟩ : syracuseStep 757595 = 1136393) B1136393
theorem B1282007 : Blo 503794 1282007 := bstep (se 1 (by rfl) ⟨961505, by rfl⟩ : syracuseStep 1282007 = 1923011) B1923011
theorem B2166907 : Blo 503794 2166907 := bstep (se 1 (by rfl) ⟨1625180, by rfl⟩ : syracuseStep 2166907 = 3250361) B3250361
theorem B758087 : Blo 503794 758087 := bstep (se 1 (by rfl) ⟨568565, by rfl⟩ : syracuseStep 758087 = 1137131) B1137131
theorem B1217263 : Blo 503794 1217263 := bstep (se 1 (by rfl) ⟨912947, by rfl⟩ : syracuseStep 1217263 = 1825895) B1825895
theorem B760559 : Blo 503794 760559 := bstep (se 1 (by rfl) ⟨570419, by rfl⟩ : syracuseStep 760559 = 1140839) B1140839
theorem B6464225 : Blo 503794 6464225 := bstep (se 2 (by rfl) ⟨2424084, by rfl⟩ : syracuseStep 6464225 = 4848169) B4848169
theorem B570703 : Blo 503794 570703 := bstep (se 1 (by rfl) ⟨428027, by rfl⟩ : syracuseStep 570703 = 856055) B856055
theorem B507327 : Blo 503794 507327 := bstep (se 1 (by rfl) ⟨380495, by rfl⟩ : syracuseStep 507327 = 760991) B760991
theorem B2738603 : Blo 503794 2738603 := bstep (se 1 (by rfl) ⟨2053952, by rfl⟩ : syracuseStep 2738603 = 4107905) B4107905
theorem B5196271 : Blo 503794 5196271 := bstep (se 1 (by rfl) ⟨3897203, by rfl⟩ : syracuseStep 5196271 = 7794407) B7794407
theorem B1135529 : Blo 503794 1135529 := bstep (se 2 (by rfl) ⟨425823, by rfl⟩ : syracuseStep 1135529 = 851647) B851647
theorem B1138427 : Blo 503794 1138427 := bstep (se 1 (by rfl) ⟨853820, by rfl⟩ : syracuseStep 1138427 = 1707641) B1707641
theorem B5762015 : Blo 503794 5762015 := bstep (se 1 (by rfl) ⟨4321511, by rfl⟩ : syracuseStep 5762015 = 8643023) B8643023
theorem B5767847 : Blo 503794 5767847 := bstep (se 1 (by rfl) ⟨4325885, by rfl⟩ : syracuseStep 5767847 = 8651771) B8651771
theorem B854671 : Blo 503794 854671 := bstep (se 1 (by rfl) ⟨641003, by rfl⟩ : syracuseStep 854671 = 1282007) B1282007
theorem B757019 : Blo 503794 757019 := bstep (se 1 (by rfl) ⟨567764, by rfl⟩ : syracuseStep 757019 = 1135529) B1135529
theorem B758951 : Blo 503794 758951 := bstep (se 1 (by rfl) ⟨569213, by rfl⟩ : syracuseStep 758951 = 1138427) B1138427
theorem B2889209 : Blo 503794 2889209 := bstep (se 2 (by rfl) ⟨1083453, by rfl⟩ : syracuseStep 2889209 = 2166907) B2166907
theorem B760937 : Blo 503794 760937 := bstep (se 2 (by rfl) ⟨285351, by rfl⟩ : syracuseStep 760937 = 570703) B570703
theorem B3841343 : Blo 503794 3841343 := bstep (se 1 (by rfl) ⟨2881007, by rfl⟩ : syracuseStep 3841343 = 5762015) B5762015
theorem B503967 : Blo 503794 503967 := bstep (se 1 (by rfl) ⟨377975, by rfl⟩ : syracuseStep 503967 = 755951) B755951
theorem B504059 : Blo 503794 504059 := bstep (se 1 (by rfl) ⟨378044, by rfl⟩ : syracuseStep 504059 = 756089) B756089
theorem B505063 : Blo 503794 505063 := bstep (se 1 (by rfl) ⟨378797, by rfl⟩ : syracuseStep 505063 = 757595) B757595
theorem B505391 : Blo 503794 505391 := bstep (se 1 (by rfl) ⟨379043, by rfl⟩ : syracuseStep 505391 = 758087) B758087
theorem B6928361 : Blo 503794 6928361 := bstep (se 2 (by rfl) ⟨2598135, by rfl⟩ : syracuseStep 6928361 = 5196271) B5196271
theorem B507039 : Blo 503794 507039 := bstep (se 1 (by rfl) ⟨380279, by rfl⟩ : syracuseStep 507039 = 760559) B760559
theorem B4309483 : Blo 503794 4309483 := bstep (se 1 (by rfl) ⟨3232112, by rfl⟩ : syracuseStep 4309483 = 6464225) B6464225
theorem B1623017 : Blo 503794 1623017 := bstep (se 2 (by rfl) ⟨608631, by rfl⟩ : syracuseStep 1623017 = 1217263) B1217263
theorem B1825735 : Blo 503794 1825735 := bstep (se 1 (by rfl) ⟨1369301, by rfl⟩ : syracuseStep 1825735 = 2738603) B2738603
theorem B1082011 : Blo 503794 1082011 := bstep (se 1 (by rfl) ⟨811508, by rfl⟩ : syracuseStep 1082011 = 1623017) B1623017
theorem B2560895 : Blo 503794 2560895 := bstep (se 1 (by rfl) ⟨1920671, by rfl⟩ : syracuseStep 2560895 = 3841343) B3841343
theorem B2434313 : Blo 503794 2434313 := bstep (se 2 (by rfl) ⟨912867, by rfl⟩ : syracuseStep 2434313 = 1825735) B1825735
theorem B3845231 : Blo 503794 3845231 := bstep (se 1 (by rfl) ⟨2883923, by rfl⟩ : syracuseStep 3845231 = 5767847) B5767847
theorem B5745977 : Blo 503794 5745977 := bstep (se 2 (by rfl) ⟨2154741, by rfl⟩ : syracuseStep 5745977 = 4309483) B4309483
theorem B504679 : Blo 503794 504679 := bstep (se 1 (by rfl) ⟨378509, by rfl⟩ : syracuseStep 504679 = 757019) B757019
theorem B505967 : Blo 503794 505967 := bstep (se 1 (by rfl) ⟨379475, by rfl⟩ : syracuseStep 505967 = 758951) B758951
theorem B507291 : Blo 503794 507291 := bstep (se 1 (by rfl) ⟨380468, by rfl⟩ : syracuseStep 507291 = 760937) B760937
theorem B1139561 : Blo 503794 1139561 := bstep (se 2 (by rfl) ⟨427335, by rfl⟩ : syracuseStep 1139561 = 854671) B854671
theorem B1926139 : Blo 503794 1926139 := bstep (se 1 (by rfl) ⟨1444604, by rfl⟩ : syracuseStep 1926139 = 2889209) B2889209
theorem B4618907 : Blo 503794 4618907 := bstep (se 1 (by rfl) ⟨3464180, by rfl⟩ : syracuseStep 4618907 = 6928361) B6928361
theorem B1442681 : Blo 503794 1442681 := bstep (se 2 (by rfl) ⟨541005, by rfl⟩ : syracuseStep 1442681 = 1082011) B1082011
theorem B1707263 : Blo 503794 1707263 := bstep (se 1 (by rfl) ⟨1280447, by rfl⟩ : syracuseStep 1707263 = 2560895) B2560895
theorem B759707 : Blo 503794 759707 := bstep (se 1 (by rfl) ⟨569780, by rfl⟩ : syracuseStep 759707 = 1139561) B1139561
theorem B2563487 : Blo 503794 2563487 := bstep (se 1 (by rfl) ⟨1922615, by rfl⟩ : syracuseStep 2563487 = 3845231) B3845231
theorem B2568185 : Blo 503794 2568185 := bstep (se 2 (by rfl) ⟨963069, by rfl⟩ : syracuseStep 2568185 = 1926139) B1926139
theorem B1622875 : Blo 503794 1622875 := bstep (se 1 (by rfl) ⟨1217156, by rfl⟩ : syracuseStep 1622875 = 2434313) B2434313
theorem B3830651 : Blo 503794 3830651 := bstep (se 1 (by rfl) ⟨2872988, by rfl⟩ : syracuseStep 3830651 = 5745977) B5745977
theorem B3079271 : Blo 503794 3079271 := bstep (se 1 (by rfl) ⟨2309453, by rfl⟩ : syracuseStep 3079271 = 4618907) B4618907
theorem B2163833 : Blo 503794 2163833 := bstep (se 2 (by rfl) ⟨811437, by rfl⟩ : syracuseStep 2163833 = 1622875) B1622875
theorem B1708991 : Blo 503794 1708991 := bstep (se 1 (by rfl) ⟨1281743, by rfl⟩ : syracuseStep 1708991 = 2563487) B2563487
theorem B1712123 : Blo 503794 1712123 := bstep (se 1 (by rfl) ⟨1284092, by rfl⟩ : syracuseStep 1712123 = 2568185) B2568185
theorem B961787 : Blo 503794 961787 := bstep (se 1 (by rfl) ⟨721340, by rfl⟩ : syracuseStep 961787 = 1442681) B1442681
theorem B506471 : Blo 503794 506471 := bstep (se 1 (by rfl) ⟨379853, by rfl⟩ : syracuseStep 506471 = 759707) B759707
theorem B2052847 : Blo 503794 2052847 := bstep (se 1 (by rfl) ⟨1539635, by rfl⟩ : syracuseStep 2052847 = 3079271) B3079271
theorem B1138175 : Blo 503794 1138175 := bstep (se 1 (by rfl) ⟨853631, by rfl⟩ : syracuseStep 1138175 = 1707263) B1707263
theorem B2553767 : Blo 503794 2553767 := bstep (se 1 (by rfl) ⟨1915325, by rfl⟩ : syracuseStep 2553767 = 3830651) B3830651
theorem B1442555 : Blo 503794 1442555 := bstep (se 1 (by rfl) ⟨1081916, by rfl⟩ : syracuseStep 1442555 = 2163833) B2163833
theorem B10948517 : Blo 503794 10948517 := bstep (se 4 (by rfl) ⟨1026423, by rfl⟩ : syracuseStep 10948517 = 2052847) B2052847
theorem B758783 : Blo 503794 758783 := bstep (se 1 (by rfl) ⟨569087, by rfl⟩ : syracuseStep 758783 = 1138175) B1138175
theorem B641191 : Blo 503794 641191 := bstep (se 1 (by rfl) ⟨480893, by rfl⟩ : syracuseStep 641191 = 961787) B961787
theorem B1139327 : Blo 503794 1139327 := bstep (se 1 (by rfl) ⟨854495, by rfl⟩ : syracuseStep 1139327 = 1708991) B1708991
theorem B1141415 : Blo 503794 1141415 := bstep (se 1 (by rfl) ⟨856061, by rfl⟩ : syracuseStep 1141415 = 1712123) B1712123
theorem B1702511 : Blo 503794 1702511 := bstep (se 1 (by rfl) ⟨1276883, by rfl⟩ : syracuseStep 1702511 = 2553767) B2553767
theorem B854921 : Blo 503794 854921 := bstep (se 2 (by rfl) ⟨320595, by rfl⟩ : syracuseStep 854921 = 641191) B641191
theorem B759551 : Blo 503794 759551 := bstep (se 1 (by rfl) ⟨569663, by rfl⟩ : syracuseStep 759551 = 1139327) B1139327
theorem B760943 : Blo 503794 760943 := bstep (se 1 (by rfl) ⟨570707, by rfl⟩ : syracuseStep 760943 = 1141415) B1141415
theorem B961703 : Blo 503794 961703 := bstep (se 1 (by rfl) ⟨721277, by rfl⟩ : syracuseStep 961703 = 1442555) B1442555
theorem B505855 : Blo 503794 505855 := bstep (se 1 (by rfl) ⟨379391, by rfl⟩ : syracuseStep 505855 = 758783) B758783
theorem B1135007 : Blo 503794 1135007 := bstep (se 1 (by rfl) ⟨851255, by rfl⟩ : syracuseStep 1135007 = 1702511) B1702511
theorem B7299011 : Blo 503794 7299011 := bstep (se 1 (by rfl) ⟨5474258, by rfl⟩ : syracuseStep 7299011 = 10948517) B10948517
theorem B756671 : Blo 503794 756671 := bstep (se 1 (by rfl) ⟨567503, by rfl⟩ : syracuseStep 756671 = 1135007) B1135007
theorem B569947 : Blo 503794 569947 := bstep (se 1 (by rfl) ⟨427460, by rfl⟩ : syracuseStep 569947 = 854921) B854921
theorem B506367 : Blo 503794 506367 := bstep (se 1 (by rfl) ⟨379775, by rfl⟩ : syracuseStep 506367 = 759551) B759551
theorem B507295 : Blo 503794 507295 := bstep (se 1 (by rfl) ⟨380471, by rfl⟩ : syracuseStep 507295 = 760943) B760943
theorem B4866007 : Blo 503794 4866007 := bstep (se 1 (by rfl) ⟨3649505, by rfl⟩ : syracuseStep 4866007 = 7299011) B7299011
theorem B641135 : Blo 503794 641135 := bstep (se 1 (by rfl) ⟨480851, by rfl⟩ : syracuseStep 641135 = 961703) B961703
theorem B1709693 : Blo 503794 1709693 := bstep (se 3 (by rfl) ⟨320567, by rfl⟩ : syracuseStep 1709693 = 641135) B641135
theorem B759929 : Blo 503794 759929 := bstep (se 2 (by rfl) ⟨284973, by rfl⟩ : syracuseStep 759929 = 569947) B569947
theorem B504447 : Blo 503794 504447 := bstep (se 1 (by rfl) ⟨378335, by rfl⟩ : syracuseStep 504447 = 756671) B756671
theorem B6488009 : Blo 503794 6488009 := bstep (se 2 (by rfl) ⟨2433003, by rfl⟩ : syracuseStep 6488009 = 4866007) B4866007
theorem B506619 : Blo 503794 506619 := bstep (se 1 (by rfl) ⟨379964, by rfl⟩ : syracuseStep 506619 = 759929) B759929
theorem B1139795 : Blo 503794 1139795 := bstep (se 1 (by rfl) ⟨854846, by rfl⟩ : syracuseStep 1139795 = 1709693) B1709693
theorem B4325339 : Blo 503794 4325339 := bstep (se 1 (by rfl) ⟨3244004, by rfl⟩ : syracuseStep 4325339 = 6488009) B6488009
theorem B759863 : Blo 503794 759863 := bstep (se 1 (by rfl) ⟨569897, by rfl⟩ : syracuseStep 759863 = 1139795) B1139795
theorem B2883559 : Blo 503794 2883559 := bstep (se 1 (by rfl) ⟨2162669, by rfl⟩ : syracuseStep 2883559 = 4325339) B4325339
theorem B3844745 : Blo 503794 3844745 := bstep (se 2 (by rfl) ⟨1441779, by rfl⟩ : syracuseStep 3844745 = 2883559) B2883559
theorem B506575 : Blo 503794 506575 := bstep (se 1 (by rfl) ⟨379931, by rfl⟩ : syracuseStep 506575 = 759863) B759863
theorem B2563163 : Blo 503794 2563163 := bstep (se 1 (by rfl) ⟨1922372, by rfl⟩ : syracuseStep 2563163 = 3844745) B3844745
theorem B1708775 : Blo 503794 1708775 := bstep (se 1 (by rfl) ⟨1281581, by rfl⟩ : syracuseStep 1708775 = 2563163) B2563163
theorem B1139183 : Blo 503794 1139183 := bstep (se 1 (by rfl) ⟨854387, by rfl⟩ : syracuseStep 1139183 = 1708775) B1708775
theorem B759455 : Blo 503794 759455 := bstep (se 1 (by rfl) ⟨569591, by rfl⟩ : syracuseStep 759455 = 1139183) B1139183
theorem B506303 : Blo 503794 506303 := bstep (se 1 (by rfl) ⟨379727, by rfl⟩ : syracuseStep 506303 = 759455) B759455

theorem C0 (j : ℕ) (h1 : 125948 ≤ j) (h2 : j ≤ 126647) : Blo 503794 (4 * j + 3) := by
  interval_cases j
  · exact B503795
  · exact B503799
  · exact B503803
  · exact B503807
  · exact B503811
  · exact B503815
  · exact B503819
  · exact B503823
  · exact B503827
  · exact B503831
  · exact B503835
  · exact B503839
  · exact B503843
  · exact B503847
  · exact B503851
  · exact B503855
  · exact B503859
  · exact B503863
  · exact B503867
  · exact B503871
  · exact B503875
  · exact B503879
  · exact B503883
  · exact B503887
  · exact B503891
  · exact B503895
  · exact B503899
  · exact B503903
  · exact B503907
  · exact B503911
  · exact B503915
  · exact B503919
  · exact B503923
  · exact B503927
  · exact B503931
  · exact B503935
  · exact B503939
  · exact B503943
  · exact B503947
  · exact B503951
  · exact B503955
  · exact B503959
  · exact B503963
  · exact B503967
  · exact B503971
  · exact B503975
  · exact B503979
  · exact B503983
  · exact B503987
  · exact B503991
  · exact B503995
  · exact B503999
  · exact B504003
  · exact B504007
  · exact B504011
  · exact B504015
  · exact B504019
  · exact B504023
  · exact B504027
  · exact B504031
  · exact B504035
  · exact B504039
  · exact B504043
  · exact B504047
  · exact B504051
  · exact B504055
  · exact B504059
  · exact B504063
  · exact B504067
  · exact B504071
  · exact B504075
  · exact B504079
  · exact B504083
  · exact B504087
  · exact B504091
  · exact B504095
  · exact B504099
  · exact B504103
  · exact B504107
  · exact B504111
  · exact B504115
  · exact B504119
  · exact B504123
  · exact B504127
  · exact B504131
  · exact B504135
  · exact B504139
  · exact B504143
  · exact B504147
  · exact B504151
  · exact B504155
  · exact B504159
  · exact B504163
  · exact B504167
  · exact B504171
  · exact B504175
  · exact B504179
  · exact B504183
  · exact B504187
  · exact B504191
  · exact B504195
  · exact B504199
  · exact B504203
  · exact B504207
  · exact B504211
  · exact B504215
  · exact B504219
  · exact B504223
  · exact B504227
  · exact B504231
  · exact B504235
  · exact B504239
  · exact B504243
  · exact B504247
  · exact B504251
  · exact B504255
  · exact B504259
  · exact B504263
  · exact B504267
  · exact B504271
  · exact B504275
  · exact B504279
  · exact B504283
  · exact B504287
  · exact B504291
  · exact B504295
  · exact B504299
  · exact B504303
  · exact B504307
  · exact B504311
  · exact B504315
  · exact B504319
  · exact B504323
  · exact B504327
  · exact B504331
  · exact B504335
  · exact B504339
  · exact B504343
  · exact B504347
  · exact B504351
  · exact B504355
  · exact B504359
  · exact B504363
  · exact B504367
  · exact B504371
  · exact B504375
  · exact B504379
  · exact B504383
  · exact B504387
  · exact B504391
  · exact B504395
  · exact B504399
  · exact B504403
  · exact B504407
  · exact B504411
  · exact B504415
  · exact B504419
  · exact B504423
  · exact B504427
  · exact B504431
  · exact B504435
  · exact B504439
  · exact B504443
  · exact B504447
  · exact B504451
  · exact B504455
  · exact B504459
  · exact B504463
  · exact B504467
  · exact B504471
  · exact B504475
  · exact B504479
  · exact B504483
  · exact B504487
  · exact B504491
  · exact B504495
  · exact B504499
  · exact B504503
  · exact B504507
  · exact B504511
  · exact B504515
  · exact B504519
  · exact B504523
  · exact B504527
  · exact B504531
  · exact B504535
  · exact B504539
  · exact B504543
  · exact B504547
  · exact B504551
  · exact B504555
  · exact B504559
  · exact B504563
  · exact B504567
  · exact B504571
  · exact B504575
  · exact B504579
  · exact B504583
  · exact B504587
  · exact B504591
  · exact B504595
  · exact B504599
  · exact B504603
  · exact B504607
  · exact B504611
  · exact B504615
  · exact B504619
  · exact B504623
  · exact B504627
  · exact B504631
  · exact B504635
  · exact B504639
  · exact B504643
  · exact B504647
  · exact B504651
  · exact B504655
  · exact B504659
  · exact B504663
  · exact B504667
  · exact B504671
  · exact B504675
  · exact B504679
  · exact B504683
  · exact B504687
  · exact B504691
  · exact B504695
  · exact B504699
  · exact B504703
  · exact B504707
  · exact B504711
  · exact B504715
  · exact B504719
  · exact B504723
  · exact B504727
  · exact B504731
  · exact B504735
  · exact B504739
  · exact B504743
  · exact B504747
  · exact B504751
  · exact B504755
  · exact B504759
  · exact B504763
  · exact B504767
  · exact B504771
  · exact B504775
  · exact B504779
  · exact B504783
  · exact B504787
  · exact B504791
  · exact B504795
  · exact B504799
  · exact B504803
  · exact B504807
  · exact B504811
  · exact B504815
  · exact B504819
  · exact B504823
  · exact B504827
  · exact B504831
  · exact B504835
  · exact B504839
  · exact B504843
  · exact B504847
  · exact B504851
  · exact B504855
  · exact B504859
  · exact B504863
  · exact B504867
  · exact B504871
  · exact B504875
  · exact B504879
  · exact B504883
  · exact B504887
  · exact B504891
  · exact B504895
  · exact B504899
  · exact B504903
  · exact B504907
  · exact B504911
  · exact B504915
  · exact B504919
  · exact B504923
  · exact B504927
  · exact B504931
  · exact B504935
  · exact B504939
  · exact B504943
  · exact B504947
  · exact B504951
  · exact B504955
  · exact B504959
  · exact B504963
  · exact B504967
  · exact B504971
  · exact B504975
  · exact B504979
  · exact B504983
  · exact B504987
  · exact B504991
  · exact B504995
  · exact B504999
  · exact B505003
  · exact B505007
  · exact B505011
  · exact B505015
  · exact B505019
  · exact B505023
  · exact B505027
  · exact B505031
  · exact B505035
  · exact B505039
  · exact B505043
  · exact B505047
  · exact B505051
  · exact B505055
  · exact B505059
  · exact B505063
  · exact B505067
  · exact B505071
  · exact B505075
  · exact B505079
  · exact B505083
  · exact B505087
  · exact B505091
  · exact B505095
  · exact B505099
  · exact B505103
  · exact B505107
  · exact B505111
  · exact B505115
  · exact B505119
  · exact B505123
  · exact B505127
  · exact B505131
  · exact B505135
  · exact B505139
  · exact B505143
  · exact B505147
  · exact B505151
  · exact B505155
  · exact B505159
  · exact B505163
  · exact B505167
  · exact B505171
  · exact B505175
  · exact B505179
  · exact B505183
  · exact B505187
  · exact B505191
  · exact B505195
  · exact B505199
  · exact B505203
  · exact B505207
  · exact B505211
  · exact B505215
  · exact B505219
  · exact B505223
  · exact B505227
  · exact B505231
  · exact B505235
  · exact B505239
  · exact B505243
  · exact B505247
  · exact B505251
  · exact B505255
  · exact B505259
  · exact B505263
  · exact B505267
  · exact B505271
  · exact B505275
  · exact B505279
  · exact B505283
  · exact B505287
  · exact B505291
  · exact B505295
  · exact B505299
  · exact B505303
  · exact B505307
  · exact B505311
  · exact B505315
  · exact B505319
  · exact B505323
  · exact B505327
  · exact B505331
  · exact B505335
  · exact B505339
  · exact B505343
  · exact B505347
  · exact B505351
  · exact B505355
  · exact B505359
  · exact B505363
  · exact B505367
  · exact B505371
  · exact B505375
  · exact B505379
  · exact B505383
  · exact B505387
  · exact B505391
  · exact B505395
  · exact B505399
  · exact B505403
  · exact B505407
  · exact B505411
  · exact B505415
  · exact B505419
  · exact B505423
  · exact B505427
  · exact B505431
  · exact B505435
  · exact B505439
  · exact B505443
  · exact B505447
  · exact B505451
  · exact B505455
  · exact B505459
  · exact B505463
  · exact B505467
  · exact B505471
  · exact B505475
  · exact B505479
  · exact B505483
  · exact B505487
  · exact B505491
  · exact B505495
  · exact B505499
  · exact B505503
  · exact B505507
  · exact B505511
  · exact B505515
  · exact B505519
  · exact B505523
  · exact B505527
  · exact B505531
  · exact B505535
  · exact B505539
  · exact B505543
  · exact B505547
  · exact B505551
  · exact B505555
  · exact B505559
  · exact B505563
  · exact B505567
  · exact B505571
  · exact B505575
  · exact B505579
  · exact B505583
  · exact B505587
  · exact B505591
  · exact B505595
  · exact B505599
  · exact B505603
  · exact B505607
  · exact B505611
  · exact B505615
  · exact B505619
  · exact B505623
  · exact B505627
  · exact B505631
  · exact B505635
  · exact B505639
  · exact B505643
  · exact B505647
  · exact B505651
  · exact B505655
  · exact B505659
  · exact B505663
  · exact B505667
  · exact B505671
  · exact B505675
  · exact B505679
  · exact B505683
  · exact B505687
  · exact B505691
  · exact B505695
  · exact B505699
  · exact B505703
  · exact B505707
  · exact B505711
  · exact B505715
  · exact B505719
  · exact B505723
  · exact B505727
  · exact B505731
  · exact B505735
  · exact B505739
  · exact B505743
  · exact B505747
  · exact B505751
  · exact B505755
  · exact B505759
  · exact B505763
  · exact B505767
  · exact B505771
  · exact B505775
  · exact B505779
  · exact B505783
  · exact B505787
  · exact B505791
  · exact B505795
  · exact B505799
  · exact B505803
  · exact B505807
  · exact B505811
  · exact B505815
  · exact B505819
  · exact B505823
  · exact B505827
  · exact B505831
  · exact B505835
  · exact B505839
  · exact B505843
  · exact B505847
  · exact B505851
  · exact B505855
  · exact B505859
  · exact B505863
  · exact B505867
  · exact B505871
  · exact B505875
  · exact B505879
  · exact B505883
  · exact B505887
  · exact B505891
  · exact B505895
  · exact B505899
  · exact B505903
  · exact B505907
  · exact B505911
  · exact B505915
  · exact B505919
  · exact B505923
  · exact B505927
  · exact B505931
  · exact B505935
  · exact B505939
  · exact B505943
  · exact B505947
  · exact B505951
  · exact B505955
  · exact B505959
  · exact B505963
  · exact B505967
  · exact B505971
  · exact B505975
  · exact B505979
  · exact B505983
  · exact B505987
  · exact B505991
  · exact B505995
  · exact B505999
  · exact B506003
  · exact B506007
  · exact B506011
  · exact B506015
  · exact B506019
  · exact B506023
  · exact B506027
  · exact B506031
  · exact B506035
  · exact B506039
  · exact B506043
  · exact B506047
  · exact B506051
  · exact B506055
  · exact B506059
  · exact B506063
  · exact B506067
  · exact B506071
  · exact B506075
  · exact B506079
  · exact B506083
  · exact B506087
  · exact B506091
  · exact B506095
  · exact B506099
  · exact B506103
  · exact B506107
  · exact B506111
  · exact B506115
  · exact B506119
  · exact B506123
  · exact B506127
  · exact B506131
  · exact B506135
  · exact B506139
  · exact B506143
  · exact B506147
  · exact B506151
  · exact B506155
  · exact B506159
  · exact B506163
  · exact B506167
  · exact B506171
  · exact B506175
  · exact B506179
  · exact B506183
  · exact B506187
  · exact B506191
  · exact B506195
  · exact B506199
  · exact B506203
  · exact B506207
  · exact B506211
  · exact B506215
  · exact B506219
  · exact B506223
  · exact B506227
  · exact B506231
  · exact B506235
  · exact B506239
  · exact B506243
  · exact B506247
  · exact B506251
  · exact B506255
  · exact B506259
  · exact B506263
  · exact B506267
  · exact B506271
  · exact B506275
  · exact B506279
  · exact B506283
  · exact B506287
  · exact B506291
  · exact B506295
  · exact B506299
  · exact B506303
  · exact B506307
  · exact B506311
  · exact B506315
  · exact B506319
  · exact B506323
  · exact B506327
  · exact B506331
  · exact B506335
  · exact B506339
  · exact B506343
  · exact B506347
  · exact B506351
  · exact B506355
  · exact B506359
  · exact B506363
  · exact B506367
  · exact B506371
  · exact B506375
  · exact B506379
  · exact B506383
  · exact B506387
  · exact B506391
  · exact B506395
  · exact B506399
  · exact B506403
  · exact B506407
  · exact B506411
  · exact B506415
  · exact B506419
  · exact B506423
  · exact B506427
  · exact B506431
  · exact B506435
  · exact B506439
  · exact B506443
  · exact B506447
  · exact B506451
  · exact B506455
  · exact B506459
  · exact B506463
  · exact B506467
  · exact B506471
  · exact B506475
  · exact B506479
  · exact B506483
  · exact B506487
  · exact B506491
  · exact B506495
  · exact B506499
  · exact B506503
  · exact B506507
  · exact B506511
  · exact B506515
  · exact B506519
  · exact B506523
  · exact B506527
  · exact B506531
  · exact B506535
  · exact B506539
  · exact B506543
  · exact B506547
  · exact B506551
  · exact B506555
  · exact B506559
  · exact B506563
  · exact B506567
  · exact B506571
  · exact B506575
  · exact B506579
  · exact B506583
  · exact B506587
  · exact B506591

theorem C1 (j : ℕ) (h1 : 126648 ≤ j) (h2 : j ≤ 126947) : Blo 503794 (4 * j + 3) := by
  interval_cases j
  · exact B506595
  · exact B506599
  · exact B506603
  · exact B506607
  · exact B506611
  · exact B506615
  · exact B506619
  · exact B506623
  · exact B506627
  · exact B506631
  · exact B506635
  · exact B506639
  · exact B506643
  · exact B506647
  · exact B506651
  · exact B506655
  · exact B506659
  · exact B506663
  · exact B506667
  · exact B506671
  · exact B506675
  · exact B506679
  · exact B506683
  · exact B506687
  · exact B506691
  · exact B506695
  · exact B506699
  · exact B506703
  · exact B506707
  · exact B506711
  · exact B506715
  · exact B506719
  · exact B506723
  · exact B506727
  · exact B506731
  · exact B506735
  · exact B506739
  · exact B506743
  · exact B506747
  · exact B506751
  · exact B506755
  · exact B506759
  · exact B506763
  · exact B506767
  · exact B506771
  · exact B506775
  · exact B506779
  · exact B506783
  · exact B506787
  · exact B506791
  · exact B506795
  · exact B506799
  · exact B506803
  · exact B506807
  · exact B506811
  · exact B506815
  · exact B506819
  · exact B506823
  · exact B506827
  · exact B506831
  · exact B506835
  · exact B506839
  · exact B506843
  · exact B506847
  · exact B506851
  · exact B506855
  · exact B506859
  · exact B506863
  · exact B506867
  · exact B506871
  · exact B506875
  · exact B506879
  · exact B506883
  · exact B506887
  · exact B506891
  · exact B506895
  · exact B506899
  · exact B506903
  · exact B506907
  · exact B506911
  · exact B506915
  · exact B506919
  · exact B506923
  · exact B506927
  · exact B506931
  · exact B506935
  · exact B506939
  · exact B506943
  · exact B506947
  · exact B506951
  · exact B506955
  · exact B506959
  · exact B506963
  · exact B506967
  · exact B506971
  · exact B506975
  · exact B506979
  · exact B506983
  · exact B506987
  · exact B506991
  · exact B506995
  · exact B506999
  · exact B507003
  · exact B507007
  · exact B507011
  · exact B507015
  · exact B507019
  · exact B507023
  · exact B507027
  · exact B507031
  · exact B507035
  · exact B507039
  · exact B507043
  · exact B507047
  · exact B507051
  · exact B507055
  · exact B507059
  · exact B507063
  · exact B507067
  · exact B507071
  · exact B507075
  · exact B507079
  · exact B507083
  · exact B507087
  · exact B507091
  · exact B507095
  · exact B507099
  · exact B507103
  · exact B507107
  · exact B507111
  · exact B507115
  · exact B507119
  · exact B507123
  · exact B507127
  · exact B507131
  · exact B507135
  · exact B507139
  · exact B507143
  · exact B507147
  · exact B507151
  · exact B507155
  · exact B507159
  · exact B507163
  · exact B507167
  · exact B507171
  · exact B507175
  · exact B507179
  · exact B507183
  · exact B507187
  · exact B507191
  · exact B507195
  · exact B507199
  · exact B507203
  · exact B507207
  · exact B507211
  · exact B507215
  · exact B507219
  · exact B507223
  · exact B507227
  · exact B507231
  · exact B507235
  · exact B507239
  · exact B507243
  · exact B507247
  · exact B507251
  · exact B507255
  · exact B507259
  · exact B507263
  · exact B507267
  · exact B507271
  · exact B507275
  · exact B507279
  · exact B507283
  · exact B507287
  · exact B507291
  · exact B507295
  · exact B507299
  · exact B507303
  · exact B507307
  · exact B507311
  · exact B507315
  · exact B507319
  · exact B507323
  · exact B507327
  · exact B507331
  · exact B507335
  · exact B507339
  · exact B507343
  · exact B507347
  · exact B507351
  · exact B507355
  · exact B507359
  · exact B507363
  · exact B507367
  · exact B507371
  · exact B507375
  · exact B507379
  · exact B507383
  · exact B507387
  · exact B507391
  · exact B507395
  · exact B507399
  · exact B507403
  · exact B507407
  · exact B507411
  · exact B507415
  · exact B507419
  · exact B507423
  · exact B507427
  · exact B507431
  · exact B507435
  · exact B507439
  · exact B507443
  · exact B507447
  · exact B507451
  · exact B507455
  · exact B507459
  · exact B507463
  · exact B507467
  · exact B507471
  · exact B507475
  · exact B507479
  · exact B507483
  · exact B507487
  · exact B507491
  · exact B507495
  · exact B507499
  · exact B507503
  · exact B507507
  · exact B507511
  · exact B507515
  · exact B507519
  · exact B507523
  · exact B507527
  · exact B507531
  · exact B507535
  · exact B507539
  · exact B507543
  · exact B507547
  · exact B507551
  · exact B507555
  · exact B507559
  · exact B507563
  · exact B507567
  · exact B507571
  · exact B507575
  · exact B507579
  · exact B507583
  · exact B507587
  · exact B507591
  · exact B507595
  · exact B507599
  · exact B507603
  · exact B507607
  · exact B507611
  · exact B507615
  · exact B507619
  · exact B507623
  · exact B507627
  · exact B507631
  · exact B507635
  · exact B507639
  · exact B507643
  · exact B507647
  · exact B507651
  · exact B507655
  · exact B507659
  · exact B507663
  · exact B507667
  · exact B507671
  · exact B507675
  · exact B507679
  · exact B507683
  · exact B507687
  · exact B507691
  · exact B507695
  · exact B507699
  · exact B507703
  · exact B507707
  · exact B507711
  · exact B507715
  · exact B507719
  · exact B507723
  · exact B507727
  · exact B507731
  · exact B507735
  · exact B507739
  · exact B507743
  · exact B507747
  · exact B507751
  · exact B507755
  · exact B507759
  · exact B507763
  · exact B507767
  · exact B507771
  · exact B507775
  · exact B507779
  · exact B507783
  · exact B507787
  · exact B507791

theorem solution (m : ℕ) (hlo : 503794 ≤ m) (hhi : m ≤ 507794) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 125948 ≤ j := by omega
    have hj2 : j ≤ 126947 := by omega
    have hb : Blo 503794 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 126648 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
