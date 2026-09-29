-- Prove2me | solution 1 for syracuse_descends_range_1632515_1634015
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:14:47.570817+00:00
-- url     : https://prove2.me/submissions/506b62aa-40bf-476b-bf41-cb957d78e9e5

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


theorem B2449421 : Blo 1632515 2449421 := bbase (se 3 (by rfl) ⟨459266, by rfl⟩ : syracuseStep 2449421 = 918533) (by norm_num)
theorem B5513237 : Blo 1632515 5513237 := bbase (se 6 (by rfl) ⟨129216, by rfl⟩ : syracuseStep 5513237 = 258433) (by norm_num)
theorem B2449445 : Blo 1632515 2449445 := bbase (se 4 (by rfl) ⟨229635, by rfl⟩ : syracuseStep 2449445 = 459271) (by norm_num)
theorem B15704117 : Blo 1632515 15704117 := bbase (se 5 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 15704117 = 1472261) (by norm_num)
theorem B2449469 : Blo 1632515 2449469 := bbase (se 3 (by rfl) ⟨459275, by rfl⟩ : syracuseStep 2449469 = 918551) (by norm_num)
theorem B2449493 : Blo 1632515 2449493 := bbase (se 8 (by rfl) ⟨14352, by rfl⟩ : syracuseStep 2449493 = 28705) (by norm_num)
theorem B2449517 : Blo 1632515 2449517 := bbase (se 3 (by rfl) ⟨459284, by rfl⟩ : syracuseStep 2449517 = 918569) (by norm_num)
theorem B2449541 : Blo 1632515 2449541 := bbase (se 4 (by rfl) ⟨229644, by rfl⟩ : syracuseStep 2449541 = 459289) (by norm_num)
theorem B2449565 : Blo 1632515 2449565 := bbase (se 3 (by rfl) ⟨459293, by rfl⟩ : syracuseStep 2449565 = 918587) (by norm_num)
theorem B2449589 : Blo 1632515 2449589 := bbase (se 5 (by rfl) ⟨114824, by rfl⟩ : syracuseStep 2449589 = 229649) (by norm_num)
theorem B2449613 : Blo 1632515 2449613 := bbase (se 3 (by rfl) ⟨459302, by rfl⟩ : syracuseStep 2449613 = 918605) (by norm_num)
theorem B1654997 : Blo 1632515 1654997 := bbase (se 7 (by rfl) ⟨19394, by rfl⟩ : syracuseStep 1654997 = 38789) (by norm_num)
theorem B2449637 : Blo 1632515 2449637 := bbase (se 4 (by rfl) ⟨229653, by rfl⟩ : syracuseStep 2449637 = 459307) (by norm_num)
theorem B1655029 : Blo 1632515 1655029 := bbase (se 5 (by rfl) ⟨77579, by rfl⟩ : syracuseStep 1655029 = 155159) (by norm_num)
theorem B2449661 : Blo 1632515 2449661 := bbase (se 3 (by rfl) ⟨459311, by rfl⟩ : syracuseStep 2449661 = 918623) (by norm_num)
theorem B2449685 : Blo 1632515 2449685 := bbase (se 6 (by rfl) ⟨57414, by rfl⟩ : syracuseStep 2449685 = 114829) (by norm_num)
theorem B2449709 : Blo 1632515 2449709 := bbase (se 3 (by rfl) ⟨459320, by rfl⟩ : syracuseStep 2449709 = 918641) (by norm_num)
theorem B2449733 : Blo 1632515 2449733 := bbase (se 4 (by rfl) ⟨229662, by rfl⟩ : syracuseStep 2449733 = 459325) (by norm_num)
theorem B2449757 : Blo 1632515 2449757 := bbase (se 3 (by rfl) ⟨459329, by rfl⟩ : syracuseStep 2449757 = 918659) (by norm_num)
theorem B2449781 : Blo 1632515 2449781 := bbase (se 5 (by rfl) ⟨114833, by rfl⟩ : syracuseStep 2449781 = 229667) (by norm_num)
theorem B2449805 : Blo 1632515 2449805 := bbase (se 3 (by rfl) ⟨459338, by rfl⟩ : syracuseStep 2449805 = 918677) (by norm_num)
theorem B2449829 : Blo 1632515 2449829 := bbase (se 4 (by rfl) ⟨229671, by rfl⟩ : syracuseStep 2449829 = 459343) (by norm_num)
theorem B2449853 : Blo 1632515 2449853 := bbase (se 3 (by rfl) ⟨459347, by rfl⟩ : syracuseStep 2449853 = 918695) (by norm_num)
theorem B5513669 : Blo 1632515 5513669 := bbase (se 4 (by rfl) ⟨516906, by rfl⟩ : syracuseStep 5513669 = 1033813) (by norm_num)
theorem B2449877 : Blo 1632515 2449877 := bbase (se 7 (by rfl) ⟨28709, by rfl⟩ : syracuseStep 2449877 = 57419) (by norm_num)
theorem B2449901 : Blo 1632515 2449901 := bbase (se 3 (by rfl) ⟨459356, by rfl⟩ : syracuseStep 2449901 = 918713) (by norm_num)
theorem B2449925 : Blo 1632515 2449925 := bbase (se 4 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 2449925 = 459361) (by norm_num)
theorem B2449949 : Blo 1632515 2449949 := bbase (se 3 (by rfl) ⟨459365, by rfl⟩ : syracuseStep 2449949 = 918731) (by norm_num)
theorem B2449973 : Blo 1632515 2449973 := bbase (se 5 (by rfl) ⟨114842, by rfl⟩ : syracuseStep 2449973 = 229685) (by norm_num)
theorem B2449997 : Blo 1632515 2449997 := bbase (se 3 (by rfl) ⟨459374, by rfl⟩ : syracuseStep 2449997 = 918749) (by norm_num)
theorem B2450021 : Blo 1632515 2450021 := bbase (se 4 (by rfl) ⟨229689, by rfl⟩ : syracuseStep 2450021 = 459379) (by norm_num)
theorem B2450045 : Blo 1632515 2450045 := bbase (se 3 (by rfl) ⟨459383, by rfl⟩ : syracuseStep 2450045 = 918767) (by norm_num)
theorem B8266373 : Blo 1632515 8266373 := bbase (se 4 (by rfl) ⟨774972, by rfl⟩ : syracuseStep 8266373 = 1549945) (by norm_num)
theorem B2450069 : Blo 1632515 2450069 := bbase (se 6 (by rfl) ⟨57423, by rfl⟩ : syracuseStep 2450069 = 114847) (by norm_num)
theorem B2450093 : Blo 1632515 2450093 := bbase (se 3 (by rfl) ⟨459392, by rfl⟩ : syracuseStep 2450093 = 918785) (by norm_num)
theorem B5587637 : Blo 1632515 5587637 := bbase (se 5 (by rfl) ⟨261920, by rfl⟩ : syracuseStep 5587637 = 523841) (by norm_num)
theorem B2450117 : Blo 1632515 2450117 := bbase (se 4 (by rfl) ⟨229698, by rfl⟩ : syracuseStep 2450117 = 459397) (by norm_num)
theorem B2450141 : Blo 1632515 2450141 := bbase (se 3 (by rfl) ⟨459401, by rfl⟩ : syracuseStep 2450141 = 918803) (by norm_num)
theorem B2450165 : Blo 1632515 2450165 := bbase (se 5 (by rfl) ⟨114851, by rfl⟩ : syracuseStep 2450165 = 229703) (by norm_num)
theorem B2450189 : Blo 1632515 2450189 := bbase (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) (by norm_num)
theorem B27214613 : Blo 1632515 27214613 := bbase (se 6 (by rfl) ⟨637842, by rfl⟩ : syracuseStep 27214613 = 1275685) (by norm_num)
theorem B2450213 : Blo 1632515 2450213 := bbase (se 4 (by rfl) ⟨229707, by rfl⟩ : syracuseStep 2450213 = 459415) (by norm_num)
theorem B2450237 : Blo 1632515 2450237 := bbase (se 3 (by rfl) ⟨459419, by rfl⟩ : syracuseStep 2450237 = 918839) (by norm_num)
theorem B2450261 : Blo 1632515 2450261 := bbase (se 9 (by rfl) ⟨7178, by rfl⟩ : syracuseStep 2450261 = 14357) (by norm_num)
theorem B17662805 : Blo 1632515 17662805 := bbase (se 9 (by rfl) ⟨51746, by rfl⟩ : syracuseStep 17662805 = 103493) (by norm_num)
theorem B2450285 : Blo 1632515 2450285 := bbase (se 3 (by rfl) ⟨459428, by rfl⟩ : syracuseStep 2450285 = 918857) (by norm_num)
theorem B5514101 : Blo 1632515 5514101 := bbase (se 5 (by rfl) ⟨258473, by rfl⟩ : syracuseStep 5514101 = 516947) (by norm_num)
theorem B2450309 : Blo 1632515 2450309 := bbase (se 4 (by rfl) ⟨229716, by rfl⟩ : syracuseStep 2450309 = 459433) (by norm_num)
theorem B2450333 : Blo 1632515 2450333 := bbase (se 3 (by rfl) ⟨459437, by rfl⟩ : syracuseStep 2450333 = 918875) (by norm_num)
theorem B2450357 : Blo 1632515 2450357 := bbase (se 5 (by rfl) ⟨114860, by rfl⟩ : syracuseStep 2450357 = 229721) (by norm_num)
theorem B2450381 : Blo 1632515 2450381 := bbase (se 3 (by rfl) ⟨459446, by rfl⟩ : syracuseStep 2450381 = 918893) (by norm_num)
theorem B2450405 : Blo 1632515 2450405 := bbase (se 4 (by rfl) ⟨229725, by rfl⟩ : syracuseStep 2450405 = 459451) (by norm_num)
theorem B2450429 : Blo 1632515 2450429 := bbase (se 3 (by rfl) ⟨459455, by rfl⟩ : syracuseStep 2450429 = 918911) (by norm_num)
theorem B2450453 : Blo 1632515 2450453 := bbase (se 6 (by rfl) ⟨57432, by rfl⟩ : syracuseStep 2450453 = 114865) (by norm_num)
theorem B2450477 : Blo 1632515 2450477 := bbase (se 3 (by rfl) ⟨459464, by rfl⟩ : syracuseStep 2450477 = 918929) (by norm_num)
theorem B6284357 : Blo 1632515 6284357 := bbase (se 4 (by rfl) ⟨589158, by rfl⟩ : syracuseStep 6284357 = 1178317) (by norm_num)
theorem B2450501 : Blo 1632515 2450501 := bbase (se 4 (by rfl) ⟨229734, by rfl⟩ : syracuseStep 2450501 = 459469) (by norm_num)
theorem B6202453 : Blo 1632515 6202453 := bbase (se 8 (by rfl) ⟨36342, by rfl⟩ : syracuseStep 6202453 = 72685) (by norm_num)
theorem B2450525 : Blo 1632515 2450525 := bbase (se 3 (by rfl) ⟨459473, by rfl⟩ : syracuseStep 2450525 = 918947) (by norm_num)
theorem B2450549 : Blo 1632515 2450549 := bbase (se 5 (by rfl) ⟨114869, by rfl⟩ : syracuseStep 2450549 = 229739) (by norm_num)
theorem B2450573 : Blo 1632515 2450573 := bbase (se 3 (by rfl) ⟨459482, by rfl⟩ : syracuseStep 2450573 = 918965) (by norm_num)
theorem B7070885 : Blo 1632515 7070885 := bbase (se 4 (by rfl) ⟨662895, by rfl⟩ : syracuseStep 7070885 = 1325791) (by norm_num)
theorem B2450597 : Blo 1632515 2450597 := bbase (se 4 (by rfl) ⟨229743, by rfl⟩ : syracuseStep 2450597 = 459487) (by norm_num)
theorem B4416677 : Blo 1632515 4416677 := bbase (se 4 (by rfl) ⟨414063, by rfl⟩ : syracuseStep 4416677 = 828127) (by norm_num)
theorem B2483389 : Blo 1632515 2483389 := bbase (se 3 (by rfl) ⟨465635, by rfl⟩ : syracuseStep 2483389 = 931271) (by norm_num)
theorem B2450621 : Blo 1632515 2450621 := bbase (se 3 (by rfl) ⟨459491, by rfl⟩ : syracuseStep 2450621 = 918983) (by norm_num)
theorem B2450645 : Blo 1632515 2450645 := bbase (se 7 (by rfl) ⟨28718, by rfl⟩ : syracuseStep 2450645 = 57437) (by norm_num)
theorem B2450669 : Blo 1632515 2450669 := bbase (se 3 (by rfl) ⟨459500, by rfl⟩ : syracuseStep 2450669 = 919001) (by norm_num)
theorem B2450693 : Blo 1632515 2450693 := bbase (se 4 (by rfl) ⟨229752, by rfl⟩ : syracuseStep 2450693 = 459505) (by norm_num)
theorem B2450717 : Blo 1632515 2450717 := bbase (se 3 (by rfl) ⟨459509, by rfl⟩ : syracuseStep 2450717 = 919019) (by norm_num)
theorem B5514533 : Blo 1632515 5514533 := bbase (se 4 (by rfl) ⟨516987, by rfl⟩ : syracuseStep 5514533 = 1033975) (by norm_num)
theorem B10462517 : Blo 1632515 10462517 := bbase (se 5 (by rfl) ⟨490430, by rfl⟩ : syracuseStep 10462517 = 980861) (by norm_num)
theorem B2450741 : Blo 1632515 2450741 := bbase (se 5 (by rfl) ⟨114878, by rfl⟩ : syracuseStep 2450741 = 229757) (by norm_num)
theorem B2450765 : Blo 1632515 2450765 := bbase (se 3 (by rfl) ⟨459518, by rfl⟩ : syracuseStep 2450765 = 919037) (by norm_num)
theorem B9299285 : Blo 1632515 9299285 := bbase (se 12 (by rfl) ⟨3405, by rfl⟩ : syracuseStep 9299285 = 6811) (by norm_num)
theorem B2450789 : Blo 1632515 2450789 := bbase (se 4 (by rfl) ⟨229761, by rfl⟩ : syracuseStep 2450789 = 459523) (by norm_num)
theorem B2450813 : Blo 1632515 2450813 := bbase (se 3 (by rfl) ⟨459527, by rfl⟩ : syracuseStep 2450813 = 919055) (by norm_num)
theorem B7849349 : Blo 1632515 7849349 := bbase (se 4 (by rfl) ⟨735876, by rfl⟩ : syracuseStep 7849349 = 1471753) (by norm_num)
theorem B6202757 : Blo 1632515 6202757 := bbase (se 4 (by rfl) ⟨581508, by rfl⟩ : syracuseStep 6202757 = 1163017) (by norm_num)
theorem B2450837 : Blo 1632515 2450837 := bbase (se 6 (by rfl) ⟨57441, by rfl⟩ : syracuseStep 2450837 = 114883) (by norm_num)
theorem B2450861 : Blo 1632515 2450861 := bbase (se 3 (by rfl) ⟨459536, by rfl⟩ : syracuseStep 2450861 = 919073) (by norm_num)
theorem B1656245 : Blo 1632515 1656245 := bbase (se 5 (by rfl) ⟨77636, by rfl⟩ : syracuseStep 1656245 = 155273) (by norm_num)
theorem B2450885 : Blo 1632515 2450885 := bbase (se 4 (by rfl) ⟨229770, by rfl⟩ : syracuseStep 2450885 = 459541) (by norm_num)
theorem B2516437 : Blo 1632515 2516437 := bbase (se 7 (by rfl) ⟨29489, by rfl⟩ : syracuseStep 2516437 = 58979) (by norm_num)
theorem B2450909 : Blo 1632515 2450909 := bbase (se 3 (by rfl) ⟨459545, by rfl⟩ : syracuseStep 2450909 = 919091) (by norm_num)
theorem B2450933 : Blo 1632515 2450933 := bbase (se 5 (by rfl) ⟨114887, by rfl⟩ : syracuseStep 2450933 = 229775) (by norm_num)
theorem B2450957 : Blo 1632515 2450957 := bbase (se 3 (by rfl) ⟨459554, by rfl⟩ : syracuseStep 2450957 = 919109) (by norm_num)
theorem B2450981 : Blo 1632515 2450981 := bbase (se 4 (by rfl) ⟨229779, by rfl⟩ : syracuseStep 2450981 = 459559) (by norm_num)
theorem B1836589 : Blo 1632515 1836589 := bbase (se 3 (by rfl) ⟨344360, by rfl⟩ : syracuseStep 1836589 = 688721) (by norm_num)
theorem B2451005 : Blo 1632515 2451005 := bbase (se 3 (by rfl) ⟨459563, by rfl⟩ : syracuseStep 2451005 = 919127) (by norm_num)
theorem B1836625 : Blo 1632515 1836625 := bbase (se 2 (by rfl) ⟨688734, by rfl⟩ : syracuseStep 1836625 = 1377469) (by norm_num)
theorem B3925597 : Blo 1632515 3925597 := bbase (se 3 (by rfl) ⟨736049, by rfl⟩ : syracuseStep 3925597 = 1472099) (by norm_num)
theorem B1836661 : Blo 1632515 1836661 := bbase (se 5 (by rfl) ⟨86093, by rfl⟩ : syracuseStep 1836661 = 172187) (by norm_num)
theorem B2942605 : Blo 1632515 2942605 := bbase (se 3 (by rfl) ⟨551738, by rfl⟩ : syracuseStep 2942605 = 1103477) (by norm_num)
theorem B1836697 : Blo 1632515 1836697 := bbase (se 2 (by rfl) ⟨688761, by rfl⟩ : syracuseStep 1836697 = 1377523) (by norm_num)
theorem B1836733 : Blo 1632515 1836733 := bbase (se 3 (by rfl) ⟨344387, by rfl⟩ : syracuseStep 1836733 = 688775) (by norm_num)
theorem B2942677 : Blo 1632515 2942677 := bbase (se 7 (by rfl) ⟨34484, by rfl⟩ : syracuseStep 2942677 = 68969) (by norm_num)
theorem B1836769 : Blo 1632515 1836769 := bbase (se 2 (by rfl) ⟨688788, by rfl⟩ : syracuseStep 1836769 = 1377577) (by norm_num)
theorem B1836805 : Blo 1632515 1836805 := bbase (se 4 (by rfl) ⟨172200, by rfl⟩ : syracuseStep 1836805 = 344401) (by norm_num)
theorem B1836841 : Blo 1632515 1836841 := bbase (se 2 (by rfl) ⟨688815, by rfl⟩ : syracuseStep 1836841 = 1377631) (by norm_num)
theorem B2066249 : Blo 1632515 2066249 := bbase (se 2 (by rfl) ⟨774843, by rfl⟩ : syracuseStep 2066249 = 1549687) (by norm_num)
theorem B1836877 : Blo 1632515 1836877 := bbase (se 3 (by rfl) ⟨344414, by rfl⟩ : syracuseStep 1836877 = 688829) (by norm_num)
theorem B4966229 : Blo 1632515 4966229 := bbase (se 9 (by rfl) ⟨14549, by rfl⟩ : syracuseStep 4966229 = 29099) (by norm_num)
theorem B2942821 : Blo 1632515 2942821 := bbase (se 4 (by rfl) ⟨275889, by rfl⟩ : syracuseStep 2942821 = 551779) (by norm_num)
theorem B1836913 : Blo 1632515 1836913 := bbase (se 2 (by rfl) ⟨688842, by rfl⟩ : syracuseStep 1836913 = 1377685) (by norm_num)
theorem B2066305 : Blo 1632515 2066305 := bbase (se 2 (by rfl) ⟨774864, by rfl⟩ : syracuseStep 2066305 = 1549729) (by norm_num)
theorem B1836949 : Blo 1632515 1836949 := bbase (se 6 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 1836949 = 86107) (by norm_num)
theorem B8267669 : Blo 1632515 8267669 := bbase (se 6 (by rfl) ⟨193773, by rfl⟩ : syracuseStep 8267669 = 387547) (by norm_num)
theorem B1836985 : Blo 1632515 1836985 := bbase (se 2 (by rfl) ⟨688869, by rfl⟩ : syracuseStep 1836985 = 1377739) (by norm_num)
theorem B1837021 : Blo 1632515 1837021 := bbase (se 3 (by rfl) ⟨344441, by rfl⟩ : syracuseStep 1837021 = 688883) (by norm_num)
theorem B2066401 : Blo 1632515 2066401 := bbase (se 2 (by rfl) ⟨774900, by rfl⟩ : syracuseStep 2066401 = 1549801) (by norm_num)
theorem B1837057 : Blo 1632515 1837057 := bbase (se 2 (by rfl) ⟨688896, by rfl⟩ : syracuseStep 1837057 = 1377793) (by norm_num)
theorem B5883941 : Blo 1632515 5883941 := bbase (se 4 (by rfl) ⟨551619, by rfl⟩ : syracuseStep 5883941 = 1103239) (by norm_num)
theorem B1837093 : Blo 1632515 1837093 := bbase (se 4 (by rfl) ⟨172227, by rfl⟩ : syracuseStep 1837093 = 344455) (by norm_num)
theorem B2615341 : Blo 1632515 2615341 := bbase (se 3 (by rfl) ⟨490376, by rfl⟩ : syracuseStep 2615341 = 980753) (by norm_num)
theorem B1837129 : Blo 1632515 1837129 := bbase (se 2 (by rfl) ⟨688923, by rfl⟩ : syracuseStep 1837129 = 1377847) (by norm_num)
theorem B1837165 : Blo 1632515 1837165 := bbase (se 3 (by rfl) ⟨344468, by rfl⟩ : syracuseStep 1837165 = 688937) (by norm_num)
theorem B2066573 : Blo 1632515 2066573 := bbase (se 3 (by rfl) ⟨387482, by rfl⟩ : syracuseStep 2066573 = 774965) (by norm_num)
theorem B1837201 : Blo 1632515 1837201 := bbase (se 2 (by rfl) ⟨688950, by rfl⟩ : syracuseStep 1837201 = 1377901) (by norm_num)
theorem B5376149 : Blo 1632515 5376149 := bbase (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) (by norm_num)
theorem B1837237 : Blo 1632515 1837237 := bbase (se 5 (by rfl) ⟨86120, by rfl⟩ : syracuseStep 1837237 = 172241) (by norm_num)
theorem B2066629 : Blo 1632515 2066629 := bbase (se 4 (by rfl) ⟨193746, by rfl⟩ : syracuseStep 2066629 = 387493) (by norm_num)
theorem B1837273 : Blo 1632515 1837273 := bbase (se 2 (by rfl) ⟨688977, by rfl⟩ : syracuseStep 1837273 = 1377955) (by norm_num)
theorem B1837309 : Blo 1632515 1837309 := bbase (se 3 (by rfl) ⟨344495, by rfl⟩ : syracuseStep 1837309 = 688991) (by norm_num)
theorem B1837345 : Blo 1632515 1837345 := bbase (se 2 (by rfl) ⟨689004, by rfl⟩ : syracuseStep 1837345 = 1378009) (by norm_num)
theorem B2066725 : Blo 1632515 2066725 := bbase (se 4 (by rfl) ⟨193755, by rfl⟩ : syracuseStep 2066725 = 387511) (by norm_num)
theorem B2124077 : Blo 1632515 2124077 := bbase (se 3 (by rfl) ⟨398264, by rfl⟩ : syracuseStep 2124077 = 796529) (by norm_num)
theorem B2754877 : Blo 1632515 2754877 := bbase (se 3 (by rfl) ⟨516539, by rfl⟩ : syracuseStep 2754877 = 1033079) (by norm_num)
theorem B1837381 : Blo 1632515 1837381 := bbase (se 4 (by rfl) ⟨172254, by rfl⟩ : syracuseStep 1837381 = 344509) (by norm_num)
theorem B1837417 : Blo 1632515 1837417 := bbase (se 2 (by rfl) ⟨689031, by rfl⟩ : syracuseStep 1837417 = 1378063) (by norm_num)
theorem B1837453 : Blo 1632515 1837453 := bbase (se 3 (by rfl) ⟨344522, by rfl⟩ : syracuseStep 1837453 = 689045) (by norm_num)
theorem B2754965 : Blo 1632515 2754965 := bbase (se 6 (by rfl) ⟨64569, by rfl⟩ : syracuseStep 2754965 = 129139) (by norm_num)
theorem B1837489 : Blo 1632515 1837489 := bbase (se 2 (by rfl) ⟨689058, by rfl⟩ : syracuseStep 1837489 = 1378117) (by norm_num)
theorem B5589445 : Blo 1632515 5589445 := bbase (se 4 (by rfl) ⟨524010, by rfl⟩ : syracuseStep 5589445 = 1048021) (by norm_num)
theorem B2066897 : Blo 1632515 2066897 := bbase (se 2 (by rfl) ⟨775086, by rfl⟩ : syracuseStep 2066897 = 1550173) (by norm_num)
theorem B1837525 : Blo 1632515 1837525 := bbase (se 7 (by rfl) ⟨21533, by rfl⟩ : syracuseStep 1837525 = 43067) (by norm_num)
theorem B1837561 : Blo 1632515 1837561 := bbase (se 2 (by rfl) ⟨689085, by rfl⟩ : syracuseStep 1837561 = 1378171) (by norm_num)
theorem B2066953 : Blo 1632515 2066953 := bbase (se 2 (by rfl) ⟨775107, by rfl⟩ : syracuseStep 2066953 = 1550215) (by norm_num)
theorem B2755093 : Blo 1632515 2755093 := bbase (se 6 (by rfl) ⟨64572, by rfl⟩ : syracuseStep 2755093 = 129145) (by norm_num)
theorem B1837597 : Blo 1632515 1837597 := bbase (se 3 (by rfl) ⟨344549, by rfl⟩ : syracuseStep 1837597 = 689099) (by norm_num)
theorem B1837633 : Blo 1632515 1837633 := bbase (se 2 (by rfl) ⟨689112, by rfl⟩ : syracuseStep 1837633 = 1378225) (by norm_num)
theorem B1837669 : Blo 1632515 1837669 := bbase (se 4 (by rfl) ⟨172281, by rfl⟩ : syracuseStep 1837669 = 344563) (by norm_num)
theorem B2067049 : Blo 1632515 2067049 := bbase (se 2 (by rfl) ⟨775143, by rfl⟩ : syracuseStep 2067049 = 1550287) (by norm_num)
theorem B2755181 : Blo 1632515 2755181 := bbase (se 3 (by rfl) ⟨516596, by rfl⟩ : syracuseStep 2755181 = 1033193) (by norm_num)
theorem B1837705 : Blo 1632515 1837705 := bbase (se 2 (by rfl) ⟨689139, by rfl⟩ : syracuseStep 1837705 = 1378279) (by norm_num)
theorem B1837741 : Blo 1632515 1837741 := bbase (se 3 (by rfl) ⟨344576, by rfl⟩ : syracuseStep 1837741 = 689153) (by norm_num)
theorem B2943685 : Blo 1632515 2943685 := bbase (se 4 (by rfl) ⟨275970, by rfl⟩ : syracuseStep 2943685 = 551941) (by norm_num)
theorem B2124493 : Blo 1632515 2124493 := bbase (se 3 (by rfl) ⟨398342, by rfl⟩ : syracuseStep 2124493 = 796685) (by norm_num)
theorem B1837777 : Blo 1632515 1837777 := bbase (se 2 (by rfl) ⟨689166, by rfl⟩ : syracuseStep 1837777 = 1378333) (by norm_num)
theorem B2755309 : Blo 1632515 2755309 := bbase (se 3 (by rfl) ⟨516620, by rfl⟩ : syracuseStep 2755309 = 1033241) (by norm_num)
theorem B1837813 : Blo 1632515 1837813 := bbase (se 5 (by rfl) ⟨86147, by rfl⟩ : syracuseStep 1837813 = 172295) (by norm_num)
theorem B3099397 : Blo 1632515 3099397 := bbase (se 4 (by rfl) ⟨290568, by rfl⟩ : syracuseStep 3099397 = 581137) (by norm_num)
theorem B2067221 : Blo 1632515 2067221 := bbase (se 6 (by rfl) ⟨48450, by rfl⟩ : syracuseStep 2067221 = 96901) (by norm_num)
theorem B1837849 : Blo 1632515 1837849 := bbase (se 2 (by rfl) ⟨689193, by rfl⟩ : syracuseStep 1837849 = 1378387) (by norm_num)
theorem B2943773 : Blo 1632515 2943773 := bbase (se 3 (by rfl) ⟨551957, by rfl⟩ : syracuseStep 2943773 = 1103915) (by norm_num)
theorem B1837885 : Blo 1632515 1837885 := bbase (se 3 (by rfl) ⟨344603, by rfl⟩ : syracuseStep 1837885 = 689207) (by norm_num)
theorem B2755397 : Blo 1632515 2755397 := bbase (se 4 (by rfl) ⟨258318, by rfl⟩ : syracuseStep 2755397 = 516637) (by norm_num)
theorem B2067277 : Blo 1632515 2067277 := bbase (se 3 (by rfl) ⟨387614, by rfl⟩ : syracuseStep 2067277 = 775229) (by norm_num)
theorem B1837921 : Blo 1632515 1837921 := bbase (se 2 (by rfl) ⟨689220, by rfl⟩ : syracuseStep 1837921 = 1378441) (by norm_num)
theorem B2206597 : Blo 1632515 2206597 := bbase (se 4 (by rfl) ⟨206868, by rfl⟩ : syracuseStep 2206597 = 413737) (by norm_num)
theorem B1837957 : Blo 1632515 1837957 := bbase (se 4 (by rfl) ⟨172308, by rfl⟩ : syracuseStep 1837957 = 344617) (by norm_num)
theorem B3099541 : Blo 1632515 3099541 := bbase (se 6 (by rfl) ⟨72645, by rfl⟩ : syracuseStep 3099541 = 145291) (by norm_num)
theorem B1837993 : Blo 1632515 1837993 := bbase (se 2 (by rfl) ⟨689247, by rfl⟩ : syracuseStep 1837993 = 1378495) (by norm_num)
theorem B2067373 : Blo 1632515 2067373 := bbase (se 3 (by rfl) ⟨387632, by rfl⟩ : syracuseStep 2067373 = 775265) (by norm_num)
theorem B2755525 : Blo 1632515 2755525 := bbase (se 4 (by rfl) ⟨258330, by rfl⟩ : syracuseStep 2755525 = 516661) (by norm_num)
theorem B1838029 : Blo 1632515 1838029 := bbase (se 3 (by rfl) ⟨344630, by rfl⟩ : syracuseStep 1838029 = 689261) (by norm_num)
theorem B7850981 : Blo 1632515 7850981 := bbase (se 4 (by rfl) ⟨736029, by rfl⟩ : syracuseStep 7850981 = 1472059) (by norm_num)
theorem B1838065 : Blo 1632515 1838065 := bbase (se 2 (by rfl) ⟨689274, by rfl⟩ : syracuseStep 1838065 = 1378549) (by norm_num)
theorem B1838101 : Blo 1632515 1838101 := bbase (se 6 (by rfl) ⟨43080, by rfl⟩ : syracuseStep 1838101 = 86161) (by norm_num)
theorem B2755613 : Blo 1632515 2755613 := bbase (se 3 (by rfl) ⟨516677, by rfl⟩ : syracuseStep 2755613 = 1033355) (by norm_num)
theorem B3099701 : Blo 1632515 3099701 := bbase (se 5 (by rfl) ⟨145298, by rfl⟩ : syracuseStep 3099701 = 290597) (by norm_num)
theorem B1838137 : Blo 1632515 1838137 := bbase (se 2 (by rfl) ⟨689301, by rfl⟩ : syracuseStep 1838137 = 1378603) (by norm_num)
theorem B6974549 : Blo 1632515 6974549 := bbase (se 8 (by rfl) ⟨40866, by rfl⟩ : syracuseStep 6974549 = 81733) (by norm_num)
theorem B2067545 : Blo 1632515 2067545 := bbase (se 2 (by rfl) ⟨775329, by rfl⟩ : syracuseStep 2067545 = 1550659) (by norm_num)
theorem B1838173 : Blo 1632515 1838173 := bbase (se 3 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 1838173 = 689315) (by norm_num)
theorem B3673205 : Blo 1632515 3673205 := bbase (se 5 (by rfl) ⟨172181, by rfl⟩ : syracuseStep 3673205 = 344363) (by norm_num)
theorem B1838209 : Blo 1632515 1838209 := bbase (se 2 (by rfl) ⟨689328, by rfl⟩ : syracuseStep 1838209 = 1378657) (by norm_num)
theorem B2067601 : Blo 1632515 2067601 := bbase (se 2 (by rfl) ⟨775350, by rfl⟩ : syracuseStep 2067601 = 1550701) (by norm_num)
theorem B2755741 : Blo 1632515 2755741 := bbase (se 3 (by rfl) ⟨516701, by rfl⟩ : syracuseStep 2755741 = 1033403) (by norm_num)
theorem B8268965 : Blo 1632515 8268965 := bbase (se 4 (by rfl) ⟨775215, by rfl⟩ : syracuseStep 8268965 = 1550431) (by norm_num)
theorem B1838245 : Blo 1632515 1838245 := bbase (se 4 (by rfl) ⟨172335, by rfl⟩ : syracuseStep 1838245 = 344671) (by norm_num)
theorem B3673277 : Blo 1632515 3673277 := bbase (se 3 (by rfl) ⟨688739, by rfl⟩ : syracuseStep 3673277 = 1377479) (by norm_num)
theorem B3099845 : Blo 1632515 3099845 := bbase (se 4 (by rfl) ⟨290610, by rfl⟩ : syracuseStep 3099845 = 581221) (by norm_num)
theorem B2518213 : Blo 1632515 2518213 := bbase (se 4 (by rfl) ⟨236082, by rfl⟩ : syracuseStep 2518213 = 472165) (by norm_num)
theorem B2944205 : Blo 1632515 2944205 := bbase (se 3 (by rfl) ⟨552038, by rfl⟩ : syracuseStep 2944205 = 1104077) (by norm_num)
theorem B2616533 : Blo 1632515 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B2067697 : Blo 1632515 2067697 := bbase (se 2 (by rfl) ⟨775386, by rfl⟩ : syracuseStep 2067697 = 1550773) (by norm_num)
theorem B2755829 : Blo 1632515 2755829 := bbase (se 5 (by rfl) ⟨129179, by rfl⟩ : syracuseStep 2755829 = 258359) (by norm_num)
theorem B3673349 : Blo 1632515 3673349 := bbase (se 4 (by rfl) ⟨344376, by rfl⟩ : syracuseStep 3673349 = 688753) (by norm_num)
theorem B3673421 : Blo 1632515 3673421 := bbase (se 3 (by rfl) ⟨688766, by rfl⟩ : syracuseStep 3673421 = 1377533) (by norm_num)
theorem B2755957 : Blo 1632515 2755957 := bbase (se 5 (by rfl) ⟨129185, by rfl⟩ : syracuseStep 2755957 = 258371) (by norm_num)
theorem B3673493 : Blo 1632515 3673493 := bbase (se 6 (by rfl) ⟨86097, by rfl⟩ : syracuseStep 3673493 = 172195) (by norm_num)
theorem B2616725 : Blo 1632515 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B2067869 : Blo 1632515 2067869 := bbase (se 3 (by rfl) ⟨387725, by rfl⟩ : syracuseStep 2067869 = 775451) (by norm_num)
theorem B15912373 : Blo 1632515 15912373 := bbase (se 5 (by rfl) ⟨745892, by rfl⟩ : syracuseStep 15912373 = 1491785) (by norm_num)
theorem B2756045 : Blo 1632515 2756045 := bbase (se 3 (by rfl) ⟨516758, by rfl⟩ : syracuseStep 2756045 = 1033517) (by norm_num)
theorem B2067925 : Blo 1632515 2067925 := bbase (se 7 (by rfl) ⟨24233, by rfl⟩ : syracuseStep 2067925 = 48467) (by norm_num)
theorem B3673565 : Blo 1632515 3673565 := bbase (se 3 (by rfl) ⟨688793, by rfl⟩ : syracuseStep 3673565 = 1377587) (by norm_num)
theorem B4189661 : Blo 1632515 4189661 := bbase (se 3 (by rfl) ⟨785561, by rfl⟩ : syracuseStep 4189661 = 1571123) (by norm_num)
theorem B3100133 : Blo 1632515 3100133 := bbase (se 4 (by rfl) ⟨290637, by rfl⟩ : syracuseStep 3100133 = 581275) (by norm_num)
theorem B2944493 : Blo 1632515 2944493 := bbase (se 3 (by rfl) ⟨552092, by rfl⟩ : syracuseStep 2944493 = 1104185) (by norm_num)
theorem B9301493 : Blo 1632515 9301493 := bbase (se 5 (by rfl) ⟨436007, by rfl⟩ : syracuseStep 9301493 = 872015) (by norm_num)
theorem B3673637 : Blo 1632515 3673637 := bbase (se 4 (by rfl) ⟨344403, by rfl⟩ : syracuseStep 3673637 = 688807) (by norm_num)
theorem B4132397 : Blo 1632515 4132397 := bbase (se 3 (by rfl) ⟨774824, by rfl⟩ : syracuseStep 4132397 = 1549649) (by norm_num)
theorem B2068021 : Blo 1632515 2068021 := bbase (se 5 (by rfl) ⟨96938, by rfl⟩ : syracuseStep 2068021 = 193877) (by norm_num)
theorem B2756173 : Blo 1632515 2756173 := bbase (se 3 (by rfl) ⟨516782, by rfl⟩ : syracuseStep 2756173 = 1033565) (by norm_num)
theorem B5885525 : Blo 1632515 5885525 := bbase (se 8 (by rfl) ⟨34485, by rfl⟩ : syracuseStep 5885525 = 68971) (by norm_num)
theorem B3673709 : Blo 1632515 3673709 := bbase (se 3 (by rfl) ⟨688820, by rfl⟩ : syracuseStep 3673709 = 1377641) (by norm_num)
theorem B3100285 : Blo 1632515 3100285 := bbase (se 3 (by rfl) ⟨581303, by rfl⟩ : syracuseStep 3100285 = 1162607) (by norm_num)
theorem B2756261 : Blo 1632515 2756261 := bbase (se 4 (by rfl) ⟨258399, by rfl⟩ : syracuseStep 2756261 = 516799) (by norm_num)
theorem B8171189 : Blo 1632515 8171189 := bbase (se 5 (by rfl) ⟨383024, by rfl⟩ : syracuseStep 8171189 = 766049) (by norm_num)
theorem B3673781 : Blo 1632515 3673781 := bbase (se 5 (by rfl) ⟨172208, by rfl⟩ : syracuseStep 3673781 = 344417) (by norm_num)
theorem B1961669 : Blo 1632515 1961669 := bbase (se 4 (by rfl) ⟨183906, by rfl⟩ : syracuseStep 1961669 = 367813) (by norm_num)
theorem B3673853 : Blo 1632515 3673853 := bbase (se 3 (by rfl) ⟨688847, by rfl⟩ : syracuseStep 3673853 = 1377695) (by norm_num)
theorem B4189981 : Blo 1632515 4189981 := bbase (se 3 (by rfl) ⟨785621, by rfl⟩ : syracuseStep 4189981 = 1571243) (by norm_num)
theorem B2756389 : Blo 1632515 2756389 := bbase (se 4 (by rfl) ⟨258411, by rfl⟩ : syracuseStep 2756389 = 516823) (by norm_num)
theorem B3673925 : Blo 1632515 3673925 := bbase (se 4 (by rfl) ⟨344430, by rfl⟩ : syracuseStep 3673925 = 688861) (by norm_num)
theorem B13946741 : Blo 1632515 13946741 := bbase (se 5 (by rfl) ⟨653753, by rfl⟩ : syracuseStep 13946741 = 1307507) (by norm_num)
theorem B2756477 : Blo 1632515 2756477 := bbase (se 3 (by rfl) ⟨516839, by rfl⟩ : syracuseStep 2756477 = 1033679) (by norm_num)
theorem B4132741 : Blo 1632515 4132741 := bbase (se 4 (by rfl) ⟨387444, by rfl⟩ : syracuseStep 4132741 = 774889) (by norm_num)
theorem B3673997 : Blo 1632515 3673997 := bbase (se 3 (by rfl) ⟨688874, by rfl⟩ : syracuseStep 3673997 = 1377749) (by norm_num)
theorem B3100589 : Blo 1632515 3100589 := bbase (se 3 (by rfl) ⟨581360, by rfl⟩ : syracuseStep 3100589 = 1162721) (by norm_num)
theorem B1961929 : Blo 1632515 1961929 := bbase (se 2 (by rfl) ⟨735723, by rfl⟩ : syracuseStep 1961929 = 1471447) (by norm_num)
theorem B3674069 : Blo 1632515 3674069 := bbase (se 7 (by rfl) ⟨43055, by rfl⟩ : syracuseStep 3674069 = 86111) (by norm_num)
theorem B4132853 : Blo 1632515 4132853 := bbase (se 5 (by rfl) ⟨193727, by rfl⟩ : syracuseStep 4132853 = 387455) (by norm_num)
theorem B1961977 : Blo 1632515 1961977 := bbase (se 2 (by rfl) ⟨735741, by rfl⟩ : syracuseStep 1961977 = 1471483) (by norm_num)
theorem B2756605 : Blo 1632515 2756605 := bbase (se 3 (by rfl) ⟨516863, by rfl⟩ : syracuseStep 2756605 = 1033727) (by norm_num)
theorem B3674141 : Blo 1632515 3674141 := bbase (se 3 (by rfl) ⟨688901, by rfl⟩ : syracuseStep 3674141 = 1377803) (by norm_num)
theorem B2756693 : Blo 1632515 2756693 := bbase (se 8 (by rfl) ⟨16152, by rfl⟩ : syracuseStep 2756693 = 32305) (by norm_num)
theorem B3674213 : Blo 1632515 3674213 := bbase (se 4 (by rfl) ⟨344457, by rfl⟩ : syracuseStep 3674213 = 688915) (by norm_num)
theorem B4305037 : Blo 1632515 4305037 := bbase (se 3 (by rfl) ⟨807194, by rfl⟩ : syracuseStep 4305037 = 1614389) (by norm_num)
theorem B3723413 : Blo 1632515 3723413 := bbase (se 6 (by rfl) ⟨87267, by rfl⟩ : syracuseStep 3723413 = 174535) (by norm_num)
theorem B3674285 : Blo 1632515 3674285 := bbase (se 3 (by rfl) ⟨688928, by rfl⟩ : syracuseStep 3674285 = 1377857) (by norm_num)
theorem B4133045 : Blo 1632515 4133045 := bbase (se 5 (by rfl) ⟨193736, by rfl⟩ : syracuseStep 4133045 = 387473) (by norm_num)
theorem B7450805 : Blo 1632515 7450805 := bbase (se 5 (by rfl) ⟨349256, by rfl⟩ : syracuseStep 7450805 = 698513) (by norm_num)
theorem B2756821 : Blo 1632515 2756821 := bbase (se 7 (by rfl) ⟨32306, by rfl⟩ : syracuseStep 2756821 = 64613) (by norm_num)
theorem B3674357 : Blo 1632515 3674357 := bbase (se 5 (by rfl) ⟨172235, by rfl⟩ : syracuseStep 3674357 = 344471) (by norm_num)
theorem B2756909 : Blo 1632515 2756909 := bbase (se 3 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 2756909 = 1033841) (by norm_num)
theorem B12407093 : Blo 1632515 12407093 := bbase (se 5 (by rfl) ⟨581582, by rfl⟩ : syracuseStep 12407093 = 1163165) (by norm_num)
theorem B3674429 : Blo 1632515 3674429 := bbase (se 3 (by rfl) ⟨688955, by rfl⟩ : syracuseStep 3674429 = 1377911) (by norm_num)
theorem B3674501 : Blo 1632515 3674501 := bbase (se 4 (by rfl) ⟨344484, by rfl⟩ : syracuseStep 3674501 = 688969) (by norm_num)
theorem B3977629 : Blo 1632515 3977629 := bbase (se 3 (by rfl) ⟨745805, by rfl⟩ : syracuseStep 3977629 = 1491611) (by norm_num)
theorem B2757037 : Blo 1632515 2757037 := bbase (se 3 (by rfl) ⟨516944, by rfl⟩ : syracuseStep 2757037 = 1033889) (by norm_num)
theorem B8270261 : Blo 1632515 8270261 := bbase (se 5 (by rfl) ⟨387668, by rfl⟩ : syracuseStep 8270261 = 775337) (by norm_num)
theorem B3674573 : Blo 1632515 3674573 := bbase (se 3 (by rfl) ⟨688982, by rfl⟩ : syracuseStep 3674573 = 1377965) (by norm_num)
theorem B2757125 : Blo 1632515 2757125 := bbase (se 4 (by rfl) ⟨258480, by rfl⟩ : syracuseStep 2757125 = 516961) (by norm_num)
theorem B4133389 : Blo 1632515 4133389 := bbase (se 3 (by rfl) ⟨775010, by rfl⟩ : syracuseStep 4133389 = 1550021) (by norm_num)
theorem B3674645 : Blo 1632515 3674645 := bbase (se 6 (by rfl) ⟨86124, by rfl⟩ : syracuseStep 3674645 = 172249) (by norm_num)
theorem B3674717 : Blo 1632515 3674717 := bbase (se 3 (by rfl) ⟨689009, by rfl⟩ : syracuseStep 3674717 = 1378019) (by norm_num)
theorem B4133501 : Blo 1632515 4133501 := bbase (se 3 (by rfl) ⟨775031, by rfl⟩ : syracuseStep 4133501 = 1550063) (by norm_num)
theorem B2757253 : Blo 1632515 2757253 := bbase (se 4 (by rfl) ⟨258492, by rfl⟩ : syracuseStep 2757253 = 516985) (by norm_num)
theorem B5509781 : Blo 1632515 5509781 := bbase (se 6 (by rfl) ⟨129135, by rfl⟩ : syracuseStep 5509781 = 258271) (by norm_num)
theorem B1962649 : Blo 1632515 1962649 := bbase (se 2 (by rfl) ⟨735993, by rfl⟩ : syracuseStep 1962649 = 1471987) (by norm_num)
theorem B3101341 : Blo 1632515 3101341 := bbase (se 3 (by rfl) ⟨581501, by rfl⟩ : syracuseStep 3101341 = 1163003) (by norm_num)
theorem B3674789 : Blo 1632515 3674789 := bbase (se 4 (by rfl) ⟨344511, by rfl⟩ : syracuseStep 3674789 = 689023) (by norm_num)
theorem B4649653 : Blo 1632515 4649653 := bbase (se 5 (by rfl) ⟨217952, by rfl⟩ : syracuseStep 4649653 = 435905) (by norm_num)
theorem B12399317 : Blo 1632515 12399317 := bbase (se 7 (by rfl) ⟨145304, by rfl⟩ : syracuseStep 12399317 = 290609) (by norm_num)
theorem B2757341 : Blo 1632515 2757341 := bbase (se 3 (by rfl) ⟨517001, by rfl⟩ : syracuseStep 2757341 = 1034003) (by norm_num)
theorem B3674861 : Blo 1632515 3674861 := bbase (se 3 (by rfl) ⟨689036, by rfl⟩ : syracuseStep 3674861 = 1378073) (by norm_num)
theorem B3101485 : Blo 1632515 3101485 := bbase (se 3 (by rfl) ⟨581528, by rfl⟩ : syracuseStep 3101485 = 1163057) (by norm_num)
theorem B3674933 : Blo 1632515 3674933 := bbase (se 5 (by rfl) ⟨172262, by rfl⟩ : syracuseStep 3674933 = 344525) (by norm_num)
theorem B4133693 : Blo 1632515 4133693 := bbase (se 3 (by rfl) ⟨775067, by rfl⟩ : syracuseStep 4133693 = 1550135) (by norm_num)
theorem B3675005 : Blo 1632515 3675005 := bbase (se 3 (by rfl) ⟨689063, by rfl⟩ : syracuseStep 3675005 = 1378127) (by norm_num)
theorem B3675077 : Blo 1632515 3675077 := bbase (se 4 (by rfl) ⟨344538, by rfl⟩ : syracuseStep 3675077 = 689077) (by norm_num)
theorem B3101645 : Blo 1632515 3101645 := bbase (se 3 (by rfl) ⟨581558, by rfl⟩ : syracuseStep 3101645 = 1163117) (by norm_num)
theorem B3675149 : Blo 1632515 3675149 := bbase (se 3 (by rfl) ⟨689090, by rfl⟩ : syracuseStep 3675149 = 1378181) (by norm_num)
theorem B5510213 : Blo 1632515 5510213 := bbase (se 4 (by rfl) ⟨516582, by rfl⟩ : syracuseStep 5510213 = 1033165) (by norm_num)
theorem B3675221 : Blo 1632515 3675221 := bbase (se 8 (by rfl) ⟨21534, by rfl⟩ : syracuseStep 3675221 = 43069) (by norm_num)
theorem B3101789 : Blo 1632515 3101789 := bbase (se 3 (by rfl) ⟨581585, by rfl⟩ : syracuseStep 3101789 = 1163171) (by norm_num)
theorem B4134037 : Blo 1632515 4134037 := bbase (se 6 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 4134037 = 193783) (by norm_num)
theorem B5969045 : Blo 1632515 5969045 := bbase (se 6 (by rfl) ⟨139899, by rfl⟩ : syracuseStep 5969045 = 279799) (by norm_num)
theorem B3675293 : Blo 1632515 3675293 := bbase (se 3 (by rfl) ⟨689117, by rfl⟩ : syracuseStep 3675293 = 1378235) (by norm_num)
theorem B3675365 : Blo 1632515 3675365 := bbase (se 4 (by rfl) ⟨344565, by rfl⟩ : syracuseStep 3675365 = 689131) (by norm_num)
theorem B4134149 : Blo 1632515 4134149 := bbase (se 4 (by rfl) ⟨387576, by rfl⟩ : syracuseStep 4134149 = 775153) (by norm_num)
theorem B6198565 : Blo 1632515 6198565 := bbase (se 4 (by rfl) ⟨581115, by rfl⟩ : syracuseStep 6198565 = 1162231) (by norm_num)
theorem B3978533 : Blo 1632515 3978533 := bbase (se 4 (by rfl) ⟨372987, by rfl⟩ : syracuseStep 3978533 = 745975) (by norm_num)
theorem B3675437 : Blo 1632515 3675437 := bbase (se 3 (by rfl) ⟨689144, by rfl⟩ : syracuseStep 3675437 = 1378289) (by norm_num)
theorem B3675509 : Blo 1632515 3675509 := bbase (se 5 (by rfl) ⟨172289, by rfl⟩ : syracuseStep 3675509 = 344579) (by norm_num)
theorem B3102077 : Blo 1632515 3102077 := bbase (se 3 (by rfl) ⟨581639, by rfl⟩ : syracuseStep 3102077 = 1163279) (by norm_num)
theorem B2651525 : Blo 1632515 2651525 := bbase (se 4 (by rfl) ⟨248580, by rfl⟩ : syracuseStep 2651525 = 497161) (by norm_num)
theorem B28661141 : Blo 1632515 28661141 := bbase (se 6 (by rfl) ⟨671745, by rfl⟩ : syracuseStep 28661141 = 1343491) (by norm_num)
theorem B3675581 : Blo 1632515 3675581 := bbase (se 3 (by rfl) ⟨689171, by rfl⟩ : syracuseStep 3675581 = 1378343) (by norm_num)
theorem B4134341 : Blo 1632515 4134341 := bbase (se 4 (by rfl) ⟨387594, by rfl⟩ : syracuseStep 4134341 = 775189) (by norm_num)
theorem B5510645 : Blo 1632515 5510645 := bbase (se 5 (by rfl) ⟨258311, by rfl⟩ : syracuseStep 5510645 = 516623) (by norm_num)
theorem B3675653 : Blo 1632515 3675653 := bbase (se 4 (by rfl) ⟨344592, by rfl⟩ : syracuseStep 3675653 = 689185) (by norm_num)
theorem B3675725 : Blo 1632515 3675725 := bbase (se 3 (by rfl) ⟨689198, by rfl⟩ : syracuseStep 3675725 = 1378397) (by norm_num)
theorem B6198869 : Blo 1632515 6198869 := bbase (se 8 (by rfl) ⟨36321, by rfl⟩ : syracuseStep 6198869 = 72643) (by norm_num)
theorem B8492645 : Blo 1632515 8492645 := bbase (se 4 (by rfl) ⟨796185, by rfl⟩ : syracuseStep 8492645 = 1592371) (by norm_num)
theorem B3675797 : Blo 1632515 3675797 := bbase (se 6 (by rfl) ⟨86151, by rfl⟩ : syracuseStep 3675797 = 172303) (by norm_num)
theorem B8271557 : Blo 1632515 8271557 := bbase (se 4 (by rfl) ⟨775458, by rfl⟩ : syracuseStep 8271557 = 1550917) (by norm_num)
theorem B6624965 : Blo 1632515 6624965 := bbase (se 4 (by rfl) ⟨621090, by rfl⟩ : syracuseStep 6624965 = 1242181) (by norm_num)
theorem B2651869 : Blo 1632515 2651869 := bbase (se 3 (by rfl) ⟨497225, by rfl⟩ : syracuseStep 2651869 = 994451) (by norm_num)
theorem B3675869 : Blo 1632515 3675869 := bbase (se 3 (by rfl) ⟨689225, by rfl⟩ : syracuseStep 3675869 = 1378451) (by norm_num)
theorem B3978973 : Blo 1632515 3978973 := bbase (se 3 (by rfl) ⟨746057, by rfl⟩ : syracuseStep 3978973 = 1492115) (by norm_num)
theorem B4134685 : Blo 1632515 4134685 := bbase (se 3 (by rfl) ⟨775253, by rfl⟩ : syracuseStep 4134685 = 1550507) (by norm_num)
theorem B3675941 : Blo 1632515 3675941 := bbase (se 4 (by rfl) ⟨344619, by rfl⟩ : syracuseStep 3675941 = 689239) (by norm_num)
theorem B2094913 : Blo 1632515 2094913 := bbase (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) (by norm_num)
theorem B3676013 : Blo 1632515 3676013 := bbase (se 3 (by rfl) ⟨689252, by rfl⟩ : syracuseStep 3676013 = 1378505) (by norm_num)
theorem B4134797 : Blo 1632515 4134797 := bbase (se 3 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 4134797 = 1550549) (by norm_num)
theorem B5511077 : Blo 1632515 5511077 := bbase (se 4 (by rfl) ⟨516663, by rfl⟩ : syracuseStep 5511077 = 1033327) (by norm_num)
theorem B3676085 : Blo 1632515 3676085 := bbase (se 5 (by rfl) ⟨172316, by rfl⟩ : syracuseStep 3676085 = 344633) (by norm_num)
theorem B3676157 : Blo 1632515 3676157 := bbase (se 3 (by rfl) ⟨689279, by rfl⟩ : syracuseStep 3676157 = 1378559) (by norm_num)
theorem B2324485 : Blo 1632515 2324485 := bbase (se 4 (by rfl) ⟨217920, by rfl⟩ : syracuseStep 2324485 = 435841) (by norm_num)
theorem B3676229 : Blo 1632515 3676229 := bbase (se 4 (by rfl) ⟨344646, by rfl⟩ : syracuseStep 3676229 = 689293) (by norm_num)
theorem B4134989 : Blo 1632515 4134989 := bbase (se 3 (by rfl) ⟨775310, by rfl⟩ : syracuseStep 4134989 = 1550621) (by norm_num)
theorem B5232757 : Blo 1632515 5232757 := bbase (se 5 (by rfl) ⟨245285, by rfl⟩ : syracuseStep 5232757 = 490571) (by norm_num)
theorem B3356797 : Blo 1632515 3356797 := bbase (se 3 (by rfl) ⟨629399, by rfl⟩ : syracuseStep 3356797 = 1258799) (by norm_num)
theorem B2095241 : Blo 1632515 2095241 := bbase (se 2 (by rfl) ⟨785715, by rfl⟩ : syracuseStep 2095241 = 1571431) (by norm_num)
theorem B3676301 : Blo 1632515 3676301 := bbase (se 3 (by rfl) ⟨689306, by rfl⟩ : syracuseStep 3676301 = 1378613) (by norm_num)
theorem B4651157 : Blo 1632515 4651157 := bbase (se 6 (by rfl) ⟨109011, by rfl⟩ : syracuseStep 4651157 = 218023) (by norm_num)
theorem B1792153 : Blo 1632515 1792153 := bbase (se 2 (by rfl) ⟨672057, by rfl⟩ : syracuseStep 1792153 = 1344115) (by norm_num)
theorem B3184805 : Blo 1632515 3184805 := bbase (se 4 (by rfl) ⟨298575, by rfl⟩ : syracuseStep 3184805 = 597151) (by norm_num)
theorem B3676373 : Blo 1632515 3676373 := bbase (se 7 (by rfl) ⟨43082, by rfl⟩ : syracuseStep 3676373 = 86165) (by norm_num)
theorem B3676445 : Blo 1632515 3676445 := bbase (se 3 (by rfl) ⟨689333, by rfl⟩ : syracuseStep 3676445 = 1378667) (by norm_num)
theorem B5511509 : Blo 1632515 5511509 := bbase (se 10 (by rfl) ⟨8073, by rfl⟩ : syracuseStep 5511509 = 16147) (by norm_num)
theorem B3676517 : Blo 1632515 3676517 := bbase (se 4 (by rfl) ⟨344673, by rfl⟩ : syracuseStep 3676517 = 689347) (by norm_num)
theorem B5233013 : Blo 1632515 5233013 := bbase (se 5 (by rfl) ⟨245297, by rfl⟩ : syracuseStep 5233013 = 490595) (by norm_num)
theorem B4135333 : Blo 1632515 4135333 := bbase (se 4 (by rfl) ⟨387687, by rfl⟩ : syracuseStep 4135333 = 775375) (by norm_num)
theorem B3488197 : Blo 1632515 3488197 := bbase (se 4 (by rfl) ⟨327018, by rfl⟩ : syracuseStep 3488197 = 654037) (by norm_num)
theorem B4135445 : Blo 1632515 4135445 := bbase (se 6 (by rfl) ⟨96924, by rfl⟩ : syracuseStep 4135445 = 193849) (by norm_num)
theorem B2652725 : Blo 1632515 2652725 := bbase (se 5 (by rfl) ⟨124346, by rfl⟩ : syracuseStep 2652725 = 248693) (by norm_num)
theorem B1743449 : Blo 1632515 1743449 := bbase (se 2 (by rfl) ⟨653793, by rfl⟩ : syracuseStep 1743449 = 1307587) (by norm_num)
theorem B1940089 : Blo 1632515 1940089 := bbase (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) (by norm_num)
theorem B4135637 : Blo 1632515 4135637 := bbase (se 7 (by rfl) ⟨48464, by rfl⟩ : syracuseStep 4135637 = 96929) (by norm_num)
theorem B1768181 : Blo 1632515 1768181 := bbase (se 5 (by rfl) ⟨82883, by rfl⟩ : syracuseStep 1768181 = 165767) (by norm_num)
theorem B5511941 : Blo 1632515 5511941 := bbase (se 4 (by rfl) ⟨516744, by rfl⟩ : syracuseStep 5511941 = 1033489) (by norm_num)
theorem B2325277 : Blo 1632515 2325277 := bbase (se 3 (by rfl) ⟨435989, by rfl⟩ : syracuseStep 2325277 = 871979) (by norm_num)
theorem B1743697 : Blo 1632515 1743697 := bbase (se 2 (by rfl) ⟨653886, by rfl⟩ : syracuseStep 1743697 = 1307773) (by norm_num)
theorem B6978581 : Blo 1632515 6978581 := bbase (se 6 (by rfl) ⟨163560, by rfl⟩ : syracuseStep 6978581 = 327121) (by norm_num)
theorem B4135981 : Blo 1632515 4135981 := bbase (se 3 (by rfl) ⟨775496, by rfl⟩ : syracuseStep 4135981 = 1550993) (by norm_num)
theorem B2325613 : Blo 1632515 2325613 := bbase (se 3 (by rfl) ⟨436052, by rfl⟩ : syracuseStep 2325613 = 872105) (by norm_num)
theorem B4136093 : Blo 1632515 4136093 := bbase (se 3 (by rfl) ⟨775517, by rfl⟩ : syracuseStep 4136093 = 1551035) (by norm_num)
theorem B5512373 : Blo 1632515 5512373 := bbase (se 5 (by rfl) ⟨258392, by rfl⟩ : syracuseStep 5512373 = 516785) (by norm_num)
theorem B1744129 : Blo 1632515 1744129 := bbase (se 2 (by rfl) ⟨654048, by rfl⟩ : syracuseStep 1744129 = 1308097) (by norm_num)
theorem B3489085 : Blo 1632515 3489085 := bbase (se 3 (by rfl) ⟨654203, by rfl⟩ : syracuseStep 3489085 = 1308407) (by norm_num)
theorem B2325829 : Blo 1632515 2325829 := bbase (se 4 (by rfl) ⟨218046, by rfl⟩ : syracuseStep 2325829 = 436093) (by norm_num)
theorem B1744201 : Blo 1632515 1744201 := bbase (se 2 (by rfl) ⟨654075, by rfl⟩ : syracuseStep 1744201 = 1308151) (by norm_num)
theorem B8265077 : Blo 1632515 8265077 := bbase (se 5 (by rfl) ⟨387425, by rfl⟩ : syracuseStep 8265077 = 774851) (by norm_num)
theorem B2448773 : Blo 1632515 2448773 := bbase (se 4 (by rfl) ⟨229572, by rfl⟩ : syracuseStep 2448773 = 459145) (by norm_num)
theorem B2448797 : Blo 1632515 2448797 := bbase (se 3 (by rfl) ⟨459149, by rfl⟩ : syracuseStep 2448797 = 918299) (by norm_num)
theorem B2448821 : Blo 1632515 2448821 := bbase (se 5 (by rfl) ⟨114788, by rfl⟩ : syracuseStep 2448821 = 229577) (by norm_num)
theorem B2448845 : Blo 1632515 2448845 := bbase (se 3 (by rfl) ⟨459158, by rfl⟩ : syracuseStep 2448845 = 918317) (by norm_num)
theorem B2448869 : Blo 1632515 2448869 := bbase (se 4 (by rfl) ⟨229581, by rfl⟩ : syracuseStep 2448869 = 459163) (by norm_num)
theorem B2448893 : Blo 1632515 2448893 := bbase (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) (by norm_num)
theorem B3923453 : Blo 1632515 3923453 := bbase (se 3 (by rfl) ⟨735647, by rfl⟩ : syracuseStep 3923453 = 1471295) (by norm_num)
theorem B2448917 : Blo 1632515 2448917 := bbase (se 6 (by rfl) ⟨57396, by rfl⟩ : syracuseStep 2448917 = 114793) (by norm_num)
theorem B2448941 : Blo 1632515 2448941 := bbase (se 3 (by rfl) ⟨459176, by rfl⟩ : syracuseStep 2448941 = 918353) (by norm_num)
theorem B2448965 : Blo 1632515 2448965 := bbase (se 4 (by rfl) ⟨229590, by rfl⟩ : syracuseStep 2448965 = 459181) (by norm_num)
theorem B2448989 : Blo 1632515 2448989 := bbase (se 3 (by rfl) ⟨459185, by rfl⟩ : syracuseStep 2448989 = 918371) (by norm_num)
theorem B5512805 : Blo 1632515 5512805 := bbase (se 4 (by rfl) ⟨516825, by rfl⟩ : syracuseStep 5512805 = 1033651) (by norm_num)
theorem B2449013 : Blo 1632515 2449013 := bbase (se 5 (by rfl) ⟨114797, by rfl⟩ : syracuseStep 2449013 = 229595) (by norm_num)
theorem B2449037 : Blo 1632515 2449037 := bbase (se 3 (by rfl) ⟨459194, by rfl⟩ : syracuseStep 2449037 = 918389) (by norm_num)
theorem B6200981 : Blo 1632515 6200981 := bbase (se 6 (by rfl) ⟨145335, by rfl⟩ : syracuseStep 6200981 = 290671) (by norm_num)
theorem B2449061 : Blo 1632515 2449061 := bbase (se 4 (by rfl) ⟨229599, by rfl⟩ : syracuseStep 2449061 = 459199) (by norm_num)
theorem B2449085 : Blo 1632515 2449085 := bbase (se 3 (by rfl) ⟨459203, by rfl⟩ : syracuseStep 2449085 = 918407) (by norm_num)
theorem B3923645 : Blo 1632515 3923645 := bbase (se 3 (by rfl) ⟨735683, by rfl⟩ : syracuseStep 3923645 = 1471367) (by norm_num)
theorem B1744573 : Blo 1632515 1744573 := bbase (se 3 (by rfl) ⟨327107, by rfl⟩ : syracuseStep 1744573 = 654215) (by norm_num)
theorem B2326205 : Blo 1632515 2326205 := bbase (se 3 (by rfl) ⟨436163, by rfl⟩ : syracuseStep 2326205 = 872327) (by norm_num)
theorem B4652741 : Blo 1632515 4652741 := bbase (se 4 (by rfl) ⟨436194, by rfl⟩ : syracuseStep 4652741 = 872389) (by norm_num)
theorem B2449109 : Blo 1632515 2449109 := bbase (se 7 (by rfl) ⟨28700, by rfl⟩ : syracuseStep 2449109 = 57401) (by norm_num)
theorem B3776213 : Blo 1632515 3776213 := bbase (se 7 (by rfl) ⟨44252, by rfl⟩ : syracuseStep 3776213 = 88505) (by norm_num)
theorem B2449133 : Blo 1632515 2449133 := bbase (se 3 (by rfl) ⟨459212, by rfl⟩ : syracuseStep 2449133 = 918425) (by norm_num)
theorem B2449157 : Blo 1632515 2449157 := bbase (se 4 (by rfl) ⟨229608, by rfl⟩ : syracuseStep 2449157 = 459217) (by norm_num)
theorem B2449181 : Blo 1632515 2449181 := bbase (se 3 (by rfl) ⟨459221, by rfl⟩ : syracuseStep 2449181 = 918443) (by norm_num)
theorem B3489581 : Blo 1632515 3489581 := bbase (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) (by norm_num)
theorem B2449205 : Blo 1632515 2449205 := bbase (se 5 (by rfl) ⟨114806, by rfl⟩ : syracuseStep 2449205 = 229613) (by norm_num)
theorem B2449229 : Blo 1632515 2449229 := bbase (se 3 (by rfl) ⟨459230, by rfl⟩ : syracuseStep 2449229 = 918461) (by norm_num)
theorem B2449253 : Blo 1632515 2449253 := bbase (se 4 (by rfl) ⟨229617, by rfl⟩ : syracuseStep 2449253 = 459235) (by norm_num)
theorem B2449277 : Blo 1632515 2449277 := bbase (se 3 (by rfl) ⟨459239, by rfl⟩ : syracuseStep 2449277 = 918479) (by norm_num)
theorem B2449301 : Blo 1632515 2449301 := bbase (se 6 (by rfl) ⟨57405, by rfl⟩ : syracuseStep 2449301 = 114811) (by norm_num)
theorem B2449325 : Blo 1632515 2449325 := bbase (se 3 (by rfl) ⟨459248, by rfl⟩ : syracuseStep 2449325 = 918497) (by norm_num)
theorem B6201269 : Blo 1632515 6201269 := bbase (se 5 (by rfl) ⟨290684, by rfl⟩ : syracuseStep 6201269 = 581369) (by norm_num)
theorem B2449349 : Blo 1632515 2449349 := bbase (se 4 (by rfl) ⟨229626, by rfl⟩ : syracuseStep 2449349 = 459253) (by norm_num)
theorem B2449373 : Blo 1632515 2449373 := bbase (se 3 (by rfl) ⟨459257, by rfl⟩ : syracuseStep 2449373 = 918515) (by norm_num)
theorem B2449397 : Blo 1632515 2449397 := bbase (se 5 (by rfl) ⟨114815, by rfl⟩ : syracuseStep 2449397 = 229631) (by norm_num)
theorem B12574709 : Blo 1632515 12574709 := bbase (se 5 (by rfl) ⟨589439, by rfl⟩ : syracuseStep 12574709 = 1178879) (by norm_num)
theorem B2449409 : Blo 1632515 2449409 := bstep (se 2 (by rfl) ⟨918528, by rfl⟩ : syracuseStep 2449409 = 1837057) B1837057
theorem B2449427 : Blo 1632515 2449427 := bstep (se 1 (by rfl) ⟨1837070, by rfl⟩ : syracuseStep 2449427 = 3674141) B3674141
theorem B10469411 : Blo 1632515 10469411 := bstep (se 1 (by rfl) ⟨7852058, by rfl⟩ : syracuseStep 10469411 = 15704117) B15704117
theorem B2449457 : Blo 1632515 2449457 := bstep (se 2 (by rfl) ⟨918546, by rfl⟩ : syracuseStep 2449457 = 1837093) B1837093
theorem B2449475 : Blo 1632515 2449475 := bstep (se 1 (by rfl) ⟨1837106, by rfl⟩ : syracuseStep 2449475 = 3674213) B3674213
theorem B2449505 : Blo 1632515 2449505 := bstep (se 2 (by rfl) ⟨918564, by rfl⟩ : syracuseStep 2449505 = 1837129) B1837129
theorem B2449523 : Blo 1632515 2449523 := bstep (se 1 (by rfl) ⟨1837142, by rfl⟩ : syracuseStep 2449523 = 3674285) B3674285
theorem B2449553 : Blo 1632515 2449553 := bstep (se 2 (by rfl) ⟨918582, by rfl⟩ : syracuseStep 2449553 = 1837165) B1837165
theorem B2449571 : Blo 1632515 2449571 := bstep (se 1 (by rfl) ⟨1837178, by rfl⟩ : syracuseStep 2449571 = 3674357) B3674357
theorem B2449601 : Blo 1632515 2449601 := bstep (se 2 (by rfl) ⟨918600, by rfl⟩ : syracuseStep 2449601 = 1837201) B1837201
theorem B2449619 : Blo 1632515 2449619 := bstep (se 1 (by rfl) ⟨1837214, by rfl⟩ : syracuseStep 2449619 = 3674429) B3674429
theorem B5513453 : Blo 1632515 5513453 := bstep (se 3 (by rfl) ⟨1033772, by rfl⟩ : syracuseStep 5513453 = 2067545) B2067545
theorem B2449649 : Blo 1632515 2449649 := bstep (se 2 (by rfl) ⟨918618, by rfl⟩ : syracuseStep 2449649 = 1837237) B1837237
theorem B2449667 : Blo 1632515 2449667 := bstep (se 1 (by rfl) ⟨1837250, by rfl⟩ : syracuseStep 2449667 = 3674501) B3674501
theorem B2449697 : Blo 1632515 2449697 := bstep (se 2 (by rfl) ⟨918636, by rfl⟩ : syracuseStep 2449697 = 1837273) B1837273
theorem B5513507 : Blo 1632515 5513507 := bstep (se 1 (by rfl) ⟨4135130, by rfl⟩ : syracuseStep 5513507 = 8270261) B8270261
theorem B2449715 : Blo 1632515 2449715 := bstep (se 1 (by rfl) ⟨1837286, by rfl⟩ : syracuseStep 2449715 = 3674573) B3674573
theorem B2449745 : Blo 1632515 2449745 := bstep (se 2 (by rfl) ⟨918654, by rfl⟩ : syracuseStep 2449745 = 1837309) B1837309
theorem B2449763 : Blo 1632515 2449763 := bstep (se 1 (by rfl) ⟨1837322, by rfl⟩ : syracuseStep 2449763 = 3674645) B3674645
theorem B5587309 : Blo 1632515 5587309 := bstep (se 3 (by rfl) ⟨1047620, by rfl⟩ : syracuseStep 5587309 = 2095241) B2095241
theorem B2449793 : Blo 1632515 2449793 := bstep (se 2 (by rfl) ⟨918672, by rfl⟩ : syracuseStep 2449793 = 1837345) B1837345
theorem B9929101 : Blo 1632515 9929101 := bstep (se 3 (by rfl) ⟨1861706, by rfl⟩ : syracuseStep 9929101 = 3723413) B3723413
theorem B2449811 : Blo 1632515 2449811 := bstep (se 1 (by rfl) ⟨1837358, by rfl⟩ : syracuseStep 2449811 = 3674717) B3674717
theorem B2449841 : Blo 1632515 2449841 := bstep (se 2 (by rfl) ⟨918690, by rfl⟩ : syracuseStep 2449841 = 1837381) B1837381
theorem B2449859 : Blo 1632515 2449859 := bstep (se 1 (by rfl) ⟨1837394, by rfl⟩ : syracuseStep 2449859 = 3674789) B3674789
theorem B2449889 : Blo 1632515 2449889 := bstep (se 2 (by rfl) ⟨918708, by rfl⟩ : syracuseStep 2449889 = 1837417) B1837417
theorem B8266211 : Blo 1632515 8266211 := bstep (se 1 (by rfl) ⟨6199658, by rfl⟩ : syracuseStep 8266211 = 12399317) B12399317
theorem B2449907 : Blo 1632515 2449907 := bstep (se 1 (by rfl) ⟨1837430, by rfl⟩ : syracuseStep 2449907 = 3674861) B3674861
theorem B2449937 : Blo 1632515 2449937 := bstep (se 2 (by rfl) ⟨918726, by rfl⟩ : syracuseStep 2449937 = 1837453) B1837453
theorem B2449955 : Blo 1632515 2449955 := bstep (se 1 (by rfl) ⟨1837466, by rfl⟩ : syracuseStep 2449955 = 3674933) B3674933
theorem B5513777 : Blo 1632515 5513777 := bstep (se 2 (by rfl) ⟨2067666, by rfl⟩ : syracuseStep 5513777 = 4135333) B4135333
theorem B2449985 : Blo 1632515 2449985 := bstep (se 2 (by rfl) ⟨918744, by rfl⟩ : syracuseStep 2449985 = 1837489) B1837489
theorem B2450003 : Blo 1632515 2450003 := bstep (se 1 (by rfl) ⟨1837502, by rfl⟩ : syracuseStep 2450003 = 3675005) B3675005
theorem B2450033 : Blo 1632515 2450033 := bstep (se 2 (by rfl) ⟨918762, by rfl⟩ : syracuseStep 2450033 = 1837525) B1837525
theorem B2450051 : Blo 1632515 2450051 := bstep (se 1 (by rfl) ⟨1837538, by rfl⟩ : syracuseStep 2450051 = 3675077) B3675077
theorem B2450081 : Blo 1632515 2450081 := bstep (se 2 (by rfl) ⟨918780, by rfl⟩ : syracuseStep 2450081 = 1837561) B1837561
theorem B2450099 : Blo 1632515 2450099 := bstep (se 1 (by rfl) ⟨1837574, by rfl⟩ : syracuseStep 2450099 = 3675149) B3675149
theorem B2450129 : Blo 1632515 2450129 := bstep (se 2 (by rfl) ⟨918798, by rfl⟩ : syracuseStep 2450129 = 1837597) B1837597
theorem B2450147 : Blo 1632515 2450147 := bstep (se 1 (by rfl) ⟨1837610, by rfl⟩ : syracuseStep 2450147 = 3675221) B3675221
theorem B2450177 : Blo 1632515 2450177 := bstep (se 2 (by rfl) ⟨918816, by rfl⟩ : syracuseStep 2450177 = 1837633) B1837633
theorem B2450195 : Blo 1632515 2450195 := bstep (se 1 (by rfl) ⟨1837646, by rfl⟩ : syracuseStep 2450195 = 3675293) B3675293
theorem B2450225 : Blo 1632515 2450225 := bstep (se 2 (by rfl) ⟨918834, by rfl⟩ : syracuseStep 2450225 = 1837669) B1837669
theorem B2450243 : Blo 1632515 2450243 := bstep (se 1 (by rfl) ⟨1837682, by rfl⟩ : syracuseStep 2450243 = 3675365) B3675365
theorem B2450273 : Blo 1632515 2450273 := bstep (se 2 (by rfl) ⟨918852, by rfl⟩ : syracuseStep 2450273 = 1837705) B1837705
theorem B2450291 : Blo 1632515 2450291 := bstep (se 1 (by rfl) ⟨1837718, by rfl⟩ : syracuseStep 2450291 = 3675437) B3675437
theorem B2450321 : Blo 1632515 2450321 := bstep (se 2 (by rfl) ⟨918870, by rfl⟩ : syracuseStep 2450321 = 1837741) B1837741
theorem B2450339 : Blo 1632515 2450339 := bstep (se 1 (by rfl) ⟨1837754, by rfl⟩ : syracuseStep 2450339 = 3675509) B3675509
theorem B18596789 : Blo 1632515 18596789 := bstep (se 5 (by rfl) ⟨871724, by rfl⟩ : syracuseStep 18596789 = 1743449) B1743449
theorem B2450369 : Blo 1632515 2450369 := bstep (se 2 (by rfl) ⟨918888, by rfl⟩ : syracuseStep 2450369 = 1837777) B1837777
theorem B2450387 : Blo 1632515 2450387 := bstep (se 1 (by rfl) ⟨1837790, by rfl⟩ : syracuseStep 2450387 = 3675581) B3675581
theorem B2450417 : Blo 1632515 2450417 := bstep (se 2 (by rfl) ⟨918906, by rfl⟩ : syracuseStep 2450417 = 1837813) B1837813
theorem B2450435 : Blo 1632515 2450435 := bstep (se 1 (by rfl) ⟨1837826, by rfl⟩ : syracuseStep 2450435 = 3675653) B3675653
theorem B2450465 : Blo 1632515 2450465 := bstep (se 2 (by rfl) ⟨918924, by rfl⟩ : syracuseStep 2450465 = 1837849) B1837849
theorem B2450483 : Blo 1632515 2450483 := bstep (se 1 (by rfl) ⟨1837862, by rfl⟩ : syracuseStep 2450483 = 3675725) B3675725
theorem B5514317 : Blo 1632515 5514317 := bstep (se 3 (by rfl) ⟨1033934, by rfl⟩ : syracuseStep 5514317 = 2067869) B2067869
theorem B2450513 : Blo 1632515 2450513 := bstep (se 2 (by rfl) ⟨918942, by rfl⟩ : syracuseStep 2450513 = 1837885) B1837885
theorem B2450531 : Blo 1632515 2450531 := bstep (se 1 (by rfl) ⟨1837898, by rfl⟩ : syracuseStep 2450531 = 3675797) B3675797
theorem B2450561 : Blo 1632515 2450561 := bstep (se 2 (by rfl) ⟨918960, by rfl⟩ : syracuseStep 2450561 = 1837921) B1837921
theorem B5514371 : Blo 1632515 5514371 := bstep (se 1 (by rfl) ⟨4135778, by rfl⟩ : syracuseStep 5514371 = 8271557) B8271557
theorem B4416643 : Blo 1632515 4416643 := bstep (se 1 (by rfl) ⟨3312482, by rfl⟩ : syracuseStep 4416643 = 6624965) B6624965
theorem B4416653 : Blo 1632515 4416653 := bstep (se 3 (by rfl) ⟨828122, by rfl⟩ : syracuseStep 4416653 = 1656245) B1656245
theorem B2450579 : Blo 1632515 2450579 := bstep (se 1 (by rfl) ⟨1837934, by rfl⟩ : syracuseStep 2450579 = 3675869) B3675869
theorem B2942129 : Blo 1632515 2942129 := bstep (se 2 (by rfl) ⟨1103298, by rfl⟩ : syracuseStep 2942129 = 2206597) B2206597
theorem B2450609 : Blo 1632515 2450609 := bstep (se 2 (by rfl) ⟨918978, by rfl⟩ : syracuseStep 2450609 = 1837957) B1837957
theorem B2450627 : Blo 1632515 2450627 := bstep (se 1 (by rfl) ⟨1837970, by rfl⟩ : syracuseStep 2450627 = 3675941) B3675941
theorem B2450657 : Blo 1632515 2450657 := bstep (se 2 (by rfl) ⟨918996, by rfl⟩ : syracuseStep 2450657 = 1837993) B1837993
theorem B2450675 : Blo 1632515 2450675 := bstep (se 1 (by rfl) ⟨1838006, by rfl⟩ : syracuseStep 2450675 = 3676013) B3676013
theorem B8267021 : Blo 1632515 8267021 := bstep (se 3 (by rfl) ⟨1550066, by rfl⟩ : syracuseStep 8267021 = 3100133) B3100133
theorem B2450705 : Blo 1632515 2450705 := bstep (se 2 (by rfl) ⟨919014, by rfl⟩ : syracuseStep 2450705 = 1838029) B1838029
theorem B2450723 : Blo 1632515 2450723 := bstep (se 1 (by rfl) ⟨1838042, by rfl⟩ : syracuseStep 2450723 = 3676085) B3676085
theorem B2450753 : Blo 1632515 2450753 := bstep (se 2 (by rfl) ⟨919032, by rfl⟩ : syracuseStep 2450753 = 1838065) B1838065
theorem B2450771 : Blo 1632515 2450771 := bstep (se 1 (by rfl) ⟨1838078, by rfl⟩ : syracuseStep 2450771 = 3676157) B3676157
theorem B2450801 : Blo 1632515 2450801 := bstep (se 2 (by rfl) ⟨919050, by rfl⟩ : syracuseStep 2450801 = 1838101) B1838101
theorem B2450819 : Blo 1632515 2450819 := bstep (se 1 (by rfl) ⟨1838114, by rfl⟩ : syracuseStep 2450819 = 3676229) B3676229
theorem B5514641 : Blo 1632515 5514641 := bstep (se 2 (by rfl) ⟨2067990, by rfl⟩ : syracuseStep 5514641 = 4135981) B4135981
theorem B2450849 : Blo 1632515 2450849 := bstep (se 2 (by rfl) ⟨919068, by rfl⟩ : syracuseStep 2450849 = 1838137) B1838137
theorem B2450867 : Blo 1632515 2450867 := bstep (se 1 (by rfl) ⟨1838150, by rfl⟩ : syracuseStep 2450867 = 3676301) B3676301
theorem B2450897 : Blo 1632515 2450897 := bstep (se 2 (by rfl) ⟨919086, by rfl⟩ : syracuseStep 2450897 = 1838173) B1838173
theorem B2450915 : Blo 1632515 2450915 := bstep (se 1 (by rfl) ⟨1838186, by rfl⟩ : syracuseStep 2450915 = 3676373) B3676373
theorem B2450945 : Blo 1632515 2450945 := bstep (se 2 (by rfl) ⟨919104, by rfl⟩ : syracuseStep 2450945 = 1838209) B1838209
theorem B2450963 : Blo 1632515 2450963 := bstep (se 1 (by rfl) ⟨1838222, by rfl⟩ : syracuseStep 2450963 = 3676445) B3676445
theorem B2450993 : Blo 1632515 2450993 := bstep (se 2 (by rfl) ⟨919122, by rfl⟩ : syracuseStep 2450993 = 1838245) B1838245
theorem B2451011 : Blo 1632515 2451011 := bstep (se 1 (by rfl) ⟨1838258, by rfl⟩ : syracuseStep 2451011 = 3676517) B3676517
theorem B3311185 : Blo 1632515 3311185 := bstep (se 2 (by rfl) ⟨1241694, by rfl⟩ : syracuseStep 3311185 = 2483389) B2483389
theorem B1836643 : Blo 1632515 1836643 := bstep (se 1 (by rfl) ⟨1377482, by rfl⟩ : syracuseStep 1836643 = 2754965) B2754965
theorem B1836787 : Blo 1632515 1836787 := bstep (se 1 (by rfl) ⟨1377590, by rfl⟩ : syracuseStep 1836787 = 2755181) B2755181
theorem B9299717 : Blo 1632515 9299717 := bstep (se 4 (by rfl) ⟨871848, by rfl⟩ : syracuseStep 9299717 = 1743697) B1743697
theorem B10463053 : Blo 1632515 10463053 := bstep (se 3 (by rfl) ⟨1961822, by rfl⟩ : syracuseStep 10463053 = 3923645) B3923645
theorem B6203213 : Blo 1632515 6203213 := bstep (se 3 (by rfl) ⟨1163102, by rfl⟩ : syracuseStep 6203213 = 2326205) B2326205
theorem B1836931 : Blo 1632515 1836931 := bstep (se 1 (by rfl) ⟨1377698, by rfl⟩ : syracuseStep 1836931 = 2755397) B2755397
theorem B1837075 : Blo 1632515 1837075 := bstep (se 1 (by rfl) ⟨1377806, by rfl⟩ : syracuseStep 1837075 = 2755613) B2755613
theorem B2066467 : Blo 1632515 2066467 := bstep (se 1 (by rfl) ⟨1549850, by rfl⟩ : syracuseStep 2066467 = 3099701) B3099701
theorem B2066563 : Blo 1632515 2066563 := bstep (se 1 (by rfl) ⟨1549922, by rfl⟩ : syracuseStep 2066563 = 3099845) B3099845
theorem B1837219 : Blo 1632515 1837219 := bstep (se 1 (by rfl) ⟨1377914, by rfl⟩ : syracuseStep 1837219 = 2755829) B2755829
theorem B1632515 : Blo 1632515 1632515 := bstep (se 1 (by rfl) ⟨1224386, by rfl⟩ : syracuseStep 1632515 = 2448773) B2448773
theorem B1632531 : Blo 1632515 1632531 := bstep (se 1 (by rfl) ⟨1224398, by rfl⟩ : syracuseStep 1632531 = 2448797) B2448797
theorem B1632547 : Blo 1632515 1632547 := bstep (se 1 (by rfl) ⟨1224410, by rfl⟩ : syracuseStep 1632547 = 2448821) B2448821
theorem B1632563 : Blo 1632515 1632563 := bstep (se 1 (by rfl) ⟨1224422, by rfl⟩ : syracuseStep 1632563 = 2448845) B2448845
theorem B1837363 : Blo 1632515 1837363 := bstep (se 1 (by rfl) ⟨1378022, by rfl⟩ : syracuseStep 1837363 = 2756045) B2756045
theorem B1632579 : Blo 1632515 1632579 := bstep (se 1 (by rfl) ⟨1224434, by rfl⟩ : syracuseStep 1632579 = 2448869) B2448869
theorem B1632595 : Blo 1632515 1632595 := bstep (se 1 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 1632595 = 2448893) B2448893
theorem B2615635 : Blo 1632515 2615635 := bstep (se 1 (by rfl) ⟨1961726, by rfl⟩ : syracuseStep 2615635 = 3923453) B3923453
theorem B1632611 : Blo 1632515 1632611 := bstep (se 1 (by rfl) ⟨1224458, by rfl⟩ : syracuseStep 1632611 = 2448917) B2448917
theorem B2754931 : Blo 1632515 2754931 := bstep (se 1 (by rfl) ⟨2066198, by rfl⟩ : syracuseStep 2754931 = 4132397) B4132397
theorem B1632627 : Blo 1632515 1632627 := bstep (se 1 (by rfl) ⟨1224470, by rfl⟩ : syracuseStep 1632627 = 2448941) B2448941
theorem B1632643 : Blo 1632515 1632643 := bstep (se 1 (by rfl) ⟨1224482, by rfl⟩ : syracuseStep 1632643 = 2448965) B2448965
theorem B1632659 : Blo 1632515 1632659 := bstep (se 1 (by rfl) ⟨1224494, by rfl⟩ : syracuseStep 1632659 = 2448989) B2448989
theorem B1632675 : Blo 1632515 1632675 := bstep (se 1 (by rfl) ⟨1224506, by rfl⟩ : syracuseStep 1632675 = 2449013) B2449013
theorem B1632691 : Blo 1632515 1632691 := bstep (se 1 (by rfl) ⟨1224518, by rfl⟩ : syracuseStep 1632691 = 2449037) B2449037
theorem B1632707 : Blo 1632515 1632707 := bstep (se 1 (by rfl) ⟨1224530, by rfl⟩ : syracuseStep 1632707 = 2449061) B2449061
theorem B1837507 : Blo 1632515 1837507 := bstep (se 1 (by rfl) ⟨1378130, by rfl⟩ : syracuseStep 1837507 = 2756261) B2756261
theorem B13420997 : Blo 1632515 13420997 := bstep (se 4 (by rfl) ⟨1258218, by rfl⟩ : syracuseStep 13420997 = 2516437) B2516437
theorem B1632723 : Blo 1632515 1632723 := bstep (se 1 (by rfl) ⟨1224542, by rfl⟩ : syracuseStep 1632723 = 2449085) B2449085
theorem B1632739 : Blo 1632515 1632739 := bstep (se 1 (by rfl) ⟨1224554, by rfl⟩ : syracuseStep 1632739 = 2449109) B2449109
theorem B2517475 : Blo 1632515 2517475 := bstep (se 1 (by rfl) ⟨1888106, by rfl⟩ : syracuseStep 2517475 = 3776213) B3776213
theorem B1632755 : Blo 1632515 1632755 := bstep (se 1 (by rfl) ⟨1224566, by rfl⟩ : syracuseStep 1632755 = 2449133) B2449133
theorem B2755073 : Blo 1632515 2755073 := bstep (se 2 (by rfl) ⟨1033152, by rfl⟩ : syracuseStep 2755073 = 2066305) B2066305
theorem B1632771 : Blo 1632515 1632771 := bstep (se 1 (by rfl) ⟨1224578, by rfl⟩ : syracuseStep 1632771 = 2449157) B2449157
theorem B1632787 : Blo 1632515 1632787 := bstep (se 1 (by rfl) ⟨1224590, by rfl⟩ : syracuseStep 1632787 = 2449181) B2449181
theorem B41388565 : Blo 1632515 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B1632803 : Blo 1632515 1632803 := bstep (se 1 (by rfl) ⟨1224602, by rfl⟩ : syracuseStep 1632803 = 2449205) B2449205
theorem B1632819 : Blo 1632515 1632819 := bstep (se 1 (by rfl) ⟨1224614, by rfl⟩ : syracuseStep 1632819 = 2449229) B2449229
theorem B18860597 : Blo 1632515 18860597 := bstep (se 5 (by rfl) ⟨884090, by rfl⟩ : syracuseStep 18860597 = 1768181) B1768181
theorem B1632835 : Blo 1632515 1632835 := bstep (se 1 (by rfl) ⟨1224626, by rfl⟩ : syracuseStep 1632835 = 2449253) B2449253
theorem B1632851 : Blo 1632515 1632851 := bstep (se 1 (by rfl) ⟨1224638, by rfl⟩ : syracuseStep 1632851 = 2449277) B2449277
theorem B1837651 : Blo 1632515 1837651 := bstep (se 1 (by rfl) ⟨1378238, by rfl⟩ : syracuseStep 1837651 = 2756477) B2756477
theorem B2615905 : Blo 1632515 2615905 := bstep (se 2 (by rfl) ⟨980964, by rfl⟩ : syracuseStep 2615905 = 1961929) B1961929
theorem B1632867 : Blo 1632515 1632867 := bstep (se 1 (by rfl) ⟨1224650, by rfl⟩ : syracuseStep 1632867 = 2449301) B2449301
theorem B1632883 : Blo 1632515 1632883 := bstep (se 1 (by rfl) ⟨1224662, by rfl⟩ : syracuseStep 1632883 = 2449325) B2449325
theorem B2067059 : Blo 1632515 2067059 := bstep (se 1 (by rfl) ⟨1550294, by rfl⟩ : syracuseStep 2067059 = 3100589) B3100589
theorem B2755201 : Blo 1632515 2755201 := bstep (se 2 (by rfl) ⟨1033200, by rfl⟩ : syracuseStep 2755201 = 2066401) B2066401
theorem B1632899 : Blo 1632515 1632899 := bstep (se 1 (by rfl) ⟨1224674, by rfl⟩ : syracuseStep 1632899 = 2449349) B2449349
theorem B1632915 : Blo 1632515 1632915 := bstep (se 1 (by rfl) ⟨1224686, by rfl⟩ : syracuseStep 1632915 = 2449373) B2449373
theorem B2615969 : Blo 1632515 2615969 := bstep (se 2 (by rfl) ⟨980988, by rfl⟩ : syracuseStep 2615969 = 1961977) B1961977
theorem B2755235 : Blo 1632515 2755235 := bstep (se 1 (by rfl) ⟨2066426, by rfl⟩ : syracuseStep 2755235 = 4132853) B4132853
theorem B1632931 : Blo 1632515 1632931 := bstep (se 1 (by rfl) ⟨1224698, by rfl⟩ : syracuseStep 1632931 = 2449397) B2449397
theorem B8383139 : Blo 1632515 8383139 := bstep (se 1 (by rfl) ⟨6287354, by rfl⟩ : syracuseStep 8383139 = 12574709) B12574709
theorem B3099313 : Blo 1632515 3099313 := bstep (se 2 (by rfl) ⟨1162242, by rfl⟩ : syracuseStep 3099313 = 2324485) B2324485
theorem B1632947 : Blo 1632515 1632947 := bstep (se 1 (by rfl) ⟨1224710, by rfl⟩ : syracuseStep 1632947 = 2449421) B2449421
theorem B1632963 : Blo 1632515 1632963 := bstep (se 1 (by rfl) ⟨1224722, by rfl⟩ : syracuseStep 1632963 = 2449445) B2449445
theorem B1632979 : Blo 1632515 1632979 := bstep (se 1 (by rfl) ⟨1224734, by rfl⟩ : syracuseStep 1632979 = 2449469) B2449469
theorem B1632995 : Blo 1632515 1632995 := bstep (se 1 (by rfl) ⟨1224746, by rfl⟩ : syracuseStep 1632995 = 2449493) B2449493
theorem B1837795 : Blo 1632515 1837795 := bstep (se 1 (by rfl) ⟨1378346, by rfl⟩ : syracuseStep 1837795 = 2756693) B2756693
theorem B1633011 : Blo 1632515 1633011 := bstep (se 1 (by rfl) ⟨1224758, by rfl⟩ : syracuseStep 1633011 = 2449517) B2449517
theorem B1633027 : Blo 1632515 1633027 := bstep (se 1 (by rfl) ⟨1224770, by rfl⟩ : syracuseStep 1633027 = 2449541) B2449541
theorem B15690509 : Blo 1632515 15690509 := bstep (se 3 (by rfl) ⟨2941970, by rfl⟩ : syracuseStep 15690509 = 5883941) B5883941
theorem B1633043 : Blo 1632515 1633043 := bstep (se 1 (by rfl) ⟨1224782, by rfl⟩ : syracuseStep 1633043 = 2449565) B2449565
theorem B2755363 : Blo 1632515 2755363 := bstep (se 1 (by rfl) ⟨2066522, by rfl⟩ : syracuseStep 2755363 = 4133045) B4133045
theorem B1633059 : Blo 1632515 1633059 := bstep (se 1 (by rfl) ⟨1224794, by rfl⟩ : syracuseStep 1633059 = 2449589) B2449589
theorem B1633075 : Blo 1632515 1633075 := bstep (se 1 (by rfl) ⟨1224806, by rfl⟩ : syracuseStep 1633075 = 2449613) B2449613
theorem B1633091 : Blo 1632515 1633091 := bstep (se 1 (by rfl) ⟨1224818, by rfl⟩ : syracuseStep 1633091 = 2449637) B2449637
theorem B4475729 : Blo 1632515 4475729 := bstep (se 2 (by rfl) ⟨1678398, by rfl⟩ : syracuseStep 4475729 = 3356797) B3356797
theorem B1633107 : Blo 1632515 1633107 := bstep (se 1 (by rfl) ⟨1224830, by rfl⟩ : syracuseStep 1633107 = 2449661) B2449661
theorem B1633123 : Blo 1632515 1633123 := bstep (se 1 (by rfl) ⟨1224842, by rfl⟩ : syracuseStep 1633123 = 2449685) B2449685
theorem B1633139 : Blo 1632515 1633139 := bstep (se 1 (by rfl) ⟨1224854, by rfl⟩ : syracuseStep 1633139 = 2449709) B2449709
theorem B1837939 : Blo 1632515 1837939 := bstep (se 1 (by rfl) ⟨1378454, by rfl⟩ : syracuseStep 1837939 = 2756909) B2756909
theorem B1633155 : Blo 1632515 1633155 := bstep (se 1 (by rfl) ⟨1224866, by rfl⟩ : syracuseStep 1633155 = 2449733) B2449733
theorem B1633171 : Blo 1632515 1633171 := bstep (se 1 (by rfl) ⟨1224878, by rfl⟩ : syracuseStep 1633171 = 2449757) B2449757
theorem B1633187 : Blo 1632515 1633187 := bstep (se 1 (by rfl) ⟨1224890, by rfl⟩ : syracuseStep 1633187 = 2449781) B2449781
theorem B2755505 : Blo 1632515 2755505 := bstep (se 2 (by rfl) ⟨1033314, by rfl⟩ : syracuseStep 2755505 = 2066629) B2066629
theorem B1633203 : Blo 1632515 1633203 := bstep (se 1 (by rfl) ⟨1224902, by rfl⟩ : syracuseStep 1633203 = 2449805) B2449805
theorem B1633219 : Blo 1632515 1633219 := bstep (se 1 (by rfl) ⟨1224914, by rfl⟩ : syracuseStep 1633219 = 2449829) B2449829
theorem B1633235 : Blo 1632515 1633235 := bstep (se 1 (by rfl) ⟨1224926, by rfl⟩ : syracuseStep 1633235 = 2449853) B2449853
theorem B1633251 : Blo 1632515 1633251 := bstep (se 1 (by rfl) ⟨1224938, by rfl⟩ : syracuseStep 1633251 = 2449877) B2449877
theorem B2206705 : Blo 1632515 2206705 := bstep (se 2 (by rfl) ⟨827514, by rfl⟩ : syracuseStep 2206705 = 1655029) B1655029
theorem B1633267 : Blo 1632515 1633267 := bstep (se 1 (by rfl) ⟨1224950, by rfl⟩ : syracuseStep 1633267 = 2449901) B2449901
theorem B1633283 : Blo 1632515 1633283 := bstep (se 1 (by rfl) ⟨1224962, by rfl⟩ : syracuseStep 1633283 = 2449925) B2449925
theorem B1838083 : Blo 1632515 1838083 := bstep (se 1 (by rfl) ⟨1378562, by rfl⟩ : syracuseStep 1838083 = 2757125) B2757125
theorem B1633299 : Blo 1632515 1633299 := bstep (se 1 (by rfl) ⟨1224974, by rfl⟩ : syracuseStep 1633299 = 2449949) B2449949
theorem B1633315 : Blo 1632515 1633315 := bstep (se 1 (by rfl) ⟨1224986, by rfl⟩ : syracuseStep 1633315 = 2449973) B2449973
theorem B2755633 : Blo 1632515 2755633 := bstep (se 2 (by rfl) ⟨1033362, by rfl⟩ : syracuseStep 2755633 = 2066725) B2066725
theorem B1633331 : Blo 1632515 1633331 := bstep (se 1 (by rfl) ⟨1224998, by rfl⟩ : syracuseStep 1633331 = 2449997) B2449997
theorem B1633347 : Blo 1632515 1633347 := bstep (se 1 (by rfl) ⟨1225010, by rfl⟩ : syracuseStep 1633347 = 2450021) B2450021
theorem B3673169 : Blo 1632515 3673169 := bstep (se 2 (by rfl) ⟨1377438, by rfl⟩ : syracuseStep 3673169 = 2754877) B2754877
theorem B2755667 : Blo 1632515 2755667 := bstep (se 1 (by rfl) ⟨2066750, by rfl⟩ : syracuseStep 2755667 = 4133501) B4133501
theorem B1633363 : Blo 1632515 1633363 := bstep (se 1 (by rfl) ⟨1225022, by rfl⟩ : syracuseStep 1633363 = 2450045) B2450045
theorem B3673187 : Blo 1632515 3673187 := bstep (se 1 (by rfl) ⟨2754890, by rfl⟩ : syracuseStep 3673187 = 5509781) B5509781
theorem B1633379 : Blo 1632515 1633379 := bstep (se 1 (by rfl) ⟨1225034, by rfl⟩ : syracuseStep 1633379 = 2450069) B2450069
theorem B1633395 : Blo 1632515 1633395 := bstep (se 1 (by rfl) ⟨1225046, by rfl⟩ : syracuseStep 1633395 = 2450093) B2450093
theorem B1633411 : Blo 1632515 1633411 := bstep (se 1 (by rfl) ⟨1225058, by rfl⟩ : syracuseStep 1633411 = 2450117) B2450117
theorem B19868813 : Blo 1632515 19868813 := bstep (se 3 (by rfl) ⟨3725402, by rfl⟩ : syracuseStep 19868813 = 7450805) B7450805
theorem B1633427 : Blo 1632515 1633427 := bstep (se 1 (by rfl) ⟨1225070, by rfl⟩ : syracuseStep 1633427 = 2450141) B2450141
theorem B1838227 : Blo 1632515 1838227 := bstep (se 1 (by rfl) ⟨1378670, by rfl⟩ : syracuseStep 1838227 = 2757341) B2757341
theorem B1633443 : Blo 1632515 1633443 := bstep (se 1 (by rfl) ⟨1225082, by rfl⟩ : syracuseStep 1633443 = 2450165) B2450165
theorem B1633459 : Blo 1632515 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B1633475 : Blo 1632515 1633475 := bstep (se 1 (by rfl) ⟨1225106, by rfl⟩ : syracuseStep 1633475 = 2450213) B2450213
theorem B2755795 : Blo 1632515 2755795 := bstep (se 1 (by rfl) ⟨2066846, by rfl⟩ : syracuseStep 2755795 = 4133693) B4133693
theorem B1633491 : Blo 1632515 1633491 := bstep (se 1 (by rfl) ⟨1225118, by rfl⟩ : syracuseStep 1633491 = 2450237) B2450237
theorem B1633507 : Blo 1632515 1633507 := bstep (se 1 (by rfl) ⟨1225130, by rfl⟩ : syracuseStep 1633507 = 2450261) B2450261
theorem B11775203 : Blo 1632515 11775203 := bstep (se 1 (by rfl) ⟨8831402, by rfl⟩ : syracuseStep 11775203 = 17662805) B17662805
theorem B1633523 : Blo 1632515 1633523 := bstep (se 1 (by rfl) ⟨1225142, by rfl⟩ : syracuseStep 1633523 = 2450285) B2450285
theorem B1633539 : Blo 1632515 1633539 := bstep (se 1 (by rfl) ⟨1225154, by rfl⟩ : syracuseStep 1633539 = 2450309) B2450309
theorem B1633555 : Blo 1632515 1633555 := bstep (se 1 (by rfl) ⟨1225166, by rfl⟩ : syracuseStep 1633555 = 2450333) B2450333
theorem B1633571 : Blo 1632515 1633571 := bstep (se 1 (by rfl) ⟨1225178, by rfl⟩ : syracuseStep 1633571 = 2450357) B2450357
theorem B1633587 : Blo 1632515 1633587 := bstep (se 1 (by rfl) ⟨1225190, by rfl⟩ : syracuseStep 1633587 = 2450381) B2450381
theorem B2067763 : Blo 1632515 2067763 := bstep (se 1 (by rfl) ⟨1550822, by rfl⟩ : syracuseStep 2067763 = 3101645) B3101645
theorem B1633603 : Blo 1632515 1633603 := bstep (se 1 (by rfl) ⟨1225202, by rfl⟩ : syracuseStep 1633603 = 2450405) B2450405
theorem B1633619 : Blo 1632515 1633619 := bstep (se 1 (by rfl) ⟨1225214, by rfl⟩ : syracuseStep 1633619 = 2450429) B2450429
theorem B2755937 : Blo 1632515 2755937 := bstep (se 2 (by rfl) ⟨1033476, by rfl⟩ : syracuseStep 2755937 = 2066953) B2066953
theorem B1633635 : Blo 1632515 1633635 := bstep (se 1 (by rfl) ⟨1225226, by rfl⟩ : syracuseStep 1633635 = 2450453) B2450453
theorem B3673457 : Blo 1632515 3673457 := bstep (se 2 (by rfl) ⟨1377546, by rfl⟩ : syracuseStep 3673457 = 2755093) B2755093
theorem B1633651 : Blo 1632515 1633651 := bstep (se 1 (by rfl) ⟨1225238, by rfl⟩ : syracuseStep 1633651 = 2450477) B2450477
theorem B3673475 : Blo 1632515 3673475 := bstep (se 1 (by rfl) ⟨2755106, by rfl⟩ : syracuseStep 3673475 = 5510213) B5510213
theorem B4189571 : Blo 1632515 4189571 := bstep (se 1 (by rfl) ⟨3142178, by rfl⟩ : syracuseStep 4189571 = 6284357) B6284357
theorem B1633667 : Blo 1632515 1633667 := bstep (se 1 (by rfl) ⟨1225250, by rfl⟩ : syracuseStep 1633667 = 2450501) B2450501
theorem B1633683 : Blo 1632515 1633683 := bstep (se 1 (by rfl) ⟨1225262, by rfl⟩ : syracuseStep 1633683 = 2450525) B2450525
theorem B2067859 : Blo 1632515 2067859 := bstep (se 1 (by rfl) ⟨1550894, by rfl⟩ : syracuseStep 2067859 = 3101789) B3101789
theorem B1633699 : Blo 1632515 1633699 := bstep (se 1 (by rfl) ⟨1225274, by rfl⟩ : syracuseStep 1633699 = 2450549) B2450549
theorem B1633715 : Blo 1632515 1633715 := bstep (se 1 (by rfl) ⟨1225286, by rfl⟩ : syracuseStep 1633715 = 2450573) B2450573
theorem B4713923 : Blo 1632515 4713923 := bstep (se 1 (by rfl) ⟨3535442, by rfl⟩ : syracuseStep 4713923 = 7070885) B7070885
theorem B1633731 : Blo 1632515 1633731 := bstep (se 1 (by rfl) ⟨1225298, by rfl⟩ : syracuseStep 1633731 = 2450597) B2450597
theorem B2944451 : Blo 1632515 2944451 := bstep (se 1 (by rfl) ⟨2208338, by rfl⟩ : syracuseStep 2944451 = 4416677) B4416677
theorem B5664205 : Blo 1632515 5664205 := bstep (se 3 (by rfl) ⟨1062038, by rfl⟩ : syracuseStep 5664205 = 2124077) B2124077
theorem B1633747 : Blo 1632515 1633747 := bstep (se 1 (by rfl) ⟨1225310, by rfl⟩ : syracuseStep 1633747 = 2450621) B2450621
theorem B2756065 : Blo 1632515 2756065 := bstep (se 2 (by rfl) ⟨1033524, by rfl⟩ : syracuseStep 2756065 = 2067049) B2067049
theorem B1633763 : Blo 1632515 1633763 := bstep (se 1 (by rfl) ⟨1225322, by rfl⟩ : syracuseStep 1633763 = 2450645) B2450645
theorem B1633779 : Blo 1632515 1633779 := bstep (se 1 (by rfl) ⟨1225334, by rfl⟩ : syracuseStep 1633779 = 2450669) B2450669
theorem B2756099 : Blo 1632515 2756099 := bstep (se 1 (by rfl) ⟨2067074, by rfl⟩ : syracuseStep 2756099 = 4134149) B4134149
theorem B1633795 : Blo 1632515 1633795 := bstep (se 1 (by rfl) ⟨1225346, by rfl⟩ : syracuseStep 1633795 = 2450693) B2450693
theorem B1633811 : Blo 1632515 1633811 := bstep (se 1 (by rfl) ⟨1225358, by rfl⟩ : syracuseStep 1633811 = 2450717) B2450717
theorem B6975011 : Blo 1632515 6975011 := bstep (se 1 (by rfl) ⟨5231258, by rfl⟩ : syracuseStep 6975011 = 10462517) B10462517
theorem B1633827 : Blo 1632515 1633827 := bstep (se 1 (by rfl) ⟨1225370, by rfl⟩ : syracuseStep 1633827 = 2450741) B2450741
theorem B1633843 : Blo 1632515 1633843 := bstep (se 1 (by rfl) ⟨1225382, by rfl⟩ : syracuseStep 1633843 = 2450765) B2450765
theorem B1633859 : Blo 1632515 1633859 := bstep (se 1 (by rfl) ⟨1225394, by rfl⟩ : syracuseStep 1633859 = 2450789) B2450789
theorem B1633875 : Blo 1632515 1633875 := bstep (se 1 (by rfl) ⟨1225406, by rfl⟩ : syracuseStep 1633875 = 2450813) B2450813
theorem B19107427 : Blo 1632515 19107427 := bstep (se 1 (by rfl) ⟨14330570, by rfl⟩ : syracuseStep 19107427 = 28661141) B28661141
theorem B1633891 : Blo 1632515 1633891 := bstep (se 1 (by rfl) ⟨1225418, by rfl⟩ : syracuseStep 1633891 = 2450837) B2450837
theorem B1633907 : Blo 1632515 1633907 := bstep (se 1 (by rfl) ⟨1225430, by rfl⟩ : syracuseStep 1633907 = 2450861) B2450861
theorem B2756227 : Blo 1632515 2756227 := bstep (se 1 (by rfl) ⟨2067170, by rfl⟩ : syracuseStep 2756227 = 4134341) B4134341
theorem B1633923 : Blo 1632515 1633923 := bstep (se 1 (by rfl) ⟨1225442, by rfl⟩ : syracuseStep 1633923 = 2450885) B2450885
theorem B3673745 : Blo 1632515 3673745 := bstep (se 2 (by rfl) ⟨1377654, by rfl⟩ : syracuseStep 3673745 = 2755309) B2755309
theorem B1633939 : Blo 1632515 1633939 := bstep (se 1 (by rfl) ⟨1225454, by rfl⟩ : syracuseStep 1633939 = 2450909) B2450909
theorem B3673763 : Blo 1632515 3673763 := bstep (se 1 (by rfl) ⟨2755322, by rfl⟩ : syracuseStep 3673763 = 5510645) B5510645
theorem B1633955 : Blo 1632515 1633955 := bstep (se 1 (by rfl) ⟨1225466, by rfl⟩ : syracuseStep 1633955 = 2450933) B2450933
theorem B4132529 : Blo 1632515 4132529 := bstep (se 2 (by rfl) ⟨1549698, by rfl⟩ : syracuseStep 4132529 = 3099397) B3099397
theorem B1633971 : Blo 1632515 1633971 := bstep (se 1 (by rfl) ⟨1225478, by rfl⟩ : syracuseStep 1633971 = 2450957) B2450957
theorem B1633987 : Blo 1632515 1633987 := bstep (se 1 (by rfl) ⟨1225490, by rfl⟩ : syracuseStep 1633987 = 2450981) B2450981
theorem B15699653 : Blo 1632515 15699653 := bstep (se 4 (by rfl) ⟨1471842, by rfl⟩ : syracuseStep 15699653 = 2943685) B2943685
theorem B3100369 : Blo 1632515 3100369 := bstep (se 2 (by rfl) ⟨1162638, by rfl⟩ : syracuseStep 3100369 = 2325277) B2325277
theorem B1634003 : Blo 1632515 1634003 := bstep (se 1 (by rfl) ⟨1225502, by rfl⟩ : syracuseStep 1634003 = 2451005) B2451005
theorem B4132579 : Blo 1632515 4132579 := bstep (se 1 (by rfl) ⟨3099434, by rfl⟩ : syracuseStep 4132579 = 6198869) B6198869
theorem B2756369 : Blo 1632515 2756369 := bstep (se 2 (by rfl) ⟨1033638, by rfl⟩ : syracuseStep 2756369 = 2067277) B2067277
theorem B21221189 : Blo 1632515 21221189 := bstep (se 4 (by rfl) ⟨1989486, by rfl⟩ : syracuseStep 21221189 = 3978973) B3978973
theorem B4132721 : Blo 1632515 4132721 := bstep (se 2 (by rfl) ⟨1549770, by rfl⟩ : syracuseStep 4132721 = 3099541) B3099541
theorem B2756497 : Blo 1632515 2756497 := bstep (se 2 (by rfl) ⟨1033686, by rfl⟩ : syracuseStep 2756497 = 2067373) B2067373
theorem B3674033 : Blo 1632515 3674033 := bstep (se 2 (by rfl) ⟨1377762, by rfl⟩ : syracuseStep 3674033 = 2755525) B2755525
theorem B2756531 : Blo 1632515 2756531 := bstep (se 1 (by rfl) ⟨2067398, by rfl⟩ : syracuseStep 2756531 = 4134797) B4134797
theorem B3674051 : Blo 1632515 3674051 := bstep (se 1 (by rfl) ⟨2755538, by rfl⟩ : syracuseStep 3674051 = 5511077) B5511077
theorem B2756659 : Blo 1632515 2756659 := bstep (se 1 (by rfl) ⟨2067494, by rfl⟩ : syracuseStep 2756659 = 4134989) B4134989
theorem B3584099 : Blo 1632515 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B3100771 : Blo 1632515 3100771 := bstep (se 1 (by rfl) ⟨2325578, by rfl⟩ : syracuseStep 3100771 = 4651157) B4651157
theorem B8269937 : Blo 1632515 8269937 := bstep (se 2 (by rfl) ⟨3101226, by rfl⟩ : syracuseStep 8269937 = 6202453) B6202453
theorem B3100817 : Blo 1632515 3100817 := bstep (se 2 (by rfl) ⟨1162806, by rfl⟩ : syracuseStep 3100817 = 2325613) B2325613
theorem B2756801 : Blo 1632515 2756801 := bstep (se 2 (by rfl) ⟨1033800, by rfl⟩ : syracuseStep 2756801 = 2067601) B2067601
theorem B3674321 : Blo 1632515 3674321 := bstep (se 2 (by rfl) ⟨1377870, by rfl⟩ : syracuseStep 3674321 = 2755741) B2755741
theorem B3674339 : Blo 1632515 3674339 := bstep (se 1 (by rfl) ⟨2755754, by rfl⟩ : syracuseStep 3674339 = 5511509) B5511509
theorem B22647053 : Blo 1632515 22647053 := bstep (se 3 (by rfl) ⟨4246322, by rfl⟩ : syracuseStep 22647053 = 8492645) B8492645
theorem B45322517 : Blo 1632515 45322517 := bstep (se 6 (by rfl) ⟨1062246, by rfl⟩ : syracuseStep 45322517 = 2124493) B2124493
theorem B2756929 : Blo 1632515 2756929 := bstep (se 2 (by rfl) ⟨1033848, by rfl⟩ : syracuseStep 2756929 = 2067697) B2067697
theorem B18608453 : Blo 1632515 18608453 := bstep (se 4 (by rfl) ⟨1744542, by rfl⟩ : syracuseStep 18608453 = 3489085) B3489085
theorem B2756963 : Blo 1632515 2756963 := bstep (se 1 (by rfl) ⟨2067722, by rfl⟩ : syracuseStep 2756963 = 4135445) B4135445
theorem B3101105 : Blo 1632515 3101105 := bstep (se 2 (by rfl) ⟨1162914, by rfl⟩ : syracuseStep 3101105 = 2325829) B2325829
theorem B2757091 : Blo 1632515 2757091 := bstep (se 1 (by rfl) ⟨2067818, by rfl⟩ : syracuseStep 2757091 = 4135637) B4135637
theorem B3674609 : Blo 1632515 3674609 := bstep (se 2 (by rfl) ⟨1377978, by rfl⟩ : syracuseStep 3674609 = 2755957) B2755957
theorem B3674627 : Blo 1632515 3674627 := bstep (se 1 (by rfl) ⟨2755970, by rfl⟩ : syracuseStep 3674627 = 5511941) B5511941
theorem B5231117 : Blo 1632515 5231117 := bstep (se 3 (by rfl) ⟨980834, by rfl⟩ : syracuseStep 5231117 = 1961669) B1961669
theorem B1962515 : Blo 1632515 1962515 := bstep (se 1 (by rfl) ⟨1471886, by rfl⟩ : syracuseStep 1962515 = 2943773) B2943773
theorem B2757233 : Blo 1632515 2757233 := bstep (se 2 (by rfl) ⟨1033962, by rfl⟩ : syracuseStep 2757233 = 2067925) B2067925
theorem B4649699 : Blo 1632515 4649699 := bstep (se 1 (by rfl) ⟨3487274, by rfl⟩ : syracuseStep 4649699 = 6974549) B6974549
theorem B2757361 : Blo 1632515 2757361 := bstep (se 2 (by rfl) ⟨1034010, by rfl⟩ : syracuseStep 2757361 = 2068021) B2068021
theorem B3674897 : Blo 1632515 3674897 := bstep (se 2 (by rfl) ⟨1378086, by rfl⟩ : syracuseStep 3674897 = 2756173) B2756173
theorem B2757395 : Blo 1632515 2757395 := bstep (se 1 (by rfl) ⟨2068046, by rfl⟩ : syracuseStep 2757395 = 4136093) B4136093
theorem B3674915 : Blo 1632515 3674915 := bstep (se 1 (by rfl) ⟨2756186, by rfl⟩ : syracuseStep 3674915 = 5512373) B5512373
theorem B1962803 : Blo 1632515 1962803 := bstep (se 1 (by rfl) ⟨1472102, by rfl⟩ : syracuseStep 1962803 = 2944205) B2944205
theorem B21214021 : Blo 1632515 21214021 := bstep (se 4 (by rfl) ⟨1988814, by rfl⟩ : syracuseStep 21214021 = 3977629) B3977629
theorem B4133713 : Blo 1632515 4133713 := bstep (se 2 (by rfl) ⟨1550142, by rfl⟩ : syracuseStep 4133713 = 3100285) B3100285
theorem B5509997 : Blo 1632515 5509997 := bstep (se 3 (by rfl) ⟨1033124, by rfl⟩ : syracuseStep 5509997 = 2066249) B2066249
theorem B13243277 : Blo 1632515 13243277 := bstep (se 3 (by rfl) ⟨2483114, by rfl⟩ : syracuseStep 13243277 = 4966229) B4966229
theorem B5510051 : Blo 1632515 5510051 := bstep (se 1 (by rfl) ⟨4132538, by rfl⟩ : syracuseStep 5510051 = 8265077) B8265077
theorem B3535825 : Blo 1632515 3535825 := bstep (se 2 (by rfl) ⟨1325934, by rfl⟩ : syracuseStep 3535825 = 2651869) B2651869
theorem B1962995 : Blo 1632515 1962995 := bstep (se 1 (by rfl) ⟨1472246, by rfl⟩ : syracuseStep 1962995 = 2944493) B2944493
theorem B3675185 : Blo 1632515 3675185 := bstep (se 2 (by rfl) ⟨1378194, by rfl⟩ : syracuseStep 3675185 = 2756389) B2756389
theorem B3675203 : Blo 1632515 3675203 := bstep (se 1 (by rfl) ⟨2756402, by rfl⟩ : syracuseStep 3675203 = 5512805) B5512805
theorem B4133987 : Blo 1632515 4133987 := bstep (se 1 (by rfl) ⟨3100490, by rfl⟩ : syracuseStep 4133987 = 6200981) B6200981
theorem B3101827 : Blo 1632515 3101827 := bstep (se 1 (by rfl) ⟨2326370, by rfl⟩ : syracuseStep 3101827 = 4652741) B4652741
theorem B5510321 : Blo 1632515 5510321 := bstep (se 2 (by rfl) ⟨2066370, by rfl⟩ : syracuseStep 5510321 = 4132741) B4132741
theorem B4134179 : Blo 1632515 4134179 := bstep (se 1 (by rfl) ⟨3100634, by rfl⟩ : syracuseStep 4134179 = 6201269) B6201269
theorem B3675473 : Blo 1632515 3675473 := bstep (se 2 (by rfl) ⟨1378302, by rfl⟩ : syracuseStep 3675473 = 2756605) B2756605
theorem B3675491 : Blo 1632515 3675491 := bstep (se 1 (by rfl) ⟨2756618, by rfl⟩ : syracuseStep 3675491 = 5513237) B5513237
theorem B3487121 : Blo 1632515 3487121 := bstep (se 2 (by rfl) ⟨1307670, by rfl⟩ : syracuseStep 3487121 = 2615341) B2615341
theorem B6977009 : Blo 1632515 6977009 := bstep (se 2 (by rfl) ⟨2616378, by rfl⟩ : syracuseStep 6977009 = 5232757) B5232757
theorem B5740049 : Blo 1632515 5740049 := bstep (se 2 (by rfl) ⟨2152518, by rfl⟩ : syracuseStep 5740049 = 4305037) B4305037
theorem B2389537 : Blo 1632515 2389537 := bstep (se 2 (by rfl) ⟨896076, by rfl⟩ : syracuseStep 2389537 = 1792153) B1792153
theorem B8271395 : Blo 1632515 8271395 := bstep (se 1 (by rfl) ⟨6203546, by rfl⟩ : syracuseStep 8271395 = 12407093) B12407093
theorem B3675761 : Blo 1632515 3675761 := bstep (se 2 (by rfl) ⟨1378410, by rfl⟩ : syracuseStep 3675761 = 2756821) B2756821
theorem B3675779 : Blo 1632515 3675779 := bstep (se 1 (by rfl) ⟨2756834, by rfl⟩ : syracuseStep 3675779 = 5513669) B5513669
theorem B5510861 : Blo 1632515 5510861 := bstep (se 3 (by rfl) ⟨1033286, by rfl⟩ : syracuseStep 5510861 = 2066573) B2066573
theorem B5510915 : Blo 1632515 5510915 := bstep (se 1 (by rfl) ⟨4133186, by rfl⟩ : syracuseStep 5510915 = 8266373) B8266373
theorem B8492813 : Blo 1632515 8492813 := bstep (se 3 (by rfl) ⟨1592402, by rfl⟩ : syracuseStep 8492813 = 3184805) B3184805
theorem B18143075 : Blo 1632515 18143075 := bstep (se 1 (by rfl) ⟨13607306, by rfl⟩ : syracuseStep 18143075 = 27214613) B27214613
theorem B4413325 : Blo 1632515 4413325 := bstep (se 3 (by rfl) ⟨827498, by rfl⟩ : syracuseStep 4413325 = 1654997) B1654997
theorem B3676049 : Blo 1632515 3676049 := bstep (se 2 (by rfl) ⟨1378518, by rfl⟩ : syracuseStep 3676049 = 2757037) B2757037
theorem B3676067 : Blo 1632515 3676067 := bstep (se 1 (by rfl) ⟨2757050, by rfl⟩ : syracuseStep 3676067 = 5514101) B5514101
theorem B4650929 : Blo 1632515 4650929 := bstep (se 2 (by rfl) ⟨1744098, by rfl⟩ : syracuseStep 4650929 = 3488197) B3488197
theorem B7452593 : Blo 1632515 7452593 := bstep (se 2 (by rfl) ⟨2794722, by rfl⟩ : syracuseStep 7452593 = 5589445) B5589445
theorem B5511185 : Blo 1632515 5511185 := bstep (se 2 (by rfl) ⟨2066694, by rfl⟩ : syracuseStep 5511185 = 4133389) B4133389
theorem B3979363 : Blo 1632515 3979363 := bstep (se 1 (by rfl) ⟨2984522, by rfl⟩ : syracuseStep 3979363 = 5969045) B5969045
theorem B10467461 : Blo 1632515 10467461 := bstep (se 4 (by rfl) ⟨981324, by rfl⟩ : syracuseStep 10467461 = 1962649) B1962649
theorem B3676337 : Blo 1632515 3676337 := bstep (se 2 (by rfl) ⟨1378626, by rfl⟩ : syracuseStep 3676337 = 2757253) B2757253
theorem B2652355 : Blo 1632515 2652355 := bstep (se 1 (by rfl) ⟨1989266, by rfl⟩ : syracuseStep 2652355 = 3978533) B3978533
theorem B3676355 : Blo 1632515 3676355 := bstep (se 1 (by rfl) ⟨2757266, by rfl⟩ : syracuseStep 3676355 = 5514533) B5514533
theorem B4135121 : Blo 1632515 4135121 := bstep (se 2 (by rfl) ⟨1550670, by rfl⟩ : syracuseStep 4135121 = 3101341) B3101341
theorem B6199523 : Blo 1632515 6199523 := bstep (se 1 (by rfl) ⟨4649642, by rfl⟩ : syracuseStep 6199523 = 9299285) B9299285
theorem B6199537 : Blo 1632515 6199537 := bstep (se 2 (by rfl) ⟨2324826, by rfl⟩ : syracuseStep 6199537 = 4649653) B4649653
theorem B1767683 : Blo 1632515 1767683 := bstep (se 1 (by rfl) ⟨1325762, by rfl⟩ : syracuseStep 1767683 = 2651525) B2651525
theorem B5232899 : Blo 1632515 5232899 := bstep (se 1 (by rfl) ⟨3924674, by rfl⟩ : syracuseStep 5232899 = 7849349) B7849349
theorem B4135171 : Blo 1632515 4135171 := bstep (se 1 (by rfl) ⟨3101378, by rfl⟩ : syracuseStep 4135171 = 6202757) B6202757
theorem B8272205 : Blo 1632515 8272205 := bstep (se 3 (by rfl) ⟨1551038, by rfl⟩ : syracuseStep 8272205 = 3102077) B3102077
theorem B6977933 : Blo 1632515 6977933 := bstep (se 3 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 6977933 = 2616725) B2616725
theorem B4135313 : Blo 1632515 4135313 := bstep (se 2 (by rfl) ⟨1550742, by rfl⟩ : syracuseStep 4135313 = 3101485) B3101485
theorem B5511725 : Blo 1632515 5511725 := bstep (se 3 (by rfl) ⟨1033448, by rfl⟩ : syracuseStep 5511725 = 2066897) B2066897
theorem B5511779 : Blo 1632515 5511779 := bstep (se 1 (by rfl) ⟨4133834, by rfl⟩ : syracuseStep 5511779 = 8267669) B8267669
theorem B5512049 : Blo 1632515 5512049 := bstep (se 2 (by rfl) ⟨2067018, by rfl⟩ : syracuseStep 5512049 = 4134037) B4134037
theorem B3488675 : Blo 1632515 3488675 := bstep (se 1 (by rfl) ⟨2616506, by rfl⟩ : syracuseStep 3488675 = 5233013) B5233013
theorem B3357617 : Blo 1632515 3357617 := bstep (se 2 (by rfl) ⟨1259106, by rfl⟩ : syracuseStep 3357617 = 2518213) B2518213
theorem B2325505 : Blo 1632515 2325505 := bstep (se 2 (by rfl) ⟨872064, by rfl⟩ : syracuseStep 2325505 = 1744129) B1744129
theorem B1768483 : Blo 1632515 1768483 := bstep (se 1 (by rfl) ⟨1326362, by rfl⟩ : syracuseStep 1768483 = 2652725) B2652725
theorem B8264753 : Blo 1632515 8264753 := bstep (se 2 (by rfl) ⟨3099282, by rfl⟩ : syracuseStep 8264753 = 6198565) B6198565
theorem B2325601 : Blo 1632515 2325601 := bstep (se 2 (by rfl) ⟨872100, by rfl⟩ : syracuseStep 2325601 = 1744201) B1744201
theorem B14900365 : Blo 1632515 14900365 := bstep (se 3 (by rfl) ⟨2793818, by rfl⟩ : syracuseStep 14900365 = 5587637) B5587637
theorem B21216497 : Blo 1632515 21216497 := bstep (se 2 (by rfl) ⟨7956186, by rfl⟩ : syracuseStep 21216497 = 15912373) B15912373
theorem B5233987 : Blo 1632515 5233987 := bstep (se 1 (by rfl) ⟨3925490, by rfl⟩ : syracuseStep 5233987 = 7850981) B7850981
theorem B4652387 : Blo 1632515 4652387 := bstep (se 1 (by rfl) ⟨3489290, by rfl⟩ : syracuseStep 4652387 = 6978581) B6978581
theorem B5512589 : Blo 1632515 5512589 := bstep (se 3 (by rfl) ⟨1033610, by rfl⟩ : syracuseStep 5512589 = 2067221) B2067221
theorem B2448785 : Blo 1632515 2448785 := bstep (se 2 (by rfl) ⟨918294, by rfl⟩ : syracuseStep 2448785 = 1836589) B1836589
theorem B2448803 : Blo 1632515 2448803 := bstep (se 1 (by rfl) ⟨1836602, by rfl⟩ : syracuseStep 2448803 = 3673205) B3673205
theorem B2448833 : Blo 1632515 2448833 := bstep (se 2 (by rfl) ⟨918312, by rfl⟩ : syracuseStep 2448833 = 1836625) B1836625
theorem B5512643 : Blo 1632515 5512643 := bstep (se 1 (by rfl) ⟨4134482, by rfl⟩ : syracuseStep 5512643 = 8268965) B8268965
theorem B9305549 : Blo 1632515 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B5234129 : Blo 1632515 5234129 := bstep (se 2 (by rfl) ⟨1962798, by rfl⟩ : syracuseStep 5234129 = 3925597) B3925597
theorem B2448851 : Blo 1632515 2448851 := bstep (se 1 (by rfl) ⟨1836638, by rfl⟩ : syracuseStep 2448851 = 3673277) B3673277
theorem B1744355 : Blo 1632515 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B2448881 : Blo 1632515 2448881 := bstep (se 2 (by rfl) ⟨918330, by rfl⟩ : syracuseStep 2448881 = 1836661) B1836661
theorem B2448899 : Blo 1632515 2448899 := bstep (se 1 (by rfl) ⟨1836674, by rfl⟩ : syracuseStep 2448899 = 3673349) B3673349
theorem B3923473 : Blo 1632515 3923473 := bstep (se 2 (by rfl) ⟨1471302, by rfl⟩ : syracuseStep 3923473 = 2942605) B2942605
theorem B2448929 : Blo 1632515 2448929 := bstep (se 2 (by rfl) ⟨918348, by rfl⟩ : syracuseStep 2448929 = 1836697) B1836697
theorem B2448947 : Blo 1632515 2448947 := bstep (se 1 (by rfl) ⟨1836710, by rfl⟩ : syracuseStep 2448947 = 3673421) B3673421
theorem B2448977 : Blo 1632515 2448977 := bstep (se 2 (by rfl) ⟨918366, by rfl⟩ : syracuseStep 2448977 = 1836733) B1836733
theorem B2326097 : Blo 1632515 2326097 := bstep (se 2 (by rfl) ⟨872286, by rfl⟩ : syracuseStep 2326097 = 1744573) B1744573
theorem B2448995 : Blo 1632515 2448995 := bstep (se 1 (by rfl) ⟨1836746, by rfl⟩ : syracuseStep 2448995 = 3673493) B3673493
theorem B3923569 : Blo 1632515 3923569 := bstep (se 2 (by rfl) ⟨1471338, by rfl⟩ : syracuseStep 3923569 = 2942677) B2942677
theorem B2449025 : Blo 1632515 2449025 := bstep (se 2 (by rfl) ⟨918384, by rfl⟩ : syracuseStep 2449025 = 1836769) B1836769
theorem B2449043 : Blo 1632515 2449043 := bstep (se 1 (by rfl) ⟨1836782, by rfl⟩ : syracuseStep 2449043 = 3673565) B3673565
theorem B2793107 : Blo 1632515 2793107 := bstep (se 1 (by rfl) ⟨2094830, by rfl⟩ : syracuseStep 2793107 = 4189661) B4189661
theorem B6200995 : Blo 1632515 6200995 := bstep (se 1 (by rfl) ⟨4650746, by rfl⟩ : syracuseStep 6200995 = 9301493) B9301493
theorem B2449073 : Blo 1632515 2449073 := bstep (se 2 (by rfl) ⟨918402, by rfl⟩ : syracuseStep 2449073 = 1836805) B1836805
theorem B2449091 : Blo 1632515 2449091 := bstep (se 1 (by rfl) ⟨1836818, by rfl⟩ : syracuseStep 2449091 = 3673637) B3673637
theorem B5586641 : Blo 1632515 5586641 := bstep (se 2 (by rfl) ⟨2094990, by rfl⟩ : syracuseStep 5586641 = 4189981) B4189981
theorem B5512913 : Blo 1632515 5512913 := bstep (se 2 (by rfl) ⟨2067342, by rfl⟩ : syracuseStep 5512913 = 4134685) B4134685
theorem B2449121 : Blo 1632515 2449121 := bstep (se 2 (by rfl) ⟨918420, by rfl⟩ : syracuseStep 2449121 = 1836841) B1836841
theorem B3923683 : Blo 1632515 3923683 := bstep (se 1 (by rfl) ⟨2942762, by rfl⟩ : syracuseStep 3923683 = 5885525) B5885525
theorem B2449139 : Blo 1632515 2449139 := bstep (se 1 (by rfl) ⟨1836854, by rfl⟩ : syracuseStep 2449139 = 3673709) B3673709
theorem B2793217 : Blo 1632515 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B2449169 : Blo 1632515 2449169 := bstep (se 2 (by rfl) ⟨918438, by rfl⟩ : syracuseStep 2449169 = 1836877) B1836877
theorem B5447459 : Blo 1632515 5447459 := bstep (se 1 (by rfl) ⟨4085594, by rfl⟩ : syracuseStep 5447459 = 8171189) B8171189
theorem B2449187 : Blo 1632515 2449187 := bstep (se 1 (by rfl) ⟨1836890, by rfl⟩ : syracuseStep 2449187 = 3673781) B3673781
theorem B3923761 : Blo 1632515 3923761 := bstep (se 2 (by rfl) ⟨1471410, by rfl⟩ : syracuseStep 3923761 = 2942821) B2942821
theorem B2449217 : Blo 1632515 2449217 := bstep (se 2 (by rfl) ⟨918456, by rfl⟩ : syracuseStep 2449217 = 1836913) B1836913
theorem B2449235 : Blo 1632515 2449235 := bstep (se 1 (by rfl) ⟨1836926, by rfl⟩ : syracuseStep 2449235 = 3673853) B3673853
theorem B2449265 : Blo 1632515 2449265 := bstep (se 2 (by rfl) ⟨918474, by rfl⟩ : syracuseStep 2449265 = 1836949) B1836949
theorem B2449283 : Blo 1632515 2449283 := bstep (se 1 (by rfl) ⟨1836962, by rfl⟩ : syracuseStep 2449283 = 3673925) B3673925
theorem B2449313 : Blo 1632515 2449313 := bstep (se 2 (by rfl) ⟨918492, by rfl⟩ : syracuseStep 2449313 = 1836985) B1836985
theorem B9297827 : Blo 1632515 9297827 := bstep (se 1 (by rfl) ⟨6973370, by rfl⟩ : syracuseStep 9297827 = 13946741) B13946741
theorem B2449331 : Blo 1632515 2449331 := bstep (se 1 (by rfl) ⟨1836998, by rfl⟩ : syracuseStep 2449331 = 3673997) B3673997
theorem B2449361 : Blo 1632515 2449361 := bstep (se 2 (by rfl) ⟨918510, by rfl⟩ : syracuseStep 2449361 = 1837021) B1837021
theorem B2449379 : Blo 1632515 2449379 := bstep (se 1 (by rfl) ⟨1837034, by rfl⟩ : syracuseStep 2449379 = 3674069) B3674069
theorem B6979607 : Blo 1632515 6979607 := bstep (se 1 (by rfl) ⟨5234705, by rfl⟩ : syracuseStep 6979607 = 10469411) B10469411
theorem B2449433 : Blo 1632515 2449433 := bstep (se 2 (by rfl) ⟨918537, by rfl⟩ : syracuseStep 2449433 = 1837075) B1837075
theorem B5513291 : Blo 1632515 5513291 := bstep (se 1 (by rfl) ⟨4134968, by rfl⟩ : syracuseStep 5513291 = 8269937) B8269937
theorem B2449547 : Blo 1632515 2449547 := bstep (se 1 (by rfl) ⟨1837160, by rfl⟩ : syracuseStep 2449547 = 3674321) B3674321
theorem B2449559 : Blo 1632515 2449559 := bstep (se 1 (by rfl) ⟨1837169, by rfl⟩ : syracuseStep 2449559 = 3674339) B3674339
theorem B15098035 : Blo 1632515 15098035 := bstep (se 1 (by rfl) ⟨11323526, by rfl⟩ : syracuseStep 15098035 = 22647053) B22647053
theorem B2449625 : Blo 1632515 2449625 := bstep (se 2 (by rfl) ⟨918609, by rfl⟩ : syracuseStep 2449625 = 1837219) B1837219
theorem B8266049 : Blo 1632515 8266049 := bstep (se 2 (by rfl) ⟨3099768, by rfl⟩ : syracuseStep 8266049 = 6199537) B6199537
theorem B2449739 : Blo 1632515 2449739 := bstep (se 1 (by rfl) ⟨1837304, by rfl⟩ : syracuseStep 2449739 = 3674609) B3674609
theorem B2449751 : Blo 1632515 2449751 := bstep (se 1 (by rfl) ⟨1837313, by rfl⟩ : syracuseStep 2449751 = 3674627) B3674627
theorem B5513561 : Blo 1632515 5513561 := bstep (se 2 (by rfl) ⟨2067585, by rfl⟩ : syracuseStep 5513561 = 4135171) B4135171
theorem B2449817 : Blo 1632515 2449817 := bstep (se 2 (by rfl) ⟨918681, by rfl⟩ : syracuseStep 2449817 = 1837363) B1837363
theorem B12403205 : Blo 1632515 12403205 := bstep (se 4 (by rfl) ⟨1162800, by rfl⟩ : syracuseStep 12403205 = 2325601) B2325601
theorem B2449931 : Blo 1632515 2449931 := bstep (se 1 (by rfl) ⟨1837448, by rfl⟩ : syracuseStep 2449931 = 3674897) B3674897
theorem B13238801 : Blo 1632515 13238801 := bstep (se 2 (by rfl) ⟨4964550, by rfl⟩ : syracuseStep 13238801 = 9929101) B9929101
theorem B2449943 : Blo 1632515 2449943 := bstep (se 1 (by rfl) ⟨1837457, by rfl⟩ : syracuseStep 2449943 = 3674915) B3674915
theorem B2450009 : Blo 1632515 2450009 := bstep (se 2 (by rfl) ⟨918753, by rfl⟩ : syracuseStep 2450009 = 1837507) B1837507
theorem B2450123 : Blo 1632515 2450123 := bstep (se 1 (by rfl) ⟨1837592, by rfl⟩ : syracuseStep 2450123 = 3675185) B3675185
theorem B2450135 : Blo 1632515 2450135 := bstep (se 1 (by rfl) ⟨1837601, by rfl⟩ : syracuseStep 2450135 = 3675203) B3675203
theorem B2450201 : Blo 1632515 2450201 := bstep (se 2 (by rfl) ⟨918825, by rfl⟩ : syracuseStep 2450201 = 1837651) B1837651
theorem B2450315 : Blo 1632515 2450315 := bstep (se 1 (by rfl) ⟨1837736, by rfl⟩ : syracuseStep 2450315 = 3675473) B3675473
theorem B2450327 : Blo 1632515 2450327 := bstep (se 1 (by rfl) ⟨1837745, by rfl⟩ : syracuseStep 2450327 = 3675491) B3675491
theorem B2450393 : Blo 1632515 2450393 := bstep (se 2 (by rfl) ⟨918897, by rfl⟩ : syracuseStep 2450393 = 1837795) B1837795
theorem B3826699 : Blo 1632515 3826699 := bstep (se 1 (by rfl) ⟨2870024, by rfl⟩ : syracuseStep 3826699 = 5740049) B5740049
theorem B5514263 : Blo 1632515 5514263 := bstep (se 1 (by rfl) ⟨4135697, by rfl⟩ : syracuseStep 5514263 = 8271395) B8271395
theorem B2450507 : Blo 1632515 2450507 := bstep (se 1 (by rfl) ⟨1837880, by rfl⟩ : syracuseStep 2450507 = 3675761) B3675761
theorem B2450519 : Blo 1632515 2450519 := bstep (se 1 (by rfl) ⟨1837889, by rfl⟩ : syracuseStep 2450519 = 3675779) B3675779
theorem B2450585 : Blo 1632515 2450585 := bstep (se 2 (by rfl) ⟨918969, by rfl⟩ : syracuseStep 2450585 = 1837939) B1837939
theorem B5661875 : Blo 1632515 5661875 := bstep (se 1 (by rfl) ⟨4246406, by rfl⟩ : syracuseStep 5661875 = 8492813) B8492813
theorem B2450699 : Blo 1632515 2450699 := bstep (se 1 (by rfl) ⟨1838024, by rfl⟩ : syracuseStep 2450699 = 3676049) B3676049
theorem B2450711 : Blo 1632515 2450711 := bstep (se 1 (by rfl) ⟨1838033, by rfl⟩ : syracuseStep 2450711 = 3676067) B3676067
theorem B2942273 : Blo 1632515 2942273 := bstep (se 2 (by rfl) ⟨1103352, by rfl⟩ : syracuseStep 2942273 = 2206705) B2206705
theorem B2450777 : Blo 1632515 2450777 := bstep (se 2 (by rfl) ⟨919041, by rfl⟩ : syracuseStep 2450777 = 1838083) B1838083
theorem B2450891 : Blo 1632515 2450891 := bstep (se 1 (by rfl) ⟨1838168, by rfl⟩ : syracuseStep 2450891 = 3676337) B3676337
theorem B2450903 : Blo 1632515 2450903 := bstep (se 1 (by rfl) ⟨1838177, by rfl⟩ : syracuseStep 2450903 = 3676355) B3676355
theorem B19867153 : Blo 1632515 19867153 := bstep (se 2 (by rfl) ⟨7450182, by rfl⟩ : syracuseStep 19867153 = 14900365) B14900365
theorem B2450969 : Blo 1632515 2450969 := bstep (se 2 (by rfl) ⟨919113, by rfl⟩ : syracuseStep 2450969 = 1838227) B1838227
theorem B6202925 : Blo 1632515 6202925 := bstep (se 3 (by rfl) ⟨1163048, by rfl⟩ : syracuseStep 6202925 = 2326097) B2326097
theorem B5514803 : Blo 1632515 5514803 := bstep (se 1 (by rfl) ⟨4136102, by rfl⟩ : syracuseStep 5514803 = 8272205) B8272205
theorem B8947331 : Blo 1632515 8947331 := bstep (se 1 (by rfl) ⟨6710498, by rfl⟩ : syracuseStep 8947331 = 13420997) B13420997
theorem B1836715 : Blo 1632515 1836715 := bstep (se 1 (by rfl) ⟨1377536, by rfl⟩ : syracuseStep 1836715 = 2755073) B2755073
theorem B1836823 : Blo 1632515 1836823 := bstep (se 1 (by rfl) ⟨1377617, by rfl⟩ : syracuseStep 1836823 = 2755235) B2755235
theorem B5588759 : Blo 1632515 5588759 := bstep (se 1 (by rfl) ⟨4191569, by rfl⟩ : syracuseStep 5588759 = 8383139) B8383139
theorem B2983819 : Blo 1632515 2983819 := bstep (se 1 (by rfl) ⟨2237864, by rfl⟩ : syracuseStep 2983819 = 4475729) B4475729
theorem B1837003 : Blo 1632515 1837003 := bstep (se 1 (by rfl) ⟨1377752, by rfl⟩ : syracuseStep 1837003 = 2755505) B2755505
theorem B1837111 : Blo 1632515 1837111 := bstep (se 1 (by rfl) ⟨1377833, by rfl⟩ : syracuseStep 1837111 = 2755667) B2755667
theorem B7850135 : Blo 1632515 7850135 := bstep (se 1 (by rfl) ⟨5887601, by rfl⟩ : syracuseStep 7850135 = 11775203) B11775203
theorem B8267993 : Blo 1632515 8267993 := bstep (se 2 (by rfl) ⟨3100497, by rfl⟩ : syracuseStep 8267993 = 6200995) B6200995
theorem B1837291 : Blo 1632515 1837291 := bstep (se 1 (by rfl) ⟨1377968, by rfl⟩ : syracuseStep 1837291 = 2755937) B2755937
theorem B1632523 : Blo 1632515 1632523 := bstep (se 1 (by rfl) ⟨1224392, by rfl⟩ : syracuseStep 1632523 = 2448785) B2448785
theorem B1632535 : Blo 1632515 1632535 := bstep (se 1 (by rfl) ⟨1224401, by rfl⟩ : syracuseStep 1632535 = 2448803) B2448803
theorem B1632555 : Blo 1632515 1632555 := bstep (se 1 (by rfl) ⟨1224416, by rfl⟩ : syracuseStep 1632555 = 2448833) B2448833
theorem B6203699 : Blo 1632515 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B1632567 : Blo 1632515 1632567 := bstep (se 1 (by rfl) ⟨1224425, by rfl⟩ : syracuseStep 1632567 = 2448851) B2448851
theorem B1632587 : Blo 1632515 1632587 := bstep (se 1 (by rfl) ⟨1224440, by rfl⟩ : syracuseStep 1632587 = 2448881) B2448881
theorem B1632599 : Blo 1632515 1632599 := bstep (se 1 (by rfl) ⟨1224449, by rfl⟩ : syracuseStep 1632599 = 2448899) B2448899
theorem B1837399 : Blo 1632515 1837399 := bstep (se 1 (by rfl) ⟨1378049, by rfl⟩ : syracuseStep 1837399 = 2756099) B2756099
theorem B1632619 : Blo 1632515 1632619 := bstep (se 1 (by rfl) ⟨1224464, by rfl⟩ : syracuseStep 1632619 = 2448929) B2448929
theorem B1632631 : Blo 1632515 1632631 := bstep (se 1 (by rfl) ⟨1224473, by rfl⟩ : syracuseStep 1632631 = 2448947) B2448947
theorem B1632651 : Blo 1632515 1632651 := bstep (se 1 (by rfl) ⟨1224488, by rfl⟩ : syracuseStep 1632651 = 2448977) B2448977
theorem B1632663 : Blo 1632515 1632663 := bstep (se 1 (by rfl) ⟨1224497, by rfl⟩ : syracuseStep 1632663 = 2448995) B2448995
theorem B1632683 : Blo 1632515 1632683 := bstep (se 1 (by rfl) ⟨1224512, by rfl⟩ : syracuseStep 1632683 = 2449025) B2449025
theorem B1632695 : Blo 1632515 1632695 := bstep (se 1 (by rfl) ⟨1224521, by rfl⟩ : syracuseStep 1632695 = 2449043) B2449043
theorem B1862071 : Blo 1632515 1862071 := bstep (se 1 (by rfl) ⟨1396553, by rfl⟩ : syracuseStep 1862071 = 2793107) B2793107
theorem B2755019 : Blo 1632515 2755019 := bstep (se 1 (by rfl) ⟨2066264, by rfl⟩ : syracuseStep 2755019 = 4132529) B4132529
theorem B1632715 : Blo 1632515 1632715 := bstep (se 1 (by rfl) ⟨1224536, by rfl⟩ : syracuseStep 1632715 = 2449073) B2449073
theorem B1632727 : Blo 1632515 1632727 := bstep (se 1 (by rfl) ⟨1224545, by rfl⟩ : syracuseStep 1632727 = 2449091) B2449091
theorem B1632747 : Blo 1632515 1632747 := bstep (se 1 (by rfl) ⟨1224560, by rfl⟩ : syracuseStep 1632747 = 2449121) B2449121
theorem B1632759 : Blo 1632515 1632759 := bstep (se 1 (by rfl) ⟨1224569, by rfl⟩ : syracuseStep 1632759 = 2449139) B2449139
theorem B1632779 : Blo 1632515 1632779 := bstep (se 1 (by rfl) ⟨1224584, by rfl⟩ : syracuseStep 1632779 = 2449169) B2449169
theorem B1837579 : Blo 1632515 1837579 := bstep (se 1 (by rfl) ⟨1378184, by rfl⟩ : syracuseStep 1837579 = 2756369) B2756369
theorem B5884433 : Blo 1632515 5884433 := bstep (se 2 (by rfl) ⟨2206662, by rfl⟩ : syracuseStep 5884433 = 4413325) B4413325
theorem B3631639 : Blo 1632515 3631639 := bstep (se 1 (by rfl) ⟨2723729, by rfl⟩ : syracuseStep 3631639 = 5447459) B5447459
theorem B1632791 : Blo 1632515 1632791 := bstep (se 1 (by rfl) ⟨1224593, by rfl⟩ : syracuseStep 1632791 = 2449187) B2449187
theorem B1632811 : Blo 1632515 1632811 := bstep (se 1 (by rfl) ⟨1224608, by rfl⟩ : syracuseStep 1632811 = 2449217) B2449217
theorem B1632823 : Blo 1632515 1632823 := bstep (se 1 (by rfl) ⟨1224617, by rfl⟩ : syracuseStep 1632823 = 2449235) B2449235
theorem B2755147 : Blo 1632515 2755147 := bstep (se 1 (by rfl) ⟨2066360, by rfl⟩ : syracuseStep 2755147 = 4132721) B4132721
theorem B1632843 : Blo 1632515 1632843 := bstep (se 1 (by rfl) ⟨1224632, by rfl⟩ : syracuseStep 1632843 = 2449265) B2449265
theorem B1632855 : Blo 1632515 1632855 := bstep (se 1 (by rfl) ⟨1224641, by rfl⟩ : syracuseStep 1632855 = 2449283) B2449283
theorem B1632875 : Blo 1632515 1632875 := bstep (se 1 (by rfl) ⟨1224656, by rfl⟩ : syracuseStep 1632875 = 2449313) B2449313
theorem B1632887 : Blo 1632515 1632887 := bstep (se 1 (by rfl) ⟨1224665, by rfl⟩ : syracuseStep 1632887 = 2449331) B2449331
theorem B1837687 : Blo 1632515 1837687 := bstep (se 1 (by rfl) ⟨1378265, by rfl⟩ : syracuseStep 1837687 = 2756531) B2756531
theorem B1632907 : Blo 1632515 1632907 := bstep (se 1 (by rfl) ⟨1224680, by rfl⟩ : syracuseStep 1632907 = 2449361) B2449361
theorem B1632919 : Blo 1632515 1632919 := bstep (se 1 (by rfl) ⟨1224689, by rfl⟩ : syracuseStep 1632919 = 2449379) B2449379
theorem B1632939 : Blo 1632515 1632939 := bstep (se 1 (by rfl) ⟨1224704, by rfl⟩ : syracuseStep 1632939 = 2449409) B2449409
theorem B1632951 : Blo 1632515 1632951 := bstep (se 1 (by rfl) ⟨1224713, by rfl⟩ : syracuseStep 1632951 = 2449427) B2449427
theorem B1632971 : Blo 1632515 1632971 := bstep (se 1 (by rfl) ⟨1224728, by rfl⟩ : syracuseStep 1632971 = 2449457) B2449457
theorem B1632983 : Blo 1632515 1632983 := bstep (se 1 (by rfl) ⟨1224737, by rfl⟩ : syracuseStep 1632983 = 2449475) B2449475
theorem B2755289 : Blo 1632515 2755289 := bstep (se 2 (by rfl) ⟨1033233, by rfl⟩ : syracuseStep 2755289 = 2066467) B2066467
theorem B1633003 : Blo 1632515 1633003 := bstep (se 1 (by rfl) ⟨1224752, by rfl⟩ : syracuseStep 1633003 = 2449505) B2449505
theorem B1633015 : Blo 1632515 1633015 := bstep (se 1 (by rfl) ⟨1224761, by rfl⟩ : syracuseStep 1633015 = 2449523) B2449523
theorem B1633035 : Blo 1632515 1633035 := bstep (se 1 (by rfl) ⟨1224776, by rfl⟩ : syracuseStep 1633035 = 2449553) B2449553
theorem B2067211 : Blo 1632515 2067211 := bstep (se 1 (by rfl) ⟨1550408, by rfl⟩ : syracuseStep 2067211 = 3100817) B3100817
theorem B1633047 : Blo 1632515 1633047 := bstep (se 1 (by rfl) ⟨1224785, by rfl⟩ : syracuseStep 1633047 = 2449571) B2449571
theorem B1633067 : Blo 1632515 1633067 := bstep (se 1 (by rfl) ⟨1224800, by rfl⟩ : syracuseStep 1633067 = 2449601) B2449601
theorem B1837867 : Blo 1632515 1837867 := bstep (se 1 (by rfl) ⟨1378400, by rfl⟩ : syracuseStep 1837867 = 2756801) B2756801
theorem B1633079 : Blo 1632515 1633079 := bstep (se 1 (by rfl) ⟨1224809, by rfl⟩ : syracuseStep 1633079 = 2449619) B2449619
theorem B1633099 : Blo 1632515 1633099 := bstep (se 1 (by rfl) ⟨1224824, by rfl⟩ : syracuseStep 1633099 = 2449649) B2449649
theorem B1633111 : Blo 1632515 1633111 := bstep (se 1 (by rfl) ⟨1224833, by rfl⟩ : syracuseStep 1633111 = 2449667) B2449667
theorem B2755417 : Blo 1632515 2755417 := bstep (se 2 (by rfl) ⟨1033281, by rfl⟩ : syracuseStep 2755417 = 2066563) B2066563
theorem B9431909 : Blo 1632515 9431909 := bstep (se 4 (by rfl) ⟨884241, by rfl⟩ : syracuseStep 9431909 = 1768483) B1768483
theorem B1633131 : Blo 1632515 1633131 := bstep (se 1 (by rfl) ⟨1224848, by rfl⟩ : syracuseStep 1633131 = 2449697) B2449697
theorem B1633143 : Blo 1632515 1633143 := bstep (se 1 (by rfl) ⟨1224857, by rfl⟩ : syracuseStep 1633143 = 2449715) B2449715
theorem B12405635 : Blo 1632515 12405635 := bstep (se 1 (by rfl) ⟨9304226, by rfl⟩ : syracuseStep 12405635 = 18608453) B18608453
theorem B1633163 : Blo 1632515 1633163 := bstep (se 1 (by rfl) ⟨1224872, by rfl⟩ : syracuseStep 1633163 = 2449745) B2449745
theorem B1633175 : Blo 1632515 1633175 := bstep (se 1 (by rfl) ⟨1224881, by rfl⟩ : syracuseStep 1633175 = 2449763) B2449763
theorem B1837975 : Blo 1632515 1837975 := bstep (se 1 (by rfl) ⟨1378481, by rfl⟩ : syracuseStep 1837975 = 2756963) B2756963
theorem B1633195 : Blo 1632515 1633195 := bstep (se 1 (by rfl) ⟨1224896, by rfl⟩ : syracuseStep 1633195 = 2449793) B2449793
theorem B1633207 : Blo 1632515 1633207 := bstep (se 1 (by rfl) ⟨1224905, by rfl⟩ : syracuseStep 1633207 = 2449811) B2449811
theorem B1633227 : Blo 1632515 1633227 := bstep (se 1 (by rfl) ⟨1224920, by rfl⟩ : syracuseStep 1633227 = 2449841) B2449841
theorem B1633239 : Blo 1632515 1633239 := bstep (se 1 (by rfl) ⟨1224929, by rfl⟩ : syracuseStep 1633239 = 2449859) B2449859
theorem B1633259 : Blo 1632515 1633259 := bstep (se 1 (by rfl) ⟨1224944, by rfl⟩ : syracuseStep 1633259 = 2449889) B2449889
theorem B1633271 : Blo 1632515 1633271 := bstep (se 1 (by rfl) ⟨1224953, by rfl⟩ : syracuseStep 1633271 = 2449907) B2449907
theorem B1633291 : Blo 1632515 1633291 := bstep (se 1 (by rfl) ⟨1224968, by rfl⟩ : syracuseStep 1633291 = 2449937) B2449937
theorem B1633303 : Blo 1632515 1633303 := bstep (se 1 (by rfl) ⟨1224977, by rfl⟩ : syracuseStep 1633303 = 2449955) B2449955
theorem B1633323 : Blo 1632515 1633323 := bstep (se 1 (by rfl) ⟨1224992, by rfl⟩ : syracuseStep 1633323 = 2449985) B2449985
theorem B1633335 : Blo 1632515 1633335 := bstep (se 1 (by rfl) ⟨1225001, by rfl⟩ : syracuseStep 1633335 = 2450003) B2450003
theorem B1633355 : Blo 1632515 1633355 := bstep (se 1 (by rfl) ⟨1225016, by rfl⟩ : syracuseStep 1633355 = 2450033) B2450033
theorem B1838155 : Blo 1632515 1838155 := bstep (se 1 (by rfl) ⟨1378616, by rfl⟩ : syracuseStep 1838155 = 2757233) B2757233
theorem B1633367 : Blo 1632515 1633367 := bstep (se 1 (by rfl) ⟨1225025, by rfl⟩ : syracuseStep 1633367 = 2450051) B2450051
theorem B1633387 : Blo 1632515 1633387 := bstep (se 1 (by rfl) ⟨1225040, by rfl⟩ : syracuseStep 1633387 = 2450081) B2450081
theorem B1633399 : Blo 1632515 1633399 := bstep (se 1 (by rfl) ⟨1225049, by rfl⟩ : syracuseStep 1633399 = 2450099) B2450099
theorem B1633419 : Blo 1632515 1633419 := bstep (se 1 (by rfl) ⟨1225064, by rfl⟩ : syracuseStep 1633419 = 2450129) B2450129
theorem B7449745 : Blo 1632515 7449745 := bstep (se 2 (by rfl) ⟨2793654, by rfl⟩ : syracuseStep 7449745 = 5587309) B5587309
theorem B3099799 : Blo 1632515 3099799 := bstep (se 1 (by rfl) ⟨2324849, by rfl⟩ : syracuseStep 3099799 = 4649699) B4649699
theorem B1633431 : Blo 1632515 1633431 := bstep (se 1 (by rfl) ⟨1225073, by rfl⟩ : syracuseStep 1633431 = 2450147) B2450147
theorem B3673241 : Blo 1632515 3673241 := bstep (se 2 (by rfl) ⟨1377465, by rfl⟩ : syracuseStep 3673241 = 2754931) B2754931
theorem B1633451 : Blo 1632515 1633451 := bstep (se 1 (by rfl) ⟨1225088, by rfl⟩ : syracuseStep 1633451 = 2450177) B2450177
theorem B1633463 : Blo 1632515 1633463 := bstep (se 1 (by rfl) ⟨1225097, by rfl⟩ : syracuseStep 1633463 = 2450195) B2450195
theorem B1838263 : Blo 1632515 1838263 := bstep (se 1 (by rfl) ⟨1378697, by rfl⟩ : syracuseStep 1838263 = 2757395) B2757395
theorem B1633483 : Blo 1632515 1633483 := bstep (se 1 (by rfl) ⟨1225112, by rfl⟩ : syracuseStep 1633483 = 2450225) B2450225
theorem B1633495 : Blo 1632515 1633495 := bstep (se 1 (by rfl) ⟨1225121, by rfl⟩ : syracuseStep 1633495 = 2450243) B2450243
theorem B1633515 : Blo 1632515 1633515 := bstep (se 1 (by rfl) ⟨1225136, by rfl⟩ : syracuseStep 1633515 = 2450273) B2450273
theorem B3673331 : Blo 1632515 3673331 := bstep (se 1 (by rfl) ⟨2754998, by rfl⟩ : syracuseStep 3673331 = 5509997) B5509997
theorem B1633527 : Blo 1632515 1633527 := bstep (se 1 (by rfl) ⟨1225145, by rfl⟩ : syracuseStep 1633527 = 2450291) B2450291
theorem B1633547 : Blo 1632515 1633547 := bstep (se 1 (by rfl) ⟨1225160, by rfl⟩ : syracuseStep 1633547 = 2450321) B2450321
theorem B3673367 : Blo 1632515 3673367 := bstep (se 1 (by rfl) ⟨2755025, by rfl⟩ : syracuseStep 3673367 = 5510051) B5510051
theorem B1633559 : Blo 1632515 1633559 := bstep (se 1 (by rfl) ⟨1225169, by rfl⟩ : syracuseStep 1633559 = 2450339) B2450339
theorem B12397859 : Blo 1632515 12397859 := bstep (se 1 (by rfl) ⟨9298394, by rfl⟩ : syracuseStep 12397859 = 18596789) B18596789
theorem B1633579 : Blo 1632515 1633579 := bstep (se 1 (by rfl) ⟨1225184, by rfl⟩ : syracuseStep 1633579 = 2450369) B2450369
theorem B56577325 : Blo 1632515 56577325 := bstep (se 3 (by rfl) ⟨10608248, by rfl⟩ : syracuseStep 56577325 = 21216497) B21216497
theorem B1633591 : Blo 1632515 1633591 := bstep (se 1 (by rfl) ⟨1225193, by rfl⟩ : syracuseStep 1633591 = 2450387) B2450387
theorem B1633611 : Blo 1632515 1633611 := bstep (se 1 (by rfl) ⟨1225208, by rfl⟩ : syracuseStep 1633611 = 2450417) B2450417
theorem B1633623 : Blo 1632515 1633623 := bstep (se 1 (by rfl) ⟨1225217, by rfl⟩ : syracuseStep 1633623 = 2450435) B2450435
theorem B4713821 : Blo 1632515 4713821 := bstep (se 3 (by rfl) ⟨883841, by rfl⟩ : syracuseStep 4713821 = 1767683) B1767683
theorem B1633643 : Blo 1632515 1633643 := bstep (se 1 (by rfl) ⟨1225232, by rfl⟩ : syracuseStep 1633643 = 2450465) B2450465
theorem B55184753 : Blo 1632515 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B1633655 : Blo 1632515 1633655 := bstep (se 1 (by rfl) ⟨1225241, by rfl⟩ : syracuseStep 1633655 = 2450483) B2450483
theorem B1633675 : Blo 1632515 1633675 := bstep (se 1 (by rfl) ⟨1225256, by rfl⟩ : syracuseStep 1633675 = 2450513) B2450513
theorem B120860045 : Blo 1632515 120860045 := bstep (se 3 (by rfl) ⟨22661258, by rfl⟩ : syracuseStep 120860045 = 45322517) B45322517
theorem B2755991 : Blo 1632515 2755991 := bstep (se 1 (by rfl) ⟨2066993, by rfl⟩ : syracuseStep 2755991 = 4133987) B4133987
theorem B1633687 : Blo 1632515 1633687 := bstep (se 1 (by rfl) ⟨1225265, by rfl⟩ : syracuseStep 1633687 = 2450531) B2450531
theorem B1633707 : Blo 1632515 1633707 := bstep (se 1 (by rfl) ⟨1225280, by rfl⟩ : syracuseStep 1633707 = 2450561) B2450561
theorem B2944435 : Blo 1632515 2944435 := bstep (se 1 (by rfl) ⟨2208326, by rfl⟩ : syracuseStep 2944435 = 4416653) B4416653
theorem B1633719 : Blo 1632515 1633719 := bstep (se 1 (by rfl) ⟨1225289, by rfl⟩ : syracuseStep 1633719 = 2450579) B2450579
theorem B1961419 : Blo 1632515 1961419 := bstep (se 1 (by rfl) ⟨1471064, by rfl⟩ : syracuseStep 1961419 = 2942129) B2942129
theorem B3673547 : Blo 1632515 3673547 := bstep (se 1 (by rfl) ⟨2755160, by rfl⟩ : syracuseStep 3673547 = 5510321) B5510321
theorem B1633739 : Blo 1632515 1633739 := bstep (se 1 (by rfl) ⟨1225304, by rfl⟩ : syracuseStep 1633739 = 2450609) B2450609
theorem B1633751 : Blo 1632515 1633751 := bstep (se 1 (by rfl) ⟨1225313, by rfl⟩ : syracuseStep 1633751 = 2450627) B2450627
theorem B1633771 : Blo 1632515 1633771 := bstep (se 1 (by rfl) ⟨1225328, by rfl⟩ : syracuseStep 1633771 = 2450657) B2450657
theorem B1633783 : Blo 1632515 1633783 := bstep (se 1 (by rfl) ⟨1225337, by rfl⟩ : syracuseStep 1633783 = 2450675) B2450675
theorem B3673601 : Blo 1632515 3673601 := bstep (se 2 (by rfl) ⟨1377600, by rfl⟩ : syracuseStep 3673601 = 2755201) B2755201
theorem B1633803 : Blo 1632515 1633803 := bstep (se 1 (by rfl) ⟨1225352, by rfl⟩ : syracuseStep 1633803 = 2450705) B2450705
theorem B2756119 : Blo 1632515 2756119 := bstep (se 1 (by rfl) ⟨2067089, by rfl⟩ : syracuseStep 2756119 = 4134179) B4134179
theorem B1633815 : Blo 1632515 1633815 := bstep (se 1 (by rfl) ⟨1225361, by rfl⟩ : syracuseStep 1633815 = 2450723) B2450723
theorem B1633835 : Blo 1632515 1633835 := bstep (se 1 (by rfl) ⟨1225376, by rfl⟩ : syracuseStep 1633835 = 2450753) B2450753
theorem B1633847 : Blo 1632515 1633847 := bstep (se 1 (by rfl) ⟨1225385, by rfl⟩ : syracuseStep 1633847 = 2450771) B2450771
theorem B4132417 : Blo 1632515 4132417 := bstep (se 2 (by rfl) ⟨1549656, by rfl⟩ : syracuseStep 4132417 = 3099313) B3099313
theorem B1633867 : Blo 1632515 1633867 := bstep (se 1 (by rfl) ⟨1225400, by rfl⟩ : syracuseStep 1633867 = 2450801) B2450801
theorem B1633879 : Blo 1632515 1633879 := bstep (se 1 (by rfl) ⟨1225409, by rfl⟩ : syracuseStep 1633879 = 2450819) B2450819
theorem B1633899 : Blo 1632515 1633899 := bstep (se 1 (by rfl) ⟨1225424, by rfl⟩ : syracuseStep 1633899 = 2450849) B2450849
theorem B1633911 : Blo 1632515 1633911 := bstep (se 1 (by rfl) ⟨1225433, by rfl⟩ : syracuseStep 1633911 = 2450867) B2450867
theorem B1633931 : Blo 1632515 1633931 := bstep (se 1 (by rfl) ⟨1225448, by rfl⟩ : syracuseStep 1633931 = 2450897) B2450897
theorem B1633943 : Blo 1632515 1633943 := bstep (se 1 (by rfl) ⟨1225457, by rfl⟩ : syracuseStep 1633943 = 2450915) B2450915
theorem B1633963 : Blo 1632515 1633963 := bstep (se 1 (by rfl) ⟨1225472, by rfl⟩ : syracuseStep 1633963 = 2450945) B2450945
theorem B1633975 : Blo 1632515 1633975 := bstep (se 1 (by rfl) ⟨1225481, by rfl⟩ : syracuseStep 1633975 = 2450963) B2450963
theorem B1633995 : Blo 1632515 1633995 := bstep (se 1 (by rfl) ⟨1225496, by rfl⟩ : syracuseStep 1633995 = 2450993) B2450993
theorem B1634007 : Blo 1632515 1634007 := bstep (se 1 (by rfl) ⟨1225505, by rfl⟩ : syracuseStep 1634007 = 2451011) B2451011
theorem B3673817 : Blo 1632515 3673817 := bstep (se 2 (by rfl) ⟨1377681, by rfl⟩ : syracuseStep 3673817 = 2755363) B2755363
theorem B8269613 : Blo 1632515 8269613 := bstep (se 3 (by rfl) ⟨1550552, by rfl⟩ : syracuseStep 8269613 = 3101105) B3101105
theorem B3673907 : Blo 1632515 3673907 := bstep (se 1 (by rfl) ⟨2755430, by rfl⟩ : syracuseStep 3673907 = 5510861) B5510861
theorem B3673943 : Blo 1632515 3673943 := bstep (se 1 (by rfl) ⟨2755457, by rfl⟩ : syracuseStep 3673943 = 5510915) B5510915
theorem B12570461 : Blo 1632515 12570461 := bstep (se 3 (by rfl) ⟨2356961, by rfl⟩ : syracuseStep 12570461 = 4713923) B4713923
theorem B20926309 : Blo 1632515 20926309 := bstep (se 4 (by rfl) ⟨1961841, by rfl⟩ : syracuseStep 20926309 = 3923683) B3923683
theorem B4714433 : Blo 1632515 4714433 := bstep (se 2 (by rfl) ⟨1767912, by rfl⟩ : syracuseStep 4714433 = 3535825) B3535825
theorem B3100619 : Blo 1632515 3100619 := bstep (se 1 (by rfl) ⟨2325464, by rfl⟩ : syracuseStep 3100619 = 4650929) B4650929
theorem B4968395 : Blo 1632515 4968395 := bstep (se 1 (by rfl) ⟨3726296, by rfl⟩ : syracuseStep 4968395 = 7452593) B7452593
theorem B3100673 : Blo 1632515 3100673 := bstep (se 2 (by rfl) ⟨1162752, by rfl⟩ : syracuseStep 3100673 = 2325505) B2325505
theorem B3674123 : Blo 1632515 3674123 := bstep (se 1 (by rfl) ⟨2755592, by rfl⟩ : syracuseStep 3674123 = 5511185) B5511185
theorem B3674177 : Blo 1632515 3674177 := bstep (se 2 (by rfl) ⟨1377816, by rfl⟩ : syracuseStep 3674177 = 2755633) B2755633
theorem B2756747 : Blo 1632515 2756747 := bstep (se 1 (by rfl) ⟨2067560, by rfl⟩ : syracuseStep 2756747 = 4135121) B4135121
theorem B4133015 : Blo 1632515 4133015 := bstep (se 1 (by rfl) ⟨3099761, by rfl⟩ : syracuseStep 4133015 = 6199523) B6199523
theorem B2756875 : Blo 1632515 2756875 := bstep (se 1 (by rfl) ⟨2067656, by rfl⟩ : syracuseStep 2756875 = 4135313) B4135313
theorem B3674393 : Blo 1632515 3674393 := bstep (se 2 (by rfl) ⟨1377897, by rfl⟩ : syracuseStep 3674393 = 2755795) B2755795
theorem B3674483 : Blo 1632515 3674483 := bstep (se 1 (by rfl) ⟨2755862, by rfl⟩ : syracuseStep 3674483 = 5511725) B5511725
theorem B3674519 : Blo 1632515 3674519 := bstep (se 1 (by rfl) ⟨2755889, by rfl⟩ : syracuseStep 3674519 = 5511779) B5511779
theorem B2757017 : Blo 1632515 2757017 := bstep (se 2 (by rfl) ⟨1033881, by rfl⟩ : syracuseStep 2757017 = 2067763) B2067763
theorem B2757145 : Blo 1632515 2757145 := bstep (se 2 (by rfl) ⟨1033929, by rfl⟩ : syracuseStep 2757145 = 2067859) B2067859
theorem B3674699 : Blo 1632515 3674699 := bstep (se 1 (by rfl) ⟨2756024, by rfl⟩ : syracuseStep 3674699 = 5512049) B5512049
theorem B3674753 : Blo 1632515 3674753 := bstep (se 2 (by rfl) ⟨1378032, by rfl⟩ : syracuseStep 3674753 = 2756065) B2756065
theorem B5231297 : Blo 1632515 5231297 := bstep (se 2 (by rfl) ⟨1961736, by rfl⟩ : syracuseStep 5231297 = 3923473) B3923473
theorem B5509835 : Blo 1632515 5509835 := bstep (se 1 (by rfl) ⟨4132376, by rfl⟩ : syracuseStep 5509835 = 8264753) B8264753
theorem B5231425 : Blo 1632515 5231425 := bstep (se 2 (by rfl) ⟨1961784, by rfl⟩ : syracuseStep 5231425 = 3923569) B3923569
theorem B3674969 : Blo 1632515 3674969 := bstep (se 2 (by rfl) ⟨1378113, by rfl⟩ : syracuseStep 3674969 = 2756227) B2756227
theorem B3101591 : Blo 1632515 3101591 := bstep (se 1 (by rfl) ⟨2326193, by rfl⟩ : syracuseStep 3101591 = 4652387) B4652387
theorem B3675059 : Blo 1632515 3675059 := bstep (se 1 (by rfl) ⟨2756294, by rfl⟩ : syracuseStep 3675059 = 5512589) B5512589
theorem B4133825 : Blo 1632515 4133825 := bstep (se 2 (by rfl) ⟨1550184, by rfl⟩ : syracuseStep 4133825 = 3100369) B3100369
theorem B3675095 : Blo 1632515 3675095 := bstep (se 1 (by rfl) ⟨2756321, by rfl⟩ : syracuseStep 3675095 = 5512643) B5512643
theorem B1962967 : Blo 1632515 1962967 := bstep (se 1 (by rfl) ⟨1472225, by rfl⟩ : syracuseStep 1962967 = 2944451) B2944451
theorem B5510105 : Blo 1632515 5510105 := bstep (se 2 (by rfl) ⟨2066289, by rfl⟩ : syracuseStep 5510105 = 4132579) B4132579
theorem B3724289 : Blo 1632515 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B4650007 : Blo 1632515 4650007 := bstep (se 1 (by rfl) ⟨3487505, by rfl⟩ : syracuseStep 4650007 = 6975011) B6975011
theorem B5231681 : Blo 1632515 5231681 := bstep (se 2 (by rfl) ⟨1961880, by rfl⟩ : syracuseStep 5231681 = 3923761) B3923761
theorem B9303133 : Blo 1632515 9303133 := bstep (se 3 (by rfl) ⟨1744337, by rfl⟩ : syracuseStep 9303133 = 3488675) B3488675
theorem B10466435 : Blo 1632515 10466435 := bstep (se 1 (by rfl) ⟨7849826, by rfl⟩ : syracuseStep 10466435 = 15699653) B15699653
theorem B3724427 : Blo 1632515 3724427 := bstep (se 1 (by rfl) ⟨2793320, by rfl⟩ : syracuseStep 3724427 = 5586641) B5586641
theorem B3675275 : Blo 1632515 3675275 := bstep (se 1 (by rfl) ⟨2756456, by rfl⟩ : syracuseStep 3675275 = 5512913) B5512913
theorem B3675329 : Blo 1632515 3675329 := bstep (se 2 (by rfl) ⟨1378248, by rfl⟩ : syracuseStep 3675329 = 2756497) B2756497
theorem B6198551 : Blo 1632515 6198551 := bstep (se 1 (by rfl) ⟨4648913, by rfl⟩ : syracuseStep 6198551 = 9297827) B9297827
theorem B3675545 : Blo 1632515 3675545 := bstep (se 2 (by rfl) ⟨1378329, by rfl⟩ : syracuseStep 3675545 = 2756659) B2756659
theorem B4134361 : Blo 1632515 4134361 := bstep (se 2 (by rfl) ⟨1550385, by rfl⟩ : syracuseStep 4134361 = 3100771) B3100771
theorem B5305817 : Blo 1632515 5305817 := bstep (se 2 (by rfl) ⟨1989681, by rfl⟩ : syracuseStep 5305817 = 3979363) B3979363
theorem B3675635 : Blo 1632515 3675635 := bstep (se 1 (by rfl) ⟨2756726, by rfl⟩ : syracuseStep 3675635 = 5513453) B5513453
theorem B3675671 : Blo 1632515 3675671 := bstep (se 1 (by rfl) ⟨2756753, by rfl⟩ : syracuseStep 3675671 = 5513507) B5513507
theorem B9557597 : Blo 1632515 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B5510807 : Blo 1632515 5510807 := bstep (se 1 (by rfl) ⟨4133105, by rfl⟩ : syracuseStep 5510807 = 8266211) B8266211
theorem B3487411 : Blo 1632515 3487411 := bstep (se 1 (by rfl) ⟨2615558, by rfl⟩ : syracuseStep 3487411 = 5231117) B5231117
theorem B3675851 : Blo 1632515 3675851 := bstep (se 1 (by rfl) ⟨2756888, by rfl⟩ : syracuseStep 3675851 = 5513777) B5513777
theorem B3675905 : Blo 1632515 3675905 := bstep (se 2 (by rfl) ⟨1378464, by rfl⟩ : syracuseStep 3675905 = 2756929) B2756929
theorem B8828851 : Blo 1632515 8828851 := bstep (se 1 (by rfl) ⟨6621638, by rfl⟩ : syracuseStep 8828851 = 13243277) B13243277
theorem B3356633 : Blo 1632515 3356633 := bstep (se 2 (by rfl) ⟨1258737, by rfl⟩ : syracuseStep 3356633 = 2517475) B2517475
theorem B3676121 : Blo 1632515 3676121 := bstep (se 2 (by rfl) ⟨1378545, by rfl⟩ : syracuseStep 3676121 = 2757091) B2757091
theorem B3676211 : Blo 1632515 3676211 := bstep (se 1 (by rfl) ⟨2757158, by rfl⟩ : syracuseStep 3676211 = 5514317) B5514317
theorem B3676247 : Blo 1632515 3676247 := bstep (se 1 (by rfl) ⟨2757185, by rfl⟩ : syracuseStep 3676247 = 5514371) B5514371
theorem B3487873 : Blo 1632515 3487873 := bstep (se 2 (by rfl) ⟨1307952, by rfl⟩ : syracuseStep 3487873 = 2615905) B2615905
theorem B5511347 : Blo 1632515 5511347 := bstep (se 1 (by rfl) ⟨4133510, by rfl⟩ : syracuseStep 5511347 = 8267021) B8267021
theorem B2324747 : Blo 1632515 2324747 := bstep (se 1 (by rfl) ⟨1743560, by rfl⟩ : syracuseStep 2324747 = 3487121) B3487121
theorem B3676427 : Blo 1632515 3676427 := bstep (se 1 (by rfl) ⟨2757320, by rfl⟩ : syracuseStep 3676427 = 5514641) B5514641
theorem B3676481 : Blo 1632515 3676481 := bstep (se 2 (by rfl) ⟨1378680, by rfl⟩ : syracuseStep 3676481 = 2757361) B2757361
theorem B4651339 : Blo 1632515 4651339 := bstep (se 1 (by rfl) ⟨3488504, by rfl⟩ : syracuseStep 4651339 = 6977009) B6977009
theorem B14145893 : Blo 1632515 14145893 := bstep (se 4 (by rfl) ⟨1326177, by rfl⟩ : syracuseStep 14145893 = 2652355) B2652355
theorem B28285361 : Blo 1632515 28285361 := bstep (se 2 (by rfl) ⟨10607010, by rfl⟩ : syracuseStep 28285361 = 21214021) B21214021
theorem B5511617 : Blo 1632515 5511617 := bstep (se 2 (by rfl) ⟨2066856, by rfl⟩ : syracuseStep 5511617 = 4133713) B4133713
theorem B6199811 : Blo 1632515 6199811 := bstep (se 1 (by rfl) ⟨4649858, by rfl⟩ : syracuseStep 6199811 = 9299717) B9299717
theorem B4135475 : Blo 1632515 4135475 := bstep (se 1 (by rfl) ⟨3101606, by rfl⟩ : syracuseStep 4135475 = 6203213) B6203213
theorem B4651613 : Blo 1632515 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B5233373 : Blo 1632515 5233373 := bstep (se 3 (by rfl) ⟨981257, by rfl⟩ : syracuseStep 5233373 = 1962515) B1962515
theorem B6978307 : Blo 1632515 6978307 := bstep (se 1 (by rfl) ⟨5233730, by rfl⟩ : syracuseStep 6978307 = 10467461) B10467461
theorem B3488599 : Blo 1632515 3488599 := bstep (se 1 (by rfl) ⟨2616449, by rfl⟩ : syracuseStep 3488599 = 5232899) B5232899
theorem B4135769 : Blo 1632515 4135769 := bstep (se 2 (by rfl) ⟨1550913, by rfl⟩ : syracuseStep 4135769 = 3101827) B3101827
theorem B5888857 : Blo 1632515 5888857 := bstep (se 2 (by rfl) ⟨2208321, by rfl⟩ : syracuseStep 5888857 = 4416643) B4416643
theorem B4651955 : Blo 1632515 4651955 := bstep (se 1 (by rfl) ⟨3488966, by rfl⟩ : syracuseStep 4651955 = 6977933) B6977933
theorem B5512157 : Blo 1632515 5512157 := bstep (se 3 (by rfl) ⟨1033529, by rfl⟩ : syracuseStep 5512157 = 2067059) B2067059
theorem B12573731 : Blo 1632515 12573731 := bstep (se 1 (by rfl) ⟨9430298, by rfl⟩ : syracuseStep 12573731 = 18860597) B18860597
theorem B6978649 : Blo 1632515 6978649 := bstep (se 2 (by rfl) ⟨2616993, by rfl⟩ : syracuseStep 6978649 = 5233987) B5233987
theorem B13950053 : Blo 1632515 13950053 := bstep (se 4 (by rfl) ⟨1307817, by rfl⟩ : syracuseStep 13950053 = 2615635) B2615635
theorem B1743979 : Blo 1632515 1743979 := bstep (se 1 (by rfl) ⟨1307984, by rfl⟩ : syracuseStep 1743979 = 2615969) B2615969
theorem B10460339 : Blo 1632515 10460339 := bstep (se 1 (by rfl) ⟨7845254, by rfl⟩ : syracuseStep 10460339 = 15690509) B15690509
theorem B7552273 : Blo 1632515 7552273 := bstep (se 2 (by rfl) ⟨2832102, by rfl⟩ : syracuseStep 7552273 = 5664205) B5664205
theorem B3186049 : Blo 1632515 3186049 := bstep (se 2 (by rfl) ⟨1194768, by rfl⟩ : syracuseStep 3186049 = 2389537) B2389537
theorem B2448779 : Blo 1632515 2448779 := bstep (se 1 (by rfl) ⟨1836584, by rfl⟩ : syracuseStep 2448779 = 3673169) B3673169
theorem B2448791 : Blo 1632515 2448791 := bstep (se 1 (by rfl) ⟨1836593, by rfl⟩ : syracuseStep 2448791 = 3673187) B3673187
theorem B13245875 : Blo 1632515 13245875 := bstep (se 1 (by rfl) ⟨9934406, by rfl⟩ : syracuseStep 13245875 = 19868813) B19868813
theorem B4414913 : Blo 1632515 4414913 := bstep (se 2 (by rfl) ⟨1655592, by rfl⟩ : syracuseStep 4414913 = 3311185) B3311185
theorem B2448857 : Blo 1632515 2448857 := bstep (se 2 (by rfl) ⟨918321, by rfl⟩ : syracuseStep 2448857 = 1836643) B1836643
theorem B25476569 : Blo 1632515 25476569 := bstep (se 2 (by rfl) ⟨9553713, by rfl⟩ : syracuseStep 25476569 = 19107427) B19107427
theorem B5234141 : Blo 1632515 5234141 := bstep (se 3 (by rfl) ⟨981401, by rfl⟩ : syracuseStep 5234141 = 1962803) B1962803
theorem B2448971 : Blo 1632515 2448971 := bstep (se 1 (by rfl) ⟨1836728, by rfl⟩ : syracuseStep 2448971 = 3673457) B3673457
theorem B2448983 : Blo 1632515 2448983 := bstep (se 1 (by rfl) ⟨1836737, by rfl⟩ : syracuseStep 2448983 = 3673475) B3673475
theorem B2793047 : Blo 1632515 2793047 := bstep (se 1 (by rfl) ⟨2094785, by rfl⟩ : syracuseStep 2793047 = 4189571) B4189571
theorem B48381533 : Blo 1632515 48381533 := bstep (se 3 (by rfl) ⟨9071537, by rfl⟩ : syracuseStep 48381533 = 18143075) B18143075
theorem B3489419 : Blo 1632515 3489419 := bstep (se 1 (by rfl) ⟨2617064, by rfl⟩ : syracuseStep 3489419 = 5234129) B5234129
theorem B2449049 : Blo 1632515 2449049 := bstep (se 2 (by rfl) ⟨918393, by rfl⟩ : syracuseStep 2449049 = 1836787) B1836787
theorem B2449163 : Blo 1632515 2449163 := bstep (se 1 (by rfl) ⟨1836872, by rfl⟩ : syracuseStep 2449163 = 3673745) B3673745
theorem B13950737 : Blo 1632515 13950737 := bstep (se 2 (by rfl) ⟨5231526, by rfl⟩ : syracuseStep 13950737 = 10463053) B10463053
theorem B2449175 : Blo 1632515 2449175 := bstep (se 1 (by rfl) ⟨1836881, by rfl⟩ : syracuseStep 2449175 = 3673763) B3673763
theorem B8953645 : Blo 1632515 8953645 := bstep (se 3 (by rfl) ⟨1678808, by rfl⟩ : syracuseStep 8953645 = 3357617) B3357617
theorem B2449241 : Blo 1632515 2449241 := bstep (se 2 (by rfl) ⟨918465, by rfl⟩ : syracuseStep 2449241 = 1836931) B1836931
theorem B14147459 : Blo 1632515 14147459 := bstep (se 1 (by rfl) ⟨10610594, by rfl⟩ : syracuseStep 14147459 = 21221189) B21221189
theorem B2449355 : Blo 1632515 2449355 := bstep (se 1 (by rfl) ⟨1837016, by rfl⟩ : syracuseStep 2449355 = 3674033) B3674033
theorem B2449367 : Blo 1632515 2449367 := bstep (se 1 (by rfl) ⟨1837025, by rfl⟩ : syracuseStep 2449367 = 3674051) B3674051
theorem B5234653 : Blo 1632515 5234653 := bstep (se 3 (by rfl) ⟨981497, by rfl⟩ : syracuseStep 5234653 = 1962995) B1962995
theorem B2449415 : Blo 1632515 2449415 := bstep (se 1 (by rfl) ⟨1837061, by rfl⟩ : syracuseStep 2449415 = 3674123) B3674123
theorem B4653071 : Blo 1632515 4653071 := bstep (se 1 (by rfl) ⟨3489803, by rfl⟩ : syracuseStep 4653071 = 6979607) B6979607
theorem B2449451 : Blo 1632515 2449451 := bstep (se 1 (by rfl) ⟨1837088, by rfl⟩ : syracuseStep 2449451 = 3674177) B3674177
theorem B2449481 : Blo 1632515 2449481 := bstep (se 2 (by rfl) ⟨918555, by rfl⟩ : syracuseStep 2449481 = 1837111) B1837111
theorem B2449595 : Blo 1632515 2449595 := bstep (se 1 (by rfl) ⟨1837196, by rfl⟩ : syracuseStep 2449595 = 3674393) B3674393
theorem B2449655 : Blo 1632515 2449655 := bstep (se 1 (by rfl) ⟨1837241, by rfl⟩ : syracuseStep 2449655 = 3674483) B3674483
theorem B2449679 : Blo 1632515 2449679 := bstep (se 1 (by rfl) ⟨1837259, by rfl⟩ : syracuseStep 2449679 = 3674519) B3674519
theorem B2449721 : Blo 1632515 2449721 := bstep (se 2 (by rfl) ⟨918645, by rfl⟩ : syracuseStep 2449721 = 1837291) B1837291
theorem B27910493 : Blo 1632515 27910493 := bstep (se 3 (by rfl) ⟨5233217, by rfl⟩ : syracuseStep 27910493 = 10466435) B10466435
theorem B2449799 : Blo 1632515 2449799 := bstep (se 1 (by rfl) ⟨1837349, by rfl⟩ : syracuseStep 2449799 = 3674699) B3674699
theorem B2449835 : Blo 1632515 2449835 := bstep (se 1 (by rfl) ⟨1837376, by rfl⟩ : syracuseStep 2449835 = 3674753) B3674753
theorem B6201785 : Blo 1632515 6201785 := bstep (se 2 (by rfl) ⟨2325669, by rfl⟩ : syracuseStep 6201785 = 4651339) B4651339
theorem B2449865 : Blo 1632515 2449865 := bstep (se 2 (by rfl) ⟨918699, by rfl⟩ : syracuseStep 2449865 = 1837399) B1837399
theorem B2449979 : Blo 1632515 2449979 := bstep (se 1 (by rfl) ⟨1837484, by rfl⟩ : syracuseStep 2449979 = 3674969) B3674969
theorem B2450039 : Blo 1632515 2450039 := bstep (se 1 (by rfl) ⟨1837529, by rfl⟩ : syracuseStep 2450039 = 3675059) B3675059
theorem B2450063 : Blo 1632515 2450063 := bstep (se 1 (by rfl) ⟨1837547, by rfl⟩ : syracuseStep 2450063 = 3675095) B3675095
theorem B2482859 : Blo 1632515 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B2450105 : Blo 1632515 2450105 := bstep (se 2 (by rfl) ⟨918789, by rfl⟩ : syracuseStep 2450105 = 1837579) B1837579
theorem B4842185 : Blo 1632515 4842185 := bstep (se 2 (by rfl) ⟨1815819, by rfl⟩ : syracuseStep 4842185 = 3631639) B3631639
theorem B2450183 : Blo 1632515 2450183 := bstep (se 1 (by rfl) ⟨1837637, by rfl⟩ : syracuseStep 2450183 = 3675275) B3675275
theorem B2450219 : Blo 1632515 2450219 := bstep (se 1 (by rfl) ⟨1837664, by rfl⟩ : syracuseStep 2450219 = 3675329) B3675329
theorem B2450249 : Blo 1632515 2450249 := bstep (se 2 (by rfl) ⟨918843, by rfl⟩ : syracuseStep 2450249 = 1837687) B1837687
theorem B2450363 : Blo 1632515 2450363 := bstep (se 1 (by rfl) ⟨1837772, by rfl⟩ : syracuseStep 2450363 = 3675545) B3675545
theorem B2450423 : Blo 1632515 2450423 := bstep (se 1 (by rfl) ⟨1837817, by rfl⟩ : syracuseStep 2450423 = 3675635) B3675635
theorem B2450447 : Blo 1632515 2450447 := bstep (se 1 (by rfl) ⟨1837835, by rfl⟩ : syracuseStep 2450447 = 3675671) B3675671
theorem B2450489 : Blo 1632515 2450489 := bstep (se 2 (by rfl) ⟨918933, by rfl⟩ : syracuseStep 2450489 = 1837867) B1837867
theorem B2450567 : Blo 1632515 2450567 := bstep (se 1 (by rfl) ⟨1837925, by rfl⟩ : syracuseStep 2450567 = 3675851) B3675851
theorem B39724181 : Blo 1632515 39724181 := bstep (se 6 (by rfl) ⟨931035, by rfl⟩ : syracuseStep 39724181 = 1862071) B1862071
theorem B2450603 : Blo 1632515 2450603 := bstep (se 1 (by rfl) ⟨1837952, by rfl⟩ : syracuseStep 2450603 = 3675905) B3675905
theorem B2450633 : Blo 1632515 2450633 := bstep (se 2 (by rfl) ⟨918987, by rfl⟩ : syracuseStep 2450633 = 1837975) B1837975
theorem B2237755 : Blo 1632515 2237755 := bstep (se 1 (by rfl) ⟨1678316, by rfl⟩ : syracuseStep 2237755 = 3356633) B3356633
theorem B2450747 : Blo 1632515 2450747 := bstep (se 1 (by rfl) ⟨1838060, by rfl⟩ : syracuseStep 2450747 = 3676121) B3676121
theorem B95438197 : Blo 1632515 95438197 := bstep (se 5 (by rfl) ⟨4473665, by rfl⟩ : syracuseStep 95438197 = 8947331) B8947331
theorem B2450807 : Blo 1632515 2450807 := bstep (se 1 (by rfl) ⟨1838105, by rfl⟩ : syracuseStep 2450807 = 3676211) B3676211
theorem B2450831 : Blo 1632515 2450831 := bstep (se 1 (by rfl) ⟨1838123, by rfl⟩ : syracuseStep 2450831 = 3676247) B3676247
theorem B2450873 : Blo 1632515 2450873 := bstep (se 2 (by rfl) ⟨919077, by rfl⟩ : syracuseStep 2450873 = 1838155) B1838155
theorem B12404177 : Blo 1632515 12404177 := bstep (se 2 (by rfl) ⟨4651566, by rfl⟩ : syracuseStep 12404177 = 9303133) B9303133
theorem B2450951 : Blo 1632515 2450951 := bstep (se 1 (by rfl) ⟨1838213, by rfl⟩ : syracuseStep 2450951 = 3676427) B3676427
theorem B2450987 : Blo 1632515 2450987 := bstep (se 1 (by rfl) ⟨1838240, by rfl⟩ : syracuseStep 2450987 = 3676481) B3676481
theorem B7448125 : Blo 1632515 7448125 := bstep (se 3 (by rfl) ⟨1396523, by rfl⟩ : syracuseStep 7448125 = 2793047) B2793047
theorem B9430595 : Blo 1632515 9430595 := bstep (se 1 (by rfl) ⟨7072946, by rfl⟩ : syracuseStep 9430595 = 14145893) B14145893
theorem B2451017 : Blo 1632515 2451017 := bstep (se 2 (by rfl) ⟨919131, by rfl⟩ : syracuseStep 2451017 = 1838263) B1838263
theorem B1836679 : Blo 1632515 1836679 := bstep (se 1 (by rfl) ⟨1377509, by rfl⟩ : syracuseStep 1836679 = 2755019) B2755019
theorem B10069697 : Blo 1632515 10069697 := bstep (se 2 (by rfl) ⟨3776136, by rfl⟩ : syracuseStep 10069697 = 7552273) B7552273
theorem B1836859 : Blo 1632515 1836859 := bstep (se 1 (by rfl) ⟨1377644, by rfl⟩ : syracuseStep 1836859 = 2755289) B2755289
theorem B3925913 : Blo 1632515 3925913 := bstep (se 2 (by rfl) ⟨1472217, by rfl⟩ : syracuseStep 3925913 = 2944435) B2944435
theorem B2615225 : Blo 1632515 2615225 := bstep (se 2 (by rfl) ⟨980709, by rfl⟩ : syracuseStep 2615225 = 1961419) B1961419
theorem B8382487 : Blo 1632515 8382487 := bstep (se 1 (by rfl) ⟨6286865, by rfl⟩ : syracuseStep 8382487 = 12573731) B12573731
theorem B14903357 : Blo 1632515 14903357 := bstep (se 3 (by rfl) ⟨2794379, by rfl⟩ : syracuseStep 14903357 = 5588759) B5588759
theorem B9300035 : Blo 1632515 9300035 := bstep (se 1 (by rfl) ⟨6975026, by rfl⟩ : syracuseStep 9300035 = 13950053) B13950053
theorem B6973559 : Blo 1632515 6973559 := bstep (se 1 (by rfl) ⟨5230169, by rfl⟩ : syracuseStep 6973559 = 10460339) B10460339
theorem B1632519 : Blo 1632515 1632519 := bstep (se 1 (by rfl) ⟨1224389, by rfl⟩ : syracuseStep 1632519 = 2448779) B2448779
theorem B1632527 : Blo 1632515 1632527 := bstep (se 1 (by rfl) ⟨1224395, by rfl⟩ : syracuseStep 1632527 = 2448791) B2448791
theorem B1837327 : Blo 1632515 1837327 := bstep (se 1 (by rfl) ⟨1377995, by rfl⟩ : syracuseStep 1837327 = 2755991) B2755991
theorem B2943275 : Blo 1632515 2943275 := bstep (se 1 (by rfl) ⟨2207456, by rfl⟩ : syracuseStep 2943275 = 4414913) B4414913
theorem B1632571 : Blo 1632515 1632571 := bstep (se 1 (by rfl) ⟨1224428, by rfl⟩ : syracuseStep 1632571 = 2448857) B2448857
theorem B16984379 : Blo 1632515 16984379 := bstep (se 1 (by rfl) ⟨12738284, by rfl⟩ : syracuseStep 16984379 = 25476569) B25476569
theorem B1632647 : Blo 1632515 1632647 := bstep (se 1 (by rfl) ⟨1224485, by rfl⟩ : syracuseStep 1632647 = 2448971) B2448971
theorem B1632655 : Blo 1632515 1632655 := bstep (se 1 (by rfl) ⟨1224491, by rfl⟩ : syracuseStep 1632655 = 2448983) B2448983
theorem B11938193 : Blo 1632515 11938193 := bstep (se 2 (by rfl) ⟨4476822, by rfl⟩ : syracuseStep 11938193 = 8953645) B8953645
theorem B32254355 : Blo 1632515 32254355 := bstep (se 1 (by rfl) ⟨24190766, by rfl⟩ : syracuseStep 32254355 = 48381533) B48381533
theorem B1632699 : Blo 1632515 1632699 := bstep (se 1 (by rfl) ⟨1224524, by rfl⟩ : syracuseStep 1632699 = 2449049) B2449049
theorem B1632775 : Blo 1632515 1632775 := bstep (se 1 (by rfl) ⟨1224581, by rfl⟩ : syracuseStep 1632775 = 2449163) B2449163
theorem B9300491 : Blo 1632515 9300491 := bstep (se 1 (by rfl) ⟨6975368, by rfl⟩ : syracuseStep 9300491 = 13950737) B13950737
theorem B1632783 : Blo 1632515 1632783 := bstep (se 1 (by rfl) ⟨1224587, by rfl⟩ : syracuseStep 1632783 = 2449175) B2449175
theorem B8268317 : Blo 1632515 8268317 := bstep (se 3 (by rfl) ⟨1550309, by rfl⟩ : syracuseStep 8268317 = 3100619) B3100619
theorem B1632827 : Blo 1632515 1632827 := bstep (se 1 (by rfl) ⟨1224620, by rfl⟩ : syracuseStep 1632827 = 2449241) B2449241
theorem B9431639 : Blo 1632515 9431639 := bstep (se 1 (by rfl) ⟨7073729, by rfl⟩ : syracuseStep 9431639 = 14147459) B14147459
theorem B1632903 : Blo 1632515 1632903 := bstep (se 1 (by rfl) ⟨1224677, by rfl⟩ : syracuseStep 1632903 = 2449355) B2449355
theorem B3312263 : Blo 1632515 3312263 := bstep (se 1 (by rfl) ⟨2484197, by rfl⟩ : syracuseStep 3312263 = 4968395) B4968395
theorem B1632911 : Blo 1632515 1632911 := bstep (se 1 (by rfl) ⟨1224683, by rfl⟩ : syracuseStep 1632911 = 2449367) B2449367
theorem B2067115 : Blo 1632515 2067115 := bstep (se 1 (by rfl) ⟨1550336, by rfl⟩ : syracuseStep 2067115 = 3100673) B3100673
theorem B1632955 : Blo 1632515 1632955 := bstep (se 1 (by rfl) ⟨1224716, by rfl⟩ : syracuseStep 1632955 = 2449433) B2449433
theorem B1633031 : Blo 1632515 1633031 := bstep (se 1 (by rfl) ⟨1224773, by rfl⟩ : syracuseStep 1633031 = 2449547) B2449547
theorem B1837831 : Blo 1632515 1837831 := bstep (se 1 (by rfl) ⟨1378373, by rfl⟩ : syracuseStep 1837831 = 2756747) B2756747
theorem B2755343 : Blo 1632515 2755343 := bstep (se 1 (by rfl) ⟨2066507, by rfl⟩ : syracuseStep 2755343 = 4133015) B4133015
theorem B1633039 : Blo 1632515 1633039 := bstep (se 1 (by rfl) ⟨1224779, by rfl⟩ : syracuseStep 1633039 = 2449559) B2449559
theorem B1633083 : Blo 1632515 1633083 := bstep (se 1 (by rfl) ⟨1224812, by rfl⟩ : syracuseStep 1633083 = 2449625) B2449625
theorem B1633159 : Blo 1632515 1633159 := bstep (se 1 (by rfl) ⟨1224869, by rfl⟩ : syracuseStep 1633159 = 2449739) B2449739
theorem B1633167 : Blo 1632515 1633167 := bstep (se 1 (by rfl) ⟨1224875, by rfl⟩ : syracuseStep 1633167 = 2449751) B2449751
theorem B81636245 : Blo 1632515 81636245 := bstep (se 6 (by rfl) ⟨1913349, by rfl⟩ : syracuseStep 81636245 = 3826699) B3826699
theorem B20130713 : Blo 1632515 20130713 := bstep (se 2 (by rfl) ⟨7549017, by rfl⟩ : syracuseStep 20130713 = 15098035) B15098035
theorem B1633211 : Blo 1632515 1633211 := bstep (se 1 (by rfl) ⟨1224908, by rfl⟩ : syracuseStep 1633211 = 2449817) B2449817
theorem B1838011 : Blo 1632515 1838011 := bstep (se 1 (by rfl) ⟨1378508, by rfl⟩ : syracuseStep 1838011 = 2757017) B2757017
theorem B8268803 : Blo 1632515 8268803 := bstep (se 1 (by rfl) ⟨6201602, by rfl⟩ : syracuseStep 8268803 = 12403205) B12403205
theorem B1633287 : Blo 1632515 1633287 := bstep (se 1 (by rfl) ⟨1224965, by rfl⟩ : syracuseStep 1633287 = 2449931) B2449931
theorem B8825867 : Blo 1632515 8825867 := bstep (se 1 (by rfl) ⟨6619400, by rfl⟩ : syracuseStep 8825867 = 13238801) B13238801
theorem B1633295 : Blo 1632515 1633295 := bstep (se 1 (by rfl) ⟨1224971, by rfl⟩ : syracuseStep 1633295 = 2449943) B2449943
theorem B9931805 : Blo 1632515 9931805 := bstep (se 3 (by rfl) ⟨1862213, by rfl⟩ : syracuseStep 9931805 = 3724427) B3724427
theorem B1633339 : Blo 1632515 1633339 := bstep (se 1 (by rfl) ⟨1225004, by rfl⟩ : syracuseStep 1633339 = 2450009) B2450009
theorem B3673223 : Blo 1632515 3673223 := bstep (se 1 (by rfl) ⟨2754917, by rfl⟩ : syracuseStep 3673223 = 5509835) B5509835
theorem B1633415 : Blo 1632515 1633415 := bstep (se 1 (by rfl) ⟨1225061, by rfl⟩ : syracuseStep 1633415 = 2450123) B2450123
theorem B1633423 : Blo 1632515 1633423 := bstep (se 1 (by rfl) ⟨1225067, by rfl⟩ : syracuseStep 1633423 = 2450135) B2450135
theorem B1633467 : Blo 1632515 1633467 := bstep (se 1 (by rfl) ⟨1225100, by rfl⟩ : syracuseStep 1633467 = 2450201) B2450201
theorem B1633543 : Blo 1632515 1633543 := bstep (se 1 (by rfl) ⟨1225157, by rfl⟩ : syracuseStep 1633543 = 2450315) B2450315
theorem B1633551 : Blo 1632515 1633551 := bstep (se 1 (by rfl) ⟨1225163, by rfl⟩ : syracuseStep 1633551 = 2450327) B2450327
theorem B2755883 : Blo 1632515 2755883 := bstep (se 1 (by rfl) ⟨2066912, by rfl⟩ : syracuseStep 2755883 = 4133825) B4133825
theorem B3673403 : Blo 1632515 3673403 := bstep (se 1 (by rfl) ⟨2755052, by rfl⟩ : syracuseStep 3673403 = 5510105) B5510105
theorem B1633595 : Blo 1632515 1633595 := bstep (se 1 (by rfl) ⟨1225196, by rfl⟩ : syracuseStep 1633595 = 2450393) B2450393
theorem B1633671 : Blo 1632515 1633671 := bstep (se 1 (by rfl) ⟨1225253, by rfl⟩ : syracuseStep 1633671 = 2450507) B2450507
theorem B1633679 : Blo 1632515 1633679 := bstep (se 1 (by rfl) ⟨1225259, by rfl⟩ : syracuseStep 1633679 = 2450519) B2450519
theorem B3673529 : Blo 1632515 3673529 := bstep (se 2 (by rfl) ⟨1377573, by rfl⟩ : syracuseStep 3673529 = 2755147) B2755147
theorem B1633723 : Blo 1632515 1633723 := bstep (se 1 (by rfl) ⟨1225292, by rfl⟩ : syracuseStep 1633723 = 2450585) B2450585
theorem B1633799 : Blo 1632515 1633799 := bstep (se 1 (by rfl) ⟨1225349, by rfl⟩ : syracuseStep 1633799 = 2450699) B2450699
theorem B4132367 : Blo 1632515 4132367 := bstep (se 1 (by rfl) ⟨3099275, by rfl⟩ : syracuseStep 4132367 = 6198551) B6198551
theorem B1633807 : Blo 1632515 1633807 := bstep (se 1 (by rfl) ⟨1225355, by rfl⟩ : syracuseStep 1633807 = 2450711) B2450711
theorem B1961515 : Blo 1632515 1961515 := bstep (se 1 (by rfl) ⟨1471136, by rfl⟩ : syracuseStep 1961515 = 2942273) B2942273
theorem B1633851 : Blo 1632515 1633851 := bstep (se 1 (by rfl) ⟨1225388, by rfl⟩ : syracuseStep 1633851 = 2450777) B2450777
theorem B1633927 : Blo 1632515 1633927 := bstep (se 1 (by rfl) ⟨1225445, by rfl⟩ : syracuseStep 1633927 = 2450891) B2450891
theorem B1633935 : Blo 1632515 1633935 := bstep (se 1 (by rfl) ⟨1225451, by rfl⟩ : syracuseStep 1633935 = 2450903) B2450903
theorem B2756281 : Blo 1632515 2756281 := bstep (se 2 (by rfl) ⟨1033605, by rfl⟩ : syracuseStep 2756281 = 2067211) B2067211
theorem B1633979 : Blo 1632515 1633979 := bstep (se 1 (by rfl) ⟨1225484, by rfl⟩ : syracuseStep 1633979 = 2450969) B2450969
theorem B6975233 : Blo 1632515 6975233 := bstep (se 2 (by rfl) ⟨2615712, by rfl⟩ : syracuseStep 6975233 = 5231425) B5231425
theorem B3673871 : Blo 1632515 3673871 := bstep (se 1 (by rfl) ⟨2755403, by rfl⟩ : syracuseStep 3673871 = 5510807) B5510807
theorem B3673889 : Blo 1632515 3673889 := bstep (se 2 (by rfl) ⟨1377708, by rfl⟩ : syracuseStep 3673889 = 2755417) B2755417
theorem B7851809 : Blo 1632515 7851809 := bstep (se 2 (by rfl) ⟨2944428, by rfl⟩ : syracuseStep 7851809 = 5888857) B5888857
theorem B2617289 : Blo 1632515 2617289 := bstep (se 2 (by rfl) ⟨981483, by rfl⟩ : syracuseStep 2617289 = 1962967) B1962967
theorem B3674231 : Blo 1632515 3674231 := bstep (se 1 (by rfl) ⟨2755673, by rfl⟩ : syracuseStep 3674231 = 5511347) B5511347
theorem B9932993 : Blo 1632515 9932993 := bstep (se 2 (by rfl) ⟨3724872, by rfl⟩ : syracuseStep 9932993 = 7449745) B7449745
theorem B4133065 : Blo 1632515 4133065 := bstep (se 2 (by rfl) ⟨1549899, by rfl⟩ : syracuseStep 4133065 = 3099799) B3099799
theorem B3674411 : Blo 1632515 3674411 := bstep (se 1 (by rfl) ⟨2755808, by rfl⟩ : syracuseStep 3674411 = 5511617) B5511617
theorem B4133207 : Blo 1632515 4133207 := bstep (se 1 (by rfl) ⟨3099905, by rfl⟩ : syracuseStep 4133207 = 6199811) B6199811
theorem B2756983 : Blo 1632515 2756983 := bstep (se 1 (by rfl) ⟨2067737, by rfl⟩ : syracuseStep 2756983 = 4135475) B4135475
theorem B75436433 : Blo 1632515 75436433 := bstep (se 2 (by rfl) ⟨28288662, by rfl⟩ : syracuseStep 75436433 = 56577325) B56577325
theorem B3101075 : Blo 1632515 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B4248065 : Blo 1632515 4248065 := bstep (se 2 (by rfl) ⟨1593024, by rfl⟩ : syracuseStep 4248065 = 3186049) B3186049
theorem B2757179 : Blo 1632515 2757179 := bstep (se 1 (by rfl) ⟨2067884, by rfl⟩ : syracuseStep 2757179 = 4135769) B4135769
theorem B6287939 : Blo 1632515 6287939 := bstep (se 1 (by rfl) ⟨4715954, by rfl⟩ : syracuseStep 6287939 = 9431909) B9431909
theorem B8270423 : Blo 1632515 8270423 := bstep (se 1 (by rfl) ⟨6202817, by rfl⟩ : syracuseStep 8270423 = 12405635) B12405635
theorem B3101303 : Blo 1632515 3101303 := bstep (se 1 (by rfl) ⟨2325977, by rfl⟩ : syracuseStep 3101303 = 4651955) B4651955
theorem B3674771 : Blo 1632515 3674771 := bstep (se 1 (by rfl) ⟨2756078, by rfl⟩ : syracuseStep 3674771 = 5512157) B5512157
theorem B26489537 : Blo 1632515 26489537 := bstep (se 2 (by rfl) ⟨9933576, by rfl⟩ : syracuseStep 26489537 = 19867153) B19867153
theorem B3674825 : Blo 1632515 3674825 := bstep (se 2 (by rfl) ⟨1378059, by rfl⟩ : syracuseStep 3674825 = 2756119) B2756119
theorem B5509889 : Blo 1632515 5509889 := bstep (se 2 (by rfl) ⟨2066208, by rfl⟩ : syracuseStep 5509889 = 4132417) B4132417
theorem B3142547 : Blo 1632515 3142547 := bstep (se 1 (by rfl) ⟨2356910, by rfl⟩ : syracuseStep 3142547 = 4713821) B4713821
theorem B4649881 : Blo 1632515 4649881 := bstep (se 2 (by rfl) ⟨1743705, by rfl⟩ : syracuseStep 4649881 = 3487411) B3487411
theorem B80573363 : Blo 1632515 80573363 := bstep (se 1 (by rfl) ⟨60430022, by rfl⟩ : syracuseStep 80573363 = 120860045) B120860045
theorem B8270909 : Blo 1632515 8270909 := bstep (se 3 (by rfl) ⟨1550795, by rfl⟩ : syracuseStep 8270909 = 3101591) B3101591
theorem B3978425 : Blo 1632515 3978425 := bstep (se 2 (by rfl) ⟨1491909, by rfl⟩ : syracuseStep 3978425 = 2983819) B2983819
theorem B3142955 : Blo 1632515 3142955 := bstep (se 1 (by rfl) ⟨2357216, by rfl⟩ : syracuseStep 3142955 = 4714433) B4714433
theorem B3675527 : Blo 1632515 3675527 := bstep (se 1 (by rfl) ⟨2756645, by rfl⟩ : syracuseStep 3675527 = 5513291) B5513291
theorem B4650497 : Blo 1632515 4650497 := bstep (se 2 (by rfl) ⟨1743936, by rfl⟩ : syracuseStep 4650497 = 3487873) B3487873
theorem B5510699 : Blo 1632515 5510699 := bstep (se 1 (by rfl) ⟨4133024, by rfl⟩ : syracuseStep 5510699 = 8266049) B8266049
theorem B3675707 : Blo 1632515 3675707 := bstep (se 1 (by rfl) ⟨2756780, by rfl⟩ : syracuseStep 3675707 = 5513561) B5513561
theorem B3675833 : Blo 1632515 3675833 := bstep (se 2 (by rfl) ⟨1378437, by rfl⟩ : syracuseStep 3675833 = 2756875) B2756875
theorem B3487531 : Blo 1632515 3487531 := bstep (se 1 (by rfl) ⟨2615648, by rfl⟩ : syracuseStep 3487531 = 5231297) B5231297
theorem B3676175 : Blo 1632515 3676175 := bstep (se 1 (by rfl) ⟨2757131, by rfl⟩ : syracuseStep 3676175 = 5514263) B5514263
theorem B6199325 : Blo 1632515 6199325 := bstep (se 3 (by rfl) ⟨1162373, by rfl⟩ : syracuseStep 6199325 = 2324747) B2324747
theorem B3676193 : Blo 1632515 3676193 := bstep (se 2 (by rfl) ⟨1378572, by rfl⟩ : syracuseStep 3676193 = 2757145) B2757145
theorem B3487787 : Blo 1632515 3487787 := bstep (se 1 (by rfl) ⟨2615840, by rfl⟩ : syracuseStep 3487787 = 5231681) B5231681
theorem B3774583 : Blo 1632515 3774583 := bstep (se 1 (by rfl) ⟨2830937, by rfl⟩ : syracuseStep 3774583 = 5661875) B5661875
theorem B3537211 : Blo 1632515 3537211 := bstep (se 1 (by rfl) ⟨2652908, by rfl⟩ : syracuseStep 3537211 = 5305817) B5305817
theorem B9304409 : Blo 1632515 9304409 := bstep (se 2 (by rfl) ⟨3489153, by rfl⟩ : syracuseStep 9304409 = 6978307) B6978307
theorem B4135283 : Blo 1632515 4135283 := bstep (se 1 (by rfl) ⟨3101462, by rfl⟩ : syracuseStep 4135283 = 6202925) B6202925
theorem B3676535 : Blo 1632515 3676535 := bstep (se 1 (by rfl) ⟨2757401, by rfl⟩ : syracuseStep 3676535 = 5514803) B5514803
theorem B6371731 : Blo 1632515 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B4651465 : Blo 1632515 4651465 := bstep (se 2 (by rfl) ⟨1744299, by rfl⟩ : syracuseStep 4651465 = 3488599) B3488599
theorem B6200009 : Blo 1632515 6200009 := bstep (se 2 (by rfl) ⟨2325003, by rfl⟩ : syracuseStep 6200009 = 4650007) B4650007
theorem B5233423 : Blo 1632515 5233423 := bstep (se 1 (by rfl) ⟨3925067, by rfl⟩ : syracuseStep 5233423 = 7850135) B7850135
theorem B9304865 : Blo 1632515 9304865 := bstep (se 2 (by rfl) ⟨3489324, by rfl⟩ : syracuseStep 9304865 = 6978649) B6978649
theorem B2325305 : Blo 1632515 2325305 := bstep (se 2 (by rfl) ⟨871989, by rfl⟩ : syracuseStep 2325305 = 1743979) B1743979
theorem B5511995 : Blo 1632515 5511995 := bstep (se 1 (by rfl) ⟨4133996, by rfl⟩ : syracuseStep 5511995 = 8267993) B8267993
theorem B4135799 : Blo 1632515 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B18856907 : Blo 1632515 18856907 := bstep (se 1 (by rfl) ⟨14142680, by rfl⟩ : syracuseStep 18856907 = 28285361) B28285361
theorem B3922955 : Blo 1632515 3922955 := bstep (se 1 (by rfl) ⟨2942216, by rfl⟩ : syracuseStep 3922955 = 5884433) B5884433
theorem B9305117 : Blo 1632515 9305117 := bstep (se 3 (by rfl) ⟨1744709, by rfl⟩ : syracuseStep 9305117 = 3489419) B3489419
theorem B3488915 : Blo 1632515 3488915 := bstep (se 1 (by rfl) ⟨2616686, by rfl⟩ : syracuseStep 3488915 = 5233373) B5233373
theorem B5512481 : Blo 1632515 5512481 := bstep (se 2 (by rfl) ⟨2067180, by rfl⟩ : syracuseStep 5512481 = 4134361) B4134361
theorem B2448827 : Blo 1632515 2448827 := bstep (se 1 (by rfl) ⟨1836620, by rfl⟩ : syracuseStep 2448827 = 3673241) B3673241
theorem B2448887 : Blo 1632515 2448887 := bstep (se 1 (by rfl) ⟨1836665, by rfl⟩ : syracuseStep 2448887 = 3673331) B3673331
theorem B2448911 : Blo 1632515 2448911 := bstep (se 1 (by rfl) ⟨1836683, by rfl⟩ : syracuseStep 2448911 = 3673367) B3673367
theorem B8265239 : Blo 1632515 8265239 := bstep (se 1 (by rfl) ⟨6198929, by rfl⟩ : syracuseStep 8265239 = 12397859) B12397859
theorem B2448953 : Blo 1632515 2448953 := bstep (se 2 (by rfl) ⟨918357, by rfl⟩ : syracuseStep 2448953 = 1836715) B1836715
theorem B36789835 : Blo 1632515 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B8830583 : Blo 1632515 8830583 := bstep (se 1 (by rfl) ⟨6622937, by rfl⟩ : syracuseStep 8830583 = 13245875) B13245875
theorem B2449031 : Blo 1632515 2449031 := bstep (se 1 (by rfl) ⟨1836773, by rfl⟩ : syracuseStep 2449031 = 3673547) B3673547
theorem B3489427 : Blo 1632515 3489427 := bstep (se 1 (by rfl) ⟨2617070, by rfl⟩ : syracuseStep 3489427 = 5234141) B5234141
theorem B2449067 : Blo 1632515 2449067 := bstep (se 1 (by rfl) ⟨1836800, by rfl⟩ : syracuseStep 2449067 = 3673601) B3673601
theorem B2449097 : Blo 1632515 2449097 := bstep (se 2 (by rfl) ⟨918411, by rfl⟩ : syracuseStep 2449097 = 1836823) B1836823
theorem B27901745 : Blo 1632515 27901745 := bstep (se 2 (by rfl) ⟨10463154, by rfl⟩ : syracuseStep 27901745 = 20926309) B20926309
theorem B2449211 : Blo 1632515 2449211 := bstep (se 1 (by rfl) ⟨1836908, by rfl⟩ : syracuseStep 2449211 = 3673817) B3673817
theorem B5513075 : Blo 1632515 5513075 := bstep (se 1 (by rfl) ⟨4134806, by rfl⟩ : syracuseStep 5513075 = 8269613) B8269613
theorem B2449271 : Blo 1632515 2449271 := bstep (se 1 (by rfl) ⟨1836953, by rfl⟩ : syracuseStep 2449271 = 3673907) B3673907
theorem B2449295 : Blo 1632515 2449295 := bstep (se 1 (by rfl) ⟨1836971, by rfl⟩ : syracuseStep 2449295 = 3673943) B3673943
theorem B8380307 : Blo 1632515 8380307 := bstep (se 1 (by rfl) ⟨6285230, by rfl⟩ : syracuseStep 8380307 = 12570461) B12570461
theorem B11771801 : Blo 1632515 11771801 := bstep (se 2 (by rfl) ⟨4414425, by rfl⟩ : syracuseStep 11771801 = 8828851) B8828851
theorem B2449337 : Blo 1632515 2449337 := bstep (se 2 (by rfl) ⟨918501, by rfl⟩ : syracuseStep 2449337 = 1837003) B1837003
theorem B6979537 : Blo 1632515 6979537 := bstep (se 2 (by rfl) ⟨2617326, by rfl⟩ : syracuseStep 6979537 = 5234653) B5234653
theorem B2449487 : Blo 1632515 2449487 := bstep (se 1 (by rfl) ⟨1837115, by rfl⟩ : syracuseStep 2449487 = 3674231) B3674231
theorem B2449607 : Blo 1632515 2449607 := bstep (se 1 (by rfl) ⟨1837205, by rfl⟩ : syracuseStep 2449607 = 3674411) B3674411
theorem B10461413 : Blo 1632515 10461413 := bstep (se 4 (by rfl) ⟨980757, by rfl⟩ : syracuseStep 10461413 = 1961515) B1961515
theorem B50290955 : Blo 1632515 50290955 := bstep (se 1 (by rfl) ⟨37718216, by rfl⟩ : syracuseStep 50290955 = 75436433) B75436433
theorem B2449769 : Blo 1632515 2449769 := bstep (se 2 (by rfl) ⟨918663, by rfl⟩ : syracuseStep 2449769 = 1837327) B1837327
theorem B5513615 : Blo 1632515 5513615 := bstep (se 1 (by rfl) ⟨4135211, by rfl⟩ : syracuseStep 5513615 = 8270423) B8270423
theorem B2449847 : Blo 1632515 2449847 := bstep (se 1 (by rfl) ⟨1837385, by rfl⟩ : syracuseStep 2449847 = 3674771) B3674771
theorem B2449883 : Blo 1632515 2449883 := bstep (se 1 (by rfl) ⟨1837412, by rfl⟩ : syracuseStep 2449883 = 3674825) B3674825
theorem B8495641 : Blo 1632515 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B6201953 : Blo 1632515 6201953 := bstep (se 2 (by rfl) ⟨2325732, by rfl⟩ : syracuseStep 6201953 = 4651465) B4651465
theorem B53715575 : Blo 1632515 53715575 := bstep (se 1 (by rfl) ⟨40286681, by rfl⟩ : syracuseStep 53715575 = 80573363) B80573363
theorem B5513939 : Blo 1632515 5513939 := bstep (se 1 (by rfl) ⟨4135454, by rfl⟩ : syracuseStep 5513939 = 8270909) B8270909
theorem B7848733 : Blo 1632515 7848733 := bstep (se 3 (by rfl) ⟨1471637, by rfl⟩ : syracuseStep 7848733 = 2943275) B2943275
theorem B2450351 : Blo 1632515 2450351 := bstep (se 1 (by rfl) ⟨1837763, by rfl⟩ : syracuseStep 2450351 = 3675527) B3675527
theorem B2450441 : Blo 1632515 2450441 := bstep (se 2 (by rfl) ⟨918915, by rfl⟩ : syracuseStep 2450441 = 1837831) B1837831
theorem B2450471 : Blo 1632515 2450471 := bstep (se 1 (by rfl) ⟨1837853, by rfl⟩ : syracuseStep 2450471 = 3675707) B3675707
theorem B2450555 : Blo 1632515 2450555 := bstep (se 1 (by rfl) ⟨1837916, by rfl⟩ : syracuseStep 2450555 = 3675833) B3675833
theorem B2450681 : Blo 1632515 2450681 := bstep (se 2 (by rfl) ⟨919005, by rfl⟩ : syracuseStep 2450681 = 1838011) B1838011
theorem B2450783 : Blo 1632515 2450783 := bstep (se 1 (by rfl) ⟨1838087, by rfl⟩ : syracuseStep 2450783 = 3676175) B3676175
theorem B2450795 : Blo 1632515 2450795 := bstep (se 1 (by rfl) ⟨1838096, by rfl⟩ : syracuseStep 2450795 = 3676193) B3676193
theorem B11322919 : Blo 1632515 11322919 := bstep (se 1 (by rfl) ⟨8492189, by rfl⟩ : syracuseStep 11322919 = 16984379) B16984379
theorem B6202939 : Blo 1632515 6202939 := bstep (se 1 (by rfl) ⟨4652204, by rfl⟩ : syracuseStep 6202939 = 9304409) B9304409
theorem B2451023 : Blo 1632515 2451023 := bstep (se 1 (by rfl) ⟨1838267, by rfl⟩ : syracuseStep 2451023 = 3676535) B3676535
theorem B8832701 : Blo 1632515 8832701 := bstep (se 3 (by rfl) ⟨1656131, by rfl⟩ : syracuseStep 8832701 = 3312263) B3312263
theorem B2983673 : Blo 1632515 2983673 := bstep (se 2 (by rfl) ⟨1118877, by rfl⟩ : syracuseStep 2983673 = 2237755) B2237755
theorem B6620957 : Blo 1632515 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B1836895 : Blo 1632515 1836895 := bstep (se 1 (by rfl) ⟨1377671, by rfl⟩ : syracuseStep 1836895 = 2755343) B2755343
theorem B6203243 : Blo 1632515 6203243 := bstep (se 1 (by rfl) ⟨4652432, by rfl⟩ : syracuseStep 6203243 = 9304865) B9304865
theorem B12912493 : Blo 1632515 12912493 := bstep (se 3 (by rfl) ⟨2421092, by rfl⟩ : syracuseStep 12912493 = 4842185) B4842185
theorem B13420475 : Blo 1632515 13420475 := bstep (se 1 (by rfl) ⟨10065356, by rfl⟩ : syracuseStep 13420475 = 20130713) B20130713
theorem B5883911 : Blo 1632515 5883911 := bstep (se 1 (by rfl) ⟨4412933, by rfl⟩ : syracuseStep 5883911 = 8825867) B8825867
theorem B2615303 : Blo 1632515 2615303 := bstep (se 1 (by rfl) ⟨1961477, by rfl⟩ : syracuseStep 2615303 = 3922955) B3922955
theorem B6621203 : Blo 1632515 6621203 := bstep (se 1 (by rfl) ⟨4965902, by rfl⟩ : syracuseStep 6621203 = 9931805) B9931805
theorem B6203411 : Blo 1632515 6203411 := bstep (se 1 (by rfl) ⟨4652558, by rfl⟩ : syracuseStep 6203411 = 9305117) B9305117
theorem B9930833 : Blo 1632515 9930833 := bstep (se 2 (by rfl) ⟨3724062, by rfl⟩ : syracuseStep 9930833 = 7448125) B7448125
theorem B1837255 : Blo 1632515 1837255 := bstep (se 1 (by rfl) ⟨1377941, by rfl⟩ : syracuseStep 1837255 = 2755883) B2755883
theorem B1632551 : Blo 1632515 1632551 := bstep (se 1 (by rfl) ⟨1224413, by rfl⟩ : syracuseStep 1632551 = 2448827) B2448827
theorem B1632591 : Blo 1632515 1632591 := bstep (se 1 (by rfl) ⟨1224443, by rfl⟩ : syracuseStep 1632591 = 2448887) B2448887
theorem B2754911 : Blo 1632515 2754911 := bstep (se 1 (by rfl) ⟨2066183, by rfl⟩ : syracuseStep 2754911 = 4132367) B4132367
theorem B1632607 : Blo 1632515 1632607 := bstep (se 1 (by rfl) ⟨1224455, by rfl⟩ : syracuseStep 1632607 = 2448911) B2448911
theorem B1632635 : Blo 1632515 1632635 := bstep (se 1 (by rfl) ⟨1224476, by rfl⟩ : syracuseStep 1632635 = 2448953) B2448953
theorem B1632687 : Blo 1632515 1632687 := bstep (se 1 (by rfl) ⟨1224515, by rfl⟩ : syracuseStep 1632687 = 2449031) B2449031
theorem B1632711 : Blo 1632515 1632711 := bstep (se 1 (by rfl) ⟨1224533, by rfl⟩ : syracuseStep 1632711 = 2449067) B2449067
theorem B1632731 : Blo 1632515 1632731 := bstep (se 1 (by rfl) ⟨1224548, by rfl⟩ : syracuseStep 1632731 = 2449097) B2449097
theorem B6973933 : Blo 1632515 6973933 := bstep (se 3 (by rfl) ⟨1307612, by rfl⟩ : syracuseStep 6973933 = 2615225) B2615225
theorem B1632807 : Blo 1632515 1632807 := bstep (se 1 (by rfl) ⟨1224605, by rfl⟩ : syracuseStep 1632807 = 2449211) B2449211
theorem B1632847 : Blo 1632515 1632847 := bstep (se 1 (by rfl) ⟨1224635, by rfl⟩ : syracuseStep 1632847 = 2449271) B2449271
theorem B1632863 : Blo 1632515 1632863 := bstep (se 1 (by rfl) ⟨1224647, by rfl⟩ : syracuseStep 1632863 = 2449295) B2449295
theorem B1632891 : Blo 1632515 1632891 := bstep (se 1 (by rfl) ⟨1224668, by rfl⟩ : syracuseStep 1632891 = 2449337) B2449337
theorem B1632943 : Blo 1632515 1632943 := bstep (se 1 (by rfl) ⟨1224707, by rfl⟩ : syracuseStep 1632943 = 2449415) B2449415
theorem B1632967 : Blo 1632515 1632967 := bstep (se 1 (by rfl) ⟨1224725, by rfl⟩ : syracuseStep 1632967 = 2449451) B2449451
theorem B11176649 : Blo 1632515 11176649 := bstep (se 2 (by rfl) ⟨4191243, by rfl⟩ : syracuseStep 11176649 = 8382487) B8382487
theorem B1632987 : Blo 1632515 1632987 := bstep (se 1 (by rfl) ⟨1224740, by rfl⟩ : syracuseStep 1632987 = 2449481) B2449481
theorem B1633063 : Blo 1632515 1633063 := bstep (se 1 (by rfl) ⟨1224797, by rfl⟩ : syracuseStep 1633063 = 2449595) B2449595
theorem B6621995 : Blo 1632515 6621995 := bstep (se 1 (by rfl) ⟨4966496, by rfl⟩ : syracuseStep 6621995 = 9932993) B9932993
theorem B5032777 : Blo 1632515 5032777 := bstep (se 2 (by rfl) ⟨1887291, by rfl⟩ : syracuseStep 5032777 = 3774583) B3774583
theorem B39742285 : Blo 1632515 39742285 := bstep (se 3 (by rfl) ⟨7451678, by rfl⟩ : syracuseStep 39742285 = 14903357) B14903357
theorem B1633103 : Blo 1632515 1633103 := bstep (se 1 (by rfl) ⟨1224827, by rfl⟩ : syracuseStep 1633103 = 2449655) B2449655
theorem B1633119 : Blo 1632515 1633119 := bstep (se 1 (by rfl) ⟨1224839, by rfl⟩ : syracuseStep 1633119 = 2449679) B2449679
theorem B1633147 : Blo 1632515 1633147 := bstep (se 1 (by rfl) ⟨1224860, by rfl⟩ : syracuseStep 1633147 = 2449721) B2449721
theorem B2755471 : Blo 1632515 2755471 := bstep (se 1 (by rfl) ⟨2066603, by rfl⟩ : syracuseStep 2755471 = 4133207) B4133207
theorem B18606995 : Blo 1632515 18606995 := bstep (se 1 (by rfl) ⟨13955246, by rfl⟩ : syracuseStep 18606995 = 27910493) B27910493
theorem B1633199 : Blo 1632515 1633199 := bstep (se 1 (by rfl) ⟨1224899, by rfl⟩ : syracuseStep 1633199 = 2449799) B2449799
theorem B2067383 : Blo 1632515 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B1633223 : Blo 1632515 1633223 := bstep (se 1 (by rfl) ⟨1224917, by rfl⟩ : syracuseStep 1633223 = 2449835) B2449835
theorem B1633243 : Blo 1632515 1633243 := bstep (se 1 (by rfl) ⟨1224932, by rfl⟩ : syracuseStep 1633243 = 2449865) B2449865
theorem B1633319 : Blo 1632515 1633319 := bstep (se 1 (by rfl) ⟨1224989, by rfl⟩ : syracuseStep 1633319 = 2449979) B2449979
theorem B1838119 : Blo 1632515 1838119 := bstep (se 1 (by rfl) ⟨1378589, by rfl⟩ : syracuseStep 1838119 = 2757179) B2757179
theorem B1633359 : Blo 1632515 1633359 := bstep (se 1 (by rfl) ⟨1225019, by rfl⟩ : syracuseStep 1633359 = 2450039) B2450039
theorem B2067535 : Blo 1632515 2067535 := bstep (se 1 (by rfl) ⟨1550651, by rfl⟩ : syracuseStep 2067535 = 3101303) B3101303
theorem B1633375 : Blo 1632515 1633375 := bstep (se 1 (by rfl) ⟨1225031, by rfl⟩ : syracuseStep 1633375 = 2450063) B2450063
theorem B1633403 : Blo 1632515 1633403 := bstep (se 1 (by rfl) ⟨1225052, by rfl⟩ : syracuseStep 1633403 = 2450105) B2450105
theorem B3673259 : Blo 1632515 3673259 := bstep (se 1 (by rfl) ⟨2754944, by rfl⟩ : syracuseStep 3673259 = 5509889) B5509889
theorem B1633455 : Blo 1632515 1633455 := bstep (se 1 (by rfl) ⟨1225091, by rfl⟩ : syracuseStep 1633455 = 2450183) B2450183
theorem B1633479 : Blo 1632515 1633479 := bstep (se 1 (by rfl) ⟨1225109, by rfl⟩ : syracuseStep 1633479 = 2450219) B2450219
theorem B1633499 : Blo 1632515 1633499 := bstep (se 1 (by rfl) ⟨1225124, by rfl⟩ : syracuseStep 1633499 = 2450249) B2450249
theorem B1633575 : Blo 1632515 1633575 := bstep (se 1 (by rfl) ⟨1225181, by rfl⟩ : syracuseStep 1633575 = 2450363) B2450363
theorem B1633615 : Blo 1632515 1633615 := bstep (se 1 (by rfl) ⟨1225211, by rfl⟩ : syracuseStep 1633615 = 2450423) B2450423
theorem B1633631 : Blo 1632515 1633631 := bstep (se 1 (by rfl) ⟨1225223, by rfl⟩ : syracuseStep 1633631 = 2450447) B2450447
theorem B1633659 : Blo 1632515 1633659 := bstep (se 1 (by rfl) ⟨1225244, by rfl⟩ : syracuseStep 1633659 = 2450489) B2450489
theorem B1633711 : Blo 1632515 1633711 := bstep (se 1 (by rfl) ⟨1225283, by rfl⟩ : syracuseStep 1633711 = 2450567) B2450567
theorem B1633735 : Blo 1632515 1633735 := bstep (se 1 (by rfl) ⟨1225301, by rfl⟩ : syracuseStep 1633735 = 2450603) B2450603
theorem B1633755 : Blo 1632515 1633755 := bstep (se 1 (by rfl) ⟨1225316, by rfl⟩ : syracuseStep 1633755 = 2450633) B2450633
theorem B1633831 : Blo 1632515 1633831 := bstep (se 1 (by rfl) ⟨1225373, by rfl⟩ : syracuseStep 1633831 = 2450747) B2450747
theorem B2756153 : Blo 1632515 2756153 := bstep (se 2 (by rfl) ⟨1033557, by rfl⟩ : syracuseStep 2756153 = 2067115) B2067115
theorem B1633871 : Blo 1632515 1633871 := bstep (se 1 (by rfl) ⟨1225403, by rfl⟩ : syracuseStep 1633871 = 2450807) B2450807
theorem B1633887 : Blo 1632515 1633887 := bstep (se 1 (by rfl) ⟨1225415, by rfl⟩ : syracuseStep 1633887 = 2450831) B2450831
theorem B1633915 : Blo 1632515 1633915 := bstep (se 1 (by rfl) ⟨1225436, by rfl⟩ : syracuseStep 1633915 = 2450873) B2450873
theorem B8269451 : Blo 1632515 8269451 := bstep (se 1 (by rfl) ⟨6202088, by rfl⟩ : syracuseStep 8269451 = 12404177) B12404177
theorem B3100331 : Blo 1632515 3100331 := bstep (se 1 (by rfl) ⟨2325248, by rfl⟩ : syracuseStep 3100331 = 4650497) B4650497
theorem B1633967 : Blo 1632515 1633967 := bstep (se 1 (by rfl) ⟨1225475, by rfl⟩ : syracuseStep 1633967 = 2450951) B2450951
theorem B3673799 : Blo 1632515 3673799 := bstep (se 1 (by rfl) ⟨2755349, by rfl⟩ : syracuseStep 3673799 = 5510699) B5510699
theorem B1633991 : Blo 1632515 1633991 := bstep (se 1 (by rfl) ⟨1225493, by rfl⟩ : syracuseStep 1633991 = 2450987) B2450987
theorem B6287063 : Blo 1632515 6287063 := bstep (se 1 (by rfl) ⟨4715297, by rfl⟩ : syracuseStep 6287063 = 9430595) B9430595
theorem B1634011 : Blo 1632515 1634011 := bstep (se 1 (by rfl) ⟨1225508, by rfl⟩ : syracuseStep 1634011 = 2451017) B2451017
theorem B6713131 : Blo 1632515 6713131 := bstep (se 1 (by rfl) ⟨5034848, by rfl⟩ : syracuseStep 6713131 = 10069697) B10069697
theorem B4132883 : Blo 1632515 4132883 := bstep (se 1 (by rfl) ⟨3099662, by rfl⟩ : syracuseStep 4132883 = 6199325) B6199325
theorem B4649039 : Blo 1632515 4649039 := bstep (se 1 (by rfl) ⟨3486779, by rfl⟩ : syracuseStep 4649039 = 6973559) B6973559
theorem B2756855 : Blo 1632515 2756855 := bstep (se 1 (by rfl) ⟨2067641, by rfl⟩ : syracuseStep 2756855 = 4135283) B4135283
theorem B7958795 : Blo 1632515 7958795 := bstep (se 1 (by rfl) ⟨5969096, by rfl⟩ : syracuseStep 7958795 = 11938193) B11938193
theorem B6287759 : Blo 1632515 6287759 := bstep (se 1 (by rfl) ⟨4715819, by rfl⟩ : syracuseStep 6287759 = 9431639) B9431639
theorem B4133339 : Blo 1632515 4133339 := bstep (se 1 (by rfl) ⟨3100004, by rfl⟩ : syracuseStep 4133339 = 6200009) B6200009
theorem B127250929 : Blo 1632515 127250929 := bstep (se 2 (by rfl) ⟨47719098, by rfl⟩ : syracuseStep 127250929 = 95438197) B95438197
theorem B3674663 : Blo 1632515 3674663 := bstep (se 1 (by rfl) ⟨2755997, by rfl⟩ : syracuseStep 3674663 = 5511995) B5511995
theorem B2757199 : Blo 1632515 2757199 := bstep (se 1 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 2757199 = 4135799) B4135799
theorem B54424163 : Blo 1632515 54424163 := bstep (se 1 (by rfl) ⟨40818122, by rfl⟩ : syracuseStep 54424163 = 81636245) B81636245
theorem B12571271 : Blo 1632515 12571271 := bstep (se 1 (by rfl) ⟨9428453, by rfl⟩ : syracuseStep 12571271 = 18856907) B18856907
theorem B3674987 : Blo 1632515 3674987 := bstep (se 1 (by rfl) ⟨2756240, by rfl⟩ : syracuseStep 3674987 = 5512481) B5512481
theorem B3675041 : Blo 1632515 3675041 := bstep (se 2 (by rfl) ⟨1378140, by rfl⟩ : syracuseStep 3675041 = 2756281) B2756281
theorem B5510159 : Blo 1632515 5510159 := bstep (se 1 (by rfl) ⟨4132619, by rfl⟩ : syracuseStep 5510159 = 8265239) B8265239
theorem B4650041 : Blo 1632515 4650041 := bstep (se 2 (by rfl) ⟨1743765, by rfl⟩ : syracuseStep 4650041 = 3487531) B3487531
theorem B5887055 : Blo 1632515 5887055 := bstep (se 1 (by rfl) ⟨4415291, by rfl⟩ : syracuseStep 5887055 = 8830583) B8830583
theorem B4650155 : Blo 1632515 4650155 := bstep (se 1 (by rfl) ⟨3487616, by rfl⟩ : syracuseStep 4650155 = 6975233) B6975233
theorem B18601163 : Blo 1632515 18601163 := bstep (se 1 (by rfl) ⟨13950872, by rfl⟩ : syracuseStep 18601163 = 27901745) B27901745
theorem B3675383 : Blo 1632515 3675383 := bstep (se 1 (by rfl) ⟨2756537, by rfl⟩ : syracuseStep 3675383 = 5513075) B5513075
theorem B3102047 : Blo 1632515 3102047 := bstep (se 1 (by rfl) ⟨2326535, by rfl⟩ : syracuseStep 3102047 = 4653071) B4653071
theorem B5510753 : Blo 1632515 5510753 := bstep (se 2 (by rfl) ⟨2066532, by rfl⟩ : syracuseStep 5510753 = 4133065) B4133065
theorem B4134523 : Blo 1632515 4134523 := bstep (se 1 (by rfl) ⟨3100892, by rfl⟩ : syracuseStep 4134523 = 6201785) B6201785
theorem B4191959 : Blo 1632515 4191959 := bstep (se 1 (by rfl) ⟨3143969, by rfl⟩ : syracuseStep 4191959 = 6287939) B6287939
theorem B4716281 : Blo 1632515 4716281 := bstep (se 2 (by rfl) ⟨1768605, by rfl⟩ : syracuseStep 4716281 = 3537211) B3537211
theorem B17659691 : Blo 1632515 17659691 := bstep (se 1 (by rfl) ⟨13244768, by rfl⟩ : syracuseStep 17659691 = 26489537) B26489537
theorem B3675977 : Blo 1632515 3675977 := bstep (se 2 (by rfl) ⟨1378491, by rfl⟩ : syracuseStep 3675977 = 2756983) B2756983
theorem B2095031 : Blo 1632515 2095031 := bstep (se 1 (by rfl) ⟨1571273, by rfl⟩ : syracuseStep 2095031 = 3142547) B3142547
theorem B26482787 : Blo 1632515 26482787 := bstep (se 1 (by rfl) ⟨19862090, by rfl⟩ : syracuseStep 26482787 = 39724181) B39724181
theorem B2652283 : Blo 1632515 2652283 := bstep (se 1 (by rfl) ⟨1989212, by rfl⟩ : syracuseStep 2652283 = 3978425) B3978425
theorem B2095303 : Blo 1632515 2095303 := bstep (se 1 (by rfl) ⟨1571477, by rfl⟩ : syracuseStep 2095303 = 3142955) B3142955
theorem B6977897 : Blo 1632515 6977897 := bstep (se 2 (by rfl) ⟨2616711, by rfl⟩ : syracuseStep 6977897 = 5233423) B5233423
theorem B6199841 : Blo 1632515 6199841 := bstep (se 2 (by rfl) ⟨2324940, by rfl⟩ : syracuseStep 6199841 = 4649881) B4649881
theorem B11328173 : Blo 1632515 11328173 := bstep (se 3 (by rfl) ⟨2124032, by rfl⟩ : syracuseStep 11328173 = 4248065) B4248065
theorem B2325191 : Blo 1632515 2325191 := bstep (se 1 (by rfl) ⟨1743893, by rfl⟩ : syracuseStep 2325191 = 3487787) B3487787
theorem B6200023 : Blo 1632515 6200023 := bstep (se 1 (by rfl) ⟨4650017, by rfl⟩ : syracuseStep 6200023 = 9300035) B9300035
theorem B21502903 : Blo 1632515 21502903 := bstep (se 1 (by rfl) ⟨16127177, by rfl⟩ : syracuseStep 21502903 = 32254355) B32254355
theorem B6200327 : Blo 1632515 6200327 := bstep (se 1 (by rfl) ⟨4650245, by rfl⟩ : syracuseStep 6200327 = 9300491) B9300491
theorem B5512211 : Blo 1632515 5512211 := bstep (se 1 (by rfl) ⟨4134158, by rfl⟩ : syracuseStep 5512211 = 8268317) B8268317
theorem B5512535 : Blo 1632515 5512535 := bstep (se 1 (by rfl) ⟨4134401, by rfl⟩ : syracuseStep 5512535 = 8268803) B8268803
theorem B2448815 : Blo 1632515 2448815 := bstep (se 1 (by rfl) ⟨1836611, by rfl⟩ : syracuseStep 2448815 = 3673223) B3673223
theorem B2325943 : Blo 1632515 2325943 := bstep (se 1 (by rfl) ⟨1744457, by rfl⟩ : syracuseStep 2325943 = 3488915) B3488915
theorem B49053113 : Blo 1632515 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B6200813 : Blo 1632515 6200813 := bstep (se 3 (by rfl) ⟨1162652, by rfl⟩ : syracuseStep 6200813 = 2325305) B2325305
theorem B2448905 : Blo 1632515 2448905 := bstep (se 2 (by rfl) ⟨918339, by rfl⟩ : syracuseStep 2448905 = 1836679) B1836679
theorem B4652569 : Blo 1632515 4652569 := bstep (se 2 (by rfl) ⟨1744713, by rfl⟩ : syracuseStep 4652569 = 3489427) B3489427
theorem B2448935 : Blo 1632515 2448935 := bstep (se 1 (by rfl) ⟨1836701, by rfl⟩ : syracuseStep 2448935 = 3673403) B3673403
theorem B2449019 : Blo 1632515 2449019 := bstep (se 1 (by rfl) ⟨1836764, by rfl⟩ : syracuseStep 2449019 = 3673529) B3673529
theorem B22347485 : Blo 1632515 22347485 := bstep (se 3 (by rfl) ⟨4190153, by rfl⟩ : syracuseStep 22347485 = 8380307) B8380307
theorem B10469101 : Blo 1632515 10469101 := bstep (se 3 (by rfl) ⟨1962956, by rfl⟩ : syracuseStep 10469101 = 3925913) B3925913
theorem B2449145 : Blo 1632515 2449145 := bstep (se 2 (by rfl) ⟨918429, by rfl⟩ : syracuseStep 2449145 = 1836859) B1836859
theorem B2449247 : Blo 1632515 2449247 := bstep (se 1 (by rfl) ⟨1836935, by rfl⟩ : syracuseStep 2449247 = 3673871) B3673871
theorem B2449259 : Blo 1632515 2449259 := bstep (se 1 (by rfl) ⟨1836944, by rfl⟩ : syracuseStep 2449259 = 3673889) B3673889
theorem B5234539 : Blo 1632515 5234539 := bstep (se 1 (by rfl) ⟨3925904, by rfl⟩ : syracuseStep 5234539 = 7851809) B7851809
theorem B7847867 : Blo 1632515 7847867 := bstep (se 1 (by rfl) ⟨5885900, by rfl⟩ : syracuseStep 7847867 = 11771801) B11771801
theorem B9306049 : Blo 1632515 9306049 := bstep (se 2 (by rfl) ⟨3489768, by rfl⟩ : syracuseStep 9306049 = 6979537) B6979537
theorem B1744859 : Blo 1632515 1744859 := bstep (se 1 (by rfl) ⟨1308644, by rfl⟩ : syracuseStep 1744859 = 2617289) B2617289
theorem B2449673 : Blo 1632515 2449673 := bstep (se 2 (by rfl) ⟨918627, by rfl⟩ : syracuseStep 2449673 = 1837255) B1837255
theorem B2793737 : Blo 1632515 2793737 := bstep (se 2 (by rfl) ⟨1047651, by rfl⟩ : syracuseStep 2793737 = 2095303) B2095303
theorem B2449775 : Blo 1632515 2449775 := bstep (se 1 (by rfl) ⟨1837331, by rfl⟩ : syracuseStep 2449775 = 3674663) B3674663
theorem B36282775 : Blo 1632515 36282775 := bstep (se 1 (by rfl) ⟨27212081, by rfl⟩ : syracuseStep 36282775 = 54424163) B54424163
theorem B8380847 : Blo 1632515 8380847 := bstep (se 1 (by rfl) ⟨6285635, by rfl⟩ : syracuseStep 8380847 = 12571271) B12571271
theorem B2449991 : Blo 1632515 2449991 := bstep (se 1 (by rfl) ⟨1837493, by rfl⟩ : syracuseStep 2449991 = 3674987) B3674987
theorem B2450027 : Blo 1632515 2450027 := bstep (se 1 (by rfl) ⟨1837520, by rfl⟩ : syracuseStep 2450027 = 3675041) B3675041
theorem B9298577 : Blo 1632515 9298577 := bstep (se 2 (by rfl) ⟨3486966, by rfl⟩ : syracuseStep 9298577 = 6973933) B6973933
theorem B3924703 : Blo 1632515 3924703 := bstep (se 1 (by rfl) ⟨2943527, by rfl⟩ : syracuseStep 3924703 = 5887055) B5887055
theorem B2450255 : Blo 1632515 2450255 := bstep (se 1 (by rfl) ⟨1837691, by rfl⟩ : syracuseStep 2450255 = 3675383) B3675383
theorem B8266697 : Blo 1632515 8266697 := bstep (se 2 (by rfl) ⟨3100011, by rfl⟩ : syracuseStep 8266697 = 6200023) B6200023
theorem B6710369 : Blo 1632515 6710369 := bstep (se 2 (by rfl) ⟨2516388, by rfl⟩ : syracuseStep 6710369 = 5032777) B5032777
theorem B11773127 : Blo 1632515 11773127 := bstep (se 1 (by rfl) ⟨8829845, by rfl⟩ : syracuseStep 11773127 = 17659691) B17659691
theorem B2450651 : Blo 1632515 2450651 := bstep (se 1 (by rfl) ⟨1837988, by rfl⟩ : syracuseStep 2450651 = 3675977) B3675977
theorem B8946983 : Blo 1632515 8946983 := bstep (se 1 (by rfl) ⟨6710237, by rfl⟩ : syracuseStep 8946983 = 13420475) B13420475
theorem B2450825 : Blo 1632515 2450825 := bstep (se 2 (by rfl) ⟨919059, by rfl⟩ : syracuseStep 2450825 = 1838119) B1838119
theorem B6620555 : Blo 1632515 6620555 := bstep (se 1 (by rfl) ⟨4965416, by rfl⟩ : syracuseStep 6620555 = 9930833) B9930833
theorem B17655191 : Blo 1632515 17655191 := bstep (se 1 (by rfl) ⟨13241393, by rfl⟩ : syracuseStep 17655191 = 26482787) B26482787
theorem B1836607 : Blo 1632515 1836607 := bstep (se 1 (by rfl) ⟨1377455, by rfl⟩ : syracuseStep 1836607 = 2754911) B2754911
theorem B12404663 : Blo 1632515 12404663 := bstep (se 1 (by rfl) ⟨9303497, by rfl⟩ : syracuseStep 12404663 = 18606995) B18606995
theorem B7956461 : Blo 1632515 7956461 := bstep (se 3 (by rfl) ⟨1491836, by rfl⟩ : syracuseStep 7956461 = 2983673) B2983673
theorem B6203425 : Blo 1632515 6203425 := bstep (se 2 (by rfl) ⟨2326284, by rfl⟩ : syracuseStep 6203425 = 4652569) B4652569
theorem B1632543 : Blo 1632515 1632543 := bstep (se 1 (by rfl) ⟨1224407, by rfl⟩ : syracuseStep 1632543 = 2448815) B2448815
theorem B1632603 : Blo 1632515 1632603 := bstep (se 1 (by rfl) ⟨1224452, by rfl⟩ : syracuseStep 1632603 = 2448905) B2448905
theorem B1632623 : Blo 1632515 1632623 := bstep (se 1 (by rfl) ⟨1224467, by rfl⟩ : syracuseStep 1632623 = 2448935) B2448935
theorem B1837435 : Blo 1632515 1837435 := bstep (se 1 (by rfl) ⟨1378076, by rfl⟩ : syracuseStep 1837435 = 2756153) B2756153
theorem B1632679 : Blo 1632515 1632679 := bstep (se 1 (by rfl) ⟨1224509, by rfl⟩ : syracuseStep 1632679 = 2449019) B2449019
theorem B2066887 : Blo 1632515 2066887 := bstep (se 1 (by rfl) ⟨1550165, by rfl⟩ : syracuseStep 2066887 = 3100331) B3100331
theorem B1632763 : Blo 1632515 1632763 := bstep (se 1 (by rfl) ⟨1224572, by rfl⟩ : syracuseStep 1632763 = 2449145) B2449145
theorem B1632831 : Blo 1632515 1632831 := bstep (se 1 (by rfl) ⟨1224623, by rfl⟩ : syracuseStep 1632831 = 2449247) B2449247
theorem B1632839 : Blo 1632515 1632839 := bstep (se 1 (by rfl) ⟨1224629, by rfl⟩ : syracuseStep 1632839 = 2449259) B2449259
theorem B2755255 : Blo 1632515 2755255 := bstep (se 1 (by rfl) ⟨2066441, by rfl⟩ : syracuseStep 2755255 = 4132883) B4132883
theorem B17656541 : Blo 1632515 17656541 := bstep (se 3 (by rfl) ⟨3310601, by rfl⟩ : syracuseStep 17656541 = 6621203) B6621203
theorem B3099359 : Blo 1632515 3099359 := bstep (se 1 (by rfl) ⟨2324519, by rfl⟩ : syracuseStep 3099359 = 4649039) B4649039
theorem B1632991 : Blo 1632515 1632991 := bstep (se 1 (by rfl) ⟨1224743, by rfl⟩ : syracuseStep 1632991 = 2449487) B2449487
theorem B1633071 : Blo 1632515 1633071 := bstep (se 1 (by rfl) ⟨1224803, by rfl⟩ : syracuseStep 1633071 = 2449607) B2449607
theorem B6974275 : Blo 1632515 6974275 := bstep (se 1 (by rfl) ⟨5230706, by rfl⟩ : syracuseStep 6974275 = 10461413) B10461413
theorem B1837903 : Blo 1632515 1837903 := bstep (se 1 (by rfl) ⟨1378427, by rfl⟩ : syracuseStep 1837903 = 2756855) B2756855
theorem B1633179 : Blo 1632515 1633179 := bstep (se 1 (by rfl) ⟨1224884, by rfl⟩ : syracuseStep 1633179 = 2449769) B2449769
theorem B1633231 : Blo 1632515 1633231 := bstep (se 1 (by rfl) ⟨1224923, by rfl⟩ : syracuseStep 1633231 = 2449847) B2449847
theorem B2755559 : Blo 1632515 2755559 := bstep (se 1 (by rfl) ⟨2066669, by rfl⟩ : syracuseStep 2755559 = 4133339) B4133339
theorem B1633255 : Blo 1632515 1633255 := bstep (se 1 (by rfl) ⟨1224941, by rfl⟩ : syracuseStep 1633255 = 2449883) B2449883
theorem B35810383 : Blo 1632515 35810383 := bstep (se 1 (by rfl) ⟨26857787, by rfl⟩ : syracuseStep 35810383 = 53715575) B53715575
theorem B1633567 : Blo 1632515 1633567 := bstep (se 1 (by rfl) ⟨1225175, by rfl⟩ : syracuseStep 1633567 = 2450351) B2450351
theorem B169667905 : Blo 1632515 169667905 := bstep (se 2 (by rfl) ⟨63625464, by rfl⟩ : syracuseStep 169667905 = 127250929) B127250929
theorem B1633627 : Blo 1632515 1633627 := bstep (se 1 (by rfl) ⟨1225220, by rfl⟩ : syracuseStep 1633627 = 2450441) B2450441
theorem B3673439 : Blo 1632515 3673439 := bstep (se 1 (by rfl) ⟨2755079, by rfl⟩ : syracuseStep 3673439 = 5510159) B5510159
theorem B1633647 : Blo 1632515 1633647 := bstep (se 1 (by rfl) ⟨1225235, by rfl⟩ : syracuseStep 1633647 = 2450471) B2450471
theorem B3100027 : Blo 1632515 3100027 := bstep (se 1 (by rfl) ⟨2325020, by rfl⟩ : syracuseStep 3100027 = 4650041) B4650041
theorem B1633703 : Blo 1632515 1633703 := bstep (se 1 (by rfl) ⟨1225277, by rfl⟩ : syracuseStep 1633703 = 2450555) B2450555
theorem B3100103 : Blo 1632515 3100103 := bstep (se 1 (by rfl) ⟨2325077, by rfl⟩ : syracuseStep 3100103 = 4650155) B4650155
theorem B1633787 : Blo 1632515 1633787 := bstep (se 1 (by rfl) ⟨1225340, by rfl⟩ : syracuseStep 1633787 = 2450681) B2450681
theorem B1633855 : Blo 1632515 1633855 := bstep (se 1 (by rfl) ⟨1225391, by rfl⟩ : syracuseStep 1633855 = 2450783) B2450783
theorem B2068031 : Blo 1632515 2068031 := bstep (se 1 (by rfl) ⟨1551023, by rfl⟩ : syracuseStep 2068031 = 3102047) B3102047
theorem B1633863 : Blo 1632515 1633863 := bstep (se 1 (by rfl) ⟨1225397, by rfl⟩ : syracuseStep 1633863 = 2450795) B2450795
theorem B10464977 : Blo 1632515 10464977 := bstep (se 2 (by rfl) ⟨3924366, by rfl⟩ : syracuseStep 10464977 = 7848733) B7848733
theorem B1634015 : Blo 1632515 1634015 := bstep (se 1 (by rfl) ⟨1225511, by rfl⟩ : syracuseStep 1634015 = 2451023) B2451023
theorem B3673835 : Blo 1632515 3673835 := bstep (se 1 (by rfl) ⟨2755376, by rfl⟩ : syracuseStep 3673835 = 5510753) B5510753
theorem B52989713 : Blo 1632515 52989713 := bstep (se 2 (by rfl) ⟨19871142, by rfl⟩ : syracuseStep 52989713 = 39742285) B39742285
theorem B3673961 : Blo 1632515 3673961 := bstep (se 2 (by rfl) ⟨1377735, by rfl⟩ : syracuseStep 3673961 = 2755471) B2755471
theorem B2756713 : Blo 1632515 2756713 := bstep (se 2 (by rfl) ⟨1033767, by rfl⟩ : syracuseStep 2756713 = 2067535) B2067535
theorem B4133227 : Blo 1632515 4133227 := bstep (se 1 (by rfl) ⟨3099920, by rfl⟩ : syracuseStep 4133227 = 6199841) B6199841
theorem B7451099 : Blo 1632515 7451099 := bstep (se 1 (by rfl) ⟨5588324, by rfl⟩ : syracuseStep 7451099 = 11176649) B11176649
theorem B16765501 : Blo 1632515 16765501 := bstep (se 3 (by rfl) ⟨3143531, by rfl⟩ : syracuseStep 16765501 = 6287063) B6287063
theorem B11178557 : Blo 1632515 11178557 := bstep (se 3 (by rfl) ⟨2095979, by rfl⟩ : syracuseStep 11178557 = 4191959) B4191959
theorem B3101257 : Blo 1632515 3101257 := bstep (se 2 (by rfl) ⟨1162971, by rfl⟩ : syracuseStep 3101257 = 2325943) B2325943
theorem B4133551 : Blo 1632515 4133551 := bstep (se 1 (by rfl) ⟨3100163, by rfl⟩ : syracuseStep 4133551 = 6200327) B6200327
theorem B3674807 : Blo 1632515 3674807 := bstep (se 1 (by rfl) ⟨2756105, by rfl⟩ : syracuseStep 3674807 = 5512211) B5512211
theorem B8270585 : Blo 1632515 8270585 := bstep (se 2 (by rfl) ⟨3101469, by rfl⟩ : syracuseStep 8270585 = 6202939) B6202939
theorem B3675023 : Blo 1632515 3675023 := bstep (se 1 (by rfl) ⟨2756267, by rfl⟩ : syracuseStep 3675023 = 5512535) B5512535
theorem B4133875 : Blo 1632515 4133875 := bstep (se 1 (by rfl) ⟨3100406, by rfl⟩ : syracuseStep 4133875 = 6200813) B6200813
theorem B8950841 : Blo 1632515 8950841 := bstep (se 2 (by rfl) ⟨3356565, by rfl⟩ : syracuseStep 8950841 = 6713131) B6713131
theorem B17216657 : Blo 1632515 17216657 := bstep (se 2 (by rfl) ⟨6456246, by rfl⟩ : syracuseStep 17216657 = 12912493) B12912493
theorem B14898323 : Blo 1632515 14898323 := bstep (se 1 (by rfl) ⟨11173742, by rfl⟩ : syracuseStep 14898323 = 22347485) B22347485
theorem B20927645 : Blo 1632515 20927645 := bstep (se 3 (by rfl) ⟨3923933, by rfl⟩ : syracuseStep 20927645 = 7847867) B7847867
theorem B12408065 : Blo 1632515 12408065 := bstep (se 2 (by rfl) ⟨4653024, by rfl⟩ : syracuseStep 12408065 = 9306049) B9306049
theorem B33527303 : Blo 1632515 33527303 := bstep (se 1 (by rfl) ⟨25145477, by rfl⟩ : syracuseStep 33527303 = 50290955) B50290955
theorem B3675743 : Blo 1632515 3675743 := bstep (se 1 (by rfl) ⟨2756807, by rfl⟩ : syracuseStep 3675743 = 5513615) B5513615
theorem B4191839 : Blo 1632515 4191839 := bstep (se 1 (by rfl) ⟨3143879, by rfl⟩ : syracuseStep 4191839 = 6287759) B6287759
theorem B4134635 : Blo 1632515 4134635 := bstep (se 1 (by rfl) ⟨3100976, by rfl⟩ : syracuseStep 4134635 = 6201953) B6201953
theorem B3675959 : Blo 1632515 3675959 := bstep (se 1 (by rfl) ⟨2756969, by rfl⟩ : syracuseStep 3675959 = 5513939) B5513939
theorem B14145509 : Blo 1632515 14145509 := bstep (se 4 (by rfl) ⟨1326141, by rfl⟩ : syracuseStep 14145509 = 2652283) B2652283
theorem B21223453 : Blo 1632515 21223453 := bstep (se 3 (by rfl) ⟨3979397, by rfl⟩ : syracuseStep 21223453 = 7958795) B7958795
theorem B11327521 : Blo 1632515 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B3676265 : Blo 1632515 3676265 := bstep (se 2 (by rfl) ⟨1378599, by rfl⟩ : syracuseStep 3676265 = 2757199) B2757199
theorem B12400775 : Blo 1632515 12400775 := bstep (se 1 (by rfl) ⟨9300581, by rfl⟩ : syracuseStep 12400775 = 18601163) B18601163
theorem B5888467 : Blo 1632515 5888467 := bstep (se 1 (by rfl) ⟨4416350, by rfl⟩ : syracuseStep 5888467 = 8832701) B8832701
theorem B3144187 : Blo 1632515 3144187 := bstep (se 1 (by rfl) ⟨2358140, by rfl⟩ : syracuseStep 3144187 = 4716281) B4716281
theorem B4413971 : Blo 1632515 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B4135495 : Blo 1632515 4135495 := bstep (se 1 (by rfl) ⟨3101621, by rfl⟩ : syracuseStep 4135495 = 6203243) B6203243
theorem B28670537 : Blo 1632515 28670537 := bstep (se 2 (by rfl) ⟨10751451, by rfl⟩ : syracuseStep 28670537 = 21502903) B21502903
theorem B3922607 : Blo 1632515 3922607 := bstep (se 1 (by rfl) ⟨2941955, by rfl⟩ : syracuseStep 3922607 = 5883911) B5883911
theorem B1743535 : Blo 1632515 1743535 := bstep (se 1 (by rfl) ⟨1307651, by rfl⟩ : syracuseStep 1743535 = 2615303) B2615303
theorem B4135607 : Blo 1632515 4135607 := bstep (se 1 (by rfl) ⟨3101705, by rfl⟩ : syracuseStep 4135607 = 6203411) B6203411
theorem B4651931 : Blo 1632515 4651931 := bstep (se 1 (by rfl) ⟨3488948, by rfl⟩ : syracuseStep 4651931 = 6977897) B6977897
theorem B7552115 : Blo 1632515 7552115 := bstep (se 1 (by rfl) ⟨5664086, by rfl⟩ : syracuseStep 7552115 = 11328173) B11328173
theorem B6200509 : Blo 1632515 6200509 := bstep (se 3 (by rfl) ⟨1162595, by rfl⟩ : syracuseStep 6200509 = 2325191) B2325191
theorem B4414663 : Blo 1632515 4414663 := bstep (se 1 (by rfl) ⟨3310997, by rfl⟩ : syracuseStep 4414663 = 6621995) B6621995
theorem B15097225 : Blo 1632515 15097225 := bstep (se 2 (by rfl) ⟨5661459, by rfl⟩ : syracuseStep 15097225 = 11322919) B11322919
theorem B2448839 : Blo 1632515 2448839 := bstep (se 1 (by rfl) ⟨1836629, by rfl⟩ : syracuseStep 2448839 = 3673259) B3673259
theorem B5512697 : Blo 1632515 5512697 := bstep (se 2 (by rfl) ⟨2067261, by rfl⟩ : syracuseStep 5512697 = 4134523) B4134523
theorem B32702075 : Blo 1632515 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B13958801 : Blo 1632515 13958801 := bstep (se 2 (by rfl) ⟨5234550, by rfl⟩ : syracuseStep 13958801 = 10469101) B10469101
theorem B5512967 : Blo 1632515 5512967 := bstep (se 1 (by rfl) ⟨4134725, by rfl⟩ : syracuseStep 5512967 = 8269451) B8269451
theorem B2449193 : Blo 1632515 2449193 := bstep (se 2 (by rfl) ⟨918447, by rfl⟩ : syracuseStep 2449193 = 1836895) B1836895
theorem B2449199 : Blo 1632515 2449199 := bstep (se 1 (by rfl) ⟨1836899, by rfl⟩ : syracuseStep 2449199 = 3673799) B3673799
theorem B6979385 : Blo 1632515 6979385 := bstep (se 2 (by rfl) ⟨2617269, by rfl⟩ : syracuseStep 6979385 = 5234539) B5234539
theorem B5586749 : Blo 1632515 5586749 := bstep (se 3 (by rfl) ⟨1047515, by rfl⟩ : syracuseStep 5586749 = 2095031) B2095031
theorem B5513021 : Blo 1632515 5513021 := bstep (se 3 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 5513021 = 2067383) B2067383
theorem B4652957 : Blo 1632515 4652957 := bstep (se 3 (by rfl) ⟨872429, by rfl⟩ : syracuseStep 4652957 = 1744859) B1744859
theorem B5587231 : Blo 1632515 5587231 := bstep (se 1 (by rfl) ⟨4190423, by rfl⟩ : syracuseStep 5587231 = 8380847) B8380847
theorem B2449871 : Blo 1632515 2449871 := bstep (se 1 (by rfl) ⟨1837403, by rfl⟩ : syracuseStep 2449871 = 3674807) B3674807
theorem B2449913 : Blo 1632515 2449913 := bstep (se 2 (by rfl) ⟨918717, by rfl⟩ : syracuseStep 2449913 = 1837435) B1837435
theorem B5513723 : Blo 1632515 5513723 := bstep (se 1 (by rfl) ⟨4135292, by rfl⟩ : syracuseStep 5513723 = 8270585) B8270585
theorem B2450015 : Blo 1632515 2450015 := bstep (se 1 (by rfl) ⟨1837511, by rfl⟩ : syracuseStep 2450015 = 3675023) B3675023
theorem B5513993 : Blo 1632515 5513993 := bstep (se 2 (by rfl) ⟨2067747, by rfl⟩ : syracuseStep 5513993 = 4135495) B4135495
theorem B11477771 : Blo 1632515 11477771 := bstep (se 1 (by rfl) ⟨8608328, by rfl⟩ : syracuseStep 11477771 = 17216657) B17216657
theorem B13951763 : Blo 1632515 13951763 := bstep (se 1 (by rfl) ⟨10463822, by rfl⟩ : syracuseStep 13951763 = 20927645) B20927645
theorem B7848751 : Blo 1632515 7848751 := bstep (se 1 (by rfl) ⟨5886563, by rfl⟩ : syracuseStep 7848751 = 11773127) B11773127
theorem B2450495 : Blo 1632515 2450495 := bstep (se 1 (by rfl) ⟨1837871, by rfl⟩ : syracuseStep 2450495 = 3675743) B3675743
theorem B2794559 : Blo 1632515 2794559 := bstep (se 1 (by rfl) ⟨2095919, by rfl⟩ : syracuseStep 2794559 = 4191839) B4191839
theorem B9299033 : Blo 1632515 9299033 := bstep (se 2 (by rfl) ⟨3487137, by rfl⟩ : syracuseStep 9299033 = 6974275) B6974275
theorem B2450537 : Blo 1632515 2450537 := bstep (se 2 (by rfl) ⟨918951, by rfl⟩ : syracuseStep 2450537 = 1837903) B1837903
theorem B2450639 : Blo 1632515 2450639 := bstep (se 1 (by rfl) ⟨1837979, by rfl⟩ : syracuseStep 2450639 = 3675959) B3675959
theorem B9430339 : Blo 1632515 9430339 := bstep (se 1 (by rfl) ⟨7072754, by rfl⟩ : syracuseStep 9430339 = 14145509) B14145509
theorem B2450843 : Blo 1632515 2450843 := bstep (se 1 (by rfl) ⟨1838132, by rfl⟩ : syracuseStep 2450843 = 3676265) B3676265
theorem B8267183 : Blo 1632515 8267183 := bstep (se 1 (by rfl) ⟨6200387, by rfl⟩ : syracuseStep 8267183 = 12400775) B12400775
theorem B5514749 : Blo 1632515 5514749 := bstep (se 3 (by rfl) ⟨1034015, by rfl⟩ : syracuseStep 5514749 = 2068031) B2068031
theorem B8267345 : Blo 1632515 8267345 := bstep (se 2 (by rfl) ⟨3100254, by rfl⟩ : syracuseStep 8267345 = 6200509) B6200509
theorem B226223873 : Blo 1632515 226223873 := bstep (se 2 (by rfl) ⟨84833952, by rfl⟩ : syracuseStep 226223873 = 169667905) B169667905
theorem B2066239 : Blo 1632515 2066239 := bstep (se 1 (by rfl) ⟨1549679, by rfl⟩ : syracuseStep 2066239 = 3099359) B3099359
theorem B20129633 : Blo 1632515 20129633 := bstep (se 2 (by rfl) ⟨7548612, by rfl⟩ : syracuseStep 20129633 = 15097225) B15097225
theorem B1837039 : Blo 1632515 1837039 := bstep (se 1 (by rfl) ⟨1377779, by rfl⟩ : syracuseStep 1837039 = 2755559) B2755559
theorem B1632559 : Blo 1632515 1632559 := bstep (se 1 (by rfl) ⟨1224419, by rfl⟩ : syracuseStep 1632559 = 2448839) B2448839
theorem B2066735 : Blo 1632515 2066735 := bstep (se 1 (by rfl) ⟨1550051, by rfl⟩ : syracuseStep 2066735 = 3100103) B3100103
theorem B12405149 : Blo 1632515 12405149 := bstep (se 3 (by rfl) ⟨2325965, by rfl⟩ : syracuseStep 12405149 = 4651931) B4651931
theorem B21801383 : Blo 1632515 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B35326475 : Blo 1632515 35326475 := bstep (se 1 (by rfl) ⟨26494856, by rfl⟩ : syracuseStep 35326475 = 52989713) B52989713
theorem B1632795 : Blo 1632515 1632795 := bstep (se 1 (by rfl) ⟨1224596, by rfl⟩ : syracuseStep 1632795 = 2449193) B2449193
theorem B1632799 : Blo 1632515 1632799 := bstep (se 1 (by rfl) ⟨1224599, by rfl⟩ : syracuseStep 1632799 = 2449199) B2449199
theorem B28297937 : Blo 1632515 28297937 := bstep (se 2 (by rfl) ⟨10611726, by rfl⟩ : syracuseStep 28297937 = 21223453) B21223453
theorem B1633115 : Blo 1632515 1633115 := bstep (se 1 (by rfl) ⟨1224836, by rfl⟩ : syracuseStep 1633115 = 2449673) B2449673
theorem B1633183 : Blo 1632515 1633183 := bstep (se 1 (by rfl) ⟨1224887, by rfl⟩ : syracuseStep 1633183 = 2449775) B2449775
theorem B17894317 : Blo 1632515 17894317 := bstep (se 3 (by rfl) ⟨3355184, by rfl⟩ : syracuseStep 17894317 = 6710369) B6710369
theorem B4967399 : Blo 1632515 4967399 := bstep (se 1 (by rfl) ⟨3725549, by rfl⟩ : syracuseStep 4967399 = 7451099) B7451099
theorem B1633327 : Blo 1632515 1633327 := bstep (se 1 (by rfl) ⟨1224995, by rfl⟩ : syracuseStep 1633327 = 2449991) B2449991
theorem B1633351 : Blo 1632515 1633351 := bstep (se 1 (by rfl) ⟨1225013, by rfl⟩ : syracuseStep 1633351 = 2450027) B2450027
theorem B48377033 : Blo 1632515 48377033 := bstep (se 2 (by rfl) ⟨18141387, by rfl⟩ : syracuseStep 48377033 = 36282775) B36282775
theorem B1633503 : Blo 1632515 1633503 := bstep (se 1 (by rfl) ⟨1225127, by rfl⟩ : syracuseStep 1633503 = 2450255) B2450255
theorem B2755849 : Blo 1632515 2755849 := bstep (se 2 (by rfl) ⟨1033443, by rfl⟩ : syracuseStep 2755849 = 2066887) B2066887
theorem B7851289 : Blo 1632515 7851289 := bstep (se 2 (by rfl) ⟨2944233, by rfl⟩ : syracuseStep 7851289 = 5888467) B5888467
theorem B7449965 : Blo 1632515 7449965 := bstep (se 3 (by rfl) ⟨1396868, by rfl⟩ : syracuseStep 7449965 = 2793737) B2793737
theorem B5967227 : Blo 1632515 5967227 := bstep (se 1 (by rfl) ⟨4475420, by rfl⟩ : syracuseStep 5967227 = 8950841) B8950841
theorem B9932215 : Blo 1632515 9932215 := bstep (se 1 (by rfl) ⟨7449161, by rfl⟩ : syracuseStep 9932215 = 14898323) B14898323
theorem B23858621 : Blo 1632515 23858621 := bstep (se 3 (by rfl) ⟨4473491, by rfl⟩ : syracuseStep 23858621 = 8946983) B8946983
theorem B1633767 : Blo 1632515 1633767 := bstep (se 1 (by rfl) ⟨1225325, by rfl⟩ : syracuseStep 1633767 = 2450651) B2450651
theorem B3673673 : Blo 1632515 3673673 := bstep (se 2 (by rfl) ⟨1377627, by rfl⟩ : syracuseStep 3673673 = 2755255) B2755255
theorem B1633883 : Blo 1632515 1633883 := bstep (se 1 (by rfl) ⟨1225412, by rfl⟩ : syracuseStep 1633883 = 2450825) B2450825
theorem B22351535 : Blo 1632515 22351535 := bstep (se 1 (by rfl) ⟨16763651, by rfl⟩ : syracuseStep 22351535 = 33527303) B33527303
theorem B2756423 : Blo 1632515 2756423 := bstep (se 1 (by rfl) ⟨2067317, by rfl⟩ : syracuseStep 2756423 = 4134635) B4134635
theorem B8269775 : Blo 1632515 8269775 := bstep (se 1 (by rfl) ⟨6202331, by rfl⟩ : syracuseStep 8269775 = 12404663) B12404663
theorem B5304307 : Blo 1632515 5304307 := bstep (se 1 (by rfl) ⟨3978230, by rfl⟩ : syracuseStep 5304307 = 7956461) B7956461
theorem B47747177 : Blo 1632515 47747177 := bstep (se 2 (by rfl) ⟨17905191, by rfl⟩ : syracuseStep 47747177 = 35810383) B35810383
theorem B5886217 : Blo 1632515 5886217 := bstep (se 2 (by rfl) ⟨2207331, by rfl⟩ : syracuseStep 5886217 = 4414663) B4414663
theorem B2757071 : Blo 1632515 2757071 := bstep (se 1 (by rfl) ⟨2067803, by rfl⟩ : syracuseStep 2757071 = 4135607) B4135607
theorem B4133369 : Blo 1632515 4133369 := bstep (se 2 (by rfl) ⟨1550013, by rfl⟩ : syracuseStep 4133369 = 3100027) B3100027
theorem B5034743 : Blo 1632515 5034743 := bstep (se 1 (by rfl) ⟨3776057, by rfl⟩ : syracuseStep 5034743 = 7552115) B7552115
theorem B3675131 : Blo 1632515 3675131 := bstep (se 1 (by rfl) ⟨2756348, by rfl⟩ : syracuseStep 3675131 = 5512697) B5512697
theorem B6976651 : Blo 1632515 6976651 := bstep (se 1 (by rfl) ⟨5232488, by rfl⟩ : syracuseStep 6976651 = 10464977) B10464977
theorem B3675311 : Blo 1632515 3675311 := bstep (se 1 (by rfl) ⟨2756483, by rfl⟩ : syracuseStep 3675311 = 5512967) B5512967
theorem B3724499 : Blo 1632515 3724499 := bstep (se 1 (by rfl) ⟨2793374, by rfl⟩ : syracuseStep 3724499 = 5586749) B5586749
theorem B3675347 : Blo 1632515 3675347 := bstep (se 1 (by rfl) ⟨2756510, by rfl⟩ : syracuseStep 3675347 = 5513021) B5513021
theorem B3101971 : Blo 1632515 3101971 := bstep (se 1 (by rfl) ⟨2326478, by rfl⟩ : syracuseStep 3101971 = 4652957) B4652957
theorem B15103361 : Blo 1632515 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B8271233 : Blo 1632515 8271233 := bstep (se 2 (by rfl) ⟨3101712, by rfl⟩ : syracuseStep 8271233 = 6203425) B6203425
theorem B3675617 : Blo 1632515 3675617 := bstep (se 2 (by rfl) ⟨1378356, by rfl⟩ : syracuseStep 3675617 = 2756713) B2756713
theorem B7452371 : Blo 1632515 7452371 := bstep (se 1 (by rfl) ⟨5589278, by rfl⟩ : syracuseStep 7452371 = 11178557) B11178557
theorem B6199051 : Blo 1632515 6199051 := bstep (se 1 (by rfl) ⟨4649288, by rfl⟩ : syracuseStep 6199051 = 9298577) B9298577
theorem B5510969 : Blo 1632515 5510969 := bstep (se 2 (by rfl) ⟨2066613, by rfl⟩ : syracuseStep 5510969 = 4133227) B4133227
theorem B5511131 : Blo 1632515 5511131 := bstep (se 1 (by rfl) ⟨4133348, by rfl⟩ : syracuseStep 5511131 = 8266697) B8266697
theorem B4192249 : Blo 1632515 4192249 := bstep (se 2 (by rfl) ⟨1572093, by rfl⟩ : syracuseStep 4192249 = 3144187) B3144187
theorem B22354001 : Blo 1632515 22354001 := bstep (se 2 (by rfl) ⟨8382750, by rfl⟩ : syracuseStep 22354001 = 16765501) B16765501
theorem B4135009 : Blo 1632515 4135009 := bstep (se 2 (by rfl) ⟨1550628, by rfl⟩ : syracuseStep 4135009 = 3101257) B3101257
theorem B8272043 : Blo 1632515 8272043 := bstep (se 1 (by rfl) ⟨6204032, by rfl⟩ : syracuseStep 8272043 = 12408065) B12408065
theorem B2324713 : Blo 1632515 2324713 := bstep (se 2 (by rfl) ⟨871767, by rfl⟩ : syracuseStep 2324713 = 1743535) B1743535
theorem B5511401 : Blo 1632515 5511401 := bstep (se 2 (by rfl) ⟨2066775, by rfl⟩ : syracuseStep 5511401 = 4133551) B4133551
theorem B4413703 : Blo 1632515 4413703 := bstep (se 1 (by rfl) ⟨3310277, by rfl⟩ : syracuseStep 4413703 = 6620555) B6620555
theorem B11770127 : Blo 1632515 11770127 := bstep (se 1 (by rfl) ⟨8827595, by rfl⟩ : syracuseStep 11770127 = 17655191) B17655191
theorem B5232937 : Blo 1632515 5232937 := bstep (se 2 (by rfl) ⟨1962351, by rfl⟩ : syracuseStep 5232937 = 3924703) B3924703
theorem B5511833 : Blo 1632515 5511833 := bstep (se 2 (by rfl) ⟨2066937, by rfl⟩ : syracuseStep 5511833 = 4133875) B4133875
theorem B11770589 : Blo 1632515 11770589 := bstep (se 3 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 11770589 = 4413971) B4413971
theorem B76454765 : Blo 1632515 76454765 := bstep (se 3 (by rfl) ⟨14335268, by rfl⟩ : syracuseStep 76454765 = 28670537) B28670537
theorem B10460285 : Blo 1632515 10460285 := bstep (se 3 (by rfl) ⟨1961303, by rfl⟩ : syracuseStep 10460285 = 3922607) B3922607
theorem B11771027 : Blo 1632515 11771027 := bstep (se 1 (by rfl) ⟨8828270, by rfl⟩ : syracuseStep 11771027 = 17656541) B17656541
theorem B2448809 : Blo 1632515 2448809 := bstep (se 2 (by rfl) ⟨918303, by rfl⟩ : syracuseStep 2448809 = 1836607) B1836607
theorem B2448959 : Blo 1632515 2448959 := bstep (se 1 (by rfl) ⟨1836719, by rfl⟩ : syracuseStep 2448959 = 3673439) B3673439
theorem B9305867 : Blo 1632515 9305867 := bstep (se 1 (by rfl) ⟨6979400, by rfl⟩ : syracuseStep 9305867 = 13958801) B13958801
theorem B2449223 : Blo 1632515 2449223 := bstep (se 1 (by rfl) ⟨1836917, by rfl⟩ : syracuseStep 2449223 = 3673835) B3673835
theorem B4652923 : Blo 1632515 4652923 := bstep (se 1 (by rfl) ⟨3489692, by rfl⟩ : syracuseStep 4652923 = 6979385) B6979385
theorem B2449307 : Blo 1632515 2449307 := bstep (se 1 (by rfl) ⟨1836980, by rfl⟩ : syracuseStep 2449307 = 3673961) B3673961
theorem B5513345 : Blo 1632515 5513345 := bstep (se 2 (by rfl) ⟨2067504, by rfl⟩ : syracuseStep 5513345 = 4135009) B4135009
theorem B7848289 : Blo 1632515 7848289 := bstep (se 2 (by rfl) ⟨2943108, by rfl⟩ : syracuseStep 7848289 = 5886217) B5886217
theorem B7651847 : Blo 1632515 7651847 := bstep (se 1 (by rfl) ⟨5738885, by rfl⟩ : syracuseStep 7651847 = 11477771) B11477771
theorem B2450087 : Blo 1632515 2450087 := bstep (se 1 (by rfl) ⟨1837565, by rfl⟩ : syracuseStep 2450087 = 3675131) B3675131
theorem B2450207 : Blo 1632515 2450207 := bstep (se 1 (by rfl) ⟨1837655, by rfl⟩ : syracuseStep 2450207 = 3675311) B3675311
theorem B2450231 : Blo 1632515 2450231 := bstep (se 1 (by rfl) ⟨1837673, by rfl⟩ : syracuseStep 2450231 = 3675347) B3675347
theorem B10068907 : Blo 1632515 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B5514155 : Blo 1632515 5514155 := bstep (se 1 (by rfl) ⟨4135616, by rfl⟩ : syracuseStep 5514155 = 8271233) B8271233
theorem B2450411 : Blo 1632515 2450411 := bstep (se 1 (by rfl) ⟨1837808, by rfl⟩ : syracuseStep 2450411 = 3675617) B3675617
theorem B150815915 : Blo 1632515 150815915 := bstep (se 1 (by rfl) ⟨113111936, by rfl⟩ : syracuseStep 150815915 = 226223873) B226223873
theorem B13419755 : Blo 1632515 13419755 := bstep (se 1 (by rfl) ⟨10064816, by rfl⟩ : syracuseStep 13419755 = 20129633) B20129633
theorem B14902667 : Blo 1632515 14902667 := bstep (se 1 (by rfl) ⟨11177000, by rfl⟩ : syracuseStep 14902667 = 22354001) B22354001
theorem B5514695 : Blo 1632515 5514695 := bstep (se 1 (by rfl) ⟨4136021, by rfl⟩ : syracuseStep 5514695 = 8272043) B8272043
theorem B14534255 : Blo 1632515 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B3311599 : Blo 1632515 3311599 := bstep (se 1 (by rfl) ⟨2483699, by rfl⟩ : syracuseStep 3311599 = 4967399) B4967399
theorem B6973523 : Blo 1632515 6973523 := bstep (se 1 (by rfl) ⟨5230142, by rfl⟩ : syracuseStep 6973523 = 10460285) B10460285
theorem B4966643 : Blo 1632515 4966643 := bstep (se 1 (by rfl) ⟨3724982, by rfl⟩ : syracuseStep 4966643 = 7449965) B7449965
theorem B1632539 : Blo 1632515 1632539 := bstep (se 1 (by rfl) ⟨1224404, by rfl⟩ : syracuseStep 1632539 = 2448809) B2448809
theorem B1632639 : Blo 1632515 1632639 := bstep (se 1 (by rfl) ⟨1224479, by rfl⟩ : syracuseStep 1632639 = 2448959) B2448959
theorem B2754985 : Blo 1632515 2754985 := bstep (se 2 (by rfl) ⟨1033119, by rfl⟩ : syracuseStep 2754985 = 2066239) B2066239
theorem B6203897 : Blo 1632515 6203897 := bstep (se 2 (by rfl) ⟨2326461, by rfl⟩ : syracuseStep 6203897 = 4652923) B4652923
theorem B6203911 : Blo 1632515 6203911 := bstep (se 1 (by rfl) ⟨4652933, by rfl⟩ : syracuseStep 6203911 = 9305867) B9305867
theorem B1632815 : Blo 1632515 1632815 := bstep (se 1 (by rfl) ⟨1224611, by rfl⟩ : syracuseStep 1632815 = 2449223) B2449223
theorem B1837615 : Blo 1632515 1837615 := bstep (se 1 (by rfl) ⟨1378211, by rfl⟩ : syracuseStep 1837615 = 2756423) B2756423
theorem B1632871 : Blo 1632515 1632871 := bstep (se 1 (by rfl) ⟨1224653, by rfl⟩ : syracuseStep 1632871 = 2449307) B2449307
theorem B7072409 : Blo 1632515 7072409 := bstep (se 2 (by rfl) ⟨2652153, by rfl⟩ : syracuseStep 7072409 = 5304307) B5304307
theorem B5589665 : Blo 1632515 5589665 := bstep (se 2 (by rfl) ⟨2096124, by rfl⟩ : syracuseStep 5589665 = 4192249) B4192249
theorem B1633247 : Blo 1632515 1633247 := bstep (se 1 (by rfl) ⟨1224935, by rfl⟩ : syracuseStep 1633247 = 2449871) B2449871
theorem B1838047 : Blo 1632515 1838047 := bstep (se 1 (by rfl) ⟨1378535, by rfl⟩ : syracuseStep 1838047 = 2757071) B2757071
theorem B3099617 : Blo 1632515 3099617 := bstep (se 2 (by rfl) ⟨1162356, by rfl⟩ : syracuseStep 3099617 = 2324713) B2324713
theorem B2755579 : Blo 1632515 2755579 := bstep (se 1 (by rfl) ⟨2066684, by rfl⟩ : syracuseStep 2755579 = 4133369) B4133369
theorem B1633275 : Blo 1632515 1633275 := bstep (se 1 (by rfl) ⟨1224956, by rfl⟩ : syracuseStep 1633275 = 2449913) B2449913
theorem B5884937 : Blo 1632515 5884937 := bstep (se 2 (by rfl) ⟨2206851, by rfl⟩ : syracuseStep 5884937 = 4413703) B4413703
theorem B7449641 : Blo 1632515 7449641 := bstep (se 2 (by rfl) ⟨2793615, by rfl⟩ : syracuseStep 7449641 = 5587231) B5587231
theorem B1633343 : Blo 1632515 1633343 := bstep (se 1 (by rfl) ⟨1225007, by rfl⟩ : syracuseStep 1633343 = 2450015) B2450015
theorem B9301175 : Blo 1632515 9301175 := bstep (se 1 (by rfl) ⟨6975881, by rfl⟩ : syracuseStep 9301175 = 13951763) B13951763
theorem B9931997 : Blo 1632515 9931997 := bstep (se 3 (by rfl) ⟨1862249, by rfl⟩ : syracuseStep 9931997 = 3724499) B3724499
theorem B1633663 : Blo 1632515 1633663 := bstep (se 1 (by rfl) ⟨1225247, by rfl⟩ : syracuseStep 1633663 = 2450495) B2450495
theorem B1633691 : Blo 1632515 1633691 := bstep (se 1 (by rfl) ⟨1225268, by rfl⟩ : syracuseStep 1633691 = 2450537) B2450537
theorem B1633759 : Blo 1632515 1633759 := bstep (se 1 (by rfl) ⟨1225319, by rfl⟩ : syracuseStep 1633759 = 2450639) B2450639
theorem B1633895 : Blo 1632515 1633895 := bstep (se 1 (by rfl) ⟨1225421, by rfl⟩ : syracuseStep 1633895 = 2450843) B2450843
theorem B15912605 : Blo 1632515 15912605 := bstep (se 3 (by rfl) ⟨2983613, by rfl⟩ : syracuseStep 15912605 = 5967227) B5967227
theorem B10465001 : Blo 1632515 10465001 := bstep (se 2 (by rfl) ⟨3924375, by rfl⟩ : syracuseStep 10465001 = 7848751) B7848751
theorem B3673979 : Blo 1632515 3673979 := bstep (se 1 (by rfl) ⟨2755484, by rfl⟩ : syracuseStep 3673979 = 5510969) B5510969
theorem B23859089 : Blo 1632515 23859089 := bstep (se 2 (by rfl) ⟨8947158, by rfl⟩ : syracuseStep 23859089 = 17894317) B17894317
theorem B3674087 : Blo 1632515 3674087 := bstep (se 1 (by rfl) ⟨2755565, by rfl⟩ : syracuseStep 3674087 = 5511131) B5511131
theorem B3674267 : Blo 1632515 3674267 := bstep (se 1 (by rfl) ⟨2755700, by rfl⟩ : syracuseStep 3674267 = 5511401) B5511401
theorem B9302201 : Blo 1632515 9302201 := bstep (se 2 (by rfl) ⟨3488325, by rfl⟩ : syracuseStep 9302201 = 6976651) B6976651
theorem B8270099 : Blo 1632515 8270099 := bstep (se 1 (by rfl) ⟨6202574, by rfl⟩ : syracuseStep 8270099 = 12405149) B12405149
theorem B3674465 : Blo 1632515 3674465 := bstep (se 2 (by rfl) ⟨1377924, by rfl⟩ : syracuseStep 3674465 = 2755849) B2755849
theorem B3674555 : Blo 1632515 3674555 := bstep (se 1 (by rfl) ⟨2755916, by rfl⟩ : syracuseStep 3674555 = 5511833) B5511833
theorem B75461165 : Blo 1632515 75461165 := bstep (se 3 (by rfl) ⟨14148968, by rfl⟩ : syracuseStep 75461165 = 28297937) B28297937
theorem B13242953 : Blo 1632515 13242953 := bstep (se 2 (by rfl) ⟨4966107, by rfl⟩ : syracuseStep 13242953 = 9932215) B9932215
theorem B15905747 : Blo 1632515 15905747 := bstep (se 1 (by rfl) ⟨11929310, by rfl⟩ : syracuseStep 15905747 = 23858621) B23858621
theorem B31831451 : Blo 1632515 31831451 := bstep (se 1 (by rfl) ⟨23873588, by rfl⟩ : syracuseStep 31831451 = 47747177) B47747177
theorem B7452157 : Blo 1632515 7452157 := bstep (se 3 (by rfl) ⟨1397279, by rfl⟩ : syracuseStep 7452157 = 2794559) B2794559
theorem B3675815 : Blo 1632515 3675815 := bstep (se 1 (by rfl) ⟨2756861, by rfl⟩ : syracuseStep 3675815 = 5513723) B5513723
theorem B6977249 : Blo 1632515 6977249 := bstep (se 2 (by rfl) ⟨2616468, by rfl⟩ : syracuseStep 6977249 = 5232937) B5232937
theorem B3356495 : Blo 1632515 3356495 := bstep (se 1 (by rfl) ⟨2517371, by rfl⟩ : syracuseStep 3356495 = 5034743) B5034743
theorem B3675995 : Blo 1632515 3675995 := bstep (se 1 (by rfl) ⟨2756996, by rfl⟩ : syracuseStep 3675995 = 5513993) B5513993
theorem B6199355 : Blo 1632515 6199355 := bstep (se 1 (by rfl) ⟨4649516, by rfl⟩ : syracuseStep 6199355 = 9299033) B9299033
theorem B5511293 : Blo 1632515 5511293 := bstep (se 3 (by rfl) ⟨1033367, by rfl⟩ : syracuseStep 5511293 = 2066735) B2066735
theorem B5511455 : Blo 1632515 5511455 := bstep (se 1 (by rfl) ⟨4133591, by rfl⟩ : syracuseStep 5511455 = 8267183) B8267183
theorem B3676499 : Blo 1632515 3676499 := bstep (se 1 (by rfl) ⟨2757374, by rfl⟩ : syracuseStep 3676499 = 5514749) B5514749
theorem B5511563 : Blo 1632515 5511563 := bstep (se 1 (by rfl) ⟨4133672, by rfl⟩ : syracuseStep 5511563 = 8267345) B8267345
theorem B7846751 : Blo 1632515 7846751 := bstep (se 1 (by rfl) ⟨5885063, by rfl⟩ : syracuseStep 7846751 = 11770127) B11770127
theorem B23550983 : Blo 1632515 23550983 := bstep (se 1 (by rfl) ⟨17663237, by rfl⟩ : syracuseStep 23550983 = 35326475) B35326475
theorem B4135961 : Blo 1632515 4135961 := bstep (se 2 (by rfl) ⟨1550985, by rfl⟩ : syracuseStep 4135961 = 3101971) B3101971
theorem B10468385 : Blo 1632515 10468385 := bstep (se 2 (by rfl) ⟨3925644, by rfl⟩ : syracuseStep 10468385 = 7851289) B7851289
theorem B12573785 : Blo 1632515 12573785 := bstep (se 2 (by rfl) ⟨4715169, by rfl⟩ : syracuseStep 12573785 = 9430339) B9430339
theorem B7847059 : Blo 1632515 7847059 := bstep (se 1 (by rfl) ⟨5885294, by rfl⟩ : syracuseStep 7847059 = 11770589) B11770589
theorem B19872989 : Blo 1632515 19872989 := bstep (se 3 (by rfl) ⟨3726185, by rfl⟩ : syracuseStep 19872989 = 7452371) B7452371
theorem B50969843 : Blo 1632515 50969843 := bstep (se 1 (by rfl) ⟨38227382, by rfl⟩ : syracuseStep 50969843 = 76454765) B76454765
theorem B7847351 : Blo 1632515 7847351 := bstep (se 1 (by rfl) ⟨5885513, by rfl⟩ : syracuseStep 7847351 = 11771027) B11771027
theorem B32251355 : Blo 1632515 32251355 := bstep (se 1 (by rfl) ⟨24188516, by rfl⟩ : syracuseStep 32251355 = 48377033) B48377033
theorem B8265401 : Blo 1632515 8265401 := bstep (se 2 (by rfl) ⟨3099525, by rfl⟩ : syracuseStep 8265401 = 6199051) B6199051
theorem B2449115 : Blo 1632515 2449115 := bstep (se 1 (by rfl) ⟨1836836, by rfl⟩ : syracuseStep 2449115 = 3673673) B3673673
theorem B14901023 : Blo 1632515 14901023 := bstep (se 1 (by rfl) ⟨11175767, by rfl⟩ : syracuseStep 14901023 = 22351535) B22351535
theorem B5513183 : Blo 1632515 5513183 := bstep (se 1 (by rfl) ⟨4134887, by rfl⟩ : syracuseStep 5513183 = 8269775) B8269775
theorem B2449385 : Blo 1632515 2449385 := bstep (se 2 (by rfl) ⟨918519, by rfl⟩ : syracuseStep 2449385 = 1837039) B1837039
theorem B2449511 : Blo 1632515 2449511 := bstep (se 1 (by rfl) ⟨1837133, by rfl⟩ : syracuseStep 2449511 = 3674267) B3674267
theorem B6201467 : Blo 1632515 6201467 := bstep (se 1 (by rfl) ⟨4651100, by rfl⟩ : syracuseStep 6201467 = 9302201) B9302201
theorem B5513399 : Blo 1632515 5513399 := bstep (se 1 (by rfl) ⟨4135049, by rfl⟩ : syracuseStep 5513399 = 8270099) B8270099
theorem B2449643 : Blo 1632515 2449643 := bstep (se 1 (by rfl) ⟨1837232, by rfl⟩ : syracuseStep 2449643 = 3674465) B3674465
theorem B2449703 : Blo 1632515 2449703 := bstep (se 1 (by rfl) ⟨1837277, by rfl⟩ : syracuseStep 2449703 = 3674555) B3674555
theorem B50307443 : Blo 1632515 50307443 := bstep (se 1 (by rfl) ⟨37730582, by rfl⟩ : syracuseStep 50307443 = 75461165) B75461165
theorem B2450153 : Blo 1632515 2450153 := bstep (se 2 (by rfl) ⟨918807, by rfl⟩ : syracuseStep 2450153 = 1837615) B1837615
theorem B8946503 : Blo 1632515 8946503 := bstep (se 1 (by rfl) ⟨6709877, by rfl⟩ : syracuseStep 8946503 = 13419755) B13419755
theorem B2450543 : Blo 1632515 2450543 := bstep (se 1 (by rfl) ⟨1837907, by rfl⟩ : syracuseStep 2450543 = 3675815) B3675815
theorem B2237663 : Blo 1632515 2237663 := bstep (se 1 (by rfl) ⟨1678247, by rfl⟩ : syracuseStep 2237663 = 3356495) B3356495
theorem B2450663 : Blo 1632515 2450663 := bstep (se 1 (by rfl) ⟨1837997, by rfl⟩ : syracuseStep 2450663 = 3675995) B3675995
theorem B2450729 : Blo 1632515 2450729 := bstep (se 2 (by rfl) ⟨919023, by rfl⟩ : syracuseStep 2450729 = 1838047) B1838047
theorem B10462745 : Blo 1632515 10462745 := bstep (se 2 (by rfl) ⟨3923529, by rfl⟩ : syracuseStep 10462745 = 7847059) B7847059
theorem B2450999 : Blo 1632515 2450999 := bstep (se 1 (by rfl) ⟨1838249, by rfl⟩ : syracuseStep 2450999 = 3676499) B3676499
theorem B2066411 : Blo 1632515 2066411 := bstep (se 1 (by rfl) ⟨1549808, by rfl⟩ : syracuseStep 2066411 = 3099617) B3099617
theorem B4966427 : Blo 1632515 4966427 := bstep (se 1 (by rfl) ⟨3724820, by rfl⟩ : syracuseStep 4966427 = 7449641) B7449641
theorem B8382523 : Blo 1632515 8382523 := bstep (se 1 (by rfl) ⟨6286892, by rfl⟩ : syracuseStep 8382523 = 12573785) B12573785
theorem B6621331 : Blo 1632515 6621331 := bstep (se 1 (by rfl) ⟨4965998, by rfl⟩ : syracuseStep 6621331 = 9931997) B9931997
theorem B13248659 : Blo 1632515 13248659 := bstep (se 1 (by rfl) ⟨9936494, by rfl⟩ : syracuseStep 13248659 = 19872989) B19872989
theorem B20924669 : Blo 1632515 20924669 := bstep (se 3 (by rfl) ⟨3923375, by rfl⟩ : syracuseStep 20924669 = 7846751) B7846751
theorem B1632743 : Blo 1632515 1632743 := bstep (se 1 (by rfl) ⟨1224557, by rfl⟩ : syracuseStep 1632743 = 2449115) B2449115
theorem B1632923 : Blo 1632515 1632923 := bstep (se 1 (by rfl) ⟨1224692, by rfl⟩ : syracuseStep 1632923 = 2449385) B2449385
theorem B1633391 : Blo 1632515 1633391 := bstep (se 1 (by rfl) ⟨1225043, by rfl⟩ : syracuseStep 1633391 = 2450087) B2450087
theorem B10464385 : Blo 1632515 10464385 := bstep (se 2 (by rfl) ⟨3924144, by rfl⟩ : syracuseStep 10464385 = 7848289) B7848289
theorem B1633471 : Blo 1632515 1633471 := bstep (se 1 (by rfl) ⟨1225103, by rfl⟩ : syracuseStep 1633471 = 2450207) B2450207
theorem B1633487 : Blo 1632515 1633487 := bstep (se 1 (by rfl) ⟨1225115, by rfl⟩ : syracuseStep 1633487 = 2450231) B2450231
theorem B3673313 : Blo 1632515 3673313 := bstep (se 2 (by rfl) ⟨1377492, by rfl⟩ : syracuseStep 3673313 = 2754985) B2754985
theorem B10603831 : Blo 1632515 10603831 := bstep (se 1 (by rfl) ⟨7952873, by rfl⟩ : syracuseStep 10603831 = 15905747) B15905747
theorem B1633607 : Blo 1632515 1633607 := bstep (se 1 (by rfl) ⟨1225205, by rfl⟩ : syracuseStep 1633607 = 2450411) B2450411
theorem B100543943 : Blo 1632515 100543943 := bstep (se 1 (by rfl) ⟨75407957, by rfl⟩ : syracuseStep 100543943 = 150815915) B150815915
theorem B21220967 : Blo 1632515 21220967 := bstep (se 1 (by rfl) ⟨15915725, by rfl⟩ : syracuseStep 21220967 = 31831451) B31831451
theorem B3674105 : Blo 1632515 3674105 := bstep (se 2 (by rfl) ⟨1377789, by rfl⟩ : syracuseStep 3674105 = 2755579) B2755579
theorem B4132903 : Blo 1632515 4132903 := bstep (se 1 (by rfl) ⟨3099677, by rfl⟩ : syracuseStep 4132903 = 6199355) B6199355
theorem B4649015 : Blo 1632515 4649015 := bstep (se 1 (by rfl) ⟨3486761, by rfl⟩ : syracuseStep 4649015 = 6973523) B6973523
theorem B3674195 : Blo 1632515 3674195 := bstep (se 1 (by rfl) ⟨2755646, by rfl⟩ : syracuseStep 3674195 = 5511293) B5511293
theorem B3674303 : Blo 1632515 3674303 := bstep (se 1 (by rfl) ⟨2755727, by rfl⟩ : syracuseStep 3674303 = 5511455) B5511455
theorem B3674375 : Blo 1632515 3674375 := bstep (se 1 (by rfl) ⟨2755781, by rfl⟩ : syracuseStep 3674375 = 5511563) B5511563
theorem B4714939 : Blo 1632515 4714939 := bstep (se 1 (by rfl) ⟨3536204, by rfl⟩ : syracuseStep 4714939 = 7072409) B7072409
theorem B15700655 : Blo 1632515 15700655 := bstep (se 1 (by rfl) ⟨11775491, by rfl⟩ : syracuseStep 15700655 = 23550983) B23550983
theorem B2757307 : Blo 1632515 2757307 := bstep (se 1 (by rfl) ⟨2067980, by rfl⟩ : syracuseStep 2757307 = 4135961) B4135961
theorem B5231567 : Blo 1632515 5231567 := bstep (se 1 (by rfl) ⟨3923675, by rfl⟩ : syracuseStep 5231567 = 7847351) B7847351
theorem B21500903 : Blo 1632515 21500903 := bstep (se 1 (by rfl) ⟨16125677, by rfl⟩ : syracuseStep 21500903 = 32251355) B32251355
theorem B5510267 : Blo 1632515 5510267 := bstep (se 1 (by rfl) ⟨4132700, by rfl⟩ : syracuseStep 5510267 = 8265401) B8265401
theorem B6976667 : Blo 1632515 6976667 := bstep (se 1 (by rfl) ⟨5232500, by rfl⟩ : syracuseStep 6976667 = 10465001) B10465001
theorem B9934015 : Blo 1632515 9934015 := bstep (se 1 (by rfl) ⟨7450511, by rfl⟩ : syracuseStep 9934015 = 14901023) B14901023
theorem B15906059 : Blo 1632515 15906059 := bstep (se 1 (by rfl) ⟨11929544, by rfl⟩ : syracuseStep 15906059 = 23859089) B23859089
theorem B3675455 : Blo 1632515 3675455 := bstep (se 1 (by rfl) ⟨2756591, by rfl⟩ : syracuseStep 3675455 = 5513183) B5513183
theorem B3675563 : Blo 1632515 3675563 := bstep (se 1 (by rfl) ⟨2756672, by rfl⟩ : syracuseStep 3675563 = 5513345) B5513345
theorem B5101231 : Blo 1632515 5101231 := bstep (se 1 (by rfl) ⟨3825923, by rfl⟩ : syracuseStep 5101231 = 7651847) B7651847
theorem B8828635 : Blo 1632515 8828635 := bstep (se 1 (by rfl) ⟨6621476, by rfl⟩ : syracuseStep 8828635 = 13242953) B13242953
theorem B3676103 : Blo 1632515 3676103 := bstep (se 1 (by rfl) ⟨2757077, by rfl⟩ : syracuseStep 3676103 = 5514155) B5514155
theorem B13244381 : Blo 1632515 13244381 := bstep (se 3 (by rfl) ⟨2483321, by rfl⟩ : syracuseStep 13244381 = 4966643) B4966643
theorem B8271881 : Blo 1632515 8271881 := bstep (se 2 (by rfl) ⟨3101955, by rfl⟩ : syracuseStep 8271881 = 6203911) B6203911
theorem B9935111 : Blo 1632515 9935111 := bstep (se 1 (by rfl) ⟨7451333, by rfl⟩ : syracuseStep 9935111 = 14902667) B14902667
theorem B3676463 : Blo 1632515 3676463 := bstep (se 1 (by rfl) ⟨2757347, by rfl⟩ : syracuseStep 3676463 = 5514695) B5514695
theorem B9689503 : Blo 1632515 9689503 := bstep (se 1 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 9689503 = 14534255) B14534255
theorem B4651499 : Blo 1632515 4651499 := bstep (se 1 (by rfl) ⟨3488624, by rfl⟩ : syracuseStep 4651499 = 6977249) B6977249
theorem B13425209 : Blo 1632515 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B4135931 : Blo 1632515 4135931 := bstep (se 1 (by rfl) ⟨3101948, by rfl⟩ : syracuseStep 4135931 = 6203897) B6203897
theorem B3726443 : Blo 1632515 3726443 := bstep (se 1 (by rfl) ⟨2794832, by rfl⟩ : syracuseStep 3726443 = 5589665) B5589665
theorem B9936209 : Blo 1632515 9936209 := bstep (se 2 (by rfl) ⟨3726078, by rfl⟩ : syracuseStep 9936209 = 7452157) B7452157
theorem B3923291 : Blo 1632515 3923291 := bstep (se 1 (by rfl) ⟨2942468, by rfl⟩ : syracuseStep 3923291 = 5884937) B5884937
theorem B6978923 : Blo 1632515 6978923 := bstep (se 1 (by rfl) ⟨5234192, by rfl⟩ : syracuseStep 6978923 = 10468385) B10468385
theorem B6200783 : Blo 1632515 6200783 := bstep (se 1 (by rfl) ⟨4650587, by rfl⟩ : syracuseStep 6200783 = 9301175) B9301175
theorem B33979895 : Blo 1632515 33979895 := bstep (se 1 (by rfl) ⟨25484921, by rfl⟩ : syracuseStep 33979895 = 50969843) B50969843
theorem B10608403 : Blo 1632515 10608403 := bstep (se 1 (by rfl) ⟨7956302, by rfl⟩ : syracuseStep 10608403 = 15912605) B15912605
theorem B2449319 : Blo 1632515 2449319 := bstep (se 1 (by rfl) ⟨1836989, by rfl⟩ : syracuseStep 2449319 = 3673979) B3673979
theorem B4415465 : Blo 1632515 4415465 := bstep (se 2 (by rfl) ⟨1655799, by rfl⟩ : syracuseStep 4415465 = 3311599) B3311599
theorem B2449391 : Blo 1632515 2449391 := bstep (se 1 (by rfl) ⟨1837043, by rfl⟩ : syracuseStep 2449391 = 3674087) B3674087
theorem B2449463 : Blo 1632515 2449463 := bstep (se 1 (by rfl) ⟨1837097, by rfl⟩ : syracuseStep 2449463 = 3674195) B3674195
theorem B2449535 : Blo 1632515 2449535 := bstep (se 1 (by rfl) ⟨1837151, by rfl⟩ : syracuseStep 2449535 = 3674303) B3674303
theorem B2449583 : Blo 1632515 2449583 := bstep (se 1 (by rfl) ⟨1837187, by rfl⟩ : syracuseStep 2449583 = 3674375) B3674375
theorem B33538295 : Blo 1632515 33538295 := bstep (se 1 (by rfl) ⟨25153721, by rfl⟩ : syracuseStep 33538295 = 50307443) B50307443
theorem B9937181 : Blo 1632515 9937181 := bstep (se 3 (by rfl) ⟨1863221, by rfl⟩ : syracuseStep 9937181 = 3726443) B3726443
theorem B12919337 : Blo 1632515 12919337 := bstep (se 2 (by rfl) ⟨4844751, by rfl⟩ : syracuseStep 12919337 = 9689503) B9689503
theorem B5964335 : Blo 1632515 5964335 := bstep (se 1 (by rfl) ⟨4473251, by rfl⟩ : syracuseStep 5964335 = 8946503) B8946503
theorem B2450303 : Blo 1632515 2450303 := bstep (se 1 (by rfl) ⟨1837727, by rfl⟩ : syracuseStep 2450303 = 3675455) B3675455
theorem B2450375 : Blo 1632515 2450375 := bstep (se 1 (by rfl) ⟨1837781, by rfl⟩ : syracuseStep 2450375 = 3675563) B3675563
theorem B2450735 : Blo 1632515 2450735 := bstep (se 1 (by rfl) ⟨1838051, by rfl⟩ : syracuseStep 2450735 = 3676103) B3676103
theorem B5514587 : Blo 1632515 5514587 := bstep (se 1 (by rfl) ⟨4135940, by rfl⟩ : syracuseStep 5514587 = 8271881) B8271881
theorem B3310951 : Blo 1632515 3310951 := bstep (se 1 (by rfl) ⟨2483213, by rfl⟩ : syracuseStep 3310951 = 4966427) B4966427
theorem B8832439 : Blo 1632515 8832439 := bstep (se 1 (by rfl) ⟨6624329, by rfl⟩ : syracuseStep 8832439 = 13248659) B13248659
theorem B13952513 : Blo 1632515 13952513 := bstep (se 2 (by rfl) ⟨5232192, by rfl⟩ : syracuseStep 13952513 = 10464385) B10464385
theorem B2450975 : Blo 1632515 2450975 := bstep (se 1 (by rfl) ⟨1838231, by rfl⟩ : syracuseStep 2450975 = 3676463) B3676463
theorem B2615527 : Blo 1632515 2615527 := bstep (se 1 (by rfl) ⟨1961645, by rfl⟩ : syracuseStep 2615527 = 3923291) B3923291
theorem B6801641 : Blo 1632515 6801641 := bstep (se 2 (by rfl) ⟨2550615, by rfl⟩ : syracuseStep 6801641 = 5101231) B5101231
theorem B67029295 : Blo 1632515 67029295 := bstep (se 1 (by rfl) ⟨50271971, by rfl⟩ : syracuseStep 67029295 = 100543943) B100543943
theorem B22653263 : Blo 1632515 22653263 := bstep (se 1 (by rfl) ⟨16989947, by rfl⟩ : syracuseStep 22653263 = 33979895) B33979895
theorem B1632879 : Blo 1632515 1632879 := bstep (se 1 (by rfl) ⟨1224659, by rfl⟩ : syracuseStep 1632879 = 2449319) B2449319
theorem B2943643 : Blo 1632515 2943643 := bstep (se 1 (by rfl) ⟨2207732, by rfl⟩ : syracuseStep 2943643 = 4415465) B4415465
theorem B1632927 : Blo 1632515 1632927 := bstep (se 1 (by rfl) ⟨1224695, by rfl⟩ : syracuseStep 1632927 = 2449391) B2449391
theorem B1633007 : Blo 1632515 1633007 := bstep (se 1 (by rfl) ⟨1224755, by rfl⟩ : syracuseStep 1633007 = 2449511) B2449511
theorem B11176697 : Blo 1632515 11176697 := bstep (se 2 (by rfl) ⟨4191261, by rfl⟩ : syracuseStep 11176697 = 8382523) B8382523
theorem B12397373 : Blo 1632515 12397373 := bstep (se 3 (by rfl) ⟨2324507, by rfl⟩ : syracuseStep 12397373 = 4649015) B4649015
theorem B1633095 : Blo 1632515 1633095 := bstep (se 1 (by rfl) ⟨1224821, by rfl⟩ : syracuseStep 1633095 = 2449643) B2449643
theorem B1633135 : Blo 1632515 1633135 := bstep (se 1 (by rfl) ⟨1224851, by rfl⟩ : syracuseStep 1633135 = 2449703) B2449703
theorem B1633435 : Blo 1632515 1633435 := bstep (se 1 (by rfl) ⟨1225076, by rfl⟩ : syracuseStep 1633435 = 2450153) B2450153
theorem B6286585 : Blo 1632515 6286585 := bstep (se 2 (by rfl) ⟨2357469, by rfl⟩ : syracuseStep 6286585 = 4714939) B4714939
theorem B5967101 : Blo 1632515 5967101 := bstep (se 3 (by rfl) ⟨1118831, by rfl⟩ : syracuseStep 5967101 = 2237663) B2237663
theorem B1633695 : Blo 1632515 1633695 := bstep (se 1 (by rfl) ⟨1225271, by rfl⟩ : syracuseStep 1633695 = 2450543) B2450543
theorem B3673511 : Blo 1632515 3673511 := bstep (se 1 (by rfl) ⟨2755133, by rfl⟩ : syracuseStep 3673511 = 5510267) B5510267
theorem B1633775 : Blo 1632515 1633775 := bstep (se 1 (by rfl) ⟨1225331, by rfl⟩ : syracuseStep 1633775 = 2450663) B2450663
theorem B10604039 : Blo 1632515 10604039 := bstep (se 1 (by rfl) ⟨7953029, by rfl⟩ : syracuseStep 10604039 = 15906059) B15906059
theorem B1633819 : Blo 1632515 1633819 := bstep (se 1 (by rfl) ⟨1225364, by rfl⟩ : syracuseStep 1633819 = 2450729) B2450729
theorem B6975163 : Blo 1632515 6975163 := bstep (se 1 (by rfl) ⟨5231372, by rfl⟩ : syracuseStep 6975163 = 10462745) B10462745
theorem B1633999 : Blo 1632515 1633999 := bstep (se 1 (by rfl) ⟨1225499, by rfl⟩ : syracuseStep 1633999 = 2450999) B2450999
theorem B6623407 : Blo 1632515 6623407 := bstep (se 1 (by rfl) ⟨4967555, by rfl⟩ : syracuseStep 6623407 = 9935111) B9935111
theorem B3100999 : Blo 1632515 3100999 := bstep (se 1 (by rfl) ⟨2325749, by rfl⟩ : syracuseStep 3100999 = 4651499) B4651499
theorem B8950139 : Blo 1632515 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B2757287 : Blo 1632515 2757287 := bstep (se 1 (by rfl) ⟨2067965, by rfl⟩ : syracuseStep 2757287 = 4135931) B4135931
theorem B6624139 : Blo 1632515 6624139 := bstep (se 1 (by rfl) ⟨4968104, by rfl⟩ : syracuseStep 6624139 = 9936209) B9936209
theorem B4133855 : Blo 1632515 4133855 := bstep (se 1 (by rfl) ⟨3100391, by rfl⟩ : syracuseStep 4133855 = 6200783) B6200783
theorem B14144537 : Blo 1632515 14144537 := bstep (se 2 (by rfl) ⟨5304201, by rfl⟩ : syracuseStep 14144537 = 10608403) B10608403
theorem B5510429 : Blo 1632515 5510429 := bstep (se 3 (by rfl) ⟨1033205, by rfl⟩ : syracuseStep 5510429 = 2066411) B2066411
theorem B5510537 : Blo 1632515 5510537 := bstep (se 2 (by rfl) ⟨2066451, by rfl⟩ : syracuseStep 5510537 = 4132903) B4132903
theorem B4134311 : Blo 1632515 4134311 := bstep (se 1 (by rfl) ⟨3100733, by rfl⟩ : syracuseStep 4134311 = 6201467) B6201467
theorem B3675599 : Blo 1632515 3675599 := bstep (se 1 (by rfl) ⟨2756699, by rfl⟩ : syracuseStep 3675599 = 5513399) B5513399
theorem B8828441 : Blo 1632515 8828441 := bstep (se 2 (by rfl) ⟨3310665, by rfl⟩ : syracuseStep 8828441 = 6621331) B6621331
theorem B10467103 : Blo 1632515 10467103 := bstep (se 1 (by rfl) ⟨7850327, by rfl⟩ : syracuseStep 10467103 = 15700655) B15700655
theorem B3487711 : Blo 1632515 3487711 := bstep (se 1 (by rfl) ⟨2615783, by rfl⟩ : syracuseStep 3487711 = 5231567) B5231567
theorem B4651111 : Blo 1632515 4651111 := bstep (se 1 (by rfl) ⟨3488333, by rfl⟩ : syracuseStep 4651111 = 6976667) B6976667
theorem B3676409 : Blo 1632515 3676409 := bstep (se 2 (by rfl) ⟨1378653, by rfl⟩ : syracuseStep 3676409 = 2757307) B2757307
theorem B8829587 : Blo 1632515 8829587 := bstep (se 1 (by rfl) ⟨6622190, by rfl⟩ : syracuseStep 8829587 = 13244381) B13244381
theorem B13949779 : Blo 1632515 13949779 := bstep (se 1 (by rfl) ⟨10462334, by rfl⟩ : syracuseStep 13949779 = 20924669) B20924669
theorem B13245353 : Blo 1632515 13245353 := bstep (se 2 (by rfl) ⟨4967007, by rfl⟩ : syracuseStep 13245353 = 9934015) B9934015
theorem B14138441 : Blo 1632515 14138441 := bstep (se 2 (by rfl) ⟨5301915, by rfl⟩ : syracuseStep 14138441 = 10603831) B10603831
theorem B2448875 : Blo 1632515 2448875 := bstep (se 1 (by rfl) ⟨1836656, by rfl⟩ : syracuseStep 2448875 = 3673313) B3673313
theorem B4652615 : Blo 1632515 4652615 := bstep (se 1 (by rfl) ⟨3489461, by rfl⟩ : syracuseStep 4652615 = 6978923) B6978923
theorem B11771513 : Blo 1632515 11771513 := bstep (se 2 (by rfl) ⟨4414317, by rfl⟩ : syracuseStep 11771513 = 8828635) B8828635
theorem B14147311 : Blo 1632515 14147311 := bstep (se 1 (by rfl) ⟨10610483, by rfl⟩ : syracuseStep 14147311 = 21220967) B21220967
theorem B57335741 : Blo 1632515 57335741 := bstep (se 3 (by rfl) ⟨10750451, by rfl⟩ : syracuseStep 57335741 = 21500903) B21500903
theorem B2449403 : Blo 1632515 2449403 := bstep (se 1 (by rfl) ⟨1837052, by rfl⟩ : syracuseStep 2449403 = 3674105) B3674105
theorem B6201481 : Blo 1632515 6201481 := bstep (se 2 (by rfl) ⟨2325555, by rfl⟩ : syracuseStep 6201481 = 4651111) B4651111
theorem B8831209 : Blo 1632515 8831209 := bstep (se 2 (by rfl) ⟨3311703, by rfl⟩ : syracuseStep 8831209 = 6623407) B6623407
theorem B9429691 : Blo 1632515 9429691 := bstep (se 1 (by rfl) ⟨7072268, by rfl⟩ : syracuseStep 9429691 = 14144537) B14144537
theorem B3924857 : Blo 1632515 3924857 := bstep (se 2 (by rfl) ⟨1471821, by rfl⟩ : syracuseStep 3924857 = 2943643) B2943643
theorem B2450399 : Blo 1632515 2450399 := bstep (se 1 (by rfl) ⟨1837799, by rfl⟩ : syracuseStep 2450399 = 3675599) B3675599
theorem B8832185 : Blo 1632515 8832185 := bstep (se 2 (by rfl) ⟨3312069, by rfl⟩ : syracuseStep 8832185 = 6624139) B6624139
theorem B2450939 : Blo 1632515 2450939 := bstep (se 1 (by rfl) ⟨1838204, by rfl⟩ : syracuseStep 2450939 = 3676409) B3676409
theorem B8382113 : Blo 1632515 8382113 := bstep (se 2 (by rfl) ⟨3143292, by rfl⟩ : syracuseStep 8382113 = 6286585) B6286585
theorem B9300217 : Blo 1632515 9300217 := bstep (se 2 (by rfl) ⟨3487581, by rfl⟩ : syracuseStep 9300217 = 6975163) B6975163
theorem B1632583 : Blo 1632515 1632583 := bstep (se 1 (by rfl) ⟨1224437, by rfl⟩ : syracuseStep 1632583 = 2448875) B2448875
theorem B1632935 : Blo 1632515 1632935 := bstep (se 1 (by rfl) ⟨1224701, by rfl⟩ : syracuseStep 1632935 = 2449403) B2449403
theorem B1632975 : Blo 1632515 1632975 := bstep (se 1 (by rfl) ⟨1224731, by rfl⟩ : syracuseStep 1632975 = 2449463) B2449463
theorem B1633023 : Blo 1632515 1633023 := bstep (se 1 (by rfl) ⟨1224767, by rfl⟩ : syracuseStep 1633023 = 2449535) B2449535
theorem B1633055 : Blo 1632515 1633055 := bstep (se 1 (by rfl) ⟨1224791, by rfl⟩ : syracuseStep 1633055 = 2449583) B2449583
theorem B22358863 : Blo 1632515 22358863 := bstep (se 1 (by rfl) ⟨16769147, by rfl⟩ : syracuseStep 22358863 = 33538295) B33538295
theorem B5966759 : Blo 1632515 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B3976223 : Blo 1632515 3976223 := bstep (se 1 (by rfl) ⟨2982167, by rfl⟩ : syracuseStep 3976223 = 5964335) B5964335
theorem B8612891 : Blo 1632515 8612891 := bstep (se 1 (by rfl) ⟨6459668, by rfl⟩ : syracuseStep 8612891 = 12919337) B12919337
theorem B1838191 : Blo 1632515 1838191 := bstep (se 1 (by rfl) ⟨1378643, by rfl⟩ : syracuseStep 1838191 = 2757287) B2757287
theorem B1633535 : Blo 1632515 1633535 := bstep (se 1 (by rfl) ⟨1225151, by rfl⟩ : syracuseStep 1633535 = 2450303) B2450303
theorem B1633583 : Blo 1632515 1633583 := bstep (se 1 (by rfl) ⟨1225187, by rfl⟩ : syracuseStep 1633583 = 2450375) B2450375
theorem B2755903 : Blo 1632515 2755903 := bstep (se 1 (by rfl) ⟨2066927, by rfl⟩ : syracuseStep 2755903 = 4133855) B4133855
theorem B3673619 : Blo 1632515 3673619 := bstep (se 1 (by rfl) ⟨2755214, by rfl⟩ : syracuseStep 3673619 = 5510429) B5510429
theorem B1633823 : Blo 1632515 1633823 := bstep (se 1 (by rfl) ⟨1225367, by rfl⟩ : syracuseStep 1633823 = 2450735) B2450735
theorem B3673691 : Blo 1632515 3673691 := bstep (se 1 (by rfl) ⟨2755268, by rfl⟩ : syracuseStep 3673691 = 5510537) B5510537
theorem B2756207 : Blo 1632515 2756207 := bstep (se 1 (by rfl) ⟨2067155, by rfl⟩ : syracuseStep 2756207 = 4134311) B4134311
theorem B9301675 : Blo 1632515 9301675 := bstep (se 1 (by rfl) ⟨6976256, by rfl⟩ : syracuseStep 9301675 = 13952513) B13952513
theorem B5885627 : Blo 1632515 5885627 := bstep (se 1 (by rfl) ⟨4414220, by rfl⟩ : syracuseStep 5885627 = 8828441) B8828441
theorem B1633983 : Blo 1632515 1633983 := bstep (se 1 (by rfl) ⟨1225487, by rfl⟩ : syracuseStep 1633983 = 2450975) B2450975
theorem B18599705 : Blo 1632515 18599705 := bstep (se 2 (by rfl) ⟨6974889, by rfl⟩ : syracuseStep 18599705 = 13949779) B13949779
theorem B4534427 : Blo 1632515 4534427 := bstep (se 1 (by rfl) ⟨3400820, by rfl⟩ : syracuseStep 4534427 = 6801641) B6801641
theorem B15102175 : Blo 1632515 15102175 := bstep (se 1 (by rfl) ⟨11326631, by rfl⟩ : syracuseStep 15102175 = 22653263) B22653263
theorem B5886391 : Blo 1632515 5886391 := bstep (se 1 (by rfl) ⟨4414793, by rfl⟩ : syracuseStep 5886391 = 8829587) B8829587
theorem B7451131 : Blo 1632515 7451131 := bstep (se 1 (by rfl) ⟨5588348, by rfl⟩ : syracuseStep 7451131 = 11176697) B11176697
theorem B11776585 : Blo 1632515 11776585 := bstep (se 2 (by rfl) ⟨4416219, by rfl⟩ : syracuseStep 11776585 = 8832439) B8832439
theorem B9425627 : Blo 1632515 9425627 := bstep (se 1 (by rfl) ⟨7069220, by rfl⟩ : syracuseStep 9425627 = 14138441) B14138441
theorem B3978067 : Blo 1632515 3978067 := bstep (se 1 (by rfl) ⟨2983550, by rfl⟩ : syracuseStep 3978067 = 5967101) B5967101
theorem B18863081 : Blo 1632515 18863081 := bstep (se 2 (by rfl) ⟨7073655, by rfl⟩ : syracuseStep 18863081 = 14147311) B14147311
theorem B13956137 : Blo 1632515 13956137 := bstep (se 2 (by rfl) ⟨5233551, by rfl⟩ : syracuseStep 13956137 = 10467103) B10467103
theorem B3101743 : Blo 1632515 3101743 := bstep (se 1 (by rfl) ⟨2326307, by rfl⟩ : syracuseStep 3101743 = 4652615) B4652615
theorem B4650281 : Blo 1632515 4650281 := bstep (se 2 (by rfl) ⟨1743855, by rfl⟩ : syracuseStep 4650281 = 3487711) B3487711
theorem B6624787 : Blo 1632515 6624787 := bstep (se 1 (by rfl) ⟨4968590, by rfl⟩ : syracuseStep 6624787 = 9937181) B9937181
theorem B3487369 : Blo 1632515 3487369 := bstep (se 2 (by rfl) ⟨1307763, by rfl⟩ : syracuseStep 3487369 = 2615527) B2615527
theorem B89372393 : Blo 1632515 89372393 := bstep (se 2 (by rfl) ⟨33514647, by rfl⟩ : syracuseStep 89372393 = 67029295) B67029295
theorem B4134665 : Blo 1632515 4134665 := bstep (se 2 (by rfl) ⟨1550499, by rfl⟩ : syracuseStep 4134665 = 3100999) B3100999
theorem B3676391 : Blo 1632515 3676391 := bstep (se 1 (by rfl) ⟨2757293, by rfl⟩ : syracuseStep 3676391 = 5514587) B5514587
theorem B28277437 : Blo 1632515 28277437 := bstep (se 3 (by rfl) ⟨5302019, by rfl⟩ : syracuseStep 28277437 = 10604039) B10604039
theorem B4414601 : Blo 1632515 4414601 := bstep (se 2 (by rfl) ⟨1655475, by rfl⟩ : syracuseStep 4414601 = 3310951) B3310951
theorem B8264915 : Blo 1632515 8264915 := bstep (se 1 (by rfl) ⟨6198686, by rfl⟩ : syracuseStep 8264915 = 12397373) B12397373
theorem B8830235 : Blo 1632515 8830235 := bstep (se 1 (by rfl) ⟨6622676, by rfl⟩ : syracuseStep 8830235 = 13245353) B13245353
theorem B2449007 : Blo 1632515 2449007 := bstep (se 1 (by rfl) ⟨1836755, by rfl⟩ : syracuseStep 2449007 = 3673511) B3673511
theorem B7847675 : Blo 1632515 7847675 := bstep (se 1 (by rfl) ⟨5885756, by rfl⟩ : syracuseStep 7847675 = 11771513) B11771513
theorem B38223827 : Blo 1632515 38223827 := bstep (se 1 (by rfl) ⟨28667870, by rfl⟩ : syracuseStep 38223827 = 57335741) B57335741
theorem B3022951 : Blo 1632515 3022951 := bstep (se 1 (by rfl) ⟨2267213, by rfl⟩ : syracuseStep 3022951 = 4534427) B4534427
theorem B20136233 : Blo 1632515 20136233 := bstep (se 2 (by rfl) ⟨7551087, by rfl⟩ : syracuseStep 20136233 = 15102175) B15102175
theorem B6283751 : Blo 1632515 6283751 := bstep (se 1 (by rfl) ⟨4712813, by rfl⟩ : syracuseStep 6283751 = 9425627) B9425627
theorem B7848521 : Blo 1632515 7848521 := bstep (se 2 (by rfl) ⟨2943195, by rfl⟩ : syracuseStep 7848521 = 5886391) B5886391
theorem B12575387 : Blo 1632515 12575387 := bstep (se 1 (by rfl) ⟨9431540, by rfl⟩ : syracuseStep 12575387 = 18863081) B18863081
theorem B29811817 : Blo 1632515 29811817 := bstep (se 2 (by rfl) ⟨11179431, by rfl⟩ : syracuseStep 29811817 = 22358863) B22358863
theorem B5588075 : Blo 1632515 5588075 := bstep (se 1 (by rfl) ⟨4191056, by rfl⟩ : syracuseStep 5588075 = 8382113) B8382113
theorem B59581595 : Blo 1632515 59581595 := bstep (se 1 (by rfl) ⟨44686196, by rfl⟩ : syracuseStep 59581595 = 89372393) B89372393
theorem B2450921 : Blo 1632515 2450921 := bstep (se 2 (by rfl) ⟨919095, by rfl⟩ : syracuseStep 2450921 = 1838191) B1838191
theorem B2450927 : Blo 1632515 2450927 := bstep (se 1 (by rfl) ⟨1838195, by rfl⟩ : syracuseStep 2450927 = 3676391) B3676391
theorem B8833049 : Blo 1632515 8833049 := bstep (se 2 (by rfl) ⟨3312393, by rfl⟩ : syracuseStep 8833049 = 6624787) B6624787
theorem B2943067 : Blo 1632515 2943067 := bstep (se 1 (by rfl) ⟨2207300, by rfl⟩ : syracuseStep 2943067 = 4414601) B4414601
theorem B1632671 : Blo 1632515 1632671 := bstep (se 1 (by rfl) ⟨1224503, by rfl⟩ : syracuseStep 1632671 = 2449007) B2449007
theorem B1837471 : Blo 1632515 1837471 := bstep (se 1 (by rfl) ⟨1378103, by rfl⟩ : syracuseStep 1837471 = 2756207) B2756207
theorem B10603261 : Blo 1632515 10603261 := bstep (se 3 (by rfl) ⟨1988111, by rfl⟩ : syracuseStep 10603261 = 3976223) B3976223
theorem B8268641 : Blo 1632515 8268641 := bstep (se 2 (by rfl) ⟨3100740, by rfl⟩ : syracuseStep 8268641 = 6201481) B6201481
theorem B11774945 : Blo 1632515 11774945 := bstep (se 2 (by rfl) ⟨4415604, by rfl⟩ : syracuseStep 11774945 = 8831209) B8831209
theorem B2616571 : Blo 1632515 2616571 := bstep (se 1 (by rfl) ⟨1962428, by rfl⟩ : syracuseStep 2616571 = 3924857) B3924857
theorem B1633599 : Blo 1632515 1633599 := bstep (se 1 (by rfl) ⟨1225199, by rfl⟩ : syracuseStep 1633599 = 2450399) B2450399
theorem B23547293 : Blo 1632515 23547293 := bstep (se 3 (by rfl) ⟨4415117, by rfl⟩ : syracuseStep 23547293 = 8830235) B8830235
theorem B3100187 : Blo 1632515 3100187 := bstep (se 1 (by rfl) ⟨2325140, by rfl⟩ : syracuseStep 3100187 = 4650281) B4650281
theorem B37703249 : Blo 1632515 37703249 := bstep (se 2 (by rfl) ⟨14138718, by rfl⟩ : syracuseStep 37703249 = 28277437) B28277437
theorem B1633959 : Blo 1632515 1633959 := bstep (se 1 (by rfl) ⟨1225469, by rfl⟩ : syracuseStep 1633959 = 2450939) B2450939
theorem B5304089 : Blo 1632515 5304089 := bstep (se 2 (by rfl) ⟨1989033, by rfl⟩ : syracuseStep 5304089 = 3978067) B3978067
theorem B2756443 : Blo 1632515 2756443 := bstep (se 1 (by rfl) ⟨2067332, by rfl⟩ : syracuseStep 2756443 = 4134665) B4134665
theorem B3674537 : Blo 1632515 3674537 := bstep (se 2 (by rfl) ⟨1377951, by rfl⟩ : syracuseStep 3674537 = 2755903) B2755903
theorem B3977839 : Blo 1632515 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B5509943 : Blo 1632515 5509943 := bstep (se 1 (by rfl) ⟨4132457, by rfl⟩ : syracuseStep 5509943 = 8264915) B8264915
theorem B4649825 : Blo 1632515 4649825 := bstep (se 2 (by rfl) ⟨1743684, by rfl⟩ : syracuseStep 4649825 = 3487369) B3487369
theorem B5231783 : Blo 1632515 5231783 := bstep (se 1 (by rfl) ⟨3923837, by rfl⟩ : syracuseStep 5231783 = 7847675) B7847675
theorem B12399803 : Blo 1632515 12399803 := bstep (se 1 (by rfl) ⟨9299852, by rfl⟩ : syracuseStep 12399803 = 18599705) B18599705
theorem B25482551 : Blo 1632515 25482551 := bstep (se 1 (by rfl) ⟨19111913, by rfl⟩ : syracuseStep 25482551 = 38223827) B38223827
theorem B12400289 : Blo 1632515 12400289 := bstep (se 2 (by rfl) ⟨4650108, by rfl⟩ : syracuseStep 12400289 = 9300217) B9300217
theorem B9934841 : Blo 1632515 9934841 := bstep (se 2 (by rfl) ⟨3725565, by rfl⟩ : syracuseStep 9934841 = 7451131) B7451131
theorem B9304091 : Blo 1632515 9304091 := bstep (se 1 (by rfl) ⟨6978068, by rfl⟩ : syracuseStep 9304091 = 13956137) B13956137
theorem B15702113 : Blo 1632515 15702113 := bstep (se 2 (by rfl) ⟨5888292, by rfl⟩ : syracuseStep 15702113 = 11776585) B11776585
theorem B5888123 : Blo 1632515 5888123 := bstep (se 1 (by rfl) ⟨4416092, by rfl⟩ : syracuseStep 5888123 = 8832185) B8832185
theorem B12572921 : Blo 1632515 12572921 := bstep (se 2 (by rfl) ⟨4714845, by rfl⟩ : syracuseStep 12572921 = 9429691) B9429691
theorem B4135657 : Blo 1632515 4135657 := bstep (se 2 (by rfl) ⟨1550871, by rfl⟩ : syracuseStep 4135657 = 3101743) B3101743
theorem B15695005 : Blo 1632515 15695005 := bstep (se 3 (by rfl) ⟨2942813, by rfl⟩ : syracuseStep 15695005 = 5885627) B5885627
theorem B5741927 : Blo 1632515 5741927 := bstep (se 1 (by rfl) ⟨4306445, by rfl⟩ : syracuseStep 5741927 = 8612891) B8612891
theorem B12402233 : Blo 1632515 12402233 := bstep (se 2 (by rfl) ⟨4650837, by rfl⟩ : syracuseStep 12402233 = 9301675) B9301675
theorem B2449079 : Blo 1632515 2449079 := bstep (se 1 (by rfl) ⟨1836809, by rfl⟩ : syracuseStep 2449079 = 3673619) B3673619
theorem B2449127 : Blo 1632515 2449127 := bstep (se 1 (by rfl) ⟨1836845, by rfl⟩ : syracuseStep 2449127 = 3673691) B3673691
theorem B3924089 : Blo 1632515 3924089 := bstep (se 2 (by rfl) ⟨1471533, by rfl⟩ : syracuseStep 3924089 = 2943067) B2943067
theorem B4030601 : Blo 1632515 4030601 := bstep (se 2 (by rfl) ⟨1511475, by rfl⟩ : syracuseStep 4030601 = 3022951) B3022951
theorem B2449691 : Blo 1632515 2449691 := bstep (se 1 (by rfl) ⟨1837268, by rfl⟩ : syracuseStep 2449691 = 3674537) B3674537
theorem B158884253 : Blo 1632515 158884253 := bstep (se 3 (by rfl) ⟨29790797, by rfl⟩ : syracuseStep 158884253 = 59581595) B59581595
theorem B2449961 : Blo 1632515 2449961 := bstep (se 2 (by rfl) ⟨918735, by rfl⟩ : syracuseStep 2449961 = 1837471) B1837471
theorem B8266535 : Blo 1632515 8266535 := bstep (se 1 (by rfl) ⟨6199901, by rfl⟩ : syracuseStep 8266535 = 12399803) B12399803
theorem B67953469 : Blo 1632515 67953469 := bstep (se 3 (by rfl) ⟨12741275, by rfl⟩ : syracuseStep 67953469 = 25482551) B25482551
theorem B5514209 : Blo 1632515 5514209 := bstep (se 2 (by rfl) ⟨2067828, by rfl⟩ : syracuseStep 5514209 = 4135657) B4135657
theorem B8266859 : Blo 1632515 8266859 := bstep (se 1 (by rfl) ⟨6200144, by rfl⟩ : syracuseStep 8266859 = 12400289) B12400289
theorem B6202727 : Blo 1632515 6202727 := bstep (se 1 (by rfl) ⟨4652045, by rfl⟩ : syracuseStep 6202727 = 9304091) B9304091
theorem B3925415 : Blo 1632515 3925415 := bstep (se 1 (by rfl) ⟨2944061, by rfl⟩ : syracuseStep 3925415 = 5888123) B5888123
theorem B7849963 : Blo 1632515 7849963 := bstep (se 1 (by rfl) ⟨5887472, by rfl⟩ : syracuseStep 7849963 = 11774945) B11774945
theorem B3827951 : Blo 1632515 3827951 := bstep (se 1 (by rfl) ⟨2870963, by rfl⟩ : syracuseStep 3827951 = 5741927) B5741927
theorem B15698195 : Blo 1632515 15698195 := bstep (se 1 (by rfl) ⟨11773646, by rfl⟩ : syracuseStep 15698195 = 23547293) B23547293
theorem B2066791 : Blo 1632515 2066791 := bstep (se 1 (by rfl) ⟨1550093, by rfl⟩ : syracuseStep 2066791 = 3100187) B3100187
theorem B8268155 : Blo 1632515 8268155 := bstep (se 1 (by rfl) ⟨6201116, by rfl⟩ : syracuseStep 8268155 = 12402233) B12402233
theorem B25135499 : Blo 1632515 25135499 := bstep (se 1 (by rfl) ⟨18851624, by rfl⟩ : syracuseStep 25135499 = 37703249) B37703249
theorem B1632719 : Blo 1632515 1632719 := bstep (se 1 (by rfl) ⟨1224539, by rfl⟩ : syracuseStep 1632719 = 2449079) B2449079
theorem B1632751 : Blo 1632515 1632751 := bstep (se 1 (by rfl) ⟨1224563, by rfl⟩ : syracuseStep 1632751 = 2449127) B2449127
theorem B41872301 : Blo 1632515 41872301 := bstep (se 3 (by rfl) ⟨7851056, by rfl⟩ : syracuseStep 41872301 = 15702113) B15702113
theorem B8383591 : Blo 1632515 8383591 := bstep (se 1 (by rfl) ⟨6287693, by rfl⟩ : syracuseStep 8383591 = 12575387) B12575387
theorem B3673295 : Blo 1632515 3673295 := bstep (se 1 (by rfl) ⟨2754971, by rfl⟩ : syracuseStep 3673295 = 5509943) B5509943
theorem B3099883 : Blo 1632515 3099883 := bstep (se 1 (by rfl) ⟨2324912, by rfl⟩ : syracuseStep 3099883 = 4649825) B4649825
theorem B1633947 : Blo 1632515 1633947 := bstep (se 1 (by rfl) ⟨1225460, by rfl⟩ : syracuseStep 1633947 = 2450921) B2450921
theorem B1633951 : Blo 1632515 1633951 := bstep (se 1 (by rfl) ⟨1225463, by rfl⟩ : syracuseStep 1633951 = 2450927) B2450927
theorem B16756669 : Blo 1632515 16756669 := bstep (se 3 (by rfl) ⟨3141875, by rfl⟩ : syracuseStep 16756669 = 6283751) B6283751
theorem B6623227 : Blo 1632515 6623227 := bstep (se 1 (by rfl) ⟨4967420, by rfl⟩ : syracuseStep 6623227 = 9934841) B9934841
theorem B20926673 : Blo 1632515 20926673 := bstep (se 2 (by rfl) ⟨7847502, by rfl⟩ : syracuseStep 20926673 = 15695005) B15695005
theorem B3675257 : Blo 1632515 3675257 := bstep (se 2 (by rfl) ⟨1378221, by rfl⟩ : syracuseStep 3675257 = 2756443) B2756443
theorem B3536059 : Blo 1632515 3536059 := bstep (se 1 (by rfl) ⟨2652044, by rfl⟩ : syracuseStep 3536059 = 5304089) B5304089
theorem B5232347 : Blo 1632515 5232347 := bstep (se 1 (by rfl) ⟨3924260, by rfl⟩ : syracuseStep 5232347 = 7848521) B7848521
theorem B158996357 : Blo 1632515 158996357 := bstep (se 4 (by rfl) ⟨14905908, by rfl⟩ : syracuseStep 158996357 = 29811817) B29811817
theorem B21215141 : Blo 1632515 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B33527789 : Blo 1632515 33527789 := bstep (se 3 (by rfl) ⟨6286460, by rfl⟩ : syracuseStep 33527789 = 12572921) B12572921
theorem B3725383 : Blo 1632515 3725383 := bstep (se 1 (by rfl) ⟨2794037, by rfl⟩ : syracuseStep 3725383 = 5588075) B5588075
theorem B53696621 : Blo 1632515 53696621 := bstep (se 3 (by rfl) ⟨10068116, by rfl⟩ : syracuseStep 53696621 = 20136233) B20136233
theorem B3487855 : Blo 1632515 3487855 := bstep (se 1 (by rfl) ⟨2615891, by rfl⟩ : syracuseStep 3487855 = 5231783) B5231783
theorem B14137681 : Blo 1632515 14137681 := bstep (se 2 (by rfl) ⟨5301630, by rfl⟩ : syracuseStep 14137681 = 10603261) B10603261
theorem B5888699 : Blo 1632515 5888699 := bstep (se 1 (by rfl) ⟨4416524, by rfl⟩ : syracuseStep 5888699 = 8833049) B8833049
theorem B3488761 : Blo 1632515 3488761 := bstep (se 2 (by rfl) ⟨1308285, by rfl⟩ : syracuseStep 3488761 = 2616571) B2616571
theorem B5512427 : Blo 1632515 5512427 := bstep (se 1 (by rfl) ⟨4134320, by rfl⟩ : syracuseStep 5512427 = 8268641) B8268641
theorem B13951115 : Blo 1632515 13951115 := bstep (se 1 (by rfl) ⟨10463336, by rfl⟩ : syracuseStep 13951115 = 20926673) B20926673
theorem B105922835 : Blo 1632515 105922835 := bstep (se 1 (by rfl) ⟨79442126, by rfl⟩ : syracuseStep 105922835 = 158884253) B158884253
theorem B18850241 : Blo 1632515 18850241 := bstep (se 2 (by rfl) ⟨7068840, by rfl⟩ : syracuseStep 18850241 = 14137681) B14137681
theorem B2450171 : Blo 1632515 2450171 := bstep (se 1 (by rfl) ⟨1837628, by rfl⟩ : syracuseStep 2450171 = 3675257) B3675257
theorem B90604625 : Blo 1632515 90604625 := bstep (se 2 (by rfl) ⟨33976734, by rfl⟩ : syracuseStep 90604625 = 67953469) B67953469
theorem B105997571 : Blo 1632515 105997571 := bstep (se 1 (by rfl) ⟨79498178, by rfl⟩ : syracuseStep 105997571 = 158996357) B158996357
theorem B42993077 : Blo 1632515 42993077 := bstep (se 5 (by rfl) ⟨2015300, by rfl⟩ : syracuseStep 42993077 = 4030601) B4030601
theorem B3925799 : Blo 1632515 3925799 := bstep (se 1 (by rfl) ⟨2944349, by rfl⟩ : syracuseStep 3925799 = 5888699) B5888699
theorem B22342225 : Blo 1632515 22342225 := bstep (se 2 (by rfl) ⟨8378334, by rfl⟩ : syracuseStep 22342225 = 16756669) B16756669
theorem B2616059 : Blo 1632515 2616059 := bstep (se 1 (by rfl) ⟨1962044, by rfl⟩ : syracuseStep 2616059 = 3924089) B3924089
theorem B4967177 : Blo 1632515 4967177 := bstep (se 2 (by rfl) ⟨1862691, by rfl⟩ : syracuseStep 4967177 = 3725383) B3725383
theorem B1633127 : Blo 1632515 1633127 := bstep (se 1 (by rfl) ⟨1224845, by rfl⟩ : syracuseStep 1633127 = 2449691) B2449691
theorem B1633307 : Blo 1632515 1633307 := bstep (se 1 (by rfl) ⟨1224980, by rfl⟩ : syracuseStep 1633307 = 2449961) B2449961
theorem B2755721 : Blo 1632515 2755721 := bstep (se 2 (by rfl) ⟨1033395, by rfl⟩ : syracuseStep 2755721 = 2066791) B2066791
theorem B2616943 : Blo 1632515 2616943 := bstep (se 1 (by rfl) ⟨1962707, by rfl⟩ : syracuseStep 2616943 = 3925415) B3925415
theorem B14143427 : Blo 1632515 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B22351859 : Blo 1632515 22351859 := bstep (se 1 (by rfl) ⟨16763894, by rfl⟩ : syracuseStep 22351859 = 33527789) B33527789
theorem B11178121 : Blo 1632515 11178121 := bstep (se 2 (by rfl) ⟨4191795, by rfl⟩ : syracuseStep 11178121 = 8383591) B8383591
theorem B2551967 : Blo 1632515 2551967 := bstep (se 1 (by rfl) ⟨1913975, by rfl⟩ : syracuseStep 2551967 = 3827951) B3827951
theorem B10465463 : Blo 1632515 10465463 := bstep (se 1 (by rfl) ⟨7849097, by rfl⟩ : syracuseStep 10465463 = 15698195) B15698195
theorem B4714745 : Blo 1632515 4714745 := bstep (se 2 (by rfl) ⟨1768029, by rfl⟩ : syracuseStep 4714745 = 3536059) B3536059
theorem B16756999 : Blo 1632515 16756999 := bstep (se 1 (by rfl) ⟨12567749, by rfl⟩ : syracuseStep 16756999 = 25135499) B25135499
theorem B4133177 : Blo 1632515 4133177 := bstep (se 2 (by rfl) ⟨1549941, by rfl⟩ : syracuseStep 4133177 = 3099883) B3099883
theorem B27914867 : Blo 1632515 27914867 := bstep (se 1 (by rfl) ⟨20936150, by rfl⟩ : syracuseStep 27914867 = 41872301) B41872301
theorem B3674951 : Blo 1632515 3674951 := bstep (se 1 (by rfl) ⟨2756213, by rfl⟩ : syracuseStep 3674951 = 5512427) B5512427
theorem B10466617 : Blo 1632515 10466617 := bstep (se 2 (by rfl) ⟨3924981, by rfl⟩ : syracuseStep 10466617 = 7849963) B7849963
theorem B4650473 : Blo 1632515 4650473 := bstep (se 2 (by rfl) ⟨1743927, by rfl⟩ : syracuseStep 4650473 = 3487855) B3487855
theorem B5511023 : Blo 1632515 5511023 := bstep (se 1 (by rfl) ⟨4133267, by rfl⟩ : syracuseStep 5511023 = 8266535) B8266535
theorem B3676139 : Blo 1632515 3676139 := bstep (se 1 (by rfl) ⟨2757104, by rfl⟩ : syracuseStep 3676139 = 5514209) B5514209
theorem B5511239 : Blo 1632515 5511239 := bstep (se 1 (by rfl) ⟨4133429, by rfl⟩ : syracuseStep 5511239 = 8266859) B8266859
theorem B4135151 : Blo 1632515 4135151 := bstep (se 1 (by rfl) ⟨3101363, by rfl⟩ : syracuseStep 4135151 = 6202727) B6202727
theorem B3488231 : Blo 1632515 3488231 := bstep (se 1 (by rfl) ⟨2616173, by rfl⟩ : syracuseStep 3488231 = 5232347) B5232347
theorem B4651681 : Blo 1632515 4651681 := bstep (se 2 (by rfl) ⟨1744380, by rfl⟩ : syracuseStep 4651681 = 3488761) B3488761
theorem B35797747 : Blo 1632515 35797747 := bstep (se 1 (by rfl) ⟨26848310, by rfl⟩ : syracuseStep 35797747 = 53696621) B53696621
theorem B5512103 : Blo 1632515 5512103 := bstep (se 1 (by rfl) ⟨4134077, by rfl⟩ : syracuseStep 5512103 = 8268155) B8268155
theorem B2448863 : Blo 1632515 2448863 := bstep (se 1 (by rfl) ⟨1836647, by rfl⟩ : syracuseStep 2448863 = 3673295) B3673295
theorem B35323877 : Blo 1632515 35323877 := bstep (se 4 (by rfl) ⟨3311613, by rfl⟩ : syracuseStep 35323877 = 6623227) B6623227
theorem B70615223 : Blo 1632515 70615223 := bstep (se 1 (by rfl) ⟨52961417, by rfl⟩ : syracuseStep 70615223 = 105922835) B105922835
theorem B12566827 : Blo 1632515 12566827 := bstep (se 1 (by rfl) ⟨9425120, by rfl⟩ : syracuseStep 12566827 = 18850241) B18850241
theorem B2449967 : Blo 1632515 2449967 := bstep (se 1 (by rfl) ⟨1837475, by rfl⟩ : syracuseStep 2449967 = 3674951) B3674951
theorem B70665047 : Blo 1632515 70665047 := bstep (se 1 (by rfl) ⟨52998785, by rfl⟩ : syracuseStep 70665047 = 105997571) B105997571
theorem B6202241 : Blo 1632515 6202241 := bstep (se 2 (by rfl) ⟨2325840, by rfl⟩ : syracuseStep 6202241 = 4651681) B4651681
theorem B114648205 : Blo 1632515 114648205 := bstep (se 3 (by rfl) ⟨21496538, by rfl⟩ : syracuseStep 114648205 = 42993077) B42993077
theorem B2450759 : Blo 1632515 2450759 := bstep (se 1 (by rfl) ⟨1838069, by rfl⟩ : syracuseStep 2450759 = 3676139) B3676139
theorem B1837147 : Blo 1632515 1837147 := bstep (se 1 (by rfl) ⟨1377860, by rfl⟩ : syracuseStep 1837147 = 2755721) B2755721
theorem B1632575 : Blo 1632515 1632575 := bstep (se 1 (by rfl) ⟨1224431, by rfl⟩ : syracuseStep 1632575 = 2448863) B2448863
theorem B9300743 : Blo 1632515 9300743 := bstep (se 1 (by rfl) ⟨6975557, by rfl⟩ : syracuseStep 9300743 = 13951115) B13951115
theorem B14904161 : Blo 1632515 14904161 := bstep (se 2 (by rfl) ⟨5589060, by rfl⟩ : syracuseStep 14904161 = 11178121) B11178121
theorem B2755451 : Blo 1632515 2755451 := bstep (se 1 (by rfl) ⟨2066588, by rfl⟩ : syracuseStep 2755451 = 4133177) B4133177
theorem B1633447 : Blo 1632515 1633447 := bstep (se 1 (by rfl) ⟨1225085, by rfl⟩ : syracuseStep 1633447 = 2450171) B2450171
theorem B29789633 : Blo 1632515 29789633 := bstep (se 2 (by rfl) ⟨11171112, by rfl⟩ : syracuseStep 29789633 = 22342225) B22342225
theorem B47730329 : Blo 1632515 47730329 := bstep (se 2 (by rfl) ⟨17898873, by rfl⟩ : syracuseStep 47730329 = 35797747) B35797747
theorem B2617199 : Blo 1632515 2617199 := bstep (se 1 (by rfl) ⟨1962899, by rfl⟩ : syracuseStep 2617199 = 3925799) B3925799
theorem B3674015 : Blo 1632515 3674015 := bstep (se 1 (by rfl) ⟨2755511, by rfl⟩ : syracuseStep 3674015 = 5511023) B5511023
theorem B9301949 : Blo 1632515 9301949 := bstep (se 3 (by rfl) ⟨1744115, by rfl⟩ : syracuseStep 9301949 = 3488231) B3488231
theorem B89370661 : Blo 1632515 89370661 := bstep (se 4 (by rfl) ⟨8378499, by rfl⟩ : syracuseStep 89370661 = 16756999) B16756999
theorem B3674159 : Blo 1632515 3674159 := bstep (se 1 (by rfl) ⟨2755619, by rfl⟩ : syracuseStep 3674159 = 5511239) B5511239
theorem B2756767 : Blo 1632515 2756767 := bstep (se 1 (by rfl) ⟨2067575, by rfl⟩ : syracuseStep 2756767 = 4135151) B4135151
theorem B13955489 : Blo 1632515 13955489 := bstep (se 2 (by rfl) ⟨5233308, by rfl⟩ : syracuseStep 13955489 = 10466617) B10466617
theorem B3674735 : Blo 1632515 3674735 := bstep (se 1 (by rfl) ⟨2756051, by rfl⟩ : syracuseStep 3674735 = 5512103) B5512103
theorem B23549251 : Blo 1632515 23549251 := bstep (se 1 (by rfl) ⟨17661938, by rfl⟩ : syracuseStep 23549251 = 35323877) B35323877
theorem B1701311 : Blo 1632515 1701311 := bstep (se 1 (by rfl) ⟨1275983, by rfl⟩ : syracuseStep 1701311 = 2551967) B2551967
theorem B6976975 : Blo 1632515 6976975 := bstep (se 1 (by rfl) ⟨5232731, by rfl⟩ : syracuseStep 6976975 = 10465463) B10465463
theorem B18609911 : Blo 1632515 18609911 := bstep (se 1 (by rfl) ⟨13957433, by rfl⟩ : syracuseStep 18609911 = 27914867) B27914867
theorem B12572653 : Blo 1632515 12572653 := bstep (se 3 (by rfl) ⟨2357372, by rfl⟩ : syracuseStep 12572653 = 4714745) B4714745
theorem B966449333 : Blo 1632515 966449333 := bstep (se 5 (by rfl) ⟨45302312, by rfl⟩ : syracuseStep 966449333 = 90604625) B90604625
theorem B12401261 : Blo 1632515 12401261 := bstep (se 3 (by rfl) ⟨2325236, by rfl⟩ : syracuseStep 12401261 = 4650473) B4650473
theorem B1744039 : Blo 1632515 1744039 := bstep (se 1 (by rfl) ⟨1308029, by rfl⟩ : syracuseStep 1744039 = 2616059) B2616059
theorem B13245805 : Blo 1632515 13245805 := bstep (se 3 (by rfl) ⟨2483588, by rfl⟩ : syracuseStep 13245805 = 4967177) B4967177
theorem B3489257 : Blo 1632515 3489257 := bstep (se 2 (by rfl) ⟨1308471, by rfl⟩ : syracuseStep 3489257 = 2616943) B2616943
theorem B9428951 : Blo 1632515 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B14901239 : Blo 1632515 14901239 := bstep (se 1 (by rfl) ⟨11175929, by rfl⟩ : syracuseStep 14901239 = 22351859) B22351859
theorem B2449439 : Blo 1632515 2449439 := bstep (se 1 (by rfl) ⟨1837079, by rfl⟩ : syracuseStep 2449439 = 3674159) B3674159
theorem B119160881 : Blo 1632515 119160881 := bstep (se 2 (by rfl) ⟨44685330, by rfl⟩ : syracuseStep 119160881 = 89370661) B89370661
theorem B2449529 : Blo 1632515 2449529 := bstep (se 2 (by rfl) ⟨918573, by rfl⟩ : syracuseStep 2449529 = 1837147) B1837147
theorem B2449823 : Blo 1632515 2449823 := bstep (se 1 (by rfl) ⟨1837367, by rfl⟩ : syracuseStep 2449823 = 3674735) B3674735
theorem B152864273 : Blo 1632515 152864273 := bstep (se 2 (by rfl) ⟨57324102, by rfl⟩ : syracuseStep 152864273 = 114648205) B114648205
theorem B8267507 : Blo 1632515 8267507 := bstep (se 1 (by rfl) ⟨6200630, by rfl⟩ : syracuseStep 8267507 = 12401261) B12401261
theorem B1836967 : Blo 1632515 1836967 := bstep (se 1 (by rfl) ⟨1377725, by rfl⟩ : syracuseStep 1836967 = 2755451) B2755451
theorem B19859755 : Blo 1632515 19859755 := bstep (se 1 (by rfl) ⟨14894816, by rfl⟩ : syracuseStep 19859755 = 29789633) B29789633
theorem B31820219 : Blo 1632515 31820219 := bstep (se 1 (by rfl) ⟨23865164, by rfl⟩ : syracuseStep 31820219 = 47730329) B47730329
theorem B6285967 : Blo 1632515 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B16763537 : Blo 1632515 16763537 := bstep (se 2 (by rfl) ⟨6286326, by rfl⟩ : syracuseStep 16763537 = 12572653) B12572653
theorem B1633311 : Blo 1632515 1633311 := bstep (se 1 (by rfl) ⟨1224983, by rfl⟩ : syracuseStep 1633311 = 2449967) B2449967
theorem B16755769 : Blo 1632515 16755769 := bstep (se 2 (by rfl) ⟨6283413, by rfl⟩ : syracuseStep 16755769 = 12566827) B12566827
theorem B2577198221 : Blo 1632515 2577198221 := bstep (se 3 (by rfl) ⟨483224666, by rfl⟩ : syracuseStep 2577198221 = 966449333) B966449333
theorem B1633839 : Blo 1632515 1633839 := bstep (se 1 (by rfl) ⟨1225379, by rfl⟩ : syracuseStep 1633839 = 2450759) B2450759
theorem B12406607 : Blo 1632515 12406607 := bstep (se 1 (by rfl) ⟨9304955, by rfl⟩ : syracuseStep 12406607 = 18609911) B18609911
theorem B9302633 : Blo 1632515 9302633 := bstep (se 2 (by rfl) ⟨3488487, by rfl⟩ : syracuseStep 9302633 = 6976975) B6976975
theorem B9934159 : Blo 1632515 9934159 := bstep (se 1 (by rfl) ⟨7450619, by rfl⟩ : syracuseStep 9934159 = 14901239) B14901239
theorem B47076815 : Blo 1632515 47076815 := bstep (se 1 (by rfl) ⟨35307611, by rfl⟩ : syracuseStep 47076815 = 70615223) B70615223
theorem B3675689 : Blo 1632515 3675689 := bstep (se 2 (by rfl) ⟨1378383, by rfl⟩ : syracuseStep 3675689 = 2756767) B2756767
theorem B9303659 : Blo 1632515 9303659 := bstep (se 1 (by rfl) ⟨6977744, by rfl⟩ : syracuseStep 9303659 = 13955489) B13955489
theorem B47110031 : Blo 1632515 47110031 := bstep (se 1 (by rfl) ⟨35332523, by rfl⟩ : syracuseStep 47110031 = 70665047) B70665047
theorem B4134827 : Blo 1632515 4134827 := bstep (se 1 (by rfl) ⟨3101120, by rfl⟩ : syracuseStep 4134827 = 6202241) B6202241
theorem B4536829 : Blo 1632515 4536829 := bstep (se 3 (by rfl) ⟨850655, by rfl⟩ : syracuseStep 4536829 = 1701311) B1701311
theorem B2325385 : Blo 1632515 2325385 := bstep (se 2 (by rfl) ⟨872019, by rfl⟩ : syracuseStep 2325385 = 1744039) B1744039
theorem B31399001 : Blo 1632515 31399001 := bstep (se 2 (by rfl) ⟨11774625, by rfl⟩ : syracuseStep 31399001 = 23549251) B23549251
theorem B17661073 : Blo 1632515 17661073 := bstep (se 2 (by rfl) ⟨6622902, by rfl⟩ : syracuseStep 17661073 = 13245805) B13245805
theorem B6200495 : Blo 1632515 6200495 := bstep (se 1 (by rfl) ⟨4650371, by rfl⟩ : syracuseStep 6200495 = 9300743) B9300743
theorem B9936107 : Blo 1632515 9936107 := bstep (se 1 (by rfl) ⟨7452080, by rfl⟩ : syracuseStep 9936107 = 14904161) B14904161
theorem B2326171 : Blo 1632515 2326171 := bstep (se 1 (by rfl) ⟨1744628, by rfl⟩ : syracuseStep 2326171 = 3489257) B3489257
theorem B1744799 : Blo 1632515 1744799 := bstep (se 1 (by rfl) ⟨1308599, by rfl⟩ : syracuseStep 1744799 = 2617199) B2617199
theorem B2449343 : Blo 1632515 2449343 := bstep (se 1 (by rfl) ⟨1837007, by rfl⟩ : syracuseStep 2449343 = 3674015) B3674015
theorem B6201299 : Blo 1632515 6201299 := bstep (se 1 (by rfl) ⟨4650974, by rfl⟩ : syracuseStep 6201299 = 9301949) B9301949
theorem B6201755 : Blo 1632515 6201755 := bstep (se 1 (by rfl) ⟨4651316, by rfl⟩ : syracuseStep 6201755 = 9302633) B9302633
theorem B31384543 : Blo 1632515 31384543 := bstep (se 1 (by rfl) ⟨23538407, by rfl⟩ : syracuseStep 31384543 = 47076815) B47076815
theorem B101909515 : Blo 1632515 101909515 := bstep (se 1 (by rfl) ⟨76432136, by rfl⟩ : syracuseStep 101909515 = 152864273) B152864273
theorem B2450459 : Blo 1632515 2450459 := bstep (se 1 (by rfl) ⟨1837844, by rfl⟩ : syracuseStep 2450459 = 3675689) B3675689
theorem B6202439 : Blo 1632515 6202439 := bstep (se 1 (by rfl) ⟨4651829, by rfl⟩ : syracuseStep 6202439 = 9303659) B9303659
theorem B22341025 : Blo 1632515 22341025 := bstep (se 2 (by rfl) ⟨8377884, by rfl⟩ : syracuseStep 22341025 = 16755769) B16755769
theorem B11175691 : Blo 1632515 11175691 := bstep (se 1 (by rfl) ⟨8381768, by rfl⟩ : syracuseStep 11175691 = 16763537) B16763537
theorem B20932667 : Blo 1632515 20932667 := bstep (se 1 (by rfl) ⟨15699500, by rfl⟩ : syracuseStep 20932667 = 31399001) B31399001
theorem B1632895 : Blo 1632515 1632895 := bstep (se 1 (by rfl) ⟨1224671, by rfl⟩ : syracuseStep 1632895 = 2449343) B2449343
theorem B1632959 : Blo 1632515 1632959 := bstep (se 1 (by rfl) ⟨1224719, by rfl⟩ : syracuseStep 1632959 = 2449439) B2449439
theorem B79440587 : Blo 1632515 79440587 := bstep (se 1 (by rfl) ⟨59580440, by rfl⟩ : syracuseStep 79440587 = 119160881) B119160881
theorem B1633019 : Blo 1632515 1633019 := bstep (se 1 (by rfl) ⟨1224764, by rfl⟩ : syracuseStep 1633019 = 2449529) B2449529
theorem B1633215 : Blo 1632515 1633215 := bstep (se 1 (by rfl) ⟨1224911, by rfl⟩ : syracuseStep 1633215 = 2449823) B2449823
theorem B26479673 : Blo 1632515 26479673 := bstep (se 2 (by rfl) ⟨9929877, by rfl⟩ : syracuseStep 26479673 = 19859755) B19859755
theorem B3100513 : Blo 1632515 3100513 := bstep (se 2 (by rfl) ⟨1162692, by rfl⟩ : syracuseStep 3100513 = 2325385) B2325385
theorem B2756551 : Blo 1632515 2756551 := bstep (se 1 (by rfl) ⟨2067413, by rfl⟩ : syracuseStep 2756551 = 4134827) B4134827
theorem B23548097 : Blo 1632515 23548097 := bstep (se 2 (by rfl) ⟨8830536, by rfl⟩ : syracuseStep 23548097 = 17661073) B17661073
theorem B21213479 : Blo 1632515 21213479 := bstep (se 1 (by rfl) ⟨15910109, by rfl⟩ : syracuseStep 21213479 = 31820219) B31820219
theorem B4133663 : Blo 1632515 4133663 := bstep (se 1 (by rfl) ⟨3100247, by rfl⟩ : syracuseStep 4133663 = 6200495) B6200495
theorem B6624071 : Blo 1632515 6624071 := bstep (se 1 (by rfl) ⟨4968053, by rfl⟩ : syracuseStep 6624071 = 9936107) B9936107
theorem B3101561 : Blo 1632515 3101561 := bstep (se 2 (by rfl) ⟨1163085, by rfl⟩ : syracuseStep 3101561 = 2326171) B2326171
theorem B8271071 : Blo 1632515 8271071 := bstep (se 1 (by rfl) ⟨6203303, by rfl⟩ : syracuseStep 8271071 = 12406607) B12406607
theorem B4134199 : Blo 1632515 4134199 := bstep (se 1 (by rfl) ⟨3100649, by rfl⟩ : syracuseStep 4134199 = 6201299) B6201299
theorem B24196421 : Blo 1632515 24196421 := bstep (se 4 (by rfl) ⟨2268414, by rfl⟩ : syracuseStep 24196421 = 4536829) B4536829
theorem B134100629 : Blo 1632515 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B5511671 : Blo 1632515 5511671 := bstep (se 1 (by rfl) ⟨4133753, by rfl⟩ : syracuseStep 5511671 = 8267507) B8267507
theorem B31406687 : Blo 1632515 31406687 := bstep (se 1 (by rfl) ⟨23555015, by rfl⟩ : syracuseStep 31406687 = 47110031) B47110031
theorem B13245545 : Blo 1632515 13245545 := bstep (se 2 (by rfl) ⟨4967079, by rfl⟩ : syracuseStep 13245545 = 9934159) B9934159
theorem B1718132147 : Blo 1632515 1718132147 := bstep (se 1 (by rfl) ⟨1288599110, by rfl⟩ : syracuseStep 1718132147 = 2577198221) B2577198221
theorem B4652797 : Blo 1632515 4652797 := bstep (se 3 (by rfl) ⟨872399, by rfl⟩ : syracuseStep 4652797 = 1744799) B1744799
theorem B2449289 : Blo 1632515 2449289 := bstep (se 2 (by rfl) ⟨918483, by rfl⟩ : syracuseStep 2449289 = 1836967) B1836967
theorem B4416047 : Blo 1632515 4416047 := bstep (se 1 (by rfl) ⟨3312035, by rfl⟩ : syracuseStep 4416047 = 6624071) B6624071
theorem B5514047 : Blo 1632515 5514047 := bstep (se 1 (by rfl) ⟨4135535, by rfl⟩ : syracuseStep 5514047 = 8271071) B8271071
theorem B16130947 : Blo 1632515 16130947 := bstep (se 1 (by rfl) ⟨12098210, by rfl⟩ : syracuseStep 16130947 = 24196421) B24196421
theorem B89400419 : Blo 1632515 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B41846057 : Blo 1632515 41846057 := bstep (se 2 (by rfl) ⟨15692271, by rfl⟩ : syracuseStep 41846057 = 31384543) B31384543
theorem B29788033 : Blo 1632515 29788033 := bstep (se 2 (by rfl) ⟨11170512, by rfl⟩ : syracuseStep 29788033 = 22341025) B22341025
theorem B6203729 : Blo 1632515 6203729 := bstep (se 2 (by rfl) ⟨2326398, by rfl⟩ : syracuseStep 6203729 = 4652797) B4652797
theorem B1632859 : Blo 1632515 1632859 := bstep (se 1 (by rfl) ⟨1224644, by rfl⟩ : syracuseStep 1632859 = 2449289) B2449289
theorem B15698731 : Blo 1632515 15698731 := bstep (se 1 (by rfl) ⟨11774048, by rfl⟩ : syracuseStep 15698731 = 23548097) B23548097
theorem B14142319 : Blo 1632515 14142319 := bstep (se 1 (by rfl) ⟨10606739, by rfl⟩ : syracuseStep 14142319 = 21213479) B21213479
theorem B2755775 : Blo 1632515 2755775 := bstep (se 1 (by rfl) ⟨2066831, by rfl⟩ : syracuseStep 2755775 = 4133663) B4133663
theorem B2067707 : Blo 1632515 2067707 := bstep (se 1 (by rfl) ⟨1550780, by rfl⟩ : syracuseStep 2067707 = 3101561) B3101561
theorem B1633639 : Blo 1632515 1633639 := bstep (se 1 (by rfl) ⟨1225229, by rfl⟩ : syracuseStep 1633639 = 2450459) B2450459
theorem B13955111 : Blo 1632515 13955111 := bstep (se 1 (by rfl) ⟨10466333, by rfl⟩ : syracuseStep 13955111 = 20932667) B20932667
theorem B3674447 : Blo 1632515 3674447 := bstep (se 1 (by rfl) ⟨2755835, by rfl⟩ : syracuseStep 3674447 = 5511671) B5511671
theorem B4134017 : Blo 1632515 4134017 := bstep (se 2 (by rfl) ⟨1550256, by rfl⟩ : syracuseStep 4134017 = 3100513) B3100513
theorem B3675401 : Blo 1632515 3675401 := bstep (se 2 (by rfl) ⟨1378275, by rfl⟩ : syracuseStep 3675401 = 2756551) B2756551
theorem B4134503 : Blo 1632515 4134503 := bstep (se 1 (by rfl) ⟨3100877, by rfl⟩ : syracuseStep 4134503 = 6201755) B6201755
theorem B35321453 : Blo 1632515 35321453 := bstep (se 3 (by rfl) ⟨6622772, by rfl⟩ : syracuseStep 35321453 = 13245545) B13245545
theorem B4134959 : Blo 1632515 4134959 := bstep (se 1 (by rfl) ⟨3101219, by rfl⟩ : syracuseStep 4134959 = 6202439) B6202439
theorem B135879353 : Blo 1632515 135879353 := bstep (se 2 (by rfl) ⟨50954757, by rfl⟩ : syracuseStep 135879353 = 101909515) B101909515
theorem B20937791 : Blo 1632515 20937791 := bstep (se 1 (by rfl) ⟨15703343, by rfl⟩ : syracuseStep 20937791 = 31406687) B31406687
theorem B5512265 : Blo 1632515 5512265 := bstep (se 2 (by rfl) ⟨2067099, by rfl⟩ : syracuseStep 5512265 = 4134199) B4134199
theorem B52960391 : Blo 1632515 52960391 := bstep (se 1 (by rfl) ⟨39720293, by rfl⟩ : syracuseStep 52960391 = 79440587) B79440587
theorem B17653115 : Blo 1632515 17653115 := bstep (se 1 (by rfl) ⟨13239836, by rfl⟩ : syracuseStep 17653115 = 26479673) B26479673
theorem B1145421431 : Blo 1632515 1145421431 := bstep (se 1 (by rfl) ⟨859066073, by rfl⟩ : syracuseStep 1145421431 = 1718132147) B1718132147
theorem B14900921 : Blo 1632515 14900921 := bstep (se 2 (by rfl) ⟨5587845, by rfl⟩ : syracuseStep 14900921 = 11175691) B11175691
theorem B2449631 : Blo 1632515 2449631 := bstep (se 1 (by rfl) ⟨1837223, by rfl⟩ : syracuseStep 2449631 = 3674447) B3674447
theorem B5513885 : Blo 1632515 5513885 := bstep (se 3 (by rfl) ⟨1033853, by rfl⟩ : syracuseStep 5513885 = 2067707) B2067707
theorem B2450267 : Blo 1632515 2450267 := bstep (se 1 (by rfl) ⟨1837700, by rfl⟩ : syracuseStep 2450267 = 3675401) B3675401
theorem B20931641 : Blo 1632515 20931641 := bstep (se 2 (by rfl) ⟨7849365, by rfl⟩ : syracuseStep 20931641 = 15698731) B15698731
theorem B75425701 : Blo 1632515 75425701 := bstep (se 4 (by rfl) ⟨7071159, by rfl⟩ : syracuseStep 75425701 = 14142319) B14142319
theorem B1837183 : Blo 1632515 1837183 := bstep (se 1 (by rfl) ⟨1377887, by rfl⟩ : syracuseStep 1837183 = 2755775) B2755775
theorem B39717377 : Blo 1632515 39717377 := bstep (se 2 (by rfl) ⟨14894016, by rfl⟩ : syracuseStep 39717377 = 29788033) B29788033
theorem B2944031 : Blo 1632515 2944031 := bstep (se 1 (by rfl) ⟨2208023, by rfl⟩ : syracuseStep 2944031 = 4416047) B4416047
theorem B59600279 : Blo 1632515 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B2756011 : Blo 1632515 2756011 := bstep (se 1 (by rfl) ⟨2067008, by rfl⟩ : syracuseStep 2756011 = 4134017) B4134017
theorem B27897371 : Blo 1632515 27897371 := bstep (se 1 (by rfl) ⟨20923028, by rfl⟩ : syracuseStep 27897371 = 41846057) B41846057
theorem B2756335 : Blo 1632515 2756335 := bstep (se 1 (by rfl) ⟨2067251, by rfl⟩ : syracuseStep 2756335 = 4134503) B4134503
theorem B23547635 : Blo 1632515 23547635 := bstep (se 1 (by rfl) ⟨17660726, by rfl⟩ : syracuseStep 23547635 = 35321453) B35321453
theorem B21507929 : Blo 1632515 21507929 := bstep (se 2 (by rfl) ⟨8065473, by rfl⟩ : syracuseStep 21507929 = 16130947) B16130947
theorem B2756639 : Blo 1632515 2756639 := bstep (se 1 (by rfl) ⟨2067479, by rfl⟩ : syracuseStep 2756639 = 4134959) B4134959
theorem B3674843 : Blo 1632515 3674843 := bstep (se 1 (by rfl) ⟨2756132, by rfl⟩ : syracuseStep 3674843 = 5512265) B5512265
theorem B11768743 : Blo 1632515 11768743 := bstep (se 1 (by rfl) ⟨8826557, by rfl⟩ : syracuseStep 11768743 = 17653115) B17653115
theorem B763614287 : Blo 1632515 763614287 := bstep (se 1 (by rfl) ⟨572710715, by rfl⟩ : syracuseStep 763614287 = 1145421431) B1145421431
theorem B9933947 : Blo 1632515 9933947 := bstep (se 1 (by rfl) ⟨7450460, by rfl⟩ : syracuseStep 9933947 = 14900921) B14900921
theorem B9303407 : Blo 1632515 9303407 := bstep (se 1 (by rfl) ⟨6977555, by rfl⟩ : syracuseStep 9303407 = 13955111) B13955111
theorem B3676031 : Blo 1632515 3676031 := bstep (se 1 (by rfl) ⟨2757023, by rfl⟩ : syracuseStep 3676031 = 5514047) B5514047
theorem B4135819 : Blo 1632515 4135819 := bstep (se 1 (by rfl) ⟨3101864, by rfl⟩ : syracuseStep 4135819 = 6203729) B6203729
theorem B90586235 : Blo 1632515 90586235 := bstep (se 1 (by rfl) ⟨67939676, by rfl⟩ : syracuseStep 90586235 = 135879353) B135879353
theorem B13958527 : Blo 1632515 13958527 := bstep (se 1 (by rfl) ⟨10468895, by rfl⟩ : syracuseStep 13958527 = 20937791) B20937791
theorem B35306927 : Blo 1632515 35306927 := bstep (se 1 (by rfl) ⟨26480195, by rfl⟩ : syracuseStep 35306927 = 52960391) B52960391
theorem B2449577 : Blo 1632515 2449577 := bstep (se 2 (by rfl) ⟨918591, by rfl⟩ : syracuseStep 2449577 = 1837183) B1837183
theorem B2449895 : Blo 1632515 2449895 := bstep (se 1 (by rfl) ⟨1837421, by rfl⟩ : syracuseStep 2449895 = 3674843) B3674843
theorem B509076191 : Blo 1632515 509076191 := bstep (se 1 (by rfl) ⟨381807143, by rfl⟩ : syracuseStep 509076191 = 763614287) B763614287
theorem B6202271 : Blo 1632515 6202271 := bstep (se 1 (by rfl) ⟨4651703, by rfl⟩ : syracuseStep 6202271 = 9303407) B9303407
theorem B5514425 : Blo 1632515 5514425 := bstep (se 2 (by rfl) ⟨2067909, by rfl⟩ : syracuseStep 5514425 = 4135819) B4135819
theorem B2450687 : Blo 1632515 2450687 := bstep (se 1 (by rfl) ⟨1838015, by rfl⟩ : syracuseStep 2450687 = 3676031) B3676031
theorem B26478251 : Blo 1632515 26478251 := bstep (se 1 (by rfl) ⟨19858688, by rfl⟩ : syracuseStep 26478251 = 39717377) B39717377
theorem B39733519 : Blo 1632515 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B23537951 : Blo 1632515 23537951 := bstep (se 1 (by rfl) ⟨17653463, by rfl⟩ : syracuseStep 23537951 = 35306927) B35306927
theorem B18598247 : Blo 1632515 18598247 := bstep (se 1 (by rfl) ⟨13948685, by rfl⟩ : syracuseStep 18598247 = 27897371) B27897371
theorem B15698423 : Blo 1632515 15698423 := bstep (se 1 (by rfl) ⟨11773817, by rfl⟩ : syracuseStep 15698423 = 23547635) B23547635
theorem B100567601 : Blo 1632515 100567601 := bstep (se 2 (by rfl) ⟨37712850, by rfl⟩ : syracuseStep 100567601 = 75425701) B75425701
theorem B14338619 : Blo 1632515 14338619 := bstep (se 1 (by rfl) ⟨10753964, by rfl⟩ : syracuseStep 14338619 = 21507929) B21507929
theorem B1837759 : Blo 1632515 1837759 := bstep (se 1 (by rfl) ⟨1378319, by rfl⟩ : syracuseStep 1837759 = 2756639) B2756639
theorem B1633087 : Blo 1632515 1633087 := bstep (se 1 (by rfl) ⟨1224815, by rfl⟩ : syracuseStep 1633087 = 2449631) B2449631
theorem B31402997 : Blo 1632515 31402997 := bstep (se 5 (by rfl) ⟨1472015, by rfl⟩ : syracuseStep 31402997 = 2944031) B2944031
theorem B1633511 : Blo 1632515 1633511 := bstep (se 1 (by rfl) ⟨1225133, by rfl⟩ : syracuseStep 1633511 = 2450267) B2450267
theorem B13954427 : Blo 1632515 13954427 := bstep (se 1 (by rfl) ⟨10465820, by rfl⟩ : syracuseStep 13954427 = 20931641) B20931641
theorem B6622631 : Blo 1632515 6622631 := bstep (se 1 (by rfl) ⟨4966973, by rfl⟩ : syracuseStep 6622631 = 9933947) B9933947
theorem B15691657 : Blo 1632515 15691657 := bstep (se 2 (by rfl) ⟨5884371, by rfl⟩ : syracuseStep 15691657 = 11768743) B11768743
theorem B3674681 : Blo 1632515 3674681 := bstep (se 2 (by rfl) ⟨1378005, by rfl⟩ : syracuseStep 3674681 = 2756011) B2756011
theorem B3675113 : Blo 1632515 3675113 := bstep (se 2 (by rfl) ⟨1378167, by rfl⟩ : syracuseStep 3675113 = 2756335) B2756335
theorem B241563293 : Blo 1632515 241563293 := bstep (se 3 (by rfl) ⟨45293117, by rfl⟩ : syracuseStep 241563293 = 90586235) B90586235
theorem B3675923 : Blo 1632515 3675923 := bstep (se 1 (by rfl) ⟨2756942, by rfl⟩ : syracuseStep 3675923 = 5513885) B5513885
theorem B18611369 : Blo 1632515 18611369 := bstep (se 2 (by rfl) ⟨6979263, by rfl⟩ : syracuseStep 18611369 = 13958527) B13958527
theorem B52978025 : Blo 1632515 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B2449787 : Blo 1632515 2449787 := bstep (se 1 (by rfl) ⟨1837340, by rfl⟩ : syracuseStep 2449787 = 3674681) B3674681
theorem B2450075 : Blo 1632515 2450075 := bstep (se 1 (by rfl) ⟨1837556, by rfl⟩ : syracuseStep 2450075 = 3675113) B3675113
theorem B2450345 : Blo 1632515 2450345 := bstep (se 2 (by rfl) ⟨918879, by rfl⟩ : syracuseStep 2450345 = 1837759) B1837759
theorem B2450615 : Blo 1632515 2450615 := bstep (se 1 (by rfl) ⟨1837961, by rfl⟩ : syracuseStep 2450615 = 3675923) B3675923
theorem B67045067 : Blo 1632515 67045067 := bstep (se 1 (by rfl) ⟨50283800, by rfl⟩ : syracuseStep 67045067 = 100567601) B100567601
theorem B1633051 : Blo 1632515 1633051 := bstep (se 1 (by rfl) ⟨1224788, by rfl⟩ : syracuseStep 1633051 = 2449577) B2449577
theorem B1633263 : Blo 1632515 1633263 := bstep (se 1 (by rfl) ⟨1224947, by rfl⟩ : syracuseStep 1633263 = 2449895) B2449895
theorem B1633791 : Blo 1632515 1633791 := bstep (se 1 (by rfl) ⟨1225343, by rfl⟩ : syracuseStep 1633791 = 2450687) B2450687
theorem B161042195 : Blo 1632515 161042195 := bstep (se 1 (by rfl) ⟨120781646, by rfl⟩ : syracuseStep 161042195 = 241563293) B241563293
theorem B15691967 : Blo 1632515 15691967 := bstep (se 1 (by rfl) ⟨11768975, by rfl⟩ : syracuseStep 15691967 = 23537951) B23537951
theorem B12398831 : Blo 1632515 12398831 := bstep (se 1 (by rfl) ⟨9299123, by rfl⟩ : syracuseStep 12398831 = 18598247) B18598247
theorem B10465615 : Blo 1632515 10465615 := bstep (se 1 (by rfl) ⟨7849211, by rfl⟩ : syracuseStep 10465615 = 15698423) B15698423
theorem B20935331 : Blo 1632515 20935331 := bstep (se 1 (by rfl) ⟨15701498, by rfl⟩ : syracuseStep 20935331 = 31402997) B31402997
theorem B12407579 : Blo 1632515 12407579 := bstep (se 1 (by rfl) ⟨9305684, by rfl⟩ : syracuseStep 12407579 = 18611369) B18611369
theorem B9302951 : Blo 1632515 9302951 := bstep (se 1 (by rfl) ⟨6977213, by rfl⟩ : syracuseStep 9302951 = 13954427) B13954427
theorem B339384127 : Blo 1632515 339384127 := bstep (se 1 (by rfl) ⟨254538095, by rfl⟩ : syracuseStep 339384127 = 509076191) B509076191
theorem B4134847 : Blo 1632515 4134847 := bstep (se 1 (by rfl) ⟨3101135, by rfl⟩ : syracuseStep 4134847 = 6202271) B6202271
theorem B3676283 : Blo 1632515 3676283 := bstep (se 1 (by rfl) ⟨2757212, by rfl⟩ : syracuseStep 3676283 = 5514425) B5514425
theorem B17652167 : Blo 1632515 17652167 := bstep (se 1 (by rfl) ⟨13239125, by rfl⟩ : syracuseStep 17652167 = 26478251) B26478251
theorem B9559079 : Blo 1632515 9559079 := bstep (se 1 (by rfl) ⟨7169309, by rfl⟩ : syracuseStep 9559079 = 14338619) B14338619
theorem B4415087 : Blo 1632515 4415087 := bstep (se 1 (by rfl) ⟨3311315, by rfl⟩ : syracuseStep 4415087 = 6622631) B6622631
theorem B20922209 : Blo 1632515 20922209 := bstep (se 2 (by rfl) ⟨7845828, by rfl⟩ : syracuseStep 20922209 = 15691657) B15691657
theorem B10461311 : Blo 1632515 10461311 := bstep (se 1 (by rfl) ⟨7845983, by rfl⟩ : syracuseStep 10461311 = 15691967) B15691967
theorem B8265887 : Blo 1632515 8265887 := bstep (se 1 (by rfl) ⟨6199415, by rfl⟩ : syracuseStep 8265887 = 12398831) B12398831
theorem B6201967 : Blo 1632515 6201967 := bstep (se 1 (by rfl) ⟨4651475, by rfl⟩ : syracuseStep 6201967 = 9302951) B9302951
theorem B44696711 : Blo 1632515 44696711 := bstep (se 1 (by rfl) ⟨33522533, by rfl⟩ : syracuseStep 44696711 = 67045067) B67045067
theorem B2450855 : Blo 1632515 2450855 := bstep (se 1 (by rfl) ⟨1838141, by rfl⟩ : syracuseStep 2450855 = 3676283) B3676283
theorem B2943391 : Blo 1632515 2943391 := bstep (se 1 (by rfl) ⟨2207543, by rfl⟩ : syracuseStep 2943391 = 4415087) B4415087
theorem B452512169 : Blo 1632515 452512169 := bstep (se 2 (by rfl) ⟨169692063, by rfl⟩ : syracuseStep 452512169 = 339384127) B339384127
theorem B35318683 : Blo 1632515 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B1633191 : Blo 1632515 1633191 := bstep (se 1 (by rfl) ⟨1224893, by rfl⟩ : syracuseStep 1633191 = 2449787) B2449787
theorem B1633383 : Blo 1632515 1633383 := bstep (se 1 (by rfl) ⟨1225037, by rfl⟩ : syracuseStep 1633383 = 2450075) B2450075
theorem B13954153 : Blo 1632515 13954153 := bstep (se 2 (by rfl) ⟨5232807, by rfl⟩ : syracuseStep 13954153 = 10465615) B10465615
theorem B1633563 : Blo 1632515 1633563 := bstep (se 1 (by rfl) ⟨1225172, by rfl⟩ : syracuseStep 1633563 = 2450345) B2450345
theorem B1633743 : Blo 1632515 1633743 := bstep (se 1 (by rfl) ⟨1225307, by rfl⟩ : syracuseStep 1633743 = 2450615) B2450615
theorem B11768111 : Blo 1632515 11768111 := bstep (se 1 (by rfl) ⟨8826083, by rfl⟩ : syracuseStep 11768111 = 17652167) B17652167
theorem B107361463 : Blo 1632515 107361463 := bstep (se 1 (by rfl) ⟨80521097, by rfl⟩ : syracuseStep 107361463 = 161042195) B161042195
theorem B13948139 : Blo 1632515 13948139 := bstep (se 1 (by rfl) ⟨10461104, by rfl⟩ : syracuseStep 13948139 = 20922209) B20922209
theorem B13956887 : Blo 1632515 13956887 := bstep (se 1 (by rfl) ⟨10467665, by rfl⟩ : syracuseStep 13956887 = 20935331) B20935331
theorem B8271719 : Blo 1632515 8271719 := bstep (se 1 (by rfl) ⟨6203789, by rfl⟩ : syracuseStep 8271719 = 12407579) B12407579
theorem B6372719 : Blo 1632515 6372719 := bstep (se 1 (by rfl) ⟨4779539, by rfl⟩ : syracuseStep 6372719 = 9559079) B9559079
theorem B5513129 : Blo 1632515 5513129 := bstep (se 2 (by rfl) ⟨2067423, by rfl⟩ : syracuseStep 5513129 = 4134847) B4134847
theorem B3924521 : Blo 1632515 3924521 := bstep (se 2 (by rfl) ⟨1471695, by rfl⟩ : syracuseStep 3924521 = 2943391) B2943391
theorem B9298759 : Blo 1632515 9298759 := bstep (se 1 (by rfl) ⟨6974069, by rfl⟩ : syracuseStep 9298759 = 13948139) B13948139
theorem B5514479 : Blo 1632515 5514479 := bstep (se 1 (by rfl) ⟨4135859, by rfl⟩ : syracuseStep 5514479 = 8271719) B8271719
theorem B18605537 : Blo 1632515 18605537 := bstep (se 2 (by rfl) ⟨6977076, by rfl⟩ : syracuseStep 18605537 = 13954153) B13954153
theorem B143148617 : Blo 1632515 143148617 := bstep (se 2 (by rfl) ⟨53680731, by rfl⟩ : syracuseStep 143148617 = 107361463) B107361463
theorem B6974207 : Blo 1632515 6974207 := bstep (se 1 (by rfl) ⟨5230655, by rfl⟩ : syracuseStep 6974207 = 10461311) B10461311
theorem B29797807 : Blo 1632515 29797807 := bstep (se 1 (by rfl) ⟨22348355, by rfl⟩ : syracuseStep 29797807 = 44696711) B44696711
theorem B8269289 : Blo 1632515 8269289 := bstep (se 2 (by rfl) ⟨3100983, by rfl⟩ : syracuseStep 8269289 = 6201967) B6201967
theorem B1633903 : Blo 1632515 1633903 := bstep (se 1 (by rfl) ⟨1225427, by rfl⟩ : syracuseStep 1633903 = 2450855) B2450855
theorem B47091577 : Blo 1632515 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B301674779 : Blo 1632515 301674779 := bstep (se 1 (by rfl) ⟨226256084, by rfl⟩ : syracuseStep 301674779 = 452512169) B452512169
theorem B4248479 : Blo 1632515 4248479 := bstep (se 1 (by rfl) ⟨3186359, by rfl⟩ : syracuseStep 4248479 = 6372719) B6372719
theorem B3675419 : Blo 1632515 3675419 := bstep (se 1 (by rfl) ⟨2756564, by rfl⟩ : syracuseStep 3675419 = 5513129) B5513129
theorem B5510591 : Blo 1632515 5510591 := bstep (se 1 (by rfl) ⟨4132943, by rfl⟩ : syracuseStep 5510591 = 8265887) B8265887
theorem B7845407 : Blo 1632515 7845407 := bstep (se 1 (by rfl) ⟨5884055, by rfl⟩ : syracuseStep 7845407 = 11768111) B11768111
theorem B9304591 : Blo 1632515 9304591 := bstep (se 1 (by rfl) ⟨6978443, by rfl⟩ : syracuseStep 9304591 = 13956887) B13956887
theorem B2450279 : Blo 1632515 2450279 := bstep (se 1 (by rfl) ⟨1837709, by rfl⟩ : syracuseStep 2450279 = 3675419) B3675419
theorem B12403691 : Blo 1632515 12403691 := bstep (se 1 (by rfl) ⟨9302768, by rfl⟩ : syracuseStep 12403691 = 18605537) B18605537
theorem B201116519 : Blo 1632515 201116519 := bstep (se 1 (by rfl) ⟨150837389, by rfl⟩ : syracuseStep 201116519 = 301674779) B301674779
theorem B2616347 : Blo 1632515 2616347 := bstep (se 1 (by rfl) ⟨1962260, by rfl⟩ : syracuseStep 2616347 = 3924521) B3924521
theorem B12406121 : Blo 1632515 12406121 := bstep (se 2 (by rfl) ⟨4652295, by rfl⟩ : syracuseStep 12406121 = 9304591) B9304591
theorem B3673727 : Blo 1632515 3673727 := bstep (se 1 (by rfl) ⟨2755295, by rfl⟩ : syracuseStep 3673727 = 5510591) B5510591
theorem B5230271 : Blo 1632515 5230271 := bstep (se 1 (by rfl) ⟨3922703, by rfl⟩ : syracuseStep 5230271 = 7845407) B7845407
theorem B95432411 : Blo 1632515 95432411 := bstep (se 1 (by rfl) ⟨71574308, by rfl⟩ : syracuseStep 95432411 = 143148617) B143148617
theorem B12398345 : Blo 1632515 12398345 := bstep (se 2 (by rfl) ⟨4649379, by rfl⟩ : syracuseStep 12398345 = 9298759) B9298759
theorem B4649471 : Blo 1632515 4649471 := bstep (se 1 (by rfl) ⟨3487103, by rfl⟩ : syracuseStep 4649471 = 6974207) B6974207
theorem B62788769 : Blo 1632515 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B2832319 : Blo 1632515 2832319 := bstep (se 1 (by rfl) ⟨2124239, by rfl⟩ : syracuseStep 2832319 = 4248479) B4248479
theorem B3676319 : Blo 1632515 3676319 := bstep (se 1 (by rfl) ⟨2757239, by rfl⟩ : syracuseStep 3676319 = 5514479) B5514479
theorem B39730409 : Blo 1632515 39730409 := bstep (se 2 (by rfl) ⟨14898903, by rfl⟩ : syracuseStep 39730409 = 29797807) B29797807
theorem B5512859 : Blo 1632515 5512859 := bstep (se 1 (by rfl) ⟨4134644, by rfl⟩ : syracuseStep 5512859 = 8269289) B8269289
theorem B2450879 : Blo 1632515 2450879 := bstep (se 1 (by rfl) ⟨1838159, by rfl⟩ : syracuseStep 2450879 = 3676319) B3676319
theorem B26486939 : Blo 1632515 26486939 := bstep (se 1 (by rfl) ⟨19865204, by rfl⟩ : syracuseStep 26486939 = 39730409) B39730409
theorem B63621607 : Blo 1632515 63621607 := bstep (se 1 (by rfl) ⟨47716205, by rfl⟩ : syracuseStep 63621607 = 95432411) B95432411
theorem B3099647 : Blo 1632515 3099647 := bstep (se 1 (by rfl) ⟨2324735, by rfl⟩ : syracuseStep 3099647 = 4649471) B4649471
theorem B1633519 : Blo 1632515 1633519 := bstep (se 1 (by rfl) ⟨1225139, by rfl⟩ : syracuseStep 1633519 = 2450279) B2450279
theorem B8269127 : Blo 1632515 8269127 := bstep (se 1 (by rfl) ⟨6201845, by rfl⟩ : syracuseStep 8269127 = 12403691) B12403691
theorem B13947389 : Blo 1632515 13947389 := bstep (se 3 (by rfl) ⟨2615135, by rfl⟩ : syracuseStep 13947389 = 5230271) B5230271
theorem B8270747 : Blo 1632515 8270747 := bstep (se 1 (by rfl) ⟨6203060, by rfl⟩ : syracuseStep 8270747 = 12406121) B12406121
theorem B3675239 : Blo 1632515 3675239 := bstep (se 1 (by rfl) ⟨2756429, by rfl⟩ : syracuseStep 3675239 = 5512859) B5512859
theorem B6976925 : Blo 1632515 6976925 := bstep (se 3 (by rfl) ⟨1308173, by rfl⟩ : syracuseStep 6976925 = 2616347) B2616347
theorem B41859179 : Blo 1632515 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B134077679 : Blo 1632515 134077679 := bstep (se 1 (by rfl) ⟨100558259, by rfl⟩ : syracuseStep 134077679 = 201116519) B201116519
theorem B2449151 : Blo 1632515 2449151 := bstep (se 1 (by rfl) ⟨1836863, by rfl⟩ : syracuseStep 2449151 = 3673727) B3673727
theorem B8265563 : Blo 1632515 8265563 := bstep (se 1 (by rfl) ⟨6199172, by rfl⟩ : syracuseStep 8265563 = 12398345) B12398345
theorem B3776425 : Blo 1632515 3776425 := bstep (se 2 (by rfl) ⟨1416159, by rfl⟩ : syracuseStep 3776425 = 2832319) B2832319
theorem B9298259 : Blo 1632515 9298259 := bstep (se 1 (by rfl) ⟨6973694, by rfl⟩ : syracuseStep 9298259 = 13947389) B13947389
theorem B5513831 : Blo 1632515 5513831 := bstep (se 1 (by rfl) ⟨4135373, by rfl⟩ : syracuseStep 5513831 = 8270747) B8270747
theorem B84828809 : Blo 1632515 84828809 := bstep (se 2 (by rfl) ⟨31810803, by rfl⟩ : syracuseStep 84828809 = 63621607) B63621607
theorem B2450159 : Blo 1632515 2450159 := bstep (se 1 (by rfl) ⟨1837619, by rfl⟩ : syracuseStep 2450159 = 3675239) B3675239
theorem B89385119 : Blo 1632515 89385119 := bstep (se 1 (by rfl) ⟨67038839, by rfl⟩ : syracuseStep 89385119 = 134077679) B134077679
theorem B1632767 : Blo 1632515 1632767 := bstep (se 1 (by rfl) ⟨1224575, by rfl⟩ : syracuseStep 1632767 = 2449151) B2449151
theorem B1633919 : Blo 1632515 1633919 := bstep (se 1 (by rfl) ⟨1225439, by rfl⟩ : syracuseStep 1633919 = 2450879) B2450879
theorem B27906119 : Blo 1632515 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B17657959 : Blo 1632515 17657959 := bstep (se 1 (by rfl) ⟨13243469, by rfl⟩ : syracuseStep 17657959 = 26486939) B26486939
theorem B20140933 : Blo 1632515 20140933 := bstep (se 4 (by rfl) ⟨1888212, by rfl⟩ : syracuseStep 20140933 = 3776425) B3776425
theorem B5510375 : Blo 1632515 5510375 := bstep (se 1 (by rfl) ⟨4132781, by rfl⟩ : syracuseStep 5510375 = 8265563) B8265563
theorem B4651283 : Blo 1632515 4651283 := bstep (se 1 (by rfl) ⟨3488462, by rfl⟩ : syracuseStep 4651283 = 6976925) B6976925
theorem B5512751 : Blo 1632515 5512751 := bstep (se 1 (by rfl) ⟨4134563, by rfl⟩ : syracuseStep 5512751 = 8269127) B8269127
theorem B8265725 : Blo 1632515 8265725 := bstep (se 3 (by rfl) ⟨1549823, by rfl⟩ : syracuseStep 8265725 = 3099647) B3099647
theorem B18604079 : Blo 1632515 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B23543945 : Blo 1632515 23543945 := bstep (se 2 (by rfl) ⟨8828979, by rfl⟩ : syracuseStep 23543945 = 17657959) B17657959
theorem B26854577 : Blo 1632515 26854577 := bstep (se 2 (by rfl) ⟨10070466, by rfl⟩ : syracuseStep 26854577 = 20140933) B20140933
theorem B59590079 : Blo 1632515 59590079 := bstep (se 1 (by rfl) ⟨44692559, by rfl⟩ : syracuseStep 59590079 = 89385119) B89385119
theorem B1633439 : Blo 1632515 1633439 := bstep (se 1 (by rfl) ⟨1225079, by rfl⟩ : syracuseStep 1633439 = 2450159) B2450159
theorem B3673583 : Blo 1632515 3673583 := bstep (se 1 (by rfl) ⟨2755187, by rfl⟩ : syracuseStep 3673583 = 5510375) B5510375
theorem B3100855 : Blo 1632515 3100855 := bstep (se 1 (by rfl) ⟨2325641, by rfl⟩ : syracuseStep 3100855 = 4651283) B4651283
theorem B226210157 : Blo 1632515 226210157 := bstep (se 3 (by rfl) ⟨42414404, by rfl⟩ : syracuseStep 226210157 = 84828809) B84828809
theorem B3675167 : Blo 1632515 3675167 := bstep (se 1 (by rfl) ⟨2756375, by rfl⟩ : syracuseStep 3675167 = 5512751) B5512751
theorem B5510483 : Blo 1632515 5510483 := bstep (se 1 (by rfl) ⟨4132862, by rfl⟩ : syracuseStep 5510483 = 8265725) B8265725
theorem B6198839 : Blo 1632515 6198839 := bstep (se 1 (by rfl) ⟨4649129, by rfl⟩ : syracuseStep 6198839 = 9298259) B9298259
theorem B3675887 : Blo 1632515 3675887 := bstep (se 1 (by rfl) ⟨2756915, by rfl⟩ : syracuseStep 3675887 = 5513831) B5513831
theorem B12402719 : Blo 1632515 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B15695963 : Blo 1632515 15695963 := bstep (se 1 (by rfl) ⟨11771972, by rfl⟩ : syracuseStep 15695963 = 23543945) B23543945
theorem B150806771 : Blo 1632515 150806771 := bstep (se 1 (by rfl) ⟨113105078, by rfl⟩ : syracuseStep 150806771 = 226210157) B226210157
theorem B2450111 : Blo 1632515 2450111 := bstep (se 1 (by rfl) ⟨1837583, by rfl⟩ : syracuseStep 2450111 = 3675167) B3675167
theorem B2450591 : Blo 1632515 2450591 := bstep (se 1 (by rfl) ⟨1837943, by rfl⟩ : syracuseStep 2450591 = 3675887) B3675887
theorem B17903051 : Blo 1632515 17903051 := bstep (se 1 (by rfl) ⟨13427288, by rfl⟩ : syracuseStep 17903051 = 26854577) B26854577
theorem B3673655 : Blo 1632515 3673655 := bstep (se 1 (by rfl) ⟨2755241, by rfl⟩ : syracuseStep 3673655 = 5510483) B5510483
theorem B39726719 : Blo 1632515 39726719 := bstep (se 1 (by rfl) ⟨29795039, by rfl⟩ : syracuseStep 39726719 = 59590079) B59590079
theorem B4132559 : Blo 1632515 4132559 := bstep (se 1 (by rfl) ⟨3099419, by rfl⟩ : syracuseStep 4132559 = 6198839) B6198839
theorem B4134473 : Blo 1632515 4134473 := bstep (se 2 (by rfl) ⟨1550427, by rfl⟩ : syracuseStep 4134473 = 3100855) B3100855
theorem B2449055 : Blo 1632515 2449055 := bstep (se 1 (by rfl) ⟨1836791, by rfl⟩ : syracuseStep 2449055 = 3673583) B3673583
theorem B1632703 : Blo 1632515 1632703 := bstep (se 1 (by rfl) ⟨1224527, by rfl⟩ : syracuseStep 1632703 = 2449055) B2449055
theorem B2755039 : Blo 1632515 2755039 := bstep (se 1 (by rfl) ⟨2066279, by rfl⟩ : syracuseStep 2755039 = 4132559) B4132559
theorem B8268479 : Blo 1632515 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B10463975 : Blo 1632515 10463975 := bstep (se 1 (by rfl) ⟨7847981, by rfl⟩ : syracuseStep 10463975 = 15695963) B15695963
theorem B1633407 : Blo 1632515 1633407 := bstep (se 1 (by rfl) ⟨1225055, by rfl⟩ : syracuseStep 1633407 = 2450111) B2450111
theorem B1633727 : Blo 1632515 1633727 := bstep (se 1 (by rfl) ⟨1225295, by rfl⟩ : syracuseStep 1633727 = 2450591) B2450591
theorem B2756315 : Blo 1632515 2756315 := bstep (se 1 (by rfl) ⟨2067236, by rfl⟩ : syracuseStep 2756315 = 4134473) B4134473
theorem B100537847 : Blo 1632515 100537847 := bstep (se 1 (by rfl) ⟨75403385, by rfl⟩ : syracuseStep 100537847 = 150806771) B150806771
theorem B11935367 : Blo 1632515 11935367 := bstep (se 1 (by rfl) ⟨8951525, by rfl⟩ : syracuseStep 11935367 = 17903051) B17903051
theorem B2449103 : Blo 1632515 2449103 := bstep (se 1 (by rfl) ⟨1836827, by rfl⟩ : syracuseStep 2449103 = 3673655) B3673655
theorem B26484479 : Blo 1632515 26484479 := bstep (se 1 (by rfl) ⟨19863359, by rfl⟩ : syracuseStep 26484479 = 39726719) B39726719
theorem B7956911 : Blo 1632515 7956911 := bstep (se 1 (by rfl) ⟨5967683, by rfl⟩ : syracuseStep 7956911 = 11935367) B11935367
theorem B1632735 : Blo 1632515 1632735 := bstep (se 1 (by rfl) ⟨1224551, by rfl⟩ : syracuseStep 1632735 = 2449103) B2449103
theorem B1837543 : Blo 1632515 1837543 := bstep (se 1 (by rfl) ⟨1378157, by rfl⟩ : syracuseStep 1837543 = 2756315) B2756315
theorem B17656319 : Blo 1632515 17656319 := bstep (se 1 (by rfl) ⟨13242239, by rfl⟩ : syracuseStep 17656319 = 26484479) B26484479
theorem B3673385 : Blo 1632515 3673385 := bstep (se 2 (by rfl) ⟨1377519, by rfl⟩ : syracuseStep 3673385 = 2755039) B2755039
theorem B6975983 : Blo 1632515 6975983 := bstep (se 1 (by rfl) ⟨5231987, by rfl⟩ : syracuseStep 6975983 = 10463975) B10463975
theorem B67025231 : Blo 1632515 67025231 := bstep (se 1 (by rfl) ⟨50268923, by rfl⟩ : syracuseStep 67025231 = 100537847) B100537847
theorem B5512319 : Blo 1632515 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B2450057 : Blo 1632515 2450057 := bstep (se 2 (by rfl) ⟨918771, by rfl⟩ : syracuseStep 2450057 = 1837543) B1837543
theorem B21218429 : Blo 1632515 21218429 := bstep (se 3 (by rfl) ⟨3978455, by rfl⟩ : syracuseStep 21218429 = 7956911) B7956911
theorem B44683487 : Blo 1632515 44683487 := bstep (se 1 (by rfl) ⟨33512615, by rfl⟩ : syracuseStep 44683487 = 67025231) B67025231
theorem B3674879 : Blo 1632515 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B18602621 : Blo 1632515 18602621 := bstep (se 3 (by rfl) ⟨3487991, by rfl⟩ : syracuseStep 18602621 = 6975983) B6975983
theorem B11770879 : Blo 1632515 11770879 := bstep (se 1 (by rfl) ⟨8828159, by rfl⟩ : syracuseStep 11770879 = 17656319) B17656319
theorem B2448923 : Blo 1632515 2448923 := bstep (se 1 (by rfl) ⟨1836692, by rfl⟩ : syracuseStep 2448923 = 3673385) B3673385
theorem B2449919 : Blo 1632515 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B1632615 : Blo 1632515 1632615 := bstep (se 1 (by rfl) ⟨1224461, by rfl⟩ : syracuseStep 1632615 = 2448923) B2448923
theorem B29788991 : Blo 1632515 29788991 := bstep (se 1 (by rfl) ⟨22341743, by rfl⟩ : syracuseStep 29788991 = 44683487) B44683487
theorem B1633371 : Blo 1632515 1633371 := bstep (se 1 (by rfl) ⟨1225028, by rfl⟩ : syracuseStep 1633371 = 2450057) B2450057
theorem B14145619 : Blo 1632515 14145619 := bstep (se 1 (by rfl) ⟨10609214, by rfl⟩ : syracuseStep 14145619 = 21218429) B21218429
theorem B15694505 : Blo 1632515 15694505 := bstep (se 2 (by rfl) ⟨5885439, by rfl⟩ : syracuseStep 15694505 = 11770879) B11770879
theorem B12401747 : Blo 1632515 12401747 := bstep (se 1 (by rfl) ⟨9301310, by rfl⟩ : syracuseStep 12401747 = 18602621) B18602621
theorem B10463003 : Blo 1632515 10463003 := bstep (se 1 (by rfl) ⟨7847252, by rfl⟩ : syracuseStep 10463003 = 15694505) B15694505
theorem B19859327 : Blo 1632515 19859327 := bstep (se 1 (by rfl) ⟨14894495, by rfl⟩ : syracuseStep 19859327 = 29788991) B29788991
theorem B8267831 : Blo 1632515 8267831 := bstep (se 1 (by rfl) ⟨6200873, by rfl⟩ : syracuseStep 8267831 = 12401747) B12401747
theorem B18860825 : Blo 1632515 18860825 := bstep (se 2 (by rfl) ⟨7072809, by rfl⟩ : syracuseStep 18860825 = 14145619) B14145619
theorem B1633279 : Blo 1632515 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B13239551 : Blo 1632515 13239551 := bstep (se 1 (by rfl) ⟨9929663, by rfl⟩ : syracuseStep 13239551 = 19859327) B19859327
theorem B6975335 : Blo 1632515 6975335 := bstep (se 1 (by rfl) ⟨5231501, by rfl⟩ : syracuseStep 6975335 = 10463003) B10463003
theorem B5511887 : Blo 1632515 5511887 := bstep (se 1 (by rfl) ⟨4133915, by rfl⟩ : syracuseStep 5511887 = 8267831) B8267831
theorem B12573883 : Blo 1632515 12573883 := bstep (se 1 (by rfl) ⟨9430412, by rfl⟩ : syracuseStep 12573883 = 18860825) B18860825
theorem B8826367 : Blo 1632515 8826367 := bstep (se 1 (by rfl) ⟨6619775, by rfl⟩ : syracuseStep 8826367 = 13239551) B13239551
theorem B16765177 : Blo 1632515 16765177 := bstep (se 2 (by rfl) ⟨6286941, by rfl⟩ : syracuseStep 16765177 = 12573883) B12573883
theorem B3674591 : Blo 1632515 3674591 := bstep (se 1 (by rfl) ⟨2755943, by rfl⟩ : syracuseStep 3674591 = 5511887) B5511887
theorem B4650223 : Blo 1632515 4650223 := bstep (se 1 (by rfl) ⟨3487667, by rfl⟩ : syracuseStep 4650223 = 6975335) B6975335
theorem B2449727 : Blo 1632515 2449727 := bstep (se 1 (by rfl) ⟨1837295, by rfl⟩ : syracuseStep 2449727 = 3674591) B3674591
theorem B11768489 : Blo 1632515 11768489 := bstep (se 2 (by rfl) ⟨4413183, by rfl⟩ : syracuseStep 11768489 = 8826367) B8826367
theorem B22353569 : Blo 1632515 22353569 := bstep (se 2 (by rfl) ⟨8382588, by rfl⟩ : syracuseStep 22353569 = 16765177) B16765177
theorem B6200297 : Blo 1632515 6200297 := bstep (se 2 (by rfl) ⟨2325111, by rfl⟩ : syracuseStep 6200297 = 4650223) B4650223
theorem B14902379 : Blo 1632515 14902379 := bstep (se 1 (by rfl) ⟨11176784, by rfl⟩ : syracuseStep 14902379 = 22353569) B22353569
theorem B1633151 : Blo 1632515 1633151 := bstep (se 1 (by rfl) ⟨1224863, by rfl⟩ : syracuseStep 1633151 = 2449727) B2449727
theorem B4133531 : Blo 1632515 4133531 := bstep (se 1 (by rfl) ⟨3100148, by rfl⟩ : syracuseStep 4133531 = 6200297) B6200297
theorem B7845659 : Blo 1632515 7845659 := bstep (se 1 (by rfl) ⟨5884244, by rfl⟩ : syracuseStep 7845659 = 11768489) B11768489
theorem B2755687 : Blo 1632515 2755687 := bstep (se 1 (by rfl) ⟨2066765, by rfl⟩ : syracuseStep 2755687 = 4133531) B4133531
theorem B5230439 : Blo 1632515 5230439 := bstep (se 1 (by rfl) ⟨3922829, by rfl⟩ : syracuseStep 5230439 = 7845659) B7845659
theorem B9934919 : Blo 1632515 9934919 := bstep (se 1 (by rfl) ⟨7451189, by rfl⟩ : syracuseStep 9934919 = 14902379) B14902379
theorem B6623279 : Blo 1632515 6623279 := bstep (se 1 (by rfl) ⟨4967459, by rfl⟩ : syracuseStep 6623279 = 9934919) B9934919
theorem B3674249 : Blo 1632515 3674249 := bstep (se 2 (by rfl) ⟨1377843, by rfl⟩ : syracuseStep 3674249 = 2755687) B2755687
theorem B3486959 : Blo 1632515 3486959 := bstep (se 1 (by rfl) ⟨2615219, by rfl⟩ : syracuseStep 3486959 = 5230439) B5230439
theorem B4415519 : Blo 1632515 4415519 := bstep (se 1 (by rfl) ⟨3311639, by rfl⟩ : syracuseStep 4415519 = 6623279) B6623279
theorem B2449499 : Blo 1632515 2449499 := bstep (se 1 (by rfl) ⟨1837124, by rfl⟩ : syracuseStep 2449499 = 3674249) B3674249
theorem B2324639 : Blo 1632515 2324639 := bstep (se 1 (by rfl) ⟨1743479, by rfl⟩ : syracuseStep 2324639 = 3486959) B3486959
theorem B1632999 : Blo 1632515 1632999 := bstep (se 1 (by rfl) ⟨1224749, by rfl⟩ : syracuseStep 1632999 = 2449499) B2449499
theorem B11774717 : Blo 1632515 11774717 := bstep (se 3 (by rfl) ⟨2207759, by rfl⟩ : syracuseStep 11774717 = 4415519) B4415519
theorem B6199037 : Blo 1632515 6199037 := bstep (se 3 (by rfl) ⟨1162319, by rfl⟩ : syracuseStep 6199037 = 2324639) B2324639
theorem B7849811 : Blo 1632515 7849811 := bstep (se 1 (by rfl) ⟨5887358, by rfl⟩ : syracuseStep 7849811 = 11774717) B11774717
theorem B4132691 : Blo 1632515 4132691 := bstep (se 1 (by rfl) ⟨3099518, by rfl⟩ : syracuseStep 4132691 = 6199037) B6199037
theorem B2755127 : Blo 1632515 2755127 := bstep (se 1 (by rfl) ⟨2066345, by rfl⟩ : syracuseStep 2755127 = 4132691) B4132691
theorem B5233207 : Blo 1632515 5233207 := bstep (se 1 (by rfl) ⟨3924905, by rfl⟩ : syracuseStep 5233207 = 7849811) B7849811
theorem B1836751 : Blo 1632515 1836751 := bstep (se 1 (by rfl) ⟨1377563, by rfl⟩ : syracuseStep 1836751 = 2755127) B2755127
theorem B6977609 : Blo 1632515 6977609 := bstep (se 2 (by rfl) ⟨2616603, by rfl⟩ : syracuseStep 6977609 = 5233207) B5233207
theorem B4651739 : Blo 1632515 4651739 := bstep (se 1 (by rfl) ⟨3488804, by rfl⟩ : syracuseStep 4651739 = 6977609) B6977609
theorem B2449001 : Blo 1632515 2449001 := bstep (se 2 (by rfl) ⟨918375, by rfl⟩ : syracuseStep 2449001 = 1836751) B1836751
theorem B1632667 : Blo 1632515 1632667 := bstep (se 1 (by rfl) ⟨1224500, by rfl⟩ : syracuseStep 1632667 = 2449001) B2449001
theorem B3101159 : Blo 1632515 3101159 := bstep (se 1 (by rfl) ⟨2325869, by rfl⟩ : syracuseStep 3101159 = 4651739) B4651739
theorem B2067439 : Blo 1632515 2067439 := bstep (se 1 (by rfl) ⟨1550579, by rfl⟩ : syracuseStep 2067439 = 3101159) B3101159
theorem B2756585 : Blo 1632515 2756585 := bstep (se 2 (by rfl) ⟨1033719, by rfl⟩ : syracuseStep 2756585 = 2067439) B2067439
theorem B1837723 : Blo 1632515 1837723 := bstep (se 1 (by rfl) ⟨1378292, by rfl⟩ : syracuseStep 1837723 = 2756585) B2756585
theorem B2450297 : Blo 1632515 2450297 := bstep (se 2 (by rfl) ⟨918861, by rfl⟩ : syracuseStep 2450297 = 1837723) B1837723
theorem B1633531 : Blo 1632515 1633531 := bstep (se 1 (by rfl) ⟨1225148, by rfl⟩ : syracuseStep 1633531 = 2450297) B2450297

theorem C0 (j : ℕ) (h1 : 408128 ≤ j) (h2 : j ≤ 408503) : Blo 1632515 (4 * j + 3) := by
  interval_cases j
  · exact B1632515
  · exact B1632519
  · exact B1632523
  · exact B1632527
  · exact B1632531
  · exact B1632535
  · exact B1632539
  · exact B1632543
  · exact B1632547
  · exact B1632551
  · exact B1632555
  · exact B1632559
  · exact B1632563
  · exact B1632567
  · exact B1632571
  · exact B1632575
  · exact B1632579
  · exact B1632583
  · exact B1632587
  · exact B1632591
  · exact B1632595
  · exact B1632599
  · exact B1632603
  · exact B1632607
  · exact B1632611
  · exact B1632615
  · exact B1632619
  · exact B1632623
  · exact B1632627
  · exact B1632631
  · exact B1632635
  · exact B1632639
  · exact B1632643
  · exact B1632647
  · exact B1632651
  · exact B1632655
  · exact B1632659
  · exact B1632663
  · exact B1632667
  · exact B1632671
  · exact B1632675
  · exact B1632679
  · exact B1632683
  · exact B1632687
  · exact B1632691
  · exact B1632695
  · exact B1632699
  · exact B1632703
  · exact B1632707
  · exact B1632711
  · exact B1632715
  · exact B1632719
  · exact B1632723
  · exact B1632727
  · exact B1632731
  · exact B1632735
  · exact B1632739
  · exact B1632743
  · exact B1632747
  · exact B1632751
  · exact B1632755
  · exact B1632759
  · exact B1632763
  · exact B1632767
  · exact B1632771
  · exact B1632775
  · exact B1632779
  · exact B1632783
  · exact B1632787
  · exact B1632791
  · exact B1632795
  · exact B1632799
  · exact B1632803
  · exact B1632807
  · exact B1632811
  · exact B1632815
  · exact B1632819
  · exact B1632823
  · exact B1632827
  · exact B1632831
  · exact B1632835
  · exact B1632839
  · exact B1632843
  · exact B1632847
  · exact B1632851
  · exact B1632855
  · exact B1632859
  · exact B1632863
  · exact B1632867
  · exact B1632871
  · exact B1632875
  · exact B1632879
  · exact B1632883
  · exact B1632887
  · exact B1632891
  · exact B1632895
  · exact B1632899
  · exact B1632903
  · exact B1632907
  · exact B1632911
  · exact B1632915
  · exact B1632919
  · exact B1632923
  · exact B1632927
  · exact B1632931
  · exact B1632935
  · exact B1632939
  · exact B1632943
  · exact B1632947
  · exact B1632951
  · exact B1632955
  · exact B1632959
  · exact B1632963
  · exact B1632967
  · exact B1632971
  · exact B1632975
  · exact B1632979
  · exact B1632983
  · exact B1632987
  · exact B1632991
  · exact B1632995
  · exact B1632999
  · exact B1633003
  · exact B1633007
  · exact B1633011
  · exact B1633015
  · exact B1633019
  · exact B1633023
  · exact B1633027
  · exact B1633031
  · exact B1633035
  · exact B1633039
  · exact B1633043
  · exact B1633047
  · exact B1633051
  · exact B1633055
  · exact B1633059
  · exact B1633063
  · exact B1633067
  · exact B1633071
  · exact B1633075
  · exact B1633079
  · exact B1633083
  · exact B1633087
  · exact B1633091
  · exact B1633095
  · exact B1633099
  · exact B1633103
  · exact B1633107
  · exact B1633111
  · exact B1633115
  · exact B1633119
  · exact B1633123
  · exact B1633127
  · exact B1633131
  · exact B1633135
  · exact B1633139
  · exact B1633143
  · exact B1633147
  · exact B1633151
  · exact B1633155
  · exact B1633159
  · exact B1633163
  · exact B1633167
  · exact B1633171
  · exact B1633175
  · exact B1633179
  · exact B1633183
  · exact B1633187
  · exact B1633191
  · exact B1633195
  · exact B1633199
  · exact B1633203
  · exact B1633207
  · exact B1633211
  · exact B1633215
  · exact B1633219
  · exact B1633223
  · exact B1633227
  · exact B1633231
  · exact B1633235
  · exact B1633239
  · exact B1633243
  · exact B1633247
  · exact B1633251
  · exact B1633255
  · exact B1633259
  · exact B1633263
  · exact B1633267
  · exact B1633271
  · exact B1633275
  · exact B1633279
  · exact B1633283
  · exact B1633287
  · exact B1633291
  · exact B1633295
  · exact B1633299
  · exact B1633303
  · exact B1633307
  · exact B1633311
  · exact B1633315
  · exact B1633319
  · exact B1633323
  · exact B1633327
  · exact B1633331
  · exact B1633335
  · exact B1633339
  · exact B1633343
  · exact B1633347
  · exact B1633351
  · exact B1633355
  · exact B1633359
  · exact B1633363
  · exact B1633367
  · exact B1633371
  · exact B1633375
  · exact B1633379
  · exact B1633383
  · exact B1633387
  · exact B1633391
  · exact B1633395
  · exact B1633399
  · exact B1633403
  · exact B1633407
  · exact B1633411
  · exact B1633415
  · exact B1633419
  · exact B1633423
  · exact B1633427
  · exact B1633431
  · exact B1633435
  · exact B1633439
  · exact B1633443
  · exact B1633447
  · exact B1633451
  · exact B1633455
  · exact B1633459
  · exact B1633463
  · exact B1633467
  · exact B1633471
  · exact B1633475
  · exact B1633479
  · exact B1633483
  · exact B1633487
  · exact B1633491
  · exact B1633495
  · exact B1633499
  · exact B1633503
  · exact B1633507
  · exact B1633511
  · exact B1633515
  · exact B1633519
  · exact B1633523
  · exact B1633527
  · exact B1633531
  · exact B1633535
  · exact B1633539
  · exact B1633543
  · exact B1633547
  · exact B1633551
  · exact B1633555
  · exact B1633559
  · exact B1633563
  · exact B1633567
  · exact B1633571
  · exact B1633575
  · exact B1633579
  · exact B1633583
  · exact B1633587
  · exact B1633591
  · exact B1633595
  · exact B1633599
  · exact B1633603
  · exact B1633607
  · exact B1633611
  · exact B1633615
  · exact B1633619
  · exact B1633623
  · exact B1633627
  · exact B1633631
  · exact B1633635
  · exact B1633639
  · exact B1633643
  · exact B1633647
  · exact B1633651
  · exact B1633655
  · exact B1633659
  · exact B1633663
  · exact B1633667
  · exact B1633671
  · exact B1633675
  · exact B1633679
  · exact B1633683
  · exact B1633687
  · exact B1633691
  · exact B1633695
  · exact B1633699
  · exact B1633703
  · exact B1633707
  · exact B1633711
  · exact B1633715
  · exact B1633719
  · exact B1633723
  · exact B1633727
  · exact B1633731
  · exact B1633735
  · exact B1633739
  · exact B1633743
  · exact B1633747
  · exact B1633751
  · exact B1633755
  · exact B1633759
  · exact B1633763
  · exact B1633767
  · exact B1633771
  · exact B1633775
  · exact B1633779
  · exact B1633783
  · exact B1633787
  · exact B1633791
  · exact B1633795
  · exact B1633799
  · exact B1633803
  · exact B1633807
  · exact B1633811
  · exact B1633815
  · exact B1633819
  · exact B1633823
  · exact B1633827
  · exact B1633831
  · exact B1633835
  · exact B1633839
  · exact B1633843
  · exact B1633847
  · exact B1633851
  · exact B1633855
  · exact B1633859
  · exact B1633863
  · exact B1633867
  · exact B1633871
  · exact B1633875
  · exact B1633879
  · exact B1633883
  · exact B1633887
  · exact B1633891
  · exact B1633895
  · exact B1633899
  · exact B1633903
  · exact B1633907
  · exact B1633911
  · exact B1633915
  · exact B1633919
  · exact B1633923
  · exact B1633927
  · exact B1633931
  · exact B1633935
  · exact B1633939
  · exact B1633943
  · exact B1633947
  · exact B1633951
  · exact B1633955
  · exact B1633959
  · exact B1633963
  · exact B1633967
  · exact B1633971
  · exact B1633975
  · exact B1633979
  · exact B1633983
  · exact B1633987
  · exact B1633991
  · exact B1633995
  · exact B1633999
  · exact B1634003
  · exact B1634007
  · exact B1634011
  · exact B1634015

theorem solution (m : ℕ) (hlo : 1632515 ≤ m) (hhi : m ≤ 1634015) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 408128 ≤ j := by omega
    have hj2 : j ≤ 408503 := by omega
    have hb : Blo 1632515 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
