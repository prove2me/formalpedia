-- Prove2me | solution 1 for syracuse_descends_range_1270453_1271953
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:28.291626+00:00
-- url     : https://prove2.me/submissions/0c958a5a-1ae7-4887-a1cb-a3aabc6958af

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


theorem B2859029 : Blo 1270453 2859029 := bbase (se 6 (by rfl) ⟨67008, by rfl⟩ : syracuseStep 2859029 = 134017) (by norm_num)
theorem B8142869 : Blo 1270453 8142869 := bbase (se 6 (by rfl) ⟨190848, by rfl⟩ : syracuseStep 8142869 = 381697) (by norm_num)
theorem B3620933 : Blo 1270453 3620933 := bbase (se 4 (by rfl) ⟨339462, by rfl⟩ : syracuseStep 3620933 = 678925) (by norm_num)
theorem B1810517 : Blo 1270453 1810517 := bbase (se 8 (by rfl) ⟨10608, by rfl⟩ : syracuseStep 1810517 = 21217) (by norm_num)
theorem B2859101 : Blo 1270453 2859101 := bbase (se 3 (by rfl) ⟨536081, by rfl⟩ : syracuseStep 2859101 = 1072163) (by norm_num)
theorem B6439013 : Blo 1270453 6439013 := bbase (se 4 (by rfl) ⟨603657, by rfl⟩ : syracuseStep 6439013 = 1207315) (by norm_num)
theorem B2146405 : Blo 1270453 2146405 := bbase (se 4 (by rfl) ⟨201225, by rfl⟩ : syracuseStep 2146405 = 402451) (by norm_num)
theorem B2859173 : Blo 1270453 2859173 := bbase (se 4 (by rfl) ⟨268047, by rfl⟩ : syracuseStep 2859173 = 536095) (by norm_num)
theorem B4292837 : Blo 1270453 4292837 := bbase (se 4 (by rfl) ⟨402453, by rfl⟩ : syracuseStep 4292837 = 804907) (by norm_num)
theorem B2859245 : Blo 1270453 2859245 := bbase (se 3 (by rfl) ⟨536108, by rfl⟩ : syracuseStep 2859245 = 1072217) (by norm_num)
theorem B3621125 : Blo 1270453 3621125 := bbase (se 4 (by rfl) ⟨339480, by rfl⟩ : syracuseStep 3621125 = 678961) (by norm_num)
theorem B5505317 : Blo 1270453 5505317 := bbase (se 4 (by rfl) ⟨516123, by rfl⟩ : syracuseStep 5505317 = 1032247) (by norm_num)
theorem B2859317 : Blo 1270453 2859317 := bbase (se 5 (by rfl) ⟨134030, by rfl⟩ : syracuseStep 2859317 = 268061) (by norm_num)
theorem B6111557 : Blo 1270453 6111557 := bbase (se 4 (by rfl) ⟨572958, by rfl⟩ : syracuseStep 6111557 = 1145917) (by norm_num)
theorem B2859389 : Blo 1270453 2859389 := bbase (se 3 (by rfl) ⟨536135, by rfl⟩ : syracuseStep 2859389 = 1072271) (by norm_num)
theorem B4071845 : Blo 1270453 4071845 := bbase (se 4 (by rfl) ⟨381735, by rfl⟩ : syracuseStep 4071845 = 763471) (by norm_num)
theorem B2859461 : Blo 1270453 2859461 := bbase (se 4 (by rfl) ⟨268074, by rfl⟩ : syracuseStep 2859461 = 536149) (by norm_num)
theorem B2859533 : Blo 1270453 2859533 := bbase (se 3 (by rfl) ⟨536162, by rfl⟩ : syracuseStep 2859533 = 1072325) (by norm_num)
theorem B2859605 : Blo 1270453 2859605 := bbase (se 8 (by rfl) ⟨16755, by rfl⟩ : syracuseStep 2859605 = 33511) (by norm_num)
theorem B7832213 : Blo 1270453 7832213 := bbase (se 6 (by rfl) ⟨183567, by rfl⟩ : syracuseStep 7832213 = 367135) (by norm_num)
theorem B2859677 : Blo 1270453 2859677 := bbase (se 3 (by rfl) ⟨536189, by rfl⟩ : syracuseStep 2859677 = 1072379) (by norm_num)
theorem B2859749 : Blo 1270453 2859749 := bbase (se 4 (by rfl) ⟨268101, by rfl⟩ : syracuseStep 2859749 = 536203) (by norm_num)
theorem B3138317 : Blo 1270453 3138317 := bbase (se 3 (by rfl) ⟨588434, by rfl⟩ : syracuseStep 3138317 = 1176869) (by norm_num)
theorem B2859821 : Blo 1270453 2859821 := bbase (se 3 (by rfl) ⟨536216, by rfl⟩ : syracuseStep 2859821 = 1072433) (by norm_num)
theorem B2900821 : Blo 1270453 2900821 := bbase (se 9 (by rfl) ⟨8498, by rfl⟩ : syracuseStep 2900821 = 16997) (by norm_num)
theorem B2859893 : Blo 1270453 2859893 := bbase (se 5 (by rfl) ⟨134057, by rfl⟩ : syracuseStep 2859893 = 268115) (by norm_num)
theorem B2859965 : Blo 1270453 2859965 := bbase (se 3 (by rfl) ⟨536243, by rfl⟩ : syracuseStep 2859965 = 1072487) (by norm_num)
theorem B4826101 : Blo 1270453 4826101 := bbase (se 5 (by rfl) ⟨226223, by rfl⟩ : syracuseStep 4826101 = 452447) (by norm_num)
theorem B2860037 : Blo 1270453 2860037 := bbase (se 4 (by rfl) ⟨268128, by rfl⟩ : syracuseStep 2860037 = 536257) (by norm_num)
theorem B2860109 : Blo 1270453 2860109 := bbase (se 3 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 2860109 = 1072541) (by norm_num)
theorem B2860181 : Blo 1270453 2860181 := bbase (se 6 (by rfl) ⟨67035, by rfl⟩ : syracuseStep 2860181 = 134071) (by norm_num)
theorem B3867797 : Blo 1270453 3867797 := bbase (se 6 (by rfl) ⟨90651, by rfl⟩ : syracuseStep 3867797 = 181303) (by norm_num)
theorem B2860253 : Blo 1270453 2860253 := bbase (se 3 (by rfl) ⟨536297, by rfl⟩ : syracuseStep 2860253 = 1072595) (by norm_num)
theorem B4826405 : Blo 1270453 4826405 := bbase (se 4 (by rfl) ⟨452475, by rfl⟩ : syracuseStep 4826405 = 904951) (by norm_num)
theorem B2860325 : Blo 1270453 2860325 := bbase (se 4 (by rfl) ⟨268155, by rfl⟩ : syracuseStep 2860325 = 536311) (by norm_num)
theorem B5432629 : Blo 1270453 5432629 := bbase (se 5 (by rfl) ⟨254654, by rfl⟩ : syracuseStep 5432629 = 509309) (by norm_num)
theorem B5432645 : Blo 1270453 5432645 := bbase (se 4 (by rfl) ⟨509310, by rfl⟩ : syracuseStep 5432645 = 1018621) (by norm_num)
theorem B2860397 : Blo 1270453 2860397 := bbase (se 3 (by rfl) ⟨536324, by rfl⟩ : syracuseStep 2860397 = 1072649) (by norm_num)
theorem B2860469 : Blo 1270453 2860469 := bbase (se 5 (by rfl) ⟨134084, by rfl⟩ : syracuseStep 2860469 = 268169) (by norm_num)
theorem B7243253 : Blo 1270453 7243253 := bbase (se 5 (by rfl) ⟨339527, by rfl⟩ : syracuseStep 7243253 = 679055) (by norm_num)
theorem B1631737 : Blo 1270453 1631737 := bbase (se 2 (by rfl) ⟨611901, by rfl⟩ : syracuseStep 1631737 = 1223803) (by norm_num)
theorem B2860541 : Blo 1270453 2860541 := bbase (se 3 (by rfl) ⟨536351, by rfl⟩ : syracuseStep 2860541 = 1072703) (by norm_num)
theorem B2860613 : Blo 1270453 2860613 := bbase (se 4 (by rfl) ⟨268182, by rfl⟩ : syracuseStep 2860613 = 536365) (by norm_num)
theorem B2860685 : Blo 1270453 2860685 := bbase (se 3 (by rfl) ⟨536378, by rfl⟩ : syracuseStep 2860685 = 1072757) (by norm_num)
theorem B2860757 : Blo 1270453 2860757 := bbase (se 7 (by rfl) ⟨33524, by rfl⟩ : syracuseStep 2860757 = 67049) (by norm_num)
theorem B6432533 : Blo 1270453 6432533 := bbase (se 6 (by rfl) ⟨150762, by rfl⟩ : syracuseStep 6432533 = 301525) (by norm_num)
theorem B2860829 : Blo 1270453 2860829 := bbase (se 3 (by rfl) ⟨536405, by rfl⟩ : syracuseStep 2860829 = 1072811) (by norm_num)
theorem B4581173 : Blo 1270453 4581173 := bbase (se 5 (by rfl) ⟨214742, by rfl⟩ : syracuseStep 4581173 = 429485) (by norm_num)
theorem B10864469 : Blo 1270453 10864469 := bbase (se 9 (by rfl) ⟨31829, by rfl⟩ : syracuseStep 10864469 = 63659) (by norm_num)
theorem B2860901 : Blo 1270453 2860901 := bbase (se 4 (by rfl) ⟨268209, by rfl⟩ : syracuseStep 2860901 = 536419) (by norm_num)
theorem B2860973 : Blo 1270453 2860973 := bbase (se 3 (by rfl) ⟨536432, by rfl⟩ : syracuseStep 2860973 = 1072865) (by norm_num)
theorem B2713589 : Blo 1270453 2713589 := bbase (se 5 (by rfl) ⟨127199, by rfl⟩ : syracuseStep 2713589 = 254399) (by norm_num)
theorem B10307573 : Blo 1270453 10307573 := bbase (se 5 (by rfl) ⟨483167, by rfl⟩ : syracuseStep 10307573 = 966335) (by norm_num)
theorem B2861045 : Blo 1270453 2861045 := bbase (se 5 (by rfl) ⟨134111, by rfl⟩ : syracuseStep 2861045 = 268223) (by norm_num)
theorem B2861117 : Blo 1270453 2861117 := bbase (se 3 (by rfl) ⟨536459, by rfl⟩ : syracuseStep 2861117 = 1072919) (by norm_num)
theorem B3434581 : Blo 1270453 3434581 := bbase (se 8 (by rfl) ⟨20124, by rfl⟩ : syracuseStep 3434581 = 40249) (by norm_num)
theorem B2861189 : Blo 1270453 2861189 := bbase (se 4 (by rfl) ⟨268236, by rfl⟩ : syracuseStep 2861189 = 536473) (by norm_num)
theorem B2861261 : Blo 1270453 2861261 := bbase (se 3 (by rfl) ⟨536486, by rfl⟩ : syracuseStep 2861261 = 1072973) (by norm_num)
theorem B13224181 : Blo 1270453 13224181 := bbase (se 5 (by rfl) ⟨619883, by rfl⟩ : syracuseStep 13224181 = 1239767) (by norm_num)
theorem B1607941 : Blo 1270453 1607941 := bbase (se 4 (by rfl) ⟨150744, by rfl⟩ : syracuseStep 1607941 = 301489) (by norm_num)
theorem B2861333 : Blo 1270453 2861333 := bbase (se 6 (by rfl) ⟨67062, by rfl⟩ : syracuseStep 2861333 = 134125) (by norm_num)
theorem B2861405 : Blo 1270453 2861405 := bbase (se 3 (by rfl) ⟨536513, by rfl⟩ : syracuseStep 2861405 = 1073027) (by norm_num)
theorem B2861477 : Blo 1270453 2861477 := bbase (se 4 (by rfl) ⟨268263, by rfl⟩ : syracuseStep 2861477 = 536527) (by norm_num)
theorem B1608113 : Blo 1270453 1608113 := bbase (se 2 (by rfl) ⟨603042, by rfl⟩ : syracuseStep 1608113 = 1206085) (by norm_num)
theorem B6105557 : Blo 1270453 6105557 := bbase (se 7 (by rfl) ⟨71549, by rfl⟩ : syracuseStep 6105557 = 143099) (by norm_num)
theorem B1608169 : Blo 1270453 1608169 := bbase (se 2 (by rfl) ⟨603063, by rfl⟩ : syracuseStep 1608169 = 1206127) (by norm_num)
theorem B2861549 : Blo 1270453 2861549 := bbase (se 3 (by rfl) ⟨536540, by rfl⟩ : syracuseStep 2861549 = 1073081) (by norm_num)
theorem B2861621 : Blo 1270453 2861621 := bbase (se 5 (by rfl) ⟨134138, by rfl⟩ : syracuseStep 2861621 = 268277) (by norm_num)
theorem B1608265 : Blo 1270453 1608265 := bbase (se 2 (by rfl) ⟨603099, by rfl⟩ : syracuseStep 1608265 = 1206199) (by norm_num)
theorem B4074101 : Blo 1270453 4074101 := bbase (se 5 (by rfl) ⟨190973, by rfl⟩ : syracuseStep 4074101 = 381947) (by norm_num)
theorem B2861693 : Blo 1270453 2861693 := bbase (se 3 (by rfl) ⟨536567, by rfl⟩ : syracuseStep 2861693 = 1073135) (by norm_num)
theorem B2861765 : Blo 1270453 2861765 := bbase (se 4 (by rfl) ⟨268290, by rfl⟩ : syracuseStep 2861765 = 536581) (by norm_num)
theorem B1526509 : Blo 1270453 1526509 := bbase (se 3 (by rfl) ⟨286220, by rfl⟩ : syracuseStep 1526509 = 572441) (by norm_num)
theorem B1608437 : Blo 1270453 1608437 := bbase (se 5 (by rfl) ⟨75395, by rfl⟩ : syracuseStep 1608437 = 150791) (by norm_num)
theorem B2861837 : Blo 1270453 2861837 := bbase (se 3 (by rfl) ⟨536594, by rfl⟩ : syracuseStep 2861837 = 1073189) (by norm_num)
theorem B5958421 : Blo 1270453 5958421 := bbase (se 6 (by rfl) ⟨139650, by rfl⟩ : syracuseStep 5958421 = 279301) (by norm_num)
theorem B1608493 : Blo 1270453 1608493 := bbase (se 3 (by rfl) ⟨301592, by rfl⟩ : syracuseStep 1608493 = 603185) (by norm_num)
theorem B2714477 : Blo 1270453 2714477 := bbase (se 3 (by rfl) ⟨508964, by rfl⟩ : syracuseStep 2714477 = 1017929) (by norm_num)
theorem B1608589 : Blo 1270453 1608589 := bbase (se 3 (by rfl) ⟨301610, by rfl⟩ : syracuseStep 1608589 = 603221) (by norm_num)
theorem B12217301 : Blo 1270453 12217301 := bbase (se 7 (by rfl) ⟨143171, by rfl⟩ : syracuseStep 12217301 = 286343) (by norm_num)
theorem B2173981 : Blo 1270453 2173981 := bbase (se 3 (by rfl) ⟨407621, by rfl⟩ : syracuseStep 2173981 = 815243) (by norm_num)
theorem B6433829 : Blo 1270453 6433829 := bbase (se 4 (by rfl) ⟨603171, by rfl⟩ : syracuseStep 6433829 = 1206343) (by norm_num)
theorem B1608761 : Blo 1270453 1608761 := bbase (se 2 (by rfl) ⟨603285, by rfl⟩ : syracuseStep 1608761 = 1206571) (by norm_num)
theorem B2714717 : Blo 1270453 2714717 := bbase (se 3 (by rfl) ⟨509009, by rfl⟩ : syracuseStep 2714717 = 1018019) (by norm_num)
theorem B1608817 : Blo 1270453 1608817 := bbase (se 2 (by rfl) ⟨603306, by rfl⟩ : syracuseStep 1608817 = 1206613) (by norm_num)
theorem B1608913 : Blo 1270453 1608913 := bbase (se 2 (by rfl) ⟨603342, by rfl⟩ : syracuseStep 1608913 = 1206685) (by norm_num)
theorem B4828517 : Blo 1270453 4828517 := bbase (se 4 (by rfl) ⟨452673, by rfl⟩ : syracuseStep 4828517 = 905347) (by norm_num)
theorem B1609085 : Blo 1270453 1609085 := bbase (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) (by norm_num)
theorem B2411957 : Blo 1270453 2411957 := bbase (se 5 (by rfl) ⟨113060, by rfl⟩ : syracuseStep 2411957 = 226121) (by norm_num)
theorem B1527221 : Blo 1270453 1527221 := bbase (se 5 (by rfl) ⟨71588, by rfl⟩ : syracuseStep 1527221 = 143177) (by norm_num)
theorem B1609141 : Blo 1270453 1609141 := bbase (se 5 (by rfl) ⟨75428, by rfl⟩ : syracuseStep 1609141 = 150857) (by norm_num)
theorem B1609237 : Blo 1270453 1609237 := bbase (se 6 (by rfl) ⟨37716, by rfl⟩ : syracuseStep 1609237 = 75433) (by norm_num)
theorem B5795381 : Blo 1270453 5795381 := bbase (se 5 (by rfl) ⟨271658, by rfl⟩ : syracuseStep 5795381 = 543317) (by norm_num)
theorem B2412109 : Blo 1270453 2412109 := bbase (se 3 (by rfl) ⟨452270, by rfl⟩ : syracuseStep 2412109 = 904541) (by norm_num)
theorem B4288085 : Blo 1270453 4288085 := bbase (se 8 (by rfl) ⟨25125, by rfl⟩ : syracuseStep 4288085 = 50251) (by norm_num)
theorem B2715221 : Blo 1270453 2715221 := bbase (se 8 (by rfl) ⟨15909, by rfl⟩ : syracuseStep 2715221 = 31819) (by norm_num)
theorem B2715229 : Blo 1270453 2715229 := bbase (se 3 (by rfl) ⟨509105, by rfl⟩ : syracuseStep 2715229 = 1018211) (by norm_num)
theorem B4828805 : Blo 1270453 4828805 := bbase (se 4 (by rfl) ⟨452700, by rfl⟩ : syracuseStep 4828805 = 905401) (by norm_num)
theorem B5426837 : Blo 1270453 5426837 := bbase (se 6 (by rfl) ⟨127191, by rfl⟩ : syracuseStep 5426837 = 254383) (by norm_num)
theorem B1609409 : Blo 1270453 1609409 := bbase (se 2 (by rfl) ⟨603528, by rfl⟩ : syracuseStep 1609409 = 1207057) (by norm_num)
theorem B2035397 : Blo 1270453 2035397 := bbase (se 4 (by rfl) ⟨190818, by rfl⟩ : syracuseStep 2035397 = 381637) (by norm_num)
theorem B1609465 : Blo 1270453 1609465 := bbase (se 2 (by rfl) ⟨603549, by rfl⟩ : syracuseStep 1609465 = 1207099) (by norm_num)
theorem B1527557 : Blo 1270453 1527557 := bbase (se 4 (by rfl) ⟨143208, by rfl⟩ : syracuseStep 1527557 = 286417) (by norm_num)
theorem B1429285 : Blo 1270453 1429285 := bbase (se 4 (by rfl) ⟨133995, by rfl⟩ : syracuseStep 1429285 = 267991) (by norm_num)
theorem B2035525 : Blo 1270453 2035525 := bbase (se 4 (by rfl) ⟨190830, by rfl⟩ : syracuseStep 2035525 = 381661) (by norm_num)
theorem B1429321 : Blo 1270453 1429321 := bbase (se 2 (by rfl) ⟨535995, by rfl⟩ : syracuseStep 1429321 = 1071991) (by norm_num)
theorem B1609561 : Blo 1270453 1609561 := bbase (se 2 (by rfl) ⟨603585, by rfl⟩ : syracuseStep 1609561 = 1207171) (by norm_num)
theorem B1429357 : Blo 1270453 1429357 := bbase (se 3 (by rfl) ⟨268004, by rfl⟩ : syracuseStep 1429357 = 536009) (by norm_num)
theorem B1527673 : Blo 1270453 1527673 := bbase (se 2 (by rfl) ⟨572877, by rfl⟩ : syracuseStep 1527673 = 1145755) (by norm_num)
theorem B2412413 : Blo 1270453 2412413 := bbase (se 3 (by rfl) ⟨452327, by rfl⟩ : syracuseStep 2412413 = 904655) (by norm_num)
theorem B1429393 : Blo 1270453 1429393 := bbase (se 2 (by rfl) ⟨536022, by rfl⟩ : syracuseStep 1429393 = 1072045) (by norm_num)
theorem B1527697 : Blo 1270453 1527697 := bbase (se 2 (by rfl) ⟨572886, by rfl⟩ : syracuseStep 1527697 = 1145773) (by norm_num)
theorem B1429429 : Blo 1270453 1429429 := bbase (se 5 (by rfl) ⟨67004, by rfl⟩ : syracuseStep 1429429 = 134009) (by norm_num)
theorem B1429465 : Blo 1270453 1429465 := bbase (se 2 (by rfl) ⟨536049, by rfl⟩ : syracuseStep 1429465 = 1072099) (by norm_num)
theorem B1429501 : Blo 1270453 1429501 := bbase (se 3 (by rfl) ⟨268031, by rfl⟩ : syracuseStep 1429501 = 536063) (by norm_num)
theorem B4288517 : Blo 1270453 4288517 := bbase (se 4 (by rfl) ⟨402048, by rfl⟩ : syracuseStep 4288517 = 804097) (by norm_num)
theorem B1609733 : Blo 1270453 1609733 := bbase (se 4 (by rfl) ⟨150912, by rfl⟩ : syracuseStep 1609733 = 301825) (by norm_num)
theorem B1429537 : Blo 1270453 1429537 := bbase (se 2 (by rfl) ⟨536076, by rfl⟩ : syracuseStep 1429537 = 1072153) (by norm_num)
theorem B2289701 : Blo 1270453 2289701 := bbase (se 4 (by rfl) ⟨214659, by rfl⟩ : syracuseStep 2289701 = 429319) (by norm_num)
theorem B2617381 : Blo 1270453 2617381 := bbase (se 4 (by rfl) ⟨245379, by rfl⟩ : syracuseStep 2617381 = 490759) (by norm_num)
theorem B1609789 : Blo 1270453 1609789 := bbase (se 3 (by rfl) ⟨301835, by rfl⟩ : syracuseStep 1609789 = 603671) (by norm_num)
theorem B1429573 : Blo 1270453 1429573 := bbase (se 4 (by rfl) ⟨134022, by rfl⟩ : syracuseStep 1429573 = 268045) (by norm_num)
theorem B1429609 : Blo 1270453 1429609 := bbase (se 2 (by rfl) ⟨536103, by rfl⟩ : syracuseStep 1429609 = 1072207) (by norm_num)
theorem B9654389 : Blo 1270453 9654389 := bbase (se 5 (by rfl) ⟨452549, by rfl⟩ : syracuseStep 9654389 = 905099) (by norm_num)
theorem B1429645 : Blo 1270453 1429645 := bbase (se 3 (by rfl) ⟨268058, by rfl⟩ : syracuseStep 1429645 = 536117) (by norm_num)
theorem B1429681 : Blo 1270453 1429681 := bbase (se 2 (by rfl) ⟨536130, by rfl⟩ : syracuseStep 1429681 = 1072261) (by norm_num)
theorem B48853205 : Blo 1270453 48853205 := bbase (se 7 (by rfl) ⟨572498, by rfl⟩ : syracuseStep 48853205 = 1144997) (by norm_num)
theorem B1429717 : Blo 1270453 1429717 := bbase (se 7 (by rfl) ⟨16754, by rfl⟩ : syracuseStep 1429717 = 33509) (by norm_num)
theorem B1429753 : Blo 1270453 1429753 := bbase (se 2 (by rfl) ⟨536157, by rfl⟩ : syracuseStep 1429753 = 1072315) (by norm_num)
theorem B1429789 : Blo 1270453 1429789 := bbase (se 3 (by rfl) ⟨268085, by rfl⟩ : syracuseStep 1429789 = 536171) (by norm_num)
theorem B6435125 : Blo 1270453 6435125 := bbase (se 5 (by rfl) ⟨301646, by rfl⟩ : syracuseStep 6435125 = 603293) (by norm_num)
theorem B1429825 : Blo 1270453 1429825 := bbase (se 2 (by rfl) ⟨536184, by rfl⟩ : syracuseStep 1429825 = 1072369) (by norm_num)
theorem B1429861 : Blo 1270453 1429861 := bbase (se 4 (by rfl) ⟨134049, by rfl⟩ : syracuseStep 1429861 = 268099) (by norm_num)
theorem B1429897 : Blo 1270453 1429897 := bbase (se 2 (by rfl) ⟨536211, by rfl⟩ : syracuseStep 1429897 = 1072423) (by norm_num)
theorem B1429933 : Blo 1270453 1429933 := bbase (se 3 (by rfl) ⟨268112, by rfl⟩ : syracuseStep 1429933 = 536225) (by norm_num)
theorem B4288949 : Blo 1270453 4288949 := bbase (se 5 (by rfl) ⟨201044, by rfl⟩ : syracuseStep 4288949 = 402089) (by norm_num)
theorem B1429969 : Blo 1270453 1429969 := bbase (se 2 (by rfl) ⟨536238, by rfl⟩ : syracuseStep 1429969 = 1072477) (by norm_num)
theorem B1430005 : Blo 1270453 1430005 := bbase (se 5 (by rfl) ⟨67031, by rfl⟩ : syracuseStep 1430005 = 134063) (by norm_num)
theorem B24441365 : Blo 1270453 24441365 := bbase (se 6 (by rfl) ⟨572844, by rfl⟩ : syracuseStep 24441365 = 1145689) (by norm_num)
theorem B1430041 : Blo 1270453 1430041 := bbase (se 2 (by rfl) ⟨536265, by rfl⟩ : syracuseStep 1430041 = 1072531) (by norm_num)
theorem B3215933 : Blo 1270453 3215933 := bbase (se 3 (by rfl) ⟨602987, by rfl⟩ : syracuseStep 3215933 = 1205975) (by norm_num)
theorem B1430077 : Blo 1270453 1430077 := bbase (se 3 (by rfl) ⟨268139, by rfl⟩ : syracuseStep 1430077 = 536279) (by norm_num)
theorem B1430113 : Blo 1270453 1430113 := bbase (se 2 (by rfl) ⟨536292, by rfl⟩ : syracuseStep 1430113 = 1072585) (by norm_num)
theorem B2290277 : Blo 1270453 2290277 := bbase (se 4 (by rfl) ⟨214713, by rfl⟩ : syracuseStep 2290277 = 429427) (by norm_num)
theorem B2413165 : Blo 1270453 2413165 := bbase (se 3 (by rfl) ⟨452468, by rfl⟩ : syracuseStep 2413165 = 904937) (by norm_num)
theorem B2036333 : Blo 1270453 2036333 := bbase (se 3 (by rfl) ⟨381812, by rfl⟩ : syracuseStep 2036333 = 763625) (by norm_num)
theorem B1430149 : Blo 1270453 1430149 := bbase (se 4 (by rfl) ⟨134076, by rfl⟩ : syracuseStep 1430149 = 268153) (by norm_num)
theorem B1430185 : Blo 1270453 1430185 := bbase (se 2 (by rfl) ⟨536319, by rfl⟩ : syracuseStep 1430185 = 1072639) (by norm_num)
theorem B2175677 : Blo 1270453 2175677 := bbase (se 3 (by rfl) ⟨407939, by rfl⟩ : syracuseStep 2175677 = 815879) (by norm_num)
theorem B2716357 : Blo 1270453 2716357 := bbase (se 4 (by rfl) ⟨254658, by rfl⟩ : syracuseStep 2716357 = 509317) (by norm_num)
theorem B1430221 : Blo 1270453 1430221 := bbase (se 3 (by rfl) ⟨268166, by rfl⟩ : syracuseStep 1430221 = 536333) (by norm_num)
theorem B1430257 : Blo 1270453 1430257 := bbase (se 2 (by rfl) ⟨536346, by rfl⟩ : syracuseStep 1430257 = 1072693) (by norm_num)
theorem B3216125 : Blo 1270453 3216125 := bbase (se 3 (by rfl) ⟨603023, by rfl⟩ : syracuseStep 3216125 = 1206047) (by norm_num)
theorem B2413309 : Blo 1270453 2413309 := bbase (se 3 (by rfl) ⟨452495, by rfl⟩ : syracuseStep 2413309 = 904991) (by norm_num)
theorem B1430293 : Blo 1270453 1430293 := bbase (se 6 (by rfl) ⟨33522, by rfl⟩ : syracuseStep 1430293 = 67045) (by norm_num)
theorem B1430329 : Blo 1270453 1430329 := bbase (se 2 (by rfl) ⟨536373, by rfl⟩ : syracuseStep 1430329 = 1072747) (by norm_num)
theorem B1430365 : Blo 1270453 1430365 := bbase (se 3 (by rfl) ⟨268193, by rfl⟩ : syracuseStep 1430365 = 536387) (by norm_num)
theorem B4289381 : Blo 1270453 4289381 := bbase (se 4 (by rfl) ⟨402129, by rfl⟩ : syracuseStep 4289381 = 804259) (by norm_num)
theorem B1430401 : Blo 1270453 1430401 := bbase (se 2 (by rfl) ⟨536400, by rfl⟩ : syracuseStep 1430401 = 1072801) (by norm_num)
theorem B2036621 : Blo 1270453 2036621 := bbase (se 3 (by rfl) ⟨381866, by rfl⟩ : syracuseStep 2036621 = 763733) (by norm_num)
theorem B2413469 : Blo 1270453 2413469 := bbase (se 3 (by rfl) ⟨452525, by rfl⟩ : syracuseStep 2413469 = 905051) (by norm_num)
theorem B1430437 : Blo 1270453 1430437 := bbase (se 4 (by rfl) ⟨134103, by rfl⟩ : syracuseStep 1430437 = 268207) (by norm_num)
theorem B3314621 : Blo 1270453 3314621 := bbase (se 3 (by rfl) ⟨621491, by rfl⟩ : syracuseStep 3314621 = 1242983) (by norm_num)
theorem B1430473 : Blo 1270453 1430473 := bbase (se 2 (by rfl) ⟨536427, by rfl⟩ : syracuseStep 1430473 = 1072855) (by norm_num)
theorem B1741805 : Blo 1270453 1741805 := bbase (se 3 (by rfl) ⟨326588, by rfl⟩ : syracuseStep 1741805 = 653177) (by norm_num)
theorem B1430509 : Blo 1270453 1430509 := bbase (se 3 (by rfl) ⟨268220, by rfl⟩ : syracuseStep 1430509 = 536441) (by norm_num)
theorem B1717237 : Blo 1270453 1717237 := bbase (se 5 (by rfl) ⟨80495, by rfl⟩ : syracuseStep 1717237 = 160991) (by norm_num)
theorem B1430545 : Blo 1270453 1430545 := bbase (se 2 (by rfl) ⟨536454, by rfl⟩ : syracuseStep 1430545 = 1072909) (by norm_num)
theorem B10187797 : Blo 1270453 10187797 := bbase (se 6 (by rfl) ⟨238776, by rfl⟩ : syracuseStep 10187797 = 477553) (by norm_num)
theorem B1905701 : Blo 1270453 1905701 := bbase (se 4 (by rfl) ⟨178659, by rfl⟩ : syracuseStep 1905701 = 357319) (by norm_num)
theorem B2413613 : Blo 1270453 2413613 := bbase (se 3 (by rfl) ⟨452552, by rfl⟩ : syracuseStep 2413613 = 905105) (by norm_num)
theorem B1430581 : Blo 1270453 1430581 := bbase (se 5 (by rfl) ⟨67058, by rfl⟩ : syracuseStep 1430581 = 134117) (by norm_num)
theorem B1905725 : Blo 1270453 1905725 := bbase (se 3 (by rfl) ⟨357323, by rfl⟩ : syracuseStep 1905725 = 714647) (by norm_num)
theorem B1905749 : Blo 1270453 1905749 := bbase (se 8 (by rfl) ⟨11166, by rfl⟩ : syracuseStep 1905749 = 22333) (by norm_num)
theorem B3216469 : Blo 1270453 3216469 := bbase (se 8 (by rfl) ⟨18846, by rfl⟩ : syracuseStep 3216469 = 37693) (by norm_num)
theorem B1430617 : Blo 1270453 1430617 := bbase (se 2 (by rfl) ⟨536481, by rfl⟩ : syracuseStep 1430617 = 1072963) (by norm_num)
theorem B1905773 : Blo 1270453 1905773 := bbase (se 3 (by rfl) ⟨357332, by rfl⟩ : syracuseStep 1905773 = 714665) (by norm_num)
theorem B1430653 : Blo 1270453 1430653 := bbase (se 3 (by rfl) ⟨268247, by rfl⟩ : syracuseStep 1430653 = 536495) (by norm_num)
theorem B1905797 : Blo 1270453 1905797 := bbase (se 4 (by rfl) ⟨178668, by rfl⟩ : syracuseStep 1905797 = 357337) (by norm_num)
theorem B1905821 : Blo 1270453 1905821 := bbase (se 3 (by rfl) ⟨357341, by rfl⟩ : syracuseStep 1905821 = 714683) (by norm_num)
theorem B1569949 : Blo 1270453 1569949 := bbase (se 3 (by rfl) ⟨294365, by rfl⟩ : syracuseStep 1569949 = 588731) (by norm_num)
theorem B1430689 : Blo 1270453 1430689 := bbase (se 2 (by rfl) ⟨536508, by rfl⟩ : syracuseStep 1430689 = 1073017) (by norm_num)
theorem B1905845 : Blo 1270453 1905845 := bbase (se 5 (by rfl) ⟨89336, by rfl⟩ : syracuseStep 1905845 = 178673) (by norm_num)
theorem B3216581 : Blo 1270453 3216581 := bbase (se 4 (by rfl) ⟨301554, by rfl⟩ : syracuseStep 3216581 = 603109) (by norm_num)
theorem B1430725 : Blo 1270453 1430725 := bbase (se 4 (by rfl) ⟨134130, by rfl⟩ : syracuseStep 1430725 = 268261) (by norm_num)
theorem B1905869 : Blo 1270453 1905869 := bbase (se 3 (by rfl) ⟨357350, by rfl⟩ : syracuseStep 1905869 = 714701) (by norm_num)
theorem B1717453 : Blo 1270453 1717453 := bbase (se 3 (by rfl) ⟨322022, by rfl⟩ : syracuseStep 1717453 = 644045) (by norm_num)
theorem B1905893 : Blo 1270453 1905893 := bbase (se 4 (by rfl) ⟨178677, by rfl⟩ : syracuseStep 1905893 = 357355) (by norm_num)
theorem B1430761 : Blo 1270453 1430761 := bbase (se 2 (by rfl) ⟨536535, by rfl⟩ : syracuseStep 1430761 = 1073071) (by norm_num)
theorem B1905917 : Blo 1270453 1905917 := bbase (se 3 (by rfl) ⟨357359, by rfl⟩ : syracuseStep 1905917 = 714719) (by norm_num)
theorem B1430797 : Blo 1270453 1430797 := bbase (se 3 (by rfl) ⟨268274, by rfl⟩ : syracuseStep 1430797 = 536549) (by norm_num)
theorem B1905941 : Blo 1270453 1905941 := bbase (se 6 (by rfl) ⟨44670, by rfl⟩ : syracuseStep 1905941 = 89341) (by norm_num)
theorem B4289813 : Blo 1270453 4289813 := bbase (se 6 (by rfl) ⟨100542, by rfl⟩ : syracuseStep 4289813 = 201085) (by norm_num)
theorem B1357085 : Blo 1270453 1357085 := bbase (se 3 (by rfl) ⟨254453, by rfl⟩ : syracuseStep 1357085 = 508907) (by norm_num)
theorem B1905965 : Blo 1270453 1905965 := bbase (se 3 (by rfl) ⟨357368, by rfl⟩ : syracuseStep 1905965 = 714737) (by norm_num)
theorem B2037037 : Blo 1270453 2037037 := bbase (se 3 (by rfl) ⟨381944, by rfl⟩ : syracuseStep 2037037 = 763889) (by norm_num)
theorem B1430833 : Blo 1270453 1430833 := bbase (se 2 (by rfl) ⟨536562, by rfl⟩ : syracuseStep 1430833 = 1073125) (by norm_num)
theorem B1905989 : Blo 1270453 1905989 := bbase (se 4 (by rfl) ⟨178686, by rfl⟩ : syracuseStep 1905989 = 357373) (by norm_num)
theorem B2413901 : Blo 1270453 2413901 := bbase (se 3 (by rfl) ⟨452606, by rfl⟩ : syracuseStep 2413901 = 905213) (by norm_num)
theorem B3052885 : Blo 1270453 3052885 := bbase (se 14 (by rfl) ⟨279, by rfl⟩ : syracuseStep 3052885 = 559) (by norm_num)
theorem B1430869 : Blo 1270453 1430869 := bbase (se 15 (by rfl) ⟨65, by rfl⟩ : syracuseStep 1430869 = 131) (by norm_num)
theorem B1906013 : Blo 1270453 1906013 := bbase (se 3 (by rfl) ⟨357377, by rfl⟩ : syracuseStep 1906013 = 714755) (by norm_num)
theorem B1906037 : Blo 1270453 1906037 := bbase (se 5 (by rfl) ⟨89345, by rfl⟩ : syracuseStep 1906037 = 178691) (by norm_num)
theorem B1430905 : Blo 1270453 1430905 := bbase (se 2 (by rfl) ⟨536589, by rfl⟩ : syracuseStep 1430905 = 1073179) (by norm_num)
theorem B3216773 : Blo 1270453 3216773 := bbase (se 4 (by rfl) ⟨301572, by rfl⟩ : syracuseStep 3216773 = 603145) (by norm_num)
theorem B5428613 : Blo 1270453 5428613 := bbase (se 4 (by rfl) ⟨508932, by rfl⟩ : syracuseStep 5428613 = 1017865) (by norm_num)
theorem B3437957 : Blo 1270453 3437957 := bbase (se 4 (by rfl) ⟨322308, by rfl⟩ : syracuseStep 3437957 = 644617) (by norm_num)
theorem B1906061 : Blo 1270453 1906061 := bbase (se 3 (by rfl) ⟨357386, by rfl⟩ : syracuseStep 1906061 = 714773) (by norm_num)
theorem B1430941 : Blo 1270453 1430941 := bbase (se 3 (by rfl) ⟨268301, by rfl⟩ : syracuseStep 1430941 = 536603) (by norm_num)
theorem B1906085 : Blo 1270453 1906085 := bbase (se 4 (by rfl) ⟨178695, by rfl⟩ : syracuseStep 1906085 = 357391) (by norm_num)
theorem B1717669 : Blo 1270453 1717669 := bbase (se 4 (by rfl) ⟨161031, by rfl⟩ : syracuseStep 1717669 = 322063) (by norm_num)
theorem B1906109 : Blo 1270453 1906109 := bbase (se 3 (by rfl) ⟨357395, by rfl⟩ : syracuseStep 1906109 = 714791) (by norm_num)
theorem B1906133 : Blo 1270453 1906133 := bbase (se 7 (by rfl) ⟨22337, by rfl⟩ : syracuseStep 1906133 = 44675) (by norm_num)
theorem B1357273 : Blo 1270453 1357273 := bbase (se 2 (by rfl) ⟨508977, by rfl⟩ : syracuseStep 1357273 = 1017955) (by norm_num)
theorem B2414053 : Blo 1270453 2414053 := bbase (se 4 (by rfl) ⟨226317, by rfl⟩ : syracuseStep 2414053 = 452635) (by norm_num)
theorem B1906157 : Blo 1270453 1906157 := bbase (se 3 (by rfl) ⟨357404, by rfl⟩ : syracuseStep 1906157 = 714809) (by norm_num)
theorem B1906181 : Blo 1270453 1906181 := bbase (se 4 (by rfl) ⟨178704, by rfl⟩ : syracuseStep 1906181 = 357409) (by norm_num)
theorem B5879317 : Blo 1270453 5879317 := bbase (se 6 (by rfl) ⟨137796, by rfl⟩ : syracuseStep 5879317 = 275593) (by norm_num)
theorem B1906205 : Blo 1270453 1906205 := bbase (se 3 (by rfl) ⟨357413, by rfl⟩ : syracuseStep 1906205 = 714827) (by norm_num)
theorem B1906229 : Blo 1270453 1906229 := bbase (se 5 (by rfl) ⟨89354, by rfl⟩ : syracuseStep 1906229 = 178709) (by norm_num)
theorem B6436421 : Blo 1270453 6436421 := bbase (se 4 (by rfl) ⟨603414, by rfl⟩ : syracuseStep 6436421 = 1206829) (by norm_num)
theorem B1906253 : Blo 1270453 1906253 := bbase (se 3 (by rfl) ⟨357422, by rfl⟩ : syracuseStep 1906253 = 714845) (by norm_num)
theorem B1906277 : Blo 1270453 1906277 := bbase (se 4 (by rfl) ⟨178713, by rfl⟩ : syracuseStep 1906277 = 357427) (by norm_num)
theorem B5428853 : Blo 1270453 5428853 := bbase (se 5 (by rfl) ⟨254477, by rfl⟩ : syracuseStep 5428853 = 508955) (by norm_num)
theorem B1906301 : Blo 1270453 1906301 := bbase (se 3 (by rfl) ⟨357431, by rfl⟩ : syracuseStep 1906301 = 714863) (by norm_num)
theorem B2578061 : Blo 1270453 2578061 := bbase (se 3 (by rfl) ⟨483386, by rfl⟩ : syracuseStep 2578061 = 966773) (by norm_num)
theorem B1906325 : Blo 1270453 1906325 := bbase (se 6 (by rfl) ⟨44679, by rfl⟩ : syracuseStep 1906325 = 89359) (by norm_num)
theorem B2143901 : Blo 1270453 2143901 := bbase (se 3 (by rfl) ⟨401981, by rfl⟩ : syracuseStep 2143901 = 803963) (by norm_num)
theorem B1906349 : Blo 1270453 1906349 := bbase (se 3 (by rfl) ⟨357440, by rfl⟩ : syracuseStep 1906349 = 714881) (by norm_num)
theorem B1906373 : Blo 1270453 1906373 := bbase (se 4 (by rfl) ⟨178722, by rfl⟩ : syracuseStep 1906373 = 357445) (by norm_num)
theorem B4290245 : Blo 1270453 4290245 := bbase (se 4 (by rfl) ⟨402210, by rfl⟩ : syracuseStep 4290245 = 804421) (by norm_num)
theorem B14669525 : Blo 1270453 14669525 := bbase (se 7 (by rfl) ⟨171908, by rfl⟩ : syracuseStep 14669525 = 343817) (by norm_num)
theorem B1906397 : Blo 1270453 1906397 := bbase (se 3 (by rfl) ⟨357449, by rfl⟩ : syracuseStep 1906397 = 714899) (by norm_num)
theorem B3217117 : Blo 1270453 3217117 := bbase (se 3 (by rfl) ⟨603209, by rfl⟩ : syracuseStep 3217117 = 1206419) (by norm_num)
theorem B1906421 : Blo 1270453 1906421 := bbase (se 5 (by rfl) ⟨89363, by rfl⟩ : syracuseStep 1906421 = 178727) (by norm_num)
theorem B1906445 : Blo 1270453 1906445 := bbase (se 3 (by rfl) ⟨357458, by rfl⟩ : syracuseStep 1906445 = 714917) (by norm_num)
theorem B2414357 : Blo 1270453 2414357 := bbase (se 6 (by rfl) ⟨56586, by rfl⟩ : syracuseStep 2414357 = 113173) (by norm_num)
theorem B2144029 : Blo 1270453 2144029 := bbase (se 3 (by rfl) ⟨402005, by rfl⟩ : syracuseStep 2144029 = 804011) (by norm_num)
theorem B1906469 : Blo 1270453 1906469 := bbase (se 4 (by rfl) ⟨178731, by rfl⟩ : syracuseStep 1906469 = 357463) (by norm_num)
theorem B3094325 : Blo 1270453 3094325 := bbase (se 5 (by rfl) ⟨145046, by rfl⟩ : syracuseStep 3094325 = 290093) (by norm_num)
theorem B1906493 : Blo 1270453 1906493 := bbase (se 3 (by rfl) ⟨357467, by rfl⟩ : syracuseStep 1906493 = 714935) (by norm_num)
theorem B3217229 : Blo 1270453 3217229 := bbase (se 3 (by rfl) ⟨603230, by rfl⟩ : syracuseStep 3217229 = 1206461) (by norm_num)
theorem B1906517 : Blo 1270453 1906517 := bbase (se 9 (by rfl) ⟨5585, by rfl⟩ : syracuseStep 1906517 = 11171) (by norm_num)
theorem B1906541 : Blo 1270453 1906541 := bbase (se 3 (by rfl) ⟨357476, by rfl⟩ : syracuseStep 1906541 = 714953) (by norm_num)
theorem B2144117 : Blo 1270453 2144117 := bbase (se 5 (by rfl) ⟨100505, by rfl⟩ : syracuseStep 2144117 = 201011) (by norm_num)
theorem B2291581 : Blo 1270453 2291581 := bbase (se 3 (by rfl) ⟨429671, by rfl⟩ : syracuseStep 2291581 = 859343) (by norm_num)
theorem B1906565 : Blo 1270453 1906565 := bbase (se 4 (by rfl) ⟨178740, by rfl⟩ : syracuseStep 1906565 = 357481) (by norm_num)
theorem B1906589 : Blo 1270453 1906589 := bbase (se 3 (by rfl) ⟨357485, by rfl⟩ : syracuseStep 1906589 = 714971) (by norm_num)
theorem B1906613 : Blo 1270453 1906613 := bbase (se 5 (by rfl) ⟨89372, by rfl⟩ : syracuseStep 1906613 = 178745) (by norm_num)
theorem B3053501 : Blo 1270453 3053501 := bbase (se 3 (by rfl) ⟨572531, by rfl⟩ : syracuseStep 3053501 = 1145063) (by norm_num)
theorem B1906637 : Blo 1270453 1906637 := bbase (se 3 (by rfl) ⟨357494, by rfl⟩ : syracuseStep 1906637 = 714989) (by norm_num)
theorem B1906661 : Blo 1270453 1906661 := bbase (se 4 (by rfl) ⟨178749, by rfl⟩ : syracuseStep 1906661 = 357499) (by norm_num)
theorem B2144245 : Blo 1270453 2144245 := bbase (se 5 (by rfl) ⟨100511, by rfl⟩ : syracuseStep 2144245 = 201023) (by norm_num)
theorem B1906685 : Blo 1270453 1906685 := bbase (se 3 (by rfl) ⟨357503, by rfl⟩ : syracuseStep 1906685 = 715007) (by norm_num)
theorem B3217421 : Blo 1270453 3217421 := bbase (se 3 (by rfl) ⟨603266, by rfl⟩ : syracuseStep 3217421 = 1206533) (by norm_num)
theorem B1906709 : Blo 1270453 1906709 := bbase (se 6 (by rfl) ⟨44688, by rfl⟩ : syracuseStep 1906709 = 89377) (by norm_num)
theorem B9164821 : Blo 1270453 9164821 := bbase (se 6 (by rfl) ⟨214800, by rfl⟩ : syracuseStep 9164821 = 429601) (by norm_num)
theorem B1906733 : Blo 1270453 1906733 := bbase (se 3 (by rfl) ⟨357512, by rfl⟩ : syracuseStep 1906733 = 715025) (by norm_num)
theorem B1906757 : Blo 1270453 1906757 := bbase (se 4 (by rfl) ⟨178758, by rfl⟩ : syracuseStep 1906757 = 357517) (by norm_num)
theorem B2144333 : Blo 1270453 2144333 := bbase (se 3 (by rfl) ⟨402062, by rfl⟩ : syracuseStep 2144333 = 804125) (by norm_num)
theorem B1906781 : Blo 1270453 1906781 := bbase (se 3 (by rfl) ⟨357521, by rfl⟩ : syracuseStep 1906781 = 715043) (by norm_num)
theorem B1906805 : Blo 1270453 1906805 := bbase (se 5 (by rfl) ⟨89381, by rfl⟩ : syracuseStep 1906805 = 178763) (by norm_num)
theorem B4290677 : Blo 1270453 4290677 := bbase (se 5 (by rfl) ⟨201125, by rfl⟩ : syracuseStep 4290677 = 402251) (by norm_num)
theorem B1906829 : Blo 1270453 1906829 := bbase (se 3 (by rfl) ⟨357530, by rfl⟩ : syracuseStep 1906829 = 715061) (by norm_num)
theorem B1906853 : Blo 1270453 1906853 := bbase (se 4 (by rfl) ⟨178767, by rfl⟩ : syracuseStep 1906853 = 357535) (by norm_num)
theorem B1906877 : Blo 1270453 1906877 := bbase (se 3 (by rfl) ⟨357539, by rfl⟩ : syracuseStep 1906877 = 715079) (by norm_num)
theorem B2144461 : Blo 1270453 2144461 := bbase (se 3 (by rfl) ⟨402086, by rfl⟩ : syracuseStep 2144461 = 804173) (by norm_num)
theorem B1906901 : Blo 1270453 1906901 := bbase (se 7 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 1906901 = 44693) (by norm_num)
theorem B1906925 : Blo 1270453 1906925 := bbase (se 3 (by rfl) ⟨357548, by rfl⟩ : syracuseStep 1906925 = 715097) (by norm_num)
theorem B2611453 : Blo 1270453 2611453 := bbase (se 3 (by rfl) ⟨489647, by rfl⟩ : syracuseStep 2611453 = 979295) (by norm_num)
theorem B1906949 : Blo 1270453 1906949 := bbase (se 4 (by rfl) ⟨178776, by rfl⟩ : syracuseStep 1906949 = 357553) (by norm_num)
theorem B1358093 : Blo 1270453 1358093 := bbase (se 3 (by rfl) ⟨254642, by rfl⟩ : syracuseStep 1358093 = 509285) (by norm_num)
theorem B1906973 : Blo 1270453 1906973 := bbase (se 3 (by rfl) ⟨357557, by rfl⟩ : syracuseStep 1906973 = 715115) (by norm_num)
theorem B2144549 : Blo 1270453 2144549 := bbase (se 4 (by rfl) ⟨201051, by rfl⟩ : syracuseStep 2144549 = 402103) (by norm_num)
theorem B1906997 : Blo 1270453 1906997 := bbase (se 5 (by rfl) ⟨89390, by rfl⟩ : syracuseStep 1906997 = 178781) (by norm_num)
theorem B1907021 : Blo 1270453 1907021 := bbase (se 3 (by rfl) ⟨357566, by rfl⟩ : syracuseStep 1907021 = 715133) (by norm_num)
theorem B3217765 : Blo 1270453 3217765 := bbase (se 4 (by rfl) ⟨301665, by rfl⟩ : syracuseStep 3217765 = 603331) (by norm_num)
theorem B1907045 : Blo 1270453 1907045 := bbase (se 4 (by rfl) ⟨178785, by rfl⟩ : syracuseStep 1907045 = 357571) (by norm_num)
theorem B2480485 : Blo 1270453 2480485 := bbase (se 4 (by rfl) ⟨232545, by rfl⟩ : syracuseStep 2480485 = 465091) (by norm_num)
theorem B3053933 : Blo 1270453 3053933 := bbase (se 3 (by rfl) ⟨572612, by rfl⟩ : syracuseStep 3053933 = 1145225) (by norm_num)
theorem B1907069 : Blo 1270453 1907069 := bbase (se 3 (by rfl) ⟨357575, by rfl⟩ : syracuseStep 1907069 = 715151) (by norm_num)
theorem B1907093 : Blo 1270453 1907093 := bbase (se 6 (by rfl) ⟨44697, by rfl⟩ : syracuseStep 1907093 = 89395) (by norm_num)
theorem B2144677 : Blo 1270453 2144677 := bbase (se 4 (by rfl) ⟨201063, by rfl⟩ : syracuseStep 2144677 = 402127) (by norm_num)
theorem B1907117 : Blo 1270453 1907117 := bbase (se 3 (by rfl) ⟨357584, by rfl⟩ : syracuseStep 1907117 = 715169) (by norm_num)
theorem B1907141 : Blo 1270453 1907141 := bbase (se 4 (by rfl) ⟨178794, by rfl⟩ : syracuseStep 1907141 = 357589) (by norm_num)
theorem B3217877 : Blo 1270453 3217877 := bbase (se 7 (by rfl) ⟨37709, by rfl⟩ : syracuseStep 3217877 = 75419) (by norm_num)
theorem B1907165 : Blo 1270453 1907165 := bbase (se 3 (by rfl) ⟨357593, by rfl⟩ : syracuseStep 1907165 = 715187) (by norm_num)
theorem B1907189 : Blo 1270453 1907189 := bbase (se 5 (by rfl) ⟨89399, by rfl⟩ : syracuseStep 1907189 = 178799) (by norm_num)
theorem B2144765 : Blo 1270453 2144765 := bbase (se 3 (by rfl) ⟨402143, by rfl⟩ : syracuseStep 2144765 = 804287) (by norm_num)
theorem B1907213 : Blo 1270453 1907213 := bbase (se 3 (by rfl) ⟨357602, by rfl⟩ : syracuseStep 1907213 = 715205) (by norm_num)
theorem B3619349 : Blo 1270453 3619349 := bbase (se 6 (by rfl) ⟨84828, by rfl⟩ : syracuseStep 3619349 = 169657) (by norm_num)
theorem B4291109 : Blo 1270453 4291109 := bbase (se 4 (by rfl) ⟨402291, by rfl⟩ : syracuseStep 4291109 = 804583) (by norm_num)
theorem B1907237 : Blo 1270453 1907237 := bbase (se 4 (by rfl) ⟨178803, by rfl⟩ : syracuseStep 1907237 = 357607) (by norm_num)
theorem B1907261 : Blo 1270453 1907261 := bbase (se 3 (by rfl) ⟨357611, by rfl⟩ : syracuseStep 1907261 = 715223) (by norm_num)
theorem B18324053 : Blo 1270453 18324053 := bbase (se 8 (by rfl) ⟨107367, by rfl⟩ : syracuseStep 18324053 = 214735) (by norm_num)
theorem B1907285 : Blo 1270453 1907285 := bbase (se 8 (by rfl) ⟨11175, by rfl⟩ : syracuseStep 1907285 = 22351) (by norm_num)
theorem B1907309 : Blo 1270453 1907309 := bbase (se 3 (by rfl) ⟨357620, by rfl⟩ : syracuseStep 1907309 = 715241) (by norm_num)
theorem B2144893 : Blo 1270453 2144893 := bbase (se 3 (by rfl) ⟨402167, by rfl⟩ : syracuseStep 2144893 = 804335) (by norm_num)
theorem B1907333 : Blo 1270453 1907333 := bbase (se 4 (by rfl) ⟨178812, by rfl⟩ : syracuseStep 1907333 = 357625) (by norm_num)
theorem B3218069 : Blo 1270453 3218069 := bbase (se 6 (by rfl) ⟨75423, by rfl⟩ : syracuseStep 3218069 = 150847) (by norm_num)
theorem B1907357 : Blo 1270453 1907357 := bbase (se 3 (by rfl) ⟨357629, by rfl⟩ : syracuseStep 1907357 = 715259) (by norm_num)
theorem B1907381 : Blo 1270453 1907381 := bbase (se 5 (by rfl) ⟨89408, by rfl⟩ : syracuseStep 1907381 = 178817) (by norm_num)
theorem B1833661 : Blo 1270453 1833661 := bbase (se 3 (by rfl) ⟨343811, by rfl⟩ : syracuseStep 1833661 = 687623) (by norm_num)
theorem B1907405 : Blo 1270453 1907405 := bbase (se 3 (by rfl) ⟨357638, by rfl⟩ : syracuseStep 1907405 = 715277) (by norm_num)
theorem B2144981 : Blo 1270453 2144981 := bbase (se 7 (by rfl) ⟨25136, by rfl⟩ : syracuseStep 2144981 = 50273) (by norm_num)
theorem B1907429 : Blo 1270453 1907429 := bbase (se 4 (by rfl) ⟨178821, by rfl⟩ : syracuseStep 1907429 = 357643) (by norm_num)
theorem B1907453 : Blo 1270453 1907453 := bbase (se 3 (by rfl) ⟨357647, by rfl⟩ : syracuseStep 1907453 = 715295) (by norm_num)
theorem B1809173 : Blo 1270453 1809173 := bbase (se 6 (by rfl) ⟨42402, by rfl⟩ : syracuseStep 1809173 = 84805) (by norm_num)
theorem B1907477 : Blo 1270453 1907477 := bbase (se 6 (by rfl) ⟨44706, by rfl⟩ : syracuseStep 1907477 = 89413) (by norm_num)
theorem B1907501 : Blo 1270453 1907501 := bbase (se 3 (by rfl) ⟨357656, by rfl⟩ : syracuseStep 1907501 = 715313) (by norm_num)
theorem B1907525 : Blo 1270453 1907525 := bbase (se 4 (by rfl) ⟨178830, by rfl⟩ : syracuseStep 1907525 = 357661) (by norm_num)
theorem B2145109 : Blo 1270453 2145109 := bbase (se 9 (by rfl) ⟨6284, by rfl⟩ : syracuseStep 2145109 = 12569) (by norm_num)
theorem B6437717 : Blo 1270453 6437717 := bbase (se 9 (by rfl) ⟨18860, by rfl⟩ : syracuseStep 6437717 = 37721) (by norm_num)
theorem B1907549 : Blo 1270453 1907549 := bbase (se 3 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 1907549 = 715331) (by norm_num)
theorem B1809253 : Blo 1270453 1809253 := bbase (se 4 (by rfl) ⟨169617, by rfl⟩ : syracuseStep 1809253 = 339235) (by norm_num)
theorem B1907573 : Blo 1270453 1907573 := bbase (se 5 (by rfl) ⟨89417, by rfl⟩ : syracuseStep 1907573 = 178835) (by norm_num)
theorem B1907597 : Blo 1270453 1907597 := bbase (se 3 (by rfl) ⟨357674, by rfl⟩ : syracuseStep 1907597 = 715349) (by norm_num)
theorem B1907621 : Blo 1270453 1907621 := bbase (se 4 (by rfl) ⟨178839, by rfl⟩ : syracuseStep 1907621 = 357679) (by norm_num)
theorem B2145197 : Blo 1270453 2145197 := bbase (se 3 (by rfl) ⟨402224, by rfl⟩ : syracuseStep 2145197 = 804449) (by norm_num)
theorem B1907645 : Blo 1270453 1907645 := bbase (se 3 (by rfl) ⟨357683, by rfl⟩ : syracuseStep 1907645 = 715367) (by norm_num)
theorem B4291541 : Blo 1270453 4291541 := bbase (se 7 (by rfl) ⟨50291, by rfl⟩ : syracuseStep 4291541 = 100583) (by norm_num)
theorem B1907669 : Blo 1270453 1907669 := bbase (se 7 (by rfl) ⟨22355, by rfl⟩ : syracuseStep 1907669 = 44711) (by norm_num)
theorem B1809373 : Blo 1270453 1809373 := bbase (se 3 (by rfl) ⟨339257, by rfl⟩ : syracuseStep 1809373 = 678515) (by norm_num)
theorem B3218413 : Blo 1270453 3218413 := bbase (se 3 (by rfl) ⟨603452, by rfl⟩ : syracuseStep 3218413 = 1206905) (by norm_num)
theorem B1907693 : Blo 1270453 1907693 := bbase (se 3 (by rfl) ⟨357692, by rfl⟩ : syracuseStep 1907693 = 715385) (by norm_num)
theorem B1907717 : Blo 1270453 1907717 := bbase (se 4 (by rfl) ⟨178848, by rfl⟩ : syracuseStep 1907717 = 357697) (by norm_num)
theorem B1907741 : Blo 1270453 1907741 := bbase (se 3 (by rfl) ⟨357701, by rfl⟩ : syracuseStep 1907741 = 715403) (by norm_num)
theorem B2145325 : Blo 1270453 2145325 := bbase (se 3 (by rfl) ⟨402248, by rfl⟩ : syracuseStep 2145325 = 804497) (by norm_num)
theorem B1907765 : Blo 1270453 1907765 := bbase (se 5 (by rfl) ⟨89426, by rfl⟩ : syracuseStep 1907765 = 178853) (by norm_num)
theorem B1809469 : Blo 1270453 1809469 := bbase (se 3 (by rfl) ⟨339275, by rfl⟩ : syracuseStep 1809469 = 678551) (by norm_num)
theorem B1907789 : Blo 1270453 1907789 := bbase (se 3 (by rfl) ⟨357710, by rfl⟩ : syracuseStep 1907789 = 715421) (by norm_num)
theorem B3218525 : Blo 1270453 3218525 := bbase (se 3 (by rfl) ⟨603473, by rfl⟩ : syracuseStep 3218525 = 1206947) (by norm_num)
theorem B1907813 : Blo 1270453 1907813 := bbase (se 4 (by rfl) ⟨178857, by rfl⟩ : syracuseStep 1907813 = 357715) (by norm_num)
theorem B1907837 : Blo 1270453 1907837 := bbase (se 3 (by rfl) ⟨357719, by rfl⟩ : syracuseStep 1907837 = 715439) (by norm_num)
theorem B2145413 : Blo 1270453 2145413 := bbase (se 4 (by rfl) ⟨201132, by rfl⟩ : syracuseStep 2145413 = 402265) (by norm_num)
theorem B1907861 : Blo 1270453 1907861 := bbase (se 6 (by rfl) ⟨44715, by rfl⟩ : syracuseStep 1907861 = 89431) (by norm_num)
theorem B1907885 : Blo 1270453 1907885 := bbase (se 3 (by rfl) ⟨357728, by rfl⟩ : syracuseStep 1907885 = 715457) (by norm_num)
theorem B1907909 : Blo 1270453 1907909 := bbase (se 4 (by rfl) ⟨178866, by rfl⟩ : syracuseStep 1907909 = 357733) (by norm_num)
theorem B2145541 : Blo 1270453 2145541 := bbase (se 4 (by rfl) ⟨201144, by rfl⟩ : syracuseStep 2145541 = 402289) (by norm_num)
theorem B3865877 : Blo 1270453 3865877 := bbase (se 6 (by rfl) ⟨90606, by rfl⟩ : syracuseStep 3865877 = 181213) (by norm_num)
theorem B3218717 : Blo 1270453 3218717 := bbase (se 3 (by rfl) ⟨603509, by rfl⟩ : syracuseStep 3218717 = 1207019) (by norm_num)
theorem B2145629 : Blo 1270453 2145629 := bbase (se 3 (by rfl) ⟨402305, by rfl⟩ : syracuseStep 2145629 = 804611) (by norm_num)
theorem B2751877 : Blo 1270453 2751877 := bbase (se 4 (by rfl) ⟨257988, by rfl⟩ : syracuseStep 2751877 = 515977) (by norm_num)
theorem B4291973 : Blo 1270453 4291973 := bbase (se 4 (by rfl) ⟨402372, by rfl⟩ : syracuseStep 4291973 = 804745) (by norm_num)
theorem B2145757 : Blo 1270453 2145757 := bbase (se 3 (by rfl) ⟨402329, by rfl⟩ : syracuseStep 2145757 = 804659) (by norm_num)
theorem B1547785 : Blo 1270453 1547785 := bbase (se 2 (by rfl) ⟨580419, by rfl⟩ : syracuseStep 1547785 = 1160839) (by norm_num)
theorem B2858525 : Blo 1270453 2858525 := bbase (se 3 (by rfl) ⟨535973, by rfl⟩ : syracuseStep 2858525 = 1071947) (by norm_num)
theorem B3055133 : Blo 1270453 3055133 := bbase (se 3 (by rfl) ⟨572837, by rfl⟩ : syracuseStep 3055133 = 1145675) (by norm_num)
theorem B1809965 : Blo 1270453 1809965 := bbase (se 3 (by rfl) ⟨339368, by rfl⟩ : syracuseStep 1809965 = 678737) (by norm_num)
theorem B4824629 : Blo 1270453 4824629 := bbase (se 5 (by rfl) ⟨226154, by rfl⟩ : syracuseStep 4824629 = 452309) (by norm_num)
theorem B2145845 : Blo 1270453 2145845 := bbase (se 5 (by rfl) ⟨100586, by rfl⟩ : syracuseStep 2145845 = 201173) (by norm_num)
theorem B2858597 : Blo 1270453 2858597 := bbase (se 4 (by rfl) ⟨267993, by rfl⟩ : syracuseStep 2858597 = 535987) (by norm_num)
theorem B3219061 : Blo 1270453 3219061 := bbase (se 5 (by rfl) ⟨150893, by rfl⟩ : syracuseStep 3219061 = 301787) (by norm_num)
theorem B2858669 : Blo 1270453 2858669 := bbase (se 3 (by rfl) ⟨536000, by rfl⟩ : syracuseStep 2858669 = 1072001) (by norm_num)
theorem B3620533 : Blo 1270453 3620533 := bbase (se 5 (by rfl) ⟨169712, by rfl⟩ : syracuseStep 3620533 = 339425) (by norm_num)
theorem B2145973 : Blo 1270453 2145973 := bbase (se 5 (by rfl) ⟨100592, by rfl⟩ : syracuseStep 2145973 = 201185) (by norm_num)
theorem B3219173 : Blo 1270453 3219173 := bbase (se 4 (by rfl) ⟨301797, by rfl⟩ : syracuseStep 3219173 = 603595) (by norm_num)
theorem B2858741 : Blo 1270453 2858741 := bbase (se 5 (by rfl) ⟨134003, by rfl⟩ : syracuseStep 2858741 = 268007) (by norm_num)
theorem B1449721 : Blo 1270453 1449721 := bbase (se 2 (by rfl) ⟨543645, by rfl⟩ : syracuseStep 1449721 = 1087291) (by norm_num)
theorem B2146061 : Blo 1270453 2146061 := bbase (se 3 (by rfl) ⟨402386, by rfl⟩ : syracuseStep 2146061 = 804773) (by norm_num)
theorem B1548077 : Blo 1270453 1548077 := bbase (se 3 (by rfl) ⟨290264, by rfl⟩ : syracuseStep 1548077 = 580529) (by norm_num)
theorem B4079413 : Blo 1270453 4079413 := bbase (se 5 (by rfl) ⟨191222, by rfl⟩ : syracuseStep 4079413 = 382445) (by norm_num)
theorem B4292405 : Blo 1270453 4292405 := bbase (se 5 (by rfl) ⟨201206, by rfl⟩ : syracuseStep 4292405 = 402413) (by norm_num)
theorem B2858813 : Blo 1270453 2858813 := bbase (se 3 (by rfl) ⟨536027, by rfl⟩ : syracuseStep 2858813 = 1072055) (by norm_num)
theorem B4824917 : Blo 1270453 4824917 := bbase (se 9 (by rfl) ⟨14135, by rfl⟩ : syracuseStep 4824917 = 28271) (by norm_num)
theorem B3620693 : Blo 1270453 3620693 := bbase (se 9 (by rfl) ⟨10607, by rfl⟩ : syracuseStep 3620693 = 21215) (by norm_num)
theorem B5431141 : Blo 1270453 5431141 := bbase (se 4 (by rfl) ⟨509169, by rfl⟩ : syracuseStep 5431141 = 1018339) (by norm_num)
theorem B1449841 : Blo 1270453 1449841 := bbase (se 2 (by rfl) ⟨543690, by rfl⟩ : syracuseStep 1449841 = 1087381) (by norm_num)
theorem B3669877 : Blo 1270453 3669877 := bbase (se 5 (by rfl) ⟨172025, by rfl⟩ : syracuseStep 3669877 = 344051) (by norm_num)
theorem B2858885 : Blo 1270453 2858885 := bbase (se 4 (by rfl) ⟨268020, by rfl⟩ : syracuseStep 2858885 = 536041) (by norm_num)
theorem B2146189 : Blo 1270453 2146189 := bbase (se 3 (by rfl) ⟨402410, by rfl⟩ : syracuseStep 2146189 = 804821) (by norm_num)
theorem B3219365 : Blo 1270453 3219365 := bbase (se 4 (by rfl) ⟨301815, by rfl⟩ : syracuseStep 3219365 = 603631) (by norm_num)
theorem B2858957 : Blo 1270453 2858957 := bbase (se 3 (by rfl) ⟨536054, by rfl⟩ : syracuseStep 2858957 = 1072109) (by norm_num)
theorem B4071397 : Blo 1270453 4071397 := bbase (se 4 (by rfl) ⟨381693, by rfl⟩ : syracuseStep 4071397 = 763387) (by norm_num)
theorem B2146277 : Blo 1270453 2146277 := bbase (se 4 (by rfl) ⟨201213, by rfl⟩ : syracuseStep 2146277 = 402427) (by norm_num)
theorem B2859011 : Blo 1270453 2859011 := bstep (se 1 (by rfl) ⟨2144258, by rfl⟩ : syracuseStep 2859011 = 4288517) B4288517
theorem B4292621 : Blo 1270453 4292621 := bstep (se 3 (by rfl) ⟨804866, by rfl⟩ : syracuseStep 4292621 = 1609733) B1609733
theorem B3489841 : Blo 1270453 3489841 := bstep (se 2 (by rfl) ⟨1308690, by rfl⟩ : syracuseStep 3489841 = 2617381) B2617381
theorem B4292675 : Blo 1270453 4292675 := bstep (se 1 (by rfl) ⟨3219506, by rfl⟩ : syracuseStep 4292675 = 6439013) B6439013
theorem B2146385 : Blo 1270453 2146385 := bstep (se 2 (by rfl) ⟨804894, by rfl⟩ : syracuseStep 2146385 = 1609789) B1609789
theorem B3670211 : Blo 1270453 3670211 := bstep (se 1 (by rfl) ⟨2752658, by rfl⟩ : syracuseStep 3670211 = 5505317) B5505317
theorem B2859281 : Blo 1270453 2859281 := bstep (se 2 (by rfl) ⟨1072230, by rfl⟩ : syracuseStep 2859281 = 2144461) B2144461
theorem B2859299 : Blo 1270453 2859299 := bstep (se 1 (by rfl) ⟨2144474, by rfl⟩ : syracuseStep 2859299 = 4288949) B4288949
theorem B9650501 : Blo 1270453 9650501 := bstep (se 4 (by rfl) ⟨904734, by rfl⟩ : syracuseStep 9650501 = 1809469) B1809469
theorem B3481937 : Blo 1270453 3481937 := bstep (se 2 (by rfl) ⟨1305726, by rfl⟩ : syracuseStep 3481937 = 2611453) B2611453
theorem B16294243 : Blo 1270453 16294243 := bstep (se 1 (by rfl) ⟨12220682, by rfl⟩ : syracuseStep 16294243 = 24441365) B24441365
theorem B10314125 : Blo 1270453 10314125 := bstep (se 3 (by rfl) ⟨1933898, by rfl⟩ : syracuseStep 10314125 = 3867797) B3867797
theorem B18317765 : Blo 1270453 18317765 := bstep (se 4 (by rfl) ⟨1717290, by rfl⟩ : syracuseStep 18317765 = 3434581) B3434581
theorem B1450451 : Blo 1270453 1450451 := bstep (se 1 (by rfl) ⟨1087838, by rfl⟩ : syracuseStep 1450451 = 2175677) B2175677
theorem B2859569 : Blo 1270453 2859569 := bstep (se 2 (by rfl) ⟨1072338, by rfl⟩ : syracuseStep 2859569 = 2144677) B2144677
theorem B2859587 : Blo 1270453 2859587 := bstep (se 1 (by rfl) ⟨2144690, by rfl⟩ : syracuseStep 2859587 = 4289381) B4289381
theorem B1270467 : Blo 1270453 1270467 := bstep (se 1 (by rfl) ⟨952850, by rfl⟩ : syracuseStep 1270467 = 1905701) B1905701
theorem B3621581 : Blo 1270453 3621581 := bstep (se 3 (by rfl) ⟨679046, by rfl⟩ : syracuseStep 3621581 = 1358093) B1358093
theorem B1270483 : Blo 1270453 1270483 := bstep (se 1 (by rfl) ⟨952862, by rfl⟩ : syracuseStep 1270483 = 1905725) B1905725
theorem B1270499 : Blo 1270453 1270499 := bstep (se 1 (by rfl) ⟨952874, by rfl⟩ : syracuseStep 1270499 = 1905749) B1905749
theorem B1270515 : Blo 1270453 1270515 := bstep (se 1 (by rfl) ⟨952886, by rfl⟩ : syracuseStep 1270515 = 1905773) B1905773
theorem B1270531 : Blo 1270453 1270531 := bstep (se 1 (by rfl) ⟨952898, by rfl⟩ : syracuseStep 1270531 = 1905797) B1905797
theorem B1270547 : Blo 1270453 1270547 := bstep (se 1 (by rfl) ⟨952910, by rfl⟩ : syracuseStep 1270547 = 1905821) B1905821
theorem B1270563 : Blo 1270453 1270563 := bstep (se 1 (by rfl) ⟨952922, by rfl⟩ : syracuseStep 1270563 = 1905845) B1905845
theorem B1270579 : Blo 1270453 1270579 := bstep (se 1 (by rfl) ⟨952934, by rfl⟩ : syracuseStep 1270579 = 1905869) B1905869
theorem B1270595 : Blo 1270453 1270595 := bstep (se 1 (by rfl) ⟨952946, by rfl⟩ : syracuseStep 1270595 = 1905893) B1905893
theorem B8373061 : Blo 1270453 8373061 := bstep (se 4 (by rfl) ⟨784974, by rfl⟩ : syracuseStep 8373061 = 1569949) B1569949
theorem B2859857 : Blo 1270453 2859857 := bstep (se 2 (by rfl) ⟨1072446, by rfl⟩ : syracuseStep 2859857 = 2144893) B2144893
theorem B1270611 : Blo 1270453 1270611 := bstep (se 1 (by rfl) ⟨952958, by rfl⟩ : syracuseStep 1270611 = 1905917) B1905917
theorem B1270627 : Blo 1270453 1270627 := bstep (se 1 (by rfl) ⟨952970, by rfl⟩ : syracuseStep 1270627 = 1905941) B1905941
theorem B2859875 : Blo 1270453 2859875 := bstep (se 1 (by rfl) ⟨2144906, by rfl⟩ : syracuseStep 2859875 = 4289813) B4289813
theorem B1270643 : Blo 1270453 1270643 := bstep (se 1 (by rfl) ⟨952982, by rfl⟩ : syracuseStep 1270643 = 1905965) B1905965
theorem B1270659 : Blo 1270453 1270659 := bstep (se 1 (by rfl) ⟨952994, by rfl⟩ : syracuseStep 1270659 = 1905989) B1905989
theorem B3621763 : Blo 1270453 3621763 := bstep (se 1 (by rfl) ⟨2716322, by rfl⟩ : syracuseStep 3621763 = 5432645) B5432645
theorem B1270675 : Blo 1270453 1270675 := bstep (se 1 (by rfl) ⟨953006, by rfl⟩ : syracuseStep 1270675 = 1906013) B1906013
theorem B1270691 : Blo 1270453 1270691 := bstep (se 1 (by rfl) ⟨953018, by rfl⟩ : syracuseStep 1270691 = 1906037) B1906037
theorem B3621809 : Blo 1270453 3621809 := bstep (se 2 (by rfl) ⟨1358178, by rfl⟩ : syracuseStep 3621809 = 2716357) B2716357
theorem B1270707 : Blo 1270453 1270707 := bstep (se 1 (by rfl) ⟨953030, by rfl⟩ : syracuseStep 1270707 = 1906061) B1906061
theorem B1270723 : Blo 1270453 1270723 := bstep (se 1 (by rfl) ⟨953042, by rfl⟩ : syracuseStep 1270723 = 1906085) B1906085
theorem B1270739 : Blo 1270453 1270739 := bstep (se 1 (by rfl) ⟨953054, by rfl⟩ : syracuseStep 1270739 = 1906109) B1906109
theorem B1270755 : Blo 1270453 1270755 := bstep (se 1 (by rfl) ⟨953066, by rfl⟩ : syracuseStep 1270755 = 1906133) B1906133
theorem B1270771 : Blo 1270453 1270771 := bstep (se 1 (by rfl) ⟨953078, by rfl⟩ : syracuseStep 1270771 = 1906157) B1906157
theorem B1270787 : Blo 1270453 1270787 := bstep (se 1 (by rfl) ⟨953090, by rfl⟩ : syracuseStep 1270787 = 1906181) B1906181
theorem B1270803 : Blo 1270453 1270803 := bstep (se 1 (by rfl) ⟨953102, by rfl⟩ : syracuseStep 1270803 = 1906205) B1906205
theorem B1270819 : Blo 1270453 1270819 := bstep (se 1 (by rfl) ⟨953114, by rfl⟩ : syracuseStep 1270819 = 1906229) B1906229
theorem B1270835 : Blo 1270453 1270835 := bstep (se 1 (by rfl) ⟨953126, by rfl⟩ : syracuseStep 1270835 = 1906253) B1906253
theorem B1270851 : Blo 1270453 1270851 := bstep (se 1 (by rfl) ⟨953138, by rfl⟩ : syracuseStep 1270851 = 1906277) B1906277
theorem B9159749 : Blo 1270453 9159749 := bstep (se 4 (by rfl) ⟨858726, by rfl⟩ : syracuseStep 9159749 = 1717453) B1717453
theorem B1270867 : Blo 1270453 1270867 := bstep (se 1 (by rfl) ⟨953150, by rfl⟩ : syracuseStep 1270867 = 1906301) B1906301
theorem B1270883 : Blo 1270453 1270883 := bstep (se 1 (by rfl) ⟨953162, by rfl⟩ : syracuseStep 1270883 = 1906325) B1906325
theorem B2860145 : Blo 1270453 2860145 := bstep (se 2 (by rfl) ⟨1072554, by rfl⟩ : syracuseStep 2860145 = 2145109) B2145109
theorem B3867761 : Blo 1270453 3867761 := bstep (se 2 (by rfl) ⟨1450410, by rfl⟩ : syracuseStep 3867761 = 2900821) B2900821
theorem B1270899 : Blo 1270453 1270899 := bstep (se 1 (by rfl) ⟨953174, by rfl⟩ : syracuseStep 1270899 = 1906349) B1906349
theorem B1270915 : Blo 1270453 1270915 := bstep (se 1 (by rfl) ⟨953186, by rfl⟩ : syracuseStep 1270915 = 1906373) B1906373
theorem B2860163 : Blo 1270453 2860163 := bstep (se 1 (by rfl) ⟨2145122, by rfl⟩ : syracuseStep 2860163 = 4290245) B4290245
theorem B6431885 : Blo 1270453 6431885 := bstep (se 3 (by rfl) ⟨1205978, by rfl⟩ : syracuseStep 6431885 = 2411957) B2411957
theorem B4072589 : Blo 1270453 4072589 := bstep (se 3 (by rfl) ⟨763610, by rfl⟩ : syracuseStep 4072589 = 1527221) B1527221
theorem B1270931 : Blo 1270453 1270931 := bstep (se 1 (by rfl) ⟨953198, by rfl⟩ : syracuseStep 1270931 = 1906397) B1906397
theorem B1270947 : Blo 1270453 1270947 := bstep (se 1 (by rfl) ⟨953210, by rfl⟩ : syracuseStep 1270947 = 1906421) B1906421
theorem B1270963 : Blo 1270453 1270963 := bstep (se 1 (by rfl) ⟨953222, by rfl⟩ : syracuseStep 1270963 = 1906445) B1906445
theorem B1270979 : Blo 1270453 1270979 := bstep (se 1 (by rfl) ⟨953234, by rfl⟩ : syracuseStep 1270979 = 1906469) B1906469
theorem B1270995 : Blo 1270453 1270995 := bstep (se 1 (by rfl) ⟨953246, by rfl⟩ : syracuseStep 1270995 = 1906493) B1906493
theorem B1271011 : Blo 1270453 1271011 := bstep (se 1 (by rfl) ⟨953258, by rfl⟩ : syracuseStep 1271011 = 1906517) B1906517
theorem B7242979 : Blo 1270453 7242979 := bstep (se 1 (by rfl) ⟨5432234, by rfl⟩ : syracuseStep 7242979 = 10864469) B10864469
theorem B1271027 : Blo 1270453 1271027 := bstep (se 1 (by rfl) ⟨953270, by rfl⟩ : syracuseStep 1271027 = 1906541) B1906541
theorem B1271043 : Blo 1270453 1271043 := bstep (se 1 (by rfl) ⟨953282, by rfl⟩ : syracuseStep 1271043 = 1906565) B1906565
theorem B1271059 : Blo 1270453 1271059 := bstep (se 1 (by rfl) ⟨953294, by rfl⟩ : syracuseStep 1271059 = 1906589) B1906589
theorem B1271075 : Blo 1270453 1271075 := bstep (se 1 (by rfl) ⟨953306, by rfl⟩ : syracuseStep 1271075 = 1906613) B1906613
theorem B1271091 : Blo 1270453 1271091 := bstep (se 1 (by rfl) ⟨953318, by rfl⟩ : syracuseStep 1271091 = 1906637) B1906637
theorem B1271107 : Blo 1270453 1271107 := bstep (se 1 (by rfl) ⟨953330, by rfl⟩ : syracuseStep 1271107 = 1906661) B1906661
theorem B1271123 : Blo 1270453 1271123 := bstep (se 1 (by rfl) ⟨953342, by rfl⟩ : syracuseStep 1271123 = 1906685) B1906685
theorem B1271139 : Blo 1270453 1271139 := bstep (se 1 (by rfl) ⟨953354, by rfl⟩ : syracuseStep 1271139 = 1906709) B1906709
theorem B13583729 : Blo 1270453 13583729 := bstep (se 2 (by rfl) ⟨5093898, by rfl⟩ : syracuseStep 13583729 = 10187797) B10187797
theorem B1271155 : Blo 1270453 1271155 := bstep (se 1 (by rfl) ⟨953366, by rfl⟩ : syracuseStep 1271155 = 1906733) B1906733
theorem B1271171 : Blo 1270453 1271171 := bstep (se 1 (by rfl) ⟨953378, by rfl⟩ : syracuseStep 1271171 = 1906757) B1906757
theorem B2860433 : Blo 1270453 2860433 := bstep (se 2 (by rfl) ⟨1072662, by rfl⟩ : syracuseStep 2860433 = 2145325) B2145325
theorem B1271187 : Blo 1270453 1271187 := bstep (se 1 (by rfl) ⟨953390, by rfl⟩ : syracuseStep 1271187 = 1906781) B1906781
theorem B1271203 : Blo 1270453 1271203 := bstep (se 1 (by rfl) ⟨953402, by rfl⟩ : syracuseStep 1271203 = 1906805) B1906805
theorem B2860451 : Blo 1270453 2860451 := bstep (se 1 (by rfl) ⟨2145338, by rfl⟩ : syracuseStep 2860451 = 4290677) B4290677
theorem B1271219 : Blo 1270453 1271219 := bstep (se 1 (by rfl) ⟨953414, by rfl⟩ : syracuseStep 1271219 = 1906829) B1906829
theorem B1271235 : Blo 1270453 1271235 := bstep (se 1 (by rfl) ⟨953426, by rfl⟩ : syracuseStep 1271235 = 1906853) B1906853
theorem B4826573 : Blo 1270453 4826573 := bstep (se 3 (by rfl) ⟨904982, by rfl⟩ : syracuseStep 4826573 = 1809965) B1809965
theorem B1271251 : Blo 1270453 1271251 := bstep (se 1 (by rfl) ⟨953438, by rfl⟩ : syracuseStep 1271251 = 1906877) B1906877
theorem B1271267 : Blo 1270453 1271267 := bstep (se 1 (by rfl) ⟨953450, by rfl⟩ : syracuseStep 1271267 = 1906901) B1906901
theorem B1271283 : Blo 1270453 1271283 := bstep (se 1 (by rfl) ⟨953462, by rfl⟩ : syracuseStep 1271283 = 1906925) B1906925
theorem B1271299 : Blo 1270453 1271299 := bstep (se 1 (by rfl) ⟨953474, by rfl⟩ : syracuseStep 1271299 = 1906949) B1906949
theorem B1271315 : Blo 1270453 1271315 := bstep (se 1 (by rfl) ⟨953486, by rfl⟩ : syracuseStep 1271315 = 1906973) B1906973
theorem B1271331 : Blo 1270453 1271331 := bstep (se 1 (by rfl) ⟨953498, by rfl⟩ : syracuseStep 1271331 = 1906997) B1906997
theorem B1271347 : Blo 1270453 1271347 := bstep (se 1 (by rfl) ⟨953510, by rfl⟩ : syracuseStep 1271347 = 1907021) B1907021
theorem B1271363 : Blo 1270453 1271363 := bstep (se 1 (by rfl) ⟨953522, by rfl⟩ : syracuseStep 1271363 = 1907045) B1907045
theorem B1271379 : Blo 1270453 1271379 := bstep (se 1 (by rfl) ⟨953534, by rfl⟩ : syracuseStep 1271379 = 1907069) B1907069
theorem B1271395 : Blo 1270453 1271395 := bstep (se 1 (by rfl) ⟨953546, by rfl⟩ : syracuseStep 1271395 = 1907093) B1907093
theorem B1271411 : Blo 1270453 1271411 := bstep (se 1 (by rfl) ⟨953558, by rfl⟩ : syracuseStep 1271411 = 1907117) B1907117
theorem B1271427 : Blo 1270453 1271427 := bstep (se 1 (by rfl) ⟨953570, by rfl⟩ : syracuseStep 1271427 = 1907141) B1907141
theorem B1271443 : Blo 1270453 1271443 := bstep (se 1 (by rfl) ⟨953582, by rfl⟩ : syracuseStep 1271443 = 1907165) B1907165
theorem B1271459 : Blo 1270453 1271459 := bstep (se 1 (by rfl) ⟨953594, by rfl⟩ : syracuseStep 1271459 = 1907189) B1907189
theorem B2860721 : Blo 1270453 2860721 := bstep (se 2 (by rfl) ⟨1072770, by rfl⟩ : syracuseStep 2860721 = 2145541) B2145541
theorem B1271475 : Blo 1270453 1271475 := bstep (se 1 (by rfl) ⟨953606, by rfl⟩ : syracuseStep 1271475 = 1907213) B1907213
theorem B2860739 : Blo 1270453 2860739 := bstep (se 1 (by rfl) ⟨2145554, by rfl⟩ : syracuseStep 2860739 = 4291109) B4291109
theorem B1271491 : Blo 1270453 1271491 := bstep (se 1 (by rfl) ⟨953618, by rfl⟩ : syracuseStep 1271491 = 1907237) B1907237
theorem B1271507 : Blo 1270453 1271507 := bstep (se 1 (by rfl) ⟨953630, by rfl⟩ : syracuseStep 1271507 = 1907261) B1907261
theorem B12216035 : Blo 1270453 12216035 := bstep (se 1 (by rfl) ⟨9162026, by rfl⟩ : syracuseStep 12216035 = 18324053) B18324053
theorem B1271523 : Blo 1270453 1271523 := bstep (se 1 (by rfl) ⟨953642, by rfl⟩ : syracuseStep 1271523 = 1907285) B1907285
theorem B7243505 : Blo 1270453 7243505 := bstep (se 2 (by rfl) ⟨2716314, by rfl⟩ : syracuseStep 7243505 = 5432629) B5432629
theorem B1271539 : Blo 1270453 1271539 := bstep (se 1 (by rfl) ⟨953654, by rfl⟩ : syracuseStep 1271539 = 1907309) B1907309
theorem B1271555 : Blo 1270453 1271555 := bstep (se 1 (by rfl) ⟨953666, by rfl⟩ : syracuseStep 1271555 = 1907333) B1907333
theorem B1271571 : Blo 1270453 1271571 := bstep (se 1 (by rfl) ⟨953678, by rfl⟩ : syracuseStep 1271571 = 1907357) B1907357
theorem B1271587 : Blo 1270453 1271587 := bstep (se 1 (by rfl) ⟨953690, by rfl⟩ : syracuseStep 1271587 = 1907381) B1907381
theorem B1271603 : Blo 1270453 1271603 := bstep (se 1 (by rfl) ⟨953702, by rfl⟩ : syracuseStep 1271603 = 1907405) B1907405
theorem B1271619 : Blo 1270453 1271619 := bstep (se 1 (by rfl) ⟨953714, by rfl⟩ : syracuseStep 1271619 = 1907429) B1907429
theorem B1271635 : Blo 1270453 1271635 := bstep (se 1 (by rfl) ⟨953726, by rfl⟩ : syracuseStep 1271635 = 1907453) B1907453
theorem B1271651 : Blo 1270453 1271651 := bstep (se 1 (by rfl) ⟨953738, by rfl⟩ : syracuseStep 1271651 = 1907477) B1907477
theorem B1271667 : Blo 1270453 1271667 := bstep (se 1 (by rfl) ⟨953750, by rfl⟩ : syracuseStep 1271667 = 1907501) B1907501
theorem B1271683 : Blo 1270453 1271683 := bstep (se 1 (by rfl) ⟨953762, by rfl⟩ : syracuseStep 1271683 = 1907525) B1907525
theorem B39118733 : Blo 1270453 39118733 := bstep (se 3 (by rfl) ⟨7334762, by rfl⟩ : syracuseStep 39118733 = 14669525) B14669525
theorem B1271699 : Blo 1270453 1271699 := bstep (se 1 (by rfl) ⟨953774, by rfl⟩ : syracuseStep 1271699 = 1907549) B1907549
theorem B1271715 : Blo 1270453 1271715 := bstep (se 1 (by rfl) ⟨953786, by rfl⟩ : syracuseStep 1271715 = 1907573) B1907573
theorem B1271731 : Blo 1270453 1271731 := bstep (se 1 (by rfl) ⟨953798, by rfl⟩ : syracuseStep 1271731 = 1907597) B1907597
theorem B1271747 : Blo 1270453 1271747 := bstep (se 1 (by rfl) ⟨953810, by rfl⟩ : syracuseStep 1271747 = 1907621) B1907621
theorem B2861009 : Blo 1270453 2861009 := bstep (se 2 (by rfl) ⟨1072878, by rfl⟩ : syracuseStep 2861009 = 2145757) B2145757
theorem B1271763 : Blo 1270453 1271763 := bstep (se 1 (by rfl) ⟨953822, by rfl⟩ : syracuseStep 1271763 = 1907645) B1907645
theorem B8144867 : Blo 1270453 8144867 := bstep (se 1 (by rfl) ⟨6108650, by rfl⟩ : syracuseStep 8144867 = 12217301) B12217301
theorem B2861027 : Blo 1270453 2861027 := bstep (se 1 (by rfl) ⟨2145770, by rfl⟩ : syracuseStep 2861027 = 4291541) B4291541
theorem B1271779 : Blo 1270453 1271779 := bstep (se 1 (by rfl) ⟨953834, by rfl⟩ : syracuseStep 1271779 = 1907669) B1907669
theorem B1271795 : Blo 1270453 1271795 := bstep (se 1 (by rfl) ⟨953846, by rfl⟩ : syracuseStep 1271795 = 1907693) B1907693
theorem B1271811 : Blo 1270453 1271811 := bstep (se 1 (by rfl) ⟨953858, by rfl⟩ : syracuseStep 1271811 = 1907717) B1907717
theorem B4073485 : Blo 1270453 4073485 := bstep (se 3 (by rfl) ⟨763778, by rfl⟩ : syracuseStep 4073485 = 1527557) B1527557
theorem B1271827 : Blo 1270453 1271827 := bstep (se 1 (by rfl) ⟨953870, by rfl⟩ : syracuseStep 1271827 = 1907741) B1907741
theorem B1271843 : Blo 1270453 1271843 := bstep (se 1 (by rfl) ⟨953882, by rfl⟩ : syracuseStep 1271843 = 1907765) B1907765
theorem B1271859 : Blo 1270453 1271859 := bstep (se 1 (by rfl) ⟨953894, by rfl⟩ : syracuseStep 1271859 = 1907789) B1907789
theorem B1271875 : Blo 1270453 1271875 := bstep (se 1 (by rfl) ⟨953906, by rfl⟩ : syracuseStep 1271875 = 1907813) B1907813
theorem B1271891 : Blo 1270453 1271891 := bstep (se 1 (by rfl) ⟨953918, by rfl⟩ : syracuseStep 1271891 = 1907837) B1907837
theorem B1271907 : Blo 1270453 1271907 := bstep (se 1 (by rfl) ⟨953930, by rfl⟩ : syracuseStep 1271907 = 1907861) B1907861
theorem B1271923 : Blo 1270453 1271923 := bstep (se 1 (by rfl) ⟨953942, by rfl⟩ : syracuseStep 1271923 = 1907885) B1907885
theorem B1271939 : Blo 1270453 1271939 := bstep (se 1 (by rfl) ⟨953954, by rfl⟩ : syracuseStep 1271939 = 1907909) B1907909
theorem B4827377 : Blo 1270453 4827377 := bstep (se 2 (by rfl) ⟨1810266, by rfl⟩ : syracuseStep 4827377 = 3620533) B3620533
theorem B2861297 : Blo 1270453 2861297 := bstep (se 2 (by rfl) ⟨1072986, by rfl⟩ : syracuseStep 2861297 = 2145973) B2145973
theorem B2861315 : Blo 1270453 2861315 := bstep (se 1 (by rfl) ⟨2145986, by rfl⟩ : syracuseStep 2861315 = 4291973) B4291973
theorem B2714033 : Blo 1270453 2714033 := bstep (se 2 (by rfl) ⟨1017762, by rfl⟩ : syracuseStep 2714033 = 2035525) B2035525
theorem B4893169 : Blo 1270453 4893169 := bstep (se 2 (by rfl) ⟨1834938, by rfl⟩ : syracuseStep 4893169 = 3669877) B3669877
theorem B2861585 : Blo 1270453 2861585 := bstep (se 2 (by rfl) ⟨1073094, by rfl⟩ : syracuseStep 2861585 = 2146189) B2146189
theorem B2861603 : Blo 1270453 2861603 := bstep (se 1 (by rfl) ⟨2146202, by rfl⟩ : syracuseStep 2861603 = 4292405) B4292405
theorem B1608275 : Blo 1270453 1608275 := bstep (se 1 (by rfl) ⟨1206206, by rfl⟩ : syracuseStep 1608275 = 2412413) B2412413
theorem B8702597 : Blo 1270453 8702597 := bstep (se 4 (by rfl) ⟨815868, by rfl⟩ : syracuseStep 8702597 = 1631737) B1631737
theorem B1526467 : Blo 1270453 1526467 := bstep (se 1 (by rfl) ⟨1144850, by rfl⟩ : syracuseStep 1526467 = 2289701) B2289701
theorem B2861873 : Blo 1270453 2861873 := bstep (se 2 (by rfl) ⟨1073202, by rfl⟩ : syracuseStep 2861873 = 2146405) B2146405
theorem B2861891 : Blo 1270453 2861891 := bstep (se 1 (by rfl) ⟨2146418, by rfl⟩ : syracuseStep 2861891 = 4292837) B4292837
theorem B4074371 : Blo 1270453 4074371 := bstep (se 1 (by rfl) ⟨3055778, by rfl⟩ : syracuseStep 4074371 = 6111557) B6111557
theorem B4828045 : Blo 1270453 4828045 := bstep (se 3 (by rfl) ⟨905258, by rfl⟩ : syracuseStep 4828045 = 1810517) B1810517
theorem B2714563 : Blo 1270453 2714563 := bstep (se 1 (by rfl) ⟨2035922, by rfl⟩ : syracuseStep 2714563 = 4071845) B4071845
theorem B17632241 : Blo 1270453 17632241 := bstep (se 2 (by rfl) ⟨6612090, by rfl⟩ : syracuseStep 17632241 = 13224181) B13224181
theorem B1526851 : Blo 1270453 1526851 := bstep (se 1 (by rfl) ⟨1145138, by rfl⟩ : syracuseStep 1526851 = 2290277) B2290277
theorem B5221475 : Blo 1270453 5221475 := bstep (se 1 (by rfl) ⟨3916106, by rfl⟩ : syracuseStep 5221475 = 7832213) B7832213
theorem B2092211 : Blo 1270453 2092211 := bstep (se 1 (by rfl) ⟨1569158, by rfl⟩ : syracuseStep 2092211 = 3138317) B3138317
theorem B1608979 : Blo 1270453 1608979 := bstep (se 1 (by rfl) ⟨1206734, by rfl⟩ : syracuseStep 1608979 = 2413469) B2413469
theorem B1609075 : Blo 1270453 1609075 := bstep (se 1 (by rfl) ⟨1206806, by rfl⟩ : syracuseStep 1609075 = 2413613) B2413613
theorem B4828835 : Blo 1270453 4828835 := bstep (se 1 (by rfl) ⟨3621626, by rfl⟩ : syracuseStep 4828835 = 7243253) B7243253
theorem B1429267 : Blo 1270453 1429267 := bstep (se 1 (by rfl) ⟨1071950, by rfl⟩ : syracuseStep 1429267 = 2143901) B2143901
theorem B4288301 : Blo 1270453 4288301 := bstep (se 3 (by rfl) ⟨804056, by rfl⟩ : syracuseStep 4288301 = 1608113) B1608113
theorem B2412337 : Blo 1270453 2412337 := bstep (se 2 (by rfl) ⟨904626, by rfl⟩ : syracuseStep 2412337 = 1809253) B1809253
theorem B4288355 : Blo 1270453 4288355 := bstep (se 1 (by rfl) ⟨3216266, by rfl⟩ : syracuseStep 4288355 = 6432533) B6432533
theorem B1609571 : Blo 1270453 1609571 := bstep (se 1 (by rfl) ⟨1207178, by rfl⟩ : syracuseStep 1609571 = 2414357) B2414357
theorem B16281485 : Blo 1270453 16281485 := bstep (se 3 (by rfl) ⟨3052778, by rfl⟩ : syracuseStep 16281485 = 6105557) B6105557
theorem B1429411 : Blo 1270453 1429411 := bstep (se 1 (by rfl) ⟨1072058, by rfl⟩ : syracuseStep 1429411 = 2144117) B2144117
theorem B2412497 : Blo 1270453 2412497 := bstep (se 2 (by rfl) ⟨904686, by rfl⟩ : syracuseStep 2412497 = 1809373) B1809373
theorem B2035667 : Blo 1270453 2035667 := bstep (se 1 (by rfl) ⟨1526750, by rfl⟩ : syracuseStep 2035667 = 3053501) B3053501
theorem B2289649 : Blo 1270453 2289649 := bstep (se 2 (by rfl) ⟨858618, by rfl⟩ : syracuseStep 2289649 = 1717237) B1717237
theorem B6434801 : Blo 1270453 6434801 := bstep (se 2 (by rfl) ⟨2413050, by rfl⟩ : syracuseStep 6434801 = 4826101) B4826101
theorem B1429555 : Blo 1270453 1429555 := bstep (se 1 (by rfl) ⟨1072166, by rfl⟩ : syracuseStep 1429555 = 2144333) B2144333
theorem B4288625 : Blo 1270453 4288625 := bstep (se 2 (by rfl) ⟨1608234, by rfl⟩ : syracuseStep 4288625 = 3216469) B3216469
theorem B1429699 : Blo 1270453 1429699 := bstep (se 1 (by rfl) ⟨1072274, by rfl⟩ : syracuseStep 1429699 = 2144549) B2144549
theorem B2035955 : Blo 1270453 2035955 := bstep (se 1 (by rfl) ⟨1526966, by rfl⟩ : syracuseStep 2035955 = 3053933) B3053933
theorem B1429843 : Blo 1270453 1429843 := bstep (se 1 (by rfl) ⟨1072382, by rfl⟩ : syracuseStep 1429843 = 2144765) B2144765
theorem B2412899 : Blo 1270453 2412899 := bstep (se 1 (by rfl) ⟨1809674, by rfl⟩ : syracuseStep 2412899 = 3619349) B3619349
theorem B2716049 : Blo 1270453 2716049 := bstep (se 2 (by rfl) ⟨1018518, by rfl⟩ : syracuseStep 2716049 = 2037037) B2037037
theorem B2716067 : Blo 1270453 2716067 := bstep (se 1 (by rfl) ⟨2037050, by rfl⟩ : syracuseStep 2716067 = 4074101) B4074101
theorem B1429987 : Blo 1270453 1429987 := bstep (se 1 (by rfl) ⟨1072490, by rfl⟩ : syracuseStep 1429987 = 2144981) B2144981
theorem B2290225 : Blo 1270453 2290225 := bstep (se 2 (by rfl) ⟨858834, by rfl⟩ : syracuseStep 2290225 = 1717669) B1717669
theorem B1430131 : Blo 1270453 1430131 := bstep (se 1 (by rfl) ⟨1072598, by rfl⟩ : syracuseStep 1430131 = 2145197) B2145197
theorem B4289165 : Blo 1270453 4289165 := bstep (se 3 (by rfl) ⟨804218, by rfl⟩ : syracuseStep 4289165 = 1608437) B1608437
theorem B4289219 : Blo 1270453 4289219 := bstep (se 1 (by rfl) ⟨3216914, by rfl⟩ : syracuseStep 4289219 = 6433829) B6433829
theorem B14676677 : Blo 1270453 14676677 := bstep (se 4 (by rfl) ⟨1375938, by rfl⟩ : syracuseStep 14676677 = 2751877) B2751877
theorem B1430275 : Blo 1270453 1430275 := bstep (se 1 (by rfl) ⟨1072706, by rfl⟩ : syracuseStep 1430275 = 2145413) B2145413
theorem B3216145 : Blo 1270453 3216145 := bstep (se 2 (by rfl) ⟨1206054, by rfl⟩ : syracuseStep 3216145 = 2412109) B2412109
theorem B2577251 : Blo 1270453 2577251 := bstep (se 1 (by rfl) ⟨1932938, by rfl⟩ : syracuseStep 2577251 = 3865877) B3865877
theorem B1430419 : Blo 1270453 1430419 := bstep (se 1 (by rfl) ⟨1072814, by rfl⟩ : syracuseStep 1430419 = 2145629) B2145629
theorem B7238605 : Blo 1270453 7238605 := bstep (se 3 (by rfl) ⟨1357238, by rfl⟩ : syracuseStep 7238605 = 2714477) B2714477
theorem B4289489 : Blo 1270453 4289489 := bstep (se 2 (by rfl) ⟨1608558, by rfl⟩ : syracuseStep 4289489 = 3217117) B3217117
theorem B1905683 : Blo 1270453 1905683 := bstep (se 1 (by rfl) ⟨1429262, by rfl⟩ : syracuseStep 1905683 = 2858525) B2858525
theorem B2036755 : Blo 1270453 2036755 := bstep (se 1 (by rfl) ⟨1527566, by rfl⟩ : syracuseStep 2036755 = 3055133) B3055133
theorem B3863587 : Blo 1270453 3863587 := bstep (se 1 (by rfl) ⟨2897690, by rfl⟩ : syracuseStep 3863587 = 5795381) B5795381
theorem B3216419 : Blo 1270453 3216419 := bstep (se 1 (by rfl) ⟨2412314, by rfl⟩ : syracuseStep 3216419 = 4824629) B4824629
theorem B1430563 : Blo 1270453 1430563 := bstep (se 1 (by rfl) ⟨1072922, by rfl⟩ : syracuseStep 1430563 = 2145845) B2145845
theorem B1905713 : Blo 1270453 1905713 := bstep (se 2 (by rfl) ⟨714642, by rfl⟩ : syracuseStep 1905713 = 1429285) B1429285
theorem B1905731 : Blo 1270453 1905731 := bstep (se 1 (by rfl) ⟨1429298, by rfl⟩ : syracuseStep 1905731 = 2858597) B2858597
theorem B1905761 : Blo 1270453 1905761 := bstep (se 2 (by rfl) ⟨714660, by rfl⟩ : syracuseStep 1905761 = 1429321) B1429321
theorem B3617891 : Blo 1270453 3617891 := bstep (se 1 (by rfl) ⟨2713418, by rfl⟩ : syracuseStep 3617891 = 5426837) B5426837
theorem B1905779 : Blo 1270453 1905779 := bstep (se 1 (by rfl) ⟨1429334, by rfl⟩ : syracuseStep 1905779 = 2858669) B2858669
theorem B1356931 : Blo 1270453 1356931 := bstep (se 1 (by rfl) ⟨1017698, by rfl⟩ : syracuseStep 1356931 = 2035397) B2035397
theorem B1905809 : Blo 1270453 1905809 := bstep (se 2 (by rfl) ⟨714678, by rfl⟩ : syracuseStep 1905809 = 1429357) B1429357
theorem B2036897 : Blo 1270453 2036897 := bstep (se 2 (by rfl) ⟨763836, by rfl⟩ : syracuseStep 2036897 = 1527673) B1527673
theorem B1905827 : Blo 1270453 1905827 := bstep (se 1 (by rfl) ⟨1429370, by rfl⟩ : syracuseStep 1905827 = 2858741) B2858741
theorem B1430707 : Blo 1270453 1430707 := bstep (se 1 (by rfl) ⟨1073030, by rfl⟩ : syracuseStep 1430707 = 2146061) B2146061
theorem B1905857 : Blo 1270453 1905857 := bstep (se 2 (by rfl) ⟨714696, by rfl⟩ : syracuseStep 1905857 = 1429393) B1429393
theorem B2036929 : Blo 1270453 2036929 := bstep (se 2 (by rfl) ⟨763848, by rfl⟩ : syracuseStep 2036929 = 1527697) B1527697
theorem B1905875 : Blo 1270453 1905875 := bstep (se 1 (by rfl) ⟨1429406, by rfl⟩ : syracuseStep 1905875 = 2858813) B2858813
theorem B3216611 : Blo 1270453 3216611 := bstep (se 1 (by rfl) ⟨2412458, by rfl⟩ : syracuseStep 3216611 = 4824917) B4824917
theorem B2413795 : Blo 1270453 2413795 := bstep (se 1 (by rfl) ⟨1810346, by rfl⟩ : syracuseStep 2413795 = 3620693) B3620693
theorem B1905905 : Blo 1270453 1905905 := bstep (se 2 (by rfl) ⟨714714, by rfl⟩ : syracuseStep 1905905 = 1429429) B1429429
theorem B1905923 : Blo 1270453 1905923 := bstep (se 1 (by rfl) ⟨1429442, by rfl⟩ : syracuseStep 1905923 = 2858885) B2858885
theorem B1905953 : Blo 1270453 1905953 := bstep (se 2 (by rfl) ⟨714732, by rfl⟩ : syracuseStep 1905953 = 1429465) B1429465
theorem B5428529 : Blo 1270453 5428529 := bstep (se 2 (by rfl) ⟨2035698, by rfl⟩ : syracuseStep 5428529 = 4071397) B4071397
theorem B1905971 : Blo 1270453 1905971 := bstep (se 1 (by rfl) ⟨1429478, by rfl⟩ : syracuseStep 1905971 = 2858957) B2858957
theorem B1430851 : Blo 1270453 1430851 := bstep (se 1 (by rfl) ⟨1073138, by rfl⟩ : syracuseStep 1430851 = 2146277) B2146277
theorem B1906001 : Blo 1270453 1906001 := bstep (se 2 (by rfl) ⟨714750, by rfl⟩ : syracuseStep 1906001 = 1429501) B1429501
theorem B1906019 : Blo 1270453 1906019 := bstep (se 1 (by rfl) ⟨1429514, by rfl⟩ : syracuseStep 1906019 = 2859029) B2859029
theorem B5428579 : Blo 1270453 5428579 := bstep (se 1 (by rfl) ⟨4071434, by rfl⟩ : syracuseStep 5428579 = 8142869) B8142869
theorem B12219761 : Blo 1270453 12219761 := bstep (se 2 (by rfl) ⟨4582410, by rfl⟩ : syracuseStep 12219761 = 9164821) B9164821
theorem B1906049 : Blo 1270453 1906049 := bstep (se 2 (by rfl) ⟨714768, by rfl⟩ : syracuseStep 1906049 = 1429537) B1429537
theorem B2413955 : Blo 1270453 2413955 := bstep (se 1 (by rfl) ⟨1810466, by rfl⟩ : syracuseStep 2413955 = 3620933) B3620933
theorem B1906067 : Blo 1270453 1906067 := bstep (se 1 (by rfl) ⟨1429550, by rfl⟩ : syracuseStep 1906067 = 2859101) B2859101
theorem B6436259 : Blo 1270453 6436259 := bstep (se 1 (by rfl) ⟨4827194, by rfl⟩ : syracuseStep 6436259 = 9654389) B9654389
theorem B1906097 : Blo 1270453 1906097 := bstep (se 2 (by rfl) ⟨714786, by rfl⟩ : syracuseStep 1906097 = 1429573) B1429573
theorem B1906115 : Blo 1270453 1906115 := bstep (se 1 (by rfl) ⟨1429586, by rfl⟩ : syracuseStep 1906115 = 2859173) B2859173
theorem B1906145 : Blo 1270453 1906145 := bstep (se 2 (by rfl) ⟨714804, by rfl⟩ : syracuseStep 1906145 = 1429609) B1429609
theorem B32568803 : Blo 1270453 32568803 := bstep (se 1 (by rfl) ⟨24426602, by rfl⟩ : syracuseStep 32568803 = 48853205) B48853205
theorem B4290029 : Blo 1270453 4290029 := bstep (se 3 (by rfl) ⟨804380, by rfl⟩ : syracuseStep 4290029 = 1608761) B1608761
theorem B1906163 : Blo 1270453 1906163 := bstep (se 1 (by rfl) ⟨1429622, by rfl⟩ : syracuseStep 1906163 = 2859245) B2859245
theorem B1906193 : Blo 1270453 1906193 := bstep (se 2 (by rfl) ⟨714822, by rfl⟩ : syracuseStep 1906193 = 1429645) B1429645
theorem B1906211 : Blo 1270453 1906211 := bstep (se 1 (by rfl) ⟨1429658, by rfl⟩ : syracuseStep 1906211 = 2859317) B2859317
theorem B4290083 : Blo 1270453 4290083 := bstep (se 1 (by rfl) ⟨3217562, by rfl⟩ : syracuseStep 4290083 = 6435125) B6435125
theorem B1906241 : Blo 1270453 1906241 := bstep (se 2 (by rfl) ⟨714840, by rfl⟩ : syracuseStep 1906241 = 1429681) B1429681
theorem B1906259 : Blo 1270453 1906259 := bstep (se 1 (by rfl) ⟨1429694, by rfl⟩ : syracuseStep 1906259 = 2859389) B2859389
theorem B1906289 : Blo 1270453 1906289 := bstep (se 2 (by rfl) ⟨714858, by rfl⟩ : syracuseStep 1906289 = 1429717) B1429717
theorem B1906307 : Blo 1270453 1906307 := bstep (se 1 (by rfl) ⟨1429730, by rfl⟩ : syracuseStep 1906307 = 2859461) B2859461
theorem B1906337 : Blo 1270453 1906337 := bstep (se 2 (by rfl) ⟨714876, by rfl⟩ : syracuseStep 1906337 = 1429753) B1429753
theorem B2143921 : Blo 1270453 2143921 := bstep (se 2 (by rfl) ⟨803970, by rfl⟩ : syracuseStep 2143921 = 1607941) B1607941
theorem B1906355 : Blo 1270453 1906355 := bstep (se 1 (by rfl) ⟨1429766, by rfl⟩ : syracuseStep 1906355 = 2859533) B2859533
theorem B1906385 : Blo 1270453 1906385 := bstep (se 2 (by rfl) ⟨714894, by rfl⟩ : syracuseStep 1906385 = 1429789) B1429789
theorem B2143955 : Blo 1270453 2143955 := bstep (se 1 (by rfl) ⟨1607966, by rfl⟩ : syracuseStep 2143955 = 3215933) B3215933
theorem B1906403 : Blo 1270453 1906403 := bstep (se 1 (by rfl) ⟨1429802, by rfl⟩ : syracuseStep 1906403 = 2859605) B2859605
theorem B1357555 : Blo 1270453 1357555 := bstep (se 1 (by rfl) ⟨1018166, by rfl⟩ : syracuseStep 1357555 = 2036333) B2036333
theorem B1906433 : Blo 1270453 1906433 := bstep (se 2 (by rfl) ⟨714912, by rfl⟩ : syracuseStep 1906433 = 1429825) B1429825
theorem B1906451 : Blo 1270453 1906451 := bstep (se 1 (by rfl) ⟨1429838, by rfl⟩ : syracuseStep 1906451 = 2859677) B2859677
theorem B127112981 : Blo 1270453 127112981 := bstep (se 6 (by rfl) ⟨2979210, by rfl⟩ : syracuseStep 127112981 = 5958421) B5958421
theorem B1906481 : Blo 1270453 1906481 := bstep (se 2 (by rfl) ⟨714930, by rfl⟩ : syracuseStep 1906481 = 1429861) B1429861
theorem B4290353 : Blo 1270453 4290353 := bstep (se 2 (by rfl) ⟨1608882, by rfl⟩ : syracuseStep 4290353 = 3217765) B3217765
theorem B3307313 : Blo 1270453 3307313 := bstep (se 2 (by rfl) ⟨1240242, by rfl⟩ : syracuseStep 3307313 = 2480485) B2480485
theorem B16512821 : Blo 1270453 16512821 := bstep (se 5 (by rfl) ⟨774038, by rfl⟩ : syracuseStep 16512821 = 1548077) B1548077
theorem B1906499 : Blo 1270453 1906499 := bstep (se 1 (by rfl) ⟨1429874, by rfl⟩ : syracuseStep 1906499 = 2859749) B2859749
theorem B2144083 : Blo 1270453 2144083 := bstep (se 1 (by rfl) ⟨1608062, by rfl⟩ : syracuseStep 2144083 = 3216125) B3216125
theorem B1906529 : Blo 1270453 1906529 := bstep (se 2 (by rfl) ⟨714948, by rfl⟩ : syracuseStep 1906529 = 1429897) B1429897
theorem B1906547 : Blo 1270453 1906547 := bstep (se 1 (by rfl) ⟨1429910, by rfl⟩ : syracuseStep 1906547 = 2859821) B2859821
theorem B1906577 : Blo 1270453 1906577 := bstep (se 2 (by rfl) ⟨714966, by rfl⟩ : syracuseStep 1906577 = 1429933) B1429933
theorem B1906595 : Blo 1270453 1906595 := bstep (se 1 (by rfl) ⟨1429946, by rfl⟩ : syracuseStep 1906595 = 2859893) B2859893
theorem B1906625 : Blo 1270453 1906625 := bstep (se 2 (by rfl) ⟨714984, by rfl⟩ : syracuseStep 1906625 = 1429969) B1429969
theorem B1906643 : Blo 1270453 1906643 := bstep (se 1 (by rfl) ⟨1429982, by rfl⟩ : syracuseStep 1906643 = 2859965) B2859965
theorem B2209747 : Blo 1270453 2209747 := bstep (se 1 (by rfl) ⟨1657310, by rfl⟩ : syracuseStep 2209747 = 3314621) B3314621
theorem B2144225 : Blo 1270453 2144225 := bstep (se 2 (by rfl) ⟨804084, by rfl⟩ : syracuseStep 2144225 = 1608169) B1608169
theorem B1906673 : Blo 1270453 1906673 := bstep (se 2 (by rfl) ⟨715002, by rfl⟩ : syracuseStep 1906673 = 1430005) B1430005
theorem B1906691 : Blo 1270453 1906691 := bstep (se 1 (by rfl) ⟨1430018, by rfl⟩ : syracuseStep 1906691 = 2860037) B2860037
theorem B9656333 : Blo 1270453 9656333 := bstep (se 3 (by rfl) ⟨1810562, by rfl⟩ : syracuseStep 9656333 = 3621125) B3621125
theorem B1906721 : Blo 1270453 1906721 := bstep (se 2 (by rfl) ⟨715020, by rfl⟩ : syracuseStep 1906721 = 1430041) B1430041
theorem B1906739 : Blo 1270453 1906739 := bstep (se 1 (by rfl) ⟨1430054, by rfl⟩ : syracuseStep 1906739 = 2860109) B2860109
theorem B3618893 : Blo 1270453 3618893 := bstep (se 3 (by rfl) ⟨678542, by rfl⟩ : syracuseStep 3618893 = 1357085) B1357085
theorem B1906769 : Blo 1270453 1906769 := bstep (se 2 (by rfl) ⟨715038, by rfl⟩ : syracuseStep 1906769 = 1430077) B1430077
theorem B2144353 : Blo 1270453 2144353 := bstep (se 2 (by rfl) ⟨804132, by rfl⟩ : syracuseStep 2144353 = 1608265) B1608265
theorem B1906787 : Blo 1270453 1906787 := bstep (se 1 (by rfl) ⟨1430090, by rfl⟩ : syracuseStep 1906787 = 2860181) B2860181
theorem B1906817 : Blo 1270453 1906817 := bstep (se 2 (by rfl) ⟨715056, by rfl⟩ : syracuseStep 1906817 = 1430113) B1430113
theorem B2144387 : Blo 1270453 2144387 := bstep (se 1 (by rfl) ⟨1608290, by rfl⟩ : syracuseStep 2144387 = 3216581) B3216581
theorem B3217553 : Blo 1270453 3217553 := bstep (se 2 (by rfl) ⟨1206582, by rfl⟩ : syracuseStep 3217553 = 2413165) B2413165
theorem B1906835 : Blo 1270453 1906835 := bstep (se 1 (by rfl) ⟨1430126, by rfl⟩ : syracuseStep 1906835 = 2860253) B2860253
theorem B1906865 : Blo 1270453 1906865 := bstep (se 2 (by rfl) ⟨715074, by rfl⟩ : syracuseStep 1906865 = 1430149) B1430149
theorem B3217603 : Blo 1270453 3217603 := bstep (se 1 (by rfl) ⟨2413202, by rfl⟩ : syracuseStep 3217603 = 4826405) B4826405
theorem B1906883 : Blo 1270453 1906883 := bstep (se 1 (by rfl) ⟨1430162, by rfl⟩ : syracuseStep 1906883 = 2860325) B2860325
theorem B6437069 : Blo 1270453 6437069 := bstep (se 3 (by rfl) ⟨1206950, by rfl⟩ : syracuseStep 6437069 = 2413901) B2413901
theorem B1906913 : Blo 1270453 1906913 := bstep (se 2 (by rfl) ⟨715092, by rfl⟩ : syracuseStep 1906913 = 1430185) B1430185
theorem B1906931 : Blo 1270453 1906931 := bstep (se 1 (by rfl) ⟨1430198, by rfl⟩ : syracuseStep 1906931 = 2860397) B2860397
theorem B2144515 : Blo 1270453 2144515 := bstep (se 1 (by rfl) ⟨1608386, by rfl⟩ : syracuseStep 2144515 = 3216773) B3216773
theorem B3619075 : Blo 1270453 3619075 := bstep (se 1 (by rfl) ⟨2714306, by rfl⟩ : syracuseStep 3619075 = 5428613) B5428613
theorem B2291971 : Blo 1270453 2291971 := bstep (se 1 (by rfl) ⟨1718978, by rfl⟩ : syracuseStep 2291971 = 3437957) B3437957
theorem B1906961 : Blo 1270453 1906961 := bstep (se 2 (by rfl) ⟨715110, by rfl⟩ : syracuseStep 1906961 = 1430221) B1430221
theorem B1906979 : Blo 1270453 1906979 := bstep (se 1 (by rfl) ⟨1430234, by rfl⟩ : syracuseStep 1906979 = 2860469) B2860469
theorem B1907009 : Blo 1270453 1907009 := bstep (se 2 (by rfl) ⟨715128, by rfl⟩ : syracuseStep 1907009 = 1430257) B1430257
theorem B9779525 : Blo 1270453 9779525 := bstep (se 4 (by rfl) ⟨916830, by rfl⟩ : syracuseStep 9779525 = 1833661) B1833661
theorem B4290893 : Blo 1270453 4290893 := bstep (se 3 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 4290893 = 1609085) B1609085
theorem B3217745 : Blo 1270453 3217745 := bstep (se 2 (by rfl) ⟨1206654, by rfl⟩ : syracuseStep 3217745 = 2413309) B2413309
theorem B1907027 : Blo 1270453 1907027 := bstep (se 1 (by rfl) ⟨1430270, by rfl⟩ : syracuseStep 1907027 = 2860541) B2860541
theorem B1907057 : Blo 1270453 1907057 := bstep (se 2 (by rfl) ⟨715146, by rfl⟩ : syracuseStep 1907057 = 1430293) B1430293
theorem B1907075 : Blo 1270453 1907075 := bstep (se 1 (by rfl) ⟨1430306, by rfl⟩ : syracuseStep 1907075 = 2860613) B2860613
theorem B4290947 : Blo 1270453 4290947 := bstep (se 1 (by rfl) ⟨3218210, by rfl⟩ : syracuseStep 4290947 = 6436421) B6436421
theorem B2144657 : Blo 1270453 2144657 := bstep (se 2 (by rfl) ⟨804246, by rfl⟩ : syracuseStep 2144657 = 1608493) B1608493
theorem B1907105 : Blo 1270453 1907105 := bstep (se 2 (by rfl) ⟨715164, by rfl⟩ : syracuseStep 1907105 = 1430329) B1430329
theorem B3619235 : Blo 1270453 3619235 := bstep (se 1 (by rfl) ⟨2714426, by rfl⟩ : syracuseStep 3619235 = 5428853) B5428853
theorem B1907123 : Blo 1270453 1907123 := bstep (se 1 (by rfl) ⟨1430342, by rfl⟩ : syracuseStep 1907123 = 2860685) B2860685
theorem B1718707 : Blo 1270453 1718707 := bstep (se 1 (by rfl) ⟨1289030, by rfl⟩ : syracuseStep 1718707 = 2578061) B2578061
theorem B1907153 : Blo 1270453 1907153 := bstep (se 2 (by rfl) ⟨715182, by rfl⟩ : syracuseStep 1907153 = 1430365) B1430365
theorem B1907171 : Blo 1270453 1907171 := bstep (se 1 (by rfl) ⟨1430378, by rfl⟩ : syracuseStep 1907171 = 2860757) B2860757
theorem B1907201 : Blo 1270453 1907201 := bstep (se 2 (by rfl) ⟨715200, by rfl⟩ : syracuseStep 1907201 = 1430401) B1430401
theorem B2144785 : Blo 1270453 2144785 := bstep (se 2 (by rfl) ⟨804294, by rfl⟩ : syracuseStep 2144785 = 1608589) B1608589
theorem B1907219 : Blo 1270453 1907219 := bstep (se 1 (by rfl) ⟨1430414, by rfl⟩ : syracuseStep 1907219 = 2860829) B2860829
theorem B2062883 : Blo 1270453 2062883 := bstep (se 1 (by rfl) ⟨1547162, by rfl⟩ : syracuseStep 2062883 = 3094325) B3094325
theorem B3054115 : Blo 1270453 3054115 := bstep (se 1 (by rfl) ⟨2290586, by rfl⟩ : syracuseStep 3054115 = 4581173) B4581173
theorem B1907249 : Blo 1270453 1907249 := bstep (se 2 (by rfl) ⟨715218, by rfl⟩ : syracuseStep 1907249 = 1430437) B1430437
theorem B2144819 : Blo 1270453 2144819 := bstep (se 1 (by rfl) ⟨1608614, by rfl⟩ : syracuseStep 2144819 = 3217229) B3217229
theorem B1907267 : Blo 1270453 1907267 := bstep (se 1 (by rfl) ⟨1430450, by rfl⟩ : syracuseStep 1907267 = 2860901) B2860901
theorem B8141381 : Blo 1270453 8141381 := bstep (se 4 (by rfl) ⟨763254, by rfl⟩ : syracuseStep 8141381 = 1526509) B1526509
theorem B1907297 : Blo 1270453 1907297 := bstep (se 2 (by rfl) ⟨715236, by rfl⟩ : syracuseStep 1907297 = 1430473) B1430473
theorem B1907315 : Blo 1270453 1907315 := bstep (se 1 (by rfl) ⟨1430486, by rfl⟩ : syracuseStep 1907315 = 2860973) B2860973
theorem B7731845 : Blo 1270453 7731845 := bstep (se 4 (by rfl) ⟨724860, by rfl⟩ : syracuseStep 7731845 = 1449721) B1449721
theorem B4291217 : Blo 1270453 4291217 := bstep (se 2 (by rfl) ⟨1609206, by rfl⟩ : syracuseStep 4291217 = 3218413) B3218413
theorem B1907345 : Blo 1270453 1907345 := bstep (se 2 (by rfl) ⟨715254, by rfl⟩ : syracuseStep 1907345 = 1430509) B1430509
theorem B1809059 : Blo 1270453 1809059 := bstep (se 1 (by rfl) ⟨1356794, by rfl⟩ : syracuseStep 1809059 = 2713589) B2713589
theorem B6871715 : Blo 1270453 6871715 := bstep (se 1 (by rfl) ⟨5153786, by rfl⟩ : syracuseStep 6871715 = 10307573) B10307573
theorem B1907363 : Blo 1270453 1907363 := bstep (se 1 (by rfl) ⟨1430522, by rfl⟩ : syracuseStep 1907363 = 2861045) B2861045
theorem B2144947 : Blo 1270453 2144947 := bstep (se 1 (by rfl) ⟨1608710, by rfl⟩ : syracuseStep 2144947 = 3217421) B3217421
theorem B1907393 : Blo 1270453 1907393 := bstep (se 2 (by rfl) ⟨715272, by rfl⟩ : syracuseStep 1907393 = 1430545) B1430545
theorem B2898641 : Blo 1270453 2898641 := bstep (se 2 (by rfl) ⟨1086990, by rfl⟩ : syracuseStep 2898641 = 2173981) B2173981
theorem B1907411 : Blo 1270453 1907411 := bstep (se 1 (by rfl) ⟨1430558, by rfl⟩ : syracuseStep 1907411 = 2861117) B2861117
theorem B1907441 : Blo 1270453 1907441 := bstep (se 2 (by rfl) ⟨715290, by rfl⟩ : syracuseStep 1907441 = 1430581) B1430581
theorem B1907459 : Blo 1270453 1907459 := bstep (se 1 (by rfl) ⟨1430594, by rfl⟩ : syracuseStep 1907459 = 2861189) B2861189
theorem B1907489 : Blo 1270453 1907489 := bstep (se 2 (by rfl) ⟨715308, by rfl⟩ : syracuseStep 1907489 = 1430617) B1430617
theorem B1907507 : Blo 1270453 1907507 := bstep (se 1 (by rfl) ⟨1430630, by rfl⟩ : syracuseStep 1907507 = 2861261) B2861261
theorem B2145089 : Blo 1270453 2145089 := bstep (se 2 (by rfl) ⟨804408, by rfl⟩ : syracuseStep 2145089 = 1608817) B1608817
theorem B1907537 : Blo 1270453 1907537 := bstep (se 2 (by rfl) ⟨715326, by rfl⟩ : syracuseStep 1907537 = 1430653) B1430653
theorem B1907555 : Blo 1270453 1907555 := bstep (se 1 (by rfl) ⟨1430666, by rfl⟩ : syracuseStep 1907555 = 2861333) B2861333
theorem B1907585 : Blo 1270453 1907585 := bstep (se 2 (by rfl) ⟨715344, by rfl⟩ : syracuseStep 1907585 = 1430689) B1430689
theorem B7240589 : Blo 1270453 7240589 := bstep (se 3 (by rfl) ⟨1357610, by rfl⟩ : syracuseStep 7240589 = 2715221) B2715221
theorem B1907603 : Blo 1270453 1907603 := bstep (se 1 (by rfl) ⟨1430702, by rfl⟩ : syracuseStep 1907603 = 2861405) B2861405
theorem B1907633 : Blo 1270453 1907633 := bstep (se 2 (by rfl) ⟨715362, by rfl⟩ : syracuseStep 1907633 = 1430725) B1430725
theorem B2145217 : Blo 1270453 2145217 := bstep (se 2 (by rfl) ⟨804456, by rfl⟩ : syracuseStep 2145217 = 1608913) B1608913
theorem B1907651 : Blo 1270453 1907651 := bstep (se 1 (by rfl) ⟨1430738, by rfl⟩ : syracuseStep 1907651 = 2861477) B2861477
theorem B21756869 : Blo 1270453 21756869 := bstep (se 4 (by rfl) ⟨2039706, by rfl⟩ : syracuseStep 21756869 = 4079413) B4079413
theorem B1907681 : Blo 1270453 1907681 := bstep (se 2 (by rfl) ⟨715380, by rfl⟩ : syracuseStep 1907681 = 1430761) B1430761
theorem B2145251 : Blo 1270453 2145251 := bstep (se 1 (by rfl) ⟨1608938, by rfl⟩ : syracuseStep 2145251 = 3217877) B3217877
theorem B1907699 : Blo 1270453 1907699 := bstep (se 1 (by rfl) ⟨1430774, by rfl⟩ : syracuseStep 1907699 = 2861549) B2861549
theorem B1907729 : Blo 1270453 1907729 := bstep (se 2 (by rfl) ⟨715398, by rfl⟩ : syracuseStep 1907729 = 1430797) B1430797
theorem B1907747 : Blo 1270453 1907747 := bstep (se 1 (by rfl) ⟨1430810, by rfl⟩ : syracuseStep 1907747 = 2861621) B2861621
theorem B1907777 : Blo 1270453 1907777 := bstep (se 2 (by rfl) ⟨715416, by rfl⟩ : syracuseStep 1907777 = 1430833) B1430833
theorem B1907795 : Blo 1270453 1907795 := bstep (se 1 (by rfl) ⟨1430846, by rfl⟩ : syracuseStep 1907795 = 2861693) B2861693
theorem B2145379 : Blo 1270453 2145379 := bstep (se 1 (by rfl) ⟨1609034, by rfl⟩ : syracuseStep 2145379 = 3218069) B3218069
theorem B4070513 : Blo 1270453 4070513 := bstep (se 2 (by rfl) ⟨1526442, by rfl⟩ : syracuseStep 4070513 = 3052885) B3052885
theorem B1907825 : Blo 1270453 1907825 := bstep (se 2 (by rfl) ⟨715434, by rfl⟩ : syracuseStep 1907825 = 1430869) B1430869
theorem B1907843 : Blo 1270453 1907843 := bstep (se 1 (by rfl) ⟨1430882, by rfl⟩ : syracuseStep 1907843 = 2861765) B2861765
theorem B1907873 : Blo 1270453 1907873 := bstep (se 2 (by rfl) ⟨715452, by rfl⟩ : syracuseStep 1907873 = 1430905) B1430905
theorem B4291757 : Blo 1270453 4291757 := bstep (se 3 (by rfl) ⟨804704, by rfl⟩ : syracuseStep 4291757 = 1609409) B1609409
theorem B1907891 : Blo 1270453 1907891 := bstep (se 1 (by rfl) ⟨1430918, by rfl⟩ : syracuseStep 1907891 = 2861837) B2861837
theorem B1907921 : Blo 1270453 1907921 := bstep (se 2 (by rfl) ⟨715470, by rfl⟩ : syracuseStep 1907921 = 1430941) B1430941
theorem B4291811 : Blo 1270453 4291811 := bstep (se 1 (by rfl) ⟨3218858, by rfl⟩ : syracuseStep 4291811 = 6437717) B6437717
theorem B2145521 : Blo 1270453 2145521 := bstep (se 2 (by rfl) ⟨804570, by rfl⟩ : syracuseStep 2145521 = 1609141) B1609141
theorem B1809697 : Blo 1270453 1809697 := bstep (se 2 (by rfl) ⟨678636, by rfl⟩ : syracuseStep 1809697 = 1357273) B1357273
theorem B3218737 : Blo 1270453 3218737 := bstep (se 2 (by rfl) ⟨1207026, by rfl⟩ : syracuseStep 3218737 = 2414053) B2414053
theorem B2063713 : Blo 1270453 2063713 := bstep (se 2 (by rfl) ⟨773892, by rfl⟩ : syracuseStep 2063713 = 1547785) B1547785
theorem B2145649 : Blo 1270453 2145649 := bstep (se 2 (by rfl) ⟨804618, by rfl⟩ : syracuseStep 2145649 = 1609237) B1609237
theorem B7839089 : Blo 1270453 7839089 := bstep (se 2 (by rfl) ⟨2939658, by rfl⟩ : syracuseStep 7839089 = 5879317) B5879317
theorem B4824461 : Blo 1270453 4824461 := bstep (se 3 (by rfl) ⟨904586, by rfl⟩ : syracuseStep 4824461 = 1809173) B1809173
theorem B1809811 : Blo 1270453 1809811 := bstep (se 1 (by rfl) ⟨1357358, by rfl⟩ : syracuseStep 1809811 = 2714717) B2714717
theorem B2145683 : Blo 1270453 2145683 := bstep (se 1 (by rfl) ⟨1609262, by rfl⟩ : syracuseStep 2145683 = 3218525) B3218525
theorem B3620305 : Blo 1270453 3620305 := bstep (se 2 (by rfl) ⟨1357614, by rfl⟩ : syracuseStep 3620305 = 2715229) B2715229
theorem B4292081 : Blo 1270453 4292081 := bstep (se 2 (by rfl) ⟨1609530, by rfl⟩ : syracuseStep 4292081 = 3219061) B3219061
theorem B2145811 : Blo 1270453 2145811 := bstep (se 1 (by rfl) ⟨1609358, by rfl⟩ : syracuseStep 2145811 = 3218717) B3218717
theorem B3219011 : Blo 1270453 3219011 := bstep (se 1 (by rfl) ⟨2414258, by rfl⟩ : syracuseStep 3219011 = 4828517) B4828517
theorem B2145953 : Blo 1270453 2145953 := bstep (se 2 (by rfl) ⟨804732, by rfl⟩ : syracuseStep 2145953 = 1609465) B1609465
theorem B5430989 : Blo 1270453 5430989 := bstep (se 3 (by rfl) ⟨1018310, by rfl⟩ : syracuseStep 5430989 = 2036621) B2036621
theorem B2858705 : Blo 1270453 2858705 := bstep (se 2 (by rfl) ⟨1072014, by rfl⟩ : syracuseStep 2858705 = 2144029) B2144029
theorem B2858723 : Blo 1270453 2858723 := bstep (se 1 (by rfl) ⟨2144042, by rfl⟩ : syracuseStep 2858723 = 4288085) B4288085
theorem B3219203 : Blo 1270453 3219203 := bstep (se 1 (by rfl) ⟨2414402, by rfl⟩ : syracuseStep 3219203 = 4828805) B4828805
theorem B2146081 : Blo 1270453 2146081 := bstep (se 2 (by rfl) ⟨804780, by rfl⟩ : syracuseStep 2146081 = 1609561) B1609561
theorem B7241521 : Blo 1270453 7241521 := bstep (se 2 (by rfl) ⟨2715570, by rfl⟩ : syracuseStep 7241521 = 5431141) B5431141
theorem B18579253 : Blo 1270453 18579253 := bstep (se 5 (by rfl) ⟨870902, by rfl⟩ : syracuseStep 18579253 = 1741805) B1741805
theorem B1933121 : Blo 1270453 1933121 := bstep (se 2 (by rfl) ⟨724920, by rfl⟩ : syracuseStep 1933121 = 1449841) B1449841
theorem B2146115 : Blo 1270453 2146115 := bstep (se 1 (by rfl) ⟨1609586, by rfl⟩ : syracuseStep 2146115 = 3219173) B3219173
theorem B3055441 : Blo 1270453 3055441 := bstep (se 2 (by rfl) ⟨1145790, by rfl⟩ : syracuseStep 3055441 = 2291581) B2291581
theorem B2146243 : Blo 1270453 2146243 := bstep (se 1 (by rfl) ⟨1609682, by rfl⟩ : syracuseStep 2146243 = 3219365) B3219365
theorem B2858993 : Blo 1270453 2858993 := bstep (se 2 (by rfl) ⟨1072122, by rfl⟩ : syracuseStep 2858993 = 2144245) B2144245
theorem B5431313 : Blo 1270453 5431313 := bstep (se 2 (by rfl) ⟨2036742, by rfl⟩ : syracuseStep 5431313 = 4073485) B4073485
theorem B4653121 : Blo 1270453 4653121 := bstep (se 2 (by rfl) ⟨1744920, by rfl⟩ : syracuseStep 4653121 = 3489841) B3489841
theorem B2859083 : Blo 1270453 2859083 := bstep (se 1 (by rfl) ⟨2144312, by rfl⟩ : syracuseStep 2859083 = 4288625) B4288625
theorem B10862693 : Blo 1270453 10862693 := bstep (se 4 (by rfl) ⟨1018377, by rfl⟩ : syracuseStep 10862693 = 2036755) B2036755
theorem B2859137 : Blo 1270453 2859137 := bstep (se 2 (by rfl) ⟨1072176, by rfl⟩ : syracuseStep 2859137 = 2144353) B2144353
theorem B1810711 : Blo 1270453 1810711 := bstep (se 1 (by rfl) ⟨1358033, by rfl⟩ : syracuseStep 1810711 = 2716067) B2716067
theorem B10314029 : Blo 1270453 10314029 := bstep (se 3 (by rfl) ⟨1933880, by rfl⟩ : syracuseStep 10314029 = 3867761) B3867761
theorem B2859353 : Blo 1270453 2859353 := bstep (se 2 (by rfl) ⟨1072257, by rfl⟩ : syracuseStep 2859353 = 2144515) B2144515
theorem B4825433 : Blo 1270453 4825433 := bstep (se 2 (by rfl) ⟨1809537, by rfl⟩ : syracuseStep 4825433 = 3619075) B3619075
theorem B3055961 : Blo 1270453 3055961 := bstep (se 2 (by rfl) ⟨1145985, by rfl⟩ : syracuseStep 3055961 = 2291971) B2291971
theorem B2859443 : Blo 1270453 2859443 := bstep (se 1 (by rfl) ⟨2144582, by rfl⟩ : syracuseStep 2859443 = 4289165) B4289165
theorem B2859479 : Blo 1270453 2859479 := bstep (se 1 (by rfl) ⟨2144609, by rfl⟩ : syracuseStep 2859479 = 4289219) B4289219
theorem B21725657 : Blo 1270453 21725657 := bstep (se 2 (by rfl) ⟨8147121, by rfl⟩ : syracuseStep 21725657 = 16294243) B16294243
theorem B2859659 : Blo 1270453 2859659 := bstep (se 1 (by rfl) ⟨2144744, by rfl⟩ : syracuseStep 2859659 = 4289489) B4289489
theorem B1270455 : Blo 1270453 1270455 := bstep (se 1 (by rfl) ⟨952841, by rfl⟩ : syracuseStep 1270455 = 1905683) B1905683
theorem B2859713 : Blo 1270453 2859713 := bstep (se 2 (by rfl) ⟨1072392, by rfl⟩ : syracuseStep 2859713 = 2144785) B2144785
theorem B1270475 : Blo 1270453 1270475 := bstep (se 1 (by rfl) ⟨952856, by rfl⟩ : syracuseStep 1270475 = 1905713) B1905713
theorem B1270487 : Blo 1270453 1270487 := bstep (se 1 (by rfl) ⟨952865, by rfl⟩ : syracuseStep 1270487 = 1905731) B1905731
theorem B4072153 : Blo 1270453 4072153 := bstep (se 2 (by rfl) ⟨1527057, by rfl⟩ : syracuseStep 4072153 = 3054115) B3054115
theorem B1270507 : Blo 1270453 1270507 := bstep (se 1 (by rfl) ⟨952880, by rfl⟩ : syracuseStep 1270507 = 1905761) B1905761
theorem B1270519 : Blo 1270453 1270519 := bstep (se 1 (by rfl) ⟨952889, by rfl⟩ : syracuseStep 1270519 = 1905779) B1905779
theorem B1270539 : Blo 1270453 1270539 := bstep (se 1 (by rfl) ⟨952904, by rfl⟩ : syracuseStep 1270539 = 1905809) B1905809
theorem B1270551 : Blo 1270453 1270551 := bstep (se 1 (by rfl) ⟨952913, by rfl⟩ : syracuseStep 1270551 = 1905827) B1905827
theorem B1270571 : Blo 1270453 1270571 := bstep (se 1 (by rfl) ⟨952928, by rfl⟩ : syracuseStep 1270571 = 1905857) B1905857
theorem B1270583 : Blo 1270453 1270583 := bstep (se 1 (by rfl) ⟨952937, by rfl⟩ : syracuseStep 1270583 = 1905875) B1905875
theorem B1270603 : Blo 1270453 1270603 := bstep (se 1 (by rfl) ⟨952952, by rfl⟩ : syracuseStep 1270603 = 1905905) B1905905
theorem B1270615 : Blo 1270453 1270615 := bstep (se 1 (by rfl) ⟨952961, by rfl⟩ : syracuseStep 1270615 = 1905923) B1905923
theorem B1270635 : Blo 1270453 1270635 := bstep (se 1 (by rfl) ⟨952976, by rfl⟩ : syracuseStep 1270635 = 1905953) B1905953
theorem B1270647 : Blo 1270453 1270647 := bstep (se 1 (by rfl) ⟨952985, by rfl⟩ : syracuseStep 1270647 = 1905971) B1905971
theorem B1270667 : Blo 1270453 1270667 := bstep (se 1 (by rfl) ⟨953000, by rfl⟩ : syracuseStep 1270667 = 1906001) B1906001
theorem B1270679 : Blo 1270453 1270679 := bstep (se 1 (by rfl) ⟨953009, by rfl⟩ : syracuseStep 1270679 = 1906019) B1906019
theorem B2859929 : Blo 1270453 2859929 := bstep (se 2 (by rfl) ⟨1072473, by rfl⟩ : syracuseStep 2859929 = 2144947) B2144947
theorem B1270699 : Blo 1270453 1270699 := bstep (se 1 (by rfl) ⟨953024, by rfl⟩ : syracuseStep 1270699 = 1906049) B1906049
theorem B1270711 : Blo 1270453 1270711 := bstep (se 1 (by rfl) ⟨953033, by rfl⟩ : syracuseStep 1270711 = 1906067) B1906067
theorem B1270731 : Blo 1270453 1270731 := bstep (se 1 (by rfl) ⟨953048, by rfl⟩ : syracuseStep 1270731 = 1906097) B1906097
theorem B1270743 : Blo 1270453 1270743 := bstep (se 1 (by rfl) ⟨953057, by rfl⟩ : syracuseStep 1270743 = 1906115) B1906115
theorem B1270763 : Blo 1270453 1270763 := bstep (se 1 (by rfl) ⟨953072, by rfl⟩ : syracuseStep 1270763 = 1906145) B1906145
theorem B2860019 : Blo 1270453 2860019 := bstep (se 1 (by rfl) ⟨2145014, by rfl⟩ : syracuseStep 2860019 = 4290029) B4290029
theorem B1270775 : Blo 1270453 1270775 := bstep (se 1 (by rfl) ⟨953081, by rfl⟩ : syracuseStep 1270775 = 1906163) B1906163
theorem B1270795 : Blo 1270453 1270795 := bstep (se 1 (by rfl) ⟨953096, by rfl⟩ : syracuseStep 1270795 = 1906193) B1906193
theorem B1270807 : Blo 1270453 1270807 := bstep (se 1 (by rfl) ⟨953105, by rfl⟩ : syracuseStep 1270807 = 1906211) B1906211
theorem B2860055 : Blo 1270453 2860055 := bstep (se 1 (by rfl) ⟨2145041, by rfl⟩ : syracuseStep 2860055 = 4290083) B4290083
theorem B1270827 : Blo 1270453 1270827 := bstep (se 1 (by rfl) ⟨953120, by rfl⟩ : syracuseStep 1270827 = 1906241) B1906241
theorem B7242797 : Blo 1270453 7242797 := bstep (se 3 (by rfl) ⟨1358024, by rfl⟩ : syracuseStep 7242797 = 2716049) B2716049
theorem B1270839 : Blo 1270453 1270839 := bstep (se 1 (by rfl) ⟨953129, by rfl⟩ : syracuseStep 1270839 = 1906259) B1906259
theorem B1270859 : Blo 1270453 1270859 := bstep (se 1 (by rfl) ⟨953144, by rfl⟩ : syracuseStep 1270859 = 1906289) B1906289
theorem B1270871 : Blo 1270453 1270871 := bstep (se 1 (by rfl) ⟨953153, by rfl⟩ : syracuseStep 1270871 = 1906307) B1906307
theorem B1270891 : Blo 1270453 1270891 := bstep (se 1 (by rfl) ⟨953168, by rfl⟩ : syracuseStep 1270891 = 1906337) B1906337
theorem B1270903 : Blo 1270453 1270903 := bstep (se 1 (by rfl) ⟨953177, by rfl⟩ : syracuseStep 1270903 = 1906355) B1906355
theorem B1270923 : Blo 1270453 1270923 := bstep (se 1 (by rfl) ⟨953192, by rfl⟩ : syracuseStep 1270923 = 1906385) B1906385
theorem B1270935 : Blo 1270453 1270935 := bstep (se 1 (by rfl) ⟨953201, by rfl⟩ : syracuseStep 1270935 = 1906403) B1906403
theorem B8144023 : Blo 1270453 8144023 := bstep (se 1 (by rfl) ⟨6108017, by rfl⟩ : syracuseStep 8144023 = 12216035) B12216035
theorem B1270955 : Blo 1270453 1270955 := bstep (se 1 (by rfl) ⟨953216, by rfl⟩ : syracuseStep 1270955 = 1906433) B1906433
theorem B1270967 : Blo 1270453 1270967 := bstep (se 1 (by rfl) ⟨953225, by rfl⟩ : syracuseStep 1270967 = 1906451) B1906451
theorem B1270987 : Blo 1270453 1270987 := bstep (se 1 (by rfl) ⟨953240, by rfl⟩ : syracuseStep 1270987 = 1906481) B1906481
theorem B2860235 : Blo 1270453 2860235 := bstep (se 1 (by rfl) ⟨2145176, by rfl⟩ : syracuseStep 2860235 = 4290353) B4290353
theorem B2204875 : Blo 1270453 2204875 := bstep (se 1 (by rfl) ⟨1653656, by rfl⟩ : syracuseStep 2204875 = 3307313) B3307313
theorem B1270999 : Blo 1270453 1270999 := bstep (se 1 (by rfl) ⟨953249, by rfl⟩ : syracuseStep 1270999 = 1906499) B1906499
theorem B3867869 : Blo 1270453 3867869 := bstep (se 3 (by rfl) ⟨725225, by rfl⟩ : syracuseStep 3867869 = 1450451) B1450451
theorem B1271019 : Blo 1270453 1271019 := bstep (se 1 (by rfl) ⟨953264, by rfl⟩ : syracuseStep 1271019 = 1906529) B1906529
theorem B1271031 : Blo 1270453 1271031 := bstep (se 1 (by rfl) ⟨953273, by rfl⟩ : syracuseStep 1271031 = 1906547) B1906547
theorem B2860289 : Blo 1270453 2860289 := bstep (se 2 (by rfl) ⟨1072608, by rfl⟩ : syracuseStep 2860289 = 2145217) B2145217
theorem B1271051 : Blo 1270453 1271051 := bstep (se 1 (by rfl) ⟨953288, by rfl⟩ : syracuseStep 1271051 = 1906577) B1906577
theorem B9651473 : Blo 1270453 9651473 := bstep (se 2 (by rfl) ⟨3619302, by rfl⟩ : syracuseStep 9651473 = 7238605) B7238605
theorem B1271063 : Blo 1270453 1271063 := bstep (se 1 (by rfl) ⟨953297, by rfl⟩ : syracuseStep 1271063 = 1906595) B1906595
theorem B1271083 : Blo 1270453 1271083 := bstep (se 1 (by rfl) ⟨953312, by rfl⟩ : syracuseStep 1271083 = 1906625) B1906625
theorem B1271095 : Blo 1270453 1271095 := bstep (se 1 (by rfl) ⟨953321, by rfl⟩ : syracuseStep 1271095 = 1906643) B1906643
theorem B1271115 : Blo 1270453 1271115 := bstep (se 1 (by rfl) ⟨953336, by rfl⟩ : syracuseStep 1271115 = 1906673) B1906673
theorem B1271127 : Blo 1270453 1271127 := bstep (se 1 (by rfl) ⟨953345, by rfl⟩ : syracuseStep 1271127 = 1906691) B1906691
theorem B1271147 : Blo 1270453 1271147 := bstep (se 1 (by rfl) ⟨953360, by rfl⟩ : syracuseStep 1271147 = 1906721) B1906721
theorem B1271159 : Blo 1270453 1271159 := bstep (se 1 (by rfl) ⟨953369, by rfl⟩ : syracuseStep 1271159 = 1906739) B1906739
theorem B1271179 : Blo 1270453 1271179 := bstep (se 1 (by rfl) ⟨953384, by rfl⟩ : syracuseStep 1271179 = 1906769) B1906769
theorem B1271191 : Blo 1270453 1271191 := bstep (se 1 (by rfl) ⟨953393, by rfl⟩ : syracuseStep 1271191 = 1906787) B1906787
theorem B1271211 : Blo 1270453 1271211 := bstep (se 1 (by rfl) ⟨953408, by rfl⟩ : syracuseStep 1271211 = 1906817) B1906817
theorem B1271223 : Blo 1270453 1271223 := bstep (se 1 (by rfl) ⟨953417, by rfl⟩ : syracuseStep 1271223 = 1906835) B1906835
theorem B1271243 : Blo 1270453 1271243 := bstep (se 1 (by rfl) ⟨953432, by rfl⟩ : syracuseStep 1271243 = 1906865) B1906865
theorem B1271255 : Blo 1270453 1271255 := bstep (se 1 (by rfl) ⟨953441, by rfl⟩ : syracuseStep 1271255 = 1906883) B1906883
theorem B2860505 : Blo 1270453 2860505 := bstep (se 2 (by rfl) ⟨1072689, by rfl⟩ : syracuseStep 2860505 = 2145379) B2145379
theorem B1271275 : Blo 1270453 1271275 := bstep (se 1 (by rfl) ⟨953456, by rfl⟩ : syracuseStep 1271275 = 1906913) B1906913
theorem B1271287 : Blo 1270453 1271287 := bstep (se 1 (by rfl) ⟨953465, by rfl⟩ : syracuseStep 1271287 = 1906931) B1906931
theorem B1271307 : Blo 1270453 1271307 := bstep (se 1 (by rfl) ⟨953480, by rfl⟩ : syracuseStep 1271307 = 1906961) B1906961
theorem B1271319 : Blo 1270453 1271319 := bstep (se 1 (by rfl) ⟨953489, by rfl⟩ : syracuseStep 1271319 = 1906979) B1906979
theorem B1271339 : Blo 1270453 1271339 := bstep (se 1 (by rfl) ⟨953504, by rfl⟩ : syracuseStep 1271339 = 1907009) B1907009
theorem B2860595 : Blo 1270453 2860595 := bstep (se 1 (by rfl) ⟨2145446, by rfl⟩ : syracuseStep 2860595 = 4290893) B4290893
theorem B1271351 : Blo 1270453 1271351 := bstep (se 1 (by rfl) ⟨953513, by rfl⟩ : syracuseStep 1271351 = 1907027) B1907027
theorem B1271371 : Blo 1270453 1271371 := bstep (se 1 (by rfl) ⟨953528, by rfl⟩ : syracuseStep 1271371 = 1907057) B1907057
theorem B188565077 : Blo 1270453 188565077 := bstep (se 8 (by rfl) ⟨1104873, by rfl⟩ : syracuseStep 188565077 = 2209747) B2209747
theorem B1271383 : Blo 1270453 1271383 := bstep (se 1 (by rfl) ⟨953537, by rfl⟩ : syracuseStep 1271383 = 1907075) B1907075
theorem B2860631 : Blo 1270453 2860631 := bstep (se 1 (by rfl) ⟨2145473, by rfl⟩ : syracuseStep 2860631 = 4290947) B4290947
theorem B1271403 : Blo 1270453 1271403 := bstep (se 1 (by rfl) ⟨953552, by rfl⟩ : syracuseStep 1271403 = 1907105) B1907105
theorem B1271415 : Blo 1270453 1271415 := bstep (se 1 (by rfl) ⟨953561, by rfl⟩ : syracuseStep 1271415 = 1907123) B1907123
theorem B1271435 : Blo 1270453 1271435 := bstep (se 1 (by rfl) ⟨953576, by rfl⟩ : syracuseStep 1271435 = 1907153) B1907153
theorem B1271447 : Blo 1270453 1271447 := bstep (se 1 (by rfl) ⟨953585, by rfl⟩ : syracuseStep 1271447 = 1907171) B1907171
theorem B1271467 : Blo 1270453 1271467 := bstep (se 1 (by rfl) ⟨953600, by rfl⟩ : syracuseStep 1271467 = 1907201) B1907201
theorem B1271479 : Blo 1270453 1271479 := bstep (se 1 (by rfl) ⟨953609, by rfl⟩ : syracuseStep 1271479 = 1907219) B1907219
theorem B1271499 : Blo 1270453 1271499 := bstep (se 1 (by rfl) ⟨953624, by rfl⟩ : syracuseStep 1271499 = 1907249) B1907249
theorem B1271511 : Blo 1270453 1271511 := bstep (se 1 (by rfl) ⟨953633, by rfl⟩ : syracuseStep 1271511 = 1907267) B1907267
theorem B1271531 : Blo 1270453 1271531 := bstep (se 1 (by rfl) ⟨953648, by rfl⟩ : syracuseStep 1271531 = 1907297) B1907297
theorem B1271543 : Blo 1270453 1271543 := bstep (se 1 (by rfl) ⟨953657, by rfl⟩ : syracuseStep 1271543 = 1907315) B1907315
theorem B5154563 : Blo 1270453 5154563 := bstep (se 1 (by rfl) ⟨3865922, by rfl⟩ : syracuseStep 5154563 = 7731845) B7731845
theorem B2860811 : Blo 1270453 2860811 := bstep (se 1 (by rfl) ⟨2145608, by rfl⟩ : syracuseStep 2860811 = 4291217) B4291217
theorem B1271563 : Blo 1270453 1271563 := bstep (se 1 (by rfl) ⟨953672, by rfl⟩ : syracuseStep 1271563 = 1907345) B1907345
theorem B4581143 : Blo 1270453 4581143 := bstep (se 1 (by rfl) ⟨3435857, by rfl⟩ : syracuseStep 4581143 = 6871715) B6871715
theorem B1271575 : Blo 1270453 1271575 := bstep (se 1 (by rfl) ⟨953681, by rfl⟩ : syracuseStep 1271575 = 1907363) B1907363
theorem B1271595 : Blo 1270453 1271595 := bstep (se 1 (by rfl) ⟨953696, by rfl⟩ : syracuseStep 1271595 = 1907393) B1907393
theorem B1271607 : Blo 1270453 1271607 := bstep (se 1 (by rfl) ⟨953705, by rfl⟩ : syracuseStep 1271607 = 1907411) B1907411
theorem B2860865 : Blo 1270453 2860865 := bstep (se 2 (by rfl) ⟨1072824, by rfl⟩ : syracuseStep 2860865 = 2145649) B2145649
theorem B1271627 : Blo 1270453 1271627 := bstep (se 1 (by rfl) ⟨953720, by rfl⟩ : syracuseStep 1271627 = 1907441) B1907441
theorem B1271639 : Blo 1270453 1271639 := bstep (se 1 (by rfl) ⟨953729, by rfl⟩ : syracuseStep 1271639 = 1907459) B1907459
theorem B1271659 : Blo 1270453 1271659 := bstep (se 1 (by rfl) ⟨953744, by rfl⟩ : syracuseStep 1271659 = 1907489) B1907489
theorem B1271671 : Blo 1270453 1271671 := bstep (se 1 (by rfl) ⟨953753, by rfl⟩ : syracuseStep 1271671 = 1907507) B1907507
theorem B1271691 : Blo 1270453 1271691 := bstep (se 1 (by rfl) ⟨953768, by rfl⟩ : syracuseStep 1271691 = 1907537) B1907537
theorem B1271703 : Blo 1270453 1271703 := bstep (se 1 (by rfl) ⟨953777, by rfl⟩ : syracuseStep 1271703 = 1907555) B1907555
theorem B1271723 : Blo 1270453 1271723 := bstep (se 1 (by rfl) ⟨953792, by rfl⟩ : syracuseStep 1271723 = 1907585) B1907585
theorem B4827059 : Blo 1270453 4827059 := bstep (se 1 (by rfl) ⟨3620294, by rfl⟩ : syracuseStep 4827059 = 7240589) B7240589
theorem B1271735 : Blo 1270453 1271735 := bstep (se 1 (by rfl) ⟨953801, by rfl⟩ : syracuseStep 1271735 = 1907603) B1907603
theorem B4827073 : Blo 1270453 4827073 := bstep (se 2 (by rfl) ⟨1810152, by rfl⟩ : syracuseStep 4827073 = 3620305) B3620305
theorem B1271755 : Blo 1270453 1271755 := bstep (se 1 (by rfl) ⟨953816, by rfl⟩ : syracuseStep 1271755 = 1907633) B1907633
theorem B1271767 : Blo 1270453 1271767 := bstep (se 1 (by rfl) ⟨953825, by rfl⟩ : syracuseStep 1271767 = 1907651) B1907651
theorem B1271787 : Blo 1270453 1271787 := bstep (se 1 (by rfl) ⟨953840, by rfl⟩ : syracuseStep 1271787 = 1907681) B1907681
theorem B1271799 : Blo 1270453 1271799 := bstep (se 1 (by rfl) ⟨953849, by rfl⟩ : syracuseStep 1271799 = 1907699) B1907699
theorem B1271819 : Blo 1270453 1271819 := bstep (se 1 (by rfl) ⟨953864, by rfl⟩ : syracuseStep 1271819 = 1907729) B1907729
theorem B1271831 : Blo 1270453 1271831 := bstep (se 1 (by rfl) ⟨953873, by rfl⟩ : syracuseStep 1271831 = 1907747) B1907747
theorem B2861081 : Blo 1270453 2861081 := bstep (se 2 (by rfl) ⟨1072905, by rfl⟩ : syracuseStep 2861081 = 2145811) B2145811
theorem B1271851 : Blo 1270453 1271851 := bstep (se 1 (by rfl) ⟨953888, by rfl⟩ : syracuseStep 1271851 = 1907777) B1907777
theorem B1271863 : Blo 1270453 1271863 := bstep (se 1 (by rfl) ⟨953897, by rfl⟩ : syracuseStep 1271863 = 1907795) B1907795
theorem B2713675 : Blo 1270453 2713675 := bstep (se 1 (by rfl) ⟨2035256, by rfl⟩ : syracuseStep 2713675 = 4070513) B4070513
theorem B1271883 : Blo 1270453 1271883 := bstep (se 1 (by rfl) ⟨953912, by rfl⟩ : syracuseStep 1271883 = 1907825) B1907825
theorem B1271895 : Blo 1270453 1271895 := bstep (se 1 (by rfl) ⟨953921, by rfl⟩ : syracuseStep 1271895 = 1907843) B1907843
theorem B1271915 : Blo 1270453 1271915 := bstep (se 1 (by rfl) ⟨953936, by rfl⟩ : syracuseStep 1271915 = 1907873) B1907873
theorem B2861171 : Blo 1270453 2861171 := bstep (se 1 (by rfl) ⟨2145878, by rfl⟩ : syracuseStep 2861171 = 4291757) B4291757
theorem B1394807 : Blo 1270453 1394807 := bstep (se 1 (by rfl) ⟨1046105, by rfl⟩ : syracuseStep 1394807 = 2092211) B2092211
theorem B1271927 : Blo 1270453 1271927 := bstep (se 1 (by rfl) ⟨953945, by rfl⟩ : syracuseStep 1271927 = 1907891) B1907891
theorem B1271947 : Blo 1270453 1271947 := bstep (se 1 (by rfl) ⟨953960, by rfl⟩ : syracuseStep 1271947 = 1907921) B1907921
theorem B2861207 : Blo 1270453 2861207 := bstep (se 1 (by rfl) ⟨2145905, by rfl⟩ : syracuseStep 2861207 = 4291811) B4291811
theorem B2861387 : Blo 1270453 2861387 := bstep (se 1 (by rfl) ⟨2146040, by rfl⟩ : syracuseStep 2861387 = 4292081) B4292081
theorem B2861441 : Blo 1270453 2861441 := bstep (se 2 (by rfl) ⟨1073040, by rfl⟩ : syracuseStep 2861441 = 2146081) B2146081
theorem B4073921 : Blo 1270453 4073921 := bstep (se 2 (by rfl) ⟨1527720, by rfl⟩ : syracuseStep 4073921 = 3055441) B3055441
theorem B1288747 : Blo 1270453 1288747 := bstep (se 1 (by rfl) ⟨966560, by rfl⟩ : syracuseStep 1288747 = 1933121) B1933121
theorem B2861657 : Blo 1270453 2861657 := bstep (se 2 (by rfl) ⟨1073121, by rfl⟩ : syracuseStep 2861657 = 2146243) B2146243
theorem B1608331 : Blo 1270453 1608331 := bstep (se 1 (by rfl) ⟨1206248, by rfl⟩ : syracuseStep 1608331 = 2412497) B2412497
theorem B2861747 : Blo 1270453 2861747 := bstep (se 1 (by rfl) ⟨2146310, by rfl⟩ : syracuseStep 2861747 = 4292621) B4292621
theorem B2861783 : Blo 1270453 2861783 := bstep (se 1 (by rfl) ⟨2146337, by rfl⟩ : syracuseStep 2861783 = 4292675) B4292675
theorem B6433667 : Blo 1270453 6433667 := bstep (se 1 (by rfl) ⟨4825250, by rfl⟩ : syracuseStep 6433667 = 9650501) B9650501
theorem B2321291 : Blo 1270453 2321291 := bstep (se 1 (by rfl) ⟨1740968, by rfl⟩ : syracuseStep 2321291 = 3481937) B3481937
theorem B1608599 : Blo 1270453 1608599 := bstep (se 1 (by rfl) ⟨1206449, by rfl⟩ : syracuseStep 1608599 = 2412899) B2412899
theorem B6876083 : Blo 1270453 6876083 := bstep (se 1 (by rfl) ⟨5157062, by rfl⟩ : syracuseStep 6876083 = 10314125) B10314125
theorem B9784451 : Blo 1270453 9784451 := bstep (se 1 (by rfl) ⟨7338338, by rfl⟩ : syracuseStep 9784451 = 14676677) B14676677
theorem B6524225 : Blo 1270453 6524225 := bstep (se 2 (by rfl) ⟨2446584, by rfl⟩ : syracuseStep 6524225 = 4893169) B4893169
theorem B7236965 : Blo 1270453 7236965 := bstep (se 4 (by rfl) ⟨678465, by rfl⟩ : syracuseStep 7236965 = 1356931) B1356931
theorem B6106499 : Blo 1270453 6106499 := bstep (se 1 (by rfl) ⟨4579874, by rfl⟩ : syracuseStep 6106499 = 9159749) B9159749
theorem B2411927 : Blo 1270453 2411927 := bstep (se 1 (by rfl) ⟨1808945, by rfl⟩ : syracuseStep 2411927 = 3617891) B3617891
theorem B4287923 : Blo 1270453 4287923 := bstep (se 1 (by rfl) ⟨3215942, by rfl⟩ : syracuseStep 4287923 = 6431885) B6431885
theorem B2715059 : Blo 1270453 2715059 := bstep (se 1 (by rfl) ⟨2036294, by rfl⟩ : syracuseStep 2715059 = 4072589) B4072589
theorem B9055819 : Blo 1270453 9055819 := bstep (se 1 (by rfl) ⟨6791864, by rfl⟩ : syracuseStep 9055819 = 13583729) B13583729
theorem B8146507 : Blo 1270453 8146507 := bstep (se 1 (by rfl) ⟨6109880, by rfl⟩ : syracuseStep 8146507 = 12219761) B12219761
theorem B1609303 : Blo 1270453 1609303 := bstep (se 1 (by rfl) ⟨1206977, by rfl⟩ : syracuseStep 1609303 = 2413955) B2413955
theorem B2035289 : Blo 1270453 2035289 := bstep (se 2 (by rfl) ⟨763233, by rfl⟩ : syracuseStep 2035289 = 1526467) B1526467
theorem B21712535 : Blo 1270453 21712535 := bstep (se 1 (by rfl) ⟨16284401, by rfl⟩ : syracuseStep 21712535 = 32568803) B32568803
theorem B4288193 : Blo 1270453 4288193 := bstep (se 2 (by rfl) ⟨1608072, by rfl⟩ : syracuseStep 4288193 = 3216145) B3216145
theorem B7237421 : Blo 1270453 7237421 := bstep (se 3 (by rfl) ⟨1357016, by rfl⟩ : syracuseStep 7237421 = 2714033) B2714033
theorem B1429303 : Blo 1270453 1429303 := bstep (se 1 (by rfl) ⟨1071977, by rfl⟩ : syracuseStep 1429303 = 2143955) B2143955
theorem B4829003 : Blo 1270453 4829003 := bstep (se 1 (by rfl) ⟨3621752, by rfl⟩ : syracuseStep 4829003 = 7243505) B7243505
theorem B4829017 : Blo 1270453 4829017 := bstep (se 2 (by rfl) ⟨1810881, by rfl⟩ : syracuseStep 4829017 = 3621763) B3621763
theorem B26079155 : Blo 1270453 26079155 := bstep (se 1 (by rfl) ⟨19559366, by rfl⟩ : syracuseStep 26079155 = 39118733) B39118733
theorem B1429483 : Blo 1270453 1429483 := bstep (se 1 (by rfl) ⟨1072112, by rfl⟩ : syracuseStep 1429483 = 2144225) B2144225
theorem B2412595 : Blo 1270453 2412595 := bstep (se 1 (by rfl) ⟨1809446, by rfl⟩ : syracuseStep 2412595 = 3618893) B3618893
theorem B1429591 : Blo 1270453 1429591 := bstep (se 1 (by rfl) ⟨1072193, by rfl⟩ : syracuseStep 1429591 = 2144387) B2144387
theorem B2035801 : Blo 1270453 2035801 := bstep (se 2 (by rfl) ⟨763425, by rfl⟩ : syracuseStep 2035801 = 1526851) B1526851
theorem B4288733 : Blo 1270453 4288733 := bstep (se 3 (by rfl) ⟨804137, by rfl⟩ : syracuseStep 4288733 = 1608275) B1608275
theorem B2715905 : Blo 1270453 2715905 := bstep (se 2 (by rfl) ⟨1018464, by rfl⟩ : syracuseStep 2715905 = 2036929) B2036929
theorem B1429771 : Blo 1270453 1429771 := bstep (se 1 (by rfl) ⟨1072328, by rfl⟩ : syracuseStep 1429771 = 2144657) B2144657
theorem B2412823 : Blo 1270453 2412823 := bstep (se 1 (by rfl) ⟨1809617, by rfl⟩ : syracuseStep 2412823 = 3619235) B3619235
theorem B1429879 : Blo 1270453 1429879 := bstep (se 1 (by rfl) ⟨1072409, by rfl⟩ : syracuseStep 1429879 = 2144819) B2144819
theorem B2412929 : Blo 1270453 2412929 := bstep (se 2 (by rfl) ⟨904848, by rfl⟩ : syracuseStep 2412929 = 1809697) B1809697
theorem B5427587 : Blo 1270453 5427587 := bstep (se 1 (by rfl) ⟨4070690, by rfl⟩ : syracuseStep 5427587 = 8141381) B8141381
theorem B7238105 : Blo 1270453 7238105 := bstep (se 2 (by rfl) ⟨2714289, by rfl⟩ : syracuseStep 7238105 = 5428579) B5428579
theorem B2413081 : Blo 1270453 2413081 := bstep (se 2 (by rfl) ⟨904905, by rfl⟩ : syracuseStep 2413081 = 1809811) B1809811
theorem B1430059 : Blo 1270453 1430059 := bstep (se 1 (by rfl) ⟨1072544, by rfl⟩ : syracuseStep 1430059 = 2145089) B2145089
theorem B2716247 : Blo 1270453 2716247 := bstep (se 1 (by rfl) ⟨2037185, by rfl⟩ : syracuseStep 2716247 = 4074371) B4074371
theorem B14504579 : Blo 1270453 14504579 := bstep (se 1 (by rfl) ⟨10878434, by rfl⟩ : syracuseStep 14504579 = 21756869) B21756869
theorem B1430167 : Blo 1270453 1430167 := bstep (se 1 (by rfl) ⟨1072625, by rfl⟩ : syracuseStep 1430167 = 2145251) B2145251
theorem B1430347 : Blo 1270453 1430347 := bstep (se 1 (by rfl) ⟨1072760, by rfl⟩ : syracuseStep 1430347 = 2145521) B2145521
theorem B3216307 : Blo 1270453 3216307 := bstep (se 1 (by rfl) ⟨2412230, by rfl⟩ : syracuseStep 3216307 = 4824461) B4824461
theorem B1430455 : Blo 1270453 1430455 := bstep (se 1 (by rfl) ⟨1072841, by rfl⟩ : syracuseStep 1430455 = 2145683) B2145683
theorem B1905689 : Blo 1270453 1905689 := bstep (se 2 (by rfl) ⟨714633, by rfl⟩ : syracuseStep 1905689 = 1429267) B1429267
theorem B3216449 : Blo 1270453 3216449 := bstep (se 2 (by rfl) ⟨1206168, by rfl⟩ : syracuseStep 3216449 = 2412337) B2412337
theorem B9655361 : Blo 1270453 9655361 := bstep (se 2 (by rfl) ⟨3620760, by rfl⟩ : syracuseStep 9655361 = 7241521) B7241521
theorem B1430635 : Blo 1270453 1430635 := bstep (se 1 (by rfl) ⟨1072976, by rfl⟩ : syracuseStep 1430635 = 2145953) B2145953
theorem B1905803 : Blo 1270453 1905803 := bstep (se 1 (by rfl) ⟨1429352, by rfl⟩ : syracuseStep 1905803 = 2858705) B2858705
theorem B1905815 : Blo 1270453 1905815 := bstep (se 1 (by rfl) ⟨1429361, by rfl⟩ : syracuseStep 1905815 = 2858723) B2858723
theorem B1430743 : Blo 1270453 1430743 := bstep (se 1 (by rfl) ⟨1073057, by rfl⟩ : syracuseStep 1430743 = 2146115) B2146115
theorem B1905881 : Blo 1270453 1905881 := bstep (se 2 (by rfl) ⟨714705, by rfl⟩ : syracuseStep 1905881 = 1429411) B1429411
theorem B1357111 : Blo 1270453 1357111 := bstep (se 1 (by rfl) ⟨1017833, by rfl⟩ : syracuseStep 1357111 = 2035667) B2035667
theorem B3052865 : Blo 1270453 3052865 := bstep (se 2 (by rfl) ⟨1144824, by rfl⟩ : syracuseStep 3052865 = 2289649) B2289649
theorem B1905995 : Blo 1270453 1905995 := bstep (se 1 (by rfl) ⟨1429496, by rfl⟩ : syracuseStep 1905995 = 2858993) B2858993
theorem B4289867 : Blo 1270453 4289867 := bstep (se 1 (by rfl) ⟨3217400, by rfl⟩ : syracuseStep 4289867 = 6434801) B6434801
theorem B1906007 : Blo 1270453 1906007 := bstep (se 1 (by rfl) ⟨1429505, by rfl⟩ : syracuseStep 1906007 = 2859011) B2859011
theorem B1430923 : Blo 1270453 1430923 := bstep (se 1 (by rfl) ⟨1073192, by rfl⟩ : syracuseStep 1430923 = 2146385) B2146385
theorem B1906073 : Blo 1270453 1906073 := bstep (se 2 (by rfl) ⟨714777, by rfl⟩ : syracuseStep 1906073 = 1429555) B1429555
theorem B2446807 : Blo 1270453 2446807 := bstep (se 1 (by rfl) ⟨1835105, by rfl⟩ : syracuseStep 2446807 = 3670211) B3670211
theorem B1906187 : Blo 1270453 1906187 := bstep (se 1 (by rfl) ⟨1429640, by rfl⟩ : syracuseStep 1906187 = 2859281) B2859281
theorem B1906199 : Blo 1270453 1906199 := bstep (se 1 (by rfl) ⟨1429649, by rfl⟩ : syracuseStep 1906199 = 2859299) B2859299
theorem B1906265 : Blo 1270453 1906265 := bstep (se 2 (by rfl) ⟨714849, by rfl⟩ : syracuseStep 1906265 = 1429699) B1429699
theorem B4290137 : Blo 1270453 4290137 := bstep (se 2 (by rfl) ⟨1608801, by rfl⟩ : syracuseStep 4290137 = 3217603) B3217603
theorem B12211843 : Blo 1270453 12211843 := bstep (se 1 (by rfl) ⟨9158882, by rfl⟩ : syracuseStep 12211843 = 18317765) B18317765
theorem B1906379 : Blo 1270453 1906379 := bstep (se 1 (by rfl) ⟨1429784, by rfl⟩ : syracuseStep 1906379 = 2859569) B2859569
theorem B1906391 : Blo 1270453 1906391 := bstep (se 1 (by rfl) ⟨1429793, by rfl⟩ : syracuseStep 1906391 = 2859587) B2859587
theorem B1906457 : Blo 1270453 1906457 := bstep (se 2 (by rfl) ⟨714921, by rfl⟩ : syracuseStep 1906457 = 1429843) B1429843
theorem B2414387 : Blo 1270453 2414387 := bstep (se 1 (by rfl) ⟨1810790, by rfl⟩ : syracuseStep 2414387 = 3621581) B3621581
theorem B1906571 : Blo 1270453 1906571 := bstep (se 1 (by rfl) ⟨1429928, by rfl⟩ : syracuseStep 1906571 = 2859857) B2859857
theorem B1906583 : Blo 1270453 1906583 := bstep (se 1 (by rfl) ⟨1429937, by rfl⟩ : syracuseStep 1906583 = 2859875) B2859875
theorem B1718167 : Blo 1270453 1718167 := bstep (se 1 (by rfl) ⟨1288625, by rfl⟩ : syracuseStep 1718167 = 2577251) B2577251
theorem B2291609 : Blo 1270453 2291609 := bstep (se 2 (by rfl) ⟨859353, by rfl⟩ : syracuseStep 2291609 = 1718707) B1718707
theorem B2414539 : Blo 1270453 2414539 := bstep (se 1 (by rfl) ⟨1810904, by rfl⟩ : syracuseStep 2414539 = 3621809) B3621809
theorem B1906649 : Blo 1270453 1906649 := bstep (se 2 (by rfl) ⟨714993, by rfl⟩ : syracuseStep 1906649 = 1429987) B1429987
theorem B5429213 : Blo 1270453 5429213 := bstep (se 3 (by rfl) ⟨1017977, by rfl⟩ : syracuseStep 5429213 = 2035955) B2035955
theorem B2144279 : Blo 1270453 2144279 := bstep (se 1 (by rfl) ⟨1608209, by rfl⟩ : syracuseStep 2144279 = 3216419) B3216419
theorem B3053633 : Blo 1270453 3053633 := bstep (se 2 (by rfl) ⟨1145112, by rfl⟩ : syracuseStep 3053633 = 2290225) B2290225
theorem B1906763 : Blo 1270453 1906763 := bstep (se 1 (by rfl) ⟨1430072, by rfl⟩ : syracuseStep 1906763 = 2860145) B2860145
theorem B1906775 : Blo 1270453 1906775 := bstep (se 1 (by rfl) ⟨1430081, by rfl⟩ : syracuseStep 1906775 = 2860163) B2860163
theorem B1357931 : Blo 1270453 1357931 := bstep (se 1 (by rfl) ⟨1018448, by rfl⟩ : syracuseStep 1357931 = 2036897) B2036897
theorem B2144407 : Blo 1270453 2144407 := bstep (se 1 (by rfl) ⟨1608305, by rfl⟩ : syracuseStep 2144407 = 3216611) B3216611
theorem B1906841 : Blo 1270453 1906841 := bstep (se 2 (by rfl) ⟨715065, by rfl⟩ : syracuseStep 1906841 = 1430131) B1430131
theorem B3619019 : Blo 1270453 3619019 := bstep (se 1 (by rfl) ⟨2714264, by rfl⟩ : syracuseStep 3619019 = 5428529) B5428529
theorem B1906955 : Blo 1270453 1906955 := bstep (se 1 (by rfl) ⟨1430216, by rfl⟩ : syracuseStep 1906955 = 2860433) B2860433
theorem B1906967 : Blo 1270453 1906967 := bstep (se 1 (by rfl) ⟨1430225, by rfl⟩ : syracuseStep 1906967 = 2860451) B2860451
theorem B4290839 : Blo 1270453 4290839 := bstep (se 1 (by rfl) ⟨3218129, by rfl⟩ : syracuseStep 4290839 = 6436259) B6436259
theorem B3217715 : Blo 1270453 3217715 := bstep (se 1 (by rfl) ⟨2413286, by rfl⟩ : syracuseStep 3217715 = 4826573) B4826573
theorem B1907033 : Blo 1270453 1907033 := bstep (se 2 (by rfl) ⟨715137, by rfl⟩ : syracuseStep 1907033 = 1430275) B1430275
theorem B11164081 : Blo 1270453 11164081 := bstep (se 2 (by rfl) ⟨4186530, by rfl⟩ : syracuseStep 11164081 = 8373061) B8373061
theorem B1907147 : Blo 1270453 1907147 := bstep (se 1 (by rfl) ⟨1430360, by rfl⟩ : syracuseStep 1907147 = 2860721) B2860721
theorem B1907159 : Blo 1270453 1907159 := bstep (se 1 (by rfl) ⟨1430369, by rfl⟩ : syracuseStep 1907159 = 2860739) B2860739
theorem B6437393 : Blo 1270453 6437393 := bstep (se 2 (by rfl) ⟨2414022, by rfl⟩ : syracuseStep 6437393 = 4828045) B4828045
theorem B1907225 : Blo 1270453 1907225 := bstep (se 2 (by rfl) ⟨715209, by rfl⟩ : syracuseStep 1907225 = 1430419) B1430419
theorem B11008547 : Blo 1270453 11008547 := bstep (se 1 (by rfl) ⟨8256410, by rfl⟩ : syracuseStep 11008547 = 16512821) B16512821
theorem B3619417 : Blo 1270453 3619417 := bstep (se 2 (by rfl) ⟨1357281, by rfl⟩ : syracuseStep 3619417 = 2714563) B2714563
theorem B1907339 : Blo 1270453 1907339 := bstep (se 1 (by rfl) ⟨1430504, by rfl⟩ : syracuseStep 1907339 = 2861009) B2861009
theorem B5429911 : Blo 1270453 5429911 := bstep (se 1 (by rfl) ⟨4072433, by rfl⟩ : syracuseStep 5429911 = 8144867) B8144867
theorem B1907351 : Blo 1270453 1907351 := bstep (se 1 (by rfl) ⟨1430513, by rfl⟩ : syracuseStep 1907351 = 2861027) B2861027
theorem B6437555 : Blo 1270453 6437555 := bstep (se 1 (by rfl) ⟨4828166, by rfl⟩ : syracuseStep 6437555 = 9656333) B9656333
theorem B5151449 : Blo 1270453 5151449 := bstep (se 2 (by rfl) ⟨1931793, by rfl⟩ : syracuseStep 5151449 = 3863587) B3863587
theorem B1907417 : Blo 1270453 1907417 := bstep (se 2 (by rfl) ⟨715281, by rfl⟩ : syracuseStep 1907417 = 1430563) B1430563
theorem B2145035 : Blo 1270453 2145035 := bstep (se 1 (by rfl) ⟨1608776, by rfl⟩ : syracuseStep 2145035 = 3217553) B3217553
theorem B4291379 : Blo 1270453 4291379 := bstep (se 1 (by rfl) ⟨3218534, by rfl⟩ : syracuseStep 4291379 = 6437069) B6437069
theorem B3218251 : Blo 1270453 3218251 := bstep (se 1 (by rfl) ⟨2413688, by rfl⟩ : syracuseStep 3218251 = 4827377) B4827377
theorem B1907531 : Blo 1270453 1907531 := bstep (se 1 (by rfl) ⟨1430648, by rfl⟩ : syracuseStep 1907531 = 2861297) B2861297
theorem B1907543 : Blo 1270453 1907543 := bstep (se 1 (by rfl) ⟨1430657, by rfl⟩ : syracuseStep 1907543 = 2861315) B2861315
theorem B6519683 : Blo 1270453 6519683 := bstep (se 1 (by rfl) ⟨4889762, by rfl⟩ : syracuseStep 6519683 = 9779525) B9779525
theorem B2145163 : Blo 1270453 2145163 := bstep (se 1 (by rfl) ⟨1608872, by rfl⟩ : syracuseStep 2145163 = 3217745) B3217745
theorem B1907609 : Blo 1270453 1907609 := bstep (se 2 (by rfl) ⟨715353, by rfl⟩ : syracuseStep 1907609 = 1430707) B1430707
theorem B3218393 : Blo 1270453 3218393 := bstep (se 2 (by rfl) ⟨1206897, by rfl⟩ : syracuseStep 3218393 = 2413795) B2413795
theorem B9657305 : Blo 1270453 9657305 := bstep (se 2 (by rfl) ⟨3621489, by rfl⟩ : syracuseStep 9657305 = 7242979) B7242979
theorem B1907723 : Blo 1270453 1907723 := bstep (se 1 (by rfl) ⟨1430792, by rfl⟩ : syracuseStep 1907723 = 2861585) B2861585
theorem B23206925 : Blo 1270453 23206925 := bstep (se 3 (by rfl) ⟨4351298, by rfl⟩ : syracuseStep 23206925 = 8702597) B8702597
theorem B1375255 : Blo 1270453 1375255 := bstep (se 1 (by rfl) ⟨1031441, by rfl⟩ : syracuseStep 1375255 = 2062883) B2062883
theorem B2145305 : Blo 1270453 2145305 := bstep (se 2 (by rfl) ⟨804489, by rfl⟩ : syracuseStep 2145305 = 1608979) B1608979
theorem B1907735 : Blo 1270453 1907735 := bstep (se 1 (by rfl) ⟨1430801, by rfl⟩ : syracuseStep 1907735 = 2861603) B2861603
theorem B4291649 : Blo 1270453 4291649 := bstep (se 2 (by rfl) ⟨1609368, by rfl⟩ : syracuseStep 4291649 = 3218737) B3218737
theorem B1907801 : Blo 1270453 1907801 := bstep (se 2 (by rfl) ⟨715425, by rfl⟩ : syracuseStep 1907801 = 1430851) B1430851
theorem B4824157 : Blo 1270453 4824157 := bstep (se 3 (by rfl) ⟨904529, by rfl⟩ : syracuseStep 4824157 = 1809059) B1809059
theorem B2751617 : Blo 1270453 2751617 := bstep (se 2 (by rfl) ⟨1031856, by rfl⟩ : syracuseStep 2751617 = 2063713) B2063713
theorem B1932427 : Blo 1270453 1932427 := bstep (se 1 (by rfl) ⟨1449320, by rfl⟩ : syracuseStep 1932427 = 2898641) B2898641
theorem B2145433 : Blo 1270453 2145433 := bstep (se 2 (by rfl) ⟨804537, by rfl⟩ : syracuseStep 2145433 = 1609075) B1609075
theorem B1907915 : Blo 1270453 1907915 := bstep (se 1 (by rfl) ⟨1430936, by rfl⟩ : syracuseStep 1907915 = 2861873) B2861873
theorem B1907927 : Blo 1270453 1907927 := bstep (se 1 (by rfl) ⟨1430945, by rfl⟩ : syracuseStep 1907927 = 2861891) B2861891
theorem B11754827 : Blo 1270453 11754827 := bstep (se 1 (by rfl) ⟨8816120, by rfl⟩ : syracuseStep 11754827 = 17632241) B17632241
theorem B338967949 : Blo 1270453 338967949 := bstep (se 3 (by rfl) ⟨63556490, by rfl⟩ : syracuseStep 338967949 = 127112981) B127112981
theorem B3480983 : Blo 1270453 3480983 := bstep (se 1 (by rfl) ⟨2610737, by rfl⟩ : syracuseStep 3480983 = 5221475) B5221475
theorem B2858561 : Blo 1270453 2858561 := bstep (se 2 (by rfl) ⟨1071960, by rfl⟩ : syracuseStep 2858561 = 2143921) B2143921
theorem B5226059 : Blo 1270453 5226059 := bstep (se 1 (by rfl) ⟨3919544, by rfl⟩ : syracuseStep 5226059 = 7839089) B7839089
theorem B4292189 : Blo 1270453 4292189 := bstep (se 3 (by rfl) ⟨804785, by rfl⟩ : syracuseStep 4292189 = 1609571) B1609571
theorem B1810073 : Blo 1270453 1810073 := bstep (se 2 (by rfl) ⟨678777, by rfl⟩ : syracuseStep 1810073 = 1357555) B1357555
theorem B2146007 : Blo 1270453 2146007 := bstep (se 1 (by rfl) ⟨1609505, by rfl⟩ : syracuseStep 2146007 = 3219011) B3219011
theorem B24772337 : Blo 1270453 24772337 := bstep (se 2 (by rfl) ⟨9289626, by rfl⟩ : syracuseStep 24772337 = 18579253) B18579253
theorem B3219223 : Blo 1270453 3219223 := bstep (se 1 (by rfl) ⟨2414417, by rfl⟩ : syracuseStep 3219223 = 4828835) B4828835
theorem B2858777 : Blo 1270453 2858777 := bstep (se 2 (by rfl) ⟨1072041, by rfl⟩ : syracuseStep 2858777 = 2144083) B2144083
theorem B3620659 : Blo 1270453 3620659 := bstep (se 1 (by rfl) ⟨2715494, by rfl⟩ : syracuseStep 3620659 = 5430989) B5430989
theorem B2146135 : Blo 1270453 2146135 := bstep (se 1 (by rfl) ⟨1609601, by rfl⟩ : syracuseStep 2146135 = 3219203) B3219203
theorem B2858867 : Blo 1270453 2858867 := bstep (se 1 (by rfl) ⟨2144150, by rfl⟩ : syracuseStep 2858867 = 4288301) B4288301
theorem B2858903 : Blo 1270453 2858903 := bstep (se 1 (by rfl) ⟨2144177, by rfl⟩ : syracuseStep 2858903 = 4288355) B4288355
theorem B10854323 : Blo 1270453 10854323 := bstep (se 1 (by rfl) ⟨8140742, by rfl⟩ : syracuseStep 10854323 = 16281485) B16281485
theorem B3620875 : Blo 1270453 3620875 := bstep (se 1 (by rfl) ⟨2715656, by rfl⟩ : syracuseStep 3620875 = 5431313) B5431313
theorem B7241795 : Blo 1270453 7241795 := bstep (se 1 (by rfl) ⟨5431346, by rfl⟩ : syracuseStep 7241795 = 10862693) B10862693
theorem B2859155 : Blo 1270453 2859155 := bstep (se 1 (by rfl) ⟨2144366, by rfl⟩ : syracuseStep 2859155 = 4288733) B4288733
theorem B1810603 : Blo 1270453 1810603 := bstep (se 1 (by rfl) ⟨1357952, by rfl⟩ : syracuseStep 1810603 = 2715905) B2715905
theorem B8143021 : Blo 1270453 8143021 := bstep (se 3 (by rfl) ⟨1526816, by rfl⟩ : syracuseStep 8143021 = 3053633) B3053633
theorem B2859209 : Blo 1270453 2859209 := bstep (se 2 (by rfl) ⟨1072203, by rfl⟩ : syracuseStep 2859209 = 2144407) B2144407
theorem B3621149 : Blo 1270453 3621149 := bstep (se 3 (by rfl) ⟨678965, by rfl⟩ : syracuseStep 3621149 = 1357931) B1357931
theorem B4825403 : Blo 1270453 4825403 := bstep (se 1 (by rfl) ⟨3619052, by rfl⟩ : syracuseStep 4825403 = 7238105) B7238105
theorem B14483771 : Blo 1270453 14483771 := bstep (se 1 (by rfl) ⟨10862828, by rfl⟩ : syracuseStep 14483771 = 21725657) B21725657
theorem B3719485 : Blo 1270453 3719485 := bstep (se 3 (by rfl) ⟨697403, by rfl⟩ : syracuseStep 3719485 = 1394807) B1394807
theorem B1810831 : Blo 1270453 1810831 := bstep (se 1 (by rfl) ⟨1358123, by rfl⟩ : syracuseStep 1810831 = 2716247) B2716247
theorem B14885441 : Blo 1270453 14885441 := bstep (se 2 (by rfl) ⟨5582040, by rfl⟩ : syracuseStep 14885441 = 11164081) B11164081
theorem B10314317 : Blo 1270453 10314317 := bstep (se 3 (by rfl) ⟨1933934, by rfl⟩ : syracuseStep 10314317 = 3867869) B3867869
theorem B1270459 : Blo 1270453 1270459 := bstep (se 1 (by rfl) ⟨952844, by rfl⟩ : syracuseStep 1270459 = 1905689) B1905689
theorem B1270535 : Blo 1270453 1270535 := bstep (se 1 (by rfl) ⟨952901, by rfl⟩ : syracuseStep 1270535 = 1905803) B1905803
theorem B1270543 : Blo 1270453 1270543 := bstep (se 1 (by rfl) ⟨952907, by rfl⟩ : syracuseStep 1270543 = 1905815) B1905815
theorem B4825889 : Blo 1270453 4825889 := bstep (se 2 (by rfl) ⟨1809708, by rfl⟩ : syracuseStep 4825889 = 3619417) B3619417
theorem B1270587 : Blo 1270453 1270587 := bstep (se 1 (by rfl) ⟨952940, by rfl⟩ : syracuseStep 1270587 = 1905881) B1905881
theorem B1270663 : Blo 1270453 1270663 := bstep (se 1 (by rfl) ⟨952997, by rfl⟩ : syracuseStep 1270663 = 1905995) B1905995
theorem B2859911 : Blo 1270453 2859911 := bstep (se 1 (by rfl) ⟨2144933, by rfl⟩ : syracuseStep 2859911 = 4289867) B4289867
theorem B1270671 : Blo 1270453 1270671 := bstep (se 1 (by rfl) ⟨953003, by rfl⟩ : syracuseStep 1270671 = 1906007) B1906007
theorem B1270715 : Blo 1270453 1270715 := bstep (se 1 (by rfl) ⟨953036, by rfl⟩ : syracuseStep 1270715 = 1906073) B1906073
theorem B1270791 : Blo 1270453 1270791 := bstep (se 1 (by rfl) ⟨953093, by rfl⟩ : syracuseStep 1270791 = 1906187) B1906187
theorem B1270799 : Blo 1270453 1270799 := bstep (se 1 (by rfl) ⟨953099, by rfl⟩ : syracuseStep 1270799 = 1906199) B1906199
theorem B2860091 : Blo 1270453 2860091 := bstep (se 1 (by rfl) ⟨2145068, by rfl⟩ : syracuseStep 2860091 = 4290137) B4290137
theorem B1270843 : Blo 1270453 1270843 := bstep (se 1 (by rfl) ⟨953132, by rfl⟩ : syracuseStep 1270843 = 1906265) B1906265
theorem B1270919 : Blo 1270453 1270919 := bstep (se 1 (by rfl) ⟨953189, by rfl⟩ : syracuseStep 1270919 = 1906379) B1906379
theorem B1270927 : Blo 1270453 1270927 := bstep (se 1 (by rfl) ⟨953195, by rfl⟩ : syracuseStep 1270927 = 1906391) B1906391
theorem B2860217 : Blo 1270453 2860217 := bstep (se 2 (by rfl) ⟨1072581, by rfl⟩ : syracuseStep 2860217 = 2145163) B2145163
theorem B1270971 : Blo 1270453 1270971 := bstep (se 1 (by rfl) ⟨953228, by rfl⟩ : syracuseStep 1270971 = 1906457) B1906457
theorem B1271047 : Blo 1270453 1271047 := bstep (se 1 (by rfl) ⟨953285, by rfl⟩ : syracuseStep 1271047 = 1906571) B1906571
theorem B1271055 : Blo 1270453 1271055 := bstep (se 1 (by rfl) ⟨953291, by rfl⟩ : syracuseStep 1271055 = 1906583) B1906583
theorem B1271099 : Blo 1270453 1271099 := bstep (se 1 (by rfl) ⟨953324, by rfl⟩ : syracuseStep 1271099 = 1906649) B1906649
theorem B1271175 : Blo 1270453 1271175 := bstep (se 1 (by rfl) ⟨953381, by rfl⟩ : syracuseStep 1271175 = 1906763) B1906763
theorem B1271183 : Blo 1270453 1271183 := bstep (se 1 (by rfl) ⟨953387, by rfl⟩ : syracuseStep 1271183 = 1906775) B1906775
theorem B1271227 : Blo 1270453 1271227 := bstep (se 1 (by rfl) ⟨953420, by rfl⟩ : syracuseStep 1271227 = 1906841) B1906841
theorem B6432209 : Blo 1270453 6432209 := bstep (se 2 (by rfl) ⟨2412078, by rfl⟩ : syracuseStep 6432209 = 4824157) B4824157
theorem B1271303 : Blo 1270453 1271303 := bstep (se 1 (by rfl) ⟨953477, by rfl⟩ : syracuseStep 1271303 = 1906955) B1906955
theorem B1271311 : Blo 1270453 1271311 := bstep (se 1 (by rfl) ⟨953483, by rfl⟩ : syracuseStep 1271311 = 1906967) B1906967
theorem B2860559 : Blo 1270453 2860559 := bstep (se 1 (by rfl) ⟨2145419, by rfl⟩ : syracuseStep 2860559 = 4290839) B4290839
theorem B13936157 : Blo 1270453 13936157 := bstep (se 3 (by rfl) ⟨2613029, by rfl⟩ : syracuseStep 13936157 = 5226059) B5226059
theorem B2860577 : Blo 1270453 2860577 := bstep (se 2 (by rfl) ⟨1072716, by rfl⟩ : syracuseStep 2860577 = 2145433) B2145433
theorem B1271355 : Blo 1270453 1271355 := bstep (se 1 (by rfl) ⟨953516, by rfl⟩ : syracuseStep 1271355 = 1907033) B1907033
theorem B1271431 : Blo 1270453 1271431 := bstep (se 1 (by rfl) ⟨953573, by rfl⟩ : syracuseStep 1271431 = 1907147) B1907147
theorem B1271439 : Blo 1270453 1271439 := bstep (se 1 (by rfl) ⟨953579, by rfl⟩ : syracuseStep 1271439 = 1907159) B1907159
theorem B1271483 : Blo 1270453 1271483 := bstep (se 1 (by rfl) ⟨953612, by rfl⟩ : syracuseStep 1271483 = 1907225) B1907225
theorem B4826861 : Blo 1270453 4826861 := bstep (se 3 (by rfl) ⟨905036, by rfl⟩ : syracuseStep 4826861 = 1810073) B1810073
theorem B1271559 : Blo 1270453 1271559 := bstep (se 1 (by rfl) ⟨953669, by rfl⟩ : syracuseStep 1271559 = 1907339) B1907339
theorem B1271567 : Blo 1270453 1271567 := bstep (se 1 (by rfl) ⟨953675, by rfl⟩ : syracuseStep 1271567 = 1907351) B1907351
theorem B1271611 : Blo 1270453 1271611 := bstep (se 1 (by rfl) ⟨953708, by rfl⟩ : syracuseStep 1271611 = 1907417) B1907417
theorem B2860919 : Blo 1270453 2860919 := bstep (se 1 (by rfl) ⟨2145689, by rfl⟩ : syracuseStep 2860919 = 4291379) B4291379
theorem B1271687 : Blo 1270453 1271687 := bstep (se 1 (by rfl) ⟨953765, by rfl⟩ : syracuseStep 1271687 = 1907531) B1907531
theorem B1271695 : Blo 1270453 1271695 := bstep (se 1 (by rfl) ⟨953771, by rfl⟩ : syracuseStep 1271695 = 1907543) B1907543
theorem B1271739 : Blo 1270453 1271739 := bstep (se 1 (by rfl) ⟨953804, by rfl⟩ : syracuseStep 1271739 = 1907609) B1907609
theorem B3262409 : Blo 1270453 3262409 := bstep (se 2 (by rfl) ⟨1223403, by rfl⟩ : syracuseStep 3262409 = 2446807) B2446807
theorem B1271815 : Blo 1270453 1271815 := bstep (se 1 (by rfl) ⟨953861, by rfl⟩ : syracuseStep 1271815 = 1907723) B1907723
theorem B1271823 : Blo 1270453 1271823 := bstep (se 1 (by rfl) ⟨953867, by rfl⟩ : syracuseStep 1271823 = 1907735) B1907735
theorem B2861099 : Blo 1270453 2861099 := bstep (se 1 (by rfl) ⟨2145824, by rfl⟩ : syracuseStep 2861099 = 4291649) B4291649
theorem B1271867 : Blo 1270453 1271867 := bstep (se 1 (by rfl) ⟨953900, by rfl⟩ : syracuseStep 1271867 = 1907801) B1907801
theorem B6522967 : Blo 1270453 6522967 := bstep (se 1 (by rfl) ⟨4892225, by rfl⟩ : syracuseStep 6522967 = 9784451) B9784451
theorem B1271943 : Blo 1270453 1271943 := bstep (se 1 (by rfl) ⟨953957, by rfl⟩ : syracuseStep 1271943 = 1907915) B1907915
theorem B1271951 : Blo 1270453 1271951 := bstep (se 1 (by rfl) ⟨953963, by rfl⟩ : syracuseStep 1271951 = 1907927) B1907927
theorem B2320655 : Blo 1270453 2320655 := bstep (se 1 (by rfl) ⟨1740491, by rfl⟩ : syracuseStep 2320655 = 3480983) B3480983
theorem B1607951 : Blo 1270453 1607951 := bstep (se 1 (by rfl) ⟨1205963, by rfl⟩ : syracuseStep 1607951 = 2411927) B2411927
theorem B2861459 : Blo 1270453 2861459 := bstep (se 1 (by rfl) ⟨2146094, by rfl⟩ : syracuseStep 2861459 = 4292189) B4292189
theorem B4827545 : Blo 1270453 4827545 := bstep (se 2 (by rfl) ⟨1810329, by rfl⟩ : syracuseStep 4827545 = 3620659) B3620659
theorem B2861513 : Blo 1270453 2861513 := bstep (se 2 (by rfl) ⟨1073067, by rfl⟩ : syracuseStep 2861513 = 2146135) B2146135
theorem B17386103 : Blo 1270453 17386103 := bstep (se 1 (by rfl) ⟨13039577, by rfl⟩ : syracuseStep 17386103 = 26079155) B26079155
theorem B7236215 : Blo 1270453 7236215 := bstep (se 1 (by rfl) ⟨5427161, by rfl⟩ : syracuseStep 7236215 = 10854323) B10854323
theorem B6204161 : Blo 1270453 6204161 := bstep (se 2 (by rfl) ⟨2326560, by rfl⟩ : syracuseStep 6204161 = 4653121) B4653121
theorem B2714401 : Blo 1270453 2714401 := bstep (se 2 (by rfl) ⟨1017900, by rfl⟩ : syracuseStep 2714401 = 2035801) B2035801
theorem B6876019 : Blo 1270453 6876019 := bstep (se 1 (by rfl) ⟨5157014, by rfl⟩ : syracuseStep 6876019 = 10314029) B10314029
theorem B9669719 : Blo 1270453 9669719 := bstep (se 1 (by rfl) ⟨7252289, by rfl⟩ : syracuseStep 9669719 = 14504579) B14504579
theorem B4828531 : Blo 1270453 4828531 := bstep (se 1 (by rfl) ⟨3621398, by rfl⟩ : syracuseStep 4828531 = 7242797) B7242797
theorem B6434315 : Blo 1270453 6434315 := bstep (se 1 (by rfl) ⟨4825736, by rfl⟩ : syracuseStep 6434315 = 9651473) B9651473
theorem B2035243 : Blo 1270453 2035243 := bstep (se 1 (by rfl) ⟨1526432, by rfl⟩ : syracuseStep 2035243 = 3052865) B3052865
theorem B6434477 : Blo 1270453 6434477 := bstep (se 3 (by rfl) ⟨1206464, by rfl⟩ : syracuseStep 6434477 = 2412929) B2412929
theorem B125710051 : Blo 1270453 125710051 := bstep (se 1 (by rfl) ⟨94282538, by rfl⟩ : syracuseStep 125710051 = 188565077) B188565077
theorem B4288409 : Blo 1270453 4288409 := bstep (se 2 (by rfl) ⟨1608153, by rfl⟩ : syracuseStep 4288409 = 3216307) B3216307
theorem B1429519 : Blo 1270453 1429519 := bstep (se 1 (by rfl) ⟨1072139, by rfl⟩ : syracuseStep 1429519 = 2144279) B2144279
theorem B2412679 : Blo 1270453 2412679 := bstep (se 1 (by rfl) ⟨1809509, by rfl⟩ : syracuseStep 2412679 = 3619019) B3619019
theorem B2576569 : Blo 1270453 2576569 := bstep (se 2 (by rfl) ⟨966213, by rfl⟩ : syracuseStep 2576569 = 1932427) B1932427
theorem B10858697 : Blo 1270453 10858697 := bstep (se 2 (by rfl) ⟨4072011, by rfl⟩ : syracuseStep 10858697 = 8144023) B8144023
theorem B2715947 : Blo 1270453 2715947 := bstep (se 1 (by rfl) ⟨2036960, by rfl⟩ : syracuseStep 2715947 = 4073921) B4073921
theorem B1430023 : Blo 1270453 1430023 := bstep (se 1 (by rfl) ⟨1072517, by rfl⟩ : syracuseStep 1430023 = 2145035) B2145035
theorem B451957265 : Blo 1270453 451957265 := bstep (se 2 (by rfl) ⟨169483974, by rfl⟩ : syracuseStep 451957265 = 338967949) B338967949
theorem B4346455 : Blo 1270453 4346455 := bstep (se 1 (by rfl) ⟨3259841, by rfl⟩ : syracuseStep 4346455 = 6519683) B6519683
theorem B4289111 : Blo 1270453 4289111 := bstep (se 1 (by rfl) ⟨3216833, by rfl⟩ : syracuseStep 4289111 = 6433667) B6433667
theorem B4584055 : Blo 1270453 4584055 := bstep (se 1 (by rfl) ⟨3438041, by rfl⟩ : syracuseStep 4584055 = 6876083) B6876083
theorem B15471283 : Blo 1270453 15471283 := bstep (se 1 (by rfl) ⟨11603462, by rfl⟩ : syracuseStep 15471283 = 23206925) B23206925
theorem B1430203 : Blo 1270453 1430203 := bstep (se 1 (by rfl) ⟨1072652, by rfl⟩ : syracuseStep 1430203 = 2145305) B2145305
theorem B16282457 : Blo 1270453 16282457 := bstep (se 2 (by rfl) ⟨6105921, by rfl⟩ : syracuseStep 16282457 = 12211843) B12211843
theorem B7836551 : Blo 1270453 7836551 := bstep (se 1 (by rfl) ⟨5877413, by rfl⟩ : syracuseStep 7836551 = 11754827) B11754827
theorem B1905707 : Blo 1270453 1905707 := bstep (se 1 (by rfl) ⟨1429280, by rfl⟩ : syracuseStep 1905707 = 2858561) B2858561
theorem B1356859 : Blo 1270453 1356859 := bstep (se 1 (by rfl) ⟨1017644, by rfl⟩ : syracuseStep 1356859 = 2035289) B2035289
theorem B4289597 : Blo 1270453 4289597 := bstep (se 3 (by rfl) ⟨804299, by rfl⟩ : syracuseStep 4289597 = 1608599) B1608599
theorem B1905737 : Blo 1270453 1905737 := bstep (se 2 (by rfl) ⟨714651, by rfl⟩ : syracuseStep 1905737 = 1429303) B1429303
theorem B1430671 : Blo 1270453 1430671 := bstep (se 1 (by rfl) ⟨1073003, by rfl⟩ : syracuseStep 1430671 = 2146007) B2146007
theorem B1905851 : Blo 1270453 1905851 := bstep (se 1 (by rfl) ⟨1429388, by rfl⟩ : syracuseStep 1905851 = 2858777) B2858777
theorem B2290889 : Blo 1270453 2290889 := bstep (se 2 (by rfl) ⟨859083, by rfl⟩ : syracuseStep 2290889 = 1718167) B1718167
theorem B1905911 : Blo 1270453 1905911 := bstep (se 1 (by rfl) ⟨1429433, by rfl⟩ : syracuseStep 1905911 = 2858867) B2858867
theorem B6436097 : Blo 1270453 6436097 := bstep (se 2 (by rfl) ⟨2413536, by rfl⟩ : syracuseStep 6436097 = 4827073) B4827073
theorem B1905935 : Blo 1270453 1905935 := bstep (se 1 (by rfl) ⟨1429451, by rfl⟩ : syracuseStep 1905935 = 2858903) B2858903
theorem B1905977 : Blo 1270453 1905977 := bstep (se 2 (by rfl) ⟨714741, by rfl⟩ : syracuseStep 1905977 = 1429483) B1429483
theorem B1906055 : Blo 1270453 1906055 := bstep (se 1 (by rfl) ⟨1429541, by rfl⟩ : syracuseStep 1906055 = 2859083) B2859083
theorem B3216793 : Blo 1270453 3216793 := bstep (se 2 (by rfl) ⟨1206297, by rfl⟩ : syracuseStep 3216793 = 2412595) B2412595
theorem B1906091 : Blo 1270453 1906091 := bstep (se 1 (by rfl) ⟨1429568, by rfl⟩ : syracuseStep 1906091 = 2859137) B2859137
theorem B3618233 : Blo 1270453 3618233 := bstep (se 2 (by rfl) ⟨1356837, by rfl⟩ : syracuseStep 3618233 = 2713675) B2713675
theorem B1906121 : Blo 1270453 1906121 := bstep (se 2 (by rfl) ⟨714795, by rfl⟩ : syracuseStep 1906121 = 1429591) B1429591
theorem B1906235 : Blo 1270453 1906235 := bstep (se 1 (by rfl) ⟨1429676, by rfl⟩ : syracuseStep 1906235 = 2859353) B2859353
theorem B3216955 : Blo 1270453 3216955 := bstep (se 1 (by rfl) ⟨2412716, by rfl⟩ : syracuseStep 3216955 = 4825433) B4825433
theorem B2037307 : Blo 1270453 2037307 := bstep (se 1 (by rfl) ⟨1527980, by rfl⟩ : syracuseStep 2037307 = 3055961) B3055961
theorem B1906295 : Blo 1270453 1906295 := bstep (se 1 (by rfl) ⟨1429721, by rfl⟩ : syracuseStep 1906295 = 2859443) B2859443
theorem B1906319 : Blo 1270453 1906319 := bstep (se 1 (by rfl) ⟨1429739, by rfl⟩ : syracuseStep 1906319 = 2859479) B2859479
theorem B1906361 : Blo 1270453 1906361 := bstep (se 2 (by rfl) ⟨714885, by rfl⟩ : syracuseStep 1906361 = 1429771) B1429771
theorem B3217097 : Blo 1270453 3217097 := bstep (se 2 (by rfl) ⟨1206411, by rfl⟩ : syracuseStep 3217097 = 2412823) B2412823
theorem B2414281 : Blo 1270453 2414281 := bstep (se 2 (by rfl) ⟨905355, by rfl⟩ : syracuseStep 2414281 = 1810711) B1810711
theorem B48297701 : Blo 1270453 48297701 := bstep (se 4 (by rfl) ⟨4527909, by rfl⟩ : syracuseStep 48297701 = 9055819) B9055819
theorem B1906439 : Blo 1270453 1906439 := bstep (se 1 (by rfl) ⟨1429829, by rfl⟩ : syracuseStep 1906439 = 2859659) B2859659
theorem B1906475 : Blo 1270453 1906475 := bstep (se 1 (by rfl) ⟨1429856, by rfl⟩ : syracuseStep 1906475 = 2859713) B2859713
theorem B1906505 : Blo 1270453 1906505 := bstep (se 2 (by rfl) ⟨714939, by rfl⟩ : syracuseStep 1906505 = 1429879) B1429879
theorem B1906619 : Blo 1270453 1906619 := bstep (se 1 (by rfl) ⟨1429964, by rfl⟩ : syracuseStep 1906619 = 2859929) B2859929
theorem B1906679 : Blo 1270453 1906679 := bstep (se 1 (by rfl) ⟨1430009, by rfl⟩ : syracuseStep 1906679 = 2860019) B2860019
theorem B1906703 : Blo 1270453 1906703 := bstep (se 1 (by rfl) ⟨1430027, by rfl⟩ : syracuseStep 1906703 = 2860055) B2860055
theorem B3217441 : Blo 1270453 3217441 := bstep (se 2 (by rfl) ⟨1206540, by rfl⟩ : syracuseStep 3217441 = 2413081) B2413081
theorem B2144299 : Blo 1270453 2144299 := bstep (se 1 (by rfl) ⟨1608224, by rfl⟩ : syracuseStep 2144299 = 3216449) B3216449
theorem B6436907 : Blo 1270453 6436907 := bstep (se 1 (by rfl) ⟨4827680, by rfl⟩ : syracuseStep 6436907 = 9655361) B9655361
theorem B1906745 : Blo 1270453 1906745 := bstep (se 2 (by rfl) ⟨715029, by rfl⟩ : syracuseStep 1906745 = 1430059) B1430059
theorem B1718329 : Blo 1270453 1718329 := bstep (se 2 (by rfl) ⟨644373, by rfl⟩ : syracuseStep 1718329 = 1288747) B1288747
theorem B1906823 : Blo 1270453 1906823 := bstep (se 1 (by rfl) ⟨1430117, by rfl⟩ : syracuseStep 1906823 = 2860235) B2860235
theorem B1906859 : Blo 1270453 1906859 := bstep (se 1 (by rfl) ⟨1430144, by rfl⟩ : syracuseStep 1906859 = 2860289) B2860289
theorem B2144441 : Blo 1270453 2144441 := bstep (se 2 (by rfl) ⟨804165, by rfl⟩ : syracuseStep 2144441 = 1608331) B1608331
theorem B7239881 : Blo 1270453 7239881 := bstep (se 2 (by rfl) ⟨2714955, by rfl⟩ : syracuseStep 7239881 = 5429911) B5429911
theorem B1906889 : Blo 1270453 1906889 := bstep (se 2 (by rfl) ⟨715083, by rfl⟩ : syracuseStep 1906889 = 1430167) B1430167
theorem B5429537 : Blo 1270453 5429537 := bstep (se 2 (by rfl) ⟨2036076, by rfl⟩ : syracuseStep 5429537 = 4072153) B4072153
theorem B1907003 : Blo 1270453 1907003 := bstep (se 1 (by rfl) ⟨1430252, by rfl⟩ : syracuseStep 1907003 = 2860505) B2860505
theorem B14473565 : Blo 1270453 14473565 := bstep (se 3 (by rfl) ⟨2713793, by rfl⟩ : syracuseStep 14473565 = 5427587) B5427587
theorem B1907063 : Blo 1270453 1907063 := bstep (se 1 (by rfl) ⟨1430297, by rfl⟩ : syracuseStep 1907063 = 2860595) B2860595
theorem B1907087 : Blo 1270453 1907087 := bstep (se 1 (by rfl) ⟨1430315, by rfl⟩ : syracuseStep 1907087 = 2860631) B2860631
theorem B4291001 : Blo 1270453 4291001 := bstep (se 2 (by rfl) ⟨1609125, by rfl⟩ : syracuseStep 4291001 = 3218251) B3218251
theorem B1907129 : Blo 1270453 1907129 := bstep (se 2 (by rfl) ⟨715173, by rfl⟩ : syracuseStep 1907129 = 1430347) B1430347
theorem B1907207 : Blo 1270453 1907207 := bstep (se 1 (by rfl) ⟨1430405, by rfl⟩ : syracuseStep 1907207 = 2860811) B2860811
theorem B3054095 : Blo 1270453 3054095 := bstep (se 1 (by rfl) ⟨2290571, by rfl⟩ : syracuseStep 3054095 = 4581143) B4581143
theorem B1907243 : Blo 1270453 1907243 := bstep (se 1 (by rfl) ⟨1430432, by rfl⟩ : syracuseStep 1907243 = 2860865) B2860865
theorem B1907273 : Blo 1270453 1907273 := bstep (se 2 (by rfl) ⟨715227, by rfl⟩ : syracuseStep 1907273 = 1430455) B1430455
theorem B3218039 : Blo 1270453 3218039 := bstep (se 1 (by rfl) ⟨2413529, by rfl⟩ : syracuseStep 3218039 = 4827059) B4827059
theorem B3619475 : Blo 1270453 3619475 := bstep (se 1 (by rfl) ⟨2714606, by rfl⟩ : syracuseStep 3619475 = 5429213) B5429213
theorem B1907387 : Blo 1270453 1907387 := bstep (se 1 (by rfl) ⟨1430540, by rfl⟩ : syracuseStep 1907387 = 2861081) B2861081
theorem B1833673 : Blo 1270453 1833673 := bstep (se 2 (by rfl) ⟨687627, by rfl⟩ : syracuseStep 1833673 = 1375255) B1375255
theorem B1907447 : Blo 1270453 1907447 := bstep (se 1 (by rfl) ⟨1430585, by rfl⟩ : syracuseStep 1907447 = 2861171) B2861171
theorem B1907471 : Blo 1270453 1907471 := bstep (se 1 (by rfl) ⟨1430603, by rfl⟩ : syracuseStep 1907471 = 2861207) B2861207
theorem B1907513 : Blo 1270453 1907513 := bstep (se 2 (by rfl) ⟨715317, by rfl⟩ : syracuseStep 1907513 = 1430635) B1430635
theorem B2145143 : Blo 1270453 2145143 := bstep (se 1 (by rfl) ⟨1608857, by rfl⟩ : syracuseStep 2145143 = 3217715) B3217715
theorem B1907591 : Blo 1270453 1907591 := bstep (se 1 (by rfl) ⟨1430693, by rfl⟩ : syracuseStep 1907591 = 2861387) B2861387
theorem B1907627 : Blo 1270453 1907627 := bstep (se 1 (by rfl) ⟨1430720, by rfl⟩ : syracuseStep 1907627 = 2861441) B2861441
theorem B2939833 : Blo 1270453 2939833 := bstep (se 2 (by rfl) ⟨1102437, by rfl⟩ : syracuseStep 2939833 = 2204875) B2204875
theorem B1907657 : Blo 1270453 1907657 := bstep (se 2 (by rfl) ⟨715371, by rfl⟩ : syracuseStep 1907657 = 1430743) B1430743
theorem B4291595 : Blo 1270453 4291595 := bstep (se 1 (by rfl) ⟨3218696, by rfl⟩ : syracuseStep 4291595 = 6437393) B6437393
theorem B7339031 : Blo 1270453 7339031 := bstep (se 1 (by rfl) ⟨5504273, by rfl⟩ : syracuseStep 7339031 = 11008547) B11008547
theorem B1907771 : Blo 1270453 1907771 := bstep (se 1 (by rfl) ⟨1430828, by rfl⟩ : syracuseStep 1907771 = 2861657) B2861657
theorem B1809481 : Blo 1270453 1809481 := bstep (se 2 (by rfl) ⟨678555, by rfl⟩ : syracuseStep 1809481 = 1357111) B1357111
theorem B4291703 : Blo 1270453 4291703 := bstep (se 1 (by rfl) ⟨3218777, by rfl⟩ : syracuseStep 4291703 = 6437555) B6437555
theorem B1907831 : Blo 1270453 1907831 := bstep (se 1 (by rfl) ⟨1430873, by rfl⟩ : syracuseStep 1907831 = 2861747) B2861747
theorem B1907855 : Blo 1270453 1907855 := bstep (se 1 (by rfl) ⟨1430891, by rfl⟩ : syracuseStep 1907855 = 2861783) B2861783
theorem B1907897 : Blo 1270453 1907897 := bstep (se 2 (by rfl) ⟨715461, by rfl⟩ : syracuseStep 1907897 = 1430923) B1430923
theorem B13737197 : Blo 1270453 13737197 := bstep (se 3 (by rfl) ⟨2575724, by rfl⟩ : syracuseStep 13737197 = 5151449) B5151449
theorem B1547527 : Blo 1270453 1547527 := bstep (se 1 (by rfl) ⟨1160645, by rfl⟩ : syracuseStep 1547527 = 2321291) B2321291
theorem B2145595 : Blo 1270453 2145595 := bstep (se 1 (by rfl) ⟨1609196, by rfl⟩ : syracuseStep 2145595 = 3218393) B3218393
theorem B6438203 : Blo 1270453 6438203 := bstep (se 1 (by rfl) ⟨4828652, by rfl⟩ : syracuseStep 6438203 = 9657305) B9657305
theorem B13745501 : Blo 1270453 13745501 := bstep (se 3 (by rfl) ⟨2577281, by rfl⟩ : syracuseStep 13745501 = 5154563) B5154563
theorem B1834411 : Blo 1270453 1834411 := bstep (se 1 (by rfl) ⟨1375808, by rfl⟩ : syracuseStep 1834411 = 2751617) B2751617
theorem B10862009 : Blo 1270453 10862009 := bstep (se 2 (by rfl) ⟨4073253, by rfl⟩ : syracuseStep 10862009 = 8146507) B8146507
theorem B2145737 : Blo 1270453 2145737 := bstep (se 2 (by rfl) ⟨804651, by rfl⟩ : syracuseStep 2145737 = 1609303) B1609303
theorem B6438365 : Blo 1270453 6438365 := bstep (se 3 (by rfl) ⟨1207193, by rfl⟩ : syracuseStep 6438365 = 2414387) B2414387
theorem B4349483 : Blo 1270453 4349483 := bstep (se 1 (by rfl) ⟨3262112, by rfl⟩ : syracuseStep 4349483 = 6524225) B6524225
theorem B4824643 : Blo 1270453 4824643 := bstep (se 1 (by rfl) ⟨3618482, by rfl⟩ : syracuseStep 4824643 = 7236965) B7236965
theorem B4070999 : Blo 1270453 4070999 := bstep (se 1 (by rfl) ⟨3053249, by rfl⟩ : syracuseStep 4070999 = 6106499) B6106499
theorem B2858615 : Blo 1270453 2858615 := bstep (se 1 (by rfl) ⟨2143961, by rfl⟩ : syracuseStep 2858615 = 4287923) B4287923
theorem B1810039 : Blo 1270453 1810039 := bstep (se 1 (by rfl) ⟨1357529, by rfl⟩ : syracuseStep 1810039 = 2715059) B2715059
theorem B4292297 : Blo 1270453 4292297 := bstep (se 2 (by rfl) ⟨1609611, by rfl⟩ : syracuseStep 4292297 = 3219223) B3219223
theorem B6110957 : Blo 1270453 6110957 := bstep (se 3 (by rfl) ⟨1145804, by rfl⟩ : syracuseStep 6110957 = 2291609) B2291609
theorem B14475023 : Blo 1270453 14475023 := bstep (se 1 (by rfl) ⟨10856267, by rfl⟩ : syracuseStep 14475023 = 21712535) B21712535
theorem B6438689 : Blo 1270453 6438689 := bstep (se 2 (by rfl) ⟨2414508, by rfl⟩ : syracuseStep 6438689 = 4829017) B4829017
theorem B2858795 : Blo 1270453 2858795 := bstep (se 1 (by rfl) ⟨2144096, by rfl⟩ : syracuseStep 2858795 = 4288193) B4288193
theorem B16514891 : Blo 1270453 16514891 := bstep (se 1 (by rfl) ⟨12386168, by rfl⟩ : syracuseStep 16514891 = 24772337) B24772337
theorem B4824947 : Blo 1270453 4824947 := bstep (se 1 (by rfl) ⟨3618710, by rfl⟩ : syracuseStep 4824947 = 7237421) B7237421
theorem B3219335 : Blo 1270453 3219335 := bstep (se 1 (by rfl) ⟨2414501, by rfl⟩ : syracuseStep 3219335 = 4829003) B4829003
theorem B3219385 : Blo 1270453 3219385 := bstep (se 2 (by rfl) ⟨1207269, by rfl⟩ : syracuseStep 3219385 = 2414539) B2414539
theorem B2859065 : Blo 1270453 2859065 := bstep (se 2 (by rfl) ⟨1072149, by rfl⟩ : syracuseStep 2859065 = 2144299) B2144299
theorem B1810631 : Blo 1270453 1810631 := bstep (se 1 (by rfl) ⟨1357973, by rfl⟩ : syracuseStep 1810631 = 2715947) B2715947
theorem B2859407 : Blo 1270453 2859407 := bstep (se 1 (by rfl) ⟨2144555, by rfl⟩ : syracuseStep 2859407 = 4289111) B4289111
theorem B10854971 : Blo 1270453 10854971 := bstep (se 1 (by rfl) ⟨8141228, by rfl⟩ : syracuseStep 10854971 = 16282457) B16282457
theorem B1270471 : Blo 1270453 1270471 := bstep (se 1 (by rfl) ⟨952853, by rfl⟩ : syracuseStep 1270471 = 1905707) B1905707
theorem B2859731 : Blo 1270453 2859731 := bstep (se 1 (by rfl) ⟨2144798, by rfl⟩ : syracuseStep 2859731 = 4289597) B4289597
theorem B1270491 : Blo 1270453 1270491 := bstep (se 1 (by rfl) ⟨952868, by rfl⟩ : syracuseStep 1270491 = 1905737) B1905737
theorem B1270567 : Blo 1270453 1270567 := bstep (se 1 (by rfl) ⟨952925, by rfl⟩ : syracuseStep 1270567 = 1905851) B1905851
theorem B6112073 : Blo 1270453 6112073 := bstep (se 2 (by rfl) ⟨2292027, by rfl⟩ : syracuseStep 6112073 = 4584055) B4584055
theorem B1270607 : Blo 1270453 1270607 := bstep (se 1 (by rfl) ⟨952955, by rfl⟩ : syracuseStep 1270607 = 1905911) B1905911
theorem B1270623 : Blo 1270453 1270623 := bstep (se 1 (by rfl) ⟨952967, by rfl⟩ : syracuseStep 1270623 = 1905935) B1905935
theorem B1270651 : Blo 1270453 1270651 := bstep (se 1 (by rfl) ⟨952988, by rfl⟩ : syracuseStep 1270651 = 1905977) B1905977
theorem B20628377 : Blo 1270453 20628377 := bstep (se 2 (by rfl) ⟨7735641, by rfl⟩ : syracuseStep 20628377 = 15471283) B15471283
theorem B1270703 : Blo 1270453 1270703 := bstep (se 1 (by rfl) ⟨953027, by rfl⟩ : syracuseStep 1270703 = 1906055) B1906055
theorem B1270727 : Blo 1270453 1270727 := bstep (se 1 (by rfl) ⟨953045, by rfl⟩ : syracuseStep 1270727 = 1906091) B1906091
theorem B1270747 : Blo 1270453 1270747 := bstep (se 1 (by rfl) ⟨953060, by rfl⟩ : syracuseStep 1270747 = 1906121) B1906121
theorem B9290771 : Blo 1270453 9290771 := bstep (se 1 (by rfl) ⟨6968078, by rfl⟩ : syracuseStep 9290771 = 13936157) B13936157
theorem B1270823 : Blo 1270453 1270823 := bstep (se 1 (by rfl) ⟨953117, by rfl⟩ : syracuseStep 1270823 = 1906235) B1906235
theorem B1270863 : Blo 1270453 1270863 := bstep (se 1 (by rfl) ⟨953147, by rfl⟩ : syracuseStep 1270863 = 1906295) B1906295
theorem B1270879 : Blo 1270453 1270879 := bstep (se 1 (by rfl) ⟨953159, by rfl⟩ : syracuseStep 1270879 = 1906319) B1906319
theorem B1270907 : Blo 1270453 1270907 := bstep (se 1 (by rfl) ⟨953180, by rfl⟩ : syracuseStep 1270907 = 1906361) B1906361
theorem B9168025 : Blo 1270453 9168025 := bstep (se 2 (by rfl) ⟨3438009, by rfl⟩ : syracuseStep 9168025 = 6876019) B6876019
theorem B1270959 : Blo 1270453 1270959 := bstep (se 1 (by rfl) ⟨953219, by rfl⟩ : syracuseStep 1270959 = 1906439) B1906439
theorem B1270983 : Blo 1270453 1270983 := bstep (se 1 (by rfl) ⟨953237, by rfl⟩ : syracuseStep 1270983 = 1906475) B1906475
theorem B1271003 : Blo 1270453 1271003 := bstep (se 1 (by rfl) ⟨953252, by rfl⟩ : syracuseStep 1271003 = 1906505) B1906505
theorem B1271079 : Blo 1270453 1271079 := bstep (se 1 (by rfl) ⟨953309, by rfl⟩ : syracuseStep 1271079 = 1906619) B1906619
theorem B1271119 : Blo 1270453 1271119 := bstep (se 1 (by rfl) ⟨953339, by rfl⟩ : syracuseStep 1271119 = 1906679) B1906679
theorem B1271135 : Blo 1270453 1271135 := bstep (se 1 (by rfl) ⟨953351, by rfl⟩ : syracuseStep 1271135 = 1906703) B1906703
theorem B1271163 : Blo 1270453 1271163 := bstep (se 1 (by rfl) ⟨953372, by rfl⟩ : syracuseStep 1271163 = 1906745) B1906745
theorem B1271215 : Blo 1270453 1271215 := bstep (se 1 (by rfl) ⟨953411, by rfl⟩ : syracuseStep 1271215 = 1906823) B1906823
theorem B1271239 : Blo 1270453 1271239 := bstep (se 1 (by rfl) ⟨953429, by rfl⟩ : syracuseStep 1271239 = 1906859) B1906859
theorem B4826587 : Blo 1270453 4826587 := bstep (se 1 (by rfl) ⟨3619940, by rfl⟩ : syracuseStep 4826587 = 7239881) B7239881
theorem B1271259 : Blo 1270453 1271259 := bstep (se 1 (by rfl) ⟨953444, by rfl⟩ : syracuseStep 1271259 = 1906889) B1906889
theorem B1271335 : Blo 1270453 1271335 := bstep (se 1 (by rfl) ⟨953501, by rfl⟩ : syracuseStep 1271335 = 1907003) B1907003
theorem B1271375 : Blo 1270453 1271375 := bstep (se 1 (by rfl) ⟨953531, by rfl⟩ : syracuseStep 1271375 = 1907063) B1907063
theorem B1271391 : Blo 1270453 1271391 := bstep (se 1 (by rfl) ⟨953543, by rfl⟩ : syracuseStep 1271391 = 1907087) B1907087
theorem B2860667 : Blo 1270453 2860667 := bstep (se 1 (by rfl) ⟨2145500, by rfl⟩ : syracuseStep 2860667 = 4291001) B4291001
theorem B1271419 : Blo 1270453 1271419 := bstep (se 1 (by rfl) ⟨953564, by rfl⟩ : syracuseStep 1271419 = 1907129) B1907129
theorem B1271471 : Blo 1270453 1271471 := bstep (se 1 (by rfl) ⟨953603, by rfl⟩ : syracuseStep 1271471 = 1907207) B1907207
theorem B1271495 : Blo 1270453 1271495 := bstep (se 1 (by rfl) ⟨953621, by rfl⟩ : syracuseStep 1271495 = 1907243) B1907243
theorem B1271515 : Blo 1270453 1271515 := bstep (se 1 (by rfl) ⟨953636, by rfl⟩ : syracuseStep 1271515 = 1907273) B1907273
theorem B2860793 : Blo 1270453 2860793 := bstep (se 2 (by rfl) ⟨1072797, by rfl⟩ : syracuseStep 2860793 = 2145595) B2145595
theorem B1271591 : Blo 1270453 1271591 := bstep (se 1 (by rfl) ⟨953693, by rfl⟩ : syracuseStep 1271591 = 1907387) B1907387
theorem B1271631 : Blo 1270453 1271631 := bstep (se 1 (by rfl) ⟨953723, by rfl⟩ : syracuseStep 1271631 = 1907447) B1907447
theorem B1271647 : Blo 1270453 1271647 := bstep (se 1 (by rfl) ⟨953735, by rfl⟩ : syracuseStep 1271647 = 1907471) B1907471
theorem B1271675 : Blo 1270453 1271675 := bstep (se 1 (by rfl) ⟨953756, by rfl⟩ : syracuseStep 1271675 = 1907513) B1907513
theorem B1271727 : Blo 1270453 1271727 := bstep (se 1 (by rfl) ⟨953795, by rfl⟩ : syracuseStep 1271727 = 1907591) B1907591
theorem B1271751 : Blo 1270453 1271751 := bstep (se 1 (by rfl) ⟨953813, by rfl⟩ : syracuseStep 1271751 = 1907627) B1907627
theorem B1271771 : Blo 1270453 1271771 := bstep (se 1 (by rfl) ⟨953828, by rfl⟩ : syracuseStep 1271771 = 1907657) B1907657
theorem B2861063 : Blo 1270453 2861063 := bstep (se 1 (by rfl) ⟨2145797, by rfl⟩ : syracuseStep 2861063 = 4291595) B4291595
theorem B4892687 : Blo 1270453 4892687 := bstep (se 1 (by rfl) ⟨3669515, by rfl⟩ : syracuseStep 4892687 = 7339031) B7339031
theorem B1271847 : Blo 1270453 1271847 := bstep (se 1 (by rfl) ⟨953885, by rfl⟩ : syracuseStep 1271847 = 1907771) B1907771
theorem B2713657 : Blo 1270453 2713657 := bstep (se 2 (by rfl) ⟨1017621, by rfl⟩ : syracuseStep 2713657 = 2035243) B2035243
theorem B2861135 : Blo 1270453 2861135 := bstep (se 1 (by rfl) ⟨2145851, by rfl⟩ : syracuseStep 2861135 = 4291703) B4291703
theorem B1271887 : Blo 1270453 1271887 := bstep (se 1 (by rfl) ⟨953915, by rfl⟩ : syracuseStep 1271887 = 1907831) B1907831
theorem B6432857 : Blo 1270453 6432857 := bstep (se 2 (by rfl) ⟨2412321, by rfl⟩ : syracuseStep 6432857 = 4824643) B4824643
theorem B1271903 : Blo 1270453 1271903 := bstep (se 1 (by rfl) ⟨953927, by rfl⟩ : syracuseStep 1271903 = 1907855) B1907855
theorem B1271931 : Blo 1270453 1271931 := bstep (se 1 (by rfl) ⟨953948, by rfl⟩ : syracuseStep 1271931 = 1907897) B1907897
theorem B2713999 : Blo 1270453 2713999 := bstep (se 1 (by rfl) ⟨2035499, by rfl⟩ : syracuseStep 2713999 = 4070999) B4070999
theorem B2861531 : Blo 1270453 2861531 := bstep (se 1 (by rfl) ⟨2146148, by rfl⟩ : syracuseStep 2861531 = 4292297) B4292297
theorem B4073971 : Blo 1270453 4073971 := bstep (se 1 (by rfl) ⟨3055478, by rfl⟩ : syracuseStep 4073971 = 6110957) B6110957
theorem B4827833 : Blo 1270453 4827833 := bstep (se 2 (by rfl) ⟨1810437, by rfl⟩ : syracuseStep 4827833 = 3620875) B3620875
theorem B4827863 : Blo 1270453 4827863 := bstep (se 1 (by rfl) ⟨3620897, by rfl⟩ : syracuseStep 4827863 = 7241795) B7241795
theorem B10857361 : Blo 1270453 10857361 := bstep (se 2 (by rfl) ⟨4071510, by rfl⟩ : syracuseStep 10857361 = 8143021) B8143021
theorem B3435425 : Blo 1270453 3435425 := bstep (se 2 (by rfl) ⟨1288284, by rfl⟩ : syracuseStep 3435425 = 2576569) B2576569
theorem B301304843 : Blo 1270453 301304843 := bstep (se 1 (by rfl) ⟨225978632, by rfl⟩ : syracuseStep 301304843 = 451957265) B451957265
theorem B9923627 : Blo 1270453 9923627 := bstep (se 1 (by rfl) ⟨7442720, by rfl⟩ : syracuseStep 9923627 = 14885441) B14885441
theorem B6876211 : Blo 1270453 6876211 := bstep (se 1 (by rfl) ⟨5157158, by rfl⟩ : syracuseStep 6876211 = 10314317) B10314317
theorem B4959313 : Blo 1270453 4959313 := bstep (se 2 (by rfl) ⟨1859742, by rfl⟩ : syracuseStep 4959313 = 3719485) B3719485
theorem B4287869 : Blo 1270453 4287869 := bstep (se 3 (by rfl) ⟨803975, by rfl⟩ : syracuseStep 4287869 = 1607951) B1607951
theorem B6188413 : Blo 1270453 6188413 := bstep (se 3 (by rfl) ⟨1160327, by rfl⟩ : syracuseStep 6188413 = 2320655) B2320655
theorem B5795273 : Blo 1270453 5795273 := bstep (se 2 (by rfl) ⟨2173227, by rfl⟩ : syracuseStep 5795273 = 4346455) B4346455
theorem B1527259 : Blo 1270453 1527259 := bstep (se 1 (by rfl) ⟨1145444, by rfl⟩ : syracuseStep 1527259 = 2290889) B2290889
theorem B2444897 : Blo 1270453 2444897 := bstep (se 2 (by rfl) ⟨916836, by rfl⟩ : syracuseStep 2444897 = 1833673) B1833673
theorem B2412155 : Blo 1270453 2412155 := bstep (se 1 (by rfl) ⟨1809116, by rfl⟩ : syracuseStep 2412155 = 3618233) B3618233
theorem B4288139 : Blo 1270453 4288139 := bstep (se 1 (by rfl) ⟨3216104, by rfl⟩ : syracuseStep 4288139 = 6432209) B6432209
theorem B32198467 : Blo 1270453 32198467 := bstep (se 1 (by rfl) ⟨24148850, by rfl⟩ : syracuseStep 32198467 = 48297701) B48297701
theorem B2174939 : Blo 1270453 2174939 := bstep (se 1 (by rfl) ⟨1631204, by rfl⟩ : syracuseStep 2174939 = 3262409) B3262409
theorem B2412641 : Blo 1270453 2412641 := bstep (se 2 (by rfl) ⟨904740, by rfl⟩ : syracuseStep 2412641 = 1809481) B1809481
theorem B1429627 : Blo 1270453 1429627 := bstep (se 1 (by rfl) ⟨1072220, by rfl⟩ : syracuseStep 1429627 = 2144441) B2144441
theorem B2036063 : Blo 1270453 2036063 := bstep (se 1 (by rfl) ⟨1527047, by rfl⟩ : syracuseStep 2036063 = 3054095) B3054095
theorem B2412983 : Blo 1270453 2412983 := bstep (se 1 (by rfl) ⟨1809737, by rfl⟩ : syracuseStep 2412983 = 3619475) B3619475
theorem B4289057 : Blo 1270453 4289057 := bstep (se 2 (by rfl) ⟨1608396, by rfl⟩ : syracuseStep 4289057 = 3216793) B3216793
theorem B2445881 : Blo 1270453 2445881 := bstep (se 2 (by rfl) ⟨917205, by rfl⟩ : syracuseStep 2445881 = 1834411) B1834411
theorem B1430095 : Blo 1270453 1430095 := bstep (se 1 (by rfl) ⟨1072571, by rfl⟩ : syracuseStep 1430095 = 2145143) B2145143
theorem B4289273 : Blo 1270453 4289273 := bstep (se 2 (by rfl) ⟨1608477, by rfl⟩ : syracuseStep 4289273 = 3216955) B3216955
theorem B2716409 : Blo 1270453 2716409 := bstep (se 2 (by rfl) ⟨1018653, by rfl⟩ : syracuseStep 2716409 = 2037307) B2037307
theorem B2413385 : Blo 1270453 2413385 := bstep (se 2 (by rfl) ⟨905019, by rfl⟩ : syracuseStep 2413385 = 1810039) B1810039
theorem B9163667 : Blo 1270453 9163667 := bstep (se 1 (by rfl) ⟨6872750, by rfl⟩ : syracuseStep 9163667 = 13745501) B13745501
theorem B167613401 : Blo 1270453 167613401 := bstep (se 2 (by rfl) ⟨62855025, by rfl⟩ : syracuseStep 167613401 = 125710051) B125710051
theorem B1430491 : Blo 1270453 1430491 := bstep (se 1 (by rfl) ⟨1072868, by rfl⟩ : syracuseStep 1430491 = 2145737) B2145737
theorem B4289543 : Blo 1270453 4289543 := bstep (se 1 (by rfl) ⟨3217157, by rfl⟩ : syracuseStep 4289543 = 6434315) B6434315
theorem B1905743 : Blo 1270453 1905743 := bstep (se 1 (by rfl) ⟨1429307, by rfl⟩ : syracuseStep 1905743 = 2858615) B2858615
theorem B4289651 : Blo 1270453 4289651 := bstep (se 1 (by rfl) ⟨3217238, by rfl⟩ : syracuseStep 4289651 = 6434477) B6434477
theorem B1905863 : Blo 1270453 1905863 := bstep (se 1 (by rfl) ⟨1429397, by rfl⟩ : syracuseStep 1905863 = 2858795) B2858795
theorem B3216631 : Blo 1270453 3216631 := bstep (se 1 (by rfl) ⟨2412473, by rfl⟩ : syracuseStep 3216631 = 4824947) B4824947
theorem B1906025 : Blo 1270453 1906025 := bstep (se 2 (by rfl) ⟨714759, by rfl⟩ : syracuseStep 1906025 = 1429519) B1429519
theorem B4289921 : Blo 1270453 4289921 := bstep (se 2 (by rfl) ⟨1608720, by rfl⟩ : syracuseStep 4289921 = 3217441) B3217441
theorem B2291105 : Blo 1270453 2291105 := bstep (se 2 (by rfl) ⟨859164, by rfl⟩ : syracuseStep 2291105 = 1718329) B1718329
theorem B1906103 : Blo 1270453 1906103 := bstep (se 1 (by rfl) ⟨1429577, by rfl⟩ : syracuseStep 1906103 = 2859155) B2859155
theorem B8697289 : Blo 1270453 8697289 := bstep (se 2 (by rfl) ⟨3261483, by rfl⟩ : syracuseStep 8697289 = 6522967) B6522967
theorem B1906139 : Blo 1270453 1906139 := bstep (se 1 (by rfl) ⟨1429604, by rfl⟩ : syracuseStep 1906139 = 2859209) B2859209
theorem B7239131 : Blo 1270453 7239131 := bstep (se 1 (by rfl) ⟨5429348, by rfl⟩ : syracuseStep 7239131 = 10858697) B10858697
theorem B3216905 : Blo 1270453 3216905 := bstep (se 2 (by rfl) ⟨1206339, by rfl⟩ : syracuseStep 3216905 = 2412679) B2412679
theorem B2414099 : Blo 1270453 2414099 := bstep (se 1 (by rfl) ⟨1810574, by rfl⟩ : syracuseStep 2414099 = 3621149) B3621149
theorem B3216935 : Blo 1270453 3216935 := bstep (se 1 (by rfl) ⟨2412701, by rfl⟩ : syracuseStep 3216935 = 4825403) B4825403
theorem B9655847 : Blo 1270453 9655847 := bstep (se 1 (by rfl) ⟨7241885, by rfl⟩ : syracuseStep 9655847 = 14483771) B14483771
theorem B2414137 : Blo 1270453 2414137 := bstep (se 2 (by rfl) ⟨905301, by rfl⟩ : syracuseStep 2414137 = 1810603) B1810603
theorem B2414441 : Blo 1270453 2414441 := bstep (se 2 (by rfl) ⟨905415, by rfl⟩ : syracuseStep 2414441 = 1810831) B1810831
theorem B3217259 : Blo 1270453 3217259 := bstep (se 1 (by rfl) ⟨2412944, by rfl⟩ : syracuseStep 3217259 = 4825889) B4825889
theorem B1906607 : Blo 1270453 1906607 := bstep (se 1 (by rfl) ⟨1429955, by rfl⟩ : syracuseStep 1906607 = 2859911) B2859911
theorem B5224367 : Blo 1270453 5224367 := bstep (se 1 (by rfl) ⟨3918275, by rfl⟩ : syracuseStep 5224367 = 7836551) B7836551
theorem B1906697 : Blo 1270453 1906697 := bstep (se 2 (by rfl) ⟨715011, by rfl⟩ : syracuseStep 1906697 = 1430023) B1430023
theorem B1906727 : Blo 1270453 1906727 := bstep (se 1 (by rfl) ⟨1430045, by rfl⟩ : syracuseStep 1906727 = 2860091) B2860091
theorem B1906811 : Blo 1270453 1906811 := bstep (se 1 (by rfl) ⟨1430108, by rfl⟩ : syracuseStep 1906811 = 2860217) B2860217
theorem B4290731 : Blo 1270453 4290731 := bstep (se 1 (by rfl) ⟨3218048, by rfl⟩ : syracuseStep 4290731 = 6436097) B6436097
theorem B1906937 : Blo 1270453 1906937 := bstep (se 2 (by rfl) ⟨715101, by rfl⟩ : syracuseStep 1906937 = 1430203) B1430203
theorem B1907039 : Blo 1270453 1907039 := bstep (se 1 (by rfl) ⟨1430279, by rfl⟩ : syracuseStep 1907039 = 2860559) B2860559
theorem B1907051 : Blo 1270453 1907051 := bstep (se 1 (by rfl) ⟨1430288, by rfl⟩ : syracuseStep 1907051 = 2860577) B2860577
theorem B3619201 : Blo 1270453 3619201 := bstep (se 2 (by rfl) ⟨1357200, by rfl⟩ : syracuseStep 3619201 = 2714401) B2714401
theorem B2144731 : Blo 1270453 2144731 := bstep (se 1 (by rfl) ⟨1608548, by rfl⟩ : syracuseStep 2144731 = 3217097) B3217097
theorem B3217907 : Blo 1270453 3217907 := bstep (se 1 (by rfl) ⟨2413430, by rfl⟩ : syracuseStep 3217907 = 4826861) B4826861
theorem B1907279 : Blo 1270453 1907279 := bstep (se 1 (by rfl) ⟨1430459, by rfl⟩ : syracuseStep 1907279 = 2860919) B2860919
theorem B4291271 : Blo 1270453 4291271 := bstep (se 1 (by rfl) ⟨3218453, by rfl⟩ : syracuseStep 4291271 = 6436907) B6436907
theorem B1907399 : Blo 1270453 1907399 := bstep (se 1 (by rfl) ⟨1430549, by rfl⟩ : syracuseStep 1907399 = 2861099) B2861099
theorem B1809145 : Blo 1270453 1809145 := bstep (se 2 (by rfl) ⟨678429, by rfl⟩ : syracuseStep 1809145 = 1356859) B1356859
theorem B1907561 : Blo 1270453 1907561 := bstep (se 2 (by rfl) ⟨715335, by rfl⟩ : syracuseStep 1907561 = 1430671) B1430671
theorem B3619691 : Blo 1270453 3619691 := bstep (se 1 (by rfl) ⟨2714768, by rfl⟩ : syracuseStep 3619691 = 5429537) B5429537
theorem B9649043 : Blo 1270453 9649043 := bstep (se 1 (by rfl) ⟨7236782, by rfl⟩ : syracuseStep 9649043 = 14473565) B14473565
theorem B1907639 : Blo 1270453 1907639 := bstep (se 1 (by rfl) ⟨1430729, by rfl⟩ : syracuseStep 1907639 = 2861459) B2861459
theorem B3218363 : Blo 1270453 3218363 := bstep (se 1 (by rfl) ⟨2413772, by rfl⟩ : syracuseStep 3218363 = 4827545) B4827545
theorem B1907675 : Blo 1270453 1907675 := bstep (se 1 (by rfl) ⟨1430756, by rfl⟩ : syracuseStep 1907675 = 2861513) B2861513
theorem B2063369 : Blo 1270453 2063369 := bstep (se 2 (by rfl) ⟨773763, by rfl⟩ : syracuseStep 2063369 = 1547527) B1547527
theorem B11590735 : Blo 1270453 11590735 := bstep (se 1 (by rfl) ⟨8693051, by rfl⟩ : syracuseStep 11590735 = 17386103) B17386103
theorem B4824143 : Blo 1270453 4824143 := bstep (se 1 (by rfl) ⟨3618107, by rfl⟩ : syracuseStep 4824143 = 7236215) B7236215
theorem B2145359 : Blo 1270453 2145359 := bstep (se 1 (by rfl) ⟨1609019, by rfl⟩ : syracuseStep 2145359 = 3218039) B3218039
theorem B6438041 : Blo 1270453 6438041 := bstep (se 2 (by rfl) ⟨2414265, by rfl⟩ : syracuseStep 6438041 = 4828531) B4828531
theorem B4136107 : Blo 1270453 4136107 := bstep (se 1 (by rfl) ⟨3102080, by rfl⟩ : syracuseStep 4136107 = 6204161) B6204161
theorem B6446479 : Blo 1270453 6446479 := bstep (se 1 (by rfl) ⟨4834859, by rfl⟩ : syracuseStep 6446479 = 9669719) B9669719
theorem B9158131 : Blo 1270453 9158131 := bstep (se 1 (by rfl) ⟨6868598, by rfl⟩ : syracuseStep 9158131 = 13737197) B13737197
theorem B4292135 : Blo 1270453 4292135 := bstep (se 1 (by rfl) ⟨3219101, by rfl⟩ : syracuseStep 4292135 = 6438203) B6438203
theorem B3219041 : Blo 1270453 3219041 := bstep (se 2 (by rfl) ⟨1207140, by rfl⟩ : syracuseStep 3219041 = 2414281) B2414281
theorem B7241339 : Blo 1270453 7241339 := bstep (se 1 (by rfl) ⟨5431004, by rfl⟩ : syracuseStep 7241339 = 10862009) B10862009
theorem B15679109 : Blo 1270453 15679109 := bstep (se 4 (by rfl) ⟨1469916, by rfl⟩ : syracuseStep 15679109 = 2939833) B2939833
theorem B4292243 : Blo 1270453 4292243 := bstep (se 1 (by rfl) ⟨3219182, by rfl⟩ : syracuseStep 4292243 = 6438365) B6438365
theorem B2899655 : Blo 1270453 2899655 := bstep (se 1 (by rfl) ⟨2174741, by rfl⟩ : syracuseStep 2899655 = 4349483) B4349483
theorem B9650015 : Blo 1270453 9650015 := bstep (se 1 (by rfl) ⟨7237511, by rfl⟩ : syracuseStep 9650015 = 14475023) B14475023
theorem B4292459 : Blo 1270453 4292459 := bstep (se 1 (by rfl) ⟨3219344, by rfl⟩ : syracuseStep 4292459 = 6438689) B6438689
theorem B11009927 : Blo 1270453 11009927 := bstep (se 1 (by rfl) ⟨8257445, by rfl⟩ : syracuseStep 11009927 = 16514891) B16514891
theorem B4292513 : Blo 1270453 4292513 := bstep (se 2 (by rfl) ⟨1609692, by rfl⟩ : syracuseStep 4292513 = 3219385) B3219385
theorem B2146223 : Blo 1270453 2146223 := bstep (se 1 (by rfl) ⟨1609667, by rfl⟩ : syracuseStep 2146223 = 3219335) B3219335
theorem B2858939 : Blo 1270453 2858939 := bstep (se 1 (by rfl) ⟨2144204, by rfl⟩ : syracuseStep 2858939 = 4288409) B4288409
theorem B2859371 : Blo 1270453 2859371 := bstep (se 1 (by rfl) ⟨2144528, by rfl⟩ : syracuseStep 2859371 = 4289057) B4289057
theorem B2859515 : Blo 1270453 2859515 := bstep (se 1 (by rfl) ⟨2144636, by rfl⟩ : syracuseStep 2859515 = 4289273) B4289273
theorem B1810939 : Blo 1270453 1810939 := bstep (se 1 (by rfl) ⟨1358204, by rfl⟩ : syracuseStep 1810939 = 2716409) B2716409
theorem B4825601 : Blo 1270453 4825601 := bstep (se 2 (by rfl) ⟨1809600, by rfl⟩ : syracuseStep 4825601 = 3619201) B3619201
theorem B2859641 : Blo 1270453 2859641 := bstep (se 2 (by rfl) ⟨1072365, by rfl⟩ : syracuseStep 2859641 = 2144731) B2144731
theorem B5431961 : Blo 1270453 5431961 := bstep (se 2 (by rfl) ⟨2036985, by rfl⟩ : syracuseStep 5431961 = 4073971) B4073971
theorem B2859695 : Blo 1270453 2859695 := bstep (se 1 (by rfl) ⟨2144771, by rfl⟩ : syracuseStep 2859695 = 4289543) B4289543
theorem B6193847 : Blo 1270453 6193847 := bstep (se 1 (by rfl) ⟨4645385, by rfl⟩ : syracuseStep 6193847 = 9290771) B9290771
theorem B1270495 : Blo 1270453 1270495 := bstep (se 1 (by rfl) ⟨952871, by rfl⟩ : syracuseStep 1270495 = 1905743) B1905743
theorem B2859767 : Blo 1270453 2859767 := bstep (se 1 (by rfl) ⟨2144825, by rfl⟩ : syracuseStep 2859767 = 4289651) B4289651
theorem B1270575 : Blo 1270453 1270575 := bstep (se 1 (by rfl) ⟨952931, by rfl⟩ : syracuseStep 1270575 = 1905863) B1905863
theorem B1270683 : Blo 1270453 1270683 := bstep (se 1 (by rfl) ⟨953012, by rfl⟩ : syracuseStep 1270683 = 1906025) B1906025
theorem B2859947 : Blo 1270453 2859947 := bstep (se 1 (by rfl) ⟨2144960, by rfl⟩ : syracuseStep 2859947 = 4289921) B4289921
theorem B1270735 : Blo 1270453 1270735 := bstep (se 1 (by rfl) ⟨953051, by rfl⟩ : syracuseStep 1270735 = 1906103) B1906103
theorem B1270759 : Blo 1270453 1270759 := bstep (se 1 (by rfl) ⟨953069, by rfl⟩ : syracuseStep 1270759 = 1906139) B1906139
theorem B4826087 : Blo 1270453 4826087 := bstep (se 1 (by rfl) ⟨3619565, by rfl⟩ : syracuseStep 4826087 = 7239131) B7239131
theorem B14476481 : Blo 1270453 14476481 := bstep (se 2 (by rfl) ⟨5428680, by rfl⟩ : syracuseStep 14476481 = 10857361) B10857361
theorem B1271071 : Blo 1270453 1271071 := bstep (se 1 (by rfl) ⟨953303, by rfl⟩ : syracuseStep 1271071 = 1906607) B1906607
theorem B3482911 : Blo 1270453 3482911 := bstep (se 1 (by rfl) ⟨2612183, by rfl⟩ : syracuseStep 3482911 = 5224367) B5224367
theorem B1271131 : Blo 1270453 1271131 := bstep (se 1 (by rfl) ⟨953348, by rfl⟩ : syracuseStep 1271131 = 1906697) B1906697
theorem B3261791 : Blo 1270453 3261791 := bstep (se 1 (by rfl) ⟨2446343, by rfl⟩ : syracuseStep 3261791 = 4892687) B4892687
theorem B1271151 : Blo 1270453 1271151 := bstep (se 1 (by rfl) ⟨953363, by rfl⟩ : syracuseStep 1271151 = 1906727) B1906727
theorem B9168281 : Blo 1270453 9168281 := bstep (se 2 (by rfl) ⟨3438105, by rfl⟩ : syracuseStep 9168281 = 6876211) B6876211
theorem B1271207 : Blo 1270453 1271207 := bstep (se 1 (by rfl) ⟨953405, by rfl⟩ : syracuseStep 1271207 = 1906811) B1906811
theorem B2860487 : Blo 1270453 2860487 := bstep (se 1 (by rfl) ⟨2145365, by rfl⟩ : syracuseStep 2860487 = 4290731) B4290731
theorem B1271291 : Blo 1270453 1271291 := bstep (se 1 (by rfl) ⟨953468, by rfl⟩ : syracuseStep 1271291 = 1906937) B1906937
theorem B12224033 : Blo 1270453 12224033 := bstep (se 2 (by rfl) ⟨4584012, by rfl⟩ : syracuseStep 12224033 = 9168025) B9168025
theorem B5514809 : Blo 1270453 5514809 := bstep (se 2 (by rfl) ⟨2068053, by rfl⟩ : syracuseStep 5514809 = 4136107) B4136107
theorem B1271359 : Blo 1270453 1271359 := bstep (se 1 (by rfl) ⟨953519, by rfl⟩ : syracuseStep 1271359 = 1907039) B1907039
theorem B1271367 : Blo 1270453 1271367 := bstep (se 1 (by rfl) ⟨953525, by rfl⟩ : syracuseStep 1271367 = 1907051) B1907051
theorem B1271519 : Blo 1270453 1271519 := bstep (se 1 (by rfl) ⟨953639, by rfl⟩ : syracuseStep 1271519 = 1907279) B1907279
theorem B2860847 : Blo 1270453 2860847 := bstep (se 1 (by rfl) ⟨2145635, by rfl⟩ : syracuseStep 2860847 = 4291271) B4291271
theorem B1271599 : Blo 1270453 1271599 := bstep (se 1 (by rfl) ⟨953699, by rfl⟩ : syracuseStep 1271599 = 1907399) B1907399
theorem B8251217 : Blo 1270453 8251217 := bstep (se 2 (by rfl) ⟨3094206, by rfl⟩ : syracuseStep 8251217 = 6188413) B6188413
theorem B8595305 : Blo 1270453 8595305 := bstep (se 2 (by rfl) ⟨3223239, by rfl⟩ : syracuseStep 8595305 = 6446479) B6446479
theorem B1271707 : Blo 1270453 1271707 := bstep (se 1 (by rfl) ⟨953780, by rfl⟩ : syracuseStep 1271707 = 1907561) B1907561
theorem B6432695 : Blo 1270453 6432695 := bstep (se 1 (by rfl) ⟨4824521, by rfl⟩ : syracuseStep 6432695 = 9649043) B9649043
theorem B1271759 : Blo 1270453 1271759 := bstep (se 1 (by rfl) ⟨953819, by rfl⟩ : syracuseStep 1271759 = 1907639) B1907639
theorem B1271783 : Blo 1270453 1271783 := bstep (se 1 (by rfl) ⟨953837, by rfl⟩ : syracuseStep 1271783 = 1907675) B1907675
theorem B200869895 : Blo 1270453 200869895 := bstep (se 1 (by rfl) ⟨150652421, by rfl⟩ : syracuseStep 200869895 = 301304843) B301304843
theorem B2861423 : Blo 1270453 2861423 := bstep (se 1 (by rfl) ⟨2146067, by rfl⟩ : syracuseStep 2861423 = 4292135) B4292135
theorem B1608103 : Blo 1270453 1608103 := bstep (se 1 (by rfl) ⟨1206077, by rfl⟩ : syracuseStep 1608103 = 2412155) B2412155
theorem B4827559 : Blo 1270453 4827559 := bstep (se 1 (by rfl) ⟨3620669, by rfl⟩ : syracuseStep 4827559 = 7241339) B7241339
theorem B2861495 : Blo 1270453 2861495 := bstep (se 1 (by rfl) ⟨2146121, by rfl⟩ : syracuseStep 2861495 = 4292243) B4292243
theorem B6433343 : Blo 1270453 6433343 := bstep (se 1 (by rfl) ⟨4825007, by rfl⟩ : syracuseStep 6433343 = 9650015) B9650015
theorem B2861639 : Blo 1270453 2861639 := bstep (se 1 (by rfl) ⟨2146229, by rfl⟩ : syracuseStep 2861639 = 4292459) B4292459
theorem B2861675 : Blo 1270453 2861675 := bstep (se 1 (by rfl) ⟨2146256, by rfl⟩ : syracuseStep 2861675 = 4292513) B4292513
theorem B1608427 : Blo 1270453 1608427 := bstep (se 1 (by rfl) ⟨1206320, by rfl⟩ : syracuseStep 1608427 = 2412641) B2412641
theorem B1608655 : Blo 1270453 1608655 := bstep (se 1 (by rfl) ⟨1206491, by rfl⟩ : syracuseStep 1608655 = 2412983) B2412983
theorem B7236647 : Blo 1270453 7236647 := bstep (se 1 (by rfl) ⟨5427485, by rfl⟩ : syracuseStep 7236647 = 10854971) B10854971
theorem B4828349 : Blo 1270453 4828349 := bstep (se 3 (by rfl) ⟨905315, by rfl⟩ : syracuseStep 4828349 = 1810631) B1810631
theorem B1608923 : Blo 1270453 1608923 := bstep (se 1 (by rfl) ⟨1206692, by rfl⟩ : syracuseStep 1608923 = 2413385) B2413385
theorem B4074715 : Blo 1270453 4074715 := bstep (se 1 (by rfl) ⟨3056036, by rfl⟩ : syracuseStep 4074715 = 6112073) B6112073
theorem B111742267 : Blo 1270453 111742267 := bstep (se 1 (by rfl) ⟨83806700, by rfl⟩ : syracuseStep 111742267 = 167613401) B167613401
theorem B2412193 : Blo 1270453 2412193 := bstep (se 2 (by rfl) ⟨904572, by rfl⟩ : syracuseStep 2412193 = 1809145) B1809145
theorem B1609399 : Blo 1270453 1609399 := bstep (se 1 (by rfl) ⟨1207049, by rfl⟩ : syracuseStep 1609399 = 2414099) B2414099
theorem B15454061 : Blo 1270453 15454061 := bstep (se 3 (by rfl) ⟨2897636, by rfl⟩ : syracuseStep 15454061 = 5795273) B5795273
theorem B1609627 : Blo 1270453 1609627 := bstep (se 1 (by rfl) ⟨1207220, by rfl⟩ : syracuseStep 1609627 = 2414441) B2414441
theorem B4288571 : Blo 1270453 4288571 := bstep (se 1 (by rfl) ⟨3216428, by rfl⟩ : syracuseStep 4288571 = 6432857) B6432857
theorem B15454313 : Blo 1270453 15454313 := bstep (se 2 (by rfl) ⟨5795367, by rfl⟩ : syracuseStep 15454313 = 11590735) B11590735
theorem B4288841 : Blo 1270453 4288841 := bstep (se 2 (by rfl) ⟨1608315, by rfl⟩ : syracuseStep 4288841 = 3216631) B3216631
theorem B2413127 : Blo 1270453 2413127 := bstep (se 1 (by rfl) ⟨1809845, by rfl⟩ : syracuseStep 2413127 = 3619691) B3619691
theorem B11596385 : Blo 1270453 11596385 := bstep (se 2 (by rfl) ⟨4348644, by rfl⟩ : syracuseStep 11596385 = 8697289) B8697289
theorem B2290283 : Blo 1270453 2290283 := bstep (se 1 (by rfl) ⟨1717712, by rfl⟩ : syracuseStep 2290283 = 3435425) B3435425
theorem B6435449 : Blo 1270453 6435449 := bstep (se 2 (by rfl) ⟨2413293, by rfl⟩ : syracuseStep 6435449 = 4826587) B4826587
theorem B2036345 : Blo 1270453 2036345 := bstep (se 2 (by rfl) ⟨763629, by rfl⟩ : syracuseStep 2036345 = 1527259) B1527259
theorem B12210841 : Blo 1270453 12210841 := bstep (se 2 (by rfl) ⟨4579065, by rfl⟩ : syracuseStep 12210841 = 9158131) B9158131
theorem B6615751 : Blo 1270453 6615751 := bstep (se 1 (by rfl) ⟨4961813, by rfl⟩ : syracuseStep 6615751 = 9923627) B9923627
theorem B3216095 : Blo 1270453 3216095 := bstep (se 1 (by rfl) ⟨2412071, by rfl⟩ : syracuseStep 3216095 = 4824143) B4824143
theorem B1430239 : Blo 1270453 1430239 := bstep (se 1 (by rfl) ⟨1072679, by rfl⟩ : syracuseStep 1430239 = 2145359) B2145359
theorem B42931289 : Blo 1270453 42931289 := bstep (se 2 (by rfl) ⟨16099233, by rfl⟩ : syracuseStep 42931289 = 32198467) B32198467
theorem B1430815 : Blo 1270453 1430815 := bstep (se 1 (by rfl) ⟨1073111, by rfl⟩ : syracuseStep 1430815 = 2146223) B2146223
theorem B1905959 : Blo 1270453 1905959 := bstep (se 1 (by rfl) ⟨1429469, by rfl⟩ : syracuseStep 1905959 = 2858939) B2858939
theorem B1906043 : Blo 1270453 1906043 := bstep (se 1 (by rfl) ⟨1429532, by rfl⟩ : syracuseStep 1906043 = 2859065) B2859065
theorem B3618209 : Blo 1270453 3618209 := bstep (se 2 (by rfl) ⟨1356828, by rfl⟩ : syracuseStep 3618209 = 2713657) B2713657
theorem B1906169 : Blo 1270453 1906169 := bstep (se 2 (by rfl) ⟨714813, by rfl⟩ : syracuseStep 1906169 = 1429627) B1429627
theorem B1906271 : Blo 1270453 1906271 := bstep (se 1 (by rfl) ⟨1429703, by rfl⟩ : syracuseStep 1906271 = 2859407) B2859407
theorem B26449669 : Blo 1270453 26449669 := bstep (se 4 (by rfl) ⟨2479656, by rfl⟩ : syracuseStep 26449669 = 4959313) B4959313
theorem B1906487 : Blo 1270453 1906487 := bstep (se 1 (by rfl) ⟨1429865, by rfl⟩ : syracuseStep 1906487 = 2859731) B2859731
theorem B3618665 : Blo 1270453 3618665 := bstep (se 2 (by rfl) ⟨1356999, by rfl⟩ : syracuseStep 3618665 = 2713999) B2713999
theorem B26089397 : Blo 1270453 26089397 := bstep (se 5 (by rfl) ⟨1222940, by rfl⟩ : syracuseStep 26089397 = 2445881) B2445881
theorem B6109111 : Blo 1270453 6109111 := bstep (se 1 (by rfl) ⟨4581833, by rfl⟩ : syracuseStep 6109111 = 9163667) B9163667
theorem B13752251 : Blo 1270453 13752251 := bstep (se 1 (by rfl) ⟨10314188, by rfl⟩ : syracuseStep 13752251 = 20628377) B20628377
theorem B1906793 : Blo 1270453 1906793 := bstep (se 2 (by rfl) ⟨715047, by rfl⟩ : syracuseStep 1906793 = 1430095) B1430095
theorem B5429501 : Blo 1270453 5429501 := bstep (se 3 (by rfl) ⟨1018031, by rfl⟩ : syracuseStep 5429501 = 2036063) B2036063
theorem B2144603 : Blo 1270453 2144603 := bstep (se 1 (by rfl) ⟨1608452, by rfl⟩ : syracuseStep 2144603 = 3216905) B3216905
theorem B2144623 : Blo 1270453 2144623 := bstep (se 1 (by rfl) ⟨1608467, by rfl⟩ : syracuseStep 2144623 = 3216935) B3216935
theorem B6437231 : Blo 1270453 6437231 := bstep (se 1 (by rfl) ⟨4827923, by rfl⟩ : syracuseStep 6437231 = 9655847) B9655847
theorem B1907111 : Blo 1270453 1907111 := bstep (se 1 (by rfl) ⟨1430333, by rfl⟩ : syracuseStep 1907111 = 2860667) B2860667
theorem B6109613 : Blo 1270453 6109613 := bstep (se 3 (by rfl) ⟨1145552, by rfl⟩ : syracuseStep 6109613 = 2291105) B2291105
theorem B1907195 : Blo 1270453 1907195 := bstep (se 1 (by rfl) ⟨1430396, by rfl⟩ : syracuseStep 1907195 = 2860793) B2860793
theorem B2144839 : Blo 1270453 2144839 := bstep (se 1 (by rfl) ⟨1608629, by rfl⟩ : syracuseStep 2144839 = 3217259) B3217259
theorem B1907321 : Blo 1270453 1907321 := bstep (se 2 (by rfl) ⟨715245, by rfl⟩ : syracuseStep 1907321 = 1430491) B1430491
theorem B1907375 : Blo 1270453 1907375 := bstep (se 1 (by rfl) ⟨1430531, by rfl⟩ : syracuseStep 1907375 = 2861063) B2861063
theorem B1907423 : Blo 1270453 1907423 := bstep (se 1 (by rfl) ⟨1430567, by rfl⟩ : syracuseStep 1907423 = 2861135) B2861135
theorem B1907687 : Blo 1270453 1907687 := bstep (se 1 (by rfl) ⟨1430765, by rfl⟩ : syracuseStep 1907687 = 2861531) B2861531
theorem B2145271 : Blo 1270453 2145271 := bstep (se 1 (by rfl) ⟨1608953, by rfl⟩ : syracuseStep 2145271 = 3217907) B3217907
theorem B3218555 : Blo 1270453 3218555 := bstep (se 1 (by rfl) ⟨2413916, by rfl⟩ : syracuseStep 3218555 = 4827833) B4827833
theorem B3218575 : Blo 1270453 3218575 := bstep (se 1 (by rfl) ⟨2413931, by rfl⟩ : syracuseStep 3218575 = 4827863) B4827863
theorem B2145575 : Blo 1270453 2145575 := bstep (se 1 (by rfl) ⟨1609181, by rfl⟩ : syracuseStep 2145575 = 3218363) B3218363
theorem B1375579 : Blo 1270453 1375579 := bstep (se 1 (by rfl) ⟨1031684, by rfl⟩ : syracuseStep 1375579 = 2063369) B2063369
theorem B3218849 : Blo 1270453 3218849 := bstep (se 2 (by rfl) ⟨1207068, by rfl⟩ : syracuseStep 3218849 = 2414137) B2414137
theorem B4292027 : Blo 1270453 4292027 := bstep (se 1 (by rfl) ⟨3219020, by rfl⟩ : syracuseStep 4292027 = 6438041) B6438041
theorem B2858579 : Blo 1270453 2858579 := bstep (se 1 (by rfl) ⟨2143934, by rfl⟩ : syracuseStep 2858579 = 4287869) B4287869
theorem B1629931 : Blo 1270453 1629931 := bstep (se 1 (by rfl) ⟨1222448, by rfl⟩ : syracuseStep 1629931 = 2444897) B2444897
theorem B2146027 : Blo 1270453 2146027 := bstep (se 1 (by rfl) ⟨1609520, by rfl⟩ : syracuseStep 2146027 = 3219041) B3219041
theorem B10452739 : Blo 1270453 10452739 := bstep (se 1 (by rfl) ⟨7839554, by rfl⟩ : syracuseStep 10452739 = 15679109) B15679109
theorem B2858759 : Blo 1270453 2858759 := bstep (se 1 (by rfl) ⟨2144069, by rfl⟩ : syracuseStep 2858759 = 4288139) B4288139
theorem B1933103 : Blo 1270453 1933103 := bstep (se 1 (by rfl) ⟨1449827, by rfl⟩ : syracuseStep 1933103 = 2899655) B2899655
theorem B7339951 : Blo 1270453 7339951 := bstep (se 1 (by rfl) ⟨5504963, by rfl⟩ : syracuseStep 7339951 = 11009927) B11009927
theorem B1449959 : Blo 1270453 1449959 := bstep (se 1 (by rfl) ⟨1087469, by rfl⟩ : syracuseStep 1449959 = 2174939) B2174939
theorem B2859047 : Blo 1270453 2859047 := bstep (se 1 (by rfl) ⟨2144285, by rfl⟩ : syracuseStep 2859047 = 4288571) B4288571
theorem B2859227 : Blo 1270453 2859227 := bstep (se 1 (by rfl) ⟨2144420, by rfl⟩ : syracuseStep 2859227 = 4288841) B4288841
theorem B4129231 : Blo 1270453 4129231 := bstep (se 1 (by rfl) ⟨3096923, by rfl⟩ : syracuseStep 4129231 = 6193847) B6193847
theorem B2859497 : Blo 1270453 2859497 := bstep (se 2 (by rfl) ⟨1072311, by rfl⟩ : syracuseStep 2859497 = 2144623) B2144623
theorem B2859785 : Blo 1270453 2859785 := bstep (se 2 (by rfl) ⟨1072419, by rfl⟩ : syracuseStep 2859785 = 2144839) B2144839
theorem B9650987 : Blo 1270453 9650987 := bstep (se 1 (by rfl) ⟨7238240, by rfl⟩ : syracuseStep 9650987 = 14476481) B14476481
theorem B1270639 : Blo 1270453 1270639 := bstep (se 1 (by rfl) ⟨952979, by rfl⟩ : syracuseStep 1270639 = 1905959) B1905959
theorem B1270695 : Blo 1270453 1270695 := bstep (se 1 (by rfl) ⟨953021, by rfl⟩ : syracuseStep 1270695 = 1906043) B1906043
theorem B6112187 : Blo 1270453 6112187 := bstep (se 1 (by rfl) ⟨4584140, by rfl⟩ : syracuseStep 6112187 = 9168281) B9168281
theorem B1270779 : Blo 1270453 1270779 := bstep (se 1 (by rfl) ⟨953084, by rfl⟩ : syracuseStep 1270779 = 1906169) B1906169
theorem B1270847 : Blo 1270453 1270847 := bstep (se 1 (by rfl) ⟨953135, by rfl⟩ : syracuseStep 1270847 = 1906271) B1906271
theorem B1270991 : Blo 1270453 1270991 := bstep (se 1 (by rfl) ⟨953243, by rfl⟩ : syracuseStep 1270991 = 1906487) B1906487
theorem B17392931 : Blo 1270453 17392931 := bstep (se 1 (by rfl) ⟨13044698, by rfl⟩ : syracuseStep 17392931 = 26089397) B26089397
theorem B9168167 : Blo 1270453 9168167 := bstep (se 1 (by rfl) ⟨6876125, by rfl⟩ : syracuseStep 9168167 = 13752251) B13752251
theorem B2860361 : Blo 1270453 2860361 := bstep (se 2 (by rfl) ⟨1072635, by rfl⟩ : syracuseStep 2860361 = 2145271) B2145271
theorem B1271195 : Blo 1270453 1271195 := bstep (se 1 (by rfl) ⟨953396, by rfl⟩ : syracuseStep 1271195 = 1906793) B1906793
theorem B1271407 : Blo 1270453 1271407 := bstep (se 1 (by rfl) ⟨953555, by rfl⟩ : syracuseStep 1271407 = 1907111) B1907111
theorem B4073075 : Blo 1270453 4073075 := bstep (se 1 (by rfl) ⟨3054806, by rfl⟩ : syracuseStep 4073075 = 6109613) B6109613
theorem B5432953 : Blo 1270453 5432953 := bstep (se 2 (by rfl) ⟨2037357, by rfl⟩ : syracuseStep 5432953 = 4074715) B4074715
theorem B1271463 : Blo 1270453 1271463 := bstep (se 1 (by rfl) ⟨953597, by rfl⟩ : syracuseStep 1271463 = 1907195) B1907195
theorem B14485229 : Blo 1270453 14485229 := bstep (se 3 (by rfl) ⟨2715980, by rfl⟩ : syracuseStep 14485229 = 5431961) B5431961
theorem B1271547 : Blo 1270453 1271547 := bstep (se 1 (by rfl) ⟨953660, by rfl⟩ : syracuseStep 1271547 = 1907321) B1907321
theorem B148989689 : Blo 1270453 148989689 := bstep (se 2 (by rfl) ⟨55871133, by rfl⟩ : syracuseStep 148989689 = 111742267) B111742267
theorem B1271583 : Blo 1270453 1271583 := bstep (se 1 (by rfl) ⟨953687, by rfl⟩ : syracuseStep 1271583 = 1907375) B1907375
theorem B1271615 : Blo 1270453 1271615 := bstep (se 1 (by rfl) ⟨953711, by rfl⟩ : syracuseStep 1271615 = 1907423) B1907423
theorem B1271791 : Blo 1270453 1271791 := bstep (se 1 (by rfl) ⟨953843, by rfl⟩ : syracuseStep 1271791 = 1907687) B1907687
theorem B5154941 : Blo 1270453 5154941 := bstep (se 3 (by rfl) ⟨966551, by rfl⟩ : syracuseStep 5154941 = 1933103) B1933103
theorem B32581925 : Blo 1270453 32581925 := bstep (se 4 (by rfl) ⟨3054555, by rfl⟩ : syracuseStep 32581925 = 6109111) B6109111
theorem B2861351 : Blo 1270453 2861351 := bstep (se 1 (by rfl) ⟨2146013, by rfl⟩ : syracuseStep 2861351 = 4292027) B4292027
theorem B2173241 : Blo 1270453 2173241 := bstep (se 2 (by rfl) ⟨814965, by rfl⟩ : syracuseStep 2173241 = 1629931) B1629931
theorem B2861369 : Blo 1270453 2861369 := bstep (se 2 (by rfl) ⟨1073013, by rfl⟩ : syracuseStep 2861369 = 2146027) B2146027
theorem B13936985 : Blo 1270453 13936985 := bstep (se 2 (by rfl) ⟨5226369, by rfl⟩ : syracuseStep 13936985 = 10452739) B10452739
theorem B1608751 : Blo 1270453 1608751 := bstep (se 1 (by rfl) ⟨1206563, by rfl⟩ : syracuseStep 1608751 = 2413127) B2413127
theorem B1526855 : Blo 1270453 1526855 := bstep (se 1 (by rfl) ⟨1145141, by rfl⟩ : syracuseStep 1526855 = 2290283) B2290283
theorem B16281121 : Blo 1270453 16281121 := bstep (se 2 (by rfl) ⟨6105420, by rfl⟩ : syracuseStep 16281121 = 12210841) B12210841
theorem B5500811 : Blo 1270453 5500811 := bstep (se 1 (by rfl) ⟨4125608, by rfl⟩ : syracuseStep 5500811 = 8251217) B8251217
theorem B5730203 : Blo 1270453 5730203 := bstep (se 1 (by rfl) ⟨4297652, by rfl⟩ : syracuseStep 5730203 = 8595305) B8595305
theorem B2412443 : Blo 1270453 2412443 := bstep (se 1 (by rfl) ⟨1809332, by rfl⟩ : syracuseStep 2412443 = 3618665) B3618665
theorem B4288463 : Blo 1270453 4288463 := bstep (se 1 (by rfl) ⟨3216347, by rfl⟩ : syracuseStep 4288463 = 6432695) B6432695
theorem B1429735 : Blo 1270453 1429735 := bstep (se 1 (by rfl) ⟨1072301, by rfl⟩ : syracuseStep 1429735 = 2144603) B2144603
theorem B4288895 : Blo 1270453 4288895 := bstep (se 1 (by rfl) ⟨3216671, by rfl⟩ : syracuseStep 4288895 = 6433343) B6433343
theorem B7336421 : Blo 1270453 7336421 := bstep (se 4 (by rfl) ⟨687789, by rfl⟩ : syracuseStep 7336421 = 1375579) B1375579
theorem B1430383 : Blo 1270453 1430383 := bstep (se 1 (by rfl) ⟨1072787, by rfl⟩ : syracuseStep 1430383 = 2145575) B2145575
theorem B3216257 : Blo 1270453 3216257 := bstep (se 2 (by rfl) ⟨1206096, by rfl⟩ : syracuseStep 3216257 = 2412193) B2412193
theorem B1905719 : Blo 1270453 1905719 := bstep (se 1 (by rfl) ⟨1429289, by rfl⟩ : syracuseStep 1905719 = 2858579) B2858579
theorem B1905839 : Blo 1270453 1905839 := bstep (se 1 (by rfl) ⟨1429379, by rfl⟩ : syracuseStep 1905839 = 2858759) B2858759
theorem B9786601 : Blo 1270453 9786601 := bstep (se 2 (by rfl) ⟨3669975, by rfl⟩ : syracuseStep 9786601 = 7339951) B7339951
theorem B10302707 : Blo 1270453 10302707 := bstep (se 1 (by rfl) ⟨7727030, by rfl⟩ : syracuseStep 10302707 = 15454061) B15454061
theorem B10302875 : Blo 1270453 10302875 := bstep (se 1 (by rfl) ⟨7727156, by rfl⟩ : syracuseStep 10302875 = 15454313) B15454313
theorem B1906247 : Blo 1270453 1906247 := bstep (se 1 (by rfl) ⟨1429685, by rfl⟩ : syracuseStep 1906247 = 2859371) B2859371
theorem B1906343 : Blo 1270453 1906343 := bstep (se 1 (by rfl) ⟨1429757, by rfl⟩ : syracuseStep 1906343 = 2859515) B2859515
theorem B3217067 : Blo 1270453 3217067 := bstep (se 1 (by rfl) ⟨2412800, by rfl⟩ : syracuseStep 3217067 = 4825601) B4825601
theorem B7730923 : Blo 1270453 7730923 := bstep (se 1 (by rfl) ⟨5798192, by rfl⟩ : syracuseStep 7730923 = 11596385) B11596385
theorem B1906427 : Blo 1270453 1906427 := bstep (se 1 (by rfl) ⟨1429820, by rfl⟩ : syracuseStep 1906427 = 2859641) B2859641
theorem B4290299 : Blo 1270453 4290299 := bstep (se 1 (by rfl) ⟨3217724, by rfl⟩ : syracuseStep 4290299 = 6435449) B6435449
theorem B1906463 : Blo 1270453 1906463 := bstep (se 1 (by rfl) ⟨1429847, by rfl⟩ : syracuseStep 1906463 = 2859695) B2859695
theorem B2144063 : Blo 1270453 2144063 := bstep (se 1 (by rfl) ⟨1608047, by rfl⟩ : syracuseStep 2144063 = 3216095) B3216095
theorem B1906511 : Blo 1270453 1906511 := bstep (se 1 (by rfl) ⟨1429883, by rfl⟩ : syracuseStep 1906511 = 2859767) B2859767
theorem B2144137 : Blo 1270453 2144137 := bstep (se 2 (by rfl) ⟨804051, by rfl⟩ : syracuseStep 2144137 = 1608103) B1608103
theorem B6436745 : Blo 1270453 6436745 := bstep (se 2 (by rfl) ⟨2413779, by rfl⟩ : syracuseStep 6436745 = 4827559) B4827559
theorem B4290461 : Blo 1270453 4290461 := bstep (se 3 (by rfl) ⟨804461, by rfl⟩ : syracuseStep 4290461 = 1608923) B1608923
theorem B58824629 : Blo 1270453 58824629 := bstep (se 5 (by rfl) ⟨2757404, by rfl⟩ : syracuseStep 58824629 = 5514809) B5514809
theorem B1906631 : Blo 1270453 1906631 := bstep (se 1 (by rfl) ⟨1429973, by rfl⟩ : syracuseStep 1906631 = 2859947) B2859947
theorem B3217391 : Blo 1270453 3217391 := bstep (se 1 (by rfl) ⟨2413043, by rfl⟩ : syracuseStep 3217391 = 4826087) B4826087
theorem B2414585 : Blo 1270453 2414585 := bstep (se 2 (by rfl) ⟨905469, by rfl⟩ : syracuseStep 2414585 = 1810939) B1810939
theorem B28620859 : Blo 1270453 28620859 := bstep (se 1 (by rfl) ⟨21465644, by rfl⟩ : syracuseStep 28620859 = 42931289) B42931289
theorem B8698109 : Blo 1270453 8698109 := bstep (se 3 (by rfl) ⟨1630895, by rfl⟩ : syracuseStep 8698109 = 3261791) B3261791
theorem B8821001 : Blo 1270453 8821001 := bstep (se 2 (by rfl) ⟨3307875, by rfl⟩ : syracuseStep 8821001 = 6615751) B6615751
theorem B1906985 : Blo 1270453 1906985 := bstep (se 2 (by rfl) ⟨715119, by rfl⟩ : syracuseStep 1906985 = 1430239) B1430239
theorem B1906991 : Blo 1270453 1906991 := bstep (se 1 (by rfl) ⟨1430243, by rfl⟩ : syracuseStep 1906991 = 2860487) B2860487
theorem B2144569 : Blo 1270453 2144569 := bstep (se 2 (by rfl) ⟨804213, by rfl⟩ : syracuseStep 2144569 = 1608427) B1608427
theorem B8149355 : Blo 1270453 8149355 := bstep (se 1 (by rfl) ⟨6112016, by rfl⟩ : syracuseStep 8149355 = 12224033) B12224033
theorem B9648557 : Blo 1270453 9648557 := bstep (se 3 (by rfl) ⟨1809104, by rfl⟩ : syracuseStep 9648557 = 3618209) B3618209
theorem B1907231 : Blo 1270453 1907231 := bstep (se 1 (by rfl) ⟨1430423, by rfl⟩ : syracuseStep 1907231 = 2860847) B2860847
theorem B2144873 : Blo 1270453 2144873 := bstep (se 2 (by rfl) ⟨804327, by rfl⟩ : syracuseStep 2144873 = 1608655) B1608655
theorem B133913263 : Blo 1270453 133913263 := bstep (se 1 (by rfl) ⟨100434947, by rfl⟩ : syracuseStep 133913263 = 200869895) B200869895
theorem B3619667 : Blo 1270453 3619667 := bstep (se 1 (by rfl) ⟨2714750, by rfl⟩ : syracuseStep 3619667 = 5429501) B5429501
theorem B4291433 : Blo 1270453 4291433 := bstep (se 2 (by rfl) ⟨1609287, by rfl⟩ : syracuseStep 4291433 = 3218575) B3218575
theorem B4291487 : Blo 1270453 4291487 := bstep (se 1 (by rfl) ⟨3218615, by rfl⟩ : syracuseStep 4291487 = 6437231) B6437231
theorem B1907615 : Blo 1270453 1907615 := bstep (se 1 (by rfl) ⟨1430711, by rfl⟩ : syracuseStep 1907615 = 2861423) B2861423
theorem B1907663 : Blo 1270453 1907663 := bstep (se 1 (by rfl) ⟨1430747, by rfl⟩ : syracuseStep 1907663 = 2861495) B2861495
theorem B5430253 : Blo 1270453 5430253 := bstep (se 3 (by rfl) ⟨1018172, by rfl⟩ : syracuseStep 5430253 = 2036345) B2036345
theorem B4643881 : Blo 1270453 4643881 := bstep (se 2 (by rfl) ⟨1741455, by rfl⟩ : syracuseStep 4643881 = 3482911) B3482911
theorem B1907753 : Blo 1270453 1907753 := bstep (se 2 (by rfl) ⟨715407, by rfl⟩ : syracuseStep 1907753 = 1430815) B1430815
theorem B1907759 : Blo 1270453 1907759 := bstep (se 1 (by rfl) ⟨1430819, by rfl⟩ : syracuseStep 1907759 = 2861639) B2861639
theorem B1907783 : Blo 1270453 1907783 := bstep (se 1 (by rfl) ⟨1430837, by rfl⟩ : syracuseStep 1907783 = 2861675) B2861675
theorem B4824431 : Blo 1270453 4824431 := bstep (se 1 (by rfl) ⟨3618323, by rfl⟩ : syracuseStep 4824431 = 7236647) B7236647
theorem B2145703 : Blo 1270453 2145703 := bstep (se 1 (by rfl) ⟨1609277, by rfl⟩ : syracuseStep 2145703 = 3218555) B3218555
theorem B3218899 : Blo 1270453 3218899 := bstep (se 1 (by rfl) ⟨2414174, by rfl⟩ : syracuseStep 3218899 = 4828349) B4828349
theorem B2145865 : Blo 1270453 2145865 := bstep (se 2 (by rfl) ⟨804699, by rfl⟩ : syracuseStep 2145865 = 1609399) B1609399
theorem B2145899 : Blo 1270453 2145899 := bstep (se 1 (by rfl) ⟨1609424, by rfl⟩ : syracuseStep 2145899 = 3218849) B3218849
theorem B35266225 : Blo 1270453 35266225 := bstep (se 2 (by rfl) ⟨13224834, by rfl⟩ : syracuseStep 35266225 = 26449669) B26449669
theorem B2146169 : Blo 1270453 2146169 := bstep (se 2 (by rfl) ⟨804813, by rfl⟩ : syracuseStep 2146169 = 1609627) B1609627
theorem B3866557 : Blo 1270453 3866557 := bstep (se 3 (by rfl) ⟨724979, by rfl⟩ : syracuseStep 3866557 = 1449959) B1449959
theorem B2859263 : Blo 1270453 2859263 := bstep (se 1 (by rfl) ⟨2144447, by rfl⟩ : syracuseStep 2859263 = 4288895) B4288895
theorem B4890947 : Blo 1270453 4890947 := bstep (se 1 (by rfl) ⟨3668210, by rfl⟩ : syracuseStep 4890947 = 7336421) B7336421
theorem B2859425 : Blo 1270453 2859425 := bstep (se 2 (by rfl) ⟨1072284, by rfl⟩ : syracuseStep 2859425 = 2144569) B2144569
theorem B5505641 : Blo 1270453 5505641 := bstep (se 2 (by rfl) ⟨2064615, by rfl⟩ : syracuseStep 5505641 = 4129231) B4129231
theorem B1270479 : Blo 1270453 1270479 := bstep (se 1 (by rfl) ⟨952859, by rfl⟩ : syracuseStep 1270479 = 1905719) B1905719
theorem B16286453 : Blo 1270453 16286453 := bstep (se 5 (by rfl) ⟨763427, by rfl⟩ : syracuseStep 16286453 = 1526855) B1526855
theorem B1270559 : Blo 1270453 1270559 := bstep (se 1 (by rfl) ⟨952919, by rfl⟩ : syracuseStep 1270559 = 1905839) B1905839
theorem B6112111 : Blo 1270453 6112111 := bstep (se 1 (by rfl) ⟨4584083, by rfl⟩ : syracuseStep 6112111 = 9168167) B9168167
theorem B1270831 : Blo 1270453 1270831 := bstep (se 1 (by rfl) ⟨953123, by rfl⟩ : syracuseStep 1270831 = 1906247) B1906247
theorem B1270895 : Blo 1270453 1270895 := bstep (se 1 (by rfl) ⟨953171, by rfl⟩ : syracuseStep 1270895 = 1906343) B1906343
theorem B1270951 : Blo 1270453 1270951 := bstep (se 1 (by rfl) ⟨953213, by rfl⟩ : syracuseStep 1270951 = 1906427) B1906427
theorem B2860199 : Blo 1270453 2860199 := bstep (se 1 (by rfl) ⟨2145149, by rfl⟩ : syracuseStep 2860199 = 4290299) B4290299
theorem B1270975 : Blo 1270453 1270975 := bstep (se 1 (by rfl) ⟨953231, by rfl⟩ : syracuseStep 1270975 = 1906463) B1906463
theorem B1271007 : Blo 1270453 1271007 := bstep (se 1 (by rfl) ⟨953255, by rfl⟩ : syracuseStep 1271007 = 1906511) B1906511
theorem B2860307 : Blo 1270453 2860307 := bstep (se 1 (by rfl) ⟨2145230, by rfl⟩ : syracuseStep 2860307 = 4290461) B4290461
theorem B39216419 : Blo 1270453 39216419 := bstep (se 1 (by rfl) ⟨29412314, by rfl⟩ : syracuseStep 39216419 = 58824629) B58824629
theorem B1271087 : Blo 1270453 1271087 := bstep (se 1 (by rfl) ⟨953315, by rfl⟩ : syracuseStep 1271087 = 1906631) B1906631
theorem B1271323 : Blo 1270453 1271323 := bstep (se 1 (by rfl) ⟨953492, by rfl⟩ : syracuseStep 1271323 = 1906985) B1906985
theorem B1271327 : Blo 1270453 1271327 := bstep (se 1 (by rfl) ⟨953495, by rfl⟩ : syracuseStep 1271327 = 1906991) B1906991
theorem B9291323 : Blo 1270453 9291323 := bstep (se 1 (by rfl) ⟨6968492, by rfl⟩ : syracuseStep 9291323 = 13936985) B13936985
theorem B5432903 : Blo 1270453 5432903 := bstep (se 1 (by rfl) ⟨4074677, by rfl⟩ : syracuseStep 5432903 = 8149355) B8149355
theorem B6432371 : Blo 1270453 6432371 := bstep (se 1 (by rfl) ⟨4824278, by rfl⟩ : syracuseStep 6432371 = 9648557) B9648557
theorem B1271487 : Blo 1270453 1271487 := bstep (se 1 (by rfl) ⟨953615, by rfl⟩ : syracuseStep 1271487 = 1907231) B1907231
theorem B2860937 : Blo 1270453 2860937 := bstep (se 2 (by rfl) ⟨1072851, by rfl⟩ : syracuseStep 2860937 = 2145703) B2145703
theorem B2860955 : Blo 1270453 2860955 := bstep (se 1 (by rfl) ⟨2145716, by rfl⟩ : syracuseStep 2860955 = 4291433) B4291433
theorem B2860991 : Blo 1270453 2860991 := bstep (se 1 (by rfl) ⟨2145743, by rfl⟩ : syracuseStep 2860991 = 4291487) B4291487
theorem B1271743 : Blo 1270453 1271743 := bstep (se 1 (by rfl) ⟨953807, by rfl⟩ : syracuseStep 1271743 = 1907615) B1907615
theorem B1271775 : Blo 1270453 1271775 := bstep (se 1 (by rfl) ⟨953831, by rfl⟩ : syracuseStep 1271775 = 1907663) B1907663
theorem B1271835 : Blo 1270453 1271835 := bstep (se 1 (by rfl) ⟨953876, by rfl⟩ : syracuseStep 1271835 = 1907753) B1907753
theorem B1271839 : Blo 1270453 1271839 := bstep (se 1 (by rfl) ⟨953879, by rfl⟩ : syracuseStep 1271839 = 1907759) B1907759
theorem B1271855 : Blo 1270453 1271855 := bstep (se 1 (by rfl) ⟨953891, by rfl⟩ : syracuseStep 1271855 = 1907783) B1907783
theorem B2861153 : Blo 1270453 2861153 := bstep (se 2 (by rfl) ⟨1072932, by rfl⟩ : syracuseStep 2861153 = 2145865) B2145865
theorem B7243937 : Blo 1270453 7243937 := bstep (se 2 (by rfl) ⟨2716476, by rfl⟩ : syracuseStep 7243937 = 5432953) B5432953
theorem B9652445 : Blo 1270453 9652445 := bstep (se 3 (by rfl) ⟨1809833, by rfl⟩ : syracuseStep 9652445 = 3619667) B3619667
theorem B10307897 : Blo 1270453 10307897 := bstep (se 2 (by rfl) ⟨3865461, by rfl⟩ : syracuseStep 10307897 = 7730923) B7730923
theorem B6433181 : Blo 1270453 6433181 := bstep (se 3 (by rfl) ⟨1206221, by rfl⟩ : syracuseStep 6433181 = 2412443) B2412443
theorem B5155409 : Blo 1270453 5155409 := bstep (se 2 (by rfl) ⟨1933278, by rfl⟩ : syracuseStep 5155409 = 3866557) B3866557
theorem B3820135 : Blo 1270453 3820135 := bstep (se 1 (by rfl) ⟨2865101, by rfl⟩ : syracuseStep 3820135 = 5730203) B5730203
theorem B38161145 : Blo 1270453 38161145 := bstep (se 2 (by rfl) ⟨14310429, by rfl⟩ : syracuseStep 38161145 = 28620859) B28620859
theorem B24767365 : Blo 1270453 24767365 := bstep (se 4 (by rfl) ⟨2321940, by rfl⟩ : syracuseStep 24767365 = 4643881) B4643881
theorem B6433991 : Blo 1270453 6433991 := bstep (se 1 (by rfl) ⟨4825493, by rfl⟩ : syracuseStep 6433991 = 9650987) B9650987
theorem B4074791 : Blo 1270453 4074791 := bstep (se 1 (by rfl) ⟨3056093, by rfl⟩ : syracuseStep 4074791 = 6112187) B6112187
theorem B23194957 : Blo 1270453 23194957 := bstep (se 3 (by rfl) ⟨4349054, by rfl⟩ : syracuseStep 23194957 = 8698109) B8698109
theorem B5795309 : Blo 1270453 5795309 := bstep (se 3 (by rfl) ⟨1086620, by rfl⟩ : syracuseStep 5795309 = 2173241) B2173241
theorem B6868471 : Blo 1270453 6868471 := bstep (se 1 (by rfl) ⟨5151353, by rfl⟩ : syracuseStep 6868471 = 10302707) B10302707
theorem B11595287 : Blo 1270453 11595287 := bstep (se 1 (by rfl) ⟨8696465, by rfl⟩ : syracuseStep 11595287 = 17392931) B17392931
theorem B6868583 : Blo 1270453 6868583 := bstep (se 1 (by rfl) ⟨5151437, by rfl⟩ : syracuseStep 6868583 = 10302875) B10302875
theorem B2715383 : Blo 1270453 2715383 := bstep (se 1 (by rfl) ⟨2036537, by rfl⟩ : syracuseStep 2715383 = 4073075) B4073075
theorem B1429375 : Blo 1270453 1429375 := bstep (se 1 (by rfl) ⟨1072031, by rfl⟩ : syracuseStep 1429375 = 2144063) B2144063
theorem B52195205 : Blo 1270453 52195205 := bstep (se 4 (by rfl) ⟨4893300, by rfl⟩ : syracuseStep 52195205 = 9786601) B9786601
theorem B1609723 : Blo 1270453 1609723 := bstep (se 1 (by rfl) ⟨1207292, by rfl⟩ : syracuseStep 1609723 = 2414585) B2414585
theorem B3436627 : Blo 1270453 3436627 := bstep (se 1 (by rfl) ⟨2577470, by rfl⟩ : syracuseStep 3436627 = 5154941) B5154941
theorem B21721283 : Blo 1270453 21721283 := bstep (se 1 (by rfl) ⟨16290962, by rfl⟩ : syracuseStep 21721283 = 32581925) B32581925
theorem B1429915 : Blo 1270453 1429915 := bstep (se 1 (by rfl) ⟨1072436, by rfl⟩ : syracuseStep 1429915 = 2144873) B2144873
theorem B3216287 : Blo 1270453 3216287 := bstep (se 1 (by rfl) ⟨2412215, by rfl⟩ : syracuseStep 3216287 = 4824431) B4824431
theorem B1430599 : Blo 1270453 1430599 := bstep (se 1 (by rfl) ⟨1072949, by rfl⟩ : syracuseStep 1430599 = 2145899) B2145899
theorem B1430779 : Blo 1270453 1430779 := bstep (se 1 (by rfl) ⟨1073084, by rfl⟩ : syracuseStep 1430779 = 2146169) B2146169
theorem B3667207 : Blo 1270453 3667207 := bstep (se 1 (by rfl) ⟨2750405, by rfl⟩ : syracuseStep 3667207 = 5500811) B5500811
theorem B1906031 : Blo 1270453 1906031 := bstep (se 1 (by rfl) ⟨1429523, by rfl⟩ : syracuseStep 1906031 = 2859047) B2859047
theorem B1906151 : Blo 1270453 1906151 := bstep (se 1 (by rfl) ⟨1429613, by rfl⟩ : syracuseStep 1906151 = 2859227) B2859227
theorem B1906313 : Blo 1270453 1906313 := bstep (se 2 (by rfl) ⟨714867, by rfl⟩ : syracuseStep 1906313 = 1429735) B1429735
theorem B1906331 : Blo 1270453 1906331 := bstep (se 1 (by rfl) ⟨1429748, by rfl⟩ : syracuseStep 1906331 = 2859497) B2859497
theorem B1906523 : Blo 1270453 1906523 := bstep (se 1 (by rfl) ⟨1429892, by rfl⟩ : syracuseStep 1906523 = 2859785) B2859785
theorem B2144171 : Blo 1270453 2144171 := bstep (se 1 (by rfl) ⟨1608128, by rfl⟩ : syracuseStep 2144171 = 3216257) B3216257
theorem B1906907 : Blo 1270453 1906907 := bstep (se 1 (by rfl) ⟨1430180, by rfl⟩ : syracuseStep 1906907 = 2860361) B2860361
theorem B178551017 : Blo 1270453 178551017 := bstep (se 2 (by rfl) ⟨66956631, by rfl⟩ : syracuseStep 178551017 = 133913263) B133913263
theorem B2144711 : Blo 1270453 2144711 := bstep (se 1 (by rfl) ⟨1608533, by rfl⟩ : syracuseStep 2144711 = 3217067) B3217067
theorem B1907177 : Blo 1270453 1907177 := bstep (se 2 (by rfl) ⟨715191, by rfl⟩ : syracuseStep 1907177 = 1430383) B1430383
theorem B9656819 : Blo 1270453 9656819 := bstep (se 1 (by rfl) ⟨7242614, by rfl⟩ : syracuseStep 9656819 = 14485229) B14485229
theorem B99326459 : Blo 1270453 99326459 := bstep (se 1 (by rfl) ⟨74494844, by rfl⟩ : syracuseStep 99326459 = 148989689) B148989689
theorem B4291163 : Blo 1270453 4291163 := bstep (se 1 (by rfl) ⟨3218372, by rfl⟩ : syracuseStep 4291163 = 6436745) B6436745
theorem B7240337 : Blo 1270453 7240337 := bstep (se 2 (by rfl) ⟨2715126, by rfl⟩ : syracuseStep 7240337 = 5430253) B5430253
theorem B2144927 : Blo 1270453 2144927 := bstep (se 1 (by rfl) ⟨1608695, by rfl⟩ : syracuseStep 2144927 = 3217391) B3217391
theorem B2145001 : Blo 1270453 2145001 := bstep (se 2 (by rfl) ⟨804375, by rfl⟩ : syracuseStep 2145001 = 1608751) B1608751
theorem B5880667 : Blo 1270453 5880667 := bstep (se 1 (by rfl) ⟨4410500, by rfl⟩ : syracuseStep 5880667 = 8821001) B8821001
theorem B1907567 : Blo 1270453 1907567 := bstep (se 1 (by rfl) ⟨1430675, by rfl⟩ : syracuseStep 1907567 = 2861351) B2861351
theorem B1907579 : Blo 1270453 1907579 := bstep (se 1 (by rfl) ⟨1430684, by rfl⟩ : syracuseStep 1907579 = 2861369) B2861369
theorem B4291865 : Blo 1270453 4291865 := bstep (se 2 (by rfl) ⟨1609449, by rfl⟩ : syracuseStep 4291865 = 3218899) B3218899
theorem B21708161 : Blo 1270453 21708161 := bstep (se 2 (by rfl) ⟨8140560, by rfl⟩ : syracuseStep 21708161 = 16281121) B16281121
theorem B47021633 : Blo 1270453 47021633 := bstep (se 2 (by rfl) ⟨17633112, by rfl⟩ : syracuseStep 47021633 = 35266225) B35266225
theorem B2858849 : Blo 1270453 2858849 := bstep (se 2 (by rfl) ⟨1072068, by rfl⟩ : syracuseStep 2858849 = 2144137) B2144137
theorem B2858975 : Blo 1270453 2858975 := bstep (se 1 (by rfl) ⟨2144231, by rfl⟩ : syracuseStep 2858975 = 4288463) B4288463
theorem B3670427 : Blo 1270453 3670427 := bstep (se 1 (by rfl) ⟨2752820, by rfl⟩ : syracuseStep 3670427 = 5505641) B5505641
theorem B1270687 : Blo 1270453 1270687 := bstep (se 1 (by rfl) ⟨953015, by rfl⟩ : syracuseStep 1270687 = 1906031) B1906031
theorem B2860001 : Blo 1270453 2860001 := bstep (se 2 (by rfl) ⟨1072500, by rfl⟩ : syracuseStep 2860001 = 2145001) B2145001
theorem B1270767 : Blo 1270453 1270767 := bstep (se 1 (by rfl) ⟨953075, by rfl⟩ : syracuseStep 1270767 = 1906151) B1906151
theorem B6194215 : Blo 1270453 6194215 := bstep (se 1 (by rfl) ⟨4645661, by rfl⟩ : syracuseStep 6194215 = 9291323) B9291323
theorem B3621935 : Blo 1270453 3621935 := bstep (se 1 (by rfl) ⟨2716451, by rfl⟩ : syracuseStep 3621935 = 5432903) B5432903
theorem B1270875 : Blo 1270453 1270875 := bstep (se 1 (by rfl) ⟨953156, by rfl⟩ : syracuseStep 1270875 = 1906313) B1906313
theorem B1270887 : Blo 1270453 1270887 := bstep (se 1 (by rfl) ⟨953165, by rfl⟩ : syracuseStep 1270887 = 1906331) B1906331
theorem B7840889 : Blo 1270453 7840889 := bstep (se 2 (by rfl) ⟨2940333, by rfl⟩ : syracuseStep 7840889 = 5880667) B5880667
theorem B33023153 : Blo 1270453 33023153 := bstep (se 2 (by rfl) ⟨12383682, by rfl⟩ : syracuseStep 33023153 = 24767365) B24767365
theorem B1271015 : Blo 1270453 1271015 := bstep (se 1 (by rfl) ⟨953261, by rfl⟩ : syracuseStep 1271015 = 1906523) B1906523
theorem B1271271 : Blo 1270453 1271271 := bstep (se 1 (by rfl) ⟨953453, by rfl⟩ : syracuseStep 1271271 = 1906907) B1906907
theorem B1271451 : Blo 1270453 1271451 := bstep (se 1 (by rfl) ⟨953588, by rfl⟩ : syracuseStep 1271451 = 1907177) B1907177
theorem B2860775 : Blo 1270453 2860775 := bstep (se 1 (by rfl) ⟨2145581, by rfl⟩ : syracuseStep 2860775 = 4291163) B4291163
theorem B4826891 : Blo 1270453 4826891 := bstep (se 1 (by rfl) ⟨3620168, by rfl⟩ : syracuseStep 4826891 = 7240337) B7240337
theorem B30926609 : Blo 1270453 30926609 := bstep (se 2 (by rfl) ⟨11597478, by rfl⟩ : syracuseStep 30926609 = 23194957) B23194957
theorem B1271711 : Blo 1270453 1271711 := bstep (se 1 (by rfl) ⟨953783, by rfl⟩ : syracuseStep 1271711 = 1907567) B1907567
theorem B1271719 : Blo 1270453 1271719 := bstep (se 1 (by rfl) ⟨953789, by rfl⟩ : syracuseStep 1271719 = 1907579) B1907579
theorem B2861243 : Blo 1270453 2861243 := bstep (se 1 (by rfl) ⟨2145932, by rfl⟩ : syracuseStep 2861243 = 4291865) B4291865
theorem B4582169 : Blo 1270453 4582169 := bstep (se 2 (by rfl) ⟨1718313, by rfl⟩ : syracuseStep 4582169 = 3436627) B3436627
theorem B10857635 : Blo 1270453 10857635 := bstep (se 1 (by rfl) ⟨8143226, by rfl⟩ : syracuseStep 10857635 = 16286453) B16286453
theorem B52170101 : Blo 1270453 52170101 := bstep (se 5 (by rfl) ⟨2445473, by rfl⟩ : syracuseStep 52170101 = 4890947) B4890947
theorem B10866109 : Blo 1270453 10866109 := bstep (se 3 (by rfl) ⟨2037395, by rfl⟩ : syracuseStep 10866109 = 4074791) B4074791
theorem B26144279 : Blo 1270453 26144279 := bstep (se 1 (by rfl) ⟨19608209, by rfl⟩ : syracuseStep 26144279 = 39216419) B39216419
theorem B4288247 : Blo 1270453 4288247 := bstep (se 1 (by rfl) ⟨3216185, by rfl⟩ : syracuseStep 4288247 = 6432371) B6432371
theorem B1429447 : Blo 1270453 1429447 := bstep (se 1 (by rfl) ⟨1072085, by rfl⟩ : syracuseStep 1429447 = 2144171) B2144171
theorem B4829291 : Blo 1270453 4829291 := bstep (se 1 (by rfl) ⟨3621968, by rfl⟩ : syracuseStep 4829291 = 7243937) B7243937
theorem B6434963 : Blo 1270453 6434963 := bstep (se 1 (by rfl) ⟨4826222, by rfl⟩ : syracuseStep 6434963 = 9652445) B9652445
theorem B119034011 : Blo 1270453 119034011 := bstep (se 1 (by rfl) ⟨89275508, by rfl⟩ : syracuseStep 119034011 = 178551017) B178551017
theorem B4288787 : Blo 1270453 4288787 := bstep (se 1 (by rfl) ⟨3216590, by rfl⟩ : syracuseStep 4288787 = 6433181) B6433181
theorem B1429807 : Blo 1270453 1429807 := bstep (se 1 (by rfl) ⟨1072355, by rfl⟩ : syracuseStep 1429807 = 2144711) B2144711
theorem B3436939 : Blo 1270453 3436939 := bstep (se 1 (by rfl) ⟨2577704, by rfl⟩ : syracuseStep 3436939 = 5155409) B5155409
theorem B1429951 : Blo 1270453 1429951 := bstep (se 1 (by rfl) ⟨1072463, by rfl⟩ : syracuseStep 1429951 = 2144927) B2144927
theorem B25440763 : Blo 1270453 25440763 := bstep (se 1 (by rfl) ⟨19080572, by rfl⟩ : syracuseStep 25440763 = 38161145) B38161145
theorem B4289327 : Blo 1270453 4289327 := bstep (se 1 (by rfl) ⟨3216995, by rfl⟩ : syracuseStep 4289327 = 6433991) B6433991
theorem B14472107 : Blo 1270453 14472107 := bstep (se 1 (by rfl) ⟨10854080, by rfl⟩ : syracuseStep 14472107 = 21708161) B21708161
theorem B3863539 : Blo 1270453 3863539 := bstep (se 1 (by rfl) ⟨2897654, by rfl⟩ : syracuseStep 3863539 = 5795309) B5795309
theorem B7730191 : Blo 1270453 7730191 := bstep (se 1 (by rfl) ⟨5797643, by rfl⟩ : syracuseStep 7730191 = 11595287) B11595287
theorem B31347755 : Blo 1270453 31347755 := bstep (se 1 (by rfl) ⟨23510816, by rfl⟩ : syracuseStep 31347755 = 47021633) B47021633
theorem B1905833 : Blo 1270453 1905833 := bstep (se 2 (by rfl) ⟨714687, by rfl⟩ : syracuseStep 1905833 = 1429375) B1429375
theorem B1905899 : Blo 1270453 1905899 := bstep (se 1 (by rfl) ⟨1429424, by rfl⟩ : syracuseStep 1905899 = 2858849) B2858849
theorem B34796803 : Blo 1270453 34796803 := bstep (se 1 (by rfl) ⟨26097602, by rfl⟩ : syracuseStep 34796803 = 52195205) B52195205
theorem B1905983 : Blo 1270453 1905983 := bstep (se 1 (by rfl) ⟨1429487, by rfl⟩ : syracuseStep 1905983 = 2858975) B2858975
theorem B14480855 : Blo 1270453 14480855 := bstep (se 1 (by rfl) ⟨10860641, by rfl⟩ : syracuseStep 14480855 = 21721283) B21721283
theorem B1906175 : Blo 1270453 1906175 := bstep (se 1 (by rfl) ⟨1429631, by rfl⟩ : syracuseStep 1906175 = 2859263) B2859263
theorem B1906283 : Blo 1270453 1906283 := bstep (se 1 (by rfl) ⟨1429712, by rfl⟩ : syracuseStep 1906283 = 2859425) B2859425
theorem B1906553 : Blo 1270453 1906553 := bstep (se 2 (by rfl) ⟨714957, by rfl⟩ : syracuseStep 1906553 = 1429915) B1429915
theorem B2144191 : Blo 1270453 2144191 := bstep (se 1 (by rfl) ⟨1608143, by rfl⟩ : syracuseStep 2144191 = 3216287) B3216287
theorem B1906799 : Blo 1270453 1906799 := bstep (se 1 (by rfl) ⟨1430099, by rfl⟩ : syracuseStep 1906799 = 2860199) B2860199
theorem B5093513 : Blo 1270453 5093513 := bstep (se 2 (by rfl) ⟨1910067, by rfl⟩ : syracuseStep 5093513 = 3820135) B3820135
theorem B1906871 : Blo 1270453 1906871 := bstep (se 1 (by rfl) ⟨1430153, by rfl⟩ : syracuseStep 1906871 = 2860307) B2860307
theorem B8149481 : Blo 1270453 8149481 := bstep (se 2 (by rfl) ⟨3056055, by rfl⟩ : syracuseStep 8149481 = 6112111) B6112111
theorem B1907291 : Blo 1270453 1907291 := bstep (se 1 (by rfl) ⟨1430468, by rfl⟩ : syracuseStep 1907291 = 2860937) B2860937
theorem B1907303 : Blo 1270453 1907303 := bstep (se 1 (by rfl) ⟨1430477, by rfl⟩ : syracuseStep 1907303 = 2860955) B2860955
theorem B1907327 : Blo 1270453 1907327 := bstep (se 1 (by rfl) ⟨1430495, by rfl⟩ : syracuseStep 1907327 = 2860991) B2860991
theorem B264870557 : Blo 1270453 264870557 := bstep (se 3 (by rfl) ⟨49663229, by rfl⟩ : syracuseStep 264870557 = 99326459) B99326459
theorem B1907435 : Blo 1270453 1907435 := bstep (se 1 (by rfl) ⟨1430576, by rfl⟩ : syracuseStep 1907435 = 2861153) B2861153
theorem B1907465 : Blo 1270453 1907465 := bstep (se 2 (by rfl) ⟨715299, by rfl⟩ : syracuseStep 1907465 = 1430599) B1430599
theorem B6871931 : Blo 1270453 6871931 := bstep (se 1 (by rfl) ⟨5153948, by rfl⟩ : syracuseStep 6871931 = 10307897) B10307897
theorem B6437879 : Blo 1270453 6437879 := bstep (se 1 (by rfl) ⟨4828409, by rfl⟩ : syracuseStep 6437879 = 9656819) B9656819
theorem B1907705 : Blo 1270453 1907705 := bstep (se 2 (by rfl) ⟨715389, by rfl⟩ : syracuseStep 1907705 = 1430779) B1430779
theorem B4889609 : Blo 1270453 4889609 := bstep (se 2 (by rfl) ⟨1833603, by rfl⟩ : syracuseStep 4889609 = 3667207) B3667207
theorem B7241021 : Blo 1270453 7241021 := bstep (se 3 (by rfl) ⟨1357691, by rfl⟩ : syracuseStep 7241021 = 2715383) B2715383
theorem B9157961 : Blo 1270453 9157961 := bstep (se 2 (by rfl) ⟨3434235, by rfl⟩ : syracuseStep 9157961 = 6868471) B6868471
theorem B4579055 : Blo 1270453 4579055 := bstep (se 1 (by rfl) ⟨3434291, by rfl⟩ : syracuseStep 4579055 = 6868583) B6868583
theorem B2146297 : Blo 1270453 2146297 := bstep (se 2 (by rfl) ⟨804861, by rfl⟩ : syracuseStep 2146297 = 1609723) B1609723
theorem B3219527 : Blo 1270453 3219527 := bstep (se 1 (by rfl) ⟨2414645, by rfl⟩ : syracuseStep 3219527 = 4829291) B4829291
theorem B79356007 : Blo 1270453 79356007 := bstep (se 1 (by rfl) ⟨59517005, by rfl⟩ : syracuseStep 79356007 = 119034011) B119034011
theorem B2859191 : Blo 1270453 2859191 := bstep (se 1 (by rfl) ⟨2144393, by rfl⟩ : syracuseStep 2859191 = 4288787) B4288787
theorem B2859551 : Blo 1270453 2859551 := bstep (se 1 (by rfl) ⟨2144663, by rfl⟩ : syracuseStep 2859551 = 4289327) B4289327
theorem B20898503 : Blo 1270453 20898503 := bstep (se 1 (by rfl) ⟨15673877, by rfl⟩ : syracuseStep 20898503 = 31347755) B31347755
theorem B5227259 : Blo 1270453 5227259 := bstep (se 1 (by rfl) ⟨3920444, by rfl⟩ : syracuseStep 5227259 = 7840889) B7840889
theorem B1270555 : Blo 1270453 1270555 := bstep (se 1 (by rfl) ⟨952916, by rfl⟩ : syracuseStep 1270555 = 1905833) B1905833
theorem B1270599 : Blo 1270453 1270599 := bstep (se 1 (by rfl) ⟨952949, by rfl⟩ : syracuseStep 1270599 = 1905899) B1905899
theorem B1270655 : Blo 1270453 1270655 := bstep (se 1 (by rfl) ⟨952991, by rfl⟩ : syracuseStep 1270655 = 1905983) B1905983
theorem B1270783 : Blo 1270453 1270783 := bstep (se 1 (by rfl) ⟨953087, by rfl⟩ : syracuseStep 1270783 = 1906175) B1906175
theorem B1270855 : Blo 1270453 1270855 := bstep (se 1 (by rfl) ⟨953141, by rfl⟩ : syracuseStep 1270855 = 1906283) B1906283
theorem B1271035 : Blo 1270453 1271035 := bstep (se 1 (by rfl) ⟨953276, by rfl⟩ : syracuseStep 1271035 = 1906553) B1906553
theorem B10306921 : Blo 1270453 10306921 := bstep (se 2 (by rfl) ⟨3865095, by rfl⟩ : syracuseStep 10306921 = 7730191) B7730191
theorem B1271199 : Blo 1270453 1271199 := bstep (se 1 (by rfl) ⟨953399, by rfl⟩ : syracuseStep 1271199 = 1906799) B1906799
theorem B1271247 : Blo 1270453 1271247 := bstep (se 1 (by rfl) ⟨953435, by rfl⟩ : syracuseStep 1271247 = 1906871) B1906871
theorem B5432987 : Blo 1270453 5432987 := bstep (se 1 (by rfl) ⟨4074740, by rfl⟩ : syracuseStep 5432987 = 8149481) B8149481
theorem B1271527 : Blo 1270453 1271527 := bstep (se 1 (by rfl) ⟨953645, by rfl⟩ : syracuseStep 1271527 = 1907291) B1907291
theorem B1271535 : Blo 1270453 1271535 := bstep (se 1 (by rfl) ⟨953651, by rfl⟩ : syracuseStep 1271535 = 1907303) B1907303
theorem B1271551 : Blo 1270453 1271551 := bstep (se 1 (by rfl) ⟨953663, by rfl⟩ : syracuseStep 1271551 = 1907327) B1907327
theorem B176580371 : Blo 1270453 176580371 := bstep (se 1 (by rfl) ⟨132435278, by rfl⟩ : syracuseStep 176580371 = 264870557) B264870557
theorem B1271623 : Blo 1270453 1271623 := bstep (se 1 (by rfl) ⟨953717, by rfl⟩ : syracuseStep 1271623 = 1907435) B1907435
theorem B1271643 : Blo 1270453 1271643 := bstep (se 1 (by rfl) ⟨953732, by rfl⟩ : syracuseStep 1271643 = 1907465) B1907465
theorem B4581287 : Blo 1270453 4581287 := bstep (se 1 (by rfl) ⟨3435965, by rfl⟩ : syracuseStep 4581287 = 6871931) B6871931
theorem B1271803 : Blo 1270453 1271803 := bstep (se 1 (by rfl) ⟨953852, by rfl⟩ : syracuseStep 1271803 = 1907705) B1907705
theorem B4827347 : Blo 1270453 4827347 := bstep (se 1 (by rfl) ⟨3620510, by rfl⟩ : syracuseStep 4827347 = 7241021) B7241021
theorem B6105307 : Blo 1270453 6105307 := bstep (se 1 (by rfl) ⟨4578980, by rfl⟩ : syracuseStep 6105307 = 9157961) B9157961
theorem B2861729 : Blo 1270453 2861729 := bstep (se 2 (by rfl) ⟨1073148, by rfl⟩ : syracuseStep 2861729 = 2146297) B2146297
theorem B4582585 : Blo 1270453 4582585 := bstep (se 2 (by rfl) ⟨1718469, by rfl⟩ : syracuseStep 4582585 = 3436939) B3436939
theorem B22015435 : Blo 1270453 22015435 := bstep (se 1 (by rfl) ⟨16511576, by rfl⟩ : syracuseStep 22015435 = 33023153) B33023153
theorem B9653903 : Blo 1270453 9653903 := bstep (se 1 (by rfl) ⟨7240427, by rfl⟩ : syracuseStep 9653903 = 14480855) B14480855
theorem B3395675 : Blo 1270453 3395675 := bstep (se 1 (by rfl) ⟨2546756, by rfl⟩ : syracuseStep 3395675 = 5093513) B5093513
theorem B46395737 : Blo 1270453 46395737 := bstep (se 2 (by rfl) ⟨17398401, by rfl⟩ : syracuseStep 46395737 = 34796803) B34796803
theorem B14488145 : Blo 1270453 14488145 := bstep (se 2 (by rfl) ⟨5433054, by rfl⟩ : syracuseStep 14488145 = 10866109) B10866109
theorem B7238423 : Blo 1270453 7238423 := bstep (se 1 (by rfl) ⟨5428817, by rfl⟩ : syracuseStep 7238423 = 10857635) B10857635
theorem B34780067 : Blo 1270453 34780067 := bstep (se 1 (by rfl) ⟨26085050, by rfl⟩ : syracuseStep 34780067 = 52170101) B52170101
theorem B17429519 : Blo 1270453 17429519 := bstep (se 1 (by rfl) ⟨13072139, by rfl⟩ : syracuseStep 17429519 = 26144279) B26144279
theorem B3052703 : Blo 1270453 3052703 := bstep (se 1 (by rfl) ⟨2289527, by rfl⟩ : syracuseStep 3052703 = 4579055) B4579055
theorem B1905929 : Blo 1270453 1905929 := bstep (se 2 (by rfl) ⟨714723, by rfl⟩ : syracuseStep 1905929 = 1429447) B1429447
theorem B4289975 : Blo 1270453 4289975 := bstep (se 1 (by rfl) ⟨3217481, by rfl⟩ : syracuseStep 4289975 = 6434963) B6434963
theorem B33035813 : Blo 1270453 33035813 := bstep (se 4 (by rfl) ⟨3097107, by rfl⟩ : syracuseStep 33035813 = 6194215) B6194215
theorem B1906409 : Blo 1270453 1906409 := bstep (se 2 (by rfl) ⟨714903, by rfl⟩ : syracuseStep 1906409 = 1429807) B1429807
theorem B1906601 : Blo 1270453 1906601 := bstep (se 2 (by rfl) ⟨714975, by rfl⟩ : syracuseStep 1906601 = 1429951) B1429951
theorem B9648071 : Blo 1270453 9648071 := bstep (se 1 (by rfl) ⟨7236053, by rfl⟩ : syracuseStep 9648071 = 14472107) B14472107
theorem B1906667 : Blo 1270453 1906667 := bstep (se 1 (by rfl) ⟨1430000, by rfl⟩ : syracuseStep 1906667 = 2860001) B2860001
theorem B33921017 : Blo 1270453 33921017 := bstep (se 2 (by rfl) ⟨12720381, by rfl⟩ : syracuseStep 33921017 = 25440763) B25440763
theorem B2414623 : Blo 1270453 2414623 := bstep (se 1 (by rfl) ⟨1810967, by rfl⟩ : syracuseStep 2414623 = 3621935) B3621935
theorem B9787805 : Blo 1270453 9787805 := bstep (se 3 (by rfl) ⟨1835213, by rfl⟩ : syracuseStep 9787805 = 3670427) B3670427
theorem B1907183 : Blo 1270453 1907183 := bstep (se 1 (by rfl) ⟨1430387, by rfl⟩ : syracuseStep 1907183 = 2860775) B2860775
theorem B3217927 : Blo 1270453 3217927 := bstep (se 1 (by rfl) ⟨2413445, by rfl⟩ : syracuseStep 3217927 = 4826891) B4826891
theorem B20617739 : Blo 1270453 20617739 := bstep (se 1 (by rfl) ⟨15463304, by rfl⟩ : syracuseStep 20617739 = 30926609) B30926609
theorem B5151385 : Blo 1270453 5151385 := bstep (se 2 (by rfl) ⟨1931769, by rfl⟩ : syracuseStep 5151385 = 3863539) B3863539
theorem B1907495 : Blo 1270453 1907495 := bstep (se 1 (by rfl) ⟨1430621, by rfl⟩ : syracuseStep 1907495 = 2861243) B2861243
theorem B3054779 : Blo 1270453 3054779 := bstep (se 1 (by rfl) ⟨2291084, by rfl⟩ : syracuseStep 3054779 = 4582169) B4582169
theorem B4291919 : Blo 1270453 4291919 := bstep (se 1 (by rfl) ⟨3218939, by rfl⟩ : syracuseStep 4291919 = 6437879) B6437879
theorem B3259739 : Blo 1270453 3259739 := bstep (se 1 (by rfl) ⟨2444804, by rfl⟩ : syracuseStep 3259739 = 4889609) B4889609
theorem B2858831 : Blo 1270453 2858831 := bstep (se 1 (by rfl) ⟨2144123, by rfl⟩ : syracuseStep 2858831 = 4288247) B4288247
theorem B2858921 : Blo 1270453 2858921 := bstep (se 2 (by rfl) ⟨1072095, by rfl⟩ : syracuseStep 2858921 = 2144191) B2144191
theorem B3219497 : Blo 1270453 3219497 := bstep (se 2 (by rfl) ⟨1207311, by rfl⟩ : syracuseStep 3219497 = 2414623) B2414623
theorem B2146351 : Blo 1270453 2146351 := bstep (se 1 (by rfl) ⟨1609763, by rfl⟩ : syracuseStep 2146351 = 3219527) B3219527
theorem B9658763 : Blo 1270453 9658763 := bstep (se 1 (by rfl) ⟨7244072, by rfl⟩ : syracuseStep 9658763 = 14488145) B14488145
theorem B4825615 : Blo 1270453 4825615 := bstep (se 1 (by rfl) ⟨3619211, by rfl⟩ : syracuseStep 4825615 = 7238423) B7238423
theorem B423232037 : Blo 1270453 423232037 := bstep (se 4 (by rfl) ⟨39678003, by rfl⟩ : syracuseStep 423232037 = 79356007) B79356007
theorem B1270619 : Blo 1270453 1270619 := bstep (se 1 (by rfl) ⟨952964, by rfl⟩ : syracuseStep 1270619 = 1905929) B1905929
theorem B2859983 : Blo 1270453 2859983 := bstep (se 1 (by rfl) ⟨2144987, by rfl⟩ : syracuseStep 2859983 = 4289975) B4289975
theorem B3621991 : Blo 1270453 3621991 := bstep (se 1 (by rfl) ⟨2716493, by rfl⟩ : syracuseStep 3621991 = 5432987) B5432987
theorem B1270939 : Blo 1270453 1270939 := bstep (se 1 (by rfl) ⟨953204, by rfl⟩ : syracuseStep 1270939 = 1906409) B1906409
theorem B1271067 : Blo 1270453 1271067 := bstep (se 1 (by rfl) ⟨953300, by rfl⟩ : syracuseStep 1271067 = 1906601) B1906601
theorem B6432047 : Blo 1270453 6432047 := bstep (se 1 (by rfl) ⟨4824035, by rfl⟩ : syracuseStep 6432047 = 9648071) B9648071
theorem B1271111 : Blo 1270453 1271111 := bstep (se 1 (by rfl) ⟨953333, by rfl⟩ : syracuseStep 1271111 = 1906667) B1906667
theorem B1271455 : Blo 1270453 1271455 := bstep (se 1 (by rfl) ⟨953591, by rfl⟩ : syracuseStep 1271455 = 1907183) B1907183
theorem B1271663 : Blo 1270453 1271663 := bstep (se 1 (by rfl) ⟨953747, by rfl⟩ : syracuseStep 1271663 = 1907495) B1907495
theorem B29353913 : Blo 1270453 29353913 := bstep (se 2 (by rfl) ⟨11007717, by rfl⟩ : syracuseStep 29353913 = 22015435) B22015435
theorem B2861279 : Blo 1270453 2861279 := bstep (se 1 (by rfl) ⟨2145959, by rfl⟩ : syracuseStep 2861279 = 4291919) B4291919
theorem B2173159 : Blo 1270453 2173159 := bstep (se 1 (by rfl) ⟨1629869, by rfl⟩ : syracuseStep 2173159 = 3259739) B3259739
theorem B55757429 : Blo 1270453 55757429 := bstep (se 5 (by rfl) ⟨2613629, by rfl⟩ : syracuseStep 55757429 = 5227259) B5227259
theorem B2263783 : Blo 1270453 2263783 := bstep (se 1 (by rfl) ⟨1697837, by rfl⟩ : syracuseStep 2263783 = 3395675) B3395675
theorem B23186711 : Blo 1270453 23186711 := bstep (se 1 (by rfl) ⟨17390033, by rfl⟩ : syracuseStep 23186711 = 34780067) B34780067
theorem B2035135 : Blo 1270453 2035135 := bstep (se 1 (by rfl) ⟨1526351, by rfl⟩ : syracuseStep 2035135 = 3052703) B3052703
theorem B6868513 : Blo 1270453 6868513 := bstep (se 2 (by rfl) ⟨2575692, by rfl⟩ : syracuseStep 6868513 = 5151385) B5151385
theorem B22023875 : Blo 1270453 22023875 := bstep (se 1 (by rfl) ⟨16517906, by rfl⟩ : syracuseStep 22023875 = 33035813) B33035813
theorem B22614011 : Blo 1270453 22614011 := bstep (se 1 (by rfl) ⟨16960508, by rfl⟩ : syracuseStep 22614011 = 33921017) B33921017
theorem B6525203 : Blo 1270453 6525203 := bstep (se 1 (by rfl) ⟨4893902, by rfl⟩ : syracuseStep 6525203 = 9787805) B9787805
theorem B13742561 : Blo 1270453 13742561 := bstep (se 2 (by rfl) ⟨5153460, by rfl⟩ : syracuseStep 13742561 = 10306921) B10306921
theorem B470880989 : Blo 1270453 470880989 := bstep (se 3 (by rfl) ⟨88290185, by rfl⟩ : syracuseStep 470880989 = 176580371) B176580371
theorem B2036519 : Blo 1270453 2036519 := bstep (se 1 (by rfl) ⟨1527389, by rfl⟩ : syracuseStep 2036519 = 3054779) B3054779
theorem B6435935 : Blo 1270453 6435935 := bstep (se 1 (by rfl) ⟨4826951, by rfl⟩ : syracuseStep 6435935 = 9653903) B9653903
theorem B1905887 : Blo 1270453 1905887 := bstep (se 1 (by rfl) ⟨1429415, by rfl⟩ : syracuseStep 1905887 = 2858831) B2858831
theorem B1905947 : Blo 1270453 1905947 := bstep (se 1 (by rfl) ⟨1429460, by rfl⟩ : syracuseStep 1905947 = 2858921) B2858921
theorem B46478717 : Blo 1270453 46478717 := bstep (se 3 (by rfl) ⟨8714759, by rfl⟩ : syracuseStep 46478717 = 17429519) B17429519
theorem B1906127 : Blo 1270453 1906127 := bstep (se 1 (by rfl) ⟨1429595, by rfl⟩ : syracuseStep 1906127 = 2859191) B2859191
theorem B30930491 : Blo 1270453 30930491 := bstep (se 1 (by rfl) ⟨23197868, by rfl⟩ : syracuseStep 30930491 = 46395737) B46395737
theorem B8140409 : Blo 1270453 8140409 := bstep (se 2 (by rfl) ⟨3052653, by rfl⟩ : syracuseStep 8140409 = 6105307) B6105307
theorem B1906367 : Blo 1270453 1906367 := bstep (se 1 (by rfl) ⟨1429775, by rfl⟩ : syracuseStep 1906367 = 2859551) B2859551
theorem B13932335 : Blo 1270453 13932335 := bstep (se 1 (by rfl) ⟨10449251, by rfl⟩ : syracuseStep 13932335 = 20898503) B20898503
theorem B4290569 : Blo 1270453 4290569 := bstep (se 2 (by rfl) ⟨1608963, by rfl⟩ : syracuseStep 4290569 = 3217927) B3217927
theorem B3054191 : Blo 1270453 3054191 := bstep (se 1 (by rfl) ⟨2290643, by rfl⟩ : syracuseStep 3054191 = 4581287) B4581287
theorem B3218231 : Blo 1270453 3218231 := bstep (se 1 (by rfl) ⟨2413673, by rfl⟩ : syracuseStep 3218231 = 4827347) B4827347
theorem B6110113 : Blo 1270453 6110113 := bstep (se 2 (by rfl) ⟨2291292, by rfl⟩ : syracuseStep 6110113 = 4582585) B4582585
theorem B13745159 : Blo 1270453 13745159 := bstep (se 1 (by rfl) ⟨10308869, by rfl⟩ : syracuseStep 13745159 = 20617739) B20617739
theorem B1907819 : Blo 1270453 1907819 := bstep (se 1 (by rfl) ⟨1430864, by rfl⟩ : syracuseStep 1907819 = 2861729) B2861729
theorem B2146331 : Blo 1270453 2146331 := bstep (se 1 (by rfl) ⟨1609748, by rfl⟩ : syracuseStep 2146331 = 3219497) B3219497
theorem B6439175 : Blo 1270453 6439175 := bstep (se 1 (by rfl) ⟨4829381, by rfl⟩ : syracuseStep 6439175 = 9658763) B9658763
theorem B1270591 : Blo 1270453 1270591 := bstep (se 1 (by rfl) ⟨952943, by rfl⟩ : syracuseStep 1270591 = 1905887) B1905887
theorem B1270631 : Blo 1270453 1270631 := bstep (se 1 (by rfl) ⟨952973, by rfl⟩ : syracuseStep 1270631 = 1905947) B1905947
theorem B1270751 : Blo 1270453 1270751 := bstep (se 1 (by rfl) ⟨953063, by rfl⟩ : syracuseStep 1270751 = 1906127) B1906127
theorem B20620327 : Blo 1270453 20620327 := bstep (se 1 (by rfl) ⟨15465245, by rfl⟩ : syracuseStep 20620327 = 30930491) B30930491
theorem B1270911 : Blo 1270453 1270911 := bstep (se 1 (by rfl) ⟨953183, by rfl⟩ : syracuseStep 1270911 = 1906367) B1906367
theorem B2860379 : Blo 1270453 2860379 := bstep (se 1 (by rfl) ⟨2145284, by rfl⟩ : syracuseStep 2860379 = 4290569) B4290569
theorem B8144509 : Blo 1270453 8144509 := bstep (se 3 (by rfl) ⟨1527095, by rfl⟩ : syracuseStep 8144509 = 3054191) B3054191
theorem B2713513 : Blo 1270453 2713513 := bstep (se 2 (by rfl) ⟨1017567, by rfl⟩ : syracuseStep 2713513 = 2035135) B2035135
theorem B1271879 : Blo 1270453 1271879 := bstep (se 1 (by rfl) ⟨953909, by rfl⟩ : syracuseStep 1271879 = 1907819) B1907819
theorem B37152893 : Blo 1270453 37152893 := bstep (se 3 (by rfl) ⟨6966167, by rfl⟩ : syracuseStep 37152893 = 13932335) B13932335
theorem B14682583 : Blo 1270453 14682583 := bstep (se 1 (by rfl) ⟨11011937, by rfl⟩ : syracuseStep 14682583 = 22023875) B22023875
theorem B15076007 : Blo 1270453 15076007 := bstep (se 1 (by rfl) ⟨11307005, by rfl⟩ : syracuseStep 15076007 = 22614011) B22614011
theorem B2861801 : Blo 1270453 2861801 := bstep (se 2 (by rfl) ⟨1073175, by rfl⟩ : syracuseStep 2861801 = 2146351) B2146351
theorem B69602165 : Blo 1270453 69602165 := bstep (se 5 (by rfl) ⟨3262601, by rfl⟩ : syracuseStep 69602165 = 6525203) B6525203
theorem B313920659 : Blo 1270453 313920659 := bstep (se 1 (by rfl) ⟨235440494, by rfl⟩ : syracuseStep 313920659 = 470880989) B470880989
theorem B6434153 : Blo 1270453 6434153 := bstep (se 2 (by rfl) ⟨2412807, by rfl⟩ : syracuseStep 6434153 = 4825615) B4825615
theorem B4288031 : Blo 1270453 4288031 := bstep (se 1 (by rfl) ⟨3216023, by rfl⟩ : syracuseStep 4288031 = 6432047) B6432047
theorem B30985811 : Blo 1270453 30985811 := bstep (se 1 (by rfl) ⟨23239358, by rfl⟩ : syracuseStep 30985811 = 46478717) B46478717
theorem B3018377 : Blo 1270453 3018377 := bstep (se 2 (by rfl) ⟨1131891, by rfl⟩ : syracuseStep 3018377 = 2263783) B2263783
theorem B5426939 : Blo 1270453 5426939 := bstep (se 1 (by rfl) ⟨4070204, by rfl⟩ : syracuseStep 5426939 = 8140409) B8140409
theorem B8146817 : Blo 1270453 8146817 := bstep (se 2 (by rfl) ⟨3055056, by rfl⟩ : syracuseStep 8146817 = 6110113) B6110113
theorem B36646829 : Blo 1270453 36646829 := bstep (se 3 (by rfl) ⟨6871280, by rfl⟩ : syracuseStep 36646829 = 13742561) B13742561
theorem B4829321 : Blo 1270453 4829321 := bstep (se 2 (by rfl) ⟨1810995, by rfl⟩ : syracuseStep 4829321 = 3621991) B3621991
theorem B37171619 : Blo 1270453 37171619 := bstep (se 1 (by rfl) ⟨27878714, by rfl⟩ : syracuseStep 37171619 = 55757429) B55757429
theorem B9163439 : Blo 1270453 9163439 := bstep (se 1 (by rfl) ⟨6872579, by rfl⟩ : syracuseStep 9163439 = 13745159) B13745159
theorem B2897545 : Blo 1270453 2897545 := bstep (se 2 (by rfl) ⟨1086579, by rfl⟩ : syracuseStep 2897545 = 2173159) B2173159
theorem B282154691 : Blo 1270453 282154691 := bstep (se 1 (by rfl) ⟨211616018, by rfl⟩ : syracuseStep 282154691 = 423232037) B423232037
theorem B1357679 : Blo 1270453 1357679 := bstep (se 1 (by rfl) ⟨1018259, by rfl⟩ : syracuseStep 1357679 = 2036519) B2036519
theorem B1906655 : Blo 1270453 1906655 := bstep (se 1 (by rfl) ⟨1429991, by rfl⟩ : syracuseStep 1906655 = 2859983) B2859983
theorem B4290623 : Blo 1270453 4290623 := bstep (se 1 (by rfl) ⟨3217967, by rfl⟩ : syracuseStep 4290623 = 6435935) B6435935
theorem B19569275 : Blo 1270453 19569275 := bstep (se 1 (by rfl) ⟨14676956, by rfl⟩ : syracuseStep 19569275 = 29353913) B29353913
theorem B1907519 : Blo 1270453 1907519 := bstep (se 1 (by rfl) ⟨1430639, by rfl⟩ : syracuseStep 1907519 = 2861279) B2861279
theorem B2145487 : Blo 1270453 2145487 := bstep (se 1 (by rfl) ⟨1609115, by rfl⟩ : syracuseStep 2145487 = 3218231) B3218231
theorem B9158017 : Blo 1270453 9158017 := bstep (se 2 (by rfl) ⟨3434256, by rfl⟩ : syracuseStep 9158017 = 6868513) B6868513
theorem B15457807 : Blo 1270453 15457807 := bstep (se 1 (by rfl) ⟨11593355, by rfl⟩ : syracuseStep 15457807 = 23186711) B23186711
theorem B3219547 : Blo 1270453 3219547 := bstep (se 1 (by rfl) ⟨2414660, by rfl⟩ : syracuseStep 3219547 = 4829321) B4829321
theorem B4292783 : Blo 1270453 4292783 := bstep (se 1 (by rfl) ⟨3219587, by rfl⟩ : syracuseStep 4292783 = 6439175) B6439175
theorem B24781079 : Blo 1270453 24781079 := bstep (se 1 (by rfl) ⟨18585809, by rfl⟩ : syracuseStep 24781079 = 37171619) B37171619
theorem B1271103 : Blo 1270453 1271103 := bstep (se 1 (by rfl) ⟨953327, by rfl⟩ : syracuseStep 1271103 = 1906655) B1906655
theorem B2860415 : Blo 1270453 2860415 := bstep (se 1 (by rfl) ⟨2145311, by rfl⟩ : syracuseStep 2860415 = 4290623) B4290623
theorem B27493769 : Blo 1270453 27493769 := bstep (se 2 (by rfl) ⟨10310163, by rfl⟩ : syracuseStep 27493769 = 20620327) B20620327
theorem B2860649 : Blo 1270453 2860649 := bstep (se 2 (by rfl) ⟨1072743, by rfl⟩ : syracuseStep 2860649 = 2145487) B2145487
theorem B752412509 : Blo 1270453 752412509 := bstep (se 3 (by rfl) ⟨141077345, by rfl⟩ : syracuseStep 752412509 = 282154691) B282154691
theorem B1271679 : Blo 1270453 1271679 := bstep (se 1 (by rfl) ⟨953759, by rfl⟩ : syracuseStep 1271679 = 1907519) B1907519
theorem B46401443 : Blo 1270453 46401443 := bstep (se 1 (by rfl) ⟨34801082, by rfl⟩ : syracuseStep 46401443 = 69602165) B69602165
theorem B24431219 : Blo 1270453 24431219 := bstep (se 1 (by rfl) ⟨18323414, by rfl⟩ : syracuseStep 24431219 = 36646829) B36646829
theorem B24768595 : Blo 1270453 24768595 := bstep (se 1 (by rfl) ⟨18576446, by rfl⟩ : syracuseStep 24768595 = 37152893) B37152893
theorem B13046183 : Blo 1270453 13046183 := bstep (se 1 (by rfl) ⟨9784637, by rfl⟩ : syracuseStep 13046183 = 19569275) B19569275
theorem B12210689 : Blo 1270453 12210689 := bstep (se 2 (by rfl) ⟨4579008, by rfl⟩ : syracuseStep 12210689 = 9158017) B9158017
theorem B10859345 : Blo 1270453 10859345 := bstep (se 2 (by rfl) ⟨4072254, by rfl⟩ : syracuseStep 10859345 = 8144509) B8144509
theorem B3863393 : Blo 1270453 3863393 := bstep (se 2 (by rfl) ⟨1448772, by rfl⟩ : syracuseStep 3863393 = 2897545) B2897545
theorem B4289435 : Blo 1270453 4289435 := bstep (se 1 (by rfl) ⟨3217076, by rfl⟩ : syracuseStep 4289435 = 6434153) B6434153
theorem B20657207 : Blo 1270453 20657207 := bstep (se 1 (by rfl) ⟨15492905, by rfl⟩ : syracuseStep 20657207 = 30985811) B30985811
theorem B2012251 : Blo 1270453 2012251 := bstep (se 1 (by rfl) ⟨1509188, by rfl⟩ : syracuseStep 2012251 = 3018377) B3018377
theorem B3617959 : Blo 1270453 3617959 := bstep (se 1 (by rfl) ⟨2713469, by rfl⟩ : syracuseStep 3617959 = 5426939) B5426939
theorem B3618017 : Blo 1270453 3618017 := bstep (se 2 (by rfl) ⟨1356756, by rfl⟩ : syracuseStep 3618017 = 2713513) B2713513
theorem B1430887 : Blo 1270453 1430887 := bstep (se 1 (by rfl) ⟨1073165, by rfl⟩ : syracuseStep 1430887 = 2146331) B2146331
theorem B6108959 : Blo 1270453 6108959 := bstep (se 1 (by rfl) ⟨4581719, by rfl⟩ : syracuseStep 6108959 = 9163439) B9163439
theorem B19576777 : Blo 1270453 19576777 := bstep (se 2 (by rfl) ⟨7341291, by rfl⟩ : syracuseStep 19576777 = 14682583) B14682583
theorem B1906919 : Blo 1270453 1906919 := bstep (se 1 (by rfl) ⟨1430189, by rfl⟩ : syracuseStep 1906919 = 2860379) B2860379
theorem B10050671 : Blo 1270453 10050671 := bstep (se 1 (by rfl) ⟨7538003, by rfl⟩ : syracuseStep 10050671 = 15076007) B15076007
theorem B1907867 : Blo 1270453 1907867 := bstep (se 1 (by rfl) ⟨1430900, by rfl⟩ : syracuseStep 1907867 = 2861801) B2861801
theorem B20610409 : Blo 1270453 20610409 := bstep (se 2 (by rfl) ⟨7728903, by rfl⟩ : syracuseStep 20610409 = 15457807) B15457807
theorem B209280439 : Blo 1270453 209280439 := bstep (se 1 (by rfl) ⟨156960329, by rfl⟩ : syracuseStep 209280439 = 313920659) B313920659
theorem B3620477 : Blo 1270453 3620477 := bstep (se 3 (by rfl) ⟨678839, by rfl⟩ : syracuseStep 3620477 = 1357679) B1357679
theorem B2858687 : Blo 1270453 2858687 := bstep (se 1 (by rfl) ⟨2144015, by rfl⟩ : syracuseStep 2858687 = 4288031) B4288031
theorem B5431211 : Blo 1270453 5431211 := bstep (se 1 (by rfl) ⟨4073408, by rfl⟩ : syracuseStep 5431211 = 8146817) B8146817
theorem B4292729 : Blo 1270453 4292729 := bstep (se 2 (by rfl) ⟨1609773, by rfl⟩ : syracuseStep 4292729 = 3219547) B3219547
theorem B2859623 : Blo 1270453 2859623 := bstep (se 1 (by rfl) ⟨2144717, by rfl⟩ : syracuseStep 2859623 = 4289435) B4289435
theorem B13771471 : Blo 1270453 13771471 := bstep (se 1 (by rfl) ⟨10328603, by rfl⟩ : syracuseStep 13771471 = 20657207) B20657207
theorem B4072639 : Blo 1270453 4072639 := bstep (se 1 (by rfl) ⟨3054479, by rfl⟩ : syracuseStep 4072639 = 6108959) B6108959
theorem B30934295 : Blo 1270453 30934295 := bstep (se 1 (by rfl) ⟨23200721, by rfl⟩ : syracuseStep 30934295 = 46401443) B46401443
theorem B1271279 : Blo 1270453 1271279 := bstep (se 1 (by rfl) ⟨953459, by rfl⟩ : syracuseStep 1271279 = 1906919) B1906919
theorem B16287479 : Blo 1270453 16287479 := bstep (se 1 (by rfl) ⟨12215609, by rfl⟩ : syracuseStep 16287479 = 24431219) B24431219
theorem B1271911 : Blo 1270453 1271911 := bstep (se 1 (by rfl) ⟨953933, by rfl⟩ : syracuseStep 1271911 = 1907867) B1907867
theorem B26102369 : Blo 1270453 26102369 := bstep (se 2 (by rfl) ⟨9788388, by rfl⟩ : syracuseStep 26102369 = 19576777) B19576777
theorem B2861855 : Blo 1270453 2861855 := bstep (se 1 (by rfl) ⟨2146391, by rfl⟩ : syracuseStep 2861855 = 4292783) B4292783
theorem B132099173 : Blo 1270453 132099173 := bstep (se 4 (by rfl) ⟨12384297, by rfl⟩ : syracuseStep 132099173 = 24768595) B24768595
theorem B2575595 : Blo 1270453 2575595 := bstep (se 1 (by rfl) ⟨1931696, by rfl⟩ : syracuseStep 2575595 = 3863393) B3863393
theorem B2412011 : Blo 1270453 2412011 := bstep (se 1 (by rfl) ⟨1809008, by rfl⟩ : syracuseStep 2412011 = 3618017) B3618017
theorem B18329179 : Blo 1270453 18329179 := bstep (se 1 (by rfl) ⟨13746884, by rfl⟩ : syracuseStep 18329179 = 27493769) B27493769
theorem B501608339 : Blo 1270453 501608339 := bstep (se 1 (by rfl) ⟨376206254, by rfl⟩ : syracuseStep 501608339 = 752412509) B752412509
theorem B2683001 : Blo 1270453 2683001 := bstep (se 2 (by rfl) ⟨1006125, by rfl⟩ : syracuseStep 2683001 = 2012251) B2012251
theorem B27480545 : Blo 1270453 27480545 := bstep (se 2 (by rfl) ⟨10305204, by rfl⟩ : syracuseStep 27480545 = 20610409) B20610409
theorem B279040585 : Blo 1270453 279040585 := bstep (se 2 (by rfl) ⟨104640219, by rfl⟩ : syracuseStep 279040585 = 209280439) B209280439
theorem B2413651 : Blo 1270453 2413651 := bstep (se 1 (by rfl) ⟨1810238, by rfl⟩ : syracuseStep 2413651 = 3620477) B3620477
theorem B1905791 : Blo 1270453 1905791 := bstep (se 1 (by rfl) ⟨1429343, by rfl⟩ : syracuseStep 1905791 = 2858687) B2858687
theorem B16520719 : Blo 1270453 16520719 := bstep (se 1 (by rfl) ⟨12390539, by rfl⟩ : syracuseStep 16520719 = 24781079) B24781079
theorem B8697455 : Blo 1270453 8697455 := bstep (se 1 (by rfl) ⟨6523091, by rfl⟩ : syracuseStep 8697455 = 13046183) B13046183
theorem B8140459 : Blo 1270453 8140459 := bstep (se 1 (by rfl) ⟨6105344, by rfl⟩ : syracuseStep 8140459 = 12210689) B12210689
theorem B7239563 : Blo 1270453 7239563 := bstep (se 1 (by rfl) ⟨5429672, by rfl⟩ : syracuseStep 7239563 = 10859345) B10859345
theorem B1906943 : Blo 1270453 1906943 := bstep (se 1 (by rfl) ⟨1430207, by rfl⟩ : syracuseStep 1906943 = 2860415) B2860415
theorem B1907099 : Blo 1270453 1907099 := bstep (se 1 (by rfl) ⟨1430324, by rfl⟩ : syracuseStep 1907099 = 2860649) B2860649
theorem B4823945 : Blo 1270453 4823945 := bstep (se 2 (by rfl) ⟨1808979, by rfl⟩ : syracuseStep 4823945 = 3617959) B3617959
theorem B1907849 : Blo 1270453 1907849 := bstep (se 2 (by rfl) ⟨715443, by rfl⟩ : syracuseStep 1907849 = 1430887) B1430887
theorem B6700447 : Blo 1270453 6700447 := bstep (se 1 (by rfl) ⟨5025335, by rfl⟩ : syracuseStep 6700447 = 10050671) B10050671
theorem B3620807 : Blo 1270453 3620807 := bstep (se 1 (by rfl) ⟨2715605, by rfl⟩ : syracuseStep 3620807 = 5431211) B5431211
theorem B1270527 : Blo 1270453 1270527 := bstep (se 1 (by rfl) ⟨952895, by rfl⟩ : syracuseStep 1270527 = 1905791) B1905791
theorem B4826375 : Blo 1270453 4826375 := bstep (se 1 (by rfl) ⟨3619781, by rfl⟩ : syracuseStep 4826375 = 7239563) B7239563
theorem B1271295 : Blo 1270453 1271295 := bstep (se 1 (by rfl) ⟨953471, by rfl⟩ : syracuseStep 1271295 = 1906943) B1906943
theorem B1271399 : Blo 1270453 1271399 := bstep (se 1 (by rfl) ⟨953549, by rfl⟩ : syracuseStep 1271399 = 1907099) B1907099
theorem B88066115 : Blo 1270453 88066115 := bstep (se 1 (by rfl) ⟨66049586, by rfl⟩ : syracuseStep 88066115 = 132099173) B132099173
theorem B1271899 : Blo 1270453 1271899 := bstep (se 1 (by rfl) ⟨953924, by rfl⟩ : syracuseStep 1271899 = 1907849) B1907849
theorem B24438905 : Blo 1270453 24438905 := bstep (se 2 (by rfl) ⟨9164589, by rfl⟩ : syracuseStep 24438905 = 18329179) B18329179
theorem B35735717 : Blo 1270453 35735717 := bstep (se 4 (by rfl) ⟨3350223, by rfl⟩ : syracuseStep 35735717 = 6700447) B6700447
theorem B1608007 : Blo 1270453 1608007 := bstep (se 1 (by rfl) ⟨1206005, by rfl⟩ : syracuseStep 1608007 = 2412011) B2412011
theorem B1788667 : Blo 1270453 1788667 := bstep (se 1 (by rfl) ⟨1341500, by rfl⟩ : syracuseStep 1788667 = 2683001) B2683001
theorem B2861819 : Blo 1270453 2861819 := bstep (se 1 (by rfl) ⟨2146364, by rfl⟩ : syracuseStep 2861819 = 4292729) B4292729
theorem B18320363 : Blo 1270453 18320363 := bstep (se 1 (by rfl) ⟨13740272, by rfl⟩ : syracuseStep 18320363 = 27480545) B27480545
theorem B6868253 : Blo 1270453 6868253 := bstep (se 3 (by rfl) ⟨1287797, by rfl⟩ : syracuseStep 6868253 = 2575595) B2575595
theorem B20622863 : Blo 1270453 20622863 := bstep (se 1 (by rfl) ⟨15467147, by rfl⟩ : syracuseStep 20622863 = 30934295) B30934295
theorem B18361961 : Blo 1270453 18361961 := bstep (se 2 (by rfl) ⟨6885735, by rfl⟩ : syracuseStep 18361961 = 13771471) B13771471
theorem B10858319 : Blo 1270453 10858319 := bstep (se 1 (by rfl) ⟨8143739, by rfl⟩ : syracuseStep 10858319 = 16287479) B16287479
theorem B3215963 : Blo 1270453 3215963 := bstep (se 1 (by rfl) ⟨2411972, by rfl⟩ : syracuseStep 3215963 = 4823945) B4823945
theorem B2413871 : Blo 1270453 2413871 := bstep (se 1 (by rfl) ⟨1810403, by rfl⟩ : syracuseStep 2413871 = 3620807) B3620807
theorem B1906415 : Blo 1270453 1906415 := bstep (se 1 (by rfl) ⟨1429811, by rfl⟩ : syracuseStep 1906415 = 2859623) B2859623
theorem B372054113 : Blo 1270453 372054113 := bstep (se 2 (by rfl) ⟨139520292, by rfl⟩ : syracuseStep 372054113 = 279040585) B279040585
theorem B5798303 : Blo 1270453 5798303 := bstep (se 1 (by rfl) ⟨4348727, by rfl⟩ : syracuseStep 5798303 = 8697455) B8697455
theorem B3218201 : Blo 1270453 3218201 := bstep (se 2 (by rfl) ⟨1206825, by rfl⟩ : syracuseStep 3218201 = 2413651) B2413651
theorem B5430185 : Blo 1270453 5430185 := bstep (se 2 (by rfl) ⟨2036319, by rfl⟩ : syracuseStep 5430185 = 4072639) B4072639
theorem B69606317 : Blo 1270453 69606317 := bstep (se 3 (by rfl) ⟨13051184, by rfl⟩ : syracuseStep 69606317 = 26102369) B26102369
theorem B1907903 : Blo 1270453 1907903 := bstep (se 1 (by rfl) ⟨1430927, by rfl⟩ : syracuseStep 1907903 = 2861855) B2861855
theorem B22027625 : Blo 1270453 22027625 := bstep (se 2 (by rfl) ⟨8260359, by rfl⟩ : syracuseStep 22027625 = 16520719) B16520719
theorem B10853945 : Blo 1270453 10853945 := bstep (se 2 (by rfl) ⟨4070229, by rfl⟩ : syracuseStep 10853945 = 8140459) B8140459
theorem B334405559 : Blo 1270453 334405559 := bstep (se 1 (by rfl) ⟨250804169, by rfl⟩ : syracuseStep 334405559 = 501608339) B501608339
theorem B1270943 : Blo 1270453 1270943 := bstep (se 1 (by rfl) ⟨953207, by rfl⟩ : syracuseStep 1270943 = 1906415) B1906415
theorem B54994301 : Blo 1270453 54994301 := bstep (se 3 (by rfl) ⟨10311431, by rfl⟩ : syracuseStep 54994301 = 20622863) B20622863
theorem B23823811 : Blo 1270453 23823811 := bstep (se 1 (by rfl) ⟨17867858, by rfl⟩ : syracuseStep 23823811 = 35735717) B35735717
theorem B1271935 : Blo 1270453 1271935 := bstep (se 1 (by rfl) ⟨953951, by rfl⟩ : syracuseStep 1271935 = 1907903) B1907903
theorem B7235963 : Blo 1270453 7235963 := bstep (se 1 (by rfl) ⟨5426972, by rfl⟩ : syracuseStep 7235963 = 10853945) B10853945
theorem B12241307 : Blo 1270453 12241307 := bstep (se 1 (by rfl) ⟨9180980, by rfl⟩ : syracuseStep 12241307 = 18361961) B18361961
theorem B1609247 : Blo 1270453 1609247 := bstep (se 1 (by rfl) ⟨1206935, by rfl⟩ : syracuseStep 1609247 = 2413871) B2413871
theorem B46404211 : Blo 1270453 46404211 := bstep (se 1 (by rfl) ⟨34803158, by rfl⟩ : syracuseStep 46404211 = 69606317) B69606317
theorem B14685083 : Blo 1270453 14685083 := bstep (se 1 (by rfl) ⟨11013812, by rfl⟩ : syracuseStep 14685083 = 22027625) B22027625
theorem B7238879 : Blo 1270453 7238879 := bstep (se 1 (by rfl) ⟨5429159, by rfl⟩ : syracuseStep 7238879 = 10858319) B10858319
theorem B2143975 : Blo 1270453 2143975 := bstep (se 1 (by rfl) ⟨1607981, by rfl⟩ : syracuseStep 2143975 = 3215963) B3215963
theorem B2144009 : Blo 1270453 2144009 := bstep (se 2 (by rfl) ⟨804003, by rfl⟩ : syracuseStep 2144009 = 1608007) B1608007
theorem B18315341 : Blo 1270453 18315341 := bstep (se 3 (by rfl) ⟨3434126, by rfl⟩ : syracuseStep 18315341 = 6868253) B6868253
theorem B3217583 : Blo 1270453 3217583 := bstep (se 1 (by rfl) ⟨2413187, by rfl⟩ : syracuseStep 3217583 = 4826375) B4826375
theorem B58710743 : Blo 1270453 58710743 := bstep (se 1 (by rfl) ⟨44033057, by rfl⟩ : syracuseStep 58710743 = 88066115) B88066115
theorem B248036075 : Blo 1270453 248036075 := bstep (se 1 (by rfl) ⟨186027056, by rfl⟩ : syracuseStep 248036075 = 372054113) B372054113
theorem B16292603 : Blo 1270453 16292603 := bstep (se 1 (by rfl) ⟨12219452, by rfl⟩ : syracuseStep 16292603 = 24438905) B24438905
theorem B3865535 : Blo 1270453 3865535 := bstep (se 1 (by rfl) ⟨2899151, by rfl⟩ : syracuseStep 3865535 = 5798303) B5798303
theorem B1907879 : Blo 1270453 1907879 := bstep (se 1 (by rfl) ⟨1430909, by rfl⟩ : syracuseStep 1907879 = 2861819) B2861819
theorem B2145467 : Blo 1270453 2145467 := bstep (se 1 (by rfl) ⟨1609100, by rfl⟩ : syracuseStep 2145467 = 3218201) B3218201
theorem B3620123 : Blo 1270453 3620123 := bstep (se 1 (by rfl) ⟨2715092, by rfl⟩ : syracuseStep 3620123 = 5430185) B5430185
theorem B12213575 : Blo 1270453 12213575 := bstep (se 1 (by rfl) ⟨9160181, by rfl⟩ : syracuseStep 12213575 = 18320363) B18320363
theorem B38158229 : Blo 1270453 38158229 := bstep (se 6 (by rfl) ⟨894333, by rfl⟩ : syracuseStep 38158229 = 1788667) B1788667
theorem B222937039 : Blo 1270453 222937039 := bstep (se 1 (by rfl) ⟨167202779, by rfl⟩ : syracuseStep 222937039 = 334405559) B334405559
theorem B9790055 : Blo 1270453 9790055 := bstep (se 1 (by rfl) ⟨7342541, by rfl⟩ : syracuseStep 9790055 = 14685083) B14685083
theorem B4825919 : Blo 1270453 4825919 := bstep (se 1 (by rfl) ⟨3619439, by rfl⟩ : syracuseStep 4825919 = 7238879) B7238879
theorem B8160871 : Blo 1270453 8160871 := bstep (se 1 (by rfl) ⟨6120653, by rfl⟩ : syracuseStep 8160871 = 12241307) B12241307
theorem B165357383 : Blo 1270453 165357383 := bstep (se 1 (by rfl) ⟨124018037, by rfl⟩ : syracuseStep 165357383 = 248036075) B248036075
theorem B1271919 : Blo 1270453 1271919 := bstep (se 1 (by rfl) ⟨953939, by rfl⟩ : syracuseStep 1271919 = 1907879) B1907879
theorem B25438819 : Blo 1270453 25438819 := bstep (se 1 (by rfl) ⟨19079114, by rfl⟩ : syracuseStep 25438819 = 38158229) B38158229
theorem B297249385 : Blo 1270453 297249385 := bstep (se 2 (by rfl) ⟨111468519, by rfl⟩ : syracuseStep 297249385 = 222937039) B222937039
theorem B36662867 : Blo 1270453 36662867 := bstep (se 1 (by rfl) ⟨27497150, by rfl⟩ : syracuseStep 36662867 = 54994301) B54994301
theorem B1429339 : Blo 1270453 1429339 := bstep (se 1 (by rfl) ⟨1072004, by rfl⟩ : syracuseStep 1429339 = 2144009) B2144009
theorem B12210227 : Blo 1270453 12210227 := bstep (se 1 (by rfl) ⟨9157670, by rfl⟩ : syracuseStep 12210227 = 18315341) B18315341
theorem B31765081 : Blo 1270453 31765081 := bstep (se 2 (by rfl) ⟨11911905, by rfl⟩ : syracuseStep 31765081 = 23823811) B23823811
theorem B2577023 : Blo 1270453 2577023 := bstep (se 1 (by rfl) ⟨1932767, by rfl⟩ : syracuseStep 2577023 = 3865535) B3865535
theorem B1430311 : Blo 1270453 1430311 := bstep (se 1 (by rfl) ⟨1072733, by rfl⟩ : syracuseStep 1430311 = 2145467) B2145467
theorem B2413415 : Blo 1270453 2413415 := bstep (se 1 (by rfl) ⟨1810061, by rfl⟩ : syracuseStep 2413415 = 3620123) B3620123
theorem B61872281 : Blo 1270453 61872281 := bstep (se 2 (by rfl) ⟨23202105, by rfl⟩ : syracuseStep 61872281 = 46404211) B46404211
theorem B4291325 : Blo 1270453 4291325 := bstep (se 3 (by rfl) ⟨804623, by rfl⟩ : syracuseStep 4291325 = 1609247) B1609247
theorem B2145055 : Blo 1270453 2145055 := bstep (se 1 (by rfl) ⟨1608791, by rfl⟩ : syracuseStep 2145055 = 3217583) B3217583
theorem B4823975 : Blo 1270453 4823975 := bstep (se 1 (by rfl) ⟨3617981, by rfl⟩ : syracuseStep 4823975 = 7235963) B7235963
theorem B39140495 : Blo 1270453 39140495 := bstep (se 1 (by rfl) ⟨29355371, by rfl⟩ : syracuseStep 39140495 = 58710743) B58710743
theorem B10861735 : Blo 1270453 10861735 := bstep (se 1 (by rfl) ⟨8146301, by rfl⟩ : syracuseStep 10861735 = 16292603) B16292603
theorem B8142383 : Blo 1270453 8142383 := bstep (se 1 (by rfl) ⟨6106787, by rfl⟩ : syracuseStep 8142383 = 12213575) B12213575
theorem B2858633 : Blo 1270453 2858633 := bstep (se 2 (by rfl) ⟨1071987, by rfl⟩ : syracuseStep 2858633 = 2143975) B2143975
theorem B42353441 : Blo 1270453 42353441 := bstep (se 2 (by rfl) ⟨15882540, by rfl⟩ : syracuseStep 42353441 = 31765081) B31765081
theorem B2860073 : Blo 1270453 2860073 := bstep (se 2 (by rfl) ⟨1072527, by rfl⟩ : syracuseStep 2860073 = 2145055) B2145055
theorem B41248187 : Blo 1270453 41248187 := bstep (se 1 (by rfl) ⟨30936140, by rfl⟩ : syracuseStep 41248187 = 61872281) B61872281
theorem B2860883 : Blo 1270453 2860883 := bstep (se 1 (by rfl) ⟨2145662, by rfl⟩ : syracuseStep 2860883 = 4291325) B4291325
theorem B26093663 : Blo 1270453 26093663 := bstep (se 1 (by rfl) ⟨19570247, by rfl⟩ : syracuseStep 26093663 = 39140495) B39140495
theorem B10881161 : Blo 1270453 10881161 := bstep (se 2 (by rfl) ⟨4080435, by rfl⟩ : syracuseStep 10881161 = 8160871) B8160871
theorem B440953021 : Blo 1270453 440953021 := bstep (se 3 (by rfl) ⟨82678691, by rfl⟩ : syracuseStep 440953021 = 165357383) B165357383
theorem B33918425 : Blo 1270453 33918425 := bstep (se 2 (by rfl) ⟨12719409, by rfl⟩ : syracuseStep 33918425 = 25438819) B25438819
theorem B396332513 : Blo 1270453 396332513 := bstep (se 2 (by rfl) ⟨148624692, by rfl⟩ : syracuseStep 396332513 = 297249385) B297249385
theorem B3215983 : Blo 1270453 3215983 := bstep (se 1 (by rfl) ⟨2411987, by rfl⟩ : syracuseStep 3215983 = 4823975) B4823975
theorem B6435773 : Blo 1270453 6435773 := bstep (se 3 (by rfl) ⟨1206707, by rfl⟩ : syracuseStep 6435773 = 2413415) B2413415
theorem B5428255 : Blo 1270453 5428255 := bstep (se 1 (by rfl) ⟨4071191, by rfl⟩ : syracuseStep 5428255 = 8142383) B8142383
theorem B24441911 : Blo 1270453 24441911 := bstep (se 1 (by rfl) ⟨18331433, by rfl⟩ : syracuseStep 24441911 = 36662867) B36662867
theorem B1905755 : Blo 1270453 1905755 := bstep (se 1 (by rfl) ⟨1429316, by rfl⟩ : syracuseStep 1905755 = 2858633) B2858633
theorem B1905785 : Blo 1270453 1905785 := bstep (se 2 (by rfl) ⟨714669, by rfl⟩ : syracuseStep 1905785 = 1429339) B1429339
theorem B8140151 : Blo 1270453 8140151 := bstep (se 1 (by rfl) ⟨6105113, by rfl⟩ : syracuseStep 8140151 = 12210227) B12210227
theorem B6526703 : Blo 1270453 6526703 := bstep (se 1 (by rfl) ⟨4895027, by rfl⟩ : syracuseStep 6526703 = 9790055) B9790055
theorem B1718015 : Blo 1270453 1718015 := bstep (se 1 (by rfl) ⟨1288511, by rfl⟩ : syracuseStep 1718015 = 2577023) B2577023
theorem B3217279 : Blo 1270453 3217279 := bstep (se 1 (by rfl) ⟨2412959, by rfl⟩ : syracuseStep 3217279 = 4825919) B4825919
theorem B1907081 : Blo 1270453 1907081 := bstep (se 2 (by rfl) ⟨715155, by rfl⟩ : syracuseStep 1907081 = 1430311) B1430311
theorem B14482313 : Blo 1270453 14482313 := bstep (se 2 (by rfl) ⟨5430867, by rfl⟩ : syracuseStep 14482313 = 10861735) B10861735
theorem B16294607 : Blo 1270453 16294607 := bstep (se 1 (by rfl) ⟨12220955, by rfl⟩ : syracuseStep 16294607 = 24441911) B24441911
theorem B1270503 : Blo 1270453 1270503 := bstep (se 1 (by rfl) ⟨952877, by rfl⟩ : syracuseStep 1270503 = 1905755) B1905755
theorem B1270523 : Blo 1270453 1270523 := bstep (se 1 (by rfl) ⟨952892, by rfl⟩ : syracuseStep 1270523 = 1905785) B1905785
theorem B1271387 : Blo 1270453 1271387 := bstep (se 1 (by rfl) ⟨953540, by rfl⟩ : syracuseStep 1271387 = 1907081) B1907081
theorem B4581373 : Blo 1270453 4581373 := bstep (se 3 (by rfl) ⟨859007, by rfl⟩ : syracuseStep 4581373 = 1718015) B1718015
theorem B22612283 : Blo 1270453 22612283 := bstep (se 1 (by rfl) ⟨16959212, by rfl⟩ : syracuseStep 22612283 = 33918425) B33918425
theorem B4287977 : Blo 1270453 4287977 := bstep (se 2 (by rfl) ⟨1607991, by rfl⟩ : syracuseStep 4287977 = 3215983) B3215983
theorem B5426767 : Blo 1270453 5426767 := bstep (se 1 (by rfl) ⟨4070075, by rfl⟩ : syracuseStep 5426767 = 8140151) B8140151
theorem B7237673 : Blo 1270453 7237673 := bstep (se 2 (by rfl) ⟨2714127, by rfl⟩ : syracuseStep 7237673 = 5428255) B5428255
theorem B17395775 : Blo 1270453 17395775 := bstep (se 1 (by rfl) ⟨13046831, by rfl⟩ : syracuseStep 17395775 = 26093663) B26093663
theorem B7254107 : Blo 1270453 7254107 := bstep (se 1 (by rfl) ⟨5440580, by rfl⟩ : syracuseStep 7254107 = 10881161) B10881161
theorem B9654875 : Blo 1270453 9654875 := bstep (se 1 (by rfl) ⟨7241156, by rfl⟩ : syracuseStep 9654875 = 14482313) B14482313
theorem B17404541 : Blo 1270453 17404541 := bstep (se 3 (by rfl) ⟨3263351, by rfl⟩ : syracuseStep 17404541 = 6526703) B6526703
theorem B264221675 : Blo 1270453 264221675 := bstep (se 1 (by rfl) ⟨198166256, by rfl⟩ : syracuseStep 264221675 = 396332513) B396332513
theorem B4289705 : Blo 1270453 4289705 := bstep (se 2 (by rfl) ⟨1608639, by rfl⟩ : syracuseStep 4289705 = 3217279) B3217279
theorem B587937361 : Blo 1270453 587937361 := bstep (se 2 (by rfl) ⟨220476510, by rfl⟩ : syracuseStep 587937361 = 440953021) B440953021
theorem B28235627 : Blo 1270453 28235627 := bstep (se 1 (by rfl) ⟨21176720, by rfl⟩ : syracuseStep 28235627 = 42353441) B42353441
theorem B4290515 : Blo 1270453 4290515 := bstep (se 1 (by rfl) ⟨3217886, by rfl⟩ : syracuseStep 4290515 = 6435773) B6435773
theorem B1906715 : Blo 1270453 1906715 := bstep (se 1 (by rfl) ⟨1430036, by rfl⟩ : syracuseStep 1906715 = 2860073) B2860073
theorem B27498791 : Blo 1270453 27498791 := bstep (se 1 (by rfl) ⟨20624093, by rfl⟩ : syracuseStep 27498791 = 41248187) B41248187
theorem B1907255 : Blo 1270453 1907255 := bstep (se 1 (by rfl) ⟨1430441, by rfl⟩ : syracuseStep 1907255 = 2860883) B2860883
theorem B4825115 : Blo 1270453 4825115 := bstep (se 1 (by rfl) ⟨3618836, by rfl⟩ : syracuseStep 4825115 = 7237673) B7237673
theorem B10863071 : Blo 1270453 10863071 := bstep (se 1 (by rfl) ⟨8147303, by rfl⟩ : syracuseStep 10863071 = 16294607) B16294607
theorem B2859803 : Blo 1270453 2859803 := bstep (se 1 (by rfl) ⟨2144852, by rfl⟩ : syracuseStep 2859803 = 4289705) B4289705
theorem B2860343 : Blo 1270453 2860343 := bstep (se 1 (by rfl) ⟨2145257, by rfl⟩ : syracuseStep 2860343 = 4290515) B4290515
theorem B1271143 : Blo 1270453 1271143 := bstep (se 1 (by rfl) ⟨953357, by rfl⟩ : syracuseStep 1271143 = 1906715) B1906715
theorem B15074855 : Blo 1270453 15074855 := bstep (se 1 (by rfl) ⟨11306141, by rfl⟩ : syracuseStep 15074855 = 22612283) B22612283
theorem B1271503 : Blo 1270453 1271503 := bstep (se 1 (by rfl) ⟨953627, by rfl⟩ : syracuseStep 1271503 = 1907255) B1907255
theorem B7235689 : Blo 1270453 7235689 := bstep (se 2 (by rfl) ⟨2713383, by rfl⟩ : syracuseStep 7235689 = 5426767) B5426767
theorem B4836071 : Blo 1270453 4836071 := bstep (se 1 (by rfl) ⟨3627053, by rfl⟩ : syracuseStep 4836071 = 7254107) B7254107
theorem B11603027 : Blo 1270453 11603027 := bstep (se 1 (by rfl) ⟨8702270, by rfl⟩ : syracuseStep 11603027 = 17404541) B17404541
theorem B176147783 : Blo 1270453 176147783 := bstep (se 1 (by rfl) ⟨132110837, by rfl⟩ : syracuseStep 176147783 = 264221675) B264221675
theorem B6108497 : Blo 1270453 6108497 := bstep (se 2 (by rfl) ⟨2290686, by rfl⟩ : syracuseStep 6108497 = 4581373) B4581373
theorem B11597183 : Blo 1270453 11597183 := bstep (se 1 (by rfl) ⟨8697887, by rfl⟩ : syracuseStep 11597183 = 17395775) B17395775
theorem B6436583 : Blo 1270453 6436583 := bstep (se 1 (by rfl) ⟨4827437, by rfl⟩ : syracuseStep 6436583 = 9654875) B9654875
theorem B18823751 : Blo 1270453 18823751 := bstep (se 1 (by rfl) ⟨14117813, by rfl⟩ : syracuseStep 18823751 = 28235627) B28235627
theorem B18332527 : Blo 1270453 18332527 := bstep (se 1 (by rfl) ⟨13749395, by rfl⟩ : syracuseStep 18332527 = 27498791) B27498791
theorem B783916481 : Blo 1270453 783916481 := bstep (se 2 (by rfl) ⟨293968680, by rfl⟩ : syracuseStep 783916481 = 587937361) B587937361
theorem B2858651 : Blo 1270453 2858651 := bstep (se 1 (by rfl) ⟨2143988, by rfl⟩ : syracuseStep 2858651 = 4287977) B4287977
theorem B7242047 : Blo 1270453 7242047 := bstep (se 1 (by rfl) ⟨5431535, by rfl⟩ : syracuseStep 7242047 = 10863071) B10863071
theorem B4072331 : Blo 1270453 4072331 := bstep (se 1 (by rfl) ⟨3054248, by rfl⟩ : syracuseStep 4072331 = 6108497) B6108497
theorem B12896189 : Blo 1270453 12896189 := bstep (se 3 (by rfl) ⟨2418035, by rfl⟩ : syracuseStep 12896189 = 4836071) B4836071
theorem B7735351 : Blo 1270453 7735351 := bstep (se 1 (by rfl) ⟨5801513, by rfl⟩ : syracuseStep 7735351 = 11603027) B11603027
theorem B522610987 : Blo 1270453 522610987 := bstep (se 1 (by rfl) ⟨391958240, by rfl⟩ : syracuseStep 522610987 = 783916481) B783916481
theorem B1905767 : Blo 1270453 1905767 := bstep (se 1 (by rfl) ⟨1429325, by rfl⟩ : syracuseStep 1905767 = 2858651) B2858651
theorem B3216743 : Blo 1270453 3216743 := bstep (se 1 (by rfl) ⟨2412557, by rfl⟩ : syracuseStep 3216743 = 4825115) B4825115
theorem B9647585 : Blo 1270453 9647585 := bstep (se 2 (by rfl) ⟨3617844, by rfl⟩ : syracuseStep 9647585 = 7235689) B7235689
theorem B1906535 : Blo 1270453 1906535 := bstep (se 1 (by rfl) ⟨1429901, by rfl⟩ : syracuseStep 1906535 = 2859803) B2859803
theorem B1906895 : Blo 1270453 1906895 := bstep (se 1 (by rfl) ⟨1430171, by rfl⟩ : syracuseStep 1906895 = 2860343) B2860343
theorem B7731455 : Blo 1270453 7731455 := bstep (se 1 (by rfl) ⟨5798591, by rfl⟩ : syracuseStep 7731455 = 11597183) B11597183
theorem B10049903 : Blo 1270453 10049903 := bstep (se 1 (by rfl) ⟨7537427, by rfl⟩ : syracuseStep 10049903 = 15074855) B15074855
theorem B24443369 : Blo 1270453 24443369 := bstep (se 2 (by rfl) ⟨9166263, by rfl⟩ : syracuseStep 24443369 = 18332527) B18332527
theorem B4291055 : Blo 1270453 4291055 := bstep (se 1 (by rfl) ⟨3218291, by rfl⟩ : syracuseStep 4291055 = 6436583) B6436583
theorem B12549167 : Blo 1270453 12549167 := bstep (se 1 (by rfl) ⟨9411875, by rfl⟩ : syracuseStep 12549167 = 18823751) B18823751
theorem B117431855 : Blo 1270453 117431855 := bstep (se 1 (by rfl) ⟨88073891, by rfl⟩ : syracuseStep 117431855 = 176147783) B176147783
theorem B10313801 : Blo 1270453 10313801 := bstep (se 2 (by rfl) ⟨3867675, by rfl⟩ : syracuseStep 10313801 = 7735351) B7735351
theorem B1270511 : Blo 1270453 1270511 := bstep (se 1 (by rfl) ⟨952883, by rfl⟩ : syracuseStep 1270511 = 1905767) B1905767
theorem B6431723 : Blo 1270453 6431723 := bstep (se 1 (by rfl) ⟨4823792, by rfl⟩ : syracuseStep 6431723 = 9647585) B9647585
theorem B1271023 : Blo 1270453 1271023 := bstep (se 1 (by rfl) ⟨953267, by rfl⟩ : syracuseStep 1271023 = 1906535) B1906535
theorem B1271263 : Blo 1270453 1271263 := bstep (se 1 (by rfl) ⟨953447, by rfl⟩ : syracuseStep 1271263 = 1906895) B1906895
theorem B16295579 : Blo 1270453 16295579 := bstep (se 1 (by rfl) ⟨12221684, by rfl⟩ : syracuseStep 16295579 = 24443369) B24443369
theorem B2860703 : Blo 1270453 2860703 := bstep (se 1 (by rfl) ⟨2145527, by rfl⟩ : syracuseStep 2860703 = 4291055) B4291055
theorem B8366111 : Blo 1270453 8366111 := bstep (se 1 (by rfl) ⟨6274583, by rfl⟩ : syracuseStep 8366111 = 12549167) B12549167
theorem B4828031 : Blo 1270453 4828031 := bstep (se 1 (by rfl) ⟨3621023, by rfl⟩ : syracuseStep 4828031 = 7242047) B7242047
theorem B696814649 : Blo 1270453 696814649 := bstep (se 2 (by rfl) ⟨261305493, by rfl⟩ : syracuseStep 696814649 = 522610987) B522610987
theorem B2714887 : Blo 1270453 2714887 := bstep (se 1 (by rfl) ⟨2036165, by rfl⟩ : syracuseStep 2714887 = 4072331) B4072331
theorem B8597459 : Blo 1270453 8597459 := bstep (se 1 (by rfl) ⟨6448094, by rfl⟩ : syracuseStep 8597459 = 12896189) B12896189
theorem B78287903 : Blo 1270453 78287903 := bstep (se 1 (by rfl) ⟨58715927, by rfl⟩ : syracuseStep 78287903 = 117431855) B117431855
theorem B2144495 : Blo 1270453 2144495 := bstep (se 1 (by rfl) ⟨1608371, by rfl⟩ : syracuseStep 2144495 = 3216743) B3216743
theorem B6699935 : Blo 1270453 6699935 := bstep (se 1 (by rfl) ⟨5024951, by rfl⟩ : syracuseStep 6699935 = 10049903) B10049903
theorem B82468853 : Blo 1270453 82468853 := bstep (se 5 (by rfl) ⟨3865727, by rfl⟩ : syracuseStep 82468853 = 7731455) B7731455
theorem B52191935 : Blo 1270453 52191935 := bstep (se 1 (by rfl) ⟨39143951, by rfl⟩ : syracuseStep 52191935 = 78287903) B78287903
theorem B10863719 : Blo 1270453 10863719 := bstep (se 1 (by rfl) ⟨8147789, by rfl⟩ : syracuseStep 10863719 = 16295579) B16295579
theorem B54979235 : Blo 1270453 54979235 := bstep (se 1 (by rfl) ⟨41234426, by rfl⟩ : syracuseStep 54979235 = 82468853) B82468853
theorem B6875867 : Blo 1270453 6875867 := bstep (se 1 (by rfl) ⟨5156900, by rfl⟩ : syracuseStep 6875867 = 10313801) B10313801
theorem B4287815 : Blo 1270453 4287815 := bstep (se 1 (by rfl) ⟨3215861, by rfl⟩ : syracuseStep 4287815 = 6431723) B6431723
theorem B14479397 : Blo 1270453 14479397 := bstep (se 4 (by rfl) ⟨1357443, by rfl⟩ : syracuseStep 14479397 = 2714887) B2714887
theorem B1429663 : Blo 1270453 1429663 := bstep (se 1 (by rfl) ⟨1072247, by rfl⟩ : syracuseStep 1429663 = 2144495) B2144495
theorem B22926557 : Blo 1270453 22926557 := bstep (se 3 (by rfl) ⟨4298729, by rfl⟩ : syracuseStep 22926557 = 8597459) B8597459
theorem B1907135 : Blo 1270453 1907135 := bstep (se 1 (by rfl) ⟨1430351, by rfl⟩ : syracuseStep 1907135 = 2860703) B2860703
theorem B5577407 : Blo 1270453 5577407 := bstep (se 1 (by rfl) ⟨4183055, by rfl⟩ : syracuseStep 5577407 = 8366111) B8366111
theorem B3218687 : Blo 1270453 3218687 := bstep (se 1 (by rfl) ⟨2414015, by rfl⟩ : syracuseStep 3218687 = 4828031) B4828031
theorem B464543099 : Blo 1270453 464543099 := bstep (se 1 (by rfl) ⟨348407324, by rfl⟩ : syracuseStep 464543099 = 696814649) B696814649
theorem B17866493 : Blo 1270453 17866493 := bstep (se 3 (by rfl) ⟨3349967, by rfl⟩ : syracuseStep 17866493 = 6699935) B6699935
theorem B7242479 : Blo 1270453 7242479 := bstep (se 1 (by rfl) ⟨5431859, by rfl⟩ : syracuseStep 7242479 = 10863719) B10863719
theorem B1271423 : Blo 1270453 1271423 := bstep (se 1 (by rfl) ⟨953567, by rfl⟩ : syracuseStep 1271423 = 1907135) B1907135
theorem B36652823 : Blo 1270453 36652823 := bstep (se 1 (by rfl) ⟨27489617, by rfl⟩ : syracuseStep 36652823 = 54979235) B54979235
theorem B9652931 : Blo 1270453 9652931 := bstep (se 1 (by rfl) ⟨7239698, by rfl⟩ : syracuseStep 9652931 = 14479397) B14479397
theorem B34794623 : Blo 1270453 34794623 := bstep (se 1 (by rfl) ⟨26095967, by rfl⟩ : syracuseStep 34794623 = 52191935) B52191935
theorem B4583911 : Blo 1270453 4583911 := bstep (se 1 (by rfl) ⟨3437933, by rfl⟩ : syracuseStep 4583911 = 6875867) B6875867
theorem B309695399 : Blo 1270453 309695399 := bstep (se 1 (by rfl) ⟨232271549, by rfl⟩ : syracuseStep 309695399 = 464543099) B464543099
theorem B1906217 : Blo 1270453 1906217 := bstep (se 2 (by rfl) ⟨714831, by rfl⟩ : syracuseStep 1906217 = 1429663) B1429663
theorem B15284371 : Blo 1270453 15284371 := bstep (se 1 (by rfl) ⟨11463278, by rfl⟩ : syracuseStep 15284371 = 22926557) B22926557
theorem B3718271 : Blo 1270453 3718271 := bstep (se 1 (by rfl) ⟨2788703, by rfl⟩ : syracuseStep 3718271 = 5577407) B5577407
theorem B2145791 : Blo 1270453 2145791 := bstep (se 1 (by rfl) ⟨1609343, by rfl⟩ : syracuseStep 2145791 = 3218687) B3218687
theorem B2858543 : Blo 1270453 2858543 := bstep (se 1 (by rfl) ⟨2143907, by rfl⟩ : syracuseStep 2858543 = 4287815) B4287815
theorem B11910995 : Blo 1270453 11910995 := bstep (se 1 (by rfl) ⟨8933246, by rfl⟩ : syracuseStep 11910995 = 17866493) B17866493
theorem B206463599 : Blo 1270453 206463599 := bstep (se 1 (by rfl) ⟨154847699, by rfl⟩ : syracuseStep 206463599 = 309695399) B309695399
theorem B6111881 : Blo 1270453 6111881 := bstep (se 2 (by rfl) ⟨2291955, by rfl⟩ : syracuseStep 6111881 = 4583911) B4583911
theorem B1270811 : Blo 1270453 1270811 := bstep (se 1 (by rfl) ⟨953108, by rfl⟩ : syracuseStep 1270811 = 1906217) B1906217
theorem B7940663 : Blo 1270453 7940663 := bstep (se 1 (by rfl) ⟨5955497, by rfl⟩ : syracuseStep 7940663 = 11910995) B11910995
theorem B9915389 : Blo 1270453 9915389 := bstep (se 3 (by rfl) ⟨1859135, by rfl⟩ : syracuseStep 9915389 = 3718271) B3718271
theorem B92785661 : Blo 1270453 92785661 := bstep (se 3 (by rfl) ⟨17397311, by rfl⟩ : syracuseStep 92785661 = 34794623) B34794623
theorem B4828319 : Blo 1270453 4828319 := bstep (se 1 (by rfl) ⟨3621239, by rfl⟩ : syracuseStep 4828319 = 7242479) B7242479
theorem B6435287 : Blo 1270453 6435287 := bstep (se 1 (by rfl) ⟨4826465, by rfl⟩ : syracuseStep 6435287 = 9652931) B9652931
theorem B1430527 : Blo 1270453 1430527 := bstep (se 1 (by rfl) ⟨1072895, by rfl⟩ : syracuseStep 1430527 = 2145791) B2145791
theorem B1905695 : Blo 1270453 1905695 := bstep (se 1 (by rfl) ⟨1429271, by rfl⟩ : syracuseStep 1905695 = 2858543) B2858543
theorem B20379161 : Blo 1270453 20379161 := bstep (se 2 (by rfl) ⟨7642185, by rfl⟩ : syracuseStep 20379161 = 15284371) B15284371
theorem B24435215 : Blo 1270453 24435215 := bstep (se 1 (by rfl) ⟨18326411, by rfl⟩ : syracuseStep 24435215 = 36652823) B36652823
theorem B137642399 : Blo 1270453 137642399 := bstep (se 1 (by rfl) ⟨103231799, by rfl⟩ : syracuseStep 137642399 = 206463599) B206463599
theorem B1270463 : Blo 1270453 1270463 := bstep (se 1 (by rfl) ⟨952847, by rfl⟩ : syracuseStep 1270463 = 1905695) B1905695
theorem B5293775 : Blo 1270453 5293775 := bstep (se 1 (by rfl) ⟨3970331, by rfl⟩ : syracuseStep 5293775 = 7940663) B7940663
theorem B4074587 : Blo 1270453 4074587 := bstep (se 1 (by rfl) ⟨3055940, by rfl⟩ : syracuseStep 4074587 = 6111881) B6111881
theorem B16290143 : Blo 1270453 16290143 := bstep (se 1 (by rfl) ⟨12217607, by rfl⟩ : syracuseStep 16290143 = 24435215) B24435215
theorem B4290191 : Blo 1270453 4290191 := bstep (se 1 (by rfl) ⟨3217643, by rfl⟩ : syracuseStep 4290191 = 6435287) B6435287
theorem B1907369 : Blo 1270453 1907369 := bstep (se 2 (by rfl) ⟨715263, by rfl⟩ : syracuseStep 1907369 = 1430527) B1430527
theorem B54344429 : Blo 1270453 54344429 := bstep (se 3 (by rfl) ⟨10189580, by rfl⟩ : syracuseStep 54344429 = 20379161) B20379161
theorem B6610259 : Blo 1270453 6610259 := bstep (se 1 (by rfl) ⟨4957694, by rfl⟩ : syracuseStep 6610259 = 9915389) B9915389
theorem B61857107 : Blo 1270453 61857107 := bstep (se 1 (by rfl) ⟨46392830, by rfl⟩ : syracuseStep 61857107 = 92785661) B92785661
theorem B3218879 : Blo 1270453 3218879 := bstep (se 1 (by rfl) ⟨2414159, by rfl⟩ : syracuseStep 3218879 = 4828319) B4828319
theorem B2860127 : Blo 1270453 2860127 := bstep (se 1 (by rfl) ⟨2145095, by rfl⟩ : syracuseStep 2860127 = 4290191) B4290191
theorem B1271579 : Blo 1270453 1271579 := bstep (se 1 (by rfl) ⟨953684, by rfl⟩ : syracuseStep 1271579 = 1907369) B1907369
theorem B14116733 : Blo 1270453 14116733 := bstep (se 3 (by rfl) ⟨2646887, by rfl⟩ : syracuseStep 14116733 = 5293775) B5293775
theorem B91761599 : Blo 1270453 91761599 := bstep (se 1 (by rfl) ⟨68821199, by rfl⟩ : syracuseStep 91761599 = 137642399) B137642399
theorem B36229619 : Blo 1270453 36229619 := bstep (se 1 (by rfl) ⟨27172214, by rfl⟩ : syracuseStep 36229619 = 54344429) B54344429
theorem B2716391 : Blo 1270453 2716391 := bstep (se 1 (by rfl) ⟨2037293, by rfl⟩ : syracuseStep 2716391 = 4074587) B4074587
theorem B10860095 : Blo 1270453 10860095 := bstep (se 1 (by rfl) ⟨8145071, by rfl⟩ : syracuseStep 10860095 = 16290143) B16290143
theorem B17627357 : Blo 1270453 17627357 := bstep (se 3 (by rfl) ⟨3305129, by rfl⟩ : syracuseStep 17627357 = 6610259) B6610259
theorem B41238071 : Blo 1270453 41238071 := bstep (se 1 (by rfl) ⟨30928553, by rfl⟩ : syracuseStep 41238071 = 61857107) B61857107
theorem B2145919 : Blo 1270453 2145919 := bstep (se 1 (by rfl) ⟨1609439, by rfl⟩ : syracuseStep 2145919 = 3218879) B3218879
theorem B1810927 : Blo 1270453 1810927 := bstep (se 1 (by rfl) ⟨1358195, by rfl⟩ : syracuseStep 1810927 = 2716391) B2716391
theorem B2861225 : Blo 1270453 2861225 := bstep (se 2 (by rfl) ⟨1072959, by rfl⟩ : syracuseStep 2861225 = 2145919) B2145919
theorem B24153079 : Blo 1270453 24153079 := bstep (se 1 (by rfl) ⟨18114809, by rfl⟩ : syracuseStep 24153079 = 36229619) B36229619
theorem B11751571 : Blo 1270453 11751571 := bstep (se 1 (by rfl) ⟨8813678, by rfl⟩ : syracuseStep 11751571 = 17627357) B17627357
theorem B61174399 : Blo 1270453 61174399 := bstep (se 1 (by rfl) ⟨45880799, by rfl⟩ : syracuseStep 61174399 = 91761599) B91761599
theorem B1906751 : Blo 1270453 1906751 := bstep (se 1 (by rfl) ⟨1430063, by rfl⟩ : syracuseStep 1906751 = 2860127) B2860127
theorem B7240063 : Blo 1270453 7240063 := bstep (se 1 (by rfl) ⟨5430047, by rfl⟩ : syracuseStep 7240063 = 10860095) B10860095
theorem B9411155 : Blo 1270453 9411155 := bstep (se 1 (by rfl) ⟨7058366, by rfl⟩ : syracuseStep 9411155 = 14116733) B14116733
theorem B27492047 : Blo 1270453 27492047 := bstep (se 1 (by rfl) ⟨20619035, by rfl⟩ : syracuseStep 27492047 = 41238071) B41238071
theorem B32204105 : Blo 1270453 32204105 := bstep (se 2 (by rfl) ⟨12076539, by rfl⟩ : syracuseStep 32204105 = 24153079) B24153079
theorem B1271167 : Blo 1270453 1271167 := bstep (se 1 (by rfl) ⟨953375, by rfl⟩ : syracuseStep 1271167 = 1906751) B1906751
theorem B18328031 : Blo 1270453 18328031 := bstep (se 1 (by rfl) ⟨13746023, by rfl⟩ : syracuseStep 18328031 = 27492047) B27492047
theorem B9653417 : Blo 1270453 9653417 := bstep (se 2 (by rfl) ⟨3620031, by rfl⟩ : syracuseStep 9653417 = 7240063) B7240063
theorem B15668761 : Blo 1270453 15668761 := bstep (se 2 (by rfl) ⟨5875785, by rfl⟩ : syracuseStep 15668761 = 11751571) B11751571
theorem B81565865 : Blo 1270453 81565865 := bstep (se 2 (by rfl) ⟨30587199, by rfl⟩ : syracuseStep 81565865 = 61174399) B61174399
theorem B1907483 : Blo 1270453 1907483 := bstep (se 1 (by rfl) ⟨1430612, by rfl⟩ : syracuseStep 1907483 = 2861225) B2861225
theorem B6274103 : Blo 1270453 6274103 := bstep (se 1 (by rfl) ⟨4705577, by rfl⟩ : syracuseStep 6274103 = 9411155) B9411155
theorem B9658277 : Blo 1270453 9658277 := bstep (se 4 (by rfl) ⟨905463, by rfl⟩ : syracuseStep 9658277 = 1810927) B1810927
theorem B1271655 : Blo 1270453 1271655 := bstep (se 1 (by rfl) ⟨953741, by rfl⟩ : syracuseStep 1271655 = 1907483) B1907483
theorem B20891681 : Blo 1270453 20891681 := bstep (se 2 (by rfl) ⟨7834380, by rfl⟩ : syracuseStep 20891681 = 15668761) B15668761
theorem B66923765 : Blo 1270453 66923765 := bstep (se 5 (by rfl) ⟨3137051, by rfl⟩ : syracuseStep 66923765 = 6274103) B6274103
theorem B12218687 : Blo 1270453 12218687 := bstep (se 1 (by rfl) ⟨9164015, by rfl⟩ : syracuseStep 12218687 = 18328031) B18328031
theorem B6435611 : Blo 1270453 6435611 := bstep (se 1 (by rfl) ⟨4826708, by rfl⟩ : syracuseStep 6435611 = 9653417) B9653417
theorem B21469403 : Blo 1270453 21469403 := bstep (se 1 (by rfl) ⟨16102052, by rfl⟩ : syracuseStep 21469403 = 32204105) B32204105
theorem B54377243 : Blo 1270453 54377243 := bstep (se 1 (by rfl) ⟨40782932, by rfl⟩ : syracuseStep 54377243 = 81565865) B81565865
theorem B6438851 : Blo 1270453 6438851 := bstep (se 1 (by rfl) ⟨4829138, by rfl⟩ : syracuseStep 6438851 = 9658277) B9658277
theorem B13927787 : Blo 1270453 13927787 := bstep (se 1 (by rfl) ⟨10445840, by rfl⟩ : syracuseStep 13927787 = 20891681) B20891681
theorem B14312935 : Blo 1270453 14312935 := bstep (se 1 (by rfl) ⟨10734701, by rfl⟩ : syracuseStep 14312935 = 21469403) B21469403
theorem B36251495 : Blo 1270453 36251495 := bstep (se 1 (by rfl) ⟨27188621, by rfl⟩ : syracuseStep 36251495 = 54377243) B54377243
theorem B44615843 : Blo 1270453 44615843 := bstep (se 1 (by rfl) ⟨33461882, by rfl⟩ : syracuseStep 44615843 = 66923765) B66923765
theorem B8145791 : Blo 1270453 8145791 := bstep (se 1 (by rfl) ⟨6109343, by rfl⟩ : syracuseStep 8145791 = 12218687) B12218687
theorem B4290407 : Blo 1270453 4290407 := bstep (se 1 (by rfl) ⟨3217805, by rfl⟩ : syracuseStep 4290407 = 6435611) B6435611
theorem B4292567 : Blo 1270453 4292567 := bstep (se 1 (by rfl) ⟨3219425, by rfl⟩ : syracuseStep 4292567 = 6438851) B6438851
theorem B2860271 : Blo 1270453 2860271 := bstep (se 1 (by rfl) ⟨2145203, by rfl⟩ : syracuseStep 2860271 = 4290407) B4290407
theorem B24167663 : Blo 1270453 24167663 := bstep (se 1 (by rfl) ⟨18125747, by rfl⟩ : syracuseStep 24167663 = 36251495) B36251495
theorem B76335653 : Blo 1270453 76335653 := bstep (se 4 (by rfl) ⟨7156467, by rfl⟩ : syracuseStep 76335653 = 14312935) B14312935
theorem B2861711 : Blo 1270453 2861711 := bstep (se 1 (by rfl) ⟨2146283, by rfl⟩ : syracuseStep 2861711 = 4292567) B4292567
theorem B9285191 : Blo 1270453 9285191 := bstep (se 1 (by rfl) ⟨6963893, by rfl⟩ : syracuseStep 9285191 = 13927787) B13927787
theorem B29743895 : Blo 1270453 29743895 := bstep (se 1 (by rfl) ⟨22307921, by rfl⟩ : syracuseStep 29743895 = 44615843) B44615843
theorem B5430527 : Blo 1270453 5430527 := bstep (se 1 (by rfl) ⟨4072895, by rfl⟩ : syracuseStep 5430527 = 8145791) B8145791
theorem B79317053 : Blo 1270453 79317053 := bstep (se 3 (by rfl) ⟨14871947, by rfl⟩ : syracuseStep 79317053 = 29743895) B29743895
theorem B6190127 : Blo 1270453 6190127 := bstep (se 1 (by rfl) ⟨4642595, by rfl⟩ : syracuseStep 6190127 = 9285191) B9285191
theorem B1906847 : Blo 1270453 1906847 := bstep (se 1 (by rfl) ⟨1430135, by rfl⟩ : syracuseStep 1906847 = 2860271) B2860271
theorem B16111775 : Blo 1270453 16111775 := bstep (se 1 (by rfl) ⟨12083831, by rfl⟩ : syracuseStep 16111775 = 24167663) B24167663
theorem B203561741 : Blo 1270453 203561741 := bstep (se 3 (by rfl) ⟨38167826, by rfl⟩ : syracuseStep 203561741 = 76335653) B76335653
theorem B1907807 : Blo 1270453 1907807 := bstep (se 1 (by rfl) ⟨1430855, by rfl⟩ : syracuseStep 1907807 = 2861711) B2861711
theorem B3620351 : Blo 1270453 3620351 := bstep (se 1 (by rfl) ⟨2715263, by rfl⟩ : syracuseStep 3620351 = 5430527) B5430527
theorem B1271231 : Blo 1270453 1271231 := bstep (se 1 (by rfl) ⟨953423, by rfl⟩ : syracuseStep 1271231 = 1906847) B1906847
theorem B10741183 : Blo 1270453 10741183 := bstep (se 1 (by rfl) ⟨8055887, by rfl⟩ : syracuseStep 10741183 = 16111775) B16111775
theorem B1271871 : Blo 1270453 1271871 := bstep (se 1 (by rfl) ⟨953903, by rfl⟩ : syracuseStep 1271871 = 1907807) B1907807
theorem B2413567 : Blo 1270453 2413567 := bstep (se 1 (by rfl) ⟨1810175, by rfl⟩ : syracuseStep 2413567 = 3620351) B3620351
theorem B4126751 : Blo 1270453 4126751 := bstep (se 1 (by rfl) ⟨3095063, by rfl⟩ : syracuseStep 4126751 = 6190127) B6190127
theorem B52878035 : Blo 1270453 52878035 := bstep (se 1 (by rfl) ⟨39658526, by rfl⟩ : syracuseStep 52878035 = 79317053) B79317053
theorem B135707827 : Blo 1270453 135707827 := bstep (se 1 (by rfl) ⟨101780870, by rfl⟩ : syracuseStep 135707827 = 203561741) B203561741
theorem B35252023 : Blo 1270453 35252023 := bstep (se 1 (by rfl) ⟨26439017, by rfl⟩ : syracuseStep 35252023 = 52878035) B52878035
theorem B3218089 : Blo 1270453 3218089 := bstep (se 2 (by rfl) ⟨1206783, by rfl⟩ : syracuseStep 3218089 = 2413567) B2413567
theorem B2751167 : Blo 1270453 2751167 := bstep (se 1 (by rfl) ⟨2063375, by rfl⟩ : syracuseStep 2751167 = 4126751) B4126751
theorem B180943769 : Blo 1270453 180943769 := bstep (se 2 (by rfl) ⟨67853913, by rfl⟩ : syracuseStep 180943769 = 135707827) B135707827
theorem B57286309 : Blo 1270453 57286309 := bstep (se 4 (by rfl) ⟨5370591, by rfl⟩ : syracuseStep 57286309 = 10741183) B10741183
theorem B120629179 : Blo 1270453 120629179 := bstep (se 1 (by rfl) ⟨90471884, by rfl⟩ : syracuseStep 120629179 = 180943769) B180943769
theorem B47002697 : Blo 1270453 47002697 := bstep (se 2 (by rfl) ⟨17626011, by rfl⟩ : syracuseStep 47002697 = 35252023) B35252023
theorem B4290785 : Blo 1270453 4290785 := bstep (se 2 (by rfl) ⟨1609044, by rfl⟩ : syracuseStep 4290785 = 3218089) B3218089
theorem B1834111 : Blo 1270453 1834111 := bstep (se 1 (by rfl) ⟨1375583, by rfl⟩ : syracuseStep 1834111 = 2751167) B2751167
theorem B76381745 : Blo 1270453 76381745 := bstep (se 2 (by rfl) ⟨28643154, by rfl⟩ : syracuseStep 76381745 = 57286309) B57286309
theorem B31335131 : Blo 1270453 31335131 := bstep (se 1 (by rfl) ⟨23501348, by rfl⟩ : syracuseStep 31335131 = 47002697) B47002697
theorem B2860523 : Blo 1270453 2860523 := bstep (se 1 (by rfl) ⟨2145392, by rfl⟩ : syracuseStep 2860523 = 4290785) B4290785
theorem B2445481 : Blo 1270453 2445481 := bstep (se 2 (by rfl) ⟨917055, by rfl⟩ : syracuseStep 2445481 = 1834111) B1834111
theorem B643355621 : Blo 1270453 643355621 := bstep (se 4 (by rfl) ⟨60314589, by rfl⟩ : syracuseStep 643355621 = 120629179) B120629179
theorem B203684653 : Blo 1270453 203684653 := bstep (se 3 (by rfl) ⟨38190872, by rfl⟩ : syracuseStep 203684653 = 76381745) B76381745
theorem B13042565 : Blo 1270453 13042565 := bstep (se 4 (by rfl) ⟨1222740, by rfl⟩ : syracuseStep 13042565 = 2445481) B2445481
theorem B83560349 : Blo 1270453 83560349 := bstep (se 3 (by rfl) ⟨15667565, by rfl⟩ : syracuseStep 83560349 = 31335131) B31335131
theorem B428903747 : Blo 1270453 428903747 := bstep (se 1 (by rfl) ⟨321677810, by rfl⟩ : syracuseStep 428903747 = 643355621) B643355621
theorem B1907015 : Blo 1270453 1907015 := bstep (se 1 (by rfl) ⟨1430261, by rfl⟩ : syracuseStep 1907015 = 2860523) B2860523
theorem B271579537 : Blo 1270453 271579537 := bstep (se 2 (by rfl) ⟨101842326, by rfl⟩ : syracuseStep 271579537 = 203684653) B203684653
theorem B55706899 : Blo 1270453 55706899 := bstep (se 1 (by rfl) ⟨41780174, by rfl⟩ : syracuseStep 55706899 = 83560349) B83560349
theorem B1271343 : Blo 1270453 1271343 := bstep (se 1 (by rfl) ⟨953507, by rfl⟩ : syracuseStep 1271343 = 1907015) B1907015
theorem B285935831 : Blo 1270453 285935831 := bstep (se 1 (by rfl) ⟨214451873, by rfl⟩ : syracuseStep 285935831 = 428903747) B428903747
theorem B362106049 : Blo 1270453 362106049 := bstep (se 2 (by rfl) ⟨135789768, by rfl⟩ : syracuseStep 362106049 = 271579537) B271579537
theorem B8695043 : Blo 1270453 8695043 := bstep (se 1 (by rfl) ⟨6521282, by rfl⟩ : syracuseStep 8695043 = 13042565) B13042565
theorem B190623887 : Blo 1270453 190623887 := bstep (se 1 (by rfl) ⟨142967915, by rfl⟩ : syracuseStep 190623887 = 285935831) B285935831
theorem B482808065 : Blo 1270453 482808065 := bstep (se 2 (by rfl) ⟨181053024, by rfl⟩ : syracuseStep 482808065 = 362106049) B362106049
theorem B5796695 : Blo 1270453 5796695 := bstep (se 1 (by rfl) ⟨4347521, by rfl⟩ : syracuseStep 5796695 = 8695043) B8695043
theorem B74275865 : Blo 1270453 74275865 := bstep (se 2 (by rfl) ⟨27853449, by rfl⟩ : syracuseStep 74275865 = 55706899) B55706899
theorem B127082591 : Blo 1270453 127082591 := bstep (se 1 (by rfl) ⟨95311943, by rfl⟩ : syracuseStep 127082591 = 190623887) B190623887
theorem B5149952693 : Blo 1270453 5149952693 := bstep (se 5 (by rfl) ⟨241404032, by rfl⟩ : syracuseStep 5149952693 = 482808065) B482808065
theorem B49517243 : Blo 1270453 49517243 := bstep (se 1 (by rfl) ⟨37137932, by rfl⟩ : syracuseStep 49517243 = 74275865) B74275865
theorem B15457853 : Blo 1270453 15457853 := bstep (se 3 (by rfl) ⟨2898347, by rfl⟩ : syracuseStep 15457853 = 5796695) B5796695
theorem B84721727 : Blo 1270453 84721727 := bstep (se 1 (by rfl) ⟨63541295, by rfl⟩ : syracuseStep 84721727 = 127082591) B127082591
theorem B3433301795 : Blo 1270453 3433301795 := bstep (se 1 (by rfl) ⟨2574976346, by rfl⟩ : syracuseStep 3433301795 = 5149952693) B5149952693
theorem B33011495 : Blo 1270453 33011495 := bstep (se 1 (by rfl) ⟨24758621, by rfl⟩ : syracuseStep 33011495 = 49517243) B49517243
theorem B10305235 : Blo 1270453 10305235 := bstep (se 1 (by rfl) ⟨7728926, by rfl⟩ : syracuseStep 10305235 = 15457853) B15457853
theorem B13740313 : Blo 1270453 13740313 := bstep (se 2 (by rfl) ⟨5152617, by rfl⟩ : syracuseStep 13740313 = 10305235) B10305235
theorem B22007663 : Blo 1270453 22007663 := bstep (se 1 (by rfl) ⟨16505747, by rfl⟩ : syracuseStep 22007663 = 33011495) B33011495
theorem B56481151 : Blo 1270453 56481151 := bstep (se 1 (by rfl) ⟨42360863, by rfl⟩ : syracuseStep 56481151 = 84721727) B84721727
theorem B2288867863 : Blo 1270453 2288867863 := bstep (se 1 (by rfl) ⟨1716650897, by rfl⟩ : syracuseStep 2288867863 = 3433301795) B3433301795
theorem B3051823817 : Blo 1270453 3051823817 := bstep (se 2 (by rfl) ⟨1144433931, by rfl⟩ : syracuseStep 3051823817 = 2288867863) B2288867863
theorem B18320417 : Blo 1270453 18320417 := bstep (se 2 (by rfl) ⟨6870156, by rfl⟩ : syracuseStep 18320417 = 13740313) B13740313
theorem B75308201 : Blo 1270453 75308201 := bstep (se 2 (by rfl) ⟨28240575, by rfl⟩ : syracuseStep 75308201 = 56481151) B56481151
theorem B14671775 : Blo 1270453 14671775 := bstep (se 1 (by rfl) ⟨11003831, by rfl⟩ : syracuseStep 14671775 = 22007663) B22007663
theorem B8138196845 : Blo 1270453 8138196845 := bstep (se 3 (by rfl) ⟨1525911908, by rfl⟩ : syracuseStep 8138196845 = 3051823817) B3051823817
theorem B50205467 : Blo 1270453 50205467 := bstep (se 1 (by rfl) ⟨37654100, by rfl⟩ : syracuseStep 50205467 = 75308201) B75308201
theorem B12213611 : Blo 1270453 12213611 := bstep (se 1 (by rfl) ⟨9160208, by rfl⟩ : syracuseStep 12213611 = 18320417) B18320417
theorem B9781183 : Blo 1270453 9781183 := bstep (se 1 (by rfl) ⟨7335887, by rfl⟩ : syracuseStep 9781183 = 14671775) B14671775
theorem B5425464563 : Blo 1270453 5425464563 := bstep (se 1 (by rfl) ⟨4069098422, by rfl⟩ : syracuseStep 5425464563 = 8138196845) B8138196845
theorem B133881245 : Blo 1270453 133881245 := bstep (se 3 (by rfl) ⟨25102733, by rfl⟩ : syracuseStep 133881245 = 50205467) B50205467
theorem B8142407 : Blo 1270453 8142407 := bstep (se 1 (by rfl) ⟨6106805, by rfl⟩ : syracuseStep 8142407 = 12213611) B12213611
theorem B13041577 : Blo 1270453 13041577 := bstep (se 2 (by rfl) ⟨4890591, by rfl⟩ : syracuseStep 13041577 = 9781183) B9781183
theorem B89254163 : Blo 1270453 89254163 := bstep (se 1 (by rfl) ⟨66940622, by rfl⟩ : syracuseStep 89254163 = 133881245) B133881245
theorem B3616976375 : Blo 1270453 3616976375 := bstep (se 1 (by rfl) ⟨2712732281, by rfl⟩ : syracuseStep 3616976375 = 5425464563) B5425464563
theorem B5428271 : Blo 1270453 5428271 := bstep (se 1 (by rfl) ⟨4071203, by rfl⟩ : syracuseStep 5428271 = 8142407) B8142407
theorem B17388769 : Blo 1270453 17388769 := bstep (se 2 (by rfl) ⟨6520788, by rfl⟩ : syracuseStep 17388769 = 13041577) B13041577
theorem B23185025 : Blo 1270453 23185025 := bstep (se 2 (by rfl) ⟨8694384, by rfl⟩ : syracuseStep 23185025 = 17388769) B17388769
theorem B2411317583 : Blo 1270453 2411317583 := bstep (se 1 (by rfl) ⟨1808488187, by rfl⟩ : syracuseStep 2411317583 = 3616976375) B3616976375
theorem B59502775 : Blo 1270453 59502775 := bstep (se 1 (by rfl) ⟨44627081, by rfl⟩ : syracuseStep 59502775 = 89254163) B89254163
theorem B3618847 : Blo 1270453 3618847 := bstep (se 1 (by rfl) ⟨2714135, by rfl⟩ : syracuseStep 3618847 = 5428271) B5428271
theorem B4825129 : Blo 1270453 4825129 := bstep (se 2 (by rfl) ⟨1809423, by rfl⟩ : syracuseStep 4825129 = 3618847) B3618847
theorem B1607545055 : Blo 1270453 1607545055 := bstep (se 1 (by rfl) ⟨1205658791, by rfl⟩ : syracuseStep 1607545055 = 2411317583) B2411317583
theorem B79337033 : Blo 1270453 79337033 := bstep (se 2 (by rfl) ⟨29751387, by rfl⟩ : syracuseStep 79337033 = 59502775) B59502775
theorem B15456683 : Blo 1270453 15456683 := bstep (se 1 (by rfl) ⟨11592512, by rfl⟩ : syracuseStep 15456683 = 23185025) B23185025
theorem B6433505 : Blo 1270453 6433505 := bstep (se 2 (by rfl) ⟨2412564, by rfl⟩ : syracuseStep 6433505 = 4825129) B4825129
theorem B1071696703 : Blo 1270453 1071696703 := bstep (se 1 (by rfl) ⟨803772527, by rfl⟩ : syracuseStep 1071696703 = 1607545055) B1607545055
theorem B52891355 : Blo 1270453 52891355 := bstep (se 1 (by rfl) ⟨39668516, by rfl⟩ : syracuseStep 52891355 = 79337033) B79337033
theorem B41217821 : Blo 1270453 41217821 := bstep (se 3 (by rfl) ⟨7728341, by rfl⟩ : syracuseStep 41217821 = 15456683) B15456683
theorem B35260903 : Blo 1270453 35260903 := bstep (se 1 (by rfl) ⟨26445677, by rfl⟩ : syracuseStep 35260903 = 52891355) B52891355
theorem B27478547 : Blo 1270453 27478547 := bstep (se 1 (by rfl) ⟨20608910, by rfl⟩ : syracuseStep 27478547 = 41217821) B41217821
theorem B4289003 : Blo 1270453 4289003 := bstep (se 1 (by rfl) ⟨3216752, by rfl⟩ : syracuseStep 4289003 = 6433505) B6433505
theorem B1428928937 : Blo 1270453 1428928937 := bstep (se 2 (by rfl) ⟨535848351, by rfl⟩ : syracuseStep 1428928937 = 1071696703) B1071696703
theorem B2859335 : Blo 1270453 2859335 := bstep (se 1 (by rfl) ⟨2144501, by rfl⟩ : syracuseStep 2859335 = 4289003) B4289003
theorem B18319031 : Blo 1270453 18319031 := bstep (se 1 (by rfl) ⟨13739273, by rfl⟩ : syracuseStep 18319031 = 27478547) B27478547
theorem B188058149 : Blo 1270453 188058149 := bstep (se 4 (by rfl) ⟨17630451, by rfl⟩ : syracuseStep 188058149 = 35260903) B35260903
theorem B952619291 : Blo 1270453 952619291 := bstep (se 1 (by rfl) ⟨714464468, by rfl⟩ : syracuseStep 952619291 = 1428928937) B1428928937
theorem B125372099 : Blo 1270453 125372099 := bstep (se 1 (by rfl) ⟨94029074, by rfl⟩ : syracuseStep 125372099 = 188058149) B188058149
theorem B635079527 : Blo 1270453 635079527 := bstep (se 1 (by rfl) ⟨476309645, by rfl⟩ : syracuseStep 635079527 = 952619291) B952619291
theorem B1906223 : Blo 1270453 1906223 := bstep (se 1 (by rfl) ⟨1429667, by rfl⟩ : syracuseStep 1906223 = 2859335) B2859335
theorem B12212687 : Blo 1270453 12212687 := bstep (se 1 (by rfl) ⟨9159515, by rfl⟩ : syracuseStep 12212687 = 18319031) B18319031
theorem B1270815 : Blo 1270453 1270815 := bstep (se 1 (by rfl) ⟨953111, by rfl⟩ : syracuseStep 1270815 = 1906223) B1906223
theorem B83581399 : Blo 1270453 83581399 := bstep (se 1 (by rfl) ⟨62686049, by rfl⟩ : syracuseStep 83581399 = 125372099) B125372099
theorem B8141791 : Blo 1270453 8141791 := bstep (se 1 (by rfl) ⟨6106343, by rfl⟩ : syracuseStep 8141791 = 12212687) B12212687
theorem B423386351 : Blo 1270453 423386351 := bstep (se 1 (by rfl) ⟨317539763, by rfl⟩ : syracuseStep 423386351 = 635079527) B635079527
theorem B10855721 : Blo 1270453 10855721 := bstep (se 2 (by rfl) ⟨4070895, by rfl⟩ : syracuseStep 10855721 = 8141791) B8141791
theorem B282257567 : Blo 1270453 282257567 := bstep (se 1 (by rfl) ⟨211693175, by rfl⟩ : syracuseStep 282257567 = 423386351) B423386351
theorem B111441865 : Blo 1270453 111441865 := bstep (se 2 (by rfl) ⟨41790699, by rfl⟩ : syracuseStep 111441865 = 83581399) B83581399
theorem B188171711 : Blo 1270453 188171711 := bstep (se 1 (by rfl) ⟨141128783, by rfl⟩ : syracuseStep 188171711 = 282257567) B282257567
theorem B148589153 : Blo 1270453 148589153 := bstep (se 2 (by rfl) ⟨55720932, by rfl⟩ : syracuseStep 148589153 = 111441865) B111441865
theorem B7237147 : Blo 1270453 7237147 := bstep (se 1 (by rfl) ⟨5427860, by rfl⟩ : syracuseStep 7237147 = 10855721) B10855721
theorem B99059435 : Blo 1270453 99059435 := bstep (se 1 (by rfl) ⟨74294576, by rfl⟩ : syracuseStep 99059435 = 148589153) B148589153
theorem B125447807 : Blo 1270453 125447807 := bstep (se 1 (by rfl) ⟨94085855, by rfl⟩ : syracuseStep 125447807 = 188171711) B188171711
theorem B9649529 : Blo 1270453 9649529 := bstep (se 2 (by rfl) ⟨3618573, by rfl⟩ : syracuseStep 9649529 = 7237147) B7237147
theorem B6433019 : Blo 1270453 6433019 := bstep (se 1 (by rfl) ⟨4824764, by rfl⟩ : syracuseStep 6433019 = 9649529) B9649529
theorem B66039623 : Blo 1270453 66039623 := bstep (se 1 (by rfl) ⟨49529717, by rfl⟩ : syracuseStep 66039623 = 99059435) B99059435
theorem B83631871 : Blo 1270453 83631871 := bstep (se 1 (by rfl) ⟨62723903, by rfl⟩ : syracuseStep 83631871 = 125447807) B125447807
theorem B44026415 : Blo 1270453 44026415 := bstep (se 1 (by rfl) ⟨33019811, by rfl⟩ : syracuseStep 44026415 = 66039623) B66039623
theorem B4288679 : Blo 1270453 4288679 := bstep (se 1 (by rfl) ⟨3216509, by rfl⟩ : syracuseStep 4288679 = 6433019) B6433019
theorem B446036645 : Blo 1270453 446036645 := bstep (se 4 (by rfl) ⟨41815935, by rfl⟩ : syracuseStep 446036645 = 83631871) B83631871
theorem B2859119 : Blo 1270453 2859119 := bstep (se 1 (by rfl) ⟨2144339, by rfl⟩ : syracuseStep 2859119 = 4288679) B4288679
theorem B297357763 : Blo 1270453 297357763 := bstep (se 1 (by rfl) ⟨223018322, by rfl⟩ : syracuseStep 297357763 = 446036645) B446036645
theorem B29350943 : Blo 1270453 29350943 := bstep (se 1 (by rfl) ⟨22013207, by rfl⟩ : syracuseStep 29350943 = 44026415) B44026415
theorem B396477017 : Blo 1270453 396477017 := bstep (se 2 (by rfl) ⟨148678881, by rfl⟩ : syracuseStep 396477017 = 297357763) B297357763
theorem B19567295 : Blo 1270453 19567295 := bstep (se 1 (by rfl) ⟨14675471, by rfl⟩ : syracuseStep 19567295 = 29350943) B29350943
theorem B1906079 : Blo 1270453 1906079 := bstep (se 1 (by rfl) ⟨1429559, by rfl⟩ : syracuseStep 1906079 = 2859119) B2859119
theorem B1270719 : Blo 1270453 1270719 := bstep (se 1 (by rfl) ⟨953039, by rfl⟩ : syracuseStep 1270719 = 1906079) B1906079
theorem B264318011 : Blo 1270453 264318011 := bstep (se 1 (by rfl) ⟨198238508, by rfl⟩ : syracuseStep 264318011 = 396477017) B396477017
theorem B13044863 : Blo 1270453 13044863 := bstep (se 1 (by rfl) ⟨9783647, by rfl⟩ : syracuseStep 13044863 = 19567295) B19567295
theorem B176212007 : Blo 1270453 176212007 := bstep (se 1 (by rfl) ⟨132159005, by rfl⟩ : syracuseStep 176212007 = 264318011) B264318011
theorem B8696575 : Blo 1270453 8696575 := bstep (se 1 (by rfl) ⟨6522431, by rfl⟩ : syracuseStep 8696575 = 13044863) B13044863
theorem B117474671 : Blo 1270453 117474671 := bstep (se 1 (by rfl) ⟨88106003, by rfl⟩ : syracuseStep 117474671 = 176212007) B176212007
theorem B11595433 : Blo 1270453 11595433 := bstep (se 2 (by rfl) ⟨4348287, by rfl⟩ : syracuseStep 11595433 = 8696575) B8696575
theorem B15460577 : Blo 1270453 15460577 := bstep (se 2 (by rfl) ⟨5797716, by rfl⟩ : syracuseStep 15460577 = 11595433) B11595433
theorem B313265789 : Blo 1270453 313265789 := bstep (se 3 (by rfl) ⟨58737335, by rfl⟩ : syracuseStep 313265789 = 117474671) B117474671
theorem B10307051 : Blo 1270453 10307051 := bstep (se 1 (by rfl) ⟨7730288, by rfl⟩ : syracuseStep 10307051 = 15460577) B15460577
theorem B208843859 : Blo 1270453 208843859 := bstep (se 1 (by rfl) ⟨156632894, by rfl⟩ : syracuseStep 208843859 = 313265789) B313265789
theorem B139229239 : Blo 1270453 139229239 := bstep (se 1 (by rfl) ⟨104421929, by rfl⟩ : syracuseStep 139229239 = 208843859) B208843859
theorem B6871367 : Blo 1270453 6871367 := bstep (se 1 (by rfl) ⟨5153525, by rfl⟩ : syracuseStep 6871367 = 10307051) B10307051
theorem B185638985 : Blo 1270453 185638985 := bstep (se 2 (by rfl) ⟨69614619, by rfl⟩ : syracuseStep 185638985 = 139229239) B139229239
theorem B4580911 : Blo 1270453 4580911 := bstep (se 1 (by rfl) ⟨3435683, by rfl⟩ : syracuseStep 4580911 = 6871367) B6871367
theorem B123759323 : Blo 1270453 123759323 := bstep (se 1 (by rfl) ⟨92819492, by rfl⟩ : syracuseStep 123759323 = 185638985) B185638985
theorem B6107881 : Blo 1270453 6107881 := bstep (se 2 (by rfl) ⟨2290455, by rfl⟩ : syracuseStep 6107881 = 4580911) B4580911
theorem B8143841 : Blo 1270453 8143841 := bstep (se 2 (by rfl) ⟨3053940, by rfl⟩ : syracuseStep 8143841 = 6107881) B6107881
theorem B82506215 : Blo 1270453 82506215 := bstep (se 1 (by rfl) ⟨61879661, by rfl⟩ : syracuseStep 82506215 = 123759323) B123759323
theorem B55004143 : Blo 1270453 55004143 := bstep (se 1 (by rfl) ⟨41253107, by rfl⟩ : syracuseStep 55004143 = 82506215) B82506215
theorem B21716909 : Blo 1270453 21716909 := bstep (se 3 (by rfl) ⟨4071920, by rfl⟩ : syracuseStep 21716909 = 8143841) B8143841
theorem B14477939 : Blo 1270453 14477939 := bstep (se 1 (by rfl) ⟨10858454, by rfl⟩ : syracuseStep 14477939 = 21716909) B21716909
theorem B73338857 : Blo 1270453 73338857 := bstep (se 2 (by rfl) ⟨27502071, by rfl⟩ : syracuseStep 73338857 = 55004143) B55004143
theorem B9651959 : Blo 1270453 9651959 := bstep (se 1 (by rfl) ⟨7238969, by rfl⟩ : syracuseStep 9651959 = 14477939) B14477939
theorem B48892571 : Blo 1270453 48892571 := bstep (se 1 (by rfl) ⟨36669428, by rfl⟩ : syracuseStep 48892571 = 73338857) B73338857
theorem B6434639 : Blo 1270453 6434639 := bstep (se 1 (by rfl) ⟨4825979, by rfl⟩ : syracuseStep 6434639 = 9651959) B9651959
theorem B32595047 : Blo 1270453 32595047 := bstep (se 1 (by rfl) ⟨24446285, by rfl⟩ : syracuseStep 32595047 = 48892571) B48892571
theorem B21730031 : Blo 1270453 21730031 := bstep (se 1 (by rfl) ⟨16297523, by rfl⟩ : syracuseStep 21730031 = 32595047) B32595047
theorem B4289759 : Blo 1270453 4289759 := bstep (se 1 (by rfl) ⟨3217319, by rfl⟩ : syracuseStep 4289759 = 6434639) B6434639
theorem B2859839 : Blo 1270453 2859839 := bstep (se 1 (by rfl) ⟨2144879, by rfl⟩ : syracuseStep 2859839 = 4289759) B4289759
theorem B14486687 : Blo 1270453 14486687 := bstep (se 1 (by rfl) ⟨10865015, by rfl⟩ : syracuseStep 14486687 = 21730031) B21730031
theorem B1906559 : Blo 1270453 1906559 := bstep (se 1 (by rfl) ⟨1429919, by rfl⟩ : syracuseStep 1906559 = 2859839) B2859839
theorem B9657791 : Blo 1270453 9657791 := bstep (se 1 (by rfl) ⟨7243343, by rfl⟩ : syracuseStep 9657791 = 14486687) B14486687
theorem B1271039 : Blo 1270453 1271039 := bstep (se 1 (by rfl) ⟨953279, by rfl⟩ : syracuseStep 1271039 = 1906559) B1906559
theorem B6438527 : Blo 1270453 6438527 := bstep (se 1 (by rfl) ⟨4828895, by rfl⟩ : syracuseStep 6438527 = 9657791) B9657791
theorem B4292351 : Blo 1270453 4292351 := bstep (se 1 (by rfl) ⟨3219263, by rfl⟩ : syracuseStep 4292351 = 6438527) B6438527
theorem B2861567 : Blo 1270453 2861567 := bstep (se 1 (by rfl) ⟨2146175, by rfl⟩ : syracuseStep 2861567 = 4292351) B4292351
theorem B1907711 : Blo 1270453 1907711 := bstep (se 1 (by rfl) ⟨1430783, by rfl⟩ : syracuseStep 1907711 = 2861567) B2861567
theorem B1271807 : Blo 1270453 1271807 := bstep (se 1 (by rfl) ⟨953855, by rfl⟩ : syracuseStep 1271807 = 1907711) B1907711

theorem C0 (j : ℕ) (h1 : 317613 ≤ j) (h2 : j ≤ 317987) : Blo 1270453 (4 * j + 3) := by
  interval_cases j
  · exact B1270455
  · exact B1270459
  · exact B1270463
  · exact B1270467
  · exact B1270471
  · exact B1270475
  · exact B1270479
  · exact B1270483
  · exact B1270487
  · exact B1270491
  · exact B1270495
  · exact B1270499
  · exact B1270503
  · exact B1270507
  · exact B1270511
  · exact B1270515
  · exact B1270519
  · exact B1270523
  · exact B1270527
  · exact B1270531
  · exact B1270535
  · exact B1270539
  · exact B1270543
  · exact B1270547
  · exact B1270551
  · exact B1270555
  · exact B1270559
  · exact B1270563
  · exact B1270567
  · exact B1270571
  · exact B1270575
  · exact B1270579
  · exact B1270583
  · exact B1270587
  · exact B1270591
  · exact B1270595
  · exact B1270599
  · exact B1270603
  · exact B1270607
  · exact B1270611
  · exact B1270615
  · exact B1270619
  · exact B1270623
  · exact B1270627
  · exact B1270631
  · exact B1270635
  · exact B1270639
  · exact B1270643
  · exact B1270647
  · exact B1270651
  · exact B1270655
  · exact B1270659
  · exact B1270663
  · exact B1270667
  · exact B1270671
  · exact B1270675
  · exact B1270679
  · exact B1270683
  · exact B1270687
  · exact B1270691
  · exact B1270695
  · exact B1270699
  · exact B1270703
  · exact B1270707
  · exact B1270711
  · exact B1270715
  · exact B1270719
  · exact B1270723
  · exact B1270727
  · exact B1270731
  · exact B1270735
  · exact B1270739
  · exact B1270743
  · exact B1270747
  · exact B1270751
  · exact B1270755
  · exact B1270759
  · exact B1270763
  · exact B1270767
  · exact B1270771
  · exact B1270775
  · exact B1270779
  · exact B1270783
  · exact B1270787
  · exact B1270791
  · exact B1270795
  · exact B1270799
  · exact B1270803
  · exact B1270807
  · exact B1270811
  · exact B1270815
  · exact B1270819
  · exact B1270823
  · exact B1270827
  · exact B1270831
  · exact B1270835
  · exact B1270839
  · exact B1270843
  · exact B1270847
  · exact B1270851
  · exact B1270855
  · exact B1270859
  · exact B1270863
  · exact B1270867
  · exact B1270871
  · exact B1270875
  · exact B1270879
  · exact B1270883
  · exact B1270887
  · exact B1270891
  · exact B1270895
  · exact B1270899
  · exact B1270903
  · exact B1270907
  · exact B1270911
  · exact B1270915
  · exact B1270919
  · exact B1270923
  · exact B1270927
  · exact B1270931
  · exact B1270935
  · exact B1270939
  · exact B1270943
  · exact B1270947
  · exact B1270951
  · exact B1270955
  · exact B1270959
  · exact B1270963
  · exact B1270967
  · exact B1270971
  · exact B1270975
  · exact B1270979
  · exact B1270983
  · exact B1270987
  · exact B1270991
  · exact B1270995
  · exact B1270999
  · exact B1271003
  · exact B1271007
  · exact B1271011
  · exact B1271015
  · exact B1271019
  · exact B1271023
  · exact B1271027
  · exact B1271031
  · exact B1271035
  · exact B1271039
  · exact B1271043
  · exact B1271047
  · exact B1271051
  · exact B1271055
  · exact B1271059
  · exact B1271063
  · exact B1271067
  · exact B1271071
  · exact B1271075
  · exact B1271079
  · exact B1271083
  · exact B1271087
  · exact B1271091
  · exact B1271095
  · exact B1271099
  · exact B1271103
  · exact B1271107
  · exact B1271111
  · exact B1271115
  · exact B1271119
  · exact B1271123
  · exact B1271127
  · exact B1271131
  · exact B1271135
  · exact B1271139
  · exact B1271143
  · exact B1271147
  · exact B1271151
  · exact B1271155
  · exact B1271159
  · exact B1271163
  · exact B1271167
  · exact B1271171
  · exact B1271175
  · exact B1271179
  · exact B1271183
  · exact B1271187
  · exact B1271191
  · exact B1271195
  · exact B1271199
  · exact B1271203
  · exact B1271207
  · exact B1271211
  · exact B1271215
  · exact B1271219
  · exact B1271223
  · exact B1271227
  · exact B1271231
  · exact B1271235
  · exact B1271239
  · exact B1271243
  · exact B1271247
  · exact B1271251
  · exact B1271255
  · exact B1271259
  · exact B1271263
  · exact B1271267
  · exact B1271271
  · exact B1271275
  · exact B1271279
  · exact B1271283
  · exact B1271287
  · exact B1271291
  · exact B1271295
  · exact B1271299
  · exact B1271303
  · exact B1271307
  · exact B1271311
  · exact B1271315
  · exact B1271319
  · exact B1271323
  · exact B1271327
  · exact B1271331
  · exact B1271335
  · exact B1271339
  · exact B1271343
  · exact B1271347
  · exact B1271351
  · exact B1271355
  · exact B1271359
  · exact B1271363
  · exact B1271367
  · exact B1271371
  · exact B1271375
  · exact B1271379
  · exact B1271383
  · exact B1271387
  · exact B1271391
  · exact B1271395
  · exact B1271399
  · exact B1271403
  · exact B1271407
  · exact B1271411
  · exact B1271415
  · exact B1271419
  · exact B1271423
  · exact B1271427
  · exact B1271431
  · exact B1271435
  · exact B1271439
  · exact B1271443
  · exact B1271447
  · exact B1271451
  · exact B1271455
  · exact B1271459
  · exact B1271463
  · exact B1271467
  · exact B1271471
  · exact B1271475
  · exact B1271479
  · exact B1271483
  · exact B1271487
  · exact B1271491
  · exact B1271495
  · exact B1271499
  · exact B1271503
  · exact B1271507
  · exact B1271511
  · exact B1271515
  · exact B1271519
  · exact B1271523
  · exact B1271527
  · exact B1271531
  · exact B1271535
  · exact B1271539
  · exact B1271543
  · exact B1271547
  · exact B1271551
  · exact B1271555
  · exact B1271559
  · exact B1271563
  · exact B1271567
  · exact B1271571
  · exact B1271575
  · exact B1271579
  · exact B1271583
  · exact B1271587
  · exact B1271591
  · exact B1271595
  · exact B1271599
  · exact B1271603
  · exact B1271607
  · exact B1271611
  · exact B1271615
  · exact B1271619
  · exact B1271623
  · exact B1271627
  · exact B1271631
  · exact B1271635
  · exact B1271639
  · exact B1271643
  · exact B1271647
  · exact B1271651
  · exact B1271655
  · exact B1271659
  · exact B1271663
  · exact B1271667
  · exact B1271671
  · exact B1271675
  · exact B1271679
  · exact B1271683
  · exact B1271687
  · exact B1271691
  · exact B1271695
  · exact B1271699
  · exact B1271703
  · exact B1271707
  · exact B1271711
  · exact B1271715
  · exact B1271719
  · exact B1271723
  · exact B1271727
  · exact B1271731
  · exact B1271735
  · exact B1271739
  · exact B1271743
  · exact B1271747
  · exact B1271751
  · exact B1271755
  · exact B1271759
  · exact B1271763
  · exact B1271767
  · exact B1271771
  · exact B1271775
  · exact B1271779
  · exact B1271783
  · exact B1271787
  · exact B1271791
  · exact B1271795
  · exact B1271799
  · exact B1271803
  · exact B1271807
  · exact B1271811
  · exact B1271815
  · exact B1271819
  · exact B1271823
  · exact B1271827
  · exact B1271831
  · exact B1271835
  · exact B1271839
  · exact B1271843
  · exact B1271847
  · exact B1271851
  · exact B1271855
  · exact B1271859
  · exact B1271863
  · exact B1271867
  · exact B1271871
  · exact B1271875
  · exact B1271879
  · exact B1271883
  · exact B1271887
  · exact B1271891
  · exact B1271895
  · exact B1271899
  · exact B1271903
  · exact B1271907
  · exact B1271911
  · exact B1271915
  · exact B1271919
  · exact B1271923
  · exact B1271927
  · exact B1271931
  · exact B1271935
  · exact B1271939
  · exact B1271943
  · exact B1271947
  · exact B1271951

theorem solution (m : ℕ) (hlo : 1270453 ≤ m) (hhi : m ≤ 1271953) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 317613 ≤ j := by omega
    have hj2 : j ≤ 317987 := by omega
    have hb : Blo 1270453 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
