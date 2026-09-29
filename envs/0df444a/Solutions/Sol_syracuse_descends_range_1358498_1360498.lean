-- Prove2me | solution 1 for syracuse_descends_range_1358498_1360498
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:54.773063+00:00
-- url     : https://prove2.me/submissions/18c2c603-1939-47ee-b300-3ce8e0b246e2

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


theorem B2039813 : Blo 1358498 2039813 := bbase (se 4 (by rfl) ⟨191232, by rfl⟩ : syracuseStep 2039813 = 382465) (by norm_num)
theorem B2580493 : Blo 1358498 2580493 := bbase (se 3 (by rfl) ⟨483842, by rfl⟩ : syracuseStep 2580493 = 967685) (by norm_num)
theorem B2039837 : Blo 1358498 2039837 := bbase (se 3 (by rfl) ⟨382469, by rfl⟩ : syracuseStep 2039837 = 764939) (by norm_num)
theorem B3440677 : Blo 1358498 3440677 := bbase (se 4 (by rfl) ⟨322563, by rfl⟩ : syracuseStep 3440677 = 645127) (by norm_num)
theorem B2293805 : Blo 1358498 2293805 := bbase (se 3 (by rfl) ⟨430088, by rfl⟩ : syracuseStep 2293805 = 860177) (by norm_num)
theorem B1720369 : Blo 1358498 1720369 := bbase (se 2 (by rfl) ⟨645138, by rfl⟩ : syracuseStep 1720369 = 1290277) (by norm_num)
theorem B2039861 : Blo 1358498 2039861 := bbase (se 5 (by rfl) ⟨95618, by rfl⟩ : syracuseStep 2039861 = 191237) (by norm_num)
theorem B2039885 : Blo 1358498 2039885 := bbase (se 3 (by rfl) ⟨382478, by rfl⟩ : syracuseStep 2039885 = 764957) (by norm_num)
theorem B2039909 : Blo 1358498 2039909 := bbase (se 4 (by rfl) ⟨191241, by rfl⟩ : syracuseStep 2039909 = 382483) (by norm_num)
theorem B2039933 : Blo 1358498 2039933 := bbase (se 3 (by rfl) ⟨382487, by rfl⟩ : syracuseStep 2039933 = 764975) (by norm_num)
theorem B3440789 : Blo 1358498 3440789 := bbase (se 6 (by rfl) ⟨80643, by rfl⟩ : syracuseStep 3440789 = 161287) (by norm_num)
theorem B2039957 : Blo 1358498 2039957 := bbase (se 6 (by rfl) ⟨47811, by rfl⟩ : syracuseStep 2039957 = 95623) (by norm_num)
theorem B2580653 : Blo 1358498 2580653 := bbase (se 3 (by rfl) ⟨483872, by rfl⟩ : syracuseStep 2580653 = 967745) (by norm_num)
theorem B2293933 : Blo 1358498 2293933 := bbase (se 3 (by rfl) ⟨430112, by rfl⟩ : syracuseStep 2293933 = 860225) (by norm_num)
theorem B2039981 : Blo 1358498 2039981 := bbase (se 3 (by rfl) ⟨382496, by rfl⟩ : syracuseStep 2039981 = 764993) (by norm_num)
theorem B2040005 : Blo 1358498 2040005 := bbase (se 4 (by rfl) ⟨191250, by rfl⟩ : syracuseStep 2040005 = 382501) (by norm_num)
theorem B1720541 : Blo 1358498 1720541 := bbase (se 3 (by rfl) ⟨322601, by rfl⟩ : syracuseStep 1720541 = 645203) (by norm_num)
theorem B2040029 : Blo 1358498 2040029 := bbase (se 3 (by rfl) ⟨382505, by rfl⟩ : syracuseStep 2040029 = 765011) (by norm_num)
theorem B2040053 : Blo 1358498 2040053 := bbase (se 5 (by rfl) ⟨95627, by rfl⟩ : syracuseStep 2040053 = 191255) (by norm_num)
theorem B2294021 : Blo 1358498 2294021 := bbase (se 4 (by rfl) ⟨215064, by rfl⟩ : syracuseStep 2294021 = 430129) (by norm_num)
theorem B2040077 : Blo 1358498 2040077 := bbase (se 3 (by rfl) ⟨382514, by rfl⟩ : syracuseStep 2040077 = 765029) (by norm_num)
theorem B1720597 : Blo 1358498 1720597 := bbase (se 6 (by rfl) ⟨40326, by rfl⟩ : syracuseStep 1720597 = 80653) (by norm_num)
theorem B2040101 : Blo 1358498 2040101 := bbase (se 4 (by rfl) ⟨191259, by rfl⟩ : syracuseStep 2040101 = 382519) (by norm_num)
theorem B2580797 : Blo 1358498 2580797 := bbase (se 3 (by rfl) ⟨483899, by rfl⟩ : syracuseStep 2580797 = 967799) (by norm_num)
theorem B2040125 : Blo 1358498 2040125 := bbase (se 3 (by rfl) ⟨382523, by rfl⟩ : syracuseStep 2040125 = 765047) (by norm_num)
theorem B3440981 : Blo 1358498 3440981 := bbase (se 10 (by rfl) ⟨5040, by rfl⟩ : syracuseStep 3440981 = 10081) (by norm_num)
theorem B2040149 : Blo 1358498 2040149 := bbase (se 10 (by rfl) ⟨2988, by rfl⟩ : syracuseStep 2040149 = 5977) (by norm_num)
theorem B2040173 : Blo 1358498 2040173 := bbase (se 3 (by rfl) ⟨382532, by rfl⟩ : syracuseStep 2040173 = 765065) (by norm_num)
theorem B4587893 : Blo 1358498 4587893 := bbase (se 5 (by rfl) ⟨215057, by rfl⟩ : syracuseStep 4587893 = 430115) (by norm_num)
theorem B1720693 : Blo 1358498 1720693 := bbase (se 5 (by rfl) ⟨80657, by rfl⟩ : syracuseStep 1720693 = 161315) (by norm_num)
theorem B2294149 : Blo 1358498 2294149 := bbase (se 4 (by rfl) ⟨215076, by rfl⟩ : syracuseStep 2294149 = 430153) (by norm_num)
theorem B2040197 : Blo 1358498 2040197 := bbase (se 4 (by rfl) ⟨191268, by rfl⟩ : syracuseStep 2040197 = 382537) (by norm_num)
theorem B2040221 : Blo 1358498 2040221 := bbase (se 3 (by rfl) ⟨382541, by rfl⟩ : syracuseStep 2040221 = 765083) (by norm_num)
theorem B2040245 : Blo 1358498 2040245 := bbase (se 5 (by rfl) ⟨95636, by rfl⟩ : syracuseStep 2040245 = 191273) (by norm_num)
theorem B2040269 : Blo 1358498 2040269 := bbase (se 3 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 2040269 = 765101) (by norm_num)
theorem B2294237 : Blo 1358498 2294237 := bbase (se 3 (by rfl) ⟨430169, by rfl⟩ : syracuseStep 2294237 = 860339) (by norm_num)
theorem B2040293 : Blo 1358498 2040293 := bbase (se 4 (by rfl) ⟨191277, by rfl⟩ : syracuseStep 2040293 = 382555) (by norm_num)
theorem B2040317 : Blo 1358498 2040317 := bbase (se 3 (by rfl) ⟨382559, by rfl⟩ : syracuseStep 2040317 = 765119) (by norm_num)
theorem B2040341 : Blo 1358498 2040341 := bbase (se 6 (by rfl) ⟨47820, by rfl⟩ : syracuseStep 2040341 = 95641) (by norm_num)
theorem B1720865 : Blo 1358498 1720865 := bbase (se 2 (by rfl) ⟨645324, by rfl⟩ : syracuseStep 1720865 = 1290649) (by norm_num)
theorem B2040365 : Blo 1358498 2040365 := bbase (se 3 (by rfl) ⟨382568, by rfl⟩ : syracuseStep 2040365 = 765137) (by norm_num)
theorem B2040389 : Blo 1358498 2040389 := bbase (se 4 (by rfl) ⟨191286, by rfl⟩ : syracuseStep 2040389 = 382573) (by norm_num)
theorem B1720921 : Blo 1358498 1720921 := bbase (se 2 (by rfl) ⟨645345, by rfl⟩ : syracuseStep 1720921 = 1290691) (by norm_num)
theorem B2581085 : Blo 1358498 2581085 := bbase (se 3 (by rfl) ⟨483953, by rfl⟩ : syracuseStep 2581085 = 967907) (by norm_num)
theorem B2294365 : Blo 1358498 2294365 := bbase (se 3 (by rfl) ⟨430193, by rfl⟩ : syracuseStep 2294365 = 860387) (by norm_num)
theorem B2040413 : Blo 1358498 2040413 := bbase (se 3 (by rfl) ⟨382577, by rfl⟩ : syracuseStep 2040413 = 765155) (by norm_num)
theorem B2040437 : Blo 1358498 2040437 := bbase (se 5 (by rfl) ⟨95645, by rfl⟩ : syracuseStep 2040437 = 191291) (by norm_num)
theorem B2040461 : Blo 1358498 2040461 := bbase (se 3 (by rfl) ⟨382586, by rfl⟩ : syracuseStep 2040461 = 765173) (by norm_num)
theorem B3490453 : Blo 1358498 3490453 := bbase (se 6 (by rfl) ⟨81807, by rfl⟩ : syracuseStep 3490453 = 163615) (by norm_num)
theorem B2761381 : Blo 1358498 2761381 := bbase (se 4 (by rfl) ⟨258879, by rfl⟩ : syracuseStep 2761381 = 517759) (by norm_num)
theorem B2040485 : Blo 1358498 2040485 := bbase (se 4 (by rfl) ⟨191295, by rfl⟩ : syracuseStep 2040485 = 382591) (by norm_num)
theorem B3441325 : Blo 1358498 3441325 := bbase (se 3 (by rfl) ⟨645248, by rfl⟩ : syracuseStep 3441325 = 1290497) (by norm_num)
theorem B2294453 : Blo 1358498 2294453 := bbase (se 5 (by rfl) ⟨107552, by rfl⟩ : syracuseStep 2294453 = 215105) (by norm_num)
theorem B1721017 : Blo 1358498 1721017 := bbase (se 2 (by rfl) ⟨645381, by rfl⟩ : syracuseStep 1721017 = 1290763) (by norm_num)
theorem B2040509 : Blo 1358498 2040509 := bbase (se 3 (by rfl) ⟨382595, by rfl⟩ : syracuseStep 2040509 = 765191) (by norm_num)
theorem B2040533 : Blo 1358498 2040533 := bbase (se 7 (by rfl) ⟨23912, by rfl⟩ : syracuseStep 2040533 = 47825) (by norm_num)
theorem B2237149 : Blo 1358498 2237149 := bbase (se 3 (by rfl) ⟨419465, by rfl⟩ : syracuseStep 2237149 = 838931) (by norm_num)
theorem B2040557 : Blo 1358498 2040557 := bbase (se 3 (by rfl) ⟨382604, by rfl⟩ : syracuseStep 2040557 = 765209) (by norm_num)
theorem B2581237 : Blo 1358498 2581237 := bbase (se 5 (by rfl) ⟨120995, by rfl⟩ : syracuseStep 2581237 = 241991) (by norm_num)
theorem B2040581 : Blo 1358498 2040581 := bbase (se 4 (by rfl) ⟨191304, by rfl⟩ : syracuseStep 2040581 = 382609) (by norm_num)
theorem B2450189 : Blo 1358498 2450189 := bbase (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) (by norm_num)
theorem B10330901 : Blo 1358498 10330901 := bbase (se 6 (by rfl) ⟨242130, by rfl⟩ : syracuseStep 10330901 = 484261) (by norm_num)
theorem B3441437 : Blo 1358498 3441437 := bbase (se 3 (by rfl) ⟨645269, by rfl⟩ : syracuseStep 3441437 = 1290539) (by norm_num)
theorem B2040605 : Blo 1358498 2040605 := bbase (se 3 (by rfl) ⟨382613, by rfl⟩ : syracuseStep 2040605 = 765227) (by norm_num)
theorem B4588325 : Blo 1358498 4588325 := bbase (se 4 (by rfl) ⟨430155, by rfl⟩ : syracuseStep 4588325 = 860311) (by norm_num)
theorem B2294581 : Blo 1358498 2294581 := bbase (se 5 (by rfl) ⟨107558, by rfl⟩ : syracuseStep 2294581 = 215117) (by norm_num)
theorem B2040629 : Blo 1358498 2040629 := bbase (se 5 (by rfl) ⟨95654, by rfl⟩ : syracuseStep 2040629 = 191309) (by norm_num)
theorem B2040653 : Blo 1358498 2040653 := bbase (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) (by norm_num)
theorem B1721189 : Blo 1358498 1721189 := bbase (se 4 (by rfl) ⟨161361, by rfl⟩ : syracuseStep 1721189 = 322723) (by norm_num)
theorem B2040677 : Blo 1358498 2040677 := bbase (se 4 (by rfl) ⟨191313, by rfl⟩ : syracuseStep 2040677 = 382627) (by norm_num)
theorem B2040701 : Blo 1358498 2040701 := bbase (se 3 (by rfl) ⟨382631, by rfl⟩ : syracuseStep 2040701 = 765263) (by norm_num)
theorem B2294669 : Blo 1358498 2294669 := bbase (se 3 (by rfl) ⟨430250, by rfl⟩ : syracuseStep 2294669 = 860501) (by norm_num)
theorem B1655701 : Blo 1358498 1655701 := bbase (se 6 (by rfl) ⟨38805, by rfl⟩ : syracuseStep 1655701 = 77611) (by norm_num)
theorem B2040725 : Blo 1358498 2040725 := bbase (se 6 (by rfl) ⟨47829, by rfl⟩ : syracuseStep 2040725 = 95659) (by norm_num)
theorem B1721245 : Blo 1358498 1721245 := bbase (se 3 (by rfl) ⟨322733, by rfl⟩ : syracuseStep 1721245 = 645467) (by norm_num)
theorem B1450921 : Blo 1358498 1450921 := bbase (se 2 (by rfl) ⟨544095, by rfl⟩ : syracuseStep 1450921 = 1088191) (by norm_num)
theorem B6882245 : Blo 1358498 6882245 := bbase (se 4 (by rfl) ⟨645210, by rfl⟩ : syracuseStep 6882245 = 1290421) (by norm_num)
theorem B3441629 : Blo 1358498 3441629 := bbase (se 3 (by rfl) ⟨645305, by rfl⟩ : syracuseStep 3441629 = 1290611) (by norm_num)
theorem B1450981 : Blo 1358498 1450981 := bbase (se 4 (by rfl) ⟨136029, by rfl⟩ : syracuseStep 1450981 = 272059) (by norm_num)
theorem B1721341 : Blo 1358498 1721341 := bbase (se 3 (by rfl) ⟨322751, by rfl⟩ : syracuseStep 1721341 = 645503) (by norm_num)
theorem B2294797 : Blo 1358498 2294797 := bbase (se 3 (by rfl) ⟨430274, by rfl⟩ : syracuseStep 2294797 = 860549) (by norm_num)
theorem B9798677 : Blo 1358498 9798677 := bbase (se 6 (by rfl) ⟨229656, by rfl⟩ : syracuseStep 9798677 = 459313) (by norm_num)
theorem B3056669 : Blo 1358498 3056669 := bbase (se 3 (by rfl) ⟨573125, by rfl⟩ : syracuseStep 3056669 = 1146251) (by norm_num)
theorem B2581541 : Blo 1358498 2581541 := bbase (se 4 (by rfl) ⟨242019, by rfl⟩ : syracuseStep 2581541 = 484039) (by norm_num)
theorem B3056741 : Blo 1358498 3056741 := bbase (se 4 (by rfl) ⟨286569, by rfl⟩ : syracuseStep 3056741 = 573139) (by norm_num)
theorem B2294885 : Blo 1358498 2294885 := bbase (se 4 (by rfl) ⟨215145, by rfl⟩ : syracuseStep 2294885 = 430291) (by norm_num)
theorem B1836149 : Blo 1358498 1836149 := bbase (se 5 (by rfl) ⟨86069, by rfl⟩ : syracuseStep 1836149 = 172139) (by norm_num)
theorem B1721513 : Blo 1358498 1721513 := bbase (se 2 (by rfl) ⟨645567, by rfl⟩ : syracuseStep 1721513 = 1291135) (by norm_num)
theorem B3056813 : Blo 1358498 3056813 := bbase (se 3 (by rfl) ⟨573152, by rfl⟩ : syracuseStep 3056813 = 1146305) (by norm_num)
theorem B10323125 : Blo 1358498 10323125 := bbase (se 5 (by rfl) ⟨483896, by rfl⟩ : syracuseStep 10323125 = 967793) (by norm_num)
theorem B2450621 : Blo 1358498 2450621 := bbase (se 3 (by rfl) ⟨459491, by rfl⟩ : syracuseStep 2450621 = 918983) (by norm_num)
theorem B1934533 : Blo 1358498 1934533 := bbase (se 4 (by rfl) ⟨181362, by rfl⟩ : syracuseStep 1934533 = 362725) (by norm_num)
theorem B1377493 : Blo 1358498 1377493 := bbase (se 7 (by rfl) ⟨16142, by rfl⟩ : syracuseStep 1377493 = 32285) (by norm_num)
theorem B4588757 : Blo 1358498 4588757 := bbase (se 7 (by rfl) ⟨53774, by rfl⟩ : syracuseStep 4588757 = 107549) (by norm_num)
theorem B1721569 : Blo 1358498 1721569 := bbase (se 2 (by rfl) ⟨645588, by rfl⟩ : syracuseStep 1721569 = 1291177) (by norm_num)
theorem B2295013 : Blo 1358498 2295013 := bbase (se 4 (by rfl) ⟨215157, by rfl⟩ : syracuseStep 2295013 = 430315) (by norm_num)
theorem B3056885 : Blo 1358498 3056885 := bbase (se 5 (by rfl) ⟨143291, by rfl⟩ : syracuseStep 3056885 = 286583) (by norm_num)
theorem B1451297 : Blo 1358498 1451297 := bbase (se 2 (by rfl) ⟨544236, by rfl⟩ : syracuseStep 1451297 = 1088473) (by norm_num)
theorem B3441973 : Blo 1358498 3441973 := bbase (se 5 (by rfl) ⟨161342, by rfl⟩ : syracuseStep 3441973 = 322685) (by norm_num)
theorem B3056957 : Blo 1358498 3056957 := bbase (se 3 (by rfl) ⟨573179, by rfl⟩ : syracuseStep 3056957 = 1146359) (by norm_num)
theorem B2295101 : Blo 1358498 2295101 := bbase (se 3 (by rfl) ⟨430331, by rfl⟩ : syracuseStep 2295101 = 860663) (by norm_num)
theorem B1721665 : Blo 1358498 1721665 := bbase (se 2 (by rfl) ⟨645624, by rfl⟩ : syracuseStep 1721665 = 1291249) (by norm_num)
theorem B2450765 : Blo 1358498 2450765 := bbase (se 3 (by rfl) ⟨459518, by rfl⟩ : syracuseStep 2450765 = 919037) (by norm_num)
theorem B3057029 : Blo 1358498 3057029 := bbase (se 4 (by rfl) ⟨286596, by rfl⟩ : syracuseStep 3057029 = 573193) (by norm_num)
theorem B26142101 : Blo 1358498 26142101 := bbase (se 6 (by rfl) ⟨612705, by rfl⟩ : syracuseStep 26142101 = 1225411) (by norm_num)
theorem B3442085 : Blo 1358498 3442085 := bbase (se 4 (by rfl) ⟨322695, by rfl⟩ : syracuseStep 3442085 = 645391) (by norm_num)
theorem B3311021 : Blo 1358498 3311021 := bbase (se 3 (by rfl) ⟨620816, by rfl⟩ : syracuseStep 3311021 = 1241633) (by norm_num)
theorem B2295229 : Blo 1358498 2295229 := bbase (se 3 (by rfl) ⟨430355, by rfl⟩ : syracuseStep 2295229 = 860711) (by norm_num)
theorem B3057101 : Blo 1358498 3057101 := bbase (se 3 (by rfl) ⟨573206, by rfl⟩ : syracuseStep 3057101 = 1146413) (by norm_num)
theorem B1721837 : Blo 1358498 1721837 := bbase (se 3 (by rfl) ⟨322844, by rfl⟩ : syracuseStep 1721837 = 645689) (by norm_num)
theorem B3311101 : Blo 1358498 3311101 := bbase (se 3 (by rfl) ⟨620831, by rfl⟩ : syracuseStep 3311101 = 1241663) (by norm_num)
theorem B3057173 : Blo 1358498 3057173 := bbase (se 6 (by rfl) ⟨71652, by rfl⟩ : syracuseStep 3057173 = 143305) (by norm_num)
theorem B1934869 : Blo 1358498 1934869 := bbase (se 6 (by rfl) ⟨45348, by rfl⟩ : syracuseStep 1934869 = 90697) (by norm_num)
theorem B2295317 : Blo 1358498 2295317 := bbase (se 6 (by rfl) ⟨53796, by rfl⟩ : syracuseStep 2295317 = 107593) (by norm_num)
theorem B2450989 : Blo 1358498 2450989 := bbase (se 3 (by rfl) ⟨459560, by rfl⟩ : syracuseStep 2450989 = 919121) (by norm_num)
theorem B6530645 : Blo 1358498 6530645 := bbase (se 8 (by rfl) ⟨38265, by rfl⟩ : syracuseStep 6530645 = 76531) (by norm_num)
theorem B3057245 : Blo 1358498 3057245 := bbase (se 3 (by rfl) ⟨573233, by rfl⟩ : syracuseStep 3057245 = 1146467) (by norm_num)
theorem B3442277 : Blo 1358498 3442277 := bbase (se 4 (by rfl) ⟨322713, by rfl⟩ : syracuseStep 3442277 = 645427) (by norm_num)
theorem B4589189 : Blo 1358498 4589189 := bbase (se 4 (by rfl) ⟨430236, by rfl⟩ : syracuseStep 4589189 = 860473) (by norm_num)
theorem B2295445 : Blo 1358498 2295445 := bbase (se 6 (by rfl) ⟨53799, by rfl⟩ : syracuseStep 2295445 = 107599) (by norm_num)
theorem B2066077 : Blo 1358498 2066077 := bbase (se 3 (by rfl) ⟨387389, by rfl⟩ : syracuseStep 2066077 = 774779) (by norm_num)
theorem B3057317 : Blo 1358498 3057317 := bbase (se 4 (by rfl) ⟨286623, by rfl⟩ : syracuseStep 3057317 = 573247) (by norm_num)
theorem B1451741 : Blo 1358498 1451741 := bbase (se 3 (by rfl) ⟨272201, by rfl⟩ : syracuseStep 1451741 = 544403) (by norm_num)
theorem B3057389 : Blo 1358498 3057389 := bbase (se 3 (by rfl) ⟨573260, by rfl⟩ : syracuseStep 3057389 = 1146521) (by norm_num)
theorem B1935085 : Blo 1358498 1935085 := bbase (se 3 (by rfl) ⟨362828, by rfl⟩ : syracuseStep 1935085 = 725657) (by norm_num)
theorem B2295533 : Blo 1358498 2295533 := bbase (se 3 (by rfl) ⟨430412, by rfl⟩ : syracuseStep 2295533 = 860825) (by norm_num)
theorem B2901757 : Blo 1358498 2901757 := bbase (se 3 (by rfl) ⟨544079, by rfl⟩ : syracuseStep 2901757 = 1088159) (by norm_num)
theorem B2582293 : Blo 1358498 2582293 := bbase (se 6 (by rfl) ⟨60522, by rfl⟩ : syracuseStep 2582293 = 121045) (by norm_num)
theorem B1451801 : Blo 1358498 1451801 := bbase (se 2 (by rfl) ⟨544425, by rfl⟩ : syracuseStep 1451801 = 1088851) (by norm_num)
theorem B3057461 : Blo 1358498 3057461 := bbase (se 5 (by rfl) ⟨143318, by rfl⟩ : syracuseStep 3057461 = 286637) (by norm_num)
theorem B1836901 : Blo 1358498 1836901 := bbase (se 4 (by rfl) ⟨172209, by rfl⟩ : syracuseStep 1836901 = 344419) (by norm_num)
theorem B2942821 : Blo 1358498 2942821 := bbase (se 4 (by rfl) ⟨275889, by rfl⟩ : syracuseStep 2942821 = 551779) (by norm_num)
theorem B2295661 : Blo 1358498 2295661 := bbase (se 3 (by rfl) ⟨430436, by rfl⟩ : syracuseStep 2295661 = 860873) (by norm_num)
theorem B3057533 : Blo 1358498 3057533 := bbase (se 3 (by rfl) ⟨573287, by rfl⟩ : syracuseStep 3057533 = 1146575) (by norm_num)
theorem B5162885 : Blo 1358498 5162885 := bbase (se 4 (by rfl) ⟨484020, by rfl⟩ : syracuseStep 5162885 = 968041) (by norm_num)
theorem B2451341 : Blo 1358498 2451341 := bbase (se 3 (by rfl) ⟨459626, by rfl⟩ : syracuseStep 2451341 = 919253) (by norm_num)
theorem B8710037 : Blo 1358498 8710037 := bbase (se 6 (by rfl) ⟨204141, by rfl⟩ : syracuseStep 8710037 = 408283) (by norm_num)
theorem B1451929 : Blo 1358498 1451929 := bbase (se 2 (by rfl) ⟨544473, by rfl⟩ : syracuseStep 1451929 = 1088947) (by norm_num)
theorem B2582437 : Blo 1358498 2582437 := bbase (se 4 (by rfl) ⟨242103, by rfl⟩ : syracuseStep 2582437 = 484207) (by norm_num)
theorem B3442621 : Blo 1358498 3442621 := bbase (se 3 (by rfl) ⟨645491, by rfl⟩ : syracuseStep 3442621 = 1290983) (by norm_num)
theorem B3057605 : Blo 1358498 3057605 := bbase (se 4 (by rfl) ⟨286650, by rfl⟩ : syracuseStep 3057605 = 573301) (by norm_num)
theorem B2295749 : Blo 1358498 2295749 := bbase (se 4 (by rfl) ⟨215226, by rfl⟩ : syracuseStep 2295749 = 430453) (by norm_num)
theorem B4900837 : Blo 1358498 4900837 := bbase (se 4 (by rfl) ⟨459453, by rfl⟩ : syracuseStep 4900837 = 918907) (by norm_num)
theorem B3057677 : Blo 1358498 3057677 := bbase (se 3 (by rfl) ⟨573314, by rfl⟩ : syracuseStep 3057677 = 1146629) (by norm_num)
theorem B3442733 : Blo 1358498 3442733 := bbase (se 3 (by rfl) ⟨645512, by rfl⟩ : syracuseStep 3442733 = 1291025) (by norm_num)
theorem B4589621 : Blo 1358498 4589621 := bbase (se 5 (by rfl) ⟨215138, by rfl⟩ : syracuseStep 4589621 = 430277) (by norm_num)
theorem B2582597 : Blo 1358498 2582597 := bbase (se 4 (by rfl) ⟨242118, by rfl⟩ : syracuseStep 2582597 = 484237) (by norm_num)
theorem B3057749 : Blo 1358498 3057749 := bbase (se 8 (by rfl) ⟨17916, by rfl⟩ : syracuseStep 3057749 = 35833) (by norm_num)
theorem B1935461 : Blo 1358498 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B9799829 : Blo 1358498 9799829 := bbase (se 6 (by rfl) ⟨229683, by rfl⟩ : syracuseStep 9799829 = 459367) (by norm_num)
theorem B3057821 : Blo 1358498 3057821 := bbase (se 3 (by rfl) ⟨573341, by rfl⟩ : syracuseStep 3057821 = 1146683) (by norm_num)
theorem B1632421 : Blo 1358498 1632421 := bbase (se 4 (by rfl) ⟨153039, by rfl⟩ : syracuseStep 1632421 = 306079) (by norm_num)
theorem B5163173 : Blo 1358498 5163173 := bbase (se 4 (by rfl) ⟨484047, by rfl⟩ : syracuseStep 5163173 = 968095) (by norm_num)
theorem B2066629 : Blo 1358498 2066629 := bbase (se 4 (by rfl) ⟨193746, by rfl⟩ : syracuseStep 2066629 = 387493) (by norm_num)
theorem B6883541 : Blo 1358498 6883541 := bbase (se 7 (by rfl) ⟨80666, by rfl⟩ : syracuseStep 6883541 = 161333) (by norm_num)
theorem B2582741 : Blo 1358498 2582741 := bbase (se 7 (by rfl) ⟨30266, by rfl⟩ : syracuseStep 2582741 = 60533) (by norm_num)
theorem B3057893 : Blo 1358498 3057893 := bbase (se 4 (by rfl) ⟨286677, by rfl⟩ : syracuseStep 3057893 = 573355) (by norm_num)
theorem B1632493 : Blo 1358498 1632493 := bbase (se 3 (by rfl) ⟨306092, by rfl⟩ : syracuseStep 1632493 = 612185) (by norm_num)
theorem B3442925 : Blo 1358498 3442925 := bbase (se 3 (by rfl) ⟨645548, by rfl⟩ : syracuseStep 3442925 = 1291097) (by norm_num)
theorem B3672341 : Blo 1358498 3672341 := bbase (se 6 (by rfl) ⟨86070, by rfl⟩ : syracuseStep 3672341 = 172141) (by norm_num)
theorem B3057965 : Blo 1358498 3057965 := bbase (se 3 (by rfl) ⟨573368, by rfl⟩ : syracuseStep 3057965 = 1146737) (by norm_num)
theorem B10471733 : Blo 1358498 10471733 := bbase (se 5 (by rfl) ⟨490862, by rfl⟩ : syracuseStep 10471733 = 981725) (by norm_num)
theorem B1452373 : Blo 1358498 1452373 := bbase (se 10 (by rfl) ⟨2127, by rfl⟩ : syracuseStep 1452373 = 4255) (by norm_num)
theorem B1378669 : Blo 1358498 1378669 := bbase (se 3 (by rfl) ⟨258500, by rfl⟩ : syracuseStep 1378669 = 517001) (by norm_num)
theorem B3058037 : Blo 1358498 3058037 := bbase (se 5 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 3058037 = 286691) (by norm_num)
theorem B3058109 : Blo 1358498 3058109 := bbase (se 3 (by rfl) ⟨573395, by rfl⟩ : syracuseStep 3058109 = 1146791) (by norm_num)
theorem B1452493 : Blo 1358498 1452493 := bbase (se 3 (by rfl) ⟨272342, by rfl⟩ : syracuseStep 1452493 = 544685) (by norm_num)
theorem B10463701 : Blo 1358498 10463701 := bbase (se 7 (by rfl) ⟨122621, by rfl⟩ : syracuseStep 10463701 = 245243) (by norm_num)
theorem B4590053 : Blo 1358498 4590053 := bbase (se 4 (by rfl) ⟨430317, by rfl⟩ : syracuseStep 4590053 = 860635) (by norm_num)
theorem B3058181 : Blo 1358498 3058181 := bbase (se 4 (by rfl) ⟨286704, by rfl⟩ : syracuseStep 3058181 = 573409) (by norm_num)
theorem B2755093 : Blo 1358498 2755093 := bbase (se 6 (by rfl) ⟨64572, by rfl⟩ : syracuseStep 2755093 = 129145) (by norm_num)
theorem B3443269 : Blo 1358498 3443269 := bbase (se 4 (by rfl) ⟨322806, by rfl⟩ : syracuseStep 3443269 = 645613) (by norm_num)
theorem B3058253 : Blo 1358498 3058253 := bbase (se 3 (by rfl) ⟨573422, by rfl⟩ : syracuseStep 3058253 = 1146845) (by norm_num)
theorem B4647509 : Blo 1358498 4647509 := bbase (se 8 (by rfl) ⟨27231, by rfl⟩ : syracuseStep 4647509 = 54463) (by norm_num)
theorem B2902645 : Blo 1358498 2902645 := bbase (se 5 (by rfl) ⟨136061, by rfl⟩ : syracuseStep 2902645 = 272123) (by norm_num)
theorem B3058325 : Blo 1358498 3058325 := bbase (se 6 (by rfl) ⟨71679, by rfl⟩ : syracuseStep 3058325 = 143359) (by norm_num)
theorem B3443381 : Blo 1358498 3443381 := bbase (se 5 (by rfl) ⟨161408, by rfl⟩ : syracuseStep 3443381 = 322817) (by norm_num)
theorem B1452745 : Blo 1358498 1452745 := bbase (se 2 (by rfl) ⟨544779, by rfl⟩ : syracuseStep 1452745 = 1089559) (by norm_num)
theorem B1551053 : Blo 1358498 1551053 := bbase (se 3 (by rfl) ⟨290822, by rfl⟩ : syracuseStep 1551053 = 581645) (by norm_num)
theorem B1452749 : Blo 1358498 1452749 := bbase (se 3 (by rfl) ⟨272390, by rfl⟩ : syracuseStep 1452749 = 544781) (by norm_num)
theorem B3058397 : Blo 1358498 3058397 := bbase (se 3 (by rfl) ⟨573449, by rfl⟩ : syracuseStep 3058397 = 1146899) (by norm_num)
theorem B3058469 : Blo 1358498 3058469 := bbase (se 4 (by rfl) ⟨286731, by rfl⟩ : syracuseStep 3058469 = 573463) (by norm_num)
theorem B6974261 : Blo 1358498 6974261 := bbase (se 5 (by rfl) ⟨326918, by rfl⟩ : syracuseStep 6974261 = 653837) (by norm_num)
theorem B3058541 : Blo 1358498 3058541 := bbase (se 3 (by rfl) ⟨573476, by rfl⟩ : syracuseStep 3058541 = 1146953) (by norm_num)
theorem B4647797 : Blo 1358498 4647797 := bbase (se 5 (by rfl) ⟨217865, by rfl⟩ : syracuseStep 4647797 = 435731) (by norm_num)
theorem B3443573 : Blo 1358498 3443573 := bbase (se 5 (by rfl) ⟨161417, by rfl⟩ : syracuseStep 3443573 = 322835) (by norm_num)
theorem B4590485 : Blo 1358498 4590485 := bbase (se 6 (by rfl) ⟨107589, by rfl⟩ : syracuseStep 4590485 = 215179) (by norm_num)
theorem B3058613 : Blo 1358498 3058613 := bbase (se 5 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 3058613 = 286745) (by norm_num)
theorem B3869669 : Blo 1358498 3869669 := bbase (se 4 (by rfl) ⟨362781, by rfl⟩ : syracuseStep 3869669 = 725563) (by norm_num)
theorem B3058685 : Blo 1358498 3058685 := bbase (se 3 (by rfl) ⟨573503, by rfl⟩ : syracuseStep 3058685 = 1147007) (by norm_num)
theorem B15494165 : Blo 1358498 15494165 := bbase (se 6 (by rfl) ⟨363144, by rfl⟩ : syracuseStep 15494165 = 726289) (by norm_num)
theorem B2755613 : Blo 1358498 2755613 := bbase (se 3 (by rfl) ⟨516677, by rfl⟩ : syracuseStep 2755613 = 1033355) (by norm_num)
theorem B3058757 : Blo 1358498 3058757 := bbase (se 4 (by rfl) ⟨286758, by rfl⟩ : syracuseStep 3058757 = 573517) (by norm_num)
theorem B7842901 : Blo 1358498 7842901 := bbase (se 8 (by rfl) ⟨45954, by rfl⟩ : syracuseStep 7842901 = 91909) (by norm_num)
theorem B2903141 : Blo 1358498 2903141 := bbase (se 4 (by rfl) ⟨272169, by rfl⟩ : syracuseStep 2903141 = 544339) (by norm_num)
theorem B3058829 : Blo 1358498 3058829 := bbase (se 3 (by rfl) ⟨573530, by rfl⟩ : syracuseStep 3058829 = 1147061) (by norm_num)
theorem B4353173 : Blo 1358498 4353173 := bbase (se 6 (by rfl) ⟨102027, by rfl⟩ : syracuseStep 4353173 = 204055) (by norm_num)
theorem B3058901 : Blo 1358498 3058901 := bbase (se 7 (by rfl) ⟨35846, by rfl⟩ : syracuseStep 3058901 = 71693) (by norm_num)
theorem B1633493 : Blo 1358498 1633493 := bbase (se 7 (by rfl) ⟨19142, by rfl⟩ : syracuseStep 1633493 = 38285) (by norm_num)
theorem B1838333 : Blo 1358498 1838333 := bbase (se 3 (by rfl) ⟨344687, by rfl⟩ : syracuseStep 1838333 = 689375) (by norm_num)
theorem B3058973 : Blo 1358498 3058973 := bbase (se 3 (by rfl) ⟨573557, by rfl⟩ : syracuseStep 3058973 = 1147115) (by norm_num)
theorem B5164357 : Blo 1358498 5164357 := bbase (se 4 (by rfl) ⟨484158, by rfl⟩ : syracuseStep 5164357 = 968317) (by norm_num)
theorem B4590917 : Blo 1358498 4590917 := bbase (se 4 (by rfl) ⟨430398, by rfl⟩ : syracuseStep 4590917 = 860797) (by norm_num)
theorem B3059045 : Blo 1358498 3059045 := bbase (se 4 (by rfl) ⟨286785, by rfl⟩ : syracuseStep 3059045 = 573571) (by norm_num)
theorem B15691157 : Blo 1358498 15691157 := bbase (se 6 (by rfl) ⟨367761, by rfl⟩ : syracuseStep 15691157 = 735523) (by norm_num)
theorem B2067877 : Blo 1358498 2067877 := bbase (se 4 (by rfl) ⟨193863, by rfl⟩ : syracuseStep 2067877 = 387727) (by norm_num)
theorem B3059117 : Blo 1358498 3059117 := bbase (se 3 (by rfl) ⟨573584, by rfl⟩ : syracuseStep 3059117 = 1147169) (by norm_num)
theorem B6884837 : Blo 1358498 6884837 := bbase (se 4 (by rfl) ⟨645453, by rfl⟩ : syracuseStep 6884837 = 1290907) (by norm_num)
theorem B3141109 : Blo 1358498 3141109 := bbase (se 5 (by rfl) ⟨147239, by rfl⟩ : syracuseStep 3141109 = 294479) (by norm_num)
theorem B3059189 : Blo 1358498 3059189 := bbase (se 5 (by rfl) ⟨143399, by rfl⟩ : syracuseStep 3059189 = 286799) (by norm_num)
theorem B1936885 : Blo 1358498 1936885 := bbase (se 5 (by rfl) ⟨90791, by rfl⟩ : syracuseStep 1936885 = 181583) (by norm_num)
theorem B1961533 : Blo 1358498 1961533 := bbase (se 3 (by rfl) ⟨367787, by rfl⟩ : syracuseStep 1961533 = 735575) (by norm_num)
theorem B3059261 : Blo 1358498 3059261 := bbase (se 3 (by rfl) ⟨573611, by rfl⟩ : syracuseStep 3059261 = 1147223) (by norm_num)
theorem B5164661 : Blo 1358498 5164661 := bbase (se 5 (by rfl) ⟨242093, by rfl⟩ : syracuseStep 5164661 = 484187) (by norm_num)
theorem B3059333 : Blo 1358498 3059333 := bbase (se 4 (by rfl) ⟨286812, by rfl⟩ : syracuseStep 3059333 = 573625) (by norm_num)
theorem B3264149 : Blo 1358498 3264149 := bbase (se 6 (by rfl) ⟨76503, by rfl⟩ : syracuseStep 3264149 = 153007) (by norm_num)
theorem B5508773 : Blo 1358498 5508773 := bbase (se 4 (by rfl) ⟨516447, by rfl⟩ : syracuseStep 5508773 = 1032895) (by norm_num)
theorem B3059405 : Blo 1358498 3059405 := bbase (se 3 (by rfl) ⟨573638, by rfl⟩ : syracuseStep 3059405 = 1147277) (by norm_num)
theorem B4591349 : Blo 1358498 4591349 := bbase (se 5 (by rfl) ⟨215219, by rfl⟩ : syracuseStep 4591349 = 430439) (by norm_num)
theorem B3059477 : Blo 1358498 3059477 := bbase (se 6 (by rfl) ⟨71706, by rfl⟩ : syracuseStep 3059477 = 143413) (by norm_num)
theorem B8376149 : Blo 1358498 8376149 := bbase (se 9 (by rfl) ⟨24539, by rfl⟩ : syracuseStep 8376149 = 49079) (by norm_num)
theorem B3059549 : Blo 1358498 3059549 := bbase (se 3 (by rfl) ⟨573665, by rfl⟩ : syracuseStep 3059549 = 1147331) (by norm_num)
theorem B1634185 : Blo 1358498 1634185 := bbase (se 2 (by rfl) ⟨612819, by rfl⟩ : syracuseStep 1634185 = 1225639) (by norm_num)
theorem B1634189 : Blo 1358498 1634189 := bbase (se 3 (by rfl) ⟨306410, by rfl⟩ : syracuseStep 1634189 = 612821) (by norm_num)
theorem B3059621 : Blo 1358498 3059621 := bbase (se 4 (by rfl) ⟨286839, by rfl⟩ : syracuseStep 3059621 = 573679) (by norm_num)
theorem B2904029 : Blo 1358498 2904029 := bbase (se 3 (by rfl) ⟨544505, by rfl⟩ : syracuseStep 2904029 = 1089011) (by norm_num)
theorem B3059693 : Blo 1358498 3059693 := bbase (se 3 (by rfl) ⟨573692, by rfl⟩ : syracuseStep 3059693 = 1147385) (by norm_num)
theorem B3059765 : Blo 1358498 3059765 := bbase (se 5 (by rfl) ⟨143426, by rfl⟩ : syracuseStep 3059765 = 286853) (by norm_num)
theorem B2904149 : Blo 1358498 2904149 := bbase (se 8 (by rfl) ⟨17016, by rfl⟩ : syracuseStep 2904149 = 34033) (by norm_num)
theorem B3059837 : Blo 1358498 3059837 := bbase (se 3 (by rfl) ⟨573719, by rfl⟩ : syracuseStep 3059837 = 1147439) (by norm_num)
theorem B1863805 : Blo 1358498 1863805 := bbase (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) (by norm_num)
theorem B3059909 : Blo 1358498 3059909 := bbase (se 4 (by rfl) ⟨286866, by rfl⟩ : syracuseStep 3059909 = 573733) (by norm_num)
theorem B2756845 : Blo 1358498 2756845 := bbase (se 3 (by rfl) ⟨516908, by rfl⟩ : syracuseStep 2756845 = 1033817) (by norm_num)
theorem B3059981 : Blo 1358498 3059981 := bbase (se 3 (by rfl) ⟨573746, by rfl⟩ : syracuseStep 3059981 = 1147493) (by norm_num)
theorem B2756909 : Blo 1358498 2756909 := bbase (se 3 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 2756909 = 1033841) (by norm_num)
theorem B3060053 : Blo 1358498 3060053 := bbase (se 10 (by rfl) ⟨4482, by rfl⟩ : syracuseStep 3060053 = 8965) (by norm_num)
theorem B3060125 : Blo 1358498 3060125 := bbase (se 3 (by rfl) ⟨573773, by rfl⟩ : syracuseStep 3060125 = 1147547) (by norm_num)
theorem B3060197 : Blo 1358498 3060197 := bbase (se 4 (by rfl) ⟨286893, by rfl⟩ : syracuseStep 3060197 = 573787) (by norm_num)
theorem B1528321 : Blo 1358498 1528321 := bbase (se 2 (by rfl) ⟨573120, by rfl⟩ : syracuseStep 1528321 = 1146241) (by norm_num)
theorem B3871253 : Blo 1358498 3871253 := bbase (se 6 (by rfl) ⟨90732, by rfl⟩ : syracuseStep 3871253 = 181465) (by norm_num)
theorem B19599893 : Blo 1358498 19599893 := bbase (se 6 (by rfl) ⟨459372, by rfl⟩ : syracuseStep 19599893 = 918745) (by norm_num)
theorem B1528357 : Blo 1358498 1528357 := bbase (se 4 (by rfl) ⟨143283, by rfl⟩ : syracuseStep 1528357 = 286567) (by norm_num)
theorem B3060269 : Blo 1358498 3060269 := bbase (se 3 (by rfl) ⟨573800, by rfl⟩ : syracuseStep 3060269 = 1147601) (by norm_num)
theorem B1528393 : Blo 1358498 1528393 := bbase (se 2 (by rfl) ⟨573147, by rfl⟩ : syracuseStep 1528393 = 1146295) (by norm_num)
theorem B16536149 : Blo 1358498 16536149 := bbase (se 8 (by rfl) ⟨96891, by rfl⟩ : syracuseStep 16536149 = 193783) (by norm_num)
theorem B1528429 : Blo 1358498 1528429 := bbase (se 3 (by rfl) ⟨286580, by rfl⟩ : syracuseStep 1528429 = 573161) (by norm_num)
theorem B3060341 : Blo 1358498 3060341 := bbase (se 5 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 3060341 = 286907) (by norm_num)
theorem B1528465 : Blo 1358498 1528465 := bbase (se 2 (by rfl) ⟨573174, by rfl⟩ : syracuseStep 1528465 = 1146349) (by norm_num)
theorem B5804693 : Blo 1358498 5804693 := bbase (se 6 (by rfl) ⟨136047, by rfl⟩ : syracuseStep 5804693 = 272095) (by norm_num)
theorem B1397405 : Blo 1358498 1397405 := bbase (se 3 (by rfl) ⟨262013, by rfl⟩ : syracuseStep 1397405 = 524027) (by norm_num)
theorem B1528501 : Blo 1358498 1528501 := bbase (se 5 (by rfl) ⟨71648, by rfl⟩ : syracuseStep 1528501 = 143297) (by norm_num)
theorem B3060413 : Blo 1358498 3060413 := bbase (se 3 (by rfl) ⟨573827, by rfl⟩ : syracuseStep 3060413 = 1147655) (by norm_num)
theorem B2904781 : Blo 1358498 2904781 := bbase (se 3 (by rfl) ⟨544646, by rfl⟩ : syracuseStep 2904781 = 1089293) (by norm_num)
theorem B1528537 : Blo 1358498 1528537 := bbase (se 2 (by rfl) ⟨573201, by rfl⟩ : syracuseStep 1528537 = 1146403) (by norm_num)
theorem B6886133 : Blo 1358498 6886133 := bbase (se 5 (by rfl) ⟨322787, by rfl⟩ : syracuseStep 6886133 = 645575) (by norm_num)
theorem B1528573 : Blo 1358498 1528573 := bbase (se 3 (by rfl) ⟨286607, by rfl⟩ : syracuseStep 1528573 = 573215) (by norm_num)
theorem B3060485 : Blo 1358498 3060485 := bbase (se 4 (by rfl) ⟨286920, by rfl⟩ : syracuseStep 3060485 = 573841) (by norm_num)
theorem B13611797 : Blo 1358498 13611797 := bbase (se 6 (by rfl) ⟨319026, by rfl⟩ : syracuseStep 13611797 = 638053) (by norm_num)
theorem B1528609 : Blo 1358498 1528609 := bbase (se 2 (by rfl) ⟨573228, by rfl⟩ : syracuseStep 1528609 = 1146457) (by norm_num)
theorem B1528645 : Blo 1358498 1528645 := bbase (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) (by norm_num)
theorem B3060557 : Blo 1358498 3060557 := bbase (se 3 (by rfl) ⟨573854, by rfl⟩ : syracuseStep 3060557 = 1147709) (by norm_num)
theorem B1528681 : Blo 1358498 1528681 := bbase (se 2 (by rfl) ⟨573255, by rfl⟩ : syracuseStep 1528681 = 1146511) (by norm_num)
theorem B1528717 : Blo 1358498 1528717 := bbase (se 3 (by rfl) ⟨286634, by rfl⟩ : syracuseStep 1528717 = 573269) (by norm_num)
theorem B3060629 : Blo 1358498 3060629 := bbase (se 6 (by rfl) ⟨71733, by rfl⟩ : syracuseStep 3060629 = 143467) (by norm_num)
theorem B1528753 : Blo 1358498 1528753 := bbase (se 2 (by rfl) ⟨573282, by rfl⟩ : syracuseStep 1528753 = 1146565) (by norm_num)
theorem B5510069 : Blo 1358498 5510069 := bbase (se 5 (by rfl) ⟨258284, by rfl⟩ : syracuseStep 5510069 = 516569) (by norm_num)
theorem B1528789 : Blo 1358498 1528789 := bbase (se 7 (by rfl) ⟨17915, by rfl⟩ : syracuseStep 1528789 = 35831) (by norm_num)
theorem B3060701 : Blo 1358498 3060701 := bbase (se 3 (by rfl) ⟨573881, by rfl⟩ : syracuseStep 3060701 = 1147763) (by norm_num)
theorem B3101669 : Blo 1358498 3101669 := bbase (se 4 (by rfl) ⟨290781, by rfl⟩ : syracuseStep 3101669 = 581563) (by norm_num)
theorem B3265525 : Blo 1358498 3265525 := bbase (se 5 (by rfl) ⟨153071, by rfl⟩ : syracuseStep 3265525 = 306143) (by norm_num)
theorem B1528825 : Blo 1358498 1528825 := bbase (se 2 (by rfl) ⟨573309, by rfl⟩ : syracuseStep 1528825 = 1146619) (by norm_num)
theorem B1528861 : Blo 1358498 1528861 := bbase (se 3 (by rfl) ⟨286661, by rfl⟩ : syracuseStep 1528861 = 573323) (by norm_num)
theorem B3060773 : Blo 1358498 3060773 := bbase (se 4 (by rfl) ⟨286947, by rfl⟩ : syracuseStep 3060773 = 573895) (by norm_num)
theorem B1528897 : Blo 1358498 1528897 := bbase (se 2 (by rfl) ⟨573336, by rfl⟩ : syracuseStep 1528897 = 1146673) (by norm_num)
theorem B1528933 : Blo 1358498 1528933 := bbase (se 4 (by rfl) ⟨143337, by rfl⟩ : syracuseStep 1528933 = 286675) (by norm_num)
theorem B3060845 : Blo 1358498 3060845 := bbase (se 3 (by rfl) ⟨573908, by rfl⟩ : syracuseStep 3060845 = 1147817) (by norm_num)
theorem B1528969 : Blo 1358498 1528969 := bbase (se 2 (by rfl) ⟨573363, by rfl⟩ : syracuseStep 1528969 = 1146727) (by norm_num)
theorem B6878357 : Blo 1358498 6878357 := bbase (se 6 (by rfl) ⟨161211, by rfl⟩ : syracuseStep 6878357 = 322423) (by norm_num)
theorem B7738517 : Blo 1358498 7738517 := bbase (se 6 (by rfl) ⟨181371, by rfl⟩ : syracuseStep 7738517 = 362743) (by norm_num)
theorem B1529005 : Blo 1358498 1529005 := bbase (se 3 (by rfl) ⟨286688, by rfl⟩ : syracuseStep 1529005 = 573377) (by norm_num)
theorem B3871925 : Blo 1358498 3871925 := bbase (se 5 (by rfl) ⟨181496, by rfl⟩ : syracuseStep 3871925 = 362993) (by norm_num)
theorem B3060917 : Blo 1358498 3060917 := bbase (se 5 (by rfl) ⟨143480, by rfl⟩ : syracuseStep 3060917 = 286961) (by norm_num)
theorem B6288581 : Blo 1358498 6288581 := bbase (se 4 (by rfl) ⟨589554, by rfl⟩ : syracuseStep 6288581 = 1179109) (by norm_num)
theorem B1529041 : Blo 1358498 1529041 := bbase (se 2 (by rfl) ⟨573390, by rfl⟩ : syracuseStep 1529041 = 1146781) (by norm_num)
theorem B1529077 : Blo 1358498 1529077 := bbase (se 5 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 1529077 = 143351) (by norm_num)
theorem B3060989 : Blo 1358498 3060989 := bbase (se 3 (by rfl) ⟨573935, by rfl⟩ : syracuseStep 3060989 = 1147871) (by norm_num)
theorem B7165189 : Blo 1358498 7165189 := bbase (se 4 (by rfl) ⟨671736, by rfl⟩ : syracuseStep 7165189 = 1343473) (by norm_num)
theorem B1766677 : Blo 1358498 1766677 := bbase (se 6 (by rfl) ⟨41406, by rfl⟩ : syracuseStep 1766677 = 82813) (by norm_num)
theorem B1529113 : Blo 1358498 1529113 := bbase (se 2 (by rfl) ⟨573417, by rfl⟩ : syracuseStep 1529113 = 1146835) (by norm_num)
theorem B4355365 : Blo 1358498 4355365 := bbase (se 4 (by rfl) ⟨408315, by rfl⟩ : syracuseStep 4355365 = 816631) (by norm_num)
theorem B8262965 : Blo 1358498 8262965 := bbase (se 5 (by rfl) ⟨387326, by rfl⟩ : syracuseStep 8262965 = 774653) (by norm_num)
theorem B1529149 : Blo 1358498 1529149 := bbase (se 3 (by rfl) ⟨286715, by rfl⟩ : syracuseStep 1529149 = 573431) (by norm_num)
theorem B3061061 : Blo 1358498 3061061 := bbase (se 4 (by rfl) ⟨286974, by rfl⟩ : syracuseStep 3061061 = 573949) (by norm_num)
theorem B1471817 : Blo 1358498 1471817 := bbase (se 2 (by rfl) ⟨551931, by rfl⟩ : syracuseStep 1471817 = 1103863) (by norm_num)
theorem B1529185 : Blo 1358498 1529185 := bbase (se 2 (by rfl) ⟨573444, by rfl⟩ : syracuseStep 1529185 = 1146889) (by norm_num)
theorem B7853429 : Blo 1358498 7853429 := bbase (se 5 (by rfl) ⟨368129, by rfl⟩ : syracuseStep 7853429 = 736259) (by norm_num)
theorem B1529221 : Blo 1358498 1529221 := bbase (se 4 (by rfl) ⟨143364, by rfl⟩ : syracuseStep 1529221 = 286729) (by norm_num)
theorem B1529257 : Blo 1358498 1529257 := bbase (se 2 (by rfl) ⟨573471, by rfl⟩ : syracuseStep 1529257 = 1146943) (by norm_num)
theorem B1529293 : Blo 1358498 1529293 := bbase (se 3 (by rfl) ⟨286742, by rfl⟩ : syracuseStep 1529293 = 573485) (by norm_num)
theorem B1529329 : Blo 1358498 1529329 := bbase (se 2 (by rfl) ⟨573498, by rfl⟩ : syracuseStep 1529329 = 1146997) (by norm_num)
theorem B1529365 : Blo 1358498 1529365 := bbase (se 6 (by rfl) ⟨35844, by rfl⟩ : syracuseStep 1529365 = 71689) (by norm_num)
theorem B1529401 : Blo 1358498 1529401 := bbase (se 2 (by rfl) ⟨573525, by rfl⟩ : syracuseStep 1529401 = 1147051) (by norm_num)
theorem B2905669 : Blo 1358498 2905669 := bbase (se 4 (by rfl) ⟨272406, by rfl⟩ : syracuseStep 2905669 = 544813) (by norm_num)
theorem B1529437 : Blo 1358498 1529437 := bbase (se 3 (by rfl) ⟨286769, by rfl⟩ : syracuseStep 1529437 = 573539) (by norm_num)
theorem B3872357 : Blo 1358498 3872357 := bbase (se 4 (by rfl) ⟨363033, by rfl⟩ : syracuseStep 3872357 = 726067) (by norm_num)
theorem B1529473 : Blo 1358498 1529473 := bbase (se 2 (by rfl) ⟨573552, by rfl⟩ : syracuseStep 1529473 = 1147105) (by norm_num)
theorem B5805701 : Blo 1358498 5805701 := bbase (se 4 (by rfl) ⟨544284, by rfl⟩ : syracuseStep 5805701 = 1088569) (by norm_num)
theorem B1570441 : Blo 1358498 1570441 := bbase (se 2 (by rfl) ⟨588915, by rfl⟩ : syracuseStep 1570441 = 1177831) (by norm_num)
theorem B1529509 : Blo 1358498 1529509 := bbase (se 4 (by rfl) ⟨143391, by rfl⟩ : syracuseStep 1529509 = 286783) (by norm_num)
theorem B1529545 : Blo 1358498 1529545 := bbase (se 2 (by rfl) ⟨573579, by rfl⟩ : syracuseStep 1529545 = 1147159) (by norm_num)
theorem B1529581 : Blo 1358498 1529581 := bbase (se 3 (by rfl) ⟨286796, by rfl⟩ : syracuseStep 1529581 = 573593) (by norm_num)
theorem B1529617 : Blo 1358498 1529617 := bbase (se 2 (by rfl) ⟨573606, by rfl⟩ : syracuseStep 1529617 = 1147213) (by norm_num)
theorem B1529653 : Blo 1358498 1529653 := bbase (se 5 (by rfl) ⟨71702, by rfl⟩ : syracuseStep 1529653 = 143405) (by norm_num)
theorem B3143477 : Blo 1358498 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B4585301 : Blo 1358498 4585301 := bbase (se 9 (by rfl) ⟨13433, by rfl⟩ : syracuseStep 4585301 = 26867) (by norm_num)
theorem B1529689 : Blo 1358498 1529689 := bbase (se 2 (by rfl) ⟨573633, by rfl⟩ : syracuseStep 1529689 = 1147267) (by norm_num)
theorem B2324341 : Blo 1358498 2324341 := bbase (se 5 (by rfl) ⟨108953, by rfl⟩ : syracuseStep 2324341 = 217907) (by norm_num)
theorem B1529725 : Blo 1358498 1529725 := bbase (se 3 (by rfl) ⟨286823, by rfl⟩ : syracuseStep 1529725 = 573647) (by norm_num)
theorem B1529761 : Blo 1358498 1529761 := bbase (se 2 (by rfl) ⟨573660, by rfl⟩ : syracuseStep 1529761 = 1147321) (by norm_num)
theorem B1529797 : Blo 1358498 1529797 := bbase (se 4 (by rfl) ⟨143418, by rfl⟩ : syracuseStep 1529797 = 286837) (by norm_num)
theorem B1529833 : Blo 1358498 1529833 := bbase (se 2 (by rfl) ⟨573687, by rfl⟩ : syracuseStep 1529833 = 1147375) (by norm_num)
theorem B2037749 : Blo 1358498 2037749 := bbase (se 5 (by rfl) ⟨95519, by rfl⟩ : syracuseStep 2037749 = 191039) (by norm_num)
theorem B8706037 : Blo 1358498 8706037 := bbase (se 5 (by rfl) ⟨408095, by rfl⟩ : syracuseStep 8706037 = 816191) (by norm_num)
theorem B6887429 : Blo 1358498 6887429 := bbase (se 4 (by rfl) ⟨645696, by rfl⟩ : syracuseStep 6887429 = 1291393) (by norm_num)
theorem B2037773 : Blo 1358498 2037773 := bbase (se 3 (by rfl) ⟨382082, by rfl⟩ : syracuseStep 2037773 = 764165) (by norm_num)
theorem B1529869 : Blo 1358498 1529869 := bbase (se 3 (by rfl) ⟨286850, by rfl⟩ : syracuseStep 1529869 = 573701) (by norm_num)
theorem B2037797 : Blo 1358498 2037797 := bbase (se 4 (by rfl) ⟨191043, by rfl⟩ : syracuseStep 2037797 = 382087) (by norm_num)
theorem B1529905 : Blo 1358498 1529905 := bbase (se 2 (by rfl) ⟨573714, by rfl⟩ : syracuseStep 1529905 = 1147429) (by norm_num)
theorem B2037821 : Blo 1358498 2037821 := bbase (se 3 (by rfl) ⟨382091, by rfl⟩ : syracuseStep 2037821 = 764183) (by norm_num)
theorem B2037845 : Blo 1358498 2037845 := bbase (se 8 (by rfl) ⟨11940, by rfl⟩ : syracuseStep 2037845 = 23881) (by norm_num)
theorem B5158997 : Blo 1358498 5158997 := bbase (se 8 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 5158997 = 60457) (by norm_num)
theorem B5232725 : Blo 1358498 5232725 := bbase (se 8 (by rfl) ⟨30660, by rfl⟩ : syracuseStep 5232725 = 61321) (by norm_num)
theorem B1529941 : Blo 1358498 1529941 := bbase (se 8 (by rfl) ⟨8964, by rfl⟩ : syracuseStep 1529941 = 17929) (by norm_num)
theorem B4356197 : Blo 1358498 4356197 := bbase (se 4 (by rfl) ⟨408393, by rfl⟩ : syracuseStep 4356197 = 816787) (by norm_num)
theorem B2037869 : Blo 1358498 2037869 := bbase (se 3 (by rfl) ⟨382100, by rfl⟩ : syracuseStep 2037869 = 764201) (by norm_num)
theorem B1529977 : Blo 1358498 1529977 := bbase (se 2 (by rfl) ⟨573741, by rfl⟩ : syracuseStep 1529977 = 1147483) (by norm_num)
theorem B2037893 : Blo 1358498 2037893 := bbase (se 4 (by rfl) ⟨191052, by rfl⟩ : syracuseStep 2037893 = 382105) (by norm_num)
theorem B3438733 : Blo 1358498 3438733 := bbase (se 3 (by rfl) ⟨644762, by rfl⟩ : syracuseStep 3438733 = 1289525) (by norm_num)
theorem B2037917 : Blo 1358498 2037917 := bbase (se 3 (by rfl) ⟨382109, by rfl⟩ : syracuseStep 2037917 = 764219) (by norm_num)
theorem B1530013 : Blo 1358498 1530013 := bbase (se 3 (by rfl) ⟨286877, by rfl⟩ : syracuseStep 1530013 = 573755) (by norm_num)
theorem B3266725 : Blo 1358498 3266725 := bbase (se 4 (by rfl) ⟨306255, by rfl⟩ : syracuseStep 3266725 = 612511) (by norm_num)
theorem B2037941 : Blo 1358498 2037941 := bbase (se 5 (by rfl) ⟨95528, by rfl⟩ : syracuseStep 2037941 = 191057) (by norm_num)
theorem B1530049 : Blo 1358498 1530049 := bbase (se 2 (by rfl) ⟨573768, by rfl⟩ : syracuseStep 1530049 = 1147537) (by norm_num)
theorem B2037965 : Blo 1358498 2037965 := bbase (se 3 (by rfl) ⟨382118, by rfl⟩ : syracuseStep 2037965 = 764237) (by norm_num)
theorem B2037989 : Blo 1358498 2037989 := bbase (se 4 (by rfl) ⟨191061, by rfl⟩ : syracuseStep 2037989 = 382123) (by norm_num)
theorem B1530085 : Blo 1358498 1530085 := bbase (se 4 (by rfl) ⟨143445, by rfl⟩ : syracuseStep 1530085 = 286891) (by norm_num)
theorem B3438845 : Blo 1358498 3438845 := bbase (se 3 (by rfl) ⟨644783, by rfl⟩ : syracuseStep 3438845 = 1289567) (by norm_num)
theorem B2038013 : Blo 1358498 2038013 := bbase (se 3 (by rfl) ⟨382127, by rfl⟩ : syracuseStep 2038013 = 764255) (by norm_num)
theorem B4585733 : Blo 1358498 4585733 := bbase (se 4 (by rfl) ⟨429912, by rfl⟩ : syracuseStep 4585733 = 859825) (by norm_num)
theorem B1530121 : Blo 1358498 1530121 := bbase (se 2 (by rfl) ⟨573795, by rfl⟩ : syracuseStep 1530121 = 1147591) (by norm_num)
theorem B2038037 : Blo 1358498 2038037 := bbase (se 6 (by rfl) ⟨47766, by rfl⟩ : syracuseStep 2038037 = 95533) (by norm_num)
theorem B2038061 : Blo 1358498 2038061 := bbase (se 3 (by rfl) ⟨382136, by rfl⟩ : syracuseStep 2038061 = 764273) (by norm_num)
theorem B1530157 : Blo 1358498 1530157 := bbase (se 3 (by rfl) ⟨286904, by rfl⟩ : syracuseStep 1530157 = 573809) (by norm_num)
theorem B2038085 : Blo 1358498 2038085 := bbase (se 4 (by rfl) ⟨191070, by rfl⟩ : syracuseStep 2038085 = 382141) (by norm_num)
theorem B1530193 : Blo 1358498 1530193 := bbase (se 2 (by rfl) ⟨573822, by rfl⟩ : syracuseStep 1530193 = 1147645) (by norm_num)
theorem B3873109 : Blo 1358498 3873109 := bbase (se 10 (by rfl) ⟨5673, by rfl⟩ : syracuseStep 3873109 = 11347) (by norm_num)
theorem B2038109 : Blo 1358498 2038109 := bbase (se 3 (by rfl) ⟨382145, by rfl⟩ : syracuseStep 2038109 = 764291) (by norm_num)
theorem B2177381 : Blo 1358498 2177381 := bbase (se 4 (by rfl) ⟨204129, by rfl⟩ : syracuseStep 2177381 = 408259) (by norm_num)
theorem B2038133 : Blo 1358498 2038133 := bbase (se 5 (by rfl) ⟨95537, by rfl⟩ : syracuseStep 2038133 = 191075) (by norm_num)
theorem B5159285 : Blo 1358498 5159285 := bbase (se 5 (by rfl) ⟨241841, by rfl⟩ : syracuseStep 5159285 = 483683) (by norm_num)
theorem B1530229 : Blo 1358498 1530229 := bbase (se 5 (by rfl) ⟨71729, by rfl⟩ : syracuseStep 1530229 = 143459) (by norm_num)
theorem B2038157 : Blo 1358498 2038157 := bbase (se 3 (by rfl) ⟨382154, by rfl⟩ : syracuseStep 2038157 = 764309) (by norm_num)
theorem B15702421 : Blo 1358498 15702421 := bbase (se 6 (by rfl) ⟨368025, by rfl⟩ : syracuseStep 15702421 = 736051) (by norm_num)
theorem B23239061 : Blo 1358498 23239061 := bbase (se 6 (by rfl) ⟨544665, by rfl⟩ : syracuseStep 23239061 = 1089331) (by norm_num)
theorem B1530265 : Blo 1358498 1530265 := bbase (se 2 (by rfl) ⟨573849, by rfl⟩ : syracuseStep 1530265 = 1147699) (by norm_num)
theorem B2038181 : Blo 1358498 2038181 := bbase (se 4 (by rfl) ⟨191079, by rfl⟩ : syracuseStep 2038181 = 382159) (by norm_num)
theorem B6879653 : Blo 1358498 6879653 := bbase (se 4 (by rfl) ⟨644967, by rfl⟩ : syracuseStep 6879653 = 1289935) (by norm_num)
theorem B3439037 : Blo 1358498 3439037 := bbase (se 3 (by rfl) ⟨644819, by rfl⟩ : syracuseStep 3439037 = 1289639) (by norm_num)
theorem B2038205 : Blo 1358498 2038205 := bbase (se 3 (by rfl) ⟨382163, by rfl⟩ : syracuseStep 2038205 = 764327) (by norm_num)
theorem B1530301 : Blo 1358498 1530301 := bbase (se 3 (by rfl) ⟨286931, by rfl⟩ : syracuseStep 1530301 = 573863) (by norm_num)
theorem B2038229 : Blo 1358498 2038229 := bbase (se 7 (by rfl) ⟨23885, by rfl⟩ : syracuseStep 2038229 = 47771) (by norm_num)
theorem B1530337 : Blo 1358498 1530337 := bbase (se 2 (by rfl) ⟨573876, by rfl⟩ : syracuseStep 1530337 = 1147753) (by norm_num)
theorem B2038253 : Blo 1358498 2038253 := bbase (se 3 (by rfl) ⟨382172, by rfl⟩ : syracuseStep 2038253 = 764345) (by norm_num)
theorem B2038277 : Blo 1358498 2038277 := bbase (se 4 (by rfl) ⟨191088, by rfl⟩ : syracuseStep 2038277 = 382177) (by norm_num)
theorem B1530373 : Blo 1358498 1530373 := bbase (se 4 (by rfl) ⟨143472, by rfl⟩ : syracuseStep 1530373 = 286945) (by norm_num)
theorem B2038301 : Blo 1358498 2038301 := bbase (se 3 (by rfl) ⟨382181, by rfl⟩ : syracuseStep 2038301 = 764363) (by norm_num)
theorem B1530409 : Blo 1358498 1530409 := bbase (se 2 (by rfl) ⟨573903, by rfl⟩ : syracuseStep 1530409 = 1147807) (by norm_num)
theorem B2038325 : Blo 1358498 2038325 := bbase (se 5 (by rfl) ⟨95546, by rfl⟩ : syracuseStep 2038325 = 191093) (by norm_num)
theorem B2038349 : Blo 1358498 2038349 := bbase (se 3 (by rfl) ⟨382190, by rfl⟩ : syracuseStep 2038349 = 764381) (by norm_num)
theorem B1530445 : Blo 1358498 1530445 := bbase (se 3 (by rfl) ⟨286958, by rfl⟩ : syracuseStep 1530445 = 573917) (by norm_num)
theorem B2038373 : Blo 1358498 2038373 := bbase (se 4 (by rfl) ⟨191097, by rfl⟩ : syracuseStep 2038373 = 382195) (by norm_num)
theorem B1530481 : Blo 1358498 1530481 := bbase (se 2 (by rfl) ⟨573930, by rfl⟩ : syracuseStep 1530481 = 1147861) (by norm_num)
theorem B2038397 : Blo 1358498 2038397 := bbase (se 3 (by rfl) ⟨382199, by rfl⟩ : syracuseStep 2038397 = 764399) (by norm_num)
theorem B2357885 : Blo 1358498 2357885 := bbase (se 3 (by rfl) ⟨442103, by rfl⟩ : syracuseStep 2357885 = 884207) (by norm_num)
theorem B2038421 : Blo 1358498 2038421 := bbase (se 6 (by rfl) ⟨47775, by rfl⟩ : syracuseStep 2038421 = 95551) (by norm_num)
theorem B1530517 : Blo 1358498 1530517 := bbase (se 6 (by rfl) ⟨35871, by rfl⟩ : syracuseStep 1530517 = 71743) (by norm_num)
theorem B2038445 : Blo 1358498 2038445 := bbase (se 3 (by rfl) ⟨382208, by rfl⟩ : syracuseStep 2038445 = 764417) (by norm_num)
theorem B4586165 : Blo 1358498 4586165 := bbase (se 5 (by rfl) ⟨214976, by rfl⟩ : syracuseStep 4586165 = 429953) (by norm_num)
theorem B1530553 : Blo 1358498 1530553 := bbase (se 2 (by rfl) ⟨573957, by rfl⟩ : syracuseStep 1530553 = 1147915) (by norm_num)
theorem B2579141 : Blo 1358498 2579141 := bbase (se 4 (by rfl) ⟨241794, by rfl⟩ : syracuseStep 2579141 = 483589) (by norm_num)
theorem B2038469 : Blo 1358498 2038469 := bbase (se 4 (by rfl) ⟨191106, by rfl⟩ : syracuseStep 2038469 = 382213) (by norm_num)
theorem B4897493 : Blo 1358498 4897493 := bbase (se 7 (by rfl) ⟨57392, by rfl⟩ : syracuseStep 4897493 = 114785) (by norm_num)
theorem B2038493 : Blo 1358498 2038493 := bbase (se 3 (by rfl) ⟨382217, by rfl⟩ : syracuseStep 2038493 = 764435) (by norm_num)
theorem B2038517 : Blo 1358498 2038517 := bbase (se 5 (by rfl) ⟨95555, by rfl⟩ : syracuseStep 2038517 = 191111) (by norm_num)
theorem B2038541 : Blo 1358498 2038541 := bbase (se 3 (by rfl) ⟨382226, by rfl⟩ : syracuseStep 2038541 = 764453) (by norm_num)
theorem B3267341 : Blo 1358498 3267341 := bbase (se 3 (by rfl) ⟨612626, by rfl⟩ : syracuseStep 3267341 = 1225253) (by norm_num)
theorem B3439381 : Blo 1358498 3439381 := bbase (se 6 (by rfl) ⟨80610, by rfl⟩ : syracuseStep 3439381 = 161221) (by norm_num)
theorem B2292509 : Blo 1358498 2292509 := bbase (se 3 (by rfl) ⟨429845, by rfl⟩ : syracuseStep 2292509 = 859691) (by norm_num)
theorem B2038565 : Blo 1358498 2038565 := bbase (se 4 (by rfl) ⟨191115, by rfl⟩ : syracuseStep 2038565 = 382231) (by norm_num)
theorem B2177837 : Blo 1358498 2177837 := bbase (se 3 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 2177837 = 816689) (by norm_num)
theorem B7748405 : Blo 1358498 7748405 := bbase (se 5 (by rfl) ⟨363206, by rfl⟩ : syracuseStep 7748405 = 726413) (by norm_num)
theorem B2038589 : Blo 1358498 2038589 := bbase (se 3 (by rfl) ⟨382235, by rfl⟩ : syracuseStep 2038589 = 764471) (by norm_num)
theorem B2038613 : Blo 1358498 2038613 := bbase (se 9 (by rfl) ⟨5972, by rfl⟩ : syracuseStep 2038613 = 11945) (by norm_num)
theorem B2579293 : Blo 1358498 2579293 := bbase (se 3 (by rfl) ⟨483617, by rfl⟩ : syracuseStep 2579293 = 967235) (by norm_num)
theorem B2038637 : Blo 1358498 2038637 := bbase (se 3 (by rfl) ⟨382244, by rfl⟩ : syracuseStep 2038637 = 764489) (by norm_num)
theorem B3439493 : Blo 1358498 3439493 := bbase (se 4 (by rfl) ⟨322452, by rfl⟩ : syracuseStep 3439493 = 644905) (by norm_num)
theorem B2038661 : Blo 1358498 2038661 := bbase (se 4 (by rfl) ⟨191124, by rfl⟩ : syracuseStep 2038661 = 382249) (by norm_num)
theorem B2292637 : Blo 1358498 2292637 := bbase (se 3 (by rfl) ⟨429869, by rfl⟩ : syracuseStep 2292637 = 859739) (by norm_num)
theorem B2038685 : Blo 1358498 2038685 := bbase (se 3 (by rfl) ⟨382253, by rfl⟩ : syracuseStep 2038685 = 764507) (by norm_num)
theorem B2038709 : Blo 1358498 2038709 := bbase (se 5 (by rfl) ⟨95564, by rfl⟩ : syracuseStep 2038709 = 191129) (by norm_num)
theorem B2038733 : Blo 1358498 2038733 := bbase (se 3 (by rfl) ⟨382262, by rfl⟩ : syracuseStep 2038733 = 764525) (by norm_num)
theorem B3267533 : Blo 1358498 3267533 := bbase (se 3 (by rfl) ⟨612662, by rfl⟩ : syracuseStep 3267533 = 1225325) (by norm_num)
theorem B2038757 : Blo 1358498 2038757 := bbase (se 4 (by rfl) ⟨191133, by rfl⟩ : syracuseStep 2038757 = 382267) (by norm_num)
theorem B2292725 : Blo 1358498 2292725 := bbase (se 5 (by rfl) ⟨107471, by rfl⟩ : syracuseStep 2292725 = 214943) (by norm_num)
theorem B2038781 : Blo 1358498 2038781 := bbase (se 3 (by rfl) ⟨382271, by rfl⟩ : syracuseStep 2038781 = 764543) (by norm_num)
theorem B2038805 : Blo 1358498 2038805 := bbase (se 6 (by rfl) ⟨47784, by rfl⟩ : syracuseStep 2038805 = 95569) (by norm_num)
theorem B1743913 : Blo 1358498 1743913 := bbase (se 2 (by rfl) ⟨653967, by rfl⟩ : syracuseStep 1743913 = 1307935) (by norm_num)
theorem B2038829 : Blo 1358498 2038829 := bbase (se 3 (by rfl) ⟨382280, by rfl⟩ : syracuseStep 2038829 = 764561) (by norm_num)
theorem B3267629 : Blo 1358498 3267629 := bbase (se 3 (by rfl) ⟨612680, by rfl⟩ : syracuseStep 3267629 = 1225361) (by norm_num)
theorem B3439685 : Blo 1358498 3439685 := bbase (se 4 (by rfl) ⟨322470, by rfl⟩ : syracuseStep 3439685 = 644941) (by norm_num)
theorem B2038853 : Blo 1358498 2038853 := bbase (se 4 (by rfl) ⟨191142, by rfl⟩ : syracuseStep 2038853 = 382285) (by norm_num)
theorem B2038877 : Blo 1358498 2038877 := bbase (se 3 (by rfl) ⟨382289, by rfl⟩ : syracuseStep 2038877 = 764579) (by norm_num)
theorem B1719397 : Blo 1358498 1719397 := bbase (se 4 (by rfl) ⟨161193, by rfl⟩ : syracuseStep 1719397 = 322387) (by norm_num)
theorem B4586597 : Blo 1358498 4586597 := bbase (se 4 (by rfl) ⟨429993, by rfl⟩ : syracuseStep 4586597 = 859987) (by norm_num)
theorem B2292853 : Blo 1358498 2292853 := bbase (se 5 (by rfl) ⟨107477, by rfl⟩ : syracuseStep 2292853 = 214955) (by norm_num)
theorem B2038901 : Blo 1358498 2038901 := bbase (se 5 (by rfl) ⟨95573, by rfl⟩ : syracuseStep 2038901 = 191147) (by norm_num)
theorem B2579597 : Blo 1358498 2579597 := bbase (se 3 (by rfl) ⟨483674, by rfl⟩ : syracuseStep 2579597 = 967349) (by norm_num)
theorem B2038925 : Blo 1358498 2038925 := bbase (se 3 (by rfl) ⟨382298, by rfl⟩ : syracuseStep 2038925 = 764597) (by norm_num)
theorem B2038949 : Blo 1358498 2038949 := bbase (se 4 (by rfl) ⟨191151, by rfl⟩ : syracuseStep 2038949 = 382303) (by norm_num)
theorem B2038973 : Blo 1358498 2038973 := bbase (se 3 (by rfl) ⟨382307, by rfl⟩ : syracuseStep 2038973 = 764615) (by norm_num)
theorem B2292941 : Blo 1358498 2292941 := bbase (se 3 (by rfl) ⟨429926, by rfl⟩ : syracuseStep 2292941 = 859853) (by norm_num)
theorem B2038997 : Blo 1358498 2038997 := bbase (se 7 (by rfl) ⟨23894, by rfl⟩ : syracuseStep 2038997 = 47789) (by norm_num)
theorem B2039021 : Blo 1358498 2039021 := bbase (se 3 (by rfl) ⟨382316, by rfl⟩ : syracuseStep 2039021 = 764633) (by norm_num)
theorem B2039045 : Blo 1358498 2039045 := bbase (se 4 (by rfl) ⟨191160, by rfl⟩ : syracuseStep 2039045 = 382321) (by norm_num)
theorem B1719569 : Blo 1358498 1719569 := bbase (se 2 (by rfl) ⟨644838, by rfl⟩ : syracuseStep 1719569 = 1289677) (by norm_num)
theorem B2039069 : Blo 1358498 2039069 := bbase (se 3 (by rfl) ⟨382325, by rfl⟩ : syracuseStep 2039069 = 764651) (by norm_num)
theorem B2039093 : Blo 1358498 2039093 := bbase (se 5 (by rfl) ⟨95582, by rfl⟩ : syracuseStep 2039093 = 191165) (by norm_num)
theorem B1719625 : Blo 1358498 1719625 := bbase (se 2 (by rfl) ⟨644859, by rfl⟩ : syracuseStep 1719625 = 1289719) (by norm_num)
theorem B2293069 : Blo 1358498 2293069 := bbase (se 3 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 2293069 = 859901) (by norm_num)
theorem B2039117 : Blo 1358498 2039117 := bbase (se 3 (by rfl) ⟨382334, by rfl⟩ : syracuseStep 2039117 = 764669) (by norm_num)
theorem B9796949 : Blo 1358498 9796949 := bbase (se 11 (by rfl) ⟨7175, by rfl⟩ : syracuseStep 9796949 = 14351) (by norm_num)
theorem B2039141 : Blo 1358498 2039141 := bbase (se 4 (by rfl) ⟨191169, by rfl⟩ : syracuseStep 2039141 = 382339) (by norm_num)
theorem B5807477 : Blo 1358498 5807477 := bbase (se 5 (by rfl) ⟨272225, by rfl⟩ : syracuseStep 5807477 = 544451) (by norm_num)
theorem B2039165 : Blo 1358498 2039165 := bbase (se 3 (by rfl) ⟨382343, by rfl⟩ : syracuseStep 2039165 = 764687) (by norm_num)
theorem B2039189 : Blo 1358498 2039189 := bbase (se 6 (by rfl) ⟨47793, by rfl⟩ : syracuseStep 2039189 = 95587) (by norm_num)
theorem B4652437 : Blo 1358498 4652437 := bbase (se 6 (by rfl) ⟨109041, by rfl⟩ : syracuseStep 4652437 = 218083) (by norm_num)
theorem B3440029 : Blo 1358498 3440029 := bbase (se 3 (by rfl) ⟨645005, by rfl⟩ : syracuseStep 3440029 = 1290011) (by norm_num)
theorem B2293157 : Blo 1358498 2293157 := bbase (se 4 (by rfl) ⟨214983, by rfl⟩ : syracuseStep 2293157 = 429967) (by norm_num)
theorem B2448805 : Blo 1358498 2448805 := bbase (se 4 (by rfl) ⟨229575, by rfl⟩ : syracuseStep 2448805 = 459151) (by norm_num)
theorem B1719721 : Blo 1358498 1719721 := bbase (se 2 (by rfl) ⟨644895, by rfl⟩ : syracuseStep 1719721 = 1289791) (by norm_num)
theorem B2039213 : Blo 1358498 2039213 := bbase (se 3 (by rfl) ⟨382352, by rfl⟩ : syracuseStep 2039213 = 764705) (by norm_num)
theorem B2039237 : Blo 1358498 2039237 := bbase (se 4 (by rfl) ⟨191178, by rfl⟩ : syracuseStep 2039237 = 382357) (by norm_num)
theorem B2039261 : Blo 1358498 2039261 := bbase (se 3 (by rfl) ⟨382361, by rfl⟩ : syracuseStep 2039261 = 764723) (by norm_num)
theorem B2039285 : Blo 1358498 2039285 := bbase (se 5 (by rfl) ⟨95591, by rfl⟩ : syracuseStep 2039285 = 191183) (by norm_num)
theorem B3726853 : Blo 1358498 3726853 := bbase (se 4 (by rfl) ⟨349392, by rfl⟩ : syracuseStep 3726853 = 698785) (by norm_num)
theorem B3440141 : Blo 1358498 3440141 := bbase (se 3 (by rfl) ⟨645026, by rfl⟩ : syracuseStep 3440141 = 1290053) (by norm_num)
theorem B2039309 : Blo 1358498 2039309 := bbase (se 3 (by rfl) ⟨382370, by rfl⟩ : syracuseStep 2039309 = 764741) (by norm_num)
theorem B4587029 : Blo 1358498 4587029 := bbase (se 6 (by rfl) ⟨107508, by rfl⟩ : syracuseStep 4587029 = 215017) (by norm_num)
theorem B5160469 : Blo 1358498 5160469 := bbase (se 6 (by rfl) ⟨120948, by rfl⟩ : syracuseStep 5160469 = 241897) (by norm_num)
theorem B2293285 : Blo 1358498 2293285 := bbase (se 4 (by rfl) ⟨214995, by rfl⟩ : syracuseStep 2293285 = 429991) (by norm_num)
theorem B2039333 : Blo 1358498 2039333 := bbase (se 4 (by rfl) ⟨191187, by rfl⟩ : syracuseStep 2039333 = 382375) (by norm_num)
theorem B2039357 : Blo 1358498 2039357 := bbase (se 3 (by rfl) ⟨382379, by rfl⟩ : syracuseStep 2039357 = 764759) (by norm_num)
theorem B1719893 : Blo 1358498 1719893 := bbase (se 8 (by rfl) ⟨10077, by rfl⟩ : syracuseStep 1719893 = 20155) (by norm_num)
theorem B7347797 : Blo 1358498 7347797 := bbase (se 8 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 7347797 = 86107) (by norm_num)
theorem B2039381 : Blo 1358498 2039381 := bbase (se 8 (by rfl) ⟨11949, by rfl⟩ : syracuseStep 2039381 = 23899) (by norm_num)
theorem B2039405 : Blo 1358498 2039405 := bbase (se 3 (by rfl) ⟨382388, by rfl⟩ : syracuseStep 2039405 = 764777) (by norm_num)
theorem B2293373 : Blo 1358498 2293373 := bbase (se 3 (by rfl) ⟨430007, by rfl⟩ : syracuseStep 2293373 = 860015) (by norm_num)
theorem B2039429 : Blo 1358498 2039429 := bbase (se 4 (by rfl) ⟨191196, by rfl⟩ : syracuseStep 2039429 = 382393) (by norm_num)
theorem B1719949 : Blo 1358498 1719949 := bbase (se 3 (by rfl) ⟨322490, by rfl⟩ : syracuseStep 1719949 = 644981) (by norm_num)
theorem B2039453 : Blo 1358498 2039453 := bbase (se 3 (by rfl) ⟨382397, by rfl⟩ : syracuseStep 2039453 = 764795) (by norm_num)
theorem B6880949 : Blo 1358498 6880949 := bbase (se 5 (by rfl) ⟨322544, by rfl⟩ : syracuseStep 6880949 = 645089) (by norm_num)
theorem B2039477 : Blo 1358498 2039477 := bbase (se 5 (by rfl) ⟨95600, by rfl⟩ : syracuseStep 2039477 = 191201) (by norm_num)
theorem B3440333 : Blo 1358498 3440333 := bbase (se 3 (by rfl) ⟨645062, by rfl⟩ : syracuseStep 3440333 = 1290125) (by norm_num)
theorem B2039501 : Blo 1358498 2039501 := bbase (se 3 (by rfl) ⟨382406, by rfl⟩ : syracuseStep 2039501 = 764813) (by norm_num)
theorem B2039525 : Blo 1358498 2039525 := bbase (se 4 (by rfl) ⟨191205, by rfl⟩ : syracuseStep 2039525 = 382411) (by norm_num)
theorem B1720045 : Blo 1358498 1720045 := bbase (se 3 (by rfl) ⟨322508, by rfl⟩ : syracuseStep 1720045 = 645017) (by norm_num)
theorem B2293501 : Blo 1358498 2293501 := bbase (se 3 (by rfl) ⟨430031, by rfl⟩ : syracuseStep 2293501 = 860063) (by norm_num)
theorem B2039549 : Blo 1358498 2039549 := bbase (se 3 (by rfl) ⟨382415, by rfl⟩ : syracuseStep 2039549 = 764831) (by norm_num)
theorem B2178829 : Blo 1358498 2178829 := bbase (se 3 (by rfl) ⟨408530, by rfl⟩ : syracuseStep 2178829 = 817061) (by norm_num)
theorem B8265493 : Blo 1358498 8265493 := bbase (se 6 (by rfl) ⟨193722, by rfl⟩ : syracuseStep 8265493 = 387445) (by norm_num)
theorem B2039573 : Blo 1358498 2039573 := bbase (se 6 (by rfl) ⟨47802, by rfl⟩ : syracuseStep 2039573 = 95605) (by norm_num)
theorem B2039597 : Blo 1358498 2039597 := bbase (se 3 (by rfl) ⟨382424, by rfl⟩ : syracuseStep 2039597 = 764849) (by norm_num)
theorem B8716085 : Blo 1358498 8716085 := bbase (se 5 (by rfl) ⟨408566, by rfl⟩ : syracuseStep 8716085 = 817133) (by norm_num)
theorem B5160773 : Blo 1358498 5160773 := bbase (se 4 (by rfl) ⟨483822, by rfl⟩ : syracuseStep 5160773 = 967645) (by norm_num)
theorem B2039621 : Blo 1358498 2039621 := bbase (se 4 (by rfl) ⟨191214, by rfl⟩ : syracuseStep 2039621 = 382429) (by norm_num)
theorem B2293589 : Blo 1358498 2293589 := bbase (se 9 (by rfl) ⟨6719, by rfl⟩ : syracuseStep 2293589 = 13439) (by norm_num)
theorem B2039645 : Blo 1358498 2039645 := bbase (se 3 (by rfl) ⟨382433, by rfl⟩ : syracuseStep 2039645 = 764867) (by norm_num)
theorem B2039669 : Blo 1358498 2039669 := bbase (se 5 (by rfl) ⟨95609, by rfl⟩ : syracuseStep 2039669 = 191219) (by norm_num)
theorem B2580349 : Blo 1358498 2580349 := bbase (se 3 (by rfl) ⟨483815, by rfl⟩ : syracuseStep 2580349 = 967631) (by norm_num)
theorem B2039693 : Blo 1358498 2039693 := bbase (se 3 (by rfl) ⟨382442, by rfl⟩ : syracuseStep 2039693 = 764885) (by norm_num)
theorem B1720217 : Blo 1358498 1720217 := bbase (se 2 (by rfl) ⟨645081, by rfl⟩ : syracuseStep 1720217 = 1290163) (by norm_num)
theorem B2039717 : Blo 1358498 2039717 := bbase (se 4 (by rfl) ⟨191223, by rfl⟩ : syracuseStep 2039717 = 382447) (by norm_num)
theorem B4358069 : Blo 1358498 4358069 := bbase (se 5 (by rfl) ⟨204284, by rfl⟩ : syracuseStep 4358069 = 408569) (by norm_num)
theorem B2039741 : Blo 1358498 2039741 := bbase (se 3 (by rfl) ⟨382451, by rfl⟩ : syracuseStep 2039741 = 764903) (by norm_num)
theorem B4587461 : Blo 1358498 4587461 := bbase (se 4 (by rfl) ⟨430074, by rfl⟩ : syracuseStep 4587461 = 860149) (by norm_num)
theorem B1720273 : Blo 1358498 1720273 := bbase (se 2 (by rfl) ⟨645102, by rfl⟩ : syracuseStep 1720273 = 1290205) (by norm_num)
theorem B2293717 : Blo 1358498 2293717 := bbase (se 7 (by rfl) ⟨26879, by rfl⟩ : syracuseStep 2293717 = 53759) (by norm_num)
theorem B2039765 : Blo 1358498 2039765 := bbase (se 7 (by rfl) ⟨23903, by rfl⟩ : syracuseStep 2039765 = 47807) (by norm_num)
theorem B2449381 : Blo 1358498 2449381 := bbase (se 4 (by rfl) ⟨229629, by rfl⟩ : syracuseStep 2449381 = 459259) (by norm_num)
theorem B2039789 : Blo 1358498 2039789 := bbase (se 3 (by rfl) ⟨382460, by rfl⟩ : syracuseStep 2039789 = 764921) (by norm_num)
theorem B1359875 : Blo 1358498 1359875 := bstep (se 1 (by rfl) ⟨1019906, by rfl⟩ : syracuseStep 1359875 = 2039813) B2039813
theorem B3440657 : Blo 1358498 3440657 := bstep (se 2 (by rfl) ⟨1290246, by rfl⟩ : syracuseStep 3440657 = 2580493) B2580493
theorem B2039825 : Blo 1358498 2039825 := bstep (se 2 (by rfl) ⟨764934, by rfl⟩ : syracuseStep 2039825 = 1529869) B1529869
theorem B1359891 : Blo 1358498 1359891 := bstep (se 1 (by rfl) ⟨1019918, by rfl⟩ : syracuseStep 1359891 = 2039837) B2039837
theorem B2039843 : Blo 1358498 2039843 := bstep (se 1 (by rfl) ⟨1529882, by rfl⟩ : syracuseStep 2039843 = 3059765) B3059765
theorem B1359907 : Blo 1358498 1359907 := bstep (se 1 (by rfl) ⟨1019930, by rfl⟩ : syracuseStep 1359907 = 2039861) B2039861
theorem B4587569 : Blo 1358498 4587569 := bstep (se 2 (by rfl) ⟨1720338, by rfl⟩ : syracuseStep 4587569 = 3440677) B3440677
theorem B1359923 : Blo 1358498 1359923 := bstep (se 1 (by rfl) ⟨1019942, by rfl⟩ : syracuseStep 1359923 = 2039885) B2039885
theorem B2293825 : Blo 1358498 2293825 := bstep (se 2 (by rfl) ⟨860184, by rfl⟩ : syracuseStep 2293825 = 1720369) B1720369
theorem B2039873 : Blo 1358498 2039873 := bstep (se 2 (by rfl) ⟨764952, by rfl⟩ : syracuseStep 2039873 = 1529905) B1529905
theorem B1359939 : Blo 1358498 1359939 := bstep (se 1 (by rfl) ⟨1019954, by rfl⟩ : syracuseStep 1359939 = 2039909) B2039909
theorem B2039891 : Blo 1358498 2039891 := bstep (se 1 (by rfl) ⟨1529918, by rfl⟩ : syracuseStep 2039891 = 3059837) B3059837
theorem B1359955 : Blo 1358498 1359955 := bstep (se 1 (by rfl) ⟨1019966, by rfl⟩ : syracuseStep 1359955 = 2039933) B2039933
theorem B2293859 : Blo 1358498 2293859 := bstep (se 1 (by rfl) ⟨1720394, by rfl⟩ : syracuseStep 2293859 = 3440789) B3440789
theorem B1359971 : Blo 1358498 1359971 := bstep (se 1 (by rfl) ⟨1019978, by rfl⟩ : syracuseStep 1359971 = 2039957) B2039957
theorem B2039921 : Blo 1358498 2039921 := bstep (se 2 (by rfl) ⟨764970, by rfl⟩ : syracuseStep 2039921 = 1529941) B1529941
theorem B1720435 : Blo 1358498 1720435 := bstep (se 1 (by rfl) ⟨1290326, by rfl⟩ : syracuseStep 1720435 = 2580653) B2580653
theorem B1359987 : Blo 1358498 1359987 := bstep (se 1 (by rfl) ⟨1019990, by rfl⟩ : syracuseStep 1359987 = 2039981) B2039981
theorem B2039939 : Blo 1358498 2039939 := bstep (se 1 (by rfl) ⟨1529954, by rfl⟩ : syracuseStep 2039939 = 3059909) B3059909
theorem B1360003 : Blo 1358498 1360003 := bstep (se 1 (by rfl) ⟨1020002, by rfl⟩ : syracuseStep 1360003 = 2040005) B2040005
theorem B1360019 : Blo 1358498 1360019 := bstep (se 1 (by rfl) ⟨1020014, by rfl⟩ : syracuseStep 1360019 = 2040029) B2040029
theorem B2039969 : Blo 1358498 2039969 := bstep (se 2 (by rfl) ⟨764988, by rfl⟩ : syracuseStep 2039969 = 1529977) B1529977
theorem B1360035 : Blo 1358498 1360035 := bstep (se 1 (by rfl) ⟨1020026, by rfl⟩ : syracuseStep 1360035 = 2040053) B2040053
theorem B2039987 : Blo 1358498 2039987 := bstep (se 1 (by rfl) ⟨1529990, by rfl⟩ : syracuseStep 2039987 = 3059981) B3059981
theorem B1360051 : Blo 1358498 1360051 := bstep (se 1 (by rfl) ⟨1020038, by rfl⟩ : syracuseStep 1360051 = 2040077) B2040077
theorem B1360067 : Blo 1358498 1360067 := bstep (se 1 (by rfl) ⟨1020050, by rfl⟩ : syracuseStep 1360067 = 2040101) B2040101
theorem B2040017 : Blo 1358498 2040017 := bstep (se 2 (by rfl) ⟨765006, by rfl⟩ : syracuseStep 2040017 = 1530013) B1530013
theorem B1720531 : Blo 1358498 1720531 := bstep (se 1 (by rfl) ⟨1290398, by rfl⟩ : syracuseStep 1720531 = 2580797) B2580797
theorem B1360083 : Blo 1358498 1360083 := bstep (se 1 (by rfl) ⟨1020062, by rfl⟩ : syracuseStep 1360083 = 2040125) B2040125
theorem B2293987 : Blo 1358498 2293987 := bstep (se 1 (by rfl) ⟨1720490, by rfl⟩ : syracuseStep 2293987 = 3440981) B3440981
theorem B2040035 : Blo 1358498 2040035 := bstep (se 1 (by rfl) ⟨1530026, by rfl⟩ : syracuseStep 2040035 = 3060053) B3060053
theorem B1360099 : Blo 1358498 1360099 := bstep (se 1 (by rfl) ⟨1020074, by rfl⟩ : syracuseStep 1360099 = 2040149) B2040149
theorem B1360115 : Blo 1358498 1360115 := bstep (se 1 (by rfl) ⟨1020086, by rfl⟩ : syracuseStep 1360115 = 2040173) B2040173
theorem B2040065 : Blo 1358498 2040065 := bstep (se 2 (by rfl) ⟨765024, by rfl⟩ : syracuseStep 2040065 = 1530049) B1530049
theorem B1360131 : Blo 1358498 1360131 := bstep (se 1 (by rfl) ⟨1020098, by rfl⟩ : syracuseStep 1360131 = 2040197) B2040197
theorem B5161229 : Blo 1358498 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B2040083 : Blo 1358498 2040083 := bstep (se 1 (by rfl) ⟨1530062, by rfl⟩ : syracuseStep 2040083 = 3060125) B3060125
theorem B1360147 : Blo 1358498 1360147 := bstep (se 1 (by rfl) ⟨1020110, by rfl⟩ : syracuseStep 1360147 = 2040221) B2040221
theorem B1360163 : Blo 1358498 1360163 := bstep (se 1 (by rfl) ⟨1020122, by rfl⟩ : syracuseStep 1360163 = 2040245) B2040245
theorem B2040113 : Blo 1358498 2040113 := bstep (se 2 (by rfl) ⟨765042, by rfl⟩ : syracuseStep 2040113 = 1530085) B1530085
theorem B1360179 : Blo 1358498 1360179 := bstep (se 1 (by rfl) ⟨1020134, by rfl⟩ : syracuseStep 1360179 = 2040269) B2040269
theorem B2040131 : Blo 1358498 2040131 := bstep (se 1 (by rfl) ⟨1530098, by rfl⟩ : syracuseStep 2040131 = 3060197) B3060197
theorem B1360195 : Blo 1358498 1360195 := bstep (se 1 (by rfl) ⟨1020146, by rfl⟩ : syracuseStep 1360195 = 2040293) B2040293
theorem B1360211 : Blo 1358498 1360211 := bstep (se 1 (by rfl) ⟨1020158, by rfl⟩ : syracuseStep 1360211 = 2040317) B2040317
theorem B2040161 : Blo 1358498 2040161 := bstep (se 2 (by rfl) ⟨765060, by rfl⟩ : syracuseStep 2040161 = 1530121) B1530121
theorem B2580835 : Blo 1358498 2580835 := bstep (se 1 (by rfl) ⟨1935626, by rfl⟩ : syracuseStep 2580835 = 3871253) B3871253
theorem B13066595 : Blo 1358498 13066595 := bstep (se 1 (by rfl) ⟨9799946, by rfl⟩ : syracuseStep 13066595 = 19599893) B19599893
theorem B1360227 : Blo 1358498 1360227 := bstep (se 1 (by rfl) ⟨1020170, by rfl⟩ : syracuseStep 1360227 = 2040341) B2040341
theorem B2294129 : Blo 1358498 2294129 := bstep (se 2 (by rfl) ⟨860298, by rfl⟩ : syracuseStep 2294129 = 1720597) B1720597
theorem B2040179 : Blo 1358498 2040179 := bstep (se 1 (by rfl) ⟨1530134, by rfl⟩ : syracuseStep 2040179 = 3060269) B3060269
theorem B1360243 : Blo 1358498 1360243 := bstep (se 1 (by rfl) ⟨1020182, by rfl⟩ : syracuseStep 1360243 = 2040365) B2040365
theorem B1360259 : Blo 1358498 1360259 := bstep (se 1 (by rfl) ⟨1020194, by rfl⟩ : syracuseStep 1360259 = 2040389) B2040389
theorem B2040209 : Blo 1358498 2040209 := bstep (se 2 (by rfl) ⟨765078, by rfl⟩ : syracuseStep 2040209 = 1530157) B1530157
theorem B1360275 : Blo 1358498 1360275 := bstep (se 1 (by rfl) ⟨1020206, by rfl⟩ : syracuseStep 1360275 = 2040413) B2040413
theorem B2040227 : Blo 1358498 2040227 := bstep (se 1 (by rfl) ⟨1530170, by rfl⟩ : syracuseStep 2040227 = 3060341) B3060341
theorem B1360291 : Blo 1358498 1360291 := bstep (se 1 (by rfl) ⟨1020218, by rfl⟩ : syracuseStep 1360291 = 2040437) B2040437
theorem B1360307 : Blo 1358498 1360307 := bstep (se 1 (by rfl) ⟨1020230, by rfl⟩ : syracuseStep 1360307 = 2040461) B2040461
theorem B2040257 : Blo 1358498 2040257 := bstep (se 2 (by rfl) ⟨765096, by rfl⟩ : syracuseStep 2040257 = 1530193) B1530193
theorem B1360323 : Blo 1358498 1360323 := bstep (se 1 (by rfl) ⟨1020242, by rfl⟩ : syracuseStep 1360323 = 2040485) B2040485
theorem B2040275 : Blo 1358498 2040275 := bstep (se 1 (by rfl) ⟨1530206, by rfl⟩ : syracuseStep 2040275 = 3060413) B3060413
theorem B1360339 : Blo 1358498 1360339 := bstep (se 1 (by rfl) ⟨1020254, by rfl⟩ : syracuseStep 1360339 = 2040509) B2040509
theorem B1360355 : Blo 1358498 1360355 := bstep (se 1 (by rfl) ⟨1020266, by rfl⟩ : syracuseStep 1360355 = 2040533) B2040533
theorem B2294257 : Blo 1358498 2294257 := bstep (se 2 (by rfl) ⟨860346, by rfl⟩ : syracuseStep 2294257 = 1720693) B1720693
theorem B2040305 : Blo 1358498 2040305 := bstep (se 2 (by rfl) ⟨765114, by rfl⟩ : syracuseStep 2040305 = 1530229) B1530229
theorem B1360371 : Blo 1358498 1360371 := bstep (se 1 (by rfl) ⟨1020278, by rfl⟩ : syracuseStep 1360371 = 2040557) B2040557
theorem B2040323 : Blo 1358498 2040323 := bstep (se 1 (by rfl) ⟨1530242, by rfl⟩ : syracuseStep 2040323 = 3060485) B3060485
theorem B1360387 : Blo 1358498 1360387 := bstep (se 1 (by rfl) ⟨1020290, by rfl⟩ : syracuseStep 1360387 = 2040581) B2040581
theorem B16769549 : Blo 1358498 16769549 := bstep (se 3 (by rfl) ⟨3144290, by rfl⟩ : syracuseStep 16769549 = 6288581) B6288581
theorem B2294291 : Blo 1358498 2294291 := bstep (se 1 (by rfl) ⟨1720718, by rfl⟩ : syracuseStep 2294291 = 3441437) B3441437
theorem B1360403 : Blo 1358498 1360403 := bstep (se 1 (by rfl) ⟨1020302, by rfl⟩ : syracuseStep 1360403 = 2040605) B2040605
theorem B2040353 : Blo 1358498 2040353 := bstep (se 2 (by rfl) ⟨765132, by rfl⟩ : syracuseStep 2040353 = 1530265) B1530265
theorem B1360419 : Blo 1358498 1360419 := bstep (se 1 (by rfl) ⟨1020314, by rfl⟩ : syracuseStep 1360419 = 2040629) B2040629
theorem B2040371 : Blo 1358498 2040371 := bstep (se 1 (by rfl) ⟨1530278, by rfl⟩ : syracuseStep 2040371 = 3060557) B3060557
theorem B1360435 : Blo 1358498 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B1360451 : Blo 1358498 1360451 := bstep (se 1 (by rfl) ⟨1020338, by rfl⟩ : syracuseStep 1360451 = 2040677) B2040677
theorem B4588109 : Blo 1358498 4588109 := bstep (se 3 (by rfl) ⟨860270, by rfl⟩ : syracuseStep 4588109 = 1720541) B1720541
theorem B2040401 : Blo 1358498 2040401 := bstep (se 2 (by rfl) ⟨765150, by rfl⟩ : syracuseStep 2040401 = 1530301) B1530301
theorem B1360467 : Blo 1358498 1360467 := bstep (se 1 (by rfl) ⟨1020350, by rfl⟩ : syracuseStep 1360467 = 2040701) B2040701
theorem B2040419 : Blo 1358498 2040419 := bstep (se 1 (by rfl) ⟨1530314, by rfl⟩ : syracuseStep 2040419 = 3060629) B3060629
theorem B1360483 : Blo 1358498 1360483 := bstep (se 1 (by rfl) ⟨1020362, by rfl⟩ : syracuseStep 1360483 = 2040725) B2040725
theorem B13951601 : Blo 1358498 13951601 := bstep (se 2 (by rfl) ⟨5231850, by rfl⟩ : syracuseStep 13951601 = 10463701) B10463701
theorem B4588163 : Blo 1358498 4588163 := bstep (se 1 (by rfl) ⟨3441122, by rfl⟩ : syracuseStep 4588163 = 6882245) B6882245
theorem B2040449 : Blo 1358498 2040449 := bstep (se 2 (by rfl) ⟨765168, by rfl⟩ : syracuseStep 2040449 = 1530337) B1530337
theorem B2294419 : Blo 1358498 2294419 := bstep (se 1 (by rfl) ⟨1720814, by rfl⟩ : syracuseStep 2294419 = 3441629) B3441629
theorem B2040467 : Blo 1358498 2040467 := bstep (se 1 (by rfl) ⟨1530350, by rfl⟩ : syracuseStep 2040467 = 3060701) B3060701
theorem B2040497 : Blo 1358498 2040497 := bstep (se 2 (by rfl) ⟨765186, by rfl⟩ : syracuseStep 2040497 = 1530373) B1530373
theorem B1721027 : Blo 1358498 1721027 := bstep (se 1 (by rfl) ⟨1290770, by rfl⟩ : syracuseStep 1721027 = 2581541) B2581541
theorem B2040515 : Blo 1358498 2040515 := bstep (se 1 (by rfl) ⟨1530386, by rfl⟩ : syracuseStep 2040515 = 3060773) B3060773
theorem B2040545 : Blo 1358498 2040545 := bstep (se 2 (by rfl) ⟨765204, by rfl⟩ : syracuseStep 2040545 = 1530409) B1530409
theorem B2040563 : Blo 1358498 2040563 := bstep (se 1 (by rfl) ⟨1530422, by rfl⟩ : syracuseStep 2040563 = 3060845) B3060845
theorem B2040593 : Blo 1358498 2040593 := bstep (se 2 (by rfl) ⟨765222, by rfl⟩ : syracuseStep 2040593 = 1530445) B1530445
theorem B2294561 : Blo 1358498 2294561 := bstep (se 2 (by rfl) ⟨860460, by rfl⟩ : syracuseStep 2294561 = 1720921) B1720921
theorem B6882083 : Blo 1358498 6882083 := bstep (se 1 (by rfl) ⟨5161562, by rfl⟩ : syracuseStep 6882083 = 10323125) B10323125
theorem B2581283 : Blo 1358498 2581283 := bstep (se 1 (by rfl) ⟨1935962, by rfl⟩ : syracuseStep 2581283 = 3871925) B3871925
theorem B2040611 : Blo 1358498 2040611 := bstep (se 1 (by rfl) ⟨1530458, by rfl⟩ : syracuseStep 2040611 = 3060917) B3060917
theorem B2040641 : Blo 1358498 2040641 := bstep (se 2 (by rfl) ⟨765240, by rfl⟩ : syracuseStep 2040641 = 1530481) B1530481
theorem B11019077 : Blo 1358498 11019077 := bstep (se 4 (by rfl) ⟨1033038, by rfl⟩ : syracuseStep 11019077 = 2066077) B2066077
theorem B2040659 : Blo 1358498 2040659 := bstep (se 1 (by rfl) ⟨1530494, by rfl⟩ : syracuseStep 2040659 = 3060989) B3060989
theorem B3924845 : Blo 1358498 3924845 := bstep (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) B1471817
theorem B4653937 : Blo 1358498 4653937 := bstep (se 2 (by rfl) ⟨1745226, by rfl⟩ : syracuseStep 4653937 = 3490453) B3490453
theorem B2040689 : Blo 1358498 2040689 := bstep (se 2 (by rfl) ⟨765258, by rfl⟩ : syracuseStep 2040689 = 1530517) B1530517
theorem B2040707 : Blo 1358498 2040707 := bstep (se 1 (by rfl) ⟨1530530, by rfl⟩ : syracuseStep 2040707 = 3061061) B3061061
theorem B4588433 : Blo 1358498 4588433 := bstep (se 2 (by rfl) ⟨1720662, by rfl⟩ : syracuseStep 4588433 = 3441325) B3441325
theorem B2294689 : Blo 1358498 2294689 := bstep (se 2 (by rfl) ⟨860508, by rfl⟩ : syracuseStep 2294689 = 1721017) B1721017
theorem B2040737 : Blo 1358498 2040737 := bstep (se 2 (by rfl) ⟨765276, by rfl⟩ : syracuseStep 2040737 = 1530553) B1530553
theorem B5235619 : Blo 1358498 5235619 := bstep (se 1 (by rfl) ⟨3926714, by rfl⟩ : syracuseStep 5235619 = 7853429) B7853429
theorem B2294723 : Blo 1358498 2294723 := bstep (se 1 (by rfl) ⟨1721042, by rfl⟩ : syracuseStep 2294723 = 3442085) B3442085
theorem B2982865 : Blo 1358498 2982865 := bstep (se 2 (by rfl) ⟨1118574, by rfl⟩ : syracuseStep 2982865 = 2237149) B2237149
theorem B3441649 : Blo 1358498 3441649 := bstep (se 2 (by rfl) ⟨1290618, by rfl⟩ : syracuseStep 3441649 = 2581237) B2581237
theorem B2581571 : Blo 1358498 2581571 := bstep (se 1 (by rfl) ⟨1936178, by rfl⟩ : syracuseStep 2581571 = 3872357) B3872357
theorem B2294851 : Blo 1358498 2294851 := bstep (se 1 (by rfl) ⟨1721138, by rfl⟩ : syracuseStep 2294851 = 3442277) B3442277
theorem B3056849 : Blo 1358498 3056849 := bstep (se 2 (by rfl) ⟨1146318, by rfl⟩ : syracuseStep 3056849 = 2292637) B2292637
theorem B2294993 : Blo 1358498 2294993 := bstep (se 2 (by rfl) ⟨860622, by rfl⟩ : syracuseStep 2294993 = 1721245) B1721245
theorem B1934561 : Blo 1358498 1934561 := bstep (se 2 (by rfl) ⟨725460, by rfl⟩ : syracuseStep 1934561 = 1450921) B1450921
theorem B3056867 : Blo 1358498 3056867 := bstep (se 1 (by rfl) ⟨2292650, by rfl⟩ : syracuseStep 3056867 = 4585301) B4585301
theorem B3441923 : Blo 1358498 3441923 := bstep (se 1 (by rfl) ⟨2581442, by rfl⟩ : syracuseStep 3441923 = 5162885) B5162885
theorem B1934641 : Blo 1358498 1934641 := bstep (se 2 (by rfl) ⟨725490, by rfl⟩ : syracuseStep 1934641 = 1450981) B1450981
theorem B2295121 : Blo 1358498 2295121 := bstep (se 2 (by rfl) ⟨860670, by rfl⟩ : syracuseStep 2295121 = 1721341) B1721341
theorem B2295155 : Blo 1358498 2295155 := bstep (se 1 (by rfl) ⟨1721366, by rfl⟩ : syracuseStep 2295155 = 3442733) B3442733
theorem B1721731 : Blo 1358498 1721731 := bstep (se 1 (by rfl) ⟨1291298, by rfl⟩ : syracuseStep 1721731 = 2582597) B2582597
theorem B4588973 : Blo 1358498 4588973 := bstep (se 3 (by rfl) ⟨860432, by rfl⟩ : syracuseStep 4588973 = 1720865) B1720865
theorem B3442115 : Blo 1358498 3442115 := bstep (se 1 (by rfl) ⟨2581586, by rfl⟩ : syracuseStep 3442115 = 5163173) B5163173
theorem B4589027 : Blo 1358498 4589027 := bstep (se 1 (by rfl) ⟨3441770, by rfl⟩ : syracuseStep 4589027 = 6883541) B6883541
theorem B1721827 : Blo 1358498 1721827 := bstep (se 1 (by rfl) ⟨1291370, by rfl⟩ : syracuseStep 1721827 = 2582741) B2582741
theorem B3057137 : Blo 1358498 3057137 := bstep (se 2 (by rfl) ⟨1146426, by rfl⟩ : syracuseStep 3057137 = 2292853) B2292853
theorem B2295283 : Blo 1358498 2295283 := bstep (se 1 (by rfl) ⟨1721462, by rfl⟩ : syracuseStep 2295283 = 3442925) B3442925
theorem B3057155 : Blo 1358498 3057155 := bstep (se 1 (by rfl) ⟨2292866, by rfl⟩ : syracuseStep 3057155 = 4585733) B4585733
theorem B6981155 : Blo 1358498 6981155 := bstep (se 1 (by rfl) ⟨5235866, by rfl⟩ : syracuseStep 6981155 = 10471733) B10471733
theorem B6882893 : Blo 1358498 6882893 := bstep (se 3 (by rfl) ⟨1290542, by rfl⟩ : syracuseStep 6882893 = 2581085) B2581085
theorem B15492707 : Blo 1358498 15492707 := bstep (se 1 (by rfl) ⟨11619530, by rfl⟩ : syracuseStep 15492707 = 23239061) B23239061
theorem B2295425 : Blo 1358498 2295425 := bstep (se 2 (by rfl) ⟨860784, by rfl⟩ : syracuseStep 2295425 = 1721569) B1721569
theorem B3098339 : Blo 1358498 3098339 := bstep (se 1 (by rfl) ⟨2323754, by rfl⟩ : syracuseStep 3098339 = 4647509) B4647509
theorem B4589297 : Blo 1358498 4589297 := bstep (se 2 (by rfl) ⟨1720986, by rfl⟩ : syracuseStep 4589297 = 3441973) B3441973
theorem B2295553 : Blo 1358498 2295553 := bstep (se 2 (by rfl) ⟨860832, by rfl⟩ : syracuseStep 2295553 = 1721665) B1721665
theorem B3057425 : Blo 1358498 3057425 := bstep (se 2 (by rfl) ⟨1146534, by rfl⟩ : syracuseStep 3057425 = 2293069) B2293069
theorem B3057443 : Blo 1358498 3057443 := bstep (se 1 (by rfl) ⟨2293082, by rfl⟩ : syracuseStep 3057443 = 4586165) B4586165
theorem B2295587 : Blo 1358498 2295587 := bstep (se 1 (by rfl) ⟨1721690, by rfl⟩ : syracuseStep 2295587 = 3443381) B3443381
theorem B6203249 : Blo 1358498 6203249 := bstep (se 2 (by rfl) ⟨2326218, by rfl⟩ : syracuseStep 6203249 = 4652437) B4652437
theorem B1451891 : Blo 1358498 1451891 := bstep (se 1 (by rfl) ⟨1088918, by rfl⟩ : syracuseStep 1451891 = 2177837) B2177837
theorem B3098531 : Blo 1358498 3098531 := bstep (se 1 (by rfl) ⟨2323898, by rfl⟩ : syracuseStep 3098531 = 4647797) B4647797
theorem B2295715 : Blo 1358498 2295715 := bstep (se 1 (by rfl) ⟨1721786, by rfl⟩ : syracuseStep 2295715 = 3443573) B3443573
theorem B12396485 : Blo 1358498 12396485 := bstep (se 4 (by rfl) ⟨1162170, by rfl⟩ : syracuseStep 12396485 = 2324341) B2324341
theorem B2582513 : Blo 1358498 2582513 := bstep (se 2 (by rfl) ⟨968442, by rfl⟩ : syracuseStep 2582513 = 1936885) B1936885
theorem B1837075 : Blo 1358498 1837075 := bstep (se 1 (by rfl) ⟨1377806, by rfl⟩ : syracuseStep 1837075 = 2755613) B2755613
theorem B3057713 : Blo 1358498 3057713 := bstep (se 2 (by rfl) ⟨1146642, by rfl⟩ : syracuseStep 3057713 = 2293285) B2293285
theorem B3057731 : Blo 1358498 3057731 := bstep (se 1 (by rfl) ⟨2293298, by rfl⟩ : syracuseStep 3057731 = 4586597) B4586597
theorem B1935427 : Blo 1358498 1935427 := bstep (se 1 (by rfl) ⟨1451570, by rfl⟩ : syracuseStep 1935427 = 2903141) B2903141
theorem B2615377 : Blo 1358498 2615377 := bstep (se 2 (by rfl) ⟨980766, by rfl⟩ : syracuseStep 2615377 = 1961533) B1961533
theorem B2902115 : Blo 1358498 2902115 := bstep (se 1 (by rfl) ⟨2176586, by rfl⟩ : syracuseStep 2902115 = 4353173) B4353173
theorem B6531299 : Blo 1358498 6531299 := bstep (se 1 (by rfl) ⟨4898474, by rfl⟩ : syracuseStep 6531299 = 9796949) B9796949
theorem B4589837 : Blo 1358498 4589837 := bstep (se 3 (by rfl) ⟨860594, by rfl⟩ : syracuseStep 4589837 = 1721189) B1721189
theorem B4589891 : Blo 1358498 4589891 := bstep (se 1 (by rfl) ⟨3442418, by rfl⟩ : syracuseStep 4589891 = 6884837) B6884837
theorem B3869009 : Blo 1358498 3869009 := bstep (se 2 (by rfl) ⟨1450878, by rfl⟩ : syracuseStep 3869009 = 2901757) B2901757
theorem B3058001 : Blo 1358498 3058001 := bstep (se 2 (by rfl) ⟨1146750, by rfl⟩ : syracuseStep 3058001 = 2293501) B2293501
theorem B3058019 : Blo 1358498 3058019 := bstep (se 1 (by rfl) ⟨2293514, by rfl⟩ : syracuseStep 3058019 = 4587029) B4587029
theorem B11020657 : Blo 1358498 11020657 := bstep (se 2 (by rfl) ⟨4132746, by rfl⟩ : syracuseStep 11020657 = 8265493) B8265493
theorem B3443057 : Blo 1358498 3443057 := bstep (se 2 (by rfl) ⟨1291146, by rfl⟩ : syracuseStep 3443057 = 2582293) B2582293
theorem B3443107 : Blo 1358498 3443107 := bstep (se 1 (by rfl) ⟨2582330, by rfl⟩ : syracuseStep 3443107 = 5164661) B5164661
theorem B3672515 : Blo 1358498 3672515 := bstep (se 1 (by rfl) ⟨2754386, by rfl⟩ : syracuseStep 3672515 = 5508773) B5508773
theorem B1935905 : Blo 1358498 1935905 := bstep (se 2 (by rfl) ⟨725964, by rfl⟩ : syracuseStep 1935905 = 1451929) B1451929
theorem B5810723 : Blo 1358498 5810723 := bstep (se 1 (by rfl) ⟨4358042, by rfl⟩ : syracuseStep 5810723 = 8716085) B8716085
theorem B3443249 : Blo 1358498 3443249 := bstep (se 2 (by rfl) ⟨1291218, by rfl⟩ : syracuseStep 3443249 = 2582437) B2582437
theorem B4590161 : Blo 1358498 4590161 := bstep (se 2 (by rfl) ⟨1721310, by rfl⟩ : syracuseStep 4590161 = 3442621) B3442621
theorem B3058289 : Blo 1358498 3058289 := bstep (se 2 (by rfl) ⟨1146858, by rfl⟩ : syracuseStep 3058289 = 2293717) B2293717
theorem B3058307 : Blo 1358498 3058307 := bstep (se 1 (by rfl) ⟨2293730, by rfl⟩ : syracuseStep 3058307 = 4587461) B4587461
theorem B1936019 : Blo 1358498 1936019 := bstep (se 1 (by rfl) ⟨1452014, by rfl⟩ : syracuseStep 1936019 = 2904029) B2904029
theorem B19876549 : Blo 1358498 19876549 := bstep (se 4 (by rfl) ⟨1863426, by rfl⟩ : syracuseStep 19876549 = 3726853) B3726853
theorem B1936099 : Blo 1358498 1936099 := bstep (se 1 (by rfl) ⟨1452074, by rfl⟩ : syracuseStep 1936099 = 2904149) B2904149
theorem B2485073 : Blo 1358498 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B1837939 : Blo 1358498 1837939 := bstep (se 1 (by rfl) ⟨1378454, by rfl⟩ : syracuseStep 1837939 = 2756909) B2756909
theorem B3058577 : Blo 1358498 3058577 := bstep (se 2 (by rfl) ⟨1146966, by rfl⟩ : syracuseStep 3058577 = 2293933) B2293933
theorem B3058595 : Blo 1358498 3058595 := bstep (se 1 (by rfl) ⟨2293946, by rfl⟩ : syracuseStep 3058595 = 4587893) B4587893
theorem B2755505 : Blo 1358498 2755505 := bstep (se 2 (by rfl) ⟨1033314, by rfl⟩ : syracuseStep 2755505 = 2066629) B2066629
theorem B3869795 : Blo 1358498 3869795 := bstep (se 1 (by rfl) ⟨2902346, by rfl⟩ : syracuseStep 3869795 = 5804693) B5804693
theorem B4590701 : Blo 1358498 4590701 := bstep (se 3 (by rfl) ⟨860756, by rfl⟩ : syracuseStep 4590701 = 1721513) B1721513
theorem B5164145 : Blo 1358498 5164145 := bstep (se 2 (by rfl) ⟨1936554, by rfl⟩ : syracuseStep 5164145 = 3873109) B3873109
theorem B1838225 : Blo 1358498 1838225 := bstep (se 2 (by rfl) ⟨689334, by rfl⟩ : syracuseStep 1838225 = 1378669) B1378669
theorem B4590755 : Blo 1358498 4590755 := bstep (se 1 (by rfl) ⟨3443066, by rfl⟩ : syracuseStep 4590755 = 6886133) B6886133
theorem B3058865 : Blo 1358498 3058865 := bstep (se 2 (by rfl) ⟨1147074, by rfl⟩ : syracuseStep 3058865 = 2294149) B2294149
theorem B1633459 : Blo 1358498 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B3058883 : Blo 1358498 3058883 := bstep (se 1 (by rfl) ⟨2294162, by rfl⟩ : syracuseStep 3058883 = 4588325) B4588325
theorem B1936657 : Blo 1358498 1936657 := bstep (se 2 (by rfl) ⟨726246, by rfl⟩ : syracuseStep 1936657 = 1452493) B1452493
theorem B3673379 : Blo 1358498 3673379 := bstep (se 1 (by rfl) ⟨2755034, by rfl⟩ : syracuseStep 3673379 = 5510069) B5510069
theorem B2067779 : Blo 1358498 2067779 := bstep (se 1 (by rfl) ⟨1550834, by rfl⟩ : syracuseStep 2067779 = 3101669) B3101669
theorem B4902221 : Blo 1358498 4902221 := bstep (se 3 (by rfl) ⟨919166, by rfl⟩ : syracuseStep 4902221 = 1838333) B1838333
theorem B6532451 : Blo 1358498 6532451 := bstep (se 1 (by rfl) ⟨4899338, by rfl⟩ : syracuseStep 6532451 = 9798677) B9798677
theorem B3673457 : Blo 1358498 3673457 := bstep (se 2 (by rfl) ⟨1377546, by rfl⟩ : syracuseStep 3673457 = 2755093) B2755093
theorem B3870125 : Blo 1358498 3870125 := bstep (se 3 (by rfl) ⟨725648, by rfl⟩ : syracuseStep 3870125 = 1451297) B1451297
theorem B4591025 : Blo 1358498 4591025 := bstep (se 2 (by rfl) ⟨1721634, by rfl⟩ : syracuseStep 4591025 = 3443269) B3443269
theorem B3059153 : Blo 1358498 3059153 := bstep (se 2 (by rfl) ⟨1147182, by rfl⟩ : syracuseStep 3059153 = 2294365) B2294365
theorem B3059171 : Blo 1358498 3059171 := bstep (se 1 (by rfl) ⟨2294378, by rfl⟩ : syracuseStep 3059171 = 4588757) B4588757
theorem B3870193 : Blo 1358498 3870193 := bstep (se 2 (by rfl) ⟨1451322, by rfl⟩ : syracuseStep 3870193 = 2902645) B2902645
theorem B5508643 : Blo 1358498 5508643 := bstep (se 1 (by rfl) ⟨4131482, by rfl⟩ : syracuseStep 5508643 = 8262965) B8262965
theorem B3681841 : Blo 1358498 3681841 := bstep (se 2 (by rfl) ⟨1380690, by rfl⟩ : syracuseStep 3681841 = 2761381) B2761381
theorem B1633843 : Blo 1358498 1633843 := bstep (se 1 (by rfl) ⟨1225382, by rfl⟩ : syracuseStep 1633843 = 2450765) B2450765
theorem B17428067 : Blo 1358498 17428067 := bstep (se 1 (by rfl) ⟨13071050, by rfl⟩ : syracuseStep 17428067 = 26142101) B26142101
theorem B4353763 : Blo 1358498 4353763 := bstep (se 1 (by rfl) ⟨3265322, by rfl⟩ : syracuseStep 4353763 = 6530645) B6530645
theorem B3059441 : Blo 1358498 3059441 := bstep (se 2 (by rfl) ⟨1147290, by rfl⟩ : syracuseStep 3059441 = 2294581) B2294581
theorem B3870467 : Blo 1358498 3870467 := bstep (se 1 (by rfl) ⟨2902850, by rfl⟩ : syracuseStep 3870467 = 5805701) B5805701
theorem B3059459 : Blo 1358498 3059459 := bstep (se 1 (by rfl) ⟨2294594, by rfl⟩ : syracuseStep 3059459 = 4589189) B4589189
theorem B4591565 : Blo 1358498 4591565 := bstep (se 3 (by rfl) ⟨860918, by rfl⟩ : syracuseStep 4591565 = 1721837) B1721837
theorem B4354033 : Blo 1358498 4354033 := bstep (se 2 (by rfl) ⟨1632762, by rfl⟩ : syracuseStep 4354033 = 3265525) B3265525
theorem B4591619 : Blo 1358498 4591619 := bstep (se 1 (by rfl) ⟨3443714, by rfl⟩ : syracuseStep 4591619 = 6887429) B6887429
theorem B3059729 : Blo 1358498 3059729 := bstep (se 2 (by rfl) ⟨1147398, by rfl⟩ : syracuseStep 3059729 = 2294797) B2294797
theorem B3059747 : Blo 1358498 3059747 := bstep (se 1 (by rfl) ⟨2294810, by rfl⟩ : syracuseStep 3059747 = 4589621) B4589621
theorem B2904131 : Blo 1358498 2904131 := bstep (se 1 (by rfl) ⟨2178098, by rfl⟩ : syracuseStep 2904131 = 4356197) B4356197
theorem B11620421 : Blo 1358498 11620421 := bstep (se 4 (by rfl) ⟨1089414, by rfl⟩ : syracuseStep 11620421 = 2178829) B2178829
theorem B6533219 : Blo 1358498 6533219 := bstep (se 1 (by rfl) ⟨4899914, by rfl⟩ : syracuseStep 6533219 = 9799829) B9799829
theorem B10457201 : Blo 1358498 10457201 := bstep (se 2 (by rfl) ⟨3921450, by rfl⟩ : syracuseStep 10457201 = 7842901) B7842901
theorem B3060017 : Blo 1358498 3060017 := bstep (se 2 (by rfl) ⟨1147506, by rfl⟩ : syracuseStep 3060017 = 2295013) B2295013
theorem B3060035 : Blo 1358498 3060035 := bstep (se 1 (by rfl) ⟨2295026, by rfl⟩ : syracuseStep 3060035 = 4590053) B4590053
theorem B2355569 : Blo 1358498 2355569 := bstep (se 2 (by rfl) ⟨883338, by rfl⟩ : syracuseStep 2355569 = 1766677) B1766677
theorem B8704397 : Blo 1358498 8704397 := bstep (se 3 (by rfl) ⟨1632074, by rfl⟩ : syracuseStep 8704397 = 3264149) B3264149
theorem B6885809 : Blo 1358498 6885809 := bstep (se 2 (by rfl) ⟨2582178, by rfl⟩ : syracuseStep 6885809 = 5164357) B5164357
theorem B7745989 : Blo 1358498 7745989 := bstep (se 4 (by rfl) ⟨726186, by rfl⟩ : syracuseStep 7745989 = 1452373) B1452373
theorem B3264995 : Blo 1358498 3264995 := bstep (se 1 (by rfl) ⟨2448746, by rfl⟩ : syracuseStep 3264995 = 4897493) B4897493
theorem B6877709 : Blo 1358498 6877709 := bstep (se 3 (by rfl) ⟨1289570, by rfl⟩ : syracuseStep 6877709 = 2579141) B2579141
theorem B1528339 : Blo 1358498 1528339 := bstep (se 1 (by rfl) ⟨1146254, by rfl⟩ : syracuseStep 1528339 = 2292509) B2292509
theorem B4649507 : Blo 1358498 4649507 := bstep (se 1 (by rfl) ⟨3487130, by rfl⟩ : syracuseStep 4649507 = 6974261) B6974261
theorem B5165603 : Blo 1358498 5165603 := bstep (se 1 (by rfl) ⟨3874202, by rfl⟩ : syracuseStep 5165603 = 7748405) B7748405
theorem B3265073 : Blo 1358498 3265073 := bstep (se 2 (by rfl) ⟨1224402, by rfl⟩ : syracuseStep 3265073 = 2448805) B2448805
theorem B2757169 : Blo 1358498 2757169 := bstep (se 2 (by rfl) ⟨1033938, by rfl⟩ : syracuseStep 2757169 = 2067877) B2067877
theorem B3871309 : Blo 1358498 3871309 := bstep (se 3 (by rfl) ⟨725870, by rfl⟩ : syracuseStep 3871309 = 1451741) B1451741
theorem B3060305 : Blo 1358498 3060305 := bstep (se 2 (by rfl) ⟨1147614, by rfl⟩ : syracuseStep 3060305 = 2295229) B2295229
theorem B3060323 : Blo 1358498 3060323 := bstep (se 1 (by rfl) ⟨2295242, by rfl⟩ : syracuseStep 3060323 = 4590485) B4590485
theorem B1528483 : Blo 1358498 1528483 := bstep (se 1 (by rfl) ⟨1146362, by rfl⟩ : syracuseStep 1528483 = 2292725) B2292725
theorem B3871469 : Blo 1358498 3871469 := bstep (se 3 (by rfl) ⟨725900, by rfl⟩ : syracuseStep 3871469 = 1451801) B1451801
theorem B1528627 : Blo 1358498 1528627 := bstep (se 1 (by rfl) ⟨1146470, by rfl⟩ : syracuseStep 1528627 = 2292941) B2292941
theorem B2093921 : Blo 1358498 2093921 := bstep (se 2 (by rfl) ⟨785220, by rfl⟩ : syracuseStep 2093921 = 1570441) B1570441
theorem B3060593 : Blo 1358498 3060593 := bstep (se 2 (by rfl) ⟨1147722, by rfl⟩ : syracuseStep 3060593 = 2295445) B2295445
theorem B3060611 : Blo 1358498 3060611 := bstep (se 1 (by rfl) ⟨2295458, by rfl⟩ : syracuseStep 3060611 = 4590917) B4590917
theorem B3871651 : Blo 1358498 3871651 := bstep (se 1 (by rfl) ⟨2903738, by rfl⟩ : syracuseStep 3871651 = 5807477) B5807477
theorem B1528771 : Blo 1358498 1528771 := bstep (se 1 (by rfl) ⟨1146578, by rfl⟩ : syracuseStep 1528771 = 2293157) B2293157
theorem B1528915 : Blo 1358498 1528915 := bstep (se 1 (by rfl) ⟨1146686, by rfl⟩ : syracuseStep 1528915 = 2293373) B2293373
theorem B3060881 : Blo 1358498 3060881 := bstep (se 2 (by rfl) ⟨1147830, by rfl⟩ : syracuseStep 3060881 = 2295661) B2295661
theorem B3060899 : Blo 1358498 3060899 := bstep (se 1 (by rfl) ⟨2295674, by rfl⟩ : syracuseStep 3060899 = 4591349) B4591349
theorem B5584099 : Blo 1358498 5584099 := bstep (se 1 (by rfl) ⟨4188074, by rfl⟩ : syracuseStep 5584099 = 8376149) B8376149
theorem B1529059 : Blo 1358498 1529059 := bstep (se 1 (by rfl) ⟨1146794, by rfl⟩ : syracuseStep 1529059 = 2293589) B2293589
theorem B2905379 : Blo 1358498 2905379 := bstep (se 1 (by rfl) ⟨2179034, by rfl⟩ : syracuseStep 2905379 = 4358069) B4358069
theorem B3265841 : Blo 1358498 3265841 := bstep (se 2 (by rfl) ⟨1224690, by rfl⟩ : syracuseStep 3265841 = 2449381) B2449381
theorem B6534449 : Blo 1358498 6534449 := bstep (se 2 (by rfl) ⟨2450418, by rfl⟩ : syracuseStep 6534449 = 4900837) B4900837
theorem B17659205 : Blo 1358498 17659205 := bstep (se 4 (by rfl) ⟨1655550, by rfl⟩ : syracuseStep 17659205 = 3311101) B3311101
theorem B1529203 : Blo 1358498 1529203 := bstep (se 1 (by rfl) ⟨1146902, by rfl⟩ : syracuseStep 1529203 = 2293805) B2293805
theorem B1529347 : Blo 1358498 1529347 := bstep (se 1 (by rfl) ⟨1147010, by rfl⟩ : syracuseStep 1529347 = 2294021) B2294021
theorem B4584977 : Blo 1358498 4584977 := bstep (se 2 (by rfl) ⟨1719366, by rfl⟩ : syracuseStep 4584977 = 3438733) B3438733
theorem B2176561 : Blo 1358498 2176561 := bstep (se 2 (by rfl) ⟨816210, by rfl⟩ : syracuseStep 2176561 = 1632421) B1632421
theorem B4355633 : Blo 1358498 4355633 := bstep (se 2 (by rfl) ⟨1633362, by rfl⟩ : syracuseStep 4355633 = 3266725) B3266725
theorem B13071941 : Blo 1358498 13071941 := bstep (se 4 (by rfl) ⟨1225494, by rfl⟩ : syracuseStep 13071941 = 2450989) B2450989
theorem B4896397 : Blo 1358498 4896397 := bstep (se 3 (by rfl) ⟨918074, by rfl⟩ : syracuseStep 4896397 = 1836149) B1836149
theorem B3675793 : Blo 1358498 3675793 := bstep (se 2 (by rfl) ⟨1378422, by rfl⟩ : syracuseStep 3675793 = 2756845) B2756845
theorem B1529491 : Blo 1358498 1529491 := bstep (se 1 (by rfl) ⟨1147118, by rfl⟩ : syracuseStep 1529491 = 2294237) B2294237
theorem B11024099 : Blo 1358498 11024099 := bstep (se 1 (by rfl) ⟨8268074, by rfl⟩ : syracuseStep 11024099 = 16536149) B16536149
theorem B1529635 : Blo 1358498 1529635 := bstep (se 1 (by rfl) ⟨1147226, by rfl⟩ : syracuseStep 1529635 = 2294453) B2294453
theorem B6534989 : Blo 1358498 6534989 := bstep (se 3 (by rfl) ⟨1225310, by rfl⟩ : syracuseStep 6534989 = 2450621) B2450621
theorem B9074531 : Blo 1358498 9074531 := bstep (se 1 (by rfl) ⟨6805898, by rfl⟩ : syracuseStep 9074531 = 13611797) B13611797
theorem B6887267 : Blo 1358498 6887267 := bstep (se 1 (by rfl) ⟨5165450, by rfl⟩ : syracuseStep 6887267 = 10330901) B10330901
theorem B20936561 : Blo 1358498 20936561 := bstep (se 2 (by rfl) ⟨7851210, by rfl⟩ : syracuseStep 20936561 = 15702421) B15702421
theorem B4355981 : Blo 1358498 4355981 := bstep (se 3 (by rfl) ⟨816746, by rfl⟩ : syracuseStep 4355981 = 1633493) B1633493
theorem B1529779 : Blo 1358498 1529779 := bstep (se 1 (by rfl) ⟨1147334, by rfl⟩ : syracuseStep 1529779 = 2294669) B2294669
theorem B2037761 : Blo 1358498 2037761 := bstep (se 2 (by rfl) ⟨764160, by rfl⟩ : syracuseStep 2037761 = 1528321) B1528321
theorem B2037779 : Blo 1358498 2037779 := bstep (se 1 (by rfl) ⟨1528334, by rfl⟩ : syracuseStep 2037779 = 3056669) B3056669
theorem B4585517 : Blo 1358498 4585517 := bstep (se 3 (by rfl) ⟨859784, by rfl⟩ : syracuseStep 4585517 = 1719569) B1719569
theorem B2037809 : Blo 1358498 2037809 := bstep (se 2 (by rfl) ⟨764178, by rfl⟩ : syracuseStep 2037809 = 1528357) B1528357
theorem B2037827 : Blo 1358498 2037827 := bstep (se 1 (by rfl) ⟨1528370, by rfl⟩ : syracuseStep 2037827 = 3056741) B3056741
theorem B1529923 : Blo 1358498 1529923 := bstep (se 1 (by rfl) ⟨1147442, by rfl⟩ : syracuseStep 1529923 = 2294885) B2294885
theorem B2037857 : Blo 1358498 2037857 := bstep (se 2 (by rfl) ⟨764196, by rfl⟩ : syracuseStep 2037857 = 1528393) B1528393
theorem B4585571 : Blo 1358498 4585571 := bstep (se 1 (by rfl) ⟨3439178, by rfl⟩ : syracuseStep 4585571 = 6878357) B6878357
theorem B5159011 : Blo 1358498 5159011 := bstep (se 1 (by rfl) ⟨3869258, by rfl⟩ : syracuseStep 5159011 = 7738517) B7738517
theorem B2037875 : Blo 1358498 2037875 := bstep (se 1 (by rfl) ⟨1528406, by rfl⟩ : syracuseStep 2037875 = 3056813) B3056813
theorem B2037905 : Blo 1358498 2037905 := bstep (se 2 (by rfl) ⟨764214, by rfl⟩ : syracuseStep 2037905 = 1528429) B1528429
theorem B2037923 : Blo 1358498 2037923 := bstep (se 1 (by rfl) ⟨1528442, by rfl⟩ : syracuseStep 2037923 = 3056885) B3056885
theorem B2037953 : Blo 1358498 2037953 := bstep (se 2 (by rfl) ⟨764232, by rfl⟩ : syracuseStep 2037953 = 1528465) B1528465
theorem B2037971 : Blo 1358498 2037971 := bstep (se 1 (by rfl) ⟨1528478, by rfl⟩ : syracuseStep 2037971 = 3056957) B3056957
theorem B1530067 : Blo 1358498 1530067 := bstep (se 1 (by rfl) ⟨1147550, by rfl⟩ : syracuseStep 1530067 = 2295101) B2295101
theorem B2038001 : Blo 1358498 2038001 := bstep (se 2 (by rfl) ⟨764250, by rfl⟩ : syracuseStep 2038001 = 1528501) B1528501
theorem B2038019 : Blo 1358498 2038019 := bstep (se 1 (by rfl) ⟨1528514, by rfl⟩ : syracuseStep 2038019 = 3057029) B3057029
theorem B5806349 : Blo 1358498 5806349 := bstep (se 3 (by rfl) ⟨1088690, by rfl⟩ : syracuseStep 5806349 = 2177381) B2177381
theorem B3873041 : Blo 1358498 3873041 := bstep (se 2 (by rfl) ⟨1452390, by rfl⟩ : syracuseStep 3873041 = 2904781) B2904781
theorem B2038049 : Blo 1358498 2038049 := bstep (se 2 (by rfl) ⟨764268, by rfl⟩ : syracuseStep 2038049 = 1528537) B1528537
theorem B2038067 : Blo 1358498 2038067 := bstep (se 1 (by rfl) ⟨1528550, by rfl⟩ : syracuseStep 2038067 = 3057101) B3057101
theorem B2038097 : Blo 1358498 2038097 := bstep (se 2 (by rfl) ⟨764286, by rfl⟩ : syracuseStep 2038097 = 1528573) B1528573
theorem B2038115 : Blo 1358498 2038115 := bstep (se 1 (by rfl) ⟨1528586, by rfl⟩ : syracuseStep 2038115 = 3057173) B3057173
theorem B1530211 : Blo 1358498 1530211 := bstep (se 1 (by rfl) ⟨1147658, by rfl⟩ : syracuseStep 1530211 = 2295317) B2295317
theorem B4585841 : Blo 1358498 4585841 := bstep (se 2 (by rfl) ⟨1719690, by rfl⟩ : syracuseStep 4585841 = 3439381) B3439381
theorem B2038145 : Blo 1358498 2038145 := bstep (se 2 (by rfl) ⟨764304, by rfl⟩ : syracuseStep 2038145 = 1528609) B1528609
theorem B7747973 : Blo 1358498 7747973 := bstep (se 4 (by rfl) ⟨726372, by rfl⟩ : syracuseStep 7747973 = 1452745) B1452745
theorem B2038163 : Blo 1358498 2038163 := bstep (se 1 (by rfl) ⟨1528622, by rfl⟩ : syracuseStep 2038163 = 3057245) B3057245
theorem B2038193 : Blo 1358498 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B2038211 : Blo 1358498 2038211 := bstep (se 1 (by rfl) ⟨1528658, by rfl⟩ : syracuseStep 2038211 = 3057317) B3057317
theorem B7346629 : Blo 1358498 7346629 := bstep (se 4 (by rfl) ⟨688746, by rfl⟩ : syracuseStep 7346629 = 1377493) B1377493
theorem B8829389 : Blo 1358498 8829389 := bstep (se 3 (by rfl) ⟨1655510, by rfl⟩ : syracuseStep 8829389 = 3311021) B3311021
theorem B3439057 : Blo 1358498 3439057 := bstep (se 2 (by rfl) ⟨1289646, by rfl⟩ : syracuseStep 3439057 = 2579293) B2579293
theorem B2038241 : Blo 1358498 2038241 := bstep (se 2 (by rfl) ⟨764340, by rfl⟩ : syracuseStep 2038241 = 1528681) B1528681
theorem B2038259 : Blo 1358498 2038259 := bstep (se 1 (by rfl) ⟨1528694, by rfl⟩ : syracuseStep 2038259 = 3057389) B3057389
theorem B1530355 : Blo 1358498 1530355 := bstep (se 1 (by rfl) ⟨1147766, by rfl⟩ : syracuseStep 1530355 = 2295533) B2295533
theorem B2038289 : Blo 1358498 2038289 := bstep (se 2 (by rfl) ⟨764358, by rfl⟩ : syracuseStep 2038289 = 1528717) B1528717
theorem B2038307 : Blo 1358498 2038307 := bstep (se 1 (by rfl) ⟨1528730, by rfl⟩ : syracuseStep 2038307 = 3057461) B3057461
theorem B2095651 : Blo 1358498 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B2038337 : Blo 1358498 2038337 := bstep (se 2 (by rfl) ⟨764376, by rfl⟩ : syracuseStep 2038337 = 1528753) B1528753
theorem B8706629 : Blo 1358498 8706629 := bstep (se 4 (by rfl) ⟨816246, by rfl⟩ : syracuseStep 8706629 = 1632493) B1632493
theorem B2038355 : Blo 1358498 2038355 := bstep (se 1 (by rfl) ⟨1528766, by rfl⟩ : syracuseStep 2038355 = 3057533) B3057533
theorem B5806691 : Blo 1358498 5806691 := bstep (se 1 (by rfl) ⟨4355018, by rfl⟩ : syracuseStep 5806691 = 8710037) B8710037
theorem B2038385 : Blo 1358498 2038385 := bstep (se 2 (by rfl) ⟨764394, by rfl⟩ : syracuseStep 2038385 = 1528789) B1528789
theorem B2038403 : Blo 1358498 2038403 := bstep (se 1 (by rfl) ⟨1528802, by rfl⟩ : syracuseStep 2038403 = 3057605) B3057605
theorem B1530499 : Blo 1358498 1530499 := bstep (se 1 (by rfl) ⟨1147874, by rfl⟩ : syracuseStep 1530499 = 2295749) B2295749
theorem B2038433 : Blo 1358498 2038433 := bstep (se 2 (by rfl) ⟨764412, by rfl⟩ : syracuseStep 2038433 = 1528825) B1528825
theorem B1358499 : Blo 1358498 1358499 := bstep (se 1 (by rfl) ⟨1018874, by rfl⟩ : syracuseStep 1358499 = 2037749) B2037749
theorem B1358515 : Blo 1358498 1358515 := bstep (se 1 (by rfl) ⟨1018886, by rfl⟩ : syracuseStep 1358515 = 2037773) B2037773
theorem B2038451 : Blo 1358498 2038451 := bstep (se 1 (by rfl) ⟨1528838, by rfl⟩ : syracuseStep 2038451 = 3057677) B3057677
theorem B1358531 : Blo 1358498 1358531 := bstep (se 1 (by rfl) ⟨1018898, by rfl⟩ : syracuseStep 1358531 = 2037797) B2037797
theorem B38214341 : Blo 1358498 38214341 := bstep (se 4 (by rfl) ⟨3582594, by rfl⟩ : syracuseStep 38214341 = 7165189) B7165189
theorem B2038481 : Blo 1358498 2038481 := bstep (se 2 (by rfl) ⟨764430, by rfl⟩ : syracuseStep 2038481 = 1528861) B1528861
theorem B1358547 : Blo 1358498 1358547 := bstep (se 1 (by rfl) ⟨1018910, by rfl⟩ : syracuseStep 1358547 = 2037821) B2037821
theorem B2325217 : Blo 1358498 2325217 := bstep (se 2 (by rfl) ⟨871956, by rfl⟩ : syracuseStep 2325217 = 1743913) B1743913
theorem B1358563 : Blo 1358498 1358563 := bstep (se 1 (by rfl) ⟨1018922, by rfl⟩ : syracuseStep 1358563 = 2037845) B2037845
theorem B3439331 : Blo 1358498 3439331 := bstep (se 1 (by rfl) ⟨2579498, by rfl⟩ : syracuseStep 3439331 = 5158997) B5158997
theorem B2038499 : Blo 1358498 2038499 := bstep (se 1 (by rfl) ⟨1528874, by rfl⟩ : syracuseStep 2038499 = 3057749) B3057749
theorem B3488483 : Blo 1358498 3488483 := bstep (se 1 (by rfl) ⟨2616362, by rfl⟩ : syracuseStep 3488483 = 5232725) B5232725
theorem B1358579 : Blo 1358498 1358579 := bstep (se 1 (by rfl) ⟨1018934, by rfl⟩ : syracuseStep 1358579 = 2037869) B2037869
theorem B2038529 : Blo 1358498 2038529 := bstep (se 2 (by rfl) ⟨764448, by rfl⟩ : syracuseStep 2038529 = 1528897) B1528897
theorem B1358595 : Blo 1358498 1358595 := bstep (se 1 (by rfl) ⟨1018946, by rfl⟩ : syracuseStep 1358595 = 2037893) B2037893
theorem B1358611 : Blo 1358498 1358611 := bstep (se 1 (by rfl) ⟨1018958, by rfl⟩ : syracuseStep 1358611 = 2037917) B2037917
theorem B2038547 : Blo 1358498 2038547 := bstep (se 1 (by rfl) ⟨1528910, by rfl⟩ : syracuseStep 2038547 = 3057821) B3057821
theorem B1358627 : Blo 1358498 1358627 := bstep (se 1 (by rfl) ⟨1018970, by rfl⟩ : syracuseStep 1358627 = 2037941) B2037941
theorem B2292529 : Blo 1358498 2292529 := bstep (se 2 (by rfl) ⟨859698, by rfl⟩ : syracuseStep 2292529 = 1719397) B1719397
theorem B2038577 : Blo 1358498 2038577 := bstep (se 2 (by rfl) ⟨764466, by rfl⟩ : syracuseStep 2038577 = 1528933) B1528933
theorem B1358643 : Blo 1358498 1358643 := bstep (se 1 (by rfl) ⟨1018982, by rfl⟩ : syracuseStep 1358643 = 2037965) B2037965
theorem B1358659 : Blo 1358498 1358659 := bstep (se 1 (by rfl) ⟨1018994, by rfl⟩ : syracuseStep 1358659 = 2037989) B2037989
theorem B2038595 : Blo 1358498 2038595 := bstep (se 1 (by rfl) ⟨1528946, by rfl⟩ : syracuseStep 2038595 = 3057893) B3057893
theorem B2292563 : Blo 1358498 2292563 := bstep (se 1 (by rfl) ⟨1719422, by rfl⟩ : syracuseStep 2292563 = 3438845) B3438845
theorem B1358675 : Blo 1358498 1358675 := bstep (se 1 (by rfl) ⟨1019006, by rfl⟩ : syracuseStep 1358675 = 2038013) B2038013
theorem B2038625 : Blo 1358498 2038625 := bstep (se 2 (by rfl) ⟨764484, by rfl⟩ : syracuseStep 2038625 = 1528969) B1528969
theorem B2448227 : Blo 1358498 2448227 := bstep (se 1 (by rfl) ⟨1836170, by rfl⟩ : syracuseStep 2448227 = 3672341) B3672341
theorem B1358691 : Blo 1358498 1358691 := bstep (se 1 (by rfl) ⟨1019018, by rfl⟩ : syracuseStep 1358691 = 2038037) B2038037
theorem B1358707 : Blo 1358498 1358707 := bstep (se 1 (by rfl) ⟨1019030, by rfl⟩ : syracuseStep 1358707 = 2038061) B2038061
theorem B2038643 : Blo 1358498 2038643 := bstep (se 1 (by rfl) ⟨1528982, by rfl⟩ : syracuseStep 2038643 = 3057965) B3057965
theorem B1358723 : Blo 1358498 1358723 := bstep (se 1 (by rfl) ⟨1019042, by rfl⟩ : syracuseStep 1358723 = 2038085) B2038085
theorem B4586381 : Blo 1358498 4586381 := bstep (se 3 (by rfl) ⟨859946, by rfl⟩ : syracuseStep 4586381 = 1719893) B1719893
theorem B2038673 : Blo 1358498 2038673 := bstep (se 2 (by rfl) ⟨764502, by rfl⟩ : syracuseStep 2038673 = 1529005) B1529005
theorem B1358739 : Blo 1358498 1358739 := bstep (se 1 (by rfl) ⟨1019054, by rfl⟩ : syracuseStep 1358739 = 2038109) B2038109
theorem B1358755 : Blo 1358498 1358755 := bstep (se 1 (by rfl) ⟨1019066, by rfl⟩ : syracuseStep 1358755 = 2038133) B2038133
theorem B3439523 : Blo 1358498 3439523 := bstep (se 1 (by rfl) ⟨2579642, by rfl⟩ : syracuseStep 3439523 = 5159285) B5159285
theorem B2038691 : Blo 1358498 2038691 := bstep (se 1 (by rfl) ⟨1529018, by rfl⟩ : syracuseStep 2038691 = 3058037) B3058037
theorem B2579377 : Blo 1358498 2579377 := bstep (se 2 (by rfl) ⟨967266, by rfl⟩ : syracuseStep 2579377 = 1934533) B1934533
theorem B1358771 : Blo 1358498 1358771 := bstep (se 1 (by rfl) ⟨1019078, by rfl⟩ : syracuseStep 1358771 = 2038157) B2038157
theorem B2038721 : Blo 1358498 2038721 := bstep (se 2 (by rfl) ⟨764520, by rfl⟩ : syracuseStep 2038721 = 1529041) B1529041
theorem B1358787 : Blo 1358498 1358787 := bstep (se 1 (by rfl) ⟨1019090, by rfl⟩ : syracuseStep 1358787 = 2038181) B2038181
theorem B4586435 : Blo 1358498 4586435 := bstep (se 1 (by rfl) ⟨3439826, by rfl⟩ : syracuseStep 4586435 = 6879653) B6879653
theorem B2292691 : Blo 1358498 2292691 := bstep (se 1 (by rfl) ⟨1719518, by rfl⟩ : syracuseStep 2292691 = 3439037) B3439037
theorem B1358803 : Blo 1358498 1358803 := bstep (se 1 (by rfl) ⟨1019102, by rfl⟩ : syracuseStep 1358803 = 2038205) B2038205
theorem B2038739 : Blo 1358498 2038739 := bstep (se 1 (by rfl) ⟨1529054, by rfl⟩ : syracuseStep 2038739 = 3058109) B3058109
theorem B1358819 : Blo 1358498 1358819 := bstep (se 1 (by rfl) ⟨1019114, by rfl⟩ : syracuseStep 1358819 = 2038229) B2038229
theorem B2038769 : Blo 1358498 2038769 := bstep (se 2 (by rfl) ⟨764538, by rfl⟩ : syracuseStep 2038769 = 1529077) B1529077
theorem B1358835 : Blo 1358498 1358835 := bstep (se 1 (by rfl) ⟨1019126, by rfl⟩ : syracuseStep 1358835 = 2038253) B2038253
theorem B1358851 : Blo 1358498 1358851 := bstep (se 1 (by rfl) ⟨1019138, by rfl⟩ : syracuseStep 1358851 = 2038277) B2038277
theorem B2038787 : Blo 1358498 2038787 := bstep (se 1 (by rfl) ⟨1529090, by rfl⟩ : syracuseStep 2038787 = 3058181) B3058181
theorem B1358867 : Blo 1358498 1358867 := bstep (se 1 (by rfl) ⟨1019150, by rfl⟩ : syracuseStep 1358867 = 2038301) B2038301
theorem B2038817 : Blo 1358498 2038817 := bstep (se 2 (by rfl) ⟨764556, by rfl⟩ : syracuseStep 2038817 = 1529113) B1529113
theorem B1358883 : Blo 1358498 1358883 := bstep (se 1 (by rfl) ⟨1019162, by rfl⟩ : syracuseStep 1358883 = 2038325) B2038325
theorem B1358899 : Blo 1358498 1358899 := bstep (se 1 (by rfl) ⟨1019174, by rfl⟩ : syracuseStep 1358899 = 2038349) B2038349
theorem B2038835 : Blo 1358498 2038835 := bstep (se 1 (by rfl) ⟨1529126, by rfl⟩ : syracuseStep 2038835 = 3058253) B3058253
theorem B5807153 : Blo 1358498 5807153 := bstep (se 2 (by rfl) ⟨2177682, by rfl⟩ : syracuseStep 5807153 = 4355365) B4355365
theorem B1358915 : Blo 1358498 1358915 := bstep (se 1 (by rfl) ⟨1019186, by rfl⟩ : syracuseStep 1358915 = 2038373) B2038373
theorem B3726413 : Blo 1358498 3726413 := bstep (se 3 (by rfl) ⟨698702, by rfl⟩ : syracuseStep 3726413 = 1397405) B1397405
theorem B2038865 : Blo 1358498 2038865 := bstep (se 2 (by rfl) ⟨764574, by rfl⟩ : syracuseStep 2038865 = 1529149) B1529149
theorem B1358931 : Blo 1358498 1358931 := bstep (se 1 (by rfl) ⟨1019198, by rfl⟩ : syracuseStep 1358931 = 2038397) B2038397
theorem B1571923 : Blo 1358498 1571923 := bstep (se 1 (by rfl) ⟨1178942, by rfl⟩ : syracuseStep 1571923 = 2357885) B2357885
theorem B2292833 : Blo 1358498 2292833 := bstep (se 2 (by rfl) ⟨859812, by rfl⟩ : syracuseStep 2292833 = 1719625) B1719625
theorem B1358947 : Blo 1358498 1358947 := bstep (se 1 (by rfl) ⟨1019210, by rfl⟩ : syracuseStep 1358947 = 2038421) B2038421
theorem B2038883 : Blo 1358498 2038883 := bstep (se 1 (by rfl) ⟨1529162, by rfl⟩ : syracuseStep 2038883 = 3058325) B3058325
theorem B1358963 : Blo 1358498 1358963 := bstep (se 1 (by rfl) ⟨1019222, by rfl⟩ : syracuseStep 1358963 = 2038445) B2038445
theorem B2038913 : Blo 1358498 2038913 := bstep (se 2 (by rfl) ⟨764592, by rfl⟩ : syracuseStep 2038913 = 1529185) B1529185
theorem B1358979 : Blo 1358498 1358979 := bstep (se 1 (by rfl) ⟨1019234, by rfl⟩ : syracuseStep 1358979 = 2038469) B2038469
theorem B1358995 : Blo 1358498 1358995 := bstep (se 1 (by rfl) ⟨1019246, by rfl⟩ : syracuseStep 1358995 = 2038493) B2038493
theorem B2038931 : Blo 1358498 2038931 := bstep (se 1 (by rfl) ⟨1529198, by rfl⟩ : syracuseStep 2038931 = 3058397) B3058397
theorem B1359011 : Blo 1358498 1359011 := bstep (se 1 (by rfl) ⟨1019258, by rfl⟩ : syracuseStep 1359011 = 2038517) B2038517
theorem B2038961 : Blo 1358498 2038961 := bstep (se 2 (by rfl) ⟨764610, by rfl⟩ : syracuseStep 2038961 = 1529221) B1529221
theorem B1359027 : Blo 1358498 1359027 := bstep (se 1 (by rfl) ⟨1019270, by rfl⟩ : syracuseStep 1359027 = 2038541) B2038541
theorem B2178227 : Blo 1358498 2178227 := bstep (se 1 (by rfl) ⟨1633670, by rfl⟩ : syracuseStep 2178227 = 3267341) B3267341
theorem B1359043 : Blo 1358498 1359043 := bstep (se 1 (by rfl) ⟨1019282, by rfl⟩ : syracuseStep 1359043 = 2038565) B2038565
theorem B2038979 : Blo 1358498 2038979 := bstep (se 1 (by rfl) ⟨1529234, by rfl⟩ : syracuseStep 2038979 = 3058469) B3058469
theorem B4136141 : Blo 1358498 4136141 := bstep (se 3 (by rfl) ⟨775526, by rfl⟩ : syracuseStep 4136141 = 1551053) B1551053
theorem B4586705 : Blo 1358498 4586705 := bstep (se 2 (by rfl) ⟨1720014, by rfl⟩ : syracuseStep 4586705 = 3440029) B3440029
theorem B1359059 : Blo 1358498 1359059 := bstep (se 1 (by rfl) ⟨1019294, by rfl⟩ : syracuseStep 1359059 = 2038589) B2038589
theorem B3873997 : Blo 1358498 3873997 := bstep (se 3 (by rfl) ⟨726374, by rfl⟩ : syracuseStep 3873997 = 1452749) B1452749
theorem B2292961 : Blo 1358498 2292961 := bstep (se 2 (by rfl) ⟨859860, by rfl⟩ : syracuseStep 2292961 = 1719721) B1719721
theorem B1359075 : Blo 1358498 1359075 := bstep (se 1 (by rfl) ⟨1019306, by rfl⟩ : syracuseStep 1359075 = 2038613) B2038613
theorem B2039009 : Blo 1358498 2039009 := bstep (se 2 (by rfl) ⟨764628, by rfl⟩ : syracuseStep 2039009 = 1529257) B1529257
theorem B1359091 : Blo 1358498 1359091 := bstep (se 1 (by rfl) ⟨1019318, by rfl⟩ : syracuseStep 1359091 = 2038637) B2038637
theorem B2039027 : Blo 1358498 2039027 := bstep (se 1 (by rfl) ⟨1529270, by rfl⟩ : syracuseStep 2039027 = 3058541) B3058541
theorem B2292995 : Blo 1358498 2292995 := bstep (se 1 (by rfl) ⟨1719746, by rfl⟩ : syracuseStep 2292995 = 3439493) B3439493
theorem B1359107 : Blo 1358498 1359107 := bstep (se 1 (by rfl) ⟨1019330, by rfl⟩ : syracuseStep 1359107 = 2038661) B2038661
theorem B2039057 : Blo 1358498 2039057 := bstep (se 2 (by rfl) ⟨764646, by rfl⟩ : syracuseStep 2039057 = 1529293) B1529293
theorem B1359123 : Blo 1358498 1359123 := bstep (se 1 (by rfl) ⟨1019342, by rfl⟩ : syracuseStep 1359123 = 2038685) B2038685
theorem B1359139 : Blo 1358498 1359139 := bstep (se 1 (by rfl) ⟨1019354, by rfl⟩ : syracuseStep 1359139 = 2038709) B2038709
theorem B2039075 : Blo 1358498 2039075 := bstep (se 1 (by rfl) ⟨1529306, by rfl⟩ : syracuseStep 2039075 = 3058613) B3058613
theorem B2178419 : Blo 1358498 2178419 := bstep (se 1 (by rfl) ⟨1633814, by rfl⟩ : syracuseStep 2178419 = 3267629) B3267629
theorem B1359155 : Blo 1358498 1359155 := bstep (se 1 (by rfl) ⟨1019366, by rfl⟩ : syracuseStep 1359155 = 2038733) B2038733
theorem B2178355 : Blo 1358498 2178355 := bstep (se 1 (by rfl) ⟨1633766, by rfl⟩ : syracuseStep 2178355 = 3267533) B3267533
theorem B2039105 : Blo 1358498 2039105 := bstep (se 2 (by rfl) ⟨764664, by rfl⟩ : syracuseStep 2039105 = 1529329) B1529329
theorem B2579779 : Blo 1358498 2579779 := bstep (se 1 (by rfl) ⟨1934834, by rfl⟩ : syracuseStep 2579779 = 3869669) B3869669
theorem B1359171 : Blo 1358498 1359171 := bstep (se 1 (by rfl) ⟨1019378, by rfl⟩ : syracuseStep 1359171 = 2038757) B2038757
theorem B1359187 : Blo 1358498 1359187 := bstep (se 1 (by rfl) ⟨1019390, by rfl⟩ : syracuseStep 1359187 = 2038781) B2038781
theorem B2039123 : Blo 1358498 2039123 := bstep (se 1 (by rfl) ⟨1529342, by rfl⟩ : syracuseStep 2039123 = 3058685) B3058685
theorem B1359203 : Blo 1358498 1359203 := bstep (se 1 (by rfl) ⟨1019402, by rfl⟩ : syracuseStep 1359203 = 2038805) B2038805
theorem B10329443 : Blo 1358498 10329443 := bstep (se 1 (by rfl) ⟨7747082, by rfl⟩ : syracuseStep 10329443 = 15494165) B15494165
theorem B2579825 : Blo 1358498 2579825 := bstep (se 2 (by rfl) ⟨967434, by rfl⟩ : syracuseStep 2579825 = 1934869) B1934869
theorem B6880625 : Blo 1358498 6880625 := bstep (se 2 (by rfl) ⟨2580234, by rfl⟩ : syracuseStep 6880625 = 5160469) B5160469
theorem B1359219 : Blo 1358498 1359219 := bstep (se 1 (by rfl) ⟨1019414, by rfl⟩ : syracuseStep 1359219 = 2038829) B2038829
theorem B2039153 : Blo 1358498 2039153 := bstep (se 2 (by rfl) ⟨764682, by rfl⟩ : syracuseStep 2039153 = 1529365) B1529365
theorem B2293123 : Blo 1358498 2293123 := bstep (se 1 (by rfl) ⟨1719842, by rfl⟩ : syracuseStep 2293123 = 3439685) B3439685
theorem B1359235 : Blo 1358498 1359235 := bstep (se 1 (by rfl) ⟨1019426, by rfl⟩ : syracuseStep 1359235 = 2038853) B2038853
theorem B2039171 : Blo 1358498 2039171 := bstep (se 1 (by rfl) ⟨1529378, by rfl⟩ : syracuseStep 2039171 = 3058757) B3058757
theorem B1359251 : Blo 1358498 1359251 := bstep (se 1 (by rfl) ⟨1019438, by rfl⟩ : syracuseStep 1359251 = 2038877) B2038877
theorem B2039201 : Blo 1358498 2039201 := bstep (se 2 (by rfl) ⟨764700, by rfl⟩ : syracuseStep 2039201 = 1529401) B1529401
theorem B1359267 : Blo 1358498 1359267 := bstep (se 1 (by rfl) ⟨1019450, by rfl⟩ : syracuseStep 1359267 = 2038901) B2038901
theorem B3874225 : Blo 1358498 3874225 := bstep (se 2 (by rfl) ⟨1452834, by rfl⟩ : syracuseStep 3874225 = 2905669) B2905669
theorem B1719731 : Blo 1358498 1719731 := bstep (se 1 (by rfl) ⟨1289798, by rfl⟩ : syracuseStep 1719731 = 2579597) B2579597
theorem B1359283 : Blo 1358498 1359283 := bstep (se 1 (by rfl) ⟨1019462, by rfl⟩ : syracuseStep 1359283 = 2038925) B2038925
theorem B2039219 : Blo 1358498 2039219 := bstep (se 1 (by rfl) ⟨1529414, by rfl⟩ : syracuseStep 2039219 = 3058829) B3058829
theorem B1359299 : Blo 1358498 1359299 := bstep (se 1 (by rfl) ⟨1019474, by rfl⟩ : syracuseStep 1359299 = 2038949) B2038949
theorem B8830405 : Blo 1358498 8830405 := bstep (se 4 (by rfl) ⟨827850, by rfl⟩ : syracuseStep 8830405 = 1655701) B1655701
theorem B2039249 : Blo 1358498 2039249 := bstep (se 2 (by rfl) ⟨764718, by rfl⟩ : syracuseStep 2039249 = 1529437) B1529437
theorem B1359315 : Blo 1358498 1359315 := bstep (se 1 (by rfl) ⟨1019486, by rfl⟩ : syracuseStep 1359315 = 2038973) B2038973
theorem B1359331 : Blo 1358498 1359331 := bstep (se 1 (by rfl) ⟨1019498, by rfl⟩ : syracuseStep 1359331 = 2038997) B2038997
theorem B2039267 : Blo 1358498 2039267 := bstep (se 1 (by rfl) ⟨1529450, by rfl⟩ : syracuseStep 2039267 = 3058901) B3058901
theorem B1359347 : Blo 1358498 1359347 := bstep (se 1 (by rfl) ⟨1019510, by rfl⟩ : syracuseStep 1359347 = 2039021) B2039021
theorem B2039297 : Blo 1358498 2039297 := bstep (se 2 (by rfl) ⟨764736, by rfl⟩ : syracuseStep 2039297 = 1529473) B1529473
theorem B1359363 : Blo 1358498 1359363 := bstep (se 1 (by rfl) ⟨1019522, by rfl⟩ : syracuseStep 1359363 = 2039045) B2039045
theorem B2293265 : Blo 1358498 2293265 := bstep (se 2 (by rfl) ⟨859974, by rfl⟩ : syracuseStep 2293265 = 1719949) B1719949
theorem B1359379 : Blo 1358498 1359379 := bstep (se 1 (by rfl) ⟨1019534, by rfl⟩ : syracuseStep 1359379 = 2039069) B2039069
theorem B2039315 : Blo 1358498 2039315 := bstep (se 1 (by rfl) ⟨1529486, by rfl⟩ : syracuseStep 2039315 = 3058973) B3058973
theorem B1359395 : Blo 1358498 1359395 := bstep (se 1 (by rfl) ⟨1019546, by rfl⟩ : syracuseStep 1359395 = 2039093) B2039093
theorem B2039345 : Blo 1358498 2039345 := bstep (se 2 (by rfl) ⟨764754, by rfl⟩ : syracuseStep 2039345 = 1529509) B1529509
theorem B1359411 : Blo 1358498 1359411 := bstep (se 1 (by rfl) ⟨1019558, by rfl⟩ : syracuseStep 1359411 = 2039117) B2039117
theorem B1359427 : Blo 1358498 1359427 := bstep (se 1 (by rfl) ⟨1019570, by rfl⟩ : syracuseStep 1359427 = 2039141) B2039141
theorem B2039363 : Blo 1358498 2039363 := bstep (se 1 (by rfl) ⟨1529522, by rfl⟩ : syracuseStep 2039363 = 3059045) B3059045
theorem B1359443 : Blo 1358498 1359443 := bstep (se 1 (by rfl) ⟨1019582, by rfl⟩ : syracuseStep 1359443 = 2039165) B2039165
theorem B2039393 : Blo 1358498 2039393 := bstep (se 2 (by rfl) ⟨764772, by rfl⟩ : syracuseStep 2039393 = 1529545) B1529545
theorem B10460771 : Blo 1358498 10460771 := bstep (se 1 (by rfl) ⟨7845578, by rfl⟩ : syracuseStep 10460771 = 15691157) B15691157
theorem B1359459 : Blo 1358498 1359459 := bstep (se 1 (by rfl) ⟨1019594, by rfl⟩ : syracuseStep 1359459 = 2039189) B2039189
theorem B1359475 : Blo 1358498 1359475 := bstep (se 1 (by rfl) ⟨1019606, by rfl⟩ : syracuseStep 1359475 = 2039213) B2039213
theorem B2039411 : Blo 1358498 2039411 := bstep (se 1 (by rfl) ⟨1529558, by rfl⟩ : syracuseStep 2039411 = 3059117) B3059117
theorem B1359491 : Blo 1358498 1359491 := bstep (se 1 (by rfl) ⟨1019618, by rfl⟩ : syracuseStep 1359491 = 2039237) B2039237
theorem B2293393 : Blo 1358498 2293393 := bstep (se 2 (by rfl) ⟨860022, by rfl⟩ : syracuseStep 2293393 = 1720045) B1720045
theorem B2580113 : Blo 1358498 2580113 := bstep (se 2 (by rfl) ⟨967542, by rfl⟩ : syracuseStep 2580113 = 1935085) B1935085
theorem B1359507 : Blo 1358498 1359507 := bstep (se 1 (by rfl) ⟨1019630, by rfl⟩ : syracuseStep 1359507 = 2039261) B2039261
theorem B2039441 : Blo 1358498 2039441 := bstep (se 2 (by rfl) ⟨764790, by rfl⟩ : syracuseStep 2039441 = 1529581) B1529581
theorem B1359523 : Blo 1358498 1359523 := bstep (se 1 (by rfl) ⟨1019642, by rfl⟩ : syracuseStep 1359523 = 2039285) B2039285
theorem B2039459 : Blo 1358498 2039459 := bstep (se 1 (by rfl) ⟨1529594, by rfl⟩ : syracuseStep 2039459 = 3059189) B3059189
theorem B2293427 : Blo 1358498 2293427 := bstep (se 1 (by rfl) ⟨1720070, by rfl⟩ : syracuseStep 2293427 = 3440141) B3440141
theorem B1359539 : Blo 1358498 1359539 := bstep (se 1 (by rfl) ⟨1019654, by rfl⟩ : syracuseStep 1359539 = 2039309) B2039309
theorem B2039489 : Blo 1358498 2039489 := bstep (se 2 (by rfl) ⟨764808, by rfl⟩ : syracuseStep 2039489 = 1529617) B1529617
theorem B1359555 : Blo 1358498 1359555 := bstep (se 1 (by rfl) ⟨1019666, by rfl⟩ : syracuseStep 1359555 = 2039333) B2039333
theorem B4357837 : Blo 1358498 4357837 := bstep (se 3 (by rfl) ⟨817094, by rfl⟩ : syracuseStep 4357837 = 1634189) B1634189
theorem B6536909 : Blo 1358498 6536909 := bstep (se 3 (by rfl) ⟨1225670, by rfl⟩ : syracuseStep 6536909 = 2451341) B2451341
theorem B1359571 : Blo 1358498 1359571 := bstep (se 1 (by rfl) ⟨1019678, by rfl⟩ : syracuseStep 1359571 = 2039357) B2039357
theorem B2039507 : Blo 1358498 2039507 := bstep (se 1 (by rfl) ⟨1529630, by rfl⟩ : syracuseStep 2039507 = 3059261) B3059261
theorem B4898531 : Blo 1358498 4898531 := bstep (se 1 (by rfl) ⟨3673898, by rfl⟩ : syracuseStep 4898531 = 7347797) B7347797
theorem B1359587 : Blo 1358498 1359587 := bstep (se 1 (by rfl) ⟨1019690, by rfl⟩ : syracuseStep 1359587 = 2039381) B2039381
theorem B4587245 : Blo 1358498 4587245 := bstep (se 3 (by rfl) ⟨860108, by rfl⟩ : syracuseStep 4587245 = 1720217) B1720217
theorem B2039537 : Blo 1358498 2039537 := bstep (se 2 (by rfl) ⟨764826, by rfl⟩ : syracuseStep 2039537 = 1529653) B1529653
theorem B1359603 : Blo 1358498 1359603 := bstep (se 1 (by rfl) ⟨1019702, by rfl⟩ : syracuseStep 1359603 = 2039405) B2039405
theorem B1359619 : Blo 1358498 1359619 := bstep (se 1 (by rfl) ⟨1019714, by rfl⟩ : syracuseStep 1359619 = 2039429) B2039429
theorem B2039555 : Blo 1358498 2039555 := bstep (se 1 (by rfl) ⟨1529666, by rfl⟩ : syracuseStep 2039555 = 3059333) B3059333
theorem B1359635 : Blo 1358498 1359635 := bstep (se 1 (by rfl) ⟨1019726, by rfl⟩ : syracuseStep 1359635 = 2039453) B2039453
theorem B2039585 : Blo 1358498 2039585 := bstep (se 2 (by rfl) ⟨764844, by rfl⟩ : syracuseStep 2039585 = 1529689) B1529689
theorem B4587299 : Blo 1358498 4587299 := bstep (se 1 (by rfl) ⟨3440474, by rfl⟩ : syracuseStep 4587299 = 6880949) B6880949
theorem B1359651 : Blo 1358498 1359651 := bstep (se 1 (by rfl) ⟨1019738, by rfl⟩ : syracuseStep 1359651 = 2039477) B2039477
theorem B2449201 : Blo 1358498 2449201 := bstep (se 2 (by rfl) ⟨918450, by rfl⟩ : syracuseStep 2449201 = 1836901) B1836901
theorem B3923761 : Blo 1358498 3923761 := bstep (se 2 (by rfl) ⟨1471410, by rfl⟩ : syracuseStep 3923761 = 2942821) B2942821
theorem B2293555 : Blo 1358498 2293555 := bstep (se 1 (by rfl) ⟨1720166, by rfl⟩ : syracuseStep 2293555 = 3440333) B3440333
theorem B1359667 : Blo 1358498 1359667 := bstep (se 1 (by rfl) ⟨1019750, by rfl⟩ : syracuseStep 1359667 = 2039501) B2039501
theorem B2039603 : Blo 1358498 2039603 := bstep (se 1 (by rfl) ⟨1529702, by rfl⟩ : syracuseStep 2039603 = 3059405) B3059405
theorem B1359683 : Blo 1358498 1359683 := bstep (se 1 (by rfl) ⟨1019762, by rfl⟩ : syracuseStep 1359683 = 2039525) B2039525
theorem B3440465 : Blo 1358498 3440465 := bstep (se 2 (by rfl) ⟨1290174, by rfl⟩ : syracuseStep 3440465 = 2580349) B2580349
theorem B2039633 : Blo 1358498 2039633 := bstep (se 2 (by rfl) ⟨764862, by rfl⟩ : syracuseStep 2039633 = 1529725) B1529725
theorem B1359699 : Blo 1358498 1359699 := bstep (se 1 (by rfl) ⟨1019774, by rfl⟩ : syracuseStep 1359699 = 2039549) B2039549
theorem B2178913 : Blo 1358498 2178913 := bstep (se 2 (by rfl) ⟨817092, by rfl⟩ : syracuseStep 2178913 = 1634185) B1634185
theorem B1359715 : Blo 1358498 1359715 := bstep (se 1 (by rfl) ⟨1019786, by rfl⟩ : syracuseStep 1359715 = 2039573) B2039573
theorem B2039651 : Blo 1358498 2039651 := bstep (se 1 (by rfl) ⟨1529738, by rfl⟩ : syracuseStep 2039651 = 3059477) B3059477
theorem B1359731 : Blo 1358498 1359731 := bstep (se 1 (by rfl) ⟨1019798, by rfl⟩ : syracuseStep 1359731 = 2039597) B2039597
theorem B2039681 : Blo 1358498 2039681 := bstep (se 2 (by rfl) ⟨764880, by rfl⟩ : syracuseStep 2039681 = 1529761) B1529761
theorem B3440515 : Blo 1358498 3440515 := bstep (se 1 (by rfl) ⟨2580386, by rfl⟩ : syracuseStep 3440515 = 5160773) B5160773
theorem B1359747 : Blo 1358498 1359747 := bstep (se 1 (by rfl) ⟨1019810, by rfl⟩ : syracuseStep 1359747 = 2039621) B2039621
theorem B1359763 : Blo 1358498 1359763 := bstep (se 1 (by rfl) ⟨1019822, by rfl⟩ : syracuseStep 1359763 = 2039645) B2039645
theorem B2039699 : Blo 1358498 2039699 := bstep (se 1 (by rfl) ⟨1529774, by rfl⟩ : syracuseStep 2039699 = 3059549) B3059549
theorem B1359779 : Blo 1358498 1359779 := bstep (se 1 (by rfl) ⟨1019834, by rfl⟩ : syracuseStep 1359779 = 2039669) B2039669
theorem B2039729 : Blo 1358498 2039729 := bstep (se 2 (by rfl) ⟨764898, by rfl⟩ : syracuseStep 2039729 = 1529797) B1529797
theorem B1359795 : Blo 1358498 1359795 := bstep (se 1 (by rfl) ⟨1019846, by rfl⟩ : syracuseStep 1359795 = 2039693) B2039693
theorem B2293697 : Blo 1358498 2293697 := bstep (se 2 (by rfl) ⟨860136, by rfl⟩ : syracuseStep 2293697 = 1720273) B1720273
theorem B1359811 : Blo 1358498 1359811 := bstep (se 1 (by rfl) ⟨1019858, by rfl⟩ : syracuseStep 1359811 = 2039717) B2039717
theorem B2039747 : Blo 1358498 2039747 := bstep (se 1 (by rfl) ⟨1529810, by rfl⟩ : syracuseStep 2039747 = 3059621) B3059621
theorem B16752581 : Blo 1358498 16752581 := bstep (se 4 (by rfl) ⟨1570554, by rfl⟩ : syracuseStep 16752581 = 3141109) B3141109
theorem B1359827 : Blo 1358498 1359827 := bstep (se 1 (by rfl) ⟨1019870, by rfl⟩ : syracuseStep 1359827 = 2039741) B2039741
theorem B2039777 : Blo 1358498 2039777 := bstep (se 2 (by rfl) ⟨764916, by rfl⟩ : syracuseStep 2039777 = 1529833) B1529833
theorem B1359843 : Blo 1358498 1359843 := bstep (se 1 (by rfl) ⟨1019882, by rfl⟩ : syracuseStep 1359843 = 2039765) B2039765
theorem B11608049 : Blo 1358498 11608049 := bstep (se 2 (by rfl) ⟨4353018, by rfl⟩ : syracuseStep 11608049 = 8706037) B8706037
theorem B1359859 : Blo 1358498 1359859 := bstep (se 1 (by rfl) ⟨1019894, by rfl⟩ : syracuseStep 1359859 = 2039789) B2039789
theorem B2039795 : Blo 1358498 2039795 := bstep (se 1 (by rfl) ⟨1529846, by rfl⟩ : syracuseStep 2039795 = 3059693) B3059693
theorem B2293771 : Blo 1358498 2293771 := bstep (se 1 (by rfl) ⟨1720328, by rfl⟩ : syracuseStep 2293771 = 3440657) B3440657
theorem B2039819 : Blo 1358498 2039819 := bstep (se 1 (by rfl) ⟨1529864, by rfl⟩ : syracuseStep 2039819 = 3059729) B3059729
theorem B1359883 : Blo 1358498 1359883 := bstep (se 1 (by rfl) ⟨1019912, by rfl⟩ : syracuseStep 1359883 = 2039825) B2039825
theorem B2039831 : Blo 1358498 2039831 := bstep (se 1 (by rfl) ⟨1529873, by rfl⟩ : syracuseStep 2039831 = 3059747) B3059747
theorem B1359895 : Blo 1358498 1359895 := bstep (se 1 (by rfl) ⟨1019921, by rfl⟩ : syracuseStep 1359895 = 2039843) B2039843
theorem B2449433 : Blo 1358498 2449433 := bstep (se 2 (by rfl) ⟨918537, by rfl⟩ : syracuseStep 2449433 = 1837075) B1837075
theorem B1359915 : Blo 1358498 1359915 := bstep (se 1 (by rfl) ⟨1019936, by rfl⟩ : syracuseStep 1359915 = 2039873) B2039873
theorem B1359927 : Blo 1358498 1359927 := bstep (se 1 (by rfl) ⟨1019945, by rfl⟩ : syracuseStep 1359927 = 2039891) B2039891
theorem B1359947 : Blo 1358498 1359947 := bstep (se 1 (by rfl) ⟨1019960, by rfl⟩ : syracuseStep 1359947 = 2039921) B2039921
theorem B1359959 : Blo 1358498 1359959 := bstep (se 1 (by rfl) ⟨1019969, by rfl⟩ : syracuseStep 1359959 = 2039939) B2039939
theorem B2580569 : Blo 1358498 2580569 := bstep (se 2 (by rfl) ⟨967713, by rfl⟩ : syracuseStep 2580569 = 1935427) B1935427
theorem B2039897 : Blo 1358498 2039897 := bstep (se 2 (by rfl) ⟨764961, by rfl⟩ : syracuseStep 2039897 = 1529923) B1529923
theorem B1359979 : Blo 1358498 1359979 := bstep (se 1 (by rfl) ⟨1019984, by rfl⟩ : syracuseStep 1359979 = 2039969) B2039969
theorem B1359991 : Blo 1358498 1359991 := bstep (se 1 (by rfl) ⟨1019993, by rfl⟩ : syracuseStep 1359991 = 2039987) B2039987
theorem B1360011 : Blo 1358498 1360011 := bstep (se 1 (by rfl) ⟨1020008, by rfl⟩ : syracuseStep 1360011 = 2040017) B2040017
theorem B1360023 : Blo 1358498 1360023 := bstep (se 1 (by rfl) ⟨1020017, by rfl⟩ : syracuseStep 1360023 = 2040035) B2040035
theorem B2293913 : Blo 1358498 2293913 := bstep (se 2 (by rfl) ⟨860217, by rfl⟩ : syracuseStep 2293913 = 1720435) B1720435
theorem B1360043 : Blo 1358498 1360043 := bstep (se 1 (by rfl) ⟨1020032, by rfl⟩ : syracuseStep 1360043 = 2040065) B2040065
theorem B3440819 : Blo 1358498 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B1360055 : Blo 1358498 1360055 := bstep (se 1 (by rfl) ⟨1020041, by rfl⟩ : syracuseStep 1360055 = 2040083) B2040083
theorem B2040011 : Blo 1358498 2040011 := bstep (se 1 (by rfl) ⟨1530008, by rfl⟩ : syracuseStep 2040011 = 3060017) B3060017
theorem B1360075 : Blo 1358498 1360075 := bstep (se 1 (by rfl) ⟨1020056, by rfl⟩ : syracuseStep 1360075 = 2040113) B2040113
theorem B2040023 : Blo 1358498 2040023 := bstep (se 1 (by rfl) ⟨1530017, by rfl⟩ : syracuseStep 2040023 = 3060035) B3060035
theorem B1360087 : Blo 1358498 1360087 := bstep (se 1 (by rfl) ⟨1020065, by rfl⟩ : syracuseStep 1360087 = 2040131) B2040131
theorem B1360107 : Blo 1358498 1360107 := bstep (se 1 (by rfl) ⟨1020080, by rfl⟩ : syracuseStep 1360107 = 2040161) B2040161
theorem B1360119 : Blo 1358498 1360119 := bstep (se 1 (by rfl) ⟨1020089, by rfl⟩ : syracuseStep 1360119 = 2040179) B2040179
theorem B1360139 : Blo 1358498 1360139 := bstep (se 1 (by rfl) ⟨1020104, by rfl⟩ : syracuseStep 1360139 = 2040209) B2040209
theorem B1360151 : Blo 1358498 1360151 := bstep (se 1 (by rfl) ⟨1020113, by rfl⟩ : syracuseStep 1360151 = 2040227) B2040227
theorem B2294041 : Blo 1358498 2294041 := bstep (se 2 (by rfl) ⟨860265, by rfl⟩ : syracuseStep 2294041 = 1720531) B1720531
theorem B2040089 : Blo 1358498 2040089 := bstep (se 2 (by rfl) ⟨765033, by rfl⟩ : syracuseStep 2040089 = 1530067) B1530067
theorem B27885869 : Blo 1358498 27885869 := bstep (se 3 (by rfl) ⟨5228600, by rfl⟩ : syracuseStep 27885869 = 10457201) B10457201
theorem B1360171 : Blo 1358498 1360171 := bstep (se 1 (by rfl) ⟨1020128, by rfl⟩ : syracuseStep 1360171 = 2040257) B2040257
theorem B1360183 : Blo 1358498 1360183 := bstep (se 1 (by rfl) ⟨1020137, by rfl⟩ : syracuseStep 1360183 = 2040275) B2040275
theorem B1360203 : Blo 1358498 1360203 := bstep (se 1 (by rfl) ⟨1020152, by rfl⟩ : syracuseStep 1360203 = 2040305) B2040305
theorem B1360215 : Blo 1358498 1360215 := bstep (se 1 (by rfl) ⟨1020161, by rfl⟩ : syracuseStep 1360215 = 2040323) B2040323
theorem B1360235 : Blo 1358498 1360235 := bstep (se 1 (by rfl) ⟨1020176, by rfl⟩ : syracuseStep 1360235 = 2040353) B2040353
theorem B1360247 : Blo 1358498 1360247 := bstep (se 1 (by rfl) ⟨1020185, by rfl⟩ : syracuseStep 1360247 = 2040371) B2040371
theorem B2040203 : Blo 1358498 2040203 := bstep (se 1 (by rfl) ⟨1530152, by rfl⟩ : syracuseStep 2040203 = 3060305) B3060305
theorem B1360267 : Blo 1358498 1360267 := bstep (se 1 (by rfl) ⟨1020200, by rfl⟩ : syracuseStep 1360267 = 2040401) B2040401
theorem B2040215 : Blo 1358498 2040215 := bstep (se 1 (by rfl) ⟨1530161, by rfl⟩ : syracuseStep 2040215 = 3060323) B3060323
theorem B1360279 : Blo 1358498 1360279 := bstep (se 1 (by rfl) ⟨1020209, by rfl⟩ : syracuseStep 1360279 = 2040419) B2040419
theorem B1360299 : Blo 1358498 1360299 := bstep (se 1 (by rfl) ⟨1020224, by rfl⟩ : syracuseStep 1360299 = 2040449) B2040449
theorem B1360311 : Blo 1358498 1360311 := bstep (se 1 (by rfl) ⟨1020233, by rfl⟩ : syracuseStep 1360311 = 2040467) B2040467
theorem B1360331 : Blo 1358498 1360331 := bstep (se 1 (by rfl) ⟨1020248, by rfl⟩ : syracuseStep 1360331 = 2040497) B2040497
theorem B1360343 : Blo 1358498 1360343 := bstep (se 1 (by rfl) ⟨1020257, by rfl⟩ : syracuseStep 1360343 = 2040515) B2040515
theorem B3441113 : Blo 1358498 3441113 := bstep (se 2 (by rfl) ⟨1290417, by rfl⟩ : syracuseStep 3441113 = 2580835) B2580835
theorem B2040281 : Blo 1358498 2040281 := bstep (se 2 (by rfl) ⟨765105, by rfl⟩ : syracuseStep 2040281 = 1530211) B1530211
theorem B1360363 : Blo 1358498 1360363 := bstep (se 1 (by rfl) ⟨1020272, by rfl⟩ : syracuseStep 1360363 = 2040545) B2040545
theorem B2580979 : Blo 1358498 2580979 := bstep (se 1 (by rfl) ⟨1935734, by rfl⟩ : syracuseStep 2580979 = 3871469) B3871469
theorem B1360375 : Blo 1358498 1360375 := bstep (se 1 (by rfl) ⟨1020281, by rfl⟩ : syracuseStep 1360375 = 2040563) B2040563
theorem B1360395 : Blo 1358498 1360395 := bstep (se 1 (by rfl) ⟨1020296, by rfl⟩ : syracuseStep 1360395 = 2040593) B2040593
theorem B4588055 : Blo 1358498 4588055 := bstep (se 1 (by rfl) ⟨3441041, by rfl⟩ : syracuseStep 4588055 = 6882083) B6882083
theorem B1720855 : Blo 1358498 1720855 := bstep (se 1 (by rfl) ⟨1290641, by rfl⟩ : syracuseStep 1720855 = 2581283) B2581283
theorem B1360407 : Blo 1358498 1360407 := bstep (se 1 (by rfl) ⟨1020305, by rfl⟩ : syracuseStep 1360407 = 2040611) B2040611
theorem B1360427 : Blo 1358498 1360427 := bstep (se 1 (by rfl) ⟨1020320, by rfl⟩ : syracuseStep 1360427 = 2040641) B2040641
theorem B1360439 : Blo 1358498 1360439 := bstep (se 1 (by rfl) ⟨1020329, by rfl⟩ : syracuseStep 1360439 = 2040659) B2040659
theorem B2040395 : Blo 1358498 2040395 := bstep (se 1 (by rfl) ⟨1530296, by rfl⟩ : syracuseStep 2040395 = 3060593) B3060593
theorem B1360459 : Blo 1358498 1360459 := bstep (se 1 (by rfl) ⟨1020344, by rfl⟩ : syracuseStep 1360459 = 2040689) B2040689
theorem B2040407 : Blo 1358498 2040407 := bstep (se 1 (by rfl) ⟨1530305, by rfl⟩ : syracuseStep 2040407 = 3060611) B3060611
theorem B1360471 : Blo 1358498 1360471 := bstep (se 1 (by rfl) ⟨1020353, by rfl⟩ : syracuseStep 1360471 = 2040707) B2040707
theorem B1360491 : Blo 1358498 1360491 := bstep (se 1 (by rfl) ⟨1020368, by rfl⟩ : syracuseStep 1360491 = 2040737) B2040737
theorem B2040473 : Blo 1358498 2040473 := bstep (se 2 (by rfl) ⟨765177, by rfl⟩ : syracuseStep 2040473 = 1530355) B1530355
theorem B2794201 : Blo 1358498 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B2040587 : Blo 1358498 2040587 := bstep (se 1 (by rfl) ⟨1530440, by rfl⟩ : syracuseStep 2040587 = 3060881) B3060881
theorem B5161745 : Blo 1358498 5161745 := bstep (se 2 (by rfl) ⟨1935654, by rfl⟩ : syracuseStep 5161745 = 3871309) B3871309
theorem B2040599 : Blo 1358498 2040599 := bstep (se 1 (by rfl) ⟨1530449, by rfl⟩ : syracuseStep 2040599 = 3060899) B3060899
theorem B2294615 : Blo 1358498 2294615 := bstep (se 1 (by rfl) ⟨1720961, by rfl⟩ : syracuseStep 2294615 = 3441923) B3441923
theorem B2040665 : Blo 1358498 2040665 := bstep (se 2 (by rfl) ⟨765249, by rfl⟩ : syracuseStep 2040665 = 1530499) B1530499
theorem B5514077 : Blo 1358498 5514077 := bstep (se 3 (by rfl) ⟨1033889, by rfl⟩ : syracuseStep 5514077 = 2067779) B2067779
theorem B11772803 : Blo 1358498 11772803 := bstep (se 1 (by rfl) ⟨8829602, by rfl⟩ : syracuseStep 11772803 = 17659205) B17659205
theorem B26502065 : Blo 1358498 26502065 := bstep (se 2 (by rfl) ⟨9938274, by rfl⟩ : syracuseStep 26502065 = 19876549) B19876549
theorem B2294743 : Blo 1358498 2294743 := bstep (se 1 (by rfl) ⟨1721057, by rfl⟩ : syracuseStep 2294743 = 3442115) B3442115
theorem B2581465 : Blo 1358498 2581465 := bstep (se 2 (by rfl) ⟨968049, by rfl⟩ : syracuseStep 2581465 = 1936099) B1936099
theorem B5809117 : Blo 1358498 5809117 := bstep (se 3 (by rfl) ⟨1089209, by rfl⟩ : syracuseStep 5809117 = 2178419) B2178419
theorem B3056651 : Blo 1358498 3056651 := bstep (se 1 (by rfl) ⟨2292488, by rfl⟩ : syracuseStep 3056651 = 4584977) B4584977
theorem B4654103 : Blo 1358498 4654103 := bstep (se 1 (by rfl) ⟨3490577, by rfl⟩ : syracuseStep 4654103 = 6981155) B6981155
theorem B4588595 : Blo 1358498 4588595 := bstep (se 1 (by rfl) ⟨3441446, by rfl⟩ : syracuseStep 4588595 = 6882893) B6882893
theorem B3056705 : Blo 1358498 3056705 := bstep (se 2 (by rfl) ⟨1146264, by rfl⟩ : syracuseStep 3056705 = 2292529) B2292529
theorem B2065559 : Blo 1358498 2065559 := bstep (se 1 (by rfl) ⟨1549169, by rfl⟩ : syracuseStep 2065559 = 3098339) B3098339
theorem B7349399 : Blo 1358498 7349399 := bstep (se 1 (by rfl) ⟨5512049, by rfl⟩ : syracuseStep 7349399 = 11024099) B11024099
theorem B2450585 : Blo 1358498 2450585 := bstep (se 2 (by rfl) ⟨918969, by rfl⟩ : syracuseStep 2450585 = 1837939) B1837939
theorem B223323317 : Blo 1358498 223323317 := bstep (se 5 (by rfl) ⟨10468280, by rfl⟩ : syracuseStep 223323317 = 20936561) B20936561
theorem B23545037 : Blo 1358498 23545037 := bstep (se 3 (by rfl) ⟨4414694, by rfl⟩ : syracuseStep 23545037 = 8829389) B8829389
theorem B5162201 : Blo 1358498 5162201 := bstep (se 2 (by rfl) ⟨1935825, by rfl⟩ : syracuseStep 5162201 = 3871651) B3871651
theorem B6980825 : Blo 1358498 6980825 := bstep (se 2 (by rfl) ⟨2617809, by rfl⟩ : syracuseStep 6980825 = 5235619) B5235619
theorem B3056921 : Blo 1358498 3056921 := bstep (se 2 (by rfl) ⟨1146345, by rfl⟩ : syracuseStep 3056921 = 2292691) B2292691
theorem B4588865 : Blo 1358498 4588865 := bstep (se 2 (by rfl) ⟨1720824, by rfl⟩ : syracuseStep 4588865 = 3441649) B3441649
theorem B1721675 : Blo 1358498 1721675 := bstep (se 1 (by rfl) ⟨1291256, by rfl⟩ : syracuseStep 1721675 = 2582513) B2582513
theorem B3057011 : Blo 1358498 3057011 := bstep (se 1 (by rfl) ⟨2292758, by rfl⟩ : syracuseStep 3057011 = 4585517) B4585517
theorem B3057047 : Blo 1358498 3057047 := bstep (se 1 (by rfl) ⟨2292785, by rfl⟩ : syracuseStep 3057047 = 4585571) B4585571
theorem B5162413 : Blo 1358498 5162413 := bstep (se 3 (by rfl) ⟨967952, by rfl⟩ : syracuseStep 5162413 = 1935905) B1935905
theorem B1359863 : Blo 1358498 1359863 := bstep (se 1 (by rfl) ⟨1019897, by rfl⟩ : syracuseStep 1359863 = 2039795) B2039795
theorem B2582027 : Blo 1358498 2582027 := bstep (se 1 (by rfl) ⟨1936520, by rfl⟩ : syracuseStep 2582027 = 3873041) B3873041
theorem B3057227 : Blo 1358498 3057227 := bstep (se 1 (by rfl) ⟨2292920, by rfl⟩ : syracuseStep 3057227 = 4585841) B4585841
theorem B2295371 : Blo 1358498 2295371 := bstep (se 1 (by rfl) ⟨1721528, by rfl⟩ : syracuseStep 2295371 = 3443057) B3443057
theorem B3057281 : Blo 1358498 3057281 := bstep (se 2 (by rfl) ⟨1146480, by rfl⟩ : syracuseStep 3057281 = 2292961) B2292961
theorem B2582209 : Blo 1358498 2582209 := bstep (se 2 (by rfl) ⟨968328, by rfl⟩ : syracuseStep 2582209 = 1936657) B1936657
theorem B2295499 : Blo 1358498 2295499 := bstep (se 1 (by rfl) ⟨1721624, by rfl⟩ : syracuseStep 2295499 = 3443249) B3443249
theorem B5162717 : Blo 1358498 5162717 := bstep (se 3 (by rfl) ⟨968009, by rfl⟩ : syracuseStep 5162717 = 1936019) B1936019
theorem B3057497 : Blo 1358498 3057497 := bstep (se 2 (by rfl) ⟨1146561, by rfl⟩ : syracuseStep 3057497 = 2293123) B2293123
theorem B2295641 : Blo 1358498 2295641 := bstep (se 2 (by rfl) ⟨860865, by rfl⟩ : syracuseStep 2295641 = 1721731) B1721731
theorem B4589405 : Blo 1358498 4589405 := bstep (se 3 (by rfl) ⟨860513, by rfl⟩ : syracuseStep 4589405 = 1721027) B1721027
theorem B11773873 : Blo 1358498 11773873 := bstep (se 2 (by rfl) ⟨4415202, by rfl⟩ : syracuseStep 11773873 = 8830405) B8830405
theorem B3057587 : Blo 1358498 3057587 := bstep (se 1 (by rfl) ⟨2293190, by rfl⟩ : syracuseStep 3057587 = 4586381) B4586381
theorem B3057623 : Blo 1358498 3057623 := bstep (se 1 (by rfl) ⟨2293217, by rfl⟩ : syracuseStep 3057623 = 4586435) B4586435
theorem B2295769 : Blo 1358498 2295769 := bstep (se 2 (by rfl) ⟨860913, by rfl⟩ : syracuseStep 2295769 = 1721827) B1721827
theorem B2484275 : Blo 1358498 2484275 := bstep (se 1 (by rfl) ⟨1863206, by rfl⟩ : syracuseStep 2484275 = 3726413) B3726413
theorem B2902081 : Blo 1358498 2902081 := bstep (se 2 (by rfl) ⟨1088280, by rfl⟩ : syracuseStep 2902081 = 2176561) B2176561
theorem B4909121 : Blo 1358498 4909121 := bstep (se 2 (by rfl) ⟨1840920, by rfl⟩ : syracuseStep 4909121 = 3681841) B3681841
theorem B3442763 : Blo 1358498 3442763 := bstep (se 1 (by rfl) ⟨2582072, by rfl⟩ : syracuseStep 3442763 = 5164145) B5164145
theorem B1452151 : Blo 1358498 1452151 := bstep (se 1 (by rfl) ⟨1089113, by rfl⟩ : syracuseStep 1452151 = 2178227) B2178227
theorem B3057803 : Blo 1358498 3057803 := bstep (se 1 (by rfl) ⟨2293352, by rfl⟩ : syracuseStep 3057803 = 4586705) B4586705
theorem B3057857 : Blo 1358498 3057857 := bstep (se 2 (by rfl) ⟨1146696, by rfl⟩ : syracuseStep 3057857 = 2293393) B2293393
theorem B4901057 : Blo 1358498 4901057 := bstep (se 2 (by rfl) ⟨1837896, by rfl⟩ : syracuseStep 4901057 = 3675793) B3675793
theorem B5810449 : Blo 1358498 5810449 := bstep (se 2 (by rfl) ⟨2178918, by rfl⟩ : syracuseStep 5810449 = 4357837) B4357837
theorem B6973847 : Blo 1358498 6973847 := bstep (se 1 (by rfl) ⟨5230385, by rfl⟩ : syracuseStep 6973847 = 10460771) B10460771
theorem B11618711 : Blo 1358498 11618711 := bstep (se 1 (by rfl) ⟨8714033, by rfl⟩ : syracuseStep 11618711 = 17428067) B17428067
theorem B3058073 : Blo 1358498 3058073 := bstep (se 2 (by rfl) ⟨1146777, by rfl⟩ : syracuseStep 3058073 = 2293555) B2293555
theorem B3058163 : Blo 1358498 3058163 := bstep (se 1 (by rfl) ⟨2293622, by rfl⟩ : syracuseStep 3058163 = 4587245) B4587245
theorem B3058199 : Blo 1358498 3058199 := bstep (se 1 (by rfl) ⟨2293649, by rfl⟩ : syracuseStep 3058199 = 4587299) B4587299
theorem B11168387 : Blo 1358498 11168387 := bstep (se 1 (by rfl) ⟨8376290, by rfl⟩ : syracuseStep 11168387 = 16752581) B16752581
theorem B3058379 : Blo 1358498 3058379 := bstep (se 1 (by rfl) ⟨2293784, by rfl⟩ : syracuseStep 3058379 = 4587569) B4587569
theorem B3058433 : Blo 1358498 3058433 := bstep (se 2 (by rfl) ⟨1146912, by rfl⟩ : syracuseStep 3058433 = 2293825) B2293825
theorem B7744349 : Blo 1358498 7744349 := bstep (se 3 (by rfl) ⟨1452065, by rfl⟩ : syracuseStep 7744349 = 2904131) B2904131
theorem B6884189 : Blo 1358498 6884189 := bstep (se 3 (by rfl) ⟨1290785, by rfl⟩ : syracuseStep 6884189 = 2581571) B2581571
theorem B8711063 : Blo 1358498 8711063 := bstep (se 1 (by rfl) ⟨6533297, by rfl⟩ : syracuseStep 8711063 = 13066595) B13066595
theorem B5802931 : Blo 1358498 5802931 := bstep (se 1 (by rfl) ⟨4352198, by rfl⟩ : syracuseStep 5802931 = 8704397) B8704397
theorem B4590539 : Blo 1358498 4590539 := bstep (se 1 (by rfl) ⟨3442904, by rfl⟩ : syracuseStep 4590539 = 6885809) B6885809
theorem B3058649 : Blo 1358498 3058649 := bstep (se 2 (by rfl) ⟨1146993, by rfl⟩ : syracuseStep 3058649 = 2293987) B2293987
theorem B3099671 : Blo 1358498 3099671 := bstep (se 1 (by rfl) ⟨2324753, by rfl⟩ : syracuseStep 3099671 = 4649507) B4649507
theorem B3443735 : Blo 1358498 3443735 := bstep (se 1 (by rfl) ⟨2582801, by rfl⟩ : syracuseStep 3443735 = 5165603) B5165603
theorem B4901933 : Blo 1358498 4901933 := bstep (se 3 (by rfl) ⟨919112, by rfl⟩ : syracuseStep 4901933 = 1838225) B1838225
theorem B3058739 : Blo 1358498 3058739 := bstep (se 1 (by rfl) ⟨2294054, by rfl⟩ : syracuseStep 3058739 = 4588109) B4588109
theorem B9301067 : Blo 1358498 9301067 := bstep (se 1 (by rfl) ⟨6975800, by rfl⟩ : syracuseStep 9301067 = 13951601) B13951601
theorem B3058775 : Blo 1358498 3058775 := bstep (se 1 (by rfl) ⟨2294081, by rfl⟩ : syracuseStep 3058775 = 4588163) B4588163
theorem B8383589 : Blo 1358498 8383589 := bstep (se 4 (by rfl) ⟨785961, by rfl⟩ : syracuseStep 8383589 = 1571923) B1571923
theorem B11029709 : Blo 1358498 11029709 := bstep (se 3 (by rfl) ⟨2068070, by rfl⟩ : syracuseStep 11029709 = 4136141) B4136141
theorem B4590809 : Blo 1358498 4590809 := bstep (se 2 (by rfl) ⟨1721553, by rfl⟩ : syracuseStep 4590809 = 3443107) B3443107
theorem B1395947 : Blo 1358498 1395947 := bstep (se 1 (by rfl) ⟨1046960, by rfl⟩ : syracuseStep 1395947 = 2093921) B2093921
theorem B2616563 : Blo 1358498 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B3058955 : Blo 1358498 3058955 := bstep (se 1 (by rfl) ⟨2294216, by rfl⟩ : syracuseStep 3058955 = 4588433) B4588433
theorem B3059009 : Blo 1358498 3059009 := bstep (se 2 (by rfl) ⟨1147128, by rfl⟩ : syracuseStep 3059009 = 2294257) B2294257
theorem B1936919 : Blo 1358498 1936919 := bstep (se 1 (by rfl) ⟨1452689, by rfl⟩ : syracuseStep 1936919 = 2905379) B2905379
theorem B3059225 : Blo 1358498 3059225 := bstep (se 2 (by rfl) ⟨1147209, by rfl⟩ : syracuseStep 3059225 = 2294419) B2294419
theorem B3059315 : Blo 1358498 3059315 := bstep (se 1 (by rfl) ⟨2294486, by rfl⟩ : syracuseStep 3059315 = 4588973) B4588973
theorem B3100289 : Blo 1358498 3100289 := bstep (se 2 (by rfl) ⟨1162608, by rfl⟩ : syracuseStep 3100289 = 2325217) B2325217
theorem B3059351 : Blo 1358498 3059351 := bstep (se 1 (by rfl) ⟨2294513, by rfl⟩ : syracuseStep 3059351 = 4589027) B4589027
theorem B6205249 : Blo 1358498 6205249 := bstep (se 2 (by rfl) ⟨2326968, by rfl⟩ : syracuseStep 6205249 = 4653937) B4653937
theorem B3059531 : Blo 1358498 3059531 := bstep (se 1 (by rfl) ⟨2294648, by rfl⟩ : syracuseStep 3059531 = 4589297) B4589297
theorem B3059585 : Blo 1358498 3059585 := bstep (se 2 (by rfl) ⟨1147344, by rfl⟩ : syracuseStep 3059585 = 2294689) B2294689
theorem B6049687 : Blo 1358498 6049687 := bstep (se 1 (by rfl) ⟨4537265, by rfl⟩ : syracuseStep 6049687 = 9074531) B9074531
theorem B4591511 : Blo 1358498 4591511 := bstep (se 1 (by rfl) ⟨3443633, by rfl⟩ : syracuseStep 4591511 = 6887267) B6887267
theorem B2903987 : Blo 1358498 2903987 := bstep (se 1 (by rfl) ⟨2177990, by rfl⟩ : syracuseStep 2903987 = 4355981) B4355981
theorem B3977153 : Blo 1358498 3977153 := bstep (se 2 (by rfl) ⟨1491432, by rfl⟩ : syracuseStep 3977153 = 2982865) B2982865
theorem B3059801 : Blo 1358498 3059801 := bstep (se 2 (by rfl) ⟨1147425, by rfl⟩ : syracuseStep 3059801 = 2294851) B2294851
theorem B4354199 : Blo 1358498 4354199 := bstep (se 1 (by rfl) ⟨3265649, by rfl⟩ : syracuseStep 4354199 = 6531299) B6531299
theorem B3870899 : Blo 1358498 3870899 := bstep (se 1 (by rfl) ⟨2903174, by rfl⟩ : syracuseStep 3870899 = 5806349) B5806349
theorem B3059891 : Blo 1358498 3059891 := bstep (se 1 (by rfl) ⟨2294918, by rfl⟩ : syracuseStep 3059891 = 4589837) B4589837
theorem B3059927 : Blo 1358498 3059927 := bstep (se 1 (by rfl) ⟨2294945, by rfl⟩ : syracuseStep 3059927 = 4589891) B4589891
theorem B5165315 : Blo 1358498 5165315 := bstep (se 1 (by rfl) ⟨3873986, by rfl⟩ : syracuseStep 5165315 = 7747973) B7747973
theorem B5165329 : Blo 1358498 5165329 := bstep (se 2 (by rfl) ⟨1936998, by rfl⟩ : syracuseStep 5165329 = 3873997) B3873997
theorem B5804419 : Blo 1358498 5804419 := bstep (se 1 (by rfl) ⟨4353314, by rfl⟩ : syracuseStep 5804419 = 8706629) B8706629
theorem B3060107 : Blo 1358498 3060107 := bstep (se 1 (by rfl) ⟨2295080, by rfl⟩ : syracuseStep 3060107 = 4590161) B4590161
theorem B3871127 : Blo 1358498 3871127 := bstep (se 1 (by rfl) ⟨2903345, by rfl⟩ : syracuseStep 3871127 = 5806691) B5806691
theorem B2904473 : Blo 1358498 2904473 := bstep (se 2 (by rfl) ⟨1089177, by rfl⟩ : syracuseStep 2904473 = 2178355) B2178355
theorem B3060161 : Blo 1358498 3060161 := bstep (se 2 (by rfl) ⟨1147560, by rfl⟩ : syracuseStep 3060161 = 2295121) B2295121
theorem B1528375 : Blo 1358498 1528375 := bstep (se 1 (by rfl) ⟨1146281, by rfl⟩ : syracuseStep 1528375 = 2292563) B2292563
theorem B5165633 : Blo 1358498 5165633 := bstep (se 2 (by rfl) ⟨1937112, by rfl⟩ : syracuseStep 5165633 = 3874225) B3874225
theorem B3060377 : Blo 1358498 3060377 := bstep (se 2 (by rfl) ⟨1147641, by rfl⟩ : syracuseStep 3060377 = 2295283) B2295283
theorem B3871435 : Blo 1358498 3871435 := bstep (se 1 (by rfl) ⟨2903576, by rfl⟩ : syracuseStep 3871435 = 5807153) B5807153
theorem B7344857 : Blo 1358498 7344857 := bstep (se 2 (by rfl) ⟨2754321, by rfl⟩ : syracuseStep 7344857 = 5508643) B5508643
theorem B1528555 : Blo 1358498 1528555 := bstep (se 1 (by rfl) ⟨1146416, by rfl⟩ : syracuseStep 1528555 = 2292833) B2292833
theorem B3060467 : Blo 1358498 3060467 := bstep (se 1 (by rfl) ⟨2295350, by rfl⟩ : syracuseStep 3060467 = 4590701) B4590701
theorem B3060503 : Blo 1358498 3060503 := bstep (se 1 (by rfl) ⟨2295377, by rfl⟩ : syracuseStep 3060503 = 4590755) B4590755
theorem B1528663 : Blo 1358498 1528663 := bstep (se 1 (by rfl) ⟨1146497, by rfl⟩ : syracuseStep 1528663 = 2292995) B2292995
theorem B4354967 : Blo 1358498 4354967 := bstep (se 1 (by rfl) ⟨3266225, by rfl⟩ : syracuseStep 4354967 = 6532451) B6532451
theorem B6886295 : Blo 1358498 6886295 := bstep (se 1 (by rfl) ⟨5164721, by rfl⟩ : syracuseStep 6886295 = 10329443) B10329443
theorem B3060683 : Blo 1358498 3060683 := bstep (se 1 (by rfl) ⟨2295512, by rfl⟩ : syracuseStep 3060683 = 4591025) B4591025
theorem B5805017 : Blo 1358498 5805017 := bstep (se 2 (by rfl) ⟨2176881, by rfl⟩ : syracuseStep 5805017 = 4353763) B4353763
theorem B3871709 : Blo 1358498 3871709 := bstep (se 3 (by rfl) ⟨725945, by rfl⟩ : syracuseStep 3871709 = 1451891) B1451891
theorem B3060737 : Blo 1358498 3060737 := bstep (se 2 (by rfl) ⟨1147776, by rfl⟩ : syracuseStep 3060737 = 2295553) B2295553
theorem B1528843 : Blo 1358498 1528843 := bstep (se 1 (by rfl) ⟨1146632, by rfl⟩ : syracuseStep 1528843 = 2293265) B2293265
theorem B3265601 : Blo 1358498 3265601 := bstep (se 2 (by rfl) ⟨1224600, by rfl⟩ : syracuseStep 3265601 = 2449201) B2449201
theorem B5231681 : Blo 1358498 5231681 := bstep (se 2 (by rfl) ⟨1961880, by rfl⟩ : syracuseStep 5231681 = 3923761) B3923761
theorem B8262749 : Blo 1358498 8262749 := bstep (se 3 (by rfl) ⟨1549265, by rfl⟩ : syracuseStep 8262749 = 3098531) B3098531
theorem B1528951 : Blo 1358498 1528951 := bstep (se 1 (by rfl) ⟨1146713, by rfl⟩ : syracuseStep 1528951 = 2293427) B2293427
theorem B2905217 : Blo 1358498 2905217 := bstep (se 2 (by rfl) ⟨1089456, by rfl⟩ : syracuseStep 2905217 = 2178913) B2178913
theorem B3265687 : Blo 1358498 3265687 := bstep (se 1 (by rfl) ⟨2449265, by rfl⟩ : syracuseStep 3265687 = 4898531) B4898531
theorem B3060953 : Blo 1358498 3060953 := bstep (se 2 (by rfl) ⟨1147857, by rfl⟩ : syracuseStep 3060953 = 2295715) B2295715
theorem B1529131 : Blo 1358498 1529131 := bstep (se 1 (by rfl) ⟨1146848, by rfl⟩ : syracuseStep 1529131 = 2293697) B2293697
theorem B3061043 : Blo 1358498 3061043 := bstep (se 1 (by rfl) ⟨2295782, by rfl⟩ : syracuseStep 3061043 = 4591565) B4591565
theorem B5805377 : Blo 1358498 5805377 := bstep (se 2 (by rfl) ⟨2177016, by rfl⟩ : syracuseStep 5805377 = 4354033) B4354033
theorem B7738699 : Blo 1358498 7738699 := bstep (se 1 (by rfl) ⟨5804024, by rfl⟩ : syracuseStep 7738699 = 11608049) B11608049
theorem B3061079 : Blo 1358498 3061079 := bstep (se 1 (by rfl) ⟨2295809, by rfl⟩ : syracuseStep 3061079 = 4591619) B4591619
theorem B7746947 : Blo 1358498 7746947 := bstep (se 1 (by rfl) ⟨5810210, by rfl⟩ : syracuseStep 7746947 = 11620421) B11620421
theorem B1529239 : Blo 1358498 1529239 := bstep (se 1 (by rfl) ⟨1146929, by rfl⟩ : syracuseStep 1529239 = 2293859) B2293859
theorem B4355479 : Blo 1358498 4355479 := bstep (se 1 (by rfl) ⟨3266609, by rfl⟩ : syracuseStep 4355479 = 6533219) B6533219
theorem B3487169 : Blo 1358498 3487169 := bstep (se 2 (by rfl) ⟨1307688, by rfl⟩ : syracuseStep 3487169 = 2615377) B2615377
theorem B6878681 : Blo 1358498 6878681 := bstep (se 2 (by rfl) ⟨2579505, by rfl⟩ : syracuseStep 6878681 = 5159011) B5159011
theorem B1570379 : Blo 1358498 1570379 := bstep (se 1 (by rfl) ⟨1177784, by rfl⟩ : syracuseStep 1570379 = 2355569) B2355569
theorem B1529419 : Blo 1358498 1529419 := bstep (se 1 (by rfl) ⟨1147064, by rfl⟩ : syracuseStep 1529419 = 2294129) B2294129
theorem B7738973 : Blo 1358498 7738973 := bstep (se 3 (by rfl) ⟨1451057, by rfl⟩ : syracuseStep 7738973 = 2902115) B2902115
theorem B4585139 : Blo 1358498 4585139 := bstep (se 1 (by rfl) ⟨3438854, by rfl⟩ : syracuseStep 4585139 = 6877709) B6877709
theorem B1529527 : Blo 1358498 1529527 := bstep (se 1 (by rfl) ⟨1147145, by rfl⟩ : syracuseStep 1529527 = 2294291) B2294291
theorem B2176715 : Blo 1358498 2176715 := bstep (se 1 (by rfl) ⟨1632536, by rfl⟩ : syracuseStep 2176715 = 3265073) B3265073
theorem B14694209 : Blo 1358498 14694209 := bstep (se 2 (by rfl) ⟨5510328, by rfl⟩ : syracuseStep 14694209 = 11020657) B11020657
theorem B1529707 : Blo 1358498 1529707 := bstep (se 1 (by rfl) ⟨1147280, by rfl⟩ : syracuseStep 1529707 = 2294561) B2294561
theorem B7346051 : Blo 1358498 7346051 := bstep (se 1 (by rfl) ⟨5509538, by rfl⟩ : syracuseStep 7346051 = 11019077) B11019077
theorem B5158829 : Blo 1358498 5158829 := bstep (se 3 (by rfl) ⟨967280, by rfl⟩ : syracuseStep 5158829 = 1934561) B1934561
theorem B9795505 : Blo 1358498 9795505 := bstep (se 2 (by rfl) ⟨3673314, by rfl⟩ : syracuseStep 9795505 = 7346629) B7346629
theorem B10327985 : Blo 1358498 10327985 := bstep (se 2 (by rfl) ⟨3872994, by rfl⟩ : syracuseStep 10327985 = 7745989) B7745989
theorem B4585409 : Blo 1358498 4585409 := bstep (se 2 (by rfl) ⟨1719528, by rfl⟩ : syracuseStep 4585409 = 3439057) B3439057
theorem B1529815 : Blo 1358498 1529815 := bstep (se 1 (by rfl) ⟨1147361, by rfl⟩ : syracuseStep 1529815 = 2294723) B2294723
theorem B2037785 : Blo 1358498 2037785 := bstep (se 2 (by rfl) ⟨764169, by rfl⟩ : syracuseStep 2037785 = 1528339) B1528339
theorem B3676225 : Blo 1358498 3676225 := bstep (se 2 (by rfl) ⟨1378584, by rfl⟩ : syracuseStep 3676225 = 2757169) B2757169
theorem B2037899 : Blo 1358498 2037899 := bstep (se 1 (by rfl) ⟨1528424, by rfl⟩ : syracuseStep 2037899 = 3056849) B3056849
theorem B1529995 : Blo 1358498 1529995 := bstep (se 1 (by rfl) ⟨1147496, by rfl⟩ : syracuseStep 1529995 = 2294993) B2294993
theorem B2037911 : Blo 1358498 2037911 := bstep (se 1 (by rfl) ⟨1528433, by rfl⟩ : syracuseStep 2037911 = 3056867) B3056867
theorem B2177227 : Blo 1358498 2177227 := bstep (se 1 (by rfl) ⟨1632920, by rfl⟩ : syracuseStep 2177227 = 3265841) B3265841
theorem B4356299 : Blo 1358498 4356299 := bstep (se 1 (by rfl) ⟨3267224, by rfl⟩ : syracuseStep 4356299 = 6534449) B6534449
theorem B13072589 : Blo 1358498 13072589 := bstep (se 3 (by rfl) ⟨2451110, by rfl⟩ : syracuseStep 13072589 = 4902221) B4902221
theorem B2037977 : Blo 1358498 2037977 := bstep (se 2 (by rfl) ⟨764241, by rfl⟩ : syracuseStep 2037977 = 1528483) B1528483
theorem B1530103 : Blo 1358498 1530103 := bstep (se 1 (by rfl) ⟨1147577, by rfl⟩ : syracuseStep 1530103 = 2295155) B2295155
theorem B2038091 : Blo 1358498 2038091 := bstep (se 1 (by rfl) ⟨1528568, by rfl⟩ : syracuseStep 2038091 = 3057137) B3057137
theorem B2038103 : Blo 1358498 2038103 := bstep (se 1 (by rfl) ⟨1528577, by rfl⟩ : syracuseStep 2038103 = 3057155) B3057155
theorem B8714627 : Blo 1358498 8714627 := bstep (se 1 (by rfl) ⟨6535970, by rfl⟩ : syracuseStep 8714627 = 13071941) B13071941
theorem B10328471 : Blo 1358498 10328471 := bstep (se 1 (by rfl) ⟨7746353, by rfl⟩ : syracuseStep 10328471 = 15492707) B15492707
theorem B2038169 : Blo 1358498 2038169 := bstep (se 2 (by rfl) ⟨764313, by rfl⟩ : syracuseStep 2038169 = 1528627) B1528627
theorem B1530283 : Blo 1358498 1530283 := bstep (se 1 (by rfl) ⟨1147712, by rfl⟩ : syracuseStep 1530283 = 2295425) B2295425
theorem B4585949 : Blo 1358498 4585949 := bstep (se 3 (by rfl) ⟨859865, by rfl⟩ : syracuseStep 4585949 = 1719731) B1719731
theorem B2038283 : Blo 1358498 2038283 := bstep (se 1 (by rfl) ⟨1528712, by rfl⟩ : syracuseStep 2038283 = 3057425) B3057425
theorem B2038295 : Blo 1358498 2038295 := bstep (se 1 (by rfl) ⟨1528721, by rfl⟩ : syracuseStep 2038295 = 3057443) B3057443
theorem B1530391 : Blo 1358498 1530391 := bstep (se 1 (by rfl) ⟨1147793, by rfl⟩ : syracuseStep 1530391 = 2295587) B2295587
theorem B4356659 : Blo 1358498 4356659 := bstep (se 1 (by rfl) ⟨3267494, by rfl⟩ : syracuseStep 4356659 = 6534989) B6534989
theorem B3439169 : Blo 1358498 3439169 := bstep (se 2 (by rfl) ⟨1289688, by rfl⟩ : syracuseStep 3439169 = 2579377) B2579377
theorem B4135499 : Blo 1358498 4135499 := bstep (se 1 (by rfl) ⟨3101624, by rfl⟩ : syracuseStep 4135499 = 6203249) B6203249
theorem B2038361 : Blo 1358498 2038361 := bstep (se 2 (by rfl) ⟨764385, by rfl⟩ : syracuseStep 2038361 = 1528771) B1528771
theorem B8706653 : Blo 1358498 8706653 := bstep (se 3 (by rfl) ⟨1632497, by rfl⟩ : syracuseStep 8706653 = 3264995) B3264995
theorem B8264323 : Blo 1358498 8264323 := bstep (se 1 (by rfl) ⟨6198242, by rfl⟩ : syracuseStep 8264323 = 12396485) B12396485
theorem B1358507 : Blo 1358498 1358507 := bstep (se 1 (by rfl) ⟨1018880, by rfl⟩ : syracuseStep 1358507 = 2037761) B2037761
theorem B1358519 : Blo 1358498 1358519 := bstep (se 1 (by rfl) ⟨1018889, by rfl⟩ : syracuseStep 1358519 = 2037779) B2037779
theorem B1358539 : Blo 1358498 1358539 := bstep (se 1 (by rfl) ⟨1018904, by rfl⟩ : syracuseStep 1358539 = 2037809) B2037809
theorem B2038475 : Blo 1358498 2038475 := bstep (se 1 (by rfl) ⟨1528856, by rfl⟩ : syracuseStep 2038475 = 3057713) B3057713
theorem B44718797 : Blo 1358498 44718797 := bstep (se 3 (by rfl) ⟨8384774, by rfl⟩ : syracuseStep 44718797 = 16769549) B16769549
theorem B1358551 : Blo 1358498 1358551 := bstep (se 1 (by rfl) ⟨1018913, by rfl⟩ : syracuseStep 1358551 = 2037827) B2037827
theorem B2038487 : Blo 1358498 2038487 := bstep (se 1 (by rfl) ⟨1528865, by rfl⟩ : syracuseStep 2038487 = 3057731) B3057731
theorem B1358571 : Blo 1358498 1358571 := bstep (se 1 (by rfl) ⟨1018928, by rfl⟩ : syracuseStep 1358571 = 2037857) B2037857
theorem B1358583 : Blo 1358498 1358583 := bstep (se 1 (by rfl) ⟨1018937, by rfl⟩ : syracuseStep 1358583 = 2037875) B2037875
theorem B1358603 : Blo 1358498 1358603 := bstep (se 1 (by rfl) ⟨1018952, by rfl⟩ : syracuseStep 1358603 = 2037905) B2037905
theorem B1358615 : Blo 1358498 1358615 := bstep (se 1 (by rfl) ⟨1018961, by rfl⟩ : syracuseStep 1358615 = 2037923) B2037923
theorem B2038553 : Blo 1358498 2038553 := bstep (se 2 (by rfl) ⟨764457, by rfl⟩ : syracuseStep 2038553 = 1528915) B1528915
theorem B1358635 : Blo 1358498 1358635 := bstep (se 1 (by rfl) ⟨1018976, by rfl⟩ : syracuseStep 1358635 = 2037953) B2037953
theorem B11615021 : Blo 1358498 11615021 := bstep (se 3 (by rfl) ⟨2177816, by rfl⟩ : syracuseStep 11615021 = 4355633) B4355633
theorem B1358647 : Blo 1358498 1358647 := bstep (se 1 (by rfl) ⟨1018985, by rfl⟩ : syracuseStep 1358647 = 2037971) B2037971
theorem B1358667 : Blo 1358498 1358667 := bstep (se 1 (by rfl) ⟨1019000, by rfl⟩ : syracuseStep 1358667 = 2038001) B2038001
theorem B1358679 : Blo 1358498 1358679 := bstep (se 1 (by rfl) ⟨1019009, by rfl⟩ : syracuseStep 1358679 = 2038019) B2038019
theorem B1358699 : Blo 1358498 1358699 := bstep (se 1 (by rfl) ⟨1019024, by rfl⟩ : syracuseStep 1358699 = 2038049) B2038049
theorem B1358711 : Blo 1358498 1358711 := bstep (se 1 (by rfl) ⟨1019033, by rfl⟩ : syracuseStep 1358711 = 2038067) B2038067
theorem B2579339 : Blo 1358498 2579339 := bstep (se 1 (by rfl) ⟨1934504, by rfl⟩ : syracuseStep 2579339 = 3869009) B3869009
theorem B1358731 : Blo 1358498 1358731 := bstep (se 1 (by rfl) ⟨1019048, by rfl⟩ : syracuseStep 1358731 = 2038097) B2038097
theorem B2038667 : Blo 1358498 2038667 := bstep (se 1 (by rfl) ⟨1529000, by rfl⟩ : syracuseStep 2038667 = 3058001) B3058001
theorem B1358743 : Blo 1358498 1358743 := bstep (se 1 (by rfl) ⟨1019057, by rfl⟩ : syracuseStep 1358743 = 2038115) B2038115
theorem B2038679 : Blo 1358498 2038679 := bstep (se 1 (by rfl) ⟨1529009, by rfl⟩ : syracuseStep 2038679 = 3058019) B3058019
theorem B2177945 : Blo 1358498 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B1358763 : Blo 1358498 1358763 := bstep (se 1 (by rfl) ⟨1019072, by rfl⟩ : syracuseStep 1358763 = 2038145) B2038145
theorem B1358775 : Blo 1358498 1358775 := bstep (se 1 (by rfl) ⟨1019081, by rfl⟩ : syracuseStep 1358775 = 2038163) B2038163
theorem B1358795 : Blo 1358498 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B2448343 : Blo 1358498 2448343 := bstep (se 1 (by rfl) ⟨1836257, by rfl⟩ : syracuseStep 2448343 = 3672515) B3672515
theorem B7445465 : Blo 1358498 7445465 := bstep (se 2 (by rfl) ⟨2792049, by rfl⟩ : syracuseStep 7445465 = 5584099) B5584099
theorem B1358807 : Blo 1358498 1358807 := bstep (se 1 (by rfl) ⟨1019105, by rfl⟩ : syracuseStep 1358807 = 2038211) B2038211
theorem B2038745 : Blo 1358498 2038745 := bstep (se 2 (by rfl) ⟨764529, by rfl⟩ : syracuseStep 2038745 = 1529059) B1529059
theorem B1358827 : Blo 1358498 1358827 := bstep (se 1 (by rfl) ⟨1019120, by rfl⟩ : syracuseStep 1358827 = 2038241) B2038241
theorem B1358839 : Blo 1358498 1358839 := bstep (se 1 (by rfl) ⟨1019129, by rfl⟩ : syracuseStep 1358839 = 2038259) B2038259
theorem B1358859 : Blo 1358498 1358859 := bstep (se 1 (by rfl) ⟨1019144, by rfl⟩ : syracuseStep 1358859 = 2038289) B2038289
theorem B1358871 : Blo 1358498 1358871 := bstep (se 1 (by rfl) ⟨1019153, by rfl⟩ : syracuseStep 1358871 = 2038307) B2038307
theorem B3873815 : Blo 1358498 3873815 := bstep (se 1 (by rfl) ⟨2905361, by rfl⟩ : syracuseStep 3873815 = 5810723) B5810723
theorem B1358891 : Blo 1358498 1358891 := bstep (se 1 (by rfl) ⟨1019168, by rfl⟩ : syracuseStep 1358891 = 2038337) B2038337
theorem B6880301 : Blo 1358498 6880301 := bstep (se 3 (by rfl) ⟨1290056, by rfl⟩ : syracuseStep 6880301 = 2580113) B2580113
theorem B1358903 : Blo 1358498 1358903 := bstep (se 1 (by rfl) ⟨1019177, by rfl⟩ : syracuseStep 1358903 = 2038355) B2038355
theorem B2579521 : Blo 1358498 2579521 := bstep (se 2 (by rfl) ⟨967320, by rfl⟩ : syracuseStep 2579521 = 1934641) B1934641
theorem B1358923 : Blo 1358498 1358923 := bstep (se 1 (by rfl) ⟨1019192, by rfl⟩ : syracuseStep 1358923 = 2038385) B2038385
theorem B2038859 : Blo 1358498 2038859 := bstep (se 1 (by rfl) ⟨1529144, by rfl⟩ : syracuseStep 2038859 = 3058289) B3058289
theorem B1358935 : Blo 1358498 1358935 := bstep (se 1 (by rfl) ⟨1019201, by rfl⟩ : syracuseStep 1358935 = 2038403) B2038403
theorem B3439705 : Blo 1358498 3439705 := bstep (se 2 (by rfl) ⟨1289889, by rfl⟩ : syracuseStep 3439705 = 2579779) B2579779
theorem B2038871 : Blo 1358498 2038871 := bstep (se 1 (by rfl) ⟨1529153, by rfl⟩ : syracuseStep 2038871 = 3058307) B3058307
theorem B1358955 : Blo 1358498 1358955 := bstep (se 1 (by rfl) ⟨1019216, by rfl⟩ : syracuseStep 1358955 = 2038433) B2038433
theorem B1358967 : Blo 1358498 1358967 := bstep (se 1 (by rfl) ⟨1019225, by rfl⟩ : syracuseStep 1358967 = 2038451) B2038451
theorem B25476227 : Blo 1358498 25476227 := bstep (se 1 (by rfl) ⟨19107170, by rfl⟩ : syracuseStep 25476227 = 38214341) B38214341
theorem B1358987 : Blo 1358498 1358987 := bstep (se 1 (by rfl) ⟨1019240, by rfl⟩ : syracuseStep 1358987 = 2038481) B2038481
theorem B2292887 : Blo 1358498 2292887 := bstep (se 1 (by rfl) ⟨1719665, by rfl⟩ : syracuseStep 2292887 = 3439331) B3439331
theorem B1358999 : Blo 1358498 1358999 := bstep (se 1 (by rfl) ⟨1019249, by rfl⟩ : syracuseStep 1358999 = 2038499) B2038499
theorem B2038937 : Blo 1358498 2038937 := bstep (se 2 (by rfl) ⟨764601, by rfl⟩ : syracuseStep 2038937 = 1529203) B1529203
theorem B2325655 : Blo 1358498 2325655 := bstep (se 1 (by rfl) ⟨1744241, by rfl⟩ : syracuseStep 2325655 = 3488483) B3488483
theorem B1359019 : Blo 1358498 1359019 := bstep (se 1 (by rfl) ⟨1019264, by rfl⟩ : syracuseStep 1359019 = 2038529) B2038529
theorem B1359031 : Blo 1358498 1359031 := bstep (se 1 (by rfl) ⟨1019273, by rfl⟩ : syracuseStep 1359031 = 2038547) B2038547
theorem B1359051 : Blo 1358498 1359051 := bstep (se 1 (by rfl) ⟨1019288, by rfl⟩ : syracuseStep 1359051 = 2038577) B2038577
theorem B17431757 : Blo 1358498 17431757 := bstep (se 3 (by rfl) ⟨3268454, by rfl⟩ : syracuseStep 17431757 = 6536909) B6536909
theorem B1359063 : Blo 1358498 1359063 := bstep (se 1 (by rfl) ⟨1019297, by rfl⟩ : syracuseStep 1359063 = 2038595) B2038595
theorem B1359083 : Blo 1358498 1359083 := bstep (se 1 (by rfl) ⟨1019312, by rfl⟩ : syracuseStep 1359083 = 2038625) B2038625
theorem B1359095 : Blo 1358498 1359095 := bstep (se 1 (by rfl) ⟨1019321, by rfl⟩ : syracuseStep 1359095 = 2038643) B2038643
theorem B1359115 : Blo 1358498 1359115 := bstep (se 1 (by rfl) ⟨1019336, by rfl⟩ : syracuseStep 1359115 = 2038673) B2038673
theorem B2039051 : Blo 1358498 2039051 := bstep (se 1 (by rfl) ⟨1529288, by rfl⟩ : syracuseStep 2039051 = 3058577) B3058577
theorem B2293015 : Blo 1358498 2293015 := bstep (se 1 (by rfl) ⟨1719761, by rfl⟩ : syracuseStep 2293015 = 3439523) B3439523
theorem B1359127 : Blo 1358498 1359127 := bstep (se 1 (by rfl) ⟨1019345, by rfl⟩ : syracuseStep 1359127 = 2038691) B2038691
theorem B2039063 : Blo 1358498 2039063 := bstep (se 1 (by rfl) ⟨1529297, by rfl⟩ : syracuseStep 2039063 = 3058595) B3058595
theorem B1359147 : Blo 1358498 1359147 := bstep (se 1 (by rfl) ⟨1019360, by rfl⟩ : syracuseStep 1359147 = 2038721) B2038721
theorem B1359159 : Blo 1358498 1359159 := bstep (se 1 (by rfl) ⟨1019369, by rfl⟩ : syracuseStep 1359159 = 2038739) B2038739
theorem B5160257 : Blo 1358498 5160257 := bstep (se 2 (by rfl) ⟨1935096, by rfl⟩ : syracuseStep 5160257 = 3870193) B3870193
theorem B1359179 : Blo 1358498 1359179 := bstep (se 1 (by rfl) ⟨1019384, by rfl⟩ : syracuseStep 1359179 = 2038769) B2038769
theorem B1359191 : Blo 1358498 1359191 := bstep (se 1 (by rfl) ⟨1019393, by rfl⟩ : syracuseStep 1359191 = 2038787) B2038787
theorem B2039129 : Blo 1358498 2039129 := bstep (se 2 (by rfl) ⟨764673, by rfl⟩ : syracuseStep 2039129 = 1529347) B1529347
theorem B1359211 : Blo 1358498 1359211 := bstep (se 1 (by rfl) ⟨1019408, by rfl⟩ : syracuseStep 1359211 = 2038817) B2038817
theorem B1359223 : Blo 1358498 1359223 := bstep (se 1 (by rfl) ⟨1019417, by rfl⟩ : syracuseStep 1359223 = 2038835) B2038835
theorem B1359243 : Blo 1358498 1359243 := bstep (se 1 (by rfl) ⟨1019432, by rfl⟩ : syracuseStep 1359243 = 2038865) B2038865
theorem B2579863 : Blo 1358498 2579863 := bstep (se 1 (by rfl) ⟨1934897, by rfl⟩ : syracuseStep 2579863 = 3869795) B3869795
theorem B1359255 : Blo 1358498 1359255 := bstep (se 1 (by rfl) ⟨1019441, by rfl⟩ : syracuseStep 1359255 = 2038883) B2038883
theorem B2178457 : Blo 1358498 2178457 := bstep (se 2 (by rfl) ⟨816921, by rfl⟩ : syracuseStep 2178457 = 1633843) B1633843
theorem B1359275 : Blo 1358498 1359275 := bstep (se 1 (by rfl) ⟨1019456, by rfl⟩ : syracuseStep 1359275 = 2038913) B2038913
theorem B1359287 : Blo 1358498 1359287 := bstep (se 1 (by rfl) ⟨1019465, by rfl⟩ : syracuseStep 1359287 = 2038931) B2038931
theorem B1359307 : Blo 1358498 1359307 := bstep (se 1 (by rfl) ⟨1019480, by rfl⟩ : syracuseStep 1359307 = 2038961) B2038961
theorem B2039243 : Blo 1358498 2039243 := bstep (se 1 (by rfl) ⟨1529432, by rfl⟩ : syracuseStep 2039243 = 3058865) B3058865
theorem B1359319 : Blo 1358498 1359319 := bstep (se 1 (by rfl) ⟨1019489, by rfl⟩ : syracuseStep 1359319 = 2038979) B2038979
theorem B2039255 : Blo 1358498 2039255 := bstep (se 1 (by rfl) ⟨1529441, by rfl⟩ : syracuseStep 2039255 = 3058883) B3058883
theorem B1359339 : Blo 1358498 1359339 := bstep (se 1 (by rfl) ⟨1019504, by rfl⟩ : syracuseStep 1359339 = 2039009) B2039009
theorem B1359351 : Blo 1358498 1359351 := bstep (se 1 (by rfl) ⟨1019513, by rfl⟩ : syracuseStep 1359351 = 2039027) B2039027
theorem B1359371 : Blo 1358498 1359371 := bstep (se 1 (by rfl) ⟨1019528, by rfl⟩ : syracuseStep 1359371 = 2039057) B2039057
theorem B6528529 : Blo 1358498 6528529 := bstep (se 2 (by rfl) ⟨2448198, by rfl⟩ : syracuseStep 6528529 = 4896397) B4896397
theorem B2448919 : Blo 1358498 2448919 := bstep (se 1 (by rfl) ⟨1836689, by rfl⟩ : syracuseStep 2448919 = 3673379) B3673379
theorem B1359383 : Blo 1358498 1359383 := bstep (se 1 (by rfl) ⟨1019537, by rfl⟩ : syracuseStep 1359383 = 2039075) B2039075
theorem B2039321 : Blo 1358498 2039321 := bstep (se 2 (by rfl) ⟨764745, by rfl⟩ : syracuseStep 2039321 = 1529491) B1529491
theorem B1359403 : Blo 1358498 1359403 := bstep (se 1 (by rfl) ⟨1019552, by rfl⟩ : syracuseStep 1359403 = 2039105) B2039105
theorem B6626861 : Blo 1358498 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B1359415 : Blo 1358498 1359415 := bstep (se 1 (by rfl) ⟨1019561, by rfl⟩ : syracuseStep 1359415 = 2039123) B2039123
theorem B1719883 : Blo 1358498 1719883 := bstep (se 1 (by rfl) ⟨1289912, by rfl⟩ : syracuseStep 1719883 = 2579825) B2579825
theorem B2448971 : Blo 1358498 2448971 := bstep (se 1 (by rfl) ⟨1836728, by rfl⟩ : syracuseStep 2448971 = 3673457) B3673457
theorem B4587083 : Blo 1358498 4587083 := bstep (se 1 (by rfl) ⟨3440312, by rfl⟩ : syracuseStep 4587083 = 6880625) B6880625
theorem B1359435 : Blo 1358498 1359435 := bstep (se 1 (by rfl) ⟨1019576, by rfl⟩ : syracuseStep 1359435 = 2039153) B2039153
theorem B1359447 : Blo 1358498 1359447 := bstep (se 1 (by rfl) ⟨1019585, by rfl⟩ : syracuseStep 1359447 = 2039171) B2039171
theorem B6528605 : Blo 1358498 6528605 := bstep (se 3 (by rfl) ⟨1224113, by rfl⟩ : syracuseStep 6528605 = 2448227) B2448227
theorem B1359467 : Blo 1358498 1359467 := bstep (se 1 (by rfl) ⟨1019600, by rfl⟩ : syracuseStep 1359467 = 2039201) B2039201
theorem B2580083 : Blo 1358498 2580083 := bstep (se 1 (by rfl) ⟨1935062, by rfl⟩ : syracuseStep 2580083 = 3870125) B3870125
theorem B1359479 : Blo 1358498 1359479 := bstep (se 1 (by rfl) ⟨1019609, by rfl⟩ : syracuseStep 1359479 = 2039219) B2039219
theorem B1359499 : Blo 1358498 1359499 := bstep (se 1 (by rfl) ⟨1019624, by rfl⟩ : syracuseStep 1359499 = 2039249) B2039249
theorem B2039435 : Blo 1358498 2039435 := bstep (se 1 (by rfl) ⟨1529576, by rfl⟩ : syracuseStep 2039435 = 3059153) B3059153
theorem B1359511 : Blo 1358498 1359511 := bstep (se 1 (by rfl) ⟨1019633, by rfl⟩ : syracuseStep 1359511 = 2039267) B2039267
theorem B2039447 : Blo 1358498 2039447 := bstep (se 1 (by rfl) ⟨1529585, by rfl⟩ : syracuseStep 2039447 = 3059171) B3059171
theorem B1359531 : Blo 1358498 1359531 := bstep (se 1 (by rfl) ⟨1019648, by rfl⟩ : syracuseStep 1359531 = 2039297) B2039297
theorem B1359543 : Blo 1358498 1359543 := bstep (se 1 (by rfl) ⟨1019657, by rfl⟩ : syracuseStep 1359543 = 2039315) B2039315
theorem B1359563 : Blo 1358498 1359563 := bstep (se 1 (by rfl) ⟨1019672, by rfl⟩ : syracuseStep 1359563 = 2039345) B2039345
theorem B1359575 : Blo 1358498 1359575 := bstep (se 1 (by rfl) ⟨1019681, by rfl⟩ : syracuseStep 1359575 = 2039363) B2039363
theorem B2039513 : Blo 1358498 2039513 := bstep (se 2 (by rfl) ⟨764817, by rfl⟩ : syracuseStep 2039513 = 1529635) B1529635
theorem B1359595 : Blo 1358498 1359595 := bstep (se 1 (by rfl) ⟨1019696, by rfl⟩ : syracuseStep 1359595 = 2039393) B2039393
theorem B1359607 : Blo 1358498 1359607 := bstep (se 1 (by rfl) ⟨1019705, by rfl⟩ : syracuseStep 1359607 = 2039411) B2039411
theorem B1359627 : Blo 1358498 1359627 := bstep (se 1 (by rfl) ⟨1019720, by rfl⟩ : syracuseStep 1359627 = 2039441) B2039441
theorem B1359639 : Blo 1358498 1359639 := bstep (se 1 (by rfl) ⟨1019729, by rfl⟩ : syracuseStep 1359639 = 2039459) B2039459
theorem B1359659 : Blo 1358498 1359659 := bstep (se 1 (by rfl) ⟨1019744, by rfl⟩ : syracuseStep 1359659 = 2039489) B2039489
theorem B7348013 : Blo 1358498 7348013 := bstep (se 3 (by rfl) ⟨1377752, by rfl⟩ : syracuseStep 7348013 = 2755505) B2755505
theorem B1359671 : Blo 1358498 1359671 := bstep (se 1 (by rfl) ⟨1019753, by rfl⟩ : syracuseStep 1359671 = 2039507) B2039507
theorem B1359691 : Blo 1358498 1359691 := bstep (se 1 (by rfl) ⟨1019768, by rfl⟩ : syracuseStep 1359691 = 2039537) B2039537
theorem B2039627 : Blo 1358498 2039627 := bstep (se 1 (by rfl) ⟨1529720, by rfl⟩ : syracuseStep 2039627 = 3059441) B3059441
theorem B2580311 : Blo 1358498 2580311 := bstep (se 1 (by rfl) ⟨1935233, by rfl⟩ : syracuseStep 2580311 = 3870467) B3870467
theorem B4587353 : Blo 1358498 4587353 := bstep (se 2 (by rfl) ⟨1720257, by rfl⟩ : syracuseStep 4587353 = 3440515) B3440515
theorem B1359703 : Blo 1358498 1359703 := bstep (se 1 (by rfl) ⟨1019777, by rfl⟩ : syracuseStep 1359703 = 2039555) B2039555
theorem B2039639 : Blo 1358498 2039639 := bstep (se 1 (by rfl) ⟨1529729, by rfl⟩ : syracuseStep 2039639 = 3059459) B3059459
theorem B1359723 : Blo 1358498 1359723 := bstep (se 1 (by rfl) ⟨1019792, by rfl⟩ : syracuseStep 1359723 = 2039585) B2039585
theorem B1359735 : Blo 1358498 1359735 := bstep (se 1 (by rfl) ⟨1019801, by rfl⟩ : syracuseStep 1359735 = 2039603) B2039603
theorem B2293643 : Blo 1358498 2293643 := bstep (se 1 (by rfl) ⟨1720232, by rfl⟩ : syracuseStep 2293643 = 3440465) B3440465
theorem B1359755 : Blo 1358498 1359755 := bstep (se 1 (by rfl) ⟨1019816, by rfl⟩ : syracuseStep 1359755 = 2039633) B2039633
theorem B1359767 : Blo 1358498 1359767 := bstep (se 1 (by rfl) ⟨1019825, by rfl⟩ : syracuseStep 1359767 = 2039651) B2039651
theorem B2039705 : Blo 1358498 2039705 := bstep (se 2 (by rfl) ⟨764889, by rfl⟩ : syracuseStep 2039705 = 1529779) B1529779
theorem B1359787 : Blo 1358498 1359787 := bstep (se 1 (by rfl) ⟨1019840, by rfl⟩ : syracuseStep 1359787 = 2039681) B2039681
theorem B1359799 : Blo 1358498 1359799 := bstep (se 1 (by rfl) ⟨1019849, by rfl⟩ : syracuseStep 1359799 = 2039699) B2039699
theorem B1359819 : Blo 1358498 1359819 := bstep (se 1 (by rfl) ⟨1019864, by rfl⟩ : syracuseStep 1359819 = 2039729) B2039729
theorem B1359831 : Blo 1358498 1359831 := bstep (se 1 (by rfl) ⟨1019873, by rfl⟩ : syracuseStep 1359831 = 2039747) B2039747
theorem B1359851 : Blo 1358498 1359851 := bstep (se 1 (by rfl) ⟨1019888, by rfl⟩ : syracuseStep 1359851 = 2039777) B2039777
theorem B1359879 : Blo 1358498 1359879 := bstep (se 1 (by rfl) ⟨1019909, by rfl⟩ : syracuseStep 1359879 = 2039819) B2039819
theorem B1359887 : Blo 1358498 1359887 := bstep (se 1 (by rfl) ⟨1019915, by rfl⟩ : syracuseStep 1359887 = 2039831) B2039831
theorem B1720379 : Blo 1358498 1720379 := bstep (se 1 (by rfl) ⟨1290284, by rfl⟩ : syracuseStep 1720379 = 2580569) B2580569
theorem B2039867 : Blo 1358498 2039867 := bstep (se 1 (by rfl) ⟨1529900, by rfl⟩ : syracuseStep 2039867 = 3059801) B3059801
theorem B1359931 : Blo 1358498 1359931 := bstep (se 1 (by rfl) ⟨1019948, by rfl⟩ : syracuseStep 1359931 = 2039897) B2039897
theorem B12410941 : Blo 1358498 12410941 := bstep (se 3 (by rfl) ⟨2327051, by rfl⟩ : syracuseStep 12410941 = 4654103) B4654103
theorem B2580599 : Blo 1358498 2580599 := bstep (se 1 (by rfl) ⟨1935449, by rfl⟩ : syracuseStep 2580599 = 3870899) B3870899
theorem B2293879 : Blo 1358498 2293879 := bstep (se 1 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 2293879 = 3440819) B3440819
theorem B2039927 : Blo 1358498 2039927 := bstep (se 1 (by rfl) ⟨1529945, by rfl⟩ : syracuseStep 2039927 = 3059891) B3059891
theorem B1360007 : Blo 1358498 1360007 := bstep (se 1 (by rfl) ⟨1020005, by rfl⟩ : syracuseStep 1360007 = 2040011) B2040011
theorem B2039951 : Blo 1358498 2039951 := bstep (se 1 (by rfl) ⟨1529963, by rfl⟩ : syracuseStep 2039951 = 3059927) B3059927
theorem B1360015 : Blo 1358498 1360015 := bstep (se 1 (by rfl) ⟨1020011, by rfl⟩ : syracuseStep 1360015 = 2040023) B2040023
theorem B8708269 : Blo 1358498 8708269 := bstep (se 3 (by rfl) ⟨1632800, by rfl⟩ : syracuseStep 8708269 = 3265601) B3265601
theorem B2039993 : Blo 1358498 2039993 := bstep (se 2 (by rfl) ⟨764997, by rfl⟩ : syracuseStep 2039993 = 1529995) B1529995
theorem B1360059 : Blo 1358498 1360059 := bstep (se 1 (by rfl) ⟨1020044, by rfl⟩ : syracuseStep 1360059 = 2040089) B2040089
theorem B2040071 : Blo 1358498 2040071 := bstep (se 1 (by rfl) ⟨1530053, by rfl⟩ : syracuseStep 2040071 = 3060107) B3060107
theorem B1360135 : Blo 1358498 1360135 := bstep (se 1 (by rfl) ⟨1020101, by rfl⟩ : syracuseStep 1360135 = 2040203) B2040203
theorem B2580751 : Blo 1358498 2580751 := bstep (se 1 (by rfl) ⟨1935563, by rfl⟩ : syracuseStep 2580751 = 3871127) B3871127
theorem B1360143 : Blo 1358498 1360143 := bstep (se 1 (by rfl) ⟨1020107, by rfl⟩ : syracuseStep 1360143 = 2040215) B2040215
theorem B2040107 : Blo 1358498 2040107 := bstep (se 1 (by rfl) ⟨1530080, by rfl⟩ : syracuseStep 2040107 = 3060161) B3060161
theorem B2294075 : Blo 1358498 2294075 := bstep (se 1 (by rfl) ⟨1720556, by rfl⟩ : syracuseStep 2294075 = 3441113) B3441113
theorem B1360187 : Blo 1358498 1360187 := bstep (se 1 (by rfl) ⟨1020140, by rfl⟩ : syracuseStep 1360187 = 2040281) B2040281
theorem B2040137 : Blo 1358498 2040137 := bstep (se 2 (by rfl) ⟨765051, by rfl⟩ : syracuseStep 2040137 = 1530103) B1530103
theorem B1360263 : Blo 1358498 1360263 := bstep (se 1 (by rfl) ⟨1020197, by rfl⟩ : syracuseStep 1360263 = 2040395) B2040395
theorem B1360271 : Blo 1358498 1360271 := bstep (se 1 (by rfl) ⟨1020203, by rfl⟩ : syracuseStep 1360271 = 2040407) B2040407
theorem B2040251 : Blo 1358498 2040251 := bstep (se 1 (by rfl) ⟨1530188, by rfl⟩ : syracuseStep 2040251 = 3060377) B3060377
theorem B1360315 : Blo 1358498 1360315 := bstep (se 1 (by rfl) ⟨1020236, by rfl⟩ : syracuseStep 1360315 = 2040473) B2040473
theorem B2040311 : Blo 1358498 2040311 := bstep (se 1 (by rfl) ⟨1530233, by rfl⟩ : syracuseStep 2040311 = 3060467) B3060467
theorem B1360391 : Blo 1358498 1360391 := bstep (se 1 (by rfl) ⟨1020293, by rfl⟩ : syracuseStep 1360391 = 2040587) B2040587
theorem B3441163 : Blo 1358498 3441163 := bstep (se 1 (by rfl) ⟨2580872, by rfl⟩ : syracuseStep 3441163 = 5161745) B5161745
theorem B2040335 : Blo 1358498 2040335 := bstep (se 1 (by rfl) ⟨1530251, by rfl⟩ : syracuseStep 2040335 = 3060503) B3060503
theorem B1360399 : Blo 1358498 1360399 := bstep (se 1 (by rfl) ⟨1020299, by rfl⟩ : syracuseStep 1360399 = 2040599) B2040599
theorem B11616797 : Blo 1358498 11616797 := bstep (se 3 (by rfl) ⟨2178149, by rfl⟩ : syracuseStep 11616797 = 4356299) B4356299
theorem B3267955 : Blo 1358498 3267955 := bstep (se 1 (by rfl) ⟨2450966, by rfl⟩ : syracuseStep 3267955 = 4901933) B4901933
theorem B2040377 : Blo 1358498 2040377 := bstep (se 2 (by rfl) ⟨765141, by rfl⟩ : syracuseStep 2040377 = 1530283) B1530283
theorem B1360443 : Blo 1358498 1360443 := bstep (se 1 (by rfl) ⟨1020332, by rfl⟩ : syracuseStep 1360443 = 2040665) B2040665
theorem B7848535 : Blo 1358498 7848535 := bstep (se 1 (by rfl) ⟨5886401, by rfl⟩ : syracuseStep 7848535 = 11772803) B11772803
theorem B2040455 : Blo 1358498 2040455 := bstep (se 1 (by rfl) ⟨1530341, by rfl⟩ : syracuseStep 2040455 = 3060683) B3060683
theorem B2581139 : Blo 1358498 2581139 := bstep (se 1 (by rfl) ⟨1935854, by rfl⟩ : syracuseStep 2581139 = 3871709) B3871709
theorem B3441305 : Blo 1358498 3441305 := bstep (se 2 (by rfl) ⟨1290489, by rfl⟩ : syracuseStep 3441305 = 2580979) B2580979
theorem B2040491 : Blo 1358498 2040491 := bstep (se 1 (by rfl) ⟨1530368, by rfl⟩ : syracuseStep 2040491 = 3060737) B3060737
theorem B52363957 : Blo 1358498 52363957 := bstep (se 5 (by rfl) ⟨2454560, by rfl⟩ : syracuseStep 52363957 = 4909121) B4909121
theorem B2294473 : Blo 1358498 2294473 := bstep (se 2 (by rfl) ⟨860427, by rfl⟩ : syracuseStep 2294473 = 1720855) B1720855
theorem B2040521 : Blo 1358498 2040521 := bstep (se 2 (by rfl) ⟨765195, by rfl⟩ : syracuseStep 2040521 = 1530391) B1530391
theorem B4899599 : Blo 1358498 4899599 := bstep (se 1 (by rfl) ⟨3674699, by rfl⟩ : syracuseStep 4899599 = 7349399) B7349399
theorem B148882211 : Blo 1358498 148882211 := bstep (se 1 (by rfl) ⟨111661658, by rfl⟩ : syracuseStep 148882211 = 223323317) B223323317
theorem B3441467 : Blo 1358498 3441467 := bstep (se 1 (by rfl) ⟨2581100, by rfl⟩ : syracuseStep 3441467 = 5162201) B5162201
theorem B4653883 : Blo 1358498 4653883 := bstep (se 1 (by rfl) ⟨3490412, by rfl⟩ : syracuseStep 4653883 = 6980825) B6980825
theorem B2040635 : Blo 1358498 2040635 := bstep (se 1 (by rfl) ⟨1530476, by rfl⟩ : syracuseStep 2040635 = 3060953) B3060953
theorem B11019097 : Blo 1358498 11019097 := bstep (se 2 (by rfl) ⟨4132161, by rfl⟩ : syracuseStep 11019097 = 8264323) B8264323
theorem B2040695 : Blo 1358498 2040695 := bstep (se 1 (by rfl) ⟨1530521, by rfl⟩ : syracuseStep 2040695 = 3061043) B3061043
theorem B2040719 : Blo 1358498 2040719 := bstep (se 1 (by rfl) ⟨1530539, by rfl⟩ : syracuseStep 2040719 = 3061079) B3061079
theorem B5161913 : Blo 1358498 5161913 := bstep (se 2 (by rfl) ⟨1935717, by rfl⟩ : syracuseStep 5161913 = 3871435) B3871435
theorem B1721351 : Blo 1358498 1721351 := bstep (se 1 (by rfl) ⟨1291013, by rfl⟩ : syracuseStep 1721351 = 2582027) B2582027
theorem B3056759 : Blo 1358498 3056759 := bstep (se 1 (by rfl) ⟨2292569, by rfl⟩ : syracuseStep 3056759 = 4585139) B4585139
theorem B1451143 : Blo 1358498 1451143 := bstep (se 1 (by rfl) ⟨1088357, by rfl⟩ : syracuseStep 1451143 = 2176715) B2176715
theorem B3441811 : Blo 1358498 3441811 := bstep (se 1 (by rfl) ⟨2581358, by rfl⟩ : syracuseStep 3441811 = 5162717) B5162717
theorem B9299117 : Blo 1358498 9299117 := bstep (se 3 (by rfl) ⟨1743584, by rfl⟩ : syracuseStep 9299117 = 3487169) B3487169
theorem B3441953 : Blo 1358498 3441953 := bstep (se 2 (by rfl) ⟨1290732, by rfl⟩ : syracuseStep 3441953 = 2581465) B2581465
theorem B3056939 : Blo 1358498 3056939 := bstep (se 1 (by rfl) ⟨2292704, by rfl⟩ : syracuseStep 3056939 = 4585409) B4585409
theorem B2295175 : Blo 1358498 2295175 := bstep (se 1 (by rfl) ⟨1721381, by rfl⟩ : syracuseStep 2295175 = 3442763) B3442763
theorem B17409613 : Blo 1358498 17409613 := bstep (se 3 (by rfl) ⟨3264302, by rfl⟩ : syracuseStep 17409613 = 6528605) B6528605
theorem B5809751 : Blo 1358498 5809751 := bstep (se 1 (by rfl) ⟨4357313, by rfl⟩ : syracuseStep 5809751 = 8714627) B8714627
theorem B3057299 : Blo 1358498 3057299 := bstep (se 1 (by rfl) ⟨2292974, by rfl⟩ : syracuseStep 3057299 = 4585949) B4585949
theorem B8267437 : Blo 1358498 8267437 := bstep (se 3 (by rfl) ⟨1550144, by rfl⟩ : syracuseStep 8267437 = 3100289) B3100289
theorem B3057353 : Blo 1358498 3057353 := bstep (se 2 (by rfl) ⟨1146507, by rfl⟩ : syracuseStep 3057353 = 2293015) B2293015
theorem B29812531 : Blo 1358498 29812531 := bstep (se 1 (by rfl) ⟨22359398, by rfl⟩ : syracuseStep 29812531 = 44718797) B44718797
theorem B7743347 : Blo 1358498 7743347 := bstep (se 1 (by rfl) ⟨5807510, by rfl⟩ : syracuseStep 7743347 = 11615021) B11615021
theorem B6883217 : Blo 1358498 6883217 := bstep (se 2 (by rfl) ⟨2581206, by rfl⟩ : syracuseStep 6883217 = 5162413) B5162413
theorem B5162899 : Blo 1358498 5162899 := bstep (se 1 (by rfl) ⟨3872174, by rfl⟩ : syracuseStep 5162899 = 7744349) B7744349
theorem B4589459 : Blo 1358498 4589459 := bstep (se 1 (by rfl) ⟨3442094, by rfl⟩ : syracuseStep 4589459 = 6884189) B6884189
theorem B1451963 : Blo 1358498 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B2066447 : Blo 1358498 2066447 := bstep (se 1 (by rfl) ⟨1549835, by rfl⟩ : syracuseStep 2066447 = 3099671) B3099671
theorem B2582543 : Blo 1358498 2582543 := bstep (se 1 (by rfl) ⟨1936907, by rfl⟩ : syracuseStep 2582543 = 3873815) B3873815
theorem B2295823 : Blo 1358498 2295823 := bstep (se 1 (by rfl) ⟨1721867, by rfl⟩ : syracuseStep 2295823 = 3443735) B3443735
theorem B5589059 : Blo 1358498 5589059 := bstep (se 1 (by rfl) ⟨4191794, by rfl⟩ : syracuseStep 5589059 = 8383589) B8383589
theorem B16984151 : Blo 1358498 16984151 := bstep (se 1 (by rfl) ⟨12738113, by rfl⟩ : syracuseStep 16984151 = 25476227) B25476227
theorem B11618437 : Blo 1358498 11618437 := bstep (se 4 (by rfl) ⟨1089228, by rfl⟩ : syracuseStep 11618437 = 2178457) B2178457
theorem B3442945 : Blo 1358498 3442945 := bstep (se 2 (by rfl) ⟨1291104, by rfl⟩ : syracuseStep 3442945 = 2582209) B2582209
theorem B4417907 : Blo 1358498 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B1632647 : Blo 1358498 1632647 := bstep (se 1 (by rfl) ⟨1224485, by rfl⟩ : syracuseStep 1632647 = 2448971) B2448971
theorem B3058055 : Blo 1358498 3058055 := bstep (se 1 (by rfl) ⟨2293541, by rfl⟩ : syracuseStep 3058055 = 4587083) B4587083
theorem B3058235 : Blo 1358498 3058235 := bstep (se 1 (by rfl) ⟨2293676, by rfl⟩ : syracuseStep 3058235 = 4587353) B4587353
theorem B13060673 : Blo 1358498 13060673 := bstep (se 2 (by rfl) ⟨4897752, by rfl⟩ : syracuseStep 13060673 = 9795505) B9795505
theorem B15698497 : Blo 1358498 15698497 := bstep (se 2 (by rfl) ⟨5886936, by rfl⟩ : syracuseStep 15698497 = 11773873) B11773873
theorem B1935991 : Blo 1358498 1935991 := bstep (se 1 (by rfl) ⟨1451993, by rfl⟩ : syracuseStep 1935991 = 2903987) B2903987
theorem B3058361 : Blo 1358498 3058361 := bstep (se 2 (by rfl) ⟨1146885, by rfl⟩ : syracuseStep 3058361 = 2293771) B2293771
theorem B1632955 : Blo 1358498 1632955 := bstep (se 1 (by rfl) ⟨1224716, by rfl⟩ : syracuseStep 1632955 = 2449433) B2449433
theorem B3869441 : Blo 1358498 3869441 := bstep (se 2 (by rfl) ⟨1451040, by rfl⟩ : syracuseStep 3869441 = 2902081) B2902081
theorem B4901633 : Blo 1358498 4901633 := bstep (se 2 (by rfl) ⟨1838112, by rfl⟩ : syracuseStep 4901633 = 3676225) B3676225
theorem B2902799 : Blo 1358498 2902799 := bstep (se 1 (by rfl) ⟨2177099, by rfl⟩ : syracuseStep 2902799 = 4354199) B4354199
theorem B13060901 : Blo 1358498 13060901 := bstep (se 4 (by rfl) ⟨1224459, by rfl⟩ : syracuseStep 13060901 = 2448919) B2448919
theorem B3443543 : Blo 1358498 3443543 := bstep (se 1 (by rfl) ⟨2582657, by rfl⟩ : syracuseStep 3443543 = 5165315) B5165315
theorem B18590579 : Blo 1358498 18590579 := bstep (se 1 (by rfl) ⟨13942934, by rfl⟩ : syracuseStep 18590579 = 27885869) B27885869
theorem B2902969 : Blo 1358498 2902969 := bstep (se 2 (by rfl) ⟨1088613, by rfl⟩ : syracuseStep 2902969 = 2177227) B2177227
theorem B1936315 : Blo 1358498 1936315 := bstep (se 1 (by rfl) ⟨1452236, by rfl⟩ : syracuseStep 1936315 = 2904473) B2904473
theorem B3058703 : Blo 1358498 3058703 := bstep (se 1 (by rfl) ⟨2294027, by rfl⟩ : syracuseStep 3058703 = 4588055) B4588055
theorem B3058721 : Blo 1358498 3058721 := bstep (se 2 (by rfl) ⟨1147020, by rfl⟩ : syracuseStep 3058721 = 2294041) B2294041
theorem B3443755 : Blo 1358498 3443755 := bstep (se 1 (by rfl) ⟨2582816, by rfl⟩ : syracuseStep 3443755 = 5165633) B5165633
theorem B5508157 : Blo 1358498 5508157 := bstep (se 3 (by rfl) ⟨1032779, by rfl⟩ : syracuseStep 5508157 = 2065559) B2065559
theorem B62786765 : Blo 1358498 62786765 := bstep (se 3 (by rfl) ⟨11772518, by rfl⟩ : syracuseStep 62786765 = 23545037) B23545037
theorem B2903311 : Blo 1358498 2903311 := bstep (se 1 (by rfl) ⟨2177483, by rfl⟩ : syracuseStep 2903311 = 4354967) B4354967
theorem B4590863 : Blo 1358498 4590863 := bstep (se 1 (by rfl) ⟨3443147, by rfl⟩ : syracuseStep 4590863 = 6886295) B6886295
theorem B3722525 : Blo 1358498 3722525 := bstep (se 3 (by rfl) ⟨697973, by rfl⟩ : syracuseStep 3722525 = 1395947) B1395947
theorem B7744805 : Blo 1358498 7744805 := bstep (se 4 (by rfl) ⟨726075, by rfl⟩ : syracuseStep 7744805 = 1452151) B1452151
theorem B3870011 : Blo 1358498 3870011 := bstep (se 1 (by rfl) ⟨2902508, by rfl⟩ : syracuseStep 3870011 = 5805017) B5805017
theorem B3059063 : Blo 1358498 3059063 := bstep (se 1 (by rfl) ⟨2294297, by rfl⟩ : syracuseStep 3059063 = 4588595) B4588595
theorem B5508499 : Blo 1358498 5508499 := bstep (se 1 (by rfl) ⟨4131374, by rfl⟩ : syracuseStep 5508499 = 8262749) B8262749
theorem B1936811 : Blo 1358498 1936811 := bstep (se 1 (by rfl) ⟨1452608, by rfl⟩ : syracuseStep 1936811 = 2905217) B2905217
theorem B4591133 : Blo 1358498 4591133 := bstep (se 3 (by rfl) ⟨860837, by rfl⟩ : syracuseStep 4591133 = 1721675) B1721675
theorem B3870251 : Blo 1358498 3870251 := bstep (se 1 (by rfl) ⟨2902688, by rfl⟩ : syracuseStep 3870251 = 5805377) B5805377
theorem B3059243 : Blo 1358498 3059243 := bstep (se 1 (by rfl) ⟨2294432, by rfl⟩ : syracuseStep 3059243 = 4588865) B4588865
theorem B5164631 : Blo 1358498 5164631 := bstep (se 1 (by rfl) ⟨3873473, by rfl⟩ : syracuseStep 5164631 = 7746947) B7746947
theorem B3059603 : Blo 1358498 3059603 := bstep (se 1 (by rfl) ⟨2294702, by rfl⟩ : syracuseStep 3059603 = 4589405) B4589405
theorem B7737241 : Blo 1358498 7737241 := bstep (se 2 (by rfl) ⟨2901465, by rfl⟩ : syracuseStep 7737241 = 5802931) B5802931
theorem B3264457 : Blo 1358498 3264457 := bstep (se 2 (by rfl) ⟨1224171, by rfl⟩ : syracuseStep 3264457 = 2448343) B2448343
theorem B3059657 : Blo 1358498 3059657 := bstep (se 2 (by rfl) ⟨1147371, by rfl⟩ : syracuseStep 3059657 = 2294743) B2294743
theorem B6885323 : Blo 1358498 6885323 := bstep (se 1 (by rfl) ⟨5163992, by rfl⟩ : syracuseStep 6885323 = 10327985) B10327985
theorem B7745489 : Blo 1358498 7745489 := bstep (se 2 (by rfl) ⟨2904558, by rfl⟩ : syracuseStep 7745489 = 5809117) B5809117
theorem B5165117 : Blo 1358498 5165117 := bstep (se 3 (by rfl) ⟨968459, by rfl⟩ : syracuseStep 5165117 = 1936919) B1936919
theorem B4354249 : Blo 1358498 4354249 := bstep (se 2 (by rfl) ⟨1632843, by rfl⟩ : syracuseStep 4354249 = 3265687) B3265687
theorem B3100873 : Blo 1358498 3100873 := bstep (se 2 (by rfl) ⟨1162827, by rfl⟩ : syracuseStep 3100873 = 2325655) B2325655
theorem B4649231 : Blo 1358498 4649231 := bstep (se 1 (by rfl) ⟨3486923, by rfl⟩ : syracuseStep 4649231 = 6973847) B6973847
theorem B7745807 : Blo 1358498 7745807 := bstep (se 1 (by rfl) ⟨5809355, by rfl⟩ : syracuseStep 7745807 = 11618711) B11618711
theorem B6885647 : Blo 1358498 6885647 := bstep (se 1 (by rfl) ⟨5164235, by rfl⟩ : syracuseStep 6885647 = 10328471) B10328471
theorem B2904439 : Blo 1358498 2904439 := bstep (se 1 (by rfl) ⟨2178329, by rfl⟩ : syracuseStep 2904439 = 4356659) B4356659
theorem B2756999 : Blo 1358498 2756999 := bstep (se 1 (by rfl) ⟨2067749, by rfl⟩ : syracuseStep 2756999 = 4135499) B4135499
theorem B5804435 : Blo 1358498 5804435 := bstep (se 1 (by rfl) ⟨4353326, by rfl⟩ : syracuseStep 5804435 = 8706653) B8706653
theorem B10318265 : Blo 1358498 10318265 := bstep (se 2 (by rfl) ⟨3869349, by rfl⟩ : syracuseStep 10318265 = 7738699) B7738699
theorem B59609621 : Blo 1358498 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B3060359 : Blo 1358498 3060359 := bstep (se 1 (by rfl) ⟨2295269, by rfl⟩ : syracuseStep 3060359 = 4590539) B4590539
theorem B8704705 : Blo 1358498 8704705 := bstep (se 2 (by rfl) ⟨3264264, by rfl⟩ : syracuseStep 8704705 = 6528529) B6528529
theorem B1528591 : Blo 1358498 1528591 := bstep (se 1 (by rfl) ⟨1146443, by rfl⟩ : syracuseStep 1528591 = 2292887) B2292887
theorem B7353139 : Blo 1358498 7353139 := bstep (se 1 (by rfl) ⟨5514854, by rfl⟩ : syracuseStep 7353139 = 11029709) B11029709
theorem B11621171 : Blo 1358498 11621171 := bstep (se 1 (by rfl) ⟨8715878, by rfl⟩ : syracuseStep 11621171 = 17431757) B17431757
theorem B3060539 : Blo 1358498 3060539 := bstep (se 1 (by rfl) ⟨2295404, by rfl⟩ : syracuseStep 3060539 = 4590809) B4590809
theorem B3060665 : Blo 1358498 3060665 := bstep (se 2 (by rfl) ⟨1147749, by rfl⟩ : syracuseStep 3060665 = 2295499) B2295499
theorem B8066249 : Blo 1358498 8066249 := bstep (se 2 (by rfl) ⟨3024843, by rfl⟩ : syracuseStep 8066249 = 6049687) B6049687
theorem B1529095 : Blo 1358498 1529095 := bstep (se 1 (by rfl) ⟨1146821, by rfl⟩ : syracuseStep 1529095 = 2293643) B2293643
theorem B3061007 : Blo 1358498 3061007 := bstep (se 1 (by rfl) ⟨2295755, by rfl⟩ : syracuseStep 3061007 = 4591511) B4591511
theorem B3061025 : Blo 1358498 3061025 := bstep (se 2 (by rfl) ⟨1147884, by rfl⟩ : syracuseStep 3061025 = 2295769) B2295769
theorem B2651435 : Blo 1358498 2651435 := bstep (se 1 (by rfl) ⟨1988576, by rfl⟩ : syracuseStep 2651435 = 3977153) B3977153
theorem B1529275 : Blo 1358498 1529275 := bstep (se 1 (by rfl) ⟨1146956, by rfl⟩ : syracuseStep 1529275 = 2293913) B2293913
theorem B7747265 : Blo 1358498 7747265 := bstep (se 2 (by rfl) ⟨2905224, by rfl⟩ : syracuseStep 7747265 = 5810449) B5810449
theorem B6887105 : Blo 1358498 6887105 := bstep (se 2 (by rfl) ⟨2582664, by rfl⟩ : syracuseStep 6887105 = 5165329) B5165329
theorem B6534893 : Blo 1358498 6534893 := bstep (se 3 (by rfl) ⟨1225292, by rfl⟩ : syracuseStep 6534893 = 2450585) B2450585
theorem B4896571 : Blo 1358498 4896571 := bstep (se 1 (by rfl) ⟨3672428, by rfl⟩ : syracuseStep 4896571 = 7344857) B7344857
theorem B7739225 : Blo 1358498 7739225 := bstep (se 2 (by rfl) ⟨2902209, by rfl⟩ : syracuseStep 7739225 = 5804419) B5804419
theorem B26498933 : Blo 1358498 26498933 := bstep (se 5 (by rfl) ⟨1242137, by rfl⟩ : syracuseStep 26498933 = 2484275) B2484275
theorem B1529743 : Blo 1358498 1529743 := bstep (se 1 (by rfl) ⟨1147307, by rfl⟩ : syracuseStep 1529743 = 2294615) B2294615
theorem B3676051 : Blo 1358498 3676051 := bstep (se 1 (by rfl) ⟨2757038, by rfl⟩ : syracuseStep 3676051 = 5514077) B5514077
theorem B17668043 : Blo 1358498 17668043 := bstep (se 1 (by rfl) ⟨13251032, by rfl⟩ : syracuseStep 17668043 = 26502065) B26502065
theorem B6977501 : Blo 1358498 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B2037767 : Blo 1358498 2037767 := bstep (se 1 (by rfl) ⟨1528325, by rfl⟩ : syracuseStep 2037767 = 3056651) B3056651
theorem B2037803 : Blo 1358498 2037803 := bstep (se 1 (by rfl) ⟨1528352, by rfl⟩ : syracuseStep 2037803 = 3056705) B3056705
theorem B3487787 : Blo 1358498 3487787 := bstep (se 1 (by rfl) ⟨2615840, by rfl⟩ : syracuseStep 3487787 = 5231681) B5231681
theorem B2037833 : Blo 1358498 2037833 := bstep (se 2 (by rfl) ⟨764187, by rfl⟩ : syracuseStep 2037833 = 1528375) B1528375
theorem B16750709 : Blo 1358498 16750709 := bstep (se 5 (by rfl) ⟨785189, by rfl⟩ : syracuseStep 16750709 = 1570379) B1570379
theorem B2037947 : Blo 1358498 2037947 := bstep (se 1 (by rfl) ⟨1528460, by rfl⟩ : syracuseStep 2037947 = 3056921) B3056921
theorem B2038007 : Blo 1358498 2038007 := bstep (se 1 (by rfl) ⟨1528505, by rfl⟩ : syracuseStep 2038007 = 3057011) B3057011
theorem B2038031 : Blo 1358498 2038031 := bstep (se 1 (by rfl) ⟨1528523, by rfl⟩ : syracuseStep 2038031 = 3057047) B3057047
theorem B2038073 : Blo 1358498 2038073 := bstep (se 2 (by rfl) ⟨764277, by rfl⟩ : syracuseStep 2038073 = 1528555) B1528555
theorem B4585787 : Blo 1358498 4585787 := bstep (se 1 (by rfl) ⟨3439340, by rfl⟩ : syracuseStep 4585787 = 6878681) B6878681
theorem B2038151 : Blo 1358498 2038151 := bstep (se 1 (by rfl) ⟨1528613, by rfl⟩ : syracuseStep 2038151 = 3057227) B3057227
theorem B1530247 : Blo 1358498 1530247 := bstep (se 1 (by rfl) ⟨1147685, by rfl⟩ : syracuseStep 1530247 = 2295371) B2295371
theorem B5159315 : Blo 1358498 5159315 := bstep (se 1 (by rfl) ⟨3869486, by rfl⟩ : syracuseStep 5159315 = 7738973) B7738973
theorem B2038187 : Blo 1358498 2038187 := bstep (se 1 (by rfl) ⟨1528640, by rfl⟩ : syracuseStep 2038187 = 3057281) B3057281
theorem B2038217 : Blo 1358498 2038217 := bstep (se 2 (by rfl) ⟨764331, by rfl⟩ : syracuseStep 2038217 = 1528663) B1528663
theorem B9796139 : Blo 1358498 9796139 := bstep (se 1 (by rfl) ⟨7347104, by rfl⟩ : syracuseStep 9796139 = 14694209) B14694209
theorem B2038331 : Blo 1358498 2038331 := bstep (se 1 (by rfl) ⟨1528748, by rfl⟩ : syracuseStep 2038331 = 3057497) B3057497
theorem B1530427 : Blo 1358498 1530427 := bstep (se 1 (by rfl) ⟨1147820, by rfl⟩ : syracuseStep 1530427 = 2295641) B2295641
theorem B4897367 : Blo 1358498 4897367 := bstep (se 1 (by rfl) ⟨3673025, by rfl⟩ : syracuseStep 4897367 = 7346051) B7346051
theorem B3439219 : Blo 1358498 3439219 := bstep (se 1 (by rfl) ⟨2579414, by rfl⟩ : syracuseStep 3439219 = 5158829) B5158829
theorem B2038391 : Blo 1358498 2038391 := bstep (se 1 (by rfl) ⟨1528793, by rfl⟩ : syracuseStep 2038391 = 3057587) B3057587
theorem B2038415 : Blo 1358498 2038415 := bstep (se 1 (by rfl) ⟨1528811, by rfl⟩ : syracuseStep 2038415 = 3057623) B3057623
theorem B2038457 : Blo 1358498 2038457 := bstep (se 2 (by rfl) ⟨764421, by rfl⟩ : syracuseStep 2038457 = 1528843) B1528843
theorem B1358523 : Blo 1358498 1358523 := bstep (se 1 (by rfl) ⟨1018892, by rfl⟩ : syracuseStep 1358523 = 2037785) B2037785
theorem B3439361 : Blo 1358498 3439361 := bstep (se 2 (by rfl) ⟨1289760, by rfl⟩ : syracuseStep 3439361 = 2579521) B2579521
theorem B1358599 : Blo 1358498 1358599 := bstep (se 1 (by rfl) ⟨1018949, by rfl⟩ : syracuseStep 1358599 = 2037899) B2037899
theorem B2038535 : Blo 1358498 2038535 := bstep (se 1 (by rfl) ⟨1528901, by rfl⟩ : syracuseStep 2038535 = 3057803) B3057803
theorem B1358607 : Blo 1358498 1358607 := bstep (se 1 (by rfl) ⟨1018955, by rfl⟩ : syracuseStep 1358607 = 2037911) B2037911
theorem B4586273 : Blo 1358498 4586273 := bstep (se 2 (by rfl) ⟨1719852, by rfl⟩ : syracuseStep 4586273 = 3439705) B3439705
theorem B2038571 : Blo 1358498 2038571 := bstep (se 1 (by rfl) ⟨1528928, by rfl⟩ : syracuseStep 2038571 = 3057857) B3057857
theorem B3267371 : Blo 1358498 3267371 := bstep (se 1 (by rfl) ⟨2450528, by rfl⟩ : syracuseStep 3267371 = 4901057) B4901057
theorem B8715059 : Blo 1358498 8715059 := bstep (se 1 (by rfl) ⟨6536294, by rfl⟩ : syracuseStep 8715059 = 13072589) B13072589
theorem B1358651 : Blo 1358498 1358651 := bstep (se 1 (by rfl) ⟨1018988, by rfl⟩ : syracuseStep 1358651 = 2037977) B2037977
theorem B2038601 : Blo 1358498 2038601 := bstep (se 2 (by rfl) ⟨764475, by rfl⟩ : syracuseStep 2038601 = 1528951) B1528951
theorem B1358727 : Blo 1358498 1358727 := bstep (se 1 (by rfl) ⟨1019045, by rfl⟩ : syracuseStep 1358727 = 2038091) B2038091
theorem B1358735 : Blo 1358498 1358735 := bstep (se 1 (by rfl) ⟨1019051, by rfl⟩ : syracuseStep 1358735 = 2038103) B2038103
theorem B1358779 : Blo 1358498 1358779 := bstep (se 1 (by rfl) ⟨1019084, by rfl⟩ : syracuseStep 1358779 = 2038169) B2038169
theorem B2038715 : Blo 1358498 2038715 := bstep (se 1 (by rfl) ⟨1529036, by rfl⟩ : syracuseStep 2038715 = 3058073) B3058073
theorem B2038775 : Blo 1358498 2038775 := bstep (se 1 (by rfl) ⟨1529081, by rfl⟩ : syracuseStep 2038775 = 3058163) B3058163
theorem B1358855 : Blo 1358498 1358855 := bstep (se 1 (by rfl) ⟨1019141, by rfl⟩ : syracuseStep 1358855 = 2038283) B2038283
theorem B1358863 : Blo 1358498 1358863 := bstep (se 1 (by rfl) ⟨1019147, by rfl⟩ : syracuseStep 1358863 = 2038295) B2038295
theorem B2038799 : Blo 1358498 2038799 := bstep (se 1 (by rfl) ⟨1529099, by rfl⟩ : syracuseStep 2038799 = 3058199) B3058199
theorem B2292779 : Blo 1358498 2292779 := bstep (se 1 (by rfl) ⟨1719584, by rfl⟩ : syracuseStep 2292779 = 3439169) B3439169
theorem B2038841 : Blo 1358498 2038841 := bstep (se 2 (by rfl) ⟨764565, by rfl⟩ : syracuseStep 2038841 = 1529131) B1529131
theorem B1358907 : Blo 1358498 1358907 := bstep (se 1 (by rfl) ⟨1019180, by rfl⟩ : syracuseStep 1358907 = 2038361) B2038361
theorem B7445591 : Blo 1358498 7445591 := bstep (se 1 (by rfl) ⟨5584193, by rfl⟩ : syracuseStep 7445591 = 11168387) B11168387
theorem B1358983 : Blo 1358498 1358983 := bstep (se 1 (by rfl) ⟨1019237, by rfl⟩ : syracuseStep 1358983 = 2038475) B2038475
theorem B2038919 : Blo 1358498 2038919 := bstep (se 1 (by rfl) ⟨1529189, by rfl⟩ : syracuseStep 2038919 = 3058379) B3058379
theorem B1358991 : Blo 1358498 1358991 := bstep (se 1 (by rfl) ⟨1019243, by rfl⟩ : syracuseStep 1358991 = 2038487) B2038487
theorem B2038955 : Blo 1358498 2038955 := bstep (se 1 (by rfl) ⟨1529216, by rfl⟩ : syracuseStep 2038955 = 3058433) B3058433
theorem B1359035 : Blo 1358498 1359035 := bstep (se 1 (by rfl) ⟨1019276, by rfl⟩ : syracuseStep 1359035 = 2038553) B2038553
theorem B3439817 : Blo 1358498 3439817 := bstep (se 2 (by rfl) ⟨1289931, by rfl⟩ : syracuseStep 3439817 = 2579863) B2579863
theorem B2038985 : Blo 1358498 2038985 := bstep (se 2 (by rfl) ⟨764619, by rfl⟩ : syracuseStep 2038985 = 1529239) B1529239
theorem B5807305 : Blo 1358498 5807305 := bstep (se 2 (by rfl) ⟨2177739, by rfl⟩ : syracuseStep 5807305 = 4355479) B4355479
theorem B1719559 : Blo 1358498 1719559 := bstep (se 1 (by rfl) ⟨1289669, by rfl⟩ : syracuseStep 1719559 = 2579339) B2579339
theorem B1359111 : Blo 1358498 1359111 := bstep (se 1 (by rfl) ⟨1019333, by rfl⟩ : syracuseStep 1359111 = 2038667) B2038667
theorem B1359119 : Blo 1358498 1359119 := bstep (se 1 (by rfl) ⟨1019339, by rfl⟩ : syracuseStep 1359119 = 2038679) B2038679
theorem B5807375 : Blo 1358498 5807375 := bstep (se 1 (by rfl) ⟨4355531, by rfl⟩ : syracuseStep 5807375 = 8711063) B8711063
theorem B1359163 : Blo 1358498 1359163 := bstep (se 1 (by rfl) ⟨1019372, by rfl⟩ : syracuseStep 1359163 = 2038745) B2038745
theorem B4963643 : Blo 1358498 4963643 := bstep (se 1 (by rfl) ⟨3722732, by rfl⟩ : syracuseStep 4963643 = 7445465) B7445465
theorem B2039099 : Blo 1358498 2039099 := bstep (se 1 (by rfl) ⟨1529324, by rfl⟩ : syracuseStep 2039099 = 3058649) B3058649
theorem B4586867 : Blo 1358498 4586867 := bstep (se 1 (by rfl) ⟨3440150, by rfl⟩ : syracuseStep 4586867 = 6880301) B6880301
theorem B2039159 : Blo 1358498 2039159 := bstep (se 1 (by rfl) ⟨1529369, by rfl⟩ : syracuseStep 2039159 = 3058739) B3058739
theorem B1359239 : Blo 1358498 1359239 := bstep (se 1 (by rfl) ⟨1019429, by rfl⟩ : syracuseStep 1359239 = 2038859) B2038859
theorem B6200711 : Blo 1358498 6200711 := bstep (se 1 (by rfl) ⟨4650533, by rfl⟩ : syracuseStep 6200711 = 9301067) B9301067
theorem B1359247 : Blo 1358498 1359247 := bstep (se 1 (by rfl) ⟨1019435, by rfl⟩ : syracuseStep 1359247 = 2038871) B2038871
theorem B2039183 : Blo 1358498 2039183 := bstep (se 1 (by rfl) ⟨1529387, by rfl⟩ : syracuseStep 2039183 = 3058775) B3058775
theorem B2293177 : Blo 1358498 2293177 := bstep (se 2 (by rfl) ⟨859941, by rfl⟩ : syracuseStep 2293177 = 1719883) B1719883
theorem B2039225 : Blo 1358498 2039225 := bstep (se 2 (by rfl) ⟨764709, by rfl⟩ : syracuseStep 2039225 = 1529419) B1529419
theorem B1359291 : Blo 1358498 1359291 := bstep (se 1 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 1359291 = 2038937) B2038937
theorem B1359367 : Blo 1358498 1359367 := bstep (se 1 (by rfl) ⟨1019525, by rfl⟩ : syracuseStep 1359367 = 2039051) B2039051
theorem B2039303 : Blo 1358498 2039303 := bstep (se 1 (by rfl) ⟨1529477, by rfl⟩ : syracuseStep 2039303 = 3058955) B3058955
theorem B1359375 : Blo 1358498 1359375 := bstep (se 1 (by rfl) ⟨1019531, by rfl⟩ : syracuseStep 1359375 = 2039063) B2039063
theorem B3440171 : Blo 1358498 3440171 := bstep (se 1 (by rfl) ⟨2580128, by rfl⟩ : syracuseStep 3440171 = 5160257) B5160257
theorem B2039339 : Blo 1358498 2039339 := bstep (se 1 (by rfl) ⟨1529504, by rfl⟩ : syracuseStep 2039339 = 3059009) B3059009
theorem B1359419 : Blo 1358498 1359419 := bstep (se 1 (by rfl) ⟨1019564, by rfl⟩ : syracuseStep 1359419 = 2039129) B2039129
theorem B2039369 : Blo 1358498 2039369 := bstep (se 2 (by rfl) ⟨764763, by rfl⟩ : syracuseStep 2039369 = 1529527) B1529527
theorem B1359495 : Blo 1358498 1359495 := bstep (se 1 (by rfl) ⟨1019621, by rfl⟩ : syracuseStep 1359495 = 2039243) B2039243
theorem B1359503 : Blo 1358498 1359503 := bstep (se 1 (by rfl) ⟨1019627, by rfl⟩ : syracuseStep 1359503 = 2039255) B2039255
theorem B1359547 : Blo 1358498 1359547 := bstep (se 1 (by rfl) ⟨1019660, by rfl⟩ : syracuseStep 1359547 = 2039321) B2039321
theorem B2039483 : Blo 1358498 2039483 := bstep (se 1 (by rfl) ⟨1529612, by rfl⟩ : syracuseStep 2039483 = 3059225) B3059225
theorem B1720055 : Blo 1358498 1720055 := bstep (se 1 (by rfl) ⟨1290041, by rfl⟩ : syracuseStep 1720055 = 2580083) B2580083
theorem B2039543 : Blo 1358498 2039543 := bstep (se 1 (by rfl) ⟨1529657, by rfl⟩ : syracuseStep 2039543 = 3059315) B3059315
theorem B8273665 : Blo 1358498 8273665 := bstep (se 2 (by rfl) ⟨3102624, by rfl⟩ : syracuseStep 8273665 = 6205249) B6205249
theorem B1359623 : Blo 1358498 1359623 := bstep (se 1 (by rfl) ⟨1019717, by rfl⟩ : syracuseStep 1359623 = 2039435) B2039435
theorem B1359631 : Blo 1358498 1359631 := bstep (se 1 (by rfl) ⟨1019723, by rfl⟩ : syracuseStep 1359631 = 2039447) B2039447
theorem B2039567 : Blo 1358498 2039567 := bstep (se 1 (by rfl) ⟨1529675, by rfl⟩ : syracuseStep 2039567 = 3059351) B3059351
theorem B2039609 : Blo 1358498 2039609 := bstep (se 2 (by rfl) ⟨764853, by rfl⟩ : syracuseStep 2039609 = 1529707) B1529707
theorem B1359675 : Blo 1358498 1359675 := bstep (se 1 (by rfl) ⟨1019756, by rfl⟩ : syracuseStep 1359675 = 2039513) B2039513
theorem B4898675 : Blo 1358498 4898675 := bstep (se 1 (by rfl) ⟨3674006, by rfl⟩ : syracuseStep 4898675 = 7348013) B7348013
theorem B1359751 : Blo 1358498 1359751 := bstep (se 1 (by rfl) ⟨1019813, by rfl⟩ : syracuseStep 1359751 = 2039627) B2039627
theorem B2039687 : Blo 1358498 2039687 := bstep (se 1 (by rfl) ⟨1529765, by rfl⟩ : syracuseStep 2039687 = 3059531) B3059531
theorem B1720207 : Blo 1358498 1720207 := bstep (se 1 (by rfl) ⟨1290155, by rfl⟩ : syracuseStep 1720207 = 2580311) B2580311
theorem B1359759 : Blo 1358498 1359759 := bstep (se 1 (by rfl) ⟨1019819, by rfl⟩ : syracuseStep 1359759 = 2039639) B2039639
theorem B2039723 : Blo 1358498 2039723 := bstep (se 1 (by rfl) ⟨1529792, by rfl⟩ : syracuseStep 2039723 = 3059585) B3059585
theorem B1359803 : Blo 1358498 1359803 := bstep (se 1 (by rfl) ⟨1019852, by rfl⟩ : syracuseStep 1359803 = 2039705) B2039705
theorem B2039753 : Blo 1358498 2039753 := bstep (se 2 (by rfl) ⟨764907, by rfl⟩ : syracuseStep 2039753 = 1529815) B1529815
theorem B1359911 : Blo 1358498 1359911 := bstep (se 1 (by rfl) ⟨1019933, by rfl⟩ : syracuseStep 1359911 = 2039867) B2039867
theorem B1359951 : Blo 1358498 1359951 := bstep (se 1 (by rfl) ⟨1019963, by rfl⟩ : syracuseStep 1359951 = 2039927) B2039927
theorem B16547921 : Blo 1358498 16547921 := bstep (se 2 (by rfl) ⟨6205470, by rfl⟩ : syracuseStep 16547921 = 12410941) B12410941
theorem B1359967 : Blo 1358498 1359967 := bstep (se 1 (by rfl) ⟨1019975, by rfl⟩ : syracuseStep 1359967 = 2039951) B2039951
theorem B1359995 : Blo 1358498 1359995 := bstep (se 1 (by rfl) ⟨1019996, by rfl⟩ : syracuseStep 1359995 = 2039993) B2039993
theorem B4587677 : Blo 1358498 4587677 := bstep (se 3 (by rfl) ⟨860189, by rfl⟩ : syracuseStep 4587677 = 1720379) B1720379
theorem B15491249 : Blo 1358498 15491249 := bstep (se 2 (by rfl) ⟨5809218, by rfl⟩ : syracuseStep 15491249 = 11618437) B11618437
theorem B1360047 : Blo 1358498 1360047 := bstep (se 1 (by rfl) ⟨1020035, by rfl⟩ : syracuseStep 1360047 = 2040071) B2040071
theorem B1360071 : Blo 1358498 1360071 := bstep (se 1 (by rfl) ⟨1020053, by rfl⟩ : syracuseStep 1360071 = 2040107) B2040107
theorem B1360091 : Blo 1358498 1360091 := bstep (se 1 (by rfl) ⟨1020068, by rfl⟩ : syracuseStep 1360091 = 2040137) B2040137
theorem B1360167 : Blo 1358498 1360167 := bstep (se 1 (by rfl) ⟨1020125, by rfl⟩ : syracuseStep 1360167 = 2040251) B2040251
theorem B6881597 : Blo 1358498 6881597 := bstep (se 3 (by rfl) ⟨1290299, by rfl⟩ : syracuseStep 6881597 = 2580599) B2580599
theorem B1360207 : Blo 1358498 1360207 := bstep (se 1 (by rfl) ⟨1020155, by rfl⟩ : syracuseStep 1360207 = 2040311) B2040311
theorem B1360223 : Blo 1358498 1360223 := bstep (se 1 (by rfl) ⟨1020167, by rfl⟩ : syracuseStep 1360223 = 2040335) B2040335
theorem B39739747 : Blo 1358498 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B3441001 : Blo 1358498 3441001 := bstep (se 2 (by rfl) ⟨1290375, by rfl⟩ : syracuseStep 3441001 = 2580751) B2580751
theorem B1360251 : Blo 1358498 1360251 := bstep (se 1 (by rfl) ⟨1020188, by rfl⟩ : syracuseStep 1360251 = 2040377) B2040377
theorem B2040239 : Blo 1358498 2040239 := bstep (se 1 (by rfl) ⟨1530179, by rfl⟩ : syracuseStep 2040239 = 3060359) B3060359
theorem B1360303 : Blo 1358498 1360303 := bstep (se 1 (by rfl) ⟨1020227, by rfl⟩ : syracuseStep 1360303 = 2040455) B2040455
theorem B1720759 : Blo 1358498 1720759 := bstep (se 1 (by rfl) ⟨1290569, by rfl⟩ : syracuseStep 1720759 = 2581139) B2581139
theorem B2294203 : Blo 1358498 2294203 := bstep (se 1 (by rfl) ⟨1720652, by rfl⟩ : syracuseStep 2294203 = 3441305) B3441305
theorem B1360327 : Blo 1358498 1360327 := bstep (se 1 (by rfl) ⟨1020245, by rfl⟩ : syracuseStep 1360327 = 2040491) B2040491
theorem B1360347 : Blo 1358498 1360347 := bstep (se 1 (by rfl) ⟨1020260, by rfl⟩ : syracuseStep 1360347 = 2040521) B2040521
theorem B2040329 : Blo 1358498 2040329 := bstep (se 2 (by rfl) ⟨765123, by rfl⟩ : syracuseStep 2040329 = 1530247) B1530247
theorem B99254807 : Blo 1358498 99254807 := bstep (se 1 (by rfl) ⟨74441105, by rfl⟩ : syracuseStep 99254807 = 148882211) B148882211
theorem B2294311 : Blo 1358498 2294311 := bstep (se 1 (by rfl) ⟨1720733, by rfl⟩ : syracuseStep 2294311 = 3441467) B3441467
theorem B2040359 : Blo 1358498 2040359 := bstep (se 1 (by rfl) ⟨1530269, by rfl⟩ : syracuseStep 2040359 = 3060539) B3060539
theorem B1360423 : Blo 1358498 1360423 := bstep (se 1 (by rfl) ⟨1020317, by rfl⟩ : syracuseStep 1360423 = 2040635) B2040635
theorem B1360463 : Blo 1358498 1360463 := bstep (se 1 (by rfl) ⟨1020347, by rfl⟩ : syracuseStep 1360463 = 2040695) B2040695
theorem B1360479 : Blo 1358498 1360479 := bstep (se 1 (by rfl) ⟨1020359, by rfl⟩ : syracuseStep 1360479 = 2040719) B2040719
theorem B3441275 : Blo 1358498 3441275 := bstep (se 1 (by rfl) ⟨2580956, by rfl⟩ : syracuseStep 3441275 = 5161913) B5161913
theorem B2040443 : Blo 1358498 2040443 := bstep (se 1 (by rfl) ⟨1530332, by rfl⟩ : syracuseStep 2040443 = 3060665) B3060665
theorem B4588217 : Blo 1358498 4588217 := bstep (se 2 (by rfl) ⟨1720581, by rfl⟩ : syracuseStep 4588217 = 3441163) B3441163
theorem B2040569 : Blo 1358498 2040569 := bstep (se 2 (by rfl) ⟨765213, by rfl⟩ : syracuseStep 2040569 = 1530427) B1530427
theorem B20931329 : Blo 1358498 20931329 := bstep (se 2 (by rfl) ⟨7849248, by rfl⟩ : syracuseStep 20931329 = 15698497) B15698497
theorem B2581321 : Blo 1358498 2581321 := bstep (se 2 (by rfl) ⟨967995, by rfl⟩ : syracuseStep 2581321 = 1935991) B1935991
theorem B2040671 : Blo 1358498 2040671 := bstep (se 1 (by rfl) ⟨1530503, by rfl⟩ : syracuseStep 2040671 = 3061007) B3061007
theorem B2294635 : Blo 1358498 2294635 := bstep (se 1 (by rfl) ⟨1720976, by rfl⟩ : syracuseStep 2294635 = 3441953) B3441953
theorem B2040683 : Blo 1358498 2040683 := bstep (se 1 (by rfl) ⟨1530512, by rfl⟩ : syracuseStep 2040683 = 3061025) B3061025
theorem B11781085 : Blo 1358498 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B5162231 : Blo 1358498 5162231 := bstep (se 1 (by rfl) ⟨3871673, by rfl⟩ : syracuseStep 5162231 = 7743347) B7743347
theorem B4588811 : Blo 1358498 4588811 := bstep (se 1 (by rfl) ⟨3441608, by rfl⟩ : syracuseStep 4588811 = 6883217) B6883217
theorem B1377631 : Blo 1358498 1377631 := bstep (se 1 (by rfl) ⟨1033223, by rfl⟩ : syracuseStep 1377631 = 2066447) B2066447
theorem B11322767 : Blo 1358498 11322767 := bstep (se 1 (by rfl) ⟨8492075, by rfl⟩ : syracuseStep 11322767 = 16984151) B16984151
theorem B11167139 : Blo 1358498 11167139 := bstep (se 1 (by rfl) ⟨8375354, by rfl⟩ : syracuseStep 11167139 = 16750709) B16750709
theorem B1934857 : Blo 1358498 1934857 := bstep (se 2 (by rfl) ⟨725571, by rfl⟩ : syracuseStep 1934857 = 1451143) B1451143
theorem B4589081 : Blo 1358498 4589081 := bstep (se 2 (by rfl) ⟨1720905, by rfl⟩ : syracuseStep 4589081 = 3441811) B3441811
theorem B3057191 : Blo 1358498 3057191 := bstep (se 1 (by rfl) ⟨2292893, by rfl⟩ : syracuseStep 3057191 = 4585787) B4585787
theorem B7743073 : Blo 1358498 7743073 := bstep (se 2 (by rfl) ⟨2903652, by rfl⟩ : syracuseStep 7743073 = 5807305) B5807305
theorem B6530759 : Blo 1358498 6530759 := bstep (se 1 (by rfl) ⟨4898069, by rfl⟩ : syracuseStep 6530759 = 9796139) B9796139
theorem B1935199 : Blo 1358498 1935199 := bstep (se 1 (by rfl) ⟨1451399, by rfl⟩ : syracuseStep 1935199 = 2902799) B2902799
theorem B3057515 : Blo 1358498 3057515 := bstep (se 1 (by rfl) ⟨2293136, by rfl⟩ : syracuseStep 3057515 = 4586273) B4586273
theorem B5810039 : Blo 1358498 5810039 := bstep (se 1 (by rfl) ⟨4357529, by rfl⟩ : syracuseStep 5810039 = 8715059) B8715059
theorem B2295695 : Blo 1358498 2295695 := bstep (se 1 (by rfl) ⟨1721771, by rfl⟩ : syracuseStep 2295695 = 3443543) B3443543
theorem B3057569 : Blo 1358498 3057569 := bstep (se 2 (by rfl) ⟨1146588, by rfl⟩ : syracuseStep 3057569 = 2293177) B2293177
theorem B5163203 : Blo 1358498 5163203 := bstep (se 1 (by rfl) ⟨3872402, by rfl⟩ : syracuseStep 5163203 = 7744805) B7744805
theorem B3057911 : Blo 1358498 3057911 := bstep (se 1 (by rfl) ⟨2293433, by rfl⟩ : syracuseStep 3057911 = 4586867) B4586867
theorem B3443087 : Blo 1358498 3443087 := bstep (se 1 (by rfl) ⟨2582315, by rfl⟩ : syracuseStep 3443087 = 5164631) B5164631
theorem B39750041 : Blo 1358498 39750041 := bstep (se 2 (by rfl) ⟨14906265, by rfl⟩ : syracuseStep 39750041 = 29812531) B29812531
theorem B6883865 : Blo 1358498 6883865 := bstep (se 2 (by rfl) ⟨2581449, by rfl⟩ : syracuseStep 6883865 = 5162899) B5162899
theorem B4901401 : Blo 1358498 4901401 := bstep (se 2 (by rfl) ⟨1838025, by rfl⟩ : syracuseStep 4901401 = 3676051) B3676051
theorem B10316321 : Blo 1358498 10316321 := bstep (se 2 (by rfl) ⟨3868620, by rfl⟩ : syracuseStep 10316321 = 7737241) B7737241
theorem B4352609 : Blo 1358498 4352609 := bstep (se 2 (by rfl) ⟨1632228, by rfl⟩ : syracuseStep 4352609 = 3264457) B3264457
theorem B4590215 : Blo 1358498 4590215 := bstep (se 1 (by rfl) ⟨3442661, by rfl⟩ : syracuseStep 4590215 = 6885323) B6885323
theorem B5163659 : Blo 1358498 5163659 := bstep (se 1 (by rfl) ⟨3872744, by rfl⟩ : syracuseStep 5163659 = 7745489) B7745489
theorem B4590269 : Blo 1358498 4590269 := bstep (se 3 (by rfl) ⟨860675, by rfl⟩ : syracuseStep 4590269 = 1721351) B1721351
theorem B3443411 : Blo 1358498 3443411 := bstep (se 1 (by rfl) ⟨2582558, by rfl⟩ : syracuseStep 3443411 = 5165117) B5165117
theorem B3058505 : Blo 1358498 3058505 := bstep (se 2 (by rfl) ⟨1146939, by rfl⟩ : syracuseStep 3058505 = 2293879) B2293879
theorem B3099487 : Blo 1358498 3099487 := bstep (se 1 (by rfl) ⟨2324615, by rfl⟩ : syracuseStep 3099487 = 4649231) B4649231
theorem B14904157 : Blo 1358498 14904157 := bstep (se 3 (by rfl) ⟨2794529, by rfl⟩ : syracuseStep 14904157 = 5589059) B5589059
theorem B5163871 : Blo 1358498 5163871 := bstep (se 1 (by rfl) ⟨3872903, by rfl⟩ : syracuseStep 5163871 = 7745807) B7745807
theorem B4590431 : Blo 1358498 4590431 := bstep (se 1 (by rfl) ⟨3442823, by rfl⟩ : syracuseStep 4590431 = 6885647) B6885647
theorem B11611025 : Blo 1358498 11611025 := bstep (se 2 (by rfl) ⟨4354134, by rfl⟩ : syracuseStep 11611025 = 8708269) B8708269
theorem B1837999 : Blo 1358498 1837999 := bstep (se 1 (by rfl) ⟨1378499, by rfl⟩ : syracuseStep 1837999 = 2756999) B2756999
theorem B3869623 : Blo 1358498 3869623 := bstep (se 1 (by rfl) ⟨2902217, by rfl⟩ : syracuseStep 3869623 = 5804435) B5804435
theorem B4590593 : Blo 1358498 4590593 := bstep (se 2 (by rfl) ⟨1721472, by rfl⟩ : syracuseStep 4590593 = 3442945) B3442945
theorem B7744531 : Blo 1358498 7744531 := bstep (se 1 (by rfl) ⟨5808398, by rfl⟩ : syracuseStep 7744531 = 11616797) B11616797
theorem B10464713 : Blo 1358498 10464713 := bstep (se 2 (by rfl) ⟨3924267, by rfl⟩ : syracuseStep 10464713 = 7848535) B7848535
theorem B5377499 : Blo 1358498 5377499 := bstep (se 1 (by rfl) ⟨4033124, by rfl⟩ : syracuseStep 5377499 = 8066249) B8066249
theorem B44092997 : Blo 1358498 44092997 := bstep (se 4 (by rfl) ⟨4133718, by rfl⟩ : syracuseStep 44092997 = 8267437) B8267437
theorem B3059297 : Blo 1358498 3059297 := bstep (se 2 (by rfl) ⟨1147236, by rfl⟩ : syracuseStep 3059297 = 2294473) B2294473
theorem B4353725 : Blo 1358498 4353725 := bstep (se 3 (by rfl) ⟨816323, by rfl⟩ : syracuseStep 4353725 = 1632647) B1632647
theorem B6205177 : Blo 1358498 6205177 := bstep (se 2 (by rfl) ⟨2326941, by rfl⟩ : syracuseStep 6205177 = 4653883) B4653883
theorem B5164829 : Blo 1358498 5164829 := bstep (se 3 (by rfl) ⟨968405, by rfl⟩ : syracuseStep 5164829 = 1936811) B1936811
theorem B5164843 : Blo 1358498 5164843 := bstep (se 1 (by rfl) ⟨3873632, by rfl⟩ : syracuseStep 5164843 = 7747265) B7747265
theorem B4591403 : Blo 1358498 4591403 := bstep (se 1 (by rfl) ⟨3443552, by rfl⟩ : syracuseStep 4591403 = 6887105) B6887105
theorem B17665955 : Blo 1358498 17665955 := bstep (se 1 (by rfl) ⟨13249466, by rfl⟩ : syracuseStep 17665955 = 26498933) B26498933
theorem B3059639 : Blo 1358498 3059639 := bstep (se 1 (by rfl) ⟨2294729, by rfl⟩ : syracuseStep 3059639 = 4589459) B4589459
theorem B4591673 : Blo 1358498 4591673 := bstep (se 2 (by rfl) ⟨1721877, by rfl⟩ : syracuseStep 4591673 = 3443755) B3443755
theorem B7344209 : Blo 1358498 7344209 := bstep (se 2 (by rfl) ⟨2754078, by rfl⟩ : syracuseStep 7344209 = 5508157) B5508157
theorem B3871081 : Blo 1358498 3871081 := bstep (se 2 (by rfl) ⟨1451655, by rfl⟩ : syracuseStep 3871081 = 2903311) B2903311
theorem B3264911 : Blo 1358498 3264911 := bstep (se 1 (by rfl) ⟨2448683, by rfl⟩ : syracuseStep 3264911 = 4897367) B4897367
theorem B3060233 : Blo 1358498 3060233 := bstep (se 2 (by rfl) ⟨1147587, by rfl⟩ : syracuseStep 3060233 = 2295175) B2295175
theorem B7344665 : Blo 1358498 7344665 := bstep (se 2 (by rfl) ⟨2754249, by rfl⟩ : syracuseStep 7344665 = 5508499) B5508499
theorem B17429093 : Blo 1358498 17429093 := bstep (se 4 (by rfl) ⟨1633977, by rfl⟩ : syracuseStep 17429093 = 3267955) B3267955
theorem B1528519 : Blo 1358498 1528519 := bstep (se 1 (by rfl) ⟨1146389, by rfl⟩ : syracuseStep 1528519 = 2292779) B2292779
theorem B23212817 : Blo 1358498 23212817 := bstep (se 2 (by rfl) ⟨8704806, by rfl⟩ : syracuseStep 23212817 = 17409613) B17409613
theorem B41857843 : Blo 1358498 41857843 := bstep (se 1 (by rfl) ⟨31393382, by rfl⟩ : syracuseStep 41857843 = 62786765) B62786765
theorem B3871583 : Blo 1358498 3871583 := bstep (se 1 (by rfl) ⟨2903687, by rfl⟩ : syracuseStep 3871583 = 5807375) B5807375
theorem B3060575 : Blo 1358498 3060575 := bstep (se 1 (by rfl) ⟨2295431, by rfl⟩ : syracuseStep 3060575 = 4590863) B4590863
theorem B4133807 : Blo 1358498 4133807 := bstep (se 1 (by rfl) ⟨3100355, by rfl⟩ : syracuseStep 4133807 = 6200711) B6200711
theorem B13063133 : Blo 1358498 13063133 := bstep (se 3 (by rfl) ⟨2449337, by rfl⟩ : syracuseStep 13063133 = 4898675) B4898675
theorem B10327013 : Blo 1358498 10327013 := bstep (se 4 (by rfl) ⟨968157, by rfl⟩ : syracuseStep 10327013 = 1936315) B1936315
theorem B11031553 : Blo 1358498 11031553 := bstep (se 2 (by rfl) ⟨4136832, by rfl⟩ : syracuseStep 11031553 = 8273665) B8273665
theorem B3060755 : Blo 1358498 3060755 := bstep (se 1 (by rfl) ⟨2295566, by rfl⟩ : syracuseStep 3060755 = 4591133) B4591133
theorem B3871901 : Blo 1358498 3871901 := bstep (se 3 (by rfl) ⟨725981, by rfl⟩ : syracuseStep 3871901 = 1451963) B1451963
theorem B3061097 : Blo 1358498 3061097 := bstep (se 2 (by rfl) ⟨1147911, by rfl⟩ : syracuseStep 3061097 = 2295823) B2295823
theorem B6886781 : Blo 1358498 6886781 := bstep (se 3 (by rfl) ⟨1291271, by rfl⟩ : syracuseStep 6886781 = 2582543) B2582543
theorem B1529383 : Blo 1358498 1529383 := bstep (se 1 (by rfl) ⟨1147037, by rfl⟩ : syracuseStep 1529383 = 2294075) B2294075
theorem B5805665 : Blo 1358498 5805665 := bstep (se 2 (by rfl) ⟨2177124, by rfl⟩ : syracuseStep 5805665 = 4354249) B4354249
theorem B4134497 : Blo 1358498 4134497 := bstep (se 2 (by rfl) ⟨1550436, by rfl⟩ : syracuseStep 4134497 = 3100873) B3100873
theorem B6878843 : Blo 1358498 6878843 := bstep (se 1 (by rfl) ⟨5159132, by rfl⟩ : syracuseStep 6878843 = 10318265) B10318265
theorem B3872585 : Blo 1358498 3872585 := bstep (se 2 (by rfl) ⟨1452219, by rfl⟩ : syracuseStep 3872585 = 2904439) B2904439
theorem B3266399 : Blo 1358498 3266399 := bstep (se 1 (by rfl) ⟨2449799, by rfl⟩ : syracuseStep 3266399 = 4899599) B4899599
theorem B7747447 : Blo 1358498 7747447 := bstep (se 1 (by rfl) ⟨5810585, by rfl⟩ : syracuseStep 7747447 = 11621171) B11621171
theorem B2037839 : Blo 1358498 2037839 := bstep (se 1 (by rfl) ⟨1528379, by rfl⟩ : syracuseStep 2037839 = 3056759) B3056759
theorem B6199411 : Blo 1358498 6199411 := bstep (se 1 (by rfl) ⟨4649558, by rfl⟩ : syracuseStep 6199411 = 9299117) B9299117
theorem B4585625 : Blo 1358498 4585625 := bstep (se 2 (by rfl) ⟨1719609, by rfl⟩ : syracuseStep 4585625 = 3439219) B3439219
theorem B2037959 : Blo 1358498 2037959 := bstep (se 1 (by rfl) ⟨1528469, by rfl⟩ : syracuseStep 2037959 = 3056939) B3056939
theorem B1767623 : Blo 1358498 1767623 := bstep (se 1 (by rfl) ⟨1325717, by rfl⟩ : syracuseStep 1767623 = 2651435) B2651435
theorem B69818609 : Blo 1358498 69818609 := bstep (se 2 (by rfl) ⟨26181978, by rfl⟩ : syracuseStep 69818609 = 52363957) B52363957
theorem B2177273 : Blo 1358498 2177273 := bstep (se 2 (by rfl) ⟨816477, by rfl⟩ : syracuseStep 2177273 = 1632955) B1632955
theorem B11606273 : Blo 1358498 11606273 := bstep (se 2 (by rfl) ⟨4352352, by rfl⟩ : syracuseStep 11606273 = 8704705) B8704705
theorem B2038121 : Blo 1358498 2038121 := bstep (se 2 (by rfl) ⟨764295, by rfl⟩ : syracuseStep 2038121 = 1528591) B1528591
theorem B3873167 : Blo 1358498 3873167 := bstep (se 1 (by rfl) ⟨2904875, by rfl⟩ : syracuseStep 3873167 = 5809751) B5809751
theorem B9804185 : Blo 1358498 9804185 := bstep (se 2 (by rfl) ⟨3676569, by rfl⟩ : syracuseStep 9804185 = 7353139) B7353139
theorem B2038199 : Blo 1358498 2038199 := bstep (se 1 (by rfl) ⟨1528649, by rfl⟩ : syracuseStep 2038199 = 3057299) B3057299
theorem B2038235 : Blo 1358498 2038235 := bstep (se 1 (by rfl) ⟨1528676, by rfl⟩ : syracuseStep 2038235 = 3057353) B3057353
theorem B4356595 : Blo 1358498 4356595 := bstep (se 1 (by rfl) ⟨3267446, by rfl⟩ : syracuseStep 4356595 = 6534893) B6534893
theorem B5159483 : Blo 1358498 5159483 := bstep (se 1 (by rfl) ⟨3869612, by rfl⟩ : syracuseStep 5159483 = 7739225) B7739225
theorem B11778695 : Blo 1358498 11778695 := bstep (se 1 (by rfl) ⟨8834021, by rfl⟩ : syracuseStep 11778695 = 17668043) B17668043
theorem B4651667 : Blo 1358498 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B1358511 : Blo 1358498 1358511 := bstep (se 1 (by rfl) ⟨1018883, by rfl⟩ : syracuseStep 1358511 = 2037767) B2037767
theorem B1358535 : Blo 1358498 1358535 := bstep (se 1 (by rfl) ⟨1018901, by rfl⟩ : syracuseStep 1358535 = 2037803) B2037803
theorem B2325191 : Blo 1358498 2325191 := bstep (se 1 (by rfl) ⟨1743893, by rfl⟩ : syracuseStep 2325191 = 3487787) B3487787
theorem B1358555 : Blo 1358498 1358555 := bstep (se 1 (by rfl) ⟨1018916, by rfl⟩ : syracuseStep 1358555 = 2037833) B2037833
theorem B1358631 : Blo 1358498 1358631 := bstep (se 1 (by rfl) ⟨1018973, by rfl⟩ : syracuseStep 1358631 = 2037947) B2037947
theorem B1358671 : Blo 1358498 1358671 := bstep (se 1 (by rfl) ⟨1019003, by rfl⟩ : syracuseStep 1358671 = 2038007) B2038007
theorem B1358687 : Blo 1358498 1358687 := bstep (se 1 (by rfl) ⟨1019015, by rfl⟩ : syracuseStep 1358687 = 2038031) B2038031
theorem B1358715 : Blo 1358498 1358715 := bstep (se 1 (by rfl) ⟨1019036, by rfl⟩ : syracuseStep 1358715 = 2038073) B2038073
theorem B1358767 : Blo 1358498 1358767 := bstep (se 1 (by rfl) ⟨1019075, by rfl⟩ : syracuseStep 1358767 = 2038151) B2038151
theorem B2038703 : Blo 1358498 2038703 := bstep (se 1 (by rfl) ⟨1529027, by rfl⟩ : syracuseStep 2038703 = 3058055) B3058055
theorem B3439543 : Blo 1358498 3439543 := bstep (se 1 (by rfl) ⟨2579657, by rfl⟩ : syracuseStep 3439543 = 5159315) B5159315
theorem B1358791 : Blo 1358498 1358791 := bstep (se 1 (by rfl) ⟨1019093, by rfl⟩ : syracuseStep 1358791 = 2038187) B2038187
theorem B1358811 : Blo 1358498 1358811 := bstep (se 1 (by rfl) ⟨1019108, by rfl⟩ : syracuseStep 1358811 = 2038217) B2038217
theorem B2292745 : Blo 1358498 2292745 := bstep (se 2 (by rfl) ⟨859779, by rfl⟩ : syracuseStep 2292745 = 1719559) B1719559
theorem B2038793 : Blo 1358498 2038793 := bstep (se 2 (by rfl) ⟨764547, by rfl⟩ : syracuseStep 2038793 = 1529095) B1529095
theorem B1358887 : Blo 1358498 1358887 := bstep (se 1 (by rfl) ⟨1019165, by rfl⟩ : syracuseStep 1358887 = 2038331) B2038331
theorem B2038823 : Blo 1358498 2038823 := bstep (se 1 (by rfl) ⟨1529117, by rfl⟩ : syracuseStep 2038823 = 3058235) B3058235
theorem B8707115 : Blo 1358498 8707115 := bstep (se 1 (by rfl) ⟨6530336, by rfl⟩ : syracuseStep 8707115 = 13060673) B13060673
theorem B1358927 : Blo 1358498 1358927 := bstep (se 1 (by rfl) ⟨1019195, by rfl⟩ : syracuseStep 1358927 = 2038391) B2038391
theorem B1358943 : Blo 1358498 1358943 := bstep (se 1 (by rfl) ⟨1019207, by rfl⟩ : syracuseStep 1358943 = 2038415) B2038415
theorem B1358971 : Blo 1358498 1358971 := bstep (se 1 (by rfl) ⟨1019228, by rfl⟩ : syracuseStep 1358971 = 2038457) B2038457
theorem B2038907 : Blo 1358498 2038907 := bstep (se 1 (by rfl) ⟨1529180, by rfl⟩ : syracuseStep 2038907 = 3058361) B3058361
theorem B58768517 : Blo 1358498 58768517 := bstep (se 4 (by rfl) ⟨5509548, by rfl⟩ : syracuseStep 58768517 = 11019097) B11019097
theorem B2292907 : Blo 1358498 2292907 := bstep (se 1 (by rfl) ⟨1719680, by rfl⟩ : syracuseStep 2292907 = 3439361) B3439361
theorem B2579627 : Blo 1358498 2579627 := bstep (se 1 (by rfl) ⟨1934720, by rfl⟩ : syracuseStep 2579627 = 3869441) B3869441
theorem B1359023 : Blo 1358498 1359023 := bstep (se 1 (by rfl) ⟨1019267, by rfl⟩ : syracuseStep 1359023 = 2038535) B2038535
theorem B3267755 : Blo 1358498 3267755 := bstep (se 1 (by rfl) ⟨2450816, by rfl⟩ : syracuseStep 3267755 = 4901633) B4901633
theorem B8707267 : Blo 1358498 8707267 := bstep (se 1 (by rfl) ⟨6530450, by rfl⟩ : syracuseStep 8707267 = 13060901) B13060901
theorem B1359047 : Blo 1358498 1359047 := bstep (se 1 (by rfl) ⟨1019285, by rfl⟩ : syracuseStep 1359047 = 2038571) B2038571
theorem B2178247 : Blo 1358498 2178247 := bstep (se 1 (by rfl) ⟨1633685, by rfl⟩ : syracuseStep 2178247 = 3267371) B3267371
theorem B1359067 : Blo 1358498 1359067 := bstep (se 1 (by rfl) ⟨1019300, by rfl⟩ : syracuseStep 1359067 = 2038601) B2038601
theorem B12393719 : Blo 1358498 12393719 := bstep (se 1 (by rfl) ⟨9295289, by rfl⟩ : syracuseStep 12393719 = 18590579) B18590579
theorem B2039033 : Blo 1358498 2039033 := bstep (se 2 (by rfl) ⟨764637, by rfl⟩ : syracuseStep 2039033 = 1529275) B1529275
theorem B1359143 : Blo 1358498 1359143 := bstep (se 1 (by rfl) ⟨1019357, by rfl⟩ : syracuseStep 1359143 = 2038715) B2038715
theorem B4586813 : Blo 1358498 4586813 := bstep (se 3 (by rfl) ⟨860027, by rfl⟩ : syracuseStep 4586813 = 1720055) B1720055
theorem B1359183 : Blo 1358498 1359183 := bstep (se 1 (by rfl) ⟨1019387, by rfl⟩ : syracuseStep 1359183 = 2038775) B2038775
theorem B1359199 : Blo 1358498 1359199 := bstep (se 1 (by rfl) ⟨1019399, by rfl⟩ : syracuseStep 1359199 = 2038799) B2038799
theorem B2039135 : Blo 1358498 2039135 := bstep (se 1 (by rfl) ⟨1529351, by rfl⟩ : syracuseStep 2039135 = 3058703) B3058703
theorem B2039147 : Blo 1358498 2039147 := bstep (se 1 (by rfl) ⟨1529360, by rfl⟩ : syracuseStep 2039147 = 3058721) B3058721
theorem B1359227 : Blo 1358498 1359227 := bstep (se 1 (by rfl) ⟨1019420, by rfl⟩ : syracuseStep 1359227 = 2038841) B2038841
theorem B4963727 : Blo 1358498 4963727 := bstep (se 1 (by rfl) ⟨3722795, by rfl⟩ : syracuseStep 4963727 = 7445591) B7445591
theorem B1359279 : Blo 1358498 1359279 := bstep (se 1 (by rfl) ⟨1019459, by rfl⟩ : syracuseStep 1359279 = 2038919) B2038919
theorem B1359303 : Blo 1358498 1359303 := bstep (se 1 (by rfl) ⟨1019477, by rfl⟩ : syracuseStep 1359303 = 2038955) B2038955
theorem B2293211 : Blo 1358498 2293211 := bstep (se 1 (by rfl) ⟨1719908, by rfl⟩ : syracuseStep 2293211 = 3439817) B3439817
theorem B1359323 : Blo 1358498 1359323 := bstep (se 1 (by rfl) ⟨1019492, by rfl⟩ : syracuseStep 1359323 = 2038985) B2038985
theorem B2481683 : Blo 1358498 2481683 := bstep (se 1 (by rfl) ⟨1861262, by rfl⟩ : syracuseStep 2481683 = 3722525) B3722525
theorem B3309095 : Blo 1358498 3309095 := bstep (se 1 (by rfl) ⟨2481821, by rfl⟩ : syracuseStep 3309095 = 4963643) B4963643
theorem B2580007 : Blo 1358498 2580007 := bstep (se 1 (by rfl) ⟨1935005, by rfl⟩ : syracuseStep 2580007 = 3870011) B3870011
theorem B1359399 : Blo 1358498 1359399 := bstep (se 1 (by rfl) ⟨1019549, by rfl⟩ : syracuseStep 1359399 = 2039099) B2039099
theorem B1359439 : Blo 1358498 1359439 := bstep (se 1 (by rfl) ⟨1019579, by rfl⟩ : syracuseStep 1359439 = 2039159) B2039159
theorem B2039375 : Blo 1358498 2039375 := bstep (se 1 (by rfl) ⟨1529531, by rfl⟩ : syracuseStep 2039375 = 3059063) B3059063
theorem B1359455 : Blo 1358498 1359455 := bstep (se 1 (by rfl) ⟨1019591, by rfl⟩ : syracuseStep 1359455 = 2039183) B2039183
theorem B1359483 : Blo 1358498 1359483 := bstep (se 1 (by rfl) ⟨1019612, by rfl⟩ : syracuseStep 1359483 = 2039225) B2039225
theorem B15482501 : Blo 1358498 15482501 := bstep (se 4 (by rfl) ⟨1451484, by rfl⟩ : syracuseStep 15482501 = 2902969) B2902969
theorem B1359535 : Blo 1358498 1359535 := bstep (se 1 (by rfl) ⟨1019651, by rfl⟩ : syracuseStep 1359535 = 2039303) B2039303
theorem B2293447 : Blo 1358498 2293447 := bstep (se 1 (by rfl) ⟨1720085, by rfl⟩ : syracuseStep 2293447 = 3440171) B3440171
theorem B2580167 : Blo 1358498 2580167 := bstep (se 1 (by rfl) ⟨1935125, by rfl⟩ : syracuseStep 2580167 = 3870251) B3870251
theorem B1359559 : Blo 1358498 1359559 := bstep (se 1 (by rfl) ⟨1019669, by rfl⟩ : syracuseStep 1359559 = 2039339) B2039339
theorem B2039495 : Blo 1358498 2039495 := bstep (se 1 (by rfl) ⟨1529621, by rfl⟩ : syracuseStep 2039495 = 3059243) B3059243
theorem B1359579 : Blo 1358498 1359579 := bstep (se 1 (by rfl) ⟨1019684, by rfl⟩ : syracuseStep 1359579 = 2039369) B2039369
theorem B6528761 : Blo 1358498 6528761 := bstep (se 2 (by rfl) ⟨2448285, by rfl⟩ : syracuseStep 6528761 = 4896571) B4896571
theorem B1359655 : Blo 1358498 1359655 := bstep (se 1 (by rfl) ⟨1019741, by rfl⟩ : syracuseStep 1359655 = 2039483) B2039483
theorem B1359695 : Blo 1358498 1359695 := bstep (se 1 (by rfl) ⟨1019771, by rfl⟩ : syracuseStep 1359695 = 2039543) B2039543
theorem B1359711 : Blo 1358498 1359711 := bstep (se 1 (by rfl) ⟨1019783, by rfl⟩ : syracuseStep 1359711 = 2039567) B2039567
theorem B2293609 : Blo 1358498 2293609 := bstep (se 2 (by rfl) ⟨860103, by rfl⟩ : syracuseStep 2293609 = 1720207) B1720207
theorem B2039657 : Blo 1358498 2039657 := bstep (se 2 (by rfl) ⟨764871, by rfl⟩ : syracuseStep 2039657 = 1529743) B1529743
theorem B1359739 : Blo 1358498 1359739 := bstep (se 1 (by rfl) ⟨1019804, by rfl⟩ : syracuseStep 1359739 = 2039609) B2039609
theorem B1359791 : Blo 1358498 1359791 := bstep (se 1 (by rfl) ⟨1019843, by rfl⟩ : syracuseStep 1359791 = 2039687) B2039687
theorem B2039735 : Blo 1358498 2039735 := bstep (se 1 (by rfl) ⟨1529801, by rfl⟩ : syracuseStep 2039735 = 3059603) B3059603
theorem B1359815 : Blo 1358498 1359815 := bstep (se 1 (by rfl) ⟨1019861, by rfl⟩ : syracuseStep 1359815 = 2039723) B2039723
theorem B1359835 : Blo 1358498 1359835 := bstep (se 1 (by rfl) ⟨1019876, by rfl⟩ : syracuseStep 1359835 = 2039753) B2039753
theorem B2039771 : Blo 1358498 2039771 := bstep (se 1 (by rfl) ⟨1529828, by rfl⟩ : syracuseStep 2039771 = 3059657) B3059657
theorem B8265881 : Blo 1358498 8265881 := bstep (se 2 (by rfl) ⟨3099705, by rfl⟩ : syracuseStep 8265881 = 6199411) B6199411
theorem B4587731 : Blo 1358498 4587731 := bstep (se 1 (by rfl) ⟨3440798, by rfl⟩ : syracuseStep 4587731 = 6881597) B6881597
theorem B1360159 : Blo 1358498 1360159 := bstep (se 1 (by rfl) ⟨1020119, by rfl⟩ : syracuseStep 1360159 = 2040239) B2040239
theorem B2040155 : Blo 1358498 2040155 := bstep (se 1 (by rfl) ⟨1530116, by rfl⟩ : syracuseStep 2040155 = 3060233) B3060233
theorem B1360219 : Blo 1358498 1360219 := bstep (se 1 (by rfl) ⟨1020164, by rfl⟩ : syracuseStep 1360219 = 2040329) B2040329
theorem B1360239 : Blo 1358498 1360239 := bstep (se 1 (by rfl) ⟨1020179, by rfl⟩ : syracuseStep 1360239 = 2040359) B2040359
theorem B2294183 : Blo 1358498 2294183 := bstep (se 1 (by rfl) ⟨1720637, by rfl⟩ : syracuseStep 2294183 = 3441275) B3441275
theorem B1360295 : Blo 1358498 1360295 := bstep (se 1 (by rfl) ⟨1020221, by rfl⟩ : syracuseStep 1360295 = 2040443) B2040443
theorem B52986329 : Blo 1358498 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B5161441 : Blo 1358498 5161441 := bstep (se 2 (by rfl) ⟨1935540, by rfl⟩ : syracuseStep 5161441 = 3871081) B3871081
theorem B4588001 : Blo 1358498 4588001 := bstep (se 2 (by rfl) ⟨1720500, by rfl⟩ : syracuseStep 4588001 = 3441001) B3441001
theorem B1360379 : Blo 1358498 1360379 := bstep (se 1 (by rfl) ⟨1020284, by rfl⟩ : syracuseStep 1360379 = 2040569) B2040569
theorem B15475211 : Blo 1358498 15475211 := bstep (se 1 (by rfl) ⟨11606408, by rfl⟩ : syracuseStep 15475211 = 23212817) B23212817
theorem B2581055 : Blo 1358498 2581055 := bstep (se 1 (by rfl) ⟨1935791, by rfl⟩ : syracuseStep 2581055 = 3871583) B3871583
theorem B2040383 : Blo 1358498 2040383 := bstep (se 1 (by rfl) ⟨1530287, by rfl⟩ : syracuseStep 2040383 = 3060575) B3060575
theorem B1360447 : Blo 1358498 1360447 := bstep (se 1 (by rfl) ⟨1020335, by rfl⟩ : syracuseStep 1360447 = 2040671) B2040671
theorem B1360455 : Blo 1358498 1360455 := bstep (se 1 (by rfl) ⟨1020341, by rfl⟩ : syracuseStep 1360455 = 2040683) B2040683
theorem B2294345 : Blo 1358498 2294345 := bstep (se 2 (by rfl) ⟨860379, by rfl⟩ : syracuseStep 2294345 = 1720759) B1720759
theorem B8708755 : Blo 1358498 8708755 := bstep (se 1 (by rfl) ⟨6531566, by rfl⟩ : syracuseStep 8708755 = 13063133) B13063133
theorem B5808793 : Blo 1358498 5808793 := bstep (se 2 (by rfl) ⟨2178297, by rfl⟩ : syracuseStep 5808793 = 4356595) B4356595
theorem B2040503 : Blo 1358498 2040503 := bstep (se 1 (by rfl) ⟨1530377, by rfl⟩ : syracuseStep 2040503 = 3060755) B3060755
theorem B3441487 : Blo 1358498 3441487 := bstep (se 1 (by rfl) ⟨2581115, by rfl⟩ : syracuseStep 3441487 = 5162231) B5162231
theorem B2040731 : Blo 1358498 2040731 := bstep (se 1 (by rfl) ⟨1530548, by rfl⟩ : syracuseStep 2040731 = 3061097) B3061097
theorem B3441761 : Blo 1358498 3441761 := bstep (se 2 (by rfl) ⟨1290660, by rfl⟩ : syracuseStep 3441761 = 2581321) B2581321
theorem B2581723 : Blo 1358498 2581723 := bstep (se 1 (by rfl) ⟨1936292, by rfl⟩ : syracuseStep 2581723 = 3872585) B3872585
theorem B2450665 : Blo 1358498 2450665 := bstep (se 2 (by rfl) ⟨918999, by rfl⟩ : syracuseStep 2450665 = 1837999) B1837999
theorem B3056993 : Blo 1358498 3056993 := bstep (se 2 (by rfl) ⟨1146372, by rfl⟩ : syracuseStep 3056993 = 2292745) B2292745
theorem B3057083 : Blo 1358498 3057083 := bstep (se 1 (by rfl) ⟨2292812, by rfl⟩ : syracuseStep 3057083 = 4585625) B4585625
theorem B3442135 : Blo 1358498 3442135 := bstep (se 1 (by rfl) ⟨2581601, by rfl⟩ : syracuseStep 3442135 = 5163203) B5163203
theorem B1451515 : Blo 1358498 1451515 := bstep (se 1 (by rfl) ⟨1088636, by rfl⟩ : syracuseStep 1451515 = 2177273) B2177273
theorem B3057209 : Blo 1358498 3057209 := bstep (se 2 (by rfl) ⟨1146453, by rfl⟩ : syracuseStep 3057209 = 2292907) B2292907
theorem B11609689 : Blo 1358498 11609689 := bstep (se 2 (by rfl) ⟨4353633, by rfl⟩ : syracuseStep 11609689 = 8707267) B8707267
theorem B2582111 : Blo 1358498 2582111 := bstep (se 1 (by rfl) ⟨1936583, by rfl⟩ : syracuseStep 2582111 = 3873167) B3873167
theorem B2295391 : Blo 1358498 2295391 := bstep (se 1 (by rfl) ⟨1721543, by rfl⟩ : syracuseStep 2295391 = 3443087) B3443087
theorem B4589243 : Blo 1358498 4589243 := bstep (se 1 (by rfl) ⟨3441932, by rfl⟩ : syracuseStep 4589243 = 6883865) B6883865
theorem B2901739 : Blo 1358498 2901739 := bstep (se 1 (by rfl) ⟨2176304, by rfl⟩ : syracuseStep 2901739 = 4352609) B4352609
theorem B3442439 : Blo 1358498 3442439 := bstep (se 1 (by rfl) ⟨2581829, by rfl⟩ : syracuseStep 3442439 = 5163659) B5163659
theorem B1836841 : Blo 1358498 1836841 := bstep (se 2 (by rfl) ⟨688815, by rfl⟩ : syracuseStep 1836841 = 1377631) B1377631
theorem B2295607 : Blo 1358498 2295607 := bstep (se 1 (by rfl) ⟨1721705, by rfl⟩ : syracuseStep 2295607 = 3443411) B3443411
theorem B10324097 : Blo 1358498 10324097 := bstep (se 2 (by rfl) ⟨3871536, by rfl⟩ : syracuseStep 10324097 = 7743073) B7743073
theorem B3057875 : Blo 1358498 3057875 := bstep (se 1 (by rfl) ⟨2293406, by rfl⟩ : syracuseStep 3057875 = 4586813) B4586813
theorem B3057929 : Blo 1358498 3057929 := bstep (se 2 (by rfl) ⟨1146723, by rfl⟩ : syracuseStep 3057929 = 2293447) B2293447
theorem B2206063 : Blo 1358498 2206063 := bstep (se 1 (by rfl) ⟨1654547, by rfl⟩ : syracuseStep 2206063 = 3309095) B3309095
theorem B29395331 : Blo 1358498 29395331 := bstep (se 1 (by rfl) ⟨22046498, by rfl⟩ : syracuseStep 29395331 = 44092997) B44092997
theorem B2902483 : Blo 1358498 2902483 := bstep (se 1 (by rfl) ⟨2176862, by rfl⟩ : syracuseStep 2902483 = 4353725) B4353725
theorem B3058145 : Blo 1358498 3058145 := bstep (se 2 (by rfl) ⟨1146804, by rfl⟩ : syracuseStep 3058145 = 2293609) B2293609
theorem B4352507 : Blo 1358498 4352507 := bstep (se 1 (by rfl) ⟨3264380, by rfl⟩ : syracuseStep 4352507 = 6528761) B6528761
theorem B3443219 : Blo 1358498 3443219 := bstep (se 1 (by rfl) ⟨2582414, by rfl⟩ : syracuseStep 3443219 = 5164829) B5164829
theorem B3058451 : Blo 1358498 3058451 := bstep (se 1 (by rfl) ⟨2293838, by rfl⟩ : syracuseStep 3058451 = 4587677) B4587677
theorem B66169871 : Blo 1358498 66169871 := bstep (se 1 (by rfl) ⟨49627403, by rfl⟩ : syracuseStep 66169871 = 99254807) B99254807
theorem B11619395 : Blo 1358498 11619395 := bstep (se 1 (by rfl) ⟨8714546, by rfl⟩ : syracuseStep 11619395 = 17429093) B17429093
theorem B10325069 : Blo 1358498 10325069 := bstep (se 3 (by rfl) ⟨1935950, by rfl⟩ : syracuseStep 10325069 = 3871901) B3871901
theorem B3058811 : Blo 1358498 3058811 := bstep (se 1 (by rfl) ⟨2294108, by rfl⟩ : syracuseStep 3058811 = 4588217) B4588217
theorem B4713661 : Blo 1358498 4713661 := bstep (se 3 (by rfl) ⟨883811, by rfl⟩ : syracuseStep 4713661 = 1767623) B1767623
theorem B3058937 : Blo 1358498 3058937 := bstep (se 2 (by rfl) ⟨1147101, by rfl⟩ : syracuseStep 3058937 = 2294203) B2294203
theorem B2755871 : Blo 1358498 2755871 := bstep (se 1 (by rfl) ⟨2066903, by rfl⟩ : syracuseStep 2755871 = 4133807) B4133807
theorem B186182957 : Blo 1358498 186182957 := bstep (se 3 (by rfl) ⟨34909304, by rfl⟩ : syracuseStep 186182957 = 69818609) B69818609
theorem B6884675 : Blo 1358498 6884675 := bstep (se 1 (by rfl) ⟨5163506, by rfl⟩ : syracuseStep 6884675 = 10327013) B10327013
theorem B3059081 : Blo 1358498 3059081 := bstep (se 2 (by rfl) ⟨1147155, by rfl⟩ : syracuseStep 3059081 = 2294311) B2294311
theorem B3059207 : Blo 1358498 3059207 := bstep (se 1 (by rfl) ⟨2294405, by rfl⟩ : syracuseStep 3059207 = 4588811) B4588811
theorem B4591187 : Blo 1358498 4591187 := bstep (se 1 (by rfl) ⟨3443390, by rfl⟩ : syracuseStep 4591187 = 6886781) B6886781
theorem B7548511 : Blo 1358498 7548511 := bstep (se 1 (by rfl) ⟨5661383, by rfl⟩ : syracuseStep 7548511 = 11322767) B11322767
theorem B3059387 : Blo 1358498 3059387 := bstep (se 1 (by rfl) ⟨2294540, by rfl⟩ : syracuseStep 3059387 = 4589081) B4589081
theorem B3870443 : Blo 1358498 3870443 := bstep (se 1 (by rfl) ⟨2902832, by rfl⟩ : syracuseStep 3870443 = 5805665) B5805665
theorem B106000109 : Blo 1358498 106000109 := bstep (se 3 (by rfl) ⟨19875020, by rfl⟩ : syracuseStep 106000109 = 39750041) B39750041
theorem B4132649 : Blo 1358498 4132649 := bstep (se 2 (by rfl) ⟨1549743, by rfl⟩ : syracuseStep 4132649 = 3099487) B3099487
theorem B6885161 : Blo 1358498 6885161 := bstep (se 2 (by rfl) ⟨2581935, by rfl⟩ : syracuseStep 6885161 = 5163871) B5163871
theorem B4353839 : Blo 1358498 4353839 := bstep (se 1 (by rfl) ⟨3265379, by rfl⟩ : syracuseStep 4353839 = 6530759) B6530759
theorem B3059513 : Blo 1358498 3059513 := bstep (se 2 (by rfl) ⟨1147317, by rfl⟩ : syracuseStep 3059513 = 2294635) B2294635
theorem B15708113 : Blo 1358498 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B14708737 : Blo 1358498 14708737 := bstep (se 2 (by rfl) ⟨5515776, by rfl⟩ : syracuseStep 14708737 = 11031553) B11031553
theorem B10326041 : Blo 1358498 10326041 := bstep (se 2 (by rfl) ⟨3872265, by rfl⟩ : syracuseStep 10326041 = 7744531) B7744531
theorem B7737515 : Blo 1358498 7737515 := bstep (se 1 (by rfl) ⟨5803136, by rfl⟩ : syracuseStep 7737515 = 11606273) B11606273
theorem B2904329 : Blo 1358498 2904329 := bstep (se 2 (by rfl) ⟨1089123, by rfl⟩ : syracuseStep 2904329 = 2178247) B2178247
theorem B6877547 : Blo 1358498 6877547 := bstep (se 1 (by rfl) ⟨5158160, by rfl⟩ : syracuseStep 6877547 = 10316321) B10316321
theorem B3060143 : Blo 1358498 3060143 := bstep (se 1 (by rfl) ⟨2295107, by rfl⟩ : syracuseStep 3060143 = 4590215) B4590215
theorem B7852463 : Blo 1358498 7852463 := bstep (se 1 (by rfl) ⟨5889347, by rfl⟩ : syracuseStep 7852463 = 11778695) B11778695
theorem B3101111 : Blo 1358498 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B3060179 : Blo 1358498 3060179 := bstep (se 1 (by rfl) ⟨2295134, by rfl⟩ : syracuseStep 3060179 = 4590269) B4590269
theorem B3060287 : Blo 1358498 3060287 := bstep (se 1 (by rfl) ⟨2295215, by rfl⟩ : syracuseStep 3060287 = 4590431) B4590431
theorem B3060395 : Blo 1358498 3060395 := bstep (se 1 (by rfl) ⟨2295296, by rfl⟩ : syracuseStep 3060395 = 4590593) B4590593
theorem B55816877 : Blo 1358498 55816877 := bstep (se 3 (by rfl) ⟨10465664, by rfl⟩ : syracuseStep 55816877 = 20931329) B20931329
theorem B5804743 : Blo 1358498 5804743 := bstep (se 1 (by rfl) ⟨4353557, by rfl⟩ : syracuseStep 5804743 = 8707115) B8707115
theorem B39179011 : Blo 1358498 39179011 := bstep (se 1 (by rfl) ⟨29384258, by rfl⟩ : syracuseStep 39179011 = 58768517) B58768517
theorem B8262479 : Blo 1358498 8262479 := bstep (se 1 (by rfl) ⟨6196859, by rfl⟩ : syracuseStep 8262479 = 12393719) B12393719
theorem B6976475 : Blo 1358498 6976475 := bstep (se 1 (by rfl) ⟨5232356, by rfl⟩ : syracuseStep 6976475 = 10464713) B10464713
theorem B1528807 : Blo 1358498 1528807 := bstep (se 1 (by rfl) ⟨1146605, by rfl⟩ : syracuseStep 1528807 = 2293211) B2293211
theorem B3584999 : Blo 1358498 3584999 := bstep (se 1 (by rfl) ⟨2688749, by rfl⟩ : syracuseStep 3584999 = 5377499) B5377499
theorem B6886457 : Blo 1358498 6886457 := bstep (se 2 (by rfl) ⟨2582421, by rfl⟩ : syracuseStep 6886457 = 5164843) B5164843
theorem B3060935 : Blo 1358498 3060935 := bstep (se 1 (by rfl) ⟨2295701, by rfl⟩ : syracuseStep 3060935 = 4591403) B4591403
theorem B11777303 : Blo 1358498 11777303 := bstep (se 1 (by rfl) ⟨8832977, by rfl⟩ : syracuseStep 11777303 = 17665955) B17665955
theorem B3061115 : Blo 1358498 3061115 := bstep (se 1 (by rfl) ⟨2295836, by rfl⟩ : syracuseStep 3061115 = 4591673) B4591673
theorem B10319237 : Blo 1358498 10319237 := bstep (se 4 (by rfl) ⟨967428, by rfl⟩ : syracuseStep 10319237 = 1934857) B1934857
theorem B4896139 : Blo 1358498 4896139 := bstep (se 1 (by rfl) ⟨3672104, by rfl⟩ : syracuseStep 4896139 = 7344209) B7344209
theorem B11031947 : Blo 1358498 11031947 := bstep (se 1 (by rfl) ⟨8273960, by rfl⟩ : syracuseStep 11031947 = 16547921) B16547921
theorem B10327499 : Blo 1358498 10327499 := bstep (se 1 (by rfl) ⟨7745624, by rfl⟩ : syracuseStep 10327499 = 15491249) B15491249
theorem B2176607 : Blo 1358498 2176607 := bstep (se 1 (by rfl) ⟨1632455, by rfl⟩ : syracuseStep 2176607 = 3264911) B3264911
theorem B4896443 : Blo 1358498 4896443 := bstep (se 1 (by rfl) ⟨3672332, by rfl⟩ : syracuseStep 4896443 = 7344665) B7344665
theorem B6879005 : Blo 1358498 6879005 := bstep (se 3 (by rfl) ⟨1289813, by rfl⟩ : syracuseStep 6879005 = 2579627) B2579627
theorem B6535201 : Blo 1358498 6535201 := bstep (se 2 (by rfl) ⟨2450700, by rfl⟩ : syracuseStep 6535201 = 4901401) B4901401
theorem B2038025 : Blo 1358498 2038025 := bstep (se 2 (by rfl) ⟨764259, by rfl⟩ : syracuseStep 2038025 = 1528519) B1528519
theorem B7444759 : Blo 1358498 7444759 := bstep (se 1 (by rfl) ⟨5583569, by rfl⟩ : syracuseStep 7444759 = 11167139) B11167139
theorem B2038127 : Blo 1358498 2038127 := bstep (se 1 (by rfl) ⟨1528595, by rfl⟩ : syracuseStep 2038127 = 3057191) B3057191
theorem B13236605 : Blo 1358498 13236605 := bstep (se 3 (by rfl) ⟨2481863, by rfl⟩ : syracuseStep 13236605 = 4963727) B4963727
theorem B55810457 : Blo 1358498 55810457 := bstep (se 2 (by rfl) ⟨20928921, by rfl⟩ : syracuseStep 55810457 = 41857843) B41857843
theorem B4585895 : Blo 1358498 4585895 := bstep (se 1 (by rfl) ⟨3439421, by rfl⟩ : syracuseStep 4585895 = 6878843) B6878843
theorem B19872209 : Blo 1358498 19872209 := bstep (se 2 (by rfl) ⟨7452078, by rfl⟩ : syracuseStep 19872209 = 14904157) B14904157
theorem B2177599 : Blo 1358498 2177599 := bstep (se 1 (by rfl) ⟨1633199, by rfl⟩ : syracuseStep 2177599 = 3266399) B3266399
theorem B2038343 : Blo 1358498 2038343 := bstep (se 1 (by rfl) ⟨1528757, by rfl⟩ : syracuseStep 2038343 = 3057515) B3057515
theorem B4586057 : Blo 1358498 4586057 := bstep (se 2 (by rfl) ⟨1719771, by rfl⟩ : syracuseStep 4586057 = 3439543) B3439543
theorem B5159497 : Blo 1358498 5159497 := bstep (se 2 (by rfl) ⟨1934811, by rfl⟩ : syracuseStep 5159497 = 3869623) B3869623
theorem B3873359 : Blo 1358498 3873359 := bstep (se 1 (by rfl) ⟨2905019, by rfl⟩ : syracuseStep 3873359 = 5810039) B5810039
theorem B1530463 : Blo 1358498 1530463 := bstep (se 1 (by rfl) ⟨1147847, by rfl⟩ : syracuseStep 1530463 = 2295695) B2295695
theorem B2038379 : Blo 1358498 2038379 := bstep (se 1 (by rfl) ⟨1528784, by rfl⟩ : syracuseStep 2038379 = 3057569) B3057569
theorem B33094277 : Blo 1358498 33094277 := bstep (se 4 (by rfl) ⟨3102588, by rfl⟩ : syracuseStep 33094277 = 6205177) B6205177
theorem B6617821 : Blo 1358498 6617821 := bstep (se 3 (by rfl) ⟨1240841, by rfl⟩ : syracuseStep 6617821 = 2481683) B2481683
theorem B1358559 : Blo 1358498 1358559 := bstep (se 1 (by rfl) ⟨1018919, by rfl⟩ : syracuseStep 1358559 = 2037839) B2037839
theorem B1358639 : Blo 1358498 1358639 := bstep (se 1 (by rfl) ⟨1018979, by rfl⟩ : syracuseStep 1358639 = 2037959) B2037959
theorem B2038607 : Blo 1358498 2038607 := bstep (se 1 (by rfl) ⟨1528955, by rfl⟩ : syracuseStep 2038607 = 3057911) B3057911
theorem B1358747 : Blo 1358498 1358747 := bstep (se 1 (by rfl) ⟨1019060, by rfl⟩ : syracuseStep 1358747 = 2038121) B2038121
theorem B11025325 : Blo 1358498 11025325 := bstep (se 3 (by rfl) ⟨2067248, by rfl⟩ : syracuseStep 11025325 = 4134497) B4134497
theorem B6536123 : Blo 1358498 6536123 := bstep (se 1 (by rfl) ⟨4902092, by rfl⟩ : syracuseStep 6536123 = 9804185) B9804185
theorem B1358799 : Blo 1358498 1358799 := bstep (se 1 (by rfl) ⟨1019099, by rfl⟩ : syracuseStep 1358799 = 2038199) B2038199
theorem B1358823 : Blo 1358498 1358823 := bstep (se 1 (by rfl) ⟨1019117, by rfl⟩ : syracuseStep 1358823 = 2038235) B2038235
theorem B3439655 : Blo 1358498 3439655 := bstep (se 1 (by rfl) ⟨2579741, by rfl⟩ : syracuseStep 3439655 = 5159483) B5159483
theorem B6200509 : Blo 1358498 6200509 := bstep (se 3 (by rfl) ⟨1162595, by rfl⟩ : syracuseStep 6200509 = 2325191) B2325191
theorem B2039003 : Blo 1358498 2039003 := bstep (se 1 (by rfl) ⟨1529252, by rfl⟩ : syracuseStep 2039003 = 3058505) B3058505
theorem B7740683 : Blo 1358498 7740683 := bstep (se 1 (by rfl) ⟨5805512, by rfl⟩ : syracuseStep 7740683 = 11611025) B11611025
theorem B1359135 : Blo 1358498 1359135 := bstep (se 1 (by rfl) ⟨1019351, by rfl⟩ : syracuseStep 1359135 = 2038703) B2038703
theorem B1359195 : Blo 1358498 1359195 := bstep (se 1 (by rfl) ⟨1019396, by rfl⟩ : syracuseStep 1359195 = 2038793) B2038793
theorem B1359215 : Blo 1358498 1359215 := bstep (se 1 (by rfl) ⟨1019411, by rfl⟩ : syracuseStep 1359215 = 2038823) B2038823
theorem B3440009 : Blo 1358498 3440009 := bstep (se 2 (by rfl) ⟨1290003, by rfl⟩ : syracuseStep 3440009 = 2580007) B2580007
theorem B2039177 : Blo 1358498 2039177 := bstep (se 2 (by rfl) ⟨764691, by rfl⟩ : syracuseStep 2039177 = 1529383) B1529383
theorem B1359271 : Blo 1358498 1359271 := bstep (se 1 (by rfl) ⟨1019453, by rfl⟩ : syracuseStep 1359271 = 2038907) B2038907
theorem B2178503 : Blo 1358498 2178503 := bstep (se 1 (by rfl) ⟨1633877, by rfl⟩ : syracuseStep 2178503 = 3267755) B3267755
theorem B1359355 : Blo 1358498 1359355 := bstep (se 1 (by rfl) ⟨1019516, by rfl⟩ : syracuseStep 1359355 = 2039033) B2039033
theorem B1359423 : Blo 1358498 1359423 := bstep (se 1 (by rfl) ⟨1019567, by rfl⟩ : syracuseStep 1359423 = 2039135) B2039135
theorem B1359431 : Blo 1358498 1359431 := bstep (se 1 (by rfl) ⟨1019573, by rfl⟩ : syracuseStep 1359431 = 2039147) B2039147
theorem B1359583 : Blo 1358498 1359583 := bstep (se 1 (by rfl) ⟨1019687, by rfl⟩ : syracuseStep 1359583 = 2039375) B2039375
theorem B2039531 : Blo 1358498 2039531 := bstep (se 1 (by rfl) ⟨1529648, by rfl⟩ : syracuseStep 2039531 = 3059297) B3059297
theorem B10321667 : Blo 1358498 10321667 := bstep (se 1 (by rfl) ⟨7741250, by rfl⟩ : syracuseStep 10321667 = 15482501) B15482501
theorem B2580265 : Blo 1358498 2580265 := bstep (se 2 (by rfl) ⟨967599, by rfl⟩ : syracuseStep 2580265 = 1935199) B1935199
theorem B1720111 : Blo 1358498 1720111 := bstep (se 1 (by rfl) ⟨1290083, by rfl⟩ : syracuseStep 1720111 = 2580167) B2580167
theorem B1359663 : Blo 1358498 1359663 := bstep (se 1 (by rfl) ⟨1019747, by rfl⟩ : syracuseStep 1359663 = 2039495) B2039495
theorem B10329929 : Blo 1358498 10329929 := bstep (se 2 (by rfl) ⟨3873723, by rfl⟩ : syracuseStep 10329929 = 7747447) B7747447
theorem B1359771 : Blo 1358498 1359771 := bstep (se 1 (by rfl) ⟨1019828, by rfl⟩ : syracuseStep 1359771 = 2039657) B2039657
theorem B1359823 : Blo 1358498 1359823 := bstep (se 1 (by rfl) ⟨1019867, by rfl⟩ : syracuseStep 1359823 = 2039735) B2039735
theorem B2039759 : Blo 1358498 2039759 := bstep (se 1 (by rfl) ⟨1529819, by rfl⟩ : syracuseStep 2039759 = 3059639) B3059639
theorem B1359847 : Blo 1358498 1359847 := bstep (se 1 (by rfl) ⟨1019885, by rfl⟩ : syracuseStep 1359847 = 2039771) B2039771
theorem B19611649 : Blo 1358498 19611649 := bstep (se 2 (by rfl) ⟨7354368, by rfl⟩ : syracuseStep 19611649 = 14708737) B14708737
theorem B1360103 : Blo 1358498 1360103 := bstep (se 1 (by rfl) ⟨1020077, by rfl⟩ : syracuseStep 1360103 = 2040155) B2040155
theorem B2040095 : Blo 1358498 2040095 := bstep (se 1 (by rfl) ⟨1530071, by rfl⟩ : syracuseStep 2040095 = 3060143) B3060143
theorem B5234975 : Blo 1358498 5234975 := bstep (se 1 (by rfl) ⟨3926231, by rfl⟩ : syracuseStep 5234975 = 7852463) B7852463
theorem B2040119 : Blo 1358498 2040119 := bstep (se 1 (by rfl) ⟨1530089, by rfl⟩ : syracuseStep 2040119 = 3060179) B3060179
theorem B35324219 : Blo 1358498 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B1720703 : Blo 1358498 1720703 := bstep (se 1 (by rfl) ⟨1290527, by rfl⟩ : syracuseStep 1720703 = 2581055) B2581055
theorem B2040191 : Blo 1358498 2040191 := bstep (se 1 (by rfl) ⟨1530143, by rfl⟩ : syracuseStep 2040191 = 3060287) B3060287
theorem B1360255 : Blo 1358498 1360255 := bstep (se 1 (by rfl) ⟨1020191, by rfl⟩ : syracuseStep 1360255 = 2040383) B2040383
theorem B2040263 : Blo 1358498 2040263 := bstep (se 1 (by rfl) ⟨1530197, by rfl⟩ : syracuseStep 2040263 = 3060395) B3060395
theorem B1360335 : Blo 1358498 1360335 := bstep (se 1 (by rfl) ⟨1020251, by rfl⟩ : syracuseStep 1360335 = 2040503) B2040503
theorem B2941417 : Blo 1358498 2941417 := bstep (se 2 (by rfl) ⟨1103031, by rfl⟩ : syracuseStep 2941417 = 2206063) B2206063
theorem B1360487 : Blo 1358498 1360487 := bstep (se 1 (by rfl) ⟨1020365, by rfl⟩ : syracuseStep 1360487 = 2040731) B2040731
theorem B6881921 : Blo 1358498 6881921 := bstep (se 2 (by rfl) ⟨2580720, by rfl⟩ : syracuseStep 6881921 = 5161441) B5161441
theorem B2294507 : Blo 1358498 2294507 := bstep (se 1 (by rfl) ⟨1720880, by rfl⟩ : syracuseStep 2294507 = 3441761) B3441761
theorem B2040617 : Blo 1358498 2040617 := bstep (se 2 (by rfl) ⟨765231, by rfl⟩ : syracuseStep 2040617 = 1530463) B1530463
theorem B2040623 : Blo 1358498 2040623 := bstep (se 1 (by rfl) ⟨1530467, by rfl⟩ : syracuseStep 2040623 = 3060935) B3060935
theorem B2040743 : Blo 1358498 2040743 := bstep (se 1 (by rfl) ⟨1530557, by rfl⟩ : syracuseStep 2040743 = 3061115) B3061115
theorem B8823761 : Blo 1358498 8823761 := bstep (se 2 (by rfl) ⟨3308910, by rfl⟩ : syracuseStep 8823761 = 6617821) B6617821
theorem B1451071 : Blo 1358498 1451071 := bstep (se 1 (by rfl) ⟨1088303, by rfl⟩ : syracuseStep 1451071 = 2176607) B2176607
theorem B1721407 : Blo 1358498 1721407 := bstep (se 1 (by rfl) ⟨1291055, by rfl⟩ : syracuseStep 1721407 = 2582111) B2582111
theorem B4588649 : Blo 1358498 4588649 := bstep (se 2 (by rfl) ⟨1720743, by rfl⟩ : syracuseStep 4588649 = 3441487) B3441487
theorem B2294959 : Blo 1358498 2294959 := bstep (se 1 (by rfl) ⟨1721219, by rfl⟩ : syracuseStep 2294959 = 3442439) B3442439
theorem B6882731 : Blo 1358498 6882731 := bstep (se 1 (by rfl) ⟨5162048, by rfl⟩ : syracuseStep 6882731 = 10324097) B10324097
theorem B6284881 : Blo 1358498 6284881 := bstep (se 2 (by rfl) ⟨2356830, by rfl⟩ : syracuseStep 6284881 = 4713661) B4713661
theorem B8267345 : Blo 1358498 8267345 := bstep (se 2 (by rfl) ⟨3100254, by rfl⟩ : syracuseStep 8267345 = 6200509) B6200509
theorem B8824403 : Blo 1358498 8824403 := bstep (se 1 (by rfl) ⟨6618302, by rfl⟩ : syracuseStep 8824403 = 13236605) B13236605
theorem B19596887 : Blo 1358498 19596887 := bstep (se 1 (by rfl) ⟨14697665, by rfl⟩ : syracuseStep 19596887 = 29395331) B29395331
theorem B3057263 : Blo 1358498 3057263 := bstep (se 1 (by rfl) ⟨2292947, by rfl⟩ : syracuseStep 3057263 = 4585895) B4585895
theorem B3442297 : Blo 1358498 3442297 := bstep (se 2 (by rfl) ⟨1290861, by rfl⟩ : syracuseStep 3442297 = 2581723) B2581723
theorem B2901671 : Blo 1358498 2901671 := bstep (se 1 (by rfl) ⟨2176253, by rfl⟩ : syracuseStep 2901671 = 4352507) B4352507
theorem B2295479 : Blo 1358498 2295479 := bstep (se 1 (by rfl) ⟨1721609, by rfl⟩ : syracuseStep 2295479 = 3443219) B3443219
theorem B3057371 : Blo 1358498 3057371 := bstep (se 1 (by rfl) ⟨2293028, by rfl⟩ : syracuseStep 3057371 = 4586057) B4586057
theorem B22062851 : Blo 1358498 22062851 := bstep (se 1 (by rfl) ⟨16547138, by rfl⟩ : syracuseStep 22062851 = 33094277) B33094277
theorem B4589513 : Blo 1358498 4589513 := bstep (se 2 (by rfl) ⟨1721067, by rfl⟩ : syracuseStep 4589513 = 3442135) B3442135
theorem B1935353 : Blo 1358498 1935353 := bstep (se 2 (by rfl) ⟨725757, by rfl⟩ : syracuseStep 1935353 = 1451515) B1451515
theorem B6883379 : Blo 1358498 6883379 := bstep (se 1 (by rfl) ⟨5162534, by rfl⟩ : syracuseStep 6883379 = 10325069) B10325069
theorem B1837247 : Blo 1358498 1837247 := bstep (se 1 (by rfl) ⟨1377935, by rfl⟩ : syracuseStep 1837247 = 2755871) B2755871
theorem B4589783 : Blo 1358498 4589783 := bstep (se 1 (by rfl) ⟨3442337, by rfl⟩ : syracuseStep 4589783 = 6884675) B6884675
theorem B1452335 : Blo 1358498 1452335 := bstep (se 1 (by rfl) ⟨1089251, by rfl⟩ : syracuseStep 1452335 = 2178503) B2178503
theorem B3868985 : Blo 1358498 3868985 := bstep (se 2 (by rfl) ⟨1450869, by rfl⟩ : syracuseStep 3868985 = 2901739) B2901739
theorem B70666739 : Blo 1358498 70666739 := bstep (se 1 (by rfl) ⟨53000054, by rfl⟩ : syracuseStep 70666739 = 106000109) B106000109
theorem B2755099 : Blo 1358498 2755099 := bstep (se 1 (by rfl) ⟨2066324, by rfl⟩ : syracuseStep 2755099 = 4132649) B4132649
theorem B4590107 : Blo 1358498 4590107 := bstep (se 1 (by rfl) ⟨3442580, by rfl⟩ : syracuseStep 4590107 = 6885161) B6885161
theorem B2902559 : Blo 1358498 2902559 := bstep (se 1 (by rfl) ⟨2176919, by rfl⟩ : syracuseStep 2902559 = 4353839) B4353839
theorem B10472075 : Blo 1358498 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B6884027 : Blo 1358498 6884027 := bstep (se 1 (by rfl) ⟨5163020, by rfl⟩ : syracuseStep 6884027 = 10326041) B10326041
theorem B3058487 : Blo 1358498 3058487 := bstep (se 1 (by rfl) ⟨2293865, by rfl⟩ : syracuseStep 3058487 = 4587731) B4587731
theorem B1936219 : Blo 1358498 1936219 := bstep (se 1 (by rfl) ⟨1452164, by rfl⟩ : syracuseStep 1936219 = 2904329) B2904329
theorem B2067407 : Blo 1358498 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B3058667 : Blo 1358498 3058667 := bstep (se 1 (by rfl) ⟨2294000, by rfl⟩ : syracuseStep 3058667 = 4588001) B4588001
theorem B10316807 : Blo 1358498 10316807 := bstep (se 1 (by rfl) ⟨7737605, by rfl⟩ : syracuseStep 10316807 = 15475211) B15475211
theorem B37211251 : Blo 1358498 37211251 := bstep (se 1 (by rfl) ⟨27908438, by rfl⟩ : syracuseStep 37211251 = 55816877) B55816877
theorem B5508319 : Blo 1358498 5508319 := bstep (se 1 (by rfl) ⟨4131239, by rfl⟩ : syracuseStep 5508319 = 8262479) B8262479
theorem B3869977 : Blo 1358498 3869977 := bstep (se 2 (by rfl) ⟨1451241, by rfl⟩ : syracuseStep 3869977 = 2902483) B2902483
theorem B4590971 : Blo 1358498 4590971 := bstep (se 1 (by rfl) ⟨3443228, by rfl⟩ : syracuseStep 4590971 = 6886457) B6886457
theorem B2903465 : Blo 1358498 2903465 := bstep (se 2 (by rfl) ⟨1088799, by rfl⟩ : syracuseStep 2903465 = 2177599) B2177599
theorem B496487885 : Blo 1358498 496487885 := bstep (se 3 (by rfl) ⟨93091478, by rfl⟩ : syracuseStep 496487885 = 186182957) B186182957
theorem B7851535 : Blo 1358498 7851535 := bstep (se 1 (by rfl) ⟨5888651, by rfl⟩ : syracuseStep 7851535 = 11777303) B11777303
theorem B11611673 : Blo 1358498 11611673 := bstep (se 2 (by rfl) ⟨4354377, by rfl⟩ : syracuseStep 11611673 = 8708755) B8708755
theorem B7745057 : Blo 1358498 7745057 := bstep (se 2 (by rfl) ⟨2904396, by rfl⟩ : syracuseStep 7745057 = 5808793) B5808793
theorem B6884999 : Blo 1358498 6884999 := bstep (se 1 (by rfl) ⟨5163749, by rfl⟩ : syracuseStep 6884999 = 10327499) B10327499
theorem B3264295 : Blo 1358498 3264295 := bstep (se 1 (by rfl) ⟨2448221, by rfl⟩ : syracuseStep 3264295 = 4896443) B4896443
theorem B3059495 : Blo 1358498 3059495 := bstep (se 1 (by rfl) ⟨2294621, by rfl⟩ : syracuseStep 3059495 = 4589243) B4589243
theorem B7746263 : Blo 1358498 7746263 := bstep (se 1 (by rfl) ⟨5809697, by rfl⟩ : syracuseStep 7746263 = 11619395) B11619395
theorem B15479585 : Blo 1358498 15479585 := bstep (se 2 (by rfl) ⟨5804844, by rfl⟩ : syracuseStep 15479585 = 11609689) B11609689
theorem B10064681 : Blo 1358498 10064681 := bstep (se 2 (by rfl) ⟨3774255, by rfl⟩ : syracuseStep 10064681 = 7548511) B7548511
theorem B3060521 : Blo 1358498 3060521 := bstep (se 2 (by rfl) ⟨1147695, by rfl⟩ : syracuseStep 3060521 = 2295391) B2295391
theorem B3060791 : Blo 1358498 3060791 := bstep (se 1 (by rfl) ⟨2295593, by rfl⟩ : syracuseStep 3060791 = 4591187) B4591187
theorem B3060809 : Blo 1358498 3060809 := bstep (se 2 (by rfl) ⟨1147803, by rfl⟩ : syracuseStep 3060809 = 2295607) B2295607
theorem B6886619 : Blo 1358498 6886619 := bstep (se 1 (by rfl) ⟨5164964, by rfl⟩ : syracuseStep 6886619 = 10329929) B10329929
theorem B8713601 : Blo 1358498 8713601 := bstep (se 2 (by rfl) ⟨3267600, by rfl⟩ : syracuseStep 8713601 = 6535201) B6535201
theorem B5510587 : Blo 1358498 5510587 := bstep (se 1 (by rfl) ⟨4132940, by rfl⟩ : syracuseStep 5510587 = 8265881) B8265881
theorem B5158343 : Blo 1358498 5158343 := bstep (se 1 (by rfl) ⟨3868757, by rfl⟩ : syracuseStep 5158343 = 7737515) B7737515
theorem B4585031 : Blo 1358498 4585031 := bstep (se 1 (by rfl) ⟨3438773, by rfl⟩ : syracuseStep 4585031 = 6877547) B6877547
theorem B1529455 : Blo 1358498 1529455 := bstep (se 1 (by rfl) ⟨1147091, by rfl⟩ : syracuseStep 1529455 = 2294183) B2294183
theorem B9926345 : Blo 1358498 9926345 := bstep (se 2 (by rfl) ⟨3722379, by rfl⟩ : syracuseStep 9926345 = 7444759) B7444759
theorem B1529563 : Blo 1358498 1529563 := bstep (se 1 (by rfl) ⟨1147172, by rfl⟩ : syracuseStep 1529563 = 2294345) B2294345
theorem B4650983 : Blo 1358498 4650983 := bstep (se 1 (by rfl) ⟨3488237, by rfl⟩ : syracuseStep 4650983 = 6976475) B6976475
theorem B2389999 : Blo 1358498 2389999 := bstep (se 1 (by rfl) ⟨1792499, by rfl⟩ : syracuseStep 2389999 = 3584999) B3584999
theorem B6879329 : Blo 1358498 6879329 := bstep (se 2 (by rfl) ⟨2579748, by rfl⟩ : syracuseStep 6879329 = 5159497) B5159497
theorem B2037995 : Blo 1358498 2037995 := bstep (se 1 (by rfl) ⟨1528496, by rfl⟩ : syracuseStep 2037995 = 3056993) B3056993
theorem B6879491 : Blo 1358498 6879491 := bstep (se 1 (by rfl) ⟨5159618, by rfl⟩ : syracuseStep 6879491 = 10319237) B10319237
theorem B7354631 : Blo 1358498 7354631 := bstep (se 1 (by rfl) ⟨5515973, by rfl⟩ : syracuseStep 7354631 = 11031947) B11031947
theorem B7739657 : Blo 1358498 7739657 := bstep (se 2 (by rfl) ⟨2902371, by rfl⟩ : syracuseStep 7739657 = 5804743) B5804743
theorem B2038055 : Blo 1358498 2038055 := bstep (se 1 (by rfl) ⟨1528541, by rfl⟩ : syracuseStep 2038055 = 3057083) B3057083
theorem B52238681 : Blo 1358498 52238681 := bstep (se 2 (by rfl) ⟨19589505, by rfl⟩ : syracuseStep 52238681 = 39179011) B39179011
theorem B2038139 : Blo 1358498 2038139 := bstep (se 1 (by rfl) ⟨1528604, by rfl⟩ : syracuseStep 2038139 = 3057209) B3057209
theorem B4586003 : Blo 1358498 4586003 := bstep (se 1 (by rfl) ⟨3439502, by rfl⟩ : syracuseStep 4586003 = 6879005) B6879005
theorem B52992557 : Blo 1358498 52992557 := bstep (se 3 (by rfl) ⟨9936104, by rfl⟩ : syracuseStep 52992557 = 19872209) B19872209
theorem B2038409 : Blo 1358498 2038409 := bstep (se 2 (by rfl) ⟨764403, by rfl⟩ : syracuseStep 2038409 = 1528807) B1528807
theorem B2038583 : Blo 1358498 2038583 := bstep (se 1 (by rfl) ⟨1528937, by rfl⟩ : syracuseStep 2038583 = 3057875) B3057875
theorem B2038619 : Blo 1358498 2038619 := bstep (se 1 (by rfl) ⟨1528964, by rfl⟩ : syracuseStep 2038619 = 3057929) B3057929
theorem B1358683 : Blo 1358498 1358683 := bstep (se 1 (by rfl) ⟨1019012, by rfl⟩ : syracuseStep 1358683 = 2038025) B2038025
theorem B10328957 : Blo 1358498 10328957 := bstep (se 3 (by rfl) ⟨1936679, by rfl⟩ : syracuseStep 10328957 = 3873359) B3873359
theorem B1358751 : Blo 1358498 1358751 := bstep (se 1 (by rfl) ⟨1019063, by rfl⟩ : syracuseStep 1358751 = 2038127) B2038127
theorem B37206971 : Blo 1358498 37206971 := bstep (se 1 (by rfl) ⟨27905228, by rfl⟩ : syracuseStep 37206971 = 55810457) B55810457
theorem B3267553 : Blo 1358498 3267553 := bstep (se 2 (by rfl) ⟨1225332, by rfl⟩ : syracuseStep 3267553 = 2450665) B2450665
theorem B2038763 : Blo 1358498 2038763 := bstep (se 1 (by rfl) ⟨1529072, by rfl⟩ : syracuseStep 2038763 = 3058145) B3058145
theorem B1358895 : Blo 1358498 1358895 := bstep (se 1 (by rfl) ⟨1019171, by rfl⟩ : syracuseStep 1358895 = 2038343) B2038343
theorem B1358919 : Blo 1358498 1358919 := bstep (se 1 (by rfl) ⟨1019189, by rfl⟩ : syracuseStep 1358919 = 2038379) B2038379
theorem B2038967 : Blo 1358498 2038967 := bstep (se 1 (by rfl) ⟨1529225, by rfl⟩ : syracuseStep 2038967 = 3058451) B3058451
theorem B6528185 : Blo 1358498 6528185 := bstep (se 2 (by rfl) ⟨2448069, by rfl⟩ : syracuseStep 6528185 = 4896139) B4896139
theorem B1359071 : Blo 1358498 1359071 := bstep (se 1 (by rfl) ⟨1019303, by rfl⟩ : syracuseStep 1359071 = 2038607) B2038607
theorem B10321181 : Blo 1358498 10321181 := bstep (se 3 (by rfl) ⟨1935221, by rfl⟩ : syracuseStep 10321181 = 3870443) B3870443
theorem B4357415 : Blo 1358498 4357415 := bstep (se 1 (by rfl) ⟨3268061, by rfl⟩ : syracuseStep 4357415 = 6536123) B6536123
theorem B44113247 : Blo 1358498 44113247 := bstep (se 1 (by rfl) ⟨33084935, by rfl⟩ : syracuseStep 44113247 = 66169871) B66169871
theorem B2293103 : Blo 1358498 2293103 := bstep (se 1 (by rfl) ⟨1719827, by rfl⟩ : syracuseStep 2293103 = 3439655) B3439655
theorem B2039207 : Blo 1358498 2039207 := bstep (se 1 (by rfl) ⟨1529405, by rfl⟩ : syracuseStep 2039207 = 3058811) B3058811
theorem B1359335 : Blo 1358498 1359335 := bstep (se 1 (by rfl) ⟨1019501, by rfl⟩ : syracuseStep 1359335 = 2039003) B2039003
theorem B2039291 : Blo 1358498 2039291 := bstep (se 1 (by rfl) ⟨1529468, by rfl⟩ : syracuseStep 2039291 = 3058937) B3058937
theorem B5160455 : Blo 1358498 5160455 := bstep (se 1 (by rfl) ⟨3870341, by rfl⟩ : syracuseStep 5160455 = 7740683) B7740683
theorem B58801733 : Blo 1358498 58801733 := bstep (se 4 (by rfl) ⟨5512662, by rfl⟩ : syracuseStep 58801733 = 11025325) B11025325
theorem B2293339 : Blo 1358498 2293339 := bstep (se 1 (by rfl) ⟨1720004, by rfl⟩ : syracuseStep 2293339 = 3440009) B3440009
theorem B1359451 : Blo 1358498 1359451 := bstep (se 1 (by rfl) ⟨1019588, by rfl⟩ : syracuseStep 1359451 = 2039177) B2039177
theorem B2039387 : Blo 1358498 2039387 := bstep (se 1 (by rfl) ⟨1529540, by rfl⟩ : syracuseStep 2039387 = 3059081) B3059081
theorem B2039471 : Blo 1358498 2039471 := bstep (se 1 (by rfl) ⟨1529603, by rfl⟩ : syracuseStep 2039471 = 3059207) B3059207
theorem B2449121 : Blo 1358498 2449121 := bstep (se 2 (by rfl) ⟨918420, by rfl⟩ : syracuseStep 2449121 = 1836841) B1836841
theorem B3440353 : Blo 1358498 3440353 := bstep (se 2 (by rfl) ⟨1290132, by rfl⟩ : syracuseStep 3440353 = 2580265) B2580265
theorem B2293481 : Blo 1358498 2293481 := bstep (se 2 (by rfl) ⟨860055, by rfl⟩ : syracuseStep 2293481 = 1720111) B1720111
theorem B2039591 : Blo 1358498 2039591 := bstep (se 1 (by rfl) ⟨1529693, by rfl⟩ : syracuseStep 2039591 = 3059387) B3059387
theorem B1359687 : Blo 1358498 1359687 := bstep (se 1 (by rfl) ⟨1019765, by rfl⟩ : syracuseStep 1359687 = 2039531) B2039531
theorem B6881111 : Blo 1358498 6881111 := bstep (se 1 (by rfl) ⟨5160833, by rfl⟩ : syracuseStep 6881111 = 10321667) B10321667
theorem B2039675 : Blo 1358498 2039675 := bstep (se 1 (by rfl) ⟨1529756, by rfl⟩ : syracuseStep 2039675 = 3059513) B3059513
theorem B1359839 : Blo 1358498 1359839 := bstep (se 1 (by rfl) ⟨1019879, by rfl⟩ : syracuseStep 1359839 = 2039759) B2039759
theorem B26148865 : Blo 1358498 26148865 := bstep (se 2 (by rfl) ⟨9805824, by rfl⟩ : syracuseStep 26148865 = 19611649) B19611649
theorem B1360063 : Blo 1358498 1360063 := bstep (se 1 (by rfl) ⟨1020047, by rfl⟩ : syracuseStep 1360063 = 2040095) B2040095
theorem B3489983 : Blo 1358498 3489983 := bstep (se 1 (by rfl) ⟨2617487, by rfl⟩ : syracuseStep 3489983 = 5234975) B5234975
theorem B1360079 : Blo 1358498 1360079 := bstep (se 1 (by rfl) ⟨1020059, by rfl⟩ : syracuseStep 1360079 = 2040119) B2040119
theorem B1360127 : Blo 1358498 1360127 := bstep (se 1 (by rfl) ⟨1020095, by rfl⟩ : syracuseStep 1360127 = 2040191) B2040191
theorem B1360175 : Blo 1358498 1360175 := bstep (se 1 (by rfl) ⟨1020131, by rfl⟩ : syracuseStep 1360175 = 2040263) B2040263
theorem B4587947 : Blo 1358498 4587947 := bstep (se 1 (by rfl) ⟨3440960, by rfl⟩ : syracuseStep 4587947 = 6881921) B6881921
theorem B4899325 : Blo 1358498 4899325 := bstep (se 3 (by rfl) ⟨918623, by rfl⟩ : syracuseStep 4899325 = 1837247) B1837247
theorem B6709787 : Blo 1358498 6709787 := bstep (se 1 (by rfl) ⟨5032340, by rfl⟩ : syracuseStep 6709787 = 10064681) B10064681
theorem B2040347 : Blo 1358498 2040347 := bstep (se 1 (by rfl) ⟨1530260, by rfl⟩ : syracuseStep 2040347 = 3060521) B3060521
theorem B1360411 : Blo 1358498 1360411 := bstep (se 1 (by rfl) ⟨1020308, by rfl⟩ : syracuseStep 1360411 = 2040617) B2040617
theorem B1360415 : Blo 1358498 1360415 := bstep (se 1 (by rfl) ⟨1020311, by rfl⟩ : syracuseStep 1360415 = 2040623) B2040623
theorem B1360495 : Blo 1358498 1360495 := bstep (se 1 (by rfl) ⟨1020371, by rfl⟩ : syracuseStep 1360495 = 2040743) B2040743
theorem B5882507 : Blo 1358498 5882507 := bstep (se 1 (by rfl) ⟨4411880, by rfl⟩ : syracuseStep 5882507 = 8823761) B8823761
theorem B2040527 : Blo 1358498 2040527 := bstep (se 1 (by rfl) ⟨1530395, by rfl⟩ : syracuseStep 2040527 = 3060791) B3060791
theorem B2040539 : Blo 1358498 2040539 := bstep (se 1 (by rfl) ⟨1530404, by rfl⟩ : syracuseStep 2040539 = 3060809) B3060809
theorem B5809067 : Blo 1358498 5809067 := bstep (se 1 (by rfl) ⟨4356800, by rfl⟩ : syracuseStep 5809067 = 8713601) B8713601
theorem B4588487 : Blo 1358498 4588487 := bstep (se 1 (by rfl) ⟨3441365, by rfl⟩ : syracuseStep 4588487 = 6882731) B6882731
theorem B4588541 : Blo 1358498 4588541 := bstep (se 3 (by rfl) ⟨860351, by rfl⟩ : syracuseStep 4588541 = 1720703) B1720703
theorem B3056687 : Blo 1358498 3056687 := bstep (se 1 (by rfl) ⟨2292515, by rfl⟩ : syracuseStep 3056687 = 4585031) B4585031
theorem B7742573 : Blo 1358498 7742573 := bstep (se 3 (by rfl) ⟨1451732, by rfl⟩ : syracuseStep 7742573 = 2903465) B2903465
theorem B1934447 : Blo 1358498 1934447 := bstep (se 1 (by rfl) ⟨1450835, by rfl⟩ : syracuseStep 1934447 = 2901671) B2901671
theorem B2581625 : Blo 1358498 2581625 := bstep (se 2 (by rfl) ⟨968109, by rfl⟩ : syracuseStep 2581625 = 1936219) B1936219
theorem B1323967693 : Blo 1358498 1323967693 := bstep (se 3 (by rfl) ⟨248243942, by rfl⟩ : syracuseStep 1323967693 = 496487885) B496487885
theorem B4588919 : Blo 1358498 4588919 := bstep (se 1 (by rfl) ⟨3441689, by rfl⟩ : syracuseStep 4588919 = 6883379) B6883379
theorem B1934761 : Blo 1358498 1934761 := bstep (se 2 (by rfl) ⟨725535, by rfl⟩ : syracuseStep 1934761 = 1451071) B1451071
theorem B2295209 : Blo 1358498 2295209 := bstep (se 2 (by rfl) ⟨860703, by rfl⟩ : syracuseStep 2295209 = 1721407) B1721407
theorem B34825787 : Blo 1358498 34825787 := bstep (se 1 (by rfl) ⟨26119340, by rfl⟩ : syracuseStep 34825787 = 52238681) B52238681
theorem B3057335 : Blo 1358498 3057335 := bstep (se 1 (by rfl) ⟨2293001, by rfl⟩ : syracuseStep 3057335 = 4586003) B4586003
theorem B6981383 : Blo 1358498 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B4589351 : Blo 1358498 4589351 := bstep (se 1 (by rfl) ⟨3442013, by rfl⟩ : syracuseStep 4589351 = 6884027) B6884027
theorem B26470253 : Blo 1358498 26470253 := bstep (se 3 (by rfl) ⟨4963172, by rfl⟩ : syracuseStep 26470253 = 9926345) B9926345
theorem B3057785 : Blo 1358498 3057785 := bstep (se 2 (by rfl) ⟨1146669, by rfl⟩ : syracuseStep 3057785 = 2293339) B2293339
theorem B4352123 : Blo 1358498 4352123 := bstep (se 1 (by rfl) ⟨3264092, by rfl⟩ : syracuseStep 4352123 = 6528185) B6528185
theorem B4589729 : Blo 1358498 4589729 := bstep (se 2 (by rfl) ⟨1721148, by rfl⟩ : syracuseStep 4589729 = 3442297) B3442297
theorem B5163371 : Blo 1358498 5163371 := bstep (se 1 (by rfl) ⟨3872528, by rfl⟩ : syracuseStep 5163371 = 7745057) B7745057
theorem B39201155 : Blo 1358498 39201155 := bstep (se 1 (by rfl) ⟨29400866, by rfl⟩ : syracuseStep 39201155 = 58801733) B58801733
theorem B4352393 : Blo 1358498 4352393 := bstep (se 2 (by rfl) ⟨1632147, by rfl⟩ : syracuseStep 4352393 = 3264295) B3264295
theorem B4589999 : Blo 1358498 4589999 := bstep (se 1 (by rfl) ⟨3442499, by rfl⟩ : syracuseStep 4589999 = 6884999) B6884999
theorem B5164175 : Blo 1358498 5164175 := bstep (se 1 (by rfl) ⟨3873131, by rfl⟩ : syracuseStep 5164175 = 7746263) B7746263
theorem B3059099 : Blo 1358498 3059099 := bstep (se 1 (by rfl) ⟨2294324, by rfl⟩ : syracuseStep 3059099 = 4588649) B4588649
theorem B11619773 : Blo 1358498 11619773 := bstep (se 3 (by rfl) ⟨2178707, by rfl⟩ : syracuseStep 11619773 = 4357415) B4357415
theorem B4591079 : Blo 1358498 4591079 := bstep (se 1 (by rfl) ⟨3443309, by rfl⟩ : syracuseStep 4591079 = 6886619) B6886619
theorem B10317293 : Blo 1358498 10317293 := bstep (se 3 (by rfl) ⟨1934492, by rfl⟩ : syracuseStep 10317293 = 3868985) B3868985
theorem B14708567 : Blo 1358498 14708567 := bstep (se 1 (by rfl) ⟨11031425, by rfl⟩ : syracuseStep 14708567 = 22062851) B22062851
theorem B3059675 : Blo 1358498 3059675 := bstep (se 1 (by rfl) ⟨2294756, by rfl⟩ : syracuseStep 3059675 = 4589513) B4589513
theorem B3100655 : Blo 1358498 3100655 := bstep (se 1 (by rfl) ⟨2325491, by rfl⟩ : syracuseStep 3100655 = 4650983) B4650983
theorem B3059855 : Blo 1358498 3059855 := bstep (se 1 (by rfl) ⟨2294891, by rfl⟩ : syracuseStep 3059855 = 4589783) B4589783
theorem B49615001 : Blo 1358498 49615001 := bstep (se 2 (by rfl) ⟨18605625, by rfl⟩ : syracuseStep 49615001 = 37211251) B37211251
theorem B4903087 : Blo 1358498 4903087 := bstep (se 1 (by rfl) ⟨3677315, by rfl⟩ : syracuseStep 4903087 = 7354631) B7354631
theorem B23531741 : Blo 1358498 23531741 := bstep (se 3 (by rfl) ⟨4412201, by rfl⟩ : syracuseStep 23531741 = 8824403) B8824403
theorem B3059945 : Blo 1358498 3059945 := bstep (se 2 (by rfl) ⟨1147479, by rfl⟩ : syracuseStep 3059945 = 2294959) B2294959
theorem B7344425 : Blo 1358498 7344425 := bstep (se 2 (by rfl) ⟨2754159, by rfl⟩ : syracuseStep 7344425 = 5508319) B5508319
theorem B3060071 : Blo 1358498 3060071 := bstep (se 1 (by rfl) ⟨2295053, by rfl⟩ : syracuseStep 3060071 = 4590107) B4590107
theorem B35328371 : Blo 1358498 35328371 := bstep (se 1 (by rfl) ⟨26496278, by rfl⟩ : syracuseStep 35328371 = 52992557) B52992557
theorem B6885971 : Blo 1358498 6885971 := bstep (se 1 (by rfl) ⟨5164478, by rfl⟩ : syracuseStep 6885971 = 10328957) B10328957
theorem B6877871 : Blo 1358498 6877871 := bstep (se 1 (by rfl) ⟨5158403, by rfl⟩ : syracuseStep 6877871 = 10316807) B10316807
theorem B1528735 : Blo 1358498 1528735 := bstep (se 1 (by rfl) ⟨1146551, by rfl⟩ : syracuseStep 1528735 = 2293103) B2293103
theorem B3060647 : Blo 1358498 3060647 := bstep (se 1 (by rfl) ⟨2295485, by rfl⟩ : syracuseStep 3060647 = 4590971) B4590971
theorem B1528987 : Blo 1358498 1528987 := bstep (se 1 (by rfl) ⟨1146740, by rfl⟩ : syracuseStep 1528987 = 2293481) B2293481
theorem B14693861 : Blo 1358498 14693861 := bstep (se 4 (by rfl) ⟨1377549, by rfl⟩ : syracuseStep 14693861 = 2755099) B2755099
theorem B167499413 : Blo 1358498 167499413 := bstep (se 6 (by rfl) ⟨3925767, by rfl⟩ : syracuseStep 167499413 = 7851535) B7851535
theorem B33519365 : Blo 1358498 33519365 := bstep (se 4 (by rfl) ⟨3142440, by rfl⟩ : syracuseStep 33519365 = 6284881) B6284881
theorem B1529671 : Blo 1358498 1529671 := bstep (se 1 (by rfl) ⟨1147253, by rfl⟩ : syracuseStep 1529671 = 2294507) B2294507
theorem B10319723 : Blo 1358498 10319723 := bstep (se 1 (by rfl) ⟨7739792, by rfl⟩ : syracuseStep 10319723 = 15479585) B15479585
theorem B3872893 : Blo 1358498 3872893 := bstep (se 3 (by rfl) ⟨726167, by rfl⟩ : syracuseStep 3872893 = 1452335) B1452335
theorem B94197917 : Blo 1358498 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B3438895 : Blo 1358498 3438895 := bstep (se 1 (by rfl) ⟨2579171, by rfl⟩ : syracuseStep 3438895 = 5158343) B5158343
theorem B5511563 : Blo 1358498 5511563 := bstep (se 1 (by rfl) ⟨4133672, by rfl⟩ : syracuseStep 5511563 = 8267345) B8267345
theorem B13064591 : Blo 1358498 13064591 := bstep (se 1 (by rfl) ⟨9798443, by rfl⟩ : syracuseStep 13064591 = 19596887) B19596887
theorem B2038175 : Blo 1358498 2038175 := bstep (se 1 (by rfl) ⟨1528631, by rfl⟩ : syracuseStep 2038175 = 3057263) B3057263
theorem B1530319 : Blo 1358498 1530319 := bstep (se 1 (by rfl) ⟨1147739, by rfl⟩ : syracuseStep 1530319 = 2295479) B2295479
theorem B2038247 : Blo 1358498 2038247 := bstep (se 1 (by rfl) ⟨1528685, by rfl⟩ : syracuseStep 2038247 = 3057371) B3057371
theorem B4356737 : Blo 1358498 4356737 := bstep (se 2 (by rfl) ⟨1633776, by rfl⟩ : syracuseStep 4356737 = 3267553) B3267553
theorem B4586219 : Blo 1358498 4586219 := bstep (se 1 (by rfl) ⟨3439664, by rfl⟩ : syracuseStep 4586219 = 6879329) B6879329
theorem B7740157 : Blo 1358498 7740157 := bstep (se 3 (by rfl) ⟨1451279, by rfl⟩ : syracuseStep 7740157 = 2902559) B2902559
theorem B1358663 : Blo 1358498 1358663 := bstep (se 1 (by rfl) ⟨1018997, by rfl⟩ : syracuseStep 1358663 = 2037995) B2037995
theorem B4586327 : Blo 1358498 4586327 := bstep (se 1 (by rfl) ⟨3439745, by rfl⟩ : syracuseStep 4586327 = 6879491) B6879491
theorem B5159771 : Blo 1358498 5159771 := bstep (se 1 (by rfl) ⟨3869828, by rfl⟩ : syracuseStep 5159771 = 7739657) B7739657
theorem B1358703 : Blo 1358498 1358703 := bstep (se 1 (by rfl) ⟨1019027, by rfl⟩ : syracuseStep 1358703 = 2038055) B2038055
theorem B1358759 : Blo 1358498 1358759 := bstep (se 1 (by rfl) ⟨1019069, by rfl⟩ : syracuseStep 1358759 = 2038139) B2038139
theorem B47111159 : Blo 1358498 47111159 := bstep (se 1 (by rfl) ⟨35333369, by rfl⟩ : syracuseStep 47111159 = 70666739) B70666739
theorem B5159969 : Blo 1358498 5159969 := bstep (se 2 (by rfl) ⟨1934988, by rfl⟩ : syracuseStep 5159969 = 3869977) B3869977
theorem B1358939 : Blo 1358498 1358939 := bstep (se 1 (by rfl) ⟨1019204, by rfl⟩ : syracuseStep 1358939 = 2038409) B2038409
theorem B1359055 : Blo 1358498 1359055 := bstep (se 1 (by rfl) ⟨1019291, by rfl⟩ : syracuseStep 1359055 = 2038583) B2038583
theorem B2038991 : Blo 1358498 2038991 := bstep (se 1 (by rfl) ⟨1529243, by rfl⟩ : syracuseStep 2038991 = 3058487) B3058487
theorem B1359079 : Blo 1358498 1359079 := bstep (se 1 (by rfl) ⟨1019309, by rfl⟩ : syracuseStep 1359079 = 2038619) B2038619
theorem B7347449 : Blo 1358498 7347449 := bstep (se 2 (by rfl) ⟨2755293, by rfl⟩ : syracuseStep 7347449 = 5510587) B5510587
theorem B24804647 : Blo 1358498 24804647 := bstep (se 1 (by rfl) ⟨18603485, by rfl⟩ : syracuseStep 24804647 = 37206971) B37206971
theorem B1359175 : Blo 1358498 1359175 := bstep (se 1 (by rfl) ⟨1019381, by rfl⟩ : syracuseStep 1359175 = 2038763) B2038763
theorem B2039111 : Blo 1358498 2039111 := bstep (se 1 (by rfl) ⟨1529333, by rfl⟩ : syracuseStep 2039111 = 3058667) B3058667
theorem B1359311 : Blo 1358498 1359311 := bstep (se 1 (by rfl) ⟨1019483, by rfl⟩ : syracuseStep 1359311 = 2038967) B2038967
theorem B2039273 : Blo 1358498 2039273 := bstep (se 2 (by rfl) ⟨764727, by rfl⟩ : syracuseStep 2039273 = 1529455) B1529455
theorem B22052341 : Blo 1358498 22052341 := bstep (se 5 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 22052341 = 2067407) B2067407
theorem B6880787 : Blo 1358498 6880787 := bstep (se 1 (by rfl) ⟨5160590, by rfl⟩ : syracuseStep 6880787 = 10321181) B10321181
theorem B29408831 : Blo 1358498 29408831 := bstep (se 1 (by rfl) ⟨22056623, by rfl⟩ : syracuseStep 29408831 = 44113247) B44113247
theorem B1359471 : Blo 1358498 1359471 := bstep (se 1 (by rfl) ⟨1019603, by rfl⟩ : syracuseStep 1359471 = 2039207) B2039207
theorem B2039417 : Blo 1358498 2039417 := bstep (se 2 (by rfl) ⟨764781, by rfl⟩ : syracuseStep 2039417 = 1529563) B1529563
theorem B4587137 : Blo 1358498 4587137 := bstep (se 2 (by rfl) ⟨1720176, by rfl⟩ : syracuseStep 4587137 = 3440353) B3440353
theorem B1359527 : Blo 1358498 1359527 := bstep (se 1 (by rfl) ⟨1019645, by rfl⟩ : syracuseStep 1359527 = 2039291) B2039291
theorem B3440303 : Blo 1358498 3440303 := bstep (se 1 (by rfl) ⟨2580227, by rfl⟩ : syracuseStep 3440303 = 5160455) B5160455
theorem B26123957 : Blo 1358498 26123957 := bstep (se 5 (by rfl) ⟨1224560, by rfl⟩ : syracuseStep 26123957 = 2449121) B2449121
theorem B7741115 : Blo 1358498 7741115 := bstep (se 1 (by rfl) ⟨5805836, by rfl⟩ : syracuseStep 7741115 = 11611673) B11611673
theorem B1359591 : Blo 1358498 1359591 := bstep (se 1 (by rfl) ⟨1019693, by rfl⟩ : syracuseStep 1359591 = 2039387) B2039387
theorem B1359647 : Blo 1358498 1359647 := bstep (se 1 (by rfl) ⟨1019735, by rfl⟩ : syracuseStep 1359647 = 2039471) B2039471
theorem B1359727 : Blo 1358498 1359727 := bstep (se 1 (by rfl) ⟨1019795, by rfl⟩ : syracuseStep 1359727 = 2039591) B2039591
theorem B2039663 : Blo 1358498 2039663 := bstep (se 1 (by rfl) ⟨1529747, by rfl⟩ : syracuseStep 2039663 = 3059495) B3059495
theorem B15687557 : Blo 1358498 15687557 := bstep (se 4 (by rfl) ⟨1470708, by rfl⟩ : syracuseStep 15687557 = 2941417) B2941417
theorem B4587407 : Blo 1358498 4587407 := bstep (se 1 (by rfl) ⟨3440555, by rfl⟩ : syracuseStep 4587407 = 6881111) B6881111
theorem B1359783 : Blo 1358498 1359783 := bstep (se 1 (by rfl) ⟨1019837, by rfl⟩ : syracuseStep 1359783 = 2039675) B2039675
theorem B3186665 : Blo 1358498 3186665 := bstep (se 2 (by rfl) ⟨1194999, by rfl⟩ : syracuseStep 3186665 = 2389999) B2389999
theorem B5160941 : Blo 1358498 5160941 := bstep (se 3 (by rfl) ⟨967676, by rfl⟩ : syracuseStep 5160941 = 1935353) B1935353
theorem B34865153 : Blo 1358498 34865153 := bstep (se 2 (by rfl) ⟨13074432, by rfl⟩ : syracuseStep 34865153 = 26148865) B26148865
theorem B2039903 : Blo 1358498 2039903 := bstep (se 1 (by rfl) ⟨1529927, by rfl⟩ : syracuseStep 2039903 = 3059855) B3059855
theorem B2326655 : Blo 1358498 2326655 := bstep (se 1 (by rfl) ⟨1744991, by rfl⟩ : syracuseStep 2326655 = 3489983) B3489983
theorem B15687827 : Blo 1358498 15687827 := bstep (se 1 (by rfl) ⟨11765870, by rfl⟩ : syracuseStep 15687827 = 23531741) B23531741
theorem B2039963 : Blo 1358498 2039963 := bstep (se 1 (by rfl) ⟨1529972, by rfl⟩ : syracuseStep 2039963 = 3059945) B3059945
theorem B6537449 : Blo 1358498 6537449 := bstep (se 2 (by rfl) ⟨2451543, by rfl⟩ : syracuseStep 6537449 = 4903087) B4903087
theorem B2040047 : Blo 1358498 2040047 := bstep (se 1 (by rfl) ⟨1530035, by rfl⟩ : syracuseStep 2040047 = 3060071) B3060071
theorem B4473191 : Blo 1358498 4473191 := bstep (se 1 (by rfl) ⟨3354893, by rfl⟩ : syracuseStep 4473191 = 6709787) B6709787
theorem B1360231 : Blo 1358498 1360231 := bstep (se 1 (by rfl) ⟨1020173, by rfl⟩ : syracuseStep 1360231 = 2040347) B2040347
theorem B1360351 : Blo 1358498 1360351 := bstep (se 1 (by rfl) ⟨1020263, by rfl⟩ : syracuseStep 1360351 = 2040527) B2040527
theorem B1360359 : Blo 1358498 1360359 := bstep (se 1 (by rfl) ⟨1020269, by rfl⟩ : syracuseStep 1360359 = 2040539) B2040539
theorem B2040425 : Blo 1358498 2040425 := bstep (se 2 (by rfl) ⟨765159, by rfl⟩ : syracuseStep 2040425 = 1530319) B1530319
theorem B2040431 : Blo 1358498 2040431 := bstep (se 1 (by rfl) ⟨1530323, by rfl⟩ : syracuseStep 2040431 = 3060647) B3060647
theorem B5161715 : Blo 1358498 5161715 := bstep (se 1 (by rfl) ⟨3871286, by rfl⟩ : syracuseStep 5161715 = 7742573) B7742573
theorem B1721083 : Blo 1358498 1721083 := bstep (se 1 (by rfl) ⟨1290812, by rfl⟩ : syracuseStep 1721083 = 2581625) B2581625
theorem B94208989 : Blo 1358498 94208989 := bstep (se 3 (by rfl) ⟨17664185, by rfl⟩ : syracuseStep 94208989 = 35328371) B35328371
theorem B23217191 : Blo 1358498 23217191 := bstep (se 1 (by rfl) ⟨17412893, by rfl⟩ : syracuseStep 23217191 = 34825787) B34825787
theorem B111666275 : Blo 1358498 111666275 := bstep (se 1 (by rfl) ⟨83749706, by rfl⟩ : syracuseStep 111666275 = 167499413) B167499413
theorem B4654255 : Blo 1358498 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B17646835 : Blo 1358498 17646835 := bstep (se 1 (by rfl) ⟨13235126, by rfl⟩ : syracuseStep 17646835 = 26470253) B26470253
theorem B2901415 : Blo 1358498 2901415 := bstep (se 1 (by rfl) ⟨2176061, by rfl⟩ : syracuseStep 2901415 = 4352123) B4352123
theorem B3442247 : Blo 1358498 3442247 := bstep (se 1 (by rfl) ⟨2581685, by rfl⟩ : syracuseStep 3442247 = 5163371) B5163371
theorem B26134103 : Blo 1358498 26134103 := bstep (se 1 (by rfl) ⟨19600577, by rfl⟩ : syracuseStep 26134103 = 39201155) B39201155
theorem B2901595 : Blo 1358498 2901595 := bstep (se 1 (by rfl) ⟨2176196, by rfl⟩ : syracuseStep 2901595 = 4352393) B4352393
theorem B3057479 : Blo 1358498 3057479 := bstep (se 1 (by rfl) ⟨2293109, by rfl⟩ : syracuseStep 3057479 = 4586219) B4586219
theorem B3057551 : Blo 1358498 3057551 := bstep (se 1 (by rfl) ⟨2293163, by rfl⟩ : syracuseStep 3057551 = 4586327) B4586327
theorem B29403121 : Blo 1358498 29403121 := bstep (se 2 (by rfl) ⟨11026170, by rfl⟩ : syracuseStep 29403121 = 22052341) B22052341
theorem B3442783 : Blo 1358498 3442783 := bstep (se 1 (by rfl) ⟨2582087, by rfl⟩ : syracuseStep 3442783 = 5164175) B5164175
theorem B19605887 : Blo 1358498 19605887 := bstep (se 1 (by rfl) ⟨14704415, by rfl⟩ : syracuseStep 19605887 = 29408831) B29408831
theorem B3058091 : Blo 1358498 3058091 := bstep (se 1 (by rfl) ⟨2293568, by rfl⟩ : syracuseStep 3058091 = 4587137) B4587137
theorem B3058271 : Blo 1358498 3058271 := bstep (se 1 (by rfl) ⟨2293703, by rfl⟩ : syracuseStep 3058271 = 4587407) B4587407
theorem B2124443 : Blo 1358498 2124443 := bstep (se 1 (by rfl) ⟨1593332, by rfl⟩ : syracuseStep 2124443 = 3186665) B3186665
theorem B2067103 : Blo 1358498 2067103 := bstep (se 1 (by rfl) ⟨1550327, by rfl⟩ : syracuseStep 2067103 = 3100655) B3100655
theorem B5163857 : Blo 1358498 5163857 := bstep (se 2 (by rfl) ⟨1936446, by rfl⟩ : syracuseStep 5163857 = 3872893) B3872893
theorem B3058631 : Blo 1358498 3058631 := bstep (se 1 (by rfl) ⟨2293973, by rfl⟩ : syracuseStep 3058631 = 4587947) B4587947
theorem B4590647 : Blo 1358498 4590647 := bstep (se 1 (by rfl) ⟨3442985, by rfl⟩ : syracuseStep 4590647 = 6885971) B6885971
theorem B3058991 : Blo 1358498 3058991 := bstep (se 1 (by rfl) ⟨2294243, by rfl⟩ : syracuseStep 3058991 = 4588487) B4588487
theorem B6532433 : Blo 1358498 6532433 := bstep (se 2 (by rfl) ⟨2449662, by rfl⟩ : syracuseStep 6532433 = 4899325) B4899325
theorem B3059027 : Blo 1358498 3059027 := bstep (se 1 (by rfl) ⟨2294270, by rfl⟩ : syracuseStep 3059027 = 4588541) B4588541
theorem B3059279 : Blo 1358498 3059279 := bstep (se 1 (by rfl) ⟨2294459, by rfl⟩ : syracuseStep 3059279 = 4588919) B4588919
theorem B3059567 : Blo 1358498 3059567 := bstep (se 1 (by rfl) ⟨2294675, by rfl⟩ : syracuseStep 3059567 = 4589351) B4589351
theorem B3059819 : Blo 1358498 3059819 := bstep (se 1 (by rfl) ⟨2294864, by rfl⟩ : syracuseStep 3059819 = 4589729) B4589729
theorem B3674375 : Blo 1358498 3674375 := bstep (se 1 (by rfl) ⟨2755781, by rfl⟩ : syracuseStep 3674375 = 5511563) B5511563
theorem B1765290257 : Blo 1358498 1765290257 := bstep (se 2 (by rfl) ⟨661983846, by rfl⟩ : syracuseStep 1765290257 = 1323967693) B1323967693
theorem B3059999 : Blo 1358498 3059999 := bstep (se 1 (by rfl) ⟨2294999, by rfl⟩ : syracuseStep 3059999 = 4589999) B4589999
theorem B2904491 : Blo 1358498 2904491 := bstep (se 1 (by rfl) ⟨2178368, by rfl⟩ : syracuseStep 2904491 = 4356737) B4356737
theorem B16536431 : Blo 1358498 16536431 := bstep (se 1 (by rfl) ⟨12402323, by rfl⟩ : syracuseStep 16536431 = 24804647) B24804647
theorem B7746515 : Blo 1358498 7746515 := bstep (se 1 (by rfl) ⟨5809886, by rfl⟩ : syracuseStep 7746515 = 11619773) B11619773
theorem B3060719 : Blo 1358498 3060719 := bstep (se 1 (by rfl) ⟨2295539, by rfl⟩ : syracuseStep 3060719 = 4591079) B4591079
theorem B6878195 : Blo 1358498 6878195 := bstep (se 1 (by rfl) ⟨5158646, by rfl⟩ : syracuseStep 6878195 = 10317293) B10317293
theorem B10458371 : Blo 1358498 10458371 := bstep (se 1 (by rfl) ⟨7843778, by rfl⟩ : syracuseStep 10458371 = 15687557) B15687557
theorem B33076667 : Blo 1358498 33076667 := bstep (se 1 (by rfl) ⟨24807500, by rfl⟩ : syracuseStep 33076667 = 49615001) B49615001
theorem B4896283 : Blo 1358498 4896283 := bstep (se 1 (by rfl) ⟨3672212, by rfl⟩ : syracuseStep 4896283 = 7344425) B7344425
theorem B5158525 : Blo 1358498 5158525 := bstep (se 3 (by rfl) ⟨967223, by rfl⟩ : syracuseStep 5158525 = 1934447) B1934447
theorem B4585193 : Blo 1358498 4585193 := bstep (se 2 (by rfl) ⟨1719447, by rfl⟩ : syracuseStep 4585193 = 3438895) B3438895
theorem B3921671 : Blo 1358498 3921671 := bstep (se 1 (by rfl) ⟨2941253, by rfl⟩ : syracuseStep 3921671 = 5882507) B5882507
theorem B4585247 : Blo 1358498 4585247 := bstep (se 1 (by rfl) ⟨3438935, by rfl⟩ : syracuseStep 4585247 = 6877871) B6877871
theorem B3872711 : Blo 1358498 3872711 := bstep (se 1 (by rfl) ⟨2904533, by rfl⟩ : syracuseStep 3872711 = 5809067) B5809067
theorem B19593197 : Blo 1358498 19593197 := bstep (se 3 (by rfl) ⟨3673724, by rfl⟩ : syracuseStep 19593197 = 7347449) B7347449
theorem B2037791 : Blo 1358498 2037791 := bstep (se 1 (by rfl) ⟨1528343, by rfl⟩ : syracuseStep 2037791 = 3056687) B3056687
theorem B1530139 : Blo 1358498 1530139 := bstep (se 1 (by rfl) ⟨1147604, by rfl⟩ : syracuseStep 1530139 = 2295209) B2295209
theorem B9795907 : Blo 1358498 9795907 := bstep (se 1 (by rfl) ⟨7346930, by rfl⟩ : syracuseStep 9795907 = 14693861) B14693861
theorem B10320209 : Blo 1358498 10320209 := bstep (se 2 (by rfl) ⟨3870078, by rfl⟩ : syracuseStep 10320209 = 7740157) B7740157
theorem B34838909 : Blo 1358498 34838909 := bstep (se 3 (by rfl) ⟨6532295, by rfl⟩ : syracuseStep 34838909 = 13064591) B13064591
theorem B2038223 : Blo 1358498 2038223 := bstep (se 1 (by rfl) ⟨1528667, by rfl⟩ : syracuseStep 2038223 = 3057335) B3057335
theorem B22346243 : Blo 1358498 22346243 := bstep (se 1 (by rfl) ⟨16759682, by rfl⟩ : syracuseStep 22346243 = 33519365) B33519365
theorem B2038313 : Blo 1358498 2038313 := bstep (se 2 (by rfl) ⟨764367, by rfl⟩ : syracuseStep 2038313 = 1528735) B1528735
theorem B6879815 : Blo 1358498 6879815 := bstep (se 1 (by rfl) ⟨5159861, by rfl⟩ : syracuseStep 6879815 = 10319723) B10319723
theorem B2038523 : Blo 1358498 2038523 := bstep (se 1 (by rfl) ⟨1528892, by rfl⟩ : syracuseStep 2038523 = 3057785) B3057785
theorem B62798611 : Blo 1358498 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B2038649 : Blo 1358498 2038649 := bstep (se 2 (by rfl) ⟨764493, by rfl⟩ : syracuseStep 2038649 = 1528987) B1528987
theorem B1358783 : Blo 1358498 1358783 := bstep (se 1 (by rfl) ⟨1019087, by rfl⟩ : syracuseStep 1358783 = 2038175) B2038175
theorem B1358831 : Blo 1358498 1358831 := bstep (se 1 (by rfl) ⟨1019123, by rfl⟩ : syracuseStep 1358831 = 2038247) B2038247
theorem B2579681 : Blo 1358498 2579681 := bstep (se 2 (by rfl) ⟨967380, by rfl⟩ : syracuseStep 2579681 = 1934761) B1934761
theorem B3439847 : Blo 1358498 3439847 := bstep (se 1 (by rfl) ⟨2579885, by rfl⟩ : syracuseStep 3439847 = 5159771) B5159771
theorem B31407439 : Blo 1358498 31407439 := bstep (se 1 (by rfl) ⟨23555579, by rfl⟩ : syracuseStep 31407439 = 47111159) B47111159
theorem B3439979 : Blo 1358498 3439979 := bstep (se 1 (by rfl) ⟨2579984, by rfl⟩ : syracuseStep 3439979 = 5159969) B5159969
theorem B1359327 : Blo 1358498 1359327 := bstep (se 1 (by rfl) ⟨1019495, by rfl⟩ : syracuseStep 1359327 = 2038991) B2038991
theorem B1359407 : Blo 1358498 1359407 := bstep (se 1 (by rfl) ⟨1019555, by rfl⟩ : syracuseStep 1359407 = 2039111) B2039111
theorem B2039399 : Blo 1358498 2039399 := bstep (se 1 (by rfl) ⟨1529549, by rfl⟩ : syracuseStep 2039399 = 3059099) B3059099
theorem B1359515 : Blo 1358498 1359515 := bstep (se 1 (by rfl) ⟨1019636, by rfl⟩ : syracuseStep 1359515 = 2039273) B2039273
theorem B4587191 : Blo 1358498 4587191 := bstep (se 1 (by rfl) ⟨3440393, by rfl⟩ : syracuseStep 4587191 = 6880787) B6880787
theorem B1359611 : Blo 1358498 1359611 := bstep (se 1 (by rfl) ⟨1019708, by rfl⟩ : syracuseStep 1359611 = 2039417) B2039417
theorem B2039561 : Blo 1358498 2039561 := bstep (se 2 (by rfl) ⟨764835, by rfl⟩ : syracuseStep 2039561 = 1529671) B1529671
theorem B2293535 : Blo 1358498 2293535 := bstep (se 1 (by rfl) ⟨1720151, by rfl⟩ : syracuseStep 2293535 = 3440303) B3440303
theorem B17415971 : Blo 1358498 17415971 := bstep (se 1 (by rfl) ⟨13061978, by rfl⟩ : syracuseStep 17415971 = 26123957) B26123957
theorem B5160743 : Blo 1358498 5160743 := bstep (se 1 (by rfl) ⟨3870557, by rfl⟩ : syracuseStep 5160743 = 7741115) B7741115
theorem B9805711 : Blo 1358498 9805711 := bstep (se 1 (by rfl) ⟨7354283, by rfl⟩ : syracuseStep 9805711 = 14708567) B14708567
theorem B1359775 : Blo 1358498 1359775 := bstep (se 1 (by rfl) ⟨1019831, by rfl⟩ : syracuseStep 1359775 = 2039663) B2039663
theorem B2039783 : Blo 1358498 2039783 := bstep (se 1 (by rfl) ⟨1529837, by rfl⟩ : syracuseStep 2039783 = 3059675) B3059675
theorem B3440627 : Blo 1358498 3440627 := bstep (se 1 (by rfl) ⟨2580470, by rfl⟩ : syracuseStep 3440627 = 5160941) B5160941
theorem B1359935 : Blo 1358498 1359935 := bstep (se 1 (by rfl) ⟨1019951, by rfl⟩ : syracuseStep 1359935 = 2039903) B2039903
theorem B2039879 : Blo 1358498 2039879 := bstep (se 1 (by rfl) ⟨1529909, by rfl⟩ : syracuseStep 2039879 = 3059819) B3059819
theorem B1359975 : Blo 1358498 1359975 := bstep (se 1 (by rfl) ⟨1019981, by rfl⟩ : syracuseStep 1359975 = 2039963) B2039963
theorem B1360031 : Blo 1358498 1360031 := bstep (se 1 (by rfl) ⟨1020023, by rfl⟩ : syracuseStep 1360031 = 2040047) B2040047
theorem B4358299 : Blo 1358498 4358299 := bstep (se 1 (by rfl) ⟨3268724, by rfl⟩ : syracuseStep 4358299 = 6537449) B6537449
theorem B2449583 : Blo 1358498 2449583 := bstep (se 1 (by rfl) ⟨1837187, by rfl⟩ : syracuseStep 2449583 = 3674375) B3674375
theorem B2039999 : Blo 1358498 2039999 := bstep (se 1 (by rfl) ⟨1529999, by rfl⟩ : syracuseStep 2039999 = 3059999) B3059999
theorem B2040185 : Blo 1358498 2040185 := bstep (se 2 (by rfl) ⟨765069, by rfl⟩ : syracuseStep 2040185 = 1530139) B1530139
theorem B1360283 : Blo 1358498 1360283 := bstep (se 1 (by rfl) ⟨1020212, by rfl⟩ : syracuseStep 1360283 = 2040425) B2040425
theorem B1360287 : Blo 1358498 1360287 := bstep (se 1 (by rfl) ⟨1020215, by rfl⟩ : syracuseStep 1360287 = 2040431) B2040431
theorem B3441143 : Blo 1358498 3441143 := bstep (se 1 (by rfl) ⟨2580857, by rfl⟩ : syracuseStep 3441143 = 5161715) B5161715
theorem B2040479 : Blo 1358498 2040479 := bstep (se 1 (by rfl) ⟨1530359, by rfl⟩ : syracuseStep 2040479 = 3060719) B3060719
theorem B6972247 : Blo 1358498 6972247 := bstep (se 1 (by rfl) ⟨5229185, by rfl⟩ : syracuseStep 6972247 = 10458371) B10458371
theorem B11928509 : Blo 1358498 11928509 := bstep (se 3 (by rfl) ⟨2236595, by rfl⟩ : syracuseStep 11928509 = 4473191) B4473191
theorem B2294777 : Blo 1358498 2294777 := bstep (se 2 (by rfl) ⟨860541, by rfl⟩ : syracuseStep 2294777 = 1721083) B1721083
theorem B83731481 : Blo 1358498 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B2294831 : Blo 1358498 2294831 := bstep (se 1 (by rfl) ⟨1721123, by rfl⟩ : syracuseStep 2294831 = 3442247) B3442247
theorem B3056795 : Blo 1358498 3056795 := bstep (se 1 (by rfl) ⟨2292596, by rfl⟩ : syracuseStep 3056795 = 4585193) B4585193
theorem B2614447 : Blo 1358498 2614447 := bstep (se 1 (by rfl) ⟨1960835, by rfl⟩ : syracuseStep 2614447 = 3921671) B3921671
theorem B3056831 : Blo 1358498 3056831 := bstep (se 1 (by rfl) ⟨2292623, by rfl⟩ : syracuseStep 3056831 = 4585247) B4585247
theorem B2581807 : Blo 1358498 2581807 := bstep (se 1 (by rfl) ⟨1936355, by rfl⟩ : syracuseStep 2581807 = 3872711) B3872711
theorem B23225939 : Blo 1358498 23225939 := bstep (se 1 (by rfl) ⟨17419454, by rfl⟩ : syracuseStep 23225939 = 34838909) B34838909
theorem B23529113 : Blo 1358498 23529113 := bstep (se 2 (by rfl) ⟨8823417, by rfl⟩ : syracuseStep 23529113 = 17646835) B17646835
theorem B3868553 : Blo 1358498 3868553 := bstep (se 2 (by rfl) ⟨1450707, by rfl⟩ : syracuseStep 3868553 = 2901415) B2901415
theorem B3442571 : Blo 1358498 3442571 := bstep (se 1 (by rfl) ⟨2581928, by rfl⟩ : syracuseStep 3442571 = 5163857) B5163857
theorem B3868793 : Blo 1358498 3868793 := bstep (se 2 (by rfl) ⟨1450797, by rfl⟩ : syracuseStep 3868793 = 2901595) B2901595
theorem B3058127 : Blo 1358498 3058127 := bstep (se 1 (by rfl) ⟨2293595, by rfl⟩ : syracuseStep 3058127 = 4587191) B4587191
theorem B11610647 : Blo 1358498 11610647 := bstep (se 1 (by rfl) ⟨8707985, by rfl⟩ : syracuseStep 11610647 = 17415971) B17415971
theorem B23243435 : Blo 1358498 23243435 := bstep (se 1 (by rfl) ⟨17432576, by rfl⟩ : syracuseStep 23243435 = 34865153) B34865153
theorem B4590377 : Blo 1358498 4590377 := bstep (se 2 (by rfl) ⟨1721391, by rfl⟩ : syracuseStep 4590377 = 3442783) B3442783
theorem B1936327 : Blo 1358498 1936327 := bstep (se 1 (by rfl) ⟨1452245, by rfl⟩ : syracuseStep 1936327 = 2904491) B2904491
theorem B6204413 : Blo 1358498 6204413 := bstep (se 3 (by rfl) ⟨1163327, by rfl⟩ : syracuseStep 6204413 = 2326655) B2326655
theorem B13061209 : Blo 1358498 13061209 := bstep (se 2 (by rfl) ⟨4897953, by rfl⟩ : syracuseStep 13061209 = 9795907) B9795907
theorem B5164343 : Blo 1358498 5164343 := bstep (se 1 (by rfl) ⟨3873257, by rfl⟩ : syracuseStep 5164343 = 7746515) B7746515
theorem B15478127 : Blo 1358498 15478127 := bstep (se 1 (by rfl) ⟨11608595, by rfl⟩ : syracuseStep 15478127 = 23217191) B23217191
theorem B74444183 : Blo 1358498 74444183 := bstep (se 1 (by rfl) ⟨55833137, by rfl⟩ : syracuseStep 74444183 = 111666275) B111666275
theorem B125611985 : Blo 1358498 125611985 := bstep (se 2 (by rfl) ⟨47104494, by rfl⟩ : syracuseStep 125611985 = 94208989) B94208989
theorem B13062131 : Blo 1358498 13062131 := bstep (se 1 (by rfl) ⟨9796598, by rfl⟩ : syracuseStep 13062131 = 19593197) B19593197
theorem B6205673 : Blo 1358498 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B13070591 : Blo 1358498 13070591 := bstep (se 1 (by rfl) ⟨9802943, by rfl⟩ : syracuseStep 13070591 = 19605887) B19605887
theorem B14897495 : Blo 1358498 14897495 := bstep (se 1 (by rfl) ⟨11173121, by rfl⟩ : syracuseStep 14897495 = 22346243) B22346243
theorem B3060431 : Blo 1358498 3060431 := bstep (se 1 (by rfl) ⟨2295323, by rfl⟩ : syracuseStep 3060431 = 4590647) B4590647
theorem B6878033 : Blo 1358498 6878033 := bstep (se 2 (by rfl) ⟨2579262, by rfl⟩ : syracuseStep 6878033 = 5158525) B5158525
theorem B4354955 : Blo 1358498 4354955 := bstep (se 1 (by rfl) ⟨3266216, by rfl⟩ : syracuseStep 4354955 = 6532433) B6532433
theorem B1529023 : Blo 1358498 1529023 := bstep (se 1 (by rfl) ⟨1146767, by rfl⟩ : syracuseStep 1529023 = 2293535) B2293535
theorem B39204161 : Blo 1358498 39204161 := bstep (se 2 (by rfl) ⟨14701560, by rfl⟩ : syracuseStep 39204161 = 29403121) B29403121
theorem B10458551 : Blo 1358498 10458551 := bstep (se 1 (by rfl) ⟨7843913, by rfl⟩ : syracuseStep 10458551 = 15687827) B15687827
theorem B1176860171 : Blo 1358498 1176860171 := bstep (se 1 (by rfl) ⟨882645128, by rfl⟩ : syracuseStep 1176860171 = 1765290257) B1765290257
theorem B2293751 : Blo 1358498 2293751 := bstep (se 1 (by rfl) ⟨1720313, by rfl⟩ : syracuseStep 2293751 = 3440627) B3440627
theorem B4585463 : Blo 1358498 4585463 := bstep (se 1 (by rfl) ⟨3439097, by rfl⟩ : syracuseStep 4585463 = 6878195) B6878195
theorem B11024549 : Blo 1358498 11024549 := bstep (se 4 (by rfl) ⟨1033551, by rfl⟩ : syracuseStep 11024549 = 2067103) B2067103
theorem B22051111 : Blo 1358498 22051111 := bstep (se 1 (by rfl) ⟨16538333, by rfl⟩ : syracuseStep 22051111 = 33076667) B33076667
theorem B17422735 : Blo 1358498 17422735 := bstep (se 1 (by rfl) ⟨13067051, by rfl⟩ : syracuseStep 17422735 = 26134103) B26134103
theorem B2038319 : Blo 1358498 2038319 := bstep (se 1 (by rfl) ⟨1528739, by rfl⟩ : syracuseStep 2038319 = 3057479) B3057479
theorem B2038367 : Blo 1358498 2038367 := bstep (se 1 (by rfl) ⟨1528775, by rfl⟩ : syracuseStep 2038367 = 3057551) B3057551
theorem B1358527 : Blo 1358498 1358527 := bstep (se 1 (by rfl) ⟨1018895, by rfl⟩ : syracuseStep 1358527 = 2037791) B2037791
theorem B6880139 : Blo 1358498 6880139 := bstep (se 1 (by rfl) ⟨5160104, by rfl⟩ : syracuseStep 6880139 = 10320209) B10320209
theorem B2038727 : Blo 1358498 2038727 := bstep (se 1 (by rfl) ⟨1529045, by rfl⟩ : syracuseStep 2038727 = 3058091) B3058091
theorem B1358815 : Blo 1358498 1358815 := bstep (se 1 (by rfl) ⟨1019111, by rfl⟩ : syracuseStep 1358815 = 2038223) B2038223
theorem B1358875 : Blo 1358498 1358875 := bstep (se 1 (by rfl) ⟨1019156, by rfl⟩ : syracuseStep 1358875 = 2038313) B2038313
theorem B4586543 : Blo 1358498 4586543 := bstep (se 1 (by rfl) ⟨3439907, by rfl⟩ : syracuseStep 4586543 = 6879815) B6879815
theorem B2038847 : Blo 1358498 2038847 := bstep (se 1 (by rfl) ⟨1529135, by rfl⟩ : syracuseStep 2038847 = 3058271) B3058271
theorem B1416295 : Blo 1358498 1416295 := bstep (se 1 (by rfl) ⟨1062221, by rfl⟩ : syracuseStep 1416295 = 2124443) B2124443
theorem B41876585 : Blo 1358498 41876585 := bstep (se 2 (by rfl) ⟨15703719, by rfl⟩ : syracuseStep 41876585 = 31407439) B31407439
theorem B1359015 : Blo 1358498 1359015 := bstep (se 1 (by rfl) ⟨1019261, by rfl⟩ : syracuseStep 1359015 = 2038523) B2038523
theorem B1359099 : Blo 1358498 1359099 := bstep (se 1 (by rfl) ⟨1019324, by rfl⟩ : syracuseStep 1359099 = 2038649) B2038649
theorem B2039087 : Blo 1358498 2039087 := bstep (se 1 (by rfl) ⟨1529315, by rfl⟩ : syracuseStep 2039087 = 3058631) B3058631
theorem B6528377 : Blo 1358498 6528377 := bstep (se 2 (by rfl) ⟨2448141, by rfl⟩ : syracuseStep 6528377 = 4896283) B4896283
theorem B1719787 : Blo 1358498 1719787 := bstep (se 1 (by rfl) ⟨1289840, by rfl⟩ : syracuseStep 1719787 = 2579681) B2579681
theorem B2293231 : Blo 1358498 2293231 := bstep (se 1 (by rfl) ⟨1719923, by rfl⟩ : syracuseStep 2293231 = 3439847) B3439847
theorem B2039327 : Blo 1358498 2039327 := bstep (se 1 (by rfl) ⟨1529495, by rfl⟩ : syracuseStep 2039327 = 3058991) B3058991
theorem B2039351 : Blo 1358498 2039351 := bstep (se 1 (by rfl) ⟨1529513, by rfl⟩ : syracuseStep 2039351 = 3059027) B3059027
theorem B2293319 : Blo 1358498 2293319 := bstep (se 1 (by rfl) ⟨1719989, by rfl⟩ : syracuseStep 2293319 = 3439979) B3439979
theorem B44097149 : Blo 1358498 44097149 := bstep (se 3 (by rfl) ⟨8268215, by rfl⟩ : syracuseStep 44097149 = 16536431) B16536431
theorem B2039519 : Blo 1358498 2039519 := bstep (se 1 (by rfl) ⟨1529639, by rfl⟩ : syracuseStep 2039519 = 3059279) B3059279
theorem B1359599 : Blo 1358498 1359599 := bstep (se 1 (by rfl) ⟨1019699, by rfl⟩ : syracuseStep 1359599 = 2039399) B2039399
theorem B1359707 : Blo 1358498 1359707 := bstep (se 1 (by rfl) ⟨1019780, by rfl⟩ : syracuseStep 1359707 = 2039561) B2039561
theorem B13074281 : Blo 1358498 13074281 := bstep (se 2 (by rfl) ⟨4902855, by rfl⟩ : syracuseStep 13074281 = 9805711) B9805711
theorem B3440495 : Blo 1358498 3440495 := bstep (se 1 (by rfl) ⟨2580371, by rfl⟩ : syracuseStep 3440495 = 5160743) B5160743
theorem B2039711 : Blo 1358498 2039711 := bstep (se 1 (by rfl) ⟨1529783, by rfl⟩ : syracuseStep 2039711 = 3059567) B3059567
theorem B1359855 : Blo 1358498 1359855 := bstep (se 1 (by rfl) ⟨1019891, by rfl⟩ : syracuseStep 1359855 = 2039783) B2039783
theorem B1359919 : Blo 1358498 1359919 := bstep (se 1 (by rfl) ⟨1019939, by rfl⟩ : syracuseStep 1359919 = 2039879) B2039879
theorem B1359999 : Blo 1358498 1359999 := bstep (se 1 (by rfl) ⟨1019999, by rfl⟩ : syracuseStep 1359999 = 2039999) B2039999
theorem B1360123 : Blo 1358498 1360123 := bstep (se 1 (by rfl) ⟨1020092, by rfl⟩ : syracuseStep 1360123 = 2040185) B2040185
theorem B2294095 : Blo 1358498 2294095 := bstep (se 1 (by rfl) ⟨1720571, by rfl⟩ : syracuseStep 2294095 = 3441143) B3441143
theorem B29401481 : Blo 1358498 29401481 := bstep (se 2 (by rfl) ⟨11025555, by rfl⟩ : syracuseStep 29401481 = 22051111) B22051111
theorem B1360319 : Blo 1358498 1360319 := bstep (se 1 (by rfl) ⟨1020239, by rfl⟩ : syracuseStep 1360319 = 2040479) B2040479
theorem B2040287 : Blo 1358498 2040287 := bstep (se 1 (by rfl) ⟨1530215, by rfl⟩ : syracuseStep 2040287 = 3060431) B3060431
theorem B7553573 : Blo 1358498 7553573 := bstep (se 4 (by rfl) ⟨708147, by rfl⟩ : syracuseStep 7553573 = 1416295) B1416295
theorem B16548461 : Blo 1358498 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B55820987 : Blo 1358498 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B6972367 : Blo 1358498 6972367 := bstep (se 1 (by rfl) ⟨5229275, by rfl⟩ : syracuseStep 6972367 = 10458551) B10458551
theorem B784573447 : Blo 1358498 784573447 := bstep (se 1 (by rfl) ⟨588430085, by rfl⟩ : syracuseStep 784573447 = 1176860171) B1176860171
theorem B15483959 : Blo 1358498 15483959 := bstep (se 1 (by rfl) ⟨11612969, by rfl⟩ : syracuseStep 15483959 = 23225939) B23225939
theorem B2295047 : Blo 1358498 2295047 := bstep (se 1 (by rfl) ⟨1721285, by rfl⟩ : syracuseStep 2295047 = 3442571) B3442571
theorem B2581769 : Blo 1358498 2581769 := bstep (se 2 (by rfl) ⟨968163, by rfl⟩ : syracuseStep 2581769 = 1936327) B1936327
theorem B3056975 : Blo 1358498 3056975 := bstep (se 1 (by rfl) ⟨2292731, by rfl⟩ : syracuseStep 3056975 = 4585463) B4585463
theorem B7349699 : Blo 1358498 7349699 := bstep (se 1 (by rfl) ⟨5512274, by rfl⟩ : syracuseStep 7349699 = 11024549) B11024549
theorem B3442409 : Blo 1358498 3442409 := bstep (se 2 (by rfl) ⟨1290903, by rfl⟩ : syracuseStep 3442409 = 2581807) B2581807
theorem B3057641 : Blo 1358498 3057641 := bstep (se 2 (by rfl) ⟨1146615, by rfl⟩ : syracuseStep 3057641 = 2293231) B2293231
theorem B3057695 : Blo 1358498 3057695 := bstep (se 1 (by rfl) ⟨2293271, by rfl⟩ : syracuseStep 3057695 = 4586543) B4586543
theorem B3442895 : Blo 1358498 3442895 := bstep (se 1 (by rfl) ⟨2582171, by rfl⟩ : syracuseStep 3442895 = 5164343) B5164343
theorem B4352251 : Blo 1358498 4352251 := bstep (se 1 (by rfl) ⟨3264188, by rfl⟩ : syracuseStep 4352251 = 6528377) B6528377
theorem B49629455 : Blo 1358498 49629455 := bstep (se 1 (by rfl) ⟨37222091, by rfl⟩ : syracuseStep 49629455 = 74444183) B74444183
theorem B83741323 : Blo 1358498 83741323 := bstep (se 1 (by rfl) ⟨62805992, by rfl⟩ : syracuseStep 83741323 = 125611985) B125611985
theorem B1633055 : Blo 1358498 1633055 := bstep (se 1 (by rfl) ⟨1224791, by rfl⟩ : syracuseStep 1633055 = 2449583) B2449583
theorem B5811065 : Blo 1358498 5811065 := bstep (se 2 (by rfl) ⟨2179149, by rfl⟩ : syracuseStep 5811065 = 4358299) B4358299
theorem B9931663 : Blo 1358498 9931663 := bstep (se 1 (by rfl) ⟨7448747, by rfl⟩ : syracuseStep 9931663 = 14897495) B14897495
theorem B2903303 : Blo 1358498 2903303 := bstep (se 1 (by rfl) ⟨2177477, by rfl⟩ : syracuseStep 2903303 = 4354955) B4354955
theorem B26136107 : Blo 1358498 26136107 := bstep (se 1 (by rfl) ⟨19602080, by rfl⟩ : syracuseStep 26136107 = 39204161) B39204161
theorem B3485929 : Blo 1358498 3485929 := bstep (se 2 (by rfl) ⟨1307223, by rfl⟩ : syracuseStep 3485929 = 2614447) B2614447
theorem B15495623 : Blo 1358498 15495623 := bstep (se 1 (by rfl) ⟨11621717, by rfl⟩ : syracuseStep 15495623 = 23243435) B23243435
theorem B3060251 : Blo 1358498 3060251 := bstep (se 1 (by rfl) ⟨2295188, by rfl⟩ : syracuseStep 3060251 = 4590377) B4590377
theorem B10318751 : Blo 1358498 10318751 := bstep (se 1 (by rfl) ⟨7739063, by rfl⟩ : syracuseStep 10318751 = 15478127) B15478127
theorem B1528879 : Blo 1358498 1528879 := bstep (se 1 (by rfl) ⟨1146659, by rfl⟩ : syracuseStep 1528879 = 2293319) B2293319
theorem B29398099 : Blo 1358498 29398099 := bstep (se 1 (by rfl) ⟨22048574, by rfl⟩ : syracuseStep 29398099 = 44097149) B44097149
theorem B1529167 : Blo 1358498 1529167 := bstep (se 1 (by rfl) ⟨1146875, by rfl⟩ : syracuseStep 1529167 = 2293751) B2293751
theorem B8713727 : Blo 1358498 8713727 := bstep (se 1 (by rfl) ⟨6535295, by rfl⟩ : syracuseStep 8713727 = 13070591) B13070591
theorem B23230313 : Blo 1358498 23230313 := bstep (se 2 (by rfl) ⟨8711367, by rfl⟩ : syracuseStep 23230313 = 17422735) B17422735
theorem B4585355 : Blo 1358498 4585355 := bstep (se 1 (by rfl) ⟨3439016, by rfl⟩ : syracuseStep 4585355 = 6878033) B6878033
theorem B7952339 : Blo 1358498 7952339 := bstep (se 1 (by rfl) ⟨5964254, by rfl⟩ : syracuseStep 7952339 = 11928509) B11928509
theorem B1529851 : Blo 1358498 1529851 := bstep (se 1 (by rfl) ⟨1147388, by rfl⟩ : syracuseStep 1529851 = 2294777) B2294777
theorem B1529887 : Blo 1358498 1529887 := bstep (se 1 (by rfl) ⟨1147415, by rfl⟩ : syracuseStep 1529887 = 2294831) B2294831
theorem B2037863 : Blo 1358498 2037863 := bstep (se 1 (by rfl) ⟨1528397, by rfl⟩ : syracuseStep 2037863 = 3056795) B3056795
theorem B2037887 : Blo 1358498 2037887 := bstep (se 1 (by rfl) ⟨1528415, by rfl⟩ : syracuseStep 2037887 = 3056831) B3056831
theorem B15686075 : Blo 1358498 15686075 := bstep (se 1 (by rfl) ⟨11764556, by rfl⟩ : syracuseStep 15686075 = 23529113) B23529113
theorem B9296329 : Blo 1358498 9296329 := bstep (se 2 (by rfl) ⟨3486123, by rfl⟩ : syracuseStep 9296329 = 6972247) B6972247
theorem B2579035 : Blo 1358498 2579035 := bstep (se 1 (by rfl) ⟨1934276, by rfl⟩ : syracuseStep 2579035 = 3868553) B3868553
theorem B2579195 : Blo 1358498 2579195 := bstep (se 1 (by rfl) ⟨1934396, by rfl⟩ : syracuseStep 2579195 = 3868793) B3868793
theorem B17414945 : Blo 1358498 17414945 := bstep (se 2 (by rfl) ⟨6530604, by rfl⟩ : syracuseStep 17414945 = 13061209) B13061209
theorem B2038697 : Blo 1358498 2038697 := bstep (se 2 (by rfl) ⟨764511, by rfl⟩ : syracuseStep 2038697 = 1529023) B1529023
theorem B2038751 : Blo 1358498 2038751 := bstep (se 1 (by rfl) ⟨1529063, by rfl⟩ : syracuseStep 2038751 = 3058127) B3058127
theorem B7740431 : Blo 1358498 7740431 := bstep (se 1 (by rfl) ⟨5805323, by rfl⟩ : syracuseStep 7740431 = 11610647) B11610647
theorem B1358879 : Blo 1358498 1358879 := bstep (se 1 (by rfl) ⟨1019159, by rfl⟩ : syracuseStep 1358879 = 2038319) B2038319
theorem B1358911 : Blo 1358498 1358911 := bstep (se 1 (by rfl) ⟨1019183, by rfl⟩ : syracuseStep 1358911 = 2038367) B2038367
theorem B4586759 : Blo 1358498 4586759 := bstep (se 1 (by rfl) ⟨3440069, by rfl⟩ : syracuseStep 4586759 = 6880139) B6880139
theorem B1359151 : Blo 1358498 1359151 := bstep (se 1 (by rfl) ⟨1019363, by rfl⟩ : syracuseStep 1359151 = 2038727) B2038727
theorem B2293049 : Blo 1358498 2293049 := bstep (se 2 (by rfl) ⟨859893, by rfl⟩ : syracuseStep 2293049 = 1719787) B1719787
theorem B4136275 : Blo 1358498 4136275 := bstep (se 1 (by rfl) ⟨3102206, by rfl⟩ : syracuseStep 4136275 = 6204413) B6204413
theorem B1359231 : Blo 1358498 1359231 := bstep (se 1 (by rfl) ⟨1019423, by rfl⟩ : syracuseStep 1359231 = 2038847) B2038847
theorem B27917723 : Blo 1358498 27917723 := bstep (se 1 (by rfl) ⟨20938292, by rfl⟩ : syracuseStep 27917723 = 41876585) B41876585
theorem B1359391 : Blo 1358498 1359391 := bstep (se 1 (by rfl) ⟨1019543, by rfl⟩ : syracuseStep 1359391 = 2039087) B2039087
theorem B1359551 : Blo 1358498 1359551 := bstep (se 1 (by rfl) ⟨1019663, by rfl⟩ : syracuseStep 1359551 = 2039327) B2039327
theorem B1359567 : Blo 1358498 1359567 := bstep (se 1 (by rfl) ⟨1019675, by rfl⟩ : syracuseStep 1359567 = 2039351) B2039351
theorem B1359679 : Blo 1358498 1359679 := bstep (se 1 (by rfl) ⟨1019759, by rfl⟩ : syracuseStep 1359679 = 2039519) B2039519
theorem B8716187 : Blo 1358498 8716187 := bstep (se 1 (by rfl) ⟨6537140, by rfl⟩ : syracuseStep 8716187 = 13074281) B13074281
theorem B2293663 : Blo 1358498 2293663 := bstep (se 1 (by rfl) ⟨1720247, by rfl⟩ : syracuseStep 2293663 = 3440495) B3440495
theorem B1359807 : Blo 1358498 1359807 := bstep (se 1 (by rfl) ⟨1019855, by rfl⟩ : syracuseStep 1359807 = 2039711) B2039711
theorem B8708087 : Blo 1358498 8708087 := bstep (se 1 (by rfl) ⟨6531065, by rfl⟩ : syracuseStep 8708087 = 13062131) B13062131
theorem B2039849 : Blo 1358498 2039849 := bstep (se 2 (by rfl) ⟨764943, by rfl⟩ : syracuseStep 2039849 = 1529887) B1529887
theorem B10330415 : Blo 1358498 10330415 := bstep (se 1 (by rfl) ⟨7747811, by rfl⟩ : syracuseStep 10330415 = 15495623) B15495623
theorem B1360191 : Blo 1358498 1360191 := bstep (se 1 (by rfl) ⟨1020143, by rfl⟩ : syracuseStep 1360191 = 2040287) B2040287
theorem B2040167 : Blo 1358498 2040167 := bstep (se 1 (by rfl) ⟨1530125, by rfl⟩ : syracuseStep 2040167 = 3060251) B3060251
theorem B12395105 : Blo 1358498 12395105 := bstep (se 2 (by rfl) ⟨4648164, by rfl⟩ : syracuseStep 12395105 = 9296329) B9296329
theorem B7742141 : Blo 1358498 7742141 := bstep (se 3 (by rfl) ⟨1451651, by rfl⟩ : syracuseStep 7742141 = 2903303) B2903303
theorem B10322639 : Blo 1358498 10322639 := bstep (se 1 (by rfl) ⟨7741979, by rfl⟩ : syracuseStep 10322639 = 15483959) B15483959
theorem B1721179 : Blo 1358498 1721179 := bstep (se 1 (by rfl) ⟨1290884, by rfl⟩ : syracuseStep 1721179 = 2581769) B2581769
theorem B4899799 : Blo 1358498 4899799 := bstep (se 1 (by rfl) ⟨3674849, by rfl⟩ : syracuseStep 4899799 = 7349699) B7349699
theorem B5809151 : Blo 1358498 5809151 := bstep (se 1 (by rfl) ⟨4356863, by rfl⟩ : syracuseStep 5809151 = 8713727) B8713727
theorem B2294939 : Blo 1358498 2294939 := bstep (se 1 (by rfl) ⟨1721204, by rfl⟩ : syracuseStep 2294939 = 3442409) B3442409
theorem B41829533 : Blo 1358498 41829533 := bstep (se 3 (by rfl) ⟨7843037, by rfl⟩ : syracuseStep 41829533 = 15686075) B15686075
theorem B3056903 : Blo 1358498 3056903 := bstep (se 1 (by rfl) ⟨2292677, by rfl⟩ : syracuseStep 3056903 = 4585355) B4585355
theorem B5301559 : Blo 1358498 5301559 := bstep (se 1 (by rfl) ⟨3976169, by rfl⟩ : syracuseStep 5301559 = 7952339) B7952339
theorem B2295263 : Blo 1358498 2295263 := bstep (se 1 (by rfl) ⟨1721447, by rfl⟩ : syracuseStep 2295263 = 3442895) B3442895
theorem B11609963 : Blo 1358498 11609963 := bstep (se 1 (by rfl) ⟨8707472, by rfl⟩ : syracuseStep 11609963 = 17414945) B17414945
theorem B3057839 : Blo 1358498 3057839 := bstep (se 1 (by rfl) ⟨2293379, by rfl⟩ : syracuseStep 3057839 = 4586759) B4586759
theorem B3058217 : Blo 1358498 3058217 := bstep (se 2 (by rfl) ⟨1146831, by rfl⟩ : syracuseStep 3058217 = 2293663) B2293663
theorem B5810791 : Blo 1358498 5810791 := bstep (se 1 (by rfl) ⟨4358093, by rfl⟩ : syracuseStep 5810791 = 8716187) B8716187
theorem B4647905 : Blo 1358498 4647905 := bstep (se 2 (by rfl) ⟨1742964, by rfl⟩ : syracuseStep 4647905 = 3485929) B3485929
theorem B5803001 : Blo 1358498 5803001 := bstep (se 2 (by rfl) ⟨2176125, by rfl⟩ : syracuseStep 5803001 = 4352251) B4352251
theorem B3058793 : Blo 1358498 3058793 := bstep (se 2 (by rfl) ⟨1147047, by rfl⟩ : syracuseStep 3058793 = 2294095) B2294095
theorem B13242217 : Blo 1358498 13242217 := bstep (se 2 (by rfl) ⟨4965831, by rfl⟩ : syracuseStep 13242217 = 9931663) B9931663
theorem B15486875 : Blo 1358498 15486875 := bstep (se 1 (by rfl) ⟨11615156, by rfl⟩ : syracuseStep 15486875 = 23230313) B23230313
theorem B1046097929 : Blo 1358498 1046097929 := bstep (se 2 (by rfl) ⟨392286723, by rfl⟩ : syracuseStep 1046097929 = 784573447) B784573447
theorem B4354813 : Blo 1358498 4354813 := bstep (se 3 (by rfl) ⟨816527, by rfl⟩ : syracuseStep 4354813 = 1633055) B1633055
theorem B1528699 : Blo 1358498 1528699 := bstep (se 1 (by rfl) ⟨1146524, by rfl⟩ : syracuseStep 1528699 = 2293049) B2293049
theorem B23221565 : Blo 1358498 23221565 := bstep (se 3 (by rfl) ⟨4354043, by rfl⟩ : syracuseStep 23221565 = 8708087) B8708087
theorem B19600987 : Blo 1358498 19600987 := bstep (se 1 (by rfl) ⟨14700740, by rfl⟩ : syracuseStep 19600987 = 29401481) B29401481
theorem B5035715 : Blo 1358498 5035715 := bstep (se 1 (by rfl) ⟨3776786, by rfl⟩ : syracuseStep 5035715 = 7553573) B7553573
theorem B11032307 : Blo 1358498 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B37213991 : Blo 1358498 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B6879167 : Blo 1358498 6879167 := bstep (se 1 (by rfl) ⟨5159375, by rfl⟩ : syracuseStep 6879167 = 10318751) B10318751
theorem B3438713 : Blo 1358498 3438713 := bstep (se 2 (by rfl) ⟨1289517, by rfl⟩ : syracuseStep 3438713 = 2579035) B2579035
theorem B1530031 : Blo 1358498 1530031 := bstep (se 1 (by rfl) ⟨1147523, by rfl⟩ : syracuseStep 1530031 = 2295047) B2295047
theorem B111655097 : Blo 1358498 111655097 := bstep (se 2 (by rfl) ⟨41870661, by rfl⟩ : syracuseStep 111655097 = 83741323) B83741323
theorem B2039801 : Blo 1358498 2039801 := bstep (se 2 (by rfl) ⟨764925, by rfl⟩ : syracuseStep 2039801 = 1529851) B1529851
theorem B2037983 : Blo 1358498 2037983 := bstep (se 1 (by rfl) ⟨1528487, by rfl⟩ : syracuseStep 2037983 = 3056975) B3056975
theorem B9296489 : Blo 1358498 9296489 := bstep (se 2 (by rfl) ⟨3486183, by rfl⟩ : syracuseStep 9296489 = 6972367) B6972367
theorem B2038427 : Blo 1358498 2038427 := bstep (se 1 (by rfl) ⟨1528820, by rfl⟩ : syracuseStep 2038427 = 3057641) B3057641
theorem B2038463 : Blo 1358498 2038463 := bstep (se 1 (by rfl) ⟨1528847, by rfl⟩ : syracuseStep 2038463 = 3057695) B3057695
theorem B2038505 : Blo 1358498 2038505 := bstep (se 2 (by rfl) ⟨764439, by rfl⟩ : syracuseStep 2038505 = 1528879) B1528879
theorem B1358575 : Blo 1358498 1358575 := bstep (se 1 (by rfl) ⟨1018931, by rfl⟩ : syracuseStep 1358575 = 2037863) B2037863
theorem B1358591 : Blo 1358498 1358591 := bstep (se 1 (by rfl) ⟨1018943, by rfl⟩ : syracuseStep 1358591 = 2037887) B2037887
theorem B39197465 : Blo 1358498 39197465 := bstep (se 2 (by rfl) ⟨14699049, by rfl⟩ : syracuseStep 39197465 = 29398099) B29398099
theorem B33086303 : Blo 1358498 33086303 := bstep (se 1 (by rfl) ⟨24814727, by rfl⟩ : syracuseStep 33086303 = 49629455) B49629455
theorem B2038889 : Blo 1358498 2038889 := bstep (se 2 (by rfl) ⟨764583, by rfl⟩ : syracuseStep 2038889 = 1529167) B1529167
theorem B22060133 : Blo 1358498 22060133 := bstep (se 4 (by rfl) ⟨2068137, by rfl⟩ : syracuseStep 22060133 = 4136275) B4136275
theorem B1719463 : Blo 1358498 1719463 := bstep (se 1 (by rfl) ⟨1289597, by rfl⟩ : syracuseStep 1719463 = 2579195) B2579195
theorem B3874043 : Blo 1358498 3874043 := bstep (se 1 (by rfl) ⟨2905532, by rfl⟩ : syracuseStep 3874043 = 5811065) B5811065
theorem B1359131 : Blo 1358498 1359131 := bstep (se 1 (by rfl) ⟨1019348, by rfl⟩ : syracuseStep 1359131 = 2038697) B2038697
theorem B1359167 : Blo 1358498 1359167 := bstep (se 1 (by rfl) ⟨1019375, by rfl⟩ : syracuseStep 1359167 = 2038751) B2038751
theorem B5160287 : Blo 1358498 5160287 := bstep (se 1 (by rfl) ⟨3870215, by rfl⟩ : syracuseStep 5160287 = 7740431) B7740431
theorem B18611815 : Blo 1358498 18611815 := bstep (se 1 (by rfl) ⟨13958861, by rfl⟩ : syracuseStep 18611815 = 27917723) B27917723
theorem B17424071 : Blo 1358498 17424071 := bstep (se 1 (by rfl) ⟨13068053, by rfl⟩ : syracuseStep 17424071 = 26136107) B26136107
theorem B1359899 : Blo 1358498 1359899 := bstep (se 1 (by rfl) ⟨1019924, by rfl⟩ : syracuseStep 1359899 = 2039849) B2039849
theorem B2040041 : Blo 1358498 2040041 := bstep (se 2 (by rfl) ⟨765015, by rfl⟩ : syracuseStep 2040041 = 1530031) B1530031
theorem B1360111 : Blo 1358498 1360111 := bstep (se 1 (by rfl) ⟨1020083, by rfl⟩ : syracuseStep 1360111 = 2040167) B2040167
theorem B5161427 : Blo 1358498 5161427 := bstep (se 1 (by rfl) ⟨3871070, by rfl⟩ : syracuseStep 5161427 = 7742141) B7742141
theorem B6881759 : Blo 1358498 6881759 := bstep (se 1 (by rfl) ⟨5161319, by rfl⟩ : syracuseStep 6881759 = 10322639) B10322639
theorem B27886355 : Blo 1358498 27886355 := bstep (se 1 (by rfl) ⟨20914766, by rfl⟩ : syracuseStep 27886355 = 41829533) B41829533
theorem B2294905 : Blo 1358498 2294905 := bstep (se 2 (by rfl) ⟨860589, by rfl⟩ : syracuseStep 2294905 = 1721179) B1721179
theorem B1359867 : Blo 1358498 1359867 := bstep (se 1 (by rfl) ⟨1019900, by rfl⟩ : syracuseStep 1359867 = 2039801) B2039801
theorem B24790637 : Blo 1358498 24790637 := bstep (se 3 (by rfl) ⟨4648244, by rfl⟩ : syracuseStep 24790637 = 9296489) B9296489
theorem B3098603 : Blo 1358498 3098603 := bstep (se 1 (by rfl) ⟨2323952, by rfl⟩ : syracuseStep 3098603 = 4647905) B4647905
theorem B3868667 : Blo 1358498 3868667 := bstep (se 1 (by rfl) ⟨2901500, by rfl⟩ : syracuseStep 3868667 = 5803001) B5803001
theorem B14706755 : Blo 1358498 14706755 := bstep (se 1 (by rfl) ⟨11030066, by rfl⟩ : syracuseStep 14706755 = 22060133) B22060133
theorem B26134649 : Blo 1358498 26134649 := bstep (se 2 (by rfl) ⟨9800493, by rfl⟩ : syracuseStep 26134649 = 19600987) B19600987
theorem B24815753 : Blo 1358498 24815753 := bstep (se 2 (by rfl) ⟨9305907, by rfl⟩ : syracuseStep 24815753 = 18611815) B18611815
theorem B2582695 : Blo 1358498 2582695 := bstep (se 1 (by rfl) ⟨1937021, by rfl⟩ : syracuseStep 2582695 = 3874043) B3874043
theorem B17656289 : Blo 1358498 17656289 := bstep (se 2 (by rfl) ⟨6621108, by rfl⟩ : syracuseStep 17656289 = 13242217) B13242217
theorem B10324583 : Blo 1358498 10324583 := bstep (se 1 (by rfl) ⟨7743437, by rfl⟩ : syracuseStep 10324583 = 15486875) B15486875
theorem B24809327 : Blo 1358498 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B6533065 : Blo 1358498 6533065 := bstep (se 2 (by rfl) ⟨2449899, by rfl⟩ : syracuseStep 6533065 = 4899799) B4899799
theorem B74436731 : Blo 1358498 74436731 := bstep (se 1 (by rfl) ⟨55827548, by rfl⟩ : syracuseStep 74436731 = 111655097) B111655097
theorem B22057535 : Blo 1358498 22057535 := bstep (se 1 (by rfl) ⟨16543151, by rfl⟩ : syracuseStep 22057535 = 33086303) B33086303
theorem B2789594477 : Blo 1358498 2789594477 := bstep (se 3 (by rfl) ⟨523048964, by rfl⟩ : syracuseStep 2789594477 = 1046097929) B1046097929
theorem B6886943 : Blo 1358498 6886943 := bstep (se 1 (by rfl) ⟨5165207, by rfl⟩ : syracuseStep 6886943 = 10330415) B10330415
theorem B8263403 : Blo 1358498 8263403 := bstep (se 1 (by rfl) ⟨6197552, by rfl⟩ : syracuseStep 8263403 = 12395105) B12395105
theorem B3872767 : Blo 1358498 3872767 := bstep (se 1 (by rfl) ⟨2904575, by rfl⟩ : syracuseStep 3872767 = 5809151) B5809151
theorem B1529959 : Blo 1358498 1529959 := bstep (se 1 (by rfl) ⟨1147469, by rfl⟩ : syracuseStep 1529959 = 2294939) B2294939
theorem B7747721 : Blo 1358498 7747721 := bstep (se 2 (by rfl) ⟨2905395, by rfl⟩ : syracuseStep 7747721 = 5810791) B5810791
theorem B2037935 : Blo 1358498 2037935 := bstep (se 1 (by rfl) ⟨1528451, by rfl⟩ : syracuseStep 2037935 = 3056903) B3056903
theorem B15481043 : Blo 1358498 15481043 := bstep (se 1 (by rfl) ⟨11610782, by rfl⟩ : syracuseStep 15481043 = 23221565) B23221565
theorem B1530175 : Blo 1358498 1530175 := bstep (se 1 (by rfl) ⟨1147631, by rfl⟩ : syracuseStep 1530175 = 2295263) B2295263
theorem B5806417 : Blo 1358498 5806417 := bstep (se 2 (by rfl) ⟨2177406, by rfl⟩ : syracuseStep 5806417 = 4354813) B4354813
theorem B3357143 : Blo 1358498 3357143 := bstep (se 1 (by rfl) ⟨2517857, by rfl⟩ : syracuseStep 3357143 = 5035715) B5035715
theorem B7354871 : Blo 1358498 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B2038265 : Blo 1358498 2038265 := bstep (se 2 (by rfl) ⟨764349, by rfl⟩ : syracuseStep 2038265 = 1528699) B1528699
theorem B7739975 : Blo 1358498 7739975 := bstep (se 1 (by rfl) ⟨5804981, by rfl⟩ : syracuseStep 7739975 = 11609963) B11609963
theorem B4586111 : Blo 1358498 4586111 := bstep (se 1 (by rfl) ⟨3439583, by rfl⟩ : syracuseStep 4586111 = 6879167) B6879167
theorem B2292475 : Blo 1358498 2292475 := bstep (se 1 (by rfl) ⟨1719356, by rfl⟩ : syracuseStep 2292475 = 3438713) B3438713
theorem B2038559 : Blo 1358498 2038559 := bstep (se 1 (by rfl) ⟨1528919, by rfl⟩ : syracuseStep 2038559 = 3057839) B3057839
theorem B1358655 : Blo 1358498 1358655 := bstep (se 1 (by rfl) ⟨1018991, by rfl⟩ : syracuseStep 1358655 = 2037983) B2037983
theorem B2292617 : Blo 1358498 2292617 := bstep (se 2 (by rfl) ⟨859731, by rfl⟩ : syracuseStep 2292617 = 1719463) B1719463
theorem B2038811 : Blo 1358498 2038811 := bstep (se 1 (by rfl) ⟨1529108, by rfl⟩ : syracuseStep 2038811 = 3058217) B3058217
theorem B7068745 : Blo 1358498 7068745 := bstep (se 2 (by rfl) ⟨2650779, by rfl⟩ : syracuseStep 7068745 = 5301559) B5301559
theorem B1358951 : Blo 1358498 1358951 := bstep (se 1 (by rfl) ⟨1019213, by rfl⟩ : syracuseStep 1358951 = 2038427) B2038427
theorem B1358975 : Blo 1358498 1358975 := bstep (se 1 (by rfl) ⟨1019231, by rfl⟩ : syracuseStep 1358975 = 2038463) B2038463
theorem B1359003 : Blo 1358498 1359003 := bstep (se 1 (by rfl) ⟨1019252, by rfl⟩ : syracuseStep 1359003 = 2038505) B2038505
theorem B26131643 : Blo 1358498 26131643 := bstep (se 1 (by rfl) ⟨19598732, by rfl⟩ : syracuseStep 26131643 = 39197465) B39197465
theorem B1359259 : Blo 1358498 1359259 := bstep (se 1 (by rfl) ⟨1019444, by rfl⟩ : syracuseStep 1359259 = 2038889) B2038889
theorem B2039195 : Blo 1358498 2039195 := bstep (se 1 (by rfl) ⟨1529396, by rfl⟩ : syracuseStep 2039195 = 3058793) B3058793
theorem B3440191 : Blo 1358498 3440191 := bstep (se 1 (by rfl) ⟨2580143, by rfl⟩ : syracuseStep 3440191 = 5160287) B5160287
theorem B11616047 : Blo 1358498 11616047 := bstep (se 1 (by rfl) ⟨8712035, by rfl⟩ : syracuseStep 11616047 = 17424071) B17424071
theorem B2039945 : Blo 1358498 2039945 := bstep (se 2 (by rfl) ⟨764979, by rfl⟩ : syracuseStep 2039945 = 1529959) B1529959
theorem B1360027 : Blo 1358498 1360027 := bstep (se 1 (by rfl) ⟨1020020, by rfl⟩ : syracuseStep 1360027 = 2040041) B2040041
theorem B3440951 : Blo 1358498 3440951 := bstep (se 1 (by rfl) ⟨2580713, by rfl⟩ : syracuseStep 3440951 = 5161427) B5161427
theorem B4587839 : Blo 1358498 4587839 := bstep (se 1 (by rfl) ⟨3440879, by rfl⟩ : syracuseStep 4587839 = 6881759) B6881759
theorem B14705023 : Blo 1358498 14705023 := bstep (se 1 (by rfl) ⟨11028767, by rfl⟩ : syracuseStep 14705023 = 22057535) B22057535
theorem B2040233 : Blo 1358498 2040233 := bstep (se 2 (by rfl) ⟨765087, by rfl⟩ : syracuseStep 2040233 = 1530175) B1530175
theorem B7741889 : Blo 1358498 7741889 := bstep (se 2 (by rfl) ⟨2903208, by rfl⟩ : syracuseStep 7741889 = 5806417) B5806417
theorem B3056633 : Blo 1358498 3056633 := bstep (se 2 (by rfl) ⟨1146237, by rfl⟩ : syracuseStep 3056633 = 2292475) B2292475
theorem B2065735 : Blo 1358498 2065735 := bstep (se 1 (by rfl) ⟨1549301, by rfl⟩ : syracuseStep 2065735 = 3098603) B3098603
theorem B2238095 : Blo 1358498 2238095 := bstep (se 1 (by rfl) ⟨1678571, by rfl⟩ : syracuseStep 2238095 = 3357143) B3357143
theorem B6883055 : Blo 1358498 6883055 := bstep (se 1 (by rfl) ⟨5162291, by rfl⟩ : syracuseStep 6883055 = 10324583) B10324583
theorem B3057407 : Blo 1358498 3057407 := bstep (se 1 (by rfl) ⟨2293055, by rfl⟩ : syracuseStep 3057407 = 4586111) B4586111
theorem B7744031 : Blo 1358498 7744031 := bstep (se 1 (by rfl) ⟨5808023, by rfl⟩ : syracuseStep 7744031 = 11616047) B11616047
theorem B8710753 : Blo 1358498 8710753 := bstep (se 2 (by rfl) ⟨3266532, by rfl⟩ : syracuseStep 8710753 = 6533065) B6533065
theorem B5163689 : Blo 1358498 5163689 := bstep (se 2 (by rfl) ⟨1936383, by rfl⟩ : syracuseStep 5163689 = 3872767) B3872767
theorem B3443593 : Blo 1358498 3443593 := bstep (se 2 (by rfl) ⟨1291347, by rfl⟩ : syracuseStep 3443593 = 2582695) B2582695
theorem B18590903 : Blo 1358498 18590903 := bstep (se 1 (by rfl) ⟨13943177, by rfl⟩ : syracuseStep 18590903 = 27886355) B27886355
theorem B4591295 : Blo 1358498 4591295 := bstep (se 1 (by rfl) ⟨3443471, by rfl⟩ : syracuseStep 4591295 = 6886943) B6886943
theorem B16527091 : Blo 1358498 16527091 := bstep (se 1 (by rfl) ⟨12395318, by rfl⟩ : syracuseStep 16527091 = 24790637) B24790637
theorem B5508935 : Blo 1358498 5508935 := bstep (se 1 (by rfl) ⟨4131701, by rfl⟩ : syracuseStep 5508935 = 8263403) B8263403
theorem B16543835 : Blo 1358498 16543835 := bstep (se 1 (by rfl) ⟨12407876, by rfl⟩ : syracuseStep 16543835 = 24815753) B24815753
theorem B5165147 : Blo 1358498 5165147 := bstep (se 1 (by rfl) ⟨3873860, by rfl⟩ : syracuseStep 5165147 = 7747721) B7747721
theorem B9424993 : Blo 1358498 9424993 := bstep (se 2 (by rfl) ⟨3534372, by rfl⟩ : syracuseStep 9424993 = 7068745) B7068745
theorem B3059873 : Blo 1358498 3059873 := bstep (se 2 (by rfl) ⟨1147452, by rfl⟩ : syracuseStep 3059873 = 2294905) B2294905
theorem B4903247 : Blo 1358498 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B1528411 : Blo 1358498 1528411 := bstep (se 1 (by rfl) ⟨1146308, by rfl⟩ : syracuseStep 1528411 = 2292617) B2292617
theorem B17421095 : Blo 1358498 17421095 := bstep (se 1 (by rfl) ⟨13065821, by rfl⟩ : syracuseStep 17421095 = 26131643) B26131643
theorem B49624487 : Blo 1358498 49624487 := bstep (se 1 (by rfl) ⟨37218365, by rfl⟩ : syracuseStep 49624487 = 74436731) B74436731
theorem B1859729651 : Blo 1358498 1859729651 := bstep (se 1 (by rfl) ⟨1394797238, by rfl⟩ : syracuseStep 1859729651 = 2789594477) B2789594477
theorem B2579111 : Blo 1358498 2579111 := bstep (se 1 (by rfl) ⟨1934333, by rfl⟩ : syracuseStep 2579111 = 3868667) B3868667
theorem B9804503 : Blo 1358498 9804503 := bstep (se 1 (by rfl) ⟨7353377, by rfl⟩ : syracuseStep 9804503 = 14706755) B14706755
theorem B17423099 : Blo 1358498 17423099 := bstep (se 1 (by rfl) ⟨13067324, by rfl⟩ : syracuseStep 17423099 = 26134649) B26134649
theorem B1358623 : Blo 1358498 1358623 := bstep (se 1 (by rfl) ⟨1018967, by rfl⟩ : syracuseStep 1358623 = 2037935) B2037935
theorem B10320695 : Blo 1358498 10320695 := bstep (se 1 (by rfl) ⟨7740521, by rfl⟩ : syracuseStep 10320695 = 15481043) B15481043
theorem B11770859 : Blo 1358498 11770859 := bstep (se 1 (by rfl) ⟨8828144, by rfl⟩ : syracuseStep 11770859 = 17656289) B17656289
theorem B1358843 : Blo 1358498 1358843 := bstep (se 1 (by rfl) ⟨1019132, by rfl⟩ : syracuseStep 1358843 = 2038265) B2038265
theorem B5159983 : Blo 1358498 5159983 := bstep (se 1 (by rfl) ⟨3869987, by rfl⟩ : syracuseStep 5159983 = 7739975) B7739975
theorem B1359039 : Blo 1358498 1359039 := bstep (se 1 (by rfl) ⟨1019279, by rfl⟩ : syracuseStep 1359039 = 2038559) B2038559
theorem B1359207 : Blo 1358498 1359207 := bstep (se 1 (by rfl) ⟨1019405, by rfl⟩ : syracuseStep 1359207 = 2038811) B2038811
theorem B4586921 : Blo 1358498 4586921 := bstep (se 2 (by rfl) ⟨1720095, by rfl⟩ : syracuseStep 4586921 = 3440191) B3440191
theorem B1359463 : Blo 1358498 1359463 := bstep (se 1 (by rfl) ⟨1019597, by rfl⟩ : syracuseStep 1359463 = 2039195) B2039195
theorem B16539551 : Blo 1358498 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B1359963 : Blo 1358498 1359963 := bstep (se 1 (by rfl) ⟨1019972, by rfl⟩ : syracuseStep 1359963 = 2039945) B2039945
theorem B2039915 : Blo 1358498 2039915 := bstep (se 1 (by rfl) ⟨1529936, by rfl⟩ : syracuseStep 2039915 = 3059873) B3059873
theorem B12566657 : Blo 1358498 12566657 := bstep (se 2 (by rfl) ⟨4712496, by rfl⟩ : syracuseStep 12566657 = 9424993) B9424993
theorem B2293967 : Blo 1358498 2293967 := bstep (se 1 (by rfl) ⟨1720475, by rfl⟩ : syracuseStep 2293967 = 3440951) B3440951
theorem B3268831 : Blo 1358498 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B1360155 : Blo 1358498 1360155 := bstep (se 1 (by rfl) ⟨1020116, by rfl⟩ : syracuseStep 1360155 = 2040233) B2040233
theorem B5161259 : Blo 1358498 5161259 := bstep (se 1 (by rfl) ⟨3870944, by rfl⟩ : syracuseStep 5161259 = 7741889) B7741889
theorem B4588703 : Blo 1358498 4588703 := bstep (se 1 (by rfl) ⟨3441527, by rfl⟩ : syracuseStep 4588703 = 6883055) B6883055
theorem B1239819767 : Blo 1358498 1239819767 := bstep (se 1 (by rfl) ⟨929864825, by rfl⟩ : syracuseStep 1239819767 = 1859729651) B1859729651
theorem B5162687 : Blo 1358498 5162687 := bstep (se 1 (by rfl) ⟨3872015, by rfl⟩ : syracuseStep 5162687 = 7744031) B7744031
theorem B2754313 : Blo 1358498 2754313 := bstep (se 2 (by rfl) ⟨1032867, by rfl⟩ : syracuseStep 2754313 = 2065735) B2065735
theorem B3442459 : Blo 1358498 3442459 := bstep (se 1 (by rfl) ⟨2581844, by rfl⟩ : syracuseStep 3442459 = 5163689) B5163689
theorem B3057947 : Blo 1358498 3057947 := bstep (se 1 (by rfl) ⟨2293460, by rfl⟩ : syracuseStep 3057947 = 4586921) B4586921
theorem B3672623 : Blo 1358498 3672623 := bstep (se 1 (by rfl) ⟨2754467, by rfl⟩ : syracuseStep 3672623 = 5508935) B5508935
theorem B11029223 : Blo 1358498 11029223 := bstep (se 1 (by rfl) ⟨8271917, by rfl⟩ : syracuseStep 11029223 = 16543835) B16543835
theorem B3443431 : Blo 1358498 3443431 := bstep (se 1 (by rfl) ⟨2582573, by rfl⟩ : syracuseStep 3443431 = 5165147) B5165147
theorem B3058559 : Blo 1358498 3058559 := bstep (se 1 (by rfl) ⟨2293919, by rfl⟩ : syracuseStep 3058559 = 4587839) B4587839
theorem B19606697 : Blo 1358498 19606697 := bstep (se 2 (by rfl) ⟨7352511, by rfl⟩ : syracuseStep 19606697 = 14705023) B14705023
theorem B33082991 : Blo 1358498 33082991 := bstep (se 1 (by rfl) ⟨24812243, by rfl⟩ : syracuseStep 33082991 = 49624487) B49624487
theorem B4591457 : Blo 1358498 4591457 := bstep (se 2 (by rfl) ⟨1721796, by rfl⟩ : syracuseStep 4591457 = 3443593) B3443593
theorem B5968253 : Blo 1358498 5968253 := bstep (se 3 (by rfl) ⟨1119047, by rfl⟩ : syracuseStep 5968253 = 2238095) B2238095
theorem B3060863 : Blo 1358498 3060863 := bstep (se 1 (by rfl) ⟨2295647, by rfl⟩ : syracuseStep 3060863 = 4591295) B4591295
theorem B11614063 : Blo 1358498 11614063 := bstep (se 1 (by rfl) ⟨8710547, by rfl⟩ : syracuseStep 11614063 = 17421095) B17421095
theorem B2037755 : Blo 1358498 2037755 := bstep (se 1 (by rfl) ⟨1528316, by rfl⟩ : syracuseStep 2037755 = 3056633) B3056633
theorem B2037881 : Blo 1358498 2037881 := bstep (se 2 (by rfl) ⟨764205, by rfl⟩ : syracuseStep 2037881 = 1528411) B1528411
theorem B11614337 : Blo 1358498 11614337 := bstep (se 2 (by rfl) ⟨4355376, by rfl⟩ : syracuseStep 11614337 = 8710753) B8710753
theorem B2038271 : Blo 1358498 2038271 := bstep (se 1 (by rfl) ⟨1528703, by rfl⟩ : syracuseStep 2038271 = 3057407) B3057407
theorem B6879977 : Blo 1358498 6879977 := bstep (se 2 (by rfl) ⟨2579991, by rfl⟩ : syracuseStep 6879977 = 5159983) B5159983
theorem B1719407 : Blo 1358498 1719407 := bstep (se 1 (by rfl) ⟨1289555, by rfl⟩ : syracuseStep 1719407 = 2579111) B2579111
theorem B6536335 : Blo 1358498 6536335 := bstep (se 1 (by rfl) ⟨4902251, by rfl⟩ : syracuseStep 6536335 = 9804503) B9804503
theorem B11615399 : Blo 1358498 11615399 := bstep (se 1 (by rfl) ⟨8711549, by rfl⟩ : syracuseStep 11615399 = 17423099) B17423099
theorem B6880463 : Blo 1358498 6880463 := bstep (se 1 (by rfl) ⟨5160347, by rfl⟩ : syracuseStep 6880463 = 10320695) B10320695
theorem B7847239 : Blo 1358498 7847239 := bstep (se 1 (by rfl) ⟨5885429, by rfl⟩ : syracuseStep 7847239 = 11770859) B11770859
theorem B12393935 : Blo 1358498 12393935 := bstep (se 1 (by rfl) ⟨9295451, by rfl⟩ : syracuseStep 12393935 = 18590903) B18590903
theorem B22036121 : Blo 1358498 22036121 := bstep (se 2 (by rfl) ⟨8263545, by rfl⟩ : syracuseStep 22036121 = 16527091) B16527091
theorem B11026367 : Blo 1358498 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B1359943 : Blo 1358498 1359943 := bstep (se 1 (by rfl) ⟨1019957, by rfl⟩ : syracuseStep 1359943 = 2039915) B2039915
theorem B3440839 : Blo 1358498 3440839 := bstep (se 1 (by rfl) ⟨2580629, by rfl⟩ : syracuseStep 3440839 = 5161259) B5161259
theorem B4358441 : Blo 1358498 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B2040575 : Blo 1358498 2040575 := bstep (se 1 (by rfl) ⟨1530431, by rfl⟩ : syracuseStep 2040575 = 3060863) B3060863
theorem B3441791 : Blo 1358498 3441791 := bstep (se 1 (by rfl) ⟨2581343, by rfl⟩ : syracuseStep 3441791 = 5162687) B5162687
theorem B14689669 : Blo 1358498 14689669 := bstep (se 4 (by rfl) ⟨1377156, by rfl⟩ : syracuseStep 14689669 = 2754313) B2754313
theorem B7742891 : Blo 1358498 7742891 := bstep (se 1 (by rfl) ⟨5807168, by rfl⟩ : syracuseStep 7742891 = 11614337) B11614337
theorem B10462985 : Blo 1358498 10462985 := bstep (se 2 (by rfl) ⟨3923619, by rfl⟩ : syracuseStep 10462985 = 7847239) B7847239
theorem B7743599 : Blo 1358498 7743599 := bstep (se 1 (by rfl) ⟨5807699, by rfl⟩ : syracuseStep 7743599 = 11615399) B11615399
theorem B4589945 : Blo 1358498 4589945 := bstep (se 2 (by rfl) ⟨1721229, by rfl⟩ : syracuseStep 4589945 = 3442459) B3442459
theorem B22055327 : Blo 1358498 22055327 := bstep (se 1 (by rfl) ⟨16541495, by rfl⟩ : syracuseStep 22055327 = 33082991) B33082991
theorem B14690747 : Blo 1358498 14690747 := bstep (se 1 (by rfl) ⟨11018060, by rfl⟩ : syracuseStep 14690747 = 22036121) B22036121
theorem B15485417 : Blo 1358498 15485417 := bstep (se 2 (by rfl) ⟨5807031, by rfl⟩ : syracuseStep 15485417 = 11614063) B11614063
theorem B7350911 : Blo 1358498 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B3059135 : Blo 1358498 3059135 := bstep (se 1 (by rfl) ⟨2294351, by rfl⟩ : syracuseStep 3059135 = 4588703) B4588703
theorem B4591241 : Blo 1358498 4591241 := bstep (se 2 (by rfl) ⟨1721715, by rfl⟩ : syracuseStep 4591241 = 3443431) B3443431
theorem B7352815 : Blo 1358498 7352815 := bstep (se 1 (by rfl) ⟨5514611, by rfl⟩ : syracuseStep 7352815 = 11029223) B11029223
theorem B13071131 : Blo 1358498 13071131 := bstep (se 1 (by rfl) ⟨9803348, by rfl⟩ : syracuseStep 13071131 = 19606697) B19606697
theorem B8262623 : Blo 1358498 8262623 := bstep (se 1 (by rfl) ⟨6196967, by rfl⟩ : syracuseStep 8262623 = 12393935) B12393935
theorem B3060971 : Blo 1358498 3060971 := bstep (se 1 (by rfl) ⟨2295728, by rfl⟩ : syracuseStep 3060971 = 4591457) B4591457
theorem B8377771 : Blo 1358498 8377771 := bstep (se 1 (by rfl) ⟨6283328, by rfl⟩ : syracuseStep 8377771 = 12566657) B12566657
theorem B1529311 : Blo 1358498 1529311 := bstep (se 1 (by rfl) ⟨1146983, by rfl⟩ : syracuseStep 1529311 = 2293967) B2293967
theorem B4585085 : Blo 1358498 4585085 := bstep (se 3 (by rfl) ⟨859703, by rfl⟩ : syracuseStep 4585085 = 1719407) B1719407
theorem B15915341 : Blo 1358498 15915341 := bstep (se 3 (by rfl) ⟨2984126, by rfl⟩ : syracuseStep 15915341 = 5968253) B5968253
theorem B826546511 : Blo 1358498 826546511 := bstep (se 1 (by rfl) ⟨619909883, by rfl⟩ : syracuseStep 826546511 = 1239819767) B1239819767
theorem B1358503 : Blo 1358498 1358503 := bstep (se 1 (by rfl) ⟨1018877, by rfl⟩ : syracuseStep 1358503 = 2037755) B2037755
theorem B1358587 : Blo 1358498 1358587 := bstep (se 1 (by rfl) ⟨1018940, by rfl⟩ : syracuseStep 1358587 = 2037881) B2037881
theorem B2038631 : Blo 1358498 2038631 := bstep (se 1 (by rfl) ⟨1528973, by rfl⟩ : syracuseStep 2038631 = 3057947) B3057947
theorem B8715113 : Blo 1358498 8715113 := bstep (se 2 (by rfl) ⟨3268167, by rfl⟩ : syracuseStep 8715113 = 6536335) B6536335
theorem B1358847 : Blo 1358498 1358847 := bstep (se 1 (by rfl) ⟨1019135, by rfl⟩ : syracuseStep 1358847 = 2038271) B2038271
theorem B2448415 : Blo 1358498 2448415 := bstep (se 1 (by rfl) ⟨1836311, by rfl⟩ : syracuseStep 2448415 = 3672623) B3672623
theorem B4586651 : Blo 1358498 4586651 := bstep (se 1 (by rfl) ⟨3439988, by rfl⟩ : syracuseStep 4586651 = 6879977) B6879977
theorem B2039039 : Blo 1358498 2039039 := bstep (se 1 (by rfl) ⟨1529279, by rfl⟩ : syracuseStep 2039039 = 3058559) B3058559
theorem B4586975 : Blo 1358498 4586975 := bstep (se 1 (by rfl) ⟨3440231, by rfl⟩ : syracuseStep 4586975 = 6880463) B6880463
theorem B4587785 : Blo 1358498 4587785 := bstep (se 2 (by rfl) ⟨1720419, by rfl⟩ : syracuseStep 4587785 = 3440839) B3440839
theorem B1360383 : Blo 1358498 1360383 := bstep (se 1 (by rfl) ⟨1020287, by rfl⟩ : syracuseStep 1360383 = 2040575) B2040575
theorem B2294527 : Blo 1358498 2294527 := bstep (se 1 (by rfl) ⟨1720895, by rfl⟩ : syracuseStep 2294527 = 3441791) B3441791
theorem B2040647 : Blo 1358498 2040647 := bstep (se 1 (by rfl) ⟨1530485, by rfl⟩ : syracuseStep 2040647 = 3060971) B3060971
theorem B5161927 : Blo 1358498 5161927 := bstep (se 1 (by rfl) ⟨3871445, by rfl⟩ : syracuseStep 5161927 = 7742891) B7742891
theorem B3056723 : Blo 1358498 3056723 := bstep (se 1 (by rfl) ⟨2292542, by rfl⟩ : syracuseStep 3056723 = 4585085) B4585085
theorem B5162399 : Blo 1358498 5162399 := bstep (se 1 (by rfl) ⟨3871799, by rfl⟩ : syracuseStep 5162399 = 7743599) B7743599
theorem B10610227 : Blo 1358498 10610227 := bstep (se 1 (by rfl) ⟨7957670, by rfl⟩ : syracuseStep 10610227 = 15915341) B15915341
theorem B10323611 : Blo 1358498 10323611 := bstep (se 1 (by rfl) ⟨7742708, by rfl⟩ : syracuseStep 10323611 = 15485417) B15485417
theorem B4900607 : Blo 1358498 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B5810075 : Blo 1358498 5810075 := bstep (se 1 (by rfl) ⟨4357556, by rfl⟩ : syracuseStep 5810075 = 8715113) B8715113
theorem B3057767 : Blo 1358498 3057767 := bstep (se 1 (by rfl) ⟨2293325, by rfl⟩ : syracuseStep 3057767 = 4586651) B4586651
theorem B3057983 : Blo 1358498 3057983 := bstep (se 1 (by rfl) ⟨2293487, by rfl⟩ : syracuseStep 3057983 = 4586975) B4586975
theorem B5508415 : Blo 1358498 5508415 := bstep (se 1 (by rfl) ⟨4131311, by rfl⟩ : syracuseStep 5508415 = 8262623) B8262623
theorem B6975323 : Blo 1358498 6975323 := bstep (se 1 (by rfl) ⟨5231492, by rfl⟩ : syracuseStep 6975323 = 10462985) B10462985
theorem B3264553 : Blo 1358498 3264553 := bstep (se 2 (by rfl) ⟨1224207, by rfl⟩ : syracuseStep 3264553 = 2448415) B2448415
theorem B551031007 : Blo 1358498 551031007 := bstep (se 1 (by rfl) ⟨413273255, by rfl⟩ : syracuseStep 551031007 = 826546511) B826546511
theorem B3059963 : Blo 1358498 3059963 := bstep (se 1 (by rfl) ⟨2294972, by rfl⟩ : syracuseStep 3059963 = 4589945) B4589945
theorem B9793831 : Blo 1358498 9793831 := bstep (se 1 (by rfl) ⟨7345373, by rfl⟩ : syracuseStep 9793831 = 14690747) B14690747
theorem B11170361 : Blo 1358498 11170361 := bstep (se 2 (by rfl) ⟨4188885, by rfl⟩ : syracuseStep 11170361 = 8377771) B8377771
theorem B3060827 : Blo 1358498 3060827 := bstep (se 1 (by rfl) ⟨2295620, by rfl⟩ : syracuseStep 3060827 = 4591241) B4591241
theorem B2905627 : Blo 1358498 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B8714087 : Blo 1358498 8714087 := bstep (se 1 (by rfl) ⟨6535565, by rfl⟩ : syracuseStep 8714087 = 13071131) B13071131
theorem B9803753 : Blo 1358498 9803753 := bstep (se 2 (by rfl) ⟨3676407, by rfl⟩ : syracuseStep 9803753 = 7352815) B7352815
theorem B14703551 : Blo 1358498 14703551 := bstep (se 1 (by rfl) ⟨11027663, by rfl⟩ : syracuseStep 14703551 = 22055327) B22055327
theorem B19586225 : Blo 1358498 19586225 := bstep (se 2 (by rfl) ⟨7344834, by rfl⟩ : syracuseStep 19586225 = 14689669) B14689669
theorem B1359087 : Blo 1358498 1359087 := bstep (se 1 (by rfl) ⟨1019315, by rfl⟩ : syracuseStep 1359087 = 2038631) B2038631
theorem B2039081 : Blo 1358498 2039081 := bstep (se 2 (by rfl) ⟨764655, by rfl⟩ : syracuseStep 2039081 = 1529311) B1529311
theorem B1359359 : Blo 1358498 1359359 := bstep (se 1 (by rfl) ⟨1019519, by rfl⟩ : syracuseStep 1359359 = 2039039) B2039039
theorem B2039423 : Blo 1358498 2039423 := bstep (se 1 (by rfl) ⟨1529567, by rfl⟩ : syracuseStep 2039423 = 3059135) B3059135
theorem B2039975 : Blo 1358498 2039975 := bstep (se 1 (by rfl) ⟨1529981, by rfl⟩ : syracuseStep 2039975 = 3059963) B3059963
theorem B734708009 : Blo 1358498 734708009 := bstep (se 2 (by rfl) ⟨275515503, by rfl⟩ : syracuseStep 734708009 = 551031007) B551031007
theorem B7446907 : Blo 1358498 7446907 := bstep (se 1 (by rfl) ⟨5585180, by rfl⟩ : syracuseStep 7446907 = 11170361) B11170361
theorem B13058441 : Blo 1358498 13058441 := bstep (se 2 (by rfl) ⟨4896915, by rfl⟩ : syracuseStep 13058441 = 9793831) B9793831
theorem B1360431 : Blo 1358498 1360431 := bstep (se 1 (by rfl) ⟨1020323, by rfl⟩ : syracuseStep 1360431 = 2040647) B2040647
theorem B2040551 : Blo 1358498 2040551 := bstep (se 1 (by rfl) ⟨1530413, by rfl⟩ : syracuseStep 2040551 = 3060827) B3060827
theorem B3441599 : Blo 1358498 3441599 := bstep (se 1 (by rfl) ⟨2581199, by rfl⟩ : syracuseStep 3441599 = 5162399) B5162399
theorem B6882407 : Blo 1358498 6882407 := bstep (se 1 (by rfl) ⟨5161805, by rfl⟩ : syracuseStep 6882407 = 10323611) B10323611
theorem B5809391 : Blo 1358498 5809391 := bstep (se 1 (by rfl) ⟨4357043, by rfl⟩ : syracuseStep 5809391 = 8714087) B8714087
theorem B6882569 : Blo 1358498 6882569 := bstep (se 2 (by rfl) ⟨2580963, by rfl⟩ : syracuseStep 6882569 = 5161927) B5161927
theorem B29378213 : Blo 1358498 29378213 := bstep (se 4 (by rfl) ⟨2754207, by rfl⟩ : syracuseStep 29378213 = 5508415) B5508415
theorem B3058523 : Blo 1358498 3058523 := bstep (se 1 (by rfl) ⟨2293892, by rfl⟩ : syracuseStep 3058523 = 4587785) B4587785
theorem B17410949 : Blo 1358498 17410949 := bstep (se 4 (by rfl) ⟨1632276, by rfl⟩ : syracuseStep 17410949 = 3264553) B3264553
theorem B3059369 : Blo 1358498 3059369 := bstep (se 2 (by rfl) ⟨1147263, by rfl⟩ : syracuseStep 3059369 = 2294527) B2294527
theorem B9802367 : Blo 1358498 9802367 := bstep (se 1 (by rfl) ⟨7351775, by rfl⟩ : syracuseStep 9802367 = 14703551) B14703551
theorem B4650215 : Blo 1358498 4650215 := bstep (se 1 (by rfl) ⟨3487661, by rfl⟩ : syracuseStep 4650215 = 6975323) B6975323
theorem B2037815 : Blo 1358498 2037815 := bstep (se 1 (by rfl) ⟨1528361, by rfl⟩ : syracuseStep 2037815 = 3056723) B3056723
theorem B3267071 : Blo 1358498 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B3873383 : Blo 1358498 3873383 := bstep (se 1 (by rfl) ⟨2905037, by rfl⟩ : syracuseStep 3873383 = 5810075) B5810075
theorem B6535835 : Blo 1358498 6535835 := bstep (se 1 (by rfl) ⟨4901876, by rfl⟩ : syracuseStep 6535835 = 9803753) B9803753
theorem B2038511 : Blo 1358498 2038511 := bstep (se 1 (by rfl) ⟨1528883, by rfl⟩ : syracuseStep 2038511 = 3057767) B3057767
theorem B2038655 : Blo 1358498 2038655 := bstep (se 1 (by rfl) ⟨1528991, by rfl⟩ : syracuseStep 2038655 = 3057983) B3057983
theorem B3874169 : Blo 1358498 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B14146969 : Blo 1358498 14146969 := bstep (se 2 (by rfl) ⟨5305113, by rfl⟩ : syracuseStep 14146969 = 10610227) B10610227
theorem B13057483 : Blo 1358498 13057483 := bstep (se 1 (by rfl) ⟨9793112, by rfl⟩ : syracuseStep 13057483 = 19586225) B19586225
theorem B1359387 : Blo 1358498 1359387 := bstep (se 1 (by rfl) ⟨1019540, by rfl⟩ : syracuseStep 1359387 = 2039081) B2039081
theorem B1359615 : Blo 1358498 1359615 := bstep (se 1 (by rfl) ⟨1019711, by rfl⟩ : syracuseStep 1359615 = 2039423) B2039423
theorem B1359983 : Blo 1358498 1359983 := bstep (se 1 (by rfl) ⟨1019987, by rfl⟩ : syracuseStep 1359983 = 2039975) B2039975
theorem B1360367 : Blo 1358498 1360367 := bstep (se 1 (by rfl) ⟨1020275, by rfl⟩ : syracuseStep 1360367 = 2040551) B2040551
theorem B2294399 : Blo 1358498 2294399 := bstep (se 1 (by rfl) ⟨1720799, by rfl⟩ : syracuseStep 2294399 = 3441599) B3441599
theorem B4588271 : Blo 1358498 4588271 := bstep (se 1 (by rfl) ⟨3441203, by rfl⟩ : syracuseStep 4588271 = 6882407) B6882407
theorem B4588379 : Blo 1358498 4588379 := bstep (se 1 (by rfl) ⟨3441284, by rfl⟩ : syracuseStep 4588379 = 6882569) B6882569
theorem B2582255 : Blo 1358498 2582255 := bstep (se 1 (by rfl) ⟨1936691, by rfl⟩ : syracuseStep 2582255 = 3873383) B3873383
theorem B17409977 : Blo 1358498 17409977 := bstep (se 2 (by rfl) ⟨6528741, by rfl⟩ : syracuseStep 17409977 = 13057483) B13057483
theorem B39716837 : Blo 1358498 39716837 := bstep (se 4 (by rfl) ⟨3723453, by rfl⟩ : syracuseStep 39716837 = 7446907) B7446907
theorem B2582779 : Blo 1358498 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B18862625 : Blo 1358498 18862625 := bstep (se 2 (by rfl) ⟨7073484, by rfl⟩ : syracuseStep 18862625 = 14146969) B14146969
theorem B489805339 : Blo 1358498 489805339 := bstep (se 1 (by rfl) ⟨367354004, by rfl⟩ : syracuseStep 489805339 = 734708009) B734708009
theorem B8705627 : Blo 1358498 8705627 := bstep (se 1 (by rfl) ⟨6529220, by rfl⟩ : syracuseStep 8705627 = 13058441) B13058441
theorem B6534911 : Blo 1358498 6534911 := bstep (se 1 (by rfl) ⟨4901183, by rfl⟩ : syracuseStep 6534911 = 9802367) B9802367
theorem B12400573 : Blo 1358498 12400573 := bstep (se 3 (by rfl) ⟨2325107, by rfl⟩ : syracuseStep 12400573 = 4650215) B4650215
theorem B3872927 : Blo 1358498 3872927 := bstep (se 1 (by rfl) ⟨2904695, by rfl⟩ : syracuseStep 3872927 = 5809391) B5809391
theorem B19585475 : Blo 1358498 19585475 := bstep (se 1 (by rfl) ⟨14689106, by rfl⟩ : syracuseStep 19585475 = 29378213) B29378213
theorem B1358543 : Blo 1358498 1358543 := bstep (se 1 (by rfl) ⟨1018907, by rfl⟩ : syracuseStep 1358543 = 2037815) B2037815
theorem B2178047 : Blo 1358498 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B4357223 : Blo 1358498 4357223 := bstep (se 1 (by rfl) ⟨3267917, by rfl⟩ : syracuseStep 4357223 = 6535835) B6535835
theorem B1359007 : Blo 1358498 1359007 := bstep (se 1 (by rfl) ⟨1019255, by rfl⟩ : syracuseStep 1359007 = 2038511) B2038511
theorem B2039015 : Blo 1358498 2039015 := bstep (se 1 (by rfl) ⟨1529261, by rfl⟩ : syracuseStep 2039015 = 3058523) B3058523
theorem B1359103 : Blo 1358498 1359103 := bstep (se 1 (by rfl) ⟨1019327, by rfl⟩ : syracuseStep 1359103 = 2038655) B2038655
theorem B11607299 : Blo 1358498 11607299 := bstep (se 1 (by rfl) ⟨8705474, by rfl⟩ : syracuseStep 11607299 = 17410949) B17410949
theorem B2039579 : Blo 1358498 2039579 := bstep (se 1 (by rfl) ⟨1529684, by rfl⟩ : syracuseStep 2039579 = 3059369) B3059369
theorem B12575083 : Blo 1358498 12575083 := bstep (se 1 (by rfl) ⟨9431312, by rfl⟩ : syracuseStep 12575083 = 18862625) B18862625
theorem B1721503 : Blo 1358498 1721503 := bstep (se 1 (by rfl) ⟨1291127, by rfl⟩ : syracuseStep 1721503 = 2582255) B2582255
theorem B26477891 : Blo 1358498 26477891 := bstep (se 1 (by rfl) ⟨19858418, by rfl⟩ : syracuseStep 26477891 = 39716837) B39716837
theorem B2581951 : Blo 1358498 2581951 := bstep (se 1 (by rfl) ⟨1936463, by rfl⟩ : syracuseStep 2581951 = 3872927) B3872927
theorem B16534097 : Blo 1358498 16534097 := bstep (se 2 (by rfl) ⟨6200286, by rfl⟩ : syracuseStep 16534097 = 12400573) B12400573
theorem B3443705 : Blo 1358498 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B3058847 : Blo 1358498 3058847 := bstep (se 1 (by rfl) ⟨2294135, by rfl⟩ : syracuseStep 3058847 = 4588271) B4588271
theorem B3058919 : Blo 1358498 3058919 := bstep (se 1 (by rfl) ⟨2294189, by rfl⟩ : syracuseStep 3058919 = 4588379) B4588379
theorem B5803751 : Blo 1358498 5803751 := bstep (se 1 (by rfl) ⟨4352813, by rfl⟩ : syracuseStep 5803751 = 8705627) B8705627
theorem B2904815 : Blo 1358498 2904815 := bstep (se 1 (by rfl) ⟨2178611, by rfl⟩ : syracuseStep 2904815 = 4357223) B4357223
theorem B7738199 : Blo 1358498 7738199 := bstep (se 1 (by rfl) ⟨5803649, by rfl⟩ : syracuseStep 7738199 = 11607299) B11607299
theorem B1529599 : Blo 1358498 1529599 := bstep (se 1 (by rfl) ⟨1147199, by rfl⟩ : syracuseStep 1529599 = 2294399) B2294399
theorem B4356607 : Blo 1358498 4356607 := bstep (se 1 (by rfl) ⟨3267455, by rfl⟩ : syracuseStep 4356607 = 6534911) B6534911
theorem B11606651 : Blo 1358498 11606651 := bstep (se 1 (by rfl) ⟨8704988, by rfl⟩ : syracuseStep 11606651 = 17409977) B17409977
theorem B13056983 : Blo 1358498 13056983 := bstep (se 1 (by rfl) ⟨9792737, by rfl⟩ : syracuseStep 13056983 = 19585475) B19585475
theorem B653073785 : Blo 1358498 653073785 := bstep (se 2 (by rfl) ⟨244902669, by rfl⟩ : syracuseStep 653073785 = 489805339) B489805339
theorem B1359343 : Blo 1358498 1359343 := bstep (se 1 (by rfl) ⟨1019507, by rfl⟩ : syracuseStep 1359343 = 2039015) B2039015
theorem B1359719 : Blo 1358498 1359719 := bstep (se 1 (by rfl) ⟨1019789, by rfl⟩ : syracuseStep 1359719 = 2039579) B2039579
theorem B5808125 : Blo 1358498 5808125 := bstep (se 3 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 5808125 = 2178047) B2178047
theorem B5808809 : Blo 1358498 5808809 := bstep (se 2 (by rfl) ⟨2178303, by rfl⟩ : syracuseStep 5808809 = 4356607) B4356607
theorem B2295337 : Blo 1358498 2295337 := bstep (se 2 (by rfl) ⟨860751, by rfl⟩ : syracuseStep 2295337 = 1721503) B1721503
theorem B3442601 : Blo 1358498 3442601 := bstep (se 2 (by rfl) ⟨1290975, by rfl⟩ : syracuseStep 3442601 = 2581951) B2581951
theorem B15476669 : Blo 1358498 15476669 := bstep (se 3 (by rfl) ⟨2901875, by rfl⟩ : syracuseStep 15476669 = 5803751) B5803751
theorem B2295803 : Blo 1358498 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B435382523 : Blo 1358498 435382523 := bstep (se 1 (by rfl) ⟨326536892, by rfl⟩ : syracuseStep 435382523 = 653073785) B653073785
theorem B1936543 : Blo 1358498 1936543 := bstep (se 1 (by rfl) ⟨1452407, by rfl⟩ : syracuseStep 1936543 = 2904815) B2904815
theorem B11022731 : Blo 1358498 11022731 := bstep (se 1 (by rfl) ⟨8267048, by rfl⟩ : syracuseStep 11022731 = 16534097) B16534097
theorem B7737767 : Blo 1358498 7737767 := bstep (se 1 (by rfl) ⟨5803325, by rfl⟩ : syracuseStep 7737767 = 11606651) B11606651
theorem B8704655 : Blo 1358498 8704655 := bstep (se 1 (by rfl) ⟨6528491, by rfl⟩ : syracuseStep 8704655 = 13056983) B13056983
theorem B15488333 : Blo 1358498 15488333 := bstep (se 3 (by rfl) ⟨2904062, by rfl⟩ : syracuseStep 15488333 = 5808125) B5808125
theorem B16766777 : Blo 1358498 16766777 := bstep (se 2 (by rfl) ⟨6287541, by rfl⟩ : syracuseStep 16766777 = 12575083) B12575083
theorem B5158799 : Blo 1358498 5158799 := bstep (se 1 (by rfl) ⟨3869099, by rfl⟩ : syracuseStep 5158799 = 7738199) B7738199
theorem B17651927 : Blo 1358498 17651927 := bstep (se 1 (by rfl) ⟨13238945, by rfl⟩ : syracuseStep 17651927 = 26477891) B26477891
theorem B2039231 : Blo 1358498 2039231 := bstep (se 1 (by rfl) ⟨1529423, by rfl⟩ : syracuseStep 2039231 = 3058847) B3058847
theorem B2039279 : Blo 1358498 2039279 := bstep (se 1 (by rfl) ⟨1529459, by rfl⟩ : syracuseStep 2039279 = 3058919) B3058919
theorem B2039465 : Blo 1358498 2039465 := bstep (se 2 (by rfl) ⟨764799, by rfl⟩ : syracuseStep 2039465 = 1529599) B1529599
theorem B7348487 : Blo 1358498 7348487 := bstep (se 1 (by rfl) ⟨5511365, by rfl⟩ : syracuseStep 7348487 = 11022731) B11022731
theorem B2295067 : Blo 1358498 2295067 := bstep (se 1 (by rfl) ⟨1721300, by rfl⟩ : syracuseStep 2295067 = 3442601) B3442601
theorem B2582057 : Blo 1358498 2582057 := bstep (se 2 (by rfl) ⟨968271, by rfl⟩ : syracuseStep 2582057 = 1936543) B1936543
theorem B5803103 : Blo 1358498 5803103 := bstep (se 1 (by rfl) ⟨4352327, by rfl⟩ : syracuseStep 5803103 = 8704655) B8704655
theorem B10325555 : Blo 1358498 10325555 := bstep (se 1 (by rfl) ⟨7744166, by rfl⟩ : syracuseStep 10325555 = 15488333) B15488333
theorem B10317779 : Blo 1358498 10317779 := bstep (se 1 (by rfl) ⟨7738334, by rfl⟩ : syracuseStep 10317779 = 15476669) B15476669
theorem B11767951 : Blo 1358498 11767951 := bstep (se 1 (by rfl) ⟨8825963, by rfl⟩ : syracuseStep 11767951 = 17651927) B17651927
theorem B290255015 : Blo 1358498 290255015 := bstep (se 1 (by rfl) ⟨217691261, by rfl⟩ : syracuseStep 290255015 = 435382523) B435382523
theorem B3060449 : Blo 1358498 3060449 := bstep (se 2 (by rfl) ⟨1147668, by rfl⟩ : syracuseStep 3060449 = 2295337) B2295337
theorem B5158511 : Blo 1358498 5158511 := bstep (se 1 (by rfl) ⟨3868883, by rfl⟩ : syracuseStep 5158511 = 7737767) B7737767
theorem B3872539 : Blo 1358498 3872539 := bstep (se 1 (by rfl) ⟨2904404, by rfl⟩ : syracuseStep 3872539 = 5808809) B5808809
theorem B3439199 : Blo 1358498 3439199 := bstep (se 1 (by rfl) ⟨2579399, by rfl⟩ : syracuseStep 3439199 = 5158799) B5158799
theorem B1530535 : Blo 1358498 1530535 := bstep (se 1 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 1530535 = 2295803) B2295803
theorem B44711405 : Blo 1358498 44711405 := bstep (se 3 (by rfl) ⟨8383388, by rfl⟩ : syracuseStep 44711405 = 16766777) B16766777
theorem B1359487 : Blo 1358498 1359487 := bstep (se 1 (by rfl) ⟨1019615, by rfl⟩ : syracuseStep 1359487 = 2039231) B2039231
theorem B1359519 : Blo 1358498 1359519 := bstep (se 1 (by rfl) ⟨1019639, by rfl⟩ : syracuseStep 1359519 = 2039279) B2039279
theorem B1359643 : Blo 1358498 1359643 := bstep (se 1 (by rfl) ⟨1019732, by rfl⟩ : syracuseStep 1359643 = 2039465) B2039465
theorem B193503343 : Blo 1358498 193503343 := bstep (se 1 (by rfl) ⟨145127507, by rfl⟩ : syracuseStep 193503343 = 290255015) B290255015
theorem B2040299 : Blo 1358498 2040299 := bstep (se 1 (by rfl) ⟨1530224, by rfl⟩ : syracuseStep 2040299 = 3060449) B3060449
theorem B19595965 : Blo 1358498 19595965 := bstep (se 3 (by rfl) ⟨3674243, by rfl⟩ : syracuseStep 19595965 = 7348487) B7348487
theorem B2040713 : Blo 1358498 2040713 := bstep (se 2 (by rfl) ⟨765267, by rfl⟩ : syracuseStep 2040713 = 1530535) B1530535
theorem B3868735 : Blo 1358498 3868735 := bstep (se 1 (by rfl) ⟨2901551, by rfl⟩ : syracuseStep 3868735 = 5803103) B5803103
theorem B6883703 : Blo 1358498 6883703 := bstep (se 1 (by rfl) ⟨5162777, by rfl⟩ : syracuseStep 6883703 = 10325555) B10325555
theorem B5163385 : Blo 1358498 5163385 := bstep (se 2 (by rfl) ⟨1936269, by rfl⟩ : syracuseStep 5163385 = 3872539) B3872539
theorem B15690601 : Blo 1358498 15690601 := bstep (se 2 (by rfl) ⟨5883975, by rfl⟩ : syracuseStep 15690601 = 11767951) B11767951
theorem B6885485 : Blo 1358498 6885485 := bstep (se 3 (by rfl) ⟨1291028, by rfl⟩ : syracuseStep 6885485 = 2582057) B2582057
theorem B3060089 : Blo 1358498 3060089 := bstep (se 2 (by rfl) ⟨1147533, by rfl⟩ : syracuseStep 3060089 = 2295067) B2295067
theorem B29807603 : Blo 1358498 29807603 := bstep (se 1 (by rfl) ⟨22355702, by rfl⟩ : syracuseStep 29807603 = 44711405) B44711405
theorem B6878519 : Blo 1358498 6878519 := bstep (se 1 (by rfl) ⟨5158889, by rfl⟩ : syracuseStep 6878519 = 10317779) B10317779
theorem B3439007 : Blo 1358498 3439007 := bstep (se 1 (by rfl) ⟨2579255, by rfl⟩ : syracuseStep 3439007 = 5158511) B5158511
theorem B2292799 : Blo 1358498 2292799 := bstep (se 1 (by rfl) ⟨1719599, by rfl⟩ : syracuseStep 2292799 = 3439199) B3439199
theorem B2040059 : Blo 1358498 2040059 := bstep (se 1 (by rfl) ⟨1530044, by rfl⟩ : syracuseStep 2040059 = 3060089) B3060089
theorem B1360199 : Blo 1358498 1360199 := bstep (se 1 (by rfl) ⟨1020149, by rfl⟩ : syracuseStep 1360199 = 2040299) B2040299
theorem B1360475 : Blo 1358498 1360475 := bstep (se 1 (by rfl) ⟨1020356, by rfl⟩ : syracuseStep 1360475 = 2040713) B2040713
theorem B3057065 : Blo 1358498 3057065 := bstep (se 2 (by rfl) ⟨1146399, by rfl⟩ : syracuseStep 3057065 = 2292799) B2292799
theorem B4589135 : Blo 1358498 4589135 := bstep (se 1 (by rfl) ⟨3441851, by rfl⟩ : syracuseStep 4589135 = 6883703) B6883703
theorem B4590323 : Blo 1358498 4590323 := bstep (se 1 (by rfl) ⟨3442742, by rfl⟩ : syracuseStep 4590323 = 6885485) B6885485
theorem B6884513 : Blo 1358498 6884513 := bstep (se 2 (by rfl) ⟨2581692, by rfl⟩ : syracuseStep 6884513 = 5163385) B5163385
theorem B26127953 : Blo 1358498 26127953 := bstep (se 2 (by rfl) ⟨9797982, by rfl⟩ : syracuseStep 26127953 = 19595965) B19595965
theorem B5158313 : Blo 1358498 5158313 := bstep (se 2 (by rfl) ⟨1934367, by rfl⟩ : syracuseStep 5158313 = 3868735) B3868735
theorem B258004457 : Blo 1358498 258004457 := bstep (se 2 (by rfl) ⟨96751671, by rfl⟩ : syracuseStep 258004457 = 193503343) B193503343
theorem B19871735 : Blo 1358498 19871735 := bstep (se 1 (by rfl) ⟨14903801, by rfl⟩ : syracuseStep 19871735 = 29807603) B29807603
theorem B4585679 : Blo 1358498 4585679 := bstep (se 1 (by rfl) ⟨3439259, by rfl⟩ : syracuseStep 4585679 = 6878519) B6878519
theorem B20920801 : Blo 1358498 20920801 := bstep (se 2 (by rfl) ⟨7845300, by rfl⟩ : syracuseStep 20920801 = 15690601) B15690601
theorem B2292671 : Blo 1358498 2292671 := bstep (se 1 (by rfl) ⟨1719503, by rfl⟩ : syracuseStep 2292671 = 3439007) B3439007
theorem B1360039 : Blo 1358498 1360039 := bstep (se 1 (by rfl) ⟨1020029, by rfl⟩ : syracuseStep 1360039 = 2040059) B2040059
theorem B27894401 : Blo 1358498 27894401 := bstep (se 2 (by rfl) ⟨10460400, by rfl⟩ : syracuseStep 27894401 = 20920801) B20920801
theorem B3057119 : Blo 1358498 3057119 := bstep (se 1 (by rfl) ⟨2292839, by rfl⟩ : syracuseStep 3057119 = 4585679) B4585679
theorem B4589675 : Blo 1358498 4589675 := bstep (se 1 (by rfl) ⟨3442256, by rfl⟩ : syracuseStep 4589675 = 6884513) B6884513
theorem B17418635 : Blo 1358498 17418635 := bstep (se 1 (by rfl) ⟨13063976, by rfl⟩ : syracuseStep 17418635 = 26127953) B26127953
theorem B172002971 : Blo 1358498 172002971 := bstep (se 1 (by rfl) ⟨129002228, by rfl⟩ : syracuseStep 172002971 = 258004457) B258004457
theorem B3059423 : Blo 1358498 3059423 := bstep (se 1 (by rfl) ⟨2294567, by rfl⟩ : syracuseStep 3059423 = 4589135) B4589135
theorem B3060215 : Blo 1358498 3060215 := bstep (se 1 (by rfl) ⟨2295161, by rfl⟩ : syracuseStep 3060215 = 4590323) B4590323
theorem B1528447 : Blo 1358498 1528447 := bstep (se 1 (by rfl) ⟨1146335, by rfl⟩ : syracuseStep 1528447 = 2292671) B2292671
theorem B52991293 : Blo 1358498 52991293 := bstep (se 3 (by rfl) ⟨9935867, by rfl⟩ : syracuseStep 52991293 = 19871735) B19871735
theorem B3438875 : Blo 1358498 3438875 := bstep (se 1 (by rfl) ⟨2579156, by rfl⟩ : syracuseStep 3438875 = 5158313) B5158313
theorem B2038043 : Blo 1358498 2038043 := bstep (se 1 (by rfl) ⟨1528532, by rfl⟩ : syracuseStep 2038043 = 3057065) B3057065
theorem B2040143 : Blo 1358498 2040143 := bstep (se 1 (by rfl) ⟨1530107, by rfl⟩ : syracuseStep 2040143 = 3060215) B3060215
theorem B18596267 : Blo 1358498 18596267 := bstep (se 1 (by rfl) ⟨13947200, by rfl⟩ : syracuseStep 18596267 = 27894401) B27894401
theorem B3059783 : Blo 1358498 3059783 := bstep (se 1 (by rfl) ⟨2294837, by rfl⟩ : syracuseStep 3059783 = 4589675) B4589675
theorem B11612423 : Blo 1358498 11612423 := bstep (se 1 (by rfl) ⟨8709317, by rfl⟩ : syracuseStep 11612423 = 17418635) B17418635
theorem B458674589 : Blo 1358498 458674589 := bstep (se 3 (by rfl) ⟨86001485, by rfl⟩ : syracuseStep 458674589 = 172002971) B172002971
theorem B2037929 : Blo 1358498 2037929 := bstep (se 2 (by rfl) ⟨764223, by rfl⟩ : syracuseStep 2037929 = 1528447) B1528447
theorem B2038079 : Blo 1358498 2038079 := bstep (se 1 (by rfl) ⟨1528559, by rfl⟩ : syracuseStep 2038079 = 3057119) B3057119
theorem B2292583 : Blo 1358498 2292583 := bstep (se 1 (by rfl) ⟨1719437, by rfl⟩ : syracuseStep 2292583 = 3438875) B3438875
theorem B1358695 : Blo 1358498 1358695 := bstep (se 1 (by rfl) ⟨1019021, by rfl⟩ : syracuseStep 1358695 = 2038043) B2038043
theorem B70655057 : Blo 1358498 70655057 := bstep (se 2 (by rfl) ⟨26495646, by rfl⟩ : syracuseStep 70655057 = 52991293) B52991293
theorem B2039615 : Blo 1358498 2039615 := bstep (se 1 (by rfl) ⟨1529711, by rfl⟩ : syracuseStep 2039615 = 3059423) B3059423
theorem B2039855 : Blo 1358498 2039855 := bstep (se 1 (by rfl) ⟨1529891, by rfl⟩ : syracuseStep 2039855 = 3059783) B3059783
theorem B7741615 : Blo 1358498 7741615 := bstep (se 1 (by rfl) ⟨5806211, by rfl⟩ : syracuseStep 7741615 = 11612423) B11612423
theorem B1360095 : Blo 1358498 1360095 := bstep (se 1 (by rfl) ⟨1020071, by rfl⟩ : syracuseStep 1360095 = 2040143) B2040143
theorem B305783059 : Blo 1358498 305783059 := bstep (se 1 (by rfl) ⟨229337294, by rfl⟩ : syracuseStep 305783059 = 458674589) B458674589
theorem B3056777 : Blo 1358498 3056777 := bstep (se 2 (by rfl) ⟨1146291, by rfl⟩ : syracuseStep 3056777 = 2292583) B2292583
theorem B12397511 : Blo 1358498 12397511 := bstep (se 1 (by rfl) ⟨9298133, by rfl⟩ : syracuseStep 12397511 = 18596267) B18596267
theorem B1358619 : Blo 1358498 1358619 := bstep (se 1 (by rfl) ⟨1018964, by rfl⟩ : syracuseStep 1358619 = 2037929) B2037929
theorem B1358719 : Blo 1358498 1358719 := bstep (se 1 (by rfl) ⟨1019039, by rfl⟩ : syracuseStep 1358719 = 2038079) B2038079
theorem B47103371 : Blo 1358498 47103371 := bstep (se 1 (by rfl) ⟨35327528, by rfl⟩ : syracuseStep 47103371 = 70655057) B70655057
theorem B1359743 : Blo 1358498 1359743 := bstep (se 1 (by rfl) ⟨1019807, by rfl⟩ : syracuseStep 1359743 = 2039615) B2039615
theorem B1359903 : Blo 1358498 1359903 := bstep (se 1 (by rfl) ⟨1019927, by rfl⟩ : syracuseStep 1359903 = 2039855) B2039855
theorem B10322153 : Blo 1358498 10322153 := bstep (se 2 (by rfl) ⟨3870807, by rfl⟩ : syracuseStep 10322153 = 7741615) B7741615
theorem B31402247 : Blo 1358498 31402247 := bstep (se 1 (by rfl) ⟨23551685, by rfl⟩ : syracuseStep 31402247 = 47103371) B47103371
theorem B407710745 : Blo 1358498 407710745 := bstep (se 2 (by rfl) ⟨152891529, by rfl⟩ : syracuseStep 407710745 = 305783059) B305783059
theorem B2037851 : Blo 1358498 2037851 := bstep (se 1 (by rfl) ⟨1528388, by rfl⟩ : syracuseStep 2037851 = 3056777) B3056777
theorem B8265007 : Blo 1358498 8265007 := bstep (se 1 (by rfl) ⟨6198755, by rfl⟩ : syracuseStep 8265007 = 12397511) B12397511
theorem B6881435 : Blo 1358498 6881435 := bstep (se 1 (by rfl) ⟨5161076, by rfl⟩ : syracuseStep 6881435 = 10322153) B10322153
theorem B83739325 : Blo 1358498 83739325 := bstep (se 3 (by rfl) ⟨15701123, by rfl⟩ : syracuseStep 83739325 = 31402247) B31402247
theorem B11020009 : Blo 1358498 11020009 := bstep (se 2 (by rfl) ⟨4132503, by rfl⟩ : syracuseStep 11020009 = 8265007) B8265007
theorem B271807163 : Blo 1358498 271807163 := bstep (se 1 (by rfl) ⟨203855372, by rfl⟩ : syracuseStep 271807163 = 407710745) B407710745
theorem B1358567 : Blo 1358498 1358567 := bstep (se 1 (by rfl) ⟨1018925, by rfl⟩ : syracuseStep 1358567 = 2037851) B2037851
theorem B4587623 : Blo 1358498 4587623 := bstep (se 1 (by rfl) ⟨3440717, by rfl⟩ : syracuseStep 4587623 = 6881435) B6881435
theorem B111652433 : Blo 1358498 111652433 := bstep (se 2 (by rfl) ⟨41869662, by rfl⟩ : syracuseStep 111652433 = 83739325) B83739325
theorem B14693345 : Blo 1358498 14693345 := bstep (se 2 (by rfl) ⟨5510004, by rfl⟩ : syracuseStep 14693345 = 11020009) B11020009
theorem B181204775 : Blo 1358498 181204775 := bstep (se 1 (by rfl) ⟨135903581, by rfl⟩ : syracuseStep 181204775 = 271807163) B271807163
theorem B74434955 : Blo 1358498 74434955 := bstep (se 1 (by rfl) ⟨55826216, by rfl⟩ : syracuseStep 74434955 = 111652433) B111652433
theorem B3058415 : Blo 1358498 3058415 := bstep (se 1 (by rfl) ⟨2293811, by rfl⟩ : syracuseStep 3058415 = 4587623) B4587623
theorem B120803183 : Blo 1358498 120803183 := bstep (se 1 (by rfl) ⟨90602387, by rfl⟩ : syracuseStep 120803183 = 181204775) B181204775
theorem B9795563 : Blo 1358498 9795563 := bstep (se 1 (by rfl) ⟨7346672, by rfl⟩ : syracuseStep 9795563 = 14693345) B14693345
theorem B198493213 : Blo 1358498 198493213 := bstep (se 3 (by rfl) ⟨37217477, by rfl⟩ : syracuseStep 198493213 = 74434955) B74434955
theorem B6530375 : Blo 1358498 6530375 := bstep (se 1 (by rfl) ⟨4897781, by rfl⟩ : syracuseStep 6530375 = 9795563) B9795563
theorem B2038943 : Blo 1358498 2038943 := bstep (se 1 (by rfl) ⟨1529207, by rfl⟩ : syracuseStep 2038943 = 3058415) B3058415
theorem B80535455 : Blo 1358498 80535455 := bstep (se 1 (by rfl) ⟨60401591, by rfl⟩ : syracuseStep 80535455 = 120803183) B120803183
theorem B4353583 : Blo 1358498 4353583 := bstep (se 1 (by rfl) ⟨3265187, by rfl⟩ : syracuseStep 4353583 = 6530375) B6530375
theorem B264657617 : Blo 1358498 264657617 := bstep (se 2 (by rfl) ⟨99246606, by rfl⟩ : syracuseStep 264657617 = 198493213) B198493213
theorem B1359295 : Blo 1358498 1359295 := bstep (se 1 (by rfl) ⟨1019471, by rfl⟩ : syracuseStep 1359295 = 2038943) B2038943
theorem B53690303 : Blo 1358498 53690303 := bstep (se 1 (by rfl) ⟨40267727, by rfl⟩ : syracuseStep 53690303 = 80535455) B80535455
theorem B35793535 : Blo 1358498 35793535 := bstep (se 1 (by rfl) ⟨26845151, by rfl⟩ : syracuseStep 35793535 = 53690303) B53690303
theorem B5804777 : Blo 1358498 5804777 := bstep (se 2 (by rfl) ⟨2176791, by rfl⟩ : syracuseStep 5804777 = 4353583) B4353583
theorem B176438411 : Blo 1358498 176438411 := bstep (se 1 (by rfl) ⟨132328808, by rfl⟩ : syracuseStep 176438411 = 264657617) B264657617
theorem B3869851 : Blo 1358498 3869851 := bstep (se 1 (by rfl) ⟨2902388, by rfl⟩ : syracuseStep 3869851 = 5804777) B5804777
theorem B117625607 : Blo 1358498 117625607 := bstep (se 1 (by rfl) ⟨88219205, by rfl⟩ : syracuseStep 117625607 = 176438411) B176438411
theorem B47724713 : Blo 1358498 47724713 := bstep (se 2 (by rfl) ⟨17896767, by rfl⟩ : syracuseStep 47724713 = 35793535) B35793535
theorem B78417071 : Blo 1358498 78417071 := bstep (se 1 (by rfl) ⟨58812803, by rfl⟩ : syracuseStep 78417071 = 117625607) B117625607
theorem B31816475 : Blo 1358498 31816475 := bstep (se 1 (by rfl) ⟨23862356, by rfl⟩ : syracuseStep 31816475 = 47724713) B47724713
theorem B5159801 : Blo 1358498 5159801 := bstep (se 2 (by rfl) ⟨1934925, by rfl⟩ : syracuseStep 5159801 = 3869851) B3869851
theorem B21210983 : Blo 1358498 21210983 := bstep (se 1 (by rfl) ⟨15908237, by rfl⟩ : syracuseStep 21210983 = 31816475) B31816475
theorem B52278047 : Blo 1358498 52278047 := bstep (se 1 (by rfl) ⟨39208535, by rfl⟩ : syracuseStep 52278047 = 78417071) B78417071
theorem B3439867 : Blo 1358498 3439867 := bstep (se 1 (by rfl) ⟨2579900, by rfl⟩ : syracuseStep 3439867 = 5159801) B5159801
theorem B14140655 : Blo 1358498 14140655 := bstep (se 1 (by rfl) ⟨10605491, by rfl⟩ : syracuseStep 14140655 = 21210983) B21210983
theorem B34852031 : Blo 1358498 34852031 := bstep (se 1 (by rfl) ⟨26139023, by rfl⟩ : syracuseStep 34852031 = 52278047) B52278047
theorem B4586489 : Blo 1358498 4586489 := bstep (se 2 (by rfl) ⟨1719933, by rfl⟩ : syracuseStep 4586489 = 3439867) B3439867
theorem B3057659 : Blo 1358498 3057659 := bstep (se 1 (by rfl) ⟨2293244, by rfl⟩ : syracuseStep 3057659 = 4586489) B4586489
theorem B23234687 : Blo 1358498 23234687 := bstep (se 1 (by rfl) ⟨17426015, by rfl⟩ : syracuseStep 23234687 = 34852031) B34852031
theorem B9427103 : Blo 1358498 9427103 := bstep (se 1 (by rfl) ⟨7070327, by rfl⟩ : syracuseStep 9427103 = 14140655) B14140655
theorem B6284735 : Blo 1358498 6284735 := bstep (se 1 (by rfl) ⟨4713551, by rfl⟩ : syracuseStep 6284735 = 9427103) B9427103
theorem B2038439 : Blo 1358498 2038439 := bstep (se 1 (by rfl) ⟨1528829, by rfl⟩ : syracuseStep 2038439 = 3057659) B3057659
theorem B15489791 : Blo 1358498 15489791 := bstep (se 1 (by rfl) ⟨11617343, by rfl⟩ : syracuseStep 15489791 = 23234687) B23234687
theorem B4189823 : Blo 1358498 4189823 := bstep (se 1 (by rfl) ⟨3142367, by rfl⟩ : syracuseStep 4189823 = 6284735) B6284735
theorem B10326527 : Blo 1358498 10326527 := bstep (se 1 (by rfl) ⟨7744895, by rfl⟩ : syracuseStep 10326527 = 15489791) B15489791
theorem B1358959 : Blo 1358498 1358959 := bstep (se 1 (by rfl) ⟨1019219, by rfl⟩ : syracuseStep 1358959 = 2038439) B2038439
theorem B6884351 : Blo 1358498 6884351 := bstep (se 1 (by rfl) ⟨5163263, by rfl⟩ : syracuseStep 6884351 = 10326527) B10326527
theorem B2793215 : Blo 1358498 2793215 := bstep (se 1 (by rfl) ⟨2094911, by rfl⟩ : syracuseStep 2793215 = 4189823) B4189823
theorem B4589567 : Blo 1358498 4589567 := bstep (se 1 (by rfl) ⟨3442175, by rfl⟩ : syracuseStep 4589567 = 6884351) B6884351
theorem B1862143 : Blo 1358498 1862143 := bstep (se 1 (by rfl) ⟨1396607, by rfl⟩ : syracuseStep 1862143 = 2793215) B2793215
theorem B9931429 : Blo 1358498 9931429 := bstep (se 4 (by rfl) ⟨931071, by rfl⟩ : syracuseStep 9931429 = 1862143) B1862143
theorem B3059711 : Blo 1358498 3059711 := bstep (se 1 (by rfl) ⟨2294783, by rfl⟩ : syracuseStep 3059711 = 4589567) B4589567
theorem B52967621 : Blo 1358498 52967621 := bstep (se 4 (by rfl) ⟨4965714, by rfl⟩ : syracuseStep 52967621 = 9931429) B9931429
theorem B2039807 : Blo 1358498 2039807 := bstep (se 1 (by rfl) ⟨1529855, by rfl⟩ : syracuseStep 2039807 = 3059711) B3059711
theorem B35311747 : Blo 1358498 35311747 := bstep (se 1 (by rfl) ⟨26483810, by rfl⟩ : syracuseStep 35311747 = 52967621) B52967621
theorem B1359871 : Blo 1358498 1359871 := bstep (se 1 (by rfl) ⟨1019903, by rfl⟩ : syracuseStep 1359871 = 2039807) B2039807
theorem B47082329 : Blo 1358498 47082329 := bstep (se 2 (by rfl) ⟨17655873, by rfl⟩ : syracuseStep 47082329 = 35311747) B35311747
theorem B31388219 : Blo 1358498 31388219 := bstep (se 1 (by rfl) ⟨23541164, by rfl⟩ : syracuseStep 31388219 = 47082329) B47082329
theorem B20925479 : Blo 1358498 20925479 := bstep (se 1 (by rfl) ⟨15694109, by rfl⟩ : syracuseStep 20925479 = 31388219) B31388219
theorem B13950319 : Blo 1358498 13950319 := bstep (se 1 (by rfl) ⟨10462739, by rfl⟩ : syracuseStep 13950319 = 20925479) B20925479
theorem B18600425 : Blo 1358498 18600425 := bstep (se 2 (by rfl) ⟨6975159, by rfl⟩ : syracuseStep 18600425 = 13950319) B13950319
theorem B12400283 : Blo 1358498 12400283 := bstep (se 1 (by rfl) ⟨9300212, by rfl⟩ : syracuseStep 12400283 = 18600425) B18600425
theorem B8266855 : Blo 1358498 8266855 := bstep (se 1 (by rfl) ⟨6200141, by rfl⟩ : syracuseStep 8266855 = 12400283) B12400283
theorem B11022473 : Blo 1358498 11022473 := bstep (se 2 (by rfl) ⟨4133427, by rfl⟩ : syracuseStep 11022473 = 8266855) B8266855
theorem B7348315 : Blo 1358498 7348315 := bstep (se 1 (by rfl) ⟨5511236, by rfl⟩ : syracuseStep 7348315 = 11022473) B11022473
theorem B9797753 : Blo 1358498 9797753 := bstep (se 2 (by rfl) ⟨3674157, by rfl⟩ : syracuseStep 9797753 = 7348315) B7348315
theorem B6531835 : Blo 1358498 6531835 := bstep (se 1 (by rfl) ⟨4898876, by rfl⟩ : syracuseStep 6531835 = 9797753) B9797753
theorem B8709113 : Blo 1358498 8709113 := bstep (se 2 (by rfl) ⟨3265917, by rfl⟩ : syracuseStep 8709113 = 6531835) B6531835
theorem B5806075 : Blo 1358498 5806075 := bstep (se 1 (by rfl) ⟨4354556, by rfl⟩ : syracuseStep 5806075 = 8709113) B8709113
theorem B7741433 : Blo 1358498 7741433 := bstep (se 2 (by rfl) ⟨2903037, by rfl⟩ : syracuseStep 7741433 = 5806075) B5806075
theorem B5160955 : Blo 1358498 5160955 := bstep (se 1 (by rfl) ⟨3870716, by rfl⟩ : syracuseStep 5160955 = 7741433) B7741433
theorem B6881273 : Blo 1358498 6881273 := bstep (se 2 (by rfl) ⟨2580477, by rfl⟩ : syracuseStep 6881273 = 5160955) B5160955
theorem B4587515 : Blo 1358498 4587515 := bstep (se 1 (by rfl) ⟨3440636, by rfl⟩ : syracuseStep 4587515 = 6881273) B6881273
theorem B3058343 : Blo 1358498 3058343 := bstep (se 1 (by rfl) ⟨2293757, by rfl⟩ : syracuseStep 3058343 = 4587515) B4587515
theorem B2038895 : Blo 1358498 2038895 := bstep (se 1 (by rfl) ⟨1529171, by rfl⟩ : syracuseStep 2038895 = 3058343) B3058343
theorem B1359263 : Blo 1358498 1359263 := bstep (se 1 (by rfl) ⟨1019447, by rfl⟩ : syracuseStep 1359263 = 2038895) B2038895

theorem C0 (j : ℕ) (h1 : 339624 ≤ j) (h2 : j ≤ 340123) : Blo 1358498 (4 * j + 3) := by
  interval_cases j
  · exact B1358499
  · exact B1358503
  · exact B1358507
  · exact B1358511
  · exact B1358515
  · exact B1358519
  · exact B1358523
  · exact B1358527
  · exact B1358531
  · exact B1358535
  · exact B1358539
  · exact B1358543
  · exact B1358547
  · exact B1358551
  · exact B1358555
  · exact B1358559
  · exact B1358563
  · exact B1358567
  · exact B1358571
  · exact B1358575
  · exact B1358579
  · exact B1358583
  · exact B1358587
  · exact B1358591
  · exact B1358595
  · exact B1358599
  · exact B1358603
  · exact B1358607
  · exact B1358611
  · exact B1358615
  · exact B1358619
  · exact B1358623
  · exact B1358627
  · exact B1358631
  · exact B1358635
  · exact B1358639
  · exact B1358643
  · exact B1358647
  · exact B1358651
  · exact B1358655
  · exact B1358659
  · exact B1358663
  · exact B1358667
  · exact B1358671
  · exact B1358675
  · exact B1358679
  · exact B1358683
  · exact B1358687
  · exact B1358691
  · exact B1358695
  · exact B1358699
  · exact B1358703
  · exact B1358707
  · exact B1358711
  · exact B1358715
  · exact B1358719
  · exact B1358723
  · exact B1358727
  · exact B1358731
  · exact B1358735
  · exact B1358739
  · exact B1358743
  · exact B1358747
  · exact B1358751
  · exact B1358755
  · exact B1358759
  · exact B1358763
  · exact B1358767
  · exact B1358771
  · exact B1358775
  · exact B1358779
  · exact B1358783
  · exact B1358787
  · exact B1358791
  · exact B1358795
  · exact B1358799
  · exact B1358803
  · exact B1358807
  · exact B1358811
  · exact B1358815
  · exact B1358819
  · exact B1358823
  · exact B1358827
  · exact B1358831
  · exact B1358835
  · exact B1358839
  · exact B1358843
  · exact B1358847
  · exact B1358851
  · exact B1358855
  · exact B1358859
  · exact B1358863
  · exact B1358867
  · exact B1358871
  · exact B1358875
  · exact B1358879
  · exact B1358883
  · exact B1358887
  · exact B1358891
  · exact B1358895
  · exact B1358899
  · exact B1358903
  · exact B1358907
  · exact B1358911
  · exact B1358915
  · exact B1358919
  · exact B1358923
  · exact B1358927
  · exact B1358931
  · exact B1358935
  · exact B1358939
  · exact B1358943
  · exact B1358947
  · exact B1358951
  · exact B1358955
  · exact B1358959
  · exact B1358963
  · exact B1358967
  · exact B1358971
  · exact B1358975
  · exact B1358979
  · exact B1358983
  · exact B1358987
  · exact B1358991
  · exact B1358995
  · exact B1358999
  · exact B1359003
  · exact B1359007
  · exact B1359011
  · exact B1359015
  · exact B1359019
  · exact B1359023
  · exact B1359027
  · exact B1359031
  · exact B1359035
  · exact B1359039
  · exact B1359043
  · exact B1359047
  · exact B1359051
  · exact B1359055
  · exact B1359059
  · exact B1359063
  · exact B1359067
  · exact B1359071
  · exact B1359075
  · exact B1359079
  · exact B1359083
  · exact B1359087
  · exact B1359091
  · exact B1359095
  · exact B1359099
  · exact B1359103
  · exact B1359107
  · exact B1359111
  · exact B1359115
  · exact B1359119
  · exact B1359123
  · exact B1359127
  · exact B1359131
  · exact B1359135
  · exact B1359139
  · exact B1359143
  · exact B1359147
  · exact B1359151
  · exact B1359155
  · exact B1359159
  · exact B1359163
  · exact B1359167
  · exact B1359171
  · exact B1359175
  · exact B1359179
  · exact B1359183
  · exact B1359187
  · exact B1359191
  · exact B1359195
  · exact B1359199
  · exact B1359203
  · exact B1359207
  · exact B1359211
  · exact B1359215
  · exact B1359219
  · exact B1359223
  · exact B1359227
  · exact B1359231
  · exact B1359235
  · exact B1359239
  · exact B1359243
  · exact B1359247
  · exact B1359251
  · exact B1359255
  · exact B1359259
  · exact B1359263
  · exact B1359267
  · exact B1359271
  · exact B1359275
  · exact B1359279
  · exact B1359283
  · exact B1359287
  · exact B1359291
  · exact B1359295
  · exact B1359299
  · exact B1359303
  · exact B1359307
  · exact B1359311
  · exact B1359315
  · exact B1359319
  · exact B1359323
  · exact B1359327
  · exact B1359331
  · exact B1359335
  · exact B1359339
  · exact B1359343
  · exact B1359347
  · exact B1359351
  · exact B1359355
  · exact B1359359
  · exact B1359363
  · exact B1359367
  · exact B1359371
  · exact B1359375
  · exact B1359379
  · exact B1359383
  · exact B1359387
  · exact B1359391
  · exact B1359395
  · exact B1359399
  · exact B1359403
  · exact B1359407
  · exact B1359411
  · exact B1359415
  · exact B1359419
  · exact B1359423
  · exact B1359427
  · exact B1359431
  · exact B1359435
  · exact B1359439
  · exact B1359443
  · exact B1359447
  · exact B1359451
  · exact B1359455
  · exact B1359459
  · exact B1359463
  · exact B1359467
  · exact B1359471
  · exact B1359475
  · exact B1359479
  · exact B1359483
  · exact B1359487
  · exact B1359491
  · exact B1359495
  · exact B1359499
  · exact B1359503
  · exact B1359507
  · exact B1359511
  · exact B1359515
  · exact B1359519
  · exact B1359523
  · exact B1359527
  · exact B1359531
  · exact B1359535
  · exact B1359539
  · exact B1359543
  · exact B1359547
  · exact B1359551
  · exact B1359555
  · exact B1359559
  · exact B1359563
  · exact B1359567
  · exact B1359571
  · exact B1359575
  · exact B1359579
  · exact B1359583
  · exact B1359587
  · exact B1359591
  · exact B1359595
  · exact B1359599
  · exact B1359603
  · exact B1359607
  · exact B1359611
  · exact B1359615
  · exact B1359619
  · exact B1359623
  · exact B1359627
  · exact B1359631
  · exact B1359635
  · exact B1359639
  · exact B1359643
  · exact B1359647
  · exact B1359651
  · exact B1359655
  · exact B1359659
  · exact B1359663
  · exact B1359667
  · exact B1359671
  · exact B1359675
  · exact B1359679
  · exact B1359683
  · exact B1359687
  · exact B1359691
  · exact B1359695
  · exact B1359699
  · exact B1359703
  · exact B1359707
  · exact B1359711
  · exact B1359715
  · exact B1359719
  · exact B1359723
  · exact B1359727
  · exact B1359731
  · exact B1359735
  · exact B1359739
  · exact B1359743
  · exact B1359747
  · exact B1359751
  · exact B1359755
  · exact B1359759
  · exact B1359763
  · exact B1359767
  · exact B1359771
  · exact B1359775
  · exact B1359779
  · exact B1359783
  · exact B1359787
  · exact B1359791
  · exact B1359795
  · exact B1359799
  · exact B1359803
  · exact B1359807
  · exact B1359811
  · exact B1359815
  · exact B1359819
  · exact B1359823
  · exact B1359827
  · exact B1359831
  · exact B1359835
  · exact B1359839
  · exact B1359843
  · exact B1359847
  · exact B1359851
  · exact B1359855
  · exact B1359859
  · exact B1359863
  · exact B1359867
  · exact B1359871
  · exact B1359875
  · exact B1359879
  · exact B1359883
  · exact B1359887
  · exact B1359891
  · exact B1359895
  · exact B1359899
  · exact B1359903
  · exact B1359907
  · exact B1359911
  · exact B1359915
  · exact B1359919
  · exact B1359923
  · exact B1359927
  · exact B1359931
  · exact B1359935
  · exact B1359939
  · exact B1359943
  · exact B1359947
  · exact B1359951
  · exact B1359955
  · exact B1359959
  · exact B1359963
  · exact B1359967
  · exact B1359971
  · exact B1359975
  · exact B1359979
  · exact B1359983
  · exact B1359987
  · exact B1359991
  · exact B1359995
  · exact B1359999
  · exact B1360003
  · exact B1360007
  · exact B1360011
  · exact B1360015
  · exact B1360019
  · exact B1360023
  · exact B1360027
  · exact B1360031
  · exact B1360035
  · exact B1360039
  · exact B1360043
  · exact B1360047
  · exact B1360051
  · exact B1360055
  · exact B1360059
  · exact B1360063
  · exact B1360067
  · exact B1360071
  · exact B1360075
  · exact B1360079
  · exact B1360083
  · exact B1360087
  · exact B1360091
  · exact B1360095
  · exact B1360099
  · exact B1360103
  · exact B1360107
  · exact B1360111
  · exact B1360115
  · exact B1360119
  · exact B1360123
  · exact B1360127
  · exact B1360131
  · exact B1360135
  · exact B1360139
  · exact B1360143
  · exact B1360147
  · exact B1360151
  · exact B1360155
  · exact B1360159
  · exact B1360163
  · exact B1360167
  · exact B1360171
  · exact B1360175
  · exact B1360179
  · exact B1360183
  · exact B1360187
  · exact B1360191
  · exact B1360195
  · exact B1360199
  · exact B1360203
  · exact B1360207
  · exact B1360211
  · exact B1360215
  · exact B1360219
  · exact B1360223
  · exact B1360227
  · exact B1360231
  · exact B1360235
  · exact B1360239
  · exact B1360243
  · exact B1360247
  · exact B1360251
  · exact B1360255
  · exact B1360259
  · exact B1360263
  · exact B1360267
  · exact B1360271
  · exact B1360275
  · exact B1360279
  · exact B1360283
  · exact B1360287
  · exact B1360291
  · exact B1360295
  · exact B1360299
  · exact B1360303
  · exact B1360307
  · exact B1360311
  · exact B1360315
  · exact B1360319
  · exact B1360323
  · exact B1360327
  · exact B1360331
  · exact B1360335
  · exact B1360339
  · exact B1360343
  · exact B1360347
  · exact B1360351
  · exact B1360355
  · exact B1360359
  · exact B1360363
  · exact B1360367
  · exact B1360371
  · exact B1360375
  · exact B1360379
  · exact B1360383
  · exact B1360387
  · exact B1360391
  · exact B1360395
  · exact B1360399
  · exact B1360403
  · exact B1360407
  · exact B1360411
  · exact B1360415
  · exact B1360419
  · exact B1360423
  · exact B1360427
  · exact B1360431
  · exact B1360435
  · exact B1360439
  · exact B1360443
  · exact B1360447
  · exact B1360451
  · exact B1360455
  · exact B1360459
  · exact B1360463
  · exact B1360467
  · exact B1360471
  · exact B1360475
  · exact B1360479
  · exact B1360483
  · exact B1360487
  · exact B1360491
  · exact B1360495

theorem solution (m : ℕ) (hlo : 1358498 ≤ m) (hhi : m ≤ 1360498) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 339624 ≤ j := by omega
    have hj2 : j ≤ 340123 := by omega
    have hb : Blo 1358498 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
